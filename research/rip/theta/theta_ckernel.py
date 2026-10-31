"""Compiled kernel for the matrix-free normal-equation product E^H E v of the sextic matrix (AVX-512 + OpenMP).

E[z, x] = chi_z(x) is never stored.  Row z is rebuilt from the symbol table T (row prime x source, int8 codes 0..5, or
100 = "prime divides source") as the sum of the table rows of z's prime ideals, one cache-resident pass per row, and
E^H E v = sum_z conj(E[z, :])^T (E[z, :] v) is accumulated in the same pass.  Models, each with E's exact zero pattern:
  mode 0  exact sixth roots of unity (sextic matrix; give the table of RCHAR for the reciprocity-broken matrix);
  mode 1  i.i.d. phases uniform on the 32nd roots of unity (the masked random baseline), drawn from a counter-based
          generator keyed by (seed, row, column) so that the matrix is the same at every call.
Single precision arithmetic, thread-local float32 accumulators, planar complex vectors.

The C source below is compiled at first use into a temporary directory (gcc, -fopenmp, -march=native).

usage (library):
    import theta_ckernel as ck
    K = ck.Kernel(T, LOC, nthreads=3)           # T: (nu, S) int8 table, LOC: (R, J) local prime indices, -1 padded
    w = K.matvec(v, mode=0, seed=0)             # E^H E v for a complex vector v of length S
    W = K.matmat(V, mode=0)                     # same for a block V of shape (S, b), b <= 8
    K.matvec(v, rows=W_idx, normalize=True)     # the same restricted to the rows W_idx, each row scaled to unit norm:
                                                #   E_W^H D^-1 E_W v, the unit-diagonal Gram of the row set
    Y = K.forward(V, rows=None)                 # E V (all rows, or the rows given)
    lam = K.top(k=4, mode=0, tol=1e-4)          # top eigenvalues of E^H E / S (ARPACK Lanczos on the operator)
    lam, vec = K.top(k=4, vectors=True)         # with the eigenvectors (right singular vectors of E)
    K.top(k=1, rows=W_idx, normalize=True)      # top eigenvalue of the unit-diagonal Gram of a row set
Row sets of fewer than 3e7 / S rows are run on one thread (fork/join cost); set OPENBLAS_NUM_THREADS=1 when calling top()
on small row sets (ARPACK's BLAS calls are slow under multithreaded BLAS on a loaded machine).  The kernel was checked
against the dense matrix (rows, products, row subsets, normalised rows, forward product) at B = 10^4 to 1e-6 relative
and against the numpy-chunk Lanczos of theta_top_free.py at B = 10^5 (top four eigenvalues to 3e-4).
"""
import os, sys, ctypes, subprocess, tempfile, time
import numpy as np

C_SRC = r'''
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <immintrin.h>
#include <omp.h>

#define MAXB 8
#define GOLD 0x9E3779B97F4A7C15ULL

static inline uint64_t mix64s(uint64_t z) {
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

typedef struct { __m512 cl, ch, sl, sh; __m512i tab6; } tabs_t;

static void make_tabs(int mode, tabs_t *t) {
    float c[32], s[32];
    for (int i = 0; i < 32; i++) { c[i] = 0.f; s[i] = 0.f; }
    if (mode == 0) {
        for (int k = 0; k < 6; k++) { c[k] = (float)cos(M_PI * k / 3.0); s[k] = (float)sin(M_PI * k / 3.0); }
    } else {
        for (int k = 0; k < 32; k++) { c[k] = (float)cos(2.0 * M_PI * k / 32.0); s[k] = (float)sin(2.0 * M_PI * k / 32.0); }
    }
    t->cl = _mm512_loadu_ps(c); t->ch = _mm512_loadu_ps(c + 16);
    t->sl = _mm512_loadu_ps(s); t->sh = _mm512_loadu_ps(s + 16);
    uint8_t m6[64];
    for (int i = 0; i < 64; i++) m6[i] = (uint8_t)(i % 6);
    t->tab6 = _mm512_loadu_si512((const void *)m6);
}

/* phase 0: phase index bytes kb[] and nonzero masks nz[] of one row */
static inline void gen_codes(const int8_t *T, int64_t S, int64_t nblk, const int32_t *li, int nj, int mode,
                             uint64_t seedz, const tabs_t *t, uint8_t *kb, uint64_t *nz) {
    const __m512i m7 = _mm512_set1_epi8(7), m40 = _mm512_set1_epi8(0x40), m31 = _mm512_set1_epi8(31);
    const __m512i lane = _mm512_set_epi64(7 * GOLD, 6 * GOLD, 5 * GOLD, 4 * GOLD, 3 * GOLD, 2 * GOLD, GOLD, 0);
    const __m512i c1 = _mm512_set1_epi64((long long)0xBF58476D1CE4E5B9ULL);
    const __m512i c2 = _mm512_set1_epi64((long long)0x94D049BB133111EBULL);
    for (int64_t blk = 0; blk < nblk; blk++) {
        int64_t off = blk * 64;
        __mmask64 valid = (off + 64 <= S) ? ~(__mmask64)0 : ((((__mmask64)1) << (S - off)) - 1);
        __m512i sum = _mm512_setzero_si512(), orv = _mm512_setzero_si512();
        for (int j = 0; j < nj; j++) {
            __m512i x = _mm512_maskz_loadu_epi8(valid, T + (int64_t)li[j] * S + off);
            sum = _mm512_add_epi8(sum, _mm512_and_si512(x, m7));
            orv = _mm512_or_si512(orv, x);
        }
        __mmask64 zm = _mm512_test_epi8_mask(orv, m40);
        nz[blk] = (~zm) & valid;
        __m512i k;
        if (mode == 0) {
            k = _mm512_permutexvar_epi8(sum, t->tab6);
        } else {
            __m512i x = _mm512_add_epi64(_mm512_set1_epi64((long long)(seedz + (uint64_t)blk * 8ULL * GOLD)), lane);
            x = _mm512_mullo_epi64(_mm512_xor_si512(x, _mm512_srli_epi64(x, 30)), c1);
            x = _mm512_mullo_epi64(_mm512_xor_si512(x, _mm512_srli_epi64(x, 27)), c2);
            x = _mm512_xor_si512(x, _mm512_srli_epi64(x, 31));
            k = _mm512_and_si512(x, m31);
        }
        _mm512_storeu_si512((void *)(kb + off), k);
    }
}

#define LOADCS(o, blk, g)                                                                                      \
    __m512i idx = _mm512_cvtepu8_epi32(_mm_loadu_si128((const __m128i *)(kb + (o))));                          \
    __mmask16 mk = (__mmask16)(nz[blk] >> (16 * (g)));                                                         \
    __m512 cs = _mm512_maskz_permutex2var_ps(mk, t->cl, idx, t->ch);                                           \
    __m512 sn = _mm512_maskz_permutex2var_ps(mk, t->sl, idx, t->sh);

static inline __attribute__((always_inline)) void phase1(const uint8_t *kb, const uint64_t *nz, int64_t nblk,
        int64_t Sp, const float *V, const tabs_t *t, const int b, float *yr, float *yi) {
    __m512 ar[MAXB], ai[MAXB];
    for (int j = 0; j < b; j++) { ar[j] = _mm512_setzero_ps(); ai[j] = _mm512_setzero_ps(); }
    for (int64_t blk = 0; blk < nblk; blk++) {
        for (int g = 0; g < 4; g++) {
            int64_t o = blk * 64 + 16 * g;
            LOADCS(o, blk, g)
            for (int j = 0; j < b; j++) {
                __m512 vr = _mm512_loadu_ps(V + (int64_t)(2 * j) * Sp + o);
                __m512 vi = _mm512_loadu_ps(V + (int64_t)(2 * j + 1) * Sp + o);
                ar[j] = _mm512_fmadd_ps(cs, vr, ar[j]);
                ar[j] = _mm512_fnmadd_ps(sn, vi, ar[j]);
                ai[j] = _mm512_fmadd_ps(sn, vr, ai[j]);
                ai[j] = _mm512_fmadd_ps(cs, vi, ai[j]);
            }
        }
    }
    for (int j = 0; j < b; j++) { yr[j] = _mm512_reduce_add_ps(ar[j]); yi[j] = _mm512_reduce_add_ps(ai[j]); }
}

static inline __attribute__((always_inline)) void phase2(const uint8_t *kb, const uint64_t *nz, int64_t nblk,
        int64_t Sp, float *Wl, const tabs_t *t, const int b, const float *yrs, const float *yis) {
    __m512 yr[MAXB], yi[MAXB];
    for (int j = 0; j < b; j++) { yr[j] = _mm512_set1_ps(yrs[j]); yi[j] = _mm512_set1_ps(yis[j]); }
    for (int64_t blk = 0; blk < nblk; blk++) {
        for (int g = 0; g < 4; g++) {
            int64_t o = blk * 64 + 16 * g;
            LOADCS(o, blk, g)
            for (int j = 0; j < b; j++) {
                float *pr = Wl + (int64_t)(2 * j) * Sp + o, *pi = Wl + (int64_t)(2 * j + 1) * Sp + o;
                __m512 wr = _mm512_loadu_ps(pr), wi = _mm512_loadu_ps(pi);
                wr = _mm512_fmadd_ps(cs, yr[j], wr);
                wr = _mm512_fmadd_ps(sn, yi[j], wr);
                wi = _mm512_fmadd_ps(cs, yi[j], wi);
                wi = _mm512_fnmadd_ps(sn, yr[j], wi);
                _mm512_storeu_ps(pr, wr); _mm512_storeu_ps(pi, wi);
            }
        }
    }
}

static inline int64_t popnz(const uint64_t *nz, int64_t nblk) {
    int64_t c = 0;
    for (int64_t i = 0; i < nblk; i++) c += __builtin_popcountll(nz[i]);
    return c;
}

/* mode_fwd = 0: W += conj(e)^T (w e V) with w = 1 (or 1 / #nonzero entries of the row when normalize);
   mode_fwd = 1: store y = e V in Y[(2j + c) * ldy + slot] and nothing else */
static inline __attribute__((always_inline)) void row_apply(const uint8_t *kb, const uint64_t *nz, int64_t nblk,
        int64_t Sp, const float *V, float *Wl, const tabs_t *t, const int b, int normalize, int fwd,
        float *Y, int64_t ldy, int64_t slot) {
    float yr[MAXB], yi[MAXB];
    phase1(kb, nz, nblk, Sp, V, t, b, yr, yi);
    if (fwd) {
        for (int j = 0; j < b; j++) { Y[(int64_t)(2 * j) * ldy + slot] = yr[j]; Y[(int64_t)(2 * j + 1) * ldy + slot] = yi[j]; }
        return;
    }
    if (normalize) {
        float inv = 1.0f / (float)popnz(nz, nblk);
        for (int j = 0; j < b; j++) { yr[j] *= inv; yi[j] *= inv; }
    }
    phase2(kb, nz, nblk, Sp, Wl, t, b, yr, yi);
}

static void row_dispatch(const uint8_t *kb, const uint64_t *nz, int64_t nblk, int64_t Sp, const float *V, float *Wl,
                         const tabs_t *t, int b, int normalize, int fwd, float *Y, int64_t ldy, int64_t slot) {
    switch (b) {
        case 1: row_apply(kb, nz, nblk, Sp, V, Wl, t, 1, normalize, fwd, Y, ldy, slot); break;
        case 2: row_apply(kb, nz, nblk, Sp, V, Wl, t, 2, normalize, fwd, Y, ldy, slot); break;
        case 3: row_apply(kb, nz, nblk, Sp, V, Wl, t, 3, normalize, fwd, Y, ldy, slot); break;
        case 4: row_apply(kb, nz, nblk, Sp, V, Wl, t, 4, normalize, fwd, Y, ldy, slot); break;
        case 5: row_apply(kb, nz, nblk, Sp, V, Wl, t, 5, normalize, fwd, Y, ldy, slot); break;
        case 6: row_apply(kb, nz, nblk, Sp, V, Wl, t, 6, normalize, fwd, Y, ldy, slot); break;
        case 7: row_apply(kb, nz, nblk, Sp, V, Wl, t, 7, normalize, fwd, Y, ldy, slot); break;
        default: row_apply(kb, nz, nblk, Sp, V, Wl, t, 8, normalize, fwd, Y, ldy, slot); break;
    }
}

/* W = sum_z conj(e_z)^T (w_z e_z V) over rows z in the list rows[0..nrows) (NULL: all rows 0..R), w_z = 1 or, with
   normalize, 1 / (number of nonzero entries of row z) -- the unit-diagonal Gram.  V, W planar [b][2][Sp].
   fwd != 0: instead Y[(2j + c) * ny + q] = (e_{rows[q]} V_j) (real / imaginary part), W unused. */
void normal_matvec(const int8_t *T, int64_t S, int64_t Sp, const int32_t *LOC, int64_t R, int J, const int64_t *rows,
                   int64_t nrows, const float *V, int b, float *W, int mode, uint64_t seed, int nthreads, int normalize,
                   int fwd, float *Y) {
    int64_t nblk = Sp / 64;
    int64_t wlen = (int64_t)2 * b * Sp;
    if (!fwd) memset(W, 0, sizeof(float) * wlen);
    int64_t nr = rows ? nrows : R;
    tabs_t t;
    make_tabs(mode, &t);
    #pragma omp parallel num_threads(nthreads)
    {
        uint8_t *kb = (uint8_t *)aligned_alloc(64, (size_t)Sp);
        uint64_t *nz = (uint64_t *)malloc(sizeof(uint64_t) * (size_t)nblk);
        float *Wl = (float *)aligned_alloc(64, sizeof(float) * (size_t)wlen);
        memset(Wl, 0, sizeof(float) * wlen);
        tabs_t tl = t;
        #pragma omp for schedule(dynamic, 4) nowait
        for (int64_t q = 0; q < nr; q++) {
            int64_t z = rows ? rows[q] : q;
            int32_t li[16]; int nj = 0;
            for (int j = 0; j < J && nj < 16; j++) { int32_t l = LOC[z * J + j]; if (l >= 0) li[nj++] = l; }
            uint64_t seedz = mix64s(seed * 0x2545F4914F6CDD1DULL + (uint64_t)(z + 1) * GOLD);
            gen_codes(T, S, nblk, li, nj, mode, seedz, &tl, kb, nz);
            row_dispatch(kb, nz, nblk, Sp, V, Wl, &tl, b, normalize, fwd, Y, nr, q);
        }
        if (!fwd) {
            #pragma omp critical
            { for (int64_t i = 0; i < wlen; i++) W[i] += Wl[i]; }
        }
        free(kb); free(nz); free(Wl);
    }
}

/* the complex entries of row z (for tests): out_re, out_im of length S */
void row_entries(const int8_t *T, int64_t S, int64_t Sp, const int32_t *LOC, int J, int64_t z, int mode,
                 uint64_t seed, float *out_re, float *out_im) {
    int64_t nblk = Sp / 64;
    tabs_t t;
    make_tabs(mode, &t);
    uint8_t *kb = (uint8_t *)aligned_alloc(64, (size_t)Sp);
    uint64_t *nz = (uint64_t *)malloc(sizeof(uint64_t) * (size_t)nblk);
    int32_t li[16]; int nj = 0;
    for (int j = 0; j < J && nj < 16; j++) { int32_t l = LOC[z * J + j]; if (l >= 0) li[nj++] = l; }
    uint64_t seedz = mix64s(seed * 0x2545F4914F6CDD1DULL + (uint64_t)(z + 1) * GOLD);
    gen_codes(T, S, nblk, li, nj, mode, seedz, &t, kb, nz);
    float c[32], s[32];
    for (int i = 0; i < 32; i++) { c[i] = 0.f; s[i] = 0.f; }
    if (mode == 0) { for (int k = 0; k < 6; k++) { c[k] = (float)cos(M_PI * k / 3.0); s[k] = (float)sin(M_PI * k / 3.0); } }
    else { for (int k = 0; k < 32; k++) { c[k] = (float)cos(2.0 * M_PI * k / 32.0); s[k] = (float)sin(2.0 * M_PI * k / 32.0); } }
    for (int64_t x = 0; x < S; x++) {
        int on = (nz[x / 64] >> (x % 64)) & 1;
        out_re[x] = on ? c[kb[x]] : 0.f;
        out_im[x] = on ? s[kb[x]] : 0.f;
    }
    free(kb); free(nz);
}
'''

_LIB = None


def _load():
    global _LIB
    if _LIB is not None:
        return _LIB
    d = tempfile.mkdtemp(prefix='thetak_')
    src = os.path.join(d, 'k.c'); so = os.path.join(d, 'k.so')
    with open(src, 'w') as f:
        f.write(C_SRC)
    subprocess.check_call(['gcc', '-O3', '-march=native', '-fopenmp', '-shared', '-fPIC', '-o', so, src, '-lm'])
    lib = ctypes.CDLL(so)
    P = ctypes.c_void_p
    lib.normal_matvec.argtypes = [P, ctypes.c_int64, ctypes.c_int64, P, ctypes.c_int64, ctypes.c_int, P,
                                  ctypes.c_int64, P, ctypes.c_int, P, ctypes.c_int, ctypes.c_uint64, ctypes.c_int, ctypes.c_int,
                                  ctypes.c_int, P]
    lib.normal_matvec.restype = None
    lib.row_entries.argtypes = [P, ctypes.c_int64, ctypes.c_int64, P, ctypes.c_int, ctypes.c_int64, ctypes.c_int,
                                ctypes.c_uint64, P, P]
    lib.row_entries.restype = None
    _LIB = lib
    for f in (src, so):
        try:
            os.remove(f)
        except OSError:
            pass
    try:
        os.rmdir(d)
    except OSError:
        pass
    return lib


class Kernel:
    def __init__(self, T, LOC, nthreads=3):
        self.lib = _load()
        self.T = np.ascontiguousarray(T, dtype=np.int8)
        self.LOC = np.ascontiguousarray(LOC, dtype=np.int32)
        self.nu, self.S = self.T.shape
        self.R, self.J = self.LOC.shape
        self.Sp = -(-self.S // 64) * 64
        self.nthreads = nthreads
        self.nmatvec = 0

    def _nt(self, nrows):
        """threads for a call over nrows rows: small row sets are faster on one thread (fork/join cost)."""
        return self.nthreads if (nrows or self.R) * self.S >= 3e7 else 1

    def _call(self, Vp, b, mode, seed, rows=None, normalize=False):
        Wp = np.empty_like(Vp)
        if rows is None:
            rp, nr = None, 0
        else:
            rows = np.ascontiguousarray(rows, dtype=np.int64)
            rp, nr = rows.ctypes.data, len(rows)
        self.lib.normal_matvec(self.T.ctypes.data, self.S, self.Sp, self.LOC.ctypes.data, self.R, self.J, rp, nr,
                               Vp.ctypes.data, b, Wp.ctypes.data, mode, ctypes.c_uint64(seed), self._nt(nr),
                               int(normalize), 0, None)
        self.nmatvec += b
        return Wp

    def _pack(self, V):
        V = np.asarray(V)
        if V.ndim == 1:
            V = V[:, None]
        b = V.shape[1]
        assert 1 <= b <= 8
        Vp = np.zeros((b, 2, self.Sp), np.float32)
        Vp[:, 0, :self.S] = V.real.T
        Vp[:, 1, :self.S] = V.imag.T
        return Vp, b

    def matmat(self, V, mode=0, seed=0, rows=None, normalize=False):
        """E^H E V for V of shape (S, b), b <= 8; returns complex128 (S, b).  rows: optional row subset; normalize: use the
        rows scaled to unit norm, i.e. the unit-diagonal Gram of the subset (E_W^H D^-1 E_W)."""
        Vp, b = self._pack(V)
        Wp = self._call(Vp, b, mode, seed, rows, normalize)
        out = Wp[:, 0, :self.S].astype(np.float64) + 1j * Wp[:, 1, :self.S].astype(np.float64)
        return out.T

    def matvec(self, v, mode=0, seed=0, rows=None, normalize=False):
        return self.matmat(np.asarray(v).reshape(-1, 1), mode, seed, rows, normalize)[:, 0]

    def forward(self, V, mode=0, seed=0, rows=None):
        """E V (rows of the subset, in the order given) for V of shape (S, b); returns complex128 (nrows, b)."""
        Vp, b = self._pack(V)
        if rows is None:
            rp, nr = None, self.R
        else:
            rows = np.ascontiguousarray(rows, dtype=np.int64)
            rp, nr = rows.ctypes.data, len(rows)
        Y = np.zeros((b, 2, nr), np.float32)
        self.lib.normal_matvec(self.T.ctypes.data, self.S, self.Sp, self.LOC.ctypes.data, self.R, self.J, rp, nr,
                               Vp.ctypes.data, b, None, mode, ctypes.c_uint64(seed), self._nt(nr), 0, 1, Y.ctypes.data)
        return (Y[:, 0, :].astype(np.float64) + 1j * Y[:, 1, :].astype(np.float64)).T

    def row(self, z, mode=0, seed=0):
        re = np.empty(self.S, np.float32); im = np.empty(self.S, np.float32)
        self.lib.row_entries(self.T.ctypes.data, self.S, self.Sp, self.LOC.ctypes.data, self.J, z, mode,
                             ctypes.c_uint64(seed), re.ctypes.data, im.ctypes.data)
        return re.astype(np.float64) + 1j * im.astype(np.float64)

    def top(self, k=4, mode=0, seed=0, tol=1e-4, ncv=None, maxiter=None, log=None, rows=None, normalize=False,
            vectors=False):
        """top k eigenvalues of E^H E / S, descending (ARPACK Lanczos on the compiled operator); with rows, those of the
        row subset (with normalize: of its unit-diagonal Gram, divided by 1 instead of S).  vectors: also return the
        eigenvectors (columns, S x k, same order)."""
        from scipy.sparse.linalg import eigsh, LinearOperator
        op = LinearOperator((self.S, self.S), matvec=lambda v: self.matvec(v, mode, seed, rows, normalize),
                            dtype=np.complex128)
        t0 = time.time()
        n0 = self.nmatvec
        v0 = np.random.default_rng(12345).standard_normal(self.S) + 0j
        res = eigsh(op, k=k, which='LA', return_eigenvectors=vectors, tol=tol, ncv=ncv, maxiter=maxiter, v0=v0)
        if log:
            log('    (%d matvecs, %.0fs)' % (self.nmatvec - n0, time.time() - t0))
        scale = 1.0 if normalize else float(self.S)
        if vectors:
            ev, vec = res
            o = np.argsort(-ev)
            return ev[o] / scale, vec[:, o]
        return np.sort(res)[::-1] / scale
