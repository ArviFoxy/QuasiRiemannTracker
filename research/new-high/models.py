"""Registry of HIGH-gate models for flow_new.py (None = the original gates.high_gate)."""
MODELS = {
    'orig': None,
    'gen': {},                       # generalized solver, no change (must reproduce 'orig')
}
# sensitivity probes: a uniform bonus to the detector root xi at saturated classes
for d in (1e-3, 2e-3, 5e-3, 1e-2):
    MODELS[f'dxi{d:g}'] = {'dxi': d, 'dxi_pmin': 0.0}
# long-branch slope kL (5/6 = sixth-power amplification of (204))
for k in (0.82, 0.80, 0.78, 0.75):
    MODELS[f'kL{k:g}'] = {'kL': k}
# inverse slot cost cI (2 = Theorem 7.3)
for c in (1.9, 1.8, 1.5):
    MODELS[f'cI{c:g}'] = {'cI': c}
for d in (2e-2, 5e-2):
    MODELS[f'dxi{d:g}'] = {'dxi': d, 'dxi_pmin': 0.0}
