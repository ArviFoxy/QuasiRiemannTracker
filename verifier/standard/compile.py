"""Compile a module DAG with separate writable state for each compiler process."""
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from pathlib import Path
import shutil


def compile_modules(order, dependencies, compile_one, *, jobs):
    pending = set(order)
    if len(pending) != len(order) or set(dependencies) != pending:
        raise ValueError('Invalid module build graph')
    if any(not set(deps) <= pending for deps in dependencies.values()):
        raise ValueError('Missing build dependency')
    done, running = set(), {}
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        while pending or running:
            for name in order:
                if len(running) >= jobs:
                    break
                if name in pending and set(dependencies[name]) <= done:
                    running[pool.submit(compile_one, name)] = name
                    pending.remove(name)
            if not running:
                raise ValueError('Cyclic module build graph')
            completed, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in completed:
                name = running.pop(future)
                future.result()
                done.add(name)


def publish_module(output, destination):
    # The sandbox supervisor has reaped the compiler and all descendants.
    # Copy only regular compiler products for this module into the read-only
    # dependency library presented to subsequent compiler processes.
    if not output.is_file() or output.is_symlink():
        raise ValueError('Compiler did not produce a regular olean')
    destination.parent.mkdir(parents=True, exist_ok=True)
    for suffix in ['', '.private', '.server']:
        product = Path(str(output) + suffix)
        if product.is_symlink():
            raise ValueError('Symlink compiler output')
        if product.exists():
            if not product.is_file():
                raise ValueError('Invalid compiler output')
            target = Path(str(destination) + suffix)
            if target.exists():
                raise ValueError('Duplicate compiler output')
            shutil.copyfile(product, target)
            target.chmod(0o444)
