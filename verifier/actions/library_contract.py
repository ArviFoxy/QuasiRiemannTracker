"""Bind setup-built libraries into the prepared contract before proof execution."""
import hashlib, json, os

def write_readonly(path, data):
    temporary = path.with_name(path.name + '.new')
    temporary.write_bytes(data)
    temporary.chmod(0o444)
    os.replace(temporary, path)

def bind_libraries(prepared, inventory):
    data = (json.dumps(inventory, sort_keys=True) + '\n').encode()
    contract = json.loads((prepared/'contract.json').read_text())
    contract['library_inventory_sha256'] = hashlib.sha256(data).hexdigest()
    write_readonly(prepared/'libraries.json', data)
    write_readonly(prepared/'contract.json', (json.dumps(contract, indent=2)+'\n').encode())
