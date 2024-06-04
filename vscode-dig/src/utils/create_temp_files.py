import sys
import json
import re
from pathlib import Path

def extract_assertions(file_path):
    with open(file_path, 'r') as file:
        lines = file.readlines()

    assertion_lines = []
    for i, line in enumerate(lines):
        if 'assert' in line and not line.strip().startswith('#include'):
            assertion_lines.append(i)

    return lines, assertion_lines

def write_assertion_file(base_path, lines, assertion_index, index):
    file_path = f"{base_path}_assert_{index}.c"
    with open(file_path, 'w') as file:
        headers = [line for line in lines if line.strip().startswith('#include')]
        
        assert_header_present = any('#include <assert.h>' in header for header in headers)
        
        for header in headers:
            file.write(header)
        
        if not assert_header_present:
            file.write("#include <assert.h>\n")
        
        for i, line in enumerate(lines):
            if line.strip().startswith('#include'):
                continue
            if 'assert' in line and not line.strip().startswith('#include') and i != assertion_index:
                continue
            file.write(line)
    
    print(f"Created temp file: {file_path}", file=sys.stderr)
    return file_path

def main(file_path):
    lines, assertion_indices = extract_assertions(file_path)
    base_path = file_path.replace('.c', '')
    symexefiles = [
        write_assertion_file(base_path, lines, assert_index, i)
        for i, assert_index in enumerate(assertion_indices)
    ]
    print(json.dumps(symexefiles))  # Output as JSON

if __name__ == "__main__":
    main(sys.argv[1])
