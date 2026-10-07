"""Native arithmetic faults must not become mathematical-integer samples."""
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))

from data.prog import C, Prog
from data.traces import Inp


def build(tmp_path, text):
    source = tmp_path / "input.c"
    source.write_text(text)
    work = tmp_path / "work"
    work.mkdir()
    compiled = C(source, work)
    return compiled, Prog(str(compiled.traceexe), compiled.inp_decls,
                          compiled.inv_decls)


def test_instrumentation_supplies_stdio_header(tmp_path):
    compiled, prog = build(tmp_path, """
        #include <stdlib.h>
        void vtrace(int x) {}
        void mainQ(int x) { vtrace(x); }
        int main(int argc, char **argv) { mainQ(atoi(argv[1])); return 7; }
    """)
    # A normal nonzero return from main is not an arithmetic fault.
    assert prog._get_traces(Inp(("x",), (12,))) == ["vtrace; 12"]


def test_signed_overflow_discards_already_printed_trace(tmp_path):
    compiled, prog = build(tmp_path, """
        #include <stdio.h>
        #include <stdlib.h>
        void vtrace(int x) {}
        void mainQ(int x) {
            vtrace(x);
            fflush(stdout);
            x = x * 2;
            vtrace(x);
        }
        int main(int argc, char **argv) { mainQ(atoi(argv[1])); return 0; }
    """)
    overflow = 1073741824
    raw = subprocess.run([str(compiled.traceexe), str(overflow)],
                         capture_output=True, text=True)
    assert raw.returncode < 0
    assert raw.stdout == f"vtrace; {overflow}\n"
    assert prog._get_traces(Inp(("x",), (overflow,))) == []
    assert prog._get_traces(Inp(("x",), (12,))) == ["vtrace; 12", "vtrace; 24"]
