#!/usr/bin/env python3
"""Inline the captured Macaulay2 transcripts into the worked-examples page.

The page is not written by hand with its outputs pasted in: page.template.html
carries the prose, and its markers are filled in here from what Macaulay2
actually printed, so a re-run of examples/run.sh cannot leave the published
page quoting output that is no longer produced.

    @@session <name> | <expr> ; <expr> ; ...@@
        The whole transcript, folded into a <details> element.  Each <expr> is
        looked up among the session's inputs and its printed value shown in the
        summary, so the headline results stay visible while the session itself
        is one click away.  An expression that is not in the transcript, or
        whose value Macaulay2 renders over several lines (a fraction, a
        matrix), is an error rather than a silently dropped chip.
    @@seconds <name>@@       the wall time examples/run.sh recorded
    @@sourcelines <name>@@   the length of the input script

Usage: examples/build-page.py <output.html>
"""
import html
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def read(name, extension):
    with io.open(os.path.join(HERE, name + extension), encoding="utf-8") as f:
        return f.read()


def session_values(name, lines):
    """Map each single-line input to the value Macaulay2 printed for it.

    Macaulay2 numbers its inputs and outputs in step, so the value belonging
    to `i14 : ...` is on the `o14 = ...` line.  A value rendered over several
    lines -- 1/2 is drawn as a fraction across three -- is left out here; the
    caller reports asking for one as an error, since a chip showing only the
    middle line of a fraction would be worse than no chip.
    """
    inputs, outputs = {}, {}
    for i, line in enumerate(lines):
        entered = re.match(r"^i(\d+) : (.*)$", line)
        if entered:
            inputs[entered.group(1)] = entered.group(2)
            continue
        printed = re.match(r"^o(\d+) = (.*)$", line)
        if printed:
            above = lines[i - 1] if i else ""
            below = lines[i + 1] if i + 1 < len(lines) else ""
            if above.strip() or (below.strip()
                    and not below.startswith("o" + printed.group(1) + " :")):
                continue  # rendered over several lines
            outputs[printed.group(1)] = printed.group(2)
    return {text: outputs[n] for n, text in inputs.items() if n in outputs}


def session(name, wanted):
    text = read(name, ".out").rstrip("\n")
    if "error:" in text:
        raise SystemExit("%s.out contains a Macaulay2 error" % name)
    lines = text.split("\n")
    values = session_values(name, lines)
    chips = []
    for expression in [w.strip() for w in wanted.split(";") if w.strip()]:
        if expression not in values:
            raise SystemExit("%s.out has no single-line value for %r"
                % (name, expression))
        chips.append('<span class="chip"><code>%s</code><b>%s</b></span>'
            % (html.escape(expression), html.escape(values[expression])))
    count = sum(1 for line in lines if re.match(r"^i\d+ : ", line))
    return (
        '<details class="session">\n'
        '<summary><span class="what">Macaulay2 session, %d inputs</span>%s</summary>\n'
        '<pre class="m2">%s</pre>\n'
        '</details>' % (count, "".join(chips), html.escape(text)))


HANDLERS = {
    "seconds": lambda name: read(name, ".time").strip(),
    "sourcelines": lambda name: str(len(read(name, ".m2").splitlines())),
}


def main():
    if len(sys.argv) != 2:
        raise SystemExit(__doc__)
    page = read("page", ".template.html")
    page = re.sub(r"@@session ([\w.-]+) \|([^@]*)@@",
        lambda m: session(m.group(1), m.group(2)), page)
    page = re.sub(r"@@(\w+) ([\w.-]+)@@",
        lambda m: HANDLERS[m.group(1)](m.group(2)), page)
    left = re.search(r"@@[^@]*@@", page)
    if left:
        raise SystemExit("unsubstituted marker: " + left.group(0))
    directory = os.path.dirname(os.path.abspath(sys.argv[1]))
    if not os.path.isdir(directory):
        os.makedirs(directory)
    with io.open(sys.argv[1], "w", encoding="utf-8") as f:
        f.write(page)
    print("wrote " + sys.argv[1])


main()
