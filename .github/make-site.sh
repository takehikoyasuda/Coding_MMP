#!/bin/sh
# Turn an installPackage html directory into a self-contained site.
#
# Macaulay2 writes those pages for a local installation: the stylesheet, the
# KaTeX scripts that render the mathematics, and every link to a core Macaulay2
# node are absolute paths into the M2 prefix.  Served from anywhere else they
# 404, leaving the pages unstyled with the mathematics as raw TeX.  This copies
# the style assets in beside the pages, repoints those paths at the copy, and
# sends the core-documentation links to macaulay2.com, which serves the same
# file names.
#
# An already-built worked-examples page may be given as a fifth argument.  It
# is copied in as examples.html before the rewriting loop, so that it picks up
# the same banner treatment as the generated pages; the manual pages then gain
# a link to it, and it gains one back to the manual.
#
# Usage: make-site.sh <html-dir> <out-dir> <package> <repo-url> [examples.html]
set -eu
HTML="$1"; OUT="$2"; PKG="$3"; REPO="$4"; EXAMPLES="${5-}"

PREFIX=$(M2 --no-readline -q -e 'print prefixDirectory; exit 0' < /dev/null | tail -1)
STYLE="${PREFIX}share/Macaulay2/Style"
[ -d "$STYLE" ] || { echo "no Style directory at $STYLE" >&2; exit 1; }

rm -rf "$OUT"; mkdir -p "$OUT"
cp -RL "$HTML"/. "$OUT"/
mkdir -p "$OUT/Style"
# -L, so that a Style tree assembled out of symlinks -- as the Debian and
# Ubuntu packages do for the bundled KaTeX -- is copied as plain files.  The
# Pages upload action tars the site with --dereference and stops on a link it
# cannot follow.
cp -RL "$STYLE"/. "$OUT/Style"/
find "$OUT" -type l -print -delete

if [ -n "$EXAMPLES" ]; then
  cp "$EXAMPLES" "$OUT/examples.html"
fi

CORE="https://macaulay2.com/doc/Macaulay2/share/doc/Macaulay2/"
BANNER_STYLE="margin:0 0 1.5em;padding:.75em 1em;border:1px solid #c9c9c9;background:#fbf7e8;font-family:sans-serif;font-size:90%;line-height:1.5"
NOTICE="<b>${PKG}</b> is a third-party research package. It is <b>not part of the Macaulay2 distribution</b> and has not been reviewed by it; these pages merely use Macaulay2's own documentation format. Source and installation instructions: <a href=\"${REPO}\">${REPO}</a>."
if [ -n "$EXAMPLES" ]; then
  TO_EXAMPLES=" Worked examples, with their Macaulay2 output: <a href=\"examples.html\">computed minimal model programs</a>."
else
  TO_EXAMPLES=""
fi
# The examples page is not one of the generated ones, so its banner points back
# at the manual rather than at itself.
TO_MANUAL=" Reference documentation: <a href=\"index.html\">the ${PKG} manual</a>."

for f in "$OUT"/*.html; do
  case "$(basename "$f")" in
    examples.html) LINK="$TO_MANUAL" ;;
    *)             LINK="$TO_EXAMPLES" ;;
  esac
  BANNER="<div style=\"${BANNER_STYLE}\">${NOTICE}${LINK}</div>"
  python3 - "$f" "$PREFIX" "$CORE" "$BANNER" <<'PY'
import sys, re, io
path, prefix, core, banner = sys.argv[1:5]
s = io.open(path, encoding="utf-8").read()
s = s.replace(prefix + "share/doc/Macaulay2/", core)
s = s.replace(prefix + "share/Macaulay2/Style/", "Style/")
s = re.sub(r"(<body[^>]*>)", lambda m: m.group(1) + banner, s, count=1)
io.open(path, "w", encoding="utf-8").write(s)
PY
done

echo "site: $OUT"
echo "remaining absolute prefix references: $(grep -o "$PREFIX" "$OUT"/*.html | wc -l | tr -d ' ')"
