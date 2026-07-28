#!/bin/bash
# Publish web/*.html to the gh-pages branch,
# which GitHub Pages serves at https://roars.dev/dig.
set -e
cd "$(dirname "$0")/.."

git fetch origin gh-pages
tree=$(for f in web/*.html; do
    printf '100644 blob %s\t%s\n' "$(git hash-object -w "$f")" "$(basename "$f")"
done | git mktree)

if [ "$tree" = "$(git rev-parse origin/gh-pages^{tree})" ]; then
    echo "gh-pages already up to date."
    exit 0
fi

commit=$(git commit-tree "$tree" -p origin/gh-pages \
         -m "Deploy frontend-classic ($(git rev-parse --short HEAD))")
git push origin "$commit":gh-pages
git branch -f gh-pages "$commit" 2>/dev/null || true
echo "Deployed: https://roars.dev/dig"
