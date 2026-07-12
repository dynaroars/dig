#!/bin/bash
# Publish web/frontend-classic/index.html to the gh-pages branch,
# which GitHub Pages serves at https://roars.dev/dig.
set -e
cd "$(dirname "$0")/.."

git fetch origin gh-pages
blob=$(git hash-object -w web/frontend-classic/index.html)
tree=$(printf '100644 blob %s\tindex.html\n' "$blob" | git mktree)

if [ "$tree" = "$(git rev-parse origin/gh-pages^{tree})" ]; then
    echo "gh-pages already up to date."
    exit 0
fi

commit=$(git commit-tree "$tree" -p origin/gh-pages \
         -m "Deploy frontend-classic/index.html ($(git rev-parse --short HEAD))")
git push origin "$commit":gh-pages
git branch -f gh-pages "$commit" 2>/dev/null || true
echo "Deployed: https://roars.dev/dig"
