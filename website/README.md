# Conformal Covariant Operators Website

This folder contains the standalone source for the interactive project-map
website of `ConformalCovariantOperators`.

The site includes:

- a short introduction to the Lean 4 formalization;
- the complete project map from the repository README;
- clickable nodes for all mapped Lean modules;
- an in-page source viewer backed by the files in `public/source`;
- search and direct GitHub source links.

## Local development

```bash
npm install
npm run dev
```

Then open <http://localhost:3000>.

## Production build

```bash
npm run build
```

The website was developed for the Conformal Covariant Operators project by
ZeTian Yan, Victor Xiao, and Tao Xu.
