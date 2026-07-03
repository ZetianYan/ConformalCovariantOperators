export const project = {
  title: 'Conformal Covariant Operators',
  shortTitle: 'CCO',
  description:
    'A Lean 4 formalization of conformal geometry, ambient constructions, Poincaré–Einstein geometry, renormalized invariants, and conformally covariant operators.',
  sourceRepository:
    'https://github.com/ZetianYan/ConformalCovariantOperators',
  sourceBranch: 'main',
  license: 'Apache-2.0',
}

export const navigation = [
  { label: 'Home', slug: '' },
  { label: 'Foundations', slug: 'foundations' },
  { label: 'FG Geometry', slug: 'fg' },
  { label: 'PE Geometry', slug: 'pe' },
  { label: 'Renormalization', slug: 'renormalization' },
  { label: 'Applications', slug: 'applications' },
] as const

export function sourceFile(path: string): string {
  return `${project.sourceRepository}/blob/${project.sourceBranch}/${path}`
}