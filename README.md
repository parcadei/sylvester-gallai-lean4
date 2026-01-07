# Classical Sylvester-Gallai Theorem in Lean 4

Autonomous formalization of the classical Sylvester-Gallai theorem for the Euclidean plane.

## Theorem

```lean
theorem sylvester_gallai (S : Finset Plane)
  (h_card : 2 < #S)
  (h_not_collinear : ¬Collinear ℝ ↑S) :
  ∃ L, IsOrdinaryLine S L
```

Given a finite set of points in the plane (≥3 points), not all collinear, there exists an "ordinary line" passing through exactly two points.

## Statistics

| Metric | Value |
|--------|-------|
| Lines | ~1000 |
| Runtime | 6 hours |
| Sorry statements | 0 |
| Proof method | Kelly's extremal argument |

## Building

```bash
lake build Proofs.SylvesterGallai
```

## Files

- `Proofs/SylvesterGallai.lean` - Main theorem
- `Proofs/AreaProof.lean` - Helper lemmas (cross product, Lagrange identity)

## License

MIT
