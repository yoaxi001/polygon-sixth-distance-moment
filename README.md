# Minimum sixth distance moment of centrally symmetric polygons

Among centrally symmetric convex polygons of area one with a fixed number of sides, the regular polygon minimizes the expected sixth power of the distance between two independent uniform points. Equality holds exactly for its rotations and translations.

[中文证明说明](README.zh-CN.md) · [Lean theorem](Equality.lean#L41) · [数学课题目录](https://github.com/yoaxi001/math-projects)

For an even integer $n \ge 4$, let $R_n$ be the regular area-one $n$-gon. For every centrally symmetric convex area-one $n$-gon $K$,

$$
\int_K\int_K |x-y|^6\,dy\,dx \;\ge\;
\int_{R_n}\int_{R_n}|x-y|^6\,dy\,dx.
$$

**Verification scope.** The Lean proof, developed with AI assistance, takes the polygonal disk-overlap inequality as an explicit hypothesis named `PolygonDiskComparison`. Starting from it, Lean checks the distance inequality and both directions of the equality classification. The geometric input is the disk-indicator case of Bogosel, Bucur and Fragalà’s [Theorem 6](https://arxiv.org/html/2302.11677v1#S2).

## Reproduce the proof

With Lean’s toolchain manager and Git installed, run these commands in the repository. The project pins Lean and mathlib to version 4.19.0.

```sh
lake update
lake exe cache get
lake build
```

The final theorem is `SixthMoment.polygon_sixth_moment_with_equality`. Its axiom report lists `propext`, `Classical.choice` and `Quot.sound`. The disk-overlap hypothesis appears directly in its statement.
