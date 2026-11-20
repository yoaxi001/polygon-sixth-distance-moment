# 中心对称凸多边形的六次距离矩

设 $K$ 是面积为 1 的中心对称凸 $n$ 边形，$n=2m\ge4$。把对称中心平移到原点，记 $R$ 为以原点为中心、同面积的正 $n$ 边形。研究的量是

$$
E(K)=\int_K\int_K |x-y|^6\,dy\,dx,\qquad
M_j(K)=\int_K |x|^j\,dx.
$$

目标是证明 $E(K)\ge E(R)$，并确定何时取等。由于面积是 1，$E(K)$ 也等于两个独立均匀随机点之间距离六次方的期望。

## Lean 已验证的结论

[主定理 `SixthMoment.polygon_sixth_moment_with_equality`](Equality.lean) 接受一个明确的几何前提。对每个同面积的凸 $n$ 边形 $S$ 和每个以原点为圆心的圆盘 $D$，要求

$$
|S\cap D|\le |R\cap D|.
$$

在此前提下，Lean 证明 $E(R)≤E(K)$，且等号成立当且仅当 $K$ 是 $R$ 的一个旋转和平移。定理允许 $K$ 的对称中心位于任意位置。代码用 `disk s` 表示半径平方为 $s$ 的闭圆盘，用 `moment K k` 表示 $M_{2k}(K)$。

几何前提取自 Bogosel、Bucur、Fragalà 的多边形 Hardy–Littlewood 不等式，将核函数取为圆盘的示性函数即可。论文表述中的区域边界和此处使用的闭凸包相差零面积。该文定理 5 处理一般多边形的二次和四次距离矩，引理 7 列出若干更高次情形。[原论文，第 2 节定理 5、6 及引理 7](https://arxiv.org/html/2302.11677v1#S2)

| Lean 中的定理 | 验证内容 |
| --- | --- |
| `energy_expand`、`mixed_bound` | 展开六次距离积分，通过两个正定二次型控制混合项 |
| `radialBound_of_linear_images` | 把行列式为 1 的线性像上的径向矩比较转化为正定二次型估计 |
| `moment_le_of_diskDominates` | 用分层积分从圆盘重叠面积比较推出每个正偶数阶的径向矩比较 |
| `energy_of_disk_comparison` | 得到定量估计 $E(K)-E(R)\ge 2[M_6(K)-M_6(R)]\ge 0$ |
| `isotropic_regular` | 从正多边形的顶点和旋转对称性证明二阶矩阵是标量矩阵 |
| `equal_disk_overlaps` | 在面积相同及圆盘重叠比较的条件下，一个正偶数阶径向矩相等就足以推出每个半径的重叠面积相等 |
| `open_disk_subset_of_equal_moment` | 若闭圆盘包含在 $R$ 中，则等号迫使它的开圆盘包含在 $K$ 中 |
| `disk_subset_of_open_disk_subset` | $K$ 为闭集且包含一个正半径开圆盘时，它也包含相应的闭圆盘 |
| `tangent_sum_rigidity` | 对外法向夹角的一半应用正切函数的 Jensen 不等式，并证明等号当且仅当各角相等 |
| `eq_of_nested_equal_area` | 面积为正的紧凸集和其中的等面积闭子集必然相等 |
| `energy_rotate`、`energy_translate` | 旋转和平移保持六次距离矩 |

## 等号如何迫使多边形为正

把对称中心平移到原点。若能量取等，每个同心圆盘与两个多边形的重叠面积都相等。因此 $K$ 包含 $R$ 的内切圆盘，并且位于 $R$ 的外接圆盘内。设外接圆半径为 $ρ$，则内切圆半径为 $ρ\cos(π/n)$。

对任意方向，把所有顶点投影到该方向。为使凸包覆盖内切圆盘，至少一个顶点的投影必须达到内切圆半径。由于顶点距离原点至多为 $ρ$，该顶点的方向与给定方向之间的夹角至多为 $π/n$。于是相邻顶点方向的间隔至多是 $2π/n$。全部 $n$ 个间隔之和为 $2π$，所以每个间隔恰好是 $2π/n$。

将 $R$ 旋转到使顶点方向重合。$K$ 的每个顶点都在原点与 $R$ 的对应顶点之间，因此 $K$ 整体包含在旋转后的 $R$ 中。两者是等面积的闭凸多边形，故它们相等。反方向由旋转和平移保持距离能量得到。

这条等号证明已在 Lean 中接通。独立复验文献前提仍需形式化 Bogosel、Bucur、Fragalà 的圆盘重叠定理。当前代码将它明确列为 `PolygonDiskComparison` 参数。

## 复验

项目固定使用 Lean 4.19.0 和 mathlib v4.19.0。已安装 Lean 和 Git 的环境中，在本目录依次运行

```sh
lake update
lake exe cache get
lake build
```

证明文件结尾用 `#print axioms` 输出主定理的公理依赖。预期只列出 `propext`、`Classical.choice`、`Quot.sound`。
