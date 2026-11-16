# Kakeya — Core Proof DAG: 调和分析视角下的本质差异与形式化工程区分

在调和分析与关联几何（Incidence Geometry）中，以下操作通常被视为“本质相同”的常规处理：
- 绝对维数常数的变化（如 $4\times 10^6, 128000, \pi/4, 6\delta$）；
- 二进抽屉原理（dyadic pigeonholing）与带对数或 $\delta^\varepsilon$ 损失的子族/子 shading 精化（refinement）；
- 标准坐标图归一化（如限制在竖直方向图 $|d_3| \geq 1/2$、有界基点 $\|p_T\| \leq 4$、或裁剪到 $[-1, 1]^3$）；
- 为避免存在量词消去时丢失“同一构造对象”上下文而显式携带的传递证书（re-entry / provenance data）。

如果将上述常规操作全部视为等价，在 Core Proof DAG 的 18 个节点中，**真正与论文打印表述存在数学本质差异**的只有以下 4 处（涉及 5 个节点）。

---

### 一、具有数学本质差异的节点

#### 1. WZ2 Lemma 6.6 (`W2L6_6`)：绝对 slab 质量 vs. 含 $\delta^2 \#\mathbb T$ 的归一化质量与重数上界

- **论文打印假设**：要求水平 slab $\mathbb R^2 \times J$（$\delta^{1/2} \leq |J| \leq \delta^\varepsilon$）内的绝对质量满足
  $$
  \sum_{T \in \mathbb T} |Y(T) \cap (\mathbb R^2 \times J)| \geq \delta^\eta |J|,
  $$
  且覆盖数满足 $\mathcal N_{|J|}(E_Y \cap (\mathbb R^2 \times J)) \leq \delta^{-\eta} |J|^{-2+\sigma}$。
- **Lean 证明版本（`pure_wz2_lemma66_prepared_interval` / `pure_wz2_lemma66_normalized_interval`）**：要求的是相对于管族总体积的**归一化 slab 质量**
  $$
  \sum_{T \in \mathbb T} |Y_J(T)| \geq \frac{\pi}{4} \delta^{\eta/8 + 2} (\#\mathbb T) |J|,
  $$
  并附带点态重数上界 $\mu_{Y_J}(p) \leq (\delta/|J|)^{2-\sigma-\eta/8}\#\mathbb T$ 与 $\delta^{2-\sigma-\eta/4096}\#\mathbb T$。
- **数学原因（原文式 (6.7)–(6.8) 的质量转计数标度）**：
  - 记 $N = \#\mathbb T$，$M_J = \sum_{T \in \mathbb T} |Y(T) \cap (\mathbb R^2 \times J)|$，并定义该 slab 上的**相对质量密度**
    $$
    \theta_J := \frac{M_J}{|J| \sum_{T \in \mathbb T} |T|} \asymp \frac{M_J}{|J| \delta^2 N}.
    $$
    在 Lemma 6.6 的证明（WZ2 式 (6.7)–(6.8)）中，每根细管在 $\mathbb R^2 \times J$ 内的体积至多为 $O(\delta^2 |J|)$；因此将保留下来的质量分配到 $K$ 个局部区域 $S$ 后，由质量下界转出的细管计数下界是
    $$
    \#\mathbb T_S \gtrsim \delta^{O(\eta)} \frac{M_J}{K \delta^2 |J|} = \delta^{O(\eta)} \theta_J \, \frac{N}{K}.
    $$
    随后证明需要将 $\#\mathbb T_S$ 与顶层 CWA 在棱柱 $P_S$ 上给出的相对上界 $\#\mathbb T[P_S] \leq \delta^{-\eta} |P_S| N$ 比较并消去两侧的 $N$。要使这一步成立，必须保证相对密度满足 $\theta_J \gtrsim \delta^{O(\eta)}$（即 $M_J \gtrsim \delta^{O(\eta) + 2} N |J|$）。
  - 在 WZ1（方向分离 / Sticky Kakeya）中，方向分离与质量下界保证 $N \approx \delta^{-2}$（允许 $\delta^\varepsilon$ 损失），故 $\delta^2 N \approx 1$，绝对质量 $M_J \geq \delta^\eta |J|$ 与相对质量 $\theta_J \gtrsim \delta^\eta$ 是一回事。
  - 但在 WZ2（Assouad / CWA）中，三维空间的直线流形是 $4$ 维的，Definition 2.12 **没有方向分离假设，也没有约束 $N \lesssim \delta^{-2}$**（顶层 CWA、$\delta^\eta$-稠密性及 $E_Y$ 上的 AD 条件关于 $N$ 是齐次的，当 $N \gg \delta^{-2}$ 如 $N \asymp \delta^{-3}$ 时，绝对质量 $M_J \geq \delta^\eta |J|$ 仅能给出 $\theta_J \gtrsim \delta^{1+\eta}$，在式 (6.7)–(6.8) 中会多损失一个无法被 $\delta^{O(\eta)}$ 吸收的固定幂次）。因此，从 WZ1 迁移到 WZ2 时漏掉因子 $\sum_T |T| \asymp \delta^2 N$ 是真实的量纲/标度遗漏。（注：由于最终 Theorem 5.2 成立从而 $\sigma > 0$ 的极值配置在逻辑上为空集，讨论 Lemma 6.6 的重点在于其证明机制 (6.7)–(6.8) 所需的实际假设标度，而非构造真极值反例。）
  - 在 Proposition 6.5 的实际构造中，slab $J$ 是对 $\delta^\eta$-dense 的全局 shading（总质量 $\sum_T |Y(T)| \geq \delta^\eta \sum_T |T| \asymp \delta^{\eta+2} N$）由抽屉原理选出的，天然满足的正是相对质量下界 $\theta_J \gtrsim \delta^\eta$（即 $M_J \gtrsim \delta^{\eta+2} N |J|$），同时由 Proposition 6.2 提供了将体积下界转化为管数下界所需的点态重数上界。

---

#### 2. WZ2 Proposition 7.1 (`W2P7_1`) 及 Lemma 7.12 输入：单位长粗管 Tube Wolff vs. 纵向平移与斜率初值 $f(0)$

此处包含两个相互独立的几何问题（仓库中均已形式化构造反例）：

1. **细管沿支撑直线的纵向位置移动（为何需要长度 $32$ 的粗管测试）**：
   - **论文打印假设**：仅假设普通 Tube Wolff，即对每个半径 $r \in [\delta, 1]$ 的**单位线段粗管** $T_r$，有 $\#\mathbb T[T_r] \leq \delta^{-\eta} r^2 (\#\mathbb T)$。
   - **数学问题**：Section 7（Lemma 7.12）的证明在支撑直线的四维参数空间 $(a, b, c, d)$（直线方程 $(x,y,z) = (a+cz, b+dz, z)$）中进行 Katz–Tao 提取与 cinematic 估计，实际使用的是**参数空间 Frostman 界**
     $$
     \#\{T \in \mathbb T : \|p_T - p_{T_0}\|_\infty \leq r\} \lesssim \delta^{-\eta} r^2 (\#\mathbb T).
     $$
     然而 $\delta$-管是**单位线段**的 $\delta$-邻域。两根细管可以位于同一条支撑直线上（拥有完全相同的四维参数 $(a,b,c,d)$），但在单位球内沿该直线有纵向偏移（例如中心高度相差 $\sqrt{\delta}$）。此时，一根固定的**单位长度**粗管 $T_r$ 只能控制横向距离 $r$，无法在纵向包住所有参数距离 $\leq r$ 的细管段。
   - **反例（`exists_normalized_ordinary_tubeWolff_longitudinal_counterexample`）**：即便固定标准斜率 $f(z) = z$，在单位球内取中心高度偏移为 $w i$（$w = \sqrt{\delta}$）的 $n^5$ 根细管，它们对**所有正半径的单位长粗管**都满足 Tube Wolff 上界，但其扭曲投影面积仅为 $O(\sqrt{\delta}) \ll \delta^{1/4}$。
   - **Lean 的修正**：将 Proposition 7.1 的粗管测试修正为中心放大 $32$ 倍的粗管 $32 \cdot T_r$（`DilatedTubeWolffVolumeBound F 32`）。在有界竖直图中，长度 $32$ 的粗轴足以覆盖工作球内的整条支撑直线段，从而以常数 $128000 = 320 \cdot 20^2$ 严格推出参数 Frostman 界。
   - **对后续定理无影响**：在 Proposition 6.8 中，输入假设是对**任意凸集**成立的 CWA；中心放大 $32$ 倍的粗管依然是凸集，因此 CWA 直接给出所需的长度 $32$ 粗管测试上界，不会给 Proposition 6.8 或 Theorem 5.2 增加任何外加假设。

2. **斜率初值 $f(0)$ 的无界偏移与定量控制**：
   - 非退化条件 $1 \leq |f'(z)| \leq 2, |f''(z)| \leq 1/100$ 并未限制 $|f(0)|$。若 $|f(0)|$ 随 $\delta \to 0$ 任意增大，阈值 $\delta_0$ 无法一致选取（反例见 `not_pureWZ2UnrestrictedTubeWolffProjectionStatement`）。
   - Lean 在 Proposition 7.1 与 Proposition 6.8 中显式要求 $f(0) = 0$，并在上游 Lemma 6.7 中通过仿射剪切缩放
     $$
     A_s(x, y, z) = \bigl(k(x + sy), \, ky, \, z\bigr), \qquad s = f(0), \quad k = \frac{1}{4(1+|s|)},
     $$
     将斜率变成 $\tilde{f} = f - f(0)$（满足 $\tilde{f}(0) = 0$），且由恒等式 $\pi_{\tilde{f}}(A_s(x,y,z)) = (k(x+f(z)y), z)$ 使二维投影面积乘上因子 $k$、三维体积乘上 Jacobian $k^2$。
   - 注意仅靠代数恒等式还不够：由于三维体积缩放了 $k^2$，为了使重新成管后的密度与 CWA 常数损失能被预设的 $\delta^\varepsilon$ 吸收，必须有 $|f(0)|$ 的小幂增长上界 $1 + |f(0)| \leq \delta^{-a}$（$a \ll \varepsilon$）。这一定量上界由 Proposition 6.5 保留的源尺度构造关系（`exists_actual_terminal_slope_offset_cutoff_for_output_loss`）在选定阈值前严格提供。

---

#### 3. WZ2 Lemma 6.7 (`W2L6_7`)：上界指数符号 $\delta^{\sigma - \varepsilon}$ vs. 论文式 (6.11) 的 $\delta^{\sigma + \varepsilon}$

- **差异**：WZ2 论文式 (6.11) 将扭曲投影面积上界打印为 $|X_f(C)| \lesssim \delta^{\sigma + \varepsilon}$（Blueprint 卡片与 Lean 均写为 $\delta^{\sigma - \varepsilon}$）。
- **数学原因**：这是原论文引用 WZ1 Corollary 6.5 时的正负号笔误。每个固定高度 $z = t$ 的水平切片是 $(\delta, 1-\sigma, \delta^{-\varepsilon})_1$-ADset，其 $\delta$-覆盖数上界为 $\delta^{-\varepsilon} \delta^{-(1-\sigma)}$，乘以区间宽度 $O(\delta)$ 并对 $t \in [-1, 1]$ 积分，得到的上界是 $O(\delta^{\sigma - \varepsilon})$。当 $\delta \in (0, 1)$ 时，$\delta^{\sigma + \varepsilon} \ll \delta^{\sigma - \varepsilon}$ 是更强的上界，无法由切片覆盖数推出；而在 Section 6.5 中，只需取 $\varepsilon < \frac{3}{4}\sigma$ 即可与下界 $\delta^{\sigma/4}$ 产生矛盾。

---

#### 4. WZ1 Theorem 5.2 (`T5_2`) 与 WZ2 Lemma 2.13 (`W2L2_13`)：直线集中方向与定理角色

- **WZ1 Theorem 5.2 (`T5_2`)**：
  1. **正交直线与仿射直线的归属方向**：考虑点积差集合 $\{a \cdot (b_1 - b_2) : (a, b_1, b_2) \in H\}$（$a \in F, b_i \in G$）。若点积差不展开，则差向量 $b_1 - b_2$ 必须平行于某单位方向 $v$，这意味着端点集 $G$ 集中在某条方向为 $v$ 的**仿射直线** $b + \mathbb R v$ 附近；而系数 $a \in F$ 必须与 $v$ 近乎正交，即 $F$ 集中在**过原点的正交直线** $\mathbb R v^\perp$ 附近（若 $G$ 所在的仿射线不过原点，$F$ 必须过原点才能使点积差小）。WZ1 v2 论文原文及 Blueprint 卡片均将“过原点的线”和“仿射线”的归属印反了，Lean 的 `WZ1ProjectionDichotomyConclusion` 按正确方向定义。
  2. **接口与实际调用的区别**：完整一般二择一命题 `WZ1ProjectionDichotomyConclusion` 在仓库中仅作为命题定义（未证明）。Proposition 6.4 实际调用的是已证明的 `wz1_well_separated_projection_union`：输入三元组集合 $H \subseteq F \times G_1 \times G_2$ 已经过标准分离与度数均匀化预处理，且集中分支只需 $G_1$ 或 $G_2$ 之一集中在仿射线上。在调和分析看来，原定理针对单个集合 $G$（当 $G_1, G_2 \subseteq G$ 时，其中一个集中即蕴含 $G$ 集中），且从一般 $H \subseteq F \times G \times G$ 做分离与度数二进均匀化属于标准的几行抽屉原理归约，因此实际使用的定理具备完全相同的调和分析实质。
- **WZ2 Lemma 2.13 (`W2L2_13`)**：
  - 论文将其表述为“对每个请求尺度 $\rho_0 \in [\delta, 1]$，存在附近尺度 $\rho$ 与粗覆盖，使粗族与每个单位重缩放纤维均继承多尺度 CWA”的独立一般引理；Lean 中没有将这一继承性质单独抽成一个通用引理声明，而是在 Proposition 6.2 的构造内部直接为所选出的具体粗族与纤维建立多尺度证书。

---

### 二、表面声明复杂但调和分析本质完全相同的节点

其余节点在 Lean 中的主声明虽然带有较多字段或参数，但在调和分析意义下与论文定理**完全等价**：

1. **Proposition 6.2 (`W2P6_2`)、Proposition 6.3 (`W2P6_3`)、Proposition 6.4 (`W2P6_4`)、Proposition 6.5 (`W2P6_5`) 中的 `Reentry` / `RichTerminal` / `RetainedConstruction` 数据**：
   - 在论文中，证明在得到一个精化配置后，可以随时引用“由上述二进抽屉原理构造可知，重数在活跃格子上为常数 $\mu_{\mathrm{fine}}$”或“对所得粗族再次应用 Proposition 6.2”。
   - 在 Lean 中，若前一步只返回纯粹的存在性结论 $\exists (\mathbb T', Y')$，构造过程中的内部均匀性（如常数包重数、粗细交叉度、普通管与裁剪管之间的刚体转换 `PureWZ2PropStickyReentryData`、以及用于控制 $|f(0)|$ 的源尺度 $\delta_{\mathrm{source}}$）会在消去存在量词时丢失。因此 Lean 将这些构造副产物保留在记录类型中，向下游传递后再投影回论文面板结论。
2. **Proposition 6.3 (`W2P6_3`) 中平面映射 $V$ 的定义域 `planeMap : E_Y → S^2`**：
   - Lean 将 $V(p)$ 的定义域严格限制在 $p \in E_Y$ 上（而非整个 $\mathbb R^3$）。由于 $E_Y$ 之外原本就没有 shading 质量，在非空局部球内取 $E_Y$ 中的占优锚点与取任意环境中心在几何上只差常数倍半径。
3. **Lemma 7.12: cinematic assembly (`W2JetCount`) 中“每个局部参数 $(a,b,d)$ 选一根代表管”**：
   - Lean 的 `TubeFamily` 是带指标的有限族（允许不同指标拥有相同直线参数）。若不按折叠参数 $(a,b,d)$ 选代表管就直接平移复制，同一条 cinematic 曲线会叠加上千根重复指标的细管，破坏 $O(1)$ 分配重数上界（`12500000`）。先按参数聚类并各取一根源管代表，只是处理多重集指标的标准离散化步骤。
4. **WZ2 Theorem 7.13 (`T7_2`, `WZ2UniformC2Input`) 中预先固定 $M$ 与 $C_{\mathrm{KT}}$**：
   - Lean 将定义域归一化为 $[0,1]$，并在选择小尺度阈值 $\delta_0$ 前固定曲线族的绝对 $C^2$ 范数上界 $M$、Katz–Tao 常数 $C_{\mathrm{KT}}$ 和邻域倍数 $\lambda$。在 Section 7 的应用中，曲线来自有界参数块与归一化斜率（$M = 40, C_{\mathrm{KT}} = 10^5$），这些量本来就是与 $\delta$ 无关的绝对常数。
5. **根定理闭环（Definition 2.12 `W2MW`、Section 6.2 `W2Sigma`、Definition 6.1 `W2D6_1`、Proposition 6.8 `W2P6_8`、Section 6.5 `W2Zero`、Theorem 5.2 `W2T5_2`）**：
   - 最终的根节点 `PureWZ2Theorem5_2Unconditional` 与论文的离散体积下界定理**逐字一致**（除了显式写出非空性 $\mathbb T \neq \varnothing$ 以排除空族平凡反例）。中间步骤对 Lemma 6.6 质量归一化、Lemma 6.7 斜率中心化 $f(0)=0$ 以及 Proposition 7.1 长度 $32$ 粗管测试的所有修正，全部在反证法闭环内部被上游构造消去，没有向最终定理引入任何额外假设。
