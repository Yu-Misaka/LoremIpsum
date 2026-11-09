# Kakeya

### Core Proof DAG

#### WZ2 Definition 2.12

> The tubes are essentially distinct. For every $\rho_0 \in [\delta, 1]$, there are $\rho \in [\rho_0, A \rho_0)$ and $\rho$-tubes $\mathcal T_\rho$ such that:
> 1. $\mathcal T_\rho$ is an $A$-uniform partitioning cover of $\mathcal T$
> 2. for each parent, the unit-rescaled child family satisfies the convex Wolff axiom with error $A$.
> 
> 
> This is the root hypothesis; neither a direction-separated cover nor self-similar child counts is stipulated.

##### tags: `Kakeya.Assouad.WZ2PaperPureCWAAtNearbyScales`

```
WZ2PaperPureCWAAtNearbyScales ✔
├─ WZ2PaperFiniteErrorConstant ✔
├─ WZ2PaperOrdinaryIsEssentiallyDistinct ✔
│  └─ wz2PaperCenteredDilatedCarrier ✔
│     └─ wz2PaperTubeMidpoint ✔
├─ WZ2PaperRequestedScale ✔
└─ WZ2PaperPureNearbyScaleCoverData ✔
   └─ WZ2PaperPureScaleCoverData ✔
      ├─ WZ2PaperPurePartitioningCover ✔
      │  ├─ wz2PaperOrdinaryFullFiberIndices ✔
      │  └─ wz2PaperOrdinaryDilatedFiberIndices ✔
      │     └─ wz2PaperCenteredDilatedCarrier ✔
      ├─ WZ2PaperPureFullFibersAreCUniform ✔
      │  └─ wz2PaperOrdinaryFullFiberCount ✔
      │     └─ wz2PaperOrdinaryFullFiberIndices ✔
      └─ WZ2PaperPureUnitRescaledFullFiberData ✔
         ├─ WZ2PaperAssouadUnitRescalingData ✔
         ├─ wz2PaperPureUnitRescaledFullFiberBodyFamily ✔
         │  ├─ wz2PaperOrdinaryFullFiberIndices ✔
         │  ├─ wz2PaperOrdinaryFullFiberIndexEquiv ✔
         │  └─ WZ2PaperAssouadUnitRescalingData.map ✔
         └─ WZ2PaperBodyConvexWolffBound ✔
```

Basic Definitions:
1. **$\delta$-tube**: closed $\delta$-neighbourhood of a unit line segment (`Kakeya.Streamlined.TubeFamily`)
2. **Essentially distinct**: $\mathbb T$ is essentially distinct if $T_i \nsubseteq 2 \cdot T_j$ and $T_j \nsubseteq 2 \cdot T_i$ for every $i \neq j$. Here $2 \cdot T$ means dilation about the center of $T$ with factor 2. (`Kakeya.Assouad.wz2PaperCenteredDilatedCarrier`, `Kakeya.Assouad.WZ2PaperOrdinaryIsEssentiallyDistinct`)
3. **$\mathbb T[T_\rho]$**: $\{T \in \mathbb T : T \subseteq T_\rho\}$ (`Kakeya.Assouad.wz2PaperOrdinaryFullFiberIndices`)
4. **Unit rescaling**: 
	- Ellipsoid (centered at $\textbf c$ under linear equivalence $A$): $\textbf c + A(\overline{B(0, 1)})$ (`JohnEllipsoid.ellipsoid`)
	- Outer John ellipsoid of set $K$: an ellipsoid of minimum volume containing $K$ (`JohnEllipsoid.IsOuterJohnEllipsoid`)
	- Unit rescaling relative to $T_\rho$: choose an outer John ellipsoid of $T_\rho$, suppose it is centered at $\textbf c$ under linear equivalence $A$. Then a unit rescaling relative to $T_\rho$ is affine equivalence $\phi_{T_\rho}: \textbf x \mapsto A^{-1} (\textbf x - \textbf c)$. 
	- In short, send the outer John ellipsoid of $T_\rho$ back to unit ball at $\textbf 0$. (`Kakeya.Assouad.WZ2PaperAssouadUnitRescalingData.map`)
5. **Convex Wolff Axioms**: a multi-set $\mathcal S$ of sets in $\mathbb R^3$ satisfies the CWA with error $C$ if for all convex sets $W \subseteq \mathbb R^3$, we have $\# \mathcal S[W] \leq C|W|(\# \mathcal S)$ (`Kakeya.Assouad.WZ2PaperBodyConvexWolffBound`, $C \in [0, +\infty]$)
6. **$C$-uniform**: $\mathbb T_\rho$ are $C$-uniform over $\mathbb T$ if $\# \mathbb T[T_\rho] \leq C (\# \mathbb T[T_\rho'])$ for every $T_\rho, T_\rho' \in \mathbb T_\rho$ (`Kakeya.Assouad.WZ2PaperPureFullFibersAreCUniform`, $C \in [0, +\infty]$)
7. **Partitioning cover**: $\mathbb T_\rho$ is a partitioning cover of $\mathbb T$ if:
	- $\forall T \in \mathbb T, \exists T_\rho \in \mathbb T_\rho, T \in \mathbb T[T_\rho]$
	- $\forall i \neq j, \mathbb T[2 \cdot T_{\rho, i}]$ and $\mathbb T[2 \cdot T_{\rho,j}]$ are disjoint
	- (`Kakeya.Assouad.WZ2PaperPurePartitioningCover`)

- `Kakeya.Assouad.WZ2PaperPureUnitRescaledFullFiberData`: The unit rescaling of $\mathbb T[T_\rho]$ relative to $T_\rho$ satisfies the CWA with error $C$ ($C \in [0, +\infty]$)

8. **CWA at actual selected scale**: Let $C \in [0, + \infty], \delta > 0, \rho > 0$. We say that a set $\mathbb T$ of $\delta$-tubes satisfies CWA at actual selected scale $\rho$ with error $C$ if there exists a set of $\rho$-tubes $\mathbb T_\rho$ that satisfies the following property:
	- $\mathbb T_\rho$ is a $C$-uniform partitioning cover of $\mathbb T$
	- For each $T_\rho \in \mathbb T_\rho$, the unit rescaling of $\mathbb T[T_\rho]$ relative to $T_\rho$ satisfies the CWA with error $C$
	- (`Kakeya.Assouad.WZ2PaperPureScaleCoverData`)

**CWA at nearby scales (WZ2 Def 2.12 / CWA at every scale)**: 

Let $C \in [1, + \infty), \delta > 0$. We say that a set $\mathbb T$ of $\delta$-tubes satisfies CWA at nearby scales if the tubes in $\mathbb T$ are essentially distinct, and for every $\rho_0 \in [\delta, 1]$, there exists $\rho \in [\rho_0, C \rho_0)$ such that $\mathbb T$ satisfies CWA at actual selected scale $\rho$ with error $C$

---

#### WZ2 Section 6.2

> Let $Bad(s)$ mean: for every $\eta, \delta_0 > 0$, some $0 < \delta \leq \delta_0$ has multi-scale convex Wolff error $\delta^{-\eta}$, shading density $\delta^\eta$, and $|E_C| \leq \delta^s$. Define $\sigma = \sigma_{CW}=\sup(\{0\} \cup \{s > 0 : Bad(s)\})$. Failure of Theorem 5.2 gives $\sigma > 0$. This is a new deficit for a different admissible class, not WZ1's $\sigma_3$.

##### tags: `Kakeya.Assouad.PureWZ2CriticalExtractionStatement`

```
PureWZ2CriticalExtractionStatement
├── PureWZ2SubunitPackageStatement
│   ├── PureWZ2FullFiberAssertionDRefinementStatement
│   │   ├── PureWZ2FullFiberAssertionDRefinementData
│   │   │   ├── WZ2PaperPureOneScaleRescalingBridge
│   │   │   │   ├── wz2PaperPureFullFiberSubfamily ✔
│   │   │   │   │   ├── Kakeya.Streamlined.TubeSubfamily ✔
│   │   │   │   │   └── Kakeya.Streamlined.TubeSubfamily.fromFinset ✔
│   │   │   │   ├── WZ2PaperLiteralUnitRescaledFamilyData ✔
│   │   │   │   │   ├── WZ1PaperIsLineClass ✔
│   │   │   │   │   │   └── WZ1PaperTubeInLineClass ✔
│   │   │   │   │   │       ├── wz1PaperDirection ✔
│   │   │   │   │   │       │   └── Point3 ✔
│   │   │   │   │   │       └── wz1TubeAxisZeroPoint ✔
│   │   │   │   │   ├── tubeAxisLine ✔
│   │   │   │   │   └── wz2PaperLiteralUnitRescalingMap ✔
│   │   │   │   │       └── unitRescalingMap ✔
│   │   │   │   │           ├── householderToE3 ✔
│   │   │   │   │           │   └── e3 ✔
│   │   │   │   │           └── transverseScaleLin ✔
│   │   │   │   │               └── point3 ✔
│   │   │   │   ├── WZ2PaperAssouadUnitRescalingData.ofTube ✔
│   │   │   │   ├── WZ2PaperAssouadToLiteralRescalingCertificate ✔
│   │   │   │   └── Kakeya.Streamlined.TubeFamily.toBodyFamily ✔
│   │   │   │       └── Kakeya.Streamlined.tubeBody ✔
│   │   │   ├── Kakeya.FrostmanSlabWolffBound ✔
│   │   │   │   ├── Kakeya.Slab ✔
│   │   │   │   ├── Kakeya.Slab.carrier ✔
│   │   │   │   │   ├── Kakeya.DeltaTube.unitBall ✔
│   │   │   │   │   └── Kakeya.Slab.hyperplane ✔
│   │   │   │   ├── Kakeya.TubeFamily ✔
│   │   │   │   ├── Kakeya.TubeFamily.containedCount ✔
│   │   │   │   └── Kakeya.TubeFamily.enncard ✔
│   │   │   ├── Kakeya.KatzTaoConvexWolffBound ✔
│   │   │   │   └── Kakeya.deltaTubeVolume ✔
│   │   │   ├── Kakeya.Shading ✔
│   │   │   ├── Kakeya.Shading.IsLambdaDense ✔
│   │   │   │   ├── Kakeya.Shading.mass ✔
│   │   │   │   └── Kakeya.TubeFamily.mass ✔
│   │   │   │       └── Kakeya.DeltaTube.volume ✔
│   │   │   ├── Kakeya.Shading.union ✔
│   │   │   ├── Kakeya.Streamlined.Shading ✔
│   │   │   ├── Kakeya.Streamlined.Shading.mass ✔
│   │   │   ├── Kakeya.Streamlined.Shading.union ✔
│   │   │   ├── Kakeya.Streamlined.TubeFamily.Nonempty ✔
│   │   │   ├── Kakeya.Streamlined.TubeFamily.enncard ✔
│   │   │   ├── Kakeya.Streamlined.TubeShading ✔
│   │   │   ├── Kakeya.TubeFamily.IsEssentiallyDistinct ✔
│   │   │   │   └── Kakeya.DeltaTube.EssentiallyDistinct ✔
│   │   │   ├── Kakeya.TubeFamily.IsInUnitBall ✔
│   │   │   │   └── Kakeya.DeltaTube.IsInUnitBall ✔
│   │   │   └── Kakeya.realRpowENN ✔
│   │   └── Kakeya.Streamlined.Shading.IsLambdaDense ✔
│   │       └── Kakeya.Streamlined.BodyFamily.mass ✔
│   │           └── Kakeya.Streamlined.Body.volume ✔
│   ├── PureWZ2WolffFloorFromAssertionDStatement
│   │   ├── Kakeya.AssertionD
│   │   │   └── Kakeya.AssertionDLowerBound
│   │   └── PureWZ2WolffVolumeFloor
│   └── PureWZ2WolffFloorImpliesSubunitCeilingStatement
│       └── PureWZ2Admissible
├── PureWZ2Theorem5_2Statement
└── PureWZ2CriticalPackage
    ├── PureWZ2ExtremalConfiguration
    │   └── WZ2PaperPureIsExtremal
    └── PureWZ2CriticalVolumeFloor
```

Basic Definitions:

> Here is a very annoying remark on tube families: 
>
> We have indexed tube family (`Kakeya.Streamlined.TubeFamily`) and de-duplicated tube family (`Kakeya.TubeFamily`). 
> 
> We are always referring to indexed tube family by default - I'll mark it out when de-duped family is in use.
>
> When we write $T$ for an indexed family, we mostly mean the index, not the underlying geometric object.
> 
> Also, "de-dup" here does not mean de-duplicating according to the underlying geometric object, it basically says nothing useful mathematically. Tubes dilated from $(0, 0, 1) \rightarrow (0, 0, 0)$ and $(0,0,0) \rightarrow (0, 0, 1)$ are considered distinct.


1. **Shading**: A shading of $\mathbb T$ is an indexed family of measurable subsets $Y(T)$ of $T$ for every $T \in \mathbb T$ (`Kakeya.Streamlined.Shading`)
	- note that `Kakeya.Shading` is for de-duplicated tube families
2. **Essentially distinct (2025)**: **$\mathbb T$** is essentially distinct (2025) if $|T \cap T'| \leq 2^{-1}\max(|T|, |T'|)$ for every $T \neq T' \in \mathbb T$ (`Kakeya.TubeFamily.IsEssentiallyDistinct`)
	- note that $\mathbb T$ here is de-duplicated
3. **$\lambda$-dense**: Let $\lambda \in [0, +\infty], (\mathbb T, Y)$ is $\lambda$-dense if $\lambda \sum_{T \in \mathbb T}|T| \leq \sum_{T \in \mathbb T}|Y(T)|$ (`Kakeya.Streamlined.Shading.IsLambdaDense`)
	- note that `Kakeya.Shading.IsLambdaDense` is for de-duplicated tube families
4. **Katz-Tao convex Wolff bound with constant $C$**: $\# \mathbb T[W] \leq C |W| (|T|^{-1})$ for every convex set $W$ (`Kakeya.KatzTaoConvexWolffBound`)
	- Tubes in $\mathbb T$ have same size so it doesn't matter which $T$ is chosen. $\mathbb T$ here is de-duplicated
5. **Slab with norm $\textbf n$, offset $a$ and radius $r$**: $\|\textbf n\| = 1, 0 \leq r$, then the corresponding slab is $\overline{B(0,1)} \cap r$-closed neighbourhood of hyperplane $\{x : \langle \textbf x, \textbf n \rangle = a\}$ (`Kakeya.Slab.carrier`)
6. **Frostman slab Wolff bound with constant $C$**: $\# \mathbb T[W] \leq C |W| (\# \mathbb T)$ for every slab $W$ (`Kakeya.FrostmanSlabWolffBound`)
	- $\mathbb T$ here is de-duplicated
7.   **Fixed-constant unit rescaling relative to $T_\rho$**: (`Kakeya.Assouad.wz2PaperLiteralUnitRescalingMap`)
		- First consider the coaxial line of $T_\rho$, written as $l$, which meets the plane $z=0$ at $A$
		- Next, consider axial vector of $T_\rho$, denoted as $\textbf d$. We write $\tilde {\textbf d} = \textbf d$ when $\textbf d_3 \geq 0$ and $\tilde {\textbf d} = - \textbf d$ otherwise
		- Let $R$ denote the reflection across the plane through the origin with norm vector $\tilde {\textbf d} - \textbf e_3$ (when $\textbf d = \textbf e_3,$ set $R=id$)
		- Let $D$ be transverse anisotropic scaling linear map $(x, y, z) \mapsto (x/\rho, y / \rho, z)$
		- ... is $\varphi_{T_\rho} : x \mapsto \frac1{100} D(R(x - A))$
8. **$\mathcal L_3$**: a $\delta$-tube $T$ is in $\mathcal L_3$ if $1/2 \leq \tilde {\textbf d_3}, |A_1| \leq 1/3$ and $|A_2| \leq 1/3$ (`Kakeya.Assouad.WZ1PaperTubeInLineClass`)
- `Kakeya.Assouad.WZ2PaperLiteralUnitRescaledFamilyData`: Let $\mathbb T$ be a family of $\delta$-tubes, $\rho > 0, T_\rho$ be a $\rho$-tube. This structure admits a target family of $\delta/\rho$-tubes $\mathbb T_{\delta/\rho}$ in $\mathcal L_3$ and a bijection $f : \mathbb T_{\delta/\rho} \rightarrow \mathbb T$ satisfying:
	- $\forall T_{\delta/\rho} \in \mathbb T_{\delta/\rho}, l(T_{\delta/\rho})=\varphi_{T_\rho}(l(f(T_{\delta/\rho})))$
- `Kakeya.Assouad.WZ2PaperAssouadToLiteralRescalingCertificate`: Let $\mathbb T$ be a family of $\delta$-tubes, $\rho > 0, T_\rho$ be a $\rho$-tube. Suppose there is a `WZ2PaperLiteralUnitRescaledFamilyData` on this setting. And set $C_j$ a constant in $[0, +\infty]$. Then this structure admits another family of $\delta/\rho$-tube $\mathbb T'_{\delta/\rho}$ together with two bijections: $g_1 : \mathbb T'_{\delta/\rho} \rightarrow \mathbb T, g_2 : \mathbb T_{\delta/\rho} \rightarrow T'_{\delta/\rho}$ and an affine automorphism $h$ of $\mathbb R^3$  satisfying:
	- $g_1 \circ g_2 =f$
	- $l \circ g_2 =l$
	- $h \circ \phi_{T_\rho} \circ f= \varphi_{T_\rho} \circ f$
	- $\varphi_{T_\rho} \circ f\subseteq g_2$
	- $W$ is convex $\Rightarrow h^{-1}(W)$ is convex
	- $\forall S \subseteq \mathbb R^3, |h^{-1}(S)| \leq C_j |S|$
- `Kakeya.Assouad.WZ2PaperPureOneScaleRescalingBridge`: Let $\mathbb T$ be a family of $\delta$-tubes, $\mathbb T_\rho$ be a family of $\rho$-
<!--stackedit_data:
eyJoaXN0b3J5IjpbLTkzNzIyNDkyOCwtODU4MjIyMTUsLTMyOD
c0MDU1LDExNTUwNzMwMjNdfQ==
-->