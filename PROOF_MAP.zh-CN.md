# 证明链与核验边界

本项目以 `n = m + 3`、`m : ℕ` 表示全部 `n≥3` 维，采用单位耦合与半径 `R>0` 的球模型。以下箭头表示 Lean 中实际组合的条件定理；箭头起点的剖面存在/正则性、标准球面谱隙、已发表整空间紧支扰动极小性及标准零迹延拓桥仍须由外部数学输入提供。

| 环节 | 主要模块与定理 | Lean 中完成的工作 |
| --- | --- | --- |
| 原点与正半径唯一性 | `OriginRatioContraction`、`OriginRatioGlobalProfile`、`PositiveRadiusLinearUniqueness`、`PositiveRadiusProfileUniqueness` | 用收缩控制奇异原点，同斜率后由线性 ODE 唯一性延拓；不再把作者论证所需的唯一性作为未说明的接口。 |
| 剖面严格次序及接触屏障 | `PhysicalProfileOrder.physical_radial_profiles_ordered_from_terminal`、`BallZeroModeCompletedBarrierInterior` | 从终端 `F(R)<f(R)`、Taylor/ODE/远场数据得到 `F<f`、接触余量与零模 Picone 符号。有限球方程只在内部使用，外边界用左连续迹。 |
| 零模原点与均值密度 | `SphereActualC1Proxy`、`SphereMeanClosedProxyIntegrability`、`SphereActualMeanIntegrable`、`SphereActualFluxIntegrable` | 实际均值 `b(r)=r\,\mathrm{mean}(u/f)` 在 `r>0` 等于正则分子均值除以 `H_f(r²)`；据此控制原点右极限、全 `[0,R]` 均值密度与通量导数可积性。 |
| Picone 环带 | `PiconeAnnulusIntegrability`、`ProfilePiconeAnnulusAutoIntegrability`、`ProfilePiconeFluxC1Proxy`、`ProfilePiconeFluxAnnulusRegularity`、`SphereActualPiconeFluxRegularity` | 精确恒等式及非负性自动给 square/remainder 分别可积；全局 `C²` 剖面与实际 `C¹` 分子给每个正环带的 Picone flux 连续和导数可积。证明无需在人工的球外端点求导。 |
| 真实逐坐标零模 | `SphereActualMeanNonnegativeC2.actual_finiteBallSphere_mean_integral_nonneg_of_C2_profiles` | 从上两行及接触屏障得到每坐标真实 bridge mean 积分非负；没有把任何零模可积性或 Picone flux 正则性作为独立前提。公开顶层 `ActualSmoothMainCanonical` 再由 `PhysicalProfileOrder` 提供所需严格次序，并构造比值延拓及剖面通量连续性。 |
| 具体球面和能量 | `SphereRealization`、`SphereLocalPoincare`、`SphereCoordinateOddness`、`SphereActualScalarBridgeIntegrable`、`ActualModeCertificate`、`EnergyActualInteriorPair` | 使用实际欧氏单位球测度、径向 `L²` 迹、极坐标/Fubini 与真实 Fréchet 梯度，得到两个轮廓的能量恒等式与非负桥。球面坐标均值零由反足对称性推出；尖锐谱隙及已发表整空间涡旋极小性仍为显示的输入。 |
| 等号与光滑顶层 | `SphereEqualityActual`、`BallPuncturedEqualityAE`、`ActualSmoothMainFromProfileOrder`、`ActualSmoothMainCanonical` | 二次和四次桥在等号时分别为零；穿孔球内实际商场等于恒等映射，再得到球内几乎处处唯一性。顶层源码为带精确剖面/几何/文献输入的光滑条件定理。 |
| 论文的弱能量 | `WeakBallEnergy.WeakH1L4BallField`、`WeakBallEnergy.WeakFixedTraceCompetitor` | 用分布积分分部定义弱梯度；要求 `L²∩L⁴` 及梯度 `L²`；能量用这个弱梯度计算并已证明能量密度真可积。零延拓固定迹与通常 trace 的等价性尚待证明。 |
| 固定迹强密度 | `WeakFixedTraceDensity.physical_weak_fixed_trace_strong_closure` | 对任意本仓零延拓定义的弱固定迹场构造球内紧支撑的共同光滑扰动序列，证明值强 $L^4$ 与各弱梯度列强 $L^2$ 收敛；`WeakEnergyStrongConvergence` 随后证明能量收敛。 |
| 统一环域稳定性 | `ActualSmoothAnnularCoordinateFixed`、`ActualSmoothAnnularDistanceUniform`、`ActualSmoothQuantitativeBridge`、`ActualSmoothAnnularEnergyGap.actual_smooth_annular_energy_gap_uniform` | Picone 与角向余量控制每个环带上的物理距离；两剖面能量桥使它由能量差控制。常数在选择光滑竞争者前固定。 |
| 弱等号及有限球主定理 | `WeakAnnularEqualityLimit`、`PhysicalWeakBallMain.physical_weak_ball_minimum_and_ae_equality` | 强逼近传递能量与环带 $L^2$ 距离；可数环带耗尽得到弱等号场几乎处处唯一。端点不再假设闭包、统一估计或弱极小元正则性。 |
| 原点与接触流接口收缩 | `OriginFactorTaylor`、`PhysicalProfileYExtension`、`PhysicalRadialDataCore.toPhysicalRadialData` | 从 $C^2$ 原点因子构造五次 Taylor 余项和系数，从 $F'>0$ 与因子分解构造可微辅助变量 $y$；公开输入不再单列这些定制数据。 |
| 文献与标准分析输入的分离 | `PublishedC1TraceBridge.publishedC1_and_standardTrace_to_ballMinimality` | 将文献原形式的内支扰动极小性与经典同迹场零延拓/强逼近分列为前提；从已证明的强收敛能量连续性推出内部球比较。 |
| 任意参数尺度还原 | `WeakGlobalDilationChainRule`、`WeakEpsilonMainTransfer`、`PhysicalWeakCanonicalYMain.physical_weak_unit_epsilon_minimum_and_ae_equality_from_core` | 已证明弱梯度、零延拓固定迹、能量和等号在尺度伸缩下的对应；`physical_weak_unit_base_from_core_ae_eq_vortex` 将单位球基场识别为论文的 $f_\varepsilon$ 涡旋。 |

整库 `lake build BrezisOP6`、库根重编和 `AxiomAudit.lean` 已完成；两个 Core 弱主端点只依赖 Lean 的 `propext`、`Classical.choice`、`Quot.sound`。验证结论以四项显示的数学前提为范围：径向剖面与整空间涡旋极小性是已发表的专项结果，球面谱隙与 Sobolev 迹/零延拓等价性是经典背景。这些前提的证明和实例化均在本仓的 Lean 证明范围之外；具体陈述及引用见 [EXTERNAL_INPUTS.md](EXTERNAL_INPUTS.md)。
