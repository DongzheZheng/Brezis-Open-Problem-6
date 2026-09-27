# 形式化结果与适用范围

仓库使用 Lean 4.29.0 与 mathlib v4.29.0。维数写为 $n=m+3$，覆盖所有 $n\ge3$；参数 $\varepsilon>0$ 任意。公开定理 [`physical_weak_unit_epsilon_minimum_and_ae_equality_from_core`](BrezisOP6/PhysicalWeakCanonicalYMain.lean) 在四项明确的解析输入下，证明单位球上真实 Ginzburg–Landau 弱能量的全局极小性，并证明等号场与径向涡旋几乎处处相等。配套定理处理任意正半径的有限球；基场识别定理给出 $f_\varepsilon(r)=f_{1/\varepsilon}(r/\varepsilon)$ 的尺度关系。

Lean 中完成的证明链包括：从径向轮廓构造原点正则的斜率缺陷函数；证明轮廓严格次序与接触余量；建立 Picone 零模与球面非零模的能量估计；将估计落实到欧氏空间的真实能量；在任意紧环带上证明对所有光滑竞争者统一的定量稳定性；构造零延拓固定迹场的强 $H^1\cap L^4$ 逼近，传递能量与等号唯一性；最后证明弱梯度、边界条件和能量的参数缩放。这些结论均连接到公开主定理。

四项输入分别是：已发表的径向剖面定理、已发表的整空间涡旋极小性、经典零迹延拓与密度定理、经典球面尖锐谱隙。它们在 Lean 主定理中以独立前提出现，证明及具体接口见 [`EXTERNAL_INPUTS.md`](EXTERNAL_INPUTS.md)。公开定理采用零延拓弱梯度定义固定迹；该定义与通常 Sobolev 迹的等价性属于所用的经典分析背景。径向剖面与整空间极小性是本问题的专项文献结果，四项输入的证明及其实例化均未纳入本仓形式化。二维结果不在本仓范围内。

完整远程构建、库根重编及 [`AxiomAudit.lean`](AxiomAudit.lean) 检查均通过。公开端点的公理输出仅为 Lean 的 `propext`、`Classical.choice` 与 `Quot.sound`，源码没有 `sorry`、`admit` 或自定义 `axiom` 声明。复现步骤见 [`VERIFICATION.md`](VERIFICATION.md)。
