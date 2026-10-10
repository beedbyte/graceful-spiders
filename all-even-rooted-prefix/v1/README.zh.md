# 有根优美图的偶数长臂上的指定零标号位置

**Beedbyte · 源码包 v1**

Jordi Gartner 通过 Beedbyte 发布这项工作。
[English](README.md) · [Deutsch](README.de.md)。德文和中文版本均为翻译草稿，尚无人工语言审校记录。

## 定理

设 **K ≥ 20 为偶数**。H 是有 Q 条边的有限图，并给定常规优美标号 g：顶点标号是 0,…,Q 中互不相同的整数，边差恰为 1,…,Q。指定根 r 必须满足 g(r)=0。在 r 处添加两条不同的新臂，每条有 K 条边，保留 H。

对于**任一条具名新臂**以及每个深度 **2 ≤ d ≤ D8(K)**，所得图都存在一个单独的常规优美标号，使该顶点标为零。深度按从 r 出发的边数计算。标号可以随目标而改变；不主张同时把多个顶点标为零。

| 偶数 K | D8(K) |
|---|---|
| 20–34 | 11 |
| 36–52 | 27 |
| 54–124 | 25 + 16⌊(K−35)/18⌋ |
| K ≥ 126 | 107 + 20a + 2s，其中 (K−4)/2 = 61 + 11a + s 且 0 ≤ s ≤ 10 |

H 无须是树、连通图、二部图或具有 alpha 标号的图。其顶点标号无须填满 0,…,Q。根标为零的给定标号是前提，不能仅由优美性推出。本定理不涵盖 H 的旧顶点、深度 1、臂端或超过 D8(K) 的深度，也不主张所有此类拼接图完全零可旋转。

## 证明与前人工作

构造给出一条有 2K 条边的路径的 alpha 标号，其分界为 K，中点标号为 K，选定位置为极值。随后给 H 标上 K+g，保留低于 K 的路径标号，并把高于 K 的路径标号增加 Q。旧边差为 1,…,Q，新边差为 Q+1,…,Q+2K。反转路径可选另一条臂；对整个图取补标号可将目标处的最大值变为零。

将 alpha 分界顶点与零根合并的一般操作属于已有方法，归于 Huang–Kotzig–Rosa，并明确见于 [Panpa、Imnang 和 Wasuanankul（2025），定理 2.5](https://onlinelibrary.wiley.com/doi/full/10.1155/jama/5826777)及 [Shan–Zhong（2026），引理 1](https://arxiv.org/html/2605.14295v2)。另见 [Barrientos（2022），*On the generation of alpha graphs*，第103页](https://www.jacodesmath.com/index.php/jacodesmath/article/view/194)，9(2)，101–114，DOI 10.13069/jacodesmath.1111733。成对的零值／分界锚点也已见于 [Barrientos–Minion（2019），§2.2](https://digitalcommons.georgiasouthern.edu/tag/vol6/iss1/4/)。

这一精确统一的中点／D8 证书族及其推论在全球文献中的优先权为 **UNKNOWN（未确定）**。已查阅来源未解决旧构造是否已蕴含此结论。[Cattell（2007）的 alpha 路径刻画](https://doi.org/10.1016/j.disc.2007.03.046)原文全文在本次比较中不可获取；各自的单位置自由度本身不能证明共同的中点／极值条件。这里不主张新的一般拼接操作或图不可能性定理。

## 复现与信任边界

主定理为 [EvenRootedPrefix.lean](source/EvenRootedPrefix.lean) 中的 `GracefulBoundary.EvenRootedPrefix.all_even_prefix`。本包包含全部 79 个传递依赖项目源码以及 9 个单独编写的查询／控制源码。需要 Python 3.9+ 和带有标准库的 Lean **4.34.0**，无须其他项目检出目录。

```text
python build.py --check
python -O build.py --check
python build.py --lean /path/to/lean --output /new/outside/package/build
```

输出目录必须尚不存在。构建程序核对全部索引文件，在空对象目录中以警告视为错误的设置编译全部模块，检查 3,583 个定理的公理依赖，展开实际图定理，并运行 16 个具名三角形例子及 7 个预期失败控制。K=20,36,124,126 和标号为 0,1,3 的余图三角形检验边界及非满射约定。深度、根、臂端和满射失败控制用于检查定理前提，并非证明图不存在。本包不分发编译对象。

普遍陈述由 Lean 证明，有限例子本身不构成普遍证明。信任基础包括定义与图描述的对应、Lean 内核／工具链以及允许的公理 `propext`、`Classical.choice`、`Quot.sound`。另行进行的项目内部复制源码重放已通过。这些属于项目内部检查，并非外部审查或同行评审。[来源记录](provenance.json)列出精确源码及证据哈希；完整历史报告保留在项目档案中。

## 方法与贡献

AI 工具协助了已记录的证明开发、Lean 实现、另行内部重放、文献比较及这些翻译草稿。Jordi Gartner 通过 Beedbyte 承担发布责任。

第1版提供所有偶数 K 的 D8 定理、完整 Lean 源码依赖及可复现的适用范围检查。
