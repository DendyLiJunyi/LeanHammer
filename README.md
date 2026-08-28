# lean-smt-hammer

一个 Lean 4 tactic，跑完整条 hammer 流水线，后端是 SMT 求解器。

> 和社区的 [LeanHammer](https://github.com/JOSHCLUNE/LeanHammer)（lean-auto + Duper）
> 不是同一个项目。那个的翻译目标是 TPTP/一阶，重建全靠 Duper；这个的翻译目标是
> SMT-LIB，主力是 z3 / cvc5 的判定过程，Duper 只在最后一步用来把 unsat core
> 换成真证明。

```
目标 + 局部上下文
  │
  ├─① 前提收集      扫 Environment，取出所有 theorem 作候选池
  ├─② 相关度过滤    MePo 风格迭代扩张，按稀有符号加权，选出 ~100 条
  ├─③ 单态化        用目标里出现的具体类型实例化多态引理，synthInstance 补实例参数
  ├─④ 编码 + 求解   翻成 SMT-LIB 2，并行跑 z3 / cvc5，取 unsat core
  │
  └─⑤ 逆向翻译      把 core 交给 Duper 在 Lean 内部重证 —— 部分覆盖，见下
```

前四步是主体。第 ⑤ 步走的是"外包"路线：外部求解器负责在几万条引理里**搜索**，
Duper（一个跑在 Lean 里的 superposition 证明器）负责在 core 那几条引理上**重建**。

* 重建成功 → 目标由真正的证明项闭合，`#print axioms` 干净。
* 重建失败 → 退回公理 `Hammer.trustSMT : ∀ p : Prop, p`，报告如实说明。

```lean
theorem demo (l₁ l₂ : List Nat) : (l₁ ++ l₂).length = l₁.length + l₂.length := by hammer
-- hammer: z3 判定 unsat（18ms）· 前提 96 选中 → 170 单态化 → 137 已断言（丢弃 33）
-- unsat core 用到的前提：
--   · List.length_append
-- 目标已由 Duper 重建的证明项闭合 —— 这是真证明，不含 `trustSMT`。
#print axioms demo
-- 'demo' depends on axioms: [propext, Classical.choice, Quot.sound]
```

即使重建失败，报告本身也有用：它告诉你哪几条引理足以推出目标，可以拿去喂
`omega` / `simp` 换一个真证明。

## 逆向翻译的实际覆盖面

`HammerTest/Reconstruct.lean` 拿 19 个目标做了实测（`#print axioms` 判定）：

| 类别 | 重建成功 | 说明 |
| --- | --- | --- |
| 命题逻辑 | 3 / 3 | Duper 的主场 |
| 不解释函数与等式 | 3 / 3 | 同上 |
| 量词 | 2 / 2 | 同上 |
| 需要 environment 引理 | 2 / 2 | `List.length_append` 一类 |
| 整数/自然数算术 | 2 / 9 | **主要缺口** |
| **合计** | **12 / 19** | |

缺口的原因很明确：**Duper 是纯一阶等式推理，没有算术决策过程**。
`a ≤ b → a ≤ b + 1`、`n - (n+1) = 0`、`n / 0 = 0` 这些目标的 core 里往往只有一两条假设，
真正的工作全在 z3 的线性算术理论里——这部分 Duper 接不住。
（成功的那两个是特例：`x < y → x + 1 ≤ y` 在 `Int` 上有现成引理，
`(-7)/2 = -4` 是闭项可计算。）

时间代价很低：19 个目标总共只多花 ~0.6 秒（约 30ms/个）。
Duper 要么很快成功，要么很快放弃。

## 安装

需要 z3 和 cvc5 在 `PATH` 上（至少一个）。

```bash
brew install z3
# cvc5 不在 homebrew 里，从 release 拿二进制：
curl -sL -o cvc5.zip "$(curl -sL https://api.github.com/repos/cvc5/cvc5/releases/latest \
  | grep browser_download_url | grep 'cvc5-macOS-arm64-static.zip' | cut -d'"' -f4)"
unzip -q cvc5.zip && sudo cp cvc5-macOS-arm64-static/bin/cvc5 /usr/local/bin/
```

然后 `lake build`。首次构建会拉 Duper 及其依赖（lean-auto、batteries），需要几分钟。

toolchain 锁在 `v4.30.0`：Duper 没有 `v4.31.0` 这个 tag（v4.30.0 直接跳到 v4.32.0），
而 v4.30.0 是离本项目最近的可用版本。

> `lakefile.toml` 里开了 `precompileModules = true`。tactic 代码默认走字节码解释器，
> 慢一个数量级；编成动态库后 Lean 侧开销从 ~800ms 降到 ~130ms（首次调用还要
> 2 秒扫一遍 environment，之后走进程内缓存）。

## 用法

```lean
import Hammer

example (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by hammer
example : ... := by hammer (timeout := 30, premises := 256)
example : ... := by hammer (verbose := true)      -- 打印 SMT-LIB 问题与问题文件路径
example : ... := by hammer (close := false)       -- 只报告，不闭合目标
```

| 选项 | 默认 | 含义 |
| --- | --- | --- |
| `premises` | 96 | 相关度过滤后保留的引理数 |
| `timeout` | 10 | 每个求解器的墙钟超时（秒） |
| `instances` | 8 | 单态化时每条引理最多产生的实例数 |
| `solvers` | `"z3,cvc5"` | 参与竞速的后端，逗号分隔 |
| `mono` | true | 是否单态化；关掉后多态引理会被整条丢弃 |
| `verbose` | false | 打印 SMT-LIB 问题 |
| `close` | true | 重建失败时，是否用信任公理闭合目标 |
| `reconstruct` | true | 是否尝试用 Duper 逆向翻译 |
| `assumeNonempty` | false | 见下面"排序非空" |

## 代码结构

| 文件 | 职责 |
| --- | --- |
| `Hammer/Basic.lean` | 配置、结果类型、信任公理 `trustSMT` |
| `Hammer/Premise/Features.lean` | 前提的特征（陈述里出现的常量集） |
| `Hammer/Premise/Collect.lean` | 扫 Environment / 局部上下文，带缓存 |
| `Hammer/Premise/Select.lean` | MePo 相关度过滤 |
| `Hammer/Translate/Encode.lean` | `Expr` → SMT-LIB，核心 |
| `Hammer/Translate/Monomorphize.lean` | 目标驱动的类型实例化 |
| `Hammer/Translate/Problem.lean` | 组装完整问题，管理 `:named` 标签 |
| `Hammer/Translate/SMTLib.lean` | S-表达式与命令的表示/打印 |
| `Hammer/Solver/Backend.lean` | 并行调 z3 / cvc5，解析 unsat core |
| `Hammer/Tactic.lean` | tactic 前端与报告，逆向翻译的挂钩 |
| `Hammer/Reconstruct.lean` | 用 Duper 重建证明；核心库不硬依赖它 |

## 编码的取舍

CIC 比多排序一阶逻辑强得多，翻译必然是部分的。三条原则：

1. **看得懂的精确翻译**：命题连接词、量词、等式、`Nat`/`Int`/`Real` 上的算术与比较。
2. **看不懂的抽象成不解释符号**。抽象只丢等式信息，让问题更难而不是更容易，
   所以 `unsat` 依然可信。
3. **前提翻译失败就丢掉那一条**，只有目标翻译失败才算整体失败。

几个具体决定：

* **`Nat` → `Int` + 非负性**。每个 `Nat` 量词加 `≥ 0` 守卫，每个返回 `Nat` 的符号加
  非负公理。
* **全函数语义**。`a - b` 翻成 `(ite (<= b a) (- a b) 0)`；`a / 0` 翻成 `0`；
  `a % 0` 翻成 `a`。Lean 的 `Int` 除法恰好就是 SMT-LIB 的欧几里得 `div`
  （实测 `(-7)/2 = -4`、`(-7)%2 = 1`），所以只需补零除守卫。
* **就地单态化**。`@f α inst a b` 里的类型参数和实例参数并入符号的**身份**，
  不作为参数翻译：`@List.length Nat l` 和 `@List.length Int l` 得到两个不同的
  SMT 符号。这样一阶编码器不必表达多态。

## 已知的不健全风险（都已堵上，记在这里备查）

一个把真命题翻成矛盾的编码，会让 `hammer` "证明"假命题。
`HammerTest/Soundness.lean` 就是守这一层的回归测试。

**依赖排序。** `Fin.pos : ∀ {n} (i : Fin n), 0 < n`。把 `Fin n` 抽象成一个与 `n`
无关的排序 `Fin`，公式就变成"只要 `Fin` 非空，所有 `n ≥ 0` 都满足 `0 < n`"——
自相矛盾，于是任何目标都能被"证明"。这个 bug 是被 `f a = f b` 这个反例抓到的。
现在编码器拒绝任何提到当前量词作用域内变量的排序或符号（`mentionsBound`）。

**排序非空。** SMT-LIB 假设每个排序非空，Lean 的类型可以是空的。`∀ x : Empty, P x`
在 Lean 里平凡为真，翻成 SMT 却是一条实打实的断言。默认要求 `Nonempty` 可合成，
不然就丢掉这条前提；`assumeNonempty := true` 可以换取覆盖面，但 `unsat` 不再可信。

代价是完备性：严格检查会让不少前提被丢掉（反例测试里 95 条能编码的只剩 16 条）。

## 还没做的

* **算术目标的逆向翻译**——上面那 7 个缺口。两条路：接一个 Lean 侧的算术 tactic
  （`omega` 能关掉其中大部分）作为 Duper 之外的重建后端；或者老老实实从 SMT 的证明
  日志（z3 的 `(get-proof)`、cvc5 的 Alethe）重建证明项，工程量大得多但覆盖面完整。
* **高阶**。λ 项目前一律被抽象。接 TPTP THF + Zipperposition 会好很多。
* **归纳**。SMT 不做归纳，凡是需要归纳的目标都出不来。
* **前提选择用机器学习**。目前是纯符号的 MePo；Sledgehammer 的 MaSh 用的是
  朴素贝叶斯/kNN，效果明显更好。
* **倒排索引**。相关度过滤现在每轮线性扫全池。core Lean 的 37k 条够快，
  上 Mathlib（~300k）需要按符号建倒排。

## 许可

Apache License 2.0，见 [`LICENSE`](LICENSE)。这也是 Lean 生态的惯例——Mathlib、
Duper、lean-auto 都用它。
