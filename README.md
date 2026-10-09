# CounterQuasi

论文选读 [*Gradual typing for functional languages*](https://www.researchgate.net/publication/213883236_Gradual_typing_for_functional_languages) 第一部分

在论文前两章，作者初步介绍了过渡类型系统（gradual typing）。在第 3 章，提及作者过去的尝试：基于子类型关系的 quasi typing，并指出其本质问题。这个 Lean 项目复现了 quasi 系统的漏洞，并展示了 gradual 系统没有这个漏洞。

## 代码总览

所有定义和证明都在 `/CounterQuasi` 文件下的四个 Lean 文件中。

### `TypeSystem.lean`

关于类型系统的若干基础定义。

- `PartialType`：对应第 2 章 Syntax of the Gradually-Typed Lambda Calculus 中 Types 的定义。在渐进类型系统中，类型有且仅有三种：

  - 基础类型：`boolean`，`number` 等
  - 函数类型：`σ ⟶ τ`，其中 `σ` 和 `τ` 是任意类型
  - 未知类型：类似 any 类型。论文中用 `?` 表示，Lean 代码为避免语法冲突改用 `??`。第 3 章的 `Ω` 也使用 `??` 代表。

  这三个元素可以组合成复杂类型，如 `(?? ⟶ number) ⟶ boolean ⟶ ??`。论文里并没有处理诸如列表、元组等复合类型。

- `Expression`：同一语法表中 Expressions 定义。作为函数编程语言，它有且仅有四种语法：

  - 常量：`114514`，`#t`，`succ` 等
  - 变量名。在 Lean 代码里，带双引号的字符串代表变量名。
  - 匿名函数，如 `lambda "x" : ?? => "x"`。参数类型是 `??` 时，可以省略作 `lambda "x" => "x"`。
  - 函数调用，如 `succ "x"`。

  我们研究的语言不允许诸如 TypeScript `x as any` 的用法。此外，在论文后续部分，还会增加变量存储有关语法，但这里不涉及。

- `TypeSystem`：一个类型系统。包含若干规定：

  - `𝕏`：如何表示变量名。绝大多数语言用字符串标识符来命名变量，但理论上也可以用数字或者其他方法。
  - `𝔾`：有哪些基础类型。我之后将定义一个只有自然数和布尔值的系统。注意，不同基础类型之间没有天然关联，不像 C++ `int` 和 `long long` 之间那样。
  - `ℂ`：有哪些常量。我在我的举例中规定了 `#f`、`#t`、自然数以及 `succ` 四种常量。
  - `Δ`：每个常量分别是什么类型。`#f` 和 `#t` 是 `boolean`，自然数是 `number`，`succ` 是 `number ⟶ number`。这个类型可以是任何合法类型，甚至包括 `??`。

### `Gradual.lean`

Gradual 类型系统的基本定义，以及对源代码的初步处理。

- `TypeConsistent`：类型间的兼容关系，记作 `σ ~ τ`，对应第 2 章 Type Consistency 定义。它满足自反性对称性，但不满足传递性：`number ~ ?? ~ boolean`，但 `number ≁ boolean`。
- `TypedExpression`：语言解释的中间形态。如果说 `Expression` 是源代码（的语法树），那么 `TypedExpression` 就是第一步处理的中间结果，每一个运算步骤都打上了类型标记，并且必须能够经过类型检查。
- `annotate`：将 `Expression` 初步解析，输出 `TypedExpression` 的算法。这个算法反映了第 2 章 Figure 2，但表述方式不同：论文中用的不是算法，而是命题陈述。

### `Quasi.lean`

作者在第 3 章将 gradual 系统与 quasi 系统比较。这个文件定义了 quasi 系统的基本关系，并且也提供了按照 quasi 系统的源码处理算法。

- `SubtypeOf`：类型间的子类型关系，记作 `σ <: τ`，对应第 3 章 Subtyping rules 定义。它满足自反性、反对称性、传递性。
- `joint`：类型之间的“有公共部分”关系，对应第 3 章提及的 `∃ μ, μ = τ ⊓ ν`。Quasi 系统为了防止 `number` 和 `boolean` 之间意外转换，quasi 系统对类型转换有一定限制。否则，那它这个约束就是错的，那它不就是“stupid cast”（原文如此）吗。
- `TypedExpression` 与 `annotate`：和前面相同，但用的是 quasi 系统。

### `Counterexample.lean`

通过反例指出 quasi 系统的根本不足，同时展示 gradual 系统没有这个不足。

- `TSys`：一个由 `number` 与 `boolean` 组成的类型系统。
- `Counterexample`：论文第 3 章使用的反例 `(lambda "x" : number => succ "x") #t`。这式子是错的，因为它在企图计算 `succ #t`，然而 true 并没有后继数。
- 之后几个 `#quasi` 与 `#gradual` 的对比展现了两套系统面对同一反例的不同表现。`#gradual` 返回 `none`，自信地拒绝了这个反例。