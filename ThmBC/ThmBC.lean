import ThmBC.BasicPi11
import ThmBC.Tree.Tree
import ThmBC.Lower.Complete
import ThmBC.Upper.Upper

/-!
# Theorems B and C — full development

This file re-exports the whole Theorem B/C development.

The main results are:

* `DSTBL3.WeightedTree.LowerComplete.lower_complete_template`, the formal
  version of Theorem B.
* `DSTBL3.WeightedTree.UpperComplete.upper_complete_template`, the formal
  version of Theorem C.

The file split follows the paper:

* `ThmBC.BasicPi11`: descriptive-set-theoretic conventions and `WF`
  `Π¹₁`-completeness.
* `ThmBC.Tree.*`: the weighted tree template and fattening.
* `ThmBC.Lower.*`: the decreasing-sequence complete coanalytic construction.
* `ThmBC.Upper.*`: the increasing-unbounded complete coanalytic construction.
-/
