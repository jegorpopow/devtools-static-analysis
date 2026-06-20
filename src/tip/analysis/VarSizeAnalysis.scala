package tip.analysis

import tip.ast.AstNodeData.DeclarationData
import tip.cfg.CfgOps.CfgNodeOps
import tip.cfg._
import tip.lattices.IntervalLattice._
import tip.lattices._
import tip.solvers._

trait VarSizeAnalysisWidening extends ValueAnalysisMisc with Dependencies[CfgNode] {

  val cfg: ProgramCfg

  val valuelattice: IntervalLattice.type

  val liftedstatelattice: LiftLattice[statelattice.type]

  /**
    * Powers of 2 plus -infinity and +infinity.
    */
  private val Appearing = cfg.nodes.flatMap { n =>
    n.appearingConstants.map { x =>
      IntNum(x.value): Num
    } + MInf + PInf
  }

  private val powers = (0 to 31).map(i => 1 << i)
  private val allValues = powers ++ powers.map(-_) ++ List(MInf, PInf)

  private val B = allValues.map {
    case PInf => PInf
    case MInf => MInf
    case b: Int => IntNum(b.toInt): Num
  }.toSet ++ Appearing
  def loophead(n: CfgNode): Boolean = indep(n).exists(cfg.rank(_) > cfg.rank(n))

  private def minB(b: IntervalLattice.Num) = B.filter(b <= _).min

  private def maxB(a: IntervalLattice.Num) = B.filter(_ <= a).max

  def widenInterval(x: valuelattice.Element, y: valuelattice.Element): valuelattice.Element =
    (x, y) match {
      case (IntervalLattice.EmptyInterval, _) => y
      case (_, IntervalLattice.EmptyInterval) => x
      case ((l1, h1), (l2, h2)) => (maxB(List(l1, l2).min), minB(List(h1, h2).max))
    }

  def widen(x: liftedstatelattice.Element, y: liftedstatelattice.Element): liftedstatelattice.Element =
    (x, y) match {
      case (liftedstatelattice.Bottom, _) => y
      case (_, liftedstatelattice.Bottom) => x
      case (liftedstatelattice.Lift(xm), liftedstatelattice.Lift(ym)) =>
        liftedstatelattice.Lift(declaredVars.map { v =>
          v -> widenInterval(xm(v), ym(v))
        }.toMap)
    }
}

object VarSizeAnalysis {

  object Intraprocedural {

    /**
      * Interval analysis, using the worklist solver with init and widening.
      */
    class WorklistSolverWithWidening(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
        extends IntraprocValueAnalysisWorklistSolverWithReachability(cfg, IntervalLattice)
        with WorklistFixpointSolverWithReachabilityAndWidening[CfgNode]
        with VarSizeAnalysisWidening

    /**
      * Interval analysis, using the worklist solver with init, widening, and narrowing.
      */
    class WorklistSolverWithWideningAndNarrowing(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
        extends IntraprocValueAnalysisWorklistSolverWithReachability(cfg, IntervalLattice)
        with WorklistFixpointSolverWithReachabilityAndWideningAndNarrowing[CfgNode]
        with VarSizeAnalysisWidening {

      val narrowingSteps = 5
    }
  }
}
