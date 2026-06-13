package tip.analysis

import tip.ast.AstNodeData.DeclarationData
import tip.ast._
import tip.ast.AstOps.AstOp
import tip.cfg._
import tip.lattices._
import tip.solvers._

/**
  * Base class for live variables analysis.
  */
abstract class LiveVarsAnalysis(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData) extends FlowSensitiveAnalysis(false) {

  val lattice: MapLattice[CfgNode, PowersetLattice[ADeclaration]] = new MapLattice(new PowersetLattice())

  val domain: Set[CfgNode] = cfg.nodes

  NoPointers.assertContainsProgram(cfg.prog)
  NoRecords.assertContainsProgram(cfg.prog)

  def transfer(n: CfgNode, s: lattice.sublattice.Element): lattice.sublattice.Element =
    n match {
      case _: CfgFunExitNode => lattice.sublattice.bottom
      case r: CfgStmtNode =>
        r.data match {
          case cond: AExpr => lattice.sublattice.lub(s, cond.appearingIds)
          case as: AAssignStmt =>
            as.left match {
              case id: AIdentifier => lattice.sublattice.lub(s - id, as.right.appearingIds)
              case _ => s // Let's just ignore it, it seems to be default way
            }
          case varr: AVarStmt => s -- varr.declIds //<--- Complete here
          case ret: AReturnStmt => lattice.sublattice.lub(s, ret.exp.appearingIds)
          case out: AOutputStmt => lattice.sublattice.lub(s, out.exp.appearingIds)
          case _ => s
        }
      case _ => s
    }
}

/**
  * Live variables analysis that uses the simple fixpoint solver.
  */
class LiveVarsAnalysisSimpleSolver(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
    extends LiveVarsAnalysis(cfg)
    with SimpleMapLatticeFixpointSolver[CfgNode]
    with BackwardDependencies

/**
  * Live variables analysis that uses the worklist solver.
  */
class LiveVarsAnalysisWorklistSolver(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
    extends LiveVarsAnalysis(cfg)
    with SimpleWorklistFixpointSolver[CfgNode]
    with BackwardDependencies
