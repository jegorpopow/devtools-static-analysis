package tip.analysis

import tip.ast.AstNodeData.DeclarationData
import tip.ast._
import tip.cfg._
import tip.lattices._
import tip.solvers._

abstract class ReachingDefinitionsAnalysis(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData) extends FlowSensitiveAnalysis(false) {

  val lattice: MapLattice[CfgNode, PowersetLattice[AStmt]] = new MapLattice(new PowersetLattice())

  val domain: Set[CfgNode] = cfg.nodes

  NoPointers.assertContainsProgram(cfg.prog)
  NoRecords.assertContainsProgram(cfg.prog)

  def transfer(n: CfgNode, s: lattice.sublattice.Element): lattice.sublattice.Element =
    n match {
      case _: CfgFunEntryNode => lattice.sublattice.bottom
      case r: CfgStmtNode =>
        r.data match {
          case as: AAssignStmt =>
            as.left match {
              case id: AIdentifier => s.filter(stmt =>
                  stmt match { // s contains assignments only
                    case asgn : AAssignStmt => asgn.left match {
                      case id2 : AIdentifier => id2.name != id.name
                      case _ => ???
                    }
                    case _ => ???
                  }
              ) + as
              case _ => s
            }
          case varr: AVarStmt =>
            lattice.sublattice.lub(s, varr.declIds.map { i =>
              AVarStmt(List(i), varr.loc)
            }.toSet[AStmt])
          case _ => s
        }
      case _ => s
    }
}

class ReachingDefinitionsAnalysisSimpleSolver(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
    extends ReachingDefinitionsAnalysis(cfg)
    with SimpleMapLatticeFixpointSolver[CfgNode]
    with ForwardDependencies



class ReachingDefinitionsAnalysisWorklistSolver(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
    extends ReachingDefinitionsAnalysis(cfg)
    with SimpleWorklistFixpointSolver[CfgNode]
    with ForwardDependencies
