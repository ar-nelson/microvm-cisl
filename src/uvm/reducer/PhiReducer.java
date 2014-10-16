package uvm.reducer;

import uvm.BasicBlock;
import uvm.CFG;
import uvm.OpCode;
import uvm.ssavalue.*;

import java.util.*;

/**
 * <p>Reduces a μVM control flow graph ({@link CFG}) to a nonstandard, non-SSA
 * form that can be more easily represented in CISL and processed by GIST.</p>
 *
 * <p>This reduction is performed by removing all PHI nodes, splitting each
 * basic block that contained a PHI node into multiple blocks, and replacing
 * the SSA variables in each block that would have been set by the PHI node
 * with the variable names that they would have been set from. The resulting
 * CFG breaks the rules of SSA by allowing variables to survive across multiple
 * basic blocks, but it also is computationally simpler, and allows SSA
 * variables to be represented in CISL as a near-infinite set of registers.</p>
 *
 * @author Adam R. Nelson [adam@sector91.com]
 */
public class PhiReducer {
    public static CFG reduce(CFG original) {
        // Sanity check.
        for (Instruction i : original.getEntry().getInsts()) {
            if (i.opcode() == OpCode.PHI) throw new IllegalArgumentException(
                "Cannot reduce a CFG with a PHI in the entry block.");
        }
        // Create a copy of the CFG
        final CFG result = new CFG();
        result.setFunc((original.getFunc()));
        result.getParams().addAll(original.getParams());
        // Split every block containing a φ-node.
        int nextID = original.getEntry().getID();
        final List<BasicBlock> blocks = new ArrayList<>();
        final Map<BasicBlock, BasicBlock> replacementMap = new HashMap<>();
        final Map<Transition, BasicBlock> jumpMap = new HashMap<>();
        for (BasicBlock bb : original.getBBs()) {
            final Set<BasicBlock> incoming = getIncomingBlocks(bb);
            if (incoming.isEmpty()) {
                final BasicBlock newbb = new BasicBlock(result);
                newbb.setID(nextID++);
                newbb.setName(bb.getName());
                newbb.getInsts().addAll(bb.getInsts());
                replacementMap.put(newbb, bb);
                blocks.add(newbb);
            } else {
                int i = 0;
                for (BasicBlock ibb : incoming) {
                    final BasicBlock fork = createPhiFork(bb, ibb, result);
                    fork.setID(nextID++);
                    fork.setName(mangle(bb.getName(), i++));
                    replacementMap.put(fork, bb);
                    jumpMap.put(new Transition(ibb, bb), fork);
                    blocks.add(fork);
                }
            }
        }
        // Remap all of the jumps in the new blocks.
        for (BasicBlock bb : blocks) {
            remapJumps(bb, replacementMap.get(bb), jumpMap);
            result.getBBs().add(bb);
            result.getBBNs().put(bb.getID(), bb.getName(), bb);
            if (replacementMap.get(bb) == original.getEntry()) {
                result.setEntry(bb);
            }
        }
        return result;
    }

    private static Set<BasicBlock> getIncomingBlocks(BasicBlock bb) {
        final Set<BasicBlock> incoming = new HashSet<>();
        for (Instruction i : bb.getInsts()) if (i instanceof InstPhi) {
            final InstPhi phi = (InstPhi)i;
            incoming.addAll(phi.getValueMap().keySet());
        }
        return incoming;
    }

    private static BasicBlock createPhiFork(BasicBlock original, BasicBlock from, CFG cfg) {
        final BasicBlock result = new BasicBlock(cfg);
        for (Instruction i : original.getInsts()) {
            Instruction i2;
            switch (i.opcode()) {
                case OpCode.PHI: {
                    // There's no assignment operation in μVM IR, so instead we
                    // reduce multi-branch φ-nodes to single-branch φ-nodes.
                    final InstPhi oi = (InstPhi)i;
                    final Map<BasicBlock, Value> map = new HashMap<>();
                    map.put(from, oi.getValueFrom(from));
                    i2 = new InstPhi(oi.getType(), map);
                    break;
                }
                // The remaining cases duplicate branch instructions, so that
                // they can be overwritten if necessary in the next step.
                case OpCode.BRANCH: {
                    final InstBranch oi = (InstBranch) i;
                    i2 = new InstBranch(oi.getDest());
                    break;
                }
                case OpCode.BRANCH2: {
                    final InstBranch2 oi = (InstBranch2) i;
                    i2 = new InstBranch2(oi.getCond(), oi.getIfTrue(), oi.getIfFalse());
                    break;
                }
                case OpCode.INVOKE: {
                    final InstInvoke oi = (InstInvoke) i;
                    final List<Value> args = new ArrayList<>(), keepAlives = new ArrayList<>();
                    for (UseBox ub : oi.getArgs()) args.add(ub.getSrc());
                    for (UseBox ub : oi.getKeepAlives()) keepAlives.add(ub.getSrc());
                    i2 = new InstInvoke(oi.getSig(), oi.getFunc(), args, keepAlives, oi.getNor(),
                            oi.getExc());
                    break;
                }
                case OpCode.IINVOKE: {
                    final InstIInvoke oi = (InstIInvoke) i;
                    final List<Value> args = new ArrayList<>(), keepAlives = new ArrayList<>();
                    for (UseBox ub : oi.getArgs()) args.add(ub.getSrc());
                    for (UseBox ub : oi.getKeepAlives()) keepAlives.add(ub.getSrc());
                    i2 = new InstIInvoke(oi.getIFunc(), args, oi.getNor(),
                            oi.getExc(), keepAlives);
                    break;
                }
                case OpCode.SWITCH: {
                    final InstSwitch oi = (InstSwitch) i;
                    final Map<Value, BasicBlock> cases = new HashMap<>();
                    for (Map.Entry<UseBox, BasicBlock> e : oi.getCases().entrySet()) {
                        cases.put(e.getKey().getSrc(), e.getValue());
                    }
                    i2 = new InstSwitch(oi.getOpndType(), oi.getOpnd(), oi.getDefaultDest(),
                            cases);
                    break;
                }
                case OpCode.WATCHPOINT: {
                    final InstWatchPoint oi = (InstWatchPoint) i;
                    final List<Value> keepAlives = new ArrayList<>();
                    for (UseBox ub : oi.getKeepAlives()) keepAlives.add(ub.getSrc());
                    i2 = new InstWatchPoint(oi.getWatchPointId(), oi.getType(),
                            oi.getDisabled(), oi.getNor(), oi.getExc(), keepAlives);
                    break;
                }
                default: i2 = i;
            }
            i2.setName(i.getName());
            i2.setID(i.getID());
            result.addInstruction(i2);
        }
        return result;
    }

    private static void remapJumps(BasicBlock bb, BasicBlock originalBlock,
            Map<Transition, BasicBlock> jumpMap) {
        for (Instruction i : bb.getInsts()) switch (i.opcode()) {
            case OpCode.BRANCH: {
                final InstBranch oi = (InstBranch) i;
                oi.setDest(remapJump(originalBlock, oi.getDest(), jumpMap));
                break;
            }
            case OpCode.BRANCH2:{
                final InstBranch2 oi = (InstBranch2) i;
                oi.setIfFalse(remapJump(originalBlock, oi.getIfFalse(), jumpMap));
                oi.setIfTrue(remapJump(originalBlock, oi.getIfTrue(), jumpMap));
                break;
            }
            case OpCode.SWITCH: {
                final InstSwitch oi = (InstSwitch) i;
                for (Map.Entry<UseBox, BasicBlock> c : oi.getCases().entrySet()) {
                    oi.getCases().put(c.getKey(), remapJump(originalBlock, c.getValue(), jumpMap));
                }
                oi.setDefaultDest(remapJump(originalBlock, oi.getDefaultDest(), jumpMap));
                break;
            }
            case OpCode.INVOKE: {
                final InstInvoke oi = (InstInvoke) i;
                oi.setNor(remapJump(originalBlock, oi.getNor(), jumpMap));
                oi.setExc(remapJump(originalBlock, oi.getExc(), jumpMap));
                break;
            }
            case OpCode.IINVOKE: {
                final InstIInvoke oi = (InstIInvoke) i;
                oi.setNor(remapJump(originalBlock, oi.getNor(), jumpMap));
                oi.setExc(remapJump(originalBlock, oi.getExc(), jumpMap));
                break;
            }
            case OpCode.WATCHPOINT: {
                final InstWatchPoint oi = (InstWatchPoint) i;
                oi.setNor(remapJump(originalBlock, oi.getNor(), jumpMap));
                oi.setExc(remapJump(originalBlock, oi.getExc(), jumpMap));
                oi.setDisabled(remapJump(originalBlock, oi.getDisabled(), jumpMap));
                break;
            }
        }
    }

    private static BasicBlock remapJump(BasicBlock from, BasicBlock to,
            Map<Transition, BasicBlock> jumpMap) {
        final BasicBlock jump = jumpMap.get(new Transition(from, to));
        return jump == null ? to : jump;
    }

    private static String mangle(String name, int number) {
        return name + "__phi__" + number;
    }

    private static class Transition {
        final String nameA, nameB;
        final int idA, idB;

        Transition(BasicBlock a, BasicBlock b) {
            nameA = a.getName();
            nameB = b.getName();
            idA = a.getID();
            idB = b.getID();
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;

            Transition that = (Transition) o;

            return idA == that.idA && idB == that.idB &&
                   nameA.equals(that.nameA) && nameB.equals(that.nameB);
        }

        @Override
        public int hashCode() {
            int result = nameA.hashCode();
            result = 31 * result + nameB.hashCode();
            result = 31 * result + idA;
            result = 31 * result + idB;
            return result;
        }
    }
}
