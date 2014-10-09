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
        // Split every block containing a PHI instruction.
        int nextID = original.getEntry().getID();
        final List<BasicBlock> blocks = new ArrayList<>();
        final Map<BasicBlock, BasicBlock> replacementMap = new HashMap<>();
        final Map<Transition, BasicBlock> jumpMap = new HashMap<>();
        for (BasicBlock bb : original.getBBs()) {
            final Map<Transition, List<UseBox>> phis = extractPhis(bb);
            if (phis.isEmpty()) {
                final BasicBlock newbb = new BasicBlock(result);
                newbb.setID(nextID++);
                newbb.setName(bb.getName());
                newbb.getInsts().addAll(bb.getInsts());
                blocks.add(newbb);
            } else {
                int i = 0;
                for (Map.Entry<Transition, List<UseBox>> e : phis.entrySet()) {
                    final BasicBlock fork = createPhiFork(bb, result, e.getValue());
                    fork.setID(nextID++);
                    fork.setName(mangle(bb.getName(), i++));
                    replacementMap.put(fork, bb);
                    jumpMap.put(e.getKey(), fork);
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

    private static Map<Transition, List<UseBox>> extractPhis(BasicBlock bb) {
        final Map<Transition, List<UseBox>> phis = new HashMap<>();
        for (Instruction i : bb.getInsts()) if (i instanceof InstPhi) {
            final InstPhi phi = (InstPhi)i;
            for (BasicBlock key : phi.getValueMap().keySet()) {
                final Transition t = new Transition(key, bb);
                if (phis.containsKey(t)) {
                    phis.get(t).add(phi.getValueMap().get(key));
                } else {
                    final List<UseBox> list = new ArrayList<>();
                    list.add(phi.getValueMap().get(key));
                    phis.put(t, list);
                }
            }
        }
        return phis;
    }

    private static BasicBlock createPhiFork(BasicBlock original, CFG cfg,
            List<UseBox> transfers) {
        final BasicBlock result = new BasicBlock(cfg);
        // TODO: Determine whether name and id of instructions matters.
        // Right now, this code ignores those values.
        for (Instruction i : original.getInsts()) switch (i.opcode()) {
            case OpCode.ALLOCAHYBRID: {
                final InstAllocaHybrid oi = (InstAllocaHybrid) i;
                result.addInstruction(new InstAllocaHybrid(
                        oi.getAllocType(), remapValue(oi.getLength(), transfers)));
                break;
            }
            case OpCode.ATOMICRMW: {
                final InstAtomicRMW oi = (InstAtomicRMW) i;
                result.addInstruction(new InstAtomicRMW(oi.getOrdering(), oi.getOptr(),
                        oi.getReferentType(), remapValue(oi.getLocation(), transfers),
                        remapValue(oi.getOpnd(), transfers)));
                break;
            }
            case OpCode.ADD:
            case OpCode.SUB:
            case OpCode.MUL:
            case OpCode.SDIV:
            case OpCode.SREM:
            case OpCode.UDIV:
            case OpCode.UREM:
            case OpCode.SHL:
            case OpCode.LSHR:
            case OpCode.ASHR:
            case OpCode.AND:
            case OpCode.OR:
            case OpCode.XOR:
            case OpCode.FADD:
            case OpCode.FSUB:
            case OpCode.FMUL:
            case OpCode.FDIV:
            case OpCode.FREM: {
                final InstBinOp oi = (InstBinOp) i;
                result.addInstruction(new InstBinOp(oi.getType(), oi.getOptr(),
                        remapValue(oi.getOp1(), transfers), remapValue(oi.getOp2(), transfers)));
                break;
            }
            case OpCode.BRANCH: {
                final InstBranch oi = (InstBranch) i;
                result.addInstruction(new InstBranch(oi.getDest()));
                break;
            }
            case OpCode.BRANCH2: {
                final InstBranch2 oi = (InstBranch2) i;
                result.addInstruction(new InstBranch2(remapValue(oi.getCond(), transfers),
                        oi.getIfTrue(), oi.getIfFalse()));
                break;
            }
            case OpCode.CALL: {
                final InstCall oi = (InstCall) i;
                final List<Value> args = new ArrayList<>(), keepAlives = new ArrayList<>();
                for (UseBox ub : oi.getArgs()) args.add(remapValue(ub.getSrc(), transfers));
                for (UseBox ub : oi.getKeepAlives()) keepAlives.add(remapValue(ub.getSrc(),
                        transfers));
                result.addInstruction(new InstCall(oi.getSig(),
                        remapValue(oi.getFunc(), transfers), args, keepAlives));
                break;
            }
            case OpCode.CCALL: {
                final InstCCall oi = (InstCCall) i;
                final List<Value> args = new ArrayList<>();
                for (UseBox ub : oi.getArgs()) args.add(remapValue(ub.getSrc(), transfers));
                result.addInstruction(new InstCCall(oi.getCallConv(), oi.getSig(),
                        remapValue(oi.getFunc(), transfers), args));
                break;
            }
            case OpCode.EQ:
            case OpCode.NE:
            case OpCode.SGE:
            case OpCode.SGT:
            case OpCode.SLE:
            case OpCode.SLT:
            case OpCode.UGE:
            case OpCode.UGT:
            case OpCode.ULE:
            case OpCode.ULT:
            case OpCode.FFALSE:
            case OpCode.FTRUE:
            case OpCode.FUNO:
            case OpCode.FUEQ:
            case OpCode.FUNE:
            case OpCode.FUGT:
            case OpCode.FUGE:
            case OpCode.FULT:
            case OpCode.FULE:
            case OpCode.FORD:
            case OpCode.FOEQ:
            case OpCode.FONE:
            case OpCode.FOGT:
            case OpCode.FOGE:
            case OpCode.FOLT:
            case OpCode.FOLE: {
                final InstCmp oi = (InstCmp) i;
                result.addInstruction(new InstCmp(oi.getOpndType(), oi.getOptr(),
                        remapValue(oi.getOp1(), transfers), remapValue(oi.getOp2(), transfers)));
                break;
            }
            case OpCode.CMPXCHG: {
                final InstCmpXchg oi = (InstCmpXchg) i;
                result.addInstruction(new InstCmpXchg(oi.getOrderingSucc(), oi.getOrderingFail(),
                        oi.getReferentType(), remapValue(oi.getLocation(), transfers),
                        remapValue(oi.getExpected(), transfers),
                        remapValue(oi.getDesired(), transfers)));
                break;
            }
            case OpCode.TRUNC:
            case OpCode.ZEXT:
            case OpCode.SEXT:
            case OpCode.FPTRUNC:
            case OpCode.FPEXT:
            case OpCode.FPTOUI:
            case OpCode.FPTOSI:
            case OpCode.UITOFP:
            case OpCode.SITOFP:
            case OpCode.BITCAST:
            case OpCode.REFCAST:
            case OpCode.IREFCAST:
            case OpCode.FUNCCAST: {
                final InstConversion oi = (InstConversion) i;
                result.addInstruction(new InstConversion(oi.getFromType(), oi.getToType(),
                        oi.getOptr(), remapValue(oi.getOpnd(), transfers)));
                break;
            }
            case OpCode.EXTRACTVALUE: {
                final InstExtractValue oi = (InstExtractValue) i;
                result.addInstruction(new InstExtractValue(oi.getStructType(), oi.getIndex(),
                        remapValue(oi.getOpnd(), transfers)));
                break;
            }
            case OpCode.GETELEMIREF: {
                final InstGetElemIRef oi = (InstGetElemIRef) i;
                result.addInstruction(new InstGetElemIRef(oi.getReferentType(),
                        remapValue(oi.getIndex(), transfers),
                        remapValue(oi.getOpnd(), transfers)));
                break;
            }
            case OpCode.GETFIELDIREF: {
                final InstGetFieldIRef oi = (InstGetFieldIRef) i;
                result.addInstruction(new InstGetFieldIRef(oi.getReferentType(), oi.getIndex(),
                        remapValue(oi.getOpnd(), transfers)));
                break;
            }
            case OpCode.GETFIXEDPARTIREF: {
                final InstGetFixedPartIRef oi = (InstGetFixedPartIRef) i;
                result.addInstruction(new InstGetFixedPartIRef(oi.getReferentType(),
                        remapValue(oi.getOpnd(), transfers)));
                break;
            }
            case OpCode.GETIREF: {
                final InstGetIRef oi = (InstGetIRef) i;
                result.addInstruction(new InstGetIRef(oi.getReferentType(),
                        remapValue(oi.getOpnd(), transfers)));
                break;
            }
            case OpCode.GETVARPARTIREF: {
                final InstGetVarPartIRef oi = (InstGetVarPartIRef) i;
                result.addInstruction(new InstGetVarPartIRef(oi.getReferentType(),
                        remapValue(oi.getOpnd(), transfers)));
                break;
            }
            case OpCode.ICALL: {
                final InstICall oi = (InstICall) i;
                final List<Value> args = new ArrayList<>(), keepAlives = new ArrayList<>();
                for (UseBox ub : oi.getArgs()) args.add(remapValue(ub.getSrc(), transfers));
                for (UseBox ub : oi.getKeepAlives()) keepAlives.add(remapValue(ub.getSrc(),
                        transfers));
                result.addInstruction(new InstICall(oi.getIFunc(), args, keepAlives));
                break;
            }
            case OpCode.INVOKE: {
                final InstInvoke oi = (InstInvoke) i;
                final List<Value> args = new ArrayList<>(), keepAlives = new ArrayList<>();
                for (UseBox ub : oi.getArgs()) args.add(remapValue(ub.getSrc(), transfers));
                for (UseBox ub : oi.getKeepAlives()) keepAlives.add(remapValue(ub.getSrc(),
                        transfers));
                result.addInstruction(new InstInvoke(oi.getSig(),
                        remapValue(oi.getFunc(), transfers), args, keepAlives, oi.getNor(),
                        oi.getExc()));
                break;
            }
            case OpCode.IINVOKE: {
                final InstIInvoke oi = (InstIInvoke) i;
                final List<Value> args = new ArrayList<>(), keepAlives = new ArrayList<>();
                for (UseBox ub : oi.getArgs()) args.add(remapValue(ub.getSrc(), transfers));
                for (UseBox ub : oi.getKeepAlives()) keepAlives.add(remapValue(ub.getSrc(),
                        transfers));
                result.addInstruction(new InstIInvoke(oi.getIFunc(), args, oi.getNor(),
                        oi.getExc(), keepAlives));
                break;
            }
            case OpCode.LOAD: {
                final InstLoad oi = (InstLoad) i;
                result.addInstruction(new InstLoad(oi.getOrdering(), oi.getReferentType(),
                        remapValue(oi.getLocation(), transfers)));
                break;
            }
            case OpCode.NEWHYBRID: {
                final InstNewHybrid oi = (InstNewHybrid) i;
                result.addInstruction(new InstNewHybrid(oi.getAllocType(),
                        remapValue(oi.getLength(), transfers)));
                break;
            }
            case OpCode.NEWSTACK: {
                final InstNewStack oi = (InstNewStack) i;
                final List<Value> args = new ArrayList<>();
                for (UseBox ub : oi.getArgs()) args.add(remapValue(ub.getSrc(), transfers));
                result.addInstruction(new InstNewStack(oi.getSig(),
                        remapValue(oi.getFunc(), transfers), args));
                break;
            }
            case OpCode.PHI:
                // Do nothing; drop all PHI nodes.
                break;
            case OpCode.RET: {
                final InstRet oi = (InstRet) i;
                result.addInstruction(new InstRet(oi.getRetType(),
                        remapValue(oi.getRetVal(), transfers)));
                break;
            }
            case OpCode.SELECT: {
                final InstSelect oi = (InstSelect) i;
                result.addInstruction(new InstSelect(oi.getType(),
                        remapValue(oi.getCond(), transfers), remapValue(oi.getIfTrue(), transfers),
                        remapValue(oi.getIfFalse(), transfers)));
                break;
            }
            case OpCode.SHIFTIREF: {
                final InstShiftIRef oi = (InstShiftIRef) i;
                result.addInstruction(new InstShiftIRef(oi.getReferentType(),
                        remapValue(oi.getOffset(), transfers),
                        remapValue(oi.getOpnd(), transfers)));
                break;
            }
            case OpCode.STORE: {
                final InstStore oi = (InstStore) i;
                result.addInstruction(new InstStore(oi.getOrdering(), oi.getReferentType(),
                        remapValue(oi.getLocation(), transfers),
                        remapValue(oi.getNewVal(), transfers)));
                break;
            }
            case OpCode.SWITCH: {
                final InstSwitch oi = (InstSwitch) i;
                final Map<Value, BasicBlock> cases = new HashMap<>();
                for (Map.Entry<UseBox, BasicBlock> e : oi.getCases().entrySet()) {
                    cases.put(e.getKey().getSrc(), e.getValue());
                }
                result.addInstruction(new InstSwitch(oi.getOpndType(),
                        remapValue(oi.getOpnd(), transfers), oi.getDefaultDest(), cases));
                break;
            }
            case OpCode.TAILCALL: {
                final InstTailCall oi = (InstTailCall) i;
                final List<Value> args = new ArrayList<>();
                for (UseBox ub : oi.getArgs()) args.add(remapValue(ub.getSrc(), transfers));
                result.addInstruction(new InstTailCall(oi.getSig(),
                        remapValue(oi.getFunc(), transfers), args));
                break;
            }
            case OpCode.THROW: {
                final InstThrow oi = (InstThrow) i;
                result.addInstruction(new InstThrow(remapValue(oi.getException(), transfers)));
                break;
            }
            case OpCode.WATCHPOINT: {
                final InstWatchPoint oi = (InstWatchPoint) i;
                final List<Value> keepAlives = new ArrayList<>();
                for (UseBox ub : oi.getKeepAlives()) keepAlives.add(remapValue(ub.getSrc(),
                        transfers));
                result.addInstruction(new InstWatchPoint(oi.getWatchPointId(), oi.getType(),
                        oi.getDisabled(), oi.getNor(), oi.getExc(), keepAlives));
                break;
            }
            default:
                result.addInstruction(i);
        }
        return result;
    }

    private static Value remapValue(Value orig, List<UseBox> transfers) {
        for (UseBox ub : transfers) if (ub.getDst() == orig) return ub.getSrc();
        return orig;
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

    public static void main(String[] args) {
        // TODO: Implement me!
        System.err.println("placeholder");
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
