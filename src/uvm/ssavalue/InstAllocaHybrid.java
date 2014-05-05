package uvm.ssavalue;

import uvm.OpCode;
import uvm.type.Hybrid;
import uvm.type.IRef;

/**
 * Allocate Hybrid on the stack.
 */
public class InstAllocaHybrid extends Instruction {

    /**
     * The type to allocate.
     */
    private Hybrid allocType;

    /**
     * The length of the variable part of the Hybrid. Must be MicroVM.WORD_TYPE
     * i.e. Int(WORD_SIZE_BITS).
     */
    private UseBox length;

    /**
     * The type of this instruction.
     */
    private IRef type;

    public InstAllocaHybrid() {
        super();
    }

    public InstAllocaHybrid(Hybrid allocType, Value length) {
        super();
        this.allocType = allocType;
        this.type = new IRef(allocType);
        this.length = use(length);
    }

    public Hybrid getAllocType() {
        return allocType;
    }

    public void setAllocType(Hybrid allocType) {
        this.allocType = allocType;
        this.type = new IRef(allocType);
    }

    public Value getLength() {
        return length.getDst();
    }

    public void setLength(Value length) {
        assertNotReset(this.length);
        this.length = use(length);
    }

    @Override
    public IRef getType() {
        return this.type;
    }

    @Override
    public <T> T accept(ValueVisitor<T> visitor) {
        return visitor.visitAllocaHybrid(this);
    }

    @Override
    public int opcode() {
        return OpCode.ALLOCAHYBRID;
    }

}
