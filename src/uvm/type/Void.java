package uvm.type;

public class Void extends Type {

    @Override
    public <T> T accept(TypeVisitor<T> visitor) {
        return visitor.visitVoid(this);
    }
}
