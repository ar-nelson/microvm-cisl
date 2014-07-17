package uvm.refimpl.mem.simpleimmix;

import static org.junit.Assert.*;

import org.junit.After;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import uvm.Bundle;
import uvm.ir.text.input.TestingHelper;
import uvm.refimpl.facade.MicroVM;
import uvm.refimpl.facade.MicroVMClient;
import uvm.refimpl.mem.ObjectMarker;
import uvm.type.Hybrid;
import uvm.type.Int;
import uvm.type.Struct;

public class TestSimpleImmixHeapWithLargerHeap {

    public static MicroVM microVM;
    public static Bundle bundle;
    public static SimpleImmixHeap heap;
    public static SimpleImmixMutator mutator;

    @BeforeClass
    public static void setUpClass() throws Exception {
        try {
            microVM = new MicroVM();
            bundle = TestingHelper
                    .parseUir("tests/uvm-refimpl-test/primitives.uir");
            microVM.addBundle(bundle);
            heap = microVM.getMemoryManager().getHeap();
        } catch (Exception e) {
            e.printStackTrace();
            throw e;
        }
    }

    @Before
    public void setUp() {
        mutator = heap.makeMutator();
    }

    @After
    public void cleanUp() {
        mutator.close();

        microVM.setClient(null);
        microVM.getMemoryManager().getHeap().mutatorTriggerAndWaitForGCEnd();
    }

    @Test
    public void testLOS() {
        Hybrid ca = (Hybrid) bundle.getTypeNs().getByName("@hCharArray");

        final long unitLen = 128 * 1024;
        final int units = 15;
        final long[] as = new long[units];

        microVM.setClient(new MicroVMClient() {
            @Override
            public void markExternalRoots(ObjectMarker marker) {
                for (int i = 0; i < units; i++) {
                    marker.markObjRef(as[i]);
                }
            }
        });

        for (int i = 0; i < units; i++) {
            long a = mutator.newHybrid(ca, unitLen);
            as[i] = a;
            System.out.format("as[%d] = %d\n", i, a);
        }

        microVM.setClient(new MicroVMClient() {
            @Override
            public void markExternalRoots(ObjectMarker marker) {
                for (int i = 8; i < 9; i++) {
                    marker.markObjRef(as[i]);
                }
            }
        });

        System.out.format("Allocating a relatively larger object...\n");
        long lo = mutator.newHybrid(ca, 1*1024*1024);
        System.out.format("lo = %d\n", lo);

    }
}