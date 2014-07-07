package uvm.refimpl.mem.simpleimmix;

import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

import uvm.platformsupport.MemorySupport;
import uvm.platformsupport.ordinaryjava.UnsafeMemorySupport;
import uvm.refimpl.mem.Mutator;

/**
 * A heap which uses the simplified Immix GC algorithm.
 * <p>
 * 
 */
public class SimpleImmixHeap {
    public static final long GC_HEADER_SIZE_BITS = 64;
    public static final long GC_HEADER_SIZE_BYTES = 8;
    public static final long GC_HEADER_SIZE_LOG = 6;

    public MemorySupport memorySupport = new UnsafeMemorySupport();

    public SimpleImmixSpace space;

    public int liveMutators;
    public int mutatorsStopped;

    public Lock lock; // For almost everything.
    public Condition gcCanStart;
    public Condition gcFinished;

    private boolean globalPauseFlag;
    
    public SimpleImmixCollector collector;
    public Thread collectorThread;

    public SimpleImmixHeap(long begin, long size) {
        super();

        space = new SimpleImmixSpace(this, "SimpleImmixSpace", begin,
                size);

        liveMutators = 0;
        mutatorsStopped = 0;

        lock = new ReentrantLock();
        gcCanStart = lock.newCondition();
        gcFinished = lock.newCondition();

        globalPauseFlag = false;
        
        collector = new SimpleImmixCollector(this);
        collectorThread = new Thread(collector);
        collectorThread.setDaemon(true);
        collectorThread.start();
    }

    public void triggerAndWaitForGC() {
        try {
            globalPauseFlag = true;
            mutatorsStopped += 1;
            if (mutatorsStopped == liveMutators) {
                gcCanStart.signal();
            }

            while (globalPauseFlag) {
                try {
                    gcFinished.await();
                } catch (InterruptedException e) {
                    // Do nothing
                }
            }

            mutatorsStopped -= 1;
        } finally {
            lock.unlock();
        }

    }

    public boolean getGlobalPauseFlag() {
        boolean rv;

        lock.lock();
        try {
            rv = globalPauseFlag;
        } finally {
            lock.unlock();
        }

        return rv;
    }

    public Mutator makeMutator() {
        lock.lock();
        Mutator mutator;
        try {
            mutator = new SimpleImmixMutator(this, space);
            liveMutators++;
        } finally {
            lock.unlock();
        }
        return mutator;
    }

}