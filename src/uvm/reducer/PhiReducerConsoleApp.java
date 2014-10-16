package uvm.reducer;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import parser.uIRLexer;
import parser.uIRParser;
import uvm.Bundle;
import uvm.Function;
import uvm.ir.text.input.RecursiveBundleBuilder;
import uvm.ir.text.output.IRTextWriter;

import java.io.*;

public class PhiReducerConsoleApp {

    public static Bundle parseUir(InputStream is, Bundle globalBundle) throws IOException {
        ANTLRInputStream input = new ANTLRInputStream(is);
        uIRLexer lexer = new uIRLexer(input);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        uIRParser parser = new uIRParser(tokens);
        uIRParser.IrContext ir = parser.ir();

        if (parser.getNumberOfSyntaxErrors() > 0) {
            // TODO: Better error output.
            throw new RuntimeException("Syntax error");
        }

        RecursiveBundleBuilder rbb = globalBundle == null ? new RecursiveBundleBuilder()
                : new RecursiveBundleBuilder(globalBundle);
        rbb.build(ir);
        return rbb.getBundle();
    }

    public static void main(String[] args) {
        System.out.println(new File(".").getAbsolutePath());
        for (String filename : args) {
            System.out.println("Reducing " + filename + "...");
            final String outFilename = (filename.endsWith(".uir") ?
                    filename.substring(0, filename.length() - 4) : filename) +
                    ".reduced.uir";
            try {
                final Bundle bundle = parseUir(new FileInputStream(filename), null);
                for (Function fn : bundle.getFuncNs().getObjects()) {
                    if (fn.getCFG() != null) {
                        System.out.println("Reducing function '" + fn.getName() + "'...");
                        final int in = fn.getCFG().getBBs().size();
                        fn.setCFG(PhiReducer.reduce(fn.getCFG()));
                        final int out = fn.getCFG().getBBs().size();
                        System.out.println("Function reduction successful. (IN: " + in +
                                " BBs, OUT: " + out + " BBs)");
                    } else {
                        System.out.println("Skipping function '" + fn.getName() + "' (no CFG).");
                    }
                }
                final FileWriter writer = new FileWriter(outFilename);
                new IRTextWriter(writer).writeBundle(bundle);
                System.out.println("Successfully reduced " + filename + " -> " + outFilename +
                        ".");
            } catch (Exception ex) {
                System.out.println("Failed to reduce " + filename);
                ex.printStackTrace();
            }
        }
    }
}
