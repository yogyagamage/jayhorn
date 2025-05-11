package jayhorn;

import com.google.common.base.Stopwatch;
import jayhorn.checker.Checker;
import jayhorn.checker.EldaricaChecker;
import jayhorn.checker.LibraryChecker;
import jayhorn.checker.SpacerChecker;
import jayhorn.solver.ProverFactory;
import jayhorn.solver.princess.PrincessProverFactory;
import jayhorn.solver.spacer.SpacerProverFactory;
import jayhorn.utils.Stats;
import org.apache.log4j.Level;
import org.kohsuke.args4j.CmdLineException;
import org.kohsuke.args4j.CmdLineParser;
import soot.validation.ValidationException;
import soottocfg.cfg.Program;
import soottocfg.soot.SootToCfg;
import soottocfg.soot.SootToCfg.MemModel;

import java.io.File;
import java.nio.file.Path;
import java.nio.file.Paths;

public class Main {

    private static String parseResult(String solver, Checker.CheckerResult result) {
        switch (result) {
            case SAFE:
                return "SAFE";
            case UNSAFE:
                return "UNSAFE";
            case VULNERABLE:
                return "VULNERABLE";
            case REACHABLE:
                return "REACHABLE";
            case UNREACHABLE:
                return "UNREACHABLE";
            default:
                return "UNKNOWN";
        }
    }

    private interface CheckerCreator {
        Checker createChecker(ProverFactory factory, Program program);
    }

    private static Checker.CheckerResult performAnalysis(ProverFactory factory,
                                                         CheckerCreator checkerCreator,
                                                         String analysisName) {
        Log.info("Building CFG  ... ");
        SootToCfg soot2cfg = new SootToCfg();

        // Common configuration
        soottocfg.Options.v().setBuiltInSpecs(Options.v().useSpecs);
        soottocfg.Options.v().setResolveVirtualCalls(true);
        soottocfg.Options.v().setMemModel(MemModel.PullPush);
        soottocfg.Options.v().printJimple = Options.v().printJimple;

        // Common output directory handling
        if (Options.v().getOut() != null) {
            Path outDir = Paths.get(Options.v().getOut());
            String in = Options.v().getJavaInput();
            String outName = in.substring(in.lastIndexOf(File.separator) + 1, in.length())
                    .replace(".java", "")
                    .replace(".class", "");
            soottocfg.Options.v().setOutDir(outDir);
            soottocfg.Options.v().setOutBaseName(outName);
        }

        Stopwatch sootTocfgTimer = Stopwatch.createStarted();
        Checker.CheckerResult result = Checker.CheckerResult.UNKNOWN;

        try {
            Log.info(Options.v().getJavaInput() + Options.v().getClasspath());
            soot2cfg.run(Options.v().getJavaInput(), Options.v().getClasspath());
            Program program = soot2cfg.getProgram();
            Stats.stats().add("SootToCFG", String.valueOf(sootTocfgTimer.stop()));

            Log.info(analysisName + " Verification ... ");
            Checker checker = checkerCreator.createChecker(factory, program);
            result = checker.checkProgram(program);
        } catch (ValidationException e) {
            Log.info("Byte code rejected by bytecode verifier:\n\t" + e);
            result = Checker.CheckerResult.UNKNOWN;
        }

        // Common result handling
        String prettyResult = parseResult(Options.v().getSolver(), result);
        Stats.stats().add("FinalResult", prettyResult);

        if (Options.v().stats) {
            Stats.stats().printStats();
        } else {
            System.out.println(prettyResult);
        }

        return result;
    }

    public static Checker.CheckerResult safetyAnalysis(ProverFactory factory) {
        return performAnalysis(factory, (f, p) -> {
            if ("spacer".equals(Options.v().getSolver())) {
                return new SpacerChecker(f);
            } else {
                return new EldaricaChecker(f);
            }
        }, "Safety");
    }

    public static Checker.CheckerResult reachabilityAnalysis(ProverFactory factory) {
        return performAnalysis(factory, (f, p) -> new LibraryChecker(f), "Reachability");
    }

    public static void main(String[] args) {
        // Hardcoded arguments equivalent to:
        // java -jar jayhorn/build/libs/jayhorn.jar -j /Users/yogyagamage/Documents/UdeM/MSR/weaverSbomMiner/target/WeaverSbomMiner.jar -cfg
        String[] hardcodedArgs = {
                "-j", "example/hello-nw",
                "-cfg", "-checker", "safety"
        };

        Options options = Options.v();
        CmdLineParser parser = new CmdLineParser(options);

        try {
            // Parse hardcoded arguments instead of actual args
            parser.parseArgument(hardcodedArgs);

            if (Options.v().version) {
                System.out.println(getVersion());
                return;
            }

            options.updateSootToCfgOptions();
            ProverFactory factory = null;
            if ("spacer".equals(Options.v().getSolver())) {
                factory = new SpacerProverFactory();
            } else if ("eldarica".equals(Options.v().getSolver())) {
                factory = new PrincessProverFactory();
            } else {
                throw new RuntimeException("Unknown solver: " + Options.v().getSolver() + ". Using Eldarica instead.");
            }

            if (Options.v().verbose) Log.v().setLevel(Level.INFO);

            Log.info("---   JayHorn : Static Analyzer for Java Programs   --- ");
            Log.info("Horn solver: " + Options.v().getSolver());

            if ("safety".equals(Options.v().getChecker())) {
                safetyAnalysis(factory);
            } else if ("theo".equals(Options.v().getChecker())) {
                reachabilityAnalysis(factory);
            } else {
                Log.error(String.format("Checker %s is unknown", Options.v().getChecker()));
            }

        } catch (CmdLineException e) {
            Log.error(e.toString());
            Log.info("Usage: java -jar jayhorn.jar [options...] -j [JAR, DIR]");
            parser.printUsage(System.err);

        } catch (Throwable t) {
            Log.error(t);
            Log.info("Execution reached error handling.");
            Stats.stats().add("Result", "UNKNOWN");
            if (Options.v().stats) {
                Stats.stats().printStats();
            } else {
                System.out.println("UNKNOWN");
            }

        } finally {
            Options.resetInstance();
            soot.G.reset();
        }
    }


    private static String getVersion() {
        final Package[] packages = Package.getPackages();
        for (final Package pkg : packages) {
            if ("JayHorn".equals(pkg.getImplementationTitle()))
                return pkg.getImplementationVersion();
        }
        return "n/a";
    }

}
