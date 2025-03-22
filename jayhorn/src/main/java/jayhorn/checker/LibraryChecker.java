package jayhorn.checker;

import com.google.common.base.Stopwatch;
import jayhorn.Log;
import jayhorn.Options;
import jayhorn.hornify.HornEncoderContext;
import jayhorn.hornify.HornPredicate;
import jayhorn.hornify.Hornify;
import jayhorn.hornify.MethodContract;
import jayhorn.solver.*;
import jayhorn.utils.GhostRegister;
import jayhorn.utils.HeapCounterTransformer;
import soottocfg.cfg.Program;
import soottocfg.cfg.method.Method;
import soottocfg.cfg.type.IntType;
import soottocfg.cfg.variable.Variable;

import java.util.*;
import java.util.concurrent.TimeUnit;

/**
 * This class checks if a method originating from a third-party library is reachable.
 */
public class LibraryChecker extends Checker {

    private final Set<String> libraryNamespaces;
    private final ProverFactory factory;
    private Prover prover;
    private HornEncoderContext hornContext;

    public LibraryChecker(ProverFactory factory) {
        super();
        this.factory = factory;
        this.libraryNamespaces = new HashSet<>();
        addLibraryNamespaces();
    }

    private void addLibraryNamespaces() {
        libraryNamespaces.add("<org.apache.");
    }

    private boolean isThirdPartyMethod(Method method) {
        String methodName = method.getMethodName();
        for (String prefix : libraryNamespaces) {
            if (methodName.startsWith(prefix)) {
                return true;
            }
        }
        return false;
    }

    @Override
    public CheckerResult checkProgram(Program program) {
        boolean isReachable = isMethodReachable(program);
        return isReachable ? CheckerResult.REACHABLE : CheckerResult.UNREACHABLE;
    }

    public boolean isMethodReachable(Program program) {
        GhostRegister.reset();
        if (soottocfg.Options.v().memPrecision() >= 2) {
            GhostRegister.v().ghostVariableMap.put("pushID", IntType.instance());
        }
        HeapCounterTransformer hct = new HeapCounterTransformer();
        hct.transform(program);
        try {
            for (Method method : program.getMethods()) {
                if (isThirdPartyMethod(method)) {
                    ProverResult result = generateAndCheckHornClauses(
                            program,
                            method
                    );
                    if (result == ProverResult.Sat) {
                        Log.info("Third-party method " + method.getMethodName() + " is reachable.");
                        return true;
                    }
                }
            }
        } catch (Exception e) {
            Log.error("Error during reachability check: " + e.getMessage());
        }
        Log.info("No third-party methods are reachable in the program.");
        return false;
    }

    private ProverResult generateAndCheckHornClauses(Program program,
                                                     Method targetMethod) {
        try {
            Hornify hf = new Hornify(factory);
            Stopwatch toHornTimer = Stopwatch.createStarted();
            this.hornContext = hf.toHorn(program, -1, HornEncoderContext.GeneratedAssertions.REACHABILITY);
            toHornTimer.stop();
            this.prover = hf.getProver();
            List<ProverHornClause> allClauses = new LinkedList<>(hf.clauses);
            addDummyAssertion(targetMethod);
            for (ProverHornClause clause : allClauses) {
                prover.addAssertion(clause);
            }
            ProverResult result;
            if (Options.v().getTimeout() > 0) {
                int timeoutInMsec = (int) TimeUnit.SECONDS.toMillis(Options.v().getTimeout());
                prover.checkSat(false);
                result = prover.getResult(timeoutInMsec);
            } else {
                result = prover.checkSat(true);
            }
            return result;
        } catch (Exception e) {
            throw new RuntimeException("Horn clause generation failed", e);
        } finally {
            if (prover != null) {
                prover.shutdown();
            }
        }
    }

    private void addDummyAssertion(Method method) {
        MethodContract contract = hornContext.getMethodContract(method);
        if (contract == null) {
            Log.error("No contract found for method: " + method.getMethodName());
            return;
        }
        HornPredicate pre = contract.precondition;
        Map<Variable, ProverExpr> varMap = new HashMap<>();
        try {
            ProverExpr preAtom = pre.instPredicate(varMap);
            ProverHornClause clause = prover.mkHornClause(
                    prover.mkLiteral(false),
                    new ProverExpr[]{preAtom},
                    prover.mkLiteral(true)
            );
            prover.addAssertion(clause);
        } catch (Exception e) {
            Log.error("Failed to inject assertion for method: " + method.getMethodName());
        }
    }
}
