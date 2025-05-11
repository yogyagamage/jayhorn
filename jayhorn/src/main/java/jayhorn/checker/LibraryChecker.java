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

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.*;
import java.util.concurrent.TimeUnit;

/**
 * This class checks if a method originating from a third-party library is reachable
 * and if it can access privileged system methods.
 */
public class LibraryChecker extends Checker {

    private final Set<String> libraryNamespaces;
    private final Set<String> privilegedMethods;
    private final ProverFactory factory;
    private Prover prover;
    private HornEncoderContext hornContext;

    public LibraryChecker(ProverFactory factory) {
        super();
        this.factory = factory;
        this.libraryNamespaces = new HashSet<>();
        this.privilegedMethods = new HashSet<>();
        loadPrivilegedMethods("privileged_methods.txt");
        loadLibraryNamespaces("library_namespaces.txt");
    }

    private void loadPrivilegedMethods(String fileName) {
        try (BufferedReader br = new BufferedReader(new FileReader(fileName))) {
            String line;
            while ((line = br.readLine()) != null) {
                if (!line.startsWith("//"))
                    privilegedMethods.add(line.trim());
            }
        } catch (IOException e) {
            System.err.println("Error loading privileged methods: " + e.getMessage());
        }
    }

    private void loadLibraryNamespaces(String fileName) {
        try (BufferedReader br = new BufferedReader(new FileReader(fileName))) {
            String line;
            while ((line = br.readLine()) != null) {
                if (!line.startsWith("//"))
                    libraryNamespaces.add(line.trim());
            }
        } catch (IOException e) {
            System.err.println("Error loading library namespaces: " + e.getMessage());
        }
    }

    private boolean isThirdPartyMethod(Method method) {
        String methodName = method.getMethodName();
        for (String prefix : libraryNamespaces) {
            if (methodName.startsWith("<" + prefix )) {
                System.out.println("Third-party method found: " + methodName);
                return true;
            }
        }
        return false;
    }

    private boolean isPrivilegedMethod(Method method) {
        String methodName = method.getMethodName();
        for (String privilegedMethod : privilegedMethods) {
            if (methodName.contains(privilegedMethod)) {
                return true;
            }
        }
        return false;
    }

    @Override
    public CheckerResult checkProgram(Program program) {
        CheckerResult result = checkVulnerability(program);
        return result;
    }

    /**
     * Extended check that not only verifies if third-party methods are reachable
     * but also checks if they can access privileged methods.
     *
     * @param program The program to check
     * @return The result of the security check
     */
    public CheckerResult checkVulnerability(Program program) {
        GhostRegister.reset();
        if (soottocfg.Options.v().memPrecision() >= 2) {
            GhostRegister.v().ghostVariableMap.put("pushID", IntType.instance());
        }
        HeapCounterTransformer hct = new HeapCounterTransformer();
        hct.transform(program);

        Set<Method> reachableThirdPartyMethods = new HashSet<>();
        HashMap<Method, Set<String>> vulnerableThirdPartyMethods = new HashMap<>();

        try {
            // Identify all reachable third-party methods
            for (Method method : program.getMethods()) {
                if (isThirdPartyMethod(method)) {
                    ProverResult result = generateAndCheckHornClauses(
                            program,
                            method
                    );
                    // ToDo: double check
                    // Check if the method is reachable
                    if (result == ProverResult.Sat) {
                        Log.info("Third-party method " + method.getMethodName() + " is reachable.");
                        reachableThirdPartyMethods.add(method);
                    }
                }
            }
            if (reachableThirdPartyMethods.isEmpty()) {
                Log.info("No third-party methods are reachable in the program.");
                return CheckerResult.UNREACHABLE;
            }
            // For each reachable third-party method, check if any privileged methods
            // are reachable from it
            for (Method thirdPartyMethod : reachableThirdPartyMethods) {
                for (Method method : program.getMethods()) {
                    if (isPrivilegedMethod(method)) {
                        // Check if the privileged method is reachable from the third-party method
                        ProverResult result = checkMethodReachability(
                                program,
                                thirdPartyMethod,
                                method
                        );
                        if (result == ProverResult.Sat) {
                            Log.info("Security violation detected: " +
                                    thirdPartyMethod.getMethodName() +
                                    " can access privileged method " +
                                    method.getMethodName());
                            if (vulnerableThirdPartyMethods.containsKey(thirdPartyMethod)) {
                                vulnerableThirdPartyMethods.get(thirdPartyMethod).add(method.getMethodName());
                            } else {
                                vulnerableThirdPartyMethods.put(thirdPartyMethod, new HashSet<>(Collections.singleton(method.getMethodName())));
                            }
                        }
                    }
                }
            }
            if (!vulnerableThirdPartyMethods.isEmpty()) {
                Log.info("Security violations detected in the program.");
                for (Map.Entry<Method, Set<String>> entry : vulnerableThirdPartyMethods.entrySet()) {
                    Log.info("Third-party method " + entry.getKey().getMethodName() + " can access privileged methods: " + entry.getValue());
                }
                return CheckerResult.VULNERABLE;
            }
            Log.info("Third-party methods are reachable but don't access privileged resources.");
            return CheckerResult.REACHABLE;
        } catch (Exception e) {
            Log.error("Error during security check: " + e.getMessage());
            return CheckerResult.UNKNOWN;
        }
    }

    /**
     * Checks if a target method is reachable from a source method in the call graph.
     */
    private ProverResult checkMethodReachability(Program program,
                                                 Method sourceMethod,
                                                 Method targetMethod) {
        try {
            Hornify hf = new Hornify(factory);
            this.hornContext = hf.toHorn(program, -1, HornEncoderContext.GeneratedAssertions.REACHABILITY);
            this.prover = hf.getProver();
            List<ProverHornClause> allClauses = new LinkedList<>(hf.clauses);
            // Create a path constraint from source to target
            addPathConstraint(sourceMethod, targetMethod);
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

    /**
     * Creates a constraint to check if targetMethod is reachable from sourceMethod.
     */
    private void addPathConstraint(Method sourceMethod, Method targetMethod) {
        MethodContract sourceContract = hornContext.getMethodContract(sourceMethod);
        MethodContract targetContract = hornContext.getMethodContract(targetMethod);
        if (sourceContract == null || targetContract == null) {
            Log.error("Missing contract for method check");
            return;
        }
        HornPredicate sourcePre = sourceContract.precondition;
        HornPredicate targetPre = targetContract.precondition;
        Map<Variable, ProverExpr> sourceVarMap = new HashMap<>();
        Map<Variable, ProverExpr> targetVarMap = new HashMap<>();
        try {
            ProverExpr sourceAtom = sourcePre.instPredicate(sourceVarMap);
            ProverExpr targetAtom = targetPre.instPredicate(targetVarMap);
            // sourceMethod -> targetMethod
            ProverHornClause reachabilityClause = prover.mkHornClause(
                    targetAtom,
                    new ProverExpr[]{sourceAtom},
                    prover.mkLiteral(true)
            );
            prover.addAssertion(reachabilityClause);
        } catch (Exception e) {
            Log.error("Failed to create path constraint: " + e.getMessage());
        }
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
