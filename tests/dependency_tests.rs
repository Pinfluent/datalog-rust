use datalog::*;

#[test]
fn test_dependency_resolution() {
    let mut rules = vec![
        // If X depends on G and G changed, X should run
        rule!(
            atom!("should_run", var!("X")) =>
            atom!("depends_on", var!("X"), var!("G")),
            atom!("changed", var!("G"))
        ),
    ];

    // Create facts for dependencies and add them as rules
    // - function_a depends on variable_1
    // - function_b depends on variable_1
    // - function_c depends on variable_2
    rules.push(rule!(atom!(
        "depends_on",
        symbol!("function_a"),
        symbol!("variable_1")
    )));
    rules.push(rule!(atom!(
        "depends_on",
        symbol!("function_b"),
        symbol!("variable_1")
    )));
    rules.push(rule!(atom!(
        "depends_on",
        symbol!("function_c"),
        symbol!("variable_2")
    )));

    // Add the fact that variable_1 changed
    rules.push(rule!(atom!("changed", symbol!("variable_1"))));

    let program = Program::new(rules);
    let result = program.solve();

    // Both function_a and function_b should run (they depend on variable_1)
    // function_c should not run (depends on variable_2)
    assert!(result
        .atoms
        .contains(&atom!("should_run", symbol!("function_a"))));
    assert!(result
        .atoms
        .contains(&atom!("should_run", symbol!("function_b"))));
    assert!(!result
        .atoms
        .contains(&atom!("should_run", symbol!("function_c"))));
}

#[test]
fn test_chained_dependencies() {
    let rules = vec![
        // Base rules for dependency resolution
        // Direct dependency: If X depends on G and G changed, X should run
        rule!(
            atom!("should_run", var!("X")) =>
            atom!("depends_on", var!("X"), var!("G")),
            atom!("changed", var!("G"))
        ),
        // Transitive dependency: If X depends on Y and Y should run, X should run too
        rule!(
            atom!("should_run", var!("X")) =>
            atom!("depends_on", var!("X"), var!("Y")),
            atom!("should_run", var!("Y"))
        ),
        // Chain: func_c depends on func_b depends on func_a depends on var_x
        rule!(atom!("depends_on", symbol!("func_a"), symbol!("var_x"))),
        rule!(atom!("depends_on", symbol!("func_b"), symbol!("func_a"))),
        rule!(atom!("depends_on", symbol!("func_c"), symbol!("func_b"))),
        // Trigger the change
        rule!(atom!("changed", symbol!("var_x"))),
    ];

    let program = Program::new(rules);
    let result = program.solve();

    // All functions should run because of the chain of dependencies
    assert!(result
        .atoms
        .contains(&atom!("should_run", symbol!("func_a"))));
    assert!(result
        .atoms
        .contains(&atom!("should_run", symbol!("func_b"))));
    assert!(result
        .atoms
        .contains(&atom!("should_run", symbol!("func_c"))));
}

#[test]
fn test_cycle_detection() {
    let rules = vec![
        // Rule to build transitive dependency relationships
        // "depends_transitively(X,Y)" means X depends on Y either directly or through other nodes
        rule!(
            atom!("depends_transitively", var!("X"), var!("Y")) =>
            atom!("depends_on", var!("X"), var!("Y"))
        ),
        // If X depends on Y and Y depends transitively on Z, then X depends transitively on Z
        rule!(
            atom!("depends_transitively", var!("X"), var!("Z")) =>
            atom!("depends_on", var!("X"), var!("Y")),
            atom!("depends_transitively", var!("Y"), var!("Z"))
        ),
        // A cycle exists if something transitively depends on itself
        rule!(
            atom!("has_cycle", var!("X")) =>
            atom!("depends_transitively", var!("X"), var!("X"))
        ),
        // Add some cyclic dependencies
        rule!(atom!("depends_on", symbol!("func_a"), symbol!("func_b"))),
        rule!(atom!("depends_on", symbol!("func_b"), symbol!("func_c"))),
        rule!(atom!("depends_on", symbol!("func_c"), symbol!("func_a"))),
    ];

    let program = Program::new(rules);
    let result = program.solve();

    // Assert that we detected cycles
    assert!(result
        .atoms
        .contains(&atom!("has_cycle", symbol!("func_a"))));
    assert!(result
        .atoms
        .contains(&atom!("has_cycle", symbol!("func_b"))));
    assert!(result
        .atoms
        .contains(&atom!("has_cycle", symbol!("func_c"))));
}

#[test]
fn test_acyclic_dependencies() {
    let rules = vec![
        // Base rules for dependency resolution
        rule!(
            atom!("should_run", var!("X")) =>
            atom!("depends_on", var!("X"), var!("G")),
            atom!("changed", var!("G"))
        ),
        rule!(
            atom!("should_run", var!("X")) =>
            atom!("depends_on", var!("X"), var!("Y")),
            atom!("should_run", var!("Y"))
        ),
        // Rule to detect cycles (same as above)
        rule!(
            atom!("depends_transitively", var!("X"), var!("Y")) =>
            atom!("depends_on", var!("X"), var!("Y"))
        ),
        rule!(
            atom!("depends_transitively", var!("X"), var!("Z")) =>
            atom!("depends_on", var!("X"), var!("Y")),
            atom!("depends_transitively", var!("Y"), var!("Z"))
        ),
        rule!(
            atom!("has_cycle", var!("X")) =>
            atom!("depends_transitively", var!("X"), var!("X"))
        ),
        // Acyclic dependency chain
        rule!(atom!(
            "depends_on",
            symbol!("display"),
            symbol!("processor")
        )),
        rule!(atom!("depends_on", symbol!("processor"), symbol!("sensor"))),
        rule!(atom!("changed", symbol!("sensor"))),
    ];

    let program = Program::new(rules);
    let result = program.solve();

    // Assert no cycles were detected
    assert!(!result.atoms.iter().any(|atom| atom.pred_sym == "has_cycle"));

    // Assert proper propagation in acyclic graph
    assert!(result
        .atoms
        .contains(&atom!("should_run", symbol!("processor"))));
    assert!(result
        .atoms
        .contains(&atom!("should_run", symbol!("display"))));
}
