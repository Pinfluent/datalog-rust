#![no_std]

extern crate alloc;
use alloc::{vec, vec::Vec};
use core::hash::Hash;
use hashbrown::{HashMap, HashSet};

#[cfg(any(feature = "parsing", test))]
mod parsing;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Atom<P: Predicate, V: Value> {
    pub pred_sym: P,
    pub terms: Vec<Term<V>>,
}

#[macro_export]
macro_rules! atom {
    ($pred_sym:expr, $($term:expr),*) => {
        $crate::Atom {
            pred_sym: $pred_sym.to_string(),
            terms: vec![$($term),*]
        }
    };
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Term<V: Value> {
    Var(V),
    Sym(V),
}

#[macro_export]
macro_rules! var {
    ($name:expr) => {
        $crate::Term::Var($name.to_string())
    };
}

#[macro_export]
macro_rules! symbol {
    ($name:expr) => {
        $crate::Term::Sym($name.to_string())
    };
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Program<P: Predicate, V: Value> {
    rules: Vec<Rule<P, V>>,
}

pub trait Predicate: Clone + Eq + Hash {}
pub trait Value: Clone + Eq + Hash {}

impl<T: Clone + Eq + Hash> Predicate for T {}
impl<T: Clone + Eq + Hash> Value for T {}

impl<P: Predicate, V: Value> Program<P, V> {
    pub fn new(rules: Vec<Rule<P, V>>) -> Self {
        Self { rules }
    }

    pub fn solve(&self) -> KnowledgeBase<P, V> {
        assert!(
            self.rules.iter().all(Rule::is_range_restricted),
            "all rules must be range-restricted"
        );

        let mut kb = KnowledgeBase::default();
        loop {
            let mut changed = false;
            for rule in &self.rules {
                changed = changed || rule.eval(&mut kb);
            }

            if !changed {
                break;
            }
        }

        kb
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct KnowledgeBase<P: Predicate, V: Value> {
    pub atoms: HashSet<Atom<P, V>>,
}

impl<P: Predicate, V: Value> Default for KnowledgeBase<P, V> {
    fn default() -> Self {
        Self {
            atoms: HashSet::new(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Substitution<V: Value> {
    mapping: HashMap<Term<V>, Term<V>>,
}

impl<V: Value> Default for Substitution<V> {
    fn default() -> Self {
        Self {
            mapping: HashMap::new(),
        }
    }
}

impl<V: Value> Substitution<V> {
    fn lookup(&self, key: &Term<V>) -> Option<&Term<V>> {
        self.mapping.get(key)
    }

    fn apply_to_atom<P: Predicate>(&self, atom: &Atom<P, V>) -> Atom<P, V> {
        let mut atom = atom.clone();
        let terms = atom
            .terms
            .iter()
            .map(|term| match term {
                v @ Term::Var(_) => self.lookup(v).cloned().unwrap_or_else(|| v.clone()),
                Term::Sym(_) => term.clone(),
            })
            .collect();
        atom.terms = terms;
        atom
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Rule<P: Predicate, V: Value> {
    pub head: Atom<P, V>,
    pub body: Vec<Atom<P, V>>,
}

#[macro_export]
macro_rules! rule {
    ($head:expr => $($body:expr),+) => {
        $crate::Rule {
            head: $head,
            body: vec![$($body),+],
        }
    };
    ($head:expr) => {
        $crate::Rule {
            head: $head,
            body: vec![],
        }
    }
}

impl<P: Predicate, V: Value> Rule<P, V> {
    fn eval(&self, kb: &mut KnowledgeBase<P, V>) -> bool {
        let substitutions = self
            .body
            .iter()
            .fold(vec![Substitution::default()], |all_subs, atom| {
                eval_atom(kb, atom, all_subs)
            });

        let extension: Vec<_> = substitutions
            .iter()
            .map(|subs| subs.apply_to_atom(&self.head))
            .collect();

        let mut changed = false;
        for atom in extension {
            if !kb.atoms.contains(&atom) {
                changed = true;
                kb.atoms.insert(atom);
            }
        }

        changed
    }

    fn is_range_restricted(&self) -> bool {
        let body_vars: HashSet<Term<V>> = self
            .body
            .iter()
            .flat_map(|atom| atom.terms.clone())
            .filter(|term| matches!(term, Term::Var(_)))
            .collect();

        for term in &self.head.terms {
            if !matches!(term, Term::Var(_)) {
                continue;
            }

            if !body_vars.contains(term) {
                return false;
            }
        }

        true
    }
}

fn eval_atom<P: Predicate, V: Value>(
    kb: &KnowledgeBase<P, V>,
    atom: &Atom<P, V>,
    all_subs: Vec<Substitution<V>>,
) -> Vec<Substitution<V>> {
    let mut new_subs = vec![];

    for substitution in all_subs {
        let down_to_earth_atom = substitution.apply_to_atom(atom);

        for entry in kb.atoms.iter() {
            if let Some(extension) = unify(&down_to_earth_atom, entry) {
                let mut new_map = substitution.mapping.clone();
                new_map.extend(extension.mapping.into_iter());
                new_subs.push(Substitution { mapping: new_map });
            }
        }
    }

    new_subs
}

fn unify<P: Predicate, V: Value>(a: &Atom<P, V>, b: &Atom<P, V>) -> Option<Substitution<V>> {
    if a.pred_sym != b.pred_sym || a.terms.len() != b.terms.len() {
        return None;
    }

    let mut subs = Substitution::default();
    for (a_term, b_term) in a.terms.iter().zip(b.terms.iter()) {
        if matches!(b_term, Term::Var(_)) {
            panic!("The second atom is assumed to be ground")
        }

        match a_term {
            Term::Var(_) => {
                let substituted = subs.lookup(a_term);
                match substituted {
                    Some(a_term @ Term::Sym(_)) if a_term != b_term => {
                        return None;
                    }
                    _ => {
                        subs.mapping.insert(a_term.clone(), b_term.clone());
                    }
                }
            }
            Term::Sym(_) if a_term != b_term => {
                return None;
            }
            _ => {}
        }
    }

    Some(subs)
}

#[cfg(test)]
mod tests {
    use alloc::string::{String, ToString as _};

    use super::{parsing::parse, *};

    #[test]
    fn example() {
        // adviser("Andrew Rice",     "Mistral Contrastin").
        // adviser("Andy Hopper",     "Andrew Rice").
        // adviser("Alan Mycroft",    "Dominic Orchard").
        // adviser("David Wheeler",   "Andy Hopper").
        // adviser("Rod Burstall",    "Alan Mycroft").
        // adviser("Robin Milner",    "Alan Mycroft").
        let advisers = [
            ("Andrew Rice", "Mistral Contrastin"),
            ("Andy Hopper", "Andrew Rice"),
            ("Alan Mycroft", "Dominic Orchard"),
            ("David Wheeler", "Andy Hopper"),
            ("Rod Burstall", "Alan Mycroft"),
            ("Robin Milner", "Alan Mycroft"),
        ];

        let mut rules: Vec<_> = advisers
            .iter()
            .map(|(adviser, student)| rule!(atom!("adviser", symbol!(adviser), symbol!(student))))
            .collect();

        // academicAncestor(X,Y) :-
        //   adviser(X,Y).
        // academicAncestor(X,Z) :-
        //   adviser(X,Y),
        //   academicAncestor(Y,Z).
        rules.extend(vec![
            rule!(atom!("academicAncestor", var!("X"), var!("Y")) =>
                atom!("adviser", var!("X"), var!("Y"))),
            rule!(atom!("academicAncestor", var!("X"), var!("Z")) =>
                atom!("adviser", var!("X"), var!("Y")),
                atom!("academicAncestor", var!("Y"), var!("Z"))),
        ]);

        let result = Program { rules }.solve();

        // Create expected knowledge base with both adviser and academicAncestor facts
        let mut expected_atoms = advisers
            .iter()
            .map(|(adviser, student)| atom!("adviser", symbol!(adviser), symbol!(student)))
            .collect::<HashSet<_>>();

        // Add expected academic ancestor relationships
        // This should include both direct adviser relationships and transitive relationships
        let academic_ancestors = [
            ("Andrew Rice", "Mistral Contrastin"),
            ("Andy Hopper", "Andrew Rice"),
            ("Andy Hopper", "Mistral Contrastin"),
            ("Alan Mycroft", "Dominic Orchard"),
            ("David Wheeler", "Andy Hopper"),
            ("David Wheeler", "Andrew Rice"),
            ("David Wheeler", "Mistral Contrastin"),
            ("Rod Burstall", "Alan Mycroft"),
            ("Rod Burstall", "Dominic Orchard"),
            ("Robin Milner", "Alan Mycroft"),
            ("Robin Milner", "Dominic Orchard"),
        ];

        expected_atoms.extend(academic_ancestors.iter().map(|(ancestor, descendant)| {
            atom!("academicAncestor", symbol!(ancestor), symbol!(descendant))
        }));

        let expected = KnowledgeBase {
            atoms: expected_atoms,
        };

        assert_eq!(result, expected);
    }

    #[test]
    fn family_tree() {
        // Define direct parent relationships
        let parents = [
            ("Alice", "Bob"),   // Alice is Bob's parent
            ("Alice", "Carol"), // Alice is Carol's parent
            ("David", "Alice"), // David is Alice's parent
            ("Eve", "Alice"),   // Eve is Alice's parent
            ("Frank", "David"), // Frank is David's parent
            ("Grace", "David"), // Grace is David's parent
        ];

        // Create parent facts
        let mut rules: Vec<_> = parents
            .iter()
            .map(|(parent, child)| rule!(atom!("parent", symbol!(parent), symbol!(child))))
            .collect();

        // Add rules for ancestor relationship:
        // 1. Direct parent is an ancestor
        // 2. Parent of an ancestor is also an ancestor (transitivity)
        rules.extend(vec![
            rule!(atom!("ancestor", var!("X"), var!("Y")) =>
                atom!("parent", var!("X"), var!("Y"))),
            rule!(atom!("ancestor", var!("X"), var!("Z")) =>
                atom!("parent", var!("X"), var!("Y")),
                atom!("ancestor", var!("Y"), var!("Z"))),
        ]);

        let result = Program { rules }.solve();

        // Create expected knowledge base with both parent and ancestor facts
        let mut expected_atoms = parents
            .iter()
            .map(|(parent, child)| atom!("parent", symbol!(parent), symbol!(child)))
            .collect::<HashSet<_>>();

        // Add expected ancestor relationships
        // This includes both direct parent relationships and ancestral relationships
        let ancestors = [
            ("Alice", "Bob"),   // Direct parent
            ("Alice", "Carol"), // Direct parent
            ("David", "Alice"), // Direct parent
            ("David", "Bob"),   // Grandparent
            ("David", "Carol"), // Grandparent
            ("Eve", "Alice"),   // Direct parent
            ("Eve", "Bob"),     // Grandparent
            ("Eve", "Carol"),   // Grandparent
            ("Frank", "David"), // Direct parent
            ("Frank", "Alice"), // Grandparent
            ("Frank", "Bob"),   // Great-grandparent
            ("Frank", "Carol"), // Great-grandparent
            ("Grace", "David"), // Direct parent
            ("Grace", "Alice"), // Grandparent
            ("Grace", "Bob"),   // Great-grandparent
            ("Grace", "Carol"), // Great-grandparent
        ];

        expected_atoms.extend(ancestors.iter().map(|(ancestor, descendant)| {
            atom!("ancestor", symbol!(ancestor), symbol!(descendant))
        }));

        let expected = KnowledgeBase {
            atoms: expected_atoms,
        };

        assert_eq!(result, expected);
    }

    #[test]
    fn test_substitute() {
        let atom = Atom {
            pred_sym: "academicAncestor".to_string(),
            terms: vec![Term::Var("X".to_string()), Term::Var("Z".to_string())],
        };
        let subs = Substitution {
            mapping: [(Term::Var("X".to_string()), Term::Sym("Quinn".to_string()))]
                .into_iter()
                .collect(),
        };
        assert_eq!(
            Atom {
                pred_sym: "academicAncestor".to_string(),
                terms: vec![Term::Sym("Quinn".to_string()), Term::Var("Z".to_string())],
            },
            subs.apply_to_atom(&atom)
        )
    }

    #[test]
    fn test_unify() {
        let atom1 = Atom {
            pred_sym: "academicAncestor".to_string(),
            terms: vec![Term::Var("X".to_string()), Term::Var("Y".to_string())],
        };

        let atom2 = Atom {
            pred_sym: "academicAncestor".to_string(),
            terms: vec![Term::Sym("Alice".to_string()), Term::Sym("Bob".to_string())],
        };

        assert_eq!(
            Some(Substitution {
                mapping: [
                    (Term::Var("X".to_string()), Term::Sym("Alice".to_string())),
                    (Term::Var("Y".to_string()), Term::Sym("Bob".to_string()))
                ]
                .into_iter()
                .collect()
            }),
            unify(&atom1, &atom2)
        );
    }

    #[test]
    fn unify_different_predsym() {
        let atom1 = Atom {
            pred_sym: "Foo".to_string(),
            terms: vec![Term::Var("X".to_string()), Term::Var("Y".to_string())],
        };

        let atom2 = Atom {
            pred_sym: "Bar".to_string(),
            terms: vec![Term::Sym("Alice".to_string()), Term::Sym("Bob".to_string())],
        };

        assert_eq!(None, unify(&atom1, &atom2));
    }

    #[test]
    fn unify_conflicting() {
        let atom1 = Atom {
            pred_sym: "academicAncestor".to_string(),
            terms: vec![Term::Var("X".to_string()), Term::Var("X".to_string())],
        };

        let atom2 = Atom {
            pred_sym: "academicAncestor".to_string(),
            terms: vec![Term::Sym("Alice".to_string()), Term::Sym("Bob".to_string())],
        };

        assert_eq!(None, unify(&atom1, &atom2));
    }

    #[test]
    fn eval_atom_test() {
        let advisers = [
            ("Andrew Rice", "Mistral Contrastin"),
            ("Andy Hopper", "Andrew Rice"),
            ("Alan Mycroft", "Dominic Orchard"),
            ("David Wheeler", "Andy Hopper"),
            ("Rod Burstall", "Alan Mycroft"),
            ("Robin Milner", "Alan Mycroft"),
        ];

        let kb = KnowledgeBase {
            atoms: advisers
                .iter()
                .map(|(adviser, student)| Atom {
                    pred_sym: "adviser".to_string(),
                    terms: vec![
                        Term::Sym(adviser.to_string()),
                        Term::Sym(student.to_string()),
                    ],
                })
                .collect(),
        };

        let atom = Atom {
            pred_sym: "adviser".to_string(),
            terms: vec![Term::Var("X".to_string()), Term::Var("Y".to_string())],
        };

        let all_subs = vec![
            Substitution {
                mapping: [(
                    Term::Var("X".to_string()),
                    Term::Sym("David Wheeler".to_string()),
                )]
                .into_iter()
                .collect(),
            },
            Substitution {
                mapping: [(
                    Term::Var("Y".to_string()),
                    Term::Sym("Alan Mycroft".to_string()),
                )]
                .into_iter()
                .collect(),
            },
        ];

        let expected_substitutions = [
            Substitution {
                mapping: [
                    (
                        Term::Var("X".to_string()),
                        Term::Sym("David Wheeler".to_string()),
                    ),
                    (
                        Term::Var("Y".to_string()),
                        Term::Sym("Andy Hopper".to_string()),
                    ),
                ]
                .into_iter()
                .collect(),
            },
            Substitution {
                mapping: [
                    (
                        Term::Var("Y".to_string()),
                        Term::Sym("Alan Mycroft".to_string()),
                    ),
                    (
                        Term::Var("X".to_string()),
                        Term::Sym("Rod Burstall".to_string()),
                    ),
                ]
                .into_iter()
                .collect(),
            },
            Substitution {
                mapping: [
                    (
                        Term::Var("Y".to_string()),
                        Term::Sym("Alan Mycroft".to_string()),
                    ),
                    (
                        Term::Var("X".to_string()),
                        Term::Sym("Robin Milner".to_string()),
                    ),
                ]
                .into_iter()
                .collect(),
            },
        ];

        let result = eval_atom(&kb, &atom, all_subs);
        assert_eq!(expected_substitutions.len(), result.len());

        for i in 0..result.len() {
            assert!(result.contains(&expected_substitutions[i]));
            assert!(expected_substitutions.contains(&result[i]));
        }
    }

    #[test]
    fn eval_rule_projection() {
        let advisers = [
            ("Andrew Rice", "Mistral Contrastin"),
            ("Andy Hopper", "Andrew Rice"),
            ("Alan Mycroft", "Dominic Orchard"),
            ("David Wheeler", "Andy Hopper"),
            ("Rod Burstall", "Alan Mycroft"),
            ("Robin Milner", "Alan Mycroft"),
        ];

        let adviser_facts: HashSet<_> = advisers
            .iter()
            .map(|(adviser, student)| Atom {
                pred_sym: "adviser".to_string(),
                terms: vec![
                    Term::Sym(adviser.to_string()),
                    Term::Sym(student.to_string()),
                ],
            })
            .collect();

        let mut kb = KnowledgeBase {
            atoms: adviser_facts.clone(),
        };

        let rule = Rule {
            head: Atom {
                pred_sym: "onlyAdvisor".to_string(),
                terms: vec![Term::Var("X".to_string())],
            },
            body: vec![Atom {
                pred_sym: "adviser".to_string(),
                terms: vec![Term::Var("X".to_string()), Term::Var("Y".to_string())],
            }],
        };

        rule.eval(&mut kb);
        assert_eq!(
            KnowledgeBase {
                atoms: advisers
                    .iter()
                    .map(|(adviser, _)| Atom {
                        pred_sym: "onlyAdvisor".to_string(),
                        terms: vec![Term::Sym(adviser.to_string()),],
                    })
                    .chain(adviser_facts.into_iter())
                    .collect(),
            },
            kb
        );
    }

    #[test]
    #[should_panic = "all rules must be range-restricted"]
    fn rules_are_range_restricted() {
        let program: Program<String, String> = Program {
            rules: vec![Rule {
                head: Atom {
                    pred_sym: "rangeUnrestricted".to_string(),
                    terms: vec![Term::Var("X".to_string())],
                },
                body: vec![Atom {
                    pred_sym: "rangeUnrestricted".to_string(),
                    terms: vec![Term::Var("Y".to_string())],
                }],
            }],
        };

        let _ = program.solve();
    }

    #[test]
    fn parses_datalog() {
        let program_text = include_str!("../example.datalog");
        let advisers = [
            ("Andrew Rice", "Mistral Contrastin"),
            ("Andy Hopper", "Andrew Rice"),
            ("Alan Mycroft", "Dominic Orchard"),
            ("David Wheeler", "Andy Hopper"),
            ("Rod Burstall", "Alan Mycroft"),
            ("Robin Milner", "Alan Mycroft"),
        ];

        let mut rules: Vec<_> = advisers
            .iter()
            .map(|(adviser, student)| rule!(atom!("adviser", symbol!(adviser), symbol!(student))))
            .collect();

        rules.extend(vec![
            rule!(atom!("academicAncestor", var!("X"), var!("Y")) =>
                atom!("adviser", var!("X"), var!("Y"))),
            rule!(atom!("academicAncestor", var!("X"), var!("Z")) =>
                atom!("adviser", var!("X"), var!("Y")),
                atom!("academicAncestor", var!("Y"), var!("Z"))),
        ]);

        let program = Program { rules };

        assert_eq!(parse(program_text).unwrap().1, program)
    }

    #[test]
    fn test_cyclic_rules() {
        let program = Program {
            rules: vec![
                rule!(atom!("cycle", var!("X"), var!("Y")) =>
                atom!("cycle", var!("Y"), var!("X"))),
                rule!(atom!("cycle", symbol!("a"), symbol!("b"))),
            ],
        };

        let result = program.solve();

        let expected = KnowledgeBase {
            atoms: vec![
                atom!("cycle", symbol!("a"), symbol!("b")),
                atom!("cycle", symbol!("b"), symbol!("a")),
            ]
            .into_iter()
            .collect(),
        };

        assert_eq!(result, expected);
    }

    #[test]
    fn test_empty_program() {
        let result = Program::<String, String> { rules: vec![] }.solve();
        assert_eq!(result, KnowledgeBase::<String, String>::default());
    }

    #[test]
    fn test_multiple_var_occurrences() {
        let program = Program {
            rules: vec![
                rule!(atom!("same", symbol!("a"), symbol!("a"))),
                rule!(atom!("same", symbol!("b"), symbol!("b"))),
                // Rule: reflexive(X, X) :- same(X, X)
                rule!(atom!("reflexive", var!("X"), var!("X")) =>
                atom!("same", var!("X"), var!("X"))),
            ],
        };

        let result = program.solve();

        let expected_atoms = vec![
            atom!("same", symbol!("a"), symbol!("a")),
            atom!("same", symbol!("b"), symbol!("b")),
            atom!("reflexive", symbol!("a"), symbol!("a")),
            atom!("reflexive", symbol!("b"), symbol!("b")),
        ]
        .into_iter()
        .collect();

        assert_eq!(result.atoms, expected_atoms);
    }

    // Using enums for compact representation
    #[derive(Clone, Debug, Eq, PartialEq, Hash)]
    enum Predicate {
        Parent,
        Ancestor,
    }

    #[derive(Clone, Debug, Eq, PartialEq, Hash)]
    enum Person {
        Alice,
        Bob,
        Carol,
        David,
    }

    #[test]
    fn test_enum_types() {
        let rules = vec![
            // Parent facts
            rule!(Atom {
                pred_sym: Predicate::Parent,
                terms: vec![Term::Sym(Person::Alice), Term::Sym(Person::Bob)]
            }),
            rule!(Atom {
                pred_sym: Predicate::Parent,
                terms: vec![Term::Sym(Person::Bob), Term::Sym(Person::Carol)]
            }),
            // Ancestor rules
            Rule {
                head: Atom {
                    pred_sym: Predicate::Ancestor,
                    terms: vec![Term::Var(Person::David), Term::Var(Person::Alice)],
                },
                body: vec![Atom {
                    pred_sym: Predicate::Parent,
                    terms: vec![Term::Var(Person::David), Term::Var(Person::Alice)],
                }],
            },
        ];

        let result = Program { rules }.solve();

        // Check if original parent relationships are preserved
        assert!(result.atoms.contains(&Atom {
            pred_sym: Predicate::Parent,
            terms: vec![Term::Sym(Person::Alice), Term::Sym(Person::Bob)]
        }));
    }

    // Using integers for compact representation
    #[test]
    fn test_integer_types() {
        // Using u32 for both predicates and terms
        let rules = vec![
            // Facts: edge(1,2), edge(2,3)
            rule!(Atom {
                pred_sym: 1u32,
                terms: vec![Term::Sym(1u32), Term::Sym(2u32)]
            }),
            rule!(Atom {
                pred_sym: 1u32,
                terms: vec![Term::Sym(2u32), Term::Sym(3u32)]
            }),
            // Rule: path(X,Y) :- edge(X,Y)
            Rule {
                head: Atom {
                    pred_sym: 2u32, // path
                    terms: vec![Term::Var(0u32), Term::Var(1u32)],
                },
                body: vec![Atom {
                    pred_sym: 1u32, // edge
                    terms: vec![Term::Var(0u32), Term::Var(1u32)],
                }],
            },
        ];

        let result = Program { rules }.solve();

        // Check if paths were derived
        assert!(result.atoms.contains(&Atom {
            pred_sym: 2u32,
            terms: vec![Term::Sym(1u32), Term::Sym(2u32)]
        }));
        assert!(result.atoms.contains(&Atom {
            pred_sym: 2u32,
            terms: vec![Term::Sym(2u32), Term::Sym(3u32)]
        }));
    }

    // Test mixing different sized types
    #[test]
    fn test_mixed_sizes() {
        let rules = vec![
            // Using u8 for predicate and u32 for terms
            rule!(Atom {
                pred_sym: 1u8,
                terms: vec![Term::Sym(1000u32), Term::Sym(2000u32)]
            }),
            Rule {
                head: Atom {
                    pred_sym: 2u8,
                    terms: vec![Term::Var(0u32), Term::Var(1u32)],
                },
                body: vec![Atom {
                    pred_sym: 1u8,
                    terms: vec![Term::Var(0u32), Term::Var(1u32)],
                }],
            },
        ];

        let result = Program { rules }.solve();

        assert!(result.atoms.contains(&Atom {
            pred_sym: 2u8,
            terms: vec![Term::Sym(1000u32), Term::Sym(2000u32)]
        }));
    }
}
