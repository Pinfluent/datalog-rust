extern crate alloc;

use core::fmt::{Display, Formatter};
use core::ops::{Deref, DerefMut};
use hashbrown::HashSet;

mod parsing;

pub use parsing::parse;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Rule {
    pub head: Atom,
    pub body: Vec<Atom>,
}

#[macro_export]
macro_rules! rule {
    ($head:expr => $($body:expr),+) => {
        Rule {
            head: $head,
            body: vec![$($body),+],
        }
    };
    ($head:expr) => {
        Rule {
            head: $head,
            body: vec![],
        }
    }
}

impl Rule {
    fn is_range_restricted(&self) -> bool {
        let body_vars: HashSet<Term> = self
            .body
            .iter()
            .flat_map(|atom| atom.terms.clone())
            .filter(|term| matches!(term, Term::Var(_)))
            .collect();

        let head_vars: HashSet<Term> = self
            .head
            .terms
            .iter()
            .filter(|term| matches!(term, Term::Var(_)))
            .cloned()
            .collect();

        head_vars.is_subset(&body_vars)
    }
}

impl Display for Rule {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.head)?;
        // Write the body
        if !self.body.is_empty() {
            writeln!(f, " :-")?;
            let last_atom_position = self.body.len() - 1;
            for (position, atom) in self.body.iter().enumerate() {
                write!(f, "  {}", atom)?;
                if position != last_atom_position {
                    writeln!(f, ",")?;
                }
            }
        }
        writeln!(f, ".")
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Atom {
    pub pred_sym: String,
    pub terms: Vec<Term>,
}

#[macro_export]
macro_rules! atom {
    ($pred_sym:expr, $($term:expr),*) => {
        Atom {
            pred_sym: $pred_sym.to_string(),
            terms: vec![$($term),*]
        }
    };
}

impl Display for Atom {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.pred_sym)?;
        if !self.terms.is_empty() {
            write!(f, "(")?;
            for (position, term) in self.terms.iter().enumerate() {
                if position != 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{term}")?;
            }
            write!(f, ")")?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Term {
    Var(String),
    Sym(String),
}

#[macro_export]
macro_rules! var {
    ($name:expr) => {
        Term::Var($name.to_string())
    };
}

#[macro_export]
macro_rules! symbol {
    ($name:expr) => {
        Term::Sym($name.to_string())
    };
}

impl Display for Term {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Var(v) => write!(f, "{v}"),
            Term::Sym(s) => write!(f, "{s:?}"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Program(pub Vec<Rule>);

impl Display for Program {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for rule in &self.0 {
            write!(f, "{}", rule)?;
        }
        Ok(())
    }
}

impl Deref for Program {
    type Target = Vec<Rule>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct KnowledgeBase(pub HashSet<Atom>);

impl Deref for KnowledgeBase {
    type Target = HashSet<Atom>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Substitution(pub Vec<(Term, Term)>);
impl Substitution {
    pub fn lookup(&self, key: &Term) -> Option<&Term> {
        self.0.iter().find_map(|(k, v)| (k == key).then_some(v))
    }
}

impl Deref for Substitution {
    type Target = Vec<(Term, Term)>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Substitution {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

pub fn solve(program: &Program) -> KnowledgeBase {
    // NOTE: We need to check range restriction
    assert_eq!(
        <Vec<Rule>>::new(),
        program
            .0
            .iter()
            .filter(|rule| !rule.is_range_restricted())
            .cloned()
            .collect::<Vec<_>>(),
        "all rules must be range-restricted"
    );
    let mut kb = KnowledgeBase::default();
    while let Some(new_kb) = immediate_consequence(program, &kb) {
        kb = new_kb
    }
    kb
}

pub fn immediate_consequence(program: &Program, kb: &KnowledgeBase) -> Option<KnowledgeBase> {
    let mut new_knowledge = vec![];
    for atom in program.iter().flat_map(|rule| eval_rule(kb, rule).0) {
        if !kb.contains(&atom) {
            new_knowledge.push(atom);
        }
    }
    if new_knowledge.is_empty() {
        None
    } else {
        Some(KnowledgeBase(
            kb.iter().chain(new_knowledge.iter()).cloned().collect(),
        ))
    }
}

pub fn eval_rule(kb: &KnowledgeBase, rule: &Rule) -> KnowledgeBase {
    KnowledgeBase(
        walk(kb, &rule.body)
            .iter()
            .map(|subs| substitute(&rule.head, subs))
            .collect(),
    )
}

pub fn walk(kb: &KnowledgeBase, atoms: &[Atom]) -> Vec<Substitution> {
    atoms
        .iter()
        .fold(vec![Substitution::default()], |all_subs, atom| {
            eval_atom(kb, atom, &all_subs)
        })
}

pub fn eval_atom(kb: &KnowledgeBase, atom: &Atom, all_subs: &[Substitution]) -> Vec<Substitution> {
    let mut new_subs = vec![];
    for substitution in all_subs {
        let down_to_earth_atom = substitute(atom, substitution);
        for entry in kb.iter() {
            if let Some(extension) = unify(&down_to_earth_atom, entry) {
                new_subs.push(Substitution(
                    substitution
                        .iter()
                        .cloned()
                        .chain(extension.0.into_iter())
                        .collect(),
                ));
            }
        }
    }
    new_subs
}

pub fn unify(a: &Atom, b: &Atom) -> Option<Substitution> {
    if a.pred_sym != b.pred_sym || a.terms.len() != b.terms.len() {
        return None;
    }
    let mut subs = Substitution::default();
    for pair in a.terms.iter().zip(b.terms.iter()) {
        match pair {
            (_, Term::Var(_)) => panic!("The second atom is assumed to be ground"),
            (v @ Term::Var(_), s @ Term::Sym(_)) => match subs.lookup(v) {
                Some(s2 @ Term::Sym(_)) if s2 != s => {
                    return None;
                }
                _ => subs.push((v.clone(), s.clone())),
            },
            (s1 @ Term::Sym(_), s2 @ Term::Sym(_)) if s1 != s2 => {
                return None;
            }
            _ => {}
        }
    }
    Some(subs)
}

pub fn substitute(atom: &Atom, substitution: &Substitution) -> Atom {
    let mut atom = atom.clone();
    let terms = atom
        .terms
        .iter()
        .map(|term| match term {
            v @ Term::Var(_) => substitution.lookup(v).cloned().unwrap_or_else(|| v.clone()),
            Term::Sym(_) => term.clone(),
        })
        .collect();
    atom.terms = terms;
    atom
}

#[cfg(test)]
mod tests {
    use super::*;

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

        let program = Program(rules);
        let result = solve(&program);

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

        let expected = KnowledgeBase(expected_atoms);

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

        let program = Program(rules);
        let result = solve(&program);

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

        let expected = KnowledgeBase(expected_atoms);

        assert_eq!(result, expected);
    }

    #[test]
    fn test_substitute() {
        let atom = Atom {
            pred_sym: "academicAncestor".to_string(),
            terms: vec![Term::Var("X".to_string()), Term::Var("Z".to_string())],
        };
        let subs = Substitution(vec![(
            Term::Var("X".to_string()),
            Term::Sym("Quinn".to_string()),
        )]);
        assert_eq!(
            Atom {
                pred_sym: "academicAncestor".to_string(),
                terms: vec![Term::Sym("Quinn".to_string()), Term::Var("Z".to_string())],
            },
            substitute(&atom, &subs)
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
            Some(Substitution(vec![
                (Term::Var("X".to_string()), Term::Sym("Alice".to_string())),
                (Term::Var("Y".to_string()), Term::Sym("Bob".to_string()))
            ])),
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

        let kb = KnowledgeBase(
            advisers
                .iter()
                .map(|(adviser, student)| Atom {
                    pred_sym: "adviser".to_string(),
                    terms: vec![
                        Term::Sym(adviser.to_string()),
                        Term::Sym(student.to_string()),
                    ],
                })
                .collect(),
        );

        let atom = Atom {
            pred_sym: "adviser".to_string(),
            terms: vec![Term::Var("X".to_string()), Term::Var("Y".to_string())],
        };

        let all_subs = vec![
            Substitution(vec![(
                Term::Var("X".to_string()),
                Term::Sym("David Wheeler".to_string()),
            )]),
            Substitution(vec![(
                Term::Var("Y".to_string()),
                Term::Sym("Alan Mycroft".to_string()),
            )]),
        ];

        assert_eq!(
            vec![
                Substitution(vec![
                    (
                        Term::Var("X".to_string()),
                        Term::Sym("David Wheeler".to_string()),
                    ),
                    (
                        Term::Var("Y".to_string()),
                        Term::Sym("Andy Hopper".to_string()),
                    ),
                ],),
                Substitution(vec![
                    (
                        Term::Var("Y".to_string(),),
                        Term::Sym("Alan Mycroft".to_string(),),
                    ),
                    (
                        Term::Var("X".to_string(),),
                        Term::Sym("Rod Burstall".to_string(),),
                    ),
                ],),
                Substitution(vec![
                    (
                        Term::Var("Y".to_string(),),
                        Term::Sym("Alan Mycroft".to_string(),),
                    ),
                    (
                        Term::Var("X".to_string(),),
                        Term::Sym("Robin Milner".to_string(),),
                    ),
                ],),
            ],
            eval_atom(&kb, &atom, &all_subs)
        )
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

        let kb = KnowledgeBase(
            advisers
                .iter()
                .map(|(adviser, student)| Atom {
                    pred_sym: "adviser".to_string(),
                    terms: vec![
                        Term::Sym(adviser.to_string()),
                        Term::Sym(student.to_string()),
                    ],
                })
                .collect(),
        );

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

        assert_eq!(
            KnowledgeBase(
                advisers
                    .iter()
                    .map(|(adviser, _)| Atom {
                        pred_sym: "onlyAdvisor".to_string(),
                        terms: vec![Term::Sym(adviser.to_string()),],
                    })
                    .collect(),
            ),
            eval_rule(&kb, &rule)
        );
    }

    #[test]
    fn display_impls() {
        // Terms
        assert_eq!("Var", &format!("{}", Term::Var("Var".to_string())));
        assert_eq!(
            "\"A string\"",
            &format!("{}", Term::Sym("A string".to_string()))
        );

        // Atoms
        assert_eq!(
            "is_true",
            &format!(
                "{}",
                Atom {
                    pred_sym: "is_true".to_string(),
                    terms: vec![]
                }
            )
        );
        assert_eq!(
            "singleton(V)",
            &format!(
                "{}",
                Atom {
                    pred_sym: "singleton".to_string(),
                    terms: vec![Term::Var("V".to_string())]
                }
            )
        );
        assert_eq!(
            "adviser(\"Andrew Rice\", \"Mistral Contrastin\")",
            &format!(
                "{}",
                Atom {
                    pred_sym: "adviser".to_string(),
                    terms: vec![
                        Term::Sym("Andrew Rice".to_string()),
                        Term::Sym("Mistral Contrastin".to_string()),
                    ],
                }
            )
        );

        // academicAncestor(X,Y) :-
        //   adviser(X,Y).
        assert_eq!(
            "academicAncestor(X, Y) :-\n  adviser(X, Y).\n",
            &format!(
                "{}",
                Rule {
                    head: Atom {
                        pred_sym: "academicAncestor".to_string(),
                        terms: vec![Term::Var("X".to_string()), Term::Var("Y".to_string())],
                    },
                    body: vec![Atom {
                        pred_sym: "adviser".to_string(),
                        terms: vec![Term::Var("X".to_string()), Term::Var("Y".to_string())],
                    }],
                }
            )
        );
        // academicAncestor(X,Z) :-
        //   adviser(X,Y),
        //   academicAncestor(Y,Z).
        assert_eq!(
            "academicAncestor(X, Z) :-\n  adviser(X, Y),\n  academicAncestor(Y, Z).\n",
            &format!(
                "{}",
                Rule {
                    head: Atom {
                        pred_sym: "academicAncestor".to_string(),
                        terms: vec![Term::Var("X".to_string()), Term::Var("Z".to_string())],
                    },
                    body: vec![
                        Atom {
                            pred_sym: "adviser".to_string(),
                            terms: vec![Term::Var("X".to_string()), Term::Var("Y".to_string())],
                        },
                        Atom {
                            pred_sym: "academicAncestor".to_string(),
                            terms: vec![Term::Var("Y".to_string()), Term::Var("Z".to_string())],
                        },
                    ],
                }
            )
        );

        assert_eq!(
            "academicAncestor(X, Y) :-\n  adviser(X, Y).\nacademicAncestor(X, Z) :-\n  adviser(X, Y),\n  academicAncestor(Y, Z).\n",
            &format!(
                "{}",
                Program(vec![
                    Rule {
                        head: Atom {
                            pred_sym: "academicAncestor".to_string(),
                            terms: vec![Term::Var("X".to_string()), Term::Var("Y".to_string())],
                        },
                        body: vec![Atom {
                            pred_sym: "adviser".to_string(),
                            terms: vec![Term::Var("X".to_string()), Term::Var("Y".to_string())],
                        }],
                    },
                    Rule {
                        head: Atom {
                            pred_sym: "academicAncestor".to_string(),
                            terms: vec![Term::Var("X".to_string()), Term::Var("Z".to_string())],
                        },
                        body: vec![
                            Atom {
                                pred_sym: "adviser".to_string(),
                                terms: vec![Term::Var("X".to_string()), Term::Var("Y".to_string())],
                            },
                            Atom {
                                pred_sym: "academicAncestor".to_string(),
                                terms: vec![Term::Var("Y".to_string()), Term::Var("Z".to_string())],
                            },
                        ],
                    },
                ])
            )
        );
    }

    #[test]
    #[should_panic = "all rules must be range-restricted"]
    fn rules_are_range_restricted() {
        let program: Program = Program(vec![Rule {
            head: Atom {
                pred_sym: "rangeUnrestricted".to_string(),
                terms: vec![Term::Var("X".to_string())],
            },
            body: vec![Atom {
                pred_sym: "rangeUnrestricted".to_string(),
                terms: vec![Term::Var("Y".to_string())],
            }],
        }]);

        let _ = solve(&program);
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

        let program = Program(rules);

        assert_eq!(parse(program_text).unwrap().1, program)
    }

    #[test]
    fn test_cyclic_rules() {
        let program = Program(vec![
            rule!(atom!("cycle", var!("X"), var!("Y")) =>
                atom!("cycle", var!("Y"), var!("X"))),
            rule!(atom!("cycle", symbol!("a"), symbol!("b"))),
        ]);

        let result = solve(&program);

        let expected = KnowledgeBase(
            vec![
                atom!("cycle", symbol!("a"), symbol!("b")),
                atom!("cycle", symbol!("b"), symbol!("a")),
            ]
            .into_iter()
            .collect(),
        );

        assert_eq!(result, expected);
    }

    #[test]
    fn test_empty_program() {
        let program = Program(vec![]);
        let result = solve(&program);
        assert_eq!(result, KnowledgeBase::default());
    }

    #[test]
    fn test_multiple_var_occurrences() {
        let program = Program(vec![
            rule!(atom!("same", symbol!("a"), symbol!("a"))),
            rule!(atom!("same", symbol!("b"), symbol!("b"))),
            // Rule: reflexive(X, X) :- same(X, X)
            rule!(atom!("reflexive", var!("X"), var!("X")) =>
                atom!("same", var!("X"), var!("X"))),
        ]);

        let result = solve(&program);

        let expected_atoms = vec![
            atom!("same", symbol!("a"), symbol!("a")),
            atom!("same", symbol!("b"), symbol!("b")),
            atom!("reflexive", symbol!("a"), symbol!("a")),
            atom!("reflexive", symbol!("b"), symbol!("b")),
        ]
        .into_iter()
        .collect();

        assert_eq!(result.0, expected_atoms);
    }
}
