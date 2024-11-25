#![no_std]

extern crate alloc;

use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
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
    /// Rule is range restricted when [Rule::head] contains only vars that're also present in [Rule::body].
    fn is_range_restricted(&self) -> bool {
        let body_vars: HashSet<Term> = self
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Program {
    rules: Vec<Rule>,
}

impl Program {
    pub fn solve(&self) -> KnowledgeBase {
        // NOTE: We need to check range restriction
        assert!(
            self.rules.iter().all(Rule::is_range_restricted),
            "all rules must be range-restricted"
        );

        let mut kb = KnowledgeBase::default();
        while self.immediate_consequence(&mut kb) {}
        kb
    }

    /// Returns `true` if `kb' have changed.
    fn immediate_consequence(&self, kb: &mut KnowledgeBase) -> bool {
        let mut new_knowledge = vec![];
        for atom in self.rules.iter().flat_map(|rule| eval_rule(kb, rule).atoms) {
            if !kb.atoms.contains(&atom) {
                new_knowledge.push(atom);
            }
        }

        if !new_knowledge.is_empty() {
            for new_atom in new_knowledge {
                kb.atoms.insert(new_atom);
            }

            true
        } else {
            false
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct KnowledgeBase {
    pub atoms: HashSet<Atom>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Substitution(pub Vec<(Term, Term)>);

impl Substitution {
    pub fn lookup(&self, key: &Term) -> Option<&Term> {
        self.0.iter().find_map(|(k, v)| (k == key).then_some(v))
    }

    fn apply(&self, atom: &Atom) -> Atom {
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

fn eval_rule(kb: &KnowledgeBase, rule: &Rule) -> KnowledgeBase {
    KnowledgeBase {
        atoms: walk(kb, &rule.body)
            .iter()
            .map(|subs| subs.apply(&rule.head))
            .collect(),
    }
}

fn walk(kb: &KnowledgeBase, atoms: &[Atom]) -> Vec<Substitution> {
    atoms
        .iter()
        .fold(vec![Substitution::default()], |all_subs, atom| {
            eval_atom(kb, atom, &all_subs)
        })
}

fn eval_atom(kb: &KnowledgeBase, atom: &Atom, all_subs: &[Substitution]) -> Vec<Substitution> {
    let mut new_subs = vec![];
    for substitution in all_subs {
        let down_to_earth_atom = substitution.apply(atom);
        for entry in kb.atoms.iter() {
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

fn unify(a: &Atom, b: &Atom) -> Option<Substitution> {
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

#[cfg(test)]
mod tests {
    use alloc::string::ToString as _;

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
        let subs = Substitution(vec![(
            Term::Var("X".to_string()),
            Term::Sym("Quinn".to_string()),
        )]);
        assert_eq!(
            Atom {
                pred_sym: "academicAncestor".to_string(),
                terms: vec![Term::Sym("Quinn".to_string()), Term::Var("Z".to_string())],
            },
            subs.apply(&atom)
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
            KnowledgeBase {
                atoms: advisers
                    .iter()
                    .map(|(adviser, _)| Atom {
                        pred_sym: "onlyAdvisor".to_string(),
                        terms: vec![Term::Sym(adviser.to_string()),],
                    })
                    .collect(),
            },
            eval_rule(&kb, &rule)
        );
    }

    #[test]
    #[should_panic = "all rules must be range-restricted"]
    fn rules_are_range_restricted() {
        let program: Program = Program {
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
        let result = Program { rules: vec![] }.solve();
        assert_eq!(result, KnowledgeBase::default());
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
}
