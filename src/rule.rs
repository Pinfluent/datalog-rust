use super::*;

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
    pub fn eval(&self, kb: &KnowledgeBase) -> KnowledgeBase {
        KnowledgeBase {
            atoms: self
                .walk(kb)
                .iter()
                .map(|subs| subs.apply_to_atom(&self.head))
                .collect(),
        }
    }

    fn walk(&self, kb: &KnowledgeBase) -> Vec<Substitution> {
        self.body
            .iter()
            .fold(vec![Substitution::default()], |all_subs, atom| {
                eval_atom(kb, atom, &all_subs)
            })
    }

    /// Rule is range restricted when [Rule::head] contains only vars that're also present in [Rule::body].
    pub fn is_range_restricted(&self) -> bool {
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

pub fn eval_atom(kb: &KnowledgeBase, atom: &Atom, all_subs: &[Substitution]) -> Vec<Substitution> {
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
                _ => {
                    subs.mapping.insert(v.clone(), s.clone());
                }
            },
            (s1 @ Term::Sym(_), s2 @ Term::Sym(_)) if s1 != s2 => {
                return None;
            }
            _ => {}
        }
    }
    Some(subs)
}
