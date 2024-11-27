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
    pub fn eval(&self, kb: &mut KnowledgeBase) -> bool {
        let substitutions = self
            .body
            .iter()
            .fold(vec![Substitution::default()], |all_subs, atom| {
                eval_atom(kb, atom, &all_subs)
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

/// None means contradiction. Some means that we've found valid substitutions.
pub fn unify(a: &Atom, b: &Atom) -> Option<Substitution> {
    if a.pred_sym != b.pred_sym || a.terms.len() != b.terms.len() {
        return None;
    }

    let mut subs = Substitution::default();
    for (a_term, b_term) in a.terms.iter().zip(b.terms.iter()) {
        if matches!(b_term, Term::Var(_)) {
            panic!("The second atom is assumed to be ground")
        }

        match a_term {
            &Term::Var(_) => {
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
            &Term::Sym(_) if a_term != b_term => {
                return None;
            }
            _ => {}
        }
    }

    Some(subs)
}
