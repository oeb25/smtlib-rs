use color_eyre::Result;
use itertools::Itertools;
use quote::{format_ident, quote};
use xshell::Shell;

struct Logic {
    name: String,
    language: String,
}

fn logics(sh: &Shell) -> Result<Vec<Logic>> {
    sh.read_dir("./smtlib/src/logics")?
        .into_iter()
        .filter(|p| p.extension().is_some_and(|c| c == "smt2"))
        .map(|p| {
            let s = sh.read_file(p)?;

            let (_, rest) = s.split_once("(logic").unwrap();
            let (name, rest) = rest
                .trim_start()
                .split_once(|c: char| c.is_whitespace())
                .unwrap();
            let (_, rest) = rest.split_once(":language").unwrap();
            let language = rest.split('"').nth(1).unwrap();

            Ok(Logic {
                name: name.to_string(),
                language: language.to_string(),
            })
        })
        .collect()
}

pub fn generate(sh: &Shell) -> Result<String> {
    let logics = logics(sh)?;

    let (name, name_str, language): (Vec<_>, Vec<_>, Vec<_>) = logics
        .iter()
        .map(|Logic { name, language }| (format_ident!("{name}"), name, language))
        .multiunzip();

    let output = quote! {
        /// Logics allow specifictation of which (sub-)logic should be used by a
        /// solver.
        ///
        /// > [A more detailed description of logics can be found on the
        /// SMT-LIB website.](https://smtlib.cs.uiowa.edu/logics.shtml)
        ///
        /// ![This is a graph :)](https://smtlib.cs.uiowa.edu/Logics/logics.png)
        #[allow(nonstandard_style)]
        pub enum Logic {
            #(
                #[doc = #language]
                #name,
            )*
            /// A fallback variant in case the user wants to specify
            /// some logic which is not part of the predefined
            /// collection.
            Custom(String),
        }

        impl std::fmt::Display for Logic {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                match self {
                    #(
                        Self::#name => #name_str,
                    )*
                    Self::Custom(s) => s.as_str(),
                }.fmt(f)
            }
        }
    };

    Ok(prettyplease::unparse(&syn::parse2(output)?))
}
