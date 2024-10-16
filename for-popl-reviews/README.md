# Agda Formalization

## Claims

The core contribution of our paper is the definition of a denotational model for
gradual typing using guarded type theory. There are two parts to this: First,
there is the model itself, which is formalized in the `Semantics` directory of
the library. The second part is the adequacy of the model, which states that the
semantics we developed behaves as we expect. While the formalization of these
results takes place across many files; the culmination of the work is distilled
in the file `Results.agda` in the root level of the library. Checking this file
will be sufficient to verifying the claims we make in the paper, modulo the
incomplete parts we list at the bottom of this document.

## Detailed Layout

The top-level `artifact` directory consists of this README file as well as the
`code` directory containing the Agda library.

The organization of the library in the `code` directory is as follows:

* `Common/` - Code used throughout the development, including guarded type theory primitives and lemmas

* `Cubical/` - Code used to support parts of the development, extending the Cubical standard library

* `Syntax/` - Code that formalizes the types, terms, type precision, and term precision for
    the gradually-typed lambda calculus discussed in Section 2 of the paper.

* `Semantics/` - The core of the development, this directory contains the
formalization of the denotational model of gradual typing as discussed in
Section 5 of the paper.

* `Results.agda` - A high-level summary of the main results of our development.

Within `Semantics/`, the layout is as follows:

* `Semantics/Concrete/` - The code defining the concrete denotational model:

  * `Predomain/` - Defines the predomain/error domain model, which corresponds
      to Section 5.1 of the paper. This includes the definitions of predomains
      and error domains, morphisms, relations, and squares, the guarded lift +
      error monad, as well as definitions of the functors `U`, `F`, `→`, and
      `×`.
  
  * `Perturbation/Semantic.agda` - Defines the notion of *semantic perturbation*
    of a predomain/error domain (an endomorphism bisimilar to the identity),
    and constructions on semantic perturbations.

  * `Types/` - Defines our notion of *value type* (resp. *computation type*),
    which are predomains (resp. error domains) equipped with a monoid of
    syntactic perturbations and an interpretation of those as semantic
    perturbations.
  
  * `Perturbation/Relation/` - Defines the notion of *push-pull* for
    predomain/error domain relations with respect to a value/computation type
    (corresponding to Definition 5.9 in the paper).

  * `Perturbation/QuasiRepresentation/` - Defines the notion of
    *quasi-representability* for predomain and error domain relations, and
    proves lemmas about quasi-representable relations.

  * `Relations/` - Defines our final notion of *value relation* and *computation
    relation* as predomain/error domain relations that are quasi-representable
    and satisfy push-pull. This corresponds to Definition 5.10 in the paper.

  * `Dyn/` - Defines the interpretation of the dynamic type using a combination
    of induction and guarded recursion, and defines the value relations `injNat`
    `InjTimes` and `InjArr`.

* `Semantics/Adequacy/` - Defines the big-step term semantics (corresponding to
   Section 3.5 in the paper) as a function from closed terms of type `nat` to
   *partial elements* of type ℕ + 1. Then extends this to a big-step relational semantics
   Also formalizes the adequacy of our relational
   semantics with respect to the graduality ordering.

* `Semantics/GuardedResults/` - Contains proofs of results concerning the
   guarded lift monad `L℧ X`, including the proof of the No-Go Theorem (Theorem
   4.1 in the paper).

## Instructions for Downloading

First, download and install the latest version of VirtualBox. If you are using
an M-series Mac computer, then it is especially important that your version of
VirtualBox is **at least 7.1**.

The subsequent steps will depend on whether you are running an M-series Mac, or
an X86-64 based machine. In the former case, please download the virtual machine
image marked "for M1/M2/M3 Macs". Otherwise, please download the virtual machine
image titled "for X86-64 Machines". The reason for needing two images is that
VirtualBox on M-series Macs does not work with an X86-based guest OS. Thus, the
version of the virtual machine for M-series Macs uses a version of Ubuntu for
the ARM architecture.

Once you've installed VirtualBox and downloaded the appropriate VM image, open
the VM in VirtualBox by double-clicking the `.vbox` file. **Warning** if you're
running the M-series Mac VM, for some reason it seems to take a while to boot up
(it can remain on the splash screen for upwards of 5 minutes).

Once you're at the login screen, use the following credentials:

* User: `reviewer`
* Password: `pass`

For the remaining steps, see the next section.

## Evaluating the Results

### Non-interactive

The provided virtual machine image has been preloaded with Agda, the Cubical
Agda library, and our library. To check our results in a non-interactive
fashion, simply open a terminal and navigate to the top-level directory of the
development:

    cd /home/reviewer/artifact/code/

Now run

    agda Results.agda

Depending on the specs of your machine, the type-checking process may take
around 10-15 minutes to complete. As Agda checks each of the files in the
development, it will output the name of the module it is checking, for example:

    Checking Semantics.Concrete.Types.Constructions

**Upon completion, there is no success message printed; you should simply be shown
the shell prompt.**

If type-checking fails, you will be notified of the module where the type error
occurred. However, the authors have tested the process and verified that it
completes successfully, so this should not occur.

Once Agda has type-checked a particular module, it caches the results, so subsequent
checks will be much faster.

**Note that the file `DynInstantiated.agda` takes quite a while to type-check, usually upwards of 5 minutes.**

### Interactive

For a more interactive experience, you can browse through the library in Emacs
and perform the type-checking there. We have installed Emacs and the Agda Emacs
mode on the virtual machine; you do not need to install anything additional.

Open Emacs, then navigate to the file you want to check:

* Type `Ctrl-x-f` (hold down the `Ctrl` key, press and hold `x`, and then
(while holding `Ctrl` and `x`) press `f`)

* Enter the path to the file and press `RET`

Now type-check the file by typing `Ctrl-c-l` (hold down the `Ctrl` key, press
and hold `c`, and then (while holding `Ctrl` and `c`) press `l`). This will
cause Agda to type-check the file, and **if successful, the bottom of the Emacs
window should say "\*All Done\*"**.

## Caveats

Our code uses features of Agda that make the development significantly more
straightforward but which circumvent some of the safety checks of Agda:

* **The code that defines the interpretation of the dynamic type uses the [`TERMINATING` PRAGMA][1]**:
  The definition of the dynamic type involves an inductive datatype in Agda. If
  we try to reuse our compositional constructions on value types as part of the
  defintion of the dynamic type, Agda's termination checker will complain
  because it cannot tell that those definitions are terminating. However, it is
  easy to see by manual inspection that our definitions do terminate. The
  warning raised by Agda is really a limitation of the termination checker.
  
  The pragma allows us to reuse constructions on value types instead of
  essentially inling those constructions in the setting of the dynamic type.

* **A few of our proofs use [rewrite rules][2]**: The code defining the big-step
  semantics implements *globalization* --- turning guarded definitions made in
  the context of a clock `k` into non-guarded definitions by universally
  quantifying over the clock `k`. This requires several lemmas about the
  behavior of clock quantification with respect to various type constructors.
  The proofs of these lemmas require certain basic facts about clock
  quantification. The current version of Guarded Cubical Agda does not have
  these built into the type-checker, so we must instead add them as axioms. Then
  to prove the lemmas, we have used rewrite rules to avoid extremely tedious
  equational reasoning involving axioms.

  This could be avoided if instead of using axioms, the relevant rules
  concerning clock quantification were incorporated as definitional equalities
  in the type-checker, based on the type theory introduced in [this paper][4].
  There has been [work][3] on this on an older version of Agda, but since we are
  using a more recent version of Agda, we instead to implement the relevant
  facts by declaring them as postulates.

[1]: <https://agda.readthedocs.io/en/v2.6.4.3/language/termination-checking.html#pragmas-and-options>
[2]: <https://agda.readthedocs.io/en/v2.6.4.3/language/rewriting.html>
[3]: <https://github.com/agda/guarded/tree/forcing-ticks>
[4]: <https://dl.acm.org/doi/abs/10.1145/3531130.3533359>

## Incomplete Aspects 🚧

The following results from the paper are not fully implemented in our library:

🚧 The proofs that the arrow and product functors preserve
   quasi-representability of relations (Lemmas D.15 and D.16 in the Appendix).
   This requires tedious reasoning about the *Kleisli actions* of the arrow and
   product functors.

   In particular, what remains to be shown is that the Kleisli actions of arrow
   and product are functorial, and that they preserve squares. These proofs are
   given in detail in Appendix B in the paper. The relevant holes corresponding
   to the proofs of these facts are located in the file
   `Semantics.Concrete.Predomain.Kleisli`.

   We must also formalize the fact that the Kleisli actions extend to actions on
   *syntactic perturbations*. This is sketched in Appendix D (see Defintiions
   D.6 and D.7). While the Agda development does define the Kleisli actions on
   syntactic perturbations, we do not currently prove that this assignment is
   coherent with respect to the Kleisli actions on *semantic* perturbations (see
   below Definition D.7 for the precise meaning of this.) The relevant holes
   corresponding to these facts are in the file
   `Semantics.Concrete.Perturbation.Kleisli` and
   `Semantics.Concrete.Perturbation.Semantic`.

   While we could in theory implement these proofs in the current version of the
   library, it would be much easier if we first made some other larger changes
   including potentially the use of the new [opacity][5] feature of Agda.

🚧 The verification in the semantic model of the rules corresponding to the
   equational rules for type precision given at the bottom of Figure 1 in the
   paper. This should be relatively straightforward, but will require us to
   state and prove several additional lemmas about *quasi-equivalence* of
   relations.

   Note that this is independent of the translation discussed in the below item
   --- what we are referring to here can be phrased as lemmas about the semantic
   model. Of course, completing the translation will require this as a
   prerequisite.

🚧 The syntax-to-semantics translation, i.e., mapping the terms to morphisms,
   the type-precision derivations to relations, and term-precision to squares.
   While this is in principle straightforward, we ran into prohibitive
   performance limitations around Agda's pattern matching on higher-inductive
   types. There may be ways around this, e.g., by defining an eliminator
   function that performs the slow pattern matching "once and for all" and then
   using that to define the translation. Investigating this further remains
   ongoing work.

[5]: <https://agda.readthedocs.io/en/v2.6.4.3/language/opaque-definitions.html>
