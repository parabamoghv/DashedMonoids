# Dashed Monoids and Categorical Groups Formalization in Lean4

Welcome! This repository contains a Lean4 formalization of concepts from my thesis on the Symmetrization of Categorical Groups, focusing on the categorical analogue of group abelianization. The project is designed to be accessible to both mathematicians and computer scientists interested in formal methods.

For questions or feedback, feel free to reach out at _parab.7@osu.edu_.

---

## Project Overview

### 1. Dashed Monoids: A New Algebraic Structure

This project introduces **dashed monoids** (`DMon S`), a generalization of free monoids (lists) over a set `S`. While standard lists are widely used in computer science for their associative concatenation property, dashed monoids extend this idea by allowing elements to have multiple levels of "dashing" (nesting).

**Examples of dashed lists:**
```
(a, ((b, c)', d'')')
(a', b'', c)''
(a, b, c, d)    -- a plain list without dashes
```
Regular lists are simply dashed lists with no dashes.

Dashed lists preserve associative concatenation and introduce a dash operation. The Lean4 formalization defines dashed lists as an inductive type with five constructors:
1. Empty list
2. Inclusion of an element from `S`
3. Inclusion of multiplication of two or more elements from `S`
4. Inclusion of dashing of an element from `S`
5. Inclusion of dashing of elements from constructors 3 and 6 
6. Inclusion of multiplication of two or more elements from constructors 4 and 5 

You can find the formal construction in `Dashed_Lists\as_inductive.lean`. This file begins with an introduction to the algebraic structure of dashed monoids and provides several examples. In the section `FDMon.Definition`, we formally define Dashed Lists with the name `FDMon`. Section `FDMon_is_FreeDMon` demonstrates that this construction satisfies the desired universal property. For the underlying mathematics, refer to `DashedMonoids.pdf`. The use of five constructors for dashed lists is inspired by the definition of the dashed monoid basis (Definition 3.2.6); the mathematical development in the document and the Lean code closely correspond.
---

See [Appendix A](#appendix-a-what-is-lean4) for a quick introduction to Lean4.


2. ### Formalizing Semi-Strict and Strict Categorical Groups

The second part of this project delves into categorical algebra. Specifically, it involves:

Defining semi-strict categorical groups and strict categorical groups in Lean4 and proving their categorical equivalence. This is a work in progress, more details will follow.

<!-- This work extends foundational concepts in category theory and provides a formal framework that connects theoretical results to computational verification.
Why This Matters -->

<!-- Formalizing mathematics ensures that proofs and constructions are rigorous, eliminating human errors in reasoning. This is particularly important in highly abstract fields like category theory, where intuition alone is often insufficient. By contributing to the formalization of advanced mathematical concepts, this project bridges the gap between abstract theory and computational implementation. You can find the related code in stCatGrp directory. -->



## Appendix A: What is Lean4

Lean is a *dependent-typed programming language and proof assistant*. It’s designed for writing mathematical proofs and formally verifying them with the help of type theory. Think of it as a tool where programming meets logic and mathematics.

If you’re familiar with languages like Python, Java, or C++, Lean might feel different because:

1. It’s rooted in Type Theory, not object-oriented. In Lean, a type can represent a mathematical proposition, and its elements are proofs of that proposition. 
2. The focus is on correctness and proof rather than just running code. Writing a function in Lean often corresponds to proving something.


### Reading Lean Code

Lean code has a declarative style, often involving theorems, definitions, and tactics:

*Definitions* (def): Define functions or values, like in most programming languages.
*Theorems/Propositions* (theorem or lemma): Statements you want to prove.
*Tactics* : Step-by-step tools to guide Lean in constructing a proof.


### Example 

The main result we want to prove is as follows: The dashed lists that we constructed is indeed the data structure we wish to create. *FDMon S* is the name given to dashed lists and the properties that we want it to satisfy are stored at FreeDMon. Thus, we have following theorem.

    theorem FDMon_is_FreeDMon {S:Type _}:FreeDMon (incS:(S→ FDMon S)):= by
    constructor
    case exist=>
        intro N stN f
        use FDMon.induce f
        ---

    case unique=>
        intro N stN f g hf hg hyp
        ext x
        apply induce_unique f g hf hg
        intro a
        rw[← @Function.comp_apply (FDMon S) N S f incS a]
        rw[hyp]
        simp only [Function.comp_apply]


In above, everything after `by` is the proof of the theorem. `Constructor` divides the proof into two cases: Exists and Unique. We use tactics given to us and developed over the course to prove these cases. If Lean does not give any error message then it means that the proof is correct.
