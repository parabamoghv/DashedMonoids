# Formalizing Parts of My Thesis in Lean4

## Introduction

Mathematics is fundamentally about developing methods or algorithms to solve problems. But how can we be sure that these methods are foolproof? Wouldn't it be amazing if a computer could understand mathematical concepts and validate our solutions?

Lean4 is a programming language designed for formalizing mathematics, providing a robust environment to verify mathematical proofs and algorithms. It has an active community that contributes to an ever-growing mathematical library, making it a valuable tool for mathematicians and computer scientists. Have a look at Appendix A for a quick guide to Lean4.

This project aims to formalize parts of my thesis on the Symmetrization of Categorical Groups, which is the categorical equivalent of the Abelianization of a Group. While the thesis itself is highly technical, the aspects I wish to formalize are accessible and potentially interesting to both mathematics and computer science enthusiasts.

Contact me at _parab.7@osu.edu_ if you have any questions or comments.

---

## Project Overview

1. ### Designing a New Inductive Data Type : Dashed Monoids

The first part of this project is motivated by the familiar construction of the data structure List S, where the elements are derived from a set S. Lists are a cornerstone of computer science, valued for their simplicity and flexibility. One of their key properties is associative concatenation:
(L1+L2)+L3=L1+(L2+L3)
(L1​+L2​)+L3​=L1​+(L2​+L3​)

Here, we introduce a new data structure, denoted as DMon S (inspired by the term "free dashed monoid"). Elements of DMon S, called dashed lists, are nested lists where elements may have 0 or more dashes applied to them. Regular lists are a special case of dashed lists, with no dashes applied.

Examples of dashed lists:

    [a, ((b, c)', d'')']
    [a', b'', c]
    [a, b, c, d] (a plain list without dashes)

Dashed lists maintain the associative concatenation property and introduce a dash operation. In this project, we provide a formal construction of dashed lists in Lean4, showcasing their structure and properties. More explanation on this and the codes related to this are in Dashed_Lists directory.

We define dashed lists as inductive type with five constructors. The first constructor is the empty list. The second constructor is the inclusion of an element of the underlying set S. The third constructor is the inclusion of a dashed elements of S. The fourth constructor is the inclusion of a dashed multiplication. The fifth constructor is the inclusion of a multiplication. This construction satisfies the required universal property.


2. ### Formalizing Semi-Strict and Strict Categorical Groups

The second part of this project delves into categorical algebra. Specifically, it involves:

Defining semi-strict categorical groups and strict categorical groups in Lean4 and proving their categorical equivalence.

This work extends foundational concepts in category theory and provides a formal framework that connects theoretical results to computational verification.
Why This Matters

Formalizing mathematics ensures that proofs and constructions are rigorous, eliminating human errors in reasoning. This is particularly important in highly abstract fields like category theory, where intuition alone is often insufficient. By contributing to the formalization of advanced mathematical concepts, this project bridges the gap between abstract theory and computational implementation. You can find the related code in stCatGrp directory.



## Appendix A: What is Lean4

Lean is a *dependent-typed programming language and proof assistant*. It’s designed for writing mathematical proofs and formally verifying them with the help of type theory. Think of it as a tool where programming meets logic and mathematics.

If you’re familiar with languages like Python, Java, or C++, Lean might feel different because:

1. It’s rooted in Type Theory, not object-oriented or imperative paradigms. In Lean, a type can represent a mathematical proposition, and its elements are proofs of that proposition. 
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
