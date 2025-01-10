# Formalizing Parts of My Thesis in Lean4

## Introduction

Mathematics is fundamentally about developing methods or algorithms to solve problems. But how can we be sure that these methods are foolproof? Wouldn't it be amazing if a computer could understand mathematical concepts and validate our solutions?

Lean4 is a programming language designed for formalizing mathematics, providing a robust environment to verify mathematical proofs and algorithms. It has an active community that contributes to an ever-growing mathematical library, making it a valuable tool for mathematicians and computer scientists. Have a look at Appendix A for a quick guide to Lean4.

This project aims to formalize parts of my thesis on the Symmetrization of Categorical Groups, which is the categorical equivalent of the Abelianization of a Group. While the thesis itself is highly technical, the aspects I wish to formalize are accessible and potentially interesting to both mathematics and computer science enthusiasts.

Contact me at _parab.7@osu.edu_ if you have any questions or comments.

---

## Project Overview

1. ### Constructing a Framework for Dashed Lists

The first part of this project is motivated by the familiar construction of the data structure List S, where the elements are derived from a set S. Lists are a cornerstone of computer science, valued for their simplicity and flexibility. One of their key properties is associative concatenation:
(L1+L2)+L3=L1+(L2+L3)
(L1​+L2​)+L3​=L1​+(L2​+L3​)

Here, we introduce a new data structure, denoted as DMon S (inspired by the term "free dashed monoid"). Elements of DMon S, called dashed lists, are nested lists where elements may have 0 or more dashes applied to them. Regular lists are a special case of dashed lists, with no dashes applied.

Examples of dashed lists:

    [a, ((b, c)', d'')']
    [a', b'', c]
    [a, b, c, d] (a plain list without dashes)

Dashed lists maintain the associative concatenation property and introduce a dash operation. In this project, we provide a formal construction of dashed lists in Lean4, showcasing their structure and properties. More explanation on this and the codes related to this are in Dashed_Lists directory.

2. ### Formalizing Semi-Strict and Strict Categorical Groups

The second part of this project delves into categorical algebra. Specifically, it involves:

    Defining semi-strict categorical groups and strict categorical groups in Lean4.
    Proving their categorical equivalence.

This work extends foundational concepts in category theory and provides a formal framework that connects theoretical results to computational verification.
Why This Matters

Formalizing mathematics ensures that proofs and constructions are rigorous, eliminating human errors in reasoning. This is particularly important in highly abstract fields like category theory, where intuition alone is often insufficient. By contributing to the formalization of advanced mathematical concepts, this project bridges the gap between abstract theory and computational implementation.



## Appendix A: What is Lean4

Lean is a *dependent-typed programming language and proof assistant*. It’s designed for writing mathematical proofs and formally verifying them with the help of type theory. Think of it as a tool where programming meets logic and mathematics.

If you’re familiar with languages like Python, Java, or C++, Lean might feel different because:

1. It’s rooted in Type Theory, not object-oriented or imperative paradigms. In Lean, a type can represent a mathematical proposition, and its elements are proofs of that proposition. 
2. The focus is on correctness and proof rather than just running code. Writing a function in Lean often corresponds to proving something.

Here’s a quick guide to understanding Lean for someone familiar with other programming languages:
What is Lean?

Lean is a dependently-typed programming language and proof assistant. It’s designed for writing mathematical proofs and formally verifying them with the help of type theory. Think of it as a tool where programming meets logic and mathematics.

If you’re familiar with languages like Python, Java, or C++, Lean might feel different because:

    It’s rooted in Type Theory, not object-oriented or imperative paradigms.
    The focus is on correctness and proof rather than just running code.

Core Concepts
1. Type Theory

Lean is based on a type system that ensures everything is consistent:

    Types as Propositions: In Lean, a type can represent a mathematical proposition, and its elements are proofs of that proposition.
    Functions as Proofs: Writing a function in Lean often corresponds to proving something.

Example:

theorem example : 1 + 1 = 2 :=
rfl  -- "rfl" means "reflexivity," i.e., this is true by definition.

Here:

    theorem example declares a theorem named example.
    1 + 1 = 2 is the proposition.
    rfl is the proof.

### Reading Lean Code

Lean code has a declarative style, often involving theorems, definitions, and tactics:

    *Definitions* (def): Define functions or values, like in most programming languages.
    *Theorems/Propositions* (theorem or lemma): Statements you want to prove.
    *Tactics* : Step-by-step tools to guide Lean in constructing a proof.

