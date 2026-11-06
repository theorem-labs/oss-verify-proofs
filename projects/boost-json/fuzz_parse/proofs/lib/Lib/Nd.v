(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia List.
From Ltac2 Require Ltac2.
From Ltac2 Require FSet.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init5Logic03and02ex" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma and_elimF2 : ltac2:(zQ "10!h4>2A1P>2A2P>1GP>0>0^3>0^3^3>0@2$0^4^3^3").
Proof. intros A1 A2 G. intros K [a r]. exact (K a r). Qed.
Lemma and_elimF3 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>1GP>0>0^4>0^4>0^4^4>0@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 G. intros K [a r]. exact (and_elimF2 A2 A3 G (K a) r). Qed.
Lemma and_elimF4 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>1GP>0>0^5>0^5>0^5>0^5^5>0@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 G. intros K [a r]. exact (and_elimF3 A2 A3 A4 G (K a) r). Qed.
Lemma and_elimF5 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>1GP>0>0^6>0^6>0^6>0^6>0^6^6>0@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 G. intros K [a r]. exact (and_elimF4 A2 A3 A4 A5 G (K a) r). Qed.
Lemma and_elimF6 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>1GP>0>0^7>0^7>0^7>0^7>0^7>0^7^7>0@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 G. intros K [a r]. exact (and_elimF5 A2 A3 A4 A5 A6 G (K a) r). Qed.
Lemma and_elimF7 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>1GP>0>0^8>0^8>0^8>0^8>0^8>0^8>0^8^8>0@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 G. intros K [a r]. exact (and_elimF6 A2 A3 A4 A5 A6 A7 G (K a) r). Qed.
Lemma and_elimF8 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>1GP>0>0^9>0^9>0^9>0^9>0^9>0^9>0^9>0^9^9>0@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 G. intros K [a r]. exact (and_elimF7 A2 A3 A4 A5 A6 A7 A8 G (K a) r). Qed.
Lemma and_elimF9 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>1GP>0>0^a>0^a>0^a>0^a>0^a>0^a>0^a>0^a>0^a^a>0@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 G. intros K [a r]. exact (and_elimF8 A2 A3 A4 A5 A6 A7 A8 A9 G (K a) r). Qed.
Lemma and_elimF10 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>1GP>0>0^b>0^b>0^b>0^b>0^b>0^b>0^b>0^b>0^b>0^b^b>0@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 G. intros K [a r]. exact (and_elimF9 A2 A3 A4 A5 A6 A7 A8 A9 A10 G (K a) r). Qed.
Lemma and_elimF11 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>1GP>0>0^c>0^c>0^c>0^c>0^c>0^c>0^c>0^c>0^c>0^c>0^c^c>0@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 G. intros K [a r]. exact (and_elimF10 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 G (K a) r). Qed.
Lemma and_elimF12 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>1GP>0>0^d>0^d>0^d>0^d>0^d>0^d>0^d>0^d>0^d>0^d>0^d>0^d^d>0@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 G. intros K [a r]. exact (and_elimF11 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 G (K a) r). Qed.
Lemma and_elimF13 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>1GP>0>0^e>0^e>0^e>0^e>0^e>0^e>0^e>0^e>0^e>0^e>0^e>0^e>0^e^e>0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 G. intros K [a r]. exact (and_elimF12 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 G (K a) r). Qed.
Lemma and_elimF14 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>1GP>0>0^f>0^f>0^f>0^f>0^f>0^f>0^f>0^f>0^f>0^f>0^f>0^f>0^f>0^f^f>0@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 G. intros K [a r]. exact (and_elimF13 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 G (K a) r). Qed.
Lemma and_elimF15 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>1GP>0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0^h0>0@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 G. intros K [a r]. exact (and_elimF14 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 G (K a) r). Qed.
Lemma and_elimF16 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>1GP>0>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1^h1>0@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 G. intros K [a r]. exact (and_elimF15 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 G (K a) r). Qed.
Lemma and_elimF17 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>1GP>0>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2^h2>0@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 G. intros K [a r]. exact (and_elimF16 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 G (K a) r). Qed.
Lemma and_elimF18 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>1GP>0>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3^h3>0@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 G. intros K [a r]. exact (and_elimF17 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 G (K a) r). Qed.
Lemma and_elimF19 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>1GP>0>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4^h4>0@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 G. intros K [a r]. exact (and_elimF18 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 G (K a) r). Qed.
Lemma and_elimF20 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>1GP>0>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5^h5>0@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 G. intros K [a r]. exact (and_elimF19 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 G (K a) r). Qed.
Lemma and_elimF21 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>1GP>0>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6^h6>0@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 G. intros K [a r]. exact (and_elimF20 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 G (K a) r). Qed.
Lemma and_elimF22 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>1GP>0>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7^h7>0@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 G. intros K [a r]. exact (and_elimF21 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 G (K a) r). Qed.
Lemma and_elimF23 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>1GP>0>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8^h8>0@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 G. intros K [a r]. exact (and_elimF22 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 G (K a) r). Qed.
Lemma and_elimF24 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>1GP>0>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9^h9>0@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 G. intros K [a r]. exact (and_elimF23 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 G (K a) r). Qed.
Lemma and_elimF25 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>1GP>0>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha^ha>0@2$0^hb@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 G. intros K [a r]. exact (and_elimF24 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 G (K a) r). Qed.
Lemma and_elimF26 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>1GP>0>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb^hb>0@2$0^hc@2$0^hb@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 G. intros K [a r]. exact (and_elimF25 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 G (K a) r). Qed.
Lemma and_elimF27 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>1GP>0>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc^hc>0@2$0^hd@2$0^hc@2$0^hb@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 G. intros K [a r]. exact (and_elimF26 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 G (K a) r). Qed.
Lemma and_elimF28 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>1GP>0>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd^hd>0@2$0^he@2$0^hd@2$0^hc@2$0^hb@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 G. intros K [a r]. exact (and_elimF27 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 G (K a) r). Qed.
Lemma and_elimF29 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>3A29P>1GP>0>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he^he>0@2$0^hf@2$0^he@2$0^hd@2$0^hc@2$0^hb@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 G. intros K [a r]. exact (and_elimF28 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 G (K a) r). Qed.
Lemma and_elimF30 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>3A29P>3A30P>1GP>0>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf^hf>0@2$0^i0@2$0^hf@2$0^he@2$0^hd@2$0^hc@2$0^hb@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 G. intros K [a r]. exact (and_elimF29 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 G (K a) r). Qed.
Lemma and_elimF31 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>3A29P>3A30P>3A31P>1GP>0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0^i0>0@2$0^i1@2$0^i0@2$0^hf@2$0^he@2$0^hd@2$0^hc@2$0^hb@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 G. intros K [a r]. exact (and_elimF30 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 G (K a) r). Qed.
Lemma and_elimF32 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>3A29P>3A30P>3A31P>3A32P>1GP>0>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1^i1>0@2$0^i2@2$0^i1@2$0^i0@2$0^hf@2$0^he@2$0^hd@2$0^hc@2$0^hb@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 G. intros K [a r]. exact (and_elimF31 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 G (K a) r). Qed.
Lemma and_elimF33 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>3A29P>3A30P>3A31P>3A32P>3A33P>1GP>0>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2^i2>0@2$0^i3@2$0^i2@2$0^i1@2$0^i0@2$0^hf@2$0^he@2$0^hd@2$0^hc@2$0^hb@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 G. intros K [a r]. exact (and_elimF32 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 G (K a) r). Qed.
Lemma and_elimF34 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>3A29P>3A30P>3A31P>3A32P>3A33P>3A34P>1GP>0>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3^i3>0@2$0^i4@2$0^i3@2$0^i2@2$0^i1@2$0^i0@2$0^hf@2$0^he@2$0^hd@2$0^hc@2$0^hb@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 G. intros K [a r]. exact (and_elimF33 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 G (K a) r). Qed.
Lemma and_elimF35 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>3A29P>3A30P>3A31P>3A32P>3A33P>3A34P>3A35P>1GP>0>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4^i4>0@2$0^i5@2$0^i4@2$0^i3@2$0^i2@2$0^i1@2$0^i0@2$0^hf@2$0^he@2$0^hd@2$0^hc@2$0^hb@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 G. intros K [a r]. exact (and_elimF34 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 G (K a) r). Qed.
Lemma and_elimF36 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>3A29P>3A30P>3A31P>3A32P>3A33P>3A34P>3A35P>3A36P>1GP>0>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5^i5>0@2$0^i6@2$0^i5@2$0^i4@2$0^i3@2$0^i2@2$0^i1@2$0^i0@2$0^hf@2$0^he@2$0^hd@2$0^hc@2$0^hb@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 G. intros K [a r]. exact (and_elimF35 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 G (K a) r). Qed.
Lemma and_elimF37 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>3A29P>3A30P>3A31P>3A32P>3A33P>3A34P>3A35P>3A36P>3A37P>1GP>0>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6^i6>0@2$0^i7@2$0^i6@2$0^i5@2$0^i4@2$0^i3@2$0^i2@2$0^i1@2$0^i0@2$0^hf@2$0^he@2$0^hd@2$0^hc@2$0^hb@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 G. intros K [a r]. exact (and_elimF36 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 G (K a) r). Qed.
Lemma and_elimF38 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>3A29P>3A30P>3A31P>3A32P>3A33P>3A34P>3A35P>3A36P>3A37P>3A38P>1GP>0>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7^i7>0@2$0^i8@2$0^i7@2$0^i6@2$0^i5@2$0^i4@2$0^i3@2$0^i2@2$0^i1@2$0^i0@2$0^hf@2$0^he@2$0^hd@2$0^hc@2$0^hb@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 G. intros K [a r]. exact (and_elimF37 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 G (K a) r). Qed.
Lemma and_elimF39 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>3A29P>3A30P>3A31P>3A32P>3A33P>3A34P>3A35P>3A36P>3A37P>3A38P>3A39P>1GP>0>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8^i8>0@2$0^i9@2$0^i8@2$0^i7@2$0^i6@2$0^i5@2$0^i4@2$0^i3@2$0^i2@2$0^i1@2$0^i0@2$0^hf@2$0^he@2$0^hd@2$0^hc@2$0^hb@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 G. intros K [a r]. exact (and_elimF38 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 G (K a) r). Qed.
Lemma and_elimF40 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>3A29P>3A30P>3A31P>3A32P>3A33P>3A34P>3A35P>3A36P>3A37P>3A38P>3A39P>3A40P>1GP>0>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9>0^i9^i9>0@2$0^ia@2$0^i9@2$0^i8@2$0^i7@2$0^i6@2$0^i5@2$0^i4@2$0^i3@2$0^i2@2$0^i1@2$0^i0@2$0^hf@2$0^he@2$0^hd@2$0^hc@2$0^hb@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 G. intros K [a r]. exact (and_elimF39 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 G (K a) r). Qed.
Lemma and_elimF41 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>3A29P>3A30P>3A31P>3A32P>3A33P>3A34P>3A35P>3A36P>3A37P>3A38P>3A39P>3A40P>3A41P>1GP>0>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia>0^ia^ia>0@2$0^ib@2$0^ia@2$0^i9@2$0^i8@2$0^i7@2$0^i6@2$0^i5@2$0^i4@2$0^i3@2$0^i2@2$0^i1@2$0^i0@2$0^hf@2$0^he@2$0^hd@2$0^hc@2$0^hb@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 G. intros K [a r]. exact (and_elimF40 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 G (K a) r). Qed.
Lemma and_elimF42 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>3A29P>3A30P>3A31P>3A32P>3A33P>3A34P>3A35P>3A36P>3A37P>3A38P>3A39P>3A40P>3A41P>3A42P>1GP>0>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib>0^ib^ib>0@2$0^ic@2$0^ib@2$0^ia@2$0^i9@2$0^i8@2$0^i7@2$0^i6@2$0^i5@2$0^i4@2$0^i3@2$0^i2@2$0^i1@2$0^i0@2$0^hf@2$0^he@2$0^hd@2$0^hc@2$0^hb@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 G. intros K [a r]. exact (and_elimF41 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 G (K a) r). Qed.
Lemma and_elimF43 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>3A29P>3A30P>3A31P>3A32P>3A33P>3A34P>3A35P>3A36P>3A37P>3A38P>3A39P>3A40P>3A41P>3A42P>3A43P>1GP>0>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic>0^ic^ic>0@2$0^id@2$0^ic@2$0^ib@2$0^ia@2$0^i9@2$0^i8@2$0^i7@2$0^i6@2$0^i5@2$0^i4@2$0^i3@2$0^i2@2$0^i1@2$0^i0@2$0^hf@2$0^he@2$0^hd@2$0^hc@2$0^hb@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 G. intros K [a r]. exact (and_elimF42 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 G (K a) r). Qed.
Lemma and_elimF44 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>3A29P>3A30P>3A31P>3A32P>3A33P>3A34P>3A35P>3A36P>3A37P>3A38P>3A39P>3A40P>3A41P>3A42P>3A43P>3A44P>1GP>0>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id>0^id^id>0@2$0^ie@2$0^id@2$0^ic@2$0^ib@2$0^ia@2$0^i9@2$0^i8@2$0^i7@2$0^i6@2$0^i5@2$0^i4@2$0^i3@2$0^i2@2$0^i1@2$0^i0@2$0^hf@2$0^he@2$0^hd@2$0^hc@2$0^hb@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 A44 G. intros K [a r]. exact (and_elimF43 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 A44 G (K a) r). Qed.
Lemma and_elimF45 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>3A29P>3A30P>3A31P>3A32P>3A33P>3A34P>3A35P>3A36P>3A37P>3A38P>3A39P>3A40P>3A41P>3A42P>3A43P>3A44P>3A45P>1GP>0>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie>0^ie^ie>0@2$0^if@2$0^ie@2$0^id@2$0^ic@2$0^ib@2$0^ia@2$0^i9@2$0^i8@2$0^i7@2$0^i6@2$0^i5@2$0^i4@2$0^i3@2$0^i2@2$0^i1@2$0^i0@2$0^hf@2$0^he@2$0^hd@2$0^hc@2$0^hb@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 A44 A45 G. intros K [a r]. exact (and_elimF44 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 A44 A45 G (K a) r). Qed.
Lemma and_elimF46 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>3A29P>3A30P>3A31P>3A32P>3A33P>3A34P>3A35P>3A36P>3A37P>3A38P>3A39P>3A40P>3A41P>3A42P>3A43P>3A44P>3A45P>3A46P>1GP>0>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if>0^if^if>0@2$0^j0@2$0^if@2$0^ie@2$0^id@2$0^ic@2$0^ib@2$0^ia@2$0^i9@2$0^i8@2$0^i7@2$0^i6@2$0^i5@2$0^i4@2$0^i3@2$0^i2@2$0^i1@2$0^i0@2$0^hf@2$0^he@2$0^hd@2$0^hc@2$0^hb@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 A44 A45 A46 G. intros K [a r]. exact (and_elimF45 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 A44 A45 A46 G (K a) r). Qed.
Lemma and_elimF47 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>3A29P>3A30P>3A31P>3A32P>3A33P>3A34P>3A35P>3A36P>3A37P>3A38P>3A39P>3A40P>3A41P>3A42P>3A43P>3A44P>3A45P>3A46P>3A47P>1GP>0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0>0^j0^j0>0@2$0^j1@2$0^j0@2$0^if@2$0^ie@2$0^id@2$0^ic@2$0^ib@2$0^ia@2$0^i9@2$0^i8@2$0^i7@2$0^i6@2$0^i5@2$0^i4@2$0^i3@2$0^i2@2$0^i1@2$0^i0@2$0^hf@2$0^he@2$0^hd@2$0^hc@2$0^hb@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 A44 A45 A46 A47 G. intros K [a r]. exact (and_elimF46 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 A44 A45 A46 A47 G (K a) r). Qed.
Lemma and_elimF48 : ltac2:(zQ "10!h4>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>3A29P>3A30P>3A31P>3A32P>3A33P>3A34P>3A35P>3A36P>3A37P>3A38P>3A39P>3A40P>3A41P>3A42P>3A43P>3A44P>3A45P>3A46P>3A47P>3A48P>1GP>0>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1>0^j1^j1>0@2$0^j2@2$0^j1@2$0^j0@2$0^if@2$0^ie@2$0^id@2$0^ic@2$0^ib@2$0^ia@2$0^i9@2$0^i8@2$0^i7@2$0^i6@2$0^i5@2$0^i4@2$0^i3@2$0^i2@2$0^i1@2$0^i0@2$0^hf@2$0^he@2$0^hd@2$0^hc@2$0^hb@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8@2$0^7@2$0^6@2$0^5@2$0^4^3^3").
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 A44 A45 A46 A47 A48 G. intros K [a r]. exact (and_elimF47 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 A44 A45 A46 A47 A48 G (K a) r). Qed.
Lemma ex_elimF1 : ltac2:(zQ "10!h9>2T1T>1P>0^1P>1GP>0>2x1^3>0@1^3^1^3>0@2$0^4\2x1^4@1^4^1^3").
Proof. intros T1 P G. intros K [x h]. exact (K x h). Qed.
Lemma ex_elimF2 : ltac2:(zQ "10!h9>2T1T>2T2T>1P>0^2>0^2P>1GP>0>2x1^4>2x2^4>0@2^4^2^1^4>0@2$0^5\2x1^5@2$0^5\2x2^5@2^5^2^1^3").
Proof. intros T1 T2 P G. intros K [x h]. exact (ex_elimF1 T2 (P x) G (K x) h). Qed.
Lemma ex_elimF3 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>1P>0^3>0^3>0^3P>1GP>0>2x1^5>2x2^5>2x3^5>0@3^5^3^2^1^5>0@2$0^6\2x1^6@2$0^6\2x2^6@2$0^6\2x3^6@3^6^3^2^1^3").
Proof. intros T1 T2 T3 P G. intros K [x h]. exact (ex_elimF2 T2 T3 (P x) G (K x) h). Qed.
Lemma ex_elimF4 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>1P>0^4>0^4>0^4>0^4P>1GP>0>2x1^6>2x2^6>2x3^6>2x4^6>0@4^6^4^3^2^1^6>0@2$0^7\2x1^7@2$0^7\2x2^7@2$0^7\2x3^7@2$0^7\2x4^7@4^7^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 P G. intros K [x h]. exact (ex_elimF3 T2 T3 T4 (P x) G (K x) h). Qed.
Lemma ex_elimF5 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>1P>0^5>0^5>0^5>0^5>0^5P>1GP>0>2x1^7>2x2^7>2x3^7>2x4^7>2x5^7>0@5^7^5^4^3^2^1^7>0@2$0^8\2x1^8@2$0^8\2x2^8@2$0^8\2x3^8@2$0^8\2x4^8@2$0^8\2x5^8@5^8^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 P G. intros K [x h]. exact (ex_elimF4 T2 T3 T4 T5 (P x) G (K x) h). Qed.
Lemma ex_elimF6 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>1P>0^6>0^6>0^6>0^6>0^6>0^6P>1GP>0>2x1^8>2x2^8>2x3^8>2x4^8>2x5^8>2x6^8>0@6^8^6^5^4^3^2^1^8>0@2$0^9\2x1^9@2$0^9\2x2^9@2$0^9\2x3^9@2$0^9\2x4^9@2$0^9\2x5^9@2$0^9\2x6^9@6^9^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 P G. intros K [x h]. exact (ex_elimF5 T2 T3 T4 T5 T6 (P x) G (K x) h). Qed.
Lemma ex_elimF7 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>1P>0^7>0^7>0^7>0^7>0^7>0^7>0^7P>1GP>0>2x1^9>2x2^9>2x3^9>2x4^9>2x5^9>2x6^9>2x7^9>0@7^9^7^6^5^4^3^2^1^9>0@2$0^a\2x1^a@2$0^a\2x2^a@2$0^a\2x3^a@2$0^a\2x4^a@2$0^a\2x5^a@2$0^a\2x6^a@2$0^a\2x7^a@7^a^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 P G. intros K [x h]. exact (ex_elimF6 T2 T3 T4 T5 T6 T7 (P x) G (K x) h). Qed.
Lemma ex_elimF8 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>1P>0^8>0^8>0^8>0^8>0^8>0^8>0^8>0^8P>1GP>0>2x1^a>2x2^a>2x3^a>2x4^a>2x5^a>2x6^a>2x7^a>2x8^a>0@8^a^8^7^6^5^4^3^2^1^a>0@2$0^b\2x1^b@2$0^b\2x2^b@2$0^b\2x3^b@2$0^b\2x4^b@2$0^b\2x5^b@2$0^b\2x6^b@2$0^b\2x7^b@2$0^b\2x8^b@8^b^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 P G. intros K [x h]. exact (ex_elimF7 T2 T3 T4 T5 T6 T7 T8 (P x) G (K x) h). Qed.
Lemma ex_elimF9 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>1P>0^9>0^9>0^9>0^9>0^9>0^9>0^9>0^9>0^9P>1GP>0>2x1^b>2x2^b>2x3^b>2x4^b>2x5^b>2x6^b>2x7^b>2x8^b>2x9^b>0@9^b^9^8^7^6^5^4^3^2^1^b>0@2$0^c\2x1^c@2$0^c\2x2^c@2$0^c\2x3^c@2$0^c\2x4^c@2$0^c\2x5^c@2$0^c\2x6^c@2$0^c\2x7^c@2$0^c\2x8^c@2$0^c\2x9^c@9^c^9^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 P G. intros K [x h]. exact (ex_elimF8 T2 T3 T4 T5 T6 T7 T8 T9 (P x) G (K x) h). Qed.
Lemma ex_elimF10 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>1P>0^a>0^a>0^a>0^a>0^a>0^a>0^a>0^a>0^a>0^aP>1GP>0>2x1^c>2x2^c>2x3^c>2x4^c>2x5^c>2x6^c>2x7^c>2x8^c>2x9^c>3x10^c>0@a^c^a^9^8^7^6^5^4^3^2^1^c>0@2$0^d\2x1^d@2$0^d\2x2^d@2$0^d\2x3^d@2$0^d\2x4^d@2$0^d\2x5^d@2$0^d\2x6^d@2$0^d\2x7^d@2$0^d\2x8^d@2$0^d\2x9^d@2$0^d\3x10^d@a^d^a^9^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 P G. intros K [x h]. exact (ex_elimF9 T2 T3 T4 T5 T6 T7 T8 T9 T10 (P x) G (K x) h). Qed.
Lemma ex_elimF11 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>1P>0^b>0^b>0^b>0^b>0^b>0^b>0^b>0^b>0^b>0^b>0^bP>1GP>0>2x1^d>2x2^d>2x3^d>2x4^d>2x5^d>2x6^d>2x7^d>2x8^d>2x9^d>3x10^d>3x11^d>0@b^d^b^a^9^8^7^6^5^4^3^2^1^d>0@2$0^e\2x1^e@2$0^e\2x2^e@2$0^e\2x3^e@2$0^e\2x4^e@2$0^e\2x5^e@2$0^e\2x6^e@2$0^e\2x7^e@2$0^e\2x8^e@2$0^e\2x9^e@2$0^e\3x10^e@2$0^e\3x11^e@b^e^b^a^9^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 P G. intros K [x h]. exact (ex_elimF10 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 (P x) G (K x) h). Qed.
Lemma ex_elimF12 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>1P>0^c>0^c>0^c>0^c>0^c>0^c>0^c>0^c>0^c>0^c>0^c>0^cP>1GP>0>2x1^e>2x2^e>2x3^e>2x4^e>2x5^e>2x6^e>2x7^e>2x8^e>2x9^e>3x10^e>3x11^e>3x12^e>0@c^e^c^b^a^9^8^7^6^5^4^3^2^1^e>0@2$0^f\2x1^f@2$0^f\2x2^f@2$0^f\2x3^f@2$0^f\2x4^f@2$0^f\2x5^f@2$0^f\2x6^f@2$0^f\2x7^f@2$0^f\2x8^f@2$0^f\2x9^f@2$0^f\3x10^f@2$0^f\3x11^f@2$0^f\3x12^f@c^f^c^b^a^9^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 P G. intros K [x h]. exact (ex_elimF11 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 (P x) G (K x) h). Qed.
Lemma ex_elimF13 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>1P>0^d>0^d>0^d>0^d>0^d>0^d>0^d>0^d>0^d>0^d>0^d>0^d>0^dP>1GP>0>2x1^f>2x2^f>2x3^f>2x4^f>2x5^f>2x6^f>2x7^f>2x8^f>2x9^f>3x10^f>3x11^f>3x12^f>3x13^f>0@d^f^d^c^b^a^9^8^7^6^5^4^3^2^1^f>0@2$0^h0\2x1^h0@2$0^h0\2x2^h0@2$0^h0\2x3^h0@2$0^h0\2x4^h0@2$0^h0\2x5^h0@2$0^h0\2x6^h0@2$0^h0\2x7^h0@2$0^h0\2x8^h0@2$0^h0\2x9^h0@2$0^h0\3x10^h0@2$0^h0\3x11^h0@2$0^h0\3x12^h0@2$0^h0\3x13^h0@d^h0^d^c^b^a^9^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 P G. intros K [x h]. exact (ex_elimF12 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 (P x) G (K x) h). Qed.
Lemma ex_elimF14 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>1P>0^e>0^e>0^e>0^e>0^e>0^e>0^e>0^e>0^e>0^e>0^e>0^e>0^e>0^eP>1GP>0>2x1^h0>2x2^h0>2x3^h0>2x4^h0>2x5^h0>2x6^h0>2x7^h0>2x8^h0>2x9^h0>3x10^h0>3x11^h0>3x12^h0>3x13^h0>3x14^h0>0@e^h0^e^d^c^b^a^9^8^7^6^5^4^3^2^1^h0>0@2$0^h1\2x1^h1@2$0^h1\2x2^h1@2$0^h1\2x3^h1@2$0^h1\2x4^h1@2$0^h1\2x5^h1@2$0^h1\2x6^h1@2$0^h1\2x7^h1@2$0^h1\2x8^h1@2$0^h1\2x9^h1@2$0^h1\3x10^h1@2$0^h1\3x11^h1@2$0^h1\3x12^h1@2$0^h1\3x13^h1@2$0^h1\3x14^h1@e^h1^e^d^c^b^a^9^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 P G. intros K [x h]. exact (ex_elimF13 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 (P x) G (K x) h). Qed.
Lemma ex_elimF15 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>1P>0^f>0^f>0^f>0^f>0^f>0^f>0^f>0^f>0^f>0^f>0^f>0^f>0^f>0^f>0^fP>1GP>0>2x1^h1>2x2^h1>2x3^h1>2x4^h1>2x5^h1>2x6^h1>2x7^h1>2x8^h1>2x9^h1>3x10^h1>3x11^h1>3x12^h1>3x13^h1>3x14^h1>3x15^h1>0@f^h1^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^h1>0@2$0^h2\2x1^h2@2$0^h2\2x2^h2@2$0^h2\2x3^h2@2$0^h2\2x4^h2@2$0^h2\2x5^h2@2$0^h2\2x6^h2@2$0^h2\2x7^h2@2$0^h2\2x8^h2@2$0^h2\2x9^h2@2$0^h2\3x10^h2@2$0^h2\3x11^h2@2$0^h2\3x12^h2@2$0^h2\3x13^h2@2$0^h2\3x14^h2@2$0^h2\3x15^h2@f^h2^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 P G. intros K [x h]. exact (ex_elimF14 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 (P x) G (K x) h). Qed.
Lemma ex_elimF16 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>1P>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0P>1GP>0>2x1^h2>2x2^h2>2x3^h2>2x4^h2>2x5^h2>2x6^h2>2x7^h2>2x8^h2>2x9^h2>3x10^h2>3x11^h2>3x12^h2>3x13^h2>3x14^h2>3x15^h2>3x16^h2>0@h0^h2^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^h2>0@2$0^h3\2x1^h3@2$0^h3\2x2^h3@2$0^h3\2x3^h3@2$0^h3\2x4^h3@2$0^h3\2x5^h3@2$0^h3\2x6^h3@2$0^h3\2x7^h3@2$0^h3\2x8^h3@2$0^h3\2x9^h3@2$0^h3\3x10^h3@2$0^h3\3x11^h3@2$0^h3\3x12^h3@2$0^h3\3x13^h3@2$0^h3\3x14^h3@2$0^h3\3x15^h3@2$0^h3\3x16^h3@h0^h3^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 P G. intros K [x h]. exact (ex_elimF15 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 (P x) G (K x) h). Qed.
Lemma ex_elimF17 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>1P>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1P>1GP>0>2x1^h3>2x2^h3>2x3^h3>2x4^h3>2x5^h3>2x6^h3>2x7^h3>2x8^h3>2x9^h3>3x10^h3>3x11^h3>3x12^h3>3x13^h3>3x14^h3>3x15^h3>3x16^h3>3x17^h3>0@h1^h3^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^h3>0@2$0^h4\2x1^h4@2$0^h4\2x2^h4@2$0^h4\2x3^h4@2$0^h4\2x4^h4@2$0^h4\2x5^h4@2$0^h4\2x6^h4@2$0^h4\2x7^h4@2$0^h4\2x8^h4@2$0^h4\2x9^h4@2$0^h4\3x10^h4@2$0^h4\3x11^h4@2$0^h4\3x12^h4@2$0^h4\3x13^h4@2$0^h4\3x14^h4@2$0^h4\3x15^h4@2$0^h4\3x16^h4@2$0^h4\3x17^h4@h1^h4^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 P G. intros K [x h]. exact (ex_elimF16 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 (P x) G (K x) h). Qed.
Lemma ex_elimF18 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>1P>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2P>1GP>0>2x1^h4>2x2^h4>2x3^h4>2x4^h4>2x5^h4>2x6^h4>2x7^h4>2x8^h4>2x9^h4>3x10^h4>3x11^h4>3x12^h4>3x13^h4>3x14^h4>3x15^h4>3x16^h4>3x17^h4>3x18^h4>0@h2^h4^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^h4>0@2$0^h5\2x1^h5@2$0^h5\2x2^h5@2$0^h5\2x3^h5@2$0^h5\2x4^h5@2$0^h5\2x5^h5@2$0^h5\2x6^h5@2$0^h5\2x7^h5@2$0^h5\2x8^h5@2$0^h5\2x9^h5@2$0^h5\3x10^h5@2$0^h5\3x11^h5@2$0^h5\3x12^h5@2$0^h5\3x13^h5@2$0^h5\3x14^h5@2$0^h5\3x15^h5@2$0^h5\3x16^h5@2$0^h5\3x17^h5@2$0^h5\3x18^h5@h2^h5^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 P G. intros K [x h]. exact (ex_elimF17 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 (P x) G (K x) h). Qed.
Lemma ex_elimF19 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>1P>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3P>1GP>0>2x1^h5>2x2^h5>2x3^h5>2x4^h5>2x5^h5>2x6^h5>2x7^h5>2x8^h5>2x9^h5>3x10^h5>3x11^h5>3x12^h5>3x13^h5>3x14^h5>3x15^h5>3x16^h5>3x17^h5>3x18^h5>3x19^h5>0@h3^h5^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^h5>0@2$0^h6\2x1^h6@2$0^h6\2x2^h6@2$0^h6\2x3^h6@2$0^h6\2x4^h6@2$0^h6\2x5^h6@2$0^h6\2x6^h6@2$0^h6\2x7^h6@2$0^h6\2x8^h6@2$0^h6\2x9^h6@2$0^h6\3x10^h6@2$0^h6\3x11^h6@2$0^h6\3x12^h6@2$0^h6\3x13^h6@2$0^h6\3x14^h6@2$0^h6\3x15^h6@2$0^h6\3x16^h6@2$0^h6\3x17^h6@2$0^h6\3x18^h6@2$0^h6\3x19^h6@h3^h6^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 P G. intros K [x h]. exact (ex_elimF18 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 (P x) G (K x) h). Qed.
Lemma ex_elimF20 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>1P>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4P>1GP>0>2x1^h6>2x2^h6>2x3^h6>2x4^h6>2x5^h6>2x6^h6>2x7^h6>2x8^h6>2x9^h6>3x10^h6>3x11^h6>3x12^h6>3x13^h6>3x14^h6>3x15^h6>3x16^h6>3x17^h6>3x18^h6>3x19^h6>3x20^h6>0@h4^h6^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^h6>0@2$0^h7\2x1^h7@2$0^h7\2x2^h7@2$0^h7\2x3^h7@2$0^h7\2x4^h7@2$0^h7\2x5^h7@2$0^h7\2x6^h7@2$0^h7\2x7^h7@2$0^h7\2x8^h7@2$0^h7\2x9^h7@2$0^h7\3x10^h7@2$0^h7\3x11^h7@2$0^h7\3x12^h7@2$0^h7\3x13^h7@2$0^h7\3x14^h7@2$0^h7\3x15^h7@2$0^h7\3x16^h7@2$0^h7\3x17^h7@2$0^h7\3x18^h7@2$0^h7\3x19^h7@2$0^h7\3x20^h7@h4^h7^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 P G. intros K [x h]. exact (ex_elimF19 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 (P x) G (K x) h). Qed.
Lemma ex_elimF21 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>1P>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5P>1GP>0>2x1^h7>2x2^h7>2x3^h7>2x4^h7>2x5^h7>2x6^h7>2x7^h7>2x8^h7>2x9^h7>3x10^h7>3x11^h7>3x12^h7>3x13^h7>3x14^h7>3x15^h7>3x16^h7>3x17^h7>3x18^h7>3x19^h7>3x20^h7>3x21^h7>0@h5^h7^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^h7>0@2$0^h8\2x1^h8@2$0^h8\2x2^h8@2$0^h8\2x3^h8@2$0^h8\2x4^h8@2$0^h8\2x5^h8@2$0^h8\2x6^h8@2$0^h8\2x7^h8@2$0^h8\2x8^h8@2$0^h8\2x9^h8@2$0^h8\3x10^h8@2$0^h8\3x11^h8@2$0^h8\3x12^h8@2$0^h8\3x13^h8@2$0^h8\3x14^h8@2$0^h8\3x15^h8@2$0^h8\3x16^h8@2$0^h8\3x17^h8@2$0^h8\3x18^h8@2$0^h8\3x19^h8@2$0^h8\3x20^h8@2$0^h8\3x21^h8@h5^h8^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 P G. intros K [x h]. exact (ex_elimF20 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 (P x) G (K x) h). Qed.
Lemma ex_elimF22 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>1P>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6P>1GP>0>2x1^h8>2x2^h8>2x3^h8>2x4^h8>2x5^h8>2x6^h8>2x7^h8>2x8^h8>2x9^h8>3x10^h8>3x11^h8>3x12^h8>3x13^h8>3x14^h8>3x15^h8>3x16^h8>3x17^h8>3x18^h8>3x19^h8>3x20^h8>3x21^h8>3x22^h8>0@h6^h8^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^h8>0@2$0^h9\2x1^h9@2$0^h9\2x2^h9@2$0^h9\2x3^h9@2$0^h9\2x4^h9@2$0^h9\2x5^h9@2$0^h9\2x6^h9@2$0^h9\2x7^h9@2$0^h9\2x8^h9@2$0^h9\2x9^h9@2$0^h9\3x10^h9@2$0^h9\3x11^h9@2$0^h9\3x12^h9@2$0^h9\3x13^h9@2$0^h9\3x14^h9@2$0^h9\3x15^h9@2$0^h9\3x16^h9@2$0^h9\3x17^h9@2$0^h9\3x18^h9@2$0^h9\3x19^h9@2$0^h9\3x20^h9@2$0^h9\3x21^h9@2$0^h9\3x22^h9@h6^h9^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 P G. intros K [x h]. exact (ex_elimF21 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 (P x) G (K x) h). Qed.
Lemma ex_elimF23 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>1P>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7P>1GP>0>2x1^h9>2x2^h9>2x3^h9>2x4^h9>2x5^h9>2x6^h9>2x7^h9>2x8^h9>2x9^h9>3x10^h9>3x11^h9>3x12^h9>3x13^h9>3x14^h9>3x15^h9>3x16^h9>3x17^h9>3x18^h9>3x19^h9>3x20^h9>3x21^h9>3x22^h9>3x23^h9>0@h7^h9^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^h9>0@2$0^ha\2x1^ha@2$0^ha\2x2^ha@2$0^ha\2x3^ha@2$0^ha\2x4^ha@2$0^ha\2x5^ha@2$0^ha\2x6^ha@2$0^ha\2x7^ha@2$0^ha\2x8^ha@2$0^ha\2x9^ha@2$0^ha\3x10^ha@2$0^ha\3x11^ha@2$0^ha\3x12^ha@2$0^ha\3x13^ha@2$0^ha\3x14^ha@2$0^ha\3x15^ha@2$0^ha\3x16^ha@2$0^ha\3x17^ha@2$0^ha\3x18^ha@2$0^ha\3x19^ha@2$0^ha\3x20^ha@2$0^ha\3x21^ha@2$0^ha\3x22^ha@2$0^ha\3x23^ha@h7^ha^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 P G. intros K [x h]. exact (ex_elimF22 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 (P x) G (K x) h). Qed.
Lemma ex_elimF24 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>1P>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8P>1GP>0>2x1^ha>2x2^ha>2x3^ha>2x4^ha>2x5^ha>2x6^ha>2x7^ha>2x8^ha>2x9^ha>3x10^ha>3x11^ha>3x12^ha>3x13^ha>3x14^ha>3x15^ha>3x16^ha>3x17^ha>3x18^ha>3x19^ha>3x20^ha>3x21^ha>3x22^ha>3x23^ha>3x24^ha>0@h8^ha^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^ha>0@2$0^hb\2x1^hb@2$0^hb\2x2^hb@2$0^hb\2x3^hb@2$0^hb\2x4^hb@2$0^hb\2x5^hb@2$0^hb\2x6^hb@2$0^hb\2x7^hb@2$0^hb\2x8^hb@2$0^hb\2x9^hb@2$0^hb\3x10^hb@2$0^hb\3x11^hb@2$0^hb\3x12^hb@2$0^hb\3x13^hb@2$0^hb\3x14^hb@2$0^hb\3x15^hb@2$0^hb\3x16^hb@2$0^hb\3x17^hb@2$0^hb\3x18^hb@2$0^hb\3x19^hb@2$0^hb\3x20^hb@2$0^hb\3x21^hb@2$0^hb\3x22^hb@2$0^hb\3x23^hb@2$0^hb\3x24^hb@h8^hb^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 P G. intros K [x h]. exact (ex_elimF23 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 (P x) G (K x) h). Qed.
Lemma ex_elimF25 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>3T25T>1P>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9P>1GP>0>2x1^hb>2x2^hb>2x3^hb>2x4^hb>2x5^hb>2x6^hb>2x7^hb>2x8^hb>2x9^hb>3x10^hb>3x11^hb>3x12^hb>3x13^hb>3x14^hb>3x15^hb>3x16^hb>3x17^hb>3x18^hb>3x19^hb>3x20^hb>3x21^hb>3x22^hb>3x23^hb>3x24^hb>3x25^hb>0@h9^hb^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^hb>0@2$0^hc\2x1^hc@2$0^hc\2x2^hc@2$0^hc\2x3^hc@2$0^hc\2x4^hc@2$0^hc\2x5^hc@2$0^hc\2x6^hc@2$0^hc\2x7^hc@2$0^hc\2x8^hc@2$0^hc\2x9^hc@2$0^hc\3x10^hc@2$0^hc\3x11^hc@2$0^hc\3x12^hc@2$0^hc\3x13^hc@2$0^hc\3x14^hc@2$0^hc\3x15^hc@2$0^hc\3x16^hc@2$0^hc\3x17^hc@2$0^hc\3x18^hc@2$0^hc\3x19^hc@2$0^hc\3x20^hc@2$0^hc\3x21^hc@2$0^hc\3x22^hc@2$0^hc\3x23^hc@2$0^hc\3x24^hc@2$0^hc\3x25^hc@h9^hc^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 P G. intros K [x h]. exact (ex_elimF24 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 (P x) G (K x) h). Qed.
Lemma ex_elimF26 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>3T25T>3T26T>1P>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^haP>1GP>0>2x1^hc>2x2^hc>2x3^hc>2x4^hc>2x5^hc>2x6^hc>2x7^hc>2x8^hc>2x9^hc>3x10^hc>3x11^hc>3x12^hc>3x13^hc>3x14^hc>3x15^hc>3x16^hc>3x17^hc>3x18^hc>3x19^hc>3x20^hc>3x21^hc>3x22^hc>3x23^hc>3x24^hc>3x25^hc>3x26^hc>0@ha^hc^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^hc>0@2$0^hd\2x1^hd@2$0^hd\2x2^hd@2$0^hd\2x3^hd@2$0^hd\2x4^hd@2$0^hd\2x5^hd@2$0^hd\2x6^hd@2$0^hd\2x7^hd@2$0^hd\2x8^hd@2$0^hd\2x9^hd@2$0^hd\3x10^hd@2$0^hd\3x11^hd@2$0^hd\3x12^hd@2$0^hd\3x13^hd@2$0^hd\3x14^hd@2$0^hd\3x15^hd@2$0^hd\3x16^hd@2$0^hd\3x17^hd@2$0^hd\3x18^hd@2$0^hd\3x19^hd@2$0^hd\3x20^hd@2$0^hd\3x21^hd@2$0^hd\3x22^hd@2$0^hd\3x23^hd@2$0^hd\3x24^hd@2$0^hd\3x25^hd@2$0^hd\3x26^hd@ha^hd^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 P G. intros K [x h]. exact (ex_elimF25 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 (P x) G (K x) h). Qed.
Lemma ex_elimF27 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>3T25T>3T26T>3T27T>1P>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hbP>1GP>0>2x1^hd>2x2^hd>2x3^hd>2x4^hd>2x5^hd>2x6^hd>2x7^hd>2x8^hd>2x9^hd>3x10^hd>3x11^hd>3x12^hd>3x13^hd>3x14^hd>3x15^hd>3x16^hd>3x17^hd>3x18^hd>3x19^hd>3x20^hd>3x21^hd>3x22^hd>3x23^hd>3x24^hd>3x25^hd>3x26^hd>3x27^hd>0@hb^hd^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^hd>0@2$0^he\2x1^he@2$0^he\2x2^he@2$0^he\2x3^he@2$0^he\2x4^he@2$0^he\2x5^he@2$0^he\2x6^he@2$0^he\2x7^he@2$0^he\2x8^he@2$0^he\2x9^he@2$0^he\3x10^he@2$0^he\3x11^he@2$0^he\3x12^he@2$0^he\3x13^he@2$0^he\3x14^he@2$0^he\3x15^he@2$0^he\3x16^he@2$0^he\3x17^he@2$0^he\3x18^he@2$0^he\3x19^he@2$0^he\3x20^he@2$0^he\3x21^he@2$0^he\3x22^he@2$0^he\3x23^he@2$0^he\3x24^he@2$0^he\3x25^he@2$0^he\3x26^he@2$0^he\3x27^he@hb^he^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 P G. intros K [x h]. exact (ex_elimF26 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 (P x) G (K x) h). Qed.
Lemma ex_elimF28 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>3T25T>3T26T>3T27T>3T28T>1P>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hcP>1GP>0>2x1^he>2x2^he>2x3^he>2x4^he>2x5^he>2x6^he>2x7^he>2x8^he>2x9^he>3x10^he>3x11^he>3x12^he>3x13^he>3x14^he>3x15^he>3x16^he>3x17^he>3x18^he>3x19^he>3x20^he>3x21^he>3x22^he>3x23^he>3x24^he>3x25^he>3x26^he>3x27^he>3x28^he>0@hc^he^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^he>0@2$0^hf\2x1^hf@2$0^hf\2x2^hf@2$0^hf\2x3^hf@2$0^hf\2x4^hf@2$0^hf\2x5^hf@2$0^hf\2x6^hf@2$0^hf\2x7^hf@2$0^hf\2x8^hf@2$0^hf\2x9^hf@2$0^hf\3x10^hf@2$0^hf\3x11^hf@2$0^hf\3x12^hf@2$0^hf\3x13^hf@2$0^hf\3x14^hf@2$0^hf\3x15^hf@2$0^hf\3x16^hf@2$0^hf\3x17^hf@2$0^hf\3x18^hf@2$0^hf\3x19^hf@2$0^hf\3x20^hf@2$0^hf\3x21^hf@2$0^hf\3x22^hf@2$0^hf\3x23^hf@2$0^hf\3x24^hf@2$0^hf\3x25^hf@2$0^hf\3x26^hf@2$0^hf\3x27^hf@2$0^hf\3x28^hf@hc^hf^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 P G. intros K [x h]. exact (ex_elimF27 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 (P x) G (K x) h). Qed.
Lemma ex_elimF29 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>3T25T>3T26T>3T27T>3T28T>3T29T>1P>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hdP>1GP>0>2x1^hf>2x2^hf>2x3^hf>2x4^hf>2x5^hf>2x6^hf>2x7^hf>2x8^hf>2x9^hf>3x10^hf>3x11^hf>3x12^hf>3x13^hf>3x14^hf>3x15^hf>3x16^hf>3x17^hf>3x18^hf>3x19^hf>3x20^hf>3x21^hf>3x22^hf>3x23^hf>3x24^hf>3x25^hf>3x26^hf>3x27^hf>3x28^hf>3x29^hf>0@hd^hf^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^hf>0@2$0^i0\2x1^i0@2$0^i0\2x2^i0@2$0^i0\2x3^i0@2$0^i0\2x4^i0@2$0^i0\2x5^i0@2$0^i0\2x6^i0@2$0^i0\2x7^i0@2$0^i0\2x8^i0@2$0^i0\2x9^i0@2$0^i0\3x10^i0@2$0^i0\3x11^i0@2$0^i0\3x12^i0@2$0^i0\3x13^i0@2$0^i0\3x14^i0@2$0^i0\3x15^i0@2$0^i0\3x16^i0@2$0^i0\3x17^i0@2$0^i0\3x18^i0@2$0^i0\3x19^i0@2$0^i0\3x20^i0@2$0^i0\3x21^i0@2$0^i0\3x22^i0@2$0^i0\3x23^i0@2$0^i0\3x24^i0@2$0^i0\3x25^i0@2$0^i0\3x26^i0@2$0^i0\3x27^i0@2$0^i0\3x28^i0@2$0^i0\3x29^i0@hd^i0^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 P G. intros K [x h]. exact (ex_elimF28 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 (P x) G (K x) h). Qed.
Lemma ex_elimF30 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>3T25T>3T26T>3T27T>3T28T>3T29T>3T30T>1P>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^heP>1GP>0>2x1^i0>2x2^i0>2x3^i0>2x4^i0>2x5^i0>2x6^i0>2x7^i0>2x8^i0>2x9^i0>3x10^i0>3x11^i0>3x12^i0>3x13^i0>3x14^i0>3x15^i0>3x16^i0>3x17^i0>3x18^i0>3x19^i0>3x20^i0>3x21^i0>3x22^i0>3x23^i0>3x24^i0>3x25^i0>3x26^i0>3x27^i0>3x28^i0>3x29^i0>3x30^i0>0@he^i0^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^i0>0@2$0^i1\2x1^i1@2$0^i1\2x2^i1@2$0^i1\2x3^i1@2$0^i1\2x4^i1@2$0^i1\2x5^i1@2$0^i1\2x6^i1@2$0^i1\2x7^i1@2$0^i1\2x8^i1@2$0^i1\2x9^i1@2$0^i1\3x10^i1@2$0^i1\3x11^i1@2$0^i1\3x12^i1@2$0^i1\3x13^i1@2$0^i1\3x14^i1@2$0^i1\3x15^i1@2$0^i1\3x16^i1@2$0^i1\3x17^i1@2$0^i1\3x18^i1@2$0^i1\3x19^i1@2$0^i1\3x20^i1@2$0^i1\3x21^i1@2$0^i1\3x22^i1@2$0^i1\3x23^i1@2$0^i1\3x24^i1@2$0^i1\3x25^i1@2$0^i1\3x26^i1@2$0^i1\3x27^i1@2$0^i1\3x28^i1@2$0^i1\3x29^i1@2$0^i1\3x30^i1@he^i1^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 P G. intros K [x h]. exact (ex_elimF29 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 (P x) G (K x) h). Qed.
Lemma ex_elimF31 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>3T25T>3T26T>3T27T>3T28T>3T29T>3T30T>3T31T>1P>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hfP>1GP>0>2x1^i1>2x2^i1>2x3^i1>2x4^i1>2x5^i1>2x6^i1>2x7^i1>2x8^i1>2x9^i1>3x10^i1>3x11^i1>3x12^i1>3x13^i1>3x14^i1>3x15^i1>3x16^i1>3x17^i1>3x18^i1>3x19^i1>3x20^i1>3x21^i1>3x22^i1>3x23^i1>3x24^i1>3x25^i1>3x26^i1>3x27^i1>3x28^i1>3x29^i1>3x30^i1>3x31^i1>0@hf^i1^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^i1>0@2$0^i2\2x1^i2@2$0^i2\2x2^i2@2$0^i2\2x3^i2@2$0^i2\2x4^i2@2$0^i2\2x5^i2@2$0^i2\2x6^i2@2$0^i2\2x7^i2@2$0^i2\2x8^i2@2$0^i2\2x9^i2@2$0^i2\3x10^i2@2$0^i2\3x11^i2@2$0^i2\3x12^i2@2$0^i2\3x13^i2@2$0^i2\3x14^i2@2$0^i2\3x15^i2@2$0^i2\3x16^i2@2$0^i2\3x17^i2@2$0^i2\3x18^i2@2$0^i2\3x19^i2@2$0^i2\3x20^i2@2$0^i2\3x21^i2@2$0^i2\3x22^i2@2$0^i2\3x23^i2@2$0^i2\3x24^i2@2$0^i2\3x25^i2@2$0^i2\3x26^i2@2$0^i2\3x27^i2@2$0^i2\3x28^i2@2$0^i2\3x29^i2@2$0^i2\3x30^i2@2$0^i2\3x31^i2@hf^i2^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 P G. intros K [x h]. exact (ex_elimF30 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 (P x) G (K x) h). Qed.
Lemma ex_elimF32 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>3T25T>3T26T>3T27T>3T28T>3T29T>3T30T>3T31T>3T32T>1P>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0P>1GP>0>2x1^i2>2x2^i2>2x3^i2>2x4^i2>2x5^i2>2x6^i2>2x7^i2>2x8^i2>2x9^i2>3x10^i2>3x11^i2>3x12^i2>3x13^i2>3x14^i2>3x15^i2>3x16^i2>3x17^i2>3x18^i2>3x19^i2>3x20^i2>3x21^i2>3x22^i2>3x23^i2>3x24^i2>3x25^i2>3x26^i2>3x27^i2>3x28^i2>3x29^i2>3x30^i2>3x31^i2>3x32^i2>0@i0^i2^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^i2>0@2$0^i3\2x1^i3@2$0^i3\2x2^i3@2$0^i3\2x3^i3@2$0^i3\2x4^i3@2$0^i3\2x5^i3@2$0^i3\2x6^i3@2$0^i3\2x7^i3@2$0^i3\2x8^i3@2$0^i3\2x9^i3@2$0^i3\3x10^i3@2$0^i3\3x11^i3@2$0^i3\3x12^i3@2$0^i3\3x13^i3@2$0^i3\3x14^i3@2$0^i3\3x15^i3@2$0^i3\3x16^i3@2$0^i3\3x17^i3@2$0^i3\3x18^i3@2$0^i3\3x19^i3@2$0^i3\3x20^i3@2$0^i3\3x21^i3@2$0^i3\3x22^i3@2$0^i3\3x23^i3@2$0^i3\3x24^i3@2$0^i3\3x25^i3@2$0^i3\3x26^i3@2$0^i3\3x27^i3@2$0^i3\3x28^i3@2$0^i3\3x29^i3@2$0^i3\3x30^i3@2$0^i3\3x31^i3@2$0^i3\3x32^i3@i0^i3^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 P G. intros K [x h]. exact (ex_elimF31 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 (P x) G (K x) h). Qed.
Lemma ex_elimF33 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>3T25T>3T26T>3T27T>3T28T>3T29T>3T30T>3T31T>3T32T>3T33T>1P>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1P>1GP>0>2x1^i3>2x2^i3>2x3^i3>2x4^i3>2x5^i3>2x6^i3>2x7^i3>2x8^i3>2x9^i3>3x10^i3>3x11^i3>3x12^i3>3x13^i3>3x14^i3>3x15^i3>3x16^i3>3x17^i3>3x18^i3>3x19^i3>3x20^i3>3x21^i3>3x22^i3>3x23^i3>3x24^i3>3x25^i3>3x26^i3>3x27^i3>3x28^i3>3x29^i3>3x30^i3>3x31^i3>3x32^i3>3x33^i3>0@i1^i3^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^i3>0@2$0^i4\2x1^i4@2$0^i4\2x2^i4@2$0^i4\2x3^i4@2$0^i4\2x4^i4@2$0^i4\2x5^i4@2$0^i4\2x6^i4@2$0^i4\2x7^i4@2$0^i4\2x8^i4@2$0^i4\2x9^i4@2$0^i4\3x10^i4@2$0^i4\3x11^i4@2$0^i4\3x12^i4@2$0^i4\3x13^i4@2$0^i4\3x14^i4@2$0^i4\3x15^i4@2$0^i4\3x16^i4@2$0^i4\3x17^i4@2$0^i4\3x18^i4@2$0^i4\3x19^i4@2$0^i4\3x20^i4@2$0^i4\3x21^i4@2$0^i4\3x22^i4@2$0^i4\3x23^i4@2$0^i4\3x24^i4@2$0^i4\3x25^i4@2$0^i4\3x26^i4@2$0^i4\3x27^i4@2$0^i4\3x28^i4@2$0^i4\3x29^i4@2$0^i4\3x30^i4@2$0^i4\3x31^i4@2$0^i4\3x32^i4@2$0^i4\3x33^i4@i1^i4^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 P G. intros K [x h]. exact (ex_elimF32 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 (P x) G (K x) h). Qed.
Lemma ex_elimF34 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>3T25T>3T26T>3T27T>3T28T>3T29T>3T30T>3T31T>3T32T>3T33T>3T34T>1P>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2P>1GP>0>2x1^i4>2x2^i4>2x3^i4>2x4^i4>2x5^i4>2x6^i4>2x7^i4>2x8^i4>2x9^i4>3x10^i4>3x11^i4>3x12^i4>3x13^i4>3x14^i4>3x15^i4>3x16^i4>3x17^i4>3x18^i4>3x19^i4>3x20^i4>3x21^i4>3x22^i4>3x23^i4>3x24^i4>3x25^i4>3x26^i4>3x27^i4>3x28^i4>3x29^i4>3x30^i4>3x31^i4>3x32^i4>3x33^i4>3x34^i4>0@i2^i4^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^i4>0@2$0^i5\2x1^i5@2$0^i5\2x2^i5@2$0^i5\2x3^i5@2$0^i5\2x4^i5@2$0^i5\2x5^i5@2$0^i5\2x6^i5@2$0^i5\2x7^i5@2$0^i5\2x8^i5@2$0^i5\2x9^i5@2$0^i5\3x10^i5@2$0^i5\3x11^i5@2$0^i5\3x12^i5@2$0^i5\3x13^i5@2$0^i5\3x14^i5@2$0^i5\3x15^i5@2$0^i5\3x16^i5@2$0^i5\3x17^i5@2$0^i5\3x18^i5@2$0^i5\3x19^i5@2$0^i5\3x20^i5@2$0^i5\3x21^i5@2$0^i5\3x22^i5@2$0^i5\3x23^i5@2$0^i5\3x24^i5@2$0^i5\3x25^i5@2$0^i5\3x26^i5@2$0^i5\3x27^i5@2$0^i5\3x28^i5@2$0^i5\3x29^i5@2$0^i5\3x30^i5@2$0^i5\3x31^i5@2$0^i5\3x32^i5@2$0^i5\3x33^i5@2$0^i5\3x34^i5@i2^i5^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 P G. intros K [x h]. exact (ex_elimF33 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 (P x) G (K x) h). Qed.
Lemma ex_elimF35 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>3T25T>3T26T>3T27T>3T28T>3T29T>3T30T>3T31T>3T32T>3T33T>3T34T>3T35T>1P>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3P>1GP>0>2x1^i5>2x2^i5>2x3^i5>2x4^i5>2x5^i5>2x6^i5>2x7^i5>2x8^i5>2x9^i5>3x10^i5>3x11^i5>3x12^i5>3x13^i5>3x14^i5>3x15^i5>3x16^i5>3x17^i5>3x18^i5>3x19^i5>3x20^i5>3x21^i5>3x22^i5>3x23^i5>3x24^i5>3x25^i5>3x26^i5>3x27^i5>3x28^i5>3x29^i5>3x30^i5>3x31^i5>3x32^i5>3x33^i5>3x34^i5>3x35^i5>0@i3^i5^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^i5>0@2$0^i6\2x1^i6@2$0^i6\2x2^i6@2$0^i6\2x3^i6@2$0^i6\2x4^i6@2$0^i6\2x5^i6@2$0^i6\2x6^i6@2$0^i6\2x7^i6@2$0^i6\2x8^i6@2$0^i6\2x9^i6@2$0^i6\3x10^i6@2$0^i6\3x11^i6@2$0^i6\3x12^i6@2$0^i6\3x13^i6@2$0^i6\3x14^i6@2$0^i6\3x15^i6@2$0^i6\3x16^i6@2$0^i6\3x17^i6@2$0^i6\3x18^i6@2$0^i6\3x19^i6@2$0^i6\3x20^i6@2$0^i6\3x21^i6@2$0^i6\3x22^i6@2$0^i6\3x23^i6@2$0^i6\3x24^i6@2$0^i6\3x25^i6@2$0^i6\3x26^i6@2$0^i6\3x27^i6@2$0^i6\3x28^i6@2$0^i6\3x29^i6@2$0^i6\3x30^i6@2$0^i6\3x31^i6@2$0^i6\3x32^i6@2$0^i6\3x33^i6@2$0^i6\3x34^i6@2$0^i6\3x35^i6@i3^i6^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 P G. intros K [x h]. exact (ex_elimF34 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 (P x) G (K x) h). Qed.
Lemma ex_elimF36 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>3T25T>3T26T>3T27T>3T28T>3T29T>3T30T>3T31T>3T32T>3T33T>3T34T>3T35T>3T36T>1P>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4P>1GP>0>2x1^i6>2x2^i6>2x3^i6>2x4^i6>2x5^i6>2x6^i6>2x7^i6>2x8^i6>2x9^i6>3x10^i6>3x11^i6>3x12^i6>3x13^i6>3x14^i6>3x15^i6>3x16^i6>3x17^i6>3x18^i6>3x19^i6>3x20^i6>3x21^i6>3x22^i6>3x23^i6>3x24^i6>3x25^i6>3x26^i6>3x27^i6>3x28^i6>3x29^i6>3x30^i6>3x31^i6>3x32^i6>3x33^i6>3x34^i6>3x35^i6>3x36^i6>0@i4^i6^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^i6>0@2$0^i7\2x1^i7@2$0^i7\2x2^i7@2$0^i7\2x3^i7@2$0^i7\2x4^i7@2$0^i7\2x5^i7@2$0^i7\2x6^i7@2$0^i7\2x7^i7@2$0^i7\2x8^i7@2$0^i7\2x9^i7@2$0^i7\3x10^i7@2$0^i7\3x11^i7@2$0^i7\3x12^i7@2$0^i7\3x13^i7@2$0^i7\3x14^i7@2$0^i7\3x15^i7@2$0^i7\3x16^i7@2$0^i7\3x17^i7@2$0^i7\3x18^i7@2$0^i7\3x19^i7@2$0^i7\3x20^i7@2$0^i7\3x21^i7@2$0^i7\3x22^i7@2$0^i7\3x23^i7@2$0^i7\3x24^i7@2$0^i7\3x25^i7@2$0^i7\3x26^i7@2$0^i7\3x27^i7@2$0^i7\3x28^i7@2$0^i7\3x29^i7@2$0^i7\3x30^i7@2$0^i7\3x31^i7@2$0^i7\3x32^i7@2$0^i7\3x33^i7@2$0^i7\3x34^i7@2$0^i7\3x35^i7@2$0^i7\3x36^i7@i4^i7^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 P G. intros K [x h]. exact (ex_elimF35 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 (P x) G (K x) h). Qed.
Lemma ex_elimF37 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>3T25T>3T26T>3T27T>3T28T>3T29T>3T30T>3T31T>3T32T>3T33T>3T34T>3T35T>3T36T>3T37T>1P>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5P>1GP>0>2x1^i7>2x2^i7>2x3^i7>2x4^i7>2x5^i7>2x6^i7>2x7^i7>2x8^i7>2x9^i7>3x10^i7>3x11^i7>3x12^i7>3x13^i7>3x14^i7>3x15^i7>3x16^i7>3x17^i7>3x18^i7>3x19^i7>3x20^i7>3x21^i7>3x22^i7>3x23^i7>3x24^i7>3x25^i7>3x26^i7>3x27^i7>3x28^i7>3x29^i7>3x30^i7>3x31^i7>3x32^i7>3x33^i7>3x34^i7>3x35^i7>3x36^i7>3x37^i7>0@i5^i7^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^i7>0@2$0^i8\2x1^i8@2$0^i8\2x2^i8@2$0^i8\2x3^i8@2$0^i8\2x4^i8@2$0^i8\2x5^i8@2$0^i8\2x6^i8@2$0^i8\2x7^i8@2$0^i8\2x8^i8@2$0^i8\2x9^i8@2$0^i8\3x10^i8@2$0^i8\3x11^i8@2$0^i8\3x12^i8@2$0^i8\3x13^i8@2$0^i8\3x14^i8@2$0^i8\3x15^i8@2$0^i8\3x16^i8@2$0^i8\3x17^i8@2$0^i8\3x18^i8@2$0^i8\3x19^i8@2$0^i8\3x20^i8@2$0^i8\3x21^i8@2$0^i8\3x22^i8@2$0^i8\3x23^i8@2$0^i8\3x24^i8@2$0^i8\3x25^i8@2$0^i8\3x26^i8@2$0^i8\3x27^i8@2$0^i8\3x28^i8@2$0^i8\3x29^i8@2$0^i8\3x30^i8@2$0^i8\3x31^i8@2$0^i8\3x32^i8@2$0^i8\3x33^i8@2$0^i8\3x34^i8@2$0^i8\3x35^i8@2$0^i8\3x36^i8@2$0^i8\3x37^i8@i5^i8^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 P G. intros K [x h]. exact (ex_elimF36 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 (P x) G (K x) h). Qed.
Lemma ex_elimF38 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>3T25T>3T26T>3T27T>3T28T>3T29T>3T30T>3T31T>3T32T>3T33T>3T34T>3T35T>3T36T>3T37T>3T38T>1P>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6P>1GP>0>2x1^i8>2x2^i8>2x3^i8>2x4^i8>2x5^i8>2x6^i8>2x7^i8>2x8^i8>2x9^i8>3x10^i8>3x11^i8>3x12^i8>3x13^i8>3x14^i8>3x15^i8>3x16^i8>3x17^i8>3x18^i8>3x19^i8>3x20^i8>3x21^i8>3x22^i8>3x23^i8>3x24^i8>3x25^i8>3x26^i8>3x27^i8>3x28^i8>3x29^i8>3x30^i8>3x31^i8>3x32^i8>3x33^i8>3x34^i8>3x35^i8>3x36^i8>3x37^i8>3x38^i8>0@i6^i8^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^i8>0@2$0^i9\2x1^i9@2$0^i9\2x2^i9@2$0^i9\2x3^i9@2$0^i9\2x4^i9@2$0^i9\2x5^i9@2$0^i9\2x6^i9@2$0^i9\2x7^i9@2$0^i9\2x8^i9@2$0^i9\2x9^i9@2$0^i9\3x10^i9@2$0^i9\3x11^i9@2$0^i9\3x12^i9@2$0^i9\3x13^i9@2$0^i9\3x14^i9@2$0^i9\3x15^i9@2$0^i9\3x16^i9@2$0^i9\3x17^i9@2$0^i9\3x18^i9@2$0^i9\3x19^i9@2$0^i9\3x20^i9@2$0^i9\3x21^i9@2$0^i9\3x22^i9@2$0^i9\3x23^i9@2$0^i9\3x24^i9@2$0^i9\3x25^i9@2$0^i9\3x26^i9@2$0^i9\3x27^i9@2$0^i9\3x28^i9@2$0^i9\3x29^i9@2$0^i9\3x30^i9@2$0^i9\3x31^i9@2$0^i9\3x32^i9@2$0^i9\3x33^i9@2$0^i9\3x34^i9@2$0^i9\3x35^i9@2$0^i9\3x36^i9@2$0^i9\3x37^i9@2$0^i9\3x38^i9@i6^i9^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 P G. intros K [x h]. exact (ex_elimF37 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 (P x) G (K x) h). Qed.
Lemma ex_elimF39 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>3T25T>3T26T>3T27T>3T28T>3T29T>3T30T>3T31T>3T32T>3T33T>3T34T>3T35T>3T36T>3T37T>3T38T>3T39T>1P>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7P>1GP>0>2x1^i9>2x2^i9>2x3^i9>2x4^i9>2x5^i9>2x6^i9>2x7^i9>2x8^i9>2x9^i9>3x10^i9>3x11^i9>3x12^i9>3x13^i9>3x14^i9>3x15^i9>3x16^i9>3x17^i9>3x18^i9>3x19^i9>3x20^i9>3x21^i9>3x22^i9>3x23^i9>3x24^i9>3x25^i9>3x26^i9>3x27^i9>3x28^i9>3x29^i9>3x30^i9>3x31^i9>3x32^i9>3x33^i9>3x34^i9>3x35^i9>3x36^i9>3x37^i9>3x38^i9>3x39^i9>0@i7^i9^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^i9>0@2$0^ia\2x1^ia@2$0^ia\2x2^ia@2$0^ia\2x3^ia@2$0^ia\2x4^ia@2$0^ia\2x5^ia@2$0^ia\2x6^ia@2$0^ia\2x7^ia@2$0^ia\2x8^ia@2$0^ia\2x9^ia@2$0^ia\3x10^ia@2$0^ia\3x11^ia@2$0^ia\3x12^ia@2$0^ia\3x13^ia@2$0^ia\3x14^ia@2$0^ia\3x15^ia@2$0^ia\3x16^ia@2$0^ia\3x17^ia@2$0^ia\3x18^ia@2$0^ia\3x19^ia@2$0^ia\3x20^ia@2$0^ia\3x21^ia@2$0^ia\3x22^ia@2$0^ia\3x23^ia@2$0^ia\3x24^ia@2$0^ia\3x25^ia@2$0^ia\3x26^ia@2$0^ia\3x27^ia@2$0^ia\3x28^ia@2$0^ia\3x29^ia@2$0^ia\3x30^ia@2$0^ia\3x31^ia@2$0^ia\3x32^ia@2$0^ia\3x33^ia@2$0^ia\3x34^ia@2$0^ia\3x35^ia@2$0^ia\3x36^ia@2$0^ia\3x37^ia@2$0^ia\3x38^ia@2$0^ia\3x39^ia@i7^ia^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 P G. intros K [x h]. exact (ex_elimF38 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 (P x) G (K x) h). Qed.
Lemma ex_elimF40 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>3T25T>3T26T>3T27T>3T28T>3T29T>3T30T>3T31T>3T32T>3T33T>3T34T>3T35T>3T36T>3T37T>3T38T>3T39T>3T40T>1P>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8P>1GP>0>2x1^ia>2x2^ia>2x3^ia>2x4^ia>2x5^ia>2x6^ia>2x7^ia>2x8^ia>2x9^ia>3x10^ia>3x11^ia>3x12^ia>3x13^ia>3x14^ia>3x15^ia>3x16^ia>3x17^ia>3x18^ia>3x19^ia>3x20^ia>3x21^ia>3x22^ia>3x23^ia>3x24^ia>3x25^ia>3x26^ia>3x27^ia>3x28^ia>3x29^ia>3x30^ia>3x31^ia>3x32^ia>3x33^ia>3x34^ia>3x35^ia>3x36^ia>3x37^ia>3x38^ia>3x39^ia>3x40^ia>0@i8^ia^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^ia>0@2$0^ib\2x1^ib@2$0^ib\2x2^ib@2$0^ib\2x3^ib@2$0^ib\2x4^ib@2$0^ib\2x5^ib@2$0^ib\2x6^ib@2$0^ib\2x7^ib@2$0^ib\2x8^ib@2$0^ib\2x9^ib@2$0^ib\3x10^ib@2$0^ib\3x11^ib@2$0^ib\3x12^ib@2$0^ib\3x13^ib@2$0^ib\3x14^ib@2$0^ib\3x15^ib@2$0^ib\3x16^ib@2$0^ib\3x17^ib@2$0^ib\3x18^ib@2$0^ib\3x19^ib@2$0^ib\3x20^ib@2$0^ib\3x21^ib@2$0^ib\3x22^ib@2$0^ib\3x23^ib@2$0^ib\3x24^ib@2$0^ib\3x25^ib@2$0^ib\3x26^ib@2$0^ib\3x27^ib@2$0^ib\3x28^ib@2$0^ib\3x29^ib@2$0^ib\3x30^ib@2$0^ib\3x31^ib@2$0^ib\3x32^ib@2$0^ib\3x33^ib@2$0^ib\3x34^ib@2$0^ib\3x35^ib@2$0^ib\3x36^ib@2$0^ib\3x37^ib@2$0^ib\3x38^ib@2$0^ib\3x39^ib@2$0^ib\3x40^ib@i8^ib^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^3").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 P G. intros K [x h]. exact (ex_elimF39 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 (P x) G (K x) h). Qed.

(* [comment removed for export] *)
Lemma ex_introF1 : ltac2:(zQ "10!h9>2T1T>1P>0^1P>2x1^2>0@1^2^1@2$0^4\2x1^4@1^4^1").
Proof. intros T1 P x1. intros H. exact (ex_intro _ x1 H). Qed.
Lemma ex_introF2 : ltac2:(zQ "10!h9>2T1T>2T2T>1P>0^2>0^2P>2x1^3>2x2^3>0@2^3^2^1@2$0^6\2x1^6@2$0^6\2x2^6@2^6^2^1").
Proof. intros T1 T2 P x1 x2. intros H. exact (ex_intro _ x1 (ex_introF1 T2 (P x1) x2 H)). Qed.
Lemma ex_introF3 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>1P>0^3>0^3>0^3P>2x1^4>2x2^4>2x3^4>0@3^4^3^2^1@2$0^8\2x1^8@2$0^8\2x2^8@2$0^8\2x3^8@3^8^3^2^1").
Proof. intros T1 T2 T3 P x1 x2 x3. intros H. exact (ex_intro _ x1 (ex_introF2 T2 T3 (P x1) x2 x3 H)). Qed.
Lemma ex_introF4 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>1P>0^4>0^4>0^4>0^4P>2x1^5>2x2^5>2x3^5>2x4^5>0@4^5^4^3^2^1@2$0^a\2x1^a@2$0^a\2x2^a@2$0^a\2x3^a@2$0^a\2x4^a@4^a^4^3^2^1").
Proof. intros T1 T2 T3 T4 P x1 x2 x3 x4. intros H. exact (ex_intro _ x1 (ex_introF3 T2 T3 T4 (P x1) x2 x3 x4 H)). Qed.
Lemma ex_introF5 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>1P>0^5>0^5>0^5>0^5>0^5P>2x1^6>2x2^6>2x3^6>2x4^6>2x5^6>0@5^6^5^4^3^2^1@2$0^c\2x1^c@2$0^c\2x2^c@2$0^c\2x3^c@2$0^c\2x4^c@2$0^c\2x5^c@5^c^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 P x1 x2 x3 x4 x5. intros H. exact (ex_intro _ x1 (ex_introF4 T2 T3 T4 T5 (P x1) x2 x3 x4 x5 H)). Qed.
Lemma ex_introF6 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>1P>0^6>0^6>0^6>0^6>0^6>0^6P>2x1^7>2x2^7>2x3^7>2x4^7>2x5^7>2x6^7>0@6^7^6^5^4^3^2^1@2$0^e\2x1^e@2$0^e\2x2^e@2$0^e\2x3^e@2$0^e\2x4^e@2$0^e\2x5^e@2$0^e\2x6^e@6^e^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 P x1 x2 x3 x4 x5 x6. intros H. exact (ex_intro _ x1 (ex_introF5 T2 T3 T4 T5 T6 (P x1) x2 x3 x4 x5 x6 H)). Qed.
Lemma ex_introF7 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>1P>0^7>0^7>0^7>0^7>0^7>0^7>0^7P>2x1^8>2x2^8>2x3^8>2x4^8>2x5^8>2x6^8>2x7^8>0@7^8^7^6^5^4^3^2^1@2$0^h0\2x1^h0@2$0^h0\2x2^h0@2$0^h0\2x3^h0@2$0^h0\2x4^h0@2$0^h0\2x5^h0@2$0^h0\2x6^h0@2$0^h0\2x7^h0@7^h0^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 P x1 x2 x3 x4 x5 x6 x7. intros H. exact (ex_intro _ x1 (ex_introF6 T2 T3 T4 T5 T6 T7 (P x1) x2 x3 x4 x5 x6 x7 H)). Qed.
Lemma ex_introF8 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>1P>0^8>0^8>0^8>0^8>0^8>0^8>0^8>0^8P>2x1^9>2x2^9>2x3^9>2x4^9>2x5^9>2x6^9>2x7^9>2x8^9>0@8^9^8^7^6^5^4^3^2^1@2$0^h2\2x1^h2@2$0^h2\2x2^h2@2$0^h2\2x3^h2@2$0^h2\2x4^h2@2$0^h2\2x5^h2@2$0^h2\2x6^h2@2$0^h2\2x7^h2@2$0^h2\2x8^h2@8^h2^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 P x1 x2 x3 x4 x5 x6 x7 x8. intros H. exact (ex_intro _ x1 (ex_introF7 T2 T3 T4 T5 T6 T7 T8 (P x1) x2 x3 x4 x5 x6 x7 x8 H)). Qed.
Lemma ex_introF9 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>1P>0^9>0^9>0^9>0^9>0^9>0^9>0^9>0^9>0^9P>2x1^a>2x2^a>2x3^a>2x4^a>2x5^a>2x6^a>2x7^a>2x8^a>2x9^a>0@9^a^9^8^7^6^5^4^3^2^1@2$0^h4\2x1^h4@2$0^h4\2x2^h4@2$0^h4\2x3^h4@2$0^h4\2x4^h4@2$0^h4\2x5^h4@2$0^h4\2x6^h4@2$0^h4\2x7^h4@2$0^h4\2x8^h4@2$0^h4\2x9^h4@9^h4^9^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 P x1 x2 x3 x4 x5 x6 x7 x8 x9. intros H. exact (ex_intro _ x1 (ex_introF8 T2 T3 T4 T5 T6 T7 T8 T9 (P x1) x2 x3 x4 x5 x6 x7 x8 x9 H)). Qed.
Lemma ex_introF10 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>1P>0^a>0^a>0^a>0^a>0^a>0^a>0^a>0^a>0^a>0^aP>2x1^b>2x2^b>2x3^b>2x4^b>2x5^b>2x6^b>2x7^b>2x8^b>2x9^b>3x10^b>0@a^b^a^9^8^7^6^5^4^3^2^1@2$0^h6\2x1^h6@2$0^h6\2x2^h6@2$0^h6\2x3^h6@2$0^h6\2x4^h6@2$0^h6\2x5^h6@2$0^h6\2x6^h6@2$0^h6\2x7^h6@2$0^h6\2x8^h6@2$0^h6\2x9^h6@2$0^h6\3x10^h6@a^h6^a^9^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10. intros H. exact (ex_intro _ x1 (ex_introF9 T2 T3 T4 T5 T6 T7 T8 T9 T10 (P x1) x2 x3 x4 x5 x6 x7 x8 x9 x10 H)). Qed.
Lemma ex_introF11 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>1P>0^b>0^b>0^b>0^b>0^b>0^b>0^b>0^b>0^b>0^b>0^bP>2x1^c>2x2^c>2x3^c>2x4^c>2x5^c>2x6^c>2x7^c>2x8^c>2x9^c>3x10^c>3x11^c>0@b^c^b^a^9^8^7^6^5^4^3^2^1@2$0^h8\2x1^h8@2$0^h8\2x2^h8@2$0^h8\2x3^h8@2$0^h8\2x4^h8@2$0^h8\2x5^h8@2$0^h8\2x6^h8@2$0^h8\2x7^h8@2$0^h8\2x8^h8@2$0^h8\2x9^h8@2$0^h8\3x10^h8@2$0^h8\3x11^h8@b^h8^b^a^9^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11. intros H. exact (ex_intro _ x1 (ex_introF10 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 (P x1) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 H)). Qed.
Lemma ex_introF12 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>1P>0^c>0^c>0^c>0^c>0^c>0^c>0^c>0^c>0^c>0^c>0^c>0^cP>2x1^d>2x2^d>2x3^d>2x4^d>2x5^d>2x6^d>2x7^d>2x8^d>2x9^d>3x10^d>3x11^d>3x12^d>0@c^d^c^b^a^9^8^7^6^5^4^3^2^1@2$0^ha\2x1^ha@2$0^ha\2x2^ha@2$0^ha\2x3^ha@2$0^ha\2x4^ha@2$0^ha\2x5^ha@2$0^ha\2x6^ha@2$0^ha\2x7^ha@2$0^ha\2x8^ha@2$0^ha\2x9^ha@2$0^ha\3x10^ha@2$0^ha\3x11^ha@2$0^ha\3x12^ha@c^ha^c^b^a^9^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12. intros H. exact (ex_intro _ x1 (ex_introF11 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 (P x1) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 H)). Qed.
Lemma ex_introF13 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>1P>0^d>0^d>0^d>0^d>0^d>0^d>0^d>0^d>0^d>0^d>0^d>0^d>0^dP>2x1^e>2x2^e>2x3^e>2x4^e>2x5^e>2x6^e>2x7^e>2x8^e>2x9^e>3x10^e>3x11^e>3x12^e>3x13^e>0@d^e^d^c^b^a^9^8^7^6^5^4^3^2^1@2$0^hc\2x1^hc@2$0^hc\2x2^hc@2$0^hc\2x3^hc@2$0^hc\2x4^hc@2$0^hc\2x5^hc@2$0^hc\2x6^hc@2$0^hc\2x7^hc@2$0^hc\2x8^hc@2$0^hc\2x9^hc@2$0^hc\3x10^hc@2$0^hc\3x11^hc@2$0^hc\3x12^hc@2$0^hc\3x13^hc@d^hc^d^c^b^a^9^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13. intros H. exact (ex_intro _ x1 (ex_introF12 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 (P x1) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 H)). Qed.
Lemma ex_introF14 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>1P>0^e>0^e>0^e>0^e>0^e>0^e>0^e>0^e>0^e>0^e>0^e>0^e>0^e>0^eP>2x1^f>2x2^f>2x3^f>2x4^f>2x5^f>2x6^f>2x7^f>2x8^f>2x9^f>3x10^f>3x11^f>3x12^f>3x13^f>3x14^f>0@e^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1@2$0^he\2x1^he@2$0^he\2x2^he@2$0^he\2x3^he@2$0^he\2x4^he@2$0^he\2x5^he@2$0^he\2x6^he@2$0^he\2x7^he@2$0^he\2x8^he@2$0^he\2x9^he@2$0^he\3x10^he@2$0^he\3x11^he@2$0^he\3x12^he@2$0^he\3x13^he@2$0^he\3x14^he@e^he^e^d^c^b^a^9^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14. intros H. exact (ex_intro _ x1 (ex_introF13 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 (P x1) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 H)). Qed.
Lemma ex_introF15 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>1P>0^f>0^f>0^f>0^f>0^f>0^f>0^f>0^f>0^f>0^f>0^f>0^f>0^f>0^f>0^fP>2x1^h0>2x2^h0>2x3^h0>2x4^h0>2x5^h0>2x6^h0>2x7^h0>2x8^h0>2x9^h0>3x10^h0>3x11^h0>3x12^h0>3x13^h0>3x14^h0>3x15^h0>0@f^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1@2$0^i0\2x1^i0@2$0^i0\2x2^i0@2$0^i0\2x3^i0@2$0^i0\2x4^i0@2$0^i0\2x5^i0@2$0^i0\2x6^i0@2$0^i0\2x7^i0@2$0^i0\2x8^i0@2$0^i0\2x9^i0@2$0^i0\3x10^i0@2$0^i0\3x11^i0@2$0^i0\3x12^i0@2$0^i0\3x13^i0@2$0^i0\3x14^i0@2$0^i0\3x15^i0@f^i0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15. intros H. exact (ex_intro _ x1 (ex_introF14 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 (P x1) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 H)). Qed.
Lemma ex_introF16 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>1P>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0P>2x1^h1>2x2^h1>2x3^h1>2x4^h1>2x5^h1>2x6^h1>2x7^h1>2x8^h1>2x9^h1>3x10^h1>3x11^h1>3x12^h1>3x13^h1>3x14^h1>3x15^h1>3x16^h1>0@h0^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1@2$0^i2\2x1^i2@2$0^i2\2x2^i2@2$0^i2\2x3^i2@2$0^i2\2x4^i2@2$0^i2\2x5^i2@2$0^i2\2x6^i2@2$0^i2\2x7^i2@2$0^i2\2x8^i2@2$0^i2\2x9^i2@2$0^i2\3x10^i2@2$0^i2\3x11^i2@2$0^i2\3x12^i2@2$0^i2\3x13^i2@2$0^i2\3x14^i2@2$0^i2\3x15^i2@2$0^i2\3x16^i2@h0^i2^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16. intros H. exact (ex_intro _ x1 (ex_introF15 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 (P x1) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 H)). Qed.
Lemma ex_introF17 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>1P>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1P>2x1^h2>2x2^h2>2x3^h2>2x4^h2>2x5^h2>2x6^h2>2x7^h2>2x8^h2>2x9^h2>3x10^h2>3x11^h2>3x12^h2>3x13^h2>3x14^h2>3x15^h2>3x16^h2>3x17^h2>0@h1^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1@2$0^i4\2x1^i4@2$0^i4\2x2^i4@2$0^i4\2x3^i4@2$0^i4\2x4^i4@2$0^i4\2x5^i4@2$0^i4\2x6^i4@2$0^i4\2x7^i4@2$0^i4\2x8^i4@2$0^i4\2x9^i4@2$0^i4\3x10^i4@2$0^i4\3x11^i4@2$0^i4\3x12^i4@2$0^i4\3x13^i4@2$0^i4\3x14^i4@2$0^i4\3x15^i4@2$0^i4\3x16^i4@2$0^i4\3x17^i4@h1^i4^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17. intros H. exact (ex_intro _ x1 (ex_introF16 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 (P x1) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 H)). Qed.
Lemma ex_introF18 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>1P>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2P>2x1^h3>2x2^h3>2x3^h3>2x4^h3>2x5^h3>2x6^h3>2x7^h3>2x8^h3>2x9^h3>3x10^h3>3x11^h3>3x12^h3>3x13^h3>3x14^h3>3x15^h3>3x16^h3>3x17^h3>3x18^h3>0@h2^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1@2$0^i6\2x1^i6@2$0^i6\2x2^i6@2$0^i6\2x3^i6@2$0^i6\2x4^i6@2$0^i6\2x5^i6@2$0^i6\2x6^i6@2$0^i6\2x7^i6@2$0^i6\2x8^i6@2$0^i6\2x9^i6@2$0^i6\3x10^i6@2$0^i6\3x11^i6@2$0^i6\3x12^i6@2$0^i6\3x13^i6@2$0^i6\3x14^i6@2$0^i6\3x15^i6@2$0^i6\3x16^i6@2$0^i6\3x17^i6@2$0^i6\3x18^i6@h2^i6^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18. intros H. exact (ex_intro _ x1 (ex_introF17 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 (P x1) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 H)). Qed.
Lemma ex_introF19 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>1P>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3P>2x1^h4>2x2^h4>2x3^h4>2x4^h4>2x5^h4>2x6^h4>2x7^h4>2x8^h4>2x9^h4>3x10^h4>3x11^h4>3x12^h4>3x13^h4>3x14^h4>3x15^h4>3x16^h4>3x17^h4>3x18^h4>3x19^h4>0@h3^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1@2$0^i8\2x1^i8@2$0^i8\2x2^i8@2$0^i8\2x3^i8@2$0^i8\2x4^i8@2$0^i8\2x5^i8@2$0^i8\2x6^i8@2$0^i8\2x7^i8@2$0^i8\2x8^i8@2$0^i8\2x9^i8@2$0^i8\3x10^i8@2$0^i8\3x11^i8@2$0^i8\3x12^i8@2$0^i8\3x13^i8@2$0^i8\3x14^i8@2$0^i8\3x15^i8@2$0^i8\3x16^i8@2$0^i8\3x17^i8@2$0^i8\3x18^i8@2$0^i8\3x19^i8@h3^i8^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19. intros H. exact (ex_intro _ x1 (ex_introF18 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 (P x1) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 H)). Qed.
Lemma ex_introF20 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>1P>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4P>2x1^h5>2x2^h5>2x3^h5>2x4^h5>2x5^h5>2x6^h5>2x7^h5>2x8^h5>2x9^h5>3x10^h5>3x11^h5>3x12^h5>3x13^h5>3x14^h5>3x15^h5>3x16^h5>3x17^h5>3x18^h5>3x19^h5>3x20^h5>0@h4^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1@2$0^ia\2x1^ia@2$0^ia\2x2^ia@2$0^ia\2x3^ia@2$0^ia\2x4^ia@2$0^ia\2x5^ia@2$0^ia\2x6^ia@2$0^ia\2x7^ia@2$0^ia\2x8^ia@2$0^ia\2x9^ia@2$0^ia\3x10^ia@2$0^ia\3x11^ia@2$0^ia\3x12^ia@2$0^ia\3x13^ia@2$0^ia\3x14^ia@2$0^ia\3x15^ia@2$0^ia\3x16^ia@2$0^ia\3x17^ia@2$0^ia\3x18^ia@2$0^ia\3x19^ia@2$0^ia\3x20^ia@h4^ia^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20. intros H. exact (ex_intro _ x1 (ex_introF19 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 (P x1) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 H)). Qed.
Lemma ex_introF21 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>1P>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5P>2x1^h6>2x2^h6>2x3^h6>2x4^h6>2x5^h6>2x6^h6>2x7^h6>2x8^h6>2x9^h6>3x10^h6>3x11^h6>3x12^h6>3x13^h6>3x14^h6>3x15^h6>3x16^h6>3x17^h6>3x18^h6>3x19^h6>3x20^h6>3x21^h6>0@h5^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1@2$0^ic\2x1^ic@2$0^ic\2x2^ic@2$0^ic\2x3^ic@2$0^ic\2x4^ic@2$0^ic\2x5^ic@2$0^ic\2x6^ic@2$0^ic\2x7^ic@2$0^ic\2x8^ic@2$0^ic\2x9^ic@2$0^ic\3x10^ic@2$0^ic\3x11^ic@2$0^ic\3x12^ic@2$0^ic\3x13^ic@2$0^ic\3x14^ic@2$0^ic\3x15^ic@2$0^ic\3x16^ic@2$0^ic\3x17^ic@2$0^ic\3x18^ic@2$0^ic\3x19^ic@2$0^ic\3x20^ic@2$0^ic\3x21^ic@h5^ic^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21. intros H. exact (ex_intro _ x1 (ex_introF20 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 (P x1) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 H)). Qed.
Lemma ex_introF22 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>1P>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6P>2x1^h7>2x2^h7>2x3^h7>2x4^h7>2x5^h7>2x6^h7>2x7^h7>2x8^h7>2x9^h7>3x10^h7>3x11^h7>3x12^h7>3x13^h7>3x14^h7>3x15^h7>3x16^h7>3x17^h7>3x18^h7>3x19^h7>3x20^h7>3x21^h7>3x22^h7>0@h6^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1@2$0^ie\2x1^ie@2$0^ie\2x2^ie@2$0^ie\2x3^ie@2$0^ie\2x4^ie@2$0^ie\2x5^ie@2$0^ie\2x6^ie@2$0^ie\2x7^ie@2$0^ie\2x8^ie@2$0^ie\2x9^ie@2$0^ie\3x10^ie@2$0^ie\3x11^ie@2$0^ie\3x12^ie@2$0^ie\3x13^ie@2$0^ie\3x14^ie@2$0^ie\3x15^ie@2$0^ie\3x16^ie@2$0^ie\3x17^ie@2$0^ie\3x18^ie@2$0^ie\3x19^ie@2$0^ie\3x20^ie@2$0^ie\3x21^ie@2$0^ie\3x22^ie@h6^ie^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22. intros H. exact (ex_intro _ x1 (ex_introF21 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 (P x1) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 H)). Qed.
Lemma ex_introF23 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>1P>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7P>2x1^h8>2x2^h8>2x3^h8>2x4^h8>2x5^h8>2x6^h8>2x7^h8>2x8^h8>2x9^h8>3x10^h8>3x11^h8>3x12^h8>3x13^h8>3x14^h8>3x15^h8>3x16^h8>3x17^h8>3x18^h8>3x19^h8>3x20^h8>3x21^h8>3x22^h8>3x23^h8>0@h7^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1@2$0^j0\2x1^j0@2$0^j0\2x2^j0@2$0^j0\2x3^j0@2$0^j0\2x4^j0@2$0^j0\2x5^j0@2$0^j0\2x6^j0@2$0^j0\2x7^j0@2$0^j0\2x8^j0@2$0^j0\2x9^j0@2$0^j0\3x10^j0@2$0^j0\3x11^j0@2$0^j0\3x12^j0@2$0^j0\3x13^j0@2$0^j0\3x14^j0@2$0^j0\3x15^j0@2$0^j0\3x16^j0@2$0^j0\3x17^j0@2$0^j0\3x18^j0@2$0^j0\3x19^j0@2$0^j0\3x20^j0@2$0^j0\3x21^j0@2$0^j0\3x22^j0@2$0^j0\3x23^j0@h7^j0^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23. intros H. exact (ex_intro _ x1 (ex_introF22 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 (P x1) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 H)). Qed.
Lemma ex_introF24 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>1P>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8P>2x1^h9>2x2^h9>2x3^h9>2x4^h9>2x5^h9>2x6^h9>2x7^h9>2x8^h9>2x9^h9>3x10^h9>3x11^h9>3x12^h9>3x13^h9>3x14^h9>3x15^h9>3x16^h9>3x17^h9>3x18^h9>3x19^h9>3x20^h9>3x21^h9>3x22^h9>3x23^h9>3x24^h9>0@h8^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1@2$0^j2\2x1^j2@2$0^j2\2x2^j2@2$0^j2\2x3^j2@2$0^j2\2x4^j2@2$0^j2\2x5^j2@2$0^j2\2x6^j2@2$0^j2\2x7^j2@2$0^j2\2x8^j2@2$0^j2\2x9^j2@2$0^j2\3x10^j2@2$0^j2\3x11^j2@2$0^j2\3x12^j2@2$0^j2\3x13^j2@2$0^j2\3x14^j2@2$0^j2\3x15^j2@2$0^j2\3x16^j2@2$0^j2\3x17^j2@2$0^j2\3x18^j2@2$0^j2\3x19^j2@2$0^j2\3x20^j2@2$0^j2\3x21^j2@2$0^j2\3x22^j2@2$0^j2\3x23^j2@2$0^j2\3x24^j2@h8^j2^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24. intros H. exact (ex_intro _ x1 (ex_introF23 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 (P x1) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 H)). Qed.
Lemma ex_introF25 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>3T25T>1P>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9P>2x1^ha>2x2^ha>2x3^ha>2x4^ha>2x5^ha>2x6^ha>2x7^ha>2x8^ha>2x9^ha>3x10^ha>3x11^ha>3x12^ha>3x13^ha>3x14^ha>3x15^ha>3x16^ha>3x17^ha>3x18^ha>3x19^ha>3x20^ha>3x21^ha>3x22^ha>3x23^ha>3x24^ha>3x25^ha>0@h9^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1@2$0^j4\2x1^j4@2$0^j4\2x2^j4@2$0^j4\2x3^j4@2$0^j4\2x4^j4@2$0^j4\2x5^j4@2$0^j4\2x6^j4@2$0^j4\2x7^j4@2$0^j4\2x8^j4@2$0^j4\2x9^j4@2$0^j4\3x10^j4@2$0^j4\3x11^j4@2$0^j4\3x12^j4@2$0^j4\3x13^j4@2$0^j4\3x14^j4@2$0^j4\3x15^j4@2$0^j4\3x16^j4@2$0^j4\3x17^j4@2$0^j4\3x18^j4@2$0^j4\3x19^j4@2$0^j4\3x20^j4@2$0^j4\3x21^j4@2$0^j4\3x22^j4@2$0^j4\3x23^j4@2$0^j4\3x24^j4@2$0^j4\3x25^j4@h9^j4^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25. intros H. exact (ex_intro _ x1 (ex_introF24 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 (P x1) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 H)). Qed.
Lemma ex_introF26 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>3T25T>3T26T>1P>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^haP>2x1^hb>2x2^hb>2x3^hb>2x4^hb>2x5^hb>2x6^hb>2x7^hb>2x8^hb>2x9^hb>3x10^hb>3x11^hb>3x12^hb>3x13^hb>3x14^hb>3x15^hb>3x16^hb>3x17^hb>3x18^hb>3x19^hb>3x20^hb>3x21^hb>3x22^hb>3x23^hb>3x24^hb>3x25^hb>3x26^hb>0@ha^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1@2$0^j6\2x1^j6@2$0^j6\2x2^j6@2$0^j6\2x3^j6@2$0^j6\2x4^j6@2$0^j6\2x5^j6@2$0^j6\2x6^j6@2$0^j6\2x7^j6@2$0^j6\2x8^j6@2$0^j6\2x9^j6@2$0^j6\3x10^j6@2$0^j6\3x11^j6@2$0^j6\3x12^j6@2$0^j6\3x13^j6@2$0^j6\3x14^j6@2$0^j6\3x15^j6@2$0^j6\3x16^j6@2$0^j6\3x17^j6@2$0^j6\3x18^j6@2$0^j6\3x19^j6@2$0^j6\3x20^j6@2$0^j6\3x21^j6@2$0^j6\3x22^j6@2$0^j6\3x23^j6@2$0^j6\3x24^j6@2$0^j6\3x25^j6@2$0^j6\3x26^j6@ha^j6^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26. intros H. exact (ex_intro _ x1 (ex_introF25 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 (P x1) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 H)). Qed.
Lemma ex_introF27 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>3T25T>3T26T>3T27T>1P>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hbP>2x1^hc>2x2^hc>2x3^hc>2x4^hc>2x5^hc>2x6^hc>2x7^hc>2x8^hc>2x9^hc>3x10^hc>3x11^hc>3x12^hc>3x13^hc>3x14^hc>3x15^hc>3x16^hc>3x17^hc>3x18^hc>3x19^hc>3x20^hc>3x21^hc>3x22^hc>3x23^hc>3x24^hc>3x25^hc>3x26^hc>3x27^hc>0@hb^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1@2$0^j8\2x1^j8@2$0^j8\2x2^j8@2$0^j8\2x3^j8@2$0^j8\2x4^j8@2$0^j8\2x5^j8@2$0^j8\2x6^j8@2$0^j8\2x7^j8@2$0^j8\2x8^j8@2$0^j8\2x9^j8@2$0^j8\3x10^j8@2$0^j8\3x11^j8@2$0^j8\3x12^j8@2$0^j8\3x13^j8@2$0^j8\3x14^j8@2$0^j8\3x15^j8@2$0^j8\3x16^j8@2$0^j8\3x17^j8@2$0^j8\3x18^j8@2$0^j8\3x19^j8@2$0^j8\3x20^j8@2$0^j8\3x21^j8@2$0^j8\3x22^j8@2$0^j8\3x23^j8@2$0^j8\3x24^j8@2$0^j8\3x25^j8@2$0^j8\3x26^j8@2$0^j8\3x27^j8@hb^j8^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27. intros H. exact (ex_intro _ x1 (ex_introF26 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 (P x1) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 H)). Qed.
Lemma ex_introF28 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>3T25T>3T26T>3T27T>3T28T>1P>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hcP>2x1^hd>2x2^hd>2x3^hd>2x4^hd>2x5^hd>2x6^hd>2x7^hd>2x8^hd>2x9^hd>3x10^hd>3x11^hd>3x12^hd>3x13^hd>3x14^hd>3x15^hd>3x16^hd>3x17^hd>3x18^hd>3x19^hd>3x20^hd>3x21^hd>3x22^hd>3x23^hd>3x24^hd>3x25^hd>3x26^hd>3x27^hd>3x28^hd>0@hc^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1@2$0^ja\2x1^ja@2$0^ja\2x2^ja@2$0^ja\2x3^ja@2$0^ja\2x4^ja@2$0^ja\2x5^ja@2$0^ja\2x6^ja@2$0^ja\2x7^ja@2$0^ja\2x8^ja@2$0^ja\2x9^ja@2$0^ja\3x10^ja@2$0^ja\3x11^ja@2$0^ja\3x12^ja@2$0^ja\3x13^ja@2$0^ja\3x14^ja@2$0^ja\3x15^ja@2$0^ja\3x16^ja@2$0^ja\3x17^ja@2$0^ja\3x18^ja@2$0^ja\3x19^ja@2$0^ja\3x20^ja@2$0^ja\3x21^ja@2$0^ja\3x22^ja@2$0^ja\3x23^ja@2$0^ja\3x24^ja@2$0^ja\3x25^ja@2$0^ja\3x26^ja@2$0^ja\3x27^ja@2$0^ja\3x28^ja@hc^ja^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28. intros H. exact (ex_intro _ x1 (ex_introF27 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 (P x1) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 H)). Qed.
Lemma ex_introF29 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>3T25T>3T26T>3T27T>3T28T>3T29T>1P>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hdP>2x1^he>2x2^he>2x3^he>2x4^he>2x5^he>2x6^he>2x7^he>2x8^he>2x9^he>3x10^he>3x11^he>3x12^he>3x13^he>3x14^he>3x15^he>3x16^he>3x17^he>3x18^he>3x19^he>3x20^he>3x21^he>3x22^he>3x23^he>3x24^he>3x25^he>3x26^he>3x27^he>3x28^he>3x29^he>0@hd^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1@2$0^jc\2x1^jc@2$0^jc\2x2^jc@2$0^jc\2x3^jc@2$0^jc\2x4^jc@2$0^jc\2x5^jc@2$0^jc\2x6^jc@2$0^jc\2x7^jc@2$0^jc\2x8^jc@2$0^jc\2x9^jc@2$0^jc\3x10^jc@2$0^jc\3x11^jc@2$0^jc\3x12^jc@2$0^jc\3x13^jc@2$0^jc\3x14^jc@2$0^jc\3x15^jc@2$0^jc\3x16^jc@2$0^jc\3x17^jc@2$0^jc\3x18^jc@2$0^jc\3x19^jc@2$0^jc\3x20^jc@2$0^jc\3x21^jc@2$0^jc\3x22^jc@2$0^jc\3x23^jc@2$0^jc\3x24^jc@2$0^jc\3x25^jc@2$0^jc\3x26^jc@2$0^jc\3x27^jc@2$0^jc\3x28^jc@2$0^jc\3x29^jc@hd^jc^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29. intros H. exact (ex_intro _ x1 (ex_introF28 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 (P x1) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 H)). Qed.
Lemma ex_introF30 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>3T25T>3T26T>3T27T>3T28T>3T29T>3T30T>1P>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^heP>2x1^hf>2x2^hf>2x3^hf>2x4^hf>2x5^hf>2x6^hf>2x7^hf>2x8^hf>2x9^hf>3x10^hf>3x11^hf>3x12^hf>3x13^hf>3x14^hf>3x15^hf>3x16^hf>3x17^hf>3x18^hf>3x19^hf>3x20^hf>3x21^hf>3x22^hf>3x23^hf>3x24^hf>3x25^hf>3x26^hf>3x27^hf>3x28^hf>3x29^hf>3x30^hf>0@he^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1@2$0^je\2x1^je@2$0^je\2x2^je@2$0^je\2x3^je@2$0^je\2x4^je@2$0^je\2x5^je@2$0^je\2x6^je@2$0^je\2x7^je@2$0^je\2x8^je@2$0^je\2x9^je@2$0^je\3x10^je@2$0^je\3x11^je@2$0^je\3x12^je@2$0^je\3x13^je@2$0^je\3x14^je@2$0^je\3x15^je@2$0^je\3x16^je@2$0^je\3x17^je@2$0^je\3x18^je@2$0^je\3x19^je@2$0^je\3x20^je@2$0^je\3x21^je@2$0^je\3x22^je@2$0^je\3x23^je@2$0^je\3x24^je@2$0^je\3x25^je@2$0^je\3x26^je@2$0^je\3x27^je@2$0^je\3x28^je@2$0^je\3x29^je@2$0^je\3x30^je@he^je^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30. intros H. exact (ex_intro _ x1 (ex_introF29 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 (P x1) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 H)). Qed.
Lemma ex_introF31 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>3T25T>3T26T>3T27T>3T28T>3T29T>3T30T>3T31T>1P>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hfP>2x1^i0>2x2^i0>2x3^i0>2x4^i0>2x5^i0>2x6^i0>2x7^i0>2x8^i0>2x9^i0>3x10^i0>3x11^i0>3x12^i0>3x13^i0>3x14^i0>3x15^i0>3x16^i0>3x17^i0>3x18^i0>3x19^i0>3x20^i0>3x21^i0>3x22^i0>3x23^i0>3x24^i0>3x25^i0>3x26^i0>3x27^i0>3x28^i0>3x29^i0>3x30^i0>3x31^i0>0@hf^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1@2$0^k0\2x1^k0@2$0^k0\2x2^k0@2$0^k0\2x3^k0@2$0^k0\2x4^k0@2$0^k0\2x5^k0@2$0^k0\2x6^k0@2$0^k0\2x7^k0@2$0^k0\2x8^k0@2$0^k0\2x9^k0@2$0^k0\3x10^k0@2$0^k0\3x11^k0@2$0^k0\3x12^k0@2$0^k0\3x13^k0@2$0^k0\3x14^k0@2$0^k0\3x15^k0@2$0^k0\3x16^k0@2$0^k0\3x17^k0@2$0^k0\3x18^k0@2$0^k0\3x19^k0@2$0^k0\3x20^k0@2$0^k0\3x21^k0@2$0^k0\3x22^k0@2$0^k0\3x23^k0@2$0^k0\3x24^k0@2$0^k0\3x25^k0@2$0^k0\3x26^k0@2$0^k0\3x27^k0@2$0^k0\3x28^k0@2$0^k0\3x29^k0@2$0^k0\3x30^k0@2$0^k0\3x31^k0@hf^k0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31. intros H. exact (ex_intro _ x1 (ex_introF30 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 (P x1) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 H)). Qed.
Lemma ex_introF32 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>3T25T>3T26T>3T27T>3T28T>3T29T>3T30T>3T31T>3T32T>1P>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0P>2x1^i1>2x2^i1>2x3^i1>2x4^i1>2x5^i1>2x6^i1>2x7^i1>2x8^i1>2x9^i1>3x10^i1>3x11^i1>3x12^i1>3x13^i1>3x14^i1>3x15^i1>3x16^i1>3x17^i1>3x18^i1>3x19^i1>3x20^i1>3x21^i1>3x22^i1>3x23^i1>3x24^i1>3x25^i1>3x26^i1>3x27^i1>3x28^i1>3x29^i1>3x30^i1>3x31^i1>3x32^i1>0@i0^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1@2$0^k2\2x1^k2@2$0^k2\2x2^k2@2$0^k2\2x3^k2@2$0^k2\2x4^k2@2$0^k2\2x5^k2@2$0^k2\2x6^k2@2$0^k2\2x7^k2@2$0^k2\2x8^k2@2$0^k2\2x9^k2@2$0^k2\3x10^k2@2$0^k2\3x11^k2@2$0^k2\3x12^k2@2$0^k2\3x13^k2@2$0^k2\3x14^k2@2$0^k2\3x15^k2@2$0^k2\3x16^k2@2$0^k2\3x17^k2@2$0^k2\3x18^k2@2$0^k2\3x19^k2@2$0^k2\3x20^k2@2$0^k2\3x21^k2@2$0^k2\3x22^k2@2$0^k2\3x23^k2@2$0^k2\3x24^k2@2$0^k2\3x25^k2@2$0^k2\3x26^k2@2$0^k2\3x27^k2@2$0^k2\3x28^k2@2$0^k2\3x29^k2@2$0^k2\3x30^k2@2$0^k2\3x31^k2@2$0^k2\3x32^k2@i0^k2^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32. intros H. exact (ex_intro _ x1 (ex_introF31 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 (P x1) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 H)). Qed.
Lemma ex_introF33 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>3T25T>3T26T>3T27T>3T28T>3T29T>3T30T>3T31T>3T32T>3T33T>1P>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1P>2x1^i2>2x2^i2>2x3^i2>2x4^i2>2x5^i2>2x6^i2>2x7^i2>2x8^i2>2x9^i2>3x10^i2>3x11^i2>3x12^i2>3x13^i2>3x14^i2>3x15^i2>3x16^i2>3x17^i2>3x18^i2>3x19^i2>3x20^i2>3x21^i2>3x22^i2>3x23^i2>3x24^i2>3x25^i2>3x26^i2>3x27^i2>3x28^i2>3x29^i2>3x30^i2>3x31^i2>3x32^i2>3x33^i2>0@i1^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1@2$0^k4\2x1^k4@2$0^k4\2x2^k4@2$0^k4\2x3^k4@2$0^k4\2x4^k4@2$0^k4\2x5^k4@2$0^k4\2x6^k4@2$0^k4\2x7^k4@2$0^k4\2x8^k4@2$0^k4\2x9^k4@2$0^k4\3x10^k4@2$0^k4\3x11^k4@2$0^k4\3x12^k4@2$0^k4\3x13^k4@2$0^k4\3x14^k4@2$0^k4\3x15^k4@2$0^k4\3x16^k4@2$0^k4\3x17^k4@2$0^k4\3x18^k4@2$0^k4\3x19^k4@2$0^k4\3x20^k4@2$0^k4\3x21^k4@2$0^k4\3x22^k4@2$0^k4\3x23^k4@2$0^k4\3x24^k4@2$0^k4\3x25^k4@2$0^k4\3x26^k4@2$0^k4\3x27^k4@2$0^k4\3x28^k4@2$0^k4\3x29^k4@2$0^k4\3x30^k4@2$0^k4\3x31^k4@2$0^k4\3x32^k4@2$0^k4\3x33^k4@i1^k4^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33. intros H. exact (ex_intro _ x1 (ex_introF32 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 (P x1) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 H)). Qed.
Lemma ex_introF34 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>3T25T>3T26T>3T27T>3T28T>3T29T>3T30T>3T31T>3T32T>3T33T>3T34T>1P>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2P>2x1^i3>2x2^i3>2x3^i3>2x4^i3>2x5^i3>2x6^i3>2x7^i3>2x8^i3>2x9^i3>3x10^i3>3x11^i3>3x12^i3>3x13^i3>3x14^i3>3x15^i3>3x16^i3>3x17^i3>3x18^i3>3x19^i3>3x20^i3>3x21^i3>3x22^i3>3x23^i3>3x24^i3>3x25^i3>3x26^i3>3x27^i3>3x28^i3>3x29^i3>3x30^i3>3x31^i3>3x32^i3>3x33^i3>3x34^i3>0@i2^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1@2$0^k6\2x1^k6@2$0^k6\2x2^k6@2$0^k6\2x3^k6@2$0^k6\2x4^k6@2$0^k6\2x5^k6@2$0^k6\2x6^k6@2$0^k6\2x7^k6@2$0^k6\2x8^k6@2$0^k6\2x9^k6@2$0^k6\3x10^k6@2$0^k6\3x11^k6@2$0^k6\3x12^k6@2$0^k6\3x13^k6@2$0^k6\3x14^k6@2$0^k6\3x15^k6@2$0^k6\3x16^k6@2$0^k6\3x17^k6@2$0^k6\3x18^k6@2$0^k6\3x19^k6@2$0^k6\3x20^k6@2$0^k6\3x21^k6@2$0^k6\3x22^k6@2$0^k6\3x23^k6@2$0^k6\3x24^k6@2$0^k6\3x25^k6@2$0^k6\3x26^k6@2$0^k6\3x27^k6@2$0^k6\3x28^k6@2$0^k6\3x29^k6@2$0^k6\3x30^k6@2$0^k6\3x31^k6@2$0^k6\3x32^k6@2$0^k6\3x33^k6@2$0^k6\3x34^k6@i2^k6^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34. intros H. exact (ex_intro _ x1 (ex_introF33 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 (P x1) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 H)). Qed.
Lemma ex_introF35 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>3T25T>3T26T>3T27T>3T28T>3T29T>3T30T>3T31T>3T32T>3T33T>3T34T>3T35T>1P>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3P>2x1^i4>2x2^i4>2x3^i4>2x4^i4>2x5^i4>2x6^i4>2x7^i4>2x8^i4>2x9^i4>3x10^i4>3x11^i4>3x12^i4>3x13^i4>3x14^i4>3x15^i4>3x16^i4>3x17^i4>3x18^i4>3x19^i4>3x20^i4>3x21^i4>3x22^i4>3x23^i4>3x24^i4>3x25^i4>3x26^i4>3x27^i4>3x28^i4>3x29^i4>3x30^i4>3x31^i4>3x32^i4>3x33^i4>3x34^i4>3x35^i4>0@i3^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1@2$0^k8\2x1^k8@2$0^k8\2x2^k8@2$0^k8\2x3^k8@2$0^k8\2x4^k8@2$0^k8\2x5^k8@2$0^k8\2x6^k8@2$0^k8\2x7^k8@2$0^k8\2x8^k8@2$0^k8\2x9^k8@2$0^k8\3x10^k8@2$0^k8\3x11^k8@2$0^k8\3x12^k8@2$0^k8\3x13^k8@2$0^k8\3x14^k8@2$0^k8\3x15^k8@2$0^k8\3x16^k8@2$0^k8\3x17^k8@2$0^k8\3x18^k8@2$0^k8\3x19^k8@2$0^k8\3x20^k8@2$0^k8\3x21^k8@2$0^k8\3x22^k8@2$0^k8\3x23^k8@2$0^k8\3x24^k8@2$0^k8\3x25^k8@2$0^k8\3x26^k8@2$0^k8\3x27^k8@2$0^k8\3x28^k8@2$0^k8\3x29^k8@2$0^k8\3x30^k8@2$0^k8\3x31^k8@2$0^k8\3x32^k8@2$0^k8\3x33^k8@2$0^k8\3x34^k8@2$0^k8\3x35^k8@i3^k8^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35. intros H. exact (ex_intro _ x1 (ex_introF34 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 (P x1) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 H)). Qed.
Lemma ex_introF36 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>3T25T>3T26T>3T27T>3T28T>3T29T>3T30T>3T31T>3T32T>3T33T>3T34T>3T35T>3T36T>1P>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4P>2x1^i5>2x2^i5>2x3^i5>2x4^i5>2x5^i5>2x6^i5>2x7^i5>2x8^i5>2x9^i5>3x10^i5>3x11^i5>3x12^i5>3x13^i5>3x14^i5>3x15^i5>3x16^i5>3x17^i5>3x18^i5>3x19^i5>3x20^i5>3x21^i5>3x22^i5>3x23^i5>3x24^i5>3x25^i5>3x26^i5>3x27^i5>3x28^i5>3x29^i5>3x30^i5>3x31^i5>3x32^i5>3x33^i5>3x34^i5>3x35^i5>3x36^i5>0@i4^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1@2$0^ka\2x1^ka@2$0^ka\2x2^ka@2$0^ka\2x3^ka@2$0^ka\2x4^ka@2$0^ka\2x5^ka@2$0^ka\2x6^ka@2$0^ka\2x7^ka@2$0^ka\2x8^ka@2$0^ka\2x9^ka@2$0^ka\3x10^ka@2$0^ka\3x11^ka@2$0^ka\3x12^ka@2$0^ka\3x13^ka@2$0^ka\3x14^ka@2$0^ka\3x15^ka@2$0^ka\3x16^ka@2$0^ka\3x17^ka@2$0^ka\3x18^ka@2$0^ka\3x19^ka@2$0^ka\3x20^ka@2$0^ka\3x21^ka@2$0^ka\3x22^ka@2$0^ka\3x23^ka@2$0^ka\3x24^ka@2$0^ka\3x25^ka@2$0^ka\3x26^ka@2$0^ka\3x27^ka@2$0^ka\3x28^ka@2$0^ka\3x29^ka@2$0^ka\3x30^ka@2$0^ka\3x31^ka@2$0^ka\3x32^ka@2$0^ka\3x33^ka@2$0^ka\3x34^ka@2$0^ka\3x35^ka@2$0^ka\3x36^ka@i4^ka^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36. intros H. exact (ex_intro _ x1 (ex_introF35 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 (P x1) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 H)). Qed.
Lemma ex_introF37 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>3T25T>3T26T>3T27T>3T28T>3T29T>3T30T>3T31T>3T32T>3T33T>3T34T>3T35T>3T36T>3T37T>1P>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5P>2x1^i6>2x2^i6>2x3^i6>2x4^i6>2x5^i6>2x6^i6>2x7^i6>2x8^i6>2x9^i6>3x10^i6>3x11^i6>3x12^i6>3x13^i6>3x14^i6>3x15^i6>3x16^i6>3x17^i6>3x18^i6>3x19^i6>3x20^i6>3x21^i6>3x22^i6>3x23^i6>3x24^i6>3x25^i6>3x26^i6>3x27^i6>3x28^i6>3x29^i6>3x30^i6>3x31^i6>3x32^i6>3x33^i6>3x34^i6>3x35^i6>3x36^i6>3x37^i6>0@i5^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1@2$0^kc\2x1^kc@2$0^kc\2x2^kc@2$0^kc\2x3^kc@2$0^kc\2x4^kc@2$0^kc\2x5^kc@2$0^kc\2x6^kc@2$0^kc\2x7^kc@2$0^kc\2x8^kc@2$0^kc\2x9^kc@2$0^kc\3x10^kc@2$0^kc\3x11^kc@2$0^kc\3x12^kc@2$0^kc\3x13^kc@2$0^kc\3x14^kc@2$0^kc\3x15^kc@2$0^kc\3x16^kc@2$0^kc\3x17^kc@2$0^kc\3x18^kc@2$0^kc\3x19^kc@2$0^kc\3x20^kc@2$0^kc\3x21^kc@2$0^kc\3x22^kc@2$0^kc\3x23^kc@2$0^kc\3x24^kc@2$0^kc\3x25^kc@2$0^kc\3x26^kc@2$0^kc\3x27^kc@2$0^kc\3x28^kc@2$0^kc\3x29^kc@2$0^kc\3x30^kc@2$0^kc\3x31^kc@2$0^kc\3x32^kc@2$0^kc\3x33^kc@2$0^kc\3x34^kc@2$0^kc\3x35^kc@2$0^kc\3x36^kc@2$0^kc\3x37^kc@i5^kc^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37. intros H. exact (ex_intro _ x1 (ex_introF36 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 (P x1) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 H)). Qed.
Lemma ex_introF38 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>3T25T>3T26T>3T27T>3T28T>3T29T>3T30T>3T31T>3T32T>3T33T>3T34T>3T35T>3T36T>3T37T>3T38T>1P>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6P>2x1^i7>2x2^i7>2x3^i7>2x4^i7>2x5^i7>2x6^i7>2x7^i7>2x8^i7>2x9^i7>3x10^i7>3x11^i7>3x12^i7>3x13^i7>3x14^i7>3x15^i7>3x16^i7>3x17^i7>3x18^i7>3x19^i7>3x20^i7>3x21^i7>3x22^i7>3x23^i7>3x24^i7>3x25^i7>3x26^i7>3x27^i7>3x28^i7>3x29^i7>3x30^i7>3x31^i7>3x32^i7>3x33^i7>3x34^i7>3x35^i7>3x36^i7>3x37^i7>3x38^i7>0@i6^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1@2$0^ke\2x1^ke@2$0^ke\2x2^ke@2$0^ke\2x3^ke@2$0^ke\2x4^ke@2$0^ke\2x5^ke@2$0^ke\2x6^ke@2$0^ke\2x7^ke@2$0^ke\2x8^ke@2$0^ke\2x9^ke@2$0^ke\3x10^ke@2$0^ke\3x11^ke@2$0^ke\3x12^ke@2$0^ke\3x13^ke@2$0^ke\3x14^ke@2$0^ke\3x15^ke@2$0^ke\3x16^ke@2$0^ke\3x17^ke@2$0^ke\3x18^ke@2$0^ke\3x19^ke@2$0^ke\3x20^ke@2$0^ke\3x21^ke@2$0^ke\3x22^ke@2$0^ke\3x23^ke@2$0^ke\3x24^ke@2$0^ke\3x25^ke@2$0^ke\3x26^ke@2$0^ke\3x27^ke@2$0^ke\3x28^ke@2$0^ke\3x29^ke@2$0^ke\3x30^ke@2$0^ke\3x31^ke@2$0^ke\3x32^ke@2$0^ke\3x33^ke@2$0^ke\3x34^ke@2$0^ke\3x35^ke@2$0^ke\3x36^ke@2$0^ke\3x37^ke@2$0^ke\3x38^ke@i6^ke^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38. intros H. exact (ex_intro _ x1 (ex_introF37 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 (P x1) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 H)). Qed.
Lemma ex_introF39 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>3T25T>3T26T>3T27T>3T28T>3T29T>3T30T>3T31T>3T32T>3T33T>3T34T>3T35T>3T36T>3T37T>3T38T>3T39T>1P>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7P>2x1^i8>2x2^i8>2x3^i8>2x4^i8>2x5^i8>2x6^i8>2x7^i8>2x8^i8>2x9^i8>3x10^i8>3x11^i8>3x12^i8>3x13^i8>3x14^i8>3x15^i8>3x16^i8>3x17^i8>3x18^i8>3x19^i8>3x20^i8>3x21^i8>3x22^i8>3x23^i8>3x24^i8>3x25^i8>3x26^i8>3x27^i8>3x28^i8>3x29^i8>3x30^i8>3x31^i8>3x32^i8>3x33^i8>3x34^i8>3x35^i8>3x36^i8>3x37^i8>3x38^i8>3x39^i8>0@i7^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1@2$0^l0\2x1^l0@2$0^l0\2x2^l0@2$0^l0\2x3^l0@2$0^l0\2x4^l0@2$0^l0\2x5^l0@2$0^l0\2x6^l0@2$0^l0\2x7^l0@2$0^l0\2x8^l0@2$0^l0\2x9^l0@2$0^l0\3x10^l0@2$0^l0\3x11^l0@2$0^l0\3x12^l0@2$0^l0\3x13^l0@2$0^l0\3x14^l0@2$0^l0\3x15^l0@2$0^l0\3x16^l0@2$0^l0\3x17^l0@2$0^l0\3x18^l0@2$0^l0\3x19^l0@2$0^l0\3x20^l0@2$0^l0\3x21^l0@2$0^l0\3x22^l0@2$0^l0\3x23^l0@2$0^l0\3x24^l0@2$0^l0\3x25^l0@2$0^l0\3x26^l0@2$0^l0\3x27^l0@2$0^l0\3x28^l0@2$0^l0\3x29^l0@2$0^l0\3x30^l0@2$0^l0\3x31^l0@2$0^l0\3x32^l0@2$0^l0\3x33^l0@2$0^l0\3x34^l0@2$0^l0\3x35^l0@2$0^l0\3x36^l0@2$0^l0\3x37^l0@2$0^l0\3x38^l0@2$0^l0\3x39^l0@i7^l0^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39. intros H. exact (ex_intro _ x1 (ex_introF38 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 (P x1) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 H)). Qed.
Lemma ex_introF40 : ltac2:(zQ "10!h9>2T1T>2T2T>2T3T>2T4T>2T5T>2T6T>2T7T>2T8T>2T9T>3T10T>3T11T>3T12T>3T13T>3T14T>3T15T>3T16T>3T17T>3T18T>3T19T>3T20T>3T21T>3T22T>3T23T>3T24T>3T25T>3T26T>3T27T>3T28T>3T29T>3T30T>3T31T>3T32T>3T33T>3T34T>3T35T>3T36T>3T37T>3T38T>3T39T>3T40T>1P>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8P>2x1^i9>2x2^i9>2x3^i9>2x4^i9>2x5^i9>2x6^i9>2x7^i9>2x8^i9>2x9^i9>3x10^i9>3x11^i9>3x12^i9>3x13^i9>3x14^i9>3x15^i9>3x16^i9>3x17^i9>3x18^i9>3x19^i9>3x20^i9>3x21^i9>3x22^i9>3x23^i9>3x24^i9>3x25^i9>3x26^i9>3x27^i9>3x28^i9>3x29^i9>3x30^i9>3x31^i9>3x32^i9>3x33^i9>3x34^i9>3x35^i9>3x36^i9>3x37^i9>3x38^i9>3x39^i9>3x40^i9>0@i8^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1@2$0^l2\2x1^l2@2$0^l2\2x2^l2@2$0^l2\2x3^l2@2$0^l2\2x4^l2@2$0^l2\2x5^l2@2$0^l2\2x6^l2@2$0^l2\2x7^l2@2$0^l2\2x8^l2@2$0^l2\2x9^l2@2$0^l2\3x10^l2@2$0^l2\3x11^l2@2$0^l2\3x12^l2@2$0^l2\3x13^l2@2$0^l2\3x14^l2@2$0^l2\3x15^l2@2$0^l2\3x16^l2@2$0^l2\3x17^l2@2$0^l2\3x18^l2@2$0^l2\3x19^l2@2$0^l2\3x20^l2@2$0^l2\3x21^l2@2$0^l2\3x22^l2@2$0^l2\3x23^l2@2$0^l2\3x24^l2@2$0^l2\3x25^l2@2$0^l2\3x26^l2@2$0^l2\3x27^l2@2$0^l2\3x28^l2@2$0^l2\3x29^l2@2$0^l2\3x30^l2@2$0^l2\3x31^l2@2$0^l2\3x32^l2@2$0^l2\3x33^l2@2$0^l2\3x34^l2@2$0^l2\3x35^l2@2$0^l2\3x36^l2@2$0^l2\3x37^l2@2$0^l2\3x38^l2@2$0^l2\3x39^l2@2$0^l2\3x40^l2@i8^l2^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1").
Proof. intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40. intros H. exact (ex_intro _ x1 (ex_introF39 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 (P x1) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 H)). Qed.

(* [comment removed for export] *)
Module NdCore.
Import Ltac2.Ltac2.

Ltac2 nd_fail () := Control.zero (Tactic_failure None).

(* [comment removed for export] *)
Ltac2 rec nd_flatten (p : Std.intro_pattern) : Std.intro_pattern list :=
  match p with
  | Std.IntroAction a =>
      match a with
      | Std.IntroOrAndPattern oa =>
          match oa with
          | Std.IntroAndPattern l =>
              match l with
              | [x; y] => x :: nd_flatten y
              | _ => [p]
              end
          | Std.IntroOrPattern _ => [p]
          end
      | _ => [p]
      end
  | _ => [p]
  end.

Ltac2 nd_is_and (t : constr) : (constr * constr) option :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if Int.equal (Array.length args) 2 then
        (if Constr.equal h '@and then Some (Array.get args 0, Array.get args 1) else None)
      else None
  | _ => None
  end.

(* [comment removed for export] *)
Ltac2 nd_is_ex (t : constr) : (constr * binder * constr) option :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if Int.equal (Array.length args) 2 then
        (if Constr.equal h '@ex then
           (match Constr.Unsafe.kind (Array.get args 1) with
            | Constr.Unsafe.Lambda b body =>
                if Constr.Unsafe.is_closed (Array.get args 0) then Some (Array.get args 0, b, body) else None
            | _ => None
            end)
         else None)
      else None
  | _ => None
  end.

(* [comment removed for export] *)
Ltac2 rec nd_and_run (dored : bool) (t : constr) (maxn : int) (acc : constr list) : constr list :=
  if Int.le maxn 1 then List.rev (t :: acc) else
  match nd_is_and t with
  | Some ab => let (a, b) := ab in nd_and_run dored b (Int.sub maxn 1) (a :: acc)
  | None =>
      if dored then
        (match acc with
         | [] => List.rev (t :: acc)
         | _ :: _ =>
           let t' := Std.eval_hnf t in
           match nd_is_and t' with
           | Some ab => let (a, b) := ab in nd_and_run dored b (Int.sub maxn 1) (a :: acc)
           | None => List.rev (t :: acc)
           end
         end)
      else List.rev (t :: acc)
  end.

(* [comment removed for export] *)
Ltac2 rec nd_ex_run (t : constr) (maxk : int) (tys : constr list) (bs : binder list) : constr list * binder list * constr :=
  if Int.le maxk 0 then (List.rev tys, List.rev bs, t) else
  match nd_is_ex t with
  | Some x => let (ty, b, body) := x in nd_ex_run body (Int.sub maxk 1) (ty :: tys) (b :: bs)
  | None => (List.rev tys, List.rev bs, t)
  end.

Ltac2 nd_and_lemma (n : int) : constr :=
  if Int.equal n 2 then '@and_elimF2
  else if Int.equal n 3 then '@and_elimF3
  else if Int.equal n 4 then '@and_elimF4
  else if Int.equal n 5 then '@and_elimF5
  else if Int.equal n 6 then '@and_elimF6
  else if Int.equal n 7 then '@and_elimF7
  else if Int.equal n 8 then '@and_elimF8
  else if Int.equal n 9 then '@and_elimF9
  else if Int.equal n 10 then '@and_elimF10
  else if Int.equal n 11 then '@and_elimF11
  else if Int.equal n 12 then '@and_elimF12
  else if Int.equal n 13 then '@and_elimF13
  else if Int.equal n 14 then '@and_elimF14
  else if Int.equal n 15 then '@and_elimF15
  else if Int.equal n 16 then '@and_elimF16
  else if Int.equal n 17 then '@and_elimF17
  else if Int.equal n 18 then '@and_elimF18
  else if Int.equal n 19 then '@and_elimF19
  else if Int.equal n 20 then '@and_elimF20
  else if Int.equal n 21 then '@and_elimF21
  else if Int.equal n 22 then '@and_elimF22
  else if Int.equal n 23 then '@and_elimF23
  else if Int.equal n 24 then '@and_elimF24
  else if Int.equal n 25 then '@and_elimF25
  else if Int.equal n 26 then '@and_elimF26
  else if Int.equal n 27 then '@and_elimF27
  else if Int.equal n 28 then '@and_elimF28
  else if Int.equal n 29 then '@and_elimF29
  else if Int.equal n 30 then '@and_elimF30
  else if Int.equal n 31 then '@and_elimF31
  else if Int.equal n 32 then '@and_elimF32
  else if Int.equal n 33 then '@and_elimF33
  else if Int.equal n 34 then '@and_elimF34
  else if Int.equal n 35 then '@and_elimF35
  else if Int.equal n 36 then '@and_elimF36
  else if Int.equal n 37 then '@and_elimF37
  else if Int.equal n 38 then '@and_elimF38
  else if Int.equal n 39 then '@and_elimF39
  else if Int.equal n 40 then '@and_elimF40
  else if Int.equal n 41 then '@and_elimF41
  else if Int.equal n 42 then '@and_elimF42
  else if Int.equal n 43 then '@and_elimF43
  else if Int.equal n 44 then '@and_elimF44
  else if Int.equal n 45 then '@and_elimF45
  else if Int.equal n 46 then '@and_elimF46
  else if Int.equal n 47 then '@and_elimF47
  else if Int.equal n 48 then '@and_elimF48
  else nd_fail ().

Ltac2 nd_ex_lemma (n : int) : constr :=
  if Int.equal n 1 then '@ex_elimF1
  else if Int.equal n 2 then '@ex_elimF2
  else if Int.equal n 3 then '@ex_elimF3
  else if Int.equal n 4 then '@ex_elimF4
  else if Int.equal n 5 then '@ex_elimF5
  else if Int.equal n 6 then '@ex_elimF6
  else if Int.equal n 7 then '@ex_elimF7
  else if Int.equal n 8 then '@ex_elimF8
  else if Int.equal n 9 then '@ex_elimF9
  else if Int.equal n 10 then '@ex_elimF10
  else if Int.equal n 11 then '@ex_elimF11
  else if Int.equal n 12 then '@ex_elimF12
  else if Int.equal n 13 then '@ex_elimF13
  else if Int.equal n 14 then '@ex_elimF14
  else if Int.equal n 15 then '@ex_elimF15
  else if Int.equal n 16 then '@ex_elimF16
  else if Int.equal n 17 then '@ex_elimF17
  else if Int.equal n 18 then '@ex_elimF18
  else if Int.equal n 19 then '@ex_elimF19
  else if Int.equal n 20 then '@ex_elimF20
  else if Int.equal n 21 then '@ex_elimF21
  else if Int.equal n 22 then '@ex_elimF22
  else if Int.equal n 23 then '@ex_elimF23
  else if Int.equal n 24 then '@ex_elimF24
  else if Int.equal n 25 then '@ex_elimF25
  else if Int.equal n 26 then '@ex_elimF26
  else if Int.equal n 27 then '@ex_elimF27
  else if Int.equal n 28 then '@ex_elimF28
  else if Int.equal n 29 then '@ex_elimF29
  else if Int.equal n 30 then '@ex_elimF30
  else if Int.equal n 31 then '@ex_elimF31
  else if Int.equal n 32 then '@ex_elimF32
  else if Int.equal n 33 then '@ex_elimF33
  else if Int.equal n 34 then '@ex_elimF34
  else if Int.equal n 35 then '@ex_elimF35
  else if Int.equal n 36 then '@ex_elimF36
  else if Int.equal n 37 then '@ex_elimF37
  else if Int.equal n 38 then '@ex_elimF38
  else if Int.equal n 39 then '@ex_elimF39
  else if Int.equal n 40 then '@ex_elimF40
  else nd_fail ().


Ltac2 nd_is_section (id : ident) : bool :=
  match Env.get [id] with None => false | Some _ => true end.

(* [comment removed for export] *)
Ltac2 nd_refine (tm : constr) : unit :=
  match Constr.Unsafe.check tm with
  | Val tm' => ltac1:(t |- refine (t _)) (Ltac1.of_constr tm')
  | Err _ => nd_fail ()
  end.

(* [comment removed for export] *)
Ltac2 nd_goal_prem () : (constr * constr) option :=
  match Constr.Unsafe.kind (Control.goal ()) with
  | Constr.Unsafe.Prod b cod =>
      if Constr.Unsafe.noccurn 1 cod then Some (Constr.Binder.type b, Constr.Unsafe.substnl [Constr.Binder.type b] 0 cod) else None
  | _ => None
  end.

Ltac2 nd_head (t0 : constr) : constr :=
  match nd_is_and t0 with
  | Some _ => t0
  | None => match nd_is_ex t0 with Some _ => t0 | None => Std.eval_hnf t0 end
  end.

(* [comment removed for export] *)
Ltac2 nd_run (maxcomp : int) (dored : bool) : int option :=
  match nd_goal_prem () with
  | None => None
  | Some tg =>
      let (t0, g) := tg in
      let t := if dored then nd_head t0 else t0 in
      match nd_is_ex t with
      | Some _ =>
          let maxk := if Int.lt (Int.sub maxcomp 1) 40 then Int.sub maxcomp 1 else 40 in
          let (tys, bs, body) := nd_ex_run t maxk [] [] in
          let k := List.length tys in
          let p := List.fold_right (fun b acc => Constr.Unsafe.make (Constr.Unsafe.Lambda b acc)) bs body in
          nd_refine (Constr.Unsafe.make (Constr.Unsafe.App (nd_ex_lemma k) (Array.of_list (List.append tys [p; g]))));
          Some k
      | None =>
          match nd_is_and t with
          | Some _ =>
              let maxn := if Int.lt maxcomp 48 then maxcomp else 48 in
              let comps := nd_and_run dored t maxn [] in
              let n := List.length comps in
              nd_refine (Constr.Unsafe.make (Constr.Unsafe.App (nd_and_lemma n) (Array.of_list (List.append comps [g]))));
              Some (Int.sub n 1)
          | None => None
          end
      end
  end.

(* [comment removed for export] *)
Ltac2 rec nd_go (pats : Std.intro_pattern list) : unit :=
  match pats with
  | [] => ()
  | [p] => Std.intros false [p]
  | _ :: _ =>
      match nd_run (List.length pats) true with
      | None => nd_fail ()
      | Some used =>
          Std.intros false (List.firstn used pats);
          nd_go (List.skipn used pats)
      end
  end.

(* [comment removed for export] *)
Ltac2 nd_front (clr : bool) (c : constr) : unit :=
  let gen () := ltac1:(t |- generalize t) (Ltac1.of_constr c) in
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Var id =>
      if clr then (if nd_is_section id then gen () else Control.plus (fun () => Std.revert [id]) (fun _ => gen ()))
      else gen ()
  | _ => gen ()
  end.

Ltac2 entry (clr : bool) (c : Ltac1.t) (p : Ltac1.t) : unit :=
  match Ltac1.to_constr c with
  | None => nd_fail ()
  | Some c =>
      match Ltac1.to_intro_pattern p with
      | None => nd_fail ()
      | Some p =>
          let pats := nd_flatten p in
          if Int.lt (List.length pats) 2 then nd_fail ()
          else Control.enter (fun () => nd_front clr c; nd_go pats)
      end
  end.
Ltac2 entry_d (c : Ltac1.t) (p : Ltac1.t) : unit := entry true c p.
Ltac2 entry_p (c : Ltac1.t) (p : Ltac1.t) : unit := entry false c p.

Ltac2 nd_intro_fresh (base : ident) : ident :=
  let h := Fresh.in_goal base in Std.intros false [Std.IntroNaming (Std.IntroIdentifier h)]; h.
Ltac2 nd_intro_named (id : ident) : unit := Std.intros false [Std.IntroNaming (Std.IntroIdentifier id)].
Ltac2 rec nd_repeat (n : int) (f : unit -> unit) : unit := if Int.le n 0 then () else (f (); nd_repeat (Int.sub n 1) f).

(* [comment removed for export] *)
Ltac2 rec nd_decomp (id : ident) : unit :=
  match nd_is_and (Constr.type (Control.hyp id)) with
  | None => ()
  | Some _ =>
      Std.revert [id];
      match nd_run 48 false with
      | None => nd_fail ()
      | Some used =>
          let rec loop (n : int) (acc : ident list) : ident list :=
            if Int.le n 0 then acc else loop (Int.sub n 1) (nd_intro_fresh @H :: acc) in
          let names := loop (Int.add used 1) [] in
          List.iter nd_decomp (List.rev names)
      end
  end.
Ltac2 entry_hyp (f : ident -> unit) (c : Ltac1.t) : unit :=
  match Ltac1.to_constr c with
  | None => nd_fail ()
  | Some c =>
      match Constr.Unsafe.kind c with
      | Constr.Unsafe.Var id => if nd_is_section id then nd_fail () else Control.enter (fun () => f id)
      | _ => nd_fail ()
      end
  end.
Ltac2 entry_decomp (c : Ltac1.t) : unit := entry_hyp nd_decomp c.

(* [comment removed for export] *)
Ltac2 rec nd_exs (po : ident) : unit :=
  let t0 := Constr.type (Control.hyp po) in
  let t := match nd_is_ex t0 with Some _ => t0 | None => Std.eval_hnf t0 end in
  match nd_is_ex t with
  | None => ()
  | Some _ =>
      Std.revert [po];
      match nd_run (Int.add 40 1) true with
      | None => nd_fail ()
      | Some k => nd_repeat k (fun () => let _ := nd_intro_fresh @x in ()); nd_intro_named po; nd_exs po
      end
  end.
Ltac2 rec nd_ands (po : ident) : unit :=
  match nd_is_and (Constr.type (Control.hyp po)) with
  | None => ()
  | Some _ =>
      Std.revert [po];
      match nd_run 48 false with
      | None => nd_fail ()
      | Some used => nd_repeat used (fun () => let _ := nd_intro_fresh @PC in ()); nd_intro_named po; nd_ands po
      end
  end.
Ltac2 entry_exs (c : Ltac1.t) : unit := entry_hyp nd_exs c.
Ltac2 entry_ands (c : Ltac1.t) : unit := entry_hyp nd_ands c.
Ltac2 nd_exi_lemma (n : int) : constr :=
  if Int.equal n 1 then '@ex_introF1
  else if Int.equal n 2 then '@ex_introF2
  else if Int.equal n 3 then '@ex_introF3
  else if Int.equal n 4 then '@ex_introF4
  else if Int.equal n 5 then '@ex_introF5
  else if Int.equal n 6 then '@ex_introF6
  else if Int.equal n 7 then '@ex_introF7
  else if Int.equal n 8 then '@ex_introF8
  else if Int.equal n 9 then '@ex_introF9
  else if Int.equal n 10 then '@ex_introF10
  else if Int.equal n 11 then '@ex_introF11
  else if Int.equal n 12 then '@ex_introF12
  else if Int.equal n 13 then '@ex_introF13
  else if Int.equal n 14 then '@ex_introF14
  else if Int.equal n 15 then '@ex_introF15
  else if Int.equal n 16 then '@ex_introF16
  else if Int.equal n 17 then '@ex_introF17
  else if Int.equal n 18 then '@ex_introF18
  else if Int.equal n 19 then '@ex_introF19
  else if Int.equal n 20 then '@ex_introF20
  else if Int.equal n 21 then '@ex_introF21
  else if Int.equal n 22 then '@ex_introF22
  else if Int.equal n 23 then '@ex_introF23
  else if Int.equal n 24 then '@ex_introF24
  else if Int.equal n 25 then '@ex_introF25
  else if Int.equal n 26 then '@ex_introF26
  else if Int.equal n 27 then '@ex_introF27
  else if Int.equal n 28 then '@ex_introF28
  else if Int.equal n 29 then '@ex_introF29
  else if Int.equal n 30 then '@ex_introF30
  else if Int.equal n 31 then '@ex_introF31
  else if Int.equal n 32 then '@ex_introF32
  else if Int.equal n 33 then '@ex_introF33
  else if Int.equal n 34 then '@ex_introF34
  else if Int.equal n 35 then '@ex_introF35
  else if Int.equal n 36 then '@ex_introF36
  else if Int.equal n 37 then '@ex_introF37
  else if Int.equal n 38 then '@ex_introF38
  else if Int.equal n 39 then '@ex_introF39
  else if Int.equal n 40 then '@ex_introF40
  else nd_fail ().

(* [comment removed for export] *)
Ltac2 nd_exi_parts (k : int) : constr list * constr :=
  let g0 := Control.goal () in
  let g := match nd_is_ex g0 with Some _ => g0 | None => Std.eval_hnf g0 end in   (* [comment removed for export] *)
  let (tys, bs, body) := nd_ex_run g k [] [] in
  if Bool.neg (Int.equal (List.length tys) k) then nd_fail () else
  if Int.equal k 0 then nd_fail () else
  (tys, List.fold_right (fun b acc => Constr.Unsafe.make (Constr.Unsafe.Lambda b acc)) bs body).
Ltac2 nd_exi (k : int) : unit :=
  let (tys, p) := nd_exi_parts k in
  let tm := Constr.Unsafe.make (Constr.Unsafe.App (nd_exi_lemma k) (Array.of_list (List.append tys [p]))) in
  match Constr.Unsafe.check tm with
  | Val tm' => ltac1:(t |- eapply t) (Ltac1.of_constr tm')
  | Err _ => nd_fail ()
  end.
Ltac2 nd_exw (ws : Ltac1.t list) : unit :=
  let k := List.length ws in
  let (tys, p) := nd_exi_parts k in
  let wcs := List.map2 (fun w ty =>
                match Ltac1.to_preterm w with
                | Some pt => Constr.Pretype.pretype Constr.Pretype.Flags.constr_flags (Constr.Pretype.expected_oftype ty) pt
                | None => nd_fail ()
                end) ws tys in
  let tm := Constr.Unsafe.make (Constr.Unsafe.App (nd_exi_lemma k) (Array.of_list (List.append tys (p :: wcs)))) in
  match Constr.Unsafe.check tm with
  | Val tm' => ltac1:(t |- refine (t _)) (Ltac1.of_constr tm')
  | Err _ => nd_fail ()
  end.
(* [comment removed for export] *)
Ltac2 entry_exi (n : Ltac1.t) : unit :=
  match Ltac1.to_int n with
  | Some k => Control.enter (fun () =>
                Control.plus (fun () => Control.once (fun () => nd_exi k))
                             (fun _ => nd_repeat k (fun () => ltac1:(eexists))))
  | None => nd_fail ()
  end.
Ltac2 entry_exw (l : Ltac1.t) : unit :=
  match Ltac1.to_list l with
  | Some ws => Control.enter (fun () =>
                 Control.plus (fun () => Control.once (fun () => nd_exw ws))
                              (fun _ => List.iter (fun w => ltac1:(w |- exists w) w) ws))
  | None => nd_fail ()
  end.
End NdCore.

Ltac nd_destruct_core := ltac2:(c p |- NdCore.entry_d c p).
Ltac nd_pose_core := ltac2:(c p |- NdCore.entry_p c p).
Ltac nd_decomp_core := ltac2:(c |- NdCore.entry_decomp c).
(* [comment removed for export] *)
Tactic Notation "ndestruct" constr(c) "as" simple_intropattern(p) := first [ nd_destruct_core c p | destruct c as p ].
Tactic Notation "npose" constr(c) "as" simple_intropattern(p) := first [ nd_pose_core c p | pose proof c as p ].
(* [comment removed for export] *)
Tactic Notation "ndecompose" constr(c) := first [ nd_decomp_core c | decompose [and] c ].
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac nd_exi_core := ltac2:(n |- NdCore.entry_exi n).
Ltac nd_exw_core := ltac2:(l |- NdCore.entry_exw l).
Tactic Notation "neexists" integer(k) := nd_exi_core k.
Tactic Notation "nexists" ne_uconstr_list_sep(l, ",") := nd_exw_core l.

(* [comment removed for export] *)
(* [comment removed for export] *)
Module NdSplits.
Import Ltac2.Ltac2.
Import NdCore.
(* [comment removed for export] *)
Ltac2 Type rec tree := [ TLeaf (ident) | TAnd (ident, tree, tree) | TEx (ident, ident, tree) ].
(* [comment removed for export] *)
Ltac2 rec fresh_from (base : string) (k : int) (taken : ident FSet.t) : ident :=
  let cand := if Int.lt k 0 then base else String.app base (Message.to_string (Message.of_int k)) in
  match Ident.of_string cand with
  | Some id => if FSet.mem id taken then fresh_from base (Int.add k 1) taken else id
  | None => nd_fail ()
  end.
Ltac2 sim_fresh (base : string) (taken : ident FSet.t) : ident := fresh_from base (Int.sub 0 1) taken.
(* [comment removed for export] *)
Ltac2 is_ex_head (t : constr) : constr option :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if Bool.and (Constr.equal h '@ex) (Int.equal (Array.length args) 2) then Some (Array.get args 1) else None
  | _ => None
  end.
(* [comment removed for export] *)
Ltac2 rec plan (t : constr) (h : ident) (taken : ident FSet.t) : tree * ident FSet.t :=
  match nd_is_and t with
  | Some ab =>
      let (a, b) := ab in
      let n1 := sim_fresh "LF" taken in let taken := FSet.add n1 taken in
      let n2 := sim_fresh "LF" taken in let taken := FSet.add n2 taken in
      let taken := FSet.remove h taken in
      let (ta, taken) := plan a n1 taken in
      let (tb, taken) := plan b n2 taken in
      (TAnd h ta tb, taken)
  | None =>
      match is_ex_head t with
      | Some p =>
          let body := match Constr.Unsafe.kind p with Constr.Unsafe.Lambda _ bd => bd | _ => p end in
          let xn := sim_fresh "x" taken in let taken := FSet.add xn taken in
          let n1 := sim_fresh "LF" taken in let taken := FSet.add n1 taken in
          let taken := FSet.remove h taken in
          let (tb, taken) := plan body n1 taken in
          (TEx h xn tb, taken)
      | None => (TLeaf h, taken)
      end
  end.
Ltac2 tree_name (t : tree) : ident := match t with TLeaf n => n | TAnd n _ _ => n | TEx n _ _ => n end.
(* [comment removed for export] *)
Ltac2 rec and_run (t : tree) (acc : tree list) : tree list :=
  match t with TAnd _ a b => and_run b (a :: acc) | _ => List.rev (t :: acc) end.
Ltac2 rec ex_run (t : tree) (xs : ident list) : ident list * tree :=
  match t with TEx _ x b => ex_run b (x :: xs) | _ => (List.rev xs, t) end.
(* [comment removed for export] *)
Ltac2 rec exec (t : tree) : unit :=
  match t with
  | TLeaf _ => ()
  | TAnd h _ _ =>
      let comps := and_run t [] in
      let n := List.length comps in
      Std.revert [h];
      (match nd_run n false with
       | None => nd_fail ()
       | Some used =>
           (* [comment removed for export] *)
           if Int.equal used (Int.sub n 1) then
             (List.iter (fun c => nd_intro_named (tree_name c)) comps; List.iter exec comps)
           else nd_fail ()
       end)
  | TEx h _ _ =>
      let (xs, body) := ex_run t [] in
      let k := List.length xs in
      Std.revert [h];
      (match nd_run (Int.add k 1) false with
       | None => nd_fail ()
       | Some used => if Int.equal used k then (List.iter nd_intro_named xs; nd_intro_named (tree_name body); exec body) else nd_fail ()
       end)
  end.
Ltac2 nd_splits (id : ident) : unit :=
  let t := Constr.type (Control.hyp id) in
  let taken := List.fold_left (fun acc h => let (n, _, _) := h in FSet.add n acc) (FSet.empty FSet.Tags.ident_tag) (Control.hyps ()) in
  let (tr, _) := plan t id taken in
  match tr with TLeaf _ => () | _ => exec tr end.
Ltac2 entry_splits (c : Ltac1.t) : unit := entry_hyp nd_splits c.
End NdSplits.
Ltac nd_splits_core := ltac2:(c |- NdSplits.entry_splits c).
(* [comment removed for export] *)
Ltac nd_splits_stock Hx :=
  lazymatch type of Hx with
  | _ /\ _ => let H1 := fresh "LF" in let H2 := fresh "LF" in destruct Hx as [H1 H2]; nd_splits_stock H1; nd_splits_stock H2
  | ex _ => let x := fresh "x" in let H1 := fresh "LF" in destruct Hx as [x H1]; nd_splits_stock H1
  | _ => idtac
  end.
Ltac nd_splits Hx := first [ nd_splits_core Hx | nd_splits_stock Hx ].
(* [comment removed for export] *)
