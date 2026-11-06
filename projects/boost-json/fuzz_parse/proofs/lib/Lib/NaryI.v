(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import List Lia.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04Some04list03nat06option37Corelib4Init5Logicj12eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5NaryI~~~~~~ka8or_chain36Stdlib5Lists4Listp19nth_errorj13and" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Fixpoint or_chain (l : list Prop) : Prop :=
  match l with
  | nil => False
  | A :: nil => A
  | A :: l' => A \/ or_chain l'
  end.

Lemma or_chainI : ltac2:(zQ "70!h8!he!i4!i9!k5!o6!q4>1l@1$1P>1i$2>1AP>0@3$4@1$3P@3$6P^3^2@2$0P^1>0^2@1$5^5").
Proof. intros l i A.
  revert i. induction l as [|B l IH]; intros [|i] H HA; cbn in H.
  - discriminate H.
  - discriminate H.
  - injection H as ->. destruct l as [|C l']; [exact HA| left; exact HA].
  - destruct l as [|C l']; [destruct i; discriminate H|]. right. exact (IH i H HA).
Qed.

(* [comment removed for export] *)
Ltac or_spine_list g :=
  lazymatch g with
  | ?A \/ ?B => let l := or_spine_list B in constr:(@cons Prop A l)
  | _ => constr:(@cons Prop g (@nil Prop))
  end.

(* [comment removed for export] *)
Ltac or_pick_from l i rest tac :=
  lazymatch rest with
  | @cons _ ?A ?rest' =>
      first [ refine (@or_chainI l i A (@eq_refl (option Prop) (@Some Prop A)) _); tac
            | or_pick_from l (S i) rest' tac ]
  end.
Ltac or_pick tac :=
  let g := lazymatch goal with |- ?g => g end in
  let l := or_spine_list g in
  or_pick_from l O l tac.

(* [comment removed for export] *)
Lemma and_introF2 : ltac2:(zQ "10!r0>2A1P>2A2P>0^2>0^2@2$0^4^3").  Proof. intros A1 A2. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF3 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>0^3>0^3>0^3@2$0^6@2$0^5^4").  Proof. intros A1 A2 A3. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF4 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>0^4>0^4>0^4>0^4@2$0^8@2$0^7@2$0^6^5").  Proof. intros A1 A2 A3 A4. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF5 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>0^5>0^5>0^5>0^5>0^5@2$0^a@2$0^9@2$0^8@2$0^7^6").  Proof. intros A1 A2 A3 A4 A5. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF6 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>0^6>0^6>0^6>0^6>0^6>0^6@2$0^c@2$0^b@2$0^a@2$0^9@2$0^8^7").  Proof. intros A1 A2 A3 A4 A5 A6. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF7 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>0^7>0^7>0^7>0^7>0^7>0^7>0^7@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a@2$0^9^8").  Proof. intros A1 A2 A3 A4 A5 A6 A7. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF8 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>0^8>0^8>0^8>0^8>0^8>0^8>0^8>0^8@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b@2$0^a^9").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF9 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>0^9>0^9>0^9>0^9>0^9>0^9>0^9>0^9>0^9@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c@2$0^b^a").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF10 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>0^a>0^a>0^a>0^a>0^a>0^a>0^a>0^a>0^a>0^a@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d@2$0^c^b").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF11 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>0^b>0^b>0^b>0^b>0^b>0^b>0^b>0^b>0^b>0^b>0^b@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e@2$0^d^c").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF12 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>0^c>0^c>0^c>0^c>0^c>0^c>0^c>0^c>0^c>0^c>0^c>0^c@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f@2$0^e^d").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF13 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>0^d>0^d>0^d>0^d>0^d>0^d>0^d>0^d>0^d>0^d>0^d>0^d>0^d@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0@2$0^f^e").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF14 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>0^e>0^e>0^e>0^e>0^e>0^e>0^e>0^e>0^e>0^e>0^e>0^e>0^e>0^e@2$0^hc@2$0^hb@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1@2$0^h0^f").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF15 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>0^f>0^f>0^f>0^f>0^f>0^f>0^f>0^f>0^f>0^f>0^f>0^f>0^f>0^f>0^f@2$0^he@2$0^hd@2$0^hc@2$0^hb@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2@2$0^h1^h0").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF16 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0>0^h0@2$0^i0@2$0^hf@2$0^he@2$0^hd@2$0^hc@2$0^hb@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3@2$0^h2^h1").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF17 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1>0^h1@2$0^i2@2$0^i1@2$0^i0@2$0^hf@2$0^he@2$0^hd@2$0^hc@2$0^hb@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4@2$0^h3^h2").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF18 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2>0^h2@2$0^i4@2$0^i3@2$0^i2@2$0^i1@2$0^i0@2$0^hf@2$0^he@2$0^hd@2$0^hc@2$0^hb@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5@2$0^h4^h3").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF19 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3>0^h3@2$0^i6@2$0^i5@2$0^i4@2$0^i3@2$0^i2@2$0^i1@2$0^i0@2$0^hf@2$0^he@2$0^hd@2$0^hc@2$0^hb@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6@2$0^h5^h4").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF20 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4>0^h4@2$0^i8@2$0^i7@2$0^i6@2$0^i5@2$0^i4@2$0^i3@2$0^i2@2$0^i1@2$0^i0@2$0^hf@2$0^he@2$0^hd@2$0^hc@2$0^hb@2$0^ha@2$0^h9@2$0^h8@2$0^h7@2$0^h6^h5").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF21 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5>0^h5@2$0^ia@2$0^i9@2$0^i8@2$0^i7@2$0^i6@2$0^i5@2$0^i4@2$0^i3@2$0^i2@2$0^i1@2$0^i0@2$0^hf@2$0^he@2$0^hd@2$0^hc@2$0^hb@2$0^ha@2$0^h9@2$0^h8@2$0^h7^h6").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF22 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6>0^h6@2$0^ic@2$0^ib@2$0^ia@2$0^i9@2$0^i8@2$0^i7@2$0^i6@2$0^i5@2$0^i4@2$0^i3@2$0^i2@2$0^i1@2$0^i0@2$0^hf@2$0^he@2$0^hd@2$0^hc@2$0^hb@2$0^ha@2$0^h9@2$0^h8^h7").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF23 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7>0^h7@2$0^ie@2$0^id@2$0^ic@2$0^ib@2$0^ia@2$0^i9@2$0^i8@2$0^i7@2$0^i6@2$0^i5@2$0^i4@2$0^i3@2$0^i2@2$0^i1@2$0^i0@2$0^hf@2$0^he@2$0^hd@2$0^hc@2$0^hb@2$0^ha@2$0^h9^h8").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF24 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8>0^h8@2$0^j0@2$0^if@2$0^ie@2$0^id@2$0^ic@2$0^ib@2$0^ia@2$0^i9@2$0^i8@2$0^i7@2$0^i6@2$0^i5@2$0^i4@2$0^i3@2$0^i2@2$0^i1@2$0^i0@2$0^hf@2$0^he@2$0^hd@2$0^hc@2$0^hb@2$0^ha^h9").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF25 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9>0^h9@2$0^j2@2$0^j1@2$0^j0@2$0^if@2$0^ie@2$0^id@2$0^ic@2$0^ib@2$0^ia@2$0^i9@2$0^i8@2$0^i7@2$0^i6@2$0^i5@2$0^i4@2$0^i3@2$0^i2@2$0^i1@2$0^i0@2$0^hf@2$0^he@2$0^hd@2$0^hc@2$0^hb^ha").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF26 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha>0^ha@2$0^j4@2$0^j3@2$0^j2@2$0^j1@2$0^j0@2$0^if@2$0^ie@2$0^id@2$0^ic@2$0^ib@2$0^ia@2$0^i9@2$0^i8@2$0^i7@2$0^i6@2$0^i5@2$0^i4@2$0^i3@2$0^i2@2$0^i1@2$0^i0@2$0^hf@2$0^he@2$0^hd@2$0^hc^hb").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF27 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb>0^hb@2$0^j6@2$0^j5@2$0^j4@2$0^j3@2$0^j2@2$0^j1@2$0^j0@2$0^if@2$0^ie@2$0^id@2$0^ic@2$0^ib@2$0^ia@2$0^i9@2$0^i8@2$0^i7@2$0^i6@2$0^i5@2$0^i4@2$0^i3@2$0^i2@2$0^i1@2$0^i0@2$0^hf@2$0^he@2$0^hd^hc").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF28 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc>0^hc@2$0^j8@2$0^j7@2$0^j6@2$0^j5@2$0^j4@2$0^j3@2$0^j2@2$0^j1@2$0^j0@2$0^if@2$0^ie@2$0^id@2$0^ic@2$0^ib@2$0^ia@2$0^i9@2$0^i8@2$0^i7@2$0^i6@2$0^i5@2$0^i4@2$0^i3@2$0^i2@2$0^i1@2$0^i0@2$0^hf@2$0^he^hd").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF29 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>3A29P>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd>0^hd@2$0^ja@2$0^j9@2$0^j8@2$0^j7@2$0^j6@2$0^j5@2$0^j4@2$0^j3@2$0^j2@2$0^j1@2$0^j0@2$0^if@2$0^ie@2$0^id@2$0^ic@2$0^ib@2$0^ia@2$0^i9@2$0^i8@2$0^i7@2$0^i6@2$0^i5@2$0^i4@2$0^i3@2$0^i2@2$0^i1@2$0^i0@2$0^hf^he").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF30 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>3A29P>3A30P>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he>0^he@2$0^jc@2$0^jb@2$0^ja@2$0^j9@2$0^j8@2$0^j7@2$0^j6@2$0^j5@2$0^j4@2$0^j3@2$0^j2@2$0^j1@2$0^j0@2$0^if@2$0^ie@2$0^id@2$0^ic@2$0^ib@2$0^ia@2$0^i9@2$0^i8@2$0^i7@2$0^i6@2$0^i5@2$0^i4@2$0^i3@2$0^i2@2$0^i1@2$0^i0^hf").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF31 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>3A29P>3A30P>3A31P>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf>0^hf@2$0^je@2$0^jd@2$0^jc@2$0^jb@2$0^ja@2$0^j9@2$0^j8@2$0^j7@2$0^j6@2$0^j5@2$0^j4@2$0^j3@2$0^j2@2$0^j1@2$0^j0@2$0^if@2$0^ie@2$0^id@2$0^ic@2$0^ib@2$0^ia@2$0^i9@2$0^i8@2$0^i7@2$0^i6@2$0^i5@2$0^i4@2$0^i3@2$0^i2@2$0^i1^i0").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF32 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>3A29P>3A30P>3A31P>3A32P>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0>0^i0@2$0^k0@2$0^jf@2$0^je@2$0^jd@2$0^jc@2$0^jb@2$0^ja@2$0^j9@2$0^j8@2$0^j7@2$0^j6@2$0^j5@2$0^j4@2$0^j3@2$0^j2@2$0^j1@2$0^j0@2$0^if@2$0^ie@2$0^id@2$0^ic@2$0^ib@2$0^ia@2$0^i9@2$0^i8@2$0^i7@2$0^i6@2$0^i5@2$0^i4@2$0^i3@2$0^i2^i1").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF33 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>3A29P>3A30P>3A31P>3A32P>3A33P>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1>0^i1@2$0^k2@2$0^k1@2$0^k0@2$0^jf@2$0^je@2$0^jd@2$0^jc@2$0^jb@2$0^ja@2$0^j9@2$0^j8@2$0^j7@2$0^j6@2$0^j5@2$0^j4@2$0^j3@2$0^j2@2$0^j1@2$0^j0@2$0^if@2$0^ie@2$0^id@2$0^ic@2$0^ib@2$0^ia@2$0^i9@2$0^i8@2$0^i7@2$0^i6@2$0^i5@2$0^i4@2$0^i3^i2").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF34 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>3A29P>3A30P>3A31P>3A32P>3A33P>3A34P>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2>0^i2@2$0^k4@2$0^k3@2$0^k2@2$0^k1@2$0^k0@2$0^jf@2$0^je@2$0^jd@2$0^jc@2$0^jb@2$0^ja@2$0^j9@2$0^j8@2$0^j7@2$0^j6@2$0^j5@2$0^j4@2$0^j3@2$0^j2@2$0^j1@2$0^j0@2$0^if@2$0^ie@2$0^id@2$0^ic@2$0^ib@2$0^ia@2$0^i9@2$0^i8@2$0^i7@2$0^i6@2$0^i5@2$0^i4^i3").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF35 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>3A29P>3A30P>3A31P>3A32P>3A33P>3A34P>3A35P>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3>0^i3@2$0^k6@2$0^k5@2$0^k4@2$0^k3@2$0^k2@2$0^k1@2$0^k0@2$0^jf@2$0^je@2$0^jd@2$0^jc@2$0^jb@2$0^ja@2$0^j9@2$0^j8@2$0^j7@2$0^j6@2$0^j5@2$0^j4@2$0^j3@2$0^j2@2$0^j1@2$0^j0@2$0^if@2$0^ie@2$0^id@2$0^ic@2$0^ib@2$0^ia@2$0^i9@2$0^i8@2$0^i7@2$0^i6@2$0^i5^i4").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF36 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>3A29P>3A30P>3A31P>3A32P>3A33P>3A34P>3A35P>3A36P>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4>0^i4@2$0^k8@2$0^k7@2$0^k6@2$0^k5@2$0^k4@2$0^k3@2$0^k2@2$0^k1@2$0^k0@2$0^jf@2$0^je@2$0^jd@2$0^jc@2$0^jb@2$0^ja@2$0^j9@2$0^j8@2$0^j7@2$0^j6@2$0^j5@2$0^j4@2$0^j3@2$0^j2@2$0^j1@2$0^j0@2$0^if@2$0^ie@2$0^id@2$0^ic@2$0^ib@2$0^ia@2$0^i9@2$0^i8@2$0^i7@2$0^i6^i5").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF37 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>3A29P>3A30P>3A31P>3A32P>3A33P>3A34P>3A35P>3A36P>3A37P>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5>0^i5@2$0^ka@2$0^k9@2$0^k8@2$0^k7@2$0^k6@2$0^k5@2$0^k4@2$0^k3@2$0^k2@2$0^k1@2$0^k0@2$0^jf@2$0^je@2$0^jd@2$0^jc@2$0^jb@2$0^ja@2$0^j9@2$0^j8@2$0^j7@2$0^j6@2$0^j5@2$0^j4@2$0^j3@2$0^j2@2$0^j1@2$0^j0@2$0^if@2$0^ie@2$0^id@2$0^ic@2$0^ib@2$0^ia@2$0^i9@2$0^i8@2$0^i7^i6").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF38 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>3A29P>3A30P>3A31P>3A32P>3A33P>3A34P>3A35P>3A36P>3A37P>3A38P>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6>0^i6@2$0^kc@2$0^kb@2$0^ka@2$0^k9@2$0^k8@2$0^k7@2$0^k6@2$0^k5@2$0^k4@2$0^k3@2$0^k2@2$0^k1@2$0^k0@2$0^jf@2$0^je@2$0^jd@2$0^jc@2$0^jb@2$0^ja@2$0^j9@2$0^j8@2$0^j7@2$0^j6@2$0^j5@2$0^j4@2$0^j3@2$0^j2@2$0^j1@2$0^j0@2$0^if@2$0^ie@2$0^id@2$0^ic@2$0^ib@2$0^ia@2$0^i9@2$0^i8^i7").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF39 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>3A29P>3A30P>3A31P>3A32P>3A33P>3A34P>3A35P>3A36P>3A37P>3A38P>3A39P>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7>0^i7@2$0^ke@2$0^kd@2$0^kc@2$0^kb@2$0^ka@2$0^k9@2$0^k8@2$0^k7@2$0^k6@2$0^k5@2$0^k4@2$0^k3@2$0^k2@2$0^k1@2$0^k0@2$0^jf@2$0^je@2$0^jd@2$0^jc@2$0^jb@2$0^ja@2$0^j9@2$0^j8@2$0^j7@2$0^j6@2$0^j5@2$0^j4@2$0^j3@2$0^j2@2$0^j1@2$0^j0@2$0^if@2$0^ie@2$0^id@2$0^ic@2$0^ib@2$0^ia@2$0^i9^i8").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39. intros; repeat (split; [assumption|]); assumption. Qed.
Lemma and_introF40 : ltac2:(zQ "10!r0>2A1P>2A2P>2A3P>2A4P>2A5P>2A6P>2A7P>2A8P>2A9P>3A10P>3A11P>3A12P>3A13P>3A14P>3A15P>3A16P>3A17P>3A18P>3A19P>3A20P>3A21P>3A22P>3A23P>3A24P>3A25P>3A26P>3A27P>3A28P>3A29P>3A30P>3A31P>3A32P>3A33P>3A34P>3A35P>3A36P>3A37P>3A38P>3A39P>3A40P>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8>0^i8@2$0^l0@2$0^kf@2$0^ke@2$0^kd@2$0^kc@2$0^kb@2$0^ka@2$0^k9@2$0^k8@2$0^k7@2$0^k6@2$0^k5@2$0^k4@2$0^k3@2$0^k2@2$0^k1@2$0^k0@2$0^jf@2$0^je@2$0^jd@2$0^jc@2$0^jb@2$0^ja@2$0^j9@2$0^j8@2$0^j7@2$0^j6@2$0^j5@2$0^j4@2$0^j3@2$0^j2@2$0^j1@2$0^j0@2$0^if@2$0^ie@2$0^id@2$0^ic@2$0^ib@2$0^ia^i9").  Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40. intros; repeat (split; [assumption|]); assumption. Qed.

(* [comment removed for export] *)
Ltac and_spine_len_cap g k := lazymatch k with O => constr:(S O) | S ?k' => lazymatch g with _ /\ ?B => let n := and_spine_len_cap B k' in constr:(S n) | _ => constr:(S O) end end.
Ltac and_introF_of n :=
  lazymatch n with
  | 2 => constr:(and_introF2)
  | 3 => constr:(and_introF3)
  | 4 => constr:(and_introF4)
  | 5 => constr:(and_introF5)
  | 6 => constr:(and_introF6)
  | 7 => constr:(and_introF7)
  | 8 => constr:(and_introF8)
  | 9 => constr:(and_introF9)
  | 10 => constr:(and_introF10)
  | 11 => constr:(and_introF11)
  | 12 => constr:(and_introF12)
  | 13 => constr:(and_introF13)
  | 14 => constr:(and_introF14)
  | 15 => constr:(and_introF15)
  | 16 => constr:(and_introF16)
  | 17 => constr:(and_introF17)
  | 18 => constr:(and_introF18)
  | 19 => constr:(and_introF19)
  | 20 => constr:(and_introF20)
  | 21 => constr:(and_introF21)
  | 22 => constr:(and_introF22)
  | 23 => constr:(and_introF23)
  | 24 => constr:(and_introF24)
  | 25 => constr:(and_introF25)
  | 26 => constr:(and_introF26)
  | 27 => constr:(and_introF27)
  | 28 => constr:(and_introF28)
  | 29 => constr:(and_introF29)
  | 30 => constr:(and_introF30)
  | 31 => constr:(and_introF31)
  | 32 => constr:(and_introF32)
  | 33 => constr:(and_introF33)
  | 34 => constr:(and_introF34)
  | 35 => constr:(and_introF35)
  | 36 => constr:(and_introF36)
  | 37 => constr:(and_introF37)
  | 38 => constr:(and_introF38)
  | 39 => constr:(and_introF39)
  | 40 => constr:(and_introF40)
  end.
Ltac nsplit :=
  let g := lazymatch goal with |- ?g => g end in
  let n := and_spine_len_cap g 39 in
  let n := eval cbv in n in
  lazymatch n with
  | 1 => fail
  | _ => let lem := and_introF_of n in simple apply lem
  end.
(* [comment removed for export] *)
