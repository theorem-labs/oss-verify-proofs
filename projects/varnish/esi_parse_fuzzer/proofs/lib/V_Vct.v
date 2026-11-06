(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Img0 ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.

Definition VCT_ADDR : Z := 0x12710.

Definition vct_tab : list Z :=
  [ 4; 4; 4; 4; 4; 4; 4; 4; 4; 5; 6; 4100; 4; 6; 4; 4; 4; 4; 4; 4; 4; 4; 4; 4; 4; 4; 4; 4; 4; 4; 4; 4; 1; 512; 16; 512; 512; 512; 512; 512; 16; 16; 512; 2560; 16; 1792; 768; 2064; 2400; 2400; 2400; 2400; 2400; 2400; 2400; 2400; 2400; 2400; 144; 16; 16; 2064; 16; 16; 16; 10440; 10440; 10440; 10440; 10440; 10440; 10376; 10376; 10376; 10376; 10376; 10376; 10376; 10376; 10376; 10376; 10376; 10376; 10376; 10376; 10376; 10376; 10376; 10376; 10376; 10376; 16; 16; 16; 512; 1664; 512; 18632; 18632; 18632; 18632; 18632; 18632; 18568; 18568; 18568; 18568; 18568; 18568; 18568; 18568; 18568; 18568; 18568; 18568; 18568; 18568; 18568; 18568; 18568; 18568; 18568; 18568; 16; 512; 16; 512; 4; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 256; 0; 0; 0; 0; 0; 0; 0; 0; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 0; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 128; 0; 128; 128; 128; 128; 128; 128; 128; 128 ].

Definition vct (c : Z) : Z := nth (Z.to_nat c) vct_tab 0.

(* [comment removed for export] *)
Definition vct_bytes : list byte :=
  [ Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 5; Z_to_bv 8 0; Z_to_bv 8 6; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 16; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 6; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 2; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 2; Z_to_bv 8 0; Z_to_bv 8 2; Z_to_bv 8 0; Z_to_bv 8 2; Z_to_bv 8 0; Z_to_bv 8 2; Z_to_bv 8 0; Z_to_bv 8 2; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 2; Z_to_bv 8 0; Z_to_bv 8 10; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 7; Z_to_bv 8 0; Z_to_bv 8 3; Z_to_bv 8 16; Z_to_bv 8 8; Z_to_bv 8 96; Z_to_bv 8 9; Z_to_bv 8 96; Z_to_bv 8 9; Z_to_bv 8 96; Z_to_bv 8 9; Z_to_bv 8 96; Z_to_bv 8 9; Z_to_bv 8 96; Z_to_bv 8 9; Z_to_bv 8 96; Z_to_bv 8 9; Z_to_bv 8 96; Z_to_bv 8 9; Z_to_bv 8 96; Z_to_bv 8 9; Z_to_bv 8 96; Z_to_bv 8 9; Z_to_bv 8 96; Z_to_bv 8 9; Z_to_bv 8 144; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 8; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 200; Z_to_bv 8 40; Z_to_bv 8 200; Z_to_bv 8 40; Z_to_bv 8 200; Z_to_bv 8 40; Z_to_bv 8 200; Z_to_bv 8 40; Z_to_bv 8 200; Z_to_bv 8 40; Z_to_bv 8 200; Z_to_bv 8 40; Z_to_bv 8 136; Z_to_bv 8 40; Z_to_bv 8 136; Z_to_bv 8 40; Z_to_bv 8 136; Z_to_bv 8 40; Z_to_bv 8 136; Z_to_bv 8 40; Z_to_bv 8 136; Z_to_bv 8 40; Z_to_bv 8 136; Z_to_bv 8 40; Z_to_bv 8 136; Z_to_bv 8 40; Z_to_bv 8 136; Z_to_bv 8 40; Z_to_bv 8 136; Z_to_bv 8 40; Z_to_bv 8 136; Z_to_bv 8 40; Z_to_bv 8 136; Z_to_bv 8 40; Z_to_bv 8 136; Z_to_bv 8 40; Z_to_bv 8 136; Z_to_bv 8 40; Z_to_bv 8 136; Z_to_bv 8 40; Z_to_bv 8 136; Z_to_bv 8 40; Z_to_bv 8 136; Z_to_bv 8 40; Z_to_bv 8 136; Z_to_bv 8 40; Z_to_bv 8 136; Z_to_bv 8 40; Z_to_bv 8 136; Z_to_bv 8 40; Z_to_bv 8 136; Z_to_bv 8 40; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 2; Z_to_bv 8 128; Z_to_bv 8 6; Z_to_bv 8 0; Z_to_bv 8 2; Z_to_bv 8 200; Z_to_bv 8 72; Z_to_bv 8 200; Z_to_bv 8 72; Z_to_bv 8 200; Z_to_bv 8 72; Z_to_bv 8 200; Z_to_bv 8 72; Z_to_bv 8 200; Z_to_bv 8 72; Z_to_bv 8 200; Z_to_bv 8 72; Z_to_bv 8 136; Z_to_bv 8 72; Z_to_bv 8 136; Z_to_bv 8 72; Z_to_bv 8 136; Z_to_bv 8 72; Z_to_bv 8 136; Z_to_bv 8 72; Z_to_bv 8 136; Z_to_bv 8 72; Z_to_bv 8 136; Z_to_bv 8 72; Z_to_bv 8 136; Z_to_bv 8 72; Z_to_bv 8 136; Z_to_bv 8 72; Z_to_bv 8 136; Z_to_bv 8 72; Z_to_bv 8 136; Z_to_bv 8 72; Z_to_bv 8 136; Z_to_bv 8 72; Z_to_bv 8 136; Z_to_bv 8 72; Z_to_bv 8 136; Z_to_bv 8 72; Z_to_bv 8 136; Z_to_bv 8 72; Z_to_bv 8 136; Z_to_bv 8 72; Z_to_bv 8 136; Z_to_bv 8 72; Z_to_bv 8 136; Z_to_bv 8 72; Z_to_bv 8 136; Z_to_bv 8 72; Z_to_bv 8 136; Z_to_bv 8 72; Z_to_bv 8 136; Z_to_bv 8 72; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 2; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 2; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 0 ].

(* [comment removed for export] *)
Definition vct_lws (c : Z) : bool := negb (Z.land (vct c) 3 =? 0).
Definition vct_sp (c : Z) : bool := negb (Z.land (vct c) 1 =? 0).
Definition vct_namestart (c : Z) : bool := negb (Z.land (vct c) 128 =? 0).
Definition vct_xmlname (c : Z) : bool := negb (Z.land (vct c) 384 =? 0).

Lemma vct_range : forall c, 0 <= vct c < 2^16.
Proof.
  intros c. unfold vct.
  assert (H : forallb (fun x => (0 <=? x) && (x <? 2^16)) vct_tab = true) by (vm_compute; reflexivity).
  destruct (nth_in_or_default (Z.to_nat c) vct_tab 0) as [IN| ->]; [|cbn; lia].
  rewrite forallb_forall in H. specialize (H _ IN). apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

(* [comment removed for export] *)
Definition vct_facts_b : bool :=
  forallb (fun i => let c := Z.of_nat i in
              implb (vct_namestart c) (vct_xmlname c && negb (vct_sp c) && negb (vct_lws c)
                                       && negb (c =? 62) && negb (c =? 47) && negb (c =? 61) && negb (c =? 60)))
          (seq 0 256).
Lemma vct_facts_ok : vct_facts_b = true. Proof. vm_compute. reflexivity. Qed.

Lemma vct_namestart_facts : forall c, 0 <= c < 256 -> vct_namestart c = true ->
  vct_xmlname c = true /\ vct_sp c = false /\ vct_lws c = false /\ c <> 62 /\ c <> 47 /\ c <> 61 /\ c <> 60.
Proof.
  intros c Hc NS. pose proof vct_facts_ok as H. unfold vct_facts_b in H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat c) ltac:(apply in_seq; lia)). cbv beta zeta in H. rewrite Z2Nat.id in H by lia.
  rewrite NS in H. cbn [implb] in H.
  repeat (apply andb_prop in H as [H ?X]).
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try exact H;
    try (apply negb_true_iff; assumption); try (apply Z.eqb_neq; apply negb_true_iff; assumption).
Qed.

(* [comment removed for export] *)
Fixpoint lbeq (a b : list byte) : bool :=
  match a, b with [], [] => true | x :: a', y :: b' => bv_eqb x y && lbeq a' b' | _, _ => false end.
Definition vct_entry_b : bool :=
  forallb (fun i => lbeq (firstn 2 (skipn (2 * i) vct_bytes)) (le2 (Z_to_bv 64 (nth i vct_tab 0)))) (seq 0 256).
Lemma vct_entry_ok : vct_entry_b = true. Proof. vm_compute. reflexivity. Qed.

Lemma list_beq_bv_eq : forall (a b : list byte), lbeq a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. unfold bv_eqb in H1. apply Z.eqb_eq in H1. apply bv_eq in H1. subst y. f_equal. apply IH, H2.
Qed.

Lemma vct_entry : forall c, 0 <= c < 256 ->
  firstn 2 (skipn (Z.to_nat (2 * c)) vct_bytes) = le2 (Z_to_bv 64 (vct c)).
Proof.
  intros c Hc. pose proof vct_entry_ok as H. unfold vct_entry_b in H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat c) ltac:(apply in_seq; lia)). apply list_beq_bv_eq in H.
  unfold vct. replace (Z.to_nat (2 * c)) with (2 * Z.to_nat c)%nat by lia. exact H.
Qed.

Section PerImage.
  Variable segs : list MemImageType.Segment.
  Hypothesis RO : ro_bytes_b segs VCT_ADDR vct_bytes = true.

  Lemma vct_bytes_at_gen : forall m, mem_inv segs m -> bytes_at segs m VCT_ADDR vct_bytes.
  Proof.
    intros m MI. apply (ro_bytes_at segs m VCT_ADDR vct_bytes MI); [unfold VCT_ADDR; lia| |].
    - change (Z.of_nat (length vct_bytes)) with 512. unfold VCT_ADDR; lia.
    - apply ro_bytes_b_sound. exact RO.
  Qed.

  Lemma vct_read_gen : forall m c a, mem_inv segs m -> 0 <= c < 256 -> a = wa (VCT_ADDR + 2 * c) ->
    ov_read_bytes segs m a 2 = Some (le2 (Z_to_bv 64 (vct c))).
  Proof.
    intros m c a MI Hc ->.
    rewrite (bytes_at_read segs m VCT_ADDR vct_bytes (2 * c) 2 (vct_bytes_at_gen m MI)); [| lia |].
    - f_equal. apply vct_entry. exact Hc.
    - change (length vct_bytes) with 512%nat. lia.
  Qed.
End PerImage.

(* [comment removed for export] *)
Lemma vct_read0 : forall m c a, mem_inv Img0.rsegs m -> 0 <= c < 256 -> a = wa (VCT_ADDR + 2 * c) ->
  ov_read_bytes Img0.rsegs m a 2 = Some (le2 (Z_to_bv 64 (vct c))).
Proof. apply vct_read_gen. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma vct_readU : forall m c a, mem_inv ImgU.rsegs m -> 0 <= c < 256 -> a = wa (VCT_ADDR + 2 * c) ->
  ov_read_bytes ImgU.rsegs m a 2 = Some (le2 (Z_to_bv 64 (vct c))).
Proof. apply vct_read_gen. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)       (* [comment removed for export] *)
(* [comment removed for export] *)       (* [comment removed for export] *)
(* [comment removed for export] *)    (* [comment removed for export] *)
(* [comment removed for export] *)       (* [comment removed for export] *)
(* [comment removed for export] *)    (* [comment removed for export] *)
(* [comment removed for export] *)   (* [comment removed for export] *)
(* [comment removed for export] *)   (* [comment removed for export] *)
