(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 44 of its 60 lines of code are new or changed and 129 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Prog/SceneTac.v, with its module paths changed; 532 of its 545 lines of code are new or changed and 47 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/U/Prog/pcap_source_next_lib.v, with its module paths changed; 192 of its 241 lines of code are new or changed and 496 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells
  owed_counter_text_c memset_c diginet_counter_text_c bcmp_c check_text_counter_c.
Import ListNotations.
Open Scope Z_scope.

Lemma relro_img_munch : forall W m m', relro_img m -> munch W m m' -> disjoint_from W RELRO_BASE RELRO_LEN -> relro_img m'.
Proof.
  intros W m m' HR MU HD i Hi. unfold mrd. rewrite (MU (wa (RELRO_BASE + i))).
  - exact (HR i Hi).
  - rewrite wa_unsigned by (unfold RELRO_BASE, RELRO_LEN in *; lia).
    eapply disjoint_outside; [exact HD | lia].
Qed.

Lemma rw_cells_app_split : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] (Ha & Hl & Hw)].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_size_app in Hl, Hw.
  rewrite cells_bytes_length in B2 by exact W1.
  split.
  - split; [split; [exact W1 | exact B1] |]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; [exact W2 | exact B2] |]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply Hw. lia.
Qed.

Lemma rw_cells_app_join : forall m A cs1 cs2,
  rw_cells rsegs m A cs1 -> rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2 ->
  rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[W1 B1] (Ha1 & Hl1 & Hw1)] [[W2 B2] (Ha2 & Hl2 & Hw2)].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat (cells_size cs1))).
    + apply Hw1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
      apply Hw2. lia.
Qed.

Lemma le1_zero : le1 (Z_to_bv 64 0) = [b8 0].
Proof. reflexivity. Qed.

Lemma le1_a5 : le1 (Z_to_bv 64 165) = [b8 165].
Proof. reflexivity. Qed.

Lemma rw_cells_join_at : forall m A B cs1 cs2,
  rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 -> B = A + Z.of_nat (cells_size cs1) ->
  rw_cells rsegs m A (cs1 ++ cs2).
Proof. intros m A B cs1 cs2 H1 H2 ->. apply rw_cells_app_join; assumption. Qed.

Lemma rw_cells_CB_bytes : forall m A n bs, rw_cells rsegs m A [CB n bs] -> bytes_at rsegs m A bs.
Proof. intros m A n bs [[_ H] _]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H. Qed.

Lemma rw_cells_CB_len : forall m A n bs, rw_cells rsegs m A [CB n bs] -> length bs = n.
Proof. intros m A n bs [[[H _] _] _]. exact H. Qed.

Lemma memcmp_model_self : forall n l, (n <= length l)%nat -> memcmp_model l l n = Some 0.
Proof.
  induction n as [|n IH]; intros [|a l] H; cbn [memcmp_model length] in *; try lia; try reflexivity.
  rewrite Z.eqb_refl. apply IH. lia.
Qed.

Lemma ct2_go_rc : forall k n s dot i seg d,
  fst (fst (ct2_go n s dot i k seg d)) = 0 \/ fst (fst (ct2_go n s dot i k seg d)) = E_RANGE.
Proof.
  induction k as [|k IH]; intros n s dot i seg d; cbn [ct2_go]; [left; reflexivity|].
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    first [ right; reflexivity | apply IH ].
Qed.

Lemma owed_rc : forall t rc sg d, owed_counter_text_spec t = (rc, sg, d) -> rc = 0 \/ rc = E_RANGE.
Proof.
  intros t rc sg d H. unfold owed_counter_text_spec in H.
  destruct (ct1_owe t 0 [] (repeat 0 8)) as [[[n s] dot]|].
  - unfold ct2 in H. pose proof (ct2_go_rc 8 n s dot 0 [] 0) as R. rewrite H in R. exact R.
  - injection H as <- _ _. right; reflexivity.
Qed.

(* A hypothesis the load tactics do not see. *)
Definition keep (P : Prop) : Prop := P.

(* Split the first cell of a cell list off hypothesis H (into H0); H keeps the rest. *)
Ltac peel H H0 :=
  lazymatch type of H with
  | rw_cells ?segs ?mm ?A (?c :: ?rest) =>
      let H1 := fresh "H" in
      destruct (rw_cells_app_split mm A [c] rest H) as [H0 H1]; clear H; rename H1 into H;
      cbn [cells_size csize Nat.add] in H
  end.

(* Resolve a branch whose condition the context decides. *)
Ltac br := first [ if_false | if_true ].

(* From 0x14e2c (both paths of the agreement check): the fuzz_all loop over seg[8..24), the epilogue,
   the frame given back to the stack. *)
Ltac ctc_tail FRj FRd FRw FR ST sp :=
  lazymatch goal with
  | HS : rw_cells ?segs ?mm ?A1 [CB 8 ?sg], HR : rw_cells _ ?mm (?A1 + 8) [CB 16 ?rep] |- _ =>
      let KS := fresh "KS" in
      assert (KS : keep (rw_cells segs mm A1 [CB 8 sg; CB 16 rep]))
        by exact (rw_cells_join_at mm A1 (A1 + 8) [CB 8 sg] [CB 16 rep] HS HR ltac:(cbn; lia));
      clear HS
  end;
  do 3 zstep;
  do 16 (zstep; zstep; try br; zstep; zstep; zstep; try br);
  do 8 zstep;
  let F1 := fresh "F1" in let F2 := fresh "F2" in let F3 := fresh "F3" in
  pose proof (rw_cells_join_at _ _ _ _ _ FRj FRd ltac:(cbn; lia)) as F1;
  pose proof (rw_cells_join_at _ _ _ _ _ F1 FRw ltac:(cbn; lia)) as F2;
  pose proof (rw_cells_join_at _ _ _ _ _ F2 FR ltac:(cbn; lia)) as F3;
  cbn [app] in F3;
  release_frame F3 ST (bv_unsigned sp);
  lazymatch goal with K : keep _ |- _ => unfold keep in K end;
  finish;
  do 2 eexists; split; eassumption.

Ltac split_pre := repeat match goal with |- _ /\ _ => split end.

Theorem check_text_counter_holds :
  owed_counter_text_contract -> memset_contract -> diginet_counter_text_contract -> bcmp_contract ->
  check_text_counter_contract.
Proof.
  intros HOW HMS HDC HBC.
  unfold owed_counter_text_contract, OWED_COUNTER_TEXT, OWED_COUNTER_TEXT_DEPTH in HOW.
  unfold diginet_counter_text_contract, DIGINET_COUNTER_TEXT, DIGINET_COUNTER_TEXT_DEPTH in HDC.
  unfold memset_contract, MEMSET in HMS.
  unfold bcmp_contract, BCMP in HBC.
  unfold check_text_counter_contract, check_text_counter_pre, CHECK_TEXT_COUNTER, CHECK_TEXT_COUNTER_DEPTH.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo tb sj dj
    (HA0 & [HTB HIN] & HA1 & HSG & HA2 & HDT & DJ12 & DJ01 & DJ02 & RI & D3 & SP0 & SP1 & SP2 & HMI & ST & LO & AG).
  unfold disj in DJ12, DJ01, DJ02.
  revert AG.
  destruct (counter_text_spec (zb tb)) as [[r1 g1] d1] eqn:E1.
  destruct (owed_counter_text_spec (zb tb)) as [[r2 g2] d2] eqn:E2.
  intros [R12 AG]. subst r1.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. pose proof (bv_unsigned_in_range 64 a0) as Ra0.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
  unfold bv_modulus in Rsp, Ra0, Ra1, Ra2.
  pose proof ST as [Hlo _].
  pose proof (rw_cells_bound rsegs m _ _ HSG) as BSG. pose proof (rw_cells_bound rsegs m _ _ HDT) as BDT.
  pose proof (bytes_at_bound rsegs m _ _ HTB) as BTB.
  cbn [cells_size csize Nat.add] in BSG, BDT.
  assert (MU0 : munch [(bv_unsigned sp - 192, bv_unsigned sp)] m m) by apply munch_refl.
  assert (MU : munch [(bv_unsigned sp - 192, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + 24);
                      (bv_unsigned a2, bv_unsigned a2 + 1)] m m) by apply munch_refl.
  assert (WM : wmono rsegs m m) by apply wmono_refl.
  (* prologue: frame 0x40, saves s4..s0 and ra, want_dots = 0 at sp' + 7, then owed_counter_text(text, sp' + 8, sp' + 7) *)
  carve_frame 64%nat ST.
  do 14 zstep.
  rewrite le1_zero.
  lazymatch type of FR with rw_cells _ ?mm ?A ?cs => split_for_access FR rsegs mm A cs 7%nat 1%nat end.
  mem_after_store.
  peel FR FRj. peel FR FRd. peel FR FRw.
  replace (bv_unsigned sp + -64 + Z.of_nat 7) with (bv_unsigned sp + -57) in FRd by lia.
  replace (bv_unsigned sp + -64 + Z.of_nat 7 + Z.of_nat 1) with (bv_unsigned sp + -56) in FRw by lia.
  replace (bv_unsigned sp + -64 + Z.of_nat 7 + Z.of_nat 1 + Z.of_nat 8) with (bv_unsigned sp + -48) in FR by lia.
  assert (U64 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  assert (U56 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -56)) = bv_unsigned sp + -56) by (apply unsigned_lit; lia).
  assert (U57 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -57)) = bv_unsigned sp + -57) by (apply unsigned_lit; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (RI1 : relro_img mm)
      by (eapply relro_img_munch; [exact RI | exact MU0 |];
          cbn [disjoint_from]; unfold disj, RELRO_BASE, RELRO_LEN in *; split; [lia | exact I])
  end.
  clear MU0 RI.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply HOW with (lo := lo) (tb := tb);
      unfold owed_counter_text_pre, OWED_COUNTER_TEXT_DEPTH; rewrite ?U64, ?U56, ?U57;
      split_pre; try first [ eassumption | lia | (split; eassumption) | (unfold disj in *; lia) ]
    | post_call rsegs mm ]
  end.
  clear RI1.
  match goal with H : stk _ _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite U64 in H; rename H into ST end.
  rewrite E2 in POST. destruct POST as (Ex & HOK & HNO). subst.
  (* want_seg / want_dots after the owed call: on rc = 0 the owed digits and dots *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (WANT : exists wsg wdv, rw_cells rsegs mm (bv_unsigned sp + -56) [CB 8 wsg] /\
                     rw_cells rsegs mm (bv_unsigned sp + -57) [C1 wdv] /\ (r2 = 0 -> wsg = bz g2 /\ wdv = b8 d2))
  end.
  { destruct (Z.eq_dec r2 0) as [R0|R0].
    - destruct (HOK R0) as [W1 W2]. rewrite U56 in W1. rewrite U57 in W2.
      exists (bz g2), (b8 d2). split; [exact W1|]. split; [exact W2|]. intros; split; reflexivity.
    - destruct (HNO R0) as (sg' & dv & W1 & W2). rewrite U56 in W1. rewrite U57 in W2.
      exists sg', dv. split; [exact W1|]. split; [exact W2|]. intros; contradiction. }
  destruct WANT as (wsg & wdv & FRw & FRd & WOK). clear HOK HNO.
  (* memset(seg, 0xa5, 24) *)
  do 6 zstep.
  assert (U24 : bv_unsigned (Z_to_bv 64 24) = 24) by reflexivity.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply HMS;
      [ change (Z.to_nat (bv_unsigned (Z_to_bv 64 24))) with 24%nat; eassumption | eassumption ]
    | post_call rsegs mm ]
  end.
  clear U24.
  change (Z.to_nat (bv_unsigned (Z_to_bv 64 24))) with 24%nat in POST.
  change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 165) mod 256)) with (b8 165) in POST.
  lazymatch type of POST with rw_cells _ ?mm _ _ =>
    pose proof (rw_cells_split_CB rsegs mm (bv_unsigned a1) [] 24 (repeat (b8 165) 24) [] [8%nat; 16%nat] POST eq_refl)
      as HSG16
  end.
  change ([] ++ mk_CB_cells [8%nat; 16%nat] (repeat (b8 165) 24) ++ [])
    with [CB 8 (repeat (b8 165) 8); CB 16 (repeat (b8 165) 16)] in HSG16.
  clear POST.
  peel HSG16 HSG8.
  replace (bv_unsigned a1 + Z.of_nat 8) with (bv_unsigned a1 + 8) in HSG16 by lia.
  (* *dots = 0xa5 *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (SOK : store_ok rsegs mm a2 1 = true)
      by (eapply (rw_cells_store_ok_at rsegs mm (bv_unsigned a2) [C1 dj] 0 (C1 dj) 1 a2 HDT);
          [reflexivity | reflexivity | addr_eq_tac])
  end.
  zstep.
  clear SOK.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm a2 ?bs) _) =>
    replace (write_to_mem mm a2 bs) with (write_to_mem mm (wa (bv_unsigned a2 + Z.of_nat 0)) [b8 165])
      by (rewrite le1_a5; f_equal; first [apply wa_of_var | symmetry; apply wa_of_var]; lia)
  end.
  mem_after_store.
  (* diginet_counter_text(text, seg, dots) *)
  do 4 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply HDC with (lo := lo) (tb := tb);
      unfold diginet_counter_text_pre, DIGINET_COUNTER_TEXT_DEPTH; rewrite ?U64;
      split_pre; try first [ eassumption | lia | (split; eassumption) | (unfold disj; lia) ]
    | post_call rsegs mm ]
  end.
  match goal with H : stk _ _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite U64 in H; rename H into ST end.
  rewrite E1 in POST. destruct POST as (Ex & HOK & HNO). subst.
  (* rc != want: both are owed_counter_text_spec's rc (agreement premise) *)
  zstep. if_false.
  destruct (owed_rc _ _ _ _ E2) as [R0 | R0]; subst r2.
  - (* both return 0: compare the digits (bcmp) and the dots *)
    destruct (HOK eq_refl) as [HS8 HD1]. clear HOK HNO.
    destruct (AG eq_refl) as [Eg Ed]. subst g2 d2.
    destruct (WOK eq_refl) as [Ew Ed']. subst wsg wdv. clear AG WOK.
    pose proof (rw_cells_CB_len _ _ _ _ HS8) as L8.
    zstep. try br.
    do 4 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply HBC with (ls := bz g1) (rs := bz g1) (v := 0);
        [ eapply rw_cells_CB_bytes; exact HS8
        | rewrite U56; eapply rw_cells_CB_bytes; exact FRw
        | change (Z.to_nat (bv_unsigned (Z_to_bv 64 8))) with 8%nat; apply memcmp_model_self; lia
        | eassumption ]
      | post_call rsegs mm ]
    end.
    zstep. try br.
    zstep. zstep. zstep. try br.
    ctc_tail FRj FRd FRw FR ST sp.
  - (* both return E_RANGE: bnez skips the comparisons *)
    destruct (HNO ltac:(unfold E_RANGE; lia)) as (sg' & dv & HS8 & HD1). clear HOK HNO AG WOK.
    zstep. try br.
    ctc_tail FRj FRd FRw FR ST sp.
Qed.
