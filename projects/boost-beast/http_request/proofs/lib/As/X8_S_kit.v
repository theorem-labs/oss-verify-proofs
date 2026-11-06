(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require TP_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Bytes.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import XE_kit.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsImgSh AsIface AsCXXHeap AsWalk AsStack0 AXPres AXRep AXRep2.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import N8Kit N8Kit2 N8Kit3 X8Kit X8SRKit X8_stream_stmt.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac blk_rd AD MU WM WH a w RD :=
  lazymatch type of AD with addressable _ ?A ?n =>
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    let ADc := fresh "ADc" in
    assert (ADc : addressable mc A n) by (eapply addressable_transport_hi; [exact AD| exact MU| exact WM| unfold AAPP_HI; lia| exact WH]);
    pose proof (addressable_rd mc A n a w ADc ltac:(lia) ltac:(lia) ltac:(first [cbn; lia | Z.div_mod_to_equations; lia])) as RD; clear ADc
  end end.

(* [comment removed for export] *)
Ltac acc_rd AC MU WH a RD :=
  lazymatch type of AC with accessible _ ?O ?n =>
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    let ACc := fresh "ACc" in
    assert (ACc : accessible mc O n) by (eapply accessible_transport_hi; [exact AC| exact MU| exact WH]);
    pose proof (accessible_read0_sr mc O n a ACc ltac:(lia) ltac:(Z.div_mod_to_equations; lia) ltac:(lia)) as RD; clear ACc
  end end.

(* [comment removed for export] *)
Ltac acc_rd_fr AC MU WFR ff k SEPtac a RD :=
  lazymatch type of AC with accessible _ ?O ?n =>
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    let ACc := fresh "ACc" in
    assert (ACc : accessible mc O n) by (eapply (accessible_transport_fr _ _ mc O n ff k); [exact AC| exact MU| exact WFR| lia| lia| lia| SEPtac]);
    pose proof (accessible_read0_sr mc O n a ACc ltac:(lia) ltac:(Z.div_mod_to_equations; lia) ltac:(lia)) as RD; clear ACc
  end end.

(* [comment removed for export] *)
Ltac img_rd ACx a RD :=
  lazymatch type of ACx with ACONST ?mc =>
    let ACi := fresh "ACi" in
    pose proof (ACONST_img_accessible mc a 8 ACx ltac:(vm_compute; reflexivity)) as ACi;
    pose proof (accessible_read0_sr mc a 8 a ACi ltac:(lia) ltac:(reflexivity) ltac:(lia)) as RD; clear ACi
  end.

(* [comment removed for export] *)
Ltac sp_range sp :=
  let SPR := fresh "SPR" in
  pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; change (2 ^ Z.of_N 64) with (2^64) in SPR.

(* [comment removed for export] *)
Ltac set_a0 v :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let cur := eval cbv beta iota delta [tget mkR] in (tget 11%positive R) in
    lazymatch cur with Some ?c => replace c with v end end.

(* [comment removed for export] *)
Ltac if_tk := let K := fresh "K" in if_cases K;
  [ clear K | exfalso; zify_cond K; unfold wz in K; rewrite ?unsigned_lit in K by lia; first [lia | congruence] ].
Ltac if_nt := let K := fresh "K" in if_cases K;
  [ exfalso; zify_cond K; unfold wz in K; rewrite ?unsigned_lit in K by lia; first [lia | congruence] | clear K ].
(* [comment removed for export] *)
Ltac shchk_pre RD :=
  step; clear RD; try replace (zxb (b8 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity);
  try replace (sxb (b8 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity); shchk_br.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Lemma AImplBlockC_open : forall LB m b I, AImplBlockC LB m b I ->
  exists p j7, In (p, b, SZ_SPCI_IMPL) LB /\ rblock_range b SZ_SPCI_IMPL
  /\ rw_cells asegs m b (SpcHdrCells (im_hdr I) j7) /\ spc_ok (im_hdr I) /\ spc_vptr (im_hdr I) = AVP_SPCI_IMPL
  /\ APMutex m (b + 32) (im_lk I)
  /\ rw_cells asegs m (b + 72) [C8 (wz (im_vb I)); C8 (wz (im_vb I + 8 * zlength (im_states I))); C8 (wz (im_vb I + 8 * im_vcap I))]
  /\ zlength (im_states I) <= im_vcap I
  /\ ((im_vcap I = 0 /\ im_vb I = 0)
      \/ (exists q junk, In (q, im_vb I, 8 * im_vcap I) LB /\ rblock_range (im_vb I) (8 * im_vcap I) /\ 0 < im_vcap I
           /\ rw_cells asegs m (im_vb I) [CB (8 * length (im_states I)) (flat_map le8z (im_states I));
                                         CB (Z.to_nat (8 * (im_vcap I - zlength (im_states I)))) junk]
           /\ SHAD m (im_vb I) (cc_shadow (8 * im_vcap I) (8 * zlength (im_states I)))))
  /\ addressable m b SZ_SPCI_IMPL.
Proof.
  intros LB m b I (p & j7 & K). exists p, j7. unfold O_SPC_STORAGE, O_IMPL_MUTEX, O_IMPL_VEC_BEGIN in K.
  replace (b + 32 + 0) with (b + 32) in K by lia. replace (b + 32 + 40) with (b + 72) in K by lia. exact K.
Qed.
Lemma AImplBlockC_close : forall LB m b I p j7,
  In (p, b, SZ_SPCI_IMPL) LB -> rblock_range b SZ_SPCI_IMPL ->
  rw_cells asegs m b (SpcHdrCells (im_hdr I) j7) -> spc_ok (im_hdr I) -> spc_vptr (im_hdr I) = AVP_SPCI_IMPL ->
  APMutex m (b + 32) (im_lk I) ->
  rw_cells asegs m (b + 72) [C8 (wz (im_vb I)); C8 (wz (im_vb I + 8 * zlength (im_states I))); C8 (wz (im_vb I + 8 * im_vcap I))] ->
  zlength (im_states I) <= im_vcap I ->
  ((im_vcap I = 0 /\ im_vb I = 0)
      \/ (exists q junk, In (q, im_vb I, 8 * im_vcap I) LB /\ rblock_range (im_vb I) (8 * im_vcap I) /\ 0 < im_vcap I
           /\ rw_cells asegs m (im_vb I) [CB (8 * length (im_states I)) (flat_map le8z (im_states I));
                                         CB (Z.to_nat (8 * (im_vcap I - zlength (im_states I)))) junk]
           /\ SHAD m (im_vb I) (cc_shadow (8 * im_vcap I) (8 * zlength (im_states I))))) ->
  addressable m b SZ_SPCI_IMPL ->
  AImplBlockC LB m b I.
Proof.
  intros LB m b I p j7 IN RB CH OK EV PM CV LE ST AD. exists p, j7. unfold O_SPC_STORAGE, O_IMPL_MUTEX, O_IMPL_VEC_BEGIN.
  replace (b + 32 + 0) with (b + 32) by lia. replace (b + 32 + 40) with (b + 72) by lia. repeat (split; [assumption|]). exact AD.
Qed.

(* [comment removed for export] *)
Lemma cc_shadow_rd0 : forall m vb len mid,
  SHAD m vb (cc_shadow len mid) -> 8 <= mid -> 0 <= vb ->
  ov_read_bytes asegs m (Z_to_bv 64 (Z.shiftr vb 3 + 2147450880)) 1 = Some [b8 0].
Proof.
  intros m vb len mid SH Hm Hv. eapply (SHAD_read m vb _ 0); [exact SH| | lia|].
  - unfold cc_shadow, poison_bytes. rewrite nth_error_app1 by (rewrite repeat_length; Z.div_mod_to_equations; lia).
    apply nth_error_repeat. Z.div_mod_to_equations; lia.
  - unfold wa. rewrite Z.add_0_r. rewrite <- (sh_shiftr vb Hv). rewrite ASHADOW_BASE_val. reflexivity.
Qed.

Lemma wins_hi_stack1 : forall l h, aceil <= l -> wins_hi [(l, h)]%Z.
Proof. intros l h Hl. pose proof aceil_facts as (AF & _). constructor; [right; cbn; unfold AHI_LO; lia| constructor]. Qed.

(* [comment removed for export] *)
Lemma acc_after_stack' : forall l h m mx a n, accessible m a n -> munch [(l, h)]%Z m mx -> aceil <= l -> accessible mx a n.
Proof.
  intros l h m mx a n AC MU Hl. eapply accessible_transport_hi; [exact AC| exact MU|].
  pose proof aceil_facts as (AF & _). constructor; [right; cbn; unfold AHI_LO; lia| constructor].
Qed.

(* [comment removed for export] *)
Lemma AFlatBuf_shape : forall LB m a F ds, AFlatBuf LB m a F ds ->
  0 <= fb_begin F /\ fb_begin F <= fb_in F <= fb_out F /\ fb_out F <= fb_last F <= fb_end F /\ fb_end F <= aceil
  /\ (F = FB_empty \/ (0 < fb_begin F /\ fb_begin F mod 16 = 0 /\ 0 < fb_cap F /\ aapp (fb_begin F) (fb_cap F)
                       /\ exists p, In (p, fb_begin F, fb_cap F) LB)).
Proof.
  intros LB m a F ds (_ & OK & _ & _). pose proof aceil_facts as (AF & _).
  destruct OK as [-> | (p & IN & RB & CP & S1 & S2)]; unfold fb_cap in *; cbn in *.
  - repeat split; cbn; try lia. left; reflexivity.
  - pose proof RB as (R1 & R2 & R3 & R4 & R5). pose proof (rblock_bounds _ _ RB) as (B1 & B2 & B3 & B4 & B5 & B6).
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. right.
    split; [lia|]. split; [exact R2|]. split; [lia|]. split; [exact R4|]. exists p. exact IN.
Qed.

(* [comment removed for export] *)
Lemma cc_shadow_8_0 : cc_shadow 8 0 = [b8 0xfc].
Proof. reflexivity. Qed.
Lemma cc_shadow_8_8 : cc_shadow 8 8 = [b8 0].
Proof. reflexivity. Qed.

End HCW.
