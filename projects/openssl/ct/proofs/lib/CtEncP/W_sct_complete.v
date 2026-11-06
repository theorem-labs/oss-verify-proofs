(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OSSVerify.Proofs.openssl.ct.lib.Malloc Require Import MallocRep.
From OSSVerify.Proofs.openssl.ct.lib.CtP Require Import Layout Lib_kit Printf_lib.
From OSSVerify.Proofs.openssl.ct.lib.CtBnP Require Import BnKit.
From OSSVerify.Proofs.openssl.ct.lib.CtRepP Require Import ApCells ApRepDefs ApWalkTac.
From OSSVerify.Proofs.openssl.ct.lib.CtSctP Require Import SctDefs W_sct_list_free SctRep W_sct_leaves.
From OSSVerify.Proofs.openssl.ct.lib.CtEncP Require Import EncPure EncStmt.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling. Context {CE__ : Ceiling}.

Definition leaf16_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) (r : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctpsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono ctpsegs m m' /\ mem_inv ctpsegs m'
    /\ stk ctpsegs m' lo (bv_unsigned sp).

Lemma SCT_signature_is_complete_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (adr : bptr -> Z) (x : sctr bptr) (vs : Z),
  stk ctpsegs m lo (bv_unsigned sp) -> mem_inv ctpsegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 16 ->
  0 < adr (sc_blk x) -> adr (sc_blk x) + SCT_SIZE <= lo ->
  rw_cells ctpsegs m (adr (sc_blk x)) (sct_cells adr x (-1) vs) -> sct_ok adr x ->
  a0 = Z_to_bv 64 (adr (sc_blk x)) ->
  evt ctpsegs (leaf16_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m (bret (sct_sig_complete x)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SCT_SIGNATURE_IS_COMPLETE) fc None m (seg_rom ctpsegs)).
Proof.
  intros until vs. intros ST MI GLO LO A0 ALO HX OK ->. unfold GLOBALS_TOP in GLO. unfold SCT_SIGNATURE_IS_COMPLETE, SCT_SIZE in *.
  destruct OK as (VR & HR & GR & SIGP & BLOBP & LOGP & ELR & BLR & EXTP & EXTL & BLBL).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctpsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold sct_cells in HX. unfold MallocRep.wz, u32 in HX.
  carve_frame 16%nat ST. do 4 zstep.
  (* [comment removed for export] *)
  assert (RES : bret (sct_sig_complete x)
                = if (sc_version x =? 0) && (sc_hash x =? 4) && ((sc_sigalg x =? 1) || (sc_sigalg x =? 3))
                  then (match sc_sig x with Some _ => (if sc_siglen x =? 0 then 0 else 1) | None => 0 end) else 0).
  { unfold bret, sct_sig_complete, sct_nid, sig_nid, NID_undef, NID_ecdsa_with_SHA256, NID_sha256WithRSAEncryption.
    destruct (sc_version x =? 0); destruct (sc_hash x =? 4); destruct (sc_sigalg x =? 1) eqn:E1; destruct (sc_sigalg x =? 3) eqn:E3; cbn;
      try reflexivity; try lia; unfold sc_siglen; destruct (sc_sig x) as [[q n]|] eqn:ES; cbn; try reflexivity;
      (destruct (Z.ltb_spec0 0 n); destruct (Z.eqb_spec n 0); cbn; try reflexivity; exfalso; pose proof (SIGP q n eq_refl); lia). }
  rewrite RES. clear RES.
  Ltac ret0 FR ST sp := do 4 zstep; release_frame FR ST (bv_unsigned sp); zstep; finish.
  (* [comment removed for export] *)
  zstep. rewrite sx32_mod32 by lia.
  zstep. if_cases K; zify_cond K.
  { replace (sc_version x =? 0) with false by (symmetry; apply Z.eqb_neq; intros E0; apply K; rewrite E0; reflexivity). cbn [andb]. ret0 FR ST sp. }
  assert (V0 : sc_version x = 0).
  { destruct VR as [E0|VR']; [exfalso; revert K; rewrite E0; vm_compute; lia|].
    revert K. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones, Z.mod_small by lia. intros K. exact K. }
  rewrite V0. cbn [Z.eqb Pos.eqb andb].
  (* [comment removed for export] *)
  zstep. zstep. zstep. if_cases K1; zify_cond K1.
  { replace (sc_hash x =? 4) with false by (symmetry; apply Z.eqb_neq; intros E0; apply K1; rewrite E0; reflexivity). cbn [andb]. ret0 FR ST sp. }
  assert (H4 : sc_hash x = 4) by (revert K1; rewrite ?u8_lit by lia; intros K1; lia). rewrite H4. cbn [Z.eqb Pos.eqb andb].
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2.
  { rewrite <- (land253 (sc_sigalg x)) by lia.
    replace (Z.land (sc_sigalg x) 253 =? 1) with false by (symmetry; apply Z.eqb_neq; intros E0; apply K2; rewrite ?u8_lit by lia; rewrite E0; reflexivity).
    ret0 FR ST sp. }
  rewrite <- (land253 (sc_sigalg x)) by lia.
  replace (Z.land (sc_sigalg x) 253 =? 1) with true by (symmetry; apply Z.eqb_eq; revert K2; rewrite ?u8_lit by lia; intros K2; lia).
  (* [comment removed for export] *)
  zstep. zstep. if_cases K3; zify_cond K3.
  { destruct (sc_sig x) as [[q n]|] eqn:ES; [| ret0 FR ST sp]. exfalso. pose proof (SIGP q n eq_refl). cbn [optr] in K3. rewrite land64_small in K3 by lia. lia. }
  destruct (sc_sig x) as [[q n]|] eqn:ES; [| exfalso; apply K3; reflexivity]. pose proof (SIGP q n eq_refl) as [Q1 Q2].
  (* [comment removed for export] *)
  zstep. zstep. unfold sc_siglen. rewrite ES. replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [Z.eqb Pos.eqb andb].
  setreg 10%Z (Z_to_bv 64 1) ltac:(symmetry; rewrite ?land64_small by lia; replace (0 <? n) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
  zstep. do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep. finish.
Qed.

Lemma SCT_is_complete_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (adr : bptr -> Z) (x : sctr bptr) (vs : Z),
  stk ctpsegs m lo (bv_unsigned sp) -> mem_inv ctpsegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 16 ->
  0 < adr (sc_blk x) -> adr (sc_blk x) + SCT_SIZE <= lo ->
  rw_cells ctpsegs m (adr (sc_blk x)) (sct_cells adr x (-1) vs) -> sct_ok adr x ->
  a0 = Z_to_bv 64 (adr (sc_blk x)) ->
  evt ctpsegs (leaf16_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m (bret (sct_complete x)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SCT_IS_COMPLETE) fc None m (seg_rom ctpsegs)).
Proof.
  intros until vs. intros ST MI GLO LO A0 ALO HX OK ->. unfold GLOBALS_TOP in GLO. unfold SCT_IS_COMPLETE, SCT_SIZE in *.
  destruct OK as (VR & HR & GR & SIGP & BLOBP & LOGP & ELR & BLR & EXTP & EXTL & BLBL).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctpsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold sct_cells in HX. unfold MallocRep.wz, u32 in HX.
  carve_frame 16%nat ST. do 4 zstep.
  (* [comment removed for export] *)
  assert (RES : bret (sct_complete x)
                = if sc_version x =? -1 then 0
                  else if sc_version x =? 0 then
                    match sc_logid x with
                    | Some _ => if (sc_hash x =? 4) && ((sc_sigalg x =? 1) || (sc_sigalg x =? 3))
                                then match sc_sig x with Some _ => 1 | None => 0 end else 0
                    | None => 0 end
                  else match sc_blob x with Some _ => 1 | None => 0 end).
  { unfold bret, sct_complete, sct_sig_complete, sct_nid, sig_nid, NID_undef, NID_ecdsa_with_SHA256, NID_sha256WithRSAEncryption.
    destruct (sc_version x =? -1); [reflexivity|]. destruct (sc_version x =? 0); [| destruct (sc_blob x) as [[? ?]|]; reflexivity].
    destruct (sc_logid x) as [lq|]; [| reflexivity]. cbn [andb].
    destruct (sc_hash x =? 4); destruct (sc_sigalg x =? 1) eqn:E1; destruct (sc_sigalg x =? 3) eqn:E3; cbn;
      try reflexivity; try lia; unfold sc_siglen; destruct (sc_sig x) as [[q n]|] eqn:ES; cbn; try reflexivity;
      (destruct (Z.ltb_spec0 0 n); cbn; try reflexivity; exfalso; pose proof (SIGP q n eq_refl); lia). }
  rewrite RES. clear RES.
  Ltac ret_epi FR ST sp := do 3 zstep; release_frame FR ST (bv_unsigned sp); zstep; finish.
  Ltac ret0' FR ST sp := zstep; zstep; ret_epi FR ST sp.
  (* [comment removed for export] *)
  zstep. rewrite sx32_mod32 by lia. zstep.
  zstep. if_cases K; zify_cond K.
  { (* [comment removed for export] *)
    assert (VM : sc_version x = -1).
    { destruct VR as [E0|VR']; [exact E0|]. exfalso. revert K. rewrite land64_small by lia. lia. }
    rewrite VM. cbn [Z.eqb Pos.eqb]. ret0' FR ST sp. }
  assert (VR' : 0 <= sc_version x < 256).
  { destruct VR as [E0|VR']; [exfalso; apply K; rewrite E0; vm_compute; reflexivity| exact VR']. }
  clear K VR. replace (sc_version x =? -1) with false by (symmetry; apply Z.eqb_neq; lia).
  (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K.
  { replace (sc_version x =? 0) with false by (symmetry; apply Z.eqb_neq; intros E0; apply K; rewrite E0; reflexivity).
    (* [comment removed for export] *)
    zstep.
    destruct (sc_blob x) as [[bq bn]|] eqn:EB.
    - pose proof (BLOBP bq bn eq_refl) as BQ. cbn [optr]. zstep.
      setreg 10%Z (Z_to_bv 64 1) ltac:(symmetry; rewrite ?land64_small by lia; replace (0 <? adr bq) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
      ret_epi FR ST sp.
    - cbn [optr]. zstep. ret_epi FR ST sp. }
  assert (V0 : sc_version x = 0) by (revert K; rewrite ?land64_small by lia; intros K; lia).
  rewrite V0. cbn [Z.eqb Pos.eqb andb]. clear K.
  (* [comment removed for export] *)
  zstep. zstep. if_cases KL; zify_cond KL.
  { destruct (sc_logid x) as [lq|] eqn:EL; [| ret0' FR ST sp].
    exfalso. pose proof (LOGP lq eq_refl). cbn [osz32 option_map optr] in KL. rewrite land64_small in KL by lia. lia. }
  destruct (sc_logid x) as [lq|] eqn:EL; [| exfalso; apply KL; reflexivity]. clear KL.
  (* [comment removed for export] *)
  zstep. zstep. zstep. if_cases K1; zify_cond K1.
  { replace (sc_hash x =? 4) with false by (symmetry; apply Z.eqb_neq; intros E0; apply K1; rewrite E0; reflexivity). cbn [andb]. ret0' FR ST sp. }
  assert (H4 : sc_hash x = 4) by (revert K1; rewrite ?u8_lit by lia; intros K1; lia). rewrite H4. cbn [Z.eqb Pos.eqb andb]. clear K1.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2.
  { rewrite <- (land253 (sc_sigalg x)) by lia.
    replace (Z.land (sc_sigalg x) 253 =? 1) with false by (symmetry; apply Z.eqb_neq; intros E0; apply K2; rewrite ?u8_lit by lia; rewrite E0; reflexivity).
    ret0' FR ST sp. }
  rewrite <- (land253 (sc_sigalg x)) by lia.
  replace (Z.land (sc_sigalg x) 253 =? 1) with true by (symmetry; apply Z.eqb_eq; revert K2; rewrite ?u8_lit by lia; intros K2; lia). clear K2.
  (* [comment removed for export] *)
  zstep. zstep. if_cases K3; zify_cond K3.
  { destruct (sc_sig x) as [[q n]|] eqn:ES; [| ret0' FR ST sp]. exfalso. pose proof (SIGP q n eq_refl). cbn [optr] in K3. rewrite land64_small in K3 by lia. lia. }
  destruct (sc_sig x) as [[q n]|] eqn:ES; [| exfalso; apply K3; reflexivity]. pose proof (SIGP q n eq_refl) as [Q1 Q2]. clear K3.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  setreg 10%Z (Z_to_bv 64 1) ltac:(symmetry; unfold sc_siglen; rewrite ?ES; rewrite ?land64_small by lia; replace (0 <? n) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
  ret_epi FR ST sp.
Qed.
End WithCeiling.
