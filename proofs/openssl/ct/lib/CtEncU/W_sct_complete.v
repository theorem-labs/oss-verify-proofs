(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_kit Printf_lib.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApWalkTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctDefs W_sct_list_free SctRep W_sct_leaves.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncU Require Import EncPure EncStmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling. Context {CE__ : Ceiling}.

Definition leaf16_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) (r : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
    /\ stk ctusegs m' lo (bv_unsigned sp).

Definition leaf48_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) (r : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
    /\ stk ctusegs m' lo (bv_unsigned sp).

Lemma SCT_get_signature_nid_specU : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (adr : bptr -> Z) (x : sctr bptr) (vs : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 16 ->
  0 < adr (sc_blk x) -> adr (sc_blk x) + SCT_SIZE <= lo -> adr (sc_blk x) mod 8 = 0 ->
  rw_cells ctusegs m (adr (sc_blk x)) (sct_cells adr x (-1) vs) -> sct_ok adr x ->
  a0 = Z_to_bv 64 (adr (sc_blk x)) ->
  evt ctusegs (leaf16_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m (sct_nid x))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SCT_GET_SIGNATURE_NID) fc None m (seg_rom ctusegs)).
Proof.
  intros until vs. intros ST MI GLO LO A0 ALO AL8 HX OK ->. unfold GLOBALS_TOP in GLO. unfold SCT_GET_SIGNATURE_NID, SCT_SIZE in *.
  destruct OK as (VR & HR & GR & SIGP & BLOBP & LOGP & ELR & BLR & EXTP & EXTL & BLBL).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold sct_cells in HX. unfold MallocRep.wz, u32 in HX.
  assert (RES : sct_nid x = if (sc_version x =? 0) && (sc_hash x =? 4) then (if sc_sigalg x =? 3 then 794 else if sc_sigalg x =? 1 then 668 else 0) else 0).
  { unfold sct_nid, sig_nid, NID_undef, NID_ecdsa_with_SHA256, NID_sha256WithRSAEncryption. reflexivity. }
  rewrite RES. clear RES.
  carve_frame 16%nat ST. do 4 zstep.
  Ltac nid_epi FR ST sp := do 3 zstep; release_frame FR ST (bv_unsigned sp); zstep; finish.
  ub. zstep. rewrite sx32_mod32 by lia.
  zstep. if_cases K; zify_cond K.
  { replace (sc_version x =? 0) with false by (symmetry; apply Z.eqb_neq; intros E0; apply K; rewrite E0; reflexivity). cbn [andb]. zstep. nid_epi FR ST sp. }
  assert (V0 : sc_version x = 0).
  { destruct VR as [E0|VR']; [exfalso; revert K; rewrite E0; vm_compute; lia|].
    revert K. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones, Z.mod_small by lia. intros K. exact K. }
  rewrite V0. cbn [Z.eqb Pos.eqb andb]. clear K.
  zstep. zstep. zstep. if_cases K1; zify_cond K1.
  { replace (sc_hash x =? 4) with false by (symmetry; apply Z.eqb_neq; intros E0; apply K1; rewrite E0; reflexivity). zstep. nid_epi FR ST sp. }
  assert (H4 : sc_hash x = 4) by (revert K1; rewrite ?u8_lit by lia; intros K1; lia). rewrite H4. cbn [Z.eqb Pos.eqb andb]. clear K1.
  zstep. zstep. zstep. if_cases K2; zify_cond K2.
  { replace (sc_sigalg x =? 3) with false by (symmetry; apply Z.eqb_neq; intros E0; apply K2; rewrite ?u8_lit by lia; rewrite E0; reflexivity).
    zstep. zstep. zstep. zstep.
    setreg 10%Z (Z_to_bv 64 (if sc_sigalg x =? 1 then 668 else 0))
      ltac:(symmetry; apply bv_eq; rewrite (u8_lit (sc_sigalg x)) by lia; destruct (Z.eq_dec (sc_sigalg x) 1) as [E1|NE1];
              [rewrite E1; vm_compute; reflexivity
              | rewrite (proj2 (Z.eqb_neq (sc_sigalg x) 1) NE1);
                replace (0 <? Z.land (sc_sigalg x + -1) 18446744073709551615) with true
                  by (symmetry; apply Z.ltb_lt; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia;
                      destruct (Z.eq_dec (sc_sigalg x) 0) as [E0|NE0]; [rewrite E0; vm_compute; reflexivity| rewrite Z.mod_small by lia; lia]);
                cbn [Z.b2z]; rewrite ?Z.land_0_l; reflexivity]).
    zstep. nid_epi FR ST sp. }
  assert (G3 : sc_sigalg x = 3) by (revert K2; rewrite ?u8_lit by lia; intros K2; lia). rewrite G3. cbn [Z.eqb Pos.eqb].
  zstep. zstep. nid_epi FR ST sp.
Qed.

Lemma SCT_signature_is_complete_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (adr : bptr -> Z) (x : sctr bptr) (vs : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 48 ->
  0 < adr (sc_blk x) -> adr (sc_blk x) + SCT_SIZE <= lo -> adr (sc_blk x) mod 8 = 0 ->
  rw_cells ctusegs m (adr (sc_blk x)) (sct_cells adr x (-1) vs) -> sct_ok adr x ->
  a0 = Z_to_bv 64 (adr (sc_blk x)) ->
  evt ctusegs (leaf48_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m (bret (sct_sig_complete x)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SCT_SIGNATURE_IS_COMPLETE) fc None m (seg_rom ctusegs)).
Proof.
  intros until vs. intros ST MI GLO LO A0 ALO AL8 HX OK ->. unfold GLOBALS_TOP in GLO. unfold SCT_SIGNATURE_IS_COMPLETE, SCT_SIZE in *.
  pose proof OK as OK0. destruct OK as (VR & HR & GR & SIGP & BLOBP & LOGP & ELR & BLR & EXTP & EXTL & BLBL).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold sct_cells in HX. unfold MallocRep.wz, u32 in HX.
  assert (RES : bret (sct_sig_complete x)
                = if sct_nid x =? 0 then 0 else (match sc_sig x with Some _ => (if sc_siglen x =? 0 then 0 else 1) | None => 0 end)).
  { unfold bret, sct_sig_complete, NID_undef. destruct (sct_nid x =? 0); cbn [negb andb]; [reflexivity|].
    unfold sc_siglen; destruct (sc_sig x) as [[q n]|] eqn:ES; cbn; [| reflexivity].
    destruct (Z.ltb_spec0 0 n); destruct (Z.eqb_spec n 0); cbn; try reflexivity; exfalso; pose proof (SIGP q n eq_refl); lia. }
  rewrite RES. clear RES.
  assert (NIDR : sct_nid x = 0 \/ sct_nid x = 668 \/ sct_nid x = 794).
  { unfold sct_nid, sig_nid, NID_undef, NID_ecdsa_with_SHA256, NID_sha256WithRSAEncryption.
    destruct (_ && _); [| left; reflexivity]. destruct (sc_sigalg x =? 3); [right; right; reflexivity|]. destruct (sc_sigalg x =? 1); [right; left; reflexivity| left; reflexivity]. }
  assert (ESP32 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  carve_frame 32%nat ST. do 6 zstep.
  zstep.
  eapply evt_cut.
  { change (Z_to_bv 64 1693340) with (Z_to_bv 64 SCT_GET_SIGNATURE_NID).
    eapply SCT_get_signature_nid_specU with (lo := lo) (adr := adr) (x := x) (vs := vs); rewrite ?ESP32;
      [exact ST| assumption| unfold GLOBALS_TOP; lia| lia| exact A0| exact ALO| exact AL8| exact HX| exact OK0| reflexivity]. }
  cbv beta. intros ms2 PO.
  destruct PO as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m2 & -> & MU2 & WM2 & MI2 & ST2). rewrite ?ESP32 in MU2, ST2.
  replace (ret_pc (Z_to_bv 64 1693584)) with (Z_to_bv 64 1693584) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  clear ST. rename ST2 into ST.
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in FR; [| cbn; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in HX; [| cbn; lia].
  assert (MU' : munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m2).
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp. cbn [outside]. intros y Hy. lia. }
  assert (WM' : wmono ctusegs m m2) by (eapply wmono_trans; [exact WM| exact WM2]).
  clear MU WM MU2 WM2. rename MU' into MU. rename WM' into WM.
  Ltac sig_epi FR ST sp := do 4 zstep; release_frame FR ST (bv_unsigned sp); zstep; finish.
  zstep. if_cases K; zify_cond K.
  { replace (sct_nid x =? 0) with true by (symmetry; apply Z.eqb_eq; revert K; rewrite ?unsigned_lit by (clear - NIDR; lia); clear - NIDR; intros K; lia).
    setreg 10%Z (Z_to_bv 64 0) ltac:(symmetry; apply bv_eq; revert K; rewrite ?unsigned_lit by (clear - NIDR; lia); intros K; rewrite ?unsigned_lit by (clear - NIDR; lia); clear - K NIDR; lia).
    sig_epi FR ST sp. }
  replace (sct_nid x =? 0) with false by (symmetry; apply Z.eqb_neq; revert K; rewrite ?unsigned_lit by (clear - NIDR; lia); clear - NIDR; intros K; lia). clear K.
  ub. zstep. zstep. if_cases K3; zify_cond K3.
  { destruct (sc_sig x) as [[q n]|] eqn:ES; [| sig_epi FR ST sp]. exfalso. pose proof (SIGP q n eq_refl). cbn [optr] in K3. rewrite land64_small in K3 by lia. lia. }
  destruct (sc_sig x) as [[q n]|] eqn:ES; [| exfalso; apply K3; reflexivity]. pose proof (SIGP q n eq_refl) as [Q1 Q2]. clear K3.
  zstep. zstep. unfold sc_siglen. rewrite ES. replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  setreg 10%Z (Z_to_bv 64 1) ltac:(symmetry; rewrite ?land64_small by lia; replace (0 <? n) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
  sig_epi FR ST sp.
Qed.

Lemma SCT_is_complete_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (adr : bptr -> Z) (x : sctr bptr) (vs : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 48 ->
  0 < adr (sc_blk x) -> adr (sc_blk x) + SCT_SIZE <= lo -> adr (sc_blk x) mod 8 = 0 ->
  rw_cells ctusegs m (adr (sc_blk x)) (sct_cells adr x (-1) vs) -> sct_ok adr x ->
  a0 = Z_to_bv 64 (adr (sc_blk x)) ->
  evt ctusegs (leaf48_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m (bret (sct_complete x)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SCT_IS_COMPLETE) fc None m (seg_rom ctusegs)).
Proof.
  intros until vs. intros ST MI GLO LO A0 ALO AL8 HX OK ->. unfold GLOBALS_TOP in GLO. unfold SCT_IS_COMPLETE, SCT_SIZE in *.
  pose proof OK as OK0. destruct OK as (VR & HR & GR & SIGP & BLOBP & LOGP & ELR & BLR & EXTP & EXTL & BLBL).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold sct_cells in HX. unfold MallocRep.wz, u32 in HX.
  carve_frame 16%nat ST. do 4 zstep.
  (* [comment removed for export] *)
  assert (RES : bret (sct_complete x)
                = if sc_version x =? -1 then 0
                  else if sc_version x =? 0 then
                    match sc_logid x with Some _ => bret (sct_sig_complete x) | None => 0 end
                  else match sc_blob x with Some _ => 1 | None => 0 end).
  { unfold bret, sct_complete. destruct (sc_version x =? -1); [reflexivity|]. destruct (sc_version x =? 0); [| destruct (sc_blob x) as [[? ?]|]; reflexivity].
    destruct (sc_logid x) as [lq|]; [| reflexivity]. cbn [andb]. reflexivity. }
  rewrite RES. clear RES.
  Ltac ret_epi FR ST sp := do 3 zstep; release_frame FR ST (bv_unsigned sp); zstep; finish.
  Ltac ret0' FR ST sp := zstep; zstep; ret_epi FR ST sp.
  (* [comment removed for export] *)
  ub. zstep. rewrite sx32_mod32 by lia. zstep.
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
  do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctusegs m m1 |- _ => rename H into WM1 end.
  match goal with H : mem_inv ctusegs m1 |- _ => rename H into MI1 end.
  eapply evt_cut.
  { change (Z_to_bv 64 1693556) with (Z_to_bv 64 SCT_SIGNATURE_IS_COMPLETE).
    eapply SCT_signature_is_complete_spec with (lo := lo) (adr := adr) (x := x) (vs := vs);
      [exact ST| exact MI1| unfold GLOBALS_TOP; lia| exact LO| exact A0| exact ALO| exact AL8| rewrite <- EL in HX; exact HX| exact OK0| reflexivity]. }
  cbv beta. intros ms2 PO.
  destruct PO as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m2 & -> & MU2 & WM2 & MI2 & ST2).
  pose proof (munch_trans _ _ _ _ MU1 MU2) as MU12. pose proof (wmono_trans _ _ _ _ WM1 WM2) as WM12. clear MU1 WM1 MU2 WM2.
  finish.
Qed.
End WithCeiling.
