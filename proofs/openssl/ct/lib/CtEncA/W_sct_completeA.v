(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire ApBase ApState ApOwner.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit R_cache_defs R_prim_defs R_sec_defs D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA AsStruct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs ApRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require W_sct_list_free SctRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncP Require Import EncPure.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncA Require Import EncStmtA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
(* [comment removed for export] *)
Ltac hshload :=
  let ad := cur_mem_addr in let X := ab_X ad in
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>
    match goal with
    | ACC : acc segs ?mb ?a ?n, MU : munch ?W ?mb mc |- _ =>
        let RD := fresh "RDsh" in
        pose proof (acc_rdG segs W mb mc a n X ad ACC MU ltac:(ab_off) ltac:(ab_alia) ltac:(ab_alia) ltac:(ab_alia) ltac:(ab_alia) ltac:(ab_addr)) as RD;
        OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step; clear RD
    end end.
Ltac hchk := hshload; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step; rewrite ?zxb_z8, ?sxb_z8; if_false.

Lemma u8_lit : forall z : Z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn. apply Z.mod_small. lia. Qed.

Definition SCT_GET_SIGNATURE_NID_B : Z := 0x33783c.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Definition leafN_postA (n : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) (r : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctasegs)
    /\ munch [(bv_unsigned sp - n, bv_unsigned sp)]%Z m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
    /\ stk ctasegs m' lo (bv_unsigned sp).
Definition leaf16_postA := leafN_postA 16.
Definition leaf48_postA := leafN_postA 48.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma SCT_get_signature_nid_specB : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z) (adr : bptr -> Z) (sc : sctr bptr) (vs : Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> ACEIL <= lo -> lo <= bv_unsigned sp - 16 ->
  In (sc_blk sc, adr (sc_blk sc), SCT_SIZE) (OW ++ LB) -> adr (sc_blk sc) mod 16 = 0 ->
  rw_cells ctasegs m (adr (sc_blk sc)) (sct_cells adr sc (-1) vs) -> sct_ok adr sc ->
  a0 = Z_to_bv 64 (adr (sc_blk sc)) ->
  evt ctasegs (leafN_postA 16 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m (sct_nid sc))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SCT_GET_SIGNATURE_NID_B) fc None m (seg_rom ctasegs)).
Proof.
  intros until vs. intros HEAP ST MI CEIL LO HIN AL16 HX OK ->.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HIN) as (B0 & _ & _ & BC & BI). cbn [blk_addr blk_size fst snd] in B0, BC, BI.
  ablock HEAP HIN ACC OFF.
  unfold SCT_GET_SIGNATURE_NID_B, SCT_SIZE, SEGTOP_A in *.
  destruct OK as (VR & HR & GR & SIGP & BLOBP & LOGP & ELR & BLR & EXTP & EXTL & BLBL).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFFW : offshW [(bv_unsigned sp - 16, bv_unsigned sp)]%Z) by (cbn [offshW]; alia).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (stk_below ctasegs m lo _ MI ST ltac:(lia)) as SPT. unfold UTOP in SPT.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (SEPX : adr (sc_blk sc) + 104 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= adr (sc_blk sc)) by alia.
  unfold sct_cells in HX. unfold MallocRep.wz, u32 in HX.
  (* [comment removed for export] *)
  assert (RES : sct_nid sc = if (sc_version sc =? 0) && (sc_hash sc =? 4) then (if sc_sigalg sc =? 3 then 794 else if sc_sigalg sc =? 1 then 668 else 0) else 0).
  { unfold sct_nid, sig_nid, NID_undef, NID_ecdsa_with_SHA256, NID_sha256WithRSAEncryption. reflexivity. }
  rewrite RES. clear RES.
  carve_frame 16%nat ST. do 4 zstep.
  Ltac epi FR ST sp := do 3 zstep; release_frame FR ST (bv_unsigned sp); zstep; finish.
  (* [comment removed for export] *)
  zstep. zstep. rewrite sx32_mod32 by lia.
  if_cases K; zify_cond K.
  { replace (sc_version sc =? 0) with false by (symmetry; apply Z.eqb_neq; intros E0; apply K; rewrite E0; reflexivity). cbn [andb]. zstep. epi FR ST sp. }
  assert (V0 : sc_version sc = 0).
  { destruct VR as [E0|VR']; [exfalso; revert K; rewrite E0; vm_compute; lia|].
    revert K. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones, Z.mod_small by lia. intros K. exact K. }
  rewrite V0. cbn [Z.eqb Pos.eqb andb]. clear K.
  (* [comment removed for export] *)
  zstep. zstep. zstep. if_cases K1; zify_cond K1.
  { replace (sc_hash sc =? 4) with false by (symmetry; apply Z.eqb_neq; intros E0; apply K1; rewrite E0; reflexivity). zstep. epi FR ST sp. }
  assert (H4 : sc_hash sc = 4) by (revert K1; rewrite ?u8_lit by lia; intros K1; lia). rewrite H4. cbn [Z.eqb Pos.eqb andb]. clear K1.
  (* [comment removed for export] *)
  zstep. zstep. zstep. if_cases K2; zify_cond K2.
  { (* [comment removed for export] *)
    replace (sc_sigalg sc =? 3) with false by (symmetry; apply Z.eqb_neq; intros E0; apply K2; rewrite ?u8_lit by lia; rewrite E0; reflexivity).
    zstep. zstep. zstep. zstep.
    setreg 10%Z (Z_to_bv 64 (if sc_sigalg sc =? 1 then 668 else 0))
      ltac:(symmetry; apply bv_eq; rewrite (u8_lit (sc_sigalg sc)) by lia; destruct (Z.eq_dec (sc_sigalg sc) 1) as [E1|NE1];
              [rewrite E1; vm_compute; reflexivity
              | rewrite (proj2 (Z.eqb_neq (sc_sigalg sc) 1) NE1);
                replace (0 <? Z.land (sc_sigalg sc + -1) 18446744073709551615) with true
                  by (symmetry; apply Z.ltb_lt; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia;
                      destruct (Z.eq_dec (sc_sigalg sc) 0) as [E0|NE0]; [rewrite E0; vm_compute; reflexivity| rewrite Z.mod_small by lia; lia]);
                cbn [Z.b2z]; rewrite ?Z.land_0_l; reflexivity]).
    zstep. epi FR ST sp. }
  assert (G3 : sc_sigalg sc = 3) by (revert K2; rewrite ?u8_lit by lia; intros K2; lia). rewrite G3. cbn [Z.eqb Pos.eqb].
  zstep. zstep. epi FR ST sp.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma SCT_signature_is_complete_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z) (adr : bptr -> Z) (sc : sctr bptr) (vs : Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> ACEIL <= lo -> lo <= bv_unsigned sp - 48 ->
  In (sc_blk sc, adr (sc_blk sc), SCT_SIZE) (OW ++ LB) -> adr (sc_blk sc) mod 16 = 0 ->
  rw_cells ctasegs m (adr (sc_blk sc)) (sct_cells adr sc (-1) vs) -> sct_ok adr sc ->
  a0 = Z_to_bv 64 (adr (sc_blk sc)) ->
  evt ctasegs (leaf48_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m (bret (sct_sig_complete sc)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SCT_SIGNATURE_IS_COMPLETE_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until vs. intros HEAP ST MI CEIL LO HIN AL16 HX OK ->.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HIN) as (B0 & _ & _ & BC & BI). cbn [blk_addr blk_size fst snd] in B0, BC, BI.
  ablock HEAP HIN ACC OFF.
  unfold SCT_SIGNATURE_IS_COMPLETE_A, SCT_SIZE, SEGTOP_A in *.
  pose proof OK as OK0. destruct OK as (VR & HR & GR & SIGP & BLOBP & LOGP & ELR & BLR & EXTP & EXTL & BLBL).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFFW : offshW [(bv_unsigned sp - 48, bv_unsigned sp)]%Z) by (cbn [offshW]; alia).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (stk_below ctasegs m lo _ MI ST ltac:(lia)) as SPT. unfold UTOP in SPT.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (SEPX : adr (sc_blk sc) + 104 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= adr (sc_blk sc)) by alia.
  unfold sct_cells in HX. unfold MallocRep.wz, u32 in HX.
  (* [comment removed for export] *)
  assert (RES : bret (sct_sig_complete sc)
                = if sct_nid sc =? 0 then 0 else (match sc_sig sc with Some _ => (if sc_siglen sc =? 0 then 0 else 1) | None => 0 end)).
  { unfold bret, sct_sig_complete, NID_undef. destruct (sct_nid sc =? 0); cbn [negb andb]; [reflexivity|].
    unfold sc_siglen; destruct (sc_sig sc) as [[q n]|] eqn:ES; cbn; [| reflexivity].
    destruct (Z.ltb_spec0 0 n); destruct (Z.eqb_spec n 0); cbn; try reflexivity; exfalso; pose proof (SIGP q n eq_refl); lia. }
  rewrite RES. clear RES.
  assert (NIDR : sct_nid sc = 0 \/ sct_nid sc = 668 \/ sct_nid sc = 794).
  { unfold sct_nid, sig_nid, NID_undef, NID_ecdsa_with_SHA256, NID_sha256WithRSAEncryption.
    destruct (_ && _); [| left; reflexivity]. destruct (sc_sigalg sc =? 3); [right; right; reflexivity|]. destruct (sc_sigalg sc =? 1); [right; left; reflexivity| left; reflexivity]. }
  assert (ESP32 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  (* [comment removed for export] *)
  carve_frame 16%nat ST. do 4 zstep.
  Ltac epiA FR ST sp := do 3 zstep; release_frame FR ST (bv_unsigned sp); zstep; finish.
  assert (NIDE : sct_nid sc = if (sc_version sc =? 0) && (sc_hash sc =? 4) then (if sc_sigalg sc =? 3 then 794 else if sc_sigalg sc =? 1 then 668 else 0) else 0).
  { unfold sct_nid, sig_nid, NID_undef, NID_ecdsa_with_SHA256, NID_sha256WithRSAEncryption. reflexivity. }
  rewrite NIDE. clear NIDE NIDR.
  zstep. zstep. rewrite sx32_mod32 by lia.
  if_cases K; zify_cond K.
  { replace (sc_version sc =? 0) with false by (symmetry; apply Z.eqb_neq; intros E0; apply K; rewrite E0; reflexivity). cbn [andb Z.eqb]. zstep. epiA FR ST sp. }
  assert (V0 : sc_version sc = 0).
  { destruct VR as [E0|VR']; [exfalso; revert K; rewrite E0; vm_compute; lia|].
    revert K. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones, Z.mod_small by lia. intros K. exact K. }
  rewrite V0. cbn [Z.eqb Pos.eqb andb]. clear K.
  zstep. zstep. zstep. if_cases K1; zify_cond K1.
  { replace (sc_hash sc =? 4) with false by (symmetry; apply Z.eqb_neq; intros E0; apply K1; rewrite E0; reflexivity). cbn [andb Z.eqb]. zstep. epiA FR ST sp. }
  assert (H4 : sc_hash sc = 4) by (revert K1; rewrite ?u8_lit by lia; intros K1; lia). rewrite H4. cbn [Z.eqb Pos.eqb andb]. clear K1.
  zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2.
  { replace (if sc_sigalg sc =? 3 then 794 else if sc_sigalg sc =? 1 then 668 else 0) with 0
      by (destruct (Z.eqb_spec (sc_sigalg sc) 3) as [E3|N3]; [exfalso; apply K2; rewrite ?u8_lit by lia; rewrite E3; reflexivity|];
          destruct (Z.eqb_spec (sc_sigalg sc) 1) as [E1|N1]; [exfalso; apply K2; rewrite ?u8_lit by lia; rewrite E1; reflexivity| reflexivity]).
    cbn [Z.eqb]. zstep. epiA FR ST sp. }
  assert (G13 : sc_sigalg sc = 1 \/ sc_sigalg sc = 3).
  { revert K2. rewrite ?u8_lit by lia. intros K2. assert (KL : Z.land (sc_sigalg sc) 253 = 1) by lia.
    pose proof (land253 (sc_sigalg sc) ltac:(lia)) as LL. rewrite KL, Z.eqb_refl in LL.
    symmetry in LL. apply orb_true_iff in LL. destruct LL as [LL|LL]; apply Z.eqb_eq in LL; [left|right]; exact LL. }
  replace ((if sc_sigalg sc =? 3 then 794 else if sc_sigalg sc =? 1 then 668 else 0) =? 0) with false
    by (destruct G13 as [E|E]; rewrite E; reflexivity). clear K2.
  zstep. zstep. if_cases K3; zify_cond K3.
  { destruct (sc_sig sc) as [[q n]|] eqn:ES; [| zstep; epiA FR ST sp]. exfalso. pose proof (SIGP q n eq_refl). cbn [optr] in K3. rewrite land64_small in K3 by lia. lia. }
  destruct (sc_sig sc) as [[q n]|] eqn:ES; [| exfalso; apply K3; reflexivity]. pose proof (SIGP q n eq_refl) as [Q1 Q2]. clear K3.
  zstep. zstep. unfold sc_siglen. rewrite ES. replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  setreg 10%Z (Z_to_bv 64 1) ltac:(symmetry; rewrite ?land64_small by lia; replace (0 <? n) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
  zstep. epiA FR ST sp.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma SCT_is_complete_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z) (adr : bptr -> Z) (sc : sctr bptr) (vs : Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> ACEIL <= lo -> lo <= bv_unsigned sp - 48 ->
  In (sc_blk sc, adr (sc_blk sc), SCT_SIZE) (OW ++ LB) -> adr (sc_blk sc) mod 16 = 0 ->
  rw_cells ctasegs m (adr (sc_blk sc)) (sct_cells adr sc (-1) vs) -> sct_ok adr sc ->
  a0 = Z_to_bv 64 (adr (sc_blk sc)) ->
  evt ctasegs (leaf48_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m (bret (sct_complete sc)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SCT_IS_COMPLETE_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until vs. intros HEAP ST MI CEIL LO HIN AL16 HX OK ->.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HIN) as (B0 & _ & _ & BC & BI). cbn [blk_addr blk_size fst snd] in B0, BC, BI.
  ablock HEAP HIN ACC OFF.
  unfold SCT_IS_COMPLETE_A, SCT_SIZE, SEGTOP_A in *.
  pose proof OK as OK0. destruct OK as (VR & HR & GR & SIGP & BLOBP & LOGP & ELR & BLR & EXTP & EXTL & BLBL).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFFW : offshW [(bv_unsigned sp - 48, bv_unsigned sp)]%Z) by (cbn [offshW]; alia).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (stk_below ctasegs m lo _ MI ST ltac:(lia)) as SPT. unfold UTOP in SPT.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (SEPX : adr (sc_blk sc) + 104 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= adr (sc_blk sc)) by alia.
  unfold sct_cells in HX. unfold MallocRep.wz, u32 in HX.
  (* [comment removed for export] *)
  assert (RES : bret (sct_complete sc)
                = if sc_version sc =? -1 then 0
                  else if sc_version sc =? 0 then
                    match sc_logid sc with Some _ => bret (sct_sig_complete sc) | None => 0 end
                  else match sc_blob sc with Some _ => 1 | None => 0 end).
  { unfold bret, sct_complete. destruct (sc_version sc =? -1); [reflexivity|]. destruct (sc_version sc =? 0); [| destruct (sc_blob sc) as [[? ?]|]; reflexivity].
    destruct (sc_logid sc) as [lq|]; [| reflexivity]. cbn [andb]. reflexivity. }
  rewrite RES. clear RES.
  carve_frame 16%nat ST. do 4 zstep.
  Ltac epi16 FR ST sp := do 3 zstep; release_frame FR ST (bv_unsigned sp); zstep; finish.
  (* [comment removed for export] *)
  zstep. zstep. rewrite sx32_mod32 by lia.
  zstep. if_cases K; zify_cond K.
  { (* [comment removed for export] *)
    assert (VM : sc_version sc = -1).
    { destruct VR as [E0|VR']; [exact E0|]. exfalso. revert K. rewrite land64_small by lia. lia. }
    rewrite VM. cbn [Z.eqb Pos.eqb]. zstep. zstep. epi16 FR ST sp. }
  assert (VR' : 0 <= sc_version sc < 256).
  { destruct VR as [E0|VR']; [exfalso; apply K; rewrite E0; vm_compute; reflexivity| exact VR']. }
  clear K VR. replace (sc_version sc =? -1) with false by (symmetry; apply Z.eqb_neq; lia).
  (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K.
  { replace (sc_version sc =? 0) with false by (symmetry; apply Z.eqb_neq; intros E0; apply K; rewrite E0; reflexivity).
    (* [comment removed for export] *)
    zstep.
    destruct (sc_blob sc) as [[bq bn]|] eqn:EB.
    - pose proof (BLOBP bq bn eq_refl) as BQ. cbn [optr]. zstep.
      setreg 10%Z (Z_to_bv 64 1) ltac:(symmetry; rewrite ?land64_small by lia; replace (0 <? adr bq) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
      epi16 FR ST sp.
    - cbn [optr]. zstep. epi16 FR ST sp. }
  assert (V0 : sc_version sc = 0) by (revert K; rewrite ?land64_small by lia; intros K; lia).
  rewrite V0. cbn [Z.eqb Pos.eqb andb]. clear K.
  (* [comment removed for export] *)
  zstep. zstep. if_cases KL; zify_cond KL.
  { destruct (sc_logid sc) as [lq|] eqn:EL; [| zstep; zstep; epi16 FR ST sp].
    exfalso. pose proof (LOGP lq eq_refl). cbn [osz32 option_map optr] in KL. rewrite land64_small in KL by lia. lia. }
  destruct (sc_logid sc) as [lq|] eqn:EL; [| exfalso; apply KL; reflexivity]. clear KL.
  (* [comment removed for export] *)
  assert (RES : bret (sct_sig_complete sc)
                = if sct_nid sc =? 0 then 0 else (match sc_sig sc with Some _ => (if sc_siglen sc =? 0 then 0 else 1) | None => 0 end)).
  { unfold bret, sct_sig_complete, NID_undef. destruct (sct_nid sc =? 0); cbn [negb andb]; [reflexivity|].
    unfold sc_siglen; destruct (sc_sig sc) as [[q n]|] eqn:ES; cbn; [| reflexivity].
    destruct (Z.ltb_spec0 0 n); destruct (Z.eqb_spec n 0); cbn; try reflexivity; exfalso; pose proof (SIGP q n eq_refl); lia. }
  rewrite RES. clear RES.
  assert (NIDE : sct_nid sc = if (sc_version sc =? 0) && (sc_hash sc =? 4) then (if sc_sigalg sc =? 3 then 794 else if sc_sigalg sc =? 1 then 668 else 0) else 0).
  { unfold sct_nid, sig_nid, NID_undef, NID_ecdsa_with_SHA256, NID_sha256WithRSAEncryption. reflexivity. }
  rewrite NIDE, V0. clear NIDE. cbn [Z.eqb Pos.eqb andb].
  zstep. zstep. zstep. if_cases K1; zify_cond K1.
  { replace (sc_hash sc =? 4) with false by (symmetry; apply Z.eqb_neq; intros E0; apply K1; rewrite E0; reflexivity). cbn [andb Z.eqb]. zstep. zstep. epi16 FR ST sp. }
  assert (H4 : sc_hash sc = 4) by (revert K1; rewrite ?u8_lit by lia; intros K1; lia). rewrite H4. cbn [Z.eqb Pos.eqb andb]. clear K1.
  zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2.
  { replace (if sc_sigalg sc =? 3 then 794 else if sc_sigalg sc =? 1 then 668 else 0) with 0
      by (destruct (Z.eqb_spec (sc_sigalg sc) 3) as [E3|N3]; [exfalso; apply K2; rewrite ?u8_lit by lia; rewrite E3; reflexivity|];
          destruct (Z.eqb_spec (sc_sigalg sc) 1) as [E1|N1]; [exfalso; apply K2; rewrite ?u8_lit by lia; rewrite E1; reflexivity| reflexivity]).
    cbn [Z.eqb]. zstep. zstep. epi16 FR ST sp. }
  assert (G13 : sc_sigalg sc = 1 \/ sc_sigalg sc = 3).
  { revert K2. rewrite ?u8_lit by lia. intros K2. assert (KL : Z.land (sc_sigalg sc) 253 = 1) by lia.
    pose proof (land253 (sc_sigalg sc) ltac:(lia)) as LL. rewrite KL, Z.eqb_refl in LL.
    symmetry in LL. apply orb_true_iff in LL. destruct LL as [LL|LL]; apply Z.eqb_eq in LL; [left|right]; exact LL. }
  replace ((if sc_sigalg sc =? 3 then 794 else if sc_sigalg sc =? 1 then 668 else 0) =? 0) with false
    by (destruct G13 as [E|E]; rewrite E; reflexivity). clear K2.
  zstep. zstep. if_cases K3; zify_cond K3.
  { destruct (sc_sig sc) as [[q n]|] eqn:ES; [| zstep; zstep; epi16 FR ST sp]. exfalso. pose proof (SIGP q n eq_refl). cbn [optr] in K3. rewrite land64_small in K3 by lia. lia. }
  destruct (sc_sig sc) as [[q n]|] eqn:ES; [| exfalso; apply K3; reflexivity]. pose proof (SIGP q n eq_refl) as [Q1 Q2]. clear K3.
  zstep. zstep. unfold sc_siglen. rewrite ES. replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  setreg 10%Z (Z_to_bv 64 1) ltac:(symmetry; rewrite ?land64_small by lia; replace (0 <? n) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
  epi16 FR ST sp.
Qed.

End WithRT.
