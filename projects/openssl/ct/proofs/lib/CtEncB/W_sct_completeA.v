(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire ApBase ApState ApOwner.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OSSVerify.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.ct.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.ct.lib.CtB Require Import Layout RT_iface RT_client_kit R_cache_defs R_prim_defs R_sec_defs D_defs D_cs.
From OSSVerify.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OSSVerify.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OSSVerify.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OSSVerify.Proofs.openssl.ct.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.ct.lib.CtKitB Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA AsStruct.
From OSSVerify.Proofs.openssl.ct.lib.CtRepB Require Import ApUTacB.
From OSSVerify.Proofs.openssl.ct.lib.CtRepB Require Import ApATac ApBImg ApWalkTac ApRepDefs ApRep.
From OSSVerify.Proofs.openssl.ct.lib.CtSctP Require Import SctDefs.
From OSSVerify.Proofs.openssl.ct.lib.CtSctP Require W_sct_list_free SctRep.
From OSSVerify.Proofs.openssl.ct.lib.CtEncP Require Import EncPure.
From OSSVerify.Proofs.openssl.ct.lib.CtSctB Require Import SctRepA.
From OSSVerify.Proofs.openssl.ct.lib.CtEncB Require Import EncStmtA.
From OSSVerify.Proofs.openssl.ct.lib.CtKitB Require Import CtUbTabB CtUTacB.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OSSVerify.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OSSVerify.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
(* [comment removed for export] *)
Ltac hshload :=
  let ad := cur_mem_addr in let X := ab_X ad in
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>
    match goal with
    | ACC : acc segs ?mb ?a ?n, MU : munch ?W ?mb mc |- _ =>
        let RD := fresh "RDsh" in
        pose proof (acc_rdG segs W mb mc a n X ad ACC MU ltac:(ab_off) ltac:(ab_alia) ltac:(ab_alia) ltac:(ab_alia) ltac:(ab_alia) ltac:(ab_addr)) as RD;
        OSSVerify.Proofs.openssl.ct.lib.Lib.Step.step; clear RD
    end end.
Ltac hchk := hshload; OSSVerify.Proofs.openssl.ct.lib.Lib.Step.step; rewrite ?zxb_z8, ?sxb_z8; if_false.

Lemma u8_lit : forall z : Z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn. apply Z.mod_small. lia. Qed.

Definition SCT_GET_SIGNATURE_NID_B : Z := 0x34bd18.

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
             F (ret_pc ra) fc None m' (seg_rom ctbsegs)
    /\ munch [(bv_unsigned sp - n, bv_unsigned sp)]%Z m m' /\ wmono ctbsegs m m' /\ mem_inv ctbsegs m'
    /\ stk ctbsegs m' lo (bv_unsigned sp).
Definition leaf16_postA := leafN_postA 16.
Definition leaf48_postA := leafN_postA 48.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma SCT_get_signature_nid_specB : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z) (adr : bptr -> Z) (sc : sctr bptr) (vs : Z),
  AHEAP Σ OW LB m ->
  stk ctbsegs m lo (bv_unsigned sp) -> mem_inv ctbsegs m -> ACEIL <= lo -> lo <= bv_unsigned sp - 16 ->
  In (sc_blk sc, adr (sc_blk sc), SCT_SIZE) (OW ++ LB) -> adr (sc_blk sc) mod 16 = 0 ->
  rw_cells ctbsegs m (adr (sc_blk sc)) (sct_cells adr sc (-1) vs) -> sct_ok adr sc ->
  a0 = Z_to_bv 64 (adr (sc_blk sc)) ->
  evt ctbsegs (leafN_postA 16 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m (sct_nid sc))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SCT_GET_SIGNATURE_NID_B) fc None m (seg_rom ctbsegs)).
Proof.
  intros until vs. intros HEAP ST MI CEIL LO HIN AL16 HX OK ->.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HIN) as (B0 & _ & _ & BC & BI). cbn [blk_addr blk_size fst snd] in B0, BC, BI.
  ablock HEAP HIN ACC OFF.
  unfold SCT_GET_SIGNATURE_NID_B, SCT_SIZE, SEGTOP_A in *.
  destruct OK as (VR & HR & GR & SIGP & BLOBP & LOGP & ELR & BLR & EXTP & EXTL & BLBL).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctbsegs m) as WM.
  assert (OFFW : offshW [(bv_unsigned sp - 16, bv_unsigned sp)]%Z) by (cbn [offshW]; alia).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (stk_below ctbsegs m lo _ MI ST ltac:(lia)) as SPT. unfold UTOP in SPT.
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
  zstep. zstep. hchk. zstep. rewrite sx32_mod32 by lia.
  zstep. if_cases K; zify_cond K.
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
  stk ctbsegs m lo (bv_unsigned sp) -> mem_inv ctbsegs m -> ACEIL <= lo -> lo <= bv_unsigned sp - 48 ->
  In (sc_blk sc, adr (sc_blk sc), SCT_SIZE) (OW ++ LB) -> adr (sc_blk sc) mod 16 = 0 ->
  rw_cells ctbsegs m (adr (sc_blk sc)) (sct_cells adr sc (-1) vs) -> sct_ok adr sc ->
  a0 = Z_to_bv 64 (adr (sc_blk sc)) ->
  evt ctbsegs (leaf48_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m (bret (sct_sig_complete sc)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SCT_SIGNATURE_IS_COMPLETE_A) fc None m (seg_rom ctbsegs)).
Proof.
  intros until vs. intros HEAP ST MI CEIL LO HIN AL16 HX OK ->.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HIN) as (B0 & _ & _ & BC & BI). cbn [blk_addr blk_size fst snd] in B0, BC, BI.
  ablock HEAP HIN ACC OFF.
  unfold SCT_SIGNATURE_IS_COMPLETE_A, SCT_SIZE, SEGTOP_A in *.
  pose proof OK as OK0. destruct OK as (VR & HR & GR & SIGP & BLOBP & LOGP & ELR & BLR & EXTP & EXTL & BLBL).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctbsegs m) as WM.
  assert (OFFW : offshW [(bv_unsigned sp - 48, bv_unsigned sp)]%Z) by (cbn [offshW]; alia).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (stk_below ctbsegs m lo _ MI ST ltac:(lia)) as SPT. unfold UTOP in SPT.
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
  carve_frame 32%nat ST. do 6 zstep.
  (* [comment removed for export] *)
  zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctbsegs m m1 |- _ => rename H into WM1 end.
  match goal with H : mem_inv ctbsegs m1 |- _ => rename H into MI1 end.
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [left; cbn; alia | constructor]. }
  eapply evt_cut.
  { change (Z_to_bv 64 3456280) with (Z_to_bv 64 SCT_GET_SIGNATURE_NID_B).
    eapply SCT_get_signature_nid_specB with (lo := lo) (adr := adr) (sc := sc) (vs := vs); rewrite ?ESP32;
      [exact HEAP1| exact ST| exact MI1| exact CEIL| clear - LO; lia| exact HIN| exact AL16| exact HX| exact OK0| reflexivity]. }
  cbv beta. intros ms2 PO.
  destruct PO as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m2 & -> & MU2 & WM2 & MI2 & ST2). rewrite ?ESP32 in MU2, ST2.
  rewrite (ret_pc_even 0x34befc) by (clear; lia). clear ST MI1. rename ST2 into ST.
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in FR; [| cbn; clear; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in HX; [| cbn; clear - SEPX; lia].
  assert (MU12 : munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m2).
  { eapply munch_trans; [exact MU1|]. eapply munch_weaken; [| exact MU2]. intros x Hx. cbn [outside fst snd] in Hx |- *. clear - Hx. lia. }
  pose proof (wmono_trans _ _ _ _ WM1 WM2) as WM12. clear MU1 WM1 MU2 WM2 HEAP1.
  Ltac epi32 FR ST sp := do 5 zstep; release_frame FR ST (bv_unsigned sp); zstep; finish.
  (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K.
  { replace (sct_nid sc =? 0) with true by (symmetry; apply Z.eqb_eq; revert K; rewrite ?unsigned_lit by (clear - NIDR; lia); clear - NIDR; intros K; lia).
    setreg 10%Z (Z_to_bv 64 0) ltac:(symmetry; apply bv_eq; revert K; rewrite ?unsigned_lit by (clear - NIDR; lia); intros K; rewrite ?unsigned_lit by (clear - NIDR; lia); clear - K NIDR; lia).
    epi32 FR ST sp. }
  replace (sct_nid sc =? 0) with false by (symmetry; apply Z.eqb_neq; revert K; rewrite ?unsigned_lit by (clear - NIDR; lia); clear - NIDR; intros K; lia). clear K.
  (* [comment removed for export] *)
  zstep. zstep. if_cases K3; zify_cond K3.
  { destruct (sc_sig sc) as [[q n]|] eqn:ES; [| epi32 FR ST sp]. exfalso. pose proof (SIGP q n eq_refl). cbn [optr] in K3. rewrite land64_small in K3 by lia. lia. }
  destruct (sc_sig sc) as [[q n]|] eqn:ES; [| exfalso; apply K3; reflexivity]. pose proof (SIGP q n eq_refl) as [Q1 Q2]. clear K3.
  (* [comment removed for export] *)
  zstep. zstep. unfold sc_siglen. rewrite ES. replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  setreg 10%Z (Z_to_bv 64 1) ltac:(symmetry; rewrite ?land64_small by lia; replace (0 <? n) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
  epi32 FR ST sp.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma SCT_is_complete_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z) (adr : bptr -> Z) (sc : sctr bptr) (vs : Z),
  AHEAP Σ OW LB m ->
  stk ctbsegs m lo (bv_unsigned sp) -> mem_inv ctbsegs m -> ACEIL <= lo -> lo <= bv_unsigned sp - 48 ->
  In (sc_blk sc, adr (sc_blk sc), SCT_SIZE) (OW ++ LB) -> adr (sc_blk sc) mod 16 = 0 ->
  rw_cells ctbsegs m (adr (sc_blk sc)) (sct_cells adr sc (-1) vs) -> sct_ok adr sc ->
  a0 = Z_to_bv 64 (adr (sc_blk sc)) ->
  evt ctbsegs (leaf48_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m (bret (sct_complete sc)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SCT_IS_COMPLETE_A) fc None m (seg_rom ctbsegs)).
Proof.
  intros until vs. intros HEAP ST MI CEIL LO HIN AL16 HX OK ->.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HIN) as (B0 & _ & _ & BC & BI). cbn [blk_addr blk_size fst snd] in B0, BC, BI.
  ablock HEAP HIN ACC OFF.
  unfold SCT_IS_COMPLETE_A, SCT_SIZE, SEGTOP_A in *.
  pose proof OK as OK0. destruct OK as (VR & HR & GR & SIGP & BLOBP & LOGP & ELR & BLR & EXTP & EXTL & BLBL).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctbsegs m) as WM.
  assert (OFFW : offshW [(bv_unsigned sp - 48, bv_unsigned sp)]%Z) by (cbn [offshW]; alia).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (stk_below ctbsegs m lo _ MI ST ltac:(lia)) as SPT. unfold UTOP in SPT.
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
  zstep. zstep. hchk. zstep. rewrite sx32_mod32 by lia. zstep.
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
  do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctbsegs m m1 |- _ => rename H into WM1 end.
  match goal with H : mem_inv ctbsegs m1 |- _ => rename H into MI1 end.
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [left; cbn; alia | constructor]. }
  eapply evt_cut.
  { change (Z_to_bv 64 3456720) with (Z_to_bv 64 SCT_SIGNATURE_IS_COMPLETE_A).
    eapply SCT_signature_is_complete_specA with (lo := lo) (adr := adr) (sc := sc) (vs := vs);
      [exact HEAP1| exact ST| exact MI1| exact CEIL| exact LO| exact HIN| exact AL16| rewrite <- EL in HX; exact HX| exact OK0| reflexivity]. }
  cbv beta. intros ms2 PO.
  destruct PO as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m2 & -> & MU2 & WM2 & MI2 & ST2).
  pose proof (munch_trans _ _ _ _ MU1 MU2) as MU12. pose proof (wmono_trans _ _ _ _ WM1 WM2) as WM12. clear MU1 WM1 MU2 WM2.
  finish.
Qed.

End WithRT.
