(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem SFModel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface Malloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Printf_lib F_memcpy.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApWalkTac ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctDefs W_sct_list_free SctRep W_sct_leaves.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncU Require Import EncPure EncStmt EncKit W_sct_complete.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  | Z_to_le_bytes 1 ?z => constr:(C1 (Z_to_bv 8 z))
  end.

(* [comment removed for export] *)
Ltac btaken := let K0 := fresh "K0" in if_cases K0; [| exfalso; revert K0; vm_compute; congruence]; clear K0.
Ltac bnot := let K0 := fresh "K0" in if_cases K0; [exfalso; revert K0; vm_compute; congruence|]; clear K0.
Ltac sfalse := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
                 replace c with false by (symmetry; unfold_cond; fold_lit_ux; rewrite ?signed_of_Z, ?unsigned_lit by lia; solve_cond_rec); cbv iota end.
Ltac strue := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
                 replace c with true by (symmetry; unfold_cond; fold_lit_ux; rewrite ?signed_of_Z, ?unsigned_lit by lia; solve_cond_rec); cbv iota end.

(* [comment removed for export] *)
Ltac blob_of R := lazymatch type of R with rw_cells _ _ _ ?cs => exists (cells_bytes cs);
  eapply (rw_cells_recast _ _ _ _ R); [cbn; repeat split; reflexivity| cbn; rewrite ?app_nil_r; reflexivity| reflexivity] end.

Section WithCeiling. Context {CE__ : Ceiling}.

(* [comment removed for export] *)
Lemma cell_bytes_read : forall m A k pre c post i n,
  rw_cells ctusegs m A (pre ++ c :: post) -> Z.of_nat (cells_size pre) = k -> 0 <= i -> (Z.to_nat i + n <= length (cbytes c))%nat ->
  ov_read_bytes ctusegs m (wa (A + k + i)) n = Some (firstn n (skipn (Z.to_nat i) (cbytes c))).
Proof.
  intros m A k pre c post i n H Hk Hi Hn.
  assert (R : ro_cells ctusegs m (A + k) [c]).
  { apply rw_cells_app in H. destruct H as [_ H2]. rewrite Hk in H2. change (c :: post) with ([c] ++ post) in H2. apply rw_cells_app in H2. exact (proj1 (proj1 H2)). }
  pose proof (ro_cells_bytes_at _ _ _ _ R) as B. cbn [cells_bytes] in B. rewrite app_nil_r in B.
  apply (bytes_at_read _ _ _ _ i n B Hi Hn).
Qed.
Ltac ts_read HX k idx i n RD :=
  lazymatch type of HX with rw_cells _ ?mm ?A ?cs =>
    let pre := eval cbv [firstn] in (firstn idx cs) in
    let c := eval cbv [nth] in (nth idx cs (C8 (Z_to_bv 64 0))) in
    let post := eval cbv [skipn] in (skipn (S idx) cs) in
    pose proof (cell_bytes_read mm A k pre c post i n HX eq_refl ltac:(lia) ltac:(cbn; lia)) as RD;
    cbn [cbytes firstn skipn le8 Z_to_le_bytes Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition I2O_SCT_RAISE : Z := 0x19cbb8.     (* [comment removed for export] *)
Definition I2O_SCT_LEN_STACK : Z := 64 + 48.

(* [comment removed for export] *)

Lemma i2o_sct_len_seg : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (adr : bptr -> Z) (x : sctr bptr) (vs : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - I2O_SCT_LEN_STACK ->
  0 < adr (sc_blk x) -> adr (sc_blk x) + SCT_SIZE <= lo -> adr (sc_blk x) mod 8 = 0 ->
  rw_cells ctusegs m (adr (sc_blk x)) (sct_cells adr x (-1) vs) -> sct_ok adr x ->
  a0 = Z_to_bv 64 (adr (sc_blk x)) -> a1 = Z_to_bv 64 0 ->
  evt ctusegs (fun ms' => exists m',
       munch [(bv_unsigned sp - I2O_SCT_LEN_STACK, bv_unsigned sp)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
       /\ if sct_complete x then
            (exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (i2o_sct_len x)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom ctusegs))
            /\ stk ctusegs m' lo (bv_unsigned sp)
          else
            (exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
               ms' = MS (mkR (Z_to_bv 64 0x19cb98) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' t1' t2' sp s1 a0' a1' a2' a3' a4' a5' a6' a7'
                             (Z_to_bv 64 (adr (sc_blk x))) s3 s4 (Z_to_bv 64 0) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (Z_to_bv 64 I2O_SCT_RAISE) fc None m' (seg_rom ctusegs))
            /\ stk ctusegs m' lo (bv_unsigned sp + -64)
            /\ rw_cells ctusegs m' (bv_unsigned sp + -64) [C8 (Z_to_bv 64 0); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 I2O_SCT) fc None m (seg_rom ctusegs)).
Proof.
  intros until vs. intros ST MI GLO LO A0 ALO AL8 HX OK -> ->.
  unfold GLOBALS_TOP in GLO. unfold I2O_SCT, I2O_SCT_RAISE, I2O_SCT_LEN_STACK, SCT_SIZE in *.
  pose proof OK as (VR & HR & GR & SIGP & BLOBP & LOGP & ELR & BLR & EXTP & EXTL & BLBL).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  unfold sct_cells, MallocRep.wz, u32 in HX.
  carve_frame 64%nat ST. do 9 zstep.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply SCT_is_complete_spec with (lo := lo) (adr := adr) (x := x) (vs := vs); rewrite ?ESP;
      try eassumption; try reflexivity; unfold GLOBALS_TOP, SCT_SIZE; lia. }
  cbv beta. intros ms2 PO.
  destruct PO as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m2 & -> & MU2 & WM2 & MI2 & ST2). rewrite ESP in *.
  replace (ret_pc (Z_to_bv 64 0x19cb98)) with (Z_to_bv 64 0x19cb98) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in FR; [| cbn; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in HX; [| cbn; lia].
  assert (MU' : munch [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m m2).
  { eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros y Hy; lia. }
  assert (WM' : wmono ctusegs m m2) by (eapply wmono_trans; [exact WM| exact WM2]).
  clear MU WM MU2 WM2 MI ST. rename MU' into MU. rename WM' into WM. rename MI2 into MI.
  (* [comment removed for export] *)
  zstep. destruct (sct_complete x) eqn:CPL; cbn [bret].
  - (* [comment removed for export] *)
    bnot. ub. zstep. rewrite sx32_mod32 by lia. zstep. if_cases KV; zify_cond KV.
    + (* [comment removed for export] *)
      assert (V0 : sc_version x = 0) by (destruct VR as [E0|VR']; [exfalso; revert KV; rewrite E0; vm_compute; congruence| revert KV; rewrite land64_small by lia; intros KV; lia]).
      zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      assert (SL : 0 <= sc_siglen x <= 65535) by (unfold sc_siglen; destruct (sc_sig x) as [[q n]|] eqn:ES; [pose proof (SIGP q n eq_refl); lia| lia]).
      zstep. rewrite (Z.shiftr_div_pow2 _ 31), Z.div_small by lia. zstep. btaken. zstep. btaken.
      zstep. rewrite Z.add_0_r, (swrap32_small (sc_extlen x + sc_siglen x + 47)) by lia.
      do 7 zstep. zstep. release_frame FR ST2 (bv_unsigned sp). zstep.
      apply evt_done. lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
      split; [| exact ST2]. do 14 eexists.
      unfold i2o_sct_len. rewrite V0. cbn [Z.eqb]. replace (43 + sc_extlen x + 4 + sc_siglen x) with (sc_extlen x + sc_siglen x + 47) by lia. reflexivity.
    + (* [comment removed for export] *)
      assert (VN : sc_version x <> 0) by (intros E0; apply KV; rewrite E0; reflexivity).
      zstep. zstep. zstep. rewrite (Z.shiftr_div_pow2 _ 31), Z.div_small by lia. zstep. btaken. zstep. btaken.
      zstep. rewrite Z.add_0_r, (swrap32_small (sc_bloblen x)) by lia.
      do 7 zstep. zstep. release_frame FR ST2 (bv_unsigned sp). zstep.
      apply evt_done. lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
      split; [| exact ST2]. do 14 eexists.
      unfold i2o_sct_len. replace (sc_version x =? 0) with false by (symmetry; apply Z.eqb_neq; exact VN). reflexivity.
  - (* [comment removed for export] *)
    btaken. apply evt_done. lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [| split; [exact ST2| exact FR]]. do 15 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma i2o_sct_fail_tail : forall x1 sp gp tp t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (ra s0 s1 s2 s3 s4 s5 pcell : word) (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk ctusegs m lo (bv_unsigned sp + -64) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - I2O_SCT_LEN_STACK ->
  crypto_statics m ->
  rw_cells ctusegs m (bv_unsigned sp + -64) [C8 pcell; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
       ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom ctusegs)
       /\ munch [(bv_unsigned sp - I2O_SCT_LEN_STACK, bv_unsigned sp)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19cbe4) fc None m (seg_rom ctusegs)).
Proof using CE__.
  intros until lo. intros ST MI GLO LO CS FR.
  unfold GLOBALS_TOP in GLO. unfold I2O_SCT_LEN_STACK in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep.
  eapply evt_cut.
  { eapply CRYPTO_free_null_spec with (lo := lo); rewrite ?ESP; [exact ST| unfold GLOBALS_TOP; lia| lia| exact MI| exact CS| reflexivity]. }
  cbv beta. intros ms2 PO.
  destruct PO as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m2 & -> & MU2 & WM2 & MI2 & ST2). rewrite ESP in *.
  replace (ret_pc (Z_to_bv 64 0x19cbfc)) with (Z_to_bv 64 0x19cbfc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in FR; [| cbn; lia].
  assert (MU' : munch [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m m2).
  { eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros y Hy; lia. }
  assert (WM' : wmono ctusegs m m2) by (eapply wmono_trans; [exact WM| exact WM2]).
  clear MU WM MU2 WM2 MI ST. rename MU' into MU. rename WM' into WM.
  (* [comment removed for export] *)
  zstep. zstep. zstep. do 7 zstep. zstep. release_frame FR ST2 (bv_unsigned sp). zstep.
  apply evt_done. do 14 eexists. eexists. split; [reflexivity|]. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition I2O_SIG_STACK : Z := 48 + 48.

Lemma i2o_sct_sig_write_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (adr : bptr -> Z) (x : sctr bptr) (vs : Z) (PP P : Z) (sq : bptr) (sn : Z) (sig j3 j4 : list byte),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - I2O_SIG_STACK ->
  0 < adr (sc_blk x) -> adr (sc_blk x) + SCT_SIZE <= lo -> adr (sc_blk x) mod 8 = 0 ->
  rw_cells ctusegs m (adr (sc_blk x)) (sct_cells adr x (-1) vs) -> sct_ok adr x ->
  sc_version x = 0 -> sct_sig_complete x = true -> sc_sig x = Some (sq, sn) ->
  bv_unsigned sp <= PP -> PP + 8 <= 2^64 -> rw_cells ctusegs m PP [C8 (Z_to_bv 64 P)] -> PP mod 8 = 0 ->
  0 < P -> P + 4 + sn <= lo -> (adr (sc_blk x) + SCT_SIZE <= P \/ P + 4 + sn <= adr (sc_blk x)) -> (adr sq + sn <= P \/ P + 4 + sn <= adr sq) ->
  adr sq + sn <= lo ->
  rw_cells ctusegs m P [CB 4%nat j3] -> rw_cells ctusegs m (P + 4) [CB (Z.to_nat sn) j4] ->
  bytes_at ctusegs m (adr sq) sig -> length sig = Z.to_nat sn ->
  a0 = Z_to_bv 64 (adr (sc_blk x)) -> a1 = Z_to_bv 64 PP ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' hb,
       ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (4 + sn)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom ctusegs)
       /\ munch [(bv_unsigned sp - I2O_SIG_STACK, bv_unsigned sp); (PP, PP + 8); (P, P + 4 + sn)]%Z m m' /\ wmono ctusegs m m'
       /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
       /\ rw_cells ctusegs m' PP [C8 (Z_to_bv 64 (P + 4 + sn))]
       /\ rw_cells ctusegs m' P [CB 4%nat hb] /\ rw_cells ctusegs m' (P + 4) [CB (Z.to_nat sn) sig])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 I2O_SCT_SIGNATURE) fc None m (seg_rom ctusegs)).
Proof.
  intros until j4. intros ST MI GLO LO A0 ALO AL8 HX OK V0 SC ES PPlo PPhi HPP PP8 P0 PLO SEPA SEPS SQLO H3 H4 SIG SLEN -> ->.
  change (frozen (adr sq + sn <= P \/ P + 4 + sn <= adr sq)) in SEPS.
  assert (SIGF : frozen (bytes_at ctusegs m (adr sq) sig)) by exact SIG. clear SIG.
  unfold GLOBALS_TOP in GLO. unfold I2O_SCT_SIGNATURE, I2O_SIG_STACK, SCT_SIZE in *.
  pose proof OK as (VR & HR & GR & SIGP & BLOBP & LOGP & ELR & BLR & EXTP & EXTL & BLBL). pose proof (SIGP sq sn ES) as [SQ0 SN].
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (PP, PP + 8); (P, P + 4 + sn)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  assert (SNE : sc_siglen x = sn) by (unfold sc_siglen; rewrite ES; reflexivity).
  unfold sct_cells, MallocRep.wz, u32 in HX. rewrite SNE, ES in HX. cbn [optr] in HX.
  carve_frame 48%nat ST. do 7 zstep.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply SCT_signature_is_complete_spec with (lo := lo) (adr := adr) (x := x) (vs := vs); rewrite ?ESP;
      try eassumption; try reflexivity; try (unfold GLOBALS_TOP, SCT_SIZE; lia).
    unfold sct_cells, MallocRep.wz, u32. rewrite SNE, ES. cbn [optr]. exact HX. }
  cbv beta. intros ms2 PO.
  destruct PO as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m2 & -> & MU2 & WM2 & MI2 & ST2). rewrite ESP in *.
  replace (ret_pc (Z_to_bv 64 0x19ca20)) with (Z_to_bv 64 0x19ca20) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in FR; [| cbn; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in HX; [| cbn; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in HPP; [| cbn; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in H3; [| cbn; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in H4; [| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; cbn; lia].
  assert (MU' : munch [(bv_unsigned sp - 96, bv_unsigned sp); (PP, PP + 8); (P, P + 4 + sn)]%Z m m2).
  { eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros y Hy; lia. }
  assert (WM' : wmono ctusegs m m2) by (eapply wmono_trans; [exact WM| exact WM2]).
  clear MU WM MU2 WM2 MI ST. rename MU' into MU. rename WM' into WM. rename MI2 into MI.
  rewrite SC. cbn [bret].
  (* [comment removed for export] *)
  zstep. bnot. ub. zstep. rewrite sx32_mod32, V0 by lia. zstep. btaken.
  zstep. zstep. zstep. sfalse. ub. zstep. zstep. sfalse. ub. zstep. zstep.
  (* [comment removed for export] *)
  zstep. zstep. zstep. ub. zstep. zstep. zstep. ub. zstep. zstep. zstep. zstep. zstep. zstep. zstep. ub. zstep. zstep. zstep. ub. zstep. zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
  assert (SIG : bytes_at ctusegs m3 (adr sq) sig).
  { pose proof SIGF as X. unfold frozen in X. pose proof SEPS as Y. unfold frozen in Y.
    eapply bytes_at_transport; [exact X| exact MU|]. rewrite SLEN, Z2Nat.id by lia. cbn. lia. }
  eapply evt_cut.
  { eapply memcpy_spec with (src := sig) (junk := j4); rewrite ?unsigned_lit by lia; [exact SIG| exact SLEN| exact H4| pose proof SEPS as Y; unfold frozen in Y; lia| assumption]. }
  cbv beta. intros ms4 PO. unfold memcpy_post in PO. rewrite ?unsigned_lit in PO by lia.
  destruct PO as (p5 & p6 & p7 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p28 & p29 & p30 & p31 & m4 & -> & MU4 & WM4 & MI4 & H4' & _).
  replace (ret_pc (Z_to_bv 64 0x19cb5c)) with (Z_to_bv 64 0x19cb5c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU4 WM4) in FR; [| cbn; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU4 WM4) in HPP; [| cbn; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU4 WM4) in H3; [| cbn; lia].
  assert (ST4 : stk ctusegs m4 lo (bv_unsigned sp + -48)) by (eapply stk_transport; [exact ST2| exact MU4| exact WM4| cbn; lia]).
  assert (MU' : munch [(bv_unsigned sp - 96, bv_unsigned sp); (PP, PP + 8); (P, P + 4 + sn)]%Z m m4).
  { eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU4]]; unfold sub_fp; cbn [outside]; intros y Hy; lia. }
  assert (WM' : wmono ctusegs m m4) by (eapply wmono_trans; [exact WM| exact WM4]).
  clear MU WM MU4 WM4 MI ST2 SIG HX. rename MU' into MU. rename WM' into WM.
  (* [comment removed for export] *)
  zstep. zstep. rewrite Z.add_0_r, (swrap32_small (sn + 4)) by lia. do 5 zstep. zstep. release_frame FR ST4 (bv_unsigned sp). zstep.
  apply evt_done. lazymatch type of H3 with rw_cells _ _ _ ?cs => do 15 eexists; exists (cells_bytes cs) end.
  split; [replace (4 + sn) with (sn + 4) by lia; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI4|]. split; [exact ST4|].
  split; [replace (P + 4 + sn) with (P + (sn + 4)) by lia; exact HPP|]. split; [| exact H4'].
  eapply (rw_cells_recast _ _ _ _ H3); [cbn; repeat split; reflexivity| cbn; reflexivity| reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma i2o_sct_write_fwd : forall (P0 : machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (adr : bptr -> Z) (x : sctr bptr) (vs : Z) (PP P : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - I2O_SCT_LEN_STACK ->
  0 < adr (sc_blk x) -> adr (sc_blk x) + SCT_SIZE <= lo -> adr (sc_blk x) mod 8 = 0 ->
  rw_cells ctusegs m (adr (sc_blk x)) (sct_cells adr x (-1) vs) -> sct_ok adr x -> sct_complete x = true ->
  bv_unsigned sp <= PP -> PP + 8 <= 2^64 -> rw_cells ctusegs m PP [C8 (Z_to_bv 64 P)] -> PP mod 8 = 0 -> 0 < P -> P + i2o_sct_len x <= lo ->
  a0 = Z_to_bv 64 (adr (sc_blk x)) -> a1 = Z_to_bv 64 PP ->
  (forall m1 (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
     munch [(bv_unsigned sp - I2O_SCT_LEN_STACK, bv_unsigned sp); (PP, PP + 8)]%Z m m1 -> wmono ctusegs m m1 -> mem_inv ctusegs m1 ->
     stk ctusegs m1 lo (bv_unsigned sp + -64) ->
     rw_cells ctusegs m1 (bv_unsigned sp + -64) [C8 (Z_to_bv 64 0); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
     rw_cells ctusegs m1 PP [C8 (Z_to_bv 64 (P + i2o_sct_len x))] ->
     evt ctusegs P0 (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 sp (Z_to_bv 64 (i2o_sct_len x))
                             (Z_to_bv 64 (sc_version x)) (Z_to_bv 64 (P + i2o_sct_len x)) x12 x13 x14 x15 x16 x17
                             (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 0) (Z_to_bv 64 P) (Z_to_bv 64 PP) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x19cc9c) fc None m1 (seg_rom ctusegs))) ->
  evt ctusegs P0 (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 I2O_SCT) fc None m (seg_rom ctusegs)).
Proof.
  intros until P. intros ST MI GLO LO A0 ALO AL8 HX OK CPL PPlo PPhi HPP PP8 P0' PLO -> -> K.
  unfold GLOBALS_TOP in GLO. unfold I2O_SCT, I2O_SCT_LEN_STACK, SCT_SIZE in *.
  pose proof OK as (VR & HR & GR & SIGP & BLOBP & LOGP & ELR & BLR & EXTP & EXTL & BLBL).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (SL : 0 <= sc_siglen x <= 65535) by (unfold sc_siglen; destruct (sc_sig x) as [[q n]|] eqn:ES; [pose proof (SIGP q n eq_refl); lia| lia]).
  assert (LENR : 0 <= i2o_sct_len x <= 3 * 65536) by (unfold i2o_sct_len; destruct (sc_version x =? 0); lia).
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (PP, PP + 8)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  unfold sct_cells, MallocRep.wz, u32 in HX.
  carve_frame 64%nat ST. do 9 zstep.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply SCT_is_complete_spec with (lo := lo) (adr := adr) (x := x) (vs := vs); rewrite ?ESP;
      try eassumption; try reflexivity; unfold GLOBALS_TOP, SCT_SIZE; lia. }
  cbv beta. intros ms2 PO.
  destruct PO as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m2 & -> & MU2 & WM2 & MI2 & ST2). rewrite ESP in *.
  replace (ret_pc (Z_to_bv 64 0x19cb98)) with (Z_to_bv 64 0x19cb98) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in FR; [| cbn; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in HX; [| cbn; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in HPP; [| cbn; lia].
  assert (MU' : munch [(bv_unsigned sp - 112, bv_unsigned sp); (PP, PP + 8)]%Z m m2).
  { eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros y Hy; lia. }
  assert (WM' : wmono ctusegs m m2) by (eapply wmono_trans; [exact WM| exact WM2]).
  clear MU WM MU2 WM2 MI ST. rename MU' into MU. rename WM' into WM. rename MI2 into MI.
  rewrite CPL. cbn [bret].
  (* [comment removed for export] *)
  zstep. bnot. ub. zstep. rewrite sx32_mod32 by lia.
  (* [comment removed for export] *)
  assert (JOIN : forall m3 (x11' x12' : word),
    rw_cells ctusegs m3 (bv_unsigned sp + -64) [C8 (Z_to_bv 64 0); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells ctusegs m3 PP [C8 (Z_to_bv 64 P)] -> mem_inv ctusegs m3 -> stk ctusegs m3 lo (bv_unsigned sp + -64) ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp); (PP, PP + 8)]%Z m m3 -> wmono ctusegs m m3 ->
    evt ctusegs P0 (MS (mkR (Z_to_bv 64 0x19cb98) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp q5 q6 q7 sp (Z_to_bv 64 (i2o_sct_len x))
                            (Z_to_bv 64 (sc_version x)) x11' x12' q13 q14 q15 q16 q17
                            (Z_to_bv 64 (adr (sc_blk x))) s3 s4 (Z_to_bv 64 PP) s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
                       F (Z_to_bv 64 0x19cc10) fc None m3 (seg_rom ctusegs))).
  { intros m3 x11' x12' FR3 HPP3 MI3 ST3 MU3 WM3. clear FR HPP MI ST2 MU WM HX.
    (* [comment removed for export] *)
    zstep. rewrite (Z.shiftr_div_pow2 _ 31), Z.div_small by lia. zstep. btaken. zstep. sfalse. ub. zstep. zstep. sfalse. ub. zstep. zstep. zstep. zstep.
    eapply K; [exact MU3| exact WM3| assumption| exact ST3| exact FR3| exact HPP3]. }
  zstep. if_cases KV; zify_cond KV.
  - assert (V0 : sc_version x = 0) by (destruct VR as [E0|VR']; [exfalso; revert KV; rewrite E0; vm_compute; congruence| revert KV; rewrite land64_small by lia; intros KV; lia]).
    zstep. zstep. zstep. zstep.
    replace (sc_extlen x + sc_siglen x + 47) with (i2o_sct_len x) by (unfold i2o_sct_len; rewrite V0; cbn [Z.eqb]; lia).
    eapply JOIN; eassumption.
  - assert (VN : sc_version x <> 0) by (intros E0; apply KV; rewrite E0; reflexivity).
    zstep. zstep. replace (sc_bloblen x) with (i2o_sct_len x) by (unfold i2o_sct_len; replace (sc_version x =? 0) with false by (symmetry; apply Z.eqb_neq; exact VN); reflexivity).
    eapply JOIN; eassumption.
Qed.

Lemma i2o_sct_write_nv1_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (adr : bptr -> Z) (x : sctr bptr) (vs : Z) (PP P : Z) (bq : bptr) (bn : Z) (blob junk : list byte),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - I2O_SCT_LEN_STACK ->
  0 < adr (sc_blk x) -> adr (sc_blk x) + SCT_SIZE <= lo -> adr (sc_blk x) mod 8 = 0 ->
  rw_cells ctusegs m (adr (sc_blk x)) (sct_cells adr x (-1) vs) -> sct_ok adr x -> sct_complete x = true -> sc_version x <> 0 -> sc_blob x = Some (bq, bn) ->
  bv_unsigned sp <= PP -> PP + 8 <= 2^64 -> rw_cells ctusegs m PP [C8 (Z_to_bv 64 P)] -> PP mod 8 = 0 -> 0 < P -> P + bn <= lo ->
  (adr bq + bn <= P \/ P + bn <= adr bq) -> adr bq + bn <= lo ->
  rw_cells ctusegs m P [CB (Z.to_nat bn) junk] -> bytes_at ctusegs m (adr bq) blob -> length blob = Z.to_nat bn ->
  a0 = Z_to_bv 64 (adr (sc_blk x)) -> a1 = Z_to_bv 64 PP ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
       ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 bn) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom ctusegs)
       /\ munch [(bv_unsigned sp - I2O_SCT_LEN_STACK, bv_unsigned sp); (PP, PP + 8); (P, P + bn)]%Z m m' /\ wmono ctusegs m m'
       /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
       /\ rw_cells ctusegs m' PP [C8 (Z_to_bv 64 (P + bn))] /\ rw_cells ctusegs m' P [CB (Z.to_nat bn) blob])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 I2O_SCT) fc None m (seg_rom ctusegs)).
Proof.
  intros until junk. intros ST MI GLO LO A0 ALO AL8 HX OK CPL VN EB PPlo PPhi HPP PP8 P0 PLO SEPB BQLO HP BLOB BLEN -> ->.
  change (frozen (adr bq + bn <= P \/ P + bn <= adr bq)) in SEPB.
  assert (BLOBF : frozen (bytes_at ctusegs m (adr bq) blob)) by exact BLOB. clear BLOB.
  pose proof OK as (VR & HR & GR & SIGP & BLOBP & LOGP & ELR & BLR & EXTP & EXTL & BLBL). pose proof (BLOBP bq bn EB) as BQ0.
  assert (LEN : i2o_sct_len x = bn).
  { unfold i2o_sct_len. replace (sc_version x =? 0) with false by (symmetry; apply Z.eqb_neq; exact VN). rewrite BLBL, EB. reflexivity. }
  assert (BN : 0 <= bn <= 65535) by (rewrite BLBL, EB in BLR; exact BLR).
  assert (VR' : 0 <= sc_version x < 256).
  { destruct VR as [E0|H]; [exfalso| exact H]. unfold sct_complete in CPL. rewrite E0 in CPL. cbn in CPL. discriminate. }
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold I2O_SCT_LEN_STACK in *.
  eapply i2o_sct_write_fwd with (lo := lo) (adr := adr) (x := x) (vs := vs) (PP := PP) (P := P); try eassumption; try reflexivity; try (unfold I2O_SCT_LEN_STACK; lia).
  intros m1 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 MU WM MI1 ST1 FR HPP1. rewrite LEN in *. unfold GLOBALS_TOP, SCT_SIZE, I2O_SCT_LEN_STACK in *.
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU WM) in HX; [| rewrite sct_cells_size; cbn; unfold SCT_SIZE; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU WM) in HP; [| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; cbn; lia].
  unfold sct_cells, MallocRep.wz, u32 in HX. rewrite EB in HX. cbn [optr] in HX.
  (* [comment removed for export] *)
  zstep. sfalse. zstep. zstep. zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
  assert (BLOB : bytes_at ctusegs m3 (adr bq) blob).
  { pose proof BLOBF as X. unfold frozen in X. pose proof SEPB as Y. unfold frozen in Y.
    eapply bytes_at_transport; [exact X| exact MU|]. rewrite BLEN, Z2Nat.id by lia. cbn. lia. }
  eapply evt_cut.
  { eapply memcpy_spec with (src := blob) (junk := junk); rewrite ?unsigned_lit by lia; [exact BLOB| exact BLEN| exact HP| pose proof SEPB as Y; unfold frozen in Y; lia| assumption]. }
  cbv beta. intros ms4 PO. unfold memcpy_post in PO. rewrite ?unsigned_lit in PO by lia.
  destruct PO as (p5 & p6 & p7 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p28 & p29 & p30 & p31 & m4 & -> & MU4 & WM4 & MI4 & HP4 & _).
  replace (ret_pc (Z_to_bv 64 0x19ccb4)) with (Z_to_bv 64 0x19ccb4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU4 WM4) in FR; [| cbn; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU4 WM4) in HPP1; [| cbn; lia].
  assert (ST4 : stk ctusegs m4 lo (bv_unsigned sp + -64)) by (eapply stk_transport; [exact ST1| exact MU4| exact WM4| cbn; lia]).
  assert (MU' : munch [(bv_unsigned sp - 112, bv_unsigned sp); (PP, PP + 8); (P, P + bn)]%Z m m4).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MU4]]; unfold sub_fp; cbn [outside]; intros y Hy; lia. }
  assert (WM' : wmono ctusegs m m4) by (eapply wmono_trans; [exact WM| exact WM4]).
  clear MU WM MU4 WM4 MI1 ST1 BLOB HX. rename MU' into MU. rename WM' into WM.
  (* [comment removed for export] *)
  zstep. zstep. rewrite Z.add_0_r, (swrap32_small bn) by lia. do 7 zstep. zstep. release_frame FR ST4 (bv_unsigned sp). zstep.
  apply evt_done. do 14 eexists. eexists. split; [reflexivity|]. repeat (split; [assumption|]). exact HP4.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition I2O_SCT_W_STACK : Z := 64 + I2O_SIG_STACK.

Lemma i2o_sct_write_v1_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (adr : bptr -> Z) (x : sctr bptr) (vs : Z) (PP P : Z)
    (lq sq : bptr) (sn en : Z) (lid ext sig j0 j1 j2 j3 j4 j5 : list byte),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - I2O_SCT_W_STACK -> bv_unsigned sp mod 16 = 0 ->
  0 < adr (sc_blk x) -> adr (sc_blk x) + SCT_SIZE <= lo -> adr (sc_blk x) mod 8 = 0 ->
  rw_cells ctusegs m (adr (sc_blk x)) (sct_cells adr x (-1) vs) -> sct_ok adr x -> sct_complete x = true ->
  sc_version x = 0 -> sc_logid x = Some lq -> sc_sig x = Some (sq, sn) -> sc_extlen x = en ->
  bv_unsigned sp <= PP -> PP + 8 <= 2^64 -> rw_cells ctusegs m PP [C8 (Z_to_bv 64 P)] -> PP mod 8 = 0 -> 0 < P -> P + 47 + en + sn <= lo ->
  (adr (sc_blk x) + SCT_SIZE <= P \/ P + 47 + en + sn <= adr (sc_blk x)) ->
  adr lq + 32 <= lo -> (adr lq + 32 <= P \/ P + 47 + en + sn <= adr lq) -> bytes_at ctusegs m (adr lq) lid -> length lid = 32%nat ->
  adr sq + sn <= lo -> (adr sq + sn <= P \/ P + 47 + en + sn <= adr sq) -> bytes_at ctusegs m (adr sq) sig -> length sig = Z.to_nat sn ->
  (forall eq, sc_ext x = Some (eq, en) -> adr eq + en <= lo /\ (adr eq + en <= P \/ P + 47 + en + sn <= adr eq) /\ bytes_at ctusegs m (adr eq) ext /\ length ext = Z.to_nat en) ->
  rw_cells ctusegs m P [CB 1%nat j0] -> rw_cells ctusegs m (P + 1) [CB 32%nat j1] -> rw_cells ctusegs m (P + 33) [CB 10%nat j2] ->
  rw_cells ctusegs m (P + 43) [CB (Z.to_nat en) j3] -> rw_cells ctusegs m (P + 43 + en) [CB 4%nat j4] -> rw_cells ctusegs m (P + 47 + en) [CB (Z.to_nat sn) j5] ->
  a0 = Z_to_bv 64 (adr (sc_blk x)) -> a1 = Z_to_bv 64 PP ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' hb0 hb2 hb3 hb4,
       ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (47 + en + sn)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom ctusegs)
       /\ munch [(bv_unsigned sp - I2O_SCT_W_STACK, bv_unsigned sp); (PP, PP + 8); (P, P + 47 + en + sn)]%Z m m' /\ wmono ctusegs m m'
       /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
       /\ rw_cells ctusegs m' PP [C8 (Z_to_bv 64 (P + 47 + en + sn))]
       /\ rw_cells ctusegs m' P [CB 1%nat hb0] /\ rw_cells ctusegs m' (P + 1) [CB 32%nat lid] /\ rw_cells ctusegs m' (P + 33) [CB 10%nat hb2]
       /\ rw_cells ctusegs m' (P + 43) [CB (Z.to_nat en) hb3] /\ rw_cells ctusegs m' (P + 43 + en) [CB 4%nat hb4] /\ rw_cells ctusegs m' (P + 47 + en) [CB (Z.to_nat sn) sig])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 I2O_SCT) fc None m (seg_rom ctusegs)).
Proof.
  intros until j5. intros ST MI GLO LO SP16 A0 ALO AL8 HX OK CPL V0 EL ES EE PPlo PPhi HPP PP8 P0 PLO SEPA LQLO SEPL LID LIDL SQLO SEPS SIG SLEN EXT R0 R1 R2 R3 R4 R5 -> ->.
  change (frozen (adr lq + 32 <= P \/ P + 47 + en + sn <= adr lq)) in SEPL. change (frozen (adr sq + sn <= P \/ P + 47 + en + sn <= adr sq)) in SEPS.
  assert (LIDF : frozen (bytes_at ctusegs m (adr lq) lid)) by exact LID. clear LID.
  assert (SIGF : frozen (bytes_at ctusegs m (adr sq) sig)) by exact SIG. clear SIG.
  assert (HXF : frozen (rw_cells ctusegs m (adr (sc_blk x)) (sct_cells adr x (-1) vs))) by exact HX.
  pose proof OK as (VR & HR & GR & SIGP & BLOBP & LOGP & ELR & BLR & EXTP & EXTL & BLBL).
  pose proof (SIGP sq sn ES) as [SQ0 SN]. pose proof (LOGP lq EL) as LQ0.
  assert (LEN : i2o_sct_len x = 47 + en + sn) by (unfold i2o_sct_len, sc_siglen; rewrite V0, ES, EE; cbn [Z.eqb]; lia).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold I2O_SCT_W_STACK, I2O_SIG_STACK in *.
  eapply i2o_sct_write_fwd with (lo := lo) (adr := adr) (x := x) (vs := vs) (PP := PP) (P := P); try eassumption; try reflexivity; try (unfold I2O_SCT_LEN_STACK; lia).
  intros m1 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 MU WM MI1 ST1 FR HPP1. rewrite LEN in *. unfold GLOBALS_TOP, SCT_SIZE, I2O_SCT_LEN_STACK in *.
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU WM) in HX; [| rewrite sct_cells_size; cbn; unfold SCT_SIZE; lia].
  Ltac xport H MU WM := apply (fun H0 => rw_cells_transport _ _ _ _ _ _ H0 MU WM) in H; [| cbn [cells_size csize]; rewrite ?Nat.add_0_r, ?Z2Nat.id by lia; cbn; lia].
  xport R0 MU WM. xport R1 MU WM. xport R2 MU WM. xport R3 MU WM. xport R4 MU WM. xport R5 MU WM.
  apply (munch_weaken _ [(bv_unsigned sp - 160, bv_unsigned sp); (PP, PP + 8); (P, P + 47 + en + sn)]%Z) in MU; [| unfold sub_fp; cbn [outside]; intros y Hy; lia].
  assert (SNE : sc_siglen x = sn) by (unfold sc_siglen; rewrite ES; reflexivity).
  unfold sct_cells, MallocRep.wz, u32 in HX. rewrite V0, EL, ES, EE, SNE in HX. cbn [optr osz32 option_map logid_len] in HX. change (0 mod 2 ^ 32) with 0 in HX.
  rewrite V0.
  (* [comment removed for export] *)
  zstep. btaken. ub. zstep. zstep. zstep. zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
  assert (LID : bytes_at ctusegs m2 (adr lq) lid).
  { pose proof LIDF as X. unfold frozen in X. pose proof SEPL as Y. unfold frozen in Y.
    eapply bytes_at_transport; [exact X| exact MU|]. rewrite LIDL. cbn. lia. }
  eapply evt_cut.
  { eapply memcpy_spec with (src := lid) (junk := j1); rewrite ?unsigned_lit by lia; [exact LID| rewrite LIDL; reflexivity| exact R1| pose proof SEPL as Y; unfold frozen in Y; lia| assumption]. }
  cbv beta. intros ms3 PO. unfold memcpy_post in PO. rewrite ?unsigned_lit in PO by lia.
  destruct PO as (p5 & p6 & p7 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p28 & p29 & p30 & p31 & m3 & -> & MU3 & WM3 & MI3 & R1' & _).
  replace (ret_pc (Z_to_bv 64 0x19ccdc)) with (Z_to_bv 64 0x19ccdc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  xport FR MU3 WM3. xport HPP1 MU3 WM3. xport R0 MU3 WM3. xport R2 MU3 WM3. xport R3 MU3 WM3. xport R4 MU3 WM3. xport R5 MU3 WM3.
  apply (fun H0 => rw_cells_transport _ _ _ _ _ _ H0 MU3 WM3) in HX; [| cbn; lia].
  assert (ST3 : stk ctusegs m3 lo (bv_unsigned sp + -64)) by (eapply stk_transport; [exact ST1| exact MU3| exact WM3| cbn; lia]).
  assert (MU' : munch [(bv_unsigned sp - 160, bv_unsigned sp); (PP, PP + 8); (P, P + 47 + en + sn)]%Z m m3).
  { eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU3]]; unfold sub_fp; cbn [outside]; intros y Hy; lia. }
  assert (WM' : wmono ctusegs m m3) by (eapply wmono_trans; [exact WM| exact WM3]).
  clear MU WM MU3 WM3 MI1 ST1 LID R1. rename MU' into MU. rename WM' into WM. rename R1' into R1.
  (* [comment removed for export] *)
  ub. ts_read HX 40 6%nat 7 1%nat RD7. zstep. clear RD7. zstep. zstep. zstep. zstep. zstep. ub.
  ts_read HX 40 6%nat 6 2%nat RD6. zstep. clear RD6. zstep. zstep. ub.
  zstep. zstep. zstep. zstep. zstep. ub.
  ts_read HX 40 6%nat 4 4%nat RD4. zstep. clear RD4. zstep. zstep. ub.
  zstep. zstep. zstep. zstep. zstep. ub. zstep. zstep. zstep. zstep. ub. zstep. zstep. zstep. zstep. zstep. ub. zstep. zstep.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. ub. zstep. zstep. zstep. ub.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
  (* [comment removed for export] *)
  assert (JOIN : forall m5 (y1 y10 y11 y12 : word) (y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) hb3,
    munch [(bv_unsigned sp - 160, bv_unsigned sp); (PP, PP + 8); (P, P + 47 + en + sn)]%Z m m5 -> wmono ctusegs m m5 -> mem_inv ctusegs m5 ->
    stk ctusegs m5 lo (bv_unsigned sp + -64) ->
    rw_cells ctusegs m5 (bv_unsigned sp + -64) [C8 (Z_to_bv 64 (P + 43 + en)); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells ctusegs m5 PP [C8 (Z_to_bv 64 (P + (47 + en + sn)))] ->
    rw_cells ctusegs m5 (adr (sc_blk x)) (sct_cells adr x (-1) vs) ->
    (exists hb0, rw_cells ctusegs m5 P [CB 1%nat hb0]) -> rw_cells ctusegs m5 (P + 1) [CB 32%nat lid] -> (exists hb2, rw_cells ctusegs m5 (P + 33) [CB 10%nat hb2]) ->
    rw_cells ctusegs m5 (P + 43) [CB (Z.to_nat en) hb3] -> rw_cells ctusegs m5 (P + 43 + en) [CB 4%nat j4] -> rw_cells ctusegs m5 (P + 47 + en) [CB (Z.to_nat sn) j5] ->
    evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' hb0 hb2 hb3 hb4,
       ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (47 + en + sn)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom ctusegs)
       /\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (PP, PP + 8); (P, P + 47 + en + sn)]%Z m m' /\ wmono ctusegs m m'
       /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
       /\ rw_cells ctusegs m' PP [C8 (Z_to_bv 64 (P + 47 + en + sn))]
       /\ rw_cells ctusegs m' P [CB 1%nat hb0] /\ rw_cells ctusegs m' (P + 1) [CB 32%nat lid] /\ rw_cells ctusegs m' (P + 33) [CB 10%nat hb2]
       /\ rw_cells ctusegs m' (P + 43) [CB (Z.to_nat en) hb3] /\ rw_cells ctusegs m' (P + 43 + en) [CB 4%nat hb4] /\ rw_cells ctusegs m' (P + 47 + en) [CB (Z.to_nat sn) sig])
    (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp y5 y6 y7 sp (Z_to_bv 64 (47 + en + sn))
             y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 0) (Z_to_bv 64 (P + 43)) (Z_to_bv 64 (P + 1)) s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
        F (Z_to_bv 64 0x19cde8) fc None m5 (seg_rom ctusegs))).
  { intros m5 y1 y10 y11 y12 y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 hb3 MU5 WM5 MI5 ST5 FR5 HPP5 HX5 [hb0 R05] R15 [hb2 R25] R35 R45 R55.
    clear MU WM FR HPP1 HX R0 R1 R2 R3 R4 R5 MI3 ST3.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
    pose proof (cells_pick_rw m5 (bv_unsigned sp + -64) 0 [] (C8 (Z_to_bv 64 (P + 43 + en))) _ FR5 eq_refl) as HPP2. rewrite Z.add_0_r in HPP2.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    eapply evt_cut.
    { eapply i2o_sct_sig_write_spec with (lo := lo) (adr := adr) (x := x) (vs := vs) (PP := bv_unsigned sp + -64) (P := P + 43 + en) (sq := sq) (sn := sn) (sig := sig) (j3 := j4) (j4 := j5);
        rewrite ?ESP; try eassumption; try reflexivity; try (unfold I2O_SIG_STACK, GLOBALS_TOP, SCT_SIZE; lia).
      all: try (pose proof SEPS as Y; unfold frozen in Y; unfold SCT_SIZE; lia).
      all: try (replace (P + 43 + en + 4) with (P + 47 + en) by lia; exact R55).
      all: match goal with
           | |- bytes_at _ _ _ _ => pose proof SIGF as X; unfold frozen in X; pose proof SEPS as Y; unfold frozen in Y;
                                  eapply bytes_at_transport; [exact X| exact MU5|]; rewrite SLEN, Z2Nat.id by lia; cbn; lia
           | |- sct_sig_complete _ = true => unfold sct_sig_complete, sct_nid; rewrite V0; unfold sct_complete, sct_sig_complete, sct_nid in CPL;
                                  rewrite V0 in CPL; cbn [Z.eqb] in CPL; rewrite EL in CPL; cbn [andb] in CPL; exact CPL
           end. }
    cbv beta. intros ms6 PO.
    destruct PO as (o5 & o6 & o7 & o11 & o12 & o13 & o14 & o15 & o16 & o17 & o28 & o29 & o30 & o31 & m6 & hb4 & -> & MU6 & WM6 & MI6 & ST6 & HPP6 & R46 & R56). rewrite ESP in *.
    unfold I2O_SIG_STACK in MU6.
    replace (ret_pc (Z_to_bv 64 0x19cdf4)) with (Z_to_bv 64 0x19cdf4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    change ([C8 (Z_to_bv 64 (P + 43 + en)); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) with ([C8 (Z_to_bv 64 (P + 43 + en))] ++ [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) in FR5.
    apply rw_cells_app in FR5. destruct FR5 as [_ FR5]. cbn [cells_size csize Nat.add] in FR5.
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU6 WM6) in FR5; [| cbn; lia].
    assert (FR : rw_cells ctusegs m6 (bv_unsigned sp + -64) ([C8 (Z_to_bv 64 (P + 43 + en + 4 + sn))] ++ [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply rw_cells_app. split; [exact HPP6| exact FR5]. }
    clear FR5 HPP6 HPP2. cbn [app] in FR.
    Ltac xport6 H MU WM := apply (fun H0 => rw_cells_transport _ _ _ _ _ _ H0 MU WM) in H; [| cbn [cells_size csize]; rewrite ?Nat.add_0_r, ?Z2Nat.id by lia; cbn; lia].
    xport6 HPP5 MU6 WM6. xport6 R05 MU6 WM6. xport6 R15 MU6 WM6. xport6 R25 MU6 WM6. xport6 R35 MU6 WM6.
    assert (MU' : munch [(bv_unsigned sp - 160, bv_unsigned sp); (PP, PP + 8); (P, P + 47 + en + sn)]%Z m m6).
    { eapply munch_trans; [exact MU5| eapply munch_weaken; [| exact MU6]]; unfold sub_fp; cbn [outside]; intros y Hy; lia. }
    assert (WM' : wmono ctusegs m m6) by (eapply wmono_trans; [exact WM5| exact WM6]).
    clear MU5 WM5 MU6 WM6 MI5 ST5 HX5 R45 R55. rename MU' into MU. rename WM' into WM.
    (* [comment removed for export] *)
    zstep. sfalse. zstep. zstep. rewrite Z.add_0_r, (swrap32_small (47 + en + sn)) by lia.
    do 7 zstep. zstep. release_frame FR ST6 (bv_unsigned sp). zstep.
    apply evt_done. do 14 eexists. lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx, hb0, hb2, hb3, hb4 end. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST6|].
    split; [replace (P + 47 + en + sn) with (P + (47 + en + sn)) by lia; exact HPP5|].
    split; [exact R05|]. split; [exact R15|]. split; [exact R25|]. split; [exact R35|].
    split; [exact R46| replace (P + 47 + en) with (P + 43 + en + 4) by lia; exact R56]. }
  (* [comment removed for export] *)
  assert (HXc : forall m5, munch [(bv_unsigned sp - 160, bv_unsigned sp); (PP, PP + 8); (P, P + 47 + en + sn)]%Z m m5 -> wmono ctusegs m m5 ->
                 rw_cells ctusegs m5 (adr (sc_blk x)) (sct_cells adr x (-1) vs)).
  { intros m5 MU5 WM5. pose proof HXF as X. unfold frozen in X. eapply rw_cells_transport; [exact X| exact MU5| exact WM5|]. rewrite sct_cells_size. unfold SCT_SIZE. cbn. lia. }
  destruct (Z.eq_dec en 0) as [EN0|ENP].
  - (* [comment removed for export] *)
    zstep. strue. rewrite !EN0 in *. rewrite ?Z.add_0_r in *.
    eapply JOIN; [exact MU| exact WM| exact MI3| exact ST3| exact FR| exact HPP1| apply HXc; [exact MU| exact WM]
                 | blob_of R0| exact R1| blob_of R2| exact R3| exact R4| exact R5].
  - (* [comment removed for export] *)
    destruct (sc_ext x) as [[eq n]|] eqn:EX; [| exfalso; lia]. assert (n = en) as -> by lia.
    destruct (EXT eq eq_refl) as (EQLO & SEPE & EXTB & EXTLEN). pose proof (EXTP eq en eq_refl) as EQ0.
    change (frozen (adr eq + en <= P \/ P + 47 + en + sn <= adr eq)) in SEPE.
    cbn [optr] in HX.
    zstep. sfalse. zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    assert (EXTB5 : bytes_at ctusegs m5 (adr eq) ext).
    { pose proof SEPE as Y. unfold frozen in Y. eapply bytes_at_transport; [exact EXTB| exact MU|]. rewrite EXTLEN, Z2Nat.id by lia. cbn. lia. }
    eapply evt_cut.
    { eapply memcpy_spec with (src := ext) (junk := j3); rewrite ?unsigned_lit by lia; [exact EXTB5| exact EXTLEN| exact R3| pose proof SEPE as Y; unfold frozen in Y; lia| assumption]. }
    cbv beta. intros ms6 PO. unfold memcpy_post in PO. rewrite ?unsigned_lit in PO by lia.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m6 & -> & MU6 & WM6 & MI6 & R3' & _).
    replace (ret_pc (Z_to_bv 64 0x19cdd4)) with (Z_to_bv 64 0x19cdd4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    xport FR MU6 WM6. xport HPP1 MU6 WM6. xport R0 MU6 WM6. xport R1 MU6 WM6. xport R2 MU6 WM6. xport R4 MU6 WM6. xport R5 MU6 WM6.
    apply (fun H0 => rw_cells_transport _ _ _ _ _ _ H0 MU6 WM6) in HX; [| cbn; lia].
    assert (ST6 : stk ctusegs m6 lo (bv_unsigned sp + -64)) by (eapply stk_transport; [exact ST3| exact MU6| exact WM6| cbn; lia]).
    assert (MU' : munch [(bv_unsigned sp - 160, bv_unsigned sp); (PP, PP + 8); (P, P + 47 + en + sn)]%Z m m6).
    { eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU6]]; unfold sub_fp; cbn [outside]; intros y Hy; lia. }
    assert (WM' : wmono ctusegs m m6) by (eapply wmono_trans; [exact WM| exact WM6]).
    clear MU WM MU6 WM6 MI3 ST3 R3 EXTB5. rename MU' into MU. rename WM' into WM. rename R3' into R3.
    (* [comment removed for export] *)
    zstep. ub. zstep. zstep.
    eapply JOIN; [exact MU| exact WM| exact MI6| exact ST6| exact FR| exact HPP1| apply HXc; [exact MU| exact WM]
                 | blob_of R0| exact R1| blob_of R2| exact R3| exact R4| exact R5].
Qed.
End WithCeiling.
