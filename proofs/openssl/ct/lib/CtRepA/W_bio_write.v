(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac ZBridge RzCPS Arr FP Frame Cells Step Mem. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Malloc Prog BnBase BnModel BnTree ApBase ApLogic ApErr.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs I_lkit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem BnTacX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA ImplA ImplAX BnIfaceA AsStruct RtCallA UnwindA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require W_bio_write.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApUTacB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_akit W_bio_ctrl W_bio_push Fr_bio_write_intern Fr_BIO_puts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Import ListNotations.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.

(* [comment removed for export] *)
Lemma land_pow2_small : forall d n, 0 <= d < 2^n -> 0 <= n -> Z.land d (2^n) = 0.
Proof.
  intros d n Hd Hn. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.pow2_bits_eqb, Z.bits_0 by lia.
  destruct (Z.eqb_spec n i); [|apply andb_false_r]. subst i.
  destruct (Z.eq_dec d 0) as [->|NZ]; [rewrite Z.bits_0; reflexivity|].
  rewrite (Z.bits_above_log2 d n); [reflexivity| lia|]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma slt_mask_pos : forall d, 0 < d < 2^63 ->
  Z.land (Z.land (0 + - Z.b2z (9223372036854775808 <? Z.lxor d 9223372036854775808)) 18446744073709551615) d = d.
Proof.
  intros d Hd. change 9223372036854775808 with (2^63).
  rewrite <- Z.add_nocarry_lxor by (apply land_pow2_small; lia).
  replace (2 ^ 63 <? d + 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia).
  change (Z.land (0 + - Z.b2z true) 18446744073709551615) with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma slt_mask_posA : forall d, 0 < d < 2^63 ->
  Z.land (bv_unsigned (Z_to_bv 64 (0 + - bv_unsigned (v_slt (Z_to_bv 64 0) (Z_to_bv 64 d))))) (bv_unsigned (Z_to_bv 64 d)) = d.
Proof.
  intros d Hd. rewrite v_slt_b2z. rewrite !Z_to_bv_unsigned.
  change (bv_wrap 64 0) with 0. rewrite (bv_wrap_small 64 d) by (unfold bv_modulus; cbn; lia).
  rewrite Z.lxor_0_l. change (2 ^ 63) with 9223372036854775808.
  rewrite <- (Z.add_nocarry_lxor d 9223372036854775808) by (change 9223372036854775808 with (2 ^ 63); apply land_pow2_small; lia).
  replace (9223372036854775808 <? d + 9223372036854775808) with true by (symmetry; apply Z.ltb_lt; lia).
  cbn [Z.b2z]. change (bv_wrap 64 1) with 1. change (bv_wrap 64 (0 + - (1))) with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma c8_small_as_c4 : forall m A pre z post,
  rw_cells ctasegs m A (pre ++ C8 (Z_to_bv 64 z) :: post) -> 0 <= z < 2^32 ->
  rw_cells ctasegs m A (pre ++ C4 (Z_to_bv 64 z) :: C4 (Z_to_bv 64 0) :: post).
Proof.
  intros m A pre z post H Hz. eapply rw_cells_recast; [exact H| | |].
  - destruct H as [[W _] _]. apply cells_wf_app in W. destruct W as [W1 W2]. cbn in W2. apply cells_wf_app. split; [exact W1|]. cbn. tauto.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes app]. rewrite (CtRepP.W_bio_write.le8_split_small z Hz). rewrite <- !app_assoc. reflexivity.
  - rewrite !cells_size_app. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma puts_clamp_small : forall n, 0 <= n < 2^31 ->
  Z.lor (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltiu (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 n)) 31)) 1) + -1))) (bv_unsigned (Z_to_bv 64 n)) = n.
Proof.
  intros n Hn. rewrite v_sltiu_b2z. rewrite !Z_to_bv_unsigned.
  rewrite (bv_wrap_small 64 n) by (unfold bv_modulus; cbn; lia).
  rewrite Z.shiftr_div_pow2, Z.div_small by lia.
  vm_compute (bv_wrap 64 0). vm_compute (bv_wrap 64 1). cbn [Z.ltb Z.b2z Z.compare]. vm_compute (bv_wrap 64 (1 + -1)). apply Z.lor_0_l.
Qed.

(* [comment removed for export] *)
Lemma v_addiw0_small : forall z, 0 <= z < 2^31 -> v_addiw (Z_to_bv 64 z) 0 = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold v_addiw. f_equal. rewrite unsigned_lit by lia. rewrite Z.add_0_r. apply bk_swrap32_small. lia.
Qed.

Definition BIO_WRITE : Z := 0x2384b8.
Definition BIO_WRITE_RA : Z := 0x2384d4.       (* [comment removed for export] *)
Definition BWRITE_CONV : Z := 0x239dac.
Definition NULL_WRITE : Z := 0x3233e8.
Definition BWI_CONV_RA : Z := 0x238710.        (* [comment removed for export] *)
(* [comment removed for export] *)
Definition BIO_WRITE_NULL_STACK : Z := 32 + BWI_FRAME + RT_STACK.
Definition BIO_PUTS : Z := 0x238ae8.
Definition NULL_PUTS : Z := 0x323430.
Definition NULL_PUTS_SL_RA : Z := 0x323450.    (* [comment removed for export] *)
Definition BPUTS_PUTS_RA : Z := 0x238cd8.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition BIO_PUTS_NULL_STACK : Z := BPUTS_FRAME + 16 + RT_STACK.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Lemma null_meth_wr_img : forall (AR' : ARun) Σ OW LB m, @BnHeapA.AHEAP AR' Σ OW LB m ->
  ro_cells ctasegs m (NULL_METHOD + 16) [C8 (Z_to_bv 64 BWRITE_CONV); C8 (Z_to_bv 64 NULL_WRITE)] /\ acc ctasegs m NULL_METHOD 112.
Proof.
  intros AR' Σ OW LB m H. pose proof (@AH_art AR' _ _ _ _ H) as HA. split.
  - apply (relro_ro_cells m (NULL_METHOD + 16) _ (af_relro _ (@ar_AF AR') Σ m HA)); [cbn; auto| unfold RELRO_LO, NULL_METHOD; lia| unfold RELRO_HI, NULL_METHOD; cbn; lia| vm_compute; reflexivity].
  - eapply (af_lib_acc_lit _ (@ar_AF AR') Σ m (0x54daa0, 112, 160)); [exact HA| vm_compute; reflexivity| cbn; unfold NULL_METHOD; lia| cbn; unfold NULL_METHOD; lia].
Qed.

(* [comment removed for export] *)
Definition bio_write_null_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (out pv nw dlen lo : Z) (m : mem) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 dlen) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp)
    /\ apres_ex LB OW (bv_unsigned sp) [(out, out + BIO_SIZE)]%Z m m'
    /\ AHEAP Σ' OW LB m'
    /\ rt_live RT Σ' = rt_live RT Σ /\ rt_credit RT Σ - 1 <= rt_credit RT Σ'
    /\ rw_cells ctasegs m' out (bio_null_cells NULL_METHOD pv (nw + dlen)).

(* [comment removed for export] *)
Lemma BIO_write_null_cpsA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z) (pb : bptr) (out pv nw dlen : Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + BIO_WRITE_NULL_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> (length FR < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  In (pb, out, BIO_SIZE) OW -> rw_cells ctasegs m out (bio_null_cells NULL_METHOD pv nw) -> 0 <= nw < 2^64 ->
  a0 = wz out -> a2 = wz dlen -> 0 < dlen < 2^31 - 1 ->
  cps ctasegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz BIO_WRITE) fc None m (seg_rom ctasegs))))
      (fun c => exists Σ', ASTA RT Σ' PMc (bio_write_null_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB out pv nw dlen lo m Σ') c
                /\ rt_live RT Σ' = rt_live RT Σ)      (* [comment removed for export] *).
Proof.
  intros until dlen. intros HEAP ST CEIL LO SPT SP16 MI -> FLEN CRED HBIN HO NW0 -> -> DL.
  unfold BIO_WRITE_NULL_STACK, BWI_FRAME, RT_STACK, BIO_WRITE, BIO_SIZE, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (CL1 & CL2 & CL3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CL1, CL2, CL3. unfold USTACK_TOP in SPT.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (HBIN' : In (pb, out, 128) (OW ++ LB)) by (apply in_or_app; left; exact HBIN).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HBIN') as (BB0 & _ & _ & BB3 & BB4). cbn [blk_addr blk_size fst snd] in BB0, BB3, BB4.
  pose proof (proj1 (AH_okA _ _ _ _ _ _ _ HEAP HBIN)) as ALB.
  unfold bio_null_cells, bio_cells, MallocRep.wz in HO.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  carve_frame 32%nat ST. do 4 step.
  step. if_cases Hqd; zify_cond Hqd; [exfalso; rewrite (proj2 (Z.ltb_lt _ _)) in Hqd by lia; rewrite (proj2 (Z.ltb_lt _ _)) in Hqd by lia; discriminate| try clear Hqd].
  step. step.
  name_mem m1.
  match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
  assert (ESP1 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; clear - SPR LO LO0; lia).
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [left; cbn; clear - CEIL LO SPT; unfold BnHeapA.ACEIL, USTACK_TOP in *; lia| constructor]. }
  apply evt_done.
  eapply (bwi_pro_cps _) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP1 | rewrite ESP1; exact ST | exact CEIL | rewrite ESP1; unfold BWI_FRAME, RT_STACK; clear - LO; lia
    | rewrite ESP1; unfold USTACK_TOP; clear - SPT; lia | rewrite ESP1; uchk_open; clear - SP16 SPR LO LO0; Z.div_mod_to_equations; lia
    | assumption | reflexivity | exact FLEN | exact CRED |].
  intros Σ1 m3 f spa g jk gj ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' j0 j8 j16 j24 j32 j40 jf24 jf32 jf40 (* [comment removed for export] *)
         HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AGF FRL FRH FRF FRS SPA32 SPAL SPAH GSZ SAVJ.
  rewrite ?ESP1 in *. unfold BWI_BODY, MallocRep.wz.
  (* [comment removed for export] *)
  pose proof (@AH_ceil (push AR f 0) _ _ _ _ HEAP3) as (D1 & D2 & D3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in D1, D2, D3. cbn [ar_SP0 push amb] in D1, D2, D3.
  destruct GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 0) with 64 in G3, G5. unfold SEGTOP_A in G4.
  assert (Ef : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; clear - G1 G3 D3; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; lia).
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - SPAL SPAH SPR LO LO0; lia).
  pose proof (FRESH _ HBIN') as OFFB. unfold off_fr in OFFB. cbn [blk_addr blk_size fst snd] in OFFB. change (fs_size 0) with 64 in OFFB.
  (* [comment removed for export] *)
  apply (rw_cells_agree _ _ _ _ _ AGF) in FR; [| intros a Ha; cbn in Ha; left; unfold USTACK_TOP; clear - Ha SPT; lia].
  apply (rw_cells_agree _ _ _ _ _ AGF) in HO; [| intros a Ha; cbn in Ha; right; right; exists (pb, out, 128); split; [exact HBIN'| cbn; clear - Ha; lia]].
  (* [comment removed for export] *)
  ablock HEAP3 HBIN' ACCO OFFO.
  assert (ACCW : acc ctasegs m3 (bv_unsigned sp + -24) 8).
  { destruct HEAP3 as (HA3 & HS3 & _). apply (af_acc_stack RT AF Σ1 m3 _ 8 HA3); [| unfold USTACK_TOP; clear - SPT; lia].
    rewrite HS3. cbn [ar_SP0 push amb]. unfold BnHeapA.ACEIL in CEIL. clear - CEIL LO. lia. }
  destruct (null_meth_wr_img _ _ _ _ _ HEAP3) as [HM ACCM]. change (NULL_METHOD + 16) with 5561008 in HM. unfold NULL_METHOD, BWRITE_CONV, NULL_WRITE in HM, ACCM.
  assert (ACCF : acc ctasegs m3 (f + 32) 8).
  { eapply (acc_of_shadow_cells m3 (shad f) bwi_shadow_pro 4 (f + 32) 8 FRS); [clear - G2; Z.div_mod_to_equations; lia| clear - G1; lia| clear; lia
      | unfold shad; clear - G2; Z.div_mod_to_equations; lia| cbn; clear; lia| reflexivity]. }
  assert (SHR : 2147450880 <= shad f /\ shad f + 8 <= 17594333495296).
  { unfold shad, SHB. pose proof (Z.div_pos f 8 ltac:(clear - G1; lia) ltac:(clear; lia)) as DP.
    assert (DQ : f / 8 + 8 <= 2 ^ 44).
    { assert (DR : f / 8 < 2 ^ 44 - 8); [apply Z.div_lt_upper_bound; [clear; lia|]; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; clear - G3 D3; lia | clear - DR; lia]. }
    clear - DP DQ; lia. }
  pose proof (munch_refl [(spa - 48, spa); (spa + 16, spa + 32); (f + 32, f + 40); (out, out + 128); (bv_unsigned sp - 32, bv_unsigned sp)]%Z m3) as MU3.
  pose proof (wmono_refl ctasegs m3) as WM3.
  assert (OFF3 : offshW [(spa - 48, spa); (spa + 16, spa + 32); (f + 32, f + 40); (out, out + 128); (bv_unsigned sp - 32, bv_unsigned sp)]%Z).
  { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. cbn [ar_SP0 push amb] in *. clear - D1 D2 D3 CEIL LO SPAL SPAH OFFO G5 SPT. lia. }
  unfold NULL_METHOD in HO.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  step. if_cases Hqw; zify_cond Hqw; [exfalso; rewrite ?unsigned_lit in Hqw by (clear - SPR LO LO0; lia); clear - Hqw SPR LO LO0; lia|]. clear Hqw.
  step.
  step. if_cases Hqb; zify_cond Hqb; [exfalso; rewrite ?unsigned_lit in Hqb by (clear - BB0 BB3 D3; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; lia); clear - Hqb BB0; lia|]. clear Hqb.
  (* [comment removed for export] *)
  step. step. if_cases Hqm; zify_cond Hqm; [exfalso; revert Hqm; vm_compute; congruence|]. clear Hqm.
  step. step. if_cases Hqbw; zify_cond Hqbw; [exfalso; revert Hqbw; vm_compute; congruence|]. clear Hqbw.
  (* [comment removed for export] *)
  step. step. step. step. step. (* [comment removed for export] *)
  step. step. if_cases Hqcb; zify_cond Hqcb; [exfalso; apply Hqcb; reflexivity|]. clear Hqcb.
  (* [comment removed for export] *)
  step. step. if_cases Hqcx; zify_cond Hqcx; [| exfalso; apply Hqcx; reflexivity]. clear Hqcx.
  (* [comment removed for export] *)
  step. step. if_cases Hqin; zify_cond Hqin; [exfalso; revert Hqin; vm_compute; congruence|]. clear Hqin.
  (* [comment removed for export] *)
  step. step. step. step. step. step. step. step.
  (* [comment removed for export] *)
  carve_frame 32%nat ST3. do 7 step. step. step.
  step. if_cases Hqcl; zify_cond Hqcl; [| exfalso; rewrite ?unsigned_lit in Hqcl by (clear - DL; lia); clear - Hqcl DL; lia]. clear Hqcl.
  (* [comment removed for export] *)
  step. step. step.
  (* [comment removed for export] *)
  carve_frame 16%nat ST3. do 5 step. do 3 step. release_frame FR1 ST3 (spa - 32). step.
  try rewrite (ret_pc_even 0x239e18) by (clear; lia).
  (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. if_cases Hqr; zify_cond Hqr; [exfalso; rewrite (proj2 (Z.ltb_lt _ _)) in Hqr by lia; rewrite (proj2 (Z.ltb_lt _ _)) in Hqr by lia; discriminate| try clear Hqr].
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  do 9 step. release_frame FR0 ST3 spa. step.
  try rewrite (ret_pc_even 0x238710) by (clear; lia).
  (* [comment removed for export] *)
  step. step. if_false. (* [comment removed for export] *)
  step. step. step. step.
  (* [comment removed for export] *)
  step. step. step. step. (* [comment removed for export] *) first [if_false | if_cases Hqc2; zify_cond Hqc2; [exfalso; apply Hqc2; reflexivity|]; clear Hqc2].
  (* [comment removed for export] *)
  step. step. first [if_true | if_cases Hqc3; zify_cond Hqc3; [| exfalso; apply Hqc3; reflexivity]; clear Hqc3].
  step. if_cases Hqw2; zify_cond Hqw2; [exfalso; rewrite ?unsigned_lit in Hqw2 by (clear - SPR LO LO0; lia); clear - Hqw2 SPR LO LO0; lia|]. clear Hqw2.
  step. step. step.
  name_mem mk.
  match goal with H : munch _ m3 mk |- _ => rename H into MUk end. match goal with H : wmono ctasegs m3 mk |- _ => rename H into WMk end.
  (* [comment removed for export] *)
  assert (HEAPk : @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB mk).
  { eapply (@AH_frame_fr (push AR f 0) Σ1 OW LB m3 mk _ f 0%nat (or_introl eq_refl) HEAP3 MUk WMk); [| intros b Hb; apply FRESH; apply in_or_app; right; exact Hb].
    change (fs_size 0) with 64. clear - CEIL LO SPAL SPAH SPT HBIN'.
    assert (SIV : forall l h, lo <= l -> h <= bv_unsigned sp -> @fr_write_ok (push AR f 0) (OW ++ LB) f 0 (l, h)).
    { intros l h Hl Hh. left. left. cbn [fst snd]. unfold BnHeapA.ACEIL, USTACK_TOP, STACK_WIN in *. cbn [ar_SP0 push amb] in *. lia. }
    constructor; [apply SIV; lia|]. constructor; [apply SIV; lia|].
    constructor; [right; left; cbn [fst snd]; change (fs_size 0) with 64; lia|].
    constructor; [left; right; right; exists (pb, out, 128); split; [exact HBIN'| cbn; lia]|].
    constructor; [apply SIV; lia| constructor]. }
  apply (rw_cells_cb_first mk spa _ 6) in FRL. cbn [cb_first csize cbytes] in FRL.
  apply evt_done.
  eapply (bwi_epi_cps _) with (lo := lo) (LB := LB) (gj := gj) (hrest := []); rewrite ?ESP1;
    [exact HEAPk | intros b Hb; apply FRESH; apply in_or_app; right; exact Hb | exact ST3 | exact CEIL | clear - LO SPAL; lia | unfold USTACK_TOP; clear - SPT; lia
    | exact SPAL | exact SPAH | exact GSZ | exact SAVJ | assumption | exact FRL | exact FRH | reflexivity |].
  intros Σ' m' HEAP' CR' EL' ST' MI' AG'.
  unfold BIO_WRITE_RA. rewrite (ret_pc_even 0x2384d4) by (clear; lia).
  (* [comment removed for export] *)
  apply (rw_cells_agree _ _ _ _ _ AG') in FR; [| intros a Ha; cbn in Ha; left; unfold USTACK_TOP; clear - Ha SPT SPAH; lia].
  apply (rw_cells_agree _ _ _ _ _ AG') in HO; [| intros a Ha; cbn in Ha; right; right; exists (pb, out, 128); split; [exact HBIN'| cbn; clear - Ha; lia]].
  rewrite (slt_mask_posA dlen) in FR, HO by (clear - DL; lia).
  lazymatch type of FR with rw_cells _ _ _ (?c0 :: C8 (Z_to_bv 64 dlen) :: ?rest) =>
    apply (c8_small_as_c4 _ _ [c0] dlen rest) in FR; [| clear - DL; lia] end. cbn [app] in FR.
  pose proof (munch_refl []%Z m') as MU9. pose proof (wmono_refl ctasegs m') as WM9.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  step. if_false.
  step. rewrite (sx32_small dlen) by (clear - DL; lia).
  step. step. step. step. release_frame FR ST' (bv_unsigned sp). step.
  apply evt_done. apply cps_post. intros c Hc. exists Σ'. split; [| rewrite EL', EL1; reflexivity].
  eapply ASTA_conseq; [exact Hc|]. intros ms0 <-. unfold bio_write_null_post, MallocRep.wz.
  do 16 eexists. exists m'. split; [reflexivity|].
  split; [exact MI'|]. split; [assumption|].
  split.
  { (* [comment removed for export] *)
    unfold apres_ex.
    assert (INC : forall b : block, In b (OW ++ LB) -> In b (OW ++ LB)) by (intros b Hb; exact Hb).
    eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU1)|];
      intros a [Ha _]; eapply (acl_outside1 _ _ _ _ _ _ lo 32); [exact HEAP| exact INC| exact CEIL| clear - LO; lia| exact Ha]|].
    eapply agree_on_trans; [eapply agree_on_mono; [exact AGF|]; intros a [Ha _]; eapply acl_sub; [exact INC| | exact Ha]; clear; lia|].
    eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MUk)|]|].
    { intros a [Ha Hx]. cbn [outside fst snd] in Hx |- *. destruct Hx as [Hx _].
      assert (A1 : ~ (bv_unsigned sp - 32 <= a < bv_unsigned sp)) by (eapply (acl_off_frame _ _ _ _ _ _ lo 32); [exact HEAP| exact INC| exact CEIL| clear - LO; lia| exact Ha]).
      assert (A2 : ~ (spa - 48 <= a < spa + 32)).
      { intros Hr. apply (acl_off_frame _ _ _ _ _ (bv_unsigned sp) lo (32 + 176 + 65536) a HEAP INC CEIL ltac:(clear - LO; lia) Ha). clear - Hr SPAL SPAH. lia. }
      assert (A3 : ~ (f + 32 <= a < f + 40)).
      { intros Hr. destruct Ha as [Ha|[Ha|(b & Hb & Hrb)]].
        - unfold BnHeapA.ACEIL, USTACK_TOP in *. clear - Hr Ha G3 CEIL LO. cbn [ar_SP0 push amb] in *. lia.
        - destruct Ha as [(l & h & Hin & Hlh) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. clear - Hin Hlh Hr G4. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
        - pose proof (FRESH b Hb) as O. unfold off_fr in O. change (fs_size 0) with 64 in O. clear - O Hrb Hr. lia. }
      unfold BIO_SIZE in Hx. clear - A1 A2 A3 Hx. repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
    eapply agree_on_mono; [exact AG'|]. intros a [Ha _]. eapply acl_sub; [exact INC| | exact Ha]. clear - SPAH; lia. }
  split; [exact HEAP'|].
  split; [rewrite EL', EL1; reflexivity|]. split; [rewrite CR', CR1; clear; lia|].
  unfold bio_null_cells, bio_cells, MallocRep.wz. exact HO.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma strlen_img_cpsA : forall (AR' : ARun)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts (@ar_RT AR')) (OW LB : list block) (lo s : Z) (str slack : list byte),
  @BnHeapA.AHEAP AR' Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> @BnHeapA.ACEIL AR' <= lo -> lo + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A ->
  0x10000 <= s -> s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= SEGTOP_A -> acc ctasegs m s (Z.of_nat (length str) + 1) ->
  bytes_at ctasegs m s (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) < 2^40 ->
  (- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  a0 = wz s ->
  cps ctasegs (ASTA (@ar_RT AR') Σ (@ar_PMc AR') (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz e_strlen) fc None m (seg_rom ctasegs))))
            (ASTA (@ar_RT AR') Σ (@ar_PMc AR') (@icall_post AR' ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz (Z.of_nat (length str))) Σ OW LB lo 0 0 m
                                              (fun m' => agree_on (fun a => in_fframe (@ar_FR AR') a) m m'))).
Proof.
  intros until slack. intros HEAP ST CEIL LO SPT SP16 MI -> SLO SHI ACCS HS NONUL HN PAD ->.
  unfold MallocRep.wz in *.
  pose proof (@AH_ceil AR' _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  eapply cps_conseq; [ eapply (rc_strlen _ (@ar_RC AR') Σ (@ar_PMc AR')) with (s := s) (str := str) (slack := slack) (lo := lo); try reflexivity | intros c Hc; exact Hc | ].
  - exact (@ar_PMc_fdfs AR').
  - exact (@ar_PMc_ms AR').
  - exact HS.
  - exact NONUL.
  - exact HN.
  - exact PAD.
  - unfold BnHeapA.ACEIL in *. lia.
  - left. unfold BnHeapA.ACEIL in *. lia.
  - split; [| left; unfold BnHeapA.ACEIL in *; lia]. intros _. split; [exact ACCS|]. right; right; right. unfold SEGTOP_A. lia.
  - exact (@AH_art AR' _ _ _ _ HEAP).
  - exact MI.
  - rewrite <- (Z_to_bv_bv_unsigned sp). eapply (@call_okA AR'); [exact HEAP | exact ST | exact CEIL | exact LO | unfold USTACK_TOP; lia | exact SP16].
  - intros c Hc. eapply ASTA_conseq; [exact Hc|]. clear Hc.
    intros ms (m2 & RS & (ART2 & MI2 & WM2 & ST2) & PRES & _).
    destruct RS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
    unfold icall_post, MallocRep.wz. do 16 eexists. exists m2. split; [reflexivity|].
    split; [exact MI2|]. split; [exact ST2|].
    split. { eapply (@AH_same_ex AR'); [exact HEAP| exact ART2| exact WM2| exact PRES| right; right; lia]. }
    split; [exact WM2|].
    pose proof (@AH_frames AR' _ _ _ _ HEAP) as HF.
    split; [eapply (@AH_agree_ex AR' _ _ _ _ _ _ _ _ _ HEAP); rewrite <- HF; exact PRES |].
    intros a Ha Hf. apply PRES; unfold wa; rewrite unsigned_lit by exact Ha; [| clear; lia]. right; right; right; left. rewrite HF. exact Hf.
Qed.

(* [comment removed for export] *)
Lemma null_meth_puts_img : forall (AR' : ARun) Σ OW LB m, @BnHeapA.AHEAP AR' Σ OW LB m ->
  ro_cells ctasegs m (NULL_METHOD + 48) [C8 (Z_to_bv 64 NULL_PUTS)].
Proof.
  intros AR' Σ OW LB m H. pose proof (@AH_art AR' _ _ _ _ H) as HA.
  apply (relro_ro_cells m (NULL_METHOD + 48) _ (af_relro _ (@ar_AF AR') Σ m HA)); [cbn; auto| unfold RELRO_LO, NULL_METHOD; lia| unfold RELRO_HI, NULL_METHOD; cbn; lia| vm_compute; reflexivity].
Qed.

(* [comment removed for export] *)
Definition bio_puts_null_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (out pv nw n lo : Z) (m : mem) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp)
    /\ apres_ex LB OW (bv_unsigned sp) [(out, out + BIO_SIZE)]%Z m m'
    /\ AHEAP Σ' OW LB m'
    /\ rt_live RT Σ' = rt_live RT Σ /\ rt_credit RT Σ - 1 <= rt_credit RT Σ'
    /\ rw_cells ctasegs m' out (bio_null_cells NULL_METHOD pv (nw + n)).

(* [comment removed for export] *)
Lemma BIO_puts_null_cpsA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z) (pb : bptr) (out pv nw S : Z) (str slack : list byte),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + BIO_PUTS_NULL_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> (length FR < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  In (pb, out, BIO_SIZE) OW -> rw_cells ctasegs m out (bio_null_cells NULL_METHOD pv nw) -> 0 <= nw < 2^64 ->
  ro_bytes ctasegs S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  0x10000 <= S -> S + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= SEGTOP_A ->
  (forall (AR' : ARun) (Σ' : rts (@ar_RT AR')) m', @BnHeapA.AHEAP AR' Σ' OW LB m' -> acc ctasegs m' S (Z.of_nat (length str) + 1)) ->
  0 < Z.of_nat (length str) < 2^31 - 1 ->
  a0 = wz out -> a1 = wz S ->
  cps ctasegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz BIO_PUTS) fc None m (seg_rom ctasegs))))
      (fun c => exists Σ', ASTA RT Σ' PMc (bio_puts_null_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB out pv nw (Z.of_nat (length str)) lo m Σ') c
                /\ rt_live RT Σ' = rt_live RT Σ)      (* [comment removed for export] *).
Proof.
  intros until slack. intros HEAP ST CEIL LO SPT SP16 MI TP FLEN CRED HBIN HO NW0 HS NONUL PAD SLO SHI ACCS LEN -> ->.
  unfold BIO_PUTS_NULL_STACK, BPUTS_FRAME, RT_STACK, BIO_PUTS, BIO_SIZE, MallocRep.wz in *.
  set (n := Z.of_nat (length str)) in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (CL1 & CL2 & CL3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CL1, CL2, CL3. unfold USTACK_TOP in SPT. unfold SEGTOP_A in SHI.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (HBIN' : In (pb, out, 128) (OW ++ LB)) by (apply in_or_app; left; exact HBIN).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HBIN') as (BB0 & _ & _ & BB3 & BB4). cbn [blk_addr blk_size fst snd] in BB0, BB3, BB4.
  pose proof (proj1 (AH_okA _ _ _ _ _ _ _ HEAP HBIN)) as ALB.
  unfold bio_null_cells, bio_cells, MallocRep.wz in HO.
  (* [comment removed for export] *)
  eapply (bputs_pro_cps _) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP | exact ST | exact CEIL | unfold BPUTS_FRAME, RT_STACK; clear - LO; lia | unfold USTACK_TOP; clear - SPT; lia | exact SP16
    | exact MI | exact TP | exact FLEN | exact CRED |].
  intros Σ1 m3 f spa g jk gj ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' j0 j8 jf24 jf40
         HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AGF FRL FRH FRF FRS SPA32 SPAL SPAH GSZ SAVJ.
  unfold BPUTS_BODY, MallocRep.wz.
  (* [comment removed for export] *)
  pose proof (@AH_ceil (push AR f 0) _ _ _ _ HEAP3) as (D1 & D2 & D3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in D1, D2, D3. cbn [ar_SP0 push amb] in D1, D2, D3.
  destruct GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 0) with 64 in G3, G5. unfold SEGTOP_A in G4.
  assert (Ef : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; clear - G1 G3 D3; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; lia).
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - SPAL SPAH SPR LO LO0; lia).
  pose proof (FRESH _ HBIN') as OFFB. unfold off_fr in OFFB. cbn [blk_addr blk_size fst snd] in OFFB. change (fs_size 0) with 64 in OFFB.
  apply (rw_cells_agree _ _ _ _ _ AGF) in HO; [| intros a Ha; cbn in Ha; right; right; exists (pb, out, 128); split; [exact HBIN'| cbn; clear - Ha; lia]].
  assert (HS3 : bytes_at ctasegs m3 S (str ++ Z_to_bv 8 0 :: slack)).
  { apply (ro_bytes_at ctasegs m3 S _ MI3); [clear - SLO; lia| rewrite length_app; cbn [length]; clear - SHI; lia| exact HS]. }
  pose proof (ACCS (push AR f 0) Σ1 m3 HEAP3) as ACCS3.
  ablock HEAP3 HBIN' ACCO OFFO.
  destruct (null_meth_wr_img _ _ _ _ _ HEAP3) as [_ ACCM]. pose proof (null_meth_puts_img _ _ _ _ _ HEAP3) as HM.
  change (NULL_METHOD + 48) with 5561040 in HM. unfold NULL_METHOD, NULL_PUTS in HM, ACCM. unfold NULL_METHOD in HO.
  pose proof (munch_refl [(spa - 16, spa); (f + 32, f + 40); (out, out + 128)]%Z m3) as MU3. pose proof (wmono_refl ctasegs m3) as WM3.
  assert (OFF3 : offshW [(spa - 16, spa); (f + 32, f + 40); (out, out + 128)]%Z).
  { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. cbn [ar_SP0 push amb] in *. clear - D1 D2 D3 CEIL LO SPAL SPAH OFFO G5 SPT. lia. }
  apply cps_from_evt'.
  (* [comment removed for export] *)
  step. if_cases Hqb; zify_cond Hqb; [exfalso; rewrite ?unsigned_lit in Hqb by (clear - BB0 BB3 D3; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; lia); clear - Hqb BB0; lia|]. clear Hqb.
  step. step. if_cases Hqm; zify_cond Hqm; [exfalso; revert Hqm; vm_compute; congruence|]. clear Hqm.
  step. step. if_cases Hqp; zify_cond Hqp; [exfalso; revert Hqp; vm_compute; congruence|]. clear Hqp.
  (* [comment removed for export] *)
  step. step. if_cases Hqcb; zify_cond Hqcb; [exfalso; apply Hqcb; reflexivity|]. clear Hqcb.
  step. step. if_cases Hqcx; zify_cond Hqcx; [| exfalso; apply Hqcx; reflexivity]. clear Hqcx.
  (* [comment removed for export] *)
  step. step. if_cases Hqin; zify_cond Hqin; [exfalso; revert Hqin; vm_compute; congruence|]. clear Hqin.
  step. step. step. step. step. step.
  (* [comment removed for export] *)
  carve_frame 16%nat ST3. do 4 step.
  step. if_cases Hqs; zify_cond Hqs; [exfalso; rewrite ?unsigned_lit in Hqs by (clear - SLO SHI; lia); clear - Hqs SLO; lia|]. clear Hqs.
  step. step.
  name_mem m4.
  match goal with H : munch _ m3 m4 |- _ => rename H into MU4 end. match goal with H : wmono ctasegs m3 m4 |- _ => rename H into WM4 end.
  assert (ESP4 : bv_unsigned (Z_to_bv 64 (spa - 16)) = spa - 16) by (apply unsigned_lit; clear - SPAL SPAH SPR LO LO0; lia).
  assert (FRW : Forall (@fr_write_ok (push AR f 0) (OW ++ LB) f 0) [(spa - 16, spa); (f + 32, f + 40); (out, out + 128)]%Z).
  { clear - CEIL LO SPAL SPAH SPT HBIN'. change (fs_size 0) with 64.
    constructor; [left; left; cbn [fst snd]; unfold BnHeapA.ACEIL, USTACK_TOP, STACK_WIN in *; cbn [ar_SP0 push amb] in *; lia|].
    constructor; [right; left; cbn [fst snd]; change (fs_size 0) with 64; lia|].
    constructor; [left; right; right; exists (pb, out, 128); split; [exact HBIN'| cbn; lia]| constructor]. }
  assert (HEAP4 : @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB m4).
  { eapply (@AH_frame_fr (push AR f 0) Σ1 OW LB m3 m4 _ f 0%nat (or_introl eq_refl) HEAP3 MU4 WM4 FRW). intros b Hb; apply FRESH; apply in_or_app; right; exact Hb. }
  apply evt_done. eapply cps_step_same.
  { eapply (strlen_img_cpsA (push AR f 0)) with (s := S) (str := str) (slack := slack) (lo := lo) (OW := OW) (LB := LB); try reflexivity.
    - exact HEAP4.
    - rewrite ESP4. exact ST3.
    - unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEIL.
    - rewrite ESP4. unfold RT_STACK. clear - LO SPAL. lia.
    - rewrite ESP4. unfold USTACK_TOP. clear - SPT SPAH. lia.
    - rewrite ESP4. clear - SPA32. Z.div_mod_to_equations. lia.
    - assumption.
    - exact SLO.
    - unfold SEGTOP_A. exact SHI.
    - exact (ACCS (push AR f 0) Σ1 m4 HEAP4).
    - first [exact HS3 | eapply bytes_at_agree; [apply (agree_on_of_munch_nw _ _ _ MU4)| exact HS3|];
        intros a Ha; rewrite length_app in Ha; cbn [length] in Ha; cbn [outside fst snd]; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; clear - Ha SHI D1 CEIL LO SPAL; lia].
    - exact NONUL.
    - clear - LEN. lia.
    - exact PAD. }
  intros msL PO. unfold icall_post in PO. rewrite ?ESP4 in PO.
  destruct PO as (v0 & v1 & v2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & v3 & v4 & v5 & v6 & F5 & fc5 & m5 & -> & MI5 & ST5 & HEAP5 & WM5 & AG5 & AGFR).
  unfold NULL_PUTS_SL_RA, MallocRep.wz. rewrite (ret_pc_even 0x323450) by (clear; lia). fold n.
  apply (rw_cells_agree _ _ _ _ _ AGFR) in FRF; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; exists f, 0%nat; split; [left; reflexivity| change (fs_size 0) with 64; clear - Ha; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG5) in FR; [| intros a Ha; cbn in Ha; split; [left; unfold USTACK_TOP; clear - Ha SPT SPAH; lia| clear; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG5) in HO; [| intros a Ha; cbn in Ha; split; [right; right; exists (pb, out, 128); split; [exact HBIN'| cbn; clear - Ha; lia]| clear; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG5) in FRL; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; unfold USTACK_TOP; clear - Ha SPT SPAH GSZ; lia| clear; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG5) in FRH; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; unfold USTACK_TOP; clear - Ha SPT SPAH; lia| clear; lia]].
  destruct (null_meth_wr_img _ _ _ _ _ HEAP5) as [_ ACCM5]. unfold NULL_METHOD in ACCM5.
  pose proof (@AH_acc (push AR f 0) _ _ _ _ _ HEAP5 HBIN') as [_ ACCO5]. cbn [blk_addr blk_size fst snd] in ACCO5.
  pose proof (munch_refl [(spa - 16, spa); (f + 32, f + 40); (out, out + 128)]%Z m5) as MU5. pose proof (wmono_refl ctasegs m5) as WM5'.
  clear ACCM ACCO ACCS3.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  step. step. step. step. rewrite (puts_clamp_small n) by (clear - LEN; lia).
  step. step. replace (bv_swrap 32 (bv_unsigned (Z_to_bv 64 n) + 0)) with n by (rewrite unsigned_lit, Z.add_0_r, bk_swrap32_small; clear - LEN; lia).
  do 3 step. release_frame FR ST5 spa. step.
  (* [comment removed for export] *)
  step. step. if_cases Hqr; zify_cond Hqr; [exfalso; rewrite (proj2 (Z.ltb_lt _ _)) in Hqr by lia; rewrite (proj2 (Z.ltb_lt _ _)) in Hqr by lia; discriminate| try clear Hqr].
  step. step. step. step. step.
  (* [comment removed for export] *)
  step. step. first [if_false | if_cases Hqc2; zify_cond Hqc2; [exfalso; apply Hqc2; reflexivity|]; clear Hqc2].
  step. step. first [if_true | if_cases Hqc3; zify_cond Hqc3; [| exfalso; apply Hqc3; reflexivity]; clear Hqc3].
  (* [comment removed for export] *)
  step. step. if_false.
  step. step. replace (bv_unsigned (Z_to_bv 64 n) ≫ 31) with 0 by (rewrite unsigned_lit by (clear - LEN; lia); rewrite Z.shiftr_div_pow2, Z.div_small by (clear - LEN; lia); reflexivity).
  step. first [if_true | if_cases Hqov; zify_cond Hqov; [| exfalso; apply Hqov; reflexivity]; clear Hqov].
  name_mem mk.
  match goal with H : munch _ m5 mk |- _ => rename H into MUk end. match goal with H : wmono ctasegs m5 mk |- _ => rename H into WMk end.
  (* [comment removed for export] *)
  assert (HEAPk : @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB mk).
  { eapply (@AH_frame_fr (push AR f 0) Σ1 OW LB m5 mk _ f 0%nat (or_introl eq_refl) HEAP5 MUk WMk FRW). intros b Hb; apply FRESH; apply in_or_app; right; exact Hb. }
  apply (rw_cells_cb_first mk spa _ 2) in FRL. cbn [cb_first csize cbytes] in FRL.
  apply evt_done.
  eapply (bputs_epi_cps _) with (lo := lo) (LB := LB) (gj := gj) (hrest := []);
    [exact HEAPk | intros b Hb; apply FRESH; apply in_or_app; right; exact Hb | exact ST5 | exact CEIL | clear - LO SPAL; lia | unfold USTACK_TOP; clear - SPT; lia
    | exact SPAL | exact SPAH | exact GSZ | exact SAVJ | assumption | exact FRL | exact FRH | reflexivity |].
  intros Σ' m' HEAP' CR' EL' ST' MI' AG'.
  rewrite (v_addiw0_small n) by (clear - LEN; lia).
  apply (rw_cells_agree _ _ _ _ _ AG') in HO; [| intros a Ha; cbn in Ha; right; right; exists (pb, out, 128); split; [exact HBIN'| cbn; clear - Ha; lia]].
  apply cps_post. intros c Hc. exists Σ'. split; [| rewrite EL', EL1; reflexivity].
  eapply ASTA_conseq; [exact Hc|]. intros ms0 <-. unfold bio_puts_null_post, MallocRep.wz.
  do 16 eexists. exists m'. split; [reflexivity|].
  split; [exact MI'|]. split; [exact ST'|].
  split.
  { unfold apres_ex.
    assert (INC : forall b : block, In b (OW ++ LB) -> In b (OW ++ LB)) by (intros b Hb; exact Hb).
    eapply agree_on_trans; [eapply agree_on_mono; [exact AGF|]; intros a [Ha _]; exact Ha|].
    assert (BODY : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ outside [(out, out + 128)]%Z a ->
                   outside [(spa - 16, spa); (f + 32, f + 40); (out, out + 128)]%Z a).
    { intros a [Ha Hx]. cbn [outside fst snd] in Hx |- *. destruct Hx as [Hx _].
      assert (A2 : ~ (spa - 16 <= a < spa)).
      { intros Hr. apply (acl_off_frame _ _ _ _ _ (bv_unsigned sp) lo (144 + 16 + 65536) a HEAP INC CEIL ltac:(clear - LO; lia) Ha). clear - Hr SPAL SPAH. lia. }
      assert (A3 : ~ (f + 32 <= a < f + 40)).
      { intros Hr. destruct Ha as [Ha|[Ha|(b & Hb & Hrb)]].
        - unfold BnHeapA.ACEIL, USTACK_TOP in *. clear - Hr Ha G3 CEIL LO. cbn [ar_SP0 push amb] in *. lia.
        - destruct Ha as [(l & h & Hin & Hlh) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. clear - Hin Hlh Hr G4. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
        - pose proof (FRESH b Hb) as O. unfold off_fr in O. change (fs_size 0) with 64 in O. clear - O Hrb Hr. lia. }
      clear - A2 A3 Hx. repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
    eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU4)| exact BODY]|].
    eapply agree_on_trans; [eapply agree_on_mono; [exact AG5|]; intros a [Ha _]; split; [eapply acl_sub; [exact INC| | exact Ha]; clear - SPAH; lia| clear; lia]|].
    eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MUk)| exact BODY]|].
    eapply agree_on_mono; [exact AG'|]. intros a [Ha _]. eapply acl_sub; [exact INC| | exact Ha]. clear - SPAH; lia. }
  split; [exact HEAP'|].
  split; [rewrite EL', EL1; reflexivity|]. split; [rewrite CR', CR1; clear; lia|].
  unfold bio_null_cells, bio_cells, MallocRep.wz. exact HO.
Qed.
End WithRT.
