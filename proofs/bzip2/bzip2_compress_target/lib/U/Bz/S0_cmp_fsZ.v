(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCState BzCSortF BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCut0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasFs BzCFactsFs BzCFactsFs2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpFsKit0 DecTac2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import UKit U0_cmp_fsL.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_cmp_fsJ.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_cmp_fsD S0_cmp_fsF S0_cmp_fsJ S0_cmp_fsK.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_fsJ.S0_cmp_fsA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_fsD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_fsF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_fsJ OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_fsK.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Strategy 1000 [fs_ftab_zero fs_count fs_copy fs_accum fs_distrib fs_bh_zero fs_bh_init fs_sentinel fs_eclass fs_H_loop fs_H_iter
               fs_bucket_loop fs_bucket_iter fs_headers fs_skip0 fs_rebuild fqs_loop fallbackQSort3 fallbackSort
               fs_scan_set_unal fs_scan_word_ff fs_scan_set fs_scan_clr_unal fs_scan_word_00 fs_scan_clr].
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require KeepVars. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas8_all.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma u32arr_u8arr : forall segs m A ws, u32arr segs m A ws <-> u8arr segs m A (u32s ws).
Proof. intros. unfold u32arr, u8arr. rewrite u32s_length, Nat2Z.inj_mul. change (Z.of_nat 4) with 4%Z. tauto. Qed.

Lemma repeat_zero_nth : forall n k (b : byte), nth_error (repeat (Z_to_bv 8 0) n) k = Some b -> b = Z_to_bv 8 0.
Proof. intros n k b H. apply nth_error_In in H. apply repeat_spec in H. subst; reflexivity. Qed.

Lemma mod16_linq : forall x, (x mod 16 = 0)%Z -> exists q, (x = 16 * q)%Z.
Proof. intros x H. exists (x / 16)%Z. Z.div_mod_to_equations. lia. Qed.
End ACeilS1.


(* [comment removed for export] *)
Ltac u8take FRu H n newbase :=
  lazymatch type of FRu with u8arr ?segs ?m ?A ?bs =>
    rewrite <- (firstn_skipn (Z.to_nat n) bs) in FRu;
    apply (proj1 (u8arr_app segs m A _ _)) in FRu;
    let H' := fresh in destruct FRu as [H' FRu]; rename H' into H;
    lazymatch type of FRu with u8arr _ _ ?A' _ => replace A' with newbase in FRu by (rewrite ?length_firstn, ?length_skipn; first [ KeepVars.keep_vars1 bs; lia | lia ]) end
  end.
(* [comment removed for export] *)
Ltac name_bytes H j n :=
  lazymatch type of H with u8arr _ _ _ ?bs =>
    let L := fresh "L" j in
    set (j := bs) in H; assert (L : Z.of_nat (length j) = n) by (subst j; rewrite ?length_firstn, ?length_skipn; first [ KeepVars.keep_vars1 bs; lia | lia ]); clearbody j
  end.
Section ACeilS2. Context {BZP : BzParams} {ACEIL__ : ACeil} {RUNW__ : RunW}.


Lemma stk_of_u8arr : forall segs m A bs, u8arr segs m A bs -> stk segs m A (A + Z.of_nat (length bs)).
Proof.
  intros segs m A bs H. pose proof (stk_of_rw_cells segs m A _ (rw_cells_of_u8arr segs m A bs H)) as S.
  cbn [cells_size csize] in S. rewrite Nat.add_0_r in S. exact S.
Qed.
Lemma stk_of_u32arr : forall segs m A ws, u32arr segs m A ws -> stk segs m A (A + 4 * Z.of_nat (length ws)).
Proof.
  intros segs m A ws H. apply (proj1 (u32arr_u8arr segs m A ws)) in H. pose proof (stk_of_u8arr segs m A _ H) as S.
  rewrite u32s_length, Nat2Z.inj_mul in S. exact S.
Qed.
Lemma stk_join : forall segs m a b b' c, stk segs m a b -> stk segs m b' c -> b = b' -> (a <= b <= c)%Z -> stk segs m a c.
Proof. intros segs m a b b' c H1 H2 -> Hle. eapply stk_merge; [exact H1| exact H2| exact Hle]. Qed.
Lemma fp_hs_0 : forall fm ec bh nb, fp_hs fm ec bh nb 0 = fp_hs0 fm ec bh nb.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rw_cells_junk16_C8 : forall segs m A (j : list byte), rw_cells segs m A [CB 16 j] ->
  exists nd rr : Z, rw_cells segs m A [C8 (Z_to_bv 64 nd); C8 (Z_to_bv 64 rr)].
Proof.
  intros segs m A j H.
  pose proof (proj1 (proj1 H)) as W. cbn in W. destruct W as [L _].
  exists (bv_unsigned (le_bytes_to_word (firstn 8 j))), (bv_unsigned (le_bytes_to_word (skipn 8 j))).
  rewrite !Z_to_bv_bv_unsigned.
  destruct H as [[Hwf Hb] Hw]. split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes] in *. rewrite app_nil_r in Hb. rewrite !le8_of_bytes by (rewrite ?length_firstn, ?length_skipn; lia).
    rewrite app_nil_r, firstn_skipn. exact Hb.
  - cbn [cells_size csize Nat.add] in *. exact Hw.
Qed.
Lemma rw_cells_junk32_C8 : forall segs m A (j : list byte), rw_cells segs m A [CB 32 j] ->
  exists a b c d : Z, rw_cells segs m A [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 c); C8 (Z_to_bv 64 d)].
Proof.
  intros segs m A j H.
  pose proof (proj1 (proj1 H)) as W. cbn in W. destruct W as [L _].
  exists (bv_unsigned (le_bytes_to_word (firstn 8 j))), (bv_unsigned (le_bytes_to_word (firstn 8 (skipn 8 j)))),
    (bv_unsigned (le_bytes_to_word (firstn 8 (skipn 8 (skipn 8 j))))), (bv_unsigned (le_bytes_to_word (skipn 8 (skipn 8 (skipn 8 j))))).
  rewrite !Z_to_bv_bv_unsigned.
  destruct H as [[Hwf Hb] Hw]. split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes] in *. rewrite app_nil_r in Hb. rewrite !le8_of_bytes by (rewrite ?length_firstn, ?length_skipn; lia).
    rewrite app_nil_r, !firstn_skipn. exact Hb.
  - cbn [cells_size csize Nat.add] in *. exact Hw.
Qed.
End ACeilS2.


(* [comment removed for export] *)
Ltac stk_add ST K :=
  lazymatch type of K with stk _ _ ?b' ?c =>
  lazymatch type of ST with stk ?segs ?m ?lo ?b =>
    let H := fresh in pose proof (stk_join segs m lo b b' c ST K ltac:(lia) ltac:(lia)) as H; clear ST K; rename H into ST end end.

(* [comment removed for export] *)
Ltac lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
  | _ => idtac
  end.
Ltac ulrun_to p :=
  first [ u_at_pc p
        | u_pc_is_lit; ustep; lit_store; ulrun_to p
        | fail 1 "ulrun_to: stopped before" p ].
Section ACeilS3. Context {BZP : BzParams} {ACEIL__ : ACeil} {RUNW__ : RunW}.


Section S0FS.
  Theorem S0_fallbackSort : fallbackSort_spec fs_facts S0C.
  Proof.
    unfold fallbackSort_spec. cbn [ci_segs ci_fallbackSort S0C]. intros until sv.
    intros Ha0 Ha1 Ha2 Ha3 Ha4 AR1 AR2 FTB CM MI ST STK LO AL CX SEP IMG FMOK ECOK FTW NB FACTS. subst a0 a1 a2 a3 a4.
    pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'.
    cps_destruct CX' as (_ & _ & RA1 & RA1' & RA2 & RA2' & RFT & RFT' & _ & _ & _ & _ & _ & MA1 & MA2 & MFT & _).
    pose proof SEP as SEP'. unfold cctx_sep, apart in SEP'. cbv zeta in SEP'.
    cps_destruct SEP' as (_ & _ & _ & _ & _ & AP12 & AP1F & _ & _ & AP2F & _).
    pose proof IMG as IMG'. unfold cctx_img, img_apart, IMG_LO3, IMG_HI3 in IMG'. cbn [ci_hi S0C] in IMG'. cps_destruct IMG' as (_ & IA1 & IA2 & IFT & _).
    bz_ceil; bz_params; unfold FTAB_WORDS, FS_FRAME, CEIL in *.
    destruct IA1 as [IA1|IA1]; [exfalso; lia|]. destruct IA2 as [IA2|IA2]; [exfalso; lia|]. destruct IFT as [IFT|IFT]; [exfalso; lia|].
    destruct (mod16_linq _ AL) as [qsp ALQ]. destruct (mod16_linq _ MA1) as [q1 AQ1]. destruct (mod16_linq _ MA2) as [q2 AQ2]. destruct (mod16_linq _ MFT) as [qF AQF].
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    set (X := FE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (c_A1 cx) (c_A2 cx) (c_FT cx) nblock lo q1 q2 qF qsp
                 (e_arr1 e) (e_arr2 e) (e_ftab e) sv m).
    assert (BW0 : bh_w32 (e_ftab e)) by (intros i; apply FTW).
    assert (XOK : fsenv_ok X).
    { bz_ceil; bz_params; unfold fsenv_ok, CEILv. cbn [fe_A1 fe_A2 fe_FT fe_lo fe_sp fe_nb fe_q1 fe_q2 fe_qF fe_qsp fe_fm fe_ec fe_bh X].
      repeat (split; [first [lia| assumption]|]). exact BW0. }
    assert (XSEP : fsenv_sep X) by (unfold fsenv_sep, apartv; cbn [fe_A1 fe_A2 fe_FT X]; split; [lia| split; lia]).
    cps_destruct FACTS as (FD & FF4 & FFM & FEC & FBK & FRB).
    cps_destruct CM as (CM1 & _ & CM3 & _). cbn [ci_segs ci_got ci_stderrp S0C] in CM1, CM3.
    pose proof (zb8_length (e_arr1 e) ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length (e_arr2 e) ARR2_SIZE ltac:(lia)) as L2.
    pose proof (zw32_length (e_ftab e) 65537 ltac:(lia)) as LB.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    pose proof (munch_refl (fallbackSort_W cx (bv_unsigned sp)) m) as MU. unfold fallbackSort_W, FTAB_WORDS, FS_FRAME in MU.
    pose proof (wmono_refl s0segs m) as WM.
    (* [comment removed for export] *)
    carve_frame 3056%nat ST.
    pose proof (u8arr_of_rw_cells s0segs _ _ _ _ FR) as FRu.
    assert (LJ : Z.of_nat (length junk) = 3056%Z) by (pose proof (proj1 (proj1 (proj1 FR))) as W; cbn in W; lia).
    clear FR.
    u8take FRu P0 8%Z (bv_unsigned sp + -3048)%Z. u8take FRu SCu 88%Z (bv_unsigned sp + -2960)%Z. u8take FRu G4 4%Z (bv_unsigned sp + -2956)%Z.
    u8take FRu FCu 1024%Z (bv_unsigned sp + -1932)%Z. u8take FRu FTu 1028%Z (bv_unsigned sp + -904)%Z. u8take FRu SHu 400%Z (bv_unsigned sp + -504)%Z.
    u8take FRu SLu 400%Z (bv_unsigned sp + -104)%Z. rename FRu into SAVu.
    name_bytes P0 j0 8%Z. name_bytes SCu jsc 88%Z. name_bytes G4 jg4 4%Z. name_bytes FCu jfc 1024%Z. name_bytes FTu jft 1028%Z.
    name_bytes SHu jhi 400%Z. name_bytes SLu jlo 400%Z. name_bytes SAVu jsav 104%Z. clear LJ junk.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ SAVu) as SAV. clear SAVu.
    replace (length jsav) with 104%nat in SAV by lia.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ FTu) as FTJ. clear FTu. replace (length jft) with (Z.to_nat (4 * 257)) in FTJ by lia.
    pose proof (ovw_init s0segs _ _ 257 _ FTJ ltac:(lia)) as FTL. clear FTJ.
    replace (bv_unsigned sp + -1932)%Z with (bv_unsigned sp - 3056 + 1124)%Z in FTL by lia.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ FCu) as FCJ. clear FCu. replace (length jfc) with (Z.to_nat (4 * 256)) in FCJ by lia.
    pose proof (ovw_init s0segs _ _ 256 _ FCJ ltac:(lia)) as FC0. clear FCJ.
    replace (bv_unsigned sp + -2956)%Z with (bv_unsigned sp - 3056 + 100)%Z in FC0 by lia.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ SHu) as SHJ. clear SHu. replace (length jhi) with (Z.to_nat (4 * 100)) in SHJ by lia.
    pose proof (ovw_init s0segs _ _ 100 _ SHJ ltac:(lia)) as SHI. clear SHJ.
    replace (bv_unsigned sp + -904)%Z with (bv_unsigned sp - 3056 + 2152)%Z in SHI by lia.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ SLu) as SLJ. clear SLu. replace (length jlo) with (Z.to_nat (4 * 100)) in SLJ by lia.
    pose proof (ovw_init s0segs _ _ 100 _ SLJ ltac:(lia)) as SLO. clear SLJ.
    replace (bv_unsigned sp + -504)%Z with (bv_unsigned sp - 3056 + 2552)%Z in SLO by lia.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ SCu) as SC. clear SCu. replace (length jsc) with 88%nat in SC by lia.
    replace (bv_unsigned sp + -3048)%Z with (bv_unsigned sp - 3056 + 8)%Z in SC by lia.
    pose proof (ovw_length znew jft 257 ltac:(lia)) as LF0. pose proof (ovw_length znew jfc 256 ltac:(lia)) as LC0.
    (* [comment removed for export] *)
    urun_to 0x2234c%Z.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (mz := mm) in * end.
    enter_with (U0_fs_zero X _ XOK 257%nat 0 znew jft mz mz); cbn [fe_sp fe_gp fe_tp fe_F fe_fc X];
      [st_eq| lia| lia| lia| exact FTL| assumption| apply munch_refl| apply wmono_refl|].
    intros m1. cbv zeta. intros FTL1 MI1 MU1 WM1.
    clear FTL. transport_after_call s0segs mz m1 MU1 WM1. clear MU1 WM1.
    assert (FTL : u32arr s0segs m1 (bv_unsigned sp - 3056 + 1124) (zw32 fp_ft1 257)).
    { unfold fp_ft1. rewrite <- (ovw_defined_zw32 (fs_ftab_zero 257 znew 0) jft 257); [exact FTL1|].
      intros i Hi. rewrite fs_ftab_zero_def. replace ((0 <=? i) && (i <? 0 + Z.of_nat 257))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia). reflexivity. }
    clear FTL1.
    (* [comment removed for export] *)
    wstep; if_cases Knb; zify_cond_z Knb; [exfalso; lia|].
    urun_to 0x22370%Z.
    enter_with (S0_fs_count X _ XOK (Z.to_nat nblock) 0 fp_ft1 m1 m1); cbn [fe_sp fe_A1 fe_A2 fe_FT fe_nb fe_gp fe_tp fe_F fe_fc fe_ec fe_fm X];
      [st_eq| lia| lia| lia| | exact AR2| exact FTL| assumption| apply munch_refl| apply wmono_refl|].
    { intros b. unfold fp_ft1. rewrite fs_ftab_zero_get, zget_znew. destruct (_ && _); lia. }
    intros m2 y12 y13 y14 y15 y16 y17. cbv zeta. intros AR2_2 FTL2 MI2 MU2 WM2 FT2B. bz_params.
    clear AR2 FTL. transport_after_call s0segs m1 m2 MU2 WM2. clear MU2 WM2.
    change (fs_count (Z.to_nat nblock) fp_ft1 (e_arr2 e) 0) with (fp_ft2 (e_arr2 e) nblock) in FTL2, FT2B.
    set (ft2 := fp_ft2 (e_arr2 e) nblock) in *.
    pose proof (zw32_length ft2 257 ltac:(lia)) as LF2.
    (* [comment removed for export] *)
    urun_to 0x223cc%Z.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    enter_with (U0_fs_copy X _ XOK 256%nat 0 ft2 znew jfc m2 m2); cbn [fe_sp fe_nb fe_gp fe_tp fe_F fe_fc X];
      [st_eq| lia| lia| lia| exact FT2B| exact FC0| exact FTL2| assumption| apply munch_refl| apply wmono_refl|].
    intros m3 z13. cbv zeta. intros FC3 FTL3 MI3 MU3 WM3.
    clear FC0 FTL2. transport_after_call s0segs m2 m3 MU3 WM3. clear MU3 WM3.
    set (fc0 := fp_fc0 (e_arr2 e) nblock) in *.
    assert (FCB : u32arr s0segs m3 (bv_unsigned sp - 3056 + 100) (zw32 fc0 256)).
    { unfold fc0, fp_fc0. fold ft2. rewrite <- (ovw_defined_zw32 (fs_copy 256 znew ft2 0) jfc 256); [exact FC3|].
      intros i Hi. rewrite fs_copy_def. replace ((0 <=? i) && (i <? 0 + Z.of_nat 256))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia). reflexivity. }
    clear FC3.
    (* [comment removed for export] *)
    urun_to 0x223e8%Z.
    enter_with (S0_fs_accum X _ XOK 256%nat 1 ft2 m3 m3); cbn [fe_sp fe_A1 fe_A2 fe_FT fe_nb fe_gp fe_tp fe_F fe_fc fe_ec fe_fm X];
      [st_eq| lia| lia| lia| intros b Hb; apply FT2B| pose proof (FT2B (1 - 1)%Z); lia| exact FTL3| assumption| apply munch_refl| apply wmono_refl| | intros b Hb; pose proof (FT2B b); lia].
    intros m4 w10 w11 w12 w13 w14. cbv zeta. intros FTL4 MI4 MU4 WM4 FT3B.
    clear FTL3. transport_after_call s0segs m3 m4 MU4 WM4. clear MU4 WM4.
    change (fs_accum 256 ft2 1) with (fp_ft3 (e_arr2 e) nblock) in FTL4, FT3B.
    set (ft3 := fp_ft3 (e_arr2 e) nblock) in *.
    (* [comment removed for export] *)
    wstep; if_cases Knb'; zify_cond_z Knb'; [exfalso; lia|].
    urun_to 0x22434%Z.
    enter_with (S0_fs_distrib X _ XOK XSEP (Z.to_nat nblock) 0 ft3 (e_arr1 e) m4 m4); cbn [fe_sp fe_A1 fe_A2 fe_FT fe_nb fe_gp fe_tp fe_F fe_fc fe_ec fe_fm X];
      [st_eq| lia| lia| lia| exact FD| reflexivity| exact AR1| exact AR2_2| exact FTL4| assumption| apply munch_refl| apply wmono_refl|].
    intros m5 q5 q6 q7 q10 q15 q16 q17 q28. cbv zeta. intros AR1_5 AR2_5 FTL5 MI5 MU5 WM5. bz_params.
    clear AR1 AR2_2 FTL4. transport_after_call s0segs m4 m5 MU5 WM5. clear MU5 WM5.
    assert (Edist : fs_distrib (Z.to_nat nblock) ft3 (e_arr1 e) (e_arr2 e) 0 = fp_dist (e_arr1 e) (e_arr2 e) nblock (Z.to_nat nblock)) by reflexivity.
    rewrite Edist in AR1_5, FTL5. clear Edist.
    change (snd (fp_dist (e_arr1 e) (e_arr2 e) nblock (Z.to_nat nblock))) with (fp_fm1 (e_arr1 e) (e_arr2 e) nblock) in AR1_5.
    change (fst (fp_dist (e_arr1 e) (e_arr2 e) nblock (Z.to_nat nblock))) with (fp_ft4 (e_arr1 e) (e_arr2 e) nblock) in FTL5.
    set (fm1 := fp_fm1 (e_arr1 e) (e_arr2 e) nblock) in *. set (ft4 := fp_ft4 (e_arr1 e) (e_arr2 e) nblock) in *.
    (* [comment removed for export] *)
    wstep. wstep; if_cases K63; zify_cond_z K63; [exfalso; lia|].
    urun_to 0x22510%Z.
    rewrite ?(Z.div_small (nblock * 2) 576460752303423488) by lia. rewrite ?Z.add_0_r.
    set (nB := (2 + nblock / 32)%Z).
    assert (HnB : (2 <= nB <= 28127)%Z) by (subst nB; pose proof (Z.div_pos nblock 32 ltac:(lia) ltac:(lia)); pose proof (Z.div_le_upper_bound nblock 32 28125 ltac:(lia) ltac:(lia)); lia).
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    enter_with (U0_fs_bhzero X _ XOK (Z.to_nat nB) 0 (e_ftab e) m5 m5); cbn [fe_sp fe_FT fe_nb fe_gp fe_tp fe_F fe_fc X];
      [st_eq| lia| lia| lia| exact FTB| assumption| apply munch_refl| apply wmono_refl|].
    intros m6 u15. cbv zeta. intros FTB6 MI6 MU6 WM6.
    clear FTB. transport_after_call s0segs m5 m6 MU6 WM6. clear MU6 WM6.
    set (bhz := fs_bh_zero (Z.to_nat nB) (e_ftab e) 0) in *.
    assert (BWz : bh_w32 bhz) by (subst bhz; apply fs_bh_zero_w32; exact BW0).
    (* [comment removed for export] *)
    urun_to 0x22554%Z.
    enter_with (S0_fs_bhinit X _ XOK 256%nat 0 ft4 bhz m6 m6); cbn [fe_sp fe_A1 fe_A2 fe_FT fe_nb fe_gp fe_tp fe_F fe_fc fe_ec fe_fm X];
      [st_eq| lia| lia| lia| exact FF4| exact BWz| exact FTL5| exact FTB6| assumption| apply munch_refl| apply wmono_refl|].
    intros m7 w10' w11' w14' w15' w16' w17'. cbv zeta. intros FTL7 FTB7 MI7 MU7 WM7 BW7.
    clear FTL5 FTB6. transport_after_call s0segs m6 m7 MU7 WM7. clear MU7 WM7.
    set (bhi := fs_bh_init 256 bhz ft4 0) in *.
    (* [comment removed for export] *)
    urun_to 0x225c4%Z.
    enter_with (S0_fs_sentinel X _ XOK 32%nat 0 bhi m7 m7); cbn [fe_sp fe_A1 fe_A2 fe_FT fe_nb fe_gp fe_tp fe_F fe_fc fe_ec fe_fm X];
      [st_eq| lia| lia| lia| exact BW7| exact FTB7| assumption| apply munch_refl| apply wmono_refl|].
    intros m8 v10 v13 v14 v15 v16. cbv zeta. intros FTB8 MI8 MU8 WM8 BW8.
    clear FTB7. transport_after_call s0segs m7 m8 MU8 WM8. clear MU8 WM8.
    set (bh3 := fs_sentinel 32 bhi nblock 0) in *.
    (* [comment removed for export] *)
    ulrun_to 0x226c8%Z.
    (* [comment removed for export] *)
    match goal with H : rw_cells _ _ (bv_unsigned sp - 3056 + 8)%Z _ |- _ => rename H into SC end.
    lazymatch type of SC with rw_cells _ ?mm ?A [?c1; ?c2; ?c3; ?c4; CB 32 ?j; ?c9; ?c10; ?c11] =>
      apply (proj1 (rw_cells_app_iff s0segs mm A [c1; c2; c3; c4] [CB 32 j; c9; c10; c11])) in SC end.
    destruct SC as [SC4 SCr].
    (* [comment removed for export] *)
    lazymatch type of SCr with rw_cells _ ?mm ?A [CB 32 ?j; ?c9; ?c10; ?c11] =>
      apply (proj1 (rw_cells_app_iff s0segs mm A [CB 32 j] [c9; c10; c11])) in SCr end.
    destruct SCr as [SCJ SC3].
    (* [comment removed for export] *)
    cps_destruct (rw_cells_junk32_C8 s0segs _ _ _ SCJ) as (nd & hc & rr & tv & SCJ').
    (* [comment removed for export] *)
    pose proof (proj2 (rw_cells_app_iff s0segs _ _ _ _) (conj SCJ' SC3)) as SCr.
    pose proof (proj2 (rw_cells_app_iff s0segs _ _ _ _) (conj SC4 SCr)) as SC. cbn [app] in SC. clear SC4 SCJ SCJ' SC3 SCr.
    (* [comment removed for export] *)
    set (HF := fp_hsF (e_arr1 e) (e_arr2 e) (e_ftab e) nblock).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m8b end.
    (* [comment removed for export] *)
    enter_with (S0_hloop X _ (Z_to_bv 64 67194) sv jlo jhi (e_arr1 e) (e_arr2 e) (e_ftab e) XOK XSEP Ljlo Ljhi FEC FBK
                  (Z.to_nat 64) 0%nat HF hc nd rr tv m8b m8b);
      rewrite ?fp_hs_0; cbn [fh_fm fh_ec fh_bh fh_H fh_slo fh_shi fh_done fp_hs0 fe_sp fe_A1 fe_A2 fe_FT fe_nb fe_gp fe_tp fe_F fe_fc X];
      [st_eq| reflexivity| subst HF; unfold fp_hsF; reflexivity| subst HF; unfold fp_hsF; apply fs_H_loop_64_done; lia| | | apply munch_refl| apply wmono_refl|].
    { unfold hinv. cbn [fe_nb X]. split; [split; [lia| exact FFM]|]. split; [apply fp_fm1_zbok; exact FMOK|]. split; [exact ECOK|]. split; [exact BW8| lia]. }
    { unfold hmem, SCq. cbn [fe_A1 fe_A2 fe_FT fe_sp X].
      split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact SC|]. split; [assumption|]. split; assumption. }
    intros mH hc9 nd9 rr9 tv9 o1 o5 o7 o10 o11 o12 o13 o14 o15 o16 o17 o21 o24 o28 o29 o30 o31 HM9 MU9 WM9 FMR9 FMOK9 ECOK9 BW9.
    cps_destruct HM9 as (AR1_9 & AR2_9 & FTB9 & SC9 & SHI9 & SLO9 & MI9). bz_params. unfold SCq in SC9.
    cbn [fe_sp fe_A1 fe_A2 fe_FT fe_nb X] in AR1_9, AR2_9, FTB9, SC9, SHI9, SLO9, MU9, FMR9.
    clear SC. transport_after_call s0segs m8b mH MU9 WM9. clear MU9 WM9.
    (* [comment removed for export] *)
    urun_to 0x234c8%Z. wstep; if_cases Knb2; zify_cond_z Knb2; [exfalso; lia|].
    urun_to 0x234e8%Z.
    enter_with (S0_rebuild X _ _ _ _ _ _ _ _ _ _ _ _ (fh_fm HF) XOK XSEP FMR9 FMOK9 (Z.to_nat nblock) 0 0 (fh_ec HF) fc0 mH mH);
      cbn [fe_sp fe_A1 fe_A2 fe_FT fe_nb fe_gp fe_tp fe_F fe_fc X];
      [st_eq| lia| lia| lia| lia| exact ECOK9| | exact AR1_9| exact AR2_9| exact FCB| exact MI9| apply munch_refl| apply wmono_refl|].
    { intros k Hk. exact (FRB k ltac:(lia)). }
    intros mR z5 z6 z7 z28. cbv zeta. intros AR1_10 AR2_10 FCB10 MI10 MU10 WM10 ECOK10 Hj10. bz_params.
    cbn [fe_sp fe_A1 fe_A2 fe_FT fe_nb X] in AR1_10, AR2_10, FCB10, MU10.
    clear AR1_9 AR2_9 FCB MI9. transport_after_call s0segs mH mR MU10 WM10. clear MU10 WM10.
    (* [comment removed for export] *)
    replace (bv_unsigned sp + -104)%Z with (bv_unsigned sp - 3056 + 2952)%Z in SAV by lia.
    urun_to 0x235a0%Z.
    (* [comment removed for export] *)
    wstep.
    lazymatch goal with |- evt _ _ (MS (mkR _ ?spv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      replace spv with sp by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; lia) end.
    (* [comment removed for export] *)
    pose proof (stk_of_u8arr s0segs _ _ _ P0) as K0. stk_add ST K0.
    pose proof (stk_of_rw_cells s0segs _ _ _ SC9) as K1. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in K1. stk_add ST K1.
    pose proof (stk_of_u8arr s0segs _ _ _ G4) as K2. stk_add ST K2.
    pose proof (stk_of_u32arr s0segs _ _ _ FCB10) as K3. rewrite zw32_length_nat in K3. stk_add ST K3.
    pose proof (stk_of_u32arr s0segs _ _ _ FTL7) as K4. rewrite zw32_length_nat in K4. stk_add ST K4.
    pose proof (stk_of_u32arr s0segs _ _ _ SHI9) as K5. rewrite ovw_length_nat in K5. stk_add ST K5.
    pose proof (stk_of_u32arr s0segs _ _ _ SLO9) as K6. rewrite ovw_length_nat in K6. stk_add ST K6.
    pose proof (stk_of_rw_cells s0segs _ _ _ SAV) as K7. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in K7. stk_add ST K7.
    lazymatch type of ST with stk _ _ _ ?hi => replace hi with (bv_unsigned sp) in ST by lia end.
    (* [comment removed for export] *)
    apply evt_done. unfold fallbackSort_post. rewrite fallbackSort_eq. cbv zeta. cbn [fr_fm fr_ec fr_bh].
    do 16 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI10|]. split; [exact ST|].
    split; [exact AR1_10|]. split; [exact AR2_10| exact FTB9].
  Qed.
End S0FS.

End ACeilS3.
