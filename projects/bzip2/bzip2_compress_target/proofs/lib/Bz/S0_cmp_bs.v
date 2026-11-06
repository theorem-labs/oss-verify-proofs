(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Musl Require Import MuslStr S0_memset.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTac BzTac2 DecTac2 BzArr BzCMem BzCState BzCSortF BzCSortM BzCBlock BzArrD CmpMem CmpCut CmpCut0 CmpFsKit0 BzCQsortM1 BzCQsortM2 BzCSewA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCSewC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCSewF BzCFactsFs BzCFactsBs BzCPermM BzCFactsBs2 BzCFactsBs3.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmasMs2.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpFsKit0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCQsortM1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCQsortM2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSewA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSewC.BzCSewB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSewF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsFs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsBs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsBs2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsBs3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasMs2.BzCFactsMs3.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasMs BzCLemmasMs2 BzCLemmasMs3 BzCLemmasMs4 CmpCutMS CmpMsKit CmpMsKit2 S0_cmp_msV S0_cmp_msA S0_cmp_msB S0_cmp_msC S0_cmp_msO S0_cmp_fsZ.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasMs6 S0_cmp_bsR S0_cmp_bsS S0_cmp_bsP.
From Stdlib Require Lia. Unset Lia Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParamsLia.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParamsLia.BzParamsX.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas8.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Strategy 1000 [ms_ftab_zero ms_radix1 ms_overshoot ms_accum ms_radix2 ms_ro_init ms_sh_shift ms_sh_pass ms_shell ms_step1 ms_copy_init ms_copy_fwd ms_copy_bwd
               ms_mark ms_shifts ms_quad ms_big ms_bigs mainSort blockSort mainQSort3 mqs_loop mainSimpleSort find_orig fallbackSort].
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Fixpoint c8s_of (k : nat) (j : list byte) : list cell :=
  match k with O => [] | S k' => C8 (le_bytes_to_word (firstn 8 j)) :: c8s_of k' (skipn 8 j) end.
(* [comment removed for export] *)
Lemma c8s_of_size : forall k j, cells_size (c8s_of k j) = (8 * k)%nat.
Proof. induction k; intros; cbn -[Nat.mul]; [reflexivity|]. rewrite IHk. lia. Qed.

Lemma rw_cells_junk_C8s : forall segs k m A (j : list byte),
  rw_cells segs m A [CB (8 * k) j] -> rw_cells segs m A (c8s_of k j).
Proof.
  intros segs k. induction k as [|k IH]; intros m A j H.
  - cbn. destruct H as [[Hwf Hb] Hw]. cbn in *. split; [split|]; cbn; try tauto.
    + destruct Hwf as [L _]. destruct j; [|cbn in L; lia]. cbn in Hb. exact Hb.
  - pose proof (proj1 (proj1 H)) as W. cbn in W. destruct W as [L _].
    assert (H2 : rw_cells segs m A ([CB 8 (firstn 8 j)] ++ [CB (8 * k) (skipn 8 j)])).
    { destruct H as [[Hwf Hb] Hw]. split; [split|].
      - cbn. rewrite length_firstn, length_skipn. repeat split; lia.
      - cbn [cells_bytes cbytes app] in *. rewrite app_nil_r in *. rewrite firstn_skipn. exact Hb.
      - cbn [cells_size csize app] in *. eapply eq_ind; [exact Hw|]. f_equal. lia. }
    apply (proj1 (rw_cells_app_iff segs m A _ _)) in H2. destruct H2 as [H8 Hr].
    cbn [cells_size csize Nat.add] in Hr.
    cbn [c8s_of]. change (C8 (le_bytes_to_word (firstn 8 j)) :: c8s_of k (skipn 8 j)) with ([C8 (le_bytes_to_word (firstn 8 j))] ++ c8s_of k (skipn 8 j)).
    apply (proj2 (rw_cells_app_iff segs m A _ _)). split.
    + destruct H8 as [[Hwf Hb] Hw]. split; [split|].
      * cbn. tauto.
      * cbn [cells_bytes cbytes app] in *. rewrite app_nil_r in *. rewrite le8_of_bytes by (rewrite length_firstn; lia). exact Hb.
      * cbn [cells_size csize Nat.add] in *. exact Hw.
    + cbn [cells_size csize Nat.add]. apply IH. exact Hr.
Qed.

Lemma rw_cells_junk_C4 : forall segs m A (j : list byte), rw_cells segs m A [CB 4 j] -> rw_cells segs m A [C4 (le_bytes_to_word j)].
Proof.
  intros segs m A j H. pose proof (proj1 (proj1 H)) as W. cbn in W. destruct W as [L _].
  destruct H as [[Hwf Hb] Hw]. split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes app] in *. rewrite app_nil_r in *. rewrite le4_le_bytes_to_word by exact L. exact Hb.
  - cbn [cells_size csize Nat.add] in *. exact Hw.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_reC8 : forall segs m A l1 k j l2,
  rw_cells segs m A (l1 ++ CB (8 * k) j :: l2) -> rw_cells segs m A (l1 ++ c8s_of k j ++ l2).
Proof.
  intros segs m A l1 k j l2 H.
  apply (proj1 (rw_cells_app_iff segs m A _ _)) in H. destruct H as [H1 H2].
  change (CB (8 * k) j :: l2) with ([CB (8 * k) j] ++ l2) in H2.
  apply (proj1 (rw_cells_app_iff segs m _ _ _)) in H2. destruct H2 as [H2 H3]. apply rw_cells_junk_C8s in H2.
  apply (proj2 (rw_cells_app_iff segs m A _ _)). split; [exact H1|].
  apply (proj2 (rw_cells_app_iff segs m _ _ _)). split; [exact H2|].
  rewrite c8s_of_size. cbn [cells_size csize Nat.add] in H3. rewrite Nat.add_0_r in H3. exact H3.
Qed.
Lemma rw_cells_reC4 : forall segs m A l1 j,
  rw_cells segs m A (l1 ++ [CB 4 j]) -> rw_cells segs m A (l1 ++ [C4 (le_bytes_to_word j)]).
Proof.
  intros segs m A l1 j H.
  apply (proj1 (rw_cells_app_iff segs m A _ _)) in H. destruct H as [H1 H2]. apply rw_cells_junk_C4 in H2.
  apply (proj2 (rw_cells_app_iff segs m A _ _)). split; [exact H1| exact H2].
Qed.

(* [comment removed for export] *)
Definition zarr_of_junkw (J : list byte) (n : Z) : zarr :=
  zarr_of_list (map (fun k => bv_unsigned (jw J (Z.of_nat k))) (seq 0 (Z.to_nat n))).
Lemma zarr_of_junkw_get : forall J n i, (0 <= i < n)%Z -> zget (zarr_of_junkw J n) i = bv_unsigned (jw J i).
Proof.
  intros J n i Hi. unfold zarr_of_junkw.
  replace i with (Z.of_nat (Z.to_nat i)) at 1 by lia. rewrite zget_of_list by (rewrite length_map, length_seq; lia).
  erewrite nth_error_nth; [reflexivity|]. rewrite nth_error_map, nth_error_seq by lia. cbn [option_map]. f_equal. f_equal. f_equal. lia.
Qed.
Lemma zw32_of_junk : forall segs m A n (J : list byte), rw_cells segs m A [CB (Z.to_nat (4 * n)) J] -> (0 <= n)%Z ->
  u32arr segs m A (zw32 (zarr_of_junkw J n) n).
Proof.
  intros segs m A n J H Hn.
  replace (zw32 (zarr_of_junkw J n) n) with (ovw znew J n); [apply (ovw_init segs _ _ n _ H Hn)|].
  apply nth_error_ext. intros k.
  destruct (Nat.lt_ge_cases k (Z.to_nat n)) as [L|G].
  - replace k with (Z.to_nat (Z.of_nat k)) by lia. rewrite ovw_nth_raw, zw32_nth by lia. rewrite zdef_znew.
    rewrite zarr_of_junkw_get by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (proj2 (nth_error_None _ _)) by (rewrite ovw_length_nat; lia). rewrite (proj2 (nth_error_None _ _)) by (rewrite zw32_length_nat; lia). reflexivity.
Qed.

Lemma mod16_of_linq : forall x q, (x = 16 * q)%Z -> (x mod 16 = 0)%Z.
Proof. intros x q ->. rewrite Z.mul_comm. apply Z_mod_mult. Qed.
End ACeilS1.


(* [comment removed for export] *)
Ltac lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?v)) _) => change (Z_to_le_bytes 4 v) with (le4 (Z_to_bv 64 v)); mem_after_store
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac take2 FRu H j n newbase jr nr :=
  u8take FRu H n newbase; name_bytes H j n; name_bytes FRu jr nr.

(* [comment removed for export] *)
Ltac stk_eat ST H :=
  let K := fresh "Kst" in
  first [ pose proof (stk_of_u8arr s0segs _ _ _ H) as K; rewrite ?zb8_length_nat, ?ovb_length_nat in K
        | pose proof (stk_of_u32arr s0segs _ _ _ H) as K; rewrite ?zw32_length_nat, ?ovw_length_nat in K
        | pose proof (stk_of_rw_cells s0segs _ _ _ H) as K; cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in K ];
  stk_add ST K; clear H.

(* [comment removed for export] *)
Ltac qlia := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | zify_prune; Zify.zify; xlia zchecker ].
Ltac addr_eq_tac ::= symmetry; first [ apply wa_of_Z_to_bv; qlia | apply wa_of_var; qlia | unfold wa; f_equal; qlia ].
Section ACeilS2. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section S0BS.
  Theorem S0_blockSort : blockSort_spec2 bsX S0C.
  Proof.
    unfold blockSort_spec2. cbn [ci_segs ci_blockSort S0C]. intros until sv.
    intros Ha0 EH1 EH2 AM CM MI ST STK LO AL CX SEP IMG EOK NB FACTS. subst a0.
    pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'.
    cps_destruct CX' as (RE & RE' & RA1 & RA1' & RA2 & RA2' & RFT & RFT' & _ & _ & _ & _ & ME16 & MA1 & MA2 & MFT & _ & _ & LJ & _).
    pose proof SEP as SEP'. unfold cctx_sep, apart in SEP'. cbv zeta in SEP'.
    cps_destruct SEP' as (SE1 & SE2 & SEF & _ & _ & AP12 & AP1F & _ & _ & AP2F & _).
    pose proof IMG as IMG'. unfold cctx_img, img_apart, IMG_LO3, IMG_HI3 in IMG'. cbn [ci_hi S0C] in IMG'. cps_destruct IMG' as (IE & IA1 & IA2 & IFT & _).
    bz_ceil; bz_params; unfold FTAB_WORDS, ESTATE_SIZE, BS_STACK, CEIL in *.
    destruct IA1 as [IA1|IA1]; [exfalso; lia|]. destruct IA2 as [IA2|IA2]; [exfalso; lia|]. destruct IFT as [IFT|IFT]; [exfalso; lia|]. clear IE.
    destruct (mod16_linq _ AL) as [qsp ALQ]. destruct (mod16_linq _ MA1) as [q1 AQ1]. destruct (mod16_linq _ MA2) as [q2 AQ2]. destruct (mod16_linq _ MFT) as [qF AQF].
    destruct (mod16_linq _ ME16) as [qE AQE]. clear AL MA1 MA2 MFT ME16.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    cps_destruct EOK as (A1OK & A2OK & FTW & NBe & _).
    pose proof CM as CM'. cps_destruct CM' as (CM1 & CM2 & CM3 & CM4). cbn [ci_segs ci_got ci_stderrp ci_crc ci_crcx S0C] in CM1, CM2, CM3, CM4.
    open_amem AM. unfold FTAB_WORDS in AR1, AR2, FTB.
    pose proof (zb8_length (e_arr1 e) ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length (e_arr2 e) ARR2_SIZE ltac:(lia)) as L2.
    pose proof (zw32_length (e_ftab e) 65537 ltac:(lia)) as LFT.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    pose proof (munch_refl (blockSort_W cx (bv_unsigned sp)) m) as MU. unfold blockSort_W, FTAB_WORDS, BS_STACK in MU.
    pose proof (wmono_refl s0segs m) as WM.
    pose proof EH1 as EH1f. unfold EHEAD1 in EH1. unfold EHEAD2 in EH2.
    cps_destruct FACTS as (FSM & FHI & FBIGS).
    (* [comment removed for export] *)
    carve_frame 4928%nat ST.
    pose proof (u8arr_of_rw_cells s0segs _ _ _ _ FR) as FRu.
    assert (LJK : Z.of_nat (length junk) = 4928%Z) by (pose proof (proj1 (proj1 (proj1 FR))) as W; cbn in W; lia).
    clear FR.
    u8take FRu FRONTu 4824%Z (bv_unsigned sp + -104)%Z. rename FRu into SAVu.
    name_bytes SAVu jsav 104%Z. name_bytes FRONTu jfr 4824%Z. clear LJK junk.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ SAVu) as SAV. clear SAVu. replace (length jsav) with 104%nat in SAV by lia.
    clear EH1f.
    wstep. do 13 wstep. wstep. wstep.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep.
    wstep. wstep.
    (* [comment removed for export] *)
    replace (bv_unsigned sp + -104)%Z with (bv_unsigned sp - 4928 + 4824)%Z in SAV by lia.
    replace (bv_unsigned sp + -4928)%Z with (bv_unsigned sp - 4928)%Z in ST by lia.
    wstep; if_cases Ksmall; zify_cond_z Ksmall.
    { (* [comment removed for export] *)
      replace (Z_to_bv 64 (bv_unsigned sp + -4928)) with (Z_to_bv 64 (bv_unsigned sp - 4928)) by (f_equal; lia).
      pose proof (FSM ltac:(lia)) as FS. unfold fs_site in FS. cbv zeta in FS. cps_destruct FS as (FSF & OKfm & EXO).
      assert (EH1f : rw_cells s0segs m0 (c_E cx) (EHEAD1 cx g e)) by (unfold EHEAD1; exact EH1). clear EH1.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (S0_bs_fbcall cx g e sp gp tp F fc lo m sv CX SEP IMG NB STK LO (mod16_of_linq _ _ ALQ) _ (e_arr1 e) (e_arr2 e) (e_ftab e)
                      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm) end;
        [st_eq| exact A1OK| exact A2OK| exact FTW| exact FSF| exact EH1f| exact AR1| exact AR2| exact FTB
        | split; [exact CM1| split; [exact CM2| split; [exact CM3| exact CM4]]]| exact MI| exact ST| exact MU| exact WM|].
      intros m2 t0' t1' t2' b0 b1 b2 b3 b4 b5 b6 b7 t3' t4' t5' t6'. cbv zeta. intros EH1' AR1' AR2' FTB' CM2' MI2 ST2 MU2 WM2 MUc WMc.
      clear EH1f AR1 AR2 FTB CM CM1 CM2 CM3 CM4 MI ST MU WM. transport_after_call s0segs m0 m2 MUc WMc. clear MUc WMc.
      (* [comment removed for export] *)
      replace (bv_unsigned sp + -4928)%Z with (bv_unsigned sp - 4928)%Z in FRONTu by lia.
      stk_eat ST2 FRONTu.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (S0_bs_find cx g e ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m CX SEP IMG NB STK LO _ _ _
                      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm) end;
        [st_eq| exact OKfm| exact EXO| apply nm_blockSort_small; lia| exact EH1'| exact EH2| exact AR1'| exact AR2'| exact FTB'| exact SAV| | exact MI2| exact MU2| exact WM2].
      lazymatch type of ST2 with stk _ _ _ ?hi => replace hi with (bv_unsigned sp - 4928 + 4824)%Z in ST2 by lia end. exact ST2. }
    (* [comment removed for export] *)
    assert (NBIG : (10000 <= e_nblock e)%Z) by lia. clear Ksmall.
    cps_destruct (FBIGS NBIG) as (FA & FBIG & FPR). clear FBIGS FSM.
    (* [comment removed for export] *)
    wstep. try rewrite (sx32_of_Z WORKFACTOR) by (bz_params; lia). wstep. wstep. wstep.
    (* [comment removed for export] *)
    eapply (evt_cut s0segs (fun ms' => ms' = _)).
    { wstep; if_true_z. wstep. wstep. wstep. if_cases Kwf; zify_cond_z Kwf.
      - apply evt_done. rewrite <- (wf_clamp_lt100 Kwf). reflexivity.
      - wstep. apply evt_done. rewrite (wf_clamp_ge100 Kwf). reflexivity. }
    intros ms' ->. pose proof (wf_clamp_rng) as WFR.
    set (QO := (e_nblock e + Z.land (e_nblock e) 1 + 34)%Z).
    assert (HQO : (QO = e_nblock e + 34 \/ QO = e_nblock e + 35)%Z /\ (QO mod 2 = 0)%Z).
    { subst QO. rewrite land1_mod2. Z.div_mod_to_equations. lia. }
    destruct HQO as [HQO EQO]. destruct (mod16_linq _ ltac:(replace 16%Z with 2%Z by reflexivity; exact EQO)) as [qq' Hqq'] || idtac.
    assert (Hqq : exists qq, (QO = 2 * qq)%Z) by (exists (QO / 2)%Z; Z.div_mod_to_equations; lia). destruct Hqq as [qq Hqq]. clear EQO.
    replace (Z.land QO 18446744073709551615) with QO by (change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
    assert (EQOF : bp_qoff e = QO).
    { unfold bp_qoff, bp_n, BZ_N_OVERSHOOT. subst QO. rewrite !land1_mod2.
      destruct (Z.eqb_spec ((e_nblock e + 34) mod 2) 0); Z.div_mod_to_equations; lia. }
    assert (LQO : (e_nblock e + 34 <= QO <= e_nblock e + 35)%Z) by lia. clear HQO.
    (* [comment removed for export] *)
    take2 FRONTu P0 j0 16%Z (bv_unsigned sp - 4928 + 16)%Z jr0 4808%Z.
    take2 FRONTu SCAu jsa 128%Z (bv_unsigned sp - 4928 + 144)%Z jr1 4680%Z.
    take2 FRONTu SCBu jsb 148%Z (bv_unsigned sp - 4928 + 292)%Z jr2 4532%Z.
    take2 FRONTu BUDu jbu 4%Z (bv_unsigned sp - 4928 + 296)%Z jr3 4528%Z.
    take2 FRONTu CEu jce 1024%Z (bv_unsigned sp - 4928 + 1320)%Z jr4 3504%Z.
    take2 FRONTu CSu jcs 1024%Z (bv_unsigned sp - 4928 + 2344)%Z jr5 2480%Z.
    take2 FRONTu BDu jbd 256%Z (bv_unsigned sp - 4928 + 2600)%Z jr6 2224%Z.
    take2 FRONTu ROu jro 1024%Z (bv_unsigned sp - 4928 + 3624)%Z jr7 1200%Z.
    take2 FRONTu SDu jsd 400%Z (bv_unsigned sp - 4928 + 4024)%Z jr8 800%Z.
    take2 FRONTu SHu jhi 400%Z (bv_unsigned sp - 4928 + 4424)%Z jlo 400%Z. rename FRONTu into SLu. rename Ljlo into Ljlo'. pose proof Ljlo' as Ljlo. clear Ljlo'.
    replace (bv_unsigned sp + -4928)%Z with (bv_unsigned sp - 4928)%Z in P0 by lia.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ SCAu) as SCA. clear SCAu. replace (length jsa) with 128%nat in SCA by lia.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ SCBu) as SCB. clear SCBu. replace (length jsb) with 148%nat in SCB by lia.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ BUDu) as BUD. clear BUDu. replace (length jbu) with 4%nat in BUD by lia.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ BDu) as BDJ. clear BDu. replace (length jbd) with (Z.to_nat 256) in BDJ by lia.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ ROu) as ROJ. clear ROu. replace (length jro) with (Z.to_nat (4 * 256)) in ROJ by lia.
    pose proof (ovw_init s0segs _ _ 256 _ ROJ ltac:(lia)) as RO. clear ROJ.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ SDu) as SDJ. clear SDu. replace (length jsd) with (Z.to_nat (4 * 100)) in SDJ by lia.
    pose proof (ovw_init s0segs _ _ 100 _ SDJ ltac:(lia)) as SD. clear SDJ.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ SHu) as SHJ. clear SHu. replace (length jhi) with (Z.to_nat (4 * 100)) in SHJ by lia.
    pose proof (ovw_init s0segs _ _ 100 _ SHJ ltac:(lia)) as SHI. clear SHJ.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ SLu) as SLJ. clear SLu. replace (length jlo) with (Z.to_nat (4 * 100)) in SLJ by lia.
    pose proof (ovw_init s0segs _ _ 100 _ SLJ ltac:(lia)) as SLO. clear SLJ.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ CEu) as CEJ. clear CEu. replace (length jce) with (Z.to_nat (4 * 256)) in CEJ by lia.
    pose proof (zw32_of_junk s0segs _ _ 256 _ CEJ ltac:(lia)) as CE. clear CEJ.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ CSu) as CSJ. clear CSu. replace (length jcs) with (Z.to_nat (4 * 256)) in CSJ by lia.
    pose proof (zw32_of_junk s0segs _ _ 256 _ CSJ ltac:(lia)) as CS. clear CSJ.
    replace (Z_to_bv 64 (bv_unsigned sp + -4928)) with (Z_to_bv 64 (bv_unsigned sp - 4928)) by (f_equal; lia).
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. rewrite zext32_id.
    do 5 wstep.
    (* [comment removed for export] *)
    rewrite budget_q_magic_land. wstep.
    rewrite (swrap32_small (e_nblock e * budget_q)) by (pose proof (budget0_rng (e_nblock e) ltac:(lia)); lia).
    wstep. wstep. lit_store. wstep.
    (* [comment removed for export] *)
    set (X := ME ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (c_E cx) (c_A1 cx) (c_A2 cx) (c_FT cx) (e_nblock e) QO lo
                 qE q1 q2 qF qsp (QO / 2) (e_arr1 e) (e_arr2 e) (e_ftab e) sv m).
    assert (XOK : msenv_ok X).
    { unfold msenv_ok, CEILm. cbn [me_E me_A1 me_A2 me_FT me_lo me_sp me_n me_qo me_qE me_q1 me_q2 me_qF me_qsp me_qq me_a1 me_a2 me_ft X].
      repeat (lazymatch goal with |- forall _, _ => fail | |- _ => idtac end; split; [first [assumption| RangeFast.rc_prune_lia| lia| Z.div_mod_to_equations; lia]|]). exact FTW. }   (* [comment removed for export] *)
    assert (XSEP : msenv_sep X) by (unfold msenv_sep, apartm; cbn [me_E me_A1 me_A2 me_FT X]; repeat (split; [first [RangeFast.rc_prune_lia| lia]|]); first [RangeFast.rc_prune_lia| lia]).
    (* [comment removed for export] *)
    wstep; if_true. wstep. wstep. wstep. rewrite zext32_id. wstep. wstep. wstep. wstep. wstep. wstep.
    (* [comment removed for export] *)
    apply (proj1 (u32arr_u8arr s0segs _ _ _)) in FTB. apply (rw_cells_of_u8arr s0segs) in FTB.
    replace (length (u32s (zw32 (e_ftab e) 65537))) with (Z.to_nat 262148) in FTB by (rewrite u32s_length, zw32_length_nat; lia).
    wstep.
    eapply evt_cut.
    { eapply (S0_memset_specZ (c_FT cx) 262148 0); [exact FTB | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia]. }
    clear FTB. lazymatch goal with |- context [S0_memsetZ_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => post_call s0segs mm end.
    match goal with H : rw_cells _ _ (c_FT cx) _ |- _ => rename H into FTZ end.
    match goal with H : mem_inv _ _ |- _ => rename H into MI end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m2 end.
    assert (FTB : u32arr s0segs m2 (c_FT cx) (zw32 (bp_ft0 e) 65537)).
    { rewrite (zw32_ext (bp_ft0 e) znew 65537). 2:{ intros i Hi. rewrite (E_ft0 e), (mft1_get (bp_ft e) i), zget_znew by lia. reflexivity. }
      eapply (zw32_init s0segs _ _ 65537 _ FTZ); [lia| apply repeat_zero_nth]. }
    clear FTZ.
    (* [comment removed for export] *)
    destruct (bs_radix_facts e QO FA EQOF) as [FACC FR2].
    assert (FT0 : forall v, (0 <= v <= 65536)%Z -> zget (bp_ft0 e) v = 0%Z) by (intros v Hv; rewrite (E_ft0 e); apply mft1_get; exact Hv).
    assert (FTNN : forall v, (0 <= zget (bp_ft0 e) v < 4294967296)%Z).
    { intros v. unfold bp_ft0, bp_ft. rewrite ms_ftab_zero_get, of_nat_65537. destruct (_ && _); [lia| apply FTW]. }
    (* [comment removed for export] *)
    wstep.
    pose proof (zb8_read1 s0segs m2 (c_A2 cx) (e_arr2 e) ARR2_SIZE 0 _ AR2 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD. wstep. clear RD. cbv beta.
    pose proof (A2OK 0%Z) as B0. rewrite (unsigned_lit8 (zget (e_arr2 e) 0)) by lia.
    wstep. wstep. wstep. rewrite zext32_id. wstep. rewrite zext32_x2. wstep. wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
    enter_with (S0_bs_radix X _ XOK XSEP (Z.to_nat (e_nblock e / 4)) (Z.to_nat (e_nblock e mod 4)) (e_arr1 e) (e_arr2 e) (bp_ft0 e) jbd
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 m3);
      cbn [me_sp me_A1 me_A2 me_FT me_n me_qo me_gp me_tp me_F me_fc X];
      [st_eq| Z.div_mod_to_equations; lia| Z.div_mod_to_equations; lia| exact A1OK| exact A2OK| exact FT0| exact FTNN| exact FACC| exact FR2
      | exact Ljbd| exact AR1| exact AR2| exact FTB| exact BDJ| exact MI| apply munch_refl| apply wmono_refl|].
    clear FACC FR2.
    intros m4 a2b ftb a1c ftc jb sc y0 y4 y5 y6 y7 y12 y13 y14 y15 y16 y18 y27 y28 y29 y30. cbv zeta.
    cbn [me_sp me_A1 me_A2 me_FT me_n me_qo me_gp me_tp me_F me_fc X].
    intros Er Eqn OK1c OKo FTCc LOWo AR1c AR2o FTBc BD MI4 MU4 WM4. bz_params.
    (* [comment removed for export] *)
    pose proof (nm_mono e QO a2b ftb jb a1c ftc sc EQOF Er Eqn FA) as MONO.
    pose proof (nm_big e QO a2b ftb jb a1c ftc sc EQOF Er Eqn FBIG (zarr_of_junkw jcs 256) (zarr_of_junkw jce 256) znew znew znew) as BF.
    pose proof (nm_pr e QO a2b ftb jb a1c ftc sc EQOF Er Eqn FPR) as PRc.
    pose proof (nm_exit_false e QO a2b ftb jb a1c ftc sc EQOF Er Eqn) as FIN0.
    pose proof (nm_exit_true e QO a2b ftb jb a1c ftc sc EQOF Er Eqn) as FIN1.
    clear Er Eqn FT0 FTNN.
    clear AR1 AR2 FTB BDJ MI. unfold WR in MU4. cbn [me_sp me_A1 me_A2 me_FT X] in MU4.
    transport_after_call s0segs m3 m4 MU4 WM4. clear MU4 WM4.
    set (a2o := ms_overshoot 34 a2b QO (e_nblock e) 0) in *.
    pose proof (zb8_length a1c ARR1_SIZE ltac:(lia)) as L1c. pose proof (zb8_length a2o ARR2_SIZE ltac:(lia)) as L2o. pose proof (zw32_length ftc 65537 ltac:(lia)) as LFc.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m4' end.
    enter_with (S0_bs_shell X _ XOK ftc jro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4' m4');
      cbn [me_sp me_A1 me_A2 me_FT me_n me_qo me_gp me_tp me_F me_fc X];
      [st_eq| exact MONO| exact Ljro| exact RO| exact FTBc| exact MI4| apply munch_refl| apply wmono_refl|].
    intros m5 z5 z6 z7 z9 z10 z11 z12 z13 z14 z15 z16 z28 z29 z30 z31. cbv zeta. cbn [me_sp me_A1 me_A2 me_FT me_n me_qo me_gp me_tp me_F me_fc X].
    intros RK6 RO6 FTB5 MI5 MU5 WM5.
    clear RO FTBc MI4. transport_after_call s0segs m4' m5 MU5 WM5. clear MU5 WM5.
    set (ro6 := ms_shell 8 (snd (ms_ro_init 256 znew znew 0)) ftc 364) in *.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    do 12 wstep.
    (* [comment removed for export] *)
    do 6 wstep. wstep; lit_store. wstep. wstep; lit_store. wstep. wstep; lit_store.
    (* [comment removed for export] *)
    wstep. wstep; lit_store. wstep. wstep. wstep; lit_store. wstep; lit_store.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m6 end.
    replace (e_nblock e + -1)%Z with (e_nblock e - 1)%Z in SCA by lia. replace (c_A1 cx + -4)%Z with (c_A1 cx - 4)%Z in SCA by lia.
    apply (rw_cells_reC8 s0segs m6 _ [_; _; _; _] 3) in SCA. cbn [app c8s_of] in SCA.
    apply (rw_cells_reC8 s0segs m6 _ [_; _; _; _; _; _; _; _; _] 3) in SCA. cbn [app c8s_of] in SCA.
    apply (rw_cells_reC8 s0segs m6 _ [] 2) in SCB. cbn [app c8s_of] in SCB.
    apply (rw_cells_reC8 s0segs m6 _ [_; _; _] 13) in SCB. cbn [app c8s_of] in SCB.
    apply (rw_cells_reC4 s0segs m6 _ [_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _]) in SCB. cbn [app] in SCB.
    rewrite (zb8_ext znew bp_bd5 256) in BD by (intros i _; rewrite bd5_zero; apply zget_znew).
    assert (Hb9 : (0 <= e_nblock e * budget_q < 2147483648)%Z) by (pose proof (budget0_rng (e_nblock e) ltac:(lia)); lia).
    (* [comment removed for export] *)
    enter_with (S0_bigs X _ XOK XSEP 256%nat 0%Z (e_nblock e * budget_q)%Z 0%Z a1c a2o ftc bp_bd5 (zarr_of_junkw jcs 256) (zarr_of_junkw jce 256)
                  znew znew znew znew znew znew ro6 jlo jhi jsd
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 m6);
      cbn [me_sp me_A1 me_A2 me_FT me_n me_qo me_gp me_tp me_F me_fc me_E me_sv X];
      [st_eq| reflexivity| lia| exact Hb9| exact BF| exact OK1c| exact OKo| apply bd5_zbok| exact PRc| exact Ljlo| exact Ljhi| exact Ljsd
      | exact AR1c| exact AR2o| exact FTB5| exact BD| exact CS| exact CE| exact SLO| exact SHI| exact SD| exact RO6
      | unfold sca_cells; cbn [k48 k56 k64 k88 k96 k104 me_sp me_A1 me_A2 me_FT me_n me_qo me_E me_sv X]; exact SCA
      | unfold scb_cells; cbn [k144 k152 k168 k176 k184 k192 k200 k208 k216 k224 k232 k240 k248 k256 k264 k272 k288 me_sp me_A1 me_A2 me_FT me_n me_qo me_E me_sv X]; exact SCB
      | exact BUD| exact MI5| apply munch_refl| apply wmono_refl| |].
    - (* [comment removed for export] *)
      clear BF. intros m7 a1' a2' ft' bd' cs' ce' sl' sh' sd' nl' nh' nd' b' nqs'
             v48 v56 v64 v88 v96 v104 v144 v152 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v288
             u0 u4 u5 u6 u7 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u20 u24 u27 u28 u29 u30.
      intros EB Hb' OK1' OK2' BDOK' PR' AR1' AR2' FTB' BD' CS' CE' SLO' SHI' SD' RO' SCA' SCB' BUD' MI7 MU7 WM7.
      cbn [me_sp me_A1 me_A2 me_FT me_n me_qo me_E me_sv X] in AR1', AR2', FTB', BD', CS', CE', SLO', SHI', SD', RO', SCA', SCB', BUD', MU7.
      bz_params. unfold WB in MU7. cbn [me_sp me_A1 me_A2 me_FT X] in MU7.
      clear AR1c AR2o FTB5 BD CS CE SLO SHI SD RO6 SCA SCB BUD MI5. transport_after_call s0segs m6 m7 MU7 WM7. clear MU7 WM7.
      destruct (FIN0 _ _ _ _ _ _ _ _ _ _ _ _ OK1c OKo RK6 EB FHI ltac:(lia) eq_refl) as [EXO EEf]. pose proof (EEf ltac:(lia)) as EE. clear EEf FIN0 FIN1.
      (* [comment removed for export] *)
      open_sc_in SCA'. open_sc_in SCB'.
      wstep. wstep; if_false. wstep. wstep. wstep. wstep. wstep; if_false.
      wstep; if_cases Kb; [clear Kb| apply bgez_not_taken in Kb; [exfalso; lia| lia]].
      (* [comment removed for export] *)
      stk_eat ST P0. stk_eat ST SCA'. stk_eat ST SCB'. stk_eat ST BUD'. stk_eat ST CE'. stk_eat ST CS'. stk_eat ST BD'. stk_eat ST RO'.
      stk_eat ST SD'. stk_eat ST SHI'. stk_eat ST SLO'.
      assert (EH1f : rw_cells s0segs m7 (c_E cx) (EHEAD1 cx g e)) by (unfold EHEAD1; exact EH1). clear EH1.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (S0_bs_find cx g e ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m CX SEP IMG NB STK LO _ _ _
                      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm) end;
        [st_eq| exact OK1'| exact EXO| exact EE| exact EH1f| exact EH2| exact AR1'| exact AR2'| exact FTB'| exact SAV| | exact MI7| exact MU| exact WM].
      lazymatch type of ST with stk _ _ _ ?hi => replace hi with (bv_unsigned sp - 4928 + 4824)%Z in ST by lia end. exact ST.
    - (* [comment removed for export] *)
      clear BF. intros m7 a1' a2' ft' bd' cs' ce' sl' sh' sd' nl' nh' nd' b' nqs'
             v48 v56 v64 v88 v96 v104 v144 v152 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v288
             u0 u4 u5 u6 u7 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u20 u22 u24 u25 u27 u28 u29 u30.
      intros EB Hb' OK1' OK2' BDOK' PR' AR1' AR2' FTB' BD' CS' CE' SLO' SHI' SD' RO' SCA' SCB' BUD' MI7 MU7 WM7.
      cbn [me_sp me_A1 me_A2 me_FT me_n me_qo me_E me_sv X] in AR1', AR2', FTB', BD', CS', CE', SLO', SHI', SD', RO', SCA', SCB', BUD', MU7.
      bz_params. unfold WB in MU7. cbn [me_sp me_A1 me_A2 me_FT X] in MU7.
      clear AR1c AR2o FTB5 BD CS CE SLO SHI SD RO6 SCA SCB BUD MI5. transport_after_call s0segs m6 m7 MU7 WM7. clear MU7 WM7.
      cps_destruct (FIN1 _ _ _ _ _ _ _ _ _ _ _ _ OK1c OKo RK6 EB FHI ltac:(lia) eq_refl ltac:(lia)) as (FTW' & FS' & EE).
      unfold fs_site in FS'. cbv zeta in FS'. cps_destruct FS' as (FSF' & OKfm' & EXO'). cbv zeta in EE. clear FIN0 FIN1.
      (* [comment removed for export] *)
      open_sc_in SCA'. open_sc_in SCB'.
      wstep. wstep. wstep. wstep; if_false.
      wstep; if_cases Kb; [apply bgez_taken in Kb; [exfalso; lia| lia]| clear Kb].
      wstep. wstep; if_false.
      assert (EH1f : rw_cells s0segs m7 (c_E cx) (EHEAD1 cx g e)) by (unfold EHEAD1; exact EH1). clear EH1.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (S0_bs_fbcall cx g e sp gp tp F fc lo m sv CX SEP IMG NB STK LO (mod16_of_linq _ _ ALQ) _ a1' a2' ft'
                      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm) end;
        [st_eq| exact OK1'| exact OK2'| exact FTW'| exact FSF'| exact EH1f| exact AR1'| exact AR2'| exact FTB'
        | split; [exact CM1| split; [exact CM2| split; [exact CM3| exact CM4]]]| exact MI7| exact ST| exact MU| exact WM|].
      intros m8 t0' t1' t2' b0 b1 b2 b3 b4 b5 b6 b7 t3' t4' t5' t6'. cbv zeta. intros EH1' AR1'' AR2'' FTB'' CM8 MI8 ST8 MU8 WM8 MUc WMc.
      clear EH1f AR1' AR2' FTB' CM1 CM2 CM3 CM4 MI7 ST MU WM. transport_after_call s0segs m7 m8 MUc WMc. clear MUc WMc.
      stk_eat ST8 P0. stk_eat ST8 SCA'. stk_eat ST8 SCB'. stk_eat ST8 BUD'. stk_eat ST8 CE'. stk_eat ST8 CS'. stk_eat ST8 BD'. stk_eat ST8 RO'.
      stk_eat ST8 SD'. stk_eat ST8 SHI'. stk_eat ST8 SLO'.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (S0_bs_find cx g e ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m CX SEP IMG NB STK LO _ _ _
                      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm) end;
        [st_eq| exact OKfm'| exact EXO'| exact EE| exact EH1'| exact EH2| exact AR1''| exact AR2''| exact FTB''| exact SAV| | exact MI8| exact MU8| exact WM8].
      lazymatch type of ST8 with stk _ _ _ ?hi => replace hi with (bv_unsigned sp - 4928 + 4824)%Z in ST8 by lia end. exact ST8.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.
End S0BS.

End ACeilS2.
