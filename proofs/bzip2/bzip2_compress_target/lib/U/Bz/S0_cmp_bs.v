(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Musl Require Import MuslStr. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Musl Require Import S0_memset.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac BzTac2 DecTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzCState BzCSortF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSortM BzCBlock. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCut CmpCut0 CmpFsKit0 BzCQsortM1 BzCQsortM2 BzCSewA.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCFactsFs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCFactsBs BzCPermM BzCFactsBs2 BzCFactsBs3.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCLemmasMs2.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSortM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpFsKit0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCQsortM1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCQsortM2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC.BzCSewB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsBs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCPermM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsBs2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsBs3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasMs2.BzCFactsMs3.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCLemmasMs BzCLemmasMs2 BzCLemmasMs3 BzCLemmasMs4 CmpCutMS CmpMsKit CmpMsKit2 S0_cmp_msV.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCLemmasMs6 UKit U0_bs_top U0_bs_mainS CmpHmKit S0_cmp_bsR S0_cmp_bsS S0_cmp_bsP.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require U0_bs_main.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCLemmasMs5 BzCFactsBs5.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParamsLia.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParamsLia.BzParamsX.
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
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas8.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
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
Lemma rw_cells_join : forall segs m A B pre post,
  rw_cells segs m A pre -> rw_cells segs m B post -> B = (A + Z.of_nat (cells_size pre))%Z -> rw_cells segs m A (pre ++ post).
Proof. intros segs m A B pre post H1 H2 ->. apply rw_cells_app_iff_c. split; [exact H1| exact H2]. Qed.
Lemma rw_cells_mid : forall segs m A l1 l2 l3,
  rw_cells segs m A (l1 ++ l2 ++ l3) <->
  rw_cells segs m A l1 /\ rw_cells segs m (A + Z.of_nat (cells_size l1))%Z l2 /\
  rw_cells segs m (A + Z.of_nat (cells_size l1) + Z.of_nat (cells_size l2))%Z l3.
Proof.
  intros segs m A l1 l2 l3. split.
  - intros H. apply rw_cells_app_iff_c in H. destruct H as [H1 H2]. apply rw_cells_app_iff_c in H2. tauto.
  - intros (H1 & H2 & H3). apply rw_cells_app_iff_c. split; [exact H1|]. apply rw_cells_app_iff_c. tauto.
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
Ltac urun_ls p := first [ urun_to p | urun; lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => lit_store end; urun_ls p ].
Section ACeilS2. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section S0BS.
  Hypothesis S0_bigs : forall X Q, msenv_ok X -> msenv_sep X -> U0_bs_main.U_bigs_spec X Q.
  Let U_bs_main := U0_bs_main.U_bs_main S0_bigs.
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
    carve_frame 104%nat ST. rename FR into SAV. rename junk into jsav.
    carve_frame 4904%nat ST.
    pose proof (u8arr_of_rw_cells s0segs _ _ _ _ FR) as FRONTu.
    assert (Ljfr : Z.of_nat (length junk) = 4904%Z) by (pose proof (proj1 (proj1 (proj1 FR))) as W; cbn in W; lia).
    clear FR. rename junk into jfr.
    clear EH1f.
    urun_to 0x203cc%Z.
    (* [comment removed for export] *)
    urun_to 0x203fc%Z.
    (* [comment removed for export] *)
    wstep; if_cases Kbig; zify_cond_z Kbig.
    2:{ (* [comment removed for export] *)
      urun_to 0x20410%Z.
      replace (Z_to_bv 64 (bv_unsigned sp + -5008)) with (Z_to_bv 64 (bv_unsigned sp - 5008)) by (f_equal; lia).
      replace (bv_unsigned sp + -5008)%Z with (bv_unsigned sp - 5008)%Z in ST by lia.
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
      replace (bv_unsigned sp + -5008)%Z with (bv_unsigned sp - 5008)%Z in FRONTu by lia.
      stk_eat ST2 FRONTu.
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (S0_bs_find cx g e ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m CX SEP IMG NB STK LO _ _ _
                      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm) end;
        [st_eq| exact OKfm| exact EXO| apply nm_blockSort_small; lia| exact EH1'| exact EH2| exact AR1'| exact AR2'| exact FTB'| | | exact MI2| exact MU2| exact WM2].
      - replace (bv_unsigned sp - 5008 + 4904)%Z with (bv_unsigned sp + -104)%Z by lia. exact SAV.
      - lazymatch type of ST2 with stk _ _ _ ?hi => replace hi with (bv_unsigned sp - 5008 + 4904)%Z in ST2 by lia end. exact ST2. }
    (* [comment removed for export] *)
    assert (NBIG : (10000 <= e_nblock e)%Z) by lia. clear Kbig.
    cps_destruct (FBIGS NBIG) as (FA & FBIG & FPR). clear FBIGS FSM.
    (* [comment removed for export] *)
    replace (bv_unsigned sp + -5008)%Z with (bv_unsigned sp - 5008)%Z in FRONTu, ST by lia.
    take2 FRONTu P0 j0 8%Z (bv_unsigned sp - 5008 + 8)%Z jr0 4896%Z.
    take2 FRONTu SA1u jsa1 48%Z (bv_unsigned sp - 5008 + 56)%Z jr1 4848%Z.
    take2 FRONTu FVu jfv 8%Z (bv_unsigned sp - 5008 + 64)%Z jr2 4840%Z.
    take2 FRONTu SA2u jsa2 56%Z (bv_unsigned sp - 5008 + 120)%Z jr3 4784%Z.
    take2 FRONTu SB1u jsb1 104%Z (bv_unsigned sp - 5008 + 224)%Z jr4 4680%Z.
    take2 FRONTu FAu jfa 8%Z (bv_unsigned sp - 5008 + 232)%Z jr5 4672%Z.
    take2 FRONTu SB2u jsb2 72%Z (bv_unsigned sp - 5008 + 304)%Z jr6 4600%Z.
    take2 FRONTu FF1u jff1 8%Z (bv_unsigned sp - 5008 + 312)%Z jr7 4592%Z.
    take2 FRONTu FF2u jff2 24%Z (bv_unsigned sp - 5008 + 336)%Z jr8 4568%Z.
    take2 FRONTu BUDu jbu 4%Z (bv_unsigned sp - 5008 + 340)%Z jr9 4564%Z.
    take2 FRONTu CEu jce 1024%Z (bv_unsigned sp - 5008 + 1364)%Z jr10 3540%Z.
    take2 FRONTu CSu jcs 1024%Z (bv_unsigned sp - 5008 + 2388)%Z jr11 2516%Z.
    take2 FRONTu BDu jbd 256%Z (bv_unsigned sp - 5008 + 2644)%Z jr12 2260%Z.
    take2 FRONTu ROu jro 1024%Z (bv_unsigned sp - 5008 + 3668)%Z jr13 1236%Z.
    take2 FRONTu NXu jnx 36%Z (bv_unsigned sp - 5008 + 3704)%Z jr14 1200%Z.
    take2 FRONTu SDu jsd 400%Z (bv_unsigned sp - 5008 + 4104)%Z jr15 800%Z.
    take2 FRONTu SHu jhi 400%Z (bv_unsigned sp - 5008 + 4504)%Z jlo 400%Z. rename FRONTu into SLu. rename Ljlo into Ljlo'. pose proof Ljlo' as Ljlo. clear Ljlo'.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ SA1u) as SA1. clear SA1u. replace (length jsa1) with (8 * 6)%nat in SA1 by lia. apply rw_cells_junk_C8s in SA1. cbn [c8s_of] in SA1.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ FVu) as FV. clear FVu. replace (length jfv) with (8 * 1)%nat in FV by lia. apply rw_cells_junk_C8s in FV. cbn [c8s_of] in FV.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ SA2u) as SA2. clear SA2u. replace (length jsa2) with (8 * 7)%nat in SA2 by lia. apply rw_cells_junk_C8s in SA2. cbn [c8s_of] in SA2.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ SB1u) as SB1. clear SB1u. replace (length jsb1) with (8 * 13)%nat in SB1 by lia. apply rw_cells_junk_C8s in SB1. cbn [c8s_of] in SB1.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ FAu) as FA8. clear FAu. replace (length jfa) with (8 * 1)%nat in FA8 by lia. apply rw_cells_junk_C8s in FA8. cbn [c8s_of] in FA8.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ SB2u) as SB2. clear SB2u. replace (length jsb2) with (8 * 9)%nat in SB2 by lia. apply rw_cells_junk_C8s in SB2. cbn [c8s_of] in SB2.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ FF1u) as FF1. clear FF1u. replace (length jff1) with (8 * 1)%nat in FF1 by lia. apply rw_cells_junk_C8s in FF1. cbn [c8s_of] in FF1.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ FF2u) as FF2. clear FF2u. replace (length jff2) with (8 * 3)%nat in FF2 by lia. apply rw_cells_junk_C8s in FF2. cbn [c8s_of] in FF2.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ BUDu) as BUD. clear BUDu. replace (length jbu) with 4%nat in BUD by lia. apply rw_cells_junk_C4 in BUD.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ BDu) as BDJ. clear BDu. replace (length jbd) with (Z.to_nat 256) in BDJ by lia.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ ROu) as ROJ. clear ROu. replace (length jro) with (Z.to_nat (4 * 256)) in ROJ by lia.
    pose proof (ovw_init s0segs _ _ 256 _ ROJ ltac:(lia)) as RO. clear ROJ.
    replace (Z_to_bv 64 (bv_unsigned sp + -5008)) with (Z_to_bv 64 (bv_unsigned sp - 5008)) by (f_equal; lia).
    (* [comment removed for export] *)
    urun_to 0x20430%Z.
    set (QO := (e_nblock e + Z.land (e_nblock e) 1 + 34)%Z).
    assert (HQO : (QO = e_nblock e + 34 \/ QO = e_nblock e + 35)%Z /\ (QO mod 2 = 0)%Z).
    { subst QO. rewrite land1_mod2. Z.div_mod_to_equations. lia. }
    destruct HQO as [HQO EQO].
    assert (Hqq : exists qq, (QO = 2 * qq)%Z) by (exists (QO / 2)%Z; Z.div_mod_to_equations; lia). destruct Hqq as [qq Hqq]. clear EQO.
    assert (EQOF : bp_qoff e = QO).
    { unfold bp_qoff, bp_n, BZ_N_OVERSHOOT. subst QO. rewrite !land1_mod2.
      destruct (Z.eqb_spec ((e_nblock e + 34) mod 2) 0); Z.div_mod_to_equations; lia. }
    assert (LQO : (e_nblock e + 34 <= QO <= e_nblock e + 35)%Z) by lia.
    assert (QOe : (Z.land (e_nblock e + 34) 1 = 0 -> QO = e_nblock e + 34)%Z) by (subst QO; rewrite !land1_mod2; Z.div_mod_to_equations; lia).
    assert (QOo : (Z.land (e_nblock e + 34) 1 <> 0 -> QO = e_nblock e + 35)%Z) by (subst QO; rewrite !land1_mod2; Z.div_mod_to_equations; lia).
    clear HQO.
    eapply (evt_cut s0segs (fun ms' => ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 5008)) gp tp t0 t1 t2
          (Z_to_bv 64 (c_FT cx)) (Z_to_bv 64 (c_E cx)) (Z_to_bv 64 WORKFACTOR) (Z_to_bv 64 QO) (Z_to_bv 64 1) (Z_to_bv 64 (e_nblock e)) a4
          (Z_to_bv 64 (c_A2 cx + QO)) a6 a7 (Z_to_bv 64 (c_A1 cx)) (Z_to_bv 64 0) (Z_to_bv 64 (c_A2 cx)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2044c) fc None m0 (seg_rom s0segs))).
    { wstep; if_cases Kp; zify_cond_z Kp.
      - urun_to 0x2044c%Z. pose proof (QOe Kp) as QOv. apply evt_done. st_eq.
      - urun_to 0x2044c%Z. pose proof (QOo Kp) as QOv. apply evt_done. st_eq. }
    intros ms' ->.
    urun_to 0x20470%Z.
    (* [comment removed for export] *)
    eapply (evt_cut s0segs (fun ms' => ms' = _)).
    { wstep; if_true_z. wstep. wstep; if_cases Kwf; zify_cond_z Kwf.
      - apply evt_done. rewrite <- (wf_clamp_lt100 Kwf). reflexivity.
      - wstep. apply evt_done. rewrite (wf_clamp_ge100 Kwf). reflexivity. }
    intros ms' ->. pose proof (wf_clamp_rng) as WFR.
    (* [comment removed for export] *)
    urun_to 0x20498%Z.
    (* [comment removed for export] *)
    rewrite budget_q_magic_land.
    wstep. wstep.
    rewrite (swrap32_small (e_nblock e * budget_q)) by (pose proof (budget0_rng (e_nblock e) ltac:(lia)); lia).
    (* [comment removed for export] *)
    urun_ls 0x204dc%Z.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (U_ftab_zero (c_FT cx) (bv_unsigned sp - 5008) _ ra gp tp t0 t1 t2 (Z_to_bv 64 (c_FT cx)) (Z_to_bv 64 (c_E cx))
                    (Z_to_bv 64 (c_A2 cx + QO)) a6 a7 (Z_to_bv 64 (c_A1 cx)) (Z_to_bv 64 0) (Z_to_bv 64 (c_A2 cx)) (Z_to_bv 64 (e_nblock e * budget_q))
                    s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ltac:(lia) ltac:(rewrite AQF; Z.div_mod_to_equations; lia) ltac:(lia)
                    ltac:(change (2 ^ 64)%Z with 18446744073709551616%Z; lia)
                    65537%nat 65536 (e_ftab e) (Z_to_bv 64 (e_nblock e)) (Z_to_bv 64 0) mm mm) end;
      [st_eq| rewrite of_nat_65537; lia| lia| exact FTW| exact FTB| exact MI| exact FF1| apply munch_refl| apply wmono_refl|].
    intros m2 x13' x14'. cbv zeta. intros FTNN FTB0 MI2 FF1b MUf WMf.
    clear FTB MI FF1. transport_after_call s0segs m1 m2 MUf WMf. clear MUf WMf.
    change (ms_ftab_zero 65537 (e_ftab e) 65536) with (bp_ft0 e) in FTNN, FTB0. rename FTB0 into FTB. rename MI2 into MI.
    (* [comment removed for export] *)
    destruct (bs_radix_facts e QO FA EQOF) as [FACC FR2].
    assert (FT0 : forall v, (0 <= v <= 65536)%Z -> zget (bp_ft0 e) v = 0%Z) by (intros v Hv; rewrite (E_ft0 e); apply mft1_get; exact Hv).
    (* [comment removed for export] *)
    urun_ls 0x20540%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zb8_read1 s0segs mm (c_A2 cx) (e_arr2 e) ARR2_SIZE 0 _ AR2 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
    wstep. clear RD. cbv beta.
    pose proof (A2OK 0%Z) as B0. rewrite (unsigned_lit8 (zget (e_arr2 e) 0)) by lia.
    urun_ls 0x20560%Z.
    (* [comment removed for export] *)
    set (X := ME ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (c_E cx) (c_A1 cx) (c_A2 cx) (c_FT cx) (e_nblock e) QO lo
                 qE q1 q2 qF qsp (QO / 2) (e_arr1 e) (e_arr2 e) (e_ftab e) sv m).
    assert (XOK : msenv_ok X).
    { unfold msenv_ok, CEILm. cbn [me_E me_A1 me_A2 me_FT me_lo me_sp me_n me_qo me_qE me_q1 me_q2 me_qF me_qsp me_qq me_a1 me_a2 me_ft X].
      repeat (lazymatch goal with |- forall _, _ => fail | |- _ => idtac end; split; [first [assumption| RangeFast.rc_prune_lia| lia| Z.div_mod_to_equations; lia]|]). exact FTW. }   (* [comment removed for export] *)
    assert (XSEP : msenv_sep X) by (unfold msenv_sep, apartm; cbn [me_E me_A1 me_A2 me_FT X]; repeat (split; [first [RangeFast.rc_prune_lia| lia]|]); first [RangeFast.rc_prune_lia| lia]).
    pose proof (rw_cells_join s0segs _ _ _ _ _ FF1b FF2 ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as FF. cbn [app] in FF. clear FF1b FF2.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
    enter_with (S0_bs_radix X _ XOK XSEP (Z.to_nat (e_nblock e / 4)) (Z.to_nat (e_nblock e mod 4)) (e_arr1 e) (e_arr2 e) (bp_ft0 e)
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 m3);
      cbn [me_sp me_A1 me_A2 me_FT me_n me_qo me_gp me_tp me_F me_fc X];
      [st_eq| Z.div_mod_to_equations; lia| Z.div_mod_to_equations; lia| exact A1OK| exact A2OK| exact FT0| exact FTNN| exact FACC| exact FR2
      | exact AR1| exact AR2| exact FTB| exact FV| exact FA8| exact FF| exact MI| apply munch_refl| apply wmono_refl|].
    clear FACC FR2.
    intros m4 a2b ftb a1c ftc jb sc y4 y9 y10 y11 y12 y13 y14 y15 y16. cbv zeta.
    cbn [me_sp me_A1 me_A2 me_FT me_n me_qo me_gp me_tp me_F me_fc X].
    intros Er Eqn OK1c OKo FTCc LOWo AR1c AR2o FTBc FV4 FA4 FF4 MI4 MU4 WM4. bz_params.
    (* [comment removed for export] *)
    pose proof (nm_mono e QO a2b ftb jb a1c ftc sc EQOF Er Eqn FA) as MONO.
    clear AR1 AR2 FTB MI FV FA8 FF FT0 FTNN. unfold WR in MU4. cbn [me_sp me_A1 me_A2 me_FT X] in MU4.
    transport_after_call s0segs m3 m4 MU4 WM4. clear MU4 WM4.
    set (a2o := ms_overshoot 34 a2b QO (e_nblock e) 0) in *.
    pose proof (zb8_length a1c ARR1_SIZE ltac:(lia)) as L1c. pose proof (zb8_length a2o ARR2_SIZE ltac:(lia)) as L2o. pose proof (zw32_length ftc 65537 ltac:(lia)) as LFc.
    (* [comment removed for export] *)
    enter_with (S0_bs_shell X _ XOK XSEP ftc jro jbd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 m4);
      cbn [me_sp me_A1 me_A2 me_FT me_n me_qo me_gp me_tp me_F me_fc X];
      [st_eq| exact MONO| exact Ljro| exact Ljbd| exact RO| exact BDJ| exact FTBc| exact FV4| exact FA4| exact FF4| exact MI4| apply munch_refl| apply wmono_refl|].
    intros m5 z0 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z18 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30. cbv zeta.
    cbn [me_sp me_A1 me_A2 me_FT me_n me_qo me_gp me_tp me_F me_fc X].
    intros RK6 RO6 BD6 FTB5 FV5 FA5 FF5 MI5 MU5 WM5.
    clear RO BDJ FTBc FV4 FA4 FF4 MI4. transport_after_call s0segs m4 m5 MU5 WM5. clear MU5 WM5.
    set (ro6 := ms_shell 8 (snd (ms_ro_init 256 znew znew 0)) ftc 364) in *.
    pose proof (rw_cells_join s0segs _ _ _ _ _ SA1 FV5 ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as SCA. cbn [app] in SCA. clear SA1 FV5.
    pose proof (rw_cells_join s0segs _ _ _ _ _ SCA SA2 ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as SCA'. cbn [app] in SCA'. clear SCA SA2. rename SCA' into SCA.
    pose proof (rw_cells_join s0segs _ _ _ _ _ SB1 FA5 ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as SCB. cbn [app] in SCB. clear SB1 FA5.
    pose proof (rw_cells_join s0segs _ _ _ _ _ SCB SB2 ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as SCB'. cbn [app] in SCB'. clear SCB SB2. rename SCB' into SCB.
    pose proof (rw_cells_join s0segs _ _ _ _ _ SCB FF5 ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as SCB'. cbn [app] in SCB'. clear SCB FF5. rename SCB' into SCB.
    replace (e_nblock e + -1)%Z with (e_nblock e - 1)%Z in SCA by lia.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ P0) as P0c. clear P0. replace (length j0) with 8%nat in P0c by lia.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ CEu) as CE. clear CEu. replace (length jce) with 1024%nat in CE by lia.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ CSu) as CS. clear CSu. replace (length jcs) with 1024%nat in CS by lia.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ NXu) as NX. clear NXu. replace (length jnx) with 36%nat in NX by lia.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ SDu) as SD. clear SDu. replace (length jsd) with 400%nat in SD by lia.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ SHu) as SHI. clear SHu. replace (length jhi) with 400%nat in SHI by lia.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ SLu) as SLO. clear SLu. replace (length jlo) with 400%nat in SLO by lia.
    rewrite (zb8_ext znew bp_bd5 256) in BD6 by (intros i _; rewrite bd5_zero; apply zget_znew).
    apply (rw_cells_mid s0segs m5 (c_E cx) [_; _; _; _; _] [_; _] _) in EH1. destruct EH1 as (EHa & E24 & EHb).
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in E24, EHb.
    pose proof (nm_big e QO a2b ftb jb a1c ftc sc EQOF Er Eqn FBIG) as BF.
    pose proof (nm_pr e QO a2b ftb jb a1c ftc sc EQOF Er Eqn FPR) as PRc.
    pose proof (nm_exit_false e QO a2b ftb jb a1c ftc sc EQOF Er Eqn) as FIN0.
    pose proof (nm_exit_true e QO a2b ftb jb a1c ftc sc EQOF Er Eqn) as FIN1.
    assert (Hb9 : (0 <= e_nblock e * budget_q < 2147483648)%Z) by (pose proof (budget0_rng (e_nblock e) ltac:(lia)); lia).
    (* [comment removed for export] *)
    enter_with (U_bs_main X _ XOK XSEP a1c a2o ftc bp_bd5 ro6 j0 jce jcs jnx jsd jhi jlo
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 m5);
      cbn [me_sp me_A1 me_A2 me_FT me_n me_qo me_gp me_tp me_F me_fc me_E me_sv X];
      [st_eq| lia| lia| lia| exact OK1c| exact OKo| apply bd5_zbok| exact PRc| exact Hb9| exact BF
      | intros cs ce nl nh nd k Hk; pose proof (bsB_bigN_ok e A2OK ltac:(lia) cs ce nl nh nd k ltac:(lia)) as BN;
        erewrite nm_ro6, nm_a1r, nm_a2o, nm_ft4 in BN by eassumption; rewrite nm_budget, EQOF in BN; unfold bp_n in BN; exact BN
      | exact AR1c| exact AR2o| exact FTB5| exact P0c| exact SCA| exact SCB| exact BUD| exact CE| exact CS| exact BD6| exact RO6
      | exact NX| exact SD| exact SHI| exact SLO| exact E24
      | split; [exact CM1| split; [exact CM2| split; [exact CM3| exact CM4]]]| exact MI5| apply munch_refl| apply wmono_refl| |].
    - (* [comment removed for export] *)
      clear BF CM1 CM2 CM3 CM4. try clear CM.
      intros m7 a1' a2' ft' bd' cs' ce' CSJ CEJ b' nqs' L'
             u0 u4 u5 u6 u7 u9 u10 u11 u12 u13 u14 u15 u16 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29 u30.
      intros EB Hb' OK1' OK2' AR1' AR2' FTB' STF E24' CM7 MI7 MU7 WM7.
      unfold WMAIN in MU7. cbn [me_sp me_A1 me_A2 me_FT X] in MU7.
      clear AR1c AR2o FTB5 BD6 RO6 P0c SCA SCB BUD CE CS NX SD SHI SLO E24 MI5. transport_after_call s0segs m5 m7 MU7 WM7. clear MU7 WM7.
      destruct (FIN0 _ _ _ _ _ _ _ _ _ _ _ _ OK1c OKo RK6 EB FHI ltac:(lia) eq_refl) as [EXO EEf]. pose proof (EEf Hb') as EE. clear EEf FIN0 FIN1.
      (* [comment removed for export] *)
      stk_add ST STF.
      assert (EH1f : rw_cells s0segs m7 (c_E cx) (EHEAD1 cx g e))
        by (unfold EHEAD1; apply (proj2 (rw_cells_mid s0segs m7 (c_E cx) [_; _; _; _; _] [_; _] _)); split; [exact EHa| split; [exact E24'| exact EHb]]).
      clear EHa E24' EHb.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (S0_bs_find cx g e ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m CX SEP IMG NB STK LO _ _ _
                      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm) end;
        [st_eq| exact OK1'| exact EXO| exact EE| exact EH1f| exact EH2| exact AR1'| exact AR2'| exact FTB'| | | exact MI7| exact MU| exact WM].
      + replace (bv_unsigned sp - 5008 + 4904)%Z with (bv_unsigned sp + -104)%Z by lia. exact SAV.
      + lazymatch type of ST with stk _ _ _ ?hi => replace hi with (bv_unsigned sp - 5008 + 4904)%Z in ST by lia end. exact ST.
    - (* [comment removed for export] *)
      clear BF CM1 CM2 CM3 CM4. try clear CM.
      intros m7 a1' a2' ft' bd' cs' ce' CSJ CEJ b' nqs' L'
             u0 u4 u5 u6 u7 u14 u15 u16 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29 u30.
      intros EB Hb' OK1' OK2' AR1' AR2' FTB' STF E24' CM7 MI7 MU7 WM7.
      unfold WMAIN in MU7. cbn [me_sp me_A1 me_A2 me_FT X] in MU7.
      clear AR1c AR2o FTB5 BD6 RO6 P0c SCA SCB BUD CE CS NX SD SHI SLO E24 MI5. transport_after_call s0segs m5 m7 MU7 WM7. clear MU7 WM7.
      cps_destruct (FIN1 _ _ _ _ _ _ _ _ _ _ _ _ OK1c OKo RK6 EB FHI ltac:(lia) eq_refl Hb') as (FTW' & FS' & EE).
      unfold fs_site in FS'. cbv zeta in FS'. cps_destruct FS' as (FSF' & OKfm' & EXO'). cbv zeta in EE. clear FIN0 FIN1.
      assert (EH1f : rw_cells s0segs m7 (c_E cx) (EHEAD1 cx g e))
        by (unfold EHEAD1; apply (proj2 (rw_cells_mid s0segs m7 (c_E cx) [_; _; _; _; _] [_; _] _)); split; [exact EHa| split; [exact E24'| exact EHb]]).
      clear EHa E24' EHb.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (S0_bs_fbcall cx g e sp gp tp F fc lo m sv CX SEP IMG NB STK LO (mod16_of_linq _ _ ALQ) _ a1' a2' ft'
                      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm) end;
        [st_eq| exact OK1'| exact OK2'| exact FTW'| exact FSF'| exact EH1f| exact AR1'| exact AR2'| exact FTB'
        | exact CM7| exact MI7| exact ST| exact MU| exact WM|].
      intros m8 t0' t1' t2' b0 b1 b2 b3 b4 b5 b6 b7 t3' t4' t5' t6'. cbv zeta. intros EH1' AR1'' AR2'' FTB'' CM8 MI8 ST8 MU8 WM8 MUc WMc.
      clear EH1f AR1' AR2' FTB' CM7 MI7 ST MU WM. transport_after_call s0segs m7 m8 MUc WMc. clear MUc WMc.
      stk_add ST8 STF.
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (S0_bs_find cx g e ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m CX SEP IMG NB STK LO _ _ _
                      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm) end;
        [st_eq| exact OKfm'| exact EXO'| exact EE| exact EH1'| exact EH2| exact AR1''| exact AR2''| exact FTB''| | | exact MI8| exact MU8| exact WM8].
      + replace (bv_unsigned sp - 5008 + 4904)%Z with (bv_unsigned sp + -104)%Z by lia. exact SAV.
      + lazymatch type of ST8 with stk _ _ _ ?hi => replace hi with (bv_unsigned sp - 5008 + 4904)%Z in ST8 by lia end. exact ST8.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.
End S0BS.

End ACeilS2.
