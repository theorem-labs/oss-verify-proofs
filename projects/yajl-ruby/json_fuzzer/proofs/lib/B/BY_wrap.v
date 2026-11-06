(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep SFW1_lemmas.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BI_shadow BYajlRep BYajl_iface BY_rz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma thunk_malloc_seg : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (n : Z),
  0 <= n < 2^32 ->
  evtA bsegs P (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 (c_wrap_malloc ACONSTS)) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AY_MALLOC_W) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until n. intros Hn. unfold AY_MALLOC_W. zstepA. zstepA. rewrite (land_M32_small n) by lia. stepA. apply evtA_done. reflexivity.
Qed.

Lemma thunk_free_seg : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  evtA bsegs P (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 (c_wrap_free ACONSTS)) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AY_FREE_W) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros. unfold AY_FREE_W. stepA. stepA. apply evtA_done. reflexivity.
Qed.

Lemma thunk_realloc_seg : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (n : Z),
  0 <= n < 2^32 ->
  evtA bsegs P (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a1 (Z_to_bv 64 n) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 (c_wrap_realloc ACONSTS)) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AY_REALLOC_W) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until n. intros Hn. unfold AY_REALLOC_W. zstepA. zstepA. rewrite (land_M32_small n) by lia. stepA. stepA. stepA. apply evtA_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ab_remove_notin : forall A LB, (forall b, In b LB -> ab_addr b <> A) -> ab_remove A LB = LB.
Proof. aceil.
  intros A LB. induction LB as [|b LB IH]; intros H; cbn; [reflexivity|].
  destruct (Z.eqb_spec (ab_addr b) A) as [E|E]; [exfalso; exact (H b (or_introl eq_refl) E)|].
  rewrite IH; [reflexivity|]. intros b' Hb'. apply H. right. exact Hb'.
Qed.
Lemma ab_find_nodup : forall A sz LB, List.NoDup (map ab_addr LB) -> In (mkABlock A sz) LB -> ab_find A LB = Some (mkABlock A sz).
Proof. aceil.
  intros A sz LB. induction LB as [|b LB IH]; intros ND HIN; [destruct HIN|].
  unfold ab_find. cbn [List.find]. inversion ND as [| x l NI ND']; subst.
  destruct HIN as [->| HIN].
  - cbn [ab_addr]. rewrite Z.eqb_refl. reflexivity.
  - destruct (Z.eqb_spec (ab_addr b) A) as [E|E].
    + exfalso. apply NI. apply in_map_iff. exists (mkABlock A sz). split; [cbn [ab_addr]; symmetry; exact E| exact HIN].
    + unfold ab_find in IH. apply IH; assumption.
Qed.
Lemma ab_remove_incl : forall A LB b, In b (ab_remove A LB) -> In b LB.
Proof. aceil.
  intros A LB. induction LB as [|x LB IH]; intros b H; cbn in *; [exact H|].
  destruct (Z.eqb (ab_addr x) A); [right; exact H|]. destruct H as [H|H]; [left; exact H| right; apply IH; exact H].
Qed.

Section W.
Variable Y : ay_params.
Hypothesis KIPY : AHK_y_kip_stmt Y.
Hypothesis MIY : AHK_y_mem_inv_stmt Y.
Hypothesis BLKY : AHK_y_blocks_stmt Y.
Hypothesis STATY : AHK_y_statics_stmt Y.
Hypothesis BSHY : AHK_y_block_shadow_stmt Y.
Hypothesis BSMALL : AHK_y_small_high_stmt Y.   (* [comment removed for export] *)
Hypothesis AYR2 : AHK_y_ayR_stmt Y.
Hypothesis FREE1 : 1 <= y_free_cost Y.
(* [comment removed for export] *)
Variables (amalloc_rel : Z -> y_APS Y -> Model -> option Z -> y_APS Y -> Model -> Prop)
          (afree_rel : Z -> y_APS Y -> Model -> y_APS Y -> Model -> Prop)
          (arealloc_rel : Z -> Z -> y_APS Y -> Model -> option Z -> y_APS Y -> Model -> Prop).
(* [comment removed for export] *)
#[local] Notation arefund := (y_arefund Y).
Hypothesis AREF0 : forall n, 0 <= arefund n.
Hypothesis AMAL : amalloc_rz_stmt bsegs ACONSTS (y_APS Y) (y_AHK Y) (y_SO Y) amalloc_rel (y_acredit Y) (y_acharge Y) (y_uanchor Y).
Hypothesis AFREE : afree_rz_stmt bsegs ACONSTS (y_APS Y) (y_AHK Y) (y_SO Y) afree_rel (y_acredit Y) arefund (y_uanchor Y).
Hypothesis AREA : arealloc_rz_stmt bsegs ACONSTS (y_APS Y) (y_AHK Y) (y_SO Y) arealloc_rel (y_acredit Y) (y_acharge Y) arefund (y_uanchor Y).
Hypothesis AREAN : arealloc_null_rz_stmt bsegs ACONSTS (y_APS Y) (y_AHK Y) (y_SO Y) arealloc_rel (y_acredit Y) (y_acharge Y) (y_uanchor Y).

(* [comment removed for export] *)
Lemma ay_pres_of_aheap : forall LB LB' LF SP m m',
  aheap_pres bsegs ACONSTS LB LF SP m m' -> (forall b, In b LB' -> In b LB) -> ay_pres LB' LF SP [] m m'.
Proof. aceil.
  intros LB LB' LF SP m m' HP HI a Ha Hc _. apply HP; [exact Ha|].
  destruct Hc as [Hc|[(b & Hb & Hr)|[Hf|Hs]]].
  - left. exact Hc.
  - right; left. exists b. split; [apply HI; exact Hb| exact Hr].
  - right; right; left. exact Hf.
  - right; right; right. unfold adrv_static, ACONSTS. cbn [c_seg3_lo c_seg3_hi c_initialized c_ystat_lo c_ystat_hi]. unfold ay_static in Hs. lia.
Qed.

(* [comment removed for export] *)
Lemma aystatics_of_aheap : forall LB LF SP m m' s' LB' LF' mo',
  aystatics m -> aheap_pres bsegs ACONSTS LB LF SP m m' -> y_AHK Y s' LB' LF' m' mo' -> aystatics m'.
Proof. aceil.
  intros LB LF SP m m' s' LB' LF' mo' (C1 & C2 & C3 & _) HP AHK'.
  assert (HS : forall A cs, rw_cells bsegs m A cs -> 0xa9b40 <= A -> A + Z.of_nat (cells_size cs) <= 0xa9c20 -> rw_cells bsegs m' A cs).
  { intros A cs HC H1 H2. eapply rw_cells_agree; [| exact HC|].
    - intros a Ha Hx. apply HP; [exact Ha| exact Hx].
    - intros a Ha. right; right; right. unfold adrv_static, ACONSTS. cbn [c_seg3_lo c_seg3_hi c_initialized c_ystat_lo c_ystat_hi]. lia. }
  split; [| split; [| split]].
  - apply HS; [exact C1| unfold AY_CALLBACKS; lia| unfold AY_CALLBACKS; cbn; lia].
  - apply HS; [exact C2| unfold AY_BUF_ALLOC_ERROR; lia| unfold AY_BUF_ALLOC_ERROR; cbn; lia].
  - apply HS; [exact C3| unfold AY_NOOP_ALLOCS; lia| unfold AY_NOOP_ALLOCS; cbn; lia].
  - exact (STATY _ _ _ _ _ AHK').
Qed.

Ltac ayframe_post_tac MIY AHK' ST' FRM' I HP :=
  split; [exact (MIY _ _ _ _ _ AHK')|]; split; [exact ST'|]; split; [exact FRM'|]; split; [exact I|];
  eapply ay_pres_of_aheap; [exact HP|].

Theorem aywrap_malloc_proof : aywrap_malloc_stmt Y.
Proof. aceil.
  unfold aywrap_malloc_stmt. intros n LB LF lo RR K. intros until s. intros K0 AY EA1 NR CRED RR0 NBIG FP UA CONT. subst a1.
  destruct FP as (ST & CEIL & LO & SPH & SP16 & MI & TP & FRM). unfold AY_WRAP_STACK in LO.
  apply AYST_split in AY. destruct AY as [AHK0 YS].
  unfold wz. arz_seg KIPY AHK0. clear Hmi.
  eapply evtA_cut; [apply thunk_malloc_seg; lia|]. cbv beta. intros ms1 ->.
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 _]. clear LINK BACK Hh HLI.
  eapply (AMAL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m mo1 s LB LF n lo K);
    [ exact K0 | exact AHK1 | exact ST | exact CEIL | exact LO | exact SP16 | exact SPH | exact TP | exact UA | exact FRM
    | reflexivity | lia | lia | exact NBIG | ].
  cbv beta. intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' mo' s' A ST' HP WM' FRM' SO' _ _ _ CRED' EA AR AHK' (junk & LJ & NEW) BS.
  (* [comment removed for export] *)
  eapply (CONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' m' mo' s' A).
  + ayframe_post_tac MIY AHK' ST' FRM' I HP. intros b Hb; exact Hb.
  + exact SO'.
  + eapply AYR2; [exact AHK0| exact AHK'].
  + lia.
  + cbv beta iota. split; [exact EA|]. split; [exact AR|]. split.
    { pose proof (BSHY _ _ _ _ _ (mkABlock A n) AHK' (or_introl eq_refl) ltac:(cbn; lia)) as [_ X]. exact X. }
    split. { intros Hn. exact (BSMALL _ _ _ _ _ (mkABlock A n) AHK' (or_introl eq_refl) ltac:(cbn; lia)). }
    split; [exact BS|]. split; [exists junk; exact NEW|].
    apply AYST_split. split; [exact AHK'| eapply aystatics_of_aheap; [exact YS| exact HP| exact AHK']].
Qed.

Theorem aywrap_realloc_null_proof : aywrap_realloc_null_stmt Y.
Proof. aceil.
  unfold aywrap_realloc_null_stmt. intros n LB LF lo RR K. intros until s. intros K0 AY EA1 EA2 NR CRED RR0 NBIG FP UA CONT. subst a1 a2.
  destruct FP as (ST & CEIL & LO & SPH & SP16 & MI & TP & FRM). unfold AY_WRAP_STACK in LO.
  apply AYST_split in AY. destruct AY as [AHK0 YS].
  unfold wz. arz_seg KIPY AHK0. clear Hmi.
  eapply evtA_cut; [apply thunk_realloc_seg; lia|]. cbv beta. intros ms1 ->.
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 _]. clear LINK BACK Hh HLI.
  eapply (AREAN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m mo1 s LB LF n lo K);
    [ exact K0 | exact AHK1 | exact ST | exact CEIL | exact LO | exact SP16 | exact SPH | exact TP | exact UA | exact FRM
    | reflexivity | reflexivity | lia | lia | exact NBIG | ].
  cbv beta. intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' mo' s' A ST' HP WM' FRM' SO' _ _ _ CRED' EA AR AHK' (junk & LJ & NEW) BS.
  (* [comment removed for export] *)
  eapply (CONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' m' mo' s' A).
  + ayframe_post_tac MIY AHK' ST' FRM' I HP. intros b Hb; exact Hb.
  + exact SO'.
  + eapply AYR2; [exact AHK0| exact AHK'].
  + lia.
  + cbv beta iota. split; [exact EA|]. split; [exact AR|]. split.
    { pose proof (BSHY _ _ _ _ _ (mkABlock A n) AHK' (or_introl eq_refl) ltac:(cbn; lia)) as [_ X]. exact X. }
    split. { intros Hn. exact (BSMALL _ _ _ _ _ (mkABlock A n) AHK' (or_introl eq_refl) ltac:(cbn; lia)). }
    split; [exact BS|]. split; [exists junk; exact NEW|].
    apply AYST_split. split; [exact AHK'| eapply aystatics_of_aheap; [exact YS| exact HP| exact AHK']].
Qed.

Theorem aywrap_free_proof : aywrap_free_stmt Y.
Proof. aceil.
  unfold aywrap_free_stmt. intros A n LB LF lo RR K. intros until s. intros K0 AY HIN EA1 CRED RR0 NBIG FP UA CONT. subst a1.
  destruct FP as (ST & CEIL & LO & SPH & SP16 & MI & TP & FRM). unfold AY_WRAP_STACK in LO.
  apply AYST_split in AY. destruct AY as [AHK0 YS].
  destruct (BLKY _ _ _ _ _ AHK0) as (RNG & _ & _). pose proof (RNG _ HIN) as AR. unfold ablock_range in AR. cbn [ab_addr ab_size] in AR.
  unfold wz. arz_seg KIPY AHK0. clear Hmi.
  eapply evtA_cut; [apply thunk_free_seg|]. cbv beta. intros ms1 ->.
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 _]. clear LINK BACK Hh HLI.
  eapply (AFREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m mo1 s LB LF A lo K);
    [ exact K0 | exact AHK1 | right; eexists; split; [exact HIN| reflexivity] | exact ST | exact CEIL | exact LO | exact SP16 | exact SPH | exact TP | exact UA | exact FRM
    | reflexivity
    | clear -CRED RR0 FREE1; unfold afree_cost; destruct (Z.eqb A 0); lia     (* [comment removed for export] *)
    | exact NBIG | ].
  cbv beta. intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' mo' s' ST' HP FRM' SO' AHK' _ _ _ CRED'.
  eapply (CONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' m' mo' s').
  + ayframe_post_tac MIY AHK' ST' FRM' I HP. intros b Hb; exact Hb.
  + exact SO'.
  + eapply AYR2; [exact AHK0| exact AHK'].
  + pose proof (AREF0) as R0. unfold arefund_at, afree_cost in CRED'. destruct (ab_find A LB); destruct (Z.eqb_spec A 0); try lia.
    all: pose proof (R0 (ab_size a)); lia.
  + apply AYST_split. split; [exact AHK'| eapply aystatics_of_aheap; [exact YS| exact HP| exact AHK']].
Qed.

Theorem aywrap_free_null_proof : aywrap_free_null_stmt Y.
Proof. aceil.
  unfold aywrap_free_null_stmt. intros u LB LF lo RR K. intros until s. intros K0 AY EA1 CRED RR0 NBIG FP UA CONT. subst a1.
  destruct FP as (ST & CEIL & LO & SPH & SP16 & MI & TP & FRM). unfold AY_WRAP_STACK in LO.
  apply AYST_split in AY. destruct AY as [AHK0 YS].
  destruct (BLKY _ _ _ _ _ AHK0) as (RNG & _ & _).
  assert (RM : ab_remove 0 LB = LB).
  { apply ab_remove_notin. intros b Hb. pose proof (RNG _ Hb) as X. unfold ablock_range in X. lia. }
  unfold wz. arz_seg KIPY AHK0. clear Hmi.
  eapply evtA_cut; [apply thunk_free_seg|]. cbv beta. intros ms1 ->.
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 _]. clear LINK BACK Hh HLI.
  eapply (AFREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m mo1 s LB LF 0 lo K);
    [ exact K0 | exact AHK1 | left; reflexivity | exact ST | exact CEIL | exact LO | exact SP16 | exact SPH | exact TP | exact UA | exact FRM
    | reflexivity
    | clear -CRED RR0; unfold afree_cost; rewrite Z.eqb_refl; lia                 (* [comment removed for export] *)
    | exact NBIG | ].
  cbv beta. rewrite RM. intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' mo' s' ST' HP FRM' SO' AHK' _ _ _ CRED'.
  eapply (CONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' m' mo' s').
  + ayframe_post_tac MIY AHK' ST' FRM' I HP. intros b Hb; exact Hb.
  + exact SO'.
  + eapply AYR2; [exact AHK0| exact AHK'].
  + unfold arefund_at, afree_cost in CRED'. rewrite Z.eqb_refl in CRED'. destruct (ab_find 0 LB); [pose proof (AREF0 (ab_size a))|]; lia.
  + apply AYST_split. split; [exact AHK'| eapply aystatics_of_aheap; [exact YS| exact HP| exact AHK']].
Qed.

Lemma arefund_at_found : forall A sz LB, List.NoDup (map ab_addr LB) -> In (mkABlock A sz) LB -> arefund_at arefund A LB = arefund sz.
Proof. aceil. intros A sz LB ND HIN. unfold arefund_at. rewrite (ab_find_nodup A sz LB ND HIN). reflexivity. Qed.

Theorem aywrap_realloc_proof : aywrap_realloc_stmt Y.
Proof. aceil.
  unfold aywrap_realloc_stmt. intros A sz n old LB LF lo RR K. intros until s. intros K0 AY HIN OLD LOLD EA1 EA2 NR CRED RR0 NBIG FP UA CONT. subst a1 a2.
  destruct FP as (ST & CEIL & LO & SPH & SP16 & MI & TP & FRM). unfold AY_WRAP_STACK in LO.
  apply AYST_split in AY. destruct AY as [AHK0 YS].
  unfold wz. arz_seg KIPY AHK0. clear Hmi.
  eapply evtA_cut; [apply thunk_realloc_seg; lia|]. cbv beta. intros ms1 ->.
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 _]. clear LINK BACK Hh HLI.
  eapply (AREA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m mo1 s LB LF A sz n lo old K);
    [ exact K0 | exact AHK1 | exact HIN | exact OLD | exact LOLD | exact ST | exact CEIL | exact LO | exact SP16 | exact SPH | exact TP | exact UA | exact FRM
    | reflexivity | reflexivity | lia | lia | exact NBIG | ].
  cbv beta. intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' mo' s' A' ST' FRM' SO' _ _ _ CRED' EA AR AHK' CRED2 HP (junk & NEW) BS.
  (* [comment removed for export] *)
  eapply (CONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' m' mo' s' A').
  + ayframe_post_tac MIY AHK' ST' FRM' I HP. intros b Hb; exact Hb.
  + exact SO'.
  + eapply AYR2; [exact AHK0| exact AHK'].
  + unfold arefund_at in CRED2. destruct (ab_find A LB); [pose proof (AREF0 (ab_size a))|]; lia.
  + cbv beta iota. split; [exact EA|]. split; [exact AR|]. split.
    { pose proof (BSHY _ _ _ _ _ (mkABlock A' n) AHK' (or_introl eq_refl) ltac:(cbn; lia)) as [_ X]. exact X. }
    split. { intros Hn. exact (BSMALL _ _ _ _ _ (mkABlock A' n) AHK' (or_introl eq_refl) ltac:(cbn; lia)). }
    split; [exact BS|]. split; [exists junk; exact NEW|].
    split; [apply AYST_split; split; [exact AHK'| eapply aystatics_of_aheap; [exact YS| exact HP| exact AHK']]|].
    destruct (BLKY _ _ _ _ _ AHK0) as (_ & _ & ND). rewrite (arefund_at_found A sz LB ND HIN) in CRED2. lia.
Qed.
End W.
End RC__1.
