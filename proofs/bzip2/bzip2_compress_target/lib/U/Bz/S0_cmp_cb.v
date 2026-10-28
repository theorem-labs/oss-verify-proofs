(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require SegsS0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast Frame.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.StoreFast OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Frame.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCBlock. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArrD BzCLemmas1 CmpMem BzSepTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCut CmpCut0 CmpCutSM CmpSdTac. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpArith. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpArith2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpArith2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCNumZ. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzWalkArith4. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCLemmasSd.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_cmp_cbT.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCutBsw S0_cmp_bsx4. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCutCB. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCutCBw CmpCutMtf CmpCutMtf0 CmpCutSmA CmpCutSmA0 CmpCutSmB CmpCutSmB0 CmpCutSmC CmpCutSmC0 CmpCutSD CmpCutSD0 CmpLaws. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCFactsGm. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCFactsSmA BzCFactsSmA2 BzCFactsSmB BzCFactsSmB3. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCFactsSd BzCFactsSd2 BzCFactsCb. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpSmKit CmpSmKit2 CmpSmKit20 CmpHmKit CmpMsKit2 CmpCutMS BzCLemmasMs6 S0_cmp_cbT S0_cmp_cbH1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_cmp_cbH3.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_cmp_cbH3 S0_cmp_cbU.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import U0_smSpec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutSM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpSdTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpArith2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpArith2.CmpSdArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCNumZ OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasSd OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_cbT.S0_cmp_bsw OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutBsw OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_bsx4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutCB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutCBw OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutMtf OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutMtf0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutSmA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutSmA0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutSmB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutSmB0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutSmC OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutSmC0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutSD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutSD0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpLaws OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsGm OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsSmA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsSmA2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsSmB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsSmB3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsSd OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsSd2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsCb OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpSmKit OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpSmKit2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpSmKit20 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpHmKit OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpMsKit2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutMS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasMs6 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_cbT OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_cbH1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_cbH3.S0_cmp_cbH2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_cbH3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_cbU.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac tlia ::= first [ Zify.zify; xlia zchecker
                         | sf_unhide; unhide_disj;
                           first [ zify_prune_neg; Zify.zify; xlia zchecker
                                 | zify_prune_plain; Zify.zify; xlia zchecker
                                 | Zify.zify; xlia zchecker ] ].
Local Ltac tslia ::= tslia_sep.
Local Ltac simpl_sizes_goal ::=
  literal_cell_sizes;
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  try match goal with |- context [length (le8 _)] => rewrite !length_le8 end;
  try match goal with |- context [length (le4 _)] => rewrite !length_le4 end;
  try match goal with |- context [length (le2 _)] => rewrite !length_le2 end;
  try match goal with |- context [length (le1 _)] => rewrite !length_le1 end;
  try match goal with |- context [length (u32s _)] => rewrite !u32s_length end;
  try match goal with |- context [length (u64s _)] => rewrite !u64s_length end;
  try match goal with |- context [length (upd _ _ _)] => rewrite !upd_length end;
  try match goal with |- context [length (zb8 _ _)] => rewrite !zb8_length_nat end;
  try match goal with |- context [length (ovb _ _ _)] => rewrite !ovb_length_nat end;
  try match goal with |- context [length (ovw _ _ _)] => rewrite !ovw_length_nat end;
  try match goal with |- context [length (zw32 _ _)] => rewrite !zw32_length_nat end.
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
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | sf_unhide; unhide_disj; first [ zify_prune_neg; Zify.zify; xlia zchecker | zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepVS.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepVS.tslia_vs.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma disjoint_from_subX : forall W A n A' n',
  disjoint_from W A n -> (A <= A')%Z -> (A' + n' <= A + n)%Z -> disjoint_from W A' n'.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros A n A' n' D H1 H2; [exact I|].
  destruct D as [D1 D2]. split; [lia| eapply IH; eauto].
Qed.
(* [comment removed for export] *)
Lemma erest_transport0 : forall cx e W m m',
  erest cx e m -> munch W m m' -> wmono s0segs m m' -> cctx_ok cx ->
  disjoint_from W (c_E cx + 128) 512 -> disjoint_from W (c_E cx + 672) (ESTATE_SIZE - 672) -> erest cx e m'.
Proof.
  (intros cx e W m m'; cps_intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9); intros MU WM CX D1 D2).
  pose proof CX as C; unfold cctx_ok in C; cbv zeta in C. cps_destruct C as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LJ & _).
  unfold ESTATE_SIZE in *. unfold erest.
  split; [eapply u8arr_transport; [exact H1 | exact MU | exact WM | rewrite ovb_length by lia; eapply disjoint_from_subX; [exact D1 | lia | lia] ]|].
  split; [eapply u8arr_transport; [exact H2 | exact MU | exact WM | rewrite ovb_length by lia; eapply disjoint_from_subX; [exact D1 | lia | lia] ]|].
  repeat match goal with |- _ /\ _ => split end;
  first [ eapply u8arr_transport; [eassumption | exact MU | exact WM | rewrite ovb_length by lia; eapply disjoint_from_subX; [exact D2 | lia | lia] ]
        | eapply u32arr_transport; [eassumption | exact MU | exact WM | rewrite ovw_length by lia; eapply disjoint_from_subX; [exact D2 | lia | lia] ] ].
Qed.
(* [comment removed for export] *)
Lemma erest_fields : forall g e, cb_entry g e -> (0 < e_nblock e)%Z ->
  e_inUse (cbEU5 e) = e_inUse e /\ e_unseqToSeq (cbEU5 e) = e_unseqToSeq e /\ e_mtfFreq (cbEU5 e) = e_mtfFreq e /\
  e_selector (cbEU5 e) = e_selector e /\ e_selectorMtf (cbEU5 e) = e_selectorMtf e /\ e_len (cbEU5 e) = e_len e /\
  e_code (cbEU5 e) = e_code e /\ e_rfreq (cbEU5 e) = e_rfreq e /\ e_len_pack (cbEU5 e) = e_len_pack e /\
  e_arr1 (cbEU5 e) = e_arr1 (cbE1 e) /\ e_ftab (cbEU5 e) = e_ftab (cbE1 e) /\ e_nblock (cbE1 e) = e_nblock e /\
  e_mode (cbEU5 e) = e_mode e /\ e_state (cbEU5 e) = e_state e /\ e_avail_in_expect (cbEU5 e) = e_avail_in_expect e /\
  e_state_in_ch (cbEU5 e) = e_state_in_ch e /\ e_state_in_len (cbEU5 e) = e_state_in_len e /\ e_state_out_pos (cbEU5 e) = e_state_out_pos e /\
  e_blockNo (cbEU5 e) = e_blockNo e /\ e_nMTF (cbEU5 e) = e_nMTF e /\ e_origPtr (cbEU5 e) = e_origPtr (cbE1 e) /\
  e_blockCRC (cbEU5 e) = e_blockCRC (cbE0 e) /\ e_combinedCRC (cbEU5 e) = e_combinedCRC (cbE0 e).
Proof.
  intros g e CE POS. cps_destruct (cbE1_shape g e CE POS) as (sa1 & sa2 & sft & sop & E1 & _).
  unfold cbEU5, est_set_arr2, est_set_bw. rewrite E1.
  cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse
       e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code e_rfreq e_len_pack].
  repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma est_C_nblock : forall x c f p h w q, e_nblock (est_C x c f p h w q) = e_nblock x. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma est_C_combinedCRC : forall x c f p h w q, e_combinedCRC (est_C x c f p h w q) = e_combinedCRC x. Proof. reflexivity. Qed.
Lemma est_C_arr2 : forall x c f p h w q, e_arr2 (est_C x c f p h w q) = e_arr2 x. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma outside_in : forall W x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof.
  induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|].
  destruct H as [H1 H2]. destruct HI as [E | HI]; [injection E; intros; subst; exact H1| exact (IH _ _ _ H2 HI)].
Qed.
Lemma sub_fp_nilX : forall W', sub_fp [] W'. Proof. intros W' x _. exact I. Qed.
Lemma sub_fp_consX : forall lo hi W W',
  (exists lo' hi', In (lo', hi') W' /\ (lo' <= lo)%Z /\ (hi <= hi')%Z) -> sub_fp W W' -> sub_fp ((lo, hi) :: W) W'.
Proof.
  (intros lo hi W W'; cps_intros (lo' & hi' & HI & L1 & L2); intros SUB x OX). cbn. split; [| exact (SUB x OX)].
  pose proof (outside_in W' x lo' hi' OX HI). lia.
Qed.
End ACeilS1.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac sub_fp_same_base :=
  lazymatch goal with |- (?lo' <= ?lo)%Z /\ _ =>
    let rec base e := lazymatch e with Z.add ?x _ => base x | Z.sub ?x _ => base x | _ => e end in
    let b1 := base lo' in let b2 := base lo in
    first [ constr_eq b1 b2
          | lazymatch b1 with bv_unsigned _ => lazymatch b2 with bv_unsigned _ => idtac end end ]   (* [comment removed for export] *)
  end.
Ltac sub_fp_tac :=
  repeat (apply sub_fp_consX;
          [ first [ eexists; eexists; split; [cbn [In]; left; reflexivity| sub_fp_same_base; split; lia]
                  | eexists; eexists; split; [cbn [In]; right; left; reflexivity| sub_fp_same_base; split; lia]
                  | eexists; eexists; split; [cbn [In]; right; right; left; reflexivity| sub_fp_same_base; split; lia]
                  | eexists; eexists; split; [cbn [In]; right; right; right; left; reflexivity| sub_fp_same_base; split; lia]
                  | eexists; eexists; split; [cbn [In]; right; right; right; right; left; reflexivity| sub_fp_same_base; split; lia]
                  | eexists; eexists; split; [cbn [In]; left; reflexivity| split; lia]
                  | eexists; eexists; split; [cbn [In]; right; left; reflexivity| split; lia]
                  | eexists; eexists; split; [cbn [In]; right; right; left; reflexivity| split; lia]
                  | eexists; eexists; split; [cbn [In]; right; right; right; left; reflexivity| split; lia]
                  | eexists; eexists; split; [cbn [In]; right; right; right; right; left; reflexivity| split; lia] ]
          | ]);
  apply sub_fp_nilX.
Section ACeilS2. Context {BZP : BzParams} {ACEIL__ : ACeil}.
Hypothesis S0_blockSort : blockSort_spec2 bsX S0C.


Lemma cbZBL_eq : forall e b, cbZBL e b = zbl (e_arr2 (cbE1 e)) (e_nblock e) b. Proof. reflexivity. Qed.

Section ASSEMBLY.

  (* [comment removed for export] *)
  Lemma cbH_W_hi : forall cx m m' A cs, cctx_ok cx -> (CEIL <= A)%Z -> rw_cells s0segs m A cs -> munch (cbH_W cx) m m' -> wmono s0segs m m' -> rw_cells s0segs m' A cs.
  Proof.
    intros cx m m' A cs CX HA H MU WM. pose proof CX as C; unfold cctx_ok in C; cbv zeta in C. cps_destruct C as (E0 & E1 & _ & _ & A0 & A1 & _).
    bz_ceil; bz_params; unfold ESTATE_SIZE, CEIL in *. eapply rw_cells_transport; [exact H| exact MU| exact WM|].
    unfold cbH_W. cbv [disjoint_from fst snd]. repeat split; try exact I; lia.
  Qed.
  Lemma cbH_W_hi8 : forall cx m m' A bs, cctx_ok cx -> (CEIL <= A)%Z -> u8arr s0segs m A bs -> munch (cbH_W cx) m m' -> wmono s0segs m m' -> u8arr s0segs m' A bs.
  Proof.
    intros cx m m' A bs CX HA H MU WM. pose proof CX as C; unfold cctx_ok in C; cbv zeta in C. cps_destruct C as (E0 & E1 & _ & _ & A0 & A1 & _).
    bz_ceil; bz_params; unfold ESTATE_SIZE, CEIL in *. eapply u8arr_transport; [exact H| exact MU| exact WM|].
    unfold cbH_W. cbv [disjoint_from fst snd]. repeat split; try exact I; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma S0_cb_pos : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cx : cctx) (g : eg) (e : est) (is_last : bool) (lo : Z) (sv : word),
    (0 < e_nblock e)%Z ->
    a0 = Z_to_bv 64 (c_E cx) -> a1 = Z_to_bv 64 (if is_last then 1 else 0) ->
    emem cx s0segs g e m -> amem cx s0segs e m -> cimg_mem S0C m sv -> mem_inv s0segs m ->
    stk s0segs m lo (bv_unsigned sp) -> (lo + CB_STACK <= bv_unsigned sp)%Z -> (CEIL <= lo)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
    cctx_ok cx -> cctx_sep cx -> cctx_img S0C cx -> cb_pre g e -> cb_facts e ->
    evt s0segs (compressBlock_post s0segs S0C cx g e is_last sv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (compressBlock_W cx (bv_unsigned sp)) m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x16344) fc None m (seg_rom s0segs)).
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cx g e is_last lo sv.
    intros POS -> -> EM AM CM MI ST STK LO AL CX SEP IMG PRE CF.
    pose proof (conj PRE CF : cb_entry g e) as CE.
    set (Q := compressBlock_post s0segs S0C cx g e is_last sv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (compressBlock_W cx (bv_unsigned sp)) m).
    (* [comment removed for export] *)
    cps_pose (cb_entry_facts g e CE) as (EOK & NBR & DEFR & IU & OP0 & NZ0 & BN1 & ALT).
    cps_pose EOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BCR & CCR & BNR). bz_params.
    cps_destruct (cbE1_shape g e CE POS) as (sa1 & sa2 & sft & sop & E1 & Z1 & Z2 & ZF & OPR).
    cps_pose (cbBS_facts g e CE POS) as (OKS & NS & _ & _ & _ & _).
    cps_pose (cbBH_facts g e CE POS) as (OKH & NH & _ & LH & BCH & OPH & _).
    cps_pose (cbEU5_facts g e CE POS) as (GF5 & N5 & B5 & A5 & A15 & F5 & I5 & NI5 & BN5 & ZB5).
    pose proof (cbEG_facts g e CE POS) as GP.
    cps_pose (cbED_fields g e CE POS) as (DN & DA2 & DA1 & DFT & DIU & DBN & DNI & DNM & DBC & DCC & DCCR).
    cps_pose (cbED_room g e CE POS) as (RNZ & RLV & ROOM).
    pose proof CX as CXL; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in CXL; cbv zeta in CXL;
    cps_destruct CXL as (XE0 & XE1 & XA10 & XA11 & XA20 & XA21 & XF0 & XF1 & _ & _ & _ & _ & ME & MA1 & MA2 & MF & _ & _ & LJ & _).
    unfold CB_STACK in STK. pose proof LO as LO'. bz_ceil; bz_params; unfold CEIL in LO'.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    (* [comment removed for export] *)
    eapply (S0_cb_H1 cx g e ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m sv is_last CX SEP IMG CE STK LO AL S0_blockSort Q);
      [exact POS| exact EM| exact AM| exact CM| exact MI| exact ST|].
    clear EM AM CM MI ST.
    intros sp' m1 J280 y0 y4 y5 y6 y9 y10 y11 y12 y13 y14 y15 y16 y27 y28 y29 y30 USP EH1 EH2 AM1 ER1 CM1 MI1 ST1 FR LFR SAV MU1 WM1.
    set (usp := bv_unsigned sp') in *.
    assert (USP1 : (CEIL <= usp)%Z) by (bz_ceil; bz_params; unfold CEIL; lia). assert (USP2 : (usp + 384 <= 18446744073709551616)%Z) by lia.
    assert (AL16 : (usp mod 16 = 0)%Z) by (rewrite USP; clear - AL SPR STK LO'; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    u8take FR FJ0 8%Z (usp + 8)%Z. u8take FR FW8 8%Z (usp + 16)%Z. rename FR into FJ16.
    name_bytes FJ0 J0 8%Z. name_bytes FJ16 J16 264%Z.
    cps_destruct (u8arr_C8s 1 s0segs _ _ _ FW8 ltac:(rewrite ?length_firstn, ?length_skipn; lia)) as (w8 & SL1).
    clear FW8. cbn [map] in SL1. clear LFR J280.
    assert (N1 : e_nblock (cbE1 e) = e_nblock e) by (rewrite E1; reflexivity).
    assert (IMGF : forall W, w_img_apartK (ci_hi S0C) W -> forall mm mm', cimg_mem S0C mm sv -> munch W mm mm' -> wmono s0segs mm mm' -> cimg_mem S0C mm' sv).
    { intros W AP mm mm' C MUx WMx. exact (cimg_transportK0 S0C W mm mm' sv eq_refl C MUx WMx AP). }
    pose proof IMG as IMG'. unfold cctx_img, img_apart, IMG_LO3 in IMG'. cbn [ci_hi S0C] in IMG'. cps_destruct IMG' as (IE & IA1 & IA2 & IFT & _).
    unfold ESTATE_SIZE, FTAB_WORDS in IE, IA1, IA2, IFT.
    pose proof SEP as SP; unfold cctx_sep, apart, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE in SP; cbv zeta in SP.
    cps_destruct SP as (AEA1 & AEA2 & AEF & _ & _ & AA12 & _ & _ & _ & AA2F & _).
    cps_destruct AM1 as (AR1 & AR2 & FTB). unfold FTAB_WORDS in AR1, AR2, FTB.
    (* [comment removed for export] *)
    set (P2 := fun mm => erest cx e mm /\ u8arr s0segs mm (c_A1 cx) (zb8 (e_arr1 (cbE1 e)) ARR1_SIZE) /\ u32arr s0segs mm (c_FT cx) (zw32 (e_ftab (cbE1 e)) 65537) /\
                         cimg_mem S0C mm sv /\ u8arr s0segs mm usp J0 /\ rw_cells s0segs mm (usp + 8) [C8 w8] /\ u8arr s0segs mm (usp + 16) J16 /\
                         rw_cells s0segs mm (usp + 280) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    assert (PT2 : forall mm mm', P2 mm -> munch (cbH_W cx) mm mm' -> wmono s0segs mm mm' -> P2 mm').
    { (intros mm mm'; cps_intros (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8); intros MUx WMx). unfold P2.
      split; [eapply erest_transport0; [exact Q1| exact MUx| exact WMx| exact CX| |]; unfold cbH_W, ESTATE_SIZE; cbv [disjoint_from fst snd]; repeat split; try exact I; lia|].
      split; [eapply u8arr_transport; [exact Q2| exact MUx| exact WMx| rewrite zb8_length by lia; unfold cbH_W; cbv [disjoint_from fst snd]; repeat split; try exact I; lia]|].
      split; [eapply u32arr_transport; [exact Q3| exact MUx| exact WMx| rewrite zw32_length by lia; unfold cbH_W; cbv [disjoint_from fst snd]; repeat split; try exact I; lia]|].
      split; [eapply (IMGF (cbH_W cx)); [| exact Q4| exact MUx| exact WMx]; unfold cbH_W;
             repeat (constructor; [cbn [fst snd ci_hi S0C]; unfold IMG_LO3; lia|]); constructor|].
      split; [eapply cbH_W_hi8; [exact CX| | exact Q5| exact MUx| exact WMx]; lia|].
      split; [eapply cbH_W_hi; [exact CX| | exact Q6| exact MUx| exact WMx]; lia|].
      split; [eapply cbH_W_hi8; [exact CX| | exact Q7| exact MUx| exact WMx]; lia|].
      eapply cbH_W_hi; [exact CX| | exact Q8| exact MUx| exact WMx]; lia. }
    assert (HP2 : P2 m1) by (unfold P2; repeat (split; [assumption|]); assumption).
    eapply (S0_cb_H2 cx (g1 g) (cbE1 e) sp' gp tp F fc CX SEP ltac:(rewrite N1; lia) P2 PT2 Q m1 lo);
      [ rewrite E1; reflexivity
      | rewrite E1; cbn [e_blockNo]; exact BNR
      | rewrite E1; cbn [e_blockNo e_bw g_bs g1]; destruct ALT as [A|(GB & BOK)]; [left; exact A| right; split; [exact GB| apply bw_ok_reset; exact BOK]]
      | rewrite N1; lia
      | exact EH1 | exact EH2 | exact AR2 | exact MI1 | exact ST1 | exact LO | exact HP2 | ].
    clear EH1 EH2 AR2 MI1 ST1 HP2 ER1 CM1 AR1 FTB FJ0 SL1 FJ16 SAV.
    intros m2 zra zt0 zt1 zt2 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6. cbv zeta. intros EH1 EH2 AR2 MI2 ST2 HP2 MU2 WM2 OKS2 NS2.
    cps_destruct HP2 as (ER & AR1 & FTB & CM2 & FJ0 & SL1 & FJ16 & SAV).
    (* [comment removed for export] *)
    replace (Z_to_bv 64 (e_nblock (cbE1 e))) with (Z_to_bv 64 (e_nblock e)) by (rewrite N1; reflexivity).
    wstep; if_cases Kc; [apply blez_taken in Kc; [exfalso; lia| bz_params; lia] | clear Kc].
    (* [comment removed for export] *)
    set (P3 := fun mm => erest cx e mm /\ u8arr s0segs mm (c_A1 cx) (zb8 (e_arr1 (cbE1 e)) ARR1_SIZE) /\ u32arr s0segs mm (c_FT cx) (zw32 (e_ftab (cbE1 e)) 65537) /\
                         cimg_mem S0C mm sv /\ u8arr s0segs mm usp J0 /\ u8arr s0segs mm (usp + 16) J16 /\
                         rw_cells s0segs mm (usp + 280) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    assert (PT3 : forall mm mm', P3 mm -> munch (((usp + 8)%Z, (usp + 16)%Z) :: cbH_W cx) mm mm' -> wmono s0segs mm mm' -> P3 mm').
    { (intros mm mm'; cps_intros (Q1 & Q2 & Q3 & Q4 & Q5 & Q7 & Q8); intros MUx WMx). unfold P3.
      split; [eapply erest_transport0; [exact Q1| exact MUx| exact WMx| exact CX| |]; unfold cbH_W, ESTATE_SIZE; cbv [disjoint_from fst snd]; repeat split; try exact I; lia|].
      split; [eapply u8arr_transport; [exact Q2| exact MUx| exact WMx| rewrite zb8_length by lia; unfold cbH_W; cbv [disjoint_from fst snd]; repeat split; try exact I; lia]|].
      split; [eapply u32arr_transport; [exact Q3| exact MUx| exact WMx| rewrite zw32_length by lia; unfold cbH_W; cbv [disjoint_from fst snd]; repeat split; try exact I; lia]|].
      split; [eapply (IMGF (((usp + 8)%Z, (usp + 16)%Z) :: cbH_W cx)); [| exact Q4| exact MUx| exact WMx]; unfold cbH_W;
             repeat (constructor; [cbn [fst snd ci_hi S0C]; unfold IMG_LO3; lia|]); constructor|].
      assert (D8 : forall A n, (usp + 16 <= A)%Z \/ (A + n <= usp + 8)%Z -> (0 <= n)%Z -> (CEIL <= A)%Z -> disjoint_from (((usp + 8)%Z, (usp + 16)%Z) :: cbH_W cx) A n).
      { intros A n HA Hn HC. bz_ceil; bz_params; unfold cbH_W, CEIL in *. cbv [disjoint_from fst snd]. repeat split; try exact I; lia. }
      split; [eapply u8arr_transport; [exact Q5| exact MUx| exact WMx| apply D8; bz_ceil; bz_params; unfold CEIL; lia]|].
      split; [eapply u8arr_transport; [exact Q7| exact MUx| exact WMx| apply D8; bz_ceil; bz_params; unfold CEIL; lia]|].
      eapply rw_cells_transport; [exact Q8| exact MUx| exact WMx| apply D8; cbn; bz_ceil; bz_params; unfold CEIL; lia]. }
    assert (HP3 : P3 m2) by (unfold P3; repeat (split; [assumption|]); assumption).
    eapply (S0_cb_H3 cx (g3 cx (g1 g) (cbE1 e)) (cbE1 e) sp' gp tp F fc CX SEP eq_refl eq_refl eq_refl ltac:(rewrite N1; lia) USP1 USP2 P3 PT3 Q (cb_hdr (cbE1 e)) m2 lo);
      [ exact OKS2 | rewrite N1; bz_params; lia | exact BCH | exact OPH | rewrite N1; exact POS
      | unfold EH1b; exact EH1 | unfold EH2b; exact EH2 | unfold AR2b; exact AR2 | exact MI2 | exact ST2 | exact LO | exact SL1 | exact HP3 | ].
    clear EH1 EH2 AR2 MI2 ST2 HP3 ER AR1 FTB CM2 FJ0 SL1 FJ16 SAV.
    intros m3 yra3 yt1 yt2 yt3 yt4 yt5 yt6. cbv zeta. intros EH1 EH2 AR2 MI3 ST3 SL1 HP3 MU3 WM3 OKH3 NH3.
    cps_destruct HP3 as (ER & AR1 & FTB & CM3 & FJ0 & FJ16 & SAV).
    unfold EH2b, AR2b in EH2, AR2.
    (* [comment removed for export] *)
    pose proof GP as GP'. unfold gm_post in GP'. cbv zeta in GP'.
    cps_destruct GP' as (_ & _ & _ & _ & _ & _ & _ & _ & GNB & GA2 & GIU & GBW & GFT & _).
    cps_destruct (erest_fields g e CE POS) as (XIU & XUS & XMF & XSL & XSM & XLN & XCD & XRF & XLP & XA1 & XFT & _ & _).
    assert (NBU : (1 <= e_nblock (cbEU5 e) <= (NBLOCKMAX + 9))%Z) by (rewrite N5; lia).
    pose proof (smA_facts_intro (cbEU5 e) (cbEG e) GP NBU) as SFA.
    pose proof (smB_facts_intro (cbEU5 e) (cbEG e) znew znew znew znew znew GP NBU) as SFB.
    pose proof (sd_facts_intro (cbEU5 e) (cbEG e) znew znew znew znew znew znew GP NBU ltac:(rewrite I5; exact DEFR) ltac:(rewrite I5; exact IU)) as SDF.
    (* [comment removed for export] *)
    cps_destruct ER as (INU & UNS & MTF & SEL & SLM & LEN & COD & RFQ & LNP).
    rewrite N1 in AR2.
    eapply (S0_cb_U cx (g3 cx (g1 g) (cbE1 e)) (cbEU5 e) sp' gp tp F fc CX SEP eq_refl eq_refl ltac:(rewrite N5; lia) USP1 USP2 IMG
              (cbEG e) sv lo eq_refl GNB GF5 SFA SFB SDF Q m3 J0 J16);
      [ | | exact CM3 | exact MI3 | exact ST3 | lia | exact LO | exact AL16
      | exact FJ0 | lia | exact SL1 | exact FJ16 | lia | exact SAV
      | rewrite GBW, B5; exact OKH | rewrite GNB, N5; unfold cbED in ROOM; lia | | ].
    { (* [comment removed for export] *)
      split; [| split; [rewrite XIU; exact INU| split; [rewrite XUS; exact UNS| split; [exact EH2| split; [rewrite XMF; exact MTF| split; [rewrite XSL; exact SEL|
             split; [rewrite XSM; exact SLM| split; [rewrite XLN; exact LEN| split; [rewrite XCD; exact COD| split; [rewrite XRF; exact RFQ| rewrite XLP; exact LNP]]]]]]]]]].
      revert EH1. unfold EHEAD1n, EHEAD1, cbEU5, cbBH, cbBS, est_set_arr2, est_set_bw. cbn_est. cbn [removelast app]. intros EH1. exact EH1. }
    { (* [comment removed for export] *)
      split; [rewrite XA1; exact AR1| split; [| rewrite XFT; exact FTB]]. rewrite A5. unfold cbZBL, cbBH, cbBS. exact AR2. }
    { (* [comment removed for export] *)
      rewrite GA2, GNB, GBW, A5, N5, B5. unfold cbZBL. apply zb8_zbl_absorb. cps_destruct OKH as (_ & _ & O3). split; [exact O3| apply Z.le_refl]. }
    clear EH1 EH2 AR2 MI3 ST3 CM3 FJ0 SL1 FJ16 SAV INU UNS MTF SEL SLM LEN COD RFQ LNP AR1 FTB.
    intros m5 J16' ura ut0 ut1 ut2 us1 ua0 ua1 ua2 ua3 ua4 ua5 ua6 ua7 us2 us3 us4 us5 us6 us7 us8 us9 us10 us11 ut3 ut4 ut5 ut6.
    intros EH1 EH2 AR2 AR1 FTB INU UNS MTF SEL SLM LEN COD RFQ LNP CM5 MI5 ST5 FJ0 SL1 FJ16 LJ16' SAV MU5 WM5 BWD.
    (* [comment removed for export] *)
    unfold Q, compressBlock_post. cbv zeta. rewrite (cb_final_eq cb_glue_gm_ok g e is_last CE POS). unfold cbEF, cbBT, cbED.
    unfold cbED in RNZ, RLV, ROOM, DCCR.
    clear SFA SFB SDF GP GF5 DN DA2 DA1 DFT DIU DBN DNI DNM DBC DCC GIU GFT.
    revert EH1 EH2 AR2 AR1 FTB INU UNS MTF SEL SLM LEN COD RFQ LNP BWD GNB GA2 GBW RNZ RLV ROOM DCCR.
    generalize (cbEG e) as X. intros X EH1 EH2 AR2 AR1 FTB INU UNS MTF SEL SLM LEN COD RFQ LNP BWD GNB GA2 GBW RNZ RLV ROOM DCCR.
    set (eC := est_C X znew znew znew znew znew znew) in *. set (eD := est_D X znew znew znew znew znew znew znew) in *.
    set (g4 := g_mtf_on (g3 cx (g1 g) (cbE1 e))) in *.
    eapply (S0_cb_t0 cx g4 eC sp' gp tp F fc CX SEP eq_refl USP1 _ (e_bw eD) m5); [unfold EH2b; exact EH2| exact SL1|].
    assert (NC : e_nblock eC = e_nblock e) by (unfold eC; rewrite est_C_nblock, GNB; exact N5).
    assert (Gzb4 : g_zbits g4 = Z_to_bv 64 (c_A2 cx + e_nblock eC)) by (rewrite NC, <- N1; reflexivity).
    assert (HnbC : (0 <= e_nblock eC)%Z) by (rewrite NC; lia).
    set (P6 := fun mm => u8arr s0segs mm (c_A1 cx) (zb8 (e_arr1 X) ARR1_SIZE) /\ u32arr s0segs mm (c_FT cx) (zw32 (e_ftab X) FTAB_WORDS) /\
                         u8arr s0segs mm (c_E cx + 128) (ovb (e_inUse X) (jseg (c_J cx) 128 256) 256) /\
                         u8arr s0segs mm (c_E cx + 384) (ovb (e_unseqToSeq X) (jseg (c_J cx) 384 256) 256) /\
                         u32arr s0segs mm (c_E cx + 672) (ovw (e_mtfFreq X) (jseg (c_J cx) 672 1032) 258) /\
                         u8arr s0segs mm (c_E cx + 1704) (ovb (it_sel (smB_it X znew znew znew znew znew)) (jseg (c_J cx) 1704 18002) 18002) /\
                         u8arr s0segs mm (c_E cx + 19706) (ovb (snd (smC_pm X znew znew znew znew znew znew)) (jseg (c_J cx) 19706 18002) 18002) /\
                         u8arr s0segs mm (c_E cx + 37708) (ovb (it_len (smB_it X znew znew znew znew znew)) (jseg (c_J cx) 37708 1548) 1548) /\
                         u32arr s0segs mm (c_E cx + 39256) (ovw (smC_code X znew znew znew znew znew) (jseg (c_J cx) 39256 6192) 1548) /\
                         u32arr s0segs mm (c_E cx + 45448) (ovw (it_rfreq (smB_it X znew znew znew znew znew)) (jseg (c_J cx) 45448 6192) 1548) /\
                         u32arr s0segs mm (c_E cx + 51640) (ovw (it_lp (smB_it X znew znew znew znew znew)) (jseg (c_J cx) 51640 4128) 1032) /\
                         cimg_mem S0C mm sv /\ u8arr s0segs mm usp J0 /\
                         rw_cells s0segs mm (usp + 8) [C8 (Z_to_bv 64 (if is_last then 1 else 0))] /\ u8arr s0segs mm (usp + 16) J16').
    assert (PT6 : forall mm mm', P6 mm -> munch (cbT_W cx) mm mm' -> wmono s0segs mm mm' -> P6 mm').
    { (intros mm mm'; cps_intros (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15); intros MUx WMx). unfold P6.
      assert (DE : forall A n, (c_E cx + 128 <= A)%Z -> (A + n <= c_E cx + 640 \/ c_E cx + 648 <= A)%Z -> (A + n <= c_E cx + 55768)%Z -> (0 <= n)%Z -> disjoint_from (cbT_W cx) A n).
      { intros A n H1 H2 H3 H4. clear - H1 H2 H3 AEA2. unfold cbT_W. cbv [disjoint_from fst snd]. repeat split; try exact I; lia. }
      assert (DS : forall A n, (usp <= A)%Z -> (0 <= n)%Z -> disjoint_from (cbT_W cx) A n).
      { intros A n H1 H2. bz_ceil; bz_params; unfold cbT_W, CEIL in *. cbv [disjoint_from fst snd]. repeat split; try exact I; lia. }
      pose proof (jseg_length (c_J cx) 128 256 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ1.
      pose proof (jseg_length (c_J cx) 384 256 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ2.
      pose proof (jseg_length (c_J cx) 672 1032 ltac:(lia) ltac:(lia) ltac:(lia)) as LJm.
      pose proof (jseg_length (c_J cx) 1704 18002 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ4.
      pose proof (jseg_length (c_J cx) 19706 18002 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ5.
      pose proof (jseg_length (c_J cx) 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ6.
      pose proof (jseg_length (c_J cx) 39256 6192 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ7.
      pose proof (jseg_length (c_J cx) 45448 6192 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ8.
      pose proof (jseg_length (c_J cx) 51640 4128 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ9.
      split; [eapply u8arr_transport; [exact Q1| exact MUx| exact WMx| rewrite zb8_length by (bz_params; lia); unfold cbT_W; cbv [disjoint_from fst snd]; repeat split; try exact I; lia]|].
      split; [eapply u32arr_transport; [exact Q2| exact MUx| exact WMx| rewrite zw32_length by (unfold FTAB_WORDS; lia); unfold cbT_W, FTAB_WORDS; cbv [disjoint_from fst snd]; repeat split; try exact I; lia]|].
      split; [eapply u8arr_transport; [exact Q3| exact MUx| exact WMx| rewrite ovb_length by lia; apply DE; lia]|].
      split; [eapply u8arr_transport; [exact Q4| exact MUx| exact WMx| rewrite ovb_length by lia; apply DE; lia]|].
      split; [eapply u32arr_transport; [exact Q5| exact MUx| exact WMx| rewrite ovw_length by lia; apply DE; lia]|].
      split; [eapply u8arr_transport; [exact Q6| exact MUx| exact WMx| rewrite ovb_length by lia; apply DE; lia]|].
      split; [eapply u8arr_transport; [exact Q7| exact MUx| exact WMx| rewrite ovb_length by lia; apply DE; lia]|].
      split; [eapply u8arr_transport; [exact Q8| exact MUx| exact WMx| rewrite ovb_length by lia; apply DE; lia]|].
      split; [eapply u32arr_transport; [exact Q9| exact MUx| exact WMx| rewrite ovw_length by lia; apply DE; lia]|].
      split; [eapply u32arr_transport; [exact Q10| exact MUx| exact WMx| rewrite ovw_length by lia; apply DE; lia]|].
      split; [eapply u32arr_transport; [exact Q11| exact MUx| exact WMx| rewrite ovw_length by lia; apply DE; lia]|].
      split; [eapply (IMGF (cbT_W cx)); [| exact Q12| exact MUx| exact WMx]; unfold cbT_W;
             repeat (constructor; [cbn [fst snd ci_hi S0C]; unfold IMG_LO3; lia|]); constructor|].
      split; [eapply u8arr_transport; [exact Q13| exact MUx| exact WMx| apply DS; lia]|].
      split; [eapply rw_cells_transport; [exact Q14| exact MUx| exact WMx| apply DS; cbn; lia]|].
      eapply u8arr_transport; [exact Q15| exact MUx| exact WMx| apply DS; lia]. }
    assert (HP6 : P6 m5) by (unfold P6; repeat (split; [assumption|]); assumption).
    assert (ROOMT : (e_nblock eC + bw_numZ (e_bw eD) + 40 <= ARR2_SIZE)%Z) by (rewrite NC; revert ROOM; clear; unfold eD; generalize (est_D X znew znew znew znew znew znew znew) as y; bz_params; intros; lia).
    assert (CCR' : (0 <= e_combinedCRC eC < 4294967296)%Z).
    { unfold eC; rewrite est_C_combinedCRC. pose proof (est_D_fields X znew znew znew znew znew znew znew) as DF; cbv zeta in DF.
      cps_destruct DF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D16 & _). rewrite <- D16. exact DCCR. }
    eapply (S0_cb_tail cx g4 eC sp' gp tp F fc CX SEP eq_refl Gzb4 HnbC USP1 P6 PT6 _ is_last (e_bw eD) m5 lo);
      [ exact BWD | exact ROOMT | exact CCR' | unfold EH1b; exact EH1 | unfold EH2b; exact EH2
      | unfold AR2b; rewrite <- (est_C_arr2 X znew znew znew znew znew znew), <- (est_C_nblock X znew znew znew znew znew znew) in AR2; exact AR2
      | exact MI5 | exact ST5 | exact LO | exact SAV | exact HP6 | ].
    clear EH1 EH2 AR2 MI5 ST5 SAV HP6 AR1 FTB INU UNS MTF SEL SLM LEN COD RFQ LNP CM5 FJ0 SL1 FJ16.
    intros m6 vt0 vt1 vt2 va0 va1 va2 va3 va4 va5 va6 va7 vt3 vt4 vt5 vt6. cbv zeta. intros EH1 EH2 AR2 MI6 ST6 SAV HP6 MU6 WM6 NZ6.
    (* [comment removed for export] *)
    cps_destruct HP6 as (AR1 & FTB & INU & UNS & MTF & SEL & SLM & LEN & COD & RFQ & LNP & CM6 & FJ0 & SL1 & FJ16).
    pose proof (est_D_fields X znew znew znew znew znew znew znew) as DF; cbv zeta in DF.
    cps_destruct DF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D16 & _).
    (* [comment removed for export] *)
    unfold eC, eD in *. unfold EH1b, EH2b, AR2b in EH1, EH2, AR2.
    rewrite est_C_combinedCRC in EH1, EH2, AR2, NZ6. rewrite est_C_arr2, est_C_nblock in AR2. rewrite D16.
    set (bT := cb_trailer is_last (e_bw (est_D X znew znew znew znew znew znew znew)) (e_combinedCRC X)) in *.
    apply evt_done.
    subst usp. replace (Z_to_bv 64 (bv_unsigned sp' + 384)) with sp by (rewrite USP; replace (bv_unsigned sp - 384 + 384)%Z with (bv_unsigned sp) by lia; symmetry; apply Z_to_bv_bv_unsigned).
    do 16 eexists. split; [reflexivity|].
    split.
    { (* [comment removed for export] *)
      unfold compressBlock_W, CB_STACK, ESTATE_SIZE, FTAB_WORDS.
      eapply munch_trans; [exact MU1|].
      eapply munch_trans; [eapply munch_weaken; [| exact MU2]; unfold cbH_W; sub_fp_tac|].
      eapply munch_trans; [eapply munch_weaken; [| exact MU3]; unfold cbH_W; sub_fp_tac|].
      eapply munch_trans; [eapply munch_weaken; [| exact MU5]; unfold cbU_W, ESTATE_SIZE; sub_fp_tac|].
      eapply munch_weaken; [| exact MU6]. unfold cbT_W; sub_fp_tac. }
    split; [exact (wmono_trans s0segs _ _ _ WM1 (wmono_trans s0segs _ _ _ WM2 (wmono_trans s0segs _ _ _ WM3 (wmono_trans s0segs _ _ _ WM5 WM6))))|].
    split; [exact MI6|].
    split.
    { (* [comment removed for export] *)
      pose proof ST6 as ST.
      pose proof (stk_of_u8arr s0segs _ _ _ FJ0) as K0. stk_add ST K0.
      pose proof (stk_of_rw_cells s0segs _ _ _ SL1) as K1. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in K1. stk_add ST K1.
      pose proof (stk_of_u8arr s0segs _ _ _ FJ16) as K4. stk_add ST K4.
      pose proof (stk_of_rw_cells s0segs _ _ _ SAV) as K11. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in K11. stk_add ST K11.
      lazymatch type of ST with stk _ _ _ ?hi => replace hi with (bv_unsigned sp) in ST by lia end. exact ST. }
    (* [comment removed for export] *)
    unfold emem, amem, est_set_arr2, est_set_bw.
    cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse
         e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code e_rfreq e_len_pack est_D est_C].
    fold bT.
    assert (HE : forall (cs cs' : list cell) A, cs = cs' -> rw_cells s0segs m6 A cs' -> rw_cells s0segs m6 A cs) by (intros cs cs' A -> H; exact H).
    split.
    { split.
      { eapply HE; [| exact EH1]. unfold EHEAD1, eg_after_cb, g4, g3, g1, g_mtf_on.
        cbn [g_aie g_sort g_mtf g_bs g_zbits e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse
             e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code e_rfreq e_len_pack est_D est_C].
        replace (0 <? e_nblock e) with true by (symmetry; apply Z.ltb_lt; exact POS). rewrite ?Bool.orb_true_r. rewrite N1. reflexivity. }
      split; [exact INU|]. split; [exact UNS|].
      split.
      { eapply HE; [| exact EH2]. unfold EHEAD2, eg_after_cb, g4, g3, g1, g_mtf_on.
        cbn [g_aie g_sort g_mtf g_bs g_zbits e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse
             e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code e_rfreq e_len_pack est_D est_C].
        replace (0 <? e_nblock e) with true by (symmetry; apply Z.ltb_lt; exact POS). rewrite ?Bool.orb_true_r. reflexivity. }
      split; [exact MTF|]. split; [exact SEL|]. split; [exact SLM|]. split; [exact LEN|]. split; [exact COD|]. split; [exact RFQ| exact LNP]. }
    split; [| exact CM6].
    split; [exact AR1|]. split; [| exact FTB].
    (* [comment removed for export] *)
    rewrite GA2, A5, GNB, N5 in AR2.
    rewrite (cbZBL_eq e (cbBH e)) in AR2. rewrite (cbZBL_eq e bT).
    assert (BND : (0 <= bw_numZ (cbBH e) <= bw_numZ bT)%Z).
    { revert RNZ NZ6 OKH. clear. generalize (e_bw (est_D X znew znew znew znew znew znew znew)) as bD. generalize bT as b2. generalize (cbBH e) as bH.
      (intros bH b2 bD RNZ NZ6; cps_intros (O1 & O2 & O3)). lia. }
    pose proof (zb8_zbl_absorb (e_arr2 (cbE1 e)) (e_nblock e) (cbBH e) bT ARR2_SIZE BND) as ZQ.
    rewrite <- ZQ. (* [comment removed for export] *)
    exact AR2.
  Qed.

  (* [comment removed for export] *)
  Lemma cbZ0_fields : forall e, e_nblock (cbZ0 e) = e_nblock e /\ e_combinedCRC (cbZ0 e) = e_combinedCRC e /\ e_arr2 (cbZ0 e) = e_arr2 e /\
    e_blockNo (cbZ0 e) = e_blockNo e /\ e_arr1 (cbZ0 e) = e_arr1 e /\ e_ftab (cbZ0 e) = e_ftab e.
  Proof. intros; repeat split; reflexivity. Qed.

  Lemma S0_cb_zero : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cx : cctx) (g : eg) (e : est) (is_last : bool) (lo : Z) (sv : word),
    e_nblock e = 0%Z ->
    a0 = Z_to_bv 64 (c_E cx) -> a1 = Z_to_bv 64 (if is_last then 1 else 0) ->
    emem cx s0segs g e m -> amem cx s0segs e m -> cimg_mem S0C m sv -> mem_inv s0segs m ->
    stk s0segs m lo (bv_unsigned sp) -> (lo + CB_STACK <= bv_unsigned sp)%Z -> (CEIL <= lo)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
    cctx_ok cx -> cctx_sep cx -> cctx_img S0C cx -> cb_pre g e -> cb_facts e ->
    evt s0segs (compressBlock_post s0segs S0C cx g e is_last sv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (compressBlock_W cx (bv_unsigned sp)) m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x16344) fc None m (seg_rom s0segs)).
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cx g e is_last lo sv.
    intros Z0 -> -> EM AM CM MI ST STK LO AL CX SEP IMG PRE CF.
    pose proof (conj PRE CF : cb_entry g e) as CE.
    set (Q := compressBlock_post s0segs S0C cx g e is_last sv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (compressBlock_W cx (bv_unsigned sp)) m).
    cps_pose (cb_entry_facts g e CE) as (EOK & NBR & DEFR & IU & OP0 & NZ0 & BN1 & ALT).
    cps_pose EOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BCR & CCR & BNR). bz_params.
    cps_pose (cbZ_facts g e CE ltac:(lia)) as (OKS & NS & _ & _ & _ & _ & _ & CCR2 & _).
    cps_destruct (cbZ0_fields e) as (ZN & ZC & ZA2 & ZB & ZA1 & ZF).
    pose proof CX as CXL; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in CXL; cbv zeta in CXL;
    cps_destruct CXL as (XE0 & XE1 & XA10 & XA11 & XA20 & XA21 & XF0 & XF1 & _ & _ & _ & _ & ME & MA1 & MA2 & MF & _ & _ & LJ & _). clear ME MA1 MA2 MF.
    unfold CB_STACK in STK. pose proof LO as LO'. bz_ceil; bz_params; unfold CEIL in LO'.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    (* [comment removed for export] *)
    eapply (S0_cb_H1z cx g e ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m sv is_last CX STK LO Q);
      [exact Z0| exact EM| exact AM| exact CM| exact MI| exact ST|].
    clear EM AM CM MI ST.
    intros sp' m1 J280 y4 y5 y6 y9 y10 y11 y12 y13 y14 y15 y16 y27 y28 y29 y30 USP EH1 EH2 AM1 ER1 CM1 MI1 ST1 FR LFR SAV MU1 WM1.
    set (usp := bv_unsigned sp') in *.
    assert (USP1 : (CEIL <= usp)%Z) by (bz_ceil; bz_params; unfold CEIL; lia). assert (USP2 : (usp + 384 <= 18446744073709551616)%Z) by lia.
    assert (IMGF : forall W, w_img_apartK (ci_hi S0C) W -> forall mm mm', cimg_mem S0C mm sv -> munch W mm mm' -> wmono s0segs mm mm' -> cimg_mem S0C mm' sv).
    { intros W AP mm mm' C MUx WMx. exact (cimg_transportK0 S0C W mm mm' sv eq_refl C MUx WMx AP). }
    pose proof IMG as IMG'. unfold cctx_img, img_apart, IMG_LO3 in IMG'. cbn [ci_hi S0C] in IMG'. cps_destruct IMG' as (IE & IA1 & IA2 & IFT & _).
    unfold ESTATE_SIZE, FTAB_WORDS in IE, IA1, IA2, IFT.
    pose proof SEP as SP; unfold cctx_sep, apart, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE in SP; cbv zeta in SP.
    cps_destruct SP as (AEA1 & AEA2 & AEF & _ & _ & AA12 & _ & _ & _ & AA2F & _).
    cps_destruct AM1 as (AR1 & AR2 & FTB). unfold FTAB_WORDS in AR1, AR2, FTB.
    (* [comment removed for export] *)
    set (P2 := fun mm => erest cx e mm /\ u8arr s0segs mm (c_A1 cx) (zb8 (e_arr1 e) ARR1_SIZE) /\ u32arr s0segs mm (c_FT cx) (zw32 (e_ftab e) 65537) /\
                         cimg_mem S0C mm sv /\ u8arr s0segs mm usp J280 /\
                         rw_cells s0segs mm (usp + 280) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    assert (PT2 : forall mm mm', P2 mm -> munch (cbH_W cx) mm mm' -> wmono s0segs mm mm' -> P2 mm').
    { (intros mm mm'; cps_intros (Q1 & Q2 & Q3 & Q4 & Q5 & Q6); intros MUx WMx). unfold P2.
      split; [eapply erest_transport0; [exact Q1| exact MUx| exact WMx| exact CX| |]; unfold cbH_W, ESTATE_SIZE; cbv [disjoint_from fst snd]; repeat split; try exact I; lia|].
      split; [eapply u8arr_transport; [exact Q2| exact MUx| exact WMx| rewrite zb8_length by lia; unfold cbH_W; cbv [disjoint_from fst snd]; repeat split; try exact I; lia]|].
      split; [eapply u32arr_transport; [exact Q3| exact MUx| exact WMx| rewrite zw32_length by lia; unfold cbH_W; cbv [disjoint_from fst snd]; repeat split; try exact I; lia]|].
      split; [eapply (IMGF (cbH_W cx)); [| exact Q4| exact MUx| exact WMx]; unfold cbH_W;
             repeat (constructor; [cbn [fst snd ci_hi S0C]; unfold IMG_LO3; lia|]); constructor|].
      split; [eapply cbH_W_hi8; [exact CX| | exact Q5| exact MUx| exact WMx]; lia|].
      eapply cbH_W_hi; [exact CX| | exact Q6| exact MUx| exact WMx]; lia. }
    assert (HP2 : P2 m1) by (unfold P2; repeat (split; [assumption|]); assumption).
    assert (HD12 : EHEAD1 cx g (cbZ0 e) = EHEAD1 cx g e /\ EHEAD2 cx g (cbZ0 e) = EHEAD2 cx g e).
    { unfold EHEAD1, EHEAD2, cbZ0, est_set_bw. cbn_est. cbn [bw_numZ bw_buff bw_live]. split; reflexivity. }
    destruct HD12 as [HD1 HD2]. rewrite <- HD1 in EH1. rewrite <- HD2 in EH2. rewrite <- ZA2 in AR2.
    replace (Z_to_bv 64 (e_nblock e)) with (Z_to_bv 64 (e_nblock (cbZ0 e))) by (rewrite ZN; reflexivity).
    eapply (S0_cb_H2 cx g (cbZ0 e) sp' gp tp F fc CX SEP ltac:(rewrite ZN; lia) P2 PT2 Q m1 lo);
      [ unfold cbZ0, est_set_bw; cbn [e_bw bw_numZ]; exact NZ0
      | rewrite ZB; exact BNR
      | rewrite ZB; unfold cbZ0, est_set_bw; cbn [e_bw]; destruct ALT as [A|(GB & BOK)]; [left; exact A| right; split; [exact GB| cps_destruct BOK as (B1 & B2 & B3); unfold bw_ok; cbn [bw_buff bw_live bw_numZ]; lia]]
      | rewrite ZN; lia
      | exact EH1 | exact EH2 | exact AR2 | exact MI1 | exact ST1 | exact LO | exact HP2 | ].
    clear EH1 EH2 AR2 MI1 ST1 HP2 ER1 CM1 AR1 FTB FR SAV.
    intros m2 zra zt0 zt1 zt2 za0 za1 za2 za3 za4 za6 za7 zt3 zt4 zt5 zt6. cbv zeta. intros EH1 EH2 AR2 MI2 ST2 HP2 MU2 WM2 OKS2 NS2.
    cps_destruct HP2 as (ER & AR1 & FTB & CM2 & FR & SAV).
    (* [comment removed for export] *)
    replace (Z_to_bv 64 (e_nblock (cbZ0 e))) with (Z_to_bv 64 0) by (rewrite ZN, Z0; reflexivity).
    wstep; first [ if_cases Kc; [clear Kc | exfalso; revert Kc; vm_compute; discriminate] | idtac ].
    (* [comment removed for export] *)
    set (g3z := g3 cx g (cbZ0 e)) in *.
    set (P6 := fun mm => erest cx e mm /\ u8arr s0segs mm (c_A1 cx) (zb8 (e_arr1 e) ARR1_SIZE) /\ u32arr s0segs mm (c_FT cx) (zw32 (e_ftab e) 65537) /\
                         cimg_mem S0C mm sv /\ u8arr s0segs mm usp J280).
    assert (PT6 : forall mm mm', P6 mm -> munch (cbT_W cx) mm mm' -> wmono s0segs mm mm' -> P6 mm').
    { (intros mm mm'; cps_intros (Q1 & Q2 & Q3 & Q4 & Q5); intros MUx WMx). unfold P6.
      split; [eapply erest_transport0; [exact Q1| exact MUx| exact WMx| exact CX| |]; unfold cbT_W, ESTATE_SIZE; cbv [disjoint_from fst snd]; repeat split; try exact I; lia|].
      split; [eapply u8arr_transport; [exact Q2| exact MUx| exact WMx| rewrite zb8_length by lia; unfold cbT_W; cbv [disjoint_from fst snd]; repeat split; try exact I; lia]|].
      split; [eapply u32arr_transport; [exact Q3| exact MUx| exact WMx| rewrite zw32_length by lia; unfold cbT_W; cbv [disjoint_from fst snd]; repeat split; try exact I; lia]|].
      split; [eapply (IMGF (cbT_W cx)); [| exact Q4| exact MUx| exact WMx]; unfold cbT_W;
             repeat (constructor; [cbn [fst snd ci_hi S0C]; unfold IMG_LO3; lia|]); constructor|].
      eapply u8arr_transport; [exact Q5| exact MUx| exact WMx|]. bz_ceil; bz_params; unfold cbT_W, CEIL in *; cbv [disjoint_from fst snd]; repeat split; try exact I; lia. }
    assert (HP6 : P6 m2) by (unfold P6; repeat (split; [assumption|]); assumption).
    assert (ROOMT : (e_nblock (cbZ0 e) + bw_numZ (cbZS e) + 40 <= ARR2_SIZE)%Z) by (rewrite ZN, Z0; revert NS; clear; generalize (cbZS e) as y; bz_params; intros; lia).
    eapply (S0_cb_tail cx g3z (cbZ0 e) sp' gp tp F fc CX SEP eq_refl eq_refl ltac:(rewrite ZN; lia) USP1 P6 PT6 Q is_last (cbZS e) m2 lo);
      [ exact OKS | exact ROOMT | rewrite ZC; exact CCR | unfold EH1b; exact EH1 | unfold EH2b; exact EH2 | unfold AR2b; exact AR2
      | exact MI2 | exact ST2 | exact LO | exact SAV | exact HP6 | ].
    clear EH1 EH2 AR2 MI2 ST2 SAV HP6 ER AR1 FTB CM2 FR.
    intros m6 vt0 vt1 vt2 va0 va1 va2 va3 va4 va5 va6 va7 vt3 vt4 vt5 vt6. cbv zeta. intros EH1 EH2 AR2 MI6 ST6 SAV HP6 MU6 WM6 NZ6.
    (* [comment removed for export] *)
    cps_destruct HP6 as (ER & AR1 & FTB & CM6 & FR).
    unfold EH1b, EH2b, AR2b in EH1, EH2, AR2. rewrite ZC in EH1, EH2, AR2, NZ6. rewrite ZA2, ZN in AR2.
    set (bT := cb_trailer is_last (cbZS e) (e_combinedCRC e)) in *.
    unfold Q, compressBlock_post. apply evt_done. cbv zeta. rewrite (cb_final_eq0 e is_last ltac:(lia)). unfold cbZF, cbZT. fold bT.
    subst usp. replace (Z_to_bv 64 (bv_unsigned sp' + 384)) with sp by (rewrite USP; replace (bv_unsigned sp - 384 + 384)%Z with (bv_unsigned sp) by lia; symmetry; apply Z_to_bv_bv_unsigned).
    do 16 eexists. split; [reflexivity|].
    split.
    { unfold compressBlock_W, CB_STACK, ESTATE_SIZE, FTAB_WORDS.
      eapply munch_trans; [exact MU1|].
      eapply munch_trans; [eapply munch_weaken; [| exact MU2]; unfold cbH_W; sub_fp_tac|].
      eapply munch_weaken; [| exact MU6]. unfold cbT_W; sub_fp_tac. }
    split; [exact (wmono_trans s0segs _ _ _ WM1 (wmono_trans s0segs _ _ _ WM2 WM6))|].
    split; [exact MI6|].
    split.
    { pose proof ST6 as ST.
      pose proof (stk_of_u8arr s0segs _ _ _ FR) as K0. stk_add ST K0.
      pose proof (stk_of_rw_cells s0segs _ _ _ SAV) as K11. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in K11. stk_add ST K11.
      lazymatch type of ST with stk _ _ _ ?hi => replace hi with (bv_unsigned sp) in ST by lia end. exact ST. }
    cps_destruct ER as (INU & UNS & MTF & SEL & SLM & LEN & COD & RFQ & LNP).
    unfold emem, amem, est_set_arr2, est_set_bw.
    cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse
         e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code e_rfreq e_len_pack].
    assert (HE : forall (cs cs' : list cell) A, cs = cs' -> rw_cells s0segs m6 A cs' -> rw_cells s0segs m6 A cs) by (intros cs cs' A -> H; exact H).
    split.
    { split.
      { eapply HE; [| exact EH1]. unfold EHEAD1, eg_after_cb, g3z, g3, cbZ0, est_set_bw.
        cbn [g_aie g_sort g_mtf g_bs g_zbits e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse
             e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code e_rfreq e_len_pack].
        replace (0 <? e_nblock e) with false by (symmetry; apply Z.ltb_ge; lia). rewrite ?Bool.orb_false_r. reflexivity. }
      split; [exact INU|]. split; [exact UNS|].
      split.
      { eapply HE; [| exact EH2]. unfold EHEAD2, eg_after_cb, g3z, g3, cbZ0, est_set_bw.
        cbn [g_aie g_sort g_mtf g_bs g_zbits e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse
             e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code e_rfreq e_len_pack].
        replace (0 <? e_nblock e) with false by (symmetry; apply Z.ltb_ge; lia). rewrite ?Bool.orb_false_r. reflexivity. }
      split; [exact MTF|]. split; [exact SEL|]. split; [exact SLM|]. split; [exact LEN|]. split; [exact COD|]. split; [exact RFQ| exact LNP]. }
    split; [| exact CM6].
    split; [exact AR1|]. split; [exact AR2| exact FTB].
  Qed.
End ASSEMBLY.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem S0_compressBlock : compressBlock_spec cb_facts S0C.
Proof.
  unfold compressBlock_spec. cbn [ci_segs ci_compressBlock S0C]. intros until sv. intros Ha0 Ha1 EM AM CM MI ST STK LO AL CX SEP IMG PRE CF.
  destruct (Z.eq_dec (e_nblock e) 0) as [ZE|NE].
  - eapply S0_cb_zero; eassumption.
  - cps_pose PRE as (_ & NB & _). eapply S0_cb_pos; try eassumption. lia.
Qed.

End ACeilS2.
