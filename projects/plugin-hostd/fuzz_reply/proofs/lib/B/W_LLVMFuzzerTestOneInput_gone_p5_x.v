(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ARx-GENERIC twin of the composition of ARM_gone's phase p5 on image B
   (lib/B/W_LLVMFuzzerTestOneInput_gone_p5.v, a Theorem Labs lane's, fee5272ac13: the table-order loop, GT0 to GCSD, from the
   loop's steps of parts a and b), for the conversion of ARM_gone to the cut invariants of
   lib/B/W_LLVMFuzzerTestOneInput_cut_x.v.  _gone_p5.v is not edited.
   - the steps are taken from lib/B/W_LLVMFuzzerTestOneInput_gone_p5a_x.v / _p5b_x.v at this Section's variables
     (P5OH_x, P5IH_x, P5T_x, P5OT_x, gp5_t0_x, gp5_oh_x, gp5_ih_x, gp5_it_x, gp5_ot_x, gp5_c8_x, gp5_c3_x);
   - RESTATED under their names + _x, merged per item with SmallX's image-A twin
     lib/A/W_LLVMFuzzerTestOneInput_gone_p5_x.v (95a5de32ab2): the inner and outer loops gp5_inner_x / gp5_outer_x and
     the phase lemma gp5_t0_csd_x.
   Section hypotheses: as parts a and b.  Every ghost list is [] (cut_x's HP0). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface YCe5x YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_kit_xb W_journal_x W_frame_x W_contract_x W_sites_x W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_img_x.
(* W_LLVMFuzzerTestOneInput_gone_p5.v's own imports, AFTER the generic kit's: the converted proofs see the names they were written against *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require ListRep RelayRunT drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_gone_base W_LLVMFuzzerTestOneInput_gone_tk.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_gone_p5a W_LLVMFuzzerTestOneInput_gone_p5b.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_gone_base_x W_LLVMFuzzerTestOneInput_gone_tk_x W_LLVMFuzzerTestOneInput_gone_p5a_x W_LLVMFuzzerTestOneInput_gone_p5b_x W_LLVMFuzzerTestOneInput_gone_p5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* the zify flag as W_LLVMFuzzerTestOneInput_gone_p5.v's proofs see it (true: its imports' last setting), whatever a Required file leaves *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* @@ B-ONLY-HDR Local_Notation LLVMF_STK *)
Local Notation LLVMF_STK := YCfn.LLVMF_STK.

(* @@ SECTION gp5 *)
Section gp5.
(* @@ MERGED Context ctx:fx *)
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* @@ MERGED #[local]_Notation segs *)
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
(* @@ MERGED Variable B *)
Variable B : asyms.
(* @@ MERGED Variable MT *)
Variable MT : ameter_ops.
(* @@ MERGED Variables XM_LIB *)
Variables XM_LIB : Z -> Z.
(* @@ MERGED Variables RLO *)
Variables RLO RHI : Z.
(* @@ MERGED Variable fr_live_pre *)
Variable fr_live_pre : astate -> Prop.
(* @@ AX-ONLY Variables LIBROOM *)
Variables LIBROOM NP : astate -> Prop.
(* @@ MERGED Variable G_fr *)
Variable G_fr : list (Z * Z).
(* @@ MERGED Variable fr_FP *)
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
(* @@ AX-ONLY Variable PST *)
Variable PST : list (Z * Z).
(* @@ AX-ONLY Variable ARx *)
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
(* @@ AX-ONLY Context ctx:hl *)
Context {hl : Z}.
(* @@ MERGED Hypothesis LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx hl.
(* the instance's ghost poisoned-head set stays empty (a Theorem Labs lane's HP0 ruling): every ghost list of the walk is [] *)
(* @@ AX-ONLY Hypothesis HP0 *)
Hypothesis HP0 : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md -> Hp = [].
(* @@ MERGED Hypothesis HG *)
Hypothesis HG : gx_ok segs B G_fr.
(* @@ AX-ONLY Variable LSx *)
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
(* @@ MERGED Variable RINV *)
Variable RINV : lfcx -> Z -> lmod -> Prop.
(* @@ MERGED #[local]_Notation VAL *)
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
(* @@ MERGED #[local]_Notation BASE *)
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
(* @@ MERGED Hypothesis HGs *)
Hypothesis HGs : GN_HGs G_fr.
(* @@ MERGED Hypothesis HGcells *)
Hypothesis HGcells : GN_HGcells G_fr.
(* @@ MERGED Hypothesis HROMPIN *)
Hypothesis HROMPIN : GN_ROM_PIN B.
(* @@ MERGED Hypothesis HZS *)
Hypothesis HZS : GN_HZS B.
(* @@ MERGED Hypothesis HCE *)
Hypothesis HCE : GN_CELLS_ERRNO B.
(* @@ RESOLVED Hypothesis RIend *)
Hypothesis RIend : GN_RI_end B MT LSx RINV.
(* @@ MERGED Hypothesis GWL *)
Hypothesis GWL : glob_wr_law G_fr.
(* @@ B-ONLY-AR[errno_law] Hypothesis ERRL *)
Hypothesis ERRL : errno_law_x B ARx.
(* @@ RESOLVED Hypothesis HERR *)
Hypothesis HERR : GN_ERRNO_LOW B.
(* ---- the two callee texts and the loop's model obligation (A's p5 set: CNL, CSHE, RIstep, ML) ---- *)
(* @@ RESOLVED Variable MMAX *)
Variable MMAX : Z.
(* the room round: the room predicate the callees are taken at (RM := fun S _ => NP S at the instance) *)
Variable RP : roomp.
(* @@ CONFLICT Hypothesis CNL *)
Hypothesis CNL : GN_CNL_x B MT PST ARx MMAX RP.
(* @@ CONFLICT Hypothesis CSHE *)
Hypothesis CSHE : GN_CSHE_x B MT PST ARx RP.
(* @@ MERGED Hypothesis RIstep *)
Hypothesis RIstep : GN_RI_step B MT LSx RINV MMAX.
(* the room round (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (c) / (d)), as _gone_p3_x.v states them: RPNP (RM is NP at the instance), the arm's
   count row LSCNT (GN_LS_cnt_x, _gone_base_x.v) and its model count rule CNTSTEP (GN_CNT_step, _gone_base.v, at
   check_no_loss's premise peak cnl_pk, W_contract_x.v:378) *)
Variable gn_pk : lfcx -> lmod -> list (hsrc * nat) -> (Z -> bool) -> nat.
Hypothesis RPNP : forall S k, rp_RM RP S k <-> NP S.
Hypothesis LSCNT : GN_LS_cnt_x B LSx RINV RP gn_pk.
Hypothesis CNTSTEP : GN_CNT_step RINV gn_pk (fun h => cnl_pk (hs_expected h) (hs_held h)).
(* @@ RESOLVED Hypothesis ML *)
Hypothesis ML : ameter_laws MT.
(* parts a and b at this Section's variables *)
(* @@ UNANCHORED Hypothesis BLKN *)
Hypothesis BLKN : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* the image is off PST (add_x's HPST): the journal's image clause takes it; trivial at PST = [] *)
(* @@ UNANCHORED Hypothesis HPST *)
Hypothesis HPST : forall a, in_img segs a -> ~ Exists (in_zr a) PST.
(* W_frame_x.v:105's Section hypothesis FRMF, for frame_al64_x / shadow_hull_vis_of_frame_x *)
(* @@ UNANCHORED Hypothesis FRMF *)
Hypothesis FRMF : forall ly S Hp (W : world segs) mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  ly_F ly mod 4096 = 0 /\ fs_frame_off cid pos mod 64 = 0 /\ 64 <= fs_frame_bytes cid /\ fs_frame_bytes cid mod 64 = 0.
(* W_kit_x's IMGC, from the laws' image field *)
(* @@ UNANCHORED Let IMGC *)
Let IMGC := W_img_x.fr_img_cover_x B ARx LAWS.

(* ---------------------------------------------------------------- the walk at the empty ghost list *)
(* @@ UNANCHORED Local_Notation AR0 *)
Local Notation AR0 ly S W mem md := (ARx ly S [] W mem md).
(* @@ UNANCHORED Local_Notation AJ0 *)
Local Notation AJ0 G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_x segs B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
(* @@ UNANCHORED Local_Notation AJi0 *)
Local Notation AJi0 STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_x segs B PST ARx STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
(* @@ UNANCHORED Local_Notation AFN0 *)
Local Notation AFN0 STK ly S W regs mem md ch := (afn_pre_x segs B ARx STK ly S [] W regs mem md ch).
(* @@ UNANCHORED Local_Notation LFB0 *)
Local Notation LFB0 cx := (lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx []).
(* a ghost list read off an ARx fact, or off a journal's last state, is [] *)
(* @@ UNANCHORED Ltac hp0a *)
Ltac hp0a H := let E := fresh "EHp" in pose proof (HP0 _ _ _ _ _ _ H) as E;
  lazymatch type of E with ?h = [] => subst h end.
(* @@ UNANCHORED Ltac hp0g *)
Ltac hp0g HJ := let H := fresh "HARg" in
  pose proof (ajournal_gx_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as H; hp0a H; clear H.

(* ---- _gone_p5.v's AR-free items that take section arguments, cited with them ---- *)
(* @@ XALIAS Local_Notation P5OH *)
Local Notation P5OH_x := (W_LLVMFuzzerTestOneInput_gone_p5a_x.P5OH_x B MT NP G_fr fr_FP PST ARx LSx RINV).
(* @@ XALIAS Local_Notation P5IH *)
Local Notation P5IH_x := (W_LLVMFuzzerTestOneInput_gone_p5a_x.P5IH_x B MT NP G_fr fr_FP PST ARx LSx RINV).
(* @@ XALIAS Local_Notation P5T *)
Local Notation P5T_x := (W_LLVMFuzzerTestOneInput_gone_p5a_x.P5T_x B MT NP G_fr fr_FP PST ARx LSx RINV).
(* @@ XALIAS Local_Notation P5OT *)
Local Notation P5OT_x := (W_LLVMFuzzerTestOneInput_gone_p5a_x.P5OT_x B MT NP G_fr fr_FP PST ARx LSx RINV).
(* @@ XALIAS Local_Notation gp5_t0 *)
Local Notation gp5_t0_x := (W_LLVMFuzzerTestOneInput_gone_p5a_x.gp5_t0_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HG LSx RINV RIend HERR BLKN).
(* @@ XALIAS Local_Notation gp5_oh *)
Local Notation gp5_oh_x := (W_LLVMFuzzerTestOneInput_gone_p5a_x.gp5_oh_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HG LSx RINV).
(* @@ XALIAS Local_Notation gp5_ih *)
Local Notation gp5_ih_x := (W_LLVMFuzzerTestOneInput_gone_p5a_x.gp5_ih_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HP0 HG LSx RINV HZS BLKN).
(* @@ XALIAS Local_Notation gp5_it *)
Local Notation gp5_it_x := (W_LLVMFuzzerTestOneInput_gone_p5a_x.gp5_it_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HG LSx RINV).
(* @@ XALIAS Local_Notation gp5_ot *)
Local Notation gp5_ot_x := (W_LLVMFuzzerTestOneInput_gone_p5a_x.gp5_ot_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HG LSx RINV RIend).
(* @@ XALIAS Local_Notation gp5_c8 *)
Local Notation gp5_c8_x := (W_LLVMFuzzerTestOneInput_gone_p5b_x.gp5_c8_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HP0 HG LSx RINV HGs HGcells HROMPIN HZS GWL ERRL MMAX RP CNL RIstep gn_pk RPNP LSCNT CNTSTEP ML BLKN HPST).
(* @@ XALIAS Local_Notation gp5_c3 *)
Local Notation gp5_c3_x := (W_LLVMFuzzerTestOneInput_gone_p5b_x.gp5_c3_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HP0 HG LSx RINV HGs HGcells HROMPIN HZS HCE GWL ERRL RP CSHE RPNP ML BLKN HPST FRMF).
(* @@ MERGED Lemma gp5_inner *)
Lemma gp5_inner_x : forall n cx t m m1 i k W c, (k + n = 4)%nat ->
  LFB0 cx -> P5IH_x cx t m m1 i k W c ->
  SRr segs W c (P5OT_x cx t m m1 i).
Proof.
  induction n as [|n IH]; intros cx t m m1 i k W c Hn HB HI.
  - exfalso. destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hk & _). lia.
  - assert (AT : forall W1 c1, P5T_x cx t m m1 i k W1 c1 -> SRr segs W1 c1 (P5OT_x cx t m m1 i)).
    { intros W1 c1 HT. eapply SRr_bind; [exact (gp5_it_x cx t m m1 i k W1 c1 HB HT)|].
      intros W2 c2 _ [(Hlt & HI2) | (Heq & HO)].
      - exact (IH cx t m m1 i (S k) W2 c2 ltac:(lia) HB HI2).
      - apply SRr_ret. exact HO. }
    eapply SRr_bind; [exact (gp5_ih_x cx t m m1 i k W c HB HI)|].
    intros W1 c1 _ [HT | HC]; [exact (AT W1 c1 HT)|].
    eapply SRr_bind; [exact (gp5_c8_x cx t m m1 i k W1 c1 HB HC)|].
    intros W2 c2 _ HM.
    eapply SRr_bind; [exact (gp5_c3_x cx t m m1 i k W2 c2 HB HM)|].
    intros W3 c3 _ HT. exact (AT W3 c3 HT).
Qed.
(* the outer loop, from 0x84870 at entry i to 0x8494c *)
(* @@ MERGED Lemma gp5_outer *)
Lemma gp5_outer_x : forall n cx t m m1 i W c, (i + n = length (lm_es m1))%nat ->
  LFB0 cx -> P5OH_x cx t m m1 i W c ->
  SRr segs W c (fun W' c' => exists mc, GCSD_x B NP G_fr fr_FP PST ARx LSx RINV cx t m mc W' c').
Proof.
  induction n as [|n IH]; intros cx t m m1 i W c Hn HB HO.
  - exfalso. destruct HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hi & _). lia.
  - eapply SRr_bind; [exact (gp5_oh_x cx t m m1 i W c HB HO)|].
    intros W1 c1 _ HI.
    eapply SRr_bind; [exact (gp5_inner_x 4 cx t m m1 i 0 W1 c1 eq_refl HB HI)|].
    intros W2 c2 _ HOT.
    eapply SRr_bind; [exact (gp5_ot_x cx t m m1 i W2 c2 HB HOT)|].
    intros W3 c3 _ [(Hlt & HO3) | HG3].
    + exact (IH cx t m m1 (S i) W3 c3 ltac:(lia) HB HO3).
    + apply SRr_ret. exact HG3.
Qed.

(* ================================================================== GP5 over ARx *)
(* @@ MERGED Lemma gp5_t0_csd *)
Lemma gp5_t0_csd_x : forall cx t m m1 W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  GT0_x B MT NP G_fr fr_FP PST ARx LSx RINV cx t m m1 W c ->
  SRr segs W c (fun W' c' => exists mc, GCSD_x B NP G_fr fr_FP PST ARx LSx RINV cx t m mc W' c').
Proof.
  intros cx t m m1 W c HB HT.
  eapply SRr_bind; [exact (gp5_t0_x cx t m m1 W c HB HT)|].
  intros W1 c1 _ [(Hlt & HO) | HG1].
  - exact (gp5_outer_x (length (lm_es m1)) cx t m m1 0 W1 c1 eq_refl HB HO).
  - apply SRr_ret. exact HG1.
Qed.
(* @@ END gp5 *)
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the R twins of this phase over the R cut points of
   W_LLVMFuzzerTestOneInput_gone_base_x.v (Section gR), as SRrG walks with the G runs.  Strict text above
   unchanged. ---- *)
Section gp5R.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
(* check_no_loss / check_shape_ends at R, per slot: gone_base_x's GN_CNL_xR / GN_CSHE_xR *)
Hypothesis CNL_R : GN_CNL_xR B MT PST ARx MMAX RP R.
Hypothesis CSHE_R : GN_CSHE_xR B MT PST ARx RP R.
Local Notation P5OH_xR := (W_LLVMFuzzerTestOneInput_gone_p5a_x.P5OH_xR B MT NP G_fr fr_FP PST ARx LSx RINV R).
Local Notation P5IH_xR := (W_LLVMFuzzerTestOneInput_gone_p5a_x.P5IH_xR B MT NP G_fr fr_FP PST ARx LSx RINV R).
Local Notation P5T_xR := (W_LLVMFuzzerTestOneInput_gone_p5a_x.P5T_xR B MT NP G_fr fr_FP PST ARx LSx RINV R).
Local Notation P5OT_xR := (W_LLVMFuzzerTestOneInput_gone_p5a_x.P5OT_xR B MT NP G_fr fr_FP PST ARx LSx RINV R).
Local Notation gp5_t0_xR := (W_LLVMFuzzerTestOneInput_gone_p5a_x.gp5_t0_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HG LSx RINV RIend HERR BLKN R R_refl).
Local Notation gp5_oh_xR := (W_LLVMFuzzerTestOneInput_gone_p5a_x.gp5_oh_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HG LSx RINV R R_refl).
Local Notation gp5_ih_xR := (W_LLVMFuzzerTestOneInput_gone_p5a_x.gp5_ih_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HP0 HG LSx RINV HZS BLKN R R_refl).
Local Notation gp5_it_xR := (W_LLVMFuzzerTestOneInput_gone_p5a_x.gp5_it_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HG LSx RINV R R_refl).
Local Notation gp5_ot_xR := (W_LLVMFuzzerTestOneInput_gone_p5a_x.gp5_ot_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HG LSx RINV RIend R R_refl).
Local Notation gp5_c8_xR := (W_LLVMFuzzerTestOneInput_gone_p5b_x.gp5_c8_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HP0 HG LSx RINV HGs HGcells HROMPIN HZS GWL ERRL MMAX RP RIstep gn_pk RPNP LSCNT CNTSTEP ML BLKN HPST R R_refl R_trans CNL_R).
Local Notation gp5_c3_xR := (W_LLVMFuzzerTestOneInput_gone_p5b_x.gp5_c3_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HP0 HG LSx RINV HGs HGcells HROMPIN HZS HCE GWL ERRL RP RPNP ML BLKN HPST FRMF R R_refl R_trans CSHE_R).
Local Notation AJ0R G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_xR segs B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AJi0R STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_xR segs B PST ARx R STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).



Lemma gp5_inner_xR : forall n cx t m m1 i k W c, (k + n = 4)%nat ->
  LFB0 cx -> P5IH_xR cx t m m1 i k W c ->
  YA0nH.SRrG segs R W c (P5OT_xR cx t m m1 i).
Proof.
  induction n as [|n IH]; intros cx t m m1 i k W c Hn HB HI.
  - exfalso. destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hk & _). lia.
  - assert (AT : forall W1 c1, P5T_xR cx t m m1 i k W1 c1 -> YA0nH.SRrG segs R W1 c1 (P5OT_xR cx t m m1 i)).
    { intros W1 c1 HT. eapply (YA0nH.SRrG_bind _ R R_trans); [exact (gp5_it_xR cx t m m1 i k W1 c1 HB HT)|].
      intros W2 c2 _ [(Hlt & HI2) | (Heq & HO)].
      - exact (IH cx t m m1 i (S k) W2 c2 ltac:(lia) HB HI2).
      - apply (YA0nH.SRrG_ret _ R R_refl). exact HO. }
    eapply (YA0nH.SRrG_bind _ R R_trans); [exact (gp5_ih_xR cx t m m1 i k W c HB HI)|].
    intros W1 c1 _ [HT | HC]; [exact (AT W1 c1 HT)|].
    eapply (YA0nH.SRrG_bind _ R R_trans); [exact (gp5_c8_xR cx t m m1 i k W1 c1 HB HC)|].
    intros W2 c2 _ HM.
    eapply (YA0nH.SRrG_bind _ R R_trans); [exact (gp5_c3_xR cx t m m1 i k W2 c2 HB HM)|].
    intros W3 c3 _ HT. exact (AT W3 c3 HT).
Qed.

Lemma gp5_outer_xR : forall n cx t m m1 i W c, (i + n = length (lm_es m1))%nat ->
  LFB0 cx -> P5OH_xR cx t m m1 i W c ->
  YA0nH.SRrG segs R W c (fun W' c' => exists mc, GCSD_xR B NP G_fr fr_FP PST ARx LSx RINV R cx t m mc W' c').
Proof.
  induction n as [|n IH]; intros cx t m m1 i W c Hn HB HO.
  - exfalso. destruct HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hi & _). lia.
  - eapply (YA0nH.SRrG_bind _ R R_trans); [exact (gp5_oh_xR cx t m m1 i W c HB HO)|].
    intros W1 c1 _ HI.
    eapply (YA0nH.SRrG_bind _ R R_trans); [exact (gp5_inner_xR 4 cx t m m1 i 0 W1 c1 eq_refl HB HI)|].
    intros W2 c2 _ HOT.
    eapply (YA0nH.SRrG_bind _ R R_trans); [exact (gp5_ot_xR cx t m m1 i W2 c2 HB HOT)|].
    intros W3 c3 _ [(Hlt & HO3) | HG3].
    + exact (IH cx t m m1 (S i) W3 c3 ltac:(lia) HB HO3).
    + apply (YA0nH.SRrG_ret _ R R_refl). exact HG3.
Qed.

Lemma gp5_t0_csd_xR : forall cx t m m1 W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  GT0_xR B MT NP G_fr fr_FP PST ARx LSx RINV R cx t m m1 W c ->
  YA0nH.SRrG segs R W c (fun W' c' => exists mc, GCSD_xR B NP G_fr fr_FP PST ARx LSx RINV R cx t m mc W' c').
Proof.
  intros cx t m m1 W c HB HT.
  eapply (YA0nH.SRrG_bind _ R R_trans); [exact (gp5_t0_xR cx t m m1 W c HB HT)|].
  intros W1 c1 _ [(Hlt & HO) | HG1].
  - exact (gp5_outer_xR (length (lm_es m1)) cx t m m1 0 W1 c1 eq_refl HB HO).
  - apply (YA0nH.SRrG_ret _ R R_refl). exact HG1.
Qed.

End gp5R.

End gp5.

