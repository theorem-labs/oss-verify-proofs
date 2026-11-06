(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: KF-COUNT F3: P5M_x carries gn_cst, gn_runc; RIstep at that bound *)
(* Theorem Labs, 2026-10: the ARx-GENERIC twin of the second part of ARM_gone's phase p5 on image B
   (lib/B/W_LLVMFuzzerTestOneInput_gone_p5b.v, a Theorem Labs lane's, fee5272ac13: the two calls of the loop, check_no_loss at
   0x84bf8 and check_shape_ends), for the conversion of ARM_gone to the cut invariants of
   lib/B/W_LLVMFuzzerTestOneInput_cut_x.v.  _gone_p5b.v is not edited.
   - part a's names (_gone_p5a.v) are taken from lib/B/W_LLVMFuzzerTestOneInput_gone_p5a_x.v at this Section's
     variables where part a restates them (p5st_x, P5C_x, P5T_x, gp5_ly_x, gp5_xport_x, gp5_sep_step_x, ...), and from
     _gone_p5a.v where they read no AR (gp5_split, gp5_surv, gp5_regs_call);
   - RESTATED under their names + _x, merged per item with SmallX's image-A twin
     lib/A/W_LLVMFuzzerTestOneInput_gone_p5_x.v (95a5de32ab2): the loop's call state P5M_x, B's gp5_stk_rd_x (cnl_spec's
     readable-stack premise from the cut's STKR), and the two call steps gp5_c8_x / gp5_c3_x (the callees' contracts
     GN_CNL_x / GN_CSHE_x: the kit's cnl_spec_x / cshe_spec_x at each slot's G).
   Section hypotheses beyond cut_x's header: as part a's, and CNL / CSHE (base_x's GN_CNL_x / GN_CSHE_x), RIstep
   (LS -> LSx), ML, MMAX.  Every ghost list is [] (cut_x's HP0). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface YCe5x YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_kit_xb W_journal_x W_frame_x W_contract_x W_sites_x W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_img_x.
(* W_LLVMFuzzerTestOneInput_gone_p5b.v's own imports, AFTER the generic kit's: the converted proofs see the names they were written against *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_gone_p5a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_contract_xR_g6.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_gone_base_x W_LLVMFuzzerTestOneInput_gone_tk_x W_LLVMFuzzerTestOneInput_gone_p5a_x W_LLVMFuzzerTestOneInput_gone_p5b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* the zify flag as W_LLVMFuzzerTestOneInput_gone_p5b.v's proofs see it (true: its imports' last setting), whatever a Required file leaves *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* @@ B-ONLY-HDR Local_Notation LLVMF_STK *)
Local Notation LLVMF_STK := YCfn.LLVMF_STK.

(* @@ SECTION gp5b *)
Section gp5b.
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
(* part a's names at this Section's variables *)
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
(* @@ XALIAS Local_Notation p5st *)
Local Notation p5st_x := (W_LLVMFuzzerTestOneInput_gone_p5a_x.p5st_x B MT NP G_fr fr_FP PST ARx LSx RINV).
(* @@ XALIAS Local_Notation P5C *)
Local Notation P5C_x := (W_LLVMFuzzerTestOneInput_gone_p5a_x.P5C_x B MT NP G_fr fr_FP PST ARx LSx RINV).
(* @@ XALIAS Local_Notation P5T *)
Local Notation P5T_x := (W_LLVMFuzzerTestOneInput_gone_p5a_x.P5T_x B MT NP G_fr fr_FP PST ARx LSx RINV).
(* @@ XALIAS Local_Notation gp5_ly *)
Local Notation gp5_ly_x := (W_LLVMFuzzerTestOneInput_gone_p5a_x.gp5_ly_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx).
(* @@ XALIAS Local_Notation gp5_aout_pre *)
Local Notation gp5_aout_pre_x := (W_LLVMFuzzerTestOneInput_gone_p5a_x.gp5_aout_pre_x B ARx LAWS BLKN).
(* @@ XALIAS Local_Notation gp5_jk_AR *)
Local Notation gp5_jk_AR_x := (W_LLVMFuzzerTestOneInput_gone_p5a_x.gp5_jk_AR_x B PST ARx).
(* @@ XALIAS Local_Notation gp5_jk_pres *)
Local Notation gp5_jk_pres_x := (W_LLVMFuzzerTestOneInput_gone_p5a_x.gp5_jk_pres_x B PST ARx).
(* @@ XALIAS Local_Notation gp5_jk_faddr *)
Local Notation gp5_jk_faddr_x := (W_LLVMFuzzerTestOneInput_gone_p5a_x.gp5_jk_faddr_x B PST ARx).
(* @@ XALIAS Local_Notation gp5_split *)
Local Notation gp5_split := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_split B fr_FP).
(* @@ XALIAS Local_Notation gp5_surv *)
Local Notation gp5_surv := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_surv B).
(* @@ XALIAS Local_Notation gp5_xport *)
Local Notation gp5_xport_x := (W_LLVMFuzzerTestOneInput_gone_p5a_x.gp5_xport_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HG HGs HGcells HROMPIN GWL ERRL BLKN HPST).
(* @@ XALIAS Local_Notation gp5_sep_step *)
Local Notation gp5_sep_step_x := (W_LLVMFuzzerTestOneInput_gone_p5a_x.gp5_sep_step_x B G_fr fr_FP PST ARx LAWS BLKN).
(* @@ XALIAS Local_Notation gp5_rebuild *)
Local Notation gp5_rebuild_x := (W_LLVMFuzzerTestOneInput_gone_p5a_x.gp5_rebuild_x B NP G_fr fr_FP PST ARx).
Local Notation gp5_tie_step := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_tie_step B).
(* @@ XALIAS Local_Notation gp5_regs_call *)
Local Notation gp5_regs_call := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_regs_call B XM_LIB RLO).
(* @@ XALIAS Local_Notation gp5_held_low *)
Local Notation gp5_held_low_x := (W_LLVMFuzzerTestOneInput_gone_p5a_x.gp5_held_low_x B ARx LAWS BLKN).
(* @@ XALIAS Local_Notation gp5_ra_stack *)
Local Notation gp5_ra_stack_x := (W_LLVMFuzzerTestOneInput_gone_p5a_x.gp5_ra_stack_x B ARx LAWS).
(* @@ RESOLVED Let RUNTO *)
Let RUNTO := paj_run_to_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
(* @@ MERGED Ltac gp5_meq *)
Ltac gp5_meq HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.
(* @@ MERGED Ltac gp5_awr *)
Ltac gp5_awr := repeat (apply awr_ok_x_cons; [intros ?a ?Ha; cbn in Ha; lia|]); apply awr_ok_x_nil.
(* @@ MERGED Ltac gp5_inl *)
Ltac gp5_inl := cbn [In gn_cells]; repeat (first [left; reflexivity | right]).

(* ---- what a callee's journal keeps (W_gestures_end.v's gse_keep_* kit, for this file) ---- *)
(* @@ RESOLVED Definition P5M *)
Definition P5M_x (cx : lfcx) (t : Z) (m m1 : lmod) (i k : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S3 kk fpos mc A h h1 E' H' ly0 S0 cst0 q,
    c = cfg_at segs (fr_B0 + AF_gn_ret1) regs mem md /\
    gst_x B NP G_fr fr_FP PST ARx cx t (gn_kq cx m) (gn_set mc k h1) fake_shadow_open fpos ly S3 W mem md kk /\
    gdone RINV cx t m m1 /\ LSx cx t m ly0 S0 /\ mo_le MT S0 S3 cst0 /\ gn_tie B cx m ly0 S0 (gn_set mc k h1) ly S3 /\
    (* check_shape_ends' count premise at this state (the room round), from gp5_c8_x *)
    cnt_ok_pk RP cshe_pk (ablocks B ly S3) /\
    gn_run (gn_pre cx m) m1 mc A i k /\
    (* KF-COUNT: the loop's calls before this one cost q; cst0 is within relay_instance_gone's cost + q + this
       check_no_loss's cnl_cost *)
    gn_runc MT (gn_pre cx m) m1 mc A i k q /\ gn_cst MT cx m m1 (q + cnl_cost MT (hs_expected h) (hs_held h)) cst0 /\
    0 <= A /\ (k < 4)%nat /\ (i < length (lm_es m1))%nat /\
    nth k (lm_hs mc) None = Some h /\ hs_fd h = re_fd (nth i (lm_es m1) gn_e0) /\
    gn_cnl_ok h h1 E' H' /\
    Z.of_nat (length (lm_O mc)) < 2 ^ 32 /\
    hl_n (hs_held h1) < 2 ^ 26 /\
    gn_at1 (lm_gn m1) A h <= Z.of_nat (length (lm_O mc)) /\
    (lm_gn m1 = 0 -> CheckRep.ends_run (gn_pre cx m) (hl_recs (hs_held h1))
        (skipn (Z.to_nat (gn_at1 (lm_gn m1) A h)) (lm_O mc))
        (CheckRep.want_of (gn_pre cx m) (hl_recs (hs_held h1))) <> None) /\
    mo_ok MT S3 (hl_n (hs_held h1) * mo_free MT) /\
    awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) (gn_at1 (lm_gn m1) A h) /\
    gn_prefix_at cx m W mem (frame_addr ly 1 fpos) /\
    sv8 W mem (lf_F cx + 24) HI_G_NOUT /\ sv8 W mem (lf_F cx + 112) gp5_HI79 /\
    gn_kregs B cx (frame_addr ly 1 fpos) regs /\ gp5_ih_regs i k regs.
(* the objects by the kit's names (W_contract.v's A_g_gone, A_g_nout, A_g_out, A_g_s) *)
(* @@ B-ONLY-AR[LAWS,afn_pre,ajournal_gx,ajournal_gx_inner_x,lf_base] Lemma gp5_stk_rd *)
Lemma gp5_stk_rd_x : forall cx fpos ly3 S3 (W : world segs) mem md k,
  LFB0 cx ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  forall a, lf_F cx <= a < ly_top ly3 -> aview segs (w_H W) mem a <> None.
Proof.
  intros cx fpos ly3 S3 W mem md k HB HJ a Ha.
  pose proof (gn_nums_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS cx [(1, fpos)] ly3 S3 W mem md k fpos HB HJ eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & _).
  pose proof HB as (_ & HPRE).
  assert (HPREE : AFN0 LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (_ & _ & _ & _ & _ & Hstk0 & _).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ) as (memS & HJ0 & Hmg).
  rewrite !Z.add_0_r in HJ0.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  unfold LLVMF_STK in *.
  destruct (Z_lt_le_dec a (spZ (c_regs cx))) as [Hlo | Hhi].
  - pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
    apply gp5_pres_view. apply Hpres. lia.
  - rewrite (aview_above_of_journal_x (PI := PB_fr) B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0 a ltac:(lia)).
    rewrite Hmg.
    + apply (gn_stkr_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx HB a). lia.
    + rewrite unsigned_lit_small by lia. intros HGa. pose proof (pa_segs_low a (proj1 (HG a HGa))).
      unfold kLowMemEnd in *. lia.
Qed.
(* @@ CONFLICT Lemma gp5_c8 *)
Lemma gp5_c8_x : forall cx t m m1 i k W c,
  LFB0 cx -> P5C_x cx t m m1 i k W c ->
  SRr segs W c (P5M_x cx t m m1 i k).
Proof.
  intros cx t m m1 i k W c HB (regs & mem & md & ly & S3 & kk & fpos & mc & A & h & -> & HST & Hk & Hi & Hh & Hfd & HR & HIR).
  pose proof HST as (HGS & HDN & (ly0 & S0 & cst & qc & HLS & Hmle & HRUNC & Hcst & Htie) & HRUN & HAW & HAT & HPF & H24 &
    H112).
  pose proof HGS as ((HJ & HFR & HFL & H16 & H144 & H88 & HIN & HRV & HJT) & HMOD & HSEP & HNP).
  pose proof HDN as (hs & qs & c2 & O2 & cap2 & out2 & Hpairs & Hafter & Hrok & HRI & Hop & Hkeys & Hcap0 & Hent & Hsrc &
    Hmpos & Hmsz & Hc2).
  pose proof (gp5_run_same _ _ _ _ _ _ HRUN) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
  (* _gone_p5b.v gp5_c8: hl_n <= hl_cap on every open source's held list of the loop state (amodel_at mc) *)
  assert (Hheld : forall j hj, nth j (lm_hs mc) None = Some hj -> hl_n (hs_held hj) <= hl_cap (hs_held hj)).
  { intros j hj Hj. pose proof HMOD as (HM1 & HM2 & _).
    assert (Hjl : (j < 4)%nat).
    { destruct (Nat.lt_ge_cases j (length (lm_hs mc))) as [Hlt | Hge]; [lia|].
      rewrite nth_overflow in Hj by exact Hge. discriminate Hj. }
    pose proof (HM2 j Hjl) as Hsl. unfold aslot in Hsl. rewrite Hj in Hsl.
    destruct Hsl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HHL & _).
    destruct HHL as (_ & _ & _ & _ & HN & _). lia. }
  destruct (RIstep cx t m ly0 S0 hs qs c2 O2 cap2 out2 m1 mc A i k h ly S3 cst qc HRI Hop Hkeys Hcap0 Hent Hsrc HLS
    Hpairs Hafter Hrok HRUN HRUNC Hmle Hcst (proj2 Htie) Hi Hk Hh Hfd Hheld)
    as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
  pose proof (gn_nums_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS cx [(1, fpos)] ly S3 W mem md kk fpos HB HJ eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & HFF4 & HFFc & HFFapp & Hfrs & HAR).
  pose proof (gp5_ly_x cx fpos ly S3 W mem md kk HB HJ) as (Ly1 & Ly2 & Ly3 & Ly4).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R27 & R3 & R4).
  pose proof HIR as (R23 & R25 & R20 & R21 & R22 & R24 & R26).
  pose proof HMOD as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10).
  assert (HSTK : CNL_STK = 16640) by (vm_compute; reflexivity).
  destruct (gp5_ca_entry W regs mem AF_gn_call R27) as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E9 : ew E 9 = getr regs 9) by (subst E; exact (gp5_EE regs _ 9 9%bv eq_refl)).
  assert (E20 : ew E 20 = getr regs 20) by (subst E; exact (gp5_EE regs _ 20 20%bv eq_refl)).
  clear HE.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_call)) with (Z_to_bv 64 (BASE + AF_gn_call)).
  paj_run_to_tok_x RUNTO HS HJ SHOK gp5_span AF_fr_check_no_loss.
  { gp5_awr. }
  pmkst HS.
  gp5_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs [] CA1_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
  prreg HS (1%bv : bv 5) N1.
  prreg HS (10%bv : bv 5) N10.
  prreg HS (11%bv : bv 5) N11.
  cbn [ms_regs restrict] in KR.
  rewrite Em in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  pose proof (gp5_jk_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
  assert (Hsp1 : spZ (ms_regs ms) = lf_F cx).
  { unfold spZ. rewrite (KR 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small.
    unfold LLVMF_STK in *. lia. }
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9, R9; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  rewrite U9 in N11. rewrite E20, R20 in N10.
  destruct (gn_afn_pre_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx HG LSx RINV cx ly S3 fpos kk W mem mdc (ms_regs ms)
    CNL_STK HB HJ (proj1 HFR) Hsp1
    ltac:(rewrite N1; apply ret_ok_codeptr_v; [lia | reflexivity])
    ltac:(unfold raZ; rewrite N1, unsigned_lit_small by lia; lia)
    ltac:(rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3)
    ltac:(rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4)
    ltac:(rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8)
    ltac:(rewrite HSTK; lia) ltac:(rewrite HSTK; unfold LLVMF_STK; lia)) as (ch & HPREc).
  pose proof (M2 k Hk) as Hslot. unfold aslot in Hslot. rewrite Hh in Hslot.
  pose proof HSEP as ((rest0 & HPM) & _).
  destruct (gp5_aout_pre_x cx mc k h ly S3 W mem mdc rest0 HARc HPM Hh M4) as (OB1 & OB2 & OB3).
  pose proof M4 as (_ & _ & M4no & _ & _ & _ & M4out & _).
  pose proof (gp5_lits W mem HRV) as (L1 & L2 & L3).
  pose proof (gp5_SLOT_rng k Hk) as (HSL1 & HSL2).
  pose proof M5 as (M5a & M5b & M5c).
  rewrite Q9 in M5a, M5c.
  assert (HF8 : (lf_F cx + 208) mod 8 = 0).
  { pose proof (Z.div_mod (lf_F cx) 32 ltac:(lia)) as D. rewrite HF32, Z.add_0_r in D. rewrite D.
    replace (32 * (lf_F cx / 32) + 208) with ((4 * (lf_F cx / 32) + 26) * 8) by lia. apply Z_mod_mult. }
  (* the room round's count facts at this call (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (c)): LS_cnt at the operation's LS state (ly0, S0)
     (LSCNT, with gdone's guards), the arm's model count rule at the loop state mc (CNTSTEP), and the block relation
     gn_tie, whose first half is the LS state's decomposition at rest0L *)
  pose proof Hop as (_ & _ & HtO & _).
  assert (HUs : Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m)).
  { rewrite Forall_forall in Hent |- *. intros e He. exact (proj1 (Hent e He)). }
  assert (Hoff : forall k0 h0, nth k0 (lm_hs m) None = Some h0 ->
      (hl_recs (hs_pending h0) = [] /\ hs_off h0 = 0) \/
      (exists r rs, hl_recs (hs_pending h0) = r :: rs /\ 0 <= hs_off h0 < Z.of_nat (length (snd r)))).
  { intros k0 h0 Hk0. rewrite Forall_forall in Hsrc.
    assert (Hin0 : In (Some h0) (lm_hs m)).
    { rewrite <- Hk0. apply nth_In. destruct (Nat.lt_ge_cases k0 (length (lm_hs m))) as [Hlt | Hge]; [exact Hlt|].
      rewrite nth_overflow in Hk0 by exact Hge. discriminate Hk0. }
    exact (proj1 (Hsrc _ Hin0)). }
  pose proof (LSCNT cx t m ly0 S0 hs HLS HRI Hpairs Hmsz HtO HUs Hmpos Hoff) as HC0.
  pose proof (fun P => CNTSTEP cx t m hs qs c2 O2 cap2 out2 m1 mc A i k h P HRI Hop Hkeys Hcap0 Hent Hsrc Hmpos
    Hpairs Hafter Hrok Hc2 HRUN Hi Hk Hh Hfd Hheld) as HSTEP.
  cbv beta in HSTEP.
  pose proof (proj1 Htie) as (rest0L & HPL0).
  assert (HCNT : cnt_ok_pk RP (cnl_pk (hs_expected h) (hs_held h)) (ablocks B ly S3)).
  { pose proof (proj2 Htie rest0L HPL0) as HP3.
    assert (EQ : forall P, (ReplyCnt.acnt P (ablocks B ly S3) + ReplyCnt.acnt P (model_blks m) =
        ReplyCnt.acnt P (ablocks B ly0 S0) + ReplyCnt.acnt P (model_blks mc))%nat).
    { intros P. rewrite (ReplyCnt.acnt_perm P _ _ HP3), (ReplyCnt.acnt_perm P _ _ HPL0), !ReplyCnt.acnt_app. lia. }
    pose proof HC0 as (C0a & C0b & C0c).
    unfold cnt_ok_pk.
    split; [|split].
    - pose proof (EQ (rp_Psec RP)). pose proof (proj1 (HSTEP (rp_Psec RP))). lia.
    - pose proof (EQ (rp_P24 RP)). pose proof (proj1 (HSTEP (rp_P24 RP))). lia.
    - intros cc0 Hcc0. pose proof (C0c cc0 Hcc0). pose proof (EQ (rp_Pcls RP cc0)).
      pose proof (proj1 (HSTEP (rp_Pcls RP cc0))). lia. }
  eassert (HCALL : SRr segs W (cfg_at segs (BASE + AF_fr_check_no_loss) (ms_regs ms) mem mdc) _).
  { apply (CNL k Hk W ly S3 [] (ms_regs ms) mem mdc ch 224 (gp5_SLOT k) k (lf_F cx + 208) h (lm_gn m1) A
      (Z.of_nat (length (lm_O mc))) (lm_out mc) (lm_O mc)) with (kr := 0%nat).
    - exact HPREc.
    - lia.
    - reflexivity.
    - rewrite Hsp1. lia.
    - rewrite Hsp1. intros a Ha. apply (gp5_jk_pres_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a).
      unfold LLVMF_STK in *. lia.
    - exact N10.
    - exact N11.
    - unfold gp5_SLOT. rewrite <- (proj2 (proj2 (proj2 gp5_objs))). reflexivity.
    - exact Hk.
    - exact HF8.
    - rewrite Hsp1. lia.
    - rewrite Hsp1. lia.
    - exact Hslot.
    - intros a Ha. unfold gn_Gs. apply inG_cons. left. unfold in_zr, gp5_SLOT in *. cbn [fst snd]. lia.
    - destruct HZS as (zr & Hzin & Hz8 & Hzlo & Hzhi). exists zr. split; [exact Hzin|]. split; [exact Hz8|].
      unfold gp5_SLOT, ASRC in *. lia.
    - exact F1.
    - exact F2.
    - exact F3.
    - exact HAT.
    - exact F4.
    - pose proof M5a as Xg. rewrite <- (proj1 gp5_objs) in Xg. exact Xg.
    - destruct M5c as [X|X]; rewrite X; lia.
    - pose proof M4no as Xg. rewrite <- (proj1 (proj2 gp5_objs)) in Xg. exact Xg.
    - pose proof M4out as Xg. rewrite <- (proj1 (proj2 (proj2 gp5_objs))) in Xg. exact Xg.
    - exact OB1.
    - reflexivity.
    - lia.
    - intros _. exact F5.
    - exact OB2.
    - exact OB3.
    - exact F6.
    - exact HRV.
    - exact L1.
    - exact L2.
    - exact L3.
    - exact F8.
    - exact F9.
    (* the room round: RM is NP at the instance (RPNP), and NP S3 is the arm's threaded invariant (gst_x) *)
    - apply (proj2 (RPNP S3 _)). exact HNP.
    - exact HCNT.
    - exact F7.
    - rewrite Hsp1. exact (gp5_stk_rd_x cx fpos ly S3 W mem mdc kk HB HJ). }
  eapply SRr_bind; [exact HCALL|].
  intros W2 cc Hwle2 (ly' & S' & Hp' & regs' & mem' & md' & kk1 & E' & H' & -> & HJc & HP & HPK & HERR1 & HSRC & HE1 &
    HE2 & HE3 & HND & HTX & HCAP & HAT1 & HGN1 & HNO1 & HOUT1 & HOB1 & HPERM & HFRS & HMLE & HRMc & HCAPGE & HCAPEQ).
  hp0g HJc.
  rewrite Hsp1 in HJc.
  replace (lf_F cx + 208 + 8) with (lf_F cx + 216) in HJc by lia.
  set (h1 := set_exp_held h E' H') in *.
  set (oldb := alist_blks (hs_expected h) ++ alist_blks (hs_held h)).
  set (newb := alist_blks E' ++ alist_blks H').
  set (R := (hs_partial h, APARTIAL) :: alist_blks (hs_pending h)).
  assert (HA0 : Permutation (asrc_blks h) (oldb ++ R)).
  { unfold oldb, R. rewrite <- app_assoc. exact (gp5_asrc_perm h). }
  assert (HA1 : Permutation (asrc_blks h1) (newb ++ R)).
  { unfold h1, newb, R. rewrite gp5_asrc_exp_held.
    change ((hs_partial h, APARTIAL) :: alist_blks (hs_pending h) ++ alist_blks E' ++ alist_blks H')
      with (((hs_partial h, APARTIAL) :: alist_blks (hs_pending h)) ++ (alist_blks E' ++ alist_blks H')).
    apply Permutation_app_comm. }
  assert (HPOSTb : forall rest, Permutation (ablocks B ly S3) (oldb ++ rest) ->
      Permutation (ablocks B ly' S') (newb ++ rest)).
  { intros rest Hr. unfold oldb, newb in *. rewrite <- app_assoc in Hr |- *. exact (HPERM rest Hr). }
  destruct (gp5_split cx mc k h ly S3 oldb R HSEP Hh HA0) as (restX & P1 & _).
  assert (Hsurv : forall b, In b (ablocks B ly S3) -> ~ In b (list_blks (hs_expected h) ++ list_blks (hs_held h)) ->
      In b (ablocks B ly' S')).
  { intros b Hb Hnb. exact (gp5_surv ly S3 ly' S' oldb newb _ b P1 (HPOSTb _ P1) Hb Hnb). }
  assert (HGS' : gst_x B NP G_fr fr_FP PST ARx cx t (gn_kq cx m) mc fake_shadow_open fpos ly S3 W mem mdc kk).
  { split; [|split; [exact HMOD | split; [exact HSEP | exact HNP]]]. repeat (split; [assumption|]); assumption. }
  pose proof (gp5_xport_x cx t m mc fpos ly S3 W mem mdc kk k h (list_blks (hs_expected h) ++ list_blks (hs_held h))
    CNL_STK ly' S' W2 mem' md' kk1 HB HGS' HAW HPF H24 H112 Hk Hh (fun b Hb => Hb) HJc
    ltac:(rewrite HSTK; lia) ltac:(rewrite HSTK; unfold LLVMF_STK; lia) HERR1 Hsurv) as HXP.
  assert (Hkl : (k < length (lm_hs mc))%nat) by (rewrite M1; exact Hk).
  pose proof (gp5_sep_step_x cx mc k h h1 fpos ly S3 W mem mdc kk ly' S' W2 mem' md' oldb newb R HJ
    (gp5_jk_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) HSEP Hkl Hh HA0 HA1 HPOSTb) as HSEP1.
  pose proof (gp5_tie_step cx m ly0 S0 mc k h h1 ly S3 ly' S' oldb newb R Htie Hkl Hh HA0 HA1 HPOSTb) as Htie1.
  destruct (gp5_rebuild_x cx t m mc fpos ly' S' W2 mem' md' (kk + kk1) k h1 HXP Hk M1 HSRC HSEP1
    (proj1 (RPNP S' _) HRMc))
    as (HGS1 & HAW1 & HPF1 & H241 & H1121).
  assert (HCOK : gn_cnl_ok h h1 E' H')
    by exact (conj eq_refl (conj HE1 (conj HE2 (conj HE3 (conj HND (conj HTX (conj HCAP (conj HCAPGE HCAPEQ)))))))).
  (* check_shape_ends' count premise at the state check_no_loss left (P5M_x carries it to gp5_c3_x): LS_cnt at the LS
     state, CNTSTEP's second half (under gn_cnl_ok) and the block relation after the call *)
  assert (HCNT2 : cnt_ok_pk RP cshe_pk (ablocks B ly' S')).
  { pose proof (proj2 Htie1 rest0L HPL0) as HP3.
    assert (EQ : forall P, (ReplyCnt.acnt P (ablocks B ly' S') + ReplyCnt.acnt P (model_blks m) =
        ReplyCnt.acnt P (ablocks B ly0 S0) + ReplyCnt.acnt P (model_blks (gn_set mc k h1)))%nat).
    { intros P. rewrite (ReplyCnt.acnt_perm P _ _ HP3), (ReplyCnt.acnt_perm P _ _ HPL0), !ReplyCnt.acnt_app. lia. }
    pose proof HC0 as (C0a & C0b & C0c).
    unfold cnt_ok_pk, cshe_pk. cbv beta.
    split; [|split].
    - pose proof (EQ (rp_Psec RP)). pose proof (proj2 (HSTEP (rp_Psec RP)) h1 E' H' HCOK). lia.
    - pose proof (EQ (rp_P24 RP)). pose proof (proj2 (HSTEP (rp_P24 RP)) h1 E' H' HCOK). lia.
    - intros cc0 Hcc0. pose proof (C0c cc0 Hcc0). pose proof (EQ (rp_Pcls RP cc0)).
      pose proof (proj2 (HSTEP (rp_Pcls RP cc0)) h1 E' H' HCOK). lia. }
  destruct (F10 h1 E' H' S' HCOK HMLE) as (G1 & G2 & G3 & G4).
  pose proof (gp5_jk_faddr_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc 1 fpos) as EFF.
  destruct (gp5_regs_call cx (frame_addr ly 1 fpos) i k regs (ms_regs ms) regs' CA1_KEPT HR HIR
    ltac:(intros r Hr; unfold CA1_KEPT; cbn [In] in Hr |- *; tauto) KR HP) as (HR' & HIR').
  apply SRr_ret.
  exists regs', mem', md', ly', S', (kk + kk1), fpos, mc, A, h, h1, E', H', ly0, S0,
    (cst + cnl_cost MT (hs_expected h) (hs_held h)), qc.
  split.
  { rewrite N1. unfold cfg_at. change (w64 (fr_B0 + AF_gn_ret1)) with (Z_to_bv 64 (BASE + 10452)). reflexivity. }
  split; [exact HGS1|]. split; [exact HDN|]. split; [exact HLS|].
  split; [exact (mo_le_trans MT ML _ _ _ _ _ Hmle HMLE)|].
  split; [exact Htie1|]. split; [exact HCNT2|].
  split; [exact HRUN|]. split; [exact HRUNC|].
  split; [destruct Hcst as (rq & Hrq & Hcle); exists rq; split; [exact Hrq | clear - Hcle; lia]|].
  split; [lia|]. split; [exact Hk|]. split; [exact Hi|]. split; [exact Hh|]. split; [exact Hfd|].
  split; [exact HCOK|].
  split; [exact F5|]. split; [exact G1|].
  split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
  split; [exact HAW1|]. split; [unfold sv8, gn_at1; exact HAT1|]. split; [exact HPF1|].
  split; [exact H241|]. split; [exact H1121|].
  rewrite EFF. split; [exact HR' | exact HIR'].
Qed.
(* @@ CONFLICT Lemma gp5_c3 *)
Lemma gp5_c3_x : forall cx t m m1 i k W c,
  LFB0 cx -> P5M_x cx t m m1 i k W c ->
  SRr segs W c (P5T_x cx t m m1 i k).
Proof.
  intros cx t m m1 i k W c HB (regs & mem & md & ly & S3 & kk & fpos & mc & A & h & h1 & E' & H' & ly0 & S0 & cst0 & qc &
    -> & HGS & HDN & HLS & Hmle & Htie & HCNT2 & HRUN & HRUNC & Hcst & HA0p & Hk & Hi & Hh & Hfd & HCOK & HO32 & G1 &
    G2 & G3 & G4 &
    HAW & HAT & HPF & H24 & H112 & HR & HIR).
  set (mc1 := gn_set mc k h1) in *.
  pose proof HGS as ((HJ & HFR & HFL & H16 & H144 & H88 & HIN & HRV & HJT) & HMOD & HSEP & HNP).
  pose proof (gp5_run_same _ _ _ _ _ _ HRUN) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
  pose proof (gn_nums_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS cx [(1, fpos)] ly S3 W mem md kk fpos HB HJ eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & HFF4 & HFFc & HFFapp & Hfrs & HAR0).
  pose proof (gp5_ly_x cx fpos ly S3 W mem md kk HB HJ) as (Ly1 & Ly2 & Ly3 & Ly4).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R27 & R3 & R4).
  pose proof HIR as (R23 & R25 & R20 & R21 & R22 & R24 & R26).
  pose proof HMOD as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10).
  assert (HSTK : CSHE_STK = 16560) by (vm_compute; reflexivity).
  assert (Hh1 : nth k (lm_hs mc1) None = Some h1).
  { unfold mc1, gn_set. cbn [lm_hs]. apply gp5_setn_same.
    rewrite <- (gp5_setn_length k (Some h1) (lm_hs mc)).
    change (gn_setn k (Some h1) (lm_hs mc)) with (lm_hs mc1). rewrite M1. exact Hk. }
  assert (Hfin : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  pose proof (frame_al64_x segs ARx FRMF ly S3 [] W mem md 1 fpos HAR0 Hfin) as (HFF64 & _).
  set (FF := frame_addr ly 1 fpos) in *.
  assert (HFF8 : FF mod 8 = 0).
  { pose proof (Z.div_mod FF 64 ltac:(lia)) as D. rewrite HFF64, Z.add_0_r in D. rewrite D.
    replace (64 * (FF / 64)) with ((8 * (FF / 64)) * 8) by lia. apply Z_mod_mult. }
  destruct (gp5_ca_entry W regs mem AF_gn_ret1 R27) as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E9 : ew E 9 = getr regs 9) by (subst E; exact (gp5_EE regs _ 9 9%bv eq_refl)).
  assert (E19 : ew E 19 = getr regs 19) by (subst E; exact (gp5_EE regs _ 19 19%bv eq_refl)).
  assert (E20 : ew E 20 = getr regs 20) by (subst E; exact (gp5_EE regs _ 20 20%bv eq_refl)).
  clear HE.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_ret1)) with (Z_to_bv 64 (BASE + AF_gn_ret1)).
  paj_run_to_tok_x RUNTO HS HJ SHOK gp5_span AF_fr_check_shape_ends.
  { gp5_awr. }
  pmkst HS.
  gp5_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs [] CA2_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
  prreg HS (1%bv : bv 5) N1.
  prreg HS (10%bv : bv 5) N10.
  prreg HS (11%bv : bv 5) N11.
  prreg HS (12%bv : bv 5) N12.
  cbn [ms_regs restrict] in KR.
  rewrite Em in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  pose proof (gp5_jk_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
  assert (Hsp1 : spZ (ms_regs ms) = lf_F cx).
  { unfold spZ. rewrite (KR 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small.
    unfold LLVMF_STK in *. lia. }
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9, R9; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  rewrite U9 in N12. rewrite E20, R20 in N10. rewrite E19, R19 in N11.
  destruct (gn_afn_pre_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx HG LSx RINV cx ly S3 fpos kk W mem mdc (ms_regs ms)
    CSHE_STK HB HJ (proj1 HFR) Hsp1
    ltac:(rewrite N1; apply ret_ok_codeptr_v; [lia | reflexivity])
    ltac:(unfold raZ; rewrite N1, unsigned_lit_small by lia; lia)
    ltac:(rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3)
    ltac:(rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4)
    ltac:(rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8)
    ltac:(rewrite HSTK; lia) ltac:(rewrite HSTK; unfold LLVMF_STK; lia)) as (ch & HPREc).
  pose proof (M2 k Hk) as Hslot. unfold aslot in Hslot. rewrite Hh1 in Hslot.
  pose proof HSEP as ((rest0 & HPM) & _).
  destruct (gp5_aout_pre_x cx mc1 k h1 ly S3 W mem mdc rest0 HARc HPM Hh1 M4) as (OB1 & OB2 & OB3).
  pose proof M4 as (_ & _ & M4no & _ & _ & _ & M4out & _).
  pose proof M5 as (M5a & M5b & M5c).
  change (lm_gn mc1) with (lm_gn mc) in M5a, M5c. rewrite Q9 in M5a, M5c.
  pose proof (gp5_held_low_x ly S3 W mem mdc (gp5_SLOT k) h1 HARc Hslot) as (HL1 & HL2).
  pose proof (gp5_SLOT_rng k Hk) as (HSL1 & HSL2).
  pose proof HPF as (PF1 & PF2 & PF3 & PF4 & PF5).
  pose proof HCOK as (EQh1 & HCE1 & HCE2 & HCE3 & HND1 & HTX1 & HCAP1 & _ & _).
  assert (HF8 : (lf_F cx + 208) mod 8 = 0).
  { pose proof (Z.div_mod (lf_F cx) 32 ltac:(lia)) as D. rewrite HF32, Z.add_0_r in D. rewrite D.
    replace (32 * (lf_F cx / 32) + 208) with ((4 * (lf_F cx / 32) + 26) * 8) by lia. apply Z_mod_mult. }
  eassert (HCALL : SRr segs W (cfg_at segs (BASE + AF_fr_check_shape_ends) (ms_regs ms) mem mdc) _).
  { apply (CSHE k Hk W ly S3 [] (ms_regs ms) mem mdc ch 224 (lf_F cx + 208) (gp5_SLOT k) k (FF + 32) h1 (gn_pre cx m)
      (gn_at1 (lm_gn m1) A h) (lm_gn m1) (Z.of_nat (length (lm_O mc))) (lm_out mc) (lm_O mc)) with (kr := 0%nat).
    - exact HPREc.
    - lia.
    - reflexivity.
    - rewrite Hsp1. lia.
    - rewrite Hsp1. intros a Ha. apply (gp5_jk_pres_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a).
      unfold LLVMF_STK in *. lia.
    - exact N10.
    - exact N11.
    - exact N12.
    - exact Hslot.
    - pose proof (Z.div_mod (gp5_SLOT k) 32 ltac:(lia)) as D. rewrite HSL2, Z.add_0_r in D. rewrite D.
      replace (32 * (gp5_SLOT k / 32)) with ((4 * (gp5_SLOT k / 32)) * 8) by lia. apply Z_mod_mult.
    - lia.
    - unfold ASRC, kLowMemEnd. lia.
    - intros a Ha. unfold gn_Gs. apply inG_cons. left. unfold in_zr, gp5_SLOT in *. cbn [fst snd]. lia.
    - destruct HZS as (zr & Hzin & Hz8 & Hzlo & Hzhi). exists zr. split; [exact Hzin|]. split; [exact Hz8|].
      unfold gp5_SLOT, ASRC in *. lia.
    - unfold gp5_SLOT. destruct gp5_hi as (_ & _ & _ & _ & H19). rewrite H19. reflexivity.
    - exact Hk.
    - intros a Ha Hw. rewrite Hsp1, HSTK in Hw. unfold ASRC, LLVMF_STK in *. lia.
    - intros a Ha. unfold cshe_home. right. left.
      assert (Hg : inG G_fr a) by (apply HGs; unfold gp5_SLOT, ASRC in *; lia).
      destruct (HG a Hg) as (Him & Hown & _). split; [exact Him|]. split; [exact Hown|].
      apply HCE. apply (gp5_cell (rg_s fr_RG) (4 * ASRC)); [gp5_inl | unfold gp5_SLOT, ASRC in *; lia].
    - rewrite EQh1. exact HND1.
    - exact G1.
    - intros a Ha Hw. pose proof (HL1 a Ha). rewrite Hsp1, HSTK in Hw. unfold LLVMF_STK in *. lia.
    - intros r Hr a Ha Hw. pose proof (HL2 r Hr a Ha). rewrite Hsp1, HSTK in Hw. unfold LLVMF_STK in *. lia.
    - exact HF8.
    - rewrite Hsp1. lia.
    - rewrite Hsp1. lia.
    - apply (gp5_ra_stack_x ly S3 W mem mdc (lf_F cx + 208) 8 HARc); unfold LLVMF_STK in *; lia.
    - exact HAT.
    - exact PF4.
    - lia.
    - lia.
    - lia.
    - exact PF1.
    - exact PF2.
    - intros a Ha. split; [apply PF3; lia | rewrite Hsp1, HSTK; unfold LLVMF_STK in *; lia].
    - apply amem_range_high; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFFapp; lia | lia].
    - apply amem_range_high; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFFapp; lia | lia].
    - apply (gp5_ra_fake cx FF W mem _ _ HFR HFF8); lia.
    - apply (shadow_hull_vis_of_frame_x segs B ARx LAWS FRMF ly S3 [] W mem mdc 1 fpos _ _ HARc Hfin);
        [fold FF; lia | change (fs_frame_bytes 1) with 128; fold FF; lia | lia].
    - (* the PF premise (the kit's disjunction): its fake-frame disjunct, PF = s3 = FF + 32 *)
      right. exists 1, fpos. split; [exact Hfin|]. intros a Ha.
      unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. fold FF. lia.
    - exact (gp5_lit_end5 W mem HRV).
    - exact HRV.
    - pose proof M5a as Xg. rewrite <- (proj1 gp5_objs) in Xg. exact Xg.
    - destruct M5c as [X|X]; rewrite X; lia.
    - pose proof M4no as Xg. rewrite <- (proj1 (proj2 gp5_objs)) in Xg. exact Xg.
    - pose proof M4out as Xg. rewrite <- (proj1 (proj2 (proj2 gp5_objs))) in Xg. exact Xg.
    - exact OB1.
    - reflexivity.
    - lia.
    - intros _. exact HO32.
    - exact OB2.
    - exact OB3.
    - split; [unfold gn_at1; destruct (lm_gn m1 =? 0); lia | exact G2].
    - exact G3.
    - exact G4.
    (* the room round: RM from NP S3 (gst_x, RPNP); the count from P5M_x (gp5_c8_x's HCNT2) *)
    - apply (proj2 (RPNP S3 _)). exact HNP.
    - exact HCNT2. }
  eapply SRr_bind; [exact HCALL|].
  intros W2 cc Hwle2 (ly' & S' & Hp' & regs' & mem' & md' & kk2 & H'' & ds & c3 & -> & HJc & HP & HERR2 & HSRC &
    HV2 & HC2 &
    HND2 & HCASE & Hc0 & HAT2 & HGN2 & HPERM2 & HFRS2 & HMLE2 & HRMe).
  hp0g HJc.
  rewrite Hsp1 in HJc.
  replace (lf_F cx + 208 + 8) with (lf_F cx + 216) in HJc by lia.
  set (h2 := set_held h1 H'') in *.
  pose proof (gp5_held_perm (hs_held h1) H'' ds HV2 HC2 (gp5_cshe_perm _ _ _ _ _ _ _ _ HCASE)) as HHP.
  assert (HA0 : Permutation (asrc_blks h1) (cshe_ds_blks ds ++ asrc_blks h2)).
  { unfold h2. rewrite gp5_asrc_held. unfold asrc_blks. apply gp5_perm_held. exact HHP. }
  assert (HA1 : Permutation (asrc_blks h2) ([] ++ asrc_blks h2)) by reflexivity.
  assert (HPOSTb : forall rest, Permutation (ablocks B ly S3) (cshe_ds_blks ds ++ rest) ->
      Permutation (ablocks B ly' S') ([] ++ rest)) by exact HPERM2.
  destruct (gp5_split cx mc1 k h1 ly S3 (cshe_ds_blks ds) (asrc_blks h2) HSEP Hh1 HA0) as (restX & P1 & _).
  assert (Hds_in : forall b, In b (cshe_ds_blks ds) -> In b (list_blks (hs_held h1))).
  { intros b Hb. apply (Permutation_in b (Permutation_sym HHP)). apply in_or_app. left. exact Hb. }
  assert (Hsurv : forall b, In b (ablocks B ly S3) -> ~ In b (list_blks (hs_held h1)) -> In b (ablocks B ly' S')).
  { intros b Hb Hnb.
    exact (gp5_surv ly S3 ly' S' (cshe_ds_blks ds) [] _ b P1 (HPOSTb _ P1) Hb (fun X => Hnb (Hds_in b X))). }
  assert (HGS' : gst_x B NP G_fr fr_FP PST ARx cx t (gn_kq cx m) mc1 fake_shadow_open fpos ly S3 W mem mdc kk).
  { split; [|split; [exact HMOD | split; [exact HSEP | exact HNP]]]. repeat (split; [assumption|]); assumption. }
  pose proof (gp5_xport_x cx t m mc1 fpos ly S3 W mem mdc kk k h1 (list_blks (hs_held h1))
    CSHE_STK ly' S' W2 mem' md' kk2 HB HGS' HAW HPF H24 H112 Hk Hh1 (fun b Hb => in_or_app _ _ _ (or_intror Hb))
    HJc ltac:(rewrite HSTK; lia) ltac:(rewrite HSTK; unfold LLVMF_STK; lia) HERR2 Hsurv) as HXP.
  assert (Hkl : (k < length (lm_hs mc1))%nat) by (rewrite M1; exact Hk).
  pose proof (gp5_sep_step_x cx mc1 k h1 h2 fpos ly S3 W mem mdc kk ly' S' W2 mem' md' (cshe_ds_blks ds) []
    (asrc_blks h2) HJ (gp5_jk_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) HSEP Hkl Hh1 HA0 HA1 HPOSTb) as HSEP1.
  pose proof (gp5_tie_step cx m ly0 S0 mc1 k h1 h2 ly S3 ly' S' (cshe_ds_blks ds) [] (asrc_blks h2)
    Htie Hkl Hh1 HA0 HA1 HPOSTb) as Htie1.
  unfold mc1 in Htie1. rewrite gp5_set_set in Htie1.
  destruct (gp5_rebuild_x cx t m mc1 fpos ly' S' W2 mem' md' (kk + kk2) k h2 HXP Hk M1 HSRC HSEP1
    (proj1 (RPNP S' _) HRMe))
    as (HGS1 & HAW1 & HPF1 & H241 & H1121).
  unfold mc1 in HGS1. rewrite gp5_set_set in HGS1.
  assert (HCSOK : gn_cshe_ok (gn_pre cx m) (lm_gn m1) (gn_at1 (lm_gn m1) A h) (lm_O mc) h1 h2 ds c3).
  { exists H''. split; [reflexivity|]. split; [exact HV2|]. split; [exact HC2|]. split; [exact HND2|].
    split; [exact Hc0 | exact HCASE]. }
  pose proof (gp5_jk_faddr_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc 1 fpos) as EFF.
  destruct (gp5_regs_call cx FF i k regs (ms_regs ms) regs' CA2_KEPT HR HIR
    ltac:(intros r Hr; unfold CA2_KEPT; cbn [In] in Hr |- *; tauto) KR HP) as (HR' & HIR').
  apply SRr_ret.
  exists regs', mem', md', ly', S', (kk + kk2), fpos, (gn_set mc k h2), (gn_at1 (lm_gn m1) A h + c3).
  split.
  { rewrite N1. unfold cfg_at. change (w64 (fr_B0 + AF_gn_skip)) with (Z_to_bv 64 (BASE + 10468)). reflexivity. }
  split.
  { split; [exact HGS1|]. split; [exact HDN|].
    (* KF-COUNT (_gone_p5b.v gp5_c3): the meter after check_shape_ends, and the run's cost index after the call *)
    split; [exists ly0, S0, (cst0 + hl_n (hs_held h1) * mo_free MT),
              (qc + cnl_cost MT (hs_expected h) (hs_held h) + cshe_cost MT (hs_held h1));
            split; [exact HLS|]; split; [exact (mo_le_trans MT ML _ _ _ _ _ Hmle HMLE2)|];
            split; [exact (gn_runc_call _ _ _ mc A i k qc h h1 h2 E' H' ds c3 HRUNC Hk Hi Hh Hfd HCOK HCSOK)|];
            split; [destruct Hcst as (rq & Hrq & Hcle); exists rq; split; [exact Hrq|];
                    unfold cshe_cost; generalize (hl_n (hs_held h1) * mo_free MT); intros zc; clear - Hcle; lia |
                    exact Htie1]|].
    split; [exact (gn_run_call _ _ mc A i k h h1 h2 E' H' ds c3 HRUN Hk Hi Hh Hfd HCOK HCSOK)|].
    split; [exact HAW1|]. split; [exact HAT2|]. split; [exact HPF1|]. split; [exact H241 | exact H1121]. }
  split; [exact Hk|]. split; [exact Hi|].
  rewrite EFF. split; [exact HR' | exact HIR'].
Qed.
(* @@ END gp5b *)



(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the R twins of this phase over the R cut points of
   W_LLVMFuzzerTestOneInput_gone_base_x.v (Section gR), as SRrG walks with the G runs.  Strict text above
   unchanged. ---- *)
Section gp5bR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Local Notation gp5_jk_AR_xR := (W_LLVMFuzzerTestOneInput_gone_p5a_x.gp5_jk_AR_xR B PST ARx).
Local Notation gp5_jk_pres_xR := (W_LLVMFuzzerTestOneInput_gone_p5a_x.gp5_jk_pres_xR B PST ARx).
Local Notation gp5_jk_faddr_xR := (W_LLVMFuzzerTestOneInput_gone_p5a_x.gp5_jk_faddr_xR B PST ARx).
(* check_no_loss / check_shape_ends at R, per slot: gone_base_x's GN_CNL_xR / GN_CSHE_xR *)
Hypothesis CNL_R : GN_CNL_xR B MT PST ARx MMAX RP R.
Hypothesis CSHE_R : GN_CSHE_xR B MT PST ARx RP R.
Local Notation p5st_xR := (W_LLVMFuzzerTestOneInput_gone_p5a_x.p5st_xR B MT NP G_fr fr_FP PST ARx LSx RINV R).
Local Notation P5C_xR := (W_LLVMFuzzerTestOneInput_gone_p5a_x.P5C_xR B MT NP G_fr fr_FP PST ARx LSx RINV R).
Local Notation P5T_xR := (W_LLVMFuzzerTestOneInput_gone_p5a_x.P5T_xR B MT NP G_fr fr_FP PST ARx LSx RINV R).
Local Notation gp5_ly_xR := (W_LLVMFuzzerTestOneInput_gone_p5a_x.gp5_ly_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx R).
Local Notation gp5_xport_xR := (W_LLVMFuzzerTestOneInput_gone_p5a_x.gp5_xport_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HG HGs HGcells HROMPIN GWL ERRL BLKN HPST R R_trans).
Local Notation gp5_sep_step_xR := (W_LLVMFuzzerTestOneInput_gone_p5a_x.gp5_sep_step_xR B G_fr fr_FP PST ARx LAWS BLKN R).
Local Notation gp5_rebuild_xR := (W_LLVMFuzzerTestOneInput_gone_p5a_x.gp5_rebuild_xR B NP G_fr fr_FP PST ARx R).
Local Notation AJ0R G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_xR segs B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AJi0R STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_xR segs B PST ARx R STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Let RUNTOG := paj_run_to_x_xG (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].

Ltac hp0gR HJ := let H := fresh "HARg" in
  pose proof (ajournal_gx_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as H; hp0a H; clear H.

Definition P5M_xR (cx : lfcx) (t : Z) (m m1 : lmod) (i k : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S3 kk fpos mc A h h1 E' H' ly0 S0 cst0 q,
    c = cfg_at segs (fr_B0 + AF_gn_ret1) regs mem md /\
    gst_xR B NP G_fr fr_FP PST ARx R cx t (gn_kq cx m) (gn_set mc k h1) fake_shadow_open fpos ly S3 W mem md kk /\
    gdone RINV cx t m m1 /\ LSx cx t m ly0 S0 /\ mo_le MT S0 S3 cst0 /\ gn_tie B cx m ly0 S0 (gn_set mc k h1) ly S3 /\
    (* check_shape_ends' count premise at this state (the room round), from gp5_c8_x *)
    cnt_ok_pk RP cshe_pk (ablocks B ly S3) /\
    gn_run (gn_pre cx m) m1 mc A i k /\
    (* KF-COUNT: the loop's calls before this one cost q; cst0 is within relay_instance_gone's cost + q + this
       check_no_loss's cnl_cost *)
    gn_runc MT (gn_pre cx m) m1 mc A i k q /\ gn_cst MT cx m m1 (q + cnl_cost MT (hs_expected h) (hs_held h)) cst0 /\
    0 <= A /\ (k < 4)%nat /\ (i < length (lm_es m1))%nat /\
    nth k (lm_hs mc) None = Some h /\ hs_fd h = re_fd (nth i (lm_es m1) gn_e0) /\
    gn_cnl_ok h h1 E' H' /\
    Z.of_nat (length (lm_O mc)) < 2 ^ 32 /\
    hl_n (hs_held h1) < 2 ^ 26 /\
    gn_at1 (lm_gn m1) A h <= Z.of_nat (length (lm_O mc)) /\
    (lm_gn m1 = 0 -> CheckRep.ends_run (gn_pre cx m) (hl_recs (hs_held h1))
        (skipn (Z.to_nat (gn_at1 (lm_gn m1) A h)) (lm_O mc))
        (CheckRep.want_of (gn_pre cx m) (hl_recs (hs_held h1))) <> None) /\
    mo_ok MT S3 (hl_n (hs_held h1) * mo_free MT) /\
    awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) (gn_at1 (lm_gn m1) A h) /\
    gn_prefix_at cx m W mem (frame_addr ly 1 fpos) /\
    sv8 W mem (lf_F cx + 24) HI_G_NOUT /\ sv8 W mem (lf_F cx + 112) gp5_HI79 /\
    gn_kregs B cx (frame_addr ly 1 fpos) regs /\ gp5_ih_regs i k regs.

Lemma gp5_stk_rd_xR : forall cx fpos ly3 S3 (W : world segs) mem md k,
  LFB0 cx ->
  AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  forall a, lf_F cx <= a < ly_top ly3 -> aview segs (w_H W) mem a <> None.
Proof.
  intros cx fpos ly3 S3 W mem md k HB HJ a Ha.
  pose proof (gn_nums_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS R cx [(1, fpos)] ly3 S3 W mem md k fpos HB HJ eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & _).
  pose proof HB as (_ & HPRE).
  assert (HPREE : AFN0 LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (_ & _ & _ & _ & _ & Hstk0 & _).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner_xR segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ) as (memS & HJ0 & Hmg).
  rewrite !Z.add_0_r in HJ0.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  unfold LLVMF_STK in *.
  destruct (Z_lt_le_dec a (spZ (c_regs cx))) as [Hlo | Hhi].
  - pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
    apply gp5_pres_view. apply Hpres. lia.
  - rewrite (aview_above_of_journal_xR (PI := PB_fr) B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0 a ltac:(lia)).
    rewrite Hmg.
    + apply (gn_stkr_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx HB a). lia.
    + rewrite unsigned_lit_small by lia. intros HGa. pose proof (pa_segs_low a (proj1 (HG a HGa))).
      unfold kLowMemEnd in *. lia.
Qed.

Lemma gp5_c8_xR : forall cx t m m1 i k W c,
  LFB0 cx -> P5C_xR cx t m m1 i k W c ->
  YA0nH.SRrG segs R W c (P5M_xR cx t m m1 i k).
Proof.
  intros cx t m m1 i k W c HB (regs & mem & md & ly & S3 & kk & fpos & mc & A & h & -> & HST & Hk & Hi & Hh & Hfd & HR & HIR).
  pose proof HST as (HGS & HDN & (ly0 & S0 & cst & qc & HLS & Hmle & HRUNC & Hcst & Htie) & HRUN & HAW & HAT & HPF & H24 &
    H112).
  pose proof HGS as ((HJ & HFR & HFL & H16 & H144 & H88 & HIN & HRV & HJT) & HMOD & HSEP & HNP).
  pose proof HDN as (hs & qs & c2 & O2 & cap2 & out2 & Hpairs & Hafter & Hrok & HRI & Hop & Hkeys & Hcap0 & Hent & Hsrc &
    Hmpos & Hmsz & Hc2).
  pose proof (gp5_run_same _ _ _ _ _ _ HRUN) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
  (* _gone_p5b.v gp5_c8: hl_n <= hl_cap on every open source's held list of the loop state (amodel_at mc) *)
  assert (Hheld : forall j hj, nth j (lm_hs mc) None = Some hj -> hl_n (hs_held hj) <= hl_cap (hs_held hj)).
  { intros j hj Hj. pose proof HMOD as (HM1 & HM2 & _).
    assert (Hjl : (j < 4)%nat).
    { destruct (Nat.lt_ge_cases j (length (lm_hs mc))) as [Hlt | Hge]; [lia|].
      rewrite nth_overflow in Hj by exact Hge. discriminate Hj. }
    pose proof (HM2 j Hjl) as Hsl. unfold aslot in Hsl. rewrite Hj in Hsl.
    destruct Hsl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HHL & _).
    destruct HHL as (_ & _ & _ & _ & HN & _). lia. }
  destruct (RIstep cx t m ly0 S0 hs qs c2 O2 cap2 out2 m1 mc A i k h ly S3 cst qc HRI Hop Hkeys Hcap0 Hent Hsrc HLS
    Hpairs Hafter Hrok HRUN HRUNC Hmle Hcst (proj2 Htie) Hi Hk Hh Hfd Hheld)
    as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
  pose proof (gn_nums_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS R cx [(1, fpos)] ly S3 W mem md kk fpos HB HJ eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & HFF4 & HFFc & HFFapp & Hfrs & HAR).
  pose proof (gp5_ly_xR cx fpos ly S3 W mem md kk HB HJ) as (Ly1 & Ly2 & Ly3 & Ly4).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R27 & R3 & R4).
  pose proof HIR as (R23 & R25 & R20 & R21 & R22 & R24 & R26).
  pose proof HMOD as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10).
  assert (HSTK : CNL_STK = 16640) by (vm_compute; reflexivity).
  destruct (gp5_ca_entry W regs mem AF_gn_call R27) as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E9 : ew E 9 = getr regs 9) by (subst E; exact (gp5_EE regs _ 9 9%bv eq_refl)).
  assert (E20 : ew E 20 = getr regs 20) by (subst E; exact (gp5_EE regs _ 20 20%bv eq_refl)).
  clear HE.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_call)) with (Z_to_bv 64 (BASE + AF_gn_call)).
  paj_run_to_tok_xR RUNTOG HS HJ SHOK gp5_span AF_fr_check_no_loss.
  { gp5_awr. }
  pmkst HS.
  gp5_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs [] CA1_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
  prreg HS (1%bv : bv 5) N1.
  prreg HS (10%bv : bv 5) N10.
  prreg HS (11%bv : bv 5) N11.
  cbn [ms_regs restrict] in KR.
  rewrite Em in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  pose proof (gp5_jk_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
  assert (Hsp1 : spZ (ms_regs ms) = lf_F cx).
  { unfold spZ. rewrite (KR 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small.
    unfold LLVMF_STK in *. lia. }
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9, R9; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  rewrite U9 in N11. rewrite E20, R20 in N10.
  destruct (gn_afn_pre_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx HG LSx RINV R cx ly S3 fpos kk W mem mdc (ms_regs ms)
    CNL_STK HB HJ (proj1 HFR) Hsp1
    ltac:(rewrite N1; apply ret_ok_codeptr_v; [lia | reflexivity])
    ltac:(unfold raZ; rewrite N1, unsigned_lit_small by lia; lia)
    ltac:(rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3)
    ltac:(rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4)
    ltac:(rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8)
    ltac:(rewrite HSTK; lia) ltac:(rewrite HSTK; unfold LLVMF_STK; lia)) as (ch & HPREc).
  pose proof (M2 k Hk) as Hslot. unfold aslot in Hslot. rewrite Hh in Hslot.
  pose proof HSEP as ((rest0 & HPM) & _).
  destruct (gp5_aout_pre_x cx mc k h ly S3 W mem mdc rest0 HARc HPM Hh M4) as (OB1 & OB2 & OB3).
  pose proof M4 as (_ & _ & M4no & _ & _ & _ & M4out & _).
  pose proof (gp5_lits W mem HRV) as (L1 & L2 & L3).
  pose proof (gp5_SLOT_rng k Hk) as (HSL1 & HSL2).
  pose proof M5 as (M5a & M5b & M5c).
  rewrite Q9 in M5a, M5c.
  assert (HF8 : (lf_F cx + 208) mod 8 = 0).
  { pose proof (Z.div_mod (lf_F cx) 32 ltac:(lia)) as D. rewrite HF32, Z.add_0_r in D. rewrite D.
    replace (32 * (lf_F cx / 32) + 208) with ((4 * (lf_F cx / 32) + 26) * 8) by lia. apply Z_mod_mult. }
  (* the room round's count facts at this call (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (c)): LS_cnt at the operation's LS state (ly0, S0)
     (LSCNT, with gdone's guards), the arm's model count rule at the loop state mc (CNTSTEP), and the block relation
     gn_tie, whose first half is the LS state's decomposition at rest0L *)
  pose proof Hop as (_ & _ & HtO & _).
  assert (HUs : Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m)).
  { rewrite Forall_forall in Hent |- *. intros e He. exact (proj1 (Hent e He)). }
  assert (Hoff : forall k0 h0, nth k0 (lm_hs m) None = Some h0 ->
      (hl_recs (hs_pending h0) = [] /\ hs_off h0 = 0) \/
      (exists r rs, hl_recs (hs_pending h0) = r :: rs /\ 0 <= hs_off h0 < Z.of_nat (length (snd r)))).
  { intros k0 h0 Hk0. rewrite Forall_forall in Hsrc.
    assert (Hin0 : In (Some h0) (lm_hs m)).
    { rewrite <- Hk0. apply nth_In. destruct (Nat.lt_ge_cases k0 (length (lm_hs m))) as [Hlt | Hge]; [exact Hlt|].
      rewrite nth_overflow in Hk0 by exact Hge. discriminate Hk0. }
    exact (proj1 (Hsrc _ Hin0)). }
  pose proof (LSCNT cx t m ly0 S0 hs HLS HRI Hpairs Hmsz HtO HUs Hmpos Hoff) as HC0.
  pose proof (fun P => CNTSTEP cx t m hs qs c2 O2 cap2 out2 m1 mc A i k h P HRI Hop Hkeys Hcap0 Hent Hsrc Hmpos
    Hpairs Hafter Hrok Hc2 HRUN Hi Hk Hh Hfd Hheld) as HSTEP.
  cbv beta in HSTEP.
  pose proof (proj1 Htie) as (rest0L & HPL0).
  assert (HCNT : cnt_ok_pk RP (cnl_pk (hs_expected h) (hs_held h)) (ablocks B ly S3)).
  { pose proof (proj2 Htie rest0L HPL0) as HP3.
    assert (EQ : forall P, (ReplyCnt.acnt P (ablocks B ly S3) + ReplyCnt.acnt P (model_blks m) =
        ReplyCnt.acnt P (ablocks B ly0 S0) + ReplyCnt.acnt P (model_blks mc))%nat).
    { intros P. rewrite (ReplyCnt.acnt_perm P _ _ HP3), (ReplyCnt.acnt_perm P _ _ HPL0), !ReplyCnt.acnt_app. lia. }
    pose proof HC0 as (C0a & C0b & C0c).
    unfold cnt_ok_pk.
    split; [|split].
    - pose proof (EQ (rp_Psec RP)). pose proof (proj1 (HSTEP (rp_Psec RP))). lia.
    - pose proof (EQ (rp_P24 RP)). pose proof (proj1 (HSTEP (rp_P24 RP))). lia.
    - intros cc0 Hcc0. pose proof (C0c cc0 Hcc0). pose proof (EQ (rp_Pcls RP cc0)).
      pose proof (proj1 (HSTEP (rp_Pcls RP cc0))). lia. }
  eassert (HCALL : YA0nH.SRrG segs R W (cfg_at segs (BASE + AF_fr_check_no_loss) (ms_regs ms) mem mdc) _).
  { apply (CNL_R k Hk W ly S3 [] (ms_regs ms) mem mdc ch 224 (gp5_SLOT k) k (lf_F cx + 208) h (lm_gn m1) A
      (Z.of_nat (length (lm_O mc))) (lm_out mc) (lm_O mc)) with (kr := 0%nat).
    - exact HPREc.
    - lia.
    - reflexivity.
    - rewrite Hsp1. lia.
    - rewrite Hsp1. intros a Ha. apply (gp5_jk_pres_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a).
      unfold LLVMF_STK in *. lia.
    - exact N10.
    - exact N11.
    - unfold gp5_SLOT. rewrite <- (proj2 (proj2 (proj2 gp5_objs))). reflexivity.
    - exact Hk.
    - exact HF8.
    - rewrite Hsp1. lia.
    - rewrite Hsp1. lia.
    - exact Hslot.
    - intros a Ha. unfold gn_Gs. apply inG_cons. left. unfold in_zr, gp5_SLOT in *. cbn [fst snd]. lia.
    - destruct HZS as (zr & Hzin & Hz8 & Hzlo & Hzhi). exists zr. split; [exact Hzin|]. split; [exact Hz8|].
      unfold gp5_SLOT, ASRC in *. lia.
    - exact F1.
    - exact F2.
    - exact F3.
    - exact HAT.
    - exact F4.
    - pose proof M5a as Xg. rewrite <- (proj1 gp5_objs) in Xg. exact Xg.
    - destruct M5c as [X|X]; rewrite X; lia.
    - pose proof M4no as Xg. rewrite <- (proj1 (proj2 gp5_objs)) in Xg. exact Xg.
    - pose proof M4out as Xg. rewrite <- (proj1 (proj2 (proj2 gp5_objs))) in Xg. exact Xg.
    - exact OB1.
    - reflexivity.
    - lia.
    - intros _. exact F5.
    - exact OB2.
    - exact OB3.
    - exact F6.
    - exact HRV.
    - exact L1.
    - exact L2.
    - exact L3.
    - exact F8.
    - exact F9.
    (* the room round: RM is NP at the instance (RPNP), and NP S3 is the arm's threaded invariant (gst_x) *)
    - apply (proj2 (RPNP S3 _)). exact HNP.
    - exact HCNT.
    - exact F7.
    - rewrite Hsp1. exact (gp5_stk_rd_xR cx fpos ly S3 W mem mdc kk HB HJ). }
  eapply (YA0nH.SRrG_bind _ R R_trans); [exact HCALL|].
  intros W2 cc Hwle2 (ly' & S' & Hp' & regs' & mem' & md' & kk1 & E' & H' & -> & HJc & HP & HPK & HERR1 & HSRC & HE1 &
    HE2 & HE3 & HND & HTX & HCAP & HAT1 & HGN1 & HNO1 & HOUT1 & HOB1 & HPERM & HFRS & HMLE & HRMc & HCAPGE & HCAPEQ).
  hp0gR HJc.
  rewrite Hsp1 in HJc.
  replace (lf_F cx + 208 + 8) with (lf_F cx + 216) in HJc by lia.
  set (h1 := set_exp_held h E' H') in *.
  set (oldb := alist_blks (hs_expected h) ++ alist_blks (hs_held h)).
  set (newb := alist_blks E' ++ alist_blks H').
  set (Rl := (hs_partial h, APARTIAL) :: alist_blks (hs_pending h)).
  assert (HA0 : Permutation (asrc_blks h) (oldb ++ Rl)).
  { unfold oldb, Rl. rewrite <- app_assoc. exact (gp5_asrc_perm h). }
  assert (HA1 : Permutation (asrc_blks h1) (newb ++ Rl)).
  { unfold h1, newb, Rl. rewrite gp5_asrc_exp_held.
    change ((hs_partial h, APARTIAL) :: alist_blks (hs_pending h) ++ alist_blks E' ++ alist_blks H')
      with (((hs_partial h, APARTIAL) :: alist_blks (hs_pending h)) ++ (alist_blks E' ++ alist_blks H')).
    apply Permutation_app_comm. }
  assert (HPOSTb : forall rest, Permutation (ablocks B ly S3) (oldb ++ rest) ->
      Permutation (ablocks B ly' S') (newb ++ rest)).
  { intros rest Hr. unfold oldb, newb in *. rewrite <- app_assoc in Hr |- *. exact (HPERM rest Hr). }
  destruct (gp5_split cx mc k h ly S3 oldb Rl HSEP Hh HA0) as (restX & P1 & _).
  assert (Hsurv : forall b, In b (ablocks B ly S3) -> ~ In b (list_blks (hs_expected h) ++ list_blks (hs_held h)) ->
      In b (ablocks B ly' S')).
  { intros b Hb Hnb. exact (gp5_surv ly S3 ly' S' oldb newb _ b P1 (HPOSTb _ P1) Hb Hnb). }
  assert (HGS' : gst_xR B NP G_fr fr_FP PST ARx R cx t (gn_kq cx m) mc fake_shadow_open fpos ly S3 W mem mdc kk).
  { split; [|split; [exact HMOD | split; [exact HSEP | exact HNP]]]. repeat (split; [assumption|]); assumption. }
  pose proof (gp5_xport_xR cx t m mc fpos ly S3 W mem mdc kk k h (list_blks (hs_expected h) ++ list_blks (hs_held h))
    CNL_STK ly' S' W2 mem' md' kk1 HB HGS' HAW HPF H24 H112 Hk Hh (fun b Hb => Hb) HJc
    ltac:(rewrite HSTK; lia) ltac:(rewrite HSTK; unfold LLVMF_STK; lia) HERR1 Hsurv) as HXP.
  assert (Hkl : (k < length (lm_hs mc))%nat) by (rewrite M1; exact Hk).
  pose proof (gp5_sep_step_xR cx mc k h h1 fpos ly S3 W mem mdc kk ly' S' W2 mem' md' oldb newb Rl HJ
    (gp5_jk_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) HSEP Hkl Hh HA0 HA1 HPOSTb) as HSEP1.
  pose proof (gp5_tie_step cx m ly0 S0 mc k h h1 ly S3 ly' S' oldb newb Rl Htie Hkl Hh HA0 HA1 HPOSTb) as Htie1.
  destruct (gp5_rebuild_xR cx t m mc fpos ly' S' W2 mem' md' (kk + kk1) k h1 HXP Hk M1 HSRC HSEP1
    (proj1 (RPNP S' _) HRMc))
    as (HGS1 & HAW1 & HPF1 & H241 & H1121).
  assert (HCOK : gn_cnl_ok h h1 E' H')
    by exact (conj eq_refl (conj HE1 (conj HE2 (conj HE3 (conj HND (conj HTX (conj HCAP (conj HCAPGE HCAPEQ)))))))).
  (* check_shape_ends' count premise at the state check_no_loss left (P5M_x carries it to gp5_c3_x): LS_cnt at the LS
     state, CNTSTEP's second half (under gn_cnl_ok) and the block relation after the call *)
  assert (HCNT2 : cnt_ok_pk RP cshe_pk (ablocks B ly' S')).
  { pose proof (proj2 Htie1 rest0L HPL0) as HP3.
    assert (EQ : forall P, (ReplyCnt.acnt P (ablocks B ly' S') + ReplyCnt.acnt P (model_blks m) =
        ReplyCnt.acnt P (ablocks B ly0 S0) + ReplyCnt.acnt P (model_blks (gn_set mc k h1)))%nat).
    { intros P. rewrite (ReplyCnt.acnt_perm P _ _ HP3), (ReplyCnt.acnt_perm P _ _ HPL0), !ReplyCnt.acnt_app. lia. }
    pose proof HC0 as (C0a & C0b & C0c).
    unfold cnt_ok_pk, cshe_pk. cbv beta.
    split; [|split].
    - pose proof (EQ (rp_Psec RP)). pose proof (proj2 (HSTEP (rp_Psec RP)) h1 E' H' HCOK). lia.
    - pose proof (EQ (rp_P24 RP)). pose proof (proj2 (HSTEP (rp_P24 RP)) h1 E' H' HCOK). lia.
    - intros cc0 Hcc0. pose proof (C0c cc0 Hcc0). pose proof (EQ (rp_Pcls RP cc0)).
      pose proof (proj2 (HSTEP (rp_Pcls RP cc0)) h1 E' H' HCOK). lia. }
  destruct (F10 h1 E' H' S' HCOK HMLE) as (G1 & G2 & G3 & G4).
  pose proof (gp5_jk_faddr_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc 1 fpos) as EFF.
  destruct (gp5_regs_call cx (frame_addr ly 1 fpos) i k regs (ms_regs ms) regs' CA1_KEPT HR HIR
    ltac:(intros r Hr; unfold CA1_KEPT; cbn [In] in Hr |- *; tauto) KR HP) as (HR' & HIR').
  apply (YA0nH.SRrG_ret _ R R_refl).
  exists regs', mem', md', ly', S', (kk + kk1), fpos, mc, A, h, h1, E', H', ly0, S0,
    (cst + cnl_cost MT (hs_expected h) (hs_held h)), qc.
  split.
  { rewrite N1. unfold cfg_at. change (w64 (fr_B0 + AF_gn_ret1)) with (Z_to_bv 64 (BASE + 10452)). reflexivity. }
  split; [exact HGS1|]. split; [exact HDN|]. split; [exact HLS|].
  split; [exact (mo_le_trans MT ML _ _ _ _ _ Hmle HMLE)|].
  split; [exact Htie1|]. split; [exact HCNT2|].
  split; [exact HRUN|]. split; [exact HRUNC|].
  split; [destruct Hcst as (rq & Hrq & Hcle); exists rq; split; [exact Hrq | clear - Hcle; lia]|].
  split; [lia|]. split; [exact Hk|]. split; [exact Hi|]. split; [exact Hh|]. split; [exact Hfd|].
  split; [exact HCOK|].
  split; [exact F5|]. split; [exact G1|].
  split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
  split; [exact HAW1|]. split; [unfold sv8, gn_at1; exact HAT1|]. split; [exact HPF1|].
  split; [exact H241|]. split; [exact H1121|].
  rewrite EFF. split; [exact HR' | exact HIR'].
Qed.

Lemma gp5_c3_xR : forall cx t m m1 i k W c,
  LFB0 cx -> P5M_xR cx t m m1 i k W c ->
  YA0nH.SRrG segs R W c (P5T_xR cx t m m1 i k).
Proof.
  intros cx t m m1 i k W c HB (regs & mem & md & ly & S3 & kk & fpos & mc & A & h & h1 & E' & H' & ly0 & S0 & cst0 & qc &
    -> & HGS & HDN & HLS & Hmle & Htie & HCNT2 & HRUN & HRUNC & Hcst & HA0p & Hk & Hi & Hh & Hfd & HCOK & HO32 & G1 &
    G2 & G3 & G4 &
    HAW & HAT & HPF & H24 & H112 & HR & HIR).
  set (mc1 := gn_set mc k h1) in *.
  pose proof HGS as ((HJ & HFR & HFL & H16 & H144 & H88 & HIN & HRV & HJT) & HMOD & HSEP & HNP).
  pose proof (gp5_run_same _ _ _ _ _ _ HRUN) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
  pose proof (gn_nums_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS R cx [(1, fpos)] ly S3 W mem md kk fpos HB HJ eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & HFF4 & HFFc & HFFapp & Hfrs & HAR0).
  pose proof (gp5_ly_xR cx fpos ly S3 W mem md kk HB HJ) as (Ly1 & Ly2 & Ly3 & Ly4).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R27 & R3 & R4).
  pose proof HIR as (R23 & R25 & R20 & R21 & R22 & R24 & R26).
  pose proof HMOD as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10).
  assert (HSTK : CSHE_STK = 16560) by (vm_compute; reflexivity).
  assert (Hh1 : nth k (lm_hs mc1) None = Some h1).
  { unfold mc1, gn_set. cbn [lm_hs]. apply gp5_setn_same.
    rewrite <- (gp5_setn_length k (Some h1) (lm_hs mc)).
    change (gn_setn k (Some h1) (lm_hs mc)) with (lm_hs mc1). rewrite M1. exact Hk. }
  assert (Hfin : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  pose proof (frame_al64_x segs ARx FRMF ly S3 [] W mem md 1 fpos HAR0 Hfin) as (HFF64 & _).
  set (FF := frame_addr ly 1 fpos) in *.
  assert (HFF8 : FF mod 8 = 0).
  { pose proof (Z.div_mod FF 64 ltac:(lia)) as D. rewrite HFF64, Z.add_0_r in D. rewrite D.
    replace (64 * (FF / 64)) with ((8 * (FF / 64)) * 8) by lia. apply Z_mod_mult. }
  destruct (gp5_ca_entry W regs mem AF_gn_ret1 R27) as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E9 : ew E 9 = getr regs 9) by (subst E; exact (gp5_EE regs _ 9 9%bv eq_refl)).
  assert (E19 : ew E 19 = getr regs 19) by (subst E; exact (gp5_EE regs _ 19 19%bv eq_refl)).
  assert (E20 : ew E 20 = getr regs 20) by (subst E; exact (gp5_EE regs _ 20 20%bv eq_refl)).
  clear HE.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_ret1)) with (Z_to_bv 64 (BASE + AF_gn_ret1)).
  paj_run_to_tok_xR RUNTOG HS HJ SHOK gp5_span AF_fr_check_shape_ends.
  { gp5_awr. }
  pmkst HS.
  gp5_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs [] CA2_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
  prreg HS (1%bv : bv 5) N1.
  prreg HS (10%bv : bv 5) N10.
  prreg HS (11%bv : bv 5) N11.
  prreg HS (12%bv : bv 5) N12.
  cbn [ms_regs restrict] in KR.
  rewrite Em in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  pose proof (gp5_jk_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
  assert (Hsp1 : spZ (ms_regs ms) = lf_F cx).
  { unfold spZ. rewrite (KR 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small.
    unfold LLVMF_STK in *. lia. }
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9, R9; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  rewrite U9 in N12. rewrite E20, R20 in N10. rewrite E19, R19 in N11.
  destruct (gn_afn_pre_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx HG LSx RINV R cx ly S3 fpos kk W mem mdc (ms_regs ms)
    CSHE_STK HB HJ (proj1 HFR) Hsp1
    ltac:(rewrite N1; apply ret_ok_codeptr_v; [lia | reflexivity])
    ltac:(unfold raZ; rewrite N1, unsigned_lit_small by lia; lia)
    ltac:(rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3)
    ltac:(rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4)
    ltac:(rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8)
    ltac:(rewrite HSTK; lia) ltac:(rewrite HSTK; unfold LLVMF_STK; lia)) as (ch & HPREc).
  pose proof (M2 k Hk) as Hslot. unfold aslot in Hslot. rewrite Hh1 in Hslot.
  pose proof HSEP as ((rest0 & HPM) & _).
  destruct (gp5_aout_pre_x cx mc1 k h1 ly S3 W mem mdc rest0 HARc HPM Hh1 M4) as (OB1 & OB2 & OB3).
  pose proof M4 as (_ & _ & M4no & _ & _ & _ & M4out & _).
  pose proof M5 as (M5a & M5b & M5c).
  change (lm_gn mc1) with (lm_gn mc) in M5a, M5c. rewrite Q9 in M5a, M5c.
  pose proof (gp5_held_low_x ly S3 W mem mdc (gp5_SLOT k) h1 HARc Hslot) as (HL1 & HL2).
  pose proof (gp5_SLOT_rng k Hk) as (HSL1 & HSL2).
  pose proof HPF as (PF1 & PF2 & PF3 & PF4 & PF5).
  pose proof HCOK as (EQh1 & HCE1 & HCE2 & HCE3 & HND1 & HTX1 & HCAP1 & _ & _).
  assert (HF8 : (lf_F cx + 208) mod 8 = 0).
  { pose proof (Z.div_mod (lf_F cx) 32 ltac:(lia)) as D. rewrite HF32, Z.add_0_r in D. rewrite D.
    replace (32 * (lf_F cx / 32) + 208) with ((4 * (lf_F cx / 32) + 26) * 8) by lia. apply Z_mod_mult. }
  eassert (HCALL : YA0nH.SRrG segs R W (cfg_at segs (BASE + AF_fr_check_shape_ends) (ms_regs ms) mem mdc) _).
  { apply (CSHE_R k Hk W ly S3 [] (ms_regs ms) mem mdc ch 224 (lf_F cx + 208) (gp5_SLOT k) k (FF + 32) h1 (gn_pre cx m)
      (gn_at1 (lm_gn m1) A h) (lm_gn m1) (Z.of_nat (length (lm_O mc))) (lm_out mc) (lm_O mc)) with (kr := 0%nat).
    - exact HPREc.
    - lia.
    - reflexivity.
    - rewrite Hsp1. lia.
    - rewrite Hsp1. intros a Ha. apply (gp5_jk_pres_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a).
      unfold LLVMF_STK in *. lia.
    - exact N10.
    - exact N11.
    - exact N12.
    - exact Hslot.
    - pose proof (Z.div_mod (gp5_SLOT k) 32 ltac:(lia)) as D. rewrite HSL2, Z.add_0_r in D. rewrite D.
      replace (32 * (gp5_SLOT k / 32)) with ((4 * (gp5_SLOT k / 32)) * 8) by lia. apply Z_mod_mult.
    - lia.
    - unfold ASRC, kLowMemEnd. lia.
    - intros a Ha. unfold gn_Gs. apply inG_cons. left. unfold in_zr, gp5_SLOT in *. cbn [fst snd]. lia.
    - destruct HZS as (zr & Hzin & Hz8 & Hzlo & Hzhi). exists zr. split; [exact Hzin|]. split; [exact Hz8|].
      unfold gp5_SLOT, ASRC in *. lia.
    - unfold gp5_SLOT. destruct gp5_hi as (_ & _ & _ & _ & H19). rewrite H19. reflexivity.
    - exact Hk.
    - intros a Ha Hw. rewrite Hsp1, HSTK in Hw. unfold ASRC, LLVMF_STK in *. lia.
    - intros a Ha. unfold cshe_home. right. left.
      assert (Hg : inG G_fr a) by (apply HGs; unfold gp5_SLOT, ASRC in *; lia).
      destruct (HG a Hg) as (Him & Hown & _). split; [exact Him|]. split; [exact Hown|].
      apply HCE. apply (gp5_cell (rg_s fr_RG) (4 * ASRC)); [gp5_inl | unfold gp5_SLOT, ASRC in *; lia].
    - rewrite EQh1. exact HND1.
    - exact G1.
    - intros a Ha Hw. pose proof (HL1 a Ha). rewrite Hsp1, HSTK in Hw. unfold LLVMF_STK in *. lia.
    - intros r Hr a Ha Hw. pose proof (HL2 r Hr a Ha). rewrite Hsp1, HSTK in Hw. unfold LLVMF_STK in *. lia.
    - exact HF8.
    - rewrite Hsp1. lia.
    - rewrite Hsp1. lia.
    - apply (gp5_ra_stack_x ly S3 W mem mdc (lf_F cx + 208) 8 HARc); unfold LLVMF_STK in *; lia.
    - exact HAT.
    - exact PF4.
    - lia.
    - lia.
    - lia.
    - exact PF1.
    - exact PF2.
    - intros a Ha. split; [apply PF3; lia | rewrite Hsp1, HSTK; unfold LLVMF_STK in *; lia].
    - apply amem_range_high; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFFapp; lia | lia].
    - apply amem_range_high; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFFapp; lia | lia].
    - apply (gp5_ra_fake cx FF W mem _ _ HFR HFF8); lia.
    - apply (shadow_hull_vis_of_frame_x segs B ARx LAWS FRMF ly S3 [] W mem mdc 1 fpos _ _ HARc Hfin);
        [fold FF; lia | change (fs_frame_bytes 1) with 128; fold FF; lia | lia].
    - (* the PF premise (the kit's disjunction): its fake-frame disjunct, PF = s3 = FF + 32 *)
      right. exists 1, fpos. split; [exact Hfin|]. intros a Ha.
      unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. fold FF. lia.
    - exact (gp5_lit_end5 W mem HRV).
    - exact HRV.
    - pose proof M5a as Xg. rewrite <- (proj1 gp5_objs) in Xg. exact Xg.
    - destruct M5c as [X|X]; rewrite X; lia.
    - pose proof M4no as Xg. rewrite <- (proj1 (proj2 gp5_objs)) in Xg. exact Xg.
    - pose proof M4out as Xg. rewrite <- (proj1 (proj2 (proj2 gp5_objs))) in Xg. exact Xg.
    - exact OB1.
    - reflexivity.
    - lia.
    - intros _. exact HO32.
    - exact OB2.
    - exact OB3.
    - split; [unfold gn_at1; destruct (lm_gn m1 =? 0); lia | exact G2].
    - exact G3.
    - exact G4.
    (* the room round: RM from NP S3 (gst_x, RPNP); the count from P5M_x (gp5_c8_x's HCNT2) *)
    - apply (proj2 (RPNP S3 _)). exact HNP.
    - exact HCNT2. }
  eapply (YA0nH.SRrG_bind _ R R_trans); [exact HCALL|].
  intros W2 cc Hwle2 (ly' & S' & Hp' & regs' & mem' & md' & kk2 & H'' & ds & c3 & -> & HJc & HP & HERR2 & HSRC &
    HV2 & HC2 &
    HND2 & HCASE & Hc0 & HAT2 & HGN2 & HPERM2 & HFRS2 & HMLE2 & HRMe).
  hp0gR HJc.
  rewrite Hsp1 in HJc.
  replace (lf_F cx + 208 + 8) with (lf_F cx + 216) in HJc by lia.
  set (h2 := set_held h1 H'') in *.
  pose proof (gp5_held_perm (hs_held h1) H'' ds HV2 HC2 (gp5_cshe_perm _ _ _ _ _ _ _ _ HCASE)) as HHP.
  assert (HA0 : Permutation (asrc_blks h1) (cshe_ds_blks ds ++ asrc_blks h2)).
  { unfold h2. rewrite gp5_asrc_held. unfold asrc_blks. apply gp5_perm_held. exact HHP. }
  assert (HA1 : Permutation (asrc_blks h2) ([] ++ asrc_blks h2)) by reflexivity.
  assert (HPOSTb : forall rest, Permutation (ablocks B ly S3) (cshe_ds_blks ds ++ rest) ->
      Permutation (ablocks B ly' S') ([] ++ rest)) by exact HPERM2.
  destruct (gp5_split cx mc1 k h1 ly S3 (cshe_ds_blks ds) (asrc_blks h2) HSEP Hh1 HA0) as (restX & P1 & _).
  assert (Hds_in : forall b, In b (cshe_ds_blks ds) -> In b (list_blks (hs_held h1))).
  { intros b Hb. apply (Permutation_in b (Permutation_sym HHP)). apply in_or_app. left. exact Hb. }
  assert (Hsurv : forall b, In b (ablocks B ly S3) -> ~ In b (list_blks (hs_held h1)) -> In b (ablocks B ly' S')).
  { intros b Hb Hnb.
    exact (gp5_surv ly S3 ly' S' (cshe_ds_blks ds) [] _ b P1 (HPOSTb _ P1) Hb (fun X => Hnb (Hds_in b X))). }
  assert (HGS' : gst_xR B NP G_fr fr_FP PST ARx R cx t (gn_kq cx m) mc1 fake_shadow_open fpos ly S3 W mem mdc kk).
  { split; [|split; [exact HMOD | split; [exact HSEP | exact HNP]]]. repeat (split; [assumption|]); assumption. }
  pose proof (gp5_xport_xR cx t m mc1 fpos ly S3 W mem mdc kk k h1 (list_blks (hs_held h1))
    CSHE_STK ly' S' W2 mem' md' kk2 HB HGS' HAW HPF H24 H112 Hk Hh1 (fun b Hb => in_or_app _ _ _ (or_intror Hb))
    HJc ltac:(rewrite HSTK; lia) ltac:(rewrite HSTK; unfold LLVMF_STK; lia) HERR2 Hsurv) as HXP.
  assert (Hkl : (k < length (lm_hs mc1))%nat) by (rewrite M1; exact Hk).
  pose proof (gp5_sep_step_xR cx mc1 k h1 h2 fpos ly S3 W mem mdc kk ly' S' W2 mem' md' (cshe_ds_blks ds) []
    (asrc_blks h2) HJ (gp5_jk_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) HSEP Hkl Hh1 HA0 HA1 HPOSTb) as HSEP1.
  pose proof (gp5_tie_step cx m ly0 S0 mc1 k h1 h2 ly S3 ly' S' (cshe_ds_blks ds) [] (asrc_blks h2)
    Htie Hkl Hh1 HA0 HA1 HPOSTb) as Htie1.
  unfold mc1 in Htie1. rewrite gp5_set_set in Htie1.
  destruct (gp5_rebuild_xR cx t m mc1 fpos ly' S' W2 mem' md' (kk + kk2) k h2 HXP Hk M1 HSRC HSEP1
    (proj1 (RPNP S' _) HRMe))
    as (HGS1 & HAW1 & HPF1 & H241 & H1121).
  unfold mc1 in HGS1. rewrite gp5_set_set in HGS1.
  assert (HCSOK : gn_cshe_ok (gn_pre cx m) (lm_gn m1) (gn_at1 (lm_gn m1) A h) (lm_O mc) h1 h2 ds c3).
  { exists H''. split; [reflexivity|]. split; [exact HV2|]. split; [exact HC2|]. split; [exact HND2|].
    split; [exact Hc0 | exact HCASE]. }
  pose proof (gp5_jk_faddr_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc 1 fpos) as EFF.
  destruct (gp5_regs_call cx FF i k regs (ms_regs ms) regs' CA2_KEPT HR HIR
    ltac:(intros r Hr; unfold CA2_KEPT; cbn [In] in Hr |- *; tauto) KR HP) as (HR' & HIR').
  apply (YA0nH.SRrG_ret _ R R_refl).
  exists regs', mem', md', ly', S', (kk + kk2), fpos, (gn_set mc k h2), (gn_at1 (lm_gn m1) A h + c3).
  split.
  { rewrite N1. unfold cfg_at. change (w64 (fr_B0 + AF_gn_skip)) with (Z_to_bv 64 (BASE + 10468)). reflexivity. }
  split.
  { split; [exact HGS1|]. split; [exact HDN|].
    (* KF-COUNT (_gone_p5b.v gp5_c3): the meter after check_shape_ends, and the run's cost index after the call *)
    split; [exists ly0, S0, (cst0 + hl_n (hs_held h1) * mo_free MT),
              (qc + cnl_cost MT (hs_expected h) (hs_held h) + cshe_cost MT (hs_held h1));
            split; [exact HLS|]; split; [exact (mo_le_trans MT ML _ _ _ _ _ Hmle HMLE2)|];
            split; [exact (gn_runc_call _ _ _ mc A i k qc h h1 h2 E' H' ds c3 HRUNC Hk Hi Hh Hfd HCOK HCSOK)|];
            split; [destruct Hcst as (rq & Hrq & Hcle); exists rq; split; [exact Hrq|];
                    unfold cshe_cost; generalize (hl_n (hs_held h1) * mo_free MT); intros zc; clear - Hcle; lia |
                    exact Htie1]|].
    split; [exact (gn_run_call _ _ mc A i k h h1 h2 E' H' ds c3 HRUN Hk Hi Hh Hfd HCOK HCSOK)|].
    split; [exact HAW1|]. split; [exact HAT2|]. split; [exact HPF1|]. split; [exact H241 | exact H1121]. }
  split; [exact Hk|]. split; [exact Hi|].
  rewrite EFF. split; [exact HR' | exact HIR'].
Qed.

End gp5bR.

End gp5b.

