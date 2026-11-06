(* lib/A/ACtlG/F36_82820.v -- GLUE for the helper stage seg_F36_82820 of fuzz_ctrl image A's walk of
   LLVMFuzzerTestOneInput (lib/A/ACtl.v names no stage for it; a Theorem Labs lane's F36_82814 / F36_8281c consume it).
   Written by a Theorem Labs lane; single writer.  rule 24: no function proved (stage glue of a walk from an
   already-proved run and a cited callee spec).

   WHAT IT PROVES
     glue_seg_F36_82820 : forall POST (j : nat),
       CF POST (ix_cut C_A828d8_at [Z.of_nat j]) -> CF POST (ix_cut C_A828cc_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []).  The segment is 0x828cc -> 0x828d8:
     0x828cc mv a0,s7   0x828d0 mv a1,s2   0x828d4 jal 84498 <reac_box_catalogue_match>   (return pc 0x828d8).

   THE PROOF (glue-pattern.md G1-G5, section 8 for the callee)
   G1  the entry cut C_A828cc_at (ACtlCutP.v:2909-2920) at index [Z.of_nat j]: Permutation, FRAC, c_n bound, j <= 255,
       HB, FLSI, LK, FLSX, rgv 20 t_want_m, LT.
   G2  no premise: Seg/F36Fs.v f36_evt_call_pre_F has none (three register moves, no memory access).
   G3  ProgBridge.cfg_at_MS, then YA0nR.SRr_xregs_eqv to the run's canonical map mkR_of regs3.
   G4  f36_evt_call_pre_F lifted by YA0nR.SRr_fevt at the empty footprint Kit.kit_RNG0; the end state is the callee
       entry (pc 0x84498, ra 0x828d8, a0 = s7 = phi, a1 = s2 = flen j).
   CALL  a Theorem Labs lane's treac_box_catalogue_match_spec (Section hypothesis CM_SPEC, below, a Theorem Labs lane's constant cited by name) at
       the callee entry, bound with YA0n.SRr_bind.  The hypothesis is first unfolded IN PLACE (a Theorem Labs lane's statement-level
       constants CM_STK EV_CM LIVE_CM CM_ROWS CM_TBLZ, CtrlRo's IMG_LO / IMG_HI, A_CM_TBL := 0x9e800 and
       A_catalogue_matchP := 0x84498, each by conversion), so its premises read in numerals.  Its premises, each
       from the cut:
         afn_pre      YCbq.afn_pre_at from the cut's journal (moved across the run's materialization by
                      ajournal_exec, as A5.v), o = sp - c_sp, STK1 = 9136 (9136 + 4096 <= LLVMF_STK); ret_ok / ra / gp /
                      tp from the run's end map and FRAC; achain at s0 = c_sp: either ly_top - 16 <= c_sp (empty chain)
                      or YCbq.achain_push of the entry's afn_pre chain with the saved ra / s0 words of FRAC's saved bytes
                      at c_sp - 8 / c_sp - 16 (lib/Lib bytes_at -> the core's rdword: local f36c_rdword_le8), the view
                      above c_sp kept by the journal;
         arodata_okS  the entry's (ctl_base) kept by the journal (local f36c_aro_keep, FP = [] so fp_spares is closed);
         a0 / a1      FLSX's rgv 23 phi / rgv 18 flen through the run;  bounds from the AR block law of (phi, flen);
         fb           SlotModel.t_g, length 50 (fr50_length);  the record block from the body's Permutation;
         garr8 fb     FLSX's bytes_at phi (t_g ..) and the block's visibility (AR block law);
         garr8 table  the core's arodata_okS at [0x9e800, 0x9e800 + 3256) (in RELRO by RELRO_CAT; not owned / errno by
                      TFIB_SYMS) and the image bytes CM_TBL (reac_box_catalogue_match_lib.CM_TBL_eq);
         GLOBS        CM_GLOB;  IMG bounds and room counts by computation (frames S3 = [(6, fpos)]);
         st_nev / blocks_bytes  the journal's k bound with the entry's EV_LIB, and AR's Wf (wf_live).
   G5  the callee's apost_base at ra = 0x828d8: the exit C_A828d8_at at the callee's (ly', S', W', regs', mem', md'):
         journal      YCbq.ajournal_sub of the cut's journal and the callee's (nf = [], k + 0);
         frames / frame law / k bound  the callee's frames S' = frames S3; own6 and kmax unchanged;
         body         registers through aregs_preserved; memory facts kept across the callee by the callee journal's
                      kept view (stack above sp: [sp, c_sp); the owned class-6 frame [fr, fr + 4096) and its shadow;
                      the live blocks), turned into raw-byte equalities by local f36c_raw (visible at the cut by the
                      journal window / AR frame and block laws, never an image byte); HB and f1_IN's addressable bytes
                      from the AR shadow law at the callee's post (local f36c_addr_of_block); rgv 10 t_want from the
                      spec's a0 (SlotModel.t_want = RcMatch.want CAT (t_len) (t_g), CAT = 0x9e800);
         ctl_rt_C     a Theorem Labs lane's PROVED A.ProgWorldCtlRtC.ctl_rt_C_of_AR (route (C): no VIS0 / OWNED_RO) at the
                      callee's AR (ly', S') and the kept arodata.
       FRAC is RE-ESTABLISHED at the post-call memory in ONE lemma, f36c_frac_mem, which walks FRAC's conjuncts
       generically (f36c_frac_walk): the announced trailer q64 m (fr + 4088) (flag_addr ..) (a Theorem Labs lane 05:56Z: LAST
       conjunct) lies in the owned frame [fr, fr + 4096), which the callee's journal keeps (its frames clause), and is
       kept with no edit.  The callee writes only its window [sp - 9136, sp), its own side-stack frames and their
       shadow; nothing in [fr + 4088, fr + 4096).

   SECTION HYPOTHESES (exact text below)
   - RELRO_IMG, LAWS, TFIB_SYMS: ACtl.v Section Ctl's (a3c6b7b35017 :183-238), same order (TFIB_LIB, XN_LIB, LS and
     the two callee constants are mirrored but unused, so the closed lemma does not take them; Batch3's RELRO_KIND_NAME,
     RELRO_FRAMES, MO_LE, KREPLY and KPARSE are left out: unused, and as Section facts in scope a tactic (lia) could
     pick one up and so change the lemma's arguments).
   - RELRO_CAT: ACtl.v's own Hypothesis RELRO_CAT (a3c6b7b35017 :205, Batch3; owner a Theorem Labs lane), same name and text:
     the catalogue lies in the read-only span.  True at ACtl.v's RLO / RHI = 0x9e380 / 0xa07c8 (CAT = 0x9e800,
     11 * 296 = 3256).  The table sits in the rw- segment [0x9e000, 0xa1000), so in_roP needs the span.
   - GLOBS, CM_GLOB : cm_glob_stmt GLOBS = In (A_CM_TBL, CM_ROWS) GLOBS in a Theorem Labs lane's own names: the runtime's
     registered-globals table of a Theorem Labs lane's spec (its Section variable GLOBS) holds the catalogue; owner: whoever
     fixes GLOBS with a Theorem Labs lane's HGM (a Theorem Labs lane / the walk top).
   - CM_SPEC : A.Prog.C_reac_box_catalogue_match.treac_box_catalogue_match_spec (SK := A.AE2k.tfib_sink_head)
     B RLO RHI GLOBS: a Theorem Labs lane's constant itself (lib/A/Prog/C_reac_box_catalogue_match.v:116, the statement-only
     file, blob 7d25cf12319 (the blob this tree had at release c5e779efe8c), taken by path (from a working branch 43728b681c5) onto this branch until
     a Theorem Labs lane's glue base carries it).  Owner a Theorem Labs lane (pb_reac_box_catalogue_match discharges it).
   - ROUTE (C) (L3; a shell from a working branch 8ce82d7e310; ACtlCut.v:243): ctl_from's runtime premise is
     A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 (was ACtlCut.ctl_rt mem3).  The stage reads no shadow byte from it (Hrt is
     unused; the callee spec CM_SPEC takes no shadow_rw), and the exit's ctl_rt_C B ly' S' mem' is a Theorem Labs lane's
     PROVED A.ProgWorldCtlRtC.ctl_rt_C_of_AR, cited by name; so VIS0 / OWNED_RO are no longer Section hypotheses.

   NAMES: every lib/Reusable and lib/Lib module is Required from its own directory and used through a full-path
   Module alias (a Theorem Labs lane 05:28Z: 160 + 15 twins).  getr / mkst / seg_rom / cfg_at only through those aliases.

   BUILD STATE: type-check on 5da74c9c931, closure reaches no stand-in (glue base 121bf608343: AE2k / AF0m /
   AF0l / ACej / ACeh compiled from their own text, no port_core_refused substitution).  No Axiom, Parameter, Admitted
   or admit.
   START-UP VALUES READ: TFIB_SYMS's ts_owned / ts_errno (f36c_cat_not_owned); the same verdict holds on the record
   AF0m (a working branch e56483f863b AF0m.v:18, :2965-2981: the neighbours (0x9e7d0, 0x30) and
   (0x9f4b8, 0x328) touch the table exactly, errno 0x5db76c). *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YM05 YO09 YI04 YI16 YO0f YK04 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YA0n YA0nR YG00 YG01 YG0f YG0n YG0d YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YC5d YCbq YE01 YI00 YP09 APostBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF MState Regs6ss Mem Frame PropExec Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v AE2k Img0 AsanRT ACfn ACtlK ACtlCut ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AF0m ACeh ProgBridge ProgWorldCtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require SlotModel reac_box_catalogue_match_lib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require CtrlRo C_reac_box_catalogue_match.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcMatch RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F36 F36Fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require Kit.
(* lib/A/Prog/YC4b.v:23 (reached through a Theorem Labs lane's C_reac_box_catalogue_match.v) sets Zify.zify_convert_to_euclidean_division_equations_flag
   to false only Locally, so it does not reach this file. lia here needs the flag true: false is its Stdlib default in Rocq 9.2, and a Required file's global
   `Ltac ... ::=` can also set it (both measured: a Local redefinition does not pass through Require, a global one does). False takes mod / div away from lia
   (build 20261029T091735Z: `No applicable tactic` at F36_82820.v:300).  The value these proofs were checked with (true) is restored for THIS file only. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Local Open Scope Z_scope.

Module CK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module CK1b := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Module CI04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI04.
Module CO0f := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO0f.
Module CK04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.
Module CK0s := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK0s.
Module CA0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
Module CA0nR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.
Module CG00 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
Module CG01 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
Module CG0f := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
Module CG0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
Module CG0d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
Module CG0v := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0v.
Module CC5d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YC5d.
Module CCbq := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
Module CE01 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YE01.
Module CI00 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI00.
Module CP09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YP09.
Module CPB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.APostBase.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LRg := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LPE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Module LImg := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Image.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module SM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Module CML := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_catalogue_match_lib.
Module RMa := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcMatch.
Module RIM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.

(* The core's segment list, as ACtlCut.v and ACtl.v bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   The text the downstream F36 stages cite by name (single writer: this file): a Theorem Labs lane's premise
   In (A_CM_TBL, CM_ROWS) GLOBS of treac_box_catalogue_match_spec, in a Theorem Labs lane's own names (its GLOBS is a Section
   variable of the spec).  a Theorem Labs lane's A_CM_TBL takes its Section b's Context (the build measured rc), so this text does
   too: a caller's Context instances fill it, the same as the spec's (an unused one drops at End CmGlob). *)
Section CmGlob.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
        {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}.
Definition cm_glob_stmt (GLOBS : list (Z * Z)) : Prop :=
  In (A.Prog.C_reac_box_catalogue_match.A_CM_TBL, A.Prog.C_reac_box_catalogue_match.CM_ROWS) GLOBS.
End CmGlob.

Section GlueF36_82820.

(* ACtl.v's Section Ctl (a3c6b7b35017 :183-238), in its order; RELRO_CAT in ACtl.v's exact text and name.  Batch3's
   RELRO_KIND_NAME, RELRO_FRAMES, MO_LE, KREPLY and KPARSE are left out (unused; see the header). *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
        {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
        {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : CG0f.asyms.
Variable MT : CC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> CG0d.in_img segs a.
Hypothesis RELRO_CAT : RLO <= A.Prog.SlotModel.CAT /\ A.Prog.SlotModel.CAT + A.Prog.SlotModel.CAT_N * A.Prog.SlotModel.CAT_ROW <= RHI.
Hypothesis LAWS : CG0d.AR_laws segs B.
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.
Hypothesis TFIB_LIB : A.ACeh.TfibLib B.
Variable REAC_CTRL_IDENTITY_REPLY_K : Z.
Variable REAC_CTRL_PARSE_BC : Z.

(* ACtl.v's notation block, verbatim for the names this stage uses. *)
Local Notation ix_cut := A.ACtlCut.ix_cut.
Local Notation CF POST X :=
  (A.ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A828cc_at := (A.ACtlCutP.C_A828cc_at B).
Local Notation C_A828d8_at := (A.ACtlCutP.C_A828d8_at B).

(* ---------------------------------------------------------------------------------------------------------
   The callee's spec and the post-call runtime facts (sources in the header). *)

(* a Theorem Labs lane's registered-globals table holds the catalogue (cm_glob_stmt above, cited by name downstream), and
   a Theorem Labs lane's spec, cited by its own name. *)
Variable GLOBS : list (Z * Z).
Hypothesis CM_GLOB : cm_glob_stmt GLOBS.
Hypothesis CM_SPEC : A.Prog.C_reac_box_catalogue_match.treac_box_catalogue_match_spec (SK := A.AE2k.tfib_sink_head) B RLO RHI GLOBS.


(* Route (C): the exit's ctl_rt_C is a Theorem Labs lane's PROVED A.ProgWorldCtlRtC.ctl_rt_C_of_AR, cited by name at G5;
   it needs neither VIS0 nor OWNED_RO. *)

(* ---------------------------------------------------------------------------------------------------------
   Local helpers (statements listed in the report). *)

Lemma f36c_ulit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  apply Z.mod_small. exact Hz.
Qed.

(* A byte the core's view keeps, visible and present before, not an image byte: the raw byte is kept. *)
Lemma f36c_raw : forall (W W' : CA0n.world segs) (m m' : word -> option byte) (a : Z),
  0 <= a < 2 ^ 64 -> ~ CG0d.in_img segs a ->
  CG0n.apresent (CA0n.w_H W) m a -> CA0n.wle W W' ->
  CG0n.aview segs (CA0n.w_H W') m' a = CG0n.aview segs (CA0n.w_H W) m a ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros W W' m m' a Ha Hni (Hh & b & Hb) Hle E.
  assert (Hh' : CA0n.w_H W' (Z_to_bv 64 a) = false).
  { destruct (CA0n.w_H W' (Z_to_bv 64 a)) eqn:E'; [|reflexivity]. rewrite (Hle _ E') in Hh. discriminate. }
  unfold CG0n.aview, CP09.mbyte, CK04.mrestrict in E. cbv beta in E.
  rewrite Hh, Hh', Hb in E. cbv beta iota in E.
  rewrite (CCbq.seg_rom_none segs a Ha Hni) in E.
  rewrite Hb.
  destruct (m' (Z_to_bv 64 a)) as [c|] eqn:Ec; cbv delta [option_map] beta iota in E; [|discriminate].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma f36c_bytes_keep : forall (m m' : word -> option byte) a bs,
  LMem.bytes_at segs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  LMem.bytes_at segs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) Hk. split; [exact H0|]. split; [exact H1|].
  intros i Hi. unfold LMem.mrd, LMem.wa in *. rewrite Hk by lia. exact (H i Hi).
Qed.

Lemma f36c_addr_keep : forall (m m' : word -> option byte) p n,
  ART.addressable m p n ->
  (forall x, p <= x < p + n -> m' (Z_to_bv 64 (ART.shadow_addr x)) = m (Z_to_bv 64 (ART.shadow_addr x))) ->
  ART.addressable m' p n.
Proof.
  intros m m' p n (H0 & H1 & H2 & H) Hk. split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hok). split; [exact Ha|]. exists b. split; [|exact Hok].
  unfold LMem.mrd, LMem.wa in *. rewrite Hk by lia. exact Hb.
Qed.

Lemma f36c_stk_keep : forall (m m' : word -> option byte) lo hi,
  LFr.stk segs m lo hi ->
  (forall x, lo <= x < hi -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  LFr.stk segs m' lo hi.
Proof.
  intros m m' lo hi (H0 & H1 & H) Hk. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (H a Ha) as (Hw & b & Hb). unfold LMem.mrd, LMem.wa in *. split.
  - unfold wview in *. rewrite (Hk a Ha). exact Hw.
  - exists b. rewrite (Hk a Ha). exact Hb.
Qed.

Lemma f36c_spill_keep : forall (regs regs' : bvmap 5 word) (m m' : word -> option byte) A off v,
  A.ACtlCutP.spill regs m off v ->
  CK11.getr regs' 9 = CK11.getr regs 9 -> A.ACtlCut.rgv regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 ->
  0 <= off -> off + 8 <= 416 ->
  (forall x, A <= x < A + 416 -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  A.ACtlCutP.spill regs' m' off v.
Proof.
  intros regs regs' m m' A off v (A0 & HA0 & Hq) E9 HA HAl HAh Ho1 Ho2 Hk.
  unfold A.ACtlCutP.q64 in Hq.
  pose proof Hq as Hb. apply LMem.bytes_at_bound in Hb. rewrite LMem.length_le8 in Hb.
  assert (EA : A0 = A).
  { unfold A.ACtlCut.rgv in HA0, HA. rewrite HA in HA0.
    apply (f_equal bv_unsigned) in HA0. rewrite !Z_to_bv_unsigned in HA0.
    unfold bv_wrap, bv_modulus in HA0. change (2 ^ Z.of_N 64) with (2 ^ 64) in HA0.
    rewrite (Z.mod_small A) in HA0 by lia. Z.div_mod_to_equations. lia. }
  subst A0. exists A. split.
  - unfold A.ACtlCut.rgv in *. rewrite E9. exact HA.
  - unfold A.ACtlCutP.q64. apply (f36c_bytes_keep m m' _ _ Hq). rewrite LMem.length_le8.
    intros x Hx. apply Hk. lia.
Qed.

(* One spill of a bundle, kept across a step that keeps the spill window [A, A + 416). *)
Ltac f36c_sk H E9 HA HA0 HA1 KA :=
  exact (f36c_spill_keep _ _ _ _ _ _ _ H E9 HA HA0 HA1 ltac:(lia) ltac:(lia) KA).

(* lib/Lib bytes of a visible range, read through the core's view. *)
Lemma f36c_aview_of_bytes : forall (H : word -> bool) (m : word -> option byte) a (bs : list byte),
  LMem.bytes_at segs m a bs ->
  (forall i, (i < length bs)%nat -> H (Z_to_bv 64 (a + Z.of_nat i)) = false) ->
  forall i, (i < length bs)%nat ->
  CG0n.aview segs H m (a + Z.of_nat i) = Some (bv_unsigned (nth i bs (Z_to_bv 8 0))).
Proof.
  intros H m a bs (_ & _ & Hb) Hv i Hi.
  pose proof (Hb i Hi) as E. rewrite (nth_error_nth' bs (Z_to_bv 8 0) Hi) in E.
  unfold LMem.mrd, LMem.wa in E.
  unfold CG0n.aview, CP09.mbyte, CK04.mrestrict. cbv beta. rewrite (Hv i Hi). cbv beta iota.
  exact (f_equal (option_map (fun b : byte => bv_unsigned b)) E).
Qed.

Lemma f36c_nth_map_u : forall (bs : list byte) j,
  nth j (map (fun b : byte => bv_unsigned b) bs) 0 = bv_unsigned (nth j bs (Z_to_bv 8 0)).
Proof.
  induction bs as [|b bs IH]; intros [|j]; cbn [nth map]; [reflexivity | reflexivity | reflexivity | apply IH].
Qed.

Lemma f36c_le_byte1 : forall b : byte, Z_to_bv 8 (CO0f.le_byte (bv_unsigned b) 1 0) = b.
Proof.
  intros b. unfold CO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. pose proof (bv_unsigned_in_range 8 b) as Hr. unfold bv_modulus in Hr.
  change (2 ^ Z.of_N 8) with 256 in Hr. change (2 ^ 8) with 256. rewrite !Z.mod_small by lia.
  apply stdpp.bitvector.definitions.Z_to_bv_bv_unsigned.
Qed.

Lemma f36c_garr8_of_aview : forall (H : word -> bool) (m : word -> option byte) a (bs : list byte),
  (forall i, (i < length bs)%nat ->
     CG0n.aview segs H m (a + Z.of_nat i) = Some (bv_unsigned (nth i bs (Z_to_bv 8 0)))) ->
  CI00.garr8 segs (CK04.mrestrict H m) a (map (fun b : byte => bv_unsigned b) bs).
Proof.
  intros H m a bs Hv j Hj. rewrite length_map in Hj.
  rewrite f36c_nth_map_u.
  pose proof (bv_unsigned_in_range 8 (nth j bs (Z_to_bv 8 0))) as Hr. unfold bv_modulus in Hr.
  change (2 ^ Z.of_N 8) with 256 in Hr.
  split; [|lia].
  intros k Hk. assert (k = 0%nat) by lia. subst k.
  replace (a + Z.of_nat j + Z.of_nat 0) with (a + Z.of_nat j) by lia.
  pose proof (Hv j Hj) as E. unfold CG0n.aview in E. cbv beta in E.
  destruct (CP09.mbyte segs (CK04.mrestrict H m) (a + Z.of_nat j)) as [c|] eqn:Ec;
    cbv delta [option_map] beta iota in E; [|discriminate].
  injection E as E. assert (Hc : c = nth j bs (Z_to_bv 8 0)) by (apply bv_eq; exact E). subst c.
  f_equal. symmetry. apply f36c_le_byte1.
Qed.

(* The image bytes CM_TBL, byte by byte. *)
Lemma f36c_image_nth : forall n A0 bs, LImg.image_bytes segs A0 n = Some bs ->
  forall i, (i < n)%nat -> CK11.seg_rom segs (Z_to_bv 64 (A0 + Z.of_nat i)) = nth_error bs i.
Proof.
  induction n as [|n IH]; intros A0 bs H i Hi; [lia|].
  cbn [LImg.image_bytes] in H.
  match type of H with context [LPE.seg_rom segs ?w] => destruct (LPE.seg_rom segs w) as [b|] eqn:E1 end;
    cbv beta iota in H; [|discriminate].
  match type of H with context [LImg.image_bytes segs ?a' n] =>
    destruct (LImg.image_bytes segs a' n) as [bs'|] eqn:E2 end; cbv beta iota in H; [|discriminate].
  injection H as <-.
  destruct i as [|i].
  - cbn [nth_error]. change (Z.of_nat 0) with 0. rewrite Z.add_0_r. exact E1.
  - cbn [nth_error]. replace (A0 + Z.of_nat (S i)) with (A0 + 1 + Z.of_nat i) by lia.
    apply IH; [exact E2 | lia].
Qed.

(* A saved word of lib/Lib bytes, visible, read as the core's rdword. *)
Lemma f36c_rdword_le8 : forall (H : word -> bool) (m : word -> option byte) a (w : word),
  LMem.bytes_at segs m a (LMem.le8 w) ->
  (forall i, 0 <= i < 8 -> H (Z_to_bv 64 (a + i)) = false) ->
  CG0d.rdword (CG0n.aview segs H m) a = Some (bv_unsigned w).
Proof.
  intros H m a w Hb Hv.
  assert (E : forall i, (i < 8)%nat ->
            CG0n.aview segs H m (a + Z.of_nat i) = Some (bv_unsigned (nth i (LMem.le8 w) (Z_to_bv 8 0)))).
  { intros i Hi. apply (f36c_aview_of_bytes H m a _ Hb); [| rewrite LMem.length_le8; exact Hi].
    intros i' Hi'. rewrite LMem.length_le8 in Hi'. apply Hv. lia. }
  unfold CG0d.rdword.
  replace a with (a + Z.of_nat 0) at 1 by lia.
  replace (a + 1) with (a + Z.of_nat 1) by lia. replace (a + 2) with (a + Z.of_nat 2) by lia.
  replace (a + 3) with (a + Z.of_nat 3) by lia. replace (a + 4) with (a + Z.of_nat 4) by lia.
  replace (a + 5) with (a + Z.of_nat 5) by lia. replace (a + 6) with (a + Z.of_nat 6) by lia.
  replace (a + 7) with (a + Z.of_nat 7) by lia.
  rewrite !E by lia. cbv beta iota.
  unfold LMem.le8, word_to_le_bytes. cbn [Z_to_le_bytes nth].
  rewrite !Z_to_bv_unsigned. f_equal.
  pose proof (bv_unsigned_in_range 64 w) as Hr. unfold bv_modulus in Hr. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hr.
  set (z := bv_unsigned w) in *.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  assert (H7 : z / 256 / 256 / 256 / 256 / 256 / 256 / 256 < 256).
  { change (2 ^ 64) with (256 * 256 * 256 * 256 * 256 * 256 * 256 * 256) in Hr.
    repeat (apply Z.div_lt_upper_bound; [lia|]). lia. }
  rewrite (Z.mod_small (z / 256 / 256 / 256 / 256 / 256 / 256 / 256))
    by (split; [repeat (apply Z.div_pos; [|lia]); lia | exact H7]).
  pose proof (Z.div_mod z 256 ltac:(lia)) as E0.
  pose proof (Z.div_mod (z / 256) 256 ltac:(lia)) as E1.
  pose proof (Z.div_mod (z / 256 / 256) 256 ltac:(lia)) as E2.
  pose proof (Z.div_mod (z / 256 / 256 / 256) 256 ltac:(lia)) as E3.
  pose proof (Z.div_mod (z / 256 / 256 / 256 / 256) 256 ltac:(lia)) as E4.
  pose proof (Z.div_mod (z / 256 / 256 / 256 / 256 / 256) 256 ltac:(lia)) as E5.
  pose proof (Z.div_mod (z / 256 / 256 / 256 / 256 / 256 / 256) 256 ltac:(lia)) as E6.
  lia.
Qed.

(* The core's read-only view of the pre is kept by a journal with FP = []. *)
Lemma f36c_aro_keep : forall STK sp0 ly S W mem md own ly' S' W' mem' md' k,
  CCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  CE01.arodata_okS segs B RLO RHI (CG0n.aview segs (CA0n.w_H W) mem) ->
  CE01.arodata_okS segs B RLO RHI (CG0n.aview segs (CA0n.w_H W') mem').
Proof.
  intros STK sp0 ly S W mem md own ly' S' W' mem' md' k HJ HR a Hro Ho He.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  rewrite (F3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He |].
  - destruct Hro as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr] | exact (RELRO_IMG a Hgot)].
  - apply (CCbq.fp_spares_closed (SK := A.AE2k.tfib_sink_head)). intros Ho'. exact (CCbq.sink_closed_nil Ho').
Qed.

(* A live block's bytes are addressable in ctrl's sense, from the core's AR shadow law. *)
Lemma f36c_addr_of_block : forall ly S (W : CA0n.world segs) (mem : word -> option byte) md p n,
  CG0n.AR segs B ly S W mem md -> In (p, n) (CG0d.ablocks B ly S) ->
  ART.addressable mem p (CG00.req_size n).
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (CG0d.al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & Hp4 & Hpc & Happ & _ & _ & Hn).
  destruct (CG0d.al_shadow _ _ LAWS ly S W mem md p n HAR Hin) as (Hbs & _).
  destruct Hbs as (Hp8 & Hn0 & Hsh).
  pose proof CCbq.asan_consts as (C1 & _).
  assert (Hr1 : 1 <= CG00.req_size n) by (unfold CG00.req_size; destruct (Z.eqb_spec n 0); lia).
  unfold CG0f.in_app, CG0f.kLowShadowBeg, CG0f.kHighMemBeg, CG0f.ASAN_CEIL in Happ.
  split; [lia|]. split; [lia|]. split; [unfold ART.APPMEM_END; lia|].
  intros i Hi. split.
  - unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END. lia.
  - set (q := i / 8).
    assert (Hq : 0 <= q < (CG00.req_size n + 7) / 8) by (unfold q; lia).
    pose proof (Hsh q Hq) as Hs. unfold CG0v.shadow_of_addr in Hs.
    assert (Ea : CG0f.SHADOW_OFF + p / 8 + q = ART.shadow_addr (p + i))
      by (unfold q, ART.shadow_addr, ART.ASAN_K, CG0f.SHADOW_OFF; lia).
    rewrite Ea in Hs.
    assert (Hx : 0 <= ART.shadow_addr (p + i) < 2 ^ 64)
      by (unfold ART.shadow_addr, ART.ASAN_K; lia).
    assert (Hxi : ~ CG0d.in_img segs (ART.shadow_addr (p + i))).
    { intros Hi'. pose proof (A.ACtlG.Kit.kit_segs_low _ Hi') as Hl. unfold CG0f.kLowMemEnd in Hl.
      unfold ART.shadow_addr, ART.ASAN_K in Hl. lia. }
    unfold CG0n.aview in Hs. cbv beta in Hs.
    destruct (CP09.mbyte segs (CK04.mrestrict (CA0n.w_H W) mem) (ART.shadow_addr (p + i))) as [b|] eqn:Eb;
      cbv delta [option_map] beta iota in Hs; [|discriminate].
    injection Hs as Hs.
    exists b. split.
    + unfold CP09.mbyte, CK04.mrestrict in Eb. cbv beta in Eb.
      destruct (CA0n.w_H W (Z_to_bv 64 (ART.shadow_addr (p + i)))) eqn:Eh.
      * cbv iota in Eb. rewrite (CCbq.seg_rom_none segs _ Hx Hxi) in Eb. discriminate.
      * cbv iota in Eb. unfold LMem.mrd, LMem.wa. exact Eb.
    + assert (Hu : 0 <= bv_unsigned b < 8).
      { rewrite Hs. destruct (q <? CG00.req_size n / 8); [lia | apply Z.mod_pos_bound; lia]. }
      assert (Hsg : bv_signed b = bv_unsigned b).
      { unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
        change (2 ^ Z.of_N 8) with 256. change (256 / 2) with 128.
        rewrite Z.mod_small by lia. lia. }
      rewrite Hsg. unfold ART.shadow_ok.
      revert Hs. destruct (q <? CG00.req_size n / 8) eqn:Ec; intros Hs.
      * left. exact Hs.
      * right. apply Z.ltb_ge in Ec. rewrite Hs. unfold q in Ec.
        split; [|pose proof (Z.mod_pos_bound (CG00.req_size n) 8 ltac:(lia)); lia].
        clear - Ec Hi Hp8. Z.div_mod_to_equations. lia.
Qed.

(* RELRO_CAT, pointwise. *)
Lemma f36c_relro_cat : forall a,
  A.Prog.SlotModel.CAT <= a < A.Prog.SlotModel.CAT + A.Prog.SlotModel.CAT_N * A.Prog.SlotModel.CAT_ROW ->
  RLO <= a < RHI.
Proof. intros a Ha. destruct RELRO_CAT as [R1 R2]. lia. Qed.

(* The catalogue bytes are neither an owned static nor errno (TFIB_SYMS). *)
Lemma f36c_cat_not_owned : forall a, 0x9e800 <= a < 0x9e800 + 3256 ->
  ~ Exists (CG0n.in_zr a) (CG0f.as_owned_static B) /\ ~ (CG0f.as_errno B <= a < CG0f.as_errno B + 4).
Proof.
  intros a Ha. rewrite (A.AF0m.ts_owned B TFIB_SYMS), (A.AF0m.ts_errno B TFIB_SYMS).
  unfold A.AF0m.TFIB_ERRNO. split; [|lia].
  intros HE. apply Exists_exists in HE as (r & Hr & Hz). unfold CG0n.in_zr in Hz.
  unfold A.AF0m.Tfib_owned_static in Hr.
  repeat (destruct Hr as [<- | Hr]; [cbn [fst snd] in Hz; lia |]). destruct Hr.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The cut bundles, kept across a step that keeps the spill window, the owned frame and its shadow. *)

Lemma f36c_PRO_keep : forall cx fr A (regs regs' : bvmap 5 word) (m m' : word -> option byte),
  A.ACtlCutP.PRO cx fr regs m ->
  CK11.getr regs' 9 = CK11.getr regs 9 -> A.ACtlCut.rgv regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 ->
  (forall x, A <= x < A + 416 -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  (forall x, fr <= x < fr + 4096 -> m' (Z_to_bv 64 (ART.shadow_addr x)) = m (Z_to_bv 64 (ART.shadow_addr x))) ->
  (forall x, A.ACtlCut.c_p cx <= x < A.ACtlCut.c_p cx + A.ACtlCut.c_n cx -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  (0 < A.ACtlCut.c_n cx -> ART.addressable m' (A.ACtlCut.c_p cx) (A.ACtlCut.c_n cx)) ->
  Z.of_nat (length (A.ACtlCut.c_in cx)) = A.ACtlCut.c_n cx ->
  A.ACtlCutP.PRO cx fr regs' m'.
Proof.
  intros cx fr A regs regs' m m' H E9 HA HA0 HA1 KA KS KI HAI Hlen.
  destruct H as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pad & Pin & Pg & P184 & P256 & P264 &
    P272 & P32).
  split; [f36c_sk P40 E9 HA HA0 HA1 KA|]. split; [f36c_sk P120 E9 HA HA0 HA1 KA|].
  split; [f36c_sk P136 E9 HA HA0 HA1 KA|]. split; [f36c_sk P160 E9 HA HA0 HA1 KA|].
  split; [f36c_sk P168 E9 HA HA0 HA1 KA|]. split; [f36c_sk P176 E9 HA HA0 HA1 KA|].
  split; [f36c_sk P208 E9 HA HA0 HA1 KA|]. split; [f36c_sk P248 E9 HA HA0 HA1 KA|].
  split; [apply (f36c_addr_keep _ _ _ _ Pad); intros x Hx; apply KS; lia|].
  split; [apply (f36c_bytes_keep _ _ _ _ Pin); rewrite Hlen; exact KI|].
  split; [exact HAI|].
  split; [f36c_sk P184 E9 HA HA0 HA1 KA|]. split; [f36c_sk P256 E9 HA HA0 HA1 KA|].
  split; [f36c_sk P264 E9 HA HA0 HA1 KA|]. split; [f36c_sk P272 E9 HA HA0 HA1 KA|].
  f36c_sk P32 E9 HA HA0 HA1 KA.
Qed.

Lemma f36c_FLC_keep : forall fr A (regs regs' : bvmap 5 word) (m m' : word -> option byte),
  A.ACtlCutP.FLC fr regs m ->
  CK11.getr regs' 9 = CK11.getr regs 9 -> A.ACtlCut.rgv regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 ->
  (forall x, A <= x < A + 416 -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  (forall x, fr <= x < fr + 4096 -> m' (Z_to_bv 64 (ART.shadow_addr x)) = m (Z_to_bv 64 (ART.shadow_addr x))) ->
  A.ACtlCutP.FLC fr regs' m'.
Proof.
  intros fr A regs regs' m m' H E9 HA HA0 HA1 KA KS.
  destruct H as (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & Ca72 & Ca38 & C72 & C64 & C56 & C48).
  split; [f36c_sk C256 E9 HA HA0 HA1 KA|]. split; [f36c_sk C184 E9 HA HA0 HA1 KA|].
  split; [f36c_sk C192 E9 HA HA0 HA1 KA|]. split; [f36c_sk C80 E9 HA HA0 HA1 KA|].
  split; [f36c_sk C88 E9 HA HA0 HA1 KA|]. split; [f36c_sk C96 E9 HA HA0 HA1 KA|].
  split; [f36c_sk C272 E9 HA HA0 HA1 KA|]. split; [f36c_sk C264 E9 HA HA0 HA1 KA|].
  split; [apply (f36c_addr_keep _ _ _ _ Ca72); intros x Hx; apply KS; unfold A.ACtlCutP.fragb in Hx; lia|].
  split; [apply (f36c_addr_keep _ _ _ _ Ca38); intros x Hx; apply KS; lia|].
  split; [f36c_sk C72 E9 HA HA0 HA1 KA|]. split; [f36c_sk C64 E9 HA HA0 HA1 KA|].
  split; [f36c_sk C56 E9 HA HA0 HA1 KA|]. f36c_sk C48 E9 HA HA0 HA1 KA.
Qed.

Lemma f36c_FLSI_keep : forall cx j fr A (regs regs' : bvmap 5 word) (m m' : word -> option byte),
  A.ACtlCutP.FLSI cx j fr regs m ->
  CK11.getr regs' 9 = CK11.getr regs 9 -> A.ACtlCut.rgv regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 ->
  (forall x, A <= x < A + 416 -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  (forall x, fr <= x < fr + 4096 -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  (forall x, fr <= x < fr + 4096 -> m' (Z_to_bv 64 (ART.shadow_addr x)) = m (Z_to_bv 64 (ART.shadow_addr x))) ->
  (forall x, A.ACtlCut.c_p cx <= x < A.ACtlCut.c_p cx + A.ACtlCut.c_n cx -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  ART.addressable m' (A.ACtlCut.c_p cx) (A.ACtlCut.c_n cx) ->
  Z.of_nat (length (A.ACtlCut.c_in cx)) = A.ACtlCut.c_n cx ->
  A.ACtlCutP.FLSI cx j fr regs' m'.
Proof.
  intros cx j fr A regs regs' m m' H E9 HA HA0 HA1 KA KF KS KI HAI Hlen.
  destruct H as ((HP & S128 & Hst & S144 & Ha) & S216 & S224 & S248 & (Hia & Hib) & HC).
  split.
  { split; [exact (f36c_PRO_keep cx fr A regs regs' m m' HP E9 HA HA0 HA1 KA KS KI (fun _ => HAI) Hlen)|].
    split; [f36c_sk S128 E9 HA HA0 HA1 KA|].
    split; [apply (f36c_stk_keep _ _ _ _ Hst); intros x Hx; apply KF; unfold A.ACtlCutP.FRAME_BYTES in Hx; lia|].
    split; [f36c_sk S144 E9 HA HA0 HA1 KA|].
    apply (f36c_addr_keep _ _ _ _ Ha); intros x Hx; apply KS; lia. }
  split; [f36c_sk S216 E9 HA HA0 HA1 KA|]. split; [f36c_sk S224 E9 HA HA0 HA1 KA|].
  split; [f36c_sk S248 E9 HA HA0 HA1 KA|].
  split; [split; [exact HAI | apply (f36c_bytes_keep _ _ _ _ Hib); rewrite Hlen; exact KI]|].
  exact (f36c_FLC_keep fr A regs regs' m m' HC E9 HA HA0 HA1 KA KS).
Qed.

Lemma f36c_FLSX_keep : forall cx j phi fr A (regs regs' : bvmap 5 word) (m m' : word -> option byte),
  A.ACtlCutP.FLSX cx j phi fr regs m ->
  CK11.getr regs' 9 = CK11.getr regs 9 -> CK11.getr regs' 18 = CK11.getr regs 18 ->
  CK11.getr regs' 22 = CK11.getr regs 22 -> CK11.getr regs' 23 = CK11.getr regs 23 ->
  CK11.getr regs' 25 = CK11.getr regs 25 ->
  A.ACtlCut.rgv regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 ->
  (forall x, A <= x < A + 416 -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  (forall x, fr <= x < fr + 4096 -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  (forall x, fr <= x < fr + 4096 -> m' (Z_to_bv 64 (ART.shadow_addr x)) = m (Z_to_bv 64 (ART.shadow_addr x))) ->
  (forall x, A.ACtlCut.c_p cx <= x < A.ACtlCut.c_p cx + A.ACtlCut.c_n cx -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  ART.addressable m' (A.ACtlCut.c_p cx) (A.ACtlCut.c_n cx) ->
  Z.of_nat (length (A.ACtlCut.c_in cx)) = A.ACtlCut.c_n cx ->
  (forall x, phi <= x < phi + A.ACtlCutP.flen cx j -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  A.ACtlCutP.FLSX cx j phi fr regs' m'.
Proof.
  intros cx j phi fr A regs regs' m m' H E9 E18 E22 E23 E25 HA HA0 HA1 KA KF KS KI HAI Hlen KP.
  destruct H as (HI & R18 & R22 & R23 & R25 & Hrec & S152 & S280).
  split; [exact (f36c_FLSI_keep cx j fr A regs regs' m m' HI E9 HA HA0 HA1 KA KF KS KI HAI Hlen)|].
  split; [unfold A.ACtlCut.rgv in *; rewrite E18; exact R18|].
  split; [unfold A.ACtlCut.rgv in *; rewrite E22; exact R22|].
  split; [unfold A.ACtlCut.rgv in *; rewrite E23; exact R23|].
  split; [unfold A.ACtlCut.rgv in *; rewrite E25; exact R25|].
  split.
  { intros H50. destruct (Hrec H50) as (Hp0 & Hp1 & Hg & Hph & Hl).
    assert (Lg : length (SM.t_g (A.ACtlCut.c_in cx) j) = 50%nat) by (unfold SM.t_g; apply SM.fr50_length).
    split; [exact Hp0|]. split; [exact Hp1|].
    split; [apply (f36c_bytes_keep _ _ _ _ Hg); rewrite Lg; intros x Hx; apply KP; lia|].
    split; [apply (f36c_bytes_keep _ _ _ _ Hph); intros x Hx; apply KP; lia | exact Hl]. }
  split; [f36c_sk S152 E9 HA HA0 HA1 KA | f36c_sk S280 E9 HA HA0 HA1 KA].
Qed.

Lemma f36c_LK_keep : forall cx fr j (regs regs' : bvmap 5 word) (m m' : word -> option byte),
  A.ACtlCutP.LK cx fr j regs m -> CK11.getr regs' 21 = CK11.getr regs 21 ->
  (forall x, fr <= x < fr + 4096 -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  A.ACtlCutP.LK cx fr j regs' m'.
Proof.
  intros cx fr j regs regs' m m' (Hj & R21 & HO) E21 KF.
  split; [exact Hj|]. split; [unfold A.ACtlCut.rgv in *; rewrite E21; exact R21|].
  unfold A.ACtlCutP.OURb in *. apply (f36c_bytes_keep _ _ _ _ HO). rewrite SM.OUR_length.
  intros x Hx. apply KF. lia.
Qed.

Lemma f36c_LT_keep : forall cx fr j A (regs regs' : bvmap 5 word) (m m' : word -> option byte),
  A.ACtlCutP.LT cx fr j regs m ->
  CK11.getr regs' 9 = CK11.getr regs 9 -> A.ACtlCut.rgv regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 ->
  (forall x, A <= x < A + 416 -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  (forall x, fr <= x < fr + 4096 -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  (forall x, fr <= x < fr + 4096 -> m' (Z_to_bv 64 (ART.shadow_addr x)) = m (Z_to_bv 64 (ART.shadow_addr x))) ->
  A.ACtlCutP.LT cx fr j regs' m'.
Proof.
  intros cx fr j A regs regs' m m' H E9 HA HA0 HA1 KA KF KS.
  unfold A.ACtlCutP.LT, A.ACtlCutP.IFS, A.ACtlCutP.IDj, A.ACtlCutP.FGj, A.ACtlCutP.FSj, A.ACtlCutP.IDb,
    A.ACtlCutP.FGb, A.ACtlCutP.FSb, A.ACtlCutP.IDBe, A.ACtlCutP.FGBe in *.
  destruct H as ((Hid & Hidok) & (Hfg & Hfgok) & (S104 & S112 & Hbody & Hab & HFI)).
  pose proof (A.Prog.Seg.F36.f36_tID_len (A.ACtlCut.c_in cx) (S j)) as L1. unfold RIM.ID_SIZE in L1.
  pose proof (A.Prog.Seg.F36.f36_tFG_len (A.ACtlCut.c_in cx) (S j)) as L2.
  pose proof (A.Prog.Seg.F36.f36_fs_body_len (A.ACtlCut.c_in cx) (S j)) as L3.
  split; [split; [apply (f36c_bytes_keep _ _ _ _ Hid); rewrite L1; intros x Hx; apply KF; lia | exact Hidok]|].
  split; [split; [apply (f36c_bytes_keep _ _ _ _ Hfg); rewrite L2; intros x Hx; apply KF; lia | exact Hfgok]|].
  split; [f36c_sk S104 E9 HA HA0 HA1 KA|]. split; [f36c_sk S112 E9 HA HA0 HA1 KA|].
  split; [apply (f36c_bytes_keep _ _ _ _ Hbody); intros x Hx; apply KF; lia|].
  split; [apply (f36c_addr_keep _ _ _ _ Hab); intros x Hx; apply KS; lia | exact HFI].
Qed.

(* FRAC re-established at a new memory (ACtlCutP.v:980-994) across a step that keeps the stack above sp, the owned
   frame and its shadow.  The ONE lemma of this file that RE-ESTABLISHES FRAC.  It walks FRAC's conjuncts generically
   (f36c_frac_walk): a register / numeric conjunct is the old one, a byte conjunct is kept by the frame / stack /
   frame-shadow range it lies in.  So FRAC's announced q64 m (fr + 4088) (flag_addr ..) conjunct (inside the owned
   frame [fr, fr + 4096), which the callee's journal keeps) needs no edit here. *)
Lemma f36c_saved_len : forall cx, Z.of_nat (length (A.ACtlCutP.saved_bytes cx)) = 104.
Proof. intros cx. reflexivity. Qed.

Lemma f36c_fsh_len : Z.of_nat (Z.to_nat A.ACtlCutP.FRAME_SHADOW) = 392.
Proof. reflexivity. Qed.

Ltac f36c_frac_conj Hc KSt KF KFS :=
  first
    [ exact Hc
    | apply (f36c_bytes_keep _ _ _ _ Hc); rewrite ?LMem.length_le8; intros ?x ?Hx;
      first [ apply KSt; lia | apply KF; lia ]
    | let sh := fresh "sh" in let Hsh := fresh "Hsh" in let Hshl := fresh "Hshl" in
      destruct Hc as (sh & Hsh & Hshl); exists sh; split; [| exact Hshl];
      apply (f36c_bytes_keep _ _ _ _ Hsh); rewrite Hshl, f36c_fsh_len; unfold A.ACtlCutP.Sfr;
      intros ?x ?Hx; apply KFS; lia
    | apply (f36c_bytes_keep _ _ _ _ Hc); rewrite f36c_saved_len; intros ?x ?Hx; apply KSt; lia ].

Ltac f36c_frac_walk H KSt KF KFS :=
  lazymatch type of H with
  | _ /\ _ =>
      let Hc := fresh "Hc" in let Hr := fresh "Hr" in
      destruct H as [Hc Hr]; split; [f36c_frac_conj Hc KSt KF KFS | f36c_frac_walk Hr KSt KF KFS]
  | _ => f36c_frac_conj H KSt KF KFS
  end.

Lemma f36c_frac_mem : forall cx fr sel (regs : bvmap 5 word) (m m' : word -> option byte),
  A.ACtlCutP.FRAC B cx fr sel regs m ->
  (forall x, CG0d.spZ regs <= x < A.ACtlCut.c_sp cx -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  (forall x, fr <= x < fr + 4096 -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  (forall y, ART.shadow_addr fr <= y < ART.shadow_addr fr + 512 -> m' (Z_to_bv 64 y) = m (Z_to_bv 64 y)) ->
  A.ACtlCutP.FRAC B cx fr sel regs m'.
Proof.
  intros cx fr sel regs m m' H KSt KF KFS.
  assert (FB : A.ACtlCutP.FRAME_BYTES = 3136) by reflexivity.
  unfold A.ACtlCutP.FRAC, A.ACtlCutP.q64 in *.
  destruct H as (A & sp & H). exists A, sp.
  f36c_frac_walk H KSt KF KFS.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_F36_82820 : forall POST (j : nat),
  CF POST (ix_cut C_A828d8_at [Z.of_nat j]) -> CF POST (ix_cut C_A828cc_at [Z.of_nat j]).
Proof.
  intros POST j HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat j] (ix_cut; C_A828cc_at, ACtlCutP.v:2909-2920). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [A.ACtlCut.cut_body A.ACtlCutP.C_A828cc_at A.ACtlCutP.ixn nth] in Hb.
  rewrite Znat.Nat2Z.id in Hb.
  destruct Hb as (phi & HP & HFRAC & Hn & Hj & HHB & HFLSI & HLK & HFLSX & R20 & HLT).
  pose proof Hk as Hk0.
  cbv beta iota delta [A.ACtlCut.cut_kmax A.ACtlCut.ix_cut A.ACtlCutP.C_A828cc_at A.ACtlCutP.ixn nth] in Hk.
  rewrite Znat.Nat2Z.id in Hk.
  (* the entry (ctl_base), the journal, the frame *)
  pose proof HB as ((Hpre0 & _ & _ & _ & Hpn & Hlen0 & _ & _ & Hnev0 & _ & Haro0 & _) & _).
  pose proof Hpre0 as (_ & _ & _ & Hgp0 & _ & _ & _ & Hch0 & _).
  pose proof HJ as (HAR3 & Hly & _ & _ & _ & _ & Hnev & _ & F1 & _ & _ & _ & _ & Hwin & Hstk & _).
  pose proof Hstk as (Hsm16 & _ & Hceil0 & Hslo0 & Hshi0 & H47 & _ & Htop0 & Htop1).
  pose proof Hly as (_ & _ & _ & _ & _ & EF & _ & _ & Etop & _).
  pose proof CCbq.asan_consts as (C1 & _).
  assert (ELL : A.ACfn.LLVMF_STK = 32768) by reflexivity.
  assert (Hin6 : In (6, A.ACtlCut.c_fpos cx) (CG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (CCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (A.ACtlCut.c_fpos cx) HAR3 Hin6)
    as (Hf4096 & Hfceil & _).
  assert (Efr : fr = CG0f.frame_addr (A.ACtlCut.c_ly cx) 6 (A.ACtlCut.c_fpos cx)) by (apply HL; left; reflexivity).
  assert (Efr3 : CG0f.frame_addr ly3 6 (A.ACtlCut.c_fpos cx) = fr)
    by (rewrite Efr; unfold CG0f.frame_addr; rewrite EF; reflexivity).
  assert (E6 : CG00.fs_frame_bytes 6 = 4096) by reflexivity.
  rewrite Efr3 in Hf4096. rewrite Efr3, E6 in Hfceil.
  (* FRAC, FLSX, HB *)
  pose proof HFRAC as (A & sp & E2 & Hspm & Esp & E4 & R8 & R9 & E3 & R19 & R26 & Hfrm & HAm & HAc & HspA & HfrA &
    HA416 & Hsp4096 & Happ & _).
  assert (Hsv : LMem.bytes_at segs mem3 (A.ACtlCut.c_sp cx - 104) (A.ACtlCutP.saved_bytes cx)).
  { clear - HFRAC. destruct HFRAC as (? & ? & HH).
    repeat match goal with H : _ /\ _ |- _ => destruct H end. assumption. }
  assert (FB : A.ACtlCutP.FRAME_BYTES = 3136) by reflexivity.
  assert (AE : ART.APPMEM_END = 0x800000000000) by reflexivity.
  pose proof HFLSX as (_ & R18 & R22 & R23 & R25 & Hrec & _ & _).
  pose proof HHB as (Hphi0 & _).
  (* the turn's block (phi, flen j) and the input block *)
  assert (Hinphi : In (phi, A.ACtlCutP.flen cx j) (CG0d.ablocks B ly3 S3)).
  { eapply Permutation_in; [exact (Permutation_sym HP)|]. apply in_or_app. right. left. reflexivity. }
  destruct (CG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR3 Hinphi) as (_ & Hph4 & Hphc & _ & Hphpres & _ & Hfl).
  assert (Hreqf : A.ACtlCutP.flen cx j <= CG00.req_size (A.ACtlCutP.flen cx j))
    by (unfold CG00.req_size; destruct (Z.eqb_spec (A.ACtlCutP.flen cx j) 0); lia).
  (* G3: the cut's configuration in the run's state form, the walk moved to the run's canonical map. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (A.ACtlCut.cut_pc (ix_cut C_A828cc_at [Z.of_nat j])) with 0x828cc.
  apply (CA0nR.SRr_xregs_eqv segs W3 (LRg.mkR_of regs3) regs3 CK11.fp_regs (Z_to_bv 64 0x828cc) CK11.fp_csr None
           mem3 (CK11.seg_rom segs) md3 (POST cx));
    [| exact (LRg.xregs_eqv_sym _ _ (LRg.mkR_of_eqv regs3))].
  unfold LRg.mkR_of.
  (* G4: f36_evt_call_pre_F, no memory access: the empty footprint. *)
  eapply (CA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 A.ACtlG.Kit.kit_RNG0 _ (POST cx)).
  { apply A.ProgBridge.fevt_of_evtF.
    apply (A.Prog.Seg.F36Fs.f36_evt_call_pre_F A.ACtlG.Kit.kit_RNG0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ _ _ _ _ CK11.fp_regs CK11.fp_csr mem3). }
  { intros ? ? Hrng0. unfold A.ACtlG.Kit.kit_RNG0 in Hrng0. destruct Hrng0. }
  intros ms' md' HQ0 Hsbm. cbv beta in HQ0. subst ms'.
  match goal with |- context [LMS.MS ?R _ _ _ _ _ _] => set (Rc := R) end.
  (* the callee entry map: ra = 0x828d8, a0 = s7, a1 = s2, every other register the cut's *)
  assert (K1 : CK11.getr Rc 1 = Z_to_bv 64 0x828d8) by reflexivity.
  assert (K2 : CK11.getr Rc 2 = CK11.getr regs3 2) by reflexivity.
  assert (K3 : CK11.getr Rc 3 = CK11.getr regs3 3) by reflexivity.
  assert (K4 : CK11.getr Rc 4 = CK11.getr regs3 4) by reflexivity.
  assert (K8 : CK11.getr Rc 8 = CK11.getr regs3 8) by reflexivity.
  assert (K9 : CK11.getr Rc 9 = CK11.getr regs3 9) by reflexivity.
  assert (K10 : CK11.getr Rc 10 = CK11.getr regs3 23) by reflexivity.
  assert (K11 : CK11.getr Rc 11 = CK11.getr regs3 18) by reflexivity.
  assert (K18 : CK11.getr Rc 18 = CK11.getr regs3 18) by reflexivity.
  assert (K19 : CK11.getr Rc 19 = CK11.getr regs3 19) by reflexivity.
  assert (K20 : CK11.getr Rc 20 = CK11.getr regs3 20) by reflexivity.
  assert (K21 : CK11.getr Rc 21 = CK11.getr regs3 21) by reflexivity.
  assert (K22 : CK11.getr Rc 22 = CK11.getr regs3 22) by reflexivity.
  assert (K23 : CK11.getr Rc 23 = CK11.getr regs3 23) by reflexivity.
  assert (K25 : CK11.getr Rc 25 = CK11.getr regs3 25) by reflexivity.
  assert (K26 : CK11.getr Rc 26 = CK11.getr regs3 26) by reflexivity.
  assert (HspZ : CG0d.spZ Rc = sp) by (unfold CG0d.spZ; rewrite K2; exact Esp).
  assert (Hs0 : CG0d.s0Z Rc = A.ACtlCut.c_sp cx).
  { unfold CG0d.s0Z. rewrite K8. unfold A.ACtlCut.rgv in R8. rewrite R8. apply f36c_ulit. lia. }
  (* the cut's journal across the run's model materialization (ajournal_exec, as A5.v) *)
  assert (HJ' : CCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (A.ACtlCut.c_sp cx) []
                  (A.ACtlCut.c_ly cx) (A.ACtlCut.c_S cx) (A.ACtlCut.c_W cx) (A.ACtlCut.c_mem cx) (A.ACtlCut.c_md cx)
                  (A.ACtlCut.own6 cx) ly3 S3 W3 mem3 md' k).
  { eapply (CCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
      [exact HJ | intros x _; reflexivity | apply CK1b.mem_grows_refl | intros x _; reflexivity
      | exact Hsbm | intros a Ha; destruct Ha]. }
  (* the read-only view at the call *)
  pose proof (f36c_aro_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Haro0) as Haro3.
  (* the frame-pointer chain at s0 = c_sp (afn_pre's achain) *)
  assert (Hch : exists ch, CCbq.achain ly3 (CG0n.aview segs (CA0n.w_H W3) mem3) sp (A.ACtlCut.c_sp cx) ch).
  { destruct (Z_le_gt_dec (CG0f.ly_top ly3 - 16) (A.ACtlCut.c_sp cx)) as [Hhi | Hlo].
    - exists []. left. split; [right; left; exact Hhi | reflexivity].
    - exists [(A.ACtlCut.c_sp cx, A.ACfn.RA_LLVMF, CG0d.s0Z (A.ACtlCut.c_regs cx))].
      apply (CCbq.achain_ly_top (A.ACtlCut.c_ly cx)); [exact Etop |].
      apply (CCbq.achain_push (A.ACtlCut.c_ly cx) (CG0n.aview segs (CA0n.w_H (A.ACtlCut.c_W cx)) (A.ACtlCut.c_mem cx))).
      + exact Hch0.
      + lia.
      + intros a Ha. apply F1; lia.
      + pose proof (A.Prog.Seg.F36.f36_ba_sub mem3 (A.ACtlCut.c_sp cx - 104) (A.ACtlCutP.saved_bytes cx) 96 8 Hsv
                      ltac:(change (length (A.ACtlCutP.saved_bytes cx)) with 104%nat; lia)) as Hs8.
        replace (firstn 8 (skipn 96 (A.ACtlCutP.saved_bytes cx))) with (LMem.le8 (Z_to_bv 64 A.ACfn.RA_LLVMF))
          in Hs8 by reflexivity.
        replace (A.ACtlCut.c_sp cx - 104 + Z.of_nat 96) with (A.ACtlCut.c_sp cx - 8) in Hs8 by lia.
        replace (Some A.ACfn.RA_LLVMF) with (Some (bv_unsigned (Z_to_bv 64 A.ACfn.RA_LLVMF)))
          by (rewrite f36c_ulit; [reflexivity | unfold A.ACfn.RA_LLVMF; lia]).
        apply (f36c_rdword_le8 _ _ _ _ Hs8). intros i Hi.
        exact (proj1 (Hwin (A.ACtlCut.c_sp cx - 8 + i) ltac:(lia))).
      + pose proof (A.Prog.Seg.F36.f36_ba_sub mem3 (A.ACtlCut.c_sp cx - 104) (A.ACtlCutP.saved_bytes cx) 88 8 Hsv
                      ltac:(change (length (A.ACtlCutP.saved_bytes cx)) with 104%nat; lia)) as Hs8.
        replace (firstn 8 (skipn 88 (A.ACtlCutP.saved_bytes cx)))
          with (LMem.le8 (CK11.getr (A.ACtlCut.c_regs cx) 8)) in Hs8 by reflexivity.
        replace (A.ACtlCut.c_sp cx - 104 + Z.of_nat 88) with (A.ACtlCut.c_sp cx - 16) in Hs8 by lia.
        apply (f36c_rdword_le8 _ _ _ _ Hs8). intros i Hi.
        exact (proj1 (Hwin (A.ACtlCut.c_sp cx - 16 + i) ltac:(lia))).
      + unfold A.ACfn.RA_LLVMF. lia.
      + lia.
      + clear - Hsm16. Z.div_mod_to_equations. lia.
      + rewrite <- Etop. lia.
      + lia. }
  destruct Hch as (ch & Hch).
  (* THE CALL: a Theorem Labs lane's spec at the callee entry, its statement-level constants unfolded in place (conversion
     only; the premises then read in numerals). *)
  pose proof CM_SPEC as CMS.
  unfold A.Prog.C_reac_box_catalogue_match.treac_box_catalogue_match_spec,
    A.Prog.C_reac_box_catalogue_match.treac_box_catalogue_match_post, A.Prog.C_reac_box_catalogue_match.CM_STK,
    A.Prog.C_reac_box_catalogue_match.EV_CM, A.Prog.C_reac_box_catalogue_match.LIVE_CM,
    A.Prog.C_reac_box_catalogue_match.CM_ROWS, A.Prog.C_reac_box_catalogue_match.CM_TBLZ,
    A.Prog.CtrlRo.IMG_LO, A.Prog.CtrlRo.IMG_HI in CMS.
  change A.Prog.C_reac_box_catalogue_match.A_CM_TBL with 0x9e800 in CMS.
  change A.Prog.C_reac_box_catalogue_match.A_catalogue_matchP with 0x84498 in CMS.
  change (CA0n.SRr segs W3 (CG0d.cfg_at segs 0x84498 Rc mem3 md') (POST cx)).
  eapply CA0n.SRr_bind.
  { apply (CMS ly3 S3 W3 Rc mem3 md' ch phi (A.ACtlCutP.flen cx j) (SM.t_g (A.ACtlCut.c_in cx) j)).
    - (* afn_pre, from the journal (YCbq.afn_pre_at) *)
      eapply CCbq.afn_pre_at with (o := sp - A.ACtlCut.c_sp cx).
      + exact HJ'.
      + rewrite HspZ. lia.
      + clear - Hspm Hsm16. Z.div_mod_to_equations. lia.
      + lia.
      + lia.
      + lia.
      + rewrite K1. unfold CK0s.ret_ok. vm_compute. reflexivity.
      + unfold CG0d.raZ. rewrite K1. rewrite f36c_ulit by lia. lia.
      + rewrite K3, E3. exact Hgp0.
      + rewrite K4, E4. reflexivity.
      + rewrite HspZ, Hs0. exact Hch.
    - (* arodata_okS *)
      exact Haro3.
    - (* a0 = phi *)
      rewrite K10. exact R23.
    - (* a1 = flen j *)
      rewrite K11. exact R18.
    - lia.
    - unfold CG00.MALLOC_MAX in Hfl. lia.
    - unfold SM.t_g. apply SM.fr50_length.
    - intros H50. exists (A.ACtlCutP.flen cx j). split; [exact Hinphi | lia].
    - (* the record's 50 bytes *)
      intros H50. apply f36c_garr8_of_aview. intros i Hi.
      destruct (Hrec H50) as (_ & _ & Hg & _ & _).
      apply (f36c_aview_of_bytes _ _ _ _ Hg); [|exact Hi].
      intros i' Hi'. assert (Lg : length (SM.t_g (A.ACtlCut.c_in cx) j) = 50%nat) by (unfold SM.t_g; apply SM.fr50_length).
      rewrite Lg in Hi'. exact (proj1 (proj1 (Hphpres (phi + Z.of_nat i') ltac:(lia)))).
    - (* the catalogue bytes *)
      apply f36c_garr8_of_aview. intros i Hi. rewrite CML.CM_TBL_len in Hi.
      destruct (f36c_cat_not_owned (0x9e800 + Z.of_nat i) ltac:(lia)) as (Hno & Hne).
      rewrite (Haro3 (0x9e800 + Z.of_nat i)); [| right; apply f36c_relro_cat;
        unfold A.Prog.SlotModel.CAT, A.Prog.SlotModel.CAT_N, A.Prog.SlotModel.CAT_ROW; lia | exact Hno | exact Hne].
      rewrite (f36c_image_nth 3256%nat 0x9e800 CML.CM_TBL CML.CM_TBL_eq i Hi).
      rewrite (nth_error_nth' CML.CM_TBL (Z_to_bv 8 0)) by (rewrite CML.CM_TBL_len; exact Hi).
      reflexivity.
    - exact CM_GLOB.
    - lia.
    - lia.
    - intros a Ha. destruct (f36c_cat_not_owned a Ha) as (Hno & Hne).
      split; [|split; [exact Hno | exact Hne]].
      unfold CPB.in_roP. right. apply f36c_relro_cat.
      unfold A.Prog.SlotModel.CAT, A.Prog.SlotModel.CAT_N, A.Prog.SlotModel.CAT_ROW. lia.
    - rewrite HF. vm_compute. reflexivity.
    - rewrite HF. vm_compute. reflexivity.
    - rewrite HF. vm_compute. reflexivity.
    - unfold A.ACfn.EV_LIB, CG00.EV_MAX in *. lia.
    - pose proof HAR3 as (HM & _). destruct HM. match goal with H : CG01.Wf _ S3 |- _ => destruct H end. lia. }
  (* G5: the callee's return at ra = 0x828d8, the exit cut C_A828d8_at. *)
  intros W2 c2 Hwle2 HQ.
  destruct HQ as (ly' & S' & regs' & mem' & md'' & Ec & HJc & HPres & H10' & HPerm).
  subst c2.
  change (CA0n.SRr segs W2
            (CG0d.cfg_at segs (A.ACtlCut.cut_pc (ix_cut C_A828d8_at [Z.of_nat j])) regs' mem' md'') (POST cx)).
  pose proof HJc as (HAR' & _ & _ & Hwlec & _ & Hfrsc & _ & _ & G1 & G2 & _ & G4 & _ & _ & _ & _ & _).
  assert (NFP : forall a, ~ CI04.inFP [] a) by (intros a (r & Hr & _); destruct Hr).
  (* the composed journal (YCbq.ajournal_sub, nf = []) *)
  assert (HJ2 : CCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (A.ACtlCut.c_sp cx) []
                  (A.ACtlCut.c_ly cx) (A.ACtlCut.c_S cx) (A.ACtlCut.c_W cx) (A.ACtlCut.c_mem cx) (A.ACtlCut.c_md cx)
                  ([] ++ A.ACtlCut.own6 cx) ly' S' W2 mem' md'' (k + 0)).
  { eapply (CCbq.ajournal_sub segs B LAWS A.ACtlG.Kit.kit_segs_low);
      [exact HJ' | exact HJc | rewrite HspZ; lia | rewrite HspZ; lia | intros a Hf; exfalso; exact (NFP a Hf)]. }
  rewrite Z.add_0_r in HJ2.
  (* raw bytes kept by the callee: the stack above sp, the owned frame and its shadow, the live blocks *)
  assert (KSt : forall x, sp <= x < A.ACtlCut.c_sp cx -> mem' (Z_to_bv 64 x) = mem3 (Z_to_bv 64 x)).
  { intros x Hx. apply (f36c_raw W3 W2 mem3 mem' x).
    - lia.
    - intros Hi. pose proof (A.ACtlG.Kit.kit_segs_low x Hi) as Hl. unfold CG0f.kLowMemEnd in Hl. lia.
    - apply Hwin. lia.
    - exact Hwlec.
    - apply G1; [lia | rewrite HspZ; lia]. }
  destruct (CG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (A.ACtlCut.c_fpos cx) HAR3 Hin6) as (_ & _ & Hfb & Hfsh).
  rewrite Efr3, E6 in Hfb, Hfsh.
  assert (KF : forall x, fr <= x < fr + 4096 -> mem' (Z_to_bv 64 x) = mem3 (Z_to_bv 64 x)).
  { intros x Hx. apply (f36c_raw W3 W2 mem3 mem' x).
    - lia.
    - apply (CCbq.frm_img segs B LAWS ly3 S3 W3 mem3 md3 6 (A.ACtlCut.c_fpos cx) x HAR3 Hin6).
      rewrite Efr3, E6. lia.
    - exact (proj1 (Hfb x Hx)).
    - exact Hwlec.
    - apply (G4 6 (A.ACtlCut.c_fpos cx) x Hin6); [| apply NFP].
      left. unfold CG0n.in_zr, CCbq.frame_rng. cbn [fst snd]. rewrite Efr3, E6. lia. }
  assert (Esh : ART.shadow_addr fr = CG0f.shadow_addr fr)
    by (unfold ART.shadow_addr, ART.ASAN_K, CG0f.shadow_addr, CG0f.SHADOW_OFF; lia).
  assert (KFS : forall y, ART.shadow_addr fr <= y < ART.shadow_addr fr + 512 -> mem' (Z_to_bv 64 y) = mem3 (Z_to_bv 64 y)).
  { intros y Hy. rewrite Esh in Hy. apply (f36c_raw W3 W2 mem3 mem' y).
    - unfold CG0f.shadow_addr, CG0f.SHADOW_OFF in Hy. lia.
    - intros Hi. pose proof (A.ACtlG.Kit.kit_segs_low y Hi) as Hl.
      unfold CG0f.kLowMemEnd, CG0f.shadow_addr, CG0f.SHADOW_OFF in *. lia.
    - replace y with (CG0f.shadow_addr fr + (y - CG0f.shadow_addr fr)) by lia.
      exact (proj1 (Hfsh (y - CG0f.shadow_addr fr) ltac:(lia))).
    - exact Hwlec.
    - apply (G4 6 (A.ACtlCut.c_fpos cx) y Hin6); [| apply NFP].
      right. unfold CG0n.in_zr. cbn [fst snd]. rewrite Efr3, E6. lia. }
  assert (KFSx : forall x, fr <= x < fr + 4096 ->
            mem' (Z_to_bv 64 (ART.shadow_addr x)) = mem3 (Z_to_bv 64 (ART.shadow_addr x))).
  { intros x Hx. apply KFS. clear - Hx Hfrm. unfold ART.shadow_addr, ART.ASAN_K. Z.div_mod_to_equations. lia. }
  assert (KB : forall p n x, In (p, n) (CG0d.ablocks B ly3 S3) -> In (p, n) (CG0d.ablocks B ly' S') ->
            p <= x < p + CG00.req_size n -> mem' (Z_to_bv 64 x) = mem3 (Z_to_bv 64 x)).
  { intros p n x H3 H' Hx.
    destruct (CG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 p n HAR3 H3) as (_ & Hp4 & Hpc & _ & Hpp & _).
    apply (f36c_raw W3 W2 mem3 mem' x).
    - lia.
    - exact (CCbq.blk_img segs B LAWS ly3 S3 W3 mem3 md3 p n x HAR3 H3 Hx).
    - exact (proj1 (Hpp x Hx)).
    - exact Hwlec.
    - pose proof (G2 p n (x - p) H3 H' ltac:(lia) (NFP _)) as E.
      replace (p + (x - p)) with x in E by lia. exact E. }
  assert (Hinphi' : In (phi, A.ACtlCutP.flen cx j) (CG0d.ablocks B ly' S'))
    by (eapply Permutation_in; [exact (Permutation_sym HPerm) | exact Hinphi]).
  assert (KP : forall x, phi <= x < phi + A.ACtlCutP.flen cx j -> mem' (Z_to_bv 64 x) = mem3 (Z_to_bv 64 x))
    by (intros x Hx; apply (KB _ _ x Hinphi Hinphi'); lia).
  (* the input block (c_p, c_n): kept bytes, addressable at the callee's post *)
  assert (Hlen : Z.of_nat (length (A.ACtlCut.c_in cx)) = A.ACtlCut.c_n cx) by (symmetry; exact Hlen0).
  pose proof HFLSI as (_ & _ & _ & _ & (Hia & _) & _).
  assert (KI : forall x, A.ACtlCut.c_p cx <= x < A.ACtlCut.c_p cx + A.ACtlCut.c_n cx ->
            mem' (Z_to_bv 64 x) = mem3 (Z_to_bv 64 x)).
  { intros x Hx. destruct Hpn as [(Hn0 & _) | (Hnp & Hinp)]; [lia|].
    assert (Hinp3 : In (A.ACtlCut.c_p cx, A.ACtlCut.c_n cx) (CG0d.ablocks B ly3 S3))
      by (eapply Permutation_in; [exact (Permutation_sym HP)|]; apply in_or_app; left; exact Hinp).
    assert (Hinp' : In (A.ACtlCut.c_p cx, A.ACtlCut.c_n cx) (CG0d.ablocks B ly' S'))
      by (eapply Permutation_in; [exact (Permutation_sym HPerm) | exact Hinp3]).
    apply (KB _ _ x Hinp3 Hinp').
    unfold CG00.req_size. destruct (Z.eqb_spec (A.ACtlCut.c_n cx) 0); lia. }
  assert (HAI : ART.addressable mem' (A.ACtlCut.c_p cx) (A.ACtlCut.c_n cx)).
  { destruct Hpn as [(Hn0 & _) | (Hnp & Hinp)].
    - apply (f36c_addr_keep _ _ _ _ Hia). intros x Hx. lia.
    - assert (Hinp3 : In (A.ACtlCut.c_p cx, A.ACtlCut.c_n cx) (CG0d.ablocks B ly3 S3))
        by (eapply Permutation_in; [exact (Permutation_sym HP)|]; apply in_or_app; left; exact Hinp).
      assert (Hinp' : In (A.ACtlCut.c_p cx, A.ACtlCut.c_n cx) (CG0d.ablocks B ly' S'))
        by (eapply Permutation_in; [exact (Permutation_sym HPerm) | exact Hinp3]).
      pose proof (f36c_addr_of_block ly' S' W2 mem' md'' _ _ HAR' Hinp') as Ha.
      replace (CG00.req_size (A.ACtlCut.c_n cx)) with (A.ACtlCut.c_n cx) in Ha
        by (unfold CG00.req_size; destruct (Z.eqb_spec (A.ACtlCut.c_n cx) 0); lia).
      exact Ha. }
  (* registers across the callee: aregs_preserved, then the run's map *)
  assert (P2 : CK11.getr regs' 2 = CK11.getr regs3 2)
    by (rewrite <- K2; exact (HPres 2 ltac:(unfold CG0d.acallee_saved; lia))).
  assert (P3 : CK11.getr regs' 3 = CK11.getr regs3 3)
    by (rewrite <- K3; exact (HPres 3 ltac:(unfold CG0d.acallee_saved; lia))).
  assert (P4 : CK11.getr regs' 4 = CK11.getr regs3 4)
    by (rewrite <- K4; exact (HPres 4 ltac:(unfold CG0d.acallee_saved; lia))).
  assert (P8 : CK11.getr regs' 8 = CK11.getr regs3 8)
    by (rewrite <- K8; exact (HPres 8 ltac:(unfold CG0d.acallee_saved; lia))).
  assert (P9 : CK11.getr regs' 9 = CK11.getr regs3 9)
    by (rewrite <- K9; exact (HPres 9 ltac:(unfold CG0d.acallee_saved; lia))).
  assert (P18 : CK11.getr regs' 18 = CK11.getr regs3 18)
    by (rewrite <- K18; exact (HPres 18 ltac:(unfold CG0d.acallee_saved; lia))).
  assert (P19 : CK11.getr regs' 19 = CK11.getr regs3 19)
    by (rewrite <- K19; exact (HPres 19 ltac:(unfold CG0d.acallee_saved; lia))).
  assert (P20 : CK11.getr regs' 20 = CK11.getr regs3 20)
    by (rewrite <- K20; exact (HPres 20 ltac:(unfold CG0d.acallee_saved; lia))).
  assert (P21 : CK11.getr regs' 21 = CK11.getr regs3 21)
    by (rewrite <- K21; exact (HPres 21 ltac:(unfold CG0d.acallee_saved; lia))).
  assert (P22 : CK11.getr regs' 22 = CK11.getr regs3 22)
    by (rewrite <- K22; exact (HPres 22 ltac:(unfold CG0d.acallee_saved; lia))).
  assert (P23 : CK11.getr regs' 23 = CK11.getr regs3 23)
    by (rewrite <- K23; exact (HPres 23 ltac:(unfold CG0d.acallee_saved; lia))).
  assert (P25 : CK11.getr regs' 25 = CK11.getr regs3 25)
    by (rewrite <- K25; exact (HPres 25 ltac:(unfold CG0d.acallee_saved; lia))).
  assert (P26 : CK11.getr regs' 26 = CK11.getr regs3 26)
    by (rewrite <- K26; exact (HPres 26 ltac:(unfold CG0d.acallee_saved; lia))).
  assert (HspZ' : CG0d.spZ regs' = sp) by (unfold CG0d.spZ; rewrite P2; exact Esp).
  assert (KA : forall x, A <= x < A + 416 -> mem' (Z_to_bv 64 x) = mem3 (Z_to_bv 64 x))
    by (intros x Hx; apply KSt; lia).
  assert (HA0 : 0 <= A) by lia.
  assert (HA1 : A + 416 <= 2 ^ 64) by lia.
  apply (HX cx [Z.of_nat j] fr k ly' S' W2 regs' mem' md'' HB).
  - (* journal *)
    exact HJ2.
  - (* frames: the callee's journal keeps frames S3 = own6 *)
    rewrite Hfrsc. exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: k unchanged, the same kmax *)
    exact Hk0.
  - (* the exit body, C_A828d8_at (ACtlCutP.v:2924-2935), at the same turn j *)
    cbv beta iota zeta delta [A.ACtlCut.cut_body A.ACtlCut.ix_cut A.ACtlCutP.C_A828d8_at A.ACtlCutP.ixn nth].
    split; [reflexivity|].
    rewrite Znat.Nat2Z.id.
    exists phi.
    split; [eapply Permutation_trans; [exact HPerm | exact HP]|].
    split.
    { apply (f36c_frac_mem cx fr fr regs' mem3 mem');
        [exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 regs' mem3 HFRAC P2 P3 P4 P8 P9 P19 P26)
        | intros x Hx; apply KSt; lia | exact KF | exact KFS]. }
    split; [exact Hn|]. split; [exact Hj|].
    split.
    { split; [exact Hphi0|].
      replace (A.ACtlK.a_size (A.ACtlCutP.flen cx j)) with (CG00.req_size (A.ACtlCutP.flen cx j))
        by (unfold A.ACtlK.a_size, CG00.req_size; destruct (Z.eqb_spec (A.ACtlCutP.flen cx j) 0); lia).
      exact (f36c_addr_of_block ly' S' W2 mem' md'' _ _ HAR' Hinphi'). }
    split; [exact (f36c_FLSI_keep cx j fr A regs3 regs' mem3 mem' HFLSI P9 R9 HA0 HA1 KA KF KFSx KI HAI Hlen)|].
    split; [exact (f36c_LK_keep cx fr j regs3 regs' mem3 mem' HLK P21 KF)|].
    split; [exact (f36c_FLSX_keep cx j phi fr A regs3 regs' mem3 mem' HFLSX P9 P18 P22 P23 P25 R9 HA0 HA1 KA KF
                     KFSx KI HAI Hlen KP)|].
    split; [unfold A.ACtlCut.rgv in *; rewrite P20; exact R20|].
    split; [unfold A.ACtlCut.rgv; rewrite H10'; reflexivity|].
    exact (f36c_LT_keep cx fr j A regs3 regs' mem3 mem' HLT P9 R9 HA0 HA1 KA KF KFSx).
  - (* ctl_rt_C B ly' S' mem': ctl_rt_C_of_AR at the callee's AR and the kept read-only view *)
    exact (A.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly' S' W2 mem' md'' HAR'
             (f36c_aro_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 Haro0)).
Qed.

End GlueF36_82820.
