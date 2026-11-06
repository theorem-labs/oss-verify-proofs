(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumA.v, with its module paths and module names changed; 1213 of its 1267 lines of code are new or changed and 724 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/BTxString.v, with its module paths and module names changed; 125 of its 164 lines of code are new or changed and 1228 lines of the source are left out. *)
(* fuzz_preset image A, slice S7b: put_string's walk (A 0x8836c, 221 instructions). The segments are
   PRW_put_string_base.v (kit-level lemmas, the entry state, the put call site, the join-point invariants),
   PRW_put_string_a.v (ps_seg_a: the entry through the opening-quote put to the loop head / tail join),
   PRW_put_string_l.v (ps_loop: the loop), PRW_put_string_e.v (ps_esc_run: the escape), PRW_put_string_t.v
   (ps_tail_run: the tail).
   rule 24: proves function put_string (CONFIRM R24Writer 2026-10-30). put_string_holds below is the kit's text
   tput_string_specX (the kit's cut 7cdbb61b5fa0, PRH_FnWriter.v d89d3c67b78c :574-649), composed
   from ps_seg_a (continuations KH / KT) with ps_loop (its escape continuation ps_esc_run, its tail continuation
   ps_tail_run). The memory invariant of the segments is instantiated ONCE here: Pm := `memnorm mem -> memnorm m` for
   put_string's entry memory mem (YSRrMemnorm.srr_inv_laws_imp over srr_inv_laws_memnorm_k, srr_inv_call_imp), so the
   post is fpostWFm's (S7a_put.v's put_holds, the same step). The float state: the entry float state is the Section's
   fx (x_fx X := fx); the loop and the escape run at the float state of their join, so the callee texts and rows read
   after the snprintf row (put, __wrap_strlen, __asan_memcpy, the snprintf row) are hypotheses at every float state.
   KIT: the kit's cut 7cdbb61b5fa0 (its PRH_* texts and its engine: int102 f44822dff082's with the P'' set). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomPre YGcfRoomKeep YCbqG YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcallMx YGcallx YGcallSx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcallSnp YGcallSnpCk.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CallerJ PRW_S7bKit PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S7a_WriterRet S7a_WriterLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_put_string_base PRW_put_string_a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_put_string_t PRW_put_string_l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_put_string_e.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterSpec WriterApp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.

(* image A's generated numbers (PRH_Img.v) are the PrhImg the texts read *)
#[local] Existing Instance prh_img_A.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {SK : YI16.sink_head}.
(* The kit's non-primary room invariant (PRH_Base.v PrhRoomLive, owner a Theorem Labs lane) *)
Context {RL : PrhRoomLive}.
Context {PA : PAImg A_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val _ A_prog_listing PA).
#[local] Abbreviation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val _ A_prog_listing PA A_TEXT).

(* ---- the segments' Section hypotheses, the same texts and owners (PRW_put_string_a.v / _l.v / _e.v / _t.v); the
   callee texts and rows a segment reads after a float-changing call are taken at every float state ---- *)
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis TL : PALib B.
Hypothesis Hent : SIGMA AS_put_string = BASE + AF_put_string.
Hypothesis Huar : as_got_uar B = VAL (A_OBJ 1).
Hypothesis Hobj : forall i, 0 <= i < 8 ->
  in_img SEGS (VAL (A_OBJ 0) + i) /\ in_img SEGS (VAL (A_OBJ 12) + i) /\ in_img SEGS (VAL (A_OBJ 1) + i).
Hypothesis HOBJ : ps_objs_disj.
Hypothesis HUARC : ps_uar_ok B.
Hypothesis segs_low : forall a, in_img SEGS a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env SEGS B.
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
Hypothesis SMX : forall ly S Hp W mem md cid, ARx ly S Hp W mem md -> 0 <= cid <= 10 ->
  count_cid cid (frames S) < fs_frames cid ->
  exists pos S', apath (stack_malloc cid S) [] (PFake cid pos, S') /\ (exists f, S' = set_fs f S) /\
    frames S' = (cid, pos) :: frames S /\ ~ In (cid, pos) (frames S).
Hypothesis ASM0 : astack_malloc_realizes_xm SEGS B ARx 0.
Hypothesis Hsm0 : pc_stack_malloc (as_code B) 0 = SIGMA AS___asan_stack_malloc_0.
Hypothesis HW : prh_head_wide.
Hypothesis ASO : asyms_ok B.
Hypothesis HIMGSH : ARx_img_shadow_vis SEGS ARx.
Hypothesis HFHULL : ARx_frame_hull_vis SEGS ARx.
Hypothesis HPAB : pa_lo = IMG_LO /\ pa_hi = IMG_TOP.
Hypothesis PST_ok : forall a, Exists (in_zr a) (@prh_pst prh_img_A) ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis HPSTRO : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) (@prh_pst prh_img_A).
Variable CTX0 : list (list Z).
(* put's text (the kit's tput_specX; S7a_put.v put_holds), at every float state *)
Hypothesis PUT : forall fx0 : YK11.FPState, tput_specX (fx := fx0) (PI := prh_img_A) (PA := PA) B ARx SK CTX0.
Hypothesis HLIT17 : forall ly' S' Hp' (W' : world SEGS) m' md',
  ARx ly' S' Hp' W' m' md' ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') m') ->
  src_rd W' m' (ps_str 65) [34] /\ kept_at B [] (ps_str 65) 1.
Hypothesis HLIT85 : ps_lit_fact B ARx 85 [92; 116; 0].
Hypothesis HLIT87 : ps_lit_fact B ARx 87 [92; 110; 0].
Hypothesis HLIT91 : ps_lit_fact B ARx 91 [92; 114; 0].
Hypothesis HLIT93 : ps_lit_fact B ARx 93 [92; 37; 99; 0].
Hypothesis HLIT89 : ps_lit_fact B ARx 89 [92; 117; 37; 48; 52; 120; 0].
(* the escape's rows (PRW_put_string_e.v), at every float state *)
Hypothesis ASTRLEN : forall fx0 : YK11.FPState,
  astrlen_realizes_xrom (fx := fx0) SEGS B ARx pa_relro_lo pa_relro_hi (SIGMA AS___wrap_strlen).
Hypothesis AMCPY : forall fx0 : YK11.FPState,
  aintrin_realizes_xm (fx := fx0) SEGS B ARx OCpy (SIGMA AS___asan_memcpy).
Variables gcan can : Z.
Hypothesis SNPI : ps_snp_img B gcan can.
Hypothesis SNP : forall fx0 : YK11.FPState,
  YGcallSnp.asnprintf_realizes_xrom (fx := fx0) SEGS B ARx pa_relro_lo pa_relro_hi (YGcallSnpCk.FF_esc IMG_LO gcan)
    STK_RT_PRINTF gcan can IMG_LO IMG_TOP ps_snp_cr (SIGMA AS___wrap_snprintf).
(* the inline release's three laws (PRW_put_string_t.v; YGcallSx.v's Section x, owner a Theorem Labs lane) *)
Hypothesis ASFX : forall ly S Hp (W : world SEGS) mem md mem' md' cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aview SEGS (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> a <> flag_addr ly cid pos ->
     aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, aview SEGS (w_H W) mem a <> None -> aview SEGS (w_H W) mem' a <> None) ->
  m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
  (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
  ARx ly (stack_free_state cid pos S) Hp W mem' md'.
Hypothesis FFLX : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aowned B ly S (flag_addr ly cid pos) /\ (app_addr (flag_addr ly cid pos) /\ ~ in_img SEGS (flag_addr ly cid pos)).
Hypothesis SFX : forall ly S Hp (W : world SEGS) mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2.

(* ---- THE COMPOSITION ---- *)
Theorem put_string_holds : tput_string_specX (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK CTX0.
Proof.
intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own ly S Hp W regs mem md ch o s d buf st bs Lam peak ran.
intros HPRE HROOM HPOS HUNIV HLEN4 HCONS H10 H11 HCASE HREC HS0 HWIN Hol Hoh HOUT HLED HCSTR HKEPT HRUN HDISJ HFR HWMAX
  HMAX HLIVE.
set (Pm := fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m).
assert (PLAW : srr_inv_laws SEGS Pm)
  by exact (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)).
assert (PCALL : srr_inv_call SEGS Pm) by exact (srr_inv_call_imp SEGS mem).
set (X := mkPSX d ly S Hp W regs mem md o s bs buf st Lam peak ran rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own fx).
assert (Hpre : ps_pre B ARx CTX0 X ch).
{ exact (conj HPRE (conj HROOM (conj HPOS (conj HUNIV (conj H10 (conj H11 (conj HCASE (conj HREC (conj HWIN (conj Hol
    (conj Hoh (conj HOUT (conj HLED (conj HCSTR (conj HKEPT (conj HDISJ (conj HFR (conj HWMAX (conj HMAX (conj HLIVE
    (conj HCONS (conj HRUN HLEN4)))))))))))))))))))))). }
assert (HS0X : ps_s0 X) by exact HS0.
assert (HZ : YK0o.frm_zero (@YK11.fp_csr fx)) by (destruct HPRE as (_ & _ & _ & _ & Hz); exact Hz).
(* the tail at any float state of the loop (ps_tail_run) *)
assert (TAIL : psl_TAILC B ARx Pm X).
{ intros fxc Hzc Hkc pos j P lyc Sc Hpc Wc regsc memc mdc kc Ht.
  eapply (ps_tail_run (fx := fxc)); first [ exact (PUT _) | eassumption ]. }
(* the escape at any float state of the loop (ps_esc_run), its continuation the loop's re-poison join *)
assert (ESC : psl_ESCC B ARx Pm X).
{ intros fxc Hzc Hkc pos i P lyc Sc Hpc Wc regsc memc mdc kc He K.
  eapply ps_esc_run;
    first [ exact (PUT _) | exact (ASTRLEN _) | exact (AMCPY _) | exact (SNP _) | eassumption ]. }
(* the loop from any head *)
assert (LOOP : forall i, psl_HEADC B ARx Pm X i).
{ intros i. eapply ps_loop; first [ exact PUT | eassumption ]. }
apply (SRr'_mono SEGS (@YGcfRehidePost.RZ_cf rc) _ _ (ps_Qfin B ARx Pm X)).
- eapply (ps_seg_a (fx := fx)) with (X := X) (ch := ch).
  all: try (intros pos i j P lyc Sc Hpc Wc regsc memc mdc kc Hh;
            exact (LOOP i fx HZ (ps_fk_refl fx) pos j P lyc Sc Hpc Wc regsc memc mdc kc Hh)).
  all: try exact (TAIL fx HZ (ps_fk_refl fx)).
  all: first [ exact (PUT _) | reflexivity | (unfold Pm; cbv beta; intros Hm; exact Hm) | eassumption ].
- intros W' c' _ (HF & HPm).
  destruct HF as (fx' & ly' & S' & Hp' & regs' & mem' & md' & k & Ec & Hz' & Hk' & HJ & HWK & HAP & HQ).
  exists fx', ly', S', Hp', regs', mem', md', k.
  split; [exact Ec|]. split; [exact Hz'|]. split; [exact Hk'|]. split; [exact HJ|]. split; [exact HWK|].
  split; [exact HAP|]. split; [exact HQ|].
  subst c'. exact HPm.
Qed.

End d.

(* implicit-SK check (a Theorem Labs lane's rule): no plain YI5b.src0_sink_head may appear in the walk's lemmas *)
Set Printing All.
Print ps_put_call.
Print ps_put_step.
Print ps_seg_a.
Print ps_loop.
Print ps_esc_run.
Print ps_tail_run.
Unset Printing All.

(* implicit-FPState check (the internal file REFIT-WRITER.md): the Prop definitions that read a float state, with every implicit shown:
   ps_pre and ps_Qfin read only the ENTRY float state x_fx; ps_float the current one; the loop's continuations bind
   their own *)
Set Printing Implicit. Unset Printing Notations.
Print ps_pre.
Print ps_Qfin.
Print ps_float.
Print psl_HEADC.
Print psl_ESCC.
Set Printing Notations. Unset Printing Implicit.

Print Assumptions ps_put_step.
Print Assumptions ps_seg_a.
Print Assumptions ps_loop.
Print Assumptions ps_esc_run.
Print Assumptions ps_tail_run.
Print Assumptions put_string_holds.
