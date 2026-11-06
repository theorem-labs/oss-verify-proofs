(* reac_ctrl_classify_box_frame (fuzz_ctrl.asan 0x831b8, libreac v1.9.0, image A): the cgif-form glue that proves
   treac_ctrl_classify_box_frame_spec (lib/A/Prog/C_reac_ctrl_classify_box_frame.v).
   rule 24: no function proved as a new top claim.  The glue composes ctrl's two PROVED v1.9 stretches
   (lib/A/Prog/reac_ctrl_classify_box_frame_Fs_on.v, route (C)'s twin of reac_ctrl_classify_box_frame_Fs.v (not in this delivery):
   reac_ctrl_classify_box_frame_pre_call_F, [0x831b8 .. the jal at 0x831fc]; reac_ctrl_classify_box_frame_post_call_F_on,
   [0x83200 .. ret 0x8337c]), each lifted into the world walk by
   Reusable/YA0nR.v SRr_fevt_hid at RNG := ProgBridge.RNG_W (w_H W), with a Theorem Labs lane's treac_ctrl_parse_spec
   (lib/A/Prog/C_reac_ctrl_parse.v) applied at reac_ctrl_parse's entry (0x83578, ra = 0x83200) between them.
   GLUE CLOSURE RULE: the _F file and its closure (lib/Lib, lib/A/MemNorm*, lib/A/Img0, lib/A/AsanRT, ...) are Required
   QUALIFIED below and never Imported or Exported; lib/Lib's getr / mkst / seg_rom shadow YK11's, so every lib/Lib name
   is written through a module alias.  No statement of this file names a frame-route identifier outside the lift
   lemmas, whose start and end states are the proved stretches' own.
   mem_inv: the two stretches take ctrl's mem_inv (no byte of a read-only segment is present in memory), which the
   cgif world does not state.  The lifts run each stretch from MemNormP.normalize_P m (P := every byte), which drops
   exactly the read-only bytes and the unmapped bytes above TASK_SIZE and so has mem_inv, and carry the run back to m
   through MemNormP.step_accesses_rel_P (the same accesses, so the same footprint); the premise on m is ro_agree.
   ROUTE (C) (L3-recipe.md (a working note, not in this delivery), a Theorem Labs lane 14:2xZ): stretch 2 is applied in its _on form
   (reac_ctrl_classify_box_frame_post_call_F_on): its region of record, the two bcmp calls' range-check words, is fed
   from RT_used_of_AR_C's cut_shadow conjunct at the parse-return state (cls_sh_word_frame), so no universal shadow_rw
   and no AR_states_vis0_shadow is used; ro_agree comes from AR by ro_agree_of_AR (owned_ro proved). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
(* The six core modules that ctrl's lib/A/Reusable duplicates (YI04, YI16, YK11, YK1b, YM05, YO09) are Required, never
   Imported: this file's closure reaches both copies, so each use is written through the aliases K11 / M05 / I04 /
   I16 / K1b below (porter rule, a Theorem Labs lane 04:24Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YI04 YI16 YM05 YK1b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import APostBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YE00 YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04R YA0nR.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import PaTable CtrlList CtrlPa CtrlImg CtrlCallerJ.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcParse RcClassify.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import C_reac_ctrl_parse C_reac_ctrl_classify_box_frame.
(* Glue-only, Required and never Imported. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require PropExec MState Frame Mem Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF RngBytes Regs6ss.
(* route (C), TWIN-LEAF rule (16:02Z): the image-A normalization twins (a Theorem Labs lane's lib/A/MemNormP.v, the root
   lib/MemNormP.v's text over lib.A.MemNorm), not the root lib/MemNorm / lib/MemNormP. *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Img0 A.AsanRT A.ProgBridge A.BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.reac_ctrl_classify_box_frame_Fs_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.bcmp_wrap_c A.Prog.memcmp_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require reac_ctrl_classify_box_frame_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorldVisFrame A.ProgWorldVisHeap A.ProgWorldVisWin.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlK A.Prog.CtrlFrame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AF0m A.ProgWorld.
(* route (C): the region form, the cut shadow, RT_used_C from AR, and the proved ro_agree / owned_ro producers. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ACtlRtC A.ProgWorldRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorldCtlRt A.ProgWorldOwnedRo.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.rng_asan A.Prog.sh_word_on A.Prog.bcmp_wrap_c_on.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module LPE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LMe := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LCe := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module LSt := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LEF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module LRB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.RngBytes.
Module LRg := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module MN := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.
Module MNP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormP.
Module Img := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module PB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgBridge.
Module BzB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.BzBridge.
Module CFs := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_classify_box_frame_Fs_on.
Module BWc := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.bcmp_wrap_c.
Module MCc := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.memcmp_c.
Module PCc := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.reac_ctrl_classify_box_frame_c.
Module PWF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldVisFrame.
Module PWH := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldVisHeap.
Module PWW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldVisWin.
Module ACK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlK.
Module K11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module M05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module I04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI04.
Module I16 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
Module K1b := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Module CFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.CtrlFrame.
Module PW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorld.
Module PWRC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldRtC.
Module PWCR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldCtlRt.
Module PWOR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldOwnedRo.
Module SRO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.
Module ARC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlRtC.
Module RNA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.rng_asan.
Module SWO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.sh_word_on.
Module BWo := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.bcmp_wrap_c_on.
Module PW_AF0m := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AF0m.

(* ---------------------------------------------------------------------------------------------------------------
   1. Normalization: a stretch run from normalize_P m is a run from m with the same footprint. *)
Notation P1 := (fun _ : word => true) (only parsing).
Notation nrm m := (MNP.normalize_P Img.rsegs P1 m) (only parsing).

Lemma cls_ms_rel_MS : forall ms' R F pc fc rv m1 ro,
  MNP.ms_rel_P Img.rsegs P1 ms' (LMS.MS R F pc fc rv m1 ro) ->
  ms' = LMS.MS R F pc fc rv (ms_mem ms') ro /\ MNP.mem_rel_P Img.rsegs P1 (ms_mem ms') m1.
Proof.
  intros ms' R F pc fc rv m1 ro (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  destruct ms'; cbn in *. subst. split; [reflexivity | exact E8].
Qed.

(* MemNormP.evtF_rel_P keeps the footprint RNG_P of the normalized bytes; this form keeps the run's own footprint:
   step_accesses_rel_P gives the same access list. *)
Lemma cls_evtF_rel : forall RNG (Q : machine_state -> Prop) s s0,
  MNP.ms_rel_P Img.rsegs P1 s s0 -> LEF.evtF Img.rsegs RNG Q s0 ->
  LEF.evtF Img.rsegs RNG
    (fun s' => exists s0', Q s0' /\ MNP.ms_rel_P Img.rsegs P1 s' s0' /\
                         MNP.same_P Img.rsegs P1 (ms_mem s) (ms_mem s')) s.
Proof.
  intros RNG Q s s0 Hrel (s0' & Hs & HQ).
  revert s Hrel HQ. induction Hs as [x | x y z [Hsvc (accs & E & Fa)] _ IH]; intros s Hrel HQ.
  - exists s. split; [apply LEF.mstepsF_refl|]. exists x. split; [exact HQ|]. split; [exact Hrel|].
    intros a _. reflexivity.
  - destruct (MNP.step_accesses_rel_P Img.rsegs P1 s x y accs BzB.wx_apart_asan Hrel E) as (t & Et & Rt & Ot & _).
    destruct (IH t Rt HQ) as (s' & Hs' & s0' & HQ' & Rs' & Os').
    exists s'. split.
    + apply (LEF.mstepsF_cons Img.rsegs RNG s t s'); [|exact Hs']. split.
      * destruct Hrel as (_ & _ & _ & Esvc & _). rewrite Esvc. exact Hsvc.
      * exists accs. split; [exact Et | exact Fa].
    + exists s0'. split; [exact HQ'|]. split; [exact Rs'|]. intros a Ha. rewrite (Os' a Ha). exact (Ot a Ha).
Qed.

Section Lift.
Context {fx : lib.Reusable.YK11.FPState}.

(* SRr_fevt_hid for a run proved from the normalized memory. *)
Lemma cls_SRr_norm : forall (W : world Img.rsegs) (model : Model) R F pc fc (m : word -> option byte)
    (Q : machine_state -> Prop) (K : world Img.rsegs -> config -> Prop),
  MN.ro_agree Img.rsegs m ->
  LEF.evtF Img.rsegs (PB.RNG_W (w_H W)) Q (LMS.MS R F pc fc None (nrm m) (LPE.seg_rom Img.rsegs)) ->
  (forall ms' model',
     (exists s0', Q s0' /\ MNP.ms_rel_P Img.rsegs P1 ms' s0' /\ MNP.same_P Img.rsegs P1 m (ms_mem ms')) ->
     (forall x : word, w_H W x = true -> ms_mem ms' x = m x) ->
     same_but_materialized model model' -> SRr Img.rsegs W (mkCfg ms' model') K) ->
  SRr Img.rsegs W (mkCfg (LMS.MS R F pc fc None m (LPE.seg_rom Img.rsegs)) model) K.
Proof.
  intros W model R F pc fc m Q K Hro H Hk.
  apply (SRr_fevt_hid Img.rsegs ctrl_wx W _ model (PB.RNG_W (w_H W))
           (fun s' => exists s0', Q s0' /\ MNP.ms_rel_P Img.rsegs P1 s' s0' /\
                                MNP.same_P Img.rsegs P1 m (ms_mem s'))).
  - apply PB.fevt_of_evtF.
    apply (cls_evtF_rel _ Q (LMS.MS R F pc fc None m (LPE.seg_rom Img.rsegs))
             (LMS.MS R F pc fc None (nrm m) (LPE.seg_rom Img.rsegs))); [|exact H].
    exact (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl
             (MNP.mem_rel_P_normalize Img.rsegs P1 m Hro)))))))).
  - exact (PB.fp_avoids_RNG_W (w_H W)).
  - exact Hk.
Qed.
End Lift.

(* The loaded image of A is [0x10000, 0x5fe000) (ProgBridge.rsegs_spans); every other address finds no segment. *)
Lemma cls_noimg_find : forall a, ~ in_img tfibsegs a -> find_segment Img.rsegs a 1 = None.
Proof. intros a Hn. exact (find_segment_none tfibsegs a Hn). Qed.

Lemma cls_hi_noimg : forall a, 0x5fe000 <= a -> ~ in_img tfibsegs a.
Proof.
  intros a Ha (sg & Hin & Hr).
  apply (in_map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s)))) in Hin.
  change tfibsegs with Img.rsegs in Hin. rewrite PB.rsegs_spans in Hin. cbn in Hin.
  destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as E1 E2; rewrite <- E1, <- E2 in Hr; lia.
Qed.

Lemma cls_noimg_ro : forall x, ~ in_img tfibsegs (bv_unsigned x) -> LMe.ro_addr Img.rsegs x = false.
Proof. intros x Hn. unfold LMe.ro_addr. rewrite (cls_noimg_find _ Hn). reflexivity. Qed.

Lemma cls_noimg_rom : forall x, ~ in_img tfibsegs (bv_unsigned x) -> LPE.seg_rom Img.rsegs x = None.
Proof. intros x Hn. apply MN.seg_rom_unmapped. exact (cls_noimg_find _ Hn). Qed.

Lemma cls_wa_unsigned : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (LMe.wa a) = a.
Proof. intros a Ha. exact (LMe.wa_unsigned a Ha). Qed.

(* Facts on m carried to nrm m. *)
Lemma cls_mrd_nrm : forall m x, MN.ro_agree Img.rsegs m -> bv_unsigned x < TASK_SIZE ->
  LMe.mrd Img.rsegs (nrm m) x = LMe.mrd Img.rsegs m x.
Proof.
  intros m x Hro Hx. rewrite (MNP.mrd_normalize_P_cj Img.rsegs P1 m x (or_introl eq_refl)).
  apply MN.mrd_normalize_cj; [exact Hro | right; right; exact Hx].
Qed.

Lemma cls_wview_nrm : forall m x, MN.ro_agree Img.rsegs m -> ~ in_img tfibsegs (bv_unsigned x) ->
  bv_unsigned x < TASK_SIZE -> wview Img.rsegs (nrm m) x = wview Img.rsegs m x.
Proof.
  intros m x Hro Hn Hx. rewrite (MNP.wview_normalize_P_cj Img.rsegs P1 m x (or_introl eq_refl)).
  apply (MN.wview_rel_cj Img.rsegs m (MN.normalize_cj Img.rsegs m) x (MN.mem_rel_cj_normalize Img.rsegs m Hro)).
  apply MN.cj_drop_false_intro; [exact (cls_noimg_ro x Hn) | right; exact Hx].
Qed.

Lemma cls_bytes_nrm : forall m a bs, MN.ro_agree Img.rsegs m -> a + Z.of_nat (length bs) <= TASK_SIZE ->
  LMe.bytes_at Img.rsegs m a bs -> LMe.bytes_at Img.rsegs (nrm m) a bs.
Proof.
  intros m a bs Hro Hl HB. apply (MNP.bytes_at_P_of_cj Img.rsegs P1 m a bs); [intros; left; reflexivity|].
  apply MN.bytes_at_normalize_cj_low; assumption.
Qed.

Lemma cls_wr_at_nrm : forall m a n, MN.ro_agree Img.rsegs m ->
  (forall i, 0 <= i < n -> ~ in_img tfibsegs (a + i)) -> a + n <= TASK_SIZE ->
  LMe.wr_at Img.rsegs m a n -> LMe.wr_at Img.rsegs (nrm m) a n.
Proof.
  intros m a n Hro Hn Hl (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi.
  assert (Ei : bv_unsigned (LMe.wa (a + i)) = a + i) by (apply cls_wa_unsigned; unfold TASK_SIZE in Hl; lia).
  assert (W1 : wview Img.rsegs (nrm m) (LMe.wa (a + i)) = wview Img.rsegs m (LMe.wa (a + i)))
    by (apply cls_wview_nrm; [exact Hro | rewrite Ei; exact (Hn i Hi) | rewrite Ei; lia]).
  rewrite W1. exact (H3 i Hi).
Qed.

Lemma cls_rw_cells_nrm : forall m a cs, MN.ro_agree Img.rsegs m ->
  (forall i, 0 <= i < Z.of_nat (LCe.cells_size cs) -> ~ in_img tfibsegs (a + i)) ->
  a + Z.of_nat (LCe.cells_size cs) <= TASK_SIZE ->
  LSt.rw_cells Img.rsegs m a cs -> LSt.rw_cells Img.rsegs (nrm m) a cs.
Proof.
  intros m a cs Hro Hn Hl ((Hwf & HB) & HW). split; [split; [exact Hwf|] | exact (cls_wr_at_nrm m a _ Hro Hn Hl HW)].
  apply cls_bytes_nrm; [exact Hro | rewrite LCe.cells_bytes_length by exact Hwf; exact Hl | exact HB].
Qed.

Lemma cls_stk_nrm : forall m lo hi, MN.ro_agree Img.rsegs m -> 0x5fe000 <= lo -> hi <= TASK_SIZE ->
  LFr.stk Img.rsegs m lo hi -> LFr.stk Img.rsegs (nrm m) lo hi.
Proof.
  intros m lo hi Hro Hlo Hhi (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros a Ha.
  assert (Ea : bv_unsigned (LMe.wa a) = a) by (apply cls_wa_unsigned; unfold TASK_SIZE in Hhi; lia).
  assert (W1 : wview Img.rsegs (nrm m) (LMe.wa a) = wview Img.rsegs m (LMe.wa a))
    by (apply cls_wview_nrm; [exact Hro | rewrite Ea; apply cls_hi_noimg; lia | rewrite Ea; lia]).
  assert (M1 : LMe.mrd Img.rsegs (nrm m) (LMe.wa a) = LMe.mrd Img.rsegs m (LMe.wa a))
    by (apply cls_mrd_nrm; [exact Hro | rewrite Ea; lia]).
  rewrite W1, M1. exact (H3 a Ha).
Qed.

Lemma cls_shadow_lt : forall a, 0 <= a < TASK_SIZE -> 0 <= ART.shadow_addr a < TASK_SIZE.
Proof. intros a Ha. unfold ART.shadow_addr, ART.ASAN_K, TASK_SIZE in *. Z.div_mod_to_equations. lia. Qed.

Lemma cls_addressable_nrm : forall m p n, MN.ro_agree Img.rsegs m ->
  ART.addressable m p n -> ART.addressable (nrm m) p n.
Proof.
  intros m p n Hro (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H4 i Hi) as (Happ & b & Eb & Hok). split; [exact Happ|]. exists b. split; [|exact Hok].
  pose proof (cls_shadow_lt (p + i) ltac:(unfold ART.APPMEM_END, TASK_SIZE in *; lia)) as Hs.
  rewrite cls_mrd_nrm; [exact Eb | exact Hro |].
  rewrite cls_wa_unsigned by (unfold TASK_SIZE in Hs; lia). lia.
Qed.

(* route (C): a shadow region present at m is present at the normalized memory (the twin of the former universal
   cls_shadow_rw_nrm, with the region guard carried). *)
Lemma cls_shadow_rw_on_nrm : forall (P : Z -> Prop) m, MN.ro_agree Img.rsegs m -> SRO.shadow_rw_on P m ->
  SRO.shadow_rw_on P (nrm m).
Proof.
  intros P m Hro H a Hp Ha.
  assert (Ra : 0x5fe000 <= a < TASK_SIZE)
    by (unfold ART.in_shadow, ART.LOWMEM_END, ART.LOWSHADOW_END, ART.HIGHSHADOW_BEG, ART.HIGHMEM_BEG, TASK_SIZE in *;
        lia).
  assert (Ea : bv_unsigned (LMe.wa a) = a) by (apply cls_wa_unsigned; unfold TASK_SIZE in Ra; lia).
  assert (W1 : wview Img.rsegs (nrm m) (LMe.wa a) = wview Img.rsegs m (LMe.wa a))
    by (apply cls_wview_nrm; [exact Hro | rewrite Ea; apply cls_hi_noimg; lia | rewrite Ea; lia]).
  assert (M1 : LMe.mrd Img.rsegs (nrm m) (LMe.wa a) = LMe.mrd Img.rsegs m (LMe.wa a))
    by (apply cls_mrd_nrm; [exact Hro | rewrite Ea; lia]).
  rewrite W1, M1. exact (H a Hp Ha).
Qed.

Lemma cls_mem_inv_nrm : forall m, LMe.mem_inv Img.rsegs (nrm m).
Proof.
  intros m. apply MNP.mem_inv_normalize_P. apply MN.mem_inv_cj_inv. apply MN.mem_inv_cj_normalize.
Qed.

Lemma cls_asan_cells_nrm : forall m, MN.ro_agree Img.rsegs m -> ART.asan_cells m -> ART.asan_cells (nrm m).
Proof.
  intros m Hro (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17).
  unfold ART.asan_cells.
  repeat match goal with |- _ /\ _ => split end;
    apply cls_bytes_nrm; first [exact Hro | assumption |
      unfold ART.CELL_K, ART.GOT_CELL_K, ART.INITED, ART.REPLACE, ART.GOT_REPLACE, ART.UAR, ART.GOT_UAR,
        ART.CANPOISON, ART.HIEND, ART.GOT_HIEND, ART.MIDBEG, ART.GOT_MIDBEG, ART.MIDEND, ART.GOT_MIDEND,
        ART.REAL_MEMCPY, ART.REAL_MEMSET, ART.GOT_REAL_MEMSET, TASK_SIZE; cbn; lia].
Qed.

(* Facts on a normalized successor carried back to the real successor (mem_rel_P m m0). *)
Lemma cls_stk_back : forall m m0 lo hi, MNP.mem_rel_P Img.rsegs P1 m m0 ->
  LFr.stk Img.rsegs m0 lo hi -> LFr.stk Img.rsegs m lo hi.
Proof.
  intros m m0 lo hi HR (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H3 a Ha) as (Hw & b & Hb). split.
  - rewrite <- (MNP.wview_rel_P Img.rsegs P1 m m0 _ HR (MNP.keep_of_wview_P Img.rsegs P1 m m0 _ HR Hw)). exact Hw.
  - exists b. exact (MNP.mrd_rel_P Img.rsegs P1 m m0 _ b HR Hb).
Qed.

Lemma cls_rw_cells_back : forall m m0 a cs, MNP.mem_rel_P Img.rsegs P1 m m0 ->
  LSt.rw_cells Img.rsegs m0 a cs -> LSt.rw_cells Img.rsegs m a cs.
Proof.
  intros m m0 a cs HR ((Hwf & HB) & HW). split; [split; [exact Hwf|]|].
  - exact (MNP.bytes_at_rel_P Img.rsegs P1 m m0 a _ HR HB).
  - exact (MNP.wr_at_rel_P Img.rsegs P1 m m0 a _ HR HW).
Qed.

Lemma cls_addressable_back : forall m m0 p n, MNP.mem_rel_P Img.rsegs P1 m m0 ->
  ART.addressable m0 p n -> ART.addressable m p n.
Proof.
  intros m m0 p n HR (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H4 i Hi) as (Happ & b & Eb & Hok). split; [exact Happ|]. exists b.
  split; [exact (MNP.mrd_rel_P Img.rsegs P1 m m0 _ b HR Eb) | exact Hok].
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   2. The two lifts.  Each states the proved stretch's premises on the REAL memory (ro_agree in place of mem_inv,
   ranges below TASK_SIZE = 2^47 so that normalization keeps their bytes), one range_visible fact per footprint
   range, and hands the continuation the stretch's post on the real successor memory plus the kept hidden bytes. *)
Section Lifts.
Context {fx : lib.Reusable.YK11.FPState}.

Lemma cls_rng_img : forall W : world Img.rsegs, LEF.rng (PB.RNG_W (w_H W)) 0x10000 0x5ee000.
Proof.
  intros W. apply PB.rng_of_visible.
  apply (PB.range_visible_sub _ _ _ _ _ (PB.img_vis_W W));
    unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.IMG_LO,
      OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.IMG_HI; lia.
Qed.

(* Stretch A, lifted: classify's entry 0x831b8 to reac_ctrl_parse's entry 0x83578 (ra = 0x83200). *)
Lemma cls_liftA : forall (W : world Img.rsegs) (model : Model)
    (ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n u o v S : Z)
    (K : world Img.rsegs -> config -> Prop),
  8864 <= S <= TASK_SIZE -> ART.HIGHMEM_BEG <= S - 8864 ->
  LFr.stk Img.rsegs m (S - 8864) S -> MN.ro_agree Img.rsegs m -> ART.asan_cells m ->
  PB.range_visible (w_H W) (S - 8864) 8864 ->
  (forall ms' model',
     (exists m1 : word -> option byte,
        ms' = LMS.MS (LFr.mkR (Z_to_bv 64 0x83200) (Z_to_bv 64 (S + -64)) gp tp t0 t1 t2 (Z_to_bv 64 v) s1
                       (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 o) (Z_to_bv 64 o) (Z_to_bv 64 v) a5 a6 a7
                       (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 u) (Z_to_bv 64 ART.ASAN_K) s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                F (Z_to_bv 64 0x83578) fc None m1 (LPE.seg_rom Img.rsegs) /\
        LFr.munch [(S + -64, S)] m m1 /\ LFr.wmono Img.rsegs m m1 /\
        LFr.stk Img.rsegs m1 (S - 8864) (S + -64) /\
        LSt.rw_cells Img.rsegs m1 (S + -64)
          [LCe.C8 s6; LCe.C8 s5; LCe.C8 s4; LCe.C8 s3; LCe.C8 s2; LCe.C8 s1; LCe.C8 s0; LCe.C8 ra]) ->
     (forall x : word, w_H W x = true -> ms_mem ms' x = m x) ->
     same_but_materialized model model' -> SRr Img.rsegs W (mkCfg ms' model') K) ->
  SRr Img.rsegs W
    (mkCfg (LMS.MS (LFr.mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 u)
                      (Z_to_bv 64 o) (Z_to_bv 64 v) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x831b8) fc None m (LPE.seg_rom Img.rsegs)) model) K.
Proof.
  intros W model ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f n u o v S K
    HS HHM ST HRO AC VW Hk.
  assert (HHM' : 0x5fe000 <= S - 8864) by (unfold ART.HIGHMEM_BEG in HHM; lia).
  eapply cls_SRr_norm; [exact HRO | |].
  - apply (CFs.reac_ctrl_classify_box_frame_pre_call_F (PB.RNG_W (w_H W)) ra gp tp t0 t1 t2 s0 s1 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (nrm m) f n u o v S).
    + unfold TASK_SIZE in HS. lia.
    + exact HHM.
    + exact (cls_stk_nrm m (S - 8864) S HRO HHM' ltac:(lia) ST).
    + apply cls_mem_inv_nrm.
    + exact (cls_asan_cells_nrm m HRO AC).
    + apply cls_rng_img.
    + exact (PB.rng_of_visible _ _ _ VW).
  - intros ms' model' (s0' & (m1 & E & MU & WM & _ & ST1 & RW) & Hrel & Hsame) Hh Hs.
    apply Hk; [| exact Hh | exact Hs].
    subst s0'. destruct (cls_ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as [Ems HR1].
    pose proof (MNP.mem_rel_P_normalize Img.rsegs P1 m HRO) as HR0.
    exists (ms_mem ms'). split; [exact Ems|].
    split; [exact (MNP.munch_rel_P Img.rsegs P1 _ m _ (ms_mem ms') m1 HR0 HR1 Hsame MU)|].
    split; [exact (MNP.wmono_rel_P Img.rsegs P1 m _ (ms_mem ms') m1 HR0 HR1 Hsame WM)|].
    split; [exact (cls_stk_back _ _ _ _ HR1 ST1) | exact (cls_rw_cells_back _ _ _ _ HR1 RW)].
Qed.

(* Stretch B, lifted: reac_ctrl_parse's return point 0x83200 to classify's ret.  The stretch's base memory and cut
   memory are both the normalized parse-return memory (so its munch / wmono premises are reflexive), and its post is
   carried back to the real successor memory. *)
Lemma cls_liftB : forall (W : world Img.rsegs) (model : Model)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m2 : word -> option byte) (f n u o v S : Z) (fr us vb : list byte)
    (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word)
    (K : world Img.rsegs -> config -> Prop),
  0 <= f < 2^64 -> 0 <= u < 2^64 -> 0 <= o < 2^64 -> 0 <= v < 2^64 -> 8864 <= S <= TASK_SIZE -> S mod 16 = 0 ->
  length fr = 50%nat -> length us = 6%nat ->
  (50 <= n -> 0 < f /\ f + 50 <= TASK_SIZE /\ LMe.bytes_at Img.rsegs m2 f fr /\ (f + 50 <= S - 8864 \/ S <= f)) ->
  (50 <= n -> u + 6 <= TASK_SIZE /\ LMe.bytes_at Img.rsegs m2 u us /\ (u + 6 <= S - 8864 \/ S <= u)) ->
  o <> 0 -> o mod 4 = 0 -> o + 36 <= TASK_SIZE -> (o + 36 <= S - 8864 \/ S <= o) ->
  (50 <= n -> o + 36 <= f \/ f + 50 <= o) -> (o + 36 <= u \/ u + 6 <= o) ->
  v <> 0 -> v mod 4 = 0 -> v + 4 <= TASK_SIZE -> (v + 4 <= S - 8864 \/ S <= v) -> (v + 4 <= o \/ o + 36 <= v) ->
  (v + 4 <= f \/ f + 50 <= v) -> (v + 4 <= u \/ u + 6 <= v) ->
  ART.HIGHMEM_BEG <= S - 8864 ->
  (50 <= n -> ART.addressable m2 f 50 /\ ART.addressable m2 u 6 /\ ART.app_mem (u + 6) /\ ART.app_mem (u + 7)) ->
  ART.addressable m2 o 36 -> ART.addressable m2 v 4 -> (v + 4 <= ART.RT_LO \/ ART.RT_HI <= v) ->
  (forall i, 0 <= i < 36 -> ~ in_img tfibsegs (o + i)) -> (forall i, 0 <= i < 4 -> ~ in_img tfibsegs (v + i)) ->
  PB.range_visible (w_H W) (S - 8864) 8864 ->
  PB.range_visible (w_H W) o 36 ->
  PB.range_visible (w_H W) (ART.shadow_addr o / 8 * 8)
    (ART.shadow_addr (o + 36 - 1) / 8 * 8 + 8 - ART.shadow_addr o / 8 * 8) ->
  PB.range_visible (w_H W) v 4 ->
  PB.range_visible (w_H W) (ART.shadow_addr v / 8 * 8)
    (ART.shadow_addr (v + 4 - 1) / 8 * 8 + 8 - ART.shadow_addr v / 8 * 8) ->
  (50 <= n -> PB.range_visible (w_H W) f 50) ->
  (50 <= n -> PB.range_visible (w_H W) (ART.shadow_addr f / 8 * 8)
                (ART.shadow_addr (f + 50 - 1) / 8 * 8 + 8 - ART.shadow_addr f / 8 * 8)) ->
  (50 <= n -> PB.range_visible (w_H W) u 6) ->
  (50 <= n -> PB.range_visible (w_H W) (ART.shadow_addr u / 8 * 8)
                (ART.shadow_addr (u + 6 - 1) / 8 * 8 + 8 - ART.shadow_addr u / 8 * 8)) ->
  LSt.rw_cells Img.rsegs m2 (S + -64)
    [LCe.C8 s6; LCe.C8 s5; LCe.C8 s4; LCe.C8 s3; LCe.C8 s2; LCe.C8 s1; LCe.C8 s0; LCe.C8 ra] ->
  LMe.bytes_at Img.rsegs m2 o (snd (ctrlparse n fr)) -> LMe.wr_at Img.rsegs m2 o 36 ->
  LSt.rw_cells Img.rsegs m2 v [LCe.CB 4 vb] ->
  LFr.stk Img.rsegs m2 (S - 8864) (S + -64) ->
  MN.ro_agree Img.rsegs m2 -> ART.asan_cells m2 ->
  SRO.shadow_rw_on (CFs.reac_ctrl_classify_box_frame_post_call_shadow_R n u o) m2 ->
  ART.addressable m2 (S - 8864) 8864 ->
  LMe.bytes_at Img.rsegs m2 BWc.REAL_BCMP (LMe.le8 (LMe.wa BWc.BCMP)) ->
  LMe.bytes_at Img.rsegs m2 BWc.REAL_MEMCMP (LMe.le8 (LMe.wa MCc.MEMCMP)) ->
  LMe.bytes_at Img.rsegs m2 BWc.GOT_CF (LMe.le8 (LMe.wa BWc.CF)) ->
  LMe.bytes_at Img.rsegs m2 (BWc.CF + 254) [Z_to_bv 8 1] ->
  LMe.bytes_at Img.rsegs m2 (BWc.CF + 255) [Z_to_bv 8 1] ->
  (forall ms' model',
     (exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
        ms' = LMS.MS (LFr.mkR ra (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (cl_r (classify n fr us)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (LMS.ret_pc ra) fc None m' (LPE.seg_rom Img.rsegs) /\
        LFr.munch [(o, o + 36); (v, v + 4); (S - 8864, S); (ART.shadow_addr (S - 8864), ART.shadow_addr S)] m2 m' /\
        LFr.wmono Img.rsegs m2 m' /\ LFr.stk Img.rsegs m' (S - 8864) S /\
        LSt.rw_cells Img.rsegs m' o [LCe.CB 36 (snd (ctrlparse n fr))] /\
        LSt.rw_cells Img.rsegs m' v [LCe.CB 4 (PCc.reac_ctrl_classify_box_frame_ev (classify n fr us) vb)] /\
        ART.addressable m' (S - 8864) 8864) ->
     (forall x : word, w_H W x = true -> ms_mem ms' x = m2 x) ->
     same_but_materialized model model' -> SRr Img.rsegs W (mkCfg ms' model') K) ->
  SRr Img.rsegs W
    (mkCfg (LMS.MS (LFr.mkR x1 (Z_to_bv 64 (S + -64)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9
                      (Z_to_bv 64 (fst (ctrlparse n fr))) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 o) (Z_to_bv 64 f)
                      (Z_to_bv 64 u) (Z_to_bv 64 ART.ASAN_K) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                   F (Z_to_bv 64 0x83200) fc None m2 (LPE.seg_rom Img.rsegs)) model) K.
Proof.
  intros W model ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m2 f n u o v S fr us vb
    x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 K
    Rf Ru Ro Rv RS S16 Lfr Lus HF HU Ho0 Ho4 Ho36 DOs DOf DOu Hv0 Hv4 Hv36 DVs DVo DVf DVu HHM AFU AO AV HVR
    NIo NIv VW VO VOS VV VVS VF VFS VU VUS FR HBo WRo HV ST HRO AC SW AW CL1 CL2 CL3 CL4 CL5 Hk.
  assert (HHM' : 0x5fe000 <= S - 8864) by (unfold ART.HIGHMEM_BEG in HHM; lia).
  assert (HT : TASK_SIZE = 2 ^ 47) by reflexivity.
  eapply cls_SRr_norm; [exact HRO | |].
  - apply (CFs.reac_ctrl_classify_box_frame_post_call_F_on (PB.RNG_W (w_H W)) ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9
             s10 s11 F fc (nrm m2) (nrm m2) f n u o v S fr us vb
             x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31).
    (* the Section's premises *)
    + exact Rf.
    + exact Ru.
    + exact Ro.
    + exact Rv.
    + rewrite HT in RS. lia.
    + exact S16.
    + exact Lfr.
    + exact Lus.
    + intros Hn. destruct (HF Hn) as (A1 & A2 & A3 & A4). rewrite HT in A2.
      split; [exact A1|]. split; [lia|]. split; [|exact A4].
      apply cls_bytes_nrm; [exact HRO | rewrite Lfr, HT; cbn; lia | exact A3].
    + intros Hn. destruct (HU Hn) as (A2 & A3 & A4). rewrite HT in A2.
      split; [lia|]. split; [|exact A4].
      apply cls_bytes_nrm; [exact HRO | rewrite Lus, HT; cbn; lia | exact A3].
    + exact Ho0.
    + exact Ho4.
    + rewrite HT in Ho36. lia.
    + exact DOs.
    + exact DOf.
    + exact DOu.
    + exact Hv0.
    + exact Hv4.
    + rewrite HT in Hv36. lia.
    + exact DVs.
    + exact DVo.
    + exact DVf.
    + exact DVu.
    + exact HHM.
    + unfold ART.APPMEM_END. rewrite HT in RS. lia.
    + intros Hn. destruct (AFU Hn) as (A1 & A2 & A3 & A4).
      split; [exact (cls_addressable_nrm m2 _ _ HRO A1)|]. split; [exact (cls_addressable_nrm m2 _ _ HRO A2)|].
      split; [exact A3 | exact A4].
    + exact (cls_addressable_nrm m2 _ _ HRO AO).
    + exact (cls_addressable_nrm m2 _ _ HRO AV).
    + exact HVR.
    (* the footprint *)
    + exact (PB.rng_bytes_RNG_W (w_H W)).
    + apply cls_rng_img.
    + exact (PB.rng_of_visible _ _ _ VW).
    + exact (PB.rng_of_visible _ _ _ VO).
    + exact (PB.rng_of_visible _ _ _ VOS).
    + exact (PB.rng_of_visible _ _ _ VV).
    + exact (PB.rng_of_visible _ _ _ VVS).
    + intros Hn. exact (PB.rng_of_visible _ _ _ (VF Hn)).
    + intros Hn. exact (PB.rng_of_visible _ _ _ (VFS Hn)).
    + intros Hn. exact (PB.rng_of_visible _ _ _ (VU Hn)).
    + intros Hn. exact (PB.rng_of_visible _ _ _ (VUS Hn)).
    (* the cut state at 0x83200 *)
    + apply cls_rw_cells_nrm; [exact HRO | | cbn; rewrite HT in RS; lia | exact FR].
      intros i Hi. apply cls_hi_noimg. cbn in Hi. lia.
    + apply cls_bytes_nrm; [exact HRO | rewrite RcParse.ctrlparse_length, HT; cbn; rewrite HT in Ho36; lia | exact HBo].
    + apply cls_wr_at_nrm; [exact HRO | exact NIo | exact Ho36 | exact WRo].
    + apply cls_rw_cells_nrm; [exact HRO | | cbn; exact Hv36 | exact HV].
      intros i Hi. apply NIv. cbn in Hi. lia.
    + apply LFr.munch_refl.
    + apply LFr.wmono_refl.
    + apply cls_mem_inv_nrm.
    + apply cls_stk_nrm; [exact HRO | exact HHM' | lia | exact ST].
    + exact (cls_asan_cells_nrm m2 HRO AC).
    + exact (cls_shadow_rw_on_nrm _ m2 HRO SW).
    + exact (cls_addressable_nrm m2 _ _ HRO AW).
    + apply cls_bytes_nrm; [exact HRO | unfold BWc.REAL_BCMP; cbn; rewrite HT; lia | exact CL1].
    + apply cls_bytes_nrm; [exact HRO | unfold BWc.REAL_MEMCMP; cbn; rewrite HT; lia | exact CL2].
    + apply cls_bytes_nrm; [exact HRO | unfold BWc.GOT_CF; cbn; rewrite HT; lia | exact CL3].
    + apply cls_bytes_nrm; [exact HRO | unfold BWc.CF; cbn; rewrite HT; lia | exact CL4].
    + apply cls_bytes_nrm; [exact HRO | unfold BWc.CF; cbn; rewrite HT; lia | exact CL5].
  - intros ms' model'
      (s0' & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & _ &
              ST1 & RWo & RWv & _ & _ & AW1) & Hrel & Hsame) Hh Hs.
    apply Hk; [| exact Hh | exact Hs].
    subst s0'. destruct (cls_ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as [Ems HR1].
    pose proof (MNP.mem_rel_P_normalize Img.rsegs P1 m2 HRO) as HR0.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', (ms_mem ms').
    split; [exact Ems|].
    split; [exact (MNP.munch_rel_P Img.rsegs P1 _ m2 _ (ms_mem ms') m' HR0 HR1 Hsame MU)|].
    split; [exact (MNP.wmono_rel_P Img.rsegs P1 m2 _ (ms_mem ms') m' HR0 HR1 Hsame WM)|].
    split; [exact (cls_stk_back _ _ _ _ HR1 ST1)|].
    split; [exact (cls_rw_cells_back _ _ _ _ HR1 RWo)|].
    split; [exact (cls_rw_cells_back _ _ _ _ HR1 RWv) | exact (cls_addressable_back _ _ _ _ HR1 AW1)].
Qed.

End Lifts.

(* ---------------------------------------------------------------------------------------------------------------
   3. Open point 4(a): stretch B's munch list names the shadow of its window [shadow_addr (S - 8864), shadow_addr S),
   which is VISIBLE in cgif's world (AR_zshadow_law at the stack entry of zero_shadow_ranges; ProgWorldVisWin.win_sh_vis)
   and in none of awr_byte's cases.  The stretch never CHANGES those bytes: post_call_F asks
   `addressable m1 (S - 8864) 8864` and gives `addressable m' (S - 8864) 8864`; the window is 8-aligned, so each of
   its shadow bytes covers a whole granule, and AsanRT.shadow_ok at granule offset 7 forces the value 0 before and
   after.  So the journal step (YCbq.ajournal_exec, whose write set only has to cover CHANGED bytes) leaves them out. *)
Lemma cls_byte_signed_small : forall b : byte, bv_unsigned b < 128 -> bv_signed b = bv_unsigned b.
Proof.
  intros b Hb. unfold bv_signed. apply bv_swrap_small. change (bv_half_modulus 8) with 128.
  pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. lia.
Qed.

Lemma cls_byte_signed0 : forall b : byte, bv_signed b = 0 -> b = Z_to_bv 8 0.
Proof.
  intros b H. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  destruct (Z_lt_le_dec (bv_unsigned b) 128) as [L|L].
  - rewrite (cls_byte_signed_small b L) in H. apply bv_eq. rewrite H. reflexivity.
  - exfalso. unfold bv_signed in H.
    rewrite (K11.bv_swrap_hi 8) in H;
      [ change (bv_modulus 8) with 256 in H; lia
      | discriminate
      | change (bv_half_modulus 8) with 128; lia
      | change (bv_modulus 8) with 256; lia ].
Qed.

Lemma cls_win_shadow_unchanged : forall (m m' : word -> option byte) (S : Z),
  S mod 8 = 0 -> ART.HIGHMEM_BEG <= S - 8864 -> S <= TASK_SIZE ->
  ART.addressable m (S - 8864) 8864 -> ART.addressable m' (S - 8864) 8864 ->
  forall x, ART.shadow_addr (S - 8864) <= x < ART.shadow_addr S -> m' (LMe.wa x) = m (LMe.wa x).
Proof.
  intros m m' S H8 HH HT (_ & _ & _ & A1) (_ & _ & _ & A2) x Hx.
  set (g := 8 * (x - ART.ASAN_K) + 7).
  assert (Hg : S - 8864 <= g < S)
    by (unfold g, ART.shadow_addr, ART.ASAN_K in *; Z.div_mod_to_equations; lia).
  assert (Hsg : ART.shadow_addr g = x) by (unfold g, ART.shadow_addr; Z.div_mod_to_equations; lia).
  assert (G7 : g mod 8 = 7) by (unfold g; Z.div_mod_to_equations; lia).
  destruct (A1 (g - (S - 8864)) ltac:(lia)) as (_ & b1 & E1 & K1).
  destruct (A2 (g - (S - 8864)) ltac:(lia)) as (_ & b2 & E2 & K2).
  replace (S - 8864 + (g - (S - 8864))) with g in E1, K1, E2, K2 by lia.
  rewrite Hsg in E1, E2. unfold ART.shadow_ok in K1, K2.
  assert (Z1 : b1 = Z_to_bv 8 0) by (apply cls_byte_signed0; destruct K1 as [K1|K1]; [exact K1 | lia]).
  assert (Z2 : b2 = Z_to_bv 8 0) by (apply cls_byte_signed0; destruct K2 as [K2|K2]; [exact K2 | lia]).
  subst b1 b2.
  assert (Hx64 : 0 <= x < 2 ^ 64)
    by (unfold ART.shadow_addr, ART.ASAN_K, ART.HIGHMEM_BEG, TASK_SIZE in *; Z.div_mod_to_equations; lia).
  assert (Hrom : LPE.seg_rom Img.rsegs (LMe.wa x) = None).
  { apply cls_noimg_rom. rewrite cls_wa_unsigned by exact Hx64. apply cls_hi_noimg.
    unfold ART.shadow_addr, ART.ASAN_K, ART.HIGHMEM_BEG in *. Z.div_mod_to_equations. lia. }
  assert (M1 : m (LMe.wa x) = Some (Z_to_bv 8 0)).
  { revert E1. unfold LMe.mrd. rewrite Hrom. destruct (m (LMe.wa x)); intros E; [exact E | discriminate E]. }
  assert (M2 : m' (LMe.wa x) = Some (Z_to_bv 8 0)).
  { revert E2. unfold LMe.mrd. rewrite Hrom. destruct (m' (LMe.wa x)); intros E; [exact E | discriminate E]. }
  rewrite M1, M2. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   4. From the cgif world's view (aview / apresent / range_addressable) to ctrl's memory predicates. *)
Lemma cls_aview_mrd : forall (H : word -> bool) (mem : word -> option byte) a,
  0 <= a < 2 ^ 64 -> H (Z_to_bv 64 a) = false ->
  aview tfibsegs H mem a = option_map (fun b : byte => bv_unsigned b) (LMe.mrd Img.rsegs mem (LMe.wa a)).
Proof.
  intros H mem a Ha Hh. unfold aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict. cbv beta. rewrite Hh.
  unfold LMe.mrd, LMe.wa. reflexivity.
Qed.

Lemma cls_vis_of_view : forall (W : world tfibsegs) (mem : word -> option byte) a,
  aview tfibsegs (w_H W) mem a <> None -> w_H W (Z_to_bv 64 a) = false.
Proof. intros W mem a H. exact (PWF.vis_of_aview tfibsegs W mem a H). Qed.

(* Bytes the view reads, at visible addresses, are ctrl bytes. *)
Lemma cls_bytes_of_view : forall (H : word -> bool) (mem : word -> option byte) a (bs : list byte) (d : byte),
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall i, (i < length bs)%nat -> H (Z_to_bv 64 (a + Z.of_nat i)) = false) ->
  (forall i, (i < length bs)%nat -> aview tfibsegs H mem (a + Z.of_nat i) = Some (bv_unsigned (nth i bs d))) ->
  LMe.bytes_at Img.rsegs mem a bs.
Proof.
  intros H mem a bs d Ha Hl Hh Hv. split; [exact Ha|]. split; [exact Hl|]. intros i Hi.
  specialize (Hv i Hi). rewrite (cls_aview_mrd H mem (a + Z.of_nat i) ltac:(lia) (Hh i Hi)) in Hv.
  rewrite (nth_error_nth' bs d Hi).
  destruct (LMe.mrd Img.rsegs mem (LMe.wa (a + Z.of_nat i))) as [b|]; cbn in Hv; [|discriminate Hv].
  injection Hv as Hb. f_equal. apply bv_eq. exact Hb.
Qed.

(* Present bytes are ctrl stack bytes. *)
Lemma cls_stk_of_pres : forall (H : word -> bool) (mem : word -> option byte) lo hi,
  0 <= lo -> hi <= 2 ^ 64 -> (forall a, lo <= a < hi -> apresent H mem a) -> LFr.stk Img.rsegs mem lo hi.
Proof.
  intros H mem lo hi Hlo Hhi Hp. split; [exact Hlo|]. split; [exact Hhi|]. intros a Ha.
  destruct (Hp a Ha) as [_ [b Hb]]. unfold LMe.wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold LMe.mrd. rewrite Hb. reflexivity.
Qed.

Lemma cls_wr_of_pres : forall (H : word -> bool) (mem : word -> option byte) a n,
  0 <= a -> a + n <= 2 ^ 64 -> (forall x, a <= x < a + n -> apresent H mem x) -> LMe.wr_at Img.rsegs mem a n.
Proof.
  intros H mem a n Ha Hn Hp. split; [exact Ha|]. split; [exact Hn|]. intros i Hi.
  destruct (Hp (a + i) ltac:(lia)) as [_ [b Hb]]. unfold LMe.wa. unfold wview. rewrite Hb. discriminate.
Qed.

(* Shadow facts the view states give ctrl's addressable. *)
Lemma cls_addressable_of_view : forall (W : world tfibsegs) (mem : word -> option byte) p n,
  0 <= p -> 0 <= n -> p + n <= ART.APPMEM_END ->
  (forall i, 0 <= i < n -> ART.app_mem (p + i)) ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF p n ->
  ART.addressable mem p n.
Proof.
  intros W mem p n H0 Hn Hp Happ HR. split; [exact H0|]. split; [exact Hn|]. split; [exact Hp|].
  intros i Hi. split; [exact (Happ i Hi)|].
  destruct (HR (p + i) ltac:(lia)) as (s & Es & Hok).
  assert (Esh : shadow_of_addr SHADOW_OFF (p + i) = ART.shadow_addr (p + i))
    by (unfold shadow_of_addr, SHADOW_OFF, ART.shadow_addr, ART.ASAN_K; lia).
  rewrite Esh in Es.
  pose proof (cls_shadow_lt (p + i) ltac:(unfold ART.APPMEM_END, TASK_SIZE in *; lia)) as Hs.
  assert (Hv : w_H W (Z_to_bv 64 (ART.shadow_addr (p + i))) = false)
    by (apply (cls_vis_of_view W mem); rewrite Es; discriminate).
  rewrite (cls_aview_mrd (w_H W) mem (ART.shadow_addr (p + i)) ltac:(unfold TASK_SIZE in Hs; lia) Hv) in Es.
  destruct (LMe.mrd Img.rsegs mem (LMe.wa (ART.shadow_addr (p + i)))) as [b|] eqn:Eb; cbn in Es;
    [|discriminate Es].
  injection Es as Es. subst s. exists b. split; [reflexivity|].
  unfold saddr_ok in Hok. assert (Hsm : bv_unsigned b < 128) by (destruct Hok; lia).
  unfold ART.shadow_ok. rewrite (cls_byte_signed_small b Hsm). destruct Hok; [left | right]; lia.
Qed.

(* A byte outside the image: the writable view is the memory itself. *)
Lemma cls_wview_noimg : forall m x, ~ in_img tfibsegs (bv_unsigned x) -> wview Img.rsegs m x = m x.
Proof. intros m x Hn. unfold wview. destruct (m x); [reflexivity|]. rewrite (cls_noimg_find _ Hn). reflexivity. Qed.

(* munch keeps the view of every byte outside its list. *)
Lemma cls_view_munch : forall Wl (H : word -> bool) (m m' : word -> option byte) a,
  LFr.munch Wl m m' -> 0 <= a < 2 ^ 64 -> LFr.outside Wl a -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof.
  intros Wl H m m' a MU Ha Ho. unfold aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict.
  rewrite (MU (Z_to_bv 64 a)); [reflexivity|]. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; lia).
  exact Ho.
Qed.

Lemma cls_munch_at : forall Wl (m m' : word -> option byte) a,
  LFr.munch Wl m m' -> 0 <= a < 2 ^ 64 -> LFr.outside Wl a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros Wl m m' a MU Ha Ho. apply MU. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; lia). exact Ho.
Qed.

Lemma cls_wr_dec : forall o v Sp x,
  (o <= x < o + 36 \/ v <= x < v + 4 \/ Sp - 8864 <= x < Sp) \/
  ~ (o <= x < o + 36 \/ v <= x < v + 4 \/ Sp - 8864 <= x < Sp).
Proof.
  intros o v Sp x.
  destruct (Z_le_gt_dec o x); destruct (Z_lt_le_dec x (o + 36)); destruct (Z_le_gt_dec v x);
    destruct (Z_lt_le_dec x (v + 4)); destruct (Z_le_gt_dec (Sp - 8864) x); destruct (Z_lt_le_dec x Sp);
    first [left; lia | right; lia].
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   5. The caller's journal across the two lifted stretches (YCbq.ajournal_exec). *)
Section Journal.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.

Ltac cls_exec_side :=
  first [ exact LAWS | exact ctrl_segs_low | assumption | idtac ].

(* Stretch A writes only its own 64-byte frame [Sp - 64, Sp), inside the journal's window. *)
Lemma cls_journal_A : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world tfibsegs) memc mdc k m1 md1 Sp,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= Sp - 64 -> Sp <= sp0 -> 0x5fe000 <= Sp - 64 -> Sp <= 2 ^ 64 ->
  LFr.munch [(Sp + -64, Sp)] memc m1 -> LFr.wmono Img.rsegs memc m1 ->
  (forall x : word, w_H W x = true -> m1 x = memc x) ->
  same_but_materialized mdc md1 ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m1 md1 k.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k m1 md1 Sp HJ H1 H2 H3 H4 MU WM Hh Hs.
  eapply ajournal_exec with (Wr := fun a => Sp - 64 <= a < Sp) (memc := memc) (mdc := mdc).
  all: cls_exec_side.
  all: lazymatch goal with
  | |- forall x : word, ~ _ -> _ = _ =>
      intros x Hx; unfold lib.Reusable.YK04.mrestrict; destruct (w_H W x); [reflexivity|];
      apply MU; cbn; split; [intros [Hx1 Hx2]; apply Hx; lia | exact I]
  | |- lib.Reusable.YK1b.mem_grows _ _ =>
      intros x Hx; unfold lib.Reusable.YK04.mrestrict in *; destruct (w_H W x); [exact Hx|];
      pose proof (bv_unsigned_in_range 64 x) as Rx; change (bv_modulus 64) with (2 ^ 64) in Rx;
      destruct (Z_lt_le_dec (bv_unsigned x) (Sp - 64)) as [L|L];
      [ rewrite (MU x) by (cbn; split; [lia | exact I]); exact Hx
      | destruct (Z_lt_le_dec (bv_unsigned x) Sp) as [L2|L2];
        [ assert (Hn : ~ in_img tfibsegs (bv_unsigned x)) by (apply cls_hi_noimg; lia);
          rewrite <- (cls_wview_noimg m1 x Hn); apply WM; rewrite (cls_wview_noimg memc x Hn); exact Hx
        | rewrite (MU x) by (cbn; split; [lia | exact I]); exact Hx ] ]
  | |- forall a, _ -> awr_byte _ _ _ _ _ _ _ _ =>
      intros a Ha; left; lia
  end.
Qed.

(* Stretch B's write set as the journal sees it: o, v and the window.  The window's shadow, which its munch list
   also names, is unchanged (cls_win_shadow_unchanged, open point 4(a)). *)
Lemma cls_journal_B : forall STK sp0 FP ly S W0 mem0 md0 own ly2 S2 (W2 : world tfibsegs) mem2 md2 k m' md' Sp o v,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k ->
  sp0 - STK <= Sp - 8864 -> Sp <= sp0 -> Sp mod 8 = 0 -> ART.HIGHMEM_BEG <= Sp - 8864 -> Sp <= TASK_SIZE ->
  0 <= o -> o + 36 <= 2 ^ 64 -> 0 <= v -> v + 4 <= 2 ^ 64 ->
  (forall i, 0 <= i < 36 -> ~ in_img tfibsegs (o + i)) -> (forall i, 0 <= i < 4 -> ~ in_img tfibsegs (v + i)) ->
  LFr.munch [(o, o + 36); (v, v + 4); (Sp - 8864, Sp); (ART.shadow_addr (Sp - 8864), ART.shadow_addr Sp)] mem2 m' ->
  LFr.wmono Img.rsegs mem2 m' ->
  ART.addressable mem2 (Sp - 8864) 8864 -> ART.addressable m' (Sp - 8864) 8864 ->
  (forall x : word, w_H W2 x = true -> m' x = mem2 x) ->
  same_but_materialized md2 md' ->
  (forall a, o <= a < o + 36 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B ly2 S2) ly2 own a) ->
  (forall a, v <= a < v + 4 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B ly2 S2) ly2 own a) ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 m' md' k.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k m' md' Sp o v HJ H1 H2 H8 HH HT
    Ho0 Ho1 Hv0 Hv1 NIo NIv MU WM A2 A' Hh Hs Wo Wv.
  assert (UNCH : forall x : word, ~ ((o <= bv_unsigned x < o + 36) \/ (v <= bv_unsigned x < v + 4) \/
                                     (Sp - 8864 <= bv_unsigned x < Sp)) -> m' x = mem2 x).
  { intros x Hx. pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
    destruct (Z_le_gt_dec (ART.shadow_addr (Sp - 8864)) (bv_unsigned x)) as [L1|L1];
      [destruct (Z_lt_le_dec (bv_unsigned x) (ART.shadow_addr Sp)) as [L2|L2]|].
    - rewrite <- (stdpp.bitvector.definitions.Z_to_bv_bv_unsigned _ x). change (Z_to_bv 64 (bv_unsigned x)) with (LMe.wa (bv_unsigned x)).
      exact (cls_win_shadow_unchanged mem2 m' Sp H8 HH HT A2 A' (bv_unsigned x) (conj L1 L2)).
    - apply MU. cbn. repeat split; try exact I; intros [Q1 Q2]; first [lia | apply Hx; lia].
    - apply MU. cbn. repeat split; try exact I; intros [Q1 Q2]; first [lia | apply Hx; lia]. }
  eapply ajournal_exec with (Wr := fun a => (o <= a < o + 36) \/ (v <= a < v + 4) \/ (Sp - 8864 <= a < Sp))
    (memc := mem2) (mdc := md2).
  all: cls_exec_side.
  all: lazymatch goal with
  | |- forall x : word, ~ _ -> _ = _ =>
      intros x Hx; unfold lib.Reusable.YK04.mrestrict; destruct (w_H W2 x); [reflexivity|]; exact (UNCH x Hx)
  | |- lib.Reusable.YK1b.mem_grows _ _ =>
      intros x Hx; unfold lib.Reusable.YK04.mrestrict in *; destruct (w_H W2 x); [exact Hx|];
      pose proof (bv_unsigned_in_range 64 x) as Rx; change (bv_modulus 64) with (2 ^ 64) in Rx;
      destruct (cls_wr_dec o v Sp (bv_unsigned x)) as [HW|HW];
      [ assert (Hn : ~ in_img tfibsegs (bv_unsigned x))
          by (destruct HW as [Q|[Q|Q]];
              [ replace (bv_unsigned x) with (o + (bv_unsigned x - o)) by lia; apply NIo; lia
              | replace (bv_unsigned x) with (v + (bv_unsigned x - v)) by lia; apply NIv; lia
              | apply cls_hi_noimg; unfold ART.HIGHMEM_BEG in HH; lia ]);
        rewrite <- (cls_wview_noimg m' x Hn); apply WM; rewrite (cls_wview_noimg mem2 x Hn); exact Hx
      | rewrite (UNCH x HW); exact Hx ]
  | |- forall a, _ -> awr_byte _ _ _ _ _ _ _ _ =>
      intros a [Ha|[Ha|Ha]]; [exact (Wo a Ha) | exact (Wv a Ha) | left; lia]
  end.
Qed.

End Journal.
(* ---------------------------------------------------------------------------------------------------------------
   6. Facts the composition takes from the cgif world. *)
Ltac cls_seg_bounds :=
  match goal with |- Z.le ?lo _ /\ Z.lt _ (?lo' + ?sz) =>
    let l := eval vm_compute in lo in let h := eval vm_compute in sz in change lo with l; change sz with h end;
  lia.

(* The four segments of image A tile [0x10000, 0x5fe000) (ProgBridge.rsegs_spans). *)
Lemma cls_img_in : forall a, 0x10000 <= a < 0x5fe000 -> in_img tfibsegs a.
Proof.
  intros a Ha. unfold in_img.
  destruct (Z_lt_le_dec a 0x30000) as [L1|L1]; [|destruct (Z_lt_le_dec a 0x9e000) as [L2|L2];
    [|destruct (Z_lt_le_dec a 0xa1000) as [L3|L3]]].
  - eexists. split; [left; reflexivity|]. cls_seg_bounds.
  - eexists. split; [right; left; reflexivity|]. cls_seg_bounds.
  - eexists. split; [right; right; left; reflexivity|]. cls_seg_bounds.
  - eexists. split; [right; right; right; left; reflexivity|]. cls_seg_bounds.
Qed.

Section Facts.
Context {rc : M05.RunCeil}.
Lemma cls_app_of_in_app : forall lo len a, in_app lo len -> lo <= a < lo + len -> ART.app_mem a.
Proof.
  intros lo len a [H0 H1] Ha. pose proof (@M05.alloc_ceiling_lt rc) as Hc.
  unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END.
  unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in H1. lia.
Qed.
End Facts.

(* The 8-aligned shadow cover of a range is visible when the view reads every byte of it (shadow_hull_vis). *)
Lemma cls_hull_vis : forall (W : world tfibsegs) mem d n, 0 <= d -> d + n <= 2 ^ 47 -> 0 < n ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) d n ->
  PB.range_visible (w_H W) (ART.shadow_addr d / 8 * 8)
    (ART.shadow_addr (d + n - 1) / 8 * 8 + 8 - ART.shadow_addr d / 8 * 8).
Proof.
  intros W mem d n Hd Hn Hn0 HV.
  assert (E1 : forall x, ART.shadow_addr x = shadow_addr x)
    by (intros x; unfold ART.shadow_addr, shadow_addr, ART.ASAN_K, SHADOW_OFF; lia).
  split; [unfold ART.shadow_addr, ART.ASAN_K; Z.div_mod_to_equations; lia|].
  split; [unfold ART.shadow_addr, ART.ASAN_K; Z.div_mod_to_equations; lia|].
  intros a Ha. apply (cls_vis_of_view W mem a). apply HV. rewrite <- !E1. lia.
Qed.

Lemma cls_ra_transfer : forall (rd rd' : reader) p n,
  (forall x, p <= x < p + n -> rd' (shadow_of_addr SHADOW_OFF x) = rd (shadow_of_addr SHADOW_OFF x)) ->
  range_addressable rd SHADOW_OFF p n -> range_addressable rd' SHADOW_OFF p n.
Proof. intros rd rd' p n E H x Hx. rewrite (E x Hx). exact (H x Hx). Qed.

Lemma cls_view_eq_pt : forall (H : word -> bool) (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof. intros H m m' a E. unfold aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict. rewrite E. reflexivity. Qed.

Lemma cls_bytes_one : forall m a bs i (d : byte), LMe.bytes_at Img.rsegs m a bs -> (i < length bs)%nat ->
  LMe.bytes_at Img.rsegs m (a + Z.of_nat i) [nth i bs d].
Proof.
  intros m a bs i d (H1 & H2 & H3) Hi. split; [lia|]. split; [cbn; lia|]. intros j Hj. cbn in Hj.
  assert (j = 0%nat) by lia. subst j. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
  rewrite (H3 i Hi). apply nth_error_nth'. exact Hi.
Qed.

(* Bytes read through two views that agree, at bytes visible in both worlds, carry over. *)
Lemma cls_bytes_transfer : forall (H1 H2 : word -> bool) (m1 m2 : word -> option byte) a (bs : list byte),
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> H1 (Z_to_bv 64 (a + i)) = false /\ H2 (Z_to_bv 64 (a + i)) = false) ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> aview tfibsegs H2 m2 (a + i) = aview tfibsegs H1 m1 (a + i)) ->
  LMe.bytes_at Img.rsegs m1 a bs -> LMe.bytes_at Img.rsegs m2 a bs.
Proof.
  intros H1 H2 m1 m2 a bs Ha Hl Hv Ee (B1 & B2 & B3). split; [exact Ha|]. split; [exact Hl|]. intros i Hi.
  destruct (Hv (Z.of_nat i) ltac:(lia)) as [V1 V2].
  pose proof (Ee (Z.of_nat i) ltac:(lia)) as E.
  rewrite (cls_aview_mrd H2 m2 (a + Z.of_nat i) ltac:(lia) V2),
    (cls_aview_mrd H1 m1 (a + Z.of_nat i) ltac:(lia) V1) in E.
  rewrite <- (B3 i Hi). revert E.
  destruct (LMe.mrd Img.rsegs m2 (LMe.wa (a + Z.of_nat i))) as [x|];
    destruct (LMe.mrd Img.rsegs m1 (LMe.wa (a + Z.of_nat i))) as [y|]; cbn; intros E; try discriminate E;
    [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma cls_classify_range : forall n fr us e, classify n fr us = Some e -> 0 <= e <= 5.
Proof.
  intros n fr us e H. unfold classify in H. cbv zeta in H.
  repeat match type of H with context [if ?b then _ else _] => destruct b end; inversion H; lia.
Qed.

(* ret_ok k (YK0s: jalr k 0 lands on k) says k is even, so lib/Lib's ret_pc returns k itself. *)
Lemma cls_ret_pc_ok : forall k : word, ret_ok k -> LMS.ret_pc k = k.
Proof.
  intros k Hk. unfold ret_ok, lib.Reusable.YK14.v_jalr, K11.jalr_tgtZ in Hk. rewrite Z.add_0_r in Hk.
  pose proof (bv_unsigned_in_range 64 k) as Rk. change (bv_modulus 64) with (2 ^ 64) in Rk.
  assert (E2 : Z.land (bv_unsigned k) (-2) = 2 * (bv_unsigned k / 2)).
  { replace (-2) with (Z.lnot (Z.ones 1)) by reflexivity.
    rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
    change (2 ^ 1) with 2. lia. }
  assert (Hev : bv_unsigned k mod 2 = 0).
  { apply (f_equal (@bv_unsigned 64)) in Hk. rewrite Z_to_bv_unsigned, E2 in Hk. unfold bv_wrap in Hk.
    change (bv_modulus 64) with (2 ^ 64) in Hk. Z.div_mod_to_equations. lia. }
  rewrite <- (stdpp.bitvector.definitions.Z_to_bv_bv_unsigned _ k). apply LMS.ret_pc_even; [exact Rk | exact Hev].
Qed.

(* Four present bytes are one ctrl rw cell, holding whatever bytes memory has there. *)
Lemma cls_cells4_of_pres : forall (H : word -> bool) (mem : word -> option byte) a,
  0 <= a -> a + 4 <= 2 ^ 64 -> (forall x, a <= x < a + 4 -> apresent H mem x) ->
  exists vb, length vb = 4%nat /\ LSt.rw_cells Img.rsegs mem a [LCe.CB 4 vb].
Proof.
  intros H mem a Ha Hn Hp.
  destruct (Hp a ltac:(lia)) as [_ [b0 E0]]. destruct (Hp (a + 1) ltac:(lia)) as [_ [b1 E1]].
  destruct (Hp (a + 2) ltac:(lia)) as [_ [b2 E2]]. destruct (Hp (a + 3) ltac:(lia)) as [_ [b3 E3]].
  exists [b0; b1; b2; b3]. split; [reflexivity|]. split.
  - split; [cbn; split; [reflexivity | exact I]|].
    split; [exact Ha|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. unfold LMe.mrd, LMe.wa.
    destruct i as [|[|[|[|i]]]].
    + change (Z.of_nat 0) with 0. rewrite Z.add_0_r, E0. reflexivity.
    + change (Z.of_nat 1) with 1. rewrite E1. reflexivity.
    + change (Z.of_nat 2) with 2. rewrite E2. reflexivity.
    + change (Z.of_nat 3) with 3. rewrite E3. reflexivity.
    + lia.
  - exact (cls_wr_of_pres H mem a 4 Ha Hn Hp).
Qed.

Section WinAddr.
Context {fx : K11.FPState} {rc : M05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.

(* The machine stack's shadow is zero (AR_zshadow_law at the stack entry of zero_shadow_ranges), so every byte of a
   stack sub-range in high memory is addressable. *)
Lemma cls_win_addressable : forall ly S (W : world tfibsegs) mem md lo len,
  AR tfibsegs B ly S W mem md ->
  ly_stk_lo ly <= lo -> lo + len <= ly_stk_hi ly -> 0 <= len -> ART.HIGHMEM_BEG <= lo ->
  lo + len <= ART.APPMEM_END -> ART.addressable mem lo len.
Proof.
  intros ly S W mem md lo len HAR Hlo Hhi Hlen HH HA.
  pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
  pose proof (lo_top ly HLY) as (_ & _ & _ & Lhi & Plo & Phi & Lbeg).
  pose proof (al_zshadow _ _ LAWS ly S W mem md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR
    ltac:(unfold zero_shadow_ranges; left; reflexivity)) as HZ.
  cbn [fst snd] in HZ. unfold zero_shadow in HZ. unfold page_aligned in Plo, Phi.
  split; [unfold ART.HIGHMEM_BEG in HH; lia|]. split; [exact Hlen|]. split; [exact HA|].
  intros i Hi. split; [unfold ART.app_mem; right; lia|].
  set (L := ly_stk_lo ly) in *. set (Hh := ly_stk_hi ly) in *.
  assert (Hj : 0 <= (lo + i) / 8 - L / 8 < (Hh - L) / 8) by (Z.div_mod_to_equations; lia).
  pose proof (HZ _ Hj) as Z0.
  assert (Esh : shadow_of_addr SHADOW_OFF L + ((lo + i) / 8 - L / 8) = ART.shadow_addr (lo + i))
    by (unfold shadow_of_addr, SHADOW_OFF, ART.shadow_addr, ART.ASAN_K; lia).
  rewrite Esh in Z0.
  pose proof (cls_shadow_lt (lo + i) ltac:(unfold ART.APPMEM_END, TASK_SIZE in *; unfold ART.HIGHMEM_BEG in HH; lia))
    as Hs.
  assert (Hv : w_H W (Z_to_bv 64 (ART.shadow_addr (lo + i))) = false)
    by (apply (cls_vis_of_view W mem); rewrite Z0; discriminate).
  rewrite (cls_aview_mrd (w_H W) mem (ART.shadow_addr (lo + i)) ltac:(unfold TASK_SIZE in Hs; lia) Hv) in Z0.
  destruct (LMe.mrd Img.rsegs mem (LMe.wa (ART.shadow_addr (lo + i)))) as [b|]; cbn in Z0; [|discriminate Z0].
  injection Z0 as Z0. exists b. split; [reflexivity|]. unfold ART.shadow_ok. left.
  rewrite cls_byte_signed_small by lia. exact Z0.
Qed.

Lemma cls_frame_noimg : forall ly S (W : world tfibsegs) mem md cid pos a,
  AR tfibsegs B ly S W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid -> ~ in_img tfibsegs a.
Proof.
  intros ly S W mem md cid pos a HAR Hin Ha.
  exact (proj2 (al_client_img _ _ LAWS ly S W mem md a HAR
                  (or_intror (or_introl (ex_intro _ cid (ex_intro _ pos (conj Hin Ha))))))).
Qed.
End WinAddr.

(* route (C): fake-stack frames are 64-aligned (ly_F is page-aligned, YG0f's layout_ok lo_F_al; fs_frame_off is a
   multiple of 64), so the aligned shadow words of a frame's bytes stay inside the frame's shadow: cut_shadow's (F)
   disjunct covers the region of record of stretch 2 at the caller's frames of o and u. *)
Lemma cls_frame_addr_64 : forall ly cid pos, ly_F ly mod 4096 = 0 -> 0 <= cid -> frame_addr ly cid pos mod 64 = 0.
Proof.
  intros ly cid pos HF Hc.
  set (X := ly_F ly / 4096).
  assert (D : ly_F ly = 4096 * X)
    by (pose proof (Z.div_mod (ly_F ly) 4096 ltac:(lia)) as D; rewrite HF, Z.add_0_r in D; exact D).
  assert (E : frame_addr ly cid pos = (X * 64 + 576 + cid * 16384 + pos * 2 ^ cid) * 64).
  { unfold lib.Reusable.YG0f.frame_addr, lib.Reusable.YG0f.fs_frame_off, lib.Reusable.YG0f.kFakeFramesOff,
      lib.Reusable.YG00.fs_frame_bytes, lib.Reusable.YG00.kStackSizeLog.
    rewrite (Z.shiftl_mul_pow2 64 cid Hc). change (Z.shiftl 1 20) with 1048576. rewrite D. ring. }
  rewrite E. apply Z_mod_mult.
Qed.

Lemma cls_sh_word_frame : forall ly cid pos p n a, ly_F ly mod 4096 = 0 -> 0 <= cid ->
  frame_addr ly cid pos <= p -> p + n <= frame_addr ly cid pos + fs_frame_bytes cid -> 0 < n ->
  SWO.sh_word_on p n a ->
  lib.Reusable.YG0f.shadow_addr (frame_addr ly cid pos) <= a <
  lib.Reusable.YG0f.shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8.
Proof.
  intros ly cid pos p n a HF Hc H1 H2 Hn (_ & Ha1 & Ha2).
  pose proof (cls_frame_addr_64 ly cid pos HF Hc) as H64.
  assert (EB : fs_frame_bytes cid = 64 * 2 ^ cid)
    by (unfold lib.Reusable.YG00.fs_frame_bytes; apply Z.shiftl_mul_pow2; exact Hc).
  pose proof (Z.pow_pos_nonneg 2 cid ltac:(lia) Hc) as Hq.
  rewrite EB in *.
  set (q := 2 ^ cid) in *. set (F0 := frame_addr ly cid pos) in *.
  unfold RNA.sh_al8_lo, RNA.sh_al8_hi, ART.shadow_addr, ART.ASAN_K in Ha1, Ha2.
  unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF.
  Z.div_mod_to_equations. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   7. Q7: CtrlCallerJ's tcj_kept over the window [S - 8864, S), composed from stretch A's munch, reac_ctrl_parse's
   acall_kept and stretch B's munch (with its window shadow unchanged, and v's bytes unchanged when classify = None). *)
Section Tcj.
Context {fx : K11.FPState} {rc : M05.RunCeil} {SK : I16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.

Lemma cls_tcj : forall lyc Sc (W W2 : world tfibsegs) memc mdc m1 mem2 m3 Sp o v (cN : Prop),
  AR tfibsegs B lyc Sc W memc mdc ->
  M05.alloc_ceiling <= Sp - 8864 -> Sp <= 2 ^ 47 ->
  0 <= o -> o + 36 <= M05.alloc_ceiling -> 0 <= v -> v + 4 <= M05.alloc_ceiling ->
  (forall i, 0 <= i < 36 -> ~ in_img tfibsegs (o + i)) -> (forall i, 0 <= i < 4 -> ~ in_img tfibsegs (v + i)) ->
  (cN \/ ~ cN) ->
  LFr.munch [(Sp + -64, Sp)] memc m1 ->
  acall_kept tfibsegs B lyc Sc W m1 W2 mem2 (Sp - 64 - REAC_CTRL_PARSE_STK) (Sp - 64) (fun a => o <= a < o + 36) ->
  LFr.munch [(o, o + 36); (v, v + 4); (Sp - 8864, Sp); (ART.shadow_addr (Sp - 8864), ART.shadow_addr Sp)] mem2 m3 ->
  (~ cN -> forall i, 0 <= i < 4 -> m3 (LMe.wa (v + i)) = mem2 (LMe.wa (v + i))) ->
  (forall a, Sp - 8864 <= a < Sp -> apresent (w_H W2) m3 a) ->
  tcj_kept (PI := PI_ctrl) B REAC_CTRL_CLASSIFY_BOX_FRAME_STK lyc Sc W memc W2 m3 Sp
    (fun a => o <= a < o + 36 \/ (cN /\ v <= a < v + 4)).
Proof.
  intros lyc Sc W W2 memc mdc m1 mem2 m3 Sp o v cN HAR B1 B2 Ho0 Ho1 Hv0 Hv1 NIo NIv DcN MUa
    (KP1 & KP2 & KP3 & KP4 & KP5 & KP6) MUb UNv P3.
  pose proof (@M05.alloc_ceiling_value rc) as [[Hc0 Hc1] _].
  unfold REAC_CTRL_PARSE_STK, ESTACK in KP1, KP5.
  assert (SW1 : ART.shadow_addr Sp <= 0x10007fff8000)
    by (unfold ART.shadow_addr, ART.ASAN_K; Z.div_mod_to_equations; lia).
  assert (SW0 : 0x20087ff7000 <= ART.shadow_addr (Sp - 8864))
    by (unfold ART.shadow_addr, ART.ASAN_K; Z.div_mod_to_equations; lia).
  assert (STEPB : forall H a, 0 <= a < 2 ^ 64 -> ~ (o <= a < o + 36) -> ~ (cN /\ v <= a < v + 4) ->
                    ~ (Sp - 8864 <= a < Sp) -> ~ (ART.shadow_addr (Sp - 8864) <= a < ART.shadow_addr Sp) ->
                    aview tfibsegs H m3 a = aview tfibsegs H mem2 a).
  { intros H a Ha Hno HnE Hnw Hns.
    destruct (Z_le_gt_dec v a) as [V1|V1]; [destruct (Z_lt_le_dec a (v + 4)) as [V2|V2]|].
    - destruct DcN as [Hc|Hc]; [exfalso; exact (HnE (conj Hc (conj V1 V2)))|].
      apply cls_view_eq_pt. specialize (UNv Hc (a - v) ltac:(lia)).
      replace (v + (a - v)) with a in UNv by lia. exact UNv.
    - apply (cls_view_munch _ H mem2 m3 a MUb Ha). cbn.
      repeat split; try exact I; intros [Q1 Q2]; first [lia | apply Hno; lia | apply Hnw; lia | apply Hns; lia].
    - apply (cls_view_munch _ H mem2 m3 a MUb Ha). cbn.
      repeat split; try exact I; intros [Q1 Q2]; first [lia | apply Hno; lia | apply Hnw; lia | apply Hns; lia]. }
  assert (STEPA : forall H a, 0 <= a < 2 ^ 64 -> ~ (Sp - 64 <= a < Sp) ->
                    aview tfibsegs H m1 a = aview tfibsegs H memc a).
  { intros H a Ha Hn. apply (cls_view_munch _ H memc m1 a MUa Ha). cbn.
    split; [intros [Q1 Q2]; apply Hn; lia | exact I]. }
  unfold tcj_kept, REAC_CTRL_CLASSIFY_BOX_FRAME_STK.
  repeat match goal with |- context [@pa_segs ?g ?L ?P] => change (@pa_segs g L P) with tfibsegs end.
  split; [|split; [|split; [|split; [|split]]]].
  - (* high memory outside the window *)
    intros a Ha Hw HE.
    rewrite (STEPB (w_H W2) a ltac:(lia));
      [ | intros Q; apply HE; left; exact Q | intros Q; apply HE; right; exact Q | exact Hw | lia ].
    rewrite (KP1 a Ha ltac:(lia)). apply STEPA; lia.
  - (* the caller's blocks *)
    intros b mm i Hin Hi HE.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b mm HAR Hin) as (_ & Hb0 & Hb1 & Hb2 & _).
    pose proof (cls_app_of_in_app _ _ (b + i) Hb2 ltac:(lia)) as Happ.
    unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END in Happ.
    rewrite (STEPB (w_H W2) (b + i) ltac:(lia));
      [ | intros Q; apply HE; left; exact Q | intros Q; apply HE; right; exact Q | lia | lia ].
    rewrite (KP2 b mm i Hin Hi ltac:(intros Q; apply HE; left; exact Q)). apply STEPA; lia.
  - (* the image *)
    intros a Hai Ho He.
    pose proof (ctrl_img_range a Hai) as Hia.
    rewrite (STEPB (w_H W2) a ltac:(lia)); [ | | | lia | lia].
    + rewrite (KP3 a Hai Ho He). apply STEPA; lia.
    + intros Q. apply (NIo (a - o) ltac:(lia)). replace (o + (a - o)) with a by lia. exact Hai.
    + intros [_ Q]. apply (NIv (a - v) ltac:(lia)). replace (v + (a - v)) with a by lia. exact Hai.
  - (* the caller's frames and their shadow *)
    intros cid pos a Hin Ha HE.
    destruct (frames_bounds tfibsegs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F0 & F1 & F2).
    pose proof (fs_frame_bytes_nonneg cid) as Fn.
    assert (Hra : 0 <= a < 2 ^ 64 /\ ~ (Sp - 8864 <= a < Sp) /\
                  ~ (ART.shadow_addr (Sp - 8864) <= a < ART.shadow_addr Sp) /\ a < Sp - 64).
    { destruct Ha as [Ha|Ha]; unfold in_zr, frame_rng in Ha; cbn [fst snd] in Ha.
      - pose proof (cls_app_of_in_app _ _ a F2 Ha) as Happ.
        unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END in Happ. lia.
      - unfold shadow_addr, SHADOW_OFF in Ha. unfold ART.shadow_addr, ART.ASAN_K.
        Z.div_mod_to_equations. lia. }
    destruct Hra as (Ha64 & Hw & Hs & Hlt).
    rewrite (STEPB (w_H W2) a Ha64);
      [ | intros Q; apply HE; left; exact Q | intros Q; apply HE; right; exact Q | exact Hw | exact Hs ].
    rewrite (KP4 cid pos a Hin Ha ltac:(intros Q; apply HE; left; exact Q)). apply STEPA; lia.
  - (* presence in high memory outside the window *)
    intros a Ha Hw Hp.
    assert (E3 : m3 (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a)).
    { apply (cls_munch_at _ mem2 m3 a MUb ltac:(lia)). cbn.
      repeat split; try exact I; intros [Q1 Q2]; first [lia | apply Hw; lia]. }
    assert (E1 : m1 (Z_to_bv 64 a) = memc (Z_to_bv 64 a)).
    { apply (cls_munch_at _ memc m1 a MUa ltac:(lia)). cbn. split; [intros [Q1 Q2]; lia | exact I]. }
    destruct Hp as [Hh [b Hb]].
    assert (Hp1 : apresent (w_H W) m1 a) by (split; [exact Hh | exists b; rewrite E1; exact Hb]).
    destruct (KP5 a Ha ltac:(lia) Hp1) as [Hh2 [b2 Hb2]].
    split; [exact Hh2|]. exists b2. rewrite E3. exact Hb2.
  - (* the window *)
    exact P3.
Qed.
End Tcj.

(* ---------------------------------------------------------------------------------------------------------------
   8. The glue. *)
Section m.
Context {fx : K11.FPState} {rc : M05.RunCeil}.
Context {SK : I16.sink_head}.
#[local] Notation SEGS := tfibsegs.
Variable B : asyms.
Variables RLO RHI : Z.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis LAWS : AR_laws tfibsegs B.
(* reac_ctrl_parse (a working branch 55301a93133), its own spec type. *)
Hypothesis TPARSE : treac_ctrl_parse_spec (SK := SK) B RLO RHI.
(* The ctrl runtime facts at a cut (a Theorem Labs lane 05:04Z), route (C) (L3-recipe.md (a working note, not in this delivery), a Theorem Labs lane 13:12Z): (i) RT_used_C:
   a Theorem Labs lane's PROVED ProgWorldRtC.RT_used_of_AR_C, cited by name; its premises beyond LAWS are TSYMS only (no
   AR_states_vis0_shadow: the former Section hypothesis VIS0 is gone). (ii) ro_agree: RO_AR, now a Let bound to
   a Theorem Labs lane's PROVED ProgWorldCtlRt.ro_agree_of_AR with its AR_states_owned_ro premise discharged by
   ProgWorldOwnedRo.AR_states_owned_ro_of_AR (the 4th part of ctl_rt_C_of_AR, from the same AR), supplied at each cut
   memory with the read-only view (C2 at entry; C2 carried by stretch A's munch and parse's acall_kept after parse);
   the normalization of section 1 turns it into the stretches' mem_inv. *)
Hypothesis TSYMS : PW_AF0m.CtrlTSyms B.
Let RO_AR : forall ly S (W : world tfibsegs) mem md, AR tfibsegs B ly S W mem md ->
  lib.Reusable.APostBase.arodata_okP tfibsegs RLO RHI B (aview tfibsegs (w_H W) mem) -> ACK.ro_agree_at mem :=
  fun ly S W mem md HAR Hro =>
    PWCR.ro_agree_of_AR B TSYMS (PWOR.AR_states_owned_ro_of_AR B TSYMS) RLO RHI ly S W mem md HAR Hro.

Theorem pb_reac_ctrl_classify_box_frame : treac_ctrl_classify_box_frame_spec (SK := SK) B RLO RHI.
Proof.
  unfold treac_ctrl_classify_box_frame_spec.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs f n u o v fr us
    C1 C2 C3a C3b C4a C4b C5f C5n C5u C5o C5v C5r C5fr C5ur C7a C7b C7c C8 C9 C10 C11 C12 C13 C14 C15 C16 C17
    C18 C19 C20 C21 C22.
  set (Sp := spZ regs) in *.
  pose proof C1 as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _ & _).
  destruct Hastk as (_ & HSTK & Hceil & Hlo & Hhi & H47 & _).
  pose proof (@M05.alloc_ceiling_value rc) as [[Hc0 Hc1] _].
  assert (HT : TASK_SIZE = 2 ^ 47) by reflexivity.
  unfold REAC_CTRL_CLASSIFY_BOX_FRAME_STK in C7b.
  assert (B1 : M05.alloc_ceiling <= Sp - 8864) by lia.
  assert (B2 : Sp <= 2 ^ 47) by lia.
  assert (B3 : ART.HIGHMEM_BEG <= Sp - 8864) by (unfold ART.HIGHMEM_BEG; lia).
  assert (Sp64 : 0 <= Sp < 2 ^ 64) by lia.
  destruct (PWRC.RT_used_of_AR_C B TSYMS LAWS _ _ _ _ _ HAR) as (RACc & _ & _ & _ & _ & _ & _ & _).
  pose proof (RO_AR _ _ _ _ _ HAR (fun a Ha => C2 a Ha)) as ROc.
  (* the caller's frames of o and v, and their bounds *)
  pose proof C12 as ((co & po & Ino & Hco & Hfo8 & Hfo1 & Hfo2) & Ho8 & RAo).
  pose proof C14 as ((cv & pv & Inv & Hcv & Hfv8 & Hfv1 & Hfv2) & Hv8 & RAv).
  destruct (frames_bounds tfibsegs B LAWS lyc Sc W memc mdc co po HAR Ino) as (Fo1 & Fo2 & Fo3).
  destruct (frames_bounds tfibsegs B LAWS lyc Sc W memc mdc cv pv HAR Inv) as (Fv1 & Fv2 & Fv3).
  pose proof (fs_frame_bytes_nonneg co) as Fon. pose proof (fs_frame_bytes_nonneg cv) as Fvn.
  assert (Fo8s : fs_frame_bytes co mod 8 = 0).
  { unfold fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by lia.
    replace (64 * 2 ^ co) with ((8 * 2 ^ co) * 8) by lia. apply Z_mod_mult. }
  assert (Fv8s : fs_frame_bytes cv mod 8 = 0).
  { unfold fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by lia.
    replace (64 * 2 ^ cv) with ((8 * 2 ^ cv) * 8) by lia. apply Z_mod_mult. }
  assert (NIo : forall i, 0 <= i < 36 -> ~ in_img tfibsegs (o + i))
    by (intros i Hi; apply (cls_frame_noimg B LAWS lyc Sc W memc mdc co po); [exact HAR | exact Ino | lia]).
  assert (NIv : forall i, 0 <= i < 4 -> ~ in_img tfibsegs (v + i))
    by (intros i Hi; apply (cls_frame_noimg B LAWS lyc Sc W memc mdc cv pv); [exact HAR | exact Inv | lia]).
  (* G0: classify's entry as stretch A's start state *)
  rewrite PB.cfg_at_MS.
  assert (EA : A_reac_ctrl_classify_box_frameP = 0x831b8) by reflexivity.
  rewrite EA. change (K11.seg_rom tfibsegs) with (LPE.seg_rom Img.rsegs).
  assert (XR0 : LRg.xregs_eqv
    (LFr.mkR (reg_get regs 1) (Z_to_bv 64 Sp) (reg_get regs 3) (reg_get regs 4) (reg_get regs 5) (reg_get regs 6)
       (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 u)
       (Z_to_bv 64 o) (Z_to_bv 64 v) (reg_get regs 15) (reg_get regs 16) (reg_get regs 17) (reg_get regs 18)
       (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24)
       (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) (reg_get regs 28) (reg_get regs 29) (reg_get regs 30)
       (reg_get regs 31)) regs).
  { apply LRg.xregs_eqv_sym. apply LRg.mkR_eqv_of;
      first [ reflexivity | exact C5f | exact C5n | exact C5u | exact C5o | exact C5v
            | (unfold Sp, spZ; rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned; reflexivity) ]. }
  refine (SRr_xregs_eqv tfibsegs W _ regs _ _ _ _ _ _ _ _ _ XR0).
  apply cls_liftA.
  { rewrite HT. lia. }
  { exact B3. }
  { apply (cls_stk_of_pres (w_H W)); [lia | lia | intros a Ha; apply Hpres; lia]. }
  { exact ROc. }
  { exact RACc. }
  { split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (Hpres a ltac:(lia))). }
  intros ms1 md1 (m1 & E1 & MU1 & WM1 & ST1 & RW1) Hh1 Hs1. subst ms1.
  (* G1: the journal over stretch A, the read-only view at m1, and reac_ctrl_parse's spec *)
  assert (J1 : ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m1 md1 k).
  { apply (cls_journal_A B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k m1 md1 Sp C1);
      first [lia | exact MU1 | exact WM1 | exact Hh1 | exact Hs1]. }
  assert (C2' : arodata_okS tfibsegs B RLO RHI (aview tfibsegs (w_H W) m1)).
  { intros a Hro Ho He. rewrite <- (C2 a Hro Ho He).
    assert (Hai : in_img tfibsegs a)
      by (destruct Hro as [(s & Hs & _ & Hr) | Hg]; [exists s; split; [exact Hs | exact Hr] | exact (RELRO_IMG a Hg)]).
    pose proof (ctrl_img_range a Hai) as Hia.
    apply (cls_view_munch [(Sp + -64, Sp)]); [exact MU1 | lia | cbn; split; [lia | exact I]]. }
  assert (VA : forall H a, 0 <= a < Sp - 64 -> aview tfibsegs H m1 a = aview tfibsegs H memc a).
  { intros H a Ha. apply (cls_view_munch [(Sp + -64, Sp)]); [exact MU1 | lia | cbn; split; [lia | exact I]]. }
  set (regsA := LFr.mkR (Z_to_bv 64 0x83200) (Z_to_bv 64 (Sp + -64)) (reg_get regs 3) (reg_get regs 4)
         (reg_get regs 5) (reg_get regs 6) (reg_get regs 7) (Z_to_bv 64 v) (reg_get regs 9) (Z_to_bv 64 f)
         (Z_to_bv 64 n) (Z_to_bv 64 o) (Z_to_bv 64 o) (Z_to_bv 64 v) (reg_get regs 15) (reg_get regs 16)
         (reg_get regs 17) (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 u) (Z_to_bv 64 ART.ASAN_K) (reg_get regs 22)
         (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27)
         (reg_get regs 28) (reg_get regs 29) (reg_get regs 30) (reg_get regs 31)).
  assert (ESA : spZ regsA = Sp - 64).
  { unfold spZ. change (K11.getr regsA 2) with (Z_to_bv 64 (Sp + -64)).
    rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; lia). lia. }
  assert (EP : A_reac_ctrl_parseP = 0x83578) by reflexivity.
  change (SRr tfibsegs W (cfg_at tfibsegs A_reac_ctrl_parseP regsA m1 md1)
            (treac_ctrl_classify_box_frame_post (SK := SK) B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
               n o v fr us)).
  eapply SRr_bind.
  { eapply (TPARSE STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m1 md1 k regsA f n o fr).
    - exact J1.
    - exact C2'.
    - apply ret_ok_even. reflexivity.
    - change (raZ regsA) with 0x83200. lia.
    - exact C4a.
    - exact C4b.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact C5r.
    - rewrite ESA. Z.div_mod_to_equations. lia.
    - rewrite ESA. unfold REAC_CTRL_PARSE_STK, ESTACK. lia.
    - rewrite ESA. lia.
    - exact C8.
    - exact C9.
    - intros _. split; [exact (ex_intro _ co (ex_intro _ po (conj Ino (conj Hco (conj Hfo8 (conj Hfo1 Hfo2))))))|].
      split; [exact Ho8|].
      apply (cls_ra_transfer (aview tfibsegs (w_H W) memc)); [|exact RAo].
      intros x Hx. apply VA. unfold shadow_of_addr, SHADOW_OFF. Z.div_mod_to_equations. lia.
    - intros _ a Ha. exact (C13 a Ha).
    - exact C10.
    - intros Hn i Hi. rewrite <- (C11 Hn i Hi). apply VA.
      destruct (C9 Hn) as (Lf & InF & HLf).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ f Lf HAR InF) as (_ & Hf0 & Hf1 & _). lia. }
  (* G2: from reac_ctrl_parse's post to stretch B's start state *)
  intros W2 c2 Hle (ly2 & S2 & regs2 & mem2 & md2 & Ec2 & J2 & Hpr2 & Hfr2 & Hbl2 & _ & Ha02 & Ho2 & KP).
  subst c2.
  rewrite ESA in KP.
  pose proof KP as (KP1 & KP2 & KP3 & KP4 & KP5 & KP6).
  pose proof J2 as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _ & _ & _).
  destruct (PWRC.RT_used_of_AR_C B TSYMS LAWS _ _ _ _ _ HAR2) as (RAC2 & RCUT2 & RIMG2 & _ & RCF2 & _ & _ & RR2).
  assert (C2'' : lib.Reusable.APostBase.arodata_okP tfibsegs RLO RHI B (aview tfibsegs (w_H W2) mem2)).
  { intros a Hro Ho He.
    assert (Hai : in_img tfibsegs a)
      by (destruct Hro as [(s & Hs & _ & Hr) | Hg]; [exists s; split; [exact Hs | exact Hr] | exact (RELRO_IMG a Hg)]).
    rewrite (KP3 a Hai Ho He). exact (C2' a Hro Ho He). }
  pose proof (RO_AR _ _ _ _ _ HAR2 C2'') as RO2.
  assert (HF2 : forall c p, frame_addr ly2 c p = frame_addr lyc c p).
  { intros c p. unfold frame_addr.
    destruct Hly as (_ & _ & _ & _ & _ & EF1 & _). destruct Hly2 as (_ & _ & _ & _ & _ & EF2 & _).
    rewrite EF1, EF2. reflexivity. }
  assert (HSL2 : ly_stk_lo ly2 = ly_stk_lo ly /\ ly_stk_hi ly2 = ly_stk_hi ly).
  { destruct Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & E1' & E2' & _). split; assumption. }
  assert (Ino2 : In (co, po) (frames S2)) by (rewrite Hfr2; exact Ino).
  assert (Inv2 : In (cv, pv) (frames S2)) by (rewrite Hfr2; exact Inv).
  (* the caller's v bytes at the parse-return memory *)
  destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 cv pv HAR2 Inv2) as (_ & _ & Pv2 & _).
  destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 co po HAR2 Ino2) as (_ & _ & Po2 & _).
  rewrite HF2 in Pv2, Po2.
  destruct (cls_cells4_of_pres (w_H W2) mem2 v ltac:(lia) ltac:(lia)
              (fun x Hx => proj1 (Pv2 x ltac:(lia)))) as (vb & Lvb & HVv).
  (* visibility at W2 *)
  assert (VO2 : PB.range_visible (w_H W2) o 36)
    by (apply (proj1 (PWF.frame_vis B LAWS ly2 S2 W2 mem2 md2 co po o 36 HAR2 Ino2 ltac:(rewrite HF2; lia)
                        ltac:(rewrite HF2; lia)))).
  assert (VV2 : PB.range_visible (w_H W2) v 4)
    by (apply (proj1 (PWF.frame_vis B LAWS ly2 S2 W2 mem2 md2 cv pv v 4 HAR2 Inv2 ltac:(rewrite HF2; lia)
                        ltac:(rewrite HF2; lia)))).
  (* the stretch-B start state *)
  change (K11.mkst regs2 (K11.getr regsA 1) mem2 (K11.seg_rom tfibsegs))
    with (LMS.MS regs2 K11.fp_regs (Z_to_bv 64 0x83200) K11.fp_csr None mem2 (LPE.seg_rom Img.rsegs)).
  assert (XR2 : LRg.xregs_eqv
    (LFr.mkR (reg_get regs2 1) (Z_to_bv 64 (Sp + -64)) (reg_get regs 3) (reg_get regs 4) (reg_get regs2 5)
       (reg_get regs2 6) (reg_get regs2 7) (Z_to_bv 64 v) (reg_get regs2 9) (Z_to_bv 64 (fst (ctrlparse n fr)))
       (reg_get regs2 11) (reg_get regs2 12) (reg_get regs2 13) (reg_get regs2 14) (reg_get regs2 15)
       (reg_get regs2 16) (reg_get regs2 17) (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 u) (Z_to_bv 64 ART.ASAN_K)
       (reg_get regs2 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26)
       (reg_get regs 27) (reg_get regs2 28) (reg_get regs2 29) (reg_get regs2 30) (reg_get regs2 31)) regs2).
  { apply LRg.xregs_eqv_sym. apply LRg.mkR_eqv_of;
      first [ reflexivity | exact Ha02
            | exact (Hpr2 2 ltac:(unfold acallee_saved; lia)) | exact (Hpr2 3 ltac:(unfold acallee_saved; lia))
            | exact (Hpr2 4 ltac:(unfold acallee_saved; lia)) | exact (Hpr2 8 ltac:(unfold acallee_saved; lia))
            | exact (Hpr2 18 ltac:(unfold acallee_saved; lia)) | exact (Hpr2 19 ltac:(unfold acallee_saved; lia))
            | exact (Hpr2 20 ltac:(unfold acallee_saved; lia)) | exact (Hpr2 21 ltac:(unfold acallee_saved; lia))
            | exact (Hpr2 23 ltac:(unfold acallee_saved; lia)) | exact (Hpr2 24 ltac:(unfold acallee_saved; lia))
            | exact (Hpr2 25 ltac:(unfold acallee_saved; lia)) | exact (Hpr2 26 ltac:(unfold acallee_saved; lia))
            | exact (Hpr2 27 ltac:(unfold acallee_saved; lia)) ]. }
  refine (SRr_xregs_eqv tfibsegs W2 _ regs2 _ _ _ _ _ _ _ _ _ XR2).
  apply (cls_liftB W2 md2 (reg_get regs 1) (reg_get regs 3) (reg_get regs 4) (reg_get regs 8) (reg_get regs 9)
           (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
           (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27)
           K11.fp_regs K11.fp_csr mem2 f n u o v Sp fr us vb
           (reg_get regs2 1) (reg_get regs2 5) (reg_get regs2 6) (reg_get regs2 7) (reg_get regs2 9)
           (reg_get regs2 11) (reg_get regs2 12) (reg_get regs2 13) (reg_get regs2 14) (reg_get regs2 15)
           (reg_get regs2 16) (reg_get regs2 17) (reg_get regs2 22) (reg_get regs2 28) (reg_get regs2 29)
           (reg_get regs2 30) (reg_get regs2 31)).
  - exact C5fr.
  - exact C5ur.
  - lia.
  - lia.
  - rewrite HT. lia.
  - exact C7a.
  - exact C10.
  - exact C16.
  - (* HF *)
    intros Hn. destruct (C9 Hn) as (Lf & InF & HLf).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ f Lf HAR InF) as (_ & Hf0 & Hf1 & _).
    assert (InF2 : In (f, Lf) (ablocks B ly2 S2)) by (rewrite Hbl2; exact InF).
    pose proof (sep_block_frame tfibsegs B LAWS lyc Sc W memc mdc f Lf co po HAR InF Ino) as SBo.
    unfold zdisjoint in SBo; cbn [fst snd] in SBo.
    pose proof (PWH.heap_vis B LAWS ly2 S2 W2 mem2 md2 f Lf f 50 HAR2 InF2 ltac:(lia) ltac:(lia)) as (_ & _ & VF).
    split; [lia|]. split; [rewrite HT; lia|]. split; [|left; lia].
    apply (cls_bytes_of_view (w_H W2) mem2 f fr cp_z); [lia | rewrite C10; lia | |].
    + intros i Hi. rewrite C10 in Hi. apply VF. lia.
    + intros i Hi. rewrite C10 in Hi.
      rewrite (KP2 f Lf (Z.of_nat i) InF ltac:(lia) ltac:(cbn; lia)).
      rewrite VA by lia. exact (C11 Hn i Hi).
  - (* HU *)
    intros Hn. destruct (C17 Hn) as ((cu & pu & Inu & Hcu & Hfu8 & Hfu1 & Hfu2) & Hu8 & RAu).
    destruct (frames_bounds tfibsegs B LAWS lyc Sc W memc mdc cu pu HAR Inu) as (Fu1 & Fu2 & Fu3).
    pose proof (fs_frame_bytes_nonneg cu) as Fun.
    assert (Inu2 : In (cu, pu) (frames S2)) by (rewrite Hfr2; exact Inu).
    pose proof (proj1 (PWF.frame_vis B LAWS ly2 S2 W2 mem2 md2 cu pu u 6 HAR2 Inu2 ltac:(rewrite HF2; lia)
                         ltac:(rewrite HF2; lia))) as (_ & _ & VU).
    split; [rewrite HT; lia|]. split; [|left; lia].
    apply (cls_bytes_of_view (w_H W2) mem2 u us cp_z); [lia | rewrite C16; lia | |].
    + intros i Hi. rewrite C16 in Hi. apply VU. lia.
    + intros i Hi. rewrite C16 in Hi.
      rewrite (KP4 cu pu (u + Z.of_nat i) Inu ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; lia) ltac:(lia)).
      rewrite VA by lia. exact (C18 Hn i Hi).
  - lia.
  - Z.div_mod_to_equations. lia.
  - rewrite HT. lia.
  - left. lia.
  - intros Hn. destruct (C9 Hn) as (Lf & InF & HLf).
    pose proof (sep_block_frame tfibsegs B LAWS lyc Sc W memc mdc f Lf co po HAR InF Ino) as SBo.
    unfold zdisjoint in SBo; cbn [fst snd] in SBo. lia.
  - exact C19.
  - lia.
  - Z.div_mod_to_equations. lia.
  - rewrite HT. lia.
  - left. lia.
  - exact C20.
  - exact C22.
  - exact C21.
  - exact B3.
  - (* AFU *)
    intros Hn. destruct (C9 Hn) as (Lf & InF & HLf).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ f Lf HAR InF) as (_ & Hf0 & Hf1 & Hf2 & _).
    assert (InF2 : In (f, Lf) (ablocks B ly2 S2)) by (rewrite Hbl2; exact InF).
    destruct (C17 Hn) as ((cu & pu & Inu & Hcu & Hfu8 & Hfu1 & Hfu2) & Hu8 & RAu).
    destruct (frames_bounds tfibsegs B LAWS lyc Sc W memc mdc cu pu HAR Inu) as (Fu1 & Fu2 & Fu3).
    destruct (al_frames _ _ LAWS lyc Sc W memc mdc cu pu HAR Inu) as (Fu32 & _).
    pose proof (fs_frame_bytes_nonneg cu) as Fun.
    assert (Fu8 : fs_frame_bytes cu mod 8 = 0).
    { unfold fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by lia.
      replace (64 * 2 ^ cu) with ((8 * 2 ^ cu) * 8) by lia. apply Z_mod_mult. }
    pose proof (M05.alloc_ceiling_lt) as Hcl.
    split; [|split; [|split]].
    + apply (cls_addressable_of_view W2 mem2 f 50); [lia | lia | unfold ART.APPMEM_END; lia | |].
      * intros i Hi. apply (cls_app_of_in_app _ _ (f + i) Hf2). lia.
      * exact (range_addressable_of_block tfibsegs B LAWS ly2 S2 W2 mem2 md2 f Lf f 50 HAR2 InF2
                 ltac:(lia) ltac:(lia)).
    + apply (cls_addressable_of_view W2 mem2 u 6); [lia | lia | unfold ART.APPMEM_END; lia | |].
      * intros i Hi. apply (cls_app_of_in_app _ _ (u + i) Fu3). lia.
      * apply (cls_ra_transfer (aview tfibsegs (w_H W) memc)); [|exact RAu].
        intros x Hx. rewrite (KP4 cu pu (shadow_of_addr SHADOW_OFF x) Inu).
        { apply VA. unfold shadow_of_addr, SHADOW_OFF. Z.div_mod_to_equations. lia. }
        { right. unfold in_zr, shadow_addr, shadow_of_addr, SHADOW_OFF. cbn [fst snd].
          Z.div_mod_to_equations. lia. }
        { unfold shadow_of_addr, SHADOW_OFF. pose proof (cls_app_of_in_app _ _ o Fo3 ltac:(lia)) as Ap.
          unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END in Ap.
          Z.div_mod_to_equations. lia. }
    + apply (cls_app_of_in_app _ _ (u + 6) Fu3). Z.div_mod_to_equations. lia.
    + apply (cls_app_of_in_app _ _ (u + 7) Fu3). Z.div_mod_to_equations. lia.
  - (* AO *)
    apply (cls_addressable_of_view W2 mem2 o 36); [lia | lia | pose proof M05.alloc_ceiling_lt; unfold ART.APPMEM_END; lia | |].
    + intros i Hi. apply (cls_app_of_in_app _ _ (o + i) Fo3). lia.
    + apply (cls_ra_transfer (aview tfibsegs (w_H W) memc)); [|exact RAo].
      intros x Hx. rewrite (KP4 co po (shadow_of_addr SHADOW_OFF x) Ino).
      { apply VA. unfold shadow_of_addr, SHADOW_OFF. Z.div_mod_to_equations. lia. }
      { right. unfold in_zr, shadow_addr, shadow_of_addr, SHADOW_OFF. cbn [fst snd].
        Z.div_mod_to_equations. lia. }
      { unfold shadow_of_addr, SHADOW_OFF. pose proof (cls_app_of_in_app _ _ o Fo3 ltac:(lia)) as Ap.
        unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END in Ap.
        Z.div_mod_to_equations. lia. }
  - (* AV *)
    apply (cls_addressable_of_view W2 mem2 v 4); [lia | lia | pose proof M05.alloc_ceiling_lt; unfold ART.APPMEM_END; lia | |].
    + intros i Hi. apply (cls_app_of_in_app _ _ (v + i) Fv3). lia.
    + apply (cls_ra_transfer (aview tfibsegs (w_H W) memc)); [|exact RAv].
      intros x Hx. rewrite (KP4 cv pv (shadow_of_addr SHADOW_OFF x) Inv).
      { apply VA. unfold shadow_of_addr, SHADOW_OFF. Z.div_mod_to_equations. lia. }
      { right. unfold in_zr, shadow_addr, shadow_of_addr, SHADOW_OFF. cbn [fst snd].
        Z.div_mod_to_equations. lia. }
      { unfold shadow_of_addr, SHADOW_OFF. pose proof (cls_app_of_in_app _ _ o Fo3 ltac:(lia)) as Ap.
        unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END in Ap.
        Z.div_mod_to_equations. lia. }
  - (* HVR *)
    destruct (Z_le_gt_dec (v + 4) ART.RT_LO); [left; lia|].
    destruct (Z_le_gt_dec ART.RT_HI v); [right; lia|].
    exfalso. apply (NIv (Z.max v ART.RT_LO - v)); [unfold ART.RT_LO, ART.RT_HI in *; lia|].
    replace (v + (Z.max v ART.RT_LO - v)) with (Z.max v ART.RT_LO) by lia.
    apply cls_img_in. unfold ART.RT_LO, ART.RT_HI in *. lia.
  - exact NIo.
  - exact NIv.
  - (* VW *)
    split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (Hpres2 a ltac:(lia))).
  - exact VO2.
  - apply (cls_hull_vis W2 mem2 o 36); [lia | pose proof M05.alloc_ceiling_lt; lia | lia |].
    exact (CFr.shadow_hull_vis_of_frame tfibsegs B LAWS ly2 S2 W2 mem2 md2 co po o 36 HAR2 Ino2
             ltac:(rewrite HF2; lia) ltac:(rewrite HF2; lia) ltac:(lia)).
  - exact VV2.
  - apply (cls_hull_vis W2 mem2 v 4); [lia | pose proof M05.alloc_ceiling_lt; lia | lia |].
    exact (CFr.shadow_hull_vis_of_frame tfibsegs B LAWS ly2 S2 W2 mem2 md2 cv pv v 4 HAR2 Inv2
             ltac:(rewrite HF2; lia) ltac:(rewrite HF2; lia) ltac:(lia)).
  - intros Hn. destruct (C9 Hn) as (Lf & InF & HLf).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ f Lf HAR InF) as (_ & Hf0 & Hf1 & _).
    assert (InF2 : In (f, Lf) (ablocks B ly2 S2)) by (rewrite Hbl2; exact InF).
    exact (PWH.heap_vis B LAWS ly2 S2 W2 mem2 md2 f Lf f 50 HAR2 InF2 ltac:(lia) ltac:(lia)).
  - intros Hn. destruct (C9 Hn) as (Lf & InF & HLf).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ f Lf HAR InF) as (_ & Hf0 & Hf1 & _).
    assert (InF2 : In (f, Lf) (ablocks B ly2 S2)) by (rewrite Hbl2; exact InF).
    apply (cls_hull_vis W2 mem2 f 50); [lia | pose proof M05.alloc_ceiling_lt; lia | lia |].
    exact (shadow_hull_vis_of_block tfibsegs B LAWS ly2 S2 W2 mem2 md2 f Lf f 50 HAR2 InF2
             ltac:(lia) ltac:(lia) ltac:(lia)).
  - intros Hn. destruct (C17 Hn) as ((cu & pu & Inu & Hcu & Hfu8 & Hfu1 & Hfu2) & Hu8 & RAu).
    assert (Inu2 : In (cu, pu) (frames S2)) by (rewrite Hfr2; exact Inu).
    exact (proj1 (PWF.frame_vis B LAWS ly2 S2 W2 mem2 md2 cu pu u 6 HAR2 Inu2 ltac:(rewrite HF2; lia)
                    ltac:(rewrite HF2; lia))).
  - intros Hn. destruct (C17 Hn) as ((cu & pu & Inu & Hcu & Hfu8 & Hfu1 & Hfu2) & Hu8 & RAu).
    destruct (frames_bounds tfibsegs B LAWS lyc Sc W memc mdc cu pu HAR Inu) as (Fu1 & Fu2 & Fu3).
    assert (Inu2 : In (cu, pu) (frames S2)) by (rewrite Hfr2; exact Inu).
    apply (cls_hull_vis W2 mem2 u 6); [lia | pose proof M05.alloc_ceiling_lt; lia | lia |].
    exact (CFr.shadow_hull_vis_of_frame tfibsegs B LAWS ly2 S2 W2 mem2 md2 cu pu u 6 HAR2 Inu2
             ltac:(rewrite HF2; lia) ltac:(rewrite HF2; lia) ltac:(lia)).
  - (* the saved registers at [S - 64, S) *)
    destruct RW1 as ((Wf1 & HB1) & _). split; [split; [exact Wf1|] | ].
    + apply (cls_bytes_transfer (w_H W) (w_H W2) m1 mem2 (Sp + -64)); [lia | rewrite LCe.cells_bytes_length by exact Wf1; cbn; lia | | | exact HB1].
      * intros i Hi. rewrite LCe.cells_bytes_length in Hi by exact Wf1. cbn in Hi.
        split; [exact (proj1 (Hpres (Sp + -64 + i) ltac:(lia))) | exact (proj1 (Hpres2 (Sp + -64 + i) ltac:(lia)))].
      * intros i Hi. rewrite LCe.cells_bytes_length in Hi by exact Wf1. cbn in Hi.
        apply KP1; [lia | unfold REAC_CTRL_PARSE_STK, ESTACK; lia].
    + apply (cls_wr_of_pres (w_H W2)); [lia | cbn; lia | intros x Hx; cbn in Hx; apply Hpres2; lia].
  - (* o's 36 bytes = parse's model *)
    apply (cls_bytes_of_view (w_H W2) mem2 o (snd (ctrlparse n fr)) cp_z);
      [lia | rewrite RcParse.ctrlparse_length; lia | |].
    + intros i Hi. rewrite RcParse.ctrlparse_length in Hi. destruct VO2 as (_ & _ & VO2'). apply VO2'. lia.
    + intros i Hi. rewrite RcParse.ctrlparse_length in Hi. apply Ho2; [lia | exact Hi].
  - apply (cls_wr_of_pres (w_H W2)); [lia | lia | intros x Hx; apply (proj1 (Po2 x ltac:(lia)))].
  - exact HVv.
  - apply (cls_stk_of_pres (w_H W2)); [lia | lia | intros a Ha; apply Hpres2; lia].
  - exact RO2.
  - exact RAC2.
  - (* route (C): stretch 2's region of record lies in cut_shadow B ly2 S2's (F) disjunct: the two strings of each
       bcmp call, o + 4 / o + 10 (6 bytes of o's 36) and u (6 bytes), are bytes of caller frames (C12 / C17) *)
    pose proof (lib.Reusable.YG0f.lo_F_al _ (lib.Reusable.YG0n.am_layout _ _ _ _ (proj1 HAR2))) as HLF.
    unfold lib.Reusable.YG0f.page_aligned in HLF.
    apply (SRO.shadow_rw_on_mono (ARC.cut_shadow B ly2 S2)); [| exact RCUT2].
    intros a Ha. unfold CFs.reac_ctrl_classify_box_frame_post_call_shadow_R, BWo.bcmp_wrap_shadow_R in Ha.
    destruct Ha as (HN & [[Ha | Ha] | [Ha | Ha]]);
      destruct (C17 HN) as ((cu & pu & Inu & Hcu & _ & Hfu1 & Hfu2) & _ & _);
      assert (Inu2 : In (cu, pu) (frames S2)) by (rewrite Hfr2; exact Inu);
      unfold ARC.cut_shadow; left.
    + exists co, po. split; [exact Ino2|].
      apply (cls_sh_word_frame ly2 co po (o + 4) 6 a HLF Hco); [rewrite HF2; lia | rewrite HF2; lia | lia | exact Ha].
    + exists cu, pu. split; [exact Inu2|].
      apply (cls_sh_word_frame ly2 cu pu u 6 a HLF Hcu); [rewrite HF2; lia | rewrite HF2; lia | lia | exact Ha].
    + exists co, po. split; [exact Ino2|].
      apply (cls_sh_word_frame ly2 co po (o + 10) 6 a HLF Hco); [rewrite HF2; lia | rewrite HF2; lia | lia | exact Ha].
    + exists cu, pu. split; [exact Inu2|].
      apply (cls_sh_word_frame ly2 cu pu u 6 a HLF Hcu); [rewrite HF2; lia | rewrite HF2; lia | lia | exact Ha].
  - apply (cls_win_addressable B LAWS ly2 S2 W2 mem2 md2); [exact HAR2 | rewrite (proj1 HSL2); lia
      | rewrite (proj2 HSL2); lia | lia | exact B3 | unfold ART.APPMEM_END; lia].
  - rewrite Forall_forall in RR2. exact (RR2 (0xa17f0, 0x97b0c)
      ltac:(unfold ART.RT_REALS; repeat first [left; reflexivity | right]) ltac:(unfold PW.REAL_USED; cbn; tauto)).
  - rewrite Forall_forall in RR2. exact (RR2 (0xa17e8, 0x97bdc)
      ltac:(unfold ART.RT_REALS; repeat first [left; reflexivity | right]) ltac:(unfold PW.REAL_USED; cbn; tauto)).
  - exact (proj1 RCF2).
  - destruct RCF2 as (_ & _ & _ & _ & _ & _ & CFb & _).
    pose proof (cls_bytes_one _ _ _ 14 (Z_to_bv 8 0) CFb ltac:(cbn; lia)) as X.
    replace (ART.RT_CF + 240 + Z.of_nat 14) with (BWc.CF + 254) in X by (unfold ART.RT_CF, BWc.CF; lia). exact X.
  - destruct RCF2 as (_ & _ & _ & _ & _ & _ & CFb & _).
    pose proof (cls_bytes_one _ _ _ 15 (Z_to_bv 8 0) CFb ltac:(cbn; lia)) as X.
    replace (ART.RT_CF + 240 + Z.of_nat 15) with (BWc.CF + 255) in X by (unfold ART.RT_CF, BWc.CF; lia). exact X.
  - (* G3: the post *)
    intros ms3 md3 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & E3 & MU3 &
                    WM3 & ST3 & RWo3 & RWv3 & AW3) Hh3 Hs3.
    subst ms3. apply SRr_ret.
    assert (AW2 : ART.addressable mem2 (Sp - 8864) 8864).
    { apply (cls_win_addressable B LAWS ly2 S2 W2 mem2 md2); [exact HAR2 | rewrite (proj1 HSL2); lia
        | rewrite (proj2 HSL2); lia | lia | exact B3 | unfold ART.APPMEM_END; lia]. }
    assert (Wo2 : forall a, o <= a < o + 36 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B ly2 S2) ly2 own a).
    { intros a Ha. rewrite Hbl2. destruct (C13 a Ha) as [Q|[Q|[Q|(cid & pos & Hown & Q)]]];
        [left; exact Q | right; left; exact Q | right; right; left; exact Q | right; right; right].
      exists cid, pos. split; [exact Hown|]. rewrite !HF2. exact Q. }
    assert (Wv2 : forall a, v <= a < v + 4 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B ly2 S2) ly2 own a).
    { intros a Ha. rewrite Hbl2. destruct (C15 a Ha) as [Q|[Q|[Q|(cid & pos & Hown & Q)]]];
        [left; exact Q | right; left; exact Q | right; right; left; exact Q | right; right; right].
      exists cid, pos. split; [exact Hown|]. rewrite !HF2. exact Q. }
    assert (J3 : ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 m3 md3 k).
    { apply (cls_journal_B B LAWS STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k m3 md3 Sp o v J2);
        first [lia | Z.div_mod_to_equations; lia | exact NIo | exact NIv | exact MU3 | exact WM3 | exact AW2
              | exact AW3 | exact Hh3 | exact Hs3 | exact Wo2 | exact Wv2]. }
    pose proof J3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _ & _ & _).
    exists ly2, S2,
      (LFr.mkR (reg_get regs 1) (Z_to_bv 64 Sp) (reg_get regs 3) (reg_get regs 4) t0' t1' t2' (reg_get regs 8)
         (reg_get regs 9) (Z_to_bv 64 (cl_r (classify n fr us))) a1' a2' a3' a4' a5' a6' a7' (reg_get regs 18)
         (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23)
         (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) t3' t4' t5' t6'), m3, md3.
    split.
    { (* Q1 *)
      rewrite (cls_ret_pc_ok (reg_get regs 1) C3a). reflexivity. }
    split.
    { (* Q2 *)
      unfold EV_CLS. rewrite Z.add_0_r. exact J3. }
    split.
    { (* Q3 *)
      intros r Hr. unfold acallee_saved in Hr.
      assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
        try reflexivity.
      change (K11.getr regs (Z_to_bv 5 2)) with (reg_get regs 2).
      change (K11.getr _ (Z_to_bv 5 2)) with (Z_to_bv 64 Sp).
      unfold Sp, spZ. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned. reflexivity. }
    split; [exact Hfr2|]. split; [exact Hbl2|].
    split; [reflexivity|].
    split.
    { (* Q5 *)
      intros i Hi. destruct RWo3 as ((_ & Bo3) & _). destruct Bo3 as (_ & _ & Bo3).
      destruct VO2 as (_ & _ & VO2').
      assert (Hi' : (i < length (LCe.cells_bytes [LCe.CB 36 (snd (ctrlparse n fr))]))%nat)
        by (cbn [LCe.cells_bytes LCe.cbytes]; rewrite app_nil_r, RcParse.ctrlparse_length; exact Hi).
      pose proof (Bo3 i Hi') as Bi. cbn [LCe.cells_bytes LCe.cbytes] in Bi. rewrite app_nil_r in Bi.
      rewrite (cls_aview_mrd (w_H W2) m3 (o + Z.of_nat i) ltac:(lia) (VO2' (o + Z.of_nat i) ltac:(lia))), Bi.
      rewrite (nth_error_nth' (snd (ctrlparse n fr)) cp_z ltac:(rewrite RcParse.ctrlparse_length; exact Hi)).
      reflexivity. }
    split.
    { (* Q6 *)
      intros e He. destruct RWv3 as ((_ & Bv3) & _). rewrite He in Bv3. cbn [LCe.cells_bytes LCe.cbytes] in Bv3.
      rewrite app_nil_r in Bv3. unfold PCc.reac_ctrl_classify_box_frame_ev in Bv3.
      destruct Bv3 as (_ & _ & Bv3). destruct VV2 as (_ & _ & VV2').
      pose proof (cls_classify_range n fr us e He) as Re.
      intros kk Hkk.
      assert (Hl : (kk < length (LMe.le4 (Z_to_bv 64 e)))%nat) by (rewrite LMe.length_le4; exact Hkk).
      pose proof (Bv3 kk Hl) as Bk.
      unfold lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict.
      rewrite (VV2' (v + Z.of_nat kk) ltac:(lia)).
      change (match m3 (Z_to_bv 64 (v + Z.of_nat kk)) with Some b => Some b
              | None => K11.seg_rom tfibsegs (Z_to_bv 64 (v + Z.of_nat kk)) end)
        with (LMe.mrd Img.rsegs m3 (LMe.wa (v + Z.of_nat kk))).
      rewrite Bk.
      assert (Ee : e = 0 \/ e = 1 \/ e = 2 \/ e = 3 \/ e = 4 \/ e = 5) by lia.
      destruct kk as [|[|[|[|kk]]]]; [| | | | lia];
        destruct Ee as [->|[->|[->|[->|[->| ->]]]]]; vm_compute; reflexivity. }
    { (* Q7 *)
      apply (cls_tcj B LAWS lyc Sc W W2 memc mdc m1 mem2 m3 Sp o v (classify n fr us <> None)); try lia.
      - exact HAR.
      - exact NIo.
      - exact NIv.
      - destruct (classify n fr us); [left; discriminate | right; intros Q; apply Q; reflexivity].
      - exact MU1.
      - exact KP.
      - exact MU3.
      - intros Hc i Hi. assert (Ec : classify n fr us = None) by (destruct (classify n fr us); [exfalso; apply Hc; discriminate | reflexivity]).
        destruct RWv3 as ((_ & Bv3) & _). rewrite Ec in Bv3. cbn [LCe.cells_bytes LCe.cbytes] in Bv3.
        rewrite app_nil_r in Bv3. unfold PCc.reac_ctrl_classify_box_frame_ev in Bv3.
        destruct HVv as ((_ & Bv2) & _). cbn [LCe.cells_bytes LCe.cbytes] in Bv2. rewrite app_nil_r in Bv2.
        destruct Bv3 as (_ & _ & Bv3). destruct Bv2 as (_ & _ & Bv2).
        assert (Hil : (Z.to_nat i < length vb)%nat) by lia.
        pose proof (Bv3 _ Hil) as X3. pose proof (Bv2 _ Hil) as X2. rewrite Z2Nat.id in X3, X2 by lia.
        rewrite <- X2 in X3. unfold LMe.mrd in X3.
        assert (Hrom : LPE.seg_rom Img.rsegs (LMe.wa (v + i)) = None).
        { apply cls_noimg_rom. rewrite cls_wa_unsigned by lia. exact (NIv i Hi). }
        rewrite Hrom in X3. destruct (m3 (LMe.wa (v + i))), (mem2 (LMe.wa (v + i))); congruence.
      - intros a Ha. apply Hpres3. lia. }
Qed.

End m.

Print Assumptions pb_reac_ctrl_classify_box_frame.
