(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* LLVMFuzzerTestOneInput_segX_crt1_fevt: the footprint-run-to-SRr toolkit of image B's LLVMFuzzerTestOneInput walk
   segments, in the form of the check_round_trip walk of the same unit (the porter's FORM ruling,
   2026-10-29 01:54Z, a working branch 02bbf1e30df lib/B/Prog/crtB_walk.v:6-9: the
   function's own code runs as decode's footprint runs (lib/Lib/ExecF.v), each carried into cgif's SRr; the journal
   is re-established across each run by lib/Reusable/YCbq.v:636 ajournal_exec; each call is cut by its callee
   contract).  Nothing here is new: it is taken by path from that branch, whose files are not on this branch:
     lib/Lib/CrtFevt.v      (prefix crt_fevt_ renamed c1f_: footprint run avoiding hidden bytes is an SRr prefix)
     lib/Lib/CrtBridge.v    (mstepF_eqv, mstepsF_eqv, evtF_eqv, getr_nonzero, mkst_eqv_mkR_of, prefixed c1f_)
     lib/B/Prog/crtB_bridge.v, crtB_fevt.v, crtB_walk.v, crtB_glue.v (prefix crtB_ renamed c1f_).
   Only the prefixes changed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK0i YK11 YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YP09 YI00 YI04.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Frame Cells Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require ExecF.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import ReacDecodeLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require LeafCgKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Module YKK := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.LeafCgKit.

(* ---- CrtFevt.v:22-27 ---- *)
Lemma c1f_ranges_avoid_hd : forall H a n l, ranges_avoid H ((a, n) :: l) -> range_avoids H a n.
Proof. intros H a n l Hr. apply Hr. left. reflexivity. Qed.

Lemma c1f_ranges_avoid_tl : forall H x l, ranges_avoid H (x :: l) -> ranges_avoid H l.
Proof. intros H x l Hr a n Hin. apply Hr. right. exact Hin. Qed.

Section d.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

(* CrtFevt.v:35-62 (YK04R.v:25-52). *)
Lemma c1f_interp_eff_accesses_restrict_conv : forall t m c mf' rs,
  interp_eff_accesses segs t m = MachineOk (@mkAccessReport _ (c, mf') rs) ->
  ranges_avoid H rs ->
  interp_eff_accesses segs t (mrestrict H m) = MachineOk (@mkAccessReport _ (c, mrestrict H mf') rs).
Proof.
  induction t as [c0 | c0 | c0 | c0 | c0 | c0 | n a k IH | n a v k IH];
    intros m c mf' rs Hi Hrs; cbn [interp_eff_accesses] in Hi |- *; try discriminate.
  - injection Hi as <- <- <-. reflexivity.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|] eqn:Hrd; [|discriminate].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m)
      as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
    cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-.
    pose proof (c1f_ranges_avoid_hd H a (width_bytes n) rs1 Hrs) as Hav.
    rewrite (ov_read_bytes_mrestrict_eq segs H (width_bytes n) m a Hav), Hrd.
    rewrite (IH _ m c1 m1 rs1 Hk (c1f_ranges_avoid_tl H _ rs1 Hrs)). reflexivity.
  - destruct (store_ok segs m a (width_bytes n)) eqn:Hso; [|discriminate].
    destruct (interp_eff_accesses segs k (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v))))
      as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
    cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-.
    pose proof (c1f_ranges_avoid_hd H a (width_bytes n) rs1 Hrs) as Hav.
    rewrite (store_ok_mrestrict_eq segs H (width_bytes n) m a Hav), Hso.
    assert (Hlen : length (Z_to_le_bytes (width_bytes n) (bv_unsigned v)) = width_bytes n)
      by apply length_Z_to_le_bytes.
    rewrite (write_to_mem_restrict H (Z_to_le_bytes (width_bytes n) (bv_unsigned v)) m a)
      by (rewrite Hlen; exact Hav).
    rewrite (IH _ c1 m1 rs1 Hk (c1f_ranges_avoid_tl H _ rs1 Hrs)). reflexivity.
Qed.

(* CrtFevt.v:64-84. *)
Lemma c1f_decode_exec_accesses_restrict_conv : forall ms w ms' rs,
  decode_exec_accesses segs ms w = MachineOk (@mkAccessReport _ ms' rs) ->
  ranges_avoid H rs ->
  decode_exec_accesses segs (restrict H ms) w = MachineOk (@mkAccessReport _ (restrict H ms') rs).
Proof.
  intros ms w ms' rs Hd Hrs. unfold decode_exec_accesses in Hd |- *.
  destruct (is_ecall w) eqn:Hec.
  - injection Hd as <- <-. reflexivity.
  - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
    destruct (interp_eff_accesses segs
      (exec (Z_to_bv 64 isz) i
        {| c_regs := ms_regs ms; c_fregs := ms_fregs ms;
           c_pc := ms_pc_val ms; c_fcsr := ms_fcsr ms;
           c_resv := ms_resv ms |})
      (ms_mem ms)) as [[[c1 m1] rs1]| |] eqn:Hint; try discriminate.
    cbn [access_value accessed_ranges] in Hd. injection Hd as <- <-.
    cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom restrict].
    rewrite (c1f_interp_eff_accesses_restrict_conv _ _ c1 m1 rs1 Hint Hrs).
    reflexivity.
Qed.

(* CrtFevt.v:86-107. *)
Theorem c1f_step_accesses_restrict_conv : forall ms ms' rs,
  step_accesses segs ms = MachineOk (@mkAccessReport _ ms' rs) ->
  ranges_avoid H rs ->
  step_accesses segs (restrict H ms) = MachineOk (@mkAccessReport _ (restrict H ms') rs).
Proof.
  intros ms ms' rs Hs Hrs. unfold step_accesses in Hs |- *.
  rewrite restrict_pc. cbn [ms_mem restrict].
  rewrite fetch_word_ov_restrict, fetch_tail_any_restrict, fetch_failure_restrict by assumption.
  destruct (fetch_word segs (ms_pc ms)) as [w|].
  { exact (c1f_decode_exec_accesses_restrict_conv ms w ms' rs Hs Hrs). }
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|].
  { exact (c1f_decode_exec_accesses_restrict_conv ms w ms' rs Hs Hrs). }
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|].
  { exact (c1f_decode_exec_accesses_restrict_conv ms w ms' rs Hs Hrs). }
  exfalso. unfold fetch_failure in Hs.
  destruct (negb (bv_unsigned (ms_pc ms) mod 2 =? 0)%Z); [discriminate|].
  destruct (fetch_byte_traps segs (ms_pc ms) || fetch_byte_traps segs (ms_pc ms + 1)
    || match fetch_half_any segs (ms_mem ms) (ms_pc ms) with
       | Some _ => fetch_byte_traps segs (ms_pc ms + 2) || fetch_byte_traps segs (ms_pc ms + 3)
       | None => false end); discriminate.
Qed.

(* CrtFevt.v:109-119. *)
Corollary c1f_step_accesses_avoid_keeps_hidden : forall ms ms' rs,
  step_accesses segs ms = MachineOk (@mkAccessReport _ ms' rs) ->
  ranges_avoid H rs ->
  ms' = unrestrict H (ms_mem ms) (restrict H ms').
Proof.
  intros ms ms' rs Hs Hrs.
  pose proof (c1f_step_accesses_restrict_conv ms ms' rs Hs Hrs) as Hr.
  destruct (step_accesses_restrict segs H HH Hwx ms (restrict H ms') rs Hr) as (Hfull & _ & _).
  rewrite Hs in Hfull. injection Hfull as E. exact E.
Qed.
End d.

(* CrtFevt.v:124-125. *)
Definition c1f_fp_avoids (H : word -> bool) (RNG : ExecF.footprint) : Prop :=
  forall (a : word) (n : nat), RNG (bv_unsigned a) n -> range_avoids H a n.

Section f.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

(* CrtFevt.v:133-139. *)
Lemma c1f_ranges_avoid_of_fp : forall RNG accs,
  c1f_fp_avoids H RNG -> Forall (ExecF.acc_in RNG) accs -> ranges_avoid H accs.
Proof.
  intros RNG accs Hfp HF a n Hin.
  apply Hfp. exact (proj1 (Forall_forall _ accs) HF (a, n) Hin).
Qed.

(* CrtFevt.v:141-147. *)
Lemma c1f_munrestrict_agree : forall (full full' m : word -> option byte),
  (forall x, H x = true -> full' x = full x) -> munrestrict H full' m = munrestrict H full m.
Proof.
  intros full full' m Hag. apply functional_extensionality. intro x. unfold munrestrict.
  destruct (H x) eqn:Hx; [exact (Hag x Hx) | reflexivity].
Qed.

(* CrtFevt.v:149-167. *)
Theorem c1f_mstepsF_restrict : forall RNG ms ms',
  ExecF.mstepsF segs RNG ms ms' -> c1f_fp_avoids H RNG ->
  msteps segs (restrict H ms) (restrict H ms')
  /\ ms' = unrestrict H (ms_mem ms) (restrict H ms').
Proof.
  intros RNG ms ms' Hrun Hfp. induction Hrun as [ms | ms ms1 ms2 [Hsvc (accs & Hs & HF)] _ IH].
  - split; [apply mst_refl | symmetry; apply unrestrict_restrict].
  - pose proof (c1f_ranges_avoid_of_fp RNG accs Hfp HF) as Hrs.
    destruct IH as [Hrest Heq2].
    pose proof (c1f_step_accesses_avoid_keeps_hidden segs H HH Hwx ms ms1 accs Hs Hrs) as Heq1.
    split.
    + eapply mst_step; [exact Hsvc | | exact Hrest].
      unfold RiscvSemantics.step, drop_access_report.
      rewrite (c1f_step_accesses_restrict_conv segs H HH Hwx ms ms1 accs Hs Hrs). reflexivity.
    + rewrite Heq2 at 1. unfold unrestrict. f_equal.
      apply c1f_munrestrict_agree. intros x Hx.
      rewrite Heq1. cbn [ms_mem unrestrict]. unfold munrestrict. rewrite Hx. reflexivity.
Qed.
End f.

Section g. Context {fx : YK11.FPState}.
(* CrtFevt.v:173-184. *)
Theorem c1f_SRr_mstepsF : forall (segs : list Segment), wx_segs_nowrap segs ->
  forall (W : world segs) ms ms' model RNG (Q : world segs -> config -> Prop),
  ExecF.mstepsF segs RNG ms ms' ->
  c1f_fp_avoids (w_H W) RNG ->
  (forall model', same_but_materialized model model' -> SRr segs W (mkCfg ms' model') Q) ->
  SRr segs W (mkCfg ms model) Q.
Proof.
  intros segs Hwx W ms ms' model RNG Q Hrun Hfp Hk.
  destruct (c1f_mstepsF_restrict segs (w_H W) (w_Hoff W) Hwx RNG ms ms' Hrun Hfp) as [Hms Heq].
  apply (SRr_msteps segs Hwx W ms (restrict (w_H W) ms') model Q Hms).
  intros model' Hsame _. rewrite <- Heq. exact (Hk model' Hsame).
Qed.
End g.

(* ---- CrtBridge.v:19-60 ---- *)
Section Transport.
Variable segs : list Segment.
Variable RNG : ExecF.footprint.

Lemma c1f_mstepF_eqv : forall ms1 ms2 ms1',
  ms_eqv ms1 ms2 -> ExecF.mstepF segs RNG ms1 ms1' ->
  exists ms2', ExecF.mstepF segs RNG ms2 ms2' /\ ms_eqv ms1' ms2'.
Proof.
  intros ms1 ms2 ms1' Heqv [Hsvc (accs & Hstep & Hacc)].
  pose proof (step_accesses_eqv segs ms1 ms2 Heqv) as Hr.
  rewrite Hstep in Hr. unfold rep_eqv in Hr.
  destruct (RiscvSemantics.step_accesses segs ms2) as [rep2| |] eqn:Hstep2; [|destruct Hr|destruct Hr].
  destruct rep2 as [ms2' accs2]. cbn [access_value accessed_ranges] in Hr.
  destruct Hr as [Hms Haccs].
  exists ms2'. split; [|exact Hms].
  split.
  - pose proof Heqv as (_ & _ & _ & Hsv & _). rewrite <- Hsv. exact Hsvc.
  - exists accs2. split; [exact Hstep2|]. rewrite <- Haccs. exact Hacc.
Qed.

Lemma c1f_mstepsF_eqv : forall ms1 ms1',
  ExecF.mstepsF segs RNG ms1 ms1' ->
  forall ms2, ms_eqv ms1 ms2 -> exists ms2', ExecF.mstepsF segs RNG ms2 ms2' /\ ms_eqv ms1' ms2'.
Proof.
  intros ms1 ms1' H. induction H as [ms | ms msa msb Hstep Hrest IH]; intros ms2 Heqv.
  - exists ms2. split; [apply ExecF.mstepsF_refl | exact Heqv].
  - destruct (c1f_mstepF_eqv ms ms2 msa Heqv Hstep) as (ms2a & Hstep2 & Heqva).
    destruct (IH ms2a Heqva) as (ms2' & Hrest2 & Heqv').
    exists ms2'. split; [eapply ExecF.mstepsF_cons; eassumption | exact Heqv'].
Qed.

Lemma c1f_evtF_eqv : forall (P : machine_state -> Prop) ms1 ms2,
  ms_eqv ms1 ms2 -> ExecF.evtF segs RNG P ms1 ->
  ExecF.evtF segs RNG (fun ms => exists ms0, P ms0 /\ ms_eqv ms0 ms) ms2.
Proof.
  intros P ms1 ms2 Heqv (ms1' & Hrun & HP).
  destruct (c1f_mstepsF_eqv ms1 ms1' Hrun ms2 Heqv) as (ms2' & Hrun2 & Heqv').
  exists ms2'. split; [exact Hrun2|]. exists ms1'. split; [exact HP | exact Heqv'].
Qed.
End Transport.

Section Shape.
Context {fx : YK11.FPState}.

(* CrtBridge.v:65-69. *)
Lemma c1f_getr_nonzero : forall (regs : bvmap 5 word) (r : bv 5), is_x0 r = false -> YK11.getr regs r = reg_get regs r.
Proof.
  intros regs r Hr. unfold YK11.getr, is_x0 in *. destruct (bv_eqb r 0) eqn:E; [|reflexivity].
  exfalso. apply bv_eqb_eq in E. subst r. cbn in Hr. discriminate Hr.
Qed.

(* CrtBridge.v:71-79. *)
Lemma c1f_mkst_eqv_mkR_of : forall (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte),
  ms_eqv (@YK11.mkst fx regs pc mem rom)
         (MS (mkR_of regs) (@fp_regs fx) pc (@fp_csr fx) None mem rom).
Proof.
  intros regs pc mem rom. unfold ms_eqv, YK11.mkst.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom].
  repeat split; try reflexivity. apply mkR_of_eqv.
Qed.

(* crtB_bridge.v:22-28. *)
Lemma c1f_ms_of_regs_regs : forall pc (regs : bvmap 5 word) (mem : word -> option byte),
  ms_regs (@LCK.ms_of_regs fx pc regs mem) = mkR_of regs.
Proof.
  intros pc regs mem. unfold LCK.ms_of_regs, mkR_of, YK11.getr. cbn.
  first [reflexivity | f_equal].
Qed.

(* crtB_bridge.v:30-39. *)
Lemma c1f_mkst_eqv_ms_of_regs : forall pc (regs : bvmap 5 word) (mem : word -> option byte),
  ms_eqv (@YK11.mkst fx regs (LCK.w64 pc) mem (YK11.seg_rom rsegs)) (@LCK.ms_of_regs fx pc regs mem).
Proof.
  intros pc regs mem.
  pose proof (@c1f_mkst_eqv_mkR_of regs (LCK.w64 pc) mem (YK11.seg_rom rsegs)) as H.
  unfold ms_eqv in H |- *. rewrite (c1f_ms_of_regs_regs pc regs mem).
  unfold LCK.ms_of_regs. cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in H |- *.
  exact H.
Qed.
End Shape.

(* crtB_fevt.v:20-29: decodesegsB0 has no writable-and-executable segment that wraps (YK04.v:40). *)
Lemma c1f_wx : wx_segs_nowrap decodesegsB0.
Proof.
  intros seg Hin Hx.
  assert (Hall : forallb (fun s => negb (seg_executable s && seg_writable s) ||
                         (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 2 ^ 64)%Z) decodesegsB0 = true)
    by (clear; vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) Hall seg Hin) as Hs. cbv beta in Hs.
  rewrite Hx in Hs. cbn [negb orb] in Hs. apply Z.leb_le in Hs. exact Hs.
Qed.

Section Walk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := decodesegsB0.

(* crtB_fevt.v:43-49: LeafCgKit.v:101 at the concrete world / w_H / SRr of decodesegsB0. *)
Theorem c1f_bridge_holds :
  LCK.bridge_evtF_stmt (world segs) (@w_H segs) (SRr segs) same_but_materialized.
Proof.
  unfold LCK.bridge_evtF_stmt.
  intros W ms model RNG P Q (ms' & Hrun & HP) Hfp Hk.
  exact (c1f_SRr_mstepsF segs c1f_wx W ms ms' model RNG Q Hrun Hfp (fun model' Hs => Hk ms' model' HP Hs)).
Qed.

(* crtB_walk.v:43-47: the footprint the walk gives every run, all visible bytes. *)
Lemma c1f_fp_avoids_W : forall (W : world segs), LCK.fp_avoids (@w_H segs W) (LCK.RNG_W (world segs) (@w_H segs) W).
Proof.
  intros W a n H. unfold LCK.RNG_W in H. rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.

(* crtB_walk.v:49-67: a footprint run from cgif's configuration at pc. *)
Lemma c1f_run : forall (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (pc : Z)
    (P : machine_state -> Prop) (Q : world segs -> config -> Prop),
  ExecF.evtF rsegs (LCK.RNG_W (world segs) (@w_H segs) W) P (@LCK.ms_of_regs fx pc regs mem) ->
  (forall ms' md', (exists ms0, P ms0 /\ ms_eqv ms0 ms') -> same_but_materialized md md' ->
     SRr segs W (mkCfg ms' md') Q) ->
  SRr segs W (mkCfg (@YK11.mkst fx regs (LCK.w64 pc) mem (YK11.seg_rom segs)) md) Q.
Proof.
  intros W regs mem md pc P Q Hrun K.
  apply (c1f_bridge_holds W (@YKK.mkst fx regs (LCK.w64 pc) mem (YKK.seg_rom segs)) md
           (LCK.RNG_W (world segs) (@w_H segs) W) (fun ms => exists ms0, P ms0 /\ ms_eqv ms0 ms) Q).
  - apply (c1f_evtF_eqv rsegs _ P (@LCK.ms_of_regs fx pc regs mem)).
    + apply ms_eqv_sym. exact (@c1f_mkst_eqv_ms_of_regs fx pc regs mem).
    + exact Hrun.
  - apply c1f_fp_avoids_W.
  - exact K.
Qed.

(* crtB_walk.v:69-77. *)
Lemma c1f_ms_shape : forall (R : bvmap 5 word) (pc : word) (m : word -> option byte) (ms' : machine_state),
  ms_eqv (MS R (@fp_regs fx) pc (@fp_csr fx) None m (YKK.seg_rom segs)) ms' ->
  ms' = @YKK.mkst fx (ms_regs ms') pc m (YKK.seg_rom segs).
Proof.
  intros R pc m [r f p sv rv fc mm ro] (_ & Hf & Hp & Hs & Hr & Hc & Hm & Hro).
  cbn [MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
  subst. reflexivity.
Qed.

(* crtB_walk.v:79-86. *)
Lemma c1f_ms_reg : forall (R : bvmap 5 word) F pc fc rv m ro (ms' : machine_state) (r : bv 5),
  ms_eqv (MS R F pc fc rv m ro) ms' -> is_x0 r = false ->
  YKK.getr (ms_regs ms') r = YKK.getr R r.
Proof.
  intros R F pc fc rv m ro ms' r (HR & _) Hr. cbn [MS ms_regs] in HR.
  rewrite !c1f_getr_nonzero by exact Hr. symmetry. apply HR. exact Hr.
Qed.
End Walk.

(* ---- crtB_glue.v: the world-level memory facts carried to decode's footprint facts, and back ---- *)
(* crtB_glue.v:30-34. *)
Lemma c1f_mrd_of_apresent : forall H mem a, apresent H mem a -> exists b, mrd rsegs mem (wa a) = Some b.
Proof.
  intros H mem a [Hh [b Hb]]. exists b. unfold mrd, wa. rewrite Hb. reflexivity.
Qed.

(* crtB_glue.v:36-40. *)
Lemma c1f_wview_some : forall mem (x : word) b, mem x = Some b -> wview rsegs mem x <> None.
Proof. intros mem x b Hm. unfold wview. rewrite Hm. discriminate. Qed.

Lemma c1f_wview_of_apresent : forall H mem a, apresent H mem a -> wview rsegs mem (wa a) <> None.
Proof. intros H mem a [Hh [b Hb]]. exact (c1f_wview_some mem (wa a) b Hb). Qed.

(* crtB_glue.v:42-49. *)
Lemma c1f_stk_of : forall H mem lo hi,
  0 <= lo -> hi <= 2 ^ 64 -> (forall a, lo <= a < hi -> apresent H mem a) -> stk rsegs mem lo hi.
Proof.
  intros H mem lo hi Hlo Hhi Hp. split; [exact Hlo|]. split; [exact Hhi|].
  intros a Ha. pose proof (Hp a Ha) as Hpa.
  split; [exact (c1f_wview_of_apresent H mem a Hpa) | exact (c1f_mrd_of_apresent H mem a Hpa)].
Qed.

(* crtB_glue.v:51-57. *)
Lemma c1f_wr_at_of : forall H mem lo n,
  0 <= lo -> lo + n <= 2 ^ 64 -> (forall a, lo <= a < lo + n -> apresent H mem a) -> wr_at rsegs mem lo n.
Proof.
  intros H mem lo n Hlo Hhi Hp. split; [exact Hlo|]. split; [exact Hhi|].
  intros i Hi. exact (c1f_wview_of_apresent H mem (lo + i) (Hp (lo + i) ltac:(lia))).
Qed.

(* crtB_glue.v:59-81. *)
Lemma c1f_rng_of_vis : forall (W : world decodesegsB0) lo len,
  0 <= lo -> lo + len <= 2 ^ 64 ->
  (forall a, lo <= a < lo + len -> w_H W (wa a) = false) ->
  ExecF.rng (LCK.RNG_W (world decodesegsB0) (@w_H decodesegsB0) W) lo len.
Proof.
  intros W lo len Hlo Hhi Hv. split; [exact Hlo|]. split; [exact Hhi|].
  intros b j Hb Hj. unfold LCK.RNG_W, LCK.range_avoids, LCK.woff.
  intros k Hk.
  assert (Hbr : 0 <= b < 2 ^ 64) by lia.
  rewrite (unsigned_lit b Hbr).
  change (Z_to_bv 64 (b + Z.of_nat k)) with (wa (b + Z.of_nat k)).
  apply Hv. lia.
Qed.

Lemma c1f_rng_of_apresent : forall (W : world decodesegsB0) mem lo len,
  0 <= lo -> lo + len <= 2 ^ 64 ->
  (forall a, lo <= a < lo + len -> apresent (w_H W) mem a) ->
  ExecF.rng (LCK.RNG_W (world decodesegsB0) (@w_H decodesegsB0) W) lo len.
Proof.
  intros W mem lo len Hlo Hhi Hp. apply c1f_rng_of_vis; [exact Hlo | exact Hhi|].
  intros a Ha. exact (proj1 (Hp a Ha)).
Qed.

(* crtB_glue.v:83-107. *)
Lemma c1f_aview_mrd : forall (H : word -> bool) mem a,
  H (wa a) = false ->
  aview decodesegsB0 H mem a = option_map (fun b : byte => bv_unsigned b) (mrd rsegs mem (wa a)).
Proof.
  intros H mem a Hh. unfold wa in Hh.
  unfold aview, mbyte, mrestrict, mrd, wa. rewrite Hh. reflexivity.
Qed.

Lemma c1f_opt_byte_eq : forall (x y : option byte),
  option_map (fun b : byte => bv_unsigned b) x = option_map (fun b : byte => bv_unsigned b) y -> x = y.
Proof.
  intros [x|] [y|] E; cbn in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma c1f_mrd_eq_of_aview : forall (H H' : word -> bool) mem mem' a,
  H (wa a) = false -> H' (wa a) = false ->
  aview decodesegsB0 H' mem' a = aview decodesegsB0 H mem a ->
  mrd rsegs mem' (wa a) = mrd rsegs mem (wa a).
Proof.
  intros H H' mem mem' a Hh Hh' E. apply c1f_opt_byte_eq.
  rewrite <- (c1f_aview_mrd H' mem' a Hh'), <- (c1f_aview_mrd H mem a Hh). exact E.
Qed.

(* crtB_glue.v:109-121. *)
Lemma c1f_bytes_at_kept : forall (H H' : word -> bool) mem mem' A bs,
  bytes_at rsegs mem A bs ->
  (forall a, A <= a < A + Z.of_nat (length bs) -> H (wa a) = false /\ H' (wa a) = false /\
     aview decodesegsB0 H' mem' a = aview decodesegsB0 H mem a) ->
  bytes_at rsegs mem' A bs.
Proof.
  intros H H' mem mem' A bs (HA & Hlen & Hb) Hk.
  split; [exact HA|]. split; [exact Hlen|].
  intros i Hi.
  destruct (Hk (A + Z.of_nat i) ltac:(lia)) as (Hh & Hh' & Ha).
  rewrite (c1f_mrd_eq_of_aview H H' mem mem' (A + Z.of_nat i) Hh Hh' Ha). exact (Hb i Hi).
Qed.

(* ---- the byte-level glue between cgif's reader and decode's footprint reads ---- *)
(* crtB_cells.v:26-33 crt_nth_le_bytes. *)
Lemma c1f_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  destruct k as [|k]; cbn [Z_to_le_bytes nth_error].
  - rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
  - rewrite (IH (Z.shiftr z 8) k ltac:(lia)). do 2 f_equal.
    rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

(* At a visible byte, cgif's byte view is decode's. *)
Lemma c1f_mbyte_mrd : forall (H : word -> bool) mem a,
  H (wa a) = false -> mbyte decodesegsB0 (mrestrict H mem) a = mrd rsegs mem (wa a).
Proof. intros H mem a Hh. unfold mbyte, mrestrict, mrd, wa in *. rewrite Hh. reflexivity. Qed.

Lemma c1f_mbyte_eq_of_aview : forall (H : word -> bool) m m' a,
  aview decodesegsB0 H m' a = aview decodesegsB0 H m a ->
  mbyte decodesegsB0 (mrestrict H m') a = mbyte decodesegsB0 (mrestrict H m) a.
Proof. intros H m m' a E. apply c1f_opt_byte_eq. exact E. Qed.

Lemma c1f_zbv8_mod : forall x, Z_to_bv 8 (x mod 256) = Z_to_bv 8 x.
Proof.
  intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* An 8-byte cell of cgif's reader is the 8-byte load of decode's runs. *)
Lemma c1f_rd8 : forall (W : world decodesegsB0) mem a v,
  0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> w_H W (wa (a + i)) = false) ->
  val_mem decodesegsB0 (mrestrict (w_H W) mem) a 8 v ->
  ov_read_bytes rsegs mem (Z_to_bv 64 a) 8 = Some (le8 (Z_to_bv 64 v)).
Proof.
  intros W mem a v Ha Ha8 Hvis HV.
  pose proof (rd_all mem a (le8 (Z_to_bv 64 v))) as R. rewrite length_le8 in R. apply R.
  split; [exact Ha|]. split; [rewrite length_le8; lia|].
  intros k Hk. rewrite length_le8 in Hk.
  specialize (HV k ltac:(lia)).
  rewrite (c1f_mbyte_mrd (w_H W) mem (a + Z.of_nat k)) in HV by (apply Hvis; lia).
  rewrite HV. unfold le8, word_to_le_bytes.
  rewrite (c1f_nth_le_bytes 8 (bv_unsigned (Z_to_bv 64 v)) k Hk). f_equal.
  unfold YO0f.le_byte. rewrite c1f_zbv8_mod, unsigned_lit_wrap.
  change (8 * Z.of_nat 8) with 64. reflexivity.
Qed.

(* A cell and an array of cgif's reader are kept by a state that keeps the reader on their bytes. *)
Lemma c1f_val_mem_kept : forall (W : world decodesegsB0) m m' a (n : nat) v,
  (forall i, 0 <= i < Z.of_nat n ->
     aview decodesegsB0 (w_H W) m' (a + i) = aview decodesegsB0 (w_H W) m (a + i)) ->
  val_mem decodesegsB0 (mrestrict (w_H W) m) a n v ->
  val_mem decodesegsB0 (mrestrict (w_H W) m') a n v.
Proof.
  intros W m m' a n v Hk HV j Hj.
  rewrite (c1f_mbyte_eq_of_aview (w_H W) m m' (a + Z.of_nat j)) by (apply Hk; lia).
  apply HV. exact Hj.
Qed.

Lemma c1f_garr8_kept : forall (W : world decodesegsB0) m m' base l,
  (forall i, 0 <= i < Z.of_nat (length l) ->
     aview decodesegsB0 (w_H W) m' (base + i) = aview decodesegsB0 (w_H W) m (base + i)) ->
  garr8 decodesegsB0 (mrestrict (w_H W) m) base l ->
  garr8 decodesegsB0 (mrestrict (w_H W) m') base l.
Proof.
  intros W m m' base l Hk HG j Hj. destruct (HG j Hj) as [HV HR]. split; [|exact HR].
  eapply c1f_val_mem_kept; [| exact HV].
  intros i Hi. rewrite <- Z.add_assoc. apply Hk. lia.
Qed.

(* crtB_glue.v:19-28: every loaded segment of image B lies below kLowMemEnd. *)
Lemma c1f_segs_low : forall a, in_img decodesegsB0 a -> 0 <= a < kLowMemEnd.
Proof.
  intros a (sg & Hin & Hr).
  assert (Hall : forallb (fun s => (0 <=? Z.of_N (seg_base s)) &&
                   (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? kLowMemEnd))%bool decodesegsB0 = true)
    by (clear; vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) Hall sg Hin) as Hs. cbv beta in Hs.
  apply andb_true_iff in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(* A byte cgif's reader answers is a byte the world does not hide: a hidden byte has no image byte either
   (YK04.v memory_read1_hidden), so its view is None. *)
Lemma c1f_vis_of_aview : forall (W : world decodesegsB0) mem a,
  aview decodesegsB0 (w_H W) mem a <> None -> w_H W (wa a) = false.
Proof.
  intros W mem a HN. destruct (w_H W (wa a)) eqn:E; [exfalso; apply HN | reflexivity].
  unfold aview, mbyte, mrestrict, wa in *. rewrite E.
  try unfold YK11.seg_rom; try unfold PropExec.seg_rom; try unfold seg_rom;
  rewrite (memory_read1_hidden decodesegsB0 (w_H W) (w_Hoff W) (Z_to_bv 64 a) E); reflexivity.
Qed.

(* ... so a window of bytes the reader answers is a window of the walk's footprint. *)
Lemma c1f_rng_of_vis_aview : forall (W : world decodesegsB0) mem lo len,
  0 <= lo -> lo + len <= 2 ^ 64 ->
  (forall a, lo <= a < lo + len -> aview decodesegsB0 (w_H W) mem a <> None) ->
  ExecF.rng (LCK.RNG_W (world decodesegsB0) (@w_H decodesegsB0) W) lo len.
Proof.
  intros W mem lo len Hlo Hhi Hv. apply (c1f_rng_of_vis W lo len Hlo Hhi).
  intros a Ha. exact (c1f_vis_of_aview W mem a (Hv a Ha)).
Qed.
