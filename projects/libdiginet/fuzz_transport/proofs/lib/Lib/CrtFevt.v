(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/B/Prog/LLVMFuzzerTestOneInput_segX_crt1_fevt.v, with its module paths changed; 40 of its 160 lines of code are new or changed and 318 lines of the source are left out. *)
(* CrtFevt: a footprint run (lib/Lib/ExecF.v evtF / mstepsF) whose footprint avoids the world's hidden bytes is a
   silent prefix of cgif's world walk SRr (lib/Reusable/YA0n.v:35), for ANY segment list.  This is the
   image-neutral half of image B's origin/cold/port-libreac-fuzz_decode-crtB 82cbfac97a3
   proofs/libreac/fuzz_decode/lib/B/Prog/crtB_fevt.v (its Sections d and f, the two list helpers, and its Section g
   stated over the segment list), with B's `crtB_` prefix renamed `crt_fevt_`.  Image B's lane may Require this file
   in place of its own copies; each image then gives only its wx_segs_nowrap fact (A: lib/A/Prog/crtA_fevt.v).
   crtB_fevt.v is a port of the target-independent kit origin/cold/h-rw-man-14-kit eea54967566
   proofs/libreac/fuzz_grant/lib/Reusable/YK04R.v (the converse of YK04.step_accesses_restrict, and fsteps_restrict)
   and YA0nR.v (SRr_fsteps, SRr_fevt), with the kit's `fstep` / `fsteps` read as ExecF.mstepF / mstepsF, which have
   the same bodies (ExecF.v:98-105). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK0i YK11 YK04 YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require ExecF.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.

(* YK04R.v:13-17. *)
Lemma crt_fevt_ranges_avoid_hd : forall H a n l, ranges_avoid H ((a, n) :: l) -> range_avoids H a n.
Proof. intros H a n l Hr. apply Hr. left. reflexivity. Qed.

Lemma crt_fevt_ranges_avoid_tl : forall H x l, ranges_avoid H (x :: l) -> ranges_avoid H l.
Proof. intros H x l Hr a n Hin. apply Hr. right. exact Hin. Qed.

Section d.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

(* YK04R.v:25-52. *)
Lemma crt_fevt_interp_eff_accesses_restrict_conv : forall t m c mf' rs,
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
    pose proof (crt_fevt_ranges_avoid_hd H a (width_bytes n) rs1 Hrs) as Hav.
    rewrite (ov_read_bytes_mrestrict_eq segs H (width_bytes n) m a Hav), Hrd.
    rewrite (IH _ m c1 m1 rs1 Hk (crt_fevt_ranges_avoid_tl H _ rs1 Hrs)). reflexivity.
  - destruct (store_ok segs m a (width_bytes n)) eqn:Hso; [|discriminate].
    destruct (interp_eff_accesses segs k (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v))))
      as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
    cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-.
    pose proof (crt_fevt_ranges_avoid_hd H a (width_bytes n) rs1 Hrs) as Hav.
    rewrite (store_ok_mrestrict_eq segs H (width_bytes n) m a Hav), Hso.
    assert (Hlen : length (Z_to_le_bytes (width_bytes n) (bv_unsigned v)) = width_bytes n)
      by apply length_Z_to_le_bytes.
    rewrite (write_to_mem_restrict H (Z_to_le_bytes (width_bytes n) (bv_unsigned v)) m a)
      by (rewrite Hlen; exact Hav).
    rewrite (IH _ c1 m1 rs1 Hk (crt_fevt_ranges_avoid_tl H _ rs1 Hrs)). reflexivity.
Qed.

(* YK04R.v:54-75. *)
Lemma crt_fevt_decode_exec_accesses_restrict_conv : forall ms w ms' rs,
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
    rewrite (crt_fevt_interp_eff_accesses_restrict_conv _ _ c1 m1 rs1 Hint Hrs).
    reflexivity.
Qed.

(* YK04R.v:77-97: a full step whose access ranges avoid H is a step of the restricted state, with the same report. *)
Theorem crt_fevt_step_accesses_restrict_conv : forall ms ms' rs,
  step_accesses segs ms = MachineOk (@mkAccessReport _ ms' rs) ->
  ranges_avoid H rs ->
  step_accesses segs (restrict H ms) = MachineOk (@mkAccessReport _ (restrict H ms') rs).
Proof.
  intros ms ms' rs Hs Hrs. unfold step_accesses in Hs |- *.
  rewrite restrict_pc. cbn [ms_mem restrict].
  rewrite fetch_word_ov_restrict, fetch_tail_any_restrict, fetch_failure_restrict by assumption.
  destruct (fetch_word segs (ms_pc ms)) as [w|].
  { exact (crt_fevt_decode_exec_accesses_restrict_conv ms w ms' rs Hs Hrs). }
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|].
  { exact (crt_fevt_decode_exec_accesses_restrict_conv ms w ms' rs Hs Hrs). }
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|].
  { exact (crt_fevt_decode_exec_accesses_restrict_conv ms w ms' rs Hs Hrs). }
  exfalso. unfold fetch_failure in Hs.
  destruct (negb (bv_unsigned (ms_pc ms) mod 2 =? 0)%Z); [discriminate|].
  destruct (fetch_byte_traps segs (ms_pc ms) || fetch_byte_traps segs (ms_pc ms + 1)
    || match fetch_half_any segs (ms_mem ms) (ms_pc ms) with
       | Some _ => fetch_byte_traps segs (ms_pc ms + 2) || fetch_byte_traps segs (ms_pc ms + 3)
       | None => false end); discriminate.
Qed.

(* YK04R.v:99-108: the step keeps every hidden byte. *)
Corollary crt_fevt_step_accesses_avoid_keeps_hidden : forall ms ms' rs,
  step_accesses segs ms = MachineOk (@mkAccessReport _ ms' rs) ->
  ranges_avoid H rs ->
  ms' = unrestrict H (ms_mem ms) (restrict H ms').
Proof.
  intros ms ms' rs Hs Hrs.
  pose proof (crt_fevt_step_accesses_restrict_conv ms ms' rs Hs Hrs) as Hr.
  destruct (step_accesses_restrict segs H HH Hwx ms (restrict H ms') rs Hr) as (Hfull & _ & _).
  rewrite Hs in Hfull. injection Hfull as E. exact E.
Qed.
End d.

(* YK04R.v:124-126 at ExecF's footprint: every footprint entry is a range of visible bytes.  The same body as
   lib/A/Prog/LeafCgKit.v:38 fp_avoids (whose range_avoids / woff copy YK04.v:44-47 verbatim). *)
Definition crt_fevt_fp_avoids (H : word -> bool) (RNG : ExecF.footprint) : Prop :=
  forall (a : word) (n : nat), RNG (bv_unsigned a) n -> range_avoids H a n.

Section f.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

(* YK04R.v:132-137. *)
Lemma crt_fevt_ranges_avoid_of_fp : forall RNG accs,
  crt_fevt_fp_avoids H RNG -> Forall (ExecF.acc_in RNG) accs -> ranges_avoid H accs.
Proof.
  intros RNG accs Hfp HF a n Hin.
  apply Hfp. exact (proj1 (Forall_forall _ accs) HF (a, n) Hin).
Qed.

(* YK04R.v:139-144. *)
Lemma crt_fevt_munrestrict_agree : forall (full full' m : word -> option byte),
  (forall x, H x = true -> full' x = full x) -> munrestrict H full' m = munrestrict H full m.
Proof.
  intros full full' m Hag. apply functional_extensionality. intro x. unfold munrestrict.
  destruct (H x) eqn:Hx; [exact (Hag x Hx) | reflexivity].
Qed.

(* YK04R.v:146-167 at ExecF.mstepsF. *)
Theorem crt_fevt_mstepsF_restrict : forall RNG ms ms',
  ExecF.mstepsF segs RNG ms ms' -> crt_fevt_fp_avoids H RNG ->
  msteps segs (restrict H ms) (restrict H ms')
  /\ ms' = unrestrict H (ms_mem ms) (restrict H ms').
Proof.
  intros RNG ms ms' Hrun Hfp. induction Hrun as [ms | ms ms1 ms2 [Hsvc (accs & Hs & HF)] _ IH].
  - split; [apply mst_refl | symmetry; apply unrestrict_restrict].
  - pose proof (crt_fevt_ranges_avoid_of_fp RNG accs Hfp HF) as Hrs.
    destruct IH as [Hrest Heq2].
    pose proof (crt_fevt_step_accesses_avoid_keeps_hidden segs H HH Hwx ms ms1 accs Hs Hrs) as Heq1.
    split.
    + eapply mst_step; [exact Hsvc | | exact Hrest].
      unfold RiscvSemantics.step, drop_access_report.
      rewrite (crt_fevt_step_accesses_restrict_conv segs H HH Hwx ms ms1 accs Hs Hrs). reflexivity.
    + rewrite Heq2 at 1. unfold unrestrict. f_equal.
      apply crt_fevt_munrestrict_agree. intros x Hx.
      rewrite Heq1. cbn [ms_mem unrestrict]. unfold munrestrict. rewrite Hx. reflexivity.
Qed.
End f.

Section g. Context {fx : YK11.FPState}.
(* YA0nR.v:20-30 at ExecF.mstepsF, over any segment list without a wrapping writable-and-executable segment; the
   world's own w_Hoff gives H_off_segments. *)
Theorem crt_fevt_SRr_mstepsF : forall (segs : list Segment), wx_segs_nowrap segs ->
  forall (W : world segs) ms ms' model RNG (Q : world segs -> config -> Prop),
  ExecF.mstepsF segs RNG ms ms' ->
  crt_fevt_fp_avoids (w_H W) RNG ->
  (forall model', same_but_materialized model model' -> SRr segs W (mkCfg ms' model') Q) ->
  SRr segs W (mkCfg ms model) Q.
Proof.
  intros segs Hwx W ms ms' model RNG Q Hrun Hfp Hk.
  destruct (crt_fevt_mstepsF_restrict segs (w_H W) (w_Hoff W) Hwx RNG ms ms' Hrun Hfp) as [Hms Heq].
  apply (SRr_msteps segs Hwx W ms (restrict (w_H W) ms') model Q Hms).
  intros model' Hsame _. rewrite <- Heq. exact (Hk model' Hsame).
Qed.

(* YA0nR.v:32-41: the eventually form, for footprint runs stated as ExecF.evtF. *)
Corollary crt_fevt_SRr_evtF : forall (segs : list Segment), wx_segs_nowrap segs ->
  forall (W : world segs) ms model RNG (P : machine_state -> Prop) (Q : world segs -> config -> Prop),
  ExecF.evtF segs RNG P ms ->
  crt_fevt_fp_avoids (w_H W) RNG ->
  (forall ms' model', P ms' -> same_but_materialized model model' -> SRr segs W (mkCfg ms' model') Q) ->
  SRr segs W (mkCfg ms model) Q.
Proof.
  intros segs Hwx W ms model RNG P Q (ms' & Hrun & HP) Hfp Hk.
  exact (crt_fevt_SRr_mstepsF segs Hwx W ms ms' model RNG Q Hrun Hfp (fun model' Hs => Hk ms' model' HP Hs)).
Qed.
End g.
