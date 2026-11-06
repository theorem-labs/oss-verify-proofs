(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module paths and module names changed; 1161 of its 1364 lines of code are new or changed and 321 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/B/Prog/check_meter_cgW.v, with its module paths and module names changed; 949 of its 1151 lines of code are new or changed and 1162 lines of the source are left out. *)
(* check_meter_cgW: Theorem wire_check_meter_holds : wire_check_meter_holds_stmt, the image-A ASan walk of
   check_meter (fuzz_wire.asan 0x80340 = wire_sigma WS_check_meter), against the frozen statement
   lib/A/Prog/check_meter_cg.v. Form: reac-repacer/fuzz_uci lib/A/Prog/check_value_cgW.v (the walk of another check
   of the same family in image A), itself in the form of the released libreac/fuzz_decode lib/A/Prog/crtA_walk.v and
   its companions: footprint runs carried into SRr, an inner journal over the call's stack window, each call cut by
   its callee's contract. The release stage and the post (cmw_outside_dec, cmw_sf_frames, cmw_aview_mrd,
   cmw_aview_munch, cmw_aview_of_bytes1, cmw_release and the assembly at the end of cmw_entry) follow the image-B
   twin of this walk, lib/B/Prog/check_meter_cgW.v; cmw_sf_frames is reac-repacer/fuzz_uci lib/A/Prog/UciCcKit.v
   ucc_sf_frames, and the facts of the fake frame the stack malloc hands back (al_frames, frames_bounds) are read
   as in reac-repacer/fuzz_uci lib/A/Prog/check_clamp_cgW.v.
   The pieces:
     1. the INNER journal at the entry state (lib/Reusable/YCbq.v ajournal_sub_init), stack window
        [spZ regs - CM_STK, spZ regs), no footprint and no frame of its own;
     2. lib/A/Prog/WireCmSegs.v cm_seg1_F, the prologue; the journal follows the frame write by YCbq.v
        ajournal_exec;
     3. the class-0 fake-stack call, by lib/A/Prog/WireCmKit.v cm_stack_malloc_at from the statement's
        astack_malloc_realizes and stack_malloc_progressP premises;
     4. cm_seg2_F, the fake frame, its header and its shadow; then cm_seg3_F or cm_seg4_F and cm_seg5_F, which
        read the frame bytes behind their shadow checks and fix the offset and the meter test; then cm_seg6_F, the
        local counter and the arguments;
     5. the leaf rp_meter_counter, through the statement's wire_leaf_wr_at premise and the kit's leaf-call bridge
        lib/A/Prog/WireCcLeafb.v wcc_leafb_journal;
     6. cm_seg7_F, the result and the counter tests (no abort is reached), and cm_seg8_F, the release and the
        return; the frame is given back by the statement's astack_free_law premise and YCbq.v
        ajournal_after_write with no owned frame left;
     7. the post: the outer journal by YCbq.v ajournal_sub, acall_kept by YCbq.v acall_kept_of_journal, and the
        meter bound by the fake frame changing the allocator state in st_fs only. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YK11 YK0s YK0o YM05 YK04 YA0i YA0n YA0o YK1b.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI16 YI5b YI5c YP09 YO0f.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import
PropExec MState Mem Frame Cells Step Regs6ss.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require AE2k Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import WirePSyms WirePAddr WireCg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import check_meter_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import
WireCmSegs WireCmSegsEo WireCmSegsOk WireCmSegsCall WireCmSegsCmp WireCmSegsRel.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require
LeafCgKit LeafCgFacts LeafCgGlue WirePImg WireCcLeafb rp_meter_counter_cg WireCmKit.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_meter_counter_c check_meter.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.LeafCgKit.
Module AC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.AsanCells.
Module AImg := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Img0.
Module WL := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.WireCcLeafb.
Module LMC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_meter_counter_cg.
Module PMC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_meter_counter_c.
Module AMC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_meter_counter_c.
Module PCM := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.check_meter.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* image-free helpers (reac-repacer/fuzz_uci lib/A/Prog/check_value_cgW.v) *)
(* ------------------------------------------------------------------ *)

Lemma cmw_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof. exact WirePImg.wire_segs_low. Qed.

Lemma cmw_u64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz. Qed.

Lemma cmw_fp_avoids : forall (W : world tfibsegs),
  LCK.fp_avoids (@w_H tfibsegs W) (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W).
Proof. intros W a n H. unfold LCK.RNG_W in H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.

(* A footprint run from the walk's configuration at pc, carried into SRr (check_value_cgW cv_run, through
   lib/A/Prog/LeafCgFacts.v bridge_evtF_stmt_YA0n). *)
Lemma cmw_run {fx : YK11.FPState} : forall (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (pc : Z) (P : machine_state -> Prop) (Q : world tfibsegs -> config -> Prop),
  ExecF.evtF AImg.rsegs (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) P (@LCK.ms_of_regs fx pc regs mem) ->
  (forall ms' md', (exists ms0, P ms0 /\ ms_eqv ms0 ms') -> same_but_materialized md md' ->
     SRr tfibsegs W (mkCfg ms' md') Q) ->
  SRr tfibsegs W (@cfg_at fx tfibsegs pc regs mem md) Q.
Proof.
  intros W regs mem md pc P Q Hrun K. unfold cfg_at.
  pose proof (LeafCgGlue.evtF_eqv AImg.rsegs _ P _ _ Hrun (@LeafCgGlue.ms_of_regs_eqv fx pc regs mem)) as Hrun'.
  apply (LeafCgFacts.bridge_evtF_stmt_YA0n W _ md _ _ Q Hrun' (cmw_fp_avoids W)).
  intros ms' md' (ms1 & HP & HE & _) Hs. apply K; [exists ms1; split; assumption | exact Hs].
Qed.

Lemma cmw_ms_shape {fx : YK11.FPState} : forall (R : bvmap 5 word) (pc : word) (m : word -> option byte)
    (ms' : machine_state),
  ms_eqv (MS R (@fp_regs fx) pc (@fp_csr fx) None m (YK11.seg_rom tfibsegs)) ms' ->
  ms' = @YK11.mkst fx (ms_regs ms') pc m (YK11.seg_rom tfibsegs).
Proof.
  intros R pc m [r f p sv rv fc mm ro] (_ & Hf & Hp & Hs & Hr & Hc & Hm & Hro).
  cbn [MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
  subst. reflexivity.
Qed.

Lemma cmw_ms_reg : forall (R : bvmap 5 word) F pc fc rv m ro (ms' : machine_state) (r : bv 5),
  ms_eqv (MS R F pc fc rv m ro) ms' -> YK11.getr (ms_regs ms') r = YK11.getr R r.
Proof.
  intros R F pc fc rv m ro ms' r (HR & _). cbn [MS ms_regs] in HR. exact (LeafCgGlue.getr_xeqv _ _ HR r).
Qed.

Lemma cmw_regs_of : forall {x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
    x25 x26 x27 x28 x29 x30 x31 : word} {F : bvmap 5 word} {pc : word} {fc : bv 32} {rv : option word}
    {m ro : word -> option byte} {ms' : machine_state},
  ms_eqv (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                  x25 x26 x27 x28 x29 x30 x31) F pc fc rv m ro) ms' ->
  YK11.getr (ms_regs ms') (Z_to_bv 5 1) = x1 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 2) = x2 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 3) = x3 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 4) = x4 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 8) = x8 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 9) = x9 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 10) = x10 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 11) = x11 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 12) = x12 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 18) = x18 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 19) = x19 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 20) = x20 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 21) = x21 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 22) = x22 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 23) = x23 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 24) = x24 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 25) = x25 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 26) = x26 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 27) = x27.
Proof.
  intros until ms'. intros H.
  repeat split; (etransitivity; [apply (cmw_ms_reg _ _ _ _ _ _ _ _ _ H) | reflexivity]).
Qed.

(* A one-byte cell block, read as one cell. *)
Lemma cmw_cb1 : forall m A j, rw_cells AImg.rsegs m A [CB 1 j] -> exists b, rw_cells AImg.rsegs m A [C1 b].
Proof.
  intros m A j H. pose proof H as [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  destruct j as [|b [|? ?]]; cbn in Hl; try lia.
  exists b. destruct H as [[_ Hb'] Hw']. split; [split|]; [cbn; tauto | exact Hb' | exact Hw'].
Qed.

Lemma cmw_byte_eq : forall (H H' : word -> bool) (m m' : word -> option byte) (a : Z),
  apresent H m a -> apresent H' m' a -> aview tfibsegs H' m' a = aview tfibsegs H m a ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros H H' m m' a [Hh [b Hb]] [Hh' [b' Hb']] E.
  unfold aview, YP09.mbyte, mrestrict in E.
  rewrite Hh, Hh' in E. rewrite Hb, Hb' in E. cbn in E.
  injection E as E. rewrite Hb, Hb'. f_equal. apply bv_eq. exact E.
Qed.

Lemma cmw_rw_cells_ext : forall (m m' : word -> option byte) (A : Z) (cs : list cell),
  rw_cells AImg.rsegs m A cs ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) -> m' (wa a) = m (wa a)) ->
  rw_cells AImg.rsegs m' A cs.
Proof.
  intros m m' A cs [[Hwf (Ha & Hl & Hb)] (Wa & Wl & Hw)] He.
  pose proof (cells_bytes_length cs Hwf) as L.
  split; [split; [exact Hwf|]|].
  - split; [exact Ha|]. split; [exact Hl|]. intros i Hi.
    assert (Hi' : A <= A + Z.of_nat i < A + Z.of_nat (cells_size cs)) by (rewrite <- L; lia).
    unfold mrd. rewrite (He _ Hi'). exact (Hb i Hi).
  - split; [exact Wa|]. split; [exact Wl|]. intros i Hi.
    unfold wview. rewrite (He (A + i)) by lia. exact (Hw i Hi).
Qed.

(* A byte that was present before a run is present after it: the run's wmono gives it back. The byte is not one
   of the loaded image's, so outside the image the view is the overlay byte itself. *)
Lemma cmw_grows_at : forall (W : world tfibsegs) (m m' : word -> option byte) (x : word),
  wmono AImg.rsegs m m' -> apresent (w_H W) m (bv_unsigned x) -> ~ in_img tfibsegs (bv_unsigned x) ->
  m' x <> None.
Proof.
  intros W m m' x WM (Hh & b & Hb) Hni.
  assert (Hw : wview AImg.rsegs m' x <> None).
  { refine (WM x _). unfold wview. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
  destruct (m' x) as [b'|] eqn:Em1; [discriminate|]. exfalso.
  unfold wview in Hw.
  rewrite (LeafCgGlue.find_segment_out AImg.rsegs (bv_unsigned x) 1) in Hw.
  - rewrite Em1 in Hw. cbn in Hw. exact (Hw eq_refl).
  - pose proof (bv_unsigned_in_range 64 x). lia.
  - intros sg Hin Hr. apply Hni. exists sg. split; [exact Hin | exact Hr].
Qed.

Lemma cmw_mem_grows : forall (W : world tfibsegs) (m m' : word -> option byte),
  wmono AImg.rsegs m m' ->
  (forall x : word, m' x = m x \/
     (apresent (w_H W) m (bv_unsigned x) /\ ~ in_img tfibsegs (bv_unsigned x))) ->
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m').
Proof.
  intros W m m' WM HC x Hx. unfold mrestrict in *. revert Hx.
  destruct (w_H W x) eqn:Ehx; intros Hx; [exact Hx|].
  destruct (HC x) as [E | (Hp & Hni)]; [rewrite E; exact Hx|].
  exact (cmw_grows_at W m m' x WM Hp Hni).
Qed.

(* Bytes read back at another memory that agrees on them. *)
Lemma cmw_bytes_ext : forall (m m' : word -> option byte) (a : Z) (bl : list byte),
  bytes_at AImg.rsegs m a bl ->
  (forall x, a <= x < a + Z.of_nat (length bl) -> m' (wa x) = m (wa x)) ->
  bytes_at AImg.rsegs m' a bl.
Proof.
  intros m m' a bl (Ha & Hl & Hb) He.
  split; [exact Ha|]. split; [exact Hl|]. intros i Hi.
  unfold mrd. rewrite (He (a + Z.of_nat i)) by lia. exact (Hb i Hi).
Qed.

Lemma cmw_pres_after : forall (W : world tfibsegs) (m m' : word -> option byte) (a : Z),
  wmono AImg.rsegs m m' -> apresent (w_H W) m a -> ~ in_img tfibsegs a -> 0 <= a < 2 ^ 64 ->
  apresent (w_H W) m' a.
Proof.
  intros W m m' a WM Hp Hni Ha. pose proof Hp as (Hh & _). split; [exact Hh|].
  pose proof (cmw_grows_at W m m' (Z_to_bv 64 a) WM) as G.
  rewrite (cmw_u64 a Ha) in G. specialize (G Hp Hni).
  destruct (m' (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | congruence].
Qed.

(* The only range the leaf writes is the two bytes of the counter. *)
Lemma cmw_in_wr : forall n' bs' c a, LCK.in_wr (LMC.wire_rmc_wr n' bs' c) a -> c <= a < c + 2.
Proof.
  intros n' bs' c a H. unfold LCK.in_wr, LMC.wire_rmc_wr in H.
  destruct (PMC.meter_ok n' bs'); [|inversion H].
  inversion H as [? ? Hh|? ? Ht]; [cbn in Hh; lia | inversion Ht].
Qed.

(* `outside` of a list of ranges is decidable (image-B twin lib/B/Prog/check_meter_cgW.v cm_outside_dec). *)
Lemma cmw_outside_dec : forall (Wl : list (Z * Z)) x, outside Wl x \/ ~ outside Wl x.
Proof.
  induction Wl as [|[lo hi] Wl IH]; intros x; [left; exact I|].
  change (outside ((lo, hi) :: Wl) x) with (~ (lo <= x < hi) /\ outside Wl x).
  destruct (IH x) as [H|H].
  - destruct (Z_le_gt_dec lo x) as [H1|H1]; [destruct (Z_lt_ge_dec x hi) as [H2|H2]|].
    + right. intros [H3 _]. apply H3. split; assumption.
    + left. split; [intros [_ H3]; lia | exact H].
    + left. split; [intros [H3 _]; lia | exact H].
  - right. intros [_ H2]. exact (H H2).
Qed.

(* Giving back the only frame of a state leaves the rest of its frames. *)
Lemma cmw_sf_frames : forall cid pos s rest,
  frames s = (cid, pos) :: rest -> frames (stack_free_state cid pos s) = rest.
Proof.
  intros cid pos s rest Hf.
  assert (E : frames (stack_free_state cid pos s) = del_pos (frames s) cid pos) by reflexivity.
  rewrite E, Hf. cbn [del_pos]. rewrite !Z.eqb_refl. reflexivity.
Qed.

Lemma cmw_aview_mrd : forall (W : world tfibsegs) mem a, w_H W (Z_to_bv 64 a) = false ->
  aview tfibsegs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (mrd AImg.rsegs mem (wa a)).
Proof. intros W mem a H. unfold aview, YP09.mbyte, mrestrict, mrd, wa. rewrite H. reflexivity. Qed.

Lemma cmw_aview_munch : forall (H : word -> bool) (m m' : word -> option byte) (Wl : list (Z * Z)) a,
  munch Wl m m' -> 0 <= a < 2 ^ 64 -> outside Wl a -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof.
  intros H m m' Wl a MU Ha Ho. apply aview_eq_of. unfold mrestrict. rewrite (MU (Z_to_bv 64 a)); [reflexivity|].
  rewrite cmw_u64 by exact Ha. exact Ho.
Qed.

(* A visible byte the view shows as v reads as the byte v. *)
Lemma cmw_aview_of_bytes1 : forall (W : world tfibsegs) m a (b : byte),
  w_H W (Z_to_bv 64 a) = false -> bytes_at AImg.rsegs m a [b] -> aview tfibsegs (w_H W) m a = Some (bv_unsigned b).
Proof.
  intros W m a b Hv (H0 & H1 & H). rewrite (cmw_aview_mrd W m a Hv).
  specialize (H 0%nat ltac:(cbn; lia)). rewrite Z.add_0_r in H. rewrite H. reflexivity.
Qed.

Section Walk.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation sink := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HPCS : pc_stack_malloc (as_code B) CM_CID = wire_sigma WS___asan_stack_malloc_0.
Hypothesis HCELLS : wire_cells B.
Hypothesis LAWS : AR_laws segs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law segs B.
Hypothesis FFL : frame_flag_lawP segs B.
Hypothesis ASM : forall fx' : YK11.FPState, @astack_malloc_realizes fx' rc segs B CM_CID.
Hypothesis LEAF : forall fx' : YK11.FPState, @wire_leaf_wr_at rc B (@LMC.wire_rp_meter_counter_cg) fx'.
Local Abbreviation ajournalA := (@ajournal rc sink segs B).

(* The fake frame given back: a run that wrote only bytes of its own frame (and its shadow) and the frame's flag
   byte, which it left 0, leaves the journal with no frame of its own at the state astack_free_law names
   (reac-repacer/fuzz_uci lib/A/Prog/UciCcKit.v ucc_flag_store_pi, after its run). *)
Lemma cmw_release : forall STK sp0 FP ly S W0 mem md lyc Sc W memc mdc k cid pos memc' mdc' (Wl : list (Z * Z)),
  ajournalA STK sp0 FP ly S W0 mem md [(cid, pos)] lyc Sc W memc mdc k ->
  munch Wl memc memc' -> mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memc') ->
  same_but_materialized mdc mdc' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside Wl a ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc [(cid, pos)] a \/ a = flag_addr lyc cid pos) ->
  (forall x : word, ~ outside Wl (bv_unsigned x) -> w_H W x = false) ->
  aview segs (w_H W) memc' (flag_addr lyc cid pos) = Some 0 ->
  ajournalA STK sp0 FP ly S W0 mem md [] lyc (stack_free_state cid pos Sc) W memc' mdc' k.
Proof.
  intros STK sp0 FP ly S W0 mem md lyc Sc W memc mdc k cid pos memc' mdc' Wl HJ MU MG Hs HW Hvis Hfl0.
  pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hkk & _).
  assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
  destruct (FFL lyc Sc W memc mdc cid pos HAR Hin) as (Hfp & Hfo & Hfr_rng & Hfr_num).
  assert (Heqw : forall a, 0 <= a < 2 ^ 64 -> outside Wl a ->
    aview segs (w_H W) memc' a = aview segs (w_H W) memc a)
    by (intros a Ha Ho; exact (cmw_aview_munch (w_H W) memc memc' Wl a MU Ha Ho)).
  pose proof MG as MGr.
  pose proof (same_but_materialized_wvb mdc mdc' Hs) as Emd.
  assert (HAR' : AR segs B lyc (stack_free_state cid pos Sc) W memc' mdc').
  { eapply (ASF lyc Sc W memc mdc memc' mdc' cid pos HAR Hin).
    - exact Hfl0.
    - intros a Ha Ho Hne. destruct (cmw_outside_dec Wl a) as [Hout|Hout]; [exact (Heqw a Ha Hout)|].
      destruct (HW a Ha Hout) as [Hw | Hw]; [|exact (False_ind _ (Hne Hw))].
      exact (False_ind _ (proj1 (awr_byte_cases segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) Ho)).
    - intros a Hv. eapply aview_keeps_vis; [exact MGr | exact Hv].
    - rewrite Emd. destruct mdc as [fm [mp lz mt] io fs pr li ti sg sc]; reflexivity.
    - rewrite Emd. destruct mdc as [fm [mp lz mt] io fs pr li ti sg sc]; reflexivity.
    - rewrite Emd. destruct mdc as [fm [mp lz mt] io fs pr li ti sg sc]; reflexivity.
    - intros a _ Hh. apply MU. destruct (cmw_outside_dec Wl (bv_unsigned (w64 a))) as [Ho|Ho]; [exact Ho|].
      rewrite (Hvis _ Ho) in Hh. discriminate. }
  eapply (ajournal_after_write segs B LAWS cmw_segs_low STK sp0 FP ly S W0 mem md [(cid, pos)] lyc Sc W memc
    mdc k memc' mdc' (fun a => 0 <= a < 2 ^ 64 /\ ~ outside Wl a) (stack_free_state cid pos Sc) [] HJ).
  - intros a Ha Hna. apply Heqw; [exact Ha|].
    destruct (cmw_outside_dec Wl a) as [Ho|Ho]; [exact Ho|]. exfalso. exact (Hna (conj Ha Ho)).
  - intros a Ha. eapply apresent_grows; [exact MGr | exact Ha].
  - exact Hs.
  - intros a [Ha Ho]. destruct (HW a Ha Ho) as [Hw | ->];
      [left; exact Hw | right; split; [exact Hfo | exact Hfr_rng]].
  - exact HAR'.
  - unfold ablocks. rewrite blocks_stack_free_state. reflexivity.
  - reflexivity.
  - cbn. lia.
  - exact (cmw_sf_frames cid pos Sc (frames S) Hfrs).
  - pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
    apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT].
Qed.

Section Entry.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (f n : Z)
  (bs : list byte).
Hypothesis HJ : ajournalA STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis Hra : YK0s.ret_ok (YK11.getr regs 1).
Hypothesis Hra4 : 4096 <= raZ regs.
Hypothesis Hgp : YK11.getr regs 3 = w64 (as_gp B).
Hypothesis Htp : YK11.getr regs 4 = w64 (as_tp B).
Hypothesis H10 : YK11.getr regs 10 = w64 f.
Hypothesis H11 : YK11.getr regs 11 = w64 n.
Hypothesis Hal : spZ regs mod 16 = 0.
Hypothesis Hwlo : sp0 - STK <= spZ regs - CM_STK.
Hypothesis Hwhi : spZ regs <= sp0.
Hypothesis Hlen : Z.of_nat (length bs) = n.
Hypothesis Hblk : 0 < n -> exists bA nA, In (bA, nA) (ablocks B lyc Sc) /\ bA <= f /\ f + n <= bA + nA.
Hypothesis Hgarr : garr8 segs (mrestrict (w_H W) memc) f (map (fun b : byte => bv_unsigned b) bs).
Hypothesis Hcnt : count_cid CM_CID (frames Sc) < fs_frames CM_CID.
Hypothesis Hnev : st_nev S + k + CM_EV <= EV_MAX.

Local Abbreviation POST := (wire_cm_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs).
Local Abbreviation JI ly1 S1 W1 m1 md1 k1 :=
  (ajournalA CM_STK (spZ regs) [] lyc Sc W memc mdc [] ly1 S1 W1 m1 md1 k1).

Lemma cmw_HARc : AR segs B lyc Sc W memc mdc.
Proof. destruct HJ as (HAR & _). exact HAR. Qed.

Lemma cmw_JI0 : JI lyc Sc W memc mdc 0.
Proof.
  apply (ajournal_sub_init segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k CM_STK (spZ regs) []
           (spZ regs - sp0) HJ).
  - lia.
  - pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (H16 & _) & _).
    rewrite Zminus_mod, Hal, H16. reflexivity.
  - lia.
  - unfold CM_STK, CM_FRAME, CM_ALIGN, ESTACK. lia.
  - lia.
Qed.

Lemma cmw_sp_rng : YM05.alloc_ceiling + CM_STK <= spZ regs /\ spZ regs <= 2 ^ 47.
Proof.
  pose proof cmw_JI0 as J. destruct J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    (_ & _ & Hc & Hlo & Hhi & H47 & _) & _).
  lia.
Qed.

Lemma cmw_win : forall ly1 S1 W1 m1 md1 k1, JI ly1 S1 W1 m1 md1 k1 ->
  forall a, spZ regs - CM_STK <= a < spZ regs -> apresent (w_H W1) m1 a.
Proof.
  intros ly1 S1 W1 m1 md1 k1 J.
  destruct J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). exact Hpres.
Qed.

Lemma cmw_AR : forall ly1 S1 W1 m1 md1 k1, JI ly1 S1 W1 m1 md1 k1 -> AR segs B ly1 S1 W1 m1 md1.
Proof. intros ly1 S1 W1 m1 md1 k1 J. destruct J as (HAR & _). exact HAR. Qed.

(* n is the length of bs, and when it is positive the caller's block that holds the frame bounds it. *)
Lemma cmw_nrng : 0 <= n /\ n <= 2 ^ 47 /\ (0 < n -> 0 <= f /\ f + n <= 2 ^ 47).
Proof.
  pose proof cmw_HARc as HARc.
  assert (HP : 0 < n -> 0 <= f /\ f + n <= 2 ^ 47).
  { intros Hn0. destruct (Hblk Hn0) as (bA & nA & HbA & H1 & H2).
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HARc HbA) as (_ & H4096 & Hceil & _ & _ & _ & _).
    pose proof (@YG0f.ASAN_CEIL_range rc) as [CR _]. unfold YG0f.ASAN_CEIL in CR.
    assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia).
    split; lia. }
  split; [lia|]. split; [|exact HP].
  destruct (Z.eq_dec n 0) as [E0|Hn0]; [lia|]. destruct (HP ltac:(lia)) as [H1 H2]. lia.
Qed.

(* The realigned stack pointer: `andi sp, sp, -0x20` after the 0x80 frame, so at most 0x10 lower. *)
Lemma cmw_sp1 : spZ regs - 144 <= 32 * ((spZ regs - 128) / 32) <= spZ regs - 128.
Proof.
  assert (Hm16 : (spZ regs - 128) mod 16 = 0) by (rewrite Zminus_mod, Hal; reflexivity).
  Z.div_mod_to_equations. lia.
Qed.

(* The caller's buffer: the journal keeps every byte of a block it keeps, so the frame bytes read the same at
   every state of the walk. *)
Lemma cmw_bytes_keep : forall ow ly1 S1 W1 m1 md1 k1 bA nA,
  ajournalA CM_STK (spZ regs) [] lyc Sc W memc mdc ow ly1 S1 W1 m1 md1 k1 ->
  In (bA, nA) (ablocks B lyc Sc) -> In (bA, nA) (ablocks B ly1 S1) ->
  bA <= f -> f + n <= bA + nA -> 0 < n ->
  bytes_at AImg.rsegs m1 f bs.
Proof.
  intros ow ly1 S1 W1 m1 md1 k1 bA nA J Hin0 Hin1 Hlo Hhi Hn.
  pose proof cmw_HARc as HARc.
  pose proof (proj1 J) as HAR1.
  pose proof cmw_nrng as (_ & Hn47 & Hfn). destruct (Hfn Hn) as [Hf0 Hf47].
  destruct J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Jblk & _).
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HARc Hin0) as (_ & _ & _ & _ & Hpr0 & _ & _).
  destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 bA nA HAR1 Hin1) as (_ & _ & _ & _ & Hpr1 & _ & _).
  assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia).
  assert (HB0 : bytes_at AImg.rsegs memc f bs).
  { apply (WL.wcc_leafb_bytes_garr8 W memc f bs Hgarr); lia. }
  apply (cmw_bytes_ext memc m1 f bs HB0). intros x Hx. rewrite Hlen in Hx.
  unfold wa. apply (cmw_byte_eq (w_H W) (w_H W1) memc m1 x).
  - apply Hpr0. lia.
  - apply Hpr1. lia.
  - replace x with (bA + (x - bA)) by lia.
    apply (Jblk bA nA (x - bA) Hin0 Hin1 ltac:(lia)). intros (r & Hin & _). destruct Hin.
Qed.

Lemma cmw_entry : SRr segs W (@cfg_at fx segs (wire_sigma WS_check_meter) regs memc mdc) POST.
Proof.
  pose proof cmw_sp_rng as [Hsp1 Hsp2].
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  pose proof cmw_JI0 as JI0.
  pose proof (cmw_win _ _ _ _ _ _ JI0) as Hpres0.
  pose proof cmw_HARc as HARc.
  pose proof cmw_nrng as (Hn0 & Hn47 & Hfn).
  pose proof cmw_sp1 as HSP1.
  assert (HE64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HE47 : 2 ^ 47 = 140737488355328) by reflexivity.
  assert (HCS : CM_STK = 4240) by reflexivity.
  assert (HES : ESTACK = 4096) by reflexivity.
  assert (ESPZ : bv_unsigned (YK11.getr regs (Z_to_bv 5 2)) = spZ regs) by reflexivity.
  destruct (WL.wcc_leafb_asan_cells B HCELLS lyc Sc W memc mdc HARc)
    as (CK & GCK & _ & _ & _ & UA & GUA & _).
  assert (HSTK : stk AImg.rsegs memc (spZ regs - CM_STK) (spZ regs))
    by (apply (WL.wcc_leafb_stk W memc); [lia | lia | exact Hpres0]).
  assert (RFR : ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) (spZ regs - 128) 128)
    by (eapply (WL.wcc_leafb_rng_journal B); [exact JI0 | lia | lia]).
  destruct (WL.wcc_leafb_rng_cells W) as [RGC RCK].
  assert (RGU : ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) AC.GOT_UAR 8).
  { apply (WL.wcc_leafb_rng W); [unfold AC.GOT_UAR; lia | unfold AC.GOT_UAR; lia |]. intros b Hb.
    replace b with (AC.GOT_UAR + (b - AC.GOT_UAR)) by lia.
    apply (WL.wcc_leafb_covers_visible (w_H W) AC.GOT_UAR 8 (b - AC.GOT_UAR) (w_Hoff W));
      [vm_compute; reflexivity | lia | unfold AC.GOT_UAR; lia]. }
  assert (RUA : ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) AC.UAR 4).
  { apply (WL.wcc_leafb_rng W); [unfold AC.UAR; lia | unfold AC.UAR; lia |]. intros b Hb.
    replace b with (AC.UAR + (b - AC.UAR)) by lia.
    apply (WL.wcc_leafb_covers_visible (w_H W) AC.UAR 4 (b - AC.UAR) (w_Hoff W));
      [vm_compute; reflexivity | lia | unfold AC.UAR; lia]. }
  assert (EWS : wire_sigma WS_check_meter = 525120) by reflexivity.
  rewrite EWS.
  (* 0x80340 .. 0x803ac: the prologue, up to the class-0 stack malloc *)
  eapply (@cmw_run fx W regs memc mdc 525120).
  { unfold LCK.ms_of_regs.
    apply (cm_seg1_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             (spZ regs - CM_STK));
    [ exact HSTK | lia
    | exact GCK | exact CK | exact GUA | exact UA | unfold AC.UAR in *; lia
    | exact RFR | exact RGC | exact RCK | exact RGU | exact RUA ]. }
  intros ms' md' (ms0 & (m1 & jlo & -> & MU & WM & FRLO & FRHI) & EQV) SBM.
  rewrite ESPZ in MU, FRLO, FRHI.
  destruct (cmw_regs_of EQV) as (E1 & E2 & E3 & E4 & E8 & E9 & E10' & E11' & E12' & E18 & E19 & E20 & E21 & E22 &
    E23 & E24 & E25 & E26 & E27).
  rewrite ESPZ in E2, E9.
  rewrite (cmw_ms_shape _ _ _ _ EQV).
  (* the inner journal after the prologue's frame write *)
  assert (HJ1 : JI lyc Sc W m1 md' 0).
  { apply (ajournal_exec segs B LAWS cmw_segs_low CM_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W memc mdc 0
             m1 md' (fun a => spZ regs - 128 <= a < spZ regs) JI0).
    - intros x Hx. unfold mrestrict. rewrite (MU x); [reflexivity|]. cbn [outside]. split; [exact Hx | exact I].
    - intros x Hx. unfold mrestrict in *. revert Hx. destruct (w_H W x) eqn:Ehx; intros Hx; [exact Hx|].
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs - 128)) as [Hl|Hl];
        [rewrite (MU x); [exact Hx | cbn [outside]; split; [lia | exact I]]|].
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [Hh|Hh];
        [|rewrite (MU x); [exact Hx | cbn [outside]; split; [lia | exact I]]].
      assert (Hxr : spZ regs - CM_STK <= bv_unsigned x < spZ regs) by lia.
      destruct (Hpres0 _ Hxr) as [_ (b & Hb)].
      assert (Hw : wview AImg.rsegs m1 x <> None).
      { refine (WM x _). unfold wview. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
      unfold wview in Hw. destruct (m1 x) as [b'|] eqn:Em1; [discriminate|]. exfalso.
      rewrite (LeafCgGlue.find_segment_out AImg.rsegs (bv_unsigned x) 1) in Hw; [exact (Hw eq_refl)|lia|].
      intros sg Hin Hr. pose proof (cmw_segs_low (bv_unsigned x) (ex_intro _ sg (conj Hin Hr))) as Hlow.
      unfold kLowMemEnd in Hlow. lia.
    - intros x Hx.
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs - 128)) as [Hl|Hl];
        [apply (MU x); cbn [outside]; split; [lia | exact I]|].
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [Hh|Hh];
        [|apply (MU x); cbn [outside]; split; [lia | exact I]].
      exfalso.
      assert (Hxr : spZ regs - CM_STK <= bv_unsigned x < spZ regs) by lia.
      pose proof (proj1 (Hpres0 _ Hxr)) as Hhx. rewrite Z_to_bv_bv_unsigned in Hhx. congruence.
    - exact SBM.
    - intros a Ha. cbv beta in Ha. left. lia. }
  (* 0x803ac: the class-0 fake-stack call *)
  set (SP1 := 32 * ((spZ regs - 128) / 32)) in *.
  assert (HOM : (SP1 - spZ regs) mod 16 = 0).
  { unfold SP1. rewrite Zminus_mod, Hal.
    replace (32 * ((spZ regs - 128) / 32)) with ((2 * ((spZ regs - 128) / 32)) * 16) by lia.
    rewrite Z_mod_mult. reflexivity. }
  assert (ERA : YK11.getr (ms_regs ms') (Z_to_bv 5 1) = Z_to_bv 64 525232) by exact E1.
  assert (EPC : pc_stack_malloc (as_code B) CM_CID = 247108) by (rewrite HPCS; reflexivity).
  rewrite <- EPC.
  eapply SRr_bind.
  { eapply (WireCmKit.cm_stack_malloc_at B LAWS SMP CM_CID (ASM fx) ltac:(unfold CM_CID; lia)
      W (ms_regs ms') m1 CM_STK (spZ regs) (@nil (Z * Z)) lyc Sc W memc mdc (@nil (Z * Z)) lyc Sc md' 0
      (SP1 - spZ regs) (Z_to_bv 64 525232) HJ1).
    - replace (spZ (ms_regs ms')) with (bv_unsigned (YK11.getr (ms_regs ms') (Z_to_bv 5 2))) by reflexivity.
      rewrite E2, (cmw_u64 SP1) by (unfold SP1 in *; lia). lia.
    - exact HOM.
    - unfold SP1 in *; lia.
    - unfold SP1 in *; lia.
    - etransitivity; [exact E3 | exact Hgp].
    - etransitivity; [exact E4 | exact Htp].
    - exact ERA.
    - apply YK0s.ret_ok_even; reflexivity.
    - exact Hcnt. }
  cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab2 & Hfrs2 & Hnev2 &
    Hset2 & Hz & Hflag & Hfpres & HK1).
  pose proof (proj1 HJ2) as HAR2.
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  assert (Hin2 : In (CM_CID, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
  destruct (al_frames _ _ LAWS _ _ _ _ _ CM_CID pos HAR2 Hin2) as (HFal & HFapp & HFb & HFsh).
  destruct (frames_bounds segs B LAWS _ _ _ _ _ CM_CID pos HAR2 Hin2) as (HF0 & HFc & _).
  change (fs_frame_bytes CM_CID) with 64 in HFb, HFc, HFapp, Hz, Hflag, Hfpres.
  change (fs_frame_bytes CM_CID / 8) with 8 in HFsh.
  set (FA := frame_addr lyc CM_CID pos) in *.
  assert (HFA8 : 0 <= FA / 8 <= 17592186044416)
    by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (HAK : AC.ASAN_K = 2147450880) by reflexivity.
  assert (HSHE : AC.shadow_addr FA = YG0f.shadow_addr FA)
    by (unfold AC.shadow_addr, YG0f.shadow_addr, AC.ASAN_K, SHADOW_OFF; lia).
  assert (HDF : FA + 64 <= spZ regs - 144) by lia.
  assert (HDS : FA / 8 + AC.ASAN_K + 8 <= spZ regs - 144) by lia.
  assert (HD : FA / 8 + AC.ASAN_K + 8 <= FA \/ FA + 64 <= FA / 8 + AC.ASAN_K).
  { destruct HFapp as (_ & [HL | [HH _]]);
    [right; unfold kLowShadowBeg in HL | left; unfold kHighMemBeg in HH]; lia. }
  (* the saved words, carried across the call: they lie above the call's stack window *)
  match type of FRHI with rw_cells _ _ _ ?cs =>
    assert (FRH2 : rw_cells AImg.rsegs mem2 (spZ regs - 96) cs) end.
  { apply (cmw_rw_cells_ext m1 mem2 _ _ FRHI). intros a Ha.
    cbn [cells_size csize cm_frhi Nat.add] in Ha.
    unfold wa. apply (cmw_byte_eq (w_H W) (w_H W) m1 mem2 a).
    - apply (cmw_win _ _ _ _ _ _ HJ1). lia.
    - apply Hpres2. lia.
    - apply (proj1 HK1); unfold SP1 in *; lia. }
  (* the frame's bytes, its shadow bytes and the realigned window as cell blocks *)
  assert (HSTKF : stk AImg.rsegs mem2 FA (FA + 64))
    by (apply (WL.wcc_leafb_stk W mem2); [lia | lia | intros a Ha; apply Hfpres; lia]).
  destruct (stk_carve AImg.rsegs mem2 FA (FA + 64) 64%nat HSTKF ltac:(cbn; lia)) as [_ [jF FRF]].
  replace (FA + 64 - Z.of_nat 64) with FA in FRF by (cbn; lia).
  assert (HSHP : forall a, AC.shadow_addr FA <= a < AC.shadow_addr FA + 8 -> apresent (w_H W) mem2 a).
  { intros a Ha. rewrite HSHE in Ha.
    replace a with (YG0f.shadow_addr FA + (a - YG0f.shadow_addr FA)) by lia.
    exact (proj1 (HFsh (a - YG0f.shadow_addr FA) ltac:(lia))). }
  assert (HSTKS : stk AImg.rsegs mem2 (AC.shadow_addr FA) (AC.shadow_addr FA + 8))
    by (apply (WL.wcc_leafb_stk W mem2);
        [unfold AC.shadow_addr; lia | unfold AC.shadow_addr; lia | exact HSHP]).
  destruct (stk_carve AImg.rsegs mem2 (AC.shadow_addr FA) (AC.shadow_addr FA + 8) 8%nat HSTKS
              ltac:(cbn; lia)) as [_ [jsh FRS]].
  replace (AC.shadow_addr FA + 8 - Z.of_nat 8) with (AC.shadow_addr FA) in FRS by (cbn; lia).
  assert (HSTKG : stk AImg.rsegs mem2 SP1 (SP1 + 32))
    by (apply (WL.wcc_leafb_stk W mem2);
        [unfold SP1 in *; lia | unfold SP1 in *; lia | intros a Ha; apply Hpres2; unfold SP1 in *; lia]).
  destruct (stk_carve AImg.rsegs mem2 SP1 (SP1 + 32) 32%nat HSTKG ltac:(cbn; lia)) as [_ [jg FRG]].
  replace (SP1 + 32 - Z.of_nat 32) with SP1 in FRG by (cbn; lia).
  assert (RFR2 : ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) (spZ regs - 144) 144)
    by (eapply (WL.wcc_leafb_rng_journal B); [exact HJ2 | lia | lia]).
  assert (RFF : ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) FA 64)
    by (apply (WL.wcc_leafb_rng_vis W mem2); [lia | lia | intros a Ha; apply Hfpres; lia]).
  assert (RFS : ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) (AC.shadow_addr FA) 8)
    by (apply (WL.wcc_leafb_rng_vis W mem2);
        [unfold AC.shadow_addr; lia | unfold AC.shadow_addr; lia | exact HSHP]).
  (* the registers the call kept *)
  assert (Q2 : YK11.getr regs2 (Z_to_bv 5 2) = Z_to_bv 64 SP1)
    by (etransitivity; [exact (HP2 2 ltac:(unfold acallee_saved; lia)) | exact E2]).
  assert (Q9 : YK11.getr regs2 (Z_to_bv 5 9) = Z_to_bv 64 SP1)
    by (etransitivity; [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | exact E9]).
  assert (Q8 : YK11.getr regs2 (Z_to_bv 5 8) = Z_to_bv 64 (spZ regs)).
  { etransitivity; [exact (HP2 8 ltac:(unfold acallee_saved; lia))|].
    etransitivity; [exact E8|]. unfold spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (Q19 : YK11.getr regs2 (Z_to_bv 5 19) = Z_to_bv 64 f).
  { etransitivity; [exact (HP2 19 ltac:(unfold acallee_saved; lia))|].
    etransitivity; [exact E19 | exact H10]. }
  assert (Q20 : YK11.getr regs2 (Z_to_bv 5 20) = Z_to_bv 64 n).
  { etransitivity; [exact (HP2 20 ltac:(unfold acallee_saved; lia))|].
    etransitivity; [exact E20 | exact H11]. }
  assert (Q24 : YK11.getr regs2 (Z_to_bv 5 24) = Z_to_bv 64 AC.ASAN_K)
    by (etransitivity; [exact (HP2 24 ltac:(unfold acallee_saved; lia)) | exact E24]).
  (* 0x803b0 .. 0x80440: the fake frame, its header and its shadow *)
  change (mkCfg (YK11.mkst regs2 (Z_to_bv 64 525232) mem2 (YK11.seg_rom segs)) md2)
    with (@cfg_at fx segs 525232 regs2 mem2 md2).
  eapply (@cmw_run fx W regs2 mem2 md2 525232).
  { unfold LCK.ms_of_regs.
    assert (Q10 : YK11.getr regs2 (Z_to_bv 5 10) = Z_to_bv 64 FA) by exact Ha0.
    rewrite Q2, Q8, Q9, Q10, Q19, Q20, Q24.
    eapply cm_seg2_F;
    [ unfold SP1 in *; lia | unfold SP1 in *; lia | lia | lia | lia | exact HDF | exact HDS | exact HD
    | exact FRG | exact FRH2 | exact FRF | exact FRS | exact RFR2 | exact RFF | exact RFS ]. }
  intros ms2' md2' (ms02 & (m2 & jF2 & jsh2 & -> & MU2 & WM2 & FRH3 & FRF2 & FRS2) & EQV2) SBM2.
  destruct (cmw_regs_of EQV2) as (G1 & G2 & G3 & G4 & G8 & G9 & G10 & G11 & G12 & G18 & G19 & G20 & G21 & G22 &
    G23 & G24 & G25 & G26 & G27).
  rewrite (cmw_ms_shape _ _ _ _ EQV2).
  (* every address is in one of the three written ranges or outside them all *)
  assert (HDEC : forall a : Z,
    (spZ regs - 144 <= a < spZ regs) \/ (FA <= a < FA + 24) \/
    (AC.shadow_addr FA <= a < AC.shadow_addr FA + 8) \/
    outside [(spZ regs - 144, spZ regs); (FA, FA + 24);
             (AC.shadow_addr FA, AC.shadow_addr FA + 8)] a).
  { intros a. cbn [outside fst snd].
    destruct (Z_lt_ge_dec a (spZ regs - 144)) as [?|?]; destruct (Z_lt_ge_dec a (spZ regs)) as [?|?];
    destruct (Z_lt_ge_dec a FA) as [?|?]; destruct (Z_lt_ge_dec a (FA + 24)) as [?|?];
    destruct (Z_lt_ge_dec a (AC.shadow_addr FA)) as [?|?];
    destruct (Z_lt_ge_dec a (AC.shadow_addr FA + 8)) as [?|?];
    try (left; lia); try (right; left; lia); try (right; right; left; lia);
    right; right; right; repeat split; try exact I; lia. }
  assert (HNIW : forall a, spZ regs - 144 <= a < spZ regs -> ~ in_img segs a)
    by (intros a Ha Hi; pose proof (cmw_segs_low a Hi); unfold kLowMemEnd in *; lia).
  assert (HNIS : forall a, AC.shadow_addr FA <= a < AC.shadow_addr FA + 8 -> ~ in_img segs a)
    by (intros a Ha Hi; pose proof (cmw_segs_low a Hi); unfold kLowMemEnd, AC.shadow_addr in *; lia).
  assert (HNIF : forall a, FA <= a < FA + 64 -> ~ in_img segs a).
  { intros a Ha. eapply (frm_img segs B LAWS); [exact HAR2 | exact Hin2 |].
    change (fs_frame_bytes CM_CID) with 64. lia. }
  (* the inner journal after the fake frame's header and shadow *)
  assert (HJ3 : ajournalA CM_STK (spZ regs) [] lyc Sc W memc mdc [(CM_CID, pos)] lyc S2 W m2 md2' 0).
  { apply (ajournal_exec segs B LAWS cmw_segs_low CM_STK (spZ regs) [] lyc Sc W memc mdc
             [(CM_CID, pos)] lyc S2 W mem2 md2 0 m2 md2'
             (fun a => (spZ regs - 144 <= a < spZ regs) \/ (FA <= a < FA + 24) \/
                       (AC.shadow_addr FA <= a < AC.shadow_addr FA + 8)) HJ2).
    - intros x Hx. unfold mrestrict. rewrite (MU2 x); [reflexivity|].
      destruct (HDEC (bv_unsigned x)) as [R1 | [R2 | [R3 | R4]]];
        [exfalso; apply Hx; left; lia | exfalso; apply Hx; right; left; lia
        | exfalso; apply Hx; right; right; lia | exact R4].
    - apply (cmw_mem_grows W mem2 m2 WM2). intros x.
      destruct (HDEC (bv_unsigned x)) as [R1 | [R2 | [R3 | R4]]].
      + right. split; [apply Hpres2; lia | apply HNIW; lia].
      + right. split; [apply Hfpres; lia | apply HNIF; lia].
      + right. split; [apply HSHP; lia | apply HNIS; lia].
      + left. exact (MU2 x R4).
    - intros x Hx.
      destruct (HDEC (bv_unsigned x)) as [R1 | [R2 | [R3 | R4]]]; [| | | exact (MU2 x R4)].
      + exfalso. pose proof (proj1 (Hpres2 (bv_unsigned x) ltac:(lia))) as Hh.
        rewrite Z_to_bv_bv_unsigned in Hh. congruence.
      + exfalso. pose proof (proj1 (Hfpres (bv_unsigned x) ltac:(lia))) as Hh.
        rewrite Z_to_bv_bv_unsigned in Hh. congruence.
      + exfalso. pose proof (proj1 (HSHP (bv_unsigned x) ltac:(lia))) as Hh.
        rewrite Z_to_bv_bv_unsigned in Hh. congruence.
    - exact SBM2.
    - intros a [Ha | [Ha | Ha]].
      + left. lia.
      + right. right. right. exists CM_CID, pos. split; [left; reflexivity|].
        left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes CM_CID) with 64. lia.
      + right. right. right. exists CM_CID, pos. split; [left; reflexivity|].
        right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes CM_CID / 8) with 8.
        unfold AC.shadow_addr, AC.ASAN_K in Ha. unfold shadow_addr, SHADOW_OFF. lia. }
  assert (Q3 : YK11.getr regs2 (Z_to_bv 5 3) = w64 (as_gp B)).
  { etransitivity; [exact (HP2 3 ltac:(unfold acallee_saved; lia))|]. etransitivity; [exact E3 | exact Hgp]. }
  assert (Q4 : YK11.getr regs2 (Z_to_bv 5 4) = w64 (as_tp B)).
  { etransitivity; [exact (HP2 4 ltac:(unfold acallee_saved; lia))|]. etransitivity; [exact E4 | exact Htp]. }
  assert (Q27 : YK11.getr regs2 (Z_to_bv 5 27) = YK11.getr regs (Z_to_bv 5 27))
    by (etransitivity; [exact (HP2 27 ltac:(unfold acallee_saved; lia)) | exact E27]).
  change (mkCfg (YK11.mkst (ms_regs ms2') (Z_to_bv 64 525376) m2 (YK11.seg_rom segs)) md2')
    with (@cfg_at fx segs 525376 (ms_regs ms2') m2 md2').
  (* both arms of the length test reach 0x804e0 with the offset in s9 and the meter test in s10 *)
  enough (HJOIN : forall (regs3 : bvmap 5 word) (md3 : Model),
      same_but_materialized md2' md3 ->
      YK11.getr regs3 (Z_to_bv 5 3)  = w64 (as_gp B) ->
      YK11.getr regs3 (Z_to_bv 5 4)  = w64 (as_tp B) ->
      YK11.getr regs3 (Z_to_bv 5 27) = YK11.getr regs (Z_to_bv 5 27) ->
      YK11.getr regs3 (Z_to_bv 5 2)  = Z_to_bv 64 SP1 ->
      YK11.getr regs3 (Z_to_bv 5 8)  = Z_to_bv 64 (spZ regs) ->
      YK11.getr regs3 (Z_to_bv 5 9)  = Z_to_bv 64 SP1 ->
      YK11.getr regs3 (Z_to_bv 5 18) = Z_to_bv 64 FA ->
      YK11.getr regs3 (Z_to_bv 5 19) = Z_to_bv 64 f ->
      YK11.getr regs3 (Z_to_bv 5 20) = Z_to_bv 64 n ->
      YK11.getr regs3 (Z_to_bv 5 22) = Z_to_bv 64 FA ->
      YK11.getr regs3 (Z_to_bv 5 23) = Z_to_bv 64 (AC.shadow_addr FA) ->
      YK11.getr regs3 (Z_to_bv 5 24) = Z_to_bv 64 AC.ASAN_K ->
      YK11.getr regs3 (Z_to_bv 5 25) = Z_to_bv 64 (Z.of_nat (PMC.meter_eo n bs)) ->
      YK11.getr regs3 (Z_to_bv 5 26) = Z_to_bv 64 (if PMC.meter_ok n bs then 1 else 0) ->
      SRr segs W (@cfg_at fx segs 525536 regs3 m2 md3) POST).
  { destruct (Z_lt_le_dec n 14) as [Hn14 | Hn14].
    - (* n < 14: the length test is taken, the offset is 12 and the meter test is false *)
      assert (EO12 : PMC.meter_eo n bs = 12%nat) by (apply PCM.meter_eo_12; left; lia).
      assert (OKF : PMC.meter_ok n bs = false) by (apply PCM.meter_ok_short; lia).
      eapply (@cmw_run fx W (ms_regs ms2') m2 md2' 525376).
      { unfold LCK.ms_of_regs. rewrite G10, G20. apply cm_seg3_F. lia. }
      intros ms3' md3' (ms03 & -> & EQV3) SBM3.
      rewrite (cmw_ms_shape _ _ _ _ EQV3).
      destruct (cmw_regs_of EQV3) as (K1 & K2 & K3 & K4 & K8 & K9 & K10 & K11 & K12 & K18 & K19 & K20 & K21 &
        K22 & K23 & K24 & K25 & K26 & K27).
      change (mkCfg (YK11.mkst (ms_regs ms3') (Z_to_bv 64 525536) m2 (YK11.seg_rom segs)) md3')
        with (@cfg_at fx segs 525536 (ms_regs ms3') m2 md3').
      apply HJOIN; rewrite ?EO12, ?OKF.
      + exact SBM3.
      + etransitivity; [exact K3|]. etransitivity; [exact G3 | exact Q3].
      + etransitivity; [exact K4|]. etransitivity; [exact G4 | exact Q4].
      + etransitivity; [exact K27|]. etransitivity; [exact G27 | exact Q27].
      + etransitivity; [exact K2 | exact G2].
      + etransitivity; [exact K8 | exact G8].
      + etransitivity; [exact K9 | exact G9].
      + etransitivity; [exact K18 | exact G18].
      + etransitivity; [exact K19 | exact G19].
      + exact K20.
      + etransitivity; [exact K22 | exact G22].
      + etransitivity; [exact K23 | exact G23].
      + etransitivity; [exact K24 | exact G24].
      + exact K25.
      + exact K26.
    - (* 14 <= n: f[12] and f[13] fix the offset, then the meter test *)
      destruct (Hblk ltac:(lia)) as (bA & nA & HbA & Hb1 & Hb2).
      pose proof cmw_nrng as (_ & Hn47' & Hfn'). destruct (Hfn' ltac:(lia)) as [Hf0 Hf47].
      assert (HBY : bytes_at AImg.rsegs m2 f bs)
        by (apply (cmw_bytes_keep [(CM_CID, pos)] lyc S2 W m2 md2' 0 bA nA HJ3 HbA
                     ltac:(rewrite Eab2; exact HbA) Hb1 Hb2 ltac:(lia))).
      pose proof (proj1 HJ3) as HAR3.
      assert (HBI : In (bA, nA) (ablocks B lyc S2)) by (rewrite Eab2; exact HbA).
      assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia).
      assert (HLEN14 : (14 <= length bs)%nat) by lia.
      eapply (@cmw_run fx W (ms_regs ms2') m2 md2' 525376).
      { unfold LCK.ms_of_regs. rewrite G10, G19, G20, G24.
        eapply cm_seg4_F with (f := f) (n := n) (bs := bs);
        [ lia | exact HLEN14 | exact HBY
        | eapply (WL.wcc_leafb_addressable_block B LAWS lyc S2 W m2 md2' bA nA); [exact HAR3 | exact HBI | lia | lia | lia]
        | lia | lia
        | eapply (WL.wcc_leafb_rng_block B LAWS lyc S2 W m2 md2' bA nA); [exact HAR3 | exact HBI | lia | lia]
        | eapply (WL.wcc_leafb_rng_shadow_block B LAWS lyc S2 W m2 md2' bA nA);
          [exact HAR3 | exact HBI | lia | lia | lia] ]. }
      intros ms4' md4' (ms04 & (b0 & b1 & b2 & ->) & EQV4) SBM4.
      rewrite (cmw_ms_shape _ _ _ _ EQV4).
      destruct (cmw_regs_of EQV4) as (L1 & L2 & L3 & L4 & L8 & L9 & L10 & L11 & L12 & L18 & L19 & L20 & L21 &
        L22 & L23 & L24 & L25 & L26 & L27).
      change (mkCfg (YK11.mkst (ms_regs ms4') (Z_to_bv 64 525444) m2 (YK11.seg_rom segs)) md4')
        with (@cfg_at fx segs 525444 (ms_regs ms4') m2 md4').
      eapply (@cmw_run fx W (ms_regs ms4') m2 md4' 525444).
      { unfold LCK.ms_of_regs. rewrite L19, L20, L24, L25.
        eapply cm_seg5_F with (f := f) (n := n) (bs := bs);
        [ lia | intros ?; lia | exact HBY
        | intros ?; eapply (WL.wcc_leafb_addressable_block B LAWS lyc S2 W m2 md2' bA nA);
          [exact HAR3 | exact HBI | lia | lia | lia]
        | lia | lia
        | intros ?; eapply (WL.wcc_leafb_rng_block B LAWS lyc S2 W m2 md2' bA nA); [exact HAR3 | exact HBI | lia | lia]
        | intros ?; eapply (WL.wcc_leafb_rng_shadow_block B LAWS lyc S2 W m2 md2' bA nA);
          [exact HAR3 | exact HBI | lia | lia | lia] ]. }
      intros ms5' md5' (ms05 & (c0 & c1 & c2 & ->) & EQV5) SBM5.
      rewrite (cmw_ms_shape _ _ _ _ EQV5).
      destruct (cmw_regs_of EQV5) as (M1 & M2 & M3 & M4 & M8 & M9 & M10 & M11 & M12 & M18 & M19 & M20 & M21 &
        M22 & M23 & M24 & M25 & M26 & M27).
      change (mkCfg (YK11.mkst (ms_regs ms5') (Z_to_bv 64 525536) m2 (YK11.seg_rom segs)) md5')
        with (@cfg_at fx segs 525536 (ms_regs ms5') m2 md5').
      apply HJOIN.
      + eapply same_but_materialized_trans; [exact SBM4 | exact SBM5].
      + etransitivity; [exact M3|]. etransitivity; [exact L3|]. etransitivity; [exact G3 | exact Q3].
      + etransitivity; [exact M4|]. etransitivity; [exact L4|]. etransitivity; [exact G4 | exact Q4].
      + etransitivity; [exact M27|]. etransitivity; [exact L27|]. etransitivity; [exact G27 | exact Q27].
      + etransitivity; [exact M2|]. etransitivity; [exact L2 | exact G2].
      + etransitivity; [exact M8|]. etransitivity; [exact L8 | exact G8].
      + etransitivity; [exact M9|]. etransitivity; [exact L9 | exact G9].
      + etransitivity; [exact M18|]. etransitivity; [exact L18 | exact G18].
      + exact M19.
      + exact M20.
      + etransitivity; [exact M22|]. etransitivity; [exact L22 | exact G22].
      + etransitivity; [exact M23|]. etransitivity; [exact L23 | exact G23].
      + exact M24.
      + exact M25.
      + exact M26. }
  intros regs3 md3 SBM3 N3 N4 N27 N2 N8 N9 N18 N19 N20 N22 N23 N24 N25 N26.
  set (EO := Z.of_nat (PMC.meter_eo n bs)) in *.
  set (WANT := if PMC.meter_ok n bs then 1 else 0) in *.
  (* 0x804e0 .. 0x80504: the local counter set to 0xa5c3, its shadow byte to 2, the three arguments *)
  eapply (@cmw_run fx W regs3 m2 md3 525536).
  { unfold LCK.ms_of_regs. rewrite N2, N8, N9, N18, N19, N20, N22, N23, N24, N25, N26.
    eapply cm_seg6_F with (SP := spZ regs) (SP1 := SP1) (FA := FA) (f := f) (n := n) (eo := EO) (want := WANT);
    [ unfold SP1 in *; lia | lia | lia | lia | lia | exact HDF | exact HDS | exact HD
    | exact FRF2 | exact FRS2 | exact RFF | exact RFS ]. }
  intros ms6' md6' (ms06 & (m6 & jF6 & jsh6 & -> & MU6 & WM6 & FRF6 & FRS6 & SH6 & CT6) & EQV6) SBM6.
  destruct (cmw_regs_of EQV6) as (P1 & P2 & P3 & P4 & P8 & P9 & P10 & P11 & P12 & P18 & P19 & P20 & P21 & P22 &
    P23 & P24 & P25 & P26 & P27).
  rewrite (cmw_ms_shape _ _ _ _ EQV6).
  assert (HPF2 : forall a, FA <= a < FA + 64 -> apresent (w_H W) m2 a)
    by (intros a Ha; apply (cmw_pres_after W mem2 m2 a WM2); [apply Hfpres; lia | apply HNIF; lia | lia]).
  assert (HPS2 : forall a, AC.shadow_addr FA <= a < AC.shadow_addr FA + 8 -> apresent (w_H W) m2 a)
    by (intros a Ha; apply (cmw_pres_after W mem2 m2 a WM2);
        [apply HSHP; lia | apply HNIS; lia | unfold AC.shadow_addr in *; lia]).
  assert (HDEC6 : forall a : Z,
    (FA + 32 <= a < FA + 34) \/ (AC.shadow_addr FA <= a < AC.shadow_addr FA + 8) \/
    outside [(FA + 32, FA + 34); (AC.shadow_addr FA, AC.shadow_addr FA + 8)] a).
  { intros a. cbn [outside fst snd].
    destruct (Z_lt_ge_dec a (FA + 32)) as [?|?]; destruct (Z_lt_ge_dec a (FA + 34)) as [?|?];
    destruct (Z_lt_ge_dec a (AC.shadow_addr FA)) as [?|?];
    destruct (Z_lt_ge_dec a (AC.shadow_addr FA + 8)) as [?|?];
    try (left; lia); try (right; left; lia);
    right; right; repeat split; try exact I; lia. }
  (* the inner journal after the counter and its shadow byte *)
  assert (HJ6 : ajournalA CM_STK (spZ regs) [] lyc Sc W memc mdc [(CM_CID, pos)] lyc S2 W m6 md6' 0).
  { apply (ajournal_exec segs B LAWS cmw_segs_low CM_STK (spZ regs) [] lyc Sc W memc mdc
             [(CM_CID, pos)] lyc S2 W m2 md2' 0 m6 md6'
             (fun a => (FA + 32 <= a < FA + 34) \/ (AC.shadow_addr FA <= a < AC.shadow_addr FA + 8)) HJ3).
    - intros x Hx. unfold mrestrict. rewrite (MU6 x); [reflexivity|].
      destruct (HDEC6 (bv_unsigned x)) as [R1 | [R2 | R3]];
        [exfalso; apply Hx; left; lia | exfalso; apply Hx; right; lia | exact R3].
    - apply (cmw_mem_grows W m2 m6 WM6). intros x.
      destruct (HDEC6 (bv_unsigned x)) as [R1 | [R2 | R3]].
      + right. split; [apply HPF2; lia | apply HNIF; lia].
      + right. split; [apply HPS2; lia | apply HNIS; lia].
      + left. exact (MU6 x R3).
    - intros x Hx.
      destruct (HDEC6 (bv_unsigned x)) as [R1 | [R2 | R3]]; [| | exact (MU6 x R3)].
      + exfalso. pose proof (proj1 (HPF2 (bv_unsigned x) ltac:(lia))) as Hh.
        rewrite Z_to_bv_bv_unsigned in Hh. congruence.
      + exfalso. pose proof (proj1 (HPS2 (bv_unsigned x) ltac:(lia))) as Hh.
        rewrite Z_to_bv_bv_unsigned in Hh. congruence.
    - eapply same_but_materialized_trans; [exact SBM3 | exact SBM6].
    - intros a [Ha | Ha].
      + right. right. right. exists CM_CID, pos. split; [left; reflexivity|].
        left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes CM_CID) with 64. lia.
      + right. right. right. exists CM_CID, pos. split; [left; reflexivity|].
        right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes CM_CID / 8) with 8.
        unfold AC.shadow_addr, AC.ASAN_K in Ha. unfold shadow_addr, SHADOW_OFF. lia. }
  (* the frame's bytes at the state the leaf is called from *)
  pose proof (proj1 HJ6) as HAR6.
  assert (HPF6 : forall a, FA <= a < FA + 64 -> apresent (w_H W) m6 a)
    by (intros a Ha; apply (cmw_pres_after W m2 m6 a WM6); [apply HPF2; lia | apply HNIF; lia | lia]).
  assert (HAPPF : forall a, FA <= a < FA + 64 -> AC.app_mem a).
  { intros a Ha. destruct HFapp as (_ & [HL | [HH HE]]);
    [left; unfold kLowShadowBeg in HL; unfold AC.LOWMEM_END; lia
    | right; unfold kHighMemBeg in HH; unfold AC.HIGHMEM_BEG, AC.APPMEM_END;
      pose proof (@YG0f.ASAN_CEIL_range rc) as [? ?]; unfold YG0f.ASAN_CEIL in *; lia]. }
  assert (HAD32 : AC.addressable m6 (FA + 32) 2).
  { split; [lia|]. split; [lia|]. split; [unfold AC.APPMEM_END; lia|].
    intros i Hi. split; [apply HAPPF; lia|].
    exists (Z_to_bv 8 2). split.
    - replace (AC.shadow_addr (FA + 32 + i)) with (AC.shadow_addr FA + 4 + Z.of_nat 0)
        by (unfold AC.shadow_addr; Z.div_mod_to_equations; lia).
      exact (AsanKAProof.bytes_nth m6 (AC.shadow_addr FA + 4) [Z_to_bv 8 2] 0 SH6 ltac:(cbn; lia)).
    - unfold AC.shadow_ok. right. change (bv_signed (Z_to_bv 8 2)) with 2.
      split; [|lia]. replace ((FA + 32 + i) mod 8) with i by (Z.div_mod_to_equations; lia). lia. }
  assert (UA1 : bv_unsigned (YK11.getr (ms_regs ms6') (Z_to_bv 5 11)) = n)
    by (rewrite P11; apply cmw_u64; lia).
  assert (UA2 : bv_unsigned (YK11.getr (ms_regs ms6') (Z_to_bv 5 12)) = FA + 32)
    by (rewrite P12; apply cmw_u64; lia).
  assert (USP6 : bv_unsigned (YK11.getr (ms_regs ms6') (Z_to_bv 5 2)) = SP1)
    by (rewrite P2; apply cmw_u64; unfold SP1 in *; lia).
  assert (HF14 : 14 <= n -> bv_unsigned (YK11.getr (ms_regs ms6') (Z_to_bv 5 10)) = f).
  { intros H14. rewrite P10. apply cmw_u64. destruct (Hfn ltac:(lia)). lia. }
  assert (HBY6 : 0 < n -> bytes_at AImg.rsegs m6 f bs).
  { intros Hpos. destruct (Hblk Hpos) as (bA & nA & HbA & Hb1 & Hb2).
    exact (cmw_bytes_keep [(CM_CID, pos)] lyc S2 W m6 md6' 0 bA nA HJ6 HbA
             ltac:(rewrite Eab2; exact HbA) Hb1 Hb2 Hpos). }
  assert (HBLK6 : 14 <= n -> exists bA nA, In (bA, nA) (ablocks B lyc S2) /\ bA <= f /\ f + n <= bA + nA).
  { intros H14. destruct (Hblk ltac:(lia)) as (bA & nA & HbA & Hb1 & Hb2).
    exists bA, nA. split; [rewrite Eab2; exact HbA | split; [exact Hb1 | exact Hb2]]. }
  (* 0x80504: the leaf rp_meter_counter *)
  eapply SRr_bind.
  { eapply (WL.wcc_leafb_journal B LAWS W (ms_regs ms6') m6 CM_STK (spZ regs) (@nil (Z * Z)) lyc Sc W memc mdc
      [(CM_CID, pos)] lyc S2 md6' 0 (SP1 - spZ regs) 528744
      (Some (if PMC.meter_ok n bs then 1 else 0)) (LMC.wire_rmc_wr n bs (FA + 32))
      (fun m2 => PMC.meter_ok n bs = true ->
         bytes_at AImg.rsegs m2 (FA + 32) (le2 (Z_to_bv 64 (PMC.meter_value n bs)))) HJ6).
    - replace (spZ (ms_regs ms6')) with (bv_unsigned (YK11.getr (ms_regs ms6') (Z_to_bv 5 2))) by reflexivity.
      rewrite USP6. lia.
    - exact HOM.
    - unfold SP1 in *; lia.
    - unfold SP1 in *; lia.
    - assert (RO : YK0s.ret_ok (Z_to_bv 64 525576)) by (apply YK0s.ret_ok_even; reflexivity).
      exact (eq_ind_r (fun x => YK0s.ret_ok x) RO P1).
    - etransitivity; [exact P3 | exact N3].
    - etransitivity; [exact P4 | exact N4].
    - intros a Ha. pose proof (cmw_in_wr n bs (FA + 32) a Ha) as Hr.
      right. right. right. exists CM_CID, pos. split; [left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes CM_CID) with 64. lia.
    - intros HPRE.
      pose proof (LEAF fx lyc S2 W (ms_regs ms6') m6 md6' bs (spZ regs - CM_STK) HPRE) as HL.
      cbv zeta in HL. rewrite UA1, UA2 in HL. apply HL; clear HL.
      + intros H14. rewrite (HF14 H14). split; [lia | exact (HBY6 ltac:(lia))].
      + intros H1000. lia.
      + intros Hok. apply (WL.wcc_leafb_wr_at W m6); [lia | lia |]. intros i Hi. apply HPF6. lia.
      + rewrite USP6. eapply (WL.wcc_leafb_stk_journal B); [exact HJ6 | lia | unfold SP1 in *; lia].
      + rewrite USP6. unfold AMC.RP_METER_COUNTER_FRAME. unfold SP1 in *; lia.
      + intros H14. rewrite (HF14 H14). unfold AsanKA.off_stk, AMC.RP_METER_COUNTER_FRAME. rewrite USP6.
        left. destruct (HBLK6 H14) as (bA & nA & HbA & Hb1 & Hb2).
        destruct (al_blocks _ _ LAWS lyc S2 W m6 md6' bA nA HAR6 HbA) as (_ & _ & Hceil & _ & _ & _ & _).
        assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia).
        unfold SP1 in *; lia.
      + intros H1000. rewrite (HF14 ltac:(lia)). unfold AsanKA.off_stk, AMC.RP_METER_COUNTER_FRAME. rewrite USP6.
        left. destruct (HBLK6 ltac:(lia)) as (bA & nA & HbA & Hb1 & Hb2).
        destruct (al_blocks _ _ LAWS lyc S2 W m6 md6' bA nA HAR6 HbA) as (_ & _ & Hceil & _ & _ & _ & _).
        assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia).
        unfold SP1 in *; lia.
      + intros Hok. unfold AsanKA.off_stk, AMC.RP_METER_COUNTER_FRAME. rewrite USP6. left. unfold SP1 in *; lia.
      + rewrite USP6. unfold AMC.RP_METER_COUNTER_FRAME. apply WL.wcc_leafb_app_stack. unfold SP1 in *; lia.
      + rewrite USP6. apply WL.wcc_leafb_app_stack. unfold SP1 in *; lia.
      + exact (WL.wcc_leafb_asan_cells B HCELLS lyc S2 W m6 md6' HAR6).
      + unfold AsanKA.off_stk, AMC.RP_METER_COUNTER_FRAME, AC.GOT_CELL_K. rewrite USP6. left. unfold SP1 in *; lia.
      + unfold AsanKA.off_stk, AMC.RP_METER_COUNTER_FRAME, AC.CELL_K. rewrite USP6. left. unfold SP1 in *; lia.
      + intros H14. rewrite (HF14 H14). destruct (HBLK6 H14) as (bA & nA & HbA & Hb1 & Hb2).
        eapply (WL.wcc_leafb_addressable_block B LAWS lyc S2 W m6 md6' bA nA);
          [exact HAR6 | exact HbA | lia | lia |].
        assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia). lia.
      + intros H1000. rewrite (HF14 ltac:(lia)). destruct (HBLK6 ltac:(lia)) as (bA & nA & HbA & Hb1 & Hb2).
        eapply (WL.wcc_leafb_addressable_block B LAWS lyc S2 W m6 md6' bA nA);
          [exact HAR6 | exact HbA | lia | lia |].
        assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia). lia.
      + intros Hok. exact HAD32.
      + rewrite USP6. unfold AMC.RP_METER_COUNTER_FRAME.
        eapply (WL.wcc_leafb_rng_journal B); [exact HJ6 | unfold SP1 in *; lia | unfold SP1 in *; lia].
      + exact (proj1 (WL.wcc_leafb_rng_cells W)).
      + exact (proj2 (WL.wcc_leafb_rng_cells W)).
      + intros H14. rewrite (HF14 H14). destruct (HBLK6 H14) as (bA & nA & HbA & Hb1 & Hb2).
        eapply (WL.wcc_leafb_rng_block B LAWS lyc S2 W m6 md6' bA nA); [exact HAR6 | exact HbA | lia |].
        assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia). lia.
      + intros H14. rewrite (HF14 H14). destruct (HBLK6 H14) as (bA & nA & HbA & Hb1 & Hb2).
        eapply (WL.wcc_leafb_rng_shadow_block B LAWS lyc S2 W m6 md6' bA nA);
          [exact HAR6 | exact HbA | lia | lia |].
        assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia). lia.
      + intros H1000. rewrite (HF14 ltac:(lia)). destruct (HBLK6 ltac:(lia)) as (bA & nA & HbA & Hb1 & Hb2).
        eapply (WL.wcc_leafb_rng_block B LAWS lyc S2 W m6 md6' bA nA); [exact HAR6 | exact HbA | lia |].
        assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia). lia.
      + intros H1000. rewrite (HF14 ltac:(lia)). destruct (HBLK6 ltac:(lia)) as (bA & nA & HbA & Hb1 & Hb2).
        eapply (WL.wcc_leafb_rng_shadow_block B LAWS lyc S2 W m6 md6' bA nA);
          [exact HAR6 | exact HbA | lia | lia |].
        assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia). lia.
      + intros Hok. apply (WL.wcc_leafb_rng_vis W m6); [lia | lia |]. intros a Ha. apply HPF6. lia.
      + intros Hok. apply (WL.wcc_leafb_rng_vis W m6);
          [unfold AC.shadow_addr; lia | unfold AC.shadow_addr; lia |].
        intros a Ha. apply (cmw_pres_after W m2 m6 a WM6);
          [apply HPS2; unfold AC.shadow_addr in *; Z.div_mod_to_equations; lia
          | apply HNIS; unfold AC.shadow_addr in *; Z.div_mod_to_equations; lia
          | unfold AC.shadow_addr in *; lia].
      + intros x Hx. pose proof (cmw_in_wr n bs (FA + 32) x Hx) as Hr.
        destruct (al_frames _ _ LAWS lyc S2 W m6 md6' CM_CID pos HAR6 Hin2) as (_ & _ & HFb6 & _).
        change (fs_frame_bytes CM_CID) with 64 in HFb6.
        split; [exact (proj2 (HFb6 x ltac:(lia))) | apply HNIF; lia]. }
  cbv beta. intros W3 c3 _ (-> & regs7 & m7 & md7 & -> & HJ7 & HP7 & HRES & HEFF & HGR & HX).
  pose proof (proj1 HJ7) as HAR7.
  assert (EPC7 : YK11.getr (ms_regs ms6') 1 = Z_to_bv 64 525576) by exact P1.
  rewrite EPC7.
  change (mkCfg (YK11.mkst regs7 (Z_to_bv 64 525576) m7 (YK11.seg_rom segs)) md7)
    with (@cfg_at fx segs 525576 regs7 m7 md7).
  assert (HPF7 : forall a, FA <= a < FA + 64 -> apresent (w_H W) m7 a)
    by (intros a Ha; apply HGR; apply HPF6; lia).
  assert (HPS6 : forall a, AC.shadow_addr FA <= a < AC.shadow_addr FA + 8 -> apresent (w_H W) m6 a)
    by (intros a Ha; apply (cmw_pres_after W m2 m6 a WM6);
        [apply HPS2; lia | apply HNIS; lia | unfold AC.shadow_addr in *; lia]).
  assert (HPS7 : forall a, AC.shadow_addr FA <= a < AC.shadow_addr FA + 8 -> apresent (w_H W) m7 a)
    by (intros a Ha; apply HGR; apply HPS6; lia).
  assert (HWIN6 : forall a, spZ regs - CM_STK <= a < spZ regs -> apresent (w_H W) m6 a).
  { intros a Ha. destruct HJ6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp6 & _). apply Hp6. lia. }
  (* the counter, read back after the call *)
  assert (CT7 : bytes_at AImg.rsegs m7 (FA + 32)
                  (if PMC.meter_ok n bs then le2 (Z_to_bv 64 (PMC.meter_value n bs))
                   else le2 (Z_to_bv 64 42435))).
  { destruct (PMC.meter_ok n bs) eqn:Hok; [exact (HX eq_refl)|].
    apply (cmw_bytes_ext m6 m7 (FA + 32) (le2 (Z_to_bv 64 42435)) CT6). intros x Hx.
    rewrite length_le2 in Hx. unfold wa.
    apply (cmw_byte_eq (w_H W) (w_H W) m6 m7 x); [apply HPF6; lia | apply HPF7; lia|].
    apply HEFF; [lia | | ].
    - replace (spZ (ms_regs ms6')) with (bv_unsigned (YK11.getr (ms_regs ms6') (Z_to_bv 5 2))) by reflexivity.
      rewrite USP6. unfold ESTACK, SP1 in *. lia.
    - intros Hw. pose proof (cmw_in_wr n bs (FA + 32) x Hw) as Hr.
      unfold LCK.in_wr, LMC.wire_rmc_wr in Hw. rewrite Hok in Hw. inversion Hw. }
  assert (BY7 : 0 < n -> bytes_at AImg.rsegs m7 f bs).
  { intros Hpos. destruct (Hblk Hpos) as (bA & nA & HbA & Hb1 & Hb2).
    exact (cmw_bytes_keep [(CM_CID, pos)] lyc S2 W m7 md7 0 bA nA HJ7 HbA
             ltac:(rewrite Eab2; exact HbA) Hb1 Hb2 Hpos). }
  (* the registers the leaf kept, and the result it returned *)
  assert (R10 : YK11.getr regs7 (Z_to_bv 5 10) = Z_to_bv 64 (if PMC.meter_ok n bs then 1 else 0))
    by exact (HRES _ eq_refl).
  assert (R19 : YK11.getr regs7 (Z_to_bv 5 19) = Z_to_bv 64 f)
    by (etransitivity; [exact (HP7 19 ltac:(unfold acallee_saved; lia)) | exact P19]).
  assert (R20 : YK11.getr regs7 (Z_to_bv 5 20) = Z_to_bv 64 n)
    by (etransitivity; [exact (HP7 20 ltac:(unfold acallee_saved; lia)) | exact P20]).
  assert (R21 : YK11.getr regs7 (Z_to_bv 5 21) = Z_to_bv 64 (FA + 32))
    by (etransitivity; [exact (HP7 21 ltac:(unfold acallee_saved; lia)) | exact P21]).
  assert (R24 : YK11.getr regs7 (Z_to_bv 5 24) = Z_to_bv 64 AC.ASAN_K)
    by (etransitivity; [exact (HP7 24 ltac:(unfold acallee_saved; lia)) | exact P24]).
  assert (R25 : YK11.getr regs7 (Z_to_bv 5 25) = Z_to_bv 64 EO)
    by (etransitivity; [exact (HP7 25 ltac:(unfold acallee_saved; lia)) | exact P25]).
  assert (R26 : YK11.getr regs7 (Z_to_bv 5 26) = Z_to_bv 64 WANT)
    by (etransitivity; [exact (HP7 26 ltac:(unfold acallee_saved; lia)) | exact P26]).
  assert (R2 : YK11.getr regs7 (Z_to_bv 5 2) = Z_to_bv 64 SP1)
    by (etransitivity; [exact (HP7 2 ltac:(unfold acallee_saved; lia)) | exact P2]).
  assert (R8 : YK11.getr regs7 (Z_to_bv 5 8) = Z_to_bv 64 (spZ regs))
    by (etransitivity; [exact (HP7 8 ltac:(unfold acallee_saved; lia)) | exact P8]).
  assert (R9 : YK11.getr regs7 (Z_to_bv 5 9) = Z_to_bv 64 SP1)
    by (etransitivity; [exact (HP7 9 ltac:(unfold acallee_saved; lia)) | exact P9]).
  assert (R18 : YK11.getr regs7 (Z_to_bv 5 18) = Z_to_bv 64 FA)
    by (etransitivity; [exact (HP7 18 ltac:(unfold acallee_saved; lia)) | exact P18]).
  assert (R22 : YK11.getr regs7 (Z_to_bv 5 22) = Z_to_bv 64 FA)
    by (etransitivity; [exact (HP7 22 ltac:(unfold acallee_saved; lia)) | exact P22]).
  assert (R23 : YK11.getr regs7 (Z_to_bv 5 23) = Z_to_bv 64 (AC.shadow_addr FA))
    by (etransitivity; [exact (HP7 23 ltac:(unfold acallee_saved; lia)) | exact P23]).
  (* 0x80508 .. 0x80568: the result and the counter tests *)
  eapply (@cmw_run fx W regs7 m7 md7 525576).
  { unfold LCK.ms_of_regs. rewrite R10, R19, R20, R21, R24, R25, R26.
    eapply cm_seg7_F with (f := f) (n := n) (ctr := FA + 32) (bs := bs);
    [ lia | intros ?; lia | intros ?; exact (BY7 ltac:(lia))
    | intros H1000; destruct (Hblk ltac:(lia)) as (bA & nA & HbA & Hb1 & Hb2);
      eapply (WL.wcc_leafb_addressable_block B LAWS lyc S2 W m7 md7 bA nA);
        [exact HAR7 | rewrite Eab2; exact HbA | lia | lia |
         assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia); lia]
    | intros H1000; destruct (Hfn ltac:(lia)); split; lia
    | lia | lia
    | intros H1000; destruct (Hblk ltac:(lia)) as (bA & nA & HbA & Hb1 & Hb2);
      eapply (WL.wcc_leafb_rng_block B LAWS lyc S2 W m7 md7 bA nA);
        [exact HAR7 | rewrite Eab2; exact HbA | lia |
         assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia); lia]
    | intros H1000; destruct (Hblk ltac:(lia)) as (bA & nA & HbA & Hb1 & Hb2);
      eapply (WL.wcc_leafb_rng_shadow_block B LAWS lyc S2 W m7 md7 bA nA);
        [exact HAR7 | rewrite Eab2; exact HbA | lia | lia |
         assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia); lia]
    | apply (WL.wcc_leafb_rng_vis W m7); [lia | lia |]; intros a Ha; apply HPF7; lia
    | exact CT7 ]. }
  intros ms7' md7' (ms07 & (a0' & a1' & a2' & a3' & a4' & ->) & EQV7) SBM7.
  rewrite (cmw_ms_shape _ _ _ _ EQV7).
  destruct (cmw_regs_of EQV7) as (T1 & T2 & T3 & T4 & T8 & T9 & T10 & T11 & T12 & T18 & T19 & T20 & T21 & T22 &
    T23 & T24 & T25 & T26 & T27).
  change (mkCfg (YK11.mkst (ms_regs ms7') (Z_to_bv 64 525672) m7 (YK11.seg_rom segs)) md7')
    with (@cfg_at fx segs 525672 (ms_regs ms7') m7 md7').
  (* the frame's flag byte *)
  set (FL := flag_addr lyc CM_CID pos) in *.
  destruct (FFL lyc S2 W m7 md7 CM_CID pos HAR7 Hin2) as (HFLp & HFLo & (HFLapp & HFLimg) & HFL0 & HFLz & HFLc).
  assert (HFLnc : ~ aclient_byte B lyc S2 FL) by exact (proj2 HFLo).
  assert (HDL : FL + 1 <= FA \/ FA + 64 <= FL).
  { destruct (Z_lt_le_dec FL FA) as [L|L]; [lia|]. destruct (Z_lt_le_dec FL (FA + 64)) as [L2|L2]; [|lia].
    exfalso. apply HFLnc. right. exists (CM_CID, pos). split; [exact Hin2|].
    left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes CM_CID) with 64. lia. }
  assert (HDLS : FL + 1 <= AC.shadow_addr FA \/ AC.shadow_addr FA + 8 <= FL).
  { destruct (Z_lt_le_dec FL (AC.shadow_addr FA)) as [L|L]; [lia|].
    destruct (Z_lt_le_dec FL (AC.shadow_addr FA + 8)) as [L2|L2]; [|lia].
    exfalso. apply HFLnc. right. exists (CM_CID, pos). split; [exact Hin2|].
    right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes CM_CID / 8) with 8.
    unfold AC.shadow_addr, AC.ASAN_K in L, L2. unfold shadow_addr, SHADOW_OFF. lia. }
  (* the word the prologue's callee left at frame + 56: the flag pointer *)
  assert (BFL7 : bytes_at AImg.rsegs m7 (FA + 56) (le8 (wa FL))).
  { assert (BFL2 : bytes_at AImg.rsegs mem2 (FA + 56) (le8 (wa FL))).
    { assert (ELE : le8 (wa FL) = Z_to_le_bytes 8 FL)
        by (unfold le8, word_to_le_bytes, wa; rewrite cmw_u64 by lia; reflexivity).
      rewrite ELE.
      replace (FA + 56) with (FA + 64 - 8) by lia.
      eapply (WL.wcc_leafb_bytes_le W mem2 (FA + 64 - 8) 8 FL FL);
        [ exact (val_mem_of_rdword segs (w_H W) mem2 _ _ Hflag) | reflexivity | lia | lia ]. }
    assert (BFL2' : bytes_at AImg.rsegs m2 (FA + 56) (le8 (wa FL))).
    { apply (cmw_bytes_ext mem2 m2 _ _ BFL2). intros x Hx. rewrite length_le8 in Hx.
      apply (MU2 (wa x)). unfold wa. rewrite cmw_u64 by lia.
      cbn [outside fst snd]. unfold AC.shadow_addr, AC.ASAN_K in *.
      repeat split; try exact I; lia. }
    assert (BFL6 : bytes_at AImg.rsegs m6 (FA + 56) (le8 (wa FL))).
    { apply (cmw_bytes_ext m2 m6 _ _ BFL2'). intros x Hx. rewrite length_le8 in Hx.
      apply (MU6 (wa x)). unfold wa. rewrite cmw_u64 by lia.
      cbn [outside fst snd]. unfold AC.shadow_addr, AC.ASAN_K in *.
      repeat split; try exact I; lia. }
    apply (cmw_bytes_ext m6 m7 _ _ BFL6). intros x Hx. rewrite length_le8 in Hx. unfold wa.
    apply (cmw_byte_eq (w_H W) (w_H W) m6 m7 x); [apply HPF6; lia | apply HPF7; lia|].
    apply HEFF; [lia | |].
    - replace (spZ (ms_regs ms6')) with (bv_unsigned (YK11.getr (ms_regs ms6') (Z_to_bv 5 2))) by reflexivity.
      rewrite USP6. unfold ESTACK, SP1 in *. lia.
    - intros Hw. pose proof (cmw_in_wr n bs (FA + 32) x Hw) as Hr. lia. }
  (* the three cell blocks the release writes *)
  assert (HSTKF7 : stk AImg.rsegs m7 FA (FA + 64))
    by (apply (WL.wcc_leafb_stk W m7); [lia | lia | intros a Ha; apply HPF7; lia]).
  destruct (stk_carve AImg.rsegs m7 FA (FA + 64) 64%nat HSTKF7 ltac:(cbn; lia)) as [_ [jF7 FRF7]].
  replace (FA + 64 - Z.of_nat 64) with FA in FRF7 by (cbn; lia).
  assert (HSTKS7 : stk AImg.rsegs m7 (AC.shadow_addr FA) (AC.shadow_addr FA + 8))
    by (apply (WL.wcc_leafb_stk W m7);
        [unfold AC.shadow_addr; lia | unfold AC.shadow_addr; lia | exact HPS7]).
  destruct (stk_carve AImg.rsegs m7 (AC.shadow_addr FA) (AC.shadow_addr FA + 8) 8%nat HSTKS7
              ltac:(cbn; lia)) as [_ [jsh7 FRS7]].
  replace (AC.shadow_addr FA + 8 - Z.of_nat 8) with (AC.shadow_addr FA) in FRS7 by (cbn; lia).
  assert (HSTKL : stk AImg.rsegs m7 FL (FL + 1))
    by (apply (WL.wcc_leafb_stk W m7); [lia | lia | intros a Ha; replace a with FL by lia; exact HFLp]).
  destruct (stk_carve AImg.rsegs m7 FL (FL + 1) 1%nat HSTKL ltac:(cbn; lia)) as [_ [jfl FRL0]].
  replace (FL + 1 - Z.of_nat 1) with FL in FRL0 by (cbn; lia).
  destruct (cmw_cb1 m7 FL jfl FRL0) as [fb FRL].
  (* the saved words, carried to the state the epilogue reloads them at *)
  match type of FRH3 with rw_cells _ _ _ ?cs =>
    assert (FRH6 : rw_cells AImg.rsegs m6 (spZ regs - 96) cs) end.
  { apply (cmw_rw_cells_ext m2 m6 _ _ FRH3). intros x Hx.
    cbn [cells_size csize cm_frhi Nat.add] in Hx.
    apply (MU6 (wa x)). unfold wa. rewrite cmw_u64 by lia.
    cbn [outside fst snd]. unfold AC.shadow_addr, AC.ASAN_K in *. repeat split; try exact I; lia. }
  match type of FRH6 with rw_cells _ _ _ ?cs =>
    assert (FRH7 : rw_cells AImg.rsegs m7 (spZ regs - 96) cs) end.
  { apply (cmw_rw_cells_ext m6 m7 _ _ FRH6). intros x Hx.
    cbn [cells_size csize cm_frhi Nat.add] in Hx. unfold wa.
    apply (cmw_byte_eq (w_H W) (w_H W) m6 m7 x);
      [apply HWIN6; lia | apply HGR; apply HWIN6; lia |].
    apply HEFF; [lia | |].
    - replace (spZ (ms_regs ms6')) with (bv_unsigned (YK11.getr (ms_regs ms6') (Z_to_bv 5 2))) by reflexivity.
      rewrite USP6. unfold ESTACK, SP1 in *. lia.
    - intros Hw. pose proof (cmw_in_wr n bs (FA + 32) x Hw) as Hr. lia. }
  (* 0x80568 .. the `ret`: the local re-poisoned, the frame retired and given back, the reloads *)
  eapply (@cmw_run fx W (ms_regs ms7') m7 md7' 525672).
  { unfold LCK.ms_of_regs.
    assert (V2 : YK11.getr (ms_regs ms7') (Z_to_bv 5 2) = Z_to_bv 64 SP1)
      by (etransitivity; [exact T2 | exact R2]).
    assert (V8 : YK11.getr (ms_regs ms7') (Z_to_bv 5 8) = Z_to_bv 64 (spZ regs))
      by (etransitivity; [exact T8 | exact R8]).
    assert (V9 : YK11.getr (ms_regs ms7') (Z_to_bv 5 9) = Z_to_bv 64 SP1)
      by (etransitivity; [exact T9 | exact R9]).
    assert (V18 : YK11.getr (ms_regs ms7') (Z_to_bv 5 18) = Z_to_bv 64 FA)
      by (etransitivity; [exact T18 | exact R18]).
    assert (V19 : YK11.getr (ms_regs ms7') (Z_to_bv 5 19) = Z_to_bv 64 f) by exact T19.
    assert (V20 : YK11.getr (ms_regs ms7') (Z_to_bv 5 20) = Z_to_bv 64 n) by exact T20.
    assert (V21 : YK11.getr (ms_regs ms7') (Z_to_bv 5 21) = Z_to_bv 64 (FA + 32)) by exact T21.
    assert (V22 : YK11.getr (ms_regs ms7') (Z_to_bv 5 22) = Z_to_bv 64 FA)
      by (etransitivity; [exact T22 | exact R22]).
    assert (V23 : YK11.getr (ms_regs ms7') (Z_to_bv 5 23) = Z_to_bv 64 (AC.shadow_addr FA))
      by (etransitivity; [exact T23 | exact R23]).
    assert (V24 : YK11.getr (ms_regs ms7') (Z_to_bv 5 24) = Z_to_bv 64 AC.ASAN_K) by exact T24.
    assert (V25 : YK11.getr (ms_regs ms7') (Z_to_bv 5 25) = Z_to_bv 64 EO) by exact T25.
    assert (V26 : YK11.getr (ms_regs ms7') (Z_to_bv 5 26) = Z_to_bv 64 WANT) by exact T26.
    rewrite V2, V8, V9, V18, V19, V20, V21, V22, V23, V24, V25, V26.
    eapply cm_seg8_F with (SP := spZ regs) (SP1 := SP1) (FA := FA) (FL := FL) (f := f) (n := n)
                          (eo := EO) (want := WANT);
    [ unfold SP1 in *; lia | lia | lia | lia | lia | lia | lia | exact HDF | exact HDS | exact HD
    | exact HDL | exact HDLS | lia
    | exact FRH7 | exact FRF7 | exact FRS7 | exact FRL | exact BFL7
    | eapply (WL.wcc_leafb_rng_journal B); [exact HJ7 | lia | lia]
    | apply (WL.wcc_leafb_rng_vis W m7); [lia | lia |]; intros a Ha; apply HPF7; lia
    | apply (WL.wcc_leafb_rng_vis W m7);
        [unfold AC.shadow_addr; lia | unfold AC.shadow_addr; lia | exact HPS7]
    | apply (WL.wcc_leafb_rng_vis W m7); [lia | lia |];
      intros a Ha; replace a with FL by lia; exact HFLp ]. }
  intros ms8' md8' (ms08 & (m8 & -> & MU8 & WM8 & BFL8) & EQV8) SBM8.
  destruct (cmw_regs_of EQV8) as (U1 & U2 & U3 & U4 & U8 & U9 & U10 & U11 & U12 & U18 & U19 & U20 & U21 & U22 &
    U23 & U24 & U25 & U26 & U27).
  assert (Hret : ret_pc (YK11.getr regs (Z_to_bv 5 1)) = YK11.getr regs (Z_to_bv 5 1))
    by (apply LeafCgFacts.ret_ok_stmt_YK0s; exact Hra).
  rewrite Hret in EQV8.
  rewrite (cmw_ms_shape _ _ _ _ EQV8).
  (* the journal at the model the result test materialized *)
  assert (HJ7' : ajournalA CM_STK (spZ regs) [] lyc Sc W memc mdc [(CM_CID, pos)] lyc S2 W m7 md7' 0).
  { apply (ajournal_exec segs B LAWS cmw_segs_low CM_STK (spZ regs) [] lyc Sc W memc mdc
             [(CM_CID, pos)] lyc S2 W m7 md7 0 m7 md7' (fun _ => False) HJ7);
    [ intros x _; reflexivity | intros x Hx; exact Hx | intros x _; reflexivity | exact SBM7
    | intros a Ha; destruct Ha ]. }
  (* the bytes the release wrote are visible, and each is the frame's, its shadow's or the flag byte *)
  assert (Hvis : forall x : word,
    ~ outside [(FA, FA + 64); (AC.shadow_addr FA, AC.shadow_addr FA + 8); (FL, FL + 1)] (bv_unsigned x) ->
    w_H W x = false).
  { intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x).
    destruct (Z_lt_le_dec (bv_unsigned x) FA) as [L1|L1];
      [|destruct (Z_lt_le_dec (bv_unsigned x) (FA + 64)) as [L2|L2];
        [exact (proj1 (HPF7 (bv_unsigned x) ltac:(lia)))|]];
    (destruct (Z_lt_le_dec (bv_unsigned x) (AC.shadow_addr FA)) as [L3|L3];
     [|destruct (Z_lt_le_dec (bv_unsigned x) (AC.shadow_addr FA + 8)) as [L4|L4];
       [exact (proj1 (HPS7 (bv_unsigned x) ltac:(lia)))|]]);
    (destruct (Z.eq_dec (bv_unsigned x) FL) as [L5|L5]; [rewrite L5; exact (proj1 HFLp)|]);
    exfalso; apply Hx; cbn [outside fst snd]; repeat split; try exact I; lia. }
  assert (HWr : forall a, 0 <= a < 2 ^ 64 ->
    ~ outside [(FA, FA + 64); (AC.shadow_addr FA, AC.shadow_addr FA + 8); (FL, FL + 1)] a ->
    awr_byte CM_STK (spZ regs) [] (ablocks B lyc Sc) (ablocks B lyc S2) lyc [(CM_CID, pos)] a \/ a = FL).
  { intros a Ha Hx.
    destruct (Z.eq_dec a FL) as [L5|L5]; [right; exact L5|]. left. right. right. right.
    exists CM_CID, pos. split; [left; reflexivity|].
    destruct (Z_lt_le_dec a FA) as [L1|L1];
      [|destruct (Z_lt_le_dec a (FA + 64)) as [L2|L2];
        [left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes CM_CID) with 64; lia|]];
    (destruct (Z_lt_le_dec a (AC.shadow_addr FA)) as [L3|L3];
     [|destruct (Z_lt_le_dec a (AC.shadow_addr FA + 8)) as [L4|L4];
       [right; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes CM_CID / 8) with 8;
        unfold AC.shadow_addr, AC.ASAN_K in L3, L4; unfold shadow_addr, SHADOW_OFF; lia|]]);
    exfalso; apply Hx; cbn [outside fst snd]; repeat split; try exact I; lia. }
  assert (MG8 : mem_grows (mrestrict (w_H W) m7) (mrestrict (w_H W) m8)).
  { apply (cmw_mem_grows W m7 m8 WM8). intros x.
    destruct (Z_lt_le_dec (bv_unsigned x) FA) as [L1|L1];
      [|destruct (Z_lt_le_dec (bv_unsigned x) (FA + 64)) as [L2|L2];
        [right; split; [apply HPF7; lia | apply HNIF; lia]|]];
    (destruct (Z_lt_le_dec (bv_unsigned x) (AC.shadow_addr FA)) as [L3|L3];
     [|destruct (Z_lt_le_dec (bv_unsigned x) (AC.shadow_addr FA + 8)) as [L4|L4];
       [right; split; [apply HPS7; lia | apply HNIS; lia]|]]);
    (destruct (Z.eq_dec (bv_unsigned x) FL) as [L5|L5];
     [right; split; [rewrite L5; exact HFLp | rewrite L5; exact HFLimg]|]);
    left; apply (MU8 x); cbn [outside fst snd]; repeat split; try exact I; lia. }
  assert (Hfl : aview segs (w_H W) m8 FL = Some 0)
    by (rewrite (cmw_aview_of_bytes1 W m8 FL _ (proj1 HFLp) BFL8); reflexivity).
  pose proof (cmw_release CM_STK (spZ regs) [] lyc Sc W memc mdc lyc S2 W m7 md7' 0 CM_CID pos m8 md8'
    _ HJ7' MU8 MG8 SBM8 HWr Hvis Hfl) as HJ8.
  (* the post: the outer journal, the registers the call kept, the blocks, acall_kept and the meter bound *)
  set (S3 := stack_free_state CM_CID pos S2) in *.
  assert (Hfr3 : frames S3 = frames Sc) by exact (cmw_sf_frames CM_CID pos S2 (frames Sc) Hfrs2).
  assert (Eab3 : ablocks B lyc S3 = ablocks B lyc Sc).
  { unfold S3, ablocks. rewrite blocks_stack_free_state. fold (ablocks B lyc S2). exact Eab2. }
  apply SRr_ret. unfold wire_cm_post.
  exists lyc, S3, (ms_regs ms8'), m8, md8'.
  split; [reflexivity|].
  split.
  { pose proof (ajournal_sub segs B LAWS cmw_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
                  CM_STK (spZ regs) [] [] lyc S3 W m8 md8' 0 HJ HJ8 Hwlo Hwhi
                  ltac:(intros a (r0 & Hr0 & _); destruct Hr0)) as J.
    cbn [app] in J. unfold CM_EV. exact J. }
  split.
  { intros i Hi. unfold acallee_saved in Hi.
    assert (Hc : i = 2 \/ i = 3 \/ i = 4 \/ i = 8 \/ i = 9 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/
                 i = 23 \/ i = 24 \/ i = 25 \/ i = 26 \/ i = 27) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
    - etransitivity; [exact U2|]. unfold spZ. apply Z_to_bv_bv_unsigned.
    - etransitivity; [exact U3|]. etransitivity; [exact T3|].
      etransitivity; [exact (HP7 3 ltac:(unfold acallee_saved; lia))|].
      etransitivity; [exact P3|]. etransitivity; [exact N3 | symmetry; exact Hgp].
    - etransitivity; [exact U4|]. etransitivity; [exact T4|].
      etransitivity; [exact (HP7 4 ltac:(unfold acallee_saved; lia))|].
      etransitivity; [exact P4|]. etransitivity; [exact N4 | symmetry; exact Htp].
    - exact U8.
    - exact U9.
    - exact U18.
    - exact U19.
    - exact U20.
    - exact U21.
    - exact U22.
    - exact U23.
    - exact U24.
    - exact U25.
    - exact U26.
    - etransitivity; [exact U27|]. etransitivity; [exact T27|].
      etransitivity; [exact (HP7 27 ltac:(unfold acallee_saved; lia))|].
      etransitivity; [exact P27 | exact N27]. }
  split; [exact Hfr3|].
  split; [rewrite Eab3; apply Permutation_refl|].
  split.
  { apply (acall_kept_of_journal segs B cmw_segs_low CM_STK (spZ regs) [] [] lyc Sc W memc mdc lyc S3 W m8
             md8' 0 (fun _ => False) HJ8 cmw_HARc).
    - intros a (r0 & Hr0 & _). destruct Hr0.
    - intros b m i Hb _ _. rewrite Eab3. exact Hb.
    - exact sink_closed_nil. }
  destruct Hset2 as (f0 & Ef0). unfold S3, stack_free_state. rewrite Ef0.
  apply (mo_le_set_fs_r MT MTF). apply (mo_le_set_fs_r MT MTF). exact (mo_le_refl MT MTL Sc).
Qed.

End Entry.
End Walk.

Theorem wire_check_meter_holds {fx : YK11.FPState} {rc : YM05.RunCeil} (B : asyms) (MT : ameter_ops) :
  @wire_check_meter_holds_stmt fx rc B MT.
Proof.
  unfold wire_check_meter_holds_stmt.
  intros HPCS HCELLS LAWS MTL MTF SMP ASF FFL ASM LEAF.
  unfold wire_check_meter_cg.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs f n bs
    HJ Hra Hra4 Hgp Htp H10 H11 Hal Hwlo Hwhi Hlen Hblk Hgarr Hcnt Hnev.
  eapply cmw_entry; eassumption.
Qed.

Print Assumptions wire_check_meter_holds.
