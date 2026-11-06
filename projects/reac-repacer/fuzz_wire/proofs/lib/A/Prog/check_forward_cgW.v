(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Spec/StrFun.v; 653 of its 721 lines of code are new or changed and 396 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac-repacer/fuzz_wire's check_width in image A, proving the frozen
   statement lib/A/Prog/check_width_cg.v wire_check_width_holds_stmt. The form is reac-repacer/fuzz_uci's
   lib/A/Prog/check_value_cgW.v (footprint runs carried into SRr, an inner journal over the call's stack window, each
   call cut by its callee's statement) with its segment file lib/A/Prog/UciCvSegs.v, and the leaf call of its
   lib/A/Prog/check_clamp_cgW.v (here through lib/A/Prog/WireCcLeafb.v wcc_leafb_journal, the leaf taken by
   WireCg.v wire_leaf_at). The w_width loop and the frame law are this unit's plain walk lib/Prog/check_width.v
   (width_loop, w_width_frame_law, fc_model_neg), restated over image A's rp_frame_channels_model. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/A/Prog/check_width_cgW.v, with its module paths, module names and numbers changed; 307 of its 487 lines of code are new or changed and 541 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac-repacer/fuzz_wire's check_forward in image A, proving the frozen statement
   lib/A/Prog/check_forward_cg.v wire_check_forward_holds_stmt, in the form of reac-repacer/fuzz_uci's
   lib/A/Prog/check_value_cgW.v (its helpers cv_u64, cv_byte_eq, cv_rw_cells_ext, cv_fp_avoids, cv_run, cv_ms_shape,
   cv_ms_reg, cv_regs_of, cv_garr8_aview, cv_garr8_of_aview, cv_aj_md and its entry / return pieces) with the leaf
   call of its lib/A/Prog/check_clamp_cgW.v (the leaf contract taken through lib/A/Prog/WireCcLeafb.v). *)
(* check_forward_cgW: wire_check_forward_cg (wire_sigma WS_check_forward) from the leaf contract the statement names.

   The walk (offsets from the entry; lib/A/Prog/WireCfSegs.v names the cut points):
     1. an INNER journal at the entry state (YCbq.v ajournal_sub_init): stack window [spZ regs - CF_STK, spZ regs),
        no footprint, no frame of its own;
     2. cf_seg1_F: the 0x30-byte frame, the shadow base, s0 = f, s1 = bcast, s2 = n; the inner journal follows the
        frame write (YCbq.v ajournal_exec);
     3. `jal rp_fwd_class` at +0x34: the leaf contract (lib/A/Prog/rp_fwd_class_cg.v through WireCg.v wire_leaf_at),
        its premises from the inner journal (WireCcLeafb.v: the frame window, the cells, f's block), its post the
        inner journal again (WireCcLeafb.v wcc_leafb_journal) with a0 = fwd_class_result n bcast of the bytes;
     4. cf_tail_F: the want of the harness, equal to a0 on every path, so the abort is not reached; the frame
        reloaded and `ret` to the caller's ra (YK0s.v ret_ok);
     5. the post: the outer journal by YCbq.v ajournal_sub, acall_kept by YCbq.v acall_kept_of_journal. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n YA0o YK1b.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI16 YI5b YI5c YP09 YO0f.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Frame Cells Step Regs6ss.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require AE2k Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import WirePSyms WirePAddr WireCg check_forward_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import WireCfSegs WireCcLeafb.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require LeafCgKit LeafCgFacts LeafCgGlue WirePImg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require rp_fwd_class_cg rp_fwd_class_F_c AsanKA.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_fwd_class_c.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.LeafCgKit.
Module AC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.AsanCells.
Module AImg := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Img0.
Module LFC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_fwd_class_cg.
Module LFF := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_fwd_class_F_c.
Module PFC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_fwd_class_c.
Module AKA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.AsanKA.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ======================================================================== *)
(* Image-free helpers (check_value_cgW.v)                                     *)
(* ======================================================================== *)

Lemma cf_u64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz. Qed.

Lemma cf_byte_eq : forall (H H' : word -> bool) (m m' : word -> option byte) (a : Z),
  apresent H m a -> apresent H' m' a -> aview tfibsegs H' m' a = aview tfibsegs H m a ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros H H' m m' a [Hh [b Hb]] [Hh' [b' Hb']] E.
  unfold aview, YP09.mbyte, mrestrict in E.
  rewrite Hh, Hh' in E. rewrite Hb, Hb' in E. cbn in E.
  injection E as E. rewrite Hb, Hb'. f_equal. apply bv_eq. exact E.
Qed.

Lemma cf_rw_cells_ext : forall (m m' : word -> option byte) (A : Z) (cs : list cell),
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

Lemma cf_fp_avoids : forall (W : world tfibsegs),
  LCK.fp_avoids (@w_H tfibsegs W) (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W).
Proof. intros W a n H. unfold LCK.RNG_W in H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.

(* A footprint run from cgif's configuration at pc, carried into SRr (check_value_cgW.v cv_run). *)
Lemma cf_run {fx : YK11.FPState} : forall (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (pc : Z) (P : machine_state -> Prop) (Q : world tfibsegs -> config -> Prop),
  ExecF.evtF AImg.rsegs (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) P (@LCK.ms_of_regs fx pc regs mem) ->
  (forall ms' md', (exists ms0, P ms0 /\ ms_eqv ms0 ms') -> same_but_materialized md md' ->
     SRr tfibsegs W (mkCfg ms' md') Q) ->
  SRr tfibsegs W (@cfg_at fx tfibsegs pc regs mem md) Q.
Proof.
  intros W regs mem md pc P Q Hrun K. unfold cfg_at.
  pose proof (LeafCgGlue.evtF_eqv AImg.rsegs _ P _ _ Hrun (@LeafCgGlue.ms_of_regs_eqv fx pc regs mem)) as Hrun'.
  apply (LeafCgFacts.bridge_evtF_stmt_YA0n W _ md _ _ Q Hrun' (cf_fp_avoids W)).
  intros ms' md' (ms1 & HP & HE & _) Hs. apply K; [exists ms1; split; assumption | exact Hs].
Qed.

Lemma cf_ms_shape {fx : YK11.FPState} : forall (R : bvmap 5 word) (pc : word) (m : word -> option byte)
    (ms' : machine_state),
  ms_eqv (MS R (@fp_regs fx) pc (@fp_csr fx) None m (YK11.seg_rom tfibsegs)) ms' ->
  ms' = @YK11.mkst fx (ms_regs ms') pc m (YK11.seg_rom tfibsegs).
Proof.
  intros R pc m [r f p sv rv fc mm ro] (_ & Hf & Hp & Hs & Hr & Hc & Hm & Hro).
  cbn [MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
  subst. reflexivity.
Qed.

Lemma cf_ms_reg : forall (R : bvmap 5 word) F pc fc rv m ro (ms' : machine_state) (r : bv 5),
  ms_eqv (MS R F pc fc rv m ro) ms' -> YK11.getr (ms_regs ms') r = YK11.getr R r.
Proof.
  intros R F pc fc rv m ro ms' r (HR & _). cbn [MS ms_regs] in HR. exact (LeafCgGlue.getr_xeqv _ _ HR r).
Qed.

Lemma cf_regs_of : forall {x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
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
  repeat split; (etransitivity; [apply (cf_ms_reg _ _ _ _ _ _ _ _ _ H) | reflexivity]).
Qed.

Lemma cf_le_byte1 : forall v, 0 <= v < 256 -> Z.shiftr (v mod 2 ^ (8 * Z.of_nat 1)) (8 * Z.of_nat 0) mod 256 = v.
Proof.
  intros v Hv. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite Z.mod_small by lia. apply Z.mod_small. lia.
Qed.

Lemma cf_garr8_aview : forall (H : word -> bool) mem a (l : list Z) (j : nat),
  garr8 tfibsegs (mrestrict H mem) a l -> (j < length l)%nat ->
  aview tfibsegs H mem (a + Z.of_nat j) = Some (nth j l 0).
Proof.
  intros H mem a l j G Hj. destruct (G j Hj) as [V R]. specialize (V 0%nat ltac:(lia)).
  rewrite Nat2Z.inj_0, Z.add_0_r in V.
  unfold aview. rewrite V. cbn [option_map]. f_equal.
  unfold YO0f.le_byte, YG0f.le_byte. rewrite Z_to_bv_unsigned, (cf_le_byte1 _ R).
  apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

Lemma cf_garr8_of_aview : forall (H : word -> bool) mem a (l : list Z),
  (forall j, (j < length l)%nat -> aview tfibsegs H mem (a + Z.of_nat j) = Some (nth j l 0) /\ 0 <= nth j l 0 < 256) ->
  garr8 tfibsegs (mrestrict H mem) a l.
Proof.
  intros H mem a l HA j Hj. destruct (HA j Hj) as [E R]. split; [|exact R].
  intros k Hk. assert (Ek : k = 0%nat) by lia. subst k. rewrite Nat2Z.inj_0, Z.add_0_r.
  unfold aview in E.
  destruct (YP09.mbyte tfibsegs (mrestrict H mem) (a + Z.of_nat j)) as [b|] eqn:Eb; cbn in E; [|discriminate].
  injection E as E. f_equal. apply bv_eq. unfold YO0f.le_byte, YG0f.le_byte.
  rewrite Z_to_bv_unsigned, (cf_le_byte1 _ R), <- E.
  symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Section Walk.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation sink := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HCELLS : wire_cells B.
Hypothesis LAWS : AR_laws segs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis LEAF : forall fx' : YK11.FPState, @wire_leaf_at rc B (@LFC.wire_rp_fwd_class_cg) fx'.
Local Abbreviation ajournalA := (@ajournal rc sink segs B).

(* A run that writes no memory: the journal follows its same_but_materialized (check_value_cgW.v cv_aj_md). *)
Lemma cf_aj_md : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k mdc',
  ajournalA STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k -> same_but_materialized mdc mdc' ->
  ajournalA STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc' k.
Proof.
  intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k mdc' HJ Hs.
  eapply (ajournal_exec segs B LAWS WirePImg.wire_segs_low STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc
            mdc' (fun _ => False) HJ).
  - intros x _. reflexivity.
  - apply YK1b.mem_grows_refl.
  - intros x _. reflexivity.
  - exact Hs.
  - intros a Ha. destruct Ha.
Qed.

Section Entry.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (f n bc : Z)
  (bs : list byte).
Hypothesis HJ : ajournalA STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis Hra : YK0s.ret_ok (YK11.getr regs 1).
Hypothesis Hra4 : 4096 <= raZ regs.
Hypothesis Hgp : YK11.getr regs 3 = w64 (as_gp B).
Hypothesis Htp : YK11.getr regs 4 = w64 (as_tp B).
Hypothesis H10 : YK11.getr regs 10 = w64 f.
Hypothesis H11 : YK11.getr regs 11 = w64 n.
Hypothesis H12 : YK11.getr regs 12 = w64 bc.
Hypothesis Hal : spZ regs mod 16 = 0.
Hypothesis Hwlo : sp0 - STK <= spZ regs - CF_STK.
Hypothesis Hwhi : spZ regs <= sp0.
Hypothesis Hn : 0 <= n <= CF_N_MAX.
Hypothesis Hlen : Z.of_nat (length bs) = n.
Hypothesis Hbc : 0 <= bc <= 1.
Hypothesis Hblk : 0 < n -> exists bA nA, In (bA, nA) (ablocks B lyc Sc) /\ bA <= f /\ f + n <= bA + nA.
Hypothesis Hgarr : garr8 segs (mrestrict (w_H W) memc) f (map (fun b : byte => bv_unsigned b) bs).
Hypothesis Hnev : st_nev S + k + CF_EV <= EV_MAX.

Local Abbreviation POST := (wire_cf_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs).
(* The inner journal: from the entry state, stack window [spZ regs - CF_STK, spZ regs). *)
Local Abbreviation JI ly1 S1 W1 m1 md1 k1 :=
  (ajournalA CF_STK (spZ regs) [] lyc Sc W memc mdc [] ly1 S1 W1 m1 md1 k1).
Local Abbreviation GR rg i := (YK11.getr rg (Z_to_bv 5 i)).

(* The frame the prologue wrote: the caller's s3, s2, s1, s0 and ra at [spZ regs - 0x28, spZ regs). *)
Definition cf_frame (m : word -> option byte) : Prop :=
  exists v0, rw_cells AImg.rsegs m (spZ regs - 48)
    (C8 v0 :: cf_fr (GR regs 19) (GR regs 18) (GR regs 9) (GR regs 8) (GR regs 1)).

(* ---- facts of the entry ---- *)

Lemma cf_HARc : AR segs B lyc Sc W memc mdc.
Proof. destruct HJ as (HAR & _). exact HAR. Qed.

Lemma cf_JI0 : JI lyc Sc W memc mdc 0.
Proof.
  apply (ajournal_sub_init segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k CF_STK (spZ regs) []
           (spZ regs - sp0) HJ).
  - lia.
  - pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (H16 & _) & _).
    rewrite Zminus_mod, Hal, H16. reflexivity.
  - lia.
  - unfold CF_STK, CF_FRAME, ESTACK. lia.
  - lia.
Qed.

Lemma cf_sp_rng : YM05.alloc_ceiling + 48 + 4096 <= spZ regs /\ spZ regs <= 2 ^ 47.
Proof.
  pose proof cf_JI0 as J. destruct J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    (_ & _ & Hc & Hlo & Hhi & H47 & _) & _).
  unfold CF_STK, CF_FRAME, ESTACK in Hlo. lia.
Qed.

Lemma cf_win : forall ly1 S1 W1 m1 md1 k1, JI ly1 S1 W1 m1 md1 k1 ->
  forall a, spZ regs - CF_STK <= a < spZ regs -> apresent (w_H W1) m1 a.
Proof.
  intros ly1 S1 W1 m1 md1 k1 J.
  destruct J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). exact Hpres.
Qed.

(* f's bytes at a state of the inner journal that keeps the caller's blocks (the journal's kept-block clause, and
   the entry's garr8; check_value_cgW.v cv_reply_at). *)
Lemma cf_garr8_at : forall m1 md1 k1, JI lyc Sc W m1 md1 k1 -> 0 < n ->
  garr8 segs (mrestrict (w_H W) m1) f (map (fun b : byte => bv_unsigned b) bs).
Proof.
  intros m1 md1 k1 J1 Hn0.
  destruct (Hblk Hn0) as (bA & nA & HbA & HbA1 & HbA2).
  assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia).
  pose proof J1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  apply cf_garr8_of_aview. intros j Hj. rewrite length_map in Hj.
  split.
  - replace (f + Z.of_nat j) with (bA + (f + Z.of_nat j - bA)) by lia.
    rewrite (F2 bA nA (f + Z.of_nat j - bA) HbA HbA ltac:(lia) ltac:(intros (r0 & Hr0 & _); destruct Hr0)).
    replace (bA + (f + Z.of_nat j - bA)) with (f + Z.of_nat j) by lia.
    apply (cf_garr8_aview (w_H W) memc f _ j Hgarr). rewrite length_map. exact Hj.
  - destruct (Hgarr j ltac:(rewrite length_map; exact Hj)) as [_ R]. exact R.
Qed.

(* The frame [spZ regs - 48, spZ regs) lies above the leaf's window [spZ regs - 48 - ESTACK, spZ regs - 48). *)
Lemma cf_frame_kept : forall (m1 m2 : word -> option byte),
  cf_frame m1 ->
  (forall a, spZ regs - CF_STK <= a < spZ regs -> apresent (w_H W) m1 a) ->
  (forall a, spZ regs - CF_STK <= a < spZ regs -> apresent (w_H W) m2 a) ->
  (forall a, spZ regs - 48 <= a < spZ regs -> aview segs (w_H W) m2 a = aview segs (w_H W) m1 a) ->
  cf_frame m2.
Proof.
  intros m1 m2 (v0 & F) P1 P2 E. exists v0.
  pose proof cf_sp_rng as [S1 S2].
  apply (cf_rw_cells_ext m1 m2 _ _ F). intros a Ha.
  change (Z.of_nat (cells_size (C8 v0 :: cf_fr (GR regs 19) (GR regs 18) (GR regs 9) (GR regs 8) (GR regs 1))))
    with 48 in Ha.
  unfold wa. apply (cf_byte_eq (w_H W) (w_H W) m1 m2 a); [apply P1 | apply P2 | apply E];
    unfold CF_STK, CF_FRAME, ESTACK in *; lia.
Qed.

(* ======================================================================== *)
(* The walk                                                                   *)
(* ======================================================================== *)

(* At CF_RET (the leaf returned with a0 = its result): cf_tail_F, the return, and the post. *)
Lemma cf_at_ret : forall regs2 m2 md2,
  JI lyc Sc W m2 md2 0 -> cf_frame m2 ->
  GR regs2 2 = Z_to_bv 64 (spZ regs - 48) -> GR regs2 3 = GR regs 3 -> GR regs2 4 = GR regs 4 ->
  GR regs2 8 = Z_to_bv 64 f -> GR regs2 9 = Z_to_bv 64 bc -> GR regs2 18 = Z_to_bv 64 n ->
  GR regs2 19 = Z_to_bv 64 AC.ASAN_K ->
  GR regs2 20 = GR regs 20 -> GR regs2 21 = GR regs 21 -> GR regs2 22 = GR regs 22 -> GR regs2 23 = GR regs 23 ->
  GR regs2 24 = GR regs 24 -> GR regs2 25 = GR regs 25 -> GR regs2 26 = GR regs 26 -> GR regs2 27 = GR regs 27 ->
  GR regs2 10 = Z_to_bv 64 (PFC.fwd_class_result (bv_unsigned (Z_to_bv 64 n)) (bv_unsigned (Z_to_bv 64 bc)) bs) ->
  SRr segs W (@cfg_at fx segs CF_RET regs2 m2 md2) POST.
Proof.
  intros regs2 m2 md2 J2 (v0 & FR) K2 K3 K4 K8 K9 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K10.
  pose proof cf_sp_rng as [Hsp1 Hsp2].
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  assert (EST : CF_STK = 48 + 4096) by reflexivity.
  assert (SP2 : bv_unsigned (GR regs2 2) = spZ regs - 48) by (rewrite K2; apply cf_u64; lia).
  assert (UN : bv_unsigned (Z_to_bv 64 n) = n) by (apply cf_u64; unfold CF_N_MAX in Hn; lia).
  pose proof (proj1 J2) as HAR2.
  eapply (@cf_run fx W regs2 m2 md2 CF_RET).
  { unfold LCK.ms_of_regs. rewrite K8, K9, K10, K18, K19.
    eapply cf_tail_F.
    - rewrite SP2. exact FR.
    - rewrite SP2. lia.
    - rewrite SP2. apply (wcc_leafb_rng_vis W m2); [lia | lia |].
      intros a Ha. apply (cf_win _ _ _ _ _ _ J2). unfold CF_STK, CF_FRAME, ESTACK in *. lia.
    - rewrite UN. intros H18.
      destruct (Hblk ltac:(lia)) as (bA & nA & HbA & HbA1 & HbA2).
      pose proof (al_blocks _ _ LAWS lyc Sc W m2 md2 bA nA HAR2 HbA) as (_ & HA4 & HAc & _).
      assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia).
      assert (UF : bv_unsigned (Z_to_bv 64 f) = f) by (apply cf_u64; lia).
      rewrite UF.
      split; [lia|].
      split.
      { apply (wcc_leafb_bytes_garr8 W m2 f bs (cf_garr8_at m2 md2 0 J2 ltac:(lia))); lia. }
      split.
      { apply (wcc_leafb_addressable_block B LAWS lyc Sc W m2 md2 bA nA f 18 HAR2 HbA); lia. }
      split.
      { apply (wcc_leafb_rng_block B LAWS lyc Sc W m2 md2 bA nA f 18 HAR2 HbA); lia. }
      apply (wcc_leafb_rng_shadow_block B LAWS lyc Sc W m2 md2 bA nA f 18 HAR2 HbA); lia. }
  intros ms' md' (ms0 & (a1' & a2' & a3' & ->) & EQV) SBM.
  destruct (cf_regs_of EQV) as (G1 & G2 & G3 & G4 & G8 & G9 & G10 & _ & _ & G18 & G19 & G20 & G21 & G22 & G23 &
    G24 & G25 & G26 & G27).
  assert (Hret : ret_pc (GR regs 1) = GR regs 1).
  { apply LeafCgFacts.ret_ok_stmt_YK0s. exact Hra. }
  rewrite Hret in EQV.
  rewrite (cf_ms_shape _ _ _ _ EQV).
  pose proof (cf_aj_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J2 SBM) as J2'.
  apply SRr_ret. unfold wire_cf_post.
  exists lyc, Sc, (ms_regs ms'), m2, md'.
  split; [reflexivity|].
  split.
  { pose proof (ajournal_sub segs B LAWS WirePImg.wire_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
                  CF_STK (spZ regs) [] [] lyc Sc W m2 md' 0 HJ J2' Hwlo Hwhi
                  ltac:(intros a (r0 & Hr0 & _); destruct Hr0)) as J.
    cbn [app] in J. unfold CF_EV. exact J. }
  split.
  { intros i Hi. unfold acallee_saved in Hi.
    assert (Hc : i = 2 \/ i = 3 \/ i = 4 \/ i = 8 \/ i = 9 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/
                 i = 23 \/ i = 24 \/ i = 25 \/ i = 26 \/ i = 27) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
    - etransitivity; [exact G2|]. rewrite SP2. replace (spZ regs - 48 + 48) with (spZ regs) by lia.
      unfold spZ. apply Z_to_bv_bv_unsigned.
    - etransitivity; [exact G3|]. exact K3.
    - etransitivity; [exact G4|]. exact K4.
    - exact G8.
    - exact G9.
    - exact G18.
    - exact G19.
    - etransitivity; [exact G20|]. exact K20.
    - etransitivity; [exact G21|]. exact K21.
    - etransitivity; [exact G22|]. exact K22.
    - etransitivity; [exact G23|]. exact K23.
    - etransitivity; [exact G24|]. exact K24.
    - etransitivity; [exact G25|]. exact K25.
    - etransitivity; [exact G26|]. exact K26.
    - etransitivity; [exact G27|]. exact K27. }
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { apply (acall_kept_of_journal segs B WirePImg.wire_segs_low CF_STK (spZ regs) [] [] lyc Sc W memc mdc lyc Sc W m2
             md' 0 (fun _ => False) J2' cf_HARc).
    - intros a (r0 & Hr0 & _). destruct Hr0.
    - intros b m i Hb _ _. exact Hb.
    - exact sink_closed_nil. }
  exact (mo_le_refl MT MTL Sc).
Qed.

(* At CF_ENTRY: the inner journal, cf_seg1_F (the prologue), then the leaf rp_fwd_class (f, n, bcast). *)
Lemma cf_entry : SRr segs W (@cfg_at fx segs CF_ENTRY regs memc mdc) POST.
Proof.
  pose proof cf_sp_rng as [Hsp1 Hsp2].
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  pose proof cf_JI0 as JI0.
  pose proof (cf_win _ _ _ _ _ _ JI0) as Hpres0.
  assert (EST : CF_STK = 48 + 4096) by reflexivity.
  pose proof (wcc_leafb_asan_cells B HCELLS lyc Sc W memc mdc cf_HARc) as (CK & GCK & _).
  assert (E10 : GR regs 10 = Z_to_bv 64 f) by exact H10.
  assert (E11 : GR regs 11 = Z_to_bv 64 n) by exact H11.
  assert (E12 : GR regs 12 = Z_to_bv 64 bc) by exact H12.
  (* the prologue *)
  eapply (@cf_run fx W regs memc mdc CF_ENTRY).
  { unfold LCK.ms_of_regs. rewrite E10, E11, E12.
    eapply cf_seg1_F with (lo := spZ regs - CF_STK).
    all: try change (bv_unsigned (GR regs 2)) with (spZ regs).
    - apply (wcc_leafb_stk W memc); [lia | lia | exact Hpres0].
    - lia.
    - exact GCK.
    - exact CK.
    - unfold AC.CELL_K. lia.
    - apply (wcc_leafb_rng_vis W memc); [lia | lia |]. intros a Ha. apply Hpres0. lia.
    - exact (proj1 (wcc_leafb_rng_cells W)).
    - exact (proj2 (wcc_leafb_rng_cells W)). }
  intros ms' md' (ms0 & (m1 & v0 & -> & MU & WM & FR) & EQV) SBM.
  change (bv_unsigned (GR regs 2)) with (spZ regs) in MU, FR.
  destruct (cf_regs_of EQV) as (E1 & E2 & E3 & E4 & E8 & E9 & E10' & E11' & E12' & E18 & E19 & E20 & E21 & E22 &
    E23 & E24 & E25 & E26 & E27).
  rewrite (cf_ms_shape _ _ _ _ EQV).
  (* the inner journal after the frame write *)
  assert (HJ1 : JI lyc Sc W m1 md' 0).
  { apply (ajournal_exec segs B LAWS WirePImg.wire_segs_low CF_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W memc
             mdc 0 m1 md' (fun a => spZ regs - 48 <= a < spZ regs) JI0).
    - intros x Hx. unfold mrestrict. rewrite (MU x); [reflexivity|]. cbn [outside]. split; [exact Hx | exact I].
    - intros x Hx. unfold mrestrict in *. revert Hx. destruct (w_H W x) eqn:Ehx; intros Hx; [exact Hx|].
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs - 48)) as [Hl|Hl];
        [rewrite (MU x); [exact Hx | cbn [outside]; split; [lia | exact I]]|].
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [Hh|Hh];
        [|rewrite (MU x); [exact Hx | cbn [outside]; split; [lia | exact I]]].
      assert (Hxr : spZ regs - CF_STK <= bv_unsigned x < spZ regs) by lia.
      destruct (Hpres0 _ Hxr) as [_ (b & Hb)].
      assert (Hw : wview AImg.rsegs m1 x <> None).
      { refine (WM x _). unfold wview. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
      unfold wview in Hw. destruct (m1 x) as [b'|] eqn:Em1; [discriminate|]. exfalso.
      rewrite (LeafCgGlue.find_segment_out AImg.rsegs (bv_unsigned x) 1) in Hw; [exact (Hw eq_refl)|lia|].
      intros sg Hin Hr. pose proof (WirePImg.wire_segs_low (bv_unsigned x) (ex_intro _ sg (conj Hin Hr))) as Hlow.
      unfold kLowMemEnd in Hlow. lia.
    - intros x Hx.
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs - 48)) as [Hl|Hl];
        [apply (MU x); cbn [outside]; split; [lia | exact I]|].
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [Hh|Hh];
        [|apply (MU x); cbn [outside]; split; [lia | exact I]].
      exfalso.
      assert (Hxr : spZ regs - CF_STK <= bv_unsigned x < spZ regs) by lia.
      pose proof (proj1 (Hpres0 _ Hxr)) as Hhx. rewrite Z_to_bv_bv_unsigned in Hhx. congruence.
    - exact SBM.
    - intros a Ha. cbv beta in Ha. left. lia. }
  assert (HF1 : cf_frame m1) by (exists v0; exact FR).
  assert (ESP : bv_unsigned (GR (ms_regs ms') 2) = spZ regs - 48).
  { rewrite E2. change (bv_unsigned (GR regs 2)) with (spZ regs). apply cf_u64. lia. }
  assert (SP1 : spZ (ms_regs ms') = spZ regs + -48)
    by (change (spZ (ms_regs ms')) with (bv_unsigned (GR (ms_regs ms') 2)); rewrite ESP; lia).
  assert (UN : bv_unsigned (Z_to_bv 64 n) = n) by (apply cf_u64; unfold CF_N_MAX in Hn; lia).
  pose proof (proj1 HJ1) as HAR1.
  pose proof (wcc_leafb_asan_cells B HCELLS lyc Sc W m1 md' HAR1) as HAC1.
  assert (HE1 : YK0s.ret_ok (YK11.getr (ms_regs ms') 1)).
  { change (YK11.getr (ms_regs ms') 1) with (GR (ms_regs ms') 1). rewrite E1.
    apply YK0s.ret_ok_even. vm_compute. reflexivity. }
  (* +0x34: the leaf; its post becomes the inner journal at the return *)
  eapply SRr_bind.
  { eapply (wcc_leafb_journal B LAWS W (ms_regs ms') m1 CF_STK (spZ regs) (@nil (Z * Z))
      lyc Sc W memc mdc (@nil (Z * Z)) lyc Sc md' 0 (-48) CF_LEAF
      (Some (PFC.fwd_class_result (bv_unsigned (Z_to_bv 64 n)) (bv_unsigned (Z_to_bv 64 bc)) bs))
      (@nil (Z * Z)) (fun _ => True) HJ1).
    - exact SP1.
    - reflexivity.
    - lia.
    - unfold YG0d.ESTACK, CF_STK, CF_FRAME, ESTACK. lia.
    - exact HE1.
    - exact (eq_trans E3 Hgp).
    - exact (eq_trans E4 Htp).
    - intros a Ha. unfold LCK.in_wr in Ha. inversion Ha.
    - intros HPRE.
      pose proof (LEAF fx) as LF.
      unfold wire_leaf_at, LFC.wire_rp_fwd_class_cg in LF.
      specialize (LF lyc Sc W (ms_regs ms') m1 md' bs (spZ regs - CF_STK) HPRE). cbv zeta in LF.
      rewrite ESP, E10', E11', E12' in LF.
      unfold LFF.RP_FWD_CLASS_FRAME, LFF.RP_FWD_CLASS_SPAN in LF.
      apply LF; clear LF.
      + eapply (wcc_leafb_stk_journal B); [exact HJ1 | lia | lia].
      + lia.
      + rewrite UN. intros H18.
        destruct (Hblk ltac:(lia)) as (bA & nA & HbA & HbA1 & HbA2).
        pose proof (al_blocks _ _ LAWS lyc Sc W m1 md' bA nA HAR1 HbA) as (_ & HA4 & HAc & _).
        assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia).
        assert (UF : bv_unsigned (Z_to_bv 64 f) = f) by (apply cf_u64; lia).
        rewrite UF.
        split; [lia|].
        split.
        { apply (wcc_leafb_bytes_garr8 W m1 f bs (cf_garr8_at m1 md' 0 HJ1 ltac:(lia))); lia. }
        split; [unfold AKA.off_stk; rewrite ESP; left; lia|].
        split; [apply (@wcc_leafb_app_stack rc); lia|].
        split; [apply (@wcc_leafb_app_stack rc); lia|].
        split; [exact HAC1|].
        split; [unfold AKA.off_stk; rewrite ESP; left; unfold AC.GOT_CELL_K; lia|].
        split; [unfold AKA.off_stk; rewrite ESP; left; unfold AC.CELL_K; lia|].
        apply (wcc_leafb_addressable_block B LAWS lyc Sc W m1 md' bA nA f 18 HAR1 HbA); lia.
      + eapply (wcc_leafb_rng_journal B); [exact HJ1 | lia | lia].
      + intros _. exact (proj1 (wcc_leafb_rng_cells W)).
      + intros _. exact (proj2 (wcc_leafb_rng_cells W)).
      + rewrite UN. intros H18.
        destruct (Hblk ltac:(lia)) as (bA & nA & HbA & HbA1 & HbA2).
        pose proof (al_blocks _ _ LAWS lyc Sc W m1 md' bA nA HAR1 HbA) as (_ & HA4 & HAc & _).
        assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia).
        assert (UF : bv_unsigned (Z_to_bv 64 f) = f) by (apply cf_u64; lia).
        rewrite UF.
        apply (wcc_leafb_rng_block B LAWS lyc Sc W m1 md' bA nA f 18 HAR1 HbA); lia.
      + rewrite UN. intros H18.
        destruct (Hblk ltac:(lia)) as (bA & nA & HbA & HbA1 & HbA2).
        pose proof (al_blocks _ _ LAWS lyc Sc W m1 md' bA nA HAR1 HbA) as (_ & HA4 & HAc & _).
        assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia).
        assert (UF : bv_unsigned (Z_to_bv 64 f) = f) by (apply cf_u64; lia).
        rewrite UF.
        apply (wcc_leafb_rng_shadow_block B LAWS lyc Sc W m1 md' bA nA f 18 HAR1 HbA); lia. }
  cbv beta.
  intros W2 c2 _ (-> & regs2 & m2 & md2 & -> & HJ2 & HP2 & H10'' & Heff2 & Hpres2 & _).
  change (YK11.getr (ms_regs ms') 1) with (GR (ms_regs ms') 1). rewrite E1.
  apply (cf_at_ret regs2 m2 md2 HJ2).
  - apply (cf_frame_kept m1 m2 HF1 (cf_win _ _ _ _ _ _ HJ1) (cf_win _ _ _ _ _ _ HJ2)).
    intros a Ha. apply Heff2.
    + lia.
    + rewrite SP1. unfold YG0d.ESTACK. lia.
    + intros Hw. unfold LCK.in_wr in Hw. inversion Hw.
  - etransitivity; [apply (HP2 2); unfold acallee_saved; lia|]. exact E2.
  - etransitivity; [apply (HP2 3); unfold acallee_saved; lia|]. exact E3.
  - etransitivity; [apply (HP2 4); unfold acallee_saved; lia|]. exact E4.
  - etransitivity; [apply (HP2 8); unfold acallee_saved; lia|]. exact E8.
  - etransitivity; [apply (HP2 9); unfold acallee_saved; lia|]. exact E9.
  - etransitivity; [apply (HP2 18); unfold acallee_saved; lia|]. exact E18.
  - etransitivity; [apply (HP2 19); unfold acallee_saved; lia|]. exact E19.
  - etransitivity; [apply (HP2 20); unfold acallee_saved; lia|]. exact E20.
  - etransitivity; [apply (HP2 21); unfold acallee_saved; lia|]. exact E21.
  - etransitivity; [apply (HP2 22); unfold acallee_saved; lia|]. exact E22.
  - etransitivity; [apply (HP2 23); unfold acallee_saved; lia|]. exact E23.
  - etransitivity; [apply (HP2 24); unfold acallee_saved; lia|]. exact E24.
  - etransitivity; [apply (HP2 25); unfold acallee_saved; lia|]. exact E25.
  - etransitivity; [apply (HP2 26); unfold acallee_saved; lia|]. exact E26.
  - etransitivity; [apply (HP2 27); unfold acallee_saved; lia|]. exact E27.
  - exact (H10'' _ eq_refl).
Qed.

End Entry.

Theorem cf_walk : wire_check_forward_cg B MT (wire_sigma WS_check_forward).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs f n bc bs.
  intros HJ Hra Hra4 Hgp Htp H10 H11 H12 Hal Hwlo Hwhi Hn Hlen Hbc Hblk Hgarr Hnev.
  eapply cf_entry; eassumption.
Qed.
End Walk.

(* The frozen statement: every premise of the walk is a premise of wire_check_forward_holds_stmt. *)
Theorem wire_check_forward_holds {fx : YK11.FPState} {rc : YM05.RunCeil} (B : asyms) (MT : ameter_ops) :
  wire_check_forward_holds_stmt B MT.
Proof.
  intros HCELLS LAWS MTL LEAF.
  apply cf_walk; assumption.
Qed.
