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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/A/Prog/check_width_cgW.v, with its module paths, module names and numbers changed; 316 of its 451 lines of code are new or changed and 586 lines of the source are left out. *)
(* check_forward_cgW: Theorem wire_check_forward_cg_holds : wire_check_forward_holds_stmt (lib/B/Prog/check_forward_cg.v),
   at fuzz_wire.asan-ubsan (check_forward at 0x7fda4 = wire_sigma WS_check_forward).
   The walk (offsets from the entry; lib/B/Prog/WireCfBSegs.v holds the footprint runs):
     1. an INNER journal at the entry state (YCbq.v ajournal_sub_init): stack window [spZ regs - CF_STK, spZ regs),
        no footprint, no frame of its own;
     2. cf_seg1_F: the 0x30-byte frame (ra, s0 .. s3 saved), s1 := bcast, s2 := n, s3 := the shadow base,
        s0 := f; the inner journal follows the frame write (YCbq.v ajournal_exec);
     3. `jal rp_fwd_class` at +0x34: the statement's wire_leaf_at premise, read by WireCcLeafb.v wcc_leafb_journal
        (the leaf's dleaf_post becomes the inner journal at the return, a0 = fwd_class_result n bcast of the bytes);
        the leaf's buffer premises (past its n >= 18 guard) come from the statement's block premise: f lies in a
        block of the caller, below alloc_ceiling and so off the stack, addressable, its n bytes kept by the journal;
     4. cf_seg2_F: from the return, the guard, the five shadow-checked reads, the want in a1, `bne a0, a1` not
        taken, the frame reloaded, `ret` to the caller's ra (YK0s.v ret_ok);
     5. the post: the outer journal by YCbq.v ajournal_sub, acall_kept by YCbq.v acall_kept_of_journal; nothing is
        allocated and nothing charged (CF_EV = 0, mo_le at 0). *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n YA0o YK1b.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YI00.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YCbq YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI16 YI5b YI5c YP09 YO0f YK0g.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Frame Cells Step Regs6ss.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require YE2k Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import WirePSyms WirePAddr WireCg check_forward_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import WireCfBSegs WireCcLeafb.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require LeafCgKit LeafCgFacts LeafCgGlue WirePImg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require rp_fwd_class_cg rp_fwd_class_F_c AsanKA.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_fwd_class_c.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.LeafCgKit.
Module BC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.AsanCells.
Module BImg := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Img0.
Module LFC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_fwd_class_cg.
Module FFC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_fwd_class_F_c.
Module PFC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_fwd_class_c.
Module AKA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.AsanKA.
Module YK0g := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK0g.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ======================================================================== *)
(* Image-free helpers (check_value_cgW.v:56-260; a numeral word's value is lib/Reusable/YK0g.v fg_lit)       *)
(* ======================================================================== *)

Lemma cf_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof. exact WirePImg.wire_segs_low. Qed.

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
  rw_cells BImg.rsegs m A cs ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) -> m' (wa a) = m (wa a)) ->
  rw_cells BImg.rsegs m' A cs.
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

(* A footprint run from cgif's configuration at pc, carried into SRr (check_value_cgW.v cv_run, with the bridge of
   lib/B/Prog/LeafCgFacts.v): the walk continues from every state the transported run can reach. *)
Lemma cf_run {fx : YK11.FPState} : forall (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (pc : Z) (P : machine_state -> Prop) (Q : world tfibsegs -> config -> Prop),
  ExecF.evtF BImg.rsegs (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) P (@LCK.ms_of_regs fx pc regs mem) ->
  (forall ms' md', (exists ms0, P ms0 /\ ms_eqv ms0 ms') -> same_but_materialized md md' ->
     SRr tfibsegs W (mkCfg ms' md') Q) ->
  SRr tfibsegs W (@cfg_at fx tfibsegs pc regs mem md) Q.
Proof.
  intros W regs mem md pc P Q Hrun K. unfold cfg_at.
  pose proof (LeafCgGlue.evtF_eqv BImg.rsegs _ P _ _ Hrun (@LeafCgGlue.ms_of_regs_eqv fx pc regs mem)) as Hrun'.
  apply (LeafCgFacts.bridge_evtF_stmt_YA0n W _ md _ _ Q Hrun' (cf_fp_avoids W)).
  intros ms' md' (ms1 & HP & HE & _) Hs. apply K; [exists ms1; split; assumption | exact Hs].
Qed.

(* A state register-equivalent to an MS form with the cgif float state is that cgif state. *)
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

(* The registers of a state register-equivalent to an `mkR` state. *)
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

(* The return address of the leaf call: even, above the null page, a numeral. *)
Lemma cf_ra_leaf : bv_unsigned (Z_to_bv 64 CF_RET_LEAF) mod 2 = 0 /\ 4096 <= bv_unsigned (Z_to_bv 64 CF_RET_LEAF) /\
  bv_unsigned (Z_to_bv 64 CF_RET_LEAF) = CF_RET_LEAF.
Proof. split; [|split]; vm_compute; first [reflexivity | discriminate]. Qed.

(* ======================================================================== *)
(* The walk                                                                   *)
(* ======================================================================== *)

Section Walk.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation sink := YE2k.tfib_sink_head.
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
  eapply (ajournal_exec segs B LAWS cf_segs_low STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc mdc'
            (fun _ => False) HJ).
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

Local Abbreviation POST := (@wire_cf_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs).
(* The inner journal: from the entry state, stack window [spZ regs - CF_STK, spZ regs). *)
Local Abbreviation JI ly1 S1 W1 m1 md1 k1 :=
  (ajournalA CF_STK (spZ regs) [] lyc Sc W memc mdc [] ly1 S1 W1 m1 md1 k1).
Local Abbreviation GR rg i := (YK11.getr rg (Z_to_bv 5 i)).

(* The frame the prologue wrote: 8 unused bytes, then the caller's s3, s2, s1, s0, ra at [spZ regs - 0x28, spZ regs). *)
Definition cf_frame (m : word -> option byte) : Prop :=
  exists v0, rw_cells BImg.rsegs m (spZ regs - 48)
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

Lemma cf_sp_rng : YM05.alloc_ceiling + CF_STK <= spZ regs /\ spZ regs <= 2 ^ 47.
Proof.
  pose proof cf_JI0 as J. destruct J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    (_ & _ & Hc & Hlo & Hhi & H47 & _) & _).
  lia.
Qed.

Lemma cf_win : forall ly1 S1 W1 m1 md1 k1, JI ly1 S1 W1 m1 md1 k1 ->
  forall a, spZ regs - CF_STK <= a < spZ regs -> apresent (w_H W1) m1 a.
Proof.
  intros ly1 S1 W1 m1 md1 k1 J.
  destruct J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). exact Hpres.
Qed.

Lemma cf_AR : forall ly1 S1 W1 m1 md1 k1, JI ly1 S1 W1 m1 md1 k1 -> AR segs B ly1 S1 W1 m1 md1.
Proof. intros ly1 S1 W1 m1 md1 k1 J. destruct J as (HAR & _). exact HAR. Qed.

(* The caller's block that holds f (when n > 0), with its bounds: below alloc_ceiling, so off the stack. *)
Lemma cf_blk : 0 < n -> exists bA nA, In (bA, nA) (ablocks B lyc Sc) /\ 4096 <= bA /\ bA <= f /\
  f + n <= bA + req_size nA /\ bA + req_size nA <= YM05.alloc_ceiling.
Proof.
  intros Hn0. destruct (Hblk Hn0) as (bA & nA & HbA & HbA1 & HbA2).
  assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ bA nA cf_HARc HbA) as (_ & H4096 & Hc & _).
  exists bA, nA. split; [exact HbA|]. lia.
Qed.

(* The n bytes of f at a state of the inner journal over the caller's blocks: the journal keeps every byte of a
   caller block that is still live (YCbq.v ajournal, the kept-block clause), and the entry's garr8 gives them. *)
Lemma cf_buf_bytes : forall m1 md1 k1, JI lyc Sc W m1 md1 k1 -> 0 < n -> bytes_at BImg.rsegs m1 f bs.
Proof.
  intros m1 md1 k1 J1 Hn0.
  destruct (cf_blk Hn0) as (bA & nA & HbA & H4096 & HbA1 & HbA2 & Hc).
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  assert (BAc : bytes_at BImg.rsegs memc f bs)
    by exact (wcc_leafb_bytes_garr8 W memc f bs Hgarr ltac:(lia) ltac:(rewrite Hlen; lia)).
  destruct BAc as (B0 & B1 & B2). split; [exact B0|]. split; [exact B1|].
  intros i Hi. rewrite <- (B2 i Hi).
  pose proof J1 as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  assert (Hin : bA <= f + Z.of_nat i < bA + req_size nA) by lia.
  assert (Ev : aview segs (w_H W) m1 (f + Z.of_nat i) = aview segs (w_H W) memc (f + Z.of_nat i)).
  { replace (f + Z.of_nat i) with (bA + (f + Z.of_nat i - bA)) by lia.
    apply (F2 bA nA (f + Z.of_nat i - bA) HbA HbA ltac:(lia) ltac:(intros (r0 & Hr0 & _); destruct Hr0)). }
  destruct (al_blocks _ _ LAWS _ _ _ _ _ bA nA cf_HARc HbA) as (_ & _ & _ & _ & Pc & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ bA nA HAR1 HbA) as (_ & _ & _ & _ & P1 & _).
  pose proof (cf_byte_eq (w_H W) (w_H W) memc m1 (f + Z.of_nat i) (proj1 (Pc _ Hin)) (proj1 (P1 _ Hin)) Ev) as E.
  unfold mrd, wa. rewrite E. reflexivity.
Qed.

(* The frame [spZ regs - 48, spZ regs) lies above the leaf's window [spZ regs - 48 - ESTACK, spZ regs - 48). *)
Lemma cf_frame_kept : forall (W1 W2 : world segs) (m1 m2 : word -> option byte),
  cf_frame m1 ->
  (forall a, spZ regs - CF_STK <= a < spZ regs -> apresent (w_H W1) m1 a) ->
  (forall a, spZ regs - CF_STK <= a < spZ regs -> apresent (w_H W2) m2 a) ->
  (forall a, spZ regs - 48 <= a < spZ regs -> aview segs (w_H W2) m2 a = aview segs (w_H W1) m1 a) ->
  cf_frame m2.
Proof.
  intros W1 W2 m1 m2 (v0 & F) P1 P2 E. exists v0.
  pose proof cf_sp_rng as [S1 S2].
  apply (cf_rw_cells_ext m1 m2 _ _ F). intros a Ha.
  change (Z.of_nat (cells_size (C8 v0 :: cf_fr (GR regs 19) (GR regs 18) (GR regs 9) (GR regs 8) (GR regs 1))))
    with 48 in Ha.
  unfold wa. apply (cf_byte_eq (w_H W1) (w_H W2) m1 m2 a); [apply P1 | apply P2 | apply E];
    unfold CF_STK, CF_FRAME, ESTACK in *; lia.
Qed.

(* ======================================================================== *)
(* The walk, from the entry                                                   *)
(* ======================================================================== *)

Lemma cf_entry : SRr segs W (@cfg_at fx segs CF_ENTRY regs memc mdc) POST.
Proof.
  pose proof cf_sp_rng as [Hsp1 Hsp2].
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  pose proof cf_JI0 as JI0.
  pose proof (cf_win _ _ _ _ _ _ JI0) as Hpres0.
  assert (EST : CF_STK = 48 + 4096) by reflexivity.
  destruct (wcc_leafb_asan_cells B HCELLS lyc Sc W memc mdc cf_HARc) as (CK & GCK & _).
  assert (E10 : GR regs 10 = Z_to_bv 64 (bv_unsigned (GR regs 10))) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (E11 : GR regs 11 = Z_to_bv 64 (bv_unsigned (GR regs 11))) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (E12 : GR regs 12 = Z_to_bv 64 (bv_unsigned (GR regs 12))) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (zr_word (GR regs 10)) as R10. pose proof (zr_word (GR regs 11)) as R11.
  pose proof (zr_word (GR regs 12)) as R12. unfold inr64 in R10, R11, R12.
  (* the prologue *)
  eapply (@cf_run fx W regs memc mdc CF_ENTRY).
  { unfold LCK.ms_of_regs. rewrite E10, E11, E12.
    eapply cf_seg1_F with (lo := spZ regs - CF_STK).
    all: try change (bv_unsigned (GR regs 2)) with (spZ regs).
    - exact R10.
    - exact R11.
    - exact R12.
    - apply (wcc_leafb_stk W memc); [lia | lia | exact Hpres0].
    - lia.
    - exact GCK.
    - exact CK.
    - unfold BC.CELL_K. lia.
    - eapply (wcc_leafb_rng_journal B); [exact JI0 | lia | lia].
    - exact (proj1 (wcc_leafb_rng_cells W)).
    - exact (proj2 (wcc_leafb_rng_cells W)). }
  intros ms' md' (ms0 & (m1 & v0 & -> & MU & WM & FR) & EQV) SBM.
  change (bv_unsigned (GR regs 2)) with (spZ regs) in MU, FR.
  destruct (cf_regs_of EQV) as (E1 & E2 & E3 & E4 & E8 & E9 & E10' & E11' & E12' & E18 & E19 & E20 & E21 & E22 &
    E23 & E24 & E25 & E26 & E27).
  change (bv_unsigned (GR regs 2)) with (spZ regs) in E2.
  rewrite <- E10 in E8, E10'. rewrite <- E11 in E11', E18. rewrite <- E12 in E9, E12'.
  rewrite (cf_ms_shape _ _ _ _ EQV).
  (* the inner journal after the frame write *)
  assert (HJ1 : JI lyc Sc W m1 md' 0).
  { apply (ajournal_exec segs B LAWS cf_segs_low CF_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W memc mdc 0 m1 md'
             (fun a => spZ regs - 48 <= a < spZ regs) JI0).
    - intros x Hx. unfold mrestrict. rewrite (MU x); [reflexivity|]. cbn [outside]. split; [exact Hx | exact I].
    - intros x Hx. unfold mrestrict in *. revert Hx. destruct (w_H W x) eqn:Ehx; intros Hx; [exact Hx|].
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs - 48)) as [Hl|Hl];
        [rewrite (MU x); [exact Hx | cbn [outside]; split; [lia | exact I]]|].
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [Hh|Hh];
        [|rewrite (MU x); [exact Hx | cbn [outside]; split; [lia | exact I]]].
      assert (Hxr : spZ regs - CF_STK <= bv_unsigned x < spZ regs) by lia.
      destruct (Hpres0 _ Hxr) as [_ (b & Hb)].
      assert (Hw : wview BImg.rsegs m1 x <> None).
      { refine (WM x _). unfold wview. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
      unfold wview in Hw. destruct (m1 x) as [b'|] eqn:Em1; [discriminate|]. exfalso.
      rewrite (LeafCgGlue.find_segment_out BImg.rsegs (bv_unsigned x) 1) in Hw; [exact (Hw eq_refl)|lia|].
      intros sg Hin Hr. pose proof (cf_segs_low (bv_unsigned x) (ex_intro _ sg (conj Hin Hr))) as Hlow.
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
  pose proof (cf_AR _ _ _ _ _ _ HJ1) as HAR1.
  assert (ESP : bv_unsigned (GR (ms_regs ms') 2) = spZ regs - 48) by (rewrite E2; apply YK0g.fg_lit; lia).
  assert (SP1 : spZ (ms_regs ms') = spZ regs + -48) by (change (spZ (ms_regs ms')) with (bv_unsigned (GR (ms_regs ms') 2)); lia).
  (* the buffer, when the leaf reads it (n >= 18) *)
  assert (EN : bv_unsigned (GR regs 11) = n)
    by (assert (H11' : GR regs 11 = Z_to_bv 64 n) by exact H11; rewrite H11'; apply YK0g.fg_lit;
        unfold CF_N_MAX in Hn; lia).
  assert (BUF : 18 <= n -> exists bA nA, In (bA, nA) (ablocks B lyc Sc) /\ 4096 <= bA /\ bA <= f /\
      f + n <= bA + req_size nA /\ bA + req_size nA <= YM05.alloc_ceiling /\ bv_unsigned (GR regs 10) = f).
  { intros H18. destruct (cf_blk ltac:(lia)) as (bA & nA & HbA & H4096 & HbA1 & HbA2 & Hc).
    exists bA, nA. split; [exact HbA|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    assert (H10' : GR regs 10 = Z_to_bv 64 f) by exact H10. rewrite H10'. apply YK0g.fg_lit. lia. }
  (* `jal rp_fwd_class` at +0x34: the leaf's post becomes the inner journal at the return *)
  eapply SRr_bind.
  { eapply (wcc_leafb_journal B LAWS W (ms_regs ms') m1 CF_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc md' 0
      (-48) CF_LEAF
      (Some (PFC.fwd_class_result n (bv_unsigned (GR (ms_regs ms') 12)) bs))
      [] (fun _ => True) HJ1).
    - exact SP1.
    - reflexivity.
    - lia.
    - unfold CF_STK, CF_FRAME. try unfold ESTACK. try unfold LCK.ESTACK. lia.
    - assert (RA : YK0s.ret_ok (GR (ms_regs ms') 1))
        by (rewrite E1; apply YK0s.ret_ok_even; exact (proj1 cf_ra_leaf)).
      exact RA.
    - exact (eq_trans E3 Hgp).
    - exact (eq_trans E4 Htp).
    - intros a Ha. unfold LCK.in_wr in Ha. inversion Ha.
    - intros HPRE.
      pose proof (LEAF fx) as LF.
      unfold wire_leaf_at, LFC.wire_rp_fwd_class_cg in LF.
      specialize (LF lyc Sc W (ms_regs ms') m1 md' bs (spZ regs - CF_STK) HPRE). cbv zeta in LF.
      rewrite ESP, E11', EN in LF. unfold FFC.RP_FWD_CLASS_FRAME, FFC.RP_FWD_CLASS_SPAN in LF.
      apply LF; clear LF.
      + eapply (wcc_leafb_stk_journal B); [exact HJ1 | lia | lia].
      + lia.
      + intros H18. destruct (BUF H18) as (bA & nA & HbA & H4096 & HbA1 & HbA2 & Hc & EF).
        rewrite E10', EF.
        split; [lia|].
        split; [lia|].
        split; [exact (cf_buf_bytes m1 md' 0 HJ1 ltac:(lia))|].
        split; [unfold AKA.off_stk; rewrite ESP; left; lia|].
        split; [apply (@wcc_leafb_app_stack rc); lia|].
        split; [apply (@wcc_leafb_app_stack rc); lia|].
        split; [exact (wcc_leafb_asan_cells B HCELLS lyc Sc W m1 md' HAR1)|].
        split; [unfold AKA.off_stk; rewrite ESP; left; unfold BC.GOT_CELL_K; lia|].
        split; [unfold AKA.off_stk; rewrite ESP; left; unfold BC.CELL_K; lia|].
        exact (wcc_leafb_addressable_block B LAWS lyc Sc W m1 md' bA nA f 18 HAR1 HbA ltac:(lia) ltac:(lia) ltac:(lia)).
      + eapply (wcc_leafb_rng_journal B); [exact HJ1 | lia | lia].
      + intros _. exact (proj1 (wcc_leafb_rng_cells W)).
      + intros _. exact (proj2 (wcc_leafb_rng_cells W)).
      + intros H18. destruct (BUF H18) as (bA & nA & HbA & H4096 & HbA1 & HbA2 & Hc & EF).
        rewrite E10', EF.
        exact (wcc_leafb_rng_block B LAWS lyc Sc W m1 md' bA nA f 18 HAR1 HbA ltac:(lia) ltac:(lia)).
      + intros H18. destruct (BUF H18) as (bA & nA & HbA & H4096 & HbA1 & HbA2 & Hc & EF).
        rewrite E10', EF.
        exact (wcc_leafb_rng_shadow_block B LAWS lyc Sc W m1 md' bA nA f 18 HAR1 HbA ltac:(lia) ltac:(lia) ltac:(lia)). }
  cbv beta.
  intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hres & Heff & Hgr & _).
  (* the registers at the return *)
  assert (V : forall r, acallee_saved r -> GR regs2 r = GR (ms_regs ms') r) by (intros r Hr; exact (HP2 r Hr)).
  assert (V2 : GR regs2 2 = GR (ms_regs ms') 2) by (apply V; hnf; lia).
  assert (V3 : GR regs2 3 = GR regs 3) by (rewrite (V 3 ltac:(hnf; lia)); exact E3).
  assert (V4 : GR regs2 4 = GR regs 4) by (rewrite (V 4 ltac:(hnf; lia)); exact E4).
  assert (V8 : GR regs2 8 = GR regs 10) by (rewrite (V 8 ltac:(hnf; lia)); exact E8).
  assert (V9 : GR regs2 9 = GR regs 12) by (rewrite (V 9 ltac:(hnf; lia)); exact E9).
  assert (V18 : GR regs2 18 = GR regs 11) by (rewrite (V 18 ltac:(hnf; lia)); exact E18).
  assert (V19 : GR regs2 19 = Z_to_bv 64 BC.ASAN_K) by (rewrite (V 19 ltac:(hnf; lia)); exact E19).
  assert (VR : forall r, 20 <= r <= 27 -> GR regs2 r = GR regs r).
  { intros r Hr. rewrite (V r ltac:(hnf; lia)).
    assert (Hc : r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; assumption. }
  assert (ESP2 : bv_unsigned (GR regs2 2) = spZ regs - 48) by (rewrite V2; exact ESP).
  (* the frame, kept by the leaf (it lies above the leaf's window) *)
  assert (HF2 : cf_frame mem2).
  { apply (cf_frame_kept W W m1 mem2 HF1 (cf_win _ _ _ _ _ _ HJ1) (cf_win _ _ _ _ _ _ HJ2)).
    intros a Ha. apply Heff.
    - lia.
    - change (spZ (ms_regs ms')) with (bv_unsigned (GR (ms_regs ms') 2)). rewrite ESP.
      try unfold ESTACK. try unfold LCK.ESTACK. lia.
    - intros Hw. unfold LCK.in_wr in Hw. inversion Hw. }
  destruct HF2 as (v2 & FR2).
  lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ _ ?pcw _ _) _) _ =>
    replace pcw with (Z_to_bv 64 CF_RET_LEAF) by (symmetry; exact E1) end.
  (* the return of the leaf to the ret *)
  change (SRr segs W (@cfg_at fx segs CF_RET_LEAF regs2 mem2 md2) POST).
  eapply (@cf_run fx W regs2 mem2 md2 CF_RET_LEAF).
  { unfold LCK.ms_of_regs.
    replace (spZ regs - 48) with (bv_unsigned (GR regs2 2)) in FR2 by exact ESP2.
    eapply cf_seg2_F.
    - exact FR2.
    - rewrite ESP2. eapply (wcc_leafb_rng_journal B); [exact HJ2 | lia | lia].
    - exact V19.
    - etransitivity; [exact (Hres _ eq_refl)|]. rewrite V18, V9, E12', EN. reflexivity.
    - intros H18. rewrite V18, EN in H18. rewrite V8.
      destruct (BUF H18) as (bA & nA & HbA & H4096 & HbA1 & HbA2 & Hc & EF). rewrite EF.
      pose proof (cf_AR _ _ _ _ _ _ HJ2) as HAR2.
      split; [lia|].
      split; [exact (cf_buf_bytes mem2 md2 0 HJ2 ltac:(lia))|].
      split; [exact (wcc_leafb_addressable_block B LAWS lyc Sc W mem2 md2 bA nA f 18 HAR2 HbA ltac:(lia) ltac:(lia) ltac:(lia))|].
      split; [exact (wcc_leafb_rng_block B LAWS lyc Sc W mem2 md2 bA nA f 18 HAR2 HbA ltac:(lia) ltac:(lia))|].
      replace (f + 17) with (f + 18 - 1) by lia.
      exact (wcc_leafb_rng_shadow_block B LAWS lyc Sc W mem2 md2 bA nA f 18 HAR2 HbA ltac:(lia) ltac:(lia) ltac:(lia)). }
  intros ms3 md3 (ms4 & POST4 & EQV4) SBM4.
  unfold cf_post in POST4. destruct POST4 as (a1' & a2' & a3' & ->).
  destruct (cf_regs_of EQV4) as (G1 & G2 & G3 & G4 & G8 & G9 & G10 & _ & _ & G18 & G19 & G20 & G21 & G22 & G23 &
    G24 & G25 & G26 & G27).
  assert (Hret : ret_pc (GR regs 1) = GR regs 1) by (apply LeafCgFacts.ret_ok_stmt_YK0s; exact Hra).
  rewrite Hret in EQV4.
  rewrite (cf_ms_shape _ _ _ _ EQV4).
  pose proof (cf_aj_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 SBM4) as J3.
  apply SRr_ret. unfold wire_cf_post.
  exists lyc, Sc, (ms_regs ms3), mem2, md3.
  split; [reflexivity|].
  split.
  { pose proof (ajournal_sub segs B LAWS cf_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
                  CF_STK (spZ regs) [] [] lyc Sc W mem2 md3 0 HJ J3 Hwlo Hwhi
                  ltac:(intros a (r0 & Hr0 & _); destruct Hr0)) as J.
    cbn [app] in J. try rewrite app_nil_r in J. exact J. }
  split.
  { intros i Hi. unfold acallee_saved in Hi.
    assert (Hc : i = 2 \/ i = 3 \/ i = 4 \/ i = 8 \/ i = 9 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/
                 i = 23 \/ i = 24 \/ i = 25 \/ i = 26 \/ i = 27) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
    - etransitivity; [exact G2|]. rewrite ESP2. replace (spZ regs - 48 + 48) with (spZ regs) by lia.
      unfold spZ. apply Z_to_bv_bv_unsigned.
    - etransitivity; [exact G3|]. exact V3.
    - etransitivity; [exact G4|]. exact V4.
    - exact G8.
    - exact G9.
    - exact G18.
    - exact G19.
    - etransitivity; [exact G20|]. exact (VR 20 ltac:(lia)).
    - etransitivity; [exact G21|]. exact (VR 21 ltac:(lia)).
    - etransitivity; [exact G22|]. exact (VR 22 ltac:(lia)).
    - etransitivity; [exact G23|]. exact (VR 23 ltac:(lia)).
    - etransitivity; [exact G24|]. exact (VR 24 ltac:(lia)).
    - etransitivity; [exact G25|]. exact (VR 25 ltac:(lia)).
    - etransitivity; [exact G26|]. exact (VR 26 ltac:(lia)).
    - etransitivity; [exact G27|]. exact (VR 27 ltac:(lia)). }
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { apply (acall_kept_of_journal segs B cf_segs_low CF_STK (spZ regs) [] [] lyc Sc W memc mdc lyc Sc W mem2
             md3 0 (fun _ => False) J3 cf_HARc).
    - intros a (r0 & Hr0 & _). destruct Hr0.
    - intros b m i Hb _ _. exact Hb.
    - exact sink_closed_nil. }
  exact (mo_le_refl MT MTL Sc).
Qed.

End Entry.

Theorem cf_walk : @wire_check_forward_cg fx rc B MT (wire_sigma WS_check_forward).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs f n bc bs.
  intros HJ Hra Hra4 Hgp Htp H10 H11 H12 Hal Hwlo Hwhi Hn Hlen Hbc Hblk Hgarr Hnev.
  eapply cf_entry; eassumption.
Qed.
End Walk.

(* The frozen statement: each premise of the walk is a premise of wire_check_forward_holds_stmt. *)
Theorem wire_check_forward_cg_holds {fx : YK11.FPState} {rc : YM05.RunCeil} (B : asyms) (MT : ameter_ops) :
  @wire_check_forward_holds_stmt fx rc B MT.
Proof.
  intros HCELLS LAWS MTL LEAF.
  exact (@cf_walk fx rc B MT HCELLS LAWS MTL LEAF).
Qed.
