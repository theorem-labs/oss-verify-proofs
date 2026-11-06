(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: copied from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_leafb.v (origin/ossv/recipes 88154566652a) for reac-repacer/fuzz_uci's image A: module paths and names changed, the cell rows are this unit's AsanCells rows, and the read-only-image helper is dropped. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/reac-repacer/fuzz_uci/lib/A/Prog/UciCcLeafb.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/UciCcLeafb.v, with its module paths and module names changed; 1106 of its 1229 lines of code are new or changed and 398 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/B/Prog/check_value_cgW.v, with its module paths, module names and numbers changed; 396 of its 628 lines of code are new or changed and 997 lines of the source are left out. *)
(* check_counter_cgW: wire_check_counter_cg (wire_sigma WS_check_counter) at image B (fuzz_wire.asan-ubsan, check_counter
   at 0x804c0; objdump of record sha256 440b9550f4f5) from the callee contract the statement names, proving the frozen
   statement lib/B/Prog/check_counter_cg.v wire_check_counter_holds_stmt. In the walk style of reac-repacer/fuzz_uci's
   lib/B/Prog/check_value_cgW.v (recipes commit 0295462466b2; its helpers copied under the prefix ccw_): the body runs
   as footprint runs (lib/B/Prog/WireCcnBSegs.v) carried into SRr by lib/B/Prog/LeafCgFacts.v bridge_evtF_stmt_YA0n,
   an inner journal over the call's stack window, and the one call, of the leaf rp_counter, cut by its leaf contract
   through the kit's lib/B/Prog/WireCcLeafb.v wcc_leafb_journal, in the form of libreac/fuzz_decode's released
   lib/B/Prog/LLVMFuzzerTestOneInput_leafb.v dec_leafb_counter (recipes commit 48907dc7e8ca).

   The walk:
     1. an INNER journal at the entry state (YCbq.v ajournal_sub_init): stack window [spZ regs - CCN_STK, spZ regs),
        no footprint, no frame of its own;
     2. n < 18: ccn_short_F, the frame written and read back, `ret`; the inner journal follows the frame write
        (YCbq.v ajournal_exec);
     3. n >= 18: ccn_seg1_F up to the call of rp_counter (the frame, s0 := f, s1 := the shadow base); the inner journal
        follows the frame write; the leaf call (ccw_leaf_call: the leaf's premises from the inner journal, f's bytes
        and shadow from the caller's block, the leaf's post back into the inner journal); ccn_seg2_F from the return
        address +0x30 to `ret` (f's bytes read through the journal's kept caller block; the property test not taken,
        as rp_counter's result is lib/Prog/rp_counter_c.v counter_result of f's bytes);
     4. the post: the outer journal by YCbq.v ajournal_sub, acall_kept by YCbq.v acall_kept_of_journal, no event and
        no meter charge. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n YA0o YK1b.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YI00.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YCbq YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI16 YI5b YI5c YP09 YO0f.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Frame Cells Step Regs6ss.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require YE2k Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import WirePSyms WirePAddr WireCg check_counter_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import WireCcnBSegs.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require LeafCgKit LeafCgFacts LeafCgGlue WirePImg WireCcLeafb AsanKA.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require rp_counter_cg rp_counter_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_counter_c.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.LeafCgKit.
Module BC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.AsanCells.
Module BImg := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Img0.
Module BKA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.AsanKA.
Module WL := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.WireCcLeafb.
Module LRC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_counter_cg.
Module RCc := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_counter_c.
Module PRC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_counter_c.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ======================================================================== *)
(* Image-free helpers (check_value_cgW.v cv_*, copied)                        *)
(* ======================================================================== *)

Lemma ccw_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof. exact WirePImg.wire_segs_low. Qed.

Lemma ccw_u64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz. Qed.

Lemma ccw_byte_eq : forall (H H' : word -> bool) (m m' : word -> option byte) (a : Z),
  apresent H m a -> apresent H' m' a -> aview tfibsegs H' m' a = aview tfibsegs H m a ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros H H' m m' a [Hh [b Hb]] [Hh' [b' Hb']] E.
  unfold aview, YP09.mbyte, mrestrict in E.
  rewrite Hh, Hh' in E. rewrite Hb, Hb' in E. cbn in E.
  injection E as E. rewrite Hb, Hb'. f_equal. apply bv_eq. exact E.
Qed.

Lemma ccw_rw_cells_ext : forall (m m' : word -> option byte) (A : Z) (cs : list cell),
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

Lemma ccw_fp_avoids : forall (W : world tfibsegs),
  LCK.fp_avoids (@w_H tfibsegs W) (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W).
Proof. intros W a n H. unfold LCK.RNG_W in H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.

(* A footprint run from cgif's configuration at pc, carried into SRr (check_value_cgW.v cv_run). *)
Lemma ccw_run {fx : YK11.FPState} : forall (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (pc : Z) (P : machine_state -> Prop) (Q : world tfibsegs -> config -> Prop),
  ExecF.evtF BImg.rsegs (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) P (@LCK.ms_of_regs fx pc regs mem) ->
  (forall ms' md', (exists ms0, P ms0 /\ ms_eqv ms0 ms') -> same_but_materialized md md' ->
     SRr tfibsegs W (mkCfg ms' md') Q) ->
  SRr tfibsegs W (@cfg_at fx tfibsegs pc regs mem md) Q.
Proof.
  intros W regs mem md pc P Q Hrun K. unfold cfg_at.
  pose proof (LeafCgGlue.evtF_eqv BImg.rsegs _ P _ _ Hrun (@LeafCgGlue.ms_of_regs_eqv fx pc regs mem)) as Hrun'.
  apply (LeafCgFacts.bridge_evtF_stmt_YA0n W _ md _ _ Q Hrun' (ccw_fp_avoids W)).
  intros ms' md' (ms1 & HP & HE & _) Hs. apply K; [exists ms1; split; assumption | exact Hs].
Qed.

Lemma ccw_ms_shape {fx : YK11.FPState} : forall (R : bvmap 5 word) (pc : word) (m : word -> option byte)
    (ms' : machine_state),
  ms_eqv (MS R (@fp_regs fx) pc (@fp_csr fx) None m (YK11.seg_rom tfibsegs)) ms' ->
  ms' = @YK11.mkst fx (ms_regs ms') pc m (YK11.seg_rom tfibsegs).
Proof.
  intros R pc m [r f p sv rv fc mm ro] (_ & Hf & Hp & Hs & Hr & Hc & Hm & Hro).
  cbn [MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
  subst. reflexivity.
Qed.

Lemma ccw_ms_reg : forall (R : bvmap 5 word) F pc fc rv m ro (ms' : machine_state) (r : bv 5),
  ms_eqv (MS R F pc fc rv m ro) ms' -> YK11.getr (ms_regs ms') r = YK11.getr R r.
Proof.
  intros R F pc fc rv m ro ms' r (HR & _). cbn [MS ms_regs] in HR. exact (LeafCgGlue.getr_xeqv _ _ HR r).
Qed.

Lemma ccw_regs_of : forall {x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
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
  repeat split; (etransitivity; [apply (ccw_ms_reg _ _ _ _ _ _ _ _ _ H) | reflexivity]).
Qed.

Lemma ccw_rng : forall (W : world tfibsegs) lo len, 0 <= lo -> lo + len <= 2 ^ 64 ->
  (forall b, lo <= b < lo + len -> w_H W (Z_to_bv 64 b) = false) ->
  ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) lo len.
Proof.
  intros W lo len H0 H1 H. split; [exact H0|]. split; [exact H1|].
  intros b j Hb Hbj. unfold LCK.RNG_W, LCK.range_avoids, LCK.woff. intros k Hk.
  rewrite (ccw_u64 b) by lia. apply H. lia.
Qed.

Lemma ccw_aview_vis : forall (W : world tfibsegs) mem a v,
  aview tfibsegs (w_H W) mem a = Some v -> w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W mem a v H. destruct (w_H W (Z_to_bv 64 a)) eqn:E; [|reflexivity]. exfalso.
  pose proof (@w_Hoff tfibsegs W _ E) as F.
  unfold aview, YP09.mbyte, mrestrict in H. rewrite E in H.
  unfold YK11.seg_rom, memory_read in H. cbn [Z.of_N] in H. rewrite F in H. discriminate H.
Qed.

Lemma ccw_aview_mrd : forall (W : world tfibsegs) mem a, w_H W (Z_to_bv 64 a) = false ->
  aview tfibsegs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (mrd BImg.rsegs mem (wa a)).
Proof. intros W mem a H. unfold aview, YP09.mbyte, mrestrict, mrd, wa. rewrite H. reflexivity. Qed.

Lemma ccw_mrd_of_aview : forall (W : world tfibsegs) mem a v,
  aview tfibsegs (w_H W) mem a = Some v -> mrd BImg.rsegs mem (wa a) = Some (Z_to_bv 8 v).
Proof.
  intros W mem a v E. pose proof (ccw_aview_vis W mem a v E) as Hv.
  rewrite (ccw_aview_mrd W mem a Hv) in E.
  destruct (mrd BImg.rsegs mem (wa a)) as [b|]; cbn in E; [|discriminate].
  injection E as E. subst v. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
  apply bv_unsigned_in_range.
Qed.

Lemma ccw_le_byte1 : forall v, 0 <= v < 256 -> Z.shiftr (v mod 2 ^ (8 * Z.of_nat 1)) (8 * Z.of_nat 0) mod 256 = v.
Proof.
  intros v Hv. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite Z.mod_small by lia. apply Z.mod_small. lia.
Qed.

Lemma ccw_garr8_aview : forall (H : word -> bool) mem a (l : list Z) (j : nat),
  garr8 tfibsegs (mrestrict H mem) a l -> (j < length l)%nat ->
  aview tfibsegs H mem (a + Z.of_nat j) = Some (nth j l 0).
Proof.
  intros H mem a l j G Hj. destruct (G j Hj) as [V R]. specialize (V 0%nat ltac:(lia)).
  rewrite Nat2Z.inj_0, Z.add_0_r in V.
  unfold aview. rewrite V. cbn [option_map]. f_equal.
  unfold YO0f.le_byte, YG0f.le_byte. rewrite Z_to_bv_unsigned, (ccw_le_byte1 _ R).
  apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

Lemma ccw_garr8_of_aview : forall (H : word -> bool) mem a (l : list Z),
  (forall j, (j < length l)%nat -> aview tfibsegs H mem (a + Z.of_nat j) = Some (nth j l 0) /\ 0 <= nth j l 0 < 256) ->
  garr8 tfibsegs (mrestrict H mem) a l.
Proof.
  intros H mem a l HA j Hj. destruct (HA j Hj) as [E R]. split; [|exact R].
  intros k Hk. assert (Ek : k = 0%nat) by lia. subst k. rewrite Nat2Z.inj_0, Z.add_0_r.
  unfold aview in E.
  destruct (YP09.mbyte tfibsegs (mrestrict H mem) (a + Z.of_nat j)) as [b|] eqn:Eb; cbn in E; [|discriminate].
  injection E as E. f_equal. apply bv_eq. unfold YO0f.le_byte, YG0f.le_byte.
  rewrite Z_to_bv_unsigned, (ccw_le_byte1 _ R), <- E.
  symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* The bytes as numbers, and as the C model reads them. *)
Lemma ccw_nth_map : forall (bs : list byte) j,
  nth j (map (fun b : byte => bv_unsigned b) bs) 0 = bv_unsigned (nth j bs (Z_to_bv 8 0)).
Proof.
  induction bs as [|b bs IH]; intros j; destruct j as [|j]; cbn [nth map]; try reflexivity. apply IH.
Qed.

Lemma ccw_nth_rng : forall (bs : list byte) j, 0 <= nth j (map (fun b : byte => bv_unsigned b) bs) 0 < 256.
Proof.
  intros bs j. rewrite ccw_nth_map. pose proof (bv_unsigned_in_range 8 (nth j bs (Z_to_bv 8 0))) as R.
  unfold bv_modulus in R. cbn in R. lia.
Qed.

Lemma ccw_stk_present : forall (H : word -> bool) m lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> apresent H m a) -> stk BImg.rsegs m lo hi.
Proof.
  intros H m lo hi H0 H1 Hp. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (Hp a Ha) as [_ [b Hb]]. unfold wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold mrd. rewrite Hb. reflexivity.
Qed.

(* The return address of the call of rp_counter: its value, parity and size. *)
Lemma ccw_ra : bv_unsigned (Z_to_bv 64 CCN_RET) = CCN_RET /\
  bv_unsigned (Z_to_bv 64 CCN_RET) mod 2 = 0 /\ 4096 <= bv_unsigned (Z_to_bv 64 CCN_RET).
Proof. split; [|split]; vm_compute; first [reflexivity | discriminate]. Qed.

Lemma ccw_leaf_pc : CCN_LEAF = RCc.RP_COUNTER.
Proof. reflexivity. Qed.

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
Hypothesis ALEAF : forall fx' : YK11.FPState, @wire_leaf_at rc B (@LRC.wire_rp_counter_cg) fx'.
Local Abbreviation ajournalA := (@ajournal rc sink segs B).

(* A run that writes no memory: the journal follows its same_but_materialized (check_value_cgW.v cv_aj_md). *)
Lemma ccw_aj_md : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k mdc',
  ajournalA STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k -> same_but_materialized mdc mdc' ->
  ajournalA STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc' k.
Proof.
  intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k mdc' HJ Hs.
  eapply (ajournal_exec segs B LAWS ccw_segs_low STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc mdc'
            (fun _ => False) HJ).
  - intros x _. reflexivity.
  - apply YK1b.mem_grows_refl.
  - intros x _. reflexivity.
  - exact Hs.
  - intros a Ha. destruct Ha.
Qed.

(* The leaf call (LLVMFuzzerTestOneInput_leafb.v dec_leafb_counter, at a pointer f inside a caller block): rp_counter
   reads the two counter bytes at f + 14 and writes nothing but its own frame. *)
Lemma ccw_leaf_call :
  forall (W : world segs) (regsT : bvmap 5 word) memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k
         (o f n bA nA : Z) (bs : list byte),
  ajournalA STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> LCK.ESTACK - o <= STK ->
  YK0s.ret_ok (YK11.getr regsT 1) -> YK11.getr regsT 3 = w64 (as_gp B) -> YK11.getr regsT 4 = w64 (as_tp B) ->
  YK11.getr regsT 10 = w64 f ->
  In (bA, nA) (ablocks B lyc Sc) -> bA <= f -> f + n <= bA + nA -> 16 <= n -> Z.of_nat (length bs) = n ->
  garr8 segs (mrestrict (w_H W) memT) f (map (fun b : byte => bv_unsigned b) bs) ->
  SRr segs W (mkCfg (YK11.mkst regsT (Z_to_bv 64 RCc.RP_COUNTER) memT (YK11.seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (YK11.mkst regs2 (YK11.getr regsT 1) mem2 (YK11.seg_rom segs)) md2 /\
       ajournalA STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       aregs_preserved regsT regs2 /\
       YK11.getr regs2 10 = w64 (PRC.counter_result bs) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - LCK.ESTACK <= a < spZ regsT) ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
  intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o f n bA nA bs
    HJ Hsp Hal Hneg Hbud Hra Hgp Htp H10 Hin Hf1 Hf2 Hn16 Hbs HG.
  pose proof (proj1 HJ) as HAR.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil0 & Hslo & Hshi & H47 & _).
  pose proof Hbud as Hbud4. unfold LCK.ESTACK in Hbud4.
  pose proof (@YM05.alloc_ceiling_val rc) as HCEIL.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ bA nA HAR Hin) as (_ & H4096 & Hceil & Happ & _ & _ & Hmr).
  pose proof (req_size_pos nA ltac:(lia)) as [Hq1 Hq2].
  assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia).
  assert (Ha0L : bv_unsigned (YK11.getr regsT (Z_to_bv 5 10)) = f).
  { assert (Hx : bv_unsigned (YK11.getr regsT 10) = f)
      by (rewrite H10; unfold w64; apply ccw_u64; lia).
    exact Hx. }
  assert (HspL : bv_unsigned (YK11.getr regsT (Z_to_bv 5 2)) = sp0 + o) by exact Hsp.
  eapply SRr_mono;
    [ eapply (WL.wcc_leafb_journal B LAWS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o
                RCc.RP_COUNTER (Some (PRC.counter_result bs)) [] (fun _ => True)
                HJ Hsp Hal Hneg Hbud Hra Hgp Htp)
    | cbv beta; intros W2 c2 _ (-> & regs2 & mem2 & md2 & Hc2 & HJ2 & Hp2 & Hres2 & Heff2 & Hgr2 & _);
      split; [reflexivity|]; exists regs2, mem2, md2;
      split; [exact Hc2|]; split; [exact HJ2|]; split; [exact Hp2|];
      split; [exact (Hres2 _ eq_refl)|];
      split; [intros a Ha Hw; apply (Heff2 a Ha Hw); intros Hx; inversion Hx | exact Hgr2] ].
  - intros a Ha. inversion Ha.
  - intros HPRE.
    refine (ALEAF fx lyc Sc W regsT memT mdc bs (sp0 - STK) HPRE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    + lia.
    + rewrite Ha0L. lia.
    + rewrite Ha0L. apply (WL.wcc_leafb_bytes_garr8 W memT f bs HG); lia.
    + exact (WL.wcc_leafb_stk_journal B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k (sp0 - STK)
               (spZ regsT) HJ ltac:(lia) ltac:(lia)).
    + unfold RCc.RP_COUNTER_FRAME. unfold LCK.ESTACK in Hbud. lia.
    + rewrite Ha0L. unfold BKA.off_stk, RCc.RP_COUNTER_FRAME. left. lia.
    + apply WL.wcc_leafb_app_stack; unfold RCc.RP_COUNTER_FRAME; lia.
    + apply WL.wcc_leafb_app_stack; lia.
    + exact (WL.wcc_leafb_asan_cells B HCELLS lyc Sc W memT mdc HAR).
    + unfold BKA.off_stk, RCc.RP_COUNTER_FRAME, BC.GOT_CELL_K. left. lia.
    + unfold BKA.off_stk, RCc.RP_COUNTER_FRAME, BC.CELL_K. left. lia.
    + rewrite Ha0L.
      exact (WL.wcc_leafb_addressable_block B LAWS lyc Sc W memT mdc bA nA (f + 14) 2 HAR Hin
               ltac:(lia) ltac:(lia) ltac:(lia)).
    + apply (WL.wcc_leafb_rng_journal B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k _ _ HJ);
        unfold RCc.RP_COUNTER_FRAME; lia.
    + exact (proj1 (WL.wcc_leafb_rng_cells W)).
    + exact (proj2 (WL.wcc_leafb_rng_cells W)).
    + rewrite Ha0L.
      exact (WL.wcc_leafb_rng_block B LAWS lyc Sc W memT mdc bA nA (f + 14) 2 HAR Hin ltac:(lia) ltac:(lia)).
    + rewrite Ha0L.
      pose proof (WL.wcc_leafb_rng_shadow_block B LAWS lyc Sc W memT mdc bA nA (f + 14) 2 HAR Hin
        ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
      replace (f + 14 + 2 - 1) with (f + 15) in HS by lia.
      exact HS.
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
Hypothesis Hwlo : sp0 - STK <= spZ regs - CCN_STK.
Hypothesis Hwhi : spZ regs <= sp0.
Hypothesis Hn : 0 <= n < 2 ^ 64.
Hypothesis Hlen : Z.of_nat (length bs) = n.
Hypothesis Hblk : 0 < n -> exists bA nA, In (bA, nA) (ablocks B lyc Sc) /\ bA <= f /\ f + n <= bA + nA.
Hypothesis Hgarr : garr8 segs (mrestrict (w_H W) memc) f (map (fun b : byte => bv_unsigned b) bs).
Hypothesis Hnev : st_nev S + k + CCN_EV <= EV_MAX.

Local Abbreviation POST := (wire_ccn_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs).
(* The inner journal: from the entry state, stack window [spZ regs - CCN_STK, spZ regs). *)
Local Abbreviation JI ly1 S1 W1 m1 md1 k1 :=
  (ajournalA CCN_STK (spZ regs) [] lyc Sc W memc mdc [] ly1 S1 W1 m1 md1 k1).
Local Abbreviation GR rg i := (YK11.getr rg (Z_to_bv 5 i)).

Lemma ccw_HARc : AR segs B lyc Sc W memc mdc.
Proof. destruct HJ as (HAR & _). exact HAR. Qed.

Lemma ccw_JI0 : JI lyc Sc W memc mdc 0.
Proof.
  apply (ajournal_sub_init segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k CCN_STK (spZ regs) []
           (spZ regs - sp0) HJ).
  - lia.
  - pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (H16 & _) & _).
    rewrite Zminus_mod, Hal, H16. reflexivity.
  - lia.
  - unfold CCN_STK, CCN_FRAME, ESTACK. lia.
  - lia.
Qed.

Lemma ccw_sp_rng : YM05.alloc_ceiling + 32 + 4096 <= spZ regs /\ spZ regs <= 2 ^ 47.
Proof.
  pose proof ccw_JI0 as J. destruct J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    (_ & _ & Hc & Hlo & Hhi & H47 & _) & _).
  unfold CCN_STK, CCN_FRAME, ESTACK in Hlo. lia.
Qed.

Lemma ccw_win : forall ly1 S1 W1 m1 md1 k1, JI ly1 S1 W1 m1 md1 k1 ->
  forall a, spZ regs - CCN_STK <= a < spZ regs -> apresent (w_H W1) m1 a.
Proof.
  intros ly1 S1 W1 m1 md1 k1 J.
  destruct J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). exact Hpres.
Qed.

Lemma ccw_AR : forall ly1 S1 W1 m1 md1 k1, JI ly1 S1 W1 m1 md1 k1 -> AR segs B ly1 S1 W1 m1 md1.
Proof. intros ly1 S1 W1 m1 md1 k1 J. destruct J as (HAR & _). exact HAR. Qed.

(* f's bytes at a state of the inner journal whose blocks keep the caller's (check_value_cgW.v cv_reply_at). *)
Lemma ccw_bytes_view : forall ly1 S1 W1 m1 md1 k1, JI ly1 S1 W1 m1 md1 k1 -> 0 < n ->
  (forall b nb, In (b, nb) (ablocks B lyc Sc) -> In (b, nb) (ablocks B ly1 S1)) ->
  forall j, (j < length bs)%nat ->
    aview segs (w_H W1) m1 (f + Z.of_nat j) = Some (nth j (map (fun b : byte => bv_unsigned b) bs) 0).
Proof.
  intros ly1 S1 W1 m1 md1 k1 J1 Hn0 Hsub j Hj.
  destruct (Hblk Hn0) as (bA & nA & HbA & HbA1 & HbA2).
  assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia).
  pose proof J1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  replace (f + Z.of_nat j) with (bA + (f + Z.of_nat j - bA)) by lia.
  rewrite (F2 bA nA (f + Z.of_nat j - bA) HbA (Hsub _ _ HbA) ltac:(lia) ltac:(intros (r0 & Hr0 & _); destruct Hr0)).
  replace (bA + (f + Z.of_nat j - bA)) with (f + Z.of_nat j) by lia.
  exact (ccw_garr8_aview (w_H W) memc f _ j Hgarr ltac:(rewrite length_map; lia)).
Qed.

Lemma ccw_garr8_at : forall ly1 S1 W1 m1 md1 k1, JI ly1 S1 W1 m1 md1 k1 -> 0 < n ->
  (forall b nb, In (b, nb) (ablocks B lyc Sc) -> In (b, nb) (ablocks B ly1 S1)) ->
  garr8 segs (mrestrict (w_H W1) m1) f (map (fun b : byte => bv_unsigned b) bs).
Proof.
  intros ly1 S1 W1 m1 md1 k1 J1 Hn0 Hsub. apply ccw_garr8_of_aview. intros j Hj.
  rewrite length_map in Hj.
  split; [exact (ccw_bytes_view _ _ _ _ _ _ J1 Hn0 Hsub j Hj) | apply ccw_nth_rng].
Qed.

(* The byte f + j as a raw read, at such a state. *)
Lemma ccw_byte_at : forall ly1 S1 W1 m1 md1 k1, JI ly1 S1 W1 m1 md1 k1 -> 0 < n ->
  (forall b nb, In (b, nb) (ablocks B lyc Sc) -> In (b, nb) (ablocks B ly1 S1)) ->
  forall j, (j < length bs)%nat ->
    mrd BImg.rsegs m1 (wa (f + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0)).
Proof.
  intros ly1 S1 W1 m1 md1 k1 J1 Hn0 Hsub j Hj.
  rewrite (ccw_mrd_of_aview W1 m1 _ _ (ccw_bytes_view _ _ _ _ _ _ J1 Hn0 Hsub j Hj)).
  rewrite ccw_nth_map. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  apply bv_unsigned_in_range.
Qed.

(* The frame [spZ regs - 32, spZ regs) lies above the leaf's window [spZ regs - 32 - ESTACK, spZ regs - 32). *)
Lemma ccw_frame_kept : forall (W1 W2 : world segs) (m1 m2 : word -> option byte) (cs : list cell),
  rw_cells BImg.rsegs m1 (spZ regs - 32) cs -> Z.of_nat (cells_size cs) = 32 ->
  (forall a, spZ regs - CCN_STK <= a < spZ regs -> apresent (w_H W1) m1 a) ->
  (forall a, spZ regs - CCN_STK <= a < spZ regs -> apresent (w_H W2) m2 a) ->
  (forall a, spZ regs - 32 <= a < spZ regs -> aview segs (w_H W2) m2 a = aview segs (w_H W1) m1 a) ->
  rw_cells BImg.rsegs m2 (spZ regs - 32) cs.
Proof.
  intros W1 W2 m1 m2 cs F Hcs P1 P2 E.
  apply (ccw_rw_cells_ext m1 m2 _ _ F). intros a Ha. rewrite Hcs in Ha.
  unfold wa. apply (ccw_byte_eq (w_H W1) (w_H W2) m1 m2 a); [apply P1 | apply P2 | apply E];
    unfold CCN_STK, CCN_FRAME, ESTACK in *; lia.
Qed.

(* The inner journal after a run that wrote the frame [spZ regs - 32, spZ regs) only (check_value_cgW.v cv_entry). *)
Lemma ccw_JI_frame : forall m1 md',
  munch [(spZ regs - 32, spZ regs)] memc m1 -> wmono BImg.rsegs memc m1 -> same_but_materialized mdc md' ->
  JI lyc Sc W m1 md' 0.
Proof.
  intros m1 md' MU WM SBM.
  pose proof ccw_sp_rng as [Hsp1 Hsp2].
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  pose proof ccw_JI0 as JI0.
  pose proof (ccw_win _ _ _ _ _ _ JI0) as Hpres0.
  apply (ajournal_exec segs B LAWS ccw_segs_low CCN_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W memc mdc 0 m1 md'
           (fun a => spZ regs - 32 <= a < spZ regs) JI0).
  - intros x Hx. unfold mrestrict. rewrite (MU x); [reflexivity|]. cbn [outside]. split; [exact Hx | exact I].
  - intros x Hx. unfold mrestrict in *. revert Hx. destruct (w_H W x) eqn:Ehx; intros Hx; [exact Hx|].
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs - 32)) as [Hl|Hl];
      [rewrite (MU x); [exact Hx | cbn [outside]; split; [lia | exact I]]|].
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [Hh|Hh];
      [|rewrite (MU x); [exact Hx | cbn [outside]; split; [lia | exact I]]].
    assert (Hxr : spZ regs - CCN_STK <= bv_unsigned x < spZ regs) by (unfold CCN_STK, CCN_FRAME, ESTACK; lia).
    destruct (Hpres0 _ Hxr) as [_ (b & Hb)].
    assert (Hw : wview BImg.rsegs m1 x <> None).
    { refine (WM x _). unfold wview. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
    unfold wview in Hw. destruct (m1 x) as [b'|] eqn:Em1; [discriminate|]. exfalso.
    rewrite (LeafCgGlue.find_segment_out BImg.rsegs (bv_unsigned x) 1) in Hw; [exact (Hw eq_refl)|lia|].
    intros sg Hin Hr. pose proof (ccw_segs_low (bv_unsigned x) (ex_intro _ sg (conj Hin Hr))) as Hlow.
    unfold kLowMemEnd in Hlow. lia.
  - intros x Hx.
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs - 32)) as [Hl|Hl];
      [apply (MU x); cbn [outside]; split; [lia | exact I]|].
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [Hh|Hh];
      [|apply (MU x); cbn [outside]; split; [lia | exact I]].
    exfalso.
    assert (Hxr : spZ regs - CCN_STK <= bv_unsigned x < spZ regs) by (unfold CCN_STK, CCN_FRAME, ESTACK; lia).
    pose proof (proj1 (Hpres0 _ Hxr)) as Hhx. rewrite Z_to_bv_bv_unsigned in Hhx. congruence.
  - exact SBM.
  - intros a Ha. cbv beta in Ha. left. unfold CCN_STK, CCN_FRAME, ESTACK. lia.
Qed.

(* The return to the caller: a state of the inner journal at the caller's ra, the caller's blocks and frames, and
   every callee-saved register the caller's, give the post. *)
Lemma ccw_post : forall regs2 m2 md2,
  JI lyc Sc W m2 md2 0 -> aregs_preserved regs regs2 ->
  POST W (mkCfg (@YK11.mkst fx regs2 (YK11.getr regs 1) m2 (YK11.seg_rom segs)) md2).
Proof.
  intros regs2 m2 md2 J2 HP.
  unfold wire_ccn_post.
  exists lyc, Sc, regs2, m2, md2.
  split; [reflexivity|].
  split.
  { pose proof (ajournal_sub segs B LAWS ccw_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
                  CCN_STK (spZ regs) [] [] lyc Sc W m2 md2 0 HJ J2 Hwlo Hwhi
                  ltac:(intros a (r0 & Hr0 & _); destruct Hr0)) as J.
    cbn [app] in J. exact J. }
  split; [exact HP|].
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { apply (acall_kept_of_journal segs B ccw_segs_low CCN_STK (spZ regs) [] [] lyc Sc W memc mdc lyc Sc W m2
             md2 0 (fun _ => False) J2 ccw_HARc).
    - intros a (r0 & Hr0 & _). destruct Hr0.
    - intros b m i Hb _ _. exact Hb.
    - exact sink_closed_nil. }
  exact (mle_start MT Sc MTL).
Qed.

(* ---- n < 18: the frame and the return ---- *)
Lemma ccw_short : n < 18 -> SRr segs W (@cfg_at fx segs CCN_ENTRY regs memc mdc) POST.
Proof.
  intros Hshort.
  pose proof ccw_sp_rng as [Hsp1 Hsp2].
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  pose proof ccw_JI0 as JI0.
  pose proof (ccw_win _ _ _ _ _ _ JI0) as Hpres0.
  assert (U11 : bv_unsigned (GR regs 11) = n).
  { assert (X : bv_unsigned (YK11.getr regs 11) = n) by (rewrite H11; unfold w64; apply ccw_u64; lia). exact X. }
  eapply (@ccw_run fx W regs memc mdc CCN_ENTRY).
  { unfold LCK.ms_of_regs.
    eapply ccn_short_F with (lo := spZ regs - CCN_STK).
    all: try change (bv_unsigned (GR regs 2)) with (spZ regs).
    - apply (ccw_stk_present (w_H W)); [unfold CCN_STK, CCN_FRAME, ESTACK; lia | lia | exact Hpres0].
    - unfold CCN_STK, CCN_FRAME, ESTACK. lia.
    - rewrite U11. lia.
    - apply ccw_rng; [lia | lia |]. intros b Hb. exact (proj1 (Hpres0 b ltac:(unfold CCN_STK, CCN_FRAME, ESTACK; lia))). }
  intros ms' md' (ms0 & (m1 & v0 & -> & MU & WM & FR) & EQV) SBM.
  change (bv_unsigned (GR regs 2)) with (spZ regs) in MU, FR, EQV.
  destruct (ccw_regs_of EQV) as (G1 & G2 & G3 & G4 & G8 & G9 & _ & _ & _ & G18 & G19 & G20 & G21 & G22 & G23 &
    G24 & G25 & G26 & G27).
  assert (Hret : ret_pc (GR regs 1) = GR regs 1).
  { apply LeafCgFacts.ret_ok_stmt_YK0s. exact Hra. }
  rewrite Hret in EQV.
  rewrite (ccw_ms_shape _ _ _ _ EQV).
  apply SRr_ret. apply ccw_post.
  - exact (ccw_JI_frame m1 md' MU WM SBM).
  - intros i Hi. unfold acallee_saved in Hi.
    assert (Hc : i = 2 \/ i = 3 \/ i = 4 \/ i = 8 \/ i = 9 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/
                 i = 23 \/ i = 24 \/ i = 25 \/ i = 26 \/ i = 27) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
    + etransitivity; [exact G2|]. unfold spZ. apply Z_to_bv_bv_unsigned.
    + exact G3.
    + exact G4.
    + exact G8.
    + exact G9.
    + exact G18.
    + exact G19.
    + exact G20.
    + exact G21.
    + exact G22.
    + exact G23.
    + exact G24.
    + exact G25.
    + exact G26.
    + exact G27.
Qed.

(* ---- n >= 18: the frame, the leaf call, the test and the return ---- *)
Lemma ccw_long : 18 <= n -> SRr segs W (@cfg_at fx segs CCN_ENTRY regs memc mdc) POST.
Proof.
  intros Hlong.
  pose proof ccw_sp_rng as [Hsp1 Hsp2].
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  pose proof ccw_JI0 as JI0.
  pose proof (ccw_win _ _ _ _ _ _ JI0) as Hpres0.
  destruct (Hblk ltac:(lia)) as (bA & nA & HbA & HbA1 & HbA2).
  pose proof (al_blocks _ _ LAWS _ _ _ _ _ bA nA ccw_HARc HbA) as (_ & H4096 & Hceil & Happ & _ & _ & Hmr).
  pose proof (req_size_pos nA ltac:(lia)) as [Hq1 Hq2].
  assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia).
  destruct (WL.wcc_leafb_asan_cells B HCELLS lyc Sc W memc mdc ccw_HARc) as (CK & GCK & _).
  assert (U11 : bv_unsigned (GR regs 11) = n).
  { assert (X : bv_unsigned (YK11.getr regs 11) = n) by (rewrite H11; unfold w64; apply ccw_u64; lia). exact X. }
  assert (U10 : bv_unsigned (GR regs 10) = f).
  { assert (X : bv_unsigned (YK11.getr regs 10) = f) by (rewrite H10; unfold w64; apply ccw_u64; lia). exact X. }
  (* the prologue, up to the call *)
  eapply (@ccw_run fx W regs memc mdc CCN_ENTRY).
  { unfold LCK.ms_of_regs.
    eapply ccn_seg1_F with (lo := spZ regs - CCN_STK).
    all: try change (bv_unsigned (GR regs 2)) with (spZ regs).
    - apply (ccw_stk_present (w_H W)); [unfold CCN_STK, CCN_FRAME, ESTACK; lia | lia | exact Hpres0].
    - unfold CCN_STK, CCN_FRAME, ESTACK. lia.
    - exact GCK.
    - exact CK.
    - unfold BC.CELL_K. lia.
    - rewrite U11. lia.
    - apply ccw_rng; [lia | lia |]. intros b Hb. exact (proj1 (Hpres0 b ltac:(unfold CCN_STK, CCN_FRAME, ESTACK; lia))).
    - exact (proj1 (WL.wcc_leafb_rng_cells W)).
    - exact (proj2 (WL.wcc_leafb_rng_cells W)). }
  intros ms' md' (ms0 & (m1 & v0 & -> & MU & WM & FR) & EQV) SBM.
  change (bv_unsigned (GR regs 2)) with (spZ regs) in MU, FR, EQV.
  destruct (ccw_regs_of EQV) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & E11 & _ & E18 & E19 & E20 & E21 & E22 &
    E23 & E24 & E25 & E26 & E27).
  rewrite (ccw_ms_shape _ _ _ _ EQV).
  pose proof (ccw_JI_frame m1 md' MU WM SBM) as HJ1.
  set (regsL := ms_regs ms') in *.
  assert (SPL : spZ regsL = spZ regs + -32).
  { change (spZ regsL) with (bv_unsigned (GR regsL 2)). rewrite E2. apply ccw_u64. lia. }
  (* the call of rp_counter *)
  rewrite ccw_leaf_pc.
  eapply SRr_bind.
  - exact (ccw_leaf_call W regsL m1 CCN_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc md' 0 (-32) f n bA nA bs
             HJ1 SPL eq_refl ltac:(lia) ltac:(unfold CCN_STK, CCN_FRAME, ESTACK, LCK.ESTACK; lia)
             ltac:(pose proof (YK0s.ret_ok_even _ (proj1 (proj2 ccw_ra))) as R; rewrite <- E1 in R; exact R)
             (eq_trans E3 Hgp) (eq_trans E4 Htp) (eq_trans E10 H10)
             HbA HbA1 HbA2 ltac:(lia) Hlen
             (ccw_garr8_at _ _ _ _ _ _ HJ1 ltac:(lia) (fun b nb H => H))).
  - intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hres2 & Heff2 & Hgr2).
    replace (YK11.getr regsL 1) with (Z_to_bv 64 CCN_RET) by (symmetry; exact E1).
    (* the frame, kept by the leaf *)
    assert (FR2 : rw_cells BImg.rsegs mem2 (spZ regs - 32) [C8 v0; C8 (GR regs 9); C8 (GR regs 8); C8 (GR regs 1)]).
    { replace (spZ regs - 32) with (spZ regs + -32) by lia.
      apply (ccw_frame_kept W W m1 mem2 _ ltac:(replace (spZ regs - 32) with (spZ regs + -32) by lia; exact FR)
               eq_refl (ccw_win _ _ _ _ _ _ HJ1) (ccw_win _ _ _ _ _ _ HJ2)).
      intros a Ha. apply Heff2; [lia|]. rewrite SPL. unfold LCK.ESTACK. lia. }
    (* the registers at the return *)
    assert (K8 : GR regs2 8 = Z_to_bv 64 f).
    { etransitivity; [apply (HP2 8); unfold acallee_saved; lia|]. rewrite E8. exact H10. }
    assert (K9 : GR regs2 9 = Z_to_bv 64 BC.ASAN_K).
    { etransitivity; [apply (HP2 9); unfold acallee_saved; lia|]. exact E9. }
    assert (K2 : bv_unsigned (GR regs2 2) = spZ regs - 32).
    { assert (X : GR regs2 2 = GR regsL 2) by (apply (HP2 2); unfold acallee_saved; lia).
      rewrite X. change (bv_unsigned (GR regsL 2)) with (spZ regsL). lia. }
    assert (Ef : bv_unsigned (Z_to_bv 64 f) = f) by (apply ccw_u64; lia).
    remember (nth 14 bs (Z_to_bv 8 0)) as b14 eqn:Eb14.
    remember (nth 15 bs (Z_to_bv 8 0)) as b15 eqn:Eb15.
    assert (Res : PRC.counter_result bs = bv_unsigned b14 + 256 * bv_unsigned b15)
      by (unfold PRC.counter_result, PRC.counter_byte; rewrite Eb14, Eb15; reflexivity).
    assert (HAR2 : AR segs B lyc Sc W mem2 md2) by exact (ccw_AR _ _ _ _ _ _ HJ2).
    assert (F14 : mrd BImg.rsegs mem2 (wa (f + 14)) = Some b14).
    { rewrite Eb14. exact (ccw_byte_at _ _ _ _ _ _ HJ2 ltac:(lia) (fun b nb H => H) 14 ltac:(lia)). }
    assert (F15 : mrd BImg.rsegs mem2 (wa (f + 15)) = Some b15).
    { rewrite Eb15. exact (ccw_byte_at _ _ _ _ _ _ HJ2 ltac:(lia) (fun b nb H => H) 15 ltac:(lia)). }
    (* +0x30 .. the return *)
    eapply (@ccw_run fx W regs2 mem2 md2 CCN_RET).
    { assert (K10 : GR regs2 10 = Z_to_bv 64 (PRC.counter_result bs)) by exact Hres2.
      unfold LCK.ms_of_regs. rewrite K8, K9, K10, Res.
      eapply ccn_seg2_F.
      - rewrite K2. exact FR2.
      - rewrite K2. lia.
      - rewrite Ef. exact (WL.wcc_leafb_addressable_block B LAWS lyc Sc W mem2 md2 bA nA (f + 14) 2 HAR2 HbA
                             ltac:(lia) ltac:(lia) ltac:(lia)).
      - rewrite Ef. exact F14.
      - rewrite Ef. exact F15.
      - rewrite K2. apply ccw_rng; [lia | lia |]. intros b Hb.
        exact (proj1 (ccw_win _ _ _ _ _ _ HJ2 b ltac:(unfold CCN_STK, CCN_FRAME, ESTACK; lia))).
      - rewrite Ef. exact (WL.wcc_leafb_rng_block B LAWS lyc Sc W mem2 md2 bA nA (f + 14) 2 HAR2 HbA
                             ltac:(lia) ltac:(lia)).
      - rewrite Ef.
        pose proof (WL.wcc_leafb_rng_shadow_block B LAWS lyc Sc W mem2 md2 bA nA (f + 14) 2 HAR2 HbA
          ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
        replace (f + 14 + 2 - 1) with (f + 15) in HS by lia.
        exact HS. }
    intros ms3 md3 (ms4 & (a1' & a2' & a3' & ->) & EQV3) SBM3.
    destruct (ccw_regs_of EQV3) as (H1' & H2' & H3' & H4' & H8' & H9' & _ & _ & _ & H18' & H19' & H20' & H21' &
      H22' & H23' & H24' & H25' & H26' & H27').
    assert (Hret : ret_pc (GR regs 1) = GR regs 1).
    { apply LeafCgFacts.ret_ok_stmt_YK0s. exact Hra. }
    rewrite Hret in EQV3.
    rewrite (ccw_ms_shape _ _ _ _ EQV3).
    apply SRr_ret. apply ccw_post.
    + exact (ccw_aj_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 SBM3).
    + intros i Hi.
      assert (HPL : forall r, acallee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> GR regs2 r = GR regs r).
      { intros r Hr H2r H8r H9r. etransitivity; [apply (HP2 r Hr)|].
        unfold acallee_saved in Hr.
        assert (Hc : r = 3 \/ r = 4 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/
                     r = 25 \/ r = 26 \/ r = 27) by lia.
        destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]];
          assumption. }
      unfold acallee_saved in Hi.
      assert (Hc : i = 2 \/ i = 3 \/ i = 4 \/ i = 8 \/ i = 9 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/
                   i = 23 \/ i = 24 \/ i = 25 \/ i = 26 \/ i = 27) by lia.
      destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
      * etransitivity; [exact H2'|]. rewrite K2. replace (spZ regs - 32 + 32) with (spZ regs) by lia.
        unfold spZ. apply Z_to_bv_bv_unsigned.
      * etransitivity; [exact H3'|]. apply HPL; unfold acallee_saved; lia.
      * etransitivity; [exact H4'|]. apply HPL; unfold acallee_saved; lia.
      * exact H8'.
      * exact H9'.
      * etransitivity; [exact H18'|]. apply HPL; unfold acallee_saved; lia.
      * etransitivity; [exact H19'|]. apply HPL; unfold acallee_saved; lia.
      * etransitivity; [exact H20'|]. apply HPL; unfold acallee_saved; lia.
      * etransitivity; [exact H21'|]. apply HPL; unfold acallee_saved; lia.
      * etransitivity; [exact H22'|]. apply HPL; unfold acallee_saved; lia.
      * etransitivity; [exact H23'|]. apply HPL; unfold acallee_saved; lia.
      * etransitivity; [exact H24'|]. apply HPL; unfold acallee_saved; lia.
      * etransitivity; [exact H25'|]. apply HPL; unfold acallee_saved; lia.
      * etransitivity; [exact H26'|]. apply HPL; unfold acallee_saved; lia.
      * etransitivity; [exact H27'|]. apply HPL; unfold acallee_saved; lia.
Qed.

Lemma ccw_entry : SRr segs W (@cfg_at fx segs CCN_ENTRY regs memc mdc) POST.
Proof.
  destruct (Z_lt_le_dec n 18) as [Hs | Hl]; [exact (ccw_short Hs) | exact (ccw_long Hl)].
Qed.

End Entry.

Theorem ccw_walk : wire_check_counter_cg B MT (wire_sigma WS_check_counter).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs f n bs.
  intros HJ Hra Hra4 Hgp Htp H10 H11 Hal Hwlo Hwhi Hn Hlen Hblk Hgarr Hnev.
  eapply ccw_entry; eassumption.
Qed.
End Walk.

(* The frozen statement: every premise of the walk is a premise of wire_check_counter_holds_stmt. *)
Theorem wire_check_counter_cg_holds {fx : YK11.FPState} {rc : YM05.RunCeil} (B : asyms) (MT : ameter_ops) :
  wire_check_counter_holds_stmt B MT.
Proof.
  intros HCELLS LAWS MTL ALEAF.
  apply ccw_walk; assumption.
Qed.
