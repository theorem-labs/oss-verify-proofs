(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: copied from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_leafb.v (origin/ossv/recipes 88154566652a) for reac-repacer/fuzz_uci's image A: module paths and names changed, the cell rows are this unit's AsanCells rows, and the read-only-image helper is dropped. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/reac-repacer/fuzz_uci/lib/A/Prog/UciCcLeafb.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/UciCcLeafb.v, with its module paths and module names changed; 1109 of its 1232 lines of code are new or changed and 398 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac-repacer/fuzz_uci's check_value in image A, proving the frozen statement
   lib/A/Prog/check_value_cg.v uci_check_value_cg_holds_stmt, in the form of proofs/libreac/fuzz_decode/lib/A/Prog/
   crtA_walk.v, crtA_w_head.v, crtA_w_tail.v, crtA_encw.v, crtA_w_mid.v and crtA_close.v (origin/ossv/recipes
   88154566652a): footprint runs carried into SRr, an inner journal over the call's stack window, each call cut by its
   callee contract, and the helpers of those files (crtA_run, crtA_ms_shape, crtA_ms_reg, crtT_regs_of, crtA_trace0,
   crtT_chain_nil, crtA_byte_eq, crtT_rw_cells_ext, crtA_rng_vis, crtT_aj_md, crtT_not_old, crtT_perm_rm,
   crtA_addressable, crtA_rng_hull, crtA_vis_hull) restated at this unit's image. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_value_cgW.v, with its module paths and module names changed; 40 of its 203 lines of code are new or changed and 1069 lines of the source are left out. *)
(* WireChkRun: the run and state helpers of the image-A walks of reac-repacer/fuzz_wire's checks, restated from
   reac-repacer/fuzz_uci's lib/A/Prog/check_value_cgW.v (its image-free helpers cv_segs_low .. cv_stk_present and
   cv_aj_md, renamed with the prefix wcr_, at this unit's segments): a footprint run carried into SRr (wcr_run, through
   lib/A/Prog/LeafCgFacts.v bridge_evtF_stmt_YA0n), the shape and registers of the state it reaches (wcr_ms_shape,
   wcr_regs_of), RNG_W W on visible bytes (wcr_rng, wcr_rng_vis), the view against the raw memory (wcr_aview_vis .. wcr_present_vis,
   wcr_garr8_aview, wcr_garr8_of_aview), present bytes as a stack range (wcr_stk_present), and a journal across a run that writes no memory
   (wcr_aj_md). No lemma here names a function. *)
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
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require LeafCgKit LeafCgFacts LeafCgGlue WirePImg.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.LeafCgKit.
Module AC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.AsanCells.
Module AImg := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Img0.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Lemma wcr_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof. exact WirePImg.wire_segs_low. Qed.

Lemma wcr_u64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz. Qed.

Lemma wcr_byte_eq : forall (H H' : word -> bool) (m m' : word -> option byte) (a : Z),
  apresent H m a -> apresent H' m' a -> aview tfibsegs H' m' a = aview tfibsegs H m a ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros H H' m m' a [Hh [b Hb]] [Hh' [b' Hb']] E.
  unfold aview, YP09.mbyte, mrestrict in E.
  rewrite Hh, Hh' in E. rewrite Hb, Hb' in E. cbn in E.
  injection E as E. rewrite Hb, Hb'. f_equal. apply bv_eq. exact E.
Qed.

Lemma wcr_rw_cells_ext : forall (m m' : word -> option byte) (A : Z) (cs : list cell),
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

Lemma wcr_rng_vis : forall (W : world tfibsegs) a n, 0 <= a -> a + n <= 2 ^ 64 ->
  (forall i, 0 <= i < n -> w_H W (Z_to_bv 64 (a + i)) = false) ->
  ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) a n.
Proof.
  intros W a n H0 H1 Hv. split; [exact H0|]. split; [exact H1|].
  intros b j Hb Hj. unfold LCK.RNG_W, LCK.range_avoids. intros kk Hk. unfold LCK.woff.
  assert (Ub : bv_unsigned (Z_to_bv 64 b) = b) by (apply wcr_u64; lia).
  rewrite Ub. replace (b + Z.of_nat kk) with (a + (b + Z.of_nat kk - a)) by lia. apply Hv. lia.
Qed.

Lemma wcr_fp_avoids : forall (W : world tfibsegs),
  LCK.fp_avoids (@w_H tfibsegs W) (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W).
Proof. intros W a n H. unfold LCK.RNG_W in H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.

Lemma wcr_run {fx : YK11.FPState} : forall (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (pc : Z) (P : machine_state -> Prop) (Q : world tfibsegs -> config -> Prop),
  ExecF.evtF AImg.rsegs (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) P (@LCK.ms_of_regs fx pc regs mem) ->
  (forall ms' md', (exists ms0, P ms0 /\ ms_eqv ms0 ms') -> same_but_materialized md md' ->
     SRr tfibsegs W (mkCfg ms' md') Q) ->
  SRr tfibsegs W (@cfg_at fx tfibsegs pc regs mem md) Q.
Proof.
  intros W regs mem md pc P Q Hrun K. unfold cfg_at.
  pose proof (LeafCgGlue.evtF_eqv AImg.rsegs _ P _ _ Hrun (@LeafCgGlue.ms_of_regs_eqv fx pc regs mem)) as Hrun'.
  apply (LeafCgFacts.bridge_evtF_stmt_YA0n W _ md _ _ Q Hrun' (wcr_fp_avoids W)).
  intros ms' md' (ms1 & HP & HE & _) Hs. apply K; [exists ms1; split; assumption | exact Hs].
Qed.

Lemma wcr_ms_shape {fx : YK11.FPState} : forall (R : bvmap 5 word) (pc : word) (m : word -> option byte)
    (ms' : machine_state),
  ms_eqv (MS R (@fp_regs fx) pc (@fp_csr fx) None m (YK11.seg_rom tfibsegs)) ms' ->
  ms' = @YK11.mkst fx (ms_regs ms') pc m (YK11.seg_rom tfibsegs).
Proof.
  intros R pc m [r f p sv rv fc mm ro] (_ & Hf & Hp & Hs & Hr & Hc & Hm & Hro).
  cbn [MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
  subst. reflexivity.
Qed.

Lemma wcr_ms_reg : forall (R : bvmap 5 word) F pc fc rv m ro (ms' : machine_state) (r : bv 5),
  ms_eqv (MS R F pc fc rv m ro) ms' -> YK11.getr (ms_regs ms') r = YK11.getr R r.
Proof.
  intros R F pc fc rv m ro ms' r (HR & _). cbn [MS ms_regs] in HR. exact (LeafCgGlue.getr_xeqv _ _ HR r).
Qed.

Lemma wcr_regs_of : forall {x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
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
  repeat split; (etransitivity; [apply (wcr_ms_reg _ _ _ _ _ _ _ _ _ H) | reflexivity]).
Qed.

Lemma wcr_rng : forall (W : world tfibsegs) lo len, 0 <= lo -> lo + len <= 2 ^ 64 ->
  (forall b, lo <= b < lo + len -> w_H W (Z_to_bv 64 b) = false) ->
  ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) lo len.
Proof.
  intros W lo len H0 H1 H. split; [exact H0|]. split; [exact H1|].
  intros b j Hb Hbj. unfold LCK.RNG_W, LCK.range_avoids, LCK.woff. intros k Hk.
  rewrite (wcr_u64 b) by lia. apply H. lia.
Qed.

Lemma wcr_aview_vis : forall (W : world tfibsegs) mem a v,
  aview tfibsegs (w_H W) mem a = Some v -> w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W mem a v H. destruct (w_H W (Z_to_bv 64 a)) eqn:E; [|reflexivity]. exfalso.
  pose proof (@w_Hoff tfibsegs W _ E) as F.
  unfold aview, YP09.mbyte, mrestrict in H. rewrite E in H.
  unfold YK11.seg_rom, memory_read in H. cbn [Z.of_N] in H. rewrite F in H. discriminate H.
Qed.

Lemma wcr_aview_mrd : forall (W : world tfibsegs) mem a, w_H W (Z_to_bv 64 a) = false ->
  aview tfibsegs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (mrd AImg.rsegs mem (wa a)).
Proof. intros W mem a H. unfold aview, YP09.mbyte, mrestrict, mrd, wa. rewrite H. reflexivity. Qed.

Lemma wcr_mrd_of_aview : forall (W : world tfibsegs) mem a v,
  aview tfibsegs (w_H W) mem a = Some v -> mrd AImg.rsegs mem (wa a) = Some (Z_to_bv 8 v).
Proof.
  intros W mem a v E. pose proof (wcr_aview_vis W mem a v E) as Hv.
  rewrite (wcr_aview_mrd W mem a Hv) in E.
  destruct (mrd AImg.rsegs mem (wa a)) as [b|]; cbn in E; [|discriminate].
  injection E as E. subst v. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
  apply bv_unsigned_in_range.
Qed.

Lemma wcr_present_vis : forall (W : world tfibsegs) m a, apresent (w_H W) m a -> aview tfibsegs (w_H W) m a <> None.
Proof.
  intros W m a (Hh & b & Hb). rewrite (wcr_aview_mrd W m a Hh). unfold mrd, wa. rewrite Hb. discriminate.
Qed.

Lemma wcr_le_byte1 : forall v, 0 <= v < 256 -> Z.shiftr (v mod 2 ^ (8 * Z.of_nat 1)) (8 * Z.of_nat 0) mod 256 = v.
Proof.
  intros v Hv. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite Z.mod_small by lia. apply Z.mod_small. lia.
Qed.

Lemma wcr_garr8_aview : forall (H : word -> bool) mem a (l : list Z) (j : nat),
  garr8 tfibsegs (mrestrict H mem) a l -> (j < length l)%nat ->
  aview tfibsegs H mem (a + Z.of_nat j) = Some (nth j l 0).
Proof.
  intros H mem a l j G Hj. destruct (G j Hj) as [V R]. specialize (V 0%nat ltac:(lia)).
  rewrite Nat2Z.inj_0, Z.add_0_r in V.
  unfold aview. rewrite V. cbn [option_map]. f_equal.
  unfold YO0f.le_byte, YG0f.le_byte. rewrite Z_to_bv_unsigned, (wcr_le_byte1 _ R).
  apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

Lemma wcr_garr8_of_aview : forall (H : word -> bool) mem a (l : list Z),
  (forall j, (j < length l)%nat -> aview tfibsegs H mem (a + Z.of_nat j) = Some (nth j l 0) /\ 0 <= nth j l 0 < 256) ->
  garr8 tfibsegs (mrestrict H mem) a l.
Proof.
  intros H mem a l HA j Hj. destruct (HA j Hj) as [E R]. split; [|exact R].
  intros k Hk. assert (Ek : k = 0%nat) by lia. subst k. rewrite Nat2Z.inj_0, Z.add_0_r.
  unfold aview in E.
  destruct (YP09.mbyte tfibsegs (mrestrict H mem) (a + Z.of_nat j)) as [b|] eqn:Eb; cbn in E; [|discriminate].
  injection E as E. f_equal. apply bv_eq. unfold YO0f.le_byte, YG0f.le_byte.
  rewrite Z_to_bv_unsigned, (wcr_le_byte1 _ R), <- E.
  symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma wcr_stk_present : forall (H : word -> bool) m lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> apresent H m a) -> stk AImg.rsegs m lo hi.
Proof.
  intros H m lo hi H0 H1 Hp. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (Hp a Ha) as [_ [b Hb]]. unfold wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold mrd. rewrite Hb. reflexivity.
Qed.

Section Aj.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation sink := AE2k.tfib_sink_head.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Local Abbreviation ajournalA := (@ajournal rc sink segs B).

(* A run that writes no memory: the journal follows its same_but_materialized. *)
Lemma wcr_aj_md : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k mdc',
  ajournalA STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k -> same_but_materialized mdc mdc' ->
  ajournalA STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc' k.
Proof.
  intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k mdc' HJ Hs.
  eapply (ajournal_exec segs B LAWS wcr_segs_low STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc mdc'
            (fun _ => False) HJ).
  - intros x _. reflexivity.
  - apply YK1b.mem_grows_refl.
  - intros x _. reflexivity.
  - exact Hs.
  - intros a Ha. destruct Ha.
Qed.
(* The two journal fields a walk reads at a cut point (fuzz_uci's check_value_cgW.v cv_AR, cv_win). *)
Lemma wcr_AR_of : forall STK sp0 FP ly S W mem md own ly1 S1 W1 m1 md1 k1,
  ajournalA STK sp0 FP ly S W mem md own ly1 S1 W1 m1 md1 k1 -> AR segs B ly1 S1 W1 m1 md1.
Proof. intros STK sp0 FP ly S W mem md own ly1 S1 W1 m1 md1 k1 J. destruct J as (HAR & _). exact HAR. Qed.

Lemma wcr_win_of : forall STK sp0 FP ly S W mem md own ly1 S1 W1 m1 md1 k1,
  ajournalA STK sp0 FP ly S W mem md own ly1 S1 W1 m1 md1 k1 ->
  forall a, sp0 - STK <= a < sp0 -> apresent (w_H W1) m1 a.
Proof.
  intros STK sp0 FP ly S W mem md own ly1 S1 W1 m1 md1 k1 J.
  destruct J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). exact Hpres.
Qed.
End Aj.
