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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/A/Prog/check_width_cgW.v, with its module paths and module names changed; 430 of its 565 lines of code are new or changed and 586 lines of the source are left out. *)
(* The caller-journal walk of reac-repacer/fuzz_wire's check_downstream in image B, proving the frozen statement lib/B/Prog/check_downstream_cg.v wire_check_downstream_holds_stmt, in the walk style of reac-repacer/fuzz_uci's lib/B/Prog/check_value_cgW.v (recipes commit 0295462466b2; its helpers copied under the prefix cdw_), the leaf call cut by the leaf contract of rp_ds_accept (lib/B/Prog/rp_ds_accept_cg.v) through the kit's lib/B/Prog/WireCcLeafb.v wcc_leafb_journal, in the form of libreac/fuzz_decode's released lib/B/Prog/LLVMFuzzerTestOneInput_leafb.v dec_leafb_counter (recipes commit 48907dc7e8ca), and the frame's want closed on each path as the released lib/Prog/check_downstream.v closes it. *)
(* check_downstream_cgW: wire_check_downstream_cg (wire_sigma WS_check_downstream) at image B (fuzz_wire.asan-ubsan,
   check_downstream at 0x7ffe8) from the premises of the frozen statement. The body runs as three footprint runs
   (lib/B/Prog/WireCdsBSegs.v) carried into SRr by lib/B/Prog/LeafCgFacts.v bridge_evtF_stmt_YA0n, an inner journal
   over the call's stack window, and the one call, of the leaf rp_ds_accept.
   The walk:
     1. an INNER journal at the entry state (YCbq.v ajournal_sub_init): stack window [spZ regs - CDS_STK, spZ regs),
        no footprint, no frame of its own;
     2. cds_frame_F, the frame [spZ regs - 16, spZ regs) written (ra, s0); the inner journal follows the write
        (YCbq.v ajournal_exec);
     3. cds_pick_F from +0xc to the call of rp_ds_accept, on both of its sides (n < 18 reads no byte; n >= 18 reads
        f[12], f[13], f[16], f[17] and their shadow bytes from the caller's block): s0 := ds_accept_result n bs of the
        released lib/Prog/rp_ds_accept_c.v, a0 = f, a1 = n, ra = +0x110;
     4. the leaf call (cdw_leaf_call: the leaf's premises, all under 18 <= n, from the inner journal, f's bytes and
        shadow from the caller's block; the leaf's post back into the inner journal; a0 := ds_accept_result n bs);
     5. cds_tail_F from +0x110 to `ret`: `bne a0, s0` not taken (both are ds_accept_result n bs), the frame read
        back (the leaf kept it);
     6. the post: the outer journal by YCbq.v ajournal_sub, acall_kept by YCbq.v acall_kept_of_journal, no event and
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
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import WirePSyms WirePAddr WireCg check_downstream_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import WireCdsBSegs.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require LeafCgKit LeafCgFacts LeafCgGlue WirePImg WireCcLeafb AsanKA.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require rp_ds_accept_cg rp_ds_accept_F_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_ds_accept_c.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.LeafCgKit.
Module BC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.AsanCells.
Module BImg := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Img0.
Module BKA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.AsanKA.
Module WL := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.WireCcLeafb.
Module LDA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_ds_accept_cg.
Module DAF := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_ds_accept_F_c.
Module PDA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_ds_accept_c.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ======================================================================== *)
(* Image-free helpers (check_value_cgW.v cv_*, copied)                        *)
(* ======================================================================== *)

Lemma cdw_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof. exact WirePImg.wire_segs_low. Qed.

Lemma cdw_u64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz. Qed.

Lemma cdw_byte_eq : forall (H H' : word -> bool) (m m' : word -> option byte) (a : Z),
  apresent H m a -> apresent H' m' a -> aview tfibsegs H' m' a = aview tfibsegs H m a ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros H H' m m' a [Hh [b Hb]] [Hh' [b' Hb']] E.
  unfold aview, YP09.mbyte, mrestrict in E.
  rewrite Hh, Hh' in E. rewrite Hb, Hb' in E. cbn in E.
  injection E as E. rewrite Hb, Hb'. f_equal. apply bv_eq. exact E.
Qed.

Lemma cdw_rw_cells_ext : forall (m m' : word -> option byte) (A : Z) (cs : list cell),
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

Lemma cdw_fp_avoids : forall (W : world tfibsegs),
  LCK.fp_avoids (@w_H tfibsegs W) (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W).
Proof. intros W a n H. unfold LCK.RNG_W in H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.

(* A footprint run from cgif's configuration at pc, carried into SRr (check_value_cgW.v cv_run). *)
Lemma cdw_run {fx : YK11.FPState} : forall (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (pc : Z) (P : machine_state -> Prop) (Q : world tfibsegs -> config -> Prop),
  ExecF.evtF BImg.rsegs (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) P (@LCK.ms_of_regs fx pc regs mem) ->
  (forall ms' md', (exists ms0, P ms0 /\ ms_eqv ms0 ms') -> same_but_materialized md md' ->
     SRr tfibsegs W (mkCfg ms' md') Q) ->
  SRr tfibsegs W (@cfg_at fx tfibsegs pc regs mem md) Q.
Proof.
  intros W regs mem md pc P Q Hrun K. unfold cfg_at.
  pose proof (LeafCgGlue.evtF_eqv BImg.rsegs _ P _ _ Hrun (@LeafCgGlue.ms_of_regs_eqv fx pc regs mem)) as Hrun'.
  apply (LeafCgFacts.bridge_evtF_stmt_YA0n W _ md _ _ Q Hrun' (cdw_fp_avoids W)).
  intros ms' md' (ms1 & HP & HE & _) Hs. apply K; [exists ms1; split; assumption | exact Hs].
Qed.

Lemma cdw_ms_shape {fx : YK11.FPState} : forall (R : bvmap 5 word) (pc : word) (m : word -> option byte)
    (ms' : machine_state),
  ms_eqv (MS R (@fp_regs fx) pc (@fp_csr fx) None m (YK11.seg_rom tfibsegs)) ms' ->
  ms' = @YK11.mkst fx (ms_regs ms') pc m (YK11.seg_rom tfibsegs).
Proof.
  intros R pc m [r f p sv rv fc mm ro] (_ & Hf & Hp & Hs & Hr & Hc & Hm & Hro).
  cbn [MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
  subst. reflexivity.
Qed.

Lemma cdw_ms_reg : forall (R : bvmap 5 word) F pc fc rv m ro (ms' : machine_state) (r : bv 5),
  ms_eqv (MS R F pc fc rv m ro) ms' -> YK11.getr (ms_regs ms') r = YK11.getr R r.
Proof.
  intros R F pc fc rv m ro ms' r (HR & _). cbn [MS ms_regs] in HR. exact (LeafCgGlue.getr_xeqv _ _ HR r).
Qed.

Lemma cdw_regs_of : forall {x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
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
  repeat split; (etransitivity; [apply (cdw_ms_reg _ _ _ _ _ _ _ _ _ H) | reflexivity]).
Qed.

Lemma cdw_rng : forall (W : world tfibsegs) lo len, 0 <= lo -> lo + len <= 2 ^ 64 ->
  (forall b, lo <= b < lo + len -> w_H W (Z_to_bv 64 b) = false) ->
  ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) lo len.
Proof.
  intros W lo len H0 H1 H. split; [exact H0|]. split; [exact H1|].
  intros b j Hb Hbj. unfold LCK.RNG_W, LCK.range_avoids, LCK.woff. intros k Hk.
  rewrite (cdw_u64 b) by lia. apply H. lia.
Qed.

Lemma cdw_le_byte1 : forall v, 0 <= v < 256 -> Z.shiftr (v mod 2 ^ (8 * Z.of_nat 1)) (8 * Z.of_nat 0) mod 256 = v.
Proof.
  intros v Hv. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite Z.mod_small by lia. apply Z.mod_small. lia.
Qed.

Lemma cdw_garr8_aview : forall (H : word -> bool) mem a (l : list Z) (j : nat),
  garr8 tfibsegs (mrestrict H mem) a l -> (j < length l)%nat ->
  aview tfibsegs H mem (a + Z.of_nat j) = Some (nth j l 0).
Proof.
  intros H mem a l j G Hj. destruct (G j Hj) as [V R]. specialize (V 0%nat ltac:(lia)).
  rewrite Nat2Z.inj_0, Z.add_0_r in V.
  unfold aview. rewrite V. cbn [option_map]. f_equal.
  unfold YO0f.le_byte, YG0f.le_byte. rewrite Z_to_bv_unsigned, (cdw_le_byte1 _ R).
  apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

Lemma cdw_garr8_of_aview : forall (H : word -> bool) mem a (l : list Z),
  (forall j, (j < length l)%nat -> aview tfibsegs H mem (a + Z.of_nat j) = Some (nth j l 0) /\ 0 <= nth j l 0 < 256) ->
  garr8 tfibsegs (mrestrict H mem) a l.
Proof.
  intros H mem a l HA j Hj. destruct (HA j Hj) as [E R]. split; [|exact R].
  intros k Hk. assert (Ek : k = 0%nat) by lia. subst k. rewrite Nat2Z.inj_0, Z.add_0_r.
  unfold aview in E.
  destruct (YP09.mbyte tfibsegs (mrestrict H mem) (a + Z.of_nat j)) as [b|] eqn:Eb; cbn in E; [|discriminate].
  injection E as E. f_equal. apply bv_eq. unfold YO0f.le_byte, YG0f.le_byte.
  rewrite Z_to_bv_unsigned, (cdw_le_byte1 _ R), <- E.
  symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* The bytes as numbers, and as the C model reads them. *)
Lemma cdw_nth_map : forall (bs : list byte) j,
  nth j (map (fun b : byte => bv_unsigned b) bs) 0 = bv_unsigned (nth j bs (Z_to_bv 8 0)).
Proof.
  induction bs as [|b bs IH]; intros j; destruct j as [|j]; cbn [nth map]; try reflexivity. apply IH.
Qed.

Lemma cdw_nth_rng : forall (bs : list byte) j, 0 <= nth j (map (fun b : byte => bv_unsigned b) bs) 0 < 256.
Proof.
  intros bs j. rewrite cdw_nth_map. pose proof (bv_unsigned_in_range 8 (nth j bs (Z_to_bv 8 0))) as R.
  unfold bv_modulus in R. cbn in R. lia.
Qed.

Lemma cdw_stk_present : forall (H : word -> bool) m lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> apresent H m a) -> stk BImg.rsegs m lo hi.
Proof.
  intros H m lo hi H0 H1 Hp. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (Hp a Ha) as [_ [b Hb]]. unfold wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold mrd. rewrite Hb. reflexivity.
Qed.

(* The return address of the call of rp_ds_accept: its value, parity and size. *)
Lemma cdw_ra : bv_unsigned (Z_to_bv 64 CDS_RET) = CDS_RET /\
  bv_unsigned (Z_to_bv 64 CDS_RET) mod 2 = 0 /\ 4096 <= bv_unsigned (Z_to_bv 64 CDS_RET).
Proof. split; [|split]; vm_compute; first [reflexivity | discriminate]. Qed.

Lemma cdw_leaf_pc : CDS_LEAF = DAF.RP_DS_ACCEPT.
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
Hypothesis ALEAF : forall fx' : YK11.FPState, @wire_leaf_at rc B (@LDA.wire_rp_ds_accept_cg) fx'.
Local Abbreviation ajournalA := (@ajournal rc sink segs B).

(* A run that writes no memory: the journal follows its same_but_materialized (check_value_cgW.v cv_aj_md). *)
Lemma cdw_aj_md : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k mdc',
  ajournalA STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k -> same_but_materialized mdc mdc' ->
  ajournalA STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc' k.
Proof.
  intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k mdc' HJ Hs.
  eapply (ajournal_exec segs B LAWS cdw_segs_low STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc mdc'
            (fun _ => False) HJ).
  - intros x _. reflexivity.
  - apply YK1b.mem_grows_refl.
  - intros x _. reflexivity.
  - exact Hs.
  - intros a Ha. destruct Ha.
Qed.

(* The leaf call (LLVMFuzzerTestOneInput_leafb.v dec_leafb_counter): rp_ds_accept at f, n writes nothing but its own
   frame and returns ds_accept_result n bs. Every premise of its contract about f's bytes stands under 18 <= n (the
   contract's own guard), so the call needs f's block only when n >= 18: a heap block's f is nonzero, and the leaf's
   frame lies on the real stack, above the block and above the whole cell region [GOT_CELL_K, MIDEND + 8). *)
Lemma cdw_leaf_call :
  forall (W : world segs) (regsT : bvmap 5 word) memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k
         (o f n : Z) (bs : list byte),
  ajournalA STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> LCK.ESTACK - o <= STK ->
  YK0s.ret_ok (YK11.getr regsT 1) -> YK11.getr regsT 3 = w64 (as_gp B) -> YK11.getr regsT 4 = w64 (as_tp B) ->
  YK11.getr regsT 10 = w64 f -> YK11.getr regsT 11 = w64 n -> 0 <= n <= CDS_N_MAX -> Z.of_nat (length bs) = n ->
  (18 <= n -> exists bA nA, In (bA, nA) (ablocks B lyc Sc) /\ bA <= f /\ f + n <= bA + nA) ->
  (18 <= n -> garr8 segs (mrestrict (w_H W) memT) f (map (fun b : byte => bv_unsigned b) bs)) ->
  SRr segs W (mkCfg (YK11.mkst regsT (Z_to_bv 64 DAF.RP_DS_ACCEPT) memT (YK11.seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (YK11.mkst regs2 (YK11.getr regsT 1) mem2 (YK11.seg_rom segs)) md2 /\
       ajournalA STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       aregs_preserved regsT regs2 /\
       YK11.getr regs2 10 = w64 (PDA.ds_accept_result n bs) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - LCK.ESTACK <= a < spZ regsT) ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
  intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o f n bs
    HJ Hsp Hal Hneg Hbud Hra Hgp Htp H10 H11 Hn Hbs Hblk HG.
  pose proof (proj1 HJ) as HAR.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil0 & Hslo & Hshi & H47 & _).
  pose proof Hbud as Hbud4. unfold LCK.ESTACK in Hbud4.
  pose proof (@YM05.alloc_ceiling_val rc) as HCEIL.
  unfold CDS_N_MAX in Hn.
  assert (Ha1L : bv_unsigned (YK11.getr regsT (Z_to_bv 5 11)) = n).
  { assert (Hx : bv_unsigned (YK11.getr regsT 11) = n)
      by (rewrite H11; unfold w64; apply cdw_u64; lia).
    exact Hx. }
  assert (HspL : bv_unsigned (YK11.getr regsT (Z_to_bv 5 2)) = sp0 + o) by exact Hsp.
  (* f's block, its bounds, and f as a0, when n >= 18 *)
  assert (HBLK : 18 <= n -> exists bA nA,
            In (bA, nA) (ablocks B lyc Sc) /\ bA <= f /\ f + n <= bA + req_size nA /\
            4096 <= bA /\ bA + req_size nA <= YM05.alloc_ceiling /\
            bv_unsigned (YK11.getr regsT (Z_to_bv 5 10)) = f).
  { intros H18. destruct (Hblk H18) as (bA & nA & Hin & Hf1 & Hf2).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ bA nA HAR Hin) as (_ & H4096 & Hceil & Happ & _ & _ & Hmr).
    pose proof (req_size_pos nA ltac:(lia)) as [Hq1 Hq2].
    assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia).
    exists bA, nA. split; [exact Hin|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    assert (Hx : bv_unsigned (YK11.getr regsT 10) = f) by (rewrite H10; unfold w64; apply cdw_u64; lia).
    exact Hx. }
  eapply SRr_mono;
    [ eapply (WL.wcc_leafb_journal B LAWS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o
                DAF.RP_DS_ACCEPT (Some (PDA.ds_accept_result n bs)) [] (fun _ => True)
                HJ Hsp Hal Hneg Hbud Hra Hgp Htp)
    | cbv beta; intros W2 c2 _ (-> & regs2 & mem2 & md2 & Hc2 & HJ2 & Hp2 & Hres2 & Heff2 & Hgr2 & _);
      split; [reflexivity|]; exists regs2, mem2, md2;
      split; [exact Hc2|]; split; [exact HJ2|]; split; [exact Hp2|];
      split; [exact (Hres2 _ eq_refl)|];
      split; [intros a Ha Hw; apply (Heff2 a Ha Hw); intros Hx; inversion Hx | exact Hgr2] ].
  - intros a Ha. inversion Ha.
  - intros HPRE. rewrite <- Ha1L.
    refine (ALEAF fx lyc Sc W regsT memT mdc bs (sp0 - STK) HPRE _ _ _ _ _).
    + exact (WL.wcc_leafb_stk_journal B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k (sp0 - STK)
               (spZ regsT) HJ ltac:(lia) ltac:(lia)).
    + unfold DAF.RP_DS_ACCEPT_FRAME. lia.
    + intros H18. rewrite Ha1L in H18.
      destruct (HBLK H18) as (bA & nA & Hin & Hf1 & Hf2 & H4096 & Hceil & Ha0L).
      rewrite Ha0L.
      split; [lia|].
      split; [lia|].
      split; [apply (WL.wcc_leafb_bytes_garr8 W memT f bs (HG H18)); lia|].
      split; [unfold BKA.off_stk, DAF.RP_DS_ACCEPT_FRAME; left; lia|].
      split; [apply WL.wcc_leafb_app_stack; unfold DAF.RP_DS_ACCEPT_FRAME; lia|].
      split; [apply WL.wcc_leafb_app_stack; lia|].
      split; [exact (WL.wcc_leafb_asan_cells B HCELLS lyc Sc W memT mdc HAR)|].
      split; [unfold BKA.off_stk, DAF.RP_DS_ACCEPT_FRAME, BC.GOT_CELL_K, BC.MIDEND; left; lia|].
      exact (WL.wcc_leafb_addressable_block B LAWS lyc Sc W memT mdc bA nA (f + 12) 6 HAR Hin
               ltac:(lia) ltac:(lia) ltac:(lia)).
    + apply (WL.wcc_leafb_rng_journal B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k _ _ HJ);
        unfold DAF.RP_DS_ACCEPT_FRAME; lia.
    + intros H18. rewrite Ha1L in H18.
      destruct (HBLK H18) as (bA & nA & Hin & Hf1 & Hf2 & H4096 & Hceil & Ha0L).
      rewrite Ha0L.
      split; [exact (proj1 (WL.wcc_leafb_rng_cells W))|].
      split; [exact (proj2 (WL.wcc_leafb_rng_cells W))|].
      split; [exact (WL.wcc_leafb_rng_block B LAWS lyc Sc W memT mdc bA nA (f + 12) 6 HAR Hin
                       ltac:(lia) ltac:(lia))|].
      exact (WL.wcc_leafb_rng_shadow_block B LAWS lyc Sc W memT mdc bA nA (f + 12) 6 HAR Hin
               ltac:(lia) ltac:(lia) ltac:(lia)).
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
Hypothesis Hwlo : sp0 - STK <= spZ regs - CDS_STK.
Hypothesis Hwhi : spZ regs <= sp0.
Hypothesis Hn : 0 <= n <= CDS_N_MAX.
Hypothesis Hlen : Z.of_nat (length bs) = n.
Hypothesis Hblk : 0 < n -> exists bA nA, In (bA, nA) (ablocks B lyc Sc) /\ bA <= f /\ f + n <= bA + nA.
Hypothesis Hgarr : garr8 segs (mrestrict (w_H W) memc) f (map (fun b : byte => bv_unsigned b) bs).
Hypothesis Hnev : st_nev S + k + CDS_EV <= EV_MAX.

Local Abbreviation POST := (wire_cds_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs).
(* The inner journal: from the entry state, stack window [spZ regs - CDS_STK, spZ regs). *)
Local Abbreviation JI ly1 S1 W1 m1 md1 k1 :=
  (ajournalA CDS_STK (spZ regs) [] lyc Sc W memc mdc [] ly1 S1 W1 m1 md1 k1).
Local Abbreviation GR rg i := (YK11.getr rg (Z_to_bv 5 i)).

Lemma cdw_HARc : AR segs B lyc Sc W memc mdc.
Proof. destruct HJ as (HAR & _). exact HAR. Qed.

Lemma cdw_JI0 : JI lyc Sc W memc mdc 0.
Proof.
  apply (ajournal_sub_init segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k CDS_STK (spZ regs) []
           (spZ regs - sp0) HJ).
  - lia.
  - pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (H16 & _) & _).
    rewrite Zminus_mod, Hal, H16. reflexivity.
  - lia.
  - unfold CDS_STK, CDS_FRAME, ESTACK. lia.
  - lia.
Qed.

Lemma cdw_sp_rng : YM05.alloc_ceiling + 16 + 4096 <= spZ regs /\ spZ regs <= 2 ^ 47.
Proof.
  pose proof cdw_JI0 as J. destruct J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    (_ & _ & Hc & Hlo & Hhi & H47 & _) & _).
  unfold CDS_STK, CDS_FRAME, ESTACK in Hlo. lia.
Qed.

Lemma cdw_win : forall ly1 S1 W1 m1 md1 k1, JI ly1 S1 W1 m1 md1 k1 ->
  forall a, spZ regs - CDS_STK <= a < spZ regs -> apresent (w_H W1) m1 a.
Proof.
  intros ly1 S1 W1 m1 md1 k1 J.
  destruct J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). exact Hpres.
Qed.

Lemma cdw_AR : forall ly1 S1 W1 m1 md1 k1, JI ly1 S1 W1 m1 md1 k1 -> AR segs B ly1 S1 W1 m1 md1.
Proof. intros ly1 S1 W1 m1 md1 k1 J. destruct J as (HAR & _). exact HAR. Qed.

(* f's bytes at a state of the inner journal whose blocks keep the caller's (check_value_cgW.v cv_reply_at). *)
Lemma cdw_bytes_view : forall ly1 S1 W1 m1 md1 k1, JI ly1 S1 W1 m1 md1 k1 -> 0 < n ->
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
  exact (cdw_garr8_aview (w_H W) memc f _ j Hgarr ltac:(rewrite length_map; lia)).
Qed.

Lemma cdw_garr8_at : forall ly1 S1 W1 m1 md1 k1, JI ly1 S1 W1 m1 md1 k1 -> 0 < n ->
  (forall b nb, In (b, nb) (ablocks B lyc Sc) -> In (b, nb) (ablocks B ly1 S1)) ->
  garr8 segs (mrestrict (w_H W1) m1) f (map (fun b : byte => bv_unsigned b) bs).
Proof.
  intros ly1 S1 W1 m1 md1 k1 J1 Hn0 Hsub. apply cdw_garr8_of_aview. intros j Hj.
  rewrite length_map in Hj.
  split; [exact (cdw_bytes_view _ _ _ _ _ _ J1 Hn0 Hsub j Hj) | apply cdw_nth_rng].
Qed.

(* The frame [spZ regs - 16, spZ regs) lies above the leaf's window [spZ regs - 16 - ESTACK, spZ regs - 16). *)
Lemma cdw_frame_kept : forall (W1 W2 : world segs) (m1 m2 : word -> option byte) (cs : list cell),
  rw_cells BImg.rsegs m1 (spZ regs - 16) cs -> Z.of_nat (cells_size cs) = 16 ->
  (forall a, spZ regs - CDS_STK <= a < spZ regs -> apresent (w_H W1) m1 a) ->
  (forall a, spZ regs - CDS_STK <= a < spZ regs -> apresent (w_H W2) m2 a) ->
  (forall a, spZ regs - 16 <= a < spZ regs -> aview segs (w_H W2) m2 a = aview segs (w_H W1) m1 a) ->
  rw_cells BImg.rsegs m2 (spZ regs - 16) cs.
Proof.
  intros W1 W2 m1 m2 cs F Hcs P1 P2 E.
  apply (cdw_rw_cells_ext m1 m2 _ _ F). intros a Ha. rewrite Hcs in Ha.
  unfold wa. apply (cdw_byte_eq (w_H W1) (w_H W2) m1 m2 a); [apply P1 | apply P2 | apply E];
    unfold CDS_STK, CDS_FRAME, ESTACK in *; lia.
Qed.

(* The inner journal after a run that wrote the frame [spZ regs - 16, spZ regs) only (check_value_cgW.v cv_entry). *)
Lemma cdw_JI_frame : forall m1 md',
  munch [(spZ regs - 16, spZ regs)] memc m1 -> wmono BImg.rsegs memc m1 -> same_but_materialized mdc md' ->
  JI lyc Sc W m1 md' 0.
Proof.
  intros m1 md' MU WM SBM.
  pose proof cdw_sp_rng as [Hsp1 Hsp2].
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  pose proof cdw_JI0 as JI0.
  pose proof (cdw_win _ _ _ _ _ _ JI0) as Hpres0.
  apply (ajournal_exec segs B LAWS cdw_segs_low CDS_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W memc mdc 0 m1 md'
           (fun a => spZ regs - 16 <= a < spZ regs) JI0).
  - intros x Hx. unfold mrestrict. rewrite (MU x); [reflexivity|]. cbn [outside]. split; [exact Hx | exact I].
  - intros x Hx. unfold mrestrict in *. revert Hx. destruct (w_H W x) eqn:Ehx; intros Hx; [exact Hx|].
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs - 16)) as [Hl|Hl];
      [rewrite (MU x); [exact Hx | cbn [outside]; split; [lia | exact I]]|].
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [Hh|Hh];
      [|rewrite (MU x); [exact Hx | cbn [outside]; split; [lia | exact I]]].
    assert (Hxr : spZ regs - CDS_STK <= bv_unsigned x < spZ regs) by (unfold CDS_STK, CDS_FRAME, ESTACK; lia).
    destruct (Hpres0 _ Hxr) as [_ (b & Hb)].
    assert (Hw : wview BImg.rsegs m1 x <> None).
    { refine (WM x _). unfold wview. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
    unfold wview in Hw. destruct (m1 x) as [b'|] eqn:Em1; [discriminate|]. exfalso.
    rewrite (LeafCgGlue.find_segment_out BImg.rsegs (bv_unsigned x) 1) in Hw; [exact (Hw eq_refl)|lia|].
    intros sg Hin Hr. pose proof (cdw_segs_low (bv_unsigned x) (ex_intro _ sg (conj Hin Hr))) as Hlow.
    unfold kLowMemEnd in Hlow. lia.
  - intros x Hx.
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs - 16)) as [Hl|Hl];
      [apply (MU x); cbn [outside]; split; [lia | exact I]|].
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [Hh|Hh];
      [|apply (MU x); cbn [outside]; split; [lia | exact I]].
    exfalso.
    assert (Hxr : spZ regs - CDS_STK <= bv_unsigned x < spZ regs) by (unfold CDS_STK, CDS_FRAME, ESTACK; lia).
    pose proof (proj1 (Hpres0 _ Hxr)) as Hhx. rewrite Z_to_bv_bv_unsigned in Hhx. congruence.
  - exact SBM.
  - intros a Ha. cbv beta in Ha. left. unfold CDS_STK, CDS_FRAME, ESTACK. lia.
Qed.

(* The return to the caller: a state of the inner journal at the caller's ra, the caller's blocks and frames, and
   every callee-saved register the caller's, give the post. *)
Lemma cdw_post : forall regs2 m2 md2,
  JI lyc Sc W m2 md2 0 -> aregs_preserved regs regs2 ->
  POST W (mkCfg (@YK11.mkst fx regs2 (YK11.getr regs 1) m2 (YK11.seg_rom segs)) md2).
Proof.
  intros regs2 m2 md2 J2 HP.
  unfold wire_cds_post.
  exists lyc, Sc, regs2, m2, md2.
  split; [reflexivity|].
  split.
  { pose proof (ajournal_sub segs B LAWS cdw_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
                  CDS_STK (spZ regs) [] [] lyc Sc W m2 md2 0 HJ J2 Hwlo Hwhi
                  ltac:(intros a (r0 & Hr0 & _); destruct Hr0)) as J.
    cbn [app] in J. exact J. }
  split; [exact HP|].
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { apply (acall_kept_of_journal segs B cdw_segs_low CDS_STK (spZ regs) [] [] lyc Sc W memc mdc lyc Sc W m2
             md2 0 (fun _ => False) J2 cdw_HARc).
    - intros a (r0 & Hr0 & _). destruct Hr0.
    - intros b m i Hb _ _. exact Hb.
    - exact sink_closed_nil. }
  exact (mle_start MT Sc MTL).
Qed.

(* ---- the frame, the want, the leaf call, the test and the return ---- *)
Lemma cdw_entry : SRr segs W (@cfg_at fx segs CDS_ENTRY regs memc mdc) POST.
Proof.
  pose proof cdw_sp_rng as [Hsp1 Hsp2].
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  pose proof cdw_JI0 as JI0.
  pose proof (cdw_win _ _ _ _ _ _ JI0) as Hpres0.
  pose proof Hn as Hn'. unfold CDS_N_MAX in Hn'.
  assert (U11 : bv_unsigned (GR regs 11) = n).
  { assert (X : bv_unsigned (YK11.getr regs 11) = n) by (rewrite H11; unfold w64; apply cdw_u64; lia). exact X. }
  (* the frame: entry .. +0xc *)
  eapply (@cdw_run fx W regs memc mdc CDS_ENTRY).
  { unfold LCK.ms_of_regs.
    eapply cds_frame_F with (lo := spZ regs - CDS_STK).
    all: try change (bv_unsigned (GR regs 2)) with (spZ regs).
    - apply (cdw_stk_present (w_H W)); [unfold CDS_STK, CDS_FRAME, ESTACK; lia | lia | exact Hpres0].
    - unfold CDS_STK, CDS_FRAME, ESTACK. lia.
    - apply cdw_rng; [lia | lia |]. intros b Hb.
      exact (proj1 (Hpres0 b ltac:(unfold CDS_STK, CDS_FRAME, ESTACK; lia))). }
  intros ms' md' (ms0 & (m1 & -> & MU & WM & FR) & EQV) SBM.
  change (bv_unsigned (GR regs 2)) with (spZ regs) in MU, FR, EQV.
  destruct (cdw_regs_of EQV) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & E11 & _ & E18 & E19 & E20 & E21 & E22 &
    E23 & E24 & E25 & E26 & E27).
  rewrite (cdw_ms_shape _ _ _ _ EQV).
  pose proof (cdw_JI_frame m1 md' MU WM SBM) as HJ1.
  pose proof (cdw_AR _ _ _ _ _ _ HJ1) as HAR1.
  set (regsP := ms_regs ms') in *.
  assert (P11 : bv_unsigned (GR regsP 11) = n) by (rewrite E11; exact U11).
  (* the want: +0xc .. the call of rp_ds_accept *)
  eapply (@cdw_run fx W regsP m1 md' CDS_PICK).
  { unfold LCK.ms_of_regs.
    eapply cds_pick_F with (bs := bs).
    - intros H18. rewrite P11 in H18.
      destruct (Hblk ltac:(lia)) as (bA & nA & HbA & HbA1 & HbA2).
      pose proof (al_blocks _ _ LAWS _ _ _ _ _ bA nA cdw_HARc HbA) as (_ & H4096 & Hceil & Happ & _ & _ & Hmr).
      pose proof (req_size_pos nA ltac:(lia)) as [Hq1 Hq2].
      assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia).
      assert (P10 : bv_unsigned (GR regsP 10) = f).
      { rewrite E10.
        assert (X : bv_unsigned (YK11.getr regs 10) = f) by (rewrite H10; unfold w64; apply cdw_u64; lia).
        exact X. }
      rewrite P10.
      destruct (WL.wcc_leafb_asan_cells B HCELLS lyc Sc W m1 md' HAR1) as (CK & GCK & _).
      split; [lia|].
      split; [apply (WL.wcc_leafb_bytes_garr8 W m1 f bs
                       (cdw_garr8_at _ _ _ _ _ _ HJ1 ltac:(lia) (fun b nb H => H))); lia|].
      split; [exact GCK|]. split; [exact CK|].
      exact (WL.wcc_leafb_addressable_block B LAWS lyc Sc W m1 md' bA nA (f + 12) 6 HAR1 HbA
               ltac:(lia) ltac:(lia) ltac:(lia)).
    - intros H18. rewrite P11 in H18.
      destruct (Hblk ltac:(lia)) as (bA & nA & HbA & HbA1 & HbA2).
      pose proof (al_blocks _ _ LAWS _ _ _ _ _ bA nA cdw_HARc HbA) as (_ & H4096 & Hceil & Happ & _ & _ & Hmr).
      pose proof (req_size_pos nA ltac:(lia)) as [Hq1 Hq2].
      assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia).
      assert (P10 : bv_unsigned (GR regsP 10) = f).
      { rewrite E10.
        assert (X : bv_unsigned (YK11.getr regs 10) = f) by (rewrite H10; unfold w64; apply cdw_u64; lia).
        exact X. }
      rewrite P10.
      split; [exact (proj1 (WL.wcc_leafb_rng_cells W))|].
      split; [exact (proj2 (WL.wcc_leafb_rng_cells W))|].
      split; [exact (WL.wcc_leafb_rng_block B LAWS lyc Sc W m1 md' bA nA (f + 12) 6 HAR1 HbA
                       ltac:(lia) ltac:(lia))|].
      exact (WL.wcc_leafb_rng_shadow_block B LAWS lyc Sc W m1 md' bA nA (f + 12) 6 HAR1 HbA
               ltac:(lia) ltac:(lia) ltac:(lia)). }
  intros ms2 md2 (ms3 & (a2' & a3' & a4' & a5' & ->) & EQV2) SBM2.
  destruct (cdw_regs_of EQV2) as (L1 & L2 & L3 & L4 & L8 & L9 & L10 & L11 & _ & L18 & L19 & L20 & L21 & L22 &
    L23 & L24 & L25 & L26 & L27).
  rewrite (cdw_ms_shape _ _ _ _ EQV2).
  set (regsL := ms_regs ms2) in *.
  pose proof (cdw_aj_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1 SBM2) as HJ1b.
  assert (SPL : spZ regsL = spZ regs + -16).
  { change (spZ regsL) with (bv_unsigned (GR regsL 2)). rewrite L2, E2. apply cdw_u64. lia. }
  (* the call of rp_ds_accept *)
  rewrite cdw_leaf_pc.
  eapply SRr_bind.
  - exact (cdw_leaf_call W regsL m1 CDS_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc md2 0 (-16) f n bs
             HJ1b SPL eq_refl ltac:(lia) ltac:(unfold CDS_STK, CDS_FRAME, ESTACK, LCK.ESTACK; lia)
             ltac:(pose proof (YK0s.ret_ok_even _ (proj1 (proj2 cdw_ra))) as R; rewrite <- L1 in R; exact R)
             (eq_trans L3 (eq_trans E3 Hgp)) (eq_trans L4 (eq_trans E4 Htp))
             (eq_trans L10 (eq_trans E10 H10)) (eq_trans L11 (eq_trans E11 H11)) Hn Hlen
             (fun H18 => Hblk ltac:(lia))
             (fun H18 => cdw_garr8_at _ _ _ _ _ _ HJ1b ltac:(lia) (fun b nb H => H))).
  - intros W2 c2 _ (-> & regs2 & mem2 & md3 & -> & HJ2 & HP2 & Hres2 & Heff2 & Hgr2).
    replace (YK11.getr regsL 1) with (Z_to_bv 64 CDS_RET) by (symmetry; exact L1).
    (* the frame, kept by the leaf *)
    assert (FR2 : rw_cells BImg.rsegs mem2 (spZ regs - 16) [C8 (GR regs 8); C8 (GR regs 1)]).
    { apply (cdw_frame_kept W W m1 mem2 _ FR eq_refl (cdw_win _ _ _ _ _ _ HJ1b) (cdw_win _ _ _ _ _ _ HJ2)).
      intros a Ha. apply Heff2; [lia|]. rewrite SPL. unfold LCK.ESTACK. lia. }
    (* the registers at the return: a0 (the leaf's result) and s0 (the want, kept by the leaf) agree *)
    assert (K10 : GR regs2 10 = Z_to_bv 64 (PDA.ds_accept_result n bs)) by exact Hres2.
    assert (K8 : GR regs2 8 = Z_to_bv 64 (PDA.ds_accept_result n bs)).
    { etransitivity; [apply (HP2 8); unfold acallee_saved; lia|]. rewrite L8, P11. reflexivity. }
    assert (K2 : bv_unsigned (GR regs2 2) = spZ regs - 16).
    { assert (X : GR regs2 2 = GR regsL 2) by (apply (HP2 2); unfold acallee_saved; lia).
      rewrite X. change (bv_unsigned (GR regsL 2)) with (spZ regsL). lia. }
    (* +0x110 .. the return *)
    eapply (@cdw_run fx W regs2 mem2 md3 CDS_RET).
    { unfold LCK.ms_of_regs. rewrite K8, K10.
      eapply cds_tail_F.
      - rewrite K2. exact FR2.
      - rewrite K2. lia.
      - rewrite K2. apply cdw_rng; [lia | lia |]. intros b Hb.
        exact (proj1 (cdw_win _ _ _ _ _ _ HJ2 b ltac:(unfold CDS_STK, CDS_FRAME, ESTACK; lia))). }
    intros ms4 md4 (ms5 & -> & EQV4) SBM4.
    destruct (cdw_regs_of EQV4) as (H1' & H2' & H3' & H4' & H8' & H9' & _ & _ & _ & H18' & H19' & H20' & H21' &
      H22' & H23' & H24' & H25' & H26' & H27').
    assert (Hret : ret_pc (GR regs 1) = GR regs 1).
    { apply LeafCgFacts.ret_ok_stmt_YK0s. exact Hra. }
    rewrite Hret in EQV4.
    rewrite (cdw_ms_shape _ _ _ _ EQV4).
    apply SRr_ret. apply cdw_post.
    + exact (cdw_aj_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 SBM4).
    + intros i Hi.
      assert (HPL : forall r, acallee_saved r -> r <> 2 -> r <> 8 -> GR regs2 r = GR regs r).
      { intros r Hr H2r H8r. etransitivity; [apply (HP2 r Hr)|].
        unfold acallee_saved in Hr.
        assert (Hc : r = 3 \/ r = 4 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
                     r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]];
          (etransitivity; [eassumption | eassumption]). }
      unfold acallee_saved in Hi.
      assert (Hc : i = 2 \/ i = 3 \/ i = 4 \/ i = 8 \/ i = 9 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/
                   i = 23 \/ i = 24 \/ i = 25 \/ i = 26 \/ i = 27) by lia.
      destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
      * etransitivity; [exact H2'|]. rewrite K2. replace (spZ regs - 16 + 16) with (spZ regs) by lia.
        unfold spZ. apply Z_to_bv_bv_unsigned.
      * etransitivity; [exact H3'|]. apply HPL; unfold acallee_saved; lia.
      * etransitivity; [exact H4'|]. apply HPL; unfold acallee_saved; lia.
      * exact H8'.
      * etransitivity; [exact H9'|]. apply HPL; unfold acallee_saved; lia.
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

End Entry.

Theorem cdw_walk : wire_check_downstream_cg B MT (wire_sigma WS_check_downstream).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs f n bs.
  intros HJ Hra Hra4 Hgp Htp H10 H11 Hal Hwlo Hwhi Hn Hlen Hblk Hgarr Hnev.
  eapply cdw_entry; eassumption.
Qed.
End Walk.

(* The frozen statement: every premise of the walk is a premise of wire_check_downstream_holds_stmt. *)
Theorem wire_check_downstream_cg_holds {fx : YK11.FPState} {rc : YM05.RunCeil} (B : asyms) (MT : ameter_ops) :
  wire_check_downstream_holds_stmt B MT.
Proof.
  intros HCELLS LAWS MTL ALEAF.
  apply cdw_walk; assumption.
Qed.
