(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module paths and module names changed; 1161 of its 1364 lines of code are new or changed and 321 lines of the source are left out. *)
(* check_meter_cgW: wire_check_meter_cg (wire_sigma WS_check_meter) at image B (fuzz_wire.asan-ubsan, check_meter at
   0x8016c) from the callee contracts the statement names, proving the frozen statement lib/B/Prog/check_meter_cg.v
   wire_check_meter_holds_stmt. No released ASan walk of this function exists, so the walk is written new: in the walk
   style of reac-repacer/fuzz_uci's lib/B/Prog/check_value_cgW.v (recipes commit 0295462466b2; footprint runs carried
   into SRr, an inner journal over the call's stack window, each call cut by its callee contract), with the fake frame
   of reac-repacer/fuzz_uci's lib/B/Prog/check_clamp_cgW.v (the class-0 stack malloc composed into the journal, as
   that unit's lib/B/Prog/UciCcKit.v ucc_stack_malloc_at, and the frame given back through the statement's
   astack_free_law, as UciCcKit.v ucc_flag_store_pi does after its run) and the leaf call of the kit's
   lib/B/Prog/WireCcLeafb.v.

   The walk (offsets from the entry; lib/B/Prog/WireCmIface.v names the cut points and states each footprint run,
   proved in lib/B/Prog/WireCmSeg1.v, WireCmSeg2.v, WireCmPre.v, WireCmCmp.v and WireCmRel.v, which refute the
   shadow-check report paths and the UBSan wrap traps from the addressable and block premises; the Section Walk
   below takes the six piece statements as hypotheses and wire_check_meter_holds at the end supplies the proofs):
     1. an INNER journal at the entry state (YCbq.v ajournal_sub_init): stack window [spZ regs - CM_STK, spZ regs);
     2. cm_seg1_stmt: the 128-byte frame, the realign, the two runtime cells; the journal follows the frame write;
     3. the class-0 stack malloc (cm_stack_malloc_at): the fake frame F joins the journal's own frames;
     4. cm_seg2a_stmt: F's header, F's shadow bytes, the slot 24(s1); the journal follows;
     5. cm_pre_stmt then cm_seg2c_stmt: the inlined test (s9 = meter_eo, s10 = the want bit), ctr := 0xa5c3 and its
        shadow byte; the journal follows;
     6. rp_meter_counter(f, n, &ctr) through the statement's wire_leaf_wr_at premise (WireCcLeafb.v
        wcc_leafb_journal): a0 = the want bit, ctr = the counter when it counts;
     7. cm_cmp_stmt then cm_rel_stmt: the checks (no abort is reached), F's shadow bytes and header released, the flag
        byte cleared, the reloads and `ret`;
     8. the journal after the release (cm_release: astack_free_law, then YCbq.v ajournal_after_write with no frame of
        its own), the outer journal by YCbq.v ajournal_sub, acall_kept by YCbq.v acall_kept_of_journal. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n YA0o YK1b.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YI00.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG0p.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YCbq YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI16 YI5b YI5c YP09 YO0f.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Frame Cells Step Regs6ss.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require ExecF StepF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require YE2k Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import WirePSyms WirePAddr WireCg check_meter_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import WireCmIface.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require LeafCgKit LeafCgFacts LeafCgGlue WirePImg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require WireCcLeafb rp_meter_counter_cg AsanKA.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require WireCmSeg1 WireCmSeg2 WireCmPre WireCmCmp
  WireCmRel.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.LeafCgKit.
Module BC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.AsanCells.
Module BImg := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Img0.
Module LMC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_meter_counter_cg.
Module WCL := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.WireCcLeafb.
Module AKA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.AsanKA.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ======================================================================== *)
(* Image-free helpers (check_value_cgW.v cv_* at this unit's names)          *)
(* ======================================================================== *)

Lemma cm_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof. exact WirePImg.wire_segs_low. Qed.

Lemma cm_u64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz. Qed.

Lemma cm_fp_avoids : forall (W : world tfibsegs),
  LCK.fp_avoids (@w_H tfibsegs W) (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W).
Proof. intros W a n H. unfold LCK.RNG_W in H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.

(* A footprint run from cgif's configuration at pc, carried into SRr (check_value_cgW.v cv_run), keeping the run's
   raw memory growth (LeafCgGlue.v evtF_eqv). *)
Lemma cm_run {fx : YK11.FPState} : forall (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (pc : Z) (P : machine_state -> Prop) (Q : world tfibsegs -> config -> Prop),
  ExecF.evtF BImg.rsegs (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) P (@LCK.ms_of_regs fx pc regs mem) ->
  (forall ms' md', (exists ms0, P ms0 /\ ms_eqv ms0 ms' /\ mem_grows mem (ms_mem ms0)) ->
     same_but_materialized md md' -> SRr tfibsegs W (mkCfg ms' md') Q) ->
  SRr tfibsegs W (@cfg_at fx tfibsegs pc regs mem md) Q.
Proof.
  intros W regs mem md pc P Q Hrun K. unfold cfg_at.
  pose proof (LeafCgGlue.evtF_eqv BImg.rsegs _ P _ _ Hrun (@LeafCgGlue.ms_of_regs_eqv fx pc regs mem)) as Hrun'.
  apply (LeafCgFacts.bridge_evtF_stmt_YA0n W _ md _ _ Q Hrun' (cm_fp_avoids W)).
  intros ms' md' (ms1 & HP & HE & HG) Hs. apply K; [exists ms1; split; [exact HP | split; [exact HE | exact HG]] | exact Hs].
Qed.

(* A state register-equivalent to an MS form with the cgif float state is that cgif state (cv_ms_shape). *)
Lemma cm_ms_shape {fx : YK11.FPState} : forall (R : bvmap 5 word) (pc : word) (m : word -> option byte)
    (ms' : machine_state),
  ms_eqv (MS R (@fp_regs fx) pc (@fp_csr fx) None m (YK11.seg_rom tfibsegs)) ms' ->
  ms' = @YK11.mkst fx (ms_regs ms') pc m (YK11.seg_rom tfibsegs).
Proof.
  intros R pc m [r f p sv rv fc mm ro] (_ & Hf & Hp & Hs & Hr & Hc & Hm & Hro).
  cbn [MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
  subst. reflexivity.
Qed.

Lemma cm_ms_reg : forall (R : bvmap 5 word) F pc fc rv m ro (ms' : machine_state) (r : bv 5),
  ms_eqv (MS R F pc fc rv m ro) ms' -> YK11.getr (ms_regs ms') r = YK11.getr R r.
Proof.
  intros R F pc fc rv m ro ms' r (HR & _). cbn [MS ms_regs] in HR. exact (LeafCgGlue.getr_xeqv _ _ HR r).
Qed.

(* The registers of a state register-equivalent to an `mkR` state (cv_regs_of), all thirty-one. *)
Lemma cm_regs_of : forall {x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
    x25 x26 x27 x28 x29 x30 x31 : word} {F : bvmap 5 word} {pc : word} {fc : bv 32} {rv : option word}
    {m ro : word -> option byte} {ms' : machine_state},
  ms_eqv (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                  x25 x26 x27 x28 x29 x30 x31) F pc fc rv m ro) ms' ->
  YK11.getr (ms_regs ms') (Z_to_bv 5 1) = x1 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 2) = x2 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 3) = x3 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 4) = x4 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 5) = x5 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 6) = x6 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 7) = x7 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 8) = x8 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 9) = x9 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 10) = x10 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 11) = x11 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 12) = x12 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 13) = x13 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 14) = x14 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 15) = x15 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 16) = x16 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 17) = x17 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 18) = x18 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 19) = x19 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 20) = x20 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 21) = x21 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 22) = x22 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 23) = x23 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 24) = x24 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 25) = x25 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 26) = x26 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 27) = x27 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 28) = x28 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 29) = x29 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 30) = x30 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 31) = x31.
Proof.
  intros until ms'. intros H.
  repeat split; (etransitivity; [apply (cm_ms_reg _ _ _ _ _ _ _ _ _ H) | reflexivity]).
Qed.

(* RNG_W W holds on a range of bytes the world does not hide (cv_rng). *)
Lemma cm_rng : forall (W : world tfibsegs) lo len, 0 <= lo -> lo + len <= 2 ^ 64 ->
  (forall b, lo <= b < lo + len -> w_H W (Z_to_bv 64 b) = false) ->
  ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) lo len.
Proof.
  intros W lo len H0 H1 H. split; [exact H0|]. split; [exact H1|].
  intros b j Hb Hbj. unfold LCK.RNG_W, LCK.range_avoids, LCK.woff. intros k Hk.
  rewrite (cm_u64 b) by lia. apply H. lia.
Qed.

Lemma cm_rng_present : forall (W : world tfibsegs) mem lo len, 0 <= lo -> lo + len <= 2 ^ 64 ->
  (forall b, lo <= b < lo + len -> apresent (w_H W) mem b) ->
  ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) lo len.
Proof. intros W mem lo len H0 H1 HP. apply cm_rng; [exact H0 | exact H1 |]. intros b Hb. exact (proj1 (HP b Hb)). Qed.

(* ---- aview at this image (cv_aview_vis, cv_aview_mrd, cv_mrd_of_aview) ---- *)

Lemma cm_aview_vis : forall (W : world tfibsegs) mem a v,
  aview tfibsegs (w_H W) mem a = Some v -> w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W mem a v H. destruct (w_H W (Z_to_bv 64 a)) eqn:E; [|reflexivity]. exfalso.
  pose proof (@w_Hoff tfibsegs W _ E) as F.
  unfold aview, YP09.mbyte, mrestrict in H. rewrite E in H.
  unfold YK11.seg_rom, memory_read in H. cbn [Z.of_N] in H. rewrite F in H. discriminate H.
Qed.

Lemma cm_aview_mrd : forall (W : world tfibsegs) mem a, w_H W (Z_to_bv 64 a) = false ->
  aview tfibsegs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (mrd BImg.rsegs mem (wa a)).
Proof. intros W mem a H. unfold aview, YP09.mbyte, mrestrict, mrd, wa. rewrite H. reflexivity. Qed.

Lemma cm_mrd_of_aview : forall (W : world tfibsegs) mem a v,
  aview tfibsegs (w_H W) mem a = Some v -> mrd BImg.rsegs mem (wa a) = Some (Z_to_bv 8 v).
Proof.
  intros W mem a v E. pose proof (cm_aview_vis W mem a v E) as Hv.
  rewrite (cm_aview_mrd W mem a Hv) in E.
  destruct (mrd BImg.rsegs mem (wa a)) as [b|]; cbn in E; [|discriminate].
  injection E as E. subst v. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
  apply bv_unsigned_in_range.
Qed.

(* A raw byte fact moves to another memory whose view agrees on that (visible) byte. *)
Lemma cm_mrd_kept : forall (W : world tfibsegs) m m' a,
  w_H W (Z_to_bv 64 a) = false ->
  aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a ->
  mrd BImg.rsegs m' (wa a) = mrd BImg.rsegs m (wa a).
Proof.
  intros W m m' a Hv E. rewrite !(cm_aview_mrd W _ a Hv) in E.
  destruct (mrd BImg.rsegs m' (wa a)) as [b'|], (mrd BImg.rsegs m (wa a)) as [b|]; cbn in E; try discriminate;
    [|reflexivity]. injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma cm_bytes_kept : forall (W : world tfibsegs) m m' a bs,
  bytes_at BImg.rsegs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> w_H W (Z_to_bv 64 (a + i)) = false /\
     aview tfibsegs (w_H W) m' (a + i) = aview tfibsegs (w_H W) m (a + i)) ->
  bytes_at BImg.rsegs m' a bs.
Proof.
  intros W m m' a bs (H0 & H1 & H) HK. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HK (Z.of_nat i) ltac:(lia)) as (Hv & E).
  rewrite (cm_mrd_kept W m m' _ Hv E). exact (H i Hi).
Qed.

(* ---- garr8 against aview (cv_garr8_aview, cv_garr8_of_aview) ---- *)

Lemma cm_le_byte1 : forall v, 0 <= v < 256 -> Z.shiftr (v mod 2 ^ (8 * Z.of_nat 1)) (8 * Z.of_nat 0) mod 256 = v.
Proof.
  intros v Hv. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite Z.mod_small by lia. apply Z.mod_small. lia.
Qed.

Lemma cm_garr8_aview : forall (H : word -> bool) mem a (l : list Z) (j : nat),
  garr8 tfibsegs (mrestrict H mem) a l -> (j < length l)%nat ->
  aview tfibsegs H mem (a + Z.of_nat j) = Some (nth j l 0).
Proof.
  intros H mem a l j G Hj. destruct (G j Hj) as [V R]. specialize (V 0%nat ltac:(lia)).
  rewrite Nat2Z.inj_0, Z.add_0_r in V.
  unfold aview. rewrite V. cbn [option_map]. f_equal.
  unfold YO0f.le_byte, YG0f.le_byte. rewrite Z_to_bv_unsigned, (cm_le_byte1 _ R).
  apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

Lemma cm_garr8_of_aview : forall (H : word -> bool) mem a (l : list Z),
  (forall j, (j < length l)%nat -> aview tfibsegs H mem (a + Z.of_nat j) = Some (nth j l 0) /\ 0 <= nth j l 0 < 256) ->
  garr8 tfibsegs (mrestrict H mem) a l.
Proof.
  intros H mem a l HA j Hj. destruct (HA j Hj) as [E R]. split; [|exact R].
  intros k Hk. assert (Ek : k = 0%nat) by lia. subst k. rewrite Nat2Z.inj_0, Z.add_0_r.
  unfold aview in E.
  destruct (YP09.mbyte tfibsegs (mrestrict H mem) (a + Z.of_nat j)) as [b|] eqn:Eb; cbn in E; [|discriminate].
  injection E as E. f_equal. apply bv_eq. unfold YO0f.le_byte, YG0f.le_byte.
  rewrite Z_to_bv_unsigned, (cm_le_byte1 _ R), <- E.
  symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* Present bytes form a stack range (cv_stk_present), and a cell of junk can be carved from them. *)
Lemma cm_stk_present : forall (H : word -> bool) m lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> apresent H m a) -> stk BImg.rsegs m lo hi.
Proof.
  intros H m lo hi H0 H1 Hp. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (Hp a Ha) as [_ [b Hb]]. unfold wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold mrd. rewrite Hb. reflexivity.
Qed.

Lemma cm_rw_carve : forall (H : word -> bool) m lo (n : nat), 0 <= lo -> lo + Z.of_nat n <= 2 ^ 64 ->
  (forall a, lo <= a < lo + Z.of_nat n -> apresent H m a) ->
  exists junk, rw_cells BImg.rsegs m lo [CB n junk].
Proof.
  intros H m lo n H0 H1 Hp.
  pose proof (cm_stk_present H m lo (lo + Z.of_nat n) H0 H1 Hp) as ST.
  destruct (stk_carve BImg.rsegs m lo (lo + Z.of_nat n) n ST ltac:(lia)) as [_ (junk & FR)].
  replace (lo + Z.of_nat n - Z.of_nat n) with lo in FR by lia. exists junk. exact FR.
Qed.

Lemma cm_shadow_addr_eq : forall a, BC.shadow_addr a = YG0f.shadow_addr a.
Proof. intros a. unfold BC.shadow_addr, YG0f.shadow_addr, BC.ASAN_K, SHADOW_OFF. lia. Qed.

(* `outside` of a list of ranges is decidable. *)
Lemma cm_outside_dec : forall (Wl : list (Z * Z)) x, outside Wl x \/ ~ outside Wl x.
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

(* ======================================================================== *)
(* The class-0 stack malloc in the caller's journal (fuzz_uci UciCcKit.v ucc_sm_path, ucc_sm_effect_journal,     *)
(* ucc_stack_malloc_at, recipes commit 0295462466b2), at this unit's segments and core                          *)
(* ======================================================================== *)

Lemma cm_sm_path : forall cid s pos s',
  apath (stack_malloc cid s) [] (PFake cid pos, s') ->
  frames s' = (cid, pos) :: frames s /\
  st_chunks s' = st_chunks s /\ st_secs s' = st_secs s /\ st_nev s' = st_nev s /\
  st_qthread s' = st_qthread s /\ st_qglobal s' = st_qglobal s /\
  (exists f, s' = set_fs f s).
Proof.
  intros cid s pos s' H.
  unfold stack_malloc, bind, get, put, ret in H. cbn [ibind] in H.
  destruct (fs_probe (Z.to_nat (fs_frames cid)) (fs_live (st_fs s)) cid (znth 0 cid (fs_hint (st_fs s))))
    as [[pos0 h0]|] eqn:E; cbn [ibind apath] in H.
  - inversion H. subst.
    repeat split; try reflexivity.
    exists (mkFS (zupd cid h0 (fs_hint (st_fs s))) ((cid, pos) :: fs_live (st_fs s))). reflexivity.
  - inversion H.
Qed.

Lemma cm_sf_frames : forall cid pos s rest,
  frames s = (cid, pos) :: rest -> frames (stack_free_state cid pos s) = rest.
Proof.
  intros cid pos s rest Hf.
  assert (E : frames (stack_free_state cid pos s) = del_pos (frames s) cid pos) by reflexivity.
  rewrite E, Hf. cbn [del_pos]. rewrite !Z.eqb_refl. reflexivity.
Qed.

Section sm. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation SK := YE2k.tfib_sink_head.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Local Notation ajournal := (@ajournal rc SK segs B).

Lemma cm_sm_effect_journal : forall stk lyc Sc W regs memc mdc ly2 S2 W2 mem2 md2 nf k1,
  AR segs B ly2 S2 W2 mem2 md2 -> layout_le (length (st_secs Sc)) lyc ly2 -> wle W W2 -> same_io mdc md2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ aowned B lyc Sc a -> ~ aowned B ly2 S2 a -> ~ (spZ regs - stk <= a < spZ regs) ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
  (forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W2) mem2 a) ->
  AR segs B lyc Sc W memc mdc ->
  astk_ok stk lyc (spZ regs) ->
  frames S2 = nf ++ frames Sc -> st_nev S2 <= st_nev Sc + k1 -> 0 <= k1 ->
  (length (st_secs Sc) <= length (st_secs S2))%nat ->
  (forall p n, In (p, n) (ablocks B lyc Sc) -> In (p, n) (ablocks B ly2 S2)) ->
  qtight S2 ->
  ajournal stk (spZ regs) [] lyc Sc W memc mdc nf ly2 S2 W2 mem2 md2 k1.
Proof.
intros stk lyc Sc W regs memc mdc ly2 S2 W2 mem2 md2 nf k1
HAR2 Hly2 Hwle2 Hio2 Hfr Hpres2 HAR Hstk Hfrs Hnev Hk1 Hsecs Hkeep HQT2.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
assert (KEEP : forall a, ~ aowned B lyc Sc a -> ~ aowned B ly2 S2 a ->
~ (spZ regs - stk <= a < spZ regs) -> 0 <= a < 2 ^ 64 ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
{ intros a H1 H2 H3 H6. exact (Hfr a H6 H1 H2 H3). }
assert (BLK : forall b m a, In (b, m) (ablocks B lyc Sc) \/ In (b, m) (ablocks B ly2 S2) -> b <= a < b + req_size m ->
app_addr a).
{ intros b m a [Hb|Hb] Hr.
- destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & _ & Hc & [Hh Hh2] & _). zlia.
- destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 b m HAR2 Hb) as (_ & _ & Hc & [Hh Hh2] & _). zlia. }
split; [exact HAR2|]. split; [exact Hly2|]. split; [exact Hsecs|]. split; [exact Hwle2|].
split; [apply aos_step_of_same_io, Hio2|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk1|].
split.
{ intros a Ha Hs. apply KEEP.
- intros Ho. pose proof (al_owned_low _ _ LAWS _ _ _ _ _ a HAR Ho). zlia.
- intros Ho. pose proof (al_owned_low _ _ LAWS _ _ _ _ _ a HAR2 Ho). zlia.
- exact Hs.
- zlia. }
split.
{ intros p n i H1 H2 Hi Hnf. apply KEEP.
- exact (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS lyc Sc W memc mdc p n HAR H1))))) (p + i) ltac:(zlia))).
- exact (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 p n HAR2 H2))))) (p + i) ltac:(zlia))).
- pose proof (BLK p n (p + i) (or_introl H1) ltac:(zlia)). zlia.
- pose proof (BLK p n (p + i) (or_introl H1) ltac:(zlia)). pose proof asan_consts. zlia. }
split.
{ intros a Hi Hns He _. pose proof (cm_segs_low a Hi). apply KEEP.
- intros Ho. exact (Hns (proj1 (al_owned_image _ _ LAWS _ _ _ _ _ a HAR Hi) Ho)).
- intros Ho. exact (Hns (proj1 (al_owned_image _ _ LAWS _ _ _ _ _ a HAR2 Hi) Ho)).
- zlia.
- zlia. }
split.
{ intros cid pos a Hin Hr Hnf.
assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc cid pos HAR Hin) as (_ & [Hh1 Hh2] & Hb & Hsh).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 cid pos HAR2 Hin2) as (_ & _ & Hb2 & Hsh2). rewrite Efa in Hb2, Hsh2.
destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf0 & Hfc & Hfh).
pose proof (fs_frame_bytes_nonneg cid) as Hnn.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)) as Hsb1.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)) as Hse.
unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
apply KEEP.
- destruct Hr as [Hr|Hr]; [exact (proj2 (Hb a Hr))|].
specialize (Hsh (a - shadow_addr (frame_addr lyc cid pos)) ltac:(zlia)).
replace (shadow_addr (frame_addr lyc cid pos) + (a - shadow_addr (frame_addr lyc cid pos))) with a in Hsh by zlia. exact (proj2 Hsh).
- destruct Hr as [Hr|Hr]; [exact (proj2 (Hb2 a Hr))|].
specialize (Hsh2 (a - shadow_addr (frame_addr lyc cid pos)) ltac:(zlia)).
replace (shadow_addr (frame_addr lyc cid pos) + (a - shadow_addr (frame_addr lyc cid pos))) with a in Hsh2 by zlia. exact (proj2 Hsh2).
- destruct Hr as [Hr|Hr]; zlia.
- destruct Hr as [Hr|Hr].
  + clear -Hr Hf0 Hfc C1. lia.
  + destruct Hsb2 as [_ Hsb2b]. destruct Hsb1 as [Hsb1a _].
    assert (Hlt : shadow_addr (frame_addr lyc cid pos + fs_frame_bytes cid) < kHighMemBeg) by (apply Hsb2b; rewrite C4; lia).
    rewrite C3 in Hlt. unfold SHADOW_OFF in Hsb1a. clear -Hr Hse Hlt Hsb1a C5. lia. }
split; [intros p n i H1 H2 Hi; exfalso; exact (H2 (Hkeep p n H1))|].
split; [exact Hpres2|]. split; [exact Hstk|]. split; [|exact HQT2].
{ intros a HXa He.
pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
pose proof (AR_extra_law_ok segs B lyc Sc W memc mdc a HAR HXa) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
pose proof (AR_extra_law_ok segs B ly2 S2 W2 mem2 md2 a HAR2 ltac:(rewrite Eextra; exact HXa)) as (Yo & Yb & _).
apply KEEP.
- exact Xo.
- exact Yo.
- intros Hs. apply Xs. zlia.
- unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp. zlia. }
Qed.

Hypothesis stack_malloc_progress : stack_malloc_progressP B.
Local Notation code := (as_code B).

Lemma cm_stack_malloc_at : forall cid, astack_malloc_realizes segs B cid -> 0 <= cid <= 10 ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw,
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
YK11.getr regsT 3 = w64 (as_gp B) -> YK11.getr regsT 4 = w64 (as_tp B) ->
YK11.getr regsT 1 = raw -> YK0s.ret_ok raw ->
count_cid cid (frames Sc) < fs_frames cid ->
SRr segs W (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 (pc_stack_malloc code cid)) memT (YK11.seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists S2 regs2 mem2 md2 pos,
c2 = mkCfg (@YK11.mkst fx regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
ajournal STK sp0 FP ly S W0 mem md ((cid, pos) :: own) lyc S2 W mem2 md2 k /\
aregs_preserved regsT regs2 /\ YK11.getr regs2 10 = w64 (frame_addr lyc cid pos) /\
ablocks B lyc S2 = ablocks B lyc Sc /\ frames S2 = (cid, pos) :: frames Sc /\
st_nev S2 = st_nev Sc /\ (exists f, S2 = set_fs f Sc) /\
zero_shadow (aview segs (w_H W) mem2) SHADOW_OFF (frame_addr lyc cid pos) (fs_frame_bytes cid) /\
rdword (aview segs (w_H W) mem2) (frame_addr lyc cid pos + fs_frame_bytes cid - 8) = Some (flag_addr lyc cid pos) /\
(forall a, frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid -> apresent (w_H W) mem2 a) /\
acall_kept segs B lyc Sc W memT W mem2 (sp0 + o - ESTACK) (sp0 + o) (fun _ => False)).
Proof.
intros cid ASM Hcid W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw
HJ Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hcnt.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (ASTACK = 16384) as Has by reflexivity. assert (ESTACK = 4096) as Hes by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ESTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
  all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|]. split; [destruct HstkC as (Q1 & _); exact Q1|].
split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
destruct (stack_malloc_progress Sc cid HWF Hcid Hcnt) as (pos & S2 & Hpath).
destruct (cm_sm_path cid Sc pos S2 Hpath) as (Hfrs2 & Hchk2 & Hsecs2 & Hnev2 & Hqt2 & Hqg2 & Hset2).
eapply SRr_mono; [exact (ASM lyc Sc W regsT memT mdc pos S2 HPRE Hcnt Hpath)|].
cbv beta. intros W2 c2 HwleW (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hz & Hflag & Hfpres & Hfr & Hpres2).
assert (Eab2 : ablocks B lyc S2 = ablocks B lyc Sc) by (unfold ablocks, blocks; rewrite Hchk2; reflexivity).
assert (HJ1 : ajournal ESTACK (spZ regsT) [] lyc Sc W memT mdc [(cid, pos)] lyc S2 W mem2 md2 0).
{ apply (cm_sm_effect_journal ESTACK lyc Sc W regsT memT mdc lyc S2 W mem2 md2 [(cid, pos)] 0);
  [exact HAR2 | apply layout_le_refl | apply wle_refl | apply same_io_materialized; exact Hsame | exact Hfr | exact Hpres2
  | exact HAR | exact HstkC | cbn; exact Hfrs2 | zlia | zlia | rewrite Hsecs2; zlia | intros p n Hp; rewrite Eab2; exact Hp |].
  apply (qtight_ext Sc); [exact Hchk2 | exact Hqt2 | exact Hqg2 | exact HQT]. }
split; [reflexivity|]. exists S2, regs2, mem2, md2, pos.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. replace k with (k + 0) by zlia. change ((cid, pos) :: own) with ([(cid, pos)] ++ own).
eapply (ajournal_sub segs B LAWS cm_segs_low); [exact HJ | exact HJ1 | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Eab2|]. split; [exact Hfrs2|]. split; [exact Hnev2|].
split; [exact Hset2|].
split; [exact Hz|]. split; [exact Hflag|]. split; [exact Hfpres|].
rewrite Hsp' in HJ1.
eapply (acall_kept_of_journal segs B cm_segs_low); [exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
intros b m i Hb Hi _. rewrite Eab2. exact Hb.
Qed.

(* ======================================================================== *)
(* The journal after a footprint run, and after the release of the fake frame                                    *)
(* ======================================================================== *)

(* A run that changed only the bytes of the ranges Wl, each a byte the journal lets this call write and visible in
   the world, leaves the journal at its end memory (YCbq.v ajournal_exec, as check_value_cgW.v's cv_entry uses it). *)
Lemma cm_aj_munch : forall STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k memc' mdc' (Wl : list (Z * Z)),
  ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  munch Wl memc memc' -> mem_grows memc memc' -> same_but_materialized mdc mdc' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside Wl a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  (forall x : word, ~ outside Wl (bv_unsigned x) -> w_H W x = false) ->
  ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memc' mdc' k.
Proof.
  intros STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k memc' mdc' Wl HJ MU MG Hs HW Hvis.
  apply (ajournal_exec segs B LAWS cm_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k memc' mdc'
           (fun a => 0 <= a < 2 ^ 64 /\ ~ outside Wl a) HJ).
  - intros x Hx. unfold mrestrict. rewrite (MU x); [reflexivity|].
    destruct (cm_outside_dec Wl (bv_unsigned x)) as [Ho|Ho]; [exact Ho|].
    exfalso. apply Hx. split; [apply bv_unsigned_in_range | exact Ho].
  - intros x Hx. unfold mrestrict in *. destruct (w_H W x); [exact Hx|]. exact (MG x Hx).
  - intros x Hh. apply MU. destruct (cm_outside_dec Wl (bv_unsigned x)) as [Ho|Ho]; [exact Ho|].
    rewrite (Hvis x Ho) in Hh. discriminate.
  - exact Hs.
  - intros a [Ha Ho]. exact (HW a Ha Ho).
Qed.

Hypothesis ASF : astack_free_law segs B.
Hypothesis FFL : frame_flag_lawP segs B.

(* The fake frame given back: a run that wrote only bytes of its own frame (and its shadow) and the frame's flag
   byte, which it left 0, leaves the journal with no frame of its own at the state astack_free_law names (fuzz_uci
   UciCcKit.v ucc_flag_store_pi, after its run). *)
Lemma cm_release : forall STK sp0 FP ly S W0 mem md lyc Sc W memc mdc k cid pos memc' mdc' (Wl : list (Z * Z)),
  ajournal STK sp0 FP ly S W0 mem md [(cid, pos)] lyc Sc W memc mdc k ->
  munch Wl memc memc' -> mem_grows memc memc' -> same_but_materialized mdc mdc' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside Wl a ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc [(cid, pos)] a \/ a = flag_addr lyc cid pos) ->
  (forall x : word, ~ outside Wl (bv_unsigned x) -> w_H W x = false) ->
  aview segs (w_H W) memc' (flag_addr lyc cid pos) = Some 0 ->
  ajournal STK sp0 FP ly S W0 mem md [] lyc (stack_free_state cid pos Sc) W memc' mdc' k.
Proof.
  intros STK sp0 FP ly S W0 mem md lyc Sc W memc mdc k cid pos memc' mdc' Wl HJ MU MG Hs HW Hvis Hfl0.
  pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hkk & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
  destruct (FFL lyc Sc W memc mdc cid pos HAR Hin) as (Hfp & Hfo & Hfr_rng & Hfr_num).
  assert (Heqw : forall a, 0 <= a < 2 ^ 64 -> outside Wl a ->
    aview segs (w_H W) memc' a = aview segs (w_H W) memc a).
  { intros a Ha Ho. apply aview_eq_of. unfold mrestrict. rewrite (MU (Z_to_bv 64 a)); [reflexivity|].
    rewrite cm_u64 by exact Ha. exact Ho. }
  assert (MGr : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memc')).
  { intros x Hx. unfold mrestrict in *. destruct (w_H W x); [exact Hx|]. exact (MG x Hx). }
  pose proof (same_but_materialized_wvb mdc mdc' Hs) as Emd.
  assert (HAR' : AR segs B lyc (stack_free_state cid pos Sc) W memc' mdc').
  { eapply (ASF lyc Sc W memc mdc memc' mdc' cid pos HAR Hin).
    - exact Hfl0.
    - intros a Ha Ho Hne. destruct (cm_outside_dec Wl a) as [Hout|Hout]; [exact (Heqw a Ha Hout)|].
      destruct (HW a Ha Hout) as [Hw | Hw]; [|exact (False_ind _ (Hne Hw))].
      exact (False_ind _ (proj1 (awr_byte_cases segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) Ho)).
    - intros a Hv. eapply aview_keeps_vis; [exact MGr | exact Hv].
    - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
    - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
    - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
    - intros a _ Hh. apply MU. destruct (cm_outside_dec Wl (bv_unsigned (w64 a))) as [Ho|Ho]; [exact Ho|].
      rewrite (Hvis _ Ho) in Hh. discriminate. }
  eapply (ajournal_after_write segs B LAWS cm_segs_low STK sp0 FP ly S W0 mem md [(cid, pos)] lyc Sc W memc
    mdc k memc' mdc' (fun a => 0 <= a < 2 ^ 64 /\ ~ outside Wl a) (stack_free_state cid pos Sc) [] HJ).
  - intros a Ha Hna. apply Heqw; [exact Ha|].
    destruct (cm_outside_dec Wl a) as [Ho|Ho]; [exact Ho|]. exfalso. exact (Hna (conj Ha Ho)).
  - intros a Ha. eapply apresent_grows; [exact MGr | exact Ha].
  - exact Hs.
  - intros a [Ha Ho]. destruct (HW a Ha Ho) as [Hw | ->]; [left; exact Hw | right; split; [exact Hfo | exact Hfr_rng]].
  - exact HAR'.
  - unfold ablocks. rewrite blocks_stack_free_state. reflexivity.
  - reflexivity.
  - cbn. zlia.
  - exact (cm_sf_frames cid pos Sc (frames S) Hfrs).
  - pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
    apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT].
Qed.
End sm.

(* ======================================================================== *)
(* The walk                                                                   *)
(* ======================================================================== *)

Lemma cm_aview_munch : forall (H : word -> bool) (m m' : word -> option byte) (Wl : list (Z * Z)) a,
  munch Wl m m' -> 0 <= a < 2 ^ 64 -> outside Wl a -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof.
  intros H m m' Wl a MU Ha Ho. apply aview_eq_of. unfold mrestrict. rewrite (MU (Z_to_bv 64 a)); [reflexivity|].
  rewrite cm_u64 by exact Ha. exact Ho.
Qed.

(* A visible byte the view shows as v reads as the byte v. *)
Lemma cm_aview_of_bytes1 : forall (W : world tfibsegs) m a (b : byte),
  w_H W (Z_to_bv 64 a) = false -> bytes_at BImg.rsegs m a [b] -> aview tfibsegs (w_H W) m a = Some (bv_unsigned b).
Proof.
  intros W m a b Hv (H0 & H1 & H). rewrite (cm_aview_mrd W m a Hv).
  specialize (H 0%nat ltac:(cbn; lia)). rewrite Z.add_0_r in H. rewrite H. reflexivity.
Qed.

Lemma cm_nth_map_u : forall (bs : list byte) (j : nat),
  nth j (map (fun b : byte => bv_unsigned b) bs) 0 = bv_unsigned (nth j bs (Z_to_bv 8 0)).
Proof.
  intros bs j. replace 0 with ((fun b : byte => bv_unsigned b) (Z_to_bv 8 0)) at 1 by reflexivity.
  apply map_nth.
Qed.

Lemma cm_rng_cell : forall (W : world tfibsegs) a n, In (a, n) wire_asan_cell_ranges -> a + n <= 2 ^ 64 ->
  ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) a n.
Proof.
  intros W a n Hin Ht. pose proof (WCL.wcc_leafb_seg_of a n Hin) as Hc.
  pose proof (WCL.wcc_leafb_covers_lo a n Hc) as H0.
  apply (WCL.wcc_leafb_rng W); [exact H0 | exact Ht |].
  intros b Hb. replace b with (a + (b - a)) by lia.
  apply (WCL.wcc_leafb_covers_visible (w_H W) a n); [exact (w_Hoff W) | exact Hc | lia | exact Ht].
Qed.

Section Walk.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation sink := YE2k.tfib_sink_head.
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
Hypothesis SEG1 : cm_seg1_stmt.
Hypothesis SEG2A : cm_seg2a_stmt.
Hypothesis PRE : cm_pre_stmt.
Hypothesis SEG2C : cm_seg2c_stmt.
Hypothesis CMP : cm_cmp_stmt.
Hypothesis REL : cm_rel_stmt.
Local Abbreviation ajournalA := (@ajournal rc sink segs B).

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
(* The inner journal: from the entry state, stack window [spZ regs - CM_STK, spZ regs). *)
Local Abbreviation JI own1 ly1 S1 m1 md1 :=
  (ajournalA CM_STK (spZ regs) [] lyc Sc W memc mdc own1 ly1 S1 W m1 md1 0).
Local Abbreviation GR rg i := (YK11.getr rg (Z_to_bv 5 i)).
Local Abbreviation SP1 := (cm_sp1 (spZ regs)).

(* The twelve words the prologue saved, [entry sp - 96, entry sp). *)
Definition cm_saves (m : word -> option byte) : Prop :=
  ro_cells BImg.rsegs m (spZ regs - 96)
    [C8 (GR regs 26); C8 (GR regs 25); C8 (GR regs 24); C8 (GR regs 23); C8 (GR regs 22); C8 (GR regs 21);
     C8 (GR regs 20); C8 (GR regs 19); C8 (GR regs 18); C8 (GR regs 9); C8 (GR regs 8); C8 (GR regs 1)].

(* The registers the walk keeps from the prologue on: sp (the realigned sp), gp, tp, s0 (the entry sp), s1, s8 (the
   shadow offset), s11 untouched. *)
Definition cm_kept (rg : bvmap 5 word) : Prop :=
  GR rg 2 = w64 SP1 /\ GR rg 3 = GR regs 3 /\ GR rg 4 = GR regs 4 /\ GR rg 8 = w64 (spZ regs) /\
  GR rg 9 = w64 SP1 /\ GR rg 24 = w64 BC.ASAN_K /\ GR rg 27 = GR regs 27.

Ltac kp_by HP i K := etransitivity; [apply (HP i); unfold acallee_saved; lia | exact K].

Lemma cm_kept_pres : forall r1 r2, cm_kept r1 -> aregs_preserved r1 r2 -> cm_kept r2.
Proof.
  intros r1 r2 (K2 & K3 & K4 & K8 & K9 & K24 & K27) HP. unfold cm_kept.
  split; [kp_by HP 2 K2|]. split; [kp_by HP 3 K3|]. split; [kp_by HP 4 K4|]. split; [kp_by HP 8 K8|].
  split; [kp_by HP 9 K9|]. split; [kp_by HP 24 K24|]. kp_by HP 27 K27.
Qed.

(* ---- facts of the entry ---- *)

Lemma cm_HARc : AR segs B lyc Sc W memc mdc.
Proof. destruct HJ as (HAR & _). exact HAR. Qed.

Lemma cm_JI0 : JI [] lyc Sc memc mdc.
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

Lemma cm_sp_rng : YM05.alloc_ceiling + CM_STK <= spZ regs /\ spZ regs <= 2 ^ 47.
Proof.
  pose proof cm_JI0 as J. destruct J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    (_ & _ & Hc & Hlo & Hhi & H47 & _) & _).
  lia.
Qed.

Lemma cm_sp1_rng : spZ regs - 144 <= SP1 <= spZ regs - 128 /\ SP1 mod 32 = 0.
Proof.
  unfold cm_sp1. pose proof (Z.div_mod (spZ regs - 128) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 128) 32 ltac:(lia)) as M.
  destruct (proj1 (Z.mod_divide (spZ regs) 16 ltac:(lia)) Hal) as [q Hq].
  split; [lia|]. rewrite Z.mul_comm, Z_mod_mult. reflexivity.
Qed.

Lemma cm_win : forall own1 ly1 S1 m1 md1, JI own1 ly1 S1 m1 md1 ->
  forall a, spZ regs - CM_STK <= a < spZ regs -> apresent (w_H W) m1 a.
Proof.
  intros own1 ly1 S1 m1 md1 J.
  destruct J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). exact Hpres.
Qed.

Lemma cm_AR : forall own1 ly1 S1 m1 md1, JI own1 ly1 S1 m1 md1 -> AR segs B ly1 S1 W m1 md1.
Proof. intros own1 ly1 S1 m1 md1 J. destruct J as (HAR & _). exact HAR. Qed.

Lemma cm_saves_kept : forall m m', cm_saves m ->
  (forall a, spZ regs - 96 <= a < spZ regs -> w_H W (Z_to_bv 64 a) = false /\
     aview segs (w_H W) m' a = aview segs (w_H W) m a) ->
  cm_saves m'.
Proof.
  intros m m' [Hwf Hb] HK. split; [exact Hwf|].
  apply (cm_bytes_kept W m m' _ _ Hb). intros i Hi.
  change (length (cells_bytes [C8 (GR regs 26); C8 (GR regs 25); C8 (GR regs 24); C8 (GR regs 23);
    C8 (GR regs 22); C8 (GR regs 21); C8 (GR regs 20); C8 (GR regs 19); C8 (GR regs 18); C8 (GR regs 9);
    C8 (GR regs 8); C8 (GR regs 1)])) with 96%nat in Hi.
  apply HK. lia.
Qed.

(* The frame's bytes at a state of the inner journal whose blocks keep the caller's (check_value_cgW.v cv_reply_at):
   f's n bytes are a caller block's, which the journal keeps. *)
Lemma cm_f_aview : forall own1 ly1 S1 m1 md1, JI own1 ly1 S1 m1 md1 -> 0 < n ->
  (forall b nb, In (b, nb) (ablocks B lyc Sc) -> In (b, nb) (ablocks B ly1 S1)) ->
  forall i, 0 <= i < n -> aview segs (w_H W) m1 (f + i) = Some (bv_unsigned (cm_byte bs i)).
Proof.
  intros own1 ly1 S1 m1 md1 J1 Hn0 Hsub i Hi.
  destruct (Hblk Hn0) as (bA & nA & HbA & HbA1 & HbA2).
  assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia).
  pose proof J1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  replace (f + i) with (bA + (f + i - bA)) by lia.
  rewrite (F2 bA nA (f + i - bA) HbA (Hsub _ _ HbA) ltac:(lia) ltac:(intros (r0 & Hr0 & _); destruct Hr0)).
  replace (bA + (f + i - bA)) with (f + Z.of_nat (Z.to_nat i)) by lia.
  rewrite (cm_garr8_aview (w_H W) memc f _ (Z.to_nat i) Hgarr ltac:(rewrite length_map; lia)).
  rewrite cm_nth_map_u. reflexivity.
Qed.

Lemma cm_f_mrd : forall own1 ly1 S1 m1 md1, JI own1 ly1 S1 m1 md1 -> 0 < n ->
  (forall b nb, In (b, nb) (ablocks B lyc Sc) -> In (b, nb) (ablocks B ly1 S1)) ->
  forall i, 0 <= i < n -> mrd BImg.rsegs m1 (wa (f + i)) = Some (cm_byte bs i).
Proof.
  intros own1 ly1 S1 m1 md1 J1 Hn0 Hsub i Hi.
  rewrite (cm_mrd_of_aview W m1 (f + i) _ (cm_f_aview own1 ly1 S1 m1 md1 J1 Hn0 Hsub i Hi)).
  f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* The block of f, with its bounds. *)
Lemma cm_f_block : 0 < n -> exists bA nA, In (bA, nA) (ablocks B lyc Sc) /\ bA <= f /\ f + n <= bA + req_size nA /\
  4096 <= f /\ f + n <= YM05.alloc_ceiling.
Proof.
  intros Hn0. destruct (Hblk Hn0) as (bA & nA & HbA & HbA1 & HbA2).
  pose proof (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA cm_HARc HbA) as (_ & HA4 & HAc & _ & _ & _ & _).
  assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia).
  exists bA, nA. split; [exact HbA|]. split; [exact HbA1|]. split; [lia|]. split; lia.
Qed.

Lemma cm_n_rng : 0 <= n < 2 ^ 47.
Proof.
  pose proof asan_consts as (C1 & _).
  destruct (Z.eq_dec n 0) as [Hn|Hn]; [lia|].
  destruct (cm_f_block ltac:(lia)) as (bA & nA & _ & _ & _ & H4 & Hc). lia.
Qed.

(* The fake frame, its shadow and its flag byte lie apart, and below the machine stack. *)
Lemma cm_sh_sep : forall Fz, 4096 <= Fz -> Fz + 64 <= YM05.alloc_ceiling -> in_app Fz 64 ->
  (BC.shadow_addr Fz + 8 <= Fz \/ Fz + 64 <= BC.shadow_addr Fz) /\ 0 <= BC.shadow_addr Fz /\
  BC.shadow_addr Fz + 8 <= YM05.alloc_ceiling - 2 ^ 20.
Proof.
  intros Fz H0 H1 [_ Happ]. pose proof asan_consts as (C1 & _).
  pose proof (Z.div_mod Fz 8 ltac:(lia)). pose proof (Z.mod_pos_bound Fz 8 ltac:(lia)).
  unfold BC.shadow_addr, BC.ASAN_K. unfold kLowShadowBeg, kHighMemBeg in Happ. lia.
Qed.

Lemma cm_flag_sep : forall ly1 S1 m1 md1 pos, AR segs B ly1 S1 W m1 md1 -> In (CM_CID, pos) (frames S1) ->
  (flag_addr ly1 CM_CID pos + 1 <= frame_addr ly1 CM_CID pos \/
   frame_addr ly1 CM_CID pos + 64 <= flag_addr ly1 CM_CID pos) /\
  (flag_addr ly1 CM_CID pos + 1 <= BC.shadow_addr (frame_addr ly1 CM_CID pos) \/
   BC.shadow_addr (frame_addr ly1 CM_CID pos) + 8 <= flag_addr ly1 CM_CID pos).
Proof.
  intros ly1 S1 m1 md1 pos HAR Hin.
  destruct (al_frames _ _ LAWS _ _ _ _ _ CM_CID pos HAR Hin) as (_ & _ & HFb & _).
  destruct (frames_bounds segs B LAWS _ _ _ _ _ CM_CID pos HAR Hin) as (HF0 & HFc & _).
  destruct (FFL _ _ _ _ _ CM_CID pos HAR Hin) as (_ & HFLo & _ & (HFL4 & HFLz & HFLc)).
  change (fs_frame_bytes CM_CID) with 64 in HFb, HFc.
  pose proof asan_consts as (C1 & _).
  set (Fz := frame_addr ly1 CM_CID pos) in *. set (FLz := flag_addr ly1 CM_CID pos) in *.
  split.
  - destruct (Z_lt_le_dec FLz Fz) as [H1|H1]; [left; lia|].
    destruct (Z_lt_le_dec FLz (Fz + 64)) as [H2|H2]; [|right; lia].
    exfalso. exact (proj2 (HFb FLz ltac:(lia)) HFLo).
  - destruct HFLz as [_ HFLz].
    pose proof (Z.div_mod Fz 8 ltac:(lia)). pose proof (Z.mod_pos_bound Fz 8 ltac:(lia)).
    unfold BC.shadow_addr, BC.ASAN_K. lia.
Qed.

(* A word of the view, as a raw cell. *)
Lemma cm_ro_of_rdword : forall m a v, rdword (aview segs (w_H W) m) a = Some v -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  ro_cells BImg.rsegs m a [C8 (Z_to_bv 64 v)].
Proof.
  intros m a v Hr H0 H1.
  pose proof (val_mem_of_rdword segs (w_H W) m a v Hr) as HV.
  pose proof (WCL.wcc_leafb_bytes_le W m a 8 v v HV eq_refl H0 H1) as HB.
  split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
  rewrite <- OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib.StepF.Z_to_le_bytes_lit8. exact HB.
Qed.

(* ---- 7 and 8: CM_RET_LEAF (the leaf returned) to the return, the release and the post ---- *)
Lemma cm_at_retleaf : forall pos S2 regs3 mem3 md3,
  JI [(CM_CID, pos)] lyc S2 mem3 md3 ->
  frames S2 = (CM_CID, pos) :: frames Sc ->
  ablocks B lyc S2 = ablocks B lyc Sc ->
  (exists f0, S2 = set_fs f0 Sc) ->
  cm_kept regs3 ->
  GR regs3 10 = w64 (cm_bit n bs) ->
  GR regs3 18 = w64 (frame_addr lyc CM_CID pos) -> GR regs3 19 = w64 f ->
  GR regs3 21 = w64 (frame_addr lyc CM_CID pos + 32) ->
  GR regs3 22 = w64 (frame_addr lyc CM_CID pos) ->
  GR regs3 23 = w64 (BC.shadow_addr (frame_addr lyc CM_CID pos)) ->
  GR regs3 25 = w64 (Z.of_nat (PMC.meter_eo n bs)) -> GR regs3 26 = w64 (cm_bit n bs) ->
  bytes_at BImg.rsegs mem3 (frame_addr lyc CM_CID pos + 32) (le2 (Z_to_bv 64 (cm_ctr n bs))) ->
  rdword (aview segs (w_H W) mem3) (frame_addr lyc CM_CID pos + 56) = Some (flag_addr lyc CM_CID pos) ->
  cm_saves mem3 ->
  SRr segs W (@cfg_at fx segs CM_RET_LEAF regs3 mem3 md3) POST.
Proof.
  intros pos S2 regs3 mem3 md3 J3 Hfr2 Eab2 Hset2 HK G10 G18 G19 G21 G22 G23 G25 G26 Hctr HFLw HSV.
  pose proof HK as (K2 & K3 & K4 & K8 & K9 & K24 & K27).
  pose proof cm_sp_rng as [Hsp1 Hsp2]. pose proof cm_sp1_rng as [Gsp1 Hsp1al].
  unfold CM_STK, CM_FRAME, CM_ALIGN, ESTACK in Hsp1.
  pose proof asan_consts as (C1 & _).
  pose proof cm_n_rng as Hnr.
  pose proof (cm_AR _ _ _ _ _ J3) as HAR3.
  assert (Hin2 : In (CM_CID, pos) (frames S2)) by (rewrite Hfr2; left; reflexivity).
  destruct (al_frames _ _ LAWS _ _ _ _ _ CM_CID pos HAR3 Hin2) as (HFal & HFapp & HFb & HFsh).
  destruct (frames_bounds segs B LAWS _ _ _ _ _ CM_CID pos HAR3 Hin2) as (HF0 & HFc & _).
  destruct (FFL _ _ _ _ _ CM_CID pos HAR3 Hin2) as (HFLp & HFLo & (HFLapp & HFLimg) & (HFL4 & HFLz & HFLc)).
  destruct (cm_flag_sep _ _ _ _ pos HAR3 Hin2) as (FS1 & FS2).
  change (fs_frame_bytes CM_CID) with 64 in HFb, HFc, HFapp. change (fs_frame_bytes CM_CID / 8) with 8 in HFsh.
  set (Fz := frame_addr lyc CM_CID pos) in *. set (FLz := flag_addr lyc CM_CID pos) in *.
  destruct (cm_sh_sep Fz HF0 HFc HFapp) as (SS1 & SS2 & SS3).
  assert (ESH : forall i, YG0f.shadow_addr Fz + i = BC.shadow_addr Fz + i) by (intros i; rewrite cm_shadow_addr_eq; reflexivity).
  assert (Psh : forall a, BC.shadow_addr Fz <= a < BC.shadow_addr Fz + 8 -> apresent (w_H W) mem3 a).
  { intros a Ha. replace a with (YG0f.shadow_addr Fz + (a - BC.shadow_addr Fz)) by (rewrite ESH; lia).
    exact (proj1 (HFsh (a - BC.shadow_addr Fz) ltac:(lia))). }
  assert (Pfr : forall a, Fz <= a < Fz + 64 -> apresent (w_H W) mem3 a) by (intros a Ha; exact (proj1 (HFb a Ha))).
  assert (Pwin : forall a, spZ regs - 96 <= a < spZ regs -> apresent (w_H W) mem3 a)
    by (intros a Ha; apply (cm_win _ _ _ _ _ J3); unfold CM_STK, CM_FRAME, CM_ALIGN, ESTACK; lia).
  destruct (cm_rw_carve (w_H W) mem3 (BC.shadow_addr Fz) 8 ltac:(lia) ltac:(lia) Psh) as (sj & RSH).
  destruct (cm_rw_carve (w_H W) mem3 Fz 8 ltac:(lia) ltac:(lia) ltac:(intros a Ha; apply Pfr; lia)) as (hj & RF).
  destruct (cm_rw_carve (w_H W) mem3 FLz 1 ltac:(lia) ltac:(lia)
    ltac:(intros a Ha; replace a with FLz by lia; exact HFLp)) as (lj & RFL).
  pose proof (cm_ro_of_rdword mem3 (Fz + 56) FLz HFLw ltac:(lia) ltac:(lia)) as RFW.
  set (P := fun ms' : machine_state => exists (a1' a2' a3' : word) (m4 : word -> option byte),
    ms' = MS (mkR (GR regs 1) (Z_to_bv 64 (spZ regs)) (GR regs3 3) (GR regs3 4) (GR regs3 5) (GR regs3 6)
               (GR regs3 7) (GR regs 8) (GR regs 9) (Z_to_bv 64 FLz) a1' a2' a3' (GR regs3 14) (GR regs3 15)
               (GR regs3 16) (GR regs3 17) (GR regs 18) (GR regs 19) (GR regs 20) (GR regs 21) (GR regs 22)
               (GR regs 23) (GR regs 24) (GR regs 25) (GR regs 26) (GR regs3 27) (GR regs3 28) (GR regs3 29)
               (GR regs3 30) (GR regs3 31))
             (@fp_regs fx) (ret_pc (GR regs 1)) (@fp_csr fx) None m4 (YK11.seg_rom tfibsegs) /\
    munch [(BC.shadow_addr Fz, BC.shadow_addr Fz + 8); (Fz, Fz + 8); (FLz, FLz + 1)] mem3 m4 /\
    wmono BImg.rsegs mem3 m4 /\ bytes_at BImg.rsegs m4 FLz [Z_to_bv 8 0]).
  eapply (@cm_run fx W regs3 mem3 md3 CM_RET_LEAF P).
  { unfold LCK.ms_of_regs. rewrite G10, G19, G21, K24, G25, G26, G18, G22, G23.
    eapply CMP with (f := f) (n := n) (Fa := Fz) (bs := bs).
    - lia.
    - exact Hlen.
    - exact HF0.
    - lia.
    - exact Hctr.
    - apply (cm_rng_present W mem3); [lia | lia | intros b Hb; apply Pfr; lia].
    - intros Hok.
      assert (Hn1 : 1000 <= n).
      { unfold PMC.meter_ok in Hok. apply andb_true_iff in Hok as [Hok _]. apply andb_true_iff in Hok as [Hok _].
        apply andb_true_iff in Hok as [_ Hok]. apply Z.leb_le in Hok. exact Hok. }
      destruct (cm_f_block ltac:(lia)) as (bA & nA & HbA & HbA1 & HbA2 & Hf4 & Hfc).
      assert (HbA3 : In (bA, nA) (ablocks B lyc S2)) by (rewrite Eab2; exact HbA).
      split; [exact Hf4|]. split; [lia|]. split.
      { intros i Hi. apply (cm_f_mrd _ _ _ _ _ J3 ltac:(lia) ltac:(intros b nb Hb; rewrite Eab2; exact Hb)). lia. }
      split; [exact (WCL.wcc_leafb_addressable_block B LAWS _ _ _ _ _ bA nA (f + 12) 8 HAR3 HbA3 ltac:(lia) ltac:(lia) ltac:(lia))|].
      split; [exact (WCL.wcc_leafb_rng_block B LAWS _ _ _ _ _ bA nA (f + 12) 8 HAR3 HbA3 ltac:(lia) ltac:(lia))|].
      pose proof (WCL.wcc_leafb_rng_shadow_block B LAWS _ _ _ _ _ bA nA (f + 12) 8 HAR3 HbA3 ltac:(lia) ltac:(lia) ltac:(lia))
        as R. replace (f + 12 + 8 - 1) with (f + 19) in R by lia. exact R.
    - intros a0' a1' a2' a3' s3' s9'.
      eapply ExecF.evtF_mono.
      + eapply REL with (Fa := Fz) (FL := FLz) (sp0 := spZ regs) (cra := GR regs 1) (c0 := GR regs 8)
          (c1 := GR regs 9) (c2 := GR regs 18) (c3 := GR regs 19) (c4 := GR regs 20) (c5 := GR regs 21)
          (c6 := GR regs 22) (c7 := GR regs 23) (c8 := GR regs 24) (c9 := GR regs 25) (c10 := GR regs 26).
        * exact HF0.
        * unfold CM_STK, CM_FRAME, CM_ALIGN, ESTACK in *. lia.
        * exact SS1.
        * unfold CM_STK, CM_FRAME, CM_ALIGN, ESTACK in *. lia.
        * lia.
        * unfold CM_STK, CM_FRAME, CM_ALIGN, ESTACK in *. lia.
        * exact FS1.
        * exact FS2.
        * lia.
        * rewrite K8. unfold w64. apply cm_u64. unfold spZ.
          pose proof (bv_unsigned_in_range 64 (YK11.getr regs 2)) as R. unfold bv_modulus in R. exact R.
        * exact RSH.
        * exact RF.
        * exact RFW.
        * exact RFL.
        * exact HSV.
        * apply (cm_rng_present W mem3); [lia | lia | exact Psh].
        * apply (cm_rng_present W mem3); [lia | lia | intros b Hb; apply Pfr; lia].
        * apply (cm_rng_present W mem3); [lia | lia | intros b Hb; apply Pfr; lia].
        * apply (cm_rng_present W mem3); [lia | lia | intros b Hb; replace b with FLz by lia; exact HFLp].
        * apply (cm_rng_present W mem3); [lia | lia | intros b Hb; apply Pwin; lia].
      + intros ms' (m4 & -> & MU & WM & Hfl). exists a1', a2', a3', m4. split; [reflexivity|].
        split; [exact MU|]. split; [exact WM | exact Hfl]. }
  intros ms' md' (ms0 & (a1' & a2' & a3' & m4 & -> & MU & WM & Hfl0) & EQV & MG) SBM.
  destruct (cm_regs_of EQV) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 &
    E16 & E17 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & E28 & E29 & E30 & E31).
  assert (Hret : ret_pc (GR regs 1) = GR regs 1) by (apply LeafCgFacts.ret_ok_stmt_YK0s; exact Hra).
  rewrite Hret in EQV.
  rewrite (cm_ms_shape _ _ _ _ EQV).
  (* the visible bytes the release wrote *)
  assert (Hvis : forall x : word,
    ~ outside [(BC.shadow_addr Fz, BC.shadow_addr Fz + 8); (Fz, Fz + 8); (FLz, FLz + 1)] (bv_unsigned x) ->
    w_H W x = false).
  { intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x).
    destruct (Z_lt_le_dec (bv_unsigned x) (BC.shadow_addr Fz)) as [L1|L1];
    [|destruct (Z_lt_le_dec (bv_unsigned x) (BC.shadow_addr Fz + 8)) as [L2|L2];
      [exact (proj1 (Psh _ (conj L1 L2)))|]];
    (destruct (Z_lt_le_dec (bv_unsigned x) Fz) as [L3|L3];
     [|destruct (Z_lt_le_dec (bv_unsigned x) (Fz + 8)) as [L4|L4]; [exact (proj1 (Pfr (bv_unsigned x) ltac:(lia)))|]]);
    (destruct (Z.eq_dec (bv_unsigned x) FLz) as [L5|L5]; [rewrite L5; exact (proj1 HFLp)|]);
    exfalso; apply Hx; cbn [outside]; repeat split; lia. }
  assert (HW : forall a, 0 <= a < 2 ^ 64 ->
    ~ outside [(BC.shadow_addr Fz, BC.shadow_addr Fz + 8); (Fz, Fz + 8); (FLz, FLz + 1)] a ->
    awr_byte CM_STK (spZ regs) [] (ablocks B lyc Sc) (ablocks B lyc S2) lyc [(CM_CID, pos)] a \/ a = FLz).
  { intros a Ha Hx.
    destruct (Z.eq_dec a FLz) as [L5|L5]; [right; exact L5|]. left. right; right; right.
    exists CM_CID, pos. split; [left; reflexivity|].
    destruct (Z_lt_le_dec a Fz) as [L3|L3];
    [|destruct (Z_lt_le_dec a (Fz + 8)) as [L4|L4]; [left; unfold in_zr; cbn [fst snd]; fold Fz;
       change (fs_frame_bytes CM_CID) with 64; lia|]];
    (destruct (Z_lt_le_dec a (BC.shadow_addr Fz)) as [L1|L1];
     [|destruct (Z_lt_le_dec a (BC.shadow_addr Fz + 8)) as [L2|L2];
       [right; unfold in_zr; cbn [fst snd]; fold Fz; change (fs_frame_bytes CM_CID / 8) with 8;
        rewrite (cm_shadow_addr_eq Fz) in L1, L2; lia|]]);
    exfalso; apply Hx; cbn [outside]; repeat split; lia. }
  assert (Hfl : aview segs (w_H W) m4 FLz = Some 0).
  { rewrite (cm_aview_of_bytes1 W m4 FLz _ (proj1 HFLp) Hfl0). reflexivity. }
  pose proof (cm_release B LAWS ASF FFL CM_STK (spZ regs) [] lyc Sc W memc mdc lyc S2 W mem3 md3 0 CM_CID pos m4 md'
    _ J3 MU MG SBM HW Hvis Hfl) as J4.
  set (S3 := stack_free_state CM_CID pos S2) in *.
  assert (Hfr3 : frames S3 = frames Sc) by exact (cm_sf_frames CM_CID pos S2 (frames Sc) Hfr2).
  assert (Eab3 : ablocks B lyc S3 = ablocks B lyc Sc).
  { unfold S3, ablocks. rewrite blocks_stack_free_state. fold (ablocks B lyc S2). exact Eab2. }
  apply SRr_ret. unfold wire_cm_post.
  exists lyc, S3, (ms_regs ms'), m4, md'.
  split; [reflexivity|].
  split.
  { pose proof (ajournal_sub segs B LAWS cm_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
                  CM_STK (spZ regs) [] [] lyc S3 W m4 md' 0 HJ J4 Hwlo Hwhi
                  ltac:(intros a (r0 & Hr0 & _); destruct Hr0)) as J.
    cbn [app] in J. unfold CM_EV. exact J. }
  split.
  { intros i Hi. unfold acallee_saved in Hi.
    assert (Hc : i = 2 \/ i = 3 \/ i = 4 \/ i = 8 \/ i = 9 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/
                 i = 23 \/ i = 24 \/ i = 25 \/ i = 26 \/ i = 27) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
    - etransitivity; [exact E2|]. unfold spZ. apply Z_to_bv_bv_unsigned.
    - etransitivity; [exact E3|]. exact K3.
    - etransitivity; [exact E4|]. exact K4.
    - exact E8.
    - exact E9.
    - exact E18.
    - exact E19.
    - exact E20.
    - exact E21.
    - exact E22.
    - exact E23.
    - exact E24.
    - exact E25.
    - exact E26.
    - etransitivity; [exact E27|]. exact K27. }
  split; [exact Hfr3|].
  split; [rewrite Eab3; apply Permutation_refl|].
  split.
  { apply (acall_kept_of_journal segs B cm_segs_low CM_STK (spZ regs) [] [] lyc Sc W memc mdc lyc S3 W m4
             md' 0 (fun _ => False) J4 cm_HARc).
    - intros a (r0 & Hr0 & _). destruct Hr0.
    - intros b m i Hb _ _. rewrite Eab3. exact Hb.
    - exact sink_closed_nil. }
  destruct Hset2 as (f0 & Ef0). unfold S3, stack_free_state. rewrite Ef0.
  apply (mo_le_set_fs_r MT MTF). apply (mo_le_set_fs_r MT MTF). exact (mo_le_refl MT MTL Sc).
Qed.

Lemma cm_mrd_of_bytes1 : forall m a (b : byte), bytes_at BImg.rsegs m a [b] -> mrd BImg.rsegs m (wa a) = Some b.
Proof. intros m a b (H0 & H1 & H). specialize (H 0%nat ltac:(cbn; lia)). rewrite Z.add_0_r in H. exact H. Qed.

(* An eight-byte word of the view, kept by a step that writes elsewhere (check_clamp_cgW.v cc_rdword_frame). *)
Lemma cm_rdword_frame : forall (rd rd' : reader) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
  intros rd rd' a Hk. unfold rdword.
  pose proof (Hk 0 ltac:(lia)) as K0. rewrite Z.add_0_r in K0.
  rewrite K0, (Hk 1 ltac:(lia)), (Hk 2 ltac:(lia)), (Hk 3 ltac:(lia)), (Hk 4 ltac:(lia)),
          (Hk 5 ltac:(lia)), (Hk 6 ltac:(lia)), (Hk 7 ltac:(lia)). reflexivity.
Qed.

(* ---- 6: the call of rp_meter_counter(f, n, &ctr) at CM_LEAF (the statement's wire_leaf_wr_at premise) ---- *)
Lemma cm_leaf_call : forall pos S2 regsL memL mdL,
  JI [(CM_CID, pos)] lyc S2 memL mdL ->
  frames S2 = (CM_CID, pos) :: frames Sc ->
  ablocks B lyc S2 = ablocks B lyc Sc ->
  (exists f0, S2 = set_fs f0 Sc) ->
  cm_kept regsL ->
  GR regsL 1 = Z_to_bv 64 CM_RET_LEAF ->
  GR regsL 10 = w64 f -> GR regsL 11 = w64 n -> GR regsL 12 = w64 (frame_addr lyc CM_CID pos + 32) ->
  GR regsL 18 = w64 (frame_addr lyc CM_CID pos) -> GR regsL 19 = w64 f ->
  GR regsL 21 = w64 (frame_addr lyc CM_CID pos + 32) ->
  GR regsL 22 = w64 (frame_addr lyc CM_CID pos) ->
  GR regsL 23 = w64 (BC.shadow_addr (frame_addr lyc CM_CID pos)) ->
  GR regsL 25 = w64 (Z.of_nat (PMC.meter_eo n bs)) -> GR regsL 26 = w64 (cm_bit n bs) ->
  bytes_at BImg.rsegs memL (BC.shadow_addr (frame_addr lyc CM_CID pos) + 4) [Z_to_bv 8 2] ->
  bytes_at BImg.rsegs memL (frame_addr lyc CM_CID pos + 32) (le2 (Z_to_bv 64 0xa5c3)) ->
  rdword (aview segs (w_H W) memL) (frame_addr lyc CM_CID pos + 56) = Some (flag_addr lyc CM_CID pos) ->
  cm_saves memL ->
  SRr segs W (mkCfg (@YK11.mkst fx regsL (Z_to_bv 64 CM_LEAF) memL (YK11.seg_rom segs)) mdL) POST.
Proof.
  intros pos S2 regsL memL mdL JL Hfr2 Eab2 Hset2 HK GL1 GL10 GL11 GL12 GL18 GL19 GL21 GL22 GL23 GL25 GL26
    Hsh4 Hctr0 HFLw HSV.
  pose proof HK as (K2 & K3 & K4 & K8 & K9 & K24 & K27).
  pose proof cm_sp_rng as [Hsp1 Hsp2]. pose proof cm_sp1_rng as [Gsp1 Hsp1al].
  unfold CM_STK, CM_FRAME, CM_ALIGN, ESTACK in Hsp1.
  pose proof asan_consts as (C1 & _).
  pose proof cm_n_rng as Hnr.
  pose proof (cm_AR _ _ _ _ _ JL) as HARL.
  assert (Hin2 : In (CM_CID, pos) (frames S2)) by (rewrite Hfr2; left; reflexivity).
  destruct (al_frames _ _ LAWS _ _ _ _ _ CM_CID pos HARL Hin2) as (HFal & HFapp & HFb & HFsh).
  destruct (frames_bounds segs B LAWS _ _ _ _ _ CM_CID pos HARL Hin2) as (HF0 & HFc & _).
  change (fs_frame_bytes CM_CID) with 64 in HFb, HFc, HFapp. change (fs_frame_bytes CM_CID / 8) with 8 in HFsh.
  set (Fz := frame_addr lyc CM_CID pos) in *. set (FLz := flag_addr lyc CM_CID pos) in *.
  destruct (cm_sh_sep Fz HF0 HFc HFapp) as (SS1 & SS2 & SS3).
  assert (Psh : forall a, BC.shadow_addr Fz <= a < BC.shadow_addr Fz + 8 -> apresent (w_H W) memL a).
  { intros a Ha. replace a with (YG0f.shadow_addr Fz + (a - BC.shadow_addr Fz)) by (rewrite cm_shadow_addr_eq; lia).
    exact (proj1 (HFsh (a - BC.shadow_addr Fz) ltac:(lia))). }
  assert (Pfr : forall a, Fz <= a < Fz + 64 -> apresent (w_H W) memL a) by (intros a Ha; exact (proj1 (HFb a Ha))).
  assert (HF8 : Fz mod 8 = 0) by (destruct (proj1 (Z.mod_divide Fz 32 ltac:(lia)) HFal) as [q Hq]; rewrite Hq;
    replace (q * 32) with ((q * 4) * 8) by lia; apply Z_mod_mult).
  assert (ESH32 : forall i, 0 <= i < 2 -> BC.shadow_addr (Fz + 32 + i) = BC.shadow_addr Fz + 4).
  { intros i Hi. unfold BC.shadow_addr. destruct (proj1 (Z.mod_divide Fz 8 ltac:(lia)) HF8) as [q Hq]. rewrite Hq.
    replace (q * 8 + 32 + i) with (i + (q + 4) * 8) by lia. rewrite Z.div_add by lia.
    rewrite (Z.div_small i 8) by lia. replace (q * 8) with (0 + q * 8) by lia. rewrite Z.div_add by lia. cbn. lia. }
  assert (ESP : bv_unsigned (GR regsL 2) = SP1) by (rewrite K2; unfold w64; apply cm_u64; lia).
  assert (SPL : spZ regsL = SP1) by exact ESP.
  assert (EA1 : bv_unsigned (GR regsL 11) = n) by (rewrite GL11; unfold w64; apply cm_u64; lia).
  assert (EA2 : bv_unsigned (GR regsL 12) = Fz + 32) by (rewrite GL12; unfold w64; apply cm_u64; lia).
  assert (Hf14 : 14 <= n -> bv_unsigned (GR regsL 10) = f /\ exists bA nA, In (bA, nA) (ablocks B lyc S2) /\
             bA <= f /\ f + n <= bA + req_size nA /\ 4096 <= f /\ f + n <= YM05.alloc_ceiling).
  { intros H14. destruct (cm_f_block ltac:(lia)) as (bA & nA & HbA & HbA1 & HbA2 & Hf4 & Hfc).
    split; [rewrite GL10; unfold w64; apply cm_u64; lia|].
    exists bA, nA. rewrite Eab2. auto. }
  assert (Hok1000 : PMC.meter_ok n bs = true -> 1000 <= n).
  { intros Hok. unfold PMC.meter_ok in Hok. apply andb_true_iff in Hok as [Hok _]. apply andb_true_iff in Hok as [Hok _].
    apply andb_true_iff in Hok as [_ Hok]. apply Z.leb_le in Hok. exact Hok. }
  set (WR := LMC.wire_rmc_wr n bs (Fz + 32)).
  assert (HWRr : forall x, LCK.in_wr WR x -> Fz + 32 <= x < Fz + 34).
  { intros x Hx. unfold WR, LMC.wire_rmc_wr in Hx. destruct (PMC.meter_ok n bs);
    unfold LCK.in_wr in Hx; [|inversion Hx].
    apply Exists_cons in Hx. destruct Hx as [Hx|Hx]; [cbn [fst snd] in Hx; lia | inversion Hx]. }
  eapply SRr_bind.
  { eapply (WCL.wcc_leafb_journal B LAWS W regsL memL CM_STK (spZ regs) [] lyc Sc W memc mdc [(CM_CID, pos)] lyc S2
      mdL 0 (SP1 - spZ regs) CM_LEAF (Some (cm_bit n bs)) WR
      (fun m2 => PMC.meter_ok n bs = true ->
         bytes_at BImg.rsegs m2 (Fz + 32) (le2 (Z_to_bv 64 (PMC.meter_value n bs)))) JL).
    - rewrite SPL. lia.
    - destruct (proj1 (Z.mod_divide _ 32 ltac:(lia)) Hsp1al) as [q Hq].
      destruct (proj1 (Z.mod_divide (spZ regs) 16 ltac:(lia)) Hal) as [q2 Hq2].
      apply Z.mod_divide; [lia|]. exists (2 * q - q2). lia.
    - lia.
    - unfold CM_STK, CM_FRAME, CM_ALIGN. lia.
    - change (YK11.getr regsL 1) with (GR regsL 1). rewrite GL1. apply YK0s.ret_ok_even. vm_compute. reflexivity.
    - exact (eq_trans K3 Hgp).
    - exact (eq_trans K4 Htp).
    - intros a Ha. right; right; right. exists CM_CID, pos. split; [left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. fold Fz. change (fs_frame_bytes CM_CID) with 64.
      pose proof (HWRr a Ha). lia.
    - intros HPRE.
      pose proof (LEAF fx) as LF.
      unfold wire_leaf_wr_at, LMC.wire_rp_meter_counter_cg in LF.
      specialize (LF lyc S2 W regsL memL mdL bs (SP1 - 16) HPRE). cbv zeta in LF.
      rewrite EA1, EA2, ESP in LF. unfold rp_meter_counter_c.RP_METER_COUNTER_FRAME in LF.
      apply LF; clear LF.
      + intros H14. destruct (Hf14 H14) as (-> & _ & _ & _ & _ & _ & Hf4 & _). lia.
      + intros _. split; [lia|]. destruct (proj1 (Z.mod_divide Fz 32 ltac:(lia)) HFal) as [q Hq]. rewrite Hq.
        replace (q * 32 + 32) with ((q * 16 + 16) * 2) by lia. apply Z_mod_mult.
      + intros H14. destruct (Hf14 H14) as (-> & bA & nA & HbA & HbA1 & HbA2 & Hf4 & Hfc).
        split; [lia|].
        apply (WCL.wcc_leafb_bytes_garr8 W memL f bs); [| lia | lia].
        apply cm_garr8_of_aview. intros j Hj. rewrite length_map in Hj. split.
        * rewrite (cm_f_aview _ _ _ _ _ JL ltac:(lia) ltac:(intros b nb Hb; rewrite Eab2; exact Hb) (Z.of_nat j)
                     ltac:(lia)).
          rewrite cm_nth_map_u. unfold cm_byte. rewrite Nat2Z.id. reflexivity.
        * rewrite cm_nth_map_u. pose proof (bv_unsigned_in_range 8 (nth j bs (Z_to_bv 8 0))) as R.
          unfold bv_modulus in R. cbn in R. lia.
      + intros H1000. lia.
      + intros _. apply (WCL.wcc_leafb_wr_at W memL (Fz + 32) 2); [lia | lia |]. intros i Hi. apply Pfr. lia.
      + exact (WCL.wcc_leafb_stk_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SP1 - 16) SP1 JL
                 ltac:(unfold CM_STK, CM_FRAME, CM_ALIGN, ESTACK; lia) ltac:(lia)).
      + lia.
      + intros H14. destruct (Hf14 H14) as (-> & _ & _ & _ & _ & _ & Hf4 & Hfc). unfold AKA.off_stk. rewrite ESP. left. lia.
      + intros H1000. destruct (Hf14 ltac:(lia)) as (-> & _ & _ & _ & _ & _ & Hf4 & Hfc).
        unfold AKA.off_stk. rewrite ESP. left. lia.
      + intros _. unfold AKA.off_stk. rewrite ESP. left. lia.
      + apply (@WCL.wcc_leafb_app_stack rc). lia.
      + apply (@WCL.wcc_leafb_app_stack rc). lia.
      + exact (WCL.wcc_leafb_asan_cells B HCELLS lyc S2 W memL mdL HARL).
      + unfold AKA.off_stk. rewrite ESP. left. unfold BC.GOT_CELL_K. lia.
      + unfold AKA.off_stk. rewrite ESP. left. unfold BC.CELL_K. lia.
      + intros H14. destruct (Hf14 H14) as (-> & bA & nA & HbA & HbA1 & HbA2 & Hf4 & Hfc).
        exact (WCL.wcc_leafb_addressable_block B LAWS _ _ _ _ _ bA nA (f + 12) 2 HARL HbA ltac:(lia) ltac:(lia) ltac:(lia)).
      + intros H1000. destruct (Hf14 ltac:(lia)) as (-> & bA & nA & HbA & HbA1 & HbA2 & Hf4 & Hfc).
        exact (WCL.wcc_leafb_addressable_block B LAWS _ _ _ _ _ bA nA (f + 12) 8 HARL HbA ltac:(lia) ltac:(lia) ltac:(lia)).
      + intros _. unfold BC.addressable. split; [lia|]. split; [lia|].
        split; [unfold BC.APPMEM_END; lia|]. intros i Hi. split.
        * replace (Fz + 32 + i) with (Fz + (32 + i)) by lia.
          exact (WCL.wcc_leafb_app_of_in_app Fz 64 (32 + i) HFapp ltac:(lia)).
        * exists (Z_to_bv 8 2). split.
          -- rewrite (ESH32 i Hi). exact (cm_mrd_of_bytes1 _ _ _ Hsh4).
          -- unfold BC.shadow_ok. right. change (bv_signed (Z_to_bv 8 2)) with 2.
             rewrite Zplus_mod, Zplus_mod with (a := Fz), HF8. cbn. rewrite (Z.mod_small i 8) by lia. lia.
      + exact (WCL.wcc_leafb_rng_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SP1 - 16) 16 JL
                 ltac:(unfold CM_STK, CM_FRAME, CM_ALIGN, ESTACK; lia) ltac:(lia)).
      + exact (proj1 (WCL.wcc_leafb_rng_cells W)).
      + exact (proj2 (WCL.wcc_leafb_rng_cells W)).
      + intros H14. destruct (Hf14 H14) as (-> & bA & nA & HbA & HbA1 & HbA2 & Hf4 & Hfc).
        exact (WCL.wcc_leafb_rng_block B LAWS _ _ _ _ _ bA nA (f + 12) 2 HARL HbA ltac:(lia) ltac:(lia)).
      + intros H14. destruct (Hf14 H14) as (-> & bA & nA & HbA & HbA1 & HbA2 & Hf4 & Hfc).
        exact (WCL.wcc_leafb_rng_shadow_block B LAWS _ _ _ _ _ bA nA (f + 12) 2 HARL HbA ltac:(lia) ltac:(lia) ltac:(lia)).
      + intros H1000. destruct (Hf14 ltac:(lia)) as (-> & bA & nA & HbA & HbA1 & HbA2 & Hf4 & Hfc).
        exact (WCL.wcc_leafb_rng_block B LAWS _ _ _ _ _ bA nA (f + 12) 8 HARL HbA ltac:(lia) ltac:(lia)).
      + intros H1000. destruct (Hf14 ltac:(lia)) as (-> & bA & nA & HbA & HbA1 & HbA2 & Hf4 & Hfc).
        exact (WCL.wcc_leafb_rng_shadow_block B LAWS _ _ _ _ _ bA nA (f + 12) 8 HARL HbA ltac:(lia) ltac:(lia) ltac:(lia)).
      + intros _. apply (cm_rng_present W memL); [lia | lia | intros b Hb; apply Pfr; lia].
      + intros _.
        replace (BC.shadow_addr (Fz + 32)) with (BC.shadow_addr Fz + 4)
          by (rewrite <- (ESH32 0 ltac:(lia)); f_equal; lia).
        replace (BC.shadow_addr (Fz + 32 + 2 - 1)) with (BC.shadow_addr Fz + 4)
          by (rewrite <- (ESH32 1 ltac:(lia)); f_equal; lia).
        replace (BC.shadow_addr Fz + 4 - (BC.shadow_addr Fz + 4) + 1) with 1 by lia.
        apply (cm_rng_present W memL); [lia | lia | intros b Hb; apply Psh; lia].
      + intros x Hx. pose proof (HWRr x Hx) as Hxr. split.
        * exact (proj2 (HFb x ltac:(lia))).
        * assert (Hcl : frame_addr lyc CM_CID pos <= x < frame_addr lyc CM_CID pos + fs_frame_bytes CM_CID)
            by (change (fs_frame_bytes CM_CID) with 64; fold Fz; lia).
          exact (proj2 (al_client_img _ _ LAWS _ _ _ _ _ x HARL
            (or_intror (or_introl (ex_intro _ CM_CID (ex_intro _ pos (conj Hin2 Hcl))))))). }
  cbv beta. intros W2 c2 _ (-> & regs3 & mem3 & md3 & -> & J3 & HP3 & HRES & HKEEP & HPRES & HX).
  change (YK11.getr regsL 1) with (GR regsL 1). rewrite GL1.
  change (mkCfg (YK11.mkst regs3 (Z_to_bv 64 CM_RET_LEAF) mem3 (YK11.seg_rom segs)) md3)
    with (@cfg_at fx segs CM_RET_LEAF regs3 mem3 md3).
  assert (KEPT : forall a, 0 <= a < 2 ^ 64 -> ~ (SP1 - ESTACK <= a < SP1) -> ~ (Fz + 32 <= a < Fz + 34) ->
    aview segs (w_H W) mem3 a = aview segs (w_H W) memL a).
  { intros a Ha H1 H2. apply HKEEP; [exact Ha | rewrite SPL; exact H1 | intros Hw; exact (H2 (HWRr a Hw))]. }
  apply (cm_at_retleaf pos S2 regs3 mem3 md3 J3 Hfr2 Eab2 Hset2 (cm_kept_pres _ _ HK HP3)).
  - exact (HRES _ eq_refl).
  - kp_by HP3 18 GL18.
  - kp_by HP3 19 GL19.
  - kp_by HP3 21 GL21.
  - kp_by HP3 22 GL22.
  - kp_by HP3 23 GL23.
  - kp_by HP3 25 GL25.
  - kp_by HP3 26 GL26.
  - unfold cm_ctr. destruct (PMC.meter_ok n bs) eqn:Eok; [exact (HX eq_refl)|].
    apply (cm_bytes_kept W memL mem3 _ _ Hctr0). intros i Hi.
    change (length (le2 (Z_to_bv 64 0xa5c3))) with 2%nat in Hi.
    split; [exact (proj1 (Pfr (Fz + 32 + i) ltac:(lia)))|].
    (* not counting: the leaf writes nothing, so ctr's bytes are kept *)
    apply HKEEP; [lia | rewrite SPL; unfold ESTACK; lia |].
    unfold WR, LMC.wire_rmc_wr. rewrite Eok. intros Hw. inversion Hw.
  - etransitivity; [|exact HFLw]. apply cm_rdword_frame. intros i Hi.
    apply KEPT; [lia | unfold ESTACK; lia | lia].
  - apply (cm_saves_kept memL mem3 HSV). intros a Ha.
    split; [exact (proj1 (cm_win _ _ _ _ _ JL a ltac:(unfold CM_STK, CM_FRAME, CM_ALIGN, ESTACK; lia)))|].
    apply KEPT; [lia | unfold ESTACK; lia | lia].
Qed.

(* ---- 5: CM_PRE (after F's header and shadow) to the call of rp_meter_counter ---- *)
Lemma cm_at_pre : forall pos S2 regsP memP mdP,
  JI [(CM_CID, pos)] lyc S2 memP mdP ->
  frames S2 = (CM_CID, pos) :: frames Sc ->
  ablocks B lyc S2 = ablocks B lyc Sc ->
  (exists f0, S2 = set_fs f0 Sc) ->
  cm_kept regsP ->
  GR regsP 10 = w64 14 ->
  GR regsP 18 = w64 (frame_addr lyc CM_CID pos) -> GR regsP 19 = w64 f -> GR regsP 20 = w64 n ->
  GR regsP 22 = w64 (frame_addr lyc CM_CID pos) ->
  GR regsP 23 = w64 (BC.shadow_addr (frame_addr lyc CM_CID pos)) ->
  rdword (aview segs (w_H W) memP) (frame_addr lyc CM_CID pos + 56) = Some (flag_addr lyc CM_CID pos) ->
  cm_saves memP ->
  SRr segs W (@cfg_at fx segs CM_PRE regsP memP mdP) POST.
Proof.
  intros pos S2 regsP memP mdP JP Hfr2 Eab2 Hset2 HK GP10 GP18 GP19 GP20 GP22 GP23 HFLw HSV.
  pose proof HK as (K2 & K3 & K4 & K8 & K9 & K24 & K27).
  pose proof cm_sp_rng as [Hsp1 Hsp2]. pose proof cm_sp1_rng as [Gsp1 Hsp1al].
  unfold CM_STK, CM_FRAME, CM_ALIGN, ESTACK in Hsp1.
  pose proof asan_consts as (C1 & _).
  pose proof cm_n_rng as Hnr.
  pose proof (cm_AR _ _ _ _ _ JP) as HARP.
  assert (Hin2 : In (CM_CID, pos) (frames S2)) by (rewrite Hfr2; left; reflexivity).
  destruct (al_frames _ _ LAWS _ _ _ _ _ CM_CID pos HARP Hin2) as (HFal & HFapp & HFb & HFsh).
  destruct (frames_bounds segs B LAWS _ _ _ _ _ CM_CID pos HARP Hin2) as (HF0 & HFc & _).
  change (fs_frame_bytes CM_CID) with 64 in HFb, HFc, HFapp. change (fs_frame_bytes CM_CID / 8) with 8 in HFsh.
  set (Fz := frame_addr lyc CM_CID pos) in *.
  destruct (cm_sh_sep Fz HF0 HFc HFapp) as (SS1 & SS2 & SS3).
  assert (Psh : forall a, BC.shadow_addr Fz <= a < BC.shadow_addr Fz + 8 -> apresent (w_H W) memP a).
  { intros a Ha. replace a with (YG0f.shadow_addr Fz + (a - BC.shadow_addr Fz)) by (rewrite cm_shadow_addr_eq; lia).
    exact (proj1 (HFsh (a - BC.shadow_addr Fz) ltac:(lia))). }
  assert (Pfr : forall a, Fz <= a < Fz + 64 -> apresent (w_H W) memP a) by (intros a Ha; exact (proj1 (HFb a Ha))).
  destruct (cm_rw_carve (w_H W) memP (BC.shadow_addr Fz + 4) 1 ltac:(lia) ltac:(lia)
    ltac:(intros a Ha; apply Psh; lia)) as (kj & RK).
  destruct (cm_rw_carve (w_H W) memP (Fz + 32) 2 ltac:(lia) ltac:(lia) ltac:(intros a Ha; apply Pfr; lia)) as (cj & RC).
  assert (Hblk2 : forall b nb, In (b, nb) (ablocks B lyc Sc) -> In (b, nb) (ablocks B lyc S2))
    by (intros b nb Hb; rewrite Eab2; exact Hb).
  assert (Hf14 : 14 <= n -> exists bA nA, In (bA, nA) (ablocks B lyc S2) /\ bA <= f /\
             f + n <= bA + req_size nA /\ 4096 <= f /\ f + n <= YM05.alloc_ceiling).
  { intros H14. destruct (cm_f_block ltac:(lia)) as (bA & nA & HbA & HbA1 & HbA2 & Hf4 & Hfc).
    exists bA, nA. rewrite Eab2. auto. }
  set (Wl := [(BC.shadow_addr Fz + 4, BC.shadow_addr Fz + 5); (Fz + 32, Fz + 34)]).
  set (P := fun ms' : machine_state => exists (a3' : word) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 CM_RET_LEAF) (GR regsP 2) (GR regsP 3) (GR regsP 4) (GR regsP 5) (GR regsP 6)
               (GR regsP 7) (GR regsP 8) (GR regsP 9) (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 (Fz + 32)) a3'
               (GR regsP 14) (GR regsP 15) (GR regsP 16) (GR regsP 17) (Z_to_bv 64 Fz) (Z_to_bv 64 f)
               (Z_to_bv 64 n) (Z_to_bv 64 (Fz + 32)) (Z_to_bv 64 Fz) (Z_to_bv 64 (BC.shadow_addr Fz))
               (Z_to_bv 64 BC.ASAN_K) (Z_to_bv 64 (Z.of_nat (PMC.meter_eo n bs))) (Z_to_bv 64 (cm_bit n bs))
               (GR regsP 27) (GR regsP 28) (GR regsP 29) (GR regsP 30) (GR regsP 31))
             (@fp_regs fx) (Z_to_bv 64 CM_LEAF) (@fp_csr fx) None m' (YK11.seg_rom tfibsegs) /\
    munch Wl memP m' /\ bytes_at BImg.rsegs m' (BC.shadow_addr Fz + 4) [Z_to_bv 8 2] /\
    bytes_at BImg.rsegs m' (Fz + 32) (le2 (Z_to_bv 64 0xa5c3))).
  eapply (@cm_run fx W regsP memP mdP CM_PRE P).
  { unfold LCK.ms_of_regs. rewrite GP10, GP18, GP19, GP20, GP22, GP23, K24.
    eapply PRE with (f := f) (n := n) (bs := bs).
    - lia.
    - exact Hlen.
    - intros H14. destruct (Hf14 H14) as (bA & nA & _ & _ & _ & Hf4 & Hfc). lia.
    - intros H14 i Hi. apply (cm_f_mrd _ _ _ _ _ JP ltac:(lia) Hblk2). lia.
    - intros H1000 i Hi. apply (cm_f_mrd _ _ _ _ _ JP ltac:(lia) Hblk2). lia.
    - intros H14. destruct (Hf14 H14) as (bA & nA & HbA & HbA1 & HbA2 & Hf4 & Hfc).
      exact (WCL.wcc_leafb_addressable_block B LAWS _ _ _ _ _ bA nA (f + 12) 2 HARP HbA ltac:(lia) ltac:(lia) ltac:(lia)).
    - intros H1000. destruct (Hf14 ltac:(lia)) as (bA & nA & HbA & HbA1 & HbA2 & Hf4 & Hfc).
      exact (WCL.wcc_leafb_addressable_block B LAWS _ _ _ _ _ bA nA (f + 12) 8 HARP HbA ltac:(lia) ltac:(lia) ltac:(lia)).
    - intros H14. destruct (Hf14 H14) as (bA & nA & HbA & HbA1 & HbA2 & Hf4 & Hfc).
      exact (WCL.wcc_leafb_rng_block B LAWS _ _ _ _ _ bA nA (f + 12) 2 HARP HbA ltac:(lia) ltac:(lia)).
    - intros H14. destruct (Hf14 H14) as (bA & nA & HbA & HbA1 & HbA2 & Hf4 & Hfc).
      pose proof (WCL.wcc_leafb_rng_shadow_block B LAWS _ _ _ _ _ bA nA (f + 12) 2 HARP HbA ltac:(lia) ltac:(lia)
        ltac:(lia)) as R. replace (f + 12 + 2 - 1) with (f + 13) in R by lia. exact R.
    - intros H1000. destruct (Hf14 ltac:(lia)) as (bA & nA & HbA & HbA1 & HbA2 & Hf4 & Hfc).
      exact (WCL.wcc_leafb_rng_block B LAWS _ _ _ _ _ bA nA (f + 12) 8 HARP HbA ltac:(lia) ltac:(lia)).
    - intros H1000. destruct (Hf14 ltac:(lia)) as (bA & nA & HbA & HbA1 & HbA2 & Hf4 & Hfc).
      pose proof (WCL.wcc_leafb_rng_shadow_block B LAWS _ _ _ _ _ bA nA (f + 12) 8 HARP HbA ltac:(lia) ltac:(lia)
        ltac:(lia)) as R. replace (f + 12 + 8 - 1) with (f + 19) in R by lia. exact R.
    - intros a0' a1' a2' a3'.
      eapply ExecF.evtF_mono.
      + eapply SEG2C with (Fa := Fz).
        * exact HF0.
        * lia.
        * exact SS1.
        * exact RK.
        * exact RC.
        * apply (cm_rng_present W memP); [lia | lia | intros b Hb; apply Psh; lia].
        * apply (cm_rng_present W memP); [lia | lia | intros b Hb; apply Pfr; lia].
      + intros ms' (m' & -> & MU & WM & B1 & B2). exists a3', m'. split; [reflexivity|].
        split; [exact MU|]. split; [exact B1 | exact B2]. }
  intros ms' md' (ms0 & (a3' & m' & -> & MU & B1 & B2) & EQV & MG) SBM.
  destruct (cm_regs_of EQV) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 &
    E16 & E17 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & E28 & E29 & E30 & E31).
  rewrite (cm_ms_shape _ _ _ _ EQV).
  assert (Hvis : forall x : word, ~ outside Wl (bv_unsigned x) -> w_H W x = false).
  { intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x).
    destruct (Z_lt_le_dec (bv_unsigned x) Fz) as [L3|L3];
    [|destruct (Z_lt_le_dec (bv_unsigned x) (Fz + 64)) as [L4|L4];
      [exact (proj1 (Pfr (bv_unsigned x) ltac:(lia)))|]];
    (destruct (Z_lt_le_dec (bv_unsigned x) (BC.shadow_addr Fz)) as [L1|L1];
     [|destruct (Z_lt_le_dec (bv_unsigned x) (BC.shadow_addr Fz + 8)) as [L2|L2];
       [exact (proj1 (Psh _ (conj L1 L2)))|]]);
    exfalso; apply Hx; unfold Wl; cbn [outside]; repeat split; lia. }
  assert (HW : forall a, 0 <= a < 2 ^ 64 -> ~ outside Wl a ->
    awr_byte CM_STK (spZ regs) [] (ablocks B lyc Sc) (ablocks B lyc S2) lyc [(CM_CID, pos)] a).
  { intros a Ha Hx. right; right; right.
    exists CM_CID, pos. split; [left; reflexivity|].
    destruct (Z_lt_le_dec a Fz) as [L3|L3];
    [|destruct (Z_lt_le_dec a (Fz + 64)) as [L4|L4]; [left; unfold in_zr; cbn [fst snd]; fold Fz;
       change (fs_frame_bytes CM_CID) with 64; lia|]];
    (destruct (Z_lt_le_dec a (BC.shadow_addr Fz)) as [L1|L1];
     [|destruct (Z_lt_le_dec a (BC.shadow_addr Fz + 8)) as [L2|L2];
       [right; unfold in_zr; cbn [fst snd]; fold Fz; change (fs_frame_bytes CM_CID / 8) with 8;
        rewrite (cm_shadow_addr_eq Fz) in L1, L2; lia|]]);
    exfalso; apply Hx; unfold Wl; cbn [outside]; repeat split; lia. }
  pose proof (cm_aj_munch B LAWS CM_STK (spZ regs) [] lyc Sc W memc mdc [(CM_CID, pos)] lyc S2 W memP mdP 0 m' md'
    Wl JP MU MG SBM HW Hvis) as JL.
  apply (cm_leaf_call pos S2 (ms_regs ms') m' md' JL Hfr2 Eab2 Hset2).
  - unfold cm_kept. split; [etransitivity; [exact E2 | exact K2]|]. split; [etransitivity; [exact E3 | exact K3]|].
    split; [etransitivity; [exact E4 | exact K4]|]. split; [etransitivity; [exact E8 | exact K8]|].
    split; [etransitivity; [exact E9 | exact K9]|]. split; [exact E24|]. etransitivity; [exact E27 | exact K27].
  - exact E1.
  - exact E10.
  - exact E11.
  - exact E12.
  - exact E18.
  - exact E19.
  - exact E21.
  - exact E22.
  - exact E23.
  - exact E25.
  - exact E26.
  - exact B1.
  - exact B2.
  - etransitivity; [|exact HFLw]. apply cm_rdword_frame. intros i Hi.
    apply (cm_aview_munch _ memP m' Wl); [exact MU | lia | unfold Wl; cbn [outside]; repeat split; lia].
  - apply (cm_saves_kept memP m' HSV). intros a Ha.
    split; [exact (proj1 (cm_win _ _ _ _ _ JP a ltac:(unfold CM_STK, CM_FRAME, CM_ALIGN, ESTACK; lia)))|].
    apply (cm_aview_munch _ memP m' Wl); [exact MU | lia | unfold Wl; cbn [outside]; repeat split; lia].
Qed.

(* ---- 4: CM_RET_SM (the stack malloc returned F in a0) to CM_PRE ---- *)
Lemma cm_at_retsm : forall pos S2 regs2 mem2 md2,
  JI [(CM_CID, pos)] lyc S2 mem2 md2 ->
  frames S2 = (CM_CID, pos) :: frames Sc ->
  ablocks B lyc S2 = ablocks B lyc Sc ->
  (exists f0, S2 = set_fs f0 Sc) ->
  cm_kept regs2 ->
  GR regs2 10 = w64 (frame_addr lyc CM_CID pos) ->
  GR regs2 19 = w64 f -> GR regs2 20 = w64 n ->
  rdword (aview segs (w_H W) mem2) (frame_addr lyc CM_CID pos + 56) = Some (flag_addr lyc CM_CID pos) ->
  cm_saves mem2 ->
  SRr segs W (@cfg_at fx segs CM_RET_SM regs2 mem2 md2) POST.
Proof.
  intros pos S2 regs2 mem2 md2 J2 Hfr2 Eab2 Hset2 HK G10 G19 G20 HFLw HSV.
  pose proof HK as (K2 & K3 & K4 & K8 & K9 & K24 & K27).
  pose proof cm_sp_rng as [Hsp1 Hsp2]. pose proof cm_sp1_rng as [Gsp1 Hsp1al].
  unfold CM_STK, CM_FRAME, CM_ALIGN, ESTACK in Hsp1.
  pose proof asan_consts as (C1 & _).
  pose proof (cm_AR _ _ _ _ _ J2) as HAR2.
  assert (Hin2 : In (CM_CID, pos) (frames S2)) by (rewrite Hfr2; left; reflexivity).
  destruct (al_frames _ _ LAWS _ _ _ _ _ CM_CID pos HAR2 Hin2) as (HFal & HFapp & HFb & HFsh).
  destruct (frames_bounds segs B LAWS _ _ _ _ _ CM_CID pos HAR2 Hin2) as (HF0 & HFc & _).
  change (fs_frame_bytes CM_CID) with 64 in HFb, HFc, HFapp. change (fs_frame_bytes CM_CID / 8) with 8 in HFsh.
  set (Fz := frame_addr lyc CM_CID pos) in *.
  destruct (cm_sh_sep Fz HF0 HFc HFapp) as (SS1 & SS2 & SS3).
  assert (Psh : forall a, BC.shadow_addr Fz <= a < BC.shadow_addr Fz + 8 -> apresent (w_H W) mem2 a).
  { intros a Ha. replace a with (YG0f.shadow_addr Fz + (a - BC.shadow_addr Fz)) by (rewrite cm_shadow_addr_eq; lia).
    exact (proj1 (HFsh (a - BC.shadow_addr Fz) ltac:(lia))). }
  assert (Pfr : forall a, Fz <= a < Fz + 64 -> apresent (w_H W) mem2 a) by (intros a Ha; exact (proj1 (HFb a Ha))).
  assert (Pwin : forall a, spZ regs - CM_STK <= a < spZ regs -> apresent (w_H W) mem2 a)
    by exact (cm_win _ _ _ _ _ J2).
  assert (ES1 : bv_unsigned (GR regs2 9) = SP1) by (rewrite K9; unfold w64; apply cm_u64; lia).
  destruct (cm_rw_carve (w_H W) mem2 Fz 24 ltac:(lia) ltac:(lia) ltac:(intros a Ha; apply Pfr; lia)) as (hj & RH).
  destruct (cm_rw_carve (w_H W) mem2 (BC.shadow_addr Fz) 8 ltac:(lia) ltac:(lia) Psh) as (sj & RS).
  destruct (cm_rw_carve (w_H W) mem2 (SP1 + 24) 8 ltac:(lia) ltac:(lia)
    ltac:(intros a Ha; apply Pwin; unfold CM_STK, CM_FRAME, CM_ALIGN, ESTACK; lia)) as (xj & RX).
  set (Wl := [(Fz, Fz + 24); (BC.shadow_addr Fz, BC.shadow_addr Fz + 8); (SP1 + 24, SP1 + 32)]).
  set (P := fun ms' : machine_state => exists m' : word -> option byte,
    ms' = MS (mkR (GR regs2 1) (GR regs2 2) (GR regs2 3) (GR regs2 4) (GR regs2 5) (GR regs2 6) (GR regs2 7)
               (GR regs2 8) (GR regs2 9) (Z_to_bv 64 14) (Z_to_bv 64 0x18cc3) (Z_to_bv 64 0x8016c)
               (Z_to_bv 64 (-13)) (GR regs2 14) (GR regs2 15) (GR regs2 16) (GR regs2 17) (Z_to_bv 64 Fz)
               (Z_to_bv 64 f) (Z_to_bv 64 n) (GR regs2 21) (Z_to_bv 64 Fz) (Z_to_bv 64 (BC.shadow_addr Fz))
               (Z_to_bv 64 BC.ASAN_K) (GR regs2 25) (GR regs2 26) (GR regs2 27) (GR regs2 28) (GR regs2 29)
               (GR regs2 30) (GR regs2 31))
             (@fp_regs fx) (Z_to_bv 64 CM_PRE) (@fp_csr fx) None m' (YK11.seg_rom tfibsegs) /\
    munch [(Fz, Fz + 24); (BC.shadow_addr Fz, BC.shadow_addr Fz + 8);
           (bv_unsigned (GR regs2 9) + 24, bv_unsigned (GR regs2 9) + 32)] mem2 m').
  eapply (@cm_run fx W regs2 mem2 md2 CM_RET_SM P).
  { unfold LCK.ms_of_regs. rewrite G10, G19, G20, K24.
    eapply ExecF.evtF_mono.
    - eapply SEG2A with (Fa := Fz).
      + exact HF0.
      + rewrite ES1. lia.
      + rewrite ES1. lia.
      + exact SS1.
      + rewrite ES1. lia.
      + exact RH.
      + exact RS.
      + rewrite ES1. exact RX.
      + apply (cm_rng_present W mem2); [lia | lia | intros b Hb; apply Pfr; lia].
      + apply (cm_rng_present W mem2); [lia | lia | exact Psh].
      + rewrite ES1. apply (cm_rng_present W mem2); [lia | lia |].
        intros b Hb. apply Pwin. unfold CM_STK, CM_FRAME, CM_ALIGN, ESTACK. lia.
    - intros ms' (m' & -> & MU & WM). exists m'. split; [reflexivity | exact MU]. }
  intros ms' md' (ms0 & (m' & -> & MU) & EQV & MG) SBM.
  destruct (cm_regs_of EQV) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 &
    E16 & E17 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & E28 & E29 & E30 & E31).
  rewrite (cm_ms_shape _ _ _ _ EQV).
  change (mkCfg (YK11.mkst (ms_regs ms') (Z_to_bv 64 CM_PRE) m' (YK11.seg_rom segs)) md')
    with (@cfg_at fx segs CM_PRE (ms_regs ms') m' md').
  assert (Hvis : forall x : word, ~ outside Wl (bv_unsigned x) -> w_H W x = false).
  { intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x).
    destruct (Z_lt_le_dec (bv_unsigned x) Fz) as [L3|L3];
    [|destruct (Z_lt_le_dec (bv_unsigned x) (Fz + 64)) as [L4|L4];
      [exact (proj1 (Pfr (bv_unsigned x) ltac:(lia)))|]];
    (destruct (Z_lt_le_dec (bv_unsigned x) (BC.shadow_addr Fz)) as [L1|L1];
     [|destruct (Z_lt_le_dec (bv_unsigned x) (BC.shadow_addr Fz + 8)) as [L2|L2];
       [exact (proj1 (Psh _ (conj L1 L2)))|]]);
    (destruct (Z_lt_le_dec (bv_unsigned x) (SP1 + 24)) as [L5|L5];
     [|destruct (Z_lt_le_dec (bv_unsigned x) (SP1 + 32)) as [L6|L6];
       [exact (proj1 (Pwin (bv_unsigned x) ltac:(unfold CM_STK, CM_FRAME, CM_ALIGN, ESTACK; lia)))|]]);
    exfalso; apply Hx; unfold Wl; cbn [outside]; repeat split; lia. }
  assert (HW : forall a, 0 <= a < 2 ^ 64 -> ~ outside Wl a ->
    awr_byte CM_STK (spZ regs) [] (ablocks B lyc Sc) (ablocks B lyc S2) lyc [(CM_CID, pos)] a).
  { intros a Ha Hx.
    destruct (Z_lt_le_dec a (SP1 + 24)) as [L5|L5];
    [|destruct (Z_lt_le_dec a (SP1 + 32)) as [L6|L6];
      [left; unfold CM_STK, CM_FRAME, CM_ALIGN, ESTACK; lia|]];
    (right; right; right; exists CM_CID, pos; split; [left; reflexivity|]);
    (destruct (Z_lt_le_dec a Fz) as [L3|L3];
     [|destruct (Z_lt_le_dec a (Fz + 64)) as [L4|L4]; [left; unfold in_zr; cbn [fst snd]; fold Fz;
        change (fs_frame_bytes CM_CID) with 64; lia|]]);
    (destruct (Z_lt_le_dec a (BC.shadow_addr Fz)) as [L1|L1];
     [|destruct (Z_lt_le_dec a (BC.shadow_addr Fz + 8)) as [L2|L2];
       [right; unfold in_zr; cbn [fst snd]; fold Fz; change (fs_frame_bytes CM_CID / 8) with 8;
        rewrite (cm_shadow_addr_eq Fz) in L1, L2; lia|]]);
    exfalso; apply Hx; unfold Wl; cbn [outside]; repeat split; lia. }
  assert (MU' : munch Wl mem2 m') by (unfold Wl; rewrite <- ES1; exact MU).
  pose proof (cm_aj_munch B LAWS CM_STK (spZ regs) [] lyc Sc W memc mdc [(CM_CID, pos)] lyc S2 W mem2 md2 0 m' md'
    Wl J2 MU' MG SBM HW Hvis) as JP.
  apply (cm_at_pre pos S2 (ms_regs ms') m' md' JP Hfr2 Eab2 Hset2).
  - unfold cm_kept. split; [etransitivity; [exact E2 | exact K2]|]. split; [etransitivity; [exact E3 | exact K3]|].
    split; [etransitivity; [exact E4 | exact K4]|]. split; [etransitivity; [exact E8 | exact K8]|].
    split; [etransitivity; [exact E9 | exact K9]|]. split; [exact E24|]. etransitivity; [exact E27 | exact K27].
  - exact E10.
  - exact E18.
  - exact E19.
  - exact E20.
  - exact E22.
  - exact E23.
  - etransitivity; [|exact HFLw]. apply cm_rdword_frame. intros i Hi.
    apply (cm_aview_munch _ mem2 m' Wl); [exact MU' | lia | unfold Wl; cbn [outside]; repeat split; lia].
  - apply (cm_saves_kept mem2 m' HSV). intros a Ha.
    split; [exact (proj1 (Pwin a ltac:(unfold CM_STK, CM_FRAME, CM_ALIGN, ESTACK; lia)))|].
    apply (cm_aview_munch _ mem2 m' Wl); [exact MU' | lia | unfold Wl; cbn [outside]; repeat split; lia].
Qed.

(* ---- 1 to 3: the entry, cm_seg1_stmt, the class-0 stack malloc ---- *)
Lemma cm_entry : SRr segs W (@cfg_at fx segs CM_ENTRY regs memc mdc) POST.
Proof.
  pose proof cm_JI0 as J0.
  pose proof cm_sp_rng as [Hsp1 Hsp2]. pose proof cm_sp1_rng as [Gsp1 Hsp1al].
  unfold CM_STK, CM_FRAME, CM_ALIGN, ESTACK in Hsp1.
  pose proof asan_consts as (C1 & _).
  pose proof (cm_win _ _ _ _ _ J0) as Pwin.
  destruct (WCL.wcc_leafb_asan_cells B HCELLS lyc Sc W memc mdc cm_HARc) as (CK & GCK & _ & _ & _ & CU & GCU & _).
  assert (ESP0 : bv_unsigned (GR regs 2) = spZ regs) by reflexivity.
  eapply (@cm_run fx W regs memc mdc CM_ENTRY).
  { unfold LCK.ms_of_regs.
    eapply SEG1 with (lo := spZ regs - CM_STK).
    - rewrite ESP0. apply (cm_stk_present (w_H W) memc);
        [unfold CM_STK, CM_FRAME, CM_ALIGN, ESTACK; lia | lia | exact Pwin].
    - rewrite ESP0. unfold CM_STK, CM_FRAME, CM_ALIGN, ESTACK. lia.
    - rewrite ESP0. exact Hal.
    - exact GCK.
    - exact CK.
    - exact GCU.
    - exact CU.
    - rewrite ESP0. unfold BC.UAR. lia.
    - rewrite ESP0. apply (cm_rng_present W memc); [lia | lia |].
      intros b Hb. apply Pwin. unfold CM_STK, CM_FRAME, CM_ALIGN, ESTACK. lia.
    - exact (proj1 (WCL.wcc_leafb_rng_cells W)).
    - exact (proj2 (WCL.wcc_leafb_rng_cells W)).
    - apply cm_rng_cell; [unfold wire_asan_cell_ranges; cbn [In]; repeat (first [left; reflexivity | right]) |
        unfold BC.GOT_UAR; lia].
    - apply cm_rng_cell; [unfold wire_asan_cell_ranges; cbn [In]; repeat (first [left; reflexivity | right]) |
        unfold BC.UAR; lia]. }
  cbv beta. intros ms' md' (ms0 & (m1 & v & -> & MU & WM & RSL & RSV) & EQV & MG) SBM.
  destruct (cm_regs_of EQV) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 &
    E16 & E17 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & E28 & E29 & E30 & E31).
  rewrite (cm_ms_shape _ _ _ _ EQV).
  set (Wl := [(spZ regs - 128, spZ regs)]).
  assert (MU' : munch Wl memc m1) by exact MU.
  assert (Hvis : forall x : word, ~ outside Wl (bv_unsigned x) -> w_H W x = false).
  { intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x). unfold Wl in Hx. cbn [outside] in Hx.
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs - 128)) as [L1|L1];
      [exfalso; apply Hx; split; [lia | exact I]|].
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [L2|L2];
      [|exfalso; apply Hx; split; [lia | exact I]].
    exact (proj1 (Pwin (bv_unsigned x) ltac:(unfold CM_STK, CM_FRAME, CM_ALIGN, ESTACK; lia))). }
  assert (HW : forall a, 0 <= a < 2 ^ 64 -> ~ outside Wl a ->
    awr_byte CM_STK (spZ regs) [] (ablocks B lyc Sc) (ablocks B lyc Sc) lyc [] a).
  { intros a Ha Hx. left. unfold Wl in Hx. cbn [outside] in Hx.
    destruct (Z_lt_le_dec a (spZ regs - 128)) as [L1|L1]; [exfalso; apply Hx; split; [lia | exact I]|].
    destruct (Z_lt_le_dec a (spZ regs)) as [L2|L2]; [unfold CM_STK, CM_FRAME, CM_ALIGN, ESTACK; lia|].
    exfalso; apply Hx; split; [lia | exact I]. }
  pose proof (cm_aj_munch B LAWS CM_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W memc mdc 0 m1 md'
    Wl J0 MU' MG SBM HW Hvis) as J1.
  assert (HSV1 : cm_saves m1) by exact (proj1 RSV).
  assert (HK1 : cm_kept (ms_regs ms')).
  { unfold cm_kept. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E8|].
    split; [exact E9|]. split; [exact E24 | exact E27]. }
  change (Z_to_bv 64 CM_SMALLOC) with (Z_to_bv 64 (wire_sigma WS___asan_stack_malloc_0)).
  rewrite <- HPCS.
  assert (ESPT : spZ (ms_regs ms') = spZ regs + (SP1 - spZ regs)).
  { change (spZ (ms_regs ms')) with (bv_unsigned (GR (ms_regs ms') 2)). rewrite E2.
    change (cm_sp1 (bv_unsigned (YK11.getr regs (Z_to_bv 5 2)))) with SP1. rewrite cm_u64 by lia. lia. }
  eapply SRr_bind.
  { exact (cm_stack_malloc_at B LAWS SMP CM_CID (ASM fx) ltac:(unfold CM_CID; lia) W (ms_regs ms') m1 CM_STK
      (spZ regs) [] lyc Sc W memc mdc [] lyc Sc md' 0 (SP1 - spZ regs) (Z_to_bv 64 CM_RET_SM) J1 ESPT
      ltac:(destruct (proj1 (Z.mod_divide _ 32 ltac:(lia)) Hsp1al) as [q Hq];
            destruct (proj1 (Z.mod_divide (spZ regs) 16 ltac:(lia)) Hal) as [q2 Hq2];
            apply Z.mod_divide; [lia|]; exists (2 * q - q2); lia)
      ltac:(lia) ltac:(unfold CM_STK, CM_FRAME, CM_ALIGN; lia)
      (eq_trans E3 Hgp) (eq_trans E4 Htp) E1
      ltac:(apply YK0s.ret_ok_even; vm_compute; reflexivity) Hcnt). }
  cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & J2 & HP2 & G10 & Eab2 & Hfr2 & Hnev2 & Hset2 &
    Hz & Hflag & Hfpres & Hkept).
  change (mkCfg (YK11.mkst regs2 (Z_to_bv 64 CM_RET_SM) mem2 (YK11.seg_rom segs)) md2)
    with (@cfg_at fx segs CM_RET_SM regs2 mem2 md2).
  apply (cm_at_retsm pos S2 regs2 mem2 md2 J2 Hfr2 Eab2 Hset2 (cm_kept_pres _ _ HK1 HP2)).
  - exact G10.
  - etransitivity; [apply (HP2 19); unfold acallee_saved; lia|]. etransitivity; [exact E19 | exact H10].
  - etransitivity; [apply (HP2 20); unfold acallee_saved; lia|]. etransitivity; [exact E20 | exact H11].
  - replace (frame_addr lyc CM_CID pos + 56) with (frame_addr lyc CM_CID pos + fs_frame_bytes CM_CID - 8)
      by (change (fs_frame_bytes CM_CID) with 64; lia).
    exact Hflag.
  - apply (cm_saves_kept m1 mem2 HSV1). intros a Ha.
    split; [exact (proj1 (Pwin a ltac:(unfold CM_STK, CM_FRAME, CM_ALIGN, ESTACK; lia)))|].
    destruct Hkept as [HKa _]. apply HKa; unfold ESTACK; lia.
Qed.

End Entry.
End Walk.

Section Holds. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.

Theorem wire_check_meter_holds : @wire_check_meter_holds_stmt fx rc B MT.
Proof.
  unfold wire_check_meter_holds_stmt.
  intros HPCS HCELLS LAWS MTL MTF SMP ASF FFL ASM LEAF.
  unfold wire_check_meter_cg.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs f n bs
    HJ Hra Hra4 Hgp Htp H10 H11 Hal Hwlo Hwhi Hlen Hblk Hgarr Hcnt Hnev.
  eapply cm_entry with (f := f) (n := n) (bs := bs);
    first [exact WireCmSeg1.cm_seg1 | exact WireCmSeg2.cm_seg2a | exact WireCmPre.cm_pre
          | exact WireCmSeg2.cm_seg2c | exact WireCmCmp.cm_cmp | exact WireCmRel.cm_rel | eassumption].
Qed.
End Holds.

Print Assumptions wire_check_meter_holds.
