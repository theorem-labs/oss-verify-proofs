(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module paths and module names changed; 1161 of its 1364 lines of code are new or changed and 321 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/B/Prog/check_meter_cgW.v, with its module paths and module names changed; 1112 of its 1298 lines of code are new or changed and 1178 lines of the source are left out. *)
(* check_read_cgW: Theorem wire_check_read_holds : wire_check_read_holds_stmt (lib/A/Prog/check_read_cg.v), the walk of
   check_read in image A (fuzz_wire.asan 0x8077c .. 0x80c38).

   The walk runs the footprint segments of lib/A/Prog/check_read_walk_kit.v and lib/A/Prog/check_read_seg3.v
   between the calls, each carried into SRr by the bridge of lib/A/Prog/LeafCgFacts.v, inside an INNER journal at
   the entry state (YCbq.v ajournal_sub_init: stack window [sp - CRD_STK, sp), no footprint):
     cr_seg0_F    +0x000 .. `jal __asan_stack_malloc_1` (+0x74): the 0x80-byte frame, the realign, the two cells;
     the class-1 fake frame F (lib/A/Prog/check_read_kit_seg.v crd_stack_malloc_at_ok, from the statement's
                  astack_malloc_realizes row): F >= 4096, so the real-stack fallback +0x8c .. +0xa4 is dead;
     cr_seg1_F    +0x78 .. `jal __asan_memset` (+0x130): the frame header, the frame's shadow;
     __asan_memset of v = F + 0x20 with 0x5a, 48 bytes (YCbq.v aj_intrin_at, the aintrin_realizes row);
     cr_seg2_F    +0x134 .. `jal rp_slot_read` (+0x1a0): the width, c[16] / c[17] behind their shadow bytes, the want;
     rp_slot_read (lib/A/Prog/rp_slot_read_cg.v through WireCg.v wire_leaf_wr_at, the journal by WireCcLeafb.v
                  wcc_leafb_journal): it writes v on the reading path only;
     crd_seg_S3   +0x1a4 .. +0x35c: the twelve samples, each equal to the one the braid puts in the slot, or still
                  UNTOUCHED_SAMPLE on a declined read, so the abort is not reached;
     cr_seg4_F    +0x35c .. `ret`: v's shadow, the retire magic, the frame's shadow 0xf5, the flag byte (the frame
                  released: check_read_kit_seg.v crd_flag_free_ok, from astack_free_law), the reloads.
   The post: the outer journal by YCbq.v ajournal_sub, acall_kept by acall_kept_of_journal, the meter by the fs laws
   (the fake frame changes st_fs only). *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n YA0o YK1b.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YI04.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI16 YI5b YI5c YP09 YO0f.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Frame Cells Step Regs6ss.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require AE2k Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import WirePSyms WirePAddr WireCg check_read_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import WireCcLeafb.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require check_read_walk_kit check_read_segs check_read_kit_segs.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require check_read_kit_seg check_read_seg3.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require LeafCgKit LeafCgFacts LeafCgGlue WirePImg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require rp_slot_read_cg rp_slot_read_F_c AsanKA AsanKAProof.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require reac_frame_clean_len_c rp_frame_channels_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_slot_read_c rp_slot_width_c check_read.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.LeafCgKit.
Module AC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.AsanCells.
Module AImg := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Img0.
Module CRK := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.check_read_walk_kit.
Module CRS := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.check_read_segs.
Module CKS := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.check_read_kit_segs.
Module KSP := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.check_read_kit_seg.
Module S3P := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.check_read_seg3.
Module LSR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_slot_read_cg.
Module ASR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_slot_read_F_c.
Module AKA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.AsanKA.
Module AKP := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.AsanKAProof.
Module ARC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.reac_frame_clean_len_c.
Module AFC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_frame_channels_c.
Module PSR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_slot_read_c.
Module PSW := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_slot_width_c.
Module PCR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.check_read.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ======================================================================== *)
(* Image-free helpers                                                         *)
(* ======================================================================== *)

Lemma crw_u64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz. Qed.

Lemma crw_byte_eq : forall (H H' : word -> bool) (m m' : word -> option byte) (a : Z),
  apresent H m a -> apresent H' m' a -> aview tfibsegs H' m' a = aview tfibsegs H m a ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros H H' m m' a [Hh [b Hb]] [Hh' [b' Hb']] E.
  unfold aview, YP09.mbyte, mrestrict in E.
  rewrite Hh, Hh' in E. rewrite Hb, Hb' in E. cbn in E.
  injection E as E. rewrite Hb, Hb'. f_equal. apply bv_eq. exact E.
Qed.

Lemma crw_rw_cells_ext : forall (m m' : word -> option byte) (A : Z) (cs : list cell),
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

Lemma crw_bytes_at_ext : forall (m m' : word -> option byte) (A : Z) (bs : list byte),
  bytes_at AImg.rsegs m A bs ->
  (forall a, A <= a < A + Z.of_nat (length bs) -> m' (wa a) = m (wa a)) ->
  bytes_at AImg.rsegs m' A bs.
Proof.
  intros m m' A bs (Ha & Hl & Hb) He. split; [exact Ha|]. split; [exact Hl|]. intros i Hi.
  unfold mrd. rewrite (He (A + Z.of_nat i)) by lia. exact (Hb i Hi).
Qed.

Lemma crw_fp_avoids : forall (W : world tfibsegs),
  LCK.fp_avoids (@w_H tfibsegs W) (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W).
Proof. intros W a n H. unfold LCK.RNG_W in H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.

(* A footprint run from the configuration at pc, carried into SRr. *)
Lemma crw_run {fx : YK11.FPState} : forall (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (pc : Z) (P : machine_state -> Prop) (Q : world tfibsegs -> config -> Prop),
  ExecF.evtF AImg.rsegs (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) P (@LCK.ms_of_regs fx pc regs mem) ->
  (forall ms' md', (exists ms0, P ms0 /\ ms_eqv ms0 ms') -> same_but_materialized md md' ->
     SRr tfibsegs W (mkCfg ms' md') Q) ->
  SRr tfibsegs W (@cfg_at fx tfibsegs pc regs mem md) Q.
Proof.
  intros W regs mem md pc P Q Hrun K. unfold cfg_at.
  pose proof (LeafCgGlue.evtF_eqv AImg.rsegs _ P _ _ Hrun (@LeafCgGlue.ms_of_regs_eqv fx pc regs mem)) as Hrun'.
  apply (LeafCgFacts.bridge_evtF_stmt_YA0n W _ md _ _ Q Hrun' (crw_fp_avoids W)).
  intros ms' md' (ms1 & HP & HE & _) Hs. apply K; [exists ms1; split; assumption | exact Hs].
Qed.

Lemma crw_ms_shape {fx : YK11.FPState} : forall (R : bvmap 5 word) (pc : word) (m : word -> option byte)
    (ms' : machine_state),
  ms_eqv (MS R (@fp_regs fx) pc (@fp_csr fx) None m (YK11.seg_rom tfibsegs)) ms' ->
  ms' = @YK11.mkst fx (ms_regs ms') pc m (YK11.seg_rom tfibsegs).
Proof.
  intros R pc m [r f p sv rv fc mm ro] (_ & Hf & Hp & Hs & Hr & Hc & Hm & Hro).
  cbn [MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
  subst. reflexivity.
Qed.

Lemma crw_ms_reg : forall (R : bvmap 5 word) F pc fc rv m ro (ms' : machine_state) (r : bv 5),
  ms_eqv (MS R F pc fc rv m ro) ms' -> YK11.getr (ms_regs ms') r = YK11.getr R r.
Proof.
  intros R F pc fc rv m ro ms' r (HR & _). cbn [MS ms_regs] in HR. exact (LeafCgGlue.getr_xeqv _ _ HR r).
Qed.

(* Every register of a state register-equivalent to an `mkR` state. *)
Lemma crw_regs_of : forall {x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
    x25 x26 x27 x28 x29 x30 x31 : word} {F : bvmap 5 word} {pc : word} {fc : bv 32} {rv : option word}
    {m ro : word -> option byte} {ms' : machine_state},
  ms_eqv (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                  x25 x26 x27 x28 x29 x30 x31) F pc fc rv m ro) ms' ->
  YK11.getr (ms_regs ms') (Z_to_bv 5 1) = x1 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 2) = x2 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 3) = x3 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 4) = x4 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 8) = x8 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 9) = x9 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 10) = x10 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 18) = x18 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 19) = x19 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 20) = x20 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 21) = x21 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 22) = x22 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 23) = x23 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 24) = x24 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 25) = x25 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 26) = x26 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 27) = x27.
Proof.
  intros until ms'. intros H.
  repeat split; (etransitivity; [apply (crw_ms_reg _ _ _ _ _ _ _ _ _ H) | reflexivity]).
Qed.

(* The argument registers a1 .. a3 of such a state. *)
Lemma crw_regs_of_a : forall {x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
    x25 x26 x27 x28 x29 x30 x31 : word} {F : bvmap 5 word} {pc : word} {fc : bv 32} {rv : option word}
    {m ro : word -> option byte} {ms' : machine_state},
  ms_eqv (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                  x25 x26 x27 x28 x29 x30 x31) F pc fc rv m ro) ms' ->
  YK11.getr (ms_regs ms') (Z_to_bv 5 11) = x11 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 12) = x12 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 13) = x13.
Proof.
  intros until ms'. intros H.
  repeat split; (etransitivity; [apply (crw_ms_reg _ _ _ _ _ _ _ _ _ H) | reflexivity]).
Qed.

Lemma crw_le_byte1 : forall v, 0 <= v < 256 -> Z.shiftr (v mod 2 ^ (8 * Z.of_nat 1)) (8 * Z.of_nat 0) mod 256 = v.
Proof.
  intros v Hv. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite Z.mod_small by lia. apply Z.mod_small. lia.
Qed.

Lemma crw_garr8_aview : forall (H : word -> bool) mem a (l : list Z) (j : nat),
  garr8 tfibsegs (mrestrict H mem) a l -> (j < length l)%nat ->
  aview tfibsegs H mem (a + Z.of_nat j) = Some (nth j l 0).
Proof.
  intros H mem a l j G Hj. destruct (G j Hj) as [V R]. specialize (V 0%nat ltac:(lia)).
  rewrite Nat2Z.inj_0, Z.add_0_r in V.
  unfold aview. rewrite V. cbn [option_map]. f_equal.
  unfold YO0f.le_byte, YG0f.le_byte. rewrite Z_to_bv_unsigned, (crw_le_byte1 _ R).
  apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

Lemma crw_garr8_of_aview : forall (H : word -> bool) mem a (l : list Z),
  (forall j, (j < length l)%nat -> aview tfibsegs H mem (a + Z.of_nat j) = Some (nth j l 0) /\ 0 <= nth j l 0 < 256) ->
  garr8 tfibsegs (mrestrict H mem) a l.
Proof.
  intros H mem a l HA j Hj. destruct (HA j Hj) as [E R]. split; [|exact R].
  intros k Hk. assert (Ek : k = 0%nat) by lia. subst k. rewrite Nat2Z.inj_0, Z.add_0_r.
  unfold aview in E.
  destruct (YP09.mbyte tfibsegs (mrestrict H mem) (a + Z.of_nat j)) as [b|] eqn:Eb; cbn in E; [|discriminate].
  injection E as E. f_equal. apply bv_eq. unfold YO0f.le_byte, YG0f.le_byte.
  rewrite Z_to_bv_unsigned, (crw_le_byte1 _ R), <- E.
  symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma crw_aview_mrd : forall (W : world tfibsegs) mem a, w_H W (Z_to_bv 64 a) = false ->
  aview tfibsegs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (mrd AImg.rsegs mem (wa a)).
Proof. intros W mem a H. unfold aview, YP09.mbyte, mrestrict, mrd, wa. rewrite H. reflexivity. Qed.

Lemma crw_aview_present : forall (W : world tfibsegs) m a, apresent (w_H W) m a -> aview tfibsegs (w_H W) m a <> None.
Proof. intros W m a [Hh [b Hb]]. unfold aview, YP09.mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.

(* The shadow bytes 4 .. 9 of the frame, zero after +0xe0 .. +0x120. *)
Lemma crw_sh_entry_zero : forall (W : world tfibsegs) m A, rw_cells AImg.rsegs m A CRK.crk_sh_entry ->
  (forall i, 4 <= i < 10 -> apresent (w_H W) m (A + i)) ->
  forall i, 4 <= i < 10 -> aview tfibsegs (w_H W) m (A + i) = Some 0.
Proof.
  intros W m A [[_ (_ & _ & Hb)] _] HP i Hi.
  rewrite (crw_aview_mrd W m _ (proj1 (HP i Hi))).
  replace i with (Z.of_nat (Z.to_nat i)) by lia.
  rewrite (Hb (Z.to_nat i)) by (unfold CRK.crk_sh_entry; cbn; lia).
  assert (Hc : (Z.to_nat i = 4 \/ Z.to_nat i = 5 \/ Z.to_nat i = 6 \/ Z.to_nat i = 7 \/ Z.to_nat i = 8 \/
                Z.to_nat i = 9)%nat) by lia.
  destruct Hc as [E|[E|[E|[E|[E|E]]]]]; rewrite E; vm_compute; reflexivity.
Qed.

(* The flag word the fake frame holds at F + 120, as raw bytes. *)
Lemma crw_rdword_bytes : forall (W : world tfibsegs) m a v, 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> w_H W (Z_to_bv 64 (a + i)) = false) ->
  rdword (aview tfibsegs (w_H W) m) a = Some v -> bytes_at AImg.rsegs m a (le8 (wa v)).
Proof.
  intros W m a v H0 H1 HH Hrd.
  assert (M : forall k, 0 <= k < 8 -> forall vk, aview tfibsegs (w_H W) m (a + k) = Some vk ->
     exists b : byte, mrd AImg.rsegs m (wa (a + k)) = Some b /\ vk = bv_unsigned b).
  { intros k Hk vk E. rewrite (crw_aview_mrd W m _ (HH k Hk)) in E.
    destruct (mrd AImg.rsegs m (wa (a + k))) as [b|]; [|discriminate E].
    injection E as E. exists b. split; [reflexivity | symmetry; exact E]. }
  unfold rdword in Hrd.
  destruct (aview tfibsegs (w_H W) m a) as [v0|] eqn:E0; [|discriminate].
  destruct (aview tfibsegs (w_H W) m (a + 1)) as [v1|] eqn:E1; [|discriminate].
  destruct (aview tfibsegs (w_H W) m (a + 2)) as [v2|] eqn:E2; [|discriminate].
  destruct (aview tfibsegs (w_H W) m (a + 3)) as [v3|] eqn:E3; [|discriminate].
  destruct (aview tfibsegs (w_H W) m (a + 4)) as [v4|] eqn:E4; [|discriminate].
  destruct (aview tfibsegs (w_H W) m (a + 5)) as [v5|] eqn:E5; [|discriminate].
  destruct (aview tfibsegs (w_H W) m (a + 6)) as [v6|] eqn:E6; [|discriminate].
  destruct (aview tfibsegs (w_H W) m (a + 7)) as [v7|] eqn:E7; [|discriminate].
  injection Hrd as Hv.
  rewrite <- (Z.add_0_r a) in E0.
  destruct (M 0 ltac:(lia) _ E0) as (b0 & B0 & -> ).
  destruct (M 1 ltac:(lia) _ E1) as (b1 & B1 & -> ).
  destruct (M 2 ltac:(lia) _ E2) as (b2 & B2 & -> ).
  destruct (M 3 ltac:(lia) _ E3) as (b3 & B3 & -> ).
  destruct (M 4 ltac:(lia) _ E4) as (b4 & B4 & -> ).
  destruct (M 5 ltac:(lia) _ E5) as (b5 & B5 & -> ).
  destruct (M 6 ltac:(lia) _ E6) as (b6 & B6 & -> ).
  destruct (M 7 ltac:(lia) _ E7) as (b7 & B7 & -> ).
  assert (EV : v = bytes_le_to_Z [b0; b1; b2; b3; b4; b5; b6; b7]).
  { rewrite !CRK.crk_ble. cbn [bytes_le_to_Z]. lia. }
  unfold wa at 1. rewrite EV, (CRK.crk_le8_of_bytes [b0; b1; b2; b3; b4; b5; b6; b7] eq_refl).
  split; [exact H0|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi.
  do 8 (destruct i as [|i]; [cbn [nth_error Z.of_nat]; first [rewrite Z.add_0_r in B0 |- *; exact B0 | assumption
     | change (Z.of_nat 1) with 1; exact B1] |]).
  lia.
Qed.



(* A range of present bytes holds some bytes the footprint may write: one CB cell over them. *)
Lemma crw_rw_cb : forall (W : world tfibsegs) mem A (n : nat),
  0 <= A -> A + Z.of_nat n <= 2 ^ 64 ->
  (forall a, A <= a < A + Z.of_nat n -> apresent (w_H W) mem a) ->
  exists junk, rw_cells AImg.rsegs mem A [CB n junk].
Proof.
  intros W mem A n H0 H1 HP.
  destruct (stk_bytes AImg.rsegs mem A (A + Z.of_nat n) (wcc_leafb_stk W mem A (A + Z.of_nat n) H0 H1 HP)
              ltac:(lia)) as (bs & L & B).
  exists bs. split; [split|].
  - cbn. split; [rewrite L; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize]. rewrite Nat.add_0_r.
    apply (wcc_leafb_wr_at W mem A (Z.of_nat n) H0 H1). intros i Hi. apply HP. lia.
Qed.

(* Raw cells over present bytes whose view a call kept are the same raw cells after it. *)
Lemma crw_rw_kept : forall (W : world tfibsegs) m m' A cs,
  rw_cells AImg.rsegs m A cs ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) ->
     apresent (w_H W) m a /\ apresent (w_H W) m' a /\ aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  rw_cells AImg.rsegs m' A cs.
Proof.
  intros W m m' A cs H K. apply (crw_rw_cells_ext m m' A cs H). intros a Ha.
  destruct (K a Ha) as (P & P' & E). exact (crw_byte_eq _ _ _ _ a P P' E).
Qed.

Lemma crw_bytes_kept : forall (W : world tfibsegs) m m' A bs,
  bytes_at AImg.rsegs m A bs ->
  (forall a, A <= a < A + Z.of_nat (length bs) ->
     apresent (w_H W) m a /\ apresent (w_H W) m' a /\ aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  bytes_at AImg.rsegs m' A bs.
Proof.
  intros W m m' A bs H K. apply (crw_bytes_at_ext m m' A bs H). intros a Ha.
  destruct (K a Ha) as (P & P' & E). exact (crw_byte_eq _ _ _ _ a P P' E).
Qed.

(* Bytes the view shows, as raw bytes. *)
Lemma crw_bytes_of_aview : forall (W : world tfibsegs) m A (bs : list byte),
  0 <= A -> A + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall i, (i < length bs)%nat ->
     aview tfibsegs (w_H W) m (A + Z.of_nat i) = option_map (fun b : byte => bv_unsigned b) (nth_error bs i)) ->
  bytes_at AImg.rsegs m A bs.
Proof.
  intros W m A bs H0 H1 HV. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  pose proof (HV i Hi) as E.
  destruct (nth_error bs i) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia]. cbn [option_map] in E.
  destruct (wcc_leafb_mrd_aview W m (A + Z.of_nat i) _ E) as (b' & Hb' & Hv).
  assert (Hb'' : mrd AImg.rsegs m (wa (A + Z.of_nat i)) = Some b') by exact Hb'.
  rewrite Hb''. f_equal. apply bv_eq. exact Hv.
Qed.

(* lib/Prog/check_read.v rw_cells_app, over image A's segments. *)
Lemma crw_rw_cells_app : forall m A cs1 cs2,
  rw_cells AImg.rsegs m A (cs1 ++ cs2) <->
  rw_cells AImg.rsegs m A cs1 /\ rw_cells AImg.rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at, wr_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] (H1 & H2 & H3)].
    rewrite (cells_bytes_length cs1 W1) in B2.
    split; (split; [split; assumption|]); (split; [lia|]); (split; [lia|]).
    + intros i Hi. apply H3. lia.
    + intros i Hi. replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
      apply H3. lia.
  - intros [[[W1 B1] (H1 & H2 & H3)] [[W2 B2] (K1 & K2 & K3)]].
    rewrite <- (cells_bytes_length cs1 W1) in B2.
    split; [split; [split; assumption | split; assumption]|].
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat (cells_size cs1))) as [L|L]; [apply H3; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
    apply K3. lia.
Qed.

Lemma crw_not_outside3 : forall a1 b1 a2 b2 a3 b3 x, ~ outside [(a1, b1); (a2, b2); (a3, b3)] x ->
  (a1 <= x < b1) \/ (a2 <= x < b2) \/ (a3 <= x < b3).
Proof.
  intros a1 b1 a2 b2 a3 b3 x H.
  destruct (Z_le_gt_dec a1 x); destruct (Z_lt_ge_dec x b1); try (left; lia).
  all: destruct (Z_le_gt_dec a2 x); destruct (Z_lt_ge_dec x b2); try (right; left; lia).
  all: destruct (Z_le_gt_dec a3 x); destruct (Z_lt_ge_dec x b3); try (right; right; lia).
  all: exfalso; apply H; cbn [outside]; repeat split; lia.
Qed.

Lemma crw_not_outside1 : forall a1 b1 x, ~ outside [(a1, b1)] x -> a1 <= x < b1.
Proof.
  intros a1 b1 x H. destruct (Z_le_gt_dec a1 x); destruct (Z_lt_ge_dec x b1); try lia.
  all: exfalso; apply H; cbn [outside]; repeat split; lia.
Qed.

Lemma crw_outside_dec : forall (L : list (Z * Z)) x, {outside L x} + {~ outside L x}.
Proof.
  induction L as [|[lo hi] L IH]; intros x; [left; exact I|].
  cbn [outside]. destruct (IH x) as [H|H].
  - destruct (Z_le_gt_dec lo x); [destruct (Z_lt_ge_dec x hi)|].
    + right. intros [H1 _]. lia.
    + left. split; [lia | exact H].
    + left. split; [lia | exact H].
  - right. intros [_ H2]. exact (H H2).
Qed.

(* What a footprint run that writes only the bytes Wr (present, outside the image) leaves for the journal: the
   visible memory changes only at Wr, grows, and the hidden bytes are kept. *)
Lemma crw_run_facts : forall (W : world tfibsegs) (m m' : word -> option byte) (L : list (Z * Z)) (Wr : Z -> Prop),
  munch L m m' -> wmono AImg.rsegs m m' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside L x -> Wr x) ->
  (forall a, Wr a -> apresent (w_H W) m a) ->
  (forall a, Wr a -> ~ in_img tfibsegs a) ->
  (forall x : word, ~ Wr (bv_unsigned x) -> mrestrict (w_H W) m' x = mrestrict (w_H W) m x) /\
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') /\
  (forall x : word, w_H W x = true -> m' x = m x).
Proof.
  intros W m m' L Wr MU WM HL HP HI.
  assert (KO : forall x : word, ~ Wr (bv_unsigned x) -> m' x = m x).
  { intros x Hx. apply MU. destruct (crw_outside_dec L (bv_unsigned x)) as [O|O]; [exact O|].
    exfalso. apply Hx. apply HL; [apply bv_unsigned_in_range | exact O]. }
  split; [|split].
  - intros x Hx. unfold mrestrict. rewrite (KO x Hx). reflexivity.
  - intros x Hx. unfold mrestrict in *. destruct (w_H W x) eqn:Eh; [exact Hx|].
    destruct (crw_outside_dec L (bv_unsigned x)) as [O|O]; [rewrite (MU x O); exact Hx|].
    assert (Hw : Wr (bv_unsigned x)) by (apply HL; [apply bv_unsigned_in_range | exact O]).
    destruct (HP _ Hw) as [_ (b & Hb)]. rewrite Z_to_bv_bv_unsigned in Hb.
    assert (Hv : wview AImg.rsegs m' x <> None) by (apply WM; unfold wview; rewrite Hb; discriminate).
    unfold wview in Hv. destruct (m' x) as [b'|] eqn:Em'; [discriminate|]. exfalso.
    rewrite (LeafCgGlue.find_segment_out AImg.rsegs (bv_unsigned x) 1) in Hv; [exact (Hv eq_refl)|lia|].
    intros sg Hin Hr. exact (HI _ Hw (ex_intro _ sg (conj Hin Hr))).
  - intros x Hh. destruct (crw_outside_dec L (bv_unsigned x)) as [O|O]; [exact (MU x O)|].
    assert (Hw : Wr (bv_unsigned x)) by (apply HL; [apply bv_unsigned_in_range | exact O]).
    destruct (HP _ Hw) as [Hv _]. rewrite Z_to_bv_bv_unsigned in Hv. congruence.
Qed.

Section Walk.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation sink := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HPCS : pc_stack_malloc (as_code B) CRD_CID = wire_sigma WS___asan_stack_malloc_1.
Hypothesis HCELLS : wire_cells B.
Hypothesis HROU : wire_ro_rd_unowned B.
Hypothesis HERR : wire_rom_no_errno B.
Hypothesis LAWS : AR_laws segs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law segs B.
Hypothesis FFL : frame_flag_lawP segs B.
Hypothesis ASM : forall fx' : YK11.FPState, @astack_malloc_realizes fx' rc segs B CRD_CID.
Hypothesis AIS : forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (wire_sigma WS___asan_memset).
Hypothesis LEAF : forall fx' : YK11.FPState, @wire_leaf_wr_at rc B (@LSR.wire_rp_slot_read_cg) fx'.
(* The three pieces proved apart. *)
Hypothesis SEG3 : CRS.crd_seg_S3_stmt.
Hypothesis SMA : CKS.crd_stack_malloc_at_stmt.
Hypothesis FREE : CKS.crd_flag_free_stmt.
Local Abbreviation ajournalA := (@ajournal rc sink segs B).
Local Abbreviation GR rg i := (YK11.getr rg (Z_to_bv 5 i)).

(* A run that writes no memory: the journal follows its same_but_materialized. *)
Lemma crw_aj_md : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k mdc',
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

(* The journal after a footprint run that writes only bytes the journal allows. *)
Lemma crw_aj_run : forall STK sp0 FP ly S W0 mem md own lyc Sc (W : world segs) m mdc k m' mdc' L (Wr : Z -> Prop),
  ajournalA STK sp0 FP ly S W0 mem md own lyc Sc W m mdc k ->
  munch L m m' -> wmono AImg.rsegs m m' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside L x -> Wr x) ->
  (forall a, Wr a -> apresent (w_H W) m a) ->
  (forall a, Wr a -> ~ in_img segs a) ->
  same_but_materialized mdc mdc' ->
  (forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  ajournalA STK sp0 FP ly S W0 mem md own lyc Sc W m' mdc' k.
Proof.
  intros STK sp0 FP ly S W0 mem md own lyc Sc W m mdc k m' mdc' L Wr HJ MU WM HL HP HI Hs HW.
  destruct (crw_run_facts W m m' L Wr MU WM HL HP HI) as (K1 & K2 & K3).
  exact (ajournal_exec segs B LAWS WirePImg.wire_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W m mdc k m' mdc' Wr
           HJ K1 K2 K3 Hs HW).
Qed.

Lemma crw_pw_app : forall {X : Type} (R : X -> X -> Prop) l1 l2 x y,
  pairwise R (l1 ++ l2) -> In x l1 -> In y l2 -> R x y.
Proof.
  intros X R l1. induction l1 as [|a l1 IH]; intros l2 x y HP Hx Hy; [destruct Hx|].
  cbn [app pairwise] in HP. destruct HP as [HF HP]. destruct Hx as [<- | Hx].
  - exact (proj1 (Forall_forall _ _) HF y (in_or_app _ _ _ (or_intror Hy))).
  - exact (IH l2 x y HP Hx Hy).
Qed.

(* A live fake frame and a live block are apart (AR_sep_law). *)
Lemma crw_frame_block : forall ly S (W : world segs) mem md cid pos p n,
  @AR rc segs B ly S W mem md -> In (cid, pos) (frames S) -> In (p, n) (ablocks B ly S) ->
  frame_addr ly cid pos + fs_frame_bytes cid <= p \/ p + req_size n <= frame_addr ly cid pos.
Proof.
  intros ly S W mem md cid pos p n HAR Hf Hb.
  destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as [HP _].
  pose proof (crw_pw_app zdisjoint _ _ (p, req_size n) (frame_addr ly cid pos, fs_frame_bytes cid) HP
    ltac:(apply in_map_iff; exists (p, n); split; [reflexivity | exact Hb])
    ltac:(apply in_map_iff; exists (cid, pos); split; [reflexivity | exact Hf])) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

(* The read-only view of the WIRE_RO_RD bytes, kept by a journal from its entry state. *)
Lemma crw_rom_view_journal : forall STK sp0 own (W : world segs) memc mdc ly2 S2 m2 md2 k lyc Sc,
  ajournalA STK sp0 [] lyc Sc W memc mdc own ly2 S2 W m2 md2 k ->
  wire_rom_view_rd W memc -> wire_rom_view_rd W m2.
Proof.
  intros STK sp0 own W memc mdc ly2 S2 m2 md2 k lyc Sc HJ HR a Ha.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K & _).
  destruct (wire_ro_rd_rom_clean a Ha) as [Hrom _].
  destruct (wire_ro_rd_scoped B HROU HERR a Ha) as [Ho He].
  rewrite (K a ltac:(destruct Hrom as (sg & Hin & _ & Hr); exists sg; split; [exact Hin | exact Hr]) Ho He
             (fp_spares_closed [] a sink_closed_nil)).
  exact (HR a Ha).
Qed.

(* Eight bytes of the read-only view, as raw bytes. *)
Lemma crw_rom8 : forall (W : world segs) mem a v, wire_rom_view_rd W mem ->
  (forall i, 0 <= i < 8 -> wire_in_ro_rd (a + i)) ->
  (forall k, (k < 8)%nat ->
     option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom segs (Z_to_bv 64 (a + Z.of_nat k))) = Some (le_byte v 8 k)) ->
  0 <= a -> a + 8 <= 2 ^ 64 -> bytes_at AImg.rsegs mem a (le8 (wa v)).
Proof.
  intros W mem a v HR HI HV H0 H1. split; [exact H0|]. split; [rewrite length_le8; exact H1|].
  intros i Hi. rewrite length_le8 in Hi.
  pose proof (HR (a + Z.of_nat i) (HI (Z.of_nat i) ltac:(lia))) as E. rewrite (HV i Hi) in E.
  destruct (wcc_leafb_mrd_aview W mem (a + Z.of_nat i) _ E) as (b & Hb & Hbv).
  assert (Hb' : mrd AImg.rsegs mem (wa (a + Z.of_nat i)) = Some b) by exact Hb.
  rewrite Hb'. symmetry. apply (wcc_leafb_opt_byte_eq _ _ (le_byte v 8 i)); [exact (wcc_leafb_le8_byte v i Hi) |].
  cbn [option_map]. rewrite Hbv. reflexivity.
Qed.

Section Entry.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (pin len slot : Z)
  (bs : list byte).
Hypothesis HJ : ajournalA STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis Hra : YK0s.ret_ok (YK11.getr regs 1).
Hypothesis Hra4 : 4096 <= raZ regs.
Hypothesis Hgp : YK11.getr regs 3 = w64 (as_gp B).
Hypothesis Htp : YK11.getr regs 4 = w64 (as_tp B).
Hypothesis H10 : YK11.getr regs 10 = w64 pin.
Hypothesis H11 : YK11.getr regs 11 = w64 len.
Hypothesis H12 : YK11.getr regs 12 = w64 slot.
Hypothesis Hal : spZ regs mod 16 = 0.
Hypothesis Hwlo : sp0 - STK <= spZ regs - CRD_STK.
Hypothesis Hwhi : spZ regs <= sp0.
Hypothesis Hn : 0 <= len <= W_RECV_MAX.
Hypothesis Hlen : Z.of_nat (length bs) = len.
Hypothesis Hslot : INT_MIN <= slot <= INT_MAX.
Hypothesis Hblk : 0 < len -> exists bA nA, In (bA, nA) (ablocks B lyc Sc) /\ bA <= pin /\ pin + len <= bA + nA.
Hypothesis Hgarr : garr8 segs (mrestrict (w_H W) memc) pin (map (fun b : byte => bv_unsigned b) bs).
Hypothesis Hcnt : count_cid CRD_CID (frames Sc) < fs_frames CRD_CID.
Hypothesis Hrom : wire_rom_view_rd W memc.
Hypothesis Hnev : st_nev S + k + CRD_EV <= EV_MAX.

Local Abbreviation POST := (wire_crd_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs).
(* The inner journal: from the entry state, stack window [spZ regs - CRD_STK, spZ regs). *)
Local Abbreviation JI own1 ly1 S1 W1 m1 md1 k1 :=
  (ajournalA CRD_STK (spZ regs) [] lyc Sc W memc mdc own1 ly1 S1 W1 m1 md1 k1).

Lemma cr_HARc : @AR rc segs B lyc Sc W memc mdc.
Proof. destruct HJ as (HAR & _). exact HAR. Qed.

Lemma cr_JI0 : JI [] lyc Sc W memc mdc 0.
Proof.
  apply (ajournal_sub_init segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k CRD_STK (spZ regs) []
           (spZ regs - sp0) HJ).
  - lia.
  - pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (H16 & _) & _).
    rewrite Zminus_mod, Hal, H16. reflexivity.
  - lia.
  - unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK. lia.
  - lia.
Qed.

Lemma cr_sp_rng : YM05.alloc_ceiling + CRD_STK <= spZ regs /\ spZ regs <= 2 ^ 47.
Proof.
  pose proof cr_JI0 as J. destruct J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    (_ & _ & Hc & Hlo & Hhi & H47 & _) & _).
  lia.
Qed.

Lemma cr_win : forall own1 ly1 S1 W1 m1 md1 k1, JI own1 ly1 S1 W1 m1 md1 k1 ->
  forall a, spZ regs - CRD_STK <= a < spZ regs -> apresent (w_H W1) m1 a.
Proof.
  intros own1 ly1 S1 W1 m1 md1 k1 J.
  destruct J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). exact Hpres.
Qed.

Local Abbreviation SP := (spZ regs).
Local Abbreviation SP1 := (CRK.crk_sp1 (YK11.getr regs (Z_to_bv 5 2))).
Local Abbreviation SAVED := (CRK.crk_saved (GR regs 1) (GR regs 8) (GR regs 9) (GR regs 18) (GR regs 19)
  (GR regs 20) (GR regs 21) (GR regs 22) (GR regs 23) (GR regs 24) (GR regs 25) (GR regs 26) (GR regs 27)).

Lemma cr_sp1 : SP - 144 <= SP1 <= SP - 128 /\ SP1 mod 32 = 0.
Proof.
  pose proof cr_sp_rng as [R1 R2]. pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  apply (CRK.crk_sp1_range (YK11.getr regs (Z_to_bv 5 2))); change (bv_unsigned (YK11.getr regs (Z_to_bv 5 2)))
    with SP; unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK in *; lia.
Qed.

(* ---- after the fake frame: S2 = the state with the class-1 frame (1, pos) ---- *)
Section Frame.
Variables (S2 : astate) (pos : Z).
Hypothesis Hfrs2 : frames S2 = (CRD_CID, pos) :: frames Sc.
Hypothesis Eab2 : ablocks B lyc S2 = ablocks B lyc Sc.
Hypothesis Hset2 : exists f, S2 = set_fs f Sc.
Hypothesis Hnev2 : st_nev S2 = st_nev Sc.
Local Abbreviation F := (frame_addr lyc CRD_CID pos).
Local Abbreviation FL := (flag_addr lyc CRD_CID pos).
Local Abbreviation SHF := (F / 8 + AC.ASAN_K).

Lemma cr_in2 : In (CRD_CID, pos) (frames S2).
Proof. rewrite Hfrs2. left. reflexivity. Qed.

(* Where the frame, its shadow, its flag byte and the stack lie, at any state of the inner journal with the frame. *)
Lemma cr_geom : forall m md, @AR rc segs B lyc S2 W m md ->
  F mod 32 = 0 /\ 4096 <= F /\ F + 128 <= YM05.alloc_ceiling /\ in_app F 128 /\
  (forall a, F <= a < F + 128 -> apresent (w_H W) m a /\ ~ aowned B lyc S2 a) /\
  (forall i, 0 <= i < 16 -> apresent (w_H W) m (SHF + i) /\ ~ aowned B lyc S2 (SHF + i)) /\
  apresent (w_H W) m FL /\ aowned B lyc S2 FL /\ app_addr FL /\ ~ in_img segs FL /\
  4096 <= FL < YM05.alloc_ceiling /\
  (FL < F \/ F + 128 <= FL) /\ (FL < SHF \/ SHF + 16 <= FL) /\
  (SHF + 16 <= F \/ F + 128 <= SHF) /\ SHF + 16 <= SP1 - 4096 /\ F + 128 <= SP1 - 4096.
Proof.
  intros m md HAR.
  pose proof cr_sp_rng as [R1 R2]. pose proof cr_sp1 as [Q1 Q2].
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  destruct (al_frames _ _ LAWS _ _ _ _ _ CRD_CID pos HAR cr_in2) as (HF32 & HFapp & HFb & HFsh).
  destruct (frames_bounds segs B LAWS _ _ _ _ _ CRD_CID pos HAR cr_in2) as (HF0 & HFc & _).
  destruct (FFL lyc S2 W m md CRD_CID pos HAR cr_in2) as (HFLp & HFLo & (HFLa & HFLi) & (HFL4 & _ & HFLc)).
  change (fs_frame_bytes CRD_CID) with 128 in HFapp, HFb, HFc.
  change (fs_frame_bytes CRD_CID / 8) with 16 in HFsh.
  assert (ESH : forall i, YG0f.shadow_addr F + i = SHF + i) by (intros i; unfold YG0f.shadow_addr, SHADOW_OFF, AC.ASAN_K; lia).
  assert (HFLF : FL < F \/ F + 128 <= FL).
  { destruct (Z_lt_le_dec FL F) as [h|h]; [left; exact h|].
    destruct (Z_lt_le_dec FL (F + 128)) as [h2|h2]; [|right; exact h2].
    exfalso. exact (proj2 (HFb _ (conj h h2)) HFLo). }
  assert (HFLS : FL < SHF \/ SHF + 16 <= FL).
  { destruct (Z_lt_le_dec FL SHF) as [h|h]; [left; exact h|].
    destruct (Z_lt_le_dec FL (SHF + 16)) as [h2|h2]; [|right; exact h2].
    exfalso. pose proof (proj2 (HFsh (FL - SHF) ltac:(lia))) as Hno. rewrite ESH in Hno.
    replace (SHF + (FL - SHF)) with FL in Hno by lia. exact (Hno HFLo). }
  assert (HD8 : 0 <= F / 8) by (apply Z.div_pos; lia).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
  split; [exact HF32|]. split; [lia|]. split; [exact HFc|]. split; [unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL; exact HFapp|].
  split; [exact HFb|].
  split; [intros i Hi; rewrite <- ESH; exact (HFsh i Hi)|].
  split; [exact HFLp|]. split; [exact HFLo|]. split; [exact HFLa|]. split; [exact HFLi|].
  split; [unfold YM05.alloc_ceiling in *; lia|].
  split; [exact HFLF|]. split; [exact HFLS|].
  unfold AC.ASAN_K. unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK in *.
  assert (F / 8 <= (2 ^ 47) / 8) by (apply Z.div_le_mono; lia).
  destruct HFapp as [HA0 [HL | [HH1 HH2]]].
  - assert (F / 8 + 2147450880 >= 2147450880) by lia. split; [right; lia|]. split; lia.
  - assert (F / 8 * 8 <= F) by (Z.div_mod_to_equations; lia). split; [left; lia|]. split; lia.
Qed.

(* +0x35c (the loop done): cr_seg4_F, the frame released by its flag byte (crd_flag_free_stmt), the post. *)
Lemma cr_at_seg4 : forall regs7 m7 md7,
  JI [(CRD_CID, pos)] lyc S2 W m7 md7 0 ->
  GR regs7 8 = Z_to_bv 64 SP -> GR regs7 18 = Z_to_bv 64 F -> GR regs7 23 = Z_to_bv 64 SHF ->
  GR regs7 25 = Z_to_bv 64 F -> GR regs7 3 = GR regs 3 -> GR regs7 4 = GR regs 4 ->
  rw_cells AImg.rsegs m7 (SP - 104) SAVED ->
  bytes_at AImg.rsegs m7 (F + 120) (le8 (wa FL)) ->
  SRr segs W (@cfg_at fx segs 0x80ad8 regs7 m7 md7) POST.
Proof.
  intros regs7 m7 md7 J7 E8 E18 E23 E25 E3 E4 SV FW.
  pose proof cr_sp_rng as [R1 R2]. pose proof cr_sp1 as [Q1 Q2].
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  pose proof (proj1 J7) as HAR7.
  destruct (cr_geom m7 md7 HAR7) as (G32 & G0 & Gc & Gapp & Gb & Gsh & GLp & GLo & GLa & GLi & GLr & GLF & GLS
    & GSF & GSs & GFs).
  pose proof (cr_win _ _ _ _ _ _ _ J7) as Hwin.
  unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK in Hwin.
  destruct (crw_rw_cb W m7 SHF 16 ltac:(unfold AC.ASAN_K in *; lia) ltac:(lia)
    ltac:(intros a Ha; replace a with (SHF + (a - SHF)) by lia; apply Gsh; cbn in Ha; lia)) as (sh16 & SH).
  destruct (crw_rw_cb W m7 F 8 ltac:(lia) ltac:(lia) ltac:(intros a Ha; apply Gb; cbn in Ha; lia)) as (hd8 & HD).
  destruct (crw_rw_cb W m7 FL 1 ltac:(lia) ltac:(lia)
    ltac:(intros a Ha; cbn in Ha; replace a with FL by lia; exact GLp)) as (fl1 & FLW).
  destruct (crw_rw_cb W m7 (SP - 128) 24 ltac:(lia) ltac:(lia) ltac:(intros a Ha; apply Hwin; cbn in Ha; lia))
    as (j24 & J24).
  assert (FR : rw_cells AImg.rsegs m7 (SP + -128) (CB 24 j24 :: SAVED)).
  { change (CB 24 j24 :: SAVED) with ([CB 24 j24] ++ SAVED).
    apply (proj2 (crw_rw_cells_app m7 (SP + -128) [CB 24 j24] SAVED)). split.
    - replace (SP + -128) with (SP - 128) by lia. exact J24.
    - cbn [cells_size csize Nat.add]. replace (SP - 104) with (SP + -128 + Z.of_nat 24) in SV by lia. exact SV. }
  eapply (@crw_run fx W regs7 m7 md7 0x80ad8).
  { unfold LCK.ms_of_regs. rewrite E8, E18, E23, E25.
    eapply (CRK.cr_seg4_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 SP)
              _ _ _ _ _ _ _ _ _ _ _ _ _ F FL _ _ m7 sh16 hd8 fl1 j24);
      try rewrite crw_u64 by lia.
    all: try eassumption. all: try exact FW.
    all: try (unfold AC.ASAN_K, CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK in *; lia).
    all: apply (wcc_leafb_rng_vis W m7); unfold AC.ASAN_K in *; try lia; intros a Ha.
    all: first [ replace a with (SHF + (a - SHF)) by (unfold AC.ASAN_K; lia); apply Gsh; unfold AC.ASAN_K in *; lia
               | apply Gb; lia | replace a with FL by lia; exact GLp | apply Hwin; lia ]. }
  intros ms' md' (ms0 & (m8 & y10 & -> & MU8 & WM8 & FLB8 & SH8 & HD8) & EQV) SBM.
  destruct (crw_regs_of EQV) as (G1 & G2 & G3 & G4 & G8 & G9 & G10 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25
    & G26 & G27).
  assert (Hret : ret_pc (GR regs 1) = GR regs 1) by (apply LeafCgFacts.ret_ok_stmt_YK0s; exact Hra).
  rewrite Hret in EQV. rewrite (crw_ms_shape _ _ _ _ EQV).
  (* the frame released: the journal with no owned frame at stack_free_state *)
  set (Wr := fun a => SHF <= a < SHF + 16 \/ F <= a < F + 8 \/ a = FL).
  assert (HL : forall x, 0 <= x < 2 ^ 64 -> ~ outside [(SHF, SHF + 16); (F, F + 8); (FL, FL + 1)] x -> Wr x).
  { intros x _ Ho. unfold Wr. destruct (crw_not_outside3 _ _ _ _ _ _ x Ho) as [Hx | [Hx | Hx]]; lia. }
  assert (HP : forall a, Wr a -> apresent (w_H W) m7 a).
  { intros a [Ha | [Ha | Ha]].
    - replace a with (SHF + (a - SHF)) by lia. apply Gsh. lia.
    - apply Gb. lia.
    - subst a. exact GLp. }
  assert (HI : forall a, Wr a -> ~ in_img segs a).
  { intros a [Ha | [Ha | Ha]] Hi.
    - pose proof (WirePImg.wire_segs_low a Hi). unfold kLowMemEnd, AC.ASAN_K in *.
      assert (0 <= F / 8) by (apply Z.div_pos; lia). lia.
    - exact (frm_img segs B LAWS _ _ _ _ _ CRD_CID pos a HAR7 cr_in2 ltac:(change (fs_frame_bytes CRD_CID) with 128; lia) Hi).
    - subst a. exact (GLi Hi). }
  replace (SHF + 16) with (F / 8 + AC.ASAN_K + 16) in MU8 by reflexivity.
  destruct (crw_run_facts W m7 m8 _ Wr MU8 WM8 HL HP HI) as (K1 & K2 & K3).
  assert (J8 : JI [] lyc (stack_free_state CRD_CID pos S2) W m8 md' 0).
  { apply (FREE rc sink B LAWS ASF FFL CRD_STK SP [] lyc Sc W memc mdc [] lyc S2 W m7 md7 0 CRD_CID pos m8 md' Wr J7
             ltac:(unfold CRD_CID; lia) K1 K2 K3 SBM).
    - intros a [Ha | [Ha | Ha]]; [left | left | right; exact Ha];
        unfold awr_byte; right; right; right; exists CRD_CID, pos; (split; [left; reflexivity|]);
        unfold in_zr; cbn [fst snd]; change (fs_frame_bytes CRD_CID) with 128; change (128 / 8) with 16;
        unfold YG0f.shadow_addr, SHADOW_OFF; unfold AC.ASAN_K in *; [right | left]; lia.
    - rewrite (crw_aview_mrd W m8 FL (proj1 GLp)).
      destruct FLB8 as [[_ (_ & _ & FB)] _]. specialize (FB 0%nat ltac:(cbn; lia)).
      rewrite Z.add_0_r in FB. unfold wa in FB |- *. rewrite FB. reflexivity. }
  apply SRr_ret. unfold wire_crd_post.
  exists lyc, (stack_free_state CRD_CID pos S2), (ms_regs ms'), m8, md'.
  split; [reflexivity|].
  split.
  { pose proof (ajournal_sub segs B LAWS WirePImg.wire_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
                  CRD_STK SP [] [] lyc (stack_free_state CRD_CID pos S2) W m8 md' 0 HJ J8 Hwlo Hwhi
                  ltac:(intros a (r0 & Hr0 & _); destruct Hr0)) as J.
    cbn [app] in J. unfold CRD_EV. exact J. }
  split.
  { intros i Hi. unfold acallee_saved in Hi.
    assert (Hc : i = 2 \/ i = 3 \/ i = 4 \/ i = 8 \/ i = 9 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/
                 i = 23 \/ i = 24 \/ i = 25 \/ i = 26 \/ i = 27) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
    - etransitivity; [exact G2|]. unfold spZ. apply Z_to_bv_bv_unsigned.
    - etransitivity; [exact G3|]. exact E3.
    - etransitivity; [exact G4|]. exact E4.
    - exact G8.
    - exact G9.
    - exact G18.
    - exact G19.
    - exact G20.
    - exact G21.
    - exact G22.
    - exact G23.
    - exact G24.
    - exact G25.
    - exact G26.
    - exact G27. }
  split; [exact (KSP.crd_sf_frames CRD_CID pos S2 (frames Sc) Hfrs2)|].
  assert (Eab' : ablocks B lyc (stack_free_state CRD_CID pos S2) = ablocks B lyc Sc).
  { transitivity (ablocks B lyc S2); [unfold ablocks; rewrite blocks_stack_free_state; reflexivity | exact Eab2]. }
  split; [rewrite Eab'; apply Permutation_refl|].
  split.
  { apply (acall_kept_of_journal segs B WirePImg.wire_segs_low CRD_STK SP [] [] lyc Sc W memc mdc lyc
             (stack_free_state CRD_CID pos S2) W m8 md' 0 (fun _ => False) J8 cr_HARc).
    - intros a (r0 & Hr0 & _). destruct Hr0.
    - intros b m i Hb _ _. rewrite Eab'. exact Hb.
    - exact sink_closed_nil. }
  unfold stack_free_state. apply (mo_le_set_fs_r MT MTF).
  destruct Hset2 as (f2 & Ef2). rewrite Ef2. apply (mo_le_set_fs_r MT MTF). exact (mo_le_refl MT MTL Sc).
Qed.

Local Abbreviation GOT := (PSR.rp_slot_read_model (bv_unsigned (w64 len)) bs (bv_signed (w64 slot))).
Local Abbreviation WID := (PSW.rp_slot_width_model (bv_unsigned (w64 len)) bs (bv_signed (w64 slot))).

Lemma cr_len_u : bv_unsigned (w64 len) = len.
Proof. unfold w64. apply crw_u64. unfold W_RECV_MAX in Hn. lia. Qed.

Lemma cr_slot_s : bv_signed (w64 slot) = slot.
Proof. unfold w64. apply AKP.signed_lit. unfold INT_MIN, INT_MAX in Hslot. lia. Qed.

(* A taken read has a frame of 50 bytes or more, hence a block. *)
Lemma cr_got_len : GOT = 1 -> 50 <= len /\ 0 <= WID.
Proof.
  intros G. unfold PSR.rp_slot_read_model in G.
  destruct (Z.ltb_spec WID 0) as [L|L]; [discriminate G|].
  split; [|exact L]. unfold PSW.rp_slot_width_model in L. rewrite cr_len_u in L.
  destruct (Z.ltb_spec len 50); [cbn in L; lia | lia].
Qed.

(* c's bytes at a state of the inner journal that keeps the caller's blocks. *)
Lemma cr_garr8_at : forall own1 S1 m1 md1 k1, JI own1 lyc S1 W m1 md1 k1 ->
  ablocks B lyc S1 = ablocks B lyc Sc -> 0 < len ->
  garr8 segs (mrestrict (w_H W) m1) pin (map (fun b : byte => bv_unsigned b) bs).
Proof.
  intros own1 S1 m1 md1 k1 J1 Eab Hn0.
  destruct (Hblk Hn0) as (bA & nA & HbA & HbA1 & HbA2).
  assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia).
  pose proof J1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  apply crw_garr8_of_aview. intros j Hj. rewrite length_map in Hj.
  split.
  - replace (pin + Z.of_nat j) with (bA + (pin + Z.of_nat j - bA)) by lia.
    rewrite (F2 bA nA (pin + Z.of_nat j - bA) HbA ltac:(rewrite Eab; exact HbA) ltac:(lia)
               ltac:(intros (r0 & Hr0 & _); destruct Hr0)).
    replace (bA + (pin + Z.of_nat j - bA)) with (pin + Z.of_nat j) by lia.
    apply (crw_garr8_aview (w_H W) memc pin _ j Hgarr). rewrite length_map. exact Hj.
  - destruct (Hgarr j ltac:(rewrite length_map; exact Hj)) as [_ R]. exact R.
Qed.

(* The footprint facts of c's bytes at such a state. *)
Lemma cr_cfacts : forall own1 S1 m1 md1 k1, JI own1 lyc S1 W m1 md1 k1 ->
  ablocks B lyc S1 = ablocks B lyc Sc -> 0 < len ->
  bytes_at AImg.rsegs m1 pin bs /\ AC.addressable m1 pin len /\
  pin + len <= YM05.alloc_ceiling /\ 4096 <= pin /\
  ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) pin len /\
  ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) (AC.shadow_addr pin)
    (AC.shadow_addr (pin + len - 1) - AC.shadow_addr pin + 1) /\
  (forall x, pin <= x < pin + len -> ~ aowned B lyc S1 x /\ ~ LCK.in_img x) /\
  exists bA nA, In (bA, nA) (ablocks B lyc S1) /\ bA <= pin /\ pin + len <= bA + req_size nA.
Proof.
  intros own1 S1 m1 md1 k1 J1 Eab Hn0.
  pose proof (proj1 J1) as HAR1.
  destruct (Hblk Hn0) as (bA & nA & HbA & HbA1 & HbA2). rewrite <- Eab in HbA.
  pose proof (al_blocks _ _ LAWS lyc S1 W m1 md1 bA nA HAR1 HbA) as (_ & HA4 & HAc & _).
  assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia).
  pose proof (cr_garr8_at own1 S1 m1 md1 k1 J1 Eab Hn0) as G.
  split; [apply (wcc_leafb_bytes_garr8 W m1 pin bs G); pose proof (@YM05.alloc_ceiling_val rc); lia|].
  split; [apply (wcc_leafb_addressable_block B LAWS lyc S1 W m1 md1 bA nA pin len HAR1 HbA); lia|].
  split; [lia|]. split; [lia|].
  split; [apply (wcc_leafb_rng_block B LAWS lyc S1 W m1 md1 bA nA pin len HAR1 HbA); lia|].
  split; [apply (wcc_leafb_rng_shadow_block B LAWS lyc S1 W m1 md1 bA nA pin len HAR1 HbA); lia|].
  split; [intros x Hx; apply (wcc_leafb_wr_block B LAWS lyc S1 W m1 md1 bA nA HAR1 HbA); lia|].
  exists bA, nA. split; [exact HbA|]. lia.
Qed.

(* +0x1a4 (rp_slot_read returned): crd_seg_S3, then cr_at_seg4. *)
Lemma cr_at_seg3 : forall regs6 mem6 md6,
  JI [(CRD_CID, pos)] lyc S2 W mem6 md6 0 ->
  GR regs6 3 = GR regs 3 -> GR regs6 4 = GR regs 4 ->
  GR regs6 8 = Z_to_bv 64 SP -> GR regs6 9 = Z_to_bv 64 SP1 -> GR regs6 10 = Z_to_bv 64 GOT ->
  GR regs6 18 = Z_to_bv 64 F -> GR regs6 19 = Z_to_bv 64 (F + 32) -> GR regs6 20 = w64 pin ->
  GR regs6 21 = w64 slot -> GR regs6 22 = w64 len -> GR regs6 23 = Z_to_bv 64 SHF ->
  GR regs6 24 = Z_to_bv 64 AC.ASAN_K -> GR regs6 25 = Z_to_bv 64 F -> GR regs6 26 = Z_to_bv 64 GOT ->
  (GOT = 1 -> GR regs6 27 = Z_to_bv 64 WID) ->
  rw_cells AImg.rsegs mem6 (SP - 104) SAVED ->
  bytes_at AImg.rsegs mem6 (F + 120) (le8 (wa FL)) ->
  (GOT = 1 -> bytes_at AImg.rsegs mem6 (F + 32) (PSR.rp_slot_bytes bs WID (bv_signed (w64 slot)))) ->
  (GOT = 0 -> bytes_at AImg.rsegs mem6 (F + 32) (repeat (Z_to_bv 8 90) 48)) ->
  SRr segs W (@cfg_at fx segs 0x80920 regs6 mem6 md6) POST.
Proof.
  intros regs6 mem6 md6 J6 R3 R4 R8 R9 R10 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 SV FW VB1 VB0.
  pose proof cr_sp_rng as [P1 P2]. pose proof cr_sp1 as [Q1 Q2].
  unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK in P1.
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  pose proof (proj1 J6) as HAR6.
  destruct (cr_geom mem6 md6 HAR6) as (G32 & G0 & Gc & Gapp & Gb & Gsh & GLp & GLo & GLa & GLi & GLr & GLF & GLS
    & GSF & GSs & GFs).
  pose proof (cr_win _ _ _ _ _ _ _ J6) as Hwin.
  unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK in Hwin.
  assert (U9 : bv_unsigned (GR regs6 9) = SP1) by (rewrite R9; apply crw_u64; lia).
  destruct (crw_rw_cb W mem6 (SP1 + 18) 6 ltac:(lia) ltac:(lia) ltac:(intros a Ha; apply Hwin; cbn in Ha; lia))
    as (j6 & J6s).
  eapply (@crw_run fx W regs6 mem6 md6 0x80920).
  { unfold LCK.ms_of_regs. rewrite R10, R19, R24, R26, R20, R21, R22.
    eapply (SEG3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (w64 pin) (w64 len) (w64 slot) (F + 32)
              _ _ mem6 bs j6); rewrite ?U9.
    - rewrite cr_len_u. unfold W_RECV_MAX in Hn. lia.
    - rewrite cr_len_u. exact Hlen.
    - lia.
    - lia.
    - lia.
    - intros G. destruct (cr_got_len G) as [H50 HW].
      destruct (cr_cfacts _ _ _ _ _ J6 Eab2 ltac:(lia)) as (CB & CA & Cc & C0 & CR & CS & _).
      assert (Upin : bv_unsigned (w64 pin) = pin) by (unfold w64; apply crw_u64; lia).
      split; [exact (R27 G)|]. split; [exact (VB1 G)|]. rewrite Upin, cr_len_u.
      split; [exact CB|]. split; [exact CA|].
      split; [lia|]. split; [unfold AC.shadow_addr, AC.ASAN_K; assert ((pin + len) / 8 <= 2 ^ 47) by
        (apply Z.div_le_upper_bound; lia); lia|]. split; [exact CR | exact CS].
    - exact VB0.
    - exact J6s.
    - apply (wcc_leafb_rng_vis W mem6); [lia | lia | intros a Ha; apply Gb; lia].
    - apply (wcc_leafb_rng_vis W mem6); [lia | lia | intros a Ha; apply Hwin; lia]. }
  intros ms' md' (ms0 & (m7 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y19 & y20 & y21 & y22
    & y28 & y29 & y30 & y31 & -> & MU7 & WM7) & EQV) SBM.
  destruct (crw_regs_of EQV) as (G1 & G2 & G3 & G4 & G8 & G9 & G10 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25
    & G26 & G27).
  rewrite (crw_ms_shape _ _ _ _ EQV).
  rewrite U9 in MU7.
  assert (J7 : JI [(CRD_CID, pos)] lyc S2 W m7 md' 0).
  { apply (crw_aj_run CRD_STK SP [] lyc Sc W memc mdc [(CRD_CID, pos)] lyc S2 W mem6 md6 0 m7 md' _
             (fun a => SP1 + 18 <= a < SP1 + 24) J6 MU7 WM7).
    - intros x _ Ho. exact (crw_not_outside1 _ _ _ Ho).
    - intros a Ha. apply Hwin. lia.
    - intros a Ha Hi. pose proof (WirePImg.wire_segs_low a Hi). unfold kLowMemEnd in *. lia.
    - exact SBM.
    - intros a Ha. left. unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK. lia. }
  apply (cr_at_seg4 (ms_regs ms') m7 md' J7).
  - rewrite G8. exact R8.
  - rewrite G18. exact R18.
  - rewrite G23. exact R23.
  - rewrite G25. exact R25.
  - rewrite G3. exact R3.
  - rewrite G4. exact R4.
  - apply (rw_cells_transport _ _ _ _ _ _ SV MU7 WM7). cbn [disjoint_from cells_size CRK.crk_saved csize Nat.add].
    split; [lia | exact I].
  - apply (bytes_at_transport _ _ _ _ _ _ FW MU7). cbn [disjoint_from]. rewrite length_le8. split; [lia | exact I].
Qed.

Lemma cr_wid_got : (0 <= WID) <-> GOT = 1.
Proof.
  unfold PSR.rp_slot_read_model. destruct (Z.ltb_spec WID 0) as [L|L]; split; intros Hx;
    first [lia | discriminate Hx | reflexivity].
Qed.

Lemma cr_wid_len : 0 <= WID -> 50 <= len.
Proof. intros H. apply cr_wid_got in H. exact (proj1 (cr_got_len H)). Qed.

(* The three constants the leaf chain reads, at any state of the inner journal. *)
Lemma cr_consts : forall own1 S1 m1 md1 k1, JI own1 lyc S1 W m1 md1 k1 ->
  bytes_at AImg.rsegs m1 ARC.A_M (le8 (Z_to_bv 64 ARC.KM)) /\
  bytes_at AImg.rsegs m1 ARC.A_T (le8 (Z_to_bv 64 ARC.KT)) /\
  bytes_at AImg.rsegs m1 AFC.A_K36 (le8 (Z_to_bv 64 AFC.K36)).
Proof.
  intros own1 S1 m1 md1 k1 J1.
  pose proof (crw_rom_view_journal CRD_STK (spZ regs) own1 W memc mdc lyc S1 m1 md1 k1 lyc Sc J1 Hrom) as HR.
  split; [|split].
  - apply (crw_rom8 W m1 ARC.A_M ARC.KM HR); [| | unfold ARC.A_M; lia | unfold ARC.A_M; lia].
    + intros i Hi. unfold wire_in_ro_rd, WIRE_RO_RD, ARC.A_M. apply Exists_cons_hd. unfold in_zr. cbn. lia.
    + intros kk Hk. do 8 (destruct kk as [|kk]; [vm_compute; reflexivity|]). lia.
  - apply (crw_rom8 W m1 ARC.A_T ARC.KT HR); [| | unfold ARC.A_T; lia | unfold ARC.A_T; lia].
    + intros i Hi. unfold wire_in_ro_rd, WIRE_RO_RD, ARC.A_T. apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn. lia.
    + intros kk Hk. do 8 (destruct kk as [|kk]; [vm_compute; reflexivity|]). lia.
  - pose proof (proj1 J1) as HAR1. pose proof (w_Hoff W) as Hoff.
    destruct HAR1 as [HM _].
    assert (HK : Forall (cell_holds B lyc (aview tfibsegs (w_H W) m1)) (as_const B lyc)) by (eapply am_const; exact HM).
    exact (wcc_leafb_z8 B lyc _ m1 WIRE_RO_FCH WIRE_RO_FCH_VAL Hoff HK ltac:(wcc_leafb_row HCELLS lyc)
             ltac:(vm_compute; reflexivity) ltac:(unfold WIRE_RO_FCH; lia)).
Qed.

(* The rng of an image range: nothing in a loaded segment is hidden. *)
Lemma cr_rng_img : forall a n, wire_seg_covers a n = true -> 0 <= a -> a + n <= 2 ^ 64 ->
  ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) a n.
Proof.
  intros a n Hc H0 H1. apply (wcc_leafb_rng W); [exact H0 | exact H1 |].
  intros x Hx. replace x with (a + (x - a)) by lia.
  apply (wcc_leafb_covers_visible (w_H W) a n); [exact (w_Hoff W) | exact Hc | lia | exact H1].
Qed.

(* +0x1a0, `jal rp_slot_read` (c, len, slot, v): the leaf contract through wire_leaf_wr_at, its post the inner
   journal again (WireCcLeafb.v wcc_leafb_journal), then cr_at_seg3. *)
Lemma cr_at_leaf : forall regs5 m5 md5,
  JI [(CRD_CID, pos)] lyc S2 W m5 md5 0 ->
  GR regs5 1 = Z_to_bv 64 0x80920 -> GR regs5 2 = Z_to_bv 64 SP1 ->
  GR regs5 3 = GR regs 3 -> GR regs5 4 = GR regs 4 ->
  GR regs5 8 = Z_to_bv 64 SP -> GR regs5 9 = Z_to_bv 64 SP1 ->
  GR regs5 10 = w64 pin -> GR regs5 11 = w64 len -> GR regs5 12 = w64 slot -> GR regs5 13 = Z_to_bv 64 (F + 32) ->
  GR regs5 18 = Z_to_bv 64 F -> GR regs5 19 = Z_to_bv 64 (F + 32) -> GR regs5 20 = w64 pin ->
  GR regs5 21 = w64 slot -> GR regs5 22 = w64 len -> GR regs5 23 = Z_to_bv 64 SHF ->
  GR regs5 24 = Z_to_bv 64 AC.ASAN_K -> GR regs5 25 = Z_to_bv 64 F -> GR regs5 26 = Z_to_bv 64 GOT ->
  (GOT = 1 -> GR regs5 27 = Z_to_bv 64 WID) ->
  rw_cells AImg.rsegs m5 (SP - 104) SAVED ->
  bytes_at AImg.rsegs m5 (F + 120) (le8 (wa FL)) ->
  bytes_at AImg.rsegs m5 (F + 32) (repeat (Z_to_bv 8 90) 48) ->
  (forall i, 4 <= i < 10 -> aview segs (w_H W) m5 (SHF + i) = Some 0) ->
  SRr segs W (mkCfg (YK11.mkst regs5 (Z_to_bv 64 0x8160c) m5 (YK11.seg_rom segs)) md5) POST.
Proof.
  intros regs5 m5 md5 J5 R1 R2 R3 R4 R8 R9 R10 R11 R12 R13 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 SV FW V5 SH5.
  pose proof cr_sp_rng as [P1 P2]. pose proof cr_sp1 as [Q1 Q2].
  unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK in P1.
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  pose proof (proj1 J5) as HAR5.
  destruct (cr_geom m5 md5 HAR5) as (G32 & G0 & Gc & Gapp & Gb & Gsh & GLp & GLo & GLa & GLi & GLr & GLF & GLS
    & GSF & GSs & GFs).
  pose proof (cr_win _ _ _ _ _ _ _ J5) as Hwin.
  unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK in Hwin.
  assert (ESP : spZ regs5 = SP + (SP1 - SP)).
  { change (spZ regs5) with (bv_unsigned (GR regs5 2)). rewrite R2, crw_u64; lia. }
  assert (Ulen : bv_unsigned (w64 len) = len) by exact cr_len_u.
  eapply SRr_bind.
  { eapply (wcc_leafb_journal B LAWS W regs5 m5 CRD_STK SP [] lyc Sc W memc mdc [(CRD_CID, pos)] lyc S2 md5 0
              (SP1 - SP) 0x8160c (Some GOT) (LSR.wire_rsr_wr (0 <=? WID) (F + 32)) _ J5).
    - exact ESP.
    - pose proof Q2 as Q2'. pose proof Hal as Hal'. Z.div_mod_to_equations. lia.
    - lia.
    - unfold YG0d.ESTACK, CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK. lia.
    - change (YK11.getr regs5 1) with (GR regs5 1). rewrite R1. apply YK0s.ret_ok_even. vm_compute. reflexivity.
    - change (YK11.getr regs5 3) with (GR regs5 3). rewrite R3. exact Hgp.
    - change (YK11.getr regs5 4) with (GR regs5 4). rewrite R4. exact Htp.
    - intros a Ha. unfold LSR.wire_rsr_wr, LCK.in_wr in Ha. destruct (0 <=? WID); [|inversion Ha].
      apply Exists_cons in Ha. destruct Ha as [Ha | Ha]; [|inversion Ha]. cbn [fst snd] in Ha.
      unfold ASR.RP_SLOT_READ_VLEN in Ha.
      unfold awr_byte. right; right; right. exists CRD_CID, pos. split; [left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes CRD_CID) with 128. lia.
    - intros HPRE.
      pose proof (LEAF fx) as LF.
      unfold wire_leaf_wr_at, LSR.wire_rp_slot_read_cg in LF.
      specialize (LF lyc S2 W regs5 m5 md5 bs (SP1 - ASR.RP_SLOT_READ_STK) HPRE). cbv zeta in LF.
      rewrite R2, R10, R11, R12, R13 in LF. rewrite crw_u64 in LF by lia.
      rewrite (crw_u64 (F + 32)) in LF by lia.
      assert (UV : forall x, F + 32 <= x < F + 80 -> 4 <= x / 8 - F / 8 < 10)
        by (intros x Hx; Z.div_mod_to_equations; lia).
      destruct (cr_consts _ _ _ _ _ J5) as (KM & KT & K36).
      assert (ERS : ASR.RP_SLOT_READ_STK = 80) by reflexivity.
      apply LF; clear LF.
      all: try rewrite ERS.
      + exact KM.
      + exact KT.
      + exact K36.
      + eapply (wcc_leafb_stk_journal B); [exact J5 | unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK; lia | lia].
      + lia.
      + apply (@wcc_leafb_app_stack rc). unfold ASR.RP_SLOT_READ_STK, ASR.RP_SLOT_READ_FRAME in *. lia.
      + apply (@wcc_leafb_app_stack rc). lia.
      + exact (wcc_leafb_asan_cells B HCELLS lyc S2 W m5 md5 HAR5).
      + unfold AKA.off_stk. rewrite crw_u64 by lia. left. unfold AC.MIDEND, AC.GOT_CELL_K. lia.
      + intros H50. unfold ASR.RP_AUDIO_OFF in H50. rewrite Ulen in H50.
        destruct (cr_cfacts _ _ _ _ _ J5 Eab2 ltac:(lia)) as (CB & CA & Cc & C0 & _).
        assert (Upin : bv_unsigned (w64 pin) = pin) by (unfold w64; apply crw_u64; lia).
        rewrite Ulen, Upin, Hlen. split; [lia|]. split; [exact CB|].
        split; [unfold AKA.off_stk; rewrite crw_u64 by lia; left; lia | exact CA].
      + intros HW. pose proof (cr_wid_len HW) as H50.
        destruct (cr_cfacts _ _ _ _ _ J5 Eab2 ltac:(lia)) as (CB & CA & Cc & C0 & _ & _ & _ & bA & nA & HbA & HbA1 & HbA2).
        assert (Upin : bv_unsigned (w64 pin) = pin) by (unfold w64; apply crw_u64; lia).
        rewrite Upin, Hlen. unfold ASR.RP_SLOT_READ_VLEN.
        split; [apply (wcc_leafb_wr_at W m5 (F + 32) 48); [lia | lia | intros i Hi; apply Gb; lia]|].
        split; [unfold AKA.off_stk; rewrite crw_u64 by lia; left; lia|].
        split.
        { destruct (crw_frame_block lyc S2 W m5 md5 CRD_CID pos bA nA HAR5 cr_in2 HbA) as [D|D];
            change (fs_frame_bytes CRD_CID) with 128 in D; lia. }
        apply (wcc_leafb_addressable W m5 (F + 32) 48); [| lia | lia | unfold AC.APPMEM_END; lia |].
        * intros x Hx. exists 0. split; [|left; reflexivity].
          unfold shadow_of_addr, SHADOW_OFF. pose proof (UV x ltac:(lia)) as Ux.
          replace (2147450880 + x / 8) with (SHF + (x / 8 - F / 8)) by (unfold AC.ASAN_K; lia).
          apply SH5. lia.
        * intros i Hi. replace (F + 32 + i) with (F + (32 + i)) by lia.
          exact (wcc_leafb_app_of_in_app F 128 (32 + i) Gapp ltac:(lia)).
      + eapply (wcc_leafb_rng_journal B); [exact J5 | unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK; lia | lia].
      + exact (proj1 (wcc_leafb_rng_cells W)).
      + exact (proj2 (wcc_leafb_rng_cells W)).
      + unfold rp_slot_width_F_c.WIRE_RFC_CONSTS, AKA.off_stk. rewrite crw_u64 by lia.
        repeat (apply Forall_cons; [cbn [fst snd]; left; unfold ARC.A_M, ARC.A_T, AFC.A_K36; lia|]); apply Forall_nil.
      + unfold rp_slot_width_F_c.WIRE_RFC_CONSTS.
        repeat (apply Forall_cons; [cbn [fst snd]; apply cr_rng_img; first [vm_compute; reflexivity | unfold ARC.A_M, ARC.A_T, AFC.A_K36; lia]|]); apply Forall_nil.
      + intros H50. unfold ASR.RP_AUDIO_OFF in H50. rewrite Ulen in H50.
        destruct (cr_cfacts _ _ _ _ _ J5 Eab2 ltac:(lia)) as (CB & CA & Cc & C0 & CR & CS & _).
        assert (Upin : bv_unsigned (w64 pin) = pin) by (unfold w64; apply crw_u64; lia).
        rewrite Upin, Hlen. split; [exact CR | exact CS].
      + intros HW. unfold ASR.RP_SLOT_READ_VLEN.
        split; [apply (wcc_leafb_rng_vis W m5); [lia | lia | intros a Ha; apply Gb; lia]|].
        assert (S0 : AC.shadow_addr (F + 32) = SHF + 4) by (unfold AC.shadow_addr; Z.div_mod_to_equations; lia).
        assert (S1 : AC.shadow_addr (F + 32 + 48 - 1) = SHF + 9) by (unfold AC.shadow_addr; Z.div_mod_to_equations; lia).
        rewrite S0, S1. apply (wcc_leafb_rng_vis W m5); [unfold AC.ASAN_K; assert (0 <= F / 8) by (apply Z.div_pos; lia); lia | unfold AC.ASAN_K in *; lia |].
        intros a Ha. replace a with (SHF + (a - SHF)) by lia. apply Gsh. lia.
      + intros x Hx. unfold LSR.wire_rsr_wr, LCK.in_wr in Hx. destruct (0 <=? WID); [|inversion Hx].
        apply Exists_cons in Hx. destruct Hx as [Hx | Hx]; [|inversion Hx]. cbn [fst snd] in Hx.
        unfold ASR.RP_SLOT_READ_VLEN in Hx.
        split; [exact (proj2 (Gb x ltac:(lia)))|].
        exact (frm_img segs B LAWS _ _ _ _ _ CRD_CID pos x HAR5 cr_in2 ltac:(change (fs_frame_bytes CRD_CID) with 128; lia)). }
  cbv beta.
  intros W2 c2 _ (-> & regs6 & m6 & md6 & -> & J6 & HP6 & HRES & Heff & Hpres6 & HX).
  change (YK11.getr regs5 1) with (GR regs5 1). rewrite R1.
  assert (HK : forall a, (SP - 104 <= a < SP) \/ (F + 120 <= a < F + 128) \/ (WID < 0 /\ F + 32 <= a < F + 80) ->
    apresent (w_H W) m5 a /\ apresent (w_H W) m6 a /\ aview segs (w_H W) m6 a = aview segs (w_H W) m5 a).
  { intros a Ha.
    assert (Pa : apresent (w_H W) m5 a) by (destruct Ha as [Ha | [Ha | [_ Ha]]]; [apply Hwin | apply Gb | apply Gb]; lia).
    split; [exact Pa|]. split; [exact (Hpres6 a Pa)|].
    apply Heff.
    - destruct Ha as [Ha | [Ha | [_ Ha]]]; lia.
    - rewrite ESP. unfold YG0d.ESTACK. destruct Ha as [Ha | [Ha | [_ Ha]]]; lia.
    - intros Hw. unfold LSR.wire_rsr_wr, LCK.in_wr in Hw.
      destruct (Z.leb_spec 0 WID) as [L|L]; [|inversion Hw].
      apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; [|inversion Hw]. cbn [fst snd] in Hw.
      unfold ASR.RP_SLOT_READ_VLEN in Hw. destruct Ha as [Ha | [Ha | [Ha _]]]; lia. }
  assert (Q : forall r, acallee_saved r -> GR regs6 r = GR regs5 r) by (intros r Hr; exact (HP6 r Hr)).
  apply (cr_at_seg3 regs6 m6 md6 J6).
  - rewrite Q by (unfold acallee_saved; lia). exact R3.
  - rewrite Q by (unfold acallee_saved; lia). exact R4.
  - rewrite Q by (unfold acallee_saved; lia). exact R8.
  - rewrite Q by (unfold acallee_saved; lia). exact R9.
  - exact (HRES _ eq_refl).
  - rewrite Q by (unfold acallee_saved; lia). exact R18.
  - rewrite Q by (unfold acallee_saved; lia). exact R19.
  - rewrite Q by (unfold acallee_saved; lia). exact R20.
  - rewrite Q by (unfold acallee_saved; lia). exact R21.
  - rewrite Q by (unfold acallee_saved; lia). exact R22.
  - rewrite Q by (unfold acallee_saved; lia). exact R23.
  - rewrite Q by (unfold acallee_saved; lia). exact R24.
  - rewrite Q by (unfold acallee_saved; lia). exact R25.
  - rewrite Q by (unfold acallee_saved; lia). exact R26.
  - intros G. rewrite Q by (unfold acallee_saved; lia). exact (R27 G).
  - apply (crw_rw_kept W m5 m6 _ _ SV). intros a Ha. apply HK. left.
    cbn [cells_size CRK.crk_saved csize Nat.add] in Ha. lia.
  - apply (crw_bytes_kept W m5 m6 _ _ FW). intros a Ha. apply HK. right; left. rewrite length_le8 in Ha. lia.
  - intros G. apply HX. apply cr_wid_got. exact G.
  - intros G. assert (WN : WID < 0) by (destruct (Z.ltb_spec WID 0) as [L|L]; [exact L|];
      apply cr_wid_got in L; rewrite L in G; discriminate G).
    apply (crw_bytes_kept W m5 m6 _ _ V5). intros a Ha. apply HK. right; right.
    rewrite repeat_length in Ha. split; [exact WN | lia].
Qed.

(* +0x134 (__asan_memset returned): cr_seg2_F (the width, c[16], c[17], the want), then cr_at_leaf. *)
Lemma cr_at_seg2 : forall regs4 m4 md4,
  JI [(CRD_CID, pos)] lyc S2 W m4 md4 0 ->
  GR regs4 2 = Z_to_bv 64 SP1 -> GR regs4 3 = GR regs 3 -> GR regs4 4 = GR regs 4 ->
  GR regs4 8 = Z_to_bv 64 SP -> GR regs4 9 = Z_to_bv 64 SP1 ->
  GR regs4 18 = Z_to_bv 64 F -> GR regs4 19 = Z_to_bv 64 (F + 32) -> GR regs4 20 = w64 pin ->
  GR regs4 21 = w64 slot -> GR regs4 22 = w64 len -> GR regs4 23 = Z_to_bv 64 SHF ->
  GR regs4 24 = Z_to_bv 64 AC.ASAN_K -> GR regs4 25 = Z_to_bv 64 F ->
  rw_cells AImg.rsegs m4 (SP - 104) SAVED ->
  bytes_at AImg.rsegs m4 (F + 120) (le8 (wa FL)) ->
  bytes_at AImg.rsegs m4 (F + 32) (repeat (Z_to_bv 8 90) 48) ->
  (forall i, 4 <= i < 10 -> aview segs (w_H W) m4 (SHF + i) = Some 0) ->
  SRr segs W (@cfg_at fx segs 0x808b0 regs4 m4 md4) POST.
Proof.
  intros regs4 m4 md4 J4 R2 R3 R4 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 SV FW V4 SH4.
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  eapply (@crw_run fx W regs4 m4 md4 0x808b0).
  { unfold LCK.ms_of_regs. rewrite R24.
    eapply CRK.cr_seg2_F with (bs := bs).
    - rewrite R22, cr_len_u. unfold W_RECV_MAX in Hn. lia.
    - rewrite R22, cr_len_u. exact Hlen.
    - rewrite R22, cr_len_u. intros H50.
      destruct (cr_cfacts _ _ _ _ _ J4 Eab2 ltac:(lia)) as (CB & CA & Cc & C0 & CR & CS & _).
      assert (Upin : bv_unsigned (w64 pin) = pin) by (unfold w64; apply crw_u64; lia).
      rewrite R20, Upin. split; [exact CB|].
      split; [destruct CA as (A0 & A1 & A2 & A3); split; [exact A0|]; split; [lia|]; split; [lia|];
              intros i Hi; apply A3; lia|].
      split; [eapply ExecF.rng_sub'; [exact CR | lia]|].
      eapply ExecF.rng_sub'; [exact CS|]. unfold AC.shadow_addr.
      assert ((pin + 18 - 1) / 8 <= (pin + len - 1) / 8) by (apply Z.div_le_mono; lia). lia. }
  intros ms' md' (ms0 & (s11' & -> & E27) & EQV) SBM.
  destruct (crw_regs_of EQV) as (G1 & G2 & G3 & G4 & G8 & G9 & G10 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25
    & G26 & G27).
  destruct (crw_regs_of_a EQV) as (G11 & G12 & G13).
  rewrite (crw_ms_shape _ _ _ _ EQV).
  pose proof (crw_aj_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J4 SBM) as J5.
  rewrite R21, R22 in G26, E27.
  apply (cr_at_leaf (ms_regs ms') m4 md' J5).
  all: rewrite ?G1, ?G2, ?G3, ?G4, ?G8, ?G9, ?G10, ?G11, ?G12, ?G13, ?G18, ?G19, ?G20, ?G21, ?G22, ?G23, ?G24, ?G25,
         ?G26, ?G27.
  all: first [ assumption | reflexivity | intros G; exact (E27 G) ].
Qed.

(* +0x130, `jal __asan_memset` (v, 0x5a, 48): YCbq.v aj_intrin_at at OSet, then cr_at_seg2. *)
Lemma cr_at_memset : forall regs3 m3 md3,
  JI [(CRD_CID, pos)] lyc S2 W m3 md3 0 ->
  GR regs3 1 = Z_to_bv 64 0x808b0 -> GR regs3 2 = Z_to_bv 64 SP1 ->
  GR regs3 3 = GR regs 3 -> GR regs3 4 = GR regs 4 ->
  GR regs3 8 = Z_to_bv 64 SP -> GR regs3 9 = Z_to_bv 64 SP1 ->
  GR regs3 10 = Z_to_bv 64 (F + 32) -> GR regs3 11 = Z_to_bv 64 0x5a -> GR regs3 12 = Z_to_bv 64 0x30 ->
  GR regs3 18 = Z_to_bv 64 F -> GR regs3 19 = Z_to_bv 64 (F + 32) -> GR regs3 20 = w64 pin ->
  GR regs3 21 = w64 slot -> GR regs3 22 = w64 len -> GR regs3 23 = Z_to_bv 64 SHF ->
  GR regs3 24 = Z_to_bv 64 AC.ASAN_K -> GR regs3 25 = Z_to_bv 64 F ->
  rw_cells AImg.rsegs m3 (SP - 104) SAVED ->
  bytes_at AImg.rsegs m3 (F + 120) (le8 (wa FL)) ->
  rw_cells AImg.rsegs m3 SHF CRK.crk_sh_entry ->
  SRr segs W (mkCfg (YK11.mkst regs3 (Z_to_bv 64 (wire_sigma WS___asan_memset)) m3 (YK11.seg_rom segs)) md3) POST.
Proof.
  intros regs3 m3 md3 J3 R1 R2 R3 R4 R8 R9 R10 R11 R12 R18 R19 R20 R21 R22 R23 R24 R25 SV FW SH3.
  pose proof cr_sp_rng as [P1 P2]. pose proof cr_sp1 as [Q1 Q2].
  unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK in P1.
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  pose proof (proj1 J3) as HAR3.
  destruct (cr_geom m3 md3 HAR3) as (G32 & G0 & Gc & Gapp & Gb & Gsh & GLp & GLo & GLa & GLi & GLr & GLF & GLS
    & GSF & GSs & GFs).
  pose proof (cr_win _ _ _ _ _ _ _ J3) as Hwin.
  unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK in Hwin.
  assert (ESP : spZ regs3 = SP + (SP1 - SP)).
  { change (spZ regs3) with (bv_unsigned (GR regs3 2)). rewrite R2, crw_u64; lia. }
  assert (HF8 : F mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (UV : forall x, F + 32 <= x < F + 80 -> 4 <= x / 8 - F / 8 < 10)
    by (intros x Hx; Z.div_mod_to_equations; lia).
  assert (SHZ : forall i, 4 <= i < 10 -> aview segs (w_H W) m3 (SHF + i) = Some 0).
  { apply (crw_sh_entry_zero W m3 SHF SH3). intros i Hi. apply Gsh. lia. }
  eapply SRr_bind.
  { eapply (aj_intrin_at segs B LAWS WirePImg.wire_segs_low OSet (wire_sigma WS___asan_memset) (AIS fx)
              W regs3 m3 CRD_STK SP [] lyc Sc W memc mdc [(CRD_CID, pos)] lyc S2 md3 0 (F + 32) 0x5a 48 (SP1 - SP)
              (Z_to_bv 64 0x808b0) J3).
    - exact R10.
    - exact R11.
    - exact R12.
    - lia.
    - lia.
    - lia.
    - exact ESP.
    - pose proof Q2 as Q2'. pose proof Hal as Hal'. Z.div_mod_to_equations. lia.
    - lia.
    - unfold YG0d.ESTACK, CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK. lia.
    - change (YK11.getr regs3 3) with (GR regs3 3). rewrite R3. exact Hgp.
    - change (YK11.getr regs3 4) with (GR regs3 4). rewrite R4. exact Htp.
    - exact R1.
    - apply YK0s.ret_ok_even. vm_compute. reflexivity.
    - intros a Ha. split.
      + unfold awr_byte. right; right; right. exists CRD_CID, pos. split; [left; reflexivity|].
        left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes CRD_CID) with 128. lia.
      + unfold YG0d.ESTACK. lia.
    - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd.
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Gapp.
      destruct Gapp as (Hap1 & [HL | [HH1 HH2]]); [left | right]; lia.
    - intros x Hx. exists 0. split; [|left; reflexivity].
      unfold shadow_of_addr, SHADOW_OFF. pose proof (UV x ltac:(lia)) as Ux.
      replace (2147450880 + x / 8) with (SHF + (x / 8 - F / 8)) by (unfold AC.ASAN_K; lia).
      apply SHZ. lia.
    - intros _ sx Hs. unfold YG0f.shadow_addr, SHADOW_OFF in Hs.
      assert (E1 : (F + 32) / 8 = F / 8 + 4) by (Z.div_mod_to_equations; lia).
      assert (E2 : (F + 32 + 48 - 1) / 8 = F / 8 + 9) by (Z.div_mod_to_equations; lia).
      rewrite E1, E2 in Hs.
      assert (D4 : F / 8 mod 4 = 0) by (Z.div_mod_to_equations; lia).
      assert (Lo : SHF <= (2147450880 + (F / 8 + 4)) / 8 * 8)
        by (unfold AC.ASAN_K; Z.div_mod_to_equations; lia).
      assert (Hi : (2147450880 + (F / 8 + 9)) / 8 * 8 + 8 <= SHF + 16)
        by (unfold AC.ASAN_K; Z.div_mod_to_equations; lia).
      apply crw_aview_present. replace sx with (SHF + (sx - SHF)) by lia. apply Gsh. lia.
    - exact I. }
  cbv beta. intros W2 c2 _ (-> & regs4 & m4 & md4 & -> & J4 & HP4 & HA10 & HSET & HVIEW & HPRES).
  assert (HK : forall a, (SP - 104 <= a < SP) \/ (F + 120 <= a < F + 128) \/ (SHF + 4 <= a < SHF + 10) ->
    apresent (w_H W) m3 a /\ apresent (w_H W) m4 a /\ aview segs (w_H W) m4 a = aview segs (w_H W) m3 a).
  { intros a Ha.
    assert (Pa : apresent (w_H W) m3 a).
    { destruct Ha as [Ha | [Ha | Ha]]; [apply Hwin; lia | apply Gb; lia |].
      replace a with (SHF + (a - SHF)) by lia. apply Gsh. lia. }
    split; [exact Pa|]. split; [exact (HPRES a Pa)|].
    apply HVIEW.
    - unfold AC.ASAN_K in *. assert (0 <= F / 8) by (apply Z.div_pos; lia). destruct Ha as [Ha | [Ha | Ha]]; lia.
    - destruct Ha as [Ha | [Ha | Ha]]; lia.
    - unfold YG0d.ESTACK. destruct Ha as [Ha | [Ha | Ha]]; lia. }
  assert (Q : forall r, acallee_saved r -> GR regs4 r = GR regs3 r) by (intros r Hr; exact (HP4 r Hr)).
  apply (cr_at_seg2 regs4 m4 md4 J4).
  - rewrite Q by (unfold acallee_saved; lia). exact R2.
  - rewrite Q by (unfold acallee_saved; lia). exact R3.
  - rewrite Q by (unfold acallee_saved; lia). exact R4.
  - rewrite Q by (unfold acallee_saved; lia). exact R8.
  - rewrite Q by (unfold acallee_saved; lia). exact R9.
  - rewrite Q by (unfold acallee_saved; lia). exact R18.
  - rewrite Q by (unfold acallee_saved; lia). exact R19.
  - rewrite Q by (unfold acallee_saved; lia). exact R20.
  - rewrite Q by (unfold acallee_saved; lia). exact R21.
  - rewrite Q by (unfold acallee_saved; lia). exact R22.
  - rewrite Q by (unfold acallee_saved; lia). exact R23.
  - rewrite Q by (unfold acallee_saved; lia). exact R24.
  - rewrite Q by (unfold acallee_saved; lia). exact R25.
  - apply (crw_rw_kept W m3 m4 _ _ SV). intros a Ha. apply HK. left.
    cbn [cells_size CRK.crk_saved csize Nat.add] in Ha. lia.
  - apply (crw_bytes_kept W m3 m4 _ _ FW). intros a Ha. apply HK. right; left. rewrite length_le8 in Ha. lia.
  - apply (crw_bytes_of_aview W m4); [lia | rewrite repeat_length; lia |].
    intros i Hi. rewrite repeat_length in Hi. rewrite nth_error_repeat by exact Hi.
    rewrite (HSET (Z.of_nat i) ltac:(lia)). reflexivity.
  - intros i Hi. rewrite (proj2 (proj2 (HK (SHF + i) ltac:(right; right; lia)))). exact (SHZ i Hi).
Qed.

(* +0x78 (the stack malloc returned, a0 = F): cr_seg1_F (the frame header, the frame's shadow), then cr_at_memset. *)
Lemma cr_at_seg1 : forall regs1 m1 md1,
  JI [(CRD_CID, pos)] lyc S2 W m1 md1 0 ->
  GR regs1 2 = Z_to_bv 64 SP1 -> GR regs1 3 = GR regs 3 -> GR regs1 4 = GR regs 4 ->
  GR regs1 8 = Z_to_bv 64 SP -> GR regs1 9 = Z_to_bv 64 SP1 -> GR regs1 10 = Z_to_bv 64 F ->
  GR regs1 20 = w64 pin -> GR regs1 21 = w64 slot -> GR regs1 22 = w64 len ->
  GR regs1 24 = Z_to_bv 64 AC.ASAN_K ->
  rw_cells AImg.rsegs m1 (SP - 104) SAVED ->
  bytes_at AImg.rsegs m1 (F + 120) (le8 (wa FL)) ->
  SRr segs W (@cfg_at fx segs 0x807f4 regs1 m1 md1) POST.
Proof.
  intros regs1 m1 md1 J1 R2 R3 R4 R8 R9 R10 R20 R21 R22 R24 SV FW.
  pose proof cr_sp_rng as [P1 P2]. pose proof cr_sp1 as [Q1 Q2].
  unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK in P1.
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  pose proof (proj1 J1) as HAR1.
  destruct (cr_geom m1 md1 HAR1) as (G32 & G0 & Gc & Gapp & Gb & Gsh & GLp & GLo & GLa & GLi & GLr & GLF & GLS
    & GSF & GSs & GFs).
  pose proof (cr_win _ _ _ _ _ _ _ J1) as Hwin.
  unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK in Hwin.
  assert (HSH0 : 0 <= SHF) by (unfold AC.ASAN_K; assert (0 <= F / 8) by (apply Z.div_pos; lia); lia).
  destruct (crw_rw_cb W m1 SP1 24 ltac:(lia) ltac:(lia) ltac:(intros a Ha; apply Hwin; cbn in Ha; lia)) as (j24 & JS).
  destruct (crw_rw_cb W m1 F 24 ltac:(lia) ltac:(lia) ltac:(intros a Ha; apply Gb; cbn in Ha; lia)) as (h24 & HD).
  destruct (crw_rw_cb W m1 SHF 16 ltac:(lia) ltac:(unfold AC.ASAN_K in *; lia)
    ltac:(intros a Ha; replace a with (SHF + (a - SHF)) by lia; apply Gsh; cbn in Ha; lia)) as (sh16 & SH).
  eapply (@crw_run fx W regs1 m1 md1 0x807f4).
  { unfold LCK.ms_of_regs. rewrite R9, R10, R24.
    eapply CRK.cr_seg1_F with (fF := F) (j24 := j24) (h24 := h24) (sh16 := sh16).
    all: rewrite ?(crw_u64 SP1) by lia.
    all: try eassumption.
    all: try (unfold AC.ASAN_K in *; lia).
    - apply (wcc_leafb_rng_vis W m1); [lia | lia | intros a Ha; apply Hwin; lia].
    - apply (wcc_leafb_rng_vis W m1); [lia | lia | intros a Ha; apply Gb; lia].
    - apply (wcc_leafb_rng_vis W m1); [lia | unfold AC.ASAN_K in *; lia |].
      intros a Ha. replace a with (SHF + (a - SHF)) by lia. apply Gsh. lia. }
  intros ms' md' (ms0 & (m2 & x0 & x16 & -> & MU & WM & C1 & C2 & C3) & EQV) SBM.
  destruct (crw_regs_of EQV) as (G1 & G2 & G3 & G4 & G8 & G9 & G10 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25
    & G26 & G27).
  destruct (crw_regs_of_a EQV) as (G11 & G12 & G13).
  rewrite (crw_ms_shape _ _ _ _ EQV).
  rewrite (crw_u64 SP1) in MU, C1 by lia.
  set (Wr := fun a => SP1 <= a < SP1 + 24 \/ F <= a < F + 24 \/ SHF <= a < SHF + 16).
  assert (J2 : JI [(CRD_CID, pos)] lyc S2 W m2 md' 0).
  { apply (crw_aj_run CRD_STK SP [] lyc Sc W memc mdc [(CRD_CID, pos)] lyc S2 W m1 md1 0 m2 md' _ Wr J1 MU WM).
    - intros x _ Ho. unfold Wr. destruct (crw_not_outside3 _ _ _ _ _ _ x Ho) as [Hx | [Hx | Hx]]; lia.
    - intros a [Ha | [Ha | Ha]]; [apply Hwin; lia | apply Gb; lia |].
      replace a with (SHF + (a - SHF)) by lia. apply Gsh. lia.
    - intros a [Ha | [Ha | Ha]] Hi.
      + pose proof (WirePImg.wire_segs_low a Hi). unfold kLowMemEnd in *. lia.
      + exact (frm_img segs B LAWS _ _ _ _ _ CRD_CID pos a HAR1 cr_in2
                 ltac:(change (fs_frame_bytes CRD_CID) with 128; lia) Hi).
      + pose proof (WirePImg.wire_segs_low a Hi). unfold kLowMemEnd, AC.ASAN_K in *. lia.
    - exact SBM.
    - intros a [Ha | [Ha | Ha]].
      + left. unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK. lia.
      + unfold awr_byte; right; right; right; exists CRD_CID, pos; (split; [left; reflexivity|]).
        unfold in_zr; cbn [fst snd]; change (fs_frame_bytes CRD_CID) with 128. left; lia.
      + unfold awr_byte; right; right; right; exists CRD_CID, pos; (split; [left; reflexivity|]).
        unfold in_zr; cbn [fst snd]; change (fs_frame_bytes CRD_CID) with 128; change (128 / 8) with 16.
        unfold YG0f.shadow_addr, SHADOW_OFF; unfold AC.ASAN_K in *. right; lia. }
  replace (Z_to_bv 64 0x510d0) with (Z_to_bv 64 (wire_sigma WS___asan_memset)) by (f_equal; vm_compute; reflexivity).
  apply (cr_at_memset (ms_regs ms') m2 md' J2).
  all: rewrite ?G1, ?G2, ?G3, ?G4, ?G8, ?G9, ?G10, ?G11, ?G12, ?G13, ?G18, ?G19, ?G20, ?G21, ?G22, ?G23, ?G24, ?G25.
  all: try first [ assumption | reflexivity ].
  - apply (rw_cells_transport _ _ _ _ _ _ SV MU WM). cbn [disjoint_from cells_size CRK.crk_saved csize Nat.add].
    repeat (split; [unfold AC.ASAN_K in *; lia|]); exact I.
  - apply (bytes_at_transport _ _ _ _ _ _ FW MU). cbn [disjoint_from]. rewrite length_le8.
    repeat (split; [unfold AC.ASAN_K in *; lia|]); exact I.
Qed.

End Frame.

(* +0x74, `jal __asan_stack_malloc_1` (0x80): the class-1 fake frame F (check_read_kit_seg.v crd_stack_malloc_at_ok,
   from the statement's astack_malloc_realizes row); F >= 4096, so `bnez s2` at +0x88 is taken; then cr_at_seg1. *)
Lemma cr_at_sm : forall regs1 m1 md1,
  JI [] lyc Sc W m1 md1 0 ->
  GR regs1 1 = Z_to_bv 64 0x807f4 -> GR regs1 2 = Z_to_bv 64 SP1 ->
  GR regs1 3 = GR regs 3 -> GR regs1 4 = GR regs 4 ->
  GR regs1 8 = Z_to_bv 64 SP -> GR regs1 9 = Z_to_bv 64 SP1 ->
  GR regs1 20 = w64 pin -> GR regs1 21 = w64 slot -> GR regs1 22 = w64 len ->
  GR regs1 24 = Z_to_bv 64 AC.ASAN_K ->
  rw_cells AImg.rsegs m1 (SP - 104) SAVED ->
  SRr segs W (mkCfg (YK11.mkst regs1 (Z_to_bv 64 (pc_stack_malloc (as_code B) CRD_CID)) m1 (YK11.seg_rom segs)) md1)
    POST.
Proof.
  intros regs1 m1 md1 J1 R1 R2 R3 R4 R8 R9 R20 R21 R22 R24 SV.
  pose proof cr_sp_rng as [P1 P2]. pose proof cr_sp1 as [Q1 Q2].
  unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK in P1.
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  pose proof (cr_win _ _ _ _ _ _ _ J1) as Hwin1.
  unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK in Hwin1.
  assert (ESP : spZ regs1 = SP + (SP1 - SP)).
  { change (spZ regs1) with (bv_unsigned (GR regs1 2)). rewrite R2, crw_u64; lia. }
  eapply SRr_bind.
  { apply (SMA fx rc sink B LAWS SMP CRD_CID (ASM fx) ltac:(unfold CRD_CID; lia) W regs1 m1 CRD_STK SP [] lyc Sc W
             memc mdc [] lyc Sc md1 0 (SP1 - SP) (Z_to_bv 64 0x807f4) J1).
    - exact ESP.
    - pose proof Q2 as Q2'. pose proof Hal as Hal'. Z.div_mod_to_equations. lia.
    - lia.
    - unfold YG0d.ESTACK, CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK. lia.
    - change (YK11.getr regs1 3) with (GR regs1 3). rewrite R3. exact Hgp.
    - change (YK11.getr regs1 4) with (GR regs1 4). rewrite R4. exact Htp.
    - exact R1.
    - apply YK0s.ret_ok_even. vm_compute. reflexivity.
    - exact Hcnt. }
  cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & J2 & HP2 & HA10 & Eab & Hfrs & Hnev' & Hset
    & ZS & RDW & PRES & KEPT).
  pose proof (proj1 J2) as HAR2.
  assert (Hin : In (CRD_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
  assert (Q : forall r, acallee_saved r -> GR regs2 r = GR regs1 r) by (intros r Hr; exact (HP2 r Hr)).
  pose proof (cr_win _ _ _ _ _ _ _ J2) as Hwin2.
  unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK in Hwin2.
  destruct (al_frames _ _ LAWS _ _ _ _ _ CRD_CID pos HAR2 Hin) as (_ & _ & HFb & _).
  change (fs_frame_bytes CRD_CID) with 128 in HFb, RDW.
  destruct (frames_bounds segs B LAWS _ _ _ _ _ CRD_CID pos HAR2 Hin) as (HF0 & HFc & _).
  change (fs_frame_bytes CRD_CID) with 128 in HFc.
  eapply (cr_at_seg1 S2 pos).
  all: first [ exact Hfrs | exact Eab | exact Hset | exact Hnev' | exact J2 | idtac ].
  all: try (rewrite Q by (unfold acallee_saved; lia); assumption).
  - exact HA10.
  - destruct KEPT as [KV _].
    apply (crw_rw_kept W m1 mem2 _ _ SV). intros a Ha.
    cbn [cells_size CRK.crk_saved csize Nat.add] in Ha.
    split; [apply Hwin1; lia|]. split; [apply Hwin2; lia|].
    apply KV; [unfold YM05.alloc_ceiling in *; lia | unfold YG0d.ESTACK; lia].
  - apply (crw_rdword_bytes W mem2); [lia | lia | |].
    + intros i Hi. exact (proj1 (proj1 (HFb (frame_addr lyc CRD_CID pos + 120 + i) ltac:(lia)))).
    + replace (frame_addr lyc CRD_CID pos + 120) with (frame_addr lyc CRD_CID pos + 128 - 8) by lia. exact RDW.
Qed.

(* The entry: cr_seg0_F (the frame, the realign, the UAR flag and the shadow base), then cr_at_sm. *)
Lemma cr_entry : SRr segs W (@cfg_at fx segs 0x8077c regs memc mdc) POST.
Proof.
  pose proof cr_sp_rng as [P1 P2]. pose proof cr_sp1 as [Q1 Q2].
  unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK in P1.
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  pose proof cr_JI0 as J0.
  pose proof (cr_win _ _ _ _ _ _ _ J0) as Hwin0.
  unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK in Hwin0.
  destruct (wcc_leafb_asan_cells B HCELLS lyc Sc W memc mdc cr_HARc)
    as (AK & AGK & _ & _ & _ & AU & AGU & _).
  eapply (@crw_run fx W regs memc mdc 0x8077c).
  { unfold LCK.ms_of_regs.
    eapply CRK.cr_seg0_F with (lo := SP - CRD_STK).
    - eapply (wcc_leafb_stk_journal B); [exact J0 | lia | change (bv_unsigned (GR regs 2)) with SP; lia].
    - unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK. change (bv_unsigned (GR regs 2)) with SP. lia.
    - change (bv_unsigned (GR regs 2)) with SP. unfold YM05.alloc_ceiling in *. lia.
    - exact AGU.
    - exact AU.
    - exact AGK.
    - exact AK.
    - eapply (wcc_leafb_rng_journal B); [exact J0 | change (bv_unsigned (GR regs 2)) with SP; unfold CRD_STK, CRD_FRAME,
        CRD_ALIGN, ESTACK; lia | change (bv_unsigned (GR regs 2)) with SP; lia].
    - apply cr_rng_img; [vm_compute; reflexivity | unfold AC.GOT_UAR; lia | unfold AC.GOT_UAR; lia].
    - apply cr_rng_img; [vm_compute; reflexivity | unfold AC.UAR; lia | unfold AC.UAR; lia].
    - exact (proj1 (wcc_leafb_rng_cells W)).
    - exact (proj2 (wcc_leafb_rng_cells W)). }
  intros ms' md' (ms0 & (m1 & v0 & v8 & v16 & -> & MU & WM & FR) & EQV) SBM.
  destruct (crw_regs_of EQV) as (G1 & G2 & G3 & G4 & G8 & G9 & G10 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25
    & G26 & G27).
  rewrite (crw_ms_shape _ _ _ _ EQV).
  change (bv_unsigned (GR regs 2)) with SP in MU, FR.
  assert (J1 : JI [] lyc Sc W m1 md' 0).
  { apply (crw_aj_run CRD_STK SP [] lyc Sc W memc mdc [] lyc Sc W memc mdc 0 m1 md' _ (fun a => SP - 128 <= a < SP)
             J0 MU WM).
    - intros x _ Ho. exact (crw_not_outside1 _ _ _ Ho).
    - intros a Ha. apply Hwin0. lia.
    - intros a Ha Hi. pose proof (WirePImg.wire_segs_low a Hi). unfold kLowMemEnd, YM05.alloc_ceiling in *. lia.
    - exact SBM.
    - intros a Ha. left. unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK. lia. }
  replace (Z_to_bv 64 0x3c6b8) with (Z_to_bv 64 (pc_stack_malloc (as_code B) CRD_CID))
    by (rewrite HPCS; f_equal; vm_compute; reflexivity).
  apply (cr_at_sm (ms_regs ms') m1 md' J1).
  all: rewrite ?G1, ?G2, ?G3, ?G4, ?G8, ?G9, ?G10, ?G18, ?G19, ?G20, ?G21, ?G22, ?G23, ?G24, ?G25.
  all: try first [ assumption | reflexivity ].
  change (CRK.crk_saved _ _ _ _ _ _ _ _ _ _ _ _ _) with SAVED in FR.
  change (C8 v0 :: C8 v8 :: C8 v16 :: SAVED) with ([C8 v0; C8 v8; C8 v16] ++ SAVED) in FR.
  destruct (proj1 (crw_rw_cells_app m1 (SP - 128) _ _) FR) as [_ FR2].
  cbn [cells_size csize Nat.add] in FR2. replace (SP - 128 + Z.of_nat 24) with (SP - 104) in FR2 by lia.
  exact FR2.
Qed.

End Entry.
End Walk.

Section crdW.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.

Theorem wire_check_read_holds : @wire_check_read_holds_stmt fx rc B MT.
Proof.
  intros HPCS HCELLS HROU HERR LAWS MTL MTF SMP ASF FFL ASM AIS LEAF.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pin len slot bs HJ Hra Hra4 Hgp Htp H10 H11 H12
    Hal Hwlo Hwhi Hn Hlen Hslot Hblk Hgarr Hcnt Hrom Hnev.
  replace (wire_sigma WS_check_read) with 0x8077c by (vm_compute; reflexivity).
  eapply cr_entry.
  all: first [ exact KSP.crd_stack_malloc_at_ok | exact KSP.crd_flag_free_ok | exact S3P.crd_seg_S3_ok
             | eassumption ].
Qed.

End crdW.
