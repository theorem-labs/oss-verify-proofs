(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths and module names changed; 754 of its 794 lines of code are new or changed and 356 lines of the source are left out. *)
(* Segment F31 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): the range 0x82af8-0x82b34
   (F31 (slot-plan-asan-ubsan section 2 (a working note, not in this delivery)), call BCMP@0x82b34, twin C02; v1.8 0x82a94-0x82ad0, a Theorem Labs lane's
   S_F31 (v190-segment-table (a working note, not in this delivery)): IDENTICAL-RENUMBER). The image-B port of lib/A/Prog/Seg/F31.v (image A v1.8
   0x826ec-0x82728, commit 3b7ac10af31).
     0x82af8 bnez a0,0x82b5c    a0 = cl_r (the classify result of F30's call): taken iff classify = None (a0 = -1)
     0x82afc ld a0,144(s1)      [A+144] = fr+452 = o+4 (0x81e94-0x81e9c; o = [A+216] = fr+448 from 0x81494-0x81498)
     0x82b00 lbu a0,0(a0)       the byte o+4 = 0x00
     0x82b04 bnez a0,0x82fa4    not taken
     0x82b08 ld a0,216(s1); lbu a0,5(a0); li a1,64; bne a0,a1,0x82fa4    the byte o+5 = 0x40: not taken
     0x82b18 ld a0,216(s1); lbu a0,6(a0); li a1,171; bne a0,a1,0x82fa4   the byte o+6 = 0xab: not taken
     0x82b28 li a2,6; ld a0,144(s1); ld a1,264(s1)    [A+264] = fr+2624 = our[] (0x814f4 / 0x81544)
     0x82b34 jal wrapper_bcmp   return point 0x82b38 with a0 = memcmp_model of (o+4 .. o+9) and our[] over 6 bytes
   classify = Some e makes the source field of the classify output (t_B bytes 4..9) begin 00 40 ab (RcClassify.cl_oui),
   so the three failure branches to 0x82fa4 are not taken. The range has no instrumented check and no branch to
   0x82fa0. The wrapper checks that the 6 bytes at o+4 and the 6 bytes at our[] are marked usable in the shadow map;
   both ranges are addressable (the entry cut), so the error path is not reached (the lib/B contract
   bcmp_wrap_contract, a Section Hypothesis). The wrapper writes only its stack scratch [sp - 4560, sp); FRA moves
   across that write by f31_stk_run (the scratch is below sp, so apart from the spill area and the saved registers,
   and apart from the frame by SlotInv.fra_frame), then to the materialized model by Tac_slot.sl_fra_move.
   v1.9.0 homes of the pass-through state: the tfill flag in the spill [A+184] (FTK; 0x8212c sd a0,184(s1), 0x82100 /
   0x8204c sd zero,184(s1)); the sum flag in s9 (reg 25; 0x82140 seqz s9,a0 / 0x8205c mv s9,zero, moved back at
   0x82ab4 mv s9,s8); s6 = 1 (reg 22; 0x82ab0); k in s8 (reg 24, moved back from [A+272] at 0x82ab8); the classify
   event word pointer [A+192] = fr+528 (0x814a0); Phi s2 (reg 18); len s4 (reg 20); fr+64 in [A+152] (0x815a0) and
   fr+32 in [A+160] (0x815a4) (PT32); blk in [A+312] (FB); j in [A+240] (LK, 0x81f44). The bcmp wrapper keeps every
   callee-saved register, so all of them pass through.
   Entry cut Inv_B82af8_at; exit cuts Inv_B82b38_at (the wrapper's return) and Inv_B82b5c_at (the target
   of the bnez at 0x82af8). The image-A cuts' frame-placement conjuncts (the FakeStack-metadata bound, the frame /
   window disjunction, fr + FRAME_BYTES <= s1) and the bound sp <= APPMEM_END are not carried: FRA gives them
   (SlotInv.fra_frame; sp <= A, A + 448 <= S < APPMEM_END). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse RcClassify RcClassifyLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require memcmp_c bcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_ro.
Import ListNotations.
(* lib.Prog's RcParse chain loads lib/Reusable/YK11.v, so the short name YK11 would resolve to that copy; this
   file's registers, mkst and FPState must be image B's, as SlotInv's and Tac_slot's are. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module BW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.bcmp_wrap_c.
Module SF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec.StrFun.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module RP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcParse.
Module RC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcClassify.
Module RCL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcClassifyLib.

Local Definition BCMP_WRAP_K := 4560.
Local Definition BCMP := 0x98930.
Local Definition REAL_BCMP := 0xa2610.
Local Definition REAL_MEMCMP := 0xa2608.
Local Definition GOT_CF := 0xa08e0.
Local Definition CF := 0x13b1e8.
Local Definition MEMCMP := 0x98a00.
Local Notation memcmp_model := SF.memcmp_model.

(* ---- Model facts: the classify result (C1.8 of the classify contract's model). *)
Lemma f31_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. exact H.
Qed.

Lemma f31_cls_r : forall c, RC.cl_r c = 0 \/ RC.cl_r c = -1.
Proof. intros [e|]; [left | right]; reflexivity. Qed.

Lemma f31_cls_some : forall c, RC.cl_r c = 0 -> exists e, c = Some e.
Proof. intros [e|] H; [exists e; reflexivity | unfold RC.cl_r in H; discriminate H]. Qed.

Lemma f31_cls_B : forall inp j e, t_cls inp j = Some e -> t_B inp j = RP.cp_struct (t_g inp j) (t_k inp j).
Proof.
  intros inp j e H. unfold t_cls in H.
  destruct (RCL.classify_some _ _ _ _ H) as (K & _).
  destruct (RCL.cl_hdr _ _ K) as [_ HB]. exact HB.
Qed.

Lemma f31_cls_oui : forall inp j e, t_cls inp j = Some e ->
  RP.cp_v (t_g inp j) 6 = 0 /\ RP.cp_v (t_g inp j) 7 = 64 /\ RP.cp_v (t_g inp j) 8 = 171.
Proof.
  intros inp j e H. unfold t_cls in H.
  destruct (RCL.classify_some _ _ _ _ H) as (_ & _ & OUI & _).
  unfold RC.cl_oui in OUI. apply andb_prop in OUI as [OUI O8]. apply andb_prop in OUI as [O6 O7].
  apply Z.eqb_eq in O6, O7, O8. split; [exact O6|]. split; [exact O7 | exact O8].
Qed.

Lemma f31_cp_b : forall fr i v, RP.cp_v fr i = v -> 0 <= v < 256 -> RP.cp_b fr i = Z_to_bv 8 v.
Proof.
  intros fr i v E Hv. apply bv_eq. unfold RP.cp_v in E. rewrite E. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small; lia.
Qed.

Lemma f31_struct_src : forall fr k,
  firstn 6 (skipn 4 (RP.cp_struct fr k)) =
  [RP.cp_b fr 6; RP.cp_b fr 7; RP.cp_b fr 8; RP.cp_b fr 9; RP.cp_b fr 10; RP.cp_b fr 11].
Proof. intros fr k. unfold RP.cp_struct. destruct (RP.cp_rec fr), (k =? 6); reflexivity. Qed.

(* classify = Some e: the source field of the classify output (bytes 4..9 of t_B) begins 00 40 ab. *)
Lemma f31_B_src : forall inp j e, t_cls inp j = Some e ->
  firstn 6 (skipn 4 (t_B inp j)) =
  [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; RP.cp_b (t_g inp j) 9; RP.cp_b (t_g inp j) 10; RP.cp_b (t_g inp j) 11].
Proof.
  intros inp j e H. rewrite (f31_cls_B inp j e H), f31_struct_src.
  destruct (f31_cls_oui inp j e H) as (O6 & O7 & O8).
  rewrite (f31_cp_b _ 6 0 O6), (f31_cp_b _ 7 64 O7), (f31_cp_b _ 8 171 O8) by lia. reflexivity.
Qed.

Lemma f31_B_length : forall inp j, length (t_B inp j) = 36%nat.
Proof. intros inp j. apply RP.ctrlparse_length. Qed.

Lemma f31_mm_spec : forall n l r v, length l = n -> length r = n -> memcmp_model l r n = Some v ->
  (v = 0 <-> l = r) /\ -256 < v < 256.
Proof.
  induction n as [|n IH]; intros l r v Hl Hr H.
  - destruct l; [|discriminate]. destruct r; [|discriminate]. cbn in H. inversion H. split; [tauto|lia].
  - destruct l as [|a l]; [discriminate|]. destruct r as [|b r]; [discriminate|]. cbn in Hl, Hr, H.
    pose proof (f31_byte_range a) as Ra. pose proof (f31_byte_range b) as Rb.
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E].
    + destruct (IH l r v ltac:(lia) ltac:(lia) H) as [I1 I2]. split; [|exact I2].
      apply bv_eq in E. subst b. split.
      * intros Hv. f_equal. apply I1. exact Hv.
      * intros Hq. apply I1. injection Hq as Hq. exact Hq.
    + inversion H; subst v. split; [|lia]. split; [lia|]. intros Hq. injection Hq as Hab _. subst b. contradiction.
Qed.

Lemma f31_lit0 : forall v, -256 < v < 256 -> (Z_to_bv 64 v = Z_to_bv 64 0 <-> v = 0).
Proof.
  intros v Hv. split; intros E; [|subst; reflexivity].
  apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit_wrap in E. change (0 mod 2 ^ 64) with 0 in E.
  Z.div_mod_to_equations. lia.
Qed.

Lemma f31_ba_sub : forall m A bs k jj, bytes_at rsegs m A bs -> (k + jj <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn jj (skipn k bs)).
Proof.
  intros m A bs k jj (HA & HL & H) Hkj.
  assert (Lf : length (firstn jj (skipn k bs)) = jj) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite Lf; lia|].
  intros i Hi. rewrite Lf in Hi.
  replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia.
  rewrite H by lia. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i jj) as [_|C]; [|lia].
  rewrite nth_error_skipn. reflexivity.
Qed.

(* A spilled word at s1 + off read at the FRA spill base A (the existential base of `spill` is A). *)
Lemma f31_spill : forall regs m off v A, spill regs m off v -> rg regs 9 A ->
  0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off <= 440 -> q64 m (A + off) v.
Proof.
  intros regs m off v A (A' & HA' & Hq) HA H0 H1 Hoff.
  unfold rg in HA, HA'. rewrite HA in HA'.
  pose proof Hq as (Hq0 & Hq1 & _). rewrite length_le8 in Hq1.
  assert (E : A' = A).
  { apply (f_equal bv_unsigned) in HA'. rewrite !unsigned_lit_wrap in HA'.
    rewrite (Z.mod_small A) in HA' by lia. Z.div_mod_to_equations. lia. }
  subst A'. exact Hq.
Qed.

(* 0x82af8 with a0 = -1 (classify = None): bnez a0 is taken to 0x82b5c. *)
Lemma f31n_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0 = Z_to_bv 64 (-1) ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                              t3 t4 t5 t6) Fr (Z_to_bv 64 0x82b5c) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82af8) fc None m (seg_rom rsegs)).
Proof.
  intros. subst a0. step. try if_true. apply evt_done. reflexivity.
Qed.

Section F31.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The bcmp wrapper (wrapper_bcmp 0x42aac): it checks that the n bytes at a0 and at a1 are marked usable, then
   calls musl bcmp; a0 = memcmp_model on return; it writes only [sp - 4560, sp). *)
Hypothesis HBC : BW.bcmp_wrap_contract.

(* ---- Cut states (SlotInv's). Frame variables are fr-relative: [A+216] = fr+448 = o, the classify output (36 bytes
   = t_B j); [A+144] = fr+452 = o+4, its source field; [A+264] = fr+2624 = our[]; [A+192] = fr+528, the classify
   event word. Entry Inv_B82af8_at: the classify result in a0, those spills and bytes, the bcmp wrapper's premises
   (the two operand ranges addressable) and the pass-through state: PT32 (Phi s2, k s8, len s4, the spills fr+64
   [A+152], blk [A+312], fr+32 [A+160], the Phi bytes, the frame), FTK (the spills tfill [A+184] and k [A+272],
   s6 = 1, k s8, sum_ok s9), FTURN and IFS (S j). Exit Inv_B82b38_at: a0 = the compare result as the OUR match
   and the same pass-through; exit Inv_B82b5c_at: the pass-through alone. The bcmp run writes only the wrapper's
   scratch below sp, so the spills (at or above sp), the frame (fra_frame), the kind-name table (low image) and
   the Phi bytes (the heap block) cross it (Seg/Tac_ro.v's lk_keep / turn_keep / ifs_munch / knt_munch). *)

(* 0x82af8 with a0 = 0: the three byte checks of the source field (00 40 ab) are not taken, then the bcmp wrapper
   compares the 6 bytes at O+4 with the 6 bytes at R. *)
Lemma f31c_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A O R : Z) (c9 c10 c11 : byte) (rs : list byte) (vcmp lo : Z),
    s1v = Z_to_bv 64 A -> a0 = Z_to_bv 64 0 ->
    0 <= O /\ O + 16 <= 2 ^ 64 -> 0 <= R < 2 ^ 64 ->
    bytes_at rsegs m (A + 144) (le8 (Z_to_bv 64 (O + 4))) ->
    bytes_at rsegs m (A + 216) (le8 (Z_to_bv 64 O)) ->
    bytes_at rsegs m (A + 264) (le8 (Z_to_bv 64 R)) ->
    bytes_at rsegs m (O + 4) [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; c9; c10; c11] ->
    bytes_at rsegs m R rs -> length rs = 6%nat ->
    memcmp_model [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; c9; c10; c11] rs 6 = Some vcmp ->
    mem_inv rsegs m -> addressable m (O + 4) 6 -> addressable m R 6 ->
    app_mem (O + 4 + 6) -> app_mem (R + 6) -> app_mem (O + 4 + 7) -> app_mem (R + 7) ->
    (O + 4 + 6 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= O + 4) ->
    (R + 6 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= R) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    LE.evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 vcmp) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82b38) fc None m' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
         /\ asan_cells m' /\ shadow_rw m')
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82af8) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A O R c9 c10 c11 rs vcmp lo -> -> [HO0 HO1] HR0 H144 H216 H264 HBL HBR HLrs Hmm HMI HADL HADR
    HaL6 HaR6 HaL7 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC HSW HRB HRM HGC HC254 HC255.
  assert (HL144 : ov_read_bytes rsegs m (wa (A + 144)) 8 = Some (le8 (Z_to_bv 64 (O + 4)))).
  { pose proof (bytes_at_ov_read rsegs m (A + 144) _ 0 8 H144 ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (HL216 : ov_read_bytes rsegs m (wa (A + 216)) 8 = Some (le8 (Z_to_bv 64 O))).
  { pose proof (bytes_at_ov_read rsegs m (A + 216) _ 0 8 H216 ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (HL264 : ov_read_bytes rsegs m (wa (A + 264)) 8 = Some (le8 (Z_to_bv 64 R))).
  { pose proof (bytes_at_ov_read rsegs m (A + 264) _ 0 8 H264 ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (HB4 : ov_read_bytes rsegs m (wa (O + 4)) 1 = Some [Z_to_bv 8 0]).
  { pose proof (bytes_at_ov_read rsegs m (O + 4) _ 0 1 HBL ltac:(cbn; lia)) as HH.
    cbn [firstn skipn] in HH. replace (O + 4 + Z.of_nat 0) with (O + 4) in HH by lia. exact HH. }
  assert (HB5 : ov_read_bytes rsegs m (wa (O + 5)) 1 = Some [Z_to_bv 8 64]).
  { pose proof (bytes_at_ov_read rsegs m (O + 4) _ 1 1 HBL ltac:(cbn; lia)) as HH.
    cbn [firstn skipn] in HH. replace (O + 4 + Z.of_nat 1) with (O + 5) in HH by lia. exact HH. }
  assert (HB6 : ov_read_bytes rsegs m (wa (O + 6)) 1 = Some [Z_to_bv 8 171]).
  { pose proof (bytes_at_ov_read rsegs m (O + 4) _ 2 1 HBL ltac:(cbn; lia)) as HH.
    cbn [firstn skipn] in HH. replace (O + 4 + Z.of_nat 2) with (O + 6) in HH by lia. exact HH. }
  (* 0x82af8 bnez a0 (a0 = 0): not taken *)
  step. try if_false.
  (* 0x82afc ld a0,144(s1); lbu a0,0(a0) = 0x00; bnez a0 (to 0x82fa4): not taken *)
  step. step. step. try if_false.
  (* 0x82b08 ld a0,216(s1); lbu a0,5(a0) = 0x40; li a1,64; bne a0,a1 (to 0x82fa4): not taken *)
  step. step. step. step. try if_false.
  (* 0x82b18 ld a0,216(s1); lbu a0,6(a0) = 0xab; li a1,171; bne a0,a1 (to 0x82fa4): not taken *)
  step. step. step. step. try if_false.
  (* 0x82b28 li a2,6; ld a0,144(s1); ld a1,264(s1); jal wrapper_bcmp *)
  step. step. step. step.
  pose proof HBC as HB. unfold BW.bcmp_wrap_contract, BW.BCMP_WRAP_K in HB. cbv zeta in HB.
  assert (EL : bv_unsigned (Z_to_bv 64 (O + 4)) = O + 4) by (apply unsigned_lit; lia).
  assert (ER : bv_unsigned (Z_to_bv 64 R) = R) by (apply unsigned_lit; lia).
  assert (E6 : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
  eapply evt_cut.
  { eapply HB with (ls := [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; c9; c10; c11]) (rs := rs) (v := vcmp) (lo := lo).
    all: rewrite ?EL, ?ER, ?E6.
    - exact HBL.
    - exact HBR.
    - change (Z.to_nat 6) with 6%nat; exact Hmm.
    - exact HMI.
    - clear; lia.
    - exact HADL.
    - exact HADR.
    - right; exact HaL6.
    - right; exact HaR6.
    - right; exact HaL7.
    - right; exact HaR7.
    - exact HdjL.
    - exact HdjR.
    - exact HST.
    - exact Hlo1.
    - exact Hlo2.
    - exact Hspa.
    - exact HAC.
    - exact HSW.
    - exact HRB.
    - exact HRM.
    - exact HGC.
    - exact HC254.
    - exact HC255. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m'
              & E & MU & WM & MI' & ST' & AC' & SW' & _ & _).
  subst ms'.
  match goal with
  | |- context [ret_pc (Z_to_bv 64 ?z)] =>
      replace (ret_pc (Z_to_bv 64 z)) with (Z_to_bv 64 z) by (symmetry; apply ret_pc_even; [clear; lia | reflexivity])
  end.
  apply evt_done.
  eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  split; [exact AC' | exact SW'].
Qed.

(* f31c_evt on the cut's own memory: ro_agree in place of mem_inv. The run is taken on the normalized memory
   (mem_inv_normalize), where the read-side premises hold by the mem_rel transfer lemmas of Seg/Tac_ro.v, and
   MemNorm.evt_normalize carries it back to the cut's memory; the post's write facts come back across mem_rel /
   ro_same. The runtime cells of the post (asan_cells, shadow_rw) are not needed by the caller and are dropped. *)
Lemma f31c_evt_ro :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A O R : Z) (c9 c10 c11 : byte) (rs : list byte) (vcmp lo : Z),
    s1v = Z_to_bv 64 A -> a0 = Z_to_bv 64 0 ->
    0 <= O /\ O + 16 <= 2 ^ 64 -> 0 <= R < 2 ^ 64 ->
    bytes_at rsegs m (A + 144) (le8 (Z_to_bv 64 (O + 4))) ->
    bytes_at rsegs m (A + 216) (le8 (Z_to_bv 64 O)) ->
    bytes_at rsegs m (A + 264) (le8 (Z_to_bv 64 R)) ->
    bytes_at rsegs m (O + 4) [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; c9; c10; c11] ->
    bytes_at rsegs m R rs -> length rs = 6%nat ->
    memcmp_model [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; c9; c10; c11] rs 6 = Some vcmp ->
    ro_agree rsegs m -> addressable m (O + 4) 6 -> addressable m R 6 ->
    app_mem (O + 4 + 6) -> app_mem (R + 6) -> app_mem (O + 4 + 7) -> app_mem (R + 7) ->
    (O + 4 + 6 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= O + 4) ->
    (R + 6 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= R) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    LE.evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 vcmp) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82b38) fc None m' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ ro_agree rsegs m' /\ ro_same rsegs m m'
         /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82af8) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A O R c9 c10 c11 rs vcmp lo E1 E0 HO HR0 H144 H216 H264 HBL HBR HLrs Hmm HRO HADL HADR
    HaL6 HaR6 HaL7 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC HSW HRB HRM HGC HC254 HC255.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  assert (Hlo0 : LOWMEM_END <= lo) by (unfold HIGHMEM_BEG, LOWMEM_END in *; lia).
  assert (Hsp64 : bv_unsigned sp <= 2 ^ 64) by (unfold APPMEM_END in Hspa; lia).
  pose proof (f31c_evt ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 Fr fc (normalize rsegs m) A O R c9 c10 c11 rs vcmp lo E1 E0 HO HR0
    (Tac_ro.ba_rel m _ _ _ REL H144) (Tac_ro.ba_rel m _ _ _ REL H216) (Tac_ro.ba_rel m _ _ _ REL H264)
    (Tac_ro.ba_rel m _ _ _ REL HBL) (Tac_ro.ba_rel m _ _ _ REL HBR) HLrs Hmm (mem_inv_normalize rsegs m)
    (Tac_ro.addressable_rel m _ _ _ REL HADL) (Tac_ro.addressable_rel m _ _ _ REL HADR)
    HaL6 HaR6 HaL7 HaR7 HdjL HdjR (Tac_ro.stk_rel m _ lo _ REL Hlo0 Hsp64 HST) Hlo1 Hlo2 Hspa
    (Tac_ro.asan_cells_rel m _ REL HAC) (Tac_ro.shadow_rw_rel m _ REL HSW)
    (Tac_ro.ba_rel m _ _ _ REL HRB) (Tac_ro.ba_rel m _ _ _ REL HRM) (Tac_ro.ba_rel m _ _ _ REL HGC)
    (Tac_ro.ba_rel m _ _ _ REL HC254) (Tac_ro.ba_rel m _ _ _ REL HC255)) as HC.
  pose proof (evt_normalize rsegs _ _ _ _ _ _ m (seg_rom rsegs) ltac:(vm_compute; reflexivity) HRO HC) as HN.
  eapply LE.evt_mono; [exact HN|].
  intros ms (s0' & (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m0'
              & E & MU & WM & MI' & ST' & AC' & SW') & Hrel & Hros).
  subst s0'.
  destruct ms as [regsX frX pcX svcX rvX fcX memX romX].
  destruct Hrel as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmr).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS]
    in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmr, Hros.
  subst regsX frX pcX svcX rvX fcX romX.
  exists ra', a1', a2', a3', a4', a5', a6', a7', t0', t1', t2', t3', t4', t5', t6', memX.
  split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) memX m0' REL Hmr Hros MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) memX m0' REL Hmr Hros WM)|].
  split; [exact (ro_agree_of_mem_rel rsegs memX m0' Hmr)|].
  split; [exact Hros|].
  exact (Tac_ro.stk_rel_back memX m0' lo _ Hmr Hlo0 Hsp64 ST').
Qed.

(* Lib-evt -> SR bridge: the one place of this file that uses the lazy-model lemma AsanLift.evt_SR_canon_lazy. seg_F31
   uses it for its two runs from 0x82af8:
   - classify = None (f31n_evt): 0x82af8 -> 0x82b5c, one taken branch; it reads registers only and touches no memory.
   - classify = Some e (f31c_evt): 0x82af8 -> 0x82b38 through wrapper_bcmp. It reads the words [s1+144, s1+152),
     [s1+216, s1+224), [s1+264, s1+272), the operand bytes [fr+452, fr+458) and [fr+2624, fr+2630) and their shadow
     bytes at (a >> 3) + 0x7fff8000, the runtime cells of the wrapper (REAL_BCMP 0xa2610, REAL_MEMCMP 0xa2608, GOT_CF
     0xa08e0, CF+254 / CF+255 at 0x13b2e6 / 0x13b2e7, the shadow-map cells of asan_cells), and writes only the
     wrapper's stack scratch [sp - 4560, sp) (BCMP_WRAP_K).
   The bcmp wrapper contract lives in Lib.Exec, so these runs are Lib.Exec.evt and feed evt_SR_canon_lazy directly. *)
Lemma sl_run_lib : forall regs pc mem md
  (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None ->
  LE.evt rsegs
    (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\ K R pc' mem')
    (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' mem' regs' md', K R pc' mem' -> (forall r, getr regs' r = getr R r) -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' mem' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh HE HK.
  eapply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE | exact Hh |].
  intros ms' md' (can & (R & pc' & mem' & -> & HKR) & Heq) Hmat.
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' md' HKR); [apply kb_getr_eqv; exact HR | exact Hmat].
Qed.

(* The runtime cells the wrapper_bcmp contract reads, from the FRA runtime invariant. *)
Lemma bcmp_cells : forall sp mem md, AsanRTInv.RT sp mem md ->
  asan_cells mem /\ shadow_rw mem /\
  bytes_at rsegs mem REAL_BCMP (le8 (wa BCMP)) /\ bytes_at rsegs mem REAL_MEMCMP (le8 (wa MEMCMP)) /\
  bytes_at rsegs mem GOT_CF (le8 (wa CF)) /\
  bytes_at rsegs mem (CF + 254) [Z_to_bv 8 1] /\ bytes_at rsegs mem (CF + 255) [Z_to_bv 8 1].
Proof.
  intros sp mem md HRT.
  destruct HRT as (HAC0 & HSW0 & _ & HCF0 & _ & HREAL0 & _).
  destruct HCF0 as (HGOTCF & _ & _ & _ & _ & _ & HCF240 & _).
  split; [exact HAC0|]. split; [exact HSW0|].
  split; [apply (real_cell_of mem REAL_BCMP BCMP HREAL0); vm_compute; reflexivity|].
  split; [apply (real_cell_of mem REAL_MEMCMP MEMCMP HREAL0); vm_compute; reflexivity|].
  split; [exact HGOTCF|].
  split.
  { pose proof (f31_ba_sub mem (RT_CF + 240) (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 14 1 HCF240
      ltac:(cbn; lia)) as Hs.
    replace (RT_CF + 240 + Z.of_nat 14) with (CF + 254) in Hs by (unfold CF, RT_CF; lia).
    replace (firstn 1 (skipn 14 (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
  { pose proof (f31_ba_sub mem (RT_CF + 240) (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 15 1 HCF240
      ltac:(cbn; lia)) as Hs.
    replace (RT_CF + 240 + Z.of_nat 15) with (CF + 255) in Hs by (unfold CF, RT_CF; lia).
    replace (firstn 1 (skipn 15 (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
Qed.

(* FRA moves across a run that writes only W, where W is apart from the frame, from the low image / shadow
   (below HIGHMEM_BEG) and from everything at or above sp (the spill area [A, A + 448), the saved registers
   [S - 104, S)): the bcmp wrapper's scratch window [sp - 4560, sp). The S-anchored window [S - SLOT_STACK, S) on
   the new memory is the caller's (the callee's stk post below sp, joined with the untouched part above sp). The frame
   location disjunction is kept by the stklo equality (real arm) and the tp word (side arm, read by a_in_fs and by
   the FakeStack-metadata bound, both below HIGHMEM_BEG) and, on the side arm, by FSREC (Tac_slot's fsrec_munch_lo,
   from the premise that W writes nothing below stklo outside the frame body). Tac_slot's sl_stk_run is the same
   move with the spill / selector / saved-register windows named one by one; this one names them all at once by
   `at or above sp`, which is what the single scratch window below sp gives here. *)
Lemma f31_stk_run : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  all_app W -> rt_disjoint W ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
  (forall x, fr <= x < fr + FRAME_BYTES -> Frame.outside W x) ->
  (forall x, 0 <= x < HIGHMEM_BEG -> Frame.outside W x) ->
  (forall x, AC.aspZ regs <= x -> Frame.outside W x) ->
  (forall x, x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
     ~ (fr + 24 <= x < fr + FRAME_BYTES) -> Frame.outside W x) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HAW HD HAH' HSTK HWIN Happ HWframe HWlo HWhi HWfs
    E2 E3 E4 E8 E9 E19 E26.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  pose proof (fra_in_apart B APIf ra g fr hb regs mem md HFRA) as Hinap.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { apply MU. rewrite MState.unsigned_lit by (unfold HIGHMEM_BEG in *; lia).
      apply HWlo. unfold HIGHMEM_BEG in *; lia. }
    unfold mbyte. rewrite Hm. reflexivity. }
  assert (HshIS : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x).
  { intros x Hx.
    assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
    { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
    pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Happ _ Hin)) as His.
    replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
    unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_store sp sp mem mem' md md W HRT MU WM HAW HD)|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo; [lia | rewrite Hthr in Hx; cbn in Hx; lia].
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo; [lia | rewrite Hlock in Hx; cbn in Hx; lia].
    - intros k Hk. rewrite KBlo; [exact (Hohd k Hk) | rewrite Hhead; lia | rewrite Hhead; lia]. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia. }
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E19; exact Hr19|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  split; [exact Hfrm|].
  split; [exact Hs5|].
  split; [exact HAm|].
  split; [exact HAS|].
  split; [exact Hspa|].
  split; [exact Hfa|].
  split; [exact HA448|].
  split; [exact HS4|].
  split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhi. rewrite Haspz. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhi. rewrite Haspz. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr56 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhi. rewrite Haspz. lia. }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split; [|split].
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
        exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
        intros k Hk. rewrite KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + eapply fsrec_munch_lo with (W := W); [exact Hrec | exact HAH | exact MU | exact HWfs]. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWframe. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWframe. lia. }
  split.
  { destruct Hsh as (sh & Hbytes & Hlen). exists sh. split; [|exact Hlen].
    eapply fl_bytes; [exact Hbytes | exact MU |]. rewrite Hlen. intros x Hx.
    change (Z.of_nat (Z.to_nat FRAME_SHADOW)) with FRAME_SHADOW in Hx.
    pose proof (HshIS x ltac:(lia)) as Hin. apply HWlo.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia. }
  split; [exact HWIN|].
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWhi. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. rewrite Haspz. lia. }
  split.
  { intros a Ha. exact (WM (Z_to_bv 64 a) (Herrno a Ha)). }
  split; [intros a Hin; exact (sl_addr_keep mem mem' W a 1 (HAG a Hin) MU HAW)|].
  split; [intros a H1 H2; exact (sl_addr_keep mem mem' W a 1 (HWA a H1 H2) MU HAW)|].
  split; [exact HSHI1|].
  split; [exact HSHI2|].
  split; [exact HSHI3|].
  split; [exact Hhb|]. split; [exact Hlive|].
  (* the input block is app memory below stklo and apart from the frame (fra_in_apart), so outside W *)
  apply (fra_in_keep g mem mem' W Hinb Hinblk MU HAW).
  intros x Hx. destruct (Hinap x Hx) as (_ & Hxlo & Hxfr & _). apply HWfs; [exact Hxlo | lia].
Qed.

Lemma seg_F31 : forall j : nat, Hat B APIf ra (Inv_B82b38_at B APIf ra) j ->
  Hat B APIf ra (Inv_B82b5c_at B APIf ra) j -> Hat B APIf ra (Inv_B82af8_at B APIf ra) j.
Proof.
  intros j H2ad4 H2af8 g c HInv.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HLK & HFTK & H10 &
    Hs144 & Hs264 & Hs216 & HBo & HadL & HadR & Hs184 & Hr25 & Hs192 & Hev & HPT & HTURN & HIFS).
  subst c. rewrite SEGS.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  destruct (fra_app B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA) as (HGT & Hfapp).
  pose proof HPT as (Hr18 & Hr24 & Hr20 & Hs152 & Hs312 & Hphi & Hplen & Hs160 & Hfstk).
  pose proof HFTK as (Hk184 & Hk22 & Hk24 & Hk272 & Hk25).
  pose proof HLK as (Hj255 & Hs240 & HOURb & HFLI).
  pose proof (Tac_ro.fli_mem g fr regs mem HFLI) as (Had & Hstk & Hid & Hfg & HKNT & Hfst).
  destruct (fra_frame B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA) as (Hdisj & _ & _ & _).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HwinB : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (unfold stk in Hwin; destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HAb : 0 <= A /\ A + 448 <= 2 ^ 64) by lia.
  assert (Hfrb : fr + FRAME_BYTES <= APPMEM_END).
  { assert (Ha : app_mem (fr + FRAME_BYTES - 1)) by (apply Hfapp; lia).
    unfold app_mem in Ha. unfold LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha |- *. destruct Ha; lia. }
  assert (Hfr64 : fr + FRAME_BYTES <= 2 ^ 64) by (unfold APPMEM_END in Hfrb; lia).
  assert (Hfr0 : 0 <= fr) by (unfold AC.GT in HGT; lia).
  assert (Q144 : q64 mem (A + 144) (fr + 452)) by (apply (f31_spill regs mem 144 _ A Hs144 Hr9); lia).
  assert (Q264 : q64 mem (A + 264) (fr + 2624)) by (apply (f31_spill regs mem 264 _ A Hs264 Hr9); lia).
  assert (Q216 : q64 mem (A + 216) (fr + 448)) by (apply (f31_spill regs mem 216 _ A Hs216 Hr9); lia).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md HAH) as Hstkhi.
  assert (Hsphi : HIGHMEM_BEG + AF.SLOT_STACK - 4096 < sp) by lia.
  destruct (f31_cls_r (t_cls (g_in g) j)) as [Er|Er]; rewrite Er in H10.
  2: {
    (* classify = None (a0 = -1): bnez a0 at 0x82af8 is taken to 0x82b5c; nothing else changes. *)
    apply (sl_run_lib regs (Z_to_bv 64 0x82af8) mem md
      (fun R0 pc' mem' => pc' = Z_to_bv 64 0x82b5c /\ mem' = mem /\
         getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
         getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
         getr R0 19 = getr regs 19 /\ getr R0 20 = getr regs 20 /\ getr R0 25 = getr regs 25 /\
         getr R0 22 = getr regs 22 /\ getr R0 24 = getr regs 24 /\
         getr R0 26 = getr regs 26 /\ getr R0 27 = getr regs 27)
      (Post B APIf ra g)).
    - exact Hhalt.
    - eapply LE.evt_mono.
      { unfold Regs6ss.mkR_of. apply f31n_evt. unfold rg in H10. exact H10. }
      { intros ms' E. eexists _, _, _. split; [exact E|].
        split; [reflexivity|]. split; [reflexivity|]. repeat split; reflexivity. }
    - intros R0 pc' mem' regs' md'
        (Hpc & Hmem & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E25 & E22 & E24 & E26 & E27) Hreg Hmat.
      subst pc' mem'.
      assert (F9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact E9).
      assert (F27 : rg regs' 27 (-8)) by (unfold rg in *; rewrite Hreg, E27; exact (proj1 HFLI)).
      assert (Ksp : forall off v, 0 <= off <= 336 -> spill regs mem off v -> spill regs' mem off v)
        by (intros off v _ Hs; exact (Tac_ro.spill_reg9 regs regs' mem off v F9 Hs)).
      assert (HIexit : Inv_B82b5c_at B APIf ra g j
                         (mkCfg (mkst regs' (Z_to_bv 64 0x82b5c) mem (seg_rom rsegs)) md')).
      { exists phi, regs', mem, md', fr. rewrite SEGS. split; [reflexivity|].
        split.
        { apply (sl_fra_move B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs regs' mem md md' HFRA);
            rewrite ?Hreg; assumption. }
        split; [eapply ent_mat; [exact HENT | exact Hmat]|].
        split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB|].
        split; [exact (Tac_ro.lk_keep g fr j regs regs' mem mem HLK F27 Had Hstk Hid Hfg HKNT Hfst HOURb Ksp)|].
        split.
        { split; [apply Ksp; [lia | exact Hk184]|].
          split; [unfold rg in *; rewrite Hreg, E22; exact Hk22|].
          split; [unfold rg in *; rewrite Hreg, E24; exact Hk24|].
          split; [apply Ksp; [lia | exact Hk272] | unfold rg in *; rewrite Hreg, E25; exact Hk25]. }
        split.
        { split; [unfold rg in *; rewrite Hreg, E18; exact Hr18|].
          split; [unfold rg in *; rewrite Hreg, E24; exact Hr24|].
          split; [unfold rg in *; rewrite Hreg, E20; exact Hr20|].
          split; [apply Ksp; [lia | exact Hs152]|].
          split; [apply Ksp; [lia | exact Hs312]|].
          split; [exact Hphi|]. split; [exact Hplen|].
          split; [apply Ksp; [lia | exact Hs160]|].
          exact Hfstk. }
        split; [exact (Tac_ro.turn_reg g j phi regs regs' mem F9 HTURN)|].
        exact (Tac_ro.ifs_reg g fr (S j) regs regs' mem F9 HIFS). }
      pose proof (H2af8 g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR. }
  (* classify = Some e (a0 = 0): the source field is 00 40 ab c9 c10 c11; the three checks fall through and the
     bcmp wrapper compares it with our[]. *)
  destruct (f31_cls_some _ Er) as (e & Ecl).
  pose proof (f31_B_src (g_in g) j e Ecl) as Esrc.
  set (c9 := RP.cp_b (t_g (g_in g) j) 9) in *.
  set (c10 := RP.cp_b (t_g (g_in g) j) 10) in *.
  set (c11 := RP.cp_b (t_g (g_in g) j) 11) in *.
  set (lsc := [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; c9; c10; c11]) in *.
  assert (HLs : bytes_at rsegs mem (fr + 448 + 4) lsc).
  { rewrite <- Esrc. change (fr + 448 + 4) with (fr + 448 + Z.of_nat 4).
    apply f31_ba_sub; [exact HBo | rewrite f31_B_length; lia]. }
  destruct (SF.memcmp_model_total lsc (OUR (g_in g)) 6 ltac:(cbn; lia) ltac:(rewrite OUR_length; lia))
    as (v & Hv).
  destruct (f31_mm_spec 6 lsc (OUR (g_in g)) v eq_refl (OUR_length _) Hv) as [Hiff Hvr].
  destruct (bcmp_cells sp mem md HRT) as (HAC0 & HSW0 & HRBc & HRMc & HGC & HC254 & HC255).
  destruct (stk_split rsegs mem (g_S g - AF.SLOT_STACK) sp (g_S g) Hwin ltac:(lia)) as (HSlo & HShi).
  set (W := [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)]).
  apply (sl_run_lib regs (Z_to_bv 64 0x82af8) mem md
    (fun R0 pc' mem' =>
       pc' = Z_to_bv 64 0x82b38 /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 19 = getr regs 19 /\ getr R0 20 = getr regs 20 /\ getr R0 25 = getr regs 25 /\
       getr R0 22 = getr regs 22 /\ getr R0 24 = getr regs 24 /\ getr R0 26 = getr regs 26 /\
       getr R0 27 = getr regs 27 /\
       getr R0 10 = Z_to_bv 64 v /\
       Frame.munch W mem mem' /\ Frame.wmono rsegs mem mem' /\ ro_agree rsegs mem' /\
       stk rsegs mem' (g_S g - AF.SLOT_STACK) (AC.aspZ regs))
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply LE.evt_mono.
    { unfold Regs6ss.mkR_of.
      eapply f31c_evt_ro with (A := A) (O := fr + 448) (R := fr + 2624) (c9 := c9) (c10 := c10) (c11 := c11)
        (rs := OUR (g_in g)) (vcmp := v) (lo := g_S g - AF.SLOT_STACK).
      - unfold rg in Hr9; exact Hr9.
      - unfold rg in H10; exact H10.
      - lia.
      - lia.
      - replace (fr + 448 + 4) with (fr + 452) by lia. exact Q144.
      - exact Q216.
      - exact Q264.
      - exact HLs.
      - exact HOURb.
      - apply OUR_length.
      - exact Hv.
      - exact Hro.
      - replace (fr + 448 + 4) with (fr + 452) by lia. exact HadL.
      - exact HadR.
      - apply Hfapp; lia.
      - apply Hfapp; lia.
      - apply Hfapp; lia.
      - apply Hfapp; lia.
      - assert (HdjL : fr + 448 + 4 + 6 <= AC.aspZ regs - BCMP_WRAP_K \/ AC.aspZ regs <= fr + 448 + 4).
        { destruct (Hdisj BCMP_WRAP_K ltac:(unfold BCMP_WRAP_K, FN_STACK; lia)) as [HD|HD];
            [left | right]; unfold BCMP_WRAP_K in *; lia. }
        exact HdjL.
      - assert (HdjR : fr + 2624 + 6 <= AC.aspZ regs - BCMP_WRAP_K \/ AC.aspZ regs <= fr + 2624).
        { destruct (Hdisj BCMP_WRAP_K ltac:(unfold BCMP_WRAP_K, FN_STACK; lia)) as [HD|HD];
            [left | right]; unfold BCMP_WRAP_K in *; lia. }
        exact HdjR.
      - assert (HstkW : stk rsegs mem (g_S g - AF.SLOT_STACK) (AC.aspZ regs)) by (rewrite Haspz; exact HSlo).
        exact HstkW.
      - assert (HloK : g_S g - AF.SLOT_STACK + BCMP_WRAP_K <= AC.aspZ regs)
          by (rewrite Haspz; unfold BCMP_WRAP_K; lia).
        exact HloK.
      - lia.
      - assert (HspE : AC.aspZ regs <= APPMEM_END) by (rewrite Haspz; lia).
        exact HspE.
      - exact HAC0.
      - exact HSW0.
      - exact HRBc.
      - exact HRMc.
      - exact HGC.
      - exact HC254.
      - exact HC255. }
    { intros ms' (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m'
                  & E & MU & WM & HroM & Hros & ST').
      eexists _, (Z_to_bv 64 0x82b38), m'. split; [exact E|].
      split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [unfold rg in Hr9; rewrite Hr9; reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact HroM|]. exact ST'. }
  - intros R0 pc' mem' regs' md'
      (Hpc & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E25 & E22 & E24 & E26 & E27 & E10 &
       MU & WM & HroM & ST') Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact E2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact E3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact E4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact E8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact E9).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact E18).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact E19).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact E20).
    assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact E25).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact E22).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact E24).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact E26).
    assert (Fr10 : getr regs' 10 = Z_to_bv 64 v) by (rewrite Hreg; exact E10).
    assert (HWlo : forall x, 0 <= x < HIGHMEM_BEG -> Frame.outside W x).
    { intros x Hx. subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2].
      rewrite Haspz in *. unfold BCMP_WRAP_K in *. lia. }
    assert (HWhi : forall x, AC.aspZ regs <= x -> Frame.outside W x).
    { intros x Hx. subst W. cbn [Frame.outside]. split; [|exact I]. lia. }
    assert (HWfr : forall x, fr <= x < fr + FRAME_BYTES -> Frame.outside W x).
    { intros x Hx. subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2].
      destruct (Hdisj BCMP_WRAP_K ltac:(unfold BCMP_WRAP_K, FN_STACK; lia)) as [HD|HD]; lia. }
    assert (Hallapp : all_app W).
    { subst W. cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right.
      rewrite Haspz in *. unfold BCMP_WRAP_K, HIGHMEM_BEG, APPMEM_END in *. lia. }
    assert (HWfs : forall x, x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
                     ~ (fr + 24 <= x < fr + FRAME_BYTES) -> Frame.outside W x).
    { intros x Hx _. destruct (fra_win B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA) as (Hlo & _).
      subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2].
      unfold BCMP_WRAP_K, FN_STACK in *. lia. }
    assert (Hrtdj : rt_disjoint W).
    { subst W. unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
        RT_AGLOB_LEN, AC.GT, BCMP_WRAP_K in *.
      rewrite Haspz in *. unfold HIGHMEM_BEG in *. cbn [disjoint_from].
      repeat split; first [left; lia | exact I]. }
    assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
      ~ AC.a_store_ok (hb1 phi (AC.a_size (flen g j)) ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia. subst W.
      cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2]. apply Hns.
      unfold AC.a_store_ok. right; left. rewrite Haspz in *. unfold BCMP_WRAP_K in *. split; lia. }
    assert (HwmL : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
      by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
    destruct (AC.a_laws_store _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem mem' md HAH HstoreC HwmL)
      as (HAH' & Hown' & HSTKeq & HSTKHIeq).
    assert (HWIN' : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
    { assert (Hhi' : stk rsegs mem' sp (g_S g)).
      { eapply (Frame.stk_transport rsegs W mem mem' sp (g_S g)); [exact HShi | exact MU | exact WM |].
        intros x Hx. left. apply HWhi. rewrite Haspz. lia. }
      assert (Hlo' : stk rsegs mem' (g_S g - AF.SLOT_STACK) sp) by (rewrite <- Haspz; exact ST').
      exact (Frame.stk_merge rsegs mem' (g_S g - AF.SLOT_STACK) sp (g_S g) Hlo' Hhi' ltac:(lia)). }
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem' md)
      by exact (f31_stk_run g fr (hb1 phi (AC.a_size (flen g j))) regs regs' mem mem' md W HFRA MU WM HroM Hallapp
                  Hrtdj HAH' HSTKeq HWIN' Hfapp HWfr HWlo HWhi HWfs Fr2 Fr3 Fr4 Fr8 Fr9 Fr19 Fr26).
    assert (HENT' : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md).
    { eapply ent_store with (W := W) (fr := fr) (regs := regs);
        [ exact HENT | exact HFRA | exact MU | | exact HSTKeq | exact HSTKHIeq
        | intros a Hia Ho; exact (proj2 (Hown' a) Ho) ].
      intros x Hx. destruct (Z_le_gt_dec (AC.aspZ regs - BCMP_WRAP_K) x) as [D1|D1];
        [destruct (Z_lt_ge_dec x (AC.aspZ regs)) as [D2|D2]|].
      - right; left. rewrite Haspz in *. unfold AF.SLOT_STACK, BCMP_WRAP_K in *. lia.
      - left. subst W. cbn [Frame.outside]. split; [lia | exact I].
      - left. subst W. cbn [Frame.outside]. split; [lia | exact I]. }
    assert (HFRA'' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem' md')
      by (apply (sl_fra_move B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' regs' mem' md md' HFRA');
          try reflexivity; exact Hmat).
    assert (Kfr : forall a bs, bytes_at rsegs mem a bs -> fr <= a -> a + Z.of_nat (length bs) <= fr + FRAME_BYTES ->
                    bytes_at rsegs mem' a bs).
    { intros a bs Hb H1 H2. apply (fl_bytes W mem mem' a bs Hb MU). intros x Hx. apply HWfr. lia. }
    assert (Khi : forall a bs, bytes_at rsegs mem a bs -> AC.aspZ regs <= a -> bytes_at rsegs mem' a bs).
    { intros a bs Hb H1. apply (fl_bytes W mem mem' a bs Hb MU). intros x Hx. apply HWhi. lia. }
    (* The spills: the base A is at or above sp, so the wrapper's scratch below sp misses them. *)
    assert (Ksp : forall off w, 0 <= off <= 336 -> spill regs mem off w -> spill regs' mem' off w).
    { intros off w Ho Hs.
      assert (Hq : q64 mem (A + off) w) by (apply (f31_spill regs mem off w A Hs Hr9); lia).
      exists A. split; [unfold rg in *; rewrite Fr9; exact Hr9|].
      unfold q64 in *. apply Khi; [exact Hq | lia]. }
    (* The kind-name table is image data below HIGHMEM_BEG; the scratch window is high app memory. *)
    assert (HKNT' : KNT mem').
    { apply (Tac_ro.knt_munch W mem mem' HKNT MU (munch_meta W mem mem' MU Hallapp)).
      intros x Hx. apply HWlo. unfold KNC.KIND_NAME, HIGHMEM_BEG in *. lia. }
    assert (Hphib : phi + flen g j <= g_S g - AF.SLOT_STACK).
    { assert (Hin : In (phi, AC.a_size (flen g j)) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
        by (apply in_or_app; left; unfold hb1; left; reflexivity).
      destruct (AC.a_laws_blocks _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md phi
        (AC.a_size (flen g j)) HAH Hin) as (_ & _ & Hle & _).
      unfold AC.a_size in Hle. lia. }
    assert (Hphi' : bytes_at rsegs mem' phi (t_phi (g_in g) j)).
    { apply (fl_bytes W mem mem' phi _ Hphi MU). intros x Hx.
      subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2]. rewrite Haspz in *.
      unfold BCMP_WRAP_K in *. lia. }
    assert (Hiff' : getr regs' 10 = Z_to_bv 64 0 <-> firstn 6 (skipn 4 (t_B (g_in g) j)) = OUR (g_in g)).
    { rewrite Fr10, (f31_lit0 v Hvr), Esrc. exact Hiff. }
    assert (HIexit : Inv_B82b38_at B APIf ra g j
                       (mkCfg (mkst regs' (Z_to_bv 64 0x82b38) mem' (seg_rom rsegs)) md')).
    { exists phi, regs', mem', md', fr. rewrite SEGS. split; [reflexivity|].
      split; [exact HFRA''|].
      split; [eapply ent_mat; [exact HENT' | exact Hmat]|].
      split; [exact Hgn|]. split; [exact Hj|].
      split.
      { split; [exact (proj1 HHB)|]. eapply sl_addr_keep; [exact (proj2 HHB) | exact MU | exact Hallapp]. }
      split.
      { eapply Tac_ro.lk_keep; [exact HLK | | | | | | | | | exact Ksp].
        - unfold rg in *. rewrite Hreg, E27. exact (proj1 HFLI).
        - eapply sl_addr_keep; [exact Had | exact MU | exact Hallapp].
        - eapply (Frame.stk_transport rsegs W mem mem' fr (fr + FRAME_BYTES)); [exact Hstk | exact MU | exact WM |].
          intros x Hx. left. apply HWfr. lia.
        - eapply sl_addr_keep; [exact Hid | exact MU | exact Hallapp].
        - eapply sl_addr_keep; [exact Hfg | exact MU | exact Hallapp].
        - exact HKNT'.
        - eapply sl_addr_keep; [exact Hfst | exact MU | exact Hallapp].
        - unfold OURb in *. apply Kfr; [exact HOURb | lia | rewrite OUR_length; lia]. }
      split.
      { split; [apply Ksp; [lia | exact Hk184]|].
        split; [unfold rg in *; rewrite Fr22; exact Hk22|].
        split; [unfold rg in *; rewrite Fr24; exact Hk24|].
        split; [apply Ksp; [lia | exact Hk272] | unfold rg in *; rewrite Fr25; exact Hk25]. }
      split; [rewrite Ecl; discriminate|].
      split; [exact Hiff'|].
      split; [apply Ksp; [lia | exact Hs184]|].
      split; [unfold rg in *; rewrite Fr25; exact Hr25|].
      split; [apply Ksp; [lia | exact Hs192]|].
      split.
      { intros e0 He0. unfold u32 in *. apply Kfr; [exact (Hev e0 He0) | lia | rewrite length_le4; lia]. }
      split.
      { split; [unfold rg in *; rewrite Fr18; exact Hr18|].
        split; [unfold rg in *; rewrite Fr24; exact Hr24|].
        split; [unfold rg in *; rewrite Fr20; exact Hr20|].
        split; [apply Ksp; [lia | exact Hs152]|].
        split; [apply Ksp; [lia | exact Hs312]|].
        split; [exact Hphi'|]. split; [exact Hplen|].
        split; [apply Ksp; [lia | exact Hs160]|].
        eapply (Frame.stk_transport rsegs W mem mem' fr (fr + FRAME_BYTES)); [exact Hfstk | exact MU | exact WM |].
        intros x Hx. left. apply HWfr. lia. }
      split.
      { apply (Tac_ro.turn_keep g j phi regs regs' mem mem' HTURN Ksp). intros _. exact Hphi'. }
      exact (Tac_ro.ifs_munch g fr (S j) regs regs' W mem mem' HIFS MU HWfr
               (sl_addr_keep mem mem' W (fr + 2880) 40 Hfst MU Hallapp)). }
    pose proof (H2ad4 g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

End F31.
