(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Spec/StrFun.v; 203 of its 237 lines of code are new or changed and 430 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/B/Prog/WireCcnBSegs.v, with its numbers changed; 322 of its 392 lines of code are new or changed and 167 lines of the source are left out. *)
(* WireCfBSegs: the footprint (ExecF.evtF) runs of check_forward in image B (fuzz_wire.asan-ubsan 0x7fda4 =
   wire_sigma WS_check_forward), stepped by lib/Lib/StepF.v. The walk lib/B/Prog/check_forward_cgW.v carries them
   into SRr and cuts the one call, rp_fwd_class, by its leaf contract.
     cf_seg1_F  CF_ENTRY -> rp_fwd_class (ra = CF_RET_LEAF): `addi sp, sp, -0x30`, ra and s0 .. s3 saved at
                0x28(sp) .. 0x8(sp), s1 := bcast, s2 := n, s3 := the shadow base through GOT_CELL_K -> CELL_K
                (+0x20 .. +0x28), s0 := f, a1 := n, `jal rp_fwd_class` at +0x34;
     cf_seg2_F  CF_RET_LEAF (a0 = the leaf's result) -> the return. `bltu s2, a1` (a1 = 18) at +0x3c skips every read
                of f when n < 18; past it the five reads of f[12], f[13], f[0] (only when bcast <> 0, `beqz s1` at
                +0x90), f[16], f[17], each after its shadow byte ((a >> 3) + s3, `lb`, `bnez`; the slow check
                `andi` / `blt` returns to the load because the byte is addressable, so no __asan_report_load1 call
                at +0x144 .. +0x184 is reached) and, but for f[0], after UBSan's pointer-overflow check of f + 12,
                f + 13, f + 16, f + 17 (+0x44, +0x6c, +0xd8, +0xfc, to `unimp` at +0x134: f + 18 <= APPMEM_END
                refutes each). The want of the harness reaches a1 (0 at +0xb0, 2 at +0x11c, 1 at +0x124), and is
                lib/Prog/rp_fwd_class_c.v fwd_class_result n bcast of the n bytes on each path, the value a0 holds,
                so `bne a0, a1` at +0xb4 falls through (the abort at +0x12c / +0x130 is never reached); then ra and
                s0 .. s3 are reloaded, sp += 0x30, `ret`.
   cf_seg2_F is cut into the five check sites (cf_site12_F .. cf_site17_F, each from its first instruction to the
   instruction after its `lbu`, in continuation form), the shared tail (cf_tail_F: +0xb4 to the return), the drop
   exit (cf_drop_F: +0xb0) and the f[16] / f[17] classification (cf_audio_F: +0xd4). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA AsanKAProof WirePSyms WirePAddr.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_fwd_class_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Spec Require StrFun.
Import ListNotations.
Open Scope Z_scope.
Module PFC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_fwd_class_c.
Module SF := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Spec.StrFun.

Definition CF_ENTRY : Z := wire_sigma WS_check_forward.
Definition CF_AT (off : Z) : Z := CF_ENTRY + off.
Definition CF_LEAF : Z := wire_sigma WS_rp_fwd_class.
(* The return address of the leaf call (`jal rp_fwd_class` at +0x34). *)
Definition CF_RET_LEAF : Z := CF_AT 0x38.

(* The frame above the 8 unused bytes at 0(sp): the caller's s3, s2, s1, s0, ra at 0x8(sp) .. 0x28(sp) of the
   0x30-byte frame. *)
Definition cf_fr (c3 c2 c1 c0 cra : word) : list cell := [C8 c3; C8 c2; C8 c1; C8 c0; C8 cra].

(* ---- helpers (UciCvBSegs.v:26-123; the little-endian round trip is this unit's lib/Spec/StrFun.v
   Z_to_le_bytes_to_Z) ---- *)

Lemma cf_le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z_to_le_bytes_mod by lia.
  rewrite <- L at 1. apply SF.Z_to_le_bytes_to_Z.
Qed.

Fixpoint cf_c8s (n : nat) (bs : list byte) : list cell :=
  match n with
  | O => []
  | S n' => C8 (Z_to_bv 64 (bytes_le_to_Z (firstn 8 bs))) :: cf_c8s n' (skipn 8 bs)
  end.

Lemma cf_c8s_spec : forall n bs, length bs = (8 * n)%nat ->
  cells_wf (cf_c8s n bs) /\ cells_bytes (cf_c8s n bs) = bs /\ cells_size (cf_c8s n bs) = (8 * n)%nat.
Proof.
  induction n as [|n IH]; intros bs L.
  - destruct bs; [|cbn in L; lia]. cbn. auto.
  - cbn [cf_c8s cells_wf cells_bytes cells_size cell_wf cbytes csize].
    assert (L8 : length (firstn 8 bs) = 8%nat) by (rewrite length_firstn; lia).
    assert (LS : length (skipn 8 bs) = (8 * n)%nat) by (rewrite length_skipn; lia).
    destruct (IH _ LS) as (W & B & S).
    split; [split; [exact I | exact W]|]. split; [|lia].
    rewrite cf_le8_of_bytes, B by exact L8. apply firstn_skipn.
Qed.

Lemma cf_rw_c8s : forall segs m A n bs, rw_cells segs m A [CB (8 * n) bs] -> rw_cells segs m A (cf_c8s n bs).
Proof.
  intros segs m A n bs [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [L _].
  destruct (cf_c8s_spec n bs L) as (W & B & S).
  split; [split|].
  - exact W.
  - rewrite B. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
  - rewrite S. cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw. exact Hw.
Qed.

(* The carved 48 bytes, read as 6 words. *)
Lemma cf_frame_words : forall m A bs, rw_cells rsegs m A [CB 48 bs] ->
  exists v0 v8 v16 v24 v32 v40 : word,
    rw_cells rsegs m A [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40].
Proof.
  intros m A bs H. apply (cf_rw_c8s rsegs m A 6 bs) in H. cbn [cf_c8s] in H. do 6 eexists. exact H.
Qed.

Lemma cf_rd_all : forall m A bs, bytes_at rsegs m A bs ->
  ov_read_bytes rsegs m (Z_to_bv 64 A) (length bs) = Some bs.
Proof.
  intros m A bs H. change (Z_to_bv 64 A) with (wa A). replace A with (A + Z.of_nat 0) at 1 by lia.
  rewrite (bytes_at_ov_read rsegs m A bs 0 (length bs) H) by lia. cbn [skipn]. rewrite firstn_all. reflexivity.
Qed.

Ltac cf_regs := unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end.
Ltac cf_usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by nia end.
Ltac cf_shift := rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia.
Ltac cf_w := cf_shift; cf_usub; cf_shift; cf_usub;
  first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; f_equal; lia
        | f_equal; Z.div_mod_to_equations; nia ].
Ltac cf_memF k := lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => k mm end.
(* StepF's step reads the start pc: every pc here is a name of this file, so each proof first computes each such
   closed name of its goal to its value. *)
Ltac cf_lit X := let v := eval vm_compute in X in change X with v.
Ltac cf_lits :=
  repeat match goal with
  | |- context [CF_RET_LEAF] => cf_lit CF_RET_LEAF
  | |- context [CF_LEAF] => cf_lit CF_LEAF
  | |- context [CF_AT ?o] => cf_lit (CF_AT o)
  | |- context [CF_ENTRY] => cf_lit CF_ENTRY
  end.

(* ---- cf_seg1_F: CF_ENTRY -> rp_fwd_class (ra = CF_RET_LEAF) ---- *)
Lemma cf_seg1_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n bc lo : Z),
    0 <= f < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= bc < 2 ^ 64 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp ->
    bytes_at rsegs m GOT_CELL_K (le8 (wa CELL_K)) -> bytes_at rsegs m CELL_K (le8 (wa ASAN_K)) ->
    CELL_K + 8 <= bv_unsigned sp - 48 ->
    ExecF.rng RNG (bv_unsigned sp - 48) 48 -> ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m1 v0,
         ms' = MS (mkR (Z_to_bv 64 CF_RET_LEAF) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2
                    (Z_to_bv 64 f) (Z_to_bv 64 bc) (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 bc) a3 a4 a5 a6 a7
                    (Z_to_bv 64 n) (Z_to_bv 64 ASAN_K) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CF_LEAF) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
         rw_cells rsegs m1 (bv_unsigned sp - 48) (C8 v0 :: cf_fr s3 s2 s1 s0 ra))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 bc) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CF_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f n bc lo
    HF HN HB ST LO GCK CK HLOW RFR RGC RCK.
  cf_lits.
  unfold GOT_CELL_K in RGC, GCK, HLOW. unfold CELL_K in RCK, GCK, CK, HLOW.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  destruct (cf_frame_words _ _ _ FR) as (v0 & v8 & v16 & v24 & v32 & v40 & FR'). clear FR.
  rename FR' into FR.
  do 9 step.
  (* the stores moved the two cell facts to the new memory (StepF's store transport) *)
  unfold ASAN_K in CK.
  pose proof (cf_rd_all _ _ _ GCK) as RDG. rewrite length_le8 in RDG.
  pose proof (cf_rd_all _ _ _ CK) as RDS. rewrite length_le8 in RDS.
  do 5 step.
  cf_memF ltac:(fun mm => apply evtF_done; exists mm, v0).
  replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia.
  split; [|split; [exact MU|split; [exact WM|exact FR]]].
  f_equal; cf_regs; try cf_w.
Qed.

(* ---- cf_seg2_F and its pieces: CF_RET_LEAF -> the return ---- *)
Section Seg2.
Variables (RNG : ExecF.footprint)
  (ra sp gp tp t0 t1 t2 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v0 c3 c2 c1 c0 cra : word).
Hypothesis FR : rw_cells rsegs m (bv_unsigned sp) (C8 v0 :: cf_fr c3 c2 c1 c0 cra).
Hypothesis RFR : ExecF.rng RNG (bv_unsigned sp) 48.

(* The state of the walk at pc: the registers check_forward changes are arguments, the others the Section's. *)
Definition cf_ms (pc : Z) (s0 s1 a0 a1 a2 a3 s2 s3 : word) : machine_state :=
  MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom rsegs).

(* The return: ra and s0 .. s3 reloaded from the frame, sp back up, a0 kept; a1 .. a3 are clobbered. *)
Definition cf_post (a0 : word) : machine_state -> Prop :=
  fun ms' => exists a1' a2' a3' : word,
    ms' = MS (mkR cra (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0 t1 t2 c0 c1 a0 a1' a2' a3' a4 a5 a6 a7
               c2 c3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc cra) fc None m (seg_rom rsegs).

(* +0xb4 `bne a0, a1` (a1 = a0: falls through), the five reloads, `addi sp, sp, 0x30`, `ret`. *)
Lemma cf_tail_F : forall (s0 s1 a0 a1 a2 a3 s2 s3 : word),
  a1 = a0 -> ExecF.evtF rsegs RNG (cf_post a0) (cf_ms (CF_AT 0xb4) s0 s1 a0 a1 a2 a3 s2 s3).
Proof.
  intros s0 s1 a0 a1 a2 a3 s2 s3 ->. unfold cf_ms. cf_lits.
  pose proof FR as FR0. unfold cf_fr in FR0.
  pose proof (rw_cells_bound _ _ _ _ FR0) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  step. if_false.
  do 7 step.
  apply evtF_done. unfold cf_post. exists a0, a2, a3. f_equal.
Qed.

(* +0xb0 `addi a1, zero, 0` (the want RP_FWD_DROP), then the tail. *)
Lemma cf_drop_F : forall (s0 s1 a0 a1 a2 a3 s2 s3 : word),
  a0 = Z_to_bv 64 0 -> ExecF.evtF rsegs RNG (cf_post a0) (cf_ms (CF_AT 0xb0) s0 s1 a0 a1 a2 a3 s2 s3).
Proof.
  intros s0 s1 a0 a1 a2 a3 s2 s3 ->. unfold cf_ms. cf_lits.
  step.
  eapply cf_tail_F. apply bv_eq. reflexivity.
Qed.

(* The f + 12 site, +0x40 .. +0x5c: UBSan's `bgeu s0, a1` (a1 = -12), the shadow byte k of f + 12 and its check,
   `lbu a1, 0(a1)`; it continues at +0x60 with a1 = the byte b. *)
Lemma cf_site12_F : forall (Q : machine_state -> Prop) (s0 s1 a0 a1 a2 a3 s2 s3 : word) (k b : byte),
  s3 = Z_to_bv 64 ASAN_K -> bv_unsigned s0 + 18 <= 2 ^ 64 ->
  mrd rsegs m (wa (shadow_addr (bv_unsigned s0 + 12))) = Some k -> shadow_ok (bv_unsigned s0 + 12) (bv_signed k) ->
  mrd rsegs m (wa (bv_unsigned s0 + 12)) = Some b ->
  ExecF.rng RNG (shadow_addr (bv_unsigned s0 + 12)) 1 -> ExecF.rng RNG (bv_unsigned s0 + 12) 1 ->
  (forall a2' a3' : word, ExecF.evtF rsegs RNG Q (cf_ms (CF_AT 0x60) s0 s1 a0 (zxb b) a2' a3' s2 s3)) ->
  ExecF.evtF rsegs RNG Q (cf_ms (CF_AT 0x40) s0 s1 a0 a1 a2 a3 s2 s3).
Proof.
  intros Q s0 s1 a0 a1 a2 a3 s2 s3 k b -> HF MK SK MB RS RB K.
  unfold cf_ms. cf_lits.
  unfold shadow_addr, ASAN_K, shadow_ok in *.
  pose proof (zr_word s0) as Rs0. unfold inr64 in Rs0.
  pose proof (Z.mod_pos_bound (bv_unsigned s0 + 12) 8 ltac:(lia)) as MB8.
  step. step. if_false.
  step. gen_addi s0 w U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 m h _ _ MK ltac:(lia)) as R. step. clear R.
  step.
  destruct SK as [C|[C Cu]].
  1: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
  2: rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb]; step; step;
     rewrite land7, U, (lts_low ((bv_unsigned s0 + 12) mod 8) k MB8), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
  all: pose proof (rdw0 m w _ _ MB ltac:(lia)) as R; step; clear R.
  all: apply K.
Qed.

(* The f + 13 site, +0x68 .. +0x84: UBSan's `bltu a1, s0` (a1 = -14), the shadow check of f + 13, `lbu a1, 0(a1)`;
   it continues at +0x88. *)
Lemma cf_site13_F : forall (Q : machine_state -> Prop) (s0 s1 a0 a1 a2 a3 s2 s3 : word) (k b : byte),
  s3 = Z_to_bv 64 ASAN_K -> bv_unsigned s0 + 18 <= 2 ^ 64 ->
  mrd rsegs m (wa (shadow_addr (bv_unsigned s0 + 13))) = Some k -> shadow_ok (bv_unsigned s0 + 13) (bv_signed k) ->
  mrd rsegs m (wa (bv_unsigned s0 + 13)) = Some b ->
  ExecF.rng RNG (shadow_addr (bv_unsigned s0 + 13)) 1 -> ExecF.rng RNG (bv_unsigned s0 + 13) 1 ->
  (forall a2' a3' : word, ExecF.evtF rsegs RNG Q (cf_ms (CF_AT 0x88) s0 s1 a0 (zxb b) a2' a3' s2 s3)) ->
  ExecF.evtF rsegs RNG Q (cf_ms (CF_AT 0x68) s0 s1 a0 a1 a2 a3 s2 s3).
Proof.
  intros Q s0 s1 a0 a1 a2 a3 s2 s3 k b -> HF MK SK MB RS RB K.
  unfold cf_ms. cf_lits.
  unfold shadow_addr, ASAN_K, shadow_ok in *.
  pose proof (zr_word s0) as Rs0. unfold inr64 in Rs0.
  pose proof (Z.mod_pos_bound (bv_unsigned s0 + 13) 8 ltac:(lia)) as MB8.
  step. step. if_false.
  step. gen_addi s0 w U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 m h _ _ MK ltac:(lia)) as R. step. clear R.
  step.
  destruct SK as [C|[C Cu]].
  1: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
  2: rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb]; step; step;
     rewrite land7, U, (lts_low ((bv_unsigned s0 + 13) mod 8) k MB8), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
  all: pose proof (rdw0 m w _ _ MB ltac:(lia)) as R; step; clear R.
  all: apply K.
Qed.

(* The f[0] site, +0x94 .. +0xa4 (no UBSan check): the shadow check of f, `lbu a1, 0(s0)`; it continues at +0xa8. *)
Lemma cf_site0_F : forall (Q : machine_state -> Prop) (s0 s1 a0 a1 a2 a3 s2 s3 : word) (k b : byte),
  s3 = Z_to_bv 64 ASAN_K -> bv_unsigned s0 + 18 <= 2 ^ 64 ->
  mrd rsegs m (wa (shadow_addr (bv_unsigned s0))) = Some k -> shadow_ok (bv_unsigned s0) (bv_signed k) ->
  mrd rsegs m (wa (bv_unsigned s0)) = Some b ->
  ExecF.rng RNG (shadow_addr (bv_unsigned s0)) 1 -> ExecF.rng RNG (bv_unsigned s0) 1 ->
  (forall a2' : word, ExecF.evtF rsegs RNG Q (cf_ms (CF_AT 0xa8) s0 s1 a0 (zxb b) a2' a3 s2 s3)) ->
  ExecF.evtF rsegs RNG Q (cf_ms (CF_AT 0x94) s0 s1 a0 a1 a2 a3 s2 s3).
Proof.
  intros Q s0 s1 a0 a1 a2 a3 s2 s3 k b -> HF MK SK MB RS RB K.
  unfold cf_ms. cf_lits.
  unfold shadow_addr, ASAN_K, shadow_ok in *.
  pose proof (zr_word s0) as Rs0. unfold inr64 in Rs0.
  pose proof (Z.mod_pos_bound (bv_unsigned s0) 8 ltac:(lia)) as MB8.
  step. gen_shr s0 g G.
  step. gen_addi g h H.
  pose proof (rdw0 m h _ _ MK ltac:(lia)) as R. step. clear R.
  step.
  destruct SK as [C|[C Cu]].
  1: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
  2: rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb]; step; step;
     rewrite land7, (lts_low ((bv_unsigned s0) mod 8) k MB8), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
  all: pose proof (rdw0 m s0 _ _ MB ltac:(lia)) as R; step; clear R.
  all: apply K.
Qed.

(* The f + 16 site, +0xd4 .. +0xf0: UBSan's `bgeu s0, a1` (a1 = -16), the shadow check of f + 16, `lbu a1, 0(a1)`;
   it continues at +0xf4. *)
Lemma cf_site16_F : forall (Q : machine_state -> Prop) (s0 s1 a0 a1 a2 a3 s2 s3 : word) (k b : byte),
  s3 = Z_to_bv 64 ASAN_K -> bv_unsigned s0 + 18 <= 2 ^ 64 ->
  mrd rsegs m (wa (shadow_addr (bv_unsigned s0 + 16))) = Some k -> shadow_ok (bv_unsigned s0 + 16) (bv_signed k) ->
  mrd rsegs m (wa (bv_unsigned s0 + 16)) = Some b ->
  ExecF.rng RNG (shadow_addr (bv_unsigned s0 + 16)) 1 -> ExecF.rng RNG (bv_unsigned s0 + 16) 1 ->
  (forall a2' a3' : word, ExecF.evtF rsegs RNG Q (cf_ms (CF_AT 0xf4) s0 s1 a0 (zxb b) a2' a3' s2 s3)) ->
  ExecF.evtF rsegs RNG Q (cf_ms (CF_AT 0xd4) s0 s1 a0 a1 a2 a3 s2 s3).
Proof.
  intros Q s0 s1 a0 a1 a2 a3 s2 s3 k b -> HF MK SK MB RS RB K.
  unfold cf_ms. cf_lits.
  unfold shadow_addr, ASAN_K, shadow_ok in *.
  pose proof (zr_word s0) as Rs0. unfold inr64 in Rs0.
  pose proof (Z.mod_pos_bound (bv_unsigned s0 + 16) 8 ltac:(lia)) as MB8.
  step. step. if_false.
  step. gen_addi s0 w U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 m h _ _ MK ltac:(lia)) as R. step. clear R.
  step.
  destruct SK as [C|[C Cu]].
  1: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
  2: rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb]; step; step;
     rewrite land7, U, (lts_low ((bv_unsigned s0 + 16) mod 8) k MB8), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
  all: pose proof (rdw0 m w _ _ MB ltac:(lia)) as R; step; clear R.
  all: apply K.
Qed.

(* The f + 17 site, +0xf8 .. +0x114: UBSan's `bltu a1, s0` (a1 = -18), `addi s0, s0, 17`, the shadow check of
   f + 17, `lbu a1, 0(s0)`; it continues at +0x118 (s0 = f + 17 there; the epilogue reloads it). *)
Lemma cf_site17_F : forall (Q : machine_state -> Prop) (s0 s1 a0 a1 a2 a3 s2 s3 : word) (k b : byte),
  s3 = Z_to_bv 64 ASAN_K -> bv_unsigned s0 + 18 <= 2 ^ 64 ->
  mrd rsegs m (wa (shadow_addr (bv_unsigned s0 + 17))) = Some k -> shadow_ok (bv_unsigned s0 + 17) (bv_signed k) ->
  mrd rsegs m (wa (bv_unsigned s0 + 17)) = Some b ->
  ExecF.rng RNG (shadow_addr (bv_unsigned s0 + 17)) 1 -> ExecF.rng RNG (bv_unsigned s0 + 17) 1 ->
  (forall s0' a2' : word, ExecF.evtF rsegs RNG Q (cf_ms (CF_AT 0x118) s0' s1 a0 (zxb b) a2' a3 s2 s3)) ->
  ExecF.evtF rsegs RNG Q (cf_ms (CF_AT 0xf8) s0 s1 a0 a1 a2 a3 s2 s3).
Proof.
  intros Q s0 s1 a0 a1 a2 a3 s2 s3 k b -> HF MK SK MB RS RB K.
  unfold cf_ms. cf_lits.
  unfold shadow_addr, ASAN_K, shadow_ok in *.
  pose proof (zr_word s0) as Rs0. unfold inr64 in Rs0.
  pose proof (Z.mod_pos_bound (bv_unsigned s0 + 17) 8 ltac:(lia)) as MB8.
  step. step. if_false.
  step. gen_addi s0 w U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 m h _ _ MK ltac:(lia)) as R. step. clear R.
  step.
  destruct SK as [C|[C Cu]].
  1: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
  2: rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb]; step; step;
     rewrite land7, U, (lts_low ((bv_unsigned s0 + 17) mod 8) k MB8), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
  all: pose proof (rdw0 m w _ _ MB ltac:(lia)) as R; step; clear R.
  all: apply K.
Qed.

(* Each test of fwd_class_result a path fixed (the released UBSan walk's eqb_facts / fwd_eval). *)
Ltac cf_eqb_facts := repeat match goal with
  | |- context [Z.eqb ?x ?c] =>
      first [ rewrite (proj2 (Z.eqb_eq x c)) by lia | rewrite (proj2 (Z.eqb_neq x c)) by lia ]
  end.
Ltac cf_model := unfold PFC.fwd_class_result, PFC.fwd_byte;
  first [ rewrite (proj2 (Z.ltb_lt _ _)) by lia | rewrite (proj2 (Z.ltb_ge _ _)) by lia ];
  cf_eqb_facts; cbn [andb orb negb].
Ltac byte_cond H := zify_cond H; rewrite ?zxb_u in H.

(* +0xd4 .. : is_audio (f) ? RP_FWD_AUDIO : RP_FWD_CTRL, from the f + 16 site to the tail (a1 = 2 at +0x11c,
   a1 = 1 at +0x124, each `j` +0xb4). *)
Lemma cf_audio_F : forall (s0 s1 a0 a1 a2 a3 s2 s3 : word) (k16 b16 k17 b17 : byte),
  s3 = Z_to_bv 64 ASAN_K -> bv_unsigned s0 + 18 <= 2 ^ 64 ->
  mrd rsegs m (wa (shadow_addr (bv_unsigned s0 + 16))) = Some k16 -> shadow_ok (bv_unsigned s0 + 16) (bv_signed k16) ->
  mrd rsegs m (wa (bv_unsigned s0 + 16)) = Some b16 ->
  ExecF.rng RNG (shadow_addr (bv_unsigned s0 + 16)) 1 -> ExecF.rng RNG (bv_unsigned s0 + 16) 1 ->
  mrd rsegs m (wa (shadow_addr (bv_unsigned s0 + 17))) = Some k17 -> shadow_ok (bv_unsigned s0 + 17) (bv_signed k17) ->
  mrd rsegs m (wa (bv_unsigned s0 + 17)) = Some b17 ->
  ExecF.rng RNG (shadow_addr (bv_unsigned s0 + 17)) 1 -> ExecF.rng RNG (bv_unsigned s0 + 17) 1 ->
  a0 = Z_to_bv 64 (if (bv_unsigned b16 =? 0) && (bv_unsigned b17 =? 0) then 1 else 2) ->
  ExecF.evtF rsegs RNG (cf_post a0) (cf_ms (CF_AT 0xd4) s0 s1 a0 a1 a2 a3 s2 s3).
Proof.
  intros s0 s1 a0 a1 a2 a3 s2 s3 k16 b16 k17 b17 E3 HF MK16 SK16 MB16 RS16 RB16 MK17 SK17 MB17 RS17 RB17 EA.
  eapply (cf_site16_F _ s0 s1 a0 a1 a2 a3 s2 s3 k16 b16 E3 HF MK16 SK16 MB16 RS16 RB16).
  intros a2' a3'. unfold cf_ms. cf_lits.
  step. if_cases H16.
  - (* f[16] <> 0: RP_FWD_CTRL *)
    byte_cond H16. do 2 step.
    eapply cf_tail_F. rewrite EA, (proj2 (Z.eqb_neq _ _) H16). cbn [andb]. apply bv_eq. reflexivity.
  - byte_cond H16.
    eapply (cf_site17_F _ s0 s1 a0 _ _ _ s2 s3 k17 b17 E3 HF MK17 SK17 MB17 RS17 RB17).
    intros s0' a2''. unfold cf_ms. cf_lits.
    step. if_cases H17.
    + (* f[17] = 0: RP_FWD_AUDIO *)
      byte_cond H17. do 2 step.
      eapply cf_tail_F. rewrite EA, (proj2 (Z.eqb_eq _ _) H16), (proj2 (Z.eqb_eq _ _) H17). cbn [andb].
      apply bv_eq. reflexivity.
    + (* f[17] <> 0: RP_FWD_CTRL *)
      byte_cond H17. do 2 step.
      eapply cf_tail_F. rewrite EA, (proj2 (Z.eqb_eq _ _) H16), (proj2 (Z.eqb_neq _ _) H17). cbn [andb].
      apply bv_eq. reflexivity.
Qed.

(* ---- cf_seg2_F: CF_RET_LEAF (a0 = the leaf's result) -> the return ---- *)
Lemma cf_seg2_F : forall (s0 s1 a0 a1 a2 a3 s2 s3 : word) (bs : list byte),
  s3 = Z_to_bv 64 ASAN_K ->
  a0 = Z_to_bv 64 (PFC.fwd_class_result (bv_unsigned s2) (bv_unsigned s1) bs) ->
  (18 <= bv_unsigned s2 ->
     (18 <= length bs)%nat /\ bytes_at rsegs m (bv_unsigned s0) bs /\ addressable m (bv_unsigned s0) 18 /\
     ExecF.rng RNG (bv_unsigned s0) 18 /\
     ExecF.rng RNG (shadow_addr (bv_unsigned s0)) (shadow_addr (bv_unsigned s0 + 17) - shadow_addr (bv_unsigned s0) + 1)) ->
  ExecF.evtF rsegs RNG (cf_post a0) (cf_ms CF_RET_LEAF s0 s1 a0 a1 a2 a3 s2 s3).
Proof.
  intros s0 s1 a0 a1 a2 a3 s2 s3 bs E3 EA HBUF.
  pose proof (zr_word s0) as Rs0. unfold inr64 in Rs0.
  pose proof (zr_word s1) as Rs1. unfold inr64 in Rs1.
  pose proof (zr_word s2) as Rs2. unfold inr64 in Rs2.
  unfold cf_ms. cf_lits.
  step. step. if_cases HL.
  - (* n < 18: RP_FWD_DROP before any read of f *)
    zify_cond HL.
    eapply cf_drop_F. rewrite EA. cf_model. reflexivity.
  - zify_cond HL.
    destruct (HBUF ltac:(lia)) as (LEN & BA & ADR & RB & RSH).
    destruct ADR as (P0 & N0 & PE & AB).
    assert (HF : bv_unsigned s0 + 18 <= 2 ^ 64) by (unfold APPMEM_END in PE; lia).
    (* the five bytes and their shadow bytes *)
    destruct (AB 0 ltac:(lia)) as (_ & k0 & MK0 & SK0). rewrite Z.add_0_r in MK0, SK0.
    destruct (AB 12 ltac:(lia)) as (_ & k12 & MK12 & SK12).
    destruct (AB 13 ltac:(lia)) as (_ & k13 & MK13 & SK13).
    destruct (AB 16 ltac:(lia)) as (_ & k16 & MK16 & SK16).
    destruct (AB 17 ltac:(lia)) as (_ & k17 & MK17 & SK17).
    pose proof (bytes_nth m _ bs 0 BA ltac:(lia)) as B0. change (Z.of_nat 0) with 0 in B0. rewrite Z.add_0_r in B0.
    pose proof (bytes_nth m _ bs 12 BA ltac:(lia)) as B12. change (Z.of_nat 12) with 12 in B12.
    pose proof (bytes_nth m _ bs 13 BA ltac:(lia)) as B13. change (Z.of_nat 13) with 13 in B13.
    pose proof (bytes_nth m _ bs 16 BA ltac:(lia)) as B16. change (Z.of_nat 16) with 16 in B16.
    pose proof (bytes_nth m _ bs 17 BA ltac:(lia)) as B17. change (Z.of_nat 17) with 17 in B17.
    (* each access inside the footprint of the 18 bytes and of their shadow *)
    assert (SH : forall i, 0 <= i < 18 ->
      ExecF.rng RNG (shadow_addr (bv_unsigned s0 + i)) 1 /\ ExecF.rng RNG (bv_unsigned s0 + i) 1).
    { intros i Hi. split; [|apply (rng_sub _ _ _ _ _ RB); lia].
      apply (rng_sub _ _ _ _ _ RSH); unfold shadow_addr.
      - pose proof (Z.div_le_mono (bv_unsigned s0) (bv_unsigned s0 + i) 8 ltac:(lia) ltac:(lia)). lia.
      - pose proof (Z.div_le_mono (bv_unsigned s0 + i) (bv_unsigned s0 + 17) 8 ltac:(lia) ltac:(lia)). lia. }
    destruct (SH 0 ltac:(lia)) as [RS0 RB0]. rewrite Z.add_0_r in RS0, RB0.
    destruct (SH 12 ltac:(lia)) as [RS12 RB12].
    destruct (SH 13 ltac:(lia)) as [RS13 RB13].
    destruct (SH 16 ltac:(lia)) as [RS16 RB16].
    destruct (SH 17 ltac:(lia)) as [RS17 RB17].
    eapply (cf_site12_F _ s0 s1 a0 _ a2 a3 s2 s3 k12 _ E3 HF MK12 SK12 B12 RS12 RB12).
    intros a2' a3'. unfold cf_ms. cf_lits.
    step. step. if_cases H12.
    + (* f[12] <> 0x88: RP_FWD_DROP *)
      byte_cond H12. eapply cf_drop_F. rewrite EA. cf_model. reflexivity.
    + byte_cond H12.
      eapply (cf_site13_F _ s0 s1 a0 _ _ _ s2 s3 k13 _ E3 HF MK13 SK13 B13 RS13 RB13).
      intros a2'' a3''. unfold cf_ms. cf_lits.
      step. step. if_cases H13.
      * (* f[13] <> 0x19: RP_FWD_DROP *)
        byte_cond H13. eapply cf_drop_F. rewrite EA. cf_model. reflexivity.
      * byte_cond H13.
        step. if_cases HB.
        -- (* bcast = 0 *)
           zify_cond HB.
           eapply (cf_audio_F s0 s1 a0 _ _ _ s2 s3 k16 _ k17 _ E3 HF MK16 SK16 B16 RS16 RB16 MK17 SK17 B17 RS17 RB17).
           rewrite EA. cf_model. reflexivity.
        -- zify_cond HB.
           eapply (cf_site0_F _ s0 s1 a0 _ _ _ s2 s3 k0 _ E3 HF MK0 SK0 B0 RS0 RB0).
           intros a2'''. unfold cf_ms. cf_lits.
           step. step. if_cases H0.
           ++ (* f[0] = 0xff *)
              byte_cond H0.
              eapply (cf_audio_F s0 s1 a0 _ _ _ s2 s3 k16 _ k17 _ E3 HF MK16 SK16 B16 RS16 RB16 MK17 SK17 B17 RS17 RB17).
              rewrite EA. cf_model. reflexivity.
           ++ (* bcast and f[0] <> 0xff: RP_FWD_DROP *)
              byte_cond H0. eapply cf_drop_F. rewrite EA. cf_model. reflexivity.
Qed.

End Seg2.
