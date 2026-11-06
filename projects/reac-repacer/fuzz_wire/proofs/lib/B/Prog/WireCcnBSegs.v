(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Spec/StrFun.v; 203 of its 237 lines of code are new or changed and 430 lines of the source are left out. *)
(* WireCcnBSegs: the footprint (ExecF.evtF) runs of the straight-line segments of reac-repacer/fuzz_wire's
   check_counter in image B (fuzz_wire.asan-ubsan 0x804c0 = wire_sigma WS_check_counter; objdump of record sha256
   440b9550f4f5), stepped by lib/Lib/StepF.v, in the form of reac-repacer/fuzz_uci's lib/B/Prog/UciCvBSegs.v (recipes
   commit 0295462466b2; its frame-word helpers copied), the shadow checks stepped as in this unit's
   lib/B/Prog/rp_counter_FW.v:
     ccn_short_F  entry, n < 18 -> the return: the 0x20-byte frame (ra, s0, s1 at 24(sp), 16(sp), 8(sp)) written and
                  read back, `bltu a1, a2` (a2 = 18) taken to +0x78;
     ccn_seg1_F   entry, n >= 18 -> the call of rp_counter (`jal` at +0x2c, return address +0x30): the frame, s0 := f,
                  s1 := the shadow base through GOT_CELL_K -> CELL_K, a0 := f;
     ccn_seg2_F   +0x30 -> the return: the UBSan checks of f + 14 / f + 15 (`bltu a1, s0` / `bgeu s0, a1`, a1 = -15,
                  not taken), the shadow checks and loads of f[14] and f[15] (no report call reached), the property
                  test `bne a0, a1` not taken (a0 = rp_counter's result, a1 = f[14] | f[15] << 8), the frame read back,
                  `ret`. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA AsanKAProof WirePSyms WirePAddr.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require rp_counter_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* ---- the cut points (offsets from the entry, read from the pinned image's code) ---- *)
Definition CCN_ENTRY : Z := wire_sigma WS_check_counter.
Definition CCN_AT (off : Z) : Z := CCN_ENTRY + off.
(* the return address of the call of rp_counter (`jal` at +0x2c) *)
Definition CCN_RET : Z := CCN_AT 0x30.
Definition CCN_LEAF : Z := wire_sigma WS_rp_counter.

(* ---- helpers (UciCvBSegs.v cv_le_bytes_to_Z .. cv_rd_all, copied) ---- *)

Lemma ccn_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (byte_range b) as Hb.
  assert (HR : 0 <= bytes_le_to_Z bs). { rewrite bytes_le_to_Z_le_val. apply (proj1 (le_val_range _ (bytes_ok_map bs))). }
  rewrite lor_shiftl8_add by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8)%Z. change (2^8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.div_add, Z.div_small by lia. cbn [Z.add]. exact IH.
Qed.

Lemma ccn_le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z_to_le_bytes_mod by lia.
  rewrite <- L at 1. apply ccn_le_bytes_to_Z.
Qed.

Fixpoint ccn_c8s (n : nat) (bs : list byte) : list cell :=
  match n with
  | O => []
  | S n' => C8 (Z_to_bv 64 (bytes_le_to_Z (firstn 8 bs))) :: ccn_c8s n' (skipn 8 bs)
  end.

Lemma ccn_c8s_spec : forall n bs, length bs = (8 * n)%nat ->
  cells_wf (ccn_c8s n bs) /\ cells_bytes (ccn_c8s n bs) = bs /\ cells_size (ccn_c8s n bs) = (8 * n)%nat.
Proof.
  induction n as [|n IH]; intros bs L.
  - destruct bs; [|cbn in L; lia]. cbn. auto.
  - cbn [ccn_c8s cells_wf cells_bytes cells_size cell_wf cbytes csize].
    assert (L8 : length (firstn 8 bs) = 8%nat) by (rewrite length_firstn; lia).
    assert (LS : length (skipn 8 bs) = (8 * n)%nat) by (rewrite length_skipn; lia).
    destruct (IH _ LS) as (W & B & S).
    split; [split; [exact I | exact W]|]. split; [|lia].
    rewrite ccn_le8_of_bytes, B by exact L8. apply firstn_skipn.
Qed.

Lemma ccn_rw_c8s : forall segs m A n bs, rw_cells segs m A [CB (8 * n) bs] -> rw_cells segs m A (ccn_c8s n bs).
Proof.
  intros segs m A n bs [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [L _].
  destruct (ccn_c8s_spec n bs L) as (W & B & S).
  split; [split|].
  - exact W.
  - rewrite B. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
  - rewrite S. cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw. exact Hw.
Qed.

(* The carved 32 bytes, read as 4 words. *)
Lemma ccn_frame_words : forall m A bs, rw_cells rsegs m A [CB 32 bs] ->
  exists v0 v8 v16 v24 : word, rw_cells rsegs m A [C8 v0; C8 v8; C8 v16; C8 v24].
Proof.
  intros m A bs H. apply (ccn_rw_c8s rsegs m A 4 bs) in H. cbn [ccn_c8s] in H. do 4 eexists. exact H.
Qed.

Lemma ccn_rd_all : forall m A bs, bytes_at rsegs m A bs ->
  ov_read_bytes rsegs m (Z_to_bv 64 A) (length bs) = Some bs.
Proof.
  intros m A bs H. change (Z_to_bv 64 A) with (wa A). replace A with (A + Z.of_nat 0) at 1 by lia.
  rewrite (bytes_at_ov_read rsegs m A bs 0 (length bs) H) by lia. cbn [skipn]. rewrite firstn_all. reflexivity.
Qed.

(* the value `or a1, a2, a1` leaves after `slli a2, a2, 8` of two zero-extended bytes *)
Lemma ccn_lor_bytes16 : forall x y : byte,
  Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned y) 8))) (bv_unsigned x) = bv_unsigned x + 256 * bv_unsigned y.
Proof.
  intros x y. pose proof (byte_range x). pose proof (byte_range y).
  rewrite (unsigned_lit (Z.shiftl (bv_unsigned y) 8)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite Z.lor_comm, lor_shiftl8_add by lia. reflexivity.
Qed.

Ltac ccn_regs := unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end.
Ltac ccn_usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by nia end.
Ltac ccn_w := ccn_usub;
  first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; f_equal; lia
        | f_equal; Z.div_mod_to_equations; nia ].
Ltac ccn_memF k := lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => k mm end.
(* StepF's step reads the start pc: each proof first computes every closed name of its goal to its value. *)
Ltac ccn_lit X := let v := eval vm_compute in X in change X with v.
Ltac ccn_lits :=
  repeat match goal with
  | |- context [CCN_RET] => ccn_lit CCN_RET
  | |- context [CCN_LEAF] => ccn_lit CCN_LEAF
  | |- context [CCN_AT ?o] => ccn_lit (CCN_AT o)
  | |- context [CCN_ENTRY] => ccn_lit CCN_ENTRY
  end.

(* ---- ccn_short_F: entry, n < 18 -> the return ---- *)
Lemma ccn_short_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp ->
    bv_unsigned a1 < 18 ->
    ExecF.rng RNG (bv_unsigned sp - 32) 32 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m1 v0,
         ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp)) gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 18)
                    a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
         rw_cells rsegs m1 (bv_unsigned sp - 32) [C8 v0; C8 s1; C8 s0; C8 ra])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CCN_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ST LO HN RFR.
  ccn_lits.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  destruct (ccn_frame_words _ _ _ FR) as (v0 & v8 & v16 & v24 & FR'). clear FR. rename FR' into FR.
  (* addi sp; sd ra; sd s0; sd s1; li a2, 18; bltu a1, a2 (taken) *)
  do 5 step. step. if_true.
  (* ld ra; ld s0; ld s1; addi sp; ret *)
  do 5 step.
  ccn_memF ltac:(fun mm => apply evtF_done; exists mm, v0).
  replace (bv_unsigned sp - 32) with (bv_unsigned sp + -32) by lia.
  split; [|split; [exact MU|split; [exact WM|exact FR]]].
  f_equal; ccn_regs; try ccn_w.
Qed.

(* ---- ccn_seg1_F: entry, n >= 18 -> rp_counter (ra = CCN_RET) ---- *)
Lemma ccn_seg1_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp ->
    bytes_at rsegs m GOT_CELL_K (le8 (wa CELL_K)) -> bytes_at rsegs m CELL_K (le8 (wa ASAN_K)) ->
    CELL_K + 8 <= bv_unsigned sp - 32 ->
    18 <= bv_unsigned a1 ->
    ExecF.rng RNG (bv_unsigned sp - 32) 32 -> ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m1 v0,
         ms' = MS (mkR (Z_to_bv 64 CCN_RET) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2
                    a0 (Z_to_bv 64 ASAN_K) a0 a1 (Z_to_bv 64 18) a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CCN_LEAF) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
         rw_cells rsegs m1 (bv_unsigned sp - 32) [C8 v0; C8 s1; C8 s0; C8 ra])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CCN_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ST LO GCK CK HLOW HN RFR RGC RCK.
  ccn_lits.
  unfold GOT_CELL_K in RGC, GCK, HLOW. unfold CELL_K in RCK, GCK, CK, HLOW.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  destruct (ccn_frame_words _ _ _ FR) as (v0 & v8 & v16 & v24 & FR'). clear FR. rename FR' into FR.
  (* addi sp; sd ra; sd s0; sd s1; li a2, 18; bltu a1, a2 (not taken); mv s0, a0 *)
  do 5 step. step. if_false. step.
  (* the shadow base through its GOT word: auipc a0; ld a0; ld s1 *)
  unfold ASAN_K in CK.
  pose proof (ccn_rd_all _ _ _ GCK) as RDG. rewrite length_le8 in RDG.
  pose proof (ccn_rd_all _ _ _ CK) as RDS. rewrite length_le8 in RDS.
  do 3 step.
  (* mv a0, s0; jal rp_counter *)
  do 2 step.
  ccn_memF ltac:(fun mm => apply evtF_done; exists mm, v0).
  replace (bv_unsigned sp - 32) with (bv_unsigned sp + -32) by lia.
  split; [|split; [exact MU|split; [exact WM|exact FR]]].
  f_equal; ccn_regs; try ccn_w.
Qed.

(* ---- ccn_seg2_F: CCN_RET -> the return ---- *)
Lemma ccn_seg2_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 fw a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b14 b15 : byte) (v0 c1 c0 cra : word),
    rw_cells rsegs m (bv_unsigned sp) [C8 v0; C8 c1; C8 c0; C8 cra] ->
    bv_unsigned sp + 32 < 2 ^ 64 ->
    addressable m (bv_unsigned fw + 14) 2 ->
    mrd rsegs m (wa (bv_unsigned fw + 14)) = Some b14 ->
    mrd rsegs m (wa (bv_unsigned fw + 15)) = Some b15 ->
    ExecF.rng RNG (bv_unsigned sp) 32 ->
    ExecF.rng RNG (bv_unsigned fw + 14) 2 ->
    ExecF.rng RNG (shadow_addr (bv_unsigned fw + 14))
      (shadow_addr (bv_unsigned fw + 15) - shadow_addr (bv_unsigned fw + 14) + 1) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists a1' a2' a3' : word,
         ms' = MS (mkR cra (Z_to_bv 64 (bv_unsigned sp + 32)) gp tp t0 t1 t2 c0 c1
                    (Z_to_bv 64 (bv_unsigned b14 + 256 * bv_unsigned b15)) a1' a2' a3' a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc cra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 fw (Z_to_bv 64 ASAN_K) (Z_to_bv 64 (bv_unsigned b14 + 256 * bv_unsigned b15))
               a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CCN_RET) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 fw a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    b14 b15 v0 c1 c0 cra FR HSP ADR F14 F15 RFR RBUF RSH.
  ccn_lits.
  pose proof (rw_cells_bound _ _ _ _ FR) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (bv_unsigned_in_range 64 fw) as Rf. unfold bv_modulus in Rf. change (2 ^ Z.of_N 64) with (2^64) in Rf.
  destruct ADR as (P0 & N0 & PE & AB).
  destruct (AB 0 ltac:(lia)) as (APP14 & k14 & MK14 & SK14).
  destruct (AB 1 ltac:(lia)) as (APP15 & k15 & MK15 & SK15).
  unfold shadow_addr, ASAN_K, shadow_ok in *.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in APP14, APP15, PE.
  rewrite Z.add_0_r in APP14, MK14, SK14.
  replace (bv_unsigned fw + 14 + 1) with (bv_unsigned fw + 15) in APP15, MK15, SK15 by lia.
  assert (DV : (bv_unsigned fw + 14) / 8 <= (bv_unsigned fw + 15) / 8) by (apply Z.div_le_mono; lia).
  pose proof (Z.mod_pos_bound (bv_unsigned fw + 14) 8 ltac:(lia)) as MB14.
  pose proof (Z.mod_pos_bound (bv_unsigned fw + 15) 8 ltac:(lia)) as MB15.
  (* the UBSan checks of f: `bltu a1, s0` and `bgeu s0, a1` (a1 = -15) fall through *)
  step. step. if_false. step. if_false.
  (* f + 14: its shadow byte and check *)
  step. gen_addi fw w14 U14.
  step. gen_shr w14 g14 G14. rewrite U14 in G14.
  step. gen_addi g14 h14 H14.
  pose proof (rdw0 m h14 _ _ MK14 ltac:(lia)) as R. step. clear R.
  step.
  destruct SK14 as [C|[C Cu]].
  1: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
  2: rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k14) 0) ltac:(lia)); cbn [negb]; step; step;
     rewrite land7, U14, (lts_low ((bv_unsigned fw + 14) mod 8) k14 MB14), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
  (* f + 15: its shadow byte and check (s0 := f + 15), and the load of f[14] between them *)
  all: step; gen_addi fw w15 U15.
  all: step; gen_shr w15 g15 G15.
  all: rewrite U15 in G15.
  all: step; gen_addi g15 h15 H15.
  all: pose proof (rdw0 m h15 _ _ MK15 ltac:(lia)) as R; step; clear R.
  all: pose proof (rdw0 m w14 _ _ F14 ltac:(lia)) as R; step; clear R.
  all: step.
  all: destruct SK15 as [C'|[C' Cu']].
  1, 3: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C'); cbn [negb].
  all: try (rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k15) 0) ltac:(lia)); cbn [negb]; step; step;
     rewrite land7, U15, (lts_low ((bv_unsigned fw + 15) mod 8) k15 MB15), (proj2 (Z.ltb_lt _ _) C'); cbn [negb]).
  (* f[15]; `slli`, `or`; the property test `bne a0, a1` not taken *)
  all: pose proof (rdw0 m w15 _ _ F15 ltac:(lia)) as R; step; clear R.
  all: do 2 step.
  all: unfold zxb; rewrite !zxb_u, ccn_lor_bytes16.
  all: step; if_false.
  (* ld ra; ld s0; ld s1; addi sp; ret *)
  all: do 5 step; apply evtF_done.
  all: do 3 eexists; reflexivity.
Qed.
