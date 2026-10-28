(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ITree Nodes Decode SysStep ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import FX_Layout.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.simdjson.fuzz_implementations.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope Z_scope.

Notation bsegs := ImageA.bsegs.
Notation mem := (word -> option byte).
Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.

Definition F_OFLUSH : Z := 0x120980.
Definition OFLUSH_SYNC_RA : Z := 0x1209d8.

Section OFlush.

  Variables (O VO VOFF SB VSB SYNC lo : Z).

  Definition ostream_cells (m : mem) (ff : byte) : Prop :=
    rw_cells bsegs m O [C8 (Z_to_bv 64 VO)]
    /\ rw_cells bsegs m (VO + -24) [C8 (Z_to_bv 64 VOFF)]
    /\ rw_cells bsegs m (O + VOFF + 9) [C1 ff]
    /\ rw_cells bsegs m (O + VOFF + 32) [C4 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m (O + VOFF + 40) [C8 (Z_to_bv 64 SB)]
    /\ rw_cells bsegs m (O + VOFF + 136) [C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m SB [C8 (Z_to_bv 64 VSB)]
    /\ rw_cells bsegs m (VSB + 48) [C8 (Z_to_bv 64 SYNC)].
  Definition ostream_ok (ff : byte) : Prop :=
    Z.land (bv_unsigned ff) 32 = 0 /\ (0 < O) /\ (O + VOFF + 144 <= lo) /\ (0 <= VOFF < 2^16) /\ (24 <= VO) /\ (VO <= lo) /\ (0 < SB) /\ (SB + 8 <= lo)
    /\ (0 <= VSB) /\ (VSB + 56 <= lo) /\ (0 <= SYNC < 2^47) /\ (SYNC mod 2 = 0).

  Definition oflush_frame (j0 j1 : list byte) (s1 s0 ra : word) : list cell :=
    [CB 8 j0; C1 (Z_to_bv 8 1); CB 7 j1; C8 (Z_to_bv 64 O); C8 s1; C8 s0; C8 ra].

  Definition oflush_seg1_post (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0 : word) (F : bvmap 5 word) (fc : bv 32) (ff : byte) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j0 j1 : list byte) (m' : mem),
      ms' = MS (mkR (Z_to_bv 64 OFLUSH_SYNC_RA) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 O) s1 (Z_to_bv 64 SB) (Z_to_bv 64 SYNC) a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 SYNC) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp + -48)
      /\ rw_cells bsegs m' (bv_unsigned sp + -48) (oflush_frame j0 j1 s1 s0 ra)
      /\ ostream_cells m' ff.

  Lemma oflush_seg1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ff : byte),
    stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 48) -> (GLOBALS_TOP <= lo) ->
    ostream_cells m ff -> ostream_ok ff ->
    mem_inv bsegs m ->
    evt bsegs (oflush_seg1_post ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0 F fc ff m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 O) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 F_OFLUSH) fc None m (seg_rom bsegs)).
  Proof.
    intros until ff. intros ST LO GLO (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8) (UB & O0 & OB & VB & VO24 & VOH & SB0 & SBB & VSB0 & VSBH & SY & SYE) MI.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold F_OFLUSH, OFLUSH_SYNC_RA, GLOBALS_TOP in *.
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
    carve_frame 48%nat ST.
    do 5 lstep.
    lstep. lstep. lstep. lstep.
    lstep. if_cases Hsb; zify_cond Hsb. 1:{ exfalso. clear - Hsb SB0 SBB LO RSP. try rewrite unsigned_lit in Hsb by lia. lia. }
    lstep. lstep. lstep.

    lstep.
    lstep. lstep.
    lstep. lstep.
    lstep.
    try (replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) by (vm_compute; reflexivity)).
    lstep. if_lit.
    lstep.
    lstep. if_lit.
    lstep. lstep.
    lstep.
    lstep.
    try (change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 1)) with (Z_to_bv 64 1 : word)).
    lstep. if_lit.
    lstep. lstep. lstep. lstep.
    lstep. lstep.
    lstep.
    rewrite (ret_pc_even SYNC) by (first [lia | exact SYE]).
    apply evt_done. unfold oflush_seg1_post, oflush_frame. sys_finish.
    all: try eassumption; try exact (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 C8))))))).
  Qed.

  Definition oflush_seg2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (ff : byte) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 O) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp + -64, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ ostream_cells m' ff.

  Lemma oflush_seg2 : forall (sp gp tp t0 t1 t2 s1x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 : word) (j0 j1 : list byte)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ff : byte),
    stk bsegs m lo (bv_unsigned sp + -48) -> (lo <= bv_unsigned sp - 64) -> (GLOBALS_TOP <= lo) ->
    rw_cells bsegs m (bv_unsigned sp + -48) (oflush_frame j0 j1 s1 s0 ra) ->
    ostream_cells m ff -> ostream_ok ff ->
    mem_inv bsegs m ->
    evt bsegs (oflush_seg2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ff m)
        (MS (mkR (Z_to_bv 64 OFLUSH_SYNC_RA) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 O) s1x (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 OFLUSH_SYNC_RA) fc None m (seg_rom bsegs)).
  Proof.
    intros until ff. intros ST LO GLO FR (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8) (UB & O0 & OB & VB & VO24 & VOH & SB0 & SBB & VSB0 & VSBH & SY & SYE) MI.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold OFLUSH_SYNC_RA, GLOBALS_TOP, oflush_frame in *.
    pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
    name_sp sp (-48)%Z. replace (bv_unsigned sp + -48) with (bv_unsigned sp0) in ST, FR by lia.
    lstep. lstep. if_lit.
    lstep. lstep.

    carve_frame 16%nat ST.
    lstep. lstep. lstep.
    lstep.
    lstep. lstep. lstep. lstep.
    lstep. if_cases Hsb2; zify_cond Hsb2. 1:{ exfalso. clear - Hsb2 SB0 SBB LO RSP. try rewrite unsigned_lit in Hsb2 by lia. lia. }
    lstep.
    try (replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) by (vm_compute; reflexivity)).
    lstep. if_lit.
    lstep.
    lstep.
    lstep. if_cases Hub; zify_cond Hub.
    2:{ exfalso. clear - Hub UB. try rewrite unsigned_lit in Hub by (pose proof (bv_unsigned_in_range 8 ff); unfold bv_modulus in *; cbn in *; lia). lia. }
    lstep. lstep. lstep.
    release_frame FR0 ST (bv_unsigned sp0).
    lstep.
    lstep. lstep. lstep. lstep. lstep.
    unname_sp.
    release_frame FR ST (bv_unsigned sp).
    lstep.
    apply evt_done. unfold oflush_seg2_post. sys_finish.
    exact (conj D1 (conj D2 (conj D3 (conj D4 (conj D5 (conj D6 (conj D7 D8))))))).
  Qed.
End OFlush.
