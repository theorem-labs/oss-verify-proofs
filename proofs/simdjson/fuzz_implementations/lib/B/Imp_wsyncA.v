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

Definition F_WSYNC : Z := 0x122e1c.
Definition WSYNC_UNSH_RA : Z := 0x122e6c.
Definition WSYNC_FWR_RA : Z := 0x122e8c.
Definition WSYNC_FFL_RA : Z := 0x122eac.
Definition F_FWRITE_ : Z := 0x6fe28.
Definition F_FFLUSH_ : Z := 0x6fe88.

Section WSync.

  Variables (SB Fp CV VCV UNSH STP lo : Z).

  Definition wsbuf_cells (m : mem) : Prop :=
    rw_cells bsegs m (SB + 64) [C8 (Z_to_bv 64 Fp); C8 (Z_to_bv 64 CV); C8 (Z_to_bv 64 STP)]
    /\ rw_cells bsegs m CV [C8 (Z_to_bv 64 VCV)]
    /\ rw_cells bsegs m (VCV + 40) [C8 (Z_to_bv 64 UNSH)].
  Definition wsbuf_ok : Prop :=
    (0 < SB) /\ (SB + 88 <= lo) /\ (0 < CV) /\ (CV + 8 <= lo) /\ (0 <= VCV) /\ (VCV + 48 <= lo) /\ (0 <= UNSH < 2^47) /\ (UNSH mod 2 = 0)
    /\ (0 <= Fp < 2^64) /\ (0 <= STP < 2^64).

  Definition wsync_saved (s5 s4 s3 s2 s1 s0 ra : word) : list cell := [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition wsync_seg1a_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (j0 j1 jb : list byte) (m' : mem),
      ms' = MS (mkR (Z_to_bv 64 WSYNC_UNSH_RA) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 SB) (Z_to_bv 64 (bv_unsigned sp + -56))
                    (Z_to_bv 64 CV) (Z_to_bv 64 STP) (Z_to_bv 64 (bv_unsigned sp + -64)) (Z_to_bv 64 (bv_unsigned sp + -56)) (Z_to_bv 64 (bv_unsigned sp + -72))
                    (Z_to_bv 64 UNSH) a6 a7 s2 s3 (Z_to_bv 64 (bv_unsigned sp + -64)) (Z_to_bv 64 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 UNSH) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp + -80, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp + -80)
      /\ rw_cells bsegs m' (bv_unsigned sp + -80) [CB 8 j0] /\ rw_cells bsegs m' (bv_unsigned sp + -72) [CB 8 j1]
      /\ rw_cells bsegs m' (bv_unsigned sp + -64) [CB 8 jb] /\ rw_cells bsegs m' (bv_unsigned sp + -56) (wsync_saved s5 s4 s3 s2 s1 s0 ra)
      /\ wsbuf_cells m'.

  Lemma wsync_seg1a : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 80) -> (GLOBALS_TOP <= lo) ->
    wsbuf_cells m -> wsbuf_ok ->
    mem_inv bsegs m ->
    evt bsegs (wsync_seg1a_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 SB) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 F_WSYNC) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros ST LO GLO (C1 & C2 & C3) (SB0 & SBH & CV0 & CVH & VCV0 & VCVH & UN & UNE & FP & STR) MI.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold F_WSYNC, WSYNC_UNSH_RA, GLOBALS_TOP in *.
    pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
    carve_frame 80%nat ST.
    do 8 lstep.
    lstep. lstep. lstep. lstep.
    lstep. lstep.
    lstep. lstep.
    lstep. lstep. lstep.
    lstep.
    rewrite (ret_pc_even UNSH) by (first [lia | exact UNE]).

    lazymatch type of FR with rw_cells _ ?mm ?A (CB 24 ?j :: ?rest) =>
      pose proof (rw_cells_split_CB bsegs mm A [] 24 j rest [8%nat; 8%nat; 8%nat] FR eq_refl) as FRS; cbn [app mk_CB_cells] in FRS;
      apply (proj1 (rw_cells_app _ _ _ [CB 8 _] _)) in FRS as [FA FRS];
      apply (proj1 (rw_cells_app _ _ _ [CB 8 _] _)) in FRS as [FE FRS];
      apply (proj1 (rw_cells_app _ _ _ [CB 8 _] _)) in FRS as [FB FSV];
      cbn [cells_size csize Nat.add] in FE, FB, FSV; change (Z.of_nat 8) with 8 in FE; change (Z.of_nat 8) with 8 in FB; change (Z.of_nat 8) with 8 in FSV
    end.
    replace (bv_unsigned sp + -80 + 8) with (bv_unsigned sp + -72) in FE by lia.
    replace (bv_unsigned sp + -80 + 8 + 8) with (bv_unsigned sp + -64) in FB by lia.
    replace (bv_unsigned sp + -80 + 8 + 8 + 8) with (bv_unsigned sp + -56) in FSV by lia.
    clear FR.
    apply evt_done. unfold wsync_seg1a_post, wsync_saved. sys_finish.
    all: try eassumption; try exact (conj C1 (conj C2 C3)).
  Qed.

  Definition wsync_seg1b_post (sp gp tp s0 s1 s4 s5 s6 s7 s8 s9 s10 s11 a4 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32) (r : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR (Z_to_bv 64 WSYNC_FWR_RA) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + -64)) (Z_to_bv 64 1) (Z_to_bv 64 0)
                    (Z_to_bv 64 Fp) a4 a5 a6 a7 (Z_to_bv 64 r) (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 F_FWRITE_) fc None m' (seg_rom bsegs)
      /\ munch [] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' (bv_unsigned sp + -72) [C8 (Z_to_bv 64 (bv_unsigned sp + -64))]
      /\ wsbuf_cells m'.

  Lemma wsync_seg1b : forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (r : Z),
    (0 <= r < 2^64) -> (80 <= bv_unsigned sp) ->
    rw_cells bsegs m (bv_unsigned sp + -72) [C8 (Z_to_bv 64 (bv_unsigned sp + -64))] ->
    wsbuf_cells m -> wsbuf_ok ->
    mem_inv bsegs m ->
    evt bsegs (wsync_seg1b_post sp gp tp (Z_to_bv 64 SB) s1 (Z_to_bv 64 (bv_unsigned sp + -64)) s5 s6 s7 s8 s9 s10 s11 a4 a5 a6 a7 F fc r m)
        (MS (mkR (Z_to_bv 64 WSYNC_UNSH_RA) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 SB) s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 (Z_to_bv 64 (bv_unsigned sp + -64)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 WSYNC_UNSH_RA) fc None m (seg_rom bsegs)).
  Proof.
    intros until r. intros RR SP80 FE (C1 & C2 & C3) (SB0 & SBH & CV0 & CVH & VCV0 & VCVH & UN & UNE & FP & STR) MI.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold WSYNC_UNSH_RA, WSYNC_FWR_RA, F_FWRITE_ in *.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
    name_sp sp (-80)%Z.
    replace (bv_unsigned sp + -72) with (bv_unsigned sp0 + 8) in FE by lia.
    lstep.
    lstep.
    lstep.
    lstep.
    lstep. lstep. lstep.
    lstep.
    replace (Z_to_bv 64 (bv_unsigned sp + -64 - (bv_unsigned sp + -64))) with (Z_to_bv 64 0 : word) by (f_equal; lia).
    unname_sp. replace (bv_unsigned sp + -80 + 16) with (bv_unsigned sp + -64) by lia.
    replace (bv_unsigned sp + -80 + 8) with (bv_unsigned sp + -72) in FE by lia.
    apply evt_done. unfold wsync_seg1b_post. sys_finish.
    all: try eassumption; try exact (conj C1 (conj C2 C3)).
  Qed.

  Variable RNC : Z.
  Definition wsync_seg2_post (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR (Z_to_bv 64 WSYNC_FFL_RA) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 2) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 F_FFLUSH_) fc None m' (seg_rom bsegs)
      /\ munch [] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ wsbuf_cells m'.

  Lemma wsync_seg2 : forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    (RNC = 3 \/ RNC = 0) ->
    wsbuf_cells m -> wsbuf_ok ->
    mem_inv bsegs m ->
    evt bsegs (wsync_seg2_post sp gp tp (Z_to_bv 64 SB) s1 (Z_to_bv 64 RNC) (Z_to_bv 64 0) s4 (Z_to_bv 64 1) s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 F fc m)
        (MS (mkR (Z_to_bv 64 WSYNC_FWR_RA) sp gp tp t0 t1 t2 (Z_to_bv 64 SB) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 RNC) (Z_to_bv 64 0) s4 (Z_to_bv 64 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 WSYNC_FWR_RA) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros HR (C1 & C2 & C3) (SB0 & SBH & CV0 & CVH & VCV0 & VCVH & UN & UNE & FP & STR) MI.
    unfold WSYNC_FWR_RA, WSYNC_FFL_RA, F_FFLUSH_ in *.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
    destruct HR as [-> | ->].
    - lstep. lstep. lstep. if_lit. lstep. if_lit. lstep. lstep. if_lit. lstep. lstep.
      apply evt_done. unfold wsync_seg2_post. sys_finish. exact (conj C1 (conj C2 C3)).
    - lstep. lstep. lstep. if_lit. lstep. if_lit. lstep. lstep. if_lit. lstep. lstep.
      apply evt_done. unfold wsync_seg2_post. sys_finish. exact (conj C1 (conj C2 C3)).
  Qed.

  Definition wsync_seg3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a1 a2 a3 a4 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp).

  Lemma wsync_seg3 : forall (sp gp tp t0 t1 t2 s0x s1x a1 a2 a3 a4 a5 a6 a7 s2x s3x s4x s5x s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 s5 e : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 jb : list byte),
    stk bsegs m lo (bv_unsigned sp + -80) -> (lo <= bv_unsigned sp - 80) -> (GLOBALS_TOP <= lo) ->
    rw_cells bsegs m (bv_unsigned sp + -80) [CB 8 j0] -> rw_cells bsegs m (bv_unsigned sp + -72) [C8 e] ->
    rw_cells bsegs m (bv_unsigned sp + -64) [CB 8 jb] -> rw_cells bsegs m (bv_unsigned sp + -56) (wsync_saved s5 s4 s3 s2 s1 s0 ra) ->
    mem_inv bsegs m ->
    evt bsegs (wsync_seg3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a1 a2 a3 a4 a5 a6 a7 F fc m)
        (MS (mkR (Z_to_bv 64 WSYNC_FFL_RA) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0x s1x (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                 s2x s3x s4x s5x s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 WSYNC_FFL_RA) fc None m (seg_rom bsegs)).
  Proof.
    intros until jb. intros ST LO GLO FA FE FB FSV MI.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold WSYNC_FFL_RA, GLOBALS_TOP, wsync_saved in *.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
    name_sp sp (-80)%Z.
    replace (bv_unsigned sp + -80) with (bv_unsigned sp0) in ST, FA by lia.
    replace (bv_unsigned sp + -72) with (bv_unsigned sp0 + 8) in FE by lia.
    replace (bv_unsigned sp + -64) with (bv_unsigned sp0 + 16) in FB by lia.
    replace (bv_unsigned sp + -56) with (bv_unsigned sp0 + 24) in FSV by lia.
    lstep. lstep.
    do 7 lstep.
    unname_sp.
    lstep.

    release_frame FA ST (bv_unsigned sp + -80 + 8). release_frame FE ST (bv_unsigned sp + -80 + 16).
    release_frame FB ST (bv_unsigned sp + -80 + 24). release_frame FSV ST (bv_unsigned sp).
    lstep.
    apply evt_done. unfold wsync_seg3_post. sys_finish.
  Qed.
End WSync.
