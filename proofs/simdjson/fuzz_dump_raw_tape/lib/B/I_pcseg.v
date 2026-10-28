(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout R_small I_qck X_atexit I_pck I_pcms I_pcbits.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require F_fwritex.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma rw_forget : forall m A cs, rw_cells bsegs m A cs -> rw_cells bsegs m A [CB (cells_size cs) (cells_bytes cs)].
Proof. intros m A cs H. apply (rw_cells_merge bsegs m A [] cs []). rewrite app_nil_r. exact H. Qed.

Definition DIR0 : list cell := [CB 8 (repeat z8 8); C8 (Z_to_bv 64 (-1)); CB 24 (repeat z8 24)].

Definition pcl_st (pc : Z) (ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 : word) (q p ap : Z)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 (q + -2240)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 10) (Z_to_bv 64 p)
          (Z_to_bv 64 89415) (Z_to_bv 64 ap) s6 (Z_to_bv 64 9) (Z_to_bv 64 (q + -2184)) (Z_to_bv 64 12297829382473034410)
          (Z_to_bv 64 (-1)) (Z_to_bv 64 37) t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom bsegs).

Definition pcs_post (q : Z) (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x6e2d0) fc None m' (seg_rom bsegs)
    /\ munch [(q + -2216, q + -2176)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' (q + -2216) DIR0.

Lemma pcom_setup_spec : forall (q : Z) (junk : list byte)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem),
  s0 = Z_to_bv 64 q -> s8 = Z_to_bv 64 (q + -2184) -> s9 = Z_to_bv 64 12297829382473034410 -> s10 = Z_to_bv 64 (-1) ->
  rw_cells bsegs m (q + -2216) [CB 40 junk] -> q mod 16 = 0 -> 2240 <= q < 2^63 -> mem_inv bsegs m ->
  evt bsegs (pcs_post q sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6e2a4) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros -> -> -> -> DIR Q16 QR MI.
  pose proof (munch_refl [(q + -2216, q + -2176)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  do 5 lstep.
  xsteps_to 0x92128%Z.
  apply rw_forget in DIR. cbn [cells_size csize Nat.add] in DIR.
  call (imemset40_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q);
    [reflexivity | reflexivity | reflexivity | exact DIR | assumption | lia | assumption | ].
  lstep.
  apply evt_done. unfold pcs_post. do 17 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  lazymatch goal with H : rw_cells _ _ (q + -2216) _ |- _ => exact H end.
Qed.

Definition txt_ok (l : list Z) : bool := forallb (fun c => (0 <? c) && (c <? 256) && negb (c =? 37)) l.

Lemma pcom_scan_spec : forall (txt : list Z) (p : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  s3 = Z_to_bv 64 p -> s11 = Z_to_bv 64 37 -> txt_ok txt = true ->
  bytes_at bsegs m p (zb8 txt) -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists a0' : word,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (p + Z.of_nat (length txt))) s4 s5 s6 s7 s8 s9
                    s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x6e2d0) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6e2d0) fc None m (seg_rom bsegs)).
Proof.
  induction txt as [|c txt IH]; intros p ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m -> -> OK BY MI.
  - apply evt_done. exists a0. cbn [length Z.of_nat]. rewrite Z.add_0_r. reflexivity.
  - cbn [txt_ok forallb] in OK. apply andb_prop in OK. destruct OK as [OKc OK].
    apply andb_prop in OKc. destruct OKc as [OKc N37]. apply andb_prop in OKc. destruct OKc as [C0 C256].
    apply Z.ltb_lt in C0. apply Z.ltb_lt in C256. apply negb_true_iff, Z.eqb_neq in N37.
    unfold zb8 in BY. cbn [map] in BY. apply (proj1 (bytes_at_app bsegs m p [Z_to_bv 8 c] _)) in BY. destruct BY as [B1 BY].
    pose proof (bytes_at_bound _ _ _ _ B1) as PB. cbn [length] in PB.
    pose proof (ro_C1_of_bytes m p _ B1) as CB0. clear B1.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
    assert (EUc : bv_unsigned (Z_to_bv 8 c) = c) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 8) with 256; apply Z.mod_small; lia).
    lstep. lstep. brF K1. lstep. brF K2. lstep. lstep. lstep.
    eapply evt_mono.
    { apply (IH (p + 1)); [reflexivity | reflexivity | exact OK | exact BY | exact MI]. }
    intros ms (a0' & ->). exists a0'. cbn [length]. rewrite Nat2Z.inj_succ.
    replace (p + Z.succ (Z.of_nat (length txt))) with (p + 1 + Z.of_nat (length txt)) by lia. reflexivity.
Qed.

Definition pcom_saved (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition pcom_end_post (q : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'.

Lemma pcom_end_spec : forall (q p : Z) (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  sp = Z_to_bv 64 (q + -2240) -> s3 = Z_to_bv 64 p -> s8 = Z_to_bv 64 (q + -2184) -> s11 = Z_to_bv 64 37 ->
  bytes_at bsegs m p [z8] -> bytes_at bsegs m (q + -2180) [z8] ->
  rw_cells bsegs m (q + -104) (pcom_saved ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11') ->
  2240 <= q < 2^63 -> mem_inv bsegs m ->
  evt bsegs (pcom_end_post q ra0 gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6e2d0) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros -> -> -> -> B0 C0 SV QR MI. unfold pcom_saved in SV.
  pose proof (bytes_at_bound _ _ _ _ B0) as PB. cbn [length] in PB.
  pose proof (ro_C1_of_bytes m p _ B0) as CB0. pose proof (ro_C1_of_bytes m _ _ C0) as CC0. clear B0 C0.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUq : bv_unsigned (Z_to_bv 64 (q + -2184)) = q + -2184) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 (q + -2240)) = q + -2240) by (apply unsigned_lit; lia).
  lstep. lstep. if_false. lstep. if_true.
  lstep. lstep. if_false. lstep.
  lstep. lstep. if_true.
  do 16 lstep.
  apply evt_done. unfold pcom_end_post. do 16 eexists. split; [ first [reflexivity | f_equal; f_equal; f_equal; lia] |].
  split; [exact MU|]. split; [exact WM| exact MI].
Qed.
