(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit D_iface D_defs D_libiface Gm_iface Fh_iface LeptB_guard LeptB_guard2 Fh_lowkit FhB_guard.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition fb1_words_exit (sp gp tp s1 a0 a2 a3 a4 s2 s3 s5 s6 s7 s8 s9 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (rs rd ld ls fb pw : Z) (fcells : list cell) (wss : list word) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t2' s0' a1' a6' a7' s4' s11' t3' : word) (m' : mem) (wsd' : list word),
    ms' = MS (mkR ra' sp gp tp t0' (Z_to_bv 64 SHB) t2' s0' s1 a0 a1' a2 a3 a4 (Z_to_bv 64 (4 * pw)) a6' a7' s2 s3 s4' s5 s6 s7 s8 s9 (Z_to_bv 64 0) s11' t3' t4 t5 t6)
             F (Z_to_bv 64 0xb2d68) fc None m' (seg_rom asegs)
    /\ munch [(rd, rd + 4 * ld); (fb + 96, fb + 200)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' rd wsd' /\ Z.of_nat (length wsd') = ld /\ u32arr asegs m' rs wss
    /\ acc asegs m' rd (4 * ld) /\ acc asegs m' rs (4 * ls)
    /\ rw_cells asegs m' (fb + 96) fcells.

Lemma fb1_words : forall (k : nat) (j : Z)
    (ra sp gp tp t0 t2 s0 a0 a1 a2 a3 a4 a6 a7 s3 s4 s11 t3 t5 t6 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v192 : word) F fc (m : mem)
    (rs rd q wpl pw c ls ld fb : Z) (wss wsd : list word),
  Z.of_nat k = pw - j -> c = pw - j -> 0 <= j -> (1 <= k)%nat -> pw <= 2^20 -> 0 < wpl <= 627 ->
  1 * wpl + 1 <= q -> q + 1 * wpl + pw + 1 <= ls -> q + pw <= ld -> ls <= 2^24 -> ld <= 2^24 ->
  sp = Z_to_bv 64 fb -> 0 < fb -> fb + 200 <= 2^47 -> fb mod 8 = 0 ->
  0 < rd -> rd mod 8 = 0 -> rd + 4 * ld <= 2^47 -> (rd + 4 * ld <= 0x7fff7000 \/ 0x10007fff8000 <= rd) ->
  (rd + 4 * ld <= 0x10000 \/ SEGTOP_A <= rd) ->
  0 < rs -> rs mod 8 = 0 -> rs + 4 * ls <= 2^47 -> (rs + 4 * ls <= 0x7fff7000 \/ 0x10007fff8000 <= rs) ->
  (rd + 4 * ld <= rs \/ rs + 4 * ls <= rd) -> (rd + 4 * ld <= fb \/ fb + 200 <= rd) -> (rs + 4 * ls <= fb \/ fb + 200 <= rs) ->
  (fb + 200 <= 0x7fff7000 \/ 0x10007fff8000 <= fb) ->
  u32arr asegs m rd wsd -> Z.of_nat (length wsd) = ld -> u32arr asegs m rs wss -> Z.of_nat (length wss) = ls ->
  acc asegs m rd (4 * ld) -> acc asegs m rs (4 * ls) -> mem_inv asegs m ->
  rw_cells asegs m (fb + 96) [C8 v96; C8 v104; C8 v112; C8 v120; C8 v128; C8 v136; C8 v144; C8 v152; C8 v160; C8 v168; C8 v176; C8 (Z_to_bv 64 0); C8 v192] ->
  evt asegs (fb1_words_exit sp gp tp (Z_to_bv 64 5) a0 a2 a3 a4 (Z_to_bv 64 (-5)) s3 (Z_to_bv 64 4294967295) (Z_to_bv 64 (rd + 4 * q)) (Z_to_bv 64 (rs + 4 * q)) (Z_to_bv 64 (rs + 4 * (q + 1 * wpl))) (Z_to_bv 64 (- (rs + 4 * (q + 1 * wpl)))) (Z_to_bv 64 0) t5 t6 F fc m rs rd ld ls fb pw
                            [C8 v96; C8 v104; C8 v112; C8 v120; C8 v128; C8 v136; C8 v144; C8 v152; C8 v160; C8 v168; C8 v176; C8 (Z_to_bv 64 0); C8 v192] wss)
    (MS (mkR ra sp gp tp t0 (Z_to_bv 64 SHB) t2 s0 (Z_to_bv 64 5) a0 a1 a2 a3 a4 (Z_to_bv 64 (4 * j)) a6 a7 (Z_to_bv 64 (-5)) s3 s4 (Z_to_bv 64 4294967295) (Z_to_bv 64 (rd + 4 * q)) (Z_to_bv 64 (rs + 4 * q)) (Z_to_bv 64 (rs + 4 * (q + 1 * wpl))) (Z_to_bv 64 (- (rs + 4 * (q + 1 * wpl)))) (Z_to_bv 64 c) s11 t3 (Z_to_bv 64 0) t5 t6)
        F (Z_to_bv 64 0xb2e5c) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j ra sp gp tp t0 t2 s0 a0 a1 a2 a3 a4 a6 a7 s3 s4 s11 t3 t5 t6 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v192 F fc m
    rs rd q wpl pw c ls ld fb wss wsd HK -> HJ HK1 PW WPL QLO QHI QD LS LD -> FB0 FBHI FB8 D0 D8 DHI DSH DSEG S0 S8 SHI SSH DSAP DFAP SFAP FSH UAD UADL UAS UASL ACCD ACCS MI SL.
  { lia. }
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl [(rd, rd + 4 * ld); (fb + 96, fb + 200)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  hide_disj.
  fwalkb rs rd [0xb2fbc].
  swrap32_fix.
  destruct k as [|k].
  - replace (pw - j + -1) with 0 by lia. fwalkb rs rd [0xb2d68].
    apply evt_done. unfold fb1_words_exit. do 12 eexists.
    split; [replace (4 * pw) with (4 * j + 4) by lia; reflexivity|].
    unhide_all.
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact UAD|]. split; [exact UADL|]. split; [exact UAS|]. split; [assumption|]. split; assumption.
  - fwalkb rs rd [0xb2e5c; 0xb2d68].
    replace (4 * j + 4) with (4 * (j + 1)) by lia. replace (pw - j + -1) with (pw - (j + 1)) by lia.
    unhide_all.
    eapply evt_cut.
    + eapply (IH (j + 1)) with (rs := rs) (rd := rd) (ld := ld) (ls := ls) (fb := fb) (q := q) (wpl := wpl) (pw := pw); try eassumption; try lia; try reflexivity.
    + intros ms' PO. apply evt_done. unfold fb1_words_exit in PO |- *.
      destruct PO as (ra' & t0' & t2' & s0' & a1' & a6' & a7' & s4' & s11' & t3' & m' & wsd' & E & MU' & WM' & R).
      exists ra', t0', t2', s0', a1', a6', a7', s4', s11', t3', m', wsd'.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact R].
Qed.

(* [comment removed for export] *)
Definition fb1_exit (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (rd ld fb : Z) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' x96' x104' x112' x120' x128' x136' x144' x152' x160' x168' x176' x184' x192' : word) (m' : mem),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
             F (Z_to_bv 64 0xb3fac) fc None m' (seg_rom asegs)
    /\ munch [(rd, rd + 4 * ld); (fb + 96, fb + 200)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (fb + 96) [C8 x96'; C8 x104'; C8 x112'; C8 x120'; C8 x128'; C8 x136'; C8 x144'; C8 x152'; C8 x160'; C8 x168'; C8 x176'; C8 x184'; C8 x192'].

Lemma fb1_rows : forall (k : nat) (i : Z)
    (ra sp gp tp t0 t2 s0 a1 a6 a7 s4 s11 t3 v112 v120 v128 v136 : word) F fc (m : mem)
    (rs rd q0 wpl pw w31 h iw ls ld fb : Z) (wss wsd : list word),
  Z.of_nat k = h - i -> 0 <= i -> (1 <= k)%nat -> 0 < h <= 20000 -> 1 <= pw <= 2^20 -> 32 <= w31 < 2^31 -> 0 < wpl <= 627 -> iw = i * wpl ->
  1 * wpl + 1 <= q0 -> q0 + (h - 1) * wpl + 1 * wpl + pw + 1 <= ls -> q0 + (h - 1) * wpl + pw <= ld -> ls <= 2^24 -> ld <= 2^24 ->
  sp = Z_to_bv 64 fb -> 0 < fb -> fb + 200 <= 2^47 -> fb mod 8 = 0 ->
  0 < rd -> rd mod 8 = 0 -> rd + 4 * ld <= 2^47 -> (rd + 4 * ld <= 0x7fff7000 \/ 0x10007fff8000 <= rd) ->
  (rd + 4 * ld <= 0x10000 \/ SEGTOP_A <= rd) ->
  0 < rs -> rs mod 8 = 0 -> rs + 4 * ls <= 2^47 -> (rs + 4 * ls <= 0x7fff7000 \/ 0x10007fff8000 <= rs) ->
  (rd + 4 * ld <= rs \/ rs + 4 * ls <= rd) -> (rd + 4 * ld <= fb \/ fb + 200 <= rd) -> (rs + 4 * ls <= fb \/ fb + 200 <= rs) ->
  (fb + 200 <= 0x7fff7000 \/ 0x10007fff8000 <= fb) ->
  u32arr asegs m rd wsd -> Z.of_nat (length wsd) = ld -> u32arr asegs m rs wss -> Z.of_nat (length wss) = ls ->
  acc asegs m rd (4 * ld) -> acc asegs m rs (4 * ls) -> mem_inv asegs m ->
  rw_cells asegs m (fb + 96) [C8 (Z_to_bv 64 wpl); C8 (Z_to_bv 64 h); C8 v112; C8 v120; C8 v128; C8 v136; C8 (Z_to_bv 64 (- (rs + 4 * (q0 + 1 * wpl)))); C8 (Z_to_bv 64 pw); C8 (Z_to_bv 64 wpl); C8 (Z_to_bv 64 (rd + 4 * q0)); C8 (Z_to_bv 64 (rs + 4 * q0)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  evt asegs (fb1_exit sp gp tp F fc m rd ld fb)
    (MS (mkR ra sp gp tp t0 (Z_to_bv 64 SHB) t2 s0 (Z_to_bv 64 5) (Z_to_bv 64 w31) a1 (Z_to_bv 64 iw) (Z_to_bv 64 iw) (Z_to_bv 64 i) (Z_to_bv 64 0) a6 a7 (Z_to_bv 64 (-5)) (Z_to_bv 64 (rs + 4 * (q0 + 1 * wpl))) s4 (Z_to_bv 64 4294967295) (Z_to_bv 64 (rd + 4 * (q0 + iw))) (Z_to_bv 64 (rs + 4 * (q0 + iw))) (Z_to_bv 64 (rs + 4 * (q0 + iw + 1 * wpl))) (Z_to_bv 64 (- (rs + 4 * (q0 + iw + 1 * wpl)))) (Z_to_bv 64 pw) s11 t3 (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 1))
        F (Z_to_bv 64 0xb2e5c) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i ra sp gp tp t0 t2 s0 a1 a6 a7 s4 s11 t3 v112 v120 v128 v136 F fc m
    rs rd q0 wpl pw w31 h iw ls ld fb wss wsd HK HI HK1 HH PW W31 WPL IWE QLO QHI QD LS LD -> FB0 FBHI FB8 D0 D8 DHI DSH DSEG S0 S8 SHI SSH DSAP DFAP SFAP FSH UAD UADL UAS UASL ACCD ACCS MI SL.
  { lia. }
  assert (PI : 0 <= i * wpl /\ i * wpl <= (h - 1) * wpl) by (clear - HK HI WPL; nia).
  assert (PH : (h - 1) * wpl <= 12540000) by (clear - HH WPL; nia).
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl [(rd, rd + 4 * ld); (fb + 96, fb + 200)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  eapply evt_cut.
  { eapply (fb1_words (Z.to_nat pw) 0) with (rs := rs) (rd := rd) (ld := ld) (ls := ls) (fb := fb) (q := q0 + iw) (wpl := wpl) (pw := pw) (c := pw);
      try eassumption; try lia; try reflexivity. }
  intros ms' PO. unfold fb1_words_exit in PO.
  destruct PO as (ra' & t0' & t2' & s0' & a1' & a6' & a7' & s4' & s11' & t3' & m' & wsd' & -> & MU' & WM' & MI' & UAD' & UADL' & UAS' & ACCD' & ACCS' & SL').
  clear MU WM UAD UADL UAS ACCD ACCS MI SL.
  hide_disj.
  fwalkb rs rd [0xb2d80].
  swrap32_fix.
  unhide_all.
  destruct k as [|k].
  - assert (EI : i + 1 = h) by lia. rewrite EI in *.
    hide_disj. fwalkb rs rd [0xb3fac]. unhide_all.
    apply evt_done. unfold fb1_exit. do 42 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; eassumption.
  - assert (PI1 : (i + 1) * wpl <= (h - 1) * wpl) by (clear - HK HI WPL; nia).
    hide_disj. fwalkb rs rd [0xb2e5c]. unhide_all.
    swrap32_fix.
    repeat match goal with |- context [?E mod 18446744073709551616] =>
      rewrite (Z.mod_small E 18446744073709551616) by (clear - PI PI1 PH IWE WPL HI; lia) end.
    canon_reg 12 (iw + wpl).
    canon_reg 13 (iw + wpl).
    canon_reg 14 (i + 1).
    canon_reg 22 (rd + 4 * (q0 + (iw + wpl))).
    canon_reg 23 (rs + 4 * (q0 + (iw + wpl))).
    canon_reg 24 (rs + 4 * (q0 + (iw + wpl) + 1 * wpl)).
    canon_reg 25 (- (rs + 4 * (q0 + (iw + wpl) + 1 * wpl))).
    lazymatch goal with H : rw_cells ?sg ?mm (fb + 96) [C8 ?c0; C8 ?c1; C8 ?c2; C8 ?c3; C8 ?c4; C8 ?c5; C8 ?c6; C8 ?c7; C8 ?c8; C8 ?c9; C8 ?c10; C8 ?c11; C8 ?c12] |- _ =>
      let N := fresh "CAN" in
      assert (N : rw_cells sg mm (fb + 96) [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12])
        by (replace [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12] with [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12]; [exact H| cells_eq]);
      clear H end.
    eapply evt_cut.
    + eapply (IH (i + 1)) with (rs := rs) (rd := rd) (ld := ld) (ls := ls) (fb := fb) (q0 := q0) (wpl := wpl) (pw := pw) (h := h) (w31 := w31) (iw := iw + wpl);
        try eassumption; try lia; try reflexivity.
    + intros ms' PO. apply evt_done. unfold fb1_exit in PO |- *.
      destruct PO as (ra'' & t0'' & t1'' & t2'' & s0'' & s1'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & s2'' & s3'' & s4'' & s5'' & s6'' & s7'' & s8'' & s9'' & s10'' & s11'' & t3'' & t4'' & t5'' & t6'' & x96'' & x104'' & x112'' & x120'' & x128'' & x136'' & x144'' & x152'' & x160'' & x168'' & x176'' & x184'' & x192'' & m'' & E & MU'' & WM'' & MI'' & SL'').
      exists ra'', t0'', t1'', t2'', s0'', s1'', a0'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', s2'', s3'', s4'', s5'', s6'', s7'', s8'', s9'', s10'', s11'', t3'', t4'', t5'', t6'', x96'', x104'', x112'', x120'', x128'', x136'', x144'', x152'', x160'', x168'', x176'', x184'', x192'', m''.
      split; [exact E|].
      split; [eapply munch_trans; eassumption|]. split; [eapply wmono_trans; eassumption|]. split; [exact MI''| exact SL''].
Qed.
