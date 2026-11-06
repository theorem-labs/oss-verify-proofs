(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit Lept_objkit LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_extractRGBValues : Z := 0x96ea8.

(* [comment removed for export] *)
Definition rgb_r (u : Z) : Z := bv_wrap 32 u / 16777216.
Definition rgb_g (u : Z) : Z := (u * 1099511627776) mod 18446744073709551616 / 72057594037927936.
Definition rgb_b (u : Z) : Z := (u * 281474976710656) mod 18446744073709551616 / 72057594037927936.
Lemma rgb_r_range : forall u, 0 <= rgb_r u <= 255.
Proof.
  intros u. unfold rgb_r, bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296.
  pose proof (Z.mod_pos_bound u 4294967296 ltac:(lia)). Z.div_mod_to_equations. lia.
Qed.
Lemma rgb_g_range : forall u, 0 <= rgb_g u <= 255.
Proof.
  intros u. unfold rgb_g.
  pose proof (Z.mod_pos_bound (u * 1099511627776) 18446744073709551616 ltac:(lia)). Z.div_mod_to_equations. lia.
Qed.
Lemma rgb_b_range : forall u, 0 <= rgb_b u <= 255.
Proof.
  intros u. unfold rgb_b.
  pose proof (Z.mod_pos_bound (u * 281474976710656) 18446744073709551616 ltac:(lia)). Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Definition extractRGBValues_post (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (usp lo pr pg pb : Z) (px : word) : machine_state -> Prop :=
  fun ms' => exists (a0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : mem),
    ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(usp - 16, usp); (pr, pr + 4); (pg, pg + 4); (pb, pb + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp
    /\ rw_cells asegs m' pr [C4 (Z_to_bv 64 (rgb_r (bv_unsigned px)))]
    /\ rw_cells asegs m' pg [C4 (Z_to_bv 64 (rgb_g (bv_unsigned px)))]
    /\ rw_cells asegs m' pb [C4 (Z_to_bv 64 (rgb_b (bv_unsigned px)))].

Lemma extractRGBValues_evt : forall (ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (usp lo : Z) (px : word) (pr pg pb : Z) (o1 o2 o3 : word),
  rw_cells asegs m pr [C4 o1] -> rw_cells asegs m pg [C4 o2] -> rw_cells asegs m pb [C4 o3] ->
  acc asegs m pr 4 -> acc asegs m pg 4 -> acc asegs m pb 4 ->
  0 < pr -> pr mod 8 = 0 -> 0 < pg -> pg mod 8 = 0 -> 0 < pb -> pb mod 8 = 0 ->
  pr + 4 <= pg -> pg + 4 <= pb ->
  ro_cells asegs m g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)] ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo usp -> lo <= usp - 16 -> usp <= 2^47 -> 0x10007fff8000 <= lo -> pb + 4 <= lo ->
  (pb + 4 <= 0x7fff7000 \/ 0x10007fff8000 <= pr) -> SEGTOP_A <= pr ->
  mem_inv asegs m ->
  evt asegs (extractRGBValues_post ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m usp lo pr pg pb px)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 px (Z_to_bv 64 pr) (Z_to_bv 64 pg) (Z_to_bv 64 pb) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_extractRGBValues) fc None m (seg_rom asegs)).
Proof.
  intros until o3. intros C1 C2 C3 A1 A2 A3 P10 P18 P20 P28 P30 P38 D12 D23 G1 G2 ST LO UHI LOH PLO PSH PSEG MI.
  unfold e_extractRGBValues, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SEGTOP_A, SHB in *.
  pose proof (munch_refl [(usp - 16, usp); (pr, pr + 4); (pg, pg + 4); (pb, pb + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lwalk [0x96f30; 0x96f4c; 0x96f60; 0x96f74].      (* [comment removed for export] *)
  lwalk (@nil Z).                                  (* [comment removed for export] *)
  pose proof (rgb_r_range (bv_unsigned px)) as RR. unfold rgb_r in RR.
  rewrite (swrap32_small (bv_wrap 32 (bv_unsigned px) / 16777216)) in C1 by lia.
  apply evt_done. unfold extractRGBValues_post. do 9 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [exact C1|]. split; [exact C2| exact C3].
Qed.
