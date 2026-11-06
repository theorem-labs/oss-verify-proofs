(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05l.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition A_speex_bits_destroy : Z := 0x97904.
Definition e_wrap_free : Z := 0x67f80.

Section F.
Context {ptr : Type}.
Variables (A D usp lo : Z) (b : bits_st ptr).
Variables ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m : mem.
Hypothesis REP : bits_rep bsegs m A D b.
Hypothesis OK : bits_ok b.
Hypothesis OBA : aobj bsegs m A BITS_SIZEOF.
Hypothesis LO : lo <= usp - 16.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Hypothesis ALO : A + BITS_SIZEOF <= lo.
Hypothesis DLO : D + sb_buf_size b <= lo.
Hypothesis IOW : 0 <= sb_owner b < 2^31.

Local Notation START := (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_bits_destroy) fc None m (seg_rom bsegs)).

Lemma bits_destroy_ret :
sb_owner b = 0 -> stk bsegs m lo usp -> client_constsB m -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (a1' a2' a3' : word),
ms = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -16, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp /\ bits_rep bsegs m1 A D b)
START.
Proof using REP OK OBA LO LOS SPH ALO DLO IOW.
intros OW ST CC MI. destruct CC as (G1 & G2 & _).
unfold A_speex_bits_destroy, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address in *.
pose proof REP as ((rj & Lrj & OBJ) & (bs & ARR & Hbs) & SIDE).
pose proof SIDE as (AL & Apos & Dpos & _ & _ & SEP).
unfold BITS_SIZEOF in *. unfold bits_cells in OBJ.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (u8arr_bound _ _ _ _ ARR) as DB.
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b) by (pose proof OK as OK'; unfold bits_ok in OK'; rewrite Hbs, zlength_map_unsigned in OK'; lia).
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -16, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -16, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 16%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0x9790c. astep. sh_if.
ato 0x97914. astep. sh_if.
ato 0x9793c. rewrite sx32_small by (unfold int31; lia). astep. sh_if.
ato 0x97964. release_frame FR ST usp. astep. astep.
apply evt_done. do 4 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
exact (conj (ex_intro _ rj (conj Lrj OBJ)) (conj (ex_intro _ bs (conj ARR Hbs)) SIDE)).
Qed.

Lemma bits_destroy_w1 :
sb_owner b <> 0 -> stk bsegs m lo usp -> client_constsB m -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (a1' a2' a3' : word),
ms = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_wrap_free) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -16, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp /\ bits_rep bsegs m1 A D b)
START.
Proof using REP OK OBA LO LOS SPH ALO DLO IOW.
intros OW ST CC MI. destruct CC as (G1 & G2 & _).
unfold A_speex_bits_destroy, e_wrap_free, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address in *.
pose proof REP as ((rj & Lrj & OBJ) & (bs & ARR & Hbs) & SIDE).
pose proof SIDE as (AL & Apos & Dpos & _ & _ & SEP).
unfold BITS_SIZEOF in *. unfold bits_cells in OBJ.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (u8arr_bound _ _ _ _ ARR) as DB.
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b) by (pose proof OK as OK'; unfold bits_ok in OK'; rewrite Hbs, zlength_map_unsigned in OK'; lia).
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -16, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -16, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 16%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0x9790c. astep. sh_if.
ato 0x97914. astep. sh_if.
ato 0x9793c. rewrite sx32_small by (unfold int31; lia). astep. sh_if.
ato 0x97958. release_frame FR ST usp. astep. astep.
apply evt_done. do 4 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
exact (conj (ex_intro _ rj (conj Lrj OBJ)) (conj (ex_intro _ bs (conj ARR Hbs)) SIDE)).
Qed.
End F.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition A_speex_bits_destroy : Z := 0x97640.
Definition e_wrap_free : Z := 0x67e94.

Section F.
Context {ptr : Type}.
Variables (A D usp lo : Z) (b : bits_st ptr).
Variables ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m : mem.
Hypothesis REP : bits_rep asegs m A D b.
Hypothesis OK : bits_ok b.
Hypothesis OBA : aobj asegs m A BITS_SIZEOF.
Hypothesis LO : lo <= usp - 16.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Hypothesis ALO : A + BITS_SIZEOF <= lo.
Hypothesis DLO : D + sb_buf_size b <= lo.
Hypothesis IOW : 0 <= sb_owner b < 2^31.

Local Notation START := (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_bits_destroy) fc None m (seg_rom asegs)).

Lemma bits_destroy_ret :
sb_owner b = 0 -> stk asegs m lo usp -> client_consts m -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (a1' a2' a3' : word),
ms = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m1 (seg_rom asegs)
/\ munch [(usp + -16, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp /\ bits_rep asegs m1 A D b)
START.
Proof using REP OK OBA LO LOS SPH ALO DLO IOW.
intros OW ST CC MI. destruct CC as (G1 & G2 & _).
unfold A_speex_bits_destroy, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
pose proof REP as ((rj & Lrj & OBJ) & (bs & ARR & Hbs) & SIDE).
pose proof SIDE as (AL & Apos & Dpos & _ & _ & SEP).
unfold BITS_SIZEOF in *. unfold bits_cells in OBJ.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (u8arr_bound _ _ _ _ ARR) as DB.
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b) by (pose proof OK as OK'; unfold bits_ok in OK'; rewrite Hbs, zlength_map_unsigned in OK'; lia).
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -16, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -16, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 16%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0x9766c. rewrite sx32_small by (unfold int31; lia). astep. sh_if.
ato 0x97694. release_frame FR ST usp. astep. astep.
apply evt_done. do 4 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
exact (conj (ex_intro _ rj (conj Lrj OBJ)) (conj (ex_intro _ bs (conj ARR Hbs)) SIDE)).
Qed.

Lemma bits_destroy_w1 :
sb_owner b <> 0 -> stk asegs m lo usp -> client_consts m -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (a1' a2' a3' : word),
ms = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_wrap_free) fc None m1 (seg_rom asegs)
/\ munch [(usp + -16, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp /\ bits_rep asegs m1 A D b)
START.
Proof using REP OK OBA LO LOS SPH ALO DLO IOW.
intros OW ST CC MI. destruct CC as (G1 & G2 & _).
unfold A_speex_bits_destroy, e_wrap_free, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
pose proof REP as ((rj & Lrj & OBJ) & (bs & ARR & Hbs) & SIDE).
pose proof SIDE as (AL & Apos & Dpos & _ & _ & SEP).
unfold BITS_SIZEOF in *. unfold bits_cells in OBJ.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (u8arr_bound _ _ _ _ ARR) as DB.
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b) by (pose proof OK as OK'; unfold bits_ok in OK'; rewrite Hbs, zlength_map_unsigned in OK'; lia).
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -16, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -16, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 16%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0x9766c. rewrite sx32_small by (unfold int31; lia). astep. sh_if.
ato 0x97688. release_frame FR ST usp. astep. astep.
apply evt_done. do 4 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
exact (conj (ex_intro _ rj (conj Lrj OBJ)) (conj (ex_intro _ bs (conj ARR Hbs)) SIDE)).
Qed.
End F.
