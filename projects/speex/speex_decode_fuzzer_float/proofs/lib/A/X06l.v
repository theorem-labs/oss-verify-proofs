(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1dg X1ch X1cg X1dk.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1rh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X081.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X0ys.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition A_speex_lib_get_mode : Z := 0xb5708.

Definition mode_addr (mo : spx_mode) : Z :=
match mo with ModeNB => A_speex_nb_mode | ModeWB => A_speex_wb_mode | ModeUWB => A_speex_uwb_mode end.
Definition mode_of_id (i : Z) : spx_mode := if i =? 0 then ModeNB else if i =? 1 then ModeWB else ModeUWB.

Definition lib_get_mode_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(usp lo i : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (mode_addr (mode_of_id i))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(usp + -16, usp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp.

Lemma speex_lib_get_mode_walk : forall (i usp lo : Z) ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
0 <= i <= 2 ->
aobj bsegs m A_speex_mode_list 24 ->
stk bsegs m lo usp -> lo <= usp - 16 -> SH_HI <= lo -> usp < 2^63 ->
client_constsB m -> lib_consts m -> mem_inv bsegs m ->
evt bsegs (lib_get_mode_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc usp lo i m)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 i) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_lib_get_mode) fc None m (seg_rom bsegs)).

Proof.
intros until m. intros Hi OB ST LO LOS SPH (G1 & G2 & _) LC MI.
unfold A_speex_lib_get_mode, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address in *.
pose proof (lib_const m A_speex_mode_list LC_speex_mode_list LC ltac:(lc_in)) as ML.
unfold A_speex_mode_list, LC_speex_mode_list in ML, OB.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -16, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -16, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
assert (AL8 : 0xf8c00 mod 8 = 0) by reflexivity.
carve_frame 16%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
astep. astep. astep. astep.
if_cases K; zify_cond K; [| exfalso; lia].
ato 0xb5730. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8. astep. sh_if.
ato 0xb5750. rewrite ?Z.shiftl_mul_pow2 by lia. change (2^3) with 8. rewrite ?(Z.mod_small (1018880 + i * 8)) by lia.
astep. astep.
rewrite (shb_zero bsegs m 1018880 24 (1018880 + i * 8) (proj2 (proj2 OB)) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)).
lit_if.
assert (C : i = 0 \/ i = 1 \/ i = 2) by lia.
destruct C as [-> |[-> | ->]]; cbn [Z.mul Z.add Pos.mul Pos.add] in *.
all: ato 0xb575c.
all: do 2 astep; release_frame FR ST usp; astep.
all: unfold lib_get_mode_post, mode_of_id, mode_addr, A_speex_nb_mode, A_speex_wb_mode, A_speex_uwb_mode; cbn [Z.eqb Pos.eqb]; finish.

Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition A_speex_lib_get_mode : Z := 0xaf2c0.

Definition mode_addr (mo : spx_mode) : Z :=
match mo with ModeNB => A_speex_nb_mode | ModeWB => A_speex_wb_mode | ModeUWB => A_speex_uwb_mode end.
Definition mode_of_id (i : Z) : spx_mode := if i =? 0 then ModeNB else if i =? 1 then ModeWB else ModeUWB.

Definition lib_get_mode_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(usp lo i : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (mode_addr (mode_of_id i))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(usp + -16, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp.

Lemma speex_lib_get_mode_walk : forall (i usp lo : Z) ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
0 <= i <= 2 ->
aobj asegs m A_speex_mode_list 24 ->
stk asegs m lo usp -> lo <= usp - 16 -> SH_HI <= lo -> usp < 2^63 ->
client_consts m -> lib_consts m -> mem_inv asegs m ->
evt asegs (lib_get_mode_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc usp lo i m)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 i) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_lib_get_mode) fc None m (seg_rom asegs)).
Proof.
intros until m. intros Hi OB ST LO LOS SPH (G1 & G2 & _) LC MI.
unfold A_speex_lib_get_mode, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
pose proof (lib_const m A_speex_mode_list LC_speex_mode_list LC ltac:(lc_in)) as ML.
unfold A_speex_mode_list, LC_speex_mode_list in ML, OB.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -16, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -16, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
assert (AL8 : 0xf0380 mod 8 = 0) by reflexivity.
carve_frame 16%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
astep. astep. astep. astep.
if_cases K; zify_cond K; [| exfalso; lia].
ato 0xaf2fc. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8. rewrite (Z.mod_small (983936 + i * 8)) by lia.
astep. astep.
rewrite (shb_zero asegs m 983936 24 (983936 + i * 8) (proj2 (proj2 OB)) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)).
lit_if.
assert (C : i = 0 \/ i = 1 \/ i = 2) by lia.
destruct C as [-> |[-> | ->]]; cbn [Z.mul Z.add Pos.mul Pos.add] in *.
all: ato 0xaf308.
all: do 2 astep; release_frame FR ST usp; astep.
all: unfold lib_get_mode_post, mode_of_id, mode_addr, A_speex_nb_mode, A_speex_wb_mode, A_speex_uwb_mode; cbn [Z.eqb Pos.eqb]; finish.

Qed.
