(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05l X05g.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X0wd.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wd.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_wrap_fprintf : Z := 0x56d08.
Definition e_wrap_realloc : Z := 0x67f8c.
Definition RA_rf_fprintf : Z := 0x97b68.
Definition RA_rf_realloc : Z := 0x97ba0.
Definition RF_GOT_STDERR : Z := 0xfcd78.
Definition RF_STDERR_VAR : Z := 0xfc010.
Definition RF_FMT_NOTIFY : Z := 0x23580.
Definition RF_MSG_LARGER : Z := 0x23360.

Definition rf_frame (j0 : list byte) (c7 c6 c5 c4 c3 c2 c1 c0 cra : word) : list cell :=
[CB 8 j0; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra].

Section Big.
Context {ptr : Type}.
Variables (A P D len usp lo : Z) (pb : list byte) (b : bits_st ptr).
Variables (gp tp s8 s9 s10 s11 : word).

Lemma read_from_big_w1 : forall (errf : Z) (ra t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
bits_rep bsegs m A D b -> bits_ok b -> 0 <= len < 2^31 -> sb_buf_size b < len ->
aobj bsegs m A 48 -> aobj bsegs m RF_STDERR_VAR 8 ->
ro_cells bsegs m RF_GOT_STDERR [C8 (Z_to_bv 64 RF_STDERR_VAR)] -> ro_cells bsegs m RF_STDERR_VAR [C8 (Z_to_bv 64 errf)] ->
stk bsegs m lo usp -> lo <= usp - 80 -> SH_HI <= lo -> usp < 2^63 -> A + 48 <= lo -> D + sb_buf_size b <= lo ->
client_constsB m -> mem_inv bsegs m ->
evt bsegs (fun ms' => exists (a3' a4' : word) (j0 : list byte) (m1 : mem),
ms' = MS (mkR (Z_to_bv 64 RA_rf_fprintf) (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 P)
(Z_to_bv 64 errf) (Z_to_bv 64 RF_FMT_NOTIFY) (Z_to_bv 64 RF_MSG_LARGER) a3' a4' a5 a6 a7
(Z_to_bv 64 len) (Z_to_bv 64 (A + 28)) (Z_to_bv 64 errf) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.shiftr (A + 28) 3 + SHB)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_wrap_fprintf) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -80, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -80)
/\ rw_cells bsegs m1 (usp + -80) (rf_frame j0 s7 s6 s5 s4 s3 s2 s1 s0 ra) /\ bits_rep bsegs m1 A D b)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 P) (Z_to_bv 64 len) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_bits_read_from) fc None m (seg_rom bsegs)).

Proof.
intros until m. intros REP OK Hlen BIG OBA OBV GOTE VARE ST LO LOS SPH ALO DLO CC MI.
destruct CC as (G1 & G2 & _).
unfold A_speex_bits_read_from, e_wrap_fprintf, RA_rf_fprintf, RF_GOT_STDERR, RF_STDERR_VAR, RF_FMT_NOTIFY, RF_MSG_LARGER, rf_frame,
gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address in *.
pose proof REP as ((rj & Lrj & OBJ) & (bs & ARR & Hbs) & SIDE).
pose proof (bits_ints A D b OK SIDE) as (In & Ic & Ib & Io & Iv & Is & Rc & Rb & Rp & Rn & Rs & R1 & Rov).
pose proof SIDE as (AL & Apos & Dpos & _ & OWN & SEP).
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. lia. }
unfold int31, BITS_BUF_MAX, BITS_SIZEOF in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (u8arr_bound _ _ _ _ ARR) as DB.
pose proof ST as (STa & STb & _).
assert (V8 : 1032208 mod 8 = 0) by reflexivity.
pose proof (munch_refl [(usp + -80, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -80, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 80%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 80 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
unfold bits_cells in OBJ.
ato 0x979b0. astep. sh_if.
ato 0x979bc. astep. sh_if.
ato 0x979ec. rewrite sx32_small by (unfold int31; lia).
astep. sh_if.
ato 0x56d08.
apply evt_done. do 4 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR|].
exact (conj (ex_intro _ rj (conj Lrj OBJ)) (conj (ex_intro _ bs (conj ARR Hbs)) SIDE)).
Qed.

Lemma read_from_big_w2 : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s4 s6 s7 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
bits_rep bsegs m A D b -> bits_ok b -> sb_owner b = 1 -> 0 <= len < 2^31 ->
aobj bsegs m A 48 -> lo <= usp - 80 -> SH_HI <= lo -> usp < 2^63 -> A + 48 <= lo -> mem_inv bsegs m ->
evt bsegs (fun ms' => exists (a2' a3' : word),
ms' = MS (mkR (Z_to_bv 64 RA_rf_realloc) (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 P)
(Z_to_bv 64 D) (Z_to_bv 64 len) a2' a3' a4 a5 a6 a7
(Z_to_bv 64 len) (Z_to_bv 64 (A + 28)) s4 (Z_to_bv 64 SHB) s6 (Z_to_bv 64 (Z.shiftr A 3 + SHB)) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_wrap_realloc) fc None m (seg_rom bsegs))
(MS (mkR (Z_to_bv 64 RA_rf_fprintf) (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 len) (Z_to_bv 64 (A + 28)) s4 (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_rf_fprintf)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros REP OK OWN1 Hlen OBA LO LOS SPH ALO MI.
unfold e_wrap_realloc, RA_rf_fprintf, RA_rf_realloc in *.
replace (ret_pc (Z_to_bv 64 0x97b68)) with (Z_to_bv 64 0x97b68) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof REP as ((rj & Lrj & OBJ) & (bs & ARR & Hbs) & SIDE).
pose proof (bits_ints A D b OK SIDE) as (In & Ic & Ib & Io & Iv & Is & Rc & Rb & Rp & Rn & Rs & R1 & Rov).
pose proof SIDE as (AL & Apos & Dpos & _ & OWN & SEP).
unfold int31, BITS_BUF_MAX, BITS_SIZEOF in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh []) by exact I.
unfold bits_cells in OBJ.
ato 0x97b80. rewrite sx32_small by (unfold int31; lia). rewrite OWN1.
ato 0x67f8c.
apply evt_done. do 2 eexists. reflexivity.
Qed.

Lemma read_from_big_w3 : forall (q : Z) (rj : list byte) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s4 s6 s7 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
length rj = 16%nat -> rw_cells bsegs m A (bits_cells D b rj) -> A mod 8 = 0 -> 0 < A -> 0 < q < 2^63 -> 0 <= len < 2^31 ->
aobj bsegs m A 48 -> lo <= usp - 80 -> SH_HI <= lo -> usp < 2^63 -> A + 48 <= lo -> (A + 48 <= SH_LO \/ SH_HI <= A) -> mem_inv bsegs m ->
s6 = Z_to_bv 64 (Z.shiftr (A + 28) 3 + SHB) -> s7 = Z_to_bv 64 (Z.shiftr A 3 + SHB) ->
evt bsegs (fun ms' => exists (a1' : word) (m1 : mem),
ms' = MS (mkR (Z_to_bv 64 RA_rf_realloc) (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 P)
(Z_to_bv 64 q) a1' a2 a3 a4 a5 a6 a7
(Z_to_bv 64 len) (Z_to_bv 64 (A + 28)) s4 (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_readfrom_join) fc None m1 (seg_rom bsegs)
/\ munch [(A, A + 48)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 A (bits_cells q (mkBits (sb_chars b) (sb_data b) (sb_nbBits b) (sb_charPtr b) (sb_bitPtr b) (sb_owner b) (sb_overflow b) len) rj))
(MS (mkR (Z_to_bv 64 RA_rf_realloc) (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 P) (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 len) (Z_to_bv 64 (A + 28)) s4 (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_rf_realloc)) fc None m (seg_rom bsegs)).

Proof.
intros until m. intros Lrj OBJ AL Apos Hq Hlen OBA LO LOS SPH ALO ASH MI -> ->.
unfold A_readfrom_join, RA_rf_realloc in *.
replace (ret_pc (Z_to_bv 64 0x97ba0)) with (Z_to_bv 64 0x97ba0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [(A, A + 48)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(A, A + 48)]) by (cbn; split; [exact ASH| exact I]).
unfold bits_cells in OBJ.
ato 0x97ba0. astep. sh_if.
ato 0x979f0.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
unfold bits_cells. cbn [sb_nbBits sb_charPtr sb_bitPtr sb_owner sb_overflow sb_buf_size]. exact OBJ.
Qed.
End Big.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_wrap_fprintf : Z := 0x56c1c.
Definition e_wrap_realloc : Z := 0x67ea0.
Definition RA_rf_fprintf : Z := 0x97848.
Definition RA_rf_realloc : Z := 0x97880.
Definition RF_GOT_STDERR : Z := 0xf44f8.
Definition RF_STDERR_VAR : Z := 0xf3790.
Definition RF_FMT_NOTIFY : Z := 0x23540.
Definition RF_MSG_LARGER : Z := 0x23320.

Definition rf_frame (j0 : list byte) (c7 c6 c5 c4 c3 c2 c1 c0 cra : word) : list cell :=
[CB 8 j0; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra].

Section Big.
Context {ptr : Type}.
Variables (A P D len usp lo : Z) (pb : list byte) (b : bits_st ptr).
Variables (gp tp s8 s9 s10 s11 : word).

Lemma read_from_big_w1 : forall (errf : Z) (ra t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
bits_rep asegs m A D b -> bits_ok b -> 0 <= len < 2^31 -> sb_buf_size b < len ->
aobj asegs m A 48 -> aobj asegs m RF_STDERR_VAR 8 ->
ro_cells asegs m RF_GOT_STDERR [C8 (Z_to_bv 64 RF_STDERR_VAR)] -> ro_cells asegs m RF_STDERR_VAR [C8 (Z_to_bv 64 errf)] ->
stk asegs m lo usp -> lo <= usp - 80 -> SH_HI <= lo -> usp < 2^63 -> A + 48 <= lo -> D + sb_buf_size b <= lo ->
client_consts m -> mem_inv asegs m ->
evt asegs (fun ms' => exists (a3' a4' : word) (j0 : list byte) (m1 : mem),
ms' = MS (mkR (Z_to_bv 64 RA_rf_fprintf) (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 P)
(Z_to_bv 64 errf) (Z_to_bv 64 RF_FMT_NOTIFY) (Z_to_bv 64 RF_MSG_LARGER) a3' a4' a5 a6 a7
(Z_to_bv 64 len) (Z_to_bv 64 (A + 28)) (Z_to_bv 64 errf) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.shiftr (A + 28) 3 + SHB)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_wrap_fprintf) fc None m1 (seg_rom asegs)
/\ munch [(usp + -80, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -80)
/\ rw_cells asegs m1 (usp + -80) (rf_frame j0 s7 s6 s5 s4 s3 s2 s1 s0 ra) /\ bits_rep asegs m1 A D b)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 P) (Z_to_bv 64 len) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_bits_read_from) fc None m (seg_rom asegs)).
Proof.
intros until m. intros REP OK Hlen BIG OBA OBV GOTE VARE ST LO LOS SPH ALO DLO CC MI.
destruct CC as (G1 & G2 & _).
unfold A_speex_bits_read_from, e_wrap_fprintf, RA_rf_fprintf, RF_GOT_STDERR, RF_STDERR_VAR, RF_FMT_NOTIFY, RF_MSG_LARGER, rf_frame,
g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
pose proof REP as ((rj & Lrj & OBJ) & (bs & ARR & Hbs) & SIDE).
pose proof (bits_ints A D b OK SIDE) as (In & Ic & Ib & Io & Iv & Is & Rc & Rb & Rp & Rn & Rs & R1 & Rov).
pose proof SIDE as (AL & Apos & Dpos & _ & OWN & SEP).
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. lia. }
unfold int31, BITS_BUF_MAX, BITS_SIZEOF in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (u8arr_bound _ _ _ _ ARR) as DB.
pose proof ST as (STa & STb & _).
assert (V8 : 997264 mod 8 = 0) by reflexivity.
pose proof (munch_refl [(usp + -80, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -80, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 80%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 80 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
unfold bits_cells in OBJ.
ato 0x9770c. rewrite sx32_small by (unfold int31; lia).
astep. sh_if.
ato 0x56c1c.
apply evt_done. do 4 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR|].
exact (conj (ex_intro _ rj (conj Lrj OBJ)) (conj (ex_intro _ bs (conj ARR Hbs)) SIDE)).
Qed.

Lemma read_from_big_w2 : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s4 s6 s7 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
bits_rep asegs m A D b -> bits_ok b -> sb_owner b = 1 -> 0 <= len < 2^31 ->
aobj asegs m A 48 -> lo <= usp - 80 -> SH_HI <= lo -> usp < 2^63 -> A + 48 <= lo -> mem_inv asegs m ->
evt asegs (fun ms' => exists (a2' a3' : word),
ms' = MS (mkR (Z_to_bv 64 RA_rf_realloc) (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 P)
(Z_to_bv 64 D) (Z_to_bv 64 len) a2' a3' a4 a5 a6 a7
(Z_to_bv 64 len) (Z_to_bv 64 (A + 28)) s4 (Z_to_bv 64 SHB) s6 (Z_to_bv 64 (Z.shiftr A 3 + SHB)) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_wrap_realloc) fc None m (seg_rom asegs))
(MS (mkR (Z_to_bv 64 RA_rf_fprintf) (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 len) (Z_to_bv 64 (A + 28)) s4 (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_rf_fprintf)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros REP OK OWN1 Hlen OBA LO LOS SPH ALO MI.
unfold e_wrap_realloc, RA_rf_fprintf, RA_rf_realloc in *.
replace (ret_pc (Z_to_bv 64 0x97848)) with (Z_to_bv 64 0x97848) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof REP as ((rj & Lrj & OBJ) & (bs & ARR & Hbs) & SIDE).
pose proof (bits_ints A D b OK SIDE) as (In & Ic & Ib & Io & Iv & Is & Rc & Rb & Rp & Rn & Rs & R1 & Rov).
pose proof SIDE as (AL & Apos & Dpos & _ & OWN & SEP).
unfold int31, BITS_BUF_MAX, BITS_SIZEOF in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh []) by exact I.
unfold bits_cells in OBJ.
ato 0x97860. rewrite sx32_small by (unfold int31; lia). rewrite OWN1.
ato 0x67ea0.
apply evt_done. do 2 eexists. reflexivity.
Qed.

Lemma read_from_big_w3 : forall (q : Z) (rj : list byte) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s4 s6 s7 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
length rj = 16%nat -> rw_cells asegs m A (bits_cells D b rj) -> A mod 8 = 0 -> 0 < A -> 0 < q < 2^63 -> 0 <= len < 2^31 ->
aobj asegs m A 48 -> lo <= usp - 80 -> SH_HI <= lo -> usp < 2^63 -> A + 48 <= lo -> (A + 48 <= SH_LO \/ SH_HI <= A) -> mem_inv asegs m ->
s6 = Z_to_bv 64 (Z.shiftr (A + 28) 3 + SHB) -> s7 = Z_to_bv 64 (Z.shiftr A 3 + SHB) ->
evt asegs (fun ms' => exists (a1' : word) (m1 : mem),
ms' = MS (mkR (Z_to_bv 64 RA_rf_realloc) (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 P)
(Z_to_bv 64 q) a1' a2 a3 a4 a5 a6 a7
(Z_to_bv 64 len) (Z_to_bv 64 (A + 28)) s4 (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_readfrom_join) fc None m1 (seg_rom asegs)
/\ munch [(A, A + 48)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 A (bits_cells q (mkBits (sb_chars b) (sb_data b) (sb_nbBits b) (sb_charPtr b) (sb_bitPtr b) (sb_owner b) (sb_overflow b) len) rj))
(MS (mkR (Z_to_bv 64 RA_rf_realloc) (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 P) (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 len) (Z_to_bv 64 (A + 28)) s4 (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_rf_realloc)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros Lrj OBJ AL Apos Hq Hlen OBA LO LOS SPH ALO ASH MI -> ->.
unfold A_readfrom_join, RA_rf_realloc in *.
replace (ret_pc (Z_to_bv 64 0x97880)) with (Z_to_bv 64 0x97880) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [(A, A + 48)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(A, A + 48)]) by (cbn; split; [exact ASH| exact I]).
unfold bits_cells in OBJ.
ato 0x97880. astep. sh_if.
ato 0x97710.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
unfold bits_cells. cbn [sb_nbBits sb_charPtr sb_bitPtr sb_owner sb_overflow sb_buf_size]. exact OBJ.
Qed.
End Big.
