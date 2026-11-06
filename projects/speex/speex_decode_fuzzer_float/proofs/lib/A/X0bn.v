(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg X1df X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05q X05l X089.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X12b X0z5.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0z5.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation mem := (word -> option byte).

Definition scb_par_cells (ssz nb scb sbits hs : Z) : list cell :=
[C4 (Z_to_bv 64 ssz); C4 (Z_to_bv 64 nb); C8 (Z_to_bv 64 scb); C4 (Z_to_bv 64 sbits); C4 (Z_to_bv 64 hs)].

Definition A_scb : Z := 0xb22a8.
Definition RA_scb_pois1 : Z := 0xb23dc.
Definition RA_scb_pois2 : Z := 0xb240c.
Definition A_scb_epi : Z := 0xb26e0.
Definition RA_scb_unpois : Z := 0xb26ec.
Definition e_alloca_poison : Z := 0x51e24.
Definition e_allocas_unpoison : Z := 0x51f50.

Definition scb_frame (k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 : cell) (r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra : word) : list cell :=
[k0; k8; k16; k24; k32; k40; k48; k56; k64; k72; k80; C8 r11; C8 r10; C8 r9; C8 r8; C8 r7; C8 r6; C8 r5; C8 r4; C8 r3; C8 r2; C8 r1; C8 r0; C8 rra].

Lemma scb_w1 : forall (INN PAR A ssz nb scb sbits hs usp lo : Z) (ra gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
ro_cells bsegs m PAR (scb_par_cells ssz nb scb sbits hs) -> aobj bsegs m PAR 24 -> PAR mod 8 = 0 -> 0x10000 <= PAR -> PAR + 24 <= IMG_TOP_B ->
1 <= ssz <= 20 -> In nb [2; 4; 5; 8] -> 0 <= scb < 2^47 -> 0 <= hs <= 1 ->
stk bsegs m lo usp -> lo <= usp - 4384 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
client_constsB m -> mem_inv bsegs m ->
evt bsegs (fun ms' => exists (a2' : word) (j8 j16 j40 j56 j72 j80 jh : list byte) (m1 : mem),
ms' = MS (mkR (Z_to_bv 64 RA_scb_pois1) (Z_to_bv 64 (usp + -288)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 (usp + -256)) (Z_to_bv 64 (4 * nb)) a2' (Z_to_bv 64 A) a4 a5 a6 a7
(Z_to_bv 64 INN) (Z_to_bv 64 96) (Z_to_bv 64 (usp + -288)) (Z_to_bv 64 A) (Z_to_bv 64 PAR) (Z_to_bv 64 (4 * nb)) (Z_to_bv 64 SHB) (Z_to_bv 64 ssz)
s10 (Z_to_bv 64 scb) t3 t4 t5 t6)
F (Z_to_bv 64 e_alloca_poison) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -4288, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -288)
/\ rw_cells bsegs m1 (usp + -192) (scb_frame (C8 (Z_to_bv 64 0)) (CB 8 j8) (CB 8 j16) (C8 (Z_to_bv 64 hs)) (C8 (Z_to_bv 64 nb)) (CB 8 j40) (C8 (Z_to_bv 64 (usp + -256))) (CB 8 j56) (C8 (Z_to_bv 64 0)) (CB 8 j72) (CB 8 j80) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
/\ rw_cells bsegs m1 (usp + -288) [CB 96 jh])
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 INN) (Z_to_bv 64 PAR) a2 (Z_to_bv 64 A) a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_scb) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros RP OBP P8 PLO PHI HS HNB HSCB HHS ST LO LOS SPH U32 (G1c & G2c & _) MI.
unfold A_scb, scb_par_cells, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. unfold IMG_TOP_B in PHI.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -4288, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -4288, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 192%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 192 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xb22e8. astep.
rewrite (land_m32_al (usp + -192)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
carve_frame 96%nat ST. rename FR0 into HULL1.
carve_frame 3992%nat ST. rename FR0 into JK1.
carve_frame 8%nat ST. rename FR0 into P1.
apply (rw_cells_split_CB bsegs _ _ [] 8 _ [] [8]%nat) in P1; [| reflexivity]. cbn [mk_CB_cells app] in P1.
assert (NBR : 2 <= nb <= 8) by (clear - HNB; cbn [In] in HNB; lia).
bato 0xb2358. rewrite !sx32_small by (unfold int31; lia).
bato 0xb237c. rewrite !sx32_small by (unfold int31; lia).
cbn [In] in HNB. destruct HNB as [<-|[<-|[<-|[<-|[]]]]].
all: bato 0xb23b0; alits; astep;
replace (usp + -192 - 96) with (usp + -288) by lia; rewrite ?Z.mod_small by lia;
astep; rewrite (land_m32_al (usp + -288)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]);
astep; astep; replace (usp + -192 - 4096) with (usp + -4288) by lia;
astep; astep; sh_if;
ato 0x51e24;
release_frame P1 ST (usp + -4280); release_frame JK1 ST (usp + -288);
apply evt_done; unfold scb_frame, RA_scb_pois1, e_alloca_poison; do 9 eexists; (split; [reflexivity|]);
(split; [exact MU|]); (split; [exact WM|]); (split; [exact MI|]); (split; [exact ST|]); (split; [exact FR| exact HULL1]).
Qed.

Section W2.
Variables (INN PAR A ssz nb scb usp lo : Z).
Variables gp tp : word.

Lemma scb_w2 : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s10 : word) (c0 c24 c32 c48 : word) (j8 j16 j40 j56 j72 j80 : list byte) (c64 r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells bsegs m (usp + -192) (scb_frame (C8 c0) (CB 8 j8) (CB 8 j16) (C8 c24) (C8 c32) (CB 8 j40) (C8 c48) (CB 8 j56) (C8 c64) (CB 8 j72) (CB 8 j80) r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra) ->
stk bsegs m lo (usp + -288) -> lo <= usp - 4384 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 -> mem_inv bsegs m ->
evt bsegs (fun ms' => exists (jh : list byte) (m1 : mem),
ms' = MS (mkR (Z_to_bv 64 RA_scb_pois2) (Z_to_bv 64 (usp + -384)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 (usp + -352)) (Z_to_bv 64 (4 * nb)) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 INN) (Z_to_bv 64 (usp + -384)) (Z_to_bv 64 (usp + -352)) (Z_to_bv 64 A) (Z_to_bv 64 PAR) (Z_to_bv 64 (4 * nb)) (Z_to_bv 64 SHB) (Z_to_bv 64 ssz)
s10 (Z_to_bv 64 scb) t3 t4 t5 t6)
F (Z_to_bv 64 e_alloca_poison) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -4384, usp + -288); (usp + -128, usp + -120)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -384)
/\ rw_cells bsegs m1 (usp + -192) (scb_frame (C8 c0) (CB 8 j8) (CB 8 j16) (C8 c24) (C8 c32) (CB 8 j40) (C8 c48) (CB 8 j56) (C8 (Z_to_bv 64 (usp + -288))) (CB 8 j72) (CB 8 j80) r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra)
/\ rw_cells bsegs m1 (usp + -384) [CB 96 jh])
(MS (mkR (Z_to_bv 64 RA_scb_pois1) (Z_to_bv 64 (usp + -288)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 INN) (Z_to_bv 64 96) (Z_to_bv 64 (usp + -288)) (Z_to_bv 64 A) (Z_to_bv 64 PAR) (Z_to_bv 64 (4 * nb)) (Z_to_bv 64 SHB) (Z_to_bv 64 ssz)
s10 (Z_to_bv 64 scb) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_scb_pois1)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FR ST LO LOS SPH U32 MI.
unfold RA_scb_pois1, RA_scb_pois2, e_alloca_poison, scb_frame in *.
replace (ret_pc (Z_to_bv 64 0xb23dc)) with (Z_to_bv 64 0xb23dc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -4384, usp + -288); (usp + -128, usp + -120)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -4384, usp + -288); (usp + -128, usp + -120)]) by (cbn; unfold SH_LO, SH_HI; lia).
astep.
carve_frame 96%nat ST. rename FR0 into HULL2.
carve_frame 3992%nat ST. rename FR0 into JK1.
carve_frame 8%nat ST. rename FR0 into P1.
apply (rw_cells_split_CB bsegs _ _ [] 8 _ [] [8]%nat) in P1; [| reflexivity]. cbn [mk_CB_cells app] in P1.
astep. replace (usp + -288 - 96) with (usp + -384) by lia. rewrite ?Z.mod_small by lia.
astep. rewrite (land_m32_al (usp + -384)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
astep. astep. replace (usp + -288 - 4096) with (usp + -4384) by lia.
astep. astep. sh_if.
ato 0x51e24.
release_frame P1 ST (usp + -4376). release_frame JK1 ST (usp + -384).
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR| exact HULL2].
Qed.

Lemma scb_w5 : forall (top : Z) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 sp : word) (c0 c16 c24 c32 c40 c48 c56 : word) (j8 j72 j80 : list byte)
(r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells bsegs m (usp + -192) (scb_frame (C8 c0) (CB 8 j8) (C8 c16) (C8 c24) (C8 c32) (C8 c40) (C8 c48) (C8 c56) (C8 (Z_to_bv 64 top)) (CB 8 j72) (CB 8 j80) r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra) ->
lo <= usp - 4384 -> SH_HI <= lo -> usp < 2^63 -> mem_inv bsegs m ->
evt bsegs (fun ms' =>
ms' = MS (mkR (Z_to_bv 64 RA_scb_unpois) sp gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 top) (Z_to_bv 64 (usp + -128)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_allocas_unpoison) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192)) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_scb_epi) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FR LO LOS SPH MI.
unfold RA_scb_unpois, A_scb_epi, e_allocas_unpoison, scb_frame in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
ato 0x51f50. apply evt_done. reflexivity.
Qed.

Lemma scb_w6 : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 sp : word) (c0 c16 c24 c32 c40 c48 c56 c64 : word) (j8 j72 j80 jh1 jh2 : list byte)
(r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells bsegs m (usp + -192) (scb_frame (C8 c0) (CB 8 j8) (C8 c16) (C8 c24) (C8 c32) (C8 c40) (C8 c48) (C8 c56) (C8 c64) (CB 8 j72) (CB 8 j80) r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra) ->
rw_cells bsegs m (usp + -288) [CB 96 jh1] -> rw_cells bsegs m (usp + -384) [CB 96 jh2] ->
stk bsegs m lo (usp + -384) ->
lo <= usp - 4384 -> SH_HI <= lo -> usp < 2^63 -> mem_inv bsegs m ->
evt bsegs (fun ms' =>
ms' = MS (mkR rra (Z_to_bv 64 usp) gp tp t0 t1 t2 r0 r1 a0 a1 a2 a3 a4 a5 a6 a7 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 t3 t4 t5 t6)
F (ret_pc rra) fc None m (seg_rom bsegs)
/\ stk bsegs m lo usp)
(MS (mkR (Z_to_bv 64 RA_scb_unpois) sp gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192)) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_scb_unpois)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FR H1 H2 ST LO LOS SPH MI.
unfold RA_scb_unpois, scb_frame in *.
replace (ret_pc (Z_to_bv 64 0xb26ec)) with (Z_to_bv 64 0xb26ec) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
ato 0xb2724. astep.
release_frame H2 ST (usp + -288). release_frame H1 ST (usp + -192). release_frame FR ST usp.
astep. apply evt_done. split; [reflexivity| exact ST].
Qed.
End W2.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation mem := (word -> option byte).

Definition scb_par_cells (ssz nb scb sbits hs : Z) : list cell :=
[C4 (Z_to_bv 64 ssz); C4 (Z_to_bv 64 nb); C8 (Z_to_bv 64 scb); C4 (Z_to_bv 64 sbits); C4 (Z_to_bv 64 hs)].

Definition A_scb : Z := 0xac694.
Definition RA_scb_pois1 : Z := 0xac7ac.
Definition RA_scb_pois2 : Z := 0xac7dc.
Definition A_scb_epi : Z := 0xaca28.
Definition RA_scb_unpois : Z := 0xaca34.

Definition scb_frame (k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 : cell) (r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra : word) : list cell :=
[k0; k8; k16; k24; k32; k40; k48; k56; k64; k72; k80; C8 r11; C8 r10; C8 r9; C8 r8; C8 r7; C8 r6; C8 r5; C8 r4; C8 r3; C8 r2; C8 r1; C8 r0; C8 rra].

Lemma scb_w1 : forall (INN PAR A ssz nb scb sbits hs usp lo : Z) (ra gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
ro_cells asegs m PAR (scb_par_cells ssz nb scb sbits hs) -> aobj asegs m PAR 24 -> PAR mod 8 = 0 -> 0x10000 <= PAR -> PAR + 24 <= IMG_TOP ->
1 <= ssz <= 20 -> In nb [2; 4; 5; 8] -> 0 <= scb < 2^47 ->
stk asegs m lo usp -> lo <= usp - 4384 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
client_consts m -> mem_inv asegs m ->
evt asegs (fun ms' => exists (a2' : word) (j8 j16 j24 j48 j72 j80 jh : list byte) (m1 : mem),
ms' = MS (mkR (Z_to_bv 64 RA_scb_pois1) (Z_to_bv 64 (usp + -288)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 (usp + -256)) (Z_to_bv 64 (4 * nb)) a2' (Z_to_bv 64 A) a4 a5 a6 a7
(Z_to_bv 64 INN) (Z_to_bv 64 nb) (Z_to_bv 64 96) (Z_to_bv 64 (usp + -288)) (Z_to_bv 64 PAR) (Z_to_bv 64 (4 * nb)) (Z_to_bv 64 ssz) (Z_to_bv 64 SHB)
(Z_to_bv 64 ssz) (Z_to_bv 64 scb) t3 t4 t5 t6)
F (Z_to_bv 64 e_alloca_poison) fc None m1 (seg_rom asegs)
/\ munch [(usp + -4288, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -288)
/\ rw_cells asegs m1 (usp + -192) (scb_frame (C8 (Z_to_bv 64 0)) (CB 8 j8) (CB 8 j16) (CB 8 j24) (C8 (Z_to_bv 64 (usp + -256))) (C8 (Z_to_bv 64 nb)) (CB 8 j48) (C8 (Z_to_bv 64 A)) (C8 (Z_to_bv 64 0)) (CB 8 j72) (CB 8 j80) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
/\ rw_cells asegs m1 (usp + -288) [CB 96 jh])
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 INN) (Z_to_bv 64 PAR) a2 (Z_to_bv 64 A) a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_scb) fc None m (seg_rom asegs)).
Proof.
intros until m. intros RP OBP P8 PLO PHI HS HNB HSCB ST LO LOS SPH U32 (G1c & G2c & _) MI.
unfold A_scb, scb_par_cells, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. unfold IMG_TOP in PHI.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -4288, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -4288, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 192%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 192 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xac6d4. astep.
rewrite (land_m32_al (usp + -192)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
carve_frame 96%nat ST. rename FR0 into HULL1.
carve_frame 3992%nat ST. rename FR0 into JK1.
carve_frame 8%nat ST. rename FR0 into P1.
apply (rw_cells_split_CB asegs _ _ [] 8 _ [] [8]%nat) in P1; [| reflexivity]. cbn [mk_CB_cells app] in P1.
cbn [In] in HNB. destruct HNB as [<-|[<-|[<-|[<-|[]]]]].
all: ato 0xac740; rewrite !zx32_small by lia; rewrite ?unsigned_small64 by lia; rewrite ?Z.add_0_r; rewrite ?swrap32_small by lia;
ato 0xac780; alits; astep;
replace (usp + -192 - 96) with (usp + -288) by lia; rewrite ?Z.mod_small by lia;
astep; rewrite (land_m32_al (usp + -288)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]);
astep; astep; replace (usp + -192 - 4096) with (usp + -4288) by lia;
astep; astep; sh_if;
ato 0x51d38;
release_frame P1 ST (usp + -4280); release_frame JK1 ST (usp + -288);
apply evt_done; unfold scb_frame, RA_scb_pois1, e_alloca_poison; do 9 eexists; (split; [reflexivity|]);
(split; [exact MU|]); (split; [exact WM|]); (split; [exact MI|]); (split; [exact ST|]); (split; [exact FR| exact HULL1]).
Qed.

Section W2.
Variables (INN PAR A ssz nb scb usp lo : Z).
Variables gp tp : word.

Lemma scb_w2 : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (c0 c32 c40 c56 : word) (j8 j16 j24 j48 j72 j80 : list byte) (c64 r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells asegs m (usp + -192) (scb_frame (C8 c0) (CB 8 j8) (CB 8 j16) (CB 8 j24) (C8 c32) (C8 c40) (CB 8 j48) (C8 c56) (C8 c64) (CB 8 j72) (CB 8 j80) r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra) ->
stk asegs m lo (usp + -288) -> lo <= usp - 4384 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 -> mem_inv asegs m ->
evt asegs (fun ms' => exists (jh : list byte) (m1 : mem),
ms' = MS (mkR (Z_to_bv 64 RA_scb_pois2) (Z_to_bv 64 (usp + -384)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 (usp + -352)) (Z_to_bv 64 (4 * nb)) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 INN) (Z_to_bv 64 nb) (Z_to_bv 64 (usp + -384)) (Z_to_bv 64 (usp + -288)) (Z_to_bv 64 PAR) (Z_to_bv 64 (4 * nb)) (Z_to_bv 64 ssz) (Z_to_bv 64 SHB)
(Z_to_bv 64 ssz) (Z_to_bv 64 scb) t3 t4 t5 t6)
F (Z_to_bv 64 e_alloca_poison) fc None m1 (seg_rom asegs)
/\ munch [(usp + -4384, usp + -288); (usp + -144, usp + -120)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -384)
/\ rw_cells asegs m1 (usp + -192) (scb_frame (C8 c0) (CB 8 j8) (CB 8 j16) (CB 8 j24) (C8 c32) (C8 c40) (C8 (Z_to_bv 64 (usp + -352))) (C8 c56) (C8 (Z_to_bv 64 (usp + -288))) (CB 8 j72) (CB 8 j80) r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra)
/\ rw_cells asegs m1 (usp + -384) [CB 96 jh])
(MS (mkR (Z_to_bv 64 RA_scb_pois1) (Z_to_bv 64 (usp + -288)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 INN) (Z_to_bv 64 nb) (Z_to_bv 64 96) (Z_to_bv 64 (usp + -288)) (Z_to_bv 64 PAR) (Z_to_bv 64 (4 * nb)) (Z_to_bv 64 ssz) (Z_to_bv 64 SHB)
(Z_to_bv 64 ssz) (Z_to_bv 64 scb) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_scb_pois1)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FR ST LO LOS SPH U32 MI.
unfold RA_scb_pois1, RA_scb_pois2, e_alloca_poison, scb_frame in *.
replace (ret_pc (Z_to_bv 64 0xac7ac)) with (Z_to_bv 64 0xac7ac) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -4384, usp + -288); (usp + -144, usp + -120)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -4384, usp + -288); (usp + -144, usp + -120)]) by (cbn; unfold SH_LO, SH_HI; lia).
astep.
carve_frame 96%nat ST. rename FR0 into HULL2.
carve_frame 3992%nat ST. rename FR0 into JK1.
carve_frame 8%nat ST. rename FR0 into P1.
apply (rw_cells_split_CB asegs _ _ [] 8 _ [] [8]%nat) in P1; [| reflexivity]. cbn [mk_CB_cells app] in P1.
astep. replace (usp + -288 - 96) with (usp + -384) by lia. rewrite ?Z.mod_small by lia.
astep. rewrite (land_m32_al (usp + -384)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
astep. astep. replace (usp + -288 - 4096) with (usp + -4384) by lia.
astep. astep. sh_if.
ato 0x51d38.
release_frame P1 ST (usp + -4376). release_frame JK1 ST (usp + -384).
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR| exact HULL2].
Qed.

Lemma scb_w5 : forall (top : Z) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 sp : word) (c0 c8 c16 c24 c32 c40 c48 c56 : word) (j72 j80 : list byte)
(r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells asegs m (usp + -192) (scb_frame (C8 c0) (C8 c8) (C8 c16) (C8 c24) (C8 c32) (C8 c40) (C8 c48) (C8 c56) (C8 (Z_to_bv 64 top)) (CB 8 j72) (CB 8 j80) r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra) ->
lo <= usp - 4384 -> SH_HI <= lo -> usp < 2^63 -> mem_inv asegs m ->
evt asegs (fun ms' =>
ms' = MS (mkR (Z_to_bv 64 RA_scb_unpois) sp gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 top) (Z_to_bv 64 (usp + -128)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_allocas_unpoison) fc None m (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192)) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_scb_epi) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FR LO LOS SPH MI.
unfold RA_scb_unpois, A_scb_epi, e_allocas_unpoison, scb_frame in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
ato 0x51e64. apply evt_done. reflexivity.
Qed.

Lemma scb_w6 : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 sp : word) (c0 c8 c16 c24 c32 c40 c48 c56 c64 : word) (j72 j80 jh1 jh2 : list byte)
(r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells asegs m (usp + -192) (scb_frame (C8 c0) (C8 c8) (C8 c16) (C8 c24) (C8 c32) (C8 c40) (C8 c48) (C8 c56) (C8 c64) (CB 8 j72) (CB 8 j80) r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra) ->
rw_cells asegs m (usp + -288) [CB 96 jh1] -> rw_cells asegs m (usp + -384) [CB 96 jh2] ->
stk asegs m lo (usp + -384) ->
lo <= usp - 4384 -> SH_HI <= lo -> usp < 2^63 -> mem_inv asegs m ->
evt asegs (fun ms' =>
ms' = MS (mkR rra (Z_to_bv 64 usp) gp tp t0 t1 t2 r0 r1 a0 a1 a2 a3 a4 a5 a6 a7 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 t3 t4 t5 t6)
F (ret_pc rra) fc None m (seg_rom asegs)
/\ stk asegs m lo usp)
(MS (mkR (Z_to_bv 64 RA_scb_unpois) sp gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192)) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_scb_unpois)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FR H1 H2 ST LO LOS SPH MI.
unfold RA_scb_unpois, scb_frame in *.
replace (ret_pc (Z_to_bv 64 0xaca34)) with (Z_to_bv 64 0xaca34) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
ato 0xaca6c. astep.
release_frame H2 ST (usp + -288). release_frame H1 ST (usp + -192). release_frame FR ST usp.
astep. apply evt_done. split; [reflexivity| exact ST].
Qed.
End W2.
