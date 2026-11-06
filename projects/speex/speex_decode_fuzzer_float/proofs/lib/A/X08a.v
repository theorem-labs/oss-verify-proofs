(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg X1df X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X089.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section L1.
Variables (IQ AK usp lo : Z).
Variables ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m : word -> option byte.

Lemma l2l8_w1 :
stk asegs m lo usp -> lo <= usp - 4384 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
client_consts m -> mem_inv asegs m ->
evt asegs (fun ms' => exists (j1 j2 jh : list byte) (m1 : word -> option byte),
ms' = MS (mkR (Z_to_bv 64 RA_l2l_pois1) (Z_to_bv 64 (usp + -288)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -128))
(Z_to_bv 64 (usp + -256)) (Z_to_bv 64 72) (Z_to_bv 64 96) (Z_to_bv 64 68719476720) (Z_to_bv 64 (-1)) a5 a6 a7
(Z_to_bv 64 8) (Z_to_bv 64 (usp + -256)) (Z_to_bv 64 16) (Z_to_bv 64 AK) (Z_to_bv 64 IQ) (Z_to_bv 64 SHB) (Z_to_bv 64 4)
(Z_to_bv 64 (usp + -288)) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_alloca_poison) fc None m1 (seg_rom asegs)
/\ munch [(usp + -4224, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -288)
/\ rw_cells asegs m1 (usp + -128) (l2l_frame (Z_to_bv 64 0) j1 j2 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
/\ rw_cells asegs m1 (usp + -288) [CB 160 jh])
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 IQ) (Z_to_bv 64 AK) (Z_to_bv 64 8) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_lsp_to_lpc) fc None m (seg_rom asegs)).
Proof.
intros ST LO LOS SPH U32 (G1 & G2 & _) MI.
unfold A_lsp_to_lpc, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -4224, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -4224, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 128%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 128 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xa9630.
rewrite (land_m32_al (usp + -128)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
carve_frame 160%nat ST. rename FR0 into HULL1.
carve_frame 3928%nat ST. rename FR0 into JK1.
carve_frame 8%nat ST. rename FR0 into P1.
apply (rw_cells_split_CB asegs _ _ [] 8 _ [] [8]%nat) in P1; [| reflexivity]. cbn [mk_CB_cells app] in P1.
ato 0xa96a8. alits.
replace (usp + -128 - 160) with (usp + -288) by lia. rewrite Z.mod_small by lia.
rewrite (land_m32_al (usp + -288)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
astep. replace (usp + -128 - 4096) with (usp + -4224) by lia.
astep. astep. sh_if.
ato 0x51d38.
release_frame P1 ST (usp + -4216). release_frame JK1 ST (usp + -288).
apply evt_done. unfold l2l_frame, RA_l2l_pois1, e_alloca_poison. do 4 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR| exact HULL1].
Qed.
End L1.

Section L2.
Variables (IQ AK usp lo : Z).
Variables gp tp s10 s11 : word.

Lemma l2l8_w2 : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j1 j2 : list byte) (c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
rw_cells asegs m (usp + -128) (l2l_frame (Z_to_bv 64 0) j1 j2 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
lo <= usp - 4384 -> SH_HI <= lo -> usp < 2^63 -> mem_inv asegs m ->
evt asegs (fun ms' => exists (m1 : word -> option byte),
ms' = MS (mkR (Z_to_bv 64 RA_l2l_memset) (Z_to_bv 64 (usp + -288)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -128))
(Z_to_bv 64 (usp + -256)) (Z_to_bv 64 0) (Z_to_bv 64 72) a3 a4 a5 a6 a7
(Z_to_bv 64 8) (Z_to_bv 64 (usp + -256)) (Z_to_bv 64 16) (Z_to_bv 64 AK) (Z_to_bv 64 IQ) (Z_to_bv 64 SHB) (Z_to_bv 64 4)
(Z_to_bv 64 (usp + -288)) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_asan_memset) fc None m1 (seg_rom asegs)
/\ munch [(usp + -128, usp + -120)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 (usp + -128) (l2l_frame (Z_to_bv 64 (usp + -288)) j1 j2 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra))
(MS (mkR (Z_to_bv 64 RA_l2l_pois1) (Z_to_bv 64 (usp + -288)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -128)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 8) (Z_to_bv 64 (usp + -256)) (Z_to_bv 64 16) (Z_to_bv 64 AK) (Z_to_bv 64 IQ) (Z_to_bv 64 SHB) (Z_to_bv 64 4)
(Z_to_bv 64 (usp + -288)) s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_l2l_pois1)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FR LO LOS SPH MI.
unfold RA_l2l_pois1, RA_l2l_memset, e_asan_memset, l2l_frame in *.
replace (ret_pc (Z_to_bv 64 0xa96c4)) with (Z_to_bv 64 0xa96c4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [(usp + -128, usp + -120)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -128, usp + -120)]) by (cbn; unfold SH_LO, SH_HI; lia).
ato 0xa96ec. alits. ato 0x667b0.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact FR].
Qed.

Lemma l2l8_w3 : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
stk asegs m lo (usp + -288) -> lo <= usp - 4384 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 -> mem_inv asegs m ->
evt asegs (fun ms' => exists (jh : list byte) (m1 : word -> option byte),
ms' = MS (mkR (Z_to_bv 64 RA_l2l_pois2) (Z_to_bv 64 (usp + -384)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -128))
(Z_to_bv 64 (usp + -352)) (Z_to_bv 64 32) (Z_to_bv 64 32) (Z_to_bv 64 68719476720) a4 a5 a6 a7
(Z_to_bv 64 8) (Z_to_bv 64 (usp + -256)) (Z_to_bv 64 (usp + -352)) (Z_to_bv 64 AK) (Z_to_bv 64 IQ) (Z_to_bv 64 SHB) (Z_to_bv 64 4)
(Z_to_bv 64 8) (Z_to_bv 64 (usp + -384)) s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_alloca_poison) fc None m1 (seg_rom asegs)
/\ munch [(usp + -4384, usp + -288)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -384)
/\ rw_cells asegs m1 (usp + -384) [CB 96 jh])
(MS (mkR (Z_to_bv 64 RA_l2l_memset) (Z_to_bv 64 (usp + -288)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -128)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 8) (Z_to_bv 64 (usp + -256)) (Z_to_bv 64 16) (Z_to_bv 64 AK) (Z_to_bv 64 IQ) (Z_to_bv 64 SHB) (Z_to_bv 64 4)
(Z_to_bv 64 (usp + -288)) s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_l2l_memset)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros ST LO LOS SPH U32 MI.
unfold RA_l2l_memset, RA_l2l_pois2, e_alloca_poison in *.
replace (ret_pc (Z_to_bv 64 0xa96f0)) with (Z_to_bv 64 0xa96f0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -4384, usp + -288)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -4384, usp + -288)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 96%nat ST. rename FR into HULL2.
carve_frame 3992%nat ST. rename FR into JK1.
carve_frame 8%nat ST. rename FR into P1.
apply (rw_cells_split_CB asegs _ _ [] 8 _ [] [8]%nat) in P1; [| reflexivity]. cbn [mk_CB_cells app] in P1.
ato 0xa973c. alits.
replace (usp + -288 - 96) with (usp + -384) by lia. rewrite Z.mod_small by lia.
rewrite (land_m32_al (usp + -384)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
astep. replace (usp + -288 - 4096) with (usp + -4384) by lia.
astep. astep. sh_if.
ato 0x51d38.
release_frame P1 ST (usp + -4376). release_frame JK1 ST (usp + -384).
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact HULL2].
Qed.
End L2.

Section L5.
Variables (usp lo : Z).
Variables gp tp : word.

Lemma l2l8_w5 : forall (top : Z) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (sp : word)
(j1 j2 : list byte) (c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
rw_cells asegs m (usp + -128) (l2l_frame (Z_to_bv 64 top) j1 j2 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
lo <= usp - 4384 -> SH_HI <= lo -> usp < 2^63 -> mem_inv asegs m ->
evt asegs (fun ms' =>
ms' = MS (mkR (Z_to_bv 64 RA_l2l_unpois) sp gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -128))
(Z_to_bv 64 top) (Z_to_bv 64 (usp + -128)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_allocas_unpoison) fc None m (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -128)) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_l2l_epi) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FR LO LOS SPH MI.
unfold RA_l2l_unpois, A_l2l_epi, e_allocas_unpoison, l2l_frame in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
ato 0x51e64. apply evt_done. reflexivity.
Qed.

Lemma l2l8_w6 : forall (top : Z) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (sp : word)
(j1 j2 jh1 jh2 : list byte) (c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
rw_cells asegs m (usp + -128) (l2l_frame (Z_to_bv 64 top) j1 j2 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
rw_cells asegs m (usp + -288) [CB 160 jh1] -> rw_cells asegs m (usp + -384) [CB 96 jh2] ->
stk asegs m lo (usp + -384) ->
lo <= usp - 4384 -> SH_HI <= lo -> usp < 2^63 -> mem_inv asegs m ->
evt asegs (fun ms' =>
ms' = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 a0 a1 a2 a3 a4 a5 a6 a7 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 t3 t4 t5 t6)
F (ret_pc cra) fc None m (seg_rom asegs)
/\ stk asegs m lo usp)
(MS (mkR (Z_to_bv 64 RA_l2l_unpois) sp gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -128)) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_l2l_unpois)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FR H1 H2 ST LO LOS SPH MI.
unfold RA_l2l_unpois, l2l_frame in *.
replace (ret_pc (Z_to_bv 64 0xa9b20)) with (Z_to_bv 64 0xa9b20) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
ato 0xa9b58. astep.
release_frame H2 ST (usp + -288). release_frame H1 ST (usp + -128). release_frame FR ST usp.
astep. apply evt_done. split; [reflexivity| exact ST].
Qed.
End L5.
