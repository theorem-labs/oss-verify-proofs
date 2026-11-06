(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg X1df X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05l X089 X07y.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation mem := (word -> option byte).

Definition A_multicomb_e : Z := 0xa5388.
Definition RA_mc_pois : Z := 0xa5480.
Definition RA_mc_ip1 : Z := 0xa5494.
Definition RA_mc_ip2 : Z := 0xa54b8.
Definition A_mc_epi : Z := 0xa58b8.
Definition RA_mc_unpois : Z := 0xa58c4.

Definition mc_frame (top : word) (j1 j2 j3 : list byte) (f8 f7 f6 f5 f4 f3 f2 f1 f0 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) : list cell :=
[C8 top; CB 8 j1; CB 8 j2; CB 8 j3; C8 f8; C8 f7; C8 f6; C8 f5; C8 f4; C8 f3; C8 f2; C8 f1; C8 f0;
C8 c9; C8 c8; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra].

Definition mc_p2 (pitch : Z) : Z := if 40 <? pitch then 2 * pitch else - pitch.

Lemma mc_w1 : forall (EXC NE pitch usp lo : Z) (ra gp tp t0 t1 t2 s0 s1 a2 a3 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
stk asegs m lo usp -> lo <= usp - 4288 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
client_consts m -> mem_inv asegs m ->
evt asegs (fun ms' => exists (j1 j2 j3 jh : list byte) (m1 : mem),
ms' = MS (mkR (Z_to_bv 64 RA_mc_pois) (Z_to_bv 64 (usp + -896)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 (usp + -864)) (Z_to_bv 64 640) (Z_to_bv 64 68719476720) (Z_to_bv 64 640) (Z_to_bv 64 0) (Z_to_bv 64 pitch) (Z_to_bv 64 40) a7
(Z_to_bv 64 80) (Z_to_bv 64 NE) (Z_to_bv 64 EXC) (Z_to_bv 64 (usp + -864)) (Z_to_bv 64 (usp + -896)) (Z_to_bv 64 40) (Z_to_bv 64 pitch) (Z_to_bv 64 SHB)
s10 s11 t3 t4 t5 t6)
(bvmap_set 8 (fmv_s (reg_get F 10)) F) (Z_to_bv 64 e_alloca_poison) fc None m1 (seg_rom asegs)
/\ munch [(usp + -4288, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -896)
/\ rw_cells asegs m1 (usp + -192) (mc_frame (Z_to_bv 64 0) j1 j2 j3 (reg_get F 24) (reg_get F 23) (reg_get F 22) (reg_get F 21) (reg_get F 20) (reg_get F 19)
(reg_get F 18) (reg_get F 9) (reg_get F 8) s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
/\ rw_cells asegs m1 (usp + -896) [CB 704 jh])
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 EXC) (Z_to_bv 64 NE) a2 a3 (Z_to_bv 64 80) (Z_to_bv 64 pitch) (Z_to_bv 64 40) a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_multicomb_e) fc None m (seg_rom asegs)).
Proof.
intros until m. intros ST LO LOS SPH U32 (G1c & G2c & _) MI.
unfold A_multicomb_e, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -4288, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -4288, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 192%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 192 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xa53e4. astep.
rewrite (land_m32_al (usp + -192)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
carve_frame 704%nat ST. rename FR0 into HULL1.
carve_frame 3384%nat ST. rename FR0 into JK1.
carve_frame 8%nat ST. rename FR0 into P1.
apply (rw_cells_split_CB asegs _ _ [] 8 _ [] [8]%nat) in P1; [| reflexivity]. cbn [mk_CB_cells app] in P1.
ato 0xa5458. alits. astep.
replace (usp + -192 - 704) with (usp + -896) by lia. rewrite ?Z.mod_small by lia.
astep. rewrite (land_m32_al (usp + -896)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
astep. astep. replace (usp + -192 - 4096) with (usp + -4288) by lia.
astep. astep. sh_if.
ato 0x51d38.
release_frame P1 ST (usp + -4280). release_frame JK1 ST (usp + -896).
apply evt_done. unfold mc_frame, RA_mc_pois, e_alloca_poison. do 5 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR| exact HULL1].
Qed.

Section W23.
Variables (EXC NE pitch usp lo : Z).
Variables gp tp s10 s11 : word.

Lemma mc_w2 : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j1 j2 j3 : list byte) (f8 f7 f6 f5 f4 f3 f2 f1 f0 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells asegs m (usp + -192) (mc_frame (Z_to_bv 64 0) j1 j2 j3 f8 f7 f6 f5 f4 f3 f2 f1 f0 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
lo <= usp - 4288 -> SH_HI <= lo -> usp < 2^63 -> mem_inv asegs m ->
evt asegs (fun ms' => exists (m1 : mem),
ms' = MS (mkR (Z_to_bv 64 RA_mc_ip1) (Z_to_bv 64 (usp + -896)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 EXC) (Z_to_bv 64 (usp + -864)) (Z_to_bv 64 pitch) a3 a4 a5 a6 a7
(Z_to_bv 64 80) (Z_to_bv 64 NE) (Z_to_bv 64 EXC) (Z_to_bv 64 (usp + -864)) (Z_to_bv 64 (usp + -896)) (Z_to_bv 64 40) (Z_to_bv 64 pitch) (Z_to_bv 64 SHB)
s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_interp_pitch) fc None m1 (seg_rom asegs)
/\ munch [(usp + -192, usp + -184)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 (usp + -192) (mc_frame (Z_to_bv 64 (usp + -896)) j1 j2 j3 f8 f7 f6 f5 f4 f3 f2 f1 f0 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra))
(MS (mkR (Z_to_bv 64 RA_mc_pois) (Z_to_bv 64 (usp + -896)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 80) (Z_to_bv 64 NE) (Z_to_bv 64 EXC) (Z_to_bv 64 (usp + -864)) (Z_to_bv 64 (usp + -896)) (Z_to_bv 64 40) (Z_to_bv 64 pitch) (Z_to_bv 64 SHB)
s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_mc_pois)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FR LO LOS SPH MI.
unfold RA_mc_pois, RA_mc_ip1, A_interp_pitch, mc_frame in *.
replace (ret_pc (Z_to_bv 64 0xa5480)) with (Z_to_bv 64 0xa5480) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [(usp + -192, usp + -184)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -192, usp + -184)]) by (cbn; unfold SH_LO, SH_HI; lia).
ato 0xa5934.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact FR].
Qed.

Lemma mc_w3 : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
17 <= pitch <= 144 -> usp < 2^63 -> 4288 <= usp ->
evt asegs (fun ms' =>
ms' = MS (mkR (Z_to_bv 64 RA_mc_ip2) (Z_to_bv 64 (usp + -896)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 EXC) (Z_to_bv 64 (usp + -544)) (Z_to_bv 64 (mc_p2 pitch)) a3 a4 a5 a6 a7
(Z_to_bv 64 80) (Z_to_bv 64 NE) (Z_to_bv 64 EXC) (Z_to_bv 64 (usp + -864)) (Z_to_bv 64 (usp + -544)) (Z_to_bv 64 40) (Z_to_bv 64 pitch) (Z_to_bv 64 SHB)
s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_interp_pitch) fc None m (seg_rom asegs))
(MS (mkR (Z_to_bv 64 RA_mc_ip1) (Z_to_bv 64 (usp + -896)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 80) (Z_to_bv 64 NE) (Z_to_bv 64 EXC) (Z_to_bv 64 (usp + -864)) (Z_to_bv 64 (usp + -896)) (Z_to_bv 64 40) (Z_to_bv 64 pitch) (Z_to_bv 64 SHB)
s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_mc_ip1)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros HP SPH SPL.
unfold RA_mc_ip1, RA_mc_ip2, A_interp_pitch, mc_p2 in *.
replace (ret_pc (Z_to_bv 64 0xa5494)) with (Z_to_bv 64 0xa5494) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
astep. astep. alits. astep. if_cases K; zify_cond K; rewrite signed_small64 in K by lia.
- astep. rewrite Z.shiftl_mul_pow2, swrap32_small by lia. replace (40 <? pitch) with true by (symmetry; apply Z.ltb_lt; lia).
replace (pitch * 2 ^ 1) with (2 * pitch) by lia.
ato 0xa5934. apply evt_done. reflexivity.
- astep. rewrite swrap32_small by lia. replace (40 <? pitch) with false by (symmetry; apply Z.ltb_ge; lia).
replace (0 - pitch) with (- pitch) by lia.
ato 0xa5934. apply evt_done. reflexivity.
Qed.
End W23.

Section W56.
Variables (usp lo : Z).
Variables gp tp : word.

Lemma mc_w5 : forall (top : Z) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 sp : word)
(j1 j2 j3 : list byte) (f8 f7 f6 f5 f4 f3 f2 f1 f0 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells asegs m (usp + -192) (mc_frame (Z_to_bv 64 top) j1 j2 j3 f8 f7 f6 f5 f4 f3 f2 f1 f0 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
lo <= usp - 4288 -> SH_HI <= lo -> usp < 2^63 -> mem_inv asegs m ->
evt asegs (fun ms' =>
ms' = MS (mkR (Z_to_bv 64 RA_mc_unpois) sp gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 top) (Z_to_bv 64 (usp + -192)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_allocas_unpoison) fc None m (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192)) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_mc_epi) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FR LO LOS SPH MI.
unfold RA_mc_unpois, A_mc_epi, e_allocas_unpoison, mc_frame in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
ato 0x51e64. apply evt_done. reflexivity.
Qed.

Lemma mc_w6 : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 sp top : word)
(j1 j2 j3 jh : list byte) (f8 f7 f6 f5 f4 f3 f2 f1 f0 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells asegs m (usp + -192) (mc_frame top j1 j2 j3 f8 f7 f6 f5 f4 f3 f2 f1 f0 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
rw_cells asegs m (usp + -896) [CB 704 jh] ->
stk asegs m lo (usp + -896) ->
lo <= usp - 4288 -> SH_HI <= lo -> usp < 2^63 -> mem_inv asegs m ->
evt asegs (fun ms' => exists F',
ms' = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 a0 a1 a2 a3 a4 a5 a6 a7 c2 c3 c4 c5 c6 c7 c8 c9 s10 s11 t3 t4 t5 t6)
F' (ret_pc cra) fc None m (seg_rom asegs)
/\ stk asegs m lo usp)
(MS (mkR (Z_to_bv 64 RA_mc_unpois) sp gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192)) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_mc_unpois)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FR H1 ST LO LOS SPH MI.
unfold RA_mc_unpois, mc_frame in *.
replace (ret_pc (Z_to_bv 64 0xa58c4)) with (Z_to_bv 64 0xa58c4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
ato 0xa5918. astep.
release_frame H1 ST (usp + -192). release_frame FR ST usp.
astep. apply evt_done. eexists. split; [reflexivity| exact ST].
Qed.
End W56.
