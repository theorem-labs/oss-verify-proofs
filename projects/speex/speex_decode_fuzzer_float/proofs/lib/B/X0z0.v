(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg X1df X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05q X05l.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0z5 X12a.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac tlia ::= tlia_one.
Local Notation mem := (word -> option byte).

Definition A_lsp_to_lpc : Z := 0xae6d8.
Definition RA_l2l_pois1 : Z := 0xae7b0.
Definition RA_l2l_pois2 : Z := 0xae858.
Definition A_l2l_epi : Z := 0xaeccc.
Definition RA_l2l_unpois : Z := 0xaecd8.

Definition l2l_frame (top : word) (j1 j2 : list byte) (c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) : list cell :=
[C8 top; CB 8 j1; CB 8 j2; C8 c11; C8 c10; C8 c9; C8 c8; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra].

Section L1.
Variables (IQ AK usp lo : Z).
Variables ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m : word -> option byte.

Lemma l2l_w1 :
stk bsegs m lo usp -> lo <= usp - 4384 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
client_constsB m -> mem_inv bsegs m ->
evt bsegs (fun ms' => exists (j1 j2 jh : list byte) (m1 : word -> option byte) (a2' a3' : word),
ms' = MS (mkR (Z_to_bv 64 RA_l2l_pois1) (Z_to_bv 64 (usp + -288)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -128))
(Z_to_bv 64 (usp + -256)) (Z_to_bv 64 88) a2' a3' a4 a5 a6 a7
(Z_to_bv 64 10) (Z_to_bv 64 AK) (Z_to_bv 64 (usp + -256)) (Z_to_bv 64 20) (Z_to_bv 64 IQ) (Z_to_bv 64 5) (Z_to_bv 64 SHB)
(Z_to_bv 64 (usp + -288)) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_alloca_poison) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -4224, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -288)
/\ rw_cells bsegs m1 (usp + -128) (l2l_frame (Z_to_bv 64 0) j1 j2 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
/\ rw_cells bsegs m1 (usp + -288) [CB 160 jh])
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 IQ) (Z_to_bv 64 AK) (Z_to_bv 64 10) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_lsp_to_lpc) fc None m (seg_rom bsegs)).
Proof.
intros ST LO LOS SPH U32 (G1 & G2 & _) MI.
unfold A_lsp_to_lpc, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -4224, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -4224, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 128%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 128 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xae71c.
rewrite (land_m32_al (usp + -128)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
carve_frame 160%nat ST. rename FR0 into HULL1.
carve_frame 3928%nat ST. rename FR0 into JK1.
carve_frame 8%nat ST. rename FR0 into P1.
apply (rw_cells_split_CB bsegs _ _ [] 8 _ [] [8]%nat) in P1; [| reflexivity]. cbn [mk_CB_cells app] in P1.
bato 0xae78c.
alits. replace (usp + -128 - 160) with (usp + -288) by lia. rewrite ?Z.mod_small by lia.
astep. rewrite (land_m32_al (usp + -288)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
astep. astep. replace (usp + -128 - 4096) with (usp + -4224) by lia.
astep. astep. sh_if.
ato 0x51e24.
release_frame P1 ST (usp + -4216). release_frame JK1 ST (usp + -288).
apply evt_done. unfold l2l_frame, RA_l2l_pois1, e_alloca_poison. do 6 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR| exact HULL1].
Qed.
End L1.

Lemma f32_snoc l x : f32 l ++ [C4 x] = f32 (l ++ [x]).
Proof. rewrite f32_app, f32_cons, f32_nil. reflexivity. Qed.

Section ZL.
Variables (WP : Z).
Variables rav spv gp tp t0v t1v t2v s0v s1v a5v a6v a7v s2v s3v s4v s6v s7v s9v s10v s11v t3v t4v t5v t6v : word.
Hypothesis W8 : WP mod 8 = 0.
Hypothesis WR : 0 < WP /\ WP + 88 < 2^62.

Definition RZ (k cnt : Z) (a3v a4v : word) : bvmap 5 word :=
mkR rav spv gp tp t0v t1v t2v s0v s1v (Z_to_bv 64 (WP + 4 * k)) (Z_to_bv 64 (-4)) (Z_to_bv 64 (WP + 4 * k)) a3v a4v a5v a6v a7v
s2v s3v s4v (Z_to_bv 64 cnt) s6v s7v (Z_to_bv 64 SHB) s9v s10v s11v t3v t4v t5v t6v.

Definition zl_post (mI : mem) (F1 : bvmap 5 word) (fc : bv 32) : machine_state -> Prop :=
fun ms' => exists a3' a4' m' (ws' : list word),
ms' = MS (RZ 22 0 a3' a4') F1 (Z_to_bv 64 0xae800) fc None m' (seg_rom bsegs)
/\ munch [(WP, WP + 88)] mI m' /\ wmono bsegs mI m' /\ mem_inv bsegs m'
/\ length ws' = 22%nat /\ rw_cells bsegs m' WP (f32 ws').

Lemma l2l_zl : forall (mI : mem) (rest done : list word) (cw : word) (k : Z) (a3v a4v : word) F1 fc mc,
k = Z.of_nat (length done) -> k + 1 + Z.of_nat (length rest) = 22 ->
aobj bsegs mI WP 88 -> offsh [(WP, WP + 88)] ->
mem_inv bsegs mc -> munch [(WP, WP + 88)] mI mc -> wmono bsegs mI mc ->
rw_cells bsegs mc WP (f32 done) -> rw_cells bsegs mc (WP + 4 * k) (f32 (cw :: rest)) ->
evt bsegs (zl_post mI F1 fc) (MS (RZ k (22 - k) a3v a4v) F1 (Z_to_bv 64 0xae7c4) fc None mc (seg_rom bsegs)).
Proof using W8 WR.
intros mI rest.
induction rest as [|cw' rest IH]; intros done cw k a3v a4v F1 fc mc Hk HN OBW OF MI MU WM XD XC;
pose proof OBW as (OW0 & OW1 & _); unfold APP_TOP in *;
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
unfold RZ; rewrite !f32_cons in XC; cbn [length] in *;
assert (K4 : (WP + 4 * k) mod 4 = 0) by (clear - W8; Z.div_mod_to_equations; lia).
- rewrite f32_nil in XC.
bato 0xae7d4. astep. chk_merge OBW 4.
bato 0xae7e8. rewrite swrap32_small by lia. replace (22 - k + -1) with 0 by lia. astep. astep.
chunk_snoc XD XC. rewrite f32_snoc in XD.
replace (WP + 4 * k + 4) with (WP + 4 * 22) by lia.
apply evt_done. unfold zl_post, RZ. do 4 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [| exact XD]. rewrite length_app. cbn [length]. lia.
- bato 0xae7d4. astep. chk_merge OBW 4.
bato 0xae7e8. rewrite swrap32_small by lia. astep. sh_if.
chunk_uncons XC as C1c. chunk_snoc XD C1c. rewrite f32_snoc in XD. rewrite <- ?f32_cons in XC.
replace (WP + 4 * k + 4) with (WP + 4 * (k + 1)) in * by lia. replace (22 - k + -1) with (22 - (k + 1)) by lia.
eapply (IH _ cw' (k + 1)); try eassumption;
try (rewrite length_app; cbn [length] in *; lia); try (cbn [length] in *; lia).
Qed.
End ZL.

Section L2.
Variables (IQ AK usp lo : Z).
Variables gp tp s10 s11 : word.

Lemma l2l_w2 : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j1 j2 jw : list byte) (c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
rw_cells bsegs m (usp + -128) (l2l_frame (Z_to_bv 64 0) j1 j2 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
rw_cells bsegs m (usp + -256) [CB 88 jw] -> aobj bsegs m (usp + -256) 88 ->
stk bsegs m lo (usp + -288) -> lo <= usp - 4384 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 -> mem_inv bsegs m ->
evt bsegs (fun ms' => exists (jh : list byte) (ws : list word) (m1 : word -> option byte) (a2' a3' a4' : word),
ms' = MS (mkR (Z_to_bv 64 RA_l2l_pois2) (Z_to_bv 64 (usp + -416)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -128))
(Z_to_bv 64 (usp + -384)) (Z_to_bv 64 40) a2' a3' a4' a5 a6 a7
(Z_to_bv 64 10) (Z_to_bv 64 AK) (Z_to_bv 64 (usp + -256)) (Z_to_bv 64 (usp + -384)) (Z_to_bv 64 IQ) (Z_to_bv 64 5) (Z_to_bv 64 SHB)
(Z_to_bv 64 (usp + -416)) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_alloca_poison) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -4384, usp + -288); (usp + -256, usp + -168); (usp + -128, usp + -120)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ stk bsegs m1 lo (usp + -416)
/\ rw_cells bsegs m1 (usp + -128) (l2l_frame (Z_to_bv 64 (usp + -288)) j1 j2 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra)
/\ rw_cells bsegs m1 (usp + -256) (f32 ws) /\ length ws = 22%nat
/\ rw_cells bsegs m1 (usp + -416) [CB 128 jh])
(MS (mkR (Z_to_bv 64 RA_l2l_pois1) (Z_to_bv 64 (usp + -288)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -128)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 10) (Z_to_bv 64 AK) (Z_to_bv 64 (usp + -256)) (Z_to_bv 64 20) (Z_to_bv 64 IQ) (Z_to_bv 64 5) (Z_to_bv 64 SHB)
(Z_to_bv 64 (usp + -288)) s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_l2l_pois1)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FR XW OBW ST LO LOS SPH U32 MI.
unfold RA_l2l_pois1, RA_l2l_pois2, e_alloca_poison, l2l_frame in *.
replace (ret_pc (Z_to_bv 64 0xae7b0)) with (Z_to_bv 64 0xae7b0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof OBW as (OW0 & OW1 & _). unfold APP_TOP in *.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -4384, usp + -288); (usp + -256, usp + -168); (usp + -128, usp + -120)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -4384, usp + -288); (usp + -256, usp + -168); (usp + -128, usp + -120)]) by (cbn; unfold SH_LO, SH_HI; lia).
assert (W8 : (usp + -256) mod 8 = 0) by (clear - U32; Z.div_mod_to_equations; lia).
assert (OFW : offsh [(usp + -256, usp + -256 + 88)]) by (cbn; unfold SH_LO, SH_HI; lia).
change 88%nat with (4 * 22)%nat in XW. destruct (rw_cells_CB_f32 bsegs _ _ 22%nat _ XW) as (wl & Lwl & XW'); clear XW.
destruct wl as [|w0 wl]; [cbn in Lwl; lia|]. cbn [length] in Lwl.
ato 0xae7c4. alits.
replace (Z_to_bv 64 (usp + -256)) with (Z_to_bv 64 (usp + -256 + 4 * 0)) by (f_equal; lia).
change (Z_to_bv 64 22) with (Z_to_bv 64 (22 - 0)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(usp + -256, usp + -256 + 88)] mc) as MU0; pose proof (wmono_refl bsegs mc) as WM0;
assert (XD0 : rw_cells bsegs mc (usp + -256) (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia);
pose proof XW' as XC0; replace (usp + -256) with (usp + -256 + 4 * 0) in XC0 at 1 by lia;
callc (l2l_zl (usp + -256) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ W8 ltac:(lia) mc wl [] w0 0 _ _ _ _ mc)
(clear XW' XC0 XD0);
[ reflexivity | cbn [length]; lia | exact (aobj_munch bsegs _ m mc (usp + -256) 88 OBW MU (shfree_of_aobj bsegs _ m (usp + -256) 88 OF OBW)) | exact OFW | exact MI | exact MU0 | exact WM0 | exact XD0 | exact XC0 | ] end.
clear MU0 WM0. rename MI0 into MI. unfold RZ.
replace (usp + -256 + 4 * 0) with (usp + -256) by lia. replace (usp + -256 + 4 * 22) with (usp + -168) by lia.
match goal with H : rw_cells _ _ (usp + -256) (f32 ?l), H2 : length ?l = 22%nat |- _ => rename H into XW2; rename H2 into LW2 end.
carve_frame 128%nat ST. rename FR0 into HULL2.
carve_frame 3960%nat ST. rename FR0 into JK1.
carve_frame 8%nat ST. rename FR0 into P1.
apply (rw_cells_split_CB bsegs _ _ [] 8 _ [] [8]%nat) in P1; [| reflexivity]. cbn [mk_CB_cells app] in P1.
bato 0xae830.
alits. astep. replace (usp + -288 - 128) with (usp + -416) by lia. rewrite ?Z.mod_small by lia.
astep. rewrite (land_m32_al (usp + -416)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
astep. astep. replace (usp + -288 - 4096) with (usp + -4384) by lia.
astep. astep. sh_if.
ato 0x51e24.
release_frame P1 ST (usp + -4376). release_frame JK1 ST (usp + -416).
apply evt_done. do 6 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR|]. split; [exact XW2|]. split; [exact LW2| exact HULL2].
Qed.
End L2.

Section L5.
Variables (usp lo : Z).
Variables gp tp : word.

Lemma l2l_w5 : forall (top : Z) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (sp : word)
(j1 j2 : list byte) (c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
rw_cells bsegs m (usp + -128) (l2l_frame (Z_to_bv 64 top) j1 j2 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
lo <= usp - 4384 -> SH_HI <= lo -> usp < 2^63 -> mem_inv bsegs m ->
evt bsegs (fun ms' =>
ms' = MS (mkR (Z_to_bv 64 RA_l2l_unpois) sp gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -128))
(Z_to_bv 64 top) (Z_to_bv 64 (usp + -128)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_allocas_unpoison) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -128)) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_l2l_epi) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FR LO LOS SPH MI.
unfold RA_l2l_unpois, A_l2l_epi, e_allocas_unpoison, l2l_frame in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
ato 0x51f50. apply evt_done. reflexivity.
Qed.

Lemma l2l_w6 : forall (top : Z) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (sp : word)
(j1 j2 jh1 jh2 : list byte) (c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
rw_cells bsegs m (usp + -128) (l2l_frame (Z_to_bv 64 top) j1 j2 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
rw_cells bsegs m (usp + -288) [CB 160 jh1] -> rw_cells bsegs m (usp + -416) [CB 128 jh2] ->
stk bsegs m lo (usp + -416) ->
lo <= usp - 4384 -> SH_HI <= lo -> usp < 2^63 -> mem_inv bsegs m ->
evt bsegs (fun ms' =>
ms' = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 a0 a1 a2 a3 a4 a5 a6 a7 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 t3 t4 t5 t6)
F (ret_pc cra) fc None m (seg_rom bsegs)
/\ stk bsegs m lo usp)
(MS (mkR (Z_to_bv 64 RA_l2l_unpois) sp gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -128)) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_l2l_unpois)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FR H1 H2 ST LO LOS SPH MI.
unfold RA_l2l_unpois, l2l_frame in *.
replace (ret_pc (Z_to_bv 64 0xaecd8)) with (Z_to_bv 64 0xaecd8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
ato 0xaed10. astep.
release_frame H2 ST (usp + -288). release_frame H1 ST (usp + -128). release_frame FR ST usp.
astep. apply evt_done. split; [reflexivity| exact ST].
Qed.
End L5.
