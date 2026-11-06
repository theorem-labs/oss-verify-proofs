(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1df X1ck X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05l X09f X069 X09e X08x.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation mem := (word -> option byte).

Lemma lor_byte_shift : forall a R, 0 <= a < 256 -> 0 <= R -> Z.lor a (Z.shiftl R 8) = a + 256 * R.
Proof.
intros a R Ha HR.
assert (L0 : Z.land a (Z.shiftl R 8) = 0).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases n 8) as [L|G]; [rewrite Z.shiftl_spec_low by lia; apply andb_false_r|].
destruct (Z.eq_dec a 0) as [->|NZ]; [rewrite Z.bits_0; reflexivity|].
rewrite (Z.bits_above_log2 a n); [reflexivity| lia|]. apply Z.lt_le_trans with 8; [|exact G]. apply Z.log2_lt_pow2; [lia|]. change (2^8) with 256. lia. }
rewrite <- Z.lxor_lor by exact L0. rewrite <- Z.add_nocarry_lxor by exact L0. rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256. lia.
Qed.
Lemma bytes_le_to_Z_bound : forall bs, 0 <= bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof.
induction bs as [|b bs IH]; [cbn; lia|].
cbn [bytes_le_to_Z length]. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
replace (8 * Z.of_nat (S (length bs))) with (8 * Z.of_nat (length bs) + 8) by lia.
rewrite Z.pow_add_r by lia. change (2^8) with 256. rewrite lor_byte_shift by lia. nia.
Qed.
Lemma Z_to_le_bytes_of_bytes : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
induction bs as [|b bs IH]; [reflexivity|].
cbn [bytes_le_to_Z length Z_to_le_bytes]. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
pose proof (bytes_le_to_Z_bound bs) as B. rewrite lor_byte_shift by lia. f_equal.
- apply zb8_eq. replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
- rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256. replace ((bv_unsigned b + 256 * bytes_le_to_Z bs) / 256) with (bytes_le_to_Z bs); [exact IH|].
apply Z.div_unique with (r := bv_unsigned b); [left; lia| lia].
Qed.
Lemma rw_cells_CB8_C8 : forall segs (m : mem) a j, rw_cells segs m a [CB 8 j] -> exists w, rw_cells segs m a [C8 w].
Proof.
intros segs m a j H. assert (L : length j = 8%nat) by (destruct H as [[[Hwf _] _] _]; exact Hwf).
exists (le_bytes_to_word j). eapply rw_cells_recast; [exact H | cbn; exact (conj I I) |].
cbn [cells_bytes cbytes app]. rewrite !app_nil_r. unfold le8, word_to_le_bytes, le_bytes_to_word.
pose proof (bytes_le_to_Z_bound j) as B. rewrite L in B. change (8 * Z.of_nat 8) with 64 in B.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). rewrite Z.mod_small by lia.
rewrite <- L at 1. apply Z_to_le_bytes_of_bytes.
Qed.

Definition A_nb_decode : Z := 0x9f634.
Definition RA_nbd_smalloc : Z := 0x9f6dc.
Definition PC_stack_malloc_5 : Z := 0x516c8.

Definition nbd_saves (F : bvmap 5 word) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
[C8 (reg_get F (Z_to_bv 5 27)); C8 (reg_get F (Z_to_bv 5 26)); C8 (reg_get F (Z_to_bv 5 25)); C8 (reg_get F (Z_to_bv 5 24));
C8 (reg_get F (Z_to_bv 5 23)); C8 (reg_get F (Z_to_bv 5 22)); C8 (reg_get F (Z_to_bv 5 21)); C8 (reg_get F (Z_to_bv 5 20));
C8 (reg_get F (Z_to_bv 5 19)); C8 (reg_get F (Z_to_bv 5 18)); C8 (reg_get F (Z_to_bv 5 9)); C8 (reg_get F (Z_to_bv 5 8));
C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma nbd_w1 : forall (usp lo ST A OUT : Z) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem),
stk asegs m lo usp -> lo <= usp - 544 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
client_consts m -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (j1 j2 : list byte),
ms = MS (mkR (Z_to_bv 64 RA_nbd_smalloc) (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544))
(Z_to_bv 64 1088) (Z_to_bv 64 g_shadow_memory_dynamic_address) (Z_to_bv 64 1) a3 a4 a5 a6 a7
(Z_to_bv 64 A) s3 s4 s5 s6 s7 (Z_to_bv 64 ST) s9 (Z_to_bv 64 SHB) s11 t3 t4 t5 t6)
F (Z_to_bv 64 PC_stack_malloc_5) fc None m1 (seg_rom asegs)
/\ munch [(usp + -544, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -544)
/\ rw_cells asegs m1 (usp + -544) ([C8 (Z_to_bv 64 0); CB 160 j1; C8 (Z_to_bv 64 OUT); CB 168 j2] ++ nbd_saves F s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ST) (Z_to_bv 64 A) (Z_to_bv 64 OUT) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_nb_decode) fc None m (seg_rom asegs)).
Proof.
intros until m. intros ST0 LO LOS SPH SP32 (G1 & G2 & G3 & G4) MI.
unfold A_nb_decode, RA_nbd_smalloc, PC_stack_malloc_5, nbd_saves,
g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST0 as (STa & STb & _).
pose proof (munch_refl [(usp + -544, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 544%nat ST0.
apply (rw_cells_split_CB asegs _ _ [] 544 _ [] [8; 160; 8; 168; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
cbn [mk_CB_cells app] in FR.
ato 0x9f6a4. astep. rewrite land_m32_al by lia.
ato 0x9f6d0. rewrite sx32_small by (unfold int31; lia).
ato 0x516c8.
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST0| exact FR].
Qed.

Lemma nbd_seg_poison : forall (sf ST : Z) (ra sp gp tp t0 t1 t2 s0 s1 a3 a5 a6 a7 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
(js : list byte) F fc (m : mem),
rw_cells asegs m sf [CB 256 js] -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (rs : list byte),
ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (ST + 24)) (Z_to_bv 64 (-14)) (Z_to_bv 64 (-8)) (Z_to_bv 64 4) (Z_to_bv 64 (-13)) a5 a6 a7
(Z_to_bv 64 sf) s3 s4 s5 s6 s7 (Z_to_bv 64 ST) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9f974) fc None m1 (seg_rom asegs)
/\ munch [(sf, sf + 256)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ rw_cells asegs m1 sf (nbd_shadow SC_X rs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-15)) (Z_to_bv 64 (-14)) (Z_to_bv 64 (-8)) a3 (Z_to_bv 64 (-13)) a5 a6 a7
(Z_to_bv 64 sf) s3 s4 s5 s6 s7 (Z_to_bv 64 ST) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9f74c) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FRS MI.
unfold nbd_shadow, nbd_shadow_bytes, SC_X, sh_run, bF1, bF2, bF3, bF8, b04, z8 in *. cbn [sc_top sc_lpc sc_main sc_innov2 sc_iq map repeat app] in *.
pose proof (rw_cells_bound _ _ _ _ FRS) as BS. cbn [cells_size csize Nat.add] in BS.
pose proof (munch_refl [(sf, sf + 256)] m) as MU. pose proof (wmono_refl asegs m) as WM.
apply (rw_cells_split_CB asegs _ _ [] 256 _ [] (repeat 1%nat 136 ++ [120%nat])) in FRS; [| reflexivity].
cbn [mk_CB_cells app repeat] in FRS.
ato 0x9f974.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact FRS].
Qed.

Definition nbd_fhdr (rest : list byte) : list cell :=
[C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x20595); C8 (Z_to_bv 64 0x9f634); CB 2016 rest].
Definition nbd_frame_w2 (ST A OUT f : Z) (ja jb jc jd je jf jg : list byte) (sv : list cell) : list cell :=
[C8 (Z_to_bv 64 0); CB 40 ja; C8 (Z_to_bv 64 (ST + 2120)); CB 96 jb; C8 (Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB)); CB 8 jc; C8 (Z_to_bv 64 OUT);
CB 64 jd; C8 (Z_to_bv 64 0); CB 8 je; C8 (Z_to_bv 64 A); CB 32 jf; C8 (Z_to_bv 64 (ST + 32)); CB 32 jg; C8 (Z_to_bv 64 f)] ++ sv.

Lemma nbd_w2 : forall (usp lo ST A OUT f sf : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 : word)
(sv : list cell) (j1 j2 jb js pad : list byte) (mode first cl srate log exc0 sid enh : word) F fc (m : mem),
stk asegs m lo (usp + -544) -> lo <= usp + -544 -> SH_HI <= lo -> usp < 2^63 ->
0 < f -> f mod 64 = 0 -> f + 2048 <= lo -> f + 2048 <= APP_TOP -> IMG_TOP <= f -> hidp (f + 2048 <= SH_LO \/ SH_HI <= f) -> sf = Z.shiftr f 3 + SHB ->
aobj asegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> ST + NBSTATE_SIZEOF <= lo -> hidp (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) ->
hidp (ST + NBSTATE_SIZEOF <= 0x10000 \/ IMG_TOP <= ST) -> hidp (ST + NBSTATE_SIZEOF <= f \/ f + 2048 <= ST) -> hidp (ST + NBSTATE_SIZEOF <= sf \/ sf + 256 <= ST) ->
0 < A < 2^47 -> length sv = 25%nat -> Forall (fun c => csize c = 8%nat) sv ->
rw_cells asegs m (usp + -544) ([C8 (Z_to_bv 64 0); CB 160 j1; C8 (Z_to_bv 64 OUT); CB 168 j2] ++ sv) ->
rw_cells asegs m f [CB 2040 jb] -> rw_cells asegs m sf [CB 256 js] ->
rw_cells asegs m ST [C8 mode; C4 first; C4 cl; C4 srate; C4 log; C8 (Z_to_bv 64 0)] ->
rw_cells asegs m (ST + 2032) [C8 exc0] ->
rw_cells asegs m (ST + 2232) [C4 (Z_to_bv 64 1); CB 4 pad; C8 (Z_to_bv 64 NB_SUBMODES_PTR); C4 sid; C4 enh] ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (a1' : word) (ja jb' jc jd je jf jg rb rs : list byte),
ms = MS (mkR (Z_to_bv 64 RA_nbd_smalloc) (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544))
(Z_to_bv 64 A) a1' (Z_to_bv 64 (-8)) (Z_to_bv 64 4) (Z_to_bv 64 (ST + 32)) (Z_to_bv 64 0x9f634) a6 a7
(Z_to_bv 64 sf) (Z_to_bv 64 0) (Z_to_bv 64 f) (Z_to_bv 64 (ST + 2120)) (Z_to_bv 64 (ST + 2047)) (Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB))
(Z_to_bv 64 ST) (Z_to_bv 64 f) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2032)) t3 t4 t5 t6)
F (Z_to_bv 64 0x9f9f8) fc None m1 (seg_rom asegs)
/\ munch [(usp + -544, usp); (f, f + 2040); (sf, sf + 256); (ST + 2032, ST + 2040)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -544)
/\ rw_cells asegs m1 (usp + -544) (nbd_frame_w2 ST A OUT f ja jb' jc jd je jf jg sv)
/\ rw_cells asegs m1 f (nbd_fhdr rb) /\ rw_cells asegs m1 sf (nbd_shadow SC_X rs)
/\ rw_cells asegs m1 ST [C8 mode; C4 first; C4 cl; C4 srate; C4 log; C8 (Z_to_bv 64 0)]
/\ rw_cells asegs m1 (ST + 2032) [C8 (Z_to_bv 64 (ST + 1368))]
/\ rw_cells asegs m1 (ST + 2232) [C4 (Z_to_bv 64 1); CB 4 pad; C8 (Z_to_bv 64 NB_SUBMODES_PTR); C4 sid; C4 enh])
(MS (mkR (Z_to_bv 64 RA_nbd_smalloc) (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) (Z_to_bv 64 f)
a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 A) s3 s4 s5 s6 s7 (Z_to_bv 64 ST) s9 (Z_to_bv 64 SHB) s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_nbd_smalloc)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros ST0 LO LOS SPH F0 F64 FLO FAT FTOP FSH Esf OBS S8 SLO SSH SIM SFA SSA A0 LSV SVS FR FRB FRS HDR EXC CFG MI.
unfold nbd_frame_w2, nbd_fhdr, RA_nbd_smalloc, NBSTATE_SIZEOF, NB_SUBMODES_PTR in *.
pose proof OBS as (OS0 & OS1 & _). unfold APP_TOP in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FTOP as FTOP'. unfold IMG_TOP in FTOP'.
pose proof (shad_range_al f 2048 ltac:(lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) ltac:(unfold APP_TOP; lia)) as SW.
rewrite <- shad_shiftr, <- Esf in SW. change (2048 / 8) with 256 in SW. unfold SH_LO, SH_HI in SW.
pose proof (FSH : _ \/ _) as FSH'. unfold SH_LO, SH_HI in FSH'. pose proof (SFA : _ \/ _) as SFA'. pose proof (SSA : _ \/ _) as SSA'.
pose proof ST0 as (STa & STb & _).
pose proof (munch_refl [(usp + -544, usp); (f, f + 2040); (sf, sf + 256); (ST + 2032, ST + 2040)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (SFR : shfree [(usp + -544, usp); (f, f + 2040); (sf, sf + 256); (ST + 2032, ST + 2040)] ST 2968).
{ apply shfree_cons_off; [unfold SH_LO, SH_HI; lia | lia | unfold APP_TOP; lia |].
apply shfree_cons_off; [unfold SH_LO, SH_HI; lia | lia | unfold APP_TOP; lia |].
apply (shfree_cons_sh _ _ _ _ _ f 2048); [clear - F64; Z.div_mod_to_equations; lia | rewrite Esf, shad_shiftr; lia | rewrite Esf, shad_shiftr; unfold shad; clear - F64; Z.div_mod_to_equations; lia | exact SFA' |].
apply shfree_cons_off; [pose proof (SSH : _ \/ _) as Y; unfold SH_LO, SH_HI in *; lia | lia | unfold APP_TOP; lia |]. apply shfree_nil. }
replace (ret_pc (Z_to_bv 64 0x9f6dc)) with (Z_to_bv 64 0x9f6dc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
apply (rw_cells_split_CB asegs _ _ [] 2040 _ [] [8; 8; 8; 2016]%nat) in FRB; [| reflexivity]. cbn [mk_CB_cells app] in FRB.
ato 0x9f6ec. astep. sh_if.
ato 0x9f748. astep. rewrite <- Esf.
call (nbd_seg_poison sf ST). { exact FRS. } { assumption. } rename POST into FRS'.
unfold nbd_shadow, nbd_shadow_bytes, SC_X, sh_run, bF1, bF2, bF3, bF8, b04, z8 in FRS'. cbn [sc_top sc_lpc sc_main sc_innov2 sc_iq map repeat app] in FRS'.
ato 0x9f9c8. astep. sh_if.
ato 0x9f9e8. astep.
ato 0x9f9f8.
apply evt_done. do 11 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST0|]. split; [exact FR|]. split; [exact FRB|]. split; [exact FRS'|].
split; [exact HDR|]. split; [exact EXC| exact CFG].
Qed.
