(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1dg X1df X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X081 X05l X07y X05m X09f X06d X069 X082 X0b1 X05j X05f X05k.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition sb_fr (g : nat -> word) : list cell := map (fun i => C8 (g i)) (seq 0 56).
Fixpoint fupds (g : nat -> word) (l : list (nat * word)) : nat -> word :=
match l with [] => g | (k, v) :: l' => fupds (fun i => if Nat.eqb i k then v else g i) l' end.
Lemma cells_size_sb_fr : forall g, cells_size (sb_fr g) = 448%nat. Proof. reflexivity. Qed.
#[export] Hint Rewrite cells_size_sb_fr : chunk_sizes.

Definition sb_e_stack_malloc_0 : Z := 0x51228.
Definition RA_sbd_smalloc : Z := 0xb6854.
Lemma Z_to_le_bytes_inv : forall (bs : list byte), Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
induction bs as [|b bs IH]; [reflexivity|].
cbn [length Z_to_le_bytes bytes_le_to_Z].
pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
assert (NN : 0 <= bytes_le_to_Z bs).
{ clear. induction bs as [|c cs IH]; cbn [bytes_le_to_Z]; [lia|]. apply Z.lor_nonneg. split; [pose proof (bv_unsigned_in_range 8 c); lia| apply Z.shiftl_nonneg; exact IH]. }
f_equal.
- apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?a) with (a mod 2^8).
rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l.
rewrite (Z.land_ones (bv_unsigned b) 8) by lia. rewrite (Z.mod_small (bv_unsigned b)) by (change (2^8) with 256; lia).
rewrite Z.land_ones by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_mul by lia. apply Z.lor_0_r.
- rewrite Z.shiftr_lor. rewrite Z.shiftr_shiftl_l by lia. change (8 - 8) with 0. rewrite Z.shiftl_0_r.
rewrite (Z.shiftr_div_pow2 (bv_unsigned b)) by lia. rewrite Z.div_small by (change (2^8) with 256; lia). rewrite Z.lor_0_l. exact IH.
Qed.

Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
intros bs L. unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
assert (R : 0 <= bytes_le_to_Z bs < 2^64).
{ pose proof (Z_to_le_bytes_inv bs) as E.
assert (H : forall n (cs : list byte), length cs = n -> 0 <= bytes_le_to_Z cs < 2 ^ (8 * Z.of_nat n)).
{ clear. induction n as [|n IH]; intros cs Lc; destruct cs as [|c cs]; try discriminate Lc; [cbn; lia|].
cbn [bytes_le_to_Z]. injection Lc as Lc. specialize (IH cs Lc).
pose proof (bv_unsigned_in_range 8 c) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
replace (Z.lor (bv_unsigned c) (bytes_le_to_Z cs ≪ 8)) with (bv_unsigned c + bytes_le_to_Z cs * 256).
- replace (8 * Z.of_nat (S n)) with (8 * Z.of_nat n + 8) by lia. rewrite Z.pow_add_r by lia. change (2^8) with 256. nia.
- rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256. symmetry. rewrite Z.lor_comm. rewrite <- Z.add_comm.
apply Z.bits_inj'. intros k Hk. rewrite Z.lor_spec.
rewrite <- (Z.shiftl_mul_pow2 _ 8) by lia.
rewrite Z.add_nocarry_lxor.
+ rewrite Z.lxor_spec. rewrite Z.shiftl_spec by lia.
destruct (Z.ltb_spec0 k 8).
* rewrite (Z.testbit_neg_r _ (k - 8)) by lia. reflexivity.
* assert (T : Z.testbit (bv_unsigned c) k = false).
{ destruct (Z.eq_dec (bv_unsigned c) 0) as [->|NZ]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; [lia|].
assert (2^8 <= 2^k) by (apply Z.pow_le_mono_r; lia). change (2^8) with 256 in *. lia. }
rewrite T. destruct (Z.testbit _ _); reflexivity.
+ apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec, Z.bits_0, Z.shiftl_spec by lia.
destruct (Z.ltb_spec0 j 8); [rewrite (Z.testbit_neg_r _ (j - 8)) by lia; reflexivity|].
assert (T : Z.testbit (bv_unsigned c) j = false).
{ destruct (Z.eq_dec (bv_unsigned c) 0) as [->|NZ]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; [lia|].
assert (2^8 <= 2^j) by (apply Z.pow_le_mono_r; lia). change (2^8) with 256 in *. lia. }
rewrite T. apply andb_false_r. }
specialize (H 8%nat bs L). exact H. }
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). rewrite Z.mod_small by exact R.
rewrite <- L. apply Z_to_le_bytes_inv.
Qed.

Lemma bytes_are_u64 : forall (n : nat) (bs : list byte), length bs = (8 * n)%nat ->
exists ws : list word, length ws = n /\ cells_bytes (map C8 ws) = bs.
Proof.
induction n as [|n IH]; intros bs L.
- exists []. destruct bs; [split; reflexivity| cbn in L; lia].
- assert (L8 : length (firstn 8 bs) = 8%nat) by (rewrite length_firstn; lia).
destruct (IH (skipn 8 bs) ltac:(rewrite length_skipn; lia)) as (ws & Lw & E).
exists (le_bytes_to_word (firstn 8 bs) :: ws). split; [cbn; lia|].
cbn [map cells_bytes cbytes]. rewrite le8_of_bytes by exact L8. rewrite E. apply firstn_skipn.
Qed.

Lemma cells_wf_C8s : forall ws : list word, cells_wf (map C8 ws).
Proof. induction ws; cbn; [exact I| split; [exact I| exact IHws]]. Qed.

Lemma rw_cells_CB_u64 : forall segs m A (n : nat) bs,
rw_cells segs m A [CB (8 * n) bs] -> exists ws : list word, length ws = n /\ rw_cells segs m A (map C8 ws).
Proof.
intros segs m A n bs H.
assert (L : length bs = (8 * n)%nat) by (destruct H as [[[Hwf _] _] _]; exact Hwf).
destruct (bytes_are_u64 n bs L) as (ws & Lw & E). exists ws. split; [exact Lw|].
eapply rw_cells_recast; [exact H| apply cells_wf_C8s|]. cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact E.
Qed.

Lemma sb_fr_of_list : forall ws : list word, length ws = 56%nat -> map C8 ws = sb_fr (fun i => nth i ws (Z_to_bv 64 0)).
Proof.
intros ws L. do 56 (destruct ws as [|? ws]; [discriminate L|]). destruct ws; [reflexivity| discriminate L].
Qed.
Lemma rw_cells_CB4_C4 : forall segs m A pre bs post, rw_cells segs m A (pre ++ CB 4 bs :: post) ->
exists w : word, rw_cells segs m A (pre ++ C4 w :: post).
Proof.
intros segs m A pre bs post H.
assert (WF : cells_wf (pre ++ CB 4 bs :: post)) by (destruct H as [[Hwf _] _]; exact Hwf).
assert (L : length bs = 4%nat).
{ clear - WF. induction pre as [|c pre IH]; cbn in WF; [exact (proj1 WF)| exact (IH (proj2 WF))]. }
destruct (bytes_are_f32 1 bs L) as (ws & Lw & E). destruct ws as [|w [|? ?]]; try discriminate Lw. exists w.
eapply rw_cells_recast; [exact H | |].
- clear - WF. induction pre as [|c pre IH]; cbn in WF |- *; [split; [exact I| exact (proj2 WF)]| split; [exact (proj1 WF)| exact (IH (proj2 WF))]].
- rewrite !cells_bytes_app. f_equal. cbn [cells_bytes cbytes]. f_equal. rewrite f32_cons, f32_nil in E. cbn [cells_bytes cbytes] in E. rewrite app_nil_r in E. exact E.
Qed.

Lemma sbd_w1 : forall (usp lo S A OUT : Z)
(ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
stk asegs m lo usp -> lo <= usp - 608 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
client_consts m -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (g : nat -> word) (xa1 : word),
ms = MS (mkR (Z_to_bv 64 RA_sbd_smalloc) (Z_to_bv 64 (usp + -608)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -608))
(Z_to_bv 64 64) xa1 (Z_to_bv 64 OUT) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 SHB) (Z_to_bv 64 OUT) (Z_to_bv 64 S) t3 t4 t5 t6)
F (Z_to_bv 64 sb_e_stack_malloc_0) fc None m1 (seg_rom asegs)
/\ munch [(usp + -608, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -608)
/\ rw_cells asegs m1 (usp + -608) (sb_fr g) /\ g 0%nat = Z_to_bv 64 0 /\ g 38%nat = Z_to_bv 64 A /\ g 52%nat = Z_to_bv 64 0
/\ rw_cells asegs m1 (usp + -160) (sb_saves F ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 A) (Z_to_bv 64 OUT) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_sb_decode) fc None m (seg_rom asegs)).
Proof.
intros until m. intros ST LO LOS SPH SP32 (G1 & G2 & G3 & G4) MI.
unfold A_sb_decode, RA_sbd_smalloc, sb_e_stack_malloc_0,
g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'.
pose proof (munch_refl [(usp + -608, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -608, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 608%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 608 _ [] (448%nat :: repeat 8%nat 20)) in FR; [| reflexivity]. cbn [repeat mk_CB_cells app] in FR.
chunk_uncons FR as FSL. change 448%nat with (8 * 56)%nat in FSL. apply rw_cells_CB_u64 in FSL. destruct FSL as (ws & Lws & FSL).
rewrite (sb_fr_of_list ws Lws) in FSL. unfold sb_fr in FSL. cbn [map seq] in FSL.
replace (usp + -608 + 448) with (usp + -160) in FR by lia.
ato 0xb6818. astep. rewrite land_m32_al by lia.
ato 0xb6848. rewrite sx32_small by (unfold int31; lia).
ato 0x51228.
apply evt_done. eexists. exists (fupds (fun i => nth i ws (Z_to_bv 64 0)) [(0%nat, Z_to_bv 64 0); (38%nat, Z_to_bv 64 A); (52%nat, Z_to_bv 64 0)]). eexists.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
split; [exact FSL|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exact FR.
Qed.

Notation sbd_desc_cells MODE c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 :=
[C8 (Z_to_bv 64 MODE); C8 c1; C8 c2; C4 c3; C4 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12] (only parsing).
Definition RA_sbd_ctl104 : Z := 0xb6984.

Lemma sbd_w2 : forall (usp lo S OUT f sf MP MODE : Z) (g : nat -> word) (s : sbd_state bptr) (a : sb_addrs)
(gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6 : word) (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 : word)
(jb js : list byte) F fc (m : mem),
stk asegs m lo (usp + -608) -> lo <= usp + -608 -> SH_HI <= lo -> usp < 2^63 ->
0 < f -> f mod 64 = 0 -> f + 64 <= lo -> f + 64 <= APP_TOP -> (f + 64 <= SH_LO \/ SH_HI <= f) -> sf = Z.shiftr f 3 + SHB ->
rw_cells asegs m (usp + -608) (sb_fr g) -> rw_cells asegs m f [CB 56 jb] -> rw_cells asegs m sf [CB 8 js] ->

rw_cells asegs m S (sbp_hdr s a) -> rw_cells asegs m (S + 40) (sbp_ptrs s a OUT) ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= lo -> (S + 160 <= SH_LO \/ SH_HI <= S) -> (S + 160 <= f \/ f + 64 <= S) -> IMG_TOP <= f ->
MP = sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode (sbd_mode s) ->
ro_cells asegs m MP (sbd_desc_cells MODE c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12) -> aobj asegs m MP 96 -> MP mod 8 = 0 -> 0x10000 <= MP -> MP + 104 <= 0x652000 ->
0 <= OUT -> OUT + 8000 < 2^63 -> 0 <= sbd_frame_size s <= 320 ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (j24 j36 : list byte) (dtx : word),
ms = MS (mkR (Z_to_bv 64 RA_sbd_ctl104) (Z_to_bv 64 (usp + -608)) gp tp xt0 xt1 xt2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -608))
(Z_to_bv 64 (a_low a)) (Z_to_bv 64 104) (Z_to_bv 64 (OUT + 4 * sbd_frame_size s)) xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 (S + 8)) (Z_to_bv 64 sf) s4 (Z_to_bv 64 (Z.shiftr (S + 8) 3 + SHB)) (Z_to_bv 64 f) (Z_to_bv 64 MODE) (Z_to_bv 64 f)
(Z_to_bv 64 SHB) (Z_to_bv 64 OUT) (Z_to_bv 64 S) xt3 xt4 xt5 xt6)
F (Z_to_bv 64 A_speex_decoder_ctl) fc None m1 (seg_rom asegs)
/\ munch [(usp + -608, usp + -160); (f, f + 56); (sf, sf + 8)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -608)
/\ rw_cells asegs m1 (usp + -608)
(sb_fr (fupds g [(51%nat, Z_to_bv 64 f); (45%nat, Z_to_bv 64 0); (26%nat, Z_to_bv 64 (S + 20)); (27%nat, Z_to_bv 64 (Z.shiftr (S + 20) 3 + SHB));
(10%nat, Z_to_bv 64 (OUT + 4 * sbd_frame_size s))]))
/\ rw_cells asegs m1 f (sb_fhdr j24 dtx j36) /\ rw_cells asegs m1 sf sb_fshadow)
(MS (mkR (Z_to_bv 64 RA_sbd_smalloc) (Z_to_bv 64 (usp + -608)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -608)) (Z_to_bv 64 f)
a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 SHB) (Z_to_bv 64 OUT) (Z_to_bv 64 S) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_smalloc)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros ST LO LOS SPH F0 F64 FLO FTOP FSH Esf FR FRB FRS HD PT OBS S8 SPOS SLO SOFF SFA FIMG EMP DESC OBM MP8 MPLO MPHI O0 O1 FSZ MI.
unfold RA_sbd_smalloc, RA_sbd_ctl104, A_speex_decoder_ctl in *.
replace (ret_pc (Z_to_bv 64 0xb6854)) with (Z_to_bv 64 0xb6854) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'.
assert (SFR : SH_LO <= sf /\ sf + 8 <= SH_HI) by (subst sf; pose proof (shad_range_al f 64 ltac:(lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) FTOP) as X; rewrite shad_shiftr; unfold shad in *; change (64 / 8) with 8 in X; lia).
pose proof (munch_refl [(usp + -608, usp + -160); (f, f + 56); (sf, sf + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
apply (rw_cells_split_CB asegs _ _ [] 56 _ [] [8; 8; 8; 8; 4; 20]%nat) in FRB; [| reflexivity]. cbn [mk_CB_cells app] in FRB.
apply (rw_cells_split_CB asegs _ _ [] 8 _ [] [1; 1; 1; 1; 1; 1; 1; 1]%nat) in FRS; [| reflexivity]. cbn [mk_CB_cells app] in FRS.
unfold sb_fr in FR. cbn [map seq] in FR. unfold sbp_hdr in HD. unfold sbp_ptrs in PT.
assert (F8 : f mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
pose proof OBS as (OBS0 & OBS1 & _). pose proof OBM as (OBM0 & OBM1 & _).
assert (SFS : shfree [(usp + -608, usp + -160); (f, f + 56); (sf, sf + 8)] S 160).
{ apply shfree_cons_off; [unfold SH_LO, SH_HI in *; lia | lia | assumption |].
apply shfree_cons_off; [unfold SH_LO, SH_HI in *; lia | lia | assumption |].
apply (shfree_cons_sh _ _ _ _ _ f 64 F8); [subst sf; rewrite shad_shiftr; lia | subst sf; rewrite shad_shiftr; unfold shad; replace ((f + 64) / 8) with (f / 8 + 8) by (clear - F8; Z.div_mod_to_equations; lia); lia | exact SFA | apply shfree_nil]. }
assert (SFM : shfree [(usp + -608, usp + -160); (f, f + 56); (sf, sf + 8)] MP 96).
{ apply shfree_cons_off; [unfold SH_LO, SH_HI in *; lia | lia | assumption |].
apply shfree_cons_off; [unfold SH_LO, SH_HI in *; lia | lia | assumption |].
apply (shfree_cons_sh _ _ _ _ _ f 64 F8); [subst sf; rewrite shad_shiftr; lia | subst sf; rewrite shad_shiftr; unfold shad; replace ((f + 64) / 8) with (f / 8 + 8) by (clear - F8; Z.div_mod_to_equations; lia); lia | unfold IMG_TOP in FIMG; lia | apply shfree_nil]. }
astep. astep. astep. astep. sh_if.
unfold IMG_TOP in FIMG. pose proof SFR as SFR'. unfold SH_LO, SH_HI in SFR'. unfold SH_LO, SH_HI in SOFF.
ato 0xb68b8. astep. rewrite <- Esf.
ato 0xb690c. astep. rewrite <- EMP.
ato 0xb696c. rewrite sx32_small by (unfold int31; lia).
ato 0x98638.
replace (OUT + sbd_frame_size s ≪ 2) with (OUT + 4 * sbd_frame_size s) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
replace (OUT + sbd_frame_size s ≪ 2) with (OUT + 4 * sbd_frame_size s) in FR by (rewrite Z.shiftl_mul_pow2 by lia; lia).
apply (rw_cells_CB4_C4 asegs _ _ [C8 _; C8 _; C8 _; CB 8 _]) in FRB. destruct FRB as (dtx & FRB).
apply evt_done. do 15 eexists. exists dtx. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
split; [exact FR|]. split; [exact FRB| exact FRS].
Qed.

Definition RA_sbd_native : Z := 0xb69a4.
Definition RA_sbd_ctl103 : Z := 0xb69c8.

Definition R_P (usp S OUT f MODE : Z) (gp tp : word) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xt3 xt4 xt5 xt6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 (usp + -608)) gp tp xt0 xt1 xt2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -608)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 (S + 8)) xs3 xs4 (Z_to_bv 64 (Z.shiftr (S + 8) 3 + SHB)) (Z_to_bv 64 f) (Z_to_bv 64 MODE) (Z_to_bv 64 f)
(Z_to_bv 64 SHB) (Z_to_bv 64 OUT) (Z_to_bv 64 S) xt3 xt4 xt5 xt6.

Lemma sbd_w3 : forall (usp S OUT A f sf MODE : Z) (g : nat -> word) (s : sbd_state bptr) (a : sb_addrs)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word) F fc (m : mem),
usp < 2^63 -> SH_HI <= usp + -608 ->
rw_cells asegs m (usp + -608) (sb_fr g) -> g 38%nat = Z_to_bv 64 A ->
rw_cells asegs m S (sbp_hdr s a) -> aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= usp + -608 -> (S + 160 <= SH_LO \/ SH_HI <= S) ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (R_P usp S OUT f MODE gp tp (Z_to_bv 64 RA_sbd_native) t0 t1 t2 (Z_to_bv 64 (a_low a)) (Z_to_bv 64 A) (Z_to_bv 64 OUT) a3 a4 a5 a6 a7
(Z_to_bv 64 sf) s4 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_decode_native) fc None m1 (seg_rom asegs)
/\ munch [(usp + -608, usp + -160)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 (usp + -608) (sb_fr (fupds g [(13%nat, Z_to_bv 64 sf)])))
(MS (R_P usp S OUT f MODE gp tp (Z_to_bv 64 RA_sbd_ctl104) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 sf) s4 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_ctl104)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SPH LOS FR E38 HD OBS S8 SPOS SLO SOFF MI.
unfold R_P, RA_sbd_ctl104, RA_sbd_native, A_speex_decode_native in *.
replace (ret_pc (Z_to_bv 64 0xb6984)) with (Z_to_bv 64 0xb6984) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'. unfold SH_LO, SH_HI in SOFF.
pose proof (munch_refl [(usp + -608, usp + -160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -608, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold sb_fr in FR. cbn [map seq] in FR. unfold sbp_hdr in HD.
ato 0xb699c. rewrite E38.
ato 0x98530.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact FR].
Qed.

Lemma sbd_w4 : forall (usp S OUT f MODE : Z) (s : sbd_state bptr) (a : sb_addrs)
(gp tp t0 t1 t2 ret a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word) F fc (m : mem),
usp < 2^63 -> 0 < f -> f + 64 < 2^63 ->
rw_cells asegs m S (sbp_hdr s a) -> aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 < 2^63 ->
mem_inv asegs m ->
evt asegs (fun ms => exists (xa3 : word),
ms = MS (R_P usp S OUT f MODE gp tp (Z_to_bv 64 RA_sbd_ctl103) t0 t1 t2 (Z_to_bv 64 (a_low a)) (Z_to_bv 64 103) (Z_to_bv 64 (f + 32)) xa3 a4 a5 a6 a7
(Z_to_bv 64 (f + 32)) ret t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_decoder_ctl) fc None m (seg_rom asegs))
(MS (R_P usp S OUT f MODE gp tp (Z_to_bv 64 RA_sbd_native) t0 t1 t2 ret a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_native)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SPH F0 F1 HD OBS S8 SPOS SHI MI.
unfold R_P, RA_sbd_ctl103, RA_sbd_native, A_speex_decoder_ctl in *.
replace (ret_pc (Z_to_bv 64 0xb69a4)) with (Z_to_bv 64 0xb69a4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold sbp_hdr in HD.
ato 0x98638.
apply evt_done. eexists. reflexivity.
Qed.

Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac tlia ::= (try unfold BITS_SIZEOF in * ); tlia_one.
Local Ltac slia ::= (try unfold BITS_SIZEOF in * ); first [ exact I | lia | split; [lia|exact I] ].

Lemma sbd_w5x : forall (usp S OUT f MODE ret : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word) F fc (m : mem),
-2 <= ret < 0 ->
evt asegs (fun ms => ms = MS (R_P usp S OUT f MODE gp tp (Z_to_bv 64 RA_sbd_ctl103) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 (Z_to_bv 64 ret) t3 t4 t5 t6)
F (Z_to_bv 64 0xb7ed0) fc None m (seg_rom asegs))
(MS (R_P usp S OUT f MODE gp tp (Z_to_bv 64 RA_sbd_ctl103) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 (Z_to_bv 64 ret) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_ctl103)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros RNG. unfold R_P, RA_sbd_ctl103.
replace (ret_pc (Z_to_bv 64 0xb69c8)) with (Z_to_bv 64 0xb69c8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
assert (C : ret = -2 \/ ret = -1) by lia. destruct C as [-> | ->]; ato 0xb7ed0; apply evt_done; reflexivity.
Qed.

Lemma sbd_w5 : forall (usp lo S OUT A D f MODE : Z) (g : nat -> word) (s : sbd_state bptr) (b : bits_st bptr) (pad1 : list byte)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_fr g) -> g 38%nat = Z_to_bv 64 A ->
rw_cells asegs m (S + 136) (sbp_cfg s pad1) -> sbd_encode_submode s = 1 ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= lo -> (S + 160 <= SH_LO \/ SH_HI <= S) ->
bits_rep asegs m A D b -> bits_ok b -> aobj asegs m A BITS_SIZEOF -> aobj asegs m D (sb_buf_size b) ->
(A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A) -> IMG_TOP <= A -> A + BITS_SIZEOF <= lo -> D + sb_buf_size b <= lo ->
stk asegs m lo (usp + -608) -> lo <= usp + -608 - 64 -> SH_HI <= lo -> usp < 2^63 ->
client_consts m -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
ms = MS (R_P usp S OUT f MODE gp tp xra xt0 xt1 xt2 (Z_to_bv 64 (sbw_id b)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 s3 (Z_to_bv 64 A) xt3 xt4 xt5 xt6)
F (Z_to_bv 64 0xb6a4c) fc None m1 (seg_rom asegs)
/\ munch [(A, A + BITS_SIZEOF); (usp + -672, usp + -160)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -608)
/\ rw_cells asegs m1 (usp + -608) (sb_fr (fupds g [(44%nat, Z_to_bv 64 (S + 144)); (43%nat, Z_to_bv 64 (S + 152))]))
/\ bits_rep asegs m1 A D (sbw_bits b) /\ bits_ok (sbw_bits b) /\ sb_buf_size (sbw_bits b) = sb_buf_size b /\ 0 <= sbw_id b < 8)
(MS (R_P usp S OUT f MODE gp tp (Z_to_bv 64 RA_sbd_ctl103) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 (Z_to_bv 64 0) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_ctl103)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FR E38 CFG ESM OBS S8 SPOS SLO SOFF REP OK OBA OBD ASH AIMG ALO DLO ST LO LOS SPH CC MI.
unfold R_P, RA_sbd_ctl103 in *.
replace (ret_pc (Z_to_bv 64 0xb69c8)) with (Z_to_bv 64 0xb69c8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'. pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'. pose proof ASH as ASH'. unfold SH_LO, SH_HI in ASH'.
unfold IMG_TOP in AIMG.
pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in G1, G2, G3, G4.
pose proof (munch_refl [(A, A + BITS_SIZEOF); (usp + -672, usp + -160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof OBA as (OBA0 & OBA1 & _).
assert (OF : offsh [(A, A + BITS_SIZEOF); (usp + -672, usp + -160)]) by (cbn; unfold SH_LO, SH_HI, BITS_SIZEOF in *; lia).
unfold sb_fr in FR. cbn [map seq] in FR. rewrite E38 in FR. unfold sbp_cfg in CFG. rewrite ESM in CFG.
destruct REP as ((rj0 & Lrj0 & OBJ) & (bs0 & DAT & Hbs0) & SIDE0). unfold bits_cells in OBJ.
assert (Lbs0 : Z.of_nat (length bs0) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs0, zlength_map_unsigned in OK'. lia. }
pose proof SIDE0 as (AL & Apos & Dpos & _).
unfold APP_TOP, BITS_SIZEOF in OBA1. rename OBA1 into OBAhi. rename OBA0 into OBAlo. unfold BITS_SIZEOF in OBA.
ato 0xb69d4. astep. sh_if.
ato 0xb6a04. astep. sh_if.
ato 0xb6a10.
rebase_bits A D b rj0 bs0.
astep.
call (speex_bits_remaining_walk A D (usp + -608) lo b _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK OBA1 ST ltac:(lia) LOS ltac:(lia) ALO DLO CC1).
all: try eassumption.
subst x. clear REP1 OBA1 OBD1 CC1.
pose proof (bits_ints A D b OK SIDE0) as (In & _ & _ & _ & _ & _ & Rc & Rb & Rp & _).
assert (RNG : -1 <= speex_bits_remaining b < 2^31).
{ pose proof (speex_bits_remaining_spec b OK) as (R0 & R1). unfold int31 in In.
destruct (Z.eq_dec (sb_overflow b) 0) as [E|E]; [destruct (R0 E) as [E1 E2]; rewrite E1 in *; unfold bits_pos in *; lia| rewrite (R1 E); lia]. }
replace (ret_pc (Z_to_bv 64 748052)) with (Z_to_bv 64 748052) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
destruct (Z_le_gt_dec (speex_bits_remaining b) 0) as [KR|KR].
- astep. sh_if.
ato 0xb6a4c.
assert (EW : sbw_wb b = (0, b)) by (unfold sbw_wb; replace (0 <? speex_bits_remaining b) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
assert (EID : sbw_id b = 0) by (unfold sbw_id; rewrite EW; reflexivity).
assert (EB : sbw_bits b = b) by (unfold sbw_bits; rewrite EW; reflexivity).
rewrite EID, EB.
apply evt_done. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact PC|].
split; [rewrite <- E38 in FR; exact FR|]. split; [exact POST|]. split; [exact OK|]. split; [reflexivity| lia].
- astep. sh_if.
destruct POST as ((rj1 & Lrj1 & OBJ) & (bs1 & DAT & Hbs1) & SIDE1). unfold bits_cells in OBJ.
ato 0xb6a1c.
rebase_bits A D b rj1 bs1. astep.
call (speex_bits_peek_walk A D (usp + -608) lo b _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK OBA1 OBD1 ASH PC ltac:(lia) LOS ltac:(lia) ALO DLO CC1).
all: try eassumption.
subst x. clear REP1 OBA1 OBD1 CC1.
destruct (speex_bits_peek b) as [wbv bp] eqn:EPK. cbn [fst snd] in *.
pose proof (speex_bits_peek_ok b wbv bp OK EPK) as (OKp & WBV & BPC).
assert (SZp : sb_buf_size bp = sb_buf_size b) by (destruct BPC as [-> | ->]; reflexivity).
assert (SWB : sbw_wb b = (wbv, bp)) by (unfold sbw_wb; replace (0 <? speex_bits_remaining b) with true by (symmetry; apply Z.ltb_lt; lia); exact EPK).
replace (ret_pc (Z_to_bv 64 748064)) with (Z_to_bv 64 748064) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
destruct (Z.eq_dec wbv 0) as [KW|KW].
+ subst wbv. ato 0xb6a4c.
assert (EID : sbw_id b = 0) by (unfold sbw_id; rewrite SWB; reflexivity).
assert (EB : sbw_bits b = bp) by (unfold sbw_bits; rewrite SWB; reflexivity).
rewrite EID, EB.
apply evt_done. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact PC|].
split; [rewrite <- E38 in FR; exact FR|]. split; [exact POST|]. split; [exact OKp|]. split; [exact SZp| lia].
+ assert (wbv = 1) by lia. subst wbv.
destruct POST as ((rj2 & Lrj2 & OBJ) & (bs2 & DAT & Hbs2) & SIDE2). unfold bits_cells in OBJ.
ato 0xb6a2c.
rebase_bits A D bp rj2 bs2. astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -608) lo bp 1 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OKp ltac:(lia) OBA1 ltac:(rewrite SZp; exact OBD1) (ASH : _ \/ _) ltac:(lia) LOS ltac:(lia) ALO ltac:(rewrite SZp; exact DLO)).
all: try eassumption.
clear PC0. clear REP1 OBA1 OBD1 CC1.
change (snd (speex_bits_unpack_unsigned bp 1)) with (ub bp 1) in *.
pose proof (ub_ok bp 1 OKp ltac:(lia)) as (OK1 & SZ1 & _).
destruct POST as ((rj3 & Lrj3 & OBJ) & (bs3 & DAT & Hbs3) & SIDE3). unfold bits_cells in OBJ.
replace (ret_pc (Z_to_bv 64 748080)) with (Z_to_bv 64 748080) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0xb6a38.
rebase_bits A D (ub bp 1) rj3 bs3. astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -608) lo (ub bp 1) 3 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK1 ltac:(lia) OBA1 ltac:(rewrite SZ1, SZp; exact OBD1) (ASH : _ \/ _) ltac:(lia) LOS ltac:(lia) ALO ltac:(rewrite SZ1, SZp; exact DLO)).
all: try eassumption.
subst x28. clear REP1 OBA1 OBD1 CC1.
change (snd (speex_bits_unpack_unsigned (ub bp 1) 3)) with (ub (ub bp 1) 3) in *. change (fst (speex_bits_unpack_unsigned (ub bp 1) 3)) with (uv (ub bp 1) 3) in *.
pose proof (ub_ok (ub bp 1) 3 OK1 ltac:(lia)) as (OK3 & SZ3 & V3). change (2 ^ 3) with 8 in V3.
replace (ret_pc (Z_to_bv 64 748092)) with (Z_to_bv 64 748092) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0xb6a4c.
assert (EID : sbw_id b = uv (ub bp 1) 3) by (unfold sbw_id; rewrite SWB; reflexivity).
assert (EB : sbw_bits b = ub (ub bp 1) 3) by (unfold sbw_bits; rewrite SWB; reflexivity).
rewrite EID, EB.
apply evt_done. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact PC|].
split; [rewrite <- E38 in FR; exact FR|]. split; [exact POST|]. split; [exact OK3|]. split; [rewrite SZ3, SZ1; exact SZp| exact V3].
Qed.

Definition sb_id_valid (mo : spx_mode) (id : Z) : bool :=
(id =? 0) || match submode_at (sbm_submodes mo) id with Some _ => true | None => false end.
Lemma sbd_w6 : forall (usp S OUT A f MODE id : Z) (g : nat -> word) (s : sbd_state bptr) (pad1 : list byte) (oid : word)
(gp tp ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_fr g) -> g 43%nat = Z_to_bv 64 (S + 152) -> g 44%nat = Z_to_bv 64 (S + 144) ->
rw_cells asegs m (S + 136) (sbp_cfg s pad1) -> rw_cells asegs m (S + 152) [C4 oid] ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= usp + -608 -> (S + 160 <= SH_LO \/ SH_HI <= S) -> IMG_TOP <= S ->
(sbd_mode s = ModeWB \/ sbd_mode s = ModeUWB) -> MODE = sbmode_struct (sbd_mode s) -> aobj asegs m MODE 216 -> lib_consts m ->
0 <= id < 8 -> SH_HI <= usp + -608 -> usp < 2^63 ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (xa0 xa1 : word),
ms = MS (R_P usp S OUT f MODE gp tp ra t0 t1 t2 xa0 xa1 a2 (Z_to_bv 64 (S + 144)) (Z_to_bv 64 (S + 152)) a5 a6 a7 s3 (Z_to_bv 64 A) t3 t4 t5 t6)
F (Z_to_bv 64 (if sb_id_valid (sbd_mode s) id then 0xb6ab0 else 0xb8114)) fc None m1 (seg_rom asegs)
/\ munch [(S + 152, S + 156)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 (S + 152) [C4 (Z_to_bv 64 id)])
(MS (R_P usp S OUT f MODE gp tp ra t0 t1 t2 (Z_to_bv 64 id) a1 a2 a3 a4 a5 a6 a7 s3 (Z_to_bv 64 A) t3 t4 t5 t6)
F (Z_to_bv 64 0xb6a4c) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FR E43 E44 CFG IDC OBS S8 SPOS SLO SOFF SIMG HMO EMODE OBM LC HID LOS SPH MI.
unfold R_P in *. unfold SH_LO, SH_HI in SOFF. unfold IMG_TOP in SIMG. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [(S + 152, S + 156)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(S + 152, S + 156)]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold sb_fr in FR. cbn [map seq] in FR. rewrite E43, E44 in FR. unfold sbp_cfg in CFG.
assert (ESUB : sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR (sbd_mode s) = MODE + 40).
{ subst MODE. destruct HMO as [-> | ->]; reflexivity. }
rewrite ESUB in CFG.
assert (M8 : MODE mod 8 = 0) by (subst MODE; destruct HMO as [-> | ->]; reflexivity).
assert (MR : 0x10000 <= MODE /\ MODE + 216 <= 0x652000) by (subst MODE; destruct HMO as [-> | ->]; cbn; unfold A_sb_wb_mode, A_sb_uwb_mode; lia).
assert (C : id = 0 \/ id = 1 \/ id = 2 \/ id = 3 \/ id = 4 \/ id = 5 \/ id = 6 \/ id = 7) by lia.
destruct HMO as [EMO | EMO]; rewrite EMO in *; cbn [sbmode_struct] in EMODE.
- pose proof (lib_const m A_sb_wb_mode LC_sb_wb_mode LC ltac:(lc_in)) as TAB. rewrite <- EMODE in TAB. unfold LC_sb_wb_mode in TAB. unfold A_sb_wb_mode in EMODE.
destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]].
all: match goal with |- context [if ?c then _ else _] => let v := eval vm_compute in c in change c with v end; cbv iota.
all: lazymatch goal with
| |- context [Z_to_bv 64 0xb6ab0] => ato 0xb6ab0
| |- context [Z_to_bv 64 0xb8114] => ato 0xb8114
end.
all: apply evt_done; do 3 eexists; (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]); exact IDC.
- pose proof (lib_const m A_sb_uwb_mode LC_sb_uwb_mode LC ltac:(lc_in)) as TAB. rewrite <- EMODE in TAB. unfold LC_sb_uwb_mode in TAB. unfold A_sb_uwb_mode in EMODE.
destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]].
all: match goal with |- context [if ?c then _ else _] => let v := eval vm_compute in c in change c with v end; cbv iota.
all: lazymatch goal with
| |- context [Z_to_bv 64 0xb6ab0] => ato 0xb6ab0
| |- context [Z_to_bv 64 0xb8114] => ato 0xb8114
end.
all: apply evt_done; do 3 eexists; (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]); exact IDC.
Qed.

Definition SB_GOT_STDERR : Z := 0xf44f8.
Definition SB_STDERR_VAR : Z := 0xf3790.
Definition SB_FMT_NOTIFY : Z := 0x272c0.
Definition SB_MSG_INVALID : Z := 0x27240.
Definition sb_e_fprintf : Z := 0x56c1c.
Definition RA_sbd_fprintf : Z := 0xb8144.
Lemma sbd_w7 : forall (usp S OUT f MODE errf : Z) (gp tp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word) F fc (m : mem),
aobj asegs m SB_STDERR_VAR 8 ->
ro_cells asegs m SB_GOT_STDERR [C8 (Z_to_bv 64 SB_STDERR_VAR)] -> ro_cells asegs m SB_STDERR_VAR [C8 (Z_to_bv 64 errf)] ->
mem_inv asegs m ->
evt asegs (fun ms =>
ms = MS (R_P usp S OUT f MODE gp tp (Z_to_bv 64 RA_sbd_fprintf) t0 t1 t2 (Z_to_bv 64 errf) (Z_to_bv 64 SB_FMT_NOTIFY) (Z_to_bv 64 SB_MSG_INVALID)
a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6)
F (Z_to_bv 64 sb_e_fprintf) fc None m (seg_rom asegs))
(MS (R_P usp S OUT f MODE gp tp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6) F (Z_to_bv 64 0xb8114) fc None m (seg_rom asegs)).
Proof.
intros until m. intros OBV GOTE VARE MI.
unfold R_P, SB_GOT_STDERR, SB_STDERR_VAR, SB_FMT_NOTIFY, SB_MSG_INVALID, sb_e_fprintf, RA_sbd_fprintf in *.
assert (V8 : 997264 mod 8 = 0) by reflexivity.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM. assert (OF : offsh []) by exact I.
ato 0x56c1c.
apply evt_done. reflexivity.
Qed.
Lemma sbd_w8 : forall (usp S OUT f MODE : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word) F fc (m : mem),
evt asegs (fun ms => ms = MS (R_P usp S OUT f MODE gp tp (Z_to_bv 64 RA_sbd_fprintf) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 (Z_to_bv 64 (-2)) t3 t4 t5 t6)
F (Z_to_bv 64 0xb7ed0) fc None m (seg_rom asegs))
(MS (R_P usp S OUT f MODE gp tp (Z_to_bv 64 RA_sbd_fprintf) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_fprintf)) fc None m (seg_rom asegs)).
Proof.
intros until m. unfold R_P, RA_sbd_fprintf.
replace (ret_pc (Z_to_bv 64 0xb8144)) with (Z_to_bv 64 0xb8144) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0xb7ed0. apply evt_done. reflexivity.
Qed.

Lemma sbd_m : forall (usp S OUT f MODE id : Z) (g : nat -> word) (s : sbd_state bptr) (pad1 : list byte)
(gp tp ra t0 t1 t2 a0 a1 a2 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_fr g) ->
rw_cells asegs m (S + 136) (sbp_cfg s pad1) -> rw_cells asegs m (S + 152) [C4 (Z_to_bv 64 id)] ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= usp + -608 -> (S + 160 <= SH_LO \/ SH_HI <= S) ->
(sbd_mode s = ModeWB \/ sbd_mode s = ModeUWB) -> MODE = sbmode_struct (sbd_mode s) -> aobj asegs m MODE 216 -> lib_consts m ->
0 <= id < 8 -> SH_HI <= usp + -608 -> usp < 2^63 ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (xa0 xa1 : word),
ms = MS (R_P usp S OUT f MODE gp tp ra t0 t1 t2 xa0 xa1 a2 (Z_to_bv 64 (S + 144)) (Z_to_bv 64 (S + 152)) a5 a6 a7 s3 s4 t3 t4 t5 t6)
F (Z_to_bv 64 (match submode_at (sbm_submodes (sbd_mode s)) id with Some _ => 0xb6b10 | None => 0xb7cec end)) fc None m1 (seg_rom asegs)
/\ munch [(usp + -608, usp + -160)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 (usp + -608) (sb_fr (fupds g [(42%nat, Z_to_bv 64 (Z.shiftr (S + 144) 3 + SHB)); (41%nat, Z_to_bv 64 (Z.shiftr (S + 152) 3 + SHB))])))
(MS (R_P usp S OUT f MODE gp tp ra t0 t1 t2 a0 a1 a2 (Z_to_bv 64 (S + 144)) (Z_to_bv 64 (S + 152)) a5 a6 a7 s3 s4 t3 t4 t5 t6)
F (Z_to_bv 64 0xb6ab0) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FR CFG IDC OBS S8 SPOS SLO SOFF HMO EMODE OBM LC HID LOS SPH MI.
unfold R_P in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [(usp + -608, usp + -160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -608, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold sb_fr in FR. cbn [map seq] in FR. unfold sbp_cfg in CFG.
assert (ESUB : sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR (sbd_mode s) = MODE + 40).
{ subst MODE. destruct HMO as [-> | ->]; reflexivity. }
rewrite ESUB in CFG.
assert (M8 : MODE mod 8 = 0) by (subst MODE; destruct HMO as [-> | ->]; reflexivity).
assert (MR : 0x10000 <= MODE /\ MODE + 216 <= 0x652000) by (subst MODE; destruct HMO as [-> | ->]; cbn; unfold A_sb_wb_mode, A_sb_uwb_mode; lia).
assert (C : id = 0 \/ id = 1 \/ id = 2 \/ id = 3 \/ id = 4 \/ id = 5 \/ id = 6 \/ id = 7) by lia.
destruct HMO as [EMO | EMO]; rewrite EMO in *; cbn [sbmode_struct] in EMODE.
- pose proof (lib_const m A_sb_wb_mode LC_sb_wb_mode LC ltac:(lc_in)) as TAB. rewrite <- EMODE in TAB. unfold LC_sb_wb_mode in TAB. unfold A_sb_wb_mode in EMODE.
destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]].
all: match goal with |- context [match ?c with Some _ => _ | None => _ end] => let v := eval vm_compute in c in change c with v end; cbv iota.
all: ato 0xb6ae8; rewrite sx32_small by (unfold int31; lia).
all: lazymatch goal with
| |- context [Z_to_bv 64 0xb6b10] => ato 0xb6b10
| |- context [Z_to_bv 64 0xb7cec] => ato 0xb7cec
end.
all: apply evt_done; do 3 eexists; (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]); exact FR.
- pose proof (lib_const m A_sb_uwb_mode LC_sb_uwb_mode LC ltac:(lc_in)) as TAB. rewrite <- EMODE in TAB. unfold LC_sb_uwb_mode in TAB. unfold A_sb_uwb_mode in EMODE.
destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]].
all: match goal with |- context [match ?c with Some _ => _ | None => _ end] => let v := eval vm_compute in c in change c with v end; cbv iota.
all: ato 0xb6ae8; rewrite sx32_small by (unfold int31; lia).
all: lazymatch goal with
| |- context [Z_to_bv 64 0xb6b10] => ato 0xb6b10
| |- context [Z_to_bv 64 0xb7cec] => ato 0xb7cec
end.
all: apply evt_done; do 3 eexists; (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]); exact FR.
Qed.

Definition sb_e_allocas_unpoison : Z := 0x51e64.
Definition RA_sbd_unpoison_x : Z := 0xb7ee8.
Definition sb_fshadow_x : list cell :=
[C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-8));
C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))].
Lemma sbd_x1 : forall (usp f sf : Z) (g : nat -> word) (topw : word)
(ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_fr g) -> g 13%nat = Z_to_bv 64 sf -> g 52%nat = topw ->
rw_cells asegs m sf sb_fshadow ->
0 < f -> f mod 64 = 0 -> f + 64 <= APP_TOP -> sf = Z.shiftr f 3 + SHB -> SH_HI <= usp + -608 -> usp < 2^63 ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR (Z_to_bv 64 RA_sbd_unpoison_x) (Z_to_bv 64 (usp + -608)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -608))
topw (Z_to_bv 64 (usp + -192)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 sf) s3 s4 s5 (Z_to_bv 64 f) s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 sb_e_allocas_unpoison) fc None m1 (seg_rom asegs)
/\ munch [(sf, sf + 8)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 sf sb_fshadow_x)
(MS (mkR ra (Z_to_bv 64 (usp + -608)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -608))
a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 f) s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xb7ed0) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FR E13 E52 FRS F0 F64 FTOP Esf LOS SPH MI.
unfold RA_sbd_unpoison_x, sb_e_allocas_unpoison, sb_fshadow, sb_fshadow_x in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (shad_range_al f 64 ltac:(lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) FTOP) as SW.
rewrite <- shad_shiftr, <- Esf in SW. change (64 / 8) with 8 in SW. unfold SH_LO, SH_HI in SW.
pose proof (munch_refl [(sf, sf + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold sb_fr in FR. cbn [map seq] in FR. rewrite E13, E52 in FR.
ato 0x51e64.
replace (usp + -608 + 416) with (usp + -192) by lia.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact FRS].
Qed.

Lemma sbd_x2 : forall (usp f sf : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 : word) (hd : word) F fc (m : mem),
0 < f -> f mod 64 = 0 -> f + 64 <= usp + -608 -> f + 64 <= APP_TOP -> (f + 64 <= SH_LO \/ SH_HI <= f) -> sf = Z.shiftr f 3 + SHB ->
SH_HI <= usp + -608 -> usp < 2^63 ->
rw_cells asegs m f [C8 hd] -> rw_cells asegs m sf sb_fshadow_x ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR (Z_to_bv 64 RA_sbd_unpoison_x) (Z_to_bv 64 (usp + -608)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -608))
(Z_to_bv 64 (-11)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 sf) s3 s4 s5 (Z_to_bv 64 f) s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xb7f1c) fc None m1 (seg_rom asegs)
/\ munch [(f, f + 56); (sf, sf + 8)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 sf (map C1 (repeat bF5 8)))
(MS (mkR (Z_to_bv 64 RA_sbd_unpoison_x) (Z_to_bv 64 (usp + -608)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -608))
a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 sf) s3 s4 s5 (Z_to_bv 64 f) s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_unpoison_x)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros F0 F64 FLO FTOP FSH Esf LOS SPH FRB FRS MI.
unfold RA_sbd_unpoison_x, sb_fshadow_x, bF5 in *. cbn [map repeat] in *. unfold APP_TOP in *.
replace (ret_pc (Z_to_bv 64 0xb7ee8)) with (Z_to_bv 64 0xb7ee8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FSH as FSH'. unfold SH_LO, SH_HI in FSH'.
pose proof (shad_range_al f 64 ltac:(lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) ltac:(unfold APP_TOP; lia)) as SW.
rewrite <- shad_shiftr, <- Esf in SW. change (64 / 8) with 8 in SW. unfold SH_LO, SH_HI in SW.
pose proof (munch_refl [(f, f + 56); (sf, sf + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0xb7ef4. astep. sh_if.
ato 0xb7f1c.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact FRS].
Qed.

Lemma sbd_x3 : forall (usp lo f fl : Z) (g : nat -> word) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F0 : bvmap 5 word) (cra c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : word) F fc (m : mem),
stk asegs m lo (usp + -608) -> lo <= usp + -608 -> usp < 2^63 -> 0 < f -> f + 64 <= lo ->
0 < fl -> fl + 1 <= lo ->
rw_cells asegs m (usp + -608) (sb_fr g) -> rw_cells asegs m (usp + -160) (sb_saves F0 cra c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11) ->
ro_cells asegs m (f + 56) [C8 (Z_to_bv 64 fl)] -> rw_cells asegs m fl [C1 (Z_to_bv 8 1)] ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (F' : bvmap 5 word),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 s4 a1 a2 a3 a4 a5 a6 a7 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 t3 t4 t5 t6)
F' (ret_pc cra) fc None m1 (seg_rom asegs)
/\ munch [(fl, fl + 1)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp
/\ rw_cells asegs m1 fl [C1 z8])
(MS (mkR ra (Z_to_bv 64 (usp + -608)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -608)) a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 (Z_to_bv 64 f) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xb7f1c) fc None m (seg_rom asegs)).
Proof.
intros until m. intros ST LO SPH F0' FLO L0 LLO FR SV FLP FLG MI.
unfold sb_saves, z8 in *. unfold sb_fr in FR. cbn [map seq] in FR.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.

ato 0xb7fa4. release_frame FR ST (usp + -160). release_frame SV ST usp. astep.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact FLG].
Qed.

Definition sb_e_alloca_poison : Z := 0x51d38.
Definition RA_sbd_pois1 : Z := 0xb6b94.

Lemma sbd_v1 : forall (usp lo S OUT f MODE : Z) (g : nat -> word) (s : sbd_state bptr) (a : sb_addrs)
(gp tp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_fr g) -> rw_cells asegs m S (sbp_hdr s a) -> sbd_nbSubframes s = 4 ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= lo -> (S + 160 <= SH_LO \/ SH_HI <= S) ->
stk asegs m lo (usp + -608) -> lo <= usp + -608 - 4192 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (xa2 : word) (jh : list byte),
ms = MS (mkR (Z_to_bv 64 RA_sbd_pois1) (Z_to_bv 64 (usp + -704)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -608))
(Z_to_bv 64 (usp + -672)) (Z_to_bv 64 16) xa2 a3 a4 a5 a6 a7
(Z_to_bv 64 (S + 8)) (Z_to_bv 64 (usp + -704)) (Z_to_bv 64 (S + 28)) (Z_to_bv 64 (Z.shiftr (S + 8) 3 + SHB)) (Z_to_bv 64 f) (Z_to_bv 64 MODE) (Z_to_bv 64 f)
(Z_to_bv 64 SHB) (Z_to_bv 64 OUT) (Z_to_bv 64 S) t3 t4 t5 t6)
F (Z_to_bv 64 sb_e_alloca_poison) fc None m1 (seg_rom asegs)
/\ munch [(usp + -4704, usp + -160)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -704)
/\ rw_cells asegs m1 (usp + -608) (sb_fr (fupds g [(36%nat, Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB)); (6%nat, Z_to_bv 64 (usp + -608)); (24%nat, Z_to_bv 64 (usp + -672))]))
/\ rw_cells asegs m1 (usp + -704) [CB 96 jh])
(MS (R_P usp S OUT f MODE gp tp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6) F (Z_to_bv 64 0xb6b10) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FR HD ENS OBS S8 SPOS SLO SOFF ST LO LOS SPH U32 MI.
unfold R_P, RA_sbd_pois1, sb_e_alloca_poison in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -4704, usp + -160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -4704, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold sb_fr in FR. cbn [map seq] in FR. unfold sbp_hdr in HD. rewrite ENS in HD.
carve_frame 96%nat ST. rename FR0 into HULL.
carve_frame 3992%nat ST. rename FR0 into JK1.
carve_frame 8%nat ST. rename FR0 into P1.
apply (rw_cells_split_CB asegs _ _ [] 8 _ [] [8]%nat) in P1; [| reflexivity]. cbn [mk_CB_cells app] in P1.
ato 0xb6b34. rewrite zx32_small by lia. ato 0xb6b6c. alits.
astep. astep.
replace (usp + -608 - 96) with (usp + -704) by lia. rewrite ?Z.mod_small by lia.
rewrite (land_m32_al (usp + -704)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
astep. astep. replace (usp + -608 - 4096) with (usp + -4704) by lia.
astep. astep. sh_if.
ato 0x51d38.
release_frame P1 ST (usp + -4696). release_frame JK1 ST (usp + -704).
replace (usp + -704 + 32) with (usp + -672) in * by lia.
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact HULL].
Qed.

Definition RA_sbd_pois2 : Z := 0xb6c0c.

Definition R_V (usp sp S OUT f MODE : Z) (gp tp : word) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 sp) gp tp xt0 xt1 xt2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -608)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 (S + 8)) xs3 (Z_to_bv 64 (S + 28)) (Z_to_bv 64 (Z.shiftr (S + 8) 3 + SHB)) (Z_to_bv 64 f) (Z_to_bv 64 MODE) (Z_to_bv 64 f)
(Z_to_bv 64 SHB) (Z_to_bv 64 OUT) (Z_to_bv 64 S) xt3 xt4 xt5 xt6.

Lemma sbd_v2 : forall (usp lo S OUT f MODE : Z) (g : nat -> word) (s : sbd_state bptr) (a : sb_addrs)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_fr g) -> g 36%nat = Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB) -> rw_cells asegs m S (sbp_hdr s a) -> sbd_nbSubframes s = 4 ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= lo -> (S + 160 <= SH_LO \/ SH_HI <= S) ->
stk asegs m lo (usp + -704) -> lo <= usp + -704 - 4192 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (xa2 : word) (jh : list byte),
ms = MS (R_V usp (usp + -800) S OUT f MODE gp tp (Z_to_bv 64 RA_sbd_pois2) t0 t1 t2 (Z_to_bv 64 (usp + -768)) (Z_to_bv 64 16) xa2 a3 a4 a5 a6 a7
(Z_to_bv 64 (usp + -800)) t3 t4 t5 t6)
F (Z_to_bv 64 sb_e_alloca_poison) fc None m1 (seg_rom asegs)
/\ munch [(usp + -4800, usp + -160)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -800)
/\ rw_cells asegs m1 (usp + -608) (sb_fr (fupds g [(52%nat, Z_to_bv 64 (usp + -704)); (14%nat, Z_to_bv 64 (usp + -768))]))
/\ rw_cells asegs m1 (usp + -800) [CB 96 jh])
(MS (R_V usp (usp + -704) S OUT f MODE gp tp (Z_to_bv 64 RA_sbd_pois1) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (usp + -704)) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_pois1)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FR E36 HD ENS OBS S8 SPOS SLO SOFF ST LO LOS SPH U32 MI.
unfold R_V, RA_sbd_pois1, RA_sbd_pois2, sb_e_alloca_poison in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xb6b94)) with (Z_to_bv 64 0xb6b94) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -4800, usp + -160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -4800, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold sb_fr in FR. cbn [map seq] in FR. rewrite E36 in FR. unfold sbp_hdr in HD. rewrite ENS in HD.
carve_frame 96%nat ST. rename FR0 into HULL.
carve_frame 3992%nat ST. rename FR0 into JK1.
carve_frame 8%nat ST. rename FR0 into P1.
apply (rw_cells_split_CB asegs _ _ [] 8 _ [] [8]%nat) in P1; [| reflexivity]. cbn [mk_CB_cells app] in P1.
ato 0xb6bac. rewrite zx32_small by lia. ato 0xb6be4. alits.
astep. astep.
replace (usp + -704 - 96) with (usp + -800) by lia. rewrite ?Z.mod_small by lia.
rewrite (land_m32_al (usp + -800)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
astep. astep. replace (usp + -704 - 4096) with (usp + -4800) by lia.
astep. astep. sh_if.
ato 0x51d38.
release_frame P1 ST (usp + -4792). release_frame JK1 ST (usp + -800).
replace (usp + -800 + 32) with (usp + -768) in * by lia.
rewrite <- E36 in FR.
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact HULL].
Qed.

Definition RA_sbd_ctl100 : Z := 0xb6c2c.
Definition RA_sbd_ctl101 : Z := 0xb6c4c.

Lemma sbd_v3 : forall (usp S OUT f MODE : Z) (g : nat -> word) (s : sbd_state bptr) (a : sb_addrs)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_fr g) -> g 24%nat = Z_to_bv 64 (usp + -672) -> rw_cells asegs m S (sbp_hdr s a) ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= usp + -800 -> (S + 160 <= SH_LO \/ SH_HI <= S) ->
SH_HI <= usp + -800 -> usp < 2^63 ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (R_V usp (usp + -800) S OUT f MODE gp tp (Z_to_bv 64 RA_sbd_ctl100) t0 t1 t2 (Z_to_bv 64 (a_low a)) (Z_to_bv 64 100) (Z_to_bv 64 (usp + -672)) a3 a4 a5 a6 a7
(Z_to_bv 64 (usp + -800)) t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_decoder_ctl) fc None m1 (seg_rom asegs)
/\ munch [(usp + -608, usp + -160)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 (usp + -608) (sb_fr (fupds g [(52%nat, Z_to_bv 64 (usp + -800))])))
(MS (R_V usp (usp + -800) S OUT f MODE gp tp (Z_to_bv 64 RA_sbd_pois2) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (usp + -800)) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_pois2)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FR E24 HD OBS S8 SPOS SLO SOFF LOS SPH MI.
unfold R_V, RA_sbd_pois2, RA_sbd_ctl100, A_speex_decoder_ctl in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xb6c0c)) with (Z_to_bv 64 0xb6c0c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(usp + -608, usp + -160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -608, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold sb_fr in FR. cbn [map seq] in FR. rewrite E24 in FR. unfold sbp_hdr in HD.
ato 0x98638. rewrite <- E24 in FR.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact FR].
Qed.

Lemma sbd_v4 : forall (usp S OUT f MODE : Z) (g : nat -> word) (s : sbd_state bptr) (a : sb_addrs)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_fr g) -> g 14%nat = Z_to_bv 64 (usp + -768) -> rw_cells asegs m S (sbp_hdr s a) ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= usp + -800 -> (S + 160 <= SH_LO \/ SH_HI <= S) ->
SH_HI <= usp + -800 -> usp < 2^63 ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (R_V usp (usp + -800) S OUT f MODE gp tp (Z_to_bv 64 RA_sbd_ctl101) t0 t1 t2 (Z_to_bv 64 (a_low a)) (Z_to_bv 64 101) (Z_to_bv 64 (usp + -768)) a3 a4 a5 a6 a7
s3 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_decoder_ctl) fc None m1 (seg_rom asegs)
/\ munch [(usp + -608, usp + -160)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 (usp + -608) (sb_fr (fupds g [(35%nat, Z_to_bv 64 (S + 28))])))
(MS (R_V usp (usp + -800) S OUT f MODE gp tp (Z_to_bv 64 RA_sbd_ctl100) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_ctl100)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FR E14 HD OBS S8 SPOS SLO SOFF LOS SPH MI.
unfold R_V, RA_sbd_ctl101, RA_sbd_ctl100, A_speex_decoder_ctl in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xb6c2c)) with (Z_to_bv 64 0xb6c2c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(usp + -608, usp + -160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -608, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold sb_fr in FR. cbn [map seq] in FR. rewrite E14 in FR. unfold sbp_hdr in HD.
ato 0x98638. rewrite <- E14 in FR.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact FR].
Qed.

Definition RA_sbd_pois3 : Z := 0xb6cd8.
Definition RA_sbd_pois4 : Z := 0xb6d08.

Definition R_V5 (usp sp S OUT f MODE : Z) (gp tp : word) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xt3 xt4 xt5 xt6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 sp) gp tp xt0 xt1 xt2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -608)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
xs2 (Z_to_bv 64 8) (Z_to_bv 64 32) xs5 (Z_to_bv 64 f) (Z_to_bv 64 MODE) (Z_to_bv 64 f)
(Z_to_bv 64 SHB) (Z_to_bv 64 OUT) (Z_to_bv 64 S) xt3 xt4 xt5 xt6.

Lemma sbd_v5 : forall (usp lo S OUT f MODE : Z) (g : nat -> word) (s : sbd_state bptr) (a : sb_addrs)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_fr g) -> rw_cells asegs m S (sbp_hdr s a) -> sbd_lpcSize s = 8 ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= lo -> (S + 160 <= SH_LO \/ SH_HI <= S) ->
stk asegs m lo (usp + -800) -> lo <= usp + -800 - 4192 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (xa2 : word) (jh : list byte),
ms = MS (R_V5 usp (usp + -896) S OUT f MODE gp tp (Z_to_bv 64 RA_sbd_pois3) t0 t1 t2 (Z_to_bv 64 (usp + -864)) (Z_to_bv 64 32) xa2 a3 a4 a5 a6 a7
(Z_to_bv 64 96) (Z_to_bv 64 (usp + -896)) t3 t4 t5 t6)
F (Z_to_bv 64 sb_e_alloca_poison) fc None m1 (seg_rom asegs)
/\ munch [(usp + -4896, usp + -160)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -896)
/\ rw_cells asegs m1 (usp + -608) (sb_fr (fupds g [(47%nat, Z_to_bv 64 (Z.shiftr (S + 32) 3 + SHB)); (40%nat, Z_to_bv 64 (S + 32)); (25%nat, Z_to_bv 64 (usp + -864))]))
/\ rw_cells asegs m1 (usp + -896) [CB 96 jh])
(MS (R_V usp (usp + -800) S OUT f MODE gp tp (Z_to_bv 64 RA_sbd_ctl101) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_ctl101)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FR HD ELPC OBS S8 SPOS SLO SOFF ST LO LOS SPH U32 MI.
unfold R_V, R_V5, RA_sbd_ctl101, RA_sbd_pois3, sb_e_alloca_poison in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xb6c4c)) with (Z_to_bv 64 0xb6c4c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -4896, usp + -160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -4896, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold sb_fr in FR. cbn [map seq] in FR. unfold sbp_hdr in HD. rewrite ELPC in HD.
carve_frame 96%nat ST. rename FR0 into HULL.
carve_frame 3992%nat ST. rename FR0 into JK1.
carve_frame 8%nat ST. rename FR0 into P1.
apply (rw_cells_split_CB asegs _ _ [] 8 _ [] [8]%nat) in P1; [| reflexivity]. cbn [mk_CB_cells app] in P1.
ato 0xb6c70. rewrite zx32_small by lia. ato 0xb6cac. alits.
astep. astep.
replace (usp + -800 - 96) with (usp + -896) by lia. rewrite ?Z.mod_small by lia.
rewrite (land_m32_al (usp + -896)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
astep. astep. replace (usp + -800 - 4096) with (usp + -4896) by lia.
astep. astep. sh_if.
ato 0x51d38.
release_frame P1 ST (usp + -4888). release_frame JK1 ST (usp + -896).
replace (usp + -896 + 32) with (usp + -864) in * by lia.
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact HULL].
Qed.

Lemma sbd_v6 : forall (usp lo S OUT f MODE : Z) (g : nat -> word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_fr g) ->
stk asegs m lo (usp + -896) -> lo <= usp + -896 - 4192 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (jh : list byte),
ms = MS (R_V5 usp (usp + -992) S OUT f MODE gp tp (Z_to_bv 64 RA_sbd_pois4) t0 t1 t2 (Z_to_bv 64 (usp + -960)) (Z_to_bv 64 32) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (usp + -992)) (Z_to_bv 64 (usp + -960)) t3 t4 t5 t6)
F (Z_to_bv 64 sb_e_alloca_poison) fc None m1 (seg_rom asegs)
/\ munch [(usp + -4992, usp + -160)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -992)
/\ rw_cells asegs m1 (usp + -608) (sb_fr (fupds g [(52%nat, Z_to_bv 64 (usp + -896))]))
/\ rw_cells asegs m1 (usp + -992) [CB 96 jh])
(MS (R_V5 usp (usp + -896) S OUT f MODE gp tp (Z_to_bv 64 RA_sbd_pois3) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 96) (Z_to_bv 64 (usp + -896)) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_pois3)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FR ST LO LOS SPH U32 MI.
unfold R_V5, RA_sbd_pois3, RA_sbd_pois4, sb_e_alloca_poison in *. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xb6cd8)) with (Z_to_bv 64 0xb6cd8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -4992, usp + -160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -4992, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold sb_fr in FR. cbn [map seq] in FR.
carve_frame 96%nat ST. rename FR0 into HULL.
carve_frame 3992%nat ST. rename FR0 into JK1.
carve_frame 8%nat ST. rename FR0 into P1.
apply (rw_cells_split_CB asegs _ _ [] 8 _ [] [8]%nat) in P1; [| reflexivity]. cbn [mk_CB_cells app] in P1.
astep. astep. astep.
replace (usp + -896 - 96) with (usp + -992) by lia. rewrite ?Z.mod_small by lia.
rewrite (land_m32_al (usp + -992)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
astep. astep. replace (usp + -896 - 4096) with (usp + -4992) by lia.
astep. astep. sh_if.
ato 0x51d38.
release_frame P1 ST (usp + -4984). release_frame JK1 ST (usp + -992).
replace (usp + -992 + 32) with (usp + -960) in * by lia.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact HULL].
Qed.

Definition RA_sbd_lspq : Z := 0xb6d90.

Lemma sbd_v7 : forall (usp S OUT A f MODE SM id : Z) (g : nat -> word) (s : sbd_state bptr) (pad1 : list byte) (sm : submode)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_fr g) ->
g 42%nat = Z_to_bv 64 (Z.shiftr (S + 144) 3 + SHB) -> g 41%nat = Z_to_bv 64 (Z.shiftr (S + 152) 3 + SHB) -> g 44%nat = Z_to_bv 64 (S + 144) ->
g 43%nat = Z_to_bv 64 (S + 152) -> g 35%nat = Z_to_bv 64 (S + 28) -> g 25%nat = Z_to_bv 64 (usp + -864) -> g 38%nat = Z_to_bv 64 A ->
rw_cells asegs m (S + 136) (sbp_cfg s pad1) -> rw_cells asegs m (S + 152) [C4 (Z_to_bv 64 id)] ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= usp + -992 -> (S + 160 <= SH_LO \/ SH_HI <= S) ->
(sbd_mode s = ModeWB \/ sbd_mode s = ModeUWB) -> MODE = sbmode_struct (sbd_mode s) -> aobj asegs m MODE 216 ->
submode_at (sbm_submodes (sbd_mode s)) id = Some sm -> 0 <= id < 8 -> SM = sb_sub_addr id -> aobj asegs m SM 88 -> lib_consts m ->
SH_HI <= usp + -992 -> usp < 2^63 ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (xa3 : word),
ms = MS (mkR (Z_to_bv 64 RA_sbd_lspq) (Z_to_bv 64 (usp + -992)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -608))
(Z_to_bv 64 (usp + -864)) (Z_to_bv 64 8) (Z_to_bv 64 A) xa3 a4 a5 a6 a7
(Z_to_bv 64 (usp + -864)) (Z_to_bv 64 8) (Z_to_bv 64 (S + 28)) (Z_to_bv 64 (usp + -960)) (Z_to_bv 64 f) (Z_to_bv 64 MODE) (Z_to_bv 64 f)
(Z_to_bv 64 SHB) (Z_to_bv 64 OUT) (Z_to_bv 64 S) t3 t4 t5 t6)
F (Z_to_bv 64 A_lsp_unquant_high) fc None m1 (seg_rom asegs)
/\ munch [(usp + -608, usp + -160)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 (usp + -608) (sb_fr (fupds g [(52%nat, Z_to_bv 64 (usp + -992))])))
(MS (R_V5 usp (usp + -992) S OUT f MODE gp tp (Z_to_bv 64 RA_sbd_pois4) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (usp + -992)) (Z_to_bv 64 (usp + -960)) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_pois4)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FR E42 E41 E44 E43 E35 E25 E38 CFG IDC OBS S8 SPOS SLO SOFF HMO EMODE OBM HSM HID ESM OBSM LC LOS SPH MI.
unfold R_V5, RA_sbd_pois4, RA_sbd_lspq, A_lsp_unquant_high in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xb6d08)) with (Z_to_bv 64 0xb6d08) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(usp + -608, usp + -160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -608, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold sb_fr in FR. cbn [map seq] in FR. rewrite E42, E41, E44, E43, E35, E25, E38 in FR. unfold sbp_cfg in CFG.
assert (ESUB : sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR (sbd_mode s) = MODE + 40).
{ subst MODE. destruct HMO as [-> | ->]; reflexivity. }
rewrite ESUB in CFG.
assert (M8 : MODE mod 8 = 0) by (subst MODE; destruct HMO as [-> | ->]; reflexivity).
assert (MR : 0x10000 <= MODE /\ MODE + 216 <= 0x652000) by (subst MODE; destruct HMO as [-> | ->]; cbn; unfold A_sb_wb_mode, A_sb_uwb_mode; lia).
pose proof (lib_const m A_wb_submode1 LC_wb_submode1 LC ltac:(lc_in)) as T1. pose proof (lib_const m A_wb_submode2 LC_wb_submode2 LC ltac:(lc_in)) as T2.
pose proof (lib_const m A_wb_submode3 LC_wb_submode3 LC ltac:(lc_in)) as T3. pose proof (lib_const m A_wb_submode4 LC_wb_submode4 LC ltac:(lc_in)) as T4.
unfold LC_wb_submode1 in T1. unfold LC_wb_submode2 in T2. unfold LC_wb_submode3 in T3. unfold LC_wb_submode4 in T4.
destruct (sb_submode_cases (sbd_mode s) id sm HMO ltac:(lia) HSM) as [(EMO & [(-> & _) | [(-> & _) | [(-> & _) | (-> & _)]]]) | (EMO & -> & _)];
rewrite EMO in *; cbn [sbmode_struct] in EMODE; cbn [sb_sub_addr Z.eqb Pos.eqb] in ESM.
- pose proof (lib_const m A_sb_wb_mode LC_sb_wb_mode LC ltac:(lc_in)) as TAB. rewrite <- EMODE in TAB. unfold LC_sb_wb_mode in TAB. unfold A_sb_wb_mode in EMODE.
rewrite <- ESM in T1. clear T2 T3 T4. unfold A_wb_submode1 in ESM. assert (SM8 : SM mod 8 = 0) by (rewrite ESM; reflexivity).
ato 0xb6d44. rewrite sx32_small by (unfold int31; lia). ato 0xb6d64. rewrite <- ESM.
ato 0xaee84.
rewrite <- E42, <- E41, <- E44, <- E43, <- E35, <- E25, <- E38 in FR.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact FR].
- pose proof (lib_const m A_sb_wb_mode LC_sb_wb_mode LC ltac:(lc_in)) as TAB. rewrite <- EMODE in TAB. unfold LC_sb_wb_mode in TAB. unfold A_sb_wb_mode in EMODE.
rewrite <- ESM in T2. clear T1 T3 T4. unfold A_wb_submode2 in ESM. assert (SM8 : SM mod 8 = 0) by (rewrite ESM; reflexivity).
ato 0xb6d44. rewrite sx32_small by (unfold int31; lia). ato 0xb6d64. rewrite <- ESM.
ato 0xaee84.
rewrite <- E42, <- E41, <- E44, <- E43, <- E35, <- E25, <- E38 in FR.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact FR].
- pose proof (lib_const m A_sb_wb_mode LC_sb_wb_mode LC ltac:(lc_in)) as TAB. rewrite <- EMODE in TAB. unfold LC_sb_wb_mode in TAB. unfold A_sb_wb_mode in EMODE.
rewrite <- ESM in T3. clear T1 T2 T4. unfold A_wb_submode3 in ESM. assert (SM8 : SM mod 8 = 0) by (rewrite ESM; reflexivity).
ato 0xb6d44. rewrite sx32_small by (unfold int31; lia). ato 0xb6d64. rewrite <- ESM.
ato 0xaee84.
rewrite <- E42, <- E41, <- E44, <- E43, <- E35, <- E25, <- E38 in FR.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact FR].
- pose proof (lib_const m A_sb_wb_mode LC_sb_wb_mode LC ltac:(lc_in)) as TAB. rewrite <- EMODE in TAB. unfold LC_sb_wb_mode in TAB. unfold A_sb_wb_mode in EMODE.
rewrite <- ESM in T4. clear T1 T2 T3. unfold A_wb_submode4 in ESM. assert (SM8 : SM mod 8 = 0) by (rewrite ESM; reflexivity).
ato 0xb6d44. rewrite sx32_small by (unfold int31; lia). ato 0xb6d64. rewrite <- ESM.
ato 0xaee84.
rewrite <- E42, <- E41, <- E44, <- E43, <- E35, <- E25, <- E38 in FR.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact FR].
- pose proof (lib_const m A_sb_uwb_mode LC_sb_uwb_mode LC ltac:(lc_in)) as TAB. rewrite <- EMODE in TAB. unfold LC_sb_uwb_mode in TAB. unfold A_sb_uwb_mode in EMODE.
rewrite <- ESM in T1. clear T2 T3 T4. unfold A_wb_submode1 in ESM. assert (SM8 : SM mod 8 = 0) by (rewrite ESM; reflexivity).
ato 0xb6d44. rewrite sx32_small by (unfold int31; lia). ato 0xb6d64. rewrite <- ESM.
ato 0xaee84.
rewrite <- E42, <- E41, <- E44, <- E43, <- E35, <- E25, <- E38 in FR.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact FR].
Qed.

Definition RA_sbd_pois5 : Z := 0xb6ee4.

Lemma sbd_v8 : forall (usp lo S OUT f MODE Q OQ : Z) (g : nat -> word) (s : sbd_state bptr) (a : sb_addrs) (lq voq : list word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_fr g) -> g 47%nat = Z_to_bv 64 (Z.shiftr (S + 32) 3 + SHB) -> g 40%nat = Z_to_bv 64 (S + 32) ->
rw_cells asegs m S (sbp_hdr s a) -> rw_cells asegs m (S + 36) [C4 (Z_to_bv 64 (sbd_first s))] -> rw_cells asegs m (S + 40) (sbp_ptrs s a OUT) ->
sbd_lpcSize s = 8 -> (sbd_first s = 0 \/ sbd_first s = 1) -> OQ = a_oq a ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= lo -> (S + 160 <= SH_LO \/ SH_HI <= S) ->
Q = usp + -864 -> rw_cells asegs m Q (f32 lq) -> length lq = 8%nat -> aobj asegs m Q 32 ->
rw_cells asegs m OQ (f32 voq) -> length voq = 8%nat -> aobj asegs m OQ 32 -> OQ mod 8 = 0 -> 0 < OQ -> OQ + 32 <= lo -> (OQ + 32 <= SH_LO \/ SH_HI <= OQ) ->
(S + 160 <= OQ \/ OQ + 32 <= S) ->
stk asegs m lo (usp + -992) -> lo <= usp + -992 - 4192 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms => exists (m1 : mem) (xt0 xa2 xa3 xa4 xa5 xa7 : word) (F' : bvmap 5 word) (jh : list byte) (voq' : list word),
ms = MS (mkR (Z_to_bv 64 RA_sbd_pois5) (Z_to_bv 64 (usp + -1088)) gp tp xt0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -608))
(Z_to_bv 64 (usp + -1056)) (Z_to_bv 64 32) xa2 xa3 xa4 xa5 a6 xa7
(Z_to_bv 64 (usp + -1088)) (Z_to_bv 64 8) (Z_to_bv 64 (S + 28)) (Z_to_bv 64 (usp + -960)) (Z_to_bv 64 f) (Z_to_bv 64 MODE) (Z_to_bv 64 f)
(Z_to_bv 64 SHB) (Z_to_bv 64 OUT) (Z_to_bv 64 S) t3 t4 t5 t6)
F' (Z_to_bv 64 sb_e_alloca_poison) fc None m1 (seg_rom asegs)
/\ munch [(OQ, OQ + 32); (usp + -5088, usp + -160)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -1088)
/\ rw_cells asegs m1 (usp + -608)
(sb_fr (fupds g [(4%nat, Z_to_bv 64 (Z.shiftr (S + 36) 3 + SHB)); (30%nat, Z_to_bv 64 (S + 80)); (5%nat, Z_to_bv 64 (S + 36)); (39%nat, Z_to_bv 64 (usp + -1056))]))
/\ rw_cells asegs m1 (usp + -1088) [CB 96 jh]
/\ rw_cells asegs m1 OQ (f32 voq') /\ length voq' = 8%nat)
(MS (mkR (Z_to_bv 64 RA_sbd_lspq) (Z_to_bv 64 (usp + -992)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -608))
a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 Q) (Z_to_bv 64 8) (Z_to_bv 64 (S + 28)) (Z_to_bv 64 (usp + -960)) (Z_to_bv 64 f) (Z_to_bv 64 MODE) (Z_to_bv 64 f)
(Z_to_bv 64 SHB) (Z_to_bv 64 OUT) (Z_to_bv 64 S) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_lspq)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FR E47 E40 HD FST PT ELPC HFST EOQ OBS S8 SPOS SLO SOFF EQ QC LQ OBQ OQC LOQ OBOQ OQ8 OQPOS OQLO OQOFF SOQ ST LO LOS SPH U32 MI FRM.
unfold RA_sbd_lspq, RA_sbd_pois5, sb_e_alloca_poison in *. unfold SH_LO, SH_HI in SOFF, OQOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xb6d90)) with (Z_to_bv 64 0xb6d90) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(OQ, OQ + 32); (usp + -5088, usp + -160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(OQ, OQ + 32); (usp + -5088, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; lia).
assert (Q8 : Q mod 8 = 0) by (subst Q; clear - U32; Z.div_mod_to_equations; lia).
unfold sb_fr in FR. cbn [map seq] in FR. rewrite E47, E40 in FR. unfold sbp_hdr in HD. rewrite ELPC in HD. unfold sbp_ptrs in PT. rewrite <- EOQ in PT.
do 8 (destruct lq as [|? lq]; [discriminate LQ|]). destruct lq; [| discriminate LQ]. cbn [f32 map] in QC.
do 8 (destruct voq as [|? voq]; [discriminate LOQ|]). destruct voq; [| discriminate LOQ]. cbn [f32 map] in OQC.
carve_frame 96%nat ST. rename FR0 into HULL.
carve_frame 3992%nat ST. rename FR0 into JK1.
carve_frame 8%nat ST. rename FR0 into P1.
apply (rw_cells_split_CB asegs _ _ [] 8 _ [] [8]%nat) in P1; [| reflexivity]. cbn [mk_CB_cells app] in P1.
ato 0xb6db0.
destruct HFST as [E0|E0]; rewrite E0 in *; rewrite sx32_small by (unfold int31; lia).
2: { ato 0xb6dd0. rewrite sx32_small by (unfold int31; lia). ato 0xb6dfc.
ato 0xb6e64.
ato 0xb6e84. rewrite zx32_small by lia. ato 0xb6ebc. alits.
astep. astep.
replace (usp + -992 - 96) with (usp + -1088) by lia. rewrite ?Z.mod_small by lia.
rewrite (land_m32_al (usp + -1088)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
astep. astep. replace (usp + -992 - 4096) with (usp + -5088) by lia.
astep. astep. sh_if.
ato 0x51d38.
release_frame P1 ST (usp + -5080). release_frame JK1 ST (usp + -1088).
replace (usp + -1088 + 32) with (usp + -1056) in * by lia.
rewrite <- E47, <- E40 in FR.
apply evt_done. lazymatch type of OQC with rw_cells _ _ _ [C4 ?w0; C4 ?w1; C4 ?w2; C4 ?w3; C4 ?w4; C4 ?w5; C4 ?w6; C4 ?w7] => do 9 eexists; exists [w0; w1; w2; w3; w4; w5; w6; w7] end. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|]. split; [exact HULL|]. split; [exact OQC| reflexivity].
}
ato 0xb6e64.
ato 0xb6e84. rewrite zx32_small by lia. ato 0xb6ebc. alits.
astep. astep.
replace (usp + -992 - 96) with (usp + -1088) by lia. rewrite ?Z.mod_small by lia.
rewrite (land_m32_al (usp + -1088)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
astep. astep. replace (usp + -992 - 4096) with (usp + -5088) by lia.
astep. astep. sh_if.
ato 0x51d38.
release_frame P1 ST (usp + -5080). release_frame JK1 ST (usp + -1088).
replace (usp + -1088 + 32) with (usp + -1056) in * by lia.
rewrite <- E47, <- E40 in FR.
apply evt_done. lazymatch type of OQC with rw_cells _ _ _ [C4 ?w0; C4 ?w1; C4 ?w2; C4 ?w3; C4 ?w4; C4 ?w5; C4 ?w6; C4 ?w7] => do 9 eexists; exists [w0; w1; w2; w3; w4; w5; w6; w7] end. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|]. split; [exact HULL|]. split; [exact OQC| reflexivity].
Qed.

Definition sb_v9_upd (usp S OUT f MODE fsz : Z) : list (nat * word) :=
[(52%nat, Z_to_bv 64 (usp + -1088)); (7%nat, Z_to_bv 64 f); (8%nat, Z_to_bv 64 f); (20%nat, Z_to_bv 64 (usp + -960)); (37%nat, Z_to_bv 64 0);
(34%nat, Z_to_bv 64 (S + 120)); (19%nat, Z_to_bv 64 (S + 104)); (23%nat, Z_to_bv 64 (S + 132)); (46%nat, Z_to_bv 64 (S + 72)); (29%nat, Z_to_bv 64 (S + 88));
(17%nat, Z_to_bv 64 (S + 112)); (9%nat, Z_to_bv 64 (OUT + 4 * fsz + 4)); (12%nat, Z_to_bv 64 (usp + -1052)); (2%nat, Z_to_bv 64 7);
(11%nat, Z_to_bv 64 (sha (usp + -1052))); (3%nat, Z_to_bv 64 3); (28%nat, Z_to_bv 64 (2^36 - 16)); (22%nat, Z_to_bv 64 OUT); (21%nat, Z_to_bv 64 S);
(18%nat, Z_to_bv 64 (S + 96)); (16%nat, Z_to_bv 64 (MODE + 32))].
Lemma sbd_v9 : forall (usp S OUT f MODE fsz : Z) (g : nat -> word) (s : sbd_state bptr) (a : sb_addrs)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_fr g) -> g 36%nat = Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB) -> g 39%nat = Z_to_bv 64 (usp + -1056) ->
g 10%nat = Z_to_bv 64 (OUT + 4 * fsz) -> g 26%nat = Z_to_bv 64 (S + 20) ->
rw_cells asegs m S (sbp_hdr s a) -> sbd_nbSubframes s = 4 ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= usp + -1088 -> (S + 160 <= SH_LO \/ SH_HI <= S) ->
0 <= OUT -> 0 <= fsz <= 320 -> OUT + 8000 < 2^63 -> SH_HI <= usp + -1088 -> usp < 2^63 ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (k : sb_rjunk) (F' : bvmap 5 word),
ms = MS (R_LA usp S OUT MODE 0 gp tp k) F' (Z_to_bv 64 SB_LA_PC) fc None m1 (seg_rom asegs)
/\ munch [(usp + -608, usp + -160)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 (usp + -608) (sb_fr (fupds g (sb_v9_upd usp S OUT f MODE fsz))))
(MS (mkR (Z_to_bv 64 RA_sbd_pois5) (Z_to_bv 64 (usp + -1088)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -608))
a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (usp + -1088)) (Z_to_bv 64 8) (Z_to_bv 64 (S + 28)) (Z_to_bv 64 (usp + -960)) (Z_to_bv 64 f) (Z_to_bv 64 MODE) (Z_to_bv 64 f)
(Z_to_bv 64 SHB) (Z_to_bv 64 OUT) (Z_to_bv 64 S) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_pois5)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FR E36 E39 E10 E26 HD ENS OBS S8 SPOS SLO SOFF O0 FSZ O1 LOS SPH MI.
unfold RA_sbd_pois5, SB_LA_PC in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xb6ee4)) with (Z_to_bv 64 0xb6ee4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(usp + -608, usp + -160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -608, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold sb_fr in FR. cbn [map seq] in FR. rewrite E36, E39, E10, E26 in FR. unfold sbp_hdr in HD. rewrite ENS in HD.
ato 0xb6f04. rewrite sx32_small by (unfold int31; lia).
ato 0xb6fd0.
assert (L20 : Z.land (S + 20) 7 = 4) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; clear - S8; Z.div_mod_to_equations; lia).
assert (L24 : Z.land (S + 24) 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; clear - S8; Z.div_mod_to_equations; lia).
rewrite L20, L24 in FR. change (4 + 3) with 7 in FR. change (0 + 3) with 3 in FR.
replace (SHB + (usp + -1052) ≫ 3) with (sha (usp + -1052)) in FR by (unfold sha; lia).
rewrite <- E36, <- E39, <- E10, <- E26 in FR.
apply evt_done. eexists. eexists (SBRJ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _). eexists. split; [unfold R_LA, sha; cbn [j_ra j_t0 j_t1 j_t2 j_a0 j_a1 j_a2 j_a3 j_a4 j_a5 j_a6 j_a7 j_s2 j_s3 j_s4 j_s5 j_s6 j_s7 j_s8 j_s11 j_t3 j_t4 j_t5 j_t6]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. unfold sb_v9_upd. exact FR.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Definition sb_A_qmf_synth : Z := 0xa4b58.
Definition sb_A_H0 : Z := 0x27000.
Definition RA_sbd_qmf_t : Z := 0xb7dfc.

Lemma sbd_t1 : forall (usp lo S OUT A f sf MODE fsz : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs) (le : word) (k : sb_rjunk)
(gp tp : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_slots usp S OUT A f sf MODE fsz v) ->
rw_cells asegs m S (sbp_hdr s a) -> rw_cells asegs m (S + 40) (sbp_ptrs s a OUT) -> rw_cells asegs m (S + 128) [C4 le] ->
sbd_frame_size s = fsz -> sbd_full_frame_size s = 2 * fsz -> (fsz = 160 \/ fsz = 320) ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= lo -> (S + 160 <= SH_LO \/ SH_HI <= S) -> IMG_TOP <= S ->
0 <= OUT -> OUT + 8000 < 2^63 ->
stk asegs m lo (usp + -1088) -> lo <= usp + -1088 - 16 -> SH_HI <= lo -> usp < 2^63 ->
mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms => exists (m1 : mem) (xt0 xt1 xt2 xt3 xt4 xt5 xt6 : word) (xs3 xs4 xs5 xs7 : word) (F' : bvmap 5 word) (fc' : bv 32) (le' : word) (ja : list byte),
ms = MS (mkR (Z_to_bv 64 RA_sbd_qmf_t) (Z_to_bv 64 (usp + -1104)) gp tp xt0 xt1 xt2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -608))
(Z_to_bv 64 OUT) (Z_to_bv 64 (OUT + 4 * fsz)) (Z_to_bv 64 sb_A_H0) (Z_to_bv 64 OUT) (Z_to_bv 64 (2 * fsz)) (Z_to_bv 64 64)
(Z_to_bv 64 (a_g0 a)) (Z_to_bv 64 (a_g1 a))
(Z_to_bv 64 (usp + -864)) xs3 xs4 xs5 (Z_to_bv 64 f) xs7 (Z_to_bv 64 f) (Z_to_bv 64 SHB) (Z_to_bv 64 OUT) (Z_to_bv 64 S) xt3 xt4 xt5 xt6)
F' (Z_to_bv 64 sb_A_qmf_synth) fc' None m1 (seg_rom asegs)
/\ munch [(S + 128, S + 132); (usp + -1104, usp + -1088)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -1104)
/\ frm0 fc' /\ rw_cells asegs m1 (S + 128) [C4 le'] /\ rw_cells asegs m1 (usp + -1104) [C8 (Z_to_bv 64 0); CB 8 ja])
(MS (R_TA usp S OUT gp tp k) F (Z_to_bv 64 SB_TA_PC) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL HD PT LE EFS EFFS HFS OBS S8 SPOS SLO SOFF SIMG O0 O1 ST LO LOS SPH MI FRM.
unfold R_TA, SB_TA_PC, RA_sbd_qmf_t, sb_A_qmf_synth, sb_A_H0 in *. unfold SH_LO, SH_HI in SOFF. unfold IMG_TOP in SIMG. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(S + 128, S + 132); (usp + -1104, usp + -1088)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(S + 128, S + 132); (usp + -1104, usp + -1088)]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold sb_slots, sha in SL. unfold sbp_hdr in HD. rewrite EFS, EFFS in HD. unfold sbp_ptrs in PT.
carve_frame 16%nat ST. rename FR into ARG.
apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in ARG; [| reflexivity]. cbn [mk_CB_cells app] in ARG.
ato 0xb7d98.
rewrite sx32_small by (unfold int31; lia).
ato 0xb7dd0. rewrite sx32_small by (unfold int31; lia).
ato 0xa4b58.
replace (OUT + fsz ≪ 2) with (OUT + 4 * fsz) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
apply evt_done. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [assumption|]. split; [exact LE| exact ARG].
Qed.

Definition RA_sbd_unpoison_t : Z := 0xb7ec8.

Lemma sbd_t2 : forall (usp lo S OUT A f sf MODE fsz Q OQ : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs) (fst0 : word) (lq voq : list word) (ja : list byte)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_slots usp S OUT A f sf MODE fsz v) ->
rw_cells asegs m S (sbp_hdr s a) -> rw_cells asegs m (S + 36) [C4 fst0] -> rw_cells asegs m (S + 40) (sbp_ptrs s a OUT) ->
sbd_lpcSize s = 8 -> OQ = a_oq a ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= lo -> (S + 160 <= SH_LO \/ SH_HI <= S) ->
Q = usp + -864 -> rw_cells asegs m Q (f32 lq) -> length lq = 8%nat -> aobj asegs m Q 32 ->
rw_cells asegs m OQ (f32 voq) -> length voq = 8%nat -> aobj asegs m OQ 32 -> OQ mod 8 = 0 -> 0 < OQ -> OQ + 32 <= lo -> (OQ + 32 <= SH_LO \/ SH_HI <= OQ) ->
(S + 160 <= OQ \/ OQ + 32 <= S) ->
rw_cells asegs m (usp + -1104) [C8 (Z_to_bv 64 0); CB 8 ja] ->
stk asegs m lo (usp + -1104) -> lo <= usp + -1104 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms => exists (m1 : mem) (xa2 xa3 xa4 xa5 : word) (F' : bvmap 5 word) (voq' : list word),
ms = MS (mkR (Z_to_bv 64 RA_sbd_unpoison_t) (Z_to_bv 64 (usp + -1088)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -608))
(v_416 v) (Z_to_bv 64 (usp + -608)) xa2 xa3 xa4 xa5 (Z_to_bv 64 (S + 36)) a7
(Z_to_bv 64 (usp + -608)) s3 s4 s5 (Z_to_bv 64 f) s7 (Z_to_bv 64 f) (Z_to_bv 64 SHB) (Z_to_bv 64 OUT) (Z_to_bv 64 S) t3 t4 t5 t6)
F' (Z_to_bv 64 sb_e_allocas_unpoison) fc None m1 (seg_rom asegs)
/\ munch [(S + 36, S + 40); (OQ, OQ + 32)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -1088)
/\ rw_cells asegs m1 (S + 36) [C4 (Z_to_bv 64 0)] /\ rw_cells asegs m1 OQ (f32 voq') /\ length voq' = 8%nat)
(MS (mkR (Z_to_bv 64 RA_sbd_qmf_t) (Z_to_bv 64 (usp + -1104)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -608))
a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 Q) s3 s4 s5 (Z_to_bv 64 f) s7 (Z_to_bv 64 f) (Z_to_bv 64 SHB) (Z_to_bv 64 OUT) (Z_to_bv 64 S) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_qmf_t)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL HD FST PT ELPC EOQ OBS S8 SPOS SLO SOFF EQ QC LQ OBQ OQC LOQ OBOQ OQ8 OQPOS OQLO OQOFF SOQ ARG ST LO LOS SPH U32 MI FRM.
unfold RA_sbd_qmf_t, RA_sbd_unpoison_t, sb_e_allocas_unpoison in *. unfold SH_LO, SH_HI in SOFF, OQOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xb7dfc)) with (Z_to_bv 64 0xb7dfc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(S + 36, S + 40); (OQ, OQ + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(S + 36, S + 40); (OQ, OQ + 32)]) by (cbn; unfold SH_LO, SH_HI; lia).
assert (Q8 : Q mod 8 = 0) by (subst Q; clear - U32; Z.div_mod_to_equations; lia).
unfold sb_slots, sha in SL. unfold sbp_hdr in HD. rewrite ELPC in HD. unfold sbp_ptrs in PT. rewrite <- EOQ in PT.
do 8 (destruct lq as [|? lq]; [discriminate LQ|]). destruct lq; [| discriminate LQ]. cbn [f32 map] in QC.
do 8 (destruct voq as [|? voq]; [discriminate LOQ|]). destruct voq; [| discriminate LOQ]. cbn [f32 map] in OQC.
astep. replace (usp + -1104 + 16) with (usp + -1088) by lia.
release_frame ARG ST (usp + -1088).
ato 0xb7e14. rewrite sx32_small by (unfold int31; lia).
ato 0x51e64.
apply evt_done. lazymatch type of OQC with rw_cells _ _ _ [C4 ?w0; C4 ?w1; C4 ?w2; C4 ?w3; C4 ?w4; C4 ?w5; C4 ?w6; C4 ?w7] => do 6 eexists; exists [w0; w1; w2; w3; w4; w5; w6; w7] end.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FST|]. split; [exact OQC| reflexivity].
Qed.

Lemma sbd_t3 : forall (usp lo f : Z) (jh : list byte)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -1088) [CB 480 jh] ->
stk asegs m lo (usp + -1088) -> lo <= usp + -1088 -> usp < 2^63 ->
mem_inv asegs m ->
evt asegs (fun ms =>
ms = MS (mkR (Z_to_bv 64 RA_sbd_unpoison_t) (Z_to_bv 64 (usp + -608)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -608))
a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (usp + -608)) s3 (Z_to_bv 64 0) s5 (Z_to_bv 64 f) s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xb7ed0) fc None m (seg_rom asegs)
/\ stk asegs m lo (usp + -608))
(MS (mkR (Z_to_bv 64 RA_sbd_unpoison_t) (Z_to_bv 64 (usp + -1088)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -608))
a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (usp + -608)) s3 s4 s5 (Z_to_bv 64 f) s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_unpoison_t)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros HULLS ST LO SPH MI.
unfold RA_sbd_unpoison_t in *.
replace (ret_pc (Z_to_bv 64 0xb7ec8)) with (Z_to_bv 64 0xb7ec8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof ST as (STa & STb & _).
astep. release_frame HULLS ST (usp + -608).
ato 0xb7ed0.
apply evt_done. split; [reflexivity| exact ST].
Qed.

Definition sb_e_asan_memset : Z := 0x667b0.
Definition RA_sbd_memset_n : Z := 0xb7d2c.

Lemma sbd_n1 : forall (usp S OUT f MODE : Z) (s : sbd_state bptr) (a : sb_addrs)
(gp tp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m S (sbp_hdr s a) -> rw_cells asegs m (S + 40) (sbp_ptrs s a OUT) ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 < 2^63 ->
0 < OUT -> OUT + 8000 < 2^63 -> match sbd_innov_save s with None => True | Some k => 0 <= k <= 2000 end -> 0 <= sbd_full_frame_size s <= 640 ->
mem_inv asegs m ->
evt asegs (fun ms =>
match sbd_innov_save s with
| None => exists (xa0 xa1 : word), ms = MS (R_P usp S OUT f MODE gp tp ra t0 t1 t2 xa0 xa1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6) F (Z_to_bv 64 0xb7d2c) fc None m (seg_rom asegs)
| Some k => ms = MS (R_P usp S OUT f MODE gp tp (Z_to_bv 64 RA_sbd_memset_n) t0 t1 t2 (Z_to_bv 64 (OUT + 4 * k)) (Z_to_bv 64 0)
(Z_to_bv 64 (4 * sbd_full_frame_size s)) a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6) F (Z_to_bv 64 sb_e_asan_memset) fc None m (seg_rom asegs)
end)
(MS (R_P usp S OUT f MODE gp tp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6) F (Z_to_bv 64 0xb7cec) fc None m (seg_rom asegs)).
Proof.
intros until m. intros HD PT OBS S8 SPOS SHI O0 O1 HK FFS MI.
unfold R_P, RA_sbd_memset_n, sb_e_asan_memset in *.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM. assert (OF : offsh []) by exact I.
unfold sbp_hdr in HD. unfold sbp_ptrs, sb_isave_ptr in PT.
destruct (sbd_innov_save s) as [k|].
- ato 0xb7d04. astep. sh_if.
ato 0xb7d20. rewrite sx32_small by (unfold int31; lia).
ato 0x667b0.
replace (sbd_full_frame_size s ≪ 2) with (4 * sbd_full_frame_size s) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
apply evt_done. reflexivity.
- ato 0xb7d2c. apply evt_done. do 2 eexists. reflexivity.
Qed.

Definition RA_sbd_lost : Z := 0xb7d48.

Lemma sbd_n2 : forall (usp S OUT f MODE dtx : Z) (g : nat -> word) (stk8 : word) (j24 j36 : list byte)
(gp tp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_fr g) -> g 45%nat = stk8 ->
rw_cells asegs m f (sb_fhdr j24 (Z_to_bv 64 dtx) j36) -> (dtx = 0 \/ dtx = 1) -> 0 < f -> f + 64 < 2^63 ->
mem_inv asegs m ->
evt asegs (fun ms =>
(dtx = 0 /\ exists xa0 : word, ms = MS (R_P usp S OUT f MODE gp tp ra t0 t1 t2 xa0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (f + 32)) s4 t3 t4 t5 t6)
F (Z_to_bv 64 0xb7fa8) fc None m (seg_rom asegs))
\/ (dtx = 1 /\ ms = MS (R_P usp S OUT f MODE gp tp (Z_to_bv 64 RA_sbd_lost) t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 OUT) (Z_to_bv 64 1) stk8 a4 a5 a6 a7
(Z_to_bv 64 (f + 32)) s4 t3 t4 t5 t6) F (Z_to_bv 64 A_sb_decode_lost) fc None m (seg_rom asegs)))
(MS (R_P usp S OUT f MODE gp tp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (f + 32)) s4 t3 t4 t5 t6) F (Z_to_bv 64 0xb7d2c) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FR E45 FRB HD F0 F1 MI.
unfold R_P, RA_sbd_lost, A_sb_decode_lost in *.
unfold sb_fr in FR. cbn [map seq] in FR. rewrite E45 in FR. unfold sb_fhdr in FRB.
destruct HD as [-> | ->].
- ato 0xb7fa8. apply evt_done. left. split; [reflexivity|]. eexists. reflexivity.
- ato 0xb85b8. apply evt_done. right. split; reflexivity.
Qed.

Lemma sbd_n3 : forall (usp S OUT f MODE : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word) F fc (m : mem),
evt asegs (fun ms => ms = MS (R_P usp S OUT f MODE gp tp (Z_to_bv 64 RA_sbd_lost) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 (Z_to_bv 64 0) t3 t4 t5 t6)
F (Z_to_bv 64 0xb7ed0) fc None m (seg_rom asegs))
(MS (R_P usp S OUT f MODE gp tp (Z_to_bv 64 RA_sbd_lost) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_lost)) fc None m (seg_rom asegs)).
Proof.
intros until m. unfold R_P, RA_sbd_lost.
replace (ret_pc (Z_to_bv 64 0xb7d48)) with (Z_to_bv 64 0xb7d48) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0xb7ed0. apply evt_done. reflexivity.
Qed.

Lemma sb_f32_snoc l x : f32 l ++ [C4 x] = f32 (l ++ [x]).
Proof. rewrite f32_app, f32_cons, f32_nil. reflexivity. Qed.
Section SIL.
Variables (Y NW : Z).
Variables rav spv gp tp t0v t1v t2v s0v s1v a3v a7v s2v s3v s4v s5v s6v s7v s8v s10v s11v t3v t4v t5v t6v : word.
Hypothesis Y4 : Y mod 4 = 0.
Hypothesis YI : IMG_TOP <= Y.
Definition RSIL (ya cnt : Z) (a5v a6v : word) : bvmap 5 word :=
mkR rav spv gp tp t0v t1v t2v s0v s1v (Z_to_bv 64 ya) (Z_to_bv 64 ya) (Z_to_bv 64 0x26901d7d) a3v (Z_to_bv 64 cnt) a5v a6v a7v
s2v s3v s4v s5v s6v s7v s8v (Z_to_bv 64 SHB) s10v s11v t3v t4v t5v t6v.
Definition sil_post (F : bvmap 5 word) (fc : bv 32) (mI : mem) : machine_state -> Prop :=
fun ms' => exists a5' a6' m' (ys' : list word),
ms' = MS (RSIL (Y + 4 * NW) 0 a5' a6') F (Z_to_bv 64 0xb7ffc) fc None m' (seg_rom asegs)
/\ munch [(Y, Y + 4 * NW)] mI m' /\ wmono asegs mI m' /\ mem_inv asegs m'
/\ Z.of_nat (length ys') = NW /\ rw_cells asegs m' Y (f32 ys').
Lemma sb_silence_loop : forall (mI : mem) (rest done : list word) (cw : word) (i ya cnt : Z) (a5v a6v : word) F fc mc,
ya = Y + 4 * i -> cnt = 1 + Z.of_nat (length rest) -> i = Z.of_nat (length done) -> i + 1 + Z.of_nat (length rest) = NW -> NW < 2^31 ->
aobj asegs mI Y (4 * NW) -> offsh [(Y, Y + 4 * NW)] ->
mem_inv asegs mc -> munch [(Y, Y + 4 * NW)] mI mc -> wmono asegs mI mc ->
rw_cells asegs mc Y (f32 done) -> rw_cells asegs mc (Y + 4 * i) (f32 (cw :: rest)) ->
evt asegs (sil_post F fc mI) (MS (RSIL ya cnt a5v a6v) F (Z_to_bv 64 0xb7fd8) fc None mc (seg_rom asegs)).
Proof using Y4 YI.
intros mI rest.
induction rest as [|cw' rest IH]; intros done cw i ya cnt a5v a6v F fc mc -> -> Hi HN HNW OBY OF MI MU WM XD XC;
pose proof OBY as (OY0 & OY1 & _); unfold APP_TOP in *; pose proof YI as YI'; unfold IMG_TOP in YI';
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
unfold RSIL; rewrite !f32_cons in XC; cbn [length] in *.
- rewrite f32_nil in XC.
ato 0xb7fe4. astep. chk_merge OBY 4.
ato 0xb7ff8. astep. sh_if.
chunk_snoc XD XC. rewrite sb_f32_snoc in XD.
replace (Y + 4 * i + 4) with (Y + 4 * NW) by lia.
replace (1 + Z.of_nat 0 + -1) with 0 by lia.
unfold sil_post, RSIL. finish; [ | exact XD ]. rewrite length_app; cbn [length]; lia.
- ato 0xb7fe4. astep. chk_merge OBY 4.
ato 0xb7ff8. astep. sh_if.
(let X1c := fresh "X1c" in chunk_uncons XC as X1c; chunk_snoc XD X1c). rewrite sb_f32_snoc in XD. rewrite <- ?f32_cons in XC.
replace (Y + 4 * i + 4) with (Y + 4 * (i + 1)) in * by lia.
replace (1 + Z.of_nat (S (length rest)) + -1) with (1 + Z.of_nat (length rest)) by lia.
eapply (IH _ cw' (i + 1)); try eassumption; try reflexivity;
try (rewrite length_app; cbn [length] in *; lia); try (cbn [length] in *; lia).
Qed.
End SIL.

Definition sb_A_iir_mem16 : Z := 0xa3860.
Definition RA_sbd_iir_n : Z := 0xb8088.

Lemma sbd_n4 : forall (usp S OUT f MODE fsz Y : Z) (g : nat -> word) (stk8 fst0 : word) (s : sbd_state bptr) (a : sb_addrs) (cw : word) (rest : list word)
(gp tp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_fr g) -> g 27%nat = Z_to_bv 64 (Z.shiftr (S + 20) 3 + SHB) -> g 26%nat = Z_to_bv 64 (S + 20) -> g 45%nat = stk8 ->
rw_cells asegs m S (sbp_hdr s a) -> rw_cells asegs m (S + 36) [C4 fst0] -> rw_cells asegs m (S + 40) (sbp_ptrs s a OUT) ->
sbd_frame_size s = fsz -> sbd_lpcSize s = 8 -> 1 <= fsz <= 320 -> Z.of_nat (length rest) + 1 = fsz ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= usp + -608 -> (S + 160 <= SH_LO \/ SH_HI <= S) -> IMG_TOP <= S ->
Y = OUT + 4 * fsz -> rw_cells asegs m Y (f32 (cw :: rest)) -> aobj asegs m Y (4 * fsz) -> Y mod 4 = 0 -> IMG_TOP <= Y -> (Y + 4 * fsz <= SH_LO \/ SH_HI <= Y) ->
(S + 160 <= Y \/ Y + 4 * fsz <= S) -> Y + 4 * fsz <= usp + -608 ->
SH_HI <= usp + -608 -> usp < 2^63 ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (xa7 : word) (ys' : list word),
ms = MS (R_P usp S OUT f MODE gp tp (Z_to_bv 64 RA_sbd_iir_n) t0 t1 t2 (Z_to_bv 64 Y) (Z_to_bv 64 (a_iq a)) (Z_to_bv 64 Y) (Z_to_bv 64 fsz) (Z_to_bv 64 8)
(Z_to_bv 64 (a_msp a)) stk8 xa7 s3 s4 t3 t4 t5 t6)
F (Z_to_bv 64 sb_A_iir_mem16) fc None m1 (seg_rom asegs)
/\ munch [(S + 36, S + 40); (Y, Y + 4 * fsz)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 (S + 36) [C4 (Z_to_bv 64 1)] /\ rw_cells asegs m1 Y (f32 ys') /\ Z.of_nat (length ys') = fsz)
(MS (R_P usp S OUT f MODE gp tp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6) F (Z_to_bv 64 0xb7fa8) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FR E27 E26 E45 HD FST PT EFS ELPC HFS LR OBS S8 SPOS SLO SOFF SIMG EY YC OBY Y4 YI YOFF SY YLO LOS SPH MI.
unfold R_P, RA_sbd_iir_n, sb_A_iir_mem16 in *. unfold SH_LO, SH_HI in SOFF, YOFF. unfold IMG_TOP in SIMG. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof OBY as (OY0 & OY1 & _). unfold APP_TOP in OY1.
pose proof (munch_refl [(S + 36, S + 40); (Y, Y + 4 * fsz)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(S + 36, S + 40); (Y, Y + 4 * fsz)]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold sb_fr in FR. cbn [map seq] in FR. rewrite E27, E26, E45 in FR. unfold sbp_hdr in HD. rewrite EFS, ELPC in HD. unfold sbp_ptrs in PT.
ato 0xb7fbc. rewrite sx32_small by (unfold int31; lia). astep. sh_if.
ato 0xb7fd8.
replace (OUT + fsz ≪ 2) with Y by (rewrite Z.shiftl_mul_pow2 by lia; lia).
pose proof (aobj_munch asegs _ m _ Y (4 * fsz) OBY MU (shfree_of_aobj asegs _ m Y (4 * fsz) OF OBY)) as OBYc.
lazymatch type of MU with munch _ _ ?mc =>
pose proof (munch_refl [(Y, Y + 4 * fsz)] mc) as MU0; pose proof (wmono_refl asegs mc) as WM0;
assert (OF0 : offsh [(Y, Y + 4 * fsz)]) by (cbn; unfold SH_LO, SH_HI; lia);
assert (XD0 : rw_cells asegs mc Y (f32 [])) by (apply rw_cells_nil; lia);
call (sb_silence_loop Y fsz _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Y4 YI mc rest [] cw 0 Y fsz _ _ _ _ mc ltac:(lia) ltac:(lia) eq_refl ltac:(cbn [length]; lia) ltac:(lia) OBYc OF0)
end.
all: try eassumption.
{ replace (Y + 4 * 0) with Y by lia. exact YC. }
clear MU0 WM0 OF0. unfold RSIL.
ato 0xb8074. rewrite ?sx32_small by (unfold int31; lia).
ato 0xa3860.
replace (OUT + fsz ≪ 2) with Y by (rewrite Z.shiftl_mul_pow2 by lia; lia).
apply evt_done. lazymatch type of POST with rw_cells _ _ _ (f32 ?l) => eexists; eexists; exists l end. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FST|]. split; [exact POST| exact PC].
Qed.

Definition RA_sbd_qmf_n : Z := 0xb810c.

Lemma sbd_n4b : forall (usp lo S OUT f MODE fsz : Z) (g : nat -> word) (stk8 : word) (s : sbd_state bptr) (a : sb_addrs)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_fr g) -> g 27%nat = Z_to_bv 64 (Z.shiftr (S + 20) 3 + SHB) -> g 45%nat = stk8 ->
rw_cells asegs m S (sbp_hdr s a) -> rw_cells asegs m (S + 40) (sbp_ptrs s a OUT) ->
sbd_frame_size s = fsz -> sbd_full_frame_size s = 2 * fsz -> 1 <= fsz <= 320 ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= lo -> (S + 160 <= SH_LO \/ SH_HI <= S) ->
0 <= OUT -> OUT + 8000 < 2^63 ->
stk asegs m lo (usp + -608) -> lo <= usp + -608 - 16 -> SH_HI <= lo -> usp < 2^63 ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (ja : list byte),
ms = MS (mkR (Z_to_bv 64 RA_sbd_qmf_n) (Z_to_bv 64 (usp + -624)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -608))
(Z_to_bv 64 OUT) (Z_to_bv 64 (OUT + 4 * fsz)) (Z_to_bv 64 sb_A_H0) (Z_to_bv 64 OUT) (Z_to_bv 64 (2 * fsz)) (Z_to_bv 64 64)
(Z_to_bv 64 (a_g0 a)) (Z_to_bv 64 (a_g1 a))
(Z_to_bv 64 (S + 8)) s3 s4 (Z_to_bv 64 (Z.shiftr (S + 8) 3 + SHB)) (Z_to_bv 64 f) (Z_to_bv 64 MODE) (Z_to_bv 64 f)
(Z_to_bv 64 SHB) (Z_to_bv 64 OUT) (Z_to_bv 64 S) t3 t4 t5 t6)
F (Z_to_bv 64 sb_A_qmf_synth) fc None m1 (seg_rom asegs)
/\ munch [(usp + -624, usp + -608)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -624)
/\ rw_cells asegs m1 (usp + -624) [C8 stk8; CB 8 ja])
(MS (R_P usp S OUT f MODE gp tp (Z_to_bv 64 RA_sbd_iir_n) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_iir_n)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FR E27 E45 HD PT EFS EFFS HFS OBS S8 SPOS SLO SOFF O0 O1 ST LO LOS SPH MI.
unfold R_P, RA_sbd_iir_n, RA_sbd_qmf_n, sb_A_qmf_synth, sb_A_H0 in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xb8088)) with (Z_to_bv 64 0xb8088) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -624, usp + -608)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -624, usp + -608)]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold sb_fr in FR. cbn [map seq] in FR. rewrite E27, E45 in FR. unfold sbp_hdr in HD. rewrite EFS, EFFS in HD. unfold sbp_ptrs in PT.
carve_frame 16%nat ST. rename FR0 into ARG.
apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in ARG; [| reflexivity]. cbn [mk_CB_cells app] in ARG.
ato 0xb80a8. rewrite ?sx32_small by (unfold int31; lia).
ato 0xb80e0. rewrite ?sx32_small by (unfold int31; lia).
ato 0xa4b58.
replace (OUT + fsz ≪ 2) with (OUT + 4 * fsz) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact ARG].
Qed.

Lemma sbd_n5 : forall (usp lo S OUT f MODE : Z) (stk8 : word) (ja : list byte)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -624) [C8 stk8; CB 8 ja] -> stk asegs m lo (usp + -624) -> lo <= usp + -624 -> usp < 2^63 ->
mem_inv asegs m ->
evt asegs (fun ms => ms = MS (R_P usp S OUT f MODE gp tp (Z_to_bv 64 RA_sbd_qmf_n) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 (Z_to_bv 64 0) t3 t4 t5 t6)
F (Z_to_bv 64 0xb7ed0) fc None m (seg_rom asegs) /\ stk asegs m lo (usp + -608))
(MS (mkR (Z_to_bv 64 RA_sbd_qmf_n) (Z_to_bv 64 (usp + -624)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -608))
a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (S + 8)) s3 s4 (Z_to_bv 64 (Z.shiftr (S + 8) 3 + SHB)) (Z_to_bv 64 f) (Z_to_bv 64 MODE) (Z_to_bv 64 f)
(Z_to_bv 64 SHB) (Z_to_bv 64 OUT) (Z_to_bv 64 S) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_qmf_n)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros ARG ST LO SPH MI. unfold R_P, RA_sbd_qmf_n in *.
replace (ret_pc (Z_to_bv 64 0xb810c)) with (Z_to_bv 64 0xb810c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof ST as (STa & STb & _).
astep. replace (usp + -624 + 16) with (usp + -608) by lia. release_frame ARG ST (usp + -608).
ato 0xb7ed0.
apply evt_done. split; [reflexivity| exact ST].
Qed.
