(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1dg X1df X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05l X05m X09f X06d.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0z5 X0ys X0yq X0x2 X0yt X11l X0wg X0wc X0wh.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition sb_fr (g : nat -> word) : list cell := map (fun i => C8 (g i)) (seq 0 72).
Fixpoint fupds (g : nat -> word) (l : list (nat * word)) : nat -> word :=
match l with [] => g | (k, v) :: l' => fupds (fun i => if Nat.eqb i k then v else g i) l' end.
Lemma cells_size_sb_fr : forall g, cells_size (sb_fr g) = 576%nat. Proof. reflexivity. Qed.
#[export] Hint Rewrite cells_size_sb_fr : chunk_sizes.

Definition sb_e_stack_malloc_0 : Z := 0x51314.
Definition RA_sbd_smalloc : Z := 0xbe758.
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

Lemma sb_fr_of_list : forall ws : list word, length ws = 72%nat -> map C8 ws = sb_fr (fun i => nth i ws (Z_to_bv 64 0)).
Proof.
intros ws L. do 72 (destruct ws as [|? ws]; [discriminate L|]). destruct ws; [reflexivity| discriminate L].
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
stk bsegs m lo usp -> lo <= usp - 736 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
client_constsB m -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (g : nat -> word) (xa1 : word),
ms = MS (mkR (Z_to_bv 64 RA_sbd_smalloc) (Z_to_bv 64 (usp + -736)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -736))
(Z_to_bv 64 64) xa1 (Z_to_bv 64 OUT) a3 a4 a5 a6 a7
(Z_to_bv 64 S) (Z_to_bv 64 A) s4 s5 (Z_to_bv 64 SHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 sb_e_stack_malloc_0) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -736, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -736)
/\ rw_cells bsegs m1 (usp + -736) (sb_fr g) /\ g 0%nat = Z_to_bv 64 0 /\ g 62%nat = Z_to_bv 64 OUT /\ g 68%nat = Z_to_bv 64 0
/\ rw_cells bsegs m1 (usp + -160) (sb_saves F ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 A) (Z_to_bv 64 OUT) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_sb_decode) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ST LO LOS SPH SP32 (G1 & G2 & G3 & G4) MI.
unfold A_sb_decode, RA_sbd_smalloc, sb_e_stack_malloc_0,
gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'.
pose proof (munch_refl [(usp + -736, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -736, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 736%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 736 _ [] (576%nat :: repeat 8%nat 20)) in FR; [| reflexivity]. cbn [repeat mk_CB_cells app] in FR.
chunk_uncons FR as FSL. change 576%nat with (8 * 72)%nat in FSL. apply rw_cells_CB_u64 in FSL. destruct FSL as (ws & Lws & FSL).
rewrite (sb_fr_of_list ws Lws) in FSL. unfold sb_fr in FSL. cbn [map seq] in FSL.
replace (usp + -736 + 576) with (usp + -160) in FR by lia.
ato 0xbe71c. astep. rewrite land_m32_al by lia.
ato 0xbe74c. rewrite sx32_small by (unfold int31; lia).
ato 0x51314.
apply evt_done. eexists. exists (fupds (fun i => nth i ws (Z_to_bv 64 0)) [(0%nat, Z_to_bv 64 0); (62%nat, Z_to_bv 64 OUT); (68%nat, Z_to_bv 64 0)]). eexists.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
split; [exact FSL|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exact FR.
Qed.

Notation sbd_desc_cells MODE c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 :=
[C8 (Z_to_bv 64 MODE); C8 c1; C8 c2; C4 c3; C4 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12] (only parsing).
Definition RA_sbd_ctl104 : Z := 0xbe904.

Lemma sbd_w2 : forall (usp lo S OUT A f sf MP MODE : Z) (g : nat -> word) (s : sbd_state bptr) (a : sb_addrs)
(gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 : word)
(jb js : list byte) F fc (m : mem),
stk bsegs m lo (usp + -736) -> lo <= usp + -736 -> SH_HI <= lo -> usp < 2^63 ->
0 < f -> f mod 64 = 0 -> f + 64 <= lo -> f + 64 <= APP_TOP -> (f + 64 <= SH_LO \/ SH_HI <= f) -> sf = Z.shiftr f 3 + SHB ->
rw_cells bsegs m (usp + -736) (sb_fr g) -> rw_cells bsegs m f [CB 56 jb] -> rw_cells bsegs m sf [CB 8 js] -> g 62%nat = Z_to_bv 64 OUT ->

rw_cells bsegs m S (sbp_hdr s a) -> rw_cells bsegs m (S + 40) (sbp_ptrs s a OUT) ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= lo -> (S + 160 <= SH_LO \/ SH_HI <= S) -> (S + 160 <= f \/ f + 64 <= S) -> IMG_TOP_B <= f ->
MP = sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode (sbd_mode s) ->
ro_cells bsegs m MP (sbd_desc_cells MODE c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12) -> aobj bsegs m MP 96 -> MP mod 8 = 0 -> 0x10000 <= MP -> MP + 104 <= 0x65b000 ->
0 < OUT -> OUT + 8000 < 2^63 -> 0 <= sbd_frame_size s <= 320 ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (j24 j36 : list byte) (dtx : word),
ms = MS (mkR (Z_to_bv 64 RA_sbd_ctl104) (Z_to_bv 64 (usp + -736)) gp tp xt0 xt1 xt2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -736))
(Z_to_bv 64 (a_low a)) (Z_to_bv 64 104) (Z_to_bv 64 (OUT + 4 * sbd_frame_size s)) xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 (S + 8)) (Z_to_bv 64 A) s4 (Z_to_bv 64 MODE) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.shiftr (S + 8) 3 + SHB)) s8
(Z_to_bv 64 S) s10 s11 xt3 xt4 xt5 xt6)
F (Z_to_bv 64 A_speex_decoder_ctl) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -736, usp + -160); (f, f + 56); (sf, sf + 8)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -736)
/\ rw_cells bsegs m1 (usp + -736)
(sb_fr (fupds g [(46%nat, Z_to_bv 64 A); (14%nat, Z_to_bv 64 f); (67%nat, Z_to_bv 64 f); (19%nat, Z_to_bv 64 f); (13%nat, Z_to_bv 64 sf);
(40%nat, Z_to_bv 64 S); (54%nat, Z_to_bv 64 0); (33%nat, Z_to_bv 64 (Z.shiftr (S + 20) 3 + SHB)); (34%nat, Z_to_bv 64 (S + 20));
(61%nat, Z_to_bv 64 1); (16%nat, Z_to_bv 64 (OUT + 4 * sbd_frame_size s))]))
/\ rw_cells bsegs m1 f (sb_fhdr j24 dtx j36) /\ rw_cells bsegs m1 sf sb_fshadow)
(MS (mkR (Z_to_bv 64 RA_sbd_smalloc) (Z_to_bv 64 (usp + -736)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -736)) (Z_to_bv 64 f)
a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 A) s4 s5 (Z_to_bv 64 SHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_smalloc)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ST LO LOS SPH F0 F64 FLO FTOP FSH Esf FR FRB FRS E62 HD PT OBS S8 SPOS SLO SOFF SFA FIMG EMP DESC OBM MP8 MPLO MPHI O0 O1 FSZ MI.
unfold RA_sbd_smalloc, RA_sbd_ctl104, A_speex_decoder_ctl in *.
replace (ret_pc (Z_to_bv 64 0xbe758)) with (Z_to_bv 64 0xbe758) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'.
assert (SFR : SH_LO <= sf /\ sf + 8 <= SH_HI) by (subst sf; pose proof (shad_range_al f 64 ltac:(lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) FTOP) as X; rewrite shad_shiftr; unfold shad in *; change (64 / 8) with 8 in X; lia).
pose proof (munch_refl [(usp + -736, usp + -160); (f, f + 56); (sf, sf + 8)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
apply (rw_cells_split_CB bsegs _ _ [] 56 _ [] [8; 8; 8; 8; 4; 20]%nat) in FRB; [| reflexivity]. cbn [mk_CB_cells app] in FRB.
apply (rw_cells_split_CB bsegs _ _ [] 8 _ [] [1; 1; 1; 1; 1; 1; 1; 1]%nat) in FRS; [| reflexivity]. cbn [mk_CB_cells app] in FRS.
unfold sb_fr in FR. cbn [map seq] in FR. rewrite E62 in FR. unfold sbp_hdr in HD. unfold sbp_ptrs in PT.
assert (F8 : f mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
pose proof OBS as (OBS0 & OBS1 & _). pose proof OBM as (OBM0 & OBM1 & _).
assert (SFS : shfree [(usp + -736, usp + -160); (f, f + 56); (sf, sf + 8)] S 160).
{ apply shfree_cons_off; [unfold SH_LO, SH_HI in *; lia | lia | assumption |].
apply shfree_cons_off; [unfold SH_LO, SH_HI in *; lia | lia | assumption |].
apply (shfree_cons_sh _ _ _ _ _ f 64 F8); [subst sf; rewrite shad_shiftr; lia | subst sf; rewrite shad_shiftr; unfold shad; replace ((f + 64) / 8) with (f / 8 + 8) by (clear - F8; Z.div_mod_to_equations; lia); lia | exact SFA | apply shfree_nil]. }
assert (SFM : shfree [(usp + -736, usp + -160); (f, f + 56); (sf, sf + 8)] MP 96).
{ apply shfree_cons_off; [unfold SH_LO, SH_HI in *; lia | lia | assumption |].
apply shfree_cons_off; [unfold SH_LO, SH_HI in *; lia | lia | assumption |].
apply (shfree_cons_sh _ _ _ _ _ f 64 F8); [subst sf; rewrite shad_shiftr; lia | subst sf; rewrite shad_shiftr; unfold shad; replace ((f + 64) / 8) with (f / 8 + 8) by (clear - F8; Z.div_mod_to_equations; lia); lia | unfold IMG_TOP_B in FIMG; lia | apply shfree_nil]. }
astep. astep. astep. astep. sh_if.
unfold IMG_TOP_B in FIMG. pose proof SFR as SFR'. unfold SH_LO, SH_HI in SFR'. unfold SH_LO, SH_HI in SOFF.
bato 0xbe7c4. astep. rewrite <- Esf.
bato 0xbe840. rewrite <- EMP.
bato 0xbe89c. rewrite sx32_small by (unfold int31; lia).
bato 0xbe8f4.
bato 0x98c74.
replace (OUT + sbd_frame_size s * 4) with (OUT + 4 * sbd_frame_size s) by lia.
replace (OUT + sbd_frame_size s * 4) with (OUT + 4 * sbd_frame_size s) in FR by lia.
replace (Z.b2z (0 <? OUT)) with 1 in FR by (replace (0 <? OUT) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
rewrite <- E62 in FR.
apply (rw_cells_CB4_C4 bsegs _ _ [C8 _; C8 _; C8 _; CB 8 _]) in FRB. destruct FRB as (dtx & FRB).
apply evt_done. do 15 eexists. exists dtx. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
split; [exact FR|]. split; [exact FRB| exact FRS].
Qed.
Definition RA_sbd_native : Z := 0xbe928.
Definition RA_sbd_ctl103 : Z := 0xbe94c.

Definition R_P (usp S A f MODE : Z) (gp tp : word) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs11 xt3 xt4 xt5 xt6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 (usp + -736)) gp tp xt0 xt1 xt2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -736)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 (S + 8)) xs3 xs4 (Z_to_bv 64 MODE) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.shiftr (S + 8) 3 + SHB)) (Z_to_bv 64 f)
(Z_to_bv 64 S) (Z_to_bv 64 A) xs11 xt3 xt4 xt5 xt6.

Lemma sbd_w3 : forall (usp S OUT A f sf MODE : Z) (g : nat -> word) (s : sbd_state bptr) (a : sb_addrs)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
usp < 2^63 -> SH_HI <= usp + -736 ->
rw_cells bsegs m (usp + -736) (sb_fr g) -> g 46%nat = Z_to_bv 64 A -> g 19%nat = Z_to_bv 64 f -> g 62%nat = Z_to_bv 64 OUT ->
rw_cells bsegs m S (sbp_hdr s a) -> aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= usp + -736 -> (S + 160 <= SH_LO \/ SH_HI <= S) ->
mem_inv bsegs m ->
evt bsegs (fun ms =>
ms = MS (R_P usp S A f MODE gp tp (Z_to_bv 64 RA_sbd_native) t0 t1 t2 (Z_to_bv 64 (a_low a)) (Z_to_bv 64 A) (Z_to_bv 64 OUT) a3 a4 a5 a6 a7
(Z_to_bv 64 A) s4 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_decode_native) fc None m (seg_rom bsegs))
(MS (mkR (Z_to_bv 64 RA_sbd_ctl104) (Z_to_bv 64 (usp + -736)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -736)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (S + 8)) (Z_to_bv 64 A) s4 (Z_to_bv 64 MODE) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.shiftr (S + 8) 3 + SHB)) s8
(Z_to_bv 64 S) s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_ctl104)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SPH LOS FR E46 E19 E62 HD OBS S8 SPOS SLO SOFF MI.
unfold R_P, RA_sbd_ctl104, RA_sbd_native, A_speex_decode_native in *.
replace (ret_pc (Z_to_bv 64 0xbe904)) with (Z_to_bv 64 0xbe904) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'. unfold SH_LO, SH_HI in SOFF.
unfold sb_fr in FR. cbn [map seq] in FR. rewrite E46, E19, E62 in FR. unfold sbp_hdr in HD.
bato 0x98b18.
apply evt_done. reflexivity.
Qed.

Lemma sbd_w4 : forall (usp S OUT A f MODE : Z) (s : sbd_state bptr) (a : sb_addrs)
(gp tp t0 t1 t2 ret a1 a2 a3 a4 a5 a6 a7 s3 s4 s11 t3 t4 t5 t6 : word) F fc (m : mem),
usp < 2^63 -> 0 < f -> f + 64 < 2^63 ->
rw_cells bsegs m S (sbp_hdr s a) -> aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 < 2^63 ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (xa3 : word),
ms = MS (R_P usp S A f MODE gp tp (Z_to_bv 64 RA_sbd_ctl103) t0 t1 t2 (Z_to_bv 64 (a_low a)) (Z_to_bv 64 103) (Z_to_bv 64 (f + 32)) xa3 a4 a5 a6 a7
(Z_to_bv 64 (f + 32)) ret s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_decoder_ctl) fc None m (seg_rom bsegs))
(MS (R_P usp S A f MODE gp tp (Z_to_bv 64 RA_sbd_native) t0 t1 t2 ret a1 a2 a3 a4 a5 a6 a7 s3 s4 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_native)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SPH F0 F1 HD OBS S8 SPOS SHI MI.
unfold R_P, RA_sbd_ctl103, RA_sbd_native, A_speex_decoder_ctl in *.
replace (ret_pc (Z_to_bv 64 0xbe928)) with (Z_to_bv 64 0xbe928) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold sbp_hdr in HD.
bato 0x98c74.
apply evt_done. eexists. reflexivity.
Qed.

Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac tlia ::= (try unfold BITS_SIZEOF in * ); tlia_one.
Local Ltac slia ::= (try unfold BITS_SIZEOF in * ); first [ exact I | lia | split; [lia|exact I] ].

Lemma sbd_w5x : forall (usp S OUT A f MODE ret : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s11 t3 t4 t5 t6 : word) F fc (m : mem),
-2 <= ret < 0 ->
evt bsegs (fun ms => ms = MS (R_P usp S A f MODE gp tp (Z_to_bv 64 RA_sbd_ctl103) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 (Z_to_bv 64 ret) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xc0458) fc None m (seg_rom bsegs))
(MS (R_P usp S A f MODE gp tp (Z_to_bv 64 RA_sbd_ctl103) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 (Z_to_bv 64 ret) s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_ctl103)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros RNG. unfold R_P, RA_sbd_ctl103.
replace (ret_pc (Z_to_bv 64 0xbe94c)) with (Z_to_bv 64 0xbe94c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
assert (C : ret = -2 \/ ret = -1) by lia. destruct C as [-> | ->]; ato 0xc0458; apply evt_done; reflexivity.
Qed.

Definition R_J4 (usp S A f MODE : Z) (gp tp : word) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs11 xt3 xt4 xt5 xt6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 (usp + -736)) gp tp xt0 xt1 xt2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -736)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 (S + 8)) xs3 xs4 (Z_to_bv 64 MODE) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.shiftr (S + 8) 3 + SHB)) (Z_to_bv 64 f)
(Z_to_bv 64 (S + 152)) (Z_to_bv 64 A) xs11 xt3 xt4 xt5 xt6.
Definition R_J (usp S A f MODE : Z) (gp tp : word) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs11 xt3 xt4 xt5 xt6 : word) : bvmap 5 word :=
R_J4 usp S A f MODE gp tp xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 (Z_to_bv 64 (S + 144)) xs11 xt3 xt4 xt5 xt6.

Lemma sbd_w5 : forall (usp lo S OUT A D f MODE : Z) (g : nat -> word) (s : sbd_state bptr) (b : bits_st bptr) (pad1 : list byte)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_fr g) ->
rw_cells bsegs m (S + 136) (sbp_cfg s pad1) -> sbd_encode_submode s = 1 ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= lo -> (S + 160 <= SH_LO \/ SH_HI <= S) ->
bits_rep bsegs m A D b -> bits_ok b -> aobj bsegs m A BITS_SIZEOF -> aobj bsegs m D (sb_buf_size b) ->
(A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A) -> IMG_TOP_B <= A -> A + BITS_SIZEOF <= lo -> D + sb_buf_size b <= lo ->
stk bsegs m lo (usp + -736) -> lo <= usp + -736 - 64 -> SH_HI <= lo -> usp < 2^63 ->
client_constsB m -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
ms = MS (R_J usp S A f MODE gp tp xra xt0 xt1 xt2 (Z_to_bv 64 (sbw_id b)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 s3 s11 xt3 xt4 xt5 xt6)
F (Z_to_bv 64 0xbe9cc) fc None m1 (seg_rom bsegs)
/\ munch [(A, A + BITS_SIZEOF); (usp + -800, usp + -160)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -736)
/\ rw_cells bsegs m1 (usp + -736) (sb_fr (fupds g [(47%nat, Z_to_bv 64 (S + 144)); (48%nat, Z_to_bv 64 (S + 152))]))
/\ bits_rep bsegs m1 A D (sbw_bits b) /\ bits_ok (sbw_bits b) /\ sb_buf_size (sbw_bits b) = sb_buf_size b /\ 0 <= sbw_id b < 8)
(MS (R_P usp S A f MODE gp tp (Z_to_bv 64 RA_sbd_ctl103) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 (Z_to_bv 64 0) s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_ctl103)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FR CFG ESM OBS S8 SPOS SLO SOFF REP OK OBA OBD ASH AIMG ALO DLO ST LO LOS SPH CC MI.
unfold R_P, R_J, R_J4, RA_sbd_ctl103 in *.
replace (ret_pc (Z_to_bv 64 0xbe94c)) with (Z_to_bv 64 0xbe94c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'. pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'. pose proof ASH as ASH'. unfold SH_LO, SH_HI in ASH'.
unfold IMG_TOP_B in AIMG.
pose proof CC as (G1 & G2 & G3 & G4).
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in G1, G2, G3, G4.
pose proof (munch_refl [(A, A + BITS_SIZEOF); (usp + -800, usp + -160)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
pose proof OBA as (OBA0 & OBA1 & _).
assert (OF : offsh [(A, A + BITS_SIZEOF); (usp + -800, usp + -160)]) by (cbn; unfold SH_LO, SH_HI, BITS_SIZEOF in *; lia).
unfold sb_fr in FR. cbn [map seq] in FR. unfold sbp_cfg in CFG. rewrite ESM in CFG.
destruct REP as ((rj0 & Lrj0 & OBJ) & (bs0 & DAT & Hbs0) & SIDE0). unfold bits_cells in OBJ.
assert (Lbs0 : Z.of_nat (length bs0) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs0, zlength_map_unsigned in OK'. lia. }
pose proof SIDE0 as (AL & Apos & Dpos & _).
unfold APP_TOP, BITS_SIZEOF in OBA1. rename OBA1 into OBAhi. rename OBA0 into OBAlo. unfold BITS_SIZEOF in OBA.
bato 0xbe98c.
rebase_bits A D b rj0 bs0.
astep.
call (speex_bits_remaining_walk A D (usp + -736) lo b _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK OBA1 ST ltac:(lia) LOS ltac:(lia) ALO DLO CC1).
all: try eassumption.
subst x. clear REP1 OBA1 OBD1 CC1.
pose proof (bits_ints A D b OK SIDE0) as (In & _ & _ & _ & _ & _ & Rc & Rb & Rp & _).
assert (RNG : -1 <= speex_bits_remaining b < 2^31).
{ pose proof (speex_bits_remaining_spec b OK) as (R0 & R1). unfold int31 in In.
destruct (Z.eq_dec (sb_overflow b) 0) as [E|E]; [destruct (R0 E) as [E1 E2]; rewrite E1 in *; unfold bits_pos in *; lia| rewrite (R1 E); lia]. }
destruct (Z_le_gt_dec (speex_bits_remaining b) 0) as [KR|KR].
- astep. sh_if.
bato 0xbe9cc.
assert (EW : sbw_wb b = (0, b)) by (unfold sbw_wb; replace (0 <? speex_bits_remaining b) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
assert (EID : sbw_id b = 0) by (unfold sbw_id; rewrite EW; reflexivity).
assert (EB : sbw_bits b = b) by (unfold sbw_bits; rewrite EW; reflexivity).
rewrite EID, EB.
apply evt_done. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact PC|].
split; [exact FR|]. split; [exact POST|]. split; [exact OK|]. split; [reflexivity| lia].
- astep. sh_if.
destruct POST as ((rj1 & Lrj1 & OBJ) & (bs1 & DAT & Hbs1) & SIDE1). unfold bits_cells in OBJ.
bato 0xbe998.
rebase_bits A D b rj1 bs1. astep.
call (speex_bits_peek_walk A D (usp + -736) lo b _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK OBA1 OBD1 ASH PC ltac:(lia) LOS ltac:(lia) ALO DLO CC1).
all: try eassumption.
subst x. clear REP1 OBA1 OBD1 CC1.
destruct (speex_bits_peek b) as [wbv bp] eqn:EPK. cbn [fst snd] in *.
pose proof (speex_bits_peek_ok b wbv bp OK EPK) as (OKp & WBV & BPC).
assert (SZp : sb_buf_size bp = sb_buf_size b) by (destruct BPC as [-> | ->]; reflexivity).
assert (SWB : sbw_wb b = (wbv, bp)) by (unfold sbw_wb; replace (0 <? speex_bits_remaining b) with true by (symmetry; apply Z.ltb_lt; lia); exact EPK).
destruct (Z.eq_dec wbv 0) as [KW|KW].
+ subst wbv. bato 0xbe9cc.
assert (EID : sbw_id b = 0) by (unfold sbw_id; rewrite SWB; reflexivity).
assert (EB : sbw_bits b = bp) by (unfold sbw_bits; rewrite SWB; reflexivity).
rewrite EID, EB.
apply evt_done. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact PC|].
split; [exact FR|]. split; [exact POST|]. split; [exact OKp|]. split; [exact SZp| lia].
+ assert (wbv = 1) by lia. subst wbv.
destruct POST as ((rj2 & Lrj2 & OBJ) & (bs2 & DAT & Hbs2) & SIDE2). unfold bits_cells in OBJ.
bato 0xbe9a8.
rebase_bits A D bp rj2 bs2. astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -736) lo bp 1 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OKp ltac:(lia) OBA1 ltac:(rewrite SZp; exact OBD1) (ASH : _ \/ _) ltac:(lia) LOS ltac:(lia) ALO ltac:(rewrite SZp; exact DLO)).
all: try eassumption.
clear PC0. clear REP1 OBA1 OBD1 CC1.
change (snd (speex_bits_unpack_unsigned bp 1)) with (ub bp 1) in *.
pose proof (ub_ok bp 1 OKp ltac:(lia)) as (OK1 & SZ1 & _).
destruct POST as ((rj3 & Lrj3 & OBJ) & (bs3 & DAT & Hbs3) & SIDE3). unfold bits_cells in OBJ.
bato 0xbe9b4.
rebase_bits A D (ub bp 1) rj3 bs3. astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -736) lo (ub bp 1) 3 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK1 ltac:(lia) OBA1 ltac:(rewrite SZ1, SZp; exact OBD1) (ASH : _ \/ _) ltac:(lia) LOS ltac:(lia) ALO ltac:(rewrite SZ1, SZp; exact DLO)).
all: try eassumption.
subst x28. clear REP1 OBA1 OBD1 CC1.
change (snd (speex_bits_unpack_unsigned (ub bp 1) 3)) with (ub (ub bp 1) 3) in *. change (fst (speex_bits_unpack_unsigned (ub bp 1) 3)) with (uv (ub bp 1) 3) in *.
pose proof (ub_ok (ub bp 1) 3 OK1 ltac:(lia)) as (OK3 & SZ3 & V3). change (2 ^ 3) with 8 in V3.
bato 0xbe9cc.
assert (EID : sbw_id b = uv (ub bp 1) 3) by (unfold sbw_id; rewrite SWB; reflexivity).
assert (EB : sbw_bits b = ub (ub bp 1) 3) by (unfold sbw_bits; rewrite SWB; reflexivity).
rewrite EID, EB.
apply evt_done. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact PC|].
split; [exact FR|]. split; [exact POST|]. split; [exact OK3|]. split; [rewrite SZ3, SZ1; exact SZp| exact V3].
Qed.

Definition sb_id_valid (mo : spx_mode) (id : Z) : bool :=
(id =? 0) || match submode_at (sbm_submodes mo) id with Some _ => true | None => false end.
Lemma sbd_w6 : forall (usp S OUT A f MODE id : Z) (g : nat -> word) (s : sbd_state bptr) (pad1 : list byte) (oid : word)
(gp tp ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_fr g) -> g 48%nat = Z_to_bv 64 (S + 152) -> g 47%nat = Z_to_bv 64 (S + 144) -> g 19%nat = Z_to_bv 64 f ->
rw_cells bsegs m (S + 136) (sbp_cfg s pad1) -> rw_cells bsegs m (S + 152) [C4 oid] ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= usp + -736 -> (S + 160 <= SH_LO \/ SH_HI <= S) -> IMG_TOP_B <= S ->
(sbd_mode s = ModeWB \/ sbd_mode s = ModeUWB) -> MODE = sbmode_struct (sbd_mode s) -> aobj bsegs m MODE 216 -> lib_consts m ->
0 <= id < 8 -> SH_HI <= usp + -736 -> usp < 2^63 ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (xa0 xa1 xa2 : word),
ms = MS (R_J usp S A f MODE gp tp ra t0 t1 t2 xa0 xa1 xa2 a3 a4 a5 a6 a7 s3 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (if sb_id_valid (sbd_mode s) id then 0xbea68 else 0xc0734)) fc None m1 (seg_rom bsegs)
/\ munch [(S + 152, S + 156)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 (S + 152) [C4 (Z_to_bv 64 id)])
(MS (R_J usp S A f MODE gp tp ra t0 t1 t2 (Z_to_bv 64 id) a1 a2 a3 a4 a5 a6 a7 s3 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xbe9cc) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FR E48 E47 E19 CFG IDC OBS S8 SPOS SLO SOFF SIMG HMO EMODE OBM LC HID LOS SPH MI.
unfold R_J, R_J4 in *. unfold SH_LO, SH_HI in SOFF. unfold IMG_TOP_B in SIMG. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [(S + 152, S + 156)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(S + 152, S + 156)]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold sb_fr in FR. cbn [map seq] in FR. rewrite E48, E47, E19 in FR. unfold sbp_cfg in CFG.
assert (ESUB : sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR (sbd_mode s) = MODE + 40).
{ subst MODE. destruct HMO as [-> | ->]; reflexivity. }
rewrite ESUB in CFG.
assert (M8 : MODE mod 8 = 0) by (subst MODE; destruct HMO as [-> | ->]; reflexivity).
assert (MR : 0x10000 <= MODE /\ MODE + 216 <= 0x65b000) by (subst MODE; destruct HMO as [-> | ->]; cbn; unfold A_sb_wb_mode, A_sb_uwb_mode; lia).
assert (C : id = 0 \/ id = 1 \/ id = 2 \/ id = 3 \/ id = 4 \/ id = 5 \/ id = 6 \/ id = 7) by lia.
destruct HMO as [EMO | EMO]; rewrite EMO in *; cbn [sbmode_struct] in EMODE.
- pose proof (lib_const m A_sb_wb_mode LC_sb_wb_mode LC ltac:(lc_in)) as TAB. rewrite <- EMODE in TAB. unfold LC_sb_wb_mode in TAB. unfold A_sb_wb_mode in EMODE.
destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]].
all: match goal with |- context [if ?c then _ else _] => let v := eval vm_compute in c in change c with v end; cbv iota.
all: lazymatch goal with
| |- context [Z_to_bv 64 0xbea68] => bato 0xbea68
| |- context [Z_to_bv 64 0xc0734] => bato 0xc0734
end.
all: apply evt_done; do 4 eexists; (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]); exact IDC.
- pose proof (lib_const m A_sb_uwb_mode LC_sb_uwb_mode LC ltac:(lc_in)) as TAB. rewrite <- EMODE in TAB. unfold LC_sb_uwb_mode in TAB. unfold A_sb_uwb_mode in EMODE.
destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]].
all: match goal with |- context [if ?c then _ else _] => let v := eval vm_compute in c in change c with v end; cbv iota.
all: lazymatch goal with
| |- context [Z_to_bv 64 0xbea68] => bato 0xbea68
| |- context [Z_to_bv 64 0xc0734] => bato 0xc0734
end.
all: apply evt_done; do 4 eexists; (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]); exact IDC.
Qed.

Definition SB_GOT_STDERR : Z := 0xfcd78.
Definition SB_STDERR_VAR : Z := 0xfc010.
Definition SB_FMT_NOTIFY : Z := 0x272c0.
Definition SB_MSG_INVALID : Z := 0x27240.
Definition sb_e_fprintf : Z := 0x56d08.
Definition RA_sbd_fprintf : Z := 0xc0764.
Lemma sbd_w7 : forall (usp S OUT A f MODE errf : Z) (gp tp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s11 t3 t4 t5 t6 : word) F fc (m : mem),
aobj bsegs m SB_STDERR_VAR 8 ->
ro_cells bsegs m SB_GOT_STDERR [C8 (Z_to_bv 64 SB_STDERR_VAR)] -> ro_cells bsegs m SB_STDERR_VAR [C8 (Z_to_bv 64 errf)] ->
mem_inv bsegs m ->
evt bsegs (fun ms =>
ms = MS (R_J usp S A f MODE gp tp (Z_to_bv 64 RA_sbd_fprintf) t0 t1 t2 (Z_to_bv 64 errf) (Z_to_bv 64 SB_FMT_NOTIFY) (Z_to_bv 64 SB_MSG_INVALID)
a3 a4 a5 a6 a7 s3 s11 t3 t4 t5 t6)
F (Z_to_bv 64 sb_e_fprintf) fc None m (seg_rom bsegs))
(MS (R_J usp S A f MODE gp tp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xc0734) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros OBV GOTE VARE MI.
unfold R_J, R_J4, SB_GOT_STDERR, SB_STDERR_VAR, SB_FMT_NOTIFY, SB_MSG_INVALID, sb_e_fprintf, RA_sbd_fprintf in *.
assert (V8 : 1032208 mod 8 = 0) by reflexivity.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM. assert (OF : offsh []) by exact I.
bato 0x56d08.
apply evt_done. reflexivity.
Qed.
Lemma sbd_w8 : forall (usp S OUT A f MODE : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s11 t3 t4 t5 t6 : word) F fc (m : mem),
evt bsegs (fun ms => ms = MS (R_J4 usp S A f MODE gp tp (Z_to_bv 64 RA_sbd_fprintf) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 (Z_to_bv 64 (-2)) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xc0458) fc None m (seg_rom bsegs))
(MS (R_J usp S A f MODE gp tp (Z_to_bv 64 RA_sbd_fprintf) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_fprintf)) fc None m (seg_rom bsegs)).
Proof.
intros until m. unfold R_J, R_J4, RA_sbd_fprintf.
replace (ret_pc (Z_to_bv 64 0xc0764)) with (Z_to_bv 64 0xc0764) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0xc0458. apply evt_done. reflexivity.
Qed.

Lemma sbd_m : forall (usp S OUT A f MODE id : Z) (g : nat -> word) (s : sbd_state bptr) (pad1 : list byte)
(gp tp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_fr g) -> g 40%nat = Z_to_bv 64 S ->
rw_cells bsegs m (S + 136) (sbp_cfg s pad1) -> rw_cells bsegs m (S + 152) [C4 (Z_to_bv 64 id)] ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= usp + -736 -> (S + 160 <= SH_LO \/ SH_HI <= S) ->
(sbd_mode s = ModeWB \/ sbd_mode s = ModeUWB) -> MODE = sbmode_struct (sbd_mode s) -> aobj bsegs m MODE 216 -> lib_consts m ->
0 <= id < 8 -> SH_HI <= usp + -736 -> usp < 2^63 ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (xa0 xa1 xa2 xa3 xa4 : word),
ms = MS (R_J4 usp S A f MODE gp tp ra t0 t1 t2 xa0 xa1 xa2 xa3 xa4 a5 a6 a7 s3 (Z_to_bv 64 S) s11 t3 t4 t5 t6)
F (Z_to_bv 64 (match submode_at (sbm_submodes (sbd_mode s)) id with Some _ => 0xbeb08 | None => 0xc0214 end)) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -736, usp + -160)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 (usp + -736) (sb_fr (fupds g [(45%nat, Z_to_bv 64 (Z.shiftr (S + 144) 3 + SHB)); (44%nat, Z_to_bv 64 (Z.shiftr (S + 152) 3 + SHB))])))
(MS (R_J usp S A f MODE gp tp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xbea68) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FR E40 CFG IDC OBS S8 SPOS SLO SOFF HMO EMODE OBM LC HID LOS SPH MI.
unfold R_J, R_J4 in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [(usp + -736, usp + -160)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -736, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold sb_fr in FR. cbn [map seq] in FR. rewrite E40 in FR. unfold sbp_cfg in CFG.
assert (ESUB : sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR (sbd_mode s) = MODE + 40).
{ subst MODE. destruct HMO as [-> | ->]; reflexivity. }
rewrite ESUB in CFG.
assert (M8 : MODE mod 8 = 0) by (subst MODE; destruct HMO as [-> | ->]; reflexivity).
assert (MR : 0x10000 <= MODE /\ MODE + 216 <= 0x65b000) by (subst MODE; destruct HMO as [-> | ->]; cbn; unfold A_sb_wb_mode, A_sb_uwb_mode; lia).
assert (C : id = 0 \/ id = 1 \/ id = 2 \/ id = 3 \/ id = 4 \/ id = 5 \/ id = 6 \/ id = 7) by lia.
destruct HMO as [EMO | EMO]; rewrite EMO in *; cbn [sbmode_struct] in EMODE.
- pose proof (lib_const m A_sb_wb_mode LC_sb_wb_mode LC ltac:(lc_in)) as TAB. rewrite <- EMODE in TAB. unfold LC_sb_wb_mode in TAB. unfold A_sb_wb_mode in EMODE.
destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]].
all: match goal with |- context [match ?c with Some _ => _ | None => _ end] => let v := eval vm_compute in c in change c with v end; cbv iota.
all: bato 0xbeaa0; rewrite sx32_small by (unfold int31; lia).
all: lazymatch goal with
| |- context [Z_to_bv 64 0xbeb08] => bato 0xbeb08
| |- context [Z_to_bv 64 0xc0214] => bato 0xc0214
end.
all: rewrite <- E40 in FR; apply evt_done; do 6 eexists; (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]); exact FR.
- pose proof (lib_const m A_sb_uwb_mode LC_sb_uwb_mode LC ltac:(lc_in)) as TAB. rewrite <- EMODE in TAB. unfold LC_sb_uwb_mode in TAB. unfold A_sb_uwb_mode in EMODE.
destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]].
all: match goal with |- context [match ?c with Some _ => _ | None => _ end] => let v := eval vm_compute in c in change c with v end; cbv iota.
all: bato 0xbeaa0; rewrite sx32_small by (unfold int31; lia).
all: lazymatch goal with
| |- context [Z_to_bv 64 0xbeb08] => bato 0xbeb08
| |- context [Z_to_bv 64 0xc0214] => bato 0xc0214
end.
all: rewrite <- E40 in FR; apply evt_done; do 6 eexists; (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]); exact FR.
Qed.

Definition sb_e_allocas_unpoison : Z := 0x51f50.
Definition RA_sbd_unpoison_x : Z := 0xc0470.
Definition sb_fshadow_x : list cell :=
[C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-8));
C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))].
Lemma sbd_x1 : forall (usp f sf : Z) (g : nat -> word) (topw : word)
(ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_fr g) -> g 13%nat = Z_to_bv 64 sf -> g 68%nat = topw ->
rw_cells bsegs m sf sb_fshadow ->
0 < f -> f mod 64 = 0 -> f + 64 <= APP_TOP -> sf = Z.shiftr f 3 + SHB -> SH_HI <= usp + -736 -> usp < 2^63 ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR (Z_to_bv 64 RA_sbd_unpoison_x) (Z_to_bv 64 (usp + -736)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -736))
topw (Z_to_bv 64 (usp + -192)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 sf) s3 s4 s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 sb_e_allocas_unpoison) fc None m1 (seg_rom bsegs)
/\ munch [(sf, sf + 8)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 sf sb_fshadow_x)
(MS (mkR ra (Z_to_bv 64 (usp + -736)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -736))
a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xc0458) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FR E13 E68 FRS F0 F64 FTOP Esf LOS SPH MI.
unfold RA_sbd_unpoison_x, sb_e_allocas_unpoison, sb_fshadow, sb_fshadow_x in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (shad_range_al f 64 ltac:(lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) FTOP) as SW.
rewrite <- shad_shiftr, <- Esf in SW. change (64 / 8) with 8 in SW. unfold SH_LO, SH_HI in SW.
pose proof (munch_refl [(sf, sf + 8)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
unfold sb_fr in FR. cbn [map seq] in FR. rewrite E13, E68 in FR.
ato 0x51f50.
replace (usp + -736 + 544) with (usp + -192) by lia.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact FRS].
Qed.
Lemma sbd_x2 : forall (usp f sf : Z) (g : nat -> word) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) (hd : word) F fc (m : mem),
0 < f -> f mod 64 = 0 -> f + 64 <= usp + -736 -> f + 64 <= APP_TOP -> (f + 64 <= SH_LO \/ SH_HI <= f) -> sf = Z.shiftr f 3 + SHB ->
SH_HI <= usp + -736 -> usp < 2^63 ->
rw_cells bsegs m (usp + -736) (sb_fr g) -> g 14%nat = Z_to_bv 64 f ->
rw_cells bsegs m f [C8 hd] -> rw_cells bsegs m sf sb_fshadow_x ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR (Z_to_bv 64 RA_sbd_unpoison_x) (Z_to_bv 64 (usp + -736)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -736))
(Z_to_bv 64 (-11)) (Z_to_bv 64 f) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 sf) s3 s4 s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xc04a8) fc None m1 (seg_rom bsegs)
/\ munch [(f, f + 56); (sf, sf + 8)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 sf (map C1 (repeat bF5 8)))
(MS (mkR (Z_to_bv 64 RA_sbd_unpoison_x) (Z_to_bv 64 (usp + -736)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -736))
a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 sf) s3 s4 s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_unpoison_x)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros F0 F64 FLO FTOP FSH Esf LOS SPH FR E14 FRB FRS MI.
unfold RA_sbd_unpoison_x, sb_fshadow_x, bF5 in *. cbn [map repeat] in *. unfold APP_TOP in *.
replace (ret_pc (Z_to_bv 64 0xc0470)) with (Z_to_bv 64 0xc0470) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FSH as FSH'. unfold SH_LO, SH_HI in FSH'.
pose proof (shad_range_al f 64 ltac:(lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) ltac:(unfold APP_TOP; lia)) as SW.
rewrite <- shad_shiftr, <- Esf in SW. change (64 / 8) with 8 in SW. unfold SH_LO, SH_HI in SW.
pose proof (munch_refl [(f, f + 56); (sf, sf + 8)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
unfold sb_fr in FR. cbn [map seq] in FR. rewrite E14 in FR.
ato 0xc0480. astep. sh_if.
ato 0xc04a8.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact FRS].
Qed.

Lemma sbd_x3 : forall (usp lo f fl : Z) (g : nat -> word) (ra gp tp t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F0 : bvmap 5 word) (cra c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : word) F fc (m : mem),
stk bsegs m lo (usp + -736) -> lo <= usp + -736 -> usp < 2^63 -> 0 < f -> f + 64 <= lo ->
0 < fl -> fl + 1 <= lo ->
rw_cells bsegs m (usp + -736) (sb_fr g) -> rw_cells bsegs m (usp + -160) (sb_saves F0 cra c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11) ->
ro_cells bsegs m (f + 56) [C8 (Z_to_bv 64 fl)] -> rw_cells bsegs m fl [C1 (Z_to_bv 8 1)] ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (F' : bvmap 5 word),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 s4 (Z_to_bv 64 f) a2 a3 a4 a5 a6 a7 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 t3 t4 t5 t6)
F' (ret_pc cra) fc None m1 (seg_rom bsegs)
/\ munch [(fl, fl + 1)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp
/\ rw_cells bsegs m1 fl [C1 z8])
(MS (mkR ra (Z_to_bv 64 (usp + -736)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -736)) a0 (Z_to_bv 64 f) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xc04a8) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ST LO SPH F0' FLO L0 LLO FR SV FLP FLG MI.
unfold sb_saves, z8 in *. unfold sb_fr in FR. cbn [map seq] in FR.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
ato 0xc0530. release_frame FR ST (usp + -160). release_frame SV ST usp. astep.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact FLG].
Qed.

Definition sb_e_alloca_poison : Z := 0x51e24.
Definition RA_sbd_pois1 : Z := 0xbeb94.

Lemma sbd_v1 : forall (usp lo S OUT A f MODE : Z) (g : nat -> word) (s : sbd_state bptr) (a : sb_addrs)
(gp tp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_fr g) -> rw_cells bsegs m S (sbp_hdr s a) -> sbd_nbSubframes s = 4 ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= lo -> (S + 160 <= SH_LO \/ SH_HI <= S) ->
stk bsegs m lo (usp + -736) -> lo <= usp + -736 - 4192 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (xa2 : word) (jh : list byte),
ms = MS (mkR (Z_to_bv 64 RA_sbd_pois1) (Z_to_bv 64 (usp + -832)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -736))
(Z_to_bv 64 (usp + -800)) (Z_to_bv 64 16) xa2 a3 a4 a5 a6 a7
(Z_to_bv 64 (S + 8)) (Z_to_bv 64 (usp + -832)) (Z_to_bv 64 (S + 28)) (Z_to_bv 64 MODE) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.shiftr (S + 8) 3 + SHB))
(Z_to_bv 64 f) (Z_to_bv 64 (S + 152)) (Z_to_bv 64 A) s11 t3 t4 t5 t6)
F (Z_to_bv 64 sb_e_alloca_poison) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -4832, usp + -160)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -832)
/\ rw_cells bsegs m1 (usp + -736) (sb_fr (fupds g [(51%nat, Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB)); (52%nat, Z_to_bv 64 (S + 28)); (31%nat, Z_to_bv 64 4);
(9%nat, Z_to_bv 64 (usp + -736)); (32%nat, Z_to_bv 64 (usp + -800))]))
/\ rw_cells bsegs m1 (usp + -832) [CB 96 jh])
(MS (R_J4 usp S A f MODE gp tp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 (Z_to_bv 64 S) s11 t3 t4 t5 t6) F (Z_to_bv 64 0xbeb08) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FR HD ENS OBS S8 SPOS SLO SOFF ST LO LOS SPH U32 MI.
unfold R_J4, RA_sbd_pois1, sb_e_alloca_poison in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -4832, usp + -160)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -4832, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold sb_fr in FR. cbn [map seq] in FR. unfold sbp_hdr in HD. rewrite ENS in HD.
carve_frame 96%nat ST. rename FR0 into HULL.
carve_frame 3992%nat ST. rename FR0 into JK1.
carve_frame 8%nat ST. rename FR0 into P1.
apply (rw_cells_split_CB bsegs _ _ [] 8 _ [] [8]%nat) in P1; [| reflexivity]. cbn [mk_CB_cells app] in P1.
bato 0xbeb2c. rewrite sx32_small by (unfold int31; lia).
bato 0xbeb6c.
bdec. alits.
astep. astep.
replace (usp + -736 - 96) with (usp + -832) by lia. rewrite ?Z.mod_small by lia.
rewrite (land_m32_al (usp + -832)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
astep. astep. replace (usp + -736 - 4096) with (usp + -4832) by lia.
astep. astep. sh_if.
bato 0x51e24.
release_frame P1 ST (usp + -4824). release_frame JK1 ST (usp + -832).
replace (usp + -832 + 32) with (usp + -800) in * by lia.
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact HULL].
Qed.
Definition RA_sbd_pois2 : Z := 0xbec14.

Definition R_V (usp sp S A f MODE : Z) (gp tp : word) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs11 xt3 xt4 xt5 xt6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 sp) gp tp xt0 xt1 xt2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -736)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 (S + 8)) xs3 (Z_to_bv 64 (S + 28)) (Z_to_bv 64 MODE) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.shiftr (S + 8) 3 + SHB)) (Z_to_bv 64 f)
(Z_to_bv 64 (S + 152)) (Z_to_bv 64 A) xs11 xt3 xt4 xt5 xt6.

Lemma sbd_v2 : forall (usp lo S OUT A f MODE : Z) (g : nat -> word) (s : sbd_state bptr) (a : sb_addrs)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_fr g) -> g 51%nat = Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB) -> g 52%nat = Z_to_bv 64 (S + 28) ->
rw_cells bsegs m S (sbp_hdr s a) -> sbd_nbSubframes s = 4 ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= lo -> (S + 160 <= SH_LO \/ SH_HI <= S) ->
stk bsegs m lo (usp + -832) -> lo <= usp + -832 - 4192 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (xa2 : word) (jh : list byte),
ms = MS (R_V usp (usp + -928) S A f MODE gp tp (Z_to_bv 64 RA_sbd_pois2) t0 t1 t2 (Z_to_bv 64 (usp + -896)) (Z_to_bv 64 16) xa2 a3 a4 a5 a6 a7
(Z_to_bv 64 (usp + -928)) s11 t3 t4 t5 t6)
F (Z_to_bv 64 sb_e_alloca_poison) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -4928, usp + -160)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -928)
/\ rw_cells bsegs m1 (usp + -736) (sb_fr (fupds g [(68%nat, Z_to_bv 64 (usp + -832)); (15%nat, Z_to_bv 64 4); (17%nat, Z_to_bv 64 (usp + -896))]))
/\ rw_cells bsegs m1 (usp + -928) [CB 96 jh])
(MS (R_V usp (usp + -832) S A f MODE gp tp (Z_to_bv 64 RA_sbd_pois1) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (usp + -832)) s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_pois1)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FR E51 E52 HD ENS OBS S8 SPOS SLO SOFF ST LO LOS SPH U32 MI.
unfold R_V, RA_sbd_pois1, RA_sbd_pois2, sb_e_alloca_poison in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xbeb94)) with (Z_to_bv 64 0xbeb94) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -4928, usp + -160)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -4928, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold sb_fr in FR. cbn [map seq] in FR. rewrite E51, E52 in FR. unfold sbp_hdr in HD. rewrite ENS in HD.
carve_frame 96%nat ST. rename FR0 into HULL.
carve_frame 3992%nat ST. rename FR0 into JK1.
carve_frame 8%nat ST. rename FR0 into P1.
apply (rw_cells_split_CB bsegs _ _ [] 8 _ [] [8]%nat) in P1; [| reflexivity]. cbn [mk_CB_cells app] in P1.
bato 0xbebb0. rewrite sx32_small by (unfold int31; lia).
bato 0xbebec. bdec. alits.
astep. astep.
replace (usp + -832 - 96) with (usp + -928) by lia. rewrite ?Z.mod_small by lia.
rewrite (land_m32_al (usp + -928)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
astep. astep. replace (usp + -832 - 4096) with (usp + -4928) by lia.
astep. astep. sh_if.
bato 0x51e24.
release_frame P1 ST (usp + -4920). release_frame JK1 ST (usp + -928).
replace (usp + -928 + 32) with (usp + -896) in * by lia.
rewrite <- E51, <- E52 in FR.
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact HULL].
Qed.
Definition RA_sbd_ctl100 : Z := 0xbec38.
Definition RA_sbd_ctl101 : Z := 0xbec54.

Lemma sbd_v3 : forall (usp S OUT A f MODE : Z) (g : nat -> word) (s : sbd_state bptr) (a : sb_addrs)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_fr g) -> g 32%nat = Z_to_bv 64 (usp + -800) -> g 40%nat = Z_to_bv 64 S -> rw_cells bsegs m S (sbp_hdr s a) ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= usp + -928 -> (S + 160 <= SH_LO \/ SH_HI <= S) ->
SH_HI <= usp + -928 -> usp < 2^63 ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (R_V usp (usp + -928) S A f MODE gp tp (Z_to_bv 64 RA_sbd_ctl100) t0 t1 t2 (Z_to_bv 64 (a_low a)) (Z_to_bv 64 100) (Z_to_bv 64 (usp + -800)) a3 a4 a5 a6 a7
(Z_to_bv 64 S) s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_decoder_ctl) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -736, usp + -160)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 (usp + -736) (sb_fr (fupds g [(68%nat, Z_to_bv 64 (usp + -928))])))
(MS (R_V usp (usp + -928) S A f MODE gp tp (Z_to_bv 64 RA_sbd_pois2) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (usp + -928)) s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_pois2)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FR E32 E40 HD OBS S8 SPOS SLO SOFF LOS SPH MI.
unfold R_V, RA_sbd_pois2, RA_sbd_ctl100, A_speex_decoder_ctl in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xbec14)) with (Z_to_bv 64 0xbec14) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(usp + -736, usp + -160)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -736, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold sb_fr in FR. cbn [map seq] in FR. rewrite E32, E40 in FR. unfold sbp_hdr in HD.
bato 0x98c74. rewrite <- E32, <- E40 in FR.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact FR].
Qed.

Lemma sbd_v4 : forall (usp S OUT A f MODE : Z) (g : nat -> word) (s : sbd_state bptr) (a : sb_addrs)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_fr g) -> g 17%nat = Z_to_bv 64 (usp + -896) -> rw_cells bsegs m S (sbp_hdr s a) ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= usp + -928 -> (S + 160 <= SH_LO \/ SH_HI <= S) ->
SH_HI <= usp + -928 -> usp < 2^63 ->
mem_inv bsegs m ->
evt bsegs (fun ms =>
ms = MS (R_V usp (usp + -928) S A f MODE gp tp (Z_to_bv 64 RA_sbd_ctl101) t0 t1 t2 (Z_to_bv 64 (a_low a)) (Z_to_bv 64 101) (Z_to_bv 64 (usp + -896)) a3 a4 a5 a6 a7
(Z_to_bv 64 S) s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_decoder_ctl) fc None m (seg_rom bsegs))
(MS (R_V usp (usp + -928) S A f MODE gp tp (Z_to_bv 64 RA_sbd_ctl100) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 S) s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_ctl100)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FR E17 HD OBS S8 SPOS SLO SOFF LOS SPH MI.
unfold R_V, RA_sbd_ctl101, RA_sbd_ctl100, A_speex_decoder_ctl in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xbec38)) with (Z_to_bv 64 0xbec38) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold sb_fr in FR. cbn [map seq] in FR. rewrite E17 in FR. unfold sbp_hdr in HD.
bato 0x98c74.
apply evt_done. reflexivity.
Qed.
Definition RA_sbd_pois3 : Z := 0xbecdc.
Definition RA_sbd_pois4 : Z := 0xbed10.

Definition R_V5 (usp sp S A f MODE : Z) (gp tp : word) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs7 xs11 xt3 xt4 xt5 xt6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 sp) gp tp xt0 xt1 xt2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -736)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 8) xs3 xs4 (Z_to_bv 64 MODE) (Z_to_bv 64 SHB) xs7 (Z_to_bv 64 f)
(Z_to_bv 64 (S + 152)) (Z_to_bv 64 A) xs11 xt3 xt4 xt5 xt6.

Lemma sbd_v5 : forall (usp lo S OUT A f MODE : Z) (g : nat -> word) (s : sbd_state bptr) (a : sb_addrs)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_fr g) -> rw_cells bsegs m S (sbp_hdr s a) -> sbd_lpcSize s = 8 ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= lo -> (S + 160 <= SH_LO \/ SH_HI <= S) ->
stk bsegs m lo (usp + -928) -> lo <= usp + -928 - 4192 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (xa2 : word) (jh : list byte),
ms = MS (R_V5 usp (usp + -1024) S A f MODE gp tp (Z_to_bv 64 RA_sbd_pois3) t0 t1 t2 (Z_to_bv 64 (usp + -992)) (Z_to_bv 64 32) xa2 a3 a4 a5 a6 a7
(Z_to_bv 64 96) (Z_to_bv 64 (usp + -1024)) (Z_to_bv 64 (Z.shiftr (S + 8) 3 + SHB)) s11 t3 t4 t5 t6)
F (Z_to_bv 64 sb_e_alloca_poison) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -5024, usp + -160)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -1024)
/\ rw_cells bsegs m1 (usp + -736) (sb_fr (fupds g [(55%nat, Z_to_bv 64 (Z.shiftr (S + 32) 3 + SHB)); (56%nat, Z_to_bv 64 (S + 32)); (41%nat, Z_to_bv 64 32);
(53%nat, Z_to_bv 64 (usp + -992))]))
/\ rw_cells bsegs m1 (usp + -1024) [CB 96 jh])
(MS (R_V usp (usp + -928) S A f MODE gp tp (Z_to_bv 64 RA_sbd_ctl101) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 S) s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_ctl101)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FR HD ELPC OBS S8 SPOS SLO SOFF ST LO LOS SPH U32 MI.
unfold R_V, R_V5, RA_sbd_ctl101, RA_sbd_pois3, sb_e_alloca_poison in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xbec54)) with (Z_to_bv 64 0xbec54) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -5024, usp + -160)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -5024, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold sb_fr in FR. cbn [map seq] in FR. unfold sbp_hdr in HD. rewrite ELPC in HD.
carve_frame 96%nat ST. rename FR0 into HULL.
carve_frame 3992%nat ST. rename FR0 into JK1.
carve_frame 8%nat ST. rename FR0 into P1.
apply (rw_cells_split_CB bsegs _ _ [] 8 _ [] [8]%nat) in P1; [| reflexivity]. cbn [mk_CB_cells app] in P1.
bato 0xbec78. rewrite sx32_small by (unfold int31; lia).
bato 0xbecb0. bdec. alits.
astep. astep.
replace (usp + -928 - 96) with (usp + -1024) by lia. rewrite ?Z.mod_small by lia.
rewrite (land_m32_al (usp + -1024)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
astep. astep. replace (usp + -928 - 4096) with (usp + -5024) by lia.
astep. astep. sh_if.
bato 0x51e24.
release_frame P1 ST (usp + -5016). release_frame JK1 ST (usp + -1024).
replace (usp + -1024 + 32) with (usp + -992) in * by lia.
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact HULL].
Qed.

Lemma sbd_v6 : forall (usp lo S OUT A f MODE : Z) (g : nat -> word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_fr g) -> g 48%nat = Z_to_bv 64 (S + 152) -> g 41%nat = Z_to_bv 64 32 ->
stk bsegs m lo (usp + -1024) -> lo <= usp + -1024 - 4192 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (jh : list byte),
ms = MS (R_V5 usp (usp + -1120) S A f MODE gp tp (Z_to_bv 64 RA_sbd_pois4) t0 t1 t2 (Z_to_bv 64 (usp + -1088)) (Z_to_bv 64 32) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (usp + -1120)) (Z_to_bv 64 (S + 152)) (Z_to_bv 64 (usp + -1088)) s11 t3 t4 t5 t6)
F (Z_to_bv 64 sb_e_alloca_poison) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -5120, usp + -160)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -1120)
/\ rw_cells bsegs m1 (usp + -736) (sb_fr (fupds g [(68%nat, Z_to_bv 64 (usp + -1024))]))
/\ rw_cells bsegs m1 (usp + -1120) [CB 96 jh])
(MS (R_V5 usp (usp + -1024) S A f MODE gp tp (Z_to_bv 64 RA_sbd_pois3) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 96) (Z_to_bv 64 (usp + -1024)) (Z_to_bv 64 (Z.shiftr (S + 8) 3 + SHB)) s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_pois3)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FR E48 E41 ST LO LOS SPH U32 MI.
unfold R_V5, RA_sbd_pois3, RA_sbd_pois4, sb_e_alloca_poison in *. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xbecdc)) with (Z_to_bv 64 0xbecdc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -5120, usp + -160)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -5120, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold sb_fr in FR. cbn [map seq] in FR. rewrite E48, E41 in FR.
carve_frame 96%nat ST. rename FR0 into HULL.
carve_frame 3992%nat ST. rename FR0 into JK1.
carve_frame 8%nat ST. rename FR0 into P1.
apply (rw_cells_split_CB bsegs _ _ [] 8 _ [] [8]%nat) in P1; [| reflexivity]. cbn [mk_CB_cells app] in P1.
astep. astep. astep.
replace (usp + -1024 - 96) with (usp + -1120) by lia. rewrite ?Z.mod_small by lia.
rewrite (land_m32_al (usp + -1120)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
astep. astep. astep. replace (usp + -1024 - 4096) with (usp + -5120) by lia.
astep. astep. sh_if.
bato 0x51e24.
release_frame P1 ST (usp + -5112). release_frame JK1 ST (usp + -1120).
replace (usp + -1120 + 32) with (usp + -1088) in * by lia.
rewrite <- E48, <- E41 in FR.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact HULL].
Qed.
Definition RA_sbd_lspq : Z := 0xbede4.

Lemma sbd_v7 : forall (usp S OUT A f MODE SM id : Z) (g : nat -> word) (s : sbd_state bptr) (pad1 : list byte) (sm : submode)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_fr g) ->
g 45%nat = Z_to_bv 64 (Z.shiftr (S + 144) 3 + SHB) -> g 44%nat = Z_to_bv 64 (Z.shiftr (S + 152) 3 + SHB) -> g 47%nat = Z_to_bv 64 (S + 144) ->
g 56%nat = Z_to_bv 64 (S + 32) -> g 53%nat = Z_to_bv 64 (usp + -992) -> g 46%nat = Z_to_bv 64 A ->
rw_cells bsegs m (S + 136) (sbp_cfg s pad1) -> rw_cells bsegs m (S + 152) [C4 (Z_to_bv 64 id)] ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= usp + -1120 -> (S + 160 <= SH_LO \/ SH_HI <= S) ->
(sbd_mode s = ModeWB \/ sbd_mode s = ModeUWB) -> MODE = sbmode_struct (sbd_mode s) -> aobj bsegs m MODE 216 ->
submode_at (sbm_submodes (sbd_mode s)) id = Some sm -> 0 <= id < 8 -> SM = sb_sub_addr id -> aobj bsegs m SM 88 -> lib_consts m ->
SH_HI <= usp + -1120 -> usp < 2^63 ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (xa4 : word),
ms = MS (R_V5 usp (usp + -1120) S A f MODE gp tp (Z_to_bv 64 RA_sbd_lspq) t0 t1 t2 (Z_to_bv 64 (usp + -992)) (Z_to_bv 64 8) (Z_to_bv 64 A)
(Z_to_bv 64 A_lsp_unquant_high) xa4 a5 a6 a7 (Z_to_bv 64 (S + 32)) (Z_to_bv 64 (S + 152)) (Z_to_bv 64 (usp + -1088)) s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_lsp_unquant_high) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -736, usp + -160)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 (usp + -736) (sb_fr (fupds g [(68%nat, Z_to_bv 64 (usp + -1120)); (30%nat, Z_to_bv 64 (usp + -1088))])))
(MS (R_V5 usp (usp + -1120) S A f MODE gp tp (Z_to_bv 64 RA_sbd_pois4) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (usp + -1120)) (Z_to_bv 64 (S + 152)) (Z_to_bv 64 (usp + -1088)) s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_pois4)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FR E45 E44 E47 E56 E53 E46 CFG IDC OBS S8 SPOS SLO SOFF HMO EMODE OBM HSM HID ESM OBSM LC LOS SPH MI.
unfold R_V5, RA_sbd_pois4, RA_sbd_lspq, A_lsp_unquant_high in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xbed10)) with (Z_to_bv 64 0xbed10) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(usp + -736, usp + -160)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -736, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold sb_fr in FR. cbn [map seq] in FR. rewrite E45, E44, E47, E56, E53, E46 in FR. unfold sbp_cfg in CFG.
assert (ESUB : sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR (sbd_mode s) = MODE + 40).
{ subst MODE. destruct HMO as [-> | ->]; reflexivity. }
rewrite ESUB in CFG.
assert (M8 : MODE mod 8 = 0) by (subst MODE; destruct HMO as [-> | ->]; reflexivity).
assert (MR : 0x10000 <= MODE /\ MODE + 216 <= 0x65b000) by (subst MODE; destruct HMO as [-> | ->]; cbn; unfold A_sb_wb_mode, A_sb_uwb_mode; lia).
pose proof (lib_const m A_wb_submode1 LC_wb_submode1 LC ltac:(lc_in)) as T1. pose proof (lib_const m A_wb_submode2 LC_wb_submode2 LC ltac:(lc_in)) as T2.
pose proof (lib_const m A_wb_submode3 LC_wb_submode3 LC ltac:(lc_in)) as T3. pose proof (lib_const m A_wb_submode4 LC_wb_submode4 LC ltac:(lc_in)) as T4.
unfold LC_wb_submode1 in T1. unfold LC_wb_submode2 in T2. unfold LC_wb_submode3 in T3. unfold LC_wb_submode4 in T4.
destruct (sb_submode_cases (sbd_mode s) id sm HMO ltac:(lia) HSM) as [(EMO & [(-> & _) | [(-> & _) | [(-> & _) | (-> & _)]]]) | (EMO & -> & _)];
rewrite EMO in *; cbn [sbmode_struct] in EMODE; cbn [sb_sub_addr Z.eqb Pos.eqb] in ESM.
- pose proof (lib_const m A_sb_wb_mode LC_sb_wb_mode LC ltac:(lc_in)) as TAB. rewrite <- EMODE in TAB. unfold LC_sb_wb_mode in TAB. unfold A_sb_wb_mode in EMODE.
rewrite <- ESM in T1. clear T2 T3 T4. unfold A_wb_submode1 in ESM. assert (SM8 : SM mod 8 = 0) by (rewrite ESM; reflexivity).
bato 0xbed44. rewrite sx32_small by (unfold int31; lia).
bato 0xbeda0. rewrite <- ESM.
bato 0xb51dc.
rewrite <- E45, <- E44, <- E47, <- E56, <- E53, <- E46 in FR.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact FR].
- pose proof (lib_const m A_sb_wb_mode LC_sb_wb_mode LC ltac:(lc_in)) as TAB. rewrite <- EMODE in TAB. unfold LC_sb_wb_mode in TAB. unfold A_sb_wb_mode in EMODE.
rewrite <- ESM in T2. clear T1 T3 T4. unfold A_wb_submode2 in ESM. assert (SM8 : SM mod 8 = 0) by (rewrite ESM; reflexivity).
bato 0xbed44. rewrite sx32_small by (unfold int31; lia).
bato 0xbeda0. rewrite <- ESM.
bato 0xb51dc.
rewrite <- E45, <- E44, <- E47, <- E56, <- E53, <- E46 in FR.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact FR].
- pose proof (lib_const m A_sb_wb_mode LC_sb_wb_mode LC ltac:(lc_in)) as TAB. rewrite <- EMODE in TAB. unfold LC_sb_wb_mode in TAB. unfold A_sb_wb_mode in EMODE.
rewrite <- ESM in T3. clear T1 T2 T4. unfold A_wb_submode3 in ESM. assert (SM8 : SM mod 8 = 0) by (rewrite ESM; reflexivity).
bato 0xbed44. rewrite sx32_small by (unfold int31; lia).
bato 0xbeda0. rewrite <- ESM.
bato 0xb51dc.
rewrite <- E45, <- E44, <- E47, <- E56, <- E53, <- E46 in FR.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact FR].
- pose proof (lib_const m A_sb_wb_mode LC_sb_wb_mode LC ltac:(lc_in)) as TAB. rewrite <- EMODE in TAB. unfold LC_sb_wb_mode in TAB. unfold A_sb_wb_mode in EMODE.
rewrite <- ESM in T4. clear T1 T2 T3. unfold A_wb_submode4 in ESM. assert (SM8 : SM mod 8 = 0) by (rewrite ESM; reflexivity).
bato 0xbed44. rewrite sx32_small by (unfold int31; lia).
bato 0xbeda0. rewrite <- ESM.
bato 0xb51dc.
rewrite <- E45, <- E44, <- E47, <- E56, <- E53, <- E46 in FR.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact FR].
- pose proof (lib_const m A_sb_uwb_mode LC_sb_uwb_mode LC ltac:(lc_in)) as TAB. rewrite <- EMODE in TAB. unfold LC_sb_uwb_mode in TAB. unfold A_sb_uwb_mode in EMODE.
rewrite <- ESM in T1. clear T2 T3 T4. unfold A_wb_submode1 in ESM. assert (SM8 : SM mod 8 = 0) by (rewrite ESM; reflexivity).
bato 0xbed44. rewrite sx32_small by (unfold int31; lia).
bato 0xbeda0. rewrite <- ESM.
bato 0xb51dc.
rewrite <- E45, <- E44, <- E47, <- E56, <- E53, <- E46 in FR.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact FR].
Qed.
