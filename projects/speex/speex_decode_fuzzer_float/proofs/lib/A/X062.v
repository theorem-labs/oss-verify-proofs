(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1dg X1df X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X081 X05l X07y X05m X09f X06d X069 X064.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X12b X0z5 X0ys X0yq X0x2 X0wx.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0z5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wx.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation mem := (word -> option byte).

Definition sbhd (mp al : Z) (ffs fs sfs nsf lpc fst sr enh : word) : list cell :=
[C8 (Z_to_bv 64 mp); C8 (Z_to_bv 64 al); C4 ffs; C4 fs; C4 sfs; C4 nsf; C4 lpc; C4 fst; C4 sr; C4 enh].

Section ARMS.
Variables (usp S P f sf : Z) (gp tp t0 t1 t2 a6 a7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
Let R (c : Z) (xra xa0 xa1 xa2 xa3 xa4 xa5 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -96)) xa0 xa1 xa2 xa3 xa4 xa5 a6 a7
(Z_to_bv 64 f) (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 c) (Z_to_bv 64 f) (Z_to_bv 64 sf) (Z_to_bv 64 SHB) s9 s10 s11 t3 t4 t5 t6.

Lemma sbarm_pass_b : forall (c : Z) (ra a0 a1 a2 a3 a4 a5 : word),
evt bsegs (fun ms' => ms' = MS (R c ra (Z_to_bv 64 0) a1 a2 a3 a4 a5) F (Z_to_bv 64 A_sbctl_epi) fc None m (seg_rom bsegs))
(MS (R c ra a0 a1 a2 a3 a4 a5) F (ret_pc (Z_to_bv 64 0xbe1ac)) fc None m (seg_rom bsegs)).
Proof.
intros. unfold R, A_sbctl_epi.
replace (ret_pc (Z_to_bv 64 0xbe1ac)) with (Z_to_bv 64 0xbe1ac) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
astep. astep. apply evt_done. reflexivity.
Qed.
Hypothesis MI : mem_inv bsegs m.
Hypothesis SB : 0 < S /\ S + 160 < 2^63.
Hypothesis PB : 0 < P /\ P + 24 < 2^63.
Hypothesis OBS : aobj bsegs m S 160.
Hypothesis S8 : S mod 8 = 0.
Hypothesis SOFF : S + 160 <= SH_LO \/ SH_HI <= S.

Lemma sbarm_pass_a : forall (c : Z) (mp al : Z) (ffs fs sfs nsf lpc fst sr enh : word) (ra a0 a1 a2 a3 a4 a5 : word),
c = 0 \/ c = 20 \/ c = 39 \/ c = 105 ->
rw_cells bsegs m S (sbhd mp al ffs fs sfs nsf lpc fst sr enh) ->
evt bsegs (fun ms' => exists xa3 xa4 xa5 : word,
ms' = MS (R c (Z_to_bv 64 (if c =? 0 then 0xbdba4 else if c =? 39 then 0xbd9b8 else 0xbe1ac))
(Z_to_bv 64 al) (Z_to_bv 64 c) (Z_to_bv 64 P) xa3 xa4 xa5) F (Z_to_bv 64 A_speex_decoder_ctl) fc None m (seg_rom bsegs))
(MS (R c ra a0 a1 a2 a3 a4 a5) F (Z_to_bv 64 (sbctl_armpc c)) fc None m (seg_rom bsegs)).
Proof using MI SB OBS S8 SOFF.
intros c mp al ffs fs sfs nsf lpc fst sr enh ra a0 a1 a2 a3 a4 a5 CODE HD. unfold sbhd in HD. unfold R, A_speex_decoder_ctl.
pose proof OBS as (OS0 & OS1 & _). unfold APP_TOP in *.
destruct CODE as [-> | [-> | [-> | ->]]]; unfold sbctl_armpc; cbn [Z.eqb Pos.eqb].
all: bato 0x98c74.
all: apply evt_done; do 3 eexists; reflexivity.
Qed.

Lemma sbarm_enh_b : forall (mp al : Z) (ffs fs sfs nsf lpc fst sr enh w : word) (ra a0 a1 a2 a3 a4 a5 : word),
aobj bsegs m P 4 -> P mod 4 = 0 -> rw_cells bsegs m P [C4 w] ->
rw_cells bsegs m S (sbhd mp al ffs fs sfs nsf lpc fst sr enh) -> (P + 4 <= S \/ S + 160 <= P) ->
evt bsegs (fun ms' => exists m' xa1 xa2, ms' = MS (R 0 ra (Z_to_bv 64 0) xa1 xa2 a3 a4 a5) F (Z_to_bv 64 A_sbctl_epi) fc None m' (seg_rom bsegs)
/\ rw_cells bsegs m' S (sbhd mp al ffs fs sfs nsf lpc fst sr (sx32 w)) /\ rw_cells bsegs m' P [C4 w]
/\ munch [(S + 44, S + 48)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m')
(MS (R 0 ra a0 a1 a2 a3 a4 a5) F (ret_pc (Z_to_bv 64 0xbdba4)) fc None m (seg_rom bsegs)).
Proof using All.
intros mp al ffs fs sfs nsf lpc fst sr enh w ra a0 a1 a2 a3 a4 a5 OBP P4 ARG HD AP. unfold sbhd in *. unfold R, A_sbctl_epi.
replace (ret_pc (Z_to_bv 64 0xbdba4)) with (Z_to_bv 64 0xbdba4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof OBS as (OS0 & OS1 & _). pose proof OBP as (OP0 & OP1 & _). unfold APP_TOP in *.
pose proof (rw_cells_bound _ _ _ _ ARG) as B. cbn [cells_size csize Nat.add] in B.
pose proof (munch_refl [(S + 44, S + 48)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(S + 44, S + 48)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
bato 0xbdbbc. astep. chk_merge OBP 4.
bato 0xbe340.
apply evt_done. do 3 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). assumption.
Qed.

Lemma sbarm_gfs : forall (mp al : Z) (v : Z) (fs sfs nsf lpc fst sr enh w : word) (ra a0 a1 a2 a3 a4 a5 : word),
aobj bsegs m P 4 -> P mod 4 = 0 -> rw_cells bsegs m P [C4 w] -> - 2^31 <= v < 2^31 ->
rw_cells bsegs m S (sbhd mp al (Z_to_bv 64 v) fs sfs nsf lpc fst sr enh) -> (P + 4 <= S \/ S + 160 <= P) ->
evt bsegs (fun ms' => exists m' xa1 xa2, ms' = MS (R 3 ra (Z_to_bv 64 0) xa1 xa2 a3 a4 a5) F (Z_to_bv 64 A_sbctl_epi) fc None m' (seg_rom bsegs)
/\ rw_cells bsegs m' S (sbhd mp al (Z_to_bv 64 v) fs sfs nsf lpc fst sr enh) /\ rw_cells bsegs m' P [C4 (Z_to_bv 64 v)]
/\ munch [(P, P + 4)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m')
(MS (R 3 ra a0 a1 a2 a3 a4 a5) F (Z_to_bv 64 (sbctl_armpc 3)) fc None m (seg_rom bsegs)).
Proof using All.
intros mp al v fs sfs nsf lpc fst sr enh w ra a0 a1 a2 a3 a4 a5 OBP P4 ARG RV HD AP. unfold sbhd in *. unfold R, A_sbctl_epi, sbctl_armpc. cbn [Z.eqb Pos.eqb].
pose proof OBS as (OS0 & OS1 & _). pose proof OBP as (OP0 & OP1 & _). unfold APP_TOP in *.
pose proof (rw_cells_bound _ _ _ _ ARG) as B. cbn [cells_size csize Nat.add] in B.
pose proof (munch_refl [(P, P + 4)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
bato 0xbdb60. astep. chk_merge OBP 4.
rewrite sx32_lit by lia.
bato 0xbe340.
apply evt_done. do 3 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). assumption.
Qed.

Lemma sbarm_gsr : forall (mp al : Z) (v : Z) (ffs fs sfs nsf lpc fst enh w : word) (ra a0 a1 a2 a3 a4 a5 : word),
aobj bsegs m P 4 -> P mod 4 = 0 -> rw_cells bsegs m P [C4 w] -> - 2^31 <= v < 2^31 ->
rw_cells bsegs m S (sbhd mp al ffs fs sfs nsf lpc fst (Z_to_bv 64 v) enh) -> (P + 4 <= S \/ S + 160 <= P) ->
evt bsegs (fun ms' => exists m' xa1 xa2, ms' = MS (R 25 ra (Z_to_bv 64 0) xa1 xa2 a3 a4 a5) F (Z_to_bv 64 A_sbctl_epi) fc None m' (seg_rom bsegs)
/\ rw_cells bsegs m' S (sbhd mp al ffs fs sfs nsf lpc fst (Z_to_bv 64 v) enh) /\ rw_cells bsegs m' P [C4 (Z_to_bv 64 v)]
/\ munch [(P, P + 4)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m')
(MS (R 25 ra a0 a1 a2 a3 a4 a5) F (Z_to_bv 64 (sbctl_armpc 25)) fc None m (seg_rom bsegs)).
Proof using All.
intros mp al v ffs fs sfs nsf lpc fst enh w ra a0 a1 a2 a3 a4 a5 OBP P4 ARG RV HD AP. unfold sbhd in *. unfold R, A_sbctl_epi, sbctl_armpc. cbn [Z.eqb Pos.eqb].
pose proof OBS as (OS0 & OS1 & _). pose proof OBP as (OP0 & OP1 & _). unfold APP_TOP in *.
pose proof (rw_cells_bound _ _ _ _ ARG) as B. cbn [cells_size csize Nat.add] in B.
pose proof (munch_refl [(P, P + 4)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
bato 0xbdf5c. astep. chk_merge OBP 4.
rewrite sx32_lit by lia.
bato 0xbe340.
apply evt_done. do 3 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). assumption.
Qed.

Lemma sbarm_gla_b : forall (v : Z) (ra a0 a1 a2 a3 a4 a5 : word),
aobj bsegs m P 4 -> P mod 4 = 0 -> rw_cells bsegs m P [C4 (Z_to_bv 64 v)] -> - 2^30 <= v < 2^30 ->
evt bsegs (fun ms' => exists m' xa1 xa2 xs8, ms' = MS (mkR ra (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -96))
(Z_to_bv 64 0) xa1 xa2 a3 a4 a5 a6 a7
(Z_to_bv 64 f) (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 39) (Z_to_bv 64 f) (Z_to_bv 64 sf) xs8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_sbctl_epi) fc None m' (seg_rom bsegs)
/\ rw_cells bsegs m' P [C4 (Z_to_bv 64 (2 * v))]
/\ munch [(P, P + 4)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m')
(MS (R 39 ra a0 a1 a2 a3 a4 a5) F (ret_pc (Z_to_bv 64 0xbd9b8)) fc None m (seg_rom bsegs)).
Proof using All.
intros v ra a0 a1 a2 a3 a4 a5 OBP P4 ARG RV. unfold R, A_sbctl_epi.
replace (ret_pc (Z_to_bv 64 0xbd9b8)) with (Z_to_bv 64 0xbd9b8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof OBP as (OP0 & OP1 & _). unfold APP_TOP in *.
pose proof (rw_cells_bound _ _ _ _ ARG) as B. cbn [cells_size csize Nat.add] in B.
pose proof (munch_refl [(P, P + 4)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
bato 0xbd9d0. astep. chk_merge OBP 4.
bato 0xbd9d8. rewrite sx32_lit by lia.
bato 0xbd9e0.
assert (E : bv_swrap 32 (v mod 18446744073709551616 + 1073741824) = v + 1073741824).
{ rewrite <- (swrap32_small (v + 1073741824)) by lia. apply swrap32_eqm. clear - RV. Z.div_mod_to_equations. lia. }
rewrite E. clear E.
bato 0xbd9e8. astep. chk_merge OBP 4. bato 0xbe340.
assert (E : Z_to_bv 64 (Z.shiftl (v mod 18446744073709551616) 1) = Z_to_bv 64 (2 * v)).
{ apply Z_to_bv_eqm. change (2^64) with 18446744073709551616. rewrite Z.shiftl_mul_pow2 by lia. change (2^1) with 2.
rewrite Zmult_mod_idemp_l. f_equal. lia. }
rewrite E in ARG. clear E.
apply evt_done. do 4 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). assumption.
Qed.

Lemma sbarm_ssr_a : forall (mp al : Z) (ffs fs sfs nsf lpc fst sr enh w : word) (l48 : list byte) (b4 b6 : byte) (ra a0 a1 a2 a3 a4 a5 : word),
aobj bsegs m P 4 -> P mod 4 = 0 -> rw_cells bsegs m P [C4 w] ->
rw_cells bsegs m S (sbhd mp al ffs fs sfs nsf lpc fst sr enh) -> (P + 4 <= S \/ S + 160 <= P) ->
rw_cells bsegs m (f + 48) [CB 4 l48] -> rw_cells bsegs m sf (sbctl_shadow b4 b6) ->
0 < f -> f mod 64 = 0 -> f + 64 <= APP_TOP -> (f + 64 <= SH_LO \/ SH_HI <= f) -> sf = Z.shiftr f 3 + SHB ->
(S + 160 <= f \/ f + 64 <= S) -> (P + 4 <= f \/ f + 64 <= P) -> (P + 4 <= SH_LO \/ SH_HI <= P) ->
evt bsegs (fun ms' => exists m' xa3 xa4 xa5 tw, ms' = MS (R 24 (Z_to_bv 64 0xbdee4) (Z_to_bv 64 al) (Z_to_bv 64 24) (Z_to_bv 64 (f + 48)) xa3 xa4 xa5)
F (Z_to_bv 64 A_speex_decoder_ctl) fc None m' (seg_rom bsegs)
/\ rw_cells bsegs m' S (sbhd mp al ffs fs sfs nsf lpc fst (sx32 w) enh) /\ rw_cells bsegs m' P [C4 w]
/\ rw_cells bsegs m' (f + 48) [C4 tw] /\ tw = Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_swrap 32 (bv_unsigned (sx32 w))) 1))
/\ rw_cells bsegs m' sf (sbctl_shadow b4 (Z_to_bv 8 4))
/\ munch [(sf, sf + 8); (S + 40, S + 44); (f + 48, f + 52)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m')
(MS (R 24 ra a0 a1 a2 a3 a4 a5) F (Z_to_bv 64 (sbctl_armpc 24)) fc None m (seg_rom bsegs)).
Proof using All.
intros mp al ffs fs sfs nsf lpc fst sr enh w l48 b4 b6 ra a0 a1 a2 a3 a4 a5 OBP P4 ARG HD AP TMP FRS F0 F64 FTOP FSH Esf SFA PFA POFF.
pose proof OBS as (_ & OBS1 & _). pose proof OBP as (_ & OBP1 & _).
unfold sbhd, sbctl_shadow, bF1, bF3 in *. unfold R, A_speex_decoder_ctl, sbctl_armpc. cbn [Z.eqb Pos.eqb]. unfold APP_TOP in *. pose proof OBP as (OP0 & _).
pose proof FSH as FSH'. unfold SH_LO, SH_HI in FSH'. pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'. pose proof POFF as POFF'. unfold SH_LO, SH_HI in POFF'.
pose proof (shad_range_al f 64 ltac:(lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) ltac:(unfold APP_TOP; lia)) as SW.
rewrite <- shad_shiftr, <- Esf in SW. change (64 / 8) with 8 in SW. unfold SH_LO, SH_HI in SW.
assert (ESF : sf = shad f) by (rewrite Esf; apply shad_shiftr).
assert (ESF2 : shad (f + 64) = sf + 8) by (rewrite ESF; unfold shad; clear - F64; Z.div_mod_to_equations; lia).
pose proof (rw_cells_bound _ _ _ _ ARG) as B. cbn [cells_size csize Nat.add] in B.
pose proof (munch_refl [(sf, sf + 8); (S + 40, S + 44); (f + 48, f + 52)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (SFS : shfree [(sf, sf + 8); (S + 40, S + 44); (f + 48, f + 52)] S 160).
{ apply (shfree_cons_sh _ _ _ _ _ f 64); [clear - F64; Z.div_mod_to_equations; lia| lia| lia| lia|].
apply shfree_cons_off; [unfold SH_LO, SH_HI; lia| lia| try unfold APP_TOP; lia|]. apply shfree_cons_off; [unfold SH_LO, SH_HI; lia| lia| try unfold APP_TOP; lia|]. apply shfree_nil. }
assert (SFP : shfree [(sf, sf + 8); (S + 40, S + 44); (f + 48, f + 52)] P 4).
{ apply (shfree_cons_sh _ _ _ _ _ f 64); [clear - F64; Z.div_mod_to_equations; lia| lia| lia| lia|].
apply shfree_cons_off; [unfold SH_LO, SH_HI; lia| lia| try unfold APP_TOP; lia|]. apply shfree_cons_off; [unfold SH_LO, SH_HI; lia| lia| try unfold APP_TOP; lia|]. apply shfree_nil. }
bato 0xbde98. astep. chk_merge OBP 4.
bato 0x98c74.
apply evt_done. do 5 eexists. split; [reflexivity|]. split; [exact HD|]. split; [exact ARG|]. split; [exact TMP|]. split; [reflexivity|].
split; [exact FRS|]. split; [exact MU|]. split; [exact WM| assumption].
Qed.

Lemma sbarm_ssr_b : forall (b4 b6 : byte) (ra a0 a1 a2 a3 a4 a5 : word),
rw_cells bsegs m sf (sbctl_shadow b4 b6) ->
evt bsegs (fun ms' => exists m' xa1, ms' = MS (R 24 ra (Z_to_bv 64 0) xa1 a2 a3 a4 a5) F (Z_to_bv 64 A_sbctl_epi) fc None m' (seg_rom bsegs)
/\ rw_cells bsegs m' sf (sbctl_shadow b4 bF8)
/\ munch [(sf, sf + 8)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m')
(MS (R 24 ra a0 a1 a2 a3 a4 a5) F (ret_pc (Z_to_bv 64 0xbdee4)) fc None m (seg_rom bsegs)).
Proof using All.
intros b4 b6 ra a0 a1 a2 a3 a4 a5 FRS. unfold sbctl_shadow, bF1, bF3, bF8 in *. unfold R, A_sbctl_epi.
replace (ret_pc (Z_to_bv 64 0xbdee4)) with (Z_to_bv 64 0xbdee4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (rw_cells_bound _ _ _ _ FRS) as B. cbn [cells_size csize Nat.add] in B.
pose proof (munch_refl [(sf, sf + 8)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
bato 0xbe340.
apply evt_done. do 2 eexists. split; [reflexivity|]. split; [exact FRS|]. split; [exact MU|]. split; [exact WM| assumption].
Qed.
End ARMS.

Lemma shr1w_low32 : forall (w : word) (v : Z), bv_unsigned w mod 2^32 = v mod 2^32 -> - 2^31 <= v < 2^31 ->
bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_swrap 32 (bv_unsigned (sx32 w))) 1))) mod 2^32 = c_shr1 v mod 2^32 /\ - 2^31 <= c_shr1 v < 2^31.
Proof.
intros w v E R. unfold c_shr1.
assert (SX : bv_swrap 32 (bv_unsigned (sx32 w)) = v).
{ unfold sx32. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite swrap32_mod64.
assert (A1 : bv_swrap 32 (bv_unsigned w) = v) by (rewrite <- (swrap32_small v R); apply swrap32_eqm; exact E).
rewrite A1. apply swrap32_small. exact R. }
rewrite SX. rewrite !Z.shiftr_div_pow2 by lia. change (2^1) with 2.
assert (R2 : - 2^31 <= v / 2 < 2^31) by (Z.div_mod_to_equations; lia).
rewrite (swrap32_small _ R2). rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite mod64_mod32.
split; [reflexivity| exact R2].
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition sbhd (mp al : Z) (ffs fs sfs nsf lpc fst sr enh : word) : list cell :=
[C8 (Z_to_bv 64 mp); C8 (Z_to_bv 64 al); C4 ffs; C4 fs; C4 sfs; C4 nsf; C4 lpc; C4 fst; C4 sr; C4 enh].

Section ARMS.
Variables (usp S P f sf : Z) (gp tp t0 t1 t2 a6 a7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
Let R (c : Z) (xra xa0 xa1 xa2 xa3 xa4 xa5 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -96)) xa0 xa1 xa2 xa3 xa4 xa5 a6 a7
(Z_to_bv 64 f) (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 c) (Z_to_bv 64 f) (Z_to_bv 64 sf) (Z_to_bv 64 SHB) s9 s10 s11 t3 t4 t5 t6.
Hypothesis MI : mem_inv asegs m.
Hypothesis SB : 0 < S /\ S + 160 < 2^63.
Hypothesis PB : 0 <= P /\ P + 24 < 2^63.
Hypothesis OBS : aobj asegs m S 160.
Hypothesis S8 : S mod 8 = 0.
Hypothesis SOFF : S + 160 <= SH_LO \/ SH_HI <= S.

Lemma sbarm_pass_a : forall (c : Z) (mp al : Z) (ffs fs sfs nsf lpc fst sr enh : word) (ra a0 a1 a2 a3 a4 a5 : word),
c = 0 \/ c = 20 \/ c = 39 \/ c = 105 ->
rw_cells asegs m S (sbhd mp al ffs fs sfs nsf lpc fst sr enh) ->
evt asegs (fun ms' => exists xa3 xa4 xa5 : word,
ms' = MS (R c (Z_to_bv 64 (if c =? 0 then 0xb5f68 else if c =? 39 then 0xb5e14 else 0xb6370))
(Z_to_bv 64 al) (Z_to_bv 64 c) (Z_to_bv 64 P) xa3 xa4 xa5) F (Z_to_bv 64 A_speex_decoder_ctl) fc None m (seg_rom asegs))
(MS (R c ra a0 a1 a2 a3 a4 a5) F (Z_to_bv 64 (sbctl_armpc c)) fc None m (seg_rom asegs)).
Proof using All.
intros c mp al ffs fs sfs nsf lpc fst sr enh ra a0 a1 a2 a3 a4 a5 CODE HD. unfold sbhd in HD. unfold R, A_speex_decoder_ctl.
destruct CODE as [-> | [-> | [-> | ->]]]; unfold sbctl_armpc; cbn [Z.eqb Pos.eqb].
all: ato 0x98638.
all: apply evt_done; do 3 eexists; reflexivity.
Qed.

Lemma sbarm_pass_b : forall (c : Z) (ra a0 a1 a2 a3 a4 a5 : word),
evt asegs (fun ms' => ms' = MS (R c ra (Z_to_bv 64 0) a1 a2 a3 a4 a5) F (Z_to_bv 64 A_sbctl_epi) fc None m (seg_rom asegs))
(MS (R c ra a0 a1 a2 a3 a4 a5) F (ret_pc (Z_to_bv 64 0xb6370)) fc None m (seg_rom asegs)).
Proof using All.
intros. unfold R, A_sbctl_epi.
replace (ret_pc (Z_to_bv 64 0xb6370)) with (Z_to_bv 64 0xb6370) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
astep. apply evt_done. reflexivity.
Qed.

Lemma sbarm_enh_b : forall (mp al : Z) (ffs fs sfs nsf lpc fst sr enh w : word) (ra a0 a1 a2 a3 a4 a5 : word),
aobj asegs m P 4 -> P mod 4 = 0 -> rw_cells asegs m P [C4 w] ->
rw_cells asegs m S (sbhd mp al ffs fs sfs nsf lpc fst sr enh) -> (P + 4 <= S \/ S + 160 <= P) ->
evt asegs (fun ms' => exists m' xa1 xa2, ms' = MS (R 0 ra (Z_to_bv 64 0) xa1 xa2 a3 a4 a5) F (Z_to_bv 64 A_sbctl_epi) fc None m' (seg_rom asegs)
/\ rw_cells asegs m' S (sbhd mp al ffs fs sfs nsf lpc fst sr (sx32 w)) /\ rw_cells asegs m' P [C4 w]
/\ munch [(S + 44, S + 48)] m m' /\ wmono asegs m m' /\ mem_inv asegs m')
(MS (R 0 ra a0 a1 a2 a3 a4 a5) F (ret_pc (Z_to_bv 64 0xb5f68)) fc None m (seg_rom asegs)).
Proof using All.
intros mp al ffs fs sfs nsf lpc fst sr enh w ra a0 a1 a2 a3 a4 a5 OBP P4 ARG HD AP. unfold sbhd in *. unfold R, A_sbctl_epi.
replace (ret_pc (Z_to_bv 64 0xb5f68)) with (Z_to_bv 64 0xb5f68) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (rw_cells_bound _ _ _ _ ARG) as B. cbn [cells_size csize Nat.add] in B.
pose proof (munch_refl [(S + 44, S + 48)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(S + 44, S + 48)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
astep. astep. astep. astep. chk_merge OBP 4.
ato 0xb6374.
apply evt_done. do 3 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). assumption.
Qed.

Lemma sbarm_gfs : forall (mp al : Z) (v : Z) (fs sfs nsf lpc fst sr enh w : word) (ra a0 a1 a2 a3 a4 a5 : word),
aobj asegs m P 4 -> P mod 4 = 0 -> rw_cells asegs m P [C4 w] -> - 2^31 <= v < 2^31 ->
rw_cells asegs m S (sbhd mp al (Z_to_bv 64 v) fs sfs nsf lpc fst sr enh) -> (P + 4 <= S \/ S + 160 <= P) ->
evt asegs (fun ms' => exists m' xa1 xa2, ms' = MS (R 3 ra (Z_to_bv 64 0) xa1 xa2 a3 a4 a5) F (Z_to_bv 64 A_sbctl_epi) fc None m' (seg_rom asegs)
/\ rw_cells asegs m' S (sbhd mp al (Z_to_bv 64 v) fs sfs nsf lpc fst sr enh) /\ rw_cells asegs m' P [C4 (Z_to_bv 64 v)]
/\ munch [(P, P + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m')
(MS (R 3 ra a0 a1 a2 a3 a4 a5) F (Z_to_bv 64 (sbctl_armpc 3)) fc None m (seg_rom asegs)).
Proof using All.
intros mp al v fs sfs nsf lpc fst sr enh w ra a0 a1 a2 a3 a4 a5 OBP P4 ARG RV HD AP. unfold sbhd in *. unfold R, A_sbctl_epi, sbctl_armpc. cbn [Z.eqb Pos.eqb].
pose proof (rw_cells_bound _ _ _ _ ARG) as B. cbn [cells_size csize Nat.add] in B.
pose proof (munch_refl [(P, P + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0xb5f30. astep. chk_merge OBP 4.
rewrite sx32_lit by lia.
ato 0xb6374.
apply evt_done. do 3 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). assumption.
Qed.

Lemma sbarm_gsr : forall (mp al : Z) (v : Z) (ffs fs sfs nsf lpc fst enh w : word) (ra a0 a1 a2 a3 a4 a5 : word),
aobj asegs m P 4 -> P mod 4 = 0 -> rw_cells asegs m P [C4 w] -> - 2^31 <= v < 2^31 ->
rw_cells asegs m S (sbhd mp al ffs fs sfs nsf lpc fst (Z_to_bv 64 v) enh) -> (P + 4 <= S \/ S + 160 <= P) ->
evt asegs (fun ms' => exists m' xa1 xa2, ms' = MS (R 25 ra (Z_to_bv 64 0) xa1 xa2 a3 a4 a5) F (Z_to_bv 64 A_sbctl_epi) fc None m' (seg_rom asegs)
/\ rw_cells asegs m' S (sbhd mp al ffs fs sfs nsf lpc fst (Z_to_bv 64 v) enh) /\ rw_cells asegs m' P [C4 (Z_to_bv 64 v)]
/\ munch [(P, P + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m')
(MS (R 25 ra a0 a1 a2 a3 a4 a5) F (Z_to_bv 64 (sbctl_armpc 25)) fc None m (seg_rom asegs)).
Proof using All.
intros mp al v ffs fs sfs nsf lpc fst enh w ra a0 a1 a2 a3 a4 a5 OBP P4 ARG RV HD AP. unfold sbhd in *. unfold R, A_sbctl_epi, sbctl_armpc. cbn [Z.eqb Pos.eqb].
pose proof (rw_cells_bound _ _ _ _ ARG) as B. cbn [cells_size csize Nat.add] in B.
pose proof (munch_refl [(P, P + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0xb6264. astep. chk_merge OBP 4.
rewrite sx32_lit by lia.
ato 0xb6374.
apply evt_done. do 3 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). assumption.
Qed.

Lemma sbarm_gla_b : forall (v : Z) (ra a0 a1 a2 a3 a4 a5 : word),
aobj asegs m P 4 -> P mod 4 = 0 -> rw_cells asegs m P [C4 (Z_to_bv 64 v)] -> - 2^30 <= v < 2^30 ->
evt asegs (fun ms' => exists m' xa1 xa2, ms' = MS (R 39 ra (Z_to_bv 64 0) xa1 xa2 a3 a4 a5) F (Z_to_bv 64 A_sbctl_epi) fc None m' (seg_rom asegs)
/\ rw_cells asegs m' P [C4 (Z_to_bv 64 (2 * v))]
/\ munch [(P, P + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m')
(MS (R 39 ra a0 a1 a2 a3 a4 a5) F (ret_pc (Z_to_bv 64 0xb5e14)) fc None m (seg_rom asegs)).
Proof using All.
intros v ra a0 a1 a2 a3 a4 a5 OBP P4 ARG RV. unfold R, A_sbctl_epi.
replace (ret_pc (Z_to_bv 64 0xb5e14)) with (Z_to_bv 64 0xb5e14) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (rw_cells_bound _ _ _ _ ARG) as B. cbn [cells_size csize Nat.add] in B.
pose proof (munch_refl [(P, P + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
astep. astep. astep. astep. chk_merge OBP 4.
ato 0xb5e2c. rewrite sx32_lit by lia.
astep.
assert (E : Z_to_bv 64 (Z.shiftl (v mod 18446744073709551616) 1) = Z_to_bv 64 (2 * v)).
{ apply Z_to_bv_eqm. change (2^64) with 18446744073709551616. rewrite Z.shiftl_mul_pow2 by lia. change (2^1) with 2.
rewrite Zmult_mod_idemp_l. f_equal. lia. }
rewrite E. clear E.
ato 0xb6374.
apply evt_done. do 3 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). assumption.
Qed.

Lemma sbarm_ssr_a : forall (mp al : Z) (ffs fs sfs nsf lpc fst sr enh w : word) (l48 : list byte) (b4 b6 : byte) (ra a0 a1 a2 a3 a4 a5 : word),
aobj asegs m P 4 -> P mod 4 = 0 -> rw_cells asegs m P [C4 w] ->
rw_cells asegs m S (sbhd mp al ffs fs sfs nsf lpc fst sr enh) -> (P + 4 <= S \/ S + 160 <= P) ->
rw_cells asegs m (f + 48) [CB 4 l48] -> rw_cells asegs m sf (sbctl_shadow b4 b6) ->
0 < f -> f mod 64 = 0 -> f + 64 <= APP_TOP -> (f + 64 <= SH_LO \/ SH_HI <= f) -> sf = Z.shiftr f 3 + SHB ->
(S + 160 <= f \/ f + 64 <= S) -> (P + 4 <= f \/ f + 64 <= P) -> (P + 4 <= SH_LO \/ SH_HI <= P) ->
evt asegs (fun ms' => exists m' xa3 xa4 xa5 tw, ms' = MS (R 24 (Z_to_bv 64 0xb6210) (Z_to_bv 64 al) (Z_to_bv 64 24) (Z_to_bv 64 (f + 48)) xa3 xa4 xa5)
F (Z_to_bv 64 A_speex_decoder_ctl) fc None m' (seg_rom asegs)
/\ rw_cells asegs m' S (sbhd mp al ffs fs sfs nsf lpc fst (sx32 w) enh) /\ rw_cells asegs m' P [C4 w]
/\ rw_cells asegs m' (f + 48) [C4 tw] /\ tw = Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_swrap 32 (bv_unsigned (sx32 w))) 1))
/\ rw_cells asegs m' sf (sbctl_shadow b4 (Z_to_bv 8 4))
/\ munch [(sf, sf + 8); (S + 40, S + 44); (f + 48, f + 52)] m m' /\ wmono asegs m m' /\ mem_inv asegs m')
(MS (R 24 ra a0 a1 a2 a3 a4 a5) F (Z_to_bv 64 (sbctl_armpc 24)) fc None m (seg_rom asegs)).
Proof using All.
intros mp al ffs fs sfs nsf lpc fst sr enh w l48 b4 b6 ra a0 a1 a2 a3 a4 a5 OBP P4 ARG HD AP TMP FRS F0 F64 FTOP FSH Esf SFA PFA POFF.
pose proof OBS as (_ & OBS1 & _). pose proof OBP as (_ & OBP1 & _).
unfold sbhd, sbctl_shadow, bF1, bF3 in *. unfold R, A_speex_decoder_ctl, sbctl_armpc. cbn [Z.eqb Pos.eqb]. unfold APP_TOP in *.
pose proof FSH as FSH'. unfold SH_LO, SH_HI in FSH'. pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'. pose proof POFF as POFF'. unfold SH_LO, SH_HI in POFF'.
pose proof (shad_range_al f 64 ltac:(lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) ltac:(unfold APP_TOP; lia)) as SW.
rewrite <- shad_shiftr, <- Esf in SW. change (64 / 8) with 8 in SW. unfold SH_LO, SH_HI in SW.
assert (ESF : sf = shad f) by (rewrite Esf; apply shad_shiftr).
assert (ESF2 : shad (f + 64) = sf + 8) by (rewrite ESF; unfold shad; clear - F64; Z.div_mod_to_equations; lia).
pose proof (rw_cells_bound _ _ _ _ ARG) as B. cbn [cells_size csize Nat.add] in B.
pose proof (munch_refl [(sf, sf + 8); (S + 40, S + 44); (f + 48, f + 52)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (SFS : shfree [(sf, sf + 8); (S + 40, S + 44); (f + 48, f + 52)] S 160).
{ apply (shfree_cons_sh _ _ _ _ _ f 64); [clear - F64; Z.div_mod_to_equations; lia| lia| lia| lia|].
apply shfree_cons_off; [unfold SH_LO, SH_HI; lia| lia| try unfold APP_TOP; lia|]. apply shfree_cons_off; [unfold SH_LO, SH_HI; lia| lia| try unfold APP_TOP; lia|]. apply shfree_nil. }
assert (SFP : shfree [(sf, sf + 8); (S + 40, S + 44); (f + 48, f + 52)] P 4).
{ apply (shfree_cons_sh _ _ _ _ _ f 64); [clear - F64; Z.div_mod_to_equations; lia| lia| lia| lia|].
apply shfree_cons_off; [unfold SH_LO, SH_HI; lia| lia| try unfold APP_TOP; lia|]. apply shfree_cons_off; [unfold SH_LO, SH_HI; lia| lia| try unfold APP_TOP; lia|]. apply shfree_nil. }
astep. astep.
astep. astep. astep. astep. chk_merge OBP 4.
ato 0x98638.
apply evt_done. do 5 eexists. split; [reflexivity|]. split; [exact HD|]. split; [exact ARG|]. split; [exact TMP|]. split; [reflexivity|].
split; [exact FRS|]. split; [exact MU|]. split; [exact WM| assumption].
Qed.

Lemma sbarm_ssr_b : forall (b4 b6 : byte) (ra a0 a1 a2 a3 a4 a5 : word),
rw_cells asegs m sf (sbctl_shadow b4 b6) ->
evt asegs (fun ms' => exists m' xa1, ms' = MS (R 24 ra (Z_to_bv 64 0) xa1 a2 a3 a4 a5) F (Z_to_bv 64 A_sbctl_epi) fc None m' (seg_rom asegs)
/\ rw_cells asegs m' sf (sbctl_shadow b4 bF8)
/\ munch [(sf, sf + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m')
(MS (R 24 ra a0 a1 a2 a3 a4 a5) F (ret_pc (Z_to_bv 64 0xb6210)) fc None m (seg_rom asegs)).
Proof using All.
intros b4 b6 ra a0 a1 a2 a3 a4 a5 FRS. unfold sbctl_shadow, bF1, bF3, bF8 in *. unfold R, A_sbctl_epi.
replace (ret_pc (Z_to_bv 64 0xb6210)) with (Z_to_bv 64 0xb6210) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (rw_cells_bound _ _ _ _ FRS) as B. cbn [cells_size csize Nat.add] in B.
pose proof (munch_refl [(sf, sf + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0xb6374.
apply evt_done. do 2 eexists. split; [reflexivity|]. split; [exact FRS|]. split; [exact MU|]. split; [exact WM| assumption].
Qed.
End ARMS.

Lemma shr1w_low32 : forall (w : word) (v : Z), bv_unsigned w mod 2^32 = v mod 2^32 -> - 2^31 <= v < 2^31 ->
bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_swrap 32 (bv_unsigned (sx32 w))) 1))) mod 2^32 = c_shr1 v mod 2^32 /\ - 2^31 <= c_shr1 v < 2^31.
Proof.
intros w v E R. unfold c_shr1.
assert (SX : bv_swrap 32 (bv_unsigned (sx32 w)) = v).
{ unfold sx32. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite swrap32_mod64.
assert (A1 : bv_swrap 32 (bv_unsigned w) = v) by (rewrite <- (swrap32_small v R); apply swrap32_eqm; exact E).
rewrite A1. apply swrap32_small. exact R. }
rewrite SX. rewrite !Z.shiftr_div_pow2 by lia. change (2^1) with 2.
assert (R2 : - 2^31 <= v / 2 < 2^31) by (Z.div_mod_to_equations; lia).
rewrite (swrap32_small _ R2). rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite mod64_mod32.
split; [reflexivity| exact R2].
Qed.
