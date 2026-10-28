(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bk X1bj X1cf X1bs X1c2.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hu X1g7 X1g0 X1gc.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma cbs_cells_split : forall k f d sc js n, (n < k)%nat -> (k <= length js)%nat ->
exists pre post,
cbs_cells k f d sc js
= pre ++ (if (16 - Z.of_nat k + Z.of_nat n =? 9) && sc then cb_cells f d (nth n js ([], [])) else cb_cells 0 0 (nth n js ([], [])))
++ post
/\ cells_size pre = (40 * n)%nat.
Proof.
induction k as [|k IH]; intros f d sc js n Hn Hk; [lia|].
destruct js as [|j js']; [cbn in Hk; lia|]. cbn [length] in Hk.
destruct n as [|n'].
- exists [], (cbs_cells k f d sc js'). split; [|reflexivity].
cbn [cbs_cells nth app]. cbv zeta.
replace (16 - Z.of_nat (S k) + Z.of_nat 0) with (16 - Z.of_nat (S k)) by lia. reflexivity.
- first [ pose proof (IH f d sc js' n' ltac:(lia) ltac:(lia)) as sfP_; sf_destruct 4%nat sfP_ as pre post E SZ | sf_fb; destruct (IH f d sc js' n' ltac:(lia) ltac:(lia)) as (pre & post & E & SZ) ].
exists ((if (16 - Z.of_nat (S k) =? 9) && sc then cb_cells f d j else cb_cells 0 0 j) ++ pre), post.
split.
+ cbn [cbs_cells nth]. cbv zeta. rewrite E.
replace (16 - Z.of_nat k + Z.of_nat n') with (16 - Z.of_nat (S k) + Z.of_nat (S n')) by lia.
rewrite <- app_assoc. reflexivity.
+ rewrite cells_size_app, SZ. destruct ((16 - Z.of_nat (S k) =? 9) && sc); rewrite cb_cells_size; lia.
Qed.

Ltac decide_ltbs :=
repeat match goal with
| |- context [?x <? ?y] =>
first [ replace (x <? y) with true by (symmetry; apply Z.ltb_lt; lia)
| replace (x <? y) with false by (symmetry; apply Z.ltb_ge; lia) ]
end.

Lemma lxor_sign_lit : forall x, 0 <= x < 2^64 -> Z.lxor x 9223372036854775808 = (x + 2^63) mod 2^64.
Proof. intros x Hx. change 9223372036854775808 with (2^63). apply zb_lxor_sign. exact Hx. Qed.

Section F.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.
Hypothesis HEXP : @exp_stmt.

Ltac rebits R A D bb rj Lrj OBJ bs DAT Hbs SIDE :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (R : bits_rep rsegs mc A D bb)
by (split; [exists rj; split; [exact Lrj| exact OBJ]| split; [exists bs; split; [exact DAT| exact Hbs]| exact SIDE]]);
clear OBJ DAT
end.

Ltac ntk := let K := fresh "K" in if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia; [exfalso; lia | clear K].
Ltac bdec := repeat match goal with
| |- context [Z.lxor ?x 9223372036854775808] => rewrite (lxor_sign_lit x) by lia
| |- context [?x <? ?y] => first [ replace (x <? y) with true by (symmetry; apply Z.ltb_lt; lia) | replace (x <? y) with false by (symmetry; apply Z.ltb_ge; lia) ]
| |- context [?x =? ?y] => first [ replace (x =? y) with true by (symmetry; apply Z.eqb_eq; lia) | replace (x =? y) with false by (symmetry; apply Z.eqb_neq; lia) ]
end; cbn [Z.b2z];
repeat match goal with |- context [Z.lxor ?x ?y] => is_Zlit x; is_Zlit y; let v := eval vm_compute in (Z.lxor x y) in change (Z.lxor x y) with v end.

#[using="Type"] Lemma inband_skip_join : forall (sc : bool) (A D : Z) b (STEREO lo adv : Z) (rj1 : list byte) (bs1 : list byte) (sws : list word)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(rav x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 xs1 xs2 : word) (F1 : bvmap 5 word) (fc1 : bv 32) (m0 m1 : mem),
adv = inband_skip_bits (uv b 4) -> sc && (uv b 4 =? SPEEX_INBAND_STEREO) = false ->
length rj1 = 16%nat -> rw_cells rsegs m1 A (bits_cells D (ub b 4) rj1) -> u8arr rsegs m1 D bs1 ->
sb_data (ub b 4) = map bv_unsigned bs1 -> bits_side A D (ub b 4) -> bits_ok (ub b 4) -> bits_ok b ->
rw_cells rsegs m1 STEREO (f32 sws) -> length sws = 2%nat ->
rw_cells rsegs m1 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
stk rsegs m1 lo (bv_unsigned sp + -32) -> lo + INBAND_DEPTH <= bv_unsigned sp -> NB_GLOBALS_TOP <= lo ->
apart STEREO 8 lo (bv_unsigned sp - lo) -> apart A BITS_SIZEOF lo (bv_unsigned sp - lo) -> apart D (sb_buf_size b) lo (bv_unsigned sp - lo) ->
apart STEREO 8 A BITS_SIZEOF -> apart STEREO 8 D (sb_buf_size b) ->
munch [(lo, bv_unsigned sp); (A, A + BITS_SIZEOF); (STEREO, STEREO + 8)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (inband_post sc A D b STEREO lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0)
(MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x1 x2 x3 (Z_to_bv 64 A) xs1 (Z_to_bv 64 (uv b 4)) (Z_to_bv 64 adv)
x4 x5 x6 x7 x8 x9 xs2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x10 x11 x12 x13)
F1 (Z_to_bv 64 0x2a17c) fc1 None m1 (seg_rom rsegs)).
Proof.
intros until m1. intros Hadv C9 Lrj1 OBJ1 DAT1 Hbs1 SIDE1 OK1 OK SW LSW FR STK LO GLO AS1 AS2 AS3 AS4 AS5 MU WM MI FRM.
unfold INBAND_DEPTH, NB_GLOBALS_TOP, apart in *. assert (BS : BITS_SIZEOF = 48) by reflexivity.
pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rsp.
unfold bits_cells in OBJ1.
pose proof (rw_cells_bound _ _ _ _ OBJ1) as GB. cbn [cells_size csize Nat.add length] in GB.
pose proof (u8arr_bound _ _ _ _ DAT1) as DB.
pose proof SIDE1 as sfP_; first [ sf_destruct 6%nat sfP_ as AL Apos Dpos BUFMAX _ SEP | sf_fb; destruct sfP_ as (AL & Apos & Dpos & BUFMAX & _ & SEP) ]. unfold BITS_BUF_MAX in BUFMAX. rewrite ub_size in BUFMAX, SEP.
assert (Lbs1 : Z.of_nat (length bs1) = sb_buf_size b).
{ pose proof OK1 as X. unfold bits_ok in X. rewrite Hbs1, zlength_map_unsigned, ub_size in X. lia. }
pose proof (speex_bits_unpack_unsigned_ok b 4 _ _ OK ltac:(lia) (unpack_eta b 4)) as (_ & Hv & _).
assert (ADV : 1 <= adv <= 64) by (subst adv; unfold inband_skip_bits; repeat destruct (_ <? _); lia).
zstep.
rebits REP1 A D (ub b 4) rj1 Lrj1 OBJ1 bs1 DAT1 Hbs1 SIDE1.
zstep. call (speex_bits_advance_spec A D (ub b 4) adv); [exact REP1 | exact OK1 | exact MI | lia |].
clear REP1. try rename MI0 into MI.
match goal with H : bits_rep _ _ _ _ (speex_bits_advance (ub b 4) adv) |- _ => rename H into REP2 end.
pose proof (speex_bits_advance_ok (ub b 4) adv OK1) as AOK.
do 6 zstep. release_frame FR STK (bv_unsigned sp). zstep.
apply evt_done. unfold inband_post.
eexists (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _). eexists _, _, _, sws.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRM|]. split; [exact STK|].
split; [exact SW|]. split; [exact LSW|].
unfold inband_bits. cbv zeta. rewrite C9, <- Hadv. split; [exact REP2|].
apply AOK. unfold bits_ok, bits_pos in OK1 |- *. lia.
Qed.

Ltac skip_leaf sc A D b STEREO lo n :=
eapply (inband_skip_join sc A D b STEREO lo n); try eassumption; try reflexivity;
try (unfold inband_skip_bits; decide_ltbs; reflexivity);
try (unfold INBAND_DEPTH, NB_GLOBALS_TOP, apart; lia).

#[using="HEXP"] Lemma inband_handler_proof : @inband_handler_stmt ptr.
Proof.
unfold inband_handler_stmt. intros until m.
intros REP OK CBS Ljs Fjs SW LSW STK LO GLO AP1 AP2 AP3 AP4 AP5 AP6 AP7 AP8 -> -> -> MI FRM CB0 CB8 SN0 SM4.
unfold INBAND_DEPTH, NB_GLOBALS_TOP, apart in *. assert (BS : BITS_SIZEOF = 48) by reflexivity.
pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rsp.
pose proof REP as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE).
pose proof SIDE as sfP_; first [ sf_destruct 6%nat sfP_ as AL Apos Dpos BUFMAX _ SEP | sf_fb; destruct sfP_ as (AL & Apos & Dpos & BUFMAX & _ & SEP) ]. unfold BITS_BUF_MAX in BUFMAX.
unfold bits_cells in OBJ. clear REP.
pose proof (rw_cells_bound _ _ _ _ OBJ) as GB. cbn [cells_size csize Nat.add length] in GB.
pose proof (u8arr_bound _ _ _ _ DAT) as DB.
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. lia. }
pose proof (rw_cells_bound _ _ _ _ CBS) as GC. rewrite cbs_cells_size in GC by lia.

pose proof (proj1 (proj1 CBS)) as WFC.
assert (CBSB : rw_cells rsegs m CBA [CB 640 (cells_bytes (cbs_cells 16 A_speex_std_stereo_request_handler STEREO sc js))]).
{ eapply rw_cells_samebytes; [exact CBS| | |].
- cbn [cells_wf cell_wf]. split; [|exact I]. rewrite cells_bytes_length by exact WFC. rewrite cbs_cells_size by lia. reflexivity.
- cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
- cbn [cells_size csize]. rewrite cbs_cells_size by lia. reflexivity. }
clear CBS.
pose proof (rw_cells_bound _ _ _ _ SW) as GS. rewrite cells_size_f32, LSW in GS.
pose proof (munch_refl [(lo, bv_unsigned sp); (A, A + BITS_SIZEOF); (STEREO, STEREO + 8)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
unfold A_speex_inband_handler.
carve_frame 32%nat STK.
do 9 zstep.
rebits REP A D b rj Lrj OBJ bs DAT Hbs SIDE.

zstep. call (speex_bits_unpack_unsigned_spec A D b 4); [exact REP | exact OK | lia | exact MI |].
clear REP. try rename MI0 into MI. rewrite (unpack_eta b 4) in *. cbn [fst snd] in *.
match goal with H : bits_rep _ _ _ _ (ub b 4) |- _ => destruct H as ((rj1 & Lrj1 & OBJ1) & (bs1 & DAT1 & Hbs1) & SIDE1) end.
unfold bits_cells in OBJ1.
match goal with H : ?v = Z_to_bv 64 (uv b 4) |- _ => subst v end.
pose proof (speex_bits_unpack_unsigned_ok b 4 _ _ OK ltac:(lia) (unpack_eta b 4)) as sfP_; first [ sf_destruct 6%nat sfP_ as OK1 Hv1 _ _ Hbs1' _ | sf_fb; destruct sfP_ as (OK1 & Hv1 & _ & _ & Hbs1' & _) ].
assert (Lbs1 : Z.of_nat (length bs1) = sb_buf_size b).
{ pose proof OK1 as X. unfold bits_ok in X. rewrite Hbs1, zlength_map_unsigned in X. lia. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (CBS : rw_cells rsegs mc CBA (cbs_cells 16 A_speex_std_stereo_request_handler STEREO sc js)) end.
{ eapply rw_cells_samebytes; [exact CBSB| exact WFC| |].
- cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
- cbn [cells_size csize]. rewrite cbs_cells_size by lia. reflexivity. }
clear CBSB.
first [ pose proof (cbs_cells_split 16 A_speex_std_stereo_request_handler STEREO sc js (Z.to_nat (uv b 4)) ltac:(lia) ltac:(lia)) as sfP_; sf_destruct 4%nat sfP_ as pre post E SZ | sf_fb; destruct (cbs_cells_split 16 A_speex_std_stereo_request_handler STEREO sc js (Z.to_nat (uv b 4)) ltac:(lia) ltac:(lia)) as (pre & post & E & SZ) ].
rewrite E in CBS. apply rw_cells_app in CBS. destruct CBS as [PRE CBS]. apply rw_cells_app in CBS. destruct CBS as [ENT POST].
rewrite SZ in ENT.
replace (16 - Z.of_nat 16 + Z.of_nat (Z.to_nat (uv b 4))) with (uv b 4) in ENT by lia.
replace (CBA + Z.of_nat (40 * Z.to_nat (uv b 4))) with (CBA + uv b 4 * 40) in ENT by lia.
pose proof (rw_cells_bound _ _ _ _ PRE) as GP. rewrite SZ in GP.
clear PRE POST E SZ.
zstep. zstep. zstep.
zstep. zstep. bdec.
zstep. ntk.
zstep. zstep. zstep. zstep. bdec.
zstep. ntk.
zstep. ntk.
zstep. rewrite land7_mod8. replace ((CBA + uv b 4 * 40) mod 8) with 0 by lia.
zstep. ntk.
destruct ((uv b 4 =? 9) && sc) eqn:C9.
-
apply andb_prop in C9. destruct C9 as [C9a C9b]. apply Z.eqb_eq in C9a.
unfold cb_cells in ENT. unfold A_speex_std_stereo_request_handler in ENT.
zstep. zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit64 in K0 by lia; lia|]. clear K0.
do 8 zstep. release_frame FR STK (bv_unsigned sp). zstep.
rebits REP1 A D (ub b 4) rj1 Lrj1 OBJ1 bs1 DAT1 Hbs1 SIDE1.
eapply evt_mono.
+ eapply (stereo_handler_proof HEXP A D (ub b 4) ST STEREO lo sws); try eassumption; try reflexivity;
unfold STEREO_DEPTH, NB_GLOBALS_TOP, apart; rewrite ?ub_size; try lia.
+ cbv beta. intros ms' sfH_; first [ sf_destruct 15%nat sfH_ as kk F' fc' m' sws' -> MU2 WM2 MI2 FRM2 STK2 SW2 LSW2 REP2 OK2 | sf_fb; destruct sfH_ as (kk & F' & fc' & m' & sws' & -> & MU2 & WM2 & MI2 & FRM2 & STK2 & SW2 & LSW2 & REP2 & OK2) ].
unfold inband_post. eexists kk, F', fc', m', sws'.
split; [reflexivity|].
split; [eapply munch_trans; [exact MU| exact MU2]|]. split; [eapply wmono_trans; [exact WM| exact WM2]|].
split; [exact MI2|]. split; [exact FRM2|]. split; [exact STK2|]. split; [exact SW2|]. split; [exact LSW2|].
unfold inband_bits. cbv zeta. unfold SPEEX_INBAND_STEREO. rewrite C9b, C9a. cbn [Z.eqb andb Pos.eqb].
split; [exact REP2| exact OK2].
-
assert (C9' : sc && (uv b 4 =? SPEEX_INBAND_STEREO) = false) by (unfold SPEEX_INBAND_STEREO; rewrite andb_comm; exact C9).
unfold cb_cells in ENT.
zstep. zstep. if_cases K0; zify_cond K0; [| exfalso; rewrite ?unsigned_lit64 in K0 by lia; lia]. clear K0.

zstep. zstep. if_cases K1; zify_cond K1; rewrite ?signed_lit_small in K1 by lia.
+
zstep. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit64 in K2 by lia.
*
zstep. zstep. if_cases K3; zify_cond K3; rewrite ?unsigned_lit64 in K3 by lia.
--   skip_leaf sc A D b STEREO lo 8.
-- zstep. zstep. if_cases K4; zify_cond K4; rewrite ?unsigned_lit64 in K4 by lia.
++
zstep. zstep. if_cases K5; zify_cond K5; rewrite ?unsigned_lit64 in K5 by lia.
**   zstep. skip_leaf sc A D b STEREO lo 32.
** zstep. zstep. skip_leaf sc A D b STEREO lo 64.
++ zstep. zstep. skip_leaf sc A D b STEREO lo 16.
* zstep. zstep. skip_leaf sc A D b STEREO lo 4.
+ zstep. zstep. skip_leaf sc A D b STEREO lo 1.
Qed.
End F.
