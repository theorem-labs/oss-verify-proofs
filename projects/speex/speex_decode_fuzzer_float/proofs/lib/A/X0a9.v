(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1dh X1ch X1cg X1dk X1cr X1cs X1dg X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require Import X1sa.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nw X1qz.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X05p X09u X0ae X09j X09r X0ab.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1cu.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X110 X106 X10e X10x.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X106 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10e OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10x.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1cu.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments skipn {A} n l : simpl nomatch.
#[local] Arguments firstn {A} n l : simpl nomatch.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section PS.

Variables (A G D lo : Z) (bytes : list byte) (sy : sync_st bptr) (j0 j1 j2 j3 : list byte).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem).
Local Notation ogc := [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3].
Local Notation W := [(bv_unsigned sp - 128, bv_unsigned sp); (A, A + 32); (G, G + 32); (D, D + Z.of_nat (length bytes))].
Local Notation len := (Z.of_nat (length bytes)).
Hypothesis FOK : sync_fields_ok sy.
Hypothesis INV : sync_inv2 sy.
Hypothesis PRE : buf_pre (sy_buf sy) bytes.
Hypothesis LENB : len = sy_storage sy.
Hypothesis HD : 0 <= D. Hypothesis TOPD : D + len < 2^63.
Hypothesis HA : 0 < A. Hypothesis HG : 0 < G.
Hypothesis LO : lo + 128 <= bv_unsigned sp.

Hypothesis SEP_fA : A + 32 <= lo \/ bv_unsigned sp <= A.
Hypothesis SEP_fG : G + 32 <= lo \/ bv_unsigned sp <= G.
Hypothesis SEP_fD : D + len <= lo \/ bv_unsigned sp <= D.
Hypothesis SEP_AG : A + 32 <= G \/ G + 32 <= A.
Hypothesis SEP_AD : A + 32 <= D \/ D + len <= A.
Hypothesis SEP_GD : G + 32 <= D \/ D + len <= G.
#[local] Set Default Proof Using "FOK INV PRE LENB HD TOPD HA HG LO SEP_fA SEP_fG SEP_fD SEP_AG SEP_AD SEP_GD".

Notation POST0 := (pageseek_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A G D lo bytes ogc m0).
Notation POST := (pageseek_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A G D lo bytes ogc sy m0).

Notation FRAME m loc := (rw_cells bsegs m (bv_unsigned sp + -96) (loc ++ [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).

Lemma ps_epilogue0 : forall m (loc : list cell) r ogo (sy' : sync_st bptr)
(x1 x5 x6 x7 x8 x9 va0 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word),
cells_size loc = 48%nat ->
FRAME m loc -> stk bsegs m lo (bv_unsigned sp + -96) ->
munch W m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
rw_cells bsegs m A (sync_cells D sy') -> sync_fields_ok sy' -> u8arr bsegs m D bytes ->
rw_cells bsegs m G (og_cells D ogo ogc) ->
va0 = wz r ->
evt bsegs (POST0 r ogo sy')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 x8 x9 va0 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xc1978) fc None m (seg_rom bsegs)).
Proof.
intros until x31. intros SZ FR ST MU WM MI SY FOK' ARR OG ->. unfold wz.
pose proof (rw_cells_bound _ _ _ _ FR) as FB. rewrite cells_size_app, SZ in FB. cbn [cells_size csize Nat.add] in FB.
apply rw_cells_app in FR. destruct FR as [FRl FR]. rewrite SZ in FR.
replace (bv_unsigned sp + -96 + Z.of_nat 48) with (bv_unsigned sp + -48) in FR by lia.
ostep. ostep. ostep. ostep. ostep. ostep. ostep.
replace (bv_unsigned sp + -48) with (bv_unsigned sp + -96 + Z.of_nat (cells_size loc)) in FR by lia.
pose proof (rw_cells_join _ _ _ _ _ FRl FR) as FR2. clear FRl FR.
pose proof (stk_release _ _ _ _ _ ST FR2 ltac:(lia)) as ST2. clear ST FR2.
rewrite cells_size_app, SZ in ST2. cbn [cells_size csize Nat.add] in ST2.
replace (bv_unsigned sp + -96 + Z.of_nat 96) with (bv_unsigned sp) in ST2 by lia.
ostep. finish.
Qed.

Lemma ps_epilogue : forall m (loc : list cell) r ogo (sy' : sync_st bptr)
(x1 x5 x6 x7 x8 x9 va0 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word),
cells_size loc = 48%nat ->
FRAME m loc -> stk bsegs m lo (bv_unsigned sp + -96) ->
munch W m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
rw_cells bsegs m A (sync_cells D sy') -> sync_fields_ok sy' -> u8arr bsegs m D bytes ->
rw_cells bsegs m G (og_cells D ogo ogc) ->
va0 = wz r ->
evt bsegs (POST r ogo sy')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 x8 x9 va0 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xc1978) fc None m (seg_rom bsegs)).
Proof.
intros. eapply evt_mono; [eapply ps_epilogue0; eassumption|]. intros ms' X. left. exact X.
Qed.

Lemma ps_ret0 : forall m (loc : list cell) (sy1 : sync_st bptr)
(x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word),
cells_size loc = 48%nat ->
FRAME m loc -> stk bsegs m lo (bv_unsigned sp + -96) ->
munch W m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
rw_cells bsegs m A (sync_cells D sy1) -> sync_fields_ok sy1 -> u8arr bsegs m D bytes ->
rw_cells bsegs m G ogc ->
evt bsegs (POST 0 None sy1)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xc18d4) fc None m (seg_rom bsegs)).
Proof.
intros until x31. intros SZ FR ST MU WM MI SY FOK' ARR OG.
ostep. ostep. eapply ps_epilogue; try eassumption. reflexivity.
Qed.

Lemma ps_sync_fail : forall m (loc : list cell) (sy1 : sync_st bptr) r (sy' : sync_st bptr)
(x1 x5 x6 x7 va0 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
cells_size loc = 48%nat ->
FRAME m loc -> stk bsegs m lo (bv_unsigned sp + -96) ->
munch W m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
rw_cells bsegs m A (sync_cells D sy1) -> sync_fields_ok sy1 -> u8arr bsegs m D bytes ->
rw_cells bsegs m G ogc ->
sy_buf sy1 = sy_buf sy ->
1 <= sy_fill sy1 - sy_returned sy1 -> sy_fill sy1 <= zlength (sy_buf sy) ->
sync_fail sy1 (sy_returned sy1) (sy_fill sy1 - sy_returned sy1) = ((r, None), sy') ->
evt bsegs (POST r None sy')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 G) va0 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (D + sy_returned sy1)) (Z_to_bv 64 (sy_fill sy1 - sy_returned sy1)) (Z_to_bv 64 D) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xc1910) fc None m (seg_rom bsegs)).
Proof.
intros until x31. intros SZ FR ST MU WM MI SY FOK1 ARR OG EB Hb Hf RES.
pose proof FOK1 as (Fs & Ff & Fr & Fu & Fh & Fbb). unfold int31 in Fs, Ff, Fr, Fu, Fh, Fbb.
pose proof PRE as [PRE1 PRE2]. unfold zlength in *.
pose proof (rw_cells_bound _ _ _ _ SY) as AB. cbn [cells_size csize Nat.add] in AB.
pose proof (u8arr_bound _ _ _ _ ARR) as DB.
pose proof (rw_cells_bound _ _ _ _ FR) as FB. rewrite cells_size_app, SZ in FB. cbn [cells_size csize Nat.add] in FB.

unfold sync_cells, wz in SY.
pose proof (rw_cells_merge bsegs m A [C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 (sy_storage sy1)); C4 (Z_to_bv 64 (sy_fill sy1)); C4 (Z_to_bv 64 (sy_returned sy1)); C4 (Z_to_bv 64 (sy_unsynced sy1))]
[C4 (Z_to_bv 64 (sy_headerbytes sy1)); C4 (Z_to_bv 64 (sy_bodybytes sy1))] [] SY) as SY2. clear SY.
cbn [cells_size csize cells_bytes cbytes app Nat.add] in SY2.
lstep.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (recell_zero8 mx A [C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 (sy_storage sy1)); C4 (Z_to_bv 64 (sy_fill sy1)); C4 (Z_to_bv 64 (sy_returned sy1)); C4 (Z_to_bv 64 (sy_unsynced sy1))] [] SY2) as SY end.
clear SY2. cbn [app] in SY. unfold wz in SY.

ostep. ostep. ostep. ostep.
apply evt_done. right. split; [reflexivity|]. unfold pageseek_cut.
eexists _, loc, sy1. do 12 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact SZ|]. split; [exact FR|].
split; [exact SY|]. split; [exact FOK1|]. split; [exact ARR|]. split; [exact OG|]. split; [exact EB|]. split; [exact Hb|]. split; [exact Hf| exact RES].
Qed.

Lemma frame_join : forall m j8 j4 (hb bb chk : Z),
rw_cells bsegs m (bv_unsigned sp + -96) [CB 8 j8] ->
rw_cells bsegs m (bv_unsigned sp + -88) [C8 (Z_to_bv 64 (D + sy_returned sy)); C4 (Z_to_bv 64 hb); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (D + sy_returned sy + hb)); C4 (Z_to_bv 64 bb); C4 (Z_to_bv 64 0)] ->
rw_cells bsegs m (bv_unsigned sp + -56) [CB 4 j4; C4 (Z_to_bv 64 chk); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
FRAME m [CB 8 j8; C8 (Z_to_bv 64 (D + sy_returned sy)); C4 (Z_to_bv 64 hb); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (D + sy_returned sy + hb)); C4 (Z_to_bv 64 bb); C4 (Z_to_bv 64 0); CB 4 j4; C4 (Z_to_bv 64 chk)].
Proof.
intros m j8 j4 hb bb chk FR0 PG FR.
replace (bv_unsigned sp + -88) with (bv_unsigned sp + -96 + Z.of_nat (cells_size [CB 8 j8])) in PG by (cbn; lia).
pose proof (rw_cells_join _ _ _ _ _ FR0 PG) as FR1.
replace (bv_unsigned sp + -56) with (bv_unsigned sp + -96 + Z.of_nat (cells_size ([CB 8 j8] ++ [C8 (Z_to_bv 64 (D + sy_returned sy)); C4 (Z_to_bv 64 hb); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (D + sy_returned sy + hb)); C4 (Z_to_bv 64 bb); C4 (Z_to_bv 64 0)]))) in FR by (cbn; lia).
pose proof (rw_cells_join _ _ _ _ _ FR1 FR) as FR2. cbn [app] in FR2. exact FR2.
Qed.

Lemma ps_deliver : forall m (j8 j4 : list byte) (hb bb chk : Z)
(x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
let ret := sy_returned sy in let fill := sy_fill sy in let buf := sy_buf sy in
let nseg := znth buf (ret + 26) in
hb = 27 + nseg -> ret + hb + bb <= fill -> 0 <= bb <= 255 * 255 ->
rw_cells bsegs m (bv_unsigned sp + -96) [CB 8 j8] ->
rw_cells bsegs m (bv_unsigned sp + -88) [C8 (Z_to_bv 64 (D + ret)); C4 (Z_to_bv 64 hb); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (D + ret + hb)); C4 (Z_to_bv 64 bb); C4 (Z_to_bv 64 0)] ->
rw_cells bsegs m (bv_unsigned sp + -56) [CB 4 j4; C4 (Z_to_bv 64 chk); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk bsegs m lo (bv_unsigned sp + -96) ->
munch W m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
rw_cells bsegs m A (sync_cells D (mkSync (sy_data sy) buf (sy_storage sy) fill ret (sy_unsynced sy) hb bb)) ->
u8arr bsegs m D bytes -> rw_cells bsegs m G ogc ->
evt bsegs (POST (hb + bb) (Some (mkPage ret hb bb)) (mkSync (sy_data sy) buf (sy_storage sy) fill (ret + (hb + bb)) 0 0 0))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 G)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (D + sy_returned sy)) (Z_to_bv 64 (sy_fill sy - sy_returned sy)) (Z_to_bv 64 chk)
s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xc1940) fc None m (seg_rom bsegs)).
Proof.
intros until x31. intros ret fill buf nseg Hhb Hfit Hbbr FR0 PG FR ST MU WM MI SY ARR OG.
pose proof FOK as sfP_; first [ sf_destruct 6%nat sfP_ as Fs Ff Fr Fu Fh Fbb | sf_fb; destruct sfP_ as (Fs & Ff & Fr & Fu & Fh & Fbb) ]. unfold int31 in Fs, Ff, Fr, Fu, Fh, Fbb.
pose proof INV as [[I1 [I2 [I3 [I4 Ibok]]]] _]. unfold zlength in I2.
fold ret fill buf in Fr, Ff, I1, I2, Ibok.
pose proof (znth_bytes_ok buf (ret + 26) Ibok) as Rnseg. fold nseg in Rnseg.
pose proof (rw_cells_bound _ _ _ _ SY) as AB. cbn [cells_size csize Nat.add] in AB.
pose proof (u8arr_bound _ _ _ _ ARR) as DB.
pose proof (rw_cells_bound _ _ _ _ FR0) as FB. cbn [cells_size csize Nat.add app length] in FB.
pose proof (rw_cells_bound _ _ _ _ OG) as GB. cbn [cells_size csize Nat.add] in GB.
unfold sync_cells, wz in SY. cbn [sy_data sy_buf sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes] in SY.

ostep. rewrite sx32_lit by (unfold int31; lia). ostep. rewrite sx32_lit by (unfold int31; lia).
ostep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia; [exfalso; lia|].

ostep. ostep. ostep. ostep. ostep.

ostep. rewrite sx32_lit by (unfold int31; lia). ostep. rewrite swrap32_small by lia. ostep. ostep. ostep.

match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (rw_cells_merge bsegs mx A [C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 (sy_storage sy)); C4 (Z_to_bv 64 fill); C4 (Z_to_bv 64 (ret + (bb + hb))); C4 (Z_to_bv 64 0)]
[C4 (Z_to_bv 64 hb); C4 (Z_to_bv 64 bb)] [] SY) as SY2 end.
clear SY. cbn [cells_size csize cells_bytes cbytes app Nat.add] in SY2.
lstep.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (recell_zero8 mx A [C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 (sy_storage sy)); C4 (Z_to_bv 64 fill); C4 (Z_to_bv 64 (ret + (bb + hb))); C4 (Z_to_bv 64 0)] [] SY2) as SY end.
clear SY2. cbn [app] in SY. unfold wz in SY. replace (ret + (bb + hb)) with (ret + (hb + bb)) in SY by lia.
pose proof (frame_join _ _ _ _ _ _ FR0 PG FR) as FR2. clear FR0 PG FR.
match type of FR2 with rw_cells _ _ _ (?loc ++ _) =>
eapply (ps_epilogue _ loc); [reflexivity| exact FR2| exact ST| exact MU| exact WM| exact MI| | | exact ARR| | unfold wz; f_equal; lia] end.
+ unfold sync_cells, wz. cbn [sy_data sy_buf sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes]. exact SY.
+ unfold sync_fields_ok, int31; cbn. lia.
+ cbn [og_cells]. unfold page_cells, wz. cbn [pg_hdr pg_header_len pg_body_len]. exact OG.
Qed.

Lemma ps_restore : forall m (j8 j4 : list byte) (hb bb c0 c1 c2 c3 : Z) (L : list byte) r (sy' : sync_st bptr)
(x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
let ret := sy_returned sy in let fill := sy_fill sy in let buf := sy_buf sy in
let nseg := znth buf (ret + 26) in
let sy1 := mkSync (sy_data sy) buf (sy_storage sy) fill ret (sy_unsynced sy) hb bb in
let chk := Z.lor (Z.lor (Z.shiftl c3 24) (Z.shiftl c2 16)) (Z.lor (Z.shiftl c1 8) c0) in
hb = 27 + nseg -> ret + hb + bb <= fill -> 0 <= bb <= 255 * 255 ->
0 <= c0 < 256 -> 0 <= c1 < 256 -> 0 <= c2 < 256 -> 0 <= c3 < 256 ->
length L = length bytes -> upd_bytes L (Z.to_nat (ret + 22)) [Z_to_bv 8 c0; Z_to_bv 8 c1; Z_to_bv 8 c2; Z_to_bv 8 c3] = bytes ->
rw_cells bsegs m (bv_unsigned sp + -96) [CB 8 j8] ->
rw_cells bsegs m (bv_unsigned sp + -88) [C8 (Z_to_bv 64 (D + ret)); C4 (Z_to_bv 64 hb); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (D + ret + hb)); C4 (Z_to_bv 64 bb); C4 (Z_to_bv 64 0)] ->
rw_cells bsegs m (bv_unsigned sp + -56) [CB 4 j4; C4 (Z_to_bv 64 chk); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk bsegs m lo (bv_unsigned sp + -96) ->
munch W m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
rw_cells bsegs m A (sync_cells D sy1) ->
u8arr bsegs m D L -> rw_cells bsegs m G ogc ->
sync_fail sy1 ret (fill - ret) = ((r, None), sy') ->
evt bsegs (POST r None sy')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 G)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (D + sy_returned sy)) (Z_to_bv 64 (sy_fill sy - sy_returned sy)) (Z_to_bv 64 chk)
s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xc18a8) fc None m (seg_rom bsegs)).
Proof.
intros until x31. intros ret fill buf nseg sy1 chk Hhb Hfit Hbbr Hc0 Hc1 Hc2 Hc3 HL EL FR0 PG FR ST MU WM MI SY ARR OG RES.
unfold sy1 in *. clear sy1. unfold chk in *. clear chk.
pose proof FOK as sfP_; first [ sf_destruct 6%nat sfP_ as Fs Ff Fr Fu Fh Fbb | sf_fb; destruct sfP_ as (Fs & Ff & Fr & Fu & Fh & Fbb) ]. unfold int31 in Fs, Ff, Fr, Fu, Fh, Fbb.
pose proof INV as [[I1 [I2 [I3 [I4 Ibok]]]] _]. unfold zlength in I2. pose proof PRE as [_ PRE2].
fold ret fill buf in Fr, Ff, I1, I2, Ibok, PRE2.
pose proof (znth_bytes_ok buf (ret + 26) Ibok) as Rnseg. fold nseg in Rnseg.
pose proof (rw_cells_bound _ _ _ _ SY) as AB. cbn [cells_size csize Nat.add] in AB.
pose proof (u8arr_bound _ _ _ _ ARR) as DB. rewrite HL in DB.
pose proof (rw_cells_bound _ _ _ _ FR0) as FB. cbn [cells_size csize Nat.add app length] in FB.
unfold sync_cells, wz in SY. cbn [sy_data sy_buf sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes] in SY.

ostep. ostep. ostep.
pose proof (u8arr_store_ok bsegs _ _ _ (ret + 22) (wa (D + ret + 22)) ARR ltac:(rewrite HL; lia) ltac:(f_equal; lia)) as SOK.
ostep. fold (chkword c0 c1 c2 c3). rewrite (chk_b0 c0 c1 c2 c3) by assumption. arr_store ARR (ret + 22) (Z_to_bv 8 c0).
pose proof (u8arr_store_ok bsegs _ _ _ (ret + 23) (wa (D + ret + 23)) ARR ltac:(rewrite ?upd_length, HL; lia) ltac:(f_equal; lia)) as SOK.
ostep. fold (chkword c0 c1 c2 c3). rewrite (chk_b1 c0 c1 c2 c3) by assumption. arr_store ARR (ret + 23) (Z_to_bv 8 c1).
pose proof (u8arr_store_ok bsegs _ _ _ (ret + 24) (wa (D + ret + 24)) ARR ltac:(rewrite ?upd_length, ?upd_length, HL; lia) ltac:(f_equal; lia)) as SOK.
ostep. fold (chkword c0 c1 c2 c3). rewrite (chk_b2 c0 c1 c2 c3) by assumption. arr_store ARR (ret + 24) (Z_to_bv 8 c2).
pose proof (u8arr_store_ok bsegs _ _ _ (ret + 25) (wa (D + ret + 25)) ARR ltac:(rewrite ?upd_length, ?upd_length, ?upd_length, HL; lia) ltac:(f_equal; lia)) as SOK.
ostep. fold (chkword c0 c1 c2 c3). rewrite (chk_b3 c0 c1 c2 c3) by assumption. arr_store ARR (ret + 25) (Z_to_bv 8 c3).

rewrite upd4_upd_bytes in ARR by (rewrite ?HL; lia). rewrite EL in ARR.

ostep. ostep.
pose proof (frame_join _ _ _ _ _ _ FR0 PG FR) as FR2. clear FR0 PG FR.
match type of FR2 with rw_cells _ _ _ (?loc ++ _) =>
eapply (ps_sync_fail _ loc (mkSync (sy_data sy) buf (sy_storage sy) fill ret (sy_unsynced sy) hb bb));
[reflexivity| exact FR2| exact ST| exact MU| exact WM| exact MI| exact SY| | exact ARR| exact OG| reflexivity| cbn; lia| cbn; fold buf; unfold zlength; lia| exact RES] end.
unfold sync_fields_ok, int31; cbn; lia.
Qed.

End PS.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments skipn {A} n l : simpl nomatch.
#[local] Arguments firstn {A} n l : simpl nomatch.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section PS.

Variables (A G D lo : Z) (bytes : list byte) (sy : sync_st bptr) (j0 j1 j2 j3 : list byte).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem).
Local Notation ogc := [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3].
Local Notation W := [(bv_unsigned sp - 128, bv_unsigned sp); (A, A + 32); (G, G + 32); (D, D + Z.of_nat (length bytes))].
Local Notation len := (Z.of_nat (length bytes)).
Hypothesis FOK : sync_fields_ok sy.
Hypothesis INV : sync_inv2 sy.
Hypothesis PRE : buf_pre (sy_buf sy) bytes.
Hypothesis LENB : len = sy_storage sy.
Hypothesis HD : 0 <= D. Hypothesis TOPD : D + len < 2^63.
Hypothesis HA : 0 < A. Hypothesis HG : 0 < G.
Hypothesis LO : lo + 128 <= bv_unsigned sp.

Hypothesis SEP_fA : A + 32 <= lo \/ bv_unsigned sp <= A.
Hypothesis SEP_fG : G + 32 <= lo \/ bv_unsigned sp <= G.
Hypothesis SEP_fD : D + len <= lo \/ bv_unsigned sp <= D.
Hypothesis SEP_AG : A + 32 <= G \/ G + 32 <= A.
Hypothesis SEP_AD : A + 32 <= D \/ D + len <= A.
Hypothesis SEP_GD : G + 32 <= D \/ D + len <= G.
#[local] Set Default Proof Using "FOK INV PRE LENB HD TOPD HA HG LO SEP_fA SEP_fG SEP_fD SEP_AG SEP_AD SEP_GD".

Notation POST0 := (pageseek_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A G D lo bytes ogc m0).
Notation POST := (pageseek_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A G D lo bytes ogc sy m0).

Notation FRAME m loc := (rw_cells asegs m (bv_unsigned sp + -96) (loc ++ [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).

Lemma ps_epilogue0 : forall m (loc : list cell) r ogo (sy' : sync_st bptr)
(x1 x5 x6 x7 x8 x9 va0 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word),
cells_size loc = 48%nat ->
FRAME m loc -> stk asegs m lo (bv_unsigned sp + -96) ->
munch W m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
rw_cells asegs m A (sync_cells D sy') -> sync_fields_ok sy' -> u8arr asegs m D bytes ->
rw_cells asegs m G (og_cells D ogo ogc) ->
va0 = wz r ->
evt asegs (POST0 r ogo sy')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 x8 x9 va0 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xb9248) fc None m (seg_rom asegs)).
Proof.
intros until x31. intros SZ FR ST MU WM MI SY FOK' ARR OG ->. unfold wz.
pose proof (rw_cells_bound _ _ _ _ FR) as FB. rewrite cells_size_app, SZ in FB. cbn [cells_size csize Nat.add] in FB.
apply rw_cells_app in FR. destruct FR as [FRl FR]. rewrite SZ in FR.
replace (bv_unsigned sp + -96 + Z.of_nat 48) with (bv_unsigned sp + -48) in FR by lia.
ostep. ostep. ostep. ostep. ostep. ostep. ostep.
replace (bv_unsigned sp + -48) with (bv_unsigned sp + -96 + Z.of_nat (cells_size loc)) in FR by lia.
pose proof (rw_cells_join _ _ _ _ _ FRl FR) as FR2. clear FRl FR.
pose proof (stk_release _ _ _ _ _ ST FR2 ltac:(lia)) as ST2. clear ST FR2.
rewrite cells_size_app, SZ in ST2. cbn [cells_size csize Nat.add] in ST2.
replace (bv_unsigned sp + -96 + Z.of_nat 96) with (bv_unsigned sp) in ST2 by lia.
ostep. finish.
Qed.

Lemma ps_epilogue : forall m (loc : list cell) r ogo (sy' : sync_st bptr)
(x1 x5 x6 x7 x8 x9 va0 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word),
cells_size loc = 48%nat ->
FRAME m loc -> stk asegs m lo (bv_unsigned sp + -96) ->
munch W m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
rw_cells asegs m A (sync_cells D sy') -> sync_fields_ok sy' -> u8arr asegs m D bytes ->
rw_cells asegs m G (og_cells D ogo ogc) ->
va0 = wz r ->
evt asegs (POST r ogo sy')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 x8 x9 va0 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xb9248) fc None m (seg_rom asegs)).
Proof.
intros. eapply evt_mono; [eapply ps_epilogue0; eassumption|]. intros ms' X. left. exact X.
Qed.

Lemma ps_ret0 : forall m (loc : list cell) (sy1 : sync_st bptr)
(x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word),
cells_size loc = 48%nat ->
FRAME m loc -> stk asegs m lo (bv_unsigned sp + -96) ->
munch W m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
rw_cells asegs m A (sync_cells D sy1) -> sync_fields_ok sy1 -> u8arr asegs m D bytes ->
rw_cells asegs m G ogc ->
evt asegs (POST 0 None sy1)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xb91a4) fc None m (seg_rom asegs)).
Proof.
intros until x31. intros SZ FR ST MU WM MI SY FOK' ARR OG.
ostep. ostep. eapply ps_epilogue; try eassumption. reflexivity.
Qed.

Lemma ps_sync_fail : forall m (loc : list cell) (sy1 : sync_st bptr) r (sy' : sync_st bptr)
(x1 x5 x6 x7 va0 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
cells_size loc = 48%nat ->
FRAME m loc -> stk asegs m lo (bv_unsigned sp + -96) ->
munch W m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
rw_cells asegs m A (sync_cells D sy1) -> sync_fields_ok sy1 -> u8arr asegs m D bytes ->
rw_cells asegs m G ogc ->
sy_buf sy1 = sy_buf sy ->
1 <= sy_fill sy1 - sy_returned sy1 -> sy_fill sy1 <= zlength (sy_buf sy) ->
sync_fail sy1 (sy_returned sy1) (sy_fill sy1 - sy_returned sy1) = ((r, None), sy') ->
evt asegs (POST r None sy')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 G) va0 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (D + sy_returned sy1)) (Z_to_bv 64 (sy_fill sy1 - sy_returned sy1)) (Z_to_bv 64 D) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xb91e0) fc None m (seg_rom asegs)).
Proof.
intros until x31. intros SZ FR ST MU WM MI SY FOK1 ARR OG EB Hb Hf RES.
pose proof FOK1 as (Fs & Ff & Fr & Fu & Fh & Fbb). unfold int31 in Fs, Ff, Fr, Fu, Fh, Fbb.
pose proof PRE as [PRE1 PRE2]. unfold zlength in *.
pose proof (rw_cells_bound _ _ _ _ SY) as AB. cbn [cells_size csize Nat.add] in AB.
pose proof (u8arr_bound _ _ _ _ ARR) as DB.
pose proof (rw_cells_bound _ _ _ _ FR) as FB. rewrite cells_size_app, SZ in FB. cbn [cells_size csize Nat.add] in FB.

unfold sync_cells, wz in SY.
pose proof (rw_cells_merge asegs m A [C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 (sy_storage sy1)); C4 (Z_to_bv 64 (sy_fill sy1)); C4 (Z_to_bv 64 (sy_returned sy1)); C4 (Z_to_bv 64 (sy_unsynced sy1))]
[C4 (Z_to_bv 64 (sy_headerbytes sy1)); C4 (Z_to_bv 64 (sy_bodybytes sy1))] [] SY) as SY2. clear SY.
cbn [cells_size csize cells_bytes cbytes app Nat.add] in SY2.
lstep.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (recell_zero8 mx A [C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 (sy_storage sy1)); C4 (Z_to_bv 64 (sy_fill sy1)); C4 (Z_to_bv 64 (sy_returned sy1)); C4 (Z_to_bv 64 (sy_unsynced sy1))] [] SY2) as SY end.
clear SY2. cbn [app] in SY. unfold wz in SY.

ostep. ostep. ostep. ostep.
apply evt_done. right. split; [reflexivity|]. unfold pageseek_cut.
eexists _, loc, sy1. do 12 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact SZ|]. split; [exact FR|].
split; [exact SY|]. split; [exact FOK1|]. split; [exact ARR|]. split; [exact OG|]. split; [exact EB|]. split; [exact Hb|]. split; [exact Hf| exact RES].
Qed.

Lemma frame_join : forall m j8 j4 (hb bb chk : Z),
rw_cells asegs m (bv_unsigned sp + -96) [CB 8 j8] ->
rw_cells asegs m (bv_unsigned sp + -88) [C8 (Z_to_bv 64 (D + sy_returned sy)); C4 (Z_to_bv 64 hb); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (D + sy_returned sy + hb)); C4 (Z_to_bv 64 bb); C4 (Z_to_bv 64 0)] ->
rw_cells asegs m (bv_unsigned sp + -56) [CB 4 j4; C4 (Z_to_bv 64 chk); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
FRAME m [CB 8 j8; C8 (Z_to_bv 64 (D + sy_returned sy)); C4 (Z_to_bv 64 hb); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (D + sy_returned sy + hb)); C4 (Z_to_bv 64 bb); C4 (Z_to_bv 64 0); CB 4 j4; C4 (Z_to_bv 64 chk)].
Proof.
intros m j8 j4 hb bb chk FR0 PG FR.
replace (bv_unsigned sp + -88) with (bv_unsigned sp + -96 + Z.of_nat (cells_size [CB 8 j8])) in PG by (cbn; lia).
pose proof (rw_cells_join _ _ _ _ _ FR0 PG) as FR1.
replace (bv_unsigned sp + -56) with (bv_unsigned sp + -96 + Z.of_nat (cells_size ([CB 8 j8] ++ [C8 (Z_to_bv 64 (D + sy_returned sy)); C4 (Z_to_bv 64 hb); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (D + sy_returned sy + hb)); C4 (Z_to_bv 64 bb); C4 (Z_to_bv 64 0)]))) in FR by (cbn; lia).
pose proof (rw_cells_join _ _ _ _ _ FR1 FR) as FR2. cbn [app] in FR2. exact FR2.
Qed.

Lemma ps_deliver : forall m (j8 j4 : list byte) (hb bb chk : Z)
(x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
let ret := sy_returned sy in let fill := sy_fill sy in let buf := sy_buf sy in
let nseg := znth buf (ret + 26) in
hb = 27 + nseg -> ret + hb + bb <= fill -> 0 <= bb <= 255 * 255 ->
rw_cells asegs m (bv_unsigned sp + -96) [CB 8 j8] ->
rw_cells asegs m (bv_unsigned sp + -88) [C8 (Z_to_bv 64 (D + ret)); C4 (Z_to_bv 64 hb); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (D + ret + hb)); C4 (Z_to_bv 64 bb); C4 (Z_to_bv 64 0)] ->
rw_cells asegs m (bv_unsigned sp + -56) [CB 4 j4; C4 (Z_to_bv 64 chk); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk asegs m lo (bv_unsigned sp + -96) ->
munch W m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
rw_cells asegs m A (sync_cells D (mkSync (sy_data sy) buf (sy_storage sy) fill ret (sy_unsynced sy) hb bb)) ->
u8arr asegs m D bytes -> rw_cells asegs m G ogc ->
evt asegs (POST (hb + bb) (Some (mkPage ret hb bb)) (mkSync (sy_data sy) buf (sy_storage sy) fill (ret + (hb + bb)) 0 0 0))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 G)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (D + sy_returned sy)) (Z_to_bv 64 (sy_fill sy - sy_returned sy)) (Z_to_bv 64 chk)
s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xb9210) fc None m (seg_rom asegs)).
Proof.
intros until x31. intros ret fill buf nseg Hhb Hfit Hbbr FR0 PG FR ST MU WM MI SY ARR OG.
pose proof FOK as sfP_; first [ sf_destruct 6%nat sfP_ as Fs Ff Fr Fu Fh Fbb | sf_fb; destruct sfP_ as (Fs & Ff & Fr & Fu & Fh & Fbb) ]. unfold int31 in Fs, Ff, Fr, Fu, Fh, Fbb.
pose proof INV as [[I1 [I2 [I3 [I4 Ibok]]]] _]. unfold zlength in I2.
fold ret fill buf in Fr, Ff, I1, I2, Ibok.
pose proof (znth_bytes_ok buf (ret + 26) Ibok) as Rnseg. fold nseg in Rnseg.
pose proof (rw_cells_bound _ _ _ _ SY) as AB. cbn [cells_size csize Nat.add] in AB.
pose proof (u8arr_bound _ _ _ _ ARR) as DB.
pose proof (rw_cells_bound _ _ _ _ FR0) as FB. cbn [cells_size csize Nat.add app length] in FB.
pose proof (rw_cells_bound _ _ _ _ OG) as GB. cbn [cells_size csize Nat.add] in GB.
unfold sync_cells, wz in SY. cbn [sy_data sy_buf sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes] in SY.

ostep. rewrite sx32_lit by (unfold int31; lia). ostep. rewrite sx32_lit by (unfold int31; lia).
ostep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia; [exfalso; lia|].

ostep. ostep. ostep. ostep. ostep.

ostep. rewrite sx32_lit by (unfold int31; lia). ostep. rewrite swrap32_small by lia. ostep. ostep. ostep.

match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (rw_cells_merge asegs mx A [C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 (sy_storage sy)); C4 (Z_to_bv 64 fill); C4 (Z_to_bv 64 (ret + (bb + hb))); C4 (Z_to_bv 64 0)]
[C4 (Z_to_bv 64 hb); C4 (Z_to_bv 64 bb)] [] SY) as SY2 end.
clear SY. cbn [cells_size csize cells_bytes cbytes app Nat.add] in SY2.
lstep.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (recell_zero8 mx A [C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 (sy_storage sy)); C4 (Z_to_bv 64 fill); C4 (Z_to_bv 64 (ret + (bb + hb))); C4 (Z_to_bv 64 0)] [] SY2) as SY end.
clear SY2. cbn [app] in SY. unfold wz in SY. replace (ret + (bb + hb)) with (ret + (hb + bb)) in SY by lia.
pose proof (frame_join _ _ _ _ _ _ FR0 PG FR) as FR2. clear FR0 PG FR.
match type of FR2 with rw_cells _ _ _ (?loc ++ _) =>
eapply (ps_epilogue _ loc); [reflexivity| exact FR2| exact ST| exact MU| exact WM| exact MI| | | exact ARR| | unfold wz; f_equal; lia] end.
+ unfold sync_cells, wz. cbn [sy_data sy_buf sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes]. exact SY.
+ unfold sync_fields_ok, int31; cbn. lia.
+ cbn [og_cells]. unfold page_cells, wz. cbn [pg_hdr pg_header_len pg_body_len]. exact OG.
Qed.

Lemma ps_restore : forall m (j8 j4 : list byte) (hb bb c0 c1 c2 c3 : Z) (L : list byte) r (sy' : sync_st bptr)
(x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
let ret := sy_returned sy in let fill := sy_fill sy in let buf := sy_buf sy in
let nseg := znth buf (ret + 26) in
let sy1 := mkSync (sy_data sy) buf (sy_storage sy) fill ret (sy_unsynced sy) hb bb in
let chk := Z.lor (Z.lor (Z.shiftl c3 24) (Z.shiftl c2 16)) (Z.lor (Z.shiftl c1 8) c0) in
hb = 27 + nseg -> ret + hb + bb <= fill -> 0 <= bb <= 255 * 255 ->
0 <= c0 < 256 -> 0 <= c1 < 256 -> 0 <= c2 < 256 -> 0 <= c3 < 256 ->
length L = length bytes -> upd_bytes L (Z.to_nat (ret + 22)) [Z_to_bv 8 c0; Z_to_bv 8 c1; Z_to_bv 8 c2; Z_to_bv 8 c3] = bytes ->
rw_cells asegs m (bv_unsigned sp + -96) [CB 8 j8] ->
rw_cells asegs m (bv_unsigned sp + -88) [C8 (Z_to_bv 64 (D + ret)); C4 (Z_to_bv 64 hb); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (D + ret + hb)); C4 (Z_to_bv 64 bb); C4 (Z_to_bv 64 0)] ->
rw_cells asegs m (bv_unsigned sp + -56) [CB 4 j4; C4 (Z_to_bv 64 chk); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk asegs m lo (bv_unsigned sp + -96) ->
munch W m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
rw_cells asegs m A (sync_cells D sy1) ->
u8arr asegs m D L -> rw_cells asegs m G ogc ->
sync_fail sy1 ret (fill - ret) = ((r, None), sy') ->
evt asegs (POST r None sy')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 G)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (D + sy_returned sy)) (Z_to_bv 64 (sy_fill sy - sy_returned sy)) (Z_to_bv 64 chk)
s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xb9178) fc None m (seg_rom asegs)).
Proof.
intros until x31. intros ret fill buf nseg sy1 chk Hhb Hfit Hbbr Hc0 Hc1 Hc2 Hc3 HL EL FR0 PG FR ST MU WM MI SY ARR OG RES.
unfold sy1 in *. clear sy1. unfold chk in *. clear chk.
pose proof FOK as sfP_; first [ sf_destruct 6%nat sfP_ as Fs Ff Fr Fu Fh Fbb | sf_fb; destruct sfP_ as (Fs & Ff & Fr & Fu & Fh & Fbb) ]. unfold int31 in Fs, Ff, Fr, Fu, Fh, Fbb.
pose proof INV as [[I1 [I2 [I3 [I4 Ibok]]]] _]. unfold zlength in I2. pose proof PRE as [_ PRE2].
fold ret fill buf in Fr, Ff, I1, I2, Ibok, PRE2.
pose proof (znth_bytes_ok buf (ret + 26) Ibok) as Rnseg. fold nseg in Rnseg.
pose proof (rw_cells_bound _ _ _ _ SY) as AB. cbn [cells_size csize Nat.add] in AB.
pose proof (u8arr_bound _ _ _ _ ARR) as DB. rewrite HL in DB.
pose proof (rw_cells_bound _ _ _ _ FR0) as FB. cbn [cells_size csize Nat.add app length] in FB.
unfold sync_cells, wz in SY. cbn [sy_data sy_buf sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes] in SY.

ostep. ostep. ostep.
pose proof (u8arr_store_ok asegs _ _ _ (ret + 22) (wa (D + ret + 22)) ARR ltac:(rewrite HL; lia) ltac:(f_equal; lia)) as SOK.
ostep. fold (chkword c0 c1 c2 c3). rewrite (chk_b0 c0 c1 c2 c3) by assumption. arr_store ARR (ret + 22) (Z_to_bv 8 c0).
pose proof (u8arr_store_ok asegs _ _ _ (ret + 23) (wa (D + ret + 23)) ARR ltac:(rewrite ?upd_length, HL; lia) ltac:(f_equal; lia)) as SOK.
ostep. fold (chkword c0 c1 c2 c3). rewrite (chk_b1 c0 c1 c2 c3) by assumption. arr_store ARR (ret + 23) (Z_to_bv 8 c1).
pose proof (u8arr_store_ok asegs _ _ _ (ret + 24) (wa (D + ret + 24)) ARR ltac:(rewrite ?upd_length, ?upd_length, HL; lia) ltac:(f_equal; lia)) as SOK.
ostep. fold (chkword c0 c1 c2 c3). rewrite (chk_b2 c0 c1 c2 c3) by assumption. arr_store ARR (ret + 24) (Z_to_bv 8 c2).
pose proof (u8arr_store_ok asegs _ _ _ (ret + 25) (wa (D + ret + 25)) ARR ltac:(rewrite ?upd_length, ?upd_length, ?upd_length, HL; lia) ltac:(f_equal; lia)) as SOK.
ostep. fold (chkword c0 c1 c2 c3). rewrite (chk_b3 c0 c1 c2 c3) by assumption. arr_store ARR (ret + 25) (Z_to_bv 8 c3).

rewrite upd4_upd_bytes in ARR by (rewrite ?HL; lia). rewrite EL in ARR.

ostep. ostep.
pose proof (frame_join _ _ _ _ _ _ FR0 PG FR) as FR2. clear FR0 PG FR.
match type of FR2 with rw_cells _ _ _ (?loc ++ _) =>
eapply (ps_sync_fail _ loc (mkSync (sy_data sy) buf (sy_storage sy) fill ret (sy_unsynced sy) hb bb));
[reflexivity| exact FR2| exact ST| exact MU| exact WM| exact MI| exact SY| | exact ARR| exact OG| reflexivity| cbn; lia| cbn; fold buf; unfold zlength; lia| exact RES] end.
unfold sync_fields_ok, int31; cbn; lia.
Qed.

End PS.
