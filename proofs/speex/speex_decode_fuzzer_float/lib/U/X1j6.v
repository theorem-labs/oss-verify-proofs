(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1cc X1bk X1bj X1cf X1bu.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1fc.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ik X1ii X1io.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1j8.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1rl X1nw X1qz X1r0 X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section PS.
Context {RCEIL : RunCeiling}.

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

Notation POST := (pageseek_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A G D lo bytes ogc m0).

Notation FRAME m loc := (rw_cells rsegs m (bv_unsigned sp + -96) (loc ++ [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).

Lemma ps_epilogue : forall m (loc : list cell) r ogo (sy' : sync_st bptr)
(x1 x5 x6 x7 x8 x9 va0 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word),
cells_size loc = 48%nat ->
FRAME m loc -> stk rsegs m lo (bv_unsigned sp + -96) ->
munch W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
rw_cells rsegs m A (sync_cells D sy') -> sync_fields_ok sy' -> u8arr rsegs m D bytes ->
rw_cells rsegs m G (og_cells D ogo ogc) ->
va0 = wz r ->
evt rsegs (POST r ogo sy')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 x8 x9 va0 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x30794) fc None m (seg_rom rsegs)).
Proof.
intros until x31. intros SZ FR ST MU WM MI SY FOK' ARR OG ->. unfold wz.
pose proof (rw_cells_bound _ _ _ _ FR) as FB. rewrite cells_size_app, SZ in FB. cbn [cells_size csize Nat.add] in FB.
apply rw_cells_app in FR. destruct FR as [FRl FR]. rewrite SZ in FR.
replace (bv_unsigned sp + -96 + Z.of_nat 48) with (bv_unsigned sp + -48) in FR by lia.
zstep. zstep. zstep. zstep. zstep. zstep. zstep.
replace (bv_unsigned sp + -48) with (bv_unsigned sp + -96 + Z.of_nat (cells_size loc)) in FR by lia.
pose proof (rw_cells_join _ _ _ _ _ FRl FR) as FR2. clear FRl FR.
pose proof (stk_release _ _ _ _ _ ST FR2 ltac:(lia)) as ST2. clear ST FR2.
rewrite cells_size_app, SZ in ST2. cbn [cells_size csize Nat.add] in ST2.
replace (bv_unsigned sp + -96 + Z.of_nat 96) with (bv_unsigned sp) in ST2 by lia.
zstep. finish.
Qed.

Lemma ps_ret0 : forall m (loc : list cell) (sy1 : sync_st bptr)
(x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word),
cells_size loc = 48%nat ->
FRAME m loc -> stk rsegs m lo (bv_unsigned sp + -96) ->
munch W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
rw_cells rsegs m A (sync_cells D sy1) -> sync_fields_ok sy1 -> u8arr rsegs m D bytes ->
rw_cells rsegs m G ogc ->
evt rsegs (POST 0 None sy1)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x306f0) fc None m (seg_rom rsegs)).
Proof.
intros until x31. intros SZ FR ST MU WM MI SY FOK' ARR OG.
zstep. zstep. eapply ps_epilogue; try eassumption. reflexivity.
Qed.

Lemma ps_sync_fail : forall m (loc : list cell) (sy1 : sync_st bptr) r (sy' : sync_st bptr)
(x1 x5 x6 x7 va0 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
cells_size loc = 48%nat ->
FRAME m loc -> stk rsegs m lo (bv_unsigned sp + -96) ->
munch W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
rw_cells rsegs m A (sync_cells D sy1) -> sync_fields_ok sy1 -> u8arr rsegs m D bytes ->
rw_cells rsegs m G ogc ->
sy_buf sy1 = sy_buf sy ->
1 <= sy_fill sy1 - sy_returned sy1 -> sy_fill sy1 <= zlength (sy_buf sy) ->
sync_fail sy1 (sy_returned sy1) (sy_fill sy1 - sy_returned sy1) = ((r, None), sy') ->
evt rsegs (POST r None sy')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 G) va0 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (D + sy_returned sy1)) (Z_to_bv 64 (sy_fill sy1 - sy_returned sy1)) (Z_to_bv 64 D) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x3072c) fc None m (seg_rom rsegs)).
Proof.
intros until x31. intros SZ FR ST MU WM MI SY FOK1 ARR OG EB Hb Hf RES.
pose proof FOK1 as sfP_; first [ sf_destruct 6%nat sfP_ as Fs Ff Fr Fu Fh Fbb | sf_fb; destruct sfP_ as (Fs & Ff & Fr & Fu & Fh & Fbb) ]. unfold int31 in Fs, Ff, Fr, Fu, Fh, Fbb.
pose proof PRE as [PRE1 PRE2]. unfold zlength in *.
set (ret := sy_returned sy1) in *. set (fill := sy_fill sy1) in *.
pose proof (rw_cells_bound _ _ _ _ SY) as AB. cbn [cells_size csize Nat.add] in AB.
pose proof (u8arr_bound _ _ _ _ ARR) as DB.
pose proof (rw_cells_bound _ _ _ _ FR) as FB. rewrite cells_size_app, SZ in FB. cbn [cells_size csize Nat.add] in FB.

unfold sync_cells, wz in SY.
pose proof (rw_cells_merge rsegs m A [C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 (sy_storage sy1)); C4 (Z_to_bv 64 fill); C4 (Z_to_bv 64 ret); C4 (Z_to_bv 64 (sy_unsynced sy1))]
[C4 (Z_to_bv 64 (sy_headerbytes sy1)); C4 (Z_to_bv 64 (sy_bodybytes sy1))] [] SY) as SY2. clear SY.
cbn [cells_size csize cells_bytes cbytes app Nat.add] in SY2.
lstep.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (recell_zero8 mx A [C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 (sy_storage sy1)); C4 (Z_to_bv 64 fill); C4 (Z_to_bv 64 ret); C4 (Z_to_bv 64 (sy_unsynced sy1))] [] SY2) as SY end.
clear SY2. cbn [app] in SY. unfold wz in SY.

pose proof (bytes_at_sub _ D bytes (Z.to_nat (ret + 1)) (Z.to_nat (fill - ret - 1)) (proj1 ARR) ltac:(lia)) as NX.
zstep. zstep. zstep. zstep.
call memchr_spec.
1:{ rewrite unsigned_lit by lia. replace (D + ret + 1) with (D + Z.of_nat (Z.to_nat (ret + 1))) by lia. exact NX. }
1:{ unfold memchr_ok. rewrite !unsigned_lit by lia. rewrite firstn_length_le by (rewrite skipn_length; lia).
destruct (X1rl.find_byte _ _); lia. }
1:{ exact MI. }
rename POST into NX2. change X1fc.rsegs with rsegs in NX2. change X1fc.rsegs with rsegs in MI0. clear NX.
rewrite !unsigned_lit in * by lia.

unfold sync_fail in RES. rewrite EB in RES.
rewrite (pre_zslice (sy_buf sy) bytes (ret + 1) (fill - ret - 1) PRE) in RES by lia.
rewrite find_byte_bridge in RES.
unfold memchr_res. rewrite firstn_firstn. replace (Z.to_nat (fill - ret + -1)) with (Z.to_nat (fill - ret - 1)) by lia. rewrite Nat.min_id.
change (79 mod 256) with CHAR_O.
destruct (X1rl.find_byte CHAR_O (firstn (Z.to_nat (fill - ret - 1)) (skipn (Z.to_nat (ret + 1)) bytes))) as [j|] eqn:FBt.
-
pose proof (find_byte_Some _ _ _ FBt) as (Hj & _ & _). rewrite firstn_length_le in Hj by (rewrite skipn_length; lia).
zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; [|exfalso; lia].
zstep. rewrite swrap32_small by lia. zstep. zstep. zstep.
injection RES as <- <-.
eapply ps_epilogue; [exact SZ| exact FR| exact ST| exact MU| exact WM| exact MI0| | | exact ARR| exact OG|].
+ match goal with |- rw_cells _ _ _ ?cs => replace cs with
[C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 (sy_storage sy1)); C4 (Z_to_bv 64 fill); C4 (Z_to_bv 64 (D + ret + 1 + Z.of_nat j - D));
C4 (Z_to_bv 64 (sy_unsynced sy1)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]; [exact SY|] end.
unfold sync_cells, wz; cbn. repeat f_equal. lia.
+ unfold sync_fields_ok, int31; cbn. lia.
+ cbn. unfold wz. f_equal. lia.
-
zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; [exfalso; lia|].
zstep. rewrite sx32_lit by (unfold int31; lia). zstep.
zstep. rewrite swrap32_small by lia. zstep. zstep. zstep.
injection RES as <- <-.
eapply ps_epilogue; [exact SZ| exact FR| exact ST| exact MU| exact WM| exact MI0| | | exact ARR| exact OG|].
+ match goal with |- rw_cells _ _ _ ?cs => replace cs with
[C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 (sy_storage sy1)); C4 (Z_to_bv 64 fill); C4 (Z_to_bv 64 (D + fill - D));
C4 (Z_to_bv 64 (sy_unsynced sy1)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]; [exact SY|] end.
unfold sync_cells, wz; cbn. repeat f_equal. lia.
+ unfold sync_fields_ok, int31; cbn. lia.
+ cbn. unfold wz. f_equal. lia.
Qed.

Lemma frame_join : forall m j8 j4 (hb bb chk : Z),
rw_cells rsegs m (bv_unsigned sp + -96) [CB 8 j8] ->
rw_cells rsegs m (bv_unsigned sp + -88) [C8 (Z_to_bv 64 (D + sy_returned sy)); C4 (Z_to_bv 64 hb); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (D + sy_returned sy + hb)); C4 (Z_to_bv 64 bb); C4 (Z_to_bv 64 0)] ->
rw_cells rsegs m (bv_unsigned sp + -56) [CB 4 j4; C4 (Z_to_bv 64 chk); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
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
rw_cells rsegs m (bv_unsigned sp + -96) [CB 8 j8] ->
rw_cells rsegs m (bv_unsigned sp + -88) [C8 (Z_to_bv 64 (D + ret)); C4 (Z_to_bv 64 hb); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (D + ret + hb)); C4 (Z_to_bv 64 bb); C4 (Z_to_bv 64 0)] ->
rw_cells rsegs m (bv_unsigned sp + -56) [CB 4 j4; C4 (Z_to_bv 64 chk); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk rsegs m lo (bv_unsigned sp + -96) ->
munch W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
rw_cells rsegs m A (sync_cells D (mkSync (sy_data sy) buf (sy_storage sy) fill ret (sy_unsynced sy) hb bb)) ->
u8arr rsegs m D bytes -> rw_cells rsegs m G ogc ->
evt rsegs (POST (hb + bb) (Some (mkPage ret hb bb)) (mkSync (sy_data sy) buf (sy_storage sy) fill (ret + (hb + bb)) 0 0 0))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 G)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (D + sy_returned sy)) (Z_to_bv 64 (sy_fill sy - sy_returned sy)) (Z_to_bv 64 chk)
s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x3075c) fc None m (seg_rom rsegs)).
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

zstep. rewrite sx32_lit by (unfold int31; lia). zstep. rewrite sx32_lit by (unfold int31; lia).
zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia; [exfalso; lia|].

zstep. zstep. zstep. zstep. zstep.

zstep. rewrite sx32_lit by (unfold int31; lia). zstep. rewrite swrap32_small by lia. zstep. zstep. zstep.

match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (rw_cells_merge rsegs mx A [C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 (sy_storage sy)); C4 (Z_to_bv 64 fill); C4 (Z_to_bv 64 (ret + (bb + hb))); C4 (Z_to_bv 64 0)]
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
rw_cells rsegs m (bv_unsigned sp + -96) [CB 8 j8] ->
rw_cells rsegs m (bv_unsigned sp + -88) [C8 (Z_to_bv 64 (D + ret)); C4 (Z_to_bv 64 hb); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (D + ret + hb)); C4 (Z_to_bv 64 bb); C4 (Z_to_bv 64 0)] ->
rw_cells rsegs m (bv_unsigned sp + -56) [CB 4 j4; C4 (Z_to_bv 64 chk); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk rsegs m lo (bv_unsigned sp + -96) ->
munch W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
rw_cells rsegs m A (sync_cells D sy1) ->
u8arr rsegs m D L -> rw_cells rsegs m G ogc ->
sync_fail sy1 ret (fill - ret) = ((r, None), sy') ->
evt rsegs (POST r None sy')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 G)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (D + sy_returned sy)) (Z_to_bv 64 (sy_fill sy - sy_returned sy)) (Z_to_bv 64 chk)
s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x306c4) fc None m (seg_rom rsegs)).
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

zstep. zstep. zstep.
pose proof (u8arr_store_ok rsegs _ _ _ (ret + 22) (wa (D + ret + 22)) ARR ltac:(rewrite HL; lia) ltac:(f_equal; lia)) as SOK.
zstep. rewrite (chk_b0 c0 c1 c2 c3) by assumption. arr_store ARR (ret + 22) (Z_to_bv 8 c0).
pose proof (u8arr_store_ok rsegs _ _ _ (ret + 23) (wa (D + ret + 23)) ARR ltac:(rewrite ?upd_length, HL; lia) ltac:(f_equal; lia)) as SOK.
zstep. rewrite (chk_b1 c0 c1 c2 c3) by assumption. arr_store ARR (ret + 23) (Z_to_bv 8 c1).
pose proof (u8arr_store_ok rsegs _ _ _ (ret + 24) (wa (D + ret + 24)) ARR ltac:(rewrite ?upd_length, ?upd_length, HL; lia) ltac:(f_equal; lia)) as SOK.
zstep. rewrite (chk_b2 c0 c1 c2 c3) by assumption. arr_store ARR (ret + 24) (Z_to_bv 8 c2).
pose proof (u8arr_store_ok rsegs _ _ _ (ret + 25) (wa (D + ret + 25)) ARR ltac:(rewrite ?upd_length, ?upd_length, ?upd_length, HL; lia) ltac:(f_equal; lia)) as SOK.
zstep. rewrite (chk_b3 c0 c1 c2 c3) by assumption. arr_store ARR (ret + 25) (Z_to_bv 8 c3).

rewrite upd4_upd_bytes in ARR by (rewrite ?HL; lia). rewrite EL in ARR.

zstep. zstep.
pose proof (frame_join _ _ _ _ _ _ FR0 PG FR) as FR2. clear FR0 PG FR.
match type of FR2 with rw_cells _ _ _ (?loc ++ _) =>
eapply (ps_sync_fail _ loc (mkSync (sy_data sy) buf (sy_storage sy) fill ret (sy_unsynced sy) hb bb));
[reflexivity| exact FR2| exact ST| exact MU| exact WM| exact MI| exact SY| | exact ARR| exact OG| reflexivity| cbn; lia| cbn; fold buf; unfold zlength; lia| exact RES] end.
unfold sync_fields_ok, int31; cbn; lia.
Qed.

End PS.
