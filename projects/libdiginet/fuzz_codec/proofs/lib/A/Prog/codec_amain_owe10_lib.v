(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the run / keep / branch / leaf tactics, kept_run and same_io_wvb are the text of
   projects/reac-pw/fuzz_qdisc/proofs/lib/A/QPgSlots.v:123-188 (made there from proofs/libreac/fuzz_knock/lib/A/APgStep.v,
   origin/ossv/recipes 6ebe35ba632), the stack-slot write tactics that of QPgCheck.v:52-69, the entry regions those of
   QPgRt.v:61-65 / 193-243, the shadow entry that of proofs/libreac/fuzz_identity/lib/A/Prog/sb_dec.v:354-370
   (origin/ossv/recipes 4b6f0df50aa7), cw_U_sx32_eqb that of proofs/libreac/fuzz_knock/lib/A/APgStep.v:54-68
   (U_sx32_eqb, origin/ossv/recipes 4b6f0df50aa7), cw_join_win that of proofs/reac-pw/fuzz_qdisc/lib/A/QPgLoop0.v:169-196
   (ra_join_win, a working branch b0f706c04a19), cw_bcmp_at that of lib/Reusable/YCbq.v:2262-2310 (aj_bcmp_at) with
   the wrapper's same_but_materialized kept in its post, cw_st_ok_at that of lib/Reusable/YI04.v:342-356 (entry_st_ok_full)
   with the env apart from the registers, renamed with the prefix cw_ and moved to libdiginet/fuzz_codec's ASan
   build (image A); the leaf ends in lib/A/Prog/CPgBase.v's cdc_post, whose memory clause is CodecCJ's tcj_kept. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgWalk.v, with its module names changed; 414 of its 469 lines of code are new or changed and 578 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owel.v; 367 of its 431 lines of code are new or changed and 405 lines of the source are left out. *)
(* Lemmas of segment OWE10 (COUNTER, owe_pc 10 = 0x82618) of the image-A walk of LLVMFuzzerTestOneInput
   (lib/A/Prog/codec_amain_inv.v seg_owe 10): owe_spec of kind 10, the two branch tests the walk meets (b > 127,
   a byte of k.bytes with bit 7 set), the reading of a sign-extended 4-byte field back from its chunk, and the
   regions and atom facts of the walk's start state. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_agree.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CodecRo CodecGlobs CPgWalk.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv codec_amain_st codec_amain_lem codec_amain_owel.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_owex.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ================================ owe_spec of kind 10 ================================
   The three cases are lib/Prog/codec_main_owe10.v:30-50 of the plain walk (as released, commit
   8642eae46e87), restated for an option desk. *)
Lemma owe10_rng_b : forall d a b c delta bytes n, 0x7f < b -> fst (owe_spec 10 (Some d) a b c delta bytes n) = E_RANGE.
Proof.
intros d a b c delta bytes n H. unfold owe_spec. cbv beta iota zeta.
replace (0x7f <? b) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma owe10_rng_s : forall d a b c delta bytes n, seven_bit (firstn 8 bytes) = false ->
fst (owe_spec 10 (Some d) a b c delta bytes n) = E_RANGE.
Proof.
intros d a b c delta bytes n H. unfold owe_spec. cbv beta iota zeta.
rewrite H. cbn [negb]. rewrite orb_true_r. reflexivity.
Qed.
Lemma owe10_ok : forall d a b c delta bytes n, b <= 0x7f -> seven_bit (firstn 8 bytes) = true ->
owe_spec 10 (Some d) a b c delta bytes n =
(0, ([0xf0; 0x13; u8 (d_dev d); u8 0x30] ++ ([d_counter d; u8 b] ++ rev (firstn 8 bytes)) ++ [0xf7],
     KEY 6 (d_counter d), 1)).
Proof.
intros d a b c delta bytes n Hb H. unfold owe_spec. cbv beta iota zeta.
replace (0x7f <? b) with false by (symmetry; apply Z.ltb_ge; lia). rewrite H. cbn [negb orb]. reflexivity.
Qed.

(* bit 7 of a byte *)
Lemma o10_tb7 : forall x, 0 <= x < 256 -> Z.testbit x 7 = (127 <? x).
Proof.
intros x Hx. pose proof (Z.testbit_spec' x 7 ltac:(lia)) as T. change (2 ^ 7) with 128 in T.
destruct (Z.ltb_spec 127 x) as [H|H].
- assert (E1 : x / 128 = 1) by (symmetry; apply Z.div_unique with (x - 128); lia). rewrite E1 in T.
  destruct (Z.testbit x 7); cbn in T; [reflexivity | discriminate T].
- assert (E0 : x / 128 = 0) by (apply Z.div_small; lia). rewrite E0 in T.
  destruct (Z.testbit x 7); cbn in T; [discriminate T | reflexivity].
Qed.
(* seven_bit of the first 8 bytes: false when byte j < 8 has bit 7 set, true when none of them has *)
Lemma o10_sb_false : forall bytes j, length bytes = 24%nat -> Forall (fun x => 0 <= x < 256) bytes -> (j < 8)%nat ->
127 < nth j bytes 0 -> seven_bit (firstn 8 bytes) = false.
Proof.
intros bytes j HL HF Hj Hb. unfold seven_bit.
apply not_true_iff_false. intros HT. rewrite forallb_forall in HT.
assert (Hin : In (nth j bytes 0) (firstn 8 bytes)).
{ rewrite <- (firstn_skipn 8 bytes) in Hb. rewrite app_nth1 in Hb by (rewrite length_firstn; lia).
  pose proof (nth_In (firstn 8 bytes) 0 (n := j) ltac:(rewrite length_firstn; lia)) as Hn.
  rewrite <- (firstn_skipn 8 bytes) at 1. rewrite app_nth1 by (rewrite length_firstn; lia). exact Hn. }
pose proof (HT _ Hin) as H1.
assert (Hr : 0 <= nth j bytes 0 < 256).
{ rewrite Forall_forall in HF. apply HF. apply nth_In. lia. }
rewrite (o10_tb7 _ Hr) in H1. apply negb_true_iff, Z.ltb_ge in H1. lia.
Qed.
Lemma o10_sb_true : forall bytes, length bytes = 24%nat -> Forall (fun x => 0 <= x < 256) bytes ->
(forall j, (j < 8)%nat -> nth j bytes 0 <= 127) -> seven_bit (firstn 8 bytes) = true.
Proof.
intros bytes HL HF Hj. unfold seven_bit. apply forallb_forall. intros x Hx.
apply In_nth with (d := 0) in Hx as (j & Hjl & Hjx). rewrite length_firstn in Hjl.
rewrite <- Hjx. rewrite nth_firstn. rewrite (proj2 (Nat.ltb_lt j 8) ltac:(lia)).
assert (Hr : 0 <= nth j bytes 0 < 256) by (rewrite Forall_forall in HF; apply HF; apply nth_In; lia).
rewrite (o10_tb7 _ Hr). specialize (Hj j ltac:(lia)).
destruct (Z.ltb_spec 127 (nth j bytes 0)); [lia | reflexivity].
Qed.

(* ================================ the branch tests ================================ *)
Section a. Context {fx : YK11.FPState}.
(* 0x82620 bltu a1,a0 with a1 = 127, a0 = b (a [0, 255] atom): taken exactly when 127 < b *)
Lemma o10_br_b : forall E n b, ew E n = Z_to_bv 64 b -> 0 <= b < 256 ->
branch_taken BC_LTU (sv_denot E (SLit 127)) (sv_denot E (SOff n 0)) = (127 <? b).
Proof.
intros E n b Hn Hb. rewrite branch_ltu_U. rewrite (U_atom E n b Hn) by lia. rewrite U_lit by lia. reflexivity.
Qed.
(* 0x82630 `lb` of a byte v (a [0, 255] atom) then `bltz`: taken exactly when 127 < v *)
Lemma o10_br_sx8 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
branch_taken BC_LT (sv_denot E (SExt true 8 (SOff n 0))) (sv_denot E (SLit 0)) = (127 <? v).
Proof.
intros E n v Hn Hr.
change (branch_taken BC_LT (sv_denot E (SExt true 8 (SOff n 0))) (sv_denot E (SLit 0)))
  with (bv_swrap 64 (U E (SExt true 8 (SOff n 0))) <? bv_swrap 64 (U E (SLit 0))).
rewrite U_lit by lia.
rewrite U_SExt. cbv iota beta. rewrite (U_atom E n v Hn) by lia.
change (2 ^ Z.of_N 8) with 256. rewrite (Z.mod_small v 256) by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
unfold zcanon, M64.
destruct (Z.ltb_spec 127 v) as [Hl|Hl].
- replace ((v + 128) mod 256) with (v - 128) by (rewrite <- (Z.mod_add (v + 128) (-1) 256) by lia; rewrite Z.mod_small; lia).
  replace ((v - 128 - 128) mod 2 ^ 64) with (v - 256 + 2 ^ 64)
    by (rewrite <- (Z.mod_add (v - 128 - 128) 1 (2 ^ 64)) by lia; rewrite Z.mod_small; lia).
  replace ((v - 256 + 2 ^ 64 + 2 ^ 63) mod 2 ^ 64) with (v - 256 + 2 ^ 63)
    by (rewrite <- (Z.mod_add (v - 256 + 2 ^ 64 + 2 ^ 63) (-1) (2 ^ 64)) by lia; rewrite Z.mod_small; lia).
  rewrite (Z.mod_small (0 + 2 ^ 63)) by lia.
  apply Z.ltb_lt. lia.
- rewrite (Z.mod_small (v + 128) 256) by lia. replace (v + 128 - 128) with v by lia.
  rewrite (Z.mod_small v (2 ^ 64)) by lia. rewrite (Z.mod_small (v + 2 ^ 63)) by lia.
  rewrite (Z.mod_small (0 + 2 ^ 63)) by lia.
  apply Z.ltb_ge. lia.
Qed.
End a.

(* ================================ the walk's regions and atoms ================================
   Atoms of the start state (am_env's ys from 37): 37 = k.b, 38 .. 45 = k.bytes[0 .. 8), 46 .. 49 = the desk's
   dev, strips, chars, counter (k.desk + 8 .. + 11). Regions: k.b and k.bytes[0 .. 8) read-only (rk), want_rc
   (rc, 0), want_len / want_key / want_display (rf, 0), the desk's four bytes (rg); on the success path, after the
   test loop, want[0 .. 4) (rd), want[14] (re) and the payload pl on the machine stack at 174(sp1) (rh). *)
Definition o10_rk : YP09.region := am_frame_region 204 224 204 204
[YP09.mkChunk 204 (CVal 4 (SOff 37 0)); YP09.mkChunk 216 (CVal 1 (SOff 38 0)); YP09.mkChunk 217 (CVal 1 (SOff 39 0));
 YP09.mkChunk 218 (CVal 1 (SOff 40 0)); YP09.mkChunk 219 (CVal 1 (SOff 41 0)); YP09.mkChunk 220 (CVal 1 (SOff 42 0));
 YP09.mkChunk 221 (CVal 1 (SOff 43 0)); YP09.mkChunk 222 (CVal 1 (SOff 44 0)); YP09.mkChunk 223 (CVal 1 (SOff 45 0))].
Definition o10_rc : YP09.region := am_frame_region 316 320 316 320 [YP09.mkChunk 316 (CVal 4 (SLit 0))].
(* want_rc after the error path's `sw a0,140(s6)` with a0 = -11 *)
Definition o10_rc_err : YP09.region :=
am_frame_region 316 320 316 320 [YP09.mkChunk 316 (CVal 4 (SLit 18446744073709551605))].
Definition o10_rf : YP09.region := am_frame_region 344 360 344 360
[YP09.mkChunk 344 (CVal 8 (SLit 0)); YP09.mkChunk 352 (CVal 4 (SLit 0)); YP09.mkChunk 356 (CVal 4 (SLit 0))].
Definition o10_rg : YP09.region := owe_desk_region [SOff 46 0; SOff 47 0; SOff 48 0; SOff 49 0].
Definition o10_rd : YP09.region := am_frame_region 320 324 320 324 [].
Definition o10_re : YP09.region := am_frame_region 334 335 334 335 [].
Definition o10_rh : YP09.region := YP09.mkRegion (Some 2%nat) 174 184 174 184 [].
Definition o10_rs : smem := [o10_rk; o10_rc; o10_rf; o10_rg].
Definition o10_AF : list (nat * afact) :=
[(23%nat, mkAF 0x9d6a0 0x9d6c0 5); (37%nat, mkAF 0 255 0); (38%nat, mkAF 0 255 0); (39%nat, mkAF 0 255 0);
 (40%nat, mkAF 0 255 0); (41%nat, mkAF 0 255 0); (42%nat, mkAF 0 255 0); (43%nat, mkAF 0 255 0);
 (44%nat, mkAF 0 255 0); (45%nat, mkAF 0 255 0); (46%nat, mkAF 0 255 0); (47%nat, mkAF 0 255 0);
 (48%nat, mkAF 0 255 0); (49%nat, mkAF 0 255 0)].
Definition o10_SH : list shent := [owe_desk_SH; owe_SHk].
Definition o10_ys (k : kcallZ) (d : desk) : list Z :=
[kz_b k; nth 0 (kz_bytes k) 0; nth 1 (kz_bytes k) 0; nth 2 (kz_bytes k) 0; nth 3 (kz_bytes k) 0;
 nth 4 (kz_bytes k) 0; nth 5 (kz_bytes k) 0; nth 6 (kz_bytes k) 0; nth 7 (kz_bytes k) 0;
 d_dev d; d_strips d; d_chars d; d_counter d].

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
(* a window region of the side-stack frame (3, pos) with no chunk, in any AR state that holds the frame *)
Lemma o10_fwin_ok : forall E (W : world tfibsegs) mem ly S md pos lo hi wlo whi,
AR tfibsegs B ly S W mem md -> In (3, pos) (frames S) ->
bv_unsigned (ew E 33) = frame_addr ly 3 pos -> 0 <= lo -> lo <= wlo -> whi <= hi -> hi <= 512 ->
region_ok tfibsegs E (mrestrict (w_H W) mem) (am_frame_region lo hi wlo whi []).
Proof.
intros E W mem ly S md pos lo hi wlo whi HAR Hin H33 Hlo Hlw Hwh Hhi.
destruct (frames_bounds tfibsegs B LAWS ly S W mem md 3 pos HAR Hin) as (Hf4096 & Hfceil & _).
destruct (al_frames _ _ LAWS ly S W mem md 3 pos HAR Hin) as (_ & _ & Hpr & _).
pose proof asan_consts as (C1 & _).
change (fs_frame_bytes 3) with 512 in *.
unfold am_frame_region, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite H33.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable tfibsegs). exact (proj1 (Hpr (frame_addr ly 3 pos + o) ltac:(lia))).
Qed.
End w.
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* a window region on the machine stack (atom 2 = sp) with no chunk, over present bytes *)
Lemma o10_swin_ok : forall E (W : world tfibsegs) mem spv lo hi,
bv_unsigned (ew E 2) = spv -> (forall a, spv + lo <= a < spv + hi -> apresent (w_H W) mem a) ->
0 <= spv + lo -> spv + hi <= 2 ^ 64 -> lo <= hi ->
region_ok tfibsegs E (mrestrict (w_H W) mem) (YP09.mkRegion (Some 2%nat) lo hi lo hi []).
Proof.
intros E W mem spv lo hi H2 Hp Hlo Hhi Hlh. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite H2.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable tfibsegs). apply Hp. lia.
Qed.
End s.

(* ================================ the end of an error path at CHK ================================
   0x82730 li a0,-11; sw a0,140(s6); 0x82738 li s11,10: want_rc = -11, the other want fields still 0 (rc_err at
   index 6 and rf at index 7 of the final state: am_regs, then rk, rc, rf, rg). owe_chk_end with L = 0. *)
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis LAWS : AR_laws tfibsegs B.
Lemma o10_err_fin : forall g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys k d E ss regs3 mem3 md3,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kj ->
frames S2 = [(3, pos)] -> 0 <= kj <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
ops_at ops regs2 -> cur_at g sp1 c W2 mem2 -> k_at g pos k W2 mem2 -> rec_okZ k (Some d) ->
kz_rc k = fst (enc_kZ k (Some d)) ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem3 md3 kj ->
env_agree 37 (am_env g pos c regs2 ys) E ->
st_ok tfibsegs E ss (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 PC_CHK) mem3 (seg_rom tfibsegs))) ->
am_keep_ok (ss_regs ss) = true -> sr_get (ss_regs ss) 26%bv = SOff 26 0 ->
nth_error (ss_mem ss) 4 = Some am_cur_region ->
nth_error (ss_mem ss) 6 = Some o10_rc_err -> nth_error (ss_mem ss) 7 = Some o10_rf ->
(forall a, 0 <= a < 2 ^ 64 -> ~ owe_zone g pos sp1 0 a ->
 aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
fst (owe_kZ k (Some d)) = E_RANGE ->
SRr tfibsegs W2 (mkCfg (mkst regs3 (Z_to_bv 64 PC_CHK) mem3 (seg_rom tfibsegs)) md3)
  (inv_chk B MT K XM_LIB g pos sp1 ops).
Proof.
intros g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys k d E ss regs3 mem3 md3
  HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HJ3 HAE HS Hkeep H26 Hc4 Hc6 Hc7 KE Hwhy.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & _).
unfold AM_HI in Hchi. change (fs_frame_bytes 3) with 512 in Hfceil.
pose proof HAE as (HA & _).
assert (U33 : bv_unsigned (ew E 33) = FA g pos).
{ rewrite (HA 33%nat ltac:(lia)), (am_ew_F g pos c regs2 ys). apply unsigned_lit_small. lia. }
set (ms3 := mkst regs3 (Z_to_bv 64 PC_CHK) mem3 (seg_rom tfibsegs)) in HS.
pose proof (st_ok_region_nth E ss (restrict (w_H W2) ms3) 6 _ HS Hc6) as R6.
pose proof (st_ok_region_nth E ss (restrict (w_H W2) ms3) 7 _ HS Hc7) as R7.
cbn [ms3 restrict ms_mem] in R6, R7.
unfold o10_rc_err, am_frame_region in R6. unfold o10_rf, am_frame_region in R7.
apply (owe_chk_end B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys k (Some d) 0 mem3 regs3 md3 E ss
  (-11) [] 0 0 0 HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HJ3 HAE HS Hkeep H26 Hc4 eq_refl ltac:(cbn; lia) KE).
- pose proof (field_of_region_any E _ 33%nat (FA g pos) _ 316 320 316 320 316 4 (SLit 18446744073709551605) R6 U33
    ltac:(left; reflexivity) ltac:(lia)) as V.
  apply (owe_vm _ _ 4 _ _ V). vm_compute. reflexivity.
- apply garr8_nil.
- exact (field_of_region E _ 33%nat (FA g pos) _ 344 360 344 360 344 8 (SLit 0) 0 R7 U33
    ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(lia)).
- exact (field_of_region E _ 33%nat (FA g pos) _ 344 360 344 360 352 4 (SLit 0) 0 R7 U33
    ltac:(right; left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(lia)).
- exact (field_of_region E _ 33%nat (FA g pos) _ 344 360 344 360 356 4 (SLit 0) 0 R7 U33
    ltac:(right; right; left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(lia)).
- lia.
- lia.
- lia.
- lia.
- apply owe_want_ok_fail; [exact Hwhy | unfold E_RANGE; lia].
Qed.
End e.

(* ================================ the success path ================================
   pl, the payload at 174(sp1): [counter; b; bytes[7] .. bytes[0]]; the zones the runs write before the
   __asan_memcpy call (zs1: the cursor's window, pl, want_rc .. want[4), want[14], want_len .. want_display) and
   after it (zs2: the same without pl); the call itself writes want[4 .. 14) and the runtime's stack below sp1. *)
Definition o10_pl (k : kcallZ) (d : desk) : list Z :=
[d_counter d; kz_b k; nth 7 (kz_bytes k) 0; nth 6 (kz_bytes k) 0; nth 5 (kz_bytes k) 0; nth 4 (kz_bytes k) 0;
 nth 3 (kz_bytes k) 0; nth 2 (kz_bytes k) 0; nth 1 (kz_bytes k) 0; nth 0 (kz_bytes k) 0].
Definition o10_zs2 (g : ectx) (pos sp1 a : Z) : Prop :=
(sp1 + 152 <= a < sp1 + 168) \/ (FA g pos + 316 <= a < FA g pos + 324) \/ (FA g pos + 334 <= a < FA g pos + 335) \/
(FA g pos + 344 <= a < FA g pos + 360).
Definition o10_zs1 (g : ectx) (pos sp1 a : Z) : Prop := o10_zs2 g pos sp1 a \/ (sp1 + 174 <= a < sp1 + 184).

(* ---- the reads of the success path ---- *)
Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* a byte as aview gives it *)
Lemma o10_aview_vm1 : forall H (m : word -> option byte) a v,
val_mem tfibsegs (mrestrict H m) a 1 v -> 0 <= v < 256 -> aview tfibsegs H m a = Some v.
Proof.
intros H m a v Hv Hr. specialize (Hv 0%nat ltac:(lia)). rewrite Z.add_0_r in Hv.
unfold aview. rewrite Hv. cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned.
unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256. change (2 ^ (8 * Z.of_nat 1)) with 256.
change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. rewrite !(Z.mod_small v 256) by lia. reflexivity.
Qed.
(* k's 184 bytes are marked usable in any memory holding the frame's 56 shadow bytes of the loop body *)
Lemma o10_bs_k : forall (W : world tfibsegs) m F, F mod 64 = 0 ->
(forall i, 0 <= i < 56 -> aview tfibsegs (w_H W) m (shadow_addr F + i) = Some (nth (Z.to_nat i) (shm 0) 0)) ->
block_shadow (aview tfibsegs (w_H W) m) SHADOW_OFF (F + 176) 184.
Proof.
intros W m F HF64 HSH. pose proof amain_pure_sat as (_ & _ & _ & _ & _ & _ & _ & Hk23 & _).
apply am_block_shadow; [exact HF64 | lia | reflexivity | lia |].
intros i Hi. change ((184 + 7) / 8) with 23 in Hi. change (184 / 8) with 23. change (176 / 8) with 22.
rewrite (proj2 (Z.ltb_lt i 23) ltac:(lia)).
rewrite (HSH (22 + i) ltac:(lia)). f_equal. apply (Hk23 0 (Z.to_nat (22 + i))). lia.
Qed.
(* the shadow hull of want[4 .. 14) = [F + 324, F + 334): shadow bytes 40 .. 47 of the frame *)
Lemma o10_hull : forall (rd : Z -> option Z) F, F mod 64 = 0 -> 0 <= F ->
(forall i, 0 <= i < 56 -> rd (shadow_addr F + i) <> None) -> shadow_hull_vis rd (F + 324) 10.
Proof.
intros rd F H64 HF0 Hv. unfold shadow_hull_vis. intros s Hs.
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite H64, Z.add_0_r in DF.
set (q := F / 64) in *.
assert (D0 : F / 8 = 8 * q) by (symmetry; apply Z.div_unique with 0; lia).
assert (D1 : (F + 324) / 8 = 8 * q + 40) by (symmetry; apply Z.div_unique with 4; lia).
assert (D2 : (F + 324 + 10 - 1) / 8 = 8 * q + 41) by (symmetry; apply Z.div_unique with 5; lia).
unfold shadow_addr, SHADOW_OFF in *. rewrite D1, D2 in Hs.
replace (2147450880 + (8 * q + 40)) with ((268431365 + q) * 8) in Hs by lia.
replace (2147450880 + (8 * q + 41)) with ((268431365 + q) * 8 + 1) in Hs by lia.
rewrite Z.div_mul in Hs by lia.
replace ((((268431365 + q) * 8 + 1)) / 8) with (268431365 + q) in Hs by (apply Z.div_unique with 1; lia).
replace s with (2147450880 + F / 8 + (s - (2147450880 + F / 8))) by lia.
apply Hv. rewrite D0. lia.
Qed.
(* the key want_key = counter | 0x60000 *)
Lemma o10_key : forall pv dv d E n, pd_okA pv dv (Some d) -> ew E n = Z_to_bv 64 (d_counter d) ->
bv_unsigned (sv_denot E (SAlu ALU_OR (SOff n 0) (SLit 393216))) = KEY 6 (d_counter d).
Proof.
intros pv dv d E n Hpd Hn.
change (bv_unsigned (sv_denot E (SAlu ALU_OR (SOff n 0) (SLit 393216))))
  with (U E (SAlu ALU_OR (SOff n 0) (SLit 393216))).
destruct Hpd as [(_ & _ & Hd) | [(_ & _ & Hd) | (_ & _ & Hd)]];
  [discriminate Hd | injection Hd as Hd' | injection Hd as Hd']; subst d;
  rewrite U_SAlu, (U_atom E n _ Hn) by (cbn; lia); rewrite U_lit by lia; vm_compute; reflexivity.
Qed.
End m.

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis LAWS : AR_laws tfibsegs B.
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* the command owe() owes for kind 10 on success, as the walk writes it *)
Lemma o10_want_ok : forall k d, rec_okZ k (Some d) -> kz_kind k = 10 -> kz_b k <= 127 ->
(forall j, (j < 8)%nat -> nth j (kz_bytes k) 0 <= 127) ->
owe_want_okZ (owe_setZ k 0 (([0xf0; 0x13; d_dev d; 0x30] ++ o10_pl k d ++ [0xf7]) ++
  skipn (length ([0xf0; 0x13; d_dev d; 0x30] ++ o10_pl k d ++ [0xf7])) (kz_want k)) 15 (KEY 6 (d_counter d)) 1)
  (Some d).
Proof.
intros k d Hrec Hkind Hb Hby.
pose proof Hrec as (_ & Hpd & Hrdr & _).
destruct (pd_range_A _ _ _ Hpd) as (_ & _ & Rdev & _ & _ & Rctr).
destruct Hrdr as (_ & Rb & _ & _ & Rlen & Rby & _ & _ & Rb8 & _). specialize (Rb8 Hkind).
assert (Hsb : seven_bit (firstn 8 (kz_bytes k)) = true) by (apply o10_sb_true; assumption).
pose proof (owe10_ok d (kz_a k) (kz_b k) (kz_c k) (kz_delta k) (kz_bytes k) (kz_n k) Hb Hsb) as HO.
change (owe_spec 10 (Some d) (kz_a k) (kz_b k) (kz_c k) (kz_delta k) (kz_bytes k) (kz_n k)) with (owe_kZ (mkKcallZ 10
  (kz_p k) (kz_desk k) (kz_a k) (kz_b k) (kz_c k) (kz_delta k) (kz_bytes k) (kz_n k) (kz_rc k) (kz_before k)
  (kz_out k) (kz_want_rc k) (kz_want k) (kz_want_len k) (kz_want_key k) (kz_want_display k)) (Some d)) in HO.
assert (HK : owe_kZ k (Some d) = owe_kZ (mkKcallZ 10
  (kz_p k) (kz_desk k) (kz_a k) (kz_b k) (kz_c k) (kz_delta k) (kz_bytes k) (kz_n k) (kz_rc k) (kz_before k)
  (kz_out k) (kz_want_rc k) (kz_want k) (kz_want_len k) (kz_want_key k) (kz_want_display k)) (Some d))
  by (unfold owe_kZ; cbn [kz_kind kz_a kz_b kz_c kz_delta kz_bytes kz_n]; rewrite Hkind; reflexivity).
rewrite <- HK in HO.
set (bs' := [0xf0; 0x13; u8 (d_dev d); u8 0x30] ++ ([d_counter d; u8 (kz_b k)] ++ rev (firstn 8 (kz_bytes k))) ++ [0xf7])
  in HO.
assert (Lbs : length bs' = 15%nat)
  by (unfold bs'; rewrite !length_app, length_rev, length_firstn, Rlen; reflexivity).
replace 15 with (Z.of_nat (length bs')) by (rewrite Lbs; reflexivity).
apply owe_want_ok_succ; [exact HO|].
rewrite Lbs.
assert (EB : [0xf0; 0x13; d_dev d; 0x30] ++ o10_pl k d ++ [0xf7] = map u8 bs').
{ unfold bs', o10_pl. pose proof Rby as Rby'. rewrite Forall_forall in Rby'.
  assert (R : forall j, (j < 8)%nat -> 0 <= nth j (kz_bytes k) 0 < 256) by (intros j Hj; apply Rby'; apply nth_In; lia).
  remember (kz_bytes k) as bl eqn:Ebl. clear - Rlen R Rdev Rctr Rb Rb8.
  destruct bl as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|x7 rest]]]]]]]]; cbn [length] in Rlen; try discriminate Rlen.
  pose proof (R 0%nat ltac:(lia)) as R0. pose proof (R 1%nat ltac:(lia)) as R1. pose proof (R 2%nat ltac:(lia)) as R2.
  pose proof (R 3%nat ltac:(lia)) as R3. pose proof (R 4%nat ltac:(lia)) as R4. pose proof (R 5%nat ltac:(lia)) as R5.
  pose proof (R 6%nat ltac:(lia)) as R6. pose proof (R 7%nat ltac:(lia)) as R7.
  cbn [nth] in R0, R1, R2, R3, R4, R5, R6, R7.
  cbn [firstn rev app map nth]. rewrite ?firstn_O. cbn [firstn rev app map nth].
  unfold u8. repeat rewrite Z.mod_mod by lia. repeat rewrite (Z.mod_small _ 256) by lia.
  reflexivity. }
rewrite <- EB. rewrite firstn_app, firstn_all2 by (cbn; lia).
unfold o10_pl. cbn [length app Nat.sub firstn]. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma o10_ok_fin : forall g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys k d E ss memc mem3 memf regsf mdf,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kj ->
frames S2 = [(3, pos)] -> 0 <= kj <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
ops_at ops regs2 -> cur_at g sp1 c W2 mem2 -> k_at g pos k W2 mem2 -> rec_okZ k (Some d) ->
kz_rc k = fst (enc_kZ k (Some d)) -> kz_kind k = 10 ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 memf mdf kj ->
env_agree 37 (am_env g pos c regs2 ys) E ->
st_ok tfibsegs E ss (restrict (w_H W2) (mkst regsf (Z_to_bv 64 PC_CHK) memf (seg_rom tfibsegs))) ->
ss_pc ss = PC_CHK -> ss_resv ss = None ->
am_keep_ok (ss_regs ss) = true -> sr_get (ss_regs ss) 26%bv = SOff 26 0 -> In am_cur_region (ss_mem ss) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ o10_zs1 g pos sp1 a -> aview tfibsegs (w_H W2) memc a = aview tfibsegs (w_H W2) mem2 a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (FA g pos + 324 <= a < FA g pos + 324 + 10) -> ~ (sp1 - 4096 <= a < sp1) ->
 aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) memc a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ o10_zs2 g pos sp1 a -> aview tfibsegs (w_H W2) memf a = aview tfibsegs (w_H W2) mem3 a) ->
(forall i, 0 <= i < 10 -> aview tfibsegs (w_H W2) mem3 (FA g pos + 324 + i) = aview tfibsegs (w_H W2) memc (sp1 + 174 + i)) ->
(forall i, 0 <= i < 10 -> aview tfibsegs (w_H W2) memc (sp1 + 174 + i) = Some (nth (Z.to_nat i) (o10_pl k d) 0)) ->
val_mem tfibsegs (rd W2 memf) (FA g pos + 320) 2 5104 -> val_mem tfibsegs (rd W2 memf) (FA g pos + 322) 1 (d_dev d) ->
val_mem tfibsegs (rd W2 memf) (FA g pos + 323) 1 48 -> val_mem tfibsegs (rd W2 memf) (FA g pos + 334) 1 247 ->
val_mem tfibsegs (rd W2 memf) (FA g pos + 316) 4 0 -> val_mem tfibsegs (rd W2 memf) (FA g pos + 344) 8 15 ->
val_mem tfibsegs (rd W2 memf) (FA g pos + 352) 4 (KEY 6 (d_counter d)) ->
val_mem tfibsegs (rd W2 memf) (FA g pos + 356) 4 1 ->
kz_b k <= 127 -> (forall j, (j < 8)%nat -> nth j (kz_bytes k) 0 <= 127) ->
SRr tfibsegs W2 (mkCfg (mkst regsf (Z_to_bv 64 PC_CHK) memf (seg_rom tfibsegs)) mdf)
  (inv_chk B MT K XM_LIB g pos sp1 ops).
Proof.
intros g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys k d E ss memc mem3 memf regsf mdf
  HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc Hkind HJf HAE HS Hpc Hrv Hkeep H26 Hcr KE1 Hkp KE2 Hcp Hpl
  V320 V322 V323 V334 Vr Vl Vkey Vdp Hb Hby.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & _).
pose proof (owe_frame_app B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as Happ.
change (fs_frame_bytes 3) with 512 in Hfceil.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold AM_HI in *.
pose proof Hrec as (_ & Hpd & Hrdr & _).
destruct (pd_range_A _ _ _ Hpd) as (_ & _ & Rdev & _ & _ & Rctr).
destruct Hrdr as (_ & Rb & _ & _ & Rlen & Rby & _ & _ & Rb8 & _). specialize (Rb8 Hkind).
pose proof HC as HSH. do 43 (destruct HSH as (_ & HSH)). destruct HSH as (HSH & _).
assert (D8 : 0 <= FA g pos / 8 /\ 8 * (FA g pos / 8) <= FA g pos)
  by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
(* a byte off every zone of the segment's writes keeps its start value *)
assert (KK : forall a, 0 <= a < 2 ^ 64 -> ~ o10_zs1 g pos sp1 a -> ~ (FA g pos + 324 <= a < FA g pos + 334) ->
  ~ (sp1 - 4096 <= a < sp1) -> aview tfibsegs (w_H W2) memf a = aview tfibsegs (w_H W2) mem2 a).
{ intros a Ha H1 H2 H3. rewrite (KE2 a Ha ltac:(intros Hz; apply H1; left; exact Hz)).
  rewrite (Hkp a Ha ltac:(lia) H3). exact (KE1 a Ha H1). }
set (bs := [0xf0; 0x13; d_dev d; 0x30] ++ o10_pl k d ++ [0xf7]).
assert (Lbs : length bs = 15%nat) by reflexivity.
(* want[0 .. 15) in the final memory *)
assert (Gbs : garr8 tfibsegs (rd W2 memf) (FA g pos + 320) bs).
{ destruct (owe_split2 _ _ 5104 5104 V320 eq_refl ltac:(lia)) as (V0 & V1).
  assert (VP : forall i, 0 <= i < 10 -> val_mem tfibsegs (rd W2 memf) (FA g pos + 324 + i) 1 (nth (Z.to_nat i) (o10_pl k d) 0)).
  { intros i Hi. apply val_mem1_of_aviewA.
    rewrite (KE2 (FA g pos + 324 + i) ltac:(lia) ltac:(unfold o10_zs2; lia)), (Hcp i Hi). exact (Hpl i Hi). }
  intros j Hj. rewrite Lbs in Hj.
  assert (Ej : (j < 4 \/ 4 <= j < 14 \/ j = 14)%nat) by lia.
  destruct Ej as [Ej | [Ej | Ej]].
  - assert (E4 : (j = 0 \/ j = 1 \/ j = 2 \/ j = 3)%nat) by lia.
    destruct E4 as [-> | [-> | [-> | ->]]]; cbn [bs app nth].
    + change (Z.of_nat 0) with 0. rewrite Z.add_0_r. split; [exact V0 | lia].
    + change (Z.of_nat 1) with 1. split; [exact V1 | lia].
    + change (Z.of_nat 2) with 2. split; [replace (FA g pos + 320 + 2) with (FA g pos + 322) by lia; exact V322 | lia].
    + change (Z.of_nat 3) with 3. split; [replace (FA g pos + 320 + 3) with (FA g pos + 323) by lia; exact V323 | lia].
  - unfold bs. rewrite app_nth2 by (cbn; lia). cbn [length]. rewrite app_nth1 by (cbn; lia).
    pose proof (VP (Z.of_nat j - 4) ltac:(lia)) as V. replace (Z.to_nat (Z.of_nat j - 4)) with (j - 4)%nat in V by lia.
    replace (FA g pos + 320 + Z.of_nat j) with (FA g pos + 324 + (Z.of_nat j - 4)) by lia.
    split; [exact V|].
    assert (Ej4 : (j - 4 < 10)%nat) by lia.
    assert (BYR : forall jj, (jj < 8)%nat -> 0 <= nth jj (kz_bytes k) 0 < 256)
      by (intros jj Hjj; rewrite Forall_forall in Rby; apply Rby; apply nth_In; lia).
    unfold o10_pl.
    destruct (j - 4)%nat as [|[|[|[|[|[|[|[|[|[|?]]]]]]]]]]; cbn [nth];
    first [lia | apply (BYR 0%nat); lia | apply (BYR 1%nat); lia | apply (BYR 2%nat); lia | apply (BYR 3%nat); lia
          | apply (BYR 4%nat); lia | apply (BYR 5%nat); lia | apply (BYR 6%nat); lia | apply (BYR 7%nat); lia].
  - subst j. cbn [bs o10_pl app nth]. change (Z.of_nat 14) with 14.
    split; [replace (FA g pos + 320 + 14) with (FA g pos + 334) by lia; exact V334 | lia]. }
assert (HKEY : 0 <= KEY 6 (d_counter d) < 2 ^ 32).
{ destruct Hpd as [(_ & _ & Hd) | [(_ & _ & Hd) | (_ & _ & Hd)]];
  [discriminate Hd | injection Hd as Hd' | injection Hd as Hd'];
  subst d; split; first [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity. }
apply (owex_chk B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys
  (owe_setZ k 0 (bs ++ skipn (length bs) (kz_want k)) 15 (KEY 6 (d_counter d)) 1) (Some d) E ss
  (mkst regsf (Z_to_bv 64 PC_CHK) memf (seg_rom tfibsegs)) mdf HJf Hfr Hk Hmo HC Hops Hcur HAE HS Hpc Hrv).
- exact Hkeep.
- exact H26.
- exact Hcr.
- intros a Ha. unfold am_keepzone in Ha. cbn [ms_mem]. apply KK; [lia | unfold o10_zs1, o10_zs2; lia | lia | lia].
- intros i Hi. cbn [ms_mem]. rewrite KK; [exact (HSH i Hi) | unfold shadow_addr, SHADOW_OFF; lia
  | unfold o10_zs1, o10_zs2, shadow_addr, SHADOW_OFF; appn; lia | unfold shadow_addr, SHADOW_OFF; appn; lia
  | unfold shadow_addr, SHADOW_OFF; lia].
- cbn [ms_mem]. apply (owe_k_at_end g pos k W2 mem2 W2 memf 0 bs 15 (KEY 6 (d_counter d)) 1 Hkat ltac:(rewrite Lbs; lia)).
  + intros a Ha. rewrite Lbs in Ha. apply KK; [lia | unfold o10_zs1, o10_zs2; lia | lia | lia].
  + replace (FA g pos + 176 + 140) with (FA g pos + 316) by lia. exact Vr.
  + replace (FA g pos + 176 + 144) with (FA g pos + 320) by lia. exact Gbs.
  + replace (FA g pos + 176 + 168) with (FA g pos + 344) by lia. exact Vl.
  + replace (FA g pos + 176 + 176) with (FA g pos + 352) by lia. exact Vkey.
  + replace (FA g pos + 176 + 180) with (FA g pos + 356) by lia. exact Vdp.
  + lia.
  + lia.
  + exact HKEY.
  + lia.
- apply owe_setZ_rec. exact Hrec.
- destruct (owe_setZ_kz k (Some d) 0 (bs ++ skipn (length bs) (kz_want k)) 15 (KEY 6 (d_counter d)) 1) as (_ & E2 & E3).
  rewrite E2, E3. exact Hrc.
- exact (o10_want_ok k d Hrec Hkind Hb Hby).
Qed.
End f.
