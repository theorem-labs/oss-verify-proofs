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
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owel.v, with its module names changed; 578 of its 651 lines of code are new or changed and 396 lines of the source are left out. *)
(* Lemmas of segment OWE9 (SCRIBBLE, owe_pc 9 = 0x8230c) of the image-A walk of LLVMFuzzerTestOneInput
   (lib/A/Prog/codec_amain_inv.v seg_owe 9): owe_spec of kind 9, the seven-bit test of the desk's characters,
   the key, the payload pl at F + 32 with its two shadow bytes, the window regions the walk adds (the s3 spill
   slot, pl, pl's shadow bytes, the last want byte), and the end of the success path at CHK.
   seven_bit_firstn_false / seven_bit_firstn_true and testbit7 are lib/Prog/codec_main_owe910_lib.v:115-138 of
   this unit's plain walk, restated for a byte of the record. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CodecRo CodecGlobs CPgWalk CPgWalkFrame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv codec_amain_st codec_amain_lem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_owel codec_amain_owex.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ================================ owe()'s SCRIBBLE case ================================ *)
Lemma owe9_split : forall od a b c delta bytes n,
owe_spec 9 od a b c delta bytes n =
match od with
| None => (E_ARG, noc)
| Some d =>
  if (0x7f <? a) || negb (seven_bit (firstn (Z.to_nat (d_chars d)) bytes)) then (E_RANGE, noc)
  else let '(bs, dp) := owe_sx (d_dev d) 0x40 ([u8 a; 0] ++ firstn (Z.to_nat (d_chars d)) bytes) in
       (0, (bs, KEY 7 a, dp))
end.
Proof. intros od a b c delta bytes n. destruct od; reflexivity. Qed.

Lemma owe9_rng_a : forall d a b c delta bytes n, 0x7f < a ->
fst (owe_spec 9 (Some d) a b c delta bytes n) = E_RANGE.
Proof.
intros d a b c delta bytes n H. rewrite owe9_split.
rewrite (proj2 (Z.ltb_lt 127 a) ltac:(lia)). reflexivity.
Qed.

Lemma owe9_rng_s : forall d a b c delta bytes n,
seven_bit (firstn (Z.to_nat (d_chars d)) bytes) = false ->
fst (owe_spec 9 (Some d) a b c delta bytes n) = E_RANGE.
Proof.
intros d a b c delta bytes n H. rewrite owe9_split, H. cbn [negb].
rewrite orb_true_r. reflexivity.
Qed.

Lemma owe9_ok : forall d a b c delta bytes n, a <= 0x7f ->
seven_bit (firstn (Z.to_nat (d_chars d)) bytes) = true ->
owe_spec 9 (Some d) a b c delta bytes n =
(0, ([0xf0; 0x13; u8 (d_dev d); 0x40; u8 a; 0] ++ firstn (Z.to_nat (d_chars d)) bytes ++ [0xf7],
     KEY 7 a, 1)).
Proof.
intros d a b c delta bytes n Ha H. rewrite owe9_split, H.
rewrite (proj2 (Z.ltb_ge 127 a) ltac:(lia)). cbn [negb orb].
unfold owe_sx. cbv beta iota zeta.
change (u8 64) with 64. change ((64 =? 0x40) || (64 =? 0x30))%bool with true.
change (bit_or_0 true 1) with 1. cbn [app]. reflexivity.
Qed.

(* ================================ the seven-bit test ================================ *)
Lemma o9_tb7 : forall x, 0 <= x < 256 -> Z.testbit x 7 = (127 <? x).
Proof.
intros x Hx. destruct (Z.ltb_spec 127 x) as [H|H].
- apply Z.testbit_true; [lia|]. change (2 ^ 7) with 128.
  assert (E1 : x / 128 = 1).
  { assert (1 <= x / 128) by (apply Z.div_le_lower_bound; lia).
    assert (x / 128 < 2) by (apply Z.div_lt_upper_bound; lia). lia. }
  rewrite E1. reflexivity.
- apply Z.testbit_false; [lia|]. change (2 ^ 7) with 128.
  rewrite (Z.div_small x 128) by lia. reflexivity.
Qed.

Lemma o9_nth_firstn : forall (l : list Z) m j, (j < m)%nat -> nth j (firstn m l) 0 = nth j l 0.
Proof.
intros l m; revert l. induction m as [|m IH]; intros l j Hj; [lia|].
destruct l as [|x l]; [destruct j; reflexivity|].
destruct j as [|j]; cbn [firstn nth]; [reflexivity | apply IH; lia].
Qed.

Lemma o9_sb_false : forall bytes m j, (j < m)%nat -> (j < length bytes)%nat ->
0 <= nth j bytes 0 < 256 -> 127 < nth j bytes 0 -> seven_bit (firstn m bytes) = false.
Proof.
intros bytes m j Hjm Hjl Hr Hb. unfold seven_bit. apply not_true_iff_false. intros HT.
rewrite forallb_forall in HT.
assert (Hin : In (nth j (firstn m bytes) 0) (firstn m bytes))
  by (apply nth_In; rewrite length_firstn; lia).
pose proof (HT _ Hin) as H1. rewrite (o9_nth_firstn bytes m j Hjm) in H1.
rewrite (o9_tb7 _ Hr) in H1. apply negb_true_iff, Z.ltb_ge in H1. lia.
Qed.

Lemma o9_sb_true : forall bytes m, (m <= length bytes)%nat ->
(forall j, (j < m)%nat -> 0 <= nth j bytes 0 <= 127) -> seven_bit (firstn m bytes) = true.
Proof.
intros bytes m Hm H. unfold seven_bit. apply forallb_forall. intros x Hx.
apply In_nth with (d := 0) in Hx. destruct Hx as (j & Hjl & Hjx).
rewrite length_firstn in Hjl. rewrite <- Hjx, (o9_nth_firstn bytes m j ltac:(lia)).
pose proof (H j ltac:(lia)) as Hj.
rewrite (o9_tb7 (nth j bytes 0) ltac:(lia)). destruct (Z.ltb_spec 127 (nth j bytes 0)); [lia | reflexivity].
Qed.

(* 0x8287c `sb s8,0(s9)`: the low byte of the sign-extended a *)
Section sx. Context {fx : YK11.FPState}.
Lemma o9_sx_u8 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v <= 127 ->
bv_unsigned (sv_denot E (SExt true 32 (SOff n 0))) mod 256 = u8 v.
Proof.
intros E n v Hn Hv.
change (bv_unsigned (sv_denot E (SExt true 32 (SOff n 0)))) with (U E (SExt true 32 (SOff n 0))).
rewrite (owe_U_sx32 E n v Hn ltac:(lia)).
rewrite (proj2 (Z.ltb_lt v (2 ^ 31)) ltac:(lia)). reflexivity.
Qed.
End sx.

(* a region the state drops, and a two-byte chunk read back as its two bytes *)
Section dr. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma o9_drop : forall E ss ms rs,
st_ok tfibsegs E ss ms -> submem rs (ss_mem ss) -> regions_wf rs = true ->
st_ok tfibsegs E (mkSS (ss_pc ss) (ss_regs ss) rs (ss_resv ss) (ss_facts ss)) ms.
Proof. intros E ss ms rs H1 H2 H3. eapply st_ok_submem; eassumption. Qed.
Lemma o9_chunk_aview2 : forall E (W : world tfibsegs) mem r base off v,
region_ok tfibsegs E (mrestrict (w_H W) mem) r -> base_val E (YP09.r_base r) = base ->
In (YP09.mkChunk off (CVal 2 (SLit v))) (YP09.r_chunks r) -> 0 <= v < 2 ^ 16 ->
aview tfibsegs (w_H W) mem (base + off) = Some (v mod 256) /\
aview tfibsegs (w_H W) mem (base + off + 1) = Some (v / 256).
Proof.
intros E W mem r base off v HR Hb Hin Hv.
pose proof (YP09.region_ok_chunk tfibsegs E (mrestrict (w_H W) mem) r _ HR Hin) as Hck.
rewrite Hb in Hck.
pose proof (val_of_chunk_any tfibsegs E (mrestrict (w_H W) mem) base off 2 (SLit v) Hck
  ltac:(cbn; lia)) as HV.
change (2 ^ (8 * Z.of_N 2)) with 65536 in HV.
assert (Hd : (bv_unsigned (sv_denot E (SLit v)) mod 65536) mod 2 ^ 16 = v)
  by (cbn [sv_denot]; rewrite unsigned_lit_small by lia; change (2 ^ 16) with 65536;
      rewrite Z.mod_mod by lia; apply Z.mod_small; lia).
destruct (owe_split2 _ _ _ v HV Hd ltac:(lia)) as (V0 & V1). split.
- apply (aview_of_val_mem1 tfibsegs (w_H W) mem (base + off) _ V0).
  apply Z.mod_pos_bound. lia.
- apply (aview_of_val_mem1 tfibsegs (w_H W) mem (base + off + 1) _ V1).
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Lemma o9_garr_of_aview : forall H (m : word -> option byte) a l,
(forall j, (j < length l)%nat -> aview tfibsegs H m (a + Z.of_nat j) = Some (nth j l 0)) ->
Forall (fun x => 0 <= x < 256) l -> garr8 tfibsegs (mrestrict H m) a l.
Proof.
intros H m a l Hv Hr j Hj. split.
- apply val_mem1_of_aviewA. apply Hv. exact Hj.
- rewrite Forall_forall in Hr. apply Hr. apply nth_In. exact Hj.
Qed.
End dr.

(* a region the call keeps: a region with an empty write window gets one inside its extent, which is what
   CPgWalkIntr's kept-region premise asks for; it is a subregion of the one the state holds *)
Definition o9_fix_win (r : YP09.region) : YP09.region :=
if (YP09.r_whi r <=? YP09.r_wlo r)
then YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) (YP09.r_lo r) (YP09.r_lo r) (YP09.r_chunks r)
else r.
Definition o9_fix_wins (rs : smem) : smem := map o9_fix_win rs.
(* the same region with its write window closed, and the first two bytes of pl with theirs closed: both are
   subregions, so a call keeps them and their chunks stay readable after it *)
Definition o9_closew (r : YP09.region) : YP09.region :=
YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) (YP09.r_lo r) (YP09.r_lo r) (YP09.r_chunks r).
Definition o9_plo (r : YP09.region) : YP09.region :=
YP09.mkRegion (YP09.r_base r) 32 34 32 32 (filter (fun c => YP09.c_off c <? 34) (YP09.r_chunks r)).

(* a range whose shadow bytes are zero is addressable *)
Section rz. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma o9_ra_zero : forall (W : world tfibsegs) mem F lo hi,
F mod 64 = 0 -> 0 <= F -> 0 <= lo -> lo <= hi ->
(forall j, lo / 8 <= j <= (hi - 1) / 8 -> aview tfibsegs (w_H W) mem (shadow_addr F + j) = Some 0) ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF (F + lo) (hi - lo).
Proof.
intros W mem F lo hi H64 HF Hlo Hlh HZ x Hx.
assert (E8 : F / 8 = 8 * (F / 64))
  by (transitivity ((8 * (F / 64) * 8) / 8); [f_equal; pose proof (Z.div_mod F 64 ltac:(lia)); lia
      | apply Z.div_mul; lia]).
assert (Dm8 : F = 8 * (F / 8)) by (pose proof (Z.div_mod F 64 ltac:(lia)); lia).
exists 0. split; [|left; reflexivity].
assert (Ex : x / 8 = F / 8 + (x - F) / 8).
{ rewrite <- (Z.div_add_l (F / 8) 8 (x - F)) by lia. f_equal. lia. }
unfold shadow_of_addr. rewrite Ex.
replace (SHADOW_OFF + (F / 8 + (x - F) / 8)) with (shadow_addr F + (x - F) / 8)
  by (unfold shadow_addr; lia).
apply HZ. split; apply Z.div_le_mono; lia.
Qed.
End rz.
(* the engine's shadow entry for k's 184 bytes, from its shadow bytes in the memory the walk has reached *)
Section sk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma o9_shk : forall (W : world tfibsegs) mem E F,
F mod 64 = 0 -> 4096 <= F -> F + 512 <= 0x7fffff800000 -> in_app F 512 ->
(forall j, 22 <= j <= 44 -> aview tfibsegs (w_H W) mem (shadow_addr F + j) = Some 0) ->
ew E 33 = Z_to_bv 64 F -> ew E 32 = Z_to_bv 64 SB ->
shent_ok tfibsegs CW_Bx E (mrestrict (w_H W) mem) owe_SHk.
Proof.
intros W mem E F H64 H4096 Hceil Happ HZ E33 E32.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hra : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF (F + 176) 184).
{ replace 184 with (360 - 176) by lia.
  apply (o9_ra_zero W mem F 176 360); [exact H64 | lia | lia | lia |].
  intros j Hj. change (176 / 8) with 22 in Hj. change ((360 - 1) / 8) with 44 in Hj. apply HZ. lia. }
assert (Ham : amem_range (F + 176) 184) by (unfold in_app in Happ; appn; lia).
unfold owe_SHk. change 360 with (176 + 184).
apply (cw_shent_ra_off W mem E 33 F 176 184 Hra Ham); [lia | lia | lia | lia | exact E33 | exact E32].
Qed.
End sk.


(* a register the walk's state holds as an atom offset or a literal *)
Section gr. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma o9_getr_off : forall E ss (H : word -> bool) ms (r : bv 5) n o v,
st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n o ->
ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + o < 2 ^ 64 ->
getr (ms_regs ms) r = w64 (v + o).
Proof.
intros E ss H ms r n o v HS Hr Hn Hv Hvo.
rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr.
rewrite (am_den_off E n v o Hn Hv Hvo). reflexivity.
Qed.
Lemma o9_getr_off0 : forall E ss (H : word -> bool) ms (r : bv 5) n w,
st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> ew E n = w ->
getr (ms_regs ms) r = w.
Proof.
intros E ss H ms r n w HS Hr Hn.
rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr. cbn [sv_denot].
rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma o9_getr_lit : forall E ss (H : word -> bool) ms (r : bv 5) v,
st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SLit v -> 0 <= v < 2 ^ 64 ->
getr (ms_regs ms) r = w64 v.
Proof.
intros E ss H ms r v HS Hr Hv.
rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr. cbn [sv_denot].
unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
Qed.
End gr.

(* a region added to a state the walk has reached *)
Section ad. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma o9_add_region : forall E ss ms r,
st_ok tfibsegs E ss ms -> YP09.region_wf r = true -> region_ok tfibsegs E (ms_mem ms) r ->
all_disjoint E r (ss_mem ss) ->
st_ok tfibsegs E (mkSS (ss_pc ss) (ss_regs ss) (r :: ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof. intros E ss ms r H1 H2 H3 H4. eapply ast_ok_add_region; eassumption. Qed.
End ad.

(* 0x82354 `lb` of a byte v (a [0, 255] atom) then `bltz`: taken exactly when 127 < v *)
Section q. Context {fx : YK11.FPState}.
Lemma o9_br_sx8 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
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
- replace ((v + 128) mod 256) with (v - 128)
    by (rewrite <- (Z.mod_add (v + 128) (-1) 256) by lia; rewrite Z.mod_small; lia).
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
End q.

(* ================================ the key and the bytes ================================ *)
(* 0x82900 lui a0,0x70; 0x82904 or a0,s8,a0 *)
Lemma o9_key : forall a, 0 <= a <= 127 -> Z.lor a 458752 = KEY 7 a.
Proof.
intros a Ha. unfold KEY. change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia.
rewrite (Z.mod_small a) by lia. change (7 * 65536) with 458752. apply Z.lor_comm.
Qed.
Lemma o9_key_rng : forall a, 0 <= a <= 127 -> 0 <= KEY 7 a < 2 ^ 32.
Proof.
intros a Ha. rewrite <- o9_key by lia.
pose proof (lor_lt_pow2 a 458752 19 ltac:(lia) ltac:(lia)) as H.
pose proof (Z.lor_nonneg a 458752) as H2. lia.
Qed.
(* 0x82908 `sw a0,176(s6)`: the stored key *)
Section kd. Context {fx : YK11.FPState}.
Lemma o9_key_den : forall E n a, ew E n = Z_to_bv 64 a -> 0 <= a <= 127 ->
bv_unsigned (sv_denot E (SAlu ALU_OR (SExt true 32 (SOff n 0)) (SLit 458752))) = KEY 7 a.
Proof.
intros E n a Hn Ha.
change (bv_unsigned (sv_denot E (SAlu ALU_OR (SExt true 32 (SOff n 0)) (SLit 458752))))
  with (U E (SAlu ALU_OR (SExt true 32 (SOff n 0)) (SLit 458752))).
rewrite U_SAlu. cbn [zalu_raw].
rewrite (owe_U_sx32 E n a Hn ltac:(lia)), U_SLit.
rewrite (proj2 (Z.ltb_lt a (2 ^ 31)) ltac:(lia)).
change (zcanon 458752) with 458752.
rewrite (o9_key a Ha). apply zcanon_id. pose proof (o9_key_rng a Ha). unfold M64; lia.
Qed.
End kd.
Lemma o9_map_u8 : forall l, Forall (fun x => 0 <= x < 256) l -> map u8 l = l.
Proof.
intros l H. induction H as [|x l Hx Hl IH]; [reflexivity|].
cbn [map]. f_equal; [|exact IH]. unfold u8. apply Z.mod_small. exact Hx.
Qed.

(* ================================ the payload and its shadow ================================ *)
(* pl at F + 32, ten bytes: the shadow bytes 4 and 5 of the frame (00 02 after 0x82854 / 0x8285c) make the
   ten bytes addressable. *)
Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma o9_ra_pl : forall (W : world tfibsegs) mem F, F mod 64 = 0 -> 0 <= F ->
aview tfibsegs (w_H W) mem (shadow_addr F + 4) = Some 0 ->
aview tfibsegs (w_H W) mem (shadow_addr F + 5) = Some 2 ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF (F + 32) 10.
Proof.
intros W mem F H64 HF H4 H5 x Hx.
assert (Dm : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)); lia).
assert (D8 : F / 8 = 8 * (F / 64)).
{ transitivity ((8 * (F / 64) * 8) / 8); [f_equal; lia | apply Z.div_mul; lia]. }
assert (Dm8 : F = 8 * (F / 8)) by lia.
destruct (Z_lt_le_dec x (F + 40)) as [Hlt|Hge].
- exists 0. split; [|left; reflexivity].
  assert (Ex : x / 8 = F / 8 + 4).
  { replace x with ((F / 8 + 4) * 8 + (x - F - 32)) by lia.
    rewrite Z.div_add_l by lia. rewrite (Z.div_small (x - F - 32)) by lia. lia. }
  unfold shadow_of_addr. rewrite Ex. unfold shadow_addr in H4.
  replace (SHADOW_OFF + (F / 8 + 4)) with (SHADOW_OFF + F / 8 + 4) by lia. exact H4.
- exists 2. split.
  + assert (Ex : x / 8 = F / 8 + 5).
    { replace x with ((F / 8 + 5) * 8 + (x - F - 40)) by lia.
      rewrite Z.div_add_l by lia. rewrite (Z.div_small (x - F - 40)) by lia. lia. }
    unfold shadow_of_addr. rewrite Ex. unfold shadow_addr in H5.
    replace (SHADOW_OFF + (F / 8 + 5)) with (SHADOW_OFF + F / 8 + 5) by lia. exact H5.
  + right. split; [|lia].
    replace x with ((x - F - 40) + (F / 8 + 5) * 8) by lia.
    rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia.
Qed.
(* a one-byte chunk of a region, read back as the memory's byte *)
Lemma o9_chunk_aview : forall E (W : world tfibsegs) mem r base off e,
region_ok tfibsegs E (mrestrict (w_H W) mem) r -> base_val E (YP09.r_base r) = base ->
In (YP09.mkChunk off (CVal 1 e)) (YP09.r_chunks r) ->
aview tfibsegs (w_H W) mem (base + off) = Some (bv_unsigned (sv_denot E e) mod 256).
Proof.
intros E W mem r base off e HR Hb Hin.
pose proof (YP09.region_ok_chunk tfibsegs E (mrestrict (w_H W) mem) r _ HR Hin) as Hck.
rewrite Hb in Hck.
pose proof (val_of_chunk_any tfibsegs E (mrestrict (w_H W) mem) base off 1 e Hck ltac:(cbn; lia)) as HV.
change (2 ^ (8 * Z.of_N 1)) with 256 in HV.
apply (aview_of_val_mem1 tfibsegs (w_H W) mem (base + off) _); [exact HV|].
apply Z.mod_pos_bound. lia.
Qed.
End p.

(* ================================ the regions and atoms of the walk ================================
   Atoms of the start state (am_env's ys from 37): 37 = k.a, 38 .. 45 = k.bytes[0 .. 8). The desk's four bytes
   are literals (the walk is done once per desk). Regions: k.a and k.bytes[0 .. 8) read-only (rk), want_rc and
   want[0 .. 4) (rr), want_len / want_key / want_display (rf), the desk's four bytes (rg); the walk adds the
   s3 spill slot at 8(sp1) (rsp), the payload pl at F + 32 (rpl), the two shadow bytes of pl (rsh) and the
   last want byte (rb). *)
Definition o9_rk : YP09.region := am_frame_region 200 224 200 200
[YP09.mkChunk 200 (CVal 4 (SOff 37 0));
 YP09.mkChunk 216 (CVal 1 (SOff 38 0)); YP09.mkChunk 217 (CVal 1 (SOff 39 0));
 YP09.mkChunk 218 (CVal 1 (SOff 40 0)); YP09.mkChunk 219 (CVal 1 (SOff 41 0));
 YP09.mkChunk 220 (CVal 1 (SOff 42 0)); YP09.mkChunk 221 (CVal 1 (SOff 43 0));
 YP09.mkChunk 222 (CVal 1 (SOff 44 0)); YP09.mkChunk 223 (CVal 1 (SOff 45 0))].
Definition o9_rr : YP09.region := am_frame_region 316 320 316 320 [YP09.mkChunk 316 (CVal 4 (SLit 0))].
Definition o9_rf : YP09.region := am_frame_region 344 360 344 360
[YP09.mkChunk 344 (CVal 8 (SLit 0)); YP09.mkChunk 352 (CVal 4 (SLit 0)); YP09.mkChunk 356 (CVal 4 (SLit 0))].
Definition o9_rg (d : desk) : YP09.region :=
owe_desk_region [SLit (d_dev d); SLit (d_strips d); SLit (d_chars d); SLit (d_counter d)].
Definition o9_rs (d : desk) : smem := [o9_rk; o9_rr; o9_rf; o9_rg d].
Definition o9_rsp : YP09.region := YP09.mkRegion (Some 2%nat) 8 16 8 16 [].
Definition o9_rpl : YP09.region := am_frame_region 32 42 32 42 [].
Definition o9_rsh : YP09.region := YP09.mkRegion (Some 34%nat) 4 6 4 6 [].
Definition o9_rb (chars : Z) : YP09.region :=
am_frame_region (326 + chars) (327 + chars) (326 + chars) (327 + chars) [].
Definition o9_rw : YP09.region := am_frame_region 320 324 320 324 [].
Definition o9_AF : list (nat * afact) :=
[(23%nat, mkAF 0x9d6a0 0x9d6c0 5); (37%nat, mkAF 0 (2 ^ 32 - 1) 0);
 (38%nat, mkAF 0 255 0); (39%nat, mkAF 0 255 0); (40%nat, mkAF 0 255 0); (41%nat, mkAF 0 255 0);
 (42%nat, mkAF 0 255 0); (43%nat, mkAF 0 255 0); (44%nat, mkAF 0 255 0); (45%nat, mkAF 0 255 0)].
Definition o9_SH : list shent := [owe_desk_SH; owe_SHk].
Definition o9_ys (k : kcallZ) : list Z :=
[kz_a k; nth 0 (kz_bytes k) 0; nth 1 (kz_bytes k) 0; nth 2 (kz_bytes k) 0; nth 3 (kz_bytes k) 0;
 nth 4 (kz_bytes k) 0; nth 5 (kz_bytes k) 0; nth 6 (kz_bytes k) 0; nth 7 (kz_bytes k) 0].

(* the bytes owe() owes for SCRIBBLE, as the walk writes them *)
Definition o9_bs (d : desk) (k : kcallZ) : list Z :=
[0xf0; 0x13; u8 (d_dev d); 0x40; u8 (kz_a k); 0] ++ firstn (Z.to_nat (d_chars d)) (kz_bytes k) ++ [0xf7].

(* the bytes the walk writes once the payload is built: the s3 slot, the cursor's window (not changed),
   want_rc .. want[chars + 6] and want_len .. want_display; the payload itself is not among them *)
Definition o9_zc (g : ectx) (pos sp1 a : Z) : Prop :=
(sp1 + 8 <= a < sp1 + 16) \/ (sp1 + 152 <= a < sp1 + 168) \/
(FA g pos + 316 <= a < FA g pos + 335) \/ (FA g pos + 344 <= a < FA g pos + 360).
(* the bytes the walk writes after the second copy: the last want byte, want_len .. want_display, pl's two
   shadow bytes and the windows it does not write; want[4 .. chars + 6) is not among them *)
Definition o9_zd (g : ectx) (pos sp1 chars a : Z) : Prop :=
(sp1 + 8 <= a < sp1 + 16) \/ (sp1 + 152 <= a < sp1 + 168) \/
(FA g pos + 316 <= a < FA g pos + 324) \/ (FA g pos + 326 + chars <= a < FA g pos + 327 + chars) \/
(FA g pos + 344 <= a < FA g pos + 360) \/
(shadow_addr (FA g pos) + 4 <= a < shadow_addr (FA g pos) + 6).

(* the bytes the segment writes: the runtime's window and the s3 slot, pl, want_rc .. want[chars + 7),
   want_len .. want_display, the cursor's window (not changed) and pl's two shadow bytes *)
Definition o9_zone (g : ectx) (pos sp1 chars a : Z) : Prop :=
(sp1 - 4096 <= a < sp1 + 16) \/ (FA g pos + 32 <= a < FA g pos + 42) \/
(FA g pos + 316 <= a < FA g pos + 327 + chars) \/ (FA g pos + 344 <= a < FA g pos + 360) \/
(sp1 + 152 <= a < sp1 + 168) \/
(shadow_addr (FA g pos) + 4 <= a < shadow_addr (FA g pos) + 6).

(* the kept fact of the first phase, over the whole segment's zone *)
Section wd. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma o9_widen : forall (W : world tfibsegs) (m m2 : word -> option byte) g pos sp1 chars, 0 <= chars ->
(forall a, 0 <= a < 2 ^ 64 -> ~ owe_zone g pos sp1 0 a -> aview tfibsegs (w_H W) m a = aview tfibsegs (w_H W) m2 a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ o9_zone g pos sp1 chars a ->
aview tfibsegs (w_H W) m a = aview tfibsegs (w_H W) m2 a.
Proof.
intros W m m2 g pos sp1 chars Hc H a Ha Hz. apply H; [exact Ha|].
intros Hw. apply Hz. unfold o9_zone, owe_zone in *. lia.
Qed.
End wd.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.

(* a window of the walk's own frame, with no chunk, in the state the journal is at *)
Lemma o9_fwin_ok : forall E ly S (W : world tfibsegs) mem md pos lo hi wlo whi,
AR tfibsegs B ly S W mem md -> In (3, pos) (frames S) ->
bv_unsigned (ew E 33) = frame_addr ly 3 pos ->
0 <= lo -> lo <= wlo -> wlo <= whi -> whi <= hi -> hi <= 512 ->
region_ok tfibsegs E (mrestrict (w_H W) mem) (am_frame_region lo hi wlo whi []).
Proof.
intros E ly S W mem md pos lo hi wlo whi HAR Hin H33 Hlo Hlw Hwh Hwi Hhi.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds tfibsegs B LAWS ly S W mem md 3 pos HAR Hin) as (Hf4096 & Hfceil & _).
destruct (al_frames _ _ LAWS ly S W mem md 3 pos HAR Hin) as (_ & _ & Hpr & _).
change (fs_frame_bytes 3) with 512 in Hfceil, Hpr.
unfold am_frame_region, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite H33.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable tfibsegs).
exact (proj1 (Hpr (frame_addr ly 3 pos + o) ltac:(lia))).
Qed.

(* a window of the frame's shadow bytes, with no chunk *)
Lemma o9_shwin_ok : forall E ly S (W : world tfibsegs) mem md pos lo hi,
AR tfibsegs B ly S W mem md -> In (3, pos) (frames S) ->
bv_unsigned (ew E 34) = shadow_addr (frame_addr ly 3 pos) ->
0 <= lo -> lo <= hi -> hi <= 64 ->
region_ok tfibsegs E (mrestrict (w_H W) mem) (YP09.mkRegion (Some 34%nat) lo hi lo hi []).
Proof.
intros E ly S W mem md pos lo hi HAR Hin H34 Hlo Hlh Hhi.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds tfibsegs B LAWS ly S W mem md 3 pos HAR Hin) as (Hf4096 & Hfceil & _).
destruct (al_frames _ _ LAWS ly S W mem md 3 pos HAR Hin) as (_ & _ & _ & Hsh).
change (fs_frame_bytes 3) with 512 in Hfceil. change (fs_frame_bytes 3 / 8) with 64 in Hsh.
assert (Hd1 : 0 <= frame_addr ly 3 pos / 8 <= frame_addr ly 3 pos)
  by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite H34.
split; [unfold shadow_addr, SHADOW_OFF; lia|].
split; [unfold shadow_addr, SHADOW_OFF; lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable tfibsegs). apply Hsh. lia.
Qed.

(* a window on the machine stack, with no chunk *)
Lemma o9_swin_ok : forall E (W : world tfibsegs) mem spv lo hi,
bv_unsigned (ew E 2) = spv -> (forall a, spv + lo <= a < spv + hi -> apresent (w_H W) mem a) ->
0 <= spv + lo -> spv + hi <= 2 ^ 64 -> lo <= hi ->
region_ok tfibsegs E (mrestrict (w_H W) mem) (YP09.mkRegion (Some 2%nat) lo hi lo hi []).
Proof.
intros E W mem spv lo hi H2 Hp Hlo Hhi Hlh. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite H2.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable tfibsegs). apply Hp. lia.
Qed.

(* the stack bytes of the journal's allowance are present *)
Lemma o9_jpres : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world tfibsegs) mem md k a,
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
sp0 - STK <= a < sp0 -> apresent (w_H W) mem a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k a HJ Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). exact (Hpres a Ha).
Qed.

(* the shadow window of a range of the walk's own frame is readable *)
Lemma o9_hull : forall ly S (W : world tfibsegs) mem md pos x n,
AR tfibsegs B ly S W mem md -> In (3, pos) (frames S) ->
frame_addr ly 3 pos <= x -> 0 < n -> x + n <= frame_addr ly 3 pos + 512 ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) x n.
Proof.
intros ly S W mem md pos x n HAR Hin Hx Hn Hxn.
eapply shadow_hull_vis_of_frame; try eassumption;
  try (change (fs_frame_bytes 3) with 512; lia).
Qed.

(* every byte of a range of the frame is readable *)
Lemma o9_frame_rd : forall ly S (W : world tfibsegs) mem md pos x n,
AR tfibsegs B ly S W mem md -> In (3, pos) (frames S) ->
frame_addr ly 3 pos <= x -> x + n <= frame_addr ly 3 pos + 512 ->
forall a, x <= a < x + n -> aview tfibsegs (w_H W) mem a <> None.
Proof.
intros ly S W mem md pos x n HAR Hin Hx Hxn a Ha.
destruct (al_frames _ _ LAWS ly S W mem md 3 pos HAR Hin) as (_ & _ & Hpr & _).
change (fs_frame_bytes 3) with 512 in Hpr.
apply (aview_some_of_apresent tfibsegs).
replace a with (frame_addr ly 3 pos + (a - frame_addr ly 3 pos)) by lia.
exact (proj1 (Hpr (frame_addr ly 3 pos + (a - frame_addr ly 3 pos)) ltac:(lia))).
Qed.
End w.

(* ================================ the end of the success path at CHK ================================ *)
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis LAWS : AR_laws tfibsegs B.
Local Notation rd W mem := (mrestrict (w_H W) mem).

Lemma o9_want_ok : forall k d, rec_okZ k (Some d) -> kz_kind k = 9 -> kz_a k <= 127 ->
0 <= d_chars d <= 8 ->
(forall j, (j < Z.to_nat (d_chars d))%nat -> nth j (kz_bytes k) 0 <= 127) ->
owe_want_okZ (owe_setZ k 0 (o9_bs d k ++ skipn (length (o9_bs d k)) (kz_want k))
  (Z.of_nat (length (o9_bs d k))) (KEY 7 (kz_a k)) 1) (Some d).
Proof.
intros k d Hrec Hkind Ha Hchars Hby.
pose proof Hrec as (_ & Hpd & Hrdr & _).
destruct (pd_range_A _ _ _ Hpd) as (_ & _ & Rdev & Rstr & Rchr & Rctr).
destruct Hrdr as (Ra & _ & _ & _ & Rlen & Rby & _).
assert (Hsb : seven_bit (firstn (Z.to_nat (d_chars d)) (kz_bytes k)) = true).
{ apply o9_sb_true; [rewrite Rlen; lia|]. intros j Hj. split; [|exact (Hby j Hj)].
  rewrite Forall_forall in Rby. apply (proj1 (Rby (nth j (kz_bytes k) 0) ltac:(apply nth_In; rewrite Rlen; lia))). }
pose proof (owe9_ok d (kz_a k) (kz_b k) (kz_c k) (kz_delta k) (kz_bytes k) (kz_n k) ltac:(lia) Hsb) as HO.
assert (HK : owe_kZ k (Some d) = owe_spec 9 (Some d) (kz_a k) (kz_b k) (kz_c k) (kz_delta k) (kz_bytes k) (kz_n k))
  by (unfold owe_kZ; rewrite Hkind; reflexivity).
rewrite <- HK in HO. fold (o9_bs d k) in HO.
apply (owe_want_ok_succ k (Some d) _ (o9_bs d k) (KEY 7 (kz_a k)) 1 HO).
rewrite firstn_app, Nat.sub_diag, firstn_all, firstn_O, app_nil_r.
symmetry. apply o9_map_u8.
unfold o9_bs. apply Forall_app. split.
- repeat apply Forall_cons; try apply Forall_nil; try (pose proof (owe_u8_range (d_dev d)); lia);
  try (pose proof (owe_u8_range (kz_a k)); lia); lia.
- apply Forall_app. split; [|repeat apply Forall_cons; try apply Forall_nil; lia].
  rewrite <- (firstn_skipn (Z.to_nat (d_chars d)) (kz_bytes k)) in Rby.
  apply Forall_app in Rby. exact (proj1 Rby).
Qed.

Lemma o9_bs_len : forall d k, length (kz_bytes k) = 24%nat -> 0 <= d_chars d <= 24 ->
Z.of_nat (length (o9_bs d k)) = d_chars d + 7.
Proof.
intros d k Hl Hc. unfold o9_bs. rewrite !length_app, length_firstn, Hl.
cbn [length]. lia.
Qed.

Lemma o9_bs_rng : forall d k, rec_okZ k (Some d) -> Forall (fun x => 0 <= x < 256) (o9_bs d k).
Proof.
intros d k Hrec. pose proof Hrec as (_ & _ & Hrdr & _).
destruct Hrdr as (_ & _ & _ & _ & _ & Rby & _).
unfold o9_bs. apply Forall_app. split.
- repeat apply Forall_cons; try apply Forall_nil; try (pose proof (owe_u8_range (d_dev d)); lia);
  try (pose proof (owe_u8_range (kz_a k)); lia); lia.
- apply Forall_app. split; [|repeat apply Forall_cons; try apply Forall_nil; lia].
  rewrite <- (firstn_skipn (Z.to_nat (d_chars d)) (kz_bytes k)) in Rby.
  apply Forall_app in Rby. exact (proj1 Rby).
Qed.

Lemma o9_bs_lenN : forall d k, length (kz_bytes k) = 24%nat -> 0 <= d_chars d <= 8 ->
length (o9_bs d k) = (7 + Z.to_nat (d_chars d))%nat.
Proof.
intros d k Hl Hc. unfold o9_bs. rewrite !length_app, length_firstn, Hl. cbn [length]. lia.
Qed.

(* the bytes after the four-byte head: the payload pl as the second copy wrote it *)
Lemma o9_bs_nth_mid : forall d k j, (4 <= j < 6 + Z.to_nat (d_chars d))%nat ->
length (kz_bytes k) = 24%nat -> 0 <= d_chars d <= 8 ->
nth j (o9_bs d k) 0 = nth (j - 4) ([u8 (kz_a k); 0] ++ firstn (Z.to_nat (d_chars d)) (kz_bytes k)) 0.
Proof.
intros d k j Hj Hl Hc. unfold o9_bs.
change ([0xf0; 0x13; u8 (d_dev d); 0x40; u8 (kz_a k); 0] ++ firstn (Z.to_nat (d_chars d)) (kz_bytes k) ++ [0xf7])
  with ([0xf0; 0x13; u8 (d_dev d); 0x40] ++ (([u8 (kz_a k); 0] ++ firstn (Z.to_nat (d_chars d)) (kz_bytes k)) ++ [0xf7])).
rewrite app_nth2 by (cbn [length]; lia). cbn [length].
rewrite app_nth1; [reflexivity|].
rewrite length_app, length_firstn, Hl. cbn [length]. lia.
Qed.

Lemma o9_bs_nth_last : forall d k, length (kz_bytes k) = 24%nat -> 0 <= d_chars d <= 8 ->
nth (6 + Z.to_nat (d_chars d)) (o9_bs d k) 0 = 0xf7.
Proof.
intros d k Hl Hc. unfold o9_bs. rewrite app_assoc.
assert (HL : length ([0xf0; 0x13; u8 (d_dev d); 0x40; u8 (kz_a k); 0] ++ firstn (Z.to_nat (d_chars d)) (kz_bytes k))
  = (6 + Z.to_nat (d_chars d))%nat) by (rewrite length_app, length_firstn, Hl; cbn [length]; lia).
rewrite app_nth2 by lia. rewrite HL, Nat.sub_diag. reflexivity.
Qed.

Lemma o9_err_fin : forall g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys k d E ss regs3 mem3 md3,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kj ->
frames S2 = [(3, pos)] -> 0 <= kj <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
ops_at ops regs2 -> cur_at g sp1 c W2 mem2 -> k_at g pos k W2 mem2 -> rec_okZ k (Some d) ->
kz_rc k = fst (enc_kZ k (Some d)) ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem3 md3 kj ->
st_ok tfibsegs E ss (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 PC_CHK) mem3 (seg_rom tfibsegs))) ->
env_agree 37 (am_env g pos c regs2 ys) E ->
am_keep_ok (ss_regs ss) = true -> sr_get (ss_regs ss) 26%bv = SOff 26 0 ->
nth_error (ss_mem ss) 4 = Some am_cur_region ->
(forall a, 0 <= a < 2 ^ 64 -> ~ owe_zone g pos sp1 0 a ->
 aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
val_mem tfibsegs (rd W2 mem3) (FA g pos + 316) 4 (-11) ->
val_mem tfibsegs (rd W2 mem3) (FA g pos + 344) 8 0 ->
val_mem tfibsegs (rd W2 mem3) (FA g pos + 352) 4 0 ->
val_mem tfibsegs (rd W2 mem3) (FA g pos + 356) 4 0 ->
fst (owe_kZ k (Some d)) = E_RANGE ->
SRr tfibsegs W2 (mkCfg (mkst regs3 (Z_to_bv 64 PC_CHK) mem3 (seg_rom tfibsegs)) md3)
  (inv_chk B MT K XM_LIB g pos sp1 ops).
Proof.
intros g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys k d E ss regs3 mem3 md3
  HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HJ3 HS HAE Hkeep H26 Hc4 KE V316 V344 V352 V356 Hwhy.
apply (owe_chk_end B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys k (Some d) 0
  mem3 regs3 md3 E ss (-11) [] 0 0 0 HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HJ3 HAE HS Hkeep H26 Hc4
  eq_refl ltac:(cbn; lia) KE).
- exact V316.
- apply garr8_nil.
- exact V344.
- exact V352.
- exact V356.
- lia.
- lia.
- lia.
- lia.
- apply owe_want_ok_fail; [exact Hwhy | unfold E_RANGE; lia].
Qed.

Lemma o9_ok_fin : forall g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys k d E ss ms md3,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kj ->
frames S2 = [(3, pos)] -> 0 <= kj <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
ops_at ops regs2 -> cur_at g sp1 c W2 mem2 -> k_at g pos k W2 mem2 -> rec_okZ k (Some d) ->
kz_rc k = fst (enc_kZ k (Some d)) -> kz_kind k = 9 -> 0 <= d_chars d <= 8 ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)]
  ly2 S2 W2 (ms_mem ms) md3 kj ->
st_ok tfibsegs E ss (restrict (w_H W2) ms) -> ss_pc ss = PC_CHK -> ss_resv ss = None ->
env_agree 37 (am_env g pos c regs2 ys) E ->
am_keep_ok (ss_regs ss) = true -> sr_get (ss_regs ss) 26%bv = SOff 26 0 -> In am_cur_region (ss_mem ss) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ o9_zone g pos sp1 (d_chars d) a ->
 aview tfibsegs (w_H W2) (ms_mem ms) a = aview tfibsegs (w_H W2) mem2 a) ->
aview tfibsegs (w_H W2) (ms_mem ms) (shadow_addr (FA g pos) + 4) = Some SH_F8 ->
aview tfibsegs (w_H W2) (ms_mem ms) (shadow_addr (FA g pos) + 5) = Some SH_F8 ->
garr8 tfibsegs (rd W2 (ms_mem ms)) (FA g pos + 320) (o9_bs d k) ->
val_mem tfibsegs (rd W2 (ms_mem ms)) (FA g pos + 316) 4 0 ->
val_mem tfibsegs (rd W2 (ms_mem ms)) (FA g pos + 344) 8 (d_chars d + 7) ->
val_mem tfibsegs (rd W2 (ms_mem ms)) (FA g pos + 352) 4 (KEY 7 (kz_a k)) ->
val_mem tfibsegs (rd W2 (ms_mem ms)) (FA g pos + 356) 4 1 ->
kz_a k <= 127 -> (forall j, (j < Z.to_nat (d_chars d))%nat -> nth j (kz_bytes k) 0 <= 127) ->
SRr tfibsegs W2 (mkCfg ms md3) (inv_chk B MT K XM_LIB g pos sp1 ops).
Proof.
intros g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys k d E ss ms md3
  HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc Hkind Hchars HJf HS Hpc Hrv HAE Hkeep H26 Hcr KK SH4 SH5
  Gbs Vr Vl Vkey Vdp Ha Hby.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & _).
pose proof (owe_frame_app B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as Happ.
change (fs_frame_bytes 3) with 512 in Hfceil.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold AM_HI in *.
pose proof Hrec as (_ & Hpd & Hrdr & _).
destruct Hrdr as (Rar & _ & _ & _ & Rlen & Rby & _).
pose proof HC as HSH. do 43 (destruct HSH as (_ & HSH)). destruct HSH as (HSH & _).
assert (D8 : 0 <= FA g pos / 8 /\ 8 * (FA g pos / 8) <= FA g pos)
  by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
assert (D2 : 512 <= FA g pos / 8) by (apply Z.div_le_lower_bound; lia).
assert (D1 : FA g pos / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia).
assert (Hsh : SB + 512 <= shadow_addr (FA g pos) <= SB + 2 ^ 44)
  by (unfold shadow_addr, SHADOW_OFF, SB; lia).
assert (Hfsh : FA g pos + 512 <= shadow_addr (FA g pos) \/ shadow_addr (FA g pos) + 64 <= FA g pos).
{ unfold in_app in Happ. unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
  destruct Happ as (_ & [Hlow | (Hh1 & Hh2)]); [left; lia|].
  right. assert (D4 : 2199291686912 <= FA g pos / 8) by (apply Z.div_le_lower_bound; lia). lia. }
assert (Lbs : Z.of_nat (length (o9_bs d k)) = d_chars d + 7) by (apply o9_bs_len; [exact Rlen | lia]).
assert (Lbs24 : (length (o9_bs d k) <= 24)%nat) by lia.
set (k' := owe_setZ k 0 (o9_bs d k ++ skipn (length (o9_bs d k)) (kz_want k))
  (Z.of_nat (length (o9_bs d k))) (KEY 7 (kz_a k)) 1).
apply (owex_chk B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys k' (Some d) E ss ms md3
  HJf Hfr Hk Hmo HC Hops Hcur HAE HS Hpc Hrv Hkeep H26 Hcr).
- intros a Ha2. unfold am_keepzone in Ha2. apply KK; [lia|].
  revert Hfsh Hsh. unfold o9_zone, shadow_addr, SHADOW_OFF, SB. appn. lia.
- intros i Hi.
  assert (Ei : i = 4 \/ i = 5 \/ (0 <= i < 56 /\ i <> 4 /\ i <> 5)) by lia.
  destruct Ei as [-> | [-> | (Hi2 & Hi4 & Hi5)]].
  + rewrite SH4. vm_compute. reflexivity.
  + rewrite SH5. vm_compute. reflexivity.
  + rewrite KK; [exact (HSH i Hi) | unfold shadow_addr, SHADOW_OFF; lia |].
    revert Hfsh Hsh. unfold o9_zone, shadow_addr, SHADOW_OFF, SB. appn. lia.
- apply (owe_k_at_end g pos k W2 mem2 W2 (ms_mem ms) 0 (o9_bs d k)
    (Z.of_nat (length (o9_bs d k))) (KEY 7 (kz_a k)) 1 Hkat Lbs24).
  + intros a Ha2. apply KK; [lia|].
    revert Hfsh Hsh. unfold o9_zone, shadow_addr, SHADOW_OFF, SB. appn. lia.
  + replace (FA g pos + 176 + 140) with (FA g pos + 316) by lia. exact Vr.
  + replace (FA g pos + 176 + 144) with (FA g pos + 320) by lia. exact Gbs.
  + replace (FA g pos + 176 + 168) with (FA g pos + 344) by lia.
    apply (owe_vm _ _ 8 (d_chars d + 7)); [exact Vl|]. rewrite Lbs. reflexivity.
  + replace (FA g pos + 176 + 176) with (FA g pos + 352) by lia. exact Vkey.
  + replace (FA g pos + 176 + 180) with (FA g pos + 356) by lia. exact Vdp.
  + lia.
  + lia.
  + exact (o9_key_rng (kz_a k) ltac:(lia)).
  + lia.
- apply owe_setZ_rec. exact Hrec.
- destruct (owe_setZ_kz k (Some d) 0 (o9_bs d k ++ skipn (length (o9_bs d k)) (kz_want k))
    (Z.of_nat (length (o9_bs d k))) (KEY 7 (kz_a k)) 1) as (_ & E2 & E3).
  unfold k'. rewrite E2, E3. exact Hrc.
- exact (o9_want_ok k d Hrec Hkind Ha ltac:(lia) Hby).
Qed.
End f.
