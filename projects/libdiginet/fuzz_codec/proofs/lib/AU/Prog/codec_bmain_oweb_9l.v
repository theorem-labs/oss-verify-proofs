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
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owe9_lib.v, with its module paths, module names and numbers changed; 206 of its 396 lines of code are new or changed and 461 lines of the source are left out. *)
(* Lemmas of segment OWE9 (SCRIBBLE, owe_pc 9 = 0x8293c) of the image-B walk of LLVMFuzzerTestOneInput
   (lib/AU/Prog/codec_bmain_inv.v seg_owe 9). It is the image-A codec_amain_owe9_lib.v at image B, where SCRIBBLE
   calls owe_sysex (0x82f70) while the payload pl at F + 48 is marked usable (the frame's shadow bytes 6, 7 read
   00 02) and s9 holds the shadow address of desk + 10:
   - owe9_split / owe9_rng_a / owe9_rng_s / o9_ok: owe_spec of kind 9.
   - o9_shS: the frame's shadow map while pl is usable; o9_ra_pl: pl's ten bytes are addressable then.
   - o9_key / o9_key_rng: want_key = a | 0x70000 (0x82f74 lhu, 0x82f7c or).
   - the regions of the walk (o9_rk, o9_rg, o9_rs, o9_rpl, o9_rsh), the window helpers (o9_shwin_ok, o9_hull,
     o9_frame_rd, o9_ra_zero, o9_chunk_aview, o9_garr_of_aview) and the kept-region shapes of the checked copy
     (o9_fix_wins, o9_closew, o9_plo).
   - o9_callst: the cut facts at owe_sysex's entry from the executor state there (lib/AU/Prog/codec_bmain_owebl.v
     bm_exit_sh from the segment's start cut); k_at_key: the record with want_key replaced. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgSatU CodecRo CodecGlobs.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkU CPgWalkImgU CPgWalkKeptU CPgWalkCallU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_inv codec_bmain_st codec_bmain_lem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_headl codec_bmain_encl codec_bmain_owel codec_bmain_owebl.
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

Lemma o9_ok : forall d a b c delta bytes n, 0 <= a <= 0x7f ->
seven_bit (firstn (Z.to_nat (d_chars d)) bytes) = true ->
owe_spec 9 (Some d) a b c delta bytes n =
(0, (fst (owe_sx (d_dev d) 0x40 ([a; 0] ++ firstn (Z.to_nat (d_chars d)) bytes)), KEY 7 a,
     snd (owe_sx (d_dev d) 0x40 ([a; 0] ++ firstn (Z.to_nat (d_chars d)) bytes)))).
Proof.
intros d a b c delta bytes n Ha H. rewrite owe9_split, H. cbn [negb].
rewrite (proj2 (Z.ltb_ge 127 a) ltac:(lia)). cbn [orb].
replace (u8 a) with a by (unfold u8; rewrite Z.mod_small by lia; reflexivity).
destruct (owe_sx (d_dev d) 0x40 ([a; 0] ++ firstn (Z.to_nat (d_chars d)) bytes)). reflexivity.
Qed.

(* 0x82f74 lhu a0,24(s7); 0x82f78 lui a1,0x70; 0x82f7c or a0,a0,a1 *)
Lemma o9_key : forall a, 0 <= a <= 127 -> Z.lor a 458752 = KEY 7 a.
Proof.
intros a Ha. unfold KEY. change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia.
rewrite (Z.mod_small a) by lia. change (7 * 65536) with 458752. apply Z.lor_comm.
Qed.
Lemma o9_key_rng : forall a, 0 <= a <= 127 -> 0 <= KEY 7 a < 2 ^ 32.
Proof.
intros a Ha.
assert (C : forallb (fun y => (0 <=? KEY 7 y) && (KEY 7 y <? 2 ^ 32)) (map Z.of_nat (seq 0 128)) = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in C. specialize (C a ltac:(apply in_map_iff; exists (Z.to_nat a); split; [lia | apply in_seq; lia])).
apply andb_prop in C as (C1 & C2). apply Z.leb_le in C1. apply Z.ltb_lt in C2. lia.
Qed.

(* ================================ the payload's shadow ================================ *)
(* the frame's shadow map while pl (F + 48, ten bytes) is usable: bytes 6, 7 = 00 02 (0x82ef0 / 0x82ef8) *)
Definition o9_shS : list Z := firstn 6 (shm 0) ++ [0; 2] ++ skipn 8 (shm 0).
Lemma o9_shS_len : length o9_shS = 60%nat.
Proof. reflexivity. Qed.
Lemma o9_shS_k : forall i, (24 <= i < 47)%nat -> nth i o9_shS 0 = 0.
Proof.
intros i Hi.
assert (C : forallb (fun j => nth j o9_shS 0 =? 0) (seq 24 23) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in C. specialize (C i ltac:(apply in_seq; lia)). apply Z.eqb_eq in C. exact C.
Qed.
Lemma o9_shS_other : forall i, (i < 60)%nat -> i <> 6%nat -> i <> 7%nat -> nth i o9_shS 0 = nth i (shm 0) 0.
Proof.
intros i Hi H6 H7.
assert (C : forallb (fun j => orb (orb (Nat.eqb j 6) (Nat.eqb j 7)) (nth j o9_shS 0 =? nth j (shm 0) 0))
  (seq 0 60) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in C. specialize (C i ltac:(apply in_seq; lia)).
apply orb_prop in C as [C | C]; [apply orb_prop in C as [C | C]; apply Nat.eqb_eq in C; lia|].
apply Z.eqb_eq in C. exact C.
Qed.

(* ================================ the regions and atoms of the walk ================================
   Atoms of the start state (bm_env's ys from 37): 37 = k.a, 38 .. 45 = k.bytes[0 .. 8). The desk's four bytes
   are literals (the walk is done once per desk). Regions: want_rc (index 5, as codec_bmain_oweb_11.v's o11_rc, so
   that o11_err_end ends the error paths), k.a and k.bytes[0 .. 8) read-only (rk), the desk's four bytes (rg); the
   walk adds pl (rpl) and pl's two shadow bytes (rsh) at 0x82ef0. *)
Definition o9_rr : YP09.region := bm_frame_region 332 336 332 336 [YP09.mkChunk 332 (CVal 4 (SLit 0))].
Definition o9_rk : YP09.region := bm_frame_region 216 240 216 216
[YP09.mkChunk 216 (CVal 4 (SOff 37 0));
 YP09.mkChunk 232 (CVal 1 (SOff 38 0)); YP09.mkChunk 233 (CVal 1 (SOff 39 0));
 YP09.mkChunk 234 (CVal 1 (SOff 40 0)); YP09.mkChunk 235 (CVal 1 (SOff 41 0));
 YP09.mkChunk 236 (CVal 1 (SOff 42 0)); YP09.mkChunk 237 (CVal 1 (SOff 43 0));
 YP09.mkChunk 238 (CVal 1 (SOff 44 0)); YP09.mkChunk 239 (CVal 1 (SOff 45 0))].
Definition o9_rg (d : desk) : YP09.region :=
owe_desk_region [SLit (d_dev d); SLit (d_strips d); SLit (d_chars d); SLit (d_counter d)].
Definition o9_rs (d : desk) : smem := [o9_rr; o9_rk; o9_rg d].
Definition o9_rpl : YP09.region := bm_frame_region 48 58 48 58 [].
Definition o9_rsh : YP09.region := YP09.mkRegion (Some 34%nat) 6 8 6 8 [].
Definition o9_AF : list (nat * afact) :=
[(22%nat, mkAF 0x9dfc0 0x9dfe0 5); (37%nat, mkAF 0 (2 ^ 32 - 1) 0);
 (38%nat, mkAF 0 255 0); (39%nat, mkAF 0 255 0); (40%nat, mkAF 0 255 0); (41%nat, mkAF 0 255 0);
 (42%nat, mkAF 0 255 0); (43%nat, mkAF 0 255 0); (44%nat, mkAF 0 255 0); (45%nat, mkAF 0 255 0)].
Definition o9_SH : list shent := [owe_desk_SH; owe_SHk].
Definition o9_ys (k : kcallZ) : list Z :=
[kz_a k; nth 0 (kz_bytes k) 0; nth 1 (kz_bytes k) 0; nth 2 (kz_bytes k) 0; nth 3 (kz_bytes k) 0;
 nth 4 (kz_bytes k) 0; nth 5 (kz_bytes k) 0; nth 6 (kz_bytes k) 0; nth 7 (kz_bytes k) 0].
(* the payload owe_sysex sends: a, 0, k.bytes[0 .. chars) *)
Definition o9_pl (d : desk) (k : kcallZ) : list Z := [kz_a k; 0] ++ firstn (Z.to_nat (d_chars d)) (kz_bytes k).

(* the bytes the walk writes up to owe_sysex: the cursor's window (not changed), want_rc, pl and its two shadow
   bytes, the callee's stack below sp1 *)
Definition o9_zone (g : ectx) (pos sp1 a : Z) : Prop :=
(sp1 - 4096 <= a < sp1) \/ (sp1 + 184 <= a < sp1 + 200) \/ (FA g pos + 332 <= a < FA g pos + 336) \/
(FA g pos + 48 <= a < FA g pos + 58) \/ (shadow_addr (FA g pos) + 6 <= a < shadow_addr (FA g pos) + 8).
(* the same without pl: what the run after the checked copy may write *)
Definition o9_zc (g : ectx) (pos sp1 a : Z) : Prop :=
(sp1 - 4096 <= a < sp1) \/ (sp1 + 184 <= a < sp1 + 200) \/ (FA g pos + 332 <= a < FA g pos + 336) \/
(shadow_addr (FA g pos) + 6 <= a < shadow_addr (FA g pos) + 8).

(* ================================ small facts ================================ *)
Lemma o9_nth_firstn : forall (l : list Z) m j, (j < m)%nat -> nth j (firstn m l) 0 = nth j l 0.
Proof.
intros l m; revert l. induction m as [|m IH]; intros l j Hj; [lia|].
destruct l as [|x l]; [destruct j; reflexivity|].
destruct j as [|j]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.

Lemma o9_vm42 : forall m a v, val_mem tfibsegs m a 4 v -> 0 <= v < 2 ^ 16 -> val_mem tfibsegs m a 2 v.
Proof.
intros m a v H Hv j Hj. assert (Hj4 : (j < 4)%nat) by lia. rewrite (H j Hj4). unfold YO0f.le_byte.
assert (M4 : v mod 2 ^ (8 * Z.of_nat 4) = v) by (apply Z.mod_small; cbn; lia).
assert (M2 : v mod 2 ^ (8 * Z.of_nat 2) = v) by (apply Z.mod_small; cbn; lia).
rewrite M4, M2. reflexivity.
Qed.

(* a region of the frame with no window, from its chunks *)
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
YP09.mkRegion (YP09.r_base r) 48 50 48 48 (filter (fun c => YP09.c_off c <? 50) (YP09.r_chunks r)).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* 0x82f18 `sb a1,0(a0)`: the low byte of the sign-extended a *)
Lemma o9_sx_u8 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v <= 127 ->
bv_unsigned (sv_denot E (SExt true 32 (SOff n 0))) mod 256 = v.
Proof.
intros E n v Hn Hv.
change (bv_unsigned (sv_denot E (SExt true 32 (SOff n 0)))) with (U E (SExt true 32 (SOff n 0))).
rewrite (owe_U_sx32 E n v Hn ltac:(lia)).
rewrite (proj2 (Z.ltb_lt v (2 ^ 31)) ltac:(lia)). apply Z.mod_small. lia.
Qed.

Lemma o9_add_region : forall E ss ms r,
st_ok tfibsegs E ss ms -> YP09.region_wf r = true -> region_ok tfibsegs E (ms_mem ms) r ->
all_disjoint E r (ss_mem ss) ->
st_ok tfibsegs E (mkSS (ss_pc ss) (ss_regs ss) (r :: ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof. intros E ss ms r H1 H2 H3 H4. eapply ast_ok_add_region; eassumption. Qed.

Lemma o9_garr_of_aview : forall H (m : word -> option byte) a l,
(forall j, (j < length l)%nat -> aview tfibsegs H m (a + Z.of_nat j) = Some (nth j l 0)) ->
Forall (fun x => 0 <= x < 256) l -> garr8 tfibsegs (mrestrict H m) a l.
Proof.
intros H m a l Hv Hr j Hj. split.
- apply val_mem1_of_aviewA. apply Hv. exact Hj.
- rewrite Forall_forall in Hr. apply Hr. apply nth_In. exact Hj.
Qed.

(* a range whose shadow bytes are zero is addressable *)
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

(* the engine's shadow entry for k's 184 bytes, from its shadow bytes in the memory the walk has reached *)
Lemma o9_shk : forall (W : world tfibsegs) mem E F,
F mod 64 = 0 -> 4096 <= F -> in_app F 512 ->
(forall j, 24 <= j <= 46 -> aview tfibsegs (w_H W) mem (shadow_addr F + j) = Some 0) ->
ew E 33 = Z_to_bv 64 F -> ew E 32 = Z_to_bv 64 SB ->
shent_ok tfibsegs CW_Bx E (mrestrict (w_H W) mem) owe_SHk.
Proof.
intros W mem E F H64 H4096 Happ HZ E33 E32.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hra : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF (F + 192) 184).
{ replace 184 with (376 - 192) by lia.
  apply (o9_ra_zero W mem F 192 376); [exact H64 | lia | lia | lia |].
  intros j Hj. change (192 / 8) with 24 in Hj. change ((376 - 1) / 8) with 46 in Hj. apply HZ. lia. }
assert (Ham : amem_range (F + 192) 184) by (unfold in_app in Happ; appn; lia).
unfold owe_SHk. change 376 with (192 + 184).
apply (cw_shent_ra_off W mem E 33 F 192 184 Hra Ham); [appn; lia | lia | lia | appn; lia | exact E33 | exact E32].
Qed.

(* pl at F + 48, ten bytes: the shadow bytes 6 and 7 of the frame (00 02) make them addressable *)
Lemma o9_ra_pl : forall (W : world tfibsegs) mem F, F mod 64 = 0 -> 0 <= F ->
aview tfibsegs (w_H W) mem (shadow_addr F + 6) = Some 0 ->
aview tfibsegs (w_H W) mem (shadow_addr F + 7) = Some 2 ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF (F + 48) 10.
Proof.
intros W mem F H64 HF H6 H7 x Hx.
assert (Dm : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)); lia).
assert (D8 : F / 8 = 8 * (F / 64)).
{ transitivity ((8 * (F / 64) * 8) / 8); [f_equal; lia | apply Z.div_mul; lia]. }
assert (Dm8 : F = 8 * (F / 8)) by lia.
destruct (Z_lt_le_dec x (F + 56)) as [Hlt|Hge].
- exists 0. split; [|left; reflexivity].
  assert (Ex : x / 8 = F / 8 + 6).
  { replace x with ((F / 8 + 6) * 8 + (x - F - 48)) by lia.
    rewrite Z.div_add_l by lia. rewrite (Z.div_small (x - F - 48)) by lia. lia. }
  unfold shadow_of_addr. rewrite Ex. unfold shadow_addr in H6.
  replace (SHADOW_OFF + (F / 8 + 6)) with (SHADOW_OFF + F / 8 + 6) by lia. exact H6.
- exists 2. split.
  + assert (Ex : x / 8 = F / 8 + 7).
    { replace x with ((F / 8 + 7) * 8 + (x - F - 56)) by lia.
      rewrite Z.div_add_l by lia. rewrite (Z.div_small (x - F - 56)) by lia. lia. }
    unfold shadow_of_addr. rewrite Ex. unfold shadow_addr in H7.
    replace (SHADOW_OFF + (F / 8 + 7)) with (SHADOW_OFF + F / 8 + 7) by lia. exact H7.
  + right. split; [|lia].
    replace x with ((x - F - 56) + (F / 8 + 7) * 8) by lia.
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

(* the record with want_key replaced, when its other bytes are kept *)
Lemma k_at_key : forall g pos k key (W W' : world tfibsegs) mem mem',
k_at g pos k W mem -> 0 <= key < 2 ^ 32 ->
(forall x, FA g pos + 192 <= x < FA g pos + 376 -> ~ (FA g pos + 368 <= x < FA g pos + 372) ->
 aview tfibsegs (w_H W') mem' x = aview tfibsegs (w_H W) mem x) ->
val_mem tfibsegs (mrestrict (w_H W') mem') (FA g pos + 192 + 176) 4 key ->
k_at g pos (owe_setZ k (kz_want_rc k) (kz_want k) (kz_want_len k) key (kz_want_display k)) W' mem'.
Proof.
intros g pos k key W W' mem mem' (HK & Hwf) Hkey Hk Vk.
set (q := FA g pos + 192) in *.
assert (Hk' : forall x, q <= x < q + 184 -> ~ (q + 176 <= x < q + 180) ->
  aview tfibsegs (w_H W') mem' x = aview tfibsegs (w_H W) mem x) by (intros x Hx Hn; apply Hk; unfold q in *; lia).
clear Hk. split.
- destruct HK as (V0 & V8 & V16 & V24 & V28 & V32 & V36 & G40 & V64 & V72 & G76 & G108 & V140 & G144 & V168 & V176 & V180).
  pose proof Hwf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Lb & Lbe & Lo & Lw).
  unfold owe_setZ, kcall_atA. cbn [kz_kind kz_p kz_desk kz_a kz_b kz_c kz_delta kz_bytes kz_n kz_rc kz_before kz_out
    kz_want_rc kz_want kz_want_len kz_want_key kz_want_display].
  fold q.
  assert (KV : forall o' n v, 0 <= o' -> o' + Z.of_nat n <= 184 -> (o' + Z.of_nat n <= 176 \/ 180 <= o') ->
    val_mem tfibsegs (mrestrict (w_H W) mem) (q + o') n v -> val_mem tfibsegs (mrestrict (w_H W') mem') (q + o') n v).
  { intros o' n v H1 H2 H3 Hv. apply (cw_val_mem_kept (w_H W) (w_H W') mem mem'); [|exact Hv].
    intros x Hx. apply Hk'; lia. }
  assert (KG : forall o' l, 0 <= o' -> o' + Z.of_nat (length l) <= 184 -> (o' + Z.of_nat (length l) <= 176 \/ 180 <= o') ->
    garr8 tfibsegs (mrestrict (w_H W) mem) (q + o') l -> garr8 tfibsegs (mrestrict (w_H W') mem') (q + o') l).
  { intros o' l H1 H2 H3 Hg. apply (bm_garr8_kept_x (w_H W) (w_H W') mem mem'); [|exact Hg].
    intros x Hx. apply Hk'; lia. }
  split; [rewrite <- (Z.add_0_r q); apply KV; [lia | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact V0]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact V8]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact V16]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact V24]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact V28]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact V32]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact V36]|].
  split; [apply KG; [lia | rewrite Lb; cbn; lia | rewrite Lb; cbn; lia | exact G40]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact V64]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact V72]|].
  split; [apply KG; [lia | rewrite Lbe; cbn; lia | rewrite Lbe; cbn; lia | exact G76]|].
  split; [apply KG; [lia | rewrite Lo; cbn; lia | rewrite Lo; cbn; lia | exact G108]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact V140]|].
  split; [apply KG; [lia | rewrite Lw; cbn; lia | rewrite Lw; cbn; lia | exact G144]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact V168]|].
  split; [exact Vk|].
  apply KV; [lia | cbn; lia | cbn; lia | exact V180].
- destruct Hwf as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17).
  unfold kcall_wfZ, owe_setZ.
  cbn [kz_kind kz_p kz_desk kz_a kz_b kz_c kz_delta kz_bytes kz_n kz_rc kz_before kz_out kz_want_rc kz_want
    kz_want_len kz_want_key kz_want_display].
  repeat split; try assumption; try lia.
Qed.

Section w.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.

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

(* a region of the frame, from its chunks *)
Lemma o9_frame_region_ok : forall E (W : world tfibsegs) mem md ly S pos lo hi wlo whi cs,
AR tfibsegs B ly S W mem md -> In (3, pos) (frames S) -> bv_unsigned (ew E 33) = frame_addr ly 3 pos ->
0 <= lo -> lo <= wlo -> whi <= hi -> hi <= 512 ->
Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) mem) (frame_addr ly 3 pos)) cs ->
region_ok tfibsegs E (mrestrict (w_H W) mem) (bm_frame_region lo hi wlo whi cs).
Proof.
intros E W mem md ly S pos lo hi wlo whi cs HAR Hin Hb Hlo Hlw Hwh Hhi Hcs.
destruct (al_frames _ _ LAWS ly S W mem md 3 pos HAR Hin) as (_ & _ & Hpr & _).
destruct (frames_bounds tfibsegs B LAWS ly S W mem md 3 pos HAR Hin) as (Hf4096 & Hfc & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
change (fs_frame_bytes 3) with 512 in Hfc, Hpr.
unfold region_ok, bm_frame_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hb.
split; [lia|]. split; [lia|]. split; [|exact Hcs].
intros o Ho. apply (apresent_writable tfibsegs).
exact (proj1 (Hpr (frame_addr ly 3 pos + o) ltac:(lia))).
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

(* ================================ the cut facts at owe_sysex's entry ================================ *)
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis LAWS : AR_laws tfibsegs B.

(* From the segment's start cut and the executor state at the call: mcom_sh with the frame's shadow map sh' the
   memory holds there and s9's value, the input cursor, s4 and k; the run wrote nothing in the spills, the saves,
   the flag word and k's bytes. *)
Lemma o9_callst : forall g pos sp1 ops c k ly2 S2 W2 regs2 mem2 md2 kev ys E ss ms md3 sh' s9v',
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kev ->
frames S2 = [(3, pos)] ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 -> ops_at ops regs2 -> cur_at g sp1 c W2 mem2 ->
k_at g pos k W2 mem2 ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2
  (ms_mem ms) md3 kev ->
env_agree 37 (bm_env g pos c regs2 ys) E ->
st_ok tfibsegs E ss (restrict (w_H W2) ms) -> ss_resv ss = None ->
bm_keep_ok9 (ss_regs ss) = true -> sr_get (ss_regs ss) 20%bv = SOff 20 0 ->
getr (ms_regs ms) 25 = w64 s9v' ->
In bm_cur_region (ss_mem ss) ->
(forall a, bm_keepzone g pos sp1 a -> aview tfibsegs (w_H W2) (ms_mem ms) a = aview tfibsegs (w_H W2) mem2 a) ->
(forall x, FA g pos + 192 <= x < FA g pos + 376 -> aview tfibsegs (w_H W2) (ms_mem ms) x = aview tfibsegs (w_H W2) mem2 x) ->
(forall i, 0 <= i < 60 ->
 aview tfibsegs (w_H W2) (ms_mem ms) (shadow_addr (FA g pos) + i) = Some (nth (Z.to_nat i) sh' 0)) ->
mcom_sh B MT K XM_LIB g pos sp1 sh' s9v' ly2 S2 W2 (ms_regs ms) (ms_mem ms) md3 /\ ops_at ops (ms_regs ms) /\
cur_at g sp1 c W2 (ms_mem ms) /\ k_at g pos k W2 (ms_mem ms).
Proof.
intros g pos sp1 ops c k ly2 S2 W2 regs2 mem2 md2 kev ys E ss ms md3 sh' s9v'
  HJ Hfr HC Hops Hcur Hkat HJ3 HAG HS Hresv Hkeep H20 H25 Hcr KZ KK KSH.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W2) E ss ms HS Hresv) as Ems.
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & Hblk).
pose proof HC as (Hpre & _ & R2 & _).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof Hcur as (Hc & _ & _).
pose proof HS as HS'. rewrite Ems in HS'.
assert (HAG35 : env_agree 35 (bm_env g pos c regs2 ys) E).
{ destruct HAG as (HA & HD). split; [intros n Hn'; apply HA; lia | exact HD]. }
split; [|split; [|split]].
- apply (bm_exit_sh B MT K XM_LIB LAWS g pos sp1 (shm 0) (FA g pos + 448) sh' s9v' c ys ly2 S2 W2 regs2 mem2 md2
    ly2 S2 W2 (ms_regs ms) (ms_mem ms) md3 kev (Z_to_bv 64 (ss_pc ss)) ss E (mcom_sh_of B MT K XM_LIB g pos sp1 0
    ly2 S2 W2 regs2 mem2 md2 HC) HJ3 HAG35 HS' Hkeep H25 KZ KSH).
  pose proof HC as HPerm. do 49 (destruct HPerm as (_ & HPerm)). exact HPerm.
- destruct Hops as (Hops & R20). split; [exact Hops|].
  rewrite (st_ok_restrict_reg tfibsegs (w_H W2) E ss ms 20%bv HS), H20.
  destruct HAG as (HA & _). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HA 20%nat ltac:(lia)).
  rewrite (bm_ew_reg g pos c regs2 ys 20 20%bv eq_refl). exact R20.
- apply (bm_cur_end g pos c regs2 ys E ss W2 ms sp1 HAG HS Hcr R2); unfold BM_HI in *; lia.
- apply (k_at_kept g pos k W2 W2 mem2 (ms_mem ms) Hkat). exact KK.
Qed.
End c.
End a.
