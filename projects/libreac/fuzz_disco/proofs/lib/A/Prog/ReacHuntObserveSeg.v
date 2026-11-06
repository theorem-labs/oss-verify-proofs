(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 334 of its 365 lines of code are new or changed and 38 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YA0o YA0q YCbm YK06 YI0m YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoFrame DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC1i YC45 YC4b YC7k YC81 YC85 YC88 YCbw YCkd ACbf ACj1 DiscoACja DiscoACjr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
ClassifyCore ReacDiscoClassifyOnSegment ReacDiscoTableObserve DiscoRo ReacFrameCleanLen ReacHuntObserve.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_classify_c disco_table_c hunt_c reac_disco_table_observe_c reac_frame_clean_len_c reac_hunt_observe_c
HuntObsFacts HuntObsLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis DRO : disco_ro_unowned B.

Lemma ho_kept_inblk : forall E lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) n lo hi wlo whi cs p b m ly2 S2 md2,
  acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi Er -> AR SEGS B ly2 S2 W2 mem2 md2 -> In (b, m) (ablocks B ly2 S2) ->
  bv_unsigned (ew E n) = p -> In (b, m) (ablocks B lyc Sc) -> b <= p + lo -> p + hi <= b + req_size m ->
  lo <= wlo -> whi <= hi -> (forall a, p + lo <= a < p + hi -> ~ Er a) ->
  region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi wlo whi cs p b m ly2 S2 md2 (_ & K2 & _) HAR2 Hin2 Hn Hin Hlo Hhi Hwlo Hwhi HnE.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hin2) as (_ & _ & _ & _ & Hpres2 & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hin); [lia|].
  replace (b + (a - b)) with a by lia. apply HnE. exact Ha.
- intros _. apply (apresent_writable SEGS). apply (proj1 (Hpres2 a ltac:(lia))).
Qed.

Lemma ho_awr_own : forall STK sp0 FP bl0 blc ly own x a,
  awr_byte STK sp0 FP bl0 blc ly own a -> awr_byte STK sp0 FP bl0 blc ly (x :: own) a.
Proof.
intros STK sp0 FP bl0 blc ly own x a [H | [H | [H | (cid & pos & Hin & Hr)]]];
[left; exact H | right; left; exact H | right; right; left; exact H |].
right; right; right. exists cid, pos. split; [right; exact Hin | exact Hr].
Qed.

Lemma ho_shok : forall E ly2 S2 (W2 : world SEGS) mem2 md2 hb hn h,
  AR SEGS B ly2 S2 W2 mem2 md2 -> In (hb, hn) (ablocks B ly2 S2) -> hb <= h -> h + 480 <= hb + req_size hn ->
  0 < h -> ew E 10 = Z_to_bv 64 h -> ew E 32 = Z_to_bv 64 SB ->
  sh_ok SEGS HOx ho_SH E (mrestrict (w_H W2) mem2).
Proof.
intros E ly2 S2 W2 mem2 md2 hb hn h HAR Hin Hhb Hhe Hh0 E10 E32.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 hb hn HAR Hin) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _).
unfold ho_SH, sh_ok. apply Forall_cons; [|apply Forall_nil].
assert (HU10 : U E (SOff 10 0) = h) by (shent_U_norm; reflexivity).
assert (HUB : U E HOx = SHADOW_OFF) by (unfold HOx; shent_U_norm; unfold SB, SHADOW_OFF; reflexivity).
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HU10, HUB. split.
- replace (h + 0) with h by lia. replace (480 - 0) with 480 by lia.
  apply (range_addressable_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 hb hn h 480 HAR Hin); lia.
- intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF in *.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp. lia.
Qed.

Lemma ho_shok_at : forall E (Wx : world SEGS) mx n (a : Z) (sz : Z),
  ew E 32 = Z_to_bv 64 SB -> ew E n = Z_to_bv 64 a -> 0 <= a -> a + sz <= 2 ^ 63 -> 0 <= sz ->
  range_addressable (aview SEGS (w_H Wx) mx) SHADOW_OFF a sz ->
  (forall x, a <= x < a + sz -> x < kLowShadowBeg) ->
  sh_ok SEGS HOx [mkSHE n 0 sz] E (mrestrict (w_H Wx) mx).
Proof.
intros E Wx mx n a sz E32 En Ha0 Hahi Hsz HR Hlow.
unfold sh_ok. apply Forall_cons; [|apply Forall_nil].
assert (HU : U E (SOff n 0) = a) by (shent_U_norm; reflexivity).
assert (HUB : U E HOx = SHADOW_OFF) by (unfold HOx; shent_U_norm; unfold SB, SHADOW_OFF; reflexivity).
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HU, HUB. split.
- replace (a + 0) with a by lia. replace (sz - 0) with sz by lia. exact HR.
- intros x Hx. cbn [Z.min Z.max] in Hx.
  pose proof (Hlow x ltac:(lia)). unfold SHADOW_OFF, kLowShadowBeg in *. lia.
Qed.

Lemma ho_slot : forall E m b od cs lo hi wlo whi (n : nat) (v : Z),
  region_ok SEGS E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 2) = b ->
  In (YP09.mkChunk od (CVal 8 (SOff n 0))) cs ->
  ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS m (b + od) 8 v.
Proof.
intros E m b od cs lo hi wlo whi n v HR Hb Hin Hn Hv.
exact (field_of_region E m 2%nat b cs lo hi wlo whi od 8%N (SOff n 0) v HR Hb Hin
  ltac:(cbn [sv_denot]; rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
  ltac:(cbn [Z.of_N Z.mul]; exact Hv) ltac:(cbn; lia)).
Qed.

Lemma ho_ro_img : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> in_img SEGS a.
Proof.
intros a [(s & Hs & _ & Hr) | Hrel]; [exists s; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hrel)].
Qed.

Lemma ho_rod_kept : forall (Wa Wb : world SEGS) ma mb,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wa) ma) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H Wb) mb a = aview SEGS (w_H Wa) ma a) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wb) mb).
Proof.
intros Wa Wb ma mb HR HK a Hro Ho He.
rewrite (HK a (ho_ro_img a Hro) Ho He). exact (HR a Hro Ho He).
Qed.

Lemma ho_garr_kept : forall (Wa Wb : world SEGS) ma mb a l,
  (forall i, a <= i < a + Z.of_nat (length l) -> aview SEGS (w_H Wb) mb i = aview SEGS (w_H Wa) ma i) ->
  garr8 SEGS (mrestrict (w_H Wa) ma) a l -> garr8 SEGS (mrestrict (w_H Wb) mb) a l.
Proof.
intros Wa Wb ma mb a l HE HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
intros kk Hk. rewrite <- (Hv kk Hk).
apply (mbyte_of_aview SEGS). apply HE. lia.
Qed.

Lemma ho_aview_frame : forall E rs (Wx : world SEGS) ma mb a,
  frame_of E rs (mrestrict (w_H Wx) ma) (mrestrict (w_H Wx) mb) -> 0 <= a < 2 ^ 64 ->
  ~ in_wrange E rs a -> aview SEGS (w_H Wx) mb a = aview SEGS (w_H Wx) ma a.
Proof.
intros E rs Wx ma mb a HF Ha Hn. unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; exact Hn)). reflexivity.
Qed.

Lemma ho_ro_keep_val : forall (Wa Wb : world SEGS) ma mb q sz a (n : nat) v,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wa) ma) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wb) mb) ->
  In (q, sz) disco_ro_ranges -> q <= a -> a + Z.of_nat n <= q + sz ->
  val_mem SEGS (mrestrict (w_H Wa) ma) a n v -> val_mem SEGS (mrestrict (w_H Wb) mb) a n v.
Proof.
intros Wa Wb ma mb q sz a n v HRa HRb Hin Hq1 Hq2 Hv k Hk.
assert (Hin' : In (q, sz) disco_ro_all) by (unfold disco_ro_all; apply in_or_app; left; exact Hin).
assert (Hrange : q <= a + Z.of_nat k < q + sz) by lia.
pose proof (ro_bytes SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wa) ma) q sz (a + Z.of_nat k) HRa
  (disco_ro_in_ro q sz (a + Z.of_nat k) Hin' Hrange) (disco_ro_unowned_at B q sz DRO Hin) Hrange) as Ha.
pose proof (ro_bytes SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wb) mb) q sz (a + Z.of_nat k) HRb
  (disco_ro_in_ro q sz (a + Z.of_nat k) Hin' Hrange) (disco_ro_unowned_at B q sz DRO Hin) Hrange) as Hb.
rewrite <- (Hv k Hk). apply (mbyte_of_aview SEGS). rewrite Hb, Ha. reflexivity.
Qed.

Record hoC : Type := mkHoC {
  c_fq : YK11.FPState; c_STK : Z; c_sp0 : Z; c_FP : list (Z * Z);
  c_ly : alayout; c_S : astate; c_W0 : world SEGS; c_mem0 : word -> option byte; c_md0 : Model;
  c_own : list (Z * Z); c_lyc : alayout; c_Sc : astate; c_W : world SEGS;
  c_memc : word -> option byte; c_k : Z; c_regs : bvmap 5 word;
  c_h : Z; c_f : Z; c_len : Z; c_now : Z; c_out : Z; c_hb : Z; c_hn : Z;
  c_H : list byte; c_FB : list byte; c_O : list byte }.

Definition ho_pre (c : hoC) : Prop :=
  (exists mdc, ajournal SEGS B (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c) (c_md0 c)
     (c_own c) (c_lyc c) (c_Sc c) (c_W c) (c_memc c) mdc (c_k c)) /\
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (c_W c)) (c_memc c)) /\
  YK0s.ret_ok (getr (c_regs c) 1) /\ 4096 <= raZ (c_regs c) /\
  getr (c_regs c) 3 = w64 (as_gp B) /\ getr (c_regs c) 4 = w64 (as_tp B) /\
  spZ (c_regs c) mod 16 = 0 /\
  c_sp0 c - c_STK c <= spZ (c_regs c) - REAC_HUNT_OBSERVE_STK /\ spZ (c_regs c) <= c_sp0 c /\
  Z.of_nat (length (frames (c_Sc c))) <= REAC_HUNT_OBSERVE_DEPTH /\
  0 <= c_len c < 2 ^ 64 /\ 0 <= c_now c < 2 ^ 64 /\ 0 <= c_out c < 2 ^ 64 /\
  0 < c_h c /\ c_h c mod 8 = 0 /\
  In (c_hb c, c_hn c) (ablocks B (c_lyc c) (c_Sc c)) /\ c_hb c <= c_h c /\
  c_h c + 480 <= c_hb c + req_size (c_hn c) /\
  (forall a, c_h c <= a < c_h c + 480 ->
     awr_byte (c_STK c) (c_sp0 c) (c_FP c) (ablocks B (c_ly c) (c_S c))
       (ablocks B (c_lyc c) (c_Sc c)) (c_lyc c) (c_own c) a) /\
  hunt_c.hunt_ok (c_H c) /\ length (c_FB c) = 50%nat /\
  garr8 SEGS (mrestrict (w_H (c_W c)) (c_memc c)) (c_h c)
    (map (fun b : byte => bv_unsigned b) (c_H c)) /\
  (50 <= c_len c -> 0 < c_f c /\
     (exists fb fn, In (fb, fn) (ablocks B (c_lyc c) (c_Sc c)) /\ fb <= c_f c /\
        c_f c + 50 <= fb + req_size fn) /\
     (c_f c + 50 <= c_h c \/ c_h c + 480 <= c_f c) /\
     garr8 SEGS (mrestrict (w_H (c_W c)) (c_memc c)) (c_f c)
       (map (fun b : byte => bv_unsigned b) (c_FB c))) /\
  (c_out c <> 0 ->
     tho_out B (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_own c) (c_lyc c) (c_Sc c)
       (c_W c) (c_memc c) (spZ (c_regs c)) (c_out c) (c_O c) /\
     (c_out c + 24 <= c_h c \/ c_h c + 480 <= c_out c) /\
     (50 <= c_len c -> c_out c + 24 <= c_f c \/ c_f c + 50 <= c_out c)) /\
  val_mem SEGS (mrestrict (w_H (c_W c)) (c_memc c)) (VAL (A_OBJ 63)) 8 reac_frame_clean_len_c.KM /\
  val_mem SEGS (mrestrict (w_H (c_W c)) (c_memc c)) (VAL (A_OBJ 64)) 8 reac_frame_clean_len_c.KT /\
  (exists ch, achain (c_lyc c) (aview SEGS (w_H (c_W c)) (c_memc c)) (spZ (c_regs c)) (s0Z (c_regs c)) ch).

Definition ho_post (c : hoC) : world SEGS -> config -> Prop :=
  treac_hunt_observe_post B (c_fq c) (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c)
    (c_mem0 c) (c_md0 c) (c_own c) (c_lyc c) (c_Sc c) (c_W c) (c_memc c) (c_k c) (c_regs c)
    (c_h c) (c_len c) (c_now c) (c_out c) (c_H c) (c_FB c) (c_O c).

Definition ho_mid (c : hoC) (fpos : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS)
  (mem2 : word -> option byte) (md2 : Model) (k2 : Z) (H2 : list byte) : Prop :=
  ajournal SEGS B (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c) (c_md0 c)
    ((1, fpos) :: c_own c) ly2 S2 W2 mem2 md2 k2 /\
  frames S2 = (1, fpos) :: frames (c_Sc c) /\
  (forall cid p, frame_addr ly2 cid p = frame_addr (c_lyc c) cid p) /\
  Permutation (ablocks B ly2 S2) (ablocks B (c_lyc c) (c_Sc c)) /\
  treac_hunt_observe_kept B (c_lyc c) (c_Sc c) (c_W c) (c_memc c) W2 mem2
    (spZ (c_regs c)) (c_h c) (c_out c) /\
  garr8 SEGS (mrestrict (w_H W2) mem2) (c_h c) (map (fun b : byte => bv_unsigned b) H2) /\
  rdword (aview SEGS (w_H W2) mem2) (frame_addr (c_lyc c) 1 fpos + 120) =
    Some (flag_addr (c_lyc c) 1 fpos) /\
  length H2 = length (c_H c) /\ k2 <= c_k c.

Definition ho_fsh (W2 : world SEGS) (mem2 : word -> option byte) (F : Z) (SH : list Z) : Prop :=
  forall i, 0 <= i < 16 -> aview SEGS (w_H W2) mem2 (SB + F / 8 + i) = Some (nth (Z.to_nat i) SH 0).

Definition ho_sreg (j : nat) : bv 5 :=
  nth j [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv 0%bv.

Definition ho_saved (c : hoC) (W2 : world SEGS) (mem2 : word -> option byte) : Prop :=
  forall j, (j < 13)%nat ->
    val_mem SEGS (mrestrict (w_H W2) mem2) (spZ (c_regs c) - 8 * (Z.of_nat j + 1)) 8
      (bv_unsigned (getr (c_regs c) (ho_sreg j))).

Definition ho_regs_mid (c : hoC) (regs2 : bvmap 5 word) (sp1 F : Z) : Prop :=
  getr regs2 2 = w64 sp1 /\ getr regs2 3 = w64 (as_gp B) /\ getr regs2 4 = w64 (as_tp B) /\
  getr regs2 8 = w64 (spZ (c_regs c)) /\ getr regs2 9 = w64 sp1 /\
  getr regs2 18 = w64 F /\ getr regs2 22 = w64 (c_h c) /\
  getr regs2 26 = w64 F /\ getr regs2 27 = w64 SB.

Definition ho_sp1 (c : hoC) (sp1 : Z) : Prop :=
  sp1 = 32 * ((spZ (c_regs c) + -160) / 32) /\
  spZ (c_regs c) - 176 <= sp1 <= spZ (c_regs c) - 160 /\ sp1 mod 32 = 0.

Definition ho_cfg (c : hoC) (regs2 : bvmap 5 word) (mem2 : word -> option byte)
  (md2 : Model) (af : Z) : config :=
  mkCfg (mkst (fx := c_fq c) regs2 (Z_to_bv 64 (BASE + af)) mem2 (seg_rom SEGS)) md2.

Definition ho_base (c : hoC) (fpos : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS)
  (mem2 : word -> option byte) (md2 : Model) (k2 : Z) (H2 : list byte)
  (regs2 : bvmap 5 word) (sp1 F : Z) : Prop :=
  ho_pre c /\ ho_mid c fpos ly2 S2 W2 mem2 md2 k2 H2 /\ ho_sp1 c sp1 /\
  F = frame_addr (c_lyc c) 1 fpos /\ ho_regs_mid c regs2 sp1 F /\ ho_saved c W2 mem2.

Definition ho_shZ : list Z := [0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0].
Definition ho_shC : list Z := [241;241;241;241;0;0;0;243;243;243;243;243;0;0;0;0].

Definition ho_L (c : hoC) : Z := reac_frame_clean_len_c.reac_frame_clean_len_model (c_len c).
Definition ho_U (c : hoC) : list byte := disco_table_c.sub (c_H c) 412 6.
Definition ho_Lk (c : hoC) : option (list byte) := Some (disco_table_c.sub (c_H c) 400 12).
Definition ho_Lk' (c : hoC) : list byte :=
  match disco_classify_c.cm_lock (c_FB c) (ho_L c) (ho_U c) (ho_Lk c) with
  | Some x => x | None => disco_table_c.sub (c_H c) 400 12 end.
Definition ho_Hcls (c : hoC) : list byte :=
  disco_table_c.sub (c_H c) 0 400 ++ ho_Lk' c ++ skipn 412 (c_H c).

Definition ho_seg_B_stmt : Prop :=
  forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F,
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 (c_H c) regs2 sp1 F ->
  getr regs2 19 = w64 (c_out c) -> getr regs2 20 = w64 (c_now c) ->
  getr regs2 21 = w64 (c_f c) -> getr regs2 24 = w64 (c_len c) ->
  ho_fsh W2 mem2 F ho_shZ ->
  (exists ch, achain ly2 (aview SEGS (w_H W2) mem2) (spZ (c_regs c) - 16) (spZ (c_regs c)) ch) ->
  (c_out c <> 0 -> garr8 SEGS (mrestrict (w_H W2) mem2) (c_out c)
     (map (fun b : byte => bv_unsigned b) (c_O c))) ->
  SRr SEGS W2 (ho_cfg c regs2 mem2 md2 0x710c) (ho_post c).

Definition ho_seg_C_stmt : Prop :=
  forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F,
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 (c_H c) regs2 sp1 F ->
  getr regs2 19 = w64 (c_out c) -> getr regs2 20 = w64 (c_now c) ->
  getr regs2 21 = w64 (c_f c) -> getr regs2 24 = w64 (c_len c) ->
  getr regs2 23 = w64 (F + 32) -> getr regs2 25 = w64 (SB + F / 8) ->
  ho_fsh W2 mem2 F ho_shC ->
  (exists ch, achain ly2 (aview SEGS (w_H W2) mem2) (spZ (c_regs c) - 16) (spZ (c_regs c)) ch) ->
  (c_out c <> 0 -> garr8 SEGS (mrestrict (w_H W2) mem2) (c_out c)
     (map (fun b : byte => bv_unsigned b) (c_O c))) ->
  SRr SEGS W2 (ho_cfg c regs2 mem2 md2 0x7178) (ho_post c).

Definition ho_seg_D_stmt : Prop :=
  forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F,
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 (ho_Hcls c) regs2 sp1 F ->
  getr regs2 19 = w64 (c_out c) ->
  getr regs2 23 = w64 (F + 32) -> getr regs2 25 = w64 (SB + F / 8) ->
  ho_fsh W2 mem2 F ho_shC ->
  disco_classify_c.cm_ret (c_FB c) (ho_L c) (ho_U c) (ho_Lk c) <> 0 ->
  hunt_c.hunt_ok (ho_Hcls c) ->
  (c_out c <> 0 -> garr8 SEGS (mrestrict (w_H W2) mem2) (c_out c)
     (map (fun b : byte => bv_unsigned b) (c_O c))) ->
  SRr SEGS W2 (ho_cfg c regs2 mem2 md2 0x719c) (ho_post c).

Definition ho_seg_E_stmt : Prop :=
  forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F,
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 (ho_Hcls c) regs2 sp1 F ->
  getr regs2 19 = w64 (c_out c) -> getr regs2 20 = w64 (c_now c) ->
  getr regs2 23 = w64 (F + 32) -> getr regs2 25 = w64 (SB + F / 8) ->
  ho_fsh W2 mem2 F ho_shC ->
  disco_classify_c.cm_ret (c_FB c) (ho_L c) (ho_U c) (ho_Lk c) = 0 ->
  hunt_c.hunt_ok (ho_Hcls c) ->
  garr8 SEGS (mrestrict (w_H W2) mem2) (F + 32)
    (map (fun b : byte => bv_unsigned b) (disco_classify_c.sight (c_FB c) (ho_L c))) ->
  (c_out c <> 0 -> garr8 SEGS (mrestrict (w_H W2) mem2) (c_out c)
     (map (fun b : byte => bv_unsigned b) (c_O c))) ->
  SRr SEGS W2 (ho_cfg c regs2 mem2 md2 0x7210) (ho_post c).

Definition ho_seg_F_stmt : Prop :=
  forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F H2 T' G ret,
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F ->
  getr regs2 10 = w64 ret -> 0 <= ret < 2 ^ 64 ->
  getr regs2 19 = w64 (c_out c) ->
  getr regs2 21 = w64 (c_h c + 384) -> getr regs2 24 = w64 (SB + (c_h c + 384) / 8) ->
  getr regs2 23 = w64 (F + 32) -> getr regs2 25 = w64 (SB + F / 8) ->
  ho_fsh W2 mem2 F ho_shC ->
  hunt_c.hunt_ok H2 ->
  H2 = T' ++ skipn 400 H2 -> length T' = 400%nat ->
  garr8 SEGS (mrestrict (w_H W2) mem2) (F + 32) (map (fun b : byte => bv_unsigned b) G) ->
  length G = 24%nat ->
  reac_disco_table_observe_c.observe_model (disco_table_c.sub (c_H c) 0 400) G 0 (c_now c) T' ret ->
  disco_classify_c.cm_ret (c_FB c) (ho_L c) (ho_U c) (ho_Lk c) = 0 ->
  G = disco_classify_c.sight (c_FB c) (ho_L c) ->
  skipn 400 H2 = ho_Lk' c ++ disco_table_c.sub (c_H c) 412 12 ++
    (if disco_table_c.n_of (disco_table_c.sub (c_H c) 0 400) =? 0
     then Mem.le8 (Z_to_bv 64 (c_now c)) else disco_table_c.sub (c_H c) 424 8) ++ skipn 432 (c_H c) ->
  (c_out c <> 0 -> garr8 SEGS (mrestrict (w_H W2) mem2) (c_out c)
     (map (fun b : byte => bv_unsigned b) (c_O c))) ->
  SRr SEGS W2 (ho_cfg c regs2 mem2 md2 0x7258) (ho_post c).

Definition ho_seg_G_stmt : Prop :=
  forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F H2 T' G r nn ii,
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F ->
  getr regs2 20 = w64 r -> (r = 0 \/ r = 1) ->
  getr regs2 19 = w64 (48 * nn) -> getr regs2 24 = w64 (48 * ii) ->
  getr regs2 23 = w64 (F + 32) -> getr regs2 25 = w64 (SB + F / 8) ->
  ho_fsh W2 mem2 F ho_shC ->
  hunt_c.hunt_ok H2 ->
  H2 = T' ++ skipn 400 H2 -> length T' = 400%nat ->
  nn = disco_table_c.n_of T' -> 0 <= ii < nn -> 0 <= nn <= 8 ->
  garr8 SEGS (mrestrict (w_H W2) mem2) (F + 32) (map (fun b : byte => bv_unsigned b) G) ->
  length G = 24%nat ->
  (forall j, 0 <= j < ii -> disco_table_c.mac_of T' j <> disco_table_c.s_mac G) ->
  c_out c <> 0 ->
  rdword (aview SEGS (w_H W2) mem2) (sp1 + 24) = Some (c_out c) ->
  garr8 SEGS (mrestrict (w_H W2) mem2) (c_out c) (map (fun b : byte => bv_unsigned b) G) ->
  (forall A, reac_hunt_observe_c.ho_answer T' G A ->
     garr8 SEGS (mrestrict (w_H W2) mem2) (c_out c) (map (fun b : byte => bv_unsigned b) G) ->
     tho_model (c_H c) (c_FB c) (c_O c) (c_len c) (c_now c) (c_out c) r H2
       (fun A' => A' = A)) ->
  SRr SEGS W2 (ho_cfg c regs2 mem2 md2 0x7294) (ho_post c).

Definition ho_seg_H_stmt : Prop :=
  forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F H2 T' G r ii,
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F ->
  getr regs2 20 = w64 r -> (r = 0 \/ r = 1) ->
  getr regs2 21 = w64 (c_h c + 48 * ii) ->
  getr regs2 23 = w64 (F + 32) -> getr regs2 25 = w64 (SB + F / 8) ->
  ho_fsh W2 mem2 F ho_shC ->
  hunt_c.hunt_ok H2 ->
  H2 = T' ++ skipn 400 H2 -> length T' = 400%nat ->
  0 <= ii < disco_table_c.n_of T' ->
  disco_table_c.mac_of T' ii = disco_table_c.s_mac G ->
  (forall j, 0 <= j < ii -> disco_table_c.mac_of T' j <> disco_table_c.s_mac G) ->
  garr8 SEGS (mrestrict (w_H W2) mem2) (F + 32) (map (fun b : byte => bv_unsigned b) G) ->
  length G = 24%nat ->
  c_out c <> 0 ->
  rdword (aview SEGS (w_H W2) mem2) (sp1 + 24) = Some (c_out c) ->
  garr8 SEGS (mrestrict (w_H W2) mem2) (c_out c) (map (fun b : byte => bv_unsigned b) G) ->
  (forall A, A = reac_hunt_observe_c.ho_entry T' G ii ->
     tho_model (c_H c) (c_FB c) (c_O c) (c_len c) (c_now c) (c_out c) r H2 (fun A' => A' = A)) ->
  SRr SEGS W2 (ho_cfg c regs2 mem2 md2 0x732c) (ho_post c).

Definition ho_seg_T_stmt : Prop :=
  forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F H2 r,
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F ->
  getr regs2 20 = w64 r -> (r = -1 \/ r = 0 \/ r = 1) ->
  getr regs2 25 = w64 (SB + F / 8) ->
  ho_fsh W2 mem2 F ho_shC ->
  hunt_c.hunt_ok H2 ->
  tho_model (c_H c) (c_FB c) (c_O c) (c_len c) (c_now c) (c_out c) r H2
    (fun A => garr8 SEGS (mrestrict (w_H W2) mem2) (c_out c)
       (map (fun b : byte => bv_unsigned b) A)) ->
  SRr SEGS W2 (ho_cfg c regs2 mem2 md2 0x71a0) (ho_post c).

End h.
End f.
End d.
