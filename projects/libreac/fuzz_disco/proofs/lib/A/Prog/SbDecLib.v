(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 470 of its 502 lines of code are new or changed and 37 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop YI0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require sb_dec_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Definition sbd_wr (lyc : alayout) (Sc : astate) (slo shi : Z) (Er : Z -> Prop) (a : Z) : Prop :=
  ~ in_img SEGS a /\
  ((alloc_ceiling <= a /\ slo <= a < shi) \/ Er a \/
   (0 <= a < alloc_ceiling /\
    (forall b m, In (b, m) (ablocks B lyc Sc) -> ~ (b <= a < b + req_size m)) /\
    (forall cid pos, In (cid, pos) (frames Sc) ->
       ~ in_zr a (frame_rng lyc (cid, pos)) /\
       ~ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)))).
Definition sbd_kept (lyc : alayout) (Sc : astate) (W : world SEGS) (memc mem' : word -> option byte)
  (slo shi : Z) (Er : Z -> Prop) : Prop :=
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> ~ Er a ->
     aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) /\
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ Er (b + i) ->
     aview SEGS (w_H W) mem' (b + i) = aview SEGS (w_H W) memc (b + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) /\
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     ~ Er a -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < shi) ->
     apresent (w_H W) memc a -> apresent (w_H W) mem' a) /\
  (forall a, slo <= a < shi -> apresent (w_H W) mem' a).
Lemma sbd_kept_refl : forall lyc Sc W memc slo shi Er,
  (forall a, slo <= a < shi -> apresent (w_H W) memc a) -> sbd_kept lyc Sc W memc memc slo shi Er.
Proof.
intros lyc Sc W memc slo shi Er Hp.
split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros; reflexivity|]. split; [intros; assumption | exact Hp].
Qed.
Lemma shadow_cell_bound : forall F b, 0 <= F -> 0 <= b -> F + b < 2 ^ 47 ->
  SHADOW_OFF <= shadow_addr F /\ shadow_addr F + b / 8 < kHighMemBeg.
Proof.
intros F b H0 H1 H2. unfold shadow_addr, SHADOW_OFF, kHighMemBeg.
assert (F / 8 + b / 8 <= (F + b) / 8).
{ apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le F 8 ltac:(lia)). pose proof (Z.mul_div_le b 8 ltac:(lia)). lia. }
assert ((F + b) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
assert (0 <= F / 8) by (apply Z.div_pos; lia). assert (0 <= b / 8) by (apply Z.div_pos; lia). lia.
Qed.
Lemma shadow_disj : forall F G b c, F mod 64 = 0 -> G mod 64 = 0 -> b mod 64 = 0 -> c mod 64 = 0 ->
  0 <= F -> 0 <= G -> 0 <= b -> 0 <= c -> (F + b <= G \/ G + c <= F) ->
  forall a, shadow_addr F <= a < shadow_addr F + b / 8 -> shadow_addr G <= a < shadow_addr G + c / 8 -> False.
Proof.
intros F G b c HF HG Hb Hc F0 G0 b0 c0 Hd a Ha1 Ha2. unfold shadow_addr in *.
assert (E8 : forall x, x mod 64 = 0 -> x / 8 = 8 * (x / 64)).
{ intros x Hx. rewrite (Z.div_mod x 64) at 1 by lia. rewrite Hx, Z.add_0_r.
  replace (64 * (x / 64)) with ((8 * (x / 64)) * 8) by lia. apply Z.div_mul. lia. }
assert (E64 : forall x, x mod 64 = 0 -> x = 64 * (x / 64)).
{ intros x Hx. rewrite (Z.div_mod x 64) at 1 by lia. rewrite Hx. lia. }
rewrite (E8 F HF), (E8 b Hb) in Ha1. rewrite (E8 G HG), (E8 c Hc) in Ha2.
rewrite (E64 F HF), (E64 G HG), (E64 b Hb), (E64 c Hc) in Hd. lia.
Qed.
Lemma app_not_shadow : forall a F b, 0 <= F -> 0 <= b -> F + b < 2 ^ 47 -> in_app a 1 ->
  ~ (shadow_addr F <= a < shadow_addr F + b / 8).
Proof.
intros a F b H0 H1 H2 Ha Hs. destruct (shadow_cell_bound F b H0 H1 H2) as [S1 S2].
unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
Lemma sbd_kept_run : forall lyc Sc W memc mem1 mem2 mdc slo shi Er (Wr : Z -> Prop),
  AR SEGS B lyc Sc W memc mdc ->
  sbd_kept lyc Sc W memc mem1 slo shi Er ->
  (forall x : word, ~ Wr (bv_unsigned x) -> mrestrict (w_H W) mem2 x = mrestrict (w_H W) mem1 x) ->
  mem_grows (mrestrict (w_H W) mem1) (mrestrict (w_H W) mem2) ->
  (forall a, 0 <= a < 2 ^ 64 -> Wr a -> sbd_wr lyc Sc slo shi Er a) ->
  sbd_kept lyc Sc W memc mem2 slo shi Er.
Proof.
intros lyc Sc W memc mem1 mem2 mdc slo shi Er Wr HAR (K1 & K2 & K3 & K4 & K5 & K6) Hfr Hgr Hwr.
pose proof asan_consts as (C1 & _).
assert (EQ : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem1 a).
{ intros a Ha Hn. apply aview_eq_of. apply Hfr. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. exact Hn. }
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hs He. rewrite <- (K1 a Ha Hs He). apply EQ; [lia|]. intros Hw.
  destruct (Hwr a ltac:(lia) Hw) as (_ & [[_ Hs'] | [He' | [Hl _]]]); [exact (Hs Hs') | exact (He He') | lia].
- intros b m i Hin Hi He. rewrite <- (K2 b m i Hin Hi He).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & H4096 & Hbc & _).
  apply EQ; [lia|]. intros Hw.
  destruct (Hwr (b + i) ltac:(lia) Hw) as (_ & [[Hc _] | [He' | [_ [Hnb _]]]]);
  [lia | exact (He He') | exact (Hnb b m Hin ltac:(lia))].
- intros a Himg Hno Herr. rewrite <- (K3 a Himg Hno Herr). pose proof (pa_segs_low a Himg) as Hlo.
  apply EQ; [unfold kLowMemEnd in Hlo; lia|]. intros Hw. exact (proj1 (Hwr a ltac:(unfold kLowMemEnd in Hlo; lia) Hw) Himg).
- intros cid pos a Hin Hr He. rewrite <- (K4 cid pos a Hin Hr He).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hin) as (H4096 & Hfc & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hb0.
  destruct (shadow_cell_bound (frame_addr lyc cid pos) (fs_frame_bytes cid) ltac:(lia) Hb0 ltac:(lia)) as [S1 S2].
  assert (Ha : 0 <= a < alloc_ceiling).
  { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; unfold SHADOW_OFF, kHighMemBeg in *; lia. }
  apply EQ; [lia|]. intros Hw.
  destruct (Hwr a ltac:(lia) Hw) as (_ & [[Hc _] | [He' | [_ [_ Hnf]]]]); [lia | exact (He He') |].
  destruct (Hnf cid pos Hin) as [N1 N2]. destruct Hr; contradiction.
- intros a Ha Hs Hp. eapply apresent_grows; [exact Hgr | exact (K5 a Ha Hs Hp)].
- intros a Ha. eapply apresent_grows; [exact Hgr | exact (K6 a Ha)].
Qed.
Lemma sbd_kept_call : forall lyc Sc W memc memT mem2 slo shi Er slo' shi',
  alloc_ceiling <= slo -> shi <= 2 ^ 64 -> slo <= slo' -> shi' <= shi ->
  sbd_kept lyc Sc W memc memT slo shi Er ->
  acall_kept SEGS B lyc Sc W memT W mem2 slo' shi' (fun _ => False) ->
  sbd_kept lyc Sc W memc mem2 slo shi Er.
Proof.
intros lyc Sc W memc memT mem2 slo shi Er slo' shi' Hc Hs1 H1 H2 (K1 & K2 & K3 & K4 & K5 & K6) (A1 & A2 & A3 & A4 & A5 & A6).
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hs He. rewrite (A1 a Ha ltac:(lia)). exact (K1 a Ha Hs He).
- intros b m i Hin Hi He. rewrite (A2 b m i Hin Hi (fun x => x)). exact (K2 b m i Hin Hi He).
- intros a Q1 Q2 Q3. rewrite (A3 a Q1 Q2 Q3). exact (K3 a Q1 Q2 Q3).
- intros cid pos a Hin Hr He. rewrite (A4 cid pos a Hin Hr (fun x => x)). exact (K4 cid pos a Hin Hr He).
- intros a Ha Hs Hp. apply (A5 a Ha ltac:(lia)). exact (K5 a Ha Hs Hp).
- intros a Ha. destruct (Z_lt_le_dec a slo') as [Hl|Hl]; [|destruct (Z_lt_le_dec a shi') as [Hl2|Hl2]].
  + apply (A5 a ltac:(lia) ltac:(lia)). exact (K6 a Ha).
  + exact (A6 a ltac:(lia)).
  + apply (A5 a ltac:(lia) ltac:(lia)). exact (K6 a Ha).
Qed.
Lemma region_kept_awr_aj : forall E lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) nn lo hi wlo whi cs b
  STK sp0 FP (ly : alayout) S own,
  acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi Er ->
  frames Sc = own ++ frames S -> alloc_ceiling <= sp0 - STK -> sp0 <= 2 ^ 47 ->
  bv_unsigned (ew E nn) = b ->
  (forall a, b + lo <= a < b + hi -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  (forall a, b + lo <= a < b + hi -> ~ (slo <= a < shi)) ->
  (forall a, b + lo <= a < b + hi -> ~ Er a) ->
  (forall a, b + wlo <= a < b + whi -> apresent (w_H W2) mem2 a) ->
  region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some nn) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er nn lo hi wlo whi cs b STK sp0 FP ly S own
  (K1 & K2 & _ & K4 & _) Hfrs Hc H47 Hn Hawr Hst Her Hpres.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS).
  destruct (Hawr a Ha) as [Hs | [[_ (b' & m' & Hb' & Hr)] | [(b' & m' & Hb' & _ & Hr) | (cid & pos & Hown & Hr)]]].
  + apply K1; [lia | exact (Hst a Ha)].
  + replace a with (b' + (a - b')) by lia. apply (K2 b' m' (a - b') Hb'); [lia|]. replace (b' + (a - b')) with a by lia. exact (Her a Ha).
  + replace a with (b' + (a - b')) by lia. apply (K2 b' m' (a - b') Hb'); [lia|]. replace (b' + (a - b')) with a by lia. exact (Her a Ha).
  + apply (K4 cid pos a); [rewrite Hfrs; apply in_or_app; left; exact Hown | unfold frame_rng; cbn [fst snd]; exact Hr | exact (Her a Ha)].
- intros _. apply (apresent_writable SEGS). apply Hpres. exact Ha.
Qed.
Lemma awr_not_new : forall STK sp0 FP ly S own lyc Sc S2 W2 mem2 md2 cid pos a,
  frames Sc = own ++ frames S -> alloc_ceiling <= sp0 - STK ->
  AR SEGS B lyc S2 W2 mem2 md2 -> frames S2 = (cid, pos) :: frames Sc -> ablocks B lyc S2 = ablocks B lyc Sc ->
  0 <= cid ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
  ~ (frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid) /\
  ~ (shadow_addr (frame_addr lyc cid pos) <= a < shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8) /\
  a <> flag_addr lyc cid pos.
Proof.
intros STK sp0 FP ly S own lyc Sc S2 W2 mem2 md2 cid pos a Hfrs Hc HAR2 Hfrs2 Eab Hcid Haw.
assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR2 Hin2) as (HF4096 & HFc & HFapp).
destruct (al_flag _ _ LAWS _ _ _ _ _ cid pos HAR2 Hin2) as (_ & HFLown & _ & HFLc).
destruct (frame_al64 SEGS B _ _ _ _ _ cid pos HAR2 Hin2) as (HFa & HFb & HF64).
pose proof asan_consts as (C1 & _).
set (F := frame_addr lyc cid pos) in *.
destruct (shadow_cell_bound F (fs_frame_bytes cid) ltac:(lia) ltac:(lia) ltac:(lia)) as [S1 S2'].
destruct Haw as [Hs | [[_ (b & m & Hb & Hr)] | [(b & m & Hb & _ & Hr) | (cid' & pos' & Hown & Hr)]]].
- unfold SHADOW_OFF, kHighMemBeg in *. split; [lia|]. split; [lia|]. lia.
- rewrite <- Eab in Hb. pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m cid pos HAR2 Hb Hin2) as Hd.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hb) as (_ & _ & _ & Hbapp & Hbo & _).
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. fold F in Hd.
  split; [lia|]. split.
  + apply (app_not_shadow a F (fs_frame_bytes cid)); [lia | lia | lia |]. unfold in_app in *. lia.
  + intros ->. exact (proj2 (Hbo _ Hr) HFLown).
- rewrite <- Eab in Hb. pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m cid pos HAR2 Hb Hin2) as Hd.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hb) as (_ & _ & _ & Hbapp & Hbo & _).
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. fold F in Hd.
  split; [lia|]. split.
  + apply (app_not_shadow a F (fs_frame_bytes cid)); [lia | lia | lia |]. unfold in_app in *. lia.
  + intros ->. exact (proj2 (Hbo _ Hr) HFLown).
- assert (Hin' : In (cid', pos') (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
  assert (Hin2' : In (cid', pos') (frames S2)) by (rewrite Hfrs2; right; exact Hin').
  destruct (al_frames _ _ LAWS _ _ _ _ _ cid' pos' HAR2 Hin2') as (_ & HGapp & HGo & HGso).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid' pos' HAR2 Hin2') as (HG4096 & HGc & _).
  destruct (frame_al64 SEGS B _ _ _ _ _ cid' pos' HAR2 Hin2') as (HGa & HGb & HG64).
  apply in_split in Hin' as (l2 & l3 & El).
  pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (cid, pos) (cid', pos') [] l2 l3 HAR2
    ltac:(rewrite Hfrs2, El; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. fold F in Hd.
  set (G := frame_addr lyc cid' pos') in *.
  destruct Hr as [Hr | Hr]; unfold in_zr in Hr; cbn [fst snd] in Hr.
  + split; [lia|]. split.
    * apply (app_not_shadow a F (fs_frame_bytes cid)); [lia | lia | lia |]. unfold in_app in *. lia.
    * intros ->. exact (proj2 (HGo _ Hr) HFLown).
  + pose proof (fs_frame_bytes_nonneg cid') as Hb'.
    split; [intros Hf; apply (app_not_shadow a G (fs_frame_bytes cid')); [lia | lia | lia | unfold in_app in *; lia | lia]|].
    split; [intros Hs; exact (shadow_disj F G _ _ HFa HGa HFb HGb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hd a Hs Hr)|].
    intros ->. assert (Hi : 0 <= flag_addr lyc cid pos - shadow_addr G < fs_frame_bytes cid' / 8) by lia.
    pose proof (proj2 (HGso _ Hi)) as Hno. replace (shadow_addr G + (flag_addr lyc cid pos - shadow_addr G)) with (flag_addr lyc cid pos) in Hno by lia.
    exact (Hno HFLown).
Qed.
Lemma new_fresh : forall lyc Sc S2 W2 mem2 md2 cid pos slo shi (Er : Z -> Prop) a,
  AR SEGS B lyc S2 W2 mem2 md2 -> frames S2 = (cid, pos) :: frames Sc -> ablocks B lyc S2 = ablocks B lyc Sc ->
  0 <= cid ->
  (frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid \/
   shadow_addr (frame_addr lyc cid pos) <= a < shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8 \/
   a = flag_addr lyc cid pos) ->
  sbd_wr lyc Sc slo shi Er a.
Proof.
intros lyc Sc S2 W2 mem2 md2 cid pos slo shi Er a HAR2 Hfrs2 Eab Hcid Ha.
assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR2 Hin2) as (HF4096 & HFc & HFapp).
destruct (al_flag _ _ LAWS _ _ _ _ _ cid pos HAR2 Hin2) as (_ & HFLown & HFLapp & HFLc).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR2 Hin2) as (_ & _ & HFo & HFso).
destruct (frame_al64 SEGS B _ _ _ _ _ cid pos HAR2 Hin2) as (HFa & HFb & HF64).
pose proof asan_consts as (C1 & _).
set (F := frame_addr lyc cid pos) in *.
destruct (shadow_cell_bound F (fs_frame_bytes cid) ltac:(lia) ltac:(lia) ltac:(lia)) as [S1 S2'].
split.
{ intros Himg. destruct Ha as [Ha | [Ha | Ha]].
  - apply (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR2 (or_intror (or_introl (ex_intro _ cid (ex_intro _ pos (conj Hin2 Ha))))))). exact Himg.
  - pose proof (pa_segs_low a Himg). unfold kLowMemEnd, SHADOW_OFF in *. lia.
  - apply (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR2 (or_intror (or_intror (ex_intro _ cid (ex_intro _ pos (conj Hin2 Ha))))))). exact Himg. }
right. right. split; [unfold in_app, SHADOW_OFF, kHighMemBeg in *; destruct Ha as [Ha | [Ha | ->]]; lia|].
split.
- intros b m Hb Hr. rewrite <- Eab in Hb.
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m cid pos HAR2 Hb Hin2) as Hd.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hb) as (_ & _ & _ & Hbapp & Hbo & _).
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. fold F in Hd.
  destruct Ha as [Ha | [Ha | ->]]; [lia | |].
  + apply (app_not_shadow a F (fs_frame_bytes cid)); [lia | lia | lia | unfold in_app in *; lia | exact Ha].
  + exact (proj2 (Hbo _ Hr) HFLown).
- intros cid' pos' Hin'.
  assert (Hin2' : In (cid', pos') (frames S2)) by (rewrite Hfrs2; right; exact Hin').
  destruct (al_frames _ _ LAWS _ _ _ _ _ cid' pos' HAR2 Hin2') as (_ & HGapp & HGo & HGso).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid' pos' HAR2 Hin2') as (HG4096 & HGc & _).
  destruct (frame_al64 SEGS B _ _ _ _ _ cid' pos' HAR2 Hin2') as (HGa & HGb & HG64).
  apply in_split in Hin' as (l2 & l3 & El).
  pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (cid, pos) (cid', pos') [] l2 l3 HAR2
    ltac:(rewrite Hfrs2, El; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. fold F in Hd.
  set (G := frame_addr lyc cid' pos') in *.
  unfold in_zr, frame_rng. cbn [fst snd]. fold G.
  destruct Ha as [Ha | [Ha | ->]].
  + split; [lia|]. intros Hs. apply (app_not_shadow a G (fs_frame_bytes cid')); [lia | lia | lia | unfold in_app in *; lia | exact Hs].
  + split; [intros Hf; apply (app_not_shadow a F (fs_frame_bytes cid)); [lia | lia | lia | unfold in_app in *; lia | exact Ha]|].
    intros Hs. exact (shadow_disj F G _ _ HFa HGa HFb HGb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hd a Ha Hs).
  + split.
    * intros Hf. exact (proj2 (HGo _ Hf) HFLown).
    * intros Hs. assert (Hi : 0 <= flag_addr lyc cid pos - shadow_addr G < fs_frame_bytes cid' / 8) by lia.
      pose proof (proj2 (HGso _ Hi)) as Hno.
      replace (shadow_addr G + (flag_addr lyc cid pos - shadow_addr G)) with (flag_addr lyc cid pos) in Hno by lia.
      exact (Hno HFLown).
Qed.
Lemma div8_page : forall z, z mod 4096 = 0 -> z = 8 * (z / 8).
Proof.
intros z H. pose proof (Z.div_mod z 4096 ltac:(lia)) as D. rewrite H, Z.add_0_r in D.
rewrite D at 2. replace (4096 * (z / 4096)) with ((512 * (z / 4096)) * 8) by lia. rewrite Z.div_mul by lia. lia.
Qed.
Lemma div8_64 : forall z, z mod 64 = 0 -> z = 8 * (z / 8).
Proof.
intros z H. pose proof (Z.div_mod z 64 ltac:(lia)) as D. rewrite H, Z.add_0_r in D.
rewrite D at 2. replace (64 * (z / 64)) with ((8 * (z / 64)) * 8) by lia. rewrite Z.div_mul by lia. lia.
Qed.
Lemma awr_addr_cur : forall STK sp0 FP (ly : alayout) S own lyc Sc W memc mdc S' mem' md' slo shi (Er : Z -> Prop) x,
  frames Sc = own ++ frames S -> astk_ok STK ly sp0 ->
  ly_stk_lo lyc = ly_stk_lo ly -> ly_stk_hi lyc = ly_stk_hi ly ->
  AR SEGS B lyc Sc W memc mdc -> AR SEGS B lyc S' W mem' md' -> ablocks B lyc S' = ablocks B lyc Sc ->
  sbd_kept lyc Sc W memc mem' slo shi Er -> ~ Er (shadow_of_addr SHADOW_OFF x) -> (x < kLowShadowBeg \/ kHighMemBeg <= x) ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF x 1 ->
  range_addressable (aview SEGS (w_H W) mem') SHADOW_OFF x 1.
Proof.
intros STK sp0 FP ly S own lyc Sc W memc mdc S' mem' md' slo shi Er x Hfrs Hstk Elo Ehi HAR HAR' Eab
  (_ & _ & _ & K4 & _) HnE Happ Haw HRA y Hy.
assert (Hyx : y = x) by lia. subst y.
pose proof (am_layout _ _ _ _ (proj1 HAR')) as LO. destruct (lo_top _ LO) as (_ & _ & _ & _ & Plo & Phi & _).
destruct Hstk as (_ & _ & Hc & Hslo & Hshi & _).
destruct Haw as [Hs | [[_ (b & m & Hb & Hr)] | [(b & m & Hb & _ & Hr) | (cid & pos & Hown & Hr)]]].
- pose proof (al_zshadow _ _ LAWS _ _ _ _ _ (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc) HAR' (or_introl eq_refl)) as Hz.
  exists 0. split; [|left; reflexivity]. cbn [fst snd] in Hz.
  pose proof (div8_page _ Plo) as Elo8. pose proof (div8_page _ Phi) as Ehi8.
  set (lo := ly_stk_lo lyc) in *. set (hi := ly_stk_hi lyc) in *.
  assert (L1 : lo <= x < hi) by lia.
  assert (Q1 : lo / 8 <= x / 8) by (apply Z.div_le_mono; lia).
  assert (Q2 : x / 8 < hi / 8) by (apply Z.div_lt_upper_bound; lia).
  assert (Q3 : (hi - lo) / 8 = hi / 8 - lo / 8).
  { rewrite Elo8 at 1. rewrite Ehi8 at 1. replace (8 * (hi / 8) - 8 * (lo / 8)) with ((hi / 8 - lo / 8) * 8) by lia.
    apply Z.div_mul. lia. }
  specialize (Hz (x / 8 - lo / 8) ltac:(lia)). unfold shadow_of_addr in *.
  replace (SHADOW_OFF + lo / 8 + (x / 8 - lo / 8)) with (SHADOW_OFF + x / 8) in Hz by lia. exact Hz.
- rewrite <- Eab in Hb. destruct (al_shadow _ _ LAWS _ _ _ _ _ b m HAR' Hb) as [(Hb8 & Hn0 & Hcells) _].
  set (nn := req_size m) in *.
  pose proof (Z.div_mod (x - b) 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound (x - b) 8 ltac:(lia)) as Mx.
  pose proof (Z.div_mod nn 8 ltac:(lia)) as Dn. pose proof (Z.mod_pos_bound nn 8 ltac:(lia)) as Mn.
  pose proof (Z.div_mod (nn + 7) 8 ltac:(lia)) as Dn7. pose proof (Z.mod_pos_bound (nn + 7) 8 ltac:(lia)) as Mn7.
  pose proof (Z.div_mod b 8 ltac:(lia)) as Db. rewrite Hb8, Z.add_0_r in Db.
  assert (Exd : x / 8 = b / 8 + (x - b) / 8).
  { replace x with ((x - b) + (b / 8) * 8) at 1 by lia. rewrite Z.div_add by lia. lia. }
  assert (Exm : x mod 8 = (x - b) mod 8).
  { replace x with ((x - b) + (b / 8) * 8) at 1 by lia. apply Z.mod_add. lia. }
  set (i := (x - b) / 8) in *.
  exists (if i <? nn / 8 then 0 else nn mod 8). split.
  + unfold shadow_of_addr in *. replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + b / 8 + i) by lia.
    apply Hcells. lia.
  + unfold saddr_ok. destruct (Z.ltb_spec i (nn / 8)); [left; reflexivity | right]. lia.
- rewrite <- Eab in Hb. destruct (al_shadow _ _ LAWS _ _ _ _ _ b m HAR' Hb) as [(Hb8 & Hn0 & Hcells) _].
  set (nn := req_size m) in *.
  pose proof (Z.div_mod (x - b) 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound (x - b) 8 ltac:(lia)) as Mx.
  pose proof (Z.div_mod nn 8 ltac:(lia)) as Dn. pose proof (Z.mod_pos_bound nn 8 ltac:(lia)) as Mn.
  pose proof (Z.div_mod (nn + 7) 8 ltac:(lia)) as Dn7. pose proof (Z.mod_pos_bound (nn + 7) 8 ltac:(lia)) as Mn7.
  pose proof (Z.div_mod b 8 ltac:(lia)) as Db. rewrite Hb8, Z.add_0_r in Db.
  assert (Exd : x / 8 = b / 8 + (x - b) / 8).
  { replace x with ((x - b) + (b / 8) * 8) at 1 by lia. rewrite Z.div_add by lia. lia. }
  assert (Exm : x mod 8 = (x - b) mod 8).
  { replace x with ((x - b) + (b / 8) * 8) at 1 by lia. apply Z.mod_add. lia. }
  set (i := (x - b) / 8) in *.
  exists (if i <? nn / 8 then 0 else nn mod 8). split.
  + unfold shadow_of_addr in *. replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + b / 8 + i) by lia.
    apply Hcells. lia.
  + unfold saddr_ok. destruct (Z.ltb_spec i (nn / 8)); [left; reflexivity | right]. lia.
- assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hin) as (HF4096 & HFc & _).
  destruct (frame_al64 SEGS B _ _ _ _ _ cid pos HAR Hin) as (HFa & HFb & HF64).
  pose proof asan_consts as (C1 & _).
  set (F := frame_addr lyc cid pos) in *.
  destruct Hr as [Hr | Hr]; unfold in_zr in Hr; cbn [fst snd] in Hr.
  + destruct (HRA x ltac:(lia)) as (s & Hs & Hok). exists s. split; [|exact Hok].
    rewrite (K4 cid pos (shadow_of_addr SHADOW_OFF x) Hin); [exact Hs | right | exact HnE].
    unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd]. fold F.
    pose proof (div8_64 F HFa) as EF8. pose proof (div8_64 _ HFb) as Eb8.
    assert (Q1 : F / 8 <= x / 8) by (apply Z.div_le_mono; lia).
    assert (Q2 : x / 8 < F / 8 + fs_frame_bytes cid / 8) by (apply Z.div_lt_upper_bound; lia).
    lia.
  + exfalso. pose proof (fs_frame_bytes_nonneg cid) as Hb0.
    destruct (shadow_cell_bound F (fs_frame_bytes cid) ltac:(lia) Hb0 ltac:(lia)) as [S1 S2].
    unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
Lemma range_disj_of_pt : forall lo n F m, (forall a, lo <= a < lo + n -> ~ (F <= a < F + m)) -> 0 < n -> 0 < m ->
  lo + n <= F \/ F + m <= lo.
Proof.
intros lo n F m H Hn Hm. destruct (Z_le_gt_dec (lo + n) F) as [H1|H1]; [left; exact H1|].
destruct (Z_le_gt_dec (F + m) lo) as [H2|H2]; [right; exact H2|].
exfalso. apply (H (Z.max lo F)); lia.
Qed.
Lemma awr_present : forall STK sp0 FP (ly : alayout) S own lyc Sc S2 W2 mem2 md2 a,
  frames Sc = own ++ frames S -> (forall c, In c (frames Sc) -> In c (frames S2)) ->
  AR SEGS B lyc S2 W2 mem2 md2 -> ablocks B lyc S2 = ablocks B lyc Sc ->
  (forall x, sp0 - STK <= x < sp0 -> apresent (w_H W2) mem2 x) ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
  apresent (w_H W2) mem2 a.
Proof.
intros STK sp0 FP ly S own lyc Sc S2 W2 mem2 md2 a Hfrs Hsub HAR2 Eab Hst Haw.
destruct Haw as [Hs | [[_ (b & m & Hb & Hr)] | [(b & m & Hb & _ & Hr) | (cid & pos & Hown & Hr)]]].
- exact (Hst a Hs).
- rewrite <- Eab in Hb. destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hb) as (_ & _ & _ & _ & Hbp & _). exact (proj1 (Hbp a Hr)).
- rewrite <- Eab in Hb. destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hb) as (_ & _ & _ & _ & Hbp & _). exact (proj1 (Hbp a Hr)).
- assert (Hin : In (cid, pos) (frames S2)) by (apply Hsub; rewrite Hfrs; apply in_or_app; left; exact Hown).
  destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR2 Hin) as (_ & _ & HFp & HFsp).
  destruct Hr as [Hr | Hr]; unfold in_zr in Hr; cbn [fst snd] in Hr.
  + exact (proj1 (HFp a Hr)).
  + pose proof (proj1 (HFsp (a - shadow_addr (frame_addr lyc cid pos)) ltac:(lia))) as Hp.
    replace (shadow_addr (frame_addr lyc cid pos) + (a - shadow_addr (frame_addr lyc cid pos))) with a in Hp by lia. exact Hp.
Qed.
Definition sbd_Er (A v md p cap n : Z) (a : Z) : Prop :=
  (A + 16 <= a < A + 28) \/
  (0 < sb_dec_c.sb_dec_room cap n /\ p + n <= a < p + n + sb_dec_c.sb_dec_acc v md cap n).
Ltac sbd_awr_rec hd :=
  lazymatch goal with
  | |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
  | |- awr_ok _ (YP09.mkRegion _ _ _ ?wlo ?whi _ :: _) _ _ _ _ _ _ _ =>
    first [ lazymatch (eval vm_compute in (Z.leb whi wlo)) with true => apply awr_ok_cons_ro; [clear; cbn; lia|] end
          | hd
          | match goal with |- awr_ok _ (?r :: _) _ _ _ _ _ _ _ => idtac "AWR-HEAD" r end; fail 1 "sbd_awr: no rule" ];
    sbd_awr_rec hd
  end.
Ltac sbd_awr hd :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  sbd_awr_rec hd.
Ltac sbd_hd AG sp0 spv sp1 HAwr :=
  lazymatch goal with
  | |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0));
    [reflexivity | evalE AG | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |]
  | |- awr_ok _ (YP09.mkRegion (Some 60%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (sp1 - sp0));
    [reflexivity | evalE AG | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |]
  | |- awr_ok _ (YP09.mkRegion (Some 10%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
    eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat _);
    [reflexivity | evalE AG | cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HAwr; lia |]
  end.
Ltac sbd_wr_tac AG wrt :=
  let a := fresh "a" in let Ha := fresh "Ha" in let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
  intros a Ha (rg & Hin & Hrg);
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
     first [exfalso; clear - Hrg; lia
           | let nb := lazymatch type of Hrg with context [ew _ ?nb] => nb end in
             revert Hrg; evalE AG; intros Hrg; wrt nb a Hrg] |]);
  destruct Hin.
Ltac sbd_wr_std nb a Hrg :=
  lazymatch nb with
  | 2%nat => split; [let Himg := fresh "Himg" in intros Himg; pose proof (pa_segs_low a Himg); unfold kLowMemEnd in *; lia | left; split; lia]
  | 60%nat => split; [let Himg := fresh "Himg" in intros Himg; pose proof (pa_segs_low a Himg); unfold kLowMemEnd in *; lia | left; split; lia]
  | 10%nat => split; [let Himg := fresh "Himg" in intros Himg; pose proof (pa_img_range a Himg); unfold boxed, IMG_LO, IMG_TOP in *; lia
           | right; left; unfold sbd_Er; left; lia]
  end.
Ltac kept_step HKP HFr HG HARc wrt AG :=
  lazymatch type of HKP with sbd_kept ?lyc ?Sc ?W ?memc ?m0 ?slo ?shi ?Er =>
  lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?mm1) (mrestrict _ ?mm2) =>
  let HK2 := fresh "HKP" in
  assert (HK2 : sbd_kept lyc Sc W memc mm2 slo shi Er);
  [ eapply (sbd_kept_run lyc Sc W memc mm1 mm2 _ slo shi Er (in_wrange Ef rs));
    [exact HARc | exact HKP | exact HFr | exact HG | sbd_wr_tac AG wrt]
  | clear HKP HFr HG; rename HK2 into HKP ] end end.
Ltac nat_le_vm := apply (proj1 (Nat.leb_le _ _)); vm_compute; reflexivity.
Ltac reseat' HS HJ2 HP2 keep AG kept_tac :=
  let K := lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => eval vm_compute in (run_K A_LIM (SOff 32 0) [] ss)
           | st_ok _ _ ?ss _ => eval vm_compute in (run_K A_LIM (SOff 32 0) [] ss) end in
  let HS2 := fresh "HS2" in
  lazymatch type of HJ2 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?W2 ?mem2 _ _ =>
  lazymatch type of HP2 with aregs_preserved _ ?regs2 =>
  jafter_call_keep_hi HS K regs2 (mrestrict (w_H W2) mem2) HP2 keep HS2 end end;
  match type of HS2 with ?Q -> _ =>
    let HQ := fresh "HQ" in
    assert (HQ : Q); [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil; kept_tac | specialize (HS2 HQ); clear HQ ] end;
  clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
  let AG2 := fresh "AG" in let Ev := fresh "E" in let HEv := fresh "HE" in
  lazymatch type of AG with forall n, _ -> _ = ew ?E0 n =>
  lazymatch type of HS with st_ok_pi _ _ ?Enew _ _ =>
  remember Enew as Ev eqn:HEv in HS;
  let HEIv := fresh "HEI" in
  lazymatch type of HEv with
  | _ = havoc ?Eo ?kk ?ws => lazymatch goal with Ho : img_env ?val ?lim Eo |- _ =>
      pose proof (img_env_havoc_hi Eo kk ws Ho ltac:(nat_le_vm)) as HEIv; rewrite <- HEv in HEIv end
  | _ = ?En => try (lazymatch goal with Hn : img_env _ _ En |- _ => rewrite <- HEv in Hn end) end;
  repeat match goal with H : img_env _ _ (ewset _ _ _) |- _ => clear H end;
  assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
    by (intros nn Hnn; rewrite HEv; rewrite ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; apply AG; exact Hnn);
  repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
    lazymatch Eo with
    | Ev => fail
    | _ => lazymatch (eval cbv in (Nat.leb 33 n)) with
      | true => let H2 := fresh H in
        assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; exact H);
        clear H; rename H2 into H
      end end end;
  clear HEv AG; rename AG2 into AG end end.
Ltac hei_pose' Eo kk ws :=
  let Ho := rnHEI Eo in let H := fresh "HEIh" in
  first [ pose proof (img_env_havoc Eo kk ws Ho ltac:(nat_le_vm)) as H
        | pose proof (img_env_havoc_hi Eo kk ws Ho ltac:(nat_le_vm)) as H ].
Ltac rebaseE' HS AG HEv :=
  let AG2 := fresh "AG" in let Ev := fresh "E" in
  lazymatch type of AG with forall n, _ -> _ = ew ?E0 n =>
  lazymatch type of HS with st_ok_pi _ _ ?Enew _ _ =>
  remember Enew as Ev eqn:HEv in HS;
  let HEIv := fresh "HEI" in
  lazymatch type of HEv with
  | _ = havoc ?Eo ?kk ?ws => lazymatch goal with Ho : img_env ?val ?lim Eo |- _ =>
    first [ pose proof (img_env_havoc Eo kk ws Ho ltac:(nat_le_vm)) as HEIv
          | pose proof (img_env_havoc_hi Eo kk ws Ho ltac:(nat_le_vm)) as HEIv ];
    rewrite <- HEv in HEIv end
  | _ = ?En => try (lazymatch goal with Hn : img_env _ _ En |- _ => rewrite <- HEv in Hn end) end;
  repeat match goal with H : img_env _ _ (ewset _ _ _) |- _ => clear H end;
  assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
    by (intros nn Hnn; rewrite HEv; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; apply AG; exact Hnn);
  repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
    lazymatch Eo with
    | Ev => fail
    | _ => lazymatch (eval cbv in (Nat.leb 33 n)) with
      | true => let H2 := fresh H in
        assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ?ew_ewset_other, ?ew_havoc_old, ?ew_havoc_above by nat_side;
          rewrite ?ew_ewset_other, ?ew_havoc_old, ?ew_havoc_above by nat_side; exact H);
        clear H; rename H2 into H
      end end end;
  clear AG; rename AG2 into AG end end.

End h.
End f.
End d.
