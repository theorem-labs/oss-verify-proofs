(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2u YC1b YC4u YC4z.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YP14 YI08 YI0c YI0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC6w YC6v YC6t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0n YC6f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition ac_cells (C : acht) : list Z := [ac_f C; ac_h C; ac_u C; ac_p C; ac_x C; ht_cnt (ac_H C); ac_T C].
Definition ac_arrs (C : acht) : list (Z * Z) := cht_blocks (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ac_T C).
Section d.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)).
Variables (s1v tb img fmt N : Z) (imgl : list Z).
Variables (hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 : Z).
Variable PROT : list (Z * Z).
Variables (lyH : alayout) (SH : astate) (WH : world trasegs) (memH : word -> option byte).
Local Notation hk_slots := (hk_slots s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav).
Local Notation hk_kept := (hk_kept s1v PROT lyH SH WH memH).
Local Notation hcore_raw := (hcore_raw B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Definition rblk_in (BL : list (Z * Z)) (a : Z) : Prop := exists b n, In (b, n) ((tb, CHT_SIZE) :: BL) /\ b <= a < b + req_size n.
Definition rperm (BL : list (Z * Z)) : Prop :=
forall b n, In (b, n) ((tb, CHT_SIZE) :: BL) ->
aftok FP (ablocks B ly S) (b, n) /\
(forall blc lyq ownq i, In (b, n) blc -> 0 <= i < req_size n -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (b + i)).
Definition rcore (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(cells : list Z) (BL : list (Z * Z)) : Prop :=
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k /\
(getr regs 2 = Z_to_bv 64 s1v /\ getr regs 9 = Z_to_bv 64 s1v /\ getr regs 8 = Z_to_bv 64 (s1v + 512) /\
getr regs 3 = Z_to_bv 64 (as_gp B) /\ getr regs 4 = Z_to_bv 64 (as_tp B) /\ getr regs 25 = Z_to_bv 64 SB /\
getr regs 18 = Z_to_bv 64 hv18 /\ getr regs 19 = Z_to_bv 64 hv19) /\
hk_slots (mrestrict (w_H W) mem) /\
obj_at trasegs (mrestrict (w_H W) mem) tb LAY_Cht cells /\
arr8 trasegs (mrestrict (w_H W) mem) img imgl /\
Permutation (ablocks B lyc Sc) (PROT ++ (tb, CHT_SIZE) :: BL) /\
rperm BL /\
hk_kept lyc Sc W mem.
Lemma rcore_of_hcore_raw : forall lyc Sc W regs mem md k C, hcore_raw lyc Sc W regs mem md k C ->
rcore lyc Sc W regs mem md k (ac_cells C) (ac_arrs C).
Proof.
intros lyc Sc W regs mem md k C (HJ & HR & Hsl & Hobj & Harr & Himg & Hlens & HTc & HPerm & Hperm & Hkk & Hkept).
split; [exact HJ|]. split; [exact HR|]. split; [exact Hsl|]. split; [exact Hobj|]. split; [exact Himg|]. split; [exact HPerm|]. split; [exact Hperm | exact Hkept].
Qed.
Lemma hcore_raw_of_rcore : forall lyc Sc W regs mem md k C, rcore lyc Sc W regs mem md k (ac_cells C) (ac_arrs C) ->
cht_arrays trasegs (mrestrict (w_H W) mem) (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ac_H C) -> ht_lens (ac_H C) -> In (ac_T C) ts_chain ->
(k <= 8 + 12 * ts_rank (ac_T C) /\ gbud S Sc k) ->
hcore_raw lyc Sc W regs mem md k C.
Proof.
intros lyc Sc W regs mem md k C (HJ & HR & Hsl & Hobj & Himg & HPerm & Hperm & Hkept) Harr Hlens HTc Hkk.
split; [exact HJ|]. split; [exact HR|]. split; [exact Hsl|]. split; [exact Hobj|]. split; [exact Harr|]. split; [exact Himg|]. split; [exact Hlens|].
split; [exact HTc|]. split; [exact HPerm|]. split; [exact Hperm|]. split; [exact Hkk | exact Hkept].
Qed.
Hypothesis Hs1 : s1v = sp0 - 512.
Hypothesis HSTK : 512 + ASTACK <= STK.
Hypothesis Himgl : zlen imgl = fmt * N.
Hypothesis HimgP : In (img, fmt * N) PROT.
Lemma rcore_AR : forall lyc Sc W regs mem md k cells BL, rcore lyc Sc W regs mem md k cells BL -> AR trasegs B lyc Sc W mem md.
Proof. intros lyc Sc W regs mem md k cells BL (HJ & _). exact (proj1 HJ). Qed.
Lemma rcore_ceil : forall lyc Sc W regs mem md k cells BL, rcore lyc Sc W regs mem md k cells BL ->
alloc_ceiling + ASTACK <= s1v /\ s1v + 512 <= 2 ^ 47.
Proof.
intros lyc Sc W regs mem md k cells BL (HJ & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _). lia.
Qed.
Lemma rcore_in_blk : forall lyc Sc W regs mem md k cells BL b n, rcore lyc Sc W regs mem md k cells BL -> In (b, n) ((tb, CHT_SIZE) :: BL) -> In (b, n) (ablocks B lyc Sc).
Proof.
intros lyc Sc W regs mem md k cells BL b n (_ & _ & _ & _ & _ & HPerm & _) Hin.
eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. exact Hin.
Qed.
Lemma rcore_in_prot : forall lyc Sc W regs mem md k cells BL b n, rcore lyc Sc W regs mem md k cells BL -> In (b, n) PROT -> In (b, n) (ablocks B lyc Sc).
Proof.
intros lyc Sc W regs mem md k cells BL b n (_ & _ & _ & _ & _ & HPerm & _) Hin.
eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. left. exact Hin.
Qed.
Lemma journal_frame_addr : forall lyc Sc W mem md k, ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
forall c p, frame_addr lyc c p = frame_addr ly c p.
Proof. intros lyc Sc W mem md k (_ & Hly & _) c p. unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & -> & _). reflexivity. Qed.
Definition rapart (lyc : alayout) (Sc : astate) (a : Z) : Prop :=
0 <= a < alloc_ceiling /\ (a < kLowShadowBeg \/ kHighMemBeg <= a) /\
(forall b n, In (b, n) (PROT ++ [(tb, CHT_SIZE)]) -> ~ (b <= a < b + req_size n)) /\
(forall cid pos, In (cid, pos) (frames Sc) -> ~ (frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid)).
Lemma rblk_apart : forall lyX SX WX memX mdX BLX b n a,
AR trasegs B lyX SX WX memX mdX -> Permutation (ablocks B lyX SX) (PROT ++ (tb, CHT_SIZE) :: BLX) -> In (b, n) BLX -> b <= a < b + req_size n ->
rapart lyX SX a.
Proof.
intros lyX SX WX memX mdX BLX b n a HAR HPerm Hin Ha.
assert (Hin' : In (b, n) (ablocks B lyX SX)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. right. exact Hin. }
destruct (al_blocks _ _ LAWS lyX SX WX memX mdX b n HAR Hin') as (_ & H4096 & Hceil & Happ & _ & _ & Hn0).
split; [lia|]. split; [unfold in_app in Happ; lia|]. split.
- intros b' n' Hp Hx.
assert (HPerm' : Permutation (ablocks B lyX SX) ((PROT ++ [(tb, CHT_SIZE)]) ++ BLX)) by (rewrite <- app_assoc; exact HPerm).
pose proof (rg_sep_app_in B LAWS lyX SX WX memX mdX _ _ (b', n') (b, n) HAR HPerm' Hp Hin) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia.
- intros cid pos Hf Hx. pose proof (sep_block_frame trasegs B LAWS lyX SX WX memX mdX b n cid pos HAR Hin' Hf) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
Lemma rapart_frames : forall lyc Sc ly2 S2 a, rapart ly2 S2 a -> frames S2 = frames Sc -> (forall c p, frame_addr ly2 c p = frame_addr lyc c p) -> rapart lyc Sc a.
Proof.
intros lyc Sc ly2 S2 a (H1 & H2 & H3 & H4) Hf Ha. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
intros cid pos Hin. rewrite <- Ha. apply H4. rewrite Hf. exact Hin.
Qed.
Lemma rcore_run : forall lyc Sc W regs mem md k cells cells' BL regs' mem' md',
rcore lyc Sc W regs mem md k cells BL ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
(forall r, In r HK_CONST -> getr regs' r = getr regs r) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> ~ (alloc_ceiling <= a < s1v) -> ~ rblk_in BL a ->
aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) ->
obj_at trasegs (mrestrict (w_H W) mem') tb LAY_Cht cells' ->
rcore lyc Sc W regs' mem' md' k cells' BL.
Proof.
intros lyc Sc W regs mem md k cells cells' BL regs' mem' md' HC HJ' Hregs Hk Hobj'.
pose proof (rcore_AR _ _ _ _ _ _ _ _ _ HC) as HAR. destruct (rcore_ceil _ _ _ _ _ _ _ _ _ HC) as [Hceil H47].
pose proof HC as (HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Himg & HPerm & Hperm & Hkept).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (Has : ASTACK = 16384) by reflexivity.
assert (Hfacts : forall a, rblk_in BL a -> 0 <= a < alloc_ceiling /\ (a < kLowShadowBeg \/ kHighMemBeg <= a) /\
(forall b n, In (b, n) PROT -> ~ (b <= a < b + req_size n)) /\
(forall cid pos, In (cid, pos) (frames Sc) -> ~ (frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid))).
{ intros a (b & n & Hin & Ha). pose proof (rcore_in_blk _ _ _ _ _ _ _ _ _ b n HC Hin) as Hin'.
destruct (al_blocks _ _ LAWS lyc Sc W mem md b n HAR Hin') as (_ & H4096 & Hbceil & Happ & _ & _ & Hn0).
split; [lia|]. split; [unfold in_app in Happ; lia|]. split.
- intros b' n' Hp Hx. pose proof (rg_sep_app_in B LAWS lyc Sc W mem md PROT ((tb, CHT_SIZE) :: BL) (b', n') (b, n) HAR HPerm Hp Hin) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia.
- intros cid pos Hf Hx. pose proof (sep_block_frame trasegs B LAWS lyc Sc W mem md b n cid pos HAR Hin' Hf) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (Hprot : forall b n, In (b, n) PROT -> rg_blk_kept (w_H W) (w_H W) mem mem' b (req_size n)).
{ intros b n Hin i Hi. pose proof (rcore_in_prot _ _ _ _ _ _ _ _ _ b n HC Hin) as Hin'.
destruct (hk_blk_low B LAWS s1v lyc Sc W mem md b n HAR Hin' ltac:(clear - Hceil Has; lia)) as (Hb0 & Hb1 & Hb2 & Hb3).
apply Hk; [clear - Hi Hb0 Hb1 H47; lia | clear - Hi Hb1; lia | clear - Hi Hb2; lia|].
intros Ht. destruct (Hfacts _ Ht) as (_ & _ & Hp & _). apply (Hp b n Hin). clear - Hi. lia. }
split; [exact HJ'|]. split.
{ repeat split; (rewrite Hregs; [assumption | cbv; tauto]). }
split.
{ apply (hk_slots_kept s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (w_H W) (w_H W) mem mem' Hsl). intros a Ha Hw.
apply Hk; [clear - Ha Hceil H47 C1 Has; lia | clear - Hw; tauto | clear - Ha; lia|].
intros Ht. destruct (Hfacts _ Ht) as (Hlt & _). clear - Hlt Ha Hceil Has. lia. }
split; [exact Hobj'|]. split.
{ apply (arr8_frame trasegs _ _ _ _ Himg). intros a Ha. apply (mbyte_of_aview trasegs).
pose proof (rcore_in_prot _ _ _ _ _ _ _ _ _ img (fmt * N) HC HimgP) as Hin'.
destruct (hk_blk_low B LAWS s1v lyc Sc W mem md img (fmt * N) HAR Hin' ltac:(clear - Hceil Has; lia)) as (_ & _ & _ & Hn).
replace a with (img + (a - img)) by lia. apply (Hprot img (fmt * N) HimgP). rewrite Himgl in Ha. lia. }
split; [exact HPerm|]. split; [exact Hperm|].
destruct Hkept as (KF & KA & K1 & K2 & K3). split; [exact KF|]. split; [exact KA|]. split.
{ intros a Ha Hw. rewrite <- (K1 a Ha Hw). apply Hk; [clear - Ha Hceil H47 C1 Has; lia | clear - Hw; tauto | clear - Ha; lia|].
intros Ht. destruct (Hfacts _ Ht) as (Hlt & _). clear - Hlt Ha Hceil Has. lia. }
split.
{ intros cid pos a Hin Ha. rewrite <- (K2 cid pos a Hin Ha).
assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite KF; exact Hin).
destruct (frames_bounds trasegs B LAWS lyc Sc W mem md cid pos HAR Hin') as (Hf0 & Hfc & _). rewrite KA in Hf0, Hfc.
pose proof (fs_frame_bytes_nonneg cid) as Hnn.
pose proof (shadow_addr_bounds (frame_addr lyH cid pos) ltac:(unfold kHighMemEnd; clear - Hf0 Hfc C1 Hnn; lia)) as Hsb1.
pose proof (shadow_addr_bounds (frame_addr lyH cid pos + fs_frame_bytes cid) ltac:(unfold kHighMemEnd; clear - Hf0 Hfc C1 Hnn; lia)) as Hsb2.
pose proof (shadow_range_end (frame_addr lyH cid pos) (fs_frame_bytes cid) Hnn) as Hse.
assert (Hrng : 0 <= a < alloc_ceiling).
{ destruct Ha as [Ha | Ha]; unfold in_zr, frame_rng in Ha; cbn [fst snd] in Ha;
[clear - Ha Hf0 Hfc; lia | revert Ha Hsb1 Hsb2 Hse C2 C5 C1; unfold kHighShadowEnd, kLowMemEnd; clear; intros; lia]. }
apply Hk; [clear - Hrng C1; lia | clear - Hrng Hceil Has; lia | clear - Hrng; lia|].
intros Ht. destruct (Hfacts _ Ht) as (_ & Hz & _ & Hfr).
destruct Ha as [Ha | Ha]; unfold in_zr, frame_rng in Ha; cbn [fst snd] in Ha.
- apply (Hfr cid pos Hin'). rewrite KA. clear - Ha. lia.
- revert Ha Hsb1 Hsb2 Hse Hz C2 C3 C5. unfold kHighShadowEnd, kLowMemEnd, kLowShadowBeg, kHighMemBeg. clear. intros. lia. }
intros b n i Hin Hi. rewrite <- (K3 b n i Hin Hi). exact (Hprot b n Hin i Hi).
Qed.
Lemma rcore_call : forall lyc Sc W regs mem md k cells BL ly2 S2 W2 regs2 mem2 md2 k2 BL2 (E : Z -> Prop) (slo : Z),
rcore lyc Sc W regs mem md k cells BL ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k2 ->
aregs_preserved regs regs2 -> frames S2 = frames Sc ->
acall_kept trasegs B lyc Sc W mem W2 mem2 slo s1v E ->
(forall a, E a -> rapart lyc Sc a) ->
Permutation (ablocks B ly2 S2) (PROT ++ (tb, CHT_SIZE) :: BL2) -> rperm BL2 ->
rcore ly2 S2 W2 regs2 mem2 md2 k2 cells BL2.
Proof.
intros lyc Sc W regs mem md k cells BL ly2 S2 W2 regs2 mem2 md2 k2 BL2 E slo HC HJ2 HP Hfr (A1 & A2 & A3 & A4 & A5 & A6) HE HPerm2 Hperm2.
pose proof (rcore_AR _ _ _ _ _ _ _ _ _ HC) as HAR. destruct (rcore_ceil _ _ _ _ _ _ _ _ _ HC) as [Hceil H47].
pose proof HC as (HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Himg & HPerm & Hperm & Hkept).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (Has : ASTACK = 16384) by reflexivity.
assert (Hprot : forall b n, In (b, n) (PROT ++ [(tb, CHT_SIZE)]) -> rg_blk_kept (w_H W) (w_H W2) mem mem2 b (req_size n)).
{ intros b n Hin i Hi. apply (A2 b n i); [| exact Hi |].
- eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff in Hin as [Hin | [Hin | []]]; apply in_app_iff; [left; exact Hin | right; left; exact Hin].
- intros He. destruct (HE _ He) as (_ & _ & Hp & _). apply (Hp b n Hin). clear - Hi. lia. }
split; [exact HJ2|]. split.
{ repeat split; (rewrite (aregs_get regs regs2 _ HP); [assumption | apply hk_const_saved; cbv; tauto]). }
split.
{ apply (hk_slots_kept s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (w_H W) (w_H W2) mem mem2 Hsl). intros a Ha Hw.
apply A1; [clear - Ha Hceil H47 C1 Has; lia | clear - Ha; lia]. }
split.
{ apply (rg_obj_at_blk_kept (w_H W) (w_H W2) mem mem2 tb LAY_Cht _ 48 Hobj lay_inside_Cht).
exact (Hprot tb CHT_SIZE ltac:(apply in_app_iff; right; left; reflexivity)). }
split.
{ apply (arr8_frame trasegs _ _ _ _ Himg). intros a Ha. apply (mbyte_of_aview trasegs).
pose proof (rcore_in_prot _ _ _ _ _ _ _ _ _ img (fmt * N) HC HimgP) as Hin'.
destruct (hk_blk_low B LAWS s1v lyc Sc W mem md img (fmt * N) HAR Hin' ltac:(clear - Hceil Has; lia)) as (_ & _ & _ & Hn).
replace a with (img + (a - img)) by lia. apply (Hprot img (fmt * N) ltac:(apply in_app_iff; left; exact HimgP)). rewrite Himgl in Ha. lia. }
split; [exact HPerm2|]. split; [exact Hperm2|].
destruct Hkept as (KF & KA & K1 & K2 & K3).
split; [rewrite Hfr; exact KF|]. split.
{ intros c p. rewrite (journal_frame_addr _ _ _ _ _ _ HJ2 c p), <- (journal_frame_addr _ _ _ _ _ _ HJ c p). apply KA. }
split.
{ intros a Ha Hw. rewrite <- (K1 a Ha Hw). apply A1; [clear - Ha Hceil H47 C1 Has; lia | clear - Ha; lia]. }
split.
{ intros cid pos a Hin Ha. rewrite <- (K2 cid pos a Hin Ha).
assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite KF; exact Hin).
apply (A4 cid pos a Hin'); [unfold frame_rng; cbn [fst snd]; rewrite !KA; exact Ha|].
intros He. destruct (HE _ He) as (Hrng & Hz & _ & Hfrm).
destruct (frames_bounds trasegs B LAWS lyc Sc W mem md cid pos HAR Hin') as (Hf0 & Hfc & _). rewrite KA in Hf0, Hfc.
pose proof (fs_frame_bytes_nonneg cid) as Hnn.
pose proof (shadow_addr_bounds (frame_addr lyH cid pos) ltac:(unfold kHighMemEnd; clear - Hf0 Hfc C1 Hnn; lia)) as Hsb1.
pose proof (shadow_addr_bounds (frame_addr lyH cid pos + fs_frame_bytes cid) ltac:(unfold kHighMemEnd; clear - Hf0 Hfc C1 Hnn; lia)) as Hsb2.
pose proof (shadow_range_end (frame_addr lyH cid pos) (fs_frame_bytes cid) Hnn) as Hse.
destruct Ha as [Ha | Ha]; unfold in_zr, frame_rng in Ha; cbn [fst snd] in Ha.
- apply (Hfrm cid pos Hin'). rewrite KA. clear - Ha. lia.
- revert Ha Hsb1 Hsb2 Hse Hz C2 C3 C5. unfold kHighShadowEnd, kLowMemEnd, kLowShadowBeg, kHighMemBeg. clear. intros. lia. }
intros b n i Hin Hi. rewrite <- (K3 b n i Hin Hi). exact (Hprot b n ltac:(apply in_app_iff; left; exact Hin) i Hi).
Qed.
End d.
