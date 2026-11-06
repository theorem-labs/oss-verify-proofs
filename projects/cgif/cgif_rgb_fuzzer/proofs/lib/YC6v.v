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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC6w.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0n YC6f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Record acht := mkACHT { ac_f : Z; ac_h : Z; ac_u : Z; ac_p : Z; ac_x : Z; ac_H : htab; ac_ent : list (colour * Z) }.
Definition ac_T (C : acht) : Z := ht_T (ac_H C).
Definition ac_blocks (tb : Z) (C : acht) : list (Z * Z) := (tb, CHT_SIZE) :: cht_blocks (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ac_T C).
Definition ts_rank (T : Z) : Z :=
if T =? 524309 then 0 else if T =? 1048583 then 1 else if T =? 2097169 then 2 else if T =? 4194319 then 3 else if T =? 8388617 then 4 else 5.
Lemma ts_rank_range : forall T, 0 <= ts_rank T <= 5.
Proof. intros T. unfold ts_rank. repeat match goal with |- context [?a =? ?b] => destruct (a =? b) end; lia. Qed.
Lemma ts_rank_next : forall T, In T ts_chain -> T < MAX_TABLE_SIZE -> ts_rank (getNextPrimePower2 T) = ts_rank T + 1.
Proof.
intros T HT Hlt. cbv [ts_chain In] in HT. unfold MAX_TABLE_SIZE in Hlt.
destruct HT as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; try lia; vm_compute; reflexivity.
Qed.
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
Definition in_tbl (C : acht) (a : Z) : Prop := exists b n, In (b, n) (ac_blocks tb C) /\ b <= a < b + req_size n.
Definition hk_perm (C : acht) : Prop :=
forall b n, In (b, n) (ac_blocks tb C) ->
aftok FP (ablocks B ly S) (b, n) /\
(forall blc lyq ownq i, In (b, n) blc -> 0 <= i < req_size n -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (b + i)).
Definition hk_kept (lyc : alayout) (Sc : astate) (W : world trasegs) (mem : word -> option byte) : Prop :=
frames Sc = frames SH /\ (forall c p, frame_addr lyc c p = frame_addr lyH c p) /\
(forall a, s1v <= a < s1v + 512 -> ~ wslot (a - s1v) -> aview trasegs (w_H W) mem a = aview trasegs (w_H WH) memH a) /\
(forall cid pos a, In (cid, pos) (frames SH) ->
(in_zr a (frame_rng lyH (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyH cid pos), fs_frame_bytes cid / 8)) ->
aview trasegs (w_H W) mem a = aview trasegs (w_H WH) memH a) /\
(forall b n i, In (b, n) PROT -> 0 <= i < req_size n -> aview trasegs (w_H W) mem (b + i) = aview trasegs (w_H WH) memH (b + i)).
Definition ht_lens (H : htab) : Prop :=
zlen (ht_used H) = ht_T H /\ zlen (ht_keys H) = 3 * ht_T H /\ zlen (ht_frequ H) = ht_T H /\
zlen (ht_colidx H) = ht_T H /\ zlen (ht_pal H) = 3 * ht_T H.

Definition hcore_raw (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) : Prop :=
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k /\
(getr regs 2 = Z_to_bv 64 s1v /\ getr regs 9 = Z_to_bv 64 s1v /\ getr regs 8 = Z_to_bv 64 (s1v + 512) /\
getr regs 3 = Z_to_bv 64 (as_gp B) /\ getr regs 4 = Z_to_bv 64 (as_tp B) /\ getr regs 25 = Z_to_bv 64 SB /\
getr regs 18 = Z_to_bv 64 hv18 /\ getr regs 19 = Z_to_bv 64 hv19) /\
hk_slots (mrestrict (w_H W) mem) /\
obj_at trasegs (mrestrict (w_H W) mem) tb LAY_Cht [ac_f C; ac_h C; ac_u C; ac_p C; ac_x C; ht_cnt (ac_H C); ac_T C] /\
cht_arrays trasegs (mrestrict (w_H W) mem) (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ac_H C) /\
arr8 trasegs (mrestrict (w_H W) mem) img imgl /\
ht_lens (ac_H C) /\ In (ac_T C) ts_chain /\
Permutation (ablocks B lyc Sc) (PROT ++ ac_blocks tb C) /\
hk_perm C /\
(k <= 8 + 12 * ts_rank (ac_T C) /\ gbud S Sc k) /\
hk_kept lyc Sc W mem.
Definition hcore (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) : Prop :=
hcore_raw lyc Sc W regs mem md k C /\ ht_inv (ac_H C) (ac_ent C).
Definition HL_HEAD : Z := 0x826ac.
Definition HL_EXIT : Z := 0x830e0.
Definition hl_home (regs : bvmap 5 word) : Prop :=
getr regs 5 = Z_to_bv 64 (tb + 8) /\ getr regs 6 = Z_to_bv 64 (tb + 16) /\ getr regs 7 = Z_to_bv 64 fmt /\
getr regs 16 = Z_to_bv 64 hv16 /\ getr regs 17 = Z_to_bv 64 hv17 /\
getr regs 22 = Z_to_bv 64 hv22 /\ getr regs 23 = Z_to_bv 64 hv23 /\ getr regs 26 = Z_to_bv 64 hv26 /\ getr regs 27 = Z_to_bv 64 hv27.
Definition at_HL (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha : Z) : Prop :=
hcore lyc Sc W regs mem md k C /\ hl_home regs /\
getr regs 28 = Z_to_bv 64 i /\ getr regs 29 = Z_to_bv 64 ha /\
0 <= i < N /\ (ha = 0 \/ (ha = 1 /\ fmt = 4)) /\ zsum (map snd (ac_ent C)) <= i.
Definition at_HX (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (ha : Z) : Prop :=
hcore lyc Sc W regs mem md k C /\ hl_home regs /\
getr regs 12 = Z_to_bv 64 ha /\ (ha = 0 \/ (ha = 1 /\ fmt = 4)) /\ zsum (map snd (ac_ent C)) <= N.
Hypothesis Hs1 : s1v = sp0 - 512.
Hypothesis HSTK : 512 <= STK.
Hypothesis Hfmt : fmt = 3 \/ fmt = 4.
Hypothesis HN : 1 <= N <= 10000.
Hypothesis Himgl : zlen imgl = fmt * N.
Hypothesis HimgP : In (img, fmt * N) PROT.
Definition HK_CONST : list (bv 5) := [2; 9; 8; 3; 4; 25; 18; 19]%bv.
Lemma hk_const_saved : forall r : bv 5, In r HK_CONST -> acallee_saved (bv_unsigned r).
Proof using.
intros r Hr. unfold HK_CONST in Hr. cbn [In] in Hr.
repeat (destruct Hr as [<- | Hr]; [unfold acallee_saved; vm_compute; repeat first [left; reflexivity | right]; split; discriminate|]). destruct Hr.
Qed.
Lemma hk_tab_off : forall off v, In (off, v) (hk_tab tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav) ->
0 <= off /\ off + 8 <= 512 /\ forall j, 0 <= j < 8 -> ~ wslot (off + j).
Proof.
intros off v Hin. unfold hk_tab in Hin. cbn [In] in Hin. unfold wslot.
repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- _; repeat split; try lia; intros j Hj; lia|]). destruct Hin.
Qed.
Lemma hk_slots_kept : forall H H' (m m' : word -> option byte),
hk_slots (mrestrict H m) ->
(forall a, s1v <= a < s1v + 512 -> ~ wslot (a - s1v) -> aview trasegs H' m' a = aview trasegs H m a) ->
hk_slots (mrestrict H' m').
Proof.
intros H H' m m' Hs Hk off v Hin j Hj. rewrite <- (Hs off v Hin j Hj).
destruct (hk_tab_off off v Hin) as (H0 & H1 & Hw).
apply (mbyte_of_aview trasegs). apply Hk; [lia|].
replace (s1v + off + Z.of_nat j - s1v) with (off + Z.of_nat j) by lia. apply Hw. lia.
Qed.
Lemma hk_blk_low : forall lyc Sc W mem md b n, AR trasegs B lyc Sc W mem md -> In (b, n) (ablocks B lyc Sc) -> alloc_ceiling <= s1v ->
0 <= b /\ b + req_size n <= s1v /\ b + req_size n <= alloc_ceiling /\ 0 <= n <= req_size n.
Proof.
intros lyc Sc W mem md b n HAR Hin Hc.
destruct (al_blocks _ _ LAWS lyc Sc W mem md b n HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hn0).
pose proof (req_size_pos n ltac:(lia)) as [_ Hrq]. repeat split; lia.
Qed.
Lemma hcore_AR : forall lyc Sc W regs mem md k C, hcore_raw lyc Sc W regs mem md k C -> AR trasegs B lyc Sc W mem md.
Proof. intros lyc Sc W regs mem md k C (HJ & _). exact (proj1 HJ). Qed.
Lemma hcore_in_tbl : forall lyc Sc W regs mem md k C b n, hcore_raw lyc Sc W regs mem md k C -> In (b, n) (ac_blocks tb C) -> In (b, n) (ablocks B lyc Sc).
Proof.
intros lyc Sc W regs mem md k C b n (_ & _ & _ & _ & _ & _ & _ & _ & HPerm & _) Hin.
eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. exact Hin.
Qed.
Lemma hcore_in_prot : forall lyc Sc W regs mem md k C b n, hcore_raw lyc Sc W regs mem md k C -> In (b, n) PROT -> In (b, n) (ablocks B lyc Sc).
Proof.
intros lyc Sc W regs mem md k C b n (_ & _ & _ & _ & _ & _ & _ & _ & HPerm & _) Hin.
eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. left. exact Hin.
Qed.
Lemma hcore_ceil : forall lyc Sc W regs mem md k C, hcore_raw lyc Sc W regs mem md k C -> alloc_ceiling <= s1v /\ s1v + 512 <= 2 ^ 47.
Proof.
intros lyc Sc W regs mem md k C (HJ & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _). lia.
Qed.
Lemma in_tbl_facts : forall lyc Sc W regs mem md k C a, hcore_raw lyc Sc W regs mem md k C -> in_tbl C a ->
0 <= a < alloc_ceiling /\ (a < kLowShadowBeg \/ kHighMemBeg <= a) /\
(forall b n, In (b, n) PROT -> ~ (b <= a < b + req_size n)) /\
(forall cid pos, In (cid, pos) (frames Sc) -> ~ (frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid)).
Proof.
intros lyc Sc W regs mem md k C a HC (b & n & Hin & Ha).
pose proof (hcore_AR _ _ _ _ _ _ _ _ HC) as HAR. pose proof (hcore_in_tbl _ _ _ _ _ _ _ _ b n HC Hin) as Hin'.
destruct (al_blocks _ _ LAWS lyc Sc W mem md b n HAR Hin') as (_ & H4096 & Hceil & Happ & _ & _ & Hn0).
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & HPerm & _).
split; [lia|]. split; [unfold in_app in Happ; lia|]. split.
- intros b' n' Hp Hx. pose proof (rg_sep_app_in B LAWS lyc Sc W mem md PROT (ac_blocks tb C) (b', n') (b, n) HAR HPerm Hp Hin) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia.
- intros cid pos Hf Hx. pose proof (sep_block_frame trasegs B LAWS lyc Sc W mem md b n cid pos HAR Hin' Hf) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
Lemma hcore_raw_step : forall lyc Sc W regs mem md k C C' regs' mem' md',
hcore_raw lyc Sc W regs mem md k C ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
(forall r, In r HK_CONST -> getr regs' r = getr regs r) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> ~ (alloc_ceiling <= a < s1v) -> ~ in_tbl C a ->
aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) ->
ac_blocks tb C' = ac_blocks tb C ->
obj_at trasegs (mrestrict (w_H W) mem') tb LAY_Cht [ac_f C'; ac_h C'; ac_u C'; ac_p C'; ac_x C'; ht_cnt (ac_H C'); ac_T C'] ->
cht_arrays trasegs (mrestrict (w_H W) mem') (ac_f C') (ac_h C') (ac_u C') (ac_p C') (ac_x C') (ac_H C') ->
ht_lens (ac_H C') ->
hcore_raw lyc Sc W regs' mem' md' k C'.
Proof.
intros lyc Sc W regs mem md k C C' regs' mem' md' HC HJ' Hregs Hk EB Hobj' Harr' Hlens'.
pose proof (hcore_AR _ _ _ _ _ _ _ _ HC) as HAR. destruct (hcore_ceil _ _ _ _ _ _ _ _ HC) as [Hceil H47].
pose proof HC as (HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Harr & Himg & Hlens & HTc & HPerm & Hperm & Hkk & Hkept).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (ET : ac_T C' = ac_T C).
{ pose proof (f_equal (fun l => snd (nth 3 l (0, 0))) EB) as E1. exact E1. }
assert (Hprot : forall b n, In (b, n) PROT -> rg_blk_kept (w_H W) (w_H W) mem mem' b (req_size n)).
{ intros b n Hin i Hi. pose proof (hcore_in_prot _ _ _ _ _ _ _ _ b n HC Hin) as Hin'.
destruct (hk_blk_low lyc Sc W mem md b n HAR Hin' Hceil) as (Hb0 & Hb1 & Hb2 & Hb3).
apply Hk; [clear - Hi Hb0 Hb1 H47; lia | clear - Hi Hb1; lia | clear - Hi Hb2; lia|].
intros Ht. destruct (in_tbl_facts _ _ _ _ _ _ _ _ _ HC Ht) as (_ & _ & Hp & _). apply (Hp b n Hin). clear - Hi. lia. }
split; [exact HJ'|]. split.
{ repeat split; (rewrite Hregs; [assumption | cbv; tauto]). }
split.
{ apply (hk_slots_kept (w_H W) (w_H W) mem mem' Hsl). intros a Ha Hw. apply Hk; [clear - Ha Hceil H47 C1; lia | clear - Hw; tauto | clear - Ha; lia|].
intros Ht. destruct (in_tbl_facts _ _ _ _ _ _ _ _ _ HC Ht) as (Hlt & _). clear - Hlt Ha Hceil. lia. }
split; [exact Hobj'|]. split; [exact Harr'|]. split.
{ apply (arr8_frame trasegs _ _ _ _ Himg). intros a Ha. apply (mbyte_of_aview trasegs).
pose proof (hcore_in_prot _ _ _ _ _ _ _ _ img (fmt * N) HC HimgP) as Hin'.
destruct (hk_blk_low lyc Sc W mem md img (fmt * N) HAR Hin' Hceil) as (_ & _ & _ & Hn).
replace a with (img + (a - img)) by lia. apply (Hprot img (fmt * N) HimgP). rewrite Himgl in Ha. lia. }
split; [exact Hlens'|]. split; [rewrite ET; exact HTc|]. split; [rewrite EB; exact HPerm|].
split; [unfold hk_perm; rewrite EB; exact Hperm|]. split; [rewrite ET; exact Hkk|].
destruct Hkept as (KF & KA & K1 & K2 & K3). split; [exact KF|]. split; [exact KA|]. split.
{ intros a Ha Hw. rewrite <- (K1 a Ha Hw). apply Hk; [clear - Ha Hceil H47 C1; lia | clear - Hw; tauto | clear - Ha; lia|].
intros Ht. destruct (in_tbl_facts _ _ _ _ _ _ _ _ _ HC Ht) as (Hlt & _). clear - Hlt Ha Hceil. lia. }
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
apply Hk; [clear - Hrng C1; lia | clear - Hrng Hceil; lia | clear - Hrng; lia|].
intros Ht. destruct (in_tbl_facts _ _ _ _ _ _ _ _ _ HC Ht) as (_ & Hz & _ & Hfr).
destruct Ha as [Ha | Ha]; unfold in_zr, frame_rng in Ha; cbn [fst snd] in Ha.
- apply (Hfr cid pos Hin'). rewrite KA. clear - Ha. lia.
- revert Ha Hsb1 Hsb2 Hse Hz C2 C3 C5. unfold kHighShadowEnd, kLowMemEnd, kLowShadowBeg, kHighMemBeg. clear. intros. lia. }
intros b n i Hin Hi. rewrite <- (K3 b n i Hin Hi). exact (Hprot b n Hin i Hi).
Qed.
Lemma hcore_raw_run_same : forall lyc Sc W regs mem md k C regs' mem' md',
hcore_raw lyc Sc W regs mem md k C ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
(forall r, In r HK_CONST -> getr regs' r = getr regs r) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> ~ (alloc_ceiling <= a < s1v) ->
aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) ->
hcore_raw lyc Sc W regs' mem' md' k C.
Proof.
intros lyc Sc W regs mem md k C regs' mem' md' HC HJ' Hregs Hk.
pose proof (hcore_AR _ _ _ _ _ _ _ _ HC) as HAR. destruct (hcore_ceil _ _ _ _ _ _ _ _ HC) as [Hceil H47].
pose proof HC as (HJ & _ & Hsl & Hobj & (Af & Ah & Au & Ap & Ax) & Himg & Hlens & HTc & HPerm & Hperm & Hkk & Hkept).
assert (Hlow : forall b n, In (b, n) (ablocks B lyc Sc) -> rg_blk_kept (w_H W) (w_H W) mem mem' b (req_size n)).
{ intros b n Hin i Hi. destruct (hk_blk_low lyc Sc W mem md b n HAR Hin Hceil) as (Hb0 & Hb1 & Hb2 & Hb3).
apply Hk; [clear - Hi Hb0 Hb1 H47; lia | clear - Hi Hb1; lia | clear - Hi Hb2; lia]. }
pose proof Hlens as (L1 & L2 & L3 & L4 & L5).
apply (hcore_raw_step lyc Sc W regs mem md k C C regs' mem' md' HC HJ' Hregs); [intros a Ha H1 H2 _; exact (Hk a Ha H1 H2) | reflexivity | | | exact Hlens].
- apply (rg_obj_at_blk_kept (w_H W) (w_H W) mem mem' tb LAY_Cht _ 48 Hobj lay_inside_Cht).
exact (Hlow tb CHT_SIZE (hcore_in_tbl _ _ _ _ _ _ _ _ tb CHT_SIZE HC ltac:(left; reflexivity))).
- assert (K : forall b n, In (b, n) (ac_blocks tb C) -> forall a, b <= a < b + n -> mbyte trasegs (mrestrict (w_H W) mem') a = mbyte trasegs (mrestrict (w_H W) mem) a).
{ intros b n Hin a Ha. apply (mbyte_of_aview trasegs). pose proof (hcore_in_tbl _ _ _ _ _ _ _ _ b n HC Hin) as Hin'.
destruct (hk_blk_low lyc Sc W mem md b n HAR Hin' Hceil) as (_ & _ & _ & Hn).
replace a with (b + (a - b)) by lia. apply (Hlow b n Hin'). lia. }
unfold ac_blocks, cht_blocks, ac_T in K.
split; [apply (arr32_frame trasegs _ _ _ _ Af); intros a Ha; apply (K (ac_f C) (4 * ht_T (ac_H C))); [cbn; tauto | rewrite L3 in Ha; exact Ha]|].
split; [apply (arr8_frame trasegs _ _ _ _ Ah); intros a Ha; apply (K (ac_h C) (3 * ht_T (ac_H C))); [cbn; tauto | rewrite L2 in Ha; exact Ha]|].
split; [apply (arr8_frame trasegs _ _ _ _ Au); intros a Ha; apply (K (ac_u C) (ht_T (ac_H C))); [cbn; tauto | rewrite L1 in Ha; exact Ha]|].
split; [apply (arr8_frame trasegs _ _ _ _ Ap); intros a Ha; apply (K (ac_p C) (3 * ht_T (ac_H C))); [cbn; tauto | rewrite L5 in Ha; exact Ha]|].
apply (arr32_frame trasegs _ _ _ _ Ax); intros a Ha; apply (K (ac_x C) (4 * ht_T (ac_H C))); [cbn; tauto | rewrite L4 in Ha; exact Ha].
Qed.
Lemma hcore_run_same : forall lyc Sc W regs mem md k C regs' mem' md',
hcore lyc Sc W regs mem md k C ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
(forall r, In r HK_CONST -> getr regs' r = getr regs r) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> ~ (alloc_ceiling <= a < s1v) ->
aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) ->
hcore lyc Sc W regs' mem' md' k C.
Proof.
intros lyc Sc W regs mem md k C regs' mem' md' [HC Hinv] HJ' Hregs Hk. split; [|exact Hinv].
exact (hcore_raw_run_same lyc Sc W regs mem md k C regs' mem' md' HC HJ' Hregs Hk).
Qed.
End d.
