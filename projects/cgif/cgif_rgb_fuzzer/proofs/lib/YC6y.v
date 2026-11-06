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
YG00 YG0a YG01 YG0h YG0u YG0d YG0f YC04 YC07.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2u YC1b YC4u YC4z
YC53.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YP14 YI08 YI0c YI0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC6w YC6v YC7d YC6k YC6t YC7c YC6l YC6m YC6n YC6o YC6p YC6q YC6r YC6u YC77 YC78 YC79 YC6x.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0n YC6f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma ts_next_facts : forall T, In T ts_chain -> T < MAX_TABLE_SIZE ->
T < getNextPrimePower2 T /\ 1048583 <= getNextPrimePower2 T <= 16777216 /\ In (getNextPrimePower2 T) ts_chain /\
15 * T + 15 * getNextPrimePower2 T + 48 <= 2 ^ 30 /\ 524309 <= T.
Proof.
intros T HT Hlt. unfold MAX_TABLE_SIZE in Hlt. cbv [ts_chain In] in HT.
destruct HT as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; try (exfalso; lia);
repeat match goal with |- context [getNextPrimePower2 ?t] => let v := eval vm_compute in (getNextPrimePower2 t) in change (getNextPrimePower2 t) with v end;
(split; [lia|]; split; [lia|]; split; [cbv [ts_chain In]; tauto|]; split; lia).
Qed.
Lemma bsum_rz_BL : forall C p1 x1, 0 <= ac_T C <= ac_Tn C -> bsum (rz_BL C p1 x1) <= 8 * ac_T C + 7 * ac_Tn C.
Proof. intros C p1 x1 H. unfold rz_BL, rbk, bsum. destruct (p1 =? 0), (x1 =? 0); cbn [fold_right snd]; lia. Qed.
Lemma bsum_optb : forall l r n, 0 <= n -> bsum (l ++ optb r n) <= bsum l + n.
Proof. intros l r n H. rewrite bsum_app. unfold optb. destruct (r =? 0); cbn [bsum fold_right snd]; lia. Qed.
Lemma saved_23_24_27 : acallee_saved 23 /\ acallee_saved 24 /\ acallee_saved 27.
Proof. repeat split; unfold acallee_saved; vm_compute; repeat first [left; reflexivity | right]; split; discriminate. Qed.
Section c.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)).
Variables (s1v tb img fmt N : Z) (imgl : list Z).
Variables (hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 : Z).
Variable PROT : list (Z * Z).
Variables (lyH : alayout) (SH : astate) (WH : world trasegs) (memH : word -> option byte).
Hypothesis Hs1 : s1v = sp0 - 512.
Hypothesis HSTK : 512 <= STK.
Hypothesis Hsp32 : sp0 mod 32 = 0.
Hypothesis HOP : hk_opaque_ok hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav.
Hypothesis Hfmt : fmt = 3 \/ fmt = 4.
Hypothesis HN : 1 <= N <= 10000.
Hypothesis HimgP : In (img, fmt * N) PROT.
Hypothesis Himgl : zlen imgl = fmt * N.
Local Notation hcore_raw := (hcore_raw B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation hcore := (hcore B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_BC := (at_BC B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_BR := (at_BR B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_PA := (at_PA B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation HRS := (hcore_run_same B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19
PROT lyH SH WH memH Hs1 HSTK Hfmt HN Himgl HimgP).
Local Notation FRAMEF := (hk_frame_facts B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH Hs1 HSTK Hsp32).
Local Notation IMGF := (hk_img_facts B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH Hfmt HN HimgP).
Local Notation at_M1C := (at_M1C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_RT := (at_RT B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation HSTEP := (hcore_raw_step B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19
PROT lyH SH WH memH Hs1 HSTK Hfmt HN Himgl HimgP).
Local Notation OTHERK := (hk_tbl_other_kept B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_M1R := (at_M1R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_M2C := (at_M2C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_M2R := (at_M2R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation HRRS := (hcore_raw_run_same B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19
PROT lyH SH WH memH Hs1 HSTK Hfmt HN Himgl HimgP).
Local Notation APARTN := (hk_tbl_apart_nth B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation pxc := (pxc fmt imgl).
Local Notation at_RA1C := (at_RA1C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_RA1R := (at_RA1R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_RA2C := (at_RA2C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_RA2R := (at_RA2R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_MA1C := (at_MA1C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_MA1R := (at_MA1R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_MA2C := (at_MA2C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_MA2R := (at_MA2R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_MA3C := (at_MA3C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_MA3R := (at_MA3R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_FAIL := (at_FAIL B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_MSC := (at_MSC B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation rh_pre := (rh_pre B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation rz_common := (rz_common B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation rcore := (rcore B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation rz_old := (rz_old).
Local Notation hspill := (hspill s1v).
Local Notation slot_is := (slot_is s1v).
Local Notation rh_slots := (rh_slots s1v).
Local Notation cfgat regs pc mem md := (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom trasegs)) md).
Hypothesis TL : TraLib B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes trasegs B.
Hypothesis AFREE : afree_realizes trasegs B.
Hypothesis AREALLOC : arealloc_realizes trasegs B 0x53108 0x53640.
Variable ch0 : list (Z * Z * Z).
Hypothesis HSTKA : 512 + ASTACK <= STK.
Hypothesis Htop32 : sp0 + 32 <= ly_top ly.
Hypothesis HCH0 : achain ly (aview trasegs (w_H W0) mem0) sp0 s0v ch0.
Hypothesis Hrav : rav = 0x81368.
Hypothesis Hspine : spine ch0 = [] \/ spine ch0 = [0x80ea8].
Hypothesis HEV : vev S + 80 <= VEV_MAX.
Hypothesis HLIVE : bsum PROT + 2 ^ 30 <= LIVE_MAX.
Local Notation hk_ch := (hk_ch sp0 rav s0v ch0).
Lemma slot_kept : forall (W W2 : world trasegs) (mem mem2 : word -> option byte) off v, 0 <= off -> off + 8 <= 512 ->
(forall a, s1v <= a < s1v + 512 -> aview trasegs (w_H W2) mem2 a = aview trasegs (w_H W) mem a) ->
slot_is W mem off v -> slot_is W2 mem2 off v.
Proof.
intros W W2 mem mem2 off v H0 H1 Hk Hs j Hj. rewrite <- (Hs j Hj). apply (mbyte_of_aview trasegs). apply Hk. lia.
Qed.
Lemma rz_common_call : forall lyc Sc W regs mem md k C i ha d BL ly2 S2 W2 regs2 mem2 md2 k2 d2 BL2,
rz_common lyc Sc W regs mem md k C i ha d BL ->
rcore ly2 S2 W2 regs2 mem2 md2 k2 (ac_cells C) BL2 -> aregs_preserved regs regs2 ->
(forall a, s1v <= a < s1v + 512 -> aview trasegs (w_H W2) mem2 a = aview trasegs (w_H W) mem a) ->
(forall y, In y [(ac_f C, 4 * ac_T C); (ac_h C, 3 * ac_T C); (ac_u C, ac_T C)] -> rg_blk_kept (w_H W) (w_H W2) mem mem2 (fst y) (req_size (snd y))) ->
k2 - k = d2 - d -> gbud S S2 k2 ->
rz_common ly2 S2 W2 regs2 mem2 md2 k2 C i ha d2 BL2.
Proof.
intros lyc Sc W regs mem md k C i ha d BL ly2 S2 W2 regs2 mem2 md2 k2 d2 BL2 (HC & (Af & Ah & Au) & HF & Hk & [SP72 SP56] & G20 & G21 & G22 & G26) HC2 HP Hfr Hblk Hkk Hg2.
pose proof HF as (Hinv & HTc & _). pose proof Hinv as ((L1 & L2 & L3 & _) & _). unfold ac_T in *.
pose proof (ts_chain_ok _ HTc) as (RT1 & RT2 & RT3).
split; [exact HC2|]. split.
{ split; [|split].
- apply (arr32_frame trasegs _ _ _ _ Af). intros a Ha. apply (mbyte_of_aview trasegs). rewrite L3 in Ha.
pose proof (req_size_pos (4 * ht_T (ac_H C)) ltac:(clear - RT1; lia)) as [_ Hrq].
replace a with (ac_f C + (a - ac_f C)) by lia. apply (Hblk (ac_f C, 4 * ht_T (ac_H C)) ltac:(cbn; tauto)). cbn [fst snd]. clear - Ha Hrq. lia.
- apply (arr8_frame trasegs _ _ _ _ Ah). intros a Ha. apply (mbyte_of_aview trasegs). rewrite L2 in Ha.
pose proof (req_size_pos (3 * ht_T (ac_H C)) ltac:(clear - RT1; lia)) as [_ Hrq].
replace a with (ac_h C + (a - ac_h C)) by lia. apply (Hblk (ac_h C, 3 * ht_T (ac_H C)) ltac:(cbn; tauto)). cbn [fst snd]. clear - Ha Hrq. lia.
- apply (arr8_frame trasegs _ _ _ _ Au). intros a Ha. apply (mbyte_of_aview trasegs). rewrite L1 in Ha.
pose proof (req_size_pos (ht_T (ac_H C)) ltac:(clear - RT1; lia)) as [_ Hrq].
replace a with (ac_u C + (a - ac_u C)) by lia. apply (Hblk (ac_u C, ht_T (ac_H C)) ltac:(cbn; tauto)). cbn [fst snd]. clear - Ha Hrq. lia. }
split; [exact HF|]. split; [split; [unfold ac_T; clear - Hk Hkk; lia | exact Hg2]|].
split; [split; [exact (slot_kept W W2 mem mem2 72 i ltac:(lia) ltac:(lia) Hfr SP72) | exact (slot_kept W W2 mem mem2 56 ha ltac:(lia) ltac:(lia) Hfr SP56)]|].
rewrite (aregs_get regs regs2 20%bv HP) by (unfold acallee_saved; vm_compute; repeat first [left; reflexivity | right]; split; discriminate).
rewrite (aregs_get regs regs2 21%bv HP) by (unfold acallee_saved; vm_compute; repeat first [left; reflexivity | right]; split; discriminate).
rewrite (aregs_get regs regs2 22%bv HP) by (unfold acallee_saved; vm_compute; repeat first [left; reflexivity | right]; split; discriminate).
rewrite (aregs_get regs regs2 26%bv HP) by (unfold acallee_saved; vm_compute; repeat first [left; reflexivity | right]; split; discriminate).
split; [exact G20|]. split; [exact G21|]. split; [exact G22 | exact G26].
Qed.
Lemma rz_old_pos : forall C p1 x1 (rest : list (Z * Z)) y, In y [(ac_f C, 4 * ac_T C); (ac_h C, 3 * ac_T C); (ac_u C, ac_T C)] ->
exists p' : nat, nth_error (rz_BL C p1 x1 ++ rest) p' = Some y /\ (p' < 3)%nat.
Proof.
intros C p1 x1 rest y [<- | [<- | [<- | []]]]; [exists 0%nat | exists 1%nat | exists 2%nat]; split; try reflexivity; lia.
Qed.
Lemma rk_frame_facts : forall lyc Sc W regs mem md k cells BL, rcore lyc Sc W regs mem md k cells BL ->
alloc_ceiling <= s1v /\ s1v + 512 <= 2 ^ 47 /\ s1v mod 32 = 0 /\ (forall a, s1v <= a < s1v + 512 -> apresent (w_H W) mem a).
Proof.
intros lyc Sc W regs mem md k cells BL HC. destruct HC as (HJ & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
split; [clear - Hs1 HSTK Hceil Hslo; lia|]. split; [clear - Hs1 Hshi H47; lia|]. split.
- rewrite Hs1. rewrite Zminus_mod, Hsp32. reflexivity.
- intros a Ha. apply Hpres. clear - Ha Hs1 HSTK. lia.
Qed.
Lemma rk_img_facts : forall lyc Sc W regs mem md k cells BL, rcore lyc Sc W regs mem md k cells BL -> 4096 <= img /\ img + fmt * N <= alloc_ceiling.
Proof.
intros lyc Sc W regs mem md k cells BL HC.
pose proof HC as (HJ & _ & _ & _ & _ & HPerm & _). pose proof (proj1 HJ) as HAR.
assert (Hin : In (img, fmt * N) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. left. exact HimgP. }
destruct (al_blocks _ _ LAWS lyc Sc W mem md img (fmt * N) HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hn0).
pose proof (req_size_pos (fmt * N) ltac:(clear - Hfmt HN; nia)) as [_ Hrq].
split; [exact H4096 | clear - Hceil Hrq; lia].
Qed.
Lemma rk_blk_bound : forall lyc Sc W regs mem md k cells BL b n, rcore lyc Sc W regs mem md k cells BL -> In (b, n) BL -> 4096 <= b < 2 ^ 47.
Proof.
intros lyc Sc W regs mem md k cells BL b n HC Hin.
pose proof HC as (HJ & _ & _ & _ & _ & HPerm & _). pose proof (proj1 HJ) as HAR.
assert (Hin' : In (b, n) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. right. exact Hin. }
destruct (al_blocks _ _ LAWS lyc Sc W mem md b n HAR Hin') as (_ & H4096 & Hceil & _ & _ & _ & Hn0).
pose proof (req_size_pos n (proj1 Hn0)) as [Hrq _]. pose proof (asan_consts) as (C1 & _). clear - H4096 Hceil Hrq C1. lia.
Qed.
Lemma rz_old_in : forall C p1 x1 (rest : list (Z * Z)) y, In y [(ac_f C, 4 * ac_T C); (ac_h C, 3 * ac_T C); (ac_u C, ac_T C)] -> In y (rz_BL C p1 x1 ++ rest).
Proof. intros C p1 x1 rest y [<- | [<- | [<- | []]]]; apply in_app_iff; left; cbn; tauto. Qed.
Lemma rz_common_run : forall lyc Sc W regs mem md k C i ha d BL regs' mem' md',
rz_common lyc Sc W regs mem md k C i ha d BL ->
(forall y, In y [(ac_f C, 4 * ac_T C); (ac_h C, 3 * ac_T C); (ac_u C, ac_T C)] -> In y BL) ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
(forall r, In r (HK_CONST ++ [20; 21; 22; 26]%bv) -> getr regs' r = getr regs r) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) ->
hspill W mem' i ha ->
rz_common lyc Sc W regs' mem' md' k C i ha d BL.
Proof.
intros lyc Sc W regs mem md k C i ha d BL regs' mem' md' (HC & (Af & Ah & Au) & HF & Hk & _ & G20 & G21 & G22 & G26) HBL HJ' Hregs KM Hsp.
pose proof HF as (Hinv & HTc & _). pose proof Hinv as ((L1 & L2 & L3 & _) & _). unfold ac_T in *.
pose proof (ts_chain_ok _ HTc) as (RT1 & RT2 & RT3).
pose proof HC as (HJ & _ & _ & Hobj & _ & HPerm & _). pose proof (proj1 HJ) as HAR.
destruct (rk_frame_facts _ _ _ _ _ _ _ _ _ HC) as (Fceil & F47 & F32 & Fpres).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hlow : forall b n, In (b, n) ((tb, CHT_SIZE) :: BL) -> rg_blk_kept (w_H W) (w_H W) mem mem' b (req_size n)).
{ intros b n Hin j Hj.
assert (Hin' : In (b, n) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; exact Hin).
destruct (hk_blk_low B LAWS s1v lyc Sc W mem md b n HAR Hin' Fceil) as (Hb0 & Hb1 & Hb2 & Hb3).
apply KM; [clear - Hj Hb0 Hb1 F47; lia | clear - Hj Hb1; lia]. }
split.
{ eapply rcore_run with (regs := regs) (mem := mem) (md := md) (cells := ac_cells C); try eassumption.
- intros r Hr. apply Hregs. apply in_or_app. left. exact Hr.
- intros a Ha H1 _ _. exact (KM a Ha H1).
- apply (rg_obj_at_blk_kept (w_H W) (w_H W) mem mem' tb LAY_Cht _ 48 Hobj lay_inside_Cht). exact (Hlow tb CHT_SIZE ltac:(left; reflexivity)). }
split.
{ split; [|split].
- apply (arr32_frame trasegs _ _ _ _ Af). intros a Ha. apply (mbyte_of_aview trasegs). rewrite L3 in Ha.
pose proof (req_size_pos (4 * ht_T (ac_H C)) ltac:(clear - RT1; lia)) as [_ Hrq].
replace a with (ac_f C + (a - ac_f C)) by lia. apply (Hlow (ac_f C) (4 * ht_T (ac_H C)) ltac:(right; apply HBL; cbn; tauto)). clear - Ha Hrq. lia.
- apply (arr8_frame trasegs _ _ _ _ Ah). intros a Ha. apply (mbyte_of_aview trasegs). rewrite L2 in Ha.
pose proof (req_size_pos (3 * ht_T (ac_H C)) ltac:(clear - RT1; lia)) as [_ Hrq].
replace a with (ac_h C + (a - ac_h C)) by lia. apply (Hlow (ac_h C) (3 * ht_T (ac_H C)) ltac:(right; apply HBL; cbn; tauto)). clear - Ha Hrq. lia.
- apply (arr8_frame trasegs _ _ _ _ Au). intros a Ha. apply (mbyte_of_aview trasegs). rewrite L1 in Ha.
pose proof (req_size_pos (ht_T (ac_H C)) ltac:(clear - RT1; lia)) as [_ Hrq].
replace a with (ac_u C + (a - ac_u C)) by lia. apply (Hlow (ac_u C) (ht_T (ac_H C)) ltac:(right; apply HBL; cbn; tauto)). clear - Ha Hrq. lia. }
split; [exact HF|]. split; [exact Hk|]. split; [exact Hsp|].
rewrite (Hregs 20%bv ltac:(cbv; clear; tauto)), (Hregs 21%bv ltac:(cbv; clear; tauto)), (Hregs 22%bv ltac:(cbv; clear; tauto)), (Hregs 26%bv ltac:(cbv; clear; tauto)).
split; [exact G20|]. split; [exact G21|]. split; [exact G22 | exact G26].
Qed.
Lemma rz_old_run : forall lyc Sc W regs mem md k cells BL C (mem' : word -> option byte),
rcore lyc Sc W regs mem md k cells BL -> rz_old W mem C -> ht_inv (ac_H C) (ac_ent C) -> In (ac_T C) ts_chain ->
(forall y, In y [(ac_f C, 4 * ac_T C); (ac_h C, 3 * ac_T C); (ac_u C, ac_T C)] -> In y BL) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> ~ (tb <= a < tb + 48) -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) ->
rz_old W mem' C.
Proof.
intros lyc Sc W regs mem md k cells BL C mem' HC (Af & Ah & Au) Hinv HTc HBL KM.
pose proof Hinv as ((L1 & L2 & L3 & _) & _). unfold ac_T in *.
pose proof (ts_chain_ok _ HTc) as (RT1 & RT2 & RT3).
pose proof HC as (HJ & _ & _ & Hobj & _ & HPerm & _). pose proof (proj1 HJ) as HAR.
destruct (rk_frame_facts _ _ _ _ _ _ _ _ _ HC) as (Fceil & F47 & F32 & Fpres).
assert (Hlow : forall b n, In (b, n) BL -> rg_blk_kept (w_H W) (w_H W) mem mem' b (req_size n)).
{ intros b n Hin j Hj.
assert (Hin' : In (b, n) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; right; exact Hin).
destruct (hk_blk_low B LAWS s1v lyc Sc W mem md b n HAR Hin' Fceil) as (Hb0 & Hb1 & Hb2 & Hb3).
assert (Hap : rapart tb PROT lyc Sc (b + j)) by (eapply rblk_apart with (b := b) (n := n) (BLX := BL); try eassumption; clear - Hj; lia).
destruct Hap as (_ & _ & Hp & _).
apply KM; [clear - Hj Hb0 Hb1 F47; lia | clear - Hj Hb1; lia|].
intros Hx. apply (Hp tb CHT_SIZE ltac:(apply in_app_iff; right; left; reflexivity)). change (req_size CHT_SIZE) with 48. exact Hx. }
split; [|split].
- apply (arr32_frame trasegs _ _ _ _ Af). intros a Ha. apply (mbyte_of_aview trasegs). rewrite L3 in Ha.
pose proof (req_size_pos (4 * ht_T (ac_H C)) ltac:(clear - RT1; lia)) as [_ Hrq].
replace a with (ac_f C + (a - ac_f C)) by lia. apply (Hlow (ac_f C) (4 * ht_T (ac_H C)) ltac:(apply HBL; cbn; tauto)). clear - Ha Hrq. lia.
- apply (arr8_frame trasegs _ _ _ _ Ah). intros a Ha. apply (mbyte_of_aview trasegs). rewrite L2 in Ha.
pose proof (req_size_pos (3 * ht_T (ac_H C)) ltac:(clear - RT1; lia)) as [_ Hrq].
replace a with (ac_h C + (a - ac_h C)) by lia. apply (Hlow (ac_h C) (3 * ht_T (ac_H C)) ltac:(apply HBL; cbn; tauto)). clear - Ha Hrq. lia.
- apply (arr8_frame trasegs _ _ _ _ Au). intros a Ha. apply (mbyte_of_aview trasegs). rewrite L1 in Ha.
pose proof (req_size_pos (ht_T (ac_H C)) ltac:(clear - RT1; lia)) as [_ Hrq].
replace a with (ac_u C + (a - ac_u C)) by lia. apply (Hlow (ac_u C) (ht_T (ac_H C)) ltac:(apply HBL; cbn; tauto)). clear - Ha Hrq. lia.
Qed.
Lemma hl_ra1 : forall lyc Sc W regs mem md k C i ha,
at_RA1C lyc Sc W regs mem md k C i ha ->
SRr trasegs W (cfgat regs A_realloc_tra mem md)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 p1, c2 = cfgat regs2 HL_RA1R mem2 md2 /\ at_RA1R ly2 S2 W2 regs2 mem2 md2 (k + 3) C i ha p1).
Proof.
intros lyc Sc W regs mem md k C i ha (HCm & G10 & G11 & Gra).
pose proof HCm as (HC & _ & (Hinv & HTc & HTlt & _) & Hk & _).
destruct (ts_next_facts _ HTc HTlt) as (Tn1 & Tn2 & Tn3 & Tn4 & Tn5). fold (ac_Tn C) in Tn1, Tn2, Tn3, Tn4.
pose proof (ts_rank_range (ac_T C)) as Hrk.
eapply SRr_mono.
{ eapply (rz_realloc B TL LAWS ML AREALLOC STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH ch0
Hs1 HSTKA Hsp32 Htop32 HCH0 Hrav Hspine ltac:(destruct HOP as (_ & _ & _ & _ & _ & _ & _ & _ & Os0 & _); exact Os0) Himgl HimgP HEV HLIVE
lyc Sc W regs mem md k (ac_cells C) (ac_arrs C) 3%nat (ac_p C) (3 * ac_T C) (3 * ac_Tn C) HL_RA1R HC eq_refl G10 G11).
- unfold MALLOC_MAX. clear - Tn2. lia.
- clear - Tn1. lia.
- unfold ac_arrs, cht_blocks, bsum. cbn [fold_right snd]. clear - Tn4 Tn5 Tn1. lia.
- clear - Hk Hrk. lia.
- exact Gra.
- unfold HL_RA1R. clear. lia.
- reflexivity.
- reflexivity.
- apply (hk_trace_in B TL sp0 rav s0v ch0 Hrav Hspine 0x53640 regs HL_RA1R); [unfold raZ; rewrite Gra; apply unsigned_lit_small; unfold HL_RA1R; clear; lia | vm_compute; reflexivity | vm_compute; reflexivity]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & p1 & -> & HC2 & HP2 & Ha0 & Hok & Hfr & Hoth & _ & _ & Hd2).
exists ly2, S2, regs2, mem2, md2, p1. split; [reflexivity|].
change (lset (ac_arrs C) 3 (rbk (ac_p C, 3 * ac_T C) p1 (3 * ac_Tn C))) with (rz_BL C p1 0) in HC2.
split; [|split; [|exact Ha0]].
- apply (rz_common_call lyc Sc W regs mem md k C i ha 0 (ac_arrs C) ly2 S2 W2 regs2 mem2 md2 (k + 3) 3 (rz_BL C p1 0) HCm HC2 HP2 Hfr); [|lia|exact (gbud_realloc S Sc S2 k _ (proj2 Hk) Hd2 ltac:(clear - Tn2; lia))].
intros y Hy. destruct (rz_old_pos C 0 0 [] y Hy) as (p' & Hp' & Hlt). apply (Hoth p' y); [exact Hp' | lia].
- destruct Hok as [-> | Hok]; [left; reflexivity | right].
apply (rk_blk_bound ly2 S2 W2 regs2 mem2 md2 (k + 3) (ac_cells C) (rz_BL C p1 0) p1 (3 * ac_Tn C) HC2).
unfold rz_BL, rbk. destruct (Z.eqb_spec p1 0) as [X | _]; [exfalso; clear - X Hok; lia | cbn; tauto].
Qed.
Lemma hl_ra1r : forall lyc Sc W regs mem md k C i ha p1,
at_RA1R lyc Sc W regs mem md k C i ha p1 ->
SRr trasegs W (cfgat regs HL_RA1R mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 A_realloc_tra mem2 md2 /\ at_RA2C lyc Sc W regs2 mem2 md2 k C i ha p1).
Proof.
intros lyc Sc W regs mem md k C i ha p1 (HCm & Hok1 & G10).
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HCm as (HC & Hold & HF & Hk & [SP72 SP56] & G20 & G21 & G22 & G26).
pose proof HF as (Hinv & HTc & HTlt & Hi & Hha & Hz).
pose proof HC as (HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Himg & HPerm & Hperm & Hkept).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (rk_frame_facts _ _ _ _ _ _ _ _ _ HC) as (Fceil & F47 & F32 & Fpres).
destruct (rk_img_facts _ _ _ _ _ _ _ _ _ HC) as (Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
destruct (ts_next_facts _ HTc HTlt) as (Tn1 & Tn2 & Tn3 & Tn4 & Tn5). fold (ac_Tn C) in Tn1, Tn2, Tn3, Tn4.
set (Tn := ac_Tn C) in *.
pose proof Hobj as OBJ. cbn [obj_at LAY_Cht ac_cells] in OBJ. unfold field_ok in OBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in OBJ.
destruct OBJ as ([_ Bf] & [_ Bh] & [_ Bu] & [_ Bp] & [_ Bx] & [_ Bc] & [_ BT] & _). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Bf, Bh, Bu, Bp, Bx.
pose proof HOP as (O24 & O27 & O26 & O23 & O18 & O22 & O17 & O16 & Os0 & Ora).
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) (ac_T C)).
set (xv := [i; ha; p1]).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E37 : ew E 37 = Z_to_bv 64 (ac_x C)) by exact (HV 5%nat _ eq_refl).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (E20 : ew E 20 = Z_to_bv 64 (3 * Tn)) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (E22 : ew E 22 = Z_to_bv 64 Tn) by (rewrite (HE 22%nat 22%bv eq_refl); exact G22).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
assert (D4T : sv_denot E (SAlu ALU_SLL (SOff 22 0) (SLit 2)) = Z_to_bv 64 (4 * Tn)).
{ rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 22 Tn E22) by (clear - Tn2; lia). rewrite (U_lit E 2) by lia.
change (Z.land 2 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite zcanon_id by (unfold M64; clear - Tn2; lia). lia. }
assert (Rp1 : 0 <= p1 < 2 ^ 64) by (destruct Hok1 as [-> | X]; [clear; lia | clear - X; lia]).
assert (E54 : ew E 54 = Z_to_bv 64 p1) by exact (HV 22%nat _ eq_refl).
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_RA1R false [(10%bv, SOff 54 0)] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [] [] [] [] [] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) (ac_T C) xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_cons; [|apply Forall_nil]. split; [reflexivity|]. cbn [fst snd]. rewrite G10. symmetry. rewrite (denot_off E 54 p1 0 E54 Rp1), Z.add_0_r. reflexivity. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_nil. }
{ apply Forall_nil. }
{ apply Forall_nil. }
{ intros e []. }
{ exact I. }
{ exact I. }
{ exact I. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 55 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan A_realloc_tra.
{ apply (hk_awr_ok s1v tb fmt E false _ _ _ _ [] STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 55 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false _ _ _ _ [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 55 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [20; 21; 22; 26]%bv ++ []) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 55 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 55 E Ex e HAE1 Hat); exact Dv);
assert (SLOT : forall idx lo hi cs off e v, nth_error (ss_mem ssx) idx = Some (YQ0b.mkRegion (Some 9%nat) lo hi lo hi cs) -> In (ck off e) cs ->
sv_denot E e = Z_to_bv 64 v -> sv_atoms_lt 55 e = true -> 0 <= v < 2 ^ 64 -> val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + off) 8 v)
by (intros idx lo hi cs off e v Hnth Hin Dv Hat Hv;
apply (hk_slot_of_state s1v Ex ssx ms (w_H W) idx lo hi lo hi cs off e v HS Hnth Hin);
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (sv_denot_agree 55 E Ex e HAE1 Hat); exact Dv | exact Hv]) end.
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (SLOT 2%nat 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | reflexivity | clear - Hi HN; lia]).
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (SLOT 1%nat 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | reflexivity | clear - Hha; lia]).
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
assert (HCm' : rz_common lyc Sc W (ms_regs ms) (ms_mem ms) mdx k C i ha 3 (rz_BL C p1 0)) end.
{ apply (rz_common_run lyc Sc W regs mem md k C i ha 3 (rz_BL C p1 0) _ _ _ HCm); [intros y Hy; rewrite <- (app_nil_r (rz_BL C p1 0)); exact (rz_old_in C p1 0 [] y Hy) | exact HJ | | exact KM1 | split; [exact SP72' | exact SP56']].
intros r Hr. apply HKR. rewrite app_assoc. apply in_or_app. left. exact Hr. }
split; [exact HCm'|]. split; [exact Hok1|].
split; [apply (RD 23%bv (SOff 54 0) p1 eq_refl); [rewrite (denot_off E 54 p1 0 E54 Rp1), Z.add_0_r; reflexivity | reflexivity]|].
split; [exact (RD 24%bv _ (4 * Tn) eq_refl D4T eq_refl)|].
split; [apply (RD 10%bv (SOff 37 0) (ac_x C) eq_refl); [rewrite (denot_off E 37 (ac_x C) 0 E37 Bx), Z.add_0_r; reflexivity | reflexivity]|].
split; [exact (RD 11%bv _ (4 * Tn) eq_refl D4T eq_refl)|].
exact (RD 1%bv (SLit HL_RA2R) HL_RA2R eq_refl eq_refl eq_refl).
Qed.
Lemma hl_ra2 : forall lyc Sc W regs mem md k C i ha p1,
at_RA2C lyc Sc W regs mem md k C i ha p1 ->
SRr trasegs W (cfgat regs A_realloc_tra mem md)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 x1, c2 = cfgat regs2 HL_RA2R mem2 md2 /\ at_RA2R ly2 S2 W2 regs2 mem2 md2 (k + 3) C i ha p1 x1).
Proof.
intros lyc Sc W regs mem md k C i ha p1 (HCm & Hok1 & G23 & G24 & G10 & G11 & Gra).
pose proof HCm as (HC & _ & (Hinv & HTc & HTlt & _) & Hk & _).
destruct (ts_next_facts _ HTc HTlt) as (Tn1 & Tn2 & Tn3 & Tn4 & Tn5). fold (ac_Tn C) in Tn1, Tn2, Tn3, Tn4.
pose proof (ts_rank_range (ac_T C)) as Hrk.
pose proof (bsum_rz_BL C p1 0 ltac:(clear - Tn1 Tn5; lia)) as Hbs.
destruct saved_23_24_27 as (Sv23 & Sv24 & Sv27).
eapply SRr_mono.
{ eapply (rz_realloc B TL LAWS ML AREALLOC STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH ch0
Hs1 HSTKA Hsp32 Htop32 HCH0 Hrav Hspine ltac:(destruct HOP as (_ & _ & _ & _ & _ & _ & _ & _ & Os0 & _); exact Os0) Himgl HimgP HEV HLIVE
lyc Sc W regs mem md k (ac_cells C) (rz_BL C p1 0) 4%nat (ac_x C) (4 * ac_T C) (4 * ac_Tn C) HL_RA2R HC eq_refl G10 G11).
- unfold MALLOC_MAX. clear - Tn2. lia.
- clear - Tn1. lia.
- clear - Hbs Tn4 Tn5 Tn1. lia.
- clear - Hk Hrk. lia.
- exact Gra.
- unfold HL_RA2R. clear. lia.
- reflexivity.
- reflexivity.
- apply (hk_trace_in B TL sp0 rav s0v ch0 Hrav Hspine 0x53640 regs HL_RA2R); [unfold raZ; rewrite Gra; apply unsigned_lit_small; unfold HL_RA2R; clear; lia | vm_compute; reflexivity | vm_compute; reflexivity]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & x1 & -> & HC2 & HP2 & Ha0 & Hok & Hfr & Hoth & _ & _ & Hd2).
exists ly2, S2, regs2, mem2, md2, x1. split; [reflexivity|].
change (lset (rz_BL C p1 0) 4 (rbk (ac_x C, 4 * ac_T C) x1 (4 * ac_Tn C))) with (rz_BL C p1 x1) in HC2.
split; [|split; [exact Hok1|]; split; [|split; [rewrite (aregs_get regs regs2 23%bv HP2 Sv23); exact G23|]; split; [rewrite (aregs_get regs regs2 24%bv HP2 Sv24); exact G24 | exact Ha0]]].
- apply (rz_common_call lyc Sc W regs mem md k C i ha 3 (rz_BL C p1 0) ly2 S2 W2 regs2 mem2 md2 (k + 3) 6 (rz_BL C p1 x1) HCm HC2 HP2 Hfr); [|lia|exact (gbud_realloc S Sc S2 k _ (proj2 Hk) Hd2 ltac:(clear - Tn2; lia))].
intros y Hy. destruct (rz_old_pos C p1 0 [] y Hy) as (p' & Hp' & Hlt). rewrite app_nil_r in Hp'. apply (Hoth p' y); [exact Hp' | lia].
- destruct Hok as [-> | Hok]; [left; reflexivity | right].
apply (rk_blk_bound ly2 S2 W2 regs2 mem2 md2 (k + 3) (ac_cells C) (rz_BL C p1 x1) x1 (4 * ac_Tn C) HC2).
unfold rz_BL. unfold rbk at 2. destruct (Z.eqb_spec x1 0) as [X | _]; [exfalso; clear - X Hok; lia | cbn; tauto].
Qed.
Lemma hl_ra2r : forall lyc Sc W regs mem md k C i ha p1 x1,
at_RA2R lyc Sc W regs mem md k C i ha p1 x1 ->
SRr trasegs W (cfgat regs HL_RA2R mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 A_malloc_tra mem2 md2 /\ at_MA1C lyc Sc W regs2 mem2 md2 k C i ha p1 x1).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 (HCm & Hok1 & Hok2 & G23 & G24 & G10).
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HCm as (HC & Hold & HF & Hk & [SP72 SP56] & G20 & G21 & G22 & G26).
pose proof HF as (Hinv & HTc & HTlt & Hi & Hha & Hz).
pose proof HC as (HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Himg & HPerm & Hperm & Hkept).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (rk_frame_facts _ _ _ _ _ _ _ _ _ HC) as (Fceil & F47 & F32 & Fpres).
destruct (rk_img_facts _ _ _ _ _ _ _ _ _ HC) as (Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
destruct (ts_next_facts _ HTc HTlt) as (Tn1 & Tn2 & Tn3 & Tn4 & Tn5). fold (ac_Tn C) in Tn1, Tn2, Tn3, Tn4.
set (Tn := ac_Tn C) in *.
pose proof Hobj as OBJ. cbn [obj_at LAY_Cht ac_cells] in OBJ. unfold field_ok in OBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in OBJ.
destruct OBJ as ([_ Bf] & [_ Bh] & [_ Bu] & [_ Bp] & [_ Bx] & [_ Bc] & [_ BT] & _). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Bf, Bh, Bu, Bp, Bx.
pose proof HOP as (O24 & O27 & O26 & O23 & O18 & O22 & O17 & O16 & Os0 & Ora).
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) (ac_T C)).
set (xv := [i; ha; x1]).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E37 : ew E 37 = Z_to_bv 64 (ac_x C)) by exact (HV 5%nat _ eq_refl).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (E20 : ew E 20 = Z_to_bv 64 (3 * Tn)) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (E22 : ew E 22 = Z_to_bv 64 Tn) by (rewrite (HE 22%nat 22%bv eq_refl); exact G22).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
assert (D4T : sv_denot E (SAlu ALU_SLL (SOff 22 0) (SLit 2)) = Z_to_bv 64 (4 * Tn)).
{ rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 22 Tn E22) by (clear - Tn2; lia). rewrite (U_lit E 2) by lia.
change (Z.land 2 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite zcanon_id by (unfold M64; clear - Tn2; lia). lia. }
assert (Rx1 : 0 <= x1 < 2 ^ 64) by (destruct Hok2 as [-> | X]; [clear; lia | clear - X; lia]).
assert (E54 : ew E 54 = Z_to_bv 64 x1) by exact (HV 22%nat _ eq_refl).
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_RA2R false [(10%bv, SOff 54 0)] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [] [] [] [] [] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) (ac_T C) xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_cons; [|apply Forall_nil]. split; [reflexivity|]. cbn [fst snd]. rewrite G10. symmetry. rewrite (denot_off E 54 x1 0 E54 Rx1), Z.add_0_r. reflexivity. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_nil. }
{ apply Forall_nil. }
{ apply Forall_nil. }
{ intros e []. }
{ exact I. }
{ exact I. }
{ exact I. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 55 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan A_malloc_tra.
{ apply (hk_awr_ok s1v tb fmt E false _ _ _ _ [] STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 55 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false _ _ _ _ [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 55 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [20; 21; 22; 26]%bv ++ [23; 24]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 55 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 55 E Ex e HAE1 Hat); exact Dv);
assert (SLOT : forall idx lo hi cs off e v, nth_error (ss_mem ssx) idx = Some (YQ0b.mkRegion (Some 9%nat) lo hi lo hi cs) -> In (ck off e) cs ->
sv_denot E e = Z_to_bv 64 v -> sv_atoms_lt 55 e = true -> 0 <= v < 2 ^ 64 -> val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + off) 8 v)
by (intros idx lo hi cs off e v Hnth Hin Dv Hat Hv;
apply (hk_slot_of_state s1v Ex ssx ms (w_H W) idx lo hi lo hi cs off e v HS Hnth Hin);
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (sv_denot_agree 55 E Ex e HAE1 Hat); exact Dv | exact Hv]) end.
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (SLOT 2%nat 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | reflexivity | clear - Hi HN; lia]).
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (SLOT 1%nat 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | reflexivity | clear - Hha; lia]).
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
assert (HCm' : rz_common lyc Sc W (ms_regs ms) (ms_mem ms) mdx k C i ha 6 (rz_BL C p1 x1)) end.
{ apply (rz_common_run lyc Sc W regs mem md k C i ha 6 (rz_BL C p1 x1) _ _ _ HCm); [intros y Hy; rewrite <- (app_nil_r (rz_BL C p1 x1)); exact (rz_old_in C p1 x1 [] y Hy) | exact HJ | | exact KM1 | split; [exact SP72' | exact SP56']].
intros r Hr. apply HKR. rewrite app_assoc. apply in_or_app. left. exact Hr. }
split; [exact HCm'|].
split; [split; [exact Hok1|]; split; [exact Hok2|]; rewrite (HKR 23%bv ltac:(cbv; clear; tauto)), (HKR 24%bv ltac:(cbv; clear; tauto));
split; [exact G23|]; split; [exact G24|]; apply (RD 27%bv (SOff 54 0) x1 eq_refl); [rewrite (denot_off E 54 x1 0 E54 Rx1), Z.add_0_r; reflexivity | reflexivity]|].
split; [apply (RD 10%bv (SOff 20 0) (3 * Tn) eq_refl); [rewrite (denot_off E 20 (3 * Tn) 0 E20 ltac:(clear - Tn2; lia)), Z.add_0_r; reflexivity | reflexivity]|].
exact (RD 1%bv (SLit HL_MA1R) HL_MA1R eq_refl eq_refl eq_refl).
Qed.
Lemma hl_ma1 : forall lyc Sc W regs mem md k C i ha p1 x1,
at_MA1C lyc Sc W regs mem md k C i ha p1 x1 ->
SRr trasegs W (cfgat regs A_malloc_tra mem md)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 h1, c2 = cfgat regs2 HL_MA1R mem2 md2 /\ at_MA1R ly2 S2 W2 regs2 mem2 md2 (k + 1) C i ha p1 x1 h1).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 (HCm & Hres & G10 & Gra).
pose proof HCm as (HC & _ & (Hinv & HTc & HTlt & _) & Hk & _).
destruct (ts_next_facts _ HTc HTlt) as (Tn1 & Tn2 & Tn3 & Tn4 & Tn5). fold (ac_Tn C) in Tn1, Tn2, Tn3, Tn4.
pose proof (ts_rank_range (ac_T C)) as Hrk.
pose proof (bsum_rz_BL C p1 x1 ltac:(clear - Tn1 Tn5; lia)) as Hbs.
destruct saved_23_24_27 as (Sv23 & Sv24 & Sv27). destruct Hres as (Hok1 & Hok2 & G23 & G24 & G27).
eapply SRr_mono.
{ eapply (rz_malloc B TL LAWS ML AMALLOC STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH ch0
Hs1 HSTKA Hsp32 Htop32 HCH0 Hrav Hspine ltac:(destruct HOP as (_ & _ & _ & _ & _ & _ & _ & _ & Os0 & _); exact Os0) Himgl HimgP HEV HLIVE
lyc Sc W regs mem md k (ac_cells C) (rz_BL C p1 x1) (3 * ac_Tn C) HL_MA1R HC G10).
- unfold MALLOC_MAX. clear - Tn2. lia.
- clear - Hbs Tn4 Tn5 Tn1. lia.
- clear - Hk Hrk. lia.
- exact Gra.
- unfold HL_MA1R. clear. lia.
- reflexivity.
- rewrite (tl_code B TL). apply (hk_trace_in B TL sp0 rav s0v ch0 Hrav Hspine _ regs HL_MA1R); [unfold raZ; rewrite Gra; apply unsigned_lit_small; unfold HL_MA1R; clear; lia | vm_compute; reflexivity | vm_compute; reflexivity]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & h1 & -> & HC2 & HP2 & Ha0 & Hok & Hfr & Hoth & Hd2).
exists ly2, S2, regs2, mem2, md2, h1. split; [reflexivity|].
assert (Hres' : rz_res regs2 C p1 x1).
{ split; [exact Hok1|]. split; [exact Hok2|]. rewrite (aregs_get regs regs2 23%bv HP2 Sv23), (aregs_get regs regs2 24%bv HP2 Sv24), (aregs_get regs regs2 27%bv HP2 Sv27).
split; [exact G23|]. split; [exact G24 | exact G27]. }
assert (Hok' : rz_ok1 h1).
{ destruct Hok as [-> | Hok]; [left; reflexivity | right].
apply (rk_blk_bound ly2 S2 W2 regs2 mem2 md2 (k + 1) (ac_cells C) ((rz_BL C p1 x1) ++ optb h1 (3 * ac_Tn C)) h1 (3 * ac_Tn C) HC2).
apply in_app_iff. right. unfold optb. destruct (Z.eqb_spec h1 0) as [X | _]; [exfalso; clear - X Hok; lia | left; reflexivity]. }
assert (HCm' : rz_common ly2 S2 W2 regs2 mem2 md2 (k + 1) C i ha 7 ((rz_BL C p1 x1) ++ optb h1 (3 * ac_Tn C))).
{ apply (rz_common_call lyc Sc W regs mem md k C i ha 6 (rz_BL C p1 x1) ly2 S2 W2 regs2 mem2 md2 (k + 1) 7 _ HCm HC2 HP2 Hfr); [|lia|exact (gbud_malloc S Sc S2 k _ (proj2 Hk) Hd2 ltac:(clear - Tn2; lia))].
intros y Hy. apply Hoth. rewrite <- (app_nil_r (rz_BL C p1 x1)). exact (rz_old_in C p1 x1 [] y Hy). }
split; [exact HCm'|]. split; [exact Hres'|]. split; [exact Hok' | exact Ha0].
Qed.
Lemma hl_ma1r : forall lyc Sc W regs mem md k C i ha p1 x1 h1,
at_MA1R lyc Sc W regs mem md k C i ha p1 x1 h1 ->
SRr trasegs W (cfgat regs HL_MA1R mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 A_malloc_tra mem2 md2 /\ at_MA2C lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 (HCm & Hres & Hok3 & G10).
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HCm as (HC & Hold & HF & Hk & [SP72 SP56] & G20 & G21 & G22 & G26).
pose proof HF as (Hinv & HTc & HTlt & Hi & Hha & Hz).
pose proof HC as (HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Himg & HPerm & Hperm & Hkept).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (rk_frame_facts _ _ _ _ _ _ _ _ _ HC) as (Fceil & F47 & F32 & Fpres).
destruct (rk_img_facts _ _ _ _ _ _ _ _ _ HC) as (Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
destruct (ts_next_facts _ HTc HTlt) as (Tn1 & Tn2 & Tn3 & Tn4 & Tn5). fold (ac_Tn C) in Tn1, Tn2, Tn3, Tn4.
set (Tn := ac_Tn C) in *.
pose proof Hobj as OBJ. cbn [obj_at LAY_Cht ac_cells] in OBJ. unfold field_ok in OBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in OBJ.
destruct OBJ as ([_ Bf] & [_ Bh] & [_ Bu] & [_ Bp] & [_ Bx] & [_ Bc] & [_ BT] & _). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Bf, Bh, Bu, Bp, Bx.
pose proof HOP as (O24 & O27 & O26 & O23 & O18 & O22 & O17 & O16 & Os0 & Ora).
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) (ac_T C)).
set (xv := [i; ha; h1]).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E37 : ew E 37 = Z_to_bv 64 (ac_x C)) by exact (HV 5%nat _ eq_refl).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (E20 : ew E 20 = Z_to_bv 64 (3 * Tn)) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (E22 : ew E 22 = Z_to_bv 64 Tn) by (rewrite (HE 22%nat 22%bv eq_refl); exact G22).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
assert (D4T : sv_denot E (SAlu ALU_SLL (SOff 22 0) (SLit 2)) = Z_to_bv 64 (4 * Tn)).
{ rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 22 Tn E22) by (clear - Tn2; lia). rewrite (U_lit E 2) by lia.
change (Z.land 2 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite zcanon_id by (unfold M64; clear - Tn2; lia). lia. }
assert (Rh1 : 0 <= h1 < 2 ^ 64) by (destruct Hok3 as [-> | X]; [clear; lia | clear - X; lia]).
assert (E54 : ew E 54 = Z_to_bv 64 h1) by exact (HV 22%nat _ eq_refl).
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_MA1R false [(10%bv, SOff 54 0)] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [] [] [] [] [] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) (ac_T C) xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_cons; [|apply Forall_nil]. split; [reflexivity|]. cbn [fst snd]. rewrite G10. symmetry. rewrite (denot_off E 54 h1 0 E54 Rh1), Z.add_0_r. reflexivity. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_nil. }
{ apply Forall_nil. }
{ apply Forall_nil. }
{ intros e []. }
{ exact I. }
{ exact I. }
{ exact I. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 55 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan A_malloc_tra.
{ apply (hk_awr_ok s1v tb fmt E false _ _ _ _ [] STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 55 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false _ _ _ _ [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 55 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [20; 21; 22; 26]%bv ++ [23; 24; 27]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 55 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 55 E Ex e HAE1 Hat); exact Dv);
assert (SLOT : forall idx lo hi cs off e v, nth_error (ss_mem ssx) idx = Some (YQ0b.mkRegion (Some 9%nat) lo hi lo hi cs) -> In (ck off e) cs ->
sv_denot E e = Z_to_bv 64 v -> sv_atoms_lt 55 e = true -> 0 <= v < 2 ^ 64 -> val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + off) 8 v)
by (intros idx lo hi cs off e v Hnth Hin Dv Hat Hv;
apply (hk_slot_of_state s1v Ex ssx ms (w_H W) idx lo hi lo hi cs off e v HS Hnth Hin);
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (sv_denot_agree 55 E Ex e HAE1 Hat); exact Dv | exact Hv]) end.
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (SLOT 2%nat 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | reflexivity | clear - Hi HN; lia]).
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (SLOT 1%nat 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | reflexivity | clear - Hha; lia]).
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
assert (HCm' : rz_common lyc Sc W (ms_regs ms) (ms_mem ms) mdx k C i ha 7 (rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C))) end.
{ apply (rz_common_run lyc Sc W regs mem md k C i ha 7 (rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) _ _ _ HCm); [intros y Hy; exact (rz_old_in C p1 x1 _ y Hy) | exact HJ | | exact KM1 | split; [exact SP72' | exact SP56']].
intros r Hr. apply HKR. rewrite app_assoc. apply in_or_app. left. exact Hr. }
split; [exact HCm'|]. split; [unfold rz_res in *; rewrite (HKR 23%bv ltac:(cbv; clear; tauto)), (HKR 24%bv ltac:(cbv; clear; tauto)), (HKR 27%bv ltac:(cbv; clear; tauto)); exact Hres|]. split; [exact Hok3|].
split; [apply (SLOT 4%nat 160 184 [ck 160 (SOff 22 0); ck 176 (SOff 54 0)] 176 (SOff 54 0) h1 eq_refl ltac:(right; left; reflexivity)); [rewrite (denot_off E 54 h1 0 E54 Rh1), Z.add_0_r; reflexivity | reflexivity | exact Rh1]|].
split; [apply (SLOT 4%nat 160 184 [ck 160 (SOff 22 0); ck 176 (SOff 54 0)] 160 (SOff 22 0) Tn eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 22 Tn 0 E22 ltac:(clear - Tn2; lia)), Z.add_0_r; reflexivity | reflexivity | clear - Tn2; lia]|].
split; [apply (RD 10%bv (SOff 22 0) Tn eq_refl); [rewrite (denot_off E 22 Tn 0 E22 ltac:(clear - Tn2; lia)), Z.add_0_r; reflexivity | reflexivity]|].
exact (RD 1%bv (SLit HL_MA2R) HL_MA2R eq_refl eq_refl eq_refl).
Qed.
Lemma hl_ma2 : forall lyc Sc W regs mem md k C i ha p1 x1 h1,
at_MA2C lyc Sc W regs mem md k C i ha p1 x1 h1 ->
SRr trasegs W (cfgat regs A_malloc_tra mem md)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 u1, c2 = cfgat regs2 HL_MA2R mem2 md2 /\ at_MA2R ly2 S2 W2 regs2 mem2 md2 (k + 1) C i ha p1 x1 h1 u1).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 (HCm & Hres & Hok3 & S176 & S160 & G10 & Gra).
pose proof HCm as (HC & _ & (Hinv & HTc & HTlt & _) & Hk & _).
destruct (ts_next_facts _ HTc HTlt) as (Tn1 & Tn2 & Tn3 & Tn4 & Tn5). fold (ac_Tn C) in Tn1, Tn2, Tn3, Tn4.
pose proof (ts_rank_range (ac_T C)) as Hrk.
pose proof (bsum_rz_BL C p1 x1 ltac:(clear - Tn1 Tn5; lia)) as Hbs.
destruct saved_23_24_27 as (Sv23 & Sv24 & Sv27). destruct Hres as (Hok1 & Hok2 & G23 & G24 & G27).
eapply SRr_mono.
{ eapply (rz_malloc B TL LAWS ML AMALLOC STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH ch0
Hs1 HSTKA Hsp32 Htop32 HCH0 Hrav Hspine ltac:(destruct HOP as (_ & _ & _ & _ & _ & _ & _ & _ & Os0 & _); exact Os0) Himgl HimgP HEV HLIVE
lyc Sc W regs mem md k (ac_cells C) (rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) (ac_Tn C) HL_MA2R HC G10).
- unfold MALLOC_MAX. clear - Tn2. lia.
- pose proof (bsum_optb (rz_BL C p1 x1) h1 (3 * ac_Tn C) ltac:(clear - Tn2; lia)) as Hb1. clear - Hbs Hb1 Tn4 Tn5 Tn1. lia.
- clear - Hk Hrk. lia.
- exact Gra.
- unfold HL_MA2R. clear. lia.
- reflexivity.
- rewrite (tl_code B TL). apply (hk_trace_in B TL sp0 rav s0v ch0 Hrav Hspine _ regs HL_MA2R); [unfold raZ; rewrite Gra; apply unsigned_lit_small; unfold HL_MA2R; clear; lia | vm_compute; reflexivity | vm_compute; reflexivity]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & u1 & -> & HC2 & HP2 & Ha0 & Hok & Hfr & Hoth & Hd2).
exists ly2, S2, regs2, mem2, md2, u1. split; [reflexivity|].
assert (Hres' : rz_res regs2 C p1 x1).
{ split; [exact Hok1|]. split; [exact Hok2|]. rewrite (aregs_get regs regs2 23%bv HP2 Sv23), (aregs_get regs regs2 24%bv HP2 Sv24), (aregs_get regs regs2 27%bv HP2 Sv27).
split; [exact G23|]. split; [exact G24 | exact G27]. }
assert (Hok' : rz_ok1 u1).
{ destruct Hok as [-> | Hok]; [left; reflexivity | right].
apply (rk_blk_bound ly2 S2 W2 regs2 mem2 md2 (k + 1) (ac_cells C) ((rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) ++ optb u1 (ac_Tn C)) u1 (ac_Tn C) HC2).
apply in_app_iff. right. unfold optb. destruct (Z.eqb_spec u1 0) as [X | _]; [exfalso; clear - X Hok; lia | left; reflexivity]. }
assert (HCm' : rz_common ly2 S2 W2 regs2 mem2 md2 (k + 1) C i ha 8 ((rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) ++ optb u1 (ac_Tn C))).
{ apply (rz_common_call lyc Sc W regs mem md k C i ha 7 (rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) ly2 S2 W2 regs2 mem2 md2 (k + 1) 8 _ HCm HC2 HP2 Hfr); [|lia|exact (gbud_malloc S Sc S2 k _ (proj2 Hk) Hd2 ltac:(clear - Tn2; lia))].
intros y Hy. apply Hoth. exact (rz_old_in C p1 x1 _ y Hy). }
split; [exact HCm'|]. split; [exact Hres'|]. split; [exact Hok3|]. split; [exact Hok'|].
split; [exact (slot_kept W W2 mem mem2 176 h1 ltac:(lia) ltac:(lia) Hfr S176)|]. split; [exact (slot_kept W W2 mem mem2 160 _ ltac:(lia) ltac:(lia) Hfr S160) | exact Ha0].
Qed.
Lemma hl_ma2r : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1,
at_MA2R lyc Sc W regs mem md k C i ha p1 x1 h1 u1 ->
SRr trasegs W (cfgat regs HL_MA2R mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 A_malloc_tra mem2 md2 /\ at_MA3C lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 (HCm & Hres & Hok3 & Hok4 & S176 & S160 & G10).
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HCm as (HC & Hold & HF & Hk & [SP72 SP56] & G20 & G21 & G22 & G26).
pose proof HF as (Hinv & HTc & HTlt & Hi & Hha & Hz).
pose proof HC as (HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Himg & HPerm & Hperm & Hkept).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (rk_frame_facts _ _ _ _ _ _ _ _ _ HC) as (Fceil & F47 & F32 & Fpres).
destruct (rk_img_facts _ _ _ _ _ _ _ _ _ HC) as (Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
destruct (ts_next_facts _ HTc HTlt) as (Tn1 & Tn2 & Tn3 & Tn4 & Tn5). fold (ac_Tn C) in Tn1, Tn2, Tn3, Tn4.
set (Tn := ac_Tn C) in *.
pose proof Hobj as OBJ. cbn [obj_at LAY_Cht ac_cells] in OBJ. unfold field_ok in OBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in OBJ.
destruct OBJ as ([_ Bf] & [_ Bh] & [_ Bu] & [_ Bp] & [_ Bx] & [_ Bc] & [_ BT] & _). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Bf, Bh, Bu, Bp, Bx.
pose proof HOP as (O24 & O27 & O26 & O23 & O18 & O22 & O17 & O16 & Os0 & Ora).
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) (ac_T C)).
set (xv := [i; ha; u1; h1]).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E37 : ew E 37 = Z_to_bv 64 (ac_x C)) by exact (HV 5%nat _ eq_refl).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (E20 : ew E 20 = Z_to_bv 64 (3 * Tn)) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (E22 : ew E 22 = Z_to_bv 64 Tn) by (rewrite (HE 22%nat 22%bv eq_refl); exact G22).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
assert (D4T : sv_denot E (SAlu ALU_SLL (SOff 22 0) (SLit 2)) = Z_to_bv 64 (4 * Tn)).
{ rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 22 Tn E22) by (clear - Tn2; lia). rewrite (U_lit E 2) by lia.
change (Z.land 2 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite zcanon_id by (unfold M64; clear - Tn2; lia). lia. }
assert (Ru1 : 0 <= u1 < 2 ^ 64) by (destruct Hok4 as [-> | X]; [clear; lia | clear - X; lia]).
assert (Rh1 : 0 <= h1 < 2 ^ 64) by (destruct Hok3 as [-> | X]; [clear; lia | clear - X; lia]).
assert (E54 : ew E 54 = Z_to_bv 64 u1) by exact (HV 22%nat _ eq_refl).
assert (E55 : ew E 55 = Z_to_bv 64 h1) by exact (HV 23%nat _ eq_refl).
assert (E24 : ew E 24 = Z_to_bv 64 (4 * Tn)) by (rewrite (HE 24%nat 24%bv eq_refl); exact (proj1 (proj2 (proj2 (proj2 Hres))))).
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_MA2R false [(10%bv, SOff 54 0)] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [ck 160 (SOff 22 0); ck 176 (SOff 55 0)] [] [] [] [] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) (ac_T C) xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_cons; [|apply Forall_nil]. split; [reflexivity|]. cbn [fst snd]. rewrite G10. symmetry. rewrite (denot_off E 54 u1 0 E54 Ru1), Z.add_0_r. reflexivity. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold ck.
- apply (chunk_ok_val trasegs E _ s1v 160 8 _ Tn); [rewrite (denot_off E 22 Tn 0 E22 ltac:(clear - Tn2; lia)), Z.add_0_r; reflexivity | clear - Tn2; lia | lia | exact S160].
- apply (chunk_ok_val trasegs E _ s1v 176 8 _ h1); [rewrite (denot_off E 55 h1 0 E55 Rh1), Z.add_0_r; reflexivity | exact Rh1 | lia | exact S176]. }
{ apply Forall_nil. }
{ apply Forall_nil. }
{ intros e []. }
{ exact I. }
{ exact I. }
{ exact I. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 56 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan A_malloc_tra.
{ apply (hk_awr_ok s1v tb fmt E false _ _ _ _ [] STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 56 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false _ _ _ _ [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 56 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [20; 21; 22; 26]%bv ++ [23; 24; 27]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 56 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 56 E Ex e HAE1 Hat); exact Dv);
assert (SLOT : forall idx lo hi cs off e v, nth_error (ss_mem ssx) idx = Some (YQ0b.mkRegion (Some 9%nat) lo hi lo hi cs) -> In (ck off e) cs ->
sv_denot E e = Z_to_bv 64 v -> sv_atoms_lt 56 e = true -> 0 <= v < 2 ^ 64 -> val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + off) 8 v)
by (intros idx lo hi cs off e v Hnth Hin Dv Hat Hv;
apply (hk_slot_of_state s1v Ex ssx ms (w_H W) idx lo hi lo hi cs off e v HS Hnth Hin);
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (sv_denot_agree 56 E Ex e HAE1 Hat); exact Dv | exact Hv]) end.
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (SLOT 2%nat 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | reflexivity | clear - Hi HN; lia]).
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (SLOT 1%nat 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | reflexivity | clear - Hha; lia]).
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
assert (HCm' : rz_common lyc Sc W (ms_regs ms) (ms_mem ms) mdx k C i ha 8 ((rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) ++ optb u1 (ac_Tn C))) end.
{ apply (rz_common_run lyc Sc W regs mem md k C i ha 8 ((rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) ++ optb u1 (ac_Tn C)) _ _ _ HCm); [intros y Hy; rewrite <- app_assoc; exact (rz_old_in C p1 x1 _ y Hy) | exact HJ | | exact KM1 | split; [exact SP72' | exact SP56']].
intros r Hr. apply HKR. rewrite app_assoc. apply in_or_app. left. exact Hr. }
split; [exact HCm'|]. split; [unfold rz_res in *; rewrite (HKR 23%bv ltac:(cbv; clear; tauto)), (HKR 24%bv ltac:(cbv; clear; tauto)), (HKR 27%bv ltac:(cbv; clear; tauto)); exact Hres|]. split; [exact Hok3|]. split; [exact Hok4|].
split; [apply (SLOT 4%nat 160 184 [ck 160 (SOff 22 0); ck 176 (SOff 55 0)] 176 (SOff 55 0) h1 eq_refl ltac:(right; left; reflexivity)); [rewrite (denot_off E 55 h1 0 E55 Rh1), Z.add_0_r; reflexivity | reflexivity | exact Rh1]|].
split; [apply (SLOT 4%nat 160 184 [ck 160 (SOff 22 0); ck 176 (SOff 55 0)] 160 (SOff 22 0) Tn eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 22 Tn 0 E22 ltac:(clear - Tn2; lia)), Z.add_0_r; reflexivity | reflexivity | clear - Tn2; lia]|].
split; [apply (SLOT 6%nat 296 304 [ck 296 (SOff 54 0)] 296 (SOff 54 0) u1 eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 54 u1 0 E54 Ru1), Z.add_0_r; reflexivity | reflexivity | exact Ru1]|].
split; [apply (RD 10%bv (SOff 24 0) (4 * Tn) eq_refl); [rewrite (denot_off E 24 (4 * Tn) 0 E24 ltac:(clear - Tn2; lia)), Z.add_0_r; reflexivity | reflexivity]|].
exact (RD 1%bv (SLit HL_MA3R) HL_MA3R eq_refl eq_refl eq_refl).
Qed.
Lemma hl_ma3 : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1,
at_MA3C lyc Sc W regs mem md k C i ha p1 x1 h1 u1 ->
SRr trasegs W (cfgat regs A_malloc_tra mem md)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 f1, c2 = cfgat regs2 HL_MA3R mem2 md2 /\ at_MA3R ly2 S2 W2 regs2 mem2 md2 (k + 1) C i ha p1 x1 h1 u1 f1).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 (HCm & Hres & Hok3 & Hok4 & S176 & S160 & S296 & G10 & Gra).
pose proof HCm as (HC & _ & (Hinv & HTc & HTlt & _) & Hk & _).
destruct (ts_next_facts _ HTc HTlt) as (Tn1 & Tn2 & Tn3 & Tn4 & Tn5). fold (ac_Tn C) in Tn1, Tn2, Tn3, Tn4.
pose proof (ts_rank_range (ac_T C)) as Hrk.
pose proof (bsum_rz_BL C p1 x1 ltac:(clear - Tn1 Tn5; lia)) as Hbs.
destruct saved_23_24_27 as (Sv23 & Sv24 & Sv27). destruct Hres as (Hok1 & Hok2 & G23 & G24 & G27).
eapply SRr_mono.
{ eapply (rz_malloc B TL LAWS ML AMALLOC STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH ch0
Hs1 HSTKA Hsp32 Htop32 HCH0 Hrav Hspine ltac:(destruct HOP as (_ & _ & _ & _ & _ & _ & _ & _ & Os0 & _); exact Os0) Himgl HimgP HEV HLIVE
lyc Sc W regs mem md k (ac_cells C) ((rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) ++ optb u1 (ac_Tn C)) (4 * ac_Tn C) HL_MA3R HC G10).
- unfold MALLOC_MAX. clear - Tn2. lia.
- pose proof (bsum_optb (rz_BL C p1 x1) h1 (3 * ac_Tn C) ltac:(clear - Tn2; lia)) as Hb1. pose proof (bsum_optb (rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) u1 (ac_Tn C) ltac:(clear - Tn2; lia)) as Hb2. clear - Hbs Hb1 Hb2 Tn4 Tn5 Tn1. lia.
- clear - Hk Hrk. lia.
- exact Gra.
- unfold HL_MA3R. clear. lia.
- reflexivity.
- rewrite (tl_code B TL). apply (hk_trace_in B TL sp0 rav s0v ch0 Hrav Hspine _ regs HL_MA3R); [unfold raZ; rewrite Gra; apply unsigned_lit_small; unfold HL_MA3R; clear; lia | vm_compute; reflexivity | vm_compute; reflexivity]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & f1 & -> & HC2 & HP2 & Ha0 & Hok & Hfr & Hoth & Hd2).
exists ly2, S2, regs2, mem2, md2, f1. split; [reflexivity|].
assert (Hres' : rz_res regs2 C p1 x1).
{ split; [exact Hok1|]. split; [exact Hok2|]. rewrite (aregs_get regs regs2 23%bv HP2 Sv23), (aregs_get regs regs2 24%bv HP2 Sv24), (aregs_get regs regs2 27%bv HP2 Sv27).
split; [exact G23|]. split; [exact G24 | exact G27]. }
assert (Hok' : rz_ok1 f1).
{ destruct Hok as [-> | Hok]; [left; reflexivity | right].
apply (rk_blk_bound ly2 S2 W2 regs2 mem2 md2 (k + 1) (ac_cells C) (((rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) ++ optb u1 (ac_Tn C)) ++ optb f1 (4 * ac_Tn C)) f1 (4 * ac_Tn C) HC2).
apply in_app_iff. right. unfold optb. destruct (Z.eqb_spec f1 0) as [X | _]; [exfalso; clear - X Hok; lia | left; reflexivity]. }
assert (HCm' : rz_common ly2 S2 W2 regs2 mem2 md2 (k + 1) C i ha 9 (((rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) ++ optb u1 (ac_Tn C)) ++ optb f1 (4 * ac_Tn C))).
{ apply (rz_common_call lyc Sc W regs mem md k C i ha 8 ((rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) ++ optb u1 (ac_Tn C)) ly2 S2 W2 regs2 mem2 md2 (k + 1) 9 _ HCm HC2 HP2 Hfr); [|lia|exact (gbud_malloc S Sc S2 k _ (proj2 Hk) Hd2 ltac:(clear - Tn2; lia))].
intros y Hy. apply Hoth. rewrite <- app_assoc. exact (rz_old_in C p1 x1 _ y Hy). }
split; [exact HCm'|]. split; [exact Hres'|]. split; [exact Hok3|]. split; [exact Hok4|]. split; [exact Hok'|].
split; [exact (slot_kept W W2 mem mem2 176 h1 ltac:(lia) ltac:(lia) Hfr S176)|]. split; [exact (slot_kept W W2 mem mem2 160 _ ltac:(lia) ltac:(lia) Hfr S160)|].
split; [exact (slot_kept W W2 mem mem2 296 u1 ltac:(lia) ltac:(lia) Hfr S296) | exact Ha0].
Qed.
Lemma hl_ma3r_f1 : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1,
at_MA3R lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 -> (p1 = 0) ->
SRr trasegs W (cfgat regs HL_MA3R mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 HL_FAIL mem2 md2 /\ at_FAIL lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 (HCm & Hres & Hok3 & Hok4 & Hok5 & S176 & S160 & S296 & G10) Hz0.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HCm as (HC & Hold & HF & Hk & [SP72 SP56] & G20 & G21 & G22 & G26).
pose proof HF as (Hinv & HTc & HTlt & Hi & Hha & Hz).
pose proof HC as (HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Himg & HPerm & Hperm & Hkept).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (rk_frame_facts _ _ _ _ _ _ _ _ _ HC) as (Fceil & F47 & F32 & Fpres).
destruct (rk_img_facts _ _ _ _ _ _ _ _ _ HC) as (Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
destruct (ts_next_facts _ HTc HTlt) as (Tn1 & Tn2 & Tn3 & Tn4 & Tn5). fold (ac_Tn C) in Tn1, Tn2, Tn3, Tn4.
set (Tn := ac_Tn C) in *.
pose proof Hobj as OBJ. cbn [obj_at LAY_Cht ac_cells] in OBJ. unfold field_ok in OBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in OBJ.
destruct OBJ as ([_ Bf] & [_ Bh] & [_ Bu] & [_ Bp] & [_ Bx] & [_ Bc] & [_ BT] & _). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Bf, Bh, Bu, Bp, Bx.
pose proof HOP as (O24 & O27 & O26 & O23 & O18 & O22 & O17 & O16 & Os0 & Ora).
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) (ac_T C)).
set (xv := [i; ha; f1; h1; u1]).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E37 : ew E 37 = Z_to_bv 64 (ac_x C)) by exact (HV 5%nat _ eq_refl).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (E20 : ew E 20 = Z_to_bv 64 (3 * Tn)) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (E22 : ew E 22 = Z_to_bv 64 Tn) by (rewrite (HE 22%nat 22%bv eq_refl); exact G22).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
assert (D4T : sv_denot E (SAlu ALU_SLL (SOff 22 0) (SLit 2)) = Z_to_bv 64 (4 * Tn)).
{ rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 22 Tn E22) by (clear - Tn2; lia). rewrite (U_lit E 2) by lia.
change (Z.land 2 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite zcanon_id by (unfold M64; clear - Tn2; lia). lia. }
assert (Rf1 : 0 <= f1 < 2 ^ 64) by (destruct Hok5 as [-> | X]; [clear; lia | clear - X; lia]).
assert (Rh1 : 0 <= h1 < 2 ^ 64) by (destruct Hok3 as [-> | X]; [clear; lia | clear - X; lia]).
assert (Ru1 : 0 <= u1 < 2 ^ 64) by (destruct Hok4 as [-> | X]; [clear; lia | clear - X; lia]).
pose proof Hres as (Hok1 & Hok2 & G23 & G24 & G27).
assert (Rp1 : 0 <= p1 < 2 ^ 64) by (destruct Hok1 as [-> | X]; [clear; lia | clear - X; lia]).
assert (Rx1 : 0 <= x1 < 2 ^ 64) by (destruct Hok2 as [-> | X]; [clear; lia | clear - X; lia]).
assert (E54 : ew E 54 = Z_to_bv 64 f1) by exact (HV 22%nat _ eq_refl).
assert (E55 : ew E 55 = Z_to_bv 64 h1) by exact (HV 23%nat _ eq_refl).
assert (E56 : ew E 56 = Z_to_bv 64 u1) by exact (HV 24%nat _ eq_refl).
assert (E23 : ew E 23 = Z_to_bv 64 p1) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (E27 : ew E 27 = Z_to_bv 64 x1) by (rewrite (HE 27%nat 27%bv eq_refl); exact G27).
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_MA3R false [(10%bv, SOff 54 0)] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [ck 160 (SOff 22 0); ck 176 (SOff 55 0)] [ck 296 (SOff 56 0)] [] [] [mkAC BC_EQ (SOff 23 0) (SLit 0)] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) (ac_T C) xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_cons; [|apply Forall_nil]. split; [reflexivity|]. cbn [fst snd]. rewrite G10. symmetry. rewrite (denot_off E 54 f1 0 E54 Rf1), Z.add_0_r. reflexivity. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold ck.
- apply (chunk_ok_val trasegs E _ s1v 160 8 _ Tn); [rewrite (denot_off E 22 Tn 0 E22 ltac:(clear - Tn2; lia)), Z.add_0_r; reflexivity | clear - Tn2; lia | lia | exact S160].
- apply (chunk_ok_val trasegs E _ s1v 176 8 _ h1); [rewrite (denot_off E 55 h1 0 E55 Rh1), Z.add_0_r; reflexivity | exact Rh1 | lia | exact S176]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 296 8 _ u1); [rewrite (denot_off E 56 u1 0 E56 Ru1), Z.add_0_r; reflexivity | exact Ru1 | lia | exact S296]. }
{ apply Forall_nil. }
{ intros e []. }
{ exact I. }
{ exact I. }
{ cbn [conds_ok]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_eq_U, (U_atom E 23 p1 E23 Rp1), (U_lit E 0) by lia; apply Z.eqb_eq; exact Hz0|]. exact I. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 57 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan HL_FAIL.
{ apply (hk_awr_ok s1v tb fmt E false _ _ _ _ [] STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 57 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false _ _ _ _ [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 57 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [20; 21; 22; 26]%bv ++ [23; 24; 27]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 57 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 57 E Ex e HAE1 Hat); exact Dv);
assert (SLOT : forall idx lo hi cs off e v, nth_error (ss_mem ssx) idx = Some (YQ0b.mkRegion (Some 9%nat) lo hi lo hi cs) -> In (ck off e) cs ->
sv_denot E e = Z_to_bv 64 v -> sv_atoms_lt 57 e = true -> 0 <= v < 2 ^ 64 -> val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + off) 8 v)
by (intros idx lo hi cs off e v Hnth Hin Dv Hat Hv;
apply (hk_slot_of_state s1v Ex ssx ms (w_H W) idx lo hi lo hi cs off e v HS Hnth Hin);
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (sv_denot_agree 57 E Ex e HAE1 Hat); exact Dv | exact Hv]) end.
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (SLOT 2%nat 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | reflexivity | clear - Hi HN; lia]).
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (SLOT 1%nat 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | reflexivity | clear - Hha; lia]).
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
assert (HCm' : rz_common lyc Sc W (ms_regs ms) (ms_mem ms) mdx k C i ha 9 (((rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) ++ optb u1 (ac_Tn C)) ++ optb f1 (4 * ac_Tn C))) end.
{ apply (rz_common_run lyc Sc W regs mem md k C i ha 9 (((rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) ++ optb u1 (ac_Tn C)) ++ optb f1 (4 * ac_Tn C)) _ _ _ HCm); [intros y Hy; rewrite <- !app_assoc; exact (rz_old_in C p1 x1 _ y Hy) | exact HJ | | exact KM1 | split; [exact SP72' | exact SP56']].
intros r Hr. apply HKR. rewrite app_assoc. apply in_or_app. left. exact Hr. }
split; [exact HCm'|]. split; [unfold rz_res in *; rewrite (HKR 23%bv ltac:(cbv; clear; tauto)), (HKR 24%bv ltac:(cbv; clear; tauto)), (HKR 27%bv ltac:(cbv; clear; tauto)); exact Hres|]. split; [exact Hok3|]. split; [exact Hok4|]. split; [exact Hok5|].
split; [apply (SLOT 4%nat 160 184 [ck 168 (SOff 54 0); ck 160 (SOff 22 0); ck 176 (SOff 55 0)] 176 (SOff 55 0) h1 eq_refl ltac:(right; right; left; reflexivity)); [rewrite (denot_off E 55 h1 0 E55 Rh1), Z.add_0_r; reflexivity | reflexivity | exact Rh1]|].
split; [apply (SLOT 6%nat 296 304 [ck 296 (SOff 56 0)] 296 (SOff 56 0) u1 eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 56 u1 0 E56 Ru1), Z.add_0_r; reflexivity | reflexivity | exact Ru1]|].
split; [apply (SLOT 4%nat 160 184 [ck 168 (SOff 54 0); ck 160 (SOff 22 0); ck 176 (SOff 55 0)] 168 (SOff 54 0) f1 eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 54 f1 0 E54 Rf1), Z.add_0_r; reflexivity | reflexivity | exact Rf1]|].
left; exact Hz0.
Qed.
Lemma hl_ma3r_f2 : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1,
at_MA3R lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 -> (p1 <> 0 /\ x1 = 0) ->
SRr trasegs W (cfgat regs HL_MA3R mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 HL_FAIL mem2 md2 /\ at_FAIL lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 (HCm & Hres & Hok3 & Hok4 & Hok5 & S176 & S160 & S296 & G10) (Hnz0 & Hz1).
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HCm as (HC & Hold & HF & Hk & [SP72 SP56] & G20 & G21 & G22 & G26).
pose proof HF as (Hinv & HTc & HTlt & Hi & Hha & Hz).
pose proof HC as (HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Himg & HPerm & Hperm & Hkept).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (rk_frame_facts _ _ _ _ _ _ _ _ _ HC) as (Fceil & F47 & F32 & Fpres).
destruct (rk_img_facts _ _ _ _ _ _ _ _ _ HC) as (Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
destruct (ts_next_facts _ HTc HTlt) as (Tn1 & Tn2 & Tn3 & Tn4 & Tn5). fold (ac_Tn C) in Tn1, Tn2, Tn3, Tn4.
set (Tn := ac_Tn C) in *.
pose proof Hobj as OBJ. cbn [obj_at LAY_Cht ac_cells] in OBJ. unfold field_ok in OBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in OBJ.
destruct OBJ as ([_ Bf] & [_ Bh] & [_ Bu] & [_ Bp] & [_ Bx] & [_ Bc] & [_ BT] & _). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Bf, Bh, Bu, Bp, Bx.
pose proof HOP as (O24 & O27 & O26 & O23 & O18 & O22 & O17 & O16 & Os0 & Ora).
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) (ac_T C)).
set (xv := [i; ha; f1; h1; u1]).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E37 : ew E 37 = Z_to_bv 64 (ac_x C)) by exact (HV 5%nat _ eq_refl).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (E20 : ew E 20 = Z_to_bv 64 (3 * Tn)) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (E22 : ew E 22 = Z_to_bv 64 Tn) by (rewrite (HE 22%nat 22%bv eq_refl); exact G22).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
assert (D4T : sv_denot E (SAlu ALU_SLL (SOff 22 0) (SLit 2)) = Z_to_bv 64 (4 * Tn)).
{ rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 22 Tn E22) by (clear - Tn2; lia). rewrite (U_lit E 2) by lia.
change (Z.land 2 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite zcanon_id by (unfold M64; clear - Tn2; lia). lia. }
assert (Rf1 : 0 <= f1 < 2 ^ 64) by (destruct Hok5 as [-> | X]; [clear; lia | clear - X; lia]).
assert (Rh1 : 0 <= h1 < 2 ^ 64) by (destruct Hok3 as [-> | X]; [clear; lia | clear - X; lia]).
assert (Ru1 : 0 <= u1 < 2 ^ 64) by (destruct Hok4 as [-> | X]; [clear; lia | clear - X; lia]).
pose proof Hres as (Hok1 & Hok2 & G23 & G24 & G27).
assert (Rp1 : 0 <= p1 < 2 ^ 64) by (destruct Hok1 as [-> | X]; [clear; lia | clear - X; lia]).
assert (Rx1 : 0 <= x1 < 2 ^ 64) by (destruct Hok2 as [-> | X]; [clear; lia | clear - X; lia]).
assert (E54 : ew E 54 = Z_to_bv 64 f1) by exact (HV 22%nat _ eq_refl).
assert (E55 : ew E 55 = Z_to_bv 64 h1) by exact (HV 23%nat _ eq_refl).
assert (E56 : ew E 56 = Z_to_bv 64 u1) by exact (HV 24%nat _ eq_refl).
assert (E23 : ew E 23 = Z_to_bv 64 p1) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (E27 : ew E 27 = Z_to_bv 64 x1) by (rewrite (HE 27%nat 27%bv eq_refl); exact G27).
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_MA3R false [(10%bv, SOff 54 0)] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [ck 160 (SOff 22 0); ck 176 (SOff 55 0)] [ck 296 (SOff 56 0)] [] [] [mkAC BC_NE (SOff 23 0) (SLit 0); mkAC BC_EQ (SOff 27 0) (SLit 0)] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) (ac_T C) xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_cons; [|apply Forall_nil]. split; [reflexivity|]. cbn [fst snd]. rewrite G10. symmetry. rewrite (denot_off E 54 f1 0 E54 Rf1), Z.add_0_r. reflexivity. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold ck.
- apply (chunk_ok_val trasegs E _ s1v 160 8 _ Tn); [rewrite (denot_off E 22 Tn 0 E22 ltac:(clear - Tn2; lia)), Z.add_0_r; reflexivity | clear - Tn2; lia | lia | exact S160].
- apply (chunk_ok_val trasegs E _ s1v 176 8 _ h1); [rewrite (denot_off E 55 h1 0 E55 Rh1), Z.add_0_r; reflexivity | exact Rh1 | lia | exact S176]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 296 8 _ u1); [rewrite (denot_off E 56 u1 0 E56 Ru1), Z.add_0_r; reflexivity | exact Ru1 | lia | exact S296]. }
{ apply Forall_nil. }
{ intros e []. }
{ exact I. }
{ exact I. }
{ cbn [conds_ok]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_ne_U, (U_atom E 23 p1 E23 Rp1), (U_lit E 0) by lia; apply Bool.negb_true_iff, Z.eqb_neq; exact Hnz0|]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_eq_U, (U_atom E 27 x1 E27 Rx1), (U_lit E 0) by lia; apply Z.eqb_eq; exact Hz1|]. exact I. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 57 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan HL_FAIL.
{ apply (hk_awr_ok s1v tb fmt E false _ _ _ _ [] STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 57 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false _ _ _ _ [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 57 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [20; 21; 22; 26]%bv ++ [23; 24; 27]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 57 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 57 E Ex e HAE1 Hat); exact Dv);
assert (SLOT : forall idx lo hi cs off e v, nth_error (ss_mem ssx) idx = Some (YQ0b.mkRegion (Some 9%nat) lo hi lo hi cs) -> In (ck off e) cs ->
sv_denot E e = Z_to_bv 64 v -> sv_atoms_lt 57 e = true -> 0 <= v < 2 ^ 64 -> val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + off) 8 v)
by (intros idx lo hi cs off e v Hnth Hin Dv Hat Hv;
apply (hk_slot_of_state s1v Ex ssx ms (w_H W) idx lo hi lo hi cs off e v HS Hnth Hin);
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (sv_denot_agree 57 E Ex e HAE1 Hat); exact Dv | exact Hv]) end.
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (SLOT 2%nat 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | reflexivity | clear - Hi HN; lia]).
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (SLOT 1%nat 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | reflexivity | clear - Hha; lia]).
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
assert (HCm' : rz_common lyc Sc W (ms_regs ms) (ms_mem ms) mdx k C i ha 9 (((rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) ++ optb u1 (ac_Tn C)) ++ optb f1 (4 * ac_Tn C))) end.
{ apply (rz_common_run lyc Sc W regs mem md k C i ha 9 (((rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) ++ optb u1 (ac_Tn C)) ++ optb f1 (4 * ac_Tn C)) _ _ _ HCm); [intros y Hy; rewrite <- !app_assoc; exact (rz_old_in C p1 x1 _ y Hy) | exact HJ | | exact KM1 | split; [exact SP72' | exact SP56']].
intros r Hr. apply HKR. rewrite app_assoc. apply in_or_app. left. exact Hr. }
split; [exact HCm'|]. split; [unfold rz_res in *; rewrite (HKR 23%bv ltac:(cbv; clear; tauto)), (HKR 24%bv ltac:(cbv; clear; tauto)), (HKR 27%bv ltac:(cbv; clear; tauto)); exact Hres|]. split; [exact Hok3|]. split; [exact Hok4|]. split; [exact Hok5|].
split; [apply (SLOT 4%nat 160 184 [ck 168 (SOff 54 0); ck 160 (SOff 22 0); ck 176 (SOff 55 0)] 176 (SOff 55 0) h1 eq_refl ltac:(right; right; left; reflexivity)); [rewrite (denot_off E 55 h1 0 E55 Rh1), Z.add_0_r; reflexivity | reflexivity | exact Rh1]|].
split; [apply (SLOT 6%nat 296 304 [ck 296 (SOff 56 0)] 296 (SOff 56 0) u1 eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 56 u1 0 E56 Ru1), Z.add_0_r; reflexivity | reflexivity | exact Ru1]|].
split; [apply (SLOT 4%nat 160 184 [ck 168 (SOff 54 0); ck 160 (SOff 22 0); ck 176 (SOff 55 0)] 168 (SOff 54 0) f1 eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 54 f1 0 E54 Rf1), Z.add_0_r; reflexivity | reflexivity | exact Rf1]|].
right; left; exact Hz1.
Qed.
Lemma hl_ma3r_f3 : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1,
at_MA3R lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 -> (p1 <> 0 /\ x1 <> 0 /\ h1 = 0) ->
SRr trasegs W (cfgat regs HL_MA3R mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 HL_FAIL mem2 md2 /\ at_FAIL lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 (HCm & Hres & Hok3 & Hok4 & Hok5 & S176 & S160 & S296 & G10) (Hnz0 & Hnz1 & Hz2).
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HCm as (HC & Hold & HF & Hk & [SP72 SP56] & G20 & G21 & G22 & G26).
pose proof HF as (Hinv & HTc & HTlt & Hi & Hha & Hz).
pose proof HC as (HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Himg & HPerm & Hperm & Hkept).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (rk_frame_facts _ _ _ _ _ _ _ _ _ HC) as (Fceil & F47 & F32 & Fpres).
destruct (rk_img_facts _ _ _ _ _ _ _ _ _ HC) as (Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
destruct (ts_next_facts _ HTc HTlt) as (Tn1 & Tn2 & Tn3 & Tn4 & Tn5). fold (ac_Tn C) in Tn1, Tn2, Tn3, Tn4.
set (Tn := ac_Tn C) in *.
pose proof Hobj as OBJ. cbn [obj_at LAY_Cht ac_cells] in OBJ. unfold field_ok in OBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in OBJ.
destruct OBJ as ([_ Bf] & [_ Bh] & [_ Bu] & [_ Bp] & [_ Bx] & [_ Bc] & [_ BT] & _). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Bf, Bh, Bu, Bp, Bx.
pose proof HOP as (O24 & O27 & O26 & O23 & O18 & O22 & O17 & O16 & Os0 & Ora).
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) (ac_T C)).
set (xv := [i; ha; f1; h1; u1]).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E37 : ew E 37 = Z_to_bv 64 (ac_x C)) by exact (HV 5%nat _ eq_refl).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (E20 : ew E 20 = Z_to_bv 64 (3 * Tn)) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (E22 : ew E 22 = Z_to_bv 64 Tn) by (rewrite (HE 22%nat 22%bv eq_refl); exact G22).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
assert (D4T : sv_denot E (SAlu ALU_SLL (SOff 22 0) (SLit 2)) = Z_to_bv 64 (4 * Tn)).
{ rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 22 Tn E22) by (clear - Tn2; lia). rewrite (U_lit E 2) by lia.
change (Z.land 2 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite zcanon_id by (unfold M64; clear - Tn2; lia). lia. }
assert (Rf1 : 0 <= f1 < 2 ^ 64) by (destruct Hok5 as [-> | X]; [clear; lia | clear - X; lia]).
assert (Rh1 : 0 <= h1 < 2 ^ 64) by (destruct Hok3 as [-> | X]; [clear; lia | clear - X; lia]).
assert (Ru1 : 0 <= u1 < 2 ^ 64) by (destruct Hok4 as [-> | X]; [clear; lia | clear - X; lia]).
pose proof Hres as (Hok1 & Hok2 & G23 & G24 & G27).
assert (Rp1 : 0 <= p1 < 2 ^ 64) by (destruct Hok1 as [-> | X]; [clear; lia | clear - X; lia]).
assert (Rx1 : 0 <= x1 < 2 ^ 64) by (destruct Hok2 as [-> | X]; [clear; lia | clear - X; lia]).
assert (E54 : ew E 54 = Z_to_bv 64 f1) by exact (HV 22%nat _ eq_refl).
assert (E55 : ew E 55 = Z_to_bv 64 h1) by exact (HV 23%nat _ eq_refl).
assert (E56 : ew E 56 = Z_to_bv 64 u1) by exact (HV 24%nat _ eq_refl).
assert (E23 : ew E 23 = Z_to_bv 64 p1) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (E27 : ew E 27 = Z_to_bv 64 x1) by (rewrite (HE 27%nat 27%bv eq_refl); exact G27).
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_MA3R false [(10%bv, SOff 54 0)] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [ck 160 (SOff 22 0); ck 176 (SOff 55 0)] [ck 296 (SOff 56 0)] [] [] [mkAC BC_NE (SOff 23 0) (SLit 0); mkAC BC_NE (SOff 27 0) (SLit 0); mkAC BC_EQ (SOff 55 0) (SLit 0)] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) (ac_T C) xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_cons; [|apply Forall_nil]. split; [reflexivity|]. cbn [fst snd]. rewrite G10. symmetry. rewrite (denot_off E 54 f1 0 E54 Rf1), Z.add_0_r. reflexivity. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold ck.
- apply (chunk_ok_val trasegs E _ s1v 160 8 _ Tn); [rewrite (denot_off E 22 Tn 0 E22 ltac:(clear - Tn2; lia)), Z.add_0_r; reflexivity | clear - Tn2; lia | lia | exact S160].
- apply (chunk_ok_val trasegs E _ s1v 176 8 _ h1); [rewrite (denot_off E 55 h1 0 E55 Rh1), Z.add_0_r; reflexivity | exact Rh1 | lia | exact S176]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 296 8 _ u1); [rewrite (denot_off E 56 u1 0 E56 Ru1), Z.add_0_r; reflexivity | exact Ru1 | lia | exact S296]. }
{ apply Forall_nil. }
{ intros e []. }
{ exact I. }
{ exact I. }
{ cbn [conds_ok]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_ne_U, (U_atom E 23 p1 E23 Rp1), (U_lit E 0) by lia; apply Bool.negb_true_iff, Z.eqb_neq; exact Hnz0|]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_ne_U, (U_atom E 27 x1 E27 Rx1), (U_lit E 0) by lia; apply Bool.negb_true_iff, Z.eqb_neq; exact Hnz1|]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_eq_U, (U_atom E 55 h1 E55 Rh1), (U_lit E 0) by lia; apply Z.eqb_eq; exact Hz2|]. exact I. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 57 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan HL_FAIL.
{ apply (hk_awr_ok s1v tb fmt E false _ _ _ _ [] STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 57 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false _ _ _ _ [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 57 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [20; 21; 22; 26]%bv ++ [23; 24; 27]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 57 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 57 E Ex e HAE1 Hat); exact Dv);
assert (SLOT : forall idx lo hi cs off e v, nth_error (ss_mem ssx) idx = Some (YQ0b.mkRegion (Some 9%nat) lo hi lo hi cs) -> In (ck off e) cs ->
sv_denot E e = Z_to_bv 64 v -> sv_atoms_lt 57 e = true -> 0 <= v < 2 ^ 64 -> val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + off) 8 v)
by (intros idx lo hi cs off e v Hnth Hin Dv Hat Hv;
apply (hk_slot_of_state s1v Ex ssx ms (w_H W) idx lo hi lo hi cs off e v HS Hnth Hin);
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (sv_denot_agree 57 E Ex e HAE1 Hat); exact Dv | exact Hv]) end.
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (SLOT 2%nat 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | reflexivity | clear - Hi HN; lia]).
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (SLOT 1%nat 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | reflexivity | clear - Hha; lia]).
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
assert (HCm' : rz_common lyc Sc W (ms_regs ms) (ms_mem ms) mdx k C i ha 9 (((rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) ++ optb u1 (ac_Tn C)) ++ optb f1 (4 * ac_Tn C))) end.
{ apply (rz_common_run lyc Sc W regs mem md k C i ha 9 (((rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) ++ optb u1 (ac_Tn C)) ++ optb f1 (4 * ac_Tn C)) _ _ _ HCm); [intros y Hy; rewrite <- !app_assoc; exact (rz_old_in C p1 x1 _ y Hy) | exact HJ | | exact KM1 | split; [exact SP72' | exact SP56']].
intros r Hr. apply HKR. rewrite app_assoc. apply in_or_app. left. exact Hr. }
split; [exact HCm'|]. split; [unfold rz_res in *; rewrite (HKR 23%bv ltac:(cbv; clear; tauto)), (HKR 24%bv ltac:(cbv; clear; tauto)), (HKR 27%bv ltac:(cbv; clear; tauto)); exact Hres|]. split; [exact Hok3|]. split; [exact Hok4|]. split; [exact Hok5|].
split; [apply (SLOT 4%nat 160 184 [ck 168 (SOff 54 0); ck 160 (SOff 22 0); ck 176 (SOff 55 0)] 176 (SOff 55 0) h1 eq_refl ltac:(right; right; left; reflexivity)); [rewrite (denot_off E 55 h1 0 E55 Rh1), Z.add_0_r; reflexivity | reflexivity | exact Rh1]|].
split; [apply (SLOT 6%nat 296 304 [ck 296 (SOff 56 0)] 296 (SOff 56 0) u1 eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 56 u1 0 E56 Ru1), Z.add_0_r; reflexivity | reflexivity | exact Ru1]|].
split; [apply (SLOT 4%nat 160 184 [ck 168 (SOff 54 0); ck 160 (SOff 22 0); ck 176 (SOff 55 0)] 168 (SOff 54 0) f1 eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 54 f1 0 E54 Rf1), Z.add_0_r; reflexivity | reflexivity | exact Rf1]|].
right; right; left; exact Hz2.
Qed.
Lemma hl_ma3r_f4 : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1,
at_MA3R lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 -> (p1 <> 0 /\ x1 <> 0 /\ h1 <> 0 /\ u1 = 0) ->
SRr trasegs W (cfgat regs HL_MA3R mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 HL_FAIL mem2 md2 /\ at_FAIL lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 (HCm & Hres & Hok3 & Hok4 & Hok5 & S176 & S160 & S296 & G10) (Hnz0 & Hnz1 & Hnz2 & Hz3).
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HCm as (HC & Hold & HF & Hk & [SP72 SP56] & G20 & G21 & G22 & G26).
pose proof HF as (Hinv & HTc & HTlt & Hi & Hha & Hz).
pose proof HC as (HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Himg & HPerm & Hperm & Hkept).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (rk_frame_facts _ _ _ _ _ _ _ _ _ HC) as (Fceil & F47 & F32 & Fpres).
destruct (rk_img_facts _ _ _ _ _ _ _ _ _ HC) as (Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
destruct (ts_next_facts _ HTc HTlt) as (Tn1 & Tn2 & Tn3 & Tn4 & Tn5). fold (ac_Tn C) in Tn1, Tn2, Tn3, Tn4.
set (Tn := ac_Tn C) in *.
pose proof Hobj as OBJ. cbn [obj_at LAY_Cht ac_cells] in OBJ. unfold field_ok in OBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in OBJ.
destruct OBJ as ([_ Bf] & [_ Bh] & [_ Bu] & [_ Bp] & [_ Bx] & [_ Bc] & [_ BT] & _). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Bf, Bh, Bu, Bp, Bx.
pose proof HOP as (O24 & O27 & O26 & O23 & O18 & O22 & O17 & O16 & Os0 & Ora).
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) (ac_T C)).
set (xv := [i; ha; f1; h1; u1]).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E37 : ew E 37 = Z_to_bv 64 (ac_x C)) by exact (HV 5%nat _ eq_refl).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (E20 : ew E 20 = Z_to_bv 64 (3 * Tn)) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (E22 : ew E 22 = Z_to_bv 64 Tn) by (rewrite (HE 22%nat 22%bv eq_refl); exact G22).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
assert (D4T : sv_denot E (SAlu ALU_SLL (SOff 22 0) (SLit 2)) = Z_to_bv 64 (4 * Tn)).
{ rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 22 Tn E22) by (clear - Tn2; lia). rewrite (U_lit E 2) by lia.
change (Z.land 2 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite zcanon_id by (unfold M64; clear - Tn2; lia). lia. }
assert (Rf1 : 0 <= f1 < 2 ^ 64) by (destruct Hok5 as [-> | X]; [clear; lia | clear - X; lia]).
assert (Rh1 : 0 <= h1 < 2 ^ 64) by (destruct Hok3 as [-> | X]; [clear; lia | clear - X; lia]).
assert (Ru1 : 0 <= u1 < 2 ^ 64) by (destruct Hok4 as [-> | X]; [clear; lia | clear - X; lia]).
pose proof Hres as (Hok1 & Hok2 & G23 & G24 & G27).
assert (Rp1 : 0 <= p1 < 2 ^ 64) by (destruct Hok1 as [-> | X]; [clear; lia | clear - X; lia]).
assert (Rx1 : 0 <= x1 < 2 ^ 64) by (destruct Hok2 as [-> | X]; [clear; lia | clear - X; lia]).
assert (E54 : ew E 54 = Z_to_bv 64 f1) by exact (HV 22%nat _ eq_refl).
assert (E55 : ew E 55 = Z_to_bv 64 h1) by exact (HV 23%nat _ eq_refl).
assert (E56 : ew E 56 = Z_to_bv 64 u1) by exact (HV 24%nat _ eq_refl).
assert (E23 : ew E 23 = Z_to_bv 64 p1) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (E27 : ew E 27 = Z_to_bv 64 x1) by (rewrite (HE 27%nat 27%bv eq_refl); exact G27).
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_MA3R false [(10%bv, SOff 54 0)] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [ck 160 (SOff 22 0); ck 176 (SOff 55 0)] [ck 296 (SOff 56 0)] [] [] [mkAC BC_NE (SOff 23 0) (SLit 0); mkAC BC_NE (SOff 27 0) (SLit 0); mkAC BC_NE (SOff 55 0) (SLit 0); mkAC BC_EQ (SOff 56 0) (SLit 0)] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) (ac_T C) xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_cons; [|apply Forall_nil]. split; [reflexivity|]. cbn [fst snd]. rewrite G10. symmetry. rewrite (denot_off E 54 f1 0 E54 Rf1), Z.add_0_r. reflexivity. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold ck.
- apply (chunk_ok_val trasegs E _ s1v 160 8 _ Tn); [rewrite (denot_off E 22 Tn 0 E22 ltac:(clear - Tn2; lia)), Z.add_0_r; reflexivity | clear - Tn2; lia | lia | exact S160].
- apply (chunk_ok_val trasegs E _ s1v 176 8 _ h1); [rewrite (denot_off E 55 h1 0 E55 Rh1), Z.add_0_r; reflexivity | exact Rh1 | lia | exact S176]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 296 8 _ u1); [rewrite (denot_off E 56 u1 0 E56 Ru1), Z.add_0_r; reflexivity | exact Ru1 | lia | exact S296]. }
{ apply Forall_nil. }
{ intros e []. }
{ exact I. }
{ exact I. }
{ cbn [conds_ok]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_ne_U, (U_atom E 23 p1 E23 Rp1), (U_lit E 0) by lia; apply Bool.negb_true_iff, Z.eqb_neq; exact Hnz0|]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_ne_U, (U_atom E 27 x1 E27 Rx1), (U_lit E 0) by lia; apply Bool.negb_true_iff, Z.eqb_neq; exact Hnz1|]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_ne_U, (U_atom E 55 h1 E55 Rh1), (U_lit E 0) by lia; apply Bool.negb_true_iff, Z.eqb_neq; exact Hnz2|]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_eq_U, (U_atom E 56 u1 E56 Ru1), (U_lit E 0) by lia; apply Z.eqb_eq; exact Hz3|]. exact I. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 57 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan HL_FAIL.
{ apply (hk_awr_ok s1v tb fmt E false _ _ _ _ [] STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 57 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false _ _ _ _ [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 57 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [20; 21; 22; 26]%bv ++ [23; 24; 27]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 57 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 57 E Ex e HAE1 Hat); exact Dv);
assert (SLOT : forall idx lo hi cs off e v, nth_error (ss_mem ssx) idx = Some (YQ0b.mkRegion (Some 9%nat) lo hi lo hi cs) -> In (ck off e) cs ->
sv_denot E e = Z_to_bv 64 v -> sv_atoms_lt 57 e = true -> 0 <= v < 2 ^ 64 -> val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + off) 8 v)
by (intros idx lo hi cs off e v Hnth Hin Dv Hat Hv;
apply (hk_slot_of_state s1v Ex ssx ms (w_H W) idx lo hi lo hi cs off e v HS Hnth Hin);
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (sv_denot_agree 57 E Ex e HAE1 Hat); exact Dv | exact Hv]) end.
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (SLOT 2%nat 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | reflexivity | clear - Hi HN; lia]).
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (SLOT 1%nat 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | reflexivity | clear - Hha; lia]).
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
assert (HCm' : rz_common lyc Sc W (ms_regs ms) (ms_mem ms) mdx k C i ha 9 (((rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) ++ optb u1 (ac_Tn C)) ++ optb f1 (4 * ac_Tn C))) end.
{ apply (rz_common_run lyc Sc W regs mem md k C i ha 9 (((rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) ++ optb u1 (ac_Tn C)) ++ optb f1 (4 * ac_Tn C)) _ _ _ HCm); [intros y Hy; rewrite <- !app_assoc; exact (rz_old_in C p1 x1 _ y Hy) | exact HJ | | exact KM1 | split; [exact SP72' | exact SP56']].
intros r Hr. apply HKR. rewrite app_assoc. apply in_or_app. left. exact Hr. }
split; [exact HCm'|]. split; [unfold rz_res in *; rewrite (HKR 23%bv ltac:(cbv; clear; tauto)), (HKR 24%bv ltac:(cbv; clear; tauto)), (HKR 27%bv ltac:(cbv; clear; tauto)); exact Hres|]. split; [exact Hok3|]. split; [exact Hok4|]. split; [exact Hok5|].
split; [apply (SLOT 4%nat 160 184 [ck 168 (SOff 54 0); ck 160 (SOff 22 0); ck 176 (SOff 55 0)] 176 (SOff 55 0) h1 eq_refl ltac:(right; right; left; reflexivity)); [rewrite (denot_off E 55 h1 0 E55 Rh1), Z.add_0_r; reflexivity | reflexivity | exact Rh1]|].
split; [apply (SLOT 6%nat 296 304 [ck 296 (SOff 56 0)] 296 (SOff 56 0) u1 eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 56 u1 0 E56 Ru1), Z.add_0_r; reflexivity | reflexivity | exact Ru1]|].
split; [apply (SLOT 4%nat 160 184 [ck 168 (SOff 54 0); ck 160 (SOff 22 0); ck 176 (SOff 55 0)] 168 (SOff 54 0) f1 eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 54 f1 0 E54 Rf1), Z.add_0_r; reflexivity | reflexivity | exact Rf1]|].
right; right; right; left; exact Hz3.
Qed.
Lemma hl_ma3r_f5 : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1,
at_MA3R lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 -> (p1 <> 0 /\ x1 <> 0 /\ h1 <> 0 /\ u1 <> 0 /\ f1 = 0) ->
SRr trasegs W (cfgat regs HL_MA3R mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 HL_FAIL mem2 md2 /\ at_FAIL lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 (HCm & Hres & Hok3 & Hok4 & Hok5 & S176 & S160 & S296 & G10) (Hnz0 & Hnz1 & Hnz2 & Hnz3 & Hz4).
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HCm as (HC & Hold & HF & Hk & [SP72 SP56] & G20 & G21 & G22 & G26).
pose proof HF as (Hinv & HTc & HTlt & Hi & Hha & Hz).
pose proof HC as (HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Himg & HPerm & Hperm & Hkept).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (rk_frame_facts _ _ _ _ _ _ _ _ _ HC) as (Fceil & F47 & F32 & Fpres).
destruct (rk_img_facts _ _ _ _ _ _ _ _ _ HC) as (Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
destruct (ts_next_facts _ HTc HTlt) as (Tn1 & Tn2 & Tn3 & Tn4 & Tn5). fold (ac_Tn C) in Tn1, Tn2, Tn3, Tn4.
set (Tn := ac_Tn C) in *.
pose proof Hobj as OBJ. cbn [obj_at LAY_Cht ac_cells] in OBJ. unfold field_ok in OBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in OBJ.
destruct OBJ as ([_ Bf] & [_ Bh] & [_ Bu] & [_ Bp] & [_ Bx] & [_ Bc] & [_ BT] & _). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Bf, Bh, Bu, Bp, Bx.
pose proof HOP as (O24 & O27 & O26 & O23 & O18 & O22 & O17 & O16 & Os0 & Ora).
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) (ac_T C)).
set (xv := [i; ha; f1; h1; u1]).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E37 : ew E 37 = Z_to_bv 64 (ac_x C)) by exact (HV 5%nat _ eq_refl).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (E20 : ew E 20 = Z_to_bv 64 (3 * Tn)) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (E22 : ew E 22 = Z_to_bv 64 Tn) by (rewrite (HE 22%nat 22%bv eq_refl); exact G22).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
assert (D4T : sv_denot E (SAlu ALU_SLL (SOff 22 0) (SLit 2)) = Z_to_bv 64 (4 * Tn)).
{ rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 22 Tn E22) by (clear - Tn2; lia). rewrite (U_lit E 2) by lia.
change (Z.land 2 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite zcanon_id by (unfold M64; clear - Tn2; lia). lia. }
assert (Rf1 : 0 <= f1 < 2 ^ 64) by (destruct Hok5 as [-> | X]; [clear; lia | clear - X; lia]).
assert (Rh1 : 0 <= h1 < 2 ^ 64) by (destruct Hok3 as [-> | X]; [clear; lia | clear - X; lia]).
assert (Ru1 : 0 <= u1 < 2 ^ 64) by (destruct Hok4 as [-> | X]; [clear; lia | clear - X; lia]).
pose proof Hres as (Hok1 & Hok2 & G23 & G24 & G27).
assert (Rp1 : 0 <= p1 < 2 ^ 64) by (destruct Hok1 as [-> | X]; [clear; lia | clear - X; lia]).
assert (Rx1 : 0 <= x1 < 2 ^ 64) by (destruct Hok2 as [-> | X]; [clear; lia | clear - X; lia]).
assert (E54 : ew E 54 = Z_to_bv 64 f1) by exact (HV 22%nat _ eq_refl).
assert (E55 : ew E 55 = Z_to_bv 64 h1) by exact (HV 23%nat _ eq_refl).
assert (E56 : ew E 56 = Z_to_bv 64 u1) by exact (HV 24%nat _ eq_refl).
assert (E23 : ew E 23 = Z_to_bv 64 p1) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (E27 : ew E 27 = Z_to_bv 64 x1) by (rewrite (HE 27%nat 27%bv eq_refl); exact G27).
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_MA3R false [(10%bv, SOff 54 0)] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [ck 160 (SOff 22 0); ck 176 (SOff 55 0)] [ck 296 (SOff 56 0)] [] [] [mkAC BC_NE (SOff 23 0) (SLit 0); mkAC BC_NE (SOff 27 0) (SLit 0); mkAC BC_NE (SOff 55 0) (SLit 0); mkAC BC_NE (SOff 56 0) (SLit 0); mkAC BC_EQ (SOff 54 0) (SLit 0)] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) (ac_T C) xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_cons; [|apply Forall_nil]. split; [reflexivity|]. cbn [fst snd]. rewrite G10. symmetry. rewrite (denot_off E 54 f1 0 E54 Rf1), Z.add_0_r. reflexivity. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold ck.
- apply (chunk_ok_val trasegs E _ s1v 160 8 _ Tn); [rewrite (denot_off E 22 Tn 0 E22 ltac:(clear - Tn2; lia)), Z.add_0_r; reflexivity | clear - Tn2; lia | lia | exact S160].
- apply (chunk_ok_val trasegs E _ s1v 176 8 _ h1); [rewrite (denot_off E 55 h1 0 E55 Rh1), Z.add_0_r; reflexivity | exact Rh1 | lia | exact S176]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 296 8 _ u1); [rewrite (denot_off E 56 u1 0 E56 Ru1), Z.add_0_r; reflexivity | exact Ru1 | lia | exact S296]. }
{ apply Forall_nil. }
{ intros e []. }
{ exact I. }
{ exact I. }
{ cbn [conds_ok]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_ne_U, (U_atom E 23 p1 E23 Rp1), (U_lit E 0) by lia; apply Bool.negb_true_iff, Z.eqb_neq; exact Hnz0|]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_ne_U, (U_atom E 27 x1 E27 Rx1), (U_lit E 0) by lia; apply Bool.negb_true_iff, Z.eqb_neq; exact Hnz1|]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_ne_U, (U_atom E 55 h1 E55 Rh1), (U_lit E 0) by lia; apply Bool.negb_true_iff, Z.eqb_neq; exact Hnz2|]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_ne_U, (U_atom E 56 u1 E56 Ru1), (U_lit E 0) by lia; apply Bool.negb_true_iff, Z.eqb_neq; exact Hnz3|]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_eq_U, (U_atom E 54 f1 E54 Rf1), (U_lit E 0) by lia; apply Z.eqb_eq; exact Hz4|]. exact I. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 57 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan HL_FAIL.
{ apply (hk_awr_ok s1v tb fmt E false _ _ _ _ [] STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 57 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false _ _ _ _ [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 57 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [20; 21; 22; 26]%bv ++ [23; 24; 27]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 57 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 57 E Ex e HAE1 Hat); exact Dv);
assert (SLOT : forall idx lo hi cs off e v, nth_error (ss_mem ssx) idx = Some (YQ0b.mkRegion (Some 9%nat) lo hi lo hi cs) -> In (ck off e) cs ->
sv_denot E e = Z_to_bv 64 v -> sv_atoms_lt 57 e = true -> 0 <= v < 2 ^ 64 -> val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + off) 8 v)
by (intros idx lo hi cs off e v Hnth Hin Dv Hat Hv;
apply (hk_slot_of_state s1v Ex ssx ms (w_H W) idx lo hi lo hi cs off e v HS Hnth Hin);
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (sv_denot_agree 57 E Ex e HAE1 Hat); exact Dv | exact Hv]) end.
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (SLOT 2%nat 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | reflexivity | clear - Hi HN; lia]).
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (SLOT 1%nat 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | reflexivity | clear - Hha; lia]).
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
assert (HCm' : rz_common lyc Sc W (ms_regs ms) (ms_mem ms) mdx k C i ha 9 (((rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) ++ optb u1 (ac_Tn C)) ++ optb f1 (4 * ac_Tn C))) end.
{ apply (rz_common_run lyc Sc W regs mem md k C i ha 9 (((rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) ++ optb u1 (ac_Tn C)) ++ optb f1 (4 * ac_Tn C)) _ _ _ HCm); [intros y Hy; rewrite <- !app_assoc; exact (rz_old_in C p1 x1 _ y Hy) | exact HJ | | exact KM1 | split; [exact SP72' | exact SP56']].
intros r Hr. apply HKR. rewrite app_assoc. apply in_or_app. left. exact Hr. }
split; [exact HCm'|]. split; [unfold rz_res in *; rewrite (HKR 23%bv ltac:(cbv; clear; tauto)), (HKR 24%bv ltac:(cbv; clear; tauto)), (HKR 27%bv ltac:(cbv; clear; tauto)); exact Hres|]. split; [exact Hok3|]. split; [exact Hok4|]. split; [exact Hok5|].
split; [apply (SLOT 4%nat 160 184 [ck 168 (SOff 54 0); ck 160 (SOff 22 0); ck 176 (SOff 55 0)] 176 (SOff 55 0) h1 eq_refl ltac:(right; right; left; reflexivity)); [rewrite (denot_off E 55 h1 0 E55 Rh1), Z.add_0_r; reflexivity | reflexivity | exact Rh1]|].
split; [apply (SLOT 6%nat 296 304 [ck 296 (SOff 56 0)] 296 (SOff 56 0) u1 eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 56 u1 0 E56 Ru1), Z.add_0_r; reflexivity | reflexivity | exact Ru1]|].
split; [apply (SLOT 4%nat 160 184 [ck 168 (SOff 54 0); ck 160 (SOff 22 0); ck 176 (SOff 55 0)] 168 (SOff 54 0) f1 eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 54 f1 0 E54 Rf1), Z.add_0_r; reflexivity | reflexivity | exact Rf1]|].
right; right; right; right; exact Hz4.
Qed.
Lemma hl_ma3r_ok : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1,
at_MA3R lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 -> (p1 <> 0 /\ x1 <> 0 /\ h1 <> 0 /\ u1 <> 0 /\ f1 <> 0) ->
SRr trasegs W (cfgat regs HL_MA3R mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 A_asan_memset mem2 md2 /\ at_MSC lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 (HCm & Hres & Hok3 & Hok4 & Hok5 & S176 & S160 & S296 & G10) (Hnz0 & Hnz1 & Hnz2 & Hnz3 & Hnz4).
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HCm as (HC & Hold & HF & Hk & [SP72 SP56] & G20 & G21 & G22 & G26).
pose proof HF as (Hinv & HTc & HTlt & Hi & Hha & Hz).
pose proof HC as (HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Himg & HPerm & Hperm & Hkept).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (rk_frame_facts _ _ _ _ _ _ _ _ _ HC) as (Fceil & F47 & F32 & Fpres).
destruct (rk_img_facts _ _ _ _ _ _ _ _ _ HC) as (Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
destruct (ts_next_facts _ HTc HTlt) as (Tn1 & Tn2 & Tn3 & Tn4 & Tn5). fold (ac_Tn C) in Tn1, Tn2, Tn3, Tn4.
set (Tn := ac_Tn C) in *.
pose proof Hobj as OBJ. cbn [obj_at LAY_Cht ac_cells] in OBJ. unfold field_ok in OBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in OBJ.
destruct OBJ as ([_ Bf] & [_ Bh] & [_ Bu] & [_ Bp] & [_ Bx] & [_ Bc] & [_ BT] & _). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Bf, Bh, Bu, Bp, Bx.
pose proof HOP as (O24 & O27 & O26 & O23 & O18 & O22 & O17 & O16 & Os0 & Ora).
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) (ac_T C)).
set (xv := [i; ha; f1; h1; u1]).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E37 : ew E 37 = Z_to_bv 64 (ac_x C)) by exact (HV 5%nat _ eq_refl).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (E20 : ew E 20 = Z_to_bv 64 (3 * Tn)) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (E22 : ew E 22 = Z_to_bv 64 Tn) by (rewrite (HE 22%nat 22%bv eq_refl); exact G22).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
assert (D4T : sv_denot E (SAlu ALU_SLL (SOff 22 0) (SLit 2)) = Z_to_bv 64 (4 * Tn)).
{ rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 22 Tn E22) by (clear - Tn2; lia). rewrite (U_lit E 2) by lia.
change (Z.land 2 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite zcanon_id by (unfold M64; clear - Tn2; lia). lia. }
assert (Rf1 : 0 <= f1 < 2 ^ 64) by (destruct Hok5 as [-> | X]; [clear; lia | clear - X; lia]).
assert (Rh1 : 0 <= h1 < 2 ^ 64) by (destruct Hok3 as [-> | X]; [clear; lia | clear - X; lia]).
assert (Ru1 : 0 <= u1 < 2 ^ 64) by (destruct Hok4 as [-> | X]; [clear; lia | clear - X; lia]).
pose proof Hres as (Hok1 & Hok2 & G23 & G24 & G27).
assert (Rp1 : 0 <= p1 < 2 ^ 64) by (destruct Hok1 as [-> | X]; [clear; lia | clear - X; lia]).
assert (Rx1 : 0 <= x1 < 2 ^ 64) by (destruct Hok2 as [-> | X]; [clear; lia | clear - X; lia]).
assert (E54 : ew E 54 = Z_to_bv 64 f1) by exact (HV 22%nat _ eq_refl).
assert (E55 : ew E 55 = Z_to_bv 64 h1) by exact (HV 23%nat _ eq_refl).
assert (E56 : ew E 56 = Z_to_bv 64 u1) by exact (HV 24%nat _ eq_refl).
assert (E23 : ew E 23 = Z_to_bv 64 p1) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (E27 : ew E 27 = Z_to_bv 64 x1) by (rewrite (HE 27%nat 27%bv eq_refl); exact G27).
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_MA3R true [(10%bv, SOff 54 0); (21%bv, SOff 32 24)] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [ck 160 (SOff 22 0); ck 176 (SOff 55 0)] [ck 296 (SOff 56 0)] [] [] [mkAC BC_NE (SOff 23 0) (SLit 0); mkAC BC_NE (SOff 27 0) (SLit 0); mkAC BC_NE (SOff 55 0) (SLit 0); mkAC BC_NE (SOff 56 0) (SLit 0); mkAC BC_NE (SOff 54 0) (SLit 0)] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) (ac_T C) xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; (split; [reflexivity|]); cbn [fst snd].
- rewrite G10. symmetry. rewrite (denot_off E 54 f1 0 E54 Rf1), Z.add_0_r. reflexivity.
- rewrite G21. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold ck.
- apply (chunk_ok_val trasegs E _ s1v 160 8 _ Tn); [rewrite (denot_off E 22 Tn 0 E22 ltac:(clear - Tn2; lia)), Z.add_0_r; reflexivity | clear - Tn2; lia | lia | exact S160].
- apply (chunk_ok_val trasegs E _ s1v 176 8 _ h1); [rewrite (denot_off E 55 h1 0 E55 Rh1), Z.add_0_r; reflexivity | exact Rh1 | lia | exact S176]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 296 8 _ u1); [rewrite (denot_off E 56 u1 0 E56 Ru1), Z.add_0_r; reflexivity | exact Ru1 | lia | exact S296]. }
{ apply Forall_nil. }
{ intros e []. }
{ exact I. }
{ exact I. }
{ cbn [conds_ok]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_ne_U, (U_atom E 23 p1 E23 Rp1), (U_lit E 0) by lia; apply Bool.negb_true_iff, Z.eqb_neq; exact Hnz0|]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_ne_U, (U_atom E 27 x1 E27 Rx1), (U_lit E 0) by lia; apply Bool.negb_true_iff, Z.eqb_neq; exact Hnz1|]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_ne_U, (U_atom E 55 h1 E55 Rh1), (U_lit E 0) by lia; apply Bool.negb_true_iff, Z.eqb_neq; exact Hnz2|]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_ne_U, (U_atom E 56 u1 E56 Ru1), (U_lit E 0) by lia; apply Bool.negb_true_iff, Z.eqb_neq; exact Hnz3|]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_ne_U, (U_atom E 54 f1 E54 Rf1), (U_lit E 0) by lia; apply Bool.negb_true_iff, Z.eqb_neq; exact Hnz4|]. exact I. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 57 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan A_asan_memset.
{ apply (hk_awr_ok s1v tb fmt E true _ _ _ _ [] STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros _ a Ha; destruct (Hperm tb CHT_SIZE ltac:(left; reflexivity)) as [_ Hw]; replace a with (tb + (a - tb)) by lia; apply Hw; [exact Htbin | change (req_size CHT_SIZE) with 48; clear - Ha; lia] | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 57 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> ~ (tb <= a < tb + 48) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn Hnt. apply (hk_frame_kept s1v tb fmt _ true _ _ _ _ [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros _; exact Hnt | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 57 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [22; 23; 24; 27]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 57 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 57 E Ex e HAE1 Hat); exact Dv);
assert (SLOT : forall idx lo hi cs off e v, nth_error (ss_mem ssx) idx = Some (YQ0b.mkRegion (Some 9%nat) lo hi lo hi cs) -> In (ck off e) cs ->
sv_denot E e = Z_to_bv 64 v -> sv_atoms_lt 57 e = true -> 0 <= v < 2 ^ 64 -> val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + off) 8 v)
by (intros idx lo hi cs off e v Hnth Hin Dv Hat Hv;
apply (hk_slot_of_state s1v Ex ssx ms (w_H W) idx lo hi lo hi cs off e v HS Hnth Hin);
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (sv_denot_agree 57 E Ex e HAE1 Hat); exact Dv | exact Hv]) end.
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (SLOT 2%nat 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | reflexivity | clear - Hi HN; lia]).
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (SLOT 1%nat 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | reflexivity | clear - Hha; lia]).
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
set (cnt := ht_cnt (ac_H C)) in *.
assert (E33 : ew E 33 = Z_to_bv 64 (ac_f C)) by exact (HV 1%nat _ eq_refl).
assert (E34 : ew E 34 = Z_to_bv 64 (ac_h C)) by exact (HV 2%nat _ eq_refl).
assert (E35 : ew E 35 = Z_to_bv 64 (ac_u C)) by exact (HV 3%nat _ eq_refl).
assert (E38 : ew E 38 = Z_to_bv 64 cnt) by exact (HV 6%nat _ eq_refl).
assert (E39 : ew E 39 = Z_to_bv 64 (ac_T C)) by exact (HV 7%nat _ eq_refl).
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Bc, BT.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
destruct (st_ok_mem_ok trasegs Ex ssx _ HS) as (_ & Hrs & _);
pose proof (proj1 (Forall_forall _ _) Hrs _ (nth_error_In (ss_mem ssx) 8%nat eq_refl)) as HRtb; cbn [ms_mem restrict] in HRtb;
assert (DA : forall n z, (n < 57)%nat -> ew E n = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> sv_denot Ex (SOff n 0) = Z_to_bv 64 z)
by (intros n z Hn En Hz0; rewrite (denot_off Ex n z 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact En | exact Hz0]);
assert (UX32 : bv_unsigned (ew Ex 32) = tb) by (rewrite (proj1 HAE1) by lia; exact U32);
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 0 8%N (SOff 33 0) (ac_f C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 33%nat _ ltac:(lia) E33 Bf) Bf ltac:(lia)) as Vf';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 8 8%N (SOff 34 0) (ac_h C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 34%nat _ ltac:(lia) E34 Bh) Bh ltac:(lia)) as Vh';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 16 8%N (SOff 35 0) (ac_u C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 35%nat _ ltac:(lia) E35 Bu) Bu ltac:(lia)) as Vu';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 24 8%N (SOff 23 0) p1 HRtb UX32 ltac:(cbn; clear; tauto) (DA 23%nat _ ltac:(lia) E23 Rp1) Rp1 ltac:(lia)) as Vp';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 32 8%N (SOff 27 0) x1 HRtb UX32 ltac:(cbn; clear; tauto) (DA 27%nat _ ltac:(lia) E27 Rx1) Rx1 ltac:(lia)) as Vx';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 40 4%N (SOff 38 0) cnt HRtb UX32 ltac:(cbn; clear; tauto) (DA 38%nat _ ltac:(lia) E38 ltac:(clear - Bc; lia)) ltac:(clear - Bc; cbn; lia) ltac:(lia)) as Vc';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 44 4%N (SOff 39 0) (ac_T C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 39%nat _ ltac:(lia) E39 ltac:(clear - BT; lia)) ltac:(clear - BT; cbn; lia) ltac:(lia)) as VT' end.
rewrite !Z.add_0_r in Vf'.
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
assert (HC' : rcore lyc Sc W (ms_regs ms) (ms_mem ms) mdx k (rh_cells C p1 x1 cnt) (((rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) ++ optb u1 (ac_Tn C)) ++ optb f1 (4 * ac_Tn C))) end.
{ eapply rcore_run with (regs := regs) (mem := mem) (md := md) (cells := ac_cells C); try eassumption.
- intros r Hr. apply HKR. apply in_or_app. left. exact Hr.
- intros a Ha H1 _ Hnb. apply KM1; [exact Ha | exact H1|]. intros Hx. apply Hnb. exists tb, CHT_SIZE. split; [left; reflexivity | change (req_size CHT_SIZE) with 48; exact Hx].
- cbn [obj_at LAY_Cht rh_cells]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite Z.add_0_r.
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32).
split; [split; [exact Vf' | exact Bf]|]. split; [split; [exact Vh' | exact Bh]|]. split; [split; [exact Vu' | exact Bu]|].
split; [split; [exact Vp' | exact Rp1]|]. split; [split; [exact Vx' | exact Rx1]|]. split; [split; [exact Vc' | exact Bc]|].
split; [split; [exact VT' | exact BT]|]. exact I. }
assert (EBL : (((rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) ++ optb u1 (ac_Tn C)) ++ optb f1 (4 * ac_Tn C)) = rh_BL C p1 x1 h1 u1 f1).
{ unfold rz_BL, rbk, optb, rh_BL. rewrite (proj2 (Z.eqb_neq p1 0) Hnz0), (proj2 (Z.eqb_neq x1 0) Hnz1), (proj2 (Z.eqb_neq h1 0) Hnz2), (proj2 (Z.eqb_neq u1 0) Hnz3), (proj2 (Z.eqb_neq f1 0) Hnz4). reflexivity. }
rewrite EBL in HC'.
assert (Hold' : rz_old W (ms_mem ms) C).
{ apply (rz_old_run lyc Sc W regs mem md k (ac_cells C) (((rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) ++ optb u1 (ac_Tn C)) ++ optb f1 (4 * ac_Tn C)) C (ms_mem ms) HC Hold Hinv HTc); [intros y Hy; rewrite <- !app_assoc; exact (rz_old_in C p1 x1 _ y Hy) | exact KM1]. }
split.
{ split; [exact HC'|]. split; [exact Hold'|]. split; [exact HF|]. split; [exact Hk|]. split; [split; [exact SP72' | exact SP56']|].
split.
{ split; [apply (SLOT 4%nat 160 184 [ck 168 (SOff 54 0); ck 160 (SOff 22 0); ck 176 (SOff 55 0)] 160 (SOff 22 0) Tn eq_refl ltac:(right; left; reflexivity)); [rewrite (denot_off E 22 Tn 0 E22 ltac:(clear - Tn2; lia)), Z.add_0_r; reflexivity | reflexivity | clear - Tn2; lia]|].
split; [apply (SLOT 4%nat 160 184 [ck 168 (SOff 54 0); ck 160 (SOff 22 0); ck 176 (SOff 55 0)] 168 (SOff 54 0) f1 eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 54 f1 0 E54 Rf1), Z.add_0_r; reflexivity | reflexivity | exact Rf1]|].
split; [apply (SLOT 4%nat 160 184 [ck 168 (SOff 54 0); ck 160 (SOff 22 0); ck 176 (SOff 55 0)] 176 (SOff 55 0) h1 eq_refl ltac:(right; right; left; reflexivity)); [rewrite (denot_off E 55 h1 0 E55 Rh1), Z.add_0_r; reflexivity | reflexivity | exact Rh1]|].
apply (SLOT 6%nat 296 304 [ck 296 (SOff 56 0)] 296 (SOff 56 0) u1 eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 56 u1 0 E56 Ru1), Z.add_0_r; reflexivity | reflexivity | exact Ru1]. }
unfold rh_ptr.
split; [destruct Hok1 as [X | X]; [contradiction | exact X]|]. split; [destruct Hok2 as [X | X]; [contradiction | exact X]|].
split; [destruct Hok3 as [X | X]; [contradiction | exact X]|]. split; [destruct Hok4 as [X | X]; [contradiction | exact X]|].
destruct Hok5 as [X | X]; [contradiction | exact X]. }
split; [apply (RD 10%bv (SOff 56 0) u1 eq_refl); [rewrite (denot_off E 56 u1 0 E56 Ru1), Z.add_0_r; reflexivity | reflexivity]|].
split; [exact (RD 11%bv (SLit 0) 0 eq_refl eq_refl eq_refl)|].
split; [apply (RD 12%bv (SOff 22 0) Tn eq_refl); [rewrite (denot_off E 22 Tn 0 E22 ltac:(clear - Tn2; lia)), Z.add_0_r; reflexivity | reflexivity]|].
split; [exact (RD 1%bv (SLit HL_MSR) HL_MSR eq_refl eq_refl eq_refl)|].
split; [apply (RD 20%bv (SOff 32 0) tb eq_refl); [rewrite (denot_off E 32 tb 0 E32 ltac:(clear - Htb4096 Htbceil C1; lia)), Z.add_0_r; reflexivity | reflexivity]|].
apply (RD 21%bv (SOff 32 40) (tb + 40) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity].
Qed.
Lemma hl_ma3r : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1,
at_MA3R lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 ->
SRr trasegs W (cfgat regs HL_MA3R mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
(c2 = cfgat regs2 A_asan_memset mem2 md2 /\ at_MSC lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1) \/
(c2 = cfgat regs2 HL_FAIL mem2 md2 /\ at_FAIL lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1)).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 HAT.
assert (FAILK : forall (Q : world trasegs -> config -> Prop),
SRr trasegs W (cfgat regs HL_MA3R mem md) (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 HL_FAIL mem2 md2 /\ at_FAIL lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1) ->
SRr trasegs W (cfgat regs HL_MA3R mem md) (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
(c2 = cfgat regs2 A_asan_memset mem2 md2 /\ at_MSC lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1) \/
(c2 = cfgat regs2 HL_FAIL mem2 md2 /\ at_FAIL lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1))).
{ intros _ H. eapply SRr_mono; [exact H|]. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HF). split; [reflexivity|]. exists regs2, mem2, md2. right. split; [reflexivity | exact HF]. }
destruct (Z.eq_dec p1 0) as [Z0 | N0]; [apply (FAILK (fun _ _ => True)); exact (hl_ma3r_f1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAT Z0)|].
destruct (Z.eq_dec x1 0) as [Z1 | N1]; [apply (FAILK (fun _ _ => True)); exact (hl_ma3r_f2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAT (conj N0 Z1))|].
destruct (Z.eq_dec h1 0) as [Z2 | N2]; [apply (FAILK (fun _ _ => True)); exact (hl_ma3r_f3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAT (conj N0 (conj N1 Z2)))|].
destruct (Z.eq_dec u1 0) as [Z3 | N3]; [apply (FAILK (fun _ _ => True)); exact (hl_ma3r_f4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAT (conj N0 (conj N1 (conj N2 Z3))))|].
destruct (Z.eq_dec f1 0) as [Z4 | N4]; [apply (FAILK (fun _ _ => True)); exact (hl_ma3r_f5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAT (conj N0 (conj N1 (conj N2 (conj N3 Z4)))))|].
eapply SRr_mono; [exact (hl_ma3r_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAT (conj N0 (conj N1 (conj N2 (conj N3 N4)))))|].
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HM). split; [reflexivity|]. exists regs2, mem2, md2. left. split; [reflexivity | exact HM].
Qed.
End c.
