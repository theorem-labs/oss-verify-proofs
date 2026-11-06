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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC2u YC1b YC4u YC4z
YC53.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YP14 YI08 YI0c YI0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC6w YC6v YC6t YC6u YC77.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0n YC6f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition rbk (old : Z * Z) (res n : Z) : Z * Z := if res =? 0 then old else (res, n).
Fixpoint ldel {A : Type} (l : list A) (q : nat) : list A :=
match l, q with [], _ => [] | _ :: r, O => r | x :: r, Datatypes.S q' => x :: ldel r q' end.
Lemma ldel_split : forall {A} (l : list A) q x, nth_error l q = Some x -> exists l1 l2, l = l1 ++ x :: l2 /\ ldel l q = l1 ++ l2 /\ length l1 = q.
Proof.
intros A l. induction l as [|a l IH]; intros [|q] x Hq; cbn in Hq; try discriminate.
- injection Hq as ->. exists [], l. repeat split.
- destruct (IH q x Hq) as (l1 & l2 & -> & E2 & E3). exists (a :: l1), l2. cbn. rewrite E2, E3. repeat split.
Qed.
Lemma lset_split : forall {A} (l : list A) q x y, nth_error l q = Some x -> exists l1 l2, l = l1 ++ x :: l2 /\ lset l q y = l1 ++ y :: l2 /\ length l1 = q.
Proof.
intros A l. induction l as [|a l IH]; intros [|q] x y Hq; cbn in Hq; try discriminate.
- injection Hq as ->. exists [], l. repeat split.
- destruct (IH q x y Hq) as (l1 & l2 & -> & E2 & E3). exists (a :: l1), l2. cbn. rewrite E2, E3. repeat split.
Qed.
Section d.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes trasegs B.
Hypothesis AFREE : afree_realizes trasegs B.
Hypothesis AREALLOC : arealloc_realizes trasegs B 0x53108 0x53640.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)).
Variables (s1v tb img fmt N : Z) (imgl : list Z).
Variables (hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 : Z).
Variable PROT : list (Z * Z).
Variables (lyH : alayout) (SH : astate) (WH : world trasegs) (memH : word -> option byte).
Variable ch0 : list (Z * Z * Z).
Hypothesis Hs1 : s1v = sp0 - 512.
Hypothesis HSTK : 512 + ASTACK <= STK.
Hypothesis Hsp32 : sp0 mod 32 = 0.
Hypothesis Htop32 : sp0 + 32 <= ly_top ly.
Hypothesis HCH0 : achain ly (aview trasegs (w_H W0) mem0) sp0 s0v ch0.
Hypothesis Hrav : rav = 0x81368.
Hypothesis Hspine : spine ch0 = [] \/ spine ch0 = [0x80ea8].
Hypothesis Hs0v : 0 <= s0v < 2 ^ 64.
Hypothesis Himgl : zlen imgl = fmt * N.
Hypothesis HimgP : In (img, fmt * N) PROT.
Hypothesis HEV : vev S + 80 <= VEV_MAX.
Hypothesis HLIVE : bsum PROT + 2 ^ 30 <= LIVE_MAX.
Local Notation rcore := (rcore B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation rperm := (rperm B STK sp0 FP ly S tb).
Local Notation rapart := (rapart tb PROT).
Local Notation hk_ch := (hk_ch sp0 rav s0v ch0).
Local Notation cfgat regs pc mem md := (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom trasegs)) md).
Lemma rperm_apart_nth : forall lyX SX WX memX mdX (L : list (Z * Z)) (p q : nat) x y,
AR trasegs B lyX SX WX memX mdX -> Permutation (ablocks B lyX SX) (PROT ++ L) ->
nth_error L p = Some x -> nth_error L q = Some y -> p <> q ->
fst x + req_size (snd x) <= fst y \/ fst y + req_size (snd y) <= fst x.
Proof.
intros lyX SX WX memX mdX L p q x y HAR HPerm Hp Hq Hne.
destruct (nth_error_split _ _ Hp) as (l1 & l2 & El & Hlen).
assert (Hy : In y (l1 ++ l2)).
{ rewrite El in Hq. destruct (Nat.lt_ge_cases q p) as [Hlt | Hge].
- rewrite nth_error_app1 in Hq by lia. apply in_app_iff. left. exact (nth_error_In _ _ Hq).
- rewrite nth_error_app2 in Hq by lia. destruct (q - length l1)%nat as [|m] eqn:Em; [lia|]. cbn in Hq.
apply in_app_iff. right. exact (nth_error_In _ _ Hq). }
rewrite El in HPerm.
pose proof (rg_sep_head_in B LAWS lyX SX WX memX mdX x (PROT ++ l1 ++ l2) y HAR) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. apply Hd.
- eapply Permutation_trans; [exact HPerm|]. rewrite app_assoc. apply Permutation_sym. rewrite app_assoc. apply Permutation_middle.
- apply in_app_iff. right. exact Hy.
Qed.
Lemma rcore_call_facts : forall lyc Sc W regs mem md k cells BL, rcore lyc Sc W regs mem md k cells BL ->
spZ regs = sp0 + -512 /\ vev Sc <= vev S + k /\ blocks_bytes Sc = bsum PROT + 48 + bsum BL /\
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 496) 8 s0v /\ val_mem trasegs (mrestrict (w_H W) mem) (s1v + 504) 8 rav.
Proof.
intros lyc Sc W regs mem md k cells BL HC.
pose proof HC as (HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Himg & HPerm & Hperm & Hkept).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & Hnev & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (Has : ASTACK = 16384) by reflexivity.
split; [unfold spZ; rewrite G2, unsigned_lit_small by (rewrite Hs1; clear - Hceil Hslo Hshi H47 C1 HSTK Has; lia); rewrite Hs1; lia|].
split; [exact (proj1 Hnev)  |]. split.
{ rewrite (blocks_bytes_bsum B lyc Sc), (bsum_perm _ _ HPerm), bsum_app, bsum_cons. cbn [snd]. change CHT_SIZE with 48. lia. }
split; [apply (Hsl 496 s0v); unfold hk_tab; cbn; tauto | apply (Hsl 504 rav); unfold hk_tab; cbn; tauto].
Qed.
Lemma rz_realloc : forall lyc Sc W (regs : bvmap 5 word) mem md k cells BL (q : nat) pa n_old n ret,
rcore lyc Sc W regs mem md k cells BL -> nth_error BL q = Some (pa, n_old) ->
getr regs 10 = Z_to_bv 64 pa -> getr regs 11 = Z_to_bv 64 n -> 64513 <= n < MALLOC_MAX -> n <> n_old ->
bsum BL + n + 48 <= 2 ^ 30 -> k + 3 <= 80 ->
getr regs 1 = Z_to_bv 64 ret -> 4096 <= ret < 2 ^ 63 -> ret mod 2 = 0 -> ret mod 4 = 0 ->
In (call_trace0 0x53640 regs hk_ch) (as_universe B) ->
SRr trasegs W (cfgat regs 0x53108 mem md)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = cfgat regs2 ret mem2 md2 /\
rcore ly2 S2 W2 regs2 mem2 md2 (k + 3) cells (lset BL q (rbk (pa, n_old) res n)) /\
aregs_preserved regs regs2 /\ getr regs2 10 = Z_to_bv 64 res /\ (res = 0 \/ 4096 <= res) /\
(forall a, s1v <= a < s1v + 512 -> aview trasegs (w_H W2) mem2 a = aview trasegs (w_H W) mem a) /\
(forall (p' : nat) y, nth_error BL p' = Some y -> p' <> q -> rg_blk_kept (w_H W) (w_H W2) mem mem2 (fst y) (req_size (snd y))) /\
(res = 0 -> rg_blk_kept (w_H W) (w_H W2) mem mem2 pa (req_size n_old)) /\
(res <> 0 -> forall i, 0 <= i < Z.min n_old n -> aview trasegs (w_H W2) mem2 (res + i) = aview trasegs (w_H W) mem (pa + i)) /\
bud_le Sc S2 3 1 (wcost n) (hcost n)).
Proof.
intros lyc Sc W regs mem md k cells BL q pa n_old n ret HC Hq G10 G11 Hn Hne Hlive Hk3 Gra Hret Hret2 Hret4 Htr.
pose proof tra_segs_low as Hsegs.
assert (HAR : AR trasegs B lyc Sc W mem md) by exact (proj1 (proj1 HC)).
assert (Hc47 : alloc_ceiling + ASTACK <= s1v /\ s1v + 512 <= 2 ^ 47) by (eapply rcore_ceil; eassumption). destruct Hc47 as [Hceil H47].
destruct (rcore_call_facts _ _ _ _ _ _ _ _ _ HC) as (Usp & Hnev & Hbb & V496 & V504).
pose proof HC as (HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Himg & HPerm & Hperm & Hkept).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (Has : ASTACK = 16384) by reflexivity.
assert (Hin : In (pa, n_old) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. right. exact (nth_error_In _ _ Hq). }
assert (Hraw : YK0s.ret_ok (Z_to_bv 64 ret)).
{ apply YK0s.ret_ok_even. rewrite unsigned_lit_small by (clear - Hret; lia). exact Hret2. }
destruct (Hperm pa n_old ltac:(right; exact (nth_error_In _ _ Hq))) as [Htok _].
eapply SRr_mono.
{ eapply (aj_realloc_atD trasegs B LAWS Hsegs errno_low ML 0x53108 0x53640 AREALLOC
ltac:(apply (tl_universe B TL); apply memZL_In; vm_compute; reflexivity)
W regs mem STK sp0 FP ly S W0 mem0 md0 own lyc Sc md k pa n_old n (-512) (Z_to_bv 64 ret) hk_ch HJ Hin G10 G11 Hn).
- rewrite Hbb. unfold LIVE_MAX in *. clear - Hlive HLIVE. lia.
- exact Usp.
- reflexivity.
- clear; lia.
- clear - HSTK; lia.
- exact G3.
- exact G4.
- exact Gra.
- exact Hraw.
- clear - Hnev Hk3 HEV. lia.
- apply (hk_chain B STK sp0 FP ly S W0 mem0 md0 own s1v Hs1 HSTK Hsp32 Htop32 rav s0v ch0 HCH0 Hrav Hs0v lyc Sc W regs mem md k HJ V496 V504 G2 G8).
unfold raZ. rewrite Gra, unsigned_lit_small by (clear - Hret; lia). clear - Hret. lia.
- exact Htr.
- exact Htok. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Ha0 & Hfr2 & Hd2 & Hres).
exists ly2, S2, regs2, mem2, md2, res. split; [reflexivity|].
replace (sp0 + -512 - ASTACK) with (s1v - ASTACK) in Hres by (rewrite Hs1; lia). replace (sp0 + -512) with s1v in Hres by (rewrite Hs1; lia).
destruct (lset_split BL q (pa, n_old) (rbk (pa, n_old) res n) Hq) as (b1 & b2 & EBL & Eset & Hlen1).
destruct Hres as [(-> & Ebl & HK) | (Hres4096 & (l1 & l2 & El & El2) & HK & Hcopy)].
-
assert (Erb : rbk (pa, n_old) 0 n = (pa, n_old)) by reflexivity.
assert (Eset' : lset BL q (rbk (pa, n_old) 0 n) = BL) by (rewrite Eset, Erb; symmetry; exact EBL).
rewrite Eset'.
split.
{ eapply rcore_call with (lyc := lyc) (Sc := Sc) (W := W) (regs := regs) (mem := mem) (md := md) (k := k) (BL := BL) (E := fun _ : Z => False); try eassumption;
[intros a [] | rewrite Ebl; exact HPerm]. }
split; [exact HP2|]. split; [exact Ha0|]. split; [left; reflexivity|].
destruct HK as (A1 & A2 & _).
split; [intros a Ha; apply A1; [clear - Ha Hceil H47 C1 Has; lia | clear - Ha; lia]|].
split.
{ intros p' y Hy _ i Hi. destruct y as [yb yn]. cbn [fst snd] in *. apply (A2 yb yn i); [| exact Hi | intros []].
eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. right. exact (nth_error_In _ _ Hy). }
split; [intros _ i Hi; apply (A2 pa n_old i Hin Hi); intros [] | split; [intros X; contradiction X; reflexivity | exact Hd2]].
-
assert (Hnz : res <> 0) by (clear - Hres4096; lia).
assert (Erb : rbk (pa, n_old) res n = (res, n)) by (unfold rbk; destruct (Z.eqb_spec res 0); [contradiction | reflexivity]).
rewrite Erb in Eset. rewrite Erb.
pose proof (proj1 HJ2) as HAR2.
assert (HPold : Permutation (l1 ++ l2) (PROT ++ (tb, CHT_SIZE) :: b1 ++ b2)).
{ replace (PROT ++ (tb, CHT_SIZE) :: b1 ++ b2) with ((PROT ++ (tb, CHT_SIZE) :: b1) ++ b2) by (rewrite <- app_assoc; reflexivity).
apply (Permutation_app_inv l1 l2 (PROT ++ (tb, CHT_SIZE) :: b1) b2 (pa, n_old)).
rewrite <- El. rewrite <- app_assoc. cbn [app]. rewrite <- EBL. exact HPerm. }
assert (HPerm2 : Permutation (ablocks B ly2 S2) (PROT ++ (tb, CHT_SIZE) :: lset BL q (res, n))).
{ rewrite El2, Eset, app_assoc. eapply Permutation_trans; [apply Permutation_app_tail; exact HPold|].
eapply Permutation_trans; [apply Permutation_sym; apply Permutation_cons_append|].
replace (PROT ++ (tb, CHT_SIZE) :: b1 ++ (res, n) :: b2) with ((PROT ++ (tb, CHT_SIZE) :: b1) ++ (res, n) :: b2) by (rewrite <- app_assoc; reflexivity).
replace (PROT ++ (tb, CHT_SIZE) :: b1 ++ b2) with ((PROT ++ (tb, CHT_SIZE) :: b1) ++ b2) by (rewrite <- app_assoc; reflexivity).
apply Permutation_middle. }
assert (Hfresh : ~ In (res, n) (ablocks B lyc Sc)).
{ intros Hc. rewrite El in Hc. apply in_app_iff in Hc as [Hc | [Hc | Hc]].
- apply in_split in Hc as (c1 & c2 & Ec).
assert (EE : ablocks B ly2 S2 = c1 ++ (res, n) :: (c2 ++ l2) ++ (res, n) :: []) by (rewrite El2, Ec, <- !app_assoc; cbn [app]; reflexivity).
pose proof (sep_blocks_pos trasegs B LAWS ly2 S2 W2 mem2 md2 (res, n) (res, n) c1 (c2 ++ l2) [] HAR2 EE) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. pose proof (req_size_pos n ltac:(clear - Hn; lia)). lia.
- injection Hc as _ Hc. exact (Hne (eq_sym Hc)).
- apply in_split in Hc as (c1 & c2 & Ec).
assert (EE : ablocks B ly2 S2 = (l1 ++ c1) ++ (res, n) :: c2 ++ (res, n) :: []) by (rewrite El2, Ec, <- !app_assoc; cbn [app]; reflexivity).
pose proof (sep_blocks_pos trasegs B LAWS ly2 S2 W2 mem2 md2 (res, n) (res, n) (l1 ++ c1) c2 [] HAR2 EE) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. pose proof (req_size_pos n ltac:(clear - Hn; lia)). lia. }
assert (Hperm2 : rperm (lset BL q (res, n))).
{ intros b m Hb. rewrite Eset in Hb.
assert (Hcase : (b, m) = (res, n) \/ In (b, m) ((tb, CHT_SIZE) :: BL)).
{ destruct Hb as [Hb | Hb]; [right; left; exact Hb|]. apply in_app_iff in Hb as [Hb | [Hb | Hb]];
[right; right; rewrite EBL; apply in_app_iff; left; exact Hb | left; symmetry; exact Hb | right; right; rewrite EBL; apply in_app_iff; right; right; exact Hb]. }
destruct Hcase as [Hc | Hc]; [injection Hc as -> ->|exact (Hperm b m Hc)].
split; [exact (aftok_fresh B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k res n HJ Hfresh)|].
intros blc lyq ownq i Hbl Hi. exact (awr_fresh_any B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k res n blc i lyq ownq HJ Hfresh Hbl Hi). }
assert (Hap_new : forall a, res <= a < res + req_size n -> rapart lyc Sc a).
{ intros a Ha. eapply rapart_frames with (ly2 := ly2) (S2 := S2); [| exact Hfr2 |].
- eapply rblk_apart with (b := res) (n := n) (BLX := lset BL q (res, n)); try eassumption. rewrite Eset. apply in_app_iff. right. left. reflexivity.
- intros c p. transitivity (frame_addr ly c p); [eapply journal_frame_addr; exact HJ2 | symmetry; eapply journal_frame_addr; exact HJ]. }
assert (Hap_old : forall a, pa <= a < pa + req_size n_old -> rapart lyc Sc a).
{ intros a Ha. eapply rblk_apart with (b := pa) (n := n_old) (BLX := BL); try eassumption. exact (nth_error_In _ _ Hq). }
split.
{ eapply rcore_call with (lyc := lyc) (Sc := Sc) (W := W) (regs := regs) (mem := mem) (md := md) (k := k) (BL := BL)
(E := fun a : Z => res <= a < res + req_size n \/ pa <= a < pa + req_size n_old); try eassumption.
intros a [Ha | Ha]; [exact (Hap_new a Ha) | exact (Hap_old a Ha)]. }
split; [exact HP2|]. split; [exact Ha0|]. split; [right; exact Hres4096|].
destruct HK as (A1 & A2 & _).
split; [intros a Ha; apply A1; [clear - Ha Hceil H47 C1 Has; lia | clear - Ha; lia]|].
split.
{ intros p' y Hy Hpq i Hi. destruct y as [yb yn]. cbn [fst snd] in *.
assert (Hyin : In (yb, yn) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. right. exact (nth_error_In _ _ Hy). }
apply (A2 yb yn i Hyin Hi). intros [He | He].
-
assert (Hy2 : nth_error (lset BL q (res, n)) p' = Some (yb, yn)) by (rewrite nth_error_lset_other by exact Hpq; exact Hy).
assert (Hq2 : nth_error (lset BL q (res, n)) q = Some (res, n)) by (apply nth_error_lset_same; apply nth_error_Some; rewrite Hq; discriminate).
pose proof (rperm_apart_nth ly2 S2 W2 mem2 md2 ((tb, CHT_SIZE) :: lset BL q (res, n)) (Datatypes.S p') (Datatypes.S q) (yb, yn) (res, n) HAR2 HPerm2 Hy2 Hq2 ltac:(lia)) as Hd.
cbn [fst snd] in Hd. clear - Hd He Hi. lia.
- pose proof (rperm_apart_nth lyc Sc W mem md ((tb, CHT_SIZE) :: BL) (Datatypes.S p') (Datatypes.S q) (yb, yn) (pa, n_old) HAR HPerm Hy Hq ltac:(lia)) as Hd.
cbn [fst snd] in Hd. clear - Hd He Hi. lia. }
split; [intros X; exfalso; exact (Hnz X) | split; [intros _; exact Hcopy | exact Hd2]].
Qed.
Lemma rz_malloc : forall lyc Sc W (regs : bvmap 5 word) mem md k cells BL n ret,
rcore lyc Sc W regs mem md k cells BL ->
getr regs 10 = Z_to_bv 64 n -> 0 < n < MALLOC_MAX ->
bsum BL + n + 48 <= 2 ^ 30 -> k + 1 <= 80 ->
getr regs 1 = Z_to_bv 64 ret -> 4096 <= ret < 2 ^ 63 -> ret mod 2 = 0 ->
In (call_trace0 (pc_malloc_ra0 (as_code B)) regs hk_ch) (as_universe B) ->
SRr trasegs W (cfgat regs 0x53104 mem md)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = cfgat regs2 ret mem2 md2 /\
rcore ly2 S2 W2 regs2 mem2 md2 (k + 1) cells (BL ++ optb res n) /\
aregs_preserved regs regs2 /\ getr regs2 10 = Z_to_bv 64 res /\ (res = 0 \/ 4096 <= res) /\
(forall a, s1v <= a < s1v + 512 -> aview trasegs (w_H W2) mem2 a = aview trasegs (w_H W) mem a) /\
(forall y, In y BL -> rg_blk_kept (w_H W) (w_H W2) mem mem2 (fst y) (req_size (snd y))) /\
bud_le Sc S2 1 1 (wcost n) (hcost n)).
Proof.
intros lyc Sc W regs mem md k cells BL n ret HC G10 Hn Hlive Hk1 Gra Hret Hret2 Htr.
pose proof tra_segs_low as Hsegs.
assert (HAR : AR trasegs B lyc Sc W mem md) by exact (proj1 (proj1 HC)).
assert (Hc47 : alloc_ceiling + ASTACK <= s1v /\ s1v + 512 <= 2 ^ 47) by (eapply rcore_ceil; eassumption). destruct Hc47 as [Hceil H47].
destruct (rcore_call_facts _ _ _ _ _ _ _ _ _ HC) as (Usp & Hnev & Hbb & V496 & V504).
pose proof HC as (HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Himg & HPerm & Hperm & Hkept).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (Has : ASTACK = 16384) by reflexivity.
assert (Hraw : YK0s.ret_ok (Z_to_bv 64 ret)).
{ apply YK0s.ret_ok_even. rewrite unsigned_lit_small by (clear - Hret; lia). exact Hret2. }
replace (Z_to_bv 64 0x53104) with (Z_to_bv 64 (pc_wrap_malloc (as_code B))) by (rewrite HBcode; vm_compute; reflexivity).
eapply SRr_mono.
{ eapply (aj_malloc_atD trasegs B LAWS Hsegs errno_low ML AMALLOC W regs mem STK sp0 FP ly S W0 mem0 md0 own lyc Sc md k n (-512) (Z_to_bv 64 ret) hk_ch HJ G10).
- clear - Hn. lia.
- rewrite Hbb. unfold LIVE_MAX in *. clear - Hlive HLIVE. lia.
- exact Usp.
- reflexivity.
- clear; lia.
- clear - HSTK; lia.
- exact G3.
- exact G4.
- exact Gra.
- exact Hraw.
- clear - Hnev Hk1 HEV. lia.
- apply (hk_chain B STK sp0 FP ly S W0 mem0 md0 own s1v Hs1 HSTK Hsp32 Htop32 rav s0v ch0 HCH0 Hrav Hs0v lyc Sc W regs mem md k HJ V496 V504 G2 G8).
unfold raZ. rewrite Gra, unsigned_lit_small by (clear - Hret; lia). clear - Hret. lia.
- exact Htr. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Ha0 & Hfr2 & Hd2 & Hres).
exists ly2, S2, regs2, mem2, md2, res. split; [reflexivity|].
replace (sp0 + -512 - ASTACK) with (s1v - ASTACK) in Hres by (rewrite Hs1; lia). replace (sp0 + -512) with s1v in Hres by (rewrite Hs1; lia).
destruct Hres as [(-> & Ebl & HK) | (Hres4096 & Ebl & HK)].
- change (optb 0 n) with (@nil (Z * Z)). rewrite app_nil_r.
split.
{ eapply rcore_call with (lyc := lyc) (Sc := Sc) (W := W) (regs := regs) (mem := mem) (md := md) (k := k) (BL := BL) (E := fun _ : Z => False); try eassumption;
[intros a [] | rewrite Ebl; exact HPerm]. }
split; [exact HP2|]. split; [exact Ha0|]. split; [left; reflexivity|].
destruct HK as (A1 & A2 & _).
split; [intros a Ha; apply A1; [clear - Ha Hceil H47 C1 Has; lia | clear - Ha; lia]|].
split; [|exact Hd2].
intros y Hy i Hi. destruct y as [yb yn]. cbn [fst snd] in *. apply (A2 yb yn i); [| exact Hi | intros []].
eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. right. exact Hy.
- assert (Hnz : res <> 0) by (clear - Hres4096; lia).
assert (Eo : optb res n = [(res, n)]) by (unfold optb; destruct (Z.eqb_spec res 0); [contradiction | reflexivity]). rewrite Eo.
pose proof (proj1 HJ2) as HAR2.
assert (HPerm2 : Permutation (ablocks B ly2 S2) (PROT ++ (tb, CHT_SIZE) :: BL ++ [(res, n)])).
{ rewrite Ebl. eapply Permutation_trans; [apply Permutation_app_tail; exact HPerm|]. rewrite <- app_assoc. cbn [app]. apply Permutation_refl. }
assert (Hperm2 : rperm (BL ++ [(res, n)])).
{ intros b m Hb.
assert (Hcase : (b, m) = (res, n) \/ In (b, m) ((tb, CHT_SIZE) :: BL)).
{ destruct Hb as [Hb | Hb]; [right; left; exact Hb|]. apply in_app_iff in Hb as [Hb | [Hb | []]]; [right; right; exact Hb | left; symmetry; exact Hb]. }
destruct Hcase as [Hc | Hc]; [injection Hc as -> ->|exact (Hperm b m Hc)].
split; [exact (aftok_new_block trasegs B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ly2 S2 W2 mem2 md2 res n HJ HAR2 Ebl ltac:(clear - Hn; lia))|].
intros blc lyq ownq i Hbl Hi.
exact (awr_new_block_any trasegs B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ly2 S2 W2 mem2 md2 res n blc i lyq ownq HJ HAR2 Ebl ltac:(clear - Hn; lia) Hbl Hi). }
assert (Hap_new : forall a, res <= a < res + req_size n -> rapart lyc Sc a).
{ intros a Ha. eapply rapart_frames with (ly2 := ly2) (S2 := S2); [| exact Hfr2 |].
- eapply rblk_apart with (b := res) (n := n) (BLX := BL ++ [(res, n)]); try eassumption. apply in_app_iff. right. left. reflexivity.
- intros c p. transitivity (frame_addr ly c p); [eapply journal_frame_addr; exact HJ2 | symmetry; eapply journal_frame_addr; exact HJ]. }
split.
{ eapply rcore_call with (lyc := lyc) (Sc := Sc) (W := W) (regs := regs) (mem := mem) (md := md) (k := k) (BL := BL)
(E := fun a : Z => res <= a < res + req_size n); try eassumption. }
split; [exact HP2|]. split; [exact Ha0|]. split; [right; exact Hres4096|].
destruct HK as (A1 & A2 & _).
split; [intros a Ha; apply A1; [clear - Ha Hceil H47 C1 Has; lia | clear - Ha; lia]|].
split; [|exact Hd2].
intros y Hy i Hi. destruct y as [yb yn]. cbn [fst snd] in *.
assert (Hyin : In (yb, yn) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. right. exact Hy. }
apply (A2 yb yn i Hyin Hi). intros He.
apply in_split in Hyin as (c1 & c2 & Ec).
assert (EE : ablocks B ly2 S2 = c1 ++ (yb, yn) :: c2 ++ (res, n) :: []) by (rewrite Ebl, Ec, <- app_assoc; reflexivity).
pose proof (sep_blocks_pos trasegs B LAWS ly2 S2 W2 mem2 md2 (yb, yn) (res, n) c1 c2 [] HAR2 EE) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. clear - Hd He Hi. lia.
Qed.
Lemma rz_free : forall lyc Sc W (regs : bvmap 5 word) mem md k cells BL (q : nat) pa n ret,
rcore lyc Sc W regs mem md k cells BL -> nth_error BL q = Some (pa, n) ->
getr regs 10 = Z_to_bv 64 pa -> k + 1 <= 80 ->
getr regs 1 = Z_to_bv 64 ret -> 4096 <= ret < 2 ^ 63 -> ret mod 2 = 0 ->
In (call_trace0 (pc_free_ra0 (as_code B)) regs hk_ch) (as_universe B) ->
SRr trasegs W (cfgat regs 0x53100 mem md)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = cfgat regs2 ret mem2 md2 /\
rcore ly2 S2 W2 regs2 mem2 md2 (k + 1) cells (ldel BL q) /\
aregs_preserved regs regs2 /\
(forall a, s1v <= a < s1v + 512 -> aview trasegs (w_H W2) mem2 a = aview trasegs (w_H W) mem a) /\
(forall (p' : nat) y, nth_error BL p' = Some y -> p' <> q -> rg_blk_kept (w_H W) (w_H W2) mem mem2 (fst y) (req_size (snd y))) /\
bud_le Sc S2 1 0 0 0).
Proof.
intros lyc Sc W regs mem md k cells BL q pa n ret HC Hq G10 Hk1 Gra Hret Hret2 Htr.
pose proof tra_segs_low as Hsegs.
assert (HAR : AR trasegs B lyc Sc W mem md) by exact (proj1 (proj1 HC)).
assert (Hc47 : alloc_ceiling + ASTACK <= s1v /\ s1v + 512 <= 2 ^ 47) by (eapply rcore_ceil; eassumption). destruct Hc47 as [Hceil H47].
destruct (rcore_call_facts _ _ _ _ _ _ _ _ _ HC) as (Usp & Hnev & Hbb & V496 & V504).
pose proof HC as (HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Himg & HPerm & Hperm & Hkept).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (Has : ASTACK = 16384) by reflexivity.
assert (Hin : In (pa, n) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. right. exact (nth_error_In _ _ Hq). }
assert (Hraw : YK0s.ret_ok (Z_to_bv 64 ret)).
{ apply YK0s.ret_ok_even. rewrite unsigned_lit_small by (clear - Hret; lia). exact Hret2. }
destruct (Hperm pa n ltac:(right; exact (nth_error_In _ _ Hq))) as [Htok _].
replace (Z_to_bv 64 0x53100) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite HBcode; vm_compute; reflexivity).
eapply SRr_mono.
{ eapply (aj_free_atD trasegs B LAWS Hsegs errno_low ML AFREE W regs mem STK sp0 FP ly S W0 mem0 md0 own lyc Sc md k pa n (-512) (Z_to_bv 64 ret) hk_ch HJ Hin G10).
- exact Usp.
- reflexivity.
- clear; lia.
- clear - HSTK; lia.
- exact G3.
- exact G4.
- exact Gra.
- exact Hraw.
- clear - Hnev Hk1 HEV. lia.
- apply (hk_chain B STK sp0 FP ly S W0 mem0 md0 own s1v Hs1 HSTK Hsp32 Htop32 rav s0v ch0 HCH0 Hrav Hs0v lyc Sc W regs mem md k HJ V496 V504 G2 G8).
unfold raZ. rewrite Gra, unsigned_lit_small by (clear - Hret; lia). clear - Hret. lia.
- exact Htr.
- exact Htok. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & El & El2) & Hfr2 & Hd2 & HK).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|].
replace (sp0 + -512 - ASTACK) with (s1v - ASTACK) in HK by (rewrite Hs1; lia). replace (sp0 + -512) with s1v in HK by (rewrite Hs1; lia).
destruct (ldel_split BL q (pa, n) Hq) as (b1 & b2 & EBL & Edel & Hlen1).
assert (HPerm2 : Permutation (ablocks B ly2 S2) (PROT ++ (tb, CHT_SIZE) :: ldel BL q)).
{ rewrite El2, Edel. replace (PROT ++ (tb, CHT_SIZE) :: b1 ++ b2) with ((PROT ++ (tb, CHT_SIZE) :: b1) ++ b2) by (rewrite <- app_assoc; reflexivity).
apply (Permutation_app_inv l1 l2 (PROT ++ (tb, CHT_SIZE) :: b1) b2 (pa, n)).
rewrite <- El. rewrite <- app_assoc. cbn [app]. rewrite <- EBL. exact HPerm. }
assert (Hperm2 : rperm (ldel BL q)).
{ intros b m Hb. apply Hperm. destruct Hb as [Hb | Hb]; [left; exact Hb|]. right. rewrite EBL. rewrite Edel in Hb.
apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb | Hb]; [left; exact Hb | right; right; exact Hb]. }
split.
{ eapply rcore_call with (lyc := lyc) (Sc := Sc) (W := W) (regs := regs) (mem := mem) (md := md) (k := k) (BL := BL)
(E := fun a : Z => pa <= a < pa + req_size n); try eassumption.
intros a Ha. eapply rblk_apart with (b := pa) (n := n) (BLX := BL); try eassumption. exact (nth_error_In _ _ Hq). }
split; [exact HP2|].
destruct HK as (A1 & A2 & _).
split; [intros a Ha; apply A1; [clear - Ha Hceil H47 C1 Has; lia | clear - Ha; lia]|].
split; [|exact Hd2].
intros p' y Hy Hpq i Hi. destruct y as [yb yn]. cbn [fst snd] in *.
assert (Hyin : In (yb, yn) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. right. exact (nth_error_In _ _ Hy). }
apply (A2 yb yn i Hyin Hi). intros He.
pose proof (rperm_apart_nth lyc Sc W mem md ((tb, CHT_SIZE) :: BL) (Datatypes.S p') (Datatypes.S q) (yb, yn) (pa, n) HAR HPerm Hy Hq ltac:(lia)) as Hd.
cbn [fst snd] in Hd. clear - Hd He Hi. lia.
Qed.
Lemma rz_free_null : forall lyc Sc W (regs : bvmap 5 word) mem md k cells BL ret,
rcore lyc Sc W regs mem md k cells BL ->
getr regs 10 = Z_to_bv 64 0 -> k + 1 <= 80 ->
getr regs 1 = Z_to_bv 64 ret -> 4096 <= ret < 2 ^ 63 -> ret mod 2 = 0 ->
In (call_trace0 (pc_free_ra0 (as_code B)) regs hk_ch) (as_universe B) ->
SRr trasegs W (cfgat regs 0x53100 mem md)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = cfgat regs2 ret mem2 md2 /\
rcore ly2 S2 W2 regs2 mem2 md2 (k + 1) cells BL /\
aregs_preserved regs regs2 /\
(forall a, s1v <= a < s1v + 512 -> aview trasegs (w_H W2) mem2 a = aview trasegs (w_H W) mem a) /\
(forall y, In y BL -> rg_blk_kept (w_H W) (w_H W2) mem mem2 (fst y) (req_size (snd y)))).
Proof.
intros lyc Sc W regs mem md k cells BL ret HC G10 Hk1 Gra Hret Hret2 Htr.
pose proof tra_segs_low as Hsegs.
assert (HAR : AR trasegs B lyc Sc W mem md) by exact (proj1 (proj1 HC)).
assert (Hc47 : alloc_ceiling + ASTACK <= s1v /\ s1v + 512 <= 2 ^ 47) by (eapply rcore_ceil; eassumption). destruct Hc47 as [Hceil H47].
destruct (rcore_call_facts _ _ _ _ _ _ _ _ _ HC) as (Usp & Hnev & Hbb & V496 & V504).
pose proof HC as (HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Himg & HPerm & Hperm & Hkept).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (Has : ASTACK = 16384) by reflexivity.
assert (Hraw : YK0s.ret_ok (Z_to_bv 64 ret)).
{ apply YK0s.ret_ok_even. rewrite unsigned_lit_small by (clear - Hret; lia). exact Hret2. }
replace (Z_to_bv 64 0x53100) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite HBcode; vm_compute; reflexivity).
eapply SRr_mono.
{ eapply (aj_free_null_at trasegs B LAWS Hsegs errno_low ML AFREE W regs mem STK sp0 FP ly S W0 mem0 md0 own lyc Sc md k (-512) (Z_to_bv 64 ret) hk_ch HJ G10).
- exact Usp.
- reflexivity.
- clear; lia.
- clear - HSTK; lia.
- exact G3.
- exact G4.
- exact Gra.
- exact Hraw.
- clear - Hnev Hk1 HEV. lia.
- apply (hk_chain B STK sp0 FP ly S W0 mem0 md0 own s1v Hs1 HSTK Hsp32 Htop32 rav s0v ch0 HCH0 Hrav Hs0v lyc Sc W regs mem md k HJ V496 V504 G2 G8).
unfold raZ. rewrite Gra, unsigned_lit_small by (clear - Hret; lia). clear - Hret. lia.
- exact Htr. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HPb & Hfr2 & HK).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|].
replace (sp0 + -512 - ASTACK) with (s1v - ASTACK) in HK by (rewrite Hs1; lia). replace (sp0 + -512) with s1v in HK by (rewrite Hs1; lia).
split.
{ eapply rcore_call with (lyc := lyc) (Sc := Sc) (W := W) (regs := regs) (mem := mem) (md := md) (k := k) (BL := BL) (E := fun _ : Z => False); try eassumption;
[intros a [] | eapply Permutation_trans; [exact HPb | exact HPerm]]. }
split; [exact HP2|].
destruct HK as (A1 & A2 & _).
split; [intros a Ha; apply A1; [clear - Ha Hceil H47 C1 Has; lia | clear - Ha; lia]|].
intros y Hy i Hi. destruct y as [yb yn]. cbn [fst snd] in *. apply (A2 yb yn i); [| exact Hi | intros []].
eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. right. exact Hy.
Qed.
End d.
