(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0k YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ02 YQ00 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG02 YG06 YG03 YG0h YG0u YG0d YG0f.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0n YG0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Lemma atok_T {A} (t : itree astate A) : forall ns (Q : bool -> A -> Prop), atok true t Q -> atok ns t (fun _ _ => True).
Proof.
destruct t as [a | q snap k | pc | f]; cbn; intros ns Q H; [exact I | | discriminate H | exact H].
destruct H as [Hr Hk]. split; [exact Hr|]. intros z Hz. eapply atok_mono; [|exact (Hk z Hz)]. intros; exact I.
Qed.
Lemma split_snoc : forall {X} (l1 l2 m : list X) x y, l1 ++ x :: l2 = m ++ [y] -> x <> y -> exists l2', l2 = l2' ++ [y] /\ m = l1 ++ x :: l2'.
Proof.
intros X l1 l2 m x y E Hxy. destruct (exists_last (l := x :: l2) ltac:(discriminate)) as (l' & z & El).
rewrite El in E. rewrite app_assoc in E. apply app_inj_tail in E as [Em Ez]. subst z.
destruct l2 as [|w l2] using rev_ind.
- destruct l' as [|u l']; [cbn in El; injection El as El; exact (False_ind _ (Hxy El))|]. cbn in El. injection El as _ El. destruct l'; discriminate El.
- clear IHl2. exists l2. rewrite app_comm_cons in El. apply app_inj_tail in El as [El Ew]. subst w. split; [reflexivity|]. rewrite <- Em, <- El. reflexivity.
Qed.
Lemma realloc_tree_ok : forall U, model_laws U -> forall s p nold n tr,
Wf U s -> qtightB s -> vev s + 2 < VEV_MAX   -> In (p, nold) (blocks s) -> 0 <= n < MALLOC_MAX -> blocks_bytes s + n <= LIVE_MAX -> In tr U ->
atok true (realloc_tree p n tr s) (fun _ _ => True).
Proof.
intros U ML s p nold n tr W QB Hev Hp Hn Hlive Htr.
destruct (realloc_s1_big U s W QB Hev) as [W1 RB1].
unfold realloc_tree. apply atok_bind. rewrite free_null_eq. cbn [atok fst snd].
apply atok_bind. eapply atok_mono; [|exact (ml_malloc_big U ML (realloc_s1 s) n tr W1 RB1 Hn ltac:(exact Hlive) Htr)].
intros b [q s2] (MP & BI2 & G2). pose proof MP as (WF2 & NEV & _ & _ & BL & QT2). cbn [fst snd] in *.
assert (RB2 : regime_big s2).
{ destruct QB as (QT & BI). apply (regime_big_vev U s2 WF2 (conj (QT2 (qtight_ext s _ eq_refl eq_refl eq_refl QT)) BI2)).
pose proof (jbud_malloc1 (realloc_s1 s) n s2 Hn G2 NEV) as (V2 & _).
pose proof (vev_le s (realloc_s1 s) 1 ltac:(lia) ltac:(eapply bud_le_mono; [exact (realloc_s1_bud s) | lia | lia | lia | unfold HULL_UNIT; lia])). lia. }
unfold realloc_s1 in BL. cbn in BL.
destruct q as [| | |]; [exact I | | |].
all: destruct BL as [BL _]; apply atok_bind;
(eapply atok_mono; [|exact (atok_T _ b _ (ml_free_big U ML s2 p nold tr WF2 RB2 ltac:(right; rewrite BL; apply in_or_app; left; exact Hp) Htr))]);
intros b' [[] s3] _; exact I.
Qed.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Hypothesis ML : model_laws (as_universe B).
Local Notation ajournal := (ajournal segs B).
Local Notation acall_kept := (acall_kept segs B).
Lemma aj_realloc_atD : forall pc pc0, arealloc_realizes segs B pc pc0 -> In [pc0] (as_universe B) ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n_old n (o : Z) raw ch,
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
In (pa, n_old) (ablocks B lyc Sc) ->
getr regsT 10 = w64 pa -> getr regsT 11 = w64 n ->
64513 <= n < MALLOC_MAX -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
vev Sc + 2 < VEV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace0 pc0 regsT ch) (as_universe B) ->
(In (pa, n_old) (ablocks B ly S) -> forall i, 0 <= i < req_size n_old -> inFP FP (pa + i)) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 3) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
bud_le Sc S2 3 1 (wcost n) (hcost n) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
acall_kept lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False))
\/ (4096 <= res /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n_old) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2 ++ [(res, n)]) /\
acall_kept lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n \/ pa <= a < pa + req_size n_old) /\
(forall i, 0 <= i < Z.min n_old n -> aview segs (w_H W2) mem2 (res + i) = aview segs (w_H W) memT (pa + i))))).
Proof.
intros pc pc0 AREALLOC UNIV W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n_old n o raw ch
HJ Hin Ha0 Ha1 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr HFP.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity.
destruct (proj1 (in_ablocks B lyc Sc pa n_old) Hin) as (pp & Hpp & Hppin).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ASTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : acall_pre segs B lyc Sc W regsT memT mdc ch).
{ destruct HstkC as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
split; [exact HAR|]. split; [exact (proj2 (regime_big_vev _ Sc (am_wf _ _ _ _ (proj1 HAR)) HQT ltac:(zlia)))  |]. split; [rewrite Hra; exact Hraw|].
split; [exact Q1|]. split; [zlia|]. split; [zlia|]. split; [zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|].
split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hch | exact (proj1 HQT)]. }
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
pose proof (call_trace_in lyc pc0 regsT ch _ UNIV Htr) as Htr'.
pose proof (realloc_tree_ok _ ML Sc pp n_old n (call_trace lyc pc0 regsT ch) HWF HQT Hev Hppin ltac:(zlia) Hlive Htr') as HTOK.
pose proof (AREALLOC lyc Sc W regsT memT mdc pp n_old n ch HPRE (aregime3_vev Sc n ltac:(zlia) HQT Hev) Hppin ltac:(rewrite Hpp; exact Ha0) Ha1 Hn Hlive Htr') as HREAL.
eapply SRr_mono.
{ exact (amreal_SRr segs _ W _ _ HREAL (atok_asafe _ _ _ HTOK) (atok_agprog _ _ _ HTOK) (atok_nospin _ _ HTOK)). }
intros W2 c2 HwleW (r & tr & Hpath & Hleaf). destruct r as [q S3].
destruct Hleaf as (ly3 & regs3 & mem3 & md3 & -> & HP & Hres & HQT3 & BODY). cbn [fst snd] in Hres, HQT3, BODY.
assert (Snev : st_nev (realloc_s1 Sc) = st_nev Sc + 1) by reflexivity.
destruct (asptr_null_dec q) as [-> | Hnn].
-
destruct BODY as ((HAR3 & Hly3 & Hwle3 & Hio3 & Hfr3 & Hpres3) & (ns & MP3)).
destruct (realloc_mpost_big _ Sc n ns PNull S3 ltac:(zlia) HQT MP3) as (HQB3 & HJB3 & HBD3).
destruct MP3 as ((HWF3 & Hnev3 & Hsecs3 & Hfrs3 & Hbl3 & _) & _).
cbn [fst snd] in *. change (frames (realloc_s1 Sc)) with (frames Sc) in Hfrs3. change (blocks (realloc_s1 Sc)) with (blocks Sc) in Hbl3.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR Hly3) as (Eab & Efa & Eown).
assert (Eab3 : ablocks B ly3 S3 = ablocks B lyc Sc).
{ unfold ablocks. rewrite Hbl3. exact Eab. }
assert (HJ1 : ajournal ASTACK (spZ regsT) [] lyc Sc W memT mdc [] ly3 S3 W2 mem3 md3 3).
{ eapply (call_effect_journal segs B LAWS segs_low errno_low ASTACK lyc Sc W regsT memT mdc ly3 S3 W2 mem3 md3 (fun _ => False) [] [] 3);
[exact HAR3 | exact Hly3 | exact Hwle3 | exact Hio3 | exact Hfr3 | exact Hpres3 | exact HAR | exact HstkC | exact Hfrs3 | exact (jbud_mono _ _ 2 3 HJB3 ltac:(zlia)) | zlia | | | | exact HQB3].
- exact (secs_ext_length _ _ Hsecs3).
- intros a [].
- intros b m i Hb Hnb Hi. exfalso. apply Hnb. rewrite Eab3. exact Hb. }
exists ly3, S3, regs3, mem3, md3, 0.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. change own with ([] ++ own); eapply (ajournal_sub segs B LAWS segs_low); [exact HJ | exact HJ1 | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfrs3|]. split; [eapply bud_le_mono; [exact HBD3 | zlia | zlia | zlia | zlia]|]. left. split; [reflexivity|]. split; [exact Eab3|].
rewrite Hsp' in HJ1. eapply (acall_kept_of_journal segs B segs_low); [exact HJ1 | exact HAR | intros a (rg & [] & _) |].
intros b m i Hb Hi _. rewrite Eab3. exact Hb.
-
assert (BODY' : exists ly2 S2 (W2' : world segs) mem2 md2,
astage segs B ASTACK lyc Sc W regsT memT mdc (fun a => sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n) ly2 S2 W2' mem2 md2 /\
(exists ns, realloc_mpost (as_universe B) Sc n ns (q, S2)) /\ qtight S2 /\
(forall i, 0 <= i < Z.min n_old n -> aview segs (w_H W2') mem2 (sptr_addr B ly2 q + i) = aview segs (w_H W) memT (sptr_addr B lyc pp + i)) /\
astage segs B ASTACK ly2 S2 W2' regsT mem2 md2 (fun a => sptr_addr B lyc pp <= a < sptr_addr B lyc pp + req_size n_old) ly3 S3 W2 mem3 md3 /\
(exists ns, realloc_fpost (as_universe B) S2 pp n_old ns (tt, S3))) by (destruct q; [exact (False_ind _ (Hnn eq_refl)) | exact BODY | exact BODY | exact BODY]).
clear BODY. destruct BODY' as (ly2 & S2 & W2' & mem2 & md2 & (HAR2 & Hly2 & Hwle2 & Hio2 & Hfr2 & Hpres2) & (ns1 & MP2) & HQT2 & HCOPY &
(HAR3 & Hly3 & Hwle3 & Hio3 & Hfr3 & Hpres3) & (ns2 & FP3)).
destruct (realloc_mpost_big _ Sc n ns1 q S2 ltac:(zlia) HQT MP2) as (HQB2 & HJB2 & HBD2).
destruct (realloc_fpost_big _ S2 pp n_old ns2 S3 HQB2 FP3) as (HQB3 & HJB3 & HBD3). specialize (HQB3 HQT3).
destruct MP2 as ((HWF2 & Hnev2 & Hsecs2 & Hfrs2 & Hbl2 & _) & _). destruct FP3 as ((HWF3 & Hnev3 & Hsecs3 & Hfrs3 & (l1 & l2 & Hsplit & Hbl3) & _) & _).
cbn [fst snd] in *. change (frames (realloc_s1 Sc)) with (frames Sc) in Hfrs2. change (blocks (realloc_s1 Sc)) with (blocks Sc) in Hbl2.
change (st_secs (realloc_s1 Sc)) with (st_secs Sc) in *. rewrite Hpp in *.
assert (Hbl2' : blocks S2 = blocks Sc ++ [(q, n)] /\ ~ In q (map fst (blocks Sc))) by (destruct q; [exact (False_ind _ (Hnn eq_refl)) | exact Hbl2 | exact Hbl2 | exact Hbl2]).
clear Hbl2. destruct Hbl2' as [Hbl2 Hfresh].
assert (Hppnn : pp <> PNull).
{ intros ->. destruct (al_blocks _ _ LAWS lyc Sc W memT mdc pa n_old HAR Hin) as (_ & H4096 & _). cbn in Hpp. zlia. }
destruct Hsplit as [[Hnull _] | Hsplit]; [exfalso; exact (Hppnn Hnull)|].
set (res := sptr_addr B ly2 q) in *.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR2 Hly3) as (Eab' & Efa' & Eown').
set (fc := fun b : sptr * Z => (sptr_addr B lyc (fst b), snd b)).
set (f2 := fun b : sptr * Z => (sptr_addr B ly2 (fst b), snd b)).
set (f3 := fun b : sptr * Z => (sptr_addr B ly3 (fst b), snd b)).
assert (Efc : forall b, In b (blocks Sc) -> f2 b = fc b) by (intros b Hb; exact (map_eq_In f2 fc (blocks Sc) b Eab Hb)).
assert (Ef3 : forall b, In b (blocks S2) -> f3 b = f2 b) by (intros b Hb; exact (map_eq_In f3 f2 (blocks S2) b Eab' Hb)).
assert (Eab2 : ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)]).
{ unfold ablocks. change (map f2 (blocks S2) = map fc (blocks Sc) ++ [(res, n)]). rewrite Hbl2, map_app. cbn [map]. f_equal. apply map_ext_in. exact Efc. }
assert (Hnew : In (res, n) (ablocks B ly2 S2)) by (rewrite Eab2; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly2 S2 W2' mem2 md2 res n HAR2 Hnew) as (_ & Hr4096 & _).
destruct (in_split _ _ Hppin) as (c1 & c2 & Ec).
assert (Esp2 : blocks S2 = c1 ++ (pp, n_old) :: (c2 ++ [(q, n)])) by (rewrite Hbl2, Ec, <- app_assoc; reflexivity).
assert (Hdisj : forall b m a, In (b, m) (ablocks B lyc Sc) -> b <= a < b + req_size m -> ~ (res <= a < res + req_size n)).
{ intros b m a Hb Hr HE. apply in_split in Hb as (b1 & b2 & Ebq).
pose proof (sep_blocks_pos segs B LAWS ly2 S2 W2' mem2 md2 (b, m) (res, n) b1 b2 [] HAR2
ltac:(rewrite Eab2, Ebq, <- app_assoc; reflexivity)) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. zlia. }
assert (Eab3 : ablocks B ly3 S3 = map f2 l1 ++ map f2 l2).
{ unfold ablocks. change (map f3 (blocks S3) = map f2 l1 ++ map f2 l2). rewrite Hbl3, map_app.
f_equal; apply map_ext_in; intros b Hb; apply Ef3; rewrite Hsplit; apply in_or_app; [left; exact Hb | right; right; exact Hb]. }
assert (Eab2s : ablocks B ly2 S2 = map f2 l1 ++ (pa, n_old) :: map f2 l2).
{ unfold ablocks. change (map f2 (blocks S2) = map f2 l1 ++ (pa, n_old) :: map f2 l2). rewrite Hsplit, map_app. cbn [map app].
replace (f2 (pp, n_old)) with (pa, n_old); [reflexivity|]. rewrite (Efc (pp, n_old) Hppin). subst fc. cbn [fst snd]. rewrite Hpp. reflexivity. }
assert (Hlive2 : forall b m i, In (b, m) (ablocks B ly2 S2) -> 0 <= i < req_size m -> ~ (pa <= b + i < pa + req_size n_old) -> In (b, m) (ablocks B ly3 S3)).
{ intros b m i Hb Hi HnE. rewrite Eab3. rewrite Eab2s in Hb. apply in_app_or in Hb as [Hb | [Hb | Hb]].
- apply in_or_app. left. exact Hb.
- exfalso. injection Hb as <- <-. apply HnE. zlia.
- apply in_or_app. right. exact Hb. }
assert (HgoneC2 : forall p m i, In (p, m) (ablocks B ly2 S2) -> ~ In (p, m) (ablocks B ly3 S3) -> 0 <= i < req_size m -> inFP [(pa, pa + req_size n_old)] (p + i)).
{ intros p m i Hp Hnp Hi. exists (pa, pa + req_size n_old). split; [left; reflexivity|]. cbn [fst snd].
destruct (Z_lt_le_dec (p + i) pa) as [H1|H1]; [exfalso; apply Hnp; apply (Hlive2 p m i Hp Hi); zlia|].
destruct (Z_lt_le_dec (p + i) (pa + req_size n_old)) as [H2|H2]; [zlia|]. exfalso; apply Hnp; apply (Hlive2 p m i Hp Hi); zlia. }
assert (HJ1 : ajournal ASTACK (spZ regsT) [(pa, pa + req_size n_old)] lyc Sc W memT mdc [] ly2 S2 W2' mem2 md2 2).
{ eapply (call_effect_journal segs B LAWS segs_low errno_low ASTACK lyc Sc W regsT memT mdc ly2 S2 W2' mem2 md2 (fun a => res <= a < res + req_size n) [(pa, pa + req_size n_old)] [] 2);
[exact HAR2 | exact Hly2 | exact Hwle2 | exact Hio2 | exact Hfr2 | exact Hpres2 | exact HAR | exact HstkC | exact Hfrs2 | exact HJB2 | zlia | | | | exact HQB2].
- exact (secs_ext_length _ _ Hsecs2).
- intros a Ha. exists res, n. split; [right; exact Hnew|]. split; [exact Ha|]. right. intros Hold. exact (Hdisj res n a Hold Ha Ha).
- intros p0 m i Hp0 Hnp Hi. exfalso. apply Hnp. rewrite Eab2. apply in_or_app. left. exact Hp0. }
assert (HstkC2 : astk_ok ASTACK ly2 (spZ regsT)).
{ destruct Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop2 & Eslo2 & Eshi2 & _). unfold astk_ok, ly_bot in *. rewrite Eslo2, Eshi2, Etop2. exact HstkC. }
assert (HJ2 : ajournal ASTACK (spZ regsT) [(pa, pa + req_size n_old)] ly2 S2 W2' mem2 md2 [] ly3 S3 W2 mem3 md3 1).
{ eapply (call_effect_journal segs B LAWS segs_low errno_low ASTACK ly2 S2 W2' regsT mem2 md2 ly3 S3 W2 mem3 md3 (fun a => pa <= a < pa + req_size n_old) [(pa, pa + req_size n_old)] [] 1);
[exact HAR3 | exact Hly3 | exact Hwle3 | exact Hio3 | exact Hfr3 | exact Hpres3 | exact HAR2 | exact HstkC2 | exact Hfrs3 | exact HJB3 | zlia | | | exact HgoneC2 | exact HQB3].
- exact (secs_ext_length _ _ Hsecs3).
- intros a Ha. exists pa, n_old. split; [left; rewrite Eab2; apply in_or_app; left; exact Hin|]. split; [exact Ha|]. left.
exists (pa, pa + req_size n_old). split; [left; reflexivity | cbn; zlia]. }
assert (HJC : ajournal ASTACK (spZ regsT) [(pa, pa + req_size n_old)] lyc Sc W memT mdc [] ly3 S3 W2 mem3 md3 3).
{ change (@nil (Z * Z)) with (@nil (Z * Z) ++ []) at 2. change 3 with (2 + 1).
eapply (ajournal_sub segs B LAWS segs_low); [exact HJ1 | exact HJ2 | zlia | zlia |].
intros a (rg & [<-|[]] & Ha). cbn [fst snd] in Ha. left. split; [exists (pa, pa + req_size n_old); split; [left; reflexivity | exact Ha]|].
exists pa, n_old. split; [rewrite Eab2; apply in_or_app; left; exact Hin | zlia]. }
exists ly3, S3, regs3, mem3, md3, res.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJC. change own with ([] ++ own); eapply (ajournal_sub segs B LAWS segs_low); [exact HJ | exact HJC | zlia | zlia |].
intros a (rg & [<-|[]] & Ha). cbn [fst snd] in Ha.
destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (pa, n_old) (ablocks B ly S)) as [H0|H0].
- left. split; [| exists pa, n_old; split; [exact Hin | zlia]].
replace a with (pa + (a - pa)) by zlia. apply (HFP H0). zlia.
- right. exists pa, n_old. split; [exact Hin|]. split; [exact H0 | zlia]. }
split; [exact HP|].
assert (Eres : sptr_addr B ly3 q = res).
{ pose proof (Ef3 (q, n) ltac:(rewrite Hbl2; apply in_or_app; right; left; reflexivity)) as E. subst f3 f2. cbn [fst snd] in E. injection E as E. exact E. }
split; [rewrite Hres, Eres; reflexivity|].
split; [rewrite Hfrs3; exact Hfrs2|].
split; [eapply bud_le_mono; [exact (bud_le_trans _ _ _ _ _ _ _ _ _ _ _ HBD2 HBD3) | zlia | zlia | zlia | zlia]|].
right. split; [exact Hr4096|].
split.
{
assert (NE : (pp, n_old) <> (q, n)).
{ intros E. injection E as E _. apply Hfresh. rewrite <- E. apply in_map_iff. exists (pp, n_old). split; [reflexivity | exact Hppin]. }
symmetry in Hsplit. rewrite Hbl2 in Hsplit.
destruct (split_snoc l1 l2 (blocks Sc) (pp, n_old) (q, n) Hsplit NE) as (l2' & El2 & ESc).
assert (In1 : forall b, In b l1 -> In b (blocks Sc)) by (intros b Hb; rewrite ESc; apply in_or_app; left; exact Hb).
assert (In2 : forall b, In b l2' -> In b (blocks Sc)) by (intros b Hb; rewrite ESc; apply in_or_app; right; right; exact Hb).
exists (map fc l1), (map fc l2'). split.
- unfold ablocks. change (map fc (blocks Sc) = map fc l1 ++ (pa, n_old) :: map fc l2'). rewrite ESc, map_app. cbn [map app].
replace (fc (pp, n_old)) with (pa, n_old) by (subst fc; cbn [fst snd]; rewrite Hpp; reflexivity). reflexivity.
- rewrite Eab3, El2, map_app. cbn [map]. change (f2 (q, n)) with (res, n).
rewrite (map_ext_in f2 fc l1 (fun b Hb => Efc b (In1 b Hb))), (map_ext_in f2 fc l2' (fun b Hb => Efc b (In2 b Hb))). reflexivity. }
split.
{ rewrite Hsp' in HJC. eapply (acall_kept_of_journal segs B segs_low); [exact HJC | exact HAR | |].
- intros a (rg & [<-|[]] & Ha). cbn [fst snd] in Ha. right. exact Ha.
- intros b m i Hb Hi HnE. apply (Hlive2 b m i); [rewrite Eab2; apply in_or_app; left; exact Hb | exact Hi | intros X; apply HnE; right; exact X]. }
intros i Hi. rewrite <- (HCOPY i Hi).
fold res. assert (Hi' : 0 <= i < req_size n) by (unfold req_size; replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; zlia); zlia).
assert (Hnew3 : In (res, n) (ablocks B ly3 S3)).
{ apply (Hlive2 res n i Hnew Hi'). intros X. exact (Hdisj pa n_old (res + i) Hin X ltac:(zlia)). }
destruct (al_blocks _ _ LAWS ly2 S2 W2' mem2 md2 res n HAR2 Hnew) as (_ & _ & Hc2 & _ & Hb2 & _).
destruct (al_blocks _ _ LAWS ly3 S3 W2 mem3 md3 res n HAR3 Hnew3) as (_ & _ & _ & _ & Hb3 & _).
apply Hfr3; [zlia | exact (proj2 (Hb2 (res + i) ltac:(zlia))) | exact (proj2 (Hb3 (res + i) ltac:(zlia))) | |].
+ unfold ascratch. intros [X|X]; [zlia|].
destruct (al_client_img _ _ LAWS ly2 S2 W2' mem2 md2 (res + i) HAR2 ltac:(left; exists res, n; split; [exact Hnew | zlia])) as [_ NI].
exact (NI (proj1 (proj2 errno_low) _ X)).
+ intros X. exact (Hdisj pa n_old (res + i) Hin X ltac:(zlia)).
Qed.

End d.
End c.
