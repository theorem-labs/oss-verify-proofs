(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a YC80 YC1f YC1g YC1h YC81 YC4b YC20 YC44 YC45.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjr ACj1 ACj0 ACja.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACj0 ACj6 ACiy ACj7 ACj3.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC7y YC7x YC85 YC88 YC7l.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AChz ACid ACie ACig.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac upd_aboveF HUP HFr AG ltac ::=
let HUP' := fresh "HUP" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of HUP with forall a, ?lo <= a < _ -> aview ?sg ?Hh _ a = aview _ ?Hw ?me a =>
assert (HUP' : forall a, lo <= a < 2 ^ 64 -> aview sg Hh (ms_mem msX) a = aview sg Hw me a);
[ let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; rewrite <- (HUP a Ha); eapply (aview_kept_frame Ef rs _ _ _ lo HFr); [lia| |exact Ha];
let b := fresh "b" in let Hb := fresh "Hb" in let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros b Hb (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
first [ ltac Hb Hrg | revert Hrg; evalE AG; intros Hrg; ltac Hb Hrg ] |]);
destruct Hin
| clear HUP; rename HUP' into HUP ] end end.
Definition xbfacts (P : Prop) : Prop := P.
Lemma xbfacts_i : forall P : Prop, P -> xbfacts P. Proof. intros P H. exact H. Qed.
Ltac xpt_facts Hpt XPT :=
let LAWS := rnLAWS in
lazymatch goal with HAR3 : AR _ ?Bv ?ly3 ?S3 ?W3 ?m3 ?md3, Hfin3 : In (2, ?fpos) (frames ?S3'), EFA3 : forall c p, frame_addr ?ly3' c p = _, Fv := frame_addr _ 2 _ : Z,
Hcur_in : In (?cur, FRAME_SIZE) (ablocks _ ?ly ?S) |- _ =>
lazymatch type of Hpt with context [fl_tmpblkX _ ?cxv ?pt ?n _ _] =>
assert (XPT : pt <> 0 -> xbfacts (4096 <= pt /\ pt + n <= alloc_ceiling /\ (pt + n <= 2147446784 \/ 17594333495296 <= pt) /\ (Fv + 256 <= pt \/ pt + n <= Fv) /\
(cur + 40 <= pt \/ pt + n <= cur) /\ 1 <= n))
by (let Hnz := fresh "Hnz" in let TB := fresh "TB" in let Hin := fresh "Hin" in let Hd := fresh "Hd" in let Hn := fresh "Hn" in
let Q1 := fresh "Q" in let Q2 := fresh "Q" in let Q3 := fresh "Q" in let Eabp := fresh "Eabp" in let HPp := fresh "HPp" in let Hdc := fresh "Hdc" in
intros Hnz;
assert (TB : fl_tmpblkX Bv cxv pt n ly3 S3)
by (decompose [and or] Hpt; first [assumption | exfalso; exact (Hnz ltac:(assumption))]);
destruct TB as ([Q1 [_ Q2]] & Q3 & _ & Eabp & _ & _);
assert (Hin : In (pt, n) (ablocks Bv ly3 S3)) by (rewrite Eabp; apply in_app_iff; right; left; reflexivity);
assert (HPp : Permutation (ablocks Bv ly3 S3) ((pt, n) :: ablocks Bv ly S)) by (rewrite Eabp; apply Permutation_sym; apply Permutation_cons_append);
assert (Hn : 1 <= n) by (lazymatch n with ?w * ?h => lazymatch goal with Hw : 1 <= w, Hh : 1 <= h |- _ => clear - Hw Hh; nia end | _ => lia end);
pose proof (sep_block_frame _ _ LAWS ly3 S3 _ _ _ pt n 2 fpos HAR3 Hin Hfin3) as Hd;
unfold zdisjoint in Hd; cbn [fst snd] in Hd; change (fs_frame_bytes 2) with 256 in Hd; rewrite EFA3 in Hd; fold Fv in Hd;
pose proof (fasep_head _ LAWS _ _ _ _ _ (pt, n) (cur, FRAME_SIZE) _ HAR3 HPp Hcur_in) as Hdc;
unfold zdisjoint, block_rng in Hdc; cbn [fst snd] in Hdc; change (req_size FRAME_SIZE) with 40 in Hdc;
replace (req_size n) with n in Hd, Hdc by (unfold req_size; destruct (Z.eqb_spec n 0); lia);
apply xbfacts_i; clear - Q1 Q2 Q3 Hd Hdc Hn; lia) end end.
Ltac xwinP Hrr :=
let Hx := fresh "Hx" in intros Hx;
lazymatch goal with XF : xfacts (_ <= alloc_ceiling /\ 4096 <= _ /\ _), XBB : xbfacts (4096 <= _ /\ _) |- _ =>
lazymatch type of Hx with _ <= _ < _ + Z.of_nat (length ?L) =>
lazymatch goal with HL : Z.of_nat (length L) = _ |- _ =>
first [ lazymatch goal with Hsp1 : _ - 400 <= ?sp1 <= _ - 384 |- _ => clear - XF XBB HL Hrr Hx Hsp1 end | clear - XF XBB HL Hrr Hx ];
unfold xbfacts in XBB; unfold xfacts in XF; unfold SB in *; lia end end end.
Ltac xwin_loopP AG Hin Hrr :=
lazymatch type of Hin with
| False => destruct Hin
| _ \/ _ => let Hq := fresh "Hq" in let Hin2 := fresh "Hin" in
destruct Hin as [Hq | Hin2]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; first [exfalso; clear - Hrr; lia | evalE_in AG Hrr; xwinP Hrr] | xwin_loopP AG Hin2 Hrr]
end.
Ltac xblk_move HFr HG msn :=
let made := match goal with H : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => constr:(false) | _ => constr:(true) end in
lazymatch type of HFr with frame_of ?Ef _ _ _ =>
lazymatch made with true => let AG0 := fresh "AG0" in assert (AG0 : forall n, (n < 33)%nat -> ew Ef n = ew Ef n) by (intros; reflexivity) | false => idtac end end;
let AG := lazymatch goal with H : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => H end in
lazymatch type of HG with garr8 ?sg (mrestrict (w_H ?Wv) ?mo) ?bb ?L =>
let UNB := fresh "UNB" in let HG2 := fresh "HG" in
pose proof (kept_of_frame (segs:=sg) _ _ _ _ _ (fun x => ~ (bb <= x < bb + Z.of_nat (length L))) HFr
ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
intros b wlo whi a Hin Hrr; vm_compute in Hin; xwin_loopP AG Hin Hrr)) as UNB;
cbn beta in UNB;
assert (HG2 : garr8 sg (mrestrict (w_H Wv) (ms_mem msn)) bb L);
[ apply (garr8_aview_kept sg (w_H Wv) (w_H Wv) mo (ms_mem msn) bb L); [| exact HG];
let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [ms_mem]; apply UNB;
[ lazymatch goal with XF : xfacts (_ <= alloc_ceiling /\ 4096 <= _ /\ _), XBB : xbfacts (4096 <= _ /\ _), HL : Z.of_nat (length L) = _ |- _ =>
clear - XF XBB HL Ha; unfold xbfacts in XBB; unfold xfacts in XF; lia end
| let Hn := fresh "Hn" in intros Hn; exact (Hn Ha) ]
| clear UNB HG; rename HG2 into HG; lazymatch made with true => clear AG | false => idtac end ] end.
Ltac xpt_stretch :=
lazymatch goal with HFr : frame_of _ _ _ _ |- SRr _ _ (mkCfg ?msn _) _ =>
lazymatch goal with XI : ?pt <> 0 -> garr8 ?sg (mrestrict (w_H ?Wv) ?mo) ?pt' ?L, XPT : _ <> 0 -> xbfacts _ |- _ =>
let XI2 := fresh "XI" in
assert (XI2 : pt <> 0 -> garr8 sg (mrestrict (w_H Wv) (ms_mem msn)) pt L);
[ let Hnz := fresh "Hnz" in let HG := fresh "HG" in let XBB := fresh "XBB" in
intros Hnz; pose proof (XI Hnz) as HG; pose proof (XPT Hnz) as XBB; xblk_move HFr HG msn; exact HG
| clear XI; rename XI2 into XI ] end end.
