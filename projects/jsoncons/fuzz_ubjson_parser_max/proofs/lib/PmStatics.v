(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec StoreOk HeapIface LibIface L5Defs L5Core PmLayout.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmStatics () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.LibIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayout."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStatics.PMST."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStatics.PMST.Statics."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1bool"; "1fst"; "1option"; "1prod"; "1snd"; "2and"; "2eq"; "3Z"; "0Lay"; "0M"; "0M'"; "4img_clear"; "4u32_at"; "4u64_at"; "4u8_at"]; ["5lib_layout"; "5lib_statics_frame"; "5lib_statics_init"; "6pa_atexit"; "6pa_errcat_guard"; "6pa_loc_foot"; "6pa_locale_lock"; "6pa_need_locks"; "6pa_syscat_guard"; "8TopLS"; "8addrs_wf"; "8atexit_st"; "8dep"; "8lay_ok"; "8ls_ok"; "7st"]; ["7st_err"; "9In"; ":add"; ":le"; ":lt"; ":pow"; "0WF"; "0a"; "0b"; "0g"; "0hi"; "0i"; "0iv"; "0lo"; "0segs"; ";Z_to_bv"]; [";bv"; "0v"; "0x"]]).
Module PMST.
Record st : Type := ST { st_loc : bool; st_sys : bool; st_err : bool }.
Definition g0 : st := ST false false false.
Definition st_le (g g' : st) : Prop :=
(st_loc g = true -> st_loc g' = true) /\ (st_sys g = true -> st_sys g' = true) /\ (st_err g = true -> st_err g' = true).
Section Statics.
Variable segs : list Segment.
Variable A : pm_addrs.
Definition img_clear_l (M : word -> option byte) (l : list (Z * Z)) : Prop :=
forall iv, In iv l -> L5.img_clear M (fst iv) (snd iv).
Definition atexit_st (M : word -> option byte) (reg : bool) : Prop :=
let X := pa_atexit A in
L5.img_clear M X (X + 8)
/\ L5.u32_at segs M (X + 8) (if reg then 2 else 1)
/\ L5.img_clear M (X + 12) (X + 16)
/\ L5.u64_at segs M (X + 16) (X + 24)
/\ L5.img_clear M (X + 24) (X + 32)
/\ L5.u64_at segs M (X + 32) (pa_atexit_call A)
/\ (if reg then L5.u64_at segs M (X + 40) (pa_errcat_dtor A) else L5.img_clear M (X + 40) (X + 48))
/\ L5.img_clear M (X + 48) (X + 288)
/\ L5.u64_at segs M (X + 288) (pa_exit_guard A)
/\ (if reg then L5.u64_at segs M (X + 296) (pa_errcat_obj A) else L5.img_clear M (X + 296) (X + 304))
/\ L5.img_clear M (X + 304) (X + 544).
Definition ax_img : list (Z * Z) :=
let X := pa_atexit A in [(X, X + 8); (X + 12, X + 16); (X + 24, X + 32); (X + 40, X + 288); (X + 296, X + 544)].
Definition ax_cells : list (Z * nat * Z) :=
let X := pa_atexit A in [(X + 8, 4%nat, 1); (X + 16, 8%nat, X + 24); (X + 32, 8%nat, pa_atexit_call A); (X + 288, 8%nat, pa_exit_guard A)].
Definition pm_foot_lib : list (Z * Z) :=
[(pa_errcat_guard A, pa_errcat_guard A + 2); (pa_syscat_guard A, pa_syscat_guard A + 2)] ++ pa_loc_foot A.
Definition loc_ok (M : word -> option byte) (b : bool) : Prop :=
if b then L5.u8_at segs M (pa_glocale A + 40) 1 /\ L5.u64_at segs M (pa_glocale A + 32) (pa_classic_imp A)
else img_clear_l M (pa_loc_foot A).
Definition sys_ok (M : word -> option byte) (b : bool) : Prop :=
if b then L5.u8_at segs M (pa_syscat_guard A) 1 else L5.img_clear M (pa_syscat_guard A) (pa_syscat_guard A + 2).
Definition err_ok (M : word -> option byte) (b : bool) : Prop :=
(if b then L5.u8_at segs M (pa_errcat_guard A) 1 else L5.img_clear M (pa_errcat_guard A) (pa_errcat_guard A + 2))
/\ atexit_st M b.
Definition base_ok (M : word -> option byte) : Prop :=
L5.img_clear M 65536 (pa_rw_lo A)
/\ (exists canary, 0 <= canary < 2 ^ 64 /\ L5.u64_at segs M (pa_canary A) canary)
/\ L5.img_clear M (pa_need_locks A) (pa_need_locks A + 1)
/\ L5.img_clear M (pa_locale_lock A) (pa_locale_lock A + 4).
Definition ls_ok (g : st) (M : word -> option byte) : Prop :=
base_ok M /\ loc_ok M (st_loc g) /\ sys_ok M (st_sys g) /\ err_ok M (st_err g).
Record addrs_wf : Prop := AWF {
aw_rw : 65536 <= pa_rw_lo A < 2 ^ 40;
aw_canary : 0 <= pa_canary A < 2 ^ 40;
aw_errg : 0 <= pa_errcat_guard A < 2 ^ 40;
aw_sysg : 0 <= pa_syscat_guard A < 2 ^ 40;
aw_gloc : 0 <= pa_glocale A < 2 ^ 40;
aw_atexit : 0 <= pa_atexit A < 2 ^ 40;
aw_nl : 0 <= pa_need_locks A < 2 ^ 40;
aw_ll : 0 <= pa_locale_lock A < 2 ^ 40;
aw_locfoot : forall iv, In iv (pa_loc_foot A) -> 0 <= fst iv /\ snd iv < 2 ^ 40;
aw_gloc_in : exists iv, In iv (pa_loc_foot A) /\ fst iv <= pa_glocale A + 32 /\ pa_glocale A + 41 <= snd iv
}.
Definition dep (a : Z) : Prop :=
(exists iv, In iv (pm_foot A) /\ fst iv <= a < snd iv) \/ (pa_canary A <= a < pa_canary A + 8)
\/ (exists iv, In iv (pm_initc A) /\ fst iv <= a < snd iv).
Lemma in_foot_errg : ltac2:(TCodec.tc2 tcn__PmStatics "C'8'6&Q3&Dv0%211r1%5221&Q4&Q2+2%2261%4261%<261&Lr2%211p041pR@B1").
Proof. intros a. intros H. left. exists (pa_errcat_guard A, pa_errcat_guard A + 2). split; [unfold pm_foot; cbn; auto| cbn; lia]. Qed.
Lemma in_foot_sysg : ltac2:(TCodec.tc2 tcn__PmStatics "C'8'6&Q3&Hv0%211r1%5221&Q4&Q2+2%2261%4261%<261&Lr2%211p041pR@B1").
Proof. intros a. intros H. left. exists (pa_syscat_guard A, pa_syscat_guard A + 2). split; [unfold pm_foot; cbn; auto| cbn; lia]. Qed.
Lemma in_foot_loc : ltac2:(TCodec.tc2 tcn__PmStatics "J'4'8%2211&Q1r2&Ev0%211%53641'6&Q3&2r3%23<<1%421:&Q4&5%13@@5%32>1%:251&L%119p031p0?1pR@G1pRJG1").
Proof. intros iv a. intros Hin H. left. exists iv. split; [|exact H]. unfold pm_foot. cbn [app]. right. right. apply in_or_app. left. exact Hin. Qed.
Lemma in_foot_atexit : ltac2:(TCodec.tc2 tcn__PmStatics "C'8'6&Q3&Cv0%211r1%5221&Q4&Q2+a0%2261%4261%<261&Lr2%211p041pR@B1").
Proof. intros a.
intros H. left. exists (pa_atexit A, pa_atexit A + 544). split; [|cbn; lia].
unfold pm_foot. cbn [app]. right. right. apply in_or_app. right. cbn. auto.
Qed.
Lemma in_foot_nl : ltac2:(TCodec.tc2 tcn__PmStatics "C'8'6&Q3&Gv0%211r1%5221&Q4&Q2+1%2261%4261%<261&Lr2%211p041pR@B1").
Proof. intros a. intros H. right. right. exists (pa_need_locks A, pa_need_locks A + 1). split; [cbn; auto| cbn; lia]. Qed.
Lemma in_foot_ll : ltac2:(TCodec.tc2 tcn__PmStatics "C'8'6&Q3&Fv0%211r1%5221&Q4&Q2+4%2261%4261%<261&Lr2%211p041pR@B1").
Proof. intros a. intros H. right. right. exists (pa_locale_lock A, pa_locale_lock A + 4). split; [cbn; auto| cbn; lia]. Qed.
Section Frame.
Hypothesis WF : addrs_wf.
Variables M M' : word -> option byte.
Hypothesis AG : forall a, 0 <= a < 2 ^ 64 -> dep a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Hypothesis RO : forall a, 65536 <= a < pa_rw_lo A -> M (Z_to_bv 64 a) = None -> M' (Z_to_bv 64 a) = None.
Lemma clear_dep : ltac2:(TCodec.tc2 tcn__PmStatics "Q2'8&Q3zr2%3221&Q4&Q5+2+Q?%3221%5271'6r5r1%=221r4%;231%6231&L%11@p031pR@E1&<v:%231<9v;r6%5321?p041p081p0D1p0K1pRFQ01pRLQ11").
Proof. intros lo hi. intros Hlo Hhi D C i Hi. rewrite AG; [apply C; exact Hi| lia| apply D; exact Hi]. Qed.
Lemma u8_dep : ltac2:(TCodec.tc2 tcn__PmStatics "M'8'6&Q3zr2%3221&Q4&Q5+2+Q?%3221%5271%;271&Lr3%211&?vQ>v:r4%443216v;r5%746214p041p0:1p0>1pS4K1pR@L1").
Proof. intros a v. intros Ha D. apply (L5C.u8_at_agree segs M M'); [|lia|lia]. intros i Hi. apply AG; [lia|]. replace i with a by lia. exact D. Qed.
Lemma u32_dep : ltac2:(TCodec.tc2 tcn__PmStatics "Q6'8'6&Q3zr2%3221&Q4&Q5+2+Q?%3221%5271%;271r4r1%=221&Q2+4%2251%=251%C251&L%11Bp031pRHH1&=vQ>v:r3%4432@1v;r5%74621Cp041p0:1p0G1pS4Q41pR@Q51").
Proof. intros a v.
intros Ha D H. unfold L5.u32_at in *. rewrite (L5C.rdn_agree segs M M' 4%nat a); [exact H|lia|cbn; lia|].
intros i Hi. apply AG; [cbn in Hi; lia|]. apply D. cbn in Hi. lia.
Qed.
Lemma u64_dep : ltac2:(TCodec.tc2 tcn__PmStatics "Q6'8'6&Q3zr2%3221&Q4&Q5+2+Q?%3221%5271%;271r4r1%=221&Q2+8%2251%=251%C251&L%11Bp031pRHH1&>vQ>v:r3%4432@1v;r5%74621Cp041p0:1p0G1pS4Q41pR@Q51").
Proof. intros a v. intros Ha D. apply (L5C.u64_at_agree segs M M'); [|lia|lia]. intros i Hi. apply AG; [lia|]. apply D. exact Hi. Qed.
Local Ltac cdep tac := lazymatch goal with |- L5.img_clear _ ?lo ?hi => apply (clear_dep lo hi); [lia| lia| tac| try assumption] end.
Lemma atexit_frame : ltac2:(TCodec.tc2 tcn__PmStatics ":'1&Kv:r1%3221v;r2%6221p041pRB91").
Proof. intros b.
pose proof (aw_atexit WF) as HX. unfold atexit_st. cbv zeta.
intros (C1 & S & C2 & H & C3 & F0 & F1 & C4 & A0 & A1 & C5).
split; [cdep ltac:(intros; apply in_foot_atexit; lia)|].
split; [apply u32_dep; [lia| intros; apply in_foot_atexit; lia| exact S]|].
split; [cdep ltac:(intros; apply in_foot_atexit; lia)|].
split; [apply u64_dep; [lia| intros; apply in_foot_atexit; lia| exact H]|].
split; [cdep ltac:(intros; apply in_foot_atexit; lia)|].
split; [apply u64_dep; [lia| intros; apply in_foot_atexit; lia| exact F0]|].
split; [destruct b; [apply u64_dep; [lia| intros; apply in_foot_atexit; lia| exact F1] | cdep ltac:(intros; apply in_foot_atexit; lia)]|].
split; [cdep ltac:(intros; apply in_foot_atexit; lia)|].
split; [apply u64_dep; [lia| intros; apply in_foot_atexit; lia| exact A0]|].
split; [destruct b; [apply u64_dep; [lia| intros; apply in_foot_atexit; lia| exact A1] | cdep ltac:(intros; apply in_foot_atexit; lia)]|].
cdep ltac:(intros; apply in_foot_atexit; lia).
Qed.
Lemma ls_ok_frame : ltac2:(TCodec.tc2 tcn__PmStatics ":'O&Nr1v:%3221r2v;%6221p041pRD91").
Proof. intros g.
intros ((RO0 & (can & Hcan & CAN) & NL & LL) & LOC & SYS & (ERG & ATX)).
pose proof (aw_rw WF) as Hrw. pose proof (aw_canary WF) as Hcn. pose proof (aw_errg WF) as Heg. pose proof (aw_sysg WF) as Hsg.
pose proof (aw_gloc WF) as Hgl. pose proof (aw_nl WF) as Hnl. pose proof (aw_ll WF) as Hll.
split; [|split; [|split]].
- split; [|split; [|split]].
+ intros i Hi. apply RO; [exact Hi| apply RO0; exact Hi].
+ exists can. split; [exact Hcan|]. apply u64_dep; [lia| intros i Hi; right; left; exact Hi| exact CAN].
+ cdep ltac:(intros; apply in_foot_nl; lia).
+ cdep ltac:(intros; apply in_foot_ll; lia).
- unfold loc_ok in *. destruct (st_loc g).
+ destruct LOC as (G & P). destruct (aw_gloc_in WF) as (iv & Hin & Hlo & Hhi). split.
* apply u8_dep; [lia| apply (in_foot_loc iv); [exact Hin| lia]| exact G].
* apply u64_dep; [lia| intros i Hi; apply (in_foot_loc iv); [exact Hin| lia]| exact P].
+ intros iv Hin. destruct (aw_locfoot WF iv Hin) as [L1 L2].
apply (clear_dep (fst iv) (snd iv)); [lia| lia| intros a Ha; apply (in_foot_loc iv); assumption| apply LOC; exact Hin].
- unfold sys_ok in *. destruct (st_sys g).
+ apply u8_dep; [lia| apply in_foot_sysg; lia| exact SYS].
+ cdep ltac:(intros; apply in_foot_sysg; lia).
- split.
+ destruct (st_err g).
* apply u8_dep; [lia| apply in_foot_errg; lia| exact ERG].
* cdep ltac:(intros; apply in_foot_errg; lia).
+ apply atexit_frame. exact ATX.
Qed.
End Frame.
Lemma atexit_agree : ltac2:(TCodec.tc2 tcn__PmStatics "Q='J'Q@yR0%211'3y8%511%311pS651'1'8'6&Q3&Cv0%211r1%5221&Q4&Q2+a0%2261%4261%<261'7r4&Q?r2%22J1%411r5%113%83I31p0:1pRHH1&K%12;9r3%32=1p031p061pRBQ01pHQ21pFQ31pR>Q<1").
Proof. intros WF M M' b.
intros AG. pose proof (aw_atexit WF) as HX. unfold atexit_st. cbv zeta.
assert (C : forall lo hi, pa_atexit A <= lo -> hi <= pa_atexit A + 544 -> L5.img_clear M lo hi -> L5.img_clear M' lo hi).
{ intros lo hi H1 H2 CL i Hi. rewrite AG by lia. apply CL. exact Hi. }
assert (U8 : forall a v, pa_atexit A <= a -> a + 8 <= pa_atexit A + 544 -> L5.u64_at segs M a v -> L5.u64_at segs M' a v).
{ intros a v H1 H2. apply (L5C.u64_at_agree segs M M'); [|lia|lia]. intros i Hi. apply AG. lia. }
assert (U4 : forall a v, pa_atexit A <= a -> a + 4 <= pa_atexit A + 544 -> L5.u32_at segs M a v -> L5.u32_at segs M' a v).
{ intros a v H1 H2 H. unfold L5.u32_at in *. rewrite (L5C.rdn_agree segs M M' 4%nat a); [exact H|lia|cbn; lia|]. intros i Hi. apply AG. cbn in Hi. lia. }
intros (C1 & S & C2 & H & C3 & F0 & F1 & C4 & A0 & A1 & C5).
split; [apply (C (pa_atexit A) (pa_atexit A + 8)); [lia|lia|exact C1]|].
split; [apply (U4 (pa_atexit A + 8)); [lia|lia|exact S]|].
split; [apply (C (pa_atexit A + 12) (pa_atexit A + 16)); [lia|lia|exact C2]|].
split; [apply (U8 (pa_atexit A + 16) (pa_atexit A + 24)); [lia|lia|exact H]|].
split; [apply (C (pa_atexit A + 24) (pa_atexit A + 32)); [lia|lia|exact C3]|].
split; [apply (U8 (pa_atexit A + 32) (pa_atexit_call A)); [lia|lia|exact F0]|].
split; [destruct b; [apply (U8 (pa_atexit A + 40) (pa_errcat_dtor A)); [lia|lia|exact F1] | apply (C (pa_atexit A + 40) (pa_atexit A + 48)); [lia|lia|exact F1]]|].
split; [apply (C (pa_atexit A + 48) (pa_atexit A + 288)); [lia|lia|exact C4]|].
split; [apply (U8 (pa_atexit A + 288) (pa_exit_guard A)); [lia|lia|exact A0]|].
split; [destruct b; [apply (U8 (pa_atexit A + 296) (pa_errcat_obj A)); [lia|lia|exact A1] | apply (C (pa_atexit A + 296) (pa_atexit A + 304)); [lia|lia|exact A1]]|].
apply (C (pa_atexit A + 304) (pa_atexit A + 544)); [lia|lia|exact C5].
Qed.
Lemma pm_statics_exit : ltac2:(TCodec.tc2 tcn__PmStatics "E'O'Q@yR0%211'3y8%511%311p051&Nr2r1%3221&K&Q0r3%211%4271p061pF;1pRDD1").
Proof. intros g M. intros (_ & _ & _ & (_ & H)). exact H. Qed.
Definition TopLS : lib_statics := {| ls_state := st; LibIface.ls_ok := ls_ok; ls_g0 := g0 |}.
Record lay_ok (Lay : lib_layout) : Prop := LAYOK {
lk_segs : hl_segs (ll_heap Lay) = segs;
lk_foot : ll_foot Lay = pm_foot A;
lk_rw : ll_rw_lo Lay = pa_rw_lo A;
lk_guard : ll_guard Lay = pa_canary A;
lk_guard_initc : exists iv, In iv (ll_initc Lay) /\ fst iv <= pa_canary A /\ pa_canary A + 8 <= snd iv;
lk_initc : forall iv, In iv (pm_initc A) -> exists iv', In iv' (ll_initc Lay) /\ fst iv' <= fst iv /\ snd iv <= snd iv';
lk_init_initc : forall iv, In iv (pm_initc A) -> exists iv', In iv' (ll_init_img Lay) /\ fst iv' <= fst iv /\ snd iv <= snd iv';
lk_init_ro : exists iv, In iv (ll_init_img Lay) /\ fst iv <= 65536 /\ pa_rw_lo A <= snd iv;
lk_init_foot : forall iv, In iv pm_foot_lib -> exists iv', In iv' (ll_init_img Lay) /\ fst iv' <= fst iv /\ snd iv <= snd iv';
lk_init_ax_img : forall iv, In iv ax_img -> exists iv', In iv' (ll_init_img Lay) /\ fst iv' <= fst iv /\ snd iv <= snd iv';
lk_init_ax_cells : forall c, In c ax_cells -> In c (ll_init_cells Lay)
}.
Lemma pm_statics_frame : ltac2:(TCodec.tc2 tcn__PmStatics "<'@'J'Mr2%211&Ar3&I%3221p051p091pD;1").
Proof. intros Lay.
intros WF LK g M M' H FOOT RO INITC. cbn [LibIface.ls_ok TopLS] in *.
apply (ls_ok_frame WF M M'); [| |exact H].
- intros a Ha [(iv & Hin & Hr)|[Hc|(iv & Hin & Hr)]].
+ apply FOOT; [exact Ha|]. exists iv. rewrite (lk_foot Lay LK). split; assumption.
+ apply INITC; [exact Ha|]. left. destruct (lk_guard_initc Lay LK) as (iv & Hin & H1 & H2). exists iv. split; [exact Hin| lia].
+ apply INITC; [exact Ha|]. left. destruct (lk_initc Lay LK iv Hin) as (iv' & Hin' & H1 & H2). exists iv'. split; [exact Hin'| lia].
- intros a Ha Hn. pose proof (aw_rw WF) as RW. apply RO; [rewrite (lk_rw Lay LK), L5.unsigned_lit by lia; lia| exact Hn].
Qed.
Lemma pm_statics_init : ltac2:(TCodec.tc2 tcn__PmStatics "<'@'J'Mr2%211&Br3&I%3221p051p091pD;1").
Proof. intros Lay.
intros WF LK av uid rnd tid canary hw M IF. cbn [LibIface.ls_ok TopLS ls_g0].
unfold lib_init_facts in IF. cbv zeta in IF.
destruct IF as (IMG & _ & _ & _ & _ & _ & _ & GU & HC & REST).
destruct REST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CELLS).
rewrite (lk_segs Lay LK) in CELLS.
assert (CL : forall iv, In iv pm_foot_lib -> L5.img_clear M (fst iv) (snd iv)).
{ intros iv Hin. destruct (lk_init_foot Lay LK iv Hin) as (iv' & Hin' & H1 & H2). intros i Hi. apply (IMG iv' i Hin'). lia. }
assert (CA : forall iv, In iv ax_img -> L5.img_clear M (fst iv) (snd iv)).
{ intros iv Hin. destruct (lk_init_ax_img Lay LK iv Hin) as (iv' & Hin' & H1 & H2). intros i Hi. apply (IMG iv' i Hin'). lia. }
assert (CC : forall c, In c ax_cells -> cellz segs M (fst (fst c)) (snd (fst c)) (snd c)).
{ intros c Hin. apply CELLS. apply (lk_init_ax_cells Lay LK). exact Hin. }
unfold ls_ok, g0. cbn [st_loc st_sys st_err].
split; [|split; [|split]].
- split; [|split; [|split]].
+ destruct (lk_init_ro Lay LK) as (iv & Hin & H1 & H2). intros i Hi. apply (IMG iv i Hin). lia.
+ exists canary. split; [exact HC|]. unfold cellz in GU. rewrite (lk_guard Lay LK), (lk_segs Lay LK) in GU. exact GU.
+ destruct (lk_init_initc Lay LK (pa_need_locks A, pa_need_locks A + 1) ltac:(cbn; auto)) as (iv' & Hin' & H1 & H2).
intros i Hi. apply (IMG iv' i Hin'). cbn [fst snd] in *. lia.
+ destruct (lk_init_initc Lay LK (pa_locale_lock A, pa_locale_lock A + 4) ltac:(cbn; auto)) as (iv' & Hin' & H1 & H2).
intros i Hi. apply (IMG iv' i Hin'). cbn [fst snd] in *. lia.
- unfold loc_ok. intros iv Hin. apply CL. unfold pm_foot_lib. cbn [app]. right. right. exact Hin.
- unfold sys_ok. apply (CL (pa_syscat_guard A, pa_syscat_guard A + 2)). unfold pm_foot_lib. cbn. auto.
- split.
+ apply (CL (pa_errcat_guard A, pa_errcat_guard A + 2)). unfold pm_foot_lib. cbn. auto.
+ unfold atexit_st. cbv zeta.
split; [apply (CA (pa_atexit A, pa_atexit A + 8)); cbn; auto|].
split; [apply (CC (pa_atexit A + 8, 4%nat, 1)); cbn; auto|].
split; [apply (CA (pa_atexit A + 12, pa_atexit A + 16)); cbn; auto|].
split; [apply (CC (pa_atexit A + 16, 8%nat, pa_atexit A + 24)); cbn; auto|].
split; [apply (CA (pa_atexit A + 24, pa_atexit A + 32)); cbn; auto|].
split; [apply (CC (pa_atexit A + 32, 8%nat, pa_atexit_call A)); cbn; auto 6|].
split; [intros i Hi; apply (CA (pa_atexit A + 40, pa_atexit A + 288)); cbn; [auto 6| lia]|].
split; [intros i Hi; apply (CA (pa_atexit A + 40, pa_atexit A + 288)); cbn; [auto 6| lia]|].
split; [apply (CC (pa_atexit A + 288, 8%nat, pa_exit_guard A)); cbn; auto 7|].
split; [intros i Hi; apply (CA (pa_atexit A + 296, pa_atexit A + 544)); cbn; [auto 7| lia]|].
intros i Hi; apply (CA (pa_atexit A + 296, pa_atexit A + 544)); cbn; [auto 7| lia].
Qed.
End Statics.
End PMST.
