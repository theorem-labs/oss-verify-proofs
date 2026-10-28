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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z YI5x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCkd.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACkc ACj4 ACj9 ACjn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a ACjr ACj1 ACj0 ACja ACj6 ACjb ACiy ACj7 ACj3 ACj5.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YC5d YC7z YC7y YC7x YC85 YC88 YC7l.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AChz ACid ACie ACig ACi0 ACih ACi4.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCi6 YCi7.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section l.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition INV_T0sX (MT : ameter_ops) (B : asyms) := fun cx xx E k ly3 S3 W3 ms3 md3 => INV_T0X MT B cx xx E k ly3 S3 W3 ms3 md3 /\ (Z.land (xgen3 cx xx) 1 =? 0) = false.
Section m.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Hypothesis TLF : PALibF B.
Variable CTX : list (list Z).
Hypothesis HDEEP : forall c, In c CTX -> (2 <= length c)%nat.
Variable wfn : Z.
Variable KS : asink_syms.
Hypothesis AIL : asink_img_laws SEGS B KS.
Variable MT : ameter_ops.
Hypothesis MLAW : ameter_laws MT.
Hypothesis MLAWF : ameter_fs_laws MT.
Variable XN : xnums.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Ltac bef_EB :=
let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in
intros j v Hj; do 9 (try (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn [Nat.add]; assumption|])); destruct j; discriminate Hj.
Ltac uval Ev x v EK HK K Ux := assert (Ux : U Ev x = v) by (clear - EK HK; unfold U; cbn [sv_denot]; rewrite ?EK; k17 HK K; vm_compute; reflexivity).
Ltac joinT1x RT1 :=
rebase_goal;
lazymatch goal with HS : st_ok_pi _ _ ?Ev ?ssv _ |- _ =>
let rs := eval vm_compute in (ss_mem ssv) in
let i := idx_of_base rs 60%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let cs := eval vm_compute in (YP09.r_chunks r) in
let j := idx_of_off cs 232 in let j := eval vm_compute in j in
lazymatch (eval vm_compute in (nth_error cs j)) with Some (YP09.mkChunk 232 (CVal 8 ?e)) =>
let E741 := fresh "E741" in
add_atom HS 741%nat (sv_denot Ev e) E741;
rechunk HS i j (SOff 741 0) ltac:(rewrite sv_denot_SOff0, E741; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity);
ra_join HS ss_T1x 742%nat fl_T1x_deads_bv ltac:(idtac);
fl_handX RT1 HS end end.
Lemma fl_T1sX : fl_fromX0 KS MT XN B CTX wfn ss_T1x (INV_T1xX MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_T0 (INV_T0sX MT B).
Proof.
intros RT1. fl_preludeX.
pose proof HINV as (((gen & E621 & Rgen) & E625 & (fb & Hfb & EB) & (pt & w & h & top & left & E682 & E683 & E684 & E681 & E685 & Hrpt & Hw1 & Hl0 & Hlw & Hh1 & Ht0 & Hth & Hpt & (XD & XI & XI0 & XLEN & XMLE)) & E621X) & Hflag).
xpt_facts Hpt XPT.
pose proof HCUR as (XCa & XCg & XCd & XCn & XCct & XCdisp & XCt & XCimg & XClen & XClp). cbn in XCg.
assert (XFBNZ : forall fb, nth (i - 1) (cg_frames s) None = Some fb -> fr_ptr fb <> 0).
{ intros fb' Hfb'. destruct (fl_bef_in s i fb' Hi Hlen3 Hfb') as [_ Hfbi'].
destruct (fl_bef_blocks B ly S g s N rest fb' HPerm Hfbi') as (Hbin' & _ & _).
destruct (al_blocks _ _ LAWS ly S W mem md (fr_ptr fb') FRAME_SIZE HAR Hbin') as (_ & Hb4096' & _). clear - Hb4096'. lia. }
destruct (fl_front_model (mkFLCX ly S W regs mem md ch g s N i f rest fpos sp1 wfn hw (as_uar_cell B) E0) GPAL cur bef XCa XCg XCn ltac:(cbn [c_f]; clear - Q3; lia)
ltac:(unfold ACj6.fl_isfirst; cbn [c_i c_s]; apply (isfirst_of_opt _ bef);
[clear - HBEF; unfold oframe_relbA in HBEF; destruct (nth (i - 1) (cg_frames s) None), bef; first [exact I | destruct HBEF] | exact XFBNZ]))
as (XNPAL & XULCT & XALPHA & XSET & XGEN3).
cbn [c_s c_f c_i] in XNPAL, XULCT, XALPHA, XSET, XGEN3. clear XFBNZ.
assert (Hgen : gen = YI0f.fl_gen3 (gcfg_of s GPAL) cur bef).
{ apply zbv_inj64; [rewrite <- E621; exact E621X | clear - Rgen; lia |].
pose proof (fl_gen3_range (gcfg_of s GPAL) cur bef ltac:(rewrite <- XCg; clear - Q3; lia)) as G; clear - G Q3 XCg; lia. }
clear XULCT XALPHA XSET XGEN3.
cbn [c_i c_s] in Hfb. pose proof Hpt as Hpt0. unfold fl_tmpblkX, fl_FP0 in Hpt. cbn [c_ly c_S c_regs c_f c_s] in Hpt.
pose proof (EB 0%nat _ eq_refl) as E651. pose proof (EB 1%nat _ eq_refl) as E652. pose proof (EB 2%nat _ eq_refl) as E653.
pose proof (EB 3%nat _ eq_refl) as E654. pose proof (EB 4%nat _ eq_refl) as E655. pose proof (EB 5%nat _ eq_refl) as E656.
pose proof (EB 6%nat _ eq_refl) as E657. pose proof (EB 7%nat _ eq_refl) as E658. pose proof (EB 8%nat _ eq_refl) as E659.
cbn [Nat.add] in E651, E652, E653, E654, E655, E656, E657, E658, E659.
assert (Hsub3 : forall x, In x (ablocks B ly S) -> In x (ablocks B ly3 S3)).
{ intros x Hx. destruct Hpt as [(_ & _ & _ & _ & Eab3) | (_ & _ & (_ & _ & _ & Eab3 & _))]; rewrite Eab3; [exact Hx | apply in_app_iff; left; exact Hx]. }
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hing).
assert (Hcur3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hcur_in).
assert (Hpf3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (apply Hsub3; exact Hpf_in).
fl_blocks3X Hing3 Hcur3 Hpf3. fold F in HdFG, HdFC.
relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
assert (Rnp : 0 <= ACj6.fl_npal (mkFLCX ly S W regs mem md ch g s N i f rest fpos sp1 wfn hw (as_uar_cell B) E0) <= 65535) by (unfold ACj6.fl_npal; cbn [c_f c_s]; destruct (fl_uselct _); [clear - Q5 | clear - R9]; lia).
hei_havoc HS; paj_run_tok RUN HS HJ3 SHOK FLBspan.
all: try (oblG HJ3 E11n E32n Hcur3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
xpt_stretch.
let HUP' := fresh "HUP" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of HUP with forall a, ?lo <= a < _ -> aview ?sg ?Hh _ a = aview _ ?Hw ?me a =>
assert (HUP' : forall a, lo <= a < 2 ^ 64 -> aview sg Hh (ms_mem msX) a = aview sg Hw me a);
[ intros a Ha; rewrite <- (HUP a Ha); eapply (aview_kept_frame Ef rs _ _ _ lo HFr); [lia| |exact Ha];
intros b Hb (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
first [ clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi Hob241 Hob242 Hob253 Huar; lia | revert Hrg; evalE AG; intros Hrg; clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi Hob241 Hob242 Hob253 Huar; lia ] |]);
destruct Hin
| clear HUP; rename HUP' into HUP ] end end.
clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
-
hc_bool Hc ltac:(fun H => lazymatch type of H with context [U ?Ev (SExt false 8 (SOff 621 0))] => rewrite (gen_test8 Ev 621 gen 1 ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E621) ltac:(clear - Rgen Hob241 Hob242 Hob253 Huar; lia) ltac:(clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia)) in H end).
exfalso. clear - Hc Hgen Hflag.
change (xgen3 _ _) with (YI0f.fl_gen3 (gcfg_of s GPAL) cur bef) in Hflag. rewrite <- Hgen, Hc in Hflag. discriminate Hflag.
-
hc_bool Hc ltac:(fun H => lazymatch type of H with context [U ?Ev (SExt false 8 (SOff 621 0))] => rewrite (gen_test8 Ev 621 gen 1 ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E621) ltac:(clear - Rgen Hob241 Hob242 Hob253 Huar; lia) ltac:(clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia)) in H end).
hei_havoc HS; paj_run_to_tok RUNTO HS HJ3 SHOK FLBspan 0x20c8.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
xpt_stretch.
let HUP' := fresh "HUP" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of HUP with forall a, ?lo <= a < _ -> aview ?sg ?Hh _ a = aview _ ?Hw ?me a =>
assert (HUP' : forall a, lo <= a < 2 ^ 64 -> aview sg Hh (ms_mem msX) a = aview sg Hw me a);
[ intros a Ha; rewrite <- (HUP a Ha); eapply (aview_kept_frame Ef rs _ _ _ lo HFr); [lia| |exact Ha];
intros b Hb (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
first [ clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi Hob241 Hob242 Hob253 Huar; lia | revert Hrg; evalE AG; intros Hrg; clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi Hob241 Hob242 Hob253 Huar; lia ] |]);
destruct Hin
| clear HUP; rename HUP' into HUP ] end end.
clear_frames.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (14%bv : bv 5) Ra4.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (fl_pow2 B LAWS 17 0 (ACj6.fl_npal (mkFLCX ly S W regs mem md ch g s N i f rest fpos sp1 wfn hw (as_uar_cell B) E0)) W3 (ms_regs msX) (ms_mem msX) mdX
TFLUSH_STK (spZ regs) [(fr_ptr f + 20, fr_ptr f + 24)] ly S W mem md [(2, fpos)] ly3 S3 k eq_refl HJ3);
[ exact Ra0 | exact Ra1 | rewrite Ra4, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E625
| clear; lia | exact Rnp | right; reflexivity ] end. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & K & -> & HJ5 & HK12 & HK10 & HK13 & HKlo & HKs1 & HKs2 & Hav5 & Hpr5 & Hrg5).
clear Ra0 Ra1 Ra4.
assert (XI5 : pt <> 0 -> garr8 SEGS (mrestrict (w_H W3) mem5) pt (xtmp (mkFLCX ly S W regs mem md ch g s N i f rest fpos sp1 wfn hw (as_uar_cell B) E0) (mkFLXX path pf Sg GPAL cur bef))).
{ intros Hnz. lazymatch type of Hav5 with forall a, aview _ _ _ a = aview _ ?Hh ?m0 a => apply (garr8_aview_kept SEGS Hh Hh m0 mem5 pt _ (fun a _ => Hav5 a) (XI Hnz)) end. }
clear XI; rename XI5 into XI.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ssx) in
jafter_stretch_hi HS kk regs5 (mrestrict (w_H W3) mem5) FPOW_CLOB 0x20d8 HS2;
specialize (HS2 Hrg5 (regions_kept_all Ev (w_H W3) (ms_mem msX) mem5 _ Hav5 Hpr5)) | st_ok _ ?Ev ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ssx) in
jafter_stretch_hi HS kk regs5 (mrestrict (w_H W3) mem5) FPOW_CLOB 0x20d8 HS2;
specialize (HS2 Hrg5 (regions_kept_all Ev (w_H W3) (ms_mem msX) mem5 _ Hav5 Hpr5))  end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. rebaseE HS AG HEv.
lazymatch type of HEv with _ = havoc _ ?kk _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
let k1 := eval vm_compute in (Datatypes.S kk) in let k2 := eval vm_compute in (Datatypes.S (Datatypes.S kk)) in
assert (EK0 : ew Ev kk = Z_to_bv 64 (K + 1)) by (rewrite HEv; unfold FPOW_CLOB; cbn [map]; rewrite (ew_havoc_new _ kk _ 0 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth]; exact HK10);
assert (EK : ew Ev k1 = Z_to_bv 64 K) by (rewrite HEv; unfold FPOW_CLOB; cbn [map]; rewrite (ew_havoc_new _ kk _ 1 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth]; exact HK12);
assert (EK2 : ew Ev k2 = Z_to_bv 64 (2 ^ K)) by (rewrite HEv; unfold FPOW_CLOB; cbn [map]; rewrite (ew_havoc_new _ kk _ 2 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth]; exact HK13) | st_ok _ ?Ev _ _ =>
let k1 := eval vm_compute in (Datatypes.S kk) in let k2 := eval vm_compute in (Datatypes.S (Datatypes.S kk)) in
assert (EK0 : ew Ev kk = Z_to_bv 64 (K + 1)) by (rewrite HEv; unfold FPOW_CLOB; cbn [map]; rewrite (ew_havoc_new _ kk _ 0 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth]; exact HK10);
assert (EK : ew Ev k1 = Z_to_bv 64 K) by (rewrite HEv; unfold FPOW_CLOB; cbn [map]; rewrite (ew_havoc_new _ kk _ 1 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth]; exact HK12);
assert (EK2 : ew Ev k2 = Z_to_bv 64 (2 ^ K)) by (rewrite HEv; unfold FPOW_CLOB; cbn [map]; rewrite (ew_havoc_new _ kk _ 2 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth]; exact HK13)  end end.
clear HEv.
assert (XK : YO07.calcNextPower2Ex (YI0f.fl_npal (gcfg_of s GPAL) cur) = K) by (rewrite <- XNPAL; exact (np2ex_of_loop K _ HKlo HKs1 HKs2)).
assert (HK2p : 1 <= 2 ^ K <= 65536) by (split; [pose proof (Z.pow_pos_nonneg 2 K); clear - HKlo H Hob241 Hob242 Hob253 Huar; lia | change 65536 with (2 ^ 16); apply Z.pow_le_mono_r; clear - HKlo Hob241 Hob242 Hob253 Huar; lia]).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
lazymatch type of EK0 with ew _ ?nK0 = _ => lazymatch type of EK with ew _ ?nK = _ => lazymatch type of EK2 with ew _ ?nK2 = _ =>
pose proof (st_ok_pi_add_fact Ev ssv msv nK0 (mkAF 1 17 0) HS ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EK0, unsigned_lit_small by (clear - HKlo Hob241 Hob242 Hob253 Huar; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - HKlo Hob241 Hob242 Hob253 Huar; lia)) as HS4;
clear HS; pose proof (st_ok_pi_add_fact Ev _ msv nK (mkAF 0 16 0) HS4 ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EK, unsigned_lit_small by (clear - HKlo Hob241 Hob242 Hob253 Huar; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - HKlo Hob241 Hob242 Hob253 Huar; lia)) as HS3;
clear HS4; pose proof (st_ok_pi_add_fact Ev _ msv nK2 (mkAF 1 65536 0) HS3 ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EK2, unsigned_lit_small by (clear - HK2p Hob241 Hob242 Hob253 Huar; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - HK2p Hob241 Hob242 Hob253 Huar; lia)) as HS;
clear HS3 end end end | st_ok _ ?Ev ?ssv ?msv =>
lazymatch type of EK0 with ew _ ?nK0 = _ => lazymatch type of EK with ew _ ?nK = _ => lazymatch type of EK2 with ew _ ?nK2 = _ =>
pose proof (st_ok_pi_add_fact Ev ssv msv nK0 (mkAF 1 17 0) HS ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EK0, unsigned_lit_small by (clear - HKlo Hob241 Hob242 Hob253 Huar; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - HKlo Hob241 Hob242 Hob253 Huar; lia)) as HS4;
clear HS; pose proof (st_ok_pi_add_fact Ev _ msv nK (mkAF 0 16 0) HS4 ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EK, unsigned_lit_small by (clear - HKlo Hob241 Hob242 Hob253 Huar; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - HKlo Hob241 Hob242 Hob253 Huar; lia)) as HS3;
clear HS4; pose proof (st_ok_pi_add_fact Ev _ msv nK2 (mkAF 1 65536 0) HS3 ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EK2, unsigned_lit_small by (clear - HK2p Hob241 Hob242 Hob253 Huar; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - HK2p Hob241 Hob242 Hob253 Huar; lia)) as HS;
clear HS3 end end end  end.
norm_ss HS. relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
hei_havoc HS; paj_run_tok RUN HS HJ5 SHOK FLBspan.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
xpt_stretch.
clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
+
hei_havoc HS; paj_run_tok RUN HS HJ5 SHOK FLBspan.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
xpt_stretch.
clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
*
rewrite branch_ltu_U in Hc0. lazymatch type of Hc0 with context [U ?Ev ?x <? U ?Ev ?y] => uval Ev x 2 EK HKlo K Ux; uval Ev y K EK HKlo K Uy; rewrite Ux, Uy in Hc0; clear Ux Uy end. apply Z.ltb_lt in Hc0.
rewrite branch_geu_U, (U_atom _ 625 _ E625 ltac:(clear - Rnp; lia)) in Hc1. lazymatch type of Hc1 with context [U ?Ev ?x <? _] => uval Ev x ((2 ^ K - 1) mod 256) EK HKlo K Ux; rewrite Ux in Hc1; clear Ux end. apply negb_true_iff, Z.ltb_ge in Hc1.
paj_run_to_tok RUNTO HS HJ5 SHOK FLBspan 0x2110.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
xpt_stretch.
clear_frames.
joinT1x RT1.
split.
{ split; [exists gen; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption|].
split; [exists fb; apply fl_bef_havoc; [clear; lia|]; apply fl_bef_havoc; [clear; lia|]; split; [exact Hfb|]; cbn [c_i c_s]; bef_EB|].
split; [| rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E621X].
exists pt, w, h, top, left. cbn [c_s c_ly c_S]. rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia).
split; [exact E682|]. split; [exact E683|]. split; [exact E684|]. split; [exact E681|]. split; [exact E685|].
split; [exact Hrpt|]. split; [exact Hw1|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh1|]. split; [exact Ht0|]. split; [exact Hth|].
split; [exact Hpt0|].
split; [exact XD|]. split; [exact XI|]. split; [exact XI0|]. split; [exact XLEN | exact XMLE]. }
split; [unfold YO07.flag; change (xgen3 _ _) with (YI0f.fl_gen3 (gcfg_of s GPAL) cur bef); rewrite <- Hgen, Hc; reflexivity|].
lazymatch goal with |- exists tv, ew ?Ev 741%nat = _ /\ _ => exists (bv_unsigned (ew Ev 741%nat)) end.
split; [symmetry; apply Z_to_bv_bv_unsigned|].
split; [lazymatch goal with |- 0 <= bv_unsigned ?v < _ => pose proof (bv_unsigned_in_range 64 v) as Hrg; change (bv_modulus 64) with (2 ^ 64) in Hrg; exact Hrg end|].
rewrite ew_havoc_old by (clear; lia). rewrite E741.
unfold xtopt, xG. cbn [c_s x_GPAL x_cur].
lazymatch goal with |- bv_unsigned (sv_denot ?Ev ?e) mod 256 = _ => change (bv_unsigned (sv_denot Ev e)) with (U Ev e); uval Ev e (2 ^ K - 1) EK HKlo K Ux; rewrite Ux; clear Ux end.
symmetry. apply (proj1 (fl_tOpt_casesB _ cur K XK HKlo)); [clear - Hc0; lia | rewrite <- XNPAL; exact Hc1].
*
rewrite branch_ltu_U in Hc0. lazymatch type of Hc0 with context [U ?Ev ?x <? U ?Ev ?y] => uval Ev x 2 EK HKlo K Ux; uval Ev y K EK HKlo K Uy; rewrite Ux, Uy in Hc0; clear Ux Uy end. apply Z.ltb_lt in Hc0.
rewrite branch_geu_U, (U_atom _ 625 _ E625 ltac:(clear - Rnp; lia)) in Hc1. lazymatch type of Hc1 with context [U ?Ev ?x <? _] => uval Ev x ((2 ^ K - 1) mod 256) EK HKlo K Ux; rewrite Ux in Hc1; clear Ux end. apply negb_false_iff, Z.ltb_lt in Hc1.
paj_run_to_tok RUNTO HS HJ5 SHOK FLBspan 0x2110.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
xpt_stretch.
clear_frames.
joinT1x RT1.
split.
{ split; [exists gen; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption|].
split; [exists fb; apply fl_bef_havoc; [clear; lia|]; apply fl_bef_havoc; [clear; lia|]; split; [exact Hfb|]; cbn [c_i c_s]; bef_EB|].
split; [| rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E621X].
exists pt, w, h, top, left. cbn [c_s c_ly c_S]. rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia).
split; [exact E682|]. split; [exact E683|]. split; [exact E684|]. split; [exact E681|]. split; [exact E685|].
split; [exact Hrpt|]. split; [exact Hw1|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh1|]. split; [exact Ht0|]. split; [exact Hth|].
split; [exact Hpt0|].
split; [exact XD|]. split; [exact XI|]. split; [exact XI0|]. split; [exact XLEN | exact XMLE]. }
split; [unfold YO07.flag; change (xgen3 _ _) with (YI0f.fl_gen3 (gcfg_of s GPAL) cur bef); rewrite <- Hgen, Hc; reflexivity|].
lazymatch goal with |- exists tv, ew ?Ev 741%nat = _ /\ _ => exists (bv_unsigned (ew Ev 741%nat)) end.
split; [symmetry; apply Z_to_bv_bv_unsigned|].
split; [lazymatch goal with |- 0 <= bv_unsigned ?v < _ => pose proof (bv_unsigned_in_range 64 v) as Hrg; change (bv_modulus 64) with (2 ^ 64) in Hrg; exact Hrg end|].
rewrite ew_havoc_old by (clear; lia). rewrite E741.
unfold xtopt, xG. cbn [c_s x_GPAL x_cur].
lazymatch goal with |- bv_unsigned (sv_denot ?Ev ?e) mod 256 = _ => change (bv_unsigned (sv_denot Ev e)) with (U Ev e); uval Ev e (2 ^ (K + 1) - 1) EK HKlo K Ux; rewrite Ux; clear Ux end.
symmetry. apply (proj1 (proj2 (fl_tOpt_casesB _ cur K XK HKlo))); [clear - Hc0; lia | rewrite <- XNPAL; exact Hc1].
+
hei_havoc HS; paj_run_tok RUN HS HJ5 SHOK FLBspan.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
xpt_stretch.
clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
*
rewrite branch_ltu_U in Hc0. lazymatch type of Hc0 with context [U ?Ev ?x <? U ?Ev ?y] => uval Ev x 2 EK HKlo K Ux; uval Ev y K EK HKlo K Uy; rewrite Ux, Uy in Hc0; clear Ux Uy end. apply Z.ltb_ge in Hc0.
rewrite branch_geu_U, (U_atom _ 625 _ E625 ltac:(clear - Rnp; lia)) in Hc1. lazymatch type of Hc1 with context [U ?Ev ?x <? _] => uval Ev x (3) EK HKlo K Ux; rewrite Ux in Hc1; clear Ux end. apply negb_true_iff, Z.ltb_ge in Hc1.
paj_run_to_tok RUNTO HS HJ5 SHOK FLBspan 0x2110.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
xpt_stretch.
clear_frames.
joinT1x RT1.
split.
{ split; [exists gen; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption|].
split; [exists fb; apply fl_bef_havoc; [clear; lia|]; apply fl_bef_havoc; [clear; lia|]; split; [exact Hfb|]; cbn [c_i c_s]; bef_EB|].
split; [| rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E621X].
exists pt, w, h, top, left. cbn [c_s c_ly c_S]. rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia).
split; [exact E682|]. split; [exact E683|]. split; [exact E684|]. split; [exact E681|]. split; [exact E685|].
split; [exact Hrpt|]. split; [exact Hw1|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh1|]. split; [exact Ht0|]. split; [exact Hth|].
split; [exact Hpt0|].
split; [exact XD|]. split; [exact XI|]. split; [exact XI0|]. split; [exact XLEN | exact XMLE]. }
split; [unfold YO07.flag; change (xgen3 _ _) with (YI0f.fl_gen3 (gcfg_of s GPAL) cur bef); rewrite <- Hgen, Hc; reflexivity|].
lazymatch goal with |- exists tv, ew ?Ev 741%nat = _ /\ _ => exists (bv_unsigned (ew Ev 741%nat)) end.
split; [symmetry; apply Z_to_bv_bv_unsigned|].
split; [lazymatch goal with |- 0 <= bv_unsigned ?v < _ => pose proof (bv_unsigned_in_range 64 v) as Hrg; change (bv_modulus 64) with (2 ^ 64) in Hrg; exact Hrg end|].
rewrite ew_havoc_old by (clear; lia). rewrite E741.
unfold xtopt, xG. cbn [c_s x_GPAL x_cur].
lazymatch goal with |- bv_unsigned (sv_denot ?Ev ?e) mod 256 = _ => change (bv_unsigned (sv_denot Ev e)) with (U Ev e); uval Ev e (3) EK HKlo K Ux; rewrite Ux; clear Ux end. change (3 mod 256) with 3.
symmetry. destruct (Z.eq_dec K 2) as [HK2|HK2]; [ rewrite (proj1 (fl_tOpt_casesB _ cur K XK HKlo)); [rewrite HK2; reflexivity | clear - HK2; lia | rewrite <- XNPAL; rewrite HK2; exact Hc1] | apply (proj1 (proj2 (proj2 (fl_tOpt_casesB _ cur K XK HKlo)))); [clear - Hc0 HK2; lia | rewrite <- XNPAL; exact Hc1] ].
*
rewrite branch_ltu_U in Hc0. lazymatch type of Hc0 with context [U ?Ev ?x <? U ?Ev ?y] => uval Ev x 2 EK HKlo K Ux; uval Ev y K EK HKlo K Uy; rewrite Ux, Uy in Hc0; clear Ux Uy end. apply Z.ltb_ge in Hc0.
rewrite branch_geu_U, (U_atom _ 625 _ E625 ltac:(clear - Rnp; lia)) in Hc1. lazymatch type of Hc1 with context [U ?Ev ?x <? _] => uval Ev x (3) EK HKlo K Ux; rewrite Ux in Hc1; clear Ux end. apply negb_false_iff, Z.ltb_lt in Hc1.
paj_run_to_tok RUNTO HS HJ5 SHOK FLBspan 0x2110.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
xpt_stretch.
clear_frames.
joinT1x RT1.
split.
{ split; [exists gen; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption|].
split; [exists fb; apply fl_bef_havoc; [clear; lia|]; apply fl_bef_havoc; [clear; lia|]; split; [exact Hfb|]; cbn [c_i c_s]; bef_EB|].
split; [| rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E621X].
exists pt, w, h, top, left. cbn [c_s c_ly c_S]. rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia).
split; [exact E682|]. split; [exact E683|]. split; [exact E684|]. split; [exact E681|]. split; [exact E685|].
split; [exact Hrpt|]. split; [exact Hw1|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh1|]. split; [exact Ht0|]. split; [exact Hth|].
split; [exact Hpt0|].
split; [exact XD|]. split; [exact XI|]. split; [exact XI0|]. split; [exact XLEN | exact XMLE]. }
split; [unfold YO07.flag; change (xgen3 _ _) with (YI0f.fl_gen3 (gcfg_of s GPAL) cur bef); rewrite <- Hgen, Hc; reflexivity|].
lazymatch goal with |- exists tv, ew ?Ev 741%nat = _ /\ _ => exists (bv_unsigned (ew Ev 741%nat)) end.
split; [symmetry; apply Z_to_bv_bv_unsigned|].
split; [lazymatch goal with |- 0 <= bv_unsigned ?v < _ => pose proof (bv_unsigned_in_range 64 v) as Hrg; change (bv_modulus 64) with (2 ^ 64) in Hrg; exact Hrg end|].
rewrite ew_havoc_old by (clear; lia). rewrite E741.
unfold xtopt, xG. cbn [c_s x_GPAL x_cur].
lazymatch goal with |- bv_unsigned (sv_denot ?Ev ?e) mod 256 = _ => change (bv_unsigned (sv_denot Ev e)) with (U Ev e); uval Ev e (7) EK HKlo K Ux; rewrite Ux; clear Ux end. change (7 mod 256) with 7.
symmetry. destruct (Z.eq_dec K 2) as [HK2|HK2]; [ rewrite (proj1 (proj2 (fl_tOpt_casesB _ cur K XK HKlo))); [rewrite HK2; reflexivity | clear - HK2; lia | rewrite <- XNPAL; rewrite HK2; exact Hc1] | apply (proj2 (proj2 (proj2 (fl_tOpt_casesB _ cur K XK HKlo)))); [clear - Hc0 HK2; lia | rewrite <- XNPAL; exact Hc1] ].
Qed.
End m.
End l.
End d.
