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
Definition INV_T0cX (MT : ameter_ops) (B : asyms) := fun cx xx E k ly3 S3 W3 ms3 md3 => INV_T0X MT B cx xx E k ly3 S3 W3 ms3 md3 /\ (Z.land (xgen3 cx xx) 1 =? 0) = true.
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
Ltac joinT1x RT1 :=
rebase_goal;
lazymatch goal with HS : st_ok_pi _ _ ?Ev ?ssv _ |- _ =>
let rs := eval vm_compute in (ss_mem ssv) in
let i := idx_of_base rs 60%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let cs := eval vm_compute in (YP09.r_chunks r) in
let j := idx_of_off cs 184 in let j := eval vm_compute in j in
lazymatch (eval vm_compute in (nth_error cs j)) with Some (YP09.mkChunk 184 (CVal 8 ?e)) =>
let E741 := fresh "E741" in
add_atom HS 741%nat (sv_denot Ev e) E741;
rechunk HS i j (SOff 741 0) ltac:(rewrite sv_denot_SOff0, E741; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity);
ra_join HS ss_T1x 742%nat fl_T1x_deads_bv ltac:(idtac);
fl_handX RT1 HS end end.
Lemma fl_T1cX : fl_fromX0 KS MT XN B CTX wfn ss_R (INV_RX MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_T0 (INV_T0cX MT B).
Proof.
intros RR. fl_preludeX.
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
hei_havoc HS; paj_run_to_tok RUNTO HS HJ3 SHOK FLBspan 0x22f0.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
xpt_stretch.
clear_frames.
rebase_goal.
lazymatch goal with HS : st_ok_pi _ _ ?Ev _ _ |- _ =>
prreg HS (23%bv : bv 5) Q23; prreg HS (27%bv : bv 5) Q27;
add_atom HS 839%nat (sv_denot Ev (SOff 679 0)) E839;
rechunk_off HS 60%nat 168 (SOff 839 0) ltac:(rewrite sv_denot_SOff0, E839; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity) end.
lazymatch goal with HS : st_ok_pi _ _ ?Ev _ _ |- _ =>
add_atom HS 840%nat (sv_denot Ev (SOff 680 0)) E840;
rechunk_off HS 60%nat 144 (SOff 840 0) ltac:(rewrite sv_denot_SOff0, E840; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity) end.
lazymatch goal with HS : st_ok_pi _ _ ?Ev _ _ |- _ =>
add_atom HS 841%nat (sv_denot Ev (SOff 681 0)) E841;
rechunk_off HS 60%nat 152 (SOff 841 0) ltac:(rewrite sv_denot_SOff0, E841; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity) end.
lazymatch goal with HS : st_ok_pi _ _ ?Ev _ _ |- _ =>
add_atom HS 842%nat (sv_denot Ev (SOff 58 0)) E842;
rechunk_off HS 60%nat 232 (SOff 842 0) ltac:(rewrite sv_denot_SOff0, E842; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity) end.
lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ =>
ra_join HS ss_R 843%nat fl_R_deads_bv ltac:(idtac;
ra_join_val HS 843%nat 0%nat Q23 E843; ra_join_val HS 843%nat 2%nat Q27 E845;
ra_join_fact HS 839%nat (mkAF 1 65535 0) ltac:(rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E839; rewrite Z.pow_0_r, Z.mod_1_r; rewrite sv_denot_SOff0; rewrite ?ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E683, unsigned_lit_small by (clear - Hw1 Hlw Hl0 R7 Hob241 Hob242 Hob253 Huar; lia); clear - Hw1 Hlw Hl0 R7 Hob241 Hob242 Hob253 Huar; lia);
ra_join_fact HS 840%nat (mkAF 0 65535 0) ltac:(rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E840; rewrite Z.pow_0_r, Z.mod_1_r; rewrite sv_denot_SOff0; rewrite ?ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E685, unsigned_lit_small by (clear - Hl0 Hlw Hw1 R7 Hob241 Hob242 Hob253 Huar; lia); clear - Hl0 Hlw Hw1 R7 Hob241 Hob242 Hob253 Huar; lia);
ra_join_fact HS 841%nat (mkAF 0 65535 0) ltac:(rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E841; rewrite Z.pow_0_r, Z.mod_1_r; rewrite sv_denot_SOff0; rewrite ?ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E681, unsigned_lit_small by (clear - Ht0 Hth Hh1 R8 Hob241 Hob242 Hob253 Huar; lia); clear - Ht0 Hth Hh1 R8 Hob241 Hob242 Hob253 Huar; lia);
ra_join_fact HS 845%nat (mkAF 1 65535 0) ltac:(rewrite E845; rewrite Z.pow_0_r, Z.mod_1_r; rewrite E684, unsigned_lit_small by (clear - Hh1 Hth Ht0 R8 Hob241 Hob242 Hob253 Huar; lia); clear - Hh1 Hth Ht0 R8 Hob241 Hob242 Hob253 Huar; lia));
fl_handX RR HS end.
split; [exists gen; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption|].
split; [| rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E621X].
exists pt, w, h, top, left, (fr_tidx f). cbn [c_s c_ly c_S].
split; [rewrite E843; exact E682|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E839, sv_denot_SOff0; rewrite ?ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); exact E683|].
split; [rewrite E845; exact E684|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E841, sv_denot_SOff0; rewrite ?ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); exact E681|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E840, sv_denot_SOff0; rewrite ?ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); exact E685|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E842, sv_denot_SOff0; rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); exact E58|].
split; [exact Hrpt|]. split; [exact Hw1|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh1|]. split; [exact Ht0|]. split; [exact Hth|]. split; [clear - Q8 Hob241 Hob242 Hob253 Huar; lia|].
split. { destruct Hpt as [(Hp0 & _ & _ & Hk0 & Eab3) | (Hp1 & Hk2 & Htb)]; [left | right].
+ split; [exact Hp0|]. split; [exact Hk0 | exact Eab3].
+ split; [exact Hp1|]. split; [exact Hk2 | exact Htb]. }
assert (XF1f : YO07.flag (YI0f.fl_gen3 (gcfg_of s GPAL) cur bef) 1 = false) by (unfold YO07.flag; rewrite <- Hgen, Hc; reflexivity).
unfold xtidx, ximg, xG. unfold xtmp, xG in XI, XI0, XLEN. cbn [c_s c_S x_GPAL x_cur x_bef] in *.
split; [exact XD|].
split; [rewrite (fl_tidx_notrans _ _ _ XF1f), <- XCt; apply Z.mod_small; clear - Q8; lia|].
rewrite (fl_img_notrans _ _ _ XF1f).
split; [exact XI|]. split; [exact XI0|]. split; [exact XLEN | exact XMLE].
-
hc_bool Hc ltac:(fun H => lazymatch type of H with context [U ?Ev (SExt false 8 (SOff 621 0))] => rewrite (gen_test8 Ev 621 gen 1 ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E621) ltac:(clear - Rgen Hob241 Hob242 Hob253 Huar; lia) ltac:(clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia)) in H end).
exfalso. clear - Hc Hgen Hflag.
change (xgen3 _ _) with (YI0f.fl_gen3 (gcfg_of s GPAL) cur bef) in Hflag. rewrite <- Hgen, Hc in Hflag. discriminate Hflag.
Qed.
End m.
End l.
End d.
