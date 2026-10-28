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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACj2 ACkc ACj4.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a ACjr ACj1 ACj0 ACja ACj6 ACjb ACiy ACj7 ACj8.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07 YI0e.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YC5d YC7z YC7y YC7x YC85 YC88 YC7l.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AChz ACid ACie ACig ACi0 ACif ACih ACi4 ACi1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma mod4_land2 : forall x, 0 <= x -> x mod 4 = 0 -> Z.land x 2 = 0.
Proof.
intros x Hx H4. replace x with ((x / 4) * 2 ^ 2) by (pose proof (Z.div_mod x 4 ltac:(lia)); lia).
apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z_lt_le_dec n 2) as [Hl|Hge].
- rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- replace (Z.testbit 2 n) with false; [apply andb_false_r|]. symmetry. change 2 with (2 ^ 1). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.
Lemma mod4_land1 : forall x, 0 <= x -> x mod 4 = 0 -> Z.land x 1 = 0.
Proof.
intros x Hx H4. replace x with ((x / 4) * 2 ^ 2) by (pose proof (Z.div_mod x 4 ltac:(lia)); lia).
apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z_lt_le_dec n 2) as [Hl|Hge].
- rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- replace (Z.testbit 1 n) with false; [apply andb_false_r|]. symmetry. change 1 with (2 ^ 0). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.
Ltac nat_side := first [ apply (proj1 (Nat.ltb_lt _ _)); vm_compute; reflexivity
| apply (proj1 (Nat.eqb_neq _ _)); vm_compute; reflexivity ].
Ltac rebaseF HS AG HEv :=
let AG2 := fresh "AG" in let Ev := fresh "E" in
lazymatch type of AG with forall n, _ -> _ = ew ?E0 n =>
lazymatch type of HS with st_ok_pi _ _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
let HEIv := fresh "HEI" in
lazymatch type of HEv with
| _ = havoc ?Eo ?kk ?ws => lazymatch goal with Ho : img_env ?val ?lim Eo |- _ =>
pose proof (img_env_havoc_hi Eo kk ws Ho ltac:(cbv; lia)) as HEIv; rewrite <- HEv in HEIv end
| _ = ?En => try (lazymatch goal with Hn : img_env _ _ En |- _ => rewrite <- HEv in Hn end) end;
repeat match goal with H : img_env _ _ (ewset _ _ _) |- _ => clear H end;
assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; apply AG; exact Hnn);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 33 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact H);
clear H; rename H2 into H
end end end;
clear AG; rename AG2 into AG | st_ok _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
let HEIv := fresh "HEI" in
lazymatch type of HEv with
| _ = havoc ?Eo ?kk ?ws => lazymatch goal with Ho : img_env ?val ?lim Eo |- _ =>
pose proof (img_env_havoc_hi Eo kk ws Ho ltac:(cbv; lia)) as HEIv; rewrite <- HEv in HEIv end
| _ = ?En => try (lazymatch goal with Hn : img_env _ _ En |- _ => rewrite <- HEv in Hn end) end;
repeat match goal with H : img_env _ _ (ewset _ _ _) |- _ => clear H end;
assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; apply AG; exact Hnn);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 33 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact H);
clear H; rename H2 into H
end end end;
clear AG; rename AG2 into AG  end end.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
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
Ltac w_hand RC target :=
lazymatch goal with HSx : st_ok_pi _ _ _ _ _, AGx : forall n, (n < 33)%nat -> _ |- _ => let HEv0 := fresh "HEv" in rebaseF HSx AGx HEv0; clear HEv0 end;
lazymatch goal with HSx : st_ok_pi _ _ _ _ _ |- _ => ra_join HSx target 681%nat ((@BV 5 10 I) :: (@BV 5 11 I) :: nil) ltac:(idtac); fl_handX RC HSx end.
Lemma fl_WX : fl_fromX0 KS MT XN B CTX wfn ss_S (INV_SX MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_Fv (INV_FvX MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_DIFF (INV_DIFFX MT B).
Proof.
intros RSv RFv. fl_preludeX.
pose proof HINV as ((Hk3 & Eab3 & (gen & E621 & Rgen & Hgen2) & E625 & (fb & Hfb & EB)) & E621X & XF2 & MLE0).
cbn [c_i c_s] in Hfb.
destruct (fl_bef_in s i fb Hi Hlen3 Hfb) as [Hfbe Hfbi].
pose proof (Ofr fb Hfbi) as Ob'. cbn [obj_at LAY_Frame LAY_FrameConfig frame_vals app] in Ob'. destruct Ob' as (_ & _ & [_ P2] & _). cbn [fst snd N.to_nat Z.of_N] in P2. change (2 ^ (8 * 4)) with (2 ^ 32) in P2.
pose proof HCUR as (XCa & _).
assert (XBa : forall b, bef = Some b -> fr_attr fb = YO07.f_attr b).
{ intros b Eb. rewrite Eb, Hfb in HBEF. exact (proj1 HBEF). }
pose proof (EB 0%nat _ eq_refl) as E651. pose proof (EB 1%nat _ eq_refl) as E652. pose proof (EB 2%nat _ eq_refl) as E653.
pose proof (EB 3%nat _ eq_refl) as E654. pose proof (EB 4%nat _ eq_refl) as E655. pose proof (EB 5%nat _ eq_refl) as E656.
pose proof (EB 6%nat _ eq_refl) as E657. pose proof (EB 7%nat _ eq_refl) as E658. pose proof (EB 8%nat _ eq_refl) as E659.
cbn [Nat.add] in E651, E652, E653, E654, E655, E656, E657, E658, E659.
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hing).
assert (Hcur3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hcur_in).
assert (Hpf3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hpf_in).
fl_blocks3X Hing3 Hcur3 Hpf3. fold F in HdFG, HdFC.
relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
-
assert (XSLOW : forall b, bef = Some b -> YO07.px_ne (gcfg_of s GPAL) cur b = YO07.cmp_pixel (gcfg_of s GPAL) cur b).
{ intros b Eb. apply YI0e.px_ne_slow. unfold YO07.flag. rewrite <- (XBa b Eb).
rewrite branch_ne_U, (U_and_atom _ 653 (fr_attr fb) 1 E653), U_lit in Hc by (clear - P2; lia).
rewrite Hc. reflexivity. }
reshok HS.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ3 SHOK FLBspan 0x1a88.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
w_hand RSv ss_S.
split.
{ split.
{ split; [exact Hk3|]. split; [exact Eab3|].
split; [exists gen; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption|]; split; [exact Rgen | exact Hgen2]|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption|].
exists fb. apply fl_bef_havoc; [clear; lia|]. split; [exact Hfb|]. cbn [c_i c_s]. bef_EB. }
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E621X | split; [exact XF2 | exact MLE0]]. }
intros xb0 Exb0; cbn [x_bef] in Exb0; exact (XSLOW xb0 Exb0).
-
assert (XB1 : Z.land (fr_attr fb) 1 = 0).
{ rewrite branch_ne_U, (U_and_atom _ 653 (fr_attr fb) 1 E653), U_lit in Hc by (clear - P2; lia). apply negb_false_iff, Z.eqb_eq in Hc. exact Hc. }
reshok HS.
hei_havoc HS; paj_run_tok RUN HS HJ3 SHOK FLBspan.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => clear Hb end.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
+
assert (XFAST : forall b, bef = Some b -> YO07.px_ne (gcfg_of s GPAL) cur b = (fun c q : Z => negb (c =? q))).
{ intros b Eb. rewrite branch_eq_U, (U_wtest _ (fr_attr fb) (fr_attr f) E653 E52 P2 Q2), U_lit in Hc by (clear; lia). apply Z.eqb_eq in Hc.
destruct (wtest_zero _ _ Hc) as (Z1 & Z2 & Z3). apply px_ne_fast_w; rewrite <- ?(XBa b Eb), <- ?XCa; assumption. }
reshok HS.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ3 SHOK FLBspan 0x1d38.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
w_hand RFv ss_Fv.
split.
{ split.
{ split; [exact Hk3|]. split; [exact Eab3|].
split; [exists gen; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption|]; split; [exact Rgen | exact Hgen2]|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption|].
exists fb. apply fl_bef_havoc; [clear; lia|]. split; [exact Hfb|]. cbn [c_i c_s]. bef_EB. }
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E621X | split; [exact XF2 | exact MLE0]]. }
intros xb0 Exb0; cbn [x_bef] in Exb0; exact (XFAST xb0 Exb0).
+
assert (XSLOW : forall b, bef = Some b -> YO07.px_ne (gcfg_of s GPAL) cur b = YO07.cmp_pixel (gcfg_of s GPAL) cur b).
{ intros b Eb. rewrite branch_eq_U, (U_wtest _ (fr_attr fb) (fr_attr f) E653 E52 P2 Q2), U_lit in Hc by (clear; lia). apply Z.eqb_neq in Hc.
apply px_ne_slow_w. rewrite <- (XBa b Eb), <- XCa. destruct (wtest_nonzero _ _ Hc) as [Z1 | [Z2 | Z3]]; [right; left; exact Z1 | right; right; left; exact Z2 | right; right; right; exact Z3]. }
reshok HS.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ3 SHOK FLBspan 0x1a88.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
w_hand RSv ss_S.
split.
{ split.
{ split; [exact Hk3|]. split; [exact Eab3|].
split; [exists gen; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption|]; split; [exact Rgen | exact Hgen2]|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption|].
exists fb. apply fl_bef_havoc; [clear; lia|]. split; [exact Hfb|]. cbn [c_i c_s]. bef_EB. }
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E621X | split; [exact XF2 | exact MLE0]]. }
intros xb0 Exb0; cbn [x_bef] in Exb0; exact (XSLOW xb0 Exb0).
Qed.
End e.
End d.
End a.
