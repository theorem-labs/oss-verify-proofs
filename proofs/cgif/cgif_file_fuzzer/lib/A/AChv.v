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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACj2 ACkc ACj4 ACjm.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a ACjr ACj1 ACj0 ACja ACj6 ACjb ACiy ACj7 ACj8 ACj3 AChd ACjc ACje ACjh ACjf.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YC5d YC7z YC7y YC7x YC85 YC88 YC7l.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AChz ACid ACie ACig ACi0 ACif ACih ACi4 ACia ACi3 ACiq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Notation SB := YC81.SB.
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
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition WF_CLOB : list Prelude.reg := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition fl_dimsi_deads_bv : list (bv 5) := [1; 5; 7; 12; 13; 14; 15; 16; 17; 19; 24; 25; 28; 29; 30; 31]%bv.
Lemma wf_clob_cases : forall r : bv 5, reg_in r WF_CLOB = false -> r = 0%bv \/ In r ([2; 3; 4; 8; 9]%bv : list (bv 5)).
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]). destruct Hin.
Qed.
Section l.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA AS_memcmp_2).
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
Ltac upd_aboveF HUP HFr AG ltac :=
let HUP' := fresh "HUP" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of HUP with forall a, ?lo <= a < _ -> aview ?sg ?Hh _ a = aview _ ?Hw ?me a =>
assert (HUP' : forall a, lo <= a < 2 ^ 64 -> aview sg Hh (ms_mem msX) a = aview sg Hw me a);
[ let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; rewrite <- (HUP a Ha); eapply (aview_kept_frame Ef rs _ _ _ lo HFr); [lia| |exact Ha];
let b := fresh "b" in let Hb := fresh "Hb" in let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros b Hb (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; first [ ltac Hb Hrg | revert Hrg; evalE AG; intros Hrg; ltac Hb Hrg ] |]);
destruct Hin
| clear HUP; rename HUP' into HUP ] end end.
Ltac bef_EB :=
let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in
intros j v Hj; do 9 (try (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn [Nat.add]; assumption|])); destruct j; discriminate Hj.
Ltac ws_pin HS r e Hr dtac :=
let HS3 := fresh "HS3" in
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msv =>
pose proof (st_ok_pin_rege Ev ssx msv r e HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite Hr; cbn [sv_denot]; dtac)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS | st_ok _ ?Ev ?ssx ?msv =>
pose proof (st_ok_pin_rege Ev ssx msv r e HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite Hr; cbn [sv_denot]; dtac)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS  end.
Lemma fl_FvX_aux : fl_fromX0 KS MT XN B CTX wfn ss_DIMS (INV_DIMSX MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_DIMSi (INV_DIMSiX MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_Fv (INV_FvX MT B).
Proof.
intros RD RDi. fl_preludeX.
pose proof HINV as (((Hk3 & Eab3 & (gen & E621 & Rgen & Hgen2) & E625 & (fb & Hfb & EB)) & E621X & XF2 & MLE0) & XFAST).
cbn [c_i c_s] in Hfb.
pose proof HCUR as (XCa & _ & _ & XCn & XCct & _ & _ & XCimg & XClen & XClp).
rewrite Hfb in HBEF. destruct bef as [bq|]; [|destruct HBEF].
pose proof HBEF as (XBa & _ & _ & XBn & XBct & _ & _ & XBimg & XBlen & XBlp).
specialize (XFAST bq eq_refl). unfold xG in XFAST. cbn [c_s x_GPAL x_cur] in XFAST.
pose proof (EB 0%nat _ eq_refl) as E651. pose proof (EB 1%nat _ eq_refl) as E652. pose proof (EB 2%nat _ eq_refl) as E653.
pose proof (EB 3%nat _ eq_refl) as E654. pose proof (EB 4%nat _ eq_refl) as E655. pose proof (EB 5%nat _ eq_refl) as E656.
pose proof (EB 6%nat _ eq_refl) as E657. pose proof (EB 7%nat _ eq_refl) as E658. pose proof (EB 8%nat _ eq_refl) as E659.
cbn [Nat.add] in E651, E652, E653, E654, E655, E656, E657, E658, E659.
rewrite Hfb in E12. cbn [frame_ptr] in E12.
destruct (fl_bef_in s i fb Hi Hlen3 Hfb) as [Hfbe Hfbi].
destruct (fl_bef_blocks B ly S g s N rest fb HPerm Hfbi) as (Hbef_in & Hbimg_in & Hblpal).
destruct (fl_bef_blocks B ly S g s N rest f HPerm Hfi) as (_ & _ & Hclpal).
pose proof (Hfwf f Hfi) as [Hfgp _]. pose proof (Hfwf fb Hfbi) as [Hbgp _].
destruct (al_blocks _ _ LAWS ly S W mem md (fr_ptr fb) FRAME_SIZE HAR Hbef_in) as (Hb16 & Hb4096 & Hbceil & [Hbh1 Hbh2] & _ & _). change (req_size FRAME_SIZE) with 40 in Hbceil, Hbh2.
destruct (al_blocks _ _ LAWS ly S W mem md (fr_img fb) N HAR Hbimg_in) as (Hbi16 & Hbi4096 & Hbiceil & [Hbih1 Hbih2] & _ & _).
assert (Hsub3 : forall x, In x (ablocks B ly S) -> In x (ablocks B ly3 S3)) by (intros x Hx; rewrite Eab3; exact Hx).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hing).
assert (Hcur3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hcur_in).
assert (Himg3 : In (fr_img f, N) (ablocks B ly3 S3)) by (apply Hsub3; exact Himg_in).
assert (Hbef3 : In (fr_ptr fb, FRAME_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hbef_in).
assert (Hbimg3 : In (fr_img fb, N) (ablocks B ly3 S3)) by (apply Hsub3; exact Hbimg_in).
assert (Hpf3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (apply Hsub3; exact Hpf_in).
fl_blocks3X Hing3 Hcur3 Hpf3. fold F in HdFG, HdFC.
pose proof (fl_bef_sep B LAWS ly S W mem md g s N rest i f fb HAR HPerm Hf Hfbe Hi) as HdCB.
pose proof (fl_img_sep B LAWS ly S W mem md g s N rest i (i - 1)%nat f fb HAR HPerm Hf Hfbe ltac:(clear - Hi Hob241 Hob242 Hob253 Huar; lia)) as HdII.
assert (Hrq : req_size N = N) by (unfold req_size; destruct (Z.eqb_spec N 0); [exfalso; clear - e HN HW1 HH1 Hob241 Hob242 Hob253 Huar; nia | reflexivity]). rewrite Hrq in HdII.
assert (HN1 : 1 <= N) by (clear - HN HW1 HH1 Hob241 Hob242 Hob253 Huar; nia).
pose proof (sep_blocks SEGS _ LAWS ly S _ _ _ (cg_raw s) RAW_SIZE g CGIF_SIZE HAR Hraw_in Hing ltac:(unfold RAW_SIZE, CGIF_SIZE; intros X; injection X; lia)) as HdRG.
unfold zdisjoint in HdRG; cbn [fst snd] in HdRG; change (req_size RAW_SIZE) with 48 in HdRG; change (req_size CGIF_SIZE) with 96 in HdRG.
pose proof (sep_blocks SEGS _ LAWS ly S _ _ _ (cg_raw s) RAW_SIZE (fr_ptr fb) FRAME_SIZE HAR Hraw_in Hbef_in ltac:(unfold RAW_SIZE, FRAME_SIZE; intros X; injection X; lia)) as HdRB.
unfold zdisjoint in HdRB; cbn [fst snd] in HdRB; change (req_size RAW_SIZE) with 48 in HdRB; change (req_size FRAME_SIZE) with 40 in HdRB.
pose proof (sep_blocks SEGS _ LAWS ly S _ _ _ (cg_raw s) RAW_SIZE (fr_ptr f) FRAME_SIZE HAR Hraw_in Hcur_in ltac:(unfold RAW_SIZE, FRAME_SIZE; intros X; injection X; lia)) as HdRC.
unfold zdisjoint in HdRC; cbn [fst snd] in HdRC; change (req_size RAW_SIZE) with 48 in HdRC; change (req_size FRAME_SIZE) with 40 in HdRC.
relowF HS AG E10 E11 E32 E10n E11n E32n.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => assert (E12n : ew Ev 12 = Z_to_bv 64 (fr_ptr fb)) by (rewrite (AG 12%nat) by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); exact E12) | st_ok _ ?Ev _ _ => assert (E12n : ew Ev 12 = Z_to_bv 64 (fr_ptr fb)) by (rewrite (AG 12%nat) by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); exact E12)  end.
reshok HS.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ3 SHOK FLBspan 0x1d68.
all: try (oblG HJ3 E12n E32n Hbef3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
upd_aboveF HUP HFr AG ltac:(fun Hb Hrg => clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi Hob241 Hob242 Hob253 Huar; lia). clear_frames.
lazymatch type of AG with forall n, _ -> ew ?Ebase n = _ => assert (Usp3 : bv_unsigned (ew Ebase 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp) end.
prreg HS (@BV 5 1 I) Rra. prreg HS (@BV 5 2 I) Rsp. prreg HS (@BV 5 3 I) Rgp. prreg HS (@BV 5 4 I) Rtp. prreg HS (@BV 5 8 I) Rs0.
prreg HS (@BV 5 9 I) Rr9. prreg HS (@BV 5 18 I) Rr18. prreg HS (@BV 5 20 I) Rr20. prreg HS (@BV 5 21 I) Rr21. prreg HS (@BV 5 22 I) Rr22.
prreg HS (@BV 5 23 I) Rr23. prreg HS (@BV 5 25 I) Rr25. prreg HS (@BV 5 26 I) Rr26. prreg HS (@BV 5 27 I) Rr27.
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E60; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47 Hob241 Hob242 Hob253 Huar; lia);
assert (Es0X : s0Z rg = spZ regs) by (unfold s0Z; rewrite Rs0, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact Usp3) end.
assert (Qtop64 : ly_top ly <= 2 ^ 64) by (clear - Htop2 H47 Htop Hshi Hob241 Hob242 Hob253 Huar; lia).
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D; rewrite Hal16, Z.add_0_r in D; rewrite D; replace (16 * (spZ regs / 16)) with ((2 * (spZ regs / 16)) * 8) by lia; apply Z_mod_mult).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat (@BV 5 1 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat (@BV 5 8 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly3 (aview SEGS (w_H W3) (ms_mem msX)) sp1 (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ sp1 Hch Qtop64 HUP
(rdword_of_val_mem SEGS _ _ _ _ Vra Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs0 Qs0) Hra4 ltac:(clear - Hceil Hslo Hstk0 FFS Hob241 Hob242 Hob253 Huar; lia) Qal8
ltac:(clear - Htop32 Hob241 Hob242 Hob253 Huar; lia) ltac:(clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia))
| ] | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_regionP) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat (@BV 5 1 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat (@BV 5 8 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly3 (aview SEGS (w_H W3) (ms_mem msX)) sp1 (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ sp1 Hch Qtop64 HUP
(rdword_of_val_mem SEGS _ _ _ _ Vra Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs0 Qs0) Hra4 ltac:(clear - Hceil Hslo Hstk0 FFS Hob241 Hob242 Hob253 Huar; lia) Qal8
ltac:(clear - Htop32 Hob241 Hob242 Hob253 Huar; lia) ltac:(clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia))
| ]  end.
assert (HF8c : 8 * (F / 8) <= F) by (apply Z.mul_div_le; clear; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
assert (F211 : ew Ex 652 = Z_to_bv 64 (fr_img fb)) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E652);
assert (F40 : ew Ex 40 = Z_to_bv 64 (cg_W s)) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E40);
assert (F41 : ew Ex 41 = Z_to_bv 64 (cg_H s)) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E41);
assert (F51 : ew Ex 51 = Z_to_bv 64 (fr_img f)) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E51);
assert (F75 : ew Ex 516 = Z_to_bv 64 F) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact RF);
let rs := eval vm_compute in (ss_mem ssx) in
let il := idx_of_base rs 60%nat in let il := eval vm_compute in il in
let rl := eval vm_compute in (nth il rs got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) il rl HS ltac:(vm_compute; reflexivity)) as HRloc; cbn [ms_mem restrict] in HRloc;
lazymatch type of HRloc with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
let slot off e v dtac rtac Hn :=
pose proof (field_of_region Ex _ 60 sp1 cs lo hi wlo whi off 8%N e v HRloc
ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E60; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47 Hob241 Hob242 Hob253 Huar; lia)
ltac:(cbn; tauto) ltac:(dtac) ltac:(rtac) ltac:(cbn; lia)) as Hn in
slot 200 (SOff 40 0) (cg_W s) ltac:(cbn [sv_denot]; rewrite F40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - R7 Hob241 Hob242 Hob253 Huar; lia) V200;
slot 208 (SOff 41 0) (cg_H s) ltac:(cbn [sv_denot]; rewrite F41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - R8 Hob241 Hob242 Hob253 Huar; lia) V208;
slot 224 (SOff 51 0) (fr_img f) ltac:(cbn [sv_denot]; rewrite F51, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - Hi4096 Hiceil C1 Hrq HN1 Hob241 Hob242 Hob253 Huar; lia) V224;
slot 240 (SOff 32 0) SB ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E32n, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(unfold SB; cbn; lia) V240;
slot 248 (SOff 12 0) (fr_ptr fb) ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E12n, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - Hbh1 Hbh2 C1 C3 Hob241 Hob242 Hob253 Huar; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia) V248;
slot 144 (SOff 516 128) (F + 128) ltac:(cbn [sv_denot]; rewrite F75, unsigned_lit_small by (clear - HF4096 HFceil C1 Hob241 Hob242 Hob253 Huar; lia); reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - HF4096 HFceil C1 Hob241 Hob242 Hob253 Huar; lia) V144;
slot 176 (SOff 516 112) (F + 112) ltac:(cbn [sv_denot]; rewrite F75, unsigned_lit_small by (clear - HF4096 HFceil C1 Hob241 Hob242 Hob253 Huar; lia); reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - HF4096 HFceil C1 Hob241 Hob242 Hob253 Huar; lia) V176;
slot 96 (SOff 516 0) F ltac:(cbn [sv_denot]; rewrite F75, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - HF4096 HFceil C1 Hob241 Hob242 Hob253 Huar; lia) V96 end;
pose proof HRloc as HR70 | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
assert (F211 : ew Ex 652 = Z_to_bv 64 (fr_img fb)) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E652);
assert (F40 : ew Ex 40 = Z_to_bv 64 (cg_W s)) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E40);
assert (F41 : ew Ex 41 = Z_to_bv 64 (cg_H s)) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E41);
assert (F51 : ew Ex 51 = Z_to_bv 64 (fr_img f)) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E51);
assert (F75 : ew Ex 516 = Z_to_bv 64 F) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact RF);
let rs := eval vm_compute in (ss_mem ssx) in
let il := idx_of_base rs 60%nat in let il := eval vm_compute in il in
let rl := eval vm_compute in (nth il rs got_regionP) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) il rl HS ltac:(vm_compute; reflexivity)) as HRloc; cbn [ms_mem restrict] in HRloc;
lazymatch type of HRloc with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
let slot off e v dtac rtac Hn :=
pose proof (field_of_region Ex _ 60 sp1 cs lo hi wlo whi off 8%N e v HRloc
ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E60; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47 Hob241 Hob242 Hob253 Huar; lia)
ltac:(cbn; tauto) ltac:(dtac) ltac:(rtac) ltac:(cbn; lia)) as Hn in
slot 200 (SOff 40 0) (cg_W s) ltac:(cbn [sv_denot]; rewrite F40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - R7 Hob241 Hob242 Hob253 Huar; lia) V200;
slot 208 (SOff 41 0) (cg_H s) ltac:(cbn [sv_denot]; rewrite F41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - R8 Hob241 Hob242 Hob253 Huar; lia) V208;
slot 224 (SOff 51 0) (fr_img f) ltac:(cbn [sv_denot]; rewrite F51, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - Hi4096 Hiceil C1 Hrq HN1 Hob241 Hob242 Hob253 Huar; lia) V224;
slot 240 (SOff 32 0) SB ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E32n, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(unfold SB; cbn; lia) V240;
slot 248 (SOff 12 0) (fr_ptr fb) ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E12n, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - Hbh1 Hbh2 C1 C3 Hob241 Hob242 Hob253 Huar; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia) V248;
slot 144 (SOff 516 128) (F + 128) ltac:(cbn [sv_denot]; rewrite F75, unsigned_lit_small by (clear - HF4096 HFceil C1 Hob241 Hob242 Hob253 Huar; lia); reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - HF4096 HFceil C1 Hob241 Hob242 Hob253 Huar; lia) V144;
slot 176 (SOff 516 112) (F + 112) ltac:(cbn [sv_denot]; rewrite F75, unsigned_lit_small by (clear - HF4096 HFceil C1 Hob241 Hob242 Hob253 Huar; lia); reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - HF4096 HFceil C1 Hob241 Hob242 Hob253 Huar; lia) V176;
slot 96 (SOff 516 0) F ltac:(cbn [sv_denot]; rewrite F75, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - HF4096 HFceil C1 Hob241 Hob242 Hob253 Huar; lia) V96 end;
pose proof HRloc as HR70  end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V200, V208, V224, V240, V248, V144, V176, V96.
assert (Og3 : obj_at SEGS (mrestrict (w_H W3) (ms_mem ms)) g LAY_CGIF (xcgif_vals path hw pf s)).
{ lazymatch goal with |- obj_at _ (mrestrict _ (ms_mem ?msX)) _ _ _ =>
eapply (aj_obj_kept B); [exact HJ3 | exact Hing | exact Hing3 | exact Og | vm_compute; reflexivity |] end.
change (req_size CGIF_SIZE) with 96. intros j Hj (rr & Hrr & Ha). cbn [In] in Hrr.
unbox. destruct Hrr as [<- | []]; cbn [fst snd] in Ha; clear - Ha Hj HdGC Hob241 Hob242 Hob253 Huar; lia. }
assert (Ob3 : obj_at SEGS (mrestrict (w_H W3) (ms_mem ms)) (fr_ptr fb) LAY_Frame (frame_vals fb)).
{ eapply (aj_obj_kept B); [exact HJ3 | exact Hbef_in | exact Hbef3 | exact (Ofr fb Hfbi) | vm_compute; reflexivity |].
change (req_size FRAME_SIZE) with 40. intros j Hj. apply fl_fp0_out_frame; [clear - HdCB Hob241 Hob242 Hob253 Huar; lia | exact Hj]. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE (proj1 HJ3) Hcur3) as (_ & _ & _ & _ & HcpresX & _). change (req_size FRAME_SIZE) with 40 in HcpresX.
destruct (obj_at_hole4 (mrestrict (w_H W) mem) (mrestrict (w_H W3) (ms_mem ms)) (fr_ptr f) LAY_Frame 40 (frame_vals f) 3 20
Oc ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity) ltac:(cbn; lia)
ltac:(intros j Hj Hnj; apply (mbyte_of_aview SEGS); pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _);
apply (F2 (fr_ptr f) FRAME_SIZE j Hcur_in Hcur3 ltac:(change (req_size FRAME_SIZE) with 40; exact Hj));
intros (rr & Hrr & Ha); cbn [In] in Hrr; destruct Hrr as [<- | []]; cbn [fst snd] in Ha; clear - Ha Hj Hnj Hob241 Hob242 Hob253 Huar; lia)
ltac:(intros j Hj; destruct (proj1 (HcpresX (fr_ptr f + 20 + j) ltac:(clear - Hj Hob241 Hob242 Hob253 Huar; lia))) as [Hh [b Hb]];
unfold mbyte, mrestrict; cbn [ms_mem]; rewrite Hh; cbn; rewrite Hb; eexists; reflexivity))
as (genC & HgenC & Oc3).
unbox.
assert (HSpresX : forall a, spZ regs - TFLUSH_STK <= a < spZ regs -> apresent (w_H W3) (ms_mem ms) a) by (pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSp & _); exact HSp).
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
assert (HC : wctx B W3 (ms_regs msX) (ms_mem msX) mdX (spZ regs) sp1 [(fr_ptr f + 20, fr_ptr f + 24)] ly S W mem md ly3 S3 k fpos
((spZ regs, raZ regs, s0Z regs) :: ch) (fr_img f) (fr_img fb) N g (fr_ptr f) (fr_ptr fb)
(xcgif_vals path hw pf s) (list_set (frame_vals f) 3 genC) (frame_vals fb)
(cg_pal s) (cg_ngp s) (fr_lpal f) (fr_attr f) (fr_nlp f) (fr_ctidx f) (fr_lpal fb) (fr_attr fb) (fr_nlp fb) (fr_ctidx fb)) end.
{ split; [exact HJ3|]. split; [exact Himg3|]. split; [exact Hbimg3|].
split; [clear - HN HW1 HH1 R7 R8 Hob241 Hob242 Hob253 Huar; nia|]. split; [clear - HdII Hob241 Hob242 Hob253 Huar; lia|].
split; [exact Hing3|]. split; [exact Hcur3|]. split; [exact Hbef3|]. split; [clear - HdCB Hob241 Hob242 Hob253 Huar; lia|].
split; [exact Og3|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact Oc3|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact Ob3|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [intros Ha1; exists (3 * fr_nlp f); split; [apply Hsub3; apply Hclpal; exact Ha1 | clear; lia]|].
split; [intros Ha1; exists (3 * fr_nlp fb); split; [apply Hsub3; apply Hblpal; exact Ha1 | clear; lia]|].
split; [intros Hor; exists (3 * cg_ngp s); split; [apply Hsub3; apply (w_gpal_block B ly S g s N rest HPerm); destruct Hor as [H0 | H0]; [exact (Hfgp H0) | exact (Hbgp H0)] | clear; lia]|].
split; [exact EspX|]. split; [exact Hsp1|]. split; [exact Hsp1al16|].
split; [rewrite Rr9, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E60|].
split; [rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 3%nat) by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite (EE 3%nat (@BV 5 3 I) eq_refl); exact Hgp|].
split; [rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 4%nat) by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite (EE 4%nat (@BV 5 4 I) eq_refl); exact Htp|].
split; [rewrite Es0X; exact Hch1|]. split; [exact Es0X|].
split; [exact V240 | exact V248]. }
assert (HGEO : 1 <= cg_W s <= 65535 /\ 1 <= cg_H s <= 65535 /\ N = cg_W s * cg_H s /\
val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (sp1 + 200) 8 (cg_W s) /\ val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (sp1 + 208) 8 (cg_H s)).
{ split; [clear - HW1 R7 Hob241 Hob242 Hob253 Huar; lia|]. split; [clear - HH1 R8 Hob241 Hob242 Hob253 Huar; lia|]. split; [exact HN|]. split; [exact V200 | exact V208]. }
assert (HRES : 0 <= F + 128 < 2 ^ 64 /\ 0 <= F + 112 < 2 ^ 64 /\
val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (sp1 + 144) 8 (F + 128) /\ val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (sp1 + 176) 8 (F + 112)).
{ split; [clear - HF4096 HFceil C1 Hob241 Hob242 Hob253 Huar; lia|]. split; [clear - HF4096 HFceil C1 Hob241 Hob242 Hob253 Huar; lia|]. split; [exact V144 | exact V176]. }
assert (HSAV2 : 0 <= F < 2 ^ 64 /\ val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (sp1 + 96) 8 F).
{ split; [clear - HF4096 HFceil C1 Hob241 Hob242 Hob253 Huar; lia | exact V96]. }
destruct (cur_obj_tail g s N rest i f Hf) as (ctail & HPct & Tgp & Timg & Tlp & Tfr).
pose proof (Permutation_trans HPerm HPct) as HPc.
assert (XJ : forall p sz L, In (p, sz) (ablocks B ly S) -> In (p, sz) ctail -> Z.of_nat (length L) <= req_size sz ->
garr8 SEGS (mrestrict (w_H W) mem) p L -> garr8 SEGS (mrestrict (w_H W3) (ms_mem ms)) p L).
{ intros p sz L Hin Hct HL HG.
eapply (garr8_journal_block_x SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p sz p L HJ3);
[ exact Hin | apply Hsub3; exact Hin | clear; lia | clear - HL; lia
| intros a Ha; apply (fp0_off_tail B LAWS ly S W mem md f ctail p sz HAR HPc Hct); clear - Ha HL; lia
| exact HG ]. }
assert (XCIMG : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms)) (fr_img f) (YO07.f_img cur)) by (apply (XJ _ N _ Himg_in Timg); [rewrite XClen, Hrq; clear; lia | exact XCimg]).
assert (XBIMG : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms)) (fr_img fb) (YO07.f_img bq))
by (apply (XJ _ N _ Hbimg_in); [apply (Tfr (i - 1)%nat fb ltac:(clear - Hi; lia) Hfbe); right; left; reflexivity | rewrite XBlen, Hrq; clear; lia | exact XBimg]).
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply (fl_search_fastX B LAWS ABCMP W3 (ms_regs msX) (ms_mem msX) mdX (spZ regs) sp1 _ ly S W mem md ly3 S3 k fpos _ (fr_img f) (fr_img fb) N g (fr_ptr f) (fr_ptr fb)
_ _ _ _ _ _ _ _ _ _ _ _ _ (cg_W s) (cg_H s) (F + 128) (F + 112) F F HC HGEO HRES V224 HSAV2 (ms_regs msX) (ms_mem msX) mdX) end;
[ exact HJ3
| apply (wkeptF_refl B); intros a Ha; apply HSpresX; clear - Ha Hsp1 FFS Hob241 Hob242 Hob253 Huar; change FBAND with 8192 in Ha; lia
| intros r Hr; reflexivity
| first [rewrite Rr21, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E10n | match goal with |- ?g => idtac "F-21" g end]
| first [rewrite Rr22, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E11n | match goal with |- ?g => idtac "F-22" g end]
| first [rewrite Rr23; first [exact F51 | rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E51] | match goal with |- ?g => idtac "F-23" g end]
| first [rewrite Rr26; first [exact F211 | rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E652] | match goal with |- ?g => idtac "F-26" g end]
| first [rewrite Rr18; first [exact F40 | rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E40] | match goal with |- ?g => idtac "F-18" g end]
| first [exact Rr27 | rewrite Rr27; reflexivity | match goal with |- ?g => idtac "F-27" g end]
| first [rewrite Rr20; first [exact F75 | rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact RF] | match goal with |- ?g => idtac "F-20" g end]
| first [rewrite Rr25; first [exact F211 | rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E652] | match goal with |- ?g => idtac "F-25" g end] ]. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & w5 & h5 & top5 & left5 & -> & HJ5 & WK5 & HK5 & H65 & H215 & H225 & H185 & H205 & H265 & H275 & H235 & V1605 & Hw1 & Hl0 & Hlw & Hh1 & Ht0 & Hth & XSC & Hcase).
assert (HSpres5 : forall a, spZ regs - TFLUSH_STK <= a < spZ regs -> apresent (w_H W3) mem5 a) by (pose proof HJ5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSp & _); exact HSp).
pose proof (proj1 HJ5) as HAR5.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR5 Hfin3) as (_ & _ & HFpres5 & HFSpres5).
change (fs_frame_bytes 2) with 256 in HFpres5, HFSpres5. change (256 / 8) with 32 in HFSpres5. rewrite !EFA3 in HFpres5, HFSpres5. fold F in HFpres5, HFSpres5.
clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3.
assert (Hb70 : bv_unsigned (ew ltac:(lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => exact Ex | st_ok _ ?Ex _ _ => exact Ex  end) 60) = sp1)
by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E60; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47 Hob241 Hob242 Hob253 Huar; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let cs23 := eval vm_compute in (YP09.r_chunks (nth 3 (ss_mem ss_DIMS) got_regionP)) in
assert (HR70' : region_ok SEGS Ex (mrestrict (w_H W3) (ms_mem msX)) (YP09.mkRegion (Some 60%nat) 0 280 0 280 cs23))
by (eapply region_ok_sub; [| clear; cbn; lia | exact HR70]; subregion_tac) | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let cs23 := eval vm_compute in (YP09.r_chunks (nth 3 (ss_mem ss_DIMS) got_regionP)) in
assert (HR70' : region_ok SEGS Ex (mrestrict (w_H W3) (ms_mem msX)) (YP09.mkRegion (Some 60%nat) 0 280 0 280 cs23))
by (eapply region_ok_sub; [| clear; cbn; lia | exact HR70]; subregion_tac)  end.
clear HR70.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msX) =>
let rs' := eval vm_compute in (w_trim_base (ss_mem ssx) 60 232 280) in
pose proof (st_ok_pi_submem Ev ssx (restrict (w_H W3) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ev ?ssx (restrict _ ?msX) =>
let rs' := eval vm_compute in (w_trim_base (ss_mem ssx) 60 232 280) in
pose proof (st_ok_submem SEGS Ev ssx (restrict (w_H W3) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS  end.
Ltac ws_reseat HS HK5 regs5 mem5 :=
let HK5' := fresh "HK5'" in let HS2 := fresh "HS2" in let HQ := fresh "HQ" in
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict (w_H ?Wx) ?msX) =>
assert (HK5' : forall r : bv 5, reg_in r WF_CLOB = false -> getr regs5 r = getr (ms_regs msX) r)
by (let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; destruct (wf_clob_cases r Hr) as [-> | Hr']; [reflexivity | exact (HK5 r Hr')]);
cbn [ms_regs restrict mkst] in HK5';
let kk := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ssx) in
jafter_stretch_keep_hi HS kk regs5 (mrestrict (w_H Wx) mem5) WF_CLOB 0x1f8c [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat HS2;
lazymatch type of HS2 with _ -> ?Q -> _ =>
assert (HQ : Q);
[ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil
| specialize (HS2 HK5' HQ); clear HQ ] end | st_ok _ ?Ev ?ssx (restrict (w_H ?Wx) ?msX) =>
assert (HK5' : forall r : bv 5, reg_in r WF_CLOB = false -> getr regs5 r = getr (ms_regs msX) r)
by (let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; destruct (wf_clob_cases r Hr) as [-> | Hr']; [reflexivity | exact (HK5 r Hr')]);
cbn [ms_regs restrict mkst] in HK5';
let kk := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ssx) in
jafter_stretch_keep_hi HS kk regs5 (mrestrict (w_H Wx) mem5) WF_CLOB 0x1f8c [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat HS2;
lazymatch type of HS2 with _ -> ?Q -> _ =>
assert (HQ : Q);
[ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil
| specialize (HS2 HK5' HQ); clear HQ ] end  end.
pose proof WK5 as [K5 X5]. aconstsF HJ5 Kgot5 Kcell5 Kguar5 Kuar5.
ws_reseat HS HK5 regs5 mem5.
all: try (idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 529%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj SEGS _); [exact K5 | evalE AG | exact Hfin3
| right; unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; unfold SB; clear; lia
| intros a Ha Hn; exact Hn
| intros a Ha; exfalso; clear - Ha Hob241 Hob242 Hob253 Huar; unfold SB in *; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj SEGS _); [exact K5 | evalE AG | exact Hfin3
| left; rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia
| intros a Ha Hn; exact Hn
| intros a Ha; apply (proj1 (HFpres5 a ltac:(clear - Ha Hob241 Hob242 Hob253 Huar; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 60%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj SEGS _); [exact K5 | exact HJ5 | evalE AG | clear; lia | rewrite FFS; clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia | clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj SEGS _); [exact K5 | exact HJ5 | evalE AG | change FBAND with 8192; clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 241%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 0) (pa_val (A_OBJ 0)) 8 (pa_val (A_OBJ 12)));
[exact (H (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kgot3 | exact Kgot5 | lia] end
| lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 253%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 12) (pa_val (A_OBJ 12)) 8 SHADOW_OFF);
[exact (H (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kcell3 | exact Kcell5 | lia] end
| lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 242%nat) _ _ _ _ _) =>
let H := rnHEI Ex in let Bv := rnB in apply (region_kept_val_at Ex _ _ (A_OBJ 1) (pa_val (A_OBJ 1)) 8 (as_uar_cell Bv));
[exact (H (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kguar3 | exact Kguar5 | lia] end
| lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 59%nat) _ _ _ _ _) =>
let AGx := lazymatch goal with A : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => A end in
let Bv := rnB in apply (region_kept_val_at Ex _ _ 59%nat (as_uar_cell Bv) 4 1); [evalE AGx | exact Kuar3 | exact Kuar5 | lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj SEGS _); [exact K5 | evalE AG | exact Hing3 | clear; lia | change (req_size CGIF_SIZE) with 96; clear; lia | clear; lia
| intros a Ha Hn; exact Hn ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 12%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj SEGS _); [exact K5 | evalE AG | exact Hbef3 | clear; lia | change (req_size FRAME_SIZE) with 40; clear; lia | clear; lia
| intros a Ha Hn; exact Hn ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply (region_kept_block_ajw2 SEGS B LAWS); [exact K5 | exact HAR5 | exact Hcur3 | evalE AG | exact Hcur3 | clear; lia | change (req_size FRAME_SIZE) with 40; clear; lia | clear; lia | clear; lia
| intros a Ha Hn; exact Hn ] end
| match goal with |- region_kept _ _ _ _ ?r => idtac "KEPTFAIL" r end ]).
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HR70' with region_ok _ _ _ (YP09.mkRegion _ _ _ _ _ ?cs23) =>
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msv =>
lazymatch Ev with havoc _ ?KK _ =>
let rs := eval vm_compute in (ss_mem ssx) in
lazymatch rs with ?r0 :: ?r1 :: ?r2 :: ?rt :: ?l2 =>
pose proof (w_st_ok_replace_region Ev ssx msv [r0; r1; r2] rt (YP09.mkRegion (Some 60%nat) 0 280 0 280 cs23) l2 HS eq_refl ltac:(vm_compute; reflexivity)
ltac:(cbn [ms_mem restrict mkst];
eapply (region_ok_transport_chunksK KK _ Ev _ _ 60 _ 0 280 0 280 cs23 HR70' Hb70);
[ apply (env_agree_havoc_ge KK KK _ _ _ ltac:(clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia) (env_agree_refl _ _))
| apply (proj1 (Nat.ltb_lt _ _)); vm_compute; reflexivity
| vm_compute; reflexivity
| let c := fresh "c" in let Hc := fresh "Hc" in let a := fresh "a" in let Ha := fresh "Ha" in let Hcf := fresh "Hcf" in
intros c Hc a Ha;
pose proof (proj1 (forallb_forall _ _) (ltac:(vm_compute; reflexivity) : forallb chunk_scratch_freeb cs23 = true) c Hc) as Hcf;
unfold chunk_scratch_freeb in Hcf;
destruct (off_scratch_free_sound _ _ _ Hcf a Ha) as [[Hlt Hns] | Hge];
[ apply (mbyte_of_aview SEGS); apply X5; [exact Hlt | exact Hns]
| apply (mbyte_of_aview SEGS); pose proof K5 as (K51 & _); apply K51;
[ clear - Hge Hsp1 Hceil FFS Hshi H47 Hstk0 Hslo C1 Hob241 Hob242 Hob253 Huar; lia
| change FBAND with 8192; clear - Hge Hob241 Hob242 Hob253 Huar; lia ] ]
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply (apresent_writable SEGS); apply HSpres5;
rewrite FFS; clear - Ha Hsp1 Hob241 Hob242 Hob253 Huar; lia ])
ltac:(cbn [all_disjoint app]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
lazymatch goal with AG : forall n, (n < 33)%nat -> _ |- _ => evalE AG end;
change (fs_frame_bytes 2) with 256; change (fs_frame_bytes 2 / 8) with 32;
unfold CGIF_SIZE, FRAME_SIZE, SB;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C2 C3 HF4096 HFceil HFhigh HF8lo HF8hi HF8c Hgh Hgceil Hcrh Hcceil Hb4096 Hbceil Hbh1 Hbh2 Hob241 Hob242 Hob253 Huar;
ceil; unfold ASAN_CEIL, kHighMemBeg, kLowShadowBeg, kHighMemBeg in *; repeat split; first [zone_lia | match goal with |- ?g => idtac "DISJ-FAIL" g end])) as HS3;
clear HS; rename HS3 into HS end end | st_ok _ ?Ev ?ssx ?msv =>
lazymatch Ev with havoc _ ?KK _ =>
let rs := eval vm_compute in (ss_mem ssx) in
lazymatch rs with ?r0 :: ?r1 :: ?r2 :: ?rt :: ?l2 =>
pose proof (w_st_ok_replace_region Ev ssx msv [r0; r1; r2] rt (YP09.mkRegion (Some 60%nat) 0 280 0 280 cs23) l2 HS eq_refl ltac:(vm_compute; reflexivity)
ltac:(cbn [ms_mem restrict mkst];
eapply (region_ok_transport_chunksK KK _ Ev _ _ 60 _ 0 280 0 280 cs23 HR70' Hb70);
[ apply (env_agree_havoc_ge KK KK _ _ _ ltac:(clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia) (env_agree_refl _ _))
| apply (proj1 (Nat.ltb_lt _ _)); vm_compute; reflexivity
| vm_compute; reflexivity
| let c := fresh "c" in let Hc := fresh "Hc" in let a := fresh "a" in let Ha := fresh "Ha" in let Hcf := fresh "Hcf" in
intros c Hc a Ha;
pose proof (proj1 (forallb_forall _ _) (ltac:(vm_compute; reflexivity) : forallb chunk_scratch_freeb cs23 = true) c Hc) as Hcf;
unfold chunk_scratch_freeb in Hcf;
destruct (off_scratch_free_sound _ _ _ Hcf a Ha) as [[Hlt Hns] | Hge];
[ apply (mbyte_of_aview SEGS); apply X5; [exact Hlt | exact Hns]
| apply (mbyte_of_aview SEGS); pose proof K5 as (K51 & _); apply K51;
[ clear - Hge Hsp1 Hceil FFS Hshi H47 Hstk0 Hslo C1 Hob241 Hob242 Hob253 Huar; lia
| change FBAND with 8192; clear - Hge Hob241 Hob242 Hob253 Huar; lia ] ]
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply (apresent_writable SEGS); apply HSpres5;
rewrite FFS; clear - Ha Hsp1 Hob241 Hob242 Hob253 Huar; lia ])
ltac:(cbn [all_disjoint app]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
lazymatch goal with AG : forall n, (n < 33)%nat -> _ |- _ => evalE AG end;
change (fs_frame_bytes 2) with 256; change (fs_frame_bytes 2 / 8) with 32;
unfold CGIF_SIZE, FRAME_SIZE, SB;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C2 C3 HF4096 HFceil HFhigh HF8lo HF8hi HF8c Hgh Hgceil Hcrh Hcceil Hb4096 Hbceil Hbh1 Hbh2 Hob241 Hob242 Hob253 Huar;
ceil; unfold ASAN_CEIL, kHighMemBeg, kLowShadowBeg, kHighMemBeg in *; repeat split; first [zone_lia | match goal with |- ?g => idtac "DISJ-FAIL" g end])) as HS3;
clear HS; rename HS3 into HS end end  end end.
norm_ss HS.
rebaseE HS AG HEv. clear HEv.
ws_pin HS (@BV 5 6 I) (SOff 32 0) H65 ltac:(rewrite (AG 32%nat) by (clear; lia); rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ws_pin HS (@BV 5 21 I) (SOff 10 0) H215 ltac:(rewrite (AG 10%nat) by (clear; lia); rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ws_pin HS (@BV 5 22 I) (SOff 11 0) H225 ltac:(rewrite (AG 11%nat) by (clear; lia); rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ws_pin HS (@BV 5 18 I) (SOff 516 0) H185 ltac:(rewrite RF, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ws_pin HS (@BV 5 20 I) (SOff 516 0) H205 ltac:(rewrite RF, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
destruct Hcase as [(H105 & H115) | (H105 & H115 & Edum & XN2)].
- ws_pin HS (@BV 5 10 I) (SOff 516 112) H105 ltac:(rewrite RF, unsigned_lit_small by (clear - HF4096 HFceil C1 Hob241 Hob242 Hob253 Huar; lia); reflexivity).
ws_pin HS (@BV 5 11 I) (SOff 516 128) H115 ltac:(rewrite RF, unsigned_lit_small by (clear - HF4096 HFceil C1 Hob241 Hob242 Hob253 Huar; lia); reflexivity).
lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ =>
ra_join HS ss_DIMS 861%nat fl_dims_deads_bv ltac:(idtac; ra_join_val HS 861%nat 0%nat H265 E861; ra_join_val HS 861%nat 1%nat H275 E862; ra_join_val HS 861%nat 2%nat H235 E863);
fl_handX RD HS end.
split; [exact Hk3|]. split; [exact Eab3|].
split; [exists gen; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption|].
split; [exists fb; apply fl_bef_havoc; [clear; lia|]; split; [exact Hfb|]; cbn [c_i c_s]; bef_EB|].
split; [| split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E621X | split; [exact XF2 | exact MLE0]]].
exists w5, h5, top5, left5. cbn [c_s].
split; [exact E861|]. split; [cbn [c_sp1 ms_mem]; exact V1605|]. split; [exact E862|]. split; [exact E863|].
do 6 (split; [clear - Hw1 Hl0 Hlw Hh1 Ht0 Hth; lia|]).
unfold xdims, xG. cbn [c_s x_GPAL x_cur x_bef]. unfold YI0f.fl_dims.
unfold xgen3, xG in XF2. cbn [c_s x_GPAL x_cur x_bef] in XF2. rewrite XF2.
unfold wfc_scan in XSC.
destruct XSC as [(bot & right & c0 & Ew & Eh & Y1 & Y2 & Y3 & Y4 & Y5 & XT1 & XF1 & XT2 & XF2b & XT3 & XF3 & XT4 & XF4) | (Edum & XNall)].
+ rewrite (wf_diff_area W3 _ (fr_img f) (fr_img fb) (gcfg_of s GPAL) cur bq N XCIMG XClen XBIMG XBlen
(cg_W s) (cg_H s) HW1 HH1 eq_refl HN XFAST top5 bot left5 right c0 Y1 Y2 Y3 Y4 Y5 XT1 XF1 XT2 XF2b XT3 XF3 XT4 XF4).
rewrite Ew, Eh. reflexivity.
+ rewrite (wf_diff_none W3 _ (fr_img f) (fr_img fb) (gcfg_of s GPAL) cur bq N XCIMG XClen XBIMG XBlen
(cg_W s) (cg_H s) HW1 HH1 eq_refl HN XFAST XNall).
symmetry. exact Edum.
- injection Edum as Ew5 Eh5 Et5 El5. subst w5 h5 top5 left5.
ws_pin HS (@BV 5 10 I) (SOff 516 128) H105 ltac:(rewrite RF, unsigned_lit_small by (clear - HF4096 HFceil C1 Hob241 Hob242 Hob253 Huar; lia); reflexivity).
ws_pin HS (@BV 5 11 I) (SOff 516 112) H115 ltac:(rewrite RF, unsigned_lit_small by (clear - HF4096 HFceil C1 Hob241 Hob242 Hob253 Huar; lia); reflexivity).
ws_pin HS (@BV 5 26 I) (SLit 1) H265 ltac:(reflexivity).
ws_pin HS (@BV 5 27 I) (SLit 0) H275 ltac:(reflexivity).
ws_pin HS (@BV 5 23 I) (SLit 0) H235 ltac:(reflexivity).
lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ =>
ra_join HS ss_DIMSi 864%nat fl_dimsi_deads_bv ltac:(idtac); fl_handX RDi HS end.
split.
{ unfold INV_DIMSi. cbn [c_ly c_S c_W c_regs c_mem c_md c_ch c_g c_s c_N c_i c_f c_rest c_fpos c_sp1 c_wfn c_hw c_uar c_E0].
split; [exact Hk3|]. split; [exact Eab3|].
split; [exists gen; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption|].
split; [exists fb; apply fl_bef_havoc; [clear; lia|]; split; [exact Hfb|]; cbn [c_i c_s]; bef_EB|].
cbn [c_sp1 ms_mem]. exact V1605. }
split; [| split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E621X | split; [exact XF2 | exact MLE0]]].
unfold xdims, xG. cbn [c_s x_GPAL x_cur x_bef]. unfold YI0f.fl_dims.
unfold xgen3, xG in XF2. cbn [c_s x_GPAL x_cur x_bef] in XF2. rewrite XF2.
rewrite (wf_diff_none W3 _ (fr_img f) (fr_img fb) (gcfg_of s GPAL) cur bq N XCIMG XClen XBIMG XBlen
(cg_W s) (cg_H s) HW1 HH1 eq_refl HN XFAST); [reflexivity | intros p Hp; apply XN2; clear - Hp; lia].
Qed.
Lemma fl_FvX : fl_fromX0 KS MT XN B CTX wfn ss_DIMS (INV_DIMSX MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_DIMSi (INV_DIMSiX MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_Fv (INV_FvX MT B).
Proof. exact fl_FvX_aux. Qed.
End l.
End h.
End d.
