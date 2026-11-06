(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI04 YI06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI20 YI1k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC0x YC1b YC2u YC1z YC1y YC27 YC23 YC28 YC1w YC24 YC25 YC20 YC17 YC29 YC2b YC2h YC2i YC2j YC2k YC2l YC2m YC2n YC2c YC2d YC2e YC2f YC2g YC1u.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
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
lazymatch type of HS with st_ok _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
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
clear AG; rename AG2 into AG end end.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section h.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ABCMP : abcmp_realizes trasegs B A_bcmp_icpt.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Ltac bef_EB :=
let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in
intros j v Hj; do 9 (try (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn [Nat.add]; assumption|])); destruct j; discriminate Hj.
Ltac ws_pin HS r e Hr dtac :=
let HS3 := fresh "HS3" in
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msv =>
pose proof (st_ok_pin_rege Ev ssx msv r e HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite Hr; cbn [sv_denot]; dtac)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Lemma fl_Fv_aux : fl_from B ss_DIMS (INV_DIMS B) -> fl_from B ss_DIMSi (INV_DIMSi B) -> fl_from B ss_Fv (INV_DIFF B).
Proof.
intros RD RDi. fl_prelude.
pose proof HINV as (Hk3 & Eab3 & (gen & E180 & Rgen & Hgen2) & E184 & (fb & Hfb & EB)).
cbn [c_i c_s] in Hfb.
pose proof (EB 0%nat _ eq_refl) as E210. pose proof (EB 1%nat _ eq_refl) as E211. pose proof (EB 2%nat _ eq_refl) as E212.
pose proof (EB 3%nat _ eq_refl) as E213. pose proof (EB 4%nat _ eq_refl) as E214. pose proof (EB 5%nat _ eq_refl) as E215.
pose proof (EB 6%nat _ eq_refl) as E216. pose proof (EB 7%nat _ eq_refl) as E217. pose proof (EB 8%nat _ eq_refl) as E218.
cbn [Nat.add] in E210, E211, E212, E213, E214, E215, E216, E217, E218.
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
fl_blocks3 Hing3 Hcur3. fold F in HdFG, HdFC.
pose proof (fl_bef_sep B LAWS ly S W mem md g s N rest i f fb HAR HPerm Hf Hfbe Hi) as HdCB.
pose proof (fl_img_sep B LAWS ly S W mem md g s N rest i (i - 1)%nat f fb HAR HPerm Hf Hfbe ltac:(clear - Hi; lia)) as HdII.
assert (Hrq : req_size N = N) by (unfold req_size; destruct (Z.eqb_spec N 0); [exfalso; clear - e HN HW1 HH1; nia | reflexivity]). rewrite Hrq in HdII.
assert (HN1 : 1 <= N) by (clear - HN HW1 HH1; nia).
pose proof (sep_blocks trasegs _ LAWS ly S _ _ _ (cg_raw s) RAW_SIZE g CGIF_SIZE HAR Hraw_in Hing ltac:(unfold RAW_SIZE, CGIF_SIZE; intros X; injection X; lia)) as HdRG.
unfold zdisjoint in HdRG; cbn [fst snd] in HdRG; change (req_size RAW_SIZE) with 48 in HdRG; change (req_size CGIF_SIZE) with 96 in HdRG.
pose proof (sep_blocks trasegs _ LAWS ly S _ _ _ (cg_raw s) RAW_SIZE (fr_ptr fb) FRAME_SIZE HAR Hraw_in Hbef_in ltac:(unfold RAW_SIZE, FRAME_SIZE; intros X; injection X; lia)) as HdRB.
unfold zdisjoint in HdRB; cbn [fst snd] in HdRB; change (req_size RAW_SIZE) with 48 in HdRB; change (req_size FRAME_SIZE) with 40 in HdRB.
pose proof (sep_blocks trasegs _ LAWS ly S _ _ _ (cg_raw s) RAW_SIZE (fr_ptr f) FRAME_SIZE HAR Hraw_in Hcur_in ltac:(unfold RAW_SIZE, FRAME_SIZE; intros X; injection X; lia)) as HdRC.
unfold zdisjoint in HdRC; cbn [fst snd] in HdRC; change (req_size RAW_SIZE) with 48 in HdRC; change (req_size FRAME_SIZE) with 40 in HdRC.
relowF HS AG E10 E11 E32 E10n E11n E32n.
lazymatch type of HS with st_ok _ ?Ev _ _ => assert (E12n : ew Ev 12 = Z_to_bv 64 (fr_ptr fb)) by (rewrite (AG 12%nat) by (clear; lia); exact E12) end.
reshok HS.
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK FLBspan 0x87338.
all: try (oblG HJ3 E12n E32n Hbef3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
upd_aboveF HUP HFr AG ltac:(fun Hb Hrg => clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi; lia). clear_frames.
assert (Usp3 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp).
rreg HS (@BV 5 1 I) Rra. rreg HS (@BV 5 2 I) Rsp. rreg HS (@BV 5 3 I) Rgp. rreg HS (@BV 5 4 I) Rtp. rreg HS (@BV 5 8 I) Rs0.
rreg HS (@BV 5 9 I) Rr9. rreg HS (@BV 5 19 I) Rr19. rreg HS (@BV 5 20 I) Rr20. rreg HS (@BV 5 21 I) Rr21. rreg HS (@BV 5 22 I) Rr22.
rreg HS (@BV 5 23 I) Rr23. rreg HS (@BV 5 24 I) Rr24. rreg HS (@BV 5 25 I) Rr25. rreg HS (@BV 5 26 I) Rr26. rreg HS (@BV 5 18 I) Rr18. rreg HS (@BV 5 27 I) Rr27.
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia);
assert (Es0X : s0Z rg = spZ regs) by (unfold s0Z; rewrite Rs0, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact Usp3) end.
assert (Qtop64 : ly_top ly <= 2 ^ 64) by (clear - Htop2 H47 Htop Hshi; lia).
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D; rewrite Hal16, Z.add_0_r in D; rewrite D; replace (16 * (spZ regs / 16)) with ((2 * (spZ regs / 16)) * 8) by lia; apply Z_mod_mult).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat (@BV 5 1 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat (@BV 5 8 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly3 (aview trasegs (w_H W3) (ms_mem msX)) sp1 (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ sp1 Hch Qtop64 HUP
(rdword_of_val_mem trasegs _ _ _ _ Vra Qra) (rdword_of_val_mem trasegs _ _ _ _ Vs0 Qs0) Hra4 ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8
ltac:(clear - Htop32; lia) ltac:(clear - Hsp1; lia))
| ] end.
assert (HF8c : 8 * (F / 8) <= F) by (apply Z.mul_div_le; clear; lia).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
assert (F211 : ew Ex 211 = Z_to_bv 64 (fr_img fb)) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E211);
assert (F40 : ew Ex 40 = Z_to_bv 64 (cg_W s)) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E40);
assert (F41 : ew Ex 41 = Z_to_bv 64 (cg_H s)) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E41);
assert (F51 : ew Ex 51 = Z_to_bv 64 (fr_img f)) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E51);
assert (F75 : ew Ex 75 = Z_to_bv 64 F) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact RF);
let rs := eval vm_compute in (ss_mem ssx) in
let il := idx_of_base rs 70%nat in let il := eval vm_compute in il in
let rl := eval vm_compute in (nth il rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) il rl HS ltac:(vm_compute; reflexivity)) as HRloc; cbn [ms_mem restrict] in HRloc;
lazymatch type of HRloc with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
let slot off e v dtac rtac Hn :=
pose proof (field_of_region Ex _ 70 sp1 cs lo hi wlo whi off 8%N e v HRloc
ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia)
ltac:(cbn; tauto) ltac:(dtac) ltac:(rtac) ltac:(cbn; lia)) as Hn in
slot 200 (SOff 40 0) (cg_W s) ltac:(cbn [sv_denot]; rewrite F40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - R7; lia) V200;
slot 208 (SOff 41 0) (cg_H s) ltac:(cbn [sv_denot]; rewrite F41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - R8; lia) V112;
slot 224 (SOff 51 0) (fr_img f) ltac:(cbn [sv_denot]; rewrite F51, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - Hi4096 Hiceil C1 Hrq HN1; lia) V216;
slot 240 (SOff 32 0) SB ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E32n, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(unfold SB; cbn; lia) V240;
slot 248 (SOff 12 0) (fr_ptr fb) ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E12n, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - Hbh1 Hbh2 C1 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia) V248;
slot 144 (SOff 75 128) (F + 128) ltac:(cbn [sv_denot]; rewrite F75, unsigned_lit_small by (clear - HF4096 HFceil C1; lia); reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - HF4096 HFceil C1; lia) V176;
slot 176 (SOff 75 112) (F + 112) ltac:(cbn [sv_denot]; rewrite F75, unsigned_lit_small by (clear - HF4096 HFceil C1; lia); reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - HF4096 HFceil C1; lia) V184;
slot 96 (SOff 75 0) F ltac:(cbn [sv_denot]; rewrite F75, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - HF4096 HFceil C1; lia) V96 end;
pose proof HRloc as HR70 end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V200, V112, V216, V240, V248, V176, V184, V96.
assert (Og3 : obj_at trasegs (mrestrict (w_H W3) (ms_mem ms)) g LAY_CGIF (tcgif_vals s)).
{ lazymatch goal with |- obj_at _ (mrestrict _ (ms_mem ?msX)) _ _ _ =>
eapply (aj_obj_kept B); [exact HJ3 | exact Hing | exact Hing3 | exact Og | vm_compute; reflexivity |] end.
change (req_size CGIF_SIZE) with 96. intros j Hj (rr & Hrr & Ha). cbn [In] in Hrr.
unbox. destruct Hrr as [<- | [<- | []]]; cbn [fst snd] in Ha; [clear - Ha Hj HdGC; lia | clear - Ha Hj HdRG; lia]. }
assert (Ob3 : obj_at trasegs (mrestrict (w_H W3) (ms_mem ms)) (fr_ptr fb) LAY_Frame (frame_vals fb)).
{ eapply (aj_obj_kept B); [exact HJ3 | exact Hbef_in | exact Hbef3 | exact (Ofr fb Hfbi) | vm_compute; reflexivity |].
change (req_size FRAME_SIZE) with 40. intros j Hj. apply fl_fp_out_frame; [clear - HdCB; lia | clear - HdRB; lia | exact Hj]. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE (proj1 HJ3) Hcur3) as (_ & _ & _ & _ & HcpresX & _). change (req_size FRAME_SIZE) with 40 in HcpresX.
destruct (obj_at_hole4 (mrestrict (w_H W) mem) (mrestrict (w_H W3) (ms_mem ms)) (fr_ptr f) LAY_Frame 40 (frame_vals f) 3 20
Oc ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity) ltac:(cbn; lia)
ltac:(intros j Hj Hnj; apply (mbyte_of_aview trasegs); pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _);
apply (F2 (fr_ptr f) FRAME_SIZE j Hcur_in Hcur3 ltac:(change (req_size FRAME_SIZE) with 40; exact Hj));
intros (rr & Hrr & Ha); cbn [In] in Hrr; destruct Hrr as [<- | [<- | []]]; cbn [fst snd] in Ha; [clear - Ha Hj Hnj; lia | clear - Ha Hj HdRC; lia])
ltac:(intros j Hj; destruct (proj1 (HcpresX (fr_ptr f + 20 + j) ltac:(clear - Hj; lia))) as [Hh [b Hb]];
unfold mbyte, mrestrict; cbn [ms_mem]; rewrite Hh; cbn; rewrite Hb; eexists; reflexivity))
as (genC & HgenC & Oc3).
unbox.
assert (HSpresX : forall a, spZ regs - TFLUSH_STK <= a < spZ regs -> apresent (w_H W3) (ms_mem ms) a) by (pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSp & _); exact HSp).
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
assert (HC : wctx B W3 (ms_regs msX) (ms_mem msX) mdX (spZ regs) sp1 [(fr_ptr f + 20, fr_ptr f + 24); (cg_raw s + 40, cg_raw s + 44)] ly S W mem md ly3 S3 k fpos
((spZ regs, raZ regs, s0Z regs) :: ch) (fr_img f) (fr_img fb) N g (fr_ptr f) (fr_ptr fb)
(tcgif_vals s) (list_set (frame_vals f) 3 genC) (frame_vals fb)
(cg_pal s) (cg_ngp s) (fr_lpal f) (fr_attr f) (fr_nlp f) (fr_ctidx f) (fr_lpal fb) (fr_attr fb) (fr_nlp fb) (fr_ctidx fb)) end.
{ split; [exact HJ3|]. split; [exact Himg3|]. split; [exact Hbimg3|].
split; [clear - HN HW1 HH1 R7 R8; nia|]. split; [clear - HdII; lia|].
split; [exact Hing3|]. split; [exact Hcur3|]. split; [exact Hbef3|]. split; [clear - HdCB; lia|].
split; [exact Og3|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact Oc3|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact Ob3|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [intros Ha1; exists (3 * fr_nlp f); split; [apply Hsub3; apply Hclpal; exact Ha1 | clear; lia]|].
split; [intros Ha1; exists (3 * fr_nlp fb); split; [apply Hsub3; apply Hblpal; exact Ha1 | clear; lia]|].
split; [intros Hor; exists (3 * cg_ngp s); split; [apply Hsub3; apply (w_gpal_block B ly S g s N rest HPerm); destruct Hor as [H0 | H0]; [exact (Hfgp H0) | exact (Hbgp H0)] | clear; lia]|].
split; [exact EspX|]. split; [exact Hsp1|]. split; [exact Hsp1al16|].
split; [rewrite Rr9, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E70|].
split; [rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 3%nat) by (clear; lia); rewrite (EE 3%nat (@BV 5 3 I) eq_refl); exact Hgp|].
split; [rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 4%nat) by (clear; lia); rewrite (EE 4%nat (@BV 5 4 I) eq_refl); exact Htp|].
split; [rewrite Es0X; exact Hch1|]. split; [exact Es0X|].
split; [exact V240 | exact V248]. }
assert (HGEO : 1 <= cg_W s <= 65535 /\ 1 <= cg_H s <= 65535 /\ N = cg_W s * cg_H s /\
val_mem trasegs (mrestrict (w_H W3) (ms_mem ms)) (sp1 + 200) 8 (cg_W s) /\ val_mem trasegs (mrestrict (w_H W3) (ms_mem ms)) (sp1 + 208) 8 (cg_H s)).
{ split; [clear - HW1 R7; lia|]. split; [clear - HH1 R8; lia|]. split; [exact HN|]. split; [exact V200 | exact V112]. }
assert (HRES : 0 <= F + 128 < 2 ^ 64 /\ 0 <= F + 112 < 2 ^ 64 /\
val_mem trasegs (mrestrict (w_H W3) (ms_mem ms)) (sp1 + 144) 8 (F + 128) /\ val_mem trasegs (mrestrict (w_H W3) (ms_mem ms)) (sp1 + 176) 8 (F + 112)).
{ split; [clear - HF4096 HFceil C1; lia|]. split; [clear - HF4096 HFceil C1; lia|]. split; [exact V176 | exact V184]. }
assert (HSAV2 : 0 <= F < 2 ^ 64 /\ val_mem trasegs (mrestrict (w_H W3) (ms_mem ms)) (sp1 + 96) 8 F).
{ split; [clear - HF4096 HFceil C1; lia | exact V96]. }
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
pose proof (fl_f1 B LAWS ABCMP W3 (ms_regs msX) (ms_mem msX) mdX (spZ regs) sp1 _ ly S W mem md ly3 S3 k fpos _ (fr_img f) (fr_img fb) N g (fr_ptr f) (fr_ptr fb)
_ _ _ _ _ _ _ _ _ _ _ _ _ (cg_W s) (cg_H s) (F + 128) (F + 112) F F HC HGEO HRES HSAV2 (Z.to_nat (cg_H s))) as S1O; unfold f1_stmt in S1O;
eapply (S1O 0 (ms_regs msX) (ms_mem msX) mdX) end;
[ rewrite Z2Nat.id by (clear - HH1; lia); clear; lia | clear - HH1; lia | exact HJ3
| apply (wkeptF_refl B); intros a Ha; apply HSpresX; clear - Ha Hsp1 FFS; change FBAND with 8192 in Ha; lia
| intros r Hr; reflexivity
| first [rewrite Rr21, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E10n | match goal with |- ?g => idtac "S1-21" g end]
| first [rewrite Rr22, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E11n | match goal with |- ?g => idtac "S1-22" g end]
| first [rewrite Rr23; first [rewrite F51 | rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E51]; f_equal; clear; lia | match goal with |- ?g => idtac "S1-23" g end]
| first [rewrite Rr26; first [rewrite F211 | rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E211]; f_equal; clear; lia | match goal with |- ?g => idtac "S1-26" g end]
| first [rewrite Rr18, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact F40 | match goal with |- ?g => idtac "S1-18" g end]
| first [exact Rr27 | rewrite Rr27; reflexivity | match goal with |- ?g => idtac "S1-27" g end]
| first [rewrite Rr20, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact F75 | rewrite Rr20; cbn [sv_denot]; rewrite F75, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | match goal with |- ?g => idtac "S1-20" g end]
| first [rewrite Rr25; first [rewrite F211 | rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E211]; reflexivity | match goal with |- ?g => idtac "S1-25" g end] ]. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & pc5 & -> & HJ5 & WK5 & HK5 & H215 & H225 & Hexit).
assert (HSpres5 : forall a, spZ regs - TFLUSH_STK <= a < spZ regs -> apresent (w_H W3) mem5 a) by (pose proof HJ5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSp & _); exact HSp).
pose proof (proj1 HJ5) as HAR5.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR5 Hfin3) as (_ & _ & HFpres5 & HFSpres5).
change (fs_frame_bytes 2) with 256 in HFpres5, HFSpres5. change (256 / 8) with 32 in HFSpres5. rewrite !EFA3 in HFpres5, HFSpres5. fold F in HFpres5, HFSpres5.
clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3.
assert (Hb70 : bv_unsigned (ew ltac:(lazymatch type of HS with st_ok _ ?Ex _ _ => exact Ex end) 70) = sp1)
by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let cs23 := eval vm_compute in (YQ0b.r_chunks (nth 3 (ss_mem ss_DIMS) got_region)) in
assert (HR70' : region_ok trasegs Ex (mrestrict (w_H W3) (ms_mem msX)) (YQ0b.mkRegion (Some 70%nat) 0 280 0 280 cs23))
by (eapply region_ok_sub; [| clear; cbn; lia | exact HR70]; subregion_tac) end.
clear HR70.
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msX) =>
let rs' := eval vm_compute in (w_trim_base (ss_mem ssx) 70 232 280) in
pose proof (st_ok_submem trasegs Ev ssx (restrict (w_H W3) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
Ltac ws_reseat HS HK5 regs5 mem5 :=
let HK5' := fresh "HK5'" in let HS2 := fresh "HS2" in let HQ := fresh "HQ" in
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict (w_H ?Wx) ?msX) =>
assert (HK5' : forall r : bv 5, reg_in r WS_CLOB = false -> getr regs5 r = getr (ms_regs msX) r)
by (let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; destruct (ws_clob_cases r Hr) as [-> | Hr']; [reflexivity | exact (HK5 r Hr')]);
cbn [ms_regs restrict mkst] in HK5';
let kk := eval vm_compute in (run_K 0 (SOff 32 0) [] ssx) in
jafter_stretch_keep HS kk regs5 (mrestrict (w_H Wx) mem5) WS_CLOB 0x8755c [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat HS2;
lazymatch type of HS2 with _ -> ?Q -> _ =>
assert (HQ : Q);
[ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil
| specialize (HS2 HK5' HQ); clear HQ ] end end.
destruct Hexit as [(-> & top & c0 & HtopR & Hc0 & HPDw & H275 & H205 & H255 & H185w) | (-> & H295 & H235 & H145 & V1605 & H105 & H115 & H185 & H205x & H65)].
-
eapply SRr_bind.
{ eapply (fl_f2 B LAWS ABCMP W3 _ _ _ (spZ regs) sp1 _ ly S W mem md ly3 S3 k fpos _ (fr_img f) (fr_img fb) N g (fr_ptr f) (fr_ptr fb)
_ _ _ _ _ _ _ _ _ _ _ _ _ (cg_W s) (cg_H s) (F + 128) (F + 112) F F HC HGEO HRES V216 HSAV2 top regs5 mem5 md5);
[ exact HtopR | exact HJ5 | exact WK5 | exact HK5 | exact H215 | exact H225 | exact H275 | exact H205 | exact H255 ]. }
cbv beta. intros W6 c6 _ (-> & regs6 & mem6 & md6 & bot & -> & HJ6 & WK6 & HK6 & H66 & H216 & H226 & HbotR & H186 & H266 & H196 & H256 & H276 & H206 & H246).
eapply SRr_bind.
{ eapply (fl_f3 B LAWS W3 _ _ _ (spZ regs) sp1 _ ly S W mem md ly3 S3 k fpos _ (fr_img f) (fr_img fb) N g (fr_ptr f) (fr_ptr fb)
_ _ _ _ _ _ _ _ _ _ _ _ _ (cg_W s) (cg_H s) (F + 128) (F + 112) F F HC HGEO HRES V216 HSAV2 top bot c0 regs6 mem6 md6);
[ clear - HtopR HbotR; lia | clear - HbotR; lia | exact Hc0 | exact HPDw | exact HJ6 | exact WK6 | exact HK6 | exact H66 | exact H216 | exact H226
| exact H276 | exact H186 | exact H266 | exact H256 | exact H246 ]. }
cbv beta. intros W7 c7 _ (-> & regs7 & mem7 & md7 & left & -> & HJ7 & WK7 & HK7 & H67 & H217 & H227 & Hleft & H237 & H127 & V1607 & H277 & H267 & H137 & H257 & H187 & H207).
eapply SRr_bind.
{ eapply (fl_f4 B LAWS W3 _ _ _ (spZ regs) sp1 _ ly S W mem md ly3 S3 k fpos _ (fr_img f) (fr_img fb) N g (fr_ptr f) (fr_ptr fb)
_ _ _ _ _ _ _ _ _ _ _ _ _ (cg_W s) (cg_H s) (F + 128) (F + 112) F F HC HGEO HRES V216 c0 top bot left regs7 mem7 md7);
[ exact Hleft | clear - Hc0; lia | clear - HtopR HbotR; lia | clear - HbotR; lia | exact HPDw | exact HJ7 | exact WK7 | exact HK7
| exact H67 | exact H217 | exact H227 | exact H237 | exact H127 | exact V1607 | exact H277 | exact H267 | exact H137 | exact H257 | exact H187 | exact H207 ]. }
cbv beta. intros W8 c8 _ (-> & regs8 & mem8 & md8 & right & -> & HJ8 & WK8 & HK8 & H68 & H218 & H228 & Hright & H148 & V1608 & H298 & H238 & H108 & H118 & H188 & H208x).
clear HSpres5 HAR5 HFpres5 HFSpres5.
assert (HSpres8 : forall a, spZ regs - TFLUSH_STK <= a < spZ regs -> apresent (w_H W3) mem8 a) by (pose proof HJ8 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSp & _); exact HSp).
pose proof (proj1 HJ8) as HAR8.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR8 Hfin3) as (_ & _ & HFpres8 & HFSpres8).
change (fs_frame_bytes 2) with 256 in HFpres8, HFSpres8. change (256 / 8) with 32 in HFSpres8. rewrite !EFA3 in HFpres8, HFSpres8. fold F in HFpres8, HFSpres8.
aconstsF HJ8 Kgot8 Kcell8 Kguar8 Kuar8.
pose proof WK8 as [K8 X8].
ws_reseat HS HK8 regs8 mem8.
all: try (idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj trasegs _); [exact K8 | evalE AG | exact Hfin3
| right; unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; unfold SB; clear; lia
| intros a Ha Hn; exact Hn
| intros a Ha; exfalso; clear - Ha; unfold SB in *; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj trasegs _); [exact K8 | evalE AG | exact Hfin3
| left; rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia
| intros a Ha Hn; exact Hn
| intros a Ha; apply (proj1 (HFpres8 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj trasegs _); [exact K8 | exact HJ8 | evalE AG | clear; lia | rewrite FFS; clear - Hsp1; lia | clear - Hsp1; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj trasegs _); [exact K8 | exact HJ8 | evalE AG | change FBAND with 8192; clear - Hsp1; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val trasegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot8 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val trasegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell8 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val trasegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar8 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val trasegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar8 | clear; lia] ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj trasegs _); [exact K8 | evalE AG | exact Hing3 | clear; lia | change (req_size CGIF_SIZE) with 96; clear; lia | clear; lia
| intros a Ha Hn; exact Hn ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 12%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj trasegs _); [exact K8 | evalE AG | exact Hbef3 | clear; lia | change (req_size FRAME_SIZE) with 40; clear; lia | clear; lia
| intros a Ha Hn; exact Hn ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply (region_kept_block_ajw2 trasegs B LAWS); [exact K8 | exact HAR8 | exact Hcur3 | evalE AG | exact Hcur3 | clear; lia | change (req_size FRAME_SIZE) with 40; clear; lia | clear; lia | clear; lia
| intros a Ha Hn; exact Hn ] end
| match goal with |- region_kept _ _ _ _ ?r => idtac "KEPTFAIL" r end ]).
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HR70' with region_ok _ _ _ (YQ0b.mkRegion _ _ _ _ _ ?cs23) =>
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msv =>
lazymatch Ev with havoc _ ?KK _ =>
let rs := eval vm_compute in (ss_mem ssx) in
lazymatch rs with ?r0 :: ?r1 :: ?r2 :: ?rt :: ?l2 =>
pose proof (w_st_ok_replace_region Ev ssx msv [r0; r1; r2] rt (YQ0b.mkRegion (Some 70%nat) 0 280 0 280 cs23) l2 HS eq_refl ltac:(vm_compute; reflexivity)
ltac:(cbn [ms_mem restrict mkst];
eapply (region_ok_transport_chunksK KK _ Ev _ _ 70 _ 0 280 0 280 cs23 HR70' Hb70);
[ apply (env_agree_havoc_ge KK KK _ _ _ ltac:(clear; lia) (env_agree_refl _ _))
| apply (proj1 (Nat.ltb_lt _ _)); vm_compute; reflexivity
| vm_compute; reflexivity
| let c := fresh "c" in let Hc := fresh "Hc" in let a := fresh "a" in let Ha := fresh "Ha" in let Hcf := fresh "Hcf" in
intros c Hc a Ha;
pose proof (proj1 (forallb_forall _ _) (ltac:(vm_compute; reflexivity) : forallb chunk_scratch_freeb cs23 = true) c Hc) as Hcf;
unfold chunk_scratch_freeb in Hcf;
destruct (off_scratch_free_sound _ _ _ Hcf a Ha) as [[Hlt Hns] | Hge];
[ apply (mbyte_of_aview trasegs); apply X8; [exact Hlt | exact Hns]
| apply (mbyte_of_aview trasegs); pose proof K8 as (K81 & _); apply K81;
[ clear - Hge Hsp1 Hceil FFS Hshi H47 Hstk0 Hslo C1; lia
| change FBAND with 8192; clear - Hge; lia ] ]
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply (apresent_writable trasegs); apply HSpres8;
rewrite FFS; clear - Ha Hsp1; lia ])
ltac:(cbn [all_disjoint app]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
lazymatch goal with AG : forall n, (n < 33)%nat -> _ |- _ => evalE AG end;
change (fs_frame_bytes 2) with 256; change (fs_frame_bytes 2 / 8) with 32;
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, CGIF_SIZE, FRAME_SIZE, SB;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C2 C3 HF4096 HFceil HFhigh HF8lo HF8hi HF8c Hgh Hgceil Hcrh Hcceil Hb4096 Hbceil Hbh1 Hbh2;
ceil; unfold ASAN_CEIL, kHighMemBeg, kLowShadowBeg, kHighMemBeg in *; repeat split; first [zone_lia | match goal with |- ?g => idtac "DISJ-FAIL" g end])) as HS3;
clear HS; rename HS3 into HS end end end end.
norm_ss HS.
rebaseE HS AG HEv. clear HEv.
ws_pin HS (@BV 5 6 I) (SOff 32 0) H68 ltac:(rewrite (AG 32%nat) by (clear; lia); rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ws_pin HS (@BV 5 10 I) (SOff 75 112) H108 ltac:(rewrite RF, unsigned_lit_small by (clear - HF4096 HFceil C1; lia); reflexivity).
ws_pin HS (@BV 5 11 I) (SOff 75 128) H118 ltac:(rewrite RF, unsigned_lit_small by (clear - HF4096 HFceil C1; lia); reflexivity).
ws_pin HS (@BV 5 21 I) (SOff 10 0) H218 ltac:(rewrite (AG 10%nat) by (clear; lia); rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ws_pin HS (@BV 5 22 I) (SOff 11 0) H228 ltac:(rewrite (AG 11%nat) by (clear; lia); rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ws_pin HS (@BV 5 18 I) (SOff 75 0) H188 ltac:(rewrite RF, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ws_pin HS (@BV 5 20 I) (SOff 75 0) H208x ltac:(rewrite RF, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
ra_join HS ss_DIMS 420%nat fl_dims_deads_bv ltac:(idtac; ra_join_val HS 420%nat 0%nat H148 E420; ra_join_val HS 420%nat 1%nat H298 E422; ra_join_val HS 420%nat 2%nat H238 E423);
fl_hand RD HS end.
split; [exact Hk3|]. split; [exact Eab3|].
split; [exists gen; split; [rewrite !ew_havoc_old by (clear; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear; lia); assumption|].
split; [exists fb; apply fl_bef_havoc; [clear; lia|]; split; [exact Hfb|]; cbn [c_i c_s]; bef_EB|].
exists (right - left + 1), (bot + 1 - top), top, left. cbn [c_s].
split; [exact E420|]. split; [cbn [c_sp1 ms_mem]; exact V1608|]. split; [exact E422|]. split; [exact E423|].
clear - Hleft Hright Hc0 HtopR HbotR. lia.
-
pose proof WK5 as [K5 X5]. aconstsF HJ5 Kgot5 Kcell5 Kguar5 Kuar5.
ws_reseat HS HK5 regs5 mem5.
all: try (idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj trasegs _); [exact K5 | evalE AG | exact Hfin3
| right; unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; unfold SB; clear; lia
| intros a Ha Hn; exact Hn
| intros a Ha; exfalso; clear - Ha; unfold SB in *; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj trasegs _); [exact K5 | evalE AG | exact Hfin3
| left; rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia
| intros a Ha Hn; exact Hn
| intros a Ha; apply (proj1 (HFpres5 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj trasegs _); [exact K5 | exact HJ5 | evalE AG | clear; lia | rewrite FFS; clear - Hsp1; lia | clear - Hsp1; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj trasegs _); [exact K5 | exact HJ5 | evalE AG | change FBAND with 8192; clear - Hsp1; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val trasegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot5 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val trasegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell5 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val trasegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar5 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val trasegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar5 | clear; lia] ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj trasegs _); [exact K5 | evalE AG | exact Hing3 | clear; lia | change (req_size CGIF_SIZE) with 96; clear; lia | clear; lia
| intros a Ha Hn; exact Hn ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 12%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj trasegs _); [exact K5 | evalE AG | exact Hbef3 | clear; lia | change (req_size FRAME_SIZE) with 40; clear; lia | clear; lia
| intros a Ha Hn; exact Hn ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply (region_kept_block_ajw2 trasegs B LAWS); [exact K5 | exact HAR5 | exact Hcur3 | evalE AG | exact Hcur3 | clear; lia | change (req_size FRAME_SIZE) with 40; clear; lia | clear; lia | clear; lia
| intros a Ha Hn; exact Hn ] end
| match goal with |- region_kept _ _ _ _ ?r => idtac "KEPTFAIL" r end ]).
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HR70' with region_ok _ _ _ (YQ0b.mkRegion _ _ _ _ _ ?cs23) =>
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msv =>
lazymatch Ev with havoc _ ?KK _ =>
let rs := eval vm_compute in (ss_mem ssx) in
lazymatch rs with ?r0 :: ?r1 :: ?r2 :: ?rt :: ?l2 =>
pose proof (w_st_ok_replace_region Ev ssx msv [r0; r1; r2] rt (YQ0b.mkRegion (Some 70%nat) 0 280 0 280 cs23) l2 HS eq_refl ltac:(vm_compute; reflexivity)
ltac:(cbn [ms_mem restrict mkst];
eapply (region_ok_transport_chunksK KK _ Ev _ _ 70 _ 0 280 0 280 cs23 HR70' Hb70);
[ apply (env_agree_havoc_ge KK KK _ _ _ ltac:(clear; lia) (env_agree_refl _ _))
| apply (proj1 (Nat.ltb_lt _ _)); vm_compute; reflexivity
| vm_compute; reflexivity
| let c := fresh "c" in let Hc := fresh "Hc" in let a := fresh "a" in let Ha := fresh "Ha" in let Hcf := fresh "Hcf" in
intros c Hc a Ha;
pose proof (proj1 (forallb_forall _ _) (ltac:(vm_compute; reflexivity) : forallb chunk_scratch_freeb cs23 = true) c Hc) as Hcf;
unfold chunk_scratch_freeb in Hcf;
destruct (off_scratch_free_sound _ _ _ Hcf a Ha) as [[Hlt Hns] | Hge];
[ apply (mbyte_of_aview trasegs); apply X5; [exact Hlt | exact Hns]
| apply (mbyte_of_aview trasegs); pose proof K5 as (K51 & _); apply K51;
[ clear - Hge Hsp1 Hceil FFS Hshi H47 Hstk0 Hslo C1; lia
| change FBAND with 8192; clear - Hge; lia ] ]
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply (apresent_writable trasegs); apply HSpres5;
rewrite FFS; clear - Ha Hsp1; lia ])
ltac:(cbn [all_disjoint app]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
lazymatch goal with AG : forall n, (n < 33)%nat -> _ |- _ => evalE AG end;
change (fs_frame_bytes 2) with 256; change (fs_frame_bytes 2 / 8) with 32;
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, CGIF_SIZE, FRAME_SIZE, SB;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C2 C3 HF4096 HFceil HFhigh HF8lo HF8hi HF8c Hgh Hgceil Hcrh Hcceil Hb4096 Hbceil Hbh1 Hbh2;
ceil; unfold ASAN_CEIL, kHighMemBeg, kLowShadowBeg, kHighMemBeg in *; repeat split; first [zone_lia | match goal with |- ?g => idtac "DISJ-FAIL" g end])) as HS3;
clear HS; rename HS3 into HS end end end end.
norm_ss HS.
rebaseE HS AG HEv. clear HEv.
ws_pin HS (@BV 5 6 I) (SOff 32 0) H65 ltac:(rewrite (AG 32%nat) by (clear; lia); rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ws_pin HS (@BV 5 10 I) (SOff 75 128) H105 ltac:(rewrite RF, unsigned_lit_small by (clear - HF4096 HFceil C1; lia); reflexivity).
ws_pin HS (@BV 5 11 I) (SOff 75 112) H115 ltac:(rewrite RF, unsigned_lit_small by (clear - HF4096 HFceil C1; lia); reflexivity).
ws_pin HS (@BV 5 21 I) (SOff 10 0) H215 ltac:(rewrite (AG 10%nat) by (clear; lia); rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ws_pin HS (@BV 5 22 I) (SOff 11 0) H225 ltac:(rewrite (AG 11%nat) by (clear; lia); rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ws_pin HS (@BV 5 18 I) (SOff 75 0) H185 ltac:(rewrite RF, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ws_pin HS (@BV 5 20 I) (SOff 75 0) H205x ltac:(rewrite RF, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ws_pin HS (@BV 5 26 I) (SLit 1) H145 ltac:(reflexivity).
ws_pin HS (@BV 5 27 I) (SLit 0) H295 ltac:(reflexivity).
ws_pin HS (@BV 5 23 I) (SLit 0) H235 ltac:(reflexivity).
lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
ra_join HS ss_DIMSi 423%nat fl_dimsi_deads_bv ltac:(idtac); fl_hand RDi HS end.
split; [exact Hk3|]. split; [exact Eab3|].
split; [exists gen; split; [rewrite !ew_havoc_old by (clear; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear; lia); assumption|].
split; [exists fb; apply fl_bef_havoc; [clear; lia|]; split; [exact Hfb|]; cbn [c_i c_s]; bef_EB|].
cbn [c_sp1 ms_mem]. exact V1605.
Qed.
Lemma fl_Fv : fl_from B ss_DIMS (INV_DIMS B) -> fl_from B ss_DIMSi (INV_DIMSi B) -> fl_from B ss_Fv (INV_DIFF B).
Proof. exact fl_Fv_aux. Qed.
End h.
End d.
