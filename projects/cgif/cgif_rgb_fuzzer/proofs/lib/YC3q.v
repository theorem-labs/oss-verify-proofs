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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI04 YI06 YC2v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC0x YC1b YC2u YC20 YC13 YC3p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac rnLAWS := lazymatch goal with L : AR_laws trasegs _ |- _ => L end.
Ltac rnTL := lazymatch goal with T : TraLib _ |- _ => T end.
Ltac rnFFL := lazymatch goal with H : frame_flag_lawP _ _ |- _ => H end.
Ltac nat_side := first [ apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); vm_compute; reflexivity
| apply (proj1 (PeanoNat.Nat.eqb_neq _ _)); vm_compute; reflexivity ].
Ltac rebaseE HS AG HEv :=
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
Ltac evalE AG :=
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
repeat match goal with |- context [ew Ev ?n] => lazymatch (eval cbv in (Nat.ltb n 33)) with true => rewrite (AG n) by lia end end end;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
repeat match goal with H : bv_unsigned (ew ?Ex 2) = _ |- context [bv_unsigned (ew ?Ex 2)] => rewrite H end;
rewrite ?unsigned_lit_small by (unfold SB; lia); unfold SB; first [reflexivity | lia | idtac].
Ltac evalE0 AG :=
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
repeat match goal with |- context [ew Ev ?n] => lazymatch (eval cbv in (Nat.ltb n 33)) with true => rewrite (AG n) by lia end end end;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
repeat match goal with H : bv_unsigned (ew ?Ex 2) = _ |- context [bv_unsigned (ew ?Ex 2)] => rewrite H end;
rewrite ?unsigned_lit_small by (unfold SB; lia); unfold SB.
Ltac awrR_rec AG fpos F EFA :=
lazymatch goal with
| |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ (YQ0b.mkRegion _ _ _ ?wlo ?whi _ :: _) _ _ _ _ _ _ _ =>
first
[ apply awr_ok_cons_ro; [cbn; lia|]
| lazymatch goal with
| |- awr_ok _ (YQ0b.mkRegion (Some 58%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 58%nat); [reflexivity | evalE AG | | ];
[ cbn [YQ0b.r_wlo YQ0b.r_whi]; intros a Ha; right; right; right; exists 1, fpos; split; [left; reflexivity|]; right;
unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; rewrite ?EFA; fold F; unfold SB; clear - Ha; lia
| ]
| |- awr_ok _ (YQ0b.mkRegion (Some 45%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 45%nat); [reflexivity | evalE AG | | ];
[ cbn [YQ0b.r_wlo YQ0b.r_whi]; intros a Ha; right; right; right; exists 1, fpos; split; [left; reflexivity|]; left;
unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 1) with 128; rewrite ?EFA; fold F; clear - Ha; lia
| ]
| |- awr_ok _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | evalE AG | cbn; lia | cbn; lia |]
| |- awr_ok _ (YQ0b.mkRegion (Some ?nb) _ _ _ _ _ :: _) _ _ _ _ ?blc _ _ =>
match goal with Rb : ew _ nb = Z_to_bv 64 ?b, Ab : forall blc' lyq ownq i, In (?b', ?sz) blc' -> _, Hin : In (?b', ?sz) blc |- _ =>
constr_eq b b';
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ nb); [reflexivity | evalE AG | | ];
[ cbn [YQ0b.r_wlo YQ0b.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; replace a with (b + (a - b)) by lia; apply Ab; [exact Hin | clear - Ha; lia]
| ] end
end
| fail 1 "awrR: no rule for the head region" ];
awrR_rec AG fpos F EFA
end.
Ltac awrR AG fpos F EFA :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
awrR_rec AG fpos F EFA.
Ltac idx_of_base rs n :=
lazymatch rs with
| YQ0b.mkRegion (Some n) _ _ _ _ _ :: _ => constr:(0%nat)
| _ :: ?tl => let i := idx_of_base tl n in constr:(S i)
end.
Ltac fs_ro HS :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 58%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region trasegs Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow trasegs Ex _ r 0 0 (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Ltac fs_rw HS E58 Hp :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 58%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region trasegs Ex ssx msx i r (set_window r 0 16) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow trasegs Ex _ r 0 16 (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YQ0b.r_base base_val ms_mem restrict mkst]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite E58, unsigned_lit_small by (unfold SB; lia);
intros o Ho; apply (apresent_writable trasegs); unfold shadow_addr in Hp; rewrite <- SB_SHADOW_OFF in Hp;
apply (proj1 (Hp o ltac:(clear - Ho; lia)))))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Ltac oblF HJx HE10 HE35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal :=
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 10 ?c)) ?len =>
lazymatch type of HE10 with _ = Z_to_bv 64 ?cfgp =>
first [ rewrite (U_atom_off Ex 10 cfgp c); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE10 | lia | lia]
| rewrite (U_atom Ex 10 cfgp); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE10 | lia] ];
eapply (obl_of_range trasegs _ _ Ex (SOff 35 0) _ len cfgp 48);
[ let L := rnLAWS in eapply (range_addressable_entry_frame trasegs _ L); [exact HJx | exact Hfin | exact Hcid0 | exact Hflo | exact Hfhi | exact Hfal
| intros x Hx; exfalso; exact (inFP_nil x Hx) | exact HAR | exact HRA]
| rewrite (U_atom Ex 35 SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE35 | unfold SB; lia]
| lia | lia ] end end.
Ltac oblG HJx HE32 HE35 Hing :=
let L := rnLAWS in
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 32 ?c)) ?len =>
lazymatch type of HE32 with _ = Z_to_bv 64 ?g =>
first [ rewrite (U_atom_off Ex 32 g c); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE32 | lia | lia]
| rewrite (U_atom Ex 32 g); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE32 | lia] ];
eapply (obl_of_block trasegs _ L _ _ _ _ _ Ex (SOff 35 0) _ len g CGIF_SIZE (proj1 HJx) Hing);
[ rewrite (U_atom Ex 35 SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE35 | unfold SB; lia]
| lia | change (req_size CGIF_SIZE) with 96; lia ] end end.
Ltac oblR HJx HE65 HE35 Hin :=
let L := rnLAWS in
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 65 ?c)) ?len =>
lazymatch type of HE65 with _ = Z_to_bv 64 ?res =>
first [ rewrite (U_atom_off Ex 65 res c); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE65 | lia | lia]
| rewrite (U_atom Ex 65 res); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE65 | lia] ];
eapply (obl_of_block trasegs _ L _ _ _ _ _ Ex (SOff 35 0) _ len res 48 (proj1 HJx) Hin);
[ rewrite (U_atom Ex 35 SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE35 | unfold SB; lia]
| lia | change (req_size 48) with 48; lia ] end end.
Ltac obl_blk HJx HEn HEbx Hin :=
let L := rnLAWS in
lazymatch goal with |- range_addressable _ (U ?Ex (SOff ?bx 0)) (U _ (SOff ?n ?c)) ?len =>
lazymatch type of HEn with _ = Z_to_bv 64 ?p =>
lazymatch type of Hin with In (_, ?sz) _ =>
first [ rewrite (U_atom_off Ex n p c); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HEn | lia | lia]
| rewrite (U_atom Ex n p); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HEn | lia] ];
eapply (obl_of_block trasegs _ L _ _ _ _ _ Ex (SOff bx 0) _ len p sz (proj1 HJx) Hin);
[ rewrite (U_atom Ex bx SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HEbx | unfold SB; lia]
| lia | let v := eval vm_compute in (req_size sz) in change (req_size sz) with v; lia ] end end end.
Ltac relow HS AG E10 E32 E10n E32n :=
try clear E10n; try clear E32n;
lazymatch type of HS with st_ok _ ?Ev _ _ =>
lazymatch type of E10 with _ = ?v10 => assert (E10n : ew Ev 10 = v10) by (rewrite (AG 10%nat) by lia; exact E10) end;
lazymatch type of E32 with _ = ?v32 => assert (E32n : ew Ev 32 = v32) by (rewrite (AG 32%nat) by lia; exact E32) end end.
Ltac creg HS AG EE :=
lazymatch goal with |- getr _ ?r = getr _ _ =>
let R := fresh "R" in rreg HS r R; rewrite R; clear R;
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite AG by lia;
apply EE; reflexivity end.
Ltac add_flag_region HS AG E57 Hp HFLrng HFLown HnoG HnoC HnoF :=
let Qceil := match goal with H : alloc_ceiling <= ly_stk_lo _ |- _ => H end in
let Qslo := match goal with H : ly_stk_lo _ + _ <= spZ _ |- _ => H end in
let QC1 := match goal with H : _ <= alloc_ceiling <= _ |- _ => H end in
let QC3 := match goal with H : kHighMemBeg = _ |- _ => H end in
let QFFS := match goal with H : TNEWGIF_STK = _ |- _ => H end in
let QFq := match goal with H : ?Fr = 32 * (?Fr / 32) |- _ => H end in
let QF8 := match goal with H : ?Fr / 8 = 4 * (?Fr / 32) |- _ => H end in
let QFceil := match goal with H : ?Fr + 128 <= alloc_ceiling |- _ => H end in
let QF8lo := match goal with H : 512 <= ?Fr / 8 |- _ => H | _ => QFq end in
let QF8hi := match goal with H : ?Fr / 8 < 17592186044416 |- _ => H | _ => QFq end in
lazymatch type of HS with st_ok _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_add_region trasegs Ev _ _ (YQ0b.mkRegion (Some 57%nat) 0 1 0 1 []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite ?ew_ewset_other by lia; rewrite E57, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable trasegs); lazymatch goal with |- apresent _ _ (?fl + ?oo) => replace (fl + oo) with fl by lia end; exact Hp)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; evalE0 AG;
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_newgif;
repeat split; first [clear - HFLrng Qceil Qslo QC1 QC3 QFFS QFq QF8 QFceil QF8lo QF8hi; zone_lia |
lazymatch goal with |- ?fl + 1 <= ?x + ?l \/ ?x + ?h <= ?fl + 0 =>
let Hlt := fresh "Hlt" in let Hge := fresh "Hge" in let Hlt2 := fresh "Hlt2" in let Hge2 := fresh "Hge2" in
destruct (Z_lt_ge_dec fl (x + l)) as [Hlt | Hge]; [left; clear - Hlt; lia|];
destruct (Z_lt_ge_dec fl (x + h)) as [Hlt2 | Hge2]; [exfalso | right; clear - Hge2; lia];
first [apply (HnoG fl); [clear - Hge Hlt2; lia | exact HFLown] | apply (HnoC fl); [clear - Hge Hlt2; lia | exact HFLown]
| apply (HnoF fl); [clear - Hge Hlt2; lia | exact HFLown]
| match goal with Hn : forall a, _ -> ~ aowned _ _ _ a |- _ => apply (Hn fl); [clear - Hge Hlt2; lia | exact HFLown] end
| match goal with |- ?g => idtac "DISJFAIL" g end] end
| match goal with |- ?g => idtac "DISJ?" g end ])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Ltac wrangeR AG fpos F EFA EFL :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (r & Hin & Hr); rewrite ?EFA, ?EFL;
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr; revert Hr; evalE0 AG; intros Hr;
first [ exfalso; clear - Hr; lia
| right; clear - Hr; lia
| left; left; clear - Hr; unfold TNEWGIF_STK, TRAWNEW_STK, ASTACK; lia
| left; right; right; right; exists 1, fpos; split; [left; reflexivity|];
first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 1) with 128; rewrite ?EFA; fold F; clear - Hr; lia
| right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; rewrite ?EFA; fold F; unfold SB; clear - Hr; lia ]
| left; match goal with A : forall blc lyq ownq i, In (?r, 48) blc -> _, Hin : In (?r, 48) (ablocks _ _ _) |- _ =>
replace a with (r + (a - r)) by lia; apply A; [exact Hin | clear - Hr; lia] end
| match goal with |- ?g => match type of Hr with ?t => idtac "WRFAIL" t g end end; fail 2 "wrangeR" ]
| ]);
destruct Hin.
Ltac flag0 E57 EFL :=
let msr := fresh "msr" in let HSr := fresh "HSr" in let HR := fresh "HR" in let V := fresh "V" in
intros msr HSr; rewrite ?EFL;
lazymatch type of HSr with st_ok _ ?Ex ?ssx _ =>
pose proof (st_ok_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR;
lazymatch type of HR with region_ok _ _ _ (YQ0b.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex (ms_mem msr) n _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E57; apply unsigned_lit_small; lia)
ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end end;
rewrite Z.add_0_r in V; pose proof (V 0%nat ltac:(lia)) as V0; cbn [Z.of_nat] in V0; rewrite Z.add_0_r in V0; exact V0.
Ltac upd_above HUP HFr AG :=
let HUP' := fresh "HUP" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of HUP with forall a, ?lo <= a < _ -> aview ?sg ?Hh _ a = aview _ _ ?me a =>
assert (HUP' : forall a, lo <= a < 2 ^ 64 -> aview sg Hh (ms_mem msX) a = aview sg Hh me a);
[ let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; rewrite <- (HUP a Ha); eapply (aview_kept_frame Ef rs _ _ _ lo HFr); [lia| |exact Ha];
let b := fresh "b" in let Hb := fresh "Hb" in let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros b Hb (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg; clear - Hb Hrg; lia|]);
destruct Hin
| clear HUP; rename HUP' into HUP ] end end.
Ltac exitR HS HJx AG fpos F cfgp g E57 E58 Hfin HfinS HingX EE Hra HEV EFA EFL :=
let HFLpres' := fresh "HFLpres'" in let HFLown := fresh "HFLown'" in let HFLrng := fresh "HFLrng'" in
let HFpres' := fresh "HFpres'" in let HFSpres' := fresh "HFSpres'" in
let HCpres' := fresh "HCpres'" in let HGpres' := fresh "HGpres'" in
let HnoG := fresh "HnoG" in let HnoC := fresh "HnoC" in let HnoF := fresh "HnoF" in
let FFL := rnFFL in let LAWS := rnLAWS in destruct (FFL _ _ _ _ _ 1 fpos (proj1 HJx) Hfin) as (HFLpres' & HFLown & HFLrng); rewrite ?EFL in HFLpres'; rewrite ?EFL in HFLown; rewrite ?EFL in HFLrng; fold F in HFLrng;
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos (proj1 HJx) Hfin) as (_ & _ & HFpres' & HFSpres'); change (fs_frame_bytes 1) with 128 in HFpres', HFSpres';
change (128 / 8) with 16 in HFSpres'; rewrite ?EFA in HFpres'; rewrite ?EFA in HFSpres'; fold F in HFpres', HFSpres';
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ (proj1 HJx) HfinS) as (_ & _ & HCpres' & _); rewrite ?EFA in HCpres';
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE (proj1 HJx) HingX) as (_ & _ & _ & _ & HGpres' & _); change (req_size CGIF_SIZE) with 96 in HGpres';
lazymatch type of HGpres' with forall a, _ -> _ /\ ~ aowned ?B ?lyx ?Sx a =>
assert (HnoG : forall a, g <= a < g + 96 -> ~ aowned B lyx Sx a) by (intros a Ha; exact (proj2 (HGpres' a Ha)));
assert (HnoC : forall a, cfgp <= a < cfgp + 48 -> ~ aowned B lyx Sx a) by (intros a Ha; apply (fun H => proj2 (HCpres' a H)); lia);
assert (HnoF : forall a, F <= a < F + 128 -> ~ aowned B lyx Sx a) by (intros a Ha; exact (proj2 (HFpres' a Ha)));
try (match goal with Hin : In (?r, 48) (ablocks _ lyx Sx) |- _ =>
let HRp := fresh "HRp" in let HnoR := fresh "HnoR" in
destruct (al_blocks _ _ LAWS _ _ _ _ _ r 48 (proj1 HJx) Hin) as (_ & _ & _ & _ & HRp & _); change (req_size 48) with 48 in HRp;
assert (HnoR : forall a, r <= a < r + 48 -> ~ aowned B lyx Sx a) by (intros a Ha; exact (proj2 (HRp a Ha))); clear HRp end) end;
fs_rw HS E58 HFSpres';
add_flag_region HS AG E57 HFLpres' HFLrng HFLown HnoG HnoC HnoF;
aj_run_flag_sh tratbl_lib_ok HS HJx; [lia | wrangeR AG fpos F EFA EFL | flag0 E57 EFL |];
let R1 := fresh "R1" in let R10 := fresh "R10" in
rreg HS (1%bv : bv 5) R1; rreg HS (10%bv : bv 5) R10;
lazymatch goal with |- SRr _ ?Wx _ _ =>
eapply (SRr_ret_at trasegs tratbl_lib tratbl_lib_ok Hwx_tfa Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end;
let mat' := fresh "mat'" in intros mat'; unfold ng_post, apost_base;
lazymatch type of HJx with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx _ _ _ _ =>
lazymatch goal with |- exists ly' S' regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists lyx, Sx, rg, mm, mdx end end;
split; [rewrite R1; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Hra; reflexivity|];
split; [cbn [ms_mem]; eapply (ajournal_mono_k trasegs _); [apply (ajournal_materialize trasegs _ LAWS tra_segs_low); exact HJx | rewrite HEV; unfold EV_RAWNEW; lia]|];
split; [apply aregs_preserved_eqs; creg HS AG EE|];
rewrite R10.
Ltac exitN HS HJx AG fpos F cfgp E57 E58 Hfin HfinS EE Hra HEV EFA EFL :=
let HFLpres' := fresh "HFLpres'" in let HFLown := fresh "HFLown'" in let HFLrng := fresh "HFLrng'" in
let HFpres' := fresh "HFpres'" in let HFSpres' := fresh "HFSpres'" in
let HCpres' := fresh "HCpres'" in
let HnoC := fresh "HnoC" in let HnoF := fresh "HnoF" in
let FFL := rnFFL in let LAWS := rnLAWS in destruct (FFL _ _ _ _ _ 1 fpos (proj1 HJx) Hfin) as (HFLpres' & HFLown & HFLrng); rewrite ?EFL in HFLpres'; rewrite ?EFL in HFLown; rewrite ?EFL in HFLrng; fold F in HFLrng;
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos (proj1 HJx) Hfin) as (_ & _ & HFpres' & HFSpres'); change (fs_frame_bytes 1) with 128 in HFpres', HFSpres';
change (128 / 8) with 16 in HFSpres'; rewrite ?EFA in HFpres'; rewrite ?EFA in HFSpres'; fold F in HFpres', HFSpres';
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ (proj1 HJx) HfinS) as (_ & _ & HCpres' & _); rewrite ?EFA in HCpres';
lazymatch type of HFpres' with forall a, _ -> _ /\ ~ aowned ?B ?lyx ?Sx a =>
assert (HnoC : forall a, cfgp <= a < cfgp + 48 -> ~ aowned B lyx Sx a) by (intros a Ha; apply (fun H => proj2 (HCpres' a H)); lia);
assert (HnoF : forall a, F <= a < F + 128 -> ~ aowned B lyx Sx a) by (intros a Ha; exact (proj2 (HFpres' a Ha))) end;
fs_rw HS E58 HFSpres';
add_flag_region HS AG E57 HFLpres' HFLrng HFLown HnoC HnoC HnoF;
aj_run_flag_sh tratbl_lib_ok HS HJx; [lia | wrangeR AG fpos F EFA EFL | flag0 E57 EFL |];
let R1 := fresh "R1" in let R10 := fresh "R10" in
rreg HS (1%bv : bv 5) R1; rreg HS (10%bv : bv 5) R10;
lazymatch goal with |- SRr _ ?Wx _ _ =>
eapply (SRr_ret_at trasegs tratbl_lib tratbl_lib_ok Hwx_tfa Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end;
let mat' := fresh "mat'" in intros mat'; unfold ng_post, apost_base;
lazymatch type of HJx with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx _ _ _ _ =>
lazymatch goal with |- exists ly' S' regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists lyx, Sx, rg, mm, mdx end end;
split; [rewrite R1; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Hra; reflexivity|];
split; [cbn [ms_mem]; eapply (ajournal_mono_k trasegs _); [apply (ajournal_materialize trasegs _ LAWS tra_segs_low); exact HJx | rewrite HEV; unfold EV_RAWNEW; lia]|];
split; [apply aregs_preserved_eqs; creg HS AG EE|];
rewrite R10.
Ltac ng_facts HCTX HCFG HE0 HE :=
let LAWS := rnLAWS in
pose proof Hwx_tfa as Hwx; pose proof tra_segs_low as Hsegs;
destruct HCTX as (HPRE & Hal32 & Hctx & Hroom & Htop32 & HROD & Hcfg & HWH & Hpala & HPerm & Hev & Hlive);
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5); assert (FFS : TNEWGIF_STK = 16768) by reflexivity;
assert (HEV : EV_NEWGIF = 12) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity; assert (Has : ASTACK = 16384) by reflexivity;
destruct HCFG as (Hfin & Hcid0 & Hfal & Hflo & Hfhi & Hcal & HRA);
destruct HE0 as (EE & E10 & E32 & Usp); destruct HE as (AG & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & RF & E57 & E58);
destruct (frames_bounds trasegs _ LAWS _ _ _ _ _ _ _ HAR Hfin) as (Hf4096 & Hfceil & Hfhigh);
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img;
cbn [CTX_cgif_newgif In] in Hctx;
let Hq := fresh "Hq" in let Hr := fresh "Hr" in let Hs := fresh "Hs" in
lazymatch type of Hra4 with _ <= raZ ?regs =>
lazymatch type of Hch with achain _ _ _ _ ?ch =>
assert (Hra88 : 0x81de4 = raZ regs) by (destruct Hctx as [Hq | [Hq | []]]; injection Hq as Hr Hs; exact Hr);
assert (Hspine : spine ch = [0x81338] \/ spine ch = [0x81338; 0x80ea8])
by (destruct Hctx as [Hq | [Hq | []]]; injection Hq as Hr Hs; rewrite <- Hs; [left | right]; reflexivity) end end;
let Hc' := fresh "Hc'" in
pose proof Hcfg as Hc'; cbn [obj_at LAY_Config] in Hc';
destruct Hc' as ([CV0 CR0] & [CV8 CR8] & [CV16 CR16] & [CV20 CR20] & [CV24 CR24] & [CV26 CR26] & [CV28 CR28] & [CV30 CR30] & [CV32 CR32] & [CV40 CR40] & HcT);
cbn [fst snd N.to_nat Z.of_N] in CV0, CV8, CV16, CV20, CV24, CV26, CV28, CV30, CV32, CV40, CR0, CR16, CR20, CR24, CR26, CR28, CR30;
change (2 ^ (8 * 8)) with (2 ^ 64) in CR0; change (2 ^ (8 * 4)) with (2 ^ 32) in CR16, CR20; change (2 ^ (8 * 2)) with 65536 in CR24, CR26, CR28, CR30.
Ltac ng_frame HJ3 Hfrs3 :=
let LAWS := rnLAWS in
pose proof (proj1 HJ3) as HAR3;
lazymatch type of HJ3 with ajournal _ _ _ _ _ ?ly ?S _ _ _ _ ?ly3 ?S3 _ _ _ _ =>
lazymatch type of Hfrs3 with frames _ = (1, ?fpos) :: _ =>
lazymatch goal with Hfin : In (?cid, ?pos) (frames S) |- _ =>
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 ltac:(lazymatch goal with H : AR trasegs _ ly S _ _ _ |- _ => exact H end) (proj1 (proj2 HJ3))) as (_ & EFA3 & _);
assert (EFL3 : forall c p, flag_addr ly3 c p = flag_addr ly c p) by (intros c p; unfold flag_addr; pose proof (EFA3 c p) as X; unfold frame_addr in X; lia);
assert (Hfin3 : In (1, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity);
assert (HfinS3 : In (cid, pos) (frames S3)) by (rewrite Hfrs3; right; exact Hfin);
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR3 Hfin3) as (HFal & [HFhi _] & HFpres3 & HFSpres3);
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR3 Hfin3) as HFapp_img;
destruct (frames_bounds trasegs _ LAWS _ _ _ _ _ 1 fpos HAR3 Hfin3) as (HF4096 & HFceil & HFhigh);
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR3 Hfin3) as HFhigh_img;
change (fs_frame_bytes 1) with 128 in *; change (128 / 8) with 16 in HFSpres3; rewrite !EFA3 in *;
set (F := frame_addr ly 1 fpos) in *; set (FL := flag_addr ly 1 fpos) in *;
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia);
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity);
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia)    ;
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia);
let fl1 := fresh "fl1" in let fl2 := fresh "fl2" in let Efl := fresh "Efl" in
destruct (in_split _ _ Hfin) as (fl1 & fl2 & Efl);
pose proof (sep_frames_pos trasegs _ LAWS ly3 S3 _ _ _ (1, fpos) (cid, pos) [] fl1 fl2 HAR3 ltac:(rewrite Hfrs3, Efl; reflexivity)) as HdFC;
unfold zdisjoint, frame_rng in HdFC; cbn [fst snd] in HdFC; change (fs_frame_bytes 1) with 128 in HdFC; rewrite !EFA3 in HdFC; fold F in HdFC
end end end.
Ltac ng_chain HS HJx AG EE :=
let Vra := fresh "Vra" in let Vs0 := fresh "Vs0" in let HUP := fresh "HUP" in let Hch1 := fresh "Hch1" in
let Qceil := fresh "Qceil" in let Qal8 := fresh "Qal8" in let Qtop := fresh "Qtop" in let Qtop64 := fresh "Qtop64" in
let Qsp := fresh "Qsp" in let Qra := fresh "Qra" in let Qs0 := fresh "Qs0" in
lazymatch goal with Hch : achain ?ly (aview _ (w_H ?W) ?mem) (spZ ?regs) (s0Z _) ?ch |- _ =>
assert (Qceil : alloc_ceiling <= spZ regs) by lia;
assert (Qal8 : spZ regs mod 8 = 0) by (let D := fresh "D" in lazymatch goal with Hal32 : spZ regs mod 32 = 0 |- _ =>
pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D; rewrite Hal32, Z.add_0_r in D; rewrite D;
replace (32 * (spZ regs / 32)) with ((4 * (spZ regs / 32)) * 8) by lia; apply Z_mod_mult end);
assert (Qtop : spZ regs < ly_top ly - 16) by lia; assert (Qtop64 : ly_top ly <= 2 ^ 64) by lia; assert (Qsp : spZ regs - 192 + 16 <= spZ regs) by lia;
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; let Hq := fresh "Hq" in pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq);
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; let Hq := fresh "Hq" in pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq);
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict (w_H ?W3) ?msX) =>
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview trasegs (w_H W3) (ms_mem msX) a = aview trasegs (w_H W) mem a)
by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
let F1 := fresh "F1" in pose proof HJx as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; [clear - Ha Qceil; lia | clear - Ha; lia]);
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 2%nat in let i := eval vm_compute in i in
let HRstk := fresh "HRstk" in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i _ HS eq_refl) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
ltac:(evalE AG) ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; let Hq := fresh "Hq" in pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
ltac:(evalE AG) ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; let Hq := fresh "Hq" in pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly (aview trasegs (w_H W3) (ms_mem msX)) (spZ regs - 192) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
lazymatch goal with Hra4 : 4096 <= raZ regs |- _ =>
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ (spZ regs - 192) Hch Qtop64 HUP
(rdword_of_val_mem trasegs _ _ _ _ Vra Qra) (rdword_of_val_mem trasegs _ _ _ _ Vs0 Qs0) Hra4 Qceil Qal8 Qtop Qsp) end
| ] end end.
Ltac keptJ HJc HJx AG Usp E10 RF E58 Hfin HfinS FFS Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2 EFA HFP HFSP HCP F fptac :=
let L := rnLAWS in
lazymatch goal with
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub trasegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat);
[exact HJc | exact HJx | evalE AG; exact Usp | clear; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_GOT_shadow _ _ _ _) => apply (region_kept_val trasegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kg | exact Kg2 | clear; lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_shadow_glob _ _ _ _) => apply (region_kept_val trasegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kc | exact Kc2 | clear; lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_GOT_uar _ _ _ _) => apply (region_kept_val trasegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kgu | exact Kgu2 | clear; lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_uar_glob _ _ _ _) => apply (region_kept_val trasegs _ _ _ A_uar_glob 4 1); [exact Ku | exact Ku2 | clear; lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_GOT_newgif _ _ _ _) => apply (region_kept_val trasegs _ _ _ A_GOT_newgif 8 A_cgif_newgif); [exact Vg | exact Vg2 | clear; lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow | change a with A_shadow_glob | change a with A_GOT_uar | change a with A_uar_glob | change a with A_GOT_newgif ];
keptJ HJc HJx AG Usp E10 RF E58 Hfin HfinS FFS Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2 EFA HFP HFSP HCP F fptac
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_frame_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 10%nat); [exact HJc | evalE AG; first [exact E10 | rewrite E10; apply unsigned_lit_small; lia] | exact HfinS
| rewrite ?EFA; lia | rewrite ?EFA; lia
| first [let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in intros a Ha Hn; exact (inFP_nil _ Hn) | fptac]
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; first [lia | apply (fun H => proj1 (HCP a H)); lia] ]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 45%nat) _ _ _ _ _) =>
eapply (region_kept_frame_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 45%nat); [exact HJc | evalE AG; first [exact RF | rewrite RF; apply unsigned_lit_small; lia] | exact Hfin
| rewrite ?EFA; fold F; change (fs_frame_bytes 1) with 128; lia | rewrite ?EFA; fold F; change (fs_frame_bytes 1) with 128; lia
| first [let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in intros a Ha Hn; exact (inFP_nil _ Hn) | fptac]
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply (fun H => proj1 (HFP a H)); lia ]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 58%nat) _ _ _ _ _) =>
eapply (region_kept_fshadow_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 58%nat); [exact HJc | evalE AG; first [exact E58 | rewrite E58; apply unsigned_lit_small; unfold SB; lia] | exact Hfin
| rewrite ?EFA; fold F; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; unfold SB; lia | rewrite ?EFA; fold F; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; unfold SB; lia
| first [let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in intros a Ha Hn; exact (inFP_nil _ Hn) | fptac]
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; unfold SB in Ha; lia ]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some ?nb) _ _ _ _ ?cs) =>
match goal with Rb : ew _ nb = Z_to_bv 64 ?b, Hin : In (?b', ?sz) (ablocks _ _ _), Hin2 : In (?b'', ?sz') (ablocks _ _ _) |- _ =>
constr_eq b b'; constr_eq b b''; constr_eq sz sz';
eapply (region_kept_block_subw _ L); [exact HJc | evalE AG; first [exact Rb | rewrite Rb; apply unsigned_lit_small; lia] | exact Hin | exact Hin2
| clear; lia | let v := eval vm_compute in (req_size sz) in change (req_size sz) with v; clear; lia | clear; lia | clear; lia
| first [let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in intros a Ha Hn; exact (inFP_nil _ Hn) | fptac] ] end
end.
Ltac rqs Hn := repeat (lazymatch type of Hn with context [req_size ?n] =>
let v := eval vm_compute in (req_size n) in
lazymatch v with Zpos _ => change (req_size n) with v in Hn | Z0 => change (req_size n) with v in Hn end end).
Definition nboxed (P : Prop) : Prop := P.
Ltac nbox H := lazymatch type of H with ?T => change T with (nboxed T) in H end.
Ltac nunbox H := unfold nboxed in H.
Ltac nbox_seps := repeat match goal with H : (_ <= _ \/ _ <= _) |- _ => lazymatch type of H with nboxed _ => fail | _ => nbox H end end.
Ltac clear_frames := repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac slim := clear_frames;
repeat match goal with
| H : st_ok _ _ _ _ |- _ => clear H
| H : _ -> st_ok _ _ _ _ |- _ => clear H
| H : sh_ok _ _ _ _ _ |- _ => clear H
end.
Ltac aconsts HROD HJx Kgot Kcell Kguar Kuar Vgr :=
let Kc := fresh "Kc" in let Ku := fresh "Ku" in let Kg := fresh "Kg" in let Kgu := fresh "Kgu" in
let LAWS := rnLAWS in let TL := rnTL in
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJx)) as (Kc & Ku & Kg & Kgu);
rewrite (tl_got_shadow _ TL), (tl_shadow_cell _ TL) in Kg; rewrite (tl_shadow_cell _ TL) in Kc;
rewrite (tl_got_uar _ TL), (tl_uar_cell _ TL) in Kgu; rewrite (tl_uar_cell _ TL) in Ku;
pose proof (val_mem_of_rdword trasegs _ _ _ _ Kg) as Kgot; pose proof (val_mem_of_rdword trasegs _ _ _ _ Kc) as Kcell;
pose proof (val_mem_of_rdword trasegs _ _ _ _ Kgu) as Kguar; pose proof (val_mem_of_rd32 trasegs _ _ _ _ Ku) as Kuar;
clear Kc Ku Kg Kgu;
pose proof (arodata_val8 _ _ _ A_GOT_newgif A_cgif_newgif TL
(arodata_ok_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJx HROD)
ltac:(unfold A_GOT_newgif; lia) ltac:(unfold A_GOT_newgif; lia)
ltac:(intros x Hx; unfold lib_const_addr, A_GOT_newgif in *; lia)
ltac:(intros kk Hkk; do 8 (destruct kk as [|kk]; [vm_compute; reflexivity|]); lia)) as Vgr.
Ltac keptR HK HJx AG Usp E10 E32 Hfin Hing Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2 EFA :=
lazymatch goal with
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj trasegs _); [exact HK | exact HJx | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?(AG 2%nat) by lia; exact Usp
| lia | unfold TNEWGIF_STK, TRAWNEW_STK, ASTACK; lia | lia | lia | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_GOT_shadow _ _ _ _) => apply (region_kept_val trasegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kg | exact Kg2 | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_shadow_glob _ _ _ _) => apply (region_kept_val trasegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kc | exact Kc2 | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_GOT_uar _ _ _ _) => apply (region_kept_val trasegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kgu | exact Kgu2 | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_uar_glob _ _ _ _) => apply (region_kept_val trasegs _ _ _ A_uar_glob 4 1); [exact Ku | exact Ku2 | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_GOT_newgif _ _ _ _) => apply (region_kept_val trasegs _ _ _ A_GOT_newgif 8 A_cgif_newgif); [exact Vg | exact Vg2 | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow | change a with A_shadow_glob | change a with A_GOT_uar | change a with A_uar_glob | change a with A_GOT_newgif ];
keptR HK HJx AG Usp E10 E32 Hfin Hing Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2 EFA
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_frame_aj trasegs _); [exact HK | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?(AG 10%nat) by lia; rewrite E10; apply unsigned_lit_small; lia
| exact Hfin | rewrite ?EFA; lia | rewrite ?EFA; lia | lia | intros a Ha Hn; first [exact Hn | lia | rqs Hn; zone_lia]]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 32%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj trasegs _); [exact HK | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?(AG 32%nat) by lia; rewrite E32; apply unsigned_lit_small; lia
| exact Hing | lia | change (req_size CGIF_SIZE) with 96; unfold CGIF_SIZE; lia | lia | intros a Ha Hn; first [exact Hn | lia | rqs Hn; zone_lia]]
end.
Ltac keptF HK AG RF E58 HfinX HFP HFSP HEr F EFA :=
lazymatch goal with
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 45%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj trasegs _); [exact HK | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite RF; apply unsigned_lit_small; lia
| exact HfinX | left; change (fs_frame_bytes 1) with 128; rewrite ?EFA; fold F; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn beta; first [exact (fun Hn : False => Hn) | apply HEr; lia]
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply (fun H => proj1 (HFP a H)); lia ]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 58%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj trasegs _); [exact HK | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E58; apply unsigned_lit_small; unfold SB; lia
| exact HfinX | right; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; rewrite ?EFA; fold F; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; first [exact (fun Hn : False => Hn) | let Hn := fresh "Hn" in intros Hn; rqs Hn; unfold SB in Ha; zone_lia]
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; unfold shadow_addr in HFSP; rewrite <- ?SB_SHADOW_OFF in HFSP;
first [lia | apply (fun H => proj1 (HFSP (a - (SB + F / 8)) H)); lia | replace a with (SB + F / 8 + (a - (SB + F / 8))) by lia; apply (fun H => proj1 (HFSP (a - (SB + F / 8)) H)); lia] ]
end.
Ltac keptI Hfr Hpres AG Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2 :=
lazymatch goal with
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some ?n) _ _ _ _ _) =>
eapply region_kept_aview; [evalE AG | intros a Ha; apply Hfr; unfold ESTACK; zone_lia | exact Hpres]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_GOT_shadow _ _ _ _) => apply (region_kept_val trasegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kg | exact Kg2 | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_shadow_glob _ _ _ _) => apply (region_kept_val trasegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kc | exact Kc2 | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_GOT_uar _ _ _ _) => apply (region_kept_val trasegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kgu | exact Kgu2 | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_uar_glob _ _ _ _) => apply (region_kept_val trasegs _ _ _ A_uar_glob 4 1); [exact Ku | exact Ku2 | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_GOT_newgif _ _ _ _) => apply (region_kept_val trasegs _ _ _ A_GOT_newgif 8 A_cgif_newgif); [exact Vg | exact Vg2 | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow | change a with A_shadow_glob | change a with A_GOT_uar | change a with A_uar_glob | change a with A_GOT_newgif ];
keptI Hfr Hpres AG Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2
end.
Ltac subregion_tac :=
unfold subregion; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks];
split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|];
let c := fresh "c" in let Hc := fresh "Hc" in intros c Hc; cbn in Hc |- *;
first [exact Hc | solve [destruct Hc] | tauto].
Ltac submem_to := repeat (first [apply submem_keep; [subregion_tac|] | apply submem_drop]); apply submem_nil.
Ltac incl_lit_tac :=
let x := fresh "x" in let Hx := fresh "Hx" in
intros x Hx; cbn in Hx; cbn;
repeat (destruct Hx as [<- | Hx]; [repeat (first [left; reflexivity | right]) |]); destruct Hx.
Ltac set_regs_rec HS N vals i rl :=
lazymatch rl with
| [] => idtac
| ?r :: ?rl' =>
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in let Hv := fresh "Hv" in
let n := eval vm_compute in (N + i)%nat in
assert (Hv : sv_denot Ev (SOff n 0) = getr (ms_regs msx) r);
[ cbn [sv_denot]; rewrite Z.add_0_r; rewrite Z_to_bv_bv_unsigned; change n with (N + i)%nat;
rewrite (ew_havoc_new _ N vals i (Z_to_bv 64 0)) by (cbn [length]; lia); cbn [nth ms_regs restrict]; reflexivity | ];
pose proof (ast_ok_set_reg_fp trasegs Ev ssx msx r (SOff n 0) HS ltac:(vm_compute; reflexivity) Hv) as HS3;
clear HS Hv; rename HS3 into HS; norm_ss HS; set_regs_rec HS N vals (S i) rl' end
end.
Ltac rn_join HS target N deads :=
norm_ss HS;
let tg := eval red in target in
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let rs := eval cbn [ss_mem] in (ss_mem tg) in
pose proof (st_ok_submem trasegs Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end;
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
pose proof (st_ok_facts_incl3 trasegs Ex ssx msx fa cs al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS;
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval red in deads in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
let vals' := eval cbn [map ms_regs restrict] in vals in
pose proof (st_ok_havoc trasegs N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS N vals' 0%nat dl end;
norm_ss HS;
lazymatch type of HS with st_ok _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg] end.
Ltac jafter_stretch_keep HS k regs2 mem2 clob newpc idxs HS2 :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
let rs := eval vm_compute in (pick (ss_mem ss) idxs) in
pose proof (st_ok_after_stretch segs k E ss ms regs2 mem2 rs newpc clob HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS2;
let ss2 := eval vm_compute in (ss_after_stretch ss rs k clob newpc) in
change (ss_after_stretch ss rs k clob newpc) with ss2 in HS2
end.
Lemma denot_mul3 : forall E n i, ew E n = Z_to_bv 64 i -> 0 <= i < 65536 ->
sv_denot E (SMd M_MUL (SOff n 0) (SLit 3)) = Z_to_bv 64 (3 * i).
Proof.
intros E n i Hn Hi. rewrite denot_lit_U. f_equal.
rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E n i Hn) by lia. rewrite U_SLit.
rewrite (zcanon_id 3) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Definition ng_rattr (attr : Z) : Z := Z.lor ((attr * 2 ^ 62) mod 2 ^ 64 / 2 ^ 63) (Z.land (attr / 8) 2).
Lemma land2_small : forall x, 0 <= x -> 0 <= Z.land x 2 < 4.
Proof.
intros x Hx. assert (H0 : 0 <= Z.land x 2) by (apply (proj2 (Z.land_nonneg x 2)); right; lia).
split; [exact H0|]. destruct (Z.eq_dec (Z.land x 2) 0) as [-> | Hnz]; [lia|].
apply (Z.log2_lt_pow2 (Z.land x 2) 2); [lia|].
pose proof (Z.log2_land x 2 Hx ltac:(lia)) as HL. change (Z.log2 2) with 1 in HL. lia.
Qed.
Lemma ng_rattr_range : forall attr, 0 <= attr -> 0 <= ng_rattr attr < 4.
Proof.
intros attr Ha. unfold ng_rattr.
remember ((attr * 2 ^ 62) mod 2 ^ 64 / 2 ^ 63) as a eqn:Ea. remember (Z.land (attr / 8) 2) as b eqn:Eb.
assert (Ha2 : 0 <= a < 2).
{ subst a. pose proof (Z.mod_pos_bound (attr * 2 ^ 62) (2 ^ 64) ltac:(lia)) as Hm.
split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia|]; change (2 ^ 63 * 2) with (2 ^ 64); lia]. }
pose proof (land2_small (attr / 8) ltac:(apply Z.div_pos; lia)) as Hb2. rewrite <- Eb in Hb2.
clear Ea Eb.
assert (Hca : a = 0 \/ a = 1) by lia. assert (Hcb : b = 0 \/ b = 1 \/ b = 2 \/ b = 3) by lia.
destruct Hca as [-> | ->]; destruct Hcb as [-> | [-> | [-> | ->]]];
match goal with |- 0 <= ?e < 4 => let v := eval vm_compute in e in change e with v end; lia.
Qed.
Lemma U_ng_rattr : forall E n attr, ew E n = Z_to_bv 64 attr -> 0 <= attr < 2 ^ 32 ->
U E (SAlu ALU_OR (SAlu ALU_SRL (SAlu ALU_SLL (SOff n 0) (SLit 62)) (SLit 63)) (SAlu ALU_AND (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SLit 2)))
= ng_rattr attr.
Proof.
intros E n attr Hn Ha. repeat (rewrite U_SAlu; cbn [zalu_raw]).
rewrite !U_SLit. rewrite (U_atom E n attr Hn) by lia.
change (Z.land (zcanon 62) 63) with 62. change (Z.land (zcanon 63) 63) with 63. change (Z.land (zcanon 3) 63) with 3. change (zcanon 2) with 2.
rewrite (Z.shiftl_mul_pow2 attr 62) by lia. rewrite !Z.shiftr_div_pow2 by lia.
unfold ng_rattr.
pose proof (Z.mod_pos_bound (attr * 2 ^ 62) (2 ^ 64) ltac:(lia)) as Hm.
assert (Hq : 0 <= (attr * 2 ^ 62) mod 2 ^ 64 / 2 ^ 63 < 2).
{ split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia|]; change (2 ^ 63 * 2) with (2 ^ 64); lia]. }
assert (Hd8 : 0 <= attr / 8 < 2 ^ 29) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
pose proof (land2_small (attr / 8) ltac:(lia)) as Hl.
unfold zcanon, M64. rewrite (Z.mod_small (_ / 2 ^ 63)) by lia. rewrite (Z.mod_small (attr / 8)) by lia. rewrite (Z.mod_small (Z.land _ 2)) by lia.
pose proof (ng_rattr_range attr ltac:(lia)) as Hr. unfold ng_rattr in Hr. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma U_sext16_mod : forall E a v, U E a = v -> 0 <= v < 2 ^ 16 -> U E (SExt true 16 a) mod 2 ^ 16 = v.
Proof.
intros E a v Ha Hv. rewrite U_SExt, Ha. change (2 ^ Z.of_N 16) with (2 ^ 16). rewrite (Z.mod_small v) by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 16) with (2 ^ 16). change (2 ^ 16 / 2) with (2 ^ 15).
unfold zcanon, M64.
destruct (Z_lt_ge_dec v (2 ^ 15)) as [Hl | Hh].
- rewrite (Z.mod_small (v + 2 ^ 15)) by lia. replace (v + 2 ^ 15 - 2 ^ 15) with v by lia. rewrite (Z.mod_small v) by lia. apply Z.mod_small. lia.
- replace ((v + 2 ^ 15) mod 2 ^ 16) with (v + 2 ^ 15 - 2 ^ 16).
2:{ replace (v + 2 ^ 15) with ((v + 2 ^ 15 - 2 ^ 16) + 1 * 2 ^ 16) at 2 by lia. rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity. }
replace (v + 2 ^ 15 - 2 ^ 16 - 2 ^ 15) with ((v - 2 ^ 16 + 2 ^ 64) + (-1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full.
rewrite (Z.mod_small (v - 2 ^ 16 + 2 ^ 64)) by lia.
replace (v - 2 ^ 16 + 2 ^ 64) with (v + (2 ^ 48 - 1) * 2 ^ 16) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
