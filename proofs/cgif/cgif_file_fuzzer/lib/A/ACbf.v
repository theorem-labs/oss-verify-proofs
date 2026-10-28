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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n YI0s YCbw.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8j ACbc.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac zone_goal := unfold zone2, off_img, in_app, app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL;
unfold RAW_SIZE, CGIF_SIZE, FRAME_SIZE; change (req_size 96) with 96; change (req_size 48) with 48; change (req_size 40) with 40;
change (req_size 72) with 72; change (req_size 32) with 32.
Ltac clear_disj := repeat match goal with H : _ \/ _ |- _ => clear H | H : off_img _ _ |- _ => clear H | H : in_app _ _ |- _ => clear H | H : zone2 _ _ |- _ => clear H end.
Ltac lia_nd := solve [clear_disj; lia].
Ltac zone_lia ::=
try zone_goal;
first [ lia_nd
| match goal with H : _ \/ _ |- _ => solve [destruct H; clear_disj; lia] end
| match goal with H : off_img _ _ |- _ => solve [unfold off_img in H; destruct H; clear_disj; lia] end
| match goal with H : in_app _ _ |- _ =>
solve [unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in H; req_lits; destruct H as [? [?|[? ?]]]; clear_disj; lia] end
| match goal with H : zone2 _ _ |- _ =>
solve [unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in H; req_lits; destruct H as [[?|?] [?|?]]; clear_disj; lia] end
| lia
| zones; req_lits; lia ].
Ltac rnLAWS := lazymatch goal with L : AR_laws _ _ |- _ => L end.
Ltac rnTL := lazymatch goal with T : PALib _ |- _ => T end.
Ltac rnB := lazymatch goal with L : AR_laws _ ?Bv |- _ => Bv end.
Ltac rnTLF := lazymatch goal with T : PALibF _ |- _ => T end.
Ltac rnFFL := lazymatch goal with H : frame_flag_lawP _ _ |- _ => H end.
Ltac rnHEI E := lazymatch goal with H : img_env _ _ E |- _ => H | _ => fail "rnHEI: no img_env fact for" E end.
Ltac img_facts E :=
let H := rnHEI E in
repeat match goal with G : ew E 241%nat = _ |- _ => clear G | G : ew E 242%nat = _ |- _ => clear G
| G : ew E 248%nat = _ |- _ => clear G | G : ew E 253%nat = _ |- _ => clear G end;
let E241 := fresh "E241" in let E242 := fresh "E242" in let E248 := fresh "E248" in let E253 := fresh "E253" in
pose proof (img_env_atomP E 241%nat H ltac:(unfold A_TEXT, A_LIM; lia)) as E241;
pose proof (img_env_atomP E 242%nat H ltac:(unfold A_TEXT, A_LIM; lia)) as E242;
pose proof (img_env_atomP E 248%nat H ltac:(unfold A_TEXT, A_LIM; lia)) as E248;
pose proof (img_env_atomP E 253%nat H ltac:(unfold A_TEXT, A_LIM; lia)) as E253.
Ltac img_hull_facts :=
let TLF := rnTLF in
pose proof (pa_obj_img 0 ltac:(lia)) as Hob241; pose proof (pa_obj_img 1 ltac:(lia)) as Hob242;
pose proof (pa_obj_img 7 ltac:(lia)) as Hob248; pose proof (pa_obj_img 12 ltac:(lia)) as Hob253;
cbv [A_OBJ Nat.add] in Hob241, Hob242, Hob248, Hob253;
pose proof (palf_uar_img _ TLF) as Huar; pose proof (palf_uar_al _ TLF) as Huar4.
Ltac nat_side := first [ apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); vm_compute; reflexivity
| apply (proj1 (PeanoNat.Nat.eqb_neq _ _)); vm_compute; reflexivity ].
Ltac rebaseE HS AG HEv :=
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
Ltac evalE AG :=
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
repeat match goal with |- context [ew Ev ?n] => lazymatch (eval cbv in (Nat.ltb n 33)) with true => rewrite (AG n) by lia end end end;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
repeat match goal with H : bv_unsigned (ew ?Ex 2) = _ |- context [bv_unsigned (ew ?Ex 2)] => rewrite H end;
rewrite ?unsigned_lit_small by (unfold SB; lia); unfold SB; first [reflexivity | lia | idtac].
Ltac awrR_rec AG fpos F EFA :=
lazymatch goal with
| |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ (YP09.mkRegion _ _ _ ?wlo ?whi _ :: _) _ _ _ _ _ _ _ =>
first
[ apply awr_ok_cons_ro; [cbn; lia|]
| lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 529%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 529%nat); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists 2, fpos; split; [left; reflexivity|]; right;
unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 2 / 8) with 32; rewrite ?EFA; fold F; unfold SB; clear - Ha; lia
| ]
| |- awr_ok _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 516%nat); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists 2, fpos; split; [left; reflexivity|]; left;
unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 2) with 256; rewrite ?EFA; fold F; clear - Ha; lia
| ]
| |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | evalE AG | cbn; lia | cbn; lia |]
| |- awr_ok _ (YP09.mkRegion (Some 534%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
let Hin := lazymatch goal with H : In (_, 48) (ablocks _ _ _) |- _ => H end in
lazymatch type of Hin with In (?res, 48) _ =>
let Ar := lazymatch goal with A : forall blc lyq ownq i, In (res, 48) blc -> _ |- _ => A end in
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 534%nat); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; replace a with (res + (a - res)) by lia; apply Ar; [exact Hin | clear - Ha; lia]
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
| YP09.mkRegion (Some n) _ _ _ _ _ :: _ => constr:(0%nat)
| _ :: ?tl => let i := idx_of_base tl n in constr:(S i)
end.
Ltac fs_ro HS :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 529%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS | st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 529%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region _ Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS  end.
Ltac fs_rw HS E529 Hp :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 529%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 32) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 32 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite E529, unsigned_lit_small by (unfold SB; lia);
intros o Ho; apply (apresent_writable _); unfold shadow_addr in Hp; rewrite <- SB_SHADOW_OFF in Hp;
apply (proj1 (Hp o ltac:(clear - Ho; lia)))))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS | st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 529%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region _ Ex ssx msx i r (set_window r 0 32) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 32 (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite E529, unsigned_lit_small by (unfold SB; lia);
intros o Ho; apply (apresent_writable _); unfold shadow_addr in Hp; rewrite <- SB_SHADOW_OFF in Hp;
apply (proj1 (Hp o ltac:(clear - Ho; lia)))))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS  end.
Ltac oblF HJx HE10 HE35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal :=
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 10 ?c)) ?len =>
lazymatch type of HE10 with _ = Z_to_bv 64 ?cfgp =>
first [ rewrite (U_atom_off Ex 10 cfgp c); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE10 | lia | lia]
| rewrite (U_atom Ex 10 cfgp); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE10 | lia] ];
eapply (obl_of_range _ _ _ Ex (SOff 35 0) _ len cfgp 40);
[ let L := rnLAWS in eapply (range_addressable_entry_frame _ _ L); [exact HJx | exact Hfin | exact Hcid0 | exact Hflo | exact Hfhi | exact Hfal
| intros x Hx; exfalso; exact (inFP_nil x Hx) | exact HAR | exact HRA]
| rewrite (U_atom Ex 35 SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE35 | unfold SB; lia]
| lia | lia ] end end.
Ltac oblG HJx HE32 HE35 Hing :=
let L := rnLAWS in
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 32 ?c)) ?len =>
lazymatch type of HE32 with _ = Z_to_bv 64 ?g =>
first [ rewrite (U_atom_off Ex 32 g c); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE32 | lia | lia]
| rewrite (U_atom Ex 32 g); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE32 | lia] ];
eapply (obl_of_block _ _ L _ _ _ _ _ Ex (SOff 35 0) _ len g CGIF_SIZE (proj1 HJx) Hing);
[ rewrite (U_atom Ex 35 SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE35 | unfold SB; lia]
| lia | change (req_size CGIF_SIZE) with 96; lia ] end end.
Ltac oblR HJx HE536 HE35 Hin :=
let L := rnLAWS in
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 534 ?c)) ?len =>
lazymatch type of HE536 with _ = Z_to_bv 64 ?res =>
first [ rewrite (U_atom_off Ex 534 res c); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE536 | lia | lia]
| rewrite (U_atom Ex 534 res); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE536 | lia] ];
eapply (obl_of_block _ _ L _ _ _ _ _ Ex (SOff 35 0) _ len res 48 (proj1 HJx) Hin);
[ rewrite (U_atom Ex 35 SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE35 | unfold SB; lia]
| lia | change (req_size 48) with 48; lia ] end end.
Ltac obl_blk HJx HEn HEbx Hin :=
let L := rnLAWS in
lazymatch goal with |- range_addressable _ (U ?Ex (SOff ?bx 0)) (U _ (SOff ?n ?c)) ?len =>
lazymatch type of HEn with _ = Z_to_bv 64 ?p =>
lazymatch type of Hin with In (_, ?sz) _ =>
first [ rewrite (U_atom_off Ex n p c); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HEn | lia | lia]
| rewrite (U_atom Ex n p); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HEn | lia] ];
eapply (obl_of_block _ _ L _ _ _ _ _ Ex (SOff bx 0) _ len p sz (proj1 HJx) Hin);
[ rewrite (U_atom Ex bx SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HEbx | unfold SB; lia]
| lia | let v := eval vm_compute in (req_size sz) in change (req_size sz) with v; lia ] end end end.
Ltac relow HS AG E10 E32 E10n E32n :=
try clear E10n; try clear E32n;
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
lazymatch type of E10 with _ = ?v10 => assert (E10n : ew Ev 10 = v10) by (rewrite (AG 10%nat) by lia; exact E10) end;
lazymatch type of E32 with _ = ?v32 => assert (E32n : ew Ev 32 = v32) by (rewrite (AG 32%nat) by lia; exact E32) end | st_ok _ ?Ev _ _ =>
lazymatch type of E10 with _ = ?v10 => assert (E10n : ew Ev 10 = v10) by (rewrite (AG 10%nat) by lia; exact E10) end;
lazymatch type of E32 with _ = ?v32 => assert (E32n : ew Ev 32 = v32) by (rewrite (AG 32%nat) by lia; exact E32) end  end.
Ltac creg HS AG EE :=
lazymatch goal with |- getr _ ?r = getr _ _ =>
let R := fresh "R" in prreg HS r R; rewrite R; clear R;
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite AG by lia;
apply EE; reflexivity end.
Ltac add_flag_region HS AG E528 Hp HFLrng HFLown HnoG HnoC HnoF :=
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 528%nat) 0 1 0 1 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite ?ew_ewset_other by lia; rewrite E528, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable _); lazymatch goal with |- apresent _ _ (?fl + ?oo) => replace (fl + oo) with fl by lia end; exact Hp)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; evalE AG;
repeat split; first [flag_disj_cheap HFLown
| zone_lia |
lazymatch goal with |- ?fl + 1 <= ?x + ?l \/ ?x + ?h <= ?fl + 0 =>
destruct (Z_lt_ge_dec fl (x + l)); [left; lia|]; destruct (Z_lt_ge_dec fl (x + h)); [exfalso | right; lia];
first [apply (HnoG fl); [lia | exact HFLown] | apply (HnoC fl); [lia | exact HFLown] | apply (HnoF fl); [lia | exact HFLown]
| match goal with Hn : forall a, _ -> ~ aowned _ _ _ a |- _ => apply (Hn fl); [lia | exact HFLown] end
| match goal with |- ?g => idtac "DISJFAIL" g end] end
| match goal with |- ?g => idtac "DISJ?" g end ])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS | st_ok _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 528%nat) 0 1 0 1 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite ?ew_ewset_other by lia; rewrite E528, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable _); lazymatch goal with |- apresent _ _ (?fl + ?oo) => replace (fl + oo) with fl by lia end; exact Hp)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; evalE AG;
repeat split; first [flag_disj_cheap HFLown
| zone_lia |
lazymatch goal with |- ?fl + 1 <= ?x + ?l \/ ?x + ?h <= ?fl + 0 =>
destruct (Z_lt_ge_dec fl (x + l)); [left; lia|]; destruct (Z_lt_ge_dec fl (x + h)); [exfalso | right; lia];
first [apply (HnoG fl); [lia | exact HFLown] | apply (HnoC fl); [lia | exact HFLown] | apply (HnoF fl); [lia | exact HFLown]
| match goal with Hn : forall a, _ -> ~ aowned _ _ _ a |- _ => apply (Hn fl); [lia | exact HFLown] end
| match goal with |- ?g => idtac "DISJFAIL" g end] end
| match goal with |- ?g => idtac "DISJ?" g end ])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS  end.
Ltac wrangeR AG fpos F EFA EFL :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (r & Hin & Hr); rewrite ?EFA, ?EFL;
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; intros Hr;
first [ exfalso; clear - Hr; lia
| right; clear - Hr; lia
| left; left; clear - Hr; unfold TRAWNEW_STK, ASTACK; lia
| left; right; right; right; exists 2, fpos; split; [left; reflexivity|];
first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 2) with 256; rewrite ?EFA; fold F; clear - Hr; lia
| right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 2 / 8) with 32; rewrite ?EFA; fold F; unfold SB; clear - Hr; lia ]
| left; match goal with A : forall blc lyq ownq i, In (?r, 48) blc -> _, Hin : In (?r, 48) (ablocks _ _ _) |- _ =>
replace a with (r + (a - r)) by lia; apply A; [exact Hin | clear - Hr; lia] end
| match goal with |- ?g => match type of Hr with ?t => idtac "WRFAIL" t g end end; fail 2 "wrangeR" ]
| ]);
destruct Hin.
Ltac flag0 E528 EFL :=
let msr := fresh "msr" in let HSr := fresh "HSr" in let HR := fresh "HR" in let V := fresh "V" in
intros msr HSr; rewrite ?EFL;
lazymatch type of HSr with st_ok_pi _ _ ?Ex ?ssx _ =>
pose proof (st_ok_pi_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR;
lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex (ms_mem msr) n _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E528; apply unsigned_lit_small; lia)
ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end | st_ok _ ?Ex ?ssx _ =>
pose proof (st_ok_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR;
lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex (ms_mem msr) n _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E528; apply unsigned_lit_small; lia)
ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end  end;
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
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg; clear - Hb Hrg; lia|]);
destruct Hin
| clear HUP; rename HUP' into HUP ] end end.
Ltac exitR RET RUNF HS HJx AG fpos F cfgp g E528 E529 Hfin HfinS HingX EE Hra HEV EFA EFL :=
let HFLpres' := fresh "HFLpres'" in let HFLown := fresh "HFLown'" in let HFLrng := fresh "HFLrng'" in
let HFpres' := fresh "HFpres'" in let HFSpres' := fresh "HFSpres'" in
let HCpres' := fresh "HCpres'" in let HGpres' := fresh "HGpres'" in
let HnoG := fresh "HnoG" in let HnoC := fresh "HnoC" in let HnoF := fresh "HnoF" in
let FFL := rnFFL in let LAWS := rnLAWS in destruct (FFL _ _ _ _ _ 2 fpos (proj1 HJx) Hfin) as (HFLpres' & HFLown & HFLrng); rewrite ?EFL in HFLpres'; rewrite ?EFL in HFLown; rewrite ?EFL in HFLrng; fold F in HFLrng;
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJx) Hfin) as (_ & _ & HFpres' & HFSpres'); change (fs_frame_bytes 2) with 256 in HFpres', HFSpres';
change (256 / 8) with 32 in HFSpres'; rewrite ?EFA in HFpres'; rewrite ?EFA in HFSpres'; fold F in HFpres', HFSpres';
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ (proj1 HJx) HfinS) as (_ & _ & HCpres' & _); rewrite ?EFA in HCpres';
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE (proj1 HJx) HingX) as (_ & _ & _ & _ & HGpres' & _); change (req_size CGIF_SIZE) with 96 in HGpres';
lazymatch type of HGpres' with forall a, _ -> _ /\ ~ aowned ?B ?lyx ?Sx a =>
assert (HnoG : forall a, g <= a < g + 96 -> ~ aowned B lyx Sx a) by (intros a Ha; exact (proj2 (HGpres' a Ha)));
assert (HnoC : forall a, cfgp <= a < cfgp + 40 -> ~ aowned B lyx Sx a) by (intros a Ha; apply (fun H => proj2 (HCpres' a H)); lia);
assert (HnoF : forall a, F <= a < F + 256 -> ~ aowned B lyx Sx a) by (intros a Ha; exact (proj2 (HFpres' a Ha)));
try (match goal with Hin : In (?r, 48) (ablocks _ lyx Sx) |- _ =>
let HRp := fresh "HRp" in let HnoR := fresh "HnoR" in
destruct (al_blocks _ _ LAWS _ _ _ _ _ r 48 (proj1 HJx) Hin) as (_ & _ & _ & _ & HRp & _); change (req_size 48) with 48 in HRp;
assert (HnoR : forall a, r <= a < r + 48 -> ~ aowned B lyx Sx a) by (intros a Ha; exact (proj2 (HRp a Ha))); clear HRp end) end;
fs_rw HS E529 HFSpres';
add_flag_region HS AG E528 HFLpres' HFLrng HFLown HnoG HnoC HnoF;
paj_run_flag_sh RUNF HS HJx; [lia | wrangeR AG fpos F EFA EFL | flag0 E528 EFL |];
let R1 := fresh "R1" in let R10 := fresh "R10" in
prreg HS (1%bv : bv 5) R1; prreg HS (10%bv : bv 5) R10;
lazymatch goal with |- SRr _ ?Wx _ _ =>
eapply (RET Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end;
let mat' := fresh "mat'" in intros mat'; unfold rn_post, apost_base;
lazymatch type of HJx with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx _ _ _ _ =>
lazymatch goal with |- exists ly' S' regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists lyx, Sx, rg, mm, mdx end end;
split; [rewrite R1; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Hra; reflexivity|];
split; [cbn [ms_mem]; eapply (ajournal_mono_k _ _); [apply (ajournal_materialize _ _ LAWS pa_segs_low); exact HJx | rewrite HEV; lia]|];
split; [apply aregs_preserved_eqs; creg HS AG EE|];
rewrite R10.
Ltac rqs Hn := repeat (lazymatch type of Hn with context [req_size ?n] =>
let v := eval vm_compute in (req_size n) in
lazymatch v with Zpos _ => change (req_size n) with v in Hn | Z0 => change (req_size n) with v in Hn end end).
Ltac clear_frames := repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac aconsts HROD HJx Kgot Kcell Kguar Kuar Vgr :=
let Kc := fresh "Kc" in let Ku := fresh "Ku" in let Kg := fresh "Kg" in let Kgu := fresh "Kgu" in
let LAWS := rnLAWS in let TL := rnTL in let TLF := rnTLF in
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJx)) as (Kc & Ku & Kg & Kgu);
rewrite (pal_got_shadow _ TL), (pal_cell _ TL) in Kg; rewrite (pal_cell _ TL) in Kc;
rewrite (palf_got_uar _ TLF) in Kgu;
pose proof (val_mem_of_rdword _ _ _ _ _ Kg) as Kgot; pose proof (val_mem_of_rdword _ _ _ _ _ Kc) as Kcell;
pose proof (val_mem_of_rdword _ _ _ _ _ Kgu) as Kguar; pose proof (val_mem_of_rd32 _ _ _ _ _ Ku) as Kuar;
clear Kc Ku Kg Kgu;
let HG7 := lazymatch goal with H : forall Hh mm, arodata_okP _ _ _ _ (aview _ Hh mm) -> val_mem _ (mrestrict Hh mm) _ 8 _ |- _ => H end in
pose proof (HG7 _ _ (arodata_ok_journalP _ _ _ pa_relro_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJx HROD)) as Vgr.
Ltac keptR HK HJx AG Usp E10 E32 Hfin Hing Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2 :=
let Bv := rnB in
lazymatch goal with
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj _ _); [exact HK | exact HJx | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?(AG 2%nat) by lia; exact Usp
| lia | unfold TRAWNEW_STK, ASTACK; lia | lia | lia | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 241%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 0) (pa_val (A_OBJ 0)) 8 (pa_val (A_OBJ 12)));
[exact (H (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kg | exact Kg2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 253%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 12) (pa_val (A_OBJ 12)) 8 SHADOW_OFF);
[exact (H (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kc | exact Kc2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 242%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 1) (pa_val (A_OBJ 1)) 8 (as_uar_cell Bv));
[exact (H (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kgu | exact Kgu2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 43%nat) _ _ _ _ _) =>
apply (region_kept_val_at Ex _ _ 43%nat (as_uar_cell Bv) 4 1); [evalE AG | exact Ku | exact Ku2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 248%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 7) (pa_val (A_OBJ 7)) 8 (pa_val A_TEXT + AF_asan3_cgif_raw_newgif));
[exact (H (A_OBJ 7) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Vg | exact Vg2 | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_frame_aj _ _); [exact HK | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?(AG 10%nat) by lia; rewrite E10; apply unsigned_lit_small; lia
| exact Hfin | lia | lia | lia | intros a Ha Hn; first [exact Hn | rqs Hn; zone_lia]]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 32%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj _ _); [exact HK | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?(AG 32%nat) by lia; rewrite E32; apply unsigned_lit_small; lia
| exact Hing | lia | change (req_size CGIF_SIZE) with 96; unfold CGIF_SIZE; lia | lia | intros a Ha Hn; first [exact Hn | rqs Hn; zone_lia]]
end.
Ltac shadow_vs Ha Hn :=
exfalso;
lazymatch type of Hn with ?p <= ?a < _ =>
lazymatch goal with Hin : in_app p ?m |- _ =>
lazymatch type of Ha with _ <= a < SB + ?Fv / 8 + ?k =>
lazymatch goal with H4 : 4096 <= Fv |- _ =>
lazymatch goal with Hce : Fv + _ <= alloc_ceiling |- _ =>
lazymatch goal with Hc1 : _ <= alloc_ceiling <= _ |- _ =>
refine (fshadow_not_app Fv k p m a H4 _ Hin _ _);
[ revert Hce Hc1; clear; intros; lia
| revert Ha; clear; unfold SB; intros Ha; lia | first [exact Hn | revert Hn; clear; intros Hn; rqs Hn; lia] ] end end end end end end.
Ltac keptF HK AG RF E529 HfinX HFP HFSP HEr F :=
lazymatch goal with
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj _ _); [exact HK | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite RF; apply unsigned_lit_small; lia
| exact HfinX | left; change (fs_frame_bytes 2) with 256; fold F; lia | intros a Ha; cbn beta; first [exact (fun Hn : False => Hn) | apply HEr; lia]
| intros a Ha; apply (fun H => proj1 (HFP a H)); lia ]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 529%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj _ _); [exact HK | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E529; apply unsigned_lit_small; unfold SB; lia
| exact HfinX | right; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 2 / 8) with 32; fold F; lia
| intros a Ha; first [exact (fun Hn : False => Hn) | let Hn := fresh "Hn" in intros Hn; shadow_vs Ha Hn]
| intros a Ha; lia ]
end.
Ltac keptI Hfr Hpres AG Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2 :=
let Bv := rnB in
lazymatch goal with
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 241%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 0) (pa_val (A_OBJ 0)) 8 (pa_val (A_OBJ 12)));
[exact (H (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kg | exact Kg2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 253%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 12) (pa_val (A_OBJ 12)) 8 SHADOW_OFF);
[exact (H (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kc | exact Kc2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 242%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 1) (pa_val (A_OBJ 1)) 8 (as_uar_cell Bv));
[exact (H (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kgu | exact Kgu2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 43%nat) _ _ _ _ _) =>
apply (region_kept_val_at Ex _ _ 43%nat (as_uar_cell Bv) 4 1); [evalE AG | exact Ku | exact Ku2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 248%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 7) (pa_val (A_OBJ 7)) 8 (pa_val A_TEXT + AF_asan3_cgif_raw_newgif));
[exact (H (A_OBJ 7) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Vg | exact Vg2 | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some ?n) _ _ _ _ _) =>
eapply region_kept_aview; [evalE AG | intros a Ha; apply Hfr; unfold ESTACK; zone_lia | exact Hpres]
end.
Ltac subregion_tac :=
unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
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
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in let Hv := fresh "Hv" in
let n := eval vm_compute in (N + i)%nat in
assert (Hv : sv_denot Ev (SOff n 0) = getr (ms_regs msx) r);
[ cbn [sv_denot]; rewrite Z.add_0_r; rewrite Z_to_bv_bv_unsigned; change n with (N + i)%nat;
rewrite (ew_havoc_new _ N vals i (Z_to_bv 64 0)) by (cbn [length]; lia); cbn [nth ms_regs restrict]; reflexivity | ];
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx r (SOff n 0) HS ltac:(vm_compute; reflexivity) Hv) as HS3;
clear HS Hv; rename HS3 into HS; norm_ss HS; set_regs_rec HS N vals (S i) rl' | st_ok _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in let Hv := fresh "Hv" in
let n := eval vm_compute in (N + i)%nat in
assert (Hv : sv_denot Ev (SOff n 0) = getr (ms_regs msx) r);
[ cbn [sv_denot]; rewrite Z.add_0_r; rewrite Z_to_bv_bv_unsigned; change n with (N + i)%nat;
rewrite (ew_havoc_new _ N vals i (Z_to_bv 64 0)) by (cbn [length]; lia); cbn [nth ms_regs restrict]; reflexivity | ];
pose proof (ast_ok_set_reg_fp _ Ev ssx msx r (SOff n 0) HS ltac:(vm_compute; reflexivity) Hv) as HS3;
clear HS Hv; rename HS3 into HS; norm_ss HS; set_regs_rec HS N vals (S i) rl'  end
end.
Ltac rn_join HS target N deads :=
norm_ss HS;
let tg := eval red in target in
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let rs := eval cbn [ss_mem] in (ss_mem tg) in
pose proof (st_ok_pi_submem Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let rs := eval cbn [ss_mem] in (ss_mem tg) in
pose proof (st_ok_submem _ Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS  end;
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
pose proof (st_ok_pi_facts_incl3 Ex ssx msx fa cs al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
pose proof (st_ok_facts_incl3 _ Ex ssx msx fa cs al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS  end;
norm_ss HS;
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval red in deads in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
let vals' := eval cbn [map ms_regs restrict] in vals in
pose proof (st_ok_pi_havoc_hi N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS N vals' 0%nat dl | st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval red in deads in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
let vals' := eval cbn [map ms_regs restrict] in vals in
pose proof (st_ok_havoc _ N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS N vals' 0%nat dl  end;
norm_ss HS;
lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg] | st_ok _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg]  end.
Ltac rn_prelude :=
let LAWS := rnLAWS in let B := lazymatch goal with L : AR_laws _ ?Bv |- _ => Bv end in
intros RC ly S W regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx rest cid pos E0 E W3 ly3 S3 ms3 md3 k fpos res
HPRE Hchne Hal32 HROD HCFG Hcfg HPerm Hev HE0 HE HNOW Hsg HS;
pose proof pa_wx as Hwx; pose proof pa_segs_low as Hsegs;
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5); assert (FFS : TRAWNEW_STK = 16576) by reflexivity;
assert (HEV : EV_RAWNEW = 4) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity;
destruct HCFG as (Hfin & Hcid0 & Hfal & Hflo & Hfhi & Hcal & HRA);
destruct HE0 as (EE & E10 & E32 & Usp); destruct HE as (AG & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & RF & E528 & E529 & Rres & E41 & E42 & E43 & HEI);
destruct HNOW as (HJ3 & Hk3 & Hfrs3 & Eab3 & Hres4096 & Tres & Ares);
pose proof (proj1 HJ3) as HAR3;
destruct (frames_bounds _ _ LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfhigh);
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img;
assert (Hing : In (g, CGIF_SIZE) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; left; reflexivity);
destruct (al_blocks _ _ LAWS ly S W mem md g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _); pose proof (proj1 Hgh_ia) as Hgh;
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img;
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh;
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR (proj1 (proj2 HJ3))) as (_ & EFA3 & _);
assert (EFL3 : forall c p, flag_addr ly3 c p = flag_addr ly c p) by (intros c p; unfold flag_addr; pose proof (EFA3 c p) as X; unfold frame_addr in X; lia);
assert (Hfin3 : In (2, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity);
assert (HfinS3 : In (cid, pos) (frames S3)) by (rewrite Hfrs3; right; exact Hfin);
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR3 Hfin3) as (HFal & [HFhi _] & HFpres3 & HFSpres3);
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hfin3) as HFapp_img;
destruct (frames_bounds _ _ LAWS _ _ _ _ _ 2 fpos HAR3 Hfin3) as (HF4096 & HFceil & HFhigh);
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hfin3) as HFhigh_img;
change (fs_frame_bytes 2) with 256 in *; change (256 / 8) with 32 in HFSpres3; rewrite !EFA3 in *;
set (F := frame_addr ly 2 fpos) in *; set (FL := flag_addr ly 2 fpos) in *;
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia);
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity);
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia)    ;
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia);
assert (Hres_in : In (res, 48) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact Eab3|]; apply in_app_iff; right; left; reflexivity);
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact Eab3|]; apply in_app_iff; left; exact Hing);
destruct (al_blocks _ _ LAWS _ _ _ _ _ res 48 HAR3 Hres_in) as (Hr16 & Hr4096 & Hrceil & Hrh_ia & Hrpres3 & _); pose proof (proj1 Hrh_ia) as Hrh;
pose proof (blk_off_imgP _ _ _ _ _ _ res 48 HAR3 Hres_in) as Hrh_img;
change (req_size 48) with 48 in Hrceil, Hrpres3;
pose proof (sep_block_frame _ _ LAWS ly3 S3 _ _ _ res 48 2 fpos HAR3 Hres_in Hfin3) as HdRF;
unfold zdisjoint in HdRF; cbn [fst snd] in HdRF; change (req_size 48) with 48 in HdRF; change (fs_frame_bytes 2) with 256 in HdRF; rewrite EFA3 in HdRF; fold F in HdRF;
pose proof (sep_block_frame _ _ LAWS ly3 S3 _ _ _ res 48 cid pos HAR3 Hres_in HfinS3) as HdRC;
unfold zdisjoint in HdRC; cbn [fst snd] in HdRC; change (req_size 48) with 48 in HdRC; rewrite EFA3 in HdRC;
pose proof (sep_blocks _ _ LAWS ly3 S3 _ _ _ g CGIF_SIZE res 48 HAR3 Hing3 Hres_in ltac:(unfold CGIF_SIZE; intros X; injection X; lia)) as HdRG;
unfold zdisjoint in HdRG; cbn [fst snd] in HdRG; change (req_size 48) with 48 in HdRG; change (req_size CGIF_SIZE) with 96 in HdRG;
pose proof (sep_block_frame _ _ LAWS ly3 S3 _ _ _ g CGIF_SIZE 2 fpos HAR3 Hing3 Hfin3) as HdFG;
unfold zdisjoint in HdFG; cbn [fst snd] in HdFG; change (req_size CGIF_SIZE) with 96 in HdFG; change (fs_frame_bytes 2) with 256 in HdFG; rewrite EFA3 in HdFG; fold F in HdFG;
destruct (in_split _ _ Hfin) as (fl1 & fl2 & Efl);
pose proof (sep_frames_pos _ _ LAWS ly3 S3 _ _ _ (2, fpos) (cid, pos) [] fl1 fl2 HAR3 ltac:(rewrite Hfrs3, Efl; reflexivity)) as HdFC;
unfold zdisjoint, frame_rng in HdFC; cbn [fst snd] in HdFC; change (fs_frame_bytes 2) with 256 in HdFC; rewrite !EFA3 in HdFC; fold F in HdFC;
let Kgot3 := fresh "Kgot3" in let Kcell3 := fresh "Kcell3" in let Kguar3 := fresh "Kguar3" in let Kuar3 := fresh "Kuar3" in let Vgr3 := fresh "Vgr3" in
aconsts HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3;
img_facts E; img_hull_facts.
Ltac wcb_site rs HS HJ3 HAR3 Hfin3 HfinS3 Hing3 Hres_in Eab3 Hfrs3 EFA3 EFL3 HFpres3 HFSpres3 Hrpres3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3 :=
let AG := lazymatch goal with H : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => H end in
let EE := lazymatch goal with H : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew _ n = getr _ r |- _ => H end in
let Usp := lazymatch goal with H : bv_unsigned (ew _ 2) = spZ _ |- _ => H end in
let E0v := lazymatch type of EE with forall n r, _ -> ew ?E0v n = _ => E0v end in
let E32 := lazymatch goal with H : ew E0v 32 = Z_to_bv 64 _ |- _ => H end in
let E41 := lazymatch goal with H : ew _ 41 = Z_to_bv 64 _ |- _ => H end in
let E42 := lazymatch goal with H : ew _ 42 = Z_to_bv 64 _ |- _ => H end in
let Hch := lazymatch goal with H : achain _ _ _ _ _ |- _ => H end in
let Hchne := lazymatch goal with H : _ <> @nil (Z * Z * Z) |- _ => H | H : ?c <> [] |- _ => H end in
let Hal32 := lazymatch goal with H : spZ _ mod 32 = 0 |- _ => H end in
let Hra4 := lazymatch goal with H : 4096 <= raZ _ |- _ => H end in
let Hgp := lazymatch goal with H : getr _ 3 = w64 (as_gp _) |- _ => H end in
let Htp := lazymatch goal with H : getr _ 4 = w64 (as_tp _) |- _ => H end in
let FFS := lazymatch goal with H : TRAWNEW_STK = _ |- _ => H end in
let HROD := lazymatch goal with H : arodata_okP _ _ _ _ _ |- _ => H end in
let WFN := lazymatch goal with H : twcb_spec _ _ _ _ |- _ => H end in
let Rwfn := lazymatch type of WFN with twcb_spec _ _ ?wf _ => lazymatch goal with H : 0 <= wf < 2 ^ 64 /\ wf mod 2 = 0 |- _ => H end end in
let LAWS := rnLAWS in let Bv := rnB in
lazymatch type of HJ3 with ajournal _ _ ?STK (spZ ?regs) _ ?ly ?S ?W ?mem ?md [(2, ?fpos)] ?ly3 ?S3 ?W3 _ _ ?k =>
lazymatch type of HfinS3 with In (?cid, ?pos) _ =>
lazymatch type of Hing3 with In (?g, CGIF_SIZE) _ =>
lazymatch type of Hres_in with In (?res, 48) _ =>
lazymatch type of Hch with achain _ _ _ _ ?ch =>
lazymatch type of WFN with twcb_spec _ _ ?wfn ?hw =>
lazymatch type of HFpres3 with forall a, ?F <= a < _ -> _ =>
let Hfin := lazymatch goal with H : In (cid, pos) (frames S) |- _ => H end in
let P2 := fresh "P2" in let Prs := fresh "Prs" in let P8 := fresh "P8" in let P10 := fresh "P10" in
let P1 := fresh "P1" in let P3 := fresh "P3" in let P4 := fresh "P4" in
let Qtop := fresh "Qtop" in let Qtop64 := fresh "Qtop64" in let Qceil := fresh "Qceil" in let Qal8 := fresh "Qal8" in
let Qra := fresh "Qra" in let Qs0 := fresh "Qs0" in let Vra := fresh "Vra" in let Vs0 := fresh "Vs0" in let HRr := fresh "HRr" in
let Hch1 := fresh "Hch1" in let Vhw := fresh "Vhw" in let Vctx := fresh "Vctx" in let Vpf := fresh "Vpf" in
let mat1 := fresh "mat" in let ms1 := fresh "msj" in let Ems1 := fresh "Emsj" in let HS1 := fresh "HSj" in let HS2 := fresh "HS2" in
let W4 := fresh "W" in let c4 := fresh "c" in let Hwle4 := fresh "Hwle" in let ly4 := fresh "ly" in let S4 := fresh "S" in
let regs4 := fresh "regs" in let mem4 := fresh "mem" in let md4 := fresh "md" in
let HJ4 := fresh "HJ4" in let HJc := fresh "HJc" in let HP4 := fresh "HP4" in let Ha04 := fresh "Ha0c" in let HPb4 := fresh "HPb" in
let HRK := fresh "HRK" in let HEv := fresh "HEv" in
prreg HS (2%bv : bv 5) P2; prreg HS rs Prs; prreg HS (8%bv : bv 5) P8;
assert (Qtop : spZ regs < ly_top ly - 16) by (destruct Hch as [[_ Hnil] | (Q1 & Q2 & _)]; [exfalso; exact (Hchne Hnil) | lia]);
assert (Qtop64 : ly_top ly <= 2 ^ 64) by lia;
assert (Qceil : alloc_ceiling <= spZ regs) by lia;
assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D; rewrite Hal32, Z.add_0_r in D; rewrite D; replace (32 * (spZ regs / 32)) with ((4 * (spZ regs / 32)) * 8) by lia; apply Z_mod_mult);
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq);
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq);
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rsm := eval vm_compute in (ss_mem ssx) in let i := idx_of_base rsm 2%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rsm got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRr; cbn [ms_mem restrict] in HRr;
lazymatch type of HRr with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRr
ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRr
ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0;
clear HRr;
assert (Hch1 : achain ly3 (aview pa_segs (w_H W3) (ms_mem msX)) (spZ regs - 192) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
let Etop := fresh "Etop" in
pose proof HJ3 as (_ & (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _) & _);
apply (achain_ly_top ly ly3); [exact Etop|];
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ (spZ regs - 192) Hch Qtop64 (aview_above_of_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3)
(rdword_of_val_mem _ _ _ _ _ Vra Qra) (rdword_of_val_mem _ _ _ _ _ Vs0 Qs0) Hra4 Qceil Qal8 Qtop ltac:(lia))
| ] end;
let i := idx_of_base rsm 32%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rsm got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRr; cbn [ms_mem restrict mkst] in HRr;
lazymatch type of HRr with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 56 8%N (SOff 42 0) hw HRr ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E42, unsigned_lit_small, Z.add_0_r by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vhw;
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 64 8%N (SOff 40 0) (bv_unsigned (ew Ex 40)) HRr ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity)
ltac:(pose proof (bv_unsigned_in_range 64 (ew Ex 40)) as Q; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Q; exact Q) ltac:(cbn; lia)) as Vctx;
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 80 8%N (SLit 0) 0 HRr ltac:(evalE AG) ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vpf end;
clear HRr;
let pcj := eval vm_compute in (ss_pc ssx) in
let wj := eval vm_compute in (match plookup asan3_1_tpi pcj with Some (PW x) => x | _ => 0 end) in
let HEIx := rnHEI Ex in
eapply (SRr_jalr_call_pi (PL:=PL_asan3_1) W3 Ex ssx _ _ _ wj (1%bv : bv 5) rs wfn HEIx HS eq_refl);
[ vm_compute; reflexivity | vm_refl_bv | reflexivity | cbn [ss_pc]; lia | rewrite Prs; exact E41 | exact (proj1 Rwfn) | exact (proj2 Rwfn) |];
clear HS; intros mat1 ms1 Ems1 HS1;
prreg HS1 (1%bv : bv 5) P1; prreg HS1 (3%bv : bv 5) P3; prreg HS1 (4%bv : bv 5) P4; clear P8; prreg HS1 (8%bv : bv 5) P8; prreg HS1 (10%bv : bv 5) P10;
clear P2; prreg HS1 (2%bv : bv 5) P2;
lazymatch goal with |- SRr _ _ (mkCfg ?msq ?mdq) _ =>
eapply SRr_bind;
[ eapply (aj_call _ Bv LAWS pa_segs_low W3 Ex _ msq STK (spZ regs) [] ly S W mem md [(2, fpos)] ly3 S3 mdq k
WCB_STK [] 0 (-192) (ew Ex 2) _ ((spZ regs, raZ regs, s0Z regs) :: ch)
(fun ly2 S2 W2 regs2 mem2 md2 => getr regs2 10 = w64 0 /\ Permutation (ablocks Bv ly2 S2) (ablocks Bv ly3 S3)) HS1 eq_refl);
[ rewrite Ems1; cbn [ms_mem mkst]; apply (ajournal_materialize _ Bv LAWS pa_segs_low); exact HJ3
| rewrite P2; cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; reflexivity
| reflexivity
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 2%nat) by lia; exact Usp
| reflexivity | lia | unfold WCB_STK; lia | rewrite FFS; unfold WCB_STK; lia
| rewrite P3; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 3%nat) by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
| rewrite P4; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 4%nat) by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
| exact P1 | apply ret_ok_codeptr_v; [lia | reflexivity] | rewrite unsigned_lit_small by lia; lia
| unfold s0Z; rewrite P8; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 2%nat) by lia; rewrite Usp;
rewrite Ems1; cbn [ms_mem mkst]; replace (spZ regs + -192) with (spZ regs - 192) by lia; exact Hch1
| let HPRE1 := fresh "HPRE1" in let HC := fresh "HC" in
intros HPRE1; eapply SRr_mono;
[ pose proof (WFN W3 ly3 S3 _ _ _ ((spZ regs, raZ regs, s0Z regs) :: ch) g (bv_unsigned (ew Ex 40)) HPRE1) as HC; unfold cfg_at in HC;
lazymatch type of HS1 with st_ok _ _ ?sse _ => replace (w64 wfn) with (Z_to_bv 64 (ss_pc sse)) in HC by reflexivity end;
eapply HC;
[ rewrite P10; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 32%nat) by lia; rewrite E32; reflexivity
| exact Hing3 | | | | pose proof (bv_unsigned_in_range 64 (ew Ex 40)) as Q; change (bv_modulus 64) with (2 ^ 64) in Q; exact Q ];
rewrite Ems1; cbn [ms_mem mkst]; [exact Vhw | exact Vctx | exact Vpf]
| cbv beta; unfold wcb_post;
let W2 := fresh "W2" in let c2 := fresh "c2" in
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ1 & HP & HK & HPb);
exists ly2, S2, regs2, mem2, md2; split; [rewrite P1; reflexivity | split; [exact HJ1 | split; [exact HP | split; [exact HK | exact HPb]]]] ]
| let a := fresh "a" in intros a (r0 & Hr0 & _); destruct Hr0 ]
| ] end;
clear P3 P4 P10 Vra Vs0 Vhw Vctx Vpf Hch1 Prs;
cbv beta; intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc & HP4 & Ha04 & HPb4);
let K := run_K_hi HS1 in
lazymatch type of HS1 with st_ok _ _ ?ssy _ =>
let n := eval vm_compute in (length (ss_mem ssy)) in let idxs := eval vm_compute in (seq 0 n) in
jafter_call_keep_hi HS1 K regs4 (mrestrict (w_H W4) mem4) HP4 idxs HS2 end;
rewrite Ems1 in HS2, HJc; cbn [ms_mem ms_regs restrict mkst] in HS2, HJc;
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3; aconsts HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3;
let HAR4 := fresh "HAR4" in let Hfrs4 := fresh "Hfrs4" in let Hfin4 := fresh "Hfin4" in let HfinS4 := fresh "HfinS4" in
let Eab4 := fresh "Eab4" in let Hres_in4 := fresh "Hres_in4" in let Hing4 := fresh "Hing4" in let EFA4 := fresh "EFA4" in let EFL4 := fresh "EFL4" in
let HFpres4 := fresh "HFpres4" in let HFSpres4 := fresh "HFSpres4" in let Hrpres4 := fresh "Hrpres4" in
let Kgot4 := fresh "Kgot4" in let Kcell4 := fresh "Kcell4" in let Kguar4 := fresh "Kguar4" in let Kuar4 := fresh "Kuar4" in let Vgr4 := fresh "Vgr4" in
pose proof (proj1 HJ4) as HAR4;
assert (Hfrs4 : frames S4 = (2, fpos) :: frames S) by (let Hfr := fresh "Hfr" in pose proof HJc as (_ & _ & _ & _ & _ & Hfr & _); rewrite Hfr; cbn [app]; exact Hfrs3);
assert (Hfin4 : In (2, fpos) (frames S4)) by (rewrite Hfrs4; left; reflexivity);
assert (HfinS4 : In (cid, pos) (frames S4)) by (rewrite Hfrs4; right; exact Hfin);
assert (Eab4 : Permutation (ablocks Bv ly4 S4) (ablocks Bv ly S ++ [(res, 48)])) by (eapply Permutation_trans; [exact HPb4 | exact Eab3]);
assert (Hres_in4 : In (res, 48) (ablocks Bv ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPb4 | exact Hres_in]);
assert (Hing4 : In (g, CGIF_SIZE) (ablocks Bv ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPb4 | exact Hing3]);
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 HJ4))))))))) (proj1 (proj2 HJ4))) as (_ & EFA4 & _)
|| (let HAR := lazymatch goal with H : AR _ Bv ly S W mem md |- _ => H end in destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _));
assert (EFL4 : forall c p, flag_addr ly4 c p = flag_addr ly c p) by (intros cc pp; unfold flag_addr; pose proof (EFA4 cc pp) as X; unfold frame_addr in X; lia);
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4); change (fs_frame_bytes 2) with 256 in HFpres4, HFSpres4;
change (256 / 8) with 32 in HFSpres4; rewrite !EFA4 in HFpres4, HFSpres4; fold F in HFpres4, HFSpres4;
destruct (al_blocks _ _ LAWS _ _ _ _ _ res 48 HAR4 Hres_in4) as (_ & _ & _ & _ & Hrpres4 & _); change (req_size 48) with 48 in Hrpres4;
aconsts HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4;
match type of HS2 with ?tq -> _ => assert (HRK : tq) end;
[ repeat apply Forall_cons; try apply Forall_nil;
lazymatch goal with
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 516%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_frame_sub (segs:=pa_segs) Bv Ey _ _ _ _ _ _ _ _ _ _ _ _ _ _ 516%nat F lo hi wlo whi _ 2 fpos HJc);
[ evalE AG | exact Hfin3 | rewrite EFA3; fold F; lia | rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; lia
| intros aa Haa Hxa; exact (inFP_nil aa Hxa) | intros aa Haa; apply (fun H => proj1 (HFpres4 aa H)); lia ]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 529%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_fshadow_sub (segs:=pa_segs) Bv Ey _ _ _ _ _ _ _ _ _ _ _ _ _ _ 529%nat (SB + F / 8) lo hi wlo whi _ 2 fpos HJc);
[ evalE AG | exact Hfin3 | rewrite EFA3; fold F; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia
| rewrite EFA3; fold F; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 2 / 8) with 32; lia
| intros aa Haa Hxa; exact (inFP_nil aa Hxa) | intros aa Haa; lia ]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 534%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_block_subw (segs:=pa_segs) Bv Ey _ _ _ _ _ _ _ _ _ _ _ _ _ _ 534%nat lo hi wlo whi _ res 48 HJc);
[ evalE AG | exact Hres_in | exact Hres_in4 | lia | change (req_size 48) with 48; lia
| intros aa Haa Hxa; exact (inFP_nil aa Hxa) | intros aa Haa; apply (fun H => proj1 (Hrpres4 aa H)); lia ]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub _ Bv); [exact HJc | exact HJ4 | evalE AG | lia | rewrite FFS; lia | lia | cbn; lia | cbn; lia]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 10%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_frame_sub (segs:=pa_segs) Bv Ey _ _ _ _ _ _ _ _ _ _ _ _ _ _ 10%nat _ lo hi wlo whi _ cid pos HJc);
[ evalE AG | exact HfinS3 | rewrite EFA3; lia | rewrite EFA3; lia | intros aa Haa Hxa; exact (inFP_nil aa Hxa) | intros aa Haa; lia ]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_block_sub _ Bv); [exact HJc | evalE AG | exact Hing3 | exact Hing4 | lia | change (req_size CGIF_SIZE) with 96; unfold CGIF_SIZE; lia | lia
| intros aa Haa Hxa; exact (inFP_nil aa Hxa) ]
| |- _ => keptI I I AG Kgot3 Kgot4 Kcell3 Kcell4 Kguar3 Kguar4 Kuar3 Kuar4 Vgr3 Vgr4
end
| ];
specialize (HS2 HRK); clear HRK HS1; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
rebaseE HS AG HEv; clear HEv;
let HS0 := fresh "HS0" in
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msr) =>
pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HS ltac:(cbn [ms_regs mkst restrict]; exact Ha04) eq_refl) as HS0 end;
clear HS; rename HS0 into HS; norm_ss HS;
clear HJ3 HAR3 Hfin3 HfinS3 Hing3 Hres_in Eab3 Hfrs3 HFpres3 HFSpres3 Hrpres3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3;
clear HJc HP4 HPb4 Ha04 Hwle4 P1 P2 P8 Qtop Qtop64 Qceil Qal8 Qra Qs0 Ems1;
(repeat match goal with H : context [ly3] |- _ => first [clear H | rewrite EFA3 in H | rewrite EFL3 in H | fail 2 "wcb_site: ly3 still used in" H] end);
try clear EFA3; try clear EFL3;
rename HJ4 into HJ3; rename HAR4 into HAR3; rename Hfin4 into Hfin3; rename HfinS4 into HfinS3; rename Hing4 into Hing3; rename Hres_in4 into Hres_in;
rename Eab4 into Eab3; rename Hfrs4 into Hfrs3; rename EFA4 into EFA3; rename EFL4 into EFL3; rename HFpres4 into HFpres3; rename HFSpres4 into HFSpres3;
rename Hrpres4 into Hrpres3; rename Kgot4 into Kgot3; rename Kcell4 into Kcell3; rename Kguar4 into Kguar3; rename Kuar4 into Kuar3; rename Vgr4 into Vgr3;
replace (k + 0) with k in HJ3 by lia
end end end end end end end end.
Lemma rn_pow_cases : forall K, 0 <= K <= 8 -> K = 0 \/ K = 1 \/ K = 2 \/ K = 3 \/ K = 4 \/ K = 5 \/ K = 6 \/ K = 7 \/ K = 8.
Proof. intros K HK. lia. Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition rn_k1 (ka : nat) : sv := SAlu ALU_ADD (SOff ka 0) (SAlu ALU_SLTU (SAlu ALU_AND (SOff ka 0) (SLit 255)) (SLit 1)).
Definition rn_pow_sv (ka : nat) : sv := SAluw ALU_SLL (SLit 1) (rn_k1 ka).
Lemma denot_rn_pow : forall E ka K, ew E ka = Z_to_bv 64 K -> 0 <= K <= 8 ->
sv_denot E (rn_pow_sv ka) = Z_to_bv 64 (2 ^ Z.max K 1).
Proof.
intros E ka K HK Hr. unfold rn_pow_sv, rn_k1. cbn [sv_denot]. rewrite HK. apply bv_eq.
destruct (rn_pow_cases K Hr) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]; vm_compute; reflexivity.
Qed.
Lemma denot_rn_pow_mask : forall E ka K, ew E ka = Z_to_bv 64 K -> 0 <= K <= 8 ->
sv_denot E (SAlu ALU_AND (rn_pow_sv ka) (SLit 65535)) = Z_to_bv 64 (2 ^ Z.max K 1).
Proof.
intros E ka K HK Hr. unfold rn_pow_sv, rn_k1. cbn [sv_denot]. rewrite HK. apply bv_eq.
destruct (rn_pow_cases K Hr) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]; vm_compute; reflexivity.
Qed.
Lemma denot_rn_ndummy : forall E ka ks K sg, ew E ka = Z_to_bv 64 K -> 0 <= K <= 8 -> ew E ks = Z_to_bv 64 sg -> 1 <= sg < 2 ^ Z.max K 1 ->
U E (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLL (SAlu ALU_SUB (rn_pow_sv ka) (SOff ks 0)) (SLit 1)) (SAlu ALU_SUB (rn_pow_sv ka) (SOff ks 0))) (SLit 65535))
= 3 * (2 ^ Z.max K 1 - sg).
Proof.
intros E ka ks K sg HK Hr Hs Hsg.
assert (Hp : 2 <= 2 ^ Z.max K 1 <= 256).
{ destruct (rn_pow_cases K Hr) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
[ change (2 ^ Z.max 0 1) with 2 | change (2 ^ Z.max 1 1) with 2 | change (2 ^ Z.max 2 1) with 4 | change (2 ^ Z.max 3 1) with 8
| change (2 ^ Z.max 4 1) with 16 | change (2 ^ Z.max 5 1) with 32 | change (2 ^ Z.max 6 1) with 64 | change (2 ^ Z.max 7 1) with 128
| change (2 ^ Z.max 8 1) with 256 ]; lia. }
assert (P : U E (rn_pow_sv ka) = 2 ^ Z.max K 1).
{ unfold U. rewrite (denot_rn_pow E ka K HK Hr). apply unsigned_lit_small. lia. }
assert (Q : U E (SOff ks 0) = sg) by (apply U_atom; [exact Hs | lia]).
set (p := 2 ^ Z.max K 1) in *.
assert (D : U E (SAlu ALU_SUB (rn_pow_sv ka) (SOff ks 0)) = p - sg).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite P, Q. apply zcanon_id. rewrite M64_val. lia. }
assert (D2 : U E (SAlu ALU_SLL (SAlu ALU_SUB (rn_pow_sv ka) (SOff ks 0)) (SLit 1)) = 2 * (p - sg)).
{ apply (U_sll1_small E); [exact D | lia | lia]. }
assert (D3 : U E (SAlu ALU_ADD (SAlu ALU_SLL (SAlu ALU_SUB (rn_pow_sv ka) (SOff ks 0)) (SLit 1)) (SAlu ALU_SUB (rn_pow_sv ka) (SOff ks 0))) = 3 * (p - sg)).
{ rewrite (U_add_small E _ _ _ _ D2 D); lia. }
rewrite U_SAlu. cbn [zalu_raw]. rewrite D3, U_SLit. change (zcanon 65535) with (Z.ones 16).
rewrite Z.land_ones_low; [apply zcanon_id; rewrite M64_val; lia | lia |].
apply (Z.le_lt_trans _ (Z.log2 1024)); [apply Z.log2_le_mono; lia | cbn; lia].
Qed.
End e.
End d.
