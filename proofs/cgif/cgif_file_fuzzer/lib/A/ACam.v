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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbk AC8a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8j ACbc ACbf ACab ACai.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac evalE AG ::=
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
repeat match goal with |- context [ew Ev ?n] => lazymatch (eval cbv in (Nat.ltb n 33)) with true => rewrite (AG n) by lia end end end;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
repeat match goal with H : bv_unsigned (ew ?Ex 2) = _ |- context [bv_unsigned (ew ?Ex 2)] => rewrite H end;
rewrite ?unsigned_lit_small by (unfold SB; lia); unfold SB;
first [ reflexivity
| lazymatch goal with |- _ = _ => lia | |- _ <= _ => lia | |- _ < _ => lia | |- _ <= _ < _ => lia | |- _ <= _ <= _ => lia | |- _ < _ <= _ => lia end
| idtac ].
Ltac img_factsA E :=
let H := rnHEI E in
repeat match goal with G : ew E 241%nat = _ |- _ => clear G | G : ew E 242%nat = _ |- _ => clear G
| G : ew E 250%nat = _ |- _ => clear G | G : ew E 253%nat = _ |- _ => clear G end;
let E241 := fresh "E241" in let E242 := fresh "E242" in let E250 := fresh "E250" in let E253 := fresh "E253" in
pose proof (img_env_atomP E 241%nat H ltac:(unfold A_TEXT, A_LIM; lia)) as E241;
pose proof (img_env_atomP E 242%nat H ltac:(unfold A_TEXT, A_LIM; lia)) as E242;
pose proof (img_env_atomP E 250%nat H ltac:(unfold A_TEXT, A_LIM; lia)) as E250;
pose proof (img_env_atomP E 253%nat H ltac:(unfold A_TEXT, A_LIM; lia)) as E253.
Ltac img_hull_factsA :=
let TLF := rnTLF in
pose proof (pa_obj_img 0 ltac:(lia)) as Hob241; pose proof (pa_obj_img 1 ltac:(lia)) as Hob242;
pose proof (pa_obj_img 9 ltac:(lia)) as Hob250; pose proof (pa_obj_img 12 ltac:(lia)) as Hob253;
cbv [A_OBJ Nat.add] in Hob241, Hob242, Hob250, Hob253;
pose proof (palf_uar_img _ TLF) as Huar; pose proof (palf_uar_al _ TLF) as Huar4.
Ltac awrR_recA AG fpos F EFA :=
lazymatch goal with
| |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ (YP09.mkRegion _ _ _ ?wlo ?whi _ :: _) _ _ _ _ _ _ _ =>
first
[ lazymatch (eval vm_compute in (Z.leb whi wlo)) with true => apply awr_ok_cons_ro; [clear; cbn; lia|] end
| lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 529%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 529%nat); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists 1, fpos; split; [left; reflexivity|]; right;
unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; rewrite ?EFA; fold F; unfold SB; clear - Ha; lia
| ]
| |- awr_ok _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 516%nat); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists 1, fpos; split; [left; reflexivity|]; left;
unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 1) with 128; rewrite ?EFA; fold F; clear - Ha; lia
| ]
| |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | evalE AG | clear; cbn; unfold TRAWADD_STK, LZW_TSTK, ASTACK; lia | clear; cbn; unfold TRAWADD_STK, LZW_TSTK, ASTACK; lia |]
| |- awr_ok _ (YP09.mkRegion (Some 10%nat) _ _ _ _ _ :: _) _ ?sp0 ?fp _ _ _ _ =>
let Hin := match goal with H : In (_, RAW_SIZE) (ablocks _ _ _) |- _ => H | H : In (_, 48) (ablocks _ _ _) |- _ => H end in
lazymatch type of Hin with In (?raw, _) _ =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; left; split;
[ exists (raw + 40, raw + 44); split; [left; reflexivity | cbn [fst snd]; clear - Ha; lia]
| exists raw, RAW_SIZE; split; [exact Hin | change (req_size RAW_SIZE) with 48; clear - Ha; lia] ]
| ] end
end
| match goal with |- awr_ok _ (?r :: _) _ _ _ _ _ _ _ => idtac "AWR-HEAD" r end; fail 1 "awrRA: no rule for the head region" ];
awrR_recA AG fpos F EFA
end.
Ltac awrRA AG fpos F EFA :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
awrR_recA AG fpos F EFA.
Ltac fs_roA HS :=
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
Ltac fs_rwA HS E517 Hp :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 529%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 16) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 16 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite E517, unsigned_lit_small by (unfold SB; lia);
intros o Ho; apply (apresent_writable _); unfold shadow_addr in Hp; rewrite <- SB_SHADOW_OFF in Hp;
apply (proj1 (Hp o ltac:(clear - Ho; lia)))))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS | st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 529%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region _ Ex ssx msx i r (set_window r 0 16) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 16 (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite E517, unsigned_lit_small by (unfold SB; lia);
intros o Ho; apply (apresent_writable _); unfold shadow_addr in Hp; rewrite <- SB_SHADOW_OFF in Hp;
apply (proj1 (Hp o ltac:(clear - Ho; lia)))))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS  end.
Ltac oblFA HJx HE10 HE35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal :=
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 11 ?c)) ?len =>
lazymatch type of HE10 with _ = Z_to_bv 64 ?cfgp =>
first [ rewrite (U_atom_off Ex 11 cfgp c); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE10 | lia | lia]
| rewrite (U_atom Ex 11 cfgp); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE10 | lia] ];
eapply (obl_of_range _ _ _ Ex (SOff 40 0) _ len cfgp 40);
[ let L := rnLAWS in eapply (range_addressable_entry_frame _ _ L); [exact HJx | exact Hfin | exact Hcid0 | exact Hflo | exact Hfhi | exact Hfal
| first [ intros x Hx; exfalso; exact (inFP_nil x Hx)
| let x := fresh "x" in let rg := fresh "rg" in let Hrg := fresh "Hrg" in let Hxr := fresh "Hxr" in
intros x (rg & Hrg & Hxr); cbn [In] in Hrg; unbox; repeat (destruct Hrg as [<- | Hrg]; [cbn [fst snd] in Hxr; unfold kHighShadowEnd; zone_lia|]); destruct Hrg ]
| exact HAR | exact HRA]
| rewrite (U_atom Ex 40 SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE35 | unfold SB; lia]
| lia | lia ] end end.
Ltac add_flag_regionA HS AG E516 Hp HFLrng HFLown HnoG HnoC HnoF :=
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 528%nat) 0 1 0 1 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite ?ew_ewset_other by lia; rewrite E516, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable _); lazymatch goal with |- apresent _ _ (?fl + ?oo) => replace (fl + oo) with fl by lia end; exact Hp)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; evalE AG;
repeat split; first [zone_lia |
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
rewrite ?ew_ewset_other by lia; rewrite E516, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable _); lazymatch goal with |- apresent _ _ (?fl + ?oo) => replace (fl + oo) with fl by lia end; exact Hp)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; evalE AG;
repeat split; first [zone_lia |
lazymatch goal with |- ?fl + 1 <= ?x + ?l \/ ?x + ?h <= ?fl + 0 =>
destruct (Z_lt_ge_dec fl (x + l)); [left; lia|]; destruct (Z_lt_ge_dec fl (x + h)); [exfalso | right; lia];
first [apply (HnoG fl); [lia | exact HFLown] | apply (HnoC fl); [lia | exact HFLown] | apply (HnoF fl); [lia | exact HFLown]
| match goal with Hn : forall a, _ -> ~ aowned _ _ _ a |- _ => apply (Hn fl); [lia | exact HFLown] end
| match goal with |- ?g => idtac "DISJFAIL" g end] end
| match goal with |- ?g => idtac "DISJ?" g end ])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS  end.
Ltac wrangeRA AG fpos F EFA EFL :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (r & Hin & Hr); rewrite ?EFA, ?EFL;
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; intros Hr;
first [ exfalso; clear - Hr; lia
| right; clear - Hr; lia
| left; left; clear - Hr; unfold TRAWADD_STK, LZW_TSTK, ASTACK; lia
| left; right; right; right; exists 1, fpos; split; [left; reflexivity|];
first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 1) with 128; rewrite ?EFA; fold F; clear - Hr; lia
| right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; rewrite ?EFA; fold F; unfold SB; clear - Hr; lia ]
| left; match goal with A : forall blc lyq ownq i, In (?r, 48) blc -> _, Hin : In (?r, 48) (ablocks _ _ _) |- _ =>
replace a with (r + (a - r)) by lia; apply A; [exact Hin | clear - Hr; lia] end
|
left; right; left; split;
[ eexists; split; [left; reflexivity | cbn [fst snd]; clear - Hr; lia]
| lazymatch goal with |- exists b n, In (b, n) ?blc /\ _ =>
match goal with Hb : In (?rw, RAW_SIZE) blc |- _ =>
exists rw, RAW_SIZE; split; [exact Hb | change (req_size RAW_SIZE) with 48; clear - Hr; lia] end end ]
| match goal with |- ?g => match type of Hr with ?t => idtac "WRFAIL" t g end end; fail 2 "wrangeRA" ]
| ]);
destruct Hin.
Ltac flag0A E516 EFL :=
let msr := fresh "msr" in let HSr := fresh "HSr" in let HR := fresh "HR" in let V := fresh "V" in
intros msr HSr; rewrite ?EFL;
lazymatch type of HSr with st_ok_pi _ _ ?Ex ?ssx _ =>
pose proof (st_ok_pi_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR;
lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex (ms_mem msr) n _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E516; apply unsigned_lit_small; lia)
ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end | st_ok _ ?Ex ?ssx _ =>
pose proof (st_ok_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR;
lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex (ms_mem msr) n _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E516; apply unsigned_lit_small; lia)
ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end  end;
rewrite Z.add_0_r in V; pose proof (V 0%nat ltac:(lia)) as V0; cbn [Z.of_nat] in V0; rewrite Z.add_0_r in V0; exact V0.
Ltac exitRA RET RUNF HS HJx AG fpos F cfgp g E516 E517 Hfin HfinS HingX EE Hra HEV EFA EFL :=
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
assert (HnoC : forall a, cfgp <= a < cfgp + 40 -> ~ aowned B lyx Sx a) by (intros a Ha; apply (fun H => proj2 (HCpres' a H)); lia);
assert (HnoF : forall a, F <= a < F + 128 -> ~ aowned B lyx Sx a) by (intros a Ha; exact (proj2 (HFpres' a Ha)));
try (match goal with Hin : In (?r, RAW_SIZE) (ablocks _ lyx Sx) |- _ =>
let HRp := fresh "HRp" in let HnoR := fresh "HnoR" in
destruct (al_blocks _ _ LAWS _ _ _ _ _ r RAW_SIZE (proj1 HJx) Hin) as (_ & _ & _ & _ & HRp & _); change (req_size RAW_SIZE) with 48 in HRp;
assert (HnoR : forall a, r <= a < r + 48 -> ~ aowned B lyx Sx a) by (intros a Ha; exact (proj2 (HRp a Ha))); clear HRp end);
try (match goal with Hin : In (?r, 48) (ablocks _ lyx Sx) |- _ =>
let HRp := fresh "HRp" in let HnoR := fresh "HnoR" in
destruct (al_blocks _ _ LAWS _ _ _ _ _ r 48 (proj1 HJx) Hin) as (_ & _ & _ & _ & HRp & _); change (req_size 48) with 48 in HRp;
assert (HnoR : forall a, r <= a < r + 48 -> ~ aowned B lyx Sx a) by (intros a Ha; exact (proj2 (HRp a Ha))); clear HRp end) end;
fs_rwA HS E517 HFSpres';
add_flag_regionA HS AG E516 HFLpres' HFLrng HFLown HnoG HnoC HnoF;
paj_run_flag_sh RUNF HS HJx; [lia | wrangeRA AG fpos F EFA EFL | flag0A E516 EFL |];
let R1 := fresh "R1" in let R10 := fresh "R10" in
prreg HS (1%bv : bv 5) R1; prreg HS (10%bv : bv 5) R10;
lazymatch goal with |- SRr _ ?Wx _ _ =>
eapply (RET Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end;
let mat' := fresh "mat'" in intros mat'; unfold ra_post, apost_base;
cbn [c_ly c_S c_W c_regs c_mem c_md c_ch c_raw c_g c_cfp c_gct c_rattr c_Wd c_Hd c_sgct c_loops c_rcur c_ctx c_lct c_img c_fattr
c_w c_h c_top c_left c_delay c_slct c_disp c_tidx c_Nimg c_rest c_cid c_pos c_fpos c_wfn c_hw c_uar c_E0];
lazymatch type of HJx with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx _ _ _ _ =>
lazymatch goal with |- exists ly' S' regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists lyx, Sx, rg, mm, mdx end end;
split; [rewrite R1; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Hra; reflexivity|];
split; [cbn [ms_mem]; eapply (ajournal_mono_k _ _); [apply (ajournal_materialize _ _ LAWS pa_segs_low); exact HJx | rewrite HEV; lia]|];
split; [apply aregs_preserved_eqs; creg HS AG EE|];
rewrite R10.
Ltac aconstsA HROD HJx Kgot Kcell Kguar Kuar Vgr :=
let Kc := fresh "Kc" in let Ku := fresh "Ku" in let Kg := fresh "Kg" in let Kgu := fresh "Kgu" in
let LAWS := rnLAWS in let TL := rnTL in let TLF := rnTLF in
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJx)) as (Kc & Ku & Kg & Kgu);
rewrite (pal_got_shadow _ TL), (pal_cell _ TL) in Kg; rewrite (pal_cell _ TL) in Kc;
rewrite (palf_got_uar _ TLF) in Kgu;
pose proof (val_mem_of_rdword _ _ _ _ _ Kg) as Kgot; pose proof (val_mem_of_rdword _ _ _ _ _ Kc) as Kcell;
pose proof (val_mem_of_rdword _ _ _ _ _ Kgu) as Kguar; pose proof (val_mem_of_rd32 _ _ _ _ _ Ku) as Kuar;
clear Kc Ku Kg Kgu;
let HG9 := lazymatch goal with H : forall Hh mm, arodata_okP _ _ _ _ (aview _ Hh mm) -> val_mem _ (mrestrict Hh mm) _ 8 _ |- _ => H end in
pose proof (HG9 _ _ (arodata_ok_journalP _ _ _ pa_relro_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJx HROD)) as Vgr.
Ltac keptRA HK HJx AG Usp E10 E32 Hfin Hing Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2 :=
let Bv := rnB in
lazymatch goal with
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj _ _); [exact HK | exact HJx | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?(AG 2%nat) by lia; exact Usp
| lia | unfold TRAWADD_STK, LZW_TSTK, ASTACK; lia | lia | lia | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 241%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 0) (pa_val (A_OBJ 0)) 8 (pa_val (A_OBJ 12)));
[exact (H (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kg | exact Kg2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 253%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 12) (pa_val (A_OBJ 12)) 8 SHADOW_OFF);
[exact (H (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kc | exact Kc2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 242%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 1) (pa_val (A_OBJ 1)) 8 (as_uar_cell Bv));
[exact (H (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kgu | exact Kgu2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 55%nat) _ _ _ _ _) =>
apply (region_kept_val_at Ex _ _ 55%nat (as_uar_cell Bv) 4 1); [evalE AG | exact Ku | exact Ku2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 250%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 9) (pa_val (A_OBJ 9)) 8 (pa_val A_TEXT + AF_asan3_cgif_raw_addframe));
[exact (H (A_OBJ 9) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Vg | exact Vg2 | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply (region_kept_frame_aj _ _); [exact HK | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?(AG 11%nat) by lia; rewrite E10; apply unsigned_lit_small; lia
| exact Hfin | rwEFA; lia | rwEFA; lia | lia | intros a Ha Hn; first [exact Hn | rqs Hn; unbox; lia]]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 32%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj _ _); [exact HK | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?(AG 32%nat) by lia; rewrite E32; apply unsigned_lit_small; lia
| exact Hing | lia | change (req_size CGIF_SIZE) with 96; unfold CGIF_SIZE; lia | lia | intros a Ha Hn; first [exact Hn | rqs Hn; unbox; lia]]
end.
Ltac keptFA HK AG RF E517 HfinX HFP HFSP HEr F :=
lazymatch goal with
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj _ _); [exact HK | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite RF; apply unsigned_lit_small; lia
| exact HfinX | left; rwEFA; change (fs_frame_bytes 1) with 128; fold F; lia | intros a Ha; cbn beta; first [exact (fun Hn : False => Hn) | apply HEr; lia]
| intros a Ha; apply (fun H => proj1 (HFP a H)); lia ]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 529%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj _ _); [exact HK | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E517; apply unsigned_lit_small; unfold SB; lia
| exact HfinX | right; rwEFA; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; fold F; lia
| intros a Ha; first [exact (fun Hn : False => Hn) | let Hn := fresh "Hn" in intros Hn; first [shadow_vs Ha Hn | rqs Hn; unfold SB in Ha; unbox; zone_lia]]
| intros a Ha; lia ]
end.
Ltac keptFA2 HK AG RF E517 HfinX HFP HFSP HEr HErS F :=
lazymatch goal with
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj _ _); [exact HK | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite RF; apply unsigned_lit_small; lia
| exact HfinX | left; rwEFA; change (fs_frame_bytes 1) with 128; fold F; lia | intros a Ha; cbn beta; first [exact (fun Hn : False => Hn) | apply HEr; lia]
| intros a Ha; apply (fun H => proj1 (HFP a H)); lia ]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 529%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj _ _); [exact HK | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E517; apply unsigned_lit_small; unfold SB; lia
| exact HfinX | right; rwEFA; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; fold F; lia
| intros a Ha; cbn beta; first [exact (fun Hn : False => Hn) | apply HErS; clear - Ha; lia]
| intros a Ha; lia ]
end.
Ltac keptIA Hfr Hpres AG Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2 :=
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
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 55%nat) _ _ _ _ _) =>
apply (region_kept_val_at Ex _ _ 55%nat (as_uar_cell Bv) 4 1); [evalE AG | exact Ku | exact Ku2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 250%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 9) (pa_val (A_OBJ 9)) 8 (pa_val A_TEXT + AF_asan3_cgif_raw_addframe));
[exact (H (A_OBJ 9) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Vg | exact Vg2 | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some ?n) _ _ _ _ _) =>
eapply region_kept_aview; [evalE AG | intros a Ha; apply Hfr; unbox; unfold ESTACK; zone_lia | exact Hpres]
end.
