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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n YI0s YC4b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a YC80 YC1f YC1g YC1h YC81 YC4b YC20 YC44 YC45.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8a ACjr ACj3 ACh9 ACk4.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACk5.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YC5d YC7z YC7x YC21 YC85 YC86 YC88.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI17 YE02 YC5n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACk0.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition xfacts (P : Prop) : Prop := P.
Lemma xfacts_i : forall P : Prop, P -> xfacts P. Proof. intros P H. exact H. Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Variable segs : list Segment.
Variable B : asyms.
Lemma ajournal_fp_nilX : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal segs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
ajournal segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k
(HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
split; [exact HAR|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
split; [eapply aos_step_mono; [|exact Hio]; intros Ho; exfalso; exact (sink_closed_nil Ho)|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|]. split; [exact F1|].
split; [intros p n i H1 H2 Hi _; apply (F2 p n i H1 H2 Hi); apply inFP_nil|].
split; [intros a Hi Hns He _; apply (F3 a Hi Hns He); apply fp_spares_closed; intros Ho; exact (sink_closed_nil Ho)|].
split; [intros cid pos a H1 H2 _; apply (F4 cid pos a H1 H2); apply inFP_nil|].
split; [intros p n i H1 H2 Hi; exfalso; exact (inFP_nil _ (Hgone p n i H1 H2 Hi))|].
split; [exact Hpres|]. split; [exact Hstatic|]. split; [exact F5 | exact HQT].
Qed.
Lemma ajournal_closed_ioX : forall STK sp0 FP ly S (W : world segs) mem md own ly' S' W' mem' md' k,
~ YI16.sink_open_fp FP ->
ajournal segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k Hcl HJ. pose proof HJ as (_ & _ & _ & _ & Hos & _).
destruct (aos_step_closed FP md md' Hcl Hos) as (Efd & Efsys & _ & _).
unfold m_fds, m_fs. rewrite Efd, Efsys. split; reflexivity.
Qed.
Lemma ajournal_nil_ioX : forall STK sp0 ly S (W : world segs) mem md own ly' S' W' mem' md' k,
ajournal segs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof. intros until 0. intros HJ. exact (ajournal_closed_ioX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sink_closed_nil HJ). Qed.
Lemma srz_enterX : forall (W : world segs) (c : config) (T : TSet),
AI segs (w_H W) (w_A W) (cfg_model c) ->
SRr segs W c (fun W' c' => AI segs (w_H W') (w_A W') (cfg_model c') -> srealizes segs c' T) -> srealizes segs c T.
Proof. intros W c T HAI HS. apply (HS HAI T). intros W' c' _ HAI' HK. exact (HK HAI'). Qed.
Lemma inFP_token : forall a, inFP [sink_token] a -> 0 <= a < 1.
Proof. intros a (r & [<-|[]] & Hr). cbn in Hr. exact Hr. Qed.
Lemma inFP_token_pos : forall a, 1 <= a -> ~ inFP [sink_token] a.
Proof. intros a Ha H. apply inFP_token in H. lia. Qed.
Lemma asink_none_model : forall (K : asink_syms) m md md', m_fds md' = m_fds md -> asink_none segs K m md -> asink_none segs K m md'.
Proof. intros K m md md' E (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. rewrite E. exact H3. Qed.
End e.
End d.
Ltac add_flag_region HS AG E528 Hp HFLrng HFLown HnoG HnoC HnoF ::=
let Qceil := match goal with H : alloc_ceiling <= ly_stk_lo _ |- _ => H end in
let Qslo := match goal with H : ly_stk_lo _ + _ <= spZ _ |- _ => H end in
let QC1 := match goal with H : _ <= alloc_ceiling <= _ |- _ => H end in
let QC3 := match goal with H : kHighMemBeg = _ |- _ => H end in
let QFFS := match goal with H : TNEWGIFX_STK = _ |- _ => H end in
let QFq := match goal with H : ?Fr = 32 * (?Fr / 32) |- _ => H end in
let QF8 := match goal with H : ?Fr / 8 = 4 * (?Fr / 32) |- _ => H end in
let QFceil := match goal with H : ?Fr + 128 <= alloc_ceiling |- _ => H end in
let QF8lo := match goal with H : 512 <= ?Fr / 8 |- _ => H | _ => QFq end in
let QF8hi := match goal with H : ?Fr / 8 < 17592186044416 |- _ => H | _ => QFq end in
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 528%nat) 0 1 0 1 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite ?ew_ewset_other by lia; rewrite E528, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable _); lazymatch goal with |- apresent _ _ (?fl + ?oo) => replace (fl + oo) with fl by lia end; exact Hp)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; evalE0 AG;
repeat split; first [lazymatch goal with QH1 : 65536 <= ?xa /\ ?xa + 8 <= _, QH2 : 65536 <= ?xb /\ ?xb + 8 <= _, QH3 : 65536 <= ?xc /\ ?xc + 8 <= _, QH4 : 65536 <= ?xd /\ ?xd + 8 <= _, QH5 : 65536 <= ?xe /\ ?xe + 8 <= _ |- _ =>
clear - HFLrng Qceil Qslo QC1 QC3 QFFS QFq QF8 QFceil QF8lo QF8hi QH1 QH2 QH3 QH4 QH5; zone_lia end |
lazymatch goal with |- ?fl + 1 <= ?x + ?l \/ ?x + ?h <= ?fl + 0 =>
let Hlt := fresh "Hlt" in let Hge := fresh "Hge" in let Hlt2 := fresh "Hlt2" in let Hge2 := fresh "Hge2" in
destruct (Z_lt_ge_dec fl (x + l)) as [Hlt | Hge]; [left; clear - Hlt; lia|];
destruct (Z_lt_ge_dec fl (x + h)) as [Hlt2 | Hge2]; [exfalso | right; clear - Hge2; lia];
first [apply (HnoG fl); [clear - Hge Hlt2; lia | exact HFLown] | apply (HnoC fl); [clear - Hge Hlt2; lia | exact HFLown]
| apply (HnoF fl); [clear - Hge Hlt2; lia | exact HFLown]
| match goal with Hn : forall a, _ -> ~ aowned _ _ _ a |- _ => apply (Hn fl); [clear - Hge Hlt2; lia | exact HFLown] end
| match goal with |- ?g => idtac "DISJFAIL" g end] end
| match goal with |- ?g => idtac "DISJ?" g end ])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS | st_ok _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_add_region _ Ev _ _ (YP09.mkRegion (Some 528%nat) 0 1 0 1 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite ?ew_ewset_other by lia; rewrite E528, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable _); lazymatch goal with |- apresent _ _ (?fl + ?oo) => replace (fl + oo) with fl by lia end; exact Hp)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; evalE0 AG;
repeat split; first [lazymatch goal with QH1 : 65536 <= ?xa /\ ?xa + 8 <= _, QH2 : 65536 <= ?xb /\ ?xb + 8 <= _, QH3 : 65536 <= ?xc /\ ?xc + 8 <= _, QH4 : 65536 <= ?xd /\ ?xd + 8 <= _, QH5 : 65536 <= ?xe /\ ?xe + 8 <= _ |- _ =>
clear - HFLrng Qceil Qslo QC1 QC3 QFFS QFq QF8 QFceil QF8lo QF8hi QH1 QH2 QH3 QH4 QH5; zone_lia end |
lazymatch goal with |- ?fl + 1 <= ?x + ?l \/ ?x + ?h <= ?fl + 0 =>
let Hlt := fresh "Hlt" in let Hge := fresh "Hge" in let Hlt2 := fresh "Hlt2" in let Hge2 := fresh "Hge2" in
destruct (Z_lt_ge_dec fl (x + l)) as [Hlt | Hge]; [left; clear - Hlt; lia|];
destruct (Z_lt_ge_dec fl (x + h)) as [Hlt2 | Hge2]; [exfalso | right; clear - Hge2; lia];
first [apply (HnoG fl); [clear - Hge Hlt2; lia | exact HFLown] | apply (HnoC fl); [clear - Hge Hlt2; lia | exact HFLown]
| apply (HnoF fl); [clear - Hge Hlt2; lia | exact HFLown]
| match goal with Hn : forall a, _ -> ~ aowned _ _ _ a |- _ => apply (Hn fl); [clear - Hge Hlt2; lia | exact HFLown] end
| match goal with |- ?g => idtac "DISJFAIL" g end] end
| match goal with |- ?g => idtac "DISJ?" g end ])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS  end.
Ltac wrangeR AG fpos F EFA EFL ::=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (r & Hin & Hr); rewrite ?EFA, ?EFL;
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE0 AG; intros Hr;
first [ exfalso; clear - Hr; lia
| right; clear - Hr; lia
| left; left; clear - Hr; unfold TNEWGIFX_STK, AFOPEN_STK; lia
| left; right; right; right; exists 1, fpos; split; [left; reflexivity|];
first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 1) with 128; rewrite ?EFA; fold F; clear - Hr; lia
| right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; rewrite ?EFA; fold F; unfold SB; clear - Hr; lia ]
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
Ltac ng_facts HCTX HCFG HE0 HE ::=
let LAWS := rnLAWS in
pose proof pa_wx as Hwx; pose proof pa_segs_low as Hsegs;
destruct HCTX as (HPRE & Hal32 & Hctx & Hroom & Htop32 & HROD & Hcfg & HWH & Hpala & HPerm & Hev & Hlive);
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5); assert (FFS : TNEWGIFX_STK = 18816) by reflexivity;
assert (HEV : EV_NEWGIF = 12) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity; assert (Has : ASTACK = 16384) by reflexivity;
destruct HCFG as (Hfin & Hcid0 & Hfal & Hflo & Hfhi & Hcal & HRA);
destruct HE0 as (EE & E10 & E32 & Usp); destruct HE as (AG & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & RF & E528 & E529 & E41 & ?HEI);
destruct (frames_bounds _ _ LAWS _ _ _ _ _ _ _ HAR Hfin) as (Hf4096 & Hfceil & Hfhigh);
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img;
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ => img_facts Ev end; img_hull_facts;
let Hc' := fresh "Hc'" in
pose proof Hcfg as Hc'; cbn [obj_at LAY_Config] in Hc';
destruct Hc' as ([CV0 CR0] & [CV8 CR8] & [CV16 CR16] & [CV20 CR20] & [CV24 CR24] & [CV26 CR26] & [CV28 CR28] & [CV30 CR30] & [CV32 CR32] & [CV40 CR40] & HcT);
cbn [fst snd N.to_nat Z.of_N] in CV0, CV8, CV16, CV20, CV24, CV26, CV28, CV30, CV32, CV40, CR0, CR16, CR20, CR24, CR26, CR28, CR30;
change (2 ^ (8 * 8)) with (2 ^ 64) in CR0; change (2 ^ (8 * 4)) with (2 ^ 32) in CR16, CR20; change (2 ^ (8 * 2)) with 65536 in CR24, CR26, CR28, CR30.
Ltac keptR HK HJx AG Usp E10 E32 Hfin Hing Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2 EFA ::=
let Bv := rnB in
lazymatch goal with
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj _ _); [exact HK | exact HJx | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?(AG 2%nat) by lia; exact Usp
| lia | unfold TNEWGIFX_STK, AFOPEN_STK; lia | lia | lia | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 241%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 0) (pa_val (A_OBJ 0)) 8 (pa_val (A_OBJ 12)));
[exact (H (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kg | exact Kg2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 253%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 12) (pa_val (A_OBJ 12)) 8 SHADOW_OFF);
[exact (H (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kc | exact Kc2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 242%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 1) (pa_val (A_OBJ 1)) 8 (as_uar_cell Bv));
[exact (H (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kgu | exact Kgu2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 41%nat) _ _ _ _ _) =>
apply (region_kept_val_at Ex _ _ 41%nat (as_uar_cell Bv) 4 1); [evalE AG | exact Ku | exact Ku2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 244%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 3) (pa_val (A_OBJ 3)) 8 (pa_val A_TEXT + 0));
[exact (H (A_OBJ 3) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Vg | exact Vg2 | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_frame_aj _ _); [exact HK | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?(AG 10%nat) by lia; rewrite E10; apply unsigned_lit_small; lia
| exact Hfin | rewrite ?EFA; lia | rewrite ?EFA; lia | lia | intros a Ha Hn; first [exact Hn | lia | rqs Hn; zone_lia]]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 32%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj _ _); [exact HK | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?(AG 32%nat) by lia; rewrite E32; apply unsigned_lit_small; lia
| exact Hing | lia | change (req_size CGIF_SIZE) with 96; unfold CGIF_SIZE; lia | lia | intros a Ha Hn; first [exact Hn | lia | rqs Hn; zone_lia]]
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
Ltac keptF HK AG RF E529 HfinX HFP HFSP HEr F EFA :=
lazymatch goal with
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj _ _); [exact HK | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite RF; apply unsigned_lit_small; lia
| exact HfinX | left; change (fs_frame_bytes 1) with 128; rewrite ?EFA; fold F; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn beta; first [exact (fun Hn : False => Hn) | apply HEr; lia]
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply (fun H => proj1 (HFP a H)); lia ]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 529%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj _ _); [exact HK | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E529; apply unsigned_lit_small; unfold SB; lia
| exact HfinX | right; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; rewrite ?EFA; fold F; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; first [exact (fun Hn : False => Hn) | let Hn := fresh "Hn" in intros Hn; first [shadow_vs Ha Hn | rqs Hn; unfold SB in Ha; zone_lia]]
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; unfold shadow_addr in HFSP; rewrite <- ?SB_SHADOW_OFF in HFSP;
first [lia | apply (fun H => proj1 (HFSP (a - (SB + F / 8)) H)); lia | replace a with (SB + F / 8 + (a - (SB + F / 8))) by lia; apply (fun H => proj1 (HFSP (a - (SB + F / 8)) H)); lia] ]
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
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 41%nat) _ _ _ _ _) =>
apply (region_kept_val_at Ex _ _ 41%nat (as_uar_cell Bv) 4 1); [evalE AG | exact Ku | exact Ku2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 244%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 3) (pa_val (A_OBJ 3)) 8 (pa_val A_TEXT + 0));
[exact (H (A_OBJ 3) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Vg | exact Vg2 | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some ?n) _ _ _ _ _) =>
eapply region_kept_aview; [evalE AG | intros a Ha; apply Hfr; unfold ESTACK; zone_lia | exact Hpres]
end.
Ltac exitR RET RUNF HS HJx AG fpos F cfgp g E528 E529 Hfin HfinS HingX EE Hra HEV EFA EFL ::=
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
fs_rw HS E529 HFSpres';
add_flag_region HS AG E528 HFLpres' HFLrng HFLown HnoG HnoC HnoF;
paj_run_flag_sh RUNF HS HJx; [lia | wrangeR AG fpos F EFA EFL | flag0 E528 EFL |];
let R1 := fresh "R1" in let R10 := fresh "R10" in
prreg HS (1%bv : bv 5) R1; prreg HS (10%bv : bv 5) R10;
lazymatch goal with |- SRr _ ?Wx _ _ =>
eapply (RET Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end;
let mat' := fresh "mat'" in intros mat'; cbv beta delta [ng_postXB tnewgif_postA tnewgif_postB0 tnewgif_postB1 apost_base YC20.apost_base];
lazymatch type of HJx with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx _ _ _ _ =>
lazymatch goal with |- exists ly' S' regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists lyx, Sx, rg, mm, mdx end end;
split; [rewrite R1; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Hra; reflexivity|];
split; [cbn [ms_mem]; eapply (ajournal_mono_k _ _); [first [apply (ajournal_materialize _ _ LAWS pa_segs_low); exact HJx | apply ajournal_fp_nilX; apply (ajournal_materialize _ _ LAWS pa_segs_low); exact HJx] | try (change YC20.EV_NEWGIF with EV_NEWGIF); rewrite HEV; unfold EV_RAWNEW; lia]|];
split; [apply aregs_preserved_eqs; creg HS AG EE|];
rewrite R10.
Ltac exitRX RET RUNF HS HJx AG fpos F cfgp g E528 E529 Hfin HfinS HingX EE Hra HEV EFA EFL xhook :=
let HFLpres' := fresh "HFLpres'" in let HFLown := fresh "HFLown'" in let HFLrng := fresh "HFLrng'" in
let HFpres' := fresh "HFpres'" in let HFSpres' := fresh "HFSpres'" in
let HCpres' := fresh "HCpres'" in let HGpres' := fresh "HGpres'" in
let HnoG := fresh "HnoG" in let HnoC := fresh "HnoC" in let HnoF := fresh "HnoF" in
let FFL := rnFFL in let LAWS := rnLAWS in destruct (FFL _ _ _ _ _ 1 fpos (proj1 HJx) Hfin) as (HFLpres' & HFLown & HFLrng); rewrite ?EFL in HFLpres'; rewrite ?EFL in HFLown; rewrite ?EFL in HFLrng; fold F in HFLrng;
(let HFLni := fresh "HFLni" in pose proof (proj2 (proj1 HFLrng)) as HFLni);
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
fs_rw HS E529 HFSpres';
add_flag_region HS AG E528 HFLpres' HFLrng HFLown HnoG HnoC HnoF;
paj_run_flag_sh RUNF HS HJx; [lia | wrangeR AG fpos F EFA EFL | flag0 E528 EFL |];
xhook;
let R1 := fresh "R1" in let R10 := fresh "R10" in
prreg HS (1%bv : bv 5) R1; prreg HS (10%bv : bv 5) R10;
lazymatch goal with |- SRr _ ?Wx _ _ =>
eapply (RET Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end;
let mat' := fresh "mat'" in intros mat'; cbv beta delta [ng_postXB tnewgif_postA tnewgif_postB0 tnewgif_postB1 apost_base YC20.apost_base];
lazymatch type of HJx with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx _ _ _ _ =>
lazymatch goal with |- exists ly' S' regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists lyx, Sx, rg, mm, mdx end end;
split; [rewrite R1; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Hra; reflexivity|];
split; [cbn [ms_mem]; eapply (ajournal_mono_k _ _); [first [apply (ajournal_materialize _ _ LAWS pa_segs_low); exact HJx | apply ajournal_fp_nilX; apply (ajournal_materialize _ _ LAWS pa_segs_low); exact HJx] | try (change YC20.EV_NEWGIF with EV_NEWGIF); rewrite HEV; unfold EV_RAWNEW; lia]|];
split; [apply aregs_preserved_eqs; creg HS AG EE|];
rewrite R10.
Ltac exitN RET RUNF HS HJx AG fpos F cfgp E528 E529 Hfin HfinS EE Hra HEV EFA EFL ::=
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
fs_rw HS E529 HFSpres';
add_flag_region HS AG E528 HFLpres' HFLrng HFLown HnoC HnoC HnoF;
paj_run_flag_sh RUNF HS HJx; [lia | wrangeR AG fpos F EFA EFL | flag0 E528 EFL |];
let R1 := fresh "R1" in let R10 := fresh "R10" in
prreg HS (1%bv : bv 5) R1; prreg HS (10%bv : bv 5) R10;
lazymatch goal with |- SRr _ ?Wx _ _ =>
eapply (RET Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end;
let mat' := fresh "mat'" in intros mat'; cbv beta delta [ng_postXB tnewgif_postA tnewgif_postB0 tnewgif_postB1 apost_base YC20.apost_base];
lazymatch type of HJx with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx _ _ _ _ =>
lazymatch goal with |- exists ly' S' regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists lyx, Sx, rg, mm, mdx end end;
split; [rewrite R1; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Hra; reflexivity|];
split; [cbn [ms_mem]; eapply (ajournal_mono_k _ _); [first [apply (ajournal_materialize _ _ LAWS pa_segs_low); exact HJx | apply ajournal_fp_nilX; apply (ajournal_materialize _ _ LAWS pa_segs_low); exact HJx] | try (change YC20.EV_NEWGIF with EV_NEWGIF); rewrite HEV; unfold EV_RAWNEW; lia]|];
split; [apply aregs_preserved_eqs; creg HS AG EE|];
rewrite R10.
Ltac exitNX RET RUNF HS HJx AG fpos F cfgp E528 E529 Hfin HfinS EE Hra HEV EFA EFL xhook :=
let HFLpres' := fresh "HFLpres'" in let HFLown := fresh "HFLown'" in let HFLrng := fresh "HFLrng'" in
let HFpres' := fresh "HFpres'" in let HFSpres' := fresh "HFSpres'" in
let HCpres' := fresh "HCpres'" in
let HnoC := fresh "HnoC" in let HnoF := fresh "HnoF" in
let FFL := rnFFL in let LAWS := rnLAWS in destruct (FFL _ _ _ _ _ 1 fpos (proj1 HJx) Hfin) as (HFLpres' & HFLown & HFLrng); rewrite ?EFL in HFLpres'; rewrite ?EFL in HFLown; rewrite ?EFL in HFLrng; fold F in HFLrng;
(let HFLni := fresh "HFLni" in pose proof (proj2 (proj1 HFLrng)) as HFLni);
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos (proj1 HJx) Hfin) as (_ & _ & HFpres' & HFSpres'); change (fs_frame_bytes 1) with 128 in HFpres', HFSpres';
change (128 / 8) with 16 in HFSpres'; rewrite ?EFA in HFpres'; rewrite ?EFA in HFSpres'; fold F in HFpres', HFSpres';
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ (proj1 HJx) HfinS) as (_ & _ & HCpres' & _); rewrite ?EFA in HCpres';
lazymatch type of HFpres' with forall a, _ -> _ /\ ~ aowned ?B ?lyx ?Sx a =>
assert (HnoC : forall a, cfgp <= a < cfgp + 48 -> ~ aowned B lyx Sx a) by (intros a Ha; apply (fun H => proj2 (HCpres' a H)); lia);
assert (HnoF : forall a, F <= a < F + 128 -> ~ aowned B lyx Sx a) by (intros a Ha; exact (proj2 (HFpres' a Ha))) end;
fs_rw HS E529 HFSpres';
add_flag_region HS AG E528 HFLpres' HFLrng HFLown HnoC HnoC HnoF;
paj_run_flag_sh RUNF HS HJx; [lia | wrangeR AG fpos F EFA EFL | flag0 E528 EFL |];
xhook;
let R1 := fresh "R1" in let R10 := fresh "R10" in
prreg HS (1%bv : bv 5) R1; prreg HS (10%bv : bv 5) R10;
lazymatch goal with |- SRr _ ?Wx _ _ =>
eapply (RET Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end;
let mat' := fresh "mat'" in intros mat'; cbv beta delta [ng_postXB tnewgif_postA tnewgif_postB0 tnewgif_postB1 apost_base YC20.apost_base];
lazymatch type of HJx with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx _ _ _ _ =>
lazymatch goal with |- exists ly' S' regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists lyx, Sx, rg, mm, mdx end end;
split; [rewrite R1; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Hra; reflexivity|];
split; [cbn [ms_mem]; eapply (ajournal_mono_k _ _); [first [apply (ajournal_materialize _ _ LAWS pa_segs_low); exact HJx | apply ajournal_fp_nilX; apply (ajournal_materialize _ _ LAWS pa_segs_low); exact HJx] | try (change YC20.EV_NEWGIF with EV_NEWGIF); rewrite HEV; unfold EV_RAWNEW; lia]|];
split; [apply aregs_preserved_eqs; creg HS AG EE|];
rewrite R10.
Ltac reseat_lo kk HS HJ2 HP2 keep AG kept_tac :=
let K := constr:(kk) in
let HS2 := fresh "HS2" in
lazymatch type of HJ2 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?W2 ?mem2 _ _ =>
lazymatch type of HP2 with aregs_preserved _ ?regs2 =>
jafter_call_keep_pi HS K regs2 (mrestrict (w_H W2) mem2) HP2 keep HS2 end end;
match type of HS2 with ?Q -> _ =>
let HQ := fresh "HQ" in
assert (HQ : Q); [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil; kept_tac | specialize (HS2 HQ); clear HQ ] end;
clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
let AG2 := fresh "AG" in let Ev := fresh "E" in let HEv := fresh "HE" in
lazymatch type of AG with forall n, _ -> _ = ew ?E0 n =>
lazymatch type of HS with st_ok_pi _ _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
let HEIv := fresh "HEI" in
lazymatch type of HEv with
| _ = havoc ?Eo ?kk0 ?ws => lazymatch goal with Ho : img_env ?val ?lim Eo |- _ =>
pose proof (img_env_havoc Eo kk0 ws Ho ltac:(cbv; lia)) as HEIv; rewrite <- HEv in HEIv end
| _ = ?En => try (lazymatch goal with Hn : img_env _ _ En |- _ => rewrite <- HEv in Hn end) end;
repeat match goal with H : img_env _ _ (ewset _ _ _) |- _ => clear H end;
assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; apply AG; exact Hnn);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 33 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; first [rewrite ew_havoc_old by lia | rewrite ew_havoc_above by (cbv [length map CLOB]; lia)]; rewrite ?ew_ewset_other by lia; exact H);
clear H; rename H2 into H
end end end;
clear HEv AG; rename AG2 into AG | st_ok _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
let HEIv := fresh "HEI" in
lazymatch type of HEv with
| _ = havoc ?Eo ?kk0 ?ws => lazymatch goal with Ho : img_env ?val ?lim Eo |- _ =>
pose proof (img_env_havoc Eo kk0 ws Ho ltac:(cbv; lia)) as HEIv; rewrite <- HEv in HEIv end
| _ = ?En => try (lazymatch goal with Hn : img_env _ _ En |- _ => rewrite <- HEv in Hn end) end;
repeat match goal with H : img_env _ _ (ewset _ _ _) |- _ => clear H end;
assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; apply AG; exact Hnn);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 33 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; first [rewrite ew_havoc_old by lia | rewrite ew_havoc_above by (cbv [length map CLOB]; lia)]; rewrite ?ew_ewset_other by lia; exact H);
clear H; rename H2 into H
end end end;
clear HEv AG; rename AG2 into AG  end end.
Ltac reseat_k kk HS HJ2 HP2 keep AG kept_tac :=
let K := constr:(kk) in
let HS2 := fresh "HS2" in
lazymatch type of HJ2 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?W2 ?mem2 _ _ =>
lazymatch type of HP2 with aregs_preserved _ ?regs2 =>
jafter_call_keep_hi HS K regs2 (mrestrict (w_H W2) mem2) HP2 keep HS2 end end;
match type of HS2 with ?Q -> _ =>
let HQ := fresh "HQ" in
assert (HQ : Q); [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil; kept_tac | specialize (HS2 HQ); clear HQ ] end;
clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
let AG2 := fresh "AG" in let Ev := fresh "E" in let HEv := fresh "HE" in
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
by (intros nn Hnn; rewrite HEv; rewrite ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; apply AG; exact Hnn);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 33 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; exact H);
clear H; rename H2 into H
end end end;
clear HEv AG; rename AG2 into AG | st_ok _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
let HEIv := fresh "HEI" in
lazymatch type of HEv with
| _ = havoc ?Eo ?kk ?ws => lazymatch goal with Ho : img_env ?val ?lim Eo |- _ =>
pose proof (img_env_havoc_hi Eo kk ws Ho ltac:(cbv; lia)) as HEIv; rewrite <- HEv in HEIv end
| _ = ?En => try (lazymatch goal with Hn : img_env _ _ En |- _ => rewrite <- HEv in Hn end) end;
repeat match goal with H : img_env _ _ (ewset _ _ _) |- _ => clear H end;
assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; apply AG; exact Hnn);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 33 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; exact H);
clear H; rename H2 into H
end end end;
clear HEv AG; rename AG2 into AG  end end.
Ltac fptok := let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
intros a Ha Hn; apply inFP_token in Hn; first [lia | unfold SB in *; lia].
Ltac evalE_in AG Hrr :=
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr; rewrite ?ew_ewset_other in Hrr by lia;
repeat match type of Hrr with context [ew ?Ex ?n] => match goal with H : ew Ex n = Z_to_bv 64 _ |- _ => rewrite H in Hrr end end;
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
repeat match type of Hrr with context [ew Ev ?n] => lazymatch (eval cbv in (Nat.ltb n 33)) with true => rewrite (AG n) in Hrr by lia end end end;
repeat match type of Hrr with context [ew ?Ex ?n] => match goal with H : ew Ex n = Z_to_bv 64 _ |- _ => rewrite H in Hrr end end;
repeat match type of Hrr with context [bv_unsigned (ew ?Ex 2)] => match goal with H : bv_unsigned (ew Ex 2) = _ |- _ => rewrite H in Hrr end end;
rewrite ?unsigned_lit_small in Hrr by (unfold SB; lia); unfold SB in Hrr.
Ltac xwinF Hrr Hpf :=
lazymatch type of Hrr with
| context [_ / 8] =>
lazymatch goal with Hia : xfacts (in_app ?pfv 1264) |- _ =>
lazymatch type of Hrr with _ <= ?a < _ + ?Fv / 8 + ?k =>
lazymatch goal with XF : xfacts (_ /\ _) |- _ =>
refine (fshadow_not_app Fv 32 pfv 1264 a _ _ Hia _ _);
[ clear - XF; unfold xfacts in XF; lia | clear - XF; unfold xfacts in XF; lia
| clear - Hrr; unfold SB in *; lia | clear - Hpf; lia ] end end end
| _ => first
[ lazymatch goal with XF : xfacts (_ /\ _) |- _ => clear - XF Hrr Hpf; unfold xfacts in XF; lia end
|
lazymatch goal with Hno : forall x, _ <= x < _ + 1264 -> ~ aowned _ _ _ x |- _ =>
lazymatch goal with Hown : aowned _ _ _ ?fl |- _ =>
let av := lazymatch type of Hpf with _ <= ?a < _ => a end in
apply (Hno _ Hpf); replace fl with av in Hown by (clear - Hrr; lia); exact Hown end end ]
end.
Ltac xwinI Hrr Himg :=
first [ let Hr := fresh "Hr" in pose proof (pa_img_range _ Himg) as Hr;
lazymatch goal with XF : xfacts (_ /\ _) |- _ => clear - XF Hrr Hr; unfold xfacts in XF; unfold SB in *; lia end
|
lazymatch goal with Hni : ~ in_img _ ?fl |- _ =>
let av := lazymatch type of Himg with in_img _ ?a => a end in
apply Hni; replace fl with av by (clear - Hrr; lia); exact Himg end ].
Ltac xwin_one AG Hrr :=
first [ exfalso; clear - Hrr; lia
| evalE_in AG Hrr; split; [ let Hpf := fresh "Hpf" in intros Hpf; xwinF Hrr Hpf | let Himg := fresh "Himg" in intros Himg; xwinI Hrr Himg ] ].
Ltac xwin_loop AG Hin Hrr :=
lazymatch type of Hin with
| False => destruct Hin
| _ \/ _ => let Hq := fresh "Hq" in let Hin2 := fresh "Hin" in
destruct Hin as [Hq | Hin2]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; xwin_one AG Hrr | xwin_loop AG Hin2 Hrr]
end.
Ltac xsink_stretch HFr HSINK :=
let made := match goal with H : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => constr:(false) | _ => constr:(true) end in
lazymatch type of HFr with frame_of ?Ef _ _ _ =>
lazymatch made with true => let AG0 := fresh "AG0" in assert (AG0 : forall n, (n < 33)%nat -> ew Ef n = ew Ef n) by (intros; reflexivity) | false => idtac end end;
let AG := lazymatch goal with H : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => H end in
let AIL := lazymatch goal with H : asink_img_laws _ _ _ |- _ => H end in
lazymatch goal with |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
lazymatch type of HSINK with asink_at ?sg ?Kv (mrestrict (w_H ?Wv) ?mo) ?mdo ?pf ?SG =>
let UN := fresh "UN" in let H2 := fresh "HSINK" in
pose proof (kept_of_frame (segs:=sg) _ _ _ _ _ (fun a => ~ (pf <= a < pf + 1264) /\ ~ in_img sg a) HFr
ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
intros b wlo whi a Hin Hrr; vm_compute in Hin; xwin_loop AG Hin Hrr)) as UN;
cbn beta in UN;
assert (H2 : asink_at sg Kv (mrestrict (w_H Wv) (ms_mem msn)) mdn pf SG);
[ apply (asink_at_model sg Kv _ mdo); [reflexivity | reflexivity |];
apply (asink_at_frame sg Kv (mrestrict (w_H Wv) mo)); [|exact HSINK];
let a := fresh "a" in let Ha := fresh "Ha" in let Hn1 := fresh "Hn" in let Hn2 := fresh "Hn" in
intros a Ha; apply (mbyte_of_aview sg); cbn [ms_mem]; apply UN;
[ destruct Ha as [Ha | Ha];
[ lazymatch goal with XF : xfacts (_ /\ _) |- _ => clear - XF Ha; unfold xfacts in XF; unfold FILE_BLOCK in Ha; lia end
| pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))); lia ]
| intros [Hn1 Hn2]; destruct Ha as [Ha | Ha];
[ apply Hn1; unfold FILE_BLOCK in Ha; exact Ha | exact (Hn2 (proj1 (ail_env _ _ _ AIL a Ha))) ] ]
| clear UN HSINK; rename H2 into HSINK; lazymatch made with true => clear AG | false => idtac end ] end end.
Ltac xsink_sub HJt HSINK Hin Hin2 :=
let AIL := lazymatch goal with H : asink_img_laws _ _ _ |- _ => H end in
lazymatch type of HJt with ajournal ?sg ?Bv _ _ ?FP _ _ _ _ _ _ _ _ ?W2 ?mem2 ?md2 _ =>
lazymatch type of HSINK with asink_at _ ?Kv _ _ ?pf ?SG =>
let H2 := fresh "HSINK" in
assert (H2 : asink_at sg Kv (mrestrict (w_H W2) mem2) md2 pf SG);
[ eapply (asink_at_kept sg Bv Kv AIL); [exact HJt | | exact Hin | exact Hin2 | | exact HSINK];
[ first [exact sink_closed_nil | apply sink_closed_ablocks_fp; repeat (constructor; [cbn; lia|]); constructor]
| let i := fresh "i" in let Hi := fresh "Hi" in let HF := fresh "HF" in
intros i Hi HF; first [exact (inFP_nil _ HF)
| let p' := fresh "p'" in let n' := fresh "n'" in let Hpn := fresh "Hpn" in let Hpa := fresh "Hpa" in
destruct (inFP_ablocks_fp_inv _ _ HF) as (p' & n' & Hpn & Hpa); cbn in Hpn;
repeat (destruct Hpn as [Hpn | Hpn]; [injection Hpn as <- <-; rqs Hpa;
lazymatch goal with XF : xfacts (_ /\ _) |- _ => clear - XF Hi Hpa; unfold xfacts in XF; unfold FILE_BLOCK in Hi; lia end |]);
destruct Hpn ] ]
| clear HSINK; rename H2 into HSINK ] end end.
Ltac xsink_intrin Hfr HSM HSINK :=
let AIL := lazymatch goal with H : asink_img_laws _ _ _ |- _ => H end in
lazymatch type of Hfr with forall a, _ -> _ -> _ -> aview ?sg (w_H ?W2) ?mem2 a = aview _ _ ?memT a =>
lazymatch type of HSM with same_but_materialized ?mdc ?md2 =>
lazymatch type of HSINK with asink_at _ ?Kv _ _ ?pf ?SG =>
let H2 := fresh "HSINK" in let Q := fresh "Q" in
pose proof (same_but_materialized_frame mdc md2 HSM) as Q;
assert (H2 : asink_at sg Kv (mrestrict (w_H W2) mem2) md2 pf SG);
[ apply (asink_at_model sg Kv _ mdc); [unfold m_fs; rewrite (proj1 (proj2 (proj2 (proj2 (proj2 Q))))); reflexivity | unfold m_fds; rewrite (proj1 Q); reflexivity |];
apply (asink_at_frame sg Kv (mrestrict (w_H W2) memT)); [|exact HSINK];
let a := fresh "a" in let Ha := fresh "Ha" in let Hr := fresh "Hr" in
intros a Ha; apply (mbyte_of_aview sg);
(destruct Ha as [Ha | Ha]; [unfold FILE_BLOCK in Ha | pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))) as Hr]);
(apply Hfr; unfold ESTACK, ASTACK; lazymatch goal with XF : xfacts (_ /\ _) |- _ => first [clear - XF Ha; unfold xfacts in XF; lia | clear - XF Ha Hr; unfold xfacts in XF; lia] end)
| clear Q HSINK; rename H2 into HSINK ] end end end.
Ltac xnone_loop AG Hin Hrr :=
lazymatch type of Hin with
| False => destruct Hin
| _ \/ _ => let Hq := fresh "Hq" in let Hin2 := fresh "Hin" in
destruct Hin as [Hq | Hin2];
[ injection Hq as <- <- <-; cbn [base_val] in Hrr;
first [ exfalso; clear - Hrr; lia | evalE_in AG Hrr; let Himg := fresh "Himg" in intros Himg; xwinI Hrr Himg ]
| xnone_loop AG Hin2 Hrr ]
end.
Ltac xnone_stretch HFr HSNK :=
let AG := lazymatch goal with H : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => H end in
let AIL := lazymatch goal with H : asink_img_laws _ _ _ |- _ => H end in
lazymatch goal with |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
lazymatch type of HSNK with asink_none ?sg ?Kv (mrestrict (w_H ?Wv) ?mo) ?mdo =>
let UN := fresh "UN" in let H2 := fresh "HSNK" in
pose proof (kept_of_frame (segs:=sg) _ _ _ _ _ (fun a => ~ in_img sg a) HFr
ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
intros b wlo whi a Hin Hrr; vm_compute in Hin; xnone_loop AG Hin Hrr)) as UN;
cbn beta in UN;
assert (H2 : asink_none sg Kv (mrestrict (w_H Wv) (ms_mem msn)) mdn);
[ apply (asink_none_model sg Kv _ mdo); [reflexivity|];
apply (asink_none_frame sg Kv (mrestrict (w_H Wv) mo)); [|exact HSNK];
let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
intros a Ha; apply (mbyte_of_aview sg); cbn [ms_mem]; apply UN;
[ pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))); lia
| intros Hn; exact (Hn (proj1 (ail_env _ _ _ AIL a Ha))) ]
| clear UN HSNK; rename H2 into HSNK ] end end.
