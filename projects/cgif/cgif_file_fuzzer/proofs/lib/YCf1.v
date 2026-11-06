(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n YI0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YB1v YCef YF0l YCej YCeh YCem YCek YCei YCep YCeo YCes YCew YCex YCer YCfm YCf5 YCf9 YCf7.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Set Hyps Limit 8. Set Printing Depth 14. Set Printing Width 250.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Variable FP : list (Z * Z).
Variable POST : rtcx -> world tfibsegs -> config -> Prop.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis FP0 : FP = [].
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy A_asan_memcpy.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
Lemma rt_B_aux : rt_from B MT FP POST ss_C (INV_C B MT) -> rt_from B MT FP POST ss_D (INV_D B MT FP) -> rt_from B MT FP POST ss_B (INV_0 B MT 0).
Proof.
intros RC RD. rt_prelude.
pose proof HINV as (Hk0 & Hacc & Eab3).
relowRT HS AG E10 E11 E32 E10n E11n E32n.
pose proof (proj1 (proj2 HJ3)) as Hly3. pose proof Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo3 & Ehi3 & _).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 70%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict _ msX) i r HS ltac:(vm_compute; reflexivity)) as HR70; cbn [ms_mem restrict] in HR70 end.
assert (B70 : bv_unsigned (ew E 70) = sp1) by (rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1; lia).
assert (B75 : bv_unsigned (ew E 75) = F) by (rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia).
assert (HpR : 4096 <= p /\ p + n <= alloc_ceiling).
{ destruct Hpn as [[Hn0 HpE] | [Hnr Hin]].
- rewrite HpE, Hn0. unfold A_EMPTY. clear - C1. lia.
- assert (Hp3 : In (p, n) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hin).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n (proj1 HJ3) Hp3) as (_ & Hp4096 & Hpceil & _).
pose proof (req_size_pos n ltac:(clear - Hnr; lia)) as [_ Hrq]. clear - Hp4096 Hpceil Hrq. lia. }
pose proof (field_of_region _ _ 70%nat sp1 _ _ _ _ _ 8 8 (SOff 10 0) p HR70 B70 ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite (AG 10%nat) by lia; rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; clear - HpR C1 Hn26; lia) ltac:(cbn; clear; lia)) as Vp.
pose proof (field_of_region _ _ 70%nat sp1 _ _ _ _ _ 16 8 (SOff 11 0) n HR70 B70 ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite (AG 11%nat) by lia; rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; clear - Hn26; lia) ltac:(cbn; clear; lia)) as Vn.
pose proof (field_of_region _ _ 70%nat sp1 _ _ _ _ _ 24 8 (SLit 0) 0 HR70 B70 ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as Vc.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vp, Vn, Vc. clear HR70.
replace (sp1 + 16) with (sp1 + 8 + 8) in Vn by (clear; lia). replace (sp1 + 24) with (sp1 + 8 + 16) in Vc by (clear; lia).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := eval vm_compute in (idx_of (fun r => match YP09.r_base r with Some 75%nat => Z.eqb (YP09.r_lo r) 32 | _ => false end) rs) in
let r := eval vm_compute in (nth i rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict _ msX) i r HS ltac:(vm_compute; reflexivity)) as HR75; cbn [ms_mem restrict] in HR75 end.
pose proof (field_of_region _ _ 75%nat F _ _ _ _ _ 32 8 (SLit 0) 0 HR75 B75 ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as Vz32.
pose proof (field_of_region _ _ 75%nat F _ _ _ _ _ 40 8 (SLit 0) 0 HR75 B75 ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as Vz40.
pose proof (field_of_region _ _ 75%nat F _ _ _ _ _ 62 2 (SLit 0) 0 HR75 B75 ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as Vz62.
pose proof (field_of_region _ _ 75%nat F _ _ _ _ _ 64 8 (SLit 0) 0 HR75 B75 ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as Vz64.
pose proof (field_of_region _ _ 75%nat F _ _ _ _ _ 72 8 (SLit 0) 0 HR75 B75 ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as Vz72.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vz32, Vz40, Vz62, Vz64, Vz72. clear HR75.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let rs2 := eval vm_compute in
(List.filter (fun r => match YP09.r_base r with
| Some 70%nat => false
| Some 75%nat => negb (Z.eqb (YP09.r_lo r) 32)
| _ => true end) rs) in
pose proof (st_ok_submem tfibsegs Ex ssx (restrict _ msX) rs2 HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
assert (HB3 : rd_src B ly3 S3 p n).
{ destruct Hpn as [[Hn0 HpE] | [Hnr Hin]]; [right; split; [exact Hn0 | exact HpE] | left; split; [clear - Hnr; lia | rewrite Eab3; exact Hin]]. }
assert (Hpdst : rboxed (forall d m, F <= d -> d + m <= F + 256 -> 0 <= m -> d + m <= p \/ p + n <= d)).
{ unfold rboxed. intros d m Hd1 Hd2 Hm. destruct Hpn as [[Hn0 HpE] | [Hnr Hin]].
- rewrite HpE, Hn0. unfold A_EMPTY. clear - Hd1 Hd2 Hm HFhigh_img. unfold off_img in HFhigh_img. lia.
- assert (Hp3 : In (p, n) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hin).
pose proof (sep_block_frame tfibsegs B LAWS ly3 S3 _ _ _ p n 2 fpos (proj1 HJ3) Hp3 Hfin3) as D.
unfold zdisjoint in D. cbn [fst snd] in D. change (fs_frame_bytes 2) with 256 in D. rewrite EFA3 in D. fold F in D.
pose proof (req_size_pos n ltac:(clear - Hnr; lia)) as [_ Hrq]. clear - D Hd1 Hd2 Hm Hrq. lia. }
assert (HSPB : alloc_ceiling <= spZ regs - LLVMF_STK /\ spZ regs <= 2 ^ 47) by (clear - Hceil Hslo Hshi H47 Hstk0; lia).
set (Zsm := fun a : Z => spZ regs - 96 <= a < spZ regs \/ F <= a < F + 32 \/ F + 80 <= a < F + 256).
reshok HS.
aj_run_to_tok tfibtbl_lib_ok HS HJ3 SHOK RTBspan A_readdata.
{ awrRT AG fpos F EFA3. }
unrunRD HFr Zsm Usp B70 Hsp1 UN1. clear HF HFr HG.
vkeepUN UN1 Vp Vn Vc ltac:(first [clear - Hi Hsp1 HSPB C1 FFS; lia | subst Zsm; cbn beta; clear - Hi Hsp1 HFceil Hceil Hslo FFS C1; lia]).
lazymatch type of UN1 with forall a, _ -> _ -> aview _ _ ?m2 a = _ =>
vkeep Vz32 (w_H W3) m2 ltac:(apply UN1; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]);
vkeep Vz40 (w_H W3) m2 ltac:(apply UN1; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]);
vkeep Vz62 (w_H W3) m2 ltac:(apply UN1; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]);
vkeep Vz64 (w_H W3) m2 ltac:(apply UN1; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]);
vkeep Vz72 (w_H W3) m2 ltac:(apply UN1; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]) end.
clear UN1.
gcfgRA HS E88 RA48.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ ly3 S3 W3 (ms_mem msX) _ _ |- _ =>
assert (RAstC : range_addressable (aview tfibsegs (w_H W3) (ms_mem msX)) SHADOW_OFF (sp1 + 8) 24)
by (apply (RA_stack B LAWS ly3 S3 W3 (ms_mem msX) _ (sp1 + 8) 24 (proj1 HJc)); [rewrite Elo3; clear - Hsp1 Hslo FFS; lia | rewrite Ehi3; clear - Hsp1 Hshi; lia | apply sp1_st8; exact Hsp1al | reflexivity | clear; lia]);
pose proof HJc as HJcall end end.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (aj_readdata_at B TL LAWS AMEMCPY _ (ms_regs msX) (ms_mem msX) LLVMF_STK (spZ regs) FP ly S W mem md [(2, fpos)] ly3 S3 _ k
(sp1 + 8) (F + 56) 2 p n 0 (sp1 - spZ regs) (Z_to_bv 64 RT_rd1_ra));
[ exact HJcall
| rewrite Ra0; evalE AG
| rewrite Ra1; evalE AG
| rewrite Ra2; reflexivity
| rewrite Rgp; evalE AG; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
| rewrite Rtp; evalE AG; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
| exact Rra
| vm_compute; reflexivity
| unfold spZ at 1; rewrite Rsp; evalE AG
| rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity
| clear - Hsp1; lia
| rewrite FFS; unfold ESTACK; clear - Hsp1; lia
| apply sp1_st8; exact Hsp1al
| clear; lia
| clear - Hsp1; lia
| exact RAstC
| exact Vp | exact Vn | exact Vc
| exact HB3 | clear - Hn26; lia
| clear; lia | clear - HF4096; lia
| intros a Ha; split; [right; right; right; exists 2, fpos; split; [left; reflexivity | left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 2) with 256; rewrite EFA3; fold F; clear - Ha; lia] | unfold ESTACK; clear - Ha Hsp1 HFceil Hceil Hslo Hstk0 C1 FFS; lia]
| apply amem_range_high; [clear; lia | clear - HFhigh HFhigh_img HFceil C1 C3; ceil; unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; zone_lia | clear - HFceil; lia]
| eapply range_addressable_sub; [exact RA48 | clear; lia | clear; lia]
| intros _; eapply (shadow_hull_vis_of_frame tfibsegs B LAWS ly3 S3 _ _ _ 2 fpos (F + 56) 2 (proj1 HJcall) Hfin3); [rewrite EFA3; fold F; clear; lia | rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia | clear; lia]
| right; left; clear - HFceil Hceil Hslo Hsp1 FFS C1; lia
| unfold rboxed in Hpdst; apply (Hpdst (F + 56) 2); clear; lia ] end. }
cbv beta. intros W1_ c1_ _ (-> & regs1 & mem1 & mdq1 & r1 & cur1 & -> & HJ4 & HP1 & Ha01 & Hr1 & Vp' & Vn' & Vc' & Hfr1 & Hpres1 & Hio1).
replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hfr1 by (clear; lia).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp RAstC RA48 Vp Vn Vc. rename Vp' into Vp. rename Vn' into Vn. rename Vc' into Vc.
assert (Hcb1 : 0 <= cur1 <= n) by (clear - Hr1 Hn26; destruct Hr1 as [(_ & X & -> & _)|(_ & _ & -> & _)]; lia).
assert (Hrc1 : rboxed ((r1 = 0 /\ cur1 = 0 + 2) \/ (r1 = 2 ^ 64 - 1 /\ cur1 = n /\ n < 0 + 2))) by (clear - Hr1; unfold rboxed; destruct Hr1 as [(A1 & _ & A2 & _)|(A1 & X & A2 & _)]; [left; split; assumption | right; split; [exact A1 | split; [exact A2 | exact X]]]).
assert (RD1 : r1 = 0 -> forall i, 0 <= i < 2 -> exists b, PB (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) (0 + i) b /\ aview tfibsegs (w_H W3) mem1 (F + 56 + i) = Some b).
{ intros Hz i Hi. destruct Hr1 as [(_ & Hle & _ & Hcp)|(Hne & _)]; [|exfalso; clear - Hne Hz; lia].
destruct Hpn as [[Hn0 _] | [Hnpos Hpin]]; [exfalso; clear - Hn0 Hle ; unfold rboxed in *; lia|].
assert (Hrq : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0) as [He|Hne]; [exfalso; clear - Hnpos He; lia | reflexivity]).
assert (Hpin3 : In (p, n) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hpin).
pose proof HJcall as HJc. rewrite FP0 in HJc.
destruct (PB_at_now B _ (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) _ _ _ _ _ _ _ (0 + i) LAWS HAR HJc Hpin Hpin3 Hrq ltac:(cbn [c_n]; unfold rboxed in *; clear - Hi Hle ; lia)) as (b & HPB & HA).
exists b. split; [exact HPB|]. rewrite (Hcp i Hi). cbn [c_p] in HA. replace (p + 0 + i) with (p + (0 + i)) by (clear; lia). exact HA. }
clear Hr1 HJcall.
vkeep Vz32 (w_H W3) mem1 ltac:(apply Hfr1; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
vkeep Vz40 (w_H W3) mem1 ltac:(apply Hfr1; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
vkeep Vz62 (w_H W3) mem1 ltac:(apply Hfr1; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
vkeep Vz64 (w_H W3) mem1 ltac:(apply Hfr1; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
vkeep Vz72 (w_H W3) mem1 ltac:(apply Hfr1; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
reseatL HS HJ4 HP1 [0; 1; 2; 3; 4; 5; 6; 7]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot4 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell4 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar4 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar4 | clear; lia] ] end
| eapply region_kept_aview;
[ evalE AG
| intros a Ha; apply Hfr1; clear - Ha HF4096 HFceil HFhigh HFhigh_img Hceil Hslo Hshi H47 Hstk0 Hsp1 HF8lo HF8hi FFS C1 C2 C3; unfold ESTACK, SB in *; zone_lia
| exact Hpres1 ]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
clear Kgot4 Kcell4 Kguar4 Kuar4 Hpres1.
rebv HS E70 RF B70 B75.
rreg HS (10%bv : bv 5) Rr1. cbn [ms_regs] in Rr1. rewrite Ha01 in Rr1. symmetry in Rr1. unfold w64 in Rr1. clear Ha01.
assert (Hrr1 : 0 <= r1 < 2 ^ 64) by (clear - Hrc1; unfold rboxed in Hrc1; lia).
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS. reshok HS.
aj_run_to_tok tfibtbl_lib_ok HS HJ4 SHOK RTBspan A_readdata.
{ awrRT AG fpos F EFA3. }
unrunRD HFr Zsm Usp B70 Hsp1 UNs. clear HF HFr HG.
vkeepUN UNs Vp Vn Vc ltac:(first [clear - Hi Hsp1 HSPB C1 FFS; lia | subst Zsm; cbn beta; clear - Hi Hsp1 HFceil Hceil Hslo FFS C1; lia]).
lazymatch type of UNs with forall a, _ -> _ -> aview _ _ ?m2 a = _ =>
vkeep Vz32 (w_H W3) m2 ltac:(apply UNs; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]);
vkeep Vz40 (w_H W3) m2 ltac:(apply UNs; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]);
vkeep Vz62 (w_H W3) m2 ltac:(apply UNs; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]);
vkeep Vz64 (w_H W3) m2 ltac:(apply UNs; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]);
vkeep Vz72 (w_H W3) m2 ltac:(apply UNs; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]);
rdkeep RD1 (w_H W3) m2 ltac:(apply UNs; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]) end.
clear UNs.
gcfgRA HS E88 RA48.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ ly3 S3 W3 (ms_mem msX) _ _ |- _ =>
assert (RAstC : range_addressable (aview tfibsegs (w_H W3) (ms_mem msX)) SHADOW_OFF (sp1 + 8) 24)
by (apply (RA_stack B LAWS ly3 S3 W3 (ms_mem msX) _ (sp1 + 8) 24 (proj1 HJc)); [rewrite Elo3; clear - Hsp1 Hslo FFS; lia | rewrite Ehi3; clear - Hsp1 Hshi; lia | apply sp1_st8; exact Hsp1al | reflexivity | clear; lia]);
pose proof HJc as HJcall end end.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (aj_readdata_at B TL LAWS AMEMCPY _ (ms_regs msX) (ms_mem msX) LLVMF_STK (spZ regs) FP ly S W mem md [(2, fpos)] ly3 S3 _ k
(sp1 + 8) (F + 58) 2 p n cur1 (sp1 - spZ regs) (Z_to_bv 64 RT_rd2_ra));
[ exact HJcall
| rewrite Ra0; evalE AG
| rewrite Ra1; evalE AG
| rewrite Ra2; reflexivity
| rewrite Rgp; evalE AG; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
| rewrite Rtp; evalE AG; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
| exact Rra
| vm_compute; reflexivity
| unfold spZ at 1; rewrite Rsp; evalE AG
| rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity
| clear - Hsp1; lia
| rewrite FFS; unfold ESTACK; clear - Hsp1; lia
| apply sp1_st8; exact Hsp1al
| clear; lia
| clear - Hsp1; lia
| exact RAstC
| exact Vp | exact Vn | exact Vc
| exact HB3 | clear - Hcb1; lia
| clear; lia | clear - HF4096; lia
| intros a Ha; split; [right; right; right; exists 2, fpos; split; [left; reflexivity | left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 2) with 256; rewrite EFA3; fold F; clear - Ha; lia] | unfold ESTACK; clear - Ha Hsp1 HFceil Hceil Hslo Hstk0 C1 FFS; lia]
| apply amem_range_high; [clear; lia | clear - HFhigh HFhigh_img HFceil C1 C3; ceil; unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; zone_lia | clear - HFceil; lia]
| eapply range_addressable_sub; [exact RA48 | clear; lia | clear; lia]
| intros _; eapply (shadow_hull_vis_of_frame tfibsegs B LAWS ly3 S3 _ _ _ 2 fpos (F + 58) 2 (proj1 HJcall) Hfin3); [rewrite EFA3; fold F; clear; lia | rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia | clear; lia]
| right; left; clear - HFceil Hceil Hslo Hsp1 FFS C1; lia
| unfold rboxed in Hpdst; apply (Hpdst (F + 58) 2); clear; lia ] end. }
cbv beta. intros W2_ c2_ _ (-> & regs2 & mem2 & mdq2 & r2 & cur2 & -> & HJ5 & HP2 & Ha02 & Hr2 & Vp' & Vn' & Vc' & Hfr2 & Hpres2 & Hio2).
replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hfr2 by (clear; lia).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp RAstC RA48 Vp Vn Vc. rename Vp' into Vp. rename Vn' into Vn. rename Vc' into Vc.
assert (Hcb2 : 0 <= cur2 <= n) by (clear - Hr2 Hcb1; destruct Hr2 as [(_ & X & -> & _)|(_ & _ & -> & _)]; lia).
assert (Hrc2 : rboxed ((r2 = 0 /\ cur2 = cur1 + 2) \/ (r2 = 2 ^ 64 - 1 /\ cur2 = n /\ n < cur1 + 2))) by (clear - Hr2; unfold rboxed; destruct Hr2 as [(A1 & _ & A2 & _)|(A1 & X & A2 & _)]; [left; split; assumption | right; split; [exact A1 | split; [exact A2 | exact X]]]).
assert (RD2 : r2 = 0 -> forall i, 0 <= i < 2 -> exists b, PB (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) (2 + i) b /\ aview tfibsegs (w_H W3) mem2 (F + 58 + i) = Some b).
{ intros Hz i Hi. destruct Hr2 as [(_ & Hle & _ & Hcp)|(Hne & _)]; [|exfalso; clear - Hne Hz; lia].
assert (Hpv : cur1 = 2) by (unfold rboxed in *; clear - Hle Hrc1 Hcb1; lia).
destruct Hpn as [[Hn0 _] | [Hnpos Hpin]]; [exfalso; clear - Hn0 Hle Hrc1 Hcb1; unfold rboxed in *; lia|].
assert (Hrq : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0) as [He|Hne]; [exfalso; clear - Hnpos He; lia | reflexivity]).
assert (Hpin3 : In (p, n) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hpin).
pose proof HJcall as HJc. rewrite FP0 in HJc.
destruct (PB_at_now B _ (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) _ _ _ _ _ _ _ (2 + i) LAWS HAR HJc Hpin Hpin3 Hrq ltac:(cbn [c_n]; unfold rboxed in *; clear - Hi Hle Hrc1 Hcb1; lia)) as (b & HPB & HA).
exists b. split; [exact HPB|]. rewrite (Hcp i Hi). cbn [c_p] in HA. rewrite Hpv. replace (p + 2 + i) with (p + (2 + i)) by (clear; lia). exact HA. }
clear Hr2 HJcall.
vkeep Vz32 (w_H W3) mem2 ltac:(apply Hfr2; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
vkeep Vz40 (w_H W3) mem2 ltac:(apply Hfr2; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
vkeep Vz62 (w_H W3) mem2 ltac:(apply Hfr2; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
vkeep Vz64 (w_H W3) mem2 ltac:(apply Hfr2; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
vkeep Vz72 (w_H W3) mem2 ltac:(apply Hfr2; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
rdkeep RD1 (w_H W3) mem2 ltac:(apply Hfr2; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ4 Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ5 Kgot4 Kcell4 Kguar4 Kuar4.
reseatL HS HJ5 HP2 [0; 1; 2; 3; 4; 5; 6; 7]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot4 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell4 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar4 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar4 | clear; lia] ] end
| eapply region_kept_aview;
[ evalE AG
| intros a Ha; apply Hfr2; clear - Ha HF4096 HFceil HFhigh HFhigh_img Hceil Hslo Hshi H47 Hstk0 Hsp1 HF8lo HF8hi FFS C1 C2 C3; unfold ESTACK, SB in *; zone_lia
| exact Hpres2 ]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
clear Kgot4 Kcell4 Kguar4 Kuar4 Hpres2.
rebv HS E70 RF B70 B75.
rreg HS (10%bv : bv 5) Rr2. cbn [ms_regs] in Rr2. rewrite Ha02 in Rr2. symmetry in Rr2. unfold w64 in Rr2. clear Ha02.
assert (Hrr2 : 0 <= r2 < 2 ^ 64) by (clear - Hrc2; unfold rboxed in Hrc2; lia).
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS. reshok HS.
aj_run_to_tok tfibtbl_lib_ok HS HJ5 SHOK RTBspan A_readdata.
{ awrRT AG fpos F EFA3. }
unrunRD HFr Zsm Usp B70 Hsp1 UNs. clear HF HFr HG.
vkeepUN UNs Vp Vn Vc ltac:(first [clear - Hi Hsp1 HSPB C1 FFS; lia | subst Zsm; cbn beta; clear - Hi Hsp1 HFceil Hceil Hslo FFS C1; lia]).
lazymatch type of UNs with forall a, _ -> _ -> aview _ _ ?m2 a = _ =>
vkeep Vz32 (w_H W3) m2 ltac:(apply UNs; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]);
vkeep Vz40 (w_H W3) m2 ltac:(apply UNs; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]);
vkeep Vz62 (w_H W3) m2 ltac:(apply UNs; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]);
vkeep Vz64 (w_H W3) m2 ltac:(apply UNs; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]);
vkeep Vz72 (w_H W3) m2 ltac:(apply UNs; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]);
rdkeep RD1 (w_H W3) m2 ltac:(apply UNs; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]);
rdkeep RD2 (w_H W3) m2 ltac:(apply UNs; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]) end.
clear UNs.
gcfgRA HS E88 RA48.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ ly3 S3 W3 (ms_mem msX) _ _ |- _ =>
assert (RAstC : range_addressable (aview tfibsegs (w_H W3) (ms_mem msX)) SHADOW_OFF (sp1 + 8) 24)
by (apply (RA_stack B LAWS ly3 S3 W3 (ms_mem msX) _ (sp1 + 8) 24 (proj1 HJc)); [rewrite Elo3; clear - Hsp1 Hslo FFS; lia | rewrite Ehi3; clear - Hsp1 Hshi; lia | apply sp1_st8; exact Hsp1al | reflexivity | clear; lia]);
pose proof HJc as HJcall end end.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (aj_readdata_at B TL LAWS AMEMCPY _ (ms_regs msX) (ms_mem msX) LLVMF_STK (spZ regs) FP ly S W mem md [(2, fpos)] ly3 S3 _ k
(sp1 + 8) (F + 48) 4 p n cur2 (sp1 - spZ regs) (Z_to_bv 64 RT_rd3_ra));
[ exact HJcall
| rewrite Ra0; evalE AG
| rewrite Ra1; evalE AG
| rewrite Ra2; reflexivity
| rewrite Rgp; evalE AG; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
| rewrite Rtp; evalE AG; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
| exact Rra
| vm_compute; reflexivity
| unfold spZ at 1; rewrite Rsp; evalE AG
| rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity
| clear - Hsp1; lia
| rewrite FFS; unfold ESTACK; clear - Hsp1; lia
| apply sp1_st8; exact Hsp1al
| clear; lia
| clear - Hsp1; lia
| exact RAstC
| exact Vp | exact Vn | exact Vc
| exact HB3 | clear - Hcb2; lia
| clear; lia | clear - HF4096; lia
| intros a Ha; split; [right; right; right; exists 2, fpos; split; [left; reflexivity | left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 2) with 256; rewrite EFA3; fold F; clear - Ha; lia] | unfold ESTACK; clear - Ha Hsp1 HFceil Hceil Hslo Hstk0 C1 FFS; lia]
| apply amem_range_high; [clear; lia | clear - HFhigh HFhigh_img HFceil C1 C3; ceil; unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; zone_lia | clear - HFceil; lia]
| eapply range_addressable_sub; [exact RA48 | clear; lia | clear; lia]
| intros _; eapply (shadow_hull_vis_of_frame tfibsegs B LAWS ly3 S3 _ _ _ 2 fpos (F + 48) 4 (proj1 HJcall) Hfin3); [rewrite EFA3; fold F; clear; lia | rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia | clear; lia]
| right; left; clear - HFceil Hceil Hslo Hsp1 FFS C1; lia
| unfold rboxed in Hpdst; apply (Hpdst (F + 48) 4); clear; lia ] end. }
cbv beta. intros W3_ c3_ _ (-> & regs3 & mem3 & mdq3 & r3 & cur3 & -> & HJ6 & HP3 & Ha03 & Hr3 & Vp' & Vn' & Vc' & Hfr3 & Hpres3 & Hio3).
replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hfr3 by (clear; lia).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp RAstC RA48 Vp Vn Vc. rename Vp' into Vp. rename Vn' into Vn. rename Vc' into Vc.
assert (Hcb3 : 0 <= cur3 <= n) by (clear - Hr3 Hcb2; destruct Hr3 as [(_ & X & -> & _)|(_ & _ & -> & _)]; lia).
assert (Hrc3 : rboxed ((r3 = 0 /\ cur3 = cur2 + 4) \/ (r3 = 2 ^ 64 - 1 /\ cur3 = n /\ n < cur2 + 4))) by (clear - Hr3; unfold rboxed; destruct Hr3 as [(A1 & _ & A2 & _)|(A1 & X & A2 & _)]; [left; split; assumption | right; split; [exact A1 | split; [exact A2 | exact X]]]).
assert (RD3 : r3 = 0 -> forall i, 0 <= i < 4 -> exists b, PB (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) (4 + i) b /\ aview tfibsegs (w_H W3) mem3 (F + 48 + i) = Some b).
{ intros Hz i Hi. destruct Hr3 as [(_ & Hle & _ & Hcp)|(Hne & _)]; [|exfalso; clear - Hne Hz; lia].
assert (Hpv : cur2 = 4) by (unfold rboxed in *; clear - Hle Hrc1 Hcb1 Hrc2 Hcb2; lia).
destruct Hpn as [[Hn0 _] | [Hnpos Hpin]]; [exfalso; clear - Hn0 Hle Hrc1 Hcb1 Hrc2 Hcb2; unfold rboxed in *; lia|].
assert (Hrq : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0) as [He|Hne]; [exfalso; clear - Hnpos He; lia | reflexivity]).
assert (Hpin3 : In (p, n) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hpin).
pose proof HJcall as HJc. rewrite FP0 in HJc.
destruct (PB_at_now B _ (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) _ _ _ _ _ _ _ (4 + i) LAWS HAR HJc Hpin Hpin3 Hrq ltac:(cbn [c_n]; unfold rboxed in *; clear - Hi Hle Hrc1 Hcb1 Hrc2 Hcb2; lia)) as (b & HPB & HA).
exists b. split; [exact HPB|]. rewrite (Hcp i Hi). cbn [c_p] in HA. rewrite Hpv. replace (p + 4 + i) with (p + (4 + i)) by (clear; lia). exact HA. }
clear Hr3 HJcall.
vkeep Vz32 (w_H W3) mem3 ltac:(apply Hfr3; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
vkeep Vz40 (w_H W3) mem3 ltac:(apply Hfr3; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
vkeep Vz62 (w_H W3) mem3 ltac:(apply Hfr3; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
vkeep Vz64 (w_H W3) mem3 ltac:(apply Hfr3; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
vkeep Vz72 (w_H W3) mem3 ltac:(apply Hfr3; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
rdkeep RD1 (w_H W3) mem3 ltac:(apply Hfr3; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
rdkeep RD2 (w_H W3) mem3 ltac:(apply Hfr3; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ5 Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ6 Kgot4 Kcell4 Kguar4 Kuar4.
reseatL HS HJ6 HP3 [0; 1; 2; 3; 4; 5; 6; 7]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot4 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell4 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar4 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar4 | clear; lia] ] end
| eapply region_kept_aview;
[ evalE AG
| intros a Ha; apply Hfr3; clear - Ha HF4096 HFceil HFhigh HFhigh_img Hceil Hslo Hshi H47 Hstk0 Hsp1 HF8lo HF8hi FFS C1 C2 C3; unfold ESTACK, SB in *; zone_lia
| exact Hpres3 ]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
clear Kgot4 Kcell4 Kguar4 Kuar4 Hpres3.
rebv HS E70 RF B70 B75.
rreg HS (10%bv : bv 5) Rr3. cbn [ms_regs] in Rr3. rewrite Ha03 in Rr3. symmetry in Rr3. unfold w64 in Rr3. clear Ha03.
assert (Hrr3 : 0 <= r3 < 2 ^ 64) by (clear - Hrc3; unfold rboxed in Hrc3; lia).
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS. reshok HS.
aj_run_to_tok tfibtbl_lib_ok HS HJ6 SHOK RTBspan A_readdata.
{ awrRT AG fpos F EFA3. }
unrunRD HFr Zsm Usp B70 Hsp1 UNs. clear HF HFr HG.
vkeepUN UNs Vp Vn Vc ltac:(first [clear - Hi Hsp1 HSPB C1 FFS; lia | subst Zsm; cbn beta; clear - Hi Hsp1 HFceil Hceil Hslo FFS C1; lia]).
lazymatch type of UNs with forall a, _ -> _ -> aview _ _ ?m2 a = _ =>
vkeep Vz32 (w_H W3) m2 ltac:(apply UNs; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]);
vkeep Vz40 (w_H W3) m2 ltac:(apply UNs; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]);
vkeep Vz62 (w_H W3) m2 ltac:(apply UNs; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]);
vkeep Vz64 (w_H W3) m2 ltac:(apply UNs; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]);
vkeep Vz72 (w_H W3) m2 ltac:(apply UNs; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]);
rdkeep RD1 (w_H W3) m2 ltac:(apply UNs; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]);
rdkeep RD2 (w_H W3) m2 ltac:(apply UNs; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]);
rdkeep RD3 (w_H W3) m2 ltac:(apply UNs; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]) end.
clear UNs.
gcfgRA HS E88 RA48.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ ly3 S3 W3 (ms_mem msX) _ _ |- _ =>
assert (RAstC : range_addressable (aview tfibsegs (w_H W3) (ms_mem msX)) SHADOW_OFF (sp1 + 8) 24)
by (apply (RA_stack B LAWS ly3 S3 W3 (ms_mem msX) _ (sp1 + 8) 24 (proj1 HJc)); [rewrite Elo3; clear - Hsp1 Hslo FFS; lia | rewrite Ehi3; clear - Hsp1 Hshi; lia | apply sp1_st8; exact Hsp1al | reflexivity | clear; lia]);
pose proof HJc as HJcall end end.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (aj_readdata_at B TL LAWS AMEMCPY _ (ms_regs msX) (ms_mem msX) LLVMF_STK (spZ regs) FP ly S W mem md [(2, fpos)] ly3 S3 _ k
(sp1 + 8) (F + 52) 4 p n cur3 (sp1 - spZ regs) (Z_to_bv 64 RT_rd4_ra));
[ exact HJcall
| rewrite Ra0; evalE AG
| rewrite Ra1; evalE AG
| rewrite Ra2; reflexivity
| rewrite Rgp; evalE AG; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
| rewrite Rtp; evalE AG; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
| exact Rra
| vm_compute; reflexivity
| unfold spZ at 1; rewrite Rsp; evalE AG
| rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity
| clear - Hsp1; lia
| rewrite FFS; unfold ESTACK; clear - Hsp1; lia
| apply sp1_st8; exact Hsp1al
| clear; lia
| clear - Hsp1; lia
| exact RAstC
| exact Vp | exact Vn | exact Vc
| exact HB3 | clear - Hcb3; lia
| clear; lia | clear - HF4096; lia
| intros a Ha; split; [right; right; right; exists 2, fpos; split; [left; reflexivity | left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 2) with 256; rewrite EFA3; fold F; clear - Ha; lia] | unfold ESTACK; clear - Ha Hsp1 HFceil Hceil Hslo Hstk0 C1 FFS; lia]
| apply amem_range_high; [clear; lia | clear - HFhigh HFhigh_img HFceil C1 C3; ceil; unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; zone_lia | clear - HFceil; lia]
| eapply range_addressable_sub; [exact RA48 | clear; lia | clear; lia]
| intros _; eapply (shadow_hull_vis_of_frame tfibsegs B LAWS ly3 S3 _ _ _ 2 fpos (F + 52) 4 (proj1 HJcall) Hfin3); [rewrite EFA3; fold F; clear; lia | rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia | clear; lia]
| right; left; clear - HFceil Hceil Hslo Hsp1 FFS C1; lia
| unfold rboxed in Hpdst; apply (Hpdst (F + 52) 4); clear; lia ] end. }
cbv beta. intros W4_ c4_ _ (-> & regs4 & mem4 & mdq4 & r4 & cur4 & -> & HJ7 & HP4 & Ha04 & Hr4 & Vp' & Vn' & Vc' & Hfr4 & Hpres4 & Hio4).
replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hfr4 by (clear; lia).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp RAstC RA48 Vp Vn Vc. rename Vp' into Vp. rename Vn' into Vn. rename Vc' into Vc.
assert (Hcb4 : 0 <= cur4 <= n) by (clear - Hr4 Hcb3; destruct Hr4 as [(_ & X & -> & _)|(_ & _ & -> & _)]; lia).
assert (Hrc4 : rboxed ((r4 = 0 /\ cur4 = cur3 + 4) \/ (r4 = 2 ^ 64 - 1 /\ cur4 = n /\ n < cur3 + 4))) by (clear - Hr4; unfold rboxed; destruct Hr4 as [(A1 & _ & A2 & _)|(A1 & X & A2 & _)]; [left; split; assumption | right; split; [exact A1 | split; [exact A2 | exact X]]]).
assert (RD4 : r4 = 0 -> forall i, 0 <= i < 4 -> exists b, PB (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) (8 + i) b /\ aview tfibsegs (w_H W3) mem4 (F + 52 + i) = Some b).
{ intros Hz i Hi. destruct Hr4 as [(_ & Hle & _ & Hcp)|(Hne & _)]; [|exfalso; clear - Hne Hz; lia].
assert (Hpv : cur3 = 8) by (unfold rboxed in *; clear - Hle Hrc1 Hcb1 Hrc2 Hcb2 Hrc3 Hcb3; lia).
destruct Hpn as [[Hn0 _] | [Hnpos Hpin]]; [exfalso; clear - Hn0 Hle Hrc1 Hcb1 Hrc2 Hcb2 Hrc3 Hcb3; unfold rboxed in *; lia|].
assert (Hrq : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0) as [He|Hne]; [exfalso; clear - Hnpos He; lia | reflexivity]).
assert (Hpin3 : In (p, n) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hpin).
pose proof HJcall as HJc. rewrite FP0 in HJc.
destruct (PB_at_now B _ (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) _ _ _ _ _ _ _ (8 + i) LAWS HAR HJc Hpin Hpin3 Hrq ltac:(cbn [c_n]; unfold rboxed in *; clear - Hi Hle Hrc1 Hcb1 Hrc2 Hcb2 Hrc3 Hcb3; lia)) as (b & HPB & HA).
exists b. split; [exact HPB|]. rewrite (Hcp i Hi). cbn [c_p] in HA. rewrite Hpv. replace (p + 8 + i) with (p + (8 + i)) by (clear; lia). exact HA. }
clear Hr4 HJcall.
vkeep Vz32 (w_H W3) mem4 ltac:(apply Hfr4; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
vkeep Vz40 (w_H W3) mem4 ltac:(apply Hfr4; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
vkeep Vz62 (w_H W3) mem4 ltac:(apply Hfr4; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
vkeep Vz64 (w_H W3) mem4 ltac:(apply Hfr4; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
vkeep Vz72 (w_H W3) mem4 ltac:(apply Hfr4; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
rdkeep RD1 (w_H W3) mem4 ltac:(apply Hfr4; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
rdkeep RD2 (w_H W3) mem4 ltac:(apply Hfr4; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
rdkeep RD3 (w_H W3) mem4 ltac:(apply Hfr4; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ6 Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ7 Kgot4 Kcell4 Kguar4 Kuar4.
reseatL HS HJ7 HP4 [0; 1; 2; 3; 4; 5; 6; 7]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot4 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell4 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar4 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar4 | clear; lia] ] end
| eapply region_kept_aview;
[ evalE AG
| intros a Ha; apply Hfr4; clear - Ha HF4096 HFceil HFhigh HFhigh_img Hceil Hslo Hshi H47 Hstk0 Hsp1 HF8lo HF8hi FFS C1 C2 C3; unfold ESTACK, SB in *; zone_lia
| exact Hpres4 ]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
clear Kgot4 Kcell4 Kguar4 Kuar4 Hpres4.
rebv HS E70 RF B70 B75.
rreg HS (10%bv : bv 5) Rr4. cbn [ms_regs] in Rr4. rewrite Ha04 in Rr4. symmetry in Rr4. unfold w64 in Rr4. clear Ha04.
assert (Hrr4 : 0 <= r4 < 2 ^ 64) by (clear - Hrc4; unfold rboxed in Hrc4; lia).
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS. reshok HS.
aj_run_to_tok tfibtbl_lib_ok HS HJ7 SHOK RTBspan A_readdata.
{ awrRT AG fpos F EFA3. }
unrunRD HFr Zsm Usp B70 Hsp1 UNs. clear HF HFr HG.
vkeepUN UNs Vp Vn Vc ltac:(first [clear - Hi Hsp1 HSPB C1 FFS; lia | subst Zsm; cbn beta; clear - Hi Hsp1 HFceil Hceil Hslo FFS C1; lia]).
lazymatch type of UNs with forall a, _ -> _ -> aview _ _ ?m2 a = _ =>
vkeep Vz32 (w_H W3) m2 ltac:(apply UNs; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]);
vkeep Vz40 (w_H W3) m2 ltac:(apply UNs; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]);
vkeep Vz62 (w_H W3) m2 ltac:(apply UNs; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]);
vkeep Vz64 (w_H W3) m2 ltac:(apply UNs; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]);
vkeep Vz72 (w_H W3) m2 ltac:(apply UNs; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]);
rdkeep RD1 (w_H W3) m2 ltac:(apply UNs; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]);
rdkeep RD2 (w_H W3) m2 ltac:(apply UNs; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]);
rdkeep RD3 (w_H W3) m2 ltac:(apply UNs; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]);
rdkeep RD4 (w_H W3) m2 ltac:(apply UNs; [clear - Hi HF4096 HFceil C1; lia | subst Zsm; cbn beta; clear - Hi HFceil Hceil Hslo Hsp1 FFS C1; lia]) end.
clear UNs.
gcfgRA HS E88 RA48.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ ly3 S3 W3 (ms_mem msX) _ _ |- _ =>
assert (RAstC : range_addressable (aview tfibsegs (w_H W3) (ms_mem msX)) SHADOW_OFF (sp1 + 8) 24)
by (apply (RA_stack B LAWS ly3 S3 W3 (ms_mem msX) _ (sp1 + 8) 24 (proj1 HJc)); [rewrite Elo3; clear - Hsp1 Hslo FFS; lia | rewrite Ehi3; clear - Hsp1 Hshi; lia | apply sp1_st8; exact Hsp1al | reflexivity | clear; lia]);
pose proof HJc as HJcall end end.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (aj_readdata_at B TL LAWS AMEMCPY _ (ms_regs msX) (ms_mem msX) LLVMF_STK (spZ regs) FP ly S W mem md [(2, fpos)] ly3 S3 _ k
(sp1 + 8) (F + 60) 2 p n cur4 (sp1 - spZ regs) (Z_to_bv 64 RT_rd5_ra));
[ exact HJcall
| rewrite Ra0; evalE AG
| rewrite Ra1; evalE AG
| rewrite Ra2; reflexivity
| rewrite Rgp; evalE AG; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
| rewrite Rtp; evalE AG; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
| exact Rra
| vm_compute; reflexivity
| unfold spZ at 1; rewrite Rsp; evalE AG
| rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity
| clear - Hsp1; lia
| rewrite FFS; unfold ESTACK; clear - Hsp1; lia
| apply sp1_st8; exact Hsp1al
| clear; lia
| clear - Hsp1; lia
| exact RAstC
| exact Vp | exact Vn | exact Vc
| exact HB3 | clear - Hcb4; lia
| clear; lia | clear - HF4096; lia
| intros a Ha; split; [right; right; right; exists 2, fpos; split; [left; reflexivity | left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 2) with 256; rewrite EFA3; fold F; clear - Ha; lia] | unfold ESTACK; clear - Ha Hsp1 HFceil Hceil Hslo Hstk0 C1 FFS; lia]
| apply amem_range_high; [clear; lia | clear - HFhigh HFhigh_img HFceil C1 C3; ceil; unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; zone_lia | clear - HFceil; lia]
| eapply range_addressable_sub; [exact RA48 | clear; lia | clear; lia]
| intros _; eapply (shadow_hull_vis_of_frame tfibsegs B LAWS ly3 S3 _ _ _ 2 fpos (F + 60) 2 (proj1 HJcall) Hfin3); [rewrite EFA3; fold F; clear; lia | rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia | clear; lia]
| right; left; clear - HFceil Hceil Hslo Hsp1 FFS C1; lia
| unfold rboxed in Hpdst; apply (Hpdst (F + 60) 2); clear; lia ] end. }
cbv beta. intros W5_ c5_ _ (-> & regs5 & mem5 & mdq5 & r5 & cur5 & -> & HJ8 & HP5 & Ha05 & Hr5 & Vp' & Vn' & Vc' & Hfr5 & Hpres5 & Hio5).
replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hfr5 by (clear; lia).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp RAstC RA48 Vp Vn Vc. rename Vp' into Vp. rename Vn' into Vn. rename Vc' into Vc.
assert (Hcb5 : 0 <= cur5 <= n) by (clear - Hr5 Hcb4; destruct Hr5 as [(_ & X & -> & _)|(_ & _ & -> & _)]; lia).
assert (Hrc5 : rboxed ((r5 = 0 /\ cur5 = cur4 + 2) \/ (r5 = 2 ^ 64 - 1 /\ cur5 = n /\ n < cur4 + 2))) by (clear - Hr5; unfold rboxed; destruct Hr5 as [(A1 & _ & A2 & _)|(A1 & X & A2 & _)]; [left; split; assumption | right; split; [exact A1 | split; [exact A2 | exact X]]]).
assert (RD5 : r5 = 0 -> forall i, 0 <= i < 2 -> exists b, PB (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) (12 + i) b /\ aview tfibsegs (w_H W3) mem5 (F + 60 + i) = Some b).
{ intros Hz i Hi. destruct Hr5 as [(_ & Hle & _ & Hcp)|(Hne & _)]; [|exfalso; clear - Hne Hz; lia].
assert (Hpv : cur4 = 12) by (unfold rboxed in *; clear - Hle Hrc1 Hcb1 Hrc2 Hcb2 Hrc3 Hcb3 Hrc4 Hcb4; lia).
destruct Hpn as [[Hn0 _] | [Hnpos Hpin]]; [exfalso; clear - Hn0 Hle Hrc1 Hcb1 Hrc2 Hcb2 Hrc3 Hcb3 Hrc4 Hcb4; unfold rboxed in *; lia|].
assert (Hrq : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0) as [He|Hne]; [exfalso; clear - Hnpos He; lia | reflexivity]).
assert (Hpin3 : In (p, n) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hpin).
pose proof HJcall as HJc. rewrite FP0 in HJc.
destruct (PB_at_now B _ (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) _ _ _ _ _ _ _ (12 + i) LAWS HAR HJc Hpin Hpin3 Hrq ltac:(cbn [c_n]; unfold rboxed in *; clear - Hi Hle Hrc1 Hcb1 Hrc2 Hcb2 Hrc3 Hcb3 Hrc4 Hcb4; lia)) as (b & HPB & HA).
exists b. split; [exact HPB|]. rewrite (Hcp i Hi). cbn [c_p] in HA. rewrite Hpv. replace (p + 12 + i) with (p + (12 + i)) by (clear; lia). exact HA. }
clear Hr5 HJcall.
vkeep Vz32 (w_H W3) mem5 ltac:(apply Hfr5; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
vkeep Vz40 (w_H W3) mem5 ltac:(apply Hfr5; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
vkeep Vz62 (w_H W3) mem5 ltac:(apply Hfr5; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
vkeep Vz64 (w_H W3) mem5 ltac:(apply Hfr5; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
vkeep Vz72 (w_H W3) mem5 ltac:(apply Hfr5; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
rdkeep RD1 (w_H W3) mem5 ltac:(apply Hfr5; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
rdkeep RD2 (w_H W3) mem5 ltac:(apply Hfr5; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
rdkeep RD3 (w_H W3) mem5 ltac:(apply Hfr5; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
rdkeep RD4 (w_H W3) mem5 ltac:(apply Hfr5; clear - Hi HF4096 HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia).
clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ7 Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ8 Kgot4 Kcell4 Kguar4 Kuar4.
reseatL HS HJ8 HP5 [0; 1; 2; 3; 4; 5; 6; 7]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot4 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell4 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar4 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar4 | clear; lia] ] end
| eapply region_kept_aview;
[ evalE AG
| intros a Ha; apply Hfr5; clear - Ha HF4096 HFceil HFhigh HFhigh_img Hceil Hslo Hshi H47 Hstk0 Hsp1 HF8lo HF8hi FFS C1 C2 C3; unfold ESTACK, SB in *; zone_lia
| exact Hpres5 ]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
clear Kgot4 Kcell4 Kguar4 Kuar4 Hpres5.
rebv HS E70 RF B70 B75.
rreg HS (10%bv : bv 5) Rr5. cbn [ms_regs] in Rr5. rewrite Ha05 in Rr5. symmetry in Rr5. unfold w64 in Rr5. clear Ha05.
assert (Hrr5 : 0 <= r5 < 2 ^ 64) by (clear - Hrc5; unfold rboxed in Hrc5; lia).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ8) Hfin3) as (_ & _ & HFpres8 & _). change (fs_frame_bytes 2) with 256 in HFpres8. rewrite !EFA3 in HFpres8. fold F in HFpres8.
set (b := fun j : Z => abyte (w_H W3) mem5 (F + 48 + j)).
assert (Hb : forall j, 0 <= b j < 256) by (intros j; subst b; apply abyte_range).
assert (Vb : forall j, 0 <= j < 14 -> val_mem tfibsegs (mrestrict (w_H W3) mem5) (F + 48 + j) 1 (b j)).
{ intros j Hj. subst b. apply abyte_val. apply (proj1 (HFpres8 (F + 48 + j) ltac:(clear - Hj; lia))). }
set (attr := (b 0 + 256 * b 1) + 65536 * (b 2 + 256 * b 3)).
set (gen := (b 4 + 256 * b 5) + 65536 * (b 6 + 256 * b 7)).
set (w16 := b 8 + 256 * b 9). set (h16 := b 10 + 256 * b 11). set (ngp := b 12 + 256 * b 13).
pose proof (Hb 0) as Hb0. pose proof (Hb 1) as Hb1. pose proof (Hb 2) as Hb2. pose proof (Hb 3) as Hb3. pose proof (Hb 4) as Hb4. pose proof (Hb 5) as Hb5.
pose proof (Hb 6) as Hb6. pose proof (Hb 7) as Hb7. pose proof (Hb 8) as Hb8. pose proof (Hb 9) as Hb9. pose proof (Hb 10) as Hb10. pose proof (Hb 11) as Hb11.
pose proof (Hb 12) as Hb12. pose proof (Hb 13) as Hb13.
assert (Rattr : 0 <= attr < 2 ^ 32) by (subst attr; clear - Hb0 Hb1 Hb2 Hb3; lia).
assert (Rgen : 0 <= gen < 2 ^ 32) by (subst gen; clear - Hb4 Hb5 Hb6 Hb7; lia).
assert (Rw16 : 0 <= w16 < 65536) by (subst w16; clear - Hb8 Hb9; lia).
assert (Rh16 : 0 <= h16 < 65536) by (subst h16; clear - Hb10 Hb11; lia).
assert (Rngp : 0 <= ngp < 65536) by (subst ngp; clear - Hb12 Hb13; lia).
assert (Vattr : val_mem tfibsegs (mrestrict (w_H W3) mem5) (F + 48) 4 attr).
{ subst attr. apply val_mem_half2; [| | clear - Hb0 Hb1; lia | clear - Hb2 Hb3; lia].
- replace (F + 48) with (F + 48 + 0) by lia. apply val_mem_bytes2; [exact (Vb 0 ltac:(lia)) | replace (F + 48 + 0 + 1) with (F + 48 + 1) by lia; exact (Vb 1 ltac:(lia)) | exact Hb0 | exact Hb1].
- replace (F + 48 + 2) with (F + 48 + 2) by lia. apply val_mem_bytes2; [exact (Vb 2 ltac:(lia)) | replace (F + 48 + 2 + 1) with (F + 48 + 3) by lia; exact (Vb 3 ltac:(lia)) | exact Hb2 | exact Hb3]. }
assert (Vgen : val_mem tfibsegs (mrestrict (w_H W3) mem5) (F + 52) 4 gen).
{ subst gen. apply val_mem_half2; [| | clear - Hb4 Hb5; lia | clear - Hb6 Hb7; lia].
- replace (F + 52) with (F + 48 + 4) by lia. apply val_mem_bytes2; [exact (Vb 4 ltac:(lia)) | replace (F + 48 + 4 + 1) with (F + 48 + 5) by lia; exact (Vb 5 ltac:(lia)) | exact Hb4 | exact Hb5].
- replace (F + 52 + 2) with (F + 48 + 6) by lia. apply val_mem_bytes2; [exact (Vb 6 ltac:(lia)) | replace (F + 48 + 6 + 1) with (F + 48 + 7) by lia; exact (Vb 7 ltac:(lia)) | exact Hb6 | exact Hb7]. }
assert (Vw16 : val_mem tfibsegs (mrestrict (w_H W3) mem5) (F + 56) 2 w16).
{ subst w16. replace (F + 56) with (F + 48 + 8) by lia. apply val_mem_bytes2; [exact (Vb 8 ltac:(lia)) | replace (F + 48 + 8 + 1) with (F + 48 + 9) by lia; exact (Vb 9 ltac:(lia)) | exact Hb8 | exact Hb9]. }
assert (Vh16 : val_mem tfibsegs (mrestrict (w_H W3) mem5) (F + 58) 2 h16).
{ subst h16. replace (F + 58) with (F + 48 + 10) by lia. apply val_mem_bytes2; [exact (Vb 10 ltac:(lia)) | replace (F + 48 + 10 + 1) with (F + 48 + 11) by lia; exact (Vb 11 ltac:(lia)) | exact Hb10 | exact Hb11]. }
assert (Vngp : val_mem tfibsegs (mrestrict (w_H W3) mem5) (F + 60) 2 ngp).
{ subst ngp. replace (F + 60) with (F + 48 + 12) by lia. apply val_mem_bytes2; [exact (Vb 12 ltac:(lia)) | replace (F + 48 + 12 + 1) with (F + 48 + 13) by lia; exact (Vb 13 ltac:(lia)) | exact Hb12 | exact Hb13]. }
assert (HPROV : r1 = 0 -> r2 = 0 -> r3 = 0 -> r4 = 0 -> r5 = 0 -> hdr_prov (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) attr gen w16 h16 ngp).
{ intros Z1 Z2 Z3 Z4 Z5.
destruct (RD1 Z1 0 ltac:(clear; lia)) as (q0 & P0 & A0). destruct (RD1 Z1 1 ltac:(clear; lia)) as (q1 & P1 & A1).
destruct (RD2 Z2 0 ltac:(clear; lia)) as (q2 & P2 & A2). destruct (RD2 Z2 1 ltac:(clear; lia)) as (q3 & P3 & A3).
destruct (RD3 Z3 0 ltac:(clear; lia)) as (q4 & P4 & A4). destruct (RD3 Z3 1 ltac:(clear; lia)) as (q5 & P5 & A5).
destruct (RD3 Z3 2 ltac:(clear; lia)) as (q6 & P6 & A6). destruct (RD3 Z3 3 ltac:(clear; lia)) as (q7 & P7 & A7).
destruct (RD4 Z4 0 ltac:(clear; lia)) as (q8 & P8 & A8). destruct (RD4 Z4 1 ltac:(clear; lia)) as (q9 & P9 & A9).
destruct (RD4 Z4 2 ltac:(clear; lia)) as (q10 & P10 & A10). destruct (RD4 Z4 3 ltac:(clear; lia)) as (q11 & P11 & A11).
destruct (RD5 Z5 0 ltac:(clear; lia)) as (q12 & P12 & A12). destruct (RD5 Z5 1 ltac:(clear; lia)) as (q13 & P13 & A13).
change (PB (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) 0 q0) in P0. change (PB (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) 1 q1) in P1. change (PB (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) 2 q2) in P2. change (PB (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) 3 q3) in P3.
change (PB (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) 4 q4) in P4. change (PB (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) 5 q5) in P5. change (PB (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) 6 q6) in P6. change (PB (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) 7 q7) in P7.
change (PB (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) 8 q8) in P8. change (PB (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) 9 q9) in P9. change (PB (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) 10 q10) in P10. change (PB (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) 11 q11) in P11.
change (PB (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) 12 q12) in P12. change (PB (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) 13 q13) in P13.
unfold hdr_prov. exists q0, q1, q2, q3, q4, q5, q6, q7. exists q8, q9, q10, q11, q12, q13.
repeat match goal with |- _ /\ _ => split end; try assumption.
- subst w16. subst b. unfold abyte. replace (F + 48 + 8) with (F + 56 + 0) by (clear; lia). replace (F + 48 + 9) with (F + 56 + 1) by (clear; lia).
rewrite A0, A1. reflexivity.
- subst h16. subst b. unfold abyte. replace (F + 48 + 10) with (F + 58 + 0) by (clear; lia). replace (F + 48 + 11) with (F + 58 + 1) by (clear; lia).
rewrite A2, A3. reflexivity.
- rewrite Z.mod_small by (clear - Rattr; lia). subst attr. subst b. unfold abyte. rewrite A4, A5, A6, A7. clear; lia.
- rewrite Z.mod_small by (clear - Rgen; lia). subst gen. subst b. unfold abyte.
replace (F + 48 + 4) with (F + 52 + 0) by (clear; lia). replace (F + 48 + 5) with (F + 52 + 1) by (clear; lia).
replace (F + 48 + 6) with (F + 52 + 2) by (clear; lia). replace (F + 48 + 7) with (F + 52 + 3) by (clear; lia).
rewrite A8, A9, A10, A11. clear; lia.
- subst ngp. subst b. unfold abyte. replace (F + 48 + 12) with (F + 60 + 0) by (clear; lia). replace (F + 48 + 13) with (F + 60 + 1) by (clear; lia).
rewrite A12, A13. reflexivity. }
clear RD1 RD2 RD3 RD4 RD5.
clearbody attr gen w16 h16 ngp. clear Vb Hb Hb0 Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11 Hb12 Hb13 b.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
let K := eval vm_compute in (run_K 0 (SOff 32 0) [] ssv) in
let HS3 := fresh "HS3" in
let WS := constr:([Z_to_bv 64 attr; Z_to_bv 64 gen; Z_to_bv 64 w16; Z_to_bv 64 h16; Z_to_bv 64 ngp] : list word) in
pose proof (st_ok_havoc_win tfibsegs K Ev ssv msv WS HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
assert (Eattr : ew (havoc Ev K WS) K = Z_to_bv 64 attr) by (exact (ew_havoc_new Ev K WS 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (Egen : ew (havoc Ev K WS) (K + 1) = Z_to_bv 64 gen) by (exact (ew_havoc_new Ev K WS 1 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (Ew16 : ew (havoc Ev K WS) (K + 2) = Z_to_bv 64 w16) by (exact (ew_havoc_new Ev K WS 2 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (Eh16 : ew (havoc Ev K WS) (K + 3) = Z_to_bv 64 h16) by (exact (ew_havoc_new Ev K WS 3 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (Engp : ew (havoc Ev K WS) (K + 4) = Z_to_bv 64 ngp) by (exact (ew_havoc_new Ev K WS 4 (Z_to_bv 64 0) ltac:(cbn; lia)));
cbn [Nat.add] in Egen, Ew16, Eh16, Engp;
let HS4 := fresh "HS4" in
pose proof (ast_ok_add_region tfibsegs _ _ _
(YP09.mkRegion (Some 75%nat) 32 80 0 0
[YP09.mkChunk 32 (CVal 8 (SLit 0)); YP09.mkChunk 40 (CVal 8 (SLit 0)); YP09.mkChunk 48 (CVal 4 (SOff K 0)); YP09.mkChunk 52 (CVal 4 (SOff (K + 1) 0));
YP09.mkChunk 56 (CVal 2 (SOff (K + 2) 0)); YP09.mkChunk 58 (CVal 2 (SOff (K + 3) 0)); YP09.mkChunk 60 (CVal 2 (SOff (K + 4) 0)); YP09.mkChunk 62 (CVal 2 (SLit 0));
YP09.mkChunk 64 (CVal 8 (SLit 0)); YP09.mkChunk 72 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [Nat.add YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite ?ew_havoc_old by (clear; cbn; lia); rewrite RF, unsigned_lit_small by (clear - HF4096 HFceil C1; lia);
split; [clear - HF4096 HFceil C1; lia|]; split; [clear - HF4096 HFceil C1; lia|]; split;
[ intros q Hq; exfalso; clear - Hq; lia
| apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]]]]]]];
[ apply (chunk_ok_val tfibsegs _ _ F 32 8 _ 0); [reflexivity | zside | zside | exact Vz32]
| apply (chunk_ok_val tfibsegs _ _ F 40 8 _ 0); [reflexivity | zside | zside | exact Vz40]
| apply (chunk_ok_val tfibsegs _ _ F 48 4 _ attr); [cbn [sv_denot]; rewrite Eattr, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vattr]
| apply (chunk_ok_val tfibsegs _ _ F 52 4 _ gen); [cbn [sv_denot]; rewrite Egen, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vgen]
| apply (chunk_ok_val tfibsegs _ _ F 56 2 _ w16); [cbn [sv_denot]; rewrite Ew16, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vw16]
| apply (chunk_ok_val tfibsegs _ _ F 58 2 _ h16); [cbn [sv_denot]; rewrite Eh16, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vh16]
| apply (chunk_ok_val tfibsegs _ _ F 60 2 _ ngp); [cbn [sv_denot]; rewrite Engp, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vngp]
| apply (chunk_ok_val tfibsegs _ _ F 62 2 _ 0); [reflexivity | zside | zside | exact Vz62]
| apply (chunk_ok_val tfibsegs _ _ F 64 8 _ 0); [reflexivity | zside | zside | exact Vz64]
| apply (chunk_ok_val tfibsegs _ _ F 72 8 _ 0); [reflexivity | zside | zside | exact Vz72] ] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite ?ew_havoc_old by (clear; cbn; lia); rewrite RF, E88, (AG 2%nat) by lia; rewrite Usp;
rewrite !unsigned_lit_small by (clear - HF4096 HFceil HF8lo HF8hi C1; unfold SB; lia);
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, SB;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi HFq HF8 HF8c; repeat split; first [zone_lia | match goal with |- ?g => idtac "DISJ" g; fail end])) as HS4;
clear HS; rename HS4 into HS; norm_ss HS end.
clear Vattr Vgen Vw16 Vh16 Vngp Vz32 Vz40 Vz62 Vz64 Vz72 HFpres8.
lazymatch type of HS with st_ok _ ?Ev _ ?msv =>
let K := lazymatch type of Eattr with ew _ ?K = _ => K end in
let HS3 := fresh "HS3" in
pose proof (st_ok_add_fact tfibsegs Ev _ msv K (mkAF 0 (2 ^ 32 - 1) 0)
(st_ok_add_fact tfibsegs Ev _ msv (K + 1)%nat (mkAF 0 (2 ^ 32 - 1) 0)
(st_ok_add_fact tfibsegs Ev _ msv (K + 2)%nat (mkAF 0 65535 0)
(st_ok_add_fact tfibsegs Ev _ msv (K + 3)%nat (mkAF 0 65535 0)
(st_ok_add_fact tfibsegs Ev _ msv (K + 4)%nat (mkAF 0 65535 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2 Nat.add]; rewrite Engp, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; clear - Rngp; lia))
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2 Nat.add]; rewrite Eh16, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; clear - Rh16; lia))
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2 Nat.add]; rewrite Ew16, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; clear - Rw16; lia))
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2 Nat.add]; rewrite Egen, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; clear - Rgen; lia))
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2 Nat.add]; rewrite Eattr, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; clear - Rattr; lia)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
reshok HS.
aj_run_tok tfibtbl_lib_ok HS HJ8 SHOK RTBspan.
{ awrRT AG fpos F EFA3. }
unrunRD HFr Zsm Usp B70 Hsp1 UNt. clear HF HFr HG.
vkeepUN UNt Vp Vn Vc ltac:(first [clear - Hi Hsp1 HSPB C1 FFS; lia | subst Zsm; cbn beta; clear - Hi Hsp1 HFceil Hceil Hslo FFS C1; lia]). clear UNt.
srr_branch_tok tfibtbl_lib_ok HS SHOK RTBspan.
all: cbn [negb] in Hc.
all: pose proof (Z_lor_bound r2 r1 64 ltac:(clear; lia) Hrr2 Hrr1) as Hl21; pose proof (Z_lor_bound r3 r4 64 ltac:(clear; lia) Hrr3 Hrr4) as Hl34;
pose proof (Z_lor_bound _ _ 64 ltac:(clear; lia) Hl21 Hl34) as Hl4; pose proof (Z_lor_bound _ r5 64 ltac:(clear; lia) Hl4 Hrr5) as Hl5;
set (racc := Z.lor (Z.lor (Z.lor r2 r1) (Z.lor r3 r4)) r5) in Hl5.
all: assert (Hracc14 : racc = 0 -> 14 <= n)
by (intros Hz; subst racc; apply Z.lor_eq_0_iff in Hz; destruct Hz as [Hz Hz5]; apply Z.lor_eq_0_iff in Hz; destruct Hz as [Hz21 Hz34];
apply Z.lor_eq_0_iff in Hz21; apply Z.lor_eq_0_iff in Hz34; unfold rboxed in *; clear - Hz21 Hz34 Hz5 Hrc1 Hrc2 Hrc3 Hrc4 Hrc5 Hcb5; lia).
all: assert (Hcur14' : racc = 0 -> cur5 = 14)
by (intros Hz; subst racc; apply Z.lor_eq_0_iff in Hz; destruct Hz as [Hz Hz5]; apply Z.lor_eq_0_iff in Hz; destruct Hz as [Hz21 Hz34];
apply Z.lor_eq_0_iff in Hz21; apply Z.lor_eq_0_iff in Hz34; unfold rboxed in *; clear - Hz21 Hz34 Hz5 Hrc1 Hrc2 Hrc3 Hrc4 Hrc5 Hcb5; lia).
all: assert (Hprov' : racc = 0 -> hdr_prov (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) attr gen w16 h16 ngp)
by (intros Hz; subst racc; apply Z.lor_eq_0_iff in Hz; destruct Hz as [Hz Hz5]; apply Z.lor_eq_0_iff in Hz; destruct Hz as [Hz21 Hz34];
apply Z.lor_eq_0_iff in Hz21; apply Z.lor_eq_0_iff in Hz34; destruct Hz21 as [Z2 Z1]; destruct Hz34 as [Z3 Z4]; exact (HPROV Z1 Z2 Z3 Z4 Hz5)).
all: assert (Hwhy' : racc <> 0 -> n < 14 \/ (Z.land attr 4 = 0 /\ hdr_prov (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) attr gen w16 h16 ngp /\ n < 14 + 3 * ngp))
by (intros Hz; left; unfold rboxed in *;
assert (Hnz : ~ (r1 = 0 /\ r2 = 0 /\ r3 = 0 /\ r4 = 0 /\ r5 = 0)) by (intros (Z1 & Z2 & Z3 & Z4 & Z5); apply Hz; subst racc; rewrite Z1, Z2, Z3, Z4, Z5; reflexivity);
clear - Hnz Hrc1 Hrc2 Hrc3 Hrc4 Hrc5 Hcb1 Hcb2 Hcb3 Hcb4 Hcb5; lia).
all: lazymatch type of Hc with _ = ?bb =>
assert (Hbit : (Z.land attr 4 =? 0) = negb bb);
[ rewrite branch_ne_U, U_and_lit, attr_test, U_lit in Hc by (clear; lia);
lazymatch type of Eattr with ew _ ?na = _ =>
rewrite (sv_denot_SOff0 _ na) in Hc; rewrite ?ew_ewset_other, ?ew_havoc_old in Hc by nat_side; rewrite Eattr, unsigned_lit_small in Hc by (clear - Rattr; lia) end;
clear - Hc; destruct (Z.land attr 4 =? 0); cbn in Hc |- *; congruence
| cbn [negb] in Hbit; clear Hc ] end.
-
apply Z.eqb_neq in Hbit.
norm_ss HS. reshok HS.
aj_run_to_tok tfibtbl_lib_ok HS HJ8 SHOK RTBspan 0x80700.
{ awrRT AG fpos F EFA3. }
unrunRD HFr Zsm Usp B70 Hsp1 UNd. clear HF HFr HG.
vkeepUN UNd Vp Vn Vc ltac:(first [clear - Hi Hsp1 HSPB C1 FFS; lia | subst Zsm; cbn beta; clear - Hi Hsp1 HFceil Hceil Hslo FFS C1; lia]). clear UNd.
rreg HS (23%bv : bv 5) R23.
add_atom_win HS 191%nat (Z_to_bv 64 0) E191. add_atom_win HS 192%nat (Z_to_bv 64 racc) E192.
ws_pin HS (23%bv : bv 5) (SOff 192 0) R23
ltac:(rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E192; symmetry; ewpeel; rewrite Rr1, Rr2, Rr3, Rr4, Rr5;
rewrite (alu_or_lits r2 r1 Hrr2 Hrr1), (alu_or_lits r3 r4 Hrr3 Hrr4), (alu_or_lits _ _ Hl21 Hl34), (alu_or_lits _ _ Hl4 Hrr5); reflexivity).
rechunk_at HS 75%nat 32 (SOff 191 0) ltac:(rewrite sv_denot_SOff0; ewpeel; rewrite E191; reflexivity).
ra_join_win HS ss_D 400%nat rt_C_deads_bv ltac:(idtac).
rebaseE HS AG HEv. clear HEv. rt_hand RD HS.
split; [clear - Hk0; lia|]. split; [macc|].
exists attr, gen, w16, h16, ngp, cur5, racc, 0.
split; [| split; [ewpeel; exact E191 | split; [clear; lia | left; split; [exact Hbit | split; [reflexivity | split; [cbn [c_ly c_S]; exact Eab3 | exact Hcur14']]]]]].
unfold rt_gc; cbn [c_n c_sp1 c_p]. ewpeel.
repeat match goal with |- _ /\ _ => split end;
first [ exact Eattr | exact Egen | exact Ew16 | exact Eh16 | exact Engp | exact E192 | exact Vp | exact Vn | exact Vc | exact Hracc14 | exact Hprov' | exact Hwhy'
| clear - Rattr Rgen Rw16 Rh16 Rngp Hcb5 Hl5; lia ].
-
apply Z.eqb_eq in Hbit.
norm_ss HS. reshok HS.
aj_run_to_tok tfibtbl_lib_ok HS HJ8 SHOK RTBspan 0x806cc.
{ awrRT AG fpos F EFA3. }
unrunRD HFr Zsm Usp B70 Hsp1 UNc. clear HF HFr HG.
vkeepUN UNc Vp Vn Vc ltac:(first [clear - Hi Hsp1 HSPB C1 FFS; lia | subst Zsm; cbn beta; clear - Hi Hsp1 HFceil Hceil Hslo FFS C1; lia]). clear UNc.
rreg HS (23%bv : bv 5) R23.
add_atom_win HS 190%nat (Z_to_bv 64 racc) E190.
ws_pin HS (23%bv : bv 5) (SOff 190 0) R23
ltac:(rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E190; symmetry; ewpeel; rewrite Rr1, Rr2, Rr3, Rr4, Rr5;
rewrite (alu_or_lits r2 r1 Hrr2 Hrr1), (alu_or_lits r3 r4 Hrr3 Hrr4), (alu_or_lits _ _ Hl21 Hl34), (alu_or_lits _ _ Hl4 Hrr5); reflexivity).
ra_join_win HS ss_C 400%nat rt_C0_deads_bv ltac:(idtac).
rebaseE HS AG HEv. clear HEv. rt_hand RC HS.
split; [exact Hk0|]. split; [macc|]. split; [cbn [c_ly c_S]; exact Eab3|].
exists attr, gen, w16, h16, ngp, cur5, racc.
split; [| split; [exact Hbit | exact Hcur14']].
unfold rt_gc; cbn [c_n c_sp1 c_p]. ewpeel.
repeat match goal with |- _ /\ _ => split end;
first [ exact Eattr | exact Egen | exact Ew16 | exact Eh16 | exact Engp | exact E190 | exact Vp | exact Vn | exact Vc | exact Hracc14 | exact Hprov' | exact Hwhy'
| clear - Rattr Rgen Rw16 Rh16 Rngp Hcb5 Hl5; lia ].
Qed.
Lemma rt_B : rt_from B MT FP POST ss_C (INV_C B MT) -> rt_from B MT FP POST ss_D (INV_D B MT FP) -> rt_from B MT FP POST ss_B (INV_0 B MT 0).
Proof. exact rt_B_aux. Qed.
End e.
End c.
