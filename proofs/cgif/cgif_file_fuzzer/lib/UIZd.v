(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import Utf8.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 YI06 UI5b YI09 YI08 YI0r UI1w UN3b UN3c UI55.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI00 UI5c YI0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI01 YI6c YI67 UN0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI02 YI03 YI0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0e YO03
YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI3w UIZe UIZc.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI4l YI5a UI2v UI5d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section zc.
Lemma byte_zext16 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 65536 ->
bv_unsigned (sv_denot E (SExt false 16 (SOff n 0))) mod 256 = v mod 256.
Proof using.
intros E n v Hn Hv. change (U E (SExt false 16 (SOff n 0)) mod 256 = v mod 256).
rewrite U_SExt. cbv beta iota. rewrite mod256_zcanon. change (2 ^ Z.of_N 16) with (2 ^ 16). rewrite mod256_mod_pow2 by lia.
rewrite (U_atom E n v Hn) by lia. reflexivity.
Qed.
Lemma byte_zext16_hi : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 65536 ->
bv_unsigned (sv_denot E (SAlu ALU_SRL (SExt false 16 (SOff n 0)) (SLit 8))) mod 256 = (v / 256) mod 256.
Proof using.
intros E n v Hn Hv. change (U E (SAlu ALU_SRL (SExt false 16 (SOff n 0)) (SLit 8)) mod 256 = (v / 256) mod 256).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (Z.land (zcanon 8) 63) with 8. rewrite mod256_zcanon, Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
rewrite U_SExt. cbv beta iota. rewrite (U_atom E n v Hn) by lia. change (2 ^ Z.of_N 16) with 65536. rewrite (Z.mod_small v 65536) by lia.
rewrite zcanon_id by (unfold M64; lia). reflexivity.
Qed.
End zc.
Section zo. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma rcfg_obj_of_chunks : forall E mem a g pgct rattr W H sgct loops,
Forall (chunk_ok ubs0segs E mem a) (obj_chunks_gen LAY_RawConfig 32 lits_RawConfig) ->
(forall j v, nth_error [ubs0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops] j = Some v -> ew E (32 + j) = Z_to_bv 64 v) ->
(forall j v, nth_error [ubs0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops] j = Some v ->
0 <= v < 2 ^ (8 * Z.of_N (snd (nth j LAY_RawConfig (0, 8%N))))) ->
obj_at ubs0segs mem a LAY_RawConfig [ubs0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops].
Proof using.
intros E mem a g pgct rattr W H sgct loops Hcs HX HR.
eapply (obj_at_of_chunks_gen ubs0segs E mem a LAY_RawConfig [ubs0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops] 32 lits_RawConfig Hcs eq_refl eq_refl).
intros j v Hj. split; [exact (HR j v Hj)|].
pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Hl. cbn [length] in Hl.
destruct j as [|j]; [cbn in Hj |- *; injection Hj as <-; reflexivity|].
replace (nth_error lits_RawConfig (Datatypes.S j)) with (Some (@None Z)) by (do 7 (destruct j as [|j]; [reflexivity|]); lia).
hnf. apply (HX (Datatypes.S j) v Hj).
Qed.
End zo.
Ltac rbyte_hyp n H36 H37 H39 := lazymatch n with 36%nat => H36 | 37%nat => H37 | 39%nat => H39 end.
Ltac rbyte_tac H36 H37 H39 HWr HHr HLr :=
idtac;
lazymatch goal with
| |- (bv_unsigned (sv_denot _ (SLit ?v)) mod 256 = _)%Z => let b := eval vm_compute in (bv_unsigned (Z_to_bv 64 v) mod 256)%Z in exact (eq_refl b)
| |- (bv_unsigned (sv_denot _ (SExt true 16 (SOff ?n 0))) mod 256 = _)%Z =>
let h := rbyte_hyp n H36 H37 H39 in let r := rbyte_hyp n HWr HHr HLr in exact (byte_sext16 _ _ _ h r)
| |- (bv_unsigned (sv_denot _ (SAlu ALU_SRL (SExt true 16 (SOff ?n 0)) (SLit 8))) mod 256 = _)%Z =>
let h := rbyte_hyp n H36 H37 H39 in let r := rbyte_hyp n HWr HHr HLr in exact (byte_sext16_hi _ _ _ h r)
| |- (bv_unsigned (sv_denot _ (SExt false 16 (SOff ?n 0))) mod 256 = _)%Z =>
let h := rbyte_hyp n H36 H37 H39 in let r := rbyte_hyp n HWr HHr HLr in exact (byte_zext16 _ _ _ h r)
| |- (bv_unsigned (sv_denot _ (SAlu ALU_SRL (SExt false 16 (SOff ?n 0)) (SLit 8))) mod 256 = _)%Z =>
let h := rbyte_hyp n H36 H37 H39 in let r := rbyte_hyp n HWr HHr HLr in exact (byte_zext16_hi _ _ _ h r)
| |- (bv_unsigned (sv_denot _ (SOff ?n 0)) mod 256 = _)%Z =>
let h := rbyte_hyp n H36 H37 H39 in let r := rbyte_hyp n HWr HHr HLr in exact (byte_atom16 _ _ _ h r)
| |- (bv_unsigned (sv_denot _ (SAlu ALU_SRL (SOff ?n 0) (SLit 8))) mod 256 = _)%Z =>
let h := rbyte_hyp n H36 H37 H39 in let r := rbyte_hyp n HWr HHr HLr in exact (byte_atom16_hi _ _ _ h r)
end.
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis FWRITE : fwrite_spec ubs0_msyms MR ubs0_A_fwrite.
Lemma rawnew_x_c0 : rn_case API 0 0.
Proof using FWRITE IMG.
intros L A regs mem md cfgp g pgct rattr W H sgct loops gvals f pga Npg S GCT bq HPRE Hid Ha0 Hcal Hclo Hchi cvals Hcfg Hcrd Hobj Hwfn Hfile Hgin Hfin HSK Hroom Hsp47 Hpal HRq HRM HH Hra Hal16 Hstk0 Hceil H63 Hstw Htp Herr Hac HSTKv HASv HGSv HRSv HDv HFv Hg0 Hg1 Hg16 HFBv HWSv Hf0 Hf1 Hf16 Hsg_r Hat_r Hlp_r E HE HX HY HE2 HE10 HE33 HE38 HE35 HE39 Hspw Hsg L2 A2 regs2 md2 res Hid2 Hres10 Hnz Hres16 b1 b2 Hbl2 Hblc Hwr HRq2 Hfin2 Hq10 HE2' Hbin2 Hb0 Hb1 Hwr' Hgc regs3 Hd10 Hrf Henvblk WR Hranges Hoff Hgf Hgin2 Hgranges Hglen HE36 HE37 HWr HHr HLr HAr regs4 ms2 HJ3 HSKc HS Hk.
Ltac finish_ok HS HJ Hq10 HE Hra Hranges HX :=
lazymatch type of Hq10 with ew _ 61 = Z_to_bv 64 ?res =>
lazymatch type of HE with (forall n r, _ -> ew ?E n = getr ?regs r) =>
let HPR := fresh "HPR" in let Hr10 := fresh "Hr10" in let Hr1 := fresh "Hr1" in
pose proof (regs_preserved_of_st_ok _ _ _ _ regs _ HS ltac:(agree_tac) ltac:(vm_compute; reflexivity)) as HPR;
(jreg HS (10%bv:reg) as Hr10); ew_strip_in Hr10; rewrite Hq10 in Hr10;
(jreg HS (1%bv:reg) as Hr1); ew_strip_in Hr1; rewrite (HE 1%nat 1%bv eq_refl) in Hr1;
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |];
[ exact (proj1 (heap_model _ _ (aa_laws _) _ _ _ _ (proj1 HJ)))
| exact (proj1 (proj2 (heap_model _ _ (aa_laws _) _ _ _ _ (proj1 HJ))))
| lazymatch type of HS with st_ok _ ?Ef ?ssf ?msx =>
lazymatch type of HJ with journal _ _ _ _ _ _ _ _ _ ?L2 ?A2 _ ?md2 =>
exists L2, A2, (ms_regs msx), (ms_mem msx), md2, res end;
cbn [ms_regs ms_mem mkst]; rewrite Hr1, Hra; split; [reflexivity|]; split; [exact HJ|]; split; [exact HPR|];
split; [assumption|]; split; [exact Hr10|]; right; split; [assumption|]; split; [assumption|]; split; [do 2 eexists; split; eassumption|];
let Hm := fresh "Hm" in let Hcs := fresh "Hcs" in
pose proof (st_ok_mem_ok _ _ _ _ HS) as Hm; destruct Hm as (_ & Hm & _); apply Forall_inv in Hm;
unfold region_ok in Hm; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in Hm; destruct Hm as (_ & _ & _ & Hcs);
ew_strip_in Hcs; rewrite Hq10, unsigned_lit_small in Hcs by lia;
apply (raw_obj_final Ef _ res); [exact Hcs | | exact Hranges];
let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in let Hlj := fresh "Hlj" in
intros j v Hj; pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Hlj; cbn [length] in Hlj;
rewrite !ew_havoc_old by (first [apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); reflexivity | lia]); apply (HX j v Hj)
end ]
end end.
Ltac sink_step HSK HFx Hoff Hq10 HE2 Hspw :=
cbn [ms_mem mkst] in HFx;
lazymatch type of HFx with frame_of _ _ _ ?m1 =>
lazymatch type of HSK with sink_at _ ?m0 ?mdx ?fx ?Sx =>
let Hn := fresh "HSKn" in
assert (Hn : sink_at ubs0_msyms m1 mdx fx Sx);
[ apply (sink_at_frame ubs0_msyms m0 m1 mdx fx Sx); [|exact HSK];
let a := fresh "a" in let Ha := fresh "Ha" in let Ha' := fresh "Ha'" in
intros a Ha; pose proof (Hoff a Ha) as Ha';
apply (mbyte_eq_of ubs0_msyms); apply HFx; rewrite unsigned_lit_small by lia;
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr); cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [r_base r_wlo r_whi base_val] in Hr; ew_strip_in Hr; rewrite ?Hq10, ?HE2, ?Hspw, ?unsigned_lit_small in Hr by lia; lia |]);
destruct Hin
| clear HSK; rename Hn into HSK ]
end
end.
Ltac sink_now HS HSK Hoff Hq10 HE2 Hspw :=
lazymatch type of HS with st_ok _ _ _ ?msx =>
match goal with HFx : frame_of _ _ _ (ms_mem msx) |- _ => sink_step HSK HFx Hoff Hq10 HE2 Hspw end end.
Ltac cur_fact HS Hbase Hn :=
lazymatch type of HS with st_ok _ ?Ec _ _ =>
lazymatch type of Hbase with ew _ ?n = ?v => assert (Hn : ew Ec n = v) by (ew_strip; exact Hbase) end end.
Ltac raw_byte_tac H36 H37 H39 HWr HHr HLr :=
idtac;
lazymatch goal with
| |- (bv_unsigned (sv_denot _ (SLit ?v)) mod 256 = _)%Z => let b := eval vm_compute in (bv_unsigned (Z_to_bv 64 v) mod 256)%Z in exact (eq_refl b)
| |- (bv_unsigned (sv_denot _ (SExt true 16 (SOff 36 0))) mod 256 = _)%Z => exact (byte_sext16 _ _ _ H36 HWr)
| |- (bv_unsigned (sv_denot _ (SAlu ALU_SRL (SExt true 16 (SOff 36 0)) (SLit 8))) mod 256 = _)%Z => exact (byte_sext16_hi _ _ _ H36 HWr)
| |- (bv_unsigned (sv_denot _ (SExt true 16 (SOff 37 0))) mod 256 = _)%Z => exact (byte_sext16 _ _ _ H37 HHr)
| |- (bv_unsigned (sv_denot _ (SAlu ALU_SRL (SExt true 16 (SOff 37 0)) (SLit 8))) mod 256 = _)%Z => exact (byte_sext16_hi _ _ _ H37 HHr)
| |- (bv_unsigned (sv_denot _ (SExt true 16 (SOff 39 0))) mod 256 = _)%Z => exact (byte_sext16 _ _ _ H39 HLr)
| |- (bv_unsigned (sv_denot _ (SAlu ALU_SRL (SExt true 16 (SOff 39 0)) (SLit 8))) mod 256 = _)%Z => exact (byte_sext16_hi _ _ _ H39 HLr)
end.
Ltac net_fact HS HE35 Hc rattr HNET b :=
let H35 := fresh "HE35c" in cur_fact HS HE35 H35;
rewrite branch_ne_U, U_and_lit, (U_atom _ 35 rattr H35), U_lit in Hc by lia;
assert (HNET : has_net rattr = b) by (rewrite has_net_land; destruct (Z.land rattr 3 =? 1); cbn in Hc; first [reflexivity | discriminate Hc]);
clear Hc H35.
Ltac sink_lists_eq :=
repeat match goal with b := _ : list Z |- _ => subst b end;
unfold hdr13, net19; rewrite ?app_nil_r; repeat rewrite <- app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity.
Ltac sink_eq0 HNET Hs0 :=
idtac; rewrite raw_header_eq, HNET, Hs0; cbn [Z.eqb]; sink_lists_eq.
Ltac sink_eqK k K2 HNET :=
idtac; rewrite (raw_header_class k K2) by first [reflexivity | lia | (cbn; lia)]; rewrite HNET;
try (match goal with |- context [repeat 0 (Z.to_nat ?e)] => replace (Z.to_nat e) with 0%nat by lia; cbn [repeat] end);
(let v := eval vm_compute in (128 + (Z.max 1 k - 1)) in change (128 + (Z.max 1 k - 1)) with v);
sink_lists_eq.
Ltac finish_okS HS HJ Hq10 HE Hra Hranges HX HSKc EQ HRQ :=
lazymatch type of Hq10 with ew _ 61 = Z_to_bv 64 ?res =>
lazymatch type of HE with (forall n r, _ -> ew ?E n = getr ?regs r) =>
let HPR := fresh "HPR" in let Hr10 := fresh "Hr10" in let Hr1 := fresh "Hr1" in
pose proof (regs_preserved_of_st_ok _ _ _ _ regs _ HS ltac:(agree_tac) ltac:(vm_compute; reflexivity)) as HPR;
(jreg HS (10%bv:reg) as Hr10); ew_strip_in Hr10; rewrite Hq10 in Hr10;
(jreg HS (1%bv:reg) as Hr1); ew_strip_in Hr1; rewrite (HE 1%nat 1%bv eq_refl) in Hr1;
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |];
[ exact (proj1 (heap_model _ _ (aa_laws _) _ _ _ _ (proj1 HJ)))
| exact (proj1 (proj2 (heap_model _ _ (aa_laws _) _ _ _ _ (proj1 HJ))))
| lazymatch type of HS with st_ok _ ?Ef ?ssf ?msx =>
lazymatch type of HJ with journal _ _ _ _ _ _ _ _ _ ?L2 ?A2 _ ?md2 =>
exists L2, A2, (ms_regs msx), (ms_mem msx), md2, res end;
cbn [ms_regs ms_mem mkst]; rewrite Hr1, Hra; split; [reflexivity|]; split; [exact HJ|]; split; [exact HPR|];
split; [assumption|]; split; [exact Hr10|]; right; split; [assumption|]; split; [assumption|];
split; [ lazymatch type of HSKc with sink_at _ _ _ _ ?Sx => lazymatch goal with |- sink_at _ _ _ _ ?Sg => replace Sg with Sx; [exact HSKc | EQ] end end |];
split; [do 2 eexists; split; eassumption|];
split; [|exact HRQ];
let Hm := fresh "Hm" in let Hcs := fresh "Hcs" in
pose proof (st_ok_mem_ok _ _ _ _ HS) as Hm; destruct Hm as (_ & Hm & _); apply Forall_inv in Hm;
unfold region_ok in Hm; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in Hm; destruct Hm as (_ & _ & _ & Hcs);
ew_strip_in Hcs; rewrite Hq10, unsigned_lit_small in Hcs by lia;
apply (raw_obj_final Ef _ res); [exact Hcs | | exact Hranges];
let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in let Hlj := fresh "Hlj" in
intros j v Hj; pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Hlj; cbn [length] in Hlj;
rewrite !ew_havoc_old by (first [apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); reflexivity | lia]); apply (HX j v Hj)
end ]
end end.
jbranch ubs0tbl HS.
2:{ exfalso. cur_fact HS HE38 HE38c. rewrite branch_eq_U, (U_atom _ 38 sgct HE38c), U_lit in Hc by lia.
destruct (Z.eqb_spec sgct 0) as [_ | Hn]; [discriminate Hc | lia]. }
clear Hc. assert (Hs0 : sgct = 0) by lia.
jrun_to LAWS ubs0tbl_ok HS HJ3 ubs0_A_cgif_writecb. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
sink_now HS HSKc Hoff Hq10 HE2 Hspw.
jreg HS (10%bv:reg) as Ha10_h0. jreg HS (11%bv:reg) as Ha11_h0. jreg HS (12%bv:reg) as Ha12_h0.
jreg HS (2%bv:reg) as Ha2_h0. jreg HS (4%bv:reg) as Ha4_h0. jreg HS (1%bv:reg) as Ha1_h0.
rewrite HE33 in Ha10_h0. rewrite HE2, Hspw in Ha11_h0, Ha2_h0. rewrite (HE 4%nat 4%bv eq_refl), Htp in Ha4_h0.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp_h0 : spZ (ms_regs msx) = spZ regs - 112) by (unfold spZ at 1; rewrite Ha2_h0; apply unsigned_lit_small; lia) end.
pose proof HJ3 as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw_h0) & _).
cur_fact HS HE36 HE36c_h0. cur_fact HS HE37 HE37c_h0. cur_fact HS HE39 HE39c_h0.
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let rg := eval vm_compute in (nth 1 (ss_mem ssc) (YP09.mkRegion None 0 0 0 0 [])) in
eassert (HG_h0 : garr8 ubs0segs (ms_mem msc) (spZ regs + -104) _);
[ eapply (garr8_of_chunk_bytesZ ubs0segs Ec (ms_mem msc) rg 2%nat (spZ regs) _ (-104));
[ exact (vst_ok_region_nth ubs0segs Ec ssc msc 1%nat rg HS eq_refl) | reflexivity | ew_strip; rewrite HE2; exact Hspw
| cbn [r_chunks]; chunk_bytesZ_tac 13%nat ltac:(rbyte_tac HE36c_h0 HE37c_h0 HE39c_h0 HWr HHr HLr) ]
| ] end.
lazymatch type of HG_h0 with garr8 _ _ _ ?l => set (bs_h0 := l) in HG_h0 end.
assert (Hbl_h0 : length bs_h0 = 13%nat) by reflexivity.
clear HE36c_h0 HE37c_h0 HE39c_h0.
lazymatch type of HS with st_ok _ ?Ec _ ?msc =>
assert (HobjC_h0 : obj_at ubs0segs (ms_mem msc) g LAY_CGIF gvals);
[ pose proof (st_ok_mem_ok _ _ _ _ HS) as Hm; destruct Hm as (_ & Hm & _);
do 3 (apply Forall_inv_tail in Hm); apply Forall_inv in Hm;
unfold region_ok in Hm; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in Hm; destruct Hm as (_ & _ & _ & Hcs);
ew_strip_in Hcs; rewrite HE33, unsigned_lit_small in Hcs by lia;
apply (cgif_obj_of_chunks Ec _ g gvals Hcs Hglen Hwfn Hfile); [| exact Hgranges];
intros j v Hj; pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Hlj; rewrite Hglen in Hlj;
rewrite !ew_havoc_old by (first [apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); reflexivity | lia]); apply (HY j v Hj)
| ] end.
eapply SR_bind.
{ lazymatch type of HSKc with sink_at _ _ _ _ ?Sx =>
eapply (jwrite ubs0_msyms MR LAWS ubs0_A_cgif_writecb (ubs0_cgif_writecb API IMG FWRITE))
with (g := g) (gvals := gvals) (src := spZ regs + -104) (n := 13) (f := f) (S := Sx) (bs := bs_h0) end;
[ exact HS | reflexivity | reflexivity | exact HJ3 | exact Ha1_h0 | apply ret_ok_even; vm_compute; reflexivity
| exact Ha10_h0 | exact Ha11_h0 | exact Ha12_h0 | rewrite Hsp_h0; rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity | rewrite Hsp_h0; lia | rewrite Hsp_h0; lia | rewrite Hsp_h0; lia
| exact Ha4_h0 | exact HobjC_h0 | exact Hwfn | exact Hfile | exact Hgin2 | exact Hfin2 | exact HSKc | exact HG_h0 | rewrite Hbl_h0; reflexivity
| lia | lia | lia | rewrite Hsp_h0; lia | repeat rewrite length_app; lia | lia | ].
intros a Ha; exact Ha. }
cbv beta. intros c' (regs_h0 & mem_h0 & md_h0 & -> & HJ_h0 & HP_h0 & Hr10_h0 & HSK_h0 & Hhi_h0 & Hblk_h0). rewrite Hsp_h0 in Hhi_h0.
clear HJ3 HSKc. rename HJ_h0 into HJ3. rename HSK_h0 into HSKc.
lazymatch type of HS with st_ok _ ?Ec _ _ => lazymatch Ec with havoc _ ?k0 ?l0 =>
let k := eval vm_compute in (k0 + length l0)%nat in
jafter_call_keep HS k regs_h0 mem_h0 HP_h0 [0%nat; 1%nat; 2%nat; 3%nat] HS2 end end.
match type of HS2 with ?P -> _ => assert (HKP : P); [|specialize (HS2 HKP); clear HKP] end.
{ constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HHw.
split; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; intros a Ha.
+ replace a with (res + (a - res)) by lia. apply (Hblk_h0 res 48 (a - res) Hbin2); [lia|].
replace (res + (a - res)) with a by lia. intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia.
+ intros _. apply (present_writable ubs0_msyms). replace a with (res + (a - res)) by lia.
apply (proj1 (heap_blocks _ _ LAWS L2 A2 _ _ res 48 (a - res) HHw Hbin2 ltac:(lia))).
- eapply (region_kept_stack ubs0segs _ _ _ 2); [ew_strip; rewrite HE2; exact Hspw | exact Hhi_h0 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs0segs _ _ _ 10); [ew_strip; rewrite HE10; apply unsigned_lit_small; lia | exact Hhi_h0 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_pointwise ubs0segs _ _ _ 33 _ _ _ _ _ g); [ew_strip; rewrite HE33; apply unsigned_lit_small; lia | | cbn; lia].
intros a Ha. cbn [r_lo r_hi] in Ha. replace a with (g + (a - g)) by lia. apply (Hblk_h0 g CGIF_SIZE (a - g) Hgin2); [lia|].
replace (g + (a - g)) with a by lia. intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia. }
clear HS. rename HS2 into HS.
pin_reg HS (10%bv:reg) 0 Hr10_h0.
lazymatch type of HS with st_ok _ _ _ ?msx => change mem_h0 with (ms_mem msx) in HJ3 end.
jrun_to LAWS ubs0tbl_ok HS HJ3 PC_NT. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
sink_now HS HSKc Hoff Hq10 HE2 Hspw.
jreg HS (2%bv:reg) as T2. jreg HS (8%bv:reg) as T8. jreg HS (9%bv:reg) as T9. jreg HS (18%bv:reg) as T18.
rewrite HE2, Hspw in T2. ew_strip_in T8. rewrite Hq10 in T8. rewrite HE10 in T9.
assert (T2' : getr (ms_regs ltac:(lazymatch type of HS with st_ok _ _ _ ?msc => exact msc end)) 2 = Z_to_bv 64 (spZ regs - 112))
by (rewrite T2; f_equal; lia).
pose proof (regs_kept_of_st_ok _ _ _ _ regs _ [3%bv; 4%bv; 24%bv; 25%bv; 26%bv; 27%bv] HS ltac:(agree_tac) ltac:(vm_compute; reflexivity)) as TK.
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let rg := eval vm_compute in (nth 1 (ss_mem ssc) (YP09.mkRegion None 0 0 0 0 [])) in
assert (TFS : frame_savedN ubs0_msyms 9 regs (ms_mem msc) (spZ regs));
[ eapply (frame_savedN_of_region ubs0_msyms 9 Ec (ms_mem msc) regs (spZ regs));
  [ exact (vst_ok_region_nth ubs0segs Ec ssc msc 1%nat rg HS eq_refl) | ew_strip; rewrite HE2; exact Hspw | ];
  let r := fresh "r" in let d := fresh "d" in let Hin := fresh "Hin" in
  intros r d Hin; cbv [SAVEDN YI0n.SAVED firstn In] in Hin;
  repeat (destruct Hin as [Hin|Hin];
    [ injection Hin as <- <-; eexists; split;
      [ cbn [In]; repeat first [left; reflexivity | right]
      | cbn [sv_denot]; ew_strip; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; apply HE; reflexivity ] |]);
  destruct Hin
| ] end.
lazymatch type of HS with st_ok _ ?Ec _ ?msc =>
assert (TOR : obj_at ubs0segs (ms_mem msc) res LAY_RawConfig cvals);
[ pose proof (st_ok_mem_ok _ _ _ _ HS) as Hm; destruct Hm as (_ & Hm & _); apply Forall_inv in Hm;
  unfold region_ok in Hm; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in Hm; destruct Hm as (_ & _ & _ & Hcs);
  ew_strip_in Hcs; rewrite Hq10, unsigned_lit_small in Hcs by lia;
  apply (rcfg_obj_of_chunks Ec _ res g pgct rattr W H sgct loops); [exact Hcs | | exact Hranges];
  intros j v Hj; pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Hlj; cbn [length] in Hlj;
  rewrite !ew_havoc_old by (first [apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); reflexivity | lia]); apply (HX j v Hj)
| ] end.
lazymatch type of HS with st_ok _ ?Ec _ ?msc =>
assert (TOC : obj_at ubs0segs (ms_mem msc) cfgp LAY_RawConfig cvals);
[ pose proof (st_ok_mem_ok _ _ _ _ HS) as Hm; destruct Hm as (_ & Hm & _); do 2 (apply Forall_inv_tail in Hm); apply Forall_inv in Hm;
  unfold region_ok in Hm; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in Hm; destruct Hm as (_ & _ & _ & Hcs);
  ew_strip_in Hcs; rewrite HE10, unsigned_lit_small in Hcs by lia;
  apply (rcfg_obj_of_chunks Ec _ cfgp g pgct rattr W H sgct loops); [exact Hcs | | exact Hranges];
  intros j v Hj; pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Hlj; cbn [length] in Hlj;
  rewrite !ew_havoc_old by (first [apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); reflexivity | lia]); apply (HX j v Hj)
| ] end.
lazymatch type of HS with st_ok _ ?Ec _ ?msc =>
assert (TOG : obj_at ubs0segs (ms_mem msc) g LAY_CGIF gvals);
[ pose proof (st_ok_mem_ok _ _ _ _ HS) as Hm; destruct Hm as (_ & Hm & _);
  do 3 (apply Forall_inv_tail in Hm); apply Forall_inv in Hm;
  unfold region_ok in Hm; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in Hm; destruct Hm as (_ & _ & _ & Hcs);
  ew_strip_in Hcs; rewrite HE33, unsigned_lit_small in Hcs by lia;
  apply (cgif_obj_of_chunks Ec _ g gvals Hcs Hglen Hwfn Hfile); [| exact Hgranges];
  intros j v Hj; pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Hlj; rewrite Hglen in Hlj;
  rewrite !ew_havoc_old by (first [apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); reflexivity | lia]); apply (HY j v Hj)
| ] end.
assert (HN0 : has_net 0 = false) by reflexivity.
lazymatch type of HSKc with sink_at _ ?m ?mdx ?fx ?Sx =>
assert (TSK : sink_at ubs0_msyms m mdx fx (S ++ YO07.raw_header W H sgct GCT 0 0));
[ replace (S ++ YO07.raw_header W H sgct GCT 0 0) with Sx; [exact HSKc | sink_eq0 HN0 Hs0] | ] end.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch type of HS with st_ok _ _ _ ?msc =>
lazymatch type of HJ3 with journal _ _ _ _ _ _ _ _ _ ?Lx ?Ax _ ?mdx =>
eapply SR_mono;
[ apply (rn_tail API IMG FWRITE L A mem md regs (ms_regs msc) Lx Ax (ms_mem msc) mdx cfgp g pgct rattr W H sgct loops res f gvals S GCT bq b1 b2);
  [ exact HJ3 | exact Hid2 | exact Hra | exact Htp | exact Hsp47 | exact TFS | exact T2'
  | apply TK; cbn; tauto | apply TK; cbn; tauto | apply TK; cbn; tauto | apply TK; cbn; tauto | apply TK; cbn; tauto | apply TK; cbn; tauto
  | exact T8 | exact T9 | exact T18 | exact Hcal | exact Hclo | exact Hchi | exact TOC | exact TOR | exact TOG | exact Hwfn | exact Hfile
  | exact Hgin | exact Hfin | rewrite HRSv; exact Hbl2 | exact Hblc
  | intros i Hi; apply Hwr'; [exact Hbin2 | rewrite HRSv in Hi; exact Hi]
  | exact TSK | exact Hroom | exact Hsg | unfold rawnew_rb; rewrite HRSv; exact HRq2 ]
| intros c' Hc'; exact Hc' ] end end.
Qed.
End S.
End t.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
