(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e
YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b YI06 UI5b YI09 YI08 YI0r
UI1w UI4l UI21 UI5o UI5l YI6b UN3c UN0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YL01 YN03 YI0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI17 YI14 YI18 YI1a UI5c YI07 YI05 YN00
UI22 YI5a UI23 UI5d UI5f UN38 UN36 YI00 YI01
UI3r UI3s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition NG_WTEST : Z := Eval vm_compute in (ubs0_A_cgif_newgif + 0x2c).
Definition NG_FOPENRET : Z := Eval vm_compute in (ubs0_A_cgif_newgif + 0x5c).
Definition NG_M96RET : Z := Eval vm_compute in (ubs0_A_cgif_newgif + 0x6c).
Definition NG_OBJ : Z := Eval vm_compute in (ubs0_A_cgif_newgif + 0x8c).
Definition NG_CPY : Z := Eval vm_compute in (ubs0_A_cgif_newgif + 0xc4).
Definition NG_PALRET : Z := Eval vm_compute in (ubs0_A_cgif_newgif + 0xe0).
Definition NG_PALCPY : Z := Eval vm_compute in (ubs0_A_cgif_newgif + 0xfc).
End c.
Definition ss_newgif : sstate :=
mkSS ubs0_A_cgif_newgif sr_atoms
[ YP09.mkRegion (Some 2%nat) (-40) 0 (-40) 0 [];
YP09.mkRegion (Some 10%nat) 0 48 0 0 cfg_chunks ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + NEWGIF_STK) (2^47) 4);
(10%nat, mkAF CEIL_MIN (2^63 - 48) 3);
(34%nat, mkAF 0 (2^32 - 1) 0); (36%nat, mkAF 0 65535 0); (37%nat, mkAF 0 65535 0);
(38%nat, mkAF 0 65535 0); (39%nat, mkAF 0 65535 0); (42%nat, mkAF 0 (2^32 - 1) 0) ] [] []).
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma denot_mul3 : forall E n x,
ew E n = Z_to_bv 64 x -> 0 <= x < 65536 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SLL (SOff n 0) (SLit 1)) (SOff n 0)) = Z_to_bv 64 (3 * x).
Proof using.
intros E n x Hn Hx. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E n x Hn), U_SLit by lia. change (Z.land (zcanon 1) 63) with 1.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
rewrite (zcanon_id (x * 2)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma denot_mul3' : forall E n x,
ew E n = Z_to_bv 64 x -> 0 <= x < 65536 ->
sv_denot E (SMd M_MUL (SOff n 0) (SLit 3)) = Z_to_bv 64 (3 * x).
Proof using.
intros E n x Hn Hx. rewrite denot_lit_U. f_equal. rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E n x Hn), U_SLit by lia.
change (zcanon 3) with 3. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma land4_mod32 : forall x, Z.land x 4 = Z.land (x mod 2 ^ 32) 4.
Proof using. intros x. rewrite <- (Z.land_ones x 32) by lia. rewrite <- Z.land_assoc. reflexivity. Qed.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis AX : AllocExtra ubs0_msyms MR.
Hypothesis MG : malloc_realizes_g ubs0_msyms MR.
Hypothesis RAWNEWX : rawnew_specX API.
Ltac ret_regs HS HE :=
apply regs_preserved_intro; cbn [ms_regs mkst]; reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
Ltac ret_pc HS HE Hra :=
cbn [ms_regs ms_mem mkst];
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
let Q1 := fresh "Q1" in
pose proof (st_ok_reg ubs0segs Ef ssf msf 1%bv HS) as Q1; eval_sr_get_in Q1; cbn [sv_denot] in Q1;
repeat (rewrite ew_havoc_old in Q1; [|nat_lt_lit]); rewrite ?Z.add_0_r, Z_to_bv_bv_unsigned, (HE 1%nat (1%bv:reg) eq_refl) in Q1;
rewrite Q1, Hra; reflexivity end.
Ltac wr_tac3 HU2 :=
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |];
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |];
apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_nil.
Theorem ubs0_cgif_newgif_x : newgif_x API.
Proof using AX IMG MG RAWNEWX.
unfold newgif_x.
intros L A regs mem md cfgp pal0 pala attr gen W H ngp loops rest GPAL b TA TB HPRE Hid Ha0 Hcal Hclo Hchi Hcfg HSN Hsp47 HWH Hpala HB HGP HFD HRES HROOM KA KB0 KB1.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HSTKv : NEWGIF_STK = 9216) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HFBv : FILE_BLOCK = 1264) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
set (sp0 := spZ regs) in *.
set (G := newgif_cfg W H attr gen ngp GPAL).
pose proof (obj_at_range _ _ _ _ _ Hcfg) as Rcfg.
pose proof (Rcfg 0%nat pal0 eq_refl) as Rpal0. pose proof (Rcfg 2%nat attr eq_refl) as Rattr. pose proof (Rcfg 3%nat gen eq_refl) as Rgen.
pose proof (Rcfg 4%nat W eq_refl) as RW. pose proof (Rcfg 5%nat H eq_refl) as RH. pose proof (Rcfg 6%nat ngp eq_refl) as Rngp.
pose proof (Rcfg 7%nat loops eq_refl) as Rloops.
cbn in Rpal0, Rattr, Rgen, RW, RH, Rngp, Rloops.
set (cvals := [pal0; ubs0_D_str_tmp_out_gif; attr; gen; W; H; ngp; loops; 0; 0]) in *.
set (E := Ereg regs (map (Z_to_bv 64) cvals ++ map (Z_to_bv 64) [W + 65536 * H] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error cvals j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HX42 : ew E 42 = Z_to_bv 64 (W + 65536 * H)) by (subst E; apply (Ereg_vals2 regs cvals [W + 65536 * H] [] 0); reflexivity).
assert (HX32 : ew E 32 = Z_to_bv 64 pal0) by (apply (HX 0%nat); reflexivity).
assert (HX34 : ew E 34 = Z_to_bv 64 attr) by (apply (HX 2%nat); reflexivity).
assert (HX35 : ew E 35 = Z_to_bv 64 gen) by (apply (HX 3%nat); reflexivity).
assert (HX36 : ew E 36 = Z_to_bv 64 W) by (apply (HX 4%nat); reflexivity).
assert (HX37 : ew E 37 = Z_to_bv 64 H) by (apply (HX 5%nat); reflexivity).
assert (HX38 : ew E 38 = Z_to_bv 64 ngp) by (apply (HX 6%nat); reflexivity).
assert (HX39 : ew E 39 = Z_to_bv 64 loops) by (apply (HX 7%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = cfgp) by (rewrite (HE 10%nat 10%bv eq_refl), Ha0; apply unsigned_lit_small; lia).
pose proof Hcfg as Hc. cbn [obj_at LAY_Config] in Hc. unfold field_ok in Hc. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N] in Hc.
destruct Hc as ((F0 & _) & (F1 & _) & (F2 & _) & (F3 & _) & (F4 & _) & (F5 & _) & (F6 & _) & (F7 & _) & (F8 & _) & (F9 & _) & _).
assert (Rpath : 0 <= ubs0_D_str_tmp_out_gif < 2 ^ 64) by (unfold ubs0_D_str_tmp_out_gif; lia).
assert (HS : st_ok ubs0segs E ss_newgif (mkst regs (Z_to_bv 64 ubs0_A_cgif_newgif) mem (seg_rom ubs0segs))).
{ unfold ss_newgif. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ apply (region_ok_stack ubs0segs _ mem 2 sp0); [exact HU2 | lia | lia | intros a Ha; apply Hstw; lia].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU10.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
unfold cfg_chunks.
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ pal0); [cbn [sv_denot]; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact F0]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ ubs0_D_str_tmp_out_gif); [reflexivity | exact Rpath | cbn; lia | exact F1]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ attr); [cbn [sv_denot]; rewrite Z.add_0_r, HX34, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact F2]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ gen); [cbn [sv_denot]; rewrite Z.add_0_r, HX35, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact F3]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (W + 65536 * H)); [cbn [sv_denot]; rewrite Z.add_0_r, HX42, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_wh_join; [exact F4 | replace (cfgp + 24 + 2) with (cfgp + 26) by lia; exact F5 | lia | lia]]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ ngp); [cbn [sv_denot]; rewrite Z.add_0_r, HX38, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact F6]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ loops); [cbn [sv_denot]; rewrite Z.add_0_r, HX39, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact F7]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ 0); [reflexivity | lit_range | cbn; lia | exact F8]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ 0); [reflexivity | lit_range | cbn; lia | exact F9]. }
apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU10. repeat split; lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, HX34, HX36, HX37, HX38, HX39, HX42, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; assumption. }
pose proof (journal_init ubs0_msyms MR NEWGIF_STK [sink_token] L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 ubs0_A_cgif_newgif) mem (seg_rom ubs0segs))) in HJ.
fold sp0 in HJ.
apply realizes_via_SR.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_memset.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ma0. rewrite HU2 in Ma0.
jreg HS (11%bv:reg) as Ma1. jreg HS (12%bv:reg) as Ma2. jreg HS (1%bv:reg) as Mra.
eapply SR_bind.
{ eapply (jmemset ubs0_msyms MR LAWS IMG ubs0_A_memset ubs0_memset E _ _ NEWGIF_STK sp0 [sink_token] L A mem md L A _ (sp0 - 80) 0 40);
[ exact HS | reflexivity | reflexivity | exact HJ | replace (sp0 - 80) with (sp0 + -80) by lia; exact Ma0 | exact Ma1 | exact Ma2 | exact Mra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | | ].
- intros i Hi. match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
apply writable_off_img_present; [lia | unfold in_img1; lia | apply Hstw; lia].
- intros a Ha. left. lia. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hd10 & Hfr2 & Hout2 & Hgr2 & Hzero2). clear HJ.
jafter_stretch_keep HS 43%nat regs2 mem2 MEMSET_CLOB NG_WTEST [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2. exact Hrr. }
{ constructor; [|constructor; [|constructor]].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU2; lia | cbn [r_base r_hi base_val]; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU10; lia | cbn [r_base r_hi base_val]; rewrite HU10; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU10; intros a Ha; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
add_region HS (YP09.mkRegion (Some 2%nat) (-80) (-40) (-80) (-40) [mkChunk (-80) (CZero 40)]).
2:{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. ew_havocA. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (writable_at_grows ubs0segs (ms_mem ms) mem2); [exact Hgr2|]. cbn [ms_mem mkst] in HG. apply (writable_at_grows ubs0segs mem (ms_mem ms)); [exact HG|]. apply Hstw. lia. }
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. cbn [c_off]. intros i Hi.
replace (sp0 + -80 + i) with (sp0 - 80 + i) by lia. apply Hzero2. exact Hi. }
2:{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite HU2, HU10. repeat split; lia. }
jrun LAWS ubs0tbl_ok HS HJ2. { wr_tac3 HU2. }
jbranch ubs0tbl HS.
{
rewrite branch_eq_U, U_zext, U_lit, (U_atom _ 42 (W + 65536 * H)) in Hc by first [lia | ew_havocA; exact HX42].
change (2 ^ Z.of_N 16) with 65536 in Hc.
assert (HW0 : W = 0).
{ destruct (Z.eqb_spec ((W + 65536 * H) mod 65536) 0) as [Hz|Hz]; [|discriminate Hc].
rewrite Z.mul_comm, Z_mod_plus_full, Z.mod_small in Hz by lia. lia. }
clear Hc.
jrun LAWS ubs0tbl_ok HS HJ2. { wr_tac3 HU2. }
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2)))). }
replace (g_opens G) with false by (subst G; unfold g_opens, newgif_cfg; cbn [YO07.g_w YO07.g_h]; rewrite HW0; reflexivity).
apply KA. unfold newgif_postA.
lazymatch type of HS with st_ok _ _ _ ?msf => exists L, A, (ms_regs msf), (ms_mem msf), md end.
split; [ret_pc HS HE Hra|]. split; [exact HJ2|]. split; [ret_regs HS HE|]. split; [exact Hid|].
split; [reg_nowF HS ltac:(reflexivity)|]. split; [apply Permutation_refl|].
split; [| split; [reflexivity | apply (res_ok_mono _ _ _ (rb_acc_le b NEWGIF_K PALSLACK ltac:(unfold NEWGIF_K; lia) ltac:(unfold PALSLACK; lia)) HRES)]].
eapply (sink_none_frame ubs0_msyms mem); [| exact HSN]. intros a Ha. pose proof (ubs0_env_addr_range a Ha).
mem_back ltac:(rewrite ?HU2, ?HU10) ltac:(lia). }
rewrite branch_eq_U, U_zext, U_lit, (U_atom _ 42 (W + 65536 * H)) in Hc by first [lia | ew_havocA; exact HX42].
change (2 ^ Z.of_N 16) with 65536 in Hc.
assert (HW1 : 1 <= W).
{ destruct (Z.eqb_spec ((W + 65536 * H) mod 65536) 0) as [Hz|Hz]; [discriminate Hc|].
rewrite Z.mul_comm, Z_mod_plus_full, Z.mod_small in Hz by lia. lia. }
clear Hc.
jrun LAWS ubs0tbl_ok HS HJ2. { wr_tac3 HU2. }
jbranch ubs0tbl HS.
{
rewrite branch_eq_U, U_SAlu, U_lit, (U_atom _ 42 (W + 65536 * H)) in Hc by first [lia | ew_havocA; exact HX42].
cbn [zalu_raw] in Hc. rewrite ?U_SLit in Hc. change (Z.land 16 63) with 16 in Hc. change (zcanon 0) with 0 in Hc.
rewrite Z.shiftr_div_pow2 in Hc by lia. change (2 ^ 16) with 65536 in Hc.
replace ((W + 65536 * H) / 65536) with H in Hc by (rewrite Z.mul_comm, Z.div_add, Z.div_small by lia; lia).
rewrite zcanon_id in Hc by (unfold M64; lia).
assert (HH0 : H = 0) by (destruct (Z.eqb_spec H 0); [assumption | discriminate Hc]). clear Hc.
jrun LAWS ubs0tbl_ok HS HJ2. { wr_tac3 HU2. }
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2)))). }
replace (g_opens G) with false by (subst G; unfold g_opens, newgif_cfg; cbn [YO07.g_w YO07.g_h]; rewrite HH0, Z.eqb_refl, orb_true_r; reflexivity).
apply KA. unfold newgif_postA.
lazymatch type of HS with st_ok _ _ _ ?msf => exists L, A, (ms_regs msf), (ms_mem msf), md end.
split; [ret_pc HS HE Hra|]. split; [exact HJ2|]. split; [ret_regs HS HE|]. split; [exact Hid|].
split; [reg_nowF HS ltac:(reflexivity)|]. split; [apply Permutation_refl|].
split; [| split; [reflexivity | apply (res_ok_mono _ _ _ (rb_acc_le b NEWGIF_K PALSLACK ltac:(unfold NEWGIF_K; lia) ltac:(unfold PALSLACK; lia)) HRES)]].
eapply (sink_none_frame ubs0_msyms mem); [| exact HSN]. intros a Ha. pose proof (ubs0_env_addr_range a Ha).
mem_back ltac:(rewrite ?HU2, ?HU10) ltac:(lia). }
rewrite branch_eq_U, U_SAlu, U_lit, (U_atom _ 42 (W + 65536 * H)) in Hc by first [lia | ew_havocA; exact HX42].
cbn [zalu_raw] in Hc. rewrite ?U_SLit in Hc. change (Z.land 16 63) with 16 in Hc. change (zcanon 0) with 0 in Hc.
rewrite Z.shiftr_div_pow2 in Hc by lia. change (2 ^ 16) with 65536 in Hc.
replace ((W + 65536 * H) / 65536) with H in Hc by (rewrite Z.mul_comm, Z.div_add, Z.div_small by lia; lia).
rewrite zcanon_id in Hc by (unfold M64; lia).
assert (HH1 : 1 <= H) by (destruct (Z.eqb_spec H 0); [discriminate Hc | lia]). clear Hc.
assert (HGO : g_opens G = true).
{ subst G. unfold g_opens, newgif_cfg. cbn [YO07.g_w YO07.g_h].
destruct (Z.eqb_spec W 0); [lia|]. destruct (Z.eqb_spec H 0); [lia|]. reflexivity. }
jrun_to LAWS ubs0tbl_ok HS HJ2 ubs0_A_fopen. { wr_tac3 HU2. }
jreg HS (10%bv:reg) as Fa0. jreg HS (11%bv:reg) as Fa1. jreg HS (2%bv:reg) as Fsp. rewrite HU2 in Fsp.
jreg HS (4%bv:reg) as Ftp. rewrite (HE 4%nat 4%bv eq_refl), Htp in Ftp. jreg HS (1%bv:reg) as Fra.
assert (Hspm : (sp0 - 80) mod 16 = 0) by (replace (sp0 - 80) with (sp0 + (-5) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
apply SR_here. rewrite HGO.
lazymatch goal with |- realizes _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
assert (HPRE1 : fn_pre ubs0_msyms MR FOPEN_STK L A rg mm md)
by (eapply (fn_pre_of_journal ubs0_msyms MR); [exact HJ2 | rewrite Fra; apply ret_ok_even; vm_compute; reflexivity
| unfold spZ; rewrite Fsp, unsigned_lit_small by lia; exact Hspm | unfold FOPEN_STK; lia
| unfold spZ, FOPEN_STK; rewrite Fsp, unsigned_lit_small by lia; lia | unfold spZ; rewrite Fsp, unsigned_lit_small by lia; lia | exact Ftp])
end.
lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?mm _) _) _ =>
assert (HSN1 : sink_none ubs0_msyms mm md)
by (eapply (sink_none_frame ubs0_msyms mem); [| exact HSN]; intros a Ha; pose proof (ubs0_env_addr_range a Ha);
mem_back ltac:(rewrite ?HU2, ?HU10) ltac:(lia))
end.
eapply (ubs0_fopenX API IMG AX MG L A _ _ md b TA TB HPRE1 Hid);
[ unfold spZ; rewrite Fsp, unsigned_lit_small by lia; lia
| rewrite Fa0; reflexivity | rewrite Fa1; reflexivity | exact HSN1 | exact HRES
| exact (ng_room1 b HROOM)
| exact HFD | | ].
-
intros c' (L4 & A4 & regs4 & mem4 & md4 & -> & HJc & HP4 & Hid4 & Hr10 & HB4 & HSN4 & Hfds4 & Hfs4 & HR4).
apply realizes_via_SR. rewrite Fra.
cbn [ms_regs ms_mem mkst] in HJc, HP4.
pose proof HJc as (_ & _ & Hhi4 & _).
assert (HJ4 : journal ubs0_msyms MR NEWGIF_STK sp0 [sink_token] L A mem md L4 A4 mem4 md4).
{ eapply (journal_sub ubs0_msyms MR); [exact HJ2 | exact HJc | unfold spZ, FOPEN_STK; rewrite Fsp, unsigned_lit_small by lia; lia
| unfold spZ; rewrite Fsp, unsigned_lit_small by lia; lia | intros a Ha; split; [exact Ha | pose proof (inFP_token a Ha); lia]]. }
jafter_call_keep HS 49%nat regs4 mem4 HP4 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack ubs0segs _ _ _ 2); [ew_havocA; exact HU2 | exact Hhi4 | lia | lia | unfold spZ; rewrite Fsp, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs0segs _ _ _ 2); [ew_havocA; exact HU2 | exact Hhi4 | lia | lia | unfold spZ; rewrite Fsp, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs0segs _ _ _ 10); [ew_havocA; exact HU10 | exact Hhi4 | lia | lia | unfold spZ; rewrite Fsp, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
pin_reg HS (10%bv:reg) 0 Hr10.
jrun LAWS ubs0tbl_ok HS HJ4. { wr_tac3 HU2. }
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ4))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ4)))). }
apply KA. unfold newgif_postA.
lazymatch type of HS with st_ok _ _ _ ?msf => exists L4, A4, (ms_regs msf), (ms_mem msf), md4 end.
split; [ret_pc HS HE Hra|]. split; [exact HJ4|]. split; [ret_regs HS HE|]. split; [exact Hid4|].
split; [reg_nowF HS ltac:(reflexivity)|]. split; [exact HB4|].
split; [| split; [exact Hfs4 | apply (res_ok_mono _ _ _ (rb_acc_le b NEWGIF_K PALSLACK ltac:(unfold NEWGIF_K; lia) ltac:(unfold PALSLACK; lia)) HR4)]].
eapply (sink_none_frame ubs0_msyms mem4); [| exact HSN4]. intros a Ha. pose proof (ubs0_env_addr_range a Ha).
mem_back ltac:(rewrite ?HU2, ?HU10) ltac:(lia).
-
intros c' (L4 & A4 & regs4 & mem4 & md4 & f & -> & HJc & HP4 & Hid4 & Hr10 & Hfnz & HB4 & HSK4 & Hfs4 & HR4).
apply realizes_via_SR. rewrite Fra.
cbn [ms_regs ms_mem mkst] in HJc, HP4.
pose proof HJc as (_ & _ & Hhi4 & _).
assert (HJ4 : journal ubs0_msyms MR NEWGIF_STK sp0 [sink_token] L A mem md L4 A4 mem4 md4).
{ eapply (journal_sub ubs0_msyms MR); [exact HJ2 | exact HJc | unfold spZ, FOPEN_STK; rewrite Fsp, unsigned_lit_small by lia; lia
| unfold spZ; rewrite Fsp, unsigned_lit_small by lia; lia | intros a Ha; split; [exact Ha | pose proof (inFP_token a Ha); lia]]. }
jafter_call_keep HS 49%nat regs4 mem4 HP4 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack ubs0segs _ _ _ 2); [ew_havocA; exact HU2 | exact Hhi4 | lia | lia | unfold spZ; rewrite Fsp, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs0segs _ _ _ 2); [ew_havocA; exact HU2 | exact Hhi4 | lia | lia | unfold spZ; rewrite Fsp, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs0segs _ _ _ 10); [ew_havocA; exact HU10 | exact Hhi4 | lia | lia | unfold spZ; rewrite Fsp, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jreg HS (10%bv:reg) as Hf53. cbn [ms_regs mkst] in Hf53. rewrite Hr10 in Hf53. symmetry in Hf53.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HH4.
assert (Hfin4 : In (f, FILE_BLOCK) (blocks L4 A4)) by (eapply blocks_perm_in; [exact HB4 | left; reflexivity]).
destruct (heap_blocks_range _ _ LAWS L4 A4 mem4 md4 f FILE_BLOCK HH4 Hfin4 ltac:(lia)) as (Hf0 & Hf1 & Hf16).
assert (Hffresh : ~ In (f, FILE_BLOCK) (blocks L A)).
{ intros Hin. pose proof (heap_sep_perm _ _ LAWS L4 A4 mem4 md4 _ _ _ HH4 HB4 Hin) as Hs. cbn [fst snd] in Hs. lia. }
add_fact HS 53%nat (mkAF 4096 (CEIL_MAX - FILE_BLOCK) 4).
2:{ rewrite Hf53, unsigned_lit_small by lia. change (2 ^ 4) with 16. lia. }
assert (Hf53' : bv_unsigned (ew (havoc (havoc E 43 (map (getr regs2) MEMSET_CLOB)) 49 (map (getr regs4) CLOB)) 53) = f) by (rewrite Hf53; apply unsigned_lit_small; lia).
jrun_to LAWS ubs0tbl_ok HS HJ4 ubs0_A_malloc. { wr_tac3 HU2. }
jreg HS (10%bv:reg) as Hr10'. jreg HS (2%bv:reg) as Hr2. rewrite HU2 in Hr2.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), Htp in Hr4. jreg HS (1%bv:reg) as Hr1.
pose proof (journal_restart ubs0_msyms MR _ _ _ _ _ _ _ _ _ _ _ (@nil (Z * Z)) HJ4) as HJl.
eapply SR_bind.
{ eapply (jmalloc_at_res API IMG) with (n := 96) (spc := sp0 - 80) (b := ng_b1 b);
[ exact HS | reflexivity | reflexivity | exact HJl | exact Hid4 | exact Hr10' | exact HR4
| exact (ng_room2 b HROOM)
| rewrite Hr2; f_equal; lia | lia | exact Hspm | lia | lia | exact Hr4 | exact Hr1 | apply ret_ok_even; vm_compute; reflexivity ]. }
intros c' (L5 & A5 & regs5 & mem5 & md5 & g & -> & HJl5 & Hid5 & HP5 & Hg10 & (Hgnz & Hg16 & (b1 & b2 & Hbl5 & Hblc5) & Hwr5) & Hkeep5 & Hhi5 & HR5).
change (ms_segs ubs0_msyms) with ubs0segs in Hkeep5, Hhi5. cbn [ms_regs ms_mem mkst] in HP5, Hkeep5, Hhi5, HJl5, Hg10.
assert (HJ5 : journal ubs0_msyms MR NEWGIF_STK sp0 [sink_token] L A mem md L5 A5 mem5 md5).
{ eapply (journal_sub ubs0_msyms MR); [exact HJ4 | exact HJl5 | lia | lia | intros a (r & [] & _)]. }
assert (HK5 : sink_at ubs0_msyms mem5 md5 f [] /\ In (f, FILE_BLOCK) (blocks L5 A5)).
{ eapply (sink_kept ubs0_msyms MR); [exact HJl5 | intros (r & [] & _) | exact Hfin4 | intros a _ (r & [] & _) |].
apply (sink_at_frame ubs0_msyms mem4 _ md4 f []); [|exact HSK4].
intros a Ha. assert (Ha' : 0 <= a < alloc_ceiling) by (destruct Ha as [Ha|Ha]; [lia | pose proof (ubs0_env_addr_range a Ha); lia]).
mem_back ltac:(rewrite ?HU2, ?HU10, ?Hf53') ltac:(lia). }
destruct HK5 as [HSK5 Hfin5]. clear HJl HJl5.
jafter_call_keep HS 65%nat regs5 mem5 HP5 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack ubs0segs _ _ _ 2); [ew_havocA; exact HU2 | exact Hhi5 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs0segs _ _ _ 2); [ew_havocA; exact HU2 | exact Hhi5 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs0segs _ _ _ 10); [ew_havocA; exact HU10 | exact Hhi5 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jreg HS (10%bv:reg) as Hq69. cbn [ms_regs mkst] in Hq69. rewrite Hg10 in Hq69. symmetry in Hq69.
assert (Hgin5 : In (g, CGIF_SIZE) (blocks L5 A5)) by (rewrite HGSv, Hbl5; apply in_app_iff; right; left; reflexivity).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5) as HH5.
destruct (heap_blocks_range _ _ LAWS L5 A5 mem5 md5 g CGIF_SIZE HH5 Hgin5 ltac:(lia)) as (Hg0 & Hg1 & _).
assert (Hbase5 : forall bb, In bb (blocks L4 A4) -> In bb (blocks L5 A5)).
{ intros bb Hb. rewrite Hbl5. rewrite Hblc5 in Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact Hb | right; right; exact Hb]. }
assert (Hgfresh4 : ~ In (g, CGIF_SIZE) (blocks L4 A4)).
{ rewrite HGSv, Hblc5. apply (fresh_not_in API L5 A5 mem5 md5 b1 b2 g 96 HH5 Hbl5). lia. }
assert (Hgfresh : ~ In (g, CGIF_SIZE) (blocks L A)).
{ intros Hin. apply Hgfresh4. eapply Permutation_in; [apply Permutation_sym; exact HB4 | right; exact Hin]. }
assert (Hsep_fg : f + FILE_BLOCK <= g \/ g + CGIF_SIZE <= f).
{ rewrite HGSv. destruct (heap_sep _ _ LAWS L5 A5 mem5 md5 b1 (g, 96) b2 (f, FILE_BLOCK) HH5 Hbl5 ltac:(rewrite <- Hblc5; exact Hfin4)) as [H0|H0]; cbn [fst snd] in H0; lia. }
add_fact HS 69%nat (mkAF 4096 (CEIL_MAX - CGIF_SIZE) 4).
2:{ rewrite Hq69, unsigned_lit_small by lia. change (2 ^ 4) with 16. lia. }
assert (Hq69' : bv_unsigned (ew (havoc (havoc (havoc E 43 (map (getr regs2) MEMSET_CLOB)) 49 (map (getr regs4) CLOB)) 65 (map (getr regs5) CLOB)) 69) = g) by (rewrite Hq69; apply unsigned_lit_small; lia).
assert (Henvblk : forall L1 A1 m1 md1 bb n a, heap_ok MR L1 A1 m1 md1 -> In (bb, n) (blocks L1 A1) -> env_addr a -> ~ (bb <= a < bb + n)).
{ intros L1 A1 m1 md1 bb n a HHx Hin1 Hea Hr. apply blocks_In in Hin1 as (q & Hq & Hqin).
destruct (skl_env ubs0_msyms a Hea) as (Himg1 & _). assert (Hrg : 0 <= a - bb < n) by lia.
apply (il_blocks IMG L1 A1 m1 md1 q n (a - bb) (proj1 HHx) Hqin Hrg). rewrite Hq. replace (bb + (a - bb)) with a by lia. exact Himg1. }
jrun_to LAWS ubs0tbl_ok HS HJ5 ubs0_A_memset. { wr_tac3 HU2. }
jreg HS (10%bv:reg) as Mb0. rewrite Hq69 in Mb0. jreg HS (11%bv:reg) as Mb1. jreg HS (12%bv:reg) as Mb2. jreg HS (1%bv:reg) as Mbra.
eapply SR_bind.
{ lazymatch type of HS with st_ok _ ?E1 _ _ =>
eapply (jmemset ubs0_msyms MR LAWS IMG ubs0_A_memset ubs0_memset E1 _ _ NEWGIF_STK sp0 [sink_token] L A mem md L5 A5 _ g 0 96);
[ exact HS | reflexivity | reflexivity | exact HJ5 | exact Mb0 | exact Mb1 | exact Mb2 | exact Mbra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | | ] end.
- intros i Hi. match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
apply (proj1 (heap_blocks _ _ LAWS L5 A5 mem5 md5 g CGIF_SIZE i HH5 Hgin5 ltac:(lia))).
- intros a Ha. right. right. exists g, CGIF_SIZE. split; [exact Hgin5|]. split; [exact Hgfresh | lia]. }
cbv beta. intros c' (regs6 & mem6 & -> & HJ6 & Hd10' & Hfr6 & Hout6 & Hgr6 & Hzero6). clear HJ5.
assert (HSK6 : sink_at ubs0_msyms mem6 md5 f []).
{ lazymatch type of Hgr6 with mem_grows ?m0 _ => apply (sink_at_frame ubs0_msyms m0 _ md5 f []) end.
- intros a Ha. assert (Ha' : 0 <= a < alloc_ceiling /\ ~ (g <= a < g + 96))
by (destruct Ha as [Ha|Ha]; [lia | pose proof (ubs0_env_addr_range a Ha); pose proof (Henvblk L5 A5 mem5 md5 g CGIF_SIZE a HH5 Hgin5 Ha); lia]).
apply (mbyte_eq_of ubs0_msyms). apply Hout6. rewrite unsigned_lit_small by lia. lia.
- apply (sink_at_frame ubs0_msyms mem5 _ md5 f []); [|exact HSK5].
intros a Ha. assert (Ha' : 0 <= a < alloc_ceiling) by (destruct Ha as [Ha|Ha]; [lia | pose proof (ubs0_env_addr_range a Ha); lia]).
mem_back ltac:(rewrite ?HU2, ?HU10, ?Hf53', ?Hq69') ltac:(lia). }
jafter_stretch_keep HS 81%nat regs6 mem6 MEMSET_CLOB (ubs0_A_cgif_newgif + 0x9c) [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr6. exact Hrr. }
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply region_kept_out; [exact Hout6 | exact Hgr6 | cbn [r_base r_lo base_val]; ew_havocA; rewrite HU2; lia | cbn [r_base r_hi base_val]; ew_havocA; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; ew_havocA; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout6 | exact Hgr6 | cbn [r_base r_lo base_val]; ew_havocA; rewrite HU2; lia | cbn [r_base r_hi base_val]; ew_havocA; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; ew_havocA; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout6 | exact Hgr6 | cbn [r_base r_lo base_val]; ew_havocA; rewrite HU10; lia | cbn [r_base r_hi base_val]; ew_havocA; rewrite HU10; lia | cbn [r_base r_lo r_hi base_val]; ew_havocA; rewrite HU10; intros a Ha; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ6) as HH6.
add_region HS (YP09.mkRegion (Some 69%nat) 0 72 0 0 [mkChunk 0 (CZero 72)]).
2:{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. ew_havocA. rewrite Hq69, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. cbn [c_off ms_mem mkst]. intros i Hi. rewrite Z.add_0_r. apply Hzero6. lia. }
2:{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite ?HU2, ?HU10, ?Hq69, ?unsigned_lit_small by lia. repeat split; lia. }
add_region HS (YP09.mkRegion (Some 69%nat) 72 96 72 96 [mkChunk 72 (CZero 24)]).
2:{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. ew_havocA. rewrite Hq69, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable ubs0segs). apply (proj1 (heap_blocks _ _ LAWS L5 A5 mem6 md5 g CGIF_SIZE o HH6 Hgin5 ltac:(lia))). }
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. cbn [c_off ms_mem mkst]. intros i Hi. replace (g + 72 + i) with (g + (72 + i)) by lia. apply Hzero6. lia. }
2:{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite ?HU2, ?HU10, ?Hq69, ?unsigned_lit_small by lia. repeat split; lia. }
jrun_to LAWS ubs0tbl_ok HS HJ6 ubs0_A_memcpy.
{ eapply wr_ok_cons_tmp; [reflexivity | ew_havocA; rewrite Hq69; apply unsigned_lit_small; lia | exact Hgin5 | exact Hgfresh | cbn; lia | cbn; lia |].
apply wr_ok_cons_ro; [cbn; lia|].
wr_tac3 HU2. }
jreg HS (10%bv:reg) as Mc0. rewrite Hq69, unsigned_lit_small in Mc0 by lia. jreg HS (11%bv:reg) as Mc1. rewrite (HE 10%nat 10%bv eq_refl), Ha0 in Mc1.
jreg HS (12%bv:reg) as Mc2. jreg HS (1%bv:reg) as Mcra.
unfold spZ in Hhi4. rewrite Fsp, unsigned_lit_small in Hhi4 by lia. change (ms_segs ubs0_msyms) with ubs0segs in Hhi4. unfold FOPEN_STK in Hhi4.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hcfg1 : obj_at ubs0segs (ms_mem msx) cfgp LAY_Config cvals)
end.
{ eapply (obj_at_transport_range _ _ _ _ _ _ 48); [exact Hcfg | reflexivity |]. intros i Hi.
mem_back ltac:(rewrite ?HU2, ?HU10, ?Hf53', ?Hq69, ?unsigned_lit_small by lia) ltac:(lia). }
eapply SR_bind.
{ eapply (UI4l.jmemcpy_rd API IMG _ ubs0_memcpy) with (d := g + 24) (src := cfgp) (n := 48);
[ exact HS | reflexivity | reflexivity | exact HJ6 | exact Mc0 | exact Mc1 | exact Mc2 | exact Mcra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | lia | | | lia | ].
- intros i Hi. match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
replace (g + 24 + i) with (g + (24 + i)) by lia.
apply (proj1 (heap_blocks _ _ LAWS L5 A5 mem6 md5 g CGIF_SIZE (24 + i) HH6 Hgin5 ltac:(lia))).
- apply (obj_at_readable _ _ _ _ _ 48 Hcfg1). reflexivity.
- intros a Ha. right. right. exists g, CGIF_SIZE. split; [exact Hgin5|]. split; [exact Hgfresh | lia]. }
cbv beta. intros c' (regs7 & mem7 & -> & HJ7 & Hd10'' & Hfr7 & Hout7 & Hgr7 & Hcp7). clear HJ6.
assert (HSK7 : sink_at ubs0_msyms mem7 md5 f []).
{ lazymatch type of Hgr7 with mem_grows ?m0 _ => apply (sink_at_frame ubs0_msyms m0 _ md5 f []) end.
- intros a Ha. assert (Ha' : 0 <= a < alloc_ceiling /\ ~ (g <= a < g + 96))
by (destruct Ha as [Ha|Ha]; [lia | pose proof (ubs0_env_addr_range a Ha); pose proof (Henvblk L5 A5 mem5 md5 g CGIF_SIZE a HH5 Hgin5 Ha); lia]).
apply (mbyte_eq_of ubs0_msyms). apply Hout7. rewrite unsigned_lit_small by lia. lia.
- apply (sink_at_frame ubs0_msyms mem6 _ md5 f []); [|exact HSK6].
intros a Ha. assert (Ha' : 0 <= a < alloc_ceiling /\ ~ (g <= a < g + 96))
by (destruct Ha as [Ha|Ha]; [lia | pose proof (ubs0_env_addr_range a Ha); pose proof (Henvblk L5 A5 mem5 md5 g CGIF_SIZE a HH5 Hgin5 Ha); lia]).
mem_back ltac:(rewrite ?HU2, ?HU10, ?Hf53', ?Hq69, ?unsigned_lit_small by lia) ltac:(lia). }
jafter_stretch_keep HS 87%nat regs7 mem7 MEMCPY_CLOB NG_CPY [0%nat; 2%nat; 3%nat; 4%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr7. exact Hrr. }
{ repeat apply Forall_cons; try apply Forall_nil;
(eapply region_kept_out; [exact Hout7 | exact Hgr7 | cbn [r_base r_lo base_val]; ew_havocA; rewrite ?HU2, ?HU10, ?Hq69, ?unsigned_lit_small by lia; lia
| cbn [r_base r_hi base_val]; ew_havocA; rewrite ?HU2, ?HU10, ?Hq69, ?unsigned_lit_small by lia; lia
| cbn [r_base r_lo r_hi base_val]; ew_havocA; rewrite ?HU2, ?HU10, ?Hq69, ?unsigned_lit_small by lia; intros a Ha; lia | cbn; lia | cbn; lia]). }
clear HS. rename HS2 into HS.
lazymatch type of HS with st_ok _ _ _ ?msx =>
assert (Hcfg2 : obj_at ubs0segs (ms_mem msx) cfgp LAY_Config cvals);
[ eapply (obj_at_transport_range _ _ _ _ _ _ 48); [exact Hcfg1 | reflexivity |]; intros i Hi;
mem_back ltac:(rewrite ?HU2, ?HU10, ?Hf53', ?Hq69, ?unsigned_lit_small by lia) ltac:(lia) |]
end.
lazymatch type of HS with st_ok _ _ _ ?msx =>
assert (heap_present_now : forall o, 0 <= o < CGIF_SIZE -> present (ms_mem msx) (g + 24 + (o - 24)))
end.
{ intros o Ho. replace (g + 24 + (o - 24)) with (g + o) by lia. cbn [ms_mem mkst] in *. eapply (present_grows _ _ _ Hgr7).
match goal with HGx : mem_grows mem6 ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end.
apply (proj1 (heap_blocks _ _ LAWS L5 A5 mem6 md5 g CGIF_SIZE o HH6 Hgin5 Ho)). }
lazymatch type of HS with st_ok _ _ _ ?msx =>
assert (Hcopy : obj_at ubs0segs (ms_mem msx) g (lay_shift 24 LAY_Config) cvals)
end.
{ apply obj_at_shift. cbn [ms_mem mkst]. eapply (obj_at_copy ubs0segs _ mem7 cfgp (g + 24) LAY_Config cvals 48); [exact Hcfg1 | reflexivity | exact Hcp7]. }
add_region HS (YP09.mkRegion (Some 69%nat) 0 72 0 72 (mkChunk 0 (CZero 24) :: obj_chunks_gen (lay_shift 24 LAY_Config) 32 lits_Config)).
2:{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. ew_havocA. rewrite Hq69, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable ubs0segs). cbn [ms_mem mkst] in *.
replace (g + o) with (g + 24 + (o - 24)) by lia. apply (heap_present_now o). lia. }
apply Forall_cons.
{ apply chunk_ok_zero. cbn [c_off]. intros i Hi. rewrite Z.add_0_r.
transitivity (mbyte ubs0segs mem6 (g + i)); [| apply Hzero6; lia].
mem_back ltac:(rewrite ?HU2, ?HU10, ?Hf53', ?Hq69, ?unsigned_lit_small by lia) ltac:(lia). }
eapply (obj_chunks_gen_ok ubs0segs _ _ g _ cvals 32 lits_Config); [exact Hcopy | reflexivity | | apply lits_Config_ok].
intros j v Hj. assert (Hlj : (j < 10)%nat) by (destruct (Nat.lt_ge_cases j 10) as [Hl|Hl]; [exact Hl|]; rewrite (proj2 (nth_error_None cvals j) Hl) in Hj; discriminate).
rewrite !ew_havoc_old by lia. exact (HX j v Hj). }
2:{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite ?HU2, ?HU10, ?Hq69, ?unsigned_lit_small by lia. repeat split; lia. }
jrun LAWS ubs0tbl_ok HS HJ7.
{ eapply wr_ok_cons_tmp; [reflexivity | ew_havocA; rewrite Hq69; apply unsigned_lit_small; lia | exact Hgin5 | exact Hgfresh | cbn; lia | cbn; lia |].
eapply wr_ok_cons_tmp; [reflexivity | ew_havocA; rewrite Hq69; apply unsigned_lit_small; lia | exact Hgin5 | exact Hgfresh | cbn; lia | cbn; lia |].
wr_tac3 HU2. }
assert (HBc : Permutation (blocks L5 A5) ((g, CGIF_SIZE) :: [] ++ (f, FILE_BLOCK) :: blocks L A)).
{ rewrite HGSv, Hbl5. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. cbn [app]. apply perm_skip. rewrite <- Hblc5. exact HB4. }
jbranch ubs0tbl HS.
+
rewrite branch_ne_U, U_and_lit, (U_atom _ 34 attr), U_lit in Hc by first [lia | ew_havocA; exact HX34].
assert (Hattr4 : Z.land attr 4 <> 0) by (intros Hz; rewrite Hz in Hc; discriminate Hc). clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ7 (ubs0_A_cgif_newgif + 0x11c).
{ eapply wr_ok_cons_tmp; [reflexivity | ew_havocA; rewrite Hq69; apply unsigned_lit_small; lia | exact Hgin5 | exact Hgfresh | cbn; lia | cbn; lia |].
eapply wr_ok_cons_tmp; [reflexivity | ew_havocA; rewrite Hq69; apply unsigned_lit_small; lia | exact Hgin5 | exact Hgfresh | cbn; lia | cbn; lia |].
wr_tac3 HU2. }
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (newgif_tail_x API IMG AX RAWNEWX L A mem md regs rg L5 A5 mm md5 cfgp pal0 pala attr gen W H ngp loops g pal0 0 f [] GPAL b TB) end.
* exact HJ7. * exact Hid5. * exact Hra. * exact Htp. * exact Hal16. * exact Hsp47. * exact Hcal. * exact Hclo. * exact Hchi.
* eapply (obj_at_transport_range _ _ _ _ _ _ 48); [exact Hcfg2 | reflexivity |]; intros i Hi.
mem_back ltac:(rewrite ?HU2, ?HU10, ?Hf53', ?Hq69, ?unsigned_lit_small by lia) ltac:(lia).
* exact HW1. * exact HH1. * exact HWH.
*
change LAY_CGIF with ([(0, 8%N); (8, 8%N); (16, 8%N)] ++ [(24, 8%N)] ++
lay_shift 24 [(8, 8%N); (16, 4%N); (20, 4%N); (24, 2%N); (26, 2%N); (28, 2%N); (30, 2%N); (32, 8%N); (40, 8%N)] ++
[(72, 8%N); (80, 8%N); (88, 4%N); (92, 4%N)]).
change [0; 0; 0; pal0; ubs0_D_str_tmp_out_gif; attr; gen; W; H; ngp; loops; 0; 0; 0; f; 0; 1]
with ([0; 0; 0] ++ [pal0] ++ [ubs0_D_str_tmp_out_gif; attr; gen; W; H; ngp; loops; 0; 0] ++ [0; f; 0; 1]).
rewrite obj_at_app by reflexivity. split.
{ cbn [obj_at]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N].
repeat split;
first [ eapply (st_chunk_zero_val _ _ _ _ 0%nat _ 69%nat 0 24 _ _ 8%nat HS); [reflexivity | reflexivity | cbv; auto 40 | ew_havocA; exact Hq69' | lia | cbn; lia]
| lia ]. }
rewrite obj_at_app by reflexivity. split.
{ cbn [obj_at]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N].
split; [split; [ eapply (st_chunk_val _ _ _ _ 0%nat _ 69%nat 24 8%N (SOff 32 0) _ _ HS);
[reflexivity | reflexivity | cbv; auto 40 | ew_havocA; exact Hq69'
| cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia ]
| cbn; lia ] | exact I]. }
rewrite obj_at_app by reflexivity. split.
{ eapply (st_obj_at _ _ _ _ 0%nat _ 69%nat _ _ _ 33 (tl lits_Config) HS eq_refl eq_refl ltac:(ew_havocA; exact Hq69'));
[ apply incl_chunks_sound; vm_compute; reflexivity | reflexivity | reflexivity | ].
intros j v Hj. cfg_fields_tac Hj HX. }
{ cbn [obj_at]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N].
split; [split; [ eapply (st_chunk_zero_val _ _ _ _ 1%nat _ 69%nat 72 8 _ _ 8%nat HS); [reflexivity | reflexivity | cbv; auto 40 | ew_havocA; exact Hq69' | lia | cbn; lia] | lit_range ] |].
split; [split; [ eapply (st_chunk_val _ _ _ _ 1%nat _ 69%nat 80 8%N (SOff 53 0) _ f HS); [reflexivity | reflexivity | cbv; auto 40 | ew_havocA; exact Hq69' | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, Hf53, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia] | change (2 ^ (8 * 8)) with (2 ^ 64); lia ] |].
split; [split; [ eapply (st_chunk_zero_val _ _ _ _ 1%nat _ 69%nat 88 4 _ _ 4%nat HS); [reflexivity | reflexivity | cbv; auto 40 | ew_havocA; exact Hq69' | lia | cbn; lia] | lit_range ] |].
split; [split; [ eapply (st_chunk_val _ _ _ _ 1%nat _ 69%nat 92 4%N (SLit 1) _ 1 HS); [reflexivity | reflexivity | cbv; auto 40 | ew_havocA; exact Hq69' | reflexivity | lit_range | cbn; lia] | lit_range ] |].
exact I. }
* exact HBc.
* destruct (Z.eqb_spec (Z.land attr 4) 0); [contradiction | reflexivity].
* exact Hgfresh.
* exact Hffresh.
* intros bb Hb. destruct Hb.
* destruct (Z.eqb_spec (Z.land attr 4) 0); [contradiction | reflexivity].
*
apply (sink_at_frame ubs0_msyms mem7 _ md5 f []); [|exact HSK7].
intros a Ha. assert (Ha' : 0 <= a < alloc_ceiling /\ ~ (g <= a < g + 96))
by (destruct Ha as [Ha|Ha]; [lia | pose proof (ubs0_env_addr_range a Ha); pose proof (Henvblk L5 A5 mem5 md5 g CGIF_SIZE a HH5 Hgin5 Ha); lia]).
mem_back ltac:(rewrite ?HU2, ?HU10, ?Hf53', ?Hq69, ?Hq69', ?unsigned_lit_small by lia) ltac:(lia).
* unfold ng_b3. destruct (Z.eqb_spec (Z.land attr 4) 0); [contradiction | exact HR5].
* exact HROOM.
* exact Hpala.
* intros Hz4. exfalso. exact (Hattr4 Hz4).
*
intros i Hi Hn16. fold sp0. destruct (Z_lt_le_dec i 16) as [Hi16|Hi16].
{ replace (sp0 - 80 + i) with (sp0 + (-80) + i) by lia.
eapply (st_chunk_zero _ _ _ 2%nat _ 2%nat (-80) 16 sp0 i HS); [reflexivity | reflexivity | cbv; auto 30 | ew_havocA; exact HU2 | lia]. }
{ replace (sp0 - 80 + i) with (sp0 + (-56) + (i - 24)) by lia.
eapply (st_chunk_zero _ _ _ 2%nat _ 2%nat (-56) 16 sp0 (i - 24) HS); [reflexivity | reflexivity | cbv; auto 30 | ew_havocA; exact HU2 | lia]. }
* fold sp0. replace (sp0 - 64) with (sp0 + (-64)) by lia.
eapply (st_chunk_word _ _ _ 2%nat _ 2%nat (-64) (SOff 32 0) sp0 pal0 HS); [reflexivity | reflexivity | cbv; auto 30 | ew_havocA; exact HU2
| cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | lia].
* frame_wordI HS 3%nat HU2 HE 1%nat (1%bv:reg).
* frame_wordI HS 3%nat HU2 HE 8%nat (8%bv:reg).
* frame_wordI HS 3%nat HU2 HE 9%nat (9%bv:reg).
* frame_wordI HS 3%nat HU2 HE 18%nat (18%bv:reg).
* frame_wordI HS 3%nat HU2 HE 19%nat (19%bv:reg).
* reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
* reg_nowF HS ltac:(rewrite Hq69, unsigned_lit_small by lia; reflexivity).
* reg_nowF HS ltac:(ew_havocA; rewrite Hf53, Z_to_bv_bv_unsigned; reflexivity).
* reg_nowF HS ltac:(rewrite HU10; reflexivity).
* reg_nowF HS ltac:(reflexivity).
* lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
pose proof (st_ok_reg ubs0segs Ec ssc msc 10%bv HS) as R10; eval_sr_get_in R10; cbn [sv_denot] in R10 end.
ew_havocA_in R10. rewrite ?Z.add_0_r, HX34 in R10. rewrite R10, ?Z_to_bv_bv_unsigned, ?unsigned_lit_small by lia. apply Z.mod_small. lia.
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
* intros Hs. exfalso. lia.
* intros _. apply KB1. subst G. unfold g_sgct_ok, g_sgct, newgif_cfg, YO07.flag. cbn [YO07.g_attr YO07.g_ngp].
destruct (Z.eqb_spec (Z.land attr 4) 0); [contradiction | reflexivity].
+
rewrite branch_ne_U, U_and_lit, (U_atom _ 34 attr), U_lit in Hc by first [lia | ew_havocA; exact HX34].
assert (Hattr4 : Z.land attr 4 = 0) by (destruct (Z.eqb_spec (Z.land attr 4) 0); [assumption | discriminate Hc]). clear Hc.
rewrite Hattr4 in HB. cbn [Z.eqb app] in HB.
assert (Hpalin : In (pala, 3 * ngp) (blocks L A)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
destruct (HGP Hattr4) as [HGPa HGPn].
jrun_to LAWS ubs0tbl_ok HS HJ7 ubs0_A_malloc.
{ eapply wr_ok_cons_tmp; [reflexivity | ew_havocA; rewrite Hq69; apply unsigned_lit_small; lia | exact Hgin5 | exact Hgfresh | cbn; lia | cbn; lia |].
eapply wr_ok_cons_tmp; [reflexivity | ew_havocA; rewrite Hq69; apply unsigned_lit_small; lia | exact Hgin5 | exact Hgfresh | cbn; lia | cbn; lia |].
wr_tac3 HU2. }
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
pose proof (st_ok_reg ubs0segs Ec ssc msc 10%bv HS) as Hn10; eval_sr_get_in Hn10;
rewrite (denot_mul3' _ 38 ngp) in Hn10 by first [lia | ew_havocA; exact HX38] end.
jreg HS (2%bv:reg) as Hn2. rewrite HU2 in Hn2. jreg HS (4%bv:reg) as Hn4. rewrite (HE 4%nat 4%bv eq_refl), Htp in Hn4. jreg HS (1%bv:reg) as Hn1.
pose proof (journal_restart ubs0_msyms MR _ _ _ _ _ _ _ _ _ _ _ (@nil (Z * Z)) HJ7) as HJl.
eapply SR_bind.
{ eapply (jmalloc_at_res API IMG) with (n := 3 * ngp) (spc := sp0 - 80) (b := ng_b2 b);
[ exact HS | reflexivity | reflexivity | exact HJl | exact Hid5 | exact Hn10 | exact HR5
| apply (ng_room3 b ngp HROOM); unfold PALMAX; lia
| rewrite Hn2; f_equal; lia | lia | exact Hspm | lia | lia | exact Hn4 | exact Hn1 | apply ret_ok_even; vm_compute; reflexivity ]. }
intros c' (L8 & A8 & regs8 & mem8 & md8 & pal & -> & HJl8 & Hid8 & HP8 & Hp10 & (Hpnz & Hp16 & (b1' & b2' & Hbl8 & Hblc8) & Hwr8) & Hkeep8 & Hhi8 & HR8).
change (ms_segs ubs0_msyms) with ubs0segs in Hkeep8, Hhi8. cbn [ms_regs ms_mem mkst] in HP8, Hkeep8, Hhi8, HJl8, Hp10.
assert (HJ8 : journal ubs0_msyms MR NEWGIF_STK sp0 [sink_token] L A mem md L8 A8 mem8 md8).
{ eapply (journal_sub ubs0_msyms MR); [exact HJ7 | exact HJl8 | lia | lia | intros a (r & [] & _)]. }
assert (HK8 : sink_at ubs0_msyms mem8 md8 f [] /\ In (f, FILE_BLOCK) (blocks L8 A8)).
{ eapply (sink_kept ubs0_msyms MR); [exact HJl8 | intros (r & [] & _) | exact Hfin5 | intros a _ (r & [] & _) |].
apply (sink_at_frame ubs0_msyms mem7 _ md5 f []); [|exact HSK7].
intros a Ha. assert (Ha' : 0 <= a < alloc_ceiling /\ ~ (g <= a < g + 96))
by (destruct Ha as [Ha|Ha]; [lia | pose proof (ubs0_env_addr_range a Ha); pose proof (Henvblk L5 A5 mem5 md5 g CGIF_SIZE a HH5 Hgin5 Ha); lia]).
mem_back ltac:(rewrite ?HU2, ?HU10, ?Hf53', ?Hq69, ?Hq69', ?unsigned_lit_small by lia) ltac:(lia). }
destruct HK8 as [HSK8 Hfin8]. clear HJl HJl8.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ8) as HH8.
assert (Hg8 : In (g, CGIF_SIZE) (blocks L8 A8)).
{ rewrite Hbl8. rewrite Hblc8 in Hgin5. apply in_app_iff in Hgin5. apply in_app_iff. destruct Hgin5 as [H0|H0]; [left; exact H0 | right; right; exact H0]. }
jafter_call_keep HS 98%nat regs8 mem8 HP8 [0%nat; 1%nat; 2%nat; 3%nat; 4%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
- split; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; ew_havocA; rewrite Hq69'; intros a Ha.
+ replace a with (g + (a - g)) by lia. apply (Hkeep8 g CGIF_SIZE (a - g) Hgin5). lia.
+ intros _. apply (present_writable ubs0segs). replace a with (g + (a - g)) by lia.
apply (proj1 (heap_blocks _ _ LAWS L8 A8 mem8 md8 g CGIF_SIZE (a - g) HH8 Hg8 ltac:(lia))).
- split; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; ew_havocA; rewrite Hq69'; intros a Ha.
+ replace a with (g + (a - g)) by lia. apply (Hkeep8 g CGIF_SIZE (a - g) Hgin5). lia.
+ intros _. apply (present_writable ubs0segs). replace a with (g + (a - g)) by lia.
apply (proj1 (heap_blocks _ _ LAWS L8 A8 mem8 md8 g CGIF_SIZE (a - g) HH8 Hg8 ltac:(lia))).
- eapply (region_kept_stack ubs0segs _ _ _ 2); [ew_havocA; exact HU2 | exact Hhi8 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs0segs _ _ _ 2); [ew_havocA; exact HU2 | exact Hhi8 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs0segs _ _ _ 10); [ew_havocA; exact HU10 | exact Hhi8 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jreg HS (10%bv:reg) as Hq102. cbn [ms_regs mkst] in Hq102. rewrite Hp10 in Hq102. symmetry in Hq102.
assert (Hpin : In (pal, 3 * ngp) (blocks L8 A8)) by (rewrite Hbl8; apply in_app_iff; right; left; reflexivity).
destruct (blocks_range _ _ LAWS L8 A8 mem8 md8 pal (3 * ngp) HH8 Hpin) as [Hp0 Hp1].
assert (Hbase8 : forall bb, In bb (blocks L5 A5) -> In bb (blocks L8 A8)).
{ intros bb Hb. rewrite Hbl8. rewrite Hblc8 in Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact Hb | right; right; exact Hb]. }
assert (Hpala8 : In (pala, 3 * ngp) (blocks L8 A8)) by (apply Hbase8; apply Hbase5; eapply Permutation_in; [apply Permutation_sym; exact HB4 | right; exact Hpalin]).
assert (Hsep_gp : g + CGIF_SIZE <= pal \/ pal + 3 * ngp <= g).
{ destruct (heap_sep _ _ LAWS L8 A8 mem8 md8 b1' (pal, 3 * ngp) b2' (g, CGIF_SIZE) HH8 Hbl8 ltac:(rewrite <- Hblc8; exact Hgin5)) as [H0|H0]; cbn [fst snd] in H0; lia. }
assert (Hsep_pp : pal + 3 * ngp <= pala \/ pala + 3 * ngp <= pal).
{ destruct (heap_sep _ _ LAWS L8 A8 mem8 md8 b1' (pal, 3 * ngp) b2' (pala, 3 * ngp) HH8 Hbl8 ltac:(rewrite <- Hblc8; apply Hbase5; eapply Permutation_in; [apply Permutation_sym; exact HB4 | right; exact Hpalin])) as [H0|H0]; cbn [fst snd] in H0; lia. }
assert (Hsep_fp : f + FILE_BLOCK <= pal \/ pal + 3 * ngp <= f).
{ destruct (heap_sep _ _ LAWS L8 A8 mem8 md8 b1' (pal, 3 * ngp) b2' (f, FILE_BLOCK) HH8 Hbl8 ltac:(rewrite <- Hblc8; exact Hfin5)) as [H0|H0]; cbn [fst snd] in H0; lia. }
assert (Hpalfresh5 : ~ In (pal, 3 * ngp) (blocks L5 A5) \/ 3 * ngp <= 0).
{ destruct (Z_lt_le_dec 0 (3 * ngp)) as [Hl|Hl]; [left | right; exact Hl].
rewrite Hblc8. apply (fresh_not_in API L8 A8 mem8 md8 b1' b2' pal (3 * ngp) HH8 Hbl8 Hl). }
add_fact HS 102%nat (mkAF 4096 CEIL_MAX 4).
2:{ rewrite Hq102, unsigned_lit_small by lia. change (2 ^ 4) with 16. lia. }
assert (Hq102' : bv_unsigned (ew (havoc (havoc (havoc (havoc (havoc (havoc E 43 (map (getr regs2) MEMSET_CLOB)) 49 (map (getr regs4) CLOB)) 65 (map (getr regs5) CLOB)) 81 (map (getr regs6) MEMSET_CLOB)) 87 (map (getr regs7) MEMCPY_CLOB)) 98 (map (getr regs8) CLOB)) 102) = pal) by (rewrite Hq102; apply unsigned_lit_small; lia).
jrun_to LAWS ubs0tbl_ok HS HJ8 ubs0_A_memcpy.
{ eapply wr_ok_cons_tmp; [reflexivity | ew_havocA; rewrite Hq69; apply unsigned_lit_small; lia | exact Hg8 | exact Hgfresh | cbn; lia | cbn; lia |].
eapply wr_ok_cons_tmp; [reflexivity | ew_havocA; rewrite Hq69; apply unsigned_lit_small; lia | exact Hg8 | exact Hgfresh | cbn; lia | cbn; lia |].
wr_tac3 HU2. }
jreg HS (10%bv:reg) as Mp0. rewrite Hq102 in Mp0.
jreg HS (11%bv:reg) as Mp1. rewrite HX32, <- Hpala in Mp1.
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
pose proof (st_ok_reg ubs0segs Ec ssc msc 12%bv HS) as Mp2; eval_sr_get_in Mp2;
first [ rewrite (denot_mul3' _ 38 ngp) in Mp2 by first [lia | ew_havocA; exact HX38]
| rewrite (denot_mul3 _ 38 ngp) in Mp2 by first [lia | ew_havocA; exact HX38] ] end.
jreg HS (1%bv:reg) as Mpra.
assert (Hpalafresh : forall i, 0 <= i < 3 * ngp -> ~ inFP [sink_token] (pala + i)).
{ intros i Hi Hin. pose proof (inFP_token _ Hin).
destruct (blocks_range _ _ LAWS L A mem md pala (3 * ngp) HH Hpalin); lia. }
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (HGP8 : YI00.garr8 ubs0segs (ms_mem msx) pala GPAL)
end.
{ eapply YI00.garr8_frame; [exact HGPa|]. intros a Ha. rewrite HGPn in Ha. replace a with (pala + (a - pala)) by lia.
apply (journal_blocks_kept ubs0_msyms MR _ _ _ _ _ _ _ _ _ _ _ HJ8 pala (3 * ngp) (a - pala) Hpalin Hpala8 ltac:(lia)).
apply Hpalafresh. lia. }
eapply SR_bind.
{ eapply (UI4l.jmemcpy_rd API IMG _ ubs0_memcpy) with (d := pal) (src := pala) (n := 3 * ngp);
[ exact HS | reflexivity | reflexivity | exact HJ8 | exact Mp0 | exact Mp1 | exact Mp2 | exact Mpra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | | lia | | | | exact Hsep_pp | ].
- destruct (blocks_range _ _ LAWS L8 A8 mem8 md8 pala (3 * ngp) HH8 Hpala8); lia.
- destruct (blocks_range _ _ LAWS L8 A8 mem8 md8 pala (3 * ngp) HH8 Hpala8); lia.
- intros i Hi. match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
apply (proj1 (heap_blocks _ _ LAWS L8 A8 mem8 md8 pal (3 * ngp) i HH8 Hpin Hi)).
- intros i Hi. apply (present_mbyte ubs0_msyms). match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
apply (proj1 (heap_blocks _ _ LAWS L8 A8 mem8 md8 pala (3 * ngp) i HH8 Hpala8 Hi)).
- intros a Ha. right. right. exists pal, (3 * ngp). split; [exact Hpin|]. split; [| lia].
intros Hin. destruct Hpalfresh5 as [Hnf | Hle]; [| lia]. apply Hnf. apply Hbase5. eapply Permutation_in; [apply Permutation_sym; exact HB4 | right; exact Hin]. }
cbv beta. intros c' (regs9 & mem9 & -> & HJ9 & Hd10''' & Hfr9 & Hout9 & Hgr9 & Hcp9). clear HJ8.
assert (HGP9 : YI00.garr8 ubs0segs mem9 pal GPAL).
{ intros j Hj. destruct (HGP8 j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk. replace (pal + Z.of_nat j + Z.of_nat k) with (pal + (Z.of_nat j + Z.of_nat k)) by lia.
cbn [ms_mem mkst] in Hcp9. rewrite Hcp9 by (cbn in Hk; lia).
replace (pala + (Z.of_nat j + Z.of_nat k)) with (pala + Z.of_nat j + Z.of_nat k) by lia. apply Hv. exact Hk. }
assert (HSK9 : sink_at ubs0_msyms mem9 md8 f []).
{ lazymatch type of Hgr9 with mem_grows ?m0 _ => apply (sink_at_frame ubs0_msyms m0 _ md8 f []) end.
- intros a Ha. assert (Ha' : 0 <= a < alloc_ceiling /\ ~ (pal <= a < pal + 3 * ngp))
by (destruct Ha as [Ha|Ha]; [lia | pose proof (ubs0_env_addr_range a Ha); pose proof (Henvblk L8 A8 mem8 md8 pal (3 * ngp) a HH8 Hpin Ha); lia]).
apply (mbyte_eq_of ubs0_msyms). apply Hout9. rewrite unsigned_lit_small by lia. lia.
- apply (sink_at_frame ubs0_msyms mem8 _ md8 f []); [|exact HSK8].
intros a Ha. assert (Ha' : 0 <= a < alloc_ceiling /\ ~ (g <= a < g + 96))
by (destruct Ha as [Ha|Ha]; [lia | pose proof (ubs0_env_addr_range a Ha); pose proof (Henvblk L5 A5 mem5 md5 g CGIF_SIZE a HH5 Hgin5 Ha); lia]).
mem_back ltac:(rewrite ?HU2, ?HU10, ?Hf53', ?Hq69, ?Hq69', ?Hq102, ?unsigned_lit_small by lia) ltac:(lia). }
jafter_stretch_keep HS 114%nat regs9 mem9 MEMCPY_CLOB NG_PALCPY [0%nat; 1%nat; 2%nat; 3%nat; 4%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr9. exact Hrr. }
{ repeat apply Forall_cons; try apply Forall_nil;
(eapply region_kept_out; [exact Hout9 | exact Hgr9 | cbn [r_base r_lo base_val]; ew_havocA; rewrite ?HU2, ?HU10, ?Hq69'; lia
| cbn [r_base r_hi base_val]; ew_havocA; rewrite ?HU2, ?HU10, ?Hq69'; lia
| cbn [r_base r_lo r_hi base_val]; ew_havocA; rewrite ?HU2, ?HU10, ?Hq69'; intros a Ha; lia | cbn; lia | cbn; lia]). }
clear HS. rename HS2 into HS.
jrun LAWS ubs0tbl_ok HS HJ9.
{ eapply wr_ok_cons_tmp; [reflexivity | ew_havocA; rewrite Hq69; apply unsigned_lit_small; lia | exact Hg8 | exact Hgfresh | cbn; lia | cbn; lia |].
eapply wr_ok_cons_tmp; [reflexivity | ew_havocA; rewrite Hq69; apply unsigned_lit_small; lia | exact Hg8 | exact Hgfresh | cbn; lia | cbn; lia |].
wr_tac3 HU2. }
jbranch ubs0tbl HS.
{ exfalso. rewrite branch_ne_U, U_and_lit, U_lit in Hc by lia.
rewrite land4_mod32, U_SExt, (U_atom _ 34 attr) in Hc by first [lia | ew_havocA; exact HX34].
change (2 ^ Z.of_N 32) with (2 ^ 32) in Hc. rewrite sext32_low in Hc by lia. rewrite Hattr4 in Hc. discriminate Hc. }
jrun_to LAWS ubs0tbl_ok HS HJ9 (ubs0_A_cgif_newgif + 0x11c).
{ eapply wr_ok_cons_tmp; [reflexivity | ew_havocA; rewrite Hq69; apply unsigned_lit_small; lia | exact Hg8 | exact Hgfresh | cbn; lia | cbn; lia |].
eapply wr_ok_cons_tmp; [reflexivity | ew_havocA; rewrite Hq69; apply unsigned_lit_small; lia | exact Hg8 | exact Hgfresh | cbn; lia | cbn; lia |].
wr_tac3 HU2. }
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (newgif_tail_x API IMG AX RAWNEWX L A mem md regs rg L8 A8 mm md8 cfgp pal0 pala attr gen W H ngp loops g pal ngp f [(pal, 3 * ngp)] GPAL b TB) end.
* exact HJ9. * exact Hid8. * exact Hra. * exact Htp. * exact Hal16. * exact Hsp47. * exact Hcal. * exact Hclo. * exact Hchi.
* eapply (obj_at_transport_range _ _ _ _ _ _ 48); [exact Hcfg2 | reflexivity |]; intros i Hi.
mem_back ltac:(rewrite ?HU2, ?HU10, ?Hf53', ?Hq69, ?Hq102, ?unsigned_lit_small by lia) ltac:(lia).
* exact HW1. * exact HH1. * exact HWH.
*
change LAY_CGIF with ([(0, 8%N); (8, 8%N); (16, 8%N)] ++ [(24, 8%N)] ++
lay_shift 24 [(8, 8%N); (16, 4%N); (20, 4%N); (24, 2%N); (26, 2%N); (28, 2%N); (30, 2%N); (32, 8%N); (40, 8%N)] ++
[(72, 8%N); (80, 8%N); (88, 4%N); (92, 4%N)]).
change [0; 0; 0; pal; ubs0_D_str_tmp_out_gif; attr; gen; W; H; ngp; loops; 0; 0; 0; f; 0; 1]
with ([0; 0; 0] ++ [pal] ++ [ubs0_D_str_tmp_out_gif; attr; gen; W; H; ngp; loops; 0; 0] ++ [0; f; 0; 1]).
rewrite obj_at_app by reflexivity. split.
{ cbn [obj_at]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N].
repeat split;
first [ eapply (st_chunk_zero_val _ _ _ _ 0%nat _ 69%nat 0 24 _ _ 8%nat HS); [reflexivity | reflexivity | cbv; auto 40 | ew_havocA; exact Hq69' | lia | cbn; lia]
| lia ]. }
rewrite obj_at_app by reflexivity. split.
{ cbn [obj_at]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N].
split; [split; [ eapply (st_chunk_val _ _ _ _ 0%nat _ 69%nat 24 8%N (SOff 102 0) _ _ HS);
[reflexivity | reflexivity | cbv; auto 40 | ew_havocA; exact Hq69'
| cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, Hq102, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia ]
| cbn; lia ] | exact I]. }
rewrite obj_at_app by reflexivity. split.
{ eapply (st_obj_at _ _ _ _ 0%nat _ 69%nat _ _ _ 33 (tl lits_Config) HS eq_refl eq_refl ltac:(ew_havocA; exact Hq69'));
[ apply incl_chunks_sound; vm_compute; reflexivity | reflexivity | reflexivity | ].
intros j v Hj. cfg_fields_tac Hj HX. }
{ cbn [obj_at]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N].
split; [split; [ eapply (st_chunk_zero_val _ _ _ _ 1%nat _ 69%nat 72 8 _ _ 8%nat HS); [reflexivity | reflexivity | cbv; auto 40 | ew_havocA; exact Hq69' | lia | cbn; lia] | lit_range ] |].
split; [split; [ eapply (st_chunk_val _ _ _ _ 1%nat _ 69%nat 80 8%N (SOff 53 0) _ f HS); [reflexivity | reflexivity | cbv; auto 40 | ew_havocA; exact Hq69' | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, Hf53, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia] | change (2 ^ (8 * 8)) with (2 ^ 64); lia ] |].
split; [split; [ eapply (st_chunk_zero_val _ _ _ _ 1%nat _ 69%nat 88 4 _ _ 4%nat HS); [reflexivity | reflexivity | cbv; auto 40 | ew_havocA; exact Hq69' | lia | cbn; lia] | lit_range ] |].
split; [split; [ eapply (st_chunk_val _ _ _ _ 1%nat _ 69%nat 92 4%N (SLit 1) _ 1 HS); [reflexivity | reflexivity | cbv; auto 40 | ew_havocA; exact Hq69' | reflexivity | lit_range | cbn; lia] | lit_range ] |].
exact I. }
* rewrite Hbl8. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
cbn [app]. eapply Permutation_trans; [| apply perm_swap]. apply perm_skip. rewrite <- Hblc8. exact HBc.
* rewrite Hattr4. reflexivity.
* exact Hgfresh.
* exact Hffresh.
* intros bb [<- | []] Hin. cbn [snd]. destruct Hpalfresh5 as [Hnf | Hle]; [| exact Hle].
exfalso. apply Hnf. apply Hbase5. eapply Permutation_in; [apply Permutation_sym; exact HB4 | right; exact Hin].
* rewrite Hattr4. reflexivity.
*
apply (sink_at_frame ubs0_msyms mem9 _ md8 f []); [|exact HSK9].
intros a Ha. assert (Ha' : 0 <= a < alloc_ceiling /\ ~ (g <= a < g + 96))
by (destruct Ha as [Ha|Ha]; [lia | pose proof (ubs0_env_addr_range a Ha); pose proof (Henvblk L5 A5 mem5 md5 g CGIF_SIZE a HH5 Hgin5 Ha); lia]).
mem_back ltac:(rewrite ?HU2, ?HU10, ?Hf53', ?Hq69, ?Hq69', ?Hq102, ?unsigned_lit_small by lia) ltac:(lia).
* unfold ng_b3. rewrite Hattr4. exact HR8.
* exact HROOM.
* exact Hpala.
* intros _. split; [exact Hpalin|].
lazymatch type of HS with st_ok _ _ _ ?msx =>
assert (FR : forall a, pala <= a < pala + 3 * ngp \/ pal <= a < pal + 3 * ngp -> mbyte ubs0segs (ms_mem msx) a = mbyte ubs0segs mem9 a) end.
{ intros a Ha. assert (Ha' : 0 <= a < alloc_ceiling /\ ~ (g <= a < g + 96)).
{ destruct (blocks_range _ _ LAWS L8 A8 mem8 md8 pala (3 * ngp) HH8 Hpala8).
destruct (heap_sep _ _ LAWS L5 A5 mem5 md5 b1 (g, 96) b2 (pala, 3 * ngp) HH5 Hbl5 ltac:(rewrite <- Hblc5; eapply Permutation_in; [apply Permutation_sym; exact HB4 | right; exact Hpalin])) as [X|X]; cbn [fst snd] in X; lia. }
mem_back ltac:(rewrite ?HU2, ?HU10, ?Hf53', ?Hq69, ?Hq69', ?Hq102, ?unsigned_lit_small by lia) ltac:(lia). }
split; [| split; [exact HGPn|]].
-- eapply YI00.garr8_frame.
++ eapply YI00.garr8_frame; [exact HGP8|]. intros a Ha. rewrite HGPn in Ha. cbn [ms_mem mkst] in Hout9 |- *.
destruct (blocks_range _ _ LAWS L8 A8 mem8 md8 pala (3 * ngp) HH8 Hpala8).
apply (mbyte_eq_of ubs0_msyms). apply Hout9. rewrite unsigned_lit_small by lia. lia.
++ intros a Ha. rewrite HGPn in Ha. apply FR. left. exact Ha.
-- eapply YI00.garr8_frame; [exact HGP9|]. intros a Ha. rewrite HGPn in Ha. apply FR. right. exact Ha.
*
intros i Hi Hn16. fold sp0. destruct (Z_lt_le_dec i 16) as [Hi16|Hi16].
{ replace (sp0 - 80 + i) with (sp0 + (-80) + i) by lia.
eapply (st_chunk_zero _ _ _ 2%nat _ 2%nat (-80) 16 sp0 i HS); [reflexivity | reflexivity | cbv; auto 30 | ew_havocA; exact HU2 | lia]. }
{ replace (sp0 - 80 + i) with (sp0 + (-56) + (i - 24)) by lia.
eapply (st_chunk_zero _ _ _ 2%nat _ 2%nat (-56) 16 sp0 (i - 24) HS); [reflexivity | reflexivity | cbv; auto 30 | ew_havocA; exact HU2 | lia]. }
* fold sp0. replace (sp0 - 64) with (sp0 + (-64)) by lia.
eapply (st_chunk_word _ _ _ 2%nat _ 2%nat (-64) (SOff 32 0) sp0 pal0 HS); [reflexivity | reflexivity | cbv; auto 30 | ew_havocA; exact HU2
| cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | lia].
* frame_wordI HS 3%nat HU2 HE 1%nat (1%bv:reg).
* frame_wordI HS 3%nat HU2 HE 8%nat (8%bv:reg).
* frame_wordI HS 3%nat HU2 HE 9%nat (9%bv:reg).
* frame_wordI HS 3%nat HU2 HE 18%nat (18%bv:reg).
* frame_wordI HS 3%nat HU2 HE 19%nat (19%bv:reg).
* reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
* reg_nowF HS ltac:(rewrite Hq69, unsigned_lit_small by lia; reflexivity).
* reg_nowF HS ltac:(ew_havocA; rewrite Hf53, Z_to_bv_bv_unsigned; reflexivity).
* reg_nowF HS ltac:(rewrite HU10; reflexivity).
* reg_nowF HS ltac:(ew_havocA; rewrite HX38, Z_to_bv_bv_unsigned; reflexivity).
* lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
pose proof (st_ok_reg ubs0segs Ec ssc msc 10%bv HS) as R10; eval_sr_get_in R10 end.
rewrite R10. change (bv_unsigned (sv_denot ?E1 ?e)) with (U E1 e). rewrite U_SExt, (U_atom _ 34 attr) by first [lia | ew_havocA; exact HX34].
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite sext32_low by lia. reflexivity.
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
* intros Hs. apply KB0. subst G. unfold g_sgct_ok, g_sgct, newgif_cfg, YO07.flag. cbn [YO07.g_attr YO07.g_ngp].
rewrite Hattr4. cbn [Z.eqb negb]. destruct (Z.ltb_spec 256 ngp); [reflexivity | lia].
* intros Hs. apply KB1. subst G. unfold g_sgct_ok, g_sgct, newgif_cfg, YO07.flag. cbn [YO07.g_attr YO07.g_ngp].
rewrite Hattr4. cbn [Z.eqb negb]. destruct (Z.ltb_spec 256 ngp); [lia | reflexivity].
Qed.
Theorem ubs0_newgif_x : newgif_x API.
Proof using AX IMG MG RAWNEWX. exact ubs0_cgif_newgif_x. Qed.
End S.
End h.
