(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open ReadWrite.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s YK0p YP0n YP0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP0h YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d
YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YL01 YN03.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b UN3c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI06 YI09 YI16 YI00 YI14 YI07 YI19 YI05 YI18 YI1a YI15 YI0r YI0o UI5b UI5c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UN3j UN37.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition FO_DEPTH : Z := 256.
Definition reg_fo_stack : YP09.region := YP09.mkRegion (Some 2%nat) (-FO_DEPTH) 0 (-FO_DEPTH) 0 [].
Definition reg_fo_errno : YP09.region := YP09.mkRegion (Some 4%nat) (-164) (-160) (-164) (-160) [].
Definition RWA_WORD : Z := 0x7665642f00617772.
Definition HIGHS_WORD : Z := 0x8080808080808080.
Definition ONES_WORD : Z := 0x0101010101010100.
Definition reg_rwa : YP09.region :=
YP09.mkRegion None ubs0_D_str_rwa (ubs0_D_str_rwa + 8) 0 0 [mkChunk ubs0_D_str_rwa (CVal 8 (SLit RWA_WORD))].
Definition reg_wb : YP09.region :=
YP09.mkRegion None ubs0_D_str_wb (ubs0_D_str_wb + 3) 0 0
[mkChunk ubs0_D_str_wb (CVal 1 (SLit 119)); mkChunk (ubs0_D_str_wb + 1) (CVal 1 (SLit 98)); mkChunk (ubs0_D_str_wb + 2) (CVal 1 (SLit 0))].
Definition reg_highs : YP09.region :=
YP09.mkRegion None ubs0_D_const_HIGHS_0x8080808080808080 (ubs0_D_const_HIGHS_0x8080808080808080 + 8) 0 0
[mkChunk ubs0_D_const_HIGHS_0x8080808080808080 (CVal 8 (SLit HIGHS_WORD))].
Definition reg_ones : YP09.region :=
YP09.mkRegion None ubs0_D_const_ONES_0x0101010101010100 (ubs0_D_const_ONES_0x0101010101010100 + 8) 0 0
[mkChunk ubs0_D_const_ONES_0x0101010101010100 (CVal 8 (SLit ONES_WORD))].
Definition reg_threaded : YP09.region :=
YP09.mkRegion None (ubs0_D_libc + 1) (ubs0_D_libc + 2) 0 0 [mkChunk (ubs0_D_libc + 1) (CVal 1 (SLit 0))].
Definition reg_needlocks : YP09.region :=
YP09.mkRegion None (ubs0_D_libc + 3) (ubs0_D_libc + 4) 0 0 [mkChunk (ubs0_D_libc + 3) (CVal 1 (SLit 0))].
Definition reg_ofl_lock : YP09.region :=
YP09.mkRegion None ubs0_D_ofl_lock (ubs0_D_ofl_lock + 4) 0 0 [mkChunk ubs0_D_ofl_lock (CVal 4 (SLit 0))].
Definition reg_ofl_head0 : YP09.region :=
YP09.mkRegion None ubs0_D_ofl_head (ubs0_D_ofl_head + 8) ubs0_D_ofl_head (ubs0_D_ofl_head + 8) [mkChunk ubs0_D_ofl_head (CVal 8 (SLit 0))].
Definition fo_facts : list (nat * afact) := [ (2%nat, mkAF (CEIL_MIN + FOPEN_STK) (2^47) 4) ].
Definition ss_fo : sstate :=
mkSS ubs0_A_fopen (sr_set (sr_set sr_atoms 10%bv (SLit ubs0_D_str_tmp_out_gif)) 11%bv (SLit ubs0_D_str_wb))
[ reg_fo_stack; reg_fo_errno; reg_rwa; reg_wb; reg_highs; reg_ones; reg_got; reg_guard; reg_threaded; reg_needlocks; reg_ofl_lock; reg_ofl_head0 ] None
(mkFacts fo_facts [] []).
Definition reg_guard32 : YP09.region :=
YP09.mkRegion None ubs0_D_stack_chk_guard (ubs0_D_stack_chk_guard + 8) 0 0 [mkChunk ubs0_D_stack_chk_guard (CVal 8 (SOff 32%nat 0))].
Definition ss_fo0 : sstate :=
mkSS ubs0_A_fopen (sr_set (sr_set sr_atoms 10%bv (SLit ubs0_D_str_tmp_out_gif)) 11%bv (SLit ubs0_D_str_wb))
[ reg_fo_stack; reg_fo_errno; reg_rwa; reg_wb; reg_highs; reg_ones; reg_got; reg_guard32; reg_threaded; reg_needlocks; reg_ofl_lock; reg_ofl_head0 ] None
(mkFacts fo_facts [] []).
Ltac add_region HS r :=
lazymatch type of HS with st_ok ?segs ?E1 ?ss1 ?ms1 =>
apply (st_ok_add_region' segs E1 ss1 ms1 r) in HS;
[ match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end
| vm_compute; reflexivity | | ]
end.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma ubs0_memset_spec_f : memset_spec ubs0_msyms ubs0_A_memset.
Proof using. exact ubs0_memset. Qed.
Lemma val_mem_of_garr8 : forall (mem : word -> option byte) a l v, garr8 ubs0segs mem a l ->
(forall k, (k < length l)%nat -> le_byte v (length l) k = nth k l 0) -> val_mem ubs0segs mem a (length l) v.
Proof using. intros mem a l v HG Hle k Hk. rewrite (garr8_mbyte _ mem a l k HG Hk), <- (Hle k Hk). reflexivity. Qed.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis AX : AllocExtra ubs0_msyms MR.
Hypothesis MG : malloc_realizes_g ubs0_msyms MR.
Theorem ubs0_fopenX : fopen_x ubs0_msyms MR ubs0_A_fopen.
Proof using AX IMG LAWS MG.
intros L A regs mem md b TA TB HPRE Hinit Hsp47 H10 H11 HSN HRb HRm Hfree0 KA KB.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HSTKv : FOPEN_STK = 512 + ALLOC_STACK) by reflexivity. assert (HAS : ALLOC_STACK = 8192) by reflexivity.
assert (HFB : FILE_BLOCK = 1264) by reflexivity. assert (HBO : FILE_BUF_OFF = 240) by reflexivity.
assert (HBS : FILE_BUFSIZ = 1024) by reflexivity. assert (HU : U32M1 = 4294967295) by reflexivity. assert (HFH : FILE_HDR = 232) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
assert (Htpn : ms_tp ubs0_msyms = 199344) by reflexivity.
assert (Heav : errno_addr ubs0_msyms = 199180) by reflexivity.
assert (Htpv : bv_unsigned (Z_to_bv 64 (ms_tp ubs0_msyms)) = 199344) by (vm_compute; reflexivity).
destruct HSN as (Henv & Hhead & Hfdn).
pose proof Henv as (Hthr & Hlock & Hpath & Hmode & Htrl & Hrwa & Hhighs & Hones).
destruct (ax_statics AX L A mem md (proj1 HH)) as (Hgot & (g & Hg0 & Hguard) & Hnl).
assert (Hspw : bv_unsigned (getr regs 2) = spZ regs) by reflexivity.
assert (Htok : sink_open_fp [sink_token]) by (apply sink_open_token; left; reflexivity).
remember (Ereg regs [Z_to_bv 64 g]) as E0 eqn:HE0.
assert (HA0 : env_agree 32 (Ereg regs [Z_to_bv 64 g]) E0) by (rewrite HE0; apply env_agree_refl).
assert (HE2 : ew E0 2 = getr regs 2) by (subst E0; apply (ew_Ereg_nat regs _ 2 2%bv); vm_compute; reflexivity).
assert (HE1 : ew E0 1 = getr regs 1) by (subst E0; apply (ew_Ereg_nat regs _ 1 1%bv); vm_compute; reflexivity).
assert (HE4 : ew E0 4 = Z_to_bv 64 (ms_tp ubs0_msyms)) by (subst E0; rewrite (ew_Ereg_nat regs _ 4 4%bv) by (vm_compute; reflexivity); exact Htp).
assert (HE10 : ew E0 10 = Z_to_bv 64 sk_path_addr) by (subst E0; rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity); exact H10).
assert (HE11 : ew E0 11 = Z_to_bv 64 sk_mode_addr) by (subst E0; rewrite (ew_Ereg_nat regs _ 11 11%bv) by (vm_compute; reflexivity); exact H11).
assert (HE32 : ew E0 32 = Z_to_bv 64 g) by (subst E0; rewrite (ew_Ereg_extra regs _ 0); reflexivity).
set (ms0 := mkst regs (Z_to_bv 64 ubs0_A_fopen) mem (seg_rom ubs0segs)).
pose proof (journal_init ubs0_msyms MR FOPEN_STK [sink_token] L A regs mem md HPRE) as HJ.
change mem with (ms_mem ms0) in HJ.
assert (Hhw : forall (m : word -> option byte) a, 332136 <= a < 332144 -> writable_at ubs0segs m a).
{ intros m a Ha.
assert (Hc : a = 332136 \/ a = 332137 \/ a = 332138 \/ a = 332139 \/ a = 332140 \/ a = 332141 \/ a = 332142 \/ a = 332143) by lia.
unfold writable_at, wview.
destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]];
(match goal with |- match m ?x with _ => _ end <> None => destruct (m x); [discriminate | (first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])] end). }
assert (Hgb : forall a l j a', garr8 ubs0segs mem a l -> (j < length l)%nat -> a' = a + Z.of_nat j -> val_mem ubs0segs mem a' 1 (nth j l 0)).
{ intros a l j a' HG Hj ->. exact (proj1 (HG j Hj)). }
assert (HS : st_ok ubs0segs E0 ss_fo0 ms0).
{ rewrite HE0. apply entry_st_ok_full; rewrite <- ?HE0.
- apply regs_ok_pin; [apply regs_ok_pin; [rewrite HE0; apply regs_ok_Ereg | reflexivity | exact H10] | reflexivity | exact H11].
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]]]]]]]].
+ apply (region_ok_stack ubs0segs _ mem 2 (spZ regs)); [| unfold FO_DEPTH; lia | lia | intros a Ha; apply Hstw; unfold FO_DEPTH in Ha; lia].
rewrite HE2. exact Hspw.
+ unfold region_ok, reg_fo_errno. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HE4, Htpv.
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply Herr. rewrite Heav. lia.
+ unfold region_ok, reg_rwa. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [intros o Ho; lia|].
constructor; [|constructor].
eapply (chunk_ok_val ubs0segs E0 mem 0 ubs0_D_str_rwa 8 (SLit RWA_WORD) RWA_WORD); [reflexivity | vm_compute; split; congruence | vm_compute; congruence | ].
apply (val_mem_of_garr8 mem _ sink_rwa_Z RWA_WORD Hrwa). intros k Hk. do 8 (destruct k as [|k]; [reflexivity|]). cbn in Hk. lia.
+ unfold region_ok, reg_wb. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor]]].
* eapply (chunk_ok_val ubs0segs E0 mem 0 ubs0_D_str_wb 1 (SLit 119) 119); [reflexivity | vm_compute; split; congruence | vm_compute; congruence | ].
exact (Hgb _ _ 0%nat _ Hmode ltac:(cbn; lia) eq_refl).
* eapply (chunk_ok_val ubs0segs E0 mem 0 (ubs0_D_str_wb + 1) 1 (SLit 98) 98); [reflexivity | vm_compute; split; congruence | vm_compute; congruence | ].
exact (Hgb _ _ 1%nat _ Hmode ltac:(cbn; lia) eq_refl).
* eapply (chunk_ok_val ubs0segs E0 mem 0 (ubs0_D_str_wb + 2) 1 (SLit 0) 0); [reflexivity | vm_compute; split; congruence | vm_compute; congruence | ].
exact (Hgb _ _ 2%nat _ Hmode ltac:(cbn; lia) eq_refl).
+ unfold region_ok, reg_highs. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [intros o Ho; lia|].
constructor; [|constructor].
eapply (chunk_ok_val ubs0segs E0 mem 0 ubs0_D_const_HIGHS_0x8080808080808080 8 (SLit HIGHS_WORD) HIGHS_WORD); [reflexivity | vm_compute; split; congruence | vm_compute; congruence | ].
apply (val_mem_of_garr8 mem _ sink_highs_Z HIGHS_WORD Hhighs). intros k Hk. do 8 (destruct k as [|k]; [reflexivity|]). cbn in Hk. lia.
+ unfold region_ok, reg_ones. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [intros o Ho; lia|].
constructor; [|constructor].
eapply (chunk_ok_val ubs0segs E0 mem 0 ubs0_D_const_ONES_0x0101010101010100 8 (SLit ONES_WORD) ONES_WORD); [reflexivity | vm_compute; split; congruence | vm_compute; congruence | ].
apply (val_mem_of_garr8 mem _ sink_ones_Z ONES_WORD Hones). intros k Hk. do 8 (destruct k as [|k]; [reflexivity|]). cbn in Hk. lia.
+ unfold region_ok, reg_got. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [intros o Ho; lia|].
constructor; [|constructor].
eapply (chunk_ok_val ubs0segs E0 mem 0 ubs0_D_got_stack_chk_guard 8 (SLit ubs0_D_stack_chk_guard) ubs0_D_stack_chk_guard);
[reflexivity | vm_compute; split; congruence | vm_compute; congruence | ].
apply (val_mem_word_mem ubs0segs). exact Hgot.
+ unfold region_ok, reg_guard32. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [intros o Ho; lia|].
constructor; [|constructor].
eapply (chunk_ok_val ubs0segs E0 mem 0 ubs0_D_stack_chk_guard 8 (SOff 32%nat 0) g);
[cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact HE32 | change (8 * Z.of_N 8) with 64; exact Hg0 | vm_compute; congruence | ].
apply (val_mem_word_mem ubs0segs). exact Hguard.
+ unfold region_ok, reg_threaded. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [intros o Ho; lia|].
constructor; [|constructor].
eapply (chunk_ok_val ubs0segs E0 mem 0 (ubs0_D_libc + 1) 1 (SLit 0) 0); [reflexivity | vm_compute; split; congruence | vm_compute; congruence | exact Hthr].
+ unfold region_ok, reg_needlocks. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [intros o Ho; lia|].
constructor; [|constructor].
eapply (chunk_ok_val ubs0segs E0 mem 0 (ubs0_D_libc + 3) 1 (SLit 0) 0); [reflexivity | vm_compute; split; congruence | vm_compute; congruence | ].
intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite !Z.add_0_r. exact Hnl.
+ unfold region_ok, reg_ofl_lock. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [intros o Ho; lia|].
constructor; [|constructor].
eapply (chunk_ok_val ubs0segs E0 mem 0 ubs0_D_ofl_lock 4 (SLit 0) 0); [reflexivity | vm_compute; split; congruence | vm_compute; congruence | exact Hlock].
+ unfold region_ok, reg_ofl_head0. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|].
split; [intros o Ho; apply Hhw; change ubs0_D_ofl_head with 332136 in Ho; lia|].
constructor; [|constructor].
eapply (chunk_ok_val ubs0segs E0 mem 0 ubs0_D_ofl_head 8 (SLit 0) 0); [reflexivity | vm_compute; split; congruence | vm_compute; congruence | ].
apply (val_mem_word_mem ubs0segs). exact Hhead.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, reg_fo_stack, reg_fo_errno, reg_rwa, reg_wb, reg_highs, reg_ones, reg_got, reg_guard32,
reg_threaded, reg_needlocks, reg_ofl_lock, reg_ofl_head0.
cbn [r_base r_lo r_hi base_val]. rewrite HE2, HE4, Hspw, Htpv.
change ubs0_D_got_stack_chk_guard with 128824. change ubs0_D_stack_chk_guard with 331032. change ubs0_D_libc with 331064.
change ubs0_D_ofl_lock with 332128. change ubs0_D_ofl_head with 332136. change ubs0_D_str_rwa with 66448. change ubs0_D_str_wb with 66210.
change ubs0_D_const_HIGHS_0x8080808080808080 with 66488. change ubs0_D_const_ONES_0x0101010101010100 with 66504. unfold FO_DEPTH.
repeat split; lia.
- split; [|split; [exact I|exact I]].
cbn [f_atoms atoms_ok fo_facts app]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE2, Hspw. change (2 ^ 4) with 16. repeat split; lia. }
assert (Hwr0 : forall E' blc cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11, ew E' 2 = getr regs 2 -> ew E' 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
wr_okE ubs0_msyms E' [YP09.mkRegion (Some 2%nat) (-256) 0 (-256) 0 cs0; YP09.mkRegion (Some 4%nat) (-164) (-160) (-164) (-160) cs1;
YP09.mkRegion None 66448 66456 0 0 cs2; YP09.mkRegion None 66210 66213 0 0 cs3;
YP09.mkRegion None 66488 66496 0 0 cs4; YP09.mkRegion None 66504 66512 0 0 cs5;
YP09.mkRegion None 128824 128832 0 0 cs6; YP09.mkRegion None 331032 331040 0 0 cs7;
YP09.mkRegion None 331065 331066 0 0 cs8; YP09.mkRegion None 331067 331068 0 0 cs9;
YP09.mkRegion None 332128 332132 0 0 cs10; YP09.mkRegion None 332136 332144 332136 332144 cs11]
FOPEN_STK (spZ regs) [sink_token] (blocks L A) blc).
{ intros E' blc cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 HE2' HE4'.
apply wr_okE_cons_ok; [eapply wr_ok_cons_stack; [reflexivity | rewrite HE2'; exact Hspw | cbn; lia | cbn; lia | apply wr_ok_nil]|].
eapply wr_okE_cons_errno; [reflexivity | rewrite HE4'; exact Htpv | cbn; lia | cbn; lia | ].
do 9 (apply wr_okE_cons_ok; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|]).
apply wr_okE_cons_head; [reflexivity | exact Htok | cbn [r_wlo]; change sk_ofl_head with 332136; lia | cbn [r_whi]; change sk_ofl_head with 332136; lia | apply wr_okE_nil]. }
assert (HfrK : forall E' cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 (m m' : word -> option byte), ew E' 2 = getr regs 2 -> ew E' 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
frame_of E' [YP09.mkRegion (Some 2%nat) (-256) 0 (-256) 0 cs0; YP09.mkRegion (Some 4%nat) (-164) (-160) (-164) (-160) cs1;
YP09.mkRegion None 66448 66456 0 0 cs2; YP09.mkRegion None 66210 66213 0 0 cs3;
YP09.mkRegion None 66488 66496 0 0 cs4; YP09.mkRegion None 66504 66512 0 0 cs5;
YP09.mkRegion None 128824 128832 0 0 cs6; YP09.mkRegion None 331032 331040 0 0 cs7;
YP09.mkRegion None 331065 331066 0 0 cs8; YP09.mkRegion None 331067 331068 0 0 cs9;
YP09.mkRegion None 332128 332132 0 0 cs10; YP09.mkRegion None 332136 332144 332136 332144 cs11] m m' ->
forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 256 <= a < spZ regs) -> ~ (199180 <= a < 199184) -> ~ (332136 <= a < 332144) ->
mbyte ubs0segs m' a = mbyte ubs0segs m a).
{ intros E' cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 m m' HE2' HE4' HF' a Ha Hns Hne Hnh. unfold mbyte. rewrite (HF' (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. intros (r & Hin & Hr).
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]; cbn [r_base r_wlo r_whi base_val] in Hr;
rewrite ?HE2', ?HE4', ?Hspw, ?Htpv in Hr by lia; lia. }
assert (Henva : forall a, env_addr a -> 0 <= a < alloc_ceiling /\ ~ (199180 <= a < 199184)).
{ intros a Ha. pose proof (ubs0_env_addr_range a Ha). unfold env_addr in Ha.
change sk_ofl_head with 0x51168 in Ha. change sk_threaded with (0x50d38 + 1) in Ha.
change sk_path_addr with 0x10304 in Ha. change sk_mode_addr with 0x102a2 in Ha. change sk_trailer_addr with 0x10311 in Ha. change sk_ofl_lock with 0x51160 in Ha.
change sk_rwa_addr with 0x10390 in Ha. change sk_highs_addr with 0x103b8 in Ha. change sk_ones_addr with 0x103c8 in Ha. lia. }
apply realizes_via_SR.
jrunE LAWS ubs0tbl_ok HS HJ.
{ wr_normE. apply Hwr0; [exact HE2 | exact HE4]. }
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
sym_ecall_open HS.
lazymatch type of HF with frame_of _ _ _ (ms_mem (pend_at ?r ?p ?m ?ro)) => change (ms_mem (pend_at r p m ro)) with m in HF, HJ end.
unfold ms0 in HF, HJ, HG; cbn [ms_mem mkst] in HF, HJ, HG.
pose proof (HfrK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HE2 HE4 HF) as Hfr1.
assert (Henv0 : stdio_env ubs0_msyms mem0) by exact (ubs0_stdio_env_kept _ _ _ (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HJ))))))) Henv).
apply SR_ret. apply (JX_openat_node ubs0_msyms MR LAWS regs0 _ mem0 _ _ _ _ _ _ _ _ _ _ TA TB HJ Htok Henv0 Hfree0).
{ rewrite (Hregs 17%bv). eval_sr_get. reflexivity. }
{ rewrite (Hregs 10%bv). eval_sr_get. apply bv_eq. vm_compute. reflexivity. }
{ rewrite (Hregs 12%bv). eval_sr_get. vm_compute. reflexivity. }
{ rewrite (Hregs 11%bv). eval_sr_get. reflexivity. }
-
intros e He. pose (md' := md). pose proof (HJ : journal _ _ _ _ _ _ _ _ _ _ _ _ md') as HJ'.
assert (Hfds' : m_fds md' = m_fds md) by reflexivity. assert (Hfs' : m_fs md' = m_fs md) by reflexivity.
apply realizes_via_SR. cbn [ss_pc].
pose proof (open_tmp_errnos_range e He) as Her. pose proof (errno_ret_unsigned e Her) as Heu.
resume_atom_sr ubs0segs 33%nat (mkAF (2 ^ 64 - 4095) (2 ^ 64 - 1) 0).
{ cbn [af_lo af_hi]. rewrite Heu. lia. }
{ cbn [af_al2]. lia. }
{ cbn [af_al2]. change (2 ^ 0) with 1. apply Z.mod_1_r. }
jrunE LAWS ubs0tbl_ok HS HJ'.
{ wr_normE. apply Hwr0; (rewrite ew_ewset_other by lia); [exact HE2 | exact HE4]. }
assert (HA33 : env_agree 32 (Ereg regs [Z_to_bv 64 g]) (ewset E0 33 (errno_ret e))) by (eapply env_agree_trans; [exact HA0 | apply (YI04.env_agree_le 33 32); [lia | apply env_agree_ewset]]).
pose proof (regs_preserved_of_st_ok _ _ _ _ _ _ HS HA33 ltac:(vm_compute; reflexivity)) as HPR.
jreg HS (1%bv:reg) as Hr1. jreg HS (10%bv:reg) as Hr10.
pose proof (mem_ok_region _ _ _ _ _ (st_ok_mem_ok _ _ _ _ HS) ltac:(do 11 right; left; reflexivity)) as (_ & _ & _ & Hcsh).
cbn [r_base r_chunks base_val] in Hcsh.
lazymatch type of HS with st_ok _ _ _ ?msF =>
assert (Hhead0 : val_mem ubs0segs (ms_mem msF) 332136 8 0)
by (inversion Hcsh as [|c cs Hc0 _]; subst;
exact (val_of_chunk_ok ubs0segs _ _ 0 332136 8 (SLit 0) 0 Hc0 eq_refl ltac:(vm_compute; split; congruence) ltac:(vm_compute; congruence))) end.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ')) as (Hh' & Hlz' & _).
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | exact Hh' | exact Hlz' | exact HS | reflexivity | vm_compute; reflexivity |].
apply KA. lazymatch type of HS with st_ok _ _ _ ?msF => exists L, A, (ms_regs msF), (ms_mem msF), md' end.
rewrite Hr1, (ew_ewset_other E0 33 _ 1 ltac:(lia)), HE1, Hra.
split; [reflexivity|]. split; [exact HJ'|]. split; [exact HPR|]. split; [exact Hinit|]. split; [exact Hr10|].
split; [apply Permutation_refl|]. split; [|split; [exact Hfds'| split; [exact Hfs' | exact HRb]]].
split; [exact (ubs0_stdio_env_kept _ _ _ (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HJ'))))))) Henv)|].
split; [apply (val_mem_word_mem ubs0segs); exact Hhead0 | rewrite Hfds'; exact Hfdn].
-
intros fd md' HJ' Hfdr Hfree Hfds' Hfs'. apply realizes_via_SR. cbn [ss_pc].
assert (Hnr : forall fds (w : word), fd_names_path fds sink_path = false -> fd_names_path (fd_remove fds w) sink_path = false).
{ clear. intros fds w. unfold fd_remove. induction fds as [|[k x] r IH]; [reflexivity|]. cbn [List.filter fst].
intros H. destruct (negb (bv_eqb k w)).
- cbn [fd_names_path]. destruct x; cbn [fd_names_path] in H |- *;
try (apply Bool.orb_false_iff in H as [H1 H2]; rewrite H1; cbn [orb]); auto.
- apply IH. destruct x; cbn [fd_names_path] in H; try (apply Bool.orb_false_iff in H as [H1 H2]); auto. }
assert (Hos1 : sink_os md' fd []).
{ split; [rewrite Hfs'; apply fs_lookup_set_eq|]. split.
- rewrite Hfds'. unfold fd_insert. cbn [fd_lookup fst]. rewrite (proj2 (bv_eqb_eq _ _) eq_refl). reflexivity.
- rewrite Hfds', fd_remove_insert. apply Hnr. exact Hfdn. }
resume_atom_sr ubs0segs 33%nat (mkAF 0 4096 0).
{ cbn [af_lo af_hi]. rewrite unsigned_lit_small by lia. lia. }
{ cbn [af_al2]. lia. }
{ cbn [af_al2]. change (2 ^ 0) with 1. apply Z.mod_1_r. }
assert (HE33 : ew (ewset E0 33 (Z_to_bv 64 fd)) 33 = Z_to_bv 64 fd) by apply ew_ewset_same.
remember (ewset E0 33 (Z_to_bv 64 fd)) as E1 eqn:HE1d.
assert (HA1 : env_agree 32 (Ereg regs [Z_to_bv 64 g]) E1) by (rewrite HE1d; eapply env_agree_trans; [exact HA0 | apply (YI04.env_agree_le 33 32); [lia | apply env_agree_ewset]]).
assert (HE2' : ew E1 2 = getr regs 2) by (rewrite HE1d, ew_ewset_other by lia; exact HE2).
assert (HE1' : ew E1 1 = getr regs 1) by (rewrite HE1d, ew_ewset_other by lia; exact HE1).
assert (HE4' : ew E1 4 = Z_to_bv 64 (ms_tp ubs0_msyms)) by (rewrite HE1d, ew_ewset_other by lia; exact HE4).
assert (HE32' : ew E1 32 = Z_to_bv 64 g) by (rewrite HE1d, ew_ewset_other by lia; exact HE32).
clear HE0 HA0.
jrunE_to LAWS ubs0tbl_ok HS HJ' ubs0_A_malloc.
{ wr_normE. apply Hwr0; [exact HE2' | exact HE4']. }
(jreg HS (10%bv:reg) as M10); (jreg HS (2%bv:reg) as M2); (jreg HS (4%bv:reg) as M4); (jreg HS (1%bv:reg) as M1).
rewrite HE4' in M4. cbn [ms_mem mkst] in HF0.
pose proof (mem_ok_region _ _ _ _ _ (st_ok_mem_ok _ _ _ _ HS) ltac:(do 7 right; left; reflexivity)) as (_ & _ & _ & Hcg).
cbn [r_base r_chunks base_val] in Hcg.
lazymatch type of HS with st_ok _ _ _ ?msM =>
assert (Hgm : word_mem ubs0segs (ms_mem msM) ubs0_D_stack_chk_guard g)
by (inversion Hcg as [|c cs Hc0 _]; subst; apply (val_mem_word_mem ubs0segs);
exact (val_of_chunk_ok ubs0segs _ _ 0 ubs0_D_stack_chk_guard 8 (SOff 32%nat 0) g Hc0
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact HE32') ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(vm_compute; congruence))) end.
clear Hcg.
eapply SR_bind.
{ eapply (jmalloc_sub_g_res ubs0_msyms MR LAWS ubs0_errno_low_f IMG MG) with (n := 1264) (o := -96) (b := b);
[ exact HS | reflexivity | reflexivity | exact HJ' | exact Hinit | exact M10 | lia | exact HRb | exact HRm
| exact M2 | exact HE2' | exact Hspw | reflexivity | lia | lia | exact M4 | reflexivity | exact M1 | apply ret_ok_even; vm_compute; reflexivity | exact Hgm ]. }
clear M10 M2 M4 M1.
cbv beta. intros c' (L1 & A1 & regs1 & mem1 & md1 & p & -> & HJ1 & HJin & Hid1 & HP1 & Hr10 & Hres & Hkeep1 & Hhi1 & HRES1 & Hg1).
cbn [ms_regs ms_mem mkst] in HP1, Hr10, Hkeep1, Hhi1, HJ1, HJin, Hg1.
change (ms_segs ubs0_msyms) with ubs0segs in Hkeep1, Hhi1, Hg1.
assert (Hntok0 : ~ sink_open_fp (@nil (Z * Z))) by (intros (r & [] & _)).
destruct (os_step_shielded _ _ _ (proj1 (proj2 HJin)) Hntok0) as (Efd1 & Efs1 & _).
assert (Hos2 : sink_os md1 fd []) by (unfold sink_os; rewrite Efd1, Efs1; exact Hos1).
jafter_call2 HS 34%nat regs1 mem1 HP1 (-96) [1%nat; 2%nat; 3%nat; 4%nat; 5%nat; 6%nat; 7%nat; 8%nat; 9%nat; 10%nat] HS2.
assert (HimgK : forall a, env_addr a -> mbyte ubs0segs mem1 a = mbyte ubs0segs (ms_mem ms) a /\ (writable_at ubs0segs (ms_mem ms) a <-> writable_at ubs0segs mem1 a)).
{ intros a Ha. destruct (skl_env ubs0_msyms a Ha) as (T1 & T2 & T3 & T4).
apply (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HJin)))))) a T1 T2 T3 T4). intros [Ho _]. exact (Hntok0 Ho). }
assert (HrkA : forall lo hi wlo whi cs, (forall a, lo <= a < hi -> env_addr a) -> wlo = lo \/ whi <= wlo -> whi <= hi ->
region_kept ubs0segs E1 (ms_mem ms) mem1 (YP09.mkRegion None lo hi wlo whi cs)).
{ intros lo hi wlo whi cs Henv' Hw1 Hw2. split; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; intros a Ha.
- apply (proj1 (HimgK a (Henv' a ltac:(lia)))).
- apply (proj1 (proj2 (HimgK a (Henv' a ltac:(lia))))). }
assert (HrkV : forall lo hi cs, (forall a, lo <= a < hi -> mbyte ubs0segs mem1 a = mbyte ubs0segs (ms_mem ms) a) ->
region_kept ubs0segs E1 (ms_mem ms) mem1 (YP09.mkRegion None lo hi 0 0 cs)).
{ intros lo hi cs Heq. split; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; intros a Ha; [apply Heq; exact Ha | lia]. }
destruct (ax_statics AX L A (ms_mem ms) md' (proj1 (proj1 HJ'))) as (Hgot0 & _ & Hnl0).
destruct (ax_statics AX L1 A1 mem1 md1 (proj1 (proj1 HJ1))) as (Hgot1 & _ & Hnl1).
change (ms_segs ubs0_msyms) with ubs0segs in Hgot0, Hnl0, Hgot1, Hnl1. change (ms_got_guard ubs0_msyms) with 128824 in Hgot0, Hgot1.
change (ms_libc ubs0_msyms) with 331064 in Hnl0, Hnl1. change ubs0_D_stack_chk_guard with 331032 in Hgm. change (ms_guard ubs0_msyms) with 331032 in Hg1.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor.
{ eapply (region_kept_stack ubs0segs _ _ _ 2); [rewrite HE2'; exact Hspw | exact Hhi1 | lia | lia | lia | lia | lia]. }
constructor; [apply HrkA; [intros a Ha; do 6 right; left; change sk_rwa_addr with 66448; lia | lia | lia]|].
constructor; [apply HrkA; [intros a Ha; do 4 right; left; change sk_mode_addr with 66210; lia | lia | lia]|].
constructor; [apply HrkA; [intros a Ha; do 7 right; left; change sk_highs_addr with 66488; lia | lia | lia]|].
constructor; [apply HrkA; [intros a Ha; do 8 right; change sk_ones_addr with 66504; lia | lia | lia]|].
constructor.
{ apply HrkV. intros a Ha. replace a with (128824 + Z.of_nat (Z.to_nat (a - 128824))) by lia.
rewrite (Hgot1 (Z.to_nat (a - 128824))) by lia. rewrite (Hgot0 (Z.to_nat (a - 128824))) by lia. reflexivity. }
constructor.
{ apply HrkV. intros a Ha. replace a with (331032 + Z.of_nat (Z.to_nat (a - 331032))) by lia.
rewrite (Hg1 (Z.to_nat (a - 331032))) by lia. rewrite (Hgm (Z.to_nat (a - 331032))) by lia. reflexivity. }
constructor; [apply HrkA; [intros a Ha; right; left; change sk_threaded with 331065; lia | lia | lia]|].
constructor.
{ apply HrkV. intros a Ha. replace a with (331064 + 3) by lia. rewrite Hnl1, Hnl0. reflexivity. }
constructor; [apply HrkA; [intros a Ha; right; right; left; change sk_ofl_lock with 332128; lia | lia | lia]|].
constructor; [apply HrkA; [intros a Ha; left; change sk_ofl_head with 332136; lia | lia | lia]|].
constructor. }
clear HS. rename HS2 into HS.
(jreg HS (10%bv:reg) as Hatom); cbn [ms_regs mkst] in Hatom; rewrite Hr10 in Hatom; symmetry in Hatom.
pose proof HJ1 as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw1) & _).
add_region HS (YP09.mkRegion (Some 2%nat) (-256) (-96) (-256) (-96) []).
2:{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val ms_mem mkst]. change (ms_segs ubs0_msyms) with ubs0segs.
rewrite ew_havoc_old, HE2', Hspw by lia.
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply Hstw1. lia. }
2:{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite ew_havoc_old, HE2', Hspw by lia.
repeat split; lia. }
remember (havoc E1 34 (map (getr regs1) CLOB)) as E2 eqn:HE2d.
assert (HA2 : env_agree 32 (Ereg regs [Z_to_bv 64 g]) E2) by (rewrite HE2d; eapply (env_agree_havoc_ge 32 34); [lia | exact HA1]).
assert (HX2 : ew E2 2 = getr regs 2) by (rewrite HE2d, ew_havoc_old by lia; exact HE2').
assert (HX1 : ew E2 1 = getr regs 1) by (rewrite HE2d, ew_havoc_old by lia; exact HE1').
assert (HX4 : ew E2 4 = Z_to_bv 64 (ms_tp ubs0_msyms)) by (rewrite HE2d, ew_havoc_old by lia; exact HE4').
assert (HX32 : ew E2 32 = Z_to_bv 64 g) by (rewrite HE2d, ew_havoc_old by lia; exact HE32').
assert (HX33 : ew E2 33 = Z_to_bv 64 fd) by (rewrite HE2d, ew_havoc_old by lia; exact HE33).
clear HE2d.
assert (Hwr1 : forall E' blc csl cs0 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11, ew E' 2 = getr regs 2 ->
wr_okE ubs0_msyms E' [YP09.mkRegion (Some 2%nat) (-256) (-96) (-256) (-96) csl; YP09.mkRegion (Some 2%nat) (-96) 0 (-96) 0 cs0;
YP09.mkRegion None 66448 66456 0 0 cs2; YP09.mkRegion None 66210 66213 0 0 cs3;
YP09.mkRegion None 66488 66496 0 0 cs4; YP09.mkRegion None 66504 66512 0 0 cs5;
YP09.mkRegion None 128824 128832 0 0 cs6; YP09.mkRegion None 331032 331040 0 0 cs7;
YP09.mkRegion None 331065 331066 0 0 cs8; YP09.mkRegion None 331067 331068 0 0 cs9;
YP09.mkRegion None 332128 332132 0 0 cs10; YP09.mkRegion None 332136 332144 332136 332144 cs11]
FOPEN_STK (spZ regs) [sink_token] (blocks L A) blc).
{ intros E' blc csl cs0 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 HE2x.
do 2 (apply wr_okE_cons_ok; [eapply wr_ok_cons_stack; [reflexivity | rewrite HE2x; exact Hspw | cbn; lia | cbn; lia | apply wr_ok_nil]|]).
do 9 (apply wr_okE_cons_ok; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|]).
apply wr_okE_cons_head; [reflexivity | exact Htok | cbn [r_wlo]; change sk_ofl_head with 332136; lia | cbn [r_whi]; change sk_ofl_head with 332136; lia | apply wr_okE_nil]. }
assert (HfrK1 : forall E' csl cs0 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 (m m' : word -> option byte), ew E' 2 = getr regs 2 ->
frame_of E' [YP09.mkRegion (Some 2%nat) (-256) (-96) (-256) (-96) csl; YP09.mkRegion (Some 2%nat) (-96) 0 (-96) 0 cs0;
YP09.mkRegion None 66448 66456 0 0 cs2; YP09.mkRegion None 66210 66213 0 0 cs3;
YP09.mkRegion None 66488 66496 0 0 cs4; YP09.mkRegion None 66504 66512 0 0 cs5;
YP09.mkRegion None 128824 128832 0 0 cs6; YP09.mkRegion None 331032 331040 0 0 cs7;
YP09.mkRegion None 331065 331066 0 0 cs8; YP09.mkRegion None 331067 331068 0 0 cs9;
YP09.mkRegion None 332128 332132 0 0 cs10; YP09.mkRegion None 332136 332144 332136 332144 cs11] m m' ->
forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 256 <= a < spZ regs) -> ~ (332136 <= a < 332144) ->
mbyte ubs0segs m' a = mbyte ubs0segs m a).
{ intros E' csl cs0 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 m m' HE2x HF' a Ha Hns Hnh. unfold mbyte. rewrite (HF' (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. intros (r & Hin & Hr).
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]; cbn [r_base r_wlo r_whi base_val] in Hr;
rewrite ?HE2x, ?Hspw in Hr by lia; lia. }
destruct Hres as (Hpnz & Hp16 & (pb1 & pb2 & HBp & HBc) & Hfresh & Hp0 & Hp1).
assert (HBin : In (p, 1264) (blocks L1 A1)) by (rewrite HBp; apply in_app_iff; right; left; reflexivity).
assert (HB1 : Permutation (blocks L1 A1) ((p, 1264) :: blocks L A)) by (rewrite HBp, HBc; apply Permutation_sym; apply Permutation_middle).
assert (Hpimg : forall i, 0 <= i < 1264 -> ~ in_img ubs0_msyms (p + i)).
{ intros i Hi. pose proof HBin as Hq. apply blocks_In in Hq as (q & Hq & Hqin). rewrite <- Hq.
exact (il_blocks IMG L1 A1 mem1 md1 q 1264 i (proj1 (proj1 HJ1)) Hqin Hi). }
assert (HpoffR : p + 1264 <= 0x10000 \/ 0x10000 + 0x2000 <= p)
by exact (blk_off_img 0x10000 0x2000 p 1264 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) Hpimg).
assert (Hpoff : p + 1264 <= 0x1f000 \/ 0x52000 <= p).
{ destruct (blk_off_img 0x1f000 0x1000 p 1264 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) Hpimg) as [Ho1 | Ho1];
destruct (blk_off_img 0x20000 0x32000 p 1264 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) Hpimg) as [Ho2 | Ho2]; lia. }
add_fact' HS 38%nat (mkAF 4096 (CEIL_MAX - 1264) 4).
2:{ rewrite Hatom, unsigned_lit_small by lia. change (2 ^ 4) with 16. lia. }
assert (Wp : forall blc a, In (p, 1264) blc -> p <= a < p + 1264 -> wr_byte FOPEN_STK (spZ regs) [sink_token] (blocks L A) blc a).
{ intros blc a Hinb Ha. right. right. exists p, 1264. split; [exact Hinb|]. split; [exact Hfresh | lia]. }
jrunE_to LAWS ubs0tbl_ok HS HJ1 ubs0_A_memset.
{ wr_normE. apply Hwr1. exact HX2. }
(jreg HS (10%bv:reg) as Mm10); (jreg HS (11%bv:reg) as Mm11); (jreg HS (12%bv:reg) as Mm12); (jreg HS (1%bv:reg) as Mm1).
cbn [ms_regs mkst] in Mm10, Mm11, Mm12, Mm1. rewrite Hatom in Mm10.
eapply SR_bind.
{ lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
eapply (jmemset ubs0_msyms MR LAWS IMG ubs0_A_memset ubs0_memset_spec_f Ex ssx msx _ _ _ _ _ _ _ _ _ _ p 0 232);
[ exact HS | reflexivity | reflexivity | exact HJ1 | exact Mm10 | exact Mm11 | exact Mm12 | exact Mm1
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia
| intros i Hi; apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ p 1264 i (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) HBin ltac:(lia)))
| intros a Ha; apply (Wp (blocks L1 A1) a HBin); lia ] end. }
clear Mm10 Mm11 Mm12 Mm1.
cbv beta. intros c' (regs2 & mem2 & -> & HJ3 & Hd10 & Hfr2 & Hout2 & Hgr2 & Zp). clear HJ1. rename HJ3 into HJ1.
lazymatch goal with |- SR _ (mkCfg (mkst _ (Z_to_bv 64 ?pcm) _ _) _) _ => jafter_stretch HS 50%nat regs2 mem2 MEMSET_CLOB pcm HS2 end.
specialize (HS2 Hfr2).
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ do 2 (apply Forall_cons;
[eapply region_kept_outside; [exact Hout2 | exact Hgr2 | | | | cbn; lia | cbn; lia]; cbn [r_base r_lo r_hi base_val]; ew_havoc; rewrite ?HX2, ?Hspw; lia |]).
do 9 (apply Forall_cons; [eapply region_kept_abs_ro; [exact Hout2 | lia | lia | lia] |]).
apply Forall_cons; [|apply Forall_nil].
eapply region_kept_outside; [exact Hout2 | exact Hgr2 | | | | cbn; lia | cbn; lia]; cbn [r_base r_lo r_hi base_val]; lia. }
clear HS. rename HS2 into HS.
remember (havoc E2 50 (map (getr regs2) MEMSET_CLOB)) as E3 eqn:HE3d.
assert (HA3 : env_agree 32 (Ereg regs [Z_to_bv 64 g]) E3) by (rewrite HE3d; eapply (env_agree_havoc_ge 32 50); [lia | exact HA2]).
assert (HY2 : ew E3 2 = getr regs 2) by (rewrite HE3d, ew_havoc_old by lia; exact HX2).
assert (HY1 : ew E3 1 = getr regs 1) by (rewrite HE3d, ew_havoc_old by lia; exact HX1).
assert (HY4 : ew E3 4 = Z_to_bv 64 (ms_tp ubs0_msyms)) by (rewrite HE3d, ew_havoc_old by lia; exact HX4).
assert (HY32 : ew E3 32 = Z_to_bv 64 g) by (rewrite HE3d, ew_havoc_old by lia; exact HX32).
assert (HY33 : ew E3 33 = Z_to_bv 64 fd) by (rewrite HE3d, ew_havoc_old by lia; exact HX33).
assert (HY38 : ew E3 38 = Z_to_bv 64 p) by (rewrite HE3d, ew_havoc_old by lia; exact Hatom).
clear HE3d.
add_region HS (YP09.mkRegion (Some 38%nat) 0 1264 0 1264 [mkChunk 0 (CZero 232)]).
2:{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val ms_mem mkst]. change (ms_segs ubs0_msyms) with ubs0segs. rewrite HY38, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable ubs0_msyms).
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ p 1264 o (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) HBin Ho)). }
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. cbn [c_off]. intros i Hi. rewrite Z.add_0_r. apply Zp. exact Hi. }
2:{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HY2, HY38, Hspw, unsigned_lit_small by lia.
repeat split; lia. }
assert (Hwr2 : forall E' blc csb csl cs0 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11, ew E' 2 = getr regs 2 -> ew E' 38 = Z_to_bv 64 p -> In (p, 1264) blc ->
wr_okE ubs0_msyms E' [YP09.mkRegion (Some 38%nat) 0 1264 0 1264 csb; YP09.mkRegion (Some 2%nat) (-256) (-96) (-256) (-96) csl; YP09.mkRegion (Some 2%nat) (-96) 0 (-96) 0 cs0;
YP09.mkRegion None 66448 66456 0 0 cs2; YP09.mkRegion None 66210 66213 0 0 cs3;
YP09.mkRegion None 66488 66496 0 0 cs4; YP09.mkRegion None 66504 66512 0 0 cs5;
YP09.mkRegion None 128824 128832 0 0 cs6; YP09.mkRegion None 331032 331040 0 0 cs7;
YP09.mkRegion None 331065 331066 0 0 cs8; YP09.mkRegion None 331067 331068 0 0 cs9;
YP09.mkRegion None 332128 332132 0 0 cs10; YP09.mkRegion None 332136 332144 332136 332144 cs11]
FOPEN_STK (spZ regs) [sink_token] (blocks L A) blc).
{ intros E' blc csb csl cs0 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 HE2x HE38x Hinb.
apply wr_okE_cons_ok.
{ eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 38%nat); [reflexivity | rewrite HE38x; apply unsigned_lit_small; lia | | apply wr_ok_nil].
cbn [r_wlo r_whi]. intros a Ha. apply (Wp blc a Hinb). lia. }
apply Hwr1. exact HE2x. }
assert (HfrK2 : forall E' csb csl cs0 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 (m m' : word -> option byte), ew E' 2 = getr regs 2 -> ew E' 38 = Z_to_bv 64 p ->
frame_of E' [YP09.mkRegion (Some 38%nat) 0 1264 0 1264 csb; YP09.mkRegion (Some 2%nat) (-256) (-96) (-256) (-96) csl; YP09.mkRegion (Some 2%nat) (-96) 0 (-96) 0 cs0;
YP09.mkRegion None 66448 66456 0 0 cs2; YP09.mkRegion None 66210 66213 0 0 cs3;
YP09.mkRegion None 66488 66496 0 0 cs4; YP09.mkRegion None 66504 66512 0 0 cs5;
YP09.mkRegion None 128824 128832 0 0 cs6; YP09.mkRegion None 331032 331040 0 0 cs7;
YP09.mkRegion None 331065 331066 0 0 cs8; YP09.mkRegion None 331067 331068 0 0 cs9;
YP09.mkRegion None 332128 332132 0 0 cs10; YP09.mkRegion None 332136 332144 332136 332144 cs11] m m' ->
forall a, 0 <= a < 2 ^ 64 -> ~ (p <= a < p + 1264) -> ~ (spZ regs - 256 <= a < spZ regs) -> ~ (332136 <= a < 332144) ->
mbyte ubs0segs m' a = mbyte ubs0segs m a).
{ intros E' csb csl cs0 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 m m' HE2x HE38x HF' a Ha Hnb Hns Hnh. unfold mbyte. rewrite (HF' (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. intros (r & Hin & Hr).
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]; cbn [r_base r_wlo r_whi base_val] in Hr;
rewrite ?HE2x, ?HE38x, ?Hspw, ?unsigned_lit_small in Hr by lia; lia. }
jrunE LAWS ubs0tbl_ok HS HJ1.
{ wr_normE. apply Hwr2; [exact HY2 | exact HY38 | exact HBin]. }
sym_ecall_open HS.
match goal with HFx : frame_of _ _ _ (ms_mem (pend_at ?r ?pp ?m ?ro)) |- _ => change (ms_mem (pend_at r pp m ro)) with m in HFx, HJ1 end.
assert (Hfdr' : 0 <= fd < 2 ^ 31) by lia.
lazymatch goal with |- SR _ (mkCfg (pend_at ?rX _ ?mX _) _) _ =>
apply (J_ioctl_winsz_node ubs0_msyms MR LAWS rX _ mX _ _ _ _ _ _ _ _ _ _ _ fd (Z_to_bv 64 (Z.of_nat (@length Z []))) HJ1) end.
{ rewrite (Hregs 17%bv). eval_sr_get. reflexivity. }
{ rewrite (Hregs 10%bv). eval_sr_get. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact HY33. }
{ exact Hfdr'. }
{ exact (proj1 (proj2 Hos2)). }
{ rewrite (Hregs 11%bv). eval_sr_get. apply bv_eq. vm_compute. reflexivity. }
cbn [ss_pc].
resume_sv_sr ubs0segs (SLit (-25)).
{ reflexivity. }
jrunE LAWS ubs0tbl_ok HS HJ1.
{ wr_normE. apply Hwr2; [exact HY2 | exact HY38 | exact HBin]. }
pose proof (regs_preserved_of_st_ok _ _ _ _ _ _ HS HA3 ltac:(vm_compute; reflexivity)) as HPR.
jreg HS (1%bv:reg) as Hr1. jreg HS (10%bv:reg) as Hq10.
pose proof (mem_ok_region _ _ _ _ _ (st_ok_mem_ok _ _ _ _ HS) ltac:(left; reflexivity)) as (_ & _ & _ & Hcs).
cbn [r_base r_chunks base_val] in Hcs. rewrite HY38, unsigned_lit_small in Hcs by lia.
pose proof (mem_ok_region _ _ _ _ _ (st_ok_mem_ok _ _ _ _ HS) ltac:(do 12 right; left; reflexivity)) as (_ & _ & _ & Hcsh).
cbn [r_base r_chunks base_val] in Hcsh.
lazymatch type of HS with st_ok _ _ _ ?msF =>
assert (Hheadp : val_mem ubs0segs (ms_mem msF) 332136 8 p)
by (inversion Hcsh as [|c cs Hc0 _]; subst;
exact (val_of_chunk_ok ubs0segs _ _ 0 332136 8 (SOff 38%nat 0) p Hc0
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact HY38) ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(vm_compute; congruence))) end.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ1)) as (Hh' & Hlz' & _).
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | exact Hh' | exact Hlz' | exact HS | reflexivity | vm_compute; reflexivity |].
apply KB. lazymatch type of HS with st_ok _ _ _ ?msF => exists L1, A1, (ms_regs msF), (ms_mem msF), md1, p end.
rewrite Hr1, HY1, Hra.
split; [reflexivity|]. split; [exact HJ1|]. split; [exact HPR|]. split; [exact Hid1|].
split; [rewrite Hq10; exact HY38|].
split; [exact Hpnz|]. split; [exact HB1|]. split; [| split; [rewrite Efs1; exact Hfs' | exact HRES1]].
exists fd, [], []. split; [reflexivity|]. split; [constructor|]. split; [cbn; unfold SINK_MAX; lia|].
split; [exact (ubs0_stdio_env_kept _ _ _ (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HJ1))))))) Henv)|].
split.
{ apply (obj_file_at_fresh ubs0_msyms _ p fd Hfdr').
apply (obj_at_of_chunks_gen2 _ _ _ _ LAY_FILE _ Hcs eq_refl).
unfold file_vals, LAY_FILE.
constructor; [fld_lit2|]. constructor; [fld_zero|]. constructor; [fld_zero|]. constructor; [fld_lit2|].
constructor; [fld_zero|]. constructor; [fld_zero|]. constructor; [fld_zero|]. constructor; [fld_zero|].
constructor; [fld_lit2|]. constructor; [fld_lit2|]. constructor; [fld_lit2|].
constructor; [fld_off2 HY38|]. constructor; [fld_lit2|].
constructor; [fld_zero|]. constructor; [fld_lit2|].
constructor; [fld_atom2 HY33|].
constructor; [fld_zero|]. constructor; [fld_zero|]. constructor; [fld_zero|].
constructor; [fld_lit2|]. constructor; [fld_lit2|].
do 10 (constructor; [fld_zero|]). constructor. }
split; [apply (val_mem_word_mem ubs0segs); exact Hheadp|]. split; [exact Hpnz|].
exact Hos2.
Qed.
End S.
End d.
