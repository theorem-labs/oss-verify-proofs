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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI06 YI09 YI16 YI00 YI14 YI07 YI19 YI15 UI5b UI5c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UN3j UN37 YI05 YI18.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition FC_DEPTH : Z := 256.
Definition reg_fc_stack : YP09.region := YP09.mkRegion (Some 2%nat) (-FC_DEPTH) 0 (-FC_DEPTH) 0 [].
Definition reg_fc_file (buffered : bool) : YP09.region :=
YP09.mkRegion (Some 10%nat) 0 FILE_HDR 0 FILE_HDR (obj_chunks_gen LAY_FILE 32 (lits_FILE buffered)).
Definition reg_needlocks : YP09.region :=
YP09.mkRegion None (ubs0_D_libc + 3) (ubs0_D_libc + 4) 0 0 [mkChunk (ubs0_D_libc + 3) (CVal 1 (SLit 0))].
Definition reg_ofl_lock : YP09.region :=
YP09.mkRegion None ubs0_D_ofl_lock (ubs0_D_ofl_lock + 4) 0 0 [mkChunk ubs0_D_ofl_lock (CVal 4 (SLit 0))].
Definition reg_ofl_head : YP09.region :=
YP09.mkRegion None ubs0_D_ofl_head (ubs0_D_ofl_head + 8) ubs0_D_ofl_head (ubs0_D_ofl_head + 8) [mkChunk ubs0_D_ofl_head (CVal 8 (SOff 10%nat 0))].
Definition fc_facts (buffered : bool) : list (nat * afact) :=
[ (2%nat, mkAF (CEIL_MIN + FCLOSE_STK) (2^47) 4); (10%nat, mkAF 4096 CEIL_MAX 4); (43%nat, mkAF 4096 CEIL_MAX 0); (47%nat, mkAF 0 (2^31 - 1) 0) ]
++ (if buffered then [ (36%nat, mkAF 4096 CEIL_MAX 0); (37%nat, mkAF 4096 CEIL_MAX 0); (39%nat, mkAF 4096 CEIL_MAX 0) ] else []).
Definition ss_fc (buffered : bool) : sstate :=
mkSS ubs0_A_fclose sr_atoms [ reg_fc_stack; reg_fc_file buffered; reg_got; reg_guard; reg_needlocks; reg_ofl_lock; reg_ofl_head ] None
(mkFacts (fc_facts buffered) [] []).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma ubs0_head_writable : forall (mem : word -> option byte) a, 332136 <= a < 332144 -> writable_at ubs0segs mem a.
Proof using.
intros mem a Ha.
assert (Hc : a = 332136 \/ a = 332137 \/ a = 332138 \/ a = 332139 \/ a = 332140 \/ a = 332141 \/ a = 332142 \/ a = 332143) by lia.
unfold writable_at, wview.
destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]];
(match goal with |- match mem ?x with _ => _ end <> None => destruct (mem x); [discriminate | (first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])] end).
Qed.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis AX : AllocExtra ubs0_msyms MR.
Theorem ubs0_fcloseR : fclose_spec_res ubs0_msyms MR ubs0_A_fclose.
Proof using AX IMG LAWS.
intros L A regs mem md f S rest b HPRE Hinit Hsp47 H10 HB HSA HRb.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HSTKv : FCLOSE_STK = 512 + ALLOC_STACK) by reflexivity. assert (HAS : ALLOC_STACK = 8192) by reflexivity.
assert (HFB : FILE_BLOCK = 1264) by reflexivity. assert (HBO : FILE_BUF_OFF = 240) by reflexivity.
assert (HBS : FILE_BUFSIZ = 1024) by reflexivity. assert (HU : U32M1 = 4294967295) by reflexivity.
assert (HSM : SINK_MAX = 2 ^ 62) by reflexivity. assert (HFH : FILE_HDR = 232) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
assert (Hfin : In (f, FILE_BLOCK) (blocks L A)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
destruct (heap_blocks_range ubs0_msyms MR LAWS L A mem md f FILE_BLOCK HH Hfin ltac:(lia)) as (Bf0 & Bf1 & Bf16).
destruct HSA as (fd & W & P & -> & Hok & Hmax & Henv & Hfile & Hhead & Hf0 & Hfs & Hfd & Huniq).
destruct (file_at_obj ubs0_msyms mem f fd P ubs0_sink_code_ok ltac:(lia) ltac:(lia) Hfile) as (Hfdr & Hreg).
destruct (ax_statics AX L A mem md (proj1 HH)) as (Hgot & (g & Hg0 & Hguard) & Hnl).
pose proof Henv as (_ & Hlock & _).
assert (Hfimg : forall i, 0 <= i < FILE_BLOCK -> ~ in_img ubs0_msyms (f + i)).
{ intros i Hi. pose proof Hfin as Hq. apply blocks_In in Hq as (q & Hq & Hqin). rewrite <- Hq.
exact (il_blocks IMG L A mem md q FILE_BLOCK i (proj1 HH) Hqin Hi). }
assert (HoffR : f + FILE_BLOCK <= 0x10000 \/ 0x10000 + 0x2000 <= f)
by exact (blk_off_img 0x10000 0x2000 f FILE_BLOCK ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) Hfimg).
assert (Hoff : f + FILE_BLOCK <= 0x1f000 \/ 0x52000 <= f).
{ destruct (blk_off_img 0x1f000 0x1000 f FILE_BLOCK ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) Hfimg) as [Hoff1 | Hoff1];
destruct (blk_off_img 0x20000 0x32000 f FILE_BLOCK ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) Hfimg) as [Hoff2 | Hoff2]; lia. }
assert (Hspw : bv_unsigned (getr regs 2) = spZ regs) by reflexivity.
assert (Htok : sink_open_fp (sink_fp f)) by (apply sink_open_token; left; reflexivity).
assert (Hwr0 : forall E' cs1 cs2 cs3 cs4 cs5 cs6 cs7, ew E' 2 = getr regs 2 -> ew E' 10 = Z_to_bv 64 f ->
wr_okE ubs0_msyms E' [YP09.mkRegion (Some 2%nat) (-256) 0 (-256) 0 cs1; YP09.mkRegion (Some 10%nat) 0 232 0 232 cs2;
YP09.mkRegion None 128824 128832 0 0 cs3; YP09.mkRegion None 331032 331040 0 0 cs4;
YP09.mkRegion None 331067 331068 0 0 cs5; YP09.mkRegion None 332128 332132 0 0 cs6;
YP09.mkRegion None 332136 332144 332136 332144 cs7]
FCLOSE_STK (spZ regs) (sink_fp f) (blocks L A) (blocks L A)).
{ intros E' cs1 cs2 cs3 cs4 cs5 cs6 cs7 HE2' HE10'.
apply wr_okE_cons_ok; [eapply wr_ok_cons_stack; [reflexivity | rewrite HE2'; exact Hspw | cbn; lia | cbn; lia | apply wr_ok_nil]|].
apply wr_okE_cons_ok.
{ eapply (wr_ok_cons_inblock _ _ _ _ _ _ _ _ 10 f f FILE_BLOCK);
[reflexivity | rewrite HE10'; apply unsigned_lit_small; lia | exact Hfin | cbn; lia | cbn; lia | | apply wr_ok_nil].
cbn [r_wlo r_whi]. intros a Ha. exists (f, f + FILE_BLOCK). split; [right; left; reflexivity | cbn; lia]. }
do 4 (apply wr_okE_cons_ok; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|]).
apply wr_okE_cons_head; [reflexivity | exact Htok | cbn [r_wlo]; change sk_ofl_head with 332136; lia | cbn [r_whi]; change sk_ofl_head with 332136; lia | apply wr_okE_nil]. }
assert (HfrK : forall E' cs1 cs2 cs3 cs4 cs5 cs6 cs7 (m m' : word -> option byte), ew E' 2 = getr regs 2 -> ew E' 10 = Z_to_bv 64 f ->
frame_of E' [YP09.mkRegion (Some 2%nat) (-256) 0 (-256) 0 cs1; YP09.mkRegion (Some 10%nat) 0 232 0 232 cs2;
YP09.mkRegion None 128824 128832 0 0 cs3; YP09.mkRegion None 331032 331040 0 0 cs4;
YP09.mkRegion None 331067 331068 0 0 cs5; YP09.mkRegion None 332128 332132 0 0 cs6;
YP09.mkRegion None 332136 332144 332136 332144 cs7] m m' ->
forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 256 <= a < spZ regs) -> ~ (f <= a < f + 232) -> ~ (332136 <= a < 332144) ->
mbyte ubs0segs m' a = mbyte ubs0segs m a).
{ intros E' cs1 cs2 cs3 cs4 cs5 cs6 cs7 m m' HE2' HE10' HF' a Ha Hns Hnf Hnh. unfold mbyte. rewrite (HF' (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. intros (r & Hin & Hr).
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn [r_base r_wlo r_whi base_val] in Hr; rewrite ?HE2', ?HE10', ?Hspw, ?unsigned_lit_small in Hr by lia; lia. }
destruct Hreg as [(-> & Hobj) | (Hobj & HGP & HLP)].
2:{
set (p := Z.of_nat (length P)) in *.
assert (Hp0 : 0 <= p) by (subst p; lia).
remember (file_vals f fd (f + FILE_BUF_OFF + FILE_BUFSIZ) (f + FILE_BUF_OFF + p) (f + FILE_BUF_OFF) U32M1) as vals eqn:Hvals.
remember (Ereg regs (map (Z_to_bv 64) vals ++ [Z_to_bv 64 g])) as E0 eqn:HE0.
assert (HA0 : env_agree 32 (Ereg regs (map (Z_to_bv 64) vals ++ [Z_to_bv 64 g])) E0) by (rewrite HE0; apply env_agree_refl).
assert (HEv : forall j v, nth_error vals j = Some v -> ew E0 (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HE2 : ew E0 2 = getr regs 2) by (subst E0; apply (ew_Ereg_nat regs _ 2 2%bv); vm_compute; reflexivity).
assert (HE1 : ew E0 1 = getr regs 1) by (subst E0; apply (ew_Ereg_nat regs _ 1 1%bv); vm_compute; reflexivity).
assert (HE10 : ew E0 10 = Z_to_bv 64 f) by (subst E0; rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity); exact H10).
assert (HE4 : ew E0 4 = Z_to_bv 64 (ms_tp ubs0_msyms)) by (subst E0; rewrite (ew_Ereg_nat regs _ 4 4%bv) by (vm_compute; reflexivity); exact Htp).
assert (HE36 : ew E0 36 = Z_to_bv 64 (f + FILE_BUF_OFF + FILE_BUFSIZ)) by (apply (HEv 4%nat); rewrite Hvals; reflexivity).
assert (HE37 : ew E0 37 = Z_to_bv 64 (f + FILE_BUF_OFF + p)) by (apply (HEv 5%nat); rewrite Hvals; reflexivity).
assert (HE39 : ew E0 39 = Z_to_bv 64 (f + FILE_BUF_OFF)) by (apply (HEv 7%nat); rewrite Hvals; reflexivity).
assert (HE43 : ew E0 43 = Z_to_bv 64 (f + FILE_BUF_OFF)) by (apply (HEv 11%nat); rewrite Hvals; reflexivity).
assert (HE47 : ew E0 47 = Z_to_bv 64 fd) by (apply (HEv 15%nat); rewrite Hvals; reflexivity).
assert (HE63 : ew E0 63 = Z_to_bv 64 g).
{ subst E0. rewrite (ew_Ereg_extra regs _ 31). rewrite Hvals. reflexivity. }
set (ms0 := mkst regs (Z_to_bv 64 ubs0_A_fclose) mem (seg_rom ubs0segs)).
pose proof (journal_init ubs0_msyms MR FCLOSE_STK (sink_fp f) L A regs mem md HPRE) as HJ.
change mem with (ms_mem ms0) in HJ.
assert (HS : st_ok ubs0segs E0 (ss_fc true) ms0).
{ rewrite HE0. apply entry_st_ok_full; rewrite <- ?HE0.
- rewrite HE0. apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]]].
+ apply (region_ok_stack ubs0segs _ mem 2 (spZ regs)); [| unfold FC_DEPTH; lia | lia | intros a Ha; apply Hstw; unfold FC_DEPTH in Ha; lia].
rewrite HE2. exact Hspw.
+ eapply (region_ok_obj_gen ubs0segs E0 mem 10 f FILE_HDR 0 FILE_HDR LAY_FILE vals 32 (lits_FILE true));
[ rewrite HE10; apply unsigned_lit_small; lia | lia | lia | exact Hobj | reflexivity | exact HEv | | ].
* intros j z Hj. rewrite Hvals.
do 31 (destruct j as [|j]; [cbn in Hj; first [discriminate Hj | injection Hj as <-; reflexivity] |]).
destruct j; discriminate Hj.
* intros i Hi. apply (present_writable ubs0_msyms).
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ f FILE_BLOCK i HH Hfin ltac:(lia))).
+ unfold region_ok, reg_got. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [intros o Ho; lia|].
constructor; [|constructor].
eapply (chunk_ok_val ubs0segs E0 mem 0 ubs0_D_got_stack_chk_guard 8 (SLit ubs0_D_stack_chk_guard) ubs0_D_stack_chk_guard);
[reflexivity | vm_compute; split; congruence | vm_compute; congruence | ].
apply (val_mem_word_mem ubs0segs). exact Hgot.
+ unfold region_ok, reg_guard. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [intros o Ho; lia|].
constructor; [|constructor].
eapply (chunk_ok_val ubs0segs E0 mem 0 ubs0_D_stack_chk_guard 8 (SOff 63%nat 0) g);
[cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact HE63 | change (8 * Z.of_N 8) with 64; exact Hg0 | vm_compute; congruence | ].
apply (val_mem_word_mem ubs0segs). exact Hguard.
+ unfold region_ok, reg_needlocks. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [intros o Ho; lia|].
constructor; [|constructor].
eapply (chunk_ok_val ubs0segs E0 mem 0 (ubs0_D_libc + 3) 1 (SLit 0) 0); [reflexivity | vm_compute; split; congruence | vm_compute; congruence | ].
intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite !Z.add_0_r. exact Hnl.
+ unfold region_ok, reg_ofl_lock. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [intros o Ho; lia|].
constructor; [|constructor].
eapply (chunk_ok_val ubs0segs E0 mem 0 ubs0_D_ofl_lock 4 (SLit 0) 0); [reflexivity | vm_compute; split; congruence | vm_compute; congruence | exact Hlock].
+ unfold region_ok, reg_ofl_head. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|].
split; [intros o Ho; apply ubs0_head_writable; change ubs0_D_ofl_head with 332136 in Ho; lia|].
constructor; [|constructor].
eapply (chunk_ok_val ubs0segs E0 mem 0 ubs0_D_ofl_head 8 (SOff 10%nat 0) f);
[cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact HE10 | change (8 * Z.of_N 8) with 64; lia | vm_compute; congruence | ].
apply (val_mem_word_mem ubs0segs). exact Hhead.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, reg_fc_stack, reg_fc_file, reg_got, reg_guard, reg_needlocks, reg_ofl_lock, reg_ofl_head.
cbn [r_base r_lo r_hi base_val]. rewrite HE2, HE10, Hspw, !unsigned_lit_small by lia.
change ubs0_D_got_stack_chk_guard with 128824. change ubs0_D_stack_chk_guard with 331032. change ubs0_D_libc with 331064.
change ubs0_D_ofl_lock with 332128. change ubs0_D_ofl_head with 332136. unfold FC_DEPTH.
repeat split; lia.
- split; [|split; [exact I|exact I]].
cbn [f_atoms atoms_ok fc_facts app]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE2, HE10, HE36, HE37, HE39, HE43, HE47, Hspw, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
jrunE LAWS ubs0tbl_ok HS HJ.
{ wr_normE. apply Hwr0; [exact HE2 | exact HE10]. }
pose proof (HfrK _ _ _ _ _ _ _ _ _ _ HE2 HE10 HF) as Hk1. unfold ms0 in Hk1. cbn [ms_mem mkst] in Hk1.
jbranch ubs0tbl HS.
-
rewrite branch_eq_U, (U_atom _ 37 _ HE37), (U_atom _ 39 _ HE39) in Hc by lia.
assert (Hp : p = 0) by (destruct (Z.eqb_spec (f + FILE_BUF_OFF + p) (f + FILE_BUF_OFF)); [lia | discriminate Hc]).
clear Hc.
assert (HP0 : P = []) by (destruct P; [reflexivity | subst p; cbn [length] in Hp; lia]).
assert (Hos : sink_os md fd (W ++ P)) by (rewrite HP0, app_nil_r; exact (conj Hfs (conj Hfd Huniq))).
jrunE LAWS ubs0tbl_ok HS HJ.
{ wr_normE. apply Hwr0; [exact HE2 | exact HE10]. }
sym_ecall_open HS.
match goal with HFx : frame_of _ _ _ (ms_mem (pend_at ?r ?pc ?m ?ro)) |- _ => change (ms_mem (pend_at r pc m ro)) with m in HFx, HJ end.
lazymatch goal with |- SR _ (mkCfg (pend_at ?rX _ ?mX _) _) _ => lazymatch type of Hos with sink_os _ _ ?wp =>
apply (J_close_node ubs0_msyms MR LAWS rX _ mX _ _ _ _ _ _ _ _ _ _ _ fd wp HJ Htok Hos Hfdr) end end.
{ rewrite (Hregs 17%bv). eval_sr_get. reflexivity. }
{ rewrite (Hregs 10%bv). eval_sr_get. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact HE47. }
intros md' HJ' Hnm' Hfs'. cbn [ss_pc].
resume_sv_sr ubs0segs (SLit 0).
{ reflexivity. }
jrunE_to LAWS ubs0tbl_ok HS HJ' 0x18244.
{ wr_normE. apply Hwr0; [exact HE2 | exact HE10]. }
jrunE_to LAWS ubs0tbl_ok HS HJ' ubs0_A_free.
{ wr_normE. apply Hwr0; [exact HE2 | exact HE10]. }
pose proof (mem_ok_region _ _ _ _ _ (st_ok_mem_ok _ _ _ _ HS) ltac:(do 6 right; left; reflexivity)) as (_ & _ & _ & Hcsh).
cbn [r_base r_chunks base_val] in Hcsh.
lazymatch type of HS with st_ok _ _ _ ?msF =>
assert (Hhead0 : val_mem ubs0segs (ms_mem msF) 332136 8 0)
by (inversion Hcsh as [|c cs Hc0 _]; subst;
exact (val_of_chunk_ok ubs0segs _ _ 0 332136 8 (SLit 0) 0 Hc0 eq_refl ltac:(vm_compute; split; congruence) ltac:(vm_compute; congruence))) end.
jreg HS (10%bv:reg) as Hr10. rewrite HE10 in Hr10.
jreg HS (4%bv:reg) as Hr4. jreg HS (1%bv:reg) as Hr1.
eapply SR_bind.
{ eapply (jfree_sub_res ubs0_msyms MR LAWS ubs0_errno_low_f IMG (aa_free API)) with (a := f) (n := FILE_BLOCK) (o := -48) (b := b);
[ exact HS | reflexivity | reflexivity | exact HJ' | exact Hfin | lia | exact HRb | exact Hr10
| exact (st_ok_reg _ _ _ _ 2%bv HS) | exact HE2 | exact Hspw | reflexivity | lia | lia
| exact Hr4 | exact HE4 | exact Hr1 | apply ret_ok_even; vm_compute; reflexivity
| intros i Hi; exists (f, f + FILE_BLOCK); split; [right; left; reflexivity | cbn; lia] ]. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HJin & HP2 & Hrm & Hkeep & Hhi2 & HRES).
replace (rb_free b FILE_BLOCK) with b in HRES by reflexivity.
jafter_call2 HS 64%nat regs2 mem2 HP2 (-48) (@nil nat) HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor].
eapply (region_kept_stack ubs0segs _ _ _ 2); [rewrite HE2; exact Hspw | exact Hhi2 | lia | lia | lia | lia | lia]. }
clear HS. rename HS2 into HS.
jrun LAWS ubs0tbl_ok HS HJ2.
{ wr_norm. eapply wr_ok_cons_stack; [reflexivity | ew_havoc; rewrite HE2; exact Hspw | cbn; lia | cbn; lia | apply wr_ok_nil]. }
assert (HA64 : env_agree 32 (Ereg regs (map (Z_to_bv 64) vals ++ [Z_to_bv 64 g])) (havoc E0 64 (map (getr regs2) CLOB)))
by (eapply (env_agree_havoc_ge 32); [lia | exact HA0]).
pose proof (regs_preserved_of_st_ok _ _ _ _ _ _ HS HA64 ltac:(vm_compute; reflexivity)) as HPR.
jreg HS (10%bv:reg) as Hq10. jreg HS (1%bv:reg) as Hq1.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2)) as (Hh' & Hlz' & _).
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | exact Hh' | exact Hlz' | exact HS | reflexivity | vm_compute; reflexivity |].
lazymatch type of HS with st_ok _ _ _ ?msx => exists L2, A2, (ms_regs msx), (ms_mem msx), md2 end.
rewrite Hq1, HE1, Hra. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HPR|]. split; [exact Hq10|].
split; [eapply perm_after_rm1; [exact HB | exact Hrm]|].
destruct HJin as (_ & HosIn & _ & _ & _ & _ & _ & HimgIn).
assert (Hntok : ~ sink_open_fp [(f, f + FILE_BLOCK)]) by (intros (r & [<-|[]] & Hr); cbn [fst snd] in Hr; lia).
destruct (os_step_shielded _ _ _ HosIn Hntok) as (Efd & Efs & _).
split; [|split; [rewrite Efs, Hfs'; exact (proj1 Hos) | exact HRES]].
split; [exact (ubs0_stdio_env_kept _ _ _ (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HJ2))))))) Henv)|].
split; [|rewrite Efd; exact Hnm'].
apply (val_mem_word_mem ubs0segs). eapply (val_mem_frame ubs0_msyms); [|exact Hhead0].
intros x Hx. change (Z.of_nat 8) with 8 in Hx. change sk_ofl_head with 332136 in Hx.
match goal with HFx : frame_of _ [_] (ms_mem ?m1) (ms_mem ?m2) |- mbyte _ (ms_mem ?m2) _ = _ =>
transitivity (mbyte ubs0segs (ms_mem m1) x);
[ unfold mbyte; rewrite (HFx (Z_to_bv 64 x)); [reflexivity|];
rewrite unsigned_lit_small by lia; intros (r & [<-|[]] & Hr); cbn [r_base r_wlo r_whi base_val] in Hr;
rewrite ew_havoc_old in Hr by (cbv; lia); rewrite HE2, Hspw in Hr; lia
| ] end.
cbn [ms_mem mkst].
assert (Hex : env_addr x) by (left; change sk_ofl_head with 332136; lia).
destruct (skl_env ubs0_msyms x Hex) as (T1 & T2 & T3 & T4).
apply (HimgIn x T1 T2 T3 T4). intros [Ho _]. exact (Hntok Ho).
-
rewrite branch_eq_U, (U_atom _ 37 _ HE37), (U_atom _ 39 _ HE39) in Hc by lia.
assert (Hp : p <> 0) by (destruct (Z.eqb_spec (f + FILE_BUF_OFF + p) (f + FILE_BUF_OFF)); [discriminate Hc | lia]).
clear Hc.
jrunE LAWS ubs0tbl_ok HS HJ.
{ wr_normE. apply Hwr0; [exact HE2 | exact HE10]. }
sym_ecall_open HS.
match goal with HFx : frame_of _ _ _ (ms_mem (pend_at ?r ?pc ?m ?ro)) |- _ =>
change (ms_mem (pend_at r pc m ro)) with m in HFx, HJ;
assert (Hk2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 256 <= a < spZ regs) -> ~ (f <= a < f + 232) -> ~ (332136 <= a < 332144) ->
mbyte ubs0segs m a = mbyte ubs0segs mem a)
by (intros a A1 A2 A3 A4; rewrite (HfrK _ _ _ _ _ _ _ _ _ _ HE2 HE10 HFx a A1 A2 A3 A4); exact (Hk1 a A1 A2 A3 A4)) end.
match type of Hmem with mem_ok _ _ _ ?rs =>
let r := eval vm_compute in (iov_read1 rs (Some 2%nat) (-184)) in
match r with Some (?vb, ?vl) =>
destruct (iov_read1_sound ubs0segs E0 mem0 rs (Some 2%nat) (-184) vb vl Hmem ltac:(vm_compute; reflexivity)) as [M0 L0] end;
let r := eval vm_compute in (iov_read1 rs (Some 2%nat) (-168)) in
match r with Some (?vb, ?vl) =>
destruct (iov_read1_sound ubs0segs E0 mem0 rs (Some 2%nat) (-168) vb vl Hmem ltac:(vm_compute; reflexivity)) as [M1 L1] end end.
rewrite (denot_lit_U E0 (SAlu _ _ _)), U_sub_form in L0; rewrite ?(U_atom _ 37 _ HE37), ?(U_atom _ 39 _ HE39) in * by lia; [|lia].
replace (f + FILE_BUF_OFF + p - (f + FILE_BUF_OFF)) with p in L0 by lia.
cbn [base_val sv_denot] in M0, L0, M1, L1.
rewrite HE2, Hspw, Z.add_0_r, Z_to_bv_bv_unsigned, HE39 in M0. rewrite HE2, Hspw in L0.
rewrite HE2, Hspw in M1. rewrite HE2, Hspw in L1.
assert (HGP0 : garr8 ubs0segs mem0 (f + FILE_BUF_OFF) P) by (eapply garr8_frame; [exact HGP|]; intros a Ha; apply Hk2; lia).
apply (J_writev_node2 ubs0_msyms MR LAWS regs0 _ mem0 _ _ _ _ _ _ _ _ _ _ _ fd W (spZ regs + -184) (f + FILE_BUF_OFF) 0 P [] HJ Htok (conj Hfs (conj Hfd Huniq)) Hfdr).
{ rewrite (Hregs 17%bv). eval_sr_get. reflexivity. }
{ rewrite (Hregs 10%bv). eval_sr_get. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact HE47. }
{ rewrite (Hregs 12%bv). eval_sr_get. rewrite denot_lit_U, U_iovcnt, (U_atom _ 37 _ HE37), (U_atom _ 39 _ HE39) by lia.
destruct (Z.eqb_spec (f + FILE_BUF_OFF + p) (f + FILE_BUF_OFF)); [lia | reflexivity]. }
{ rewrite (Hregs 11%bv). eval_sr_get. cbn [sv_denot]. rewrite HE2, Hspw. reflexivity. }
{ lia. } { lia. }
{ exact M0. } { exact L0. }
{ replace (spZ regs + -184 + 16) with (spZ regs + -168) by lia. exact M1. }
{ replace (spZ regs + -184 + 24) with (spZ regs + -168 + 8) by lia. exact L1. }
{ exact HGP0. } { apply garr8_nil. } { lia. } { fold p. lia. } { lia. } { cbn [length Z.of_nat]. lia. }
{ fold p. cbn [length Z.of_nat]. change MAX_RW_COUNT with 2147479552. lia. }
{ fold p. cbn [length Z.of_nat]. rewrite length_app, Nat2Z.inj_add in Hmax. fold p in Hmax. lia. }
intros md1 HJ1 Hos1. cbn [ss_pc].
assert (HUrem : U E0 (SAlu ALU_ADD (SOff 37 0) (SMd M_MUL (SOff 39 0) (SLit 18446744073709551615))) = p).
{ rewrite U_sub_form_gen; [| reflexivity | rewrite ?(U_atom _ 37 _ HE37), ?(U_atom _ 39 _ HE39) by lia; lia].
rewrite ?(U_atom _ 37 _ HE37), ?(U_atom _ 39 _ HE39) by lia. lia. }
resume_reg_sr ubs0segs (22%bv : reg).
{ rewrite denot_lit_U, HUrem. f_equal. fold p. cbn [length Z.of_nat]. lia. }
jrunE LAWS ubs0tbl_ok HS HJ1.
{ wr_normE. apply Hwr0; [exact HE2 | exact HE10]. }
jbranch ubs0tbl HS.
2:{ exfalso. rewrite branch_ltu_U, HUrem, U_lit in Hc by lia. destruct (Z.ltb_spec p 18446744073709547521); [discriminate Hc | lia]. }
clear Hc.
jrunE LAWS ubs0tbl_ok HS HJ1.
{ wr_normE. apply Hwr0; [exact HE2 | exact HE10]. }
clear M0 L0 M1 L1 Hk2 HGP0. clear HJ. rename HJ1 into HJ.
rewrite app_nil_r in Hos1. rename Hos1 into Hos.
sym_ecall_open HS.
match goal with HFx : frame_of _ _ _ (ms_mem (pend_at ?r ?pc ?m ?ro)) |- _ => change (ms_mem (pend_at r pc m ro)) with m in HFx, HJ end.
lazymatch goal with |- SR _ (mkCfg (pend_at ?rX _ ?mX _) _) _ => lazymatch type of Hos with sink_os _ _ ?wp =>
apply (J_close_node ubs0_msyms MR LAWS rX _ mX _ _ _ _ _ _ _ _ _ _ _ fd wp HJ Htok Hos Hfdr) end end.
{ rewrite (Hregs 17%bv). eval_sr_get. reflexivity. }
{ rewrite (Hregs 10%bv). eval_sr_get. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact HE47. }
intros md' HJ' Hnm' Hfs'. cbn [ss_pc].
resume_sv_sr ubs0segs (SLit 0).
{ reflexivity. }
jrunE_to LAWS ubs0tbl_ok HS HJ' 0x18244.
{ wr_normE. apply Hwr0; [exact HE2 | exact HE10]. }
jrunE_to LAWS ubs0tbl_ok HS HJ' ubs0_A_free.
{ wr_normE. apply Hwr0; [exact HE2 | exact HE10]. }
pose proof (mem_ok_region _ _ _ _ _ (st_ok_mem_ok _ _ _ _ HS) ltac:(do 6 right; left; reflexivity)) as (_ & _ & _ & Hcsh).
cbn [r_base r_chunks base_val] in Hcsh.
lazymatch type of HS with st_ok _ _ _ ?msF =>
assert (Hhead0 : val_mem ubs0segs (ms_mem msF) 332136 8 0)
by (inversion Hcsh as [|c cs Hc0 _]; subst;
exact (val_of_chunk_ok ubs0segs _ _ 0 332136 8 (SLit 0) 0 Hc0 eq_refl ltac:(vm_compute; split; congruence) ltac:(vm_compute; congruence))) end.
jreg HS (10%bv:reg) as Hr10. rewrite HE10 in Hr10.
jreg HS (4%bv:reg) as Hr4. jreg HS (1%bv:reg) as Hr1.
eapply SR_bind.
{ eapply (jfree_sub_res ubs0_msyms MR LAWS ubs0_errno_low_f IMG (aa_free API)) with (a := f) (n := FILE_BLOCK) (o := -48) (b := b);
[ exact HS | reflexivity | reflexivity | exact HJ' | exact Hfin | lia | exact HRb | exact Hr10
| exact (st_ok_reg _ _ _ _ 2%bv HS) | exact HE2 | exact Hspw | reflexivity | lia | lia
| exact Hr4 | exact HE4 | exact Hr1 | apply ret_ok_even; vm_compute; reflexivity
| intros i Hi; exists (f, f + FILE_BLOCK); split; [right; left; reflexivity | cbn; lia] ]. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HJin & HP2 & Hrm & Hkeep & Hhi2 & HRES).
replace (rb_free b FILE_BLOCK) with b in HRES by reflexivity.
jafter_call2 HS 64%nat regs2 mem2 HP2 (-48) (@nil nat) HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor].
eapply (region_kept_stack ubs0segs _ _ _ 2); [rewrite HE2; exact Hspw | exact Hhi2 | lia | lia | lia | lia | lia]. }
clear HS. rename HS2 into HS.
jrun LAWS ubs0tbl_ok HS HJ2.
{ wr_norm. eapply wr_ok_cons_stack; [reflexivity | ew_havoc; rewrite HE2; exact Hspw | cbn; lia | cbn; lia | apply wr_ok_nil]. }
assert (HA64 : env_agree 32 (Ereg regs (map (Z_to_bv 64) vals ++ [Z_to_bv 64 g])) (havoc E0 64 (map (getr regs2) CLOB)))
by (eapply (env_agree_havoc_ge 32); [lia | exact HA0]).
pose proof (regs_preserved_of_st_ok _ _ _ _ _ _ HS HA64 ltac:(vm_compute; reflexivity)) as HPR.
jreg HS (10%bv:reg) as Hq10. jreg HS (1%bv:reg) as Hq1.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2)) as (Hh' & Hlz' & _).
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | exact Hh' | exact Hlz' | exact HS | reflexivity | vm_compute; reflexivity |].
lazymatch type of HS with st_ok _ _ _ ?msx => exists L2, A2, (ms_regs msx), (ms_mem msx), md2 end.
rewrite Hq1, HE1, Hra. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HPR|]. split; [exact Hq10|].
split; [eapply perm_after_rm1; [exact HB | exact Hrm]|].
destruct HJin as (_ & HosIn & _ & _ & _ & _ & _ & HimgIn).
assert (Hntok : ~ sink_open_fp [(f, f + FILE_BLOCK)]) by (intros (r & [<-|[]] & Hr); cbn [fst snd] in Hr; lia).
destruct (os_step_shielded _ _ _ HosIn Hntok) as (Efd & Efs & _).
split; [|split; [rewrite Efs, Hfs'; exact (proj1 Hos) | exact HRES]].
split; [exact (ubs0_stdio_env_kept _ _ _ (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HJ2))))))) Henv)|].
split; [|rewrite Efd; exact Hnm'].
apply (val_mem_word_mem ubs0segs). eapply (val_mem_frame ubs0_msyms); [|exact Hhead0].
intros x Hx. change (Z.of_nat 8) with 8 in Hx. change sk_ofl_head with 332136 in Hx.
match goal with HFx : frame_of _ [_] (ms_mem ?m1) (ms_mem ?m2) |- mbyte _ (ms_mem ?m2) _ = _ =>
transitivity (mbyte ubs0segs (ms_mem m1) x);
[ unfold mbyte; rewrite (HFx (Z_to_bv 64 x)); [reflexivity|];
rewrite unsigned_lit_small by lia; intros (r & [<-|[]] & Hr); cbn [r_base r_wlo r_whi base_val] in Hr;
rewrite ew_havoc_old in Hr by (cbv; lia); rewrite HE2, Hspw in Hr; lia
| ] end.
cbn [ms_mem mkst].
assert (Hex : env_addr x) by (left; change sk_ofl_head with 332136; lia).
destruct (skl_env ubs0_msyms x Hex) as (T1 & T2 & T3 & T4).
apply (HimgIn x T1 T2 T3 T4). intros [Ho _]. exact (Hntok Ho).
}
remember (file_vals f fd 0 0 0 0) as vals eqn:Hvals.
remember (Ereg regs (map (Z_to_bv 64) vals ++ [Z_to_bv 64 g])) as E0 eqn:HE0.
assert (HA0 : env_agree 32 (Ereg regs (map (Z_to_bv 64) vals ++ [Z_to_bv 64 g])) E0) by (rewrite HE0; apply env_agree_refl).
assert (HEv : forall j v, nth_error vals j = Some v -> ew E0 (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HE2 : ew E0 2 = getr regs 2) by (subst E0; apply (ew_Ereg_nat regs _ 2 2%bv); vm_compute; reflexivity).
assert (HE1 : ew E0 1 = getr regs 1) by (subst E0; apply (ew_Ereg_nat regs _ 1 1%bv); vm_compute; reflexivity).
assert (HE10 : ew E0 10 = Z_to_bv 64 f) by (subst E0; rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity); exact H10).
assert (HE4 : ew E0 4 = Z_to_bv 64 (ms_tp ubs0_msyms)) by (subst E0; rewrite (ew_Ereg_nat regs _ 4 4%bv) by (vm_compute; reflexivity); exact Htp).
assert (HE43 : ew E0 43 = Z_to_bv 64 (f + FILE_BUF_OFF)) by (apply (HEv 11%nat); rewrite Hvals; reflexivity).
assert (HE47 : ew E0 47 = Z_to_bv 64 fd) by (apply (HEv 15%nat); rewrite Hvals; reflexivity).
assert (HE63 : ew E0 63 = Z_to_bv 64 g).
{ subst E0. rewrite (ew_Ereg_extra regs _ 31). rewrite Hvals. reflexivity. }
set (ms0 := mkst regs (Z_to_bv 64 ubs0_A_fclose) mem (seg_rom ubs0segs)).
pose proof (journal_init ubs0_msyms MR FCLOSE_STK (sink_fp f) L A regs mem md HPRE) as HJ.
change mem with (ms_mem ms0) in HJ.
assert (HS : st_ok ubs0segs E0 (ss_fc false) ms0).
{ rewrite HE0. apply entry_st_ok_full; rewrite <- ?HE0.
- rewrite HE0. apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]]].
+ apply (region_ok_stack ubs0segs _ mem 2 (spZ regs)); [| unfold FC_DEPTH; lia | lia | intros a Ha; apply Hstw; unfold FC_DEPTH in Ha; lia].
rewrite HE2. exact Hspw.
+ eapply (region_ok_obj_gen ubs0segs E0 mem 10 f FILE_HDR 0 FILE_HDR LAY_FILE vals 32 (lits_FILE false));
[ rewrite HE10; apply unsigned_lit_small; lia | lia | lia | exact Hobj | reflexivity | exact HEv | | ].
* intros j z Hj. rewrite Hvals.
do 31 (destruct j as [|j]; [cbn in Hj; first [discriminate Hj | injection Hj as <-; reflexivity] |]).
destruct j; discriminate Hj.
* intros i Hi. apply (present_writable ubs0_msyms).
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ f FILE_BLOCK i HH Hfin ltac:(lia))).
+ unfold region_ok, reg_got. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [intros o Ho; lia|].
constructor; [|constructor].
eapply (chunk_ok_val ubs0segs E0 mem 0 ubs0_D_got_stack_chk_guard 8 (SLit ubs0_D_stack_chk_guard) ubs0_D_stack_chk_guard);
[reflexivity | vm_compute; split; congruence | vm_compute; congruence | ].
apply (val_mem_word_mem ubs0segs). exact Hgot.
+ unfold region_ok, reg_guard. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [intros o Ho; lia|].
constructor; [|constructor].
eapply (chunk_ok_val ubs0segs E0 mem 0 ubs0_D_stack_chk_guard 8 (SOff 63%nat 0) g);
[cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact HE63 | change (8 * Z.of_N 8) with 64; exact Hg0 | vm_compute; congruence | ].
apply (val_mem_word_mem ubs0segs). exact Hguard.
+ unfold region_ok, reg_needlocks. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [intros o Ho; lia|].
constructor; [|constructor].
eapply (chunk_ok_val ubs0segs E0 mem 0 (ubs0_D_libc + 3) 1 (SLit 0) 0); [reflexivity | vm_compute; split; congruence | vm_compute; congruence | ].
intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite !Z.add_0_r. exact Hnl.
+ unfold region_ok, reg_ofl_lock. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [intros o Ho; lia|].
constructor; [|constructor].
eapply (chunk_ok_val ubs0segs E0 mem 0 ubs0_D_ofl_lock 4 (SLit 0) 0); [reflexivity | vm_compute; split; congruence | vm_compute; congruence | exact Hlock].
+ unfold region_ok, reg_ofl_head. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|].
split; [intros o Ho; apply ubs0_head_writable; change ubs0_D_ofl_head with 332136 in Ho; lia|].
constructor; [|constructor].
eapply (chunk_ok_val ubs0segs E0 mem 0 ubs0_D_ofl_head 8 (SOff 10%nat 0) f);
[cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact HE10 | change (8 * Z.of_N 8) with 64; lia | vm_compute; congruence | ].
apply (val_mem_word_mem ubs0segs). exact Hhead.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, reg_fc_stack, reg_fc_file, reg_got, reg_guard, reg_needlocks, reg_ofl_lock, reg_ofl_head.
cbn [r_base r_lo r_hi base_val]. rewrite HE2, HE10, Hspw, !unsigned_lit_small by lia.
change ubs0_D_got_stack_chk_guard with 128824. change ubs0_D_stack_chk_guard with 331032. change ubs0_D_libc with 331064.
change ubs0_D_ofl_lock with 332128. change ubs0_D_ofl_head with 332136. unfold FC_DEPTH.
repeat split; lia.
- split; [|split; [exact I|exact I]].
cbn [f_atoms atoms_ok fc_facts app]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE2, HE10, HE43, HE47, Hspw, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
assert (Hos : sink_os md fd (W ++ [])) by (rewrite app_nil_r; exact (conj Hfs (conj Hfd Huniq))).
jrunE LAWS ubs0tbl_ok HS HJ.
{ wr_normE. apply Hwr0; [exact HE2 | exact HE10]. }
sym_ecall_open HS.
match goal with HFx : frame_of _ _ _ (ms_mem (pend_at ?r ?pc ?m ?ro)) |- _ => change (ms_mem (pend_at r pc m ro)) with m in HFx, HJ end.
lazymatch goal with |- SR _ (mkCfg (pend_at ?rX _ ?mX _) _) _ => lazymatch type of Hos with sink_os _ _ ?wp =>
apply (J_close_node ubs0_msyms MR LAWS rX _ mX _ _ _ _ _ _ _ _ _ _ _ fd wp HJ Htok Hos Hfdr) end end.
{ rewrite (Hregs 17%bv). eval_sr_get. reflexivity. }
{ rewrite (Hregs 10%bv). eval_sr_get. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact HE47. }
intros md' HJ' Hnm' Hfs'. cbn [ss_pc].
resume_sv_sr ubs0segs (SLit 0).
{ reflexivity. }
jrunE_to LAWS ubs0tbl_ok HS HJ' 0x18244.
{ wr_normE. apply Hwr0; [exact HE2 | exact HE10]. }
jrunE_to LAWS ubs0tbl_ok HS HJ' ubs0_A_free.
{ wr_normE. apply Hwr0; [exact HE2 | exact HE10]. }
pose proof (mem_ok_region _ _ _ _ _ (st_ok_mem_ok _ _ _ _ HS) ltac:(do 6 right; left; reflexivity)) as (_ & _ & _ & Hcsh).
cbn [r_base r_chunks base_val] in Hcsh.
lazymatch type of HS with st_ok _ _ _ ?msF =>
assert (Hhead0 : val_mem ubs0segs (ms_mem msF) 332136 8 0)
by (inversion Hcsh as [|c cs Hc0 _]; subst;
exact (val_of_chunk_ok ubs0segs _ _ 0 332136 8 (SLit 0) 0 Hc0 eq_refl ltac:(vm_compute; split; congruence) ltac:(vm_compute; congruence))) end.
jreg HS (10%bv:reg) as Hr10. rewrite HE10 in Hr10.
jreg HS (4%bv:reg) as Hr4. jreg HS (1%bv:reg) as Hr1.
eapply SR_bind.
{ eapply (jfree_sub_res ubs0_msyms MR LAWS ubs0_errno_low_f IMG (aa_free API)) with (a := f) (n := FILE_BLOCK) (o := -48) (b := b);
[ exact HS | reflexivity | reflexivity | exact HJ' | exact Hfin | lia | exact HRb | exact Hr10
| exact (st_ok_reg _ _ _ _ 2%bv HS) | exact HE2 | exact Hspw | reflexivity | lia | lia
| exact Hr4 | exact HE4 | exact Hr1 | apply ret_ok_even; vm_compute; reflexivity
| intros i Hi; exists (f, f + FILE_BLOCK); split; [right; left; reflexivity | cbn; lia] ]. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HJin & HP2 & Hrm & Hkeep & Hhi2 & HRES).
replace (rb_free b FILE_BLOCK) with b in HRES by reflexivity.
jafter_call2 HS 64%nat regs2 mem2 HP2 (-48) (@nil nat) HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor].
eapply (region_kept_stack ubs0segs _ _ _ 2); [rewrite HE2; exact Hspw | exact Hhi2 | lia | lia | lia | lia | lia]. }
clear HS. rename HS2 into HS.
jrun LAWS ubs0tbl_ok HS HJ2.
{ wr_norm. eapply wr_ok_cons_stack; [reflexivity | ew_havoc; rewrite HE2; exact Hspw | cbn; lia | cbn; lia | apply wr_ok_nil]. }
assert (HA64 : env_agree 32 (Ereg regs (map (Z_to_bv 64) vals ++ [Z_to_bv 64 g])) (havoc E0 64 (map (getr regs2) CLOB)))
by (eapply (env_agree_havoc_ge 32); [lia | exact HA0]).
pose proof (regs_preserved_of_st_ok _ _ _ _ _ _ HS HA64 ltac:(vm_compute; reflexivity)) as HPR.
jreg HS (10%bv:reg) as Hq10. jreg HS (1%bv:reg) as Hq1.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2)) as (Hh' & Hlz' & _).
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | exact Hh' | exact Hlz' | exact HS | reflexivity | vm_compute; reflexivity |].
lazymatch type of HS with st_ok _ _ _ ?msx => exists L2, A2, (ms_regs msx), (ms_mem msx), md2 end.
rewrite Hq1, HE1, Hra. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HPR|]. split; [exact Hq10|].
split; [eapply perm_after_rm1; [exact HB | exact Hrm]|].
destruct HJin as (_ & HosIn & _ & _ & _ & _ & _ & HimgIn).
assert (Hntok : ~ sink_open_fp [(f, f + FILE_BLOCK)]) by (intros (r & [<-|[]] & Hr); cbn [fst snd] in Hr; lia).
destruct (os_step_shielded _ _ _ HosIn Hntok) as (Efd & Efs & _).
split; [|split; [rewrite Efs, Hfs'; exact (proj1 Hos) | exact HRES]].
split; [exact (ubs0_stdio_env_kept _ _ _ (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HJ2))))))) Henv)|].
split; [|rewrite Efd; exact Hnm'].
apply (val_mem_word_mem ubs0segs). eapply (val_mem_frame ubs0_msyms); [|exact Hhead0].
intros x Hx. change (Z.of_nat 8) with 8 in Hx. change sk_ofl_head with 332136 in Hx.
match goal with HFx : frame_of _ [_] (ms_mem ?m1) (ms_mem ?m2) |- mbyte _ (ms_mem ?m2) _ = _ =>
transitivity (mbyte ubs0segs (ms_mem m1) x);
[ unfold mbyte; rewrite (HFx (Z_to_bv 64 x)); [reflexivity|];
rewrite unsigned_lit_small by lia; intros (r & [<-|[]] & Hr); cbn [r_base r_wlo r_whi base_val] in Hr;
rewrite ew_havoc_old in Hr by (cbv; lia); rewrite HE2, Hspw in Hr; lia
| ] end.
cbn [ms_mem mkst].
assert (Hex : env_addr x) by (left; change sk_ofl_head with 332136; lia).
destruct (skl_env ubs0_msyms x Hex) as (T1 & T2 & T3 & T4).
apply (HimgIn x T1 T2 T3 T4). intros [Ho _]. exact (Hntok Ho).
Qed.
End S.
End d.
