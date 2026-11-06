(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open ReadWrite.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s YK0p YP0n YP0o.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP0h YP01.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YH00 YH03 YH02.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI06 YI16 YI00 YI14 YI07 YI19 YI18 YI1a YI5b YI5c YN3j.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma src0_errno_low_u : errno_addr src0_msyms + 4 <= alloc_ceiling.
Proof. pose proof (proj1 alloc_ceiling_val). enough (errno_addr src0_msyms + 4 <= CEIL_MIN) by lia. vm_compute. intros H'. discriminate H'. Qed.
Definition ss_unlink0 : sstate :=
mkSS src0_A_unlink sr_atoms
[ YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0 [];
YP09.mkRegion (Some 4%nat) (-164) (-160) (-164) (-160) [] ]
None (mkFacts [ (2%nat, mkAF (CEIL_MIN + UNLINK_STK) (2^63) 4) ] [] []).
Section S.
Variable API : AllocAPI src0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src0_msyms MR.
Theorem src0_unlinkX : unlink_x src0_msyms MR src0_A_unlink.
Proof.
intros L A regs mem md TA TB HPRE H10 HSN KA KB.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HSTKv : UNLINK_STK = 64) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
pose proof src0_errno_low_u as Hel.
assert (Htpn : ms_tp src0_msyms = 197008) by reflexivity.
assert (Heav : errno_addr src0_msyms = 196844) by reflexivity.
remember (Ereg regs []) as E0 eqn:HE0.
assert (HA0 : env_agree 32 (Ereg regs []) E0) by (rewrite HE0; apply env_agree_refl).
assert (HE2 : ew E0 2 = getr regs 2) by (subst E0; apply (ew_Ereg_nat regs _ 2 2%bv); vm_compute; reflexivity).
assert (HE1 : ew E0 1 = getr regs 1) by (subst E0; apply (ew_Ereg_nat regs _ 1 1%bv); vm_compute; reflexivity).
assert (HE4 : ew E0 4 = Z_to_bv 64 (ms_tp src0_msyms)) by (subst E0; rewrite (ew_Ereg_nat regs _ 4 4%bv) by (vm_compute; reflexivity); exact Htp).
assert (HE10 : ew E0 10 = Z_to_bv 64 sk_path_addr) by (subst E0; rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity); exact H10).
assert (Hspw : bv_unsigned (getr regs 2) = spZ regs) by reflexivity.
assert (Htpv : bv_unsigned (Z_to_bv 64 (ms_tp src0_msyms)) = 197008) by (vm_compute; reflexivity).
set (ms0 := mkst regs (Z_to_bv 64 src0_A_unlink) mem (seg_rom src0segs)).
pose proof (journal_init src0_msyms MR UNLINK_STK [sink_token] L A regs mem md HPRE) as HJ.
change mem with (ms_mem ms0) in HJ.
assert (HS : st_ok src0segs E0 ss_unlink0 ms0).
{ rewrite HE0. apply entry_st_ok_full; rewrite <- ?HE0.
- rewrite HE0. apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ apply (region_ok_stack src0segs _ mem 2 (spZ regs)); [| lia | lia | intros a Ha; apply Hstw; lia].
rewrite HE2. exact Hspw.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HE4, Htpv.
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply Herr. rewrite Heav. lia.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HE2, HE4, Hspw, Htpv. repeat split; lia.
- split; [|split; [exact I|exact I]].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE2, Hspw. change (2 ^ 4) with 16. repeat split; lia. }
assert (Hwr0 : forall E' cs1 cs2, ew E' 2 = getr regs 2 -> ew E' 4 = Z_to_bv 64 (ms_tp src0_msyms) ->
wr_okE src0_msyms E' [YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0 cs1; YP09.mkRegion (Some 4%nat) (-164) (-160) (-164) (-160) cs2]
UNLINK_STK (spZ regs) [sink_token] (blocks L A) (blocks L A)).
{ intros E' cs1 cs2 HE2' HE4'.
apply wr_okE_cons_ok; [eapply wr_ok_cons_stack; [reflexivity | rewrite HE2'; exact Hspw | cbn; lia | cbn; lia | apply wr_ok_nil] |].
eapply wr_okE_cons_errno; [reflexivity | rewrite HE4'; exact Htpv | cbn; lia | cbn; lia | apply wr_okE_nil]. }
apply realizes_via_SR.
jrunE LAWS src0tbl_ok HS HJ.
{ wr_normE. apply Hwr0; [exact HE2 | exact HE4]. }
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
sym_ecall_open HS.
lazymatch type of HF with frame_of _ _ _ (ms_mem (pend_at ?r ?p ?m ?ro)) => change (ms_mem (pend_at r p m ro)) with m in HF, HJ end.
unfold ms0 in HF, HJ, HG; cbn [ms_mem mkst] in HF, HJ, HG.
destruct HSN as (Henv & Hhead & Hfdn).
assert (Henva : forall a, env_addr a -> 0 <= a < alloc_ceiling /\ ~ (196844 <= a < 196848)).
{ intros a Ha. unfold env_addr in Ha.
change sk_ofl_head with 0x50848 in Ha. change sk_threaded with (0x50418 + 1) in Ha.
change sk_path_addr with 0x10304 in Ha. change sk_mode_addr with 0x102a2 in Ha. change sk_trailer_addr with 0x10311 in Ha. change sk_ofl_lock with 0x50840 in Ha.
change sk_rwa_addr with 0x10390 in Ha. change sk_highs_addr with 0x103b8 in Ha. change sk_ones_addr with 0x103c8 in Ha. lia. }
assert (HfrK : forall E' cs1 cs2 (m m' : word -> option byte), ew E' 2 = getr regs 2 -> ew E' 4 = Z_to_bv 64 (ms_tp src0_msyms) ->
frame_of E' [YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0 cs1; YP09.mkRegion (Some 4%nat) (-164) (-160) (-164) (-160) cs2] m m' ->
forall a, env_addr a -> mbyte src0segs m' a = mbyte src0segs m a).
{ intros E' cs1 cs2 m m' H2' H4' HF' a Ha. destruct (Henva a Ha) as [Ha1 Ha2].
unfold mbyte. rewrite (HF' (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. intros (r & Hin & Hr).
destruct Hin as [<-|[<-|[]]]; cbn [r_base r_wlo r_whi base_val] in Hr; rewrite ?H2', ?H4', ?Hspw, ?Htpv in Hr; lia. }
assert (HsnK : forall (m' : word -> option byte) md', (forall a, env_addr a -> mbyte src0segs m' a = mbyte src0segs mem a) ->
m_fds md' = m_fds md -> sink_none src0_msyms m' md').
{ intros m' md' Hm Hf. split; [exact (stdio_env_frame src0_msyms mem m' Hm Henv)|]. split; [|rewrite Hf; exact Hfdn].
apply (val_mem_word_mem src0segs). apply (val_mem_word_mem src0segs) in Hhead.
eapply (val_mem_frame src0_msyms); [|exact Hhead]. intros x Hx. apply Hm. left. change (Z.of_nat 8) with 8 in Hx. lia. }
pose proof (HfrK _ _ _ _ _ HE2 HE4 HF) as Hfr1.
assert (Henv0 : stdio_env src0_msyms mem0) by exact (stdio_env_frame src0_msyms mem mem0 Hfr1 Henv).
assert (Htok : sink_open_fp [sink_token]) by (apply sink_open_token; left; reflexivity).
apply SR_ret. apply (JX_unlink_node src0_msyms MR LAWS regs0 _ mem0 _ _ _ _ _ _ _ _ _ _ TA TB HJ Htok Henv0 Hfdn).
{ rewrite (Hregs 17%bv). eval_sr_get. reflexivity. }
{ rewrite (Hregs 10%bv). eval_sr_get. apply bv_eq. vm_compute. reflexivity. }
{ rewrite (Hregs 12%bv). eval_sr_get. reflexivity. }
{ rewrite (Hregs 11%bv). eval_sr_get. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact HE10. }
-
intros e He. pose proof HJ as HJ'. apply realizes_via_SR. cbn [ss_pc].
pose proof (unlink_errnos_range e He) as Her. pose proof (errno_ret_unsigned e Her) as Heu.
resume_atom_sr src0segs 32%nat (mkAF (2 ^ 64 - 4095) (2 ^ 64 - 1) 0).
{ cbn [af_lo af_hi]. rewrite Heu. lia. }
{ cbn [af_al2]. lia. }
{ cbn [af_al2]. change (2 ^ 0) with 1. apply Z.mod_1_r. }
jrunE LAWS src0tbl_ok HS HJ'.
{ wr_normE. apply Hwr0; (rewrite ew_ewset_other by lia); [exact HE2 | exact HE4]. }
assert (HA32 : env_agree 32 (Ereg regs []) (ewset E0 32 (errno_ret e))) by (eapply env_agree_trans; [exact HA0 | apply env_agree_ewset]).
pose proof (regs_preserved_of_st_ok _ _ _ _ _ _ HS HA32 ltac:(vm_compute; reflexivity)) as HPR.
jreg HS (1%bv:reg) as Hr1.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ')) as (Hh' & Hlz' & _).
eapply (SR_ret_at src0segs src0tbl); [exact src0tbl_ok | exact Hh' | exact Hlz' | exact HS | reflexivity | vm_compute; reflexivity |].
apply KA. exists (ms_regs ms), (ms_mem ms), md.
rewrite Hr1, (ew_ewset_other E0 32 _ 1 ltac:(lia)), HE1, Hra.
split; [reflexivity|]. split; [exact HJ'|]. split; [exact HPR|].
split.
{ apply HsnK; [|reflexivity]. intros a Ha.
assert (HE2' : ew (ewset E0 32 (errno_ret e)) 2 = getr regs 2) by (rewrite ew_ewset_other by lia; exact HE2).
assert (HE4' : ew (ewset E0 32 (errno_ret e)) 4 = Z_to_bv 64 (ms_tp src0_msyms)) by (rewrite ew_ewset_other by lia; exact HE4).
rewrite (HfrK _ _ _ _ _ HE2' HE4' HF0 a Ha).
exact (Hfr1 a Ha). }
split; reflexivity.
-
intros md' HJ' Hfds' Hfs' Hheld. apply realizes_via_SR. cbn [ss_pc].
resume_sv_sr src0segs (SLit 0).
{ reflexivity. }
jrunE LAWS src0tbl_ok HS HJ'.
{ wr_normE. apply Hwr0; [exact HE2 | exact HE4]. }
pose proof (regs_preserved_of_st_ok _ _ _ _ _ _ HS HA0 ltac:(vm_compute; reflexivity)) as HPR.
jreg HS (1%bv:reg) as Hr1.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ')) as (Hh' & Hlz' & _).
eapply (SR_ret_at src0segs src0tbl); [exact src0tbl_ok | exact Hh' | exact Hlz' | exact HS | reflexivity | vm_compute; reflexivity |].
apply KB. exists (ms_regs ms), (ms_mem ms), md'.
rewrite Hr1, HE1, Hra.
split; [reflexivity|]. split; [exact HJ'|]. split; [exact HPR|].
split.
{ apply HsnK; [|exact Hfds']. intros a Ha. rewrite (HfrK _ _ _ _ _ HE2 HE4 HF0 a Ha). exact (Hfr1 a Ha). }
split; [exact Hfds'|]. split; [exact Hfs' | exact Hheld].
Qed.
End S.
End b.
