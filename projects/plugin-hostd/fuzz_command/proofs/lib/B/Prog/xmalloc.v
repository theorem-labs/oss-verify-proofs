(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of xmalloc on the ASan+UBSan build of plugin-hostd/fuzz_command
   (image fuzz_command.asan-ubsan), in the shape of cgif_file_fuzzer's walks (lib/A/ACb8.v, lib/A/ACh2.v): the
   symbolic executor over the position-abstract listing (CmdPaLib.v, PaLibF.v, PaCallRun.v) and the malloc call
   through amalloc04_sub (PaCall.v). It is the malloc call and the null edge of the A side's xstrdup walk
   (lib/A/Prog/xstrdup.v), which A inlines and B keeps as its own function. *)
(* The walk proves txmalloc_spec (xmalloc_c.v) from the statement's own hypothesis AMALLOC4 (fx-generic, applied at
   this section's fx) and TL (the malloc trampoline is the malloc rule's entry, CmdPaLib.v pal_malloc). The code
   (0x899b4..0x899e0): the 16-byte frame (ra at sp + 8), n ? n : 1 (`seqz a1,a0; add a0,a0,a1`), the malloc wrapper
   call, the null check `beqz a0` (not taken: the malloc rule gives a block at or above 4096, so the
   `__asan_handle_no_return` / abort stubs and the `unimp` after them are not reached), the epilogue and ret. s0 is
   the caller's at the malloc call: the wrapper's chain_pre is the entry's achain (afn_pre), kept by the prologue
   (it writes only below the entry sp), through achain_chain_pre. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaLibF PaLibG PaLibH PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep xmalloc_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* n ? n : 1 as the code computes it (`seqz a1,a0; add a0,a0,a1`, unsigned, no wrap for n < 2 ^ 64) *)
Lemma xm_seqz_add : forall a, 0 <= a < 2 ^ 64 ->
alu64 ALU_ADD (Z_to_bv 64 a) (alu64 ALU_SLTU (Z_to_bv 64 a) (Z_to_bv 64 1)) = Z_to_bv 64 (Z.max a 1).
Proof.
intros a Ha. destruct (Z.eq_dec a 0) as [->|Hne]; [apply bv_eq; vm_compute; reflexivity|].
rewrite Z.max_l by lia.
apply bv_eq. rewrite alu64_unsigned. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
replace (a <? 1) with false by (symmetry; apply Z.ltb_ge; lia). unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small 0) by lia. rewrite Z.add_0_r. apply Z.mod_small. lia.
Qed.
Lemma not_inFP_nil : forall a, ~ inFP [] a.
Proof. intros a (r & Hr & _). destruct Hr. Qed.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the symbolic state at the entry: every register its own atom, the 16-byte frame below sp writable, sp 16-aligned *)
Definition xm_ss0 : sstate := mkSS AF_xmalloc sr_atoms [stack_region 16] None (mkFacts [(2%nat, mkAF (2^46) (2^47) 4)] [] []).
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
(* the symbolic state xm_ss0 holds of the entry configuration *)
Lemma xm_seed : forall W regs mem ly S md ch, afn_pre SEGS B XMALLOC_STK ly S W regs mem md ch ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) xm_ss0 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_xmalloc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem ly S md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HXS : XMALLOC_STK = 16400) by reflexivity.
assert (E2 : bv_unsigned (ew (Eimg (Ereg regs [])) 2) = spZ regs) by (rewrite (ew_Eimg_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
rewrite restrict_mkst_fx. unfold xm_ss0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil. unfold region_ok, stack_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite E2.
  change (2 ^ 4) with 16. lia.
Qed.
Variable MT : ameter_ops.
(* the statement's runtime hypothesis (xmalloc_c.v, Section e), fx-generic *)
Hypothesis AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc SK SEGS B MT.
(* the malloc trampoline the listing calls is the malloc rule's entry (pal_malloc) *)
Hypothesis TL : PALib B.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let BR := paj_branch (PI := PI). Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).
(* the walk: the prologue and n ? n : 1, malloc, the null check (not taken: the block is at or above 4096), the
   epilogue and ret *)
Theorem txmalloc_spec_holds : txmalloc_spec B MT.
Proof.
unfold txmalloc_spec. intros ly S W regs mem md ch n HPRE H10 Hn Hev Hlive MOK.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HXS : XMALLOC_STK = 16400) by reflexivity.
pose proof (@pa_B_ok _ _ PI) as HBASE. pose proof (pa_base_lo (L := cmd_listing)) as HBLO.
assert (Has : ASTACK = 16384) by reflexivity.
assert (HMM : 1 < MALLOC_MAX) by (unfold MALLOC_MAX; lia).
pose proof (xm_seed W regs mem ly S md ch HPRE) as HS.
pose proof (ajournal_init SEGS B XMALLOC_STK [] ly S W regs mem md ch HPRE) as HJ.
set (E := Eimg (Ereg regs [])) in HS. assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Eimg_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n0 r Hn1; subst E; apply ew_Eimg_Ereg_nat; exact Hn1).
unfold cfg_at. change (w64 (BASE + AF_xmalloc)) with (Z_to_bv 64 (BASE + AF_xmalloc)).
(* the prologue, n ? n : 1, and the call of the malloc wrapper *)
paj_run_shc RUNP RUNC HS HJ.
{ awr_ok_tac. exact Usp. }
pmkst HS.
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8.
assert (Hsp1 : spZ (ms_regs ms) = spZ regs + -16).
{ unfold spZ at 1. rewrite R2, Usp. rewrite unsigned_lit_small by lia. reflexivity. }
lazymatch goal with Hfr : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ =>
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - XMALLOC_STK <= a < spZ regs) -> rdW W (ms_mem ms) a = rdW W mem a)
by (intros a Ha Hna; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - XMALLOC_STK <= a < spZ regs) Hfr);
  [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite Usp in Hrr; rewrite HXS; lia|]);
    destruct Hin
  | exact Ha | exact Hna ]) end.
assert (R10' : getr (ms_regs ms) 10 = w64 (Z.max n 1)).
{ rewrite R10, (EE 10%nat 10%bv eq_refl), H10. unfold w64. apply xm_seqz_add. unfold MALLOC_MAX in Hn. lia. }
ppcs.
eapply SRr_bind.
{ eapply (amalloc04_sub SEGS B LAWS pa_segs_low MT (AMALLOC4 fx) _ (ms_regs ms) (ms_mem ms) XMALLOC_STK (spZ regs) [] ly S W mem md []
    ly S _ 0 (Z.max n 1) (-16) (Z_to_bv 64 (BASE + 13464)) ch HJ).
  - exact R10'.
  - lia.
  - unfold LIVE_XMALLOC in Hlive. exact Hlive.
  - exact Hsp1.
  - reflexivity.
  - lia.
  - rewrite Has, HXS. lia.
  - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold EV_XMALLOC in Hev. lia.
  - (* the caller's s0 and the entry's frame chain: the prologue writes only below the entry sp *)
    apply (achain_chain_pre ly _ (spZ regs) (s0Z regs) ch (ms_regs ms)).
    + apply (achain_kept ly (rdW W mem) _ (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |].
      intros a Ha. apply KEEP1; lia.
    + rewrite Hsp1. lia.
    + unfold s0Z. rewrite R8, (EE 8%nat 8%bv eq_refl). reflexivity.
    + unfold raZ. rewrite R1, unsigned_lit_small by lia. lia.
  - unfold XM_XMALLOC, LIVE_XMALLOC in MOK. exact MOK. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & res & -> & HJ3 & HP3 & Ha03 & Hfrs3 & Hres4096 & Eab3 & HK3 & MLE3 & HJt3).
pose proof (proj1 HJ3) as HAR3.
jafter_call_keep_pi HS 32%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [|apply Forall_nil].
  eapply (region_kept_stack_sub SEGS B); [exact HJt3 | exact HJ3 | exact Usp | lia | rewrite HXS; lia | lia | cbn; lia | cbn; lia | intros a _; apply not_inFP_nil]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E 32 (map (getr regs3) CLOB)) as E3 eqn:HE3 in HS.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD3 : forall n, (n < 32)%nat -> ew E3 n = ew E n) by (intros n0 Hn1; rewrite HE3; apply YN3v.ew_havoc_old; exact Hn1).
assert (E36 : ew E3 36 = getr regs3 10) by (rewrite HE3; reflexivity).
assert (Usp3 : bv_unsigned (ew E3 2) = spZ regs) by (rewrite OLD3 by lia; exact Usp).
clear HE3.
assert (Hres_in : In (res, Z.max n 1) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res (Z.max n 1) HAR3 Hres_in) as (_ & _ & Hrceil & _ & _ & _ & _).
pose proof (req_size_pos (Z.max n 1) ltac:(lia)) as [Hq1 Hq2].
(* the null check: a0 is the block, at or above 4096 *)
psrr_branch_pi RUNP BR HS.
{ exfalso. assert (U36 : U E3 (SOff 36 0) = res) by (apply U_atom; [rewrite E36; exact Ha03 | lia]).
  rewrite branch_eq_U, U_SLit, U36 in Hc. change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc. lia. }
(* the epilogue and ret *)
paj_run_shc RUNP RUNC HS HJ3.
{ awr_ok_tac. exact Usp3. }
prreg HS (10%bv : bv 5) F10. prreg HS (1%bv : bv 5) F1.
eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly3, S3, r, m, d end.
split.
{ rewrite F1, OLD3, (EE 1%nat 1%bv eq_refl) by lia. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split.
{ eapply (ajournal_mono_k SEGS B); [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ3 | unfold EV_XMALLOC; lia]. }
split.
{ unfold aregs_preserved. intros r Hr.
  assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27 \/ False) by (unfold acallee_saved in Hr; lia).
  clear Hr.
  repeat (destruct Hcases as [-> | Hcases]); [..| destruct Hcases];
  rewrite (st_ok_pi_restrict_reg (w_H W3) E3 _ _ _ HS); cbn [ms_regs];
  lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
  cbn [sv_denot]; rewrite OLD3 by lia; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; apply EE; reflexivity. }
exists res.
split; [rewrite F10, E36; exact Ha03|].
split; [lia|].
split; [unfold LIVE_XMALLOC; rewrite Eab3; apply Permutation_sym, Permutation_cons_append|].
split.
{ apply Forall_forall. intros [b m] Hbm. cbn [fst snd].
  assert (Hbm3 : In (b, m) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; left; exact Hbm).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR3 Hbm3) as (_ & _ & _ & _ & _ & _ & Hm).
  pose proof (req_size_pos m (proj1 Hm)) as [Hm1 Hm2].
  apply in_split in Hbm as (l1 & l2 & El).
  pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W3 _ _ (b, m) (res, Z.max n 1) l1 l2 [] HAR3) as Hd.
  rewrite Eab3, El, <- app_assoc in Hd. specialize (Hd eq_refl). unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
  unfold iv_apart, LIVE_XMALLOC. lia. }
split; [exists res, (Z.max n 1); split; [exact Hres_in | unfold LIVE_XMALLOC; lia]|].
split.
{ rewrite (blocks_bytes_bsum B ly3 S3), Eab3, YCbq.bsum_app, <- (blocks_bytes_bsum B ly S).
  unfold LIVE_XMALLOC. cbn [YCbq.bsum fold_right snd]. lia. }
unfold XM_XMALLOC, LIVE_XMALLOC. exact MLE3.
Qed.
End e.
End d.
End b.
