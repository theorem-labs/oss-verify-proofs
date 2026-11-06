(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the head of the top loop of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86654) with no byte left: beqz s8 to the second rec_clear (jal 0x86af0), LT_Z_stmt from the empty rest, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (a segment lemma from one point of the function to the next, its seed lemma cl_seedX). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaSB CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdBase CmdRep CmdObj CmdRo PaCallPg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
rec_clear_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s21.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSnText.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.

(* ---- the symbolic state at the head 0x86654 (LO_LH) with r = 0 ----
   Every register is its own atom (sr_atoms) but s8, pinned to 0, so that beqz s8 is decided; no region, no fact:
   the branch and the jal of rec_clear (0x86af0) read nothing. *)
Definition LZx : sv := SOff 25 0.
Definition LZspan : Z * Z := (LT_SB, LT_SB + 2 ^ 44 - 1).
Definition ss_lz : sstate := mkSS LO_LH sr_atoms [] None (mkFacts [] [] []).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma lz_E_reg : forall regs n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (snt_E regs) n = getr regs rr.
Proof.
intros regs n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold snt_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.

(* the seed: the state at 0x86654 is an instance of ss_lz *)
Lemma lz_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem,
  st_ok_pi SEGS VAL (snt_E regs) ss_lz (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_LH)) mem (seg_rom SEGS))).
Proof.
intros W regs mem. unfold ss_lz. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold snt_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- exact I.
- split; [exact I | split; [exact I | exact I]].
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the walk's hypotheses, with the names of a Theorem Labs lane's RULING-STMT.md section 1 *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis SIGP : cmd_sig_prog.
Let RUN := paj_run B LAWS.

(* ---- 0x86654 with r = 0: beqz s8 is taken, jal rec_clear at 0x86af0 (ra = 0x86af4); LT_Z_stmt with the budget of
   the empty rest, ev_from f R [] = EV_REC_CLEAR R ---- *)
Theorem lh_zero : forall m, LTA_Z B MT ->
  forall cx ly S W regs mem md k acc (R : rstate) (O : list (Z * Z)) (q : Z),
  lt_base B MT cx -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 -> lt_body B cx ly S W regs mem md k m ->
  getr regs 24 = w64 0 ->
  lt_rec B cx ly S W mem R O q [] ->
  lt_bud MT cx S k acc (ev_from (32 - m) R (x_rest cx 0)) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + LO_LH)) mem (seg_rom SEGS)) md) (lt_post B MT cx).
Proof.
intros m HZA cx ly S W regs mem md k acc R O q HB HFP HBody R24 HREC HBUD.
pose proof (HZA fx) as HZ. clear HZA.
pose proof HBody as (HFRM & Hsl & R8 & R9 & R18 & R25 & R26 & R27 & Hm).
pose proof HFRM as (HJ & Hsp & Hgp & Htp & Hsv).
pose proof HREC as (Hrep & Hspill & H2 & Hq & Hq0 & Hperm).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & HLEN & _).
pose proof (lz_seed W regs mem) as HS0.
pose proof (st_ok_pi_pin_reg' _ _ _ (24%bv : bv 5) 0 HS0 R24 eq_refl) as HS. clear HS0.
assert (HEI : img_env VAL A_LIM (snt_E regs)) by (unfold snt_E; apply Eimg_env).
assert (EEo : forall (n : nat) (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (snt_E regs) n = getr regs rr)
  by (intros n rr Hn; apply lz_E_reg; exact Hn).
assert (SHOK : sh_ok SEGS LZx [] (snt_E regs) (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
remember (snt_E regs) as E eqn:HE. clear HE.
(* 0x86654 .. 0x86af0: beqz s8 (s8 = 0), jal rec_clear *)
paj_run_tok RUN HS HJ SHOK LZspan.
{ awr_ok_tac. }
lhh_mdv.
assert (K1 : forall a, rdW W (ms_mem ms) a = rdW W mem a) by (intros a; lhh_keep HFr).
clear HF HFr HG. rename ms into ms1.
pmkst HS.
rewrite (SIGP CS_rec_clear ltac:(unfold cmd_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (cmd_af CS_rec_clear) with AF_rec_clear by (vm_compute; reflexivity).
assert (HRD : forall a v, rdword (rdW W mem) a = Some v -> rdword (rdW W (ms_mem ms1)) a = Some v).
{ intros a v H. rewrite (rdword_ext (rdW W mem) (rdW W (ms_mem ms1)) a); [exact H|]. intros j _. apply K1. }
assert (P2 : getr (ms_regs ms1) 2 = getr regs 2) by lhh_kreg HS (2%bv : bv 5).
assert (P3 : getr (ms_regs ms1) 3 = getr regs 3) by lhh_kreg HS (3%bv : bv 5).
assert (P4 : getr (ms_regs ms1) 4 = getr regs 4) by lhh_kreg HS (4%bv : bv 5).
assert (P8 : getr (ms_regs ms1) 8 = getr regs 8) by lhh_kreg HS (8%bv : bv 5).
assert (P25 : getr (ms_regs ms1) 25 = getr regs 25) by lhh_kreg HS (25%bv : bv 5).
prreg HS (1%bv : bv 5) P1.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?d3) _ =>
  apply (HZ cx ly S W r3 m3 d3 k acc R O q HB HFP) end.
- split; [exact HJ|]. split; [unfold spZ in *; rewrite P2; exact Hsp|].
  split; [rewrite P3; exact Hgp|]. split; [rewrite P4; exact Htp|].
  intros i rr Hi. apply HRD. exact (Hsv i rr Hi).
- rewrite P1. reflexivity.
- rewrite P25. exact R25.
- rewrite P8. exact R8.
- split; [|split; [exact Hspill|split; [exact H2|split; [|split; [exact Hq0 | exact Hperm]]]]].
  + apply (rec_repA_kept B ly S (rdW W mem) ly S (rdW W (ms_mem ms1)) R O Hrep).
    * intros pn Hpn. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left. exact Hpn.
    * intros a _. apply K1.
  + intros j Hj. rewrite K1. exact (Hq j Hj).
- unfold x_rest in HBUD. rewrite (lt_rest_0 (x_pl cx) (x_n cx) HLEN), ev_from_nil in HBUD. exact HBUD.
Qed.

End e.
End f.
End d.
