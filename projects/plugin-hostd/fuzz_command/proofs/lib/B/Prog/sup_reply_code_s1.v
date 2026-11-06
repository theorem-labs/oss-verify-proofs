(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the kit of sup_reply_code's ASan walk (plugin-hostd/fuzz_command), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v and AChd.v: the literal "resp " and the strncmp wrapper's answer on it, and the symbolic entry state with its seed. The step through a runtime entry and the facts carried over to a call are in lib/A/Prog/PaArt.v. *)
(* Modified by Theorem Labs, 2026-10: ported from lib/A/Prog/sup_reply_code_s1.v (a working branch efc67a58cf8) to fuzz_command.asan-ubsan: module paths, the literal at 0x21d60 (RO_lit_21d60), the 32-byte frame. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtNumber RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdBase CmdRep CmdObj CmdRo CmdAddr PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_reply_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require __intscan_c.
(* the plain proof's strncmp lemma on the literal "resp " (lib/Prog/sup_reply_code.v:47-59); its module shares the
   base name of the walk, so it is named by its full path *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require sup_reply_code.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Module PSRC := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.sup_reply_code.
Module PSRCc := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.sup_reply_code_c.

(* The literal "resp " (without its terminator) as the strncmp wrapper's second string. *)
Definition src_resp : list byte := map (Z_to_bv 8) [114; 101; 115; 112; 32].
Lemma src_resp_lit : src_resp ++ [Z_to_bv 8 0] = PSRCc.resp_lit_bytes.
Proof. vm_compute. reflexivity. Qed.
Lemma src_resp_ro : src_resp ++ [Z_to_bv 8 0] = RO_lit_21d60.
Proof. vm_compute. reflexivity. Qed.
Lemma src_resp_nz : ~ In (Z_to_bv 8 0) src_resp.
Proof. unfold src_resp. cbn [map In]. intros H. repeat (destruct H as [H|H]; [vm_compute in H; discriminate H|]). exact H. Qed.

(* the strncmp wrapper's answer on (s, "resp ", 5) is zero exactly when s starts with "resp " *)
Lemma src_strncmp_iff : forall s, ~ In (Z_to_bv 8 0) s ->
(StrFun.strncmp_model (s ++ [Z_to_bv 8 0]) (src_resp ++ [Z_to_bv 8 0]) 5 = Some 0 <->
map bv_unsigned (firstn 5 s) = [114; 101; 115; 112; 32]).
Proof.
intros s NZ. rewrite src_resp_lit.
destruct (PSRC.strncmp_resp s NZ) as (v & Hm & _ & Hiff). rewrite Hm. split.
- intros H. injection H as ->. apply Hiff. reflexivity.
- intros H. f_equal. apply Hiff. exact H.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the symbolic entry state: every register is its own atom, atom 32 is the shadow base, and the one region is the
   32-byte frame below the entry sp (atom 2). The function makes no inline check, so the token list is empty. *)
Definition src_SB : Z := 0x7fff8000.
Definition src_Bx : sv := SOff 32 0.
Definition src_regions : smem := [ stack_region 32 ].
Definition src_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF src_SB src_SB 0) ] [] [].
Definition ss_src : sstate := mkSS AF_sup_reply_code sr_atoms src_regions None src_facts.
Definition src_SH : list shent := [].
Definition src_Bspan : Z * Z := (src_SB, src_SB + 2 ^ 44 - 1).
Definition src_extra : list word := [Z_to_bv 64 src_SB].
Definition src_E (regs : bvmap 5 word) : env := Eimg (Ereg regs src_extra).

Lemma src_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem ly,
astk_ok SUP_REPLY_CODE_STK ly (spZ regs) ->
(forall a, spZ regs - SUP_REPLY_CODE_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
st_ok_pi SEGS VAL (src_E regs) ss_src (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sup_reply_code)) mem (seg_rom SEGS)))
/\ sh_ok SEGS src_Bx src_SH (src_E regs) (mrestrict (w_H W) mem).
Proof.
intros W regs mem ly Hstk Hpres.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : SUP_REPLY_CODE_STK = 12288) by reflexivity.
set (E := src_E regs).
assert (E2 : ew E 2 = getr regs 2).
{ subst E. unfold src_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ 2 2%bv eq_refl). }
assert (E32 : ew E 32 = Z_to_bv 64 src_SB).
{ subst E. unfold src_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
split.
- unfold ss_src. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
+ subst E. unfold src_E. apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold src_regions, stack_region. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ apply pairwise_disjoint_of_extents. cbn [src_regions map zpairwise_disjoint zall_disjoint]. repeat split.
+ split; [|split; [exact I | exact I]].
cbn [src_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, unsigned_lit_small by (unfold src_SB; lia).
change (2 ^ 4) with 16. rewrite Z.pow_0_r, Z.mod_1_r. unfold src_SB.
repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
- unfold sh_ok, src_SH. apply Forall_nil.
Qed.
End f.
End d.
