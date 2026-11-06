(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the kit of the last two steps of segment K of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86a24 .. the jal to check_round_trip at 0x86a38): the symbolic state at 0x86a24 and 0x86a2c with the frame word at sp + 112 (g_rec.host_settings before the send, the word 0x86a34 loads); the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_Krefusal_s1.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (cl_seedX: the symbolic state at a point inside the function) and lib/A/Prog/check_refusal_s1.v (cr_entry). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
rec_clear_c send_message_c check_reply_c check_arity_c check_words_c check_refusal_c check_round_trip_c
verbs_receive_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_Kcut.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec HarnessProps.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.

(* The symbolic state at 0x86a24 (pc LO_K3) and at 0x86a2c (pc LO_K4), with the word at sp + off (off = 112: the
   word 0x86a34 loads): the registers are atoms 0..31 of the state's registers, atom 32 is the frame word (8 bytes,
   no inline check), held by a read-only stack region of one chunk; atom 2 (sp = sp1) is 16-aligned. No shadow
   entry: the steps make no ASan check and reach no UBSan trap site. *)
Definition KRx : sv := SLit LT_SB.
Definition KRspan : Z * Z := (LT_SB, LT_SB + 2 ^ 44 - 1).
Definition kr_rs (off : Z) : smem :=
  [YP09.mkRegion (Some 2%nat) off (off + 8) off off [YP09.mkChunk off (CVal 8 (SOff 32 0))]].
Definition kr_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition kr_ss (pc off : Z) : sstate := mkSS pc sr_atoms (kr_rs off) None kr_facts.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition kr_E (regs : bvmap 5 word) (v : Z) : env := Eimg (PI := PI) (Ereg regs [Z_to_bv 64 v]).

(* the seed: the state at BASE + pc with the frame word at sp + off *)
Lemma kr_seed_loc : forall (W : world SEGS) (regs : bvmap 5 word) mem pc off v,
  regions_wf (kr_rs off) = true ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 -> 0 <= off <= 256 ->
  rdword (rdW W mem) (spZ regs + off) = Some v ->
  st_ok_pi SEGS VAL (kr_E regs v) (kr_ss pc off)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))) /\
  sh_ok SEGS KRx [] (kr_E regs v) (mrestrict (w_H W) mem).
Proof.
intros W regs mem pc off v Hwf Hsp Hal Hoff Hv.
set (E := kr_E regs v).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 v]) n)
  by (intros n Hn; subst E; unfold kr_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 v) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
pose proof (lt_rdword_rng SEGS (w_H W) mem _ _ Hv) as Rv.
split.
- unfold kr_ss. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. unfold kr_E. apply regs_ok_Eimg_Ereg.
  + exact Hwf.
  + unfold kr_rs. constructor; [|constructor]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (spZ regs) off 8 (SOff 32 0) v);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword SEGS _ _ _ _ Hv).
  + unfold kr_rs. cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  + split; [|split; [exact I | exact I]].
    cbn [kr_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
    split; [|exact I]. split; [lia|]. split; [exact Hal | lia].
- unfold sh_ok. constructor.
Qed.
End f.
End d.
