From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10 (a Theorem Labs lane): asan-ubsan twin of lib/A/Stdio/PFreadITbl.v
   (a working branch d340d6cc759, a Theorem Labs lane), ported from that file: the same table and the same three
   run lemmas; Requires lib.A.A<n> -> lib.Reusable.Y<n> (AB1v AE34 AF0l AF0m AF0x AE2y) and A<n>. -> Y<n>.
   qualified names. Every pc RE-DERIVED on the asan-ubsan image by symbol + offset (pyelftools + capstone).

   The code table and the three symbolic-run lemmas that the fread interceptor walk needs, in the form
   lib/Reusable/YE2y.v states them for `tbl_icpt`.

   WHY THIS FILE EXISTS. YE34.v's `icpt_ranges` covers (0x432e0, 156) and (0x437c4, 157), i.e. it stops
   exactly at 0x43550 and resumes exactly at 0x437c4. Those two bounds are the end of ___interceptor_read
   and the start of ___interceptor_fwrite, so `tbl_icpt` has a hole of exactly 157 instructions at
   ___interceptor_fread 0x43550 .. 0x437c4 (MEASURED on the unstripped twin c969d83cdd59 of the pin
   fuzz_pcap.asan-ubsan 9e66f771f22a: ___interceptor_fread+0 = 0x43550, st_size 628 = 157 * 4).
   `tbl_fr` is `tbl_icpt` with that one range added, and nothing else; `tbl_fr_ok` is proved from
   `tbl_icpt_ok` by `build_table_ok`, so no lookup of `tbl_icpt` changes.

   YE2y.icpt_memisz (the summary of __sanitizer::mem_is_zero 0x64190) is REUSED UNCHANGED: its proof
   fetches nothing, so it does not mention a code table. Only `icpt_phase`, `icpt_phase_to` and
   `icpt_ld8` name the table, and only those three are restated here, with the same proofs.

   B VALUES, each by symbol + offset on the asan-ubsan image (A value in brackets):
     0x415d0 = __interceptor_trampoline_fread+0 = __wrap_fread+0, raw word 0x7810106f `j +0x1f80` [0x41580]
     0x43550 = ___interceptor_fread+0, raw word 0x81010113                                       [0x43500]
     0x437c0 = ___interceptor_fread+0x270, the last word 0xe51ff06f `j 0x43610`                  [0x43770]
     0x598e4 = __asan::TryAsanInitFromRtl+0, word 0xff010113                                    [0x59894]
     0x54450 = __asan_region_is_poisoned+0, word 0xfc010113                                     [0x54400]
     0x53fc4 = __asan::MemToShadow (the copy called by region_is_poisoned)+0, word 0x00045597
               `auipc a1,0x45` (A: 0x00046597 at 0x53f74; the auipc immediate differs because its GOT
               target moved, 0x99830 -> 0x996f8)
     0x64190 = __sanitizer::mem_is_zero+0                                                       [0x64140]
     PStdioImgB.PFREAD_U = fread+0 (musl), by name                                              [0x8ee5c]

   CROSS-CHECK (owner's order, template only, nothing imported): the walk fread_walkA
   (I_freadw.v:38 (sha256 25add494ffa2; internal record), a working branch f2159272960) starts at the same 0x415d0 and
   stops at 0x8ed28; its interior pcs 0x435ac / 0x435b8 / 0x436d4 / 0x436ec / 0x43610 all lie in the
   range this table adds. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YB1v YE34 YF0l YF0m YF0x YE2y.
(* musl fread's entry by NAME from the image's single stdio-pc home. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio Require PStdioImgB.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* MEASURED on the pin's unstripped twin: ___interceptor_fread+0, 157 instructions (st_size 628). *)
Definition FR_ICPT_U : Z := (symaddr Symbols.AsanUbsan.s___interceptor_fread).
Definition FR_ICPT_N : nat := 157%nat.

Definition tbl_fr : ctable := Eval vm_compute in build_table tfibsegs FR_ICPT_U FR_ICPT_N tbl_icpt.
Lemma tbl_fr_eq : tbl_fr = build_table tfibsegs FR_ICPT_U FR_ICPT_N tbl_icpt.
Proof. vm_cast_no_check (eq_refl tbl_fr). Qed.
Lemma tbl_fr_ok : table_ok tfibsegs tbl_fr.
Proof. rewrite tbl_fr_eq. apply build_table_ok; [cbv; discriminate | apply tbl_icpt_ok]. Qed.

(* The interceptor's first and last instruction, its trampoline, and the three callees the success
   path reaches are all in the table; mem_is_zero deliberately is not (YE2y.icpt_memisz summarises it). *)
Lemma tbl_fr_probe :
clookup tbl_fr (symaddr Symbols.AsanUbsan.s___wrap_fread) = Some 0x7810106f /\          (* j 0x43550, the trampoline *)
clookup tbl_fr (symaddr Symbols.AsanUbsan.s___interceptor_fread) = Some 0x81010113 /\          (* addi sp,sp,-2032 *)
clookup tbl_fr (symaddr (Symbols.AsanUbsan.s___interceptor_fread + 0x270)%Z) = Some 0xe51ff06f /\          (* j 0x43610, the last instruction *)
clookup tbl_fr (symaddr Symbols.AsanUbsan.s__ZN6__asan18TryAsanInitFromRtlEv) = Some 0xff010113 /\          (* TryAsanInitFromRtl *)
clookup tbl_fr (symaddr Symbols.AsanUbsan.s___asan_region_is_poisoned) = Some 0xfc010113 /\          (* __asan_region_is_poisoned *)
clookup tbl_fr (symaddr (Symbols.AsanUbsan.s__ZN6__asan12PoisonShadowEmmh + 0x4fc)%Z) = Some 0x00045597 /\          (* __asan::MemToShadow *)
clookup tbl_fr (symaddr Symbols.AsanUbsan.s__ZN11__sanitizer11mem_is_zeroEPKcm) = None /\                     (* mem_is_zero: summarised, never fetched *)
clookup tbl_fr PStdioImgB.PFREAD_U = None.           (* REAL fread: a Section hypothesis, never fetched *)
Proof. vm_compute. repeat split; reflexivity. Qed.

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* YE2y.icpt_phase at tbl_fr. *)
Lemma fr_phase : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sym_runN tfibsegs tbl_fr FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tbl_fr tbl_fr_ok YF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.

(* YE2y.icpt_phase_to at tbl_fr. *)
Lemma fr_phase_to : forall (W : world tfibsegs) E stop ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sym_run_toN tfibsegs tbl_fr FUEL stop ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E stop ss ss' st ms md HS Hrun.
eapply (SRr_run_to_gen tfibsegs tbl_fr tbl_fr_ok YF0x.Hwx_tfa W FUEL stop E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.

(* YE2y.icpt_ld8 at tbl_fr. *)
Lemma fr_ld8 : forall (W : world tfibsegs) E ss ms md (rd rs : bv 5) (w : Z) (h : Z) (k K : nat),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_atoms_lt K ss = true ->
clookup tbl_fr (ss_pc ss) = Some w -> decode_any (Z_to_bv 32 w) = Some (Load SZ8 true rd rs 0%bv, 4) ->
bv_eqb rd 0%bv = false ->
sv_denot E (sr_get (ss_regs ss) rs) = Z_to_bv 64 h -> 0 <= h -> h + 8 <= 2 ^ 64 ->
rdword (aview tfibsegs (w_H W) (ms_mem ms)) h = Some (bv_unsigned (ew E k)) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
st_ok tfibsegs E (set_regs_pc ss [(rd, SOff k 0)] (ss_pc ss + 4)) (restrict (w_H W) ms1) /\
ms_mem ms1 = ms_mem ms).
Proof.
intros W E ss ms md rd rs w h k K HS Hrv Hat Hlk Hdec Hrd Hrs Hh0 Hh8 Hw. pose proof YF0x.Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape.
pose proof (tbl_fr_ok _ _ Hlk) as Hfetch.
assert (Hec : is_ecall (Z_to_bv 32 w) = false).
{ unfold is_ecall. destruct (bv_eqb (Z_to_bv 32 w) _) eqn:Eq; [|reflexivity].
apply bv_eqb_eq in Eq. rewrite Eq in Hdec. vm_compute in Hdec. discriminate. }
pose proof (YE2y.val_mem_of_rdword (w_H W) (ms_mem ms) h _ Hw) as Hvm.
apply (proj1 (val_mem_word_mem tfibsegs _ _ _)) in Hvm.
destruct (word_mem_ld tfibsegs _ h _ Hvm Hh0 Hh8) as (bs & Hbs & Hle). rewrite Z_to_bv_bv_unsigned in Hle.
assert (R : getr (ms_regs ms) rs = Z_to_bv 64 h) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ss ms rs HS); exact Hrs).
rewrite Hshape. eapply (SRr_step tfibsegs Hwx W); [reflexivity | |].
- rewrite restrict_mkst_fx. apply (step_ld tfibsegs _ _ _ _ _ rd rs (0%bv : bv 12) bs (ew E k) Hfetch Hec Hdec); [|exact Hle].
rewrite R. replace (v_addi (Z_to_bv 64 h) (bv_signed (0%bv : bv 12))) with (Z_to_bv 64 h : word); [exact Hbs|].
apply bv_eq. unfold v_addi. rewrite !Z_to_bv_unsigned. change (bv_signed (0%bv : bv 12)) with 0.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_0_r, Z.mod_mod by lia. reflexivity.
- intros model' Hsbm. rewrite (same_but_materialized_wvb md model' Hsbm). rewrite Hrd.
cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
apply SRr_ret. split; [reflexivity|]. eexists _, _. split; [reflexivity|]. split; [|reflexivity].
rewrite restrict_mkst_fx. rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
replace (v_addi (Z_to_bv 64 (ss_pc ss)) 4) with (Z_to_bv 64 (ss_pc ss + 4) : word)
by (apply bv_eq; unfold v_addi; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64);
rewrite Zplus_mod_idemp_l; reflexivity).
apply (st_ok_set_regs tfibsegs K E E ss _ _ _ (ss_pc ss + 4) _ [(rd, SOff k 0)] HS (env_agree_refl K E) Hat Hrv).
+ cbn. rewrite ?Bool.orb_false_r. reflexivity.
+ intros r Hr. cbn in Hr. rewrite ?Bool.orb_false_r in Hr. rewrite getr_other; [reflexivity|].
intros ->. rewrite bv_eqb_refl in Hr. discriminate.
+ constructor; [|constructor]. cbn [fst snd]. split; [exact Hrd|].
rewrite getr_same by (intros H'; rewrite H', bv_eqb_refl in Hrd; discriminate). cbn [sv_denot].
rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

End f.
