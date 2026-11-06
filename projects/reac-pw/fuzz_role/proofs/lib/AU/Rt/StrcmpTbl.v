(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-29: relocated from libreac/fuzz_grant (origin/cold/h-rw-cmd-7-rt 97c611eec86,
   proofs/libreac/fuzz_grant/lib/A/Rt/StrcmpTbl.v, owner h-rw-cmd-7) to libreac/fuzz_identity's ASan build (image A)
   by an address map recorded by the porting lane; module paths, GrantSyms ->
   TfibSyms, and scmp_ranges now states the trampoline word itself (see below). The proofs are h-rw-cmd-7's,
   unchanged. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_identity/lib/A/Rt/StrcmpTbl.v at origin/ossv/recipes 7cbe5270d908 (donor image sha256 c954b804786c); module paths changed and addresses moved to reac-pw/fuzz_role's ASan build (fuzz_role.asan sha256 614cffc0864c) by port_core.py 1e42da8952ec, cross-checked numeral by numeral with alreloc a5c53bb2bed4 (ledger provenance/reloc/A-Rt-Strcmp.tsv); hand: tbl_sc_probe's trampoline word 0x5b40006f is 0x5b00006f here (j +0x5b0, read from fuzz_role.asan at 0x41ad0); the two flag cells are role's start-up rows at 0x135018 / 0x135020. *)
(* libreac/fuzz_identity, build asan: the code table of the strcmp interceptor walk (lib/A/Rt/Strcmp.v) and the
   A/AE2y.v phase lemmas over it (icpt_phase, icpt_phase_to, icpt_ld8 with tbl_icpt replaced by tbl_sc; same
   proofs). The table is A/AE34.v's tbl_icpt plus the one word of the trampoline
   __interceptor_trampoline_strcmp = __wrap_strcmp 0x42194 and the 333 four-byte words from 0x42744:
   __sanitizer_weak_hook_strcmp 0x42744 (4 B, one `ret`) and ___interceptor_strcmp 0x42748 (1328 B, 332 insns),
   checked against fuzz_identity.asan.
   The trampoline word is stated here and not taken from tbl_icpt. On fuzz_grant the walk read it from A/AE34.v's
   trampoline range (grant 0x42130, 38 words, which covers grant's 0x42138); identity's A/AE34.v has not landed,
   so a walk that entered at 0x42194 would depend on where that unlanded range starts. One extra range of one word
   removes the dependency and changes nothing else: build_ranges reads every word from the image, so a range that
   overlaps tbl_icpt is harmless and table_ok is proved the same way.
   tbl_icpt still supplies __asan::TryAsanInitFromRtl 0x59868 and __asan_region_is_poisoned 0x543d4, which the walk
   steps through; identity's AE34 must hold both for the already-relocated memchr walk as well. *)
(* Modified by Theorem Labs, 2026-10-29: for r-identity's acceptance (cold/h-rw-ide-6-wrapacc), the record class is TfibSyms, not IdentTfibSyms (DECISIONS-LIVE 05:31Z: TfibSyms in both A and B, no --rename), and the core modules are Required by full path at the applied A core's names (lib/A/A*.v, lib/Reusable/YA0m, YE08, YE21). *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/Rt/StrcmpTbl.v of this library at d428443238a6 by derive_y.py: module paths lib.A -> lib.AU (A.Axyz -> AU.Yxyz), addresses moved from reac-pw/fuzz_role's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/Rt/StrcmpTbl.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.

From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.

From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
Require Import
  OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable.YA0m.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.

Require Import
  OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU.YB1v
  OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU.YE34
  OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU.YF0l
  OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU.YF0m
  OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU.YF0x
  OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU.YB1w
  OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU.YE20
  OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU.YE2y.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN01 YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition scmp_ranges : list (Z * nat) := [(0x41b68, 1%nat); (0x42114, 333%nat)].
Definition tbl_sc : ctable := Eval vm_compute in build_ranges scmp_ranges tbl_icpt.
Lemma tbl_sc_eq : tbl_sc = build_ranges scmp_ranges tbl_icpt.
Proof. vm_cast_no_check (eq_refl tbl_sc). Qed.
Lemma tbl_sc_ok : table_ok tfibsegs tbl_sc.
Proof.
rewrite tbl_sc_eq. apply build_ranges_ok; [| apply tbl_icpt_ok].
unfold scmp_ranges. repeat constructor; cbn; discriminate.
Qed.
(* The trampoline word (`j 0x42748`), the interceptor's first word (`addi sp,sp,-2032`), the weak hook (`ret`),
   the interceptor's last word and the first word past it. *)
Lemma tbl_sc_probe :
clookup tbl_sc 0x41b68 = Some 0x5b00006f /\ clookup tbl_sc 0x42118 = Some 0x81010113 /\
clookup tbl_sc 0x42114 = Some RET_WORD_r /\ clookup tbl_sc 0x42644 = Some 0xc0dff06f /\ clookup tbl_sc 0x42648 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* The runtime cells the range checks read besides A/YE2y.v's icpt_rodata (the shadow base, the asan-inited flags,
   __asan_region_is_poisoned's bounds), all checked against fuzz_identity.asan and taken from AF0m's Tfib_const
   (the AR const law) by YE2y.rodata_ok:
   - 0x9c3a0 (.got) = 0x136ae8 __sanitizer::common_flags_dont_use, read by `auipc a0,0x5a; ld s8,-1060(a0)` at
     0x427c4 / 0x427c8 (YF0m row `z8 (ANum 0x9c3a0) 0x136ae8`);
   - common_flags + 0xfa = 0x136be2 intercept_strcmp, read by `lbu a0,0xfa(s8)` at 0x427cc: byte 2 of AF0m's row
     `z8 (ANum 0x136be0) 0x101010101010101` = 1, so `beqz a0` at 0x427d0 does not skip the checks;
   - common_flags + 0xf5 = 0x136bdd strict_string_checks, read by `lbu a1,0xf5(s8)` at 0x427d4 and `lbu a0,0xf5(s8)`
     at 0x42830: byte 5 of AF0m's row `z8 (ANum 0x136bd8) 0x101000100000000` = 0, so internal_strlen is not called
     (`bnez a1` 0x427e4, `bnez a0` 0x42834 not taken).
   The two flag cells are declared as the 8-byte words YF0m holds. *)
Definition sc_rodata : list (Z * Z * list (Z * N * Z)) :=
icpt_rodata ++ [(0x9aac0, 8, [(0, 8%N, 0x1351a8)]); (0x135298, 16, [(0, 8%N, 0x101000100000000); (8, 8%N, 0x101010101010101)])].
Lemma sc_rodata_chk : forall ly, rodata_chk ly sc_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma sc_phase : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sym_runN tfibsegs tbl_sc FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tbl_sc tbl_sc_ok YF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Lemma sc_phase_to : forall (W : world tfibsegs) E stop ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sym_run_toN tfibsegs tbl_sc FUEL stop ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E stop ss ss' st ms md HS Hrun.
eapply (SRr_run_to_gen tfibsegs tbl_sc tbl_sc_ok YF0x.Hwx_tfa W FUEL stop E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Lemma sc_ld8 : forall (W : world tfibsegs) E ss ms md (rd rs : bv 5) (w : Z) (h : Z) (k K : nat),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_atoms_lt K ss = true ->
clookup tbl_sc (ss_pc ss) = Some w -> decode_any (Z_to_bv 32 w) = Some (Load SZ8 true rd rs 0%bv, 4) ->
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
pose proof (tbl_sc_ok _ _ Hlk) as Hfetch.
assert (Hec : is_ecall (Z_to_bv 32 w) = false).
{ unfold is_ecall. destruct (bv_eqb (Z_to_bv 32 w) _) eqn:Eq; [|reflexivity].
apply bv_eqb_eq in Eq. rewrite Eq in Hdec. vm_compute in Hdec. discriminate. }
pose proof (val_mem_of_rdword (w_H W) (ms_mem ms) h _ Hw) as Hvm.
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
