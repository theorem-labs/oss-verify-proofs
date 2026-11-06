(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: relocated from proofs/libreac/fuzz_grant/lib/A/Rt/StrcmpTbl.v (a working branch 97c611eec86) by port_core.py, with its module paths changed and its addresses moved to libreac/fuzz_ctrl's ASan build. *)
(* Written by Theorem Labs, 2026-10, for libreac/fuzz_grant's ASan build: the code table of the strcmp interceptor
   walk (lib/A/Rt/Strcmp.v) and the A/AE2y.v phase lemmas over it (icpt_phase, icpt_phase_to, icpt_ld8 with
   tbl_icpt replaced by tbl_sc; same proofs). The table is A/AE34.v's tbl_icpt plus the 333 four-byte words from
   0x42f14: __sanitizer_weak_hook_strcmp 0x42f14 (4 B, one `ret`) and ___interceptor_strcmp 0x42f18 (1328 B, 332
   insns), MEASURED on fuzz_grant.asan.debug (elfdis.py). tbl_icpt already holds the trampoline
   __interceptor_trampoline_strcmp = __wrap_strcmp 0x42964 (range 0x4295c, 38), __asan::TryAsanInitFromRtl 0x5a038
   (range 0x5a038, 40) and __asan_region_is_poisoned 0x54ba4 (range 0x54ba4, 209). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE20 AE2y.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN01 YM05.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition scmp_ranges : list (Z * nat) := [(0x42f14, 333%nat)].
Definition tbl_sc : ctable := Eval vm_compute in build_ranges scmp_ranges tbl_icpt.
Lemma tbl_sc_eq : tbl_sc = build_ranges scmp_ranges tbl_icpt.
Proof. vm_cast_no_check (eq_refl tbl_sc). Qed.
Lemma tbl_sc_ok : table_ok tfibsegs tbl_sc.
Proof.
rewrite tbl_sc_eq. apply build_ranges_ok; [| apply tbl_icpt_ok].
unfold scmp_ranges. repeat constructor; cbn; discriminate.
Qed.
(* The trampoline word (`j 0x42f18`), the interceptor's first word (`addi sp,sp,-2032`), the weak hook (`ret`),
   the interceptor's last word and the first word past it. *)
Lemma tbl_sc_probe :
clookup tbl_sc 0x42964 = Some 0x5b40006f /\ clookup tbl_sc 0x42f18 = Some 0x81010113 /\
clookup tbl_sc 0x42f14 = Some RET_WORD_r /\ clookup tbl_sc 0x43444 = Some 0xc0dff06f /\ clookup tbl_sc 0x43448 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* The runtime cells the range checks read besides A/AE2y.v's icpt_rodata (the shadow base, the asan-inited flags,
   __asan_region_is_poisoned's bounds), all MEASURED on fuzz_grant.asan.debug and taken from AF0m's Tfib_const
   (the AR const law) by AE2y.rodata_ok:
   - 0x9fac0 (.got) = 0x13a3a8 __sanitizer::common_flags_dont_use, read by `auipc a0,0x5a; ld s8,0xf8(a0)` at
     0x42f94 / 0x42f98 (AF0m row `z8 (ANum 0x9fac0) 0x13a3a8`);
   - common_flags + 0xfa = 0x13a4a2 intercept_strcmp, read by `lbu a0,0xfa(s8)` at 0x42f9c: byte 2 of AF0m's row
     `z8 (ANum 0x13a4a0) 0x101010101010101` = 1, so `beqz a0` at 0x42fa0 does not skip the checks;
   - common_flags + 0xf5 = 0x13a49d strict_string_checks, read by `lbu a1,0xf5(s8)` at 0x42fa4 and `lbu a0,0xf5(s8)`
     at 0x43000: byte 5 of AF0m's row `z8 (ANum 0x13a498) 0x101000100000000` = 0, so internal_strlen is not called
     (`bnez a1` 0x42fb4, `bnez a0` 0x43004 not taken).
   The two flag cells are declared as the 8-byte words AF0m holds. *)
Definition sc_rodata : list (Z * Z * list (Z * N * Z)) :=
icpt_rodata ++ [(0x9fac0, 8, [(0, 8%N, 0x13a3a8)]); (0x13a498, 16, [(0, 8%N, 0x101000100000000); (8, 8%N, 0x101010101010101)])].
Lemma sc_rodata_chk : forall ly, rodata_chk ly sc_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Section f. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
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
eapply (SRr_run_gen tfibsegs tbl_sc tbl_sc_ok AF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
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
eapply (SRr_run_to_gen tfibsegs tbl_sc tbl_sc_ok AF0x.Hwx_tfa W FUEL stop E ss ss' st ms md _ HS Hrun).
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
intros W E ss ms md rd rs w h k K HS Hrv Hat Hlk Hdec Hrd Hrs Hh0 Hh8 Hw. pose proof AF0x.Hwx_tfa as Hwx.
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
