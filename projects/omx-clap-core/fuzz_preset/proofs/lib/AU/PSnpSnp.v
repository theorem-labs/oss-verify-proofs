(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: fm.asan's __interceptor_vsnprintf 0x458a0 over the GXA-route contract
   sh_avsnprintf_icpt_realizes_xa (FMsnprintfSx.v), generic in the format family and in the windows (the walk's K,
   musl vsnprintf's Kvs, printf_common's Kpc, under 0x870 + Kvs <= K, 0x870 + Kpc <= K, 0x870 + ESTACK <= K,
   ESTACK <= Kvs): the same function as FMsnprintfGvsni.v's walk, restated in the kit's vocabulary (FMsnprintfSk.v:
   sn_pre, sn_post, sw_frame, sn_pcom, sn_pre_shrink, sn_applyA, kcall_fx, sn_contractA) from printf_common's contract
   (sh_apcommon_realizes_xz) and musl vsnprintf's (sh_avsnprintf_realizes_xa). FMsnprintfGvsni's runs carry a stack region
   of SNK_STK + 0x9d0 bytes, more than a window K = 8064 holds, so its runs are re-run (MEASURED, same stops) over the
   interceptor's own frame [entry - 0x880, entry) (0x870 of frame plus TryAsanInitFromRtl's 0x10), with the callees'
   windows below entry - 0x870 handed to kcall / kcall_fx as written set; its epilogue run r_epi is reused. Added: the
   size < res + 1 side of the branch at 0x45940 (MEASURED: from 0x45940 not taken the run reaches 0x45944 with
   s1 = s3 = size, s2 = str, a0 = res; run r_fEt), whose check WRITE_RANGE (str, size) is FMsnprintfGwrcT.v's
   vsn_wr_check_srrUT; there sn_len (n - 1) T = n. *)
(* Modified by Theorem Labs, 2026-10: port-fm's FMsnprintfSvsni.v (origin/cold/port-fm-rtprintf-param 7e395de08f5)
   restated over the engine's generic ARx with the ghost list Hp fixed (route (a), c-omx-hpreset 10:51Z) and re-pinned
   at preset image A (fuzz_preset.asan, unstripped f0d2e8d4, pin d83eb25d). Restatement: ARU tfibsegs B .. U .. ->
   ARx .. Hp ..; the shared contracts -> their _x forms (PSnpSx: sh_apcommon_realizes_xz, sh_avsnprintf_realizes_xa,
   sh_avsnprintf_icpt_realizes_xa); the laws are Section hypotheses named after their AR_laws_x fields (alx_frame,
   alx_stack, alx_const_cells), not the record; stk_kHighMemBeg (ARU_ARm ..) -> stk_bounds_x, a Section hypothesis of
   the engine lemma's exact statement (YCbqG.stk_bounds_x, 7792959a2abb); g_ecall_preU -> PSnpGt's g_ecall_pre_x; Gwrc / GwrcT's
   vsn_wr_check_srrU(T) -> PSnpGwrc / PSnpGwrcT's vsn_wr_check_srr_x(T); the entry's rodata site (fm :933-949:
   AE2y.rodata_ok over unpoison U mem and ARU_ARm, then kregion_transport with the ARU_mem_low rewrite) -> one
   one PSnpRodata.rodata_ok_lx at vsni_rodata (its real_vsnprintf cell is a row of AF0m.v since h-pre-b3's
   generated blob 1d01cd9b0fcd); ARx reads the real memory, so no transport. Re-pin: the walk's addresses
   (A_VSNI, A_PCOM, A_VSN, RA_ constants, WRC_ENTRY, RT_ENTRY) are PSnpI / PSnpGwrc / PSnpGwrcT's, vsni_rodata PSnpGvsni's; this
   file's own code has no address. Relocation table of the numerals in the comment above, fm.asan (unstripped
   fc92e86b) -> preset A, by symbol + offset (pyelftools + capstone):
     ___interceptor_vsnprintf  +0x0     0x458a0 -> 0x46188
     ___interceptor_vsnprintf  +0xa0    0x45940 -> 0x46228   (the branch on size >= res + 1)
     ___interceptor_vsnprintf  +0xa4    0x45944 -> 0x4622c   (the truncation side)
     ___interceptor_vsnprintf  +0x178   0x45a18 -> 0x46300   (the size >= res + 1 side's check)
   '+ 8' in this file: the shadow hull's granule end and the saved-register slot offsets (address ranges), no presence
   form. *)
(* Modified by Theorem Labs, 2026-10: port-fm 00daeaf3796's destination slack (origin/cold/port-fm-rtprintf-param, the
   final text 3e35620c52e) passed through: the _xa entry's 'amem_range d (sn_len (n - 1) T + 8)' is the Section
   hypothesis HD8, handed unchanged to musl vsnprintf's contract (sn_applyA). The '+ 8' is an address-range fact. *)
(* Modified by Theorem Labs, 2026-10: the memnorm keep (c-omx-alloc 17:03Z ruling (b); the kit texts of
   origin/cold/c-libc-stdio-presetsnp-vfp 43002a8926a7): the post ends in `YAkMemnorm.memnorm segs mem ->
   YAkMemnorm.memnorm segs mem'` (sn_post), from sw_frame's 6th conjunct; at each sw_step the callee's keep: printf_common's
   and musl vsnprintf's from their posts' last conjunct (printf_common's through kcall's Q), Gwrc / GwrcT's from POSTr's
   raw frame over [sp - RC_SCR, sp) and the present window by PSnpKeep.memnorm_of_subframe_dw (empty destination);
   POSTa (the after-REAL post) carries the keep to the end. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PSnpSvsni.v, with its module paths and module names changed; 365 of its 431 lines of code are new or changed and 889 lines of the source are left out. *)
(* fm's snprintf over the shared contracts: __wrap_snprintf 0x41314 (`j 0x45c90`) and __interceptor_snprintf 0x45c90
   (frame 0x60; a3..a7 spilled at sp + 0x38, the va area at the entry sp - 40; TryAsanInitFromRtl; the vsnprintf
   interceptor (str, size, format, ap = the va area)) from the vsnprintf interceptor's shared contract, generic in the
   format family and in the windows (the callee's KV, the entry's K >= KV + 0x60). The same function as FMsnprintfG.v's
   snprintf_of_vsni, restated in the kit's vocabulary (FMsnprintfSk.v). G's runs carry a stack region of SN_K bytes,
   larger than a K the contract allows (K = 8160 on GXA's route), so the two runs are G's over a stack region of SNP_R =
   0x70 bytes (the interceptor's 0x60 frame and TryAsanInitFromRtl's 0x10, MEASURED: G's run 1 writes 8-byte chunks at
   sp - 0x70 .. sp - 8); G's sn_facts0, KEPT and reg_is are reused. New file. *)
(* Modified by Theorem Labs, 2026-10: port-fm's FMsnprintfSnp.v (origin/cold/port-fm-rtprintf-param 7e395de08f5)
   restated over the engine's generic ARx with the ghost list Hp fixed (route (a), c-omx-hpreset 10:51Z) and re-pinned
   at preset image A (fuzz_preset.asan, unstripped f0d2e8d4, pin d83eb25d). Restatement: ARU tfibsegs B .. U .. ->
   ARx .. Hp ..; ecall_preU -> ecall_pre_x; the shared contracts -> their _x forms (PSnpShared / PSnpSx); the laws are
   Section hypotheses named after their AR_laws_x fields (alx_frame, alx_stack, alx_const_cells), not the record;
   stk_kHighMemBeg (ARU_ARm ..) -> stk_bounds_x, a Section hypothesis of the engine lemma's exact statement
   (YCbqG.stk_bounds_x, 7792959a2abb); FMsnprintfGwrc.icpt_rodata_okU (ARU_mem_low + AE2y.rodata_ok over ARU_ARm) -> PSnpRodata's
   rodata_ok_lx at icpt_rodata; snp_ok's premise is ecall_pre_x, one flat conjunction (fm's three-conjunct ecall_preU
   destructure and ARU rebuild go). Re-pin: TFIB_IMG_END 0x5f7000 (fm) -> 0x600000 (preset A's AF0x.v); the walk's
   addresses (PC_snprintf, A_VSNI, RA_VSNI) are PSnpI's and icpt_rodata is preset A's AE2y.v. Relocation table of
   the numerals above, fm.asan (unstripped fc92e86b) -> preset A, by symbol + offset (pyelftools + capstone):
     __wrap_snprintf (fm alias __interceptor_trampoline_snprintf) +0x0   0x41314 -> 0x42cc4
     ___interceptor_snprintf                                      +0x0   0x45c90 -> 0x46578
   Re-measured at preset A: 0x46578 `addi sp, sp, -0x60`, a3 .. a7 spilled at sp + 0x38 .. 0x58. '+ 8' in this file:
   word and slot ranges of rdword / va_words / amem_range (address ranges), no presence form. *)
(* Modified by Theorem Labs, 2026-10: image B twin (fuzz_preset.asan-ubsan, unstripped 3b5e1a09, pin f8f98a95) of
   lib/A/PSnpSnp.v: image A's modules (AB1v AE34 AF0l AF0m AF0x AE20 AE2y AE3h AE2p) -> image B's (YB1v YE34 YF0l YF0m YF0x
   YE20 YE2y YE3h YE2p), the defs / walk / rodata layers' lib/A files -> their lib/AU twins (same names, B values).
   Numerals relocated A -> B by symbol + offset (pyelftools + capstone), A's tables above read at B as:
     __wrap_snprintf (alias __interceptor_trampoline_snprintf) +0x0    0x42cc4 -> 0x42d48
     ___interceptor_snprintf                          +0x0    0x46578 -> 0x465fc
   TFIB_IMG_END is 0x600000 at A' and 0x601000 at B' (YF0x.v). *)
(* Modified by Theorem Labs, 2026-10: port-fm 00daeaf3796's destination slack (origin/cold/port-fm-rtprintf-param, the
   final text 3e35620c52e) passed through: snp_ok's top (sh_asnprintf_realizes_x) now carries
   'amem_range d (sn_len (n - 1) T + 8)' (Ham); the callee's bundle keeps the written extent (Ham0, by amem_range's
   definition) and sn_applyA gets Ham itself for the _xa contract's new premise. The '+ 8' is an address-range fact. *)
(* Modified by Theorem Labs, 2026-10: the memnorm keep (c-omx-alloc 17:03Z ruling (b); the kit texts of
   origin/cold/c-libc-stdio-presetsnp-vfp 43002a8926a7): snp_ok's post ends in `YAkMemnorm.memnorm segs mem ->
   YAkMemnorm.memnorm segs mem'`, from sw_frame's 6th conjunct; at the one sw_step the vsnprintf interceptor's keep,
   its post's last conjunct. *)
(* Modified by Theorem Labs, 2026-10: moved to the #102 pins, image B' (fuzz_preset.asan-ubsan d663f82d, unstripped c90d4fa5), from the old-pin donor origin/cold/c-libc-stdio-presetsnp-vfp ac1750cac8be: every code numeral by symbol + offset, checked equal to the B -> B' map of record (preset-F reloc102-maps bmap_b2bp.py 27b4c628bef6 over this file); B''s derived bounds from that map: the read-only top / writable start 0xa1000 -> 0xa2000, the image top 0x600000 -> 0x601000; kept as written: the IImg record keys, the instruction words and the segment sizes; audited by port_addr_check 0767e70e074a (only the record keys flag). Per-numeral table: c-libc-stdio scratch/p102/reloc/AU/PSnpSnp.v.reloc.tsv. Comment numerals are as written. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YI00 YI16 YK06 YCbqG FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YE34 YF0l YF0m YF0x YE20 YE2y YE3h.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PSnpI PSnpK.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import PSnpG PSnpGkit PSnpGt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PSnpGk.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import PSnpShared PSnpSx PSnpSk.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PSnpVa PSnpRodata.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
Import ListNotations.
Open Scope Z_scope.

(* ---- the walk's symbolic states and runs over a stack region [sp - SNP_R, sp) (atom 2 = the entry sp) ---- *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition SNP_R : Z := 0x70.
Definition snp_regs0 : smem := YP09.mkRegion (Some 2%nat) (- SNP_R) 0 (- SNP_R) 0 [] :: map ro_region icpt_rodata.
Definition ss_snp : sstate := mkSS PC_snprintf sr_atoms snp_regs0 None sn_facts0.
Definition snp_e1 : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs tbl_g FUEL A_VSNI ss_snp).
Lemma r_snp1 : sym_run_toN tfibsegs tbl_g FUEL A_VSNI ss_snp = (snp_e1, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition snp_r0 : YP09.region := Eval vm_compute in hd (YP09.mkRegion None 0 0 0 0 []) (ss_mem snp_e1).
Lemma snp_e1_mem : ss_mem snp_e1 = snp_r0 :: map ro_region icpt_rodata.
Proof. vm_compute. reflexivity. Qed.
Definition snp_e1s : sstate := set_mem snp_e1 [snp_r0].
Definition snp_s2 : sstate := Eval vm_compute in kafter 32 snp_e1s RA_VSNI (-0x60) 0 0.
Lemma snp_s2_eq : kafter 32 snp_e1s RA_VSNI (-0x60) 0 0 = snp_s2.
Proof. vm_compute. reflexivity. Qed.
Definition snp_e2 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tbl_g FUEL snp_s2).
Lemma r_snp2 : sym_runN tfibsegs tbl_g FUEL snp_s2 = (snp_e2, RS_stopped (SR_jalr (SOff 1 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma snp_r0_eq : snp_r0 = YP09.mkRegion (Some 2%nat) (- SNP_R) 0 (- SNP_R) 0 (YP09.r_chunks snp_r0).
Proof. vm_compute. reflexivity. Qed.
Lemma snp_e1_pc : ss_pc snp_e1 = A_VSNI.
Proof. vm_compute. reflexivity. Qed.
Lemma snp_e1_resv : ss_resv snp_e1 = None.
Proof. vm_compute. reflexivity. Qed.
Lemma snp_e1_r : sr_get (ss_regs snp_e1) 1 = SLit RA_VSNI /\ sr_get (ss_regs snp_e1) 2 = SOff 2 (-0x60) /\
  sr_get (ss_regs snp_e1) 10 = SOff 10 0 /\ sr_get (ss_regs snp_e1) 11 = SOff 11 0 /\
  sr_get (ss_regs snp_e1) 12 = SOff 12 0 /\ sr_get (ss_regs snp_e1) 13 = SOff 2 (-0x28) /\
  sr_get (ss_regs snp_e1) 3 = SOff 3 0 /\ sr_get (ss_regs snp_e1) 4 = SOff 4 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma snp_e1_slots : forall i, (i < 5)%nat ->
  In (YP09.mkChunk (-0x28 + 8 * Z.of_nat i) (CVal 8 (SOff (13 + i) 0))) (YP09.r_chunks snp_r0).
Proof.
intros i Hi. do 5 (destruct i as [|i]; [vm_compute; tauto|]). lia.
Qed.
Lemma snp_e2_r : forall r, In r KEPT -> sr_get (ss_regs snp_e2) (Z_to_bv 5 r) = SOff (Z.to_nat r) 0.
Proof.
intros r Hr. assert (X : forallb (fun r => reg_is snp_e2 r (SOff (Z.to_nat r) 0)) KEPT = true) by (vm_compute; reflexivity).
rewrite forallb_forall in X. unfold reg_is in X. apply sv_eqb_eq. exact (X r Hr).
Qed.
Lemma snp_e2_ra_a0 : sr_get (ss_regs snp_e2) 1 = SOff 1 0 /\ sr_get (ss_regs snp_e2) 10 = SOff 36 0 /\
  ss_resv snp_e2 = None /\ clookup tbl_g (ss_pc snp_e2) = Some RET_WORD_r.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma snp_win0 : forallb (fun t => win_eqb t (Some 2%nat, - SNP_R, 0) || (snd t <=? snd (fst t))) (windows (ss_mem ss_snp)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma snp_win2 : forallb (fun t => win_eqb t (Some 2%nat, - SNP_R, 0) || (snd t <=? snd (fst t))) (windows (ss_mem snp_s2)) = true.
Proof. vm_compute. reflexivity. Qed.
Definition snp_r2 : YP09.region := Eval vm_compute in hd (YP09.mkRegion None 0 0 0 0 []) (ss_mem snp_e2).
Lemma snp_e2_mem0 : nth_error (ss_mem snp_e2) 0 = Some snp_r2.
Proof. vm_compute. reflexivity. Qed.
Lemma snp_r2_eq : YP09.r_base snp_r2 = Some 2%nat /\ YP09.r_wlo snp_r2 = - SNP_R /\ YP09.r_whi snp_r2 = 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
End s.

(* a byte of [lo, hi) present after a run whose writable windows lie in [wlo, hi): from the run's window above wlo,
   kept from before below it *)
Lemma present_split : forall (H : word -> bool) E rs (m m' : word -> option byte) lo wlo hi,
  0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, in_wrange E rs a -> wlo <= a < hi) -> frame_of E rs m m' ->
  (forall a, lo <= a < hi -> apresent H m a) -> (forall a, wlo <= a < hi -> apresent H m' a) ->
  forall a, lo <= a < hi -> apresent H m' a.
Proof.
intros H E rs m m' lo wlo hi H0 H64 Hwin Hfo Hpz Hpz' a Ha.
destruct (Z_lt_le_dec a wlo) as [L|L]; [|apply Hpz'; lia].
apply (apresent_same H m m' a); [|exact (Hpz a Ha)].
apply Hfo. rewrite unsigned_lit_small by lia. intros Hin. pose proof (Hwin a Hin). lia.
Qed.

(* ---- the vsnprintf interceptor's bundle at the call: the entry's premises at the memory the walk reached (changed only
   inside the entry window [sp - K, sp)), with the va area at sp - 40 (a3..a7 spilled from the ENTRY registers, then the
   caller's stack words at sp), at the callee's sp - 0x60 and window KV ---- *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
(* the stack band, as the engine lemma's exact statement (YCbqG.stk_bounds_x, c-omx-alloc 7792959a2abb YCbqG.v:308,
   which needs the whole AR_laws_x record): an instance passes `YCbqG.stk_bounds_x segs B ARx LAWS`; never proved here *)
Hypothesis stk_bounds_x : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
  kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd.
Lemma snp_pre_call : forall FF (K KV gc gv : Z) cr ly S Hp W regs mem md mem1 md1 d n f xs ws T cval,
  ff_stable64 FF -> ff_mono FF -> ESTACK <= KV -> KV + 0x60 <= K ->
  ARx ly S Hp W mem md ->
  ly_stk_lo ly + K <= spZ regs -> spZ regs <= ly_stk_hi ly -> spZ regs mod 16 = 0 ->
  consts_view tfibsegs W mem cr -> Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr ->
  Forall (fun r => Forall (zdisjoint r) (snp_out K (spZ regs) d (sn_len (n - 1) T))) cr ->
  rdword (aview tfibsegs (w_H W) mem) gc = Some gv -> rdword (aview tfibsegs (w_H W) mem) gv = Some cval ->
  0 <= gc -> gc + 8 <= 2 ^ 63 -> 0 <= gv -> gv + 8 <= 2 ^ 63 ->
  Forall (zdisjoint (gc, 8)) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
  Forall (zdisjoint (gv, 8)) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
  va_words regs (aview tfibsegs (w_H W) mem) (spZ regs) xs ws ->
  spZ regs + 8 * Z.of_nat (length xs) < 2 ^ 63 ->
  Forall (zdisjoint (spZ regs, 8 * Z.of_nat (length xs))) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
  FF (aview tfibsegs (w_H W) mem) (snp_out K (spZ regs) d (sn_len (n - 1) T)) f ws T ->
  1 <= n < 2 ^ 31 -> Z.of_nat (length T) < 2 ^ 31 - 1 -> 0 < d -> d + sn_len (n - 1) T <= 2 ^ 63 ->
  pairwise zdisjoint (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
  dest_ok tfibsegs B ly S W regs mem d (sn_len (n - 1) T) -> amem_range d (sn_len (n - 1) T) ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF d (sn_len (n - 1) T) ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) d (sn_len (n - 1) T) ->
  ARx ly S Hp W mem1 md1 ->
  (forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem1 a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - K <= a < spZ regs) ->
     aview tfibsegs (w_H W) mem1 a = aview tfibsegs (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a) ->
  words_at (aview tfibsegs (w_H W) mem1) (spZ regs - vs_off asan_snprintf_spill)
    (map (argZ regs) (map Z.of_nat (vs_regs asan_snprintf_spill))) ->
  sn_pre tfibsegs B ARx FF KV gc gv cr ly S Hp W mem1 md1 (spZ regs - 0x60) d n f (spZ regs - vs_off asan_snprintf_spill) ws T cval.
Proof.
intros FF K KV gc gv cr ly S Hp W regs mem md mem1 md1 d n f xs ws T cval STAB MONO HKV1 HKV2 HA HKlo Hhi H16
  Hcv Hcb Hcd Hgc Hgv G1 G2 G3 G4 Hgcd Hgvd Hva Hxs Hxd HFF Hn HT Hd0 Hdw Hpw Hdst Ham Hra Hhull HA1 Hp1 KEEP PRES SPILL.
pose proof (stk_bounds_x ly S Hp W mem md HA) as [K1 K2].
assert (HE : ESTACK = 4096) by reflexivity.
pose proof (sn_len_pos (n - 1) T) as Hw1.
pose proof Hva as Hva'. destruct Hva' as [Hws _].
assert (Hlws : length ws = (5 + length xs)%nat) by (rewrite Hws, length_app; reflexivity).
set (sp := spZ regs) in *. set (w := sn_len (n - 1) T) in *.
pose proof Hpw as Hpw'. apply pairwise_snp in Hpw'. unfold zdisjoint in Hpw'. cbn [fst snd] in Hpw'.
assert (KZ : forall p l, zdisjoint (p, l) (sp - K, K) -> 0 <= p -> p + l <= 2 ^ 63 ->
  forall a, p <= a < p + l -> aview tfibsegs (w_H W) mem1 a = aview tfibsegs (w_H W) mem a).
{ intros p l Z1 Hp0 Hpl a Ha. unfold zdisjoint in Z1. cbn [fst snd] in Z1. apply KEEP; lia. }
assert (KS : forall s, SHADOW_OFF <= s < kHighMemBeg -> aview tfibsegs (w_H W) mem1 s = aview tfibsegs (w_H W) mem s).
{ intros s Hs. apply KEEP; unfold SHADOW_OFF, kHighMemBeg in *; lia. }
assert (SUB : forall x, Forall (zdisjoint x) (snp_out K sp d w) -> Forall (zdisjoint x) (snp_out KV (sp - 0x60) d w)).
{ intros x Hx. apply Forall_snp in Hx as [X1 X2]. apply Forall_snp. split; [|exact X2].
  apply (zdisjoint_sub x (sp - K, K)); [exact X1 | cbn [fst snd]; lia | cbn [fst snd]; lia]. }
assert (VS : vs_off asan_snprintf_spill = 40) by reflexivity.
assert (K0 : 0 <= ly_stk_lo ly) by (unfold kHighMemBeg in K1; lia).
assert (V1 : vs_off asan_snprintf_spill <= sp) by (change (vs_off asan_snprintf_spill) with 40; lia).
assert (V2 : vs_off asan_snprintf_spill <= 0x60) by (change (vs_off asan_snprintf_spill) with 40; lia).
assert (V3 : vs_off asan_snprintf_spill <= K) by (change (vs_off asan_snprintf_spill) with 40; lia).
pose proof (va_spill_ap_ok asan_snprintf_spill regs (sp - 0x60) 0x60 K KV d w xs asan_snprintf_spill_off
  V1 Hxs eq_refl V2 V3 ltac:(lia) Hxd Hpw) as (AP1 & AP2 & AP3).
pose proof Hgcd as Gc. apply Forall_snp in Gc as [Gc1 _]. pose proof Hgvd as Gv. apply Forall_snp in Gv as [Gv1 _].
unfold sn_pre, sn_rs. fold w.
split; [exact HA1|]. split; [lia|]. split; [lia|].
split; [replace (sp - 0x60) with (sp + (-6) * 16) by lia; rewrite Z_mod_plus_full; exact H16|].
split; [exact HKV1|].
split; [intros a Ha; apply Hp1; lia|].
split.
{ intros a Ha. rewrite Exists_exists in Ha. destruct Ha as (r & Hr & Hin).
  rewrite Forall_forall in Hcd, Hcb. pose proof (Hcd r Hr) as Hd. apply Forall_snp in Hd as [D1 D2].
  pose proof (Hcb r Hr) as Hb. unfold in_zr in Hin.
  rewrite (KZ (fst r) (snd r)); [| destruct r; exact D1 | lia | lia | exact Hin].
  apply Hcv. rewrite Exists_exists. exists r. split; [exact Hr | exact Hin]. }
split; [exact Hcb|].
split; [rewrite Forall_forall in Hcd |- *; intros r Hr; exact (SUB r (Hcd r Hr))|].
split; [apply (rdword_keep (aview tfibsegs (w_H W) mem)); [|exact Hgc]; intros a Ha; apply (KZ gc 8); auto; lia|].
split; [apply (rdword_keep (aview tfibsegs (w_H W) mem)); [|exact Hgv]; intros a Ha; apply (KZ gv 8); auto; lia|].
split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
split; [exact (SUB _ Hgcd)|]. split; [exact (SUB _ Hgvd)|].
split.
{ apply (va_spill_of_va_words asan_snprintf_spill regs (aview tfibsegs (w_H W) mem) _ xs ws eq_refl
    asan_snprintf_spill_off Hva); [|exact SPILL].
  intros i Hi. apply rdword_same. intros k Hk. apply KEEP; lia. }
split; [exact AP1|]. split; [rewrite Hlws; exact AP2|]. split; [rewrite Hlws; exact AP3|].
split.
{ apply (MONO _ (snp_out K sp d w)).
  - apply (STAB (aview tfibsegs (w_H W) mem)); [exact HFF|].
    intros a Ha. destruct (Z_lt_le_dec a (sp - K)) as [L1|L1]; [left; apply KEEP; [exact Ha | lia]|].
    destruct (Z_lt_le_dec a sp) as [L2|L2]; [|left; apply KEEP; [exact Ha | lia]].
    right. split; [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia|]. unfold SHADOW_OFF, kHighMemBeg in *; lia.
  - intros r' Hr'. unfold snp_out in Hr'. destruct Hr' as [<-|[<-|[]]].
    + exists (sp - K, K). split; [left; reflexivity | cbn [fst snd]; lia].
    + exists (d, w). split; [right; left; reflexivity | cbn [fst snd]; lia]. }
split; [exact Hn|]. split; [exact HT|]. split; [exact Hd0|]. split; [exact Hdw|].
split; [apply pairwise_snp; unfold zdisjoint; cbn [fst snd]; lia|].
split.
{ intros a Ha. destruct (Hdst a Ha) as (X1 & X2 & _). split; [|exact X2].
  exact (writable_xfer (w_H W) mem mem1 a X1 (PRES a)). }
split; [exact Ham|].
split; [exact (ra_keep _ _ d w Ham ltac:(lia) KS Hra)|].
exact (hull_keep _ _ d w Ham ltac:(lia) Hw1 KS Hhull).
Qed.
End c.

(* ---- __wrap_snprintf / __interceptor_snprintf at an entry window K from the vsnprintf interceptor's GXA-route contract
   (FMsnprintfSx's sh_avsnprintf_icpt_realizes_xa) at a window KV with KV + 0x60 <= K (fm's chain: KV = OSP_VSNI +
   SNK_STK, K = SN_K; GXA's route: KV = 8064, K >= 8160). Its three extra premises hold of the va area at sp - 40: above
   the callee's sp - 0x60, ending at sp + 8 |xs| <= 2^47, and off the destination (below the window, or above the
   caller's slots by the entry's disjointness). The wrapper does no FP before the call, so its frm0_entry is the
   callee's. The callee returns at its own FP state fx'; the epilogue runs at fx' (kcall_fx) and the post names that
   fx'. ---- *)
Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Hypothesis alx_frame : ARx_frame_law tfibsegs B ARx.
Hypothesis alx_stack : ARx_stack_law tfibsegs B ARx.
Hypothesis alx_const_cells : ARx_const_cells_law tfibsegs B ARx.
(* the stack band, as the engine lemma's exact statement (YCbqG.stk_bounds_x, c-omx-alloc 7792959a2abb YCbqG.v:308,
   which needs the whole AR_laws_x record): an instance passes `YCbqG.stk_bounds_x segs B ARx LAWS`; never proved here *)
Hypothesis stk_bounds_x : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
  kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd.
Hypothesis TB : TfibSyms B.
Variables (FF : fmt_fam) (gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (KV K : Z).
Hypothesis STAB : ff_stable64 FF.
Hypothesis MONO : ff_mono FF.
Hypothesis HKV : ESTACK <= KV.
Hypothesis HKK : KV + 0x60 <= K.
Hypothesis AVSNI : sh_avsnprintf_icpt_realizes_xa tfibsegs B ARx FF KV gc gv img_lo img_hi cr A_VSNI.
Theorem snp_ok : sh_asnprintf_realizes_x tfibsegs B ARx FF K gc gv img_lo img_hi cr PC_snprintf.
Proof.
intros ly S Hp W regs mem md d n f xs ws T cval HPRE HKlo HKp G10 G11 G12 Hcv Hcb Hcd Hgc Hgv C1 C2 C3 C4 Hgcd Hgvd
  Hva Hxs Hxd HFF Hn HT Hd0 Hdw Hpw Hdst Ham Hra Hhull Hdog Hfrm.
assert (Ham0 : amem_range d (sn_len (n - 1) T)) by (unfold amem_range in Ham |- *; lia).
pose proof HPRE as (HA & Hret & H16 & Hes & Hhi & Hpe & Hgp & Htp).
pose proof (stk_bounds_x ly S Hp W mem md HA) as [K1 K2].
assert (HC : SNP_R = 112 /\ kHighMemEnd = 2 ^ 47 /\ kHighMemBeg = 17594333495296 /\ TFIB_IMG_END = 0x601000)
  by (repeat split; reflexivity).
destruct HC as (C5 & C6 & C7 & C8).
assert (HE : ESTACK = 4096) by reflexivity.
pose proof (snp_pre_call B ARx stk_bounds_x FF K KV gc gv cr ly S Hp W regs mem md) as PREC.
set (sp := spZ regs) in *.
set (w := sn_len (n - 1) T) in *.
set (XW := fun a => d <= a < d + w).
pose proof (sn_len_pos (n - 1) T) as Hw1. fold w in Hw1.
pose proof Hpw as Hpw'. apply pairwise_snp in Hpw'. unfold zdisjoint in Hpw'. cbn [fst snd] in Hpw'.
assert (Hxs63 : sp + 8 * Z.of_nat (length xs) < 2 ^ 63) by lia.
assert (Hlws : length ws = (5 + length xs)%nat) by (destruct Hva as [-> _]; rewrite length_app; reflexivity).
(* the callee's GXA-route premises: the va area above its sp, off the destination, below 2^47 *)
assert (AP0 : sp - 0x60 <= sp - vs_off asan_snprintf_spill) by (change (vs_off asan_snprintf_spill) with 40; lia).
assert (AP1 : sp - vs_off asan_snprintf_spill + 8 * Z.of_nat (length ws) = sp + 8 * Z.of_nat (length xs))
  by (rewrite Hlws; change (vs_off asan_snprintf_spill) with 40; lia).
assert (AP2 : d + w <= sp - 0x60 - KV \/ sp - vs_off asan_snprintf_spill + 8 * Z.of_nat (length ws) <= d).
{ rewrite AP1. destruct Hpw' as [L|L]; [right | left; lia].
  apply Forall_snp in Hxd as [_ X]. unfold zdisjoint in X. cbn [fst snd] in X. lia. }
(* the entry state *)
set (E := Ereg regs []).
assert (E2 : bv_unsigned (ew E 2) = sp) by (unfold E; rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
assert (EREG : forall (r : bv 5), ew E (Z.to_nat (bv_unsigned r)) = getr regs r) by (intros r; apply ew_Ereg_reg).
assert (E2' : bv_unsigned (ew (Ereg regs []) 2) = sp) by exact E2.
assert (HS0 : st_ok tfibsegs E ss_snp (restrict (w_H W) (mkst regs (Z_to_bv 64 PC_snprintf) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_snp. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold snp_regs0. apply Forall_cons.
    + apply (region_ok_stack tfibsegs E _ 2 sp (- SNP_R)); [exact E2 | lia | lia |].
      intros a Ha. apply YE2y.apresent_writable. apply HKp. lia.
    + exact (rodata_ok_lx B ARx alx_const_cells TB icpt_rodata ly S Hp W mem md E (icpt_rodata_chk ly) HA).
  - apply pairwise_disjoint_of_extents. unfold snp_regs0, icpt_rodata, ro_region, extent_of_region.
    cbn [map fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?E2, ?E2'.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; exact I]. cbn [sn_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite ?E2, ?E2'.
    change (2 ^ 4) with 16. repeat split; lia. }
pose proof (sw_init tfibsegs ARx ly S Hp W mem md (sp - K) sp XW HA HKp) as F0.
unfold cfg_at. change (w64 PC_snprintf) with (Z_to_bv 64 PC_snprintf).
(* run 1: to the vsnprintf interceptor *)
eapply SRr_bind; [exact (g_phase_to W E A_VSNI ss_snp snp_e1 RS_running _ md HS0 r_snp1)|].
intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1).
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md).
assert (WIN1 : forall a, in_wrange E (ss_mem ss_snp) a -> sp - SNP_R <= a < sp).
{ intros a Hwi. pose proof (in_wrange_single_b E _ a 2 (- SNP_R) 0 sp snp_win0 E2 Hwi). lia. }
assert (WIN1K : forall a, in_wrange E (ss_mem ss_snp) a -> sp - K <= a < sp) by (intros a Hwi; pose proof (WIN1 a Hwi); lia).
assert (PW1R : forall a, sp - SNP_R <= a < sp -> apresent (w_H W) (ms_mem ms1) a).
{ intros a Ha. apply (st_ok_window_apresent (w_H W) E snp_e1 ms1 0 snp_r0 a HS1); [rewrite snp_e1_mem; reflexivity | |].
  - rewrite snp_r0_eq. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. rewrite E2. lia.
  - lia. }
assert (PW1 : forall a, sp - K <= a < sp -> apresent (w_H W) (ms_mem ms1) a)
  by exact (present_split (w_H W) E (ss_mem ss_snp) mem (ms_mem ms1) (sp - K) (sp - SNP_R) sp ltac:(lia) ltac:(lia)
    WIN1 HF1 HKp PW1R).
assert (F1 : sw_frame tfibsegs ARx ly S Hp W mem md (sp - K) sp XW (ms_mem ms1) md1)
  by exact (sw_run tfibsegs B ARx alx_frame alx_stack stk_bounds_x ly S Hp W mem md (sp - K) sp XW ltac:(lia) Hhi mem md (ms_mem ms1) mat1 E (ss_mem ss_snp)
    F0 WIN1K HF1 PW1).
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - K <= a < sp) ->
  aview tfibsegs (w_H W) (ms_mem ms1) a = aview tfibsegs (w_H W) mem a).
{ intros a Ha Hb. apply aview_same. apply HF1. rewrite unsigned_lit_small by lia. intros Hin. exact (Hb (WIN1K _ Hin)). }
pose proof snp_e1_r as (R1 & R2 & R10 & R11 & R12 & R13 & R3 & R4).
assert (RD : forall (r : bv 5) v, sr_get (ss_regs snp_e1) r = v -> getr (ms_regs ms1) r = sv_denot E v).
{ intros r v Hr. exact (g_reg W E snp_e1 ms1 r v HS1 Hr). }
assert (OFF : forall (r : bv 5) z, sv_denot E (SOff (Z.to_nat (bv_unsigned r)) z) = Z_to_bv 64 (bv_unsigned (getr regs r) + z)).
{ intros r z. cbn [sv_denot]. rewrite EREG. reflexivity. }
assert (Q1 : getr (ms_regs ms1) 1 = w64 RA_VSNI) by (rewrite (RD _ _ R1); reflexivity).
assert (Q2 : getr (ms_regs ms1) 2 = w64 (sp - 0x60)) by (rewrite (RD _ _ R2); cbn [sv_denot]; rewrite E2; reflexivity).
assert (Q10 : getr (ms_regs ms1) 10 = w64 d).
{ rewrite (RD _ _ R10). rewrite (OFF 10%bv 0). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact G10. }
assert (Q11 : getr (ms_regs ms1) 11 = w64 n).
{ rewrite (RD _ _ R11). rewrite (OFF 11%bv 0). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact G11. }
assert (Q12 : getr (ms_regs ms1) 12 = w64 f).
{ rewrite (RD _ _ R12). rewrite (OFF 12%bv 0). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact G12. }
assert (Q13 : getr (ms_regs ms1) 13 = w64 (sp - vs_off asan_snprintf_spill)).
{ rewrite (RD _ _ R13). cbn [sv_denot]. rewrite E2. reflexivity. }
assert (Q3 : getr (ms_regs ms1) 3 = w64 (as_gp B)).
{ rewrite (RD _ _ R3). rewrite (OFF 3%bv 0). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hgp. }
assert (Q4 : getr (ms_regs ms1) 4 = w64 (as_tp B)).
{ rewrite (RD _ _ R4). rewrite (OFF 4%bv 0). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Htp. }
assert (SP1 : spZ (ms_regs ms1) = sp - 0x60).
{ unfold spZ. rewrite Q2. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (RET1 : ret_ok (getr (ms_regs ms1) 1)) by (rewrite Q1; apply ret_ok_lit; [unfold RA_VSNI; lia | reflexivity]).
assert (RAQ : raZ (ms_regs ms1) = RA_VSNI).
{ unfold raZ. rewrite Q1. unfold w64. rewrite unsigned_lit_small by (unfold RA_VSNI; lia). reflexivity. }
(* a3..a7 of the ENTRY registers, spilled at sp - 40 *)
assert (ARGR : forall j, 0 <= argZ regs j < 2 ^ 64) by (intros j; unfold argZ; apply u64_range).
assert (EN : forall n0, (n0 < 32)%nat -> ew E n0 = getr regs (Z_to_bv 5 (Z.of_nat n0))).
{ intros n0 Hn0. unfold E. apply ew_Ereg_nat. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
  rewrite Z.mod_small; lia. }
assert (SPILL : words_at (aview tfibsegs (w_H W) (ms_mem ms1)) (sp - vs_off asan_snprintf_spill)
  (map (argZ regs) (map Z.of_nat (vs_regs asan_snprintf_spill)))).
{ intros i Hi. cbn [vs_off vs_regs asan_snprintf_spill length map] in Hi |- *.
  apply YF0x.val_mem_rdword; [do 5 (destruct i as [|i]; [cbn [nth map]; apply ARGR|]); lia|].
  pose proof (g_slot W E snp_e1 ms1 0 snp_r0 _ 8%N _ (nth i (map (argZ regs) (map Z.of_nat [3; 4; 5; 6; 7]%nat)) 0) HS1
    ltac:(rewrite snp_e1_mem; reflexivity) (snp_e1_slots i Hi)) as X.
  rewrite snp_r0_eq in X. cbn [YP09.r_base base_val] in X. rewrite E2 in X.
  replace (sp + (-40 + 8 * Z.of_nat i)) with (sp - 40 + 8 * Z.of_nat i) in X by lia.
  apply X; [| change (8 * Z.of_N 8) with 64; do 5 (destruct i as [|i]; [cbn [nth map]; apply ARGR|]); lia | lia].
  cbn [sv_denot].
  do 5 (destruct i as [|i]; [cbn [nth map Nat.add]; rewrite EN by lia; unfold argZ;
    rewrite ?Z.add_0_r; repeat rewrite Z_to_bv_bv_unsigned; reflexivity|]). lia. }
pose proof F1 as (HA1 & Hsb1 & Hp1 & Hfr1 & Hpm1 & _).
pose proof (PREC (ms_mem ms1) md1 d n f xs ws T cval STAB MONO HKV HKK HA HKlo Hhi H16 Hcv Hcb Hcd Hgc Hgv C1 C2 C3 C4
  Hgcd Hgvd Hva Hxs63 Hxd HFF Hn HT Hd0 Hdw Hpw Hdst Ham0 Hra Hhull HA1 PW1 KEEP1 Hpm1 SPILL) as PRE1.
clear PREC.
(* the call: the vsnprintf interceptor's contract, then the epilogue at the FP state it returned with *)
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS1 snp_e1_resv) as Hshape1.
rewrite Hshape1, snp_e1_pc.
change (mkCfg (mkst (ms_regs ms1) (Z_to_bv 64 A_VSNI) (ms_mem ms1) (seg_rom tfibsegs)) md1)
  with (cfg_at tfibsegs A_VSNI (ms_regs ms1) (ms_mem ms1) md1).
apply (srr_fx_continue tfibsegs W (cfg_at tfibsegs A_VSNI (ms_regs ms1) (ms_mem ms1) md1) (raZ (ms_regs ms1))
  (fun _ regs' mem' md' => ARx ly S Hp W mem' md' /\ aregs_preserved (ms_regs ms1) regs' /\
     same_but_materialized md1 md' /\ getr regs' 10 = w64 (Z.of_nat (length T)) /\
     (forall i, 0 <= i < sn_len (n - 1) T ->
        aview tfibsegs (w_H W) mem' (d + i) = Some (nth (Z.to_nat i) (sn_bytes (n - 1) T) 0)) /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (n - 1) T) ->
        ~ (spZ (ms_regs ms1) - KV <= a < spZ (ms_regs ms1)) ->
        aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) (ms_mem ms1) a) /\
     (forall a, apresent (w_H W) (ms_mem ms1) a -> apresent (w_H W) mem' a) /\
     (YAkMemnorm.memnorm tfibsegs (ms_mem ms1) -> YAkMemnorm.memnorm tfibsegs mem'))).
{ assert (PRE1' : sn_pre tfibsegs B ARx FF KV gc gv cr ly S Hp W (ms_mem ms1) md1 (spZ (ms_regs ms1)) d n f
    (sp - vs_off asan_snprintf_spill) ws T cval) by (rewrite SP1; exact PRE1).
  exact (sn_applyA tfibsegs B ARx FF KV gc gv img_lo img_hi cr A_VSNI ly S Hp W (ms_regs ms1) (ms_mem ms1) md1 d n f _ ws T cval
    (or_intror AVSNI) PRE1' Hdog Hfrm ltac:(rewrite SP1; exact AP0) ltac:(rewrite SP1; exact AP2)
    ltac:(rewrite AP1; exact Hxs) Ham RET1 Q3 Q4 Q10 Q11 Q12 Q13). }
intros fx' regs2 mem2 md2 FP1 FP2 (HA2 & HP2 & Hsb2 & G10b & HDb & Hfr2 & Hpm2 & Hkp2).
rewrite RAQ.
(* the state after the call, at fx': the callee wrote below sp - 0x60 (its window [sp - 0x60 - KV, sp - 0x60): the band
   [sp - SNP_R, sp - 0x60) inside the region, the rest in XW') and the destination *)
set (E2v := havoc E 32 (map (getr regs2) CLOB)).
assert (E22 : bv_unsigned (ew E2v 2) = sp) by (unfold E2v; rewrite ew_havoc_old by lia; exact E2).
assert (HS1s : st_ok (fx:=fx) tfibsegs E snp_e1s (restrict (w_H W) ms1))
  by exact (st_ok_take1 E snp_e1 _ snp_r0 _ HS1 snp_e1_mem).
pose proof snp_r0_eq as R0.
set (XW' := fun a => XW a \/ sp - 0x60 - KV <= a < sp - SNP_R).
assert (HS2 : st_ok (fx:=fx') tfibsegs E2v snp_s2
  (restrict (w_H W) (mkst (fx:=fx') regs2 (Z_to_bv 64 RA_VSNI) mem2 (seg_rom tfibsegs)))).
{ rewrite <- snp_s2_eq.
  apply (kcall_fx fx fx' W E snp_e1s ms1 sp SNP_R snp_r0 [] 32 RA_VSNI (-0x60) 0 0 (SNP_R - 0x60) XW' regs2 mem2
    HS1s ltac:(exact snp_e1_resv) E2 eq_refl).
  - rewrite R0. reflexivity.
  - rewrite R0. reflexivity.
  - rewrite R0. reflexivity.
  - rewrite R0. cbn. lia.
  - rewrite R0. cbn. lia.
  - vm_compute. reflexivity.
  - rewrite snp_s2_eq. vm_compute. reflexivity.
  - rewrite snp_s2_eq. vm_compute. reflexivity.
  - rewrite snp_s2_eq. vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - intros a Hx Hr. exfalso. destruct Hx as [Hx|Hx]; unfold XW in Hx; lia.
  - intros r a Hr. destruct Hr.
  - intros r a Hr. destruct Hr.
  - intros a Ha. apply PW1. lia.
  - exact HP2.
  - intros a Ha H1 H2. apply Hfr2; [exact Ha | intros Hd; apply H2; left; exact Hd |].
    rewrite SP1. intros Hc. destruct (Z_lt_le_dec a (sp - SNP_R)) as [L|L]; [apply H2; right; lia | apply H1; lia].
  - exact Hpm2. }
assert (F2 : sw_frame tfibsegs ARx ly S Hp W mem md (sp - K) sp XW mem2 md2).
{ apply (sw_step tfibsegs ARx ly S Hp W mem md (sp - K) sp XW (ms_mem ms1) md1 mem2 md2 F1 HA2 Hsb2).
  - intros a Ha. apply Hpm2. apply PW1. exact Ha.
  - intros a Ha H1 H2. apply Hfr2; [exact Ha | exact H2 | rewrite SP1; lia].
  - exact Hpm2.
  - exact Hkp2. }
pose proof F2 as (_ & _ & Hp2 & _ & _).
(* run 2: the epilogue *)
unfold cfg_at. change (w64 RA_VSNI) with (Z_to_bv 64 RA_VSNI).
eapply SRr_bind;
  [exact (g_phase (fx:=fx') W E2v snp_s2 snp_e2 (RS_stopped (SR_jalr (SOff 1 0)))
     (mkst (fx:=fx') regs2 (Z_to_bv 64 RA_VSNI) mem2 (seg_rom tfibsegs)) md2 HS2 r_snp2)|].
intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3).
set (md3 := with_vm_backing (m_vm_lazy md2) mat3 md2) in *.
assert (WIN2 : forall a, in_wrange E2v (ss_mem snp_s2) a -> sp - SNP_R <= a < sp).
{ intros a Hwi. pose proof (in_wrange_single_b E2v _ a 2 (- SNP_R) 0 sp snp_win2 E22 Hwi). lia. }
assert (WIN2K : forall a, in_wrange E2v (ss_mem snp_s2) a -> sp - K <= a < sp) by (intros a Hwi; pose proof (WIN2 a Hwi); lia).
assert (PW3R : forall a, sp - SNP_R <= a < sp -> apresent (w_H W) (ms_mem ms3) a).
{ intros a Ha. pose proof snp_r2_eq as (B2 & L2 & H2).
  apply (st_ok_window_apresent (w_H W) E2v snp_e2 ms3 0 snp_r2 a HS3 snp_e2_mem0); [|lia].
  rewrite B2, L2, H2. cbn [base_val]. rewrite E22. lia. }
assert (PW3 : forall a, sp - K <= a < sp -> apresent (w_H W) (ms_mem ms3) a)
  by exact (present_split (w_H W) E2v (ss_mem snp_s2) mem2 (ms_mem ms3) (sp - K) (sp - SNP_R) sp ltac:(lia) ltac:(lia)
    WIN2 HF3 Hp2 PW3R).
assert (F3 : sw_frame tfibsegs ARx ly S Hp W mem md (sp - K) sp XW (ms_mem ms3) md3)
  by exact (sw_run tfibsegs B ARx alx_frame alx_stack stk_bounds_x ly S Hp W mem md (sp - K) sp XW ltac:(lia) Hhi mem2 md2 (ms_mem ms3) mat3 E2v (ss_mem snp_s2)
    F2 WIN2K HF3 PW3).
pose proof snp_e2_ra_a0 as (S1 & S10 & Srv & Sret).
apply (g_ret (fx:=fx') W E2v snp_e2 ms3 md3 _ HS3 Srv Sret).
intros mat'. cbv beta. split; [reflexivity|].
set (md4 := with_vm_backing (m_vm_lazy md3) mat' md3).
pose proof F3 as (HA3 & Hsb3 & Hp3 & Hfr3 & Hpm3 & Hkp3).
assert (RD3 : forall (r : bv 5) v, sr_get (ss_regs snp_e2) r = v -> getr (ms_regs ms3) r = sv_denot E2v v).
{ intros r v Hr. exact (g_reg (fx:=fx') W E2v snp_e2 ms3 r v HS3 Hr). }
assert (EOLD : forall (r : bv 5), (Z.to_nat (bv_unsigned r) < 32)%nat -> ew E2v (Z.to_nat (bv_unsigned r)) = getr regs r).
{ intros r Hr. unfold E2v. rewrite ew_havoc_old by exact Hr. apply EREG. }
assert (RA3 : getr (ms_regs ms3) 1 = getr regs 1).
{ rewrite (RD3 _ _ S1). cbn [sv_denot]. rewrite Z.add_0_r.
  change 1%nat with (Z.to_nat (bv_unsigned (1%bv : bv 5))). rewrite EOLD by (vm_compute; lia). apply Z_to_bv_bv_unsigned. }
exists fx', (ms_regs ms3), (ms_mem ms3), md4.
split.
{ unfold cfg_at. rewrite RA3. unfold ret_ok in Hret. rewrite Hret. unfold raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split; [exact FP1|]. split; [exact FP2|].
assert (HA4 : ARx ly S Hp W (ms_mem ms3) md4).
{ pose proof (same_but_materialized_frame md3 _ (with_vm_backing_same md3 mat')) as MF.
  apply (alx_frame ly S Hp W (ms_mem ms3) md3 (ms_mem ms3) md4 HA3);
    [intros; reflexivity | intros a Hv; exact Hv | apply MF | apply MF | apply MF | intros; reflexivity]. }
split; [exact HA4|].
split.
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hin2 : In r KEPT) by (unfold KEPT; cbn [In]; lia).
  rewrite (RD3 _ _ (snp_e2_r r Hin2)). cbn [sv_denot]. rewrite Z.add_0_r.
  assert (Hr5 : bv_unsigned (Z_to_bv 5 r) = r).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. apply Z.mod_small. lia. }
  replace (Z.to_nat r) with (Z.to_nat (bv_unsigned (Z_to_bv 5 r))) by (rewrite Hr5; reflexivity).
  rewrite EOLD by (rewrite Hr5; lia). apply Z_to_bv_bv_unsigned. }
split; [eapply same_but_materialized_trans; [exact Hsb3 | apply with_vm_backing_same]|].
split.
{ rewrite (RD3 _ _ S10). cbn [sv_denot]. rewrite Z.add_0_r.
  assert (X : ew E2v 36 = getr regs2 10) by (unfold E2v, havoc; cbn [ew]; reflexivity).
  rewrite X, Z_to_bv_bv_unsigned. exact G10b. }
split.
{ intros i Hi. rewrite (aview_same (w_H W) mem2 (ms_mem ms3)); [exact (HDb i Hi)|].
  apply HF3. rewrite unsigned_lit_small by (unfold amem_range in Ham; lia). intros Hwi.
  pose proof (WIN2 _ Hwi). lia. }
split.
{ intros a Ha H1 H2. apply Hfr3; [exact Ha | exact H2 | exact H1]. }
split; [exact Hpm3 | exact Hkp3].
Qed.
End m.
