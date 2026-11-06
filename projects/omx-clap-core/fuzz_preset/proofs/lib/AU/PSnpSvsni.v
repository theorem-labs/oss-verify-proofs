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
(* Modified by Theorem Labs, 2026-10: image B twin (fuzz_preset.asan-ubsan, unstripped 3b5e1a09, pin f8f98a95) of
   lib/A/PSnpSvsni.v: image A's modules (AB1v AE34 AF0l AF0m AF0x AE20 AE2y AE3h AE2p) -> image B's (YB1v YE34 YF0l YF0m YF0x
   YE20 YE2y YE3h YE2p), the defs / walk / rodata layers' lib/A files -> their lib/AU twins (same names, B values).
   Numerals relocated A -> B by symbol + offset (pyelftools + capstone), A's tables above read at B as:
     ___interceptor_vsnprintf                         +0x0    0x46188 -> 0x4620c
     ___interceptor_vsnprintf                         +0xa0   0x46228 -> 0x462ac
     ___interceptor_vsnprintf                         +0x178  0x46300 -> 0x46384
     ___interceptor_vsnprintf                         +0xa4   0x4622c -> 0x462b0
     __interception::real_vsnprintf (object)          +0x0    0xa3850 -> 0xa40f0  (the real_vsnprintf cell, holding vsnprintf 0x9aed8: a row of YF0m.v, blob d82ec2d7dae8)
   TFIB_IMG_END is 0x600000 at A' and 0x601000 at B' (YF0x.v). *)
(* Modified by Theorem Labs, 2026-10: port-fm 00daeaf3796's destination slack (origin/cold/port-fm-rtprintf-param, the
   final text 3e35620c52e) passed through: the _xa entry's 'amem_range d (sn_len (n - 1) T + 8)' is the Section
   hypothesis HD8, handed unchanged to musl vsnprintf's contract (sn_applyA). The '+ 8' is an address-range fact. *)
(* Modified by Theorem Labs, 2026-10: the memnorm keep (c-omx-alloc 17:03Z ruling (b); the kit texts of
   origin/cold/c-libc-stdio-presetsnp-vfp 43002a8926a7): the post ends in `YAkMemnorm.memnorm segs mem ->
   YAkMemnorm.memnorm segs mem'` (sn_post), from sw_frame's 6th conjunct; at each sw_step the callee's keep: printf_common's
   and musl vsnprintf's from their posts' last conjunct (printf_common's through kcall's Q), Gwrc / GwrcT's from POSTr's
   raw frame over [sp - RC_SCR, sp) and the present window by PSnpKeep.memnorm_of_subframe_dw (empty destination);
   POSTa (the after-REAL post) carries the keep to the end. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import PSnpShared PSnpSx PSnpSk.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import PSnpGkit PSnpGt PSnpGvsnikit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PSnpGk.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PSnpGwrc PSnpGwrcT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PSnpGvsni PSnpRodata.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm PSnpKeep.
Import ListNotations.
Open Scope Z_scope.

(* ---- the interceptor's own frame [entry - 0x880, entry): 0x870 of frame and TryAsanInitFromRtl's 0x10 below it ---- *)
Definition FRK : Z := 0x880.
Ltac zl := cbv beta in *; unfold FRK, STK_PCOM, PSnpGwrc.RC_SCR, SNK_STK, OSP_VSN, OSP_VSNI, ESTACK, kHighMemBeg,
  kHighMemEnd in *; lia.
Definition stkF : YP09.region := YP09.mkRegion (Some 2%nat) (- FRK) 0 (- FRK) 0 [].
Definition ssF : sstate :=
  mkSS A_VSNI sr_atoms (stkF :: map ro_region vsni_rodata) None (mkFacts [(2%nat, mkAF (2^44) (2^47) 4)] [] []).
(* FMsnprintfGvsni's runs over the frame region: to printf_common, to REAL (vsnprintf), from its return to the two
   branches, to the check at 0x45a18 (size >= res + 1) or at 0x45944 (size < res + 1) *)
Definition fA : sstate := Eval vm_compute in fst (RUNTO A_PCOM ssF).
Lemma r_fA : RUNTO A_PCOM ssF = (fA, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition fB : sstate := Eval vm_compute in fst (RUNTO A_VSN (kafter 32 fA RA_PCOM_VSNI (-0x870) 0 0)).
Lemma r_fB : RUNTO A_VSN (kafter 32 fA RA_PCOM_VSNI (-0x870) 0 0) = (fB, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition fB0 : sstate := Eval vm_compute in set_mem fB (firstn 1 (ss_mem fB)).
Definition fC : sstate := Eval vm_compute in fst (RUN (kafter 48 fB0 RA_VSN (-0x870) 0 0)).
Lemma r_fC : RUN (kafter 48 fB0 RA_VSN (-0x870) 0 0) = (fC, RS_stopped (SR_branch BC_LT (SOff 52 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition fD : sstate := Eval vm_compute in fst (RUN (AC fC BC_GE (SOff 52 0) (SLit 0))).
Lemma r_fD : RUN (AC fC BC_GE (SOff 52 0) (SLit 0)) =
  (fD, RS_stopped (SR_branch BC_GEU (SOff 11 0) (SAluw ALU_ADD (SOff 52 0) (SLit 1)))).
Proof. vm_compute. reflexivity. Qed.
Definition fE : sstate :=
  Eval vm_compute in fst (RUNTO WRC_ENTRY (AC fD BC_GEU (SOff 11 0) (SAluw ALU_ADD (SOff 52 0) (SLit 1)))).
Lemma r_fE : RUNTO WRC_ENTRY (AC fD BC_GEU (SOff 11 0) (SAluw ALU_ADD (SOff 52 0) (SLit 1))) = (fE, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition fEt : sstate := Eval vm_compute in
  fst (RUNTO PSnpGwrcT.RT_ENTRY (AC fD BC_LTU (SOff 11 0) (SAluw ALU_ADD (SOff 52 0) (SLit 1)))).
Lemma r_fEt : RUNTO PSnpGwrcT.RT_ENTRY (AC fD BC_LTU (SOff 11 0) (SAluw ALU_ADD (SOff 52 0) (SLit 1))) =
  (fEt, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition stk_okF (ss : sstate) : bool :=
  match ss_mem ss with
  | r :: _ => obase_eqb (YP09.r_base r) (Some 2%nat) && (YP09.r_wlo r =? - FRK) && (YP09.r_whi r =? 0)
  | [] => false
  end.
Definition win_okF (ss : sstate) : bool :=
  forallb (fun t => win_eqb t (Some 2%nat, - FRK, 0) || (snd t <=? snd (fst t))) (windows (ss_mem ss)).

(* ---- res = |T| < 2^31 - 1 (FMsnprintfGvsni asked res <= 2^30) ---- *)
Lemma U_addw1' : forall E v, ew E 52 = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 - 1 ->
  U E (SAluw ALU_ADD (SOff 52 0) (SLit 1)) = v + 1.
Proof.
intros E v Hv Hr. rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite (U_atom E 52 v Hv) by lia. rewrite U_SLit.
change (zcanon 1 mod 2 ^ 32) with 1. rewrite (Z.mod_small v (2 ^ 32)) by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small (v + 1 + 2 ^ 31) (2 ^ 32)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma br_ge0' : forall E v, ew E 52 = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 - 1 ->
  branch_taken BC_LT (sv_denot E (SOff 52 0)) (sv_denot E (SLit 0)) = false.
Proof.
intros E v Hv Hr. cbn [branch_taken]. unfold bv_lts. rewrite !signed_is_swrap_unsigned.
fold (U E (SOff 52 0)). fold (U E (SLit 0)). rewrite (U_atom E 52 v Hv) by lia. rewrite U_SLit.
change (zcanon 0) with 0. rewrite !swrap64_id by (unfold half64; lia). apply Z.ltb_ge. lia.
Qed.
Lemma br_room' : forall E v n, ew E 11 = Z_to_bv 64 n -> ew E 52 = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 - 1 ->
  v + 1 <= n -> n < 2 ^ 31 ->
  branch_taken BC_GEU (sv_denot E (SOff 11 0)) (sv_denot E (SAluw ALU_ADD (SOff 52 0) (SLit 1))) = true.
Proof.
intros E v n Hn Hv H0 H1 H2. rewrite branch_geu_U, (U_atom E 11 n Hn) by lia. rewrite (U_addw1' E v Hv) by lia.
apply negb_true_iff, Z.ltb_ge. lia.
Qed.
Lemma br_trunc : forall E v n, ew E 11 = Z_to_bv 64 n -> ew E 52 = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 - 1 ->
  0 <= n < v + 1 ->
  branch_taken BC_GEU (sv_denot E (SOff 11 0)) (sv_denot E (SAluw ALU_ADD (SOff 52 0) (SLit 1))) = false.
Proof.
intros E v n Hn Hv H0 H1. rewrite branch_geu_U, (U_atom E 11 n Hn) by lia. rewrite (U_addw1' E v Hv) by lia.
apply negb_false_iff, Z.ltb_lt. lia.
Qed.
Lemma U_x9' : forall E v, ew E 52 = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 - 1 ->
  sv_denot E (SAlu ALU_ADD (SAluw ALU_ADD (SOff 52 0) (SLit 1)) (SLit 0)) = Z_to_bv 64 (v + 1).
Proof.
intros E v Hv Hr. rewrite denot_lit_U, U_SAlu. cbn [zalu_raw]. rewrite (U_addw1' E v Hv Hr), U_SLit.
change (zcanon 0) with 0. rewrite Z.add_0_r. rewrite zcanon_small by lia. reflexivity.
Qed.
(* the written part: |T| + 1 when the text fits, else n *)
Lemma sn_len_cases : forall n T, 1 <= n ->
  (Z.of_nat (length T) + 1 <= n /\ sn_len (n - 1) T = Z.of_nat (length T) + 1) \/
  (n < Z.of_nat (length T) + 1 /\ sn_len (n - 1) T = n).
Proof.
intros n T Hn. destruct (Z_lt_le_dec n (Z.of_nat (length T) + 1)) as [Hlt|Hle].
- right. split; [exact Hlt|]. unfold sn_len, sn_bytes. rewrite length_app, length_firstn. cbn [length].
  rewrite Nat.min_l by lia. lia.
- left. split; [exact Hle|]. apply sn_len_full. lia.
Qed.

(* ---- the entry registers as atoms; the walk's windows ---- *)
Definition EOK (regs : bvmap 5 word) (E : env) : Prop :=
  forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r.
Lemma EOK_spK : forall regs E, EOK regs E -> bv_unsigned (ew E 2) = spZ regs.
Proof. intros regs E HE. rewrite (HE 2%nat 2%bv eq_refl). reflexivity. Qed.
Lemma EOK_havocK : forall regs E k ws, EOK regs E -> (32 <= k)%nat -> EOK regs (havoc E k ws).
Proof.
intros regs E k ws HE Hk i r Hi. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
rewrite EOK_havoc_lt by lia. apply HE. exact Hi.
Qed.
Lemma win_inK : forall E ss sp, win_okF ss = true -> bv_unsigned (ew E 2) = sp ->
  forall a, in_wrange E (ss_mem ss) a -> sp - FRK <= a < sp.
Proof.
intros E ss sp Hb H2 a Hin. pose proof (in_wrange_single_b E (ss_mem ss) a 2 (- FRK) 0 _ Hb H2 Hin). lia.
Qed.
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma win_presK : forall (W : world tfibsegs) E ss ms sp a, st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  stk_okF ss = true -> bv_unsigned (ew E 2) = sp -> kHighMemBeg <= sp - FRK -> sp <= 2 ^ 47 ->
  sp - FRK <= a < sp -> apresent (w_H W) (ms_mem ms) a.
Proof.
intros W E ss ms sp a HS Hk H2 B1 B2 Ha.
unfold stk_okF in Hk. destruct (ss_mem ss) as [|r0 rest] eqn:Hm; [discriminate|].
apply andb_prop in Hk as [Hk Hh]. apply andb_prop in Hk as [Hb Hl].
apply obase_eqb_eq in Hb. apply Z.eqb_eq in Hl. apply Z.eqb_eq in Hh.
apply (st_ok_window_apresent (w_H W) E ss ms 0 r0 a HS ltac:(rewrite Hm; reflexivity)).
- rewrite Hb, Hl, Hh. cbn [base_val]. rewrite H2. lia.
- unfold TFIB_IMG_END. zl.
Qed.
(* a run whose writable windows lie in [rlo, hi), inside the frame's window [lo, hi) *)
Lemma sw_runR : forall B (ARx : alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model -> Prop),
  ARx_frame_law tfibsegs B ARx -> ARx_stack_law tfibsegs B ARx ->
  (forall ly S Hp W mem md, ARx ly S Hp W mem md -> kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd) ->
  forall ly S Hp W mem0 md0 lo hi XW rlo mem md memB mat E rs,
  ly_stk_lo ly <= lo -> hi <= ly_stk_hi ly -> 0 <= lo -> hi <= 2 ^ 64 -> lo <= rlo ->
  sw_frame tfibsegs ARx ly S Hp W mem0 md0 lo hi XW mem md ->
  (forall a, in_wrange E rs a -> rlo <= a < hi) -> frame_of E rs mem memB ->
  (forall a, rlo <= a < hi -> apresent (w_H W) memB a) ->
  sw_frame tfibsegs ARx ly S Hp W mem0 md0 lo hi XW memB (with_vm_backing (m_vm_lazy md) mat md).
Proof.
intros B ARx alx_frame alx_stack stk_bounds_x ly S Hp W mem0 md0 lo hi XW rlo mem md memB mat E rs L1 L2 L3 L4 L5 HF
  Hw Hfo Hpz.
apply (sw_run tfibsegs B ARx alx_frame alx_stack stk_bounds_x ly S Hp W mem0 md0 lo hi XW L1 L2 mem md memB mat E rs HF);
  [intros a Hin; pose proof (Hw a Hin); lia | exact Hfo |].
intros a Ha. destruct (Z_lt_le_dec a rlo) as [Lt|Ge]; [|apply Hpz; lia].
pose proof HF as (_ & _ & Hpm & _ & _).
apply (apresent_same (w_H W) mem memB a); [|apply Hpm; lia].
apply Hfo. rewrite unsigned_lit_small by lia. intros Hin. pose proof (Hw a Hin). lia.
Qed.
End h.

(* ==== after REAL (vsnprintf) returns: generic in the FP state the callee returned with ==== *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
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
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (d n : Z) (T : list Z) (K : Z).
(* the walk's window K holds its frame and the check's scratch, ESTACK below entry - 0x870 *)
Hypothesis HKK : 0x870 + ESTACK <= K.
(* what the walk keeps from the interceptor's entry (regs, mem, md) *)
Definition aft_pre : Prop :=
  ARx ly S Hp W mem md /\ ly_stk_lo ly + K <= spZ regs /\ spZ regs <= ly_stk_hi ly /\
  spZ regs mod 16 = 0 /\ YK0s.ret_ok (getr regs 1) /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  getr regs 10 = w64 d /\ getr regs 11 = w64 n /\ 1 <= n < 2 ^ 31 /\ Z.of_nat (length T) < 2 ^ 31 - 1 /\ 0 < d /\
  d + sn_len (n - 1) T <= 2 ^ 63 /\ zdisjoint (spZ regs - K, K) (d, sn_len (n - 1) T) /\
  amem_range d (sn_len (n - 1) T) /\
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF d (sn_len (n - 1) T) /\
  shadow_hull_vis (aview tfibsegs (w_H W) mem) d (sn_len (n - 1) T).
Hypothesis HAFT : aft_pre.
Definition XWd (a : Z) : Prop := d <= a < d + sn_len (n - 1) T.
Definition INV (m : word -> option byte) (md' : Model) : Prop :=
  sw_frame tfibsegs ARx ly S Hp W mem md (spZ regs - K) (spZ regs) XWd m md'.
Definition BYTES (m : word -> option byte) : Prop :=
  forall i, 0 <= i < sn_len (n - 1) T ->
    aview tfibsegs (w_H W) m (d + i) = Some (nth (Z.to_nat i) (sn_bytes (n - 1) T) 0).
Definition SLOTS (m : word -> option byte) : Prop :=
  forall j, (j < 9)%nat -> val_mem tfibsegs (mrestrict (w_H W) m) (spZ regs - 8 - 8 * Z.of_nat j) 8
    (bv_unsigned (getr regs (Z_to_bv 5 (nth j SAVED 0)))).
Definition POSTa : world tfibsegs -> config -> Prop := fun W' c' => W' = W /\ exists regs' mem' md',
  c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
  ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
  getr regs' 10 = w64 (Z.of_nat (length T)) /\ BYTES mem' /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (n - 1) T) -> ~ (spZ regs - K <= a < spZ regs) ->
     aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
  (YAkMemnorm.memnorm tfibsegs mem -> YAkMemnorm.memnorm tfibsegs mem').

Lemma bas : kHighMemBeg <= spZ regs - K /\ spZ regs <= 2 ^ 47 /\ 2 ^ 44 <= spZ regs - K /\
  spZ regs mod 16 = 0 /\ ly_stk_lo ly <= spZ regs - K /\ spZ regs <= ly_stk_hi ly /\
  1 <= n < 2 ^ 31 /\ Z.of_nat (length T) < 2 ^ 31 - 1 /\ 0 < d /\ 1 <= sn_len (n - 1) T /\
  d + sn_len (n - 1) T <= 2 ^ 63 /\ zdisjoint (spZ regs - K, K) (d, sn_len (n - 1) T) /\
  amem_range d (sn_len (n - 1) T).
Proof.
pose proof HAFT as (HA & HKlo & HKhi & H16 & _ & _ & _ & _ & _ & Hn & HT & Hd0 & Hdw & Hdj & Ham & _).
pose proof (stk_bounds_x ly S Hp W mem md HA) as [K1 K2].
pose proof (sn_len_pos (n - 1) T) as Hw1.
split; [zl|]. split; [zl|]. split; [zl|]. split; [exact H16|]. split; [zl|]. split; [exact HKhi|].
split; [exact Hn|]. split; [exact HT|]. split; [exact Hd0|]. split; [exact Hw1|]. split; [exact Hdw|].
split; [exact Hdj | exact Ham].
Qed.
Lemma inv_pres : forall m md', INV m md' -> forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) m a.
Proof. intros m md' (_ & _ & Hpz & _ & _) a Ha. exact (Hpz a Ha). Qed.
(* a run of the walk's own code, its windows in the interceptor's window *)
Lemma v_run : forall m1 md1 mB mat E rs, INV m1 md1 ->
  (forall a, in_wrange E rs a -> spZ regs - FRK <= a < spZ regs) -> frame_of E rs m1 mB ->
  (forall a, spZ regs - FRK <= a < spZ regs -> apresent (w_H W) mB a) ->
  INV mB (with_vm_backing (m_vm_lazy md1) mat md1).
Proof.
intros m1 md1 mB mat E rs HI Hw Hf Hpz. pose proof bas as (B1 & B2 & _ & _ & L1 & L2 & _).
exact (sw_runR B ARx alx_frame alx_stack stk_bounds_x ly S Hp W mem md _ _ XWd (spZ regs - FRK) m1 md1 mB mat E rs L1 L2 ltac:(zl) ltac:(zl) ltac:(zl)
  HI Hw Hf Hpz).
Qed.
Lemma bytes_run : forall E rs m mB, BYTES m ->
  (forall a, in_wrange E rs a -> spZ regs - FRK <= a < spZ regs) -> frame_of E rs m mB -> BYTES mB.
Proof.
intros E rs m mB HB Hw Hfo i Hi.
pose proof bas as (_ & _ & _ & _ & _ & _ & _ & _ & Hd0 & Hw1 & Hdw & Hdj & _).
unfold zdisjoint in Hdj. cbn [fst snd] in Hdj.
rewrite <- (HB i Hi). apply aview_same. apply Hfo.
rewrite unsigned_lit_small by lia. intros Hin. pose proof (Hw _ Hin). zl.
Qed.
(* the shadow of a destination byte lies outside the window and the destination *)
Lemma shadow_out : forall y, d <= y < d + sn_len (n - 1) T ->
  0 <= SHADOW_OFF + y / 8 < 2 ^ 64 /\ ~ (spZ regs - K <= SHADOW_OFF + y / 8 < spZ regs) /\
  ~ XWd (SHADOW_OFF + y / 8).
Proof.
intros y Hy. pose proof bas as (B1 & B2 & B3 & _ & _ & _ & _ & _ & Hd0 & Hw1 & Hdw & Hdj & Ham).
assert (Hd : 0 <= y / 8 < 2 ^ 44).
{ split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham. lia. }
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF, XWd in *. lia.
Qed.
(* so does the 8-aligned shadow hull of a prefix of the destination *)
Lemma hull_out : forall k s, 1 <= k <= sn_len (n - 1) T ->
  shadow_addr d / 8 * 8 <= s < shadow_addr (d + k - 1) / 8 * 8 + 8 ->
  0 <= s < 2 ^ 64 /\ ~ (spZ regs - K <= s < spZ regs) /\ ~ XWd s.
Proof.
intros k s Hk Hs. pose proof bas as (B1 & B2 & B3 & _ & _ & _ & _ & _ & Hd0 & Hw1 & Hdw & Hdj & Ham).
unfold shadow_addr in Hs.
assert (Q1 : 0 <= d / 8 < 2 ^ 44).
{ split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham. lia. }
assert (Q2 : 0 <= (d + k - 1) / 8 < 2 ^ 44).
{ split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham. lia. }
assert (Q3 : d / 8 <= (d + k - 1) / 8) by (apply Z.div_le_mono; lia).
assert (Q4 : 8 * (d / 8) <= d) by (apply Z.mul_div_le; lia).
set (q1 := SHADOW_OFF + d / 8) in Hs. set (q2 := SHADOW_OFF + (d + k - 1) / 8) in Hs.
pose proof (Z.div_mod q1 8 ltac:(lia)) as M1. pose proof (Z.mod_pos_bound q1 8 ltac:(lia)) as M2.
pose proof (Z.div_mod q2 8 ltac:(lia)) as M3. pose proof (Z.mod_pos_bound q2 8 ltac:(lia)) as M4.
subst q1 q2. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF, XWd in *. lia.
Qed.
Lemma slots_kept : forall m m', SLOTS m ->
  (forall a, spZ regs - 0x48 <= a < spZ regs -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  SLOTS m'.
Proof.
intros m m' HS Heq j Hj. apply (val_mem_kept (w_H W) (w_H W) m m'); [|exact (HS j Hj)].
intros k Hk. apply Heq. change (Z.of_nat 8) with 8 in Hk. lia.
Qed.
(* a register the walk keeps *)
Lemma reg_kept : forall E ss ms (r : Z) (i : nat), EOK regs E -> st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  sr_get (ss_regs ss) (Z_to_bv 5 r) = SOff i 0 -> Z.of_nat i = r -> 0 <= r < 32 ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Proof.
intros E ss ms r i HE HS Hg Hi Hr. rewrite (g_reg W E ss ms _ _ HS Hg), den_atom. apply HE.
rewrite bvu5 by exact Hr. exact Hi.
Qed.
(* the saved slots of a state of the walk *)
Lemma slots_of : forall E ss ms, EOK regs E -> st_ok tfibsegs E ss (restrict (w_H W) ms) -> stk_okF ss = true ->
  bv_unsigned (ew E 2) = spZ regs ->
  (forall j, (j < 9)%nat ->
     In (YP09.mkChunk (- 8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat (nth j SAVED 0)) 0))) (stk_chunks ss)) ->
  SLOTS (ms_mem ms).
Proof.
intros E ss ms HE HS Hk H2 Hin j Hj. pose proof (saved_range j Hj) as Hsr.
unfold stk_okF, stk_chunks in *. destruct (ss_mem ss) as [|r0 rest] eqn:Hm; [discriminate|].
apply andb_prop in Hk as [Hk _]. apply andb_prop in Hk as [Hb _]. apply obase_eqb_eq in Hb.
pose proof (g_slot W E ss ms 0 r0 _ 8 _ (bv_unsigned (getr regs (Z_to_bv 5 (nth j SAVED 0)))) HS
  ltac:(rewrite Hm; reflexivity) (Hin j Hj)) as X.
rewrite Hb in X. cbn [base_val] in X. rewrite H2 in X.
replace (spZ regs - 8 - 8 * Z.of_nat j) with (spZ regs + (- 8 - 8 * Z.of_nat j)) by lia.
apply X.
- rewrite den_atom, (HE _ (Z_to_bv 5 (nth j SAVED 0))). { symmetry. apply Z_to_bv_bv_unsigned. }
  rewrite bvu5 by exact Hsr. apply Z2Nat.id. lia.
- change (8 * Z.of_N 8) with 64. apply u64_range.
- cbn. lia.
Qed.

(* ---- the epilogue, from the check's return ---- *)
Lemma vsni_epi : forall regs3 mem3 md3,
  INV mem3 md3 ->
  getr regs3 2 = w64 (spZ regs - 0x870) -> getr regs3 10 = w64 (Z.of_nat (length T)) ->
  (forall r, In r [3; 4; 24; 25; 26; 27] -> getr regs3 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  SLOTS mem3 -> BYTES mem3 ->
  SRr tfibsegs W (cfg_at tfibsegs WRC_END regs3 mem3 md3) POSTa.
Proof.
intros regs3 mem3 md3 HI R2 R10 RK SV HBY.
pose proof bas as (B1 & B2 & B3 & B4 & _).
pose proof HAFT as (_ & _ & _ & _ & Hret & _).
set (E5 := Ereg regs3 (map (fun r => getr regs (Z_to_bv 5 r)) SAVED)).
assert (E5_2 : bv_unsigned (ew E5 2) = spZ regs - 0x870).
{ subst E5. rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. zl. }
assert (E5_x : forall j, (j < 9)%nat -> ew E5 (32 + j) = getr regs (Z_to_bv 5 (nth j SAVED 0))).
{ intros j Hj. subst E5. rewrite ew_Ereg_extra. do 9 (destruct j as [|j]; [reflexivity|]). lia. }
assert (E5_r : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E5 i = getr regs3 r)
  by (intros i r Hi; subst E5; apply ew_Ereg_nat; exact Hi).
assert (HSe : st_ok tfibsegs E5 ss_epi (restrict (w_H W) (mkst regs3 (Z_to_bv 64 WRC_END) mem3 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_epi. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    change (Ereg regs3 (map (fun r => getr regs (Z_to_bv 5 r)) SAVED)) with E5. rewrite E5_2.
    split; [zl|]. split; [zl|]. split; [intros o Ho; exfalso; lia|].
    unfold epi_chunks. apply Forall_map. apply Forall_forall. intros j Hj. apply in_seq in Hj.
    apply (chunk_ok_val tfibsegs E5 _ _ _ 8 _ (bv_unsigned (getr regs (Z_to_bv 5 (nth j SAVED 0))))).
    + rewrite den_atom, E5_x by lia. symmetry. apply Z_to_bv_bv_unsigned.
    + change (8 * Z.of_N 8) with 64. apply u64_range.
    + cbn. lia.
    + replace (spZ regs - 0x870 + (0x868 - 8 * Z.of_nat j)) with (spZ regs - 8 - 8 * Z.of_nat j) by lia.
      apply SV. lia.
  - apply pairwise_disjoint_of_extents. cbn. repeat split.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    change (Ereg regs3 (map (fun r => getr regs (Z_to_bv 5 r)) SAVED)) with E5. rewrite E5_2.
    change (2 ^ 4) with 16. split; [|exact I]. split; [zl|]. split; [|zl].
    replace (spZ regs - 0x870) with (spZ regs + (-135) * 16) by lia. rewrite Z_mod_plus_full. exact B4. }
unfold cfg_at. change (w64 WRC_END) with (Z_to_bv 64 WRC_END).
eapply SRr_bind; [exact (g_phase W E5 ss_epi epi_e _ _ md3 HSe r_epi)|].
intros W1 c1 _ (-> & ms5 & mat5 & -> & HS5 & HF5).
change (st_ok tfibsegs E5 epi_e (restrict (w_H W) ms5)) in HS5.
assert (MEQ5 : forall z, ms_mem ms5 z = mem3 z).
{ intros z. apply HF5. intros Hin.
  pose proof (in_wrange_single_b E5 (ss_mem ss_epi) _ 2 0x828 0x828 _ ltac:(vm_compute; reflexivity) eq_refl Hin).
  lia. }
apply (g_ret W E5 epi_e ms5 _ POSTa HS5 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
intros mat'.
assert (RD : forall (r : bv 5) v, sr_get (ss_regs epi_e) r = v -> getr (ms_regs ms5) r = sv_denot E5 v)
  by (intros r v Hv; exact (g_reg W E5 epi_e ms5 r v HS5 Hv)).
assert (P1 : getr (ms_regs ms5) 1 = getr regs 1).
{ rewrite (RD 1%bv (SOff 32 0)) by (vm_compute; reflexivity). rewrite den_atom. exact (E5_x 0%nat ltac:(lia)). }
assert (HI5 : INV (ms_mem ms5) (with_vm_backing (m_vm_lazy md3) mat5 md3)).
{ apply (v_run mem3 md3 (ms_mem ms5) mat5 E5 (ss_mem ss_epi) HI).
  - intros a Hin. exfalso.
    pose proof (in_wrange_single_b E5 (ss_mem ss_epi) _ 2 0x828 0x828 _ ltac:(vm_compute; reflexivity) eq_refl Hin).
    lia.
  - exact HF5.
  - intros a Ha. apply (apresent_same (w_H W) mem3 (ms_mem ms5) a (MEQ5 _)). exact (inv_pres _ _ HI a ltac:(zl)). }
assert (HI6 : INV (ms_mem ms5) (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md3) mat5 md3)) mat'
  (with_vm_backing (m_vm_lazy md3) mat5 md3))).
{ apply (v_run (ms_mem ms5) _ (ms_mem ms5) mat' E5 [] HI5).
  - intros a (r & Hr & _). destruct Hr.
  - apply frame_of_refl.
  - intros a Ha. exact (inv_pres _ _ HI5 a ltac:(zl)). }
destruct HI6 as (HA6 & Hsb6 & Hp6 & Hfr6 & Hpr6 & Hkp6).
unfold POSTa. split; [reflexivity|].
exists (ms_regs ms5), (ms_mem ms5),
  (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md3) mat5 md3)) mat' (with_vm_backing (m_vm_lazy md3) mat5 md3)).
split.
{ replace (v_jalr (getr (ms_regs ms5) 1) 0) with (w64 (raZ regs)); [reflexivity|].
  rewrite P1. unfold raZ, w64. rewrite Z_to_bv_bv_unsigned. symmetry. exact Hret. }
split; [exact HA6|].
split.
{ intros r Hr. unfold acallee_saved in Hr.
  assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  assert (SVD : forall (j : nat), (j < 9)%nat -> sr_get (ss_regs epi_e) (Z_to_bv 5 (nth j SAVED 0)) = SOff (32 + j) 0 ->
    getr (ms_regs ms5) (Z_to_bv 5 (nth j SAVED 0)) = getr regs (Z_to_bv 5 (nth j SAVED 0))).
  { intros j Hj Hg. rewrite (RD _ _ Hg), den_atom. exact (E5_x j Hj). }
  assert (KPT : forall (r' : Z), In r' [3; 4; 24; 25; 26; 27] ->
    sr_get (ss_regs epi_e) (Z_to_bv 5 r') = SOff (Z.to_nat r') 0 ->
    getr (ms_regs ms5) (Z_to_bv 5 r') = getr regs (Z_to_bv 5 r')).
  { intros r' Hin Hg. assert (Hr' : 0 <= r' < 32) by (cbn [In] in Hin; lia).
    rewrite (RD _ _ Hg), den_atom, (E5_r (Z.to_nat r') (Z_to_bv 5 r')).
    - exact (RK r' Hin).
    - rewrite bvu5 by exact Hr'. apply Z2Nat.id. lia. }
  assert (SP2 : getr (ms_regs ms5) (Z_to_bv 5 2) = getr regs (Z_to_bv 5 2)).
  { rewrite (RD _ (SOff 2 2160)) by (vm_compute; reflexivity). cbn [sv_denot]. rewrite E5_2.
    replace (spZ regs - 0x870 + 2160) with (spZ regs) by lia.
    replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity).
    unfold spZ. apply Z_to_bv_bv_unsigned. }
  repeat destruct C as [C|C]; subst r;
  first [ exact SP2
        | exact (SVD 0%nat ltac:(lia) ltac:(vm_compute; reflexivity))
        | exact (SVD 1%nat ltac:(lia) ltac:(vm_compute; reflexivity))
        | exact (SVD 2%nat ltac:(lia) ltac:(vm_compute; reflexivity))
        | exact (SVD 3%nat ltac:(lia) ltac:(vm_compute; reflexivity))
        | exact (SVD 4%nat ltac:(lia) ltac:(vm_compute; reflexivity))
        | exact (SVD 5%nat ltac:(lia) ltac:(vm_compute; reflexivity))
        | exact (SVD 6%nat ltac:(lia) ltac:(vm_compute; reflexivity))
        | exact (SVD 7%nat ltac:(lia) ltac:(vm_compute; reflexivity))
        | exact (SVD 8%nat ltac:(lia) ltac:(vm_compute; reflexivity))
        | (apply KPT; [cbn; tauto | vm_compute; reflexivity]) ]. }
split; [exact Hsb6|].
split.
{ rewrite (RD 10%bv (SOff 10 0)) by (vm_compute; reflexivity). rewrite den_atom, (E5_r 10%nat 10%bv eq_refl). exact R10. }
split; [intros i Hi; rewrite <- (HBY i Hi); apply aview_same; apply MEQ5|].
split; [intros a Ha H1 H2; apply Hfr6; [exact Ha | exact H2 | exact H1]|].
split; [exact Hpr6 | exact Hkp6].
Qed.

(* ---- WRITE_RANGE (str, res + 1) from 0x45a18 (size >= res + 1), then the epilogue ---- *)
Lemma vsni_wrc : forall regs4 mem4 md4, Z.of_nat (length T) + 1 <= n ->
  INV mem4 md4 ->
  getr regs4 2 = w64 (spZ regs - 0x870) -> getr regs4 9 = w64 (Z.of_nat (length T) + 1) -> getr regs4 18 = w64 d ->
  getr regs4 10 = w64 (Z.of_nat (length T)) -> getr regs4 19 = w64 n ->
  (forall r, In r [3; 4; 24; 25; 26; 27] -> getr regs4 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  SLOTS mem4 -> BYTES mem4 ->
  SRr tfibsegs W (cfg_at tfibsegs WRC_ENTRY regs4 mem4 md4) POSTa.
Proof.
intros regs4 mem4 md4 Hfull HI R2 R9 R18 R10 R19 RK HSL HBY.
pose proof bas as (B1 & B2 & B3 & B4 & L1 & L2 & Hn & HT & Hd0 & Hw1 & Hdw & Hdj & Ham).
pose proof HAFT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hra & Hhull).
assert (HW : sn_len (n - 1) T = Z.of_nat (length T) + 1) by (apply sn_len_full; lia).
pose proof HI as (HA & Hsb & Hb & Hf & Hpz).
assert (SP4 : spZ regs4 = spZ regs - 0x870) by (unfold spZ at 1; rewrite R2; unfold w64; apply unsigned_lit_small; zl).
eapply SRr_bind.
{ apply (PSnpGwrc.vsn_wr_check_srr_x B ARx alx_frame alx_stack alx_const_cells stk_bounds_x TB ly S W regs4 mem4 md4 d
    (Z.of_nat (length T) + 1) Hp (Z.of_nat (length T)) n HA).
  - rewrite SP4. replace (spZ regs - 0x870) with (spZ regs + (-135) * 16) by lia. rewrite Z_mod_plus_full. exact B4.
  - rewrite SP4. zl.
  - rewrite SP4. zl.
  - intros a Ha. rewrite SP4 in Ha. apply (inv_pres _ _ HI). zl.
  - exact R9.
  - exact R18.
  - exact R10.
  - exact R19.
  - lia.
  - lia.
  - lia.
  - lia.
  - rewrite <- HW. exact Ham.
  - rewrite <- HW. apply (ra_xfer _ _ _ _ Hra). intros y Hy. destruct (shadow_out y Hy) as (S1 & S2 & S3).
    apply Hf; assumption.
  - rewrite <- HW. apply (hull_xfer _ _ _ _ Hhull). intros s Hs.
    destruct (hull_out (sn_len (n - 1) T) s ltac:(lia) Hs) as (S1 & S2 & S3). apply Hf; assumption. }
intros W1 c1 _ HQ. unfold PSnpGwrc.POSTr in HQ.
destruct HQ as (-> & regs3 & mem3 & md3 & -> & HA3 & RK3 & Hsb3 & R10' & Hf3 & Hp3 & Hraw3).
rewrite SP4 in Hf3.
assert (OUTW : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 0x870 - 72 <= a < spZ regs - 0x870) ->
  aview tfibsegs (w_H W) mem3 a = aview tfibsegs (w_H W) mem4 a) by (intros a Ha Hn'; apply Hf3; assumption).
assert (R2' : getr regs3 2 = getr regs4 2).
{ exact (RK3 2 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
unfold zdisjoint in Hdj. cbn [fst snd] in Hdj.
apply (vsni_epi regs3 mem3 md3).
- apply (sw_step tfibsegs ARx ly S Hp W mem md _ _ XWd mem4 md4 mem3 md3 HI HA3 Hsb3).
  + intros a Ha. apply Hp3. apply Hb. exact Ha.
  + intros a Ha H1 _. apply OUTW; [exact Ha|]. zl.
  + exact Hp3.
  + intros HMN. apply (PSnpKeep.memnorm_of_subframe_dw tfibsegs (w_H W) mem4 mem3 0 0
      (spZ regs4 - PSnpGwrc.RC_SCR) (spZ regs4) HMN (fun z _ _ Hz => Hraw3 z Hz)).
    * intros a Ha. rewrite SP4 in Ha. apply (inv_pres _ _ HI). zl.
    * intros a Ha. lia.
- rewrite R2'. exact R2.
- exact R10'.
- intros r Hr. rewrite (RK3 r); [exact (RK r Hr) | | | | |]; cbn [In] in Hr; unfold acallee_saved; lia.
- apply (slots_kept mem4 mem3 HSL). intros a Ha. apply OUTW; zl.
- intros i Hi. rewrite <- (HBY i Hi). apply OUTW; zl.
Qed.

(* ---- WRITE_RANGE (str, size) from 0x45944 (size < res + 1, the truncation), then the epilogue ---- *)
Lemma vsni_wrcT : forall regs4 mem4 md4, n < Z.of_nat (length T) + 1 ->
  INV mem4 md4 ->
  getr regs4 2 = w64 (spZ regs - 0x870) -> getr regs4 9 = w64 n -> getr regs4 18 = w64 d ->
  getr regs4 10 = w64 (Z.of_nat (length T)) -> getr regs4 19 = w64 n ->
  (forall r, In r [3; 4; 24; 25; 26; 27] -> getr regs4 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  SLOTS mem4 -> BYTES mem4 ->
  SRr tfibsegs W (cfg_at tfibsegs PSnpGwrcT.RT_ENTRY regs4 mem4 md4) POSTa.
Proof.
intros regs4 mem4 md4 Htr HI R2 R9 R18 R10 R19 RK HSL HBY.
pose proof bas as (B1 & B2 & B3 & B4 & L1 & L2 & Hn & HT & Hd0 & Hw1 & Hdw & Hdj & Ham).
pose proof HAFT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hra & Hhull).
assert (HW : sn_len (n - 1) T = n).
{ destruct (sn_len_cases n T ltac:(lia)) as [(X & _) | (_ & X)]; [lia | exact X]. }
pose proof HI as (HA & Hsb & Hb & Hf & Hpz).
assert (SP4 : spZ regs4 = spZ regs - 0x870) by (unfold spZ at 1; rewrite R2; unfold w64; apply unsigned_lit_small; zl).
eapply SRr_bind.
{ apply (PSnpGwrcT.vsn_wr_check_srr_xT B ARx alx_frame alx_stack alx_const_cells stk_bounds_x TB ly S W regs4 mem4 md4 d n Hp
    (Z.of_nat (length T)) n HA).
  - rewrite SP4. replace (spZ regs - 0x870) with (spZ regs + (-135) * 16) by lia. rewrite Z_mod_plus_full. exact B4.
  - rewrite SP4. zl.
  - rewrite SP4. zl.
  - intros a Ha. rewrite SP4 in Ha. apply (inv_pres _ _ HI). zl.
  - exact R9.
  - exact R18.
  - exact R10.
  - exact R19.
  - lia.
  - lia.
  - lia.
  - lia.
  - rewrite <- HW. exact Ham.
  - rewrite <- HW. apply (ra_xfer _ _ _ _ Hra). intros y Hy. destruct (shadow_out y Hy) as (S1 & S2 & S3).
    apply Hf; assumption.
  - rewrite <- HW. apply (hull_xfer _ _ _ _ Hhull). intros s Hs.
    destruct (hull_out (sn_len (n - 1) T) s ltac:(lia) Hs) as (S1 & S2 & S3). apply Hf; assumption. }
intros W1 c1 _ HQ. unfold PSnpGwrcT.POSTr in HQ.
destruct HQ as (-> & regs3 & mem3 & md3 & -> & HA3 & RK3 & Hsb3 & R10' & Hf3 & Hp3 & Hraw3).
rewrite SP4 in Hf3.
assert (OUTW : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 0x870 - 72 <= a < spZ regs - 0x870) ->
  aview tfibsegs (w_H W) mem3 a = aview tfibsegs (w_H W) mem4 a) by (intros a Ha Hn'; apply Hf3; assumption).
assert (R2' : getr regs3 2 = getr regs4 2).
{ exact (RK3 2 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
unfold zdisjoint in Hdj. cbn [fst snd] in Hdj.
apply (vsni_epi regs3 mem3 md3).
- apply (sw_step tfibsegs ARx ly S Hp W mem md _ _ XWd mem4 md4 mem3 md3 HI HA3 Hsb3).
  + intros a Ha. apply Hp3. apply Hb. exact Ha.
  + intros a Ha H1 _. apply OUTW; [exact Ha|]. zl.
  + exact Hp3.
  + intros HMN. apply (PSnpKeep.memnorm_of_subframe_dw tfibsegs (w_H W) mem4 mem3 0 0
      (spZ regs4 - PSnpGwrc.RC_SCR) (spZ regs4) HMN (fun z _ _ Hz => Hraw3 z Hz)).
    * intros a Ha. rewrite SP4 in Ha. apply (inv_pres _ _ HI). zl.
    * intros a Ha. lia.
- rewrite R2'. exact R2.
- exact R10'.
- intros r Hr. rewrite (RK3 r); [exact (RK r Hr) | | | | |]; cbn [In] in Hr; unfold acallee_saved; lia.
- apply (slots_kept mem4 mem3 HSL). intros a Ha. apply OUTW; zl.
- intros i Hi. rewrite <- (HBY i Hi). apply OUTW; zl.
Qed.

(* ---- from REAL (vsnprintf)'s return: res >= 0, then size >= res + 1 or size < res + 1, to the check ---- *)
Lemma vsni_after : forall E ms md2,
  st_ok tfibsegs E (kafter 48 fB0 RA_VSN (-0x870) 0 0) (restrict (w_H W) ms) -> EOK regs E ->
  ew E 52 = w64 (Z.of_nat (length T)) -> INV (ms_mem ms) md2 -> BYTES (ms_mem ms) ->
  SRr tfibsegs W (mkCfg ms md2) POSTa.
Proof using All.
intros E ms md2 HS HE H52 HI HBY.
pose proof bas as (B1 & B2 & B3 & B4 & L1 & L2 & Hn & HT & Hd0 & Hw1 & Hdw & Hdj & Ham).
pose proof HAFT as (_ & _ & _ & _ & _ & _ & _ & G10 & G11 & _).
pose proof (EOK_spK regs E HE) as E2.
assert (E11 : ew E 11 = Z_to_bv 64 n) by (rewrite (HE 11%nat 11%bv eq_refl); exact G11).
eapply SRr_bind; [exact (g_phase W E _ fC _ ms md2 HS r_fC)|].
intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1).
change (st_ok tfibsegs E fC (restrict (w_H W) ms1)) in HS1.
pose proof (win_inK E (kafter 48 fB0 RA_VSN (-0x870) 0 0) _ ltac:(vm_compute; reflexivity) E2) as WC.
pose proof (v_run _ _ _ mat1 E _ HI WC HF1
  (fun a Ha => win_presK W E fC ms1 _ a HS1 ltac:(vm_compute; reflexivity) E2 ltac:(zl) B2 Ha)) as HI1.
pose proof (bytes_run E _ _ _ HBY WC HF1) as HBY1.
pose proof (st_ok_add_cond_neg tfibsegs E fC _ BC_LT (SOff 52 0) (SLit 0) HS1
  (br_ge0' E (Z.of_nat (length T)) H52 ltac:(lia))) as HS1'.
change (neg_bc BC_LT) with BC_GE in HS1'.
eapply SRr_bind; [exact (g_phase W E (AC fC BC_GE (SOff 52 0) (SLit 0)) fD _ ms1 _ HS1' r_fD)|].
intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2).
change (st_ok tfibsegs E fD (restrict (w_H W) ms2)) in HS2.
pose proof (win_inK E (AC fC BC_GE (SOff 52 0) (SLit 0)) _ ltac:(vm_compute; reflexivity) E2) as WD.
pose proof (v_run _ _ _ mat2 E _ HI1 WD HF2
  (fun a Ha => win_presK W E fD ms2 _ a HS2 ltac:(vm_compute; reflexivity) E2 ltac:(zl) B2 Ha)) as HI2.
pose proof (bytes_run E _ _ _ HBY1 WD HF2) as HBY2.
destruct (Z_lt_le_dec n (Z.of_nat (length T) + 1)) as [Htr|Hfull].
- (* size < res + 1: WRITE_RANGE (str, size) *)
  pose proof (st_ok_add_cond_neg tfibsegs E fD _ BC_GEU (SOff 11 0) (SAluw ALU_ADD (SOff 52 0) (SLit 1)) HS2
    (br_trunc E (Z.of_nat (length T)) n E11 H52 ltac:(lia) ltac:(lia))) as HS2'.
  change (neg_bc BC_GEU) with BC_LTU in HS2'.
  eapply SRr_bind; [exact (g_phase_to W E PSnpGwrcT.RT_ENTRY
    (AC fD BC_LTU (SOff 11 0) (SAluw ALU_ADD (SOff 52 0) (SLit 1))) fEt _ ms2 _ HS2' r_fEt)|].
  intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3).
  change (st_ok tfibsegs E fEt (restrict (w_H W) ms3)) in HS3.
  pose proof (win_inK E (AC fD BC_LTU (SOff 11 0) (SAluw ALU_ADD (SOff 52 0) (SLit 1))) _
    ltac:(vm_compute; reflexivity) E2) as WE.
  pose proof (v_run _ _ _ mat3 E _ HI2 WE HF3
    (fun a Ha => win_presK W E fEt ms3 _ a HS3 ltac:(vm_compute; reflexivity) E2 ltac:(zl) B2 Ha)) as HI3.
  pose proof (bytes_run E _ _ _ HBY2 WE HF3) as HBY3.
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS3 eq_refl) as Hshape.
  rewrite Hshape. replace (Z_to_bv 64 (ss_pc fEt)) with (w64 PSnpGwrcT.RT_ENTRY) by (vm_compute; reflexivity).
  apply (vsni_wrcT (ms_regs ms3) (ms_mem ms3) _ Htr HI3).
  + rewrite (g_reg W E fEt ms3 2%bv (SOff 2 (-2160)) HS3 ltac:(vm_compute; reflexivity)). cbn [sv_denot]. rewrite E2.
    unfold w64. f_equal; lia.
  + rewrite (g_reg W E fEt ms3 9%bv (SOff 11 0) HS3 ltac:(vm_compute; reflexivity)). rewrite den_atom. exact E11.
  + rewrite (g_reg W E fEt ms3 18%bv (SOff 10 0) HS3 ltac:(vm_compute; reflexivity)).
    rewrite den_atom, (HE 10%nat 10%bv eq_refl). exact G10.
  + rewrite (g_reg W E fEt ms3 10%bv (SOff 52 0) HS3 ltac:(vm_compute; reflexivity)). rewrite den_atom. exact H52.
  + rewrite (g_reg W E fEt ms3 19%bv (SOff 11 0) HS3 ltac:(vm_compute; reflexivity)). rewrite den_atom. exact E11.
  + intros r Hr. apply (reg_kept E fEt ms3 r (Z.to_nat r) HE HS3).
    * cbn [In] in Hr. repeat destruct Hr as [<-|Hr]; try destruct Hr; vm_compute; reflexivity.
    * cbn [In] in Hr. apply Z2Nat.id. lia.
    * cbn [In] in Hr. lia.
  + apply (slots_of E fEt ms3 HE HS3 ltac:(vm_compute; reflexivity) E2).
    intros j Hj. do 9 (destruct j as [|j]; [vm_compute; repeat (first [left; reflexivity | right]) |]). lia.
  + exact HBY3.
- (* size >= res + 1: WRITE_RANGE (str, res + 1) *)
  pose proof (st_ok_add_cond tfibsegs E fD _ BC_GEU (SOff 11 0) (SAluw ALU_ADD (SOff 52 0) (SLit 1)) HS2
    (br_room' E (Z.of_nat (length T)) n E11 H52 ltac:(lia) ltac:(lia) ltac:(lia))) as HS2'.
  eapply SRr_bind;
    [exact (g_phase_to W E WRC_ENTRY (AC fD BC_GEU (SOff 11 0) (SAluw ALU_ADD (SOff 52 0) (SLit 1))) fE _ ms2 _ HS2' r_fE)|].
  intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3).
  change (st_ok tfibsegs E fE (restrict (w_H W) ms3)) in HS3.
  pose proof (win_inK E (AC fD BC_GEU (SOff 11 0) (SAluw ALU_ADD (SOff 52 0) (SLit 1))) _
    ltac:(vm_compute; reflexivity) E2) as WE.
  pose proof (v_run _ _ _ mat3 E _ HI2 WE HF3
    (fun a Ha => win_presK W E fE ms3 _ a HS3 ltac:(vm_compute; reflexivity) E2 ltac:(zl) B2 Ha)) as HI3.
  pose proof (bytes_run E _ _ _ HBY2 WE HF3) as HBY3.
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS3 eq_refl) as Hshape.
  rewrite Hshape. replace (Z_to_bv 64 (ss_pc fE)) with (w64 WRC_ENTRY) by (vm_compute; reflexivity).
  apply (vsni_wrc (ms_regs ms3) (ms_mem ms3) _ Hfull HI3).
  + rewrite (g_reg W E fE ms3 2%bv (SOff 2 (-2160)) HS3 ltac:(vm_compute; reflexivity)). cbn [sv_denot]. rewrite E2.
    unfold w64. f_equal; lia.
  + rewrite (g_reg W E fE ms3 9%bv _ HS3 ltac:(vm_compute; reflexivity)). apply (U_x9' E _ H52). lia.
  + rewrite (g_reg W E fE ms3 18%bv (SOff 10 0) HS3 ltac:(vm_compute; reflexivity)).
    rewrite den_atom, (HE 10%nat 10%bv eq_refl). exact G10.
  + rewrite (g_reg W E fE ms3 10%bv (SOff 52 0) HS3 ltac:(vm_compute; reflexivity)). rewrite den_atom. exact H52.
  + rewrite (g_reg W E fE ms3 19%bv (SOff 11 0) HS3 ltac:(vm_compute; reflexivity)). rewrite den_atom. exact E11.
  + intros r Hr. apply (reg_kept E fE ms3 r (Z.to_nat r) HE HS3).
    * cbn [In] in Hr. repeat destruct Hr as [<-|Hr]; try destruct Hr; vm_compute; reflexivity.
    * cbn [In] in Hr. apply Z2Nat.id. lia.
    * cbn [In] in Hr. lia.
  + apply (slots_of E fE ms3 HE HS3 ltac:(vm_compute; reflexivity) E2).
    intros j Hj. do 9 (destruct j as [|j]; [vm_compute; repeat (first [left; reflexivity | right]) |]). lia.
  + exact HBY3.
Qed.
End a.

(* ==== the interceptor from its entry ==== *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
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
Variable FF : fmt_fam.
Hypothesis STAB : ff_stable64 FF.
Hypothesis MONO : ff_mono FF.
Variables (gc gv img_lo img_hi : Z) (cr : list (Z * Z)).
(* the windows: the walk's K at its entry sp, musl vsnprintf's Kvs and printf_common's Kpc at entry - 0x870 *)
Variables (K Kvs Kpc : Z).
Hypothesis HKvs : 0x870 + Kvs <= K.
Hypothesis HKpc : 0x870 + Kpc <= K.
Hypothesis HKE : 0x870 + ESTACK <= K.
Hypothesis HEvs : ESTACK <= Kvs.
Hypothesis APCOMMON : sh_apcommon_realizes_xz tfibsegs B ARx FF Kpc cr A_PCOM.
Hypothesis AVSN : sh_avsnprintf_realizes_xa tfibsegs B ARx FF Kvs gc gv img_lo img_hi cr A_VSN.

Section w.
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (d n f ap : Z) (ws T : list Z) (cval : Z).
Hypothesis HPRE : sn_pre tfibsegs B ARx FF K gc gv cr ly S Hp W mem md (spZ regs) d n f ap ws T cval.
Hypothesis HDOG : zdisjoint (d, sn_len (n - 1) T) (img_lo, img_hi - img_lo).
(* frm0_entry: the FP state is untouched up to REAL (vsnprintf), whose contract asks it *)
Hypothesis HFRM : Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0.
(* the GXA-route premises: the argument slots at or above the entry sp, the destination below the window or above
   the slots, the slots below 2^47 *)
Hypothesis HORD : spZ regs <= ap.
Hypothesis HDST : d + sn_len (n - 1) T <= spZ regs - K \/ ap + 8 * Z.of_nat (length ws) <= d.
Hypothesis H47 : ap + 8 * Z.of_nat (length ws) <= 2 ^ 47.
Hypothesis HD8 : amem_range d (sn_len (n - 1) T + 8).
Hypothesis HRET : YK0s.ret_ok (getr regs 1).
Hypothesis HGP : getr regs 3 = w64 (as_gp B).
Hypothesis HTP : getr regs 4 = w64 (as_tp B).
Hypothesis G10 : getr regs 10 = w64 d.
Hypothesis G11 : getr regs 11 = w64 n.
Hypothesis G12 : getr regs 12 = w64 f.
Hypothesis G13 : getr regs 13 = w64 ap.

Definition POST : world tfibsegs -> config -> Prop := sn_post tfibsegs ARx ly S Hp W regs mem md K d n T.
(* before REAL (vsnprintf): only the window changes *)
Definition INV0 (m : word -> option byte) (md' : Model) : Prop :=
  sw_frame tfibsegs ARx ly S Hp W mem md (spZ regs - K) (spZ regs) (fun _ => False) m md'.

Lemma basb : kHighMemBeg <= spZ regs - K /\ spZ regs <= 2 ^ 47 /\ 2 ^ 44 <= spZ regs - K /\
  spZ regs mod 16 = 0 /\ ly_stk_lo ly <= spZ regs - K /\ spZ regs <= ly_stk_hi ly /\
  zdisjoint (spZ regs - K, K) (d, sn_len (n - 1) T) /\ 1 <= sn_len (n - 1) T /\ 0 < d /\
  d + sn_len (n - 1) T <= 2 ^ 63.
Proof.
pose proof HPRE as (HA & Hlo & Hhi & H16 & HK & Hpz & Hcv & Hcb & Hcd & Hgc & Hgv & G1 & G2 & G3 & G4 & Hgcd & Hgvd &
  Hws & A1 & A2 & Ad & HFF & Hn & HT & Hd0 & Hdw & Hpw & Hdst & Ham & Hra & Hhull).
pose proof (stk_bounds_x ly S Hp W mem md HA) as [K1 K2].
pose proof (sn_len_pos (n - 1) T) as Hw1.
unfold sn_rs in Hpw. apply pairwise_snp in Hpw.
split; [zl|]. split; [zl|]. split; [zl|]. split; [exact H16|]. split; [zl|]. split; [exact Hhi|].
split; [exact Hpw|]. split; [exact Hw1|]. split; [exact Hd0 | exact Hdw].
Qed.
Lemma aft_of : aft_pre B ARx ly S Hp W regs mem md d n T K.
Proof.
pose proof HPRE as (HA & Hlo & Hhi & H16 & HK & Hpz & Hcv & Hcb & Hcd & Hgc & Hgv & G1 & G2 & G3 & G4 & Hgcd & Hgvd &
  Hws & A1 & A2 & Ad & HFF & Hn & HT & Hd0 & Hdw & Hpw & Hdst & Ham & Hra & Hhull).
unfold sn_rs in Hpw. apply pairwise_snp in Hpw.
unfold aft_pre.
split; [exact HA|]. split; [exact Hlo|]. split; [exact Hhi|]. split; [exact H16|]. split; [exact HRET|].
split; [exact HGP|]. split; [exact HTP|]. split; [exact G10|]. split; [exact G11|]. split; [exact Hn|].
split; [exact HT|]. split; [exact Hd0|]. split; [exact Hdw|]. split; [exact Hpw|]. split; [exact Ham|].
split; [exact Hra | exact Hhull].
Qed.
(* the bundle at a memory the walk changed only inside the window *)
Lemma pre_at : forall m md', INV0 m md' -> sn_pre tfibsegs B ARx FF K gc gv cr ly S Hp W m md' (spZ regs) d n f ap ws T cval.
Proof.
intros m md' (HA' & _ & Hpz' & Hfr' & Hpr' & _).
pose proof basb as (_ & _ & _ & _ & _ & _ & Hdj & Hw1 & Hd0 & Hdw).
unfold zdisjoint in Hdj. cbn [fst snd] in Hdj.
apply (sn_pre_keep tfibsegs B ARx stk_bounds_x FF K gc gv cr ly S Hp W mem md m md' (spZ regs) d n f ap ws T cval STAB HPRE HA' Hpz').
- intros a Ha H1 _. apply Hfr'; [exact Ha | exact H1 | intros []].
- left. apply Hfr'; [lia | lia | intros []].
- exact Hpr'.
Qed.

(* ---- REAL (vsnprintf): musl vsnprintf's contract at entry - 0x870 with window Kvs, its FP state re-pinned ---- *)
Lemma vsni_call : forall E ms md1,
  st_ok tfibsegs E fB (restrict (w_H W) ms) -> EOK regs E -> INV0 (ms_mem ms) md1 ->
  SRr tfibsegs W (mkCfg ms md1) POST.
Proof using All.
intros E ms md1 HS HE HI.
pose proof basb as (B1 & B2 & B3 & B4 & L1 & L2 & Hdj & Hw1 & Hd0 & Hdw).
pose proof (EOK_spK regs E HE) as E2.
assert (HS0 : st_ok tfibsegs E fB0 (restrict (w_H W) ms)).
{ change fB0 with (set_mem fB [hd stkF (ss_mem fB)]).
  apply (st_ok_head E fB _ _ (tl (ss_mem fB)) HS). vm_compute. reflexivity. }
assert (RG : forall (r : bv 5) v, sr_get (ss_regs fB0) r = v -> getr (ms_regs ms) r = sv_denot E v)
  by (intros r v Hv; exact (g_reg W E fB0 ms r v HS0 Hv)).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS0 ltac:(vm_compute; reflexivity)) as Hshape.
assert (SPc : spZ (ms_regs ms) = spZ regs - 0x870).
{ unfold spZ at 1. rewrite (RG 2%bv (SOff 2 (-2160))) by (vm_compute; reflexivity). cbn [sv_denot]. rewrite E2.
  rewrite unsigned_lit_small by zl. lia. }
assert (RA : raZ (ms_regs ms) = RA_VSN).
{ unfold raZ. rewrite (RG 1%bv (SLit RA_VSN)) by (vm_compute; reflexivity). cbn [sv_denot].
  apply unsigned_lit_small. unfold RA_VSN. lia. }
pose proof (pre_at _ _ HI) as P1.
pose proof P1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hws & A1 & A2 & Ad & _).
assert (P2 : sn_pre tfibsegs B ARx FF Kvs gc gv cr ly S Hp W (ms_mem ms) md1 (spZ (ms_regs ms)) d n f ap ws T cval).
{ rewrite SPc.
  apply (sn_pre_shrink tfibsegs B ARx FF K Kvs gc gv cr ly S Hp W (ms_mem ms) md1 (spZ regs) (spZ regs - 0x870) d n f ap ap
    ws T cval MONO P1).
  - zl.
  - lia.
  - zl.
  - replace (spZ regs - 0x870) with (spZ regs + (-135) * 16) by lia. rewrite Z_mod_plus_full. exact B4.
  - exact Hws.
  - exact A1.
  - exact A2.
  - unfold sn_rs in Ad |- *. apply Forall_snp in Ad as [X1 X2]. apply Forall_snp. split; [|exact X2].
    apply (zdisjoint_sub _ (spZ regs - K, K)); [exact X1 | cbn [fst snd]; zl | cbn [fst snd]; zl]. }
assert (HC : SRr tfibsegs W (cfg_at tfibsegs A_VSN (ms_regs ms) (ms_mem ms) md1)
  (sn_post tfibsegs ARx ly S Hp W (ms_regs ms) (ms_mem ms) md1 Kvs d n T)).
{ apply (sn_applyA tfibsegs B ARx FF Kvs gc gv img_lo img_hi cr A_VSN ly S Hp W (ms_regs ms) (ms_mem ms) md1 d n f ap ws T cval
    (or_introl AVSN) P2 HDOG HFRM).
  - rewrite SPc. lia.
  - rewrite SPc. destruct HDST as [X|X]; [left; zl | right; exact X].
  - exact H47.
  - exact HD8.
  - rewrite (RG 1%bv (SLit RA_VSN)) by (vm_compute; reflexivity). apply ret_ok_lit; [unfold RA_VSN; lia|].
    reflexivity.
  - rewrite (RG 3%bv (SOff 3 0)) by (vm_compute; reflexivity). rewrite den_atom, (HE 3%nat 3%bv eq_refl). exact HGP.
  - rewrite (RG 4%bv (SOff 4 0)) by (vm_compute; reflexivity). rewrite den_atom, (HE 4%nat 4%bv eq_refl). exact HTP.
  - rewrite (RG 10%bv (SOff 10 0)) by (vm_compute; reflexivity). rewrite den_atom, (HE 10%nat 10%bv eq_refl).
    exact G10.
  - rewrite (RG 11%bv (SOff 11 0)) by (vm_compute; reflexivity). rewrite den_atom, (HE 11%nat 11%bv eq_refl).
    exact G11.
  - rewrite (RG 12%bv (SOff 12 0)) by (vm_compute; reflexivity). rewrite den_atom, (HE 12%nat 12%bv eq_refl).
    exact G12.
  - rewrite (RG 13%bv (SOff 13 0)) by (vm_compute; reflexivity). rewrite den_atom, (HE 13%nat 13%bv eq_refl).
    exact G13. }
rewrite Hshape.
change (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc fB0)) (ms_mem ms) (seg_rom tfibsegs)) md1)
  with (cfg_at tfibsegs A_VSN (ms_regs ms) (ms_mem ms) md1).
unfold sn_post in HC.
apply (srr_fx_continue tfibsegs W _ (raZ (ms_regs ms))
  (fun (fx' : YK11.FPState) regs' mem' md' => ARx ly S Hp W mem' md' /\ aregs_preserved (ms_regs ms) regs' /\
     same_but_materialized md1 md' /\ getr regs' 10 = w64 (Z.of_nat (length T)) /\
     (forall i, 0 <= i < sn_len (n - 1) T ->
        aview tfibsegs (w_H W) mem' (d + i) = Some (nth (Z.to_nat i) (sn_bytes (n - 1) T) 0)) /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (n - 1) T) ->
        ~ (spZ (ms_regs ms) - Kvs <= a < spZ (ms_regs ms)) ->
        aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) (ms_mem ms) a) /\
     (forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) mem' a) /\
     (YAkMemnorm.memnorm tfibsegs (ms_mem ms) -> YAkMemnorm.memnorm tfibsegs mem')) POST HC).
intros fx' regs' mem' md' FP1 FP2 (HA' & Hap & Hsb & R10' & HBY & Hfr & Hpr & Hkp).
rewrite RA.
pose proof HI as (_ & _ & Hb & _).
set (E' := havoc E 48 (map (getr regs') CLOB)).
assert (HS2 : st_ok (fx:=fx') tfibsegs E' (kafter 48 fB0 RA_VSN (-0x870) 0 0)
  (restrict (w_H W) (mkst (fx:=fx') regs' (Z_to_bv 64 RA_VSN) mem' (seg_rom tfibsegs)))).
{ apply (kcall_fx fx fx' W E fB0 ms (spZ regs) FRK (hd stkF (ss_mem fB0)) [] 48 RA_VSN (-0x870) 0 0 0x10
    (fun a => (spZ regs - 0x870 - Kvs <= a < spZ regs - FRK) \/ XWd d n T a) regs' mem' HS0).
  - vm_compute. reflexivity.
  - exact E2.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. intros Hc. discriminate.
  - vm_compute. intros Hc. discriminate.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - zl.
  - zl.
  - zl.
  - zl.
  - zl.
  - intros a Ha Hs. unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. destruct Ha as [Ha|Ha]; unfold XWd in Ha; zl.
  - intros r a Hr. destruct Hr.
  - intros r a Hr. destruct Hr.
  - intros a Ha. apply Hb. zl.
  - exact Hap.
  - intros a Ha H1 H2. cbv beta in H2. apply Hfr; [exact Ha | intros X; apply H2; right; exact X |].
    rewrite SPc. intros X. unfold XWd in H2. zl.
  - exact Hpr. }
assert (HE' : EOK regs E') by (apply EOK_havocK; [exact HE | lia]).
assert (HI' : INV ARx ly S Hp W regs mem md d n T K mem' md').
{ apply (sw_step tfibsegs ARx ly S Hp W mem md _ _ (XWd d n T) (ms_mem ms) md1 mem' md').
  - apply (sw_mono tfibsegs ARx ly S Hp W mem md _ _ (fun _ => False) (XWd d n T) (ms_mem ms) md1 HI). intros a [].
  - exact HA'.
  - exact Hsb.
  - intros a Ha. apply Hpr. apply Hb. exact Ha.
  - intros a Ha H1 H2. apply Hfr; [exact Ha | exact H2 |]. rewrite SPc. intros X. apply H1. zl.
  - exact Hpr.
  - exact Hkp. }
unfold cfg_at. change (w64 RA_VSN) with (Z_to_bv 64 RA_VSN).
eapply SRr_mono.
{ exact (vsni_after (fx:=fx') B ARx alx_frame alx_stack alx_const_cells stk_bounds_x TB ly S Hp W regs mem md d n T K HKE aft_of E'
    (mkst (fx:=fx') regs' (Z_to_bv 64 RA_VSN) mem' (seg_rom tfibsegs)) md' HS2 HE' R10' HI' HBY). }
intros W' c' _ (-> & regs'' & mem'' & md'' & -> & HA'' & Hap'' & Hsb'' & R10'' & HBY'' & Hfr'' & Hpr'' & Hkp'').
unfold POST, sn_post. split; [reflexivity|].
exists fx', regs'', mem'', md''. split; [reflexivity|]. split; [exact FP1|]. split; [exact FP2|].
split; [exact HA''|]. split; [exact Hap''|]. split; [exact Hsb''|]. split; [exact R10''|].
split; [exact HBY''|]. split; [exact Hfr''|]. split; [exact Hpr'' | exact Hkp''].
Qed.

(* ---- printf_common, then the run to REAL (vsnprintf) ---- *)
Lemma vsni_pcom : forall E ms md1,
  st_ok tfibsegs E fA (restrict (w_H W) ms) -> EOK regs E -> INV0 (ms_mem ms) md1 ->
  SRr tfibsegs W (mkCfg ms md1) POST.
Proof using All.
intros E ms md1 HS HE HI.
pose proof basb as (B1 & B2 & B3 & B4 & L1 & L2 & Hdj & Hw1 & Hd0 & Hdw).
pose proof (EOK_spK regs E HE) as E2.
pose proof HI as (HA & _ & Hb & _ & Hpz).
assert (RG : forall (r : bv 5) v, sr_get (ss_regs fA) r = v -> getr (ms_regs ms) r = sv_denot E v)
  by (intros r v Hv; exact (g_reg W E fA ms r v HS Hv)).
assert (SP : spZ (ms_regs ms) = spZ regs - 0x870).
{ unfold spZ at 1. rewrite (RG 2%bv (SOff 2 (-2160))) by (vm_compute; reflexivity). cbn [sv_denot]. rewrite E2.
  rewrite unsigned_lit_small by zl. lia. }
assert (RA : raZ (ms_regs ms) = RA_PCOM_VSNI).
{ unfold raZ. rewrite (RG 1%bv (SLit RA_PCOM_VSNI)) by (vm_compute; reflexivity). cbn [sv_denot].
  apply unsigned_lit_small. unfold RA_PCOM_VSNI. lia. }
assert (Hrest : tl (ss_mem fA) = map ro_region vsni_rodata) by (vm_compute; reflexivity).
pose proof (pre_at _ _ HI) as P1.
pose proof P1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hap0 & _).
destruct (sn_pcom tfibsegs B ARx FF K Kpc gc gv cr ly S Hp W (ms_mem ms) md1 (spZ regs) (spZ (ms_regs ms)) d n f ap ws T
  cval MONO P1 ltac:(rewrite SP; zl) ltac:(rewrite SP; zl)) as (Pcv & Pcb & Pcd & Pws & Pap & Pdj & PFF).
eapply SRr_bind.
{ apply (kcall W E fA ms md1 (spZ regs) FRK (hd stkF (ss_mem fA)) (tl (ss_mem fA)) 32 RA_PCOM_VSNI (-0x870) 0 0
    0x10 (fun a => spZ regs - 0x870 - Kpc <= a < spZ regs - FRK)
    (fun _ mem2 md2 => ARx ly S Hp W mem2 md2 /\
       (YAkMemnorm.memnorm tfibsegs (ms_mem ms) -> YAkMemnorm.memnorm tfibsegs mem2)) HS).
  - vm_compute. reflexivity.
  - exact E2.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. intros Hc. discriminate.
  - vm_compute. intros Hc. discriminate.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - zl.
  - zl.
  - zl.
  - zl.
  - zl.
  - intros a Ha Hs. zl.
  - intros r a Hr Ha. rewrite Hrest in Hr. destruct (ro_low r Hr) as (_ & Hbs & Hlo' & Hhi' & _).
    rewrite Hbs in Ha. cbn [base_val] in Ha. split; [lia|]. split; zl.
  - intros r a Hr Ha. rewrite Hrest in Hr. destruct (ro_low r Hr) as (_ & _ & _ & _ & Hw). lia.
  - intros a Ha. apply Hb. zl.
  - eapply SRr_mono.
    + apply (APCOMMON ly S Hp W (ms_regs ms) (ms_mem ms) md1 f ap ws T).
      * apply (g_ecall_pre_x B ARx ly S Hp W (ms_regs ms) (ms_mem ms) md1 HA).
        -- rewrite (RG 1%bv (SLit RA_PCOM_VSNI)) by (vm_compute; reflexivity).
           apply ret_ok_lit; [unfold RA_PCOM_VSNI; lia|]. reflexivity.
        -- rewrite SP. replace (spZ regs - 0x870) with (spZ regs + (-135) * 16) by lia. rewrite Z_mod_plus_full.
           exact B4.
        -- rewrite SP. zl.
        -- rewrite SP. zl.
        -- intros a Ha. rewrite SP in Ha. apply Hb. zl.
        -- rewrite (RG 3%bv (SOff 3 0)) by (vm_compute; reflexivity). rewrite den_atom, (HE 3%nat 3%bv eq_refl).
           exact HGP.
        -- rewrite (RG 4%bv (SOff 4 0)) by (vm_compute; reflexivity). rewrite den_atom, (HE 4%nat 4%bv eq_refl).
           exact HTP.
      * rewrite SP. zl.
      * intros a Ha. rewrite SP in Ha. apply Hb. zl.
      * rewrite (RG 11%bv (SOff 12 0)) by (vm_compute; reflexivity). rewrite den_atom, (HE 12%nat 12%bv eq_refl).
        exact G12.
      * rewrite (RG 12%bv (SOff 13 0)) by (vm_compute; reflexivity). rewrite den_atom, (HE 13%nat 13%bv eq_refl).
        exact G13.
      * exact Pcv.
      * exact Pcb.
      * exact Pcd.
      * exact Pws.
      * exact Pdj.
      * exact Hap0.
      * exact H47.
      * exact PFF.
    + intros W' c' _ (-> & regs' & mem' & md' & -> & HA' & Hap & Hsb' & Hfr' & Hpr' & Hkp').
      split; [reflexivity|]. exists regs', mem', md'. rewrite RA. split; [reflexivity|].
      split; [exact Hap|]. split; [exact Hsb'|]. split.
      * intros a Ha H1 H2. cbv beta in H2. apply Hfr'; [exact Ha|]. rewrite SP. intros X. zl.
      * split; [exact Hpr' | exact (conj HA' Hkp')]. }
intros W1 c1 _ (-> & ms2 & mat2 & -> & HS2 & Hap2 & Hfr2 & Hpr2 & HA2 & Hkp2).
set (E1 := havoc E 32 (map (getr (ms_regs ms2)) CLOB)) in *.
assert (HE1 : EOK regs E1) by (apply EOK_havocK; [exact HE | lia]).
pose proof (EOK_spK regs E1 HE1) as E12.
assert (HI2 : INV0 (ms_mem ms2) (with_vm_backing (m_vm_lazy md1) mat2 md1)).
{ apply (sw_step tfibsegs ARx ly S Hp W mem md _ _ (fun _ => False) (ms_mem ms) md1 (ms_mem ms2) _ HI HA2
    (with_vm_backing_same md1 mat2)).
  - intros a Ha. apply Hpr2. apply Hb. exact Ha.
  - intros a Ha H1 _. apply Hfr2; [exact Ha | intros X; apply H1; zl | cbv beta; intros X; apply H1; zl].
  - exact Hpr2.
  - exact Hkp2. }
eapply SRr_bind; [exact (g_phase_to W E1 A_VSN _ fB _ ms2 _ HS2 r_fB)|].
intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3).
change (st_ok tfibsegs E1 fB (restrict (w_H W) ms3)) in HS3.
apply (vsni_call E1 ms3 _ HS3 HE1).
apply (sw_runR B ARx alx_frame alx_stack stk_bounds_x ly S Hp W mem md _ _ (fun _ => False) (spZ regs - FRK) _ _ (ms_mem ms3) mat3 E1
  (ss_mem (kafter 32 fA RA_PCOM_VSNI (-0x870) 0 0)) L1 L2 ltac:(zl) ltac:(zl) ltac:(zl) HI2).
- apply (win_inK E1 (kafter 32 fA RA_PCOM_VSNI (-0x870) 0 0) _ ltac:(vm_compute; reflexivity) E12).
- exact HF3.
- intros a Ha. exact (win_presK W E1 fB ms3 _ a HS3 ltac:(vm_compute; reflexivity) E12 ltac:(zl) B2 Ha).
Qed.

(* ---- the entry ---- *)
Lemma vsni_main : SRr tfibsegs W (cfg_at tfibsegs A_VSNI regs mem md) POST.
Proof using All.
pose proof basb as (B1 & B2 & B3 & B4 & L1 & L2 & Hdj & Hw1 & Hd0 & Hdw).
pose proof HPRE as (HA & _ & _ & _ & _ & Hpz & _).
set (E0 := Ereg regs []).
assert (HE0 : EOK regs E0) by (intros i r Hi; apply ew_Ereg_nat; exact Hi).
pose proof (EOK_spK regs E0 HE0) as E2.
assert (RO : Forall (region_ok tfibsegs E0 (mrestrict (w_H W) mem)) (map ro_region vsni_rodata))
  by exact (rodata_ok_lx B ARx alx_const_cells TB vsni_rodata ly S Hp W mem md E0 (vsni_rodata_chk ly) HA).
assert (HS0 : st_ok tfibsegs E0 ssF (restrict (w_H W) (mkst regs (Z_to_bv 64 A_VSNI) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssF. apply (entry_st_ok_full tfibsegs); change (Ereg regs []) with E0.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons.
    + unfold stkF. apply (region_ok_stack tfibsegs E0 _ 2 (spZ regs) (- FRK)); [exact E2 | zl | zl |].
      intros a Ha. apply apresent_writable. apply Hpz. zl.
    + exact RO.
  - apply pairwise_disjoint_of_extents. unfold stkF, vsni_rodata, ro_region, extent_of_region.
    cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; zl.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
    change (2 ^ 4) with 16. split; [|exact I]. split; [zl|]. split; [exact B4 | zl]. }
unfold cfg_at. change (w64 A_VSNI) with (Z_to_bv 64 A_VSNI).
eapply SRr_bind; [exact (g_phase_to W E0 A_PCOM ssF fA _ _ md HS0 r_fA)|].
intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1).
change (st_ok tfibsegs E0 fA (restrict (w_H W) ms1)) in HS1.
apply (vsni_pcom E0 ms1 _ HS1 HE0).
apply (sw_runR B ARx alx_frame alx_stack stk_bounds_x ly S Hp W mem md _ _ (fun _ => False) (spZ regs - FRK) mem md (ms_mem ms1) mat1 E0 (ss_mem ssF)
  L1 L2 ltac:(zl) ltac:(zl) ltac:(zl)).
- apply (sw_init tfibsegs ARx ly S Hp W mem md _ _ (fun _ => False) HA). intros a Ha. apply Hpz. exact Ha.
- apply (win_inK E0 ssF _); [vm_compute; reflexivity | exact E2].
- exact HF1.
- intros a Ha. exact (win_presK W E0 fA ms1 _ a HS1 ltac:(vm_compute; reflexivity) E2 ltac:(zl) B2 Ha).
Qed.
End w.

Lemma svsni_walk : sn_walkA tfibsegs B ARx FF K gc gv img_lo img_hi cr A_VSNI.
Proof using All.
intros ly S Hp W regs mem md d n f ap ws T cval Hpre Hdog Hfrm Hord Hdst H47 Hd8 Hret Hgp Htp R10 R11 R12 R13.
exact (vsni_main ly S Hp W regs mem md d n f ap ws T cval Hpre Hdog Hfrm Hord Hdst H47 Hd8 Hret Hgp Htp R10 R11 R12 R13).
Qed.
(* fm.asan's __interceptor_vsnprintf realizes the GXA-route vsnprintf-interceptor contract (FMsnprintfSx), for any
   format family the chain's lemmas accept, from printf_common's and musl vsnprintf's *)
Theorem svsni_ok : sh_avsnprintf_icpt_realizes_xa tfibsegs B ARx FF K gc gv img_lo img_hi cr A_VSNI.
Proof using All.
exact (proj2 (sn_contractA tfibsegs B ARx FF K gc gv img_lo img_hi cr A_VSNI ltac:(zl) svsni_walk)).
Qed.
End b.
