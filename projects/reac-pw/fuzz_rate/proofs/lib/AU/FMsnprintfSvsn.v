(* Modified by Theorem Labs, 2026-10: relocated from omx-clap-core/fuzz_manifest lib/A/FMsnprintfSvsni.v (a working branch 3e35620c52e) to libreac/fuzz_boxreg.asan: module paths changed; 0 address numerals relocated (port_addr_check 5033540ba83b predict mode, symbol + offset); name TfibSyms -> BoxregSyms (2x; boxreg's lib/A/AF0m.v record); re-pointed Requires: FMsnprintfShared, FMsnprintfPf, FMsnprintfSx, FMupoison -> lib.A.Rt; FMH_Base -> lib.A.Rt.SnprintfFmh. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: fm.asan's __interceptor_vsnprintf 0x458a0 over the GXA-route contract
   sh_avsnprintf_icpt_realizesUa (FMsnprintfSx.v), generic in the format family and in the windows (the walk's K,
   musl vsnprintf's Kvs, printf_common's Kpc, under 0x870 + Kvs <= K, 0x870 + Kpc <= K, 0x870 + ESTACK <= K,
   ESTACK <= Kvs): the same function as FMsnprintfGvsni.v's walk, restated in the kit's vocabulary (FMsnprintfSk.v:
   sn_pre, sn_post, sw_frame, sn_pcom, sn_pre_shrink, sn_applyA, kcall_fx, sn_contractA) from printf_common's contract
   (sh_apcommon_realizesUz) and musl vsnprintf's (sh_avsnprintf_realizesUa). FMsnprintfGvsni's runs carry a stack region
   of the chain's band plus 0x9d0 bytes, more than a window K = 8064 holds, so its runs are re-run (MEASURED, same stops) over the
   interceptor's own frame [entry - 0x880, entry) (0x870 of frame plus TryAsanInitFromRtl's 0x10), with the callees'
   windows below entry - 0x870 handed to kcall / kcall_fx as written set; its epilogue run r_epi is reused. Added: the
   size < res + 1 side of the branch at 0x45940 (MEASURED: from 0x45940 not taken the run reaches 0x45944 with
   s1 = s3 = size, s2 = str, a0 = res; run r_fEt), whose check WRITE_RANGE (str, size) is FMsnprintfGwrcT.v's
   vsn_wr_check_srrUT; there sn_len (n - 1) T = n. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Rt/FMsnprintfSvsni.v, with its module paths and module names changed; 740 of its 801 lines of code are new or changed and 870 lines of the source are left out. *)
(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfSvsn.v (cold/port-fm-rtprintf-param 3e35620c52e); relocated to libreac/fuzz_disco.asan by g9/tool (reloc.py target disco-A): module paths changed; 3 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan, symbol + offset; table g9/tool/tables/disco-A/FMsnprintfSvsn.table); YImgTop zify_pre_hook added after the last Require. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/FMsnprintfSvsn.v at 2d2ff01bb6f2 relocated to reac-pw/fuzz_rate's ASan image A: module paths changed; numerals by port_core 1e42da8952ec (ledger provenance/reloc/A-Snp.tsv); the zify hook that unfolds YImgTop.IMG_TOP / IMG_LO dropped (rate's YImgTop states both as notations, which lia reads as they are). *)
(* musl vsnprintf 0x91f0c (fm.asan) over the shared contracts in their GXA-route form: FMsnprintfSx's
   sh_avsnprintf_realizesUa (and its interceptor twin) from __wrap_memset's aintrin_realizesU and the vfprintf
   interceptor's sh_avfprintf_icpt_realizesUx, proved in the kit's vocabulary (FMsnprintfSk.v sn_walkA,
   sn_contractA, vf_applyX) and generic in the format family FF and in the two windows: the walk's own window K and
   the window Kvi of the vfprintf interceptor it calls, with ESTACK <= Kvi and 0x130 + Kvi <= K (its frame is 0x130).
   The walk is the one RtPrintf's FMsnprintfGvsn.v already proves: entry at the caller's sp, memset of the 232-byte
   FILE through __wrap_memset 0x51a60 (ra 0x91f70), the FILE fields, the cookie {d, n - 1}, *d = 0, __wrap_vfprintf
   0x41308 = j 0x457ec (ra 0x91fac) with the FILE at sp - 0x130, the canary check and the epilogue.
   Its symbolic runs are Gvsn's, recomputed twice over: the entry fact on n is the shared contract's 1 <= n < 2 ^ 31
   (= musl's `n > INT_MAX` check, which the engine still decides) where Gvsn's is 1 <= N <= 2 ^ 30, and the stack
   region is the walk's own frame [sp - 0x130, sp) (Gvsn's spans the whole chain's band), so that the walk needs the
   caller's window only where the contract gives it. The callees' cells are carried in the kcall XW instead of in a
   band below sp. New file. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/FMsnprintfSvsn.v at 71994ff034c7, derived by derive_y.py: addresses moved from reac-pw/fuzz_rate's asan image (image A) to its asan-ubsan image (image B), the image module Asan -> AsanUbsan; the Modified-by lines above describe how lib/A/FMsnprintfSvsn.v was made and quote that file's image-A values; the code below carries image B's values; a numeral in a comment that quotes the donor's text (lib/A/FMsnprintfSvsn.v keeps its donor's comment text) is kept as lib/A/FMsnprintfSvsn.v writes it. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s.

From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.

From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YI00 YI16 YK06.

From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import YB1v YE34 YF0l YF0m YF0x YE20 YE2y.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Rt Require Import SnUpoison.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import FMH_Base FMsnprintfImg FMsnprintfK.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Rt Require Import PfFacts SnShared SnSx.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import FMsnprintfSk.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import FMsnprintfGk0 FMsnprintfGt0 FMsnprintfGvsn0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require FMsnprintfG0.
Import ListNotations.
Open Scope Z_scope.

(* ---- the walk's symbolic states and runs. Atom 2 = the entry sp, atoms 0..31 the entry registers, atom 32 the
   canary value; the stack region is the walk's own frame [sp - 0x130, sp). ---- *)
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition sv_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 44) (2 ^ 47) 4); (11%nat, mkAF 1 (2 ^ 31 - 1) 0)] [] [].
Definition sv_stk0 : YP09.region := YP09.mkRegion (Some 2%nat) (-304) 0 (-304) 0 [].
Definition sv_s0 : sstate := mkSS A_VSN sr_atoms [sv_stk0; gv_got; gv_can] None sv_facts.
(* entry to the memset call: frame, canary copy, cookie {d, n - 1} at sp - 72 *)
Definition sv_e1 : sstate := Eval vm_compute in fst (GVTO W_MEMSET sv_s0).
Lemma r_sv1 : GVTO W_MEMSET sv_s0 = (sv_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition sv_e1r : YP09.region := Eval vm_compute in hd sv_stk0 (ss_mem sv_e1).
Lemma sv_e1_mem : ss_mem sv_e1 = [sv_e1r] ++ gv_got :: [gv_can]. Proof. vm_compute. reflexivity. Qed.
(* the GOT slot is read once; it is dropped before the calls *)
Definition sv_e1d : sstate := set_mem sv_e1 ([sv_e1r] ++ [gv_can]).
(* after memset: the caller-saved registers havoc'd from atom 33, the zeros back as a CZero chunk *)
Definition sv_k1 : sstate := kafter 33 sv_e1d RA_MSET (-304) (-304) (-72).
Definition sv_k1r : YP09.region := Eval vm_compute in hd sv_stk0 (ss_mem sv_k1).
Lemma sv_k1_mem : ss_mem sv_k1 = sv_k1r :: [gv_can]. Proof. vm_compute. reflexivity. Qed.
Definition sv_s2 : sstate := set_mem sv_k1 (gv_addc sv_k1r gv_zc :: [gv_can]).
(* the FILE stores, up to `sb zero, 0(s3)` (s3 = d, outside every region) *)
Definition sv_e3 : sstate := Eval vm_compute in fst (GVTO A_VFPI sv_s2).
Lemma r_sv3 : GVTO A_VFPI sv_s2 = (sv_e3, RS_stopped (SR_store (Some 10%nat) 0)). Proof. vm_compute. reflexivity. Qed.
Definition sv_e3r : YP09.region := Eval vm_compute in hd sv_stk0 (ss_mem sv_e3).
Lemma sv_e3_mem : ss_mem sv_e3 = sv_e3r :: [gv_can]. Proof. vm_compute. reflexivity. Qed.
Definition sv_s3 : sstate := set_regs_pc sv_e3 [] (0x94c50 + 4).
(* to __interceptor_vfprintf through __wrap_vfprintf *)
Definition sv_e4 : sstate := Eval vm_compute in fst (GVTO A_VFPI sv_s3).
Lemma r_sv4 : GVTO A_VFPI sv_s3 = (sv_e4, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition sv_e4r : YP09.region := Eval vm_compute in hd sv_stk0 (ss_mem sv_e4).
Lemma sv_e4_mem : ss_mem sv_e4 = sv_e4r :: [gv_can]. Proof. vm_compute. reflexivity. Qed.
(* after the call: havoc from atom 49; the canary copy and the saved registers stay *)
Definition sv_s5 : sstate := kafter 49 sv_e4 RA_VFPI (-304) (-304) (-56).
Definition sv_e5 : sstate := Eval vm_compute in fst (GVRUN sv_s5).
Lemma r_sv5 : GVRUN sv_s5 = (sv_e5, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.

(* ---- the shape checks: every write window is the frame [-0x130, 0) of the stack region ---- *)
Definition sv_wb (r : YP09.region) : bool :=
  match YP09.r_base r with Some 2%nat => (-304 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 0) | _ => false end
  || (YP09.r_whi r <=? YP09.r_wlo r).
Definition sv_win (rs : smem) : bool := forallb sv_wb rs.
Definition sv_stk (rs : smem) : bool :=
  match rs with
  | r :: _ => obase_eqb (YP09.r_base r) (Some 2%nat) && (YP09.r_wlo r =? -304) && (YP09.r_whi r =? 0)
  | [] => false end.
Lemma c_sw0 : sv_win (ss_mem sv_s0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma c_sk1 : sv_stk (ss_mem sv_e1) = true. Proof. vm_compute. reflexivity. Qed.
Lemma c_sw2 : sv_win (ss_mem sv_s2) = true. Proof. vm_compute. reflexivity. Qed.
Lemma c_sk3 : sv_stk (ss_mem sv_e3) = true. Proof. vm_compute. reflexivity. Qed.
Lemma c_sw3 : sv_win (ss_mem sv_s3) = true. Proof. vm_compute. reflexivity. Qed.
Lemma c_sk4 : sv_stk (ss_mem sv_e4) = true. Proof. vm_compute. reflexivity. Qed.
Lemma c_sw5 : sv_win (ss_mem sv_s5) = true. Proof. vm_compute. reflexivity. Qed.
Lemma c_sk5 : sv_stk (ss_mem sv_e5) = true. Proof. vm_compute. reflexivity. Qed.
(* at the memset call *)
Lemma s1_resv : ss_resv sv_e1d = None. Proof. vm_compute. reflexivity. Qed.
Lemma s1_pc : ss_pc sv_e1d = W_MEMSET. Proof. vm_compute. reflexivity. Qed.
Lemma s1_base : YP09.r_base sv_e1r = Some 2%nat. Proof. vm_compute. reflexivity. Qed.
Lemma s1_lo : YP09.r_lo sv_e1r = -304. Proof. vm_compute. reflexivity. Qed.
Lemma s1_hi : YP09.r_hi sv_e1r = 0. Proof. vm_compute. reflexivity. Qed.
Lemma s1_wlo : YP09.r_wlo sv_e1r = -304. Proof. vm_compute. reflexivity. Qed.
Lemma s1_whi : YP09.r_whi sv_e1r = 0. Proof. vm_compute. reflexivity. Qed.
Lemma s1_ra : sr_get (ss_regs sv_e1d) 1 = SLit RA_MSET. Proof. vm_compute. reflexivity. Qed.
Lemma s1_sp : sr_get (ss_regs sv_e1d) 2 = SOff 2 (-304). Proof. vm_compute. reflexivity. Qed.
Lemma s1_gp : sr_get (ss_regs sv_e1d) 3 = SOff 3 0. Proof. vm_compute. reflexivity. Qed.
Lemma s1_tp : sr_get (ss_regs sv_e1d) 4 = SOff 4 0. Proof. vm_compute. reflexivity. Qed.
Lemma s1_a0 : sr_get (ss_regs sv_e1d) 10 = SOff 2 (-304). Proof. vm_compute. reflexivity. Qed.
Lemma s1_a1 : sr_get (ss_regs sv_e1d) 11 = SLit 0. Proof. vm_compute. reflexivity. Qed.
Lemma s1_a2 : sr_get (ss_regs sv_e1d) 12 = SLit 232. Proof. vm_compute. reflexivity. Qed.
Lemma s1_at : ss_atoms_lt 33 sv_e1d = true. Proof. vm_compute. reflexivity. Qed.
Lemma s1_wf : regions_wf (ss_mem sv_k1) = true. Proof. vm_compute. reflexivity. Qed.
Lemma s1_nc : no_cdata (ss_mem sv_k1) = true. Proof. vm_compute. reflexivity. Qed.
Lemma s1_ma : mem_atoms_lt 33 (ss_mem sv_k1) = true. Proof. vm_compute. reflexivity. Qed.
Lemma s1_ci : forallb (chunk_inside sv_e1r) (YP09.r_chunks sv_e1r) = true. Proof. vm_compute. reflexivity. Qed.
Lemma s1_zc : chunk_inside sv_k1r gv_zc = true. Proof. vm_compute. reflexivity. Qed.
Lemma s1_kb : YP09.r_base sv_k1r = Some 2%nat. Proof. vm_compute. reflexivity. Qed.
(* at the d store *)
Lemma s3_pc : ss_pc sv_e3 = 0x94c50. Proof. vm_compute. reflexivity. Qed.
Lemma s3_resv : ss_resv sv_e3 = None. Proof. vm_compute. reflexivity. Qed.
Lemma s3_s3 : sr_get (ss_regs sv_e3) 19 = SOff 10 0. Proof. vm_compute. reflexivity. Qed.
Lemma s3_base : YP09.r_base sv_e3r = Some 2%nat. Proof. vm_compute. reflexivity. Qed.
Lemma s3_lo : YP09.r_lo sv_e3r = -304. Proof. vm_compute. reflexivity. Qed.
Lemma s3_hi : YP09.r_hi sv_e3r = 0. Proof. vm_compute. reflexivity. Qed.
(* at the __wrap_vfprintf call *)
Lemma s4_resv : ss_resv sv_e4 = None. Proof. vm_compute. reflexivity. Qed.
Lemma s4_pc : ss_pc sv_e4 = A_VFPI. Proof. vm_compute. reflexivity. Qed.
Lemma s4_base : YP09.r_base sv_e4r = Some 2%nat. Proof. vm_compute. reflexivity. Qed.
Lemma s4_lo : YP09.r_lo sv_e4r = -304. Proof. vm_compute. reflexivity. Qed.
Lemma s4_hi : YP09.r_hi sv_e4r = 0. Proof. vm_compute. reflexivity. Qed.
Lemma s4_wlo : YP09.r_wlo sv_e4r = -304. Proof. vm_compute. reflexivity. Qed.
Lemma s4_whi : YP09.r_whi sv_e4r = 0. Proof. vm_compute. reflexivity. Qed.
Lemma s4_ra : sr_get (ss_regs sv_e4) 1 = SLit RA_VFPI. Proof. vm_compute. reflexivity. Qed.
Lemma s4_sp : sr_get (ss_regs sv_e4) 2 = SOff 2 (-304). Proof. vm_compute. reflexivity. Qed.
Lemma s4_gp : sr_get (ss_regs sv_e4) 3 = SOff 3 0. Proof. vm_compute. reflexivity. Qed.
Lemma s4_tp : sr_get (ss_regs sv_e4) 4 = SOff 4 0. Proof. vm_compute. reflexivity. Qed.
Lemma s4_a0 : sr_get (ss_regs sv_e4) 10 = SOff 2 (-304). Proof. vm_compute. reflexivity. Qed.
Lemma s4_a1 : sr_get (ss_regs sv_e4) 11 = SOff 12 0. Proof. vm_compute. reflexivity. Qed.
Lemma s4_a2 : sr_get (ss_regs sv_e4) 12 = SOff 13 0. Proof. vm_compute. reflexivity. Qed.
Lemma s4_at : ss_atoms_lt 49 sv_e4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma s4_wf : regions_wf (ss_mem sv_s5) = true. Proof. vm_compute. reflexivity. Qed.
Lemma s4_nc : no_cdata (ss_mem sv_s5) = true. Proof. vm_compute. reflexivity. Qed.
Lemma s4_ma : mem_atoms_lt 49 (ss_mem sv_s5) = true. Proof. vm_compute. reflexivity. Qed.
Lemma s4_ci : forallb (chunk_inside sv_e4r) (YP09.r_chunks sv_e4r) = true. Proof. vm_compute. reflexivity. Qed.
(* at the ret *)
Lemma s5_resv : ss_resv sv_e5 = None. Proof. vm_compute. reflexivity. Qed.
Lemma s5_ret : clookup tbl_g (ss_pc sv_e5) = Some RET_WORD_r. Proof. vm_compute. reflexivity. Qed.
Lemma s5_saved : forallb (fun i => sv_eqb (sr_get (ss_regs sv_e5) (Z_to_bv 5 i)) (SOff (Z.to_nat i) 0))
  [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma s5_a0 : sr_get (ss_regs sv_e5) 10 = sr_get (ss_regs sv_s5) 10. Proof. vm_compute. reflexivity. Qed.

(* ---- the shape checks are sound ---- *)
Lemma sv_win_sound : forall E rs a, sv_win rs = true -> in_wrange E rs a ->
  base_val E (Some 2%nat) - 304 <= a < base_val E (Some 2%nat).
Proof.
intros E rs a Hok (r & Hin & Ha). unfold sv_win in Hok. rewrite forallb_forall in Hok.
specialize (Hok r Hin). unfold sv_wb in Hok. revert Ha Hok.
destruct (YP09.r_base r) as [[|[|[|nn]]]|]; intros Ha Hok; cbn [orb] in Hok;
  try (apply Z.leb_le in Hok; lia).
apply orb_prop in Hok as [Hb|Hb].
- apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
- apply Z.leb_le in Hb. lia.
Qed.
Lemma sv_stk_sound : forall rs, sv_stk rs = true -> exists r rest, rs = r :: rest /\
  YP09.r_base r = Some 2%nat /\ YP09.r_wlo r = -304 /\ YP09.r_whi r = 0.
Proof.
intros [|r rest] H; [discriminate|]. unfold sv_stk in H.
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
exists r, rest. split; [reflexivity|]. split; [exact (obase_eqb_eq _ _ H1)|].
split; [exact (proj1 (Z.eqb_eq _ _) H2) | exact (proj1 (Z.eqb_eq _ _) H3)].
Qed.
(* the FILE fields read off the chunks at the call (the offsets are from the entry sp) *)
Lemma s4_fields :
  gv_zchk (YP09.r_chunks sv_e4r) (-304) 8 = true /\ gv_zchk (YP09.r_chunks sv_e4r) (-296) 8 = true /\
  gv_zchk (YP09.r_chunks sv_e4r) (-288) 8 = true /\ gv_zchk (YP09.r_chunks sv_e4r) (-280) 8 = true /\
  gv_zchk (YP09.r_chunks sv_e4r) (-272) 8 = true /\ gv_zchk (YP09.r_chunks sv_e4r) (-264) 8 = true /\
  gv_zchk (YP09.r_chunks sv_e4r) (-256) 8 = true /\ gv_zchk (YP09.r_chunks sv_e4r) (-248) 8 = true /\
  gv_zchk (YP09.r_chunks sv_e4r) (-240) 8 = true /\
  gv_vget (YP09.r_chunks sv_e4r) (-232) 8 = Some (SLit A_SNW) /\
  gv_zchk (YP09.r_chunks sv_e4r) (-224) 8 = true /\
  gv_vget (YP09.r_chunks sv_e4r) (-216) 8 = Some (SOff 2 (-49)) /\
  gv_zchk (YP09.r_chunks sv_e4r) (-208) 8 = true /\ gv_zchk (YP09.r_chunks sv_e4r) (-200) 8 = true /\
  gv_zchk (YP09.r_chunks sv_e4r) (-192) 8 = true /\ gv_zchk (YP09.r_chunks sv_e4r) (-184) 8 = true /\
  gv_zchk (YP09.r_chunks sv_e4r) (-176) 8 = true /\ gv_zchk (YP09.r_chunks sv_e4r) (-168) 4 = true /\
  gv_vget (YP09.r_chunks sv_e4r) (-164) 4 = Some (SLit 18446744073709551615) /\
  gv_vget (YP09.r_chunks sv_e4r) (-160) 4 = Some (SLit 18446744073709551615) /\
  gv_zchk (YP09.r_chunks sv_e4r) (-156) 4 = true /\
  gv_vget (YP09.r_chunks sv_e4r) (-152) 8 = Some (SOff 2 (-72)) /\
  gv_zchk (YP09.r_chunks sv_e4r) (-144) 8 = true /\ gv_zchk (YP09.r_chunks sv_e4r) (-136) 8 = true /\
  gv_zchk (YP09.r_chunks sv_e4r) (-128) 8 = true /\ gv_zchk (YP09.r_chunks sv_e4r) (-120) 8 = true /\
  gv_zchk (YP09.r_chunks sv_e4r) (-112) 8 = true /\ gv_zchk (YP09.r_chunks sv_e4r) (-104) 8 = true /\
  gv_zchk (YP09.r_chunks sv_e4r) (-96) 8 = true /\ gv_zchk (YP09.r_chunks sv_e4r) (-88) 8 = true /\
  gv_zchk (YP09.r_chunks sv_e4r) (-80) 8 = true /\
  gv_vget (YP09.r_chunks sv_e4r) (-72) 8 = Some (SOff 10 0) /\
  gv_vget (YP09.r_chunks sv_e4r) (-64) 8 = Some (SOff 11 (-1)).
Proof. vm_compute. repeat split; reflexivity. Qed.
End r.

(* ---- two 4-byte fields read as one 8-byte word, and the range of a word read ---- *)
Lemma sv_cat4 : forall m a lo hi v,
  val_mem tfibsegs m a 4 lo -> val_mem tfibsegs m (a + 4) 4 hi ->
  (forall k, (k < 4)%nat -> YO0f.le_byte v 8 k = YO0f.le_byte lo 4 k) ->
  (forall k, (k < 4)%nat -> YO0f.le_byte v 8 (4 + k) = YO0f.le_byte hi 4 k) ->
  val_mem tfibsegs m a 8 v.
Proof.
intros m a lo hi v H1 H2 K1 K2 k Hk. destruct (Nat.lt_ge_cases k 4) as [Hlt|Hge].
- rewrite (K1 k Hlt). exact (H1 k Hlt).
- replace k with (4 + (k - 4))%nat by lia. rewrite (K2 (k - 4)%nat ltac:(lia)).
  replace (a + Z.of_nat (4 + (k - 4))) with (a + 4 + Z.of_nat (k - 4)) by lia.
  exact (H2 (k - 4)%nat ltac:(lia)).
Qed.
Lemma sv_rdword_range : forall (Hd : word -> bool) m a v,
  rdword (aview tfibsegs Hd m) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros Hd m a v Hw. unfold rdword in Hw.
destruct (aview tfibsegs Hd m a) as [b0|] eqn:E0; [|discriminate].
destruct (aview tfibsegs Hd m (a + 1)) as [b1|] eqn:E1; [|discriminate].
destruct (aview tfibsegs Hd m (a + 2)) as [b2|] eqn:E2; [|discriminate].
destruct (aview tfibsegs Hd m (a + 3)) as [b3|] eqn:E3; [|discriminate].
destruct (aview tfibsegs Hd m (a + 4)) as [b4|] eqn:E4; [|discriminate].
destruct (aview tfibsegs Hd m (a + 5)) as [b5|] eqn:E5; [|discriminate].
destruct (aview tfibsegs Hd m (a + 6)) as [b6|] eqn:E6; [|discriminate].
destruct (aview tfibsegs Hd m (a + 7)) as [b7|] eqn:E7; [|discriminate].
injection Hw as <-.
apply aview_byte_ex in E0 as (c0 & _ & _ & R0). apply aview_byte_ex in E1 as (c1 & _ & _ & R1).
apply aview_byte_ex in E2 as (c2 & _ & _ & R2). apply aview_byte_ex in E3 as (c3 & _ & _ & R3).
apply aview_byte_ex in E4 as (c4 & _ & _ & R4). apply aview_byte_ex in E5 as (c5 & _ & _ & R5).
apply aview_byte_ex in E6 as (c6 & _ & _ & R6). apply aview_byte_ex in E7 as (c7 & _ & _ & R7).
lia.
Qed.

Section v. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Variable FF : fmt_fam.
Hypothesis STAB : ff_stable64 FF.
Hypothesis MONO : ff_mono FF.
Variables (K Kvi gc gv img_lo img_hi : Z) (cr : list (Z * Z)).
(* the walk's frame is 0x130 and the interceptor runs below it; its own window is the caller's *)
Hypothesis HKvi : ESTACK <= Kvi.
Hypothesis HKK : 304 + Kvi <= K.
(* the walk reads the stack-protector cells through the image's GOT slot: the contract's gc / gv are fm's *)
Hypothesis GCV : gc = FM_GOT_canary.
Hypothesis GVV : gv = FM_canary.
Hypothesis AMEMSET : aintrin_realizesU B OSet W_MEMSET.
Hypothesis AVFPI : sh_avfprintf_icpt_realizesUx tfibsegs B FF Kvi gc gv img_lo img_hi cr A_SNW A_VFPI.

Section w.
Variables (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (d n f ap : Z) (ws T : list Z) (cval : Z).
Hypothesis HPRE : sn_pre B FF K gc gv cr ly S U W mem md (spZ regs) d n f ap ws T cval.
Hypothesis HDOG : zdisjoint (d, sn_len (n - 1) T) (img_lo, img_hi - img_lo).
Hypothesis HFRM : Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0.
(* the GXA-route premises of the entry (FMsnprintfSx sh_avsnprintf_realizesUa): the va area above the entry sp,
   the destination off it, both below 2 ^ 47 *)
Hypothesis HORD : spZ regs <= ap.
Hypothesis HSL : (d + sn_len (n - 1) T <= spZ regs - K \/ ap + 8 * Z.of_nat (length ws) <= d).
Hypothesis H47 : ap + 8 * Z.of_nat (length ws) <= 2 ^ 47.
Hypothesis HD8 : amem_range d (sn_len (n - 1) T + 8).
Hypothesis HRA : YK0s.ret_ok (getr regs 1).
Hypothesis HGP : getr regs 3 = w64 (as_gp B).
Hypothesis HTP : getr regs 4 = w64 (as_tp B).
Hypothesis G10 : getr regs 10 = w64 d.
Hypothesis G11 : getr regs 11 = w64 n.
Hypothesis G12 : getr regs 12 = w64 f.
Hypothesis G13 : getr regs 13 = w64 ap.

#[local] Notation sp := (spZ regs).
#[local] Notation w := (sn_len (n - 1) T).
(* the bytes outside the walk's stack window that the walk and its callee write: the destination *)
Definition svXW (a : Z) : Prop := d <= a < d + sn_len (n - 1) T.

Ltac svp := pose proof HPRE as
  (HA & HKlo & HKhi & H16 & HKE & HPp & Hcv & Hcb & Hcd & Hgcw & Hgvw & GB1 & GB2 & GB3 & GB4 & Hgcd & Hgvd & Hwsa &
   AP1 & AP2 & APd & HFFm & Hn1 & HTl & Hd0 & Hdw & Hpw & Hdst & Ham & Hrad & Hhull);
  unfold sn_rs in *.
Lemma sv_ARU : ARU tfibsegs B ly S U W mem md.
Proof. svp. exact HA. Qed.

(* ---- the environment: atom 2 = the entry sp, atom 32 = the canary value ---- *)
Definition svE0 : env := Ereg regs [Z_to_bv 64 cval].
Definition svOK (E : env) : Prop := forall i, (i < 33)%nat -> ew E i = ew svE0 i.
Definition svFR (XW : Z -> Prop) (m : word -> option byte) (mdX : Model) : Prop :=
  sw_frame B ly S U W mem md (sp - K) sp XW m mdX.
Definition svQ : world tfibsegs -> config -> Prop := sn_post B ly S U W regs mem md K d n T.

Lemma sv_cval : 0 <= cval < 2 ^ 64.
Proof. svp. exact (sv_rdword_range (w_H W) mem gv cval Hgvw). Qed.
Lemma svOK_E0 : svOK svE0.
Proof. intros i _. reflexivity. Qed.
Lemma svOK_havoc : forall E k xs, svOK E -> (33 <= k)%nat -> svOK (havoc E k xs).
Proof. intros E k xs HE Hk i Hi. rewrite ew_havoc_old by lia. exact (HE i Hi). Qed.
Lemma svOK_reg : forall E i (r : bv 5), svOK E -> Z.of_nat i = bv_unsigned r -> ew E i = getr regs r.
Proof.
intros E i r HE Hi. pose proof (u5_range r) as Hr.
rewrite (HE i) by lia. unfold svE0. exact (ew_Ereg_nat regs _ i r Hi).
Qed.
Lemma svOK_sp : forall E, svOK E -> bv_unsigned (ew E 2) = sp.
Proof. intros E HE. rewrite (svOK_reg E 2 2%bv HE eq_refl). reflexivity. Qed.
Lemma svOK_can : forall E, svOK E -> ew E 32 = Z_to_bv 64 cval.
Proof. intros E HE. rewrite (HE 32%nat) by lia. unfold svE0. exact (ew_Ereg_extra regs _ 0). Qed.
Lemma sv_den_reg : forall E i (r : bv 5), svOK E -> Z.of_nat i = bv_unsigned r -> sv_denot E (SOff i 0) = getr regs r.
Proof. intros E i r HE Hi. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (svOK_reg E i r HE Hi). Qed.
Lemma sv_den_sp : forall E z, svOK E -> sv_denot E (SOff 2 z) = Z_to_bv 64 (sp + z).
Proof. intros E z HE. cbn [sv_denot]. rewrite (svOK_sp E HE). reflexivity. Qed.

(* ---- numbers of the walk's windows ---- *)
Lemma sv_pres : forall a, sp - K <= a < sp -> apresent (w_H W) mem a.
Proof. svp. exact HPp. Qed.
Lemma sv_geom : 2 ^ 44 <= sp /\ sp <= 2 ^ 47 /\ sp mod 16 = 0 /\ ly_stk_lo ly + K <= sp /\ sp <= ly_stk_hi ly /\
  0 < d /\ d + w <= 2 ^ 63 /\ 1 <= w /\ 1 <= n < 2 ^ 31 /\ (d + w <= sp - K \/ sp <= d) /\
  17594333495296 <= sp - K /\ 4400 <= K.
Proof.
svp. assert (HES : ESTACK = 4096) by reflexivity.
pose proof (stk_kHighMemBeg B ly S _ (ARU_ARm tfibsegs B ly S U W mem md sv_ARU)) as [KB1 KB2].
pose proof (sn_len_pos (n - 1) T) as HW1.
apply pairwise_snp in Hpw. unfold zdisjoint in Hpw. cbn [fst snd] in Hpw.
unfold kHighMemBeg, kHighMemEnd in KB1, KB2.
repeat split; try assumption; try lia.
Qed.
Ltac svg := pose proof sv_geom as (GE1 & GE2 & GE3 & GE4 & GE5 & GE6 & GE7 & GE8 & GE9 & GE10 & GE11 & GE12);
  assert (HES : ESTACK = 4096) by reflexivity.

(* ---- the frame: the kit's sw_frame over the contract's window [sp - K, sp) ---- *)
Lemma sv_frame_init : svFR (fun a => a = d) mem md.
Proof. svg. apply (sw_init B ly S U W mem md (sp - K) sp (fun a => a = d)); [exact sv_ARU | exact sv_pres]. Qed.
(* the shadow of a range inside [sp - 4400, sp): the stack's shadow is zero (ARm's zero_shadow_ranges) *)
Lemma sv_shadow : forall m mdX x nn, ARU tfibsegs B ly S U W m mdX ->
  sp - 4400 + 64 <= x -> x + nn + 64 <= sp -> x mod 8 = 0 -> nn mod 8 = 0 -> 0 <= nn ->
  range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF x nn /\
  (0 < nn -> shadow_hull_vis (aview tfibsegs (w_H W) m) x nn).
Proof.
intros m mdX x nn HAm Hx1 Hx2 Hx8 Hn8 Hn0. svg.
assert (Hsp : sp = 16 * (sp / 16)) by (pose proof (Z.div_mod sp 16 ltac:(lia)); lia).
assert (Hb8 : (sp - 4400) / 8 = 2 * (sp / 16) - 550).
{ rewrite Hsp at 1. replace (16 * (sp / 16) - 4400) with ((2 * (sp / 16) - 550) * 8) by lia.
  apply Z.div_mul. lia. }
assert (Hzs : zero_shadow (aview tfibsegs (w_H W) m) SHADOW_OFF (sp - 4400) 4400).
{ apply (FMsnprintfG0.stack_zero_shadow B LAWS ly S U W m mdX); [exact HAm | lia | lia | | reflexivity | lia].
  rewrite Hsp. replace (16 * (sp / 16) - 4400) with ((2 * (sp / 16) - 550) * 8) by lia.
  apply Z.mod_mul. lia. }
assert (Z0 : forall s, SHADOW_OFF + (sp - 4400) / 8 <= s < SHADOW_OFF + (sp - 4400) / 8 + 550 ->
  aview tfibsegs (w_H W) m s = Some 0).
{ intros s Hs. replace s with (shadow_of_addr SHADOW_OFF (sp - 4400) + (s - SHADOW_OFF - (sp - 4400) / 8))
    by (unfold shadow_of_addr; lia). apply Hzs. assert (H48 : 4400 / 8 = 550) by reflexivity. lia. }
assert (Hxq : x = 8 * (x / 8)) by (pose proof (Z.div_mod x 8 ltac:(lia)); lia).
assert (Hnq : nn = 8 * (nn / 8)) by (pose proof (Z.div_mod nn 8 ltac:(lia)); lia).
split.
- apply zero_shadow_range; [exact Hx8 | exact Hn8|]. intros i Hi. apply Z0. unfold shadow_of_addr. lia.
- intros Hn s Hs. unfold shadow_addr in Hs.
  assert (Hv : aview tfibsegs (w_H W) m s = Some 0).
  { apply Z0.
    pose proof (Z.div_mod (SHADOW_OFF + x / 8) 8 ltac:(lia)) as D1.
    pose proof (Z.mod_pos_bound (SHADOW_OFF + x / 8) 8 ltac:(lia)) as D1'.
    pose proof (Z.div_mod (SHADOW_OFF + (x + nn - 1) / 8) 8 ltac:(lia)) as D2.
    pose proof (Z.mod_pos_bound (SHADOW_OFF + (x + nn - 1) / 8) 8 ltac:(lia)) as D2'.
    pose proof (Z.div_mod (x + nn - 1) 8 ltac:(lia)) as D3.
    pose proof (Z.mod_pos_bound (x + nn - 1) 8 ltac:(lia)) as D3'.
    lia. }
  rewrite Hv. discriminate.
Qed.

(* ---- what a walk state at ANY FP state gives: the callee returns at its own fp_regs / fcsr, and the epilogue
   (canary check, restore, ret) runs there ---- *)
Section e1. Context {fy : YK11.FPState}.
Lemma sv_rd : forall E ss ms (r : bv 5), st_ok (fx:=fy) tfibsegs E ss (restrict (w_H W) ms) ->
  getr (ms_regs ms) r = sv_denot E (sr_get (ss_regs ss) r).
Proof. intros E ss ms r HS. exact (st_ok_reg_denot (w_H W) E ss ms r HS). Qed.
Lemma sv_run_out : forall E ss (m m' : word -> option byte) a, svOK E ->
  frame_of E (ss_mem ss) m m' -> sv_win (ss_mem ss) = true -> 0 <= a < 2 ^ 64 -> ~ (sp - 304 <= a < sp) ->
  aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a.
Proof.
intros E ss m m' a HE Hfo Hw Ha Hb. apply aview_same. apply Hfo. rewrite unsigned_lit_small by lia.
intros Hin. pose proof (sv_win_sound E _ a Hw Hin) as X. cbn [base_val] in X. rewrite (svOK_sp E HE) in X. lia.
Qed.
Lemma sv_frame_run : forall XW E ss ss' ms ms1 mdX mat1,
  svFR XW (ms_mem ms) mdX -> svOK E -> st_ok (fx:=fy) tfibsegs E ss' (restrict (w_H W) ms1) ->
  frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) -> sv_win (ss_mem ss) = true -> sv_stk (ss_mem ss') = true ->
  svFR XW (ms_mem ms1) (with_vm_backing (m_vm_lazy mdX) mat1 mdX).
Proof.
intros XW E ss ss' ms ms1 mdX mat1 HF HE HS1 Hfo Hw Hk. svg.
apply (sw_run B LAWS ly S U W mem md (sp - K) sp XW ltac:(lia) ltac:(lia) (ms_mem ms) mdX (ms_mem ms1) mat1 E
  (ss_mem ss) HF).
- intros a Ha. pose proof (sv_win_sound E _ a Hw Ha) as X. cbn [base_val] in X. rewrite (svOK_sp E HE) in X. lia.
- exact Hfo.
- intros a Hb. destruct (sv_stk_sound _ Hk) as (r & rest & Hrs & Hb2 & Hlo2 & Hhi2).
  destruct (Z_lt_le_dec a (sp - 304)) as [L|L].
  + (* below the walk's own frame: the run leaves the byte alone *)
    destruct HF as (_ & _ & Hp & _ & _). destruct (Hp a ltac:(lia)) as [Hh [bb Hbb]].
    split; [exact Hh|]. exists bb. rewrite (Hfo (Z_to_bv 64 a)); [exact Hbb|].
    rewrite unsigned_lit_small by lia. intros Hin.
    pose proof (sv_win_sound E _ a Hw Hin) as X. cbn [base_val] in X. rewrite (svOK_sp E HE) in X. lia.
  + apply (st_ok_window_apresent (w_H W) E ss' ms1 0 r a HS1); [rewrite Hrs; reflexivity | |].
    * rewrite Hb2, Hlo2, Hhi2. cbn [base_val]. rewrite (svOK_sp E HE). lia.
    * unfold TFIB_IMG_END. lia.
Qed.
(* the canary check and the epilogue, at the FP state the callee returned with *)
Lemma sv_epi : forall E ms mdX,
  svOK E -> st_ok (fx:=fy) tfibsegs E sv_s5 (restrict (w_H W) ms) -> svFR svXW (ms_mem ms) mdX ->
  getr (ms_regs ms) 10 = w64 (Z.of_nat (length T)) ->
  (forall i, 0 <= i < w ->
     aview tfibsegs (w_H W) (ms_mem ms) (d + i) = Some (nth (Z.to_nat i) (sn_bytes (n - 1) T) 0)) ->
  (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fy) k = Sem.reg_get (@fp_regs fx) k) ->
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fy)) 5) 7 = 0 ->
  SRr tfibsegs W (mkCfg ms mdX) svQ.
Proof.
intros E ms mdX HE HS HF Ha0 Hout Hfpr Hcsr. svg.
pose proof HRA as Hret. unfold YK0s.ret_ok in Hret.
eapply SRr_bind; [exact (g_phase W E sv_s5 sv_e5 _ ms mdX HS r_sv5)|].
intros W' c' _ (-> & ms6 & mat6 & -> & HS6 & HF6).
pose proof (sv_frame_run svXW E sv_s5 sv_e5 ms ms6 mdX mat6 HF HE HS6 HF6 c_sw5 c_sk5) as HF6'.
apply (g_ret W E sv_e5 ms6 _ svQ HS6 s5_resv s5_ret).
intros mat'.
assert (RK : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r ->
  In (Z.of_nat i) [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr (ms_regs ms6) r = getr regs r).
{ intros r i Hi Hin. pose proof s5_saved as C. rewrite forallb_forall in C. specialize (C _ Hin). cbv beta in C.
  rewrite Nat2Z.id in C. apply sv_eqb_eq in C. rewrite Hi, Z_to_bv_bv_unsigned in C.
  rewrite (sv_rd E sv_e5 ms6 r HS6), C. exact (sv_den_reg E i r HE Hi). }
assert (P1 : getr (ms_regs ms6) 1 = getr regs 1) by exact (RK 1%bv 1%nat eq_refl ltac:(cbn; tauto)).
assert (HFn : svFR svXW (ms_mem ms6) (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy mdX) mat6 mdX)) mat'
  (with_vm_backing (m_vm_lazy mdX) mat6 mdX))).
{ apply (sw_run B LAWS ly S U W mem md (sp - K) sp svXW ltac:(lia) ltac:(lia) (ms_mem ms6) _ (ms_mem ms6) mat' E []
    HF6').
  - intros a (r & [] & _).
  - apply frame_of_refl.
  - destruct HF6' as (_ & _ & Hp & _). exact Hp. }
destruct HFn as (HAn & Hsbn & Hpn & Hfrn & Hpmn).
unfold svQ, sn_post. split; [reflexivity|].
exists fy, (ms_regs ms6), (ms_mem ms6), (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy mdX) mat6 mdX)) mat'
  (with_vm_backing (m_vm_lazy mdX) mat6 mdX)).
split; [unfold cfg_at, raZ, w64; rewrite P1, Z_to_bv_bv_unsigned, Hret; reflexivity|].
split; [exact Hfpr|]. split; [exact Hcsr|]. split; [exact HAn|].
split.
{ intros r Hr. assert (Hr' : 0 <= r < 32) by (unfold acallee_saved in Hr; lia).
  apply (RK (Z_to_bv 5 r) (Z.to_nat r)).
  - rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with (2 ^ 5).
    rewrite Z.mod_small by lia. reflexivity.
  - rewrite Z2Nat.id by lia. unfold acallee_saved in Hr. cbn [In]. lia. }
split; [exact Hsbn|].
split.
{ rewrite (sv_rd E sv_e5 ms6 10 HS6), s5_a0, <- (sv_rd E sv_s5 ms 10 HS). exact Ha0. }
split.
{ intros i Hi. rewrite <- (Hout i Hi).
  apply (sv_run_out E sv_s5 (ms_mem ms) (ms_mem ms6) (d + i) HE HF6 c_sw5); lia. }
split; [|exact Hpmn].
intros a Ha H1 H2. apply Hfrn; [exact Ha | exact H2 | exact H1].
Qed.
End e1.

(* ---- the FILE, its cookie and its buffer as __interceptor_vfprintf finds them at the call ---- *)
Lemma sv_file : forall E m,
  svOK E -> Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) m) sp) (YP09.r_chunks sv_e4r) ->
  words_at (aview tfibsegs (w_H W) m) (sp - 304) (sn_file A_SNW (sp - 49) (sp - 72)) /\
  words_at (aview tfibsegs (w_H W) m) (sp - 72) [d; n - 1].
Proof.
intros E m HE HCS. svg.
assert (RZ : forall off, gv_zchk (YP09.r_chunks sv_e4r) off 8 = true ->
  rdword (aview tfibsegs (w_H W) m) (sp + off) = Some 0).
{ intros off Ho. apply val_mem_rdword; [lia|]. exact (gv_fld_zero E _ sp _ off 8%nat HCS Ho). }
assert (RV : forall off e v, gv_vget (YP09.r_chunks sv_e4r) off 8 = Some e ->
  bv_unsigned (sv_denot E e) mod 2 ^ 64 = v -> 0 <= v < 2 ^ 64 ->
  rdword (aview tfibsegs (w_H W) m) (sp + off) = Some v).
{ intros off e v Ho Hv Hr. apply val_mem_rdword; [exact Hr|].
  exact (gv_fld_val E _ sp _ off 8%nat e v HCS Ho ltac:(lia) Hv). }
assert (R17 : rdword (aview tfibsegs (w_H W) m) (sp + (-168)) = Some 18446744069414584320).
{ apply val_mem_rdword; [lia|]. apply (sv_cat4 _ _ 0 4294967295).
  - exact (gv_fld_zero E _ sp _ (-168) 4%nat HCS ltac:(vm_compute; reflexivity)).
  - replace (sp + -168 + 4) with (sp + -164) by lia.
    exact (gv_fld_val E _ sp _ (-164) 4%nat (SLit 18446744073709551615) 4294967295 HCS
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; reflexivity)).
  - intros k Hk. do 4 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
  - intros k Hk. do 4 (destruct k as [|k]; [vm_compute; reflexivity|]). lia. }
assert (R18 : rdword (aview tfibsegs (w_H W) m) (sp + (-160)) = Some 4294967295).
{ apply val_mem_rdword; [lia|]. apply (sv_cat4 _ _ 4294967295 0).
  - exact (gv_fld_val E _ sp _ (-160) 4%nat (SLit 18446744073709551615) 4294967295 HCS
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; reflexivity)).
  - replace (sp + -160 + 4) with (sp + -156) by lia.
    exact (gv_fld_zero E _ sp _ (-156) 4%nat HCS ltac:(vm_compute; reflexivity)).
  - intros k Hk. do 4 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
  - intros k Hk. do 4 (destruct k as [|k]; [vm_compute; reflexivity|]). lia. }
assert (AD : forall i : nat, sp - 304 + 8 * Z.of_nat i = sp + (-304 + 8 * Z.of_nat i)) by (intros; lia).
assert (AD2 : forall i : nat, sp - 72 + 8 * Z.of_nat i = sp + (-72 + 8 * Z.of_nat i)) by (intros; lia).
split.
- intros i Hi. unfold sn_file in Hi. cbn [length] in Hi. rewrite AD.
  do 29 (destruct i as [|i];
    [ cbn [nth sn_file];
      first [ apply RZ; vm_compute; reflexivity
            | exact R17 | exact R18
            | apply (RV _ (SLit A_SNW) A_SNW);
              [vm_compute; reflexivity | vm_compute; reflexivity | unfold A_SNW; lia]
            | apply (RV _ (SOff 2 (-49)) (sp - 49));
              [ vm_compute; reflexivity
              | rewrite (sv_den_sp E _ HE); rewrite unsigned_lit_small by lia; apply Z.mod_small; lia
              | lia]
            | apply (RV _ (SOff 2 (-72)) (sp - 72));
              [ vm_compute; reflexivity
              | rewrite (sv_den_sp E _ HE); rewrite unsigned_lit_small by lia; apply Z.mod_small; lia
              | lia] ]
    |]).
  lia.
- intros i Hi. cbn [length] in Hi. rewrite AD2.
  do 2 (destruct i as [|i];
    [ cbn [nth];
      first [ apply (RV _ (SOff 10 0) d);
                [ vm_compute; reflexivity
                | rewrite (sv_den_reg E 10 10%bv HE eq_refl), G10; unfold w64;
                  rewrite unsigned_lit_small by lia; apply Z.mod_small; lia
                | lia]
            | apply (RV _ (SOff 11 (-1)) (n - 1));
                [ vm_compute; reflexivity
                | cbn [sv_denot]; rewrite (svOK_reg E 11 11%bv HE eq_refl), G11; unfold w64;
                  rewrite (unsigned_lit_small n) by lia; rewrite unsigned_lit_small by lia;
                  apply Z.mod_small; lia
                | lia] ]
    |]).
  lia.
Qed.

(* ---- the step `sb zero, 0(s3)` at d ---- *)
Lemma sv_store_frame : forall m m' mdX mat,
  svFR (fun a => a = d) m mdX -> writable_at tfibsegs (mrestrict (w_H W) m) d ->
  (forall x : word, m' x = if bv_eqb x (Z_to_bv 64 d) then Some (Z_to_bv 8 0) else m x) ->
  svFR (fun a => a = d) m' (with_vm_backing (m_vm_lazy mdX) mat mdX) /\ aview tfibsegs (w_H W) m' d = Some 0.
Proof.
intros m m' mdX mat HF Hwr Hm. svg. svp.
assert (HDr : 0 <= d < 2 ^ 64) by lia.
pose proof (writable_unhidden W m d HDr Hwr) as Hh.
assert (Hsame : forall x : word, bv_eqb x (Z_to_bv 64 d) = false -> m' x = m x)
  by (intros x Hx; rewrite Hm, Hx; reflexivity).
assert (Hne : forall a, 0 <= a < 2 ^ 64 -> a <> d -> bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 d) = false).
{ intros a Ha Hn. destruct (bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 d)) eqn:Eq; [|reflexivity].
  exfalso. apply bv_eqb_eq in Eq. exact (Hn (gv_bv64_inj a d Ha HDr Eq)). }
assert (HmD : m' (Z_to_bv 64 d) = Some (Z_to_bv 8 0)).
{ rewrite Hm. rewrite (proj2 (bv_eqb_eq (Z_to_bv 64 d) (Z_to_bv 64 d)) eq_refl). reflexivity. }
assert (Hpres : forall a, apresent (w_H W) m a -> apresent (w_H W) m' a).
{ intros a [Hha [b Hb]]. split; [exact Hha|]. rewrite Hm.
  destruct (bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 d)); [eexists; reflexivity | exists b; exact Hb]. }
pose proof (same_but_materialized_frame mdX _ (with_vm_backing_same mdX mat)) as MF.
split.
- apply (sw_step B ly S U W mem md (sp - K) sp (fun a => a = d) m mdX m' _ HF).
  + destruct HF as (HAm & _). apply (ARU_frame tfibsegs B LAWS ly S U W m mdX m' _ HAm).
    * intros a Ha Hown. apply aview_same. apply Hsame. apply Hne; [exact Ha|]. intros ->.
      destruct (Hdst d ltac:(lia)) as (_ & X). exact (X Hown).
    * intros a Hv. destruct (bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 d)) eqn:Eq.
      -- apply bv_eqb_eq in Eq. unfold aview, mbyte, mrestrict. rewrite Eq, Hh, HmD. discriminate.
      -- rewrite (aview_same (w_H W) m m' a (Hsame _ Eq)). exact Hv.
    * apply MF. * apply MF. * apply MF.
    * intros a _ Hha. apply Hsame. destruct (bv_eqb (w64 a) (Z_to_bv 64 d)) eqn:Eq; [|reflexivity].
      apply bv_eqb_eq in Eq. rewrite Eq, Hh in Hha. discriminate.
  + apply with_vm_backing_same.
  + intros a Ha. apply Hpres. destruct HF as (_ & _ & Hp & _). exact (Hp a Ha).
  + intros a Ha _ Hx. apply aview_same. apply Hsame. exact (Hne a Ha Hx).
  + exact Hpres.
- unfold aview, mbyte, mrestrict. rewrite Hh, HmD. reflexivity.
Qed.

(* ---- the call of __wrap_vfprintf = __interceptor_vfprintf (the FILE at sp - 0x130, f, ap) ---- *)
Lemma sv_call2 : forall E ms mdX, svOK E -> st_ok tfibsegs E sv_e4 (restrict (w_H W) ms) ->
  svFR (fun a => a = d) (ms_mem ms) mdX -> aview tfibsegs (w_H W) (ms_mem ms) d = Some 0 ->
  SRr tfibsegs W (mkCfg ms mdX) svQ.
Proof.
intros E ms mdX HE HS HF HD0. svg. svp.
pose proof (svOK_sp E HE) as E2.
pose proof HF as (HA1 & Hsb1 & Hp1 & Hk1 & Hpm1).
assert (R1 : getr (ms_regs ms) 1 = Z_to_bv 64 RA_VFPI) by (rewrite (sv_rd E sv_e4 ms 1 HS), s4_ra; reflexivity).
assert (R2 : getr (ms_regs ms) 2 = w64 (sp - 304)).
{ rewrite (sv_rd E sv_e4 ms 2 HS), s4_sp, (sv_den_sp E _ HE). unfold w64. f_equal; lia. }
assert (R3 : getr (ms_regs ms) 3 = w64 (as_gp B)).
{ rewrite (sv_rd E sv_e4 ms 3 HS), s4_gp, (sv_den_reg E 3 3%bv HE eq_refl). exact HGP. }
assert (R4 : getr (ms_regs ms) 4 = w64 (as_tp B)).
{ rewrite (sv_rd E sv_e4 ms 4 HS), s4_tp, (sv_den_reg E 4 4%bv HE eq_refl). exact HTP. }
assert (R10 : getr (ms_regs ms) 10 = w64 (sp - 304)).
{ rewrite (sv_rd E sv_e4 ms 10 HS), s4_a0, (sv_den_sp E _ HE). unfold w64. f_equal; lia. }
assert (R11 : getr (ms_regs ms) 11 = w64 f).
{ rewrite (sv_rd E sv_e4 ms 11 HS), s4_a1, (sv_den_reg E 12 12%bv HE eq_refl). exact G12. }
assert (R12 : getr (ms_regs ms) 12 = w64 ap).
{ rewrite (sv_rd E sv_e4 ms 12 HS), s4_a2, (sv_den_reg E 13 13%bv HE eq_refl). exact G13. }
assert (HspT : spZ (ms_regs ms) = sp - 304).
{ change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) 2)). rewrite R2. unfold w64.
  apply unsigned_lit_small; lia. }
assert (R1ok : YK0s.ret_ok (getr (ms_regs ms) 1)).
{ rewrite R1. apply ret_ok_lit; [unfold RA_VFPI; lia | unfold RA_VFPI; reflexivity]. }
(* the vsnprintf bundle at the call's memory *)
pose proof (sn_pre_keep B FF K gc gv cr ly S U W mem md (ms_mem ms) mdX sp d n f ap ws T cval STAB HPRE HA1 Hp1
  Hk1 (or_intror HD0) Hpm1) as HP1.
destruct HP1 as (HA1' & _ & _ & _ & _ & _ & Hcv1 & Hcb1 & Hcd1 & Hgc1 & Hgv1 & _ & _ & _ & _ & Hgcd1 & Hgvd1 & Hws1 &
  _ & _ & Ad1 & HFF1 & _ & HTl1 & _ & _ & _ & Hdst1 & Ham1 & Hra1 & Hhull1).
(* the FILE and its cookie *)
assert (HCS : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms)) sp) (YP09.r_chunks sv_e4r)).
{ pose proof (st_ok_mem_ok tfibsegs E sv_e4 _ HS) as (_ & Hrs & _). rewrite sv_e4_mem in Hrs.
  apply Forall_inv in Hrs. destruct Hrs as (_ & _ & _ & Hcs). rewrite s4_base in Hcs. cbn [base_val] in Hcs.
  rewrite E2 in Hcs. exact Hcs. }
destruct (sv_file E (ms_mem ms) HE HCS) as (FILE1 & FILE2).
(* the callee's regions sit inside the walk's window *)
assert (SUB : forall x, Forall (zdisjoint x) (snp_out K sp d w) ->
  Forall (zdisjoint x) (vfp_out Kvi (spZ (ms_regs ms)) d w (sp - 304) (sp - 72))).
{ intros x Hx. apply Forall_snp in Hx as [X1 X2]. rewrite HspT. apply Forall_vfp.
  split; [|split; [exact X2 | split]].
  - apply (zdisjoint_sub x (sp - K, K)); [exact X1 | cbn [fst snd]; lia | cbn [fst snd]; lia].
  - apply (zdisjoint_sub x (sp - K, K)); [exact X1 | cbn [fst snd]; lia | cbn [fst snd]; lia].
  - apply (zdisjoint_sub x (sp - K, K)); [exact X1 | cbn [fst snd]; lia | cbn [fst snd]; lia]. }
assert (HFF2 : FF (aview tfibsegs (w_H W) (ms_mem ms))
  (vfp_out Kvi (spZ (ms_regs ms)) d w (sp - 304) (sp - 72)) f ws T).
{ rewrite HspT. apply (MONO _ (snp_out K sp d w)); [exact HFF1|].
  intros r' Hr'. unfold vfp_out in Hr'. destruct Hr' as [<-|[<-|[<-|[<-|[]]]]].
  - exists (sp - K, K). split; [left; reflexivity | cbn [fst snd]; lia].
  - exists (d, w). split; [right; left; reflexivity | cbn [fst snd]; lia].
  - exists (sp - K, K). split; [left; reflexivity | cbn [fst snd]; lia].
  - exists (sp - K, K). split; [left; reflexivity | cbn [fst snd]; lia]. }
assert (HPW2 : pairwise zdisjoint (vfp_out Kvi (spZ (ms_regs ms)) d w (sp - 304) (sp - 72))).
{ rewrite HspT. apply pairwise_vfp. unfold zdisjoint. cbn [fst snd]. repeat split; lia. }
assert (DF : dest_ok tfibsegs B ly S W (ms_regs ms) (ms_mem ms) (sp - 304) 232).
{ intros a Ha. split; [apply apresent_writable; apply Hp1; lia|].
  split; [apply (ARU_stack tfibsegs B LAWS ly S U W (ms_mem ms) mdX a HA1); lia | rewrite HspT; lia]. }
assert (DC : dest_ok tfibsegs B ly S W (ms_regs ms) (ms_mem ms) (sp - 72) 16).
{ intros a Ha. split; [apply apresent_writable; apply Hp1; lia|].
  split; [apply (ARU_stack tfibsegs B LAWS ly S U W (ms_mem ms) mdX a HA1); lia | rewrite HspT; lia]. }
assert (DS : dest_ok tfibsegs B ly S W (ms_regs ms) (ms_mem ms) d w).
{ intros a Ha. destruct (Hdst1 a Ha) as (X1 & X2). split; [exact X1|]. split; [exact X2 | rewrite HspT; lia]. }
assert (PR2 : forall a, spZ (ms_regs ms) - Kvi <= a < spZ (ms_regs ms) -> apresent (w_H W) (ms_mem ms) a).
{ rewrite HspT. intros a Ha. apply Hp1. lia. }
assert (HEC : ecall_preU tfibsegs B ly S U W (ms_regs ms) (ms_mem ms) mdX).
{ apply (g_ecall_preU B ly S U W (ms_regs ms) (ms_mem ms) mdX HA1 R1ok).
  - rewrite HspT. replace (sp - 304) with (sp + (-19) * 16) by lia. rewrite Z_mod_plus_full. exact GE3.
  - rewrite HspT. lia.
  - rewrite HspT. lia.
  - rewrite HspT. intros a Ha. apply Hp1. lia.
  - exact R3.
  - exact R4. }
pose proof (vf_pre_intro B FF Kvi gc gv cr A_SNW ly S U W (ms_regs ms) (ms_mem ms) mdX
  (sp - 304) f ap (sp - 49) (sp - 72) d (n - 1) ws T cval
  ltac:(lia) HEC ltac:(rewrite HspT; lia) PR2 FILE1 ltac:(lia) FILE2 DF DC ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  Hcv1 Hcb1 ltac:(rewrite Forall_forall in Hcd1 |- *; intros r Hr; exact (SUB r (Hcd1 r Hr)))
  Hgc1 Hgv1 GB1 GB2 GB3 GB4 (SUB _ Hgcd1) (SUB _ Hgvd1) Hws1 AP1 AP2 (SUB _ Ad1) HFF2
  ltac:(lia) HTl1 ltac:(lia) ltac:(lia) HPW2 DS Ham1 Hra1 Hhull1) as HVP.
(* the call *)
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E sv_e4 ms HS s4_resv) as Hshape. rewrite s4_pc in Hshape.
rewrite Hshape.
eapply SRr_bind.
{ exact (vf_applyX B FF Kvi gc gv img_lo img_hi cr A_SNW A_VFPI ly S U W (ms_regs ms) (ms_mem ms) mdX
    (sp - 304) f ap (sp - 49) (sp - 72) d (n - 1) ws T cval AVFPI HVP HDOG HFRM HD0
    ltac:(rewrite HspT; lia) ltac:(lia) ltac:(lia) ltac:(rewrite HspT; lia) H47 HD8 R1ok R3 R4 R10 R11 R12). }
intros W' c' _ (-> & fx' & regs' & mem' & md' & -> & Hfpr & Hcsr & HAR' & Hpres' & Hsbm' & Ha0' & Hbytes' & Hframe' &
  Hpm').
(* the state after the call, re-pinned at the FP state the callee returned with *)
assert (HFRv : forall a, 0 <= a < 2 ^ 64 -> ~ (sp + (-304) - 0 <= a < sp + (-304)) ->
  ~ ((sp - 304 - Kvi <= a < sp - 56) \/ svXW a) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) (ms_mem ms) a).
{ intros a Ha _ HX. apply Hframe'; [exact Ha | intros C; apply HX; right; exact C |].
  intros HE2. rewrite Exists_exists in HE2. destruct HE2 as (r & Hr & Hin).
  cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[]]]]; unfold in_zr in Hin; cbn [fst snd] in Hin;
    rewrite ?HspT in Hin; apply HX; left; lia. }
assert (HS5 : st_ok (fx:=fx') tfibsegs (havoc E 49 (map (getr regs') CLOB)) sv_s5
  (restrict (w_H W) (mkst (fx:=fx') regs' (Z_to_bv 64 RA_VFPI) mem' (seg_rom tfibsegs)))).
{ apply (kcall_fx fx fx' W E sv_e4 ms sp 304 sv_e4r [gv_can] 49 RA_VFPI (-304) (-304) (-56) 0
    (fun a => (sp - 304 - Kvi <= a < sp - 56) \/ svXW a) regs' mem'
    HS s4_resv E2 sv_e4_mem s4_base s4_lo s4_hi ltac:(rewrite s4_wlo; lia) ltac:(rewrite s4_whi; lia)
    s4_at s4_wf s4_nc s4_ma s4_ci ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  - intros a [Hc|Hc] Hb; unfold svXW in *; lia.
  - intros r a [<-|[]] Ha. unfold gv_can in Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha.
    apply Forall_snp in Hgvd as [_ Hgvd2]. unfold zdisjoint in Hgvd2. cbn [fst snd] in Hgvd2.
    split; [unfold FM_canary in *; lia|]. split; [unfold FM_canary in *; lia|].
    intros [Hc|Hc]; unfold svXW, FM_canary in *; lia.
  - intros r a [<-|[]] Ha. unfold gv_can in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia.
  - intros a Ha. apply Hp1. lia.
  - exact Hpres'.
  - exact HFRv.
  - exact Hpm'. }
assert (HRAZ : raZ (ms_regs ms) = RA_VFPI)
  by (unfold raZ; rewrite R1; apply unsigned_lit_small; unfold RA_VFPI; lia).
rewrite HRAZ. unfold cfg_at.
apply (sv_epi (fy:=fx') (havoc E 49 (map (getr regs') CLOB))
  (mkst (fx:=fx') regs' (w64 RA_VFPI) mem' (seg_rom tfibsegs)) md').
- apply svOK_havoc; [exact HE | lia].
- exact HS5.
- apply (sw_step B ly S U W mem md (sp - K) sp svXW (ms_mem ms) mdX mem' md'
    (sw_mono B ly S U W mem md (sp - K) sp (fun a => a = d) svXW (ms_mem ms) mdX HF
       ltac:(intros a ->; unfold svXW; lia))
    HAR' Hsbm').
  + intros a Ha. apply Hpm'. apply Hp1. exact Ha.
  + intros a Ha H1 H2. apply HFRv; [exact Ha | lia |].
    intros [Hc|Hc]; [apply H1; lia | exact (H2 Hc)].
  + exact Hpm'.
- exact Ha0'.
- exact Hbytes'.
- exact Hfpr.
- exact Hcsr.
Qed.

(* ---- from after the d store to the call ---- *)
Lemma sv_run3 : forall E ms mdX, svOK E -> st_ok tfibsegs E sv_s3 (restrict (w_H W) ms) ->
  svFR (fun a => a = d) (ms_mem ms) mdX -> aview tfibsegs (w_H W) (ms_mem ms) d = Some 0 ->
  SRr tfibsegs W (mkCfg ms mdX) svQ.
Proof.
intros E ms mdX HE HS HF HD0. svg.
eapply SRr_bind; [exact (g_phase_to W E A_VFPI sv_s3 sv_e4 _ ms mdX HS r_sv4)|].
intros W' c' _ (-> & ms4 & mat4 & -> & HS4 & HF4).
apply (sv_call2 E ms4 _ HE HS4
  (sv_frame_run (fun a => a = d) E sv_s3 sv_e4 ms ms4 mdX mat4 HF HE HS4 HF4 c_sw3 c_sk4)).
rewrite (sv_run_out E sv_s3 (ms_mem ms) (ms_mem ms4) d HE HF4 c_sw3 ltac:(lia) ltac:(lia)). exact HD0.
Qed.

(* ---- `sb zero, 0(s3)`: *d = 0 ---- *)
Lemma sv_store : forall E ms mdX, svOK E -> st_ok tfibsegs E sv_e3 (restrict (w_H W) ms) ->
  svFR (fun a => a = d) (ms_mem ms) mdX -> SRr tfibsegs W (mkCfg ms mdX) svQ.
Proof.
intros E ms mdX HE HS HF. svg. svp. pose proof (svOK_sp E HE) as E2.
assert (HW : writable_at tfibsegs (mrestrict (w_H W) (ms_mem ms)) d).
{ destruct (Hdst d ltac:(lia)) as (Hw & _). destruct HF as (_ & _ & _ & _ & Hpm).
  exact (writable_xfer (w_H W) mem (ms_mem ms) d Hw (Hpm d)). }
assert (R19 : getr (ms_regs ms) 19 = Z_to_bv 64 d).
{ rewrite (sv_rd E sv_e3 ms 19 HS), s3_s3, (sv_den_reg E 10 10%bv HE eq_refl). exact G10. }
apply Forall_snp in Hgvd as [_ Hgvd2]. unfold zdisjoint in Hgvd2. cbn [fst snd] in Hgvd2.
eapply SRr_bind.
{ apply (kstore0 tbl_g W E sv_e3 ms mdX 0x94c50 622627 19%bv d tbl_g_ok HS s3_pc s3_resv ltac:(lia) ltac:(lia)
    c3_lk c3_ec c3_dec R19 ltac:(lia) HW).
  intros r x Hr Hx Heq. rewrite sv_e3_mem in Hr. destruct Hr as [<-|[<-|[]]].
  - rewrite s3_base, s3_lo, s3_hi in Hx. cbn [base_val] in Hx. rewrite E2 in Hx.
    apply gv_bv64_inj in Heq; [| lia | lia]. lia.
  - unfold gv_can in Hx. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Hx.
    apply gv_bv64_inj in Heq; [| unfold FM_canary in *; lia | lia]. unfold FM_canary in *. lia. }
intros W' c' _ (-> & ms1 & mat1 & -> & HS1 & HR1 & HM1).
destruct (sv_store_frame (ms_mem ms) (ms_mem ms1) mdX mat1 HF HW HM1) as [HF1 HD1].
exact (sv_run3 E ms1 _ HE HS1 HF1 HD1).
Qed.

(* ---- after memset: the FILE stores up to the d store ---- *)
Lemma sv_run2 : forall E ms mdX, svOK E -> st_ok tfibsegs E sv_s2 (restrict (w_H W) ms) ->
  svFR (fun a => a = d) (ms_mem ms) mdX -> SRr tfibsegs W (mkCfg ms mdX) svQ.
Proof.
intros E ms mdX HE HS HF.
eapply SRr_bind; [exact (g_phase_to W E A_VFPI sv_s2 sv_e3 _ ms mdX HS r_sv3)|].
intros W' c' _ (-> & ms3 & mat3 & -> & HS3 & HF3).
exact (sv_store E ms3 _ HE HS3
  (sv_frame_run (fun a => a = d) E sv_s2 sv_e3 ms ms3 mdX mat3 HF HE HS3 HF3 c_sw2 c_sk3)).
Qed.

(* ---- the memset (sp - 0x130, 0, 0xe8) call ---- *)
Lemma sv_call1 : forall E ms mdX, svOK E -> st_ok tfibsegs E sv_e1d (restrict (w_H W) ms) ->
  svFR (fun a => a = d) (ms_mem ms) mdX -> SRr tfibsegs W (mkCfg ms mdX) svQ.
Proof.
intros E ms mdX HE HS HF. svg. svp. pose proof (svOK_sp E HE) as E2.
pose proof HF as (HA1 & Hsb1 & Hp1 & Hk1 & Hpm1).
assert (R1 : getr (ms_regs ms) 1 = Z_to_bv 64 RA_MSET) by (rewrite (sv_rd E sv_e1d ms 1 HS), s1_ra; reflexivity).
assert (R2 : getr (ms_regs ms) 2 = w64 (sp - 304)).
{ rewrite (sv_rd E sv_e1d ms 2 HS), s1_sp, (sv_den_sp E _ HE). unfold w64. f_equal; lia. }
assert (R3 : getr (ms_regs ms) 3 = w64 (as_gp B)).
{ rewrite (sv_rd E sv_e1d ms 3 HS), s1_gp, (sv_den_reg E 3 3%bv HE eq_refl). exact HGP. }
assert (R4 : getr (ms_regs ms) 4 = w64 (as_tp B)).
{ rewrite (sv_rd E sv_e1d ms 4 HS), s1_tp, (sv_den_reg E 4 4%bv HE eq_refl). exact HTP. }
assert (R10 : getr (ms_regs ms) 10 = w64 (sp - 304)).
{ rewrite (sv_rd E sv_e1d ms 10 HS), s1_a0, (sv_den_sp E _ HE). unfold w64. f_equal; lia. }
assert (R11 : getr (ms_regs ms) 11 = w64 0) by (rewrite (sv_rd E sv_e1d ms 11 HS), s1_a1; reflexivity).
assert (R12 : getr (ms_regs ms) 12 = w64 232) by (rewrite (sv_rd E sv_e1d ms 12 HS), s1_a2; reflexivity).
assert (HspT : spZ (ms_regs ms) = sp - 304).
{ change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) 2)). rewrite R2. unfold w64.
  apply unsigned_lit_small; lia. }
assert (Hsp16 : sp = 16 * (sp / 16)) by (pose proof (Z.div_mod sp 16 ltac:(lia)); lia).
assert (H8 : (sp - 304) mod 8 = 0).
{ rewrite Hsp16. replace (16 * (sp / 16) - 304) with ((2 * (sp / 16) - 38) * 8) by lia. apply Z.mod_mul. lia. }
destruct (sv_shadow (ms_mem ms) mdX (sp - 304) 232 HA1 ltac:(lia) ltac:(lia) H8 ltac:(reflexivity) ltac:(lia))
  as [Hra2 Hhull2].
eapply SRr_bind.
{ apply (kcall W E sv_e1d ms mdX sp 304 sv_e1r [gv_can] 33 RA_MSET (-304) (-304) (-72) 0
    (fun a => sp - 4400 <= a < sp - 72)
    (fun regs2 mem2 md2 => ARU tfibsegs B ly S U W mem2 md2 /\
       (forall i, 0 <= i < 232 -> aview tfibsegs (w_H W) mem2 (sp - 304 + i) = Some 0))
    HS s1_resv E2 eq_refl s1_base s1_lo s1_hi ltac:(rewrite s1_wlo; lia) ltac:(rewrite s1_whi; lia)
    s1_ra s1_sp s1_at s1_wf s1_nc s1_ma s1_ci ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  - intros a Ha Hb. lia.
  - intros r a [<-|[]] Ha. unfold gv_can in Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha.
    split; [unfold FM_canary in *; lia|]. split; unfold FM_canary in *; lia.
  - intros r a [<-|[]] Ha. unfold gv_can in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia.
  - intros a Ha. apply Hp1. lia.
  - rewrite s1_pc. eapply SRr_mono.
    { apply (AMEMSET ly S U W (ms_regs ms) (ms_mem ms) mdX (sp - 304) 0 232).
      - apply (g_ecall_preU B ly S U W (ms_regs ms) (ms_mem ms) mdX HA1).
        + rewrite R1. apply ret_ok_lit; [unfold RA_MSET; lia | unfold RA_MSET; reflexivity].
        + rewrite HspT. replace (sp - 304) with (sp + (-19) * 16) by lia. rewrite Z_mod_plus_full. exact GE3.
        + rewrite HspT. lia.
        + rewrite HspT. lia.
        + rewrite HspT. intros a Ha. apply Hp1. lia.
        + exact R3.
        + exact R4.
      - exact R10.
      - exact R11.
      - exact R12.
      - lia.
      - lia.
      - lia.
      - intros a Ha. split; [apply apresent_writable; apply Hp1; lia|].
        split; [apply (ARU_stack tfibsegs B LAWS ly S U W (ms_mem ms) mdX a HA1); lia | rewrite HspT; lia].
      - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
      - exact Hra2.
      - exact Hhull2.
      - exact I. }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsbm & _ & Heff & Hfr2 & Hpres2).
    split; [reflexivity|]. exists regs2, mem2, md2.
    split; [unfold cfg_at, raZ; rewrite R1, unsigned_lit_small by (unfold RA_MSET; lia); reflexivity|].
    split; [exact HP|]. split; [exact Hsbm|].
    split.
    { intros a Ha Hb Hx. apply Hfr2; [exact Ha | intros C; apply Hx; lia | rewrite HspT; intros C; apply Hx; lia]. }
    split; [exact Hpres2|]. split; [exact HAR2|]. intros i Hi. rewrite (Heff i Hi). reflexivity. }
intros W' c' _ (-> & ms2 & mat2 & -> & HS2 & HP2 & Hfr2 & Hpm2 & HAR2 & HZ2).
assert (HE2 : svOK (havoc E 33 (map (getr (ms_regs ms2)) CLOB))) by (apply svOK_havoc; [exact HE | lia]).
assert (HS2' : st_ok tfibsegs (havoc E 33 (map (getr (ms_regs ms2)) CLOB)) sv_s2 (restrict (w_H W) ms2)).
{ apply (gv_st_ok_add _ sv_k1 (restrict (w_H W) ms2) sv_k1r [gv_can] gv_zc HS2 sv_k1_mem s1_zc).
  rewrite s1_kb. cbn [base_val]. rewrite (svOK_sp _ HE2). unfold gv_zc. apply chunk_ok_zero.
  intros i Hi. change (ms_mem (restrict (w_H W) ms2)) with (mrestrict (w_H W) (ms_mem ms2)). apply YF0x.aview_byte.
  replace (sp + -304 + i) with (sp - 304 + i) by lia. exact (HZ2 i Hi). }
assert (HF2 : svFR (fun a => a = d) (ms_mem ms2) (with_vm_backing (m_vm_lazy mdX) mat2 mdX)).
{ apply (sw_step B ly S U W mem md (sp - K) sp (fun a => a = d) (ms_mem ms) mdX (ms_mem ms2) _ HF HAR2
    (with_vm_backing_same mdX mat2)).
  - intros a Ha. apply Hpm2. exact (Hp1 a Ha).
  - intros a Ha Hout Hx. apply Hfr2; [exact Ha | lia | intros C; apply Hout; lia].
  - exact Hpm2. }
exact (sv_run2 _ ms2 _ HE2 HS2' HF2).
Qed.

(* ---- the entry: st_ok of sv_s0, the run to the memset call ---- *)
Lemma sv_main : SRr tfibsegs W (cfg_at tfibsegs A_VSN regs mem md) svQ.
Proof.
svg. svp.
assert (EE2 : bv_unsigned (ew svE0 2) = sp) by exact (svOK_sp svE0 svOK_E0).
assert (EE32 : bv_unsigned (ew svE0 32) = cval)
  by (rewrite (svOK_can svE0 svOK_E0); apply unsigned_lit_small; exact sv_cval).
assert (EE11 : bv_unsigned (ew svE0 11) = n)
  by (rewrite (svOK_reg svE0 11 11%bv svOK_E0 eq_refl), G11; unfold w64; apply unsigned_lit_small; lia).
assert (HS0 : st_ok tfibsegs svE0 sv_s0 (restrict (w_H W) (mkst regs (Z_to_bv 64 A_VSN) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold sv_s0, svE0. apply (entry_st_ok_full tfibsegs);
    change (Ereg regs [Z_to_bv 64 cval]) with svE0.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + unfold sv_stk0. apply (region_ok_stack tfibsegs svE0 _ 2 sp (-304)); [exact EE2 | lia | lia |].
      intros a Ha. apply apresent_writable. apply sv_pres. lia.
    + unfold gv_got, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      split; [unfold FM_GOT_canary; lia|]. split; [unfold FM_GOT_canary; lia|].
      split; [intros o Ho; exfalso; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs svE0 _ 0 FM_GOT_canary 8 (SLit FM_canary) FM_canary);
        [reflexivity | unfold FM_canary; cbn; lia | cbn; lia |].
      rewrite Z.add_0_l. rewrite <- GVV. rewrite <- GCV.
      exact (val_mem_of_rdword (w_H W) mem gc gv Hgcw).
    + unfold gv_can, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      split; [unfold FM_canary; lia|]. split; [unfold FM_canary; lia|].
      split; [intros o Ho; exfalso; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs svE0 _ 0 FM_canary 8 (SOff 32 0) cval);
        [cbn [sv_denot]; rewrite EE32, Z.add_0_r; reflexivity
        | cbn; pose proof sv_cval; lia | cbn; lia |].
      rewrite Z.add_0_l. rewrite <- GVV. exact (val_mem_of_rdword (w_H W) mem gv cval Hgvw).
  - apply pairwise_disjoint_of_extents. unfold sv_stk0, gv_got, gv_can, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite EE2.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold FM_canary, FM_GOT_canary in *. repeat split; lia.
  - split; [|split; exact I]. cbn [sv_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite EE2, EE11. change (2 ^ 4) with 16. change (2 ^ 0) with 1.
    repeat split; first [apply Z.mod_1_r | exact GE3 | lia]. }
unfold cfg_at, w64.
eapply SRr_bind; [exact (g_phase_to W svE0 W_MEMSET sv_s0 sv_e1 _ _ md HS0 r_sv1)|].
intros W' c' _ (-> & ms1 & mat1 & -> & HS1 & HF1).
pose proof (sv_frame_run (fun a => a = d) svE0 sv_s0 sv_e1
  (mkst regs (Z_to_bv 64 A_VSN) mem (seg_rom tfibsegs)) ms1 md mat1 sv_frame_init svOK_E0 HS1 HF1 c_sw0 c_sk1) as HFR1.
exact (sv_call1 svE0 ms1 _ svOK_E0 (st_ok_del svE0 sv_e1 _ [sv_e1r] gv_got [gv_can] HS1 sv_e1_mem) HFR1).
Qed.
End w.

(* ---- the walk, and the shared contract it gives ---- *)
Theorem svsn_walk : sn_walkA B FF K gc gv img_lo img_hi cr A_VSN.
Proof.
intros ly S U W regs mem md d n f ap ws T cval HPRE HDOG HFRM HORD HSL H47 HD8 HRA HGP HTP G10 G11 G12 G13.
apply (sv_main ly S U W regs mem md d n f ap ws T cval); assumption.
Qed.
Theorem svsn_ok : sh_avsnprintf_realizesUa tfibsegs B FF K gc gv img_lo img_hi cr A_VSN.
Proof.
assert (HK : ESTACK <= K) by (assert (HES : ESTACK = 4096) by reflexivity; lia).
exact (proj1 (sn_contractA B FF K gc gv img_lo img_hi cr A_VSN HK svsn_walk)).
Qed.
Theorem svsn_icpt_ok : sh_avsnprintf_icpt_realizesUa tfibsegs B FF K gc gv img_lo img_hi cr A_VSN.
Proof.
assert (HK : ESTACK <= K) by (assert (HES : ESTACK = 4096) by reflexivity; lia).
exact (proj2 (sn_contractA B FF K gc gv img_lo img_hi cr A_VSN HK svsn_walk)).
Qed.
End v.
