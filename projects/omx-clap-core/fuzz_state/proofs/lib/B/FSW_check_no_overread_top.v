(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFl3.v:106-108
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:383-389, 448-454, 493-498, 501-509 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:625-631 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:208-214, 227-233 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan
   build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg10.v, with its module paths and module names changed; 2634 of its 2686 lines of code are new or changed and 608 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_parse_value.v, with its module paths, module names, addresses and numbers changed; 1012 of its 1163 lines of code are new or changed and 2535 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSW_check_no_overread.v; 491 of its 541 lines of code are new or changed and 1113 lines of the source are left out. *)
(* check_no_overread B 0x8124c (fs.c), fs.asan-ubsan: the TOP of the CTX-free ASan walk of lib/B/FSH_Fn_cno.v
   check_no_overread_spec (the FROZEN B statement; this file proves it, it does not restate it). Owner of this file:
   a Theorem Labs lane.
   It chains the entry and segment 1 (lib/B/FSW_check_no_overread.v cno_seg1, 0x8124c-0x8137c), the two past_nul calls
   (cno_call_pn, 0x8137c / 0x81390), the __wrap_malloc call (cno_call_mal_T, 0x8139c) up to INV_M (0x813a0), then the
   three spans of lib/B/FSW_check_no_overread_inv.v, each its real lemma (segM_T: INV_M -> INV_D1, _segM.v cno_segM;
   segD_T: INV_D1 -> INV_F1, _segD.v segD; segF_T: INV_F1 -> INV_R, _segF.v segF) and the tail (cno_tail_ret,
   _ret.v), and states check_no_overread_ok. Each call site is one call
   step of the interface (cno_site -> cno_ret); the code between two call sites is run by the engine (FSW_K
   fsw_aj_run_toU), and the symbolic state at each return is rebuilt by cno_resume (_inv.v). The chain is written
   backwards: `cno_from ss INV` at the returns of past_nul x2 (INV_P1 at 0x81380, INV_P2 at 0x81394, this file) and of
   __wrap_malloc (INV_M at 0x813a0, _inv.v); every boundary is the state the segment before it produces.
   MEASURED (listing (internal path)):
   0x81380 `sd a0,24(s1)` (a into the slot 0x18(s1)), 0x81384 `li a2,66`, 0x81388 `mv a0,s7`, 0x8138c `mv a1,s6`,
   0x81390 `jal past_nul`; 0x81394 `mv s4,a0` (b), 0x81398 `addi a0,s6,18`, 0x8139c `jal wrapper_malloc`. Registers
   across the range: s0 = sp0, s1 = sp = sp1, s2 = the frame's shadow, s3 = s9 = the frame F, s6 = len, s7 = d,
   s8 = the shadow base.
   GUARDS in 0x8124c-0x813a0 past segment 1: none. The range 0x81380-0x8139c holds three jal, one store and five
   register moves only: no branch, no UBSan check (U1 / U2 / U3 are at 0x813c0 / 0x813e0 / 0x813f8, in segM's range),
   no inline ASan check (0x813c8-0x813d4 and 0x81404-0x81410, segM's range). The `beqz a0` at 0x813a0 (malloc NULL ->
   the abort block) is segM's first instruction; INV_M carries `t <> 0` from cno_call_mal_T's post for it.
   Section hypotheses of check_no_overread_ok (Section F): ONLY the callee contracts in CTX-free form (past_nul_spec,
   decode_spec_ff, fuzz_free_spec), the runtime contracts (__asan_stack_malloc_1, __wrap_malloc / __wrap_free,
   __asan_memcpy / __asan_memset, bcmp), the image facts and the B-cell equations; no span Prop. Every call step and
   every span is applied as its real lemma.
   LOOKUP (rule 24): proof-index by NAME check_no_overread and by B ADDRESS 0x8124c, unpiped, a Theorem Labs lane
   2026-10-29 05:4xZ (outputs (internal path), r24-cnoB-addr.txt): released plain /
   UBSan templates only, no released lib/A or lib/B walk; 0x8124c: 0 released hits. CONFIRM:
   (internal path).
   Template (text only, B addresses MEASURED): lib/A/FSW_check_no_overread_top.v at a working branch
   bfe2a7f05ba. Kit lemmas by path (lib/B FSW_K / FSW_rd / YCem; lib/A's image-generic FSupoison / FSupoisonU /
   FSH_Gen; Reusable). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_ret FSW_rres FSW_frame FSW_strkit FSW_rd FSH_Fn_cno FSH_Fn_alloc
FSW_check_no_overread_tbl FSW_check_no_overread FSW_check_no_overread_inv.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSH_Fn_writer YCem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSW_check_no_overread_mem FSW_check_no_overread_dec
  FSW_check_no_overread_tail FSW_check_no_overread_ret FSW_check_no_overread_ffree FSW_check_no_overread_segM
  FSW_check_no_overread_segD FSW_check_no_overread_segF.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================= the boundary states ================= *)
(* the return of the first past_nul (0x81380): the walk's four regions, nothing in the slots yet; the return of the
   second (0x81394): a in the slot 0x18(s1) (0x81380 `sd a0,24(s1)`), the walk's extra atom 48 (_inv.v cno_sl18) *)
Definition ss_P1 : sstate := cno_ss 0x81380 19 18 cno_flag_chunk [].
Definition ss_P2 : sstate := cno_ss 0x81394 19 18 cno_flag_chunk cno_sl18.

(* a chunk's membership in a computed chunk list *)
Ltac cno_inc := vm_compute; repeat first [left; reflexivity | right].

(* ================= the chain ================= *)
Section T. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
(* past_nul's contract (CTX-free), for the call step cno_call_pn *)
Hypothesis PN : past_nul_spec tfibsegs B.
(* segment 1's (FSW_check_no_overread.v Section W) *)
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis HGOT : as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address.
Hypothesis HCELL : as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address.
Hypothesis HGUAR : as_got_uar B = fs_D_GOT_uar.
Hypothesis HUCELL : as_uar_cell B = fs_D_uar_cell.
Hypothesis HSM1 : pc_stack_malloc (as_code B) 1 = PC_stack_malloc_1.
Hypothesis ASM1 : astack_malloc_realizesU tfibsegs B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis FS_ENV : api_env tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
(* the __wrap_malloc call step, exactly the interface's Prop (FSW_check_no_overread.v Section I, CTX-free) *)
Hypothesis cno_call_mal : cno_call_mal_T B.

(* ---- P1: the return of the first past_nul (0x81380): a = past_nul (d, len, 'A') in a0, nothing else changed ---- *)
Definition INV_P1 : cno_inv := fun cx E k ly3 S3 U3 W3 ms3 md3 => exists a,
  U3 = c_U cx /\ k = 1 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ [(a, cno_n cx + 18)] /\
  a <> 0 /\ a mod 16 = 0 /\ cno_core cx E /\ ew E 10 = w64 a /\
  ew E 22 = w64 (cno_n cx) /\ ew E 23 = w64 (c_d cx) /\ ew E 24 = w64 SHADOW_OFF /\ ew E 25 = w64 (cno_F cx) /\
  zbytes_at tfibsegs W3 (ms_mem ms3) a (pn_copy (c_db cx) 65) /\
  fs_glob tfibsegs W3 (ms_mem ms3) (c_live cx) (c_peak cx) (c_cnt cx) (c_fail cx) /\
  FSupoisonU.fs_heads B ly3 S3 U3.

(* ---- the entry: segment 1 (to the first past_nul call 0x8137c), the call, the return P1 ---- *)
Lemma cno_enter : cno_from B ss_P1 INV_P1 -> check_no_overread_spec tfibsegs B.
Proof.
intros HNX ly S U W regs mem md ch d db live peak cnt fail HPRE Hh Hfr Htop Hd Hn Hsrc Hnz Hblk Hmax Hg Hq
  Hhd Hnev Hbb.
pose proof HPRE as (HAPU & HRO).
apply (cno_seg1 B IMG HGOT HCELL HGUAR HUCELL HSM1 ASM1 SMP FS_ENV ML ly S U W regs mem md ch _ HAPU HRO Hfr).
cbv zeta. intros S2 pos regs2 md2 ms mat HS HJ HARU Hin Hfrs Eab Hnev2 Hbb2 HR2 HLG.
set (cx := mkCNOCX ly S U W regs mem md ch d db live peak cnt fail pos).
assert (Hb : cno_base B cx)
  by exact (conj HPRE (conj Hh (conj Hfr (conj Htop (conj Hd (conj Hn (conj Hsrc (conj Hnz (conj Hblk
    (conj Hmax (conj Hg (conj Hq (conj Hhd (conj Hnev Hbb)))))))))))))).
pose proof (cno_nums B cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof cno_stk as FS.
destruct HR2 as (G2 & G9 & G8 & G3 & G4 & G10 & G22 & G23 & G24).
set (md2' := with_vm_backing (m_vm_lazy md2) mat md2) in *.
change (st_ok tfibsegs (cno_env cx regs2 0 0 0) cno_ssC (restrict (w_H W) ms)) in HS.
set (E := cno_env cx regs2 0 0 0) in *.
assert (HE : cno_E cx E) by apply cno_E_env.
pose proof (ARU_AR tfibsegs B ly S2 U W (ms_mem ms) md2' HARU) as HAR2.
destruct (frames_bounds tfibsegs B LAWS ly S2 W (unpoison U (ms_mem ms)) md2' 1 pos HAR2 Hin) as (HF4096 & HFceil & HFapp).
change (fs_frame_bytes 1) with 128 in HF4096, HFceil, HFapp.
change (frame_addr ly 1 pos) with (cno_F cx) in HF4096, HFceil, HFapp.
pose proof (shadow_addr_bounds (cno_F cx) ltac:(lia)) as (Hs1 & Hs2).
assert (HF64 : 0 <= cno_F cx < 2 ^ 64) by (unfold in_app, kLowShadowBeg, ASAN_CEIL in HFapp; lia).
assert (E8 : bv_unsigned (ew E 8) = cno_sp0 cx)
  by (subst E; unfold cno_env; rewrite (ew_Ereg_nat regs2 _ 8 8%bv eq_refl), G8; apply wz; unfold cno_sp0 in *; lia).
(* the registers at the call (0x8137c), read off cno_ssC: s3 = s9 = the frame (atom 10), s6 / s7 = len / d,
   s8 = the shadow base (atom 24), s2 = the frame's shadow (extra atom 47), a0 / a1 / a2 = d / len / 'A' *)
assert (R2 : getr (ms_regs ms) 2 = w64 (cno_sp1 cx))
  by (rewrite (fsw_reg_atom (w_H W) regs2 _ cno_ssC ms 2%bv 2%bv 2 HS ltac:(vm_compute; reflexivity) eq_refl), G2;
      reflexivity).
assert (R9 : getr (ms_regs ms) 9 = w64 (cno_sp1 cx))
  by (rewrite (fsw_reg_atom (w_H W) regs2 _ cno_ssC ms 9%bv 9%bv 9 HS ltac:(vm_compute; reflexivity) eq_refl), G9;
      reflexivity).
assert (R8 : getr (ms_regs ms) 8 = w64 (cno_sp0 cx))
  by (rewrite (fsw_reg_atom (w_H W) regs2 _ cno_ssC ms 8%bv 8%bv 8 HS ltac:(vm_compute; reflexivity) eq_refl), G8;
      reflexivity).
assert (R3 : getr (ms_regs ms) 3 = getr (c_regs cx) 3)
  by (rewrite (fsw_reg_atom (w_H W) regs2 _ cno_ssC ms 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl), G3;
      reflexivity).
assert (R4 : getr (ms_regs ms) 4 = getr (c_regs cx) 4)
  by (rewrite (fsw_reg_atom (w_H W) regs2 _ cno_ssC ms 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl), G4;
      reflexivity).
assert (R1 : getr (ms_regs ms) 1 = w64 0x81380)
  by exact (fsw_reg_lit (w_H W) E cno_ssC ms 1%bv 0x81380 HS ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (R10 : getr (ms_regs ms) 10 = w64 (c_d cx))
  by (rewrite (fsw_reg_atom (w_H W) regs2 _ cno_ssC ms 10%bv 23%bv 23 HS ltac:(vm_compute; reflexivity) eq_refl), G23;
      exact Hd).
assert (R11 : getr (ms_regs ms) 11 = w64 (cno_n cx))
  by (rewrite (fsw_reg_atom (w_H W) regs2 _ cno_ssC ms 11%bv 22%bv 22 HS ltac:(vm_compute; reflexivity) eq_refl), G22;
      exact Hn).
assert (R12 : getr (ms_regs ms) 12 = w64 65)
  by exact (fsw_reg_lit (w_H W) E cno_ssC ms 12%bv 65 HS ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (R18 : getr (ms_regs ms) 18 = w64 (cno_SF cx))
  by exact (fsw_reg_extra (w_H W) regs2 _ cno_ssC ms 18%bv 15 HS ltac:(vm_compute; reflexivity)).
assert (R19 : getr (ms_regs ms) 19 = w64 (cno_F cx))
  by (rewrite (fsw_reg_atom (w_H W) regs2 _ cno_ssC ms 19%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl), G10;
      reflexivity).
assert (R22 : getr (ms_regs ms) 22 = w64 (cno_n cx))
  by (rewrite (fsw_reg_atom (w_H W) regs2 _ cno_ssC ms 22%bv 22%bv 22 HS ltac:(vm_compute; reflexivity) eq_refl), G22;
      exact Hn).
assert (R23 : getr (ms_regs ms) 23 = w64 (c_d cx))
  by (rewrite (fsw_reg_atom (w_H W) regs2 _ cno_ssC ms 23%bv 23%bv 23 HS ltac:(vm_compute; reflexivity) eq_refl), G23;
      exact Hd).
assert (R24 : getr (ms_regs ms) 24 = w64 SHADOW_OFF)
  by (rewrite (fsw_reg_atom (w_H W) regs2 _ cno_ssC ms 24%bv 24%bv 24 HS ltac:(vm_compute; reflexivity) eq_refl), G24;
      reflexivity).
assert (R25 : getr (ms_regs ms) 25 = w64 (cno_F cx))
  by (rewrite (fsw_reg_atom (w_H W) regs2 _ cno_ssC ms 25%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl), G10;
      reflexivity).
assert (Hh2 : FSupoisonU.fs_heads B ly S2 U) by exact (cno_heads B ly S ly S2 U Eab Hh).
assert (Hsite : cno_site B cx 0 ly S2 U W (ms_regs ms) (ms_mem ms) md2')
  by exact (cno_site_of B cx E cno_ssC W ms 0 ly S2 U md2' 0x81380 HE E8 HS ltac:(vm_compute; reflexivity) HJ HARU
    Hh2 R2 R8 R3 R4 R1 ltac:(lia) ltac:(reflexivity)).
destruct (cno_src_kept B cx 0 ly S2 W (ms_mem ms) md2' Hb HJ HARU) as (Hsrc2 & Hblk2).
assert (Hg2 : fs_glob tfibsegs W (ms_mem ms) live peak cnt fail)
  by exact (cno_glob_ledger W W mem (ms_mem ms) _ _ _ _ HLG Hg).
(* the call *)
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E cno_ssC ms HS eq_refl).
replace (ss_pc cno_ssC) with A_past_nul by (vm_compute; reflexivity).
change (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 A_past_nul) (ms_mem ms) (seg_rom tfibsegs)) md2')
  with (cfg_at tfibsegs A_past_nul (ms_regs ms) (ms_mem ms) md2').
assert (Hq1 : quiet cnt fail 1) by (unfold quiet in *; lia).
assert (Hk1 : 0 + 1 <= EV_check_no_overread) by (unfold EV_check_no_overread; lia).
assert (Hbb1 : blocks_bytes S2 + (cno_n cx + 18) <= LIVE_MAX).
{ rewrite Hbb2. change (cno_n cx) with (Z.of_nat (length db)).
  unfold LIVE_check_no_overread, PRESET_FILE_MAX_BYTES in *. lia. }
eapply SRr_bind.
{ exact (cno_call_pn B PN cx 0 ly S2 U W (ms_regs ms) (ms_mem ms) md2' 65 live peak cnt fail
    Hb Hsite (or_introl R1) R10 R11 R12 ltac:(lia) Hsrc2 Hblk2 Hg2 Hq1 Hk1 Hbb1). }
cbv beta. intros W' c' _ (res & Hret).
(* the frame's flag chunk at the call (the frame region of cno_ssC, base atom 10 = F) *)
pose (r1 := match nth_error (ss_mem cno_ssC) 1 with Some r => r | None => YP09.mkRegion None 0 0 0 0 [] end).
assert (Hr1 : nth_error (ss_mem cno_ssC) 1 = Some r1) by (vm_compute; reflexivity).
assert (Hrb1 : YP09.r_base r1 = Some 10%nat) by (vm_compute; reflexivity).
assert (Hrc1 : In (YP09.mkChunk 120 (CVal 8 (SOff 46 0))) (YP09.r_chunks r1)) by cno_inc.
pose proof (fsw_region_nth _ _ _ 1 _ HS Hr1) as HR1. cbn [ms_mem restrict] in HR1.
destruct HR1 as (_ & _ & _ & Hcs1). rewrite Hrb1 in Hcs1. cbn [base_val] in Hcs1.
assert (E10 : bv_unsigned (ew E 10) = cno_F cx)
  by (subst E; unfold cno_env; rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl), G10; apply wz; exact HF64).
rewrite E10 in Hcs1.
pose proof (proj1 (Forall_forall _ _) Hcs1 _ Hrc1) as Hflag.
destruct (cno_resume B cx 0 ly S2 U W (ms_regs ms) (ms_mem ms) md2' 1 U (fun _ => False) _ W' c'
  (fs_extraT ++ cno_extra regs (cno_FL cx) (cno_SF cx) res 0 0) cno_flag_chunk [] Hb Hsite Hret R9 R18 R19)
  as (ly' & S' & regs' & mem' & md' & Ec & HJ' & HARU' & Hh' & HP & HBK & HZ & HPP & HS').
- intros a _ X. exact X.
- vm_compute. reflexivity.
- intros regs'. apply (proj2 (proj2 (cno_saved_of_st cx E cno_ssC W ms HE E8 HS ltac:(vm_compute; reflexivity)))).
  intros j Hj. exact (cno_env_saved cx regs2 regs' 0 0 0 res 0 0 j Hj).
- constructor; [|apply Forall_nil]. cbn. split; [lia|]. split; [lia|]. intros i _ X. exact X.
- apply Forall_nil.
- intros regs' _. constructor; [|apply Forall_nil].
  apply (cno_chunk_env E _ _ _ _ _ _ _ Hflag). rewrite !fsw_SOff0. unfold cno_env.
  change 46%nat with (32 + 14)%nat. rewrite !ew_Ereg_extra. reflexivity.
- intros regs' _. apply Forall_nil.
- cbv beta in HPP. destruct HPP as (E10' & Hres0 & Hres16 & Hab & Hz & Hg').
  assert (Era : raZ (ms_regs ms) = 0x81380) by (unfold raZ; rewrite R1; unfold w64; apply wz; lia).
  rewrite Era in Ec, HS'. subst c'.
  set (E' := Ereg regs' (fs_extraT ++ cno_extra regs (cno_FL cx) (cno_SF cx) res 0 0)) in *.
  assert (KR : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> acallee_saved (bv_unsigned r) ->
    ew E' n = getr (ms_regs ms) r).
  { intros r n Hn' Hc. subst E'. rewrite (ew_Ereg_nat regs' _ n r Hn'). exact (fsw_pres _ _ r HP Hc). }
  apply (HNX cx E' (0 + 1) ly' S' U W' (mkst regs' (Z_to_bv 64 0x81380) mem' (seg_rom tfibsegs)) md' Hb
    (cno_E_env cx regs' res 0 0) HJ' HARU').
  + exists res. split; [reflexivity|]. split; [reflexivity|].
    split; [cbn [ms_mem mkst]; rewrite Hab, Eab; reflexivity|].
    split; [exact Hres0|]. split; [exact Hres16|].
    split; [unfold cno_core; rewrite (KR 2%bv 2%nat eq_refl ltac:(cno_cs)), (KR 8%bv 8%nat eq_refl ltac:(cno_cs)),
      (KR 9%bv 9%nat eq_refl ltac:(cno_cs)), (KR 18%bv 18%nat eq_refl ltac:(cno_cs)), (KR 19%bv 19%nat eq_refl ltac:(cno_cs)),
      (KR 3%bv 3%nat eq_refl ltac:(cno_cs)), (KR 4%bv 4%nat eq_refl ltac:(cno_cs)); repeat split; assumption|].
    split; [subst E'; rewrite (ew_Ereg_nat regs' _ 10 10%bv eq_refl); exact E10'|].
    split; [rewrite (KR 22%bv 22%nat eq_refl ltac:(cno_cs)); exact R22|].
    split; [rewrite (KR 23%bv 23%nat eq_refl ltac:(cno_cs)); exact R23|].
    split; [rewrite (KR 24%bv 24%nat eq_refl ltac:(cno_cs)); exact R24|].
    split; [rewrite (KR 25%bv 25%nat eq_refl ltac:(cno_cs)); exact R25|].
    split; [exact Hz|]. split; [exact Hg' | exact Hh'].
  + exact HS'.
Qed.

(* ---- P2: the return of the second past_nul (0x81394): b = past_nul (d, len, 'B') in a0, a in the slot 0x18(s1) ---- *)
Definition INV_P2 : cno_inv := fun cx E k ly3 S3 U3 W3 ms3 md3 => exists a b,
  U3 = c_U cx /\ k = 2 /\
  ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ [(a, cno_n cx + 18); (b, cno_n cx + 18)] /\
  a <> 0 /\ a mod 16 = 0 /\ b <> 0 /\ b mod 16 = 0 /\ cno_core cx E /\ ew E 48 = w64 a /\ ew E 10 = w64 b /\
  ew E 22 = w64 (cno_n cx) /\ ew E 23 = w64 (c_d cx) /\ ew E 24 = w64 SHADOW_OFF /\ ew E 25 = w64 (cno_F cx) /\
  zbytes_at tfibsegs W3 (ms_mem ms3) a (pn_copy (c_db cx) 65) /\
  zbytes_at tfibsegs W3 (ms_mem ms3) b (pn_copy (c_db cx) 66) /\
  fs_glob tfibsegs W3 (ms_mem ms3) (c_live cx) (c_peak cx) (c_cnt cx) (c_fail cx) /\
  FSupoisonU.fs_heads B ly3 S3 U3.

(* ---- from P1: the store of a at 0x81380, the second past_nul call (0x81390), the return P2 ---- *)
Lemma cno_seg_P1 : cno_from B ss_P2 INV_P2 -> cno_from B ss_P1 INV_P1.
Proof.
intros HNX cx E k ly3 S3 U3 W3 ms3 md3 Hb HE HJ HARU HINV HS.
destruct HINV as (a & -> & -> & Hab & Ha0 & Ha16 & (C2 & C8 & C9 & C18 & C19 & C3 & C4) & E10 & E22 & E23 & E24 & E25
  & Hz & Hg & Hh).
pose proof (cno_nums B cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5). pose proof cno_stk as FS.
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & Hnevj & _).
assert (Hin : In (1, c_fpos cx) (frames S3)) by (rewrite Hfrs; left; reflexivity).
assert (EF : ly_F ly3 = ly_F (c_ly cx)) by (destruct Hly as (_ & _ & _ & _ & _ & X & _); exact X).
assert (EFa : cno_F cx = frame_addr ly3 1 (c_fpos cx)) by (unfold cno_F, frame_addr; rewrite EF; reflexivity).
pose proof (ARU_AR tfibsegs B ly3 S3 (c_U cx) W3 (ms_mem ms3) md3 HARU) as HAR.
destruct (frames_bounds tfibsegs B LAWS ly3 S3 W3 (unpoison (c_U cx) (ms_mem ms3)) md3 1 (c_fpos cx) HAR Hin)
  as (HF4096 & HFceil & HFapp).
rewrite <- EFa in HF4096, HFceil, HFapp. change (fs_frame_bytes 1) with 128 in HF4096, HFceil, HFapp.
pose proof (shadow_addr_bounds (cno_F cx) ltac:(lia)) as (Hs1 & Hs2).
assert (HF64 : 0 <= cno_F cx < 2 ^ 64) by (unfold in_app, kLowShadowBeg, ASAN_CEIL in HFapp; lia).
assert (U8 : bv_unsigned (ew E 8) = cno_sp0 cx) by (rewrite C8; unfold w64; apply wz; lia).
assert (U9 : bv_unsigned (ew E 9) = cno_sp1 cx) by (rewrite C9; unfold w64; apply wz; lia).
assert (U19 : bv_unsigned (ew E 19) = cno_F cx) by (rewrite C19; unfold w64; apply wz; lia).
assert (U18 : bv_unsigned (ew E 18) = cno_SF cx)
  by (rewrite C18; unfold w64; apply wz; unfold cno_SF, kHighShadowEnd in *; lia).
(* the run 0x81380 -> past_nul (the slot 0x18(s1) := a, a0 := d, a1 := len, a2 := 'B', ra := 0x81394) *)
fsw_aj_run_toU cno_tbl_ok HS HJ HARU A_past_nul.
{ eapply (cno_awr_ss B E _ _ _ _ _ ly3 _ (c_fpos cx) (cno_F cx) (cno_sp1 cx) _ _ _ U8 U19 U18 U9 EFa); lia. }
destruct (cno_run_keeps B cx E 0x81380 cno_flag_chunk [] ly3 S3 (c_U cx) W3 (ms_mem ms) _ (ms_mem ms3) (ms_mem ms)
  Hb HARU Hin EF U8 U9 U19 U18 HF) as (KL & KB).
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
lazymatch type of HS with st_ok _ _ ?ss _ => set (ssR := ss) in HS end.
(* the call site *)
assert (R2 : getr (ms_regs ms) 2 = w64 (cno_sp1 cx))
  by (rewrite (cno_reg _ E _ ms 2%bv 2 HS ltac:(vm_compute; reflexivity)); exact C2).
assert (R8 : getr (ms_regs ms) 8 = w64 (cno_sp0 cx))
  by (rewrite (cno_reg _ E _ ms 8%bv 8 HS ltac:(vm_compute; reflexivity)); exact C8).
assert (R9 : getr (ms_regs ms) 9 = w64 (cno_sp1 cx))
  by (rewrite (cno_reg _ E _ ms 9%bv 9 HS ltac:(vm_compute; reflexivity)); exact C9).
assert (R3 : getr (ms_regs ms) 3 = getr (c_regs cx) 3)
  by (rewrite (cno_reg _ E _ ms 3%bv 3 HS ltac:(vm_compute; reflexivity)); exact C3).
assert (R4 : getr (ms_regs ms) 4 = getr (c_regs cx) 4)
  by (rewrite (cno_reg _ E _ ms 4%bv 4 HS ltac:(vm_compute; reflexivity)); exact C4).
assert (R18 : getr (ms_regs ms) 18 = w64 (cno_SF cx))
  by (rewrite (cno_reg _ E _ ms 18%bv 18 HS ltac:(vm_compute; reflexivity)); exact C18).
assert (R19 : getr (ms_regs ms) 19 = w64 (cno_F cx))
  by (rewrite (cno_reg _ E _ ms 19%bv 19 HS ltac:(vm_compute; reflexivity)); exact C19).
assert (R10 : getr (ms_regs ms) 10 = w64 (c_d cx))
  by (rewrite (cno_reg _ E _ ms 10%bv 23 HS ltac:(vm_compute; reflexivity)); exact E23).
assert (R11 : getr (ms_regs ms) 11 = w64 (cno_n cx))
  by (rewrite (cno_reg _ E _ ms 11%bv 22 HS ltac:(vm_compute; reflexivity)); exact E22).
assert (R22 : getr (ms_regs ms) 22 = w64 (cno_n cx))
  by (rewrite (cno_reg _ E _ ms 22%bv 22 HS ltac:(vm_compute; reflexivity)); exact E22).
assert (R23 : getr (ms_regs ms) 23 = w64 (c_d cx))
  by (rewrite (cno_reg _ E _ ms 23%bv 23 HS ltac:(vm_compute; reflexivity)); exact E23).
assert (R24 : getr (ms_regs ms) 24 = w64 SHADOW_OFF)
  by (rewrite (cno_reg _ E _ ms 24%bv 24 HS ltac:(vm_compute; reflexivity)); exact E24).
assert (R25 : getr (ms_regs ms) 25 = w64 (cno_F cx))
  by (rewrite (cno_reg _ E _ ms 25%bv 25 HS ltac:(vm_compute; reflexivity)); exact E25).
assert (R1 : getr (ms_regs ms) 1 = w64 0x81394)
  by exact (fsw_reg_lit (w_H W3) E ssR ms 1%bv 0x81394 HS ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (R12 : getr (ms_regs ms) 12 = w64 66)
  by exact (fsw_reg_lit (w_H W3) E ssR ms 12%bv 66 HS ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (Hsite : cno_site B cx 1 ly3 S3 (c_U cx) W3 (ms_regs ms) (ms_mem ms) md4)
  by exact (cno_site_of B cx E ssR W3 ms 1 ly3 S3 (c_U cx) md4 0x81394 HE U8 HS ltac:(vm_compute; reflexivity) HJ HARU
    Hh R2 R8 R3 R4 R1 ltac:(lia) ltac:(reflexivity)).
destruct (cno_src_kept B cx 1 ly3 S3 W3 (ms_mem ms) md4 Hb HJ HARU) as (Hsrc2 & Hblk2).
assert (Hg2 : fs_glob tfibsegs W3 (ms_mem ms) (c_live cx) (c_peak cx) (c_cnt cx) (c_fail cx)).
{ apply (cno_glob_ledger W3 W3 (ms_mem ms3) (ms_mem ms) _ _ _ _); [|exact Hg].
  intros x Hx. exact (aview_at tfibsegs (w_H W3) (ms_mem ms) (ms_mem ms3) x (KL x Hx)). }
assert (HaIn : In (a, cno_n cx + 18) (ablocks B ly3 S3)) by (rewrite Hab; apply in_or_app; right; left; reflexivity).
assert (Hza : zbytes_at tfibsegs W3 (ms_mem ms) a (pn_copy (c_db cx) 65)).
{ apply (cno_zbytes_kept W3 W3 (ms_mem ms3) (ms_mem ms) a _); [|exact Hz].
  intros j Hj. rewrite (cno_pn_length (c_db cx) 65) in Hj. fold (cno_n cx) in Hj.
  pose proof (req_size_pos (cno_n cx + 18) ltac:(unfold cno_n; lia)) as Hrq.
  exact (aview_at tfibsegs (w_H W3) (ms_mem ms) (ms_mem ms3) (a + j) (KB a (cno_n cx + 18) j HaIn ltac:(lia))). }
assert (Hq1 : quiet (c_cnt cx) (c_fail cx) 1).
{ pose proof Hb as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hq & _). unfold quiet in *. lia. }
assert (Hk1 : 1 + 1 <= EV_check_no_overread) by (unfold EV_check_no_overread; lia).
assert (Hbb1 : blocks_bytes S3 + (cno_n cx + 18) <= LIVE_MAX).
{ pose proof Hb as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hmax & _ & _ & _ & _ & Hbb0).
  rewrite (blocks_bytes_bsum B ly3 S3), Hab, cno_bsum_app, <- (blocks_bytes_bsum B (c_ly cx) (c_S cx)).
  change (bsum [(a, cno_n cx + 18)]) with (cno_n cx + 18 + 0).
  unfold LIVE_check_no_overread, PRESET_FILE_MAX_BYTES, cno_n in *. lia. }
(* the call *)
rewrite (st_ok_restrict_mkst tfibsegs (w_H W3) E ssR ms HS eq_refl).
replace (ss_pc ssR) with A_past_nul by (vm_compute; reflexivity).
change (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 A_past_nul) (ms_mem ms) (seg_rom tfibsegs)) md4)
  with (cfg_at tfibsegs A_past_nul (ms_regs ms) (ms_mem ms) md4).
eapply SRr_bind.
{ exact (cno_call_pn B PN cx 1 ly3 S3 (c_U cx) W3 (ms_regs ms) (ms_mem ms) md4 66 (c_live cx) (c_peak cx) (c_cnt cx)
    (c_fail cx) Hb Hsite (or_intror R1) R10 R11 R12 ltac:(lia) Hsrc2 Hblk2 Hg2 Hq1 Hk1 Hbb1). }
cbv beta. intros W' c' _ (res & Hret).
(* the chunks at the call: the flag word (frame region 1, base 19) and a in the slot 0x18(s1) (slot region 3, base 9) *)
pose (rF := match nth_error (ss_mem ssR) 1 with Some x => x | None => YP09.mkRegion None 0 0 0 0 [] end).
assert (HcF : YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (bv_unsigned (ew E 19))
  (YP09.mkChunk 120 (CVal 8 (SOff 46 0)))).
{ apply (cno_chunk_at E ssR (w_H W3) ms 1 rF 19 _ HS); [vm_compute; reflexivity | vm_compute; reflexivity |].
  cno_inc. }
pose (rL := match nth_error (ss_mem ssR) 3 with Some x => x | None => YP09.mkRegion None 0 0 0 0 [] end).
assert (HcL : YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (bv_unsigned (ew E 9))
  (YP09.mkChunk 24 (CVal 8 (SOff 10 0)))).
{ apply (cno_chunk_at E ssR (w_H W3) ms 3 rL 9 _ HS); [vm_compute; reflexivity | vm_compute; reflexivity |].
  cno_inc. }
rewrite U19 in HcF. rewrite U9 in HcL.
destruct HE as (HE32 & HE33 & HE46 & HE47).
set (xs := fs_extraT ++ cno_extra (c_regs cx) (cno_FL cx) (cno_SF cx) a res 0).
destruct (cno_resume B cx 1 ly3 S3 (c_U cx) W3 (ms_regs ms) (ms_mem ms) md4 1 (c_U cx) (fun _ => False) _ W' c' xs
  cno_flag_chunk cno_sl18 Hb Hsite Hret R9 R18 R19)
  as (ly' & S' & regs' & mem' & md' & Ec & HJ' & HARU' & Hh' & HP & HBK & HZ & HPP & HS').
- intros x _ X. exact X.
- vm_compute. reflexivity.
- intros regs'. apply (proj2 (proj2 (cno_saved_of_st cx E ssR W3 ms (conj HE32 (conj HE33 (conj HE46 HE47))) U8 HS
    ltac:(vm_compute; reflexivity)))).
  intros j Hj. destruct (cno_E_env cx regs' a res 0) as (_ & HX & _). exact (eq_trans (HX j Hj) (eq_sym (HE33 j Hj))).
- constructor; [|apply Forall_nil]. cbn. split; [lia|]. split; [lia|]. intros i _ X. exact X.
- constructor; [|apply Forall_nil]. cbn. split; [lia|]. split; [lia|]. intros i _ X. exact X.
- intros regs' _. constructor; [|apply Forall_nil].
  apply (cno_chunk_env E _ _ _ _ _ _ _ HcF). rewrite !fsw_SOff0.
  destruct (cno_E_env cx regs' a res 0) as (_ & _ & X46 & _). exact (eq_trans X46 (eq_sym HE46)).
- intros regs' _. constructor; [|apply Forall_nil].
  apply (cno_chunk_env E _ _ _ _ _ _ _ HcL). rewrite !fsw_SOff0, E10.
  unfold xs. change 48%nat with (32 + 16)%nat. rewrite ew_Ereg_extra. reflexivity.
- cbv beta in HPP. destruct HPP as (E10' & Hres0 & Hres16 & Hab' & Hzr & Hg').
  assert (Era : raZ (ms_regs ms) = 0x81394) by (unfold raZ; rewrite R1; unfold w64; apply wz; lia).
  rewrite Era in Ec, HS'. subst c'.
  set (E' := Ereg regs' xs) in *.
  assert (KR : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> acallee_saved (bv_unsigned r) ->
    ew E' n = getr (ms_regs ms) r).
  { intros r n Hn' Hc. subst E'. rewrite (ew_Ereg_nat regs' _ n r Hn'). exact (fsw_pres _ _ r HP Hc). }
  apply (HNX cx E' (1 + 1) ly' S' (c_U cx) W' (mkst regs' (Z_to_bv 64 0x81394) mem' (seg_rom tfibsegs)) md' Hb
    (cno_E_env cx regs' a res 0) HJ' HARU').
  + exists a, res. split; [reflexivity|]. split; [reflexivity|].
    split; [cbn [ms_mem mkst]; rewrite Hab', Hab, <- app_assoc; reflexivity|].
    split; [exact Ha0|]. split; [exact Ha16|]. split; [exact Hres0|]. split; [exact Hres16|].
    split; [unfold cno_core; rewrite (KR 2%bv 2%nat eq_refl ltac:(cno_cs)), (KR 8%bv 8%nat eq_refl ltac:(cno_cs)),
      (KR 9%bv 9%nat eq_refl ltac:(cno_cs)), (KR 18%bv 18%nat eq_refl ltac:(cno_cs)),
      (KR 19%bv 19%nat eq_refl ltac:(cno_cs)), (KR 3%bv 3%nat eq_refl ltac:(cno_cs)),
      (KR 4%bv 4%nat eq_refl ltac:(cno_cs)); repeat split; assumption|].
    split; [subst E'; unfold xs; change 48%nat with (32 + 16)%nat; rewrite ew_Ereg_extra; reflexivity|].
    split; [subst E'; rewrite (ew_Ereg_nat regs' _ 10 10%bv eq_refl); exact E10'|].
    split; [rewrite (KR 22%bv 22%nat eq_refl ltac:(cno_cs)); exact R22|].
    split; [rewrite (KR 23%bv 23%nat eq_refl ltac:(cno_cs)); exact R23|].
    split; [rewrite (KR 24%bv 24%nat eq_refl ltac:(cno_cs)); exact R24|].
    split; [rewrite (KR 25%bv 25%nat eq_refl ltac:(cno_cs)); exact R25|].
    split.
    { apply (cno_zbytes_kept W3 W' (ms_mem ms) mem' a _); [|exact Hza].
      intros j Hj. rewrite (cno_pn_length (c_db cx) 65) in Hj. fold (cno_n cx) in Hj.
      pose proof (req_size_pos (cno_n cx + 18) ltac:(unfold cno_n; lia)) as Hrq.
      apply (HBK a (cno_n cx + 18) j HaIn); [rewrite Hab'; apply in_or_app; left; exact HaIn | lia | intros X; exact X]. }
    split; [exact Hzr|]. split; [exact Hg' | exact Hh'].
  + exact HS'.
Qed.

(* ---- from P2: s4 := b (0x81394), a0 := len + 18 (0x81398), the __wrap_malloc call (0x8139c), the return M
   (_inv.v INV_M at ss_M, 0x813a0: t in a0, and [t, t + len + 18) addressable, cno_call_mal_T's B-specific post) ---- *)
Lemma cno_seg_P2 : cno_from B ss_M (INV_M B) -> cno_from B ss_P2 INV_P2.
Proof.
intros HNX cx E k ly3 S3 U3 W3 ms3 md3 Hb HE HJ HARU HINV HS.
destruct HINV as (a & b & -> & -> & Hab & Ha0 & Ha16 & Hb0 & Hb16 & (C2 & C8 & C9 & C18 & C19 & C3 & C4) & E48 & E10
  & E22 & E23 & E24 & E25 & Hza0 & Hzb0 & Hg & Hh).
pose proof (cno_nums B cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5). pose proof cno_stk as FS.
pose proof Hb as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hmax & _ & Hq & _ & _ & Hbb0).
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & Hnevj & _).
assert (Hin : In (1, c_fpos cx) (frames S3)) by (rewrite Hfrs; left; reflexivity).
assert (EF : ly_F ly3 = ly_F (c_ly cx)) by (destruct Hly as (_ & _ & _ & _ & _ & X & _); exact X).
assert (EFa : cno_F cx = frame_addr ly3 1 (c_fpos cx)) by (unfold cno_F, frame_addr; rewrite EF; reflexivity).
pose proof (ARU_AR tfibsegs B ly3 S3 (c_U cx) W3 (ms_mem ms3) md3 HARU) as HAR.
destruct (frames_bounds tfibsegs B LAWS ly3 S3 W3 (unpoison (c_U cx) (ms_mem ms3)) md3 1 (c_fpos cx) HAR Hin)
  as (HF4096 & HFceil & HFapp).
rewrite <- EFa in HF4096, HFceil, HFapp. change (fs_frame_bytes 1) with 128 in HF4096, HFceil, HFapp.
pose proof (shadow_addr_bounds (cno_F cx) ltac:(lia)) as (Hs1 & Hs2).
assert (U8 : bv_unsigned (ew E 8) = cno_sp0 cx) by (rewrite C8; unfold w64; apply wz; lia).
assert (U9 : bv_unsigned (ew E 9) = cno_sp1 cx) by (rewrite C9; unfold w64; apply wz; lia).
assert (U19 : bv_unsigned (ew E 19) = cno_F cx)
  by (rewrite C19; unfold w64; apply wz; unfold in_app, kLowShadowBeg, ASAN_CEIL in HFapp; lia).
assert (U18 : bv_unsigned (ew E 18) = cno_SF cx)
  by (rewrite C18; unfold w64; apply wz; unfold cno_SF, kHighShadowEnd in *; lia).
assert (Hn64 : 0 <= cno_n cx + 18 < 2 ^ 64) by (unfold cno_n, PRESET_FILE_MAX_BYTES in *; lia).
assert (Hn0 : 0 <= cno_n cx < 2 ^ 64) by (unfold cno_n, PRESET_FILE_MAX_BYTES in *; lia).
(* the run 0x81394 -> __wrap_malloc (s4 := b, a0 := len + 18, ra := 0x813a0) *)
fsw_aj_run_toU cno_tbl_ok HS HJ HARU PC_malloc.
{ eapply (cno_awr_ss B E _ _ _ _ _ ly3 _ (c_fpos cx) (cno_F cx) (cno_sp1 cx) _ _ _ U8 U19 U18 U9 EFa); lia. }
destruct (cno_run_keeps B cx E 0x81394 cno_flag_chunk cno_sl18 ly3 S3 (c_U cx) W3 (ms_mem ms) _ (ms_mem ms3) (ms_mem ms)
  Hb HARU Hin EF U8 U9 U19 U18 HF) as (KL & KB).
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
lazymatch type of HS with st_ok _ _ ?ss _ => set (ssR := ss) in HS end.
assert (R2 : getr (ms_regs ms) 2 = w64 (cno_sp1 cx))
  by (rewrite (cno_reg _ E _ ms 2%bv 2 HS ltac:(vm_compute; reflexivity)); exact C2).
assert (R8 : getr (ms_regs ms) 8 = w64 (cno_sp0 cx))
  by (rewrite (cno_reg _ E _ ms 8%bv 8 HS ltac:(vm_compute; reflexivity)); exact C8).
assert (R9 : getr (ms_regs ms) 9 = w64 (cno_sp1 cx))
  by (rewrite (cno_reg _ E _ ms 9%bv 9 HS ltac:(vm_compute; reflexivity)); exact C9).
assert (R3 : getr (ms_regs ms) 3 = getr (c_regs cx) 3)
  by (rewrite (cno_reg _ E _ ms 3%bv 3 HS ltac:(vm_compute; reflexivity)); exact C3).
assert (R4 : getr (ms_regs ms) 4 = getr (c_regs cx) 4)
  by (rewrite (cno_reg _ E _ ms 4%bv 4 HS ltac:(vm_compute; reflexivity)); exact C4).
assert (R18 : getr (ms_regs ms) 18 = w64 (cno_SF cx))
  by (rewrite (cno_reg _ E _ ms 18%bv 18 HS ltac:(vm_compute; reflexivity)); exact C18).
assert (R19 : getr (ms_regs ms) 19 = w64 (cno_F cx))
  by (rewrite (cno_reg _ E _ ms 19%bv 19 HS ltac:(vm_compute; reflexivity)); exact C19).
assert (R10 : getr (ms_regs ms) 10 = w64 (cno_n cx + 18))
  by exact (cno_reg_off _ E _ ms 10%bv 22 18 (cno_n cx) HS ltac:(vm_compute; reflexivity) E22 Hn0 Hn64).
assert (R20 : getr (ms_regs ms) 20 = w64 b)
  by (rewrite (cno_reg _ E _ ms 20%bv 10 HS ltac:(vm_compute; reflexivity)); exact E10).
assert (R22 : getr (ms_regs ms) 22 = w64 (cno_n cx))
  by (rewrite (cno_reg _ E _ ms 22%bv 22 HS ltac:(vm_compute; reflexivity)); exact E22).
assert (R23 : getr (ms_regs ms) 23 = w64 (c_d cx))
  by (rewrite (cno_reg _ E _ ms 23%bv 23 HS ltac:(vm_compute; reflexivity)); exact E23).
assert (R24 : getr (ms_regs ms) 24 = w64 SHADOW_OFF)
  by (rewrite (cno_reg _ E _ ms 24%bv 24 HS ltac:(vm_compute; reflexivity)); exact E24).
assert (R25 : getr (ms_regs ms) 25 = w64 (cno_F cx))
  by (rewrite (cno_reg _ E _ ms 25%bv 25 HS ltac:(vm_compute; reflexivity)); exact E25).
assert (R1 : getr (ms_regs ms) 1 = w64 0x813a0)
  by exact (fsw_reg_lit (w_H W3) E ssR ms 1%bv 0x813a0 HS ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (Hsite : cno_site B cx 2 ly3 S3 (c_U cx) W3 (ms_regs ms) (ms_mem ms) md4)
  by exact (cno_site_of B cx E ssR W3 ms 2 ly3 S3 (c_U cx) md4 0x813a0 HE U8 HS ltac:(vm_compute; reflexivity) HJ HARU
    Hh R2 R8 R3 R4 R1 ltac:(lia) ltac:(reflexivity)).
assert (Hg2 : fs_glob tfibsegs W3 (ms_mem ms) (c_live cx) (c_peak cx) (c_cnt cx) (c_fail cx)).
{ apply (cno_glob_ledger W3 W3 (ms_mem ms3) (ms_mem ms) _ _ _ _); [|exact Hg].
  intros x Hx. exact (aview_at tfibsegs (w_H W3) (ms_mem ms) (ms_mem ms3) x (KL x Hx)). }
assert (HaIn : In (a, cno_n cx + 18) (ablocks B ly3 S3))
  by (rewrite Hab; apply in_or_app; right; left; reflexivity).
assert (HbIn : In (b, cno_n cx + 18) (ablocks B ly3 S3))
  by (rewrite Hab; apply in_or_app; right; right; left; reflexivity).
assert (Hrq : 1 <= req_size (cno_n cx + 18) /\ cno_n cx + 18 <= req_size (cno_n cx + 18))
  by (apply req_size_pos; unfold cno_n; lia).
assert (KZ : forall p c, In (p, cno_n cx + 18) (ablocks B ly3 S3) ->
  zbytes_at tfibsegs W3 (ms_mem ms3) p (pn_copy (c_db cx) c) -> zbytes_at tfibsegs W3 (ms_mem ms) p (pn_copy (c_db cx) c)).
{ intros p c Hp Hzp. apply (cno_zbytes_kept W3 W3 (ms_mem ms3) (ms_mem ms) p _); [|exact Hzp].
  intros j Hj. rewrite (cno_pn_length (c_db cx) c) in Hj. fold (cno_n cx) in Hj.
  exact (aview_at tfibsegs (w_H W3) (ms_mem ms) (ms_mem ms3) (p + j) (KB p (cno_n cx + 18) j Hp ltac:(lia))). }
pose proof (KZ a 65 HaIn Hza0) as Hza. pose proof (KZ b 66 HbIn Hzb0) as Hzb.
assert (Hk1 : 2 + 1 <= EV_check_no_overread) by (unfold EV_check_no_overread; lia).
assert (Hbb1 : blocks_bytes S3 + (cno_n cx + 18) <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly3 S3), Hab, cno_bsum_app, <- (blocks_bytes_bsum B (c_ly cx) (c_S cx)).
  change (bsum [(a, cno_n cx + 18); (b, cno_n cx + 18)]) with (cno_n cx + 18 + (cno_n cx + 18 + 0)).
  unfold LIVE_check_no_overread, PRESET_FILE_MAX_BYTES, cno_n in *. lia. }
(* the call *)
rewrite (st_ok_restrict_mkst tfibsegs (w_H W3) E ssR ms HS eq_refl).
replace (ss_pc ssR) with PC_malloc by (vm_compute; reflexivity).
change (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 PC_malloc) (ms_mem ms) (seg_rom tfibsegs)) md4)
  with (cfg_at tfibsegs PC_malloc (ms_regs ms) (ms_mem ms) md4).
eapply SRr_bind.
{ exact (cno_call_mal cx 2 ly3 S3 (c_U cx) W3 (ms_regs ms) (ms_mem ms) md4 (c_live cx) (c_peak cx) (c_cnt cx) (c_fail cx)
    Hb Hsite R1 R10 Hg2 Hk1 Hbb1). }
cbv beta. intros W' c' _ (t & Hret).
pose (rF := match nth_error (ss_mem ssR) 1 with Some x => x | None => YP09.mkRegion None 0 0 0 0 [] end).
assert (HcF : YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (bv_unsigned (ew E 19))
  (YP09.mkChunk 120 (CVal 8 (SOff 46 0)))).
{ apply (cno_chunk_at E ssR (w_H W3) ms 1 rF 19 _ HS); [vm_compute; reflexivity | vm_compute; reflexivity |].
  cno_inc. }
pose (rL := match nth_error (ss_mem ssR) 3 with Some x => x | None => YP09.mkRegion None 0 0 0 0 [] end).
assert (HcL : YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (bv_unsigned (ew E 9))
  (YP09.mkChunk 24 (CVal 8 (SOff 48 0)))).
{ apply (cno_chunk_at E ssR (w_H W3) ms 3 rL 9 _ HS); [vm_compute; reflexivity | vm_compute; reflexivity |].
  cno_inc. }
rewrite U19 in HcF. rewrite U9 in HcL.
destruct HE as (HE32 & HE33 & HE46 & HE47).
set (xs := fs_extraT ++ cno_extra (c_regs cx) (cno_FL cx) (cno_SF cx) a b t).
destruct (cno_resume B cx 2 ly3 S3 (c_U cx) W3 (ms_regs ms) (ms_mem ms) md4 1 (c_U cx) (fun _ => False) _ W' c' xs
  cno_flag_chunk cno_sl18 Hb Hsite Hret R9 R18 R19)
  as (ly' & S' & regs' & mem' & md' & Ec & HJ' & HARU' & Hh' & HP & HBK & HZ & HPP & HS').
- intros x _ X. exact X.
- vm_compute. reflexivity.
- intros regs'. apply (proj2 (proj2 (cno_saved_of_st cx E ssR W3 ms (conj HE32 (conj HE33 (conj HE46 HE47))) U8 HS
    ltac:(vm_compute; reflexivity)))).
  intros j Hj. destruct (cno_E_env cx regs' a b t) as (_ & HX & _). exact (eq_trans (HX j Hj) (eq_sym (HE33 j Hj))).
- constructor; [|apply Forall_nil]. cbn. split; [lia|]. split; [lia|]. intros i _ X. exact X.
- constructor; [|apply Forall_nil]. cbn. split; [lia|]. split; [lia|]. intros i _ X. exact X.
- intros regs' _. constructor; [|apply Forall_nil].
  apply (cno_chunk_env E _ _ _ _ _ _ _ HcF). rewrite !fsw_SOff0.
  destruct (cno_E_env cx regs' a b t) as (_ & _ & X46 & _). exact (eq_trans X46 (eq_sym HE46)).
- intros regs' _. constructor; [|apply Forall_nil].
  apply (cno_chunk_env E _ _ _ _ _ _ _ HcL). rewrite !fsw_SOff0, E48.
  unfold xs. change 48%nat with (32 + 16)%nat. rewrite ew_Ereg_extra. reflexivity.
- cbv beta in HPP. destruct HPP as (E10' & Ht0 & Hab' & Hrt & Hg').
  assert (Era : raZ (ms_regs ms) = 0x813a0) by (unfold raZ; rewrite R1; unfold w64; apply wz; lia).
  rewrite Era in Ec, HS'. subst c'.
  set (E' := Ereg regs' xs) in *.
  assert (KR : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> acallee_saved (bv_unsigned r) ->
    ew E' n = getr (ms_regs ms) r).
  { intros r n Hn' Hc. subst E'. rewrite (ew_Ereg_nat regs' _ n r Hn'). exact (fsw_pres _ _ r HP Hc). }
  assert (KZ' : forall p c, In (p, cno_n cx + 18) (ablocks B ly3 S3) ->
    zbytes_at tfibsegs W3 (ms_mem ms) p (pn_copy (c_db cx) c) -> zbytes_at tfibsegs W' mem' p (pn_copy (c_db cx) c)).
  { intros p c Hp Hzp. apply (cno_zbytes_kept W3 W' (ms_mem ms) mem' p _); [|exact Hzp].
    intros j Hj. rewrite (cno_pn_length (c_db cx) c) in Hj. fold (cno_n cx) in Hj.
    apply (HBK p (cno_n cx + 18) j Hp); [rewrite Hab'; apply in_or_app; left; exact Hp | lia | intros X; exact X]. }
  apply (HNX cx E' (2 + 1) ly' S' (c_U cx) W' (mkst regs' (Z_to_bv 64 0x813a0) mem' (seg_rom tfibsegs)) md' Hb
    (cno_E_env cx regs' a b t) HJ' HARU').
  + exists a, b, t. split; [reflexivity|]. split; [reflexivity|].
    split; [cbn [ms_mem mkst]; rewrite Hab', Hab, <- app_assoc; reflexivity|].
    split; [exact Ha0|]. split; [exact Ha16|]. split; [exact Hb0|]. split; [exact Hb16|]. split; [exact Ht0|].
    split; [unfold cno_core; rewrite (KR 2%bv 2%nat eq_refl ltac:(cno_cs)), (KR 8%bv 8%nat eq_refl ltac:(cno_cs)),
      (KR 9%bv 9%nat eq_refl ltac:(cno_cs)), (KR 18%bv 18%nat eq_refl ltac:(cno_cs)),
      (KR 19%bv 19%nat eq_refl ltac:(cno_cs)), (KR 3%bv 3%nat eq_refl ltac:(cno_cs)),
      (KR 4%bv 4%nat eq_refl ltac:(cno_cs)); repeat split; assumption|].
    split; [subst E'; unfold xs; change 48%nat with (32 + 16)%nat; rewrite ew_Ereg_extra; reflexivity|].
    split; [subst E'; unfold xs; change 49%nat with (32 + 17)%nat; rewrite ew_Ereg_extra; reflexivity|].
    split; [subst E'; unfold xs; change 50%nat with (32 + 18)%nat; rewrite ew_Ereg_extra; reflexivity|].
    split; [subst E'; rewrite (ew_Ereg_nat regs' _ 10 10%bv eq_refl); exact E10'|].
    split; [rewrite (KR 20%bv 20%nat eq_refl ltac:(cno_cs)); exact R20|].
    split; [rewrite (KR 22%bv 22%nat eq_refl ltac:(cno_cs)); exact R22|].
    split; [rewrite (KR 23%bv 23%nat eq_refl ltac:(cno_cs)); exact R23|].
    split; [rewrite (KR 24%bv 24%nat eq_refl ltac:(cno_cs)); exact R24|].
    split; [rewrite (KR 25%bv 25%nat eq_refl ltac:(cno_cs)); exact R25|].
    split; [exact (KZ' a 65 HaIn Hza)|]. split; [exact (KZ' b 66 HbIn Hzb)|].
    split; [exact Hrt|].
    split; [exact Hg' | exact Hh'].
  + exact HS'.
Qed.

(* ================= the chain: the entry and segment 1, past_nul x2, __wrap_malloc, span M (__asan_memcpy, U1, the
   inline check and store t[len], U2, __asan_memset, U3, the inline check and store t[len + 17], the locals), span D
   (the decodes, the branches, bcmp x2), span F (fuzz_free x3, __wrap_free x3), the epilogue and the ret
   (cno_tail_ret) ================= *)
Lemma cno_chain : segM_T B -> segD_T B -> segF_T B -> check_no_overread_spec tfibsegs B.
Proof.
intros HM HD HF. apply cno_enter, cno_seg_P1, cno_seg_P2, HM, HD, HF.
exact (FSW_check_no_overread_ret.cno_tail_ret B).
Qed.
End T.

(* ================= check_no_overread_ok, at the B image's sink (FSH_Base.fsB_sink_head, passed explicitly) =================
   Section hypotheses: the callee contracts in CTX-free form (past_nul, preset_base64_decode, fuzz_free), the runtime
   contracts (__asan_stack_malloc_1, __wrap_malloc / __wrap_free, __asan_memcpy / __asan_memset, bcmp), the image facts
   and the B-cell equations, as every fs walk takes them; every call step and every span (_segM.v cno_segM, _segD.v
   segD, _segF.v segF) is applied as its real lemma. *)
Section F. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis PN : @past_nul_spec fx rc FSH_Base.fsB_sink_head tfibsegs B.
Hypothesis DEC : @FSH_Fn_writer.decode_spec_ff fx rc FSH_Base.fsB_sink_head B tfibsegs.
Hypothesis FFREE : @fuzz_free_spec fx rc FSH_Base.fsB_sink_head tfibsegs B.
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis HGOT : as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address.
Hypothesis HCELL : as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address.
Hypothesis HGUAR : as_got_uar B = fs_D_GOT_uar.
Hypothesis HUCELL : as_uar_cell B = fs_D_uar_cell.
Hypothesis HSM1 : pc_stack_malloc (as_code B) 1 = PC_stack_malloc_1.
Hypothesis ASM1 : astack_malloc_realizesU tfibsegs B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis FS_ENV : api_env tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : FSupoisonU.amalloc_realizesU tfibsegs B.
Hypothesis HMAL : pc_wrap_malloc (as_code B) = PC_malloc.
Hypothesis AMEMCPY : FSupoisonU.aintrin_realizesU tfibsegs B OCpy PC_memcpy.
Hypothesis AMEMSET : FSupoisonU.aintrin_realizesU tfibsegs B OSet PC_memset.
Hypothesis ABCMP : FSupoisonU.abcmp_realizesU tfibsegs B PC_bcmp.
Hypothesis AFREE : FSupoisonU.afree_realizesU tfibsegs B.
Hypothesis HFRE : pc_wrap_free (as_code B) = PC_free.

Lemma check_no_overread_ok : @check_no_overread_spec fx rc FSH_Base.fsB_sink_head tfibsegs B.
Proof.
apply (@cno_chain fx rc FSH_Base.fsB_sink_head B); try assumption.
all: lazymatch goal with
  | |- cno_call_mal_T _ =>
      eapply (@FSW_check_no_overread_mem.cno_call_mal fx rc FSH_Base.fsB_sink_head B); eassumption
  | |- segM_T _ => eapply (@FSW_check_no_overread_segM.cno_segM fx rc FSH_Base.fsB_sink_head B); eassumption
  | |- segD_T _ => eapply (@FSW_check_no_overread_segD.segD fx rc FSH_Base.fsB_sink_head B); eassumption
  | |- segF_T _ =>
      eapply (@FSW_check_no_overread_segF.segF fx rc FSH_Base.fsB_sink_head B);
      [eapply (@FSW_check_no_overread_ffree.cno_call_ffree fx rc FSH_Base.fsB_sink_head B); eassumption
      | eapply (@FSW_check_no_overread_tail.cno_call_afree fx rc FSH_Base.fsB_sink_head B); eassumption]
  end.
Qed.
End F.

About check_no_overread_ok.
Print Assumptions check_no_overread_ok.
