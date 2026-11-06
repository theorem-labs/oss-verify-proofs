(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YCbo.v, with its module paths and module names changed; 256 of its 314 lines of code are new or changed and 2409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSH_crt_segD2_s39.v, with its module names changed; 50 of its 124 lines of code are new or changed and 240 lines of the source are left out. *)
(* check_round_trip 0x81b9c, fs.asan-ubsan (image tfibsegs = lib/B/YB1v.v), lane D2, SEGMENT 38: the first
   `__wrap_free` thunk. B twin of lib/A/FSH_crt_segD2_s38.v.
   rule 24: proves no function (kind: segment lemma of check_round_trip's walk, PORTED from 6cf61486dca lib/A/FSH_crt_segD2_s38.v)
   rule 24: proves no function (kind: segment lemmas of check_round_trip's walk, PORTED from 1ab57ca7ad7) - RT : CrtRt B,
   crt_fr_free B RT (a working branch 1ab57ca7ad7).
   Port source: a working branch 6cf61486dca proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segD2_s38.v (CTX-free),
   itself PORTED from a working branch d25a984c903 proofs/omx-clap-core/fuzz_state/lib/A/Prog/
   check_round_trip_sd23.v, stage St23 - the same __wrap_free thunk (on fs.asan at 0x82348), freeing the raw interceptor
   block `want`. The function-level lookup is the one quoted in the lane head
   (internal path) (checker a Theorem Labs lane, role check, CONFIRM). Same
   Definition / Lemma names and statement shapes as the A file; every pc, return address, register and slot RE-MEASURED
   on fs.asan-ubsan (capstone over the pinned image, (internal path)) and mapped from A by
   instruction meaning. A new file: no licence lines.

   A name -> A pc -> B pc (names keep their A form, content is B's):
     crt_ss38 (boundary, return of fuzz_free (text))   0x82344 -> 0x824a4
     crtD2_ss38c (call site, pc PC_free)                0x53070 -> 0x530e0 (__wrap_free), ra 0x8234c -> ra 0x824ac
     crt_ss39 (boundary, return of free (want))         0x8234c -> 0x824ac
     a0 at the call                                     A `ld a0, 0x38(s1)` (want's slot on A) -> B `ld a0, 0x30(s1)`
                                                        (want's slot on B, crt_cs1's chunk 0x30); atom 49 on both

   The code (MEASURED, crt_tbl): 0x824a4 `ld a0, 0x30(s1)` (the s1 slot 0x30 holds want, atom 49) and 0x824a8
   `jal __wrap_free` (PC_free 0x530e0), returning to 0x824ac (crt_ss39).
   What St23 proves, restated in S0's ajournal / ARU / U form: the block freed is (want, enc_size len), the FIRST raw
   __wrap_malloc block (the malloc returning to 0x81da4), which owns no user-poisoned head, so U (a permutation of c_U,
   crtD2_INV_38) has no range in it (crtD2_no_head with the entry heads naming entry blocks, + crtD2_free_outside); the
   free keeps U, the fake frame, the real stack, `same` (still live) and fuzz/alloc.c's statics, and is crossed with the
   base's crt_seg_call over the free's own callee journal (FSH_crt_segD2_s39.crtD2_free_sub). No trace premise is taken
   (see FSH_crt_segD2_s39.v's header). B only: s3 = F (crtD2_INV_39's register conjunct, for crt_INV_T) is
   callee-saved, read off the call-site register s3 = atom 19. The read-only view after the call is the site's crt_rom
   (the A file used s39's local copy crtD2_rom, not carried on B). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP03 YP0l YP0k YP06 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG08 YG0d YG05 YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import SetShadowDefU FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
FSH_Base FSH_Rt FSPstat FSW_K FSW_rres FSW_ret FSW_frame FSW_frame3 FSW_K3 FSW_crt_tbl FSH_Fn_reader FSH_Fn_writer
FSH_Fn_alloc FSH_Fn_crt FSH_crt_base FSH_crt_site FSH_crt_segD FSH_crt_segD2 FSH_crt_segD2_s39.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec HState PjStruct.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the call-site state of segment 38, MEASURED by the engine from crt_ss2 0x824a4: `ld a0, 0x30(s1)` then
   `jal __wrap_free`, no store; a0 = atom 49 (want), ra = 0x824ac, s8 still atom 24 (same), s3 atom 19 (F) *)
Definition crtD2_ss38c : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL PC_free (crt_ss2 0x824a4)).
Lemma crtD2_seg38c_run : sym_run_toN tfibsegs crt_tbl FUEL PC_free (crt_ss2 0x824a4) = (crtD2_ss38c, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtD2_ss38c_site : crt_csite crtD2_ss38c PC_free 0x824ac.
Proof. unfold crt_csite. repeat split; vm_compute; reflexivity. Qed.
Lemma crtD2_ss38c_regs : sr_get (ss_regs crtD2_ss38c) 10%bv = SOff 49 0 /\ sr_get (ss_regs crtD2_ss38c) 24%bv = SOff 24 0 /\
  sr_get (ss_regs crtD2_ss38c) 19%bv = SOff 19 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

Section s38. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis RT : CrtRt B.
Hypothesis HENV : api_env tfibsegs B.
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* the free of `want`: from crtD2_INV_38 at the call, the callee half of the free, and crtD2_INV_39 after it *)
Lemma crtD2_hcall38 : crt_hcall SK B crtD2_ss38c PC_free 0x824ac ASTACK (crtD2_INV_38 B) (crtD2_INV_39 B).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 regsC memC mdC HB HE HINV HJ HARU Hfr HSB RG HPRE HFRL HTOP.
destruct HINV as (E19 & same & nsame & peak & cnt & E24 & HBL & HHD & HFH & HGL & HRV & Hcnt & Hk).
unfold crtD2_blocks, crtD2_heads in HBL, HHD. rewrite app_nil_r in HHD.
set (en := FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx)))) in *.
pose proof (crt_fr_free B RT) as (EPC & AFREE).
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARU) as HAR.
pose proof HB as (_ & HFH0 & _).
destruct crtD2_ss38c_regs as (G10 & G24 & G19).
assert (R10 : YK11.getr regsC 10%bv = Z_to_bv 64 (c_want cx))
  by (rewrite RG, G10, fsw_SOff0; exact (crt_E_want cx E HE)).
(* the block, its absence from the entry, and U outside it *)
assert (Hin : In (c_want cx, en) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HBL)). apply in_or_app. right. left. reflexivity. }
assert (Hnin0 : ~ In (c_want cx, en) (ablocks B (c_ly cx) (c_S cx))).
{ intros X. apply (crtD2_once B ly3 S3 W3 _ mdC (ablocks B (c_ly cx) (c_S cx)) [(same, nsame)] (c_want cx, en) HAR HBL).
  apply in_or_app. left. exact X. }
assert (Hnot : ~ In (c_want cx, 16) U3).
{ apply (crtD2_no_head B ly3 S3 W3 _ mdC U3 (c_U cx) (ablocks B (c_ly cx) (c_S cx)) [(same, nsame)] (c_want cx) en
    HAR HFH HBL HHD).
  intros q Hq. destruct (crtD2_head_of_U B (c_ly cx) (c_S cx) (c_U cx) q HFH0 Hq) as (m & Hm & _).
  exists m. apply in_or_app. left. exact Hm. }
pose proof (crtD2_free_outside B ly3 S3 U3 W3 memC mdC (c_want cx) en HARU HFH Hin Hnot) as Hout.
destruct (al_blocks _ _ LAWS ly3 S3 W3 _ mdC (c_want cx) en HAR Hin) as (_ & Hw4096 & _).
(* the callee's precondition *)
assert (Hev : st_nev S3 < EV_MAX)
  by (apply (crtD2_nev SK B cx k ly3 S3 W3 _ mdC (2 * CRT_EV_WRAP) HB HJ); [unfold CRT_EV_WRAP; lia | exact Hk]).
destruct (crtD2_acall_preU B ly3 S3 U3 W3 regsC memC mdC (crt_ch1 cx) HPRE Hev) as (HPREU & HstkC).
exists [(c_want cx, c_want cx + req_size en)], 1. eexists.
split.
{ change (cfg_at tfibsegs PC_free regsC memC mdC)
    with (mkCfg (mkst regsC (Z_to_bv 64 PC_free) memC (seg_rom tfibsegs)) mdC).
  rewrite <- EPC.
  exact (crtD2_free_sub SK B HENV ML AFREE ly3 S3 U3 W3 regsC memC mdC (c_want cx) en (YK11.getr regsC 1%bv)
    (crt_ch1 cx) HPREU HstkC Hev Hin Hout R10 eq_refl). }
split.
{ (* the footprint is a block the walk made: in_tmp_block *)
  intros a (rg & [<-|[]] & Ha). cbn [fst snd] in Ha. right. left.
  exists (c_want cx), en. split; [exact Hin|]. split; [exact Hnin0 | exact Ha]. }
split.
{ (* the flag word is a frame byte, apart from every block *)
  intros a Ha (rg & [<-|[]] & Ha'). cbn [fst snd] in Ha'.
  pose proof HJ as (_ & Hly & _).
  pose proof (crt_F_ly cx _ ly3 Hly) as EF.
  assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
  pose proof (sep_block_frame tfibsegs B LAWS ly3 S3 W3 _ mdC (c_want cx) en 3 (c_pos cx) HAR Hin Hin3) as D.
  rewrite EF, crt_frame3 in D. rewrite crt_frame3 in Ha. unfold zdisjoint in D. cbn [fst snd] in D. lia. }
intros W' c' (ly2 & S2 & regs2 & mem2 & md2 & -> & HJc & OK2 & PO2 & HP & (l1 & l2 & Esp & E2)).
exists ly2, S2, U3, regs2, mem2, md2.
split; [reflexivity|]. split; [exact HJc|]. split; [exact OK2|]. split; [exact PO2|]. split; [exact HP|].
intros HJ' HARU'.
unfold crtD2_INV_39. cbn [ms_regs ms_mem mkst].
split.
{ (* s3 is callee-saved: still F *)
  rewrite (ew_Ereg_nat regs2 (crt_extra cx) 19 19%bv eq_refl).
  transitivity (YK11.getr regsC 19%bv); [exact (HP 19 ltac:(unfold acallee_saved; lia))|].
  rewrite RG, G19, fsw_SOff0. exact E19. }
exists same, nsame, peak, cnt.
split.
{ (* s8 is callee-saved: still same *)
  rewrite (ew_Ereg_nat regs2 (crt_extra cx) 24 24%bv eq_refl).
  transitivity (YK11.getr regsC 24%bv); [exact (HP 24 ltac:(unfold acallee_saved; lia))|].
  rewrite RG, G24, fsw_SOff0. exact E24. }
split.
{ unfold crtD2_blocks. rewrite E2. rewrite Esp in HBL. exact (Permutation_app_inv _ _ _ _ _ HBL). }
split; [unfold crtD2_heads; rewrite app_nil_r; exact HHD|].
split; [exact (crtD2_heads_free B ly3 S3 ly2 S2 U3 l1 l2 (c_want cx) en HFH Hnot Esp E2)|].
split.
{ apply (crtD2_glob_call SK B IMG ly3 S3 U3 W3 (ms_mem ms3) memC mdC ly2 S2 U3 W' mem2 md2 ASTACK (spZ regsC)
    [(c_want cx, c_want cx + req_size en)] 1 _ _ _ _ HARU HARU' HJc HSB); [| | exact HGL].
  - intros a Hi (rg & [<-|[]] & Ha). cbn [fst snd] in Ha.
    exact (blk_img tfibsegs B LAWS ly3 S3 W3 _ mdC (c_want cx) en a HAR Hin Ha Hi).
  - apply sink_closed_pos. constructor; [cbn [fst]; lia | constructor]. }
split; [exact (crt_rom SK B IMG cx (k + 1) ly2 S2 U3 W' mem2 md2 HB HJ' HARU')|].
split; [exact Hcnt|].
unfold CRT_EV_WRAP in *. lia.
Qed.

(* ---- segment 38: crt_from at 0x824ac under crtD2_INV_39 gives crt_from at 0x824a4 under crtD2_INV_38 ---- *)
Lemma crtD2_seg38 : crt_from SK B crt_ss39 (crtD2_INV_39 B) -> crt_from SK B crt_ss38 (crtD2_INV_38 B).
Proof.
intros NEXT.
exact (crt_seg_call SK B 0x824a4 PC_free 0x824ac crtD2_ss38c (crtD2_INV_38 B) (crtD2_INV_39 B) ASTACK
  crtD2_seg38c_run crtD2_ss38c_site ltac:(lia) ltac:(reflexivity) (proj2 (proj2 crtD2_stk_pos)) crtD2_stk_free
  crtD2_hcall38 NEXT).
Qed.
End s38.
