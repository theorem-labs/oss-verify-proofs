(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AShadow U2AKit U2AArr U2AObj U2AStore InfAGlue InfPure InfPure_type InfPure_w7 InfPure_w7d InfAGlue_w7 InfPure_table InfPure_codelens.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfBTables InfB_w7base InfB_w7tab InfB_w7pull InfB_w6base InfB_w6kit InfB_w6garm InfB_cldone_base.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load_hyp :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] => match goal with HR : ov_read_bytes segs m a n = Some _ |- _ => rewrite HR end
  end; load_post.
Local Ltac solve_load ::= first [ solve_load_hyp | solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint_hyp := lazymatch goal with |- acc_in ?R ?x => match goal with HA : acc_in R x |- _ => exact HA end end.
Local Ltac acc_hint ::= first [ acc_hint_hyp | acc_hint_sh ].
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= farr_store_extra m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= farr_call_extra segs W m m' MU WM.


Section CANSEC1. Context {rc : runConstT}.
Definition CLHEAD_MS (cx : ictx) (ly : ilay) (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (st : ist)
    (x6 x10 x11 x13 x14 x19 x21 x23 x26 x29 x30 x31 : word) (m : amem) : machine_state :=
  (MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (c_p cx + 1384)) x6 (Z_to_bv 64 (2 ^ t_lb st - 1)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
           x10 x11 (Z_to_bv 64 (t_lb st)) x13 x14 (Z_to_bv 64 (Z.shiftr (c_p cx + 156) 3 + 2147450880)) (Z_to_bv 64 (t_shave st)) (Z_to_bv 64 (t_nlen st + t_ndist st))
           (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (c_n cx - t_cin st)) x19 (Z_to_bv 64 2147450880) x26 (Z_to_bv 64 (t_hold st))
           (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x23 x21 (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (c_q cx + t_cin st)) x29 x30 x31)
      FR (Z_to_bv 64 0x8f8a8) fc None m (seg_rom bsegs)).

Definition CLRES_MS (cx : ictx) (ly : ilay) (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (st : ist) (cf : Z -> Z) (ci H B : Z)
    (x6 x10 x22 x28 : word) (m : amem) : machine_state :=
  (MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (c_p cx + 1384)) x6 (Z_to_bv 64 (2 ^ t_lb st - 1)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
           x10 (Z_to_bv 64 (c_q cx + ci)) (Z_to_bv 64 (t_lb st)) (Z_to_bv 64 (rdc cf (CDyn 0) (H mod 2 ^ t_lb st)))
           (Z_to_bv 64 (code_bits (rdc cf (CDyn 0) (H mod 2 ^ t_lb st)))) (Z_to_bv 64 (Z.shiftr (c_p cx + 156) 3 + 2147450880)) (Z_to_bv 64 (t_shave st))
           (Z_to_bv 64 (t_nlen st + t_ndist st))
           (* [U14B] A2 2026-11-12: the 1.4 codelens decode allocation (c4 goal of InfB_cldec at 0x8fa30): s3 free, s4 = the
              code word >> 8, s5 = shadow base, s6 = 1, s7 = hold, s8 = shadow(F0), s9 = - bits, s10 = avail_in *)
           (Z_to_bv 64 (l_Zs ly)) x22 (Z_to_bv 64 (Z.shiftr (rdc cf (CDyn 0) (H mod 2 ^ t_lb st)) 8)) (Z_to_bv 64 2147450880) (Z_to_bv 64 1)
           (Z_to_bv 64 H) (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (- B)) (Z_to_bv 64 (c_n cx - ci)) (Z_to_bv 64 (l_F0 ly)) x28 (Z_to_bv 64 B) (Z_to_bv 64 (c_n cx - ci)) (Z_to_bv 64 B))
      FR (Z_to_bv 64 0x8f9f8) fc None m (seg_rom bsegs)).

Section K.
Variables (cx : ictx) (ly : ilay).
Variable AI : AMallocIface.
Variables (L : alayout) (RNG : footprint) (stA : astate) (LB : list ablock).
Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (POST : machine_state -> Prop).
Variables (LBc : list ablock) (m0 : amem) (payload : list Z) (fw : Z -> Z) (saved fk fksh : list cell).

Definition clhead_stmt (N : nat) : Prop :=
  forall (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
         (x6 x10 x11 x13 x14 x19 x21 x23 x26 x29 x30 x31 : word) (m : amem),
    (Z.to_nat (t_nlen st + t_ndist st - t_shave st) <= N)%nat -> t_shave st < t_nlen st + t_ndist st ->
    inf_ctx cx ly AI RNG LB ->
    Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = CODELENS -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    inf_vis cx ly st lf cf wf fo payload v0
            (Z_to_bv 64 (Z.shiftr (c_p cx + 152) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (c_p cx + 148) 3 + 2147450880)) v8 (Z_to_bv 64 (t_nlen st))
            (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m ->
    KALL cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (meas cx st) ->
    evtF bsegs RNG POST (CLHEAD_MS cx ly gp tp FR fc st x6 x10 x11 x13 x14 x19 x21 x23 x26 x29 x30 x31 m).

Definition clres_stmt (N : nat) : Prop :=
  forall (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
         (x6 x10 x22 x28 : word) (m : amem) (ci H B : Z),
    (Z.to_nat (t_nlen st + t_ndist st - t_shave st) <= S N)%nat -> t_shave st < t_nlen st + t_ndist st ->
    inf_ctx cx ly AI RNG LB ->
    Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = CODELENS -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    inf_vis cx ly (st_cin st ci) lf cf wf fo payload v0
            (Z_to_bv 64 (Z.shiftr (c_p cx + 152) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (c_p cx + 148) 3 + 2147450880)) v8 (Z_to_bv 64 (t_nlen st))
            (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m ->
    KALL cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (meas cx st) ->
    t_cin st <= ci <= c_n cx -> B = t_bits st + 8 * (ci - t_cin st) -> 0 <= H < 2 ^ B -> B <= 40 ->
    code_bits (rdc cf (CDyn 0) (H mod 2 ^ t_lb st)) <= B ->
    evtF bsegs RNG POST (CLRES_MS cx ly gp tp FR fc st cf ci H B x6 x10 x22 x28 m).
End K.
End CANSEC1.
