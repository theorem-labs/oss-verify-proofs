(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_type InfPure_w7 InfPure_table InfPure_itab.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U3B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfB_w7base InfB_w6base.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U3B Require Import U2BKit U2BKit_p04 InfBTraps InfB_w6base InfB_w6garm.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.
Local Ltac ub_is_trap pc ::= ub_in_traps inf_traps pc.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= farr_store_extra m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= farr_call_extra segs W m m' MU WM.

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variable AI : AMallocIface.
  Variables (L : alayout) (RNG : footprint) (stA : astate) (LB : list ablock).
  Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (POST : machine_state -> Prop).
  Variables (LBc : list ablock) (m0 : amem) (payload : list Z) (fw : Z -> Z) (saved fk fksh : list cell).

  Notation KALLB cx ly B := (KALL cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh B).
  Notation HIDm cx ly m := (inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m).
  Notation GARM2 cx ly Lb X := (garm2_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).

  Lemma ll_post : forall (cx : ictx) (ly : ilay) (st : ist) (cs : Z) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 x30 x31 : word) (m : amem) (rv B : Z),
    GARM2 cx ly 0x8f8d8 CODELENS ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LENLENS -> IDefs.RNG cx st lf cf -> inf_arr_ok cx wf fo ->
    inf_vis cx ly (st_cin st cs) lf cf wf fo payload v0 v8 v16 v24 v240 v328 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    HIDm cx ly m -> KALLB cx ly B ->
    (rv = 0 \/ rv = 1 \/ rv = -1) ->
    (rv = 0 -> sinv cx (st_llok st) lf cf /\ meas cx (st_llok st) <= B) ->
    (rv <> 0 -> sinv cx (bad_of (st_ret st (rv mod 18446744073709551616))) lf cf /\ meas cx (bad_of (st_ret st (rv mod 18446744073709551616))) < B) ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 0x8f83c) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly)) (Z_to_bv 64 rv) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (Z.shiftr (c_p cx + 156) 3 + 2147450880)) (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 2147450880)
               (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x26 (Z_to_bv 64 (c_q cx + t_cin st))
               (Z_to_bv 64 (l_F0 ly)) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x8f83c) fc None m (seg_rom bsegs)).
  Proof.
    intros until B. intros HCL CTX PAYR PLEN MODE RN0 ARR VIS HID KA RET HOK HBAD.
    pose proof KA as (KD & KB & KL & KLV).
    inf_arm_open_sn.
    destruct RET as [E|[E|E]]; subst rv.
    -
      destruct (HOK eq_refl) as (SI' & ME'). unfold st_llok in SI', ME'. icx_cbn.
      zrung [0x8f8d8].
      eapply (HCL (IST CODELENS last flags cin cout hold bits out 0 len offset extra lc dc lb db ncode nlen ndist 0 nx whave wnext) lf cf wf fo);
        [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI'| exact ARR| change CODELENS with 16198; inf_vis_close| inf_hid_close
        | eapply KALL_mono; [| split; [exact KD| split; [exact KB| split; [exact KL| exact KLV]]]]; exact ME'].
    -
      destruct (HBAD ltac:(lia)) as (SI' & ME'). change (1 mod 18446744073709551616) with 1 in SI', ME'. unfold st_ret, bad_of in SI', ME'. icx_cbn.
      zrung [0x8e5ec].
      eapply (KD (IST 16209 last flags cin cout hold bits out 1 len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact SI'| exact ME'| exact ARR| inf_vis_close| inf_hid_close].
    -
      destruct (HBAD ltac:(lia)) as (SI' & ME'). change ((-1) mod 18446744073709551616) with 18446744073709551615 in SI', ME'. unfold st_ret, bad_of in SI', ME'. icx_cbn.
      replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; reflexivity).
      zrung [0x8e5ec].
      eapply (KD (IST 16209 last flags cin cout hold bits out 18446744073709551615 len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact SI'| exact ME'| exact ARR| inf_vis_close| inf_hid_close].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.
End S.
End CANSEC1.
