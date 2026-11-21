(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_type InfPure_w7 InfPure_table InfPure_itab InfPure_cld.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfB_w7base InfB_w6base InfB_w6garm InfB_w7pull.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import U2BKit U2BKit_p04 InfBTraps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac ub_is_trap pc ::= ub_in_traps inf_traps pc.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.
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
  Notation GARM cx ly Lb X := (garm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).

  Definition CLD_RET (cx : ictx) (ly : ilay) (st : ist) (RA rv : Z) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x23 x26 x28 x29 x30 x31 : word) (m : amem) : machine_state :=
    MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly)) (Z_to_bv 64 rv) x11 x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (Z.shiftr (c_p cx + 160) 3 + 2147450880)) x23
            (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x26 (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 (l_F0 ly)) x28 x29 x30 x31)
       FR (Z_to_bv 64 RA) fc None m (seg_rom bsegs).

  Lemma cld_post2 : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x23 x26 x28 x29 x30 x31 : word) (m : amem) (rv B : Z),
    GARM cx ly 0x913a4 LEN_ ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = CODELENS -> IDefs.RNG cx st lf cf -> inf_arr_ok cx wf fo ->
    inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v24 v240 (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    HIDm cx ly m -> KALLB cx ly B ->
    (rv = 0 \/ rv = 1 \/ rv = -1) ->
    (rv = 0 -> sinv cx (st_len_ st) lf cf /\ meas cx (st_len_ st) <= B) ->
    (rv <> 0 -> sinv cx (st_badr st (rv mod 18446744073709551616)) lf cf /\ meas cx (st_badr st (rv mod 18446744073709551616)) < B) ->
    evtF bsegs RNG POST (CLD_RET cx ly st 0x9092c rv x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x23 x26 x28 x29 x30 x31 m).
  Proof.
    intros until B. intros HLEN_ CTX PAYR PLEN MODE RN0 ARR VIS HID KA RET HOK HBAD.
    pose proof KA as (KD & KB & KL & KLV).
    unfold CLD_RET.
    inf_arm_open_rn. subst mode.
    destruct RET as [E|[E|E]]; subst rv.
    -
      destruct (HOK eq_refl) as (SI' & ME'). unfold st_len_ in SI', ME'. icx_cbn.
      Time zrung [0x913a4].
      eapply (HLEN_ (IST LEN_ last flags cin cout hold bits out 0 len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI'| exact ARR| change LEN_ with 16199; inf_vis_close| inf_hid_close
        | eapply KALL_mono; [| split; [exact KD| split; [exact KB| split; [exact KL| exact KLV]]]]; exact ME'].
    -
      destruct (HBAD ltac:(lia)) as (SI' & ME'). change (1 mod 18446744073709551616) with 1 in SI', ME'. unfold st_badr in SI', ME'. icx_cbn.
      Time zrung [0x8e260].
      eapply (KD (IST BAD last flags cin cout hold bits out 1 len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact SI'| exact ME'| exact ARR| change BAD with 16209; inf_vis_close| inf_hid_close].
    -
      destruct (HBAD ltac:(lia)) as (SI' & ME'). change ((-1) mod 18446744073709551616) with 18446744073709551615 in SI', ME'. unfold st_badr in SI', ME'. icx_cbn.
      replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; reflexivity).
      Time zrung [0x8e260].
      eapply (KD (IST BAD last flags cin cout hold bits out 18446744073709551615 len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact SI'| exact ME'| exact ARR| change BAD with 16209; inf_vis_close| inf_hid_close].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Time Qed.
End S.
End CANSEC1.
