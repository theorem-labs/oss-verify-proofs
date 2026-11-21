(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AObj U2AStore InfAGlue InfPure InfPure_w7 InfPure_w7d InfPure_w7e InfPure_w7f InfPure_w7h InfAGlue_w7 InfAGlue_w7b.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfBTables InfB_w7base InfB_w7tab InfB_w7tab16 InfB_w7pull.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2B Require Import U2BKit U2BKit_p04 InfBTraps.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= farr_store_extra m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= farr_call_extra segs W m m' MU WM.
Local Ltac ub_is_trap pc ::= ub_in_traps inf_traps pc.


Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variable AI : AMallocIface.
  Variables (L : alayout) (RNG : footprint) (stA : astate) (LB : list ablock).
  Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (POST : machine_state -> Prop).
  Variables (LBc : list ablock) (m0 : amem) (payload : list Z) (fw : Z -> Z) (saved fk fksh : list cell).

  Notation KALLB cx ly B := (KALL cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh B).
  Notation VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m :=
    (inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m).
  Notation HIDm cx ly m := (inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m).
  Notation GARM cx ly Lb X := (garm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).

  Definition DX_STMT (cx : ictx) (ly : ilay) : Prop :=
    forall (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x6 x7 x10 x11 x13 x14 x15 x16 x19 x21 x22 x23 x26 x28 x29 x30 x31 : word) (m : amem),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = DISTEXT -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (t_bits st)) x6 x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly)) x10 x11
               (Z_to_bv 64 (t_extra st)) x13 x14 x15 x16 (Z_to_bv 64 (c_n cx - t_cin st))
               (Z_to_bv 64 (l_Zs ly)) x19 x21 (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 (t_hold st))
               (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x23 x26 (Z_to_bv 64 (l_F0 ly)) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x920e8) fc None m (seg_rom bsegs)).

  Lemma d_term : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits was pad : word)
      (x5 x6 x7 x10 x11 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word) (m : amem) (c bk : Z),
    DX_STMT cx ly ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = DIST -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits (Z_to_bv 64 bk) was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    0 <= c < 4294967296 -> 0 <= code_bits c <= t_bits st -> code_bits c <= 15 -> 0 <= bk <= 64 ->
    ((16 <= code_op c <= 29 /\ 1 <= code_val c /\ code_val c + 2 ^ (code_op c - 16) - 1 <= 32768) \/ Z.land (code_op c) 64 <> 0) ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly)) x10 x11
               (Z_to_bv 64 c) (Z_to_bv 64 (code_op c)) (Z_to_bv 64 (t_bits st)) x15 x16 x17
               (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (c_n cx - t_cin st)) x21 (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 (t_hold st))
               (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (code_bits c)) (Z_to_bv 64 (Z.shiftr c 8)) (Z_to_bv 64 (l_F0 ly)) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x92030) fc None m (seg_rom bsegs)).
  Proof.
    intros until bk. intros HDX CTX PAYR PLEN MODE SI ARR VIS HID KA HCR HHB HB15 HBK HTERM.
    pose proof KA as (KD & KB & KL & KLV).
    pose proof (sinv_bits_facts _ _ _ _ SI) as (CIN0 & CINN & BITS0 & BLE & HOLD0).
    pose proof (code_op_range c) as OPR. pose proof (code_val_range c) as VALR.
    pose proof (cw_land192 c ltac:(lia)) as L192. pose proof (cw_mod64 c ltac:(lia)) as M64.
    set (hb := code_bits c) in *.
    inf_arm_open.
    pose proof (pow2_le_40 bits ltac:(lia)) as P40.
    pose proof (drop_bound hold bits hb ltac:(lia) ltac:(lia)) as DB.
    destruct (sinv_pull _ _ lf cf cin (hold / 2 ^ hb) (bits - hb) SI ltac:(icx_cbn; lia) ltac:(icx_cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(icx_cbn; lia) ltac:(icx_cbn; lia)) as (SI1 & ME1).
    zs. rewrite L192.
    zrung [0x92064].
    zrung [0x92070].
    zs. rewrite M64. rewrite (Z.shiftr_div_pow2 hold hb) by lia.
    zs.
    zrung [0x92084].
    zs. zbr0 KI.
    -
      zrung [0x8e500].
      pose proof (sinv_bad_ofP _ _ lf cf SI1) as SIB.
      pose proof (meas_bad_ofP (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc) (st_pull (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cin (hold / 2 ^ hb) (bits - hb))) as MEB.
      st_norm SI1. st_norm ME1. unfold bad_ofP in SIB, MEB. st_norm SIB. st_norm MEB. subst mode. change (rank DIST) with 16 in *.
      eapply (KD (IST BAD last flags cin cout (hold / 2 ^ hb) (bits - hb) out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact SIB| clear - ME1 MEB HHB; unfold meas, Wm in *; icx_cbn; lia| exact ARR| change BAD with 16209; inf_vis_close| inf_hid_close].
    -
      destruct HTERM as [(OP1 & VAL1 & VAL2)|BADOP]; [| exfalso; lia].
      pose proof (op_land15 (code_op c) OP1) as L15.
      zrung [0x920e8].
      rewrite L15 in *. rewrite (code_word_val c HCR) in *.
      set (val := code_val c) in *. set (op := code_op c) in *.
      destruct (sinv_to_distext _ _ lf cf val (op - 16) SI1 MODE ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (SI2 & ME2).
      st_norm SI1. st_norm ME1. st_norm SI2. st_norm ME2.
      eapply (HDX (IST DISTEXT last flags cin cout (hold / 2 ^ hb) (bits - hb) out ret len val (op - 16) lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI2| exact ARR| change DISTEXT with 16203; inf_vis_close| inf_hid_close| eapply KALL_mono; [| exact KA]; lia].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder of KDISP / DX_STMT at 1.4 (InfBBase's inf_locals no longer holds it) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Time Qed.
End S.
End CANSEC1.
