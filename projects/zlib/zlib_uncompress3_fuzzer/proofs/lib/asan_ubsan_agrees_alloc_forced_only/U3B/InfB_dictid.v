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
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfAGlue_w7 InfPure InfPure_w7 InfPure_head.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U3B Require Import U2BObj U2BClient U2BIface U2BCall InfBBase InfBKit AdlUBIface InfBEpiK InfB_w7base InfB_head InfB_head2 InfB_dict.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U3B Require Import U2BKit U2BKit_p04 InfBTraps.
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
  Hypothesis ADLN : adler32_null_stmtU.

  Notation KALLB cx ly B := (KALL cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh B).
  Notation HIDm cx ly m := (inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m).
  Notation GARM cx ly Lb X := (garm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).
  Notation KEPI cx ly := (LV_KEPI AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly).

  Lemma dictid_tail : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x1 x5 x6 x7 x10 x11 x14 x15 x16 x17 x19 x21 x22 x23 x26 x28 x29 x30 x31 : word) (m : amem) (cin1 hold1 bits1 : Z),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = DICTID -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v24 v240 v328 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    GARM cx ly 0x8f134 TYPE -> KEPI cx ly ->
    t_cin st <= cin1 <= c_n cx -> 32 <= bits1 <= 40 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
    8 * (c_n cx - cin1) + bits1 = 8 * (c_n cx - t_cin st) + t_bits st ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               x10 x11 (Z_to_bv 64 (c_n cx - cin1)) (Z_to_bv 64 (c_q cx + cin1)) x14 x15 x16 x17
               (Z_to_bv 64 (l_Zs ly)) x19 x21 (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 hold1)
               (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x23 x26 (Z_to_bv 64 (l_F0 ly)) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x8eff4) fc None m (seg_rom bsegs)).
  Proof.
    intros until bits1. intros CTX PAYR PLEN MODE SI ARR VIS HID KA GT KE HC HB HH HBC HW.
    pose proof (flags_not_m1 _ _ _ _ SI ltac:(rewrite MODE; cbv; discriminate) ltac:(rewrite MODE; cbv; discriminate)) as FNM.
    inf_arm_open.
    pose proof (pow2_le_40 bits1 ltac:(lia)) as P40.
    Time zrung [0x8f00c].
    Local Ltac genreg r := let v := reg_val r in let g := fresh "g" in set (g := v); clearbody g.
    (* [U14B] A2 2026-11-12: the byte-swapped hold is written to s7 (x23) at 1.4 (1.3.1 s8 = x24) *)
    zs; genreg 15. zs. zs; genreg 14. zs. zs; genreg 15. zs; genreg 11. zs; genreg 23. zs; genreg 15. zs. zs.
    zs; genreg 11. zs; genreg 11. zs; genreg 11. zs; genreg 11. zs; genreg 15.
    Time zrung [0x8f090].
    assert (MLT : (t_mode (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) <? CHECK) = true)
      by (cbn [t_mode]; rewrite MODE; reflexivity).
    assert (SI' : sinv (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc)
                    (hd_st (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) DICT flags cin1 0 0) lf cf).
    { apply sinv_hd; [exact SI| exact MLT| cbv [HEAD DICTID DICT TYPE TYPEDO STORED CHECK LENGTH DONE BAD]; do 2 right; left; reflexivity| left; reflexivity
                      | intros X; exfalso; apply FNM; exact X| cbn [t_cin c_n]; exact HC| clear; lia| clear; cbn; lia| clear - HB HBC; lia| cbn [t_cin t_bits c_n]; clear - HB HW; lia]. }
    assert (ME' : meas (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc)
                    (hd_st (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) DICT flags cin1 0 0)
                  < meas (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)).
    { apply meas_hd. left. cbn [t_cin t_bits c_n]. clear - HB HW. lia. }
    eapply (dict_body AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh ADLN
              (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
              (hd_st (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) DICT flags cin1 0 0) lf cf wf fo);
      [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI'| exact ARR| unfold hd_st; inf_vis_close| inf_hid_close| eapply KALL_mono; [| exact KA]; lia| exact GT| exact KE].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.
End S.
End CANSEC1.
