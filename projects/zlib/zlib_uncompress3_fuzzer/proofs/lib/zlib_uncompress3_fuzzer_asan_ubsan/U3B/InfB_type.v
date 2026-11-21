(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_type.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U3B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfB_w7base.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U3B Require Import U2BKit U2BKit_p04 InfBTraps.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load_hyp :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] => match goal with HR : ov_read_bytes segs m a n = Some _ |- _ => rewrite HR end
  end; load_post.
Local Ltac solve_load ::= first [ solve_load_hyp | solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
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
  Notation VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m :=
    (inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m).
  Notation HIDm cx ly m := (inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m).

  Lemma typedo_tail : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x6 x7 x10 x13 x14 x16 x21 x22 x23 x26 x28 x29 x30 x31 : word) (m : amem) (cin1 hold1 bits1 : Z),
    inf_ctx cx ly AI RNG LB -> Z.of_nat (length payload) = c_n cx ->
    (t_mode st = TYPE \/ t_mode st = TYPEDO) -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    t_cin st <= cin1 <= c_n cx -> 3 <= bits1 <= 40 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
    8 * (c_n cx - cin1) + bits1 = 8 * (c_n cx - t_cin st) + t_bits st ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 bits1) x6 x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               (Z_to_bv 64 (c_p cx + 12)) (Z_to_bv 64 (Z.shiftr (c_p cx + 12) 3 + 2147450880)) x10 x13 x14 (Z_to_bv 64 (c_p cx + 8)) x16
               (Z_to_bv 64 (c_n cx - cin1)) (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (c_q cx + cin1)) x22 (Z_to_bv 64 2147450880) x21 (Z_to_bv 64 hold1)
               (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x23 x26 (Z_to_bv 64 (l_F0 ly)) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x8f1f4) fc None m (seg_rom bsegs)).
  Proof.
    intros until bits1. intros CTX PLEN MODE SI ARR VIS HID (KD & KB & KL) HC HB HH HBC HW.
    inf_arm_open.
    pose proof (AI_rtcells AI _ _ _ _ _ AH) as ART. unfold artcells in ART.
    destruct ART as (_ & GOT & RIC & REAL & SHB & _ & INI & LAY & _).
    pose proof (pow2_le_40 bits1 ltac:(lia)) as P40.
    Time zrung [0x8f214].
    setreg 11 (Z_to_bv 64 ((hold1 / 2) mod 4)) ltac:(rewrite bits2_of_shift by lia; reflexivity).
    assert (TY : 0 <= (hold1 / 2) mod 4 < 4) by (Z.div_mod_to_equations; lia).
    set (ty := (hold1 / 2) mod 4) in *. clearbody ty.
    Local Ltac typedo_close KD SI MODE HC HB HH HBC HW ARR m' fx :=
      lazymatch type of SI with sinv ?cx0 ?st0 ?lf0 ?cf0 =>
        let SI' := fresh "SI'" in let ME' := fresh "ME'" in
        destruct (sinv_typedo cx0 st0 lf0 cf0 m' _ _ _ fx SI MODE HC HB HH HBC HW ltac:(tauto) ltac:(split; intros X; first [discriminate | reflexivity | exfalso; cbv in X; lia])) as (SI' & ME');
        lazymatch type of HH with 0 <= ?h1 < 2 ^ ?b1 => lazymatch type of HC with _ <= ?c1 <= _ =>
          replace (b1 + -3) with (b1 - 3) by lia;
          eapply (KD (typedo_st st0 m' c1 h1 b1 fx) lf0 cf0); [exact SI'| exact ME'| exact ARR| inf_vis_close| inf_hid_close] end end
      end.
    zs. zbr0 K1.
    -
      zs. zs. zbr0 K2.
      +
        zrung [0x8e5ec].
        typedo_close KD SI MODE HC HB HH HBC HW ARR BAD false.
      +
        zrung [0x8e5ec].
        typedo_close KD SI MODE HC HB HH HBC HW ARR TABLE false.
    - zs. zbr0 K3.
      +
        zrung [0x8e5ec].
        (* 1.4: TYPE's fixed-block case CALLS inflate_fixed (inlined fixedtables at 1.3.1): carve its 16-byte frame from
           the stack, walk through the callee and back to the dispatch, then give the frame back *)
        destruct (stk_carve bsegs m1 lo SPA 16 STK ltac:(lia)) as [STKc [jfx FRX]].
        replace (SPA - Z.of_nat 16) with (SPA + -16) in FRX, STKc by lia.
        clear STK.
        Time zrung [0x8e5ec].
        pose proof (stk_release _ _ _ _ _ STKc FRX ltac:(lia)) as STK.
        replace (SPA + -16 + Z.of_nat (cells_size _)) with SPA in STK by (cbn; lia).
        clear STKc FRX.
        typedo_close KD SI MODE HC HB HH HBC HW ARR LEN_ true.
      +
        zrung [0x8e5ec].
        typedo_close KD SI MODE HC HB HH HBC HW ARR STORED false.
    Unshelve. all: exact (Z_to_bv 64 0).
  Time Qed.

  Lemma typedo_body : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x6 x7 x10 x11 x12 x13 x14 x16 x19 x21 x22 x23 x26 x28 x29 x30 x31 : word) (m : amem),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    (t_mode st = TYPE \/ t_mode st = TYPEDO) -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    evtF bsegs RNG POST (GARM_MS cx ly gp tp FR fc 0x8f144 st x6 x7 x10 x11 x12 x13 x14 x16 x19 x21 x22 x23 x26 x28 x29 x30 x31 m).
  Proof.
    intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA. unfold GARM_MS.
    pose proof KA as (KD & KB & KL & KLV).
    Time inf_arm_open.
    pose proof (pow2_le_40 bits ltac:(lia)) as P40.
    Time zrung [0x8f160].
    zs. zbr KLAST.
    2: {
      Time zrung [0x8e5ec].
      Time destruct (sinv_bytebits _ _ _ _ SI MODE) as (SI' & ME').
      setreg 5 (Z_to_bv 64 (bits - bits mod 8)) ltac:(rewrite land_m8_64 by lia; reflexivity).
      setreg 23 (Z_to_bv 64 (Z.shiftr hold (bits mod 8))) ltac:(first [rewrite srl_land7 by lia | rewrite srl_land7' by lia]; reflexivity).
      Time eapply (KD (bytebits_st (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)) lf cf wf fo);
        [exact SI'| exact ME'| exact ARR| change CHECK with 16206; inf_vis_close| inf_hid_close]. }
    zs. zs. zbr0 KB2.
    -
      zrung [0x8f1f4].
      eapply (typedo_tail (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cin hold bits);
        [exact CTX0| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| | | | | ]; icx_cbn; lia.
    -
      zs. zbr0 KH0.
      2: {
        zrung [0x93758].
        eapply (KLV (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ret lf cf wf fo);
          [exact SI| exact ARR| exact VISf| exact HID]. }
      destruct (unp_check_mu bsegs _ _ _ _ _ (D + cin) 1 UNP MU DJP ltac:(lia) ltac:(lia) ltac:(lia) (mod8_room1 _)) as (b & RDB & CK).
      zrung [0x8f1c4].
      zs. rewrite sxb_sval.
      Time ck_branchJ 13 0x8f1d0 CK.
      pose proof (pay_read bsegs _ D payload cin PAYB ltac:(lia)) as RDP. fold (bz payload cin) in RDP.
      pose proof (bz_range payload cin PAYR) as BZR.
      zs. cbv beta. rewrite (bz_val payload cin PAYR).
      zrung [0x8f1f4].
      setreg 5 (Z_to_bv 64 (bits + 8)) ltac:(rewrite lor8_small by lia; reflexivity).
      setreg 23 (Z_to_bv 64 (hold + bz payload cin * 2 ^ bits)) ltac:(rewrite pull_hold by lia; reflexivity).
      replace (D + cin + 1) with (D + (cin + 1)) by lia. replace (n - cin + -1) with (n - (cin + 1)) by lia.
      pose proof (pullbyte_bound hold bits (bz payload cin) ltac:(lia) ltac:(lia) BZR) as PB.
      eapply (typedo_tail (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (cin + 1) (hold + bz payload cin * 2 ^ bits) (bits + 8));
        [exact CTX0| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| | | | | ]; icx_cbn; lia.
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.

  Theorem typedo_garm : forall cx ly, garm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh 0x8f144 TYPEDO.
  Proof.
    intros cx ly. unfold garm_stmtA. intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA.
    eapply typedo_body; [exact CTX| exact PAYR| exact PLEN| right; exact MODE| exact SI| exact ARR| exact VIS| exact HID| exact KA].
  Qed.

  Theorem type_garm : forall cx ly, garm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh 0x8f134 TYPE.
  Proof.
    intros cx ly. unfold garm_stmtA, GARM_MS. intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA.
    inf_arm_open.
    zs. zs. zs.
    eapply (typedo_body (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
              (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
      [exact CTX0| exact PAYR| exact PLEN| left; exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA].
  Qed.

  Theorem typedo_arm : forall cx ly, arm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh 0x8f144 TYPEDO.
  Proof. intros cx ly. apply garm_arm. apply typedo_garm. Qed.
  Theorem type_arm : forall cx ly, arm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh 0x8f134 TYPE.
  Proof. intros cx ly. apply garm_arm. apply type_garm. Qed.
End S.
End CANSEC1.
