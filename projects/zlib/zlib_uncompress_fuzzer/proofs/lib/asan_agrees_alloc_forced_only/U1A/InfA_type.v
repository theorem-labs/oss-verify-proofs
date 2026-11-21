(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2ABlob U2AStore InfAGlue InfPure InfPure_type.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U1A Require Import U2AObj U2AClient U2AIface InfABase InfAKit InfA_w7base.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
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
  Notation VIS cx ly st lf cf wf fo v0 v8 v16 v240 v504 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m :=
    (inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v240 v504 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m).
  Notation HIDm cx ly m := (inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m).

  (* the 1.4 state at 0x8eae0, read off a probe of typedo_body's two call sites (ZProbe/PgType2,
     reg_val x1..x31): the 1.4 homes (s3 = bits, s4 = hold, s10 = next_in, s11 = avail), a4 = S + 12, a5 = S; frame cells
     v16 / v504 pinned as garm_stmtA pins them, v240 a 1.4 vestige *)
  Lemma typedo_tail : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x5 x6 x12 x13 x16 x17 x22 x23 : word) (m : amem) (cin1 hold1 bits1 : Z),
    inf_ctx cx ly AI RNG LB -> Z.of_nat (length payload) = c_n cx ->
    (t_mode st = TYPE \/ t_mode st = TYPEDO) -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 0) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    t_cin st <= cin1 <= c_n cx -> 3 <= bits1 <= 40 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
    8 * (c_n cx - cin1) + bits1 = 8 * (c_n cx - t_cin st) + t_bits st ->
    evtF asegs RNG POST
      (MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 (Z_to_bv 64 (c_p cx + 56)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (Z.shiftr (c_p cx + 12) 3 + 2147450880)) x12 x13 (Z_to_bv 64 (c_p cx + 12)) (Z_to_bv 64 (c_p cx)) x16 x17
               (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 bits1) (Z_to_bv 64 hold1) (Z_to_bv 64 2147450880)
               x22 x23 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly))
               (Z_to_bv 64 (c_q cx + cin1)) (Z_to_bv 64 (c_n cx - cin1)) (Z_to_bv 64 (c_p cx + 28)) (Z_to_bv 64 (c_osz cx - t_cout st))
               (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880)) (Z_to_bv 64 (c_p cx + 108)))
          FR (Z_to_bv 64 0x8eb30) fc None m (seg_rom asegs)).
  Proof.
    intros until bits1. intros CTX PLEN MODE SI ARR VIS HID (KD & KB & KL) HC HB HH HBC HW.
    inf_arm_open.
    (* the GOT word and the shadow base inflate_fixed loads (0x96684, 0x96688) *)
    pose proof (AI_rtcells AI _ _ _ _ _ AH) as ART. unfold artcells in ART. destruct ART as (_ & RTG & _ & _ & RTS & _).
    pose proof (pow2_le_40 bits1 ltac:(lia)) as P40.
    Time zrunb [0x8eb58].
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
        zrunb [0x8df7c].
        typedo_close KD SI MODE HC HB HH HBC HW ARR BAD false.
      +
        zrunb [0x8df7c].
        typedo_close KD SI MODE HC HB HH HBC HW ARR TABLE false.
    - zs. zbr0 K3.
      +
        (* 1.4 builds the fixed tables in a call to inflate_fixed (0x8f860 jal 0x96678), whose
           16-byte frame (the saved ra) sits just below SPA; then mode = 16209 - 10 from frame slot 472 (0x8f874) *)
        zrunb [0x8df7c; 0x966cc].
        carve_frame 16%nat STK.
        lazymatch goal with H : rw_cells asegs _ (SPA + -16) [CB 16 ?j] |- _ =>
          apply (rw_cells_chop asegs _ (SPA + -16) 16 j (repeat SH8 2)) in H; [| reflexivity];
          cbn [chop chop1 shape_size repeat] in H; chop_names H end.
        zrunb [0x8df7c; 0x8f8b4].
        lazymatch goal with H : rw_cells asegs _ (SPA + -16) _ |- _ => rename H into FRF end.
        release_frame FRF STK SPA.
        zrunb [0x8df7c].
        typedo_close KD SI MODE HC HB HH HBC HW ARR LEN_ true.
      +
        zrunb [0x8df7c].
        typedo_close KD SI MODE HC HB HH HBC HW ARR STORED false.
    (* v240 is a vestige binder at 1.4 *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Time Qed.

  (* stated at the 1.4 TYPEDO entry state, InfA_w7base's GARM_MS (the 1.4 dispatch homes), with the
     frame cells v16 / v504 pinned as garm_stmtA pins them *)
  Lemma typedo_body : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x5 x6 x11 x12 x13 x14 x15 x16 x17 x22 x23 : word) (m : amem),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    (t_mode st = TYPE \/ t_mode st = TYPEDO) -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) v240 (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    evtF asegs RNG POST (GARM_MS cx ly gp tp FR fc 0x8ea9c st x5 x6 x11 x12 x13 x14 x15 x16 x17 x22 x23 m).
  Proof.
    intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA. unfold GARM_MS.
    pose proof KA as (KD & KB & KL & KLV).
    Time inf_arm_open.
    pose proof (pow2_le_40 bits ltac:(lia)) as P40.
    Time zrunb [0x8df7c].
    zbr KLAST.
    2: {
      Time zrunb [0x8df7c].
      Time destruct (sinv_bytebits _ _ _ _ SI MODE) as (SI' & ME').
      setreg 19 (Z_to_bv 64 (bits - bits mod 8)) ltac:(rewrite land_m8_64 by lia; reflexivity).
      setreg 20 (Z_to_bv 64 (Z.shiftr hold (bits mod 8))) ltac:(first [rewrite srl_land7 by lia | rewrite srl_land7' by lia]; reflexivity).
      Time eapply (KD (bytebits_st (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)) lf cf wf fo);
        [exact SI'| exact ME'| exact ARR| change CHECK with 16206; inf_vis_close| inf_hid_close]. }
    zs. zs. zbr0 KB2.
    2: {
      zs. zs. zbr0 KH0.
      2: {
        zs.
        eapply (KL (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
          [exact SI| exact ARR| exact VISf| exact HID]. }
      destruct (unp_check_mu asegs _ _ _ _ _ (D + cin) 1 UNP MU DJP ltac:(lia) ltac:(lia) ltac:(lia) (mod8_room1 _)) as (b & RDB & CK).
      zs. zs. zs. rewrite sxb_sval.
      Time ck_branchJ 13 0x8eb10 CK.
      pose proof (pay_read asegs _ D payload cin PAYB ltac:(lia)) as RDP. fold (bz payload cin) in RDP.
      pose proof (bz_range payload cin PAYR) as BZR.
      zs. cbv beta. rewrite (bz_val payload cin PAYR).
      zrunb [0x8eb30].
      setreg 19 (Z_to_bv 64 (bits + 8)) ltac:(rewrite lor8_small by lia; reflexivity).
      setreg 20 (Z_to_bv 64 (hold + bz payload cin * 2 ^ bits)) ltac:(rewrite pull_hold by lia; reflexivity).
      replace (D + cin + 1) with (D + (cin + 1)) by lia. replace (n - cin + -1) with (n - (cin + 1)) by lia.
      pose proof (pullbyte_bound hold bits (bz payload cin) ltac:(lia) ltac:(lia) BZR) as PB.
      eapply (typedo_tail (ICX u S D n 6335680 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (cin + 1) (hold + bz payload cin * 2 ^ bits) (bits + 8));
        [exact CTX0| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| | | | | ]; icx_cbn; lia. }
    zrunb [0x8eb30].
    eapply (typedo_tail (ICX u S D n 6335680 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cin hold bits);
      [exact CTX0| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| | | | | ]; icx_cbn; lia.
    (* v240 is a vestige binder at 1.4 *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.

  Theorem typedo_garm : forall cx ly, garm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh 0x8ea9c TYPEDO.
  Proof.
    intros cx ly. unfold garm_stmtA, GARM_MS. intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA.
    eapply typedo_body; [exact CTX| exact PAYR| exact PLEN| right; exact MODE| exact SI| exact ARR| exact VIS| exact HID| exact KA].
  Qed.

  Theorem type_garm : forall cx ly, garm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh 0x8ea8c TYPE.
  Proof.
    intros cx ly. unfold garm_stmtA, GARM_MS. intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA.
    inf_arm_open.
    zs. zs. zs.
    eapply (typedo_body (ICX u S D n 6335680 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
              (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
      [exact CTX0| exact PAYR| exact PLEN| left; exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA].
  Qed.

  Theorem typedo_arm : forall cx ly, arm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh 0x8ea9c TYPEDO.
  Proof. intros cx ly. apply garm_arm. apply typedo_garm. Qed.
  Theorem type_arm : forall cx ly, arm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh 0x8ea8c TYPE.
  Proof. intros cx ly. apply garm_arm. apply type_garm. Qed.
End S.
End CANSEC1.
