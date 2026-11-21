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
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AObj U2AStore InfAGlue InfPure InfPure_type InfPure_w7 InfPure_table.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfB_w7base.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2B Require Import U2BKit U2BKit_p04 InfBTraps InfB_w6base.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
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
  Notation HIDm cx ly m := (inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m).
  Notation GARM cx ly Lb X := (garm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).

  Definition llin_stmtA (cx : ictx) (ly : ilay) : Prop :=
    forall (st : ist) (cs : Z) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
           (x6 x7 x12 x13 x14 x16 x17 x22 x23 x26 x28 x29 x30 x31 : word) (m : amem),
      inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
      t_mode st = LENLENS -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
      inf_vis cx ly (st_cin st cs) lf cf wf fo payload v0 v8 v16 v24 v240 v328 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
      HIDm cx ly m -> KALLB cx ly (meas cx st) ->
      evtF bsegs RNG POST
        (MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (t_bits st)) x6 x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
                 (Z_to_bv 64 (c_p cx + 156)) (Z_to_bv 64 (t_shave st)) x12 x13 x14 (Z_to_bv 64 (c_p cx + 144)) x16 x17
                 (Z_to_bv 64 (l_Zs ly)) x22 (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 2147450880) x23 (Z_to_bv 64 (t_hold st))
                 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x26 (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (l_F0 ly)) x28 x29 x30 x31)
            FR (Z_to_bv 64 0x8f474) fc None m (seg_rom bsegs)).

  Lemma table_tail : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x22 x23 x26 x28 x29 x30 x31 : word) (m : amem) (cin1 hold1 bits1 : Z),
    llin_stmtA cx ly ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = TABLE -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v24 v240 v328 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    t_cin st <= cin1 <= c_n cx -> 14 <= bits1 <= 40 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
    8 * (c_n cx - cin1) + bits1 = 8 * (c_n cx - t_cin st) + t_bits st ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               x10 x11 (Z_to_bv 64 bits1) x13 x14 x15 x16 x17
               (Z_to_bv 64 (l_Zs ly)) x23 (Z_to_bv 64 (c_n cx - cin1)) (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 hold1)
               (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x26 (Z_to_bv 64 (c_q cx + cin1)) (Z_to_bv 64 (l_F0 ly)) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x8f398) fc None m (seg_rom bsegs)).
  Proof.
    intros until bits1. intros HLL CTX PAYR PLEN MODE SI ARR VIS HID (KD & KB & KL) HC HB HH HBC HW.
    inf_arm_open.
    pose proof (pow2_le_40 bits1 ltac:(lia)) as P40.
    assert (HU : 0 <= hold1 < 18446744073709551616) by lia.
    zrung [0x8f3b4]. rewrite land31_mod by lia.
    pose proof (mod_range hold1 32 ltac:(lia)) as RNL. pose proof (mod_range (hold1 / 32) 32 ltac:(lia)) as RND. pose proof (mod_range (hold1 / 1024) 16 ltac:(lia)) as RNC.
    remember (hold1 mod 32) as nl eqn:ENL. remember ((hold1 / 32) mod 32) as nd eqn:END. remember ((hold1 / 1024) mod 16) as nc eqn:ENC.
    zrung [0x8f3e4]. rewrite bits_54_59 by lia. rewrite <- END.
    zrung [0x8f410]. rewrite bits_50_60 by lia. rewrite <- ENC.
    zrung [0x8f420].
    replace (bits1 + -14) with (bits1 - 14) by lia. rewrite (Z.shiftr_div_pow2 hold1 14) by lia.
    Local Ltac table_bad SI MODE HC HB HH HBC HW nc nl nd :=
      lazymatch type of SI with sinv ?cx0 ?st0 ?lf0 ?cf0 =>
        lazymatch type of HH with 0 <= ?h1 < 2 ^ ?b1 => lazymatch type of HC with _ <= ?c1 <= _ =>
          let SI' := fresh "SI'" in let ME' := fresh "ME'" in
          destruct (sinv_tb_bad cx0 st0 lf0 cf0 c1 h1 b1 (nc + 4) (nl + 257) (nd + 1) SI MODE ltac:(icx_cbn; lia) ltac:(icx_cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HBC HW
                      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (SI' & ME');
          unfold st_tb, bad_ofP in SI', ME'; icx_cbn
        end end end.
    zs. zbr0 KNL.
    -
      zrung [0x8e500].
      table_bad SI MODE HC HB HH HBC HW nc nl nd.
      eapply (KD (bad_of (IST mode last flags cin1 cout (hold1 / 2 ^ 14) (bits1 - 14) out ret len offset extra lc dc lb db (nc + 4) (nl + 257) (nd + 1) shave nx whave wnext)) lf cf wf fo);
        [exact SI'| exact ME'| exact ARR| unfold bad_of; change BAD with 16209; inf_vis_close| inf_hid_close].
    - zs. zs. zbr0 KND.
      +
        zrung [0x8e500].
        table_bad SI MODE HC HB HH HBC HW nc nl nd.
        eapply (KD (bad_of (IST mode last flags cin1 cout (hold1 / 2 ^ 14) (bits1 - 14) out ret len offset extra lc dc lb db (nc + 4) (nl + 257) (nd + 1) shave nx whave wnext)) lf cf wf fo);
          [exact SI'| exact ME'| exact ARR| unfold bad_of; change BAD with 16209; inf_vis_close| inf_hid_close].
      +
        zrung [0x8f474].
        lazymatch type of SI with sinv ?cx0 ?st0 ?lf0 ?cf0 =>
          destruct (sinv_tb cx0 st0 lf0 cf0 cin1 hold1 bits1 (nc + 4) (nl + 257) (nd + 1) SI MODE ltac:(icx_cbn; lia) ltac:(icx_cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HBC HW
                      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (SI' & ME') end.
        unfold st_tb in SI', ME'. icx_cbn.
        eapply (HLL (IST LENLENS last flags cin1 cout (hold1 / 2 ^ 14) (bits1 - 14) out ret len offset extra lc dc lb db (nc + 4) (nl + 257) (nd + 1) 0 nx whave wnext) cin lf cf wf fo);
          [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI'| exact ARR| change LENLENS with 16197; inf_vis_close_sn| inf_hid_close| eapply KALL_mono; [| split; [exact KD| split; [exact KB| exact KL]]]; lia].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.

  Lemma table_loop : forall (N : nat) (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x6 x7 x13 x16 x17 x21 x22 x23 x26 x28 x29 x30 x31 : word) (m : amem) (cin1 hold1 bits1 : Z),
    (Z.to_nat (14 - bits1) <= N)%nat ->
    llin_stmtA cx ly ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = TABLE -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v24 v240 v328 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    t_cin st <= cin1 <= c_n cx -> 0 <= bits1 < 14 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
    8 * (c_n cx - cin1) + bits1 = 8 * (c_n cx - t_cin st) + t_bits st ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (t_bits st)) x6 x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 (c_q cx + cin1)) (Z_to_bv 64 bits1) x13 (Z_to_bv 64 (c_q cx + cin1)) (Z_to_bv 64 bits1) x16 x17
               (Z_to_bv 64 (l_Zs ly)) x21 (Z_to_bv 64 (c_n cx - cin1)) (Z_to_bv 64 2147450880) x26 (Z_to_bv 64 hold1)
               (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x22 x23 (Z_to_bv 64 (l_F0 ly)) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x8ed50) fc None m (seg_rom bsegs)).
  Proof.
    induction N as [|N IH]; intros until bits1; intros HN HLL CTX PAYR PLEN MODE SI ARR VIS HID KA HC HB HH HBC HW; [lia|].
    pose proof KA as (KD & KB & KL & KLV).
    inf_arm_open.
    assert (P14 : 2 ^ bits1 <= 16384) by (change 16384 with (2 ^ 14); apply Z.pow_le_mono_r; lia).
    zs. zbr0 KH0.
    2: {
      zrung [0x9366c].
      assert (ECI : cin1 = n) by lia. subst cin1.
      replace ((n - cin) ≪ 3 + bits) with bits1 by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 3) with 8; icx_cbn; lia).
      lazymatch goal with HF : rw_cells bsegs _ SPA _ |- _ =>
        replace (D + cin + (n - cin) mod 4294967296) with (D + n) in HF by (rewrite Z.mod_small by lia; lia) end.
      replace (Z_to_bv 64 0) with (Z_to_bv 64 (n - n)) by (f_equal; lia).
      lazymatch type of SI with sinv ?cx0 ?st0 ?lf0 ?cf0 =>
        destruct (sinv_pull cx0 st0 lf0 cf0 n hold1 bits1 SI ltac:(icx_cbn; lia) ltac:(icx_cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HBC ltac:(icx_cbn; lia)) as (SI' & _) end.
      unfold st_pull in SI'. icx_cbn.
      eapply (KLV (IST mode last flags n cout hold1 bits1 out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ret lf cf wf fo);
        [exact SI'| exact ARR| inf_vis_close| inf_hid_close]. }
    destruct (unp_check_mu bsegs _ _ _ _ _ (D + cin1) 1 UNP MU DJP ltac:(lia) ltac:(lia) ltac:(lia) (mod8_room1 _)) as (b & RDB & CK).
    zrung [0x8ed74].
    zs. rewrite sxb_sval.
    ck_branchJ 17 0x8ed7c CK.
    pose proof (pay_read bsegs _ D payload cin1 PAYB ltac:(lia)) as RDP. fold (bz payload cin1) in RDP.
    pose proof (bz_range payload cin1 PAYR) as BZR.
    zs. zs. cbv beta. rewrite (bz_val payload cin1 PAYR).
    zrung [0x8eda4].
    setreg 23 (Z_to_bv 64 (hold1 + bz payload cin1 * 2 ^ bits1)) ltac:(rewrite pull_hold by lia; reflexivity).
    replace (D + cin1 + 1) with (D + (cin1 + 1)) by lia. replace (n - cin1 + -1) with (n - (cin1 + 1)) by lia.
    pose proof (pullbyte_bound hold1 bits1 (bz payload cin1) ltac:(lia) ltac:(lia) BZR) as PB.
    zs. zbr0 KAG.
    -
      eapply (IH (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (cin1 + 1) (hold1 + bz payload cin1 * 2 ^ bits1) (bits1 + 8));
        [lia| exact HLL| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| | | | | ]; icx_cbn; lia.
    - zs.
      eapply (table_tail (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (cin1 + 1) (hold1 + bz payload cin1 * 2 ^ bits1) (bits1 + 8));
        [exact HLL| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| | | | | ]; icx_cbn; lia.
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.

  Theorem table_garm : forall cx ly, llin_stmtA cx ly -> GARM cx ly 0x8ed30 TABLE.
  Proof.
    intros cx ly HLL. unfold garm_stmtA, GARM_MS. intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA.
    inf_arm_open.
    pose proof (pow2_le_40 bits ltac:(lia)) as P40.
    zs. zs. zbr0 KB14.
    - zrung [0x8f398].
      eapply (table_tail (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cin hold bits);
        [exact HLL| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| | | | | ]; icx_cbn; lia.
    - zrung [0x8ed50].
      eapply (table_loop (Z.to_nat (14 - bits)) (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cin hold bits);
        [lia| exact HLL| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| | | | | ]; icx_cbn; lia.
  Qed.
End S.
End CANSEC1.
