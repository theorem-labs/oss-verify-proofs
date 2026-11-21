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
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit I_asan_memcpy.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_type InfPure_w7 InfPure_stored InfPure_check U2ABlob UwAKit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U3B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfBGlue_p04 U2BCall U2BGlue AdlUBIface InfBAdlCall_p04 InfB_length.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U3B Require Import U2BKit U2BKit_p04.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Common Require Import RunDraw.
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

  Lemma check_cmp : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x5 x6 x7 x10 x11 x12 x13 x16 x17 x23 x26 x28 x29 x30 x31 : word) (m : amem) (cin1 hold1 bits1 : Z),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = CHECK -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m ->
    KALLB cx ly (meas cx st) ->
    t_cin st <= cin1 <= c_n cx -> 32 <= bits1 <= 40 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
    8 * (c_n cx - cin1) + bits1 <= 8 * (c_n cx - t_cin st) + t_bits st ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly)) x10 x11 x12 (Z_to_bv 64 (c_p cx + 28))
               x13 (Z_to_bv 64 (c_p cx + 8)) x16 x17
               (Z_to_bv 64 (l_Zs ly)) x23 (Z_to_bv 64 (c_n cx - cin1)) (Z_to_bv 64 2147450880) x26 (Z_to_bv 64 hold1)
               (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 bits1) (Z_to_bv 64 (c_q cx + cin1)) (Z_to_bv 64 (l_F0 ly)) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x909a0) fc None m (seg_rom bsegs)).
  Proof.
    intros until bits1. intros CTX PAYR PLEN MODE SI ARR VIS HID KA HC HB HH HBC HW.
    pose proof KA as (KD & KB & KL & KLV).
    pose proof (flags_not_m1 _ _ _ _ SI ltac:(rewrite MODE; cbv; discriminate) ltac:(rewrite MODE; cbv; discriminate)) as HFL.
    inf_arm_open. subst mode.
    assert (F0E : flags = 0) by (destruct R13 as [X|X]; [exact X| exfalso; exact (HFL X)]). clear R13. subst flags.
    assert (P40 : 2 ^ bits1 <= 2 ^ 40) by (apply Z.pow_le_mono_r; lia). change (2 ^ 40) with 1099511627776 in P40.
    zrung [0x909cc].
    lazymatch goal with |- context [bv_swrap 32 ?e] =>
      assert (SW24 : 0 <= e < 256)
        by (unfold bv_wrap, bv_modulus; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ Z.of_N 32) with 4294967296; change (2 ^ 24) with 16777216;
            pose proof (Z.mod_pos_bound hold1 4294967296 ltac:(lia)); Z.div_mod_to_equations; lia);
      rewrite (swrap32_small e) by lia end.
    zrung [0x90a14].
    zs. zbr KNE.
    -
      zrung [0x8e5ec].
      assert (SIB : sinv (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc)
                       (ck_st (IST CHECK last 0 cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) BAD cin1 hold1 bits1 (osz - cout)) lf cf).
      { apply sinv_ck; [exact SI| reflexivity| right; right; right; reflexivity| icx_cbn; lia| lia| lia| lia| icx_cbn; lia| right; split; [reflexivity| cbv; reflexivity]]. }
      assert (MEB : meas (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc)
                       (ck_st (IST CHECK last 0 cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) BAD cin1 hold1 bits1 (osz - cout))
                  < meas (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) (IST CHECK last 0 cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)).
      { apply meas_ck. right. split; [icx_cbn; lia| vm_compute; reflexivity]. }
      eapply (KD (ck_st (IST CHECK last 0 cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) BAD cin1 hold1 bits1 (osz - cout)) lf cf wf fo);
        [exact SIB| exact MEB| exact ARR| change BAD with 16209; unfold ck_st; inf_vis_close| inf_hid_close].
    -
      zrung [0x90a4c].
      assert (SIL : sinv (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc)
                       (ck_st (IST CHECK last 0 cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) LENGTH cin1 0 0 (osz - cout)) lf cf).
      { apply sinv_ck; [exact SI| reflexivity| right; left; reflexivity| icx_cbn; lia| lia| change (2 ^ 0) with 1; lia| lia| icx_cbn; lia| right; split; [reflexivity| cbv; reflexivity]]. }
      assert (MEL : meas (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc)
                       (ck_st (IST CHECK last 0 cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) LENGTH cin1 0 0 (osz - cout))
                  < meas (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) (IST CHECK last 0 cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)).
      { apply meas_ck. right. split; [icx_cbn; lia| vm_compute; reflexivity]. }
      pose proof (length_body AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
                    (ck_st (IST CHECK last 0 cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) LENGTH cin1 0 0 (osz - cout)) lf cf wf fo) as LBD.
      unfold ck_st in LBD, MEL. cbn [c_u c_p c_q c_n c_ob c_osz c_w l_SP l_SPA l_Zs l_F0 l_lo t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
                                 t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in LBD, MEL.
      eapply LBD; [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SIL| exact ARR| change LENGTH with 16207; inf_vis_close| inf_hid_close|].
      eapply KALL_mono; [| exact KA]. apply Z.lt_le_incl. exact MEL.
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.
End S.
End CANSEC1.
