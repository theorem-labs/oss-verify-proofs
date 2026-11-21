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
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U3B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfBGlue_p04 U2BCall U2BGlue AdlUBIface InfBAdlCall_p04 InfB_length InfB_checkm.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U3B Require Import U2BKit U2BKit_p04.
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
  Hypothesis ADL : adler32_stmtU.

  Lemma check_loop : forall (k : nat) (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x7 x10 x12 x16 x17 x22 x23 x28 x29 x30 x31 : word) (m : amem) (cinj holdj j j0 : Z),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = CHECK -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m ->
    KALLB cx ly (meas cx st) ->
    32 - 8 * Z.of_nat k <= j < 40 - 8 * Z.of_nat k -> (1 <= k <= 4)%nat -> 0 <= j0 -> j - j0 = 8 * (cinj - t_cin st) ->
    t_cin st <= cinj <= c_n cx -> 0 <= holdj < 2 ^ j -> j <= 8 * cinj ->
    8 * (c_n cx - cinj) + j <= 8 * (c_n cx - t_cin st) + t_bits st ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 j0) x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               x10 (Z_to_bv 64 (c_q cx + cinj)) x12 (Z_to_bv 64 5) (Z_to_bv 64 (c_q cx + cinj)) (Z_to_bv 64 j) x16 x17
               (Z_to_bv 64 (l_Zs ly)) x23 (Z_to_bv 64 (c_n cx - cinj)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr (c_p cx + 16) 3 + 2147450880)) (Z_to_bv 64 holdj)
               (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 j) x22 (Z_to_bv 64 (l_F0 ly)) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x8eef0) fc None m (seg_rom bsegs)).
  Proof.
    induction k as [|k IH]; intros until j0; intros CTX PAYR PLEN MODE SI ARR VIS HID KA EJ HK J00 EJ0 HC HH HBC HW; [exfalso; lia|].
    pose proof KA as (KD & KB & KL & KLV).
    pose proof (flags_not_m1 _ _ _ _ SI ltac:(rewrite MODE; cbv; discriminate) ltac:(rewrite MODE; cbv; discriminate)) as HFL.
    inf_arm_open. subst mode.
    assert (F0E : flags = 0) by (destruct R13 as [X|X]; [exact X| exfalso; exact (HFL X)]). clear R13. subst flags.
    assert (J31 : 0 <= j <= 31) by lia.
    assert (P32 : 2 ^ j <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia). change (2 ^ 31) with 2147483648 in P32.
    assert (SIS : sinv (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc)
                       (ck_st (IST CHECK last 0 cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) CHECK cinj holdj j out) lf cf).
    { apply sinv_ck; [exact SI| reflexivity| left; reflexivity| icx_cbn; lia| lia| lia| lia| icx_cbn; lia| left; split; [reflexivity| intros X; exact X]]. }
    zs. zbr KH0.
    2: {
      zrung [0x93750].
      assert (ECN : cinj = n) by lia.
      replace (Z.shiftl (n - cin) 3 + j0) with j by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 3) with 8; lia).
      replace (D + cin + (n - cin) mod 4294967296) with (D + cinj) in * by (rewrite Z.mod_small by lia; lia).
      eapply (KL (ck_st (IST CHECK last 0 cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) CHECK cinj holdj j out) lf cf wf fo);
        [exact SIS| exact ARR| exact ECN| unfold ck_st; inf_vis_close| inf_hid_close]. }
    zrung [0x8ef0c].
    destruct (unp_check_mu bsegs _ _ _ _ _ (D + cinj) 1 UNP MU DJP ltac:(lia) ltac:(lia) ltac:(lia) (mod8_room1 _)) as (b & RDB & CK).
    zs. zs. zs. rewrite sxb_sval.
    ck_branchJ 10 0x8ef1c CK.
    pose proof (pay_read bsegs _ D payload cinj PAYB ltac:(lia)) as RDP. fold (bz payload cinj) in RDP.
    pose proof (bz_range payload cinj PAYR) as BZR.
    zs. zs. cbv beta. rewrite (bz_val payload cinj PAYR).
    zrung [0x8ef44].

    setreg 23 (Z_to_bv 64 (holdj + bz payload cinj * 2 ^ j)) ltac:(rewrite pull_hold by lia; reflexivity).
    replace (n - cinj + -1) with (n - (cinj + 1)) by lia. replace (D + cinj + 1) with (D + (cinj + 1)) by lia.
    pose proof (pullbyte_bound holdj j (bz payload cinj) ltac:(lia) ltac:(lia) BZR) as PB.
    zs. zbr KJ.
    -
      pose proof (IH (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST CHECK last 0 cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo) as IHk.
      cbn [c_u c_p c_q c_n c_ob c_osz c_w l_SP l_SPA l_Zs l_F0 l_lo t_mode t_cin t_cout t_hold t_bits t_length] in IHk.
      eapply IHk with (cinj := cinj + 1) (holdj := holdj + bz payload cinj * 2 ^ j) (j := j + 8) (j0 := j0);
        [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI| exact ARR| exact VISf| exact HID| exact KA| lia| lia| lia| lia| lia| exact PB| lia| lia].
    -
      zs.
      pose proof (check_main AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh ADL (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST CHECK last 0 cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo) as CM.
      cbn [c_u c_p c_q c_n c_ob c_osz c_w l_SP l_SPA l_Zs l_F0 l_lo t_mode t_cin t_cout t_hold t_bits t_length] in CM.
      eapply CM with (cin1 := cinj + 1) (hold1 := holdj + bz payload cinj * 2 ^ j) (bits1 := j + 8);
        [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI| exact ARR| exact VISf| exact HID| exact KA| lia| lia| exact PB| lia| lia].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.

  Theorem check_arm : forall cx ly, arm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh 0x8eea4 CHECK.
  Proof.
    intros cx ly. unfold arm_stmtA, ARM_MS. intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA.
    pose proof (flags_not_m1 _ _ _ _ SI ltac:(rewrite MODE; cbv; discriminate) ltac:(rewrite MODE; cbv; discriminate)) as HFL.
    inf_arm_open. subst mode.
    assert (F0E : flags = 0) by (destruct R13 as [X|X]; [exact X| exfalso; exact (HFL X)]). clear R13. subst flags.
    pose proof (pow2_le_40 bits ltac:(lia)) as P40. change (2 ^ 40) with 1099511627776 in P40.
    zrung [0x8eecc].
    zs. zbr KB31.
    -
      zrung [0x8eef0].
      pose proof (check_loop (Z.to_nat ((39 - bits) / 8)) (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST CHECK last 0 cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo) as CL.
      cbn [c_u c_p c_q c_n c_ob c_osz c_w l_SP l_SPA l_Zs l_F0 l_lo t_mode t_cin t_cout t_hold t_bits t_length] in CL.
      eapply CL with (cinj := cin) (holdj := hold) (j := bits) (j0 := bits);
        [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI| exact ARR| exact VISf| exact HID| exact KA
        | clear - KB31 R4; Z.div_mod_to_equations; lia| clear - KB31 R4; Z.div_mod_to_equations; lia| lia| lia| lia| lia| lia| lia].
    -
      zrung [0x903c4].
      pose proof (check_main AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh ADL (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST CHECK last 0 cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo) as CM.
      cbn [c_u c_p c_q c_n c_ob c_osz c_w l_SP l_SPA l_Zs l_F0 l_lo t_mode t_cin t_cout t_hold t_bits t_length] in CM.
      eapply CM with (cin1 := cin) (hold1 := hold) (bits1 := bits);
        [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI| exact ARR| exact VISf| exact HID| exact KA| lia| lia| lia| lia| lia].
  Qed.
End S.
End CANSEC1.
