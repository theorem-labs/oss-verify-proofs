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
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit I_asan_memcpy.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AObj U2AStore InfAGlue InfPure InfPure_type InfPure_w7 InfPure_stored U2ABlob UwAKit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfBGlue_p04 U2BCall U2BGlue InfB_copy.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2B Require Import U2BKit U2BKit_p04.
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

  Lemma stored_check : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x5 x6 x10 x11 x14 x15 x16 x17 x19 x21 x23 x26 x28 x30 x31 : word) (m : amem) (cin1 hold1 bits1 : Z),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = STORED -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m ->
    KALLB cx ly (meas cx st) ->
    t_cin st <= cin1 <= c_n cx -> 32 <= bits1 <= 40 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
    8 * (c_n cx - cin1) + bits1 <= 8 * (c_n cx - t_cin st) + t_bits st ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 (Z_to_bv 64 bits1) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly)) x10 x11
               (Z_to_bv 64 (c_n cx - cin1)) (Z_to_bv 64 (c_q cx + cin1)) x14 x15 x16 x17
               (Z_to_bv 64 (l_Zs ly)) x19 x21 (Z_to_bv 64 2147450880) x23 (Z_to_bv 64 hold1)
               (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x26 (Z_to_bv 64 (-3)) (Z_to_bv 64 (l_F0 ly)) x28 (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) x30 x31)
          FR (Z_to_bv 64 0x8f1dc) fc None m (seg_rom bsegs)).
  Proof.
    intros until bits1. intros CTX PAYR PLEN MODE SI ARR VIS HID KA HC HB HH HBC HW.
    pose proof KA as (KD & KB & KL & KLV).
    pose proof (flags_not_m1 _ _ _ _ SI ltac:(rewrite MODE; cbv; discriminate) ltac:(rewrite MODE; cbv; discriminate)) as HFL.
    inf_arm_open. subst mode.
    clear R13.
    assert (P40 : 2 ^ bits1 <= 2 ^ 40) by (apply Z.pow_le_mono_r; lia). change (2 ^ 40) with 1099511627776 in P40.
    zrung [0x8f1f4].
    assert (L16 : 0 <= hold1 mod 65536 < 65536) by (apply Z.mod_pos_bound; lia).
    assert (SIS : sinv (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc)
                       (set_st (IST STORED last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) STORED cin1 cout hold1 bits1 len) lf cf).
    { apply sinv_set; [exact SI| exact HFL| reflexivity| right; left; reflexivity| intros [X|X]; cbv in X; discriminate X
                       | icx_cbn; lia| icx_cbn; lia| lia| lia| lia| icx_cbn; lia| unfold Wm; icx_cbn; lia]. }
    zs. zbr0 KNE.
    {
      zrung [0x8e500].
      pose proof (sinv_bad_ofP _ _ lf cf SIS) as SIB.
      pose proof (meas_bad_ofP (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc)
                    (set_st (IST STORED last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) STORED cin1 cout hold1 bits1 len)) as MEB.
      unfold bad_ofP, set_st in SIB, MEB.
      cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SIB, MEB.
      change (rank STORED) with 30 in MEB.
      eapply (KD (IST BAD last flags cin1 cout hold1 bits1 out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact SIB| unfold meas, Wm in *; icx_cbn; cbn [t_mode t_cin t_cout t_bits] in *; lia| exact ARR| change BAD with 16209; inf_vis_close| inf_hid_close]. }
    zrung [0x8f254].
    zrung [0x8f270].
    assert (SI' : sinv (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc)
                       (set_st (IST STORED last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) COPY cin1 cout 0 0 (hold1 mod 65536)) lf cf).
    { apply sinv_set; [exact SI| exact HFL| reflexivity| right; right; right; left; reflexivity| intros _; lia
                       | icx_cbn; lia| icx_cbn; lia| lia| change (2 ^ 0) with 1; lia| lia| lia| unfold Wm; icx_cbn; lia]. }
    assert (ME' : meas (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc)
                       (set_st (IST STORED last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) COPY cin1 cout 0 0 (hold1 mod 65536))
                  < meas (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc) (IST STORED last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)).
    { apply meas_set. left. unfold Wm; icx_cbn. lia. }
    pose proof (copy_body AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
                  (set_st (IST STORED last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) COPY cin1 cout 0 0 (hold1 mod 65536)) lf cf wf fo) as CB.
    unfold set_st in CB, ME'. cbn [c_u c_p c_q c_n c_ob c_osz c_w l_SP l_SPA l_Zs l_F0 l_lo t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
                               t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in CB, ME'.
    eapply CB; [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI'| exact ARR| change COPY with 16195; inf_vis_close| inf_hid_close|].
    eapply KALL_mono; [| exact KA]. apply Z.lt_le_incl. exact ME'.
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.

  Lemma stored_loop : forall (k : nat) (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x5 x6 x13 x15 x19 x21 x23 x26 x28 x30 x31 : word) (m : amem) (cinj holdj j j0 : Z),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = STORED -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m ->
    KALLB cx ly (meas cx st) ->
    j = 32 - 8 * Z.of_nat k -> (1 <= k <= 4)%nat -> 0 <= j0 -> j - j0 = 8 * (cinj - t_cin st) ->
    t_cin st <= cinj <= c_n cx -> 0 <= holdj < 2 ^ j -> j <= 8 * cinj ->
    8 * (c_n cx - cinj) + j <= 8 * (c_n cx - t_cin st) + t_bits st ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 (Z_to_bv 64 j) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 (c_q cx + cinj)) (Z_to_bv 64 (c_n cx - cinj)) x13 (Z_to_bv 64 j0) x15 (Z_to_bv 64 (c_q cx + cinj)) (Z_to_bv 64 j)
               (Z_to_bv 64 (l_Zs ly)) x21 x19 (Z_to_bv 64 2147450880) x26 (Z_to_bv 64 holdj)
               (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x23 (Z_to_bv 64 (-3)) (Z_to_bv 64 (l_F0 ly)) x28 (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) x30 x31)
          FR (Z_to_bv 64 0x8ecc8) fc None m (seg_rom bsegs)).
  Proof.
    induction k as [|k IH]; intros until j0; intros CTX PAYR PLEN MODE SI ARR VIS HID KA EJ HK J00 EJ0 HC HH HBC HW; [exfalso; lia|].
    pose proof KA as (KD & KB & KL & KLV).
    pose proof (flags_not_m1 _ _ _ _ SI ltac:(rewrite MODE; cbv; discriminate) ltac:(rewrite MODE; cbv; discriminate)) as HFL.
    inf_arm_open. subst mode.
    clear R13.
    assert (J0 : 0 <= j <= 24) by lia.
    assert (P32 : 2 ^ j <= 2 ^ 24) by (apply Z.pow_le_mono_r; lia). change (2 ^ 24) with 16777216 in P32.
    assert (SIS : sinv (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc)
                       (set_st (IST STORED last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) STORED cinj cout holdj j len) lf cf).
    { apply sinv_set; [exact SI| exact HFL| reflexivity| right; left; reflexivity| intros [X|X]; cbv in X; discriminate X
                       | icx_cbn; lia| icx_cbn; lia| lia| lia| lia| icx_cbn; lia| unfold Wm; icx_cbn; lia]. }
    zs. zbr0 KH0.
    2: {
      zrung [0x93664].

      assert (ECN : cinj = n) by lia.
      replace (Z.shiftl (n - cin) 3 + j0) with j by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 3) with 8; lia).
      replace (D + cin + (n - cin) mod 4294967296) with (D + cinj) in * by (rewrite Z.mod_small by lia; lia).
      eapply (KL (IST STORED last flags cinj cout holdj j out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact SIS| exact ARR| exact ECN| inf_vis_close| inf_hid_close]. }
    zrung [0x8ece4].
    destruct (unp_check_mu bsegs _ _ _ _ _ (D + cinj) 1 UNP MU DJP ltac:(lia) ltac:(lia) ltac:(lia) (mod8_room1 _)) as (b & RDB & CK).
    zs. zs. zs. rewrite sxb_sval.
    ck_branchJ 17 0x8ecf4 CK.
    pose proof (pay_read bsegs _ D payload cinj PAYB ltac:(lia)) as RDP. fold (bz payload cinj) in RDP.
    pose proof (bz_range payload cinj PAYR) as BZR.
    zs. zs. cbv beta. rewrite (bz_val payload cinj PAYR).
    zrung [0x8ed1c].
    setreg 23 (Z_to_bv 64 (holdj + bz payload cinj * 2 ^ j)) ltac:(rewrite pull_hold by lia; reflexivity).
    replace (n - cinj + -1) with (n - (cinj + 1)) by lia. replace (D + cinj + 1) with (D + (cinj + 1)) by lia.
    pose proof (pullbyte_bound holdj j (bz payload cinj) ltac:(lia) ltac:(lia) BZR) as PB.
    zs. zbr0 KJ.
    -
      pose proof (IH (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST STORED last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo) as IHk.
      cbn [c_u c_p c_q c_n c_ob c_osz c_w l_SP l_SPA l_Zs l_F0 l_lo t_mode t_cin t_cout t_hold t_bits t_length] in IHk.
      eapply IHk with (cinj := cinj + 1) (holdj := holdj + bz payload cinj * 2 ^ j) (j := j + 8) (j0 := j0);
        [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI| exact ARR| exact VISf| exact HID| exact KA| lia| lia| lia| lia| lia| exact PB| lia| lia].
    -
      zs.
      pose proof (stored_check (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST STORED last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo) as SC.
      cbn [c_u c_p c_q c_n c_ob c_osz c_w l_SP l_SPA l_Zs l_F0 l_lo t_mode t_cin t_cout t_hold t_bits t_length] in SC.
      eapply SC with (cin1 := cinj + 1) (hold1 := holdj + bz payload cinj * 2 ^ j) (bits1 := j + 8);
        [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI| exact ARR| exact VISf| exact HID| exact KA| lia| lia| exact PB| lia| lia].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.

  Theorem stored_arm : forall cx ly, arm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh 0x8ec9c STORED.
  Proof.
    intros cx ly. unfold arm_stmtA, ARM_MS. intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA.
    inf_arm_open. subst mode.
    clear R13.
    pose proof (pow2_le_40 bits ltac:(lia)) as P40. change (2 ^ 40) with 1099511627776 in P40.
    assert (BM : 0 <= bits mod 8 <= bits /\ (bits - bits mod 8) mod 8 = 0) by (clear - R4; Z.div_mod_to_equations; lia).
    pose proof (shiftr_lt_pow2 hold bits (bits mod 8) ltac:(lia) ltac:(lia)) as HSH.
    zs. zs. zs.
    (* [U14B] A2 2026-11-12: hold is in s7 (x23) at 1.4 (0x8ecdc srl s7,s7,a1; 1.3.1 s8 = x24) *)
    setreg 23 (Z_to_bv 64 (Z.shiftr hold (bits mod 8))) ltac:(first [rewrite srl_land7 by lia | rewrite srl_land7' by lia]; reflexivity).
    zs. zbr0 KB31.
    -
      zrung [0x8f1dc].
      setreg 7 (Z_to_bv 64 (bits - bits mod 8)) ltac:(rewrite land_m8_64 by lia; reflexivity).
      pose proof (stored_check (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST STORED last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo) as SC.
      cbn [c_u c_p c_q c_n c_ob c_osz c_w l_SP l_SPA l_Zs l_F0 l_lo t_mode t_cin t_cout t_hold t_bits t_length] in SC.
      eapply SC with (cin1 := cin) (hold1 := Z.shiftr hold (bits mod 8)) (bits1 := bits - bits mod 8);
        [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI| exact ARR| exact VISf| exact HID| exact KA| lia| clear - KB31 R5 BM; Z.div_mod_to_equations; lia| exact HSH| clear - R8 BM; lia| lia].
    -
      zrung [0x8ecc8].
      replace (Z.land bits 24) with (bits - bits mod 8) by (symmetry; apply land24; lia).
      pose proof (stored_loop (Z.to_nat ((32 - (bits - bits mod 8)) / 8)) (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST STORED last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo) as SL.
      cbn [c_u c_p c_q c_n c_ob c_osz c_w l_SP l_SPA l_Zs l_F0 l_lo t_mode t_cin t_cout t_hold t_bits t_length] in SL.
      eapply SL with (cinj := cin) (holdj := Z.shiftr hold (bits mod 8)) (j := bits - bits mod 8) (j0 := bits - bits mod 8);
        [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI| exact ARR| exact VISf| exact HID| exact KA
        | clear - KB31 R4 BM; Z.div_mod_to_equations; lia| clear - KB31 R4 BM; Z.div_mod_to_equations; lia| lia| lia| lia| exact HSH| clear - R8 BM; lia| lia].
  Qed.
End S.
End CANSEC1.
