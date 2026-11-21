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
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_type InfPure_w7 InfPure_table InfPure_itab InfPure_lenlens ItAPure.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U3B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfB_w7base InfB_w6base InfB_w6kit U2BIface_fit2_draft InfB_itcall InfB_llcall InfB_llfill.
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
  Variable rng_fs : alayout -> footprint -> Prop.
  Variables (L : alayout) (RNG : footprint) (stA : astate) (LB : list ablock).
  Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (POST : machine_state -> Prop).
  Variables (LBc : list ablock) (m0 : amem) (payload : list Z) (fw : Z -> Z) (saved fk fksh : list cell).

  Notation KALLB cx ly B := (KALL cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh B).
  Notation HIDm cx ly m := (inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m).
  Notation GARM2 cx ly Lb X := (garm2_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).

  Notation GARM cx ly Lb X := (garm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).

  Lemma drop3_bound : forall H B, 0 <= H < 2 ^ B -> 3 <= B -> 0 <= H / 8 < 2 ^ (B - 3).
  Proof.
    intros H B HH HB. assert (E : 2 ^ B = 8 * 2 ^ (B - 3)) by (change 8 with (2 ^ 3); rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (0 < 2 ^ (B - 3)) by (apply Z.pow_pos_nonneg; lia).
    split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
  Qed.

  Definition LLHEAD (N : nat) (cx : ictx) (ly : ilay) : Prop :=
    forall (st : ist) (cs : Z) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x6 x7 x11 x17 x22 x23 x26 x28 x29 x30 x31 : word) (m : amem),
    (Z.to_nat (t_ncode st - t_shave st) <= N)%nat -> t_shave st < t_ncode st ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LENLENS -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    inf_vis cx ly (st_cin st cs) lf cf wf fo payload v0 v8 v16 v24 v240 v328 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (t_bits st)) x6 x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               (Z_to_bv 64 (c_p cx + 156)) x11 (Z_to_bv 64 141376) (Z_to_bv 64 (-19)) (Z_to_bv 64 (t_shave st + 1)) (Z_to_bv 64 (0 - t_ncode st)) (Z_to_bv 64 (2 * t_shave st)) x17
               (Z_to_bv 64 (l_Zs ly)) x22 (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 2147450880) x23 (Z_to_bv 64 (t_hold st))
               (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x26 (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (l_F0 ly)) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x8f5a8) fc None m (seg_rom bsegs)).

  Lemma ll_body : forall (N : nat) (cx : ictx) (ly : ilay) (st : ist) (cs : Z) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x6 x7 x11 x17 x22 x23 x26 x28 x29 x30 x31 : word) (m : amem) (cin1 hold1 bits1 : Z),
    LLHEAD N cx ly -> (Z.to_nat (t_ncode st - t_shave st) <= S N)%nat -> t_shave st < t_ncode st ->
    itcall_env AI rng_fs L RNG LB tp ly -> GARM2 cx ly 0x8f8d8 CODELENS ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LENLENS -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    inf_vis cx ly (st_cin st cs) lf cf wf fo payload v0 v8 v16 v24 v240 v328 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    t_cin st <= cin1 <= c_n cx -> 3 <= bits1 <= 40 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
    8 * (c_n cx - cin1) + bits1 = 8 * (c_n cx - t_cin st) + t_bits st ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 bits1) x6 x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               (Z_to_bv 64 (c_p cx + 156)) x11 (Z_to_bv 64 141376) (Z_to_bv 64 (-19)) (Z_to_bv 64 (t_shave st + 1)) (Z_to_bv 64 (0 - t_ncode st)) (Z_to_bv 64 (2 * t_shave st)) x17
               (Z_to_bv 64 (l_Zs ly)) x22 (Z_to_bv 64 (c_n cx - cin1)) (Z_to_bv 64 2147450880) x23 (Z_to_bv 64 hold1)
               (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x26 (Z_to_bv 64 (c_q cx + cin1)) (Z_to_bv 64 (l_F0 ly)) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x8f5f8) fc None m (seg_rom bsegs)).
  Proof.
    intros until bits1. intros HEAD HN HJN ENV HCL CTX PAYR PLEN MODE SI ARR VIS HID KA HC HB HH HBC HW.
    destruct (ll_mode_facts _ _ _ _ SI MODE) as (NC1 & NC2 & SH0 & SH1 & L7 & RLF).
    pose proof (order_f_range (t_shave st) ltac:(lia)) as ORJ.
    pose proof (drop3_bound hold1 bits1 HH ltac:(lia)) as D3.
    inf_arm_open_s.
    pose proof (pow2_le_40 bits1 ltac:(lia)) as P40.
    Time zrung [0x8f60c].
    zs.
    replace (18446744073709551597 + (shave + 1)) with ((shave + 1 - 19) + 4294967296 * 4294967296) by lia.
    rewrite swrap32_shift, swrap32_small by lia.
    Time zrung [0x8f618].
    zs. zbr KG.
    2: { exfalso. clear - KG SH0 SH1 NC1 NC2 HJN. Z.div_mod_to_equations. lia. }
    clear KG.
    Time zrung [0x8f62c]. zs.
    setreg 11 (Z_to_bv 64 (141376 + 2 * shave)) ltac:(f_equal; lia).
    lazymatch type of MU with munch _ _ ?mc =>
      pose proof (shadow_bytes_munch _ _ mc _ _ _ SHOR MU DJOR) as SHOR1; pose proof (shadow_bytes_munch _ _ mc _ _ _ SHO6 MU DJO6) as SHO61;
      destruct (order_check mc shave SHOR1 SHO61 ltac:(lia)) as (b & RDB & CK);
      pose proof (order_read mc shave _ MI ltac:(lia) eq_refl) as RDO
    end.
    zs. zs. zs. rewrite sxb_sval.
    Time ck_branchJ 5 0x8f640 CK.
    zs. rewrite (zx16_small (order_f shave)) by lia. clear RDO RDB.
    zs. setreg 11 (Z_to_bv 64 (2 * order_f shave)) ltac:(rewrite shl1_2x; reflexivity).
    zs. setreg 10 (Z_to_bv 64 (18446744073709551615 - (S + 168))) ltac:(rewrite lxor_ones64 by lia; reflexivity).
    Time zrung [0x8f66c].
    zs. setreg 17 (Z_to_bv 64 (hold1 mod 8)) ltac:(rewrite land7_mod by lia; reflexivity).
    zs. setreg 23 (Z_to_bv 64 (hold1 / 8)) ltac:(rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    zs. zs.
    pose proof (Z.mod_pos_bound hold1 8 ltac:(lia)) as RV.
    lazymatch type of LENS with f16arr _ ?mc _ _ _ =>
      assert (SOK : store_ok bsegs mc (Z_to_bv 64 (S + 168 + 2 * order_f shave)) 2 = true)
        by (eapply (f16arr_store_ok bsegs mc (S + 168) 320 lf (order_f shave)); [exact LENS| lia| reflexivity]);
      zstep;
      pose proof (f16arr_write bsegs mc (S + 168) 320 lf (order_f shave) (Z_to_bv 64 (hold1 mod 8)) (hold1 mod 8) LENS ltac:(lia) eq_refl) as LENS'
    end.
    store_done.
    pose proof (lens_rng_upd lf (order_f shave) (hold1 mod 8) RLF ltac:(lia)) as RLF'.
    pose proof (lens7_upd lf shave (hold1 mod 8) L7 ltac:(lia)) as L7'.
    destruct (sinv_ll _ _ lf cf cin1 (hold1 / 8) (bits1 - 3) (shave + 1) (fupd lf (order_f shave) (hold1 mod 8)) SI MODE
                ltac:(icx_cbn; lia) ltac:(icx_cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(icx_cbn; lia) ltac:(lia) ltac:(lia) RLF' L7') as (SI' & ME').
    unfold st_ll in SI', ME'. icx_cbn.
    Time zrung [0x8f680].
    zs.
    assert (ENC : (0 - ncode) mod 18446744073709551616 = 18446744073709551616 - ncode) by (clear - NC1 NC2; Z.div_mod_to_equations; lia).
    rewrite ENC. replace (18446744073709551616 - ncode + (shave + 2)) with ((shave + 2 - ncode) + 4294967296 * 4294967296) by lia.
    rewrite swrap32_shift, swrap32_small by lia.
    Time zrung [0x8f690].
    zs. zbr KJ.
    -
      assert (JN : shave + 1 < ncode) by (clear - KJ SH0 SH1 NC2 HJN; Z.div_mod_to_equations; lia).
      replace (bits1 + -3) with (bits1 - 3) by lia.
      replace (shave + 2) with (shave + 1 + 1) by lia. replace (2 * shave + 2) with (2 * (shave + 1)) by lia.
      eapply (HEAD (IST mode last flags cin1 cout (hold1 / 8) (bits1 - 3) out ret len offset extra lc dc lb db ncode nlen ndist (shave + 1) nx whave wnext) cs
                   (fupd lf (order_f shave) (hold1 mod 8)) cf wf fo);
        [icx_cbn; lia| icx_cbn; lia| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI'| exact ARR| inf_vis_close_sn| inf_hid_close
        | eapply KALL_mono; [| exact KA]; exact ME'].
    -
      assert (JN : shave + 1 = ncode) by (clear - KJ SH0 SH1 NC2 HJN; Z.div_mod_to_equations; lia).
      zrung [0x8f6d8].
      replace (bits1 + -3) with (bits1 - 3) by lia.
      eapply (ll_fill AI rng_fs L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
                (IST mode last flags cin1 cout (hold1 / 8) (bits1 - 3) out ret len offset extra lc dc lb db ncode nlen ndist (shave + 1) nx whave wnext) cs
                (fupd lf (order_f shave) (hold1 mod 8)) cf wf fo);
        [exact ENV| exact HCL| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI'| exact ARR| inf_vis_close_sn| inf_hid_close
        | eapply KALL_mono; [| exact KA]; exact ME'].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.
End S.
End CANSEC1.
