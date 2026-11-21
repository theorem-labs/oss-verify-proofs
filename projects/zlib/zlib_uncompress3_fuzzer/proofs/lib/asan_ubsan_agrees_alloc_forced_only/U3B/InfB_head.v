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
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U3B Require Import U2BObj U2BClient U2BIface U2BCall InfBBase InfBKit AdlUBIface.
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

  Definition adln_postz (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (SPV lo : Z) (m : amem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               FR (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(SPV - 176, SPV)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo SPV.
  Lemma adler32_null_callz : forall (lo : Z) (ra t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (m : amem) (SPV : Z),
    0 <= SPV < 2^64 -> mem_inv bsegs m -> stk bsegs m lo SPV -> lo <= SPV - 176 -> KHIGH <= lo -> rt_got m -> rt_shbase m ->
    rng_aimg RNG -> rng RNG lo (SPV - lo) ->
    evtF bsegs RNG (adln_postz ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV lo m)
         (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (Z_to_bv 64 A_ADLER32) fc None m (seg_rom bsegs)).
  Proof.
    intros until SPV. intros RS MI ST LOS KH GOT SHB RI RSTK.
    eapply evtF_mono; [eapply (ADLN RNG ra (Z_to_bv 64 SPV)); rewrite ?unsigned_lit by lia; try eassumption; reflexivity|].
    cbv beta. unfold adln_postz, ADL_STACK. rewrite !unsigned_lit by lia. intros ms' PO. exact PO.
  Qed.

  Lemma head_main : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x5 x6 x7 x10 x11 x14 x15 x16 x17 x19 x23 x26 x28 x30 x31 : word) (m : amem) (cin1 hold1 bits1 : Z),
    inf_ctx cx ly AI RNG LB -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = HEAD -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    t_cin st <= cin1 <= c_n cx -> 16 <= bits1 <= 40 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
    8 * (c_n cx - cin1) + bits1 = 8 * (c_n cx - t_cin st) + t_bits st ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               x10 x11 (Z_to_bv 64 bits1) (Z_to_bv 64 5) x14 x15 x16 x17
               (Z_to_bv 64 (l_Zs ly)) x19 (Z_to_bv 64 (c_q cx + cin1)) (Z_to_bv 64 2147450880) x23 (Z_to_bv 64 hold1)
               (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x26 (Z_to_bv 64 (c_n cx - cin1)) (Z_to_bv 64 (l_F0 ly)) x28 (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) x30 x31)
          FR (Z_to_bv 64 0x902cc) fc None m (seg_rom bsegs)).
  Proof.
    intros until bits1. intros CTX PLEN MODE SI ARR VIS HID (KD & KB & KL & KLV) HC HB HH HBC HW.
    pose proof HID as (AH0 & _). pose proof (AI_rtcells AI _ _ _ _ _ AH0) as ART. unfold artcells in ART.
    destruct ART as (_ & RTG & _ & _ & RTS & _).
    inf_arm_open.
    pose proof (pow2_le_40 bits1 ltac:(lia)) as P40.
    Time zrung [0x8e5ec; 0x924f4; 0x96db4].
    lazymatch goal with |- context [Z_to_bv 64 (?e * 17256631552825064415)] => set (g31 := Z_to_bv 64 (e * 17256631552825064415)); clearbody g31 end.
    assert (MLT : (t_mode (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) <? CHECK) = true)
      by (cbn [t_mode]; rewrite MODE; reflexivity).
    Local Ltac gc := cbn [c_u c_p c_q c_n c_ob c_osz c_w c_cin0 c_cout0 c_W0 c_K c_zc
                         t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
                         t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext].
    Local Ltac or_refl := repeat (first [ left; reflexivity | right ]); reflexivity.
    Local Ltac hd_close KD SI MLT ARR MODE m' fl' c1 h1 b1 ar :=
      lazymatch type of SI with sinv ?cx0 ?st0 ?lf0 ?cf0 =>
        let SI' := fresh "SI'" in let ME' := fresh "ME'" in
        assert (SI' : sinv cx0 (hd_st st0 m' fl' c1 h1 b1) lf0 cf0)
          by (apply sinv_hd; [exact SI| exact MLT| or_refl| first [left; reflexivity | right; reflexivity]
                              | intros X; first [right; reflexivity | exfalso; clear - X; lia]| gc; ar| gc; ar| gc; ar| gc; ar| gc; ar]);
        assert (ME' : meas cx0 (hd_st st0 m' fl' c1 h1 b1) < meas cx0 st0)
          by (apply meas_hd; gc; first [left; ar | right; split; [ar| rewrite MODE; vm_compute; reflexivity]]);
        eapply (KD (hd_st st0 m' fl' c1 h1 b1) lf0 cf0); [exact SI'| exact ME'| exact ARR| unfold hd_st; inf_vis_close| inf_hid_close]
      end.
    if_cases K31.
    -
      Time zrung [0x8e5ec; 0x924f4; 0x96db4].
      hd_close KD SI MLT ARR MODE BAD flags cin1 hold1 bits1 ltac:(first [exact HC | exact HH | exact HBC | clear - HB HW; lia]).
    -
      Time zrung [0x8e5ec; 0x924f4; 0x96db4].
      if_cases KMETH.
      +
        (* [U14B] A2 2026-11-12: zlib 1.4 checks the window size in another order (inflate.c l.548-554): the 1.4 combined code
           branches on len > 7 at 0x91694 (bltu a3,a0,0x916cc), then reads wbits and branches on wbits < len + 8 at
           0x916c4. The mover had no 1.4 pc for the 1.3.1 stop 0x911d8. wbits is 15 here, so the second branch never
           goes to the error (probe h2: KWS : len <= 7, KW2 : 15 < len + 8). *)
        Time zrung [0x9165c; 0x8e5ec; 0x924f4; 0x96db4].
        assert (SH4 : 0 <= Z.shiftr hold1 4 < 2 ^ (bits1 - 4)).
        { clear - HH HB. rewrite Z.shiftr_div_pow2 by lia. replace (2 ^ bits1) with (2 ^ 4 * 2 ^ (bits1 - 4)) in HH by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
          split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
        assert (L15 : 0 <= Z.land (Z.shiftr hold1 4) 15 <= 15).
        { clear - SH4. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound (Z.shiftr hold1 4) (2 ^ 4) ltac:(lia)). change (2 ^ 4) with 16 in *. change (Z.ones 4) with 15. lia. }
        zs. zbr0 KWS.
        *
          Time zrung [0x8e5ec; 0x924f4; 0x96db4].
          replace (bits1 + -4) with (bits1 - 4) by lia.
          hd_close KD SI MLT ARR MODE BAD flags cin1 (Z.shiftr hold1 4) (bits1 - 4) ltac:(first [exact HC | exact SH4 | clear - HB HBC HW; lia]).
        *
          zrung [0x9168c; 0x8e5ec; 0x924f4; 0x96db4].
          zs. zbr0 KW2; [exfalso; clear - KWS KW2; lia|].
          Time zrung [0x8e5ec; 0x924f4; 0x96db4].
          callq (adler32_null_callz lo).
          all: lazymatch goal with
               | |- evtF _ _ _ _ => idtac
               | |- stk _ _ _ _ => eassumption
               | |- mem_inv _ _ => eassumption
               | |- rw_cells _ _ _ _ => eassumption
               | |- rng _ ?l _ => first [ constr_eq l lo; eapply rng_sub'; [exact RSTK| lia] | exact RI ]
               | |- _ => unfold KHIGH; lia
               end.
          Time zrung [0x92858; 0x8e5ec; 0x924f4; 0x96db4].
          zs.
          if_cases KDICT.
          -- Time zrung [0x8e5ec; 0x924f4; 0x96db4].
             hd_close KD SI MLT ARR MODE TYPE 0 cin1 0 0 ltac:(first [exact HC | (clear; cbn; lia) | clear - HB HBC HW; lia]).
          -- Time zrung [0x8e5ec; 0x924f4; 0x96db4].
             hd_close KD SI MLT ARR MODE DICTID 0 cin1 0 0 ltac:(first [exact HC | (clear; cbn; lia) | clear - HB HBC HW; lia]).
      +
        Time zrung [0x8e5ec; 0x924f4; 0x96db4].
        hd_close KD SI MLT ARR MODE BAD flags cin1 hold1 bits1 ltac:(first [exact HC | exact HH | exact HBC | clear - HB HW; lia]).
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.


End S.
End CANSEC1.
