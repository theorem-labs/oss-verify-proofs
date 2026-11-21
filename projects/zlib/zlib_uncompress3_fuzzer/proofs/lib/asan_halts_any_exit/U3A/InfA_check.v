(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg RtCells ABase ABytes AMalloc_iface AUri_kit I_asan_memcpy.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_type InfPure_w7 InfPure_stored InfPure_check U2ABlob UwAKit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U3A Require Import U2AObj U2AClient U2AIface InfABase InfAKit InfAGlue_p04 U2ACall U2AGlue AdlUIface InfA_leave_adl InfA_length.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
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
  Hypothesis ADL : adler32_stmtU.

  (* the 1.3.1 register homes of check_cmp, check_loop, check_main moved to 1.4 by tools/regmap_text_gr.py (ra>s6 t2>ra s4>s8 s5>s10 s6>t5 s7>s9 s8>s11 s9>s5 s10>s4 s11>s7 t3>t6 t4>t3 t5>t4 t6>t2) *)
  Lemma check_cmp : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x1 x5 x6 x11 x12 x13 x14 x15 x16 x17 : word) (m : amem) (cin1 hold1 bits1 : Z),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = CHECK -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    (* 1.4's CHECK does not store next_in to frame slot 496 (1.3.1's check_main began with
       sd a7,496(s1)), so vnext is whatever the arm had *)
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) v240 (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m ->
    KALLB cx ly (meas cx st) ->
    t_cin st <= cin1 <= c_n cx -> 32 <= bits1 <= 40 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
    8 * (c_n cx - cin1) + bits1 <= 8 * (c_n cx - t_cin st) + t_bits st ->
    evtF asegs RNG POST
      (MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 (Z_to_bv 64 (c_p cx + 56)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               (Z_to_bv 64 (l_F0 ly)) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 bits1) (Z_to_bv 64 hold1) (Z_to_bv 64 2147450880)
               (* 1.4's CHECK code keeps the wrap shadow in s7 and next_in in s10 (probe PgCheckB1) *)
               x1 (Z_to_bv 64 (Z.shiftr (c_p cx + 16) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly))
               (Z_to_bv 64 (c_q cx + cin1)) (Z_to_bv 64 (c_n cx - cin1)) (Z_to_bv 64 (c_p cx + 28)) (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880))
               (Z_to_bv 64 (c_p cx + 108)))
          FR (Z_to_bv 64 0x9018c) fc None m (seg_rom asegs)).
  Proof.
    intros until bits1. intros CTX PAYR PLEN MODE SI ARR VIS HID KA HC HB HH HBC HW.
    pose proof KA as (KD & KB & KL & KLV).
    pose proof (flags_not_m1 _ _ _ _ SI ltac:(rewrite MODE; cbv; discriminate) ltac:(rewrite MODE; cbv; discriminate)) as HFL.
    inf_arm_open. subst mode.
    assert (F0E : flags = 0) by (destruct R13 as [X|X]; [exact X| exfalso; exact (HFL X)]). clear R13. subst flags.
    assert (P40 : 2 ^ bits1 <= 2 ^ 40) by (apply Z.pow_le_mono_r; lia). change (2 ^ 40) with 1099511627776 in P40.
    zrunb [0x9019c].
    lazymatch goal with H : rw_cells asegs _ S (C8 _ :: _) |- _ => rename H into SSC' end.
    rw_split SSC' 3%nat SSA SSB. rw_split SSB 1%nat SW SSD.
    eapply (rw_cells_recast asegs _ _ _ [C1 (Z_to_bv 8 5); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) in SW; [| cbn; tauto| reflexivity| reflexivity].
    zs.
    eapply (rw_cells_recast asegs _ _ _ [C4 (Z_to_bv 64 5)]) in SW; [| cbn; tauto| reflexivity| reflexivity].
    rw_join SW SSD SSB'. rw_join SSA SSB' SSC'.
    zrunb [0x901d4].
    lazymatch goal with |- context [bv_swrap 32 ?e] =>
      assert (SW24 : 0 <= e < 256)
        by (unfold bv_wrap, bv_modulus; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ Z.of_N 32) with 4294967296; change (2 ^ 24) with 16777216;
            pose proof (Z.mod_pos_bound hold1 4294967296 ltac:(lia)); Z.div_mod_to_equations; lia);
      rewrite (swrap32_small e) by lia end.
    zrunb [0x90218].
    zs. zbr0 KNE.
    -
      zrunb [0x8e2dc].
      assert (SIB : sinv (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc)
                       (ck_st (IST CHECK last 0 cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) BAD cin1 hold1 bits1 (osz - cout)) lf cf).
      { apply sinv_ck; [exact SI| reflexivity| right; right; right; reflexivity| icx_cbn; lia| lia| lia| lia| icx_cbn; lia| right; split; [reflexivity| cbv; reflexivity]]. }
      assert (MEB : meas (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc)
                       (ck_st (IST CHECK last 0 cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) BAD cin1 hold1 bits1 (osz - cout))
                  < meas (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (IST CHECK last 0 cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)).
      { apply meas_ck. right. split; [icx_cbn; lia| vm_compute; reflexivity]. }
      eapply (KD (ck_st (IST CHECK last 0 cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) BAD cin1 hold1 bits1 (osz - cout)) lf cf wf fo);
        [exact SIB| exact MEB| exact ARR| change BAD with 16209; unfold ck_st; inf_vis_close| inf_hid_close].
    -
      zrunb [0x90240].
      assert (SIL : sinv (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc)
                       (ck_st (IST CHECK last 0 cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) LENGTH cin1 0 0 (osz - cout)) lf cf).
      { apply sinv_ck; [exact SI| reflexivity| right; left; reflexivity| icx_cbn; lia| lia| change (2 ^ 0) with 1; lia| lia| icx_cbn; lia| right; split; [reflexivity| cbv; reflexivity]]. }
      assert (MEL : meas (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc)
                       (ck_st (IST CHECK last 0 cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) LENGTH cin1 0 0 (osz - cout))
                  < meas (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (IST CHECK last 0 cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)).
      { apply meas_ck. right. split; [icx_cbn; lia| vm_compute; reflexivity]. }
      pose proof (length_body AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
                    (ck_st (IST CHECK last 0 cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) LENGTH cin1 0 0 (osz - cout)) lf cf wf fo) as LBD.
      unfold ck_st in LBD, MEL. cbn [c_u c_p c_q c_n c_ob c_osz c_w l_SP l_SPA l_Zs l_F0 l_lo t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
                                 t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in LBD, MEL.
      eapply LBD; [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SIL| exact ARR| change LENGTH with 16207; inf_vis_close| inf_hid_close|].
      eapply KALL_mono; [| exact KA]. apply Z.lt_le_incl. exact MEL.
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Qed.

  Lemma check_main : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x5 x6 x11 x12 x14 x15 x16 x17 x22 : word) (m : amem) (cin1 hold1 bits1 : Z),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = CHECK -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) v240 (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m ->
    KALLB cx ly (meas cx st) ->
    t_cin st <= cin1 <= c_n cx -> 32 <= bits1 <= 40 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
    8 * (c_n cx - cin1) + bits1 <= 8 * (c_n cx - t_cin st) + t_bits st ->
    evtF asegs RNG POST
      (MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 (Z_to_bv 64 (c_p cx + 56)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               (* the 1.4 state at 0x8f1f0 (probe PgCheckB1, the enough-bits path) *)
               (Z_to_bv 64 (l_F0 ly)) x11 x12 (Z_to_bv 64 5) x14 x15 x16 x17
               (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 bits1) (Z_to_bv 64 hold1) (Z_to_bv 64 2147450880)
               x22 (Z_to_bv 64 (Z.shiftr (c_p cx + 16) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly))
               (Z_to_bv 64 (c_q cx + cin1)) (Z_to_bv 64 (c_n cx - cin1)) (Z_to_bv 64 (c_p cx + 28)) (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880))
               (Z_to_bv 64 (c_p cx + 108)))
          FR (Z_to_bv 64 0x8f220) fc None m (seg_rom asegs)).
  Proof.
    intros until bits1. intros CTX PAYR PLEN MODE SI ARR VIS HID KA HC HB HH HBC HW.
    pose proof HID as (AH0 & _). pose proof (AI_rtcells AI _ _ _ _ _ AH0) as ART. unfold artcells in ART.
    destruct ART as (_ & RTG & _ & _ & RTS & _).
    pose proof (flags_not_m1 _ _ _ _ SI ltac:(rewrite MODE; cbv; discriminate) ltac:(rewrite MODE; cbv; discriminate)) as HFL.
    inf_arm_open. subst mode.
    assert (F0E : flags = 0) by (destruct R13 as [X|X]; [exact X| exfalso; exact (HFL X)]). clear R13. subst flags.
    pose proof (proj2 ARR) as ARO. cbn [c_osz] in ARO.
    zrunb [0x9018c]. (* 1.4 reaches the out == left branch inside this run (1.3.1 stopped at 0x8f6ec) *)
    zbr0 KEQ.
    -
      pose proof (check_cmp (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST CHECK last 0 cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo) as CC.
      cbn [c_u c_p c_q c_n c_ob c_osz c_w l_SP l_SPA l_Zs l_F0 l_lo t_mode t_cin t_cout t_hold t_bits t_length] in CC.
      eapply CC with (cin1 := cin1) (hold1 := hold1) (bits1 := bits1);
        [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI| exact ARR| inf_vis_close| inf_hid_close| exact KA| lia| lia| exact HH| lia| lia].
    -
      zrunb [0x90138].
      pose proof (bv_unsigned_in_range 64 check) as RCHK. unfold bv_modulus in RCHK.
      lazymatch goal with H : f8arr asegs ?mx 6336512 _ fo |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (f8arr_sub_bytes mx 6336512 (Z.to_nat osz) fo (Z.to_nat (cout - (out - (osz - cout)))) (Z.to_nat (out - (osz - cout))) H ltac:(lia)) as BUF end.
      replace (6336512 + Z.of_nat (Z.to_nat (cout - (out - (osz - cout))))) with (6336512 + (cout - (out - (osz - cout)))) in BUF by lia.
      set (bs := map (fun i => fo (Z.of_nat i)) (seq (Z.to_nat (cout - (out - (osz - cout)))) (Z.to_nat (out - (osz - cout))))) in *.
      assert (BL : Z.of_nat (length bs) = out - (osz - cout)) by (subst bs; rewrite length_map, length_seq; lia).
      assert (BR : Forall (fun b => 0 <= b < 256) bs).
      { subst bs. apply Forall_forall. intros b Hb. apply in_map_iff in Hb. destruct Hb as (i & <- & Hi). apply in_seq in Hi. apply ARO. lia. }
      clearbody bs.
      assert (ODR : 0 < out - (osz - cout) <= cout /\ cout <= osz /\ osz <= 262144) by lia.
      zs.
      setreg 11 (Z_to_bv 64 (6336512 + (cout - (out - (osz - cout))))) ltac:(rewrite Z.mod_small by lia; f_equal; lia).
      setreg 10 (Z_to_bv 64 (bv_unsigned check)) ltac:(apply Z_to_bv_bv_unsigned).
      callq (adler32_callz ADL lo bs RNG).
      all: lazymatch goal with
           | |- evtF _ _ _ _ => idtac
           | |- bytes_at _ _ _ _ => exact BUF
           | |- Forall _ _ => exact BR
           | |- stk _ _ _ _ => eassumption
           | |- mem_inv _ _ => eassumption
           | |- rw_cells _ _ _ _ => eassumption
           | |- rng_aimg _ => exact RI
           | |- unpoisoned _ _ _ => rewrite BL; eapply (unp_of_sh0 _ 6336512 32768); [exact (sh0_mu _ _ _ _ _ SHO MU DJO)| reflexivity| lia| lia| lia| lia| lia]
           | |- rng _ ?l _ => first [ constr_eq l lo; eapply rng_sub'; [exact RSTK| lia] | rewrite BL; eapply rng_sub'; [exact ROB| lia] ]
           | |- _ -> rng _ _ _ => intros _; rewrite BL; eapply rng_sub'; [exact ROBS|]; rewrite !shad_div; unfold ASHOFF;
                                  rewrite ?Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - ODR; Z.div_mod_to_equations; lia
           | |- _ => first [ rewrite BL; unfold KHIGH; lia | unfold KHIGH; lia | rewrite BL; apply Z.mod_small; lia ]
           end.
      zrunb [0x9018c].
      pose proof (check_cmp (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST CHECK last 0 cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo) as CC.
      cbn [c_u c_p c_q c_n c_ob c_osz c_w l_SP l_SPA l_Zs l_F0 l_lo t_mode t_cin t_cout t_hold t_bits t_length] in CC.
      eapply CC with (cin1 := cin1) (hold1 := hold1) (bits1 := bits1);
        [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI| exact ARR| inf_vis_close| inf_hid_close| exact KA| lia| lia| exact HH| lia| lia].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Qed.

  Lemma check_loop : forall (k : nat) (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x5 x6 x12 x16 x17 x22 : word) (m : amem) (cinj holdj j : Z),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = CHECK -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) v240 (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m ->
    KALLB cx ly (meas cx st) ->
    32 - 8 * Z.of_nat k <= j < 40 - 8 * Z.of_nat k -> (1 <= k <= 4)%nat -> 0 <= j ->
    t_cin st <= cinj <= c_n cx -> 0 <= holdj < 2 ^ j -> j <= 8 * cinj ->
    8 * (c_n cx - cinj) + j <= 8 * (c_n cx - t_cin st) + t_bits st ->
    evtF asegs RNG POST
      (MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 (Z_to_bv 64 (c_p cx + 56)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (c_q cx + cinj)) x12 (Z_to_bv 64 5) (Z_to_bv 64 (c_q cx + cinj)) (Z_to_bv 64 j) x16 x17
               (* the 1.4 state at 0x8e9bc (probe PgCheckB1, the pull loop) *)
               (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 j) (Z_to_bv 64 holdj) (Z_to_bv 64 2147450880)
               x22 (Z_to_bv 64 (Z.shiftr (c_p cx + 16) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly))
               (Z_to_bv 64 (c_q cx + cinj)) (Z_to_bv 64 (c_n cx - cinj)) (Z_to_bv 64 (c_p cx + 28)) (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880))
               (Z_to_bv 64 (c_p cx + 108)))
          FR (Z_to_bv 64 0x8e9ec) fc None m (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros until j; intros CTX PAYR PLEN MODE SI ARR VIS HID KA EJ HK J0 HC HH HBC HW; [exfalso; lia|].
    pose proof KA as (KD & KB & KL & KLV).
    pose proof (flags_not_m1 _ _ _ _ SI ltac:(rewrite MODE; cbv; discriminate) ltac:(rewrite MODE; cbv; discriminate)) as HFL.
    inf_arm_open. subst mode.
    assert (F0E : flags = 0) by (destruct R13 as [X|X]; [exact X| exfalso; exact (HFL X)]). clear R13. subst flags.
    assert (J31 : j <= 31) by lia.
    assert (P32 : 2 ^ j <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia). change (2 ^ 31) with 2147483648 in P32.
    assert (SIS : sinv (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc)
                       (ck_st (IST CHECK last 0 cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) CHECK cinj holdj j out) lf cf).
    { apply sinv_ck; [exact SI| reflexivity| left; reflexivity| icx_cbn; lia| lia| lia| lia| icx_cbn; lia| left; split; [reflexivity| intros X; exact X]]. }
    zs. zbr0 KH0.
    2: {
      zrunb [0x929cc].
      eapply (KLV (ck_st (IST CHECK last 0 cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) CHECK cinj holdj j out) ret lf cf wf fo);
        [exact SIS| exact ARR| unfold ck_st; inf_vis_close| inf_hid_close]. }
    zs.
    destruct (unp_check_mu asegs _ _ _ _ _ (D + cinj) 1 UNP MU DJP ltac:(lia) ltac:(lia) ltac:(lia) (mod8_room1 _)) as (b & RDB & CK).
    zs. zs. zs. rewrite sxb_sval.
    ck_branchJ 16 0x8ea08 CK.
    pose proof (pay_read asegs _ D payload cinj PAYB ltac:(lia)) as RDP. fold (bz payload cinj) in RDP.
    pose proof (bz_range payload cinj PAYR) as BZR.
    zs. zs. cbv beta. rewrite (bz_val payload cinj PAYR).
    zrunb [0x8ea30].
    setreg 20 (Z_to_bv 64 (holdj + bz payload cinj * 2 ^ j)) ltac:(rewrite pull_hold by lia; reflexivity).
    replace (n - cinj + -1) with (n - (cinj + 1)) by lia. replace (D + cinj + 1) with (D + (cinj + 1)) by lia.
    pose proof (pullbyte_bound holdj j (bz payload cinj) ltac:(lia) ltac:(lia) BZR) as PB.
    zs. zbr0 KJ.
    -
      pose proof (IH (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST CHECK last 0 cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo) as IHk.
      cbn [c_u c_p c_q c_n c_ob c_osz c_w l_SP l_SPA l_Zs l_F0 l_lo t_mode t_cin t_cout t_hold t_bits t_length] in IHk.
      eapply IHk with (cinj := cinj + 1) (holdj := holdj + bz payload cinj * 2 ^ j) (j := j + 8);
        [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI| exact ARR| exact VISf| exact HID| exact KA| lia| lia| lia| lia| exact PB| lia| lia].
    -
      zs.
      pose proof (check_main (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST CHECK last 0 cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo) as CM.
      cbn [c_u c_p c_q c_n c_ob c_osz c_w l_SP l_SPA l_Zs l_F0 l_lo t_mode t_cin t_cout t_hold t_bits t_length] in CM.
      eapply CM with (cin1 := cinj + 1) (hold1 := holdj + bz payload cinj * 2 ^ j) (bits1 := j + 8);
        [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI| exact ARR| exact VISf| exact HID| exact KA| lia| lia| exact PB| lia| lia].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Qed.

  Theorem check_arm : forall cx ly, arm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh 0x8e9b4 CHECK.
  Proof.
    intros cx ly. unfold arm_stmtA, ARM_MS. intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA.
    pose proof (flags_not_m1 _ _ _ _ SI ltac:(rewrite MODE; cbv; discriminate) ltac:(rewrite MODE; cbv; discriminate)) as HFL.
    inf_arm_open. subst mode.
    assert (F0E : flags = 0) by (destruct R13 as [X|X]; [exact X| exfalso; exact (HFL X)]). clear R13. subst flags.
    pose proof (pow2_le_40 bits ltac:(lia)) as P40. change (2 ^ 40) with 1099511627776 in P40.
    zrunb [0x8e9dc].
    zs. zbr0 KB31.
    -
      zrunb [0x8f220].
      pose proof (check_main (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST CHECK last 0 cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo) as CM.
      cbn [c_u c_p c_q c_n c_ob c_osz c_w l_SP l_SPA l_Zs l_F0 l_lo t_mode t_cin t_cout t_hold t_bits t_length] in CM.
      eapply CM with (cin1 := cin) (hold1 := hold) (bits1 := bits);
        [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI| exact ARR| exact VISf| exact HID| exact KA| lia| lia| lia| lia| lia].
    -
      zrunb [0x8e9ec].
      pose proof (check_loop (Z.to_nat ((39 - bits) / 8)) (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST CHECK last 0 cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo) as CL.
      cbn [c_u c_p c_q c_n c_ob c_osz c_w l_SP l_SPA l_Zs l_F0 l_lo t_mode t_cin t_cout t_hold t_bits t_length] in CL.
      eapply CL with (cinj := cin) (holdj := hold) (j := bits);
        [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI| exact ARR| exact VISf| exact HID| exact KA
        | clear - KB31 R4; Z.div_mod_to_equations; lia| clear - KB31 R4; Z.div_mod_to_equations; lia| lia| lia| lia| lia| lia].
    (* at 1.4 the KB31 branch's first goal is the enough-bits path, so the bullets swapped *)
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Qed.
End S.
End CANSEC1.
