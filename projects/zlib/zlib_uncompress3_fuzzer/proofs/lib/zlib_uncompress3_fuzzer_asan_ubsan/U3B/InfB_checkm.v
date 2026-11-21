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
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U3B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfBGlue_p04 U2BCall U2BGlue AdlUBIface InfBAdlCall_p04 InfB_length InfB_checkc.
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
  Hypothesis ADL : adler32_stmtU.

  Lemma check_main : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x23 x28 x29 x30 x31 : word) (m : amem) (cin1 hold1 bits1 : Z),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = CHECK -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m ->
    KALLB cx ly (meas cx st) ->
    t_cin st <= cin1 <= c_n cx -> 32 <= bits1 <= 40 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
    8 * (c_n cx - cin1) + bits1 <= 8 * (c_n cx - t_cin st) + t_bits st ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly)) x10 x11 x12 (Z_to_bv 64 5)
               x14 x15 x16 x17
               (Z_to_bv 64 (l_Zs ly)) x23 (Z_to_bv 64 (c_n cx - cin1)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr (c_p cx + 16) 3 + 2147450880)) (Z_to_bv 64 hold1)
               (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 bits1) (Z_to_bv 64 (c_q cx + cin1)) (Z_to_bv 64 (l_F0 ly)) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x903c4) fc None m (seg_rom bsegs)).
  Proof.
    intros until bits1. intros CTX PAYR PLEN MODE SI ARR VIS HID KA HC HB HH HBC HW.
    pose proof HID as (AH0 & _). pose proof (AI_rtcells AI _ _ _ _ _ AH0) as ART. unfold artcells in ART.
    destruct ART as (_ & RTG & _ & _ & RTS & _).
    pose proof (flags_not_m1 _ _ _ _ SI ltac:(rewrite MODE; cbv; discriminate) ltac:(rewrite MODE; cbv; discriminate)) as HFL.
    inf_arm_open. subst mode.
    assert (F0E : flags = 0) by (destruct R13 as [X|X]; [exact X| exfalso; exact (HFL X)]). clear R13. subst flags.
    pose proof (proj2 ARR) as ARO. cbn [c_osz] in ARO.
    zrung [0x90434].
    zs. zbr KEQ.
    -
      zrung [0x90594].
      lazymatch goal with H : rw_cells bsegs _ S (C8 _ :: _) |- _ => rename H into SSC' end.
      rw_split SSC' 3%nat SSA SSB. rw_split SSB 1%nat SW SSD.
      eapply (rw_cells_recast bsegs _ _ _ [C1 (Z_to_bv 8 5); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) in SW; [| cbn; tauto| reflexivity| reflexivity].
      zs.
      eapply (rw_cells_recast bsegs _ _ _ [C4 (Z_to_bv 64 5)]) in SW; [| cbn; tauto| reflexivity| reflexivity].
      rw_join SW SSD SSB'. rw_join SSA SSB' SSC'.
      zrung [0x909a0].
      pose proof (check_cmp AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST CHECK last 0 cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo) as CC.
      cbn [c_u c_p c_q c_n c_ob c_osz c_w l_SP l_SPA l_Zs l_F0 l_lo t_mode t_cin t_cout t_hold t_bits t_length] in CC.
      eapply CC with (cin1 := cin1) (hold1 := hold1) (bits1 := bits1);
        [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI| exact ARR| inf_vis_close| inf_hid_close| exact KA| lia| lia| exact HH| lia| lia].
    -
      zrung [0x9093c].
      rewrite (Z.mod_small (out - (osz - cout)) 4294967296) in * by lia.
      ub_b2z.
      lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?w) _) then _ else _) _ _ _ _) => let v := eval vm_compute in w in change w with v
      end.
      pc_lit.
      zrung [0x9093c].
      pose proof (bv_unsigned_in_range 64 check) as RCHK. unfold bv_modulus in RCHK.
      lazymatch goal with H : f8arr bsegs ?mx 6341952 _ fo |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (f8arr_sub_bytes mx 6341952 (Z.to_nat osz) fo (Z.to_nat (cout - (out - (osz - cout)))) (Z.to_nat (out - (osz - cout))) H ltac:(lia)) as BUF end.
      replace (6341952 + Z.of_nat (Z.to_nat (cout - (out - (osz - cout))))) with (6341952 + (cout - (out - (osz - cout)))) in BUF by lia.
      set (bs := map (fun i => fo (Z.of_nat i)) (seq (Z.to_nat (cout - (out - (osz - cout)))) (Z.to_nat (out - (osz - cout))))) in *.
      assert (BL : Z.of_nat (length bs) = out - (osz - cout)) by (subst bs; rewrite length_map, length_seq; lia).
      assert (BR : Forall (fun b => 0 <= b < 256) bs).
      { subst bs. apply Forall_forall. intros b Hb. apply in_map_iff in Hb. destruct Hb as (i & <- & Hi). apply in_seq in Hi. apply ARO. lia. }
      clearbody bs.
      assert (ODR : 0 < out - (osz - cout) <= cout /\ cout <= osz /\ osz <= 262144) by lia.
      zs.
      setreg 11 (Z_to_bv 64 (6341952 + (cout - (out - (osz - cout))))) ltac:(f_equal; lia).
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
           | |- unpoisoned _ _ _ => rewrite BL; eapply (unp_of_sh0 _ 6341952 32768); [exact (sh0_mu _ _ _ _ _ SHO MU DJO)| reflexivity| lia| lia| lia| lia| lia]
           | |- rng _ ?l _ => first [ constr_eq l lo; eapply rng_sub'; [exact RSTK| lia] | rewrite BL; eapply rng_sub'; [exact ROB| lia] ]
           | |- _ -> rng _ _ _ => intros _; rewrite BL; eapply rng_sub'; [exact ROBS|]; rewrite !shad_div; unfold ASHOFF;
                                  rewrite ?Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - ODR; Z.div_mod_to_equations; lia
           | |- _ => first [ rewrite BL; unfold KHIGH; lia | unfold KHIGH; lia | rewrite BL; apply Z.mod_small; lia ]
           end.
      zrung [0x90994].
      lazymatch goal with H : rw_cells bsegs _ S (C8 _ :: _) |- _ => rename H into SSC' end.
      rw_split SSC' 3%nat SSA SSB. rw_split SSB 1%nat SW SSD.
      eapply (rw_cells_recast bsegs _ _ _ [C1 (Z_to_bv 8 5); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) in SW; [| cbn; tauto| reflexivity| reflexivity].
      zs.
      eapply (rw_cells_recast bsegs _ _ _ [C4 (Z_to_bv 64 5)]) in SW; [| cbn; tauto| reflexivity| reflexivity].
      rw_join SW SSD SSB'. rw_join SSA SSB' SSC'.
      zrung [0x909a0].
      pose proof (check_cmp AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST CHECK last 0 cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo) as CC.
      cbn [c_u c_p c_q c_n c_ob c_osz c_w l_SP l_SPA l_Zs l_F0 l_lo t_mode t_cin t_cout t_hold t_bits t_length] in CC.
      eapply CC with (cin1 := cin1) (hold1 := hold1) (bits1 := bits1);
        [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI| exact ARR| inf_vis_close| inf_hid_close| exact KA| lia| lia| exact HH| lia| lia].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.
End S.
End CANSEC1.
