(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_type InfPure_w7 InfPure_table InfPure_itab InfPure_cld InfAGlue_w7 ItAPure.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U1B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfB_w7base InfB_w6base InfB_w6kit InfB_w6garm InfB_w7pull U2BIface_fit2_draft InfB_itcall InfB_cldone_base InfB_cld1 InfB_cld2.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U1B Require Import U2BKit U2BKit_p04 InfBTraps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac ub_is_trap pc ::= ub_in_traps inf_traps pc.
Local Ltac solve_load_hyp :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] => match goal with HR : ov_read_bytes segs m a n = Some _ |- _ => rewrite HR end
  end; load_post.
Local Ltac solve_load ::= first [ solve_load_hyp | solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint_hyp := lazymatch goal with |- acc_in ?R ?x => match goal with HA : acc_in R x |- _ => exact HA end end.
Local Ltac acc_hint ::= first [ acc_hint_hyp | acc_hint_sh ].
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
  Notation GARM cx ly Lb X := (garm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).

  Theorem cldone_thm : forall cx ly, itcall_env AI rng_fs L RNG LB tp ly -> GARM cx ly 0x913a4 LEN_ ->
    cldone_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh.
  Proof.
    intros cx ly ENV HLEN_. unfold cldone_stmtA, CLDONE_MS. intros until m. intros CTX PAYR PLEN MODE SHV SI ARR VIS HID KA.
    pose proof KA as (KD & KB & KL & KLV).
    destruct (ex_intro (fun r0 => r0 = resA InflateState.LENS lf 0 (t_nlen st) 0 9 cf wf) _ eq_refl) as [r1 ER1].
    destruct (ex_intro (fun r0 => r0 = resA DISTS lf (t_nlen st) (t_ndist st) (it_table r1) 6 (arr_get (it_tbl r1)) (arr_get (it_work r1))) _ eq_refl) as [r2 ER2].
    pose proof (cl_exits cx st lf cf wf r1 r2 SI MODE SHV (proj1 ARR) ER1 ER2) as EX. cbv zeta in EX.
    destruct EX as (ITC1 & RN1 & RW1 & NL & ND & HBAD1 & HOK1).
    pose proof (sinv_bad_ofP _ _ lf cf SI) as SIB. pose proof (meas_bad_ofP cx st) as MEB. rewrite MODE in MEB. change (rank CODELENS) with 20 in MEB.
    revert ITC1 RN1 RW1 HBAD1 HOK1 ER1 ER2 SIB MEB.
    inf_arm_open. intros ITC1 RN1 RW1 HBAD1 HOK1 ER1 ER2 SIB MEB. subst mode.
    change CODELENS with 16198 in SSC.
    Time zrung [0x8fb88].
    pose proof (f16arr_read bsegs _ (S + 168) 320 lf 256 (Z_to_bv 64 (S + 680)) LENS ltac:(clear; lia) ltac:(unfold wa; f_equal; clear; lia)) as RD256.
    pose proof (rng_acc_litZ RNG S 7176 (S + 680) 2%nat 2 RS eq_refl ltac:(clear; lia) ltac:(clear; lia)) as AC256.
    pose proof (R30 256 ltac:(unfold N_LENS; clear; lia)) as LF256.
    zs. cbv beta. rewrite (zx16_small (lf 256)) by (clear - LF256; lia).
    zs. zs. zs. zbr0 K256.
    -
      Time zrung [0x8e260].
      unfold bad_ofP in SIB, MEB. st_norm SIB. st_norm MEB.
      eapply (KD (IST BAD last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact SIB| clear - MEB; lia| exact ARR| change BAD with 16209; inf_vis_close| inf_hid_close].
    -
      Time zrung [0x96a34].
      replace (S + 1384) with (S + 1384 + 4 * 0) in SSC by (clear; lia).
      eapply (inf_itcall AI rng_fs L RNG stA LB LBc m0 payload POST (ICX u S D n 6341056 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
                (IST CODELENS last flags cin cout hold bits out ret len offset extra (CDyn 0) dc 9 db ncode nlen ndist shave 0 whave wnext) lf cf wf fo fw)
        with (isd := false) (ty := InflateState.LENS) (lens_ofs := 0) (codes := nlen) (bits := 9) (RA := 0x8fc08) (r := r1);
        [exact ENV| exact CTX0| change CODELENS with 16198; inf_vis_close| inf_hid_close| exact PLEN| reflexivity| exact ITC1| exact ER1| reflexivity| lia| reflexivity| reflexivity
        | reflexivity| icx_cbn; f_equal; lia| reflexivity| reflexivity| reflexivity| reflexivity| ].
      intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' VIS' HID' RET1.
      eapply (cld_post1 AI rng_fs L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (ICX u S D n 6341056 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
                (st_itab (IST CODELENS last flags cin cout hold bits out ret len offset extra (CDyn 0) dc 9 db ncode nlen ndist shave 0 whave wnext) false (it_bits r1) (it_table r1))
                lf (arr_get (it_tbl r1)) (arr_get (it_work r1)) fo) with (B := meas (ICX u S D n 6341056 osz Wd cin0 cout0 W0 K0 zc) (IST CODELENS last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)) (r2 := r2);
        [exact ENV| exact HLEN_| exact CTX0| exact PAYR| exact PLEN| reflexivity| exact RN1| split; [exact RW1| exact (proj2 ARR)]| exact NL| exact ND| exact VIS'| exact HID'
        | split; [exact KD| split; [exact KB| split; [exact KL| exact KLV]]]| exact RET1| | ].
      + intros NE. destruct (HBAD1 NE) as (SB1 & MB1). split; [exact SB1| exact MB1].
      + intros E0. destruct (HOK1 E0) as (ITC2 & RN2 & RW2 & HOK2 & HBAD2).
        split; [exact ITC2|]. split; [exact ER2|]. split; [exact RN2|]. split; [exact RW2|]. split; [exact HOK2| exact HBAD2].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Time Qed.
End S.
End CANSEC1.
