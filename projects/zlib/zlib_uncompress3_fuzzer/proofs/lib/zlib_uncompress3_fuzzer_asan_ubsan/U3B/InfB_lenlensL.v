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
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_type InfPure_w7 InfPure_table InfPure_itab InfPure_lenlens ItAPure.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U3B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfB_w7base InfB_w6base InfB_w6kit U2BIface_fit2_draft InfB_itcall InfB_llcall InfB_llfill InfB_lenlens.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U3B Require Import U2BKit U2BKit_p04 InfBTraps InfB_w6base InfB_w6garm InfB_table.
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
  Notation LLH N cx ly := (LLHEAD AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh N cx ly).

  Lemma zx32_small' : forall e, 0 <= e < 4294967296 -> zx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
  Proof. intros e H. unfold zx32. rewrite unsigned_lit by lia. change (2 ^ 32) with 4294967296. rewrite Z.mod_small by lia. reflexivity. Qed.

  Lemma ll_loop : forall (N : nat) (cx : ictx) (ly : ilay),
    itcall_env AI rng_fs L RNG LB tp ly -> GARM2 cx ly 0x8f8d8 CODELENS -> LLH N cx ly.
  Proof.
    induction N as [|N IH]; intros cx ly ENV HCL; unfold LLHEAD; intros until m; intros HN HJN CTX PAYR PLEN MODE SI ARR VIS HID KA; [lia|].
    pose proof KA as (KD & KB & KL & KLV).
    pose proof (IH cx ly ENV HCL) as HEAD.
    inf_arm_open_s.
    pose proof (pow2_le_40 bits ltac:(lia)) as P40.
    zs. zs. zbr0 KB3.
    -
      eapply (ll_body AI rng_fs L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh N (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
                (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cs lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cin hold bits);
        [exact HEAD| exact HN| exact HJN| exact ENV| exact HCL| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| | | | | ]; icx_cbn; lia.
    - zs. zbr0 KAV.
      2: {
        zrung [0x93758].
        replace (Z_to_bv 64 0) with (Z_to_bv 64 (n - cin)) by (f_equal; lia).
        eapply (KLV (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ret lf cf wf fo);
          [exact SI| exact ARR| inf_vis_close| inf_hid_close]. }
      destruct (unp_check_mu bsegs _ _ _ _ _ (D + cin) 1 UNP MU DJP ltac:(lia) ltac:(lia) ltac:(lia) (mod8_room1 _)) as (b & RDB & CK).
      zrung [0x8f5d4].
      zs. rewrite sxb_sval.
      ck_branchJ 5 0x8f5dc CK.
      pose proof (pay_read bsegs _ D payload cin PAYB ltac:(lia)) as RDP. fold (bz payload cin) in RDP.
      pose proof (bz_range payload cin PAYR) as BZR.
      zs. cbv beta. rewrite (bz_val payload cin PAYR).
      zrung [0x8f5f8].
      rewrite (lor8_small bits) by lia.
      setreg 23 (Z_to_bv 64 (hold + bz payload cin * 2 ^ bits)) ltac:(rewrite pull_hold by lia; reflexivity).
      pose proof (pullbyte_bound hold bits (bz payload cin) ltac:(lia) ltac:(lia) BZR) as PB.
      replace (D + cin + 1) with (D + (cin + 1)) by lia. replace (n - cin + -1) with (n - (cin + 1)) by lia.
      eapply (ll_body AI rng_fs L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh N (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
                (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cs lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (cin + 1) (hold + bz payload cin * 2 ^ bits) (bits + 8));
        [exact HEAD| exact HN| exact HJN| exact ENV| exact HCL| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| inf_vis_close_sn| inf_hid_close| exact KA| | | | | ]; icx_cbn; lia.
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.

  Theorem llin_proof : forall cx ly, itcall_env AI rng_fs L RNG LB tp ly -> GARM2 cx ly 0x8f8d8 CODELENS ->
    llin_stmtA AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly.
  Proof.
    intros cx ly ENV HCL. unfold llin_stmtA. intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA.
    destruct (ll_mode_facts _ _ _ _ SI MODE) as (NC1 & NC2 & SH0 & SH1 & L7 & RLF).
    inf_arm_open_s.
    zrung [0x8f580].
    zs. zbr0 KHN.
    -
      zrung [0x8f6d8].
      eapply (ll_fill AI rng_fs L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
                (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cs lf cf wf fo);
        [exact ENV| exact HCL| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| inf_vis_close_sn| inf_hid_close| exact KA].
    - zrung [0x8f5a8].
      assert (E16 : Z.shiftr (Z.shiftl shave 32 mod 18446744073709551616) 31 = 2 * shave).
      { clear - SH0 SH1 NC2. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 32) with 4294967296. change (2 ^ 31) with 2147483648.
        rewrite Z.mod_small by lia. Z.div_mod_to_equations. lia. }
      rewrite E16.
      eapply (ll_loop (Z.to_nat (ncode - shave)) (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) ENV HCL
                (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cs lf cf wf fo);
        [icx_cbn; lia| icx_cbn; lia| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| inf_vis_close_sn| inf_hid_close| exact KA].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.

  Theorem lenlens_garm : forall cx ly, itcall_env AI rng_fs L RNG LB tp ly -> GARM2 cx ly 0x8f8d8 CODELENS -> GARM cx ly 0x8e700 LENLENS.
  Proof.
    intros cx ly ENV HCL. unfold garm_stmtA, GARM_MS. intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA.
    pose proof (llin_proof cx ly ENV HCL) as LLIN. unfold llin_stmtA in LLIN.
    destruct (ll_mode_facts _ _ _ _ SI MODE) as (NC1 & NC2 & SH0 & SH1 & L7 & RLF).
    inf_arm_open.
    zrung [0x8f560].
    rewrite ?(sx32_small shave) by lia.
    eapply (LLIN (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cin lf cf wf fo);
      [exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| inf_vis_close_sn| inf_hid_close| exact KA].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.
End S.
End CANSEC1.
