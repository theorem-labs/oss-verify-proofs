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
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_type InfPure_w7 InfPure_table InfPure_itab InfPure_lenlens ItAPure.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U1B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfB_w7base InfB_w6base InfB_w6kit U2BIface_fit2_draft InfB_itcall InfB_llcall.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U1B Require Import U2BKit U2BKit_p04 InfBTraps InfB_w6base InfB_w6garm.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import RunDraw.
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

  Lemma lxor_ones64 : forall x, 0 <= x < 18446744073709551616 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
  Proof.
    intros x Hx. change 18446744073709551615 with (Z.ones 64).
    assert (LL : Z.land (Z.lxor x (Z.ones 64)) x = 0).
    { apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.lxor_spec, Z.bits_0.
      destruct (Z.ltb_spec k 64).
      - rewrite Z.ones_spec_low by lia. destruct (Z.testbit x k); reflexivity.
      - rewrite Z.ones_spec_high by lia. rewrite (Z.bits_above_log2 x k); [reflexivity| lia| ].
        destruct (Z.eq_dec x 0) as [->|N]; [cbn; lia|]. assert (Z.log2 x < 64) by (apply Z.log2_lt_pow2; lia). lia. }
    pose proof (Z.add_nocarry_lxor _ _ LL) as A.
    rewrite (Z.lxor_comm x (Z.ones 64)) in A at 2. rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r in A. lia.
  Qed.

  Lemma ll_fill_loop : forall (N : nat) (cx : ictx) (ly : ilay) (st : ist) (cs : Z) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x1 x6 x7 x11 x15 x17 x23 x28 x29 x30 x31 : word) (m : amem) (j : Z),
    (Z.to_nat (19 - j) <= N)%nat -> t_shave st <= j -> 0 <= j < 19 ->
    itcall_env AI rng_fs L RNG LB tp ly -> GARM2 cx ly 0x8f54c CODELENS ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LENLENS -> sinv cx st lf cf -> (forall i, 0 <= i < j -> lf (order_f i) <= 7) -> inf_arr_ok cx wf fo ->
    inf_vis cx ly (st_cin st cs) lf cf wf fo payload v0 v8 v16 v24 v240 v328 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    evtF bsegs RNG POST
      (* [U14B] A2 2026-11-12: the 1.4 combined fill loop (0x8f394 .. 0x8f3f4; 1.3.1 0x8ee58 .. 0x8eeb8): the loop offset
         2 j is in a3 (1.3.1 t0), codes in t0 (0x8f37c ld t0,88(s1); 1.3.1 t1), bits saved in s6 (0x8f358 mv s6,t0;
         1.3.1 t2), the have shadow in s3 (0x8f35c; 1.3.1 s6), avail_in in s4, next_in in s10, hold in s7, shadow base
         in s5, shadow(F0) in s8 (1.3.1 s3, s5, s8, s9, s4). &next is no longer kept in a register (0x8f438 loads it). *)
      (MS (mkR x1 (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (c_p cx + 1384)) x6 x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               (Z_to_bv 64 (141376 + 2 * j)) x11 (Z_to_bv 64 141376) (Z_to_bv 64 (2 * j)) (Z_to_bv 64 (141376 + 2 * j)) x15 (Z_to_bv 64 (j + 1)) x17
               (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (Z.shiftr (c_p cx + 156) 3 + 2147450880)) (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 2147450880)
               (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x23 (Z_to_bv 64 (c_q cx + t_cin st))
               (Z_to_bv 64 (l_F0 ly)) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x8f384) fc None m (seg_rom bsegs)).
  Proof.
    induction N as [|N IH]; intros until j; intros HN HSJ HJ ENV HCL CTX PAYR PLEN MODE SI L7 ARR VIS HID KA; [lia|].
    destruct (ll_mode_facts _ _ _ _ SI MODE) as (NC1 & NC2 & SH0 & SH1 & _ & RLF).
    pose proof (order_f_range j ltac:(lia)) as ORJ.
    inf_arm_open_s.
    destruct (order_check m j SHOR SHO6 ltac:(lia)) as (b & RDB & CK).
    zrung [0x8f398].
    zs. rewrite sxb_sval.
    ck_branchJ 15 0x8f3a0 CK.
    pose proof (order_read m j _ MI ltac:(lia) eq_refl) as RDO.
    zs. rewrite (zx16_small (order_f j)) by lia. clear RDO.
    zs. setreg 11 (Z_to_bv 64 (2 * order_f j)) ltac:(rewrite shl1_2x; reflexivity).
    zs. setreg 15 (Z_to_bv 64 (18446744073709551615 - (S + 168))) ltac:(rewrite lxor_ones64 by lia; reflexivity).
    zrung [0x8f3cc].
    assert (SOK : store_ok bsegs m (Z_to_bv 64 (S + 168 + 2 * order_f j)) 2 = true)
      by (eapply (f16arr_store_ok bsegs m (S + 168) 320 lf (order_f j)); [exact LENS| lia| reflexivity]).
    zstep.
    pose proof (f16arr_write bsegs m (S + 168) 320 lf (order_f j) (Z_to_bv 64 0) 0 LENS ltac:(lia) eq_refl) as LENS'.
    store_done.
    pose proof (lens_rng_upd lf (order_f j) 0 RLF ltac:(lia)) as RLF'.
    pose proof (lens7_upd lf j 0 L7 ltac:(lia)) as L7'.
    zrung [0x8f3e4].
    replace (141376 + 2 * j + 2) with (141376 + 2 * (j + 1)) by lia. replace (2 * j + 2) with (2 * (j + 1)) by lia.
    zs. zbr0 KJ.
    -
      replace (j + 2) with (j + 1 + 1) by lia.
      eapply (IH (ICX u S D n 6341056 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cs (fupd lf (order_f j) 0) cf wf fo
                 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (j + 1));
        [lia| icx_cbn; lia| lia| exact ENV| exact HCL| exact CTX0| exact PAYR| exact PLEN| exact MODE
        | exact (proj1 (sinv_have _ _ lf cf shave (fupd lf (order_f j) 0) SI MODE SH0 SH1 RLF' ltac:(intros i Hi; apply L7'; icx_cbn; lia)))
        | exact L7'| exact ARR| inf_vis_close_sn| inf_hid_close| exact KA].
    -
      (* [U14B] A2 2026-11-12: ll_call's 1.4 entry is the join 0x8f438 (see InfB_llcall) *)
      zrung [0x8f428].
      assert (L19 : forall i, 0 <= i < 19 -> fupd lf (order_f j) 0 (order_f i) <= 7) by (intros i Hi; apply L7'; lia).
      destruct (sinv_have _ _ lf cf 19 (fupd lf (order_f j) 0) SI MODE ltac:(lia) ltac:(lia) RLF' L19) as (SI19 & ME19).
      unfold st_sh in SI19, ME19. icx_cbn.
      eapply (ll_call AI rng_fs L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (ICX u S D n 6341056 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
                (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist 19 nx whave wnext) cs (fupd lf (order_f j) 0) cf wf fo);
        [exact ENV| exact HCL| exact CTX0| exact PAYR| exact PLEN| exact MODE| reflexivity| exact SI19| exact ARR| inf_vis_close_sn| inf_hid_close
        | eapply KALL_mono; [| exact KA]; exact ME19].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.

  Lemma ll_fill : forall (cx : ictx) (ly : ilay) (st : ist) (cs : Z) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x1 x6 x7 x11 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31 : word) (m : amem),
    itcall_env AI rng_fs L RNG LB tp ly -> GARM2 cx ly 0x8f54c CODELENS ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LENLENS -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    inf_vis cx ly (st_cin st cs) lf cf wf fo payload v0 v8 v16 v24 v240 v328 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    evtF bsegs RNG POST
      (* [U14B] A2 2026-11-12: the 1.4 file at 0x8f35c: bits in t0 and already saved in s6 (0x8f358 mv s6,t0), avail_in in
         s4, next_in in s10, hold in s7, shadow base in s5, shadow(F0) in s8; s3 is free (0x8f35c sets it) *)
      (MS (mkR x1 (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (t_bits st)) x6 x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               (Z_to_bv 64 (c_p cx + 156)) x11 (Z_to_bv 64 141376) x13 x14 x15 x16 x17
               (Z_to_bv 64 (l_Zs ly)) x22 (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 2147450880)
               (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x23 (Z_to_bv 64 (c_q cx + t_cin st))
               (Z_to_bv 64 (l_F0 ly)) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x8f34c) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros ENV HCL CTX PAYR PLEN MODE SI ARR VIS HID KA.
    destruct (ll_mode_facts _ _ _ _ SI MODE) as (NC1 & NC2 & SH0 & SH1 & L7 & RLF).
    inf_arm_open_s.
    zrung [0x8f370].
    zs. zbr0 KH.
    -
      eapply (ll_call AI rng_fs L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (ICX u S D n 6341056 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
                (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cs lf cf wf fo);
        [exact ENV| exact HCL| exact CTX0| exact PAYR| exact PLEN| exact MODE| icx_cbn; lia| exact SI| exact ARR| exact VISf| exact HID| exact KA].
    - zrung [0x8f384].
      (* [U14B] A2 2026-11-12: the order table is at 141376 (0x22840) at 1.4; the mover had moved one of the two literals *)
      rewrite ?shl1_2x. replace (2 * shave + 141376) with (141376 + 2 * shave) by lia.
      eapply (ll_fill_loop (Z.to_nat (19 - shave)) (ICX u S D n 6341056 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cs lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ shave);
        [lia| icx_cbn; lia| lia| exact ENV| exact HCL| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact L7| exact ARR| exact VISf| exact HID| exact KA].
  Qed.
End S.
End CANSEC1.
