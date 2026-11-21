(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* inflate_state arrays at their 1.4 offsets (lens 168, work 808, codes 1384, sane 7160; 1.3.1: 152, 792, 1368, 7144) *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_type InfPure_w7 InfPure_table InfPure_itab InfPure_lenlens ItAPure.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U1A Require Import U2AObj U2AClient U2AIface InfABase InfAKit InfA_w7base InfA_w6base InfA_w6kit U2AIface_fit2_draft InfA_itcall InfA_llcall.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
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
  Variable rng_fs : alayout -> footprint -> Prop.
  Variables (L : alayout) (RNG : footprint) (stA : astate) (LB : list ablock).
  Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (POST : machine_state -> Prop).
  Variables (LBc : list ablock) (m0 : amem) (payload : list Z) (fw : Z -> Z) (saved fk fksh : list cell).

  Notation KALLB cx ly B := (KALL cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh B).
  Notation VIS cx ly st lf cf wf fo v0 v8 v16 v240 v504 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m :=
    (inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v240 v504 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m).
  Notation HIDm cx ly m := (inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m).
  Notation GARM2 cx ly Lb X := (garm2_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).

  (* the 1.4 fill loop head 0x8ef64 (lens[order[j]] = 0 while j < 19).  a0 = a7 =
     &order[j] (141376 = 0x22840), a4 = j + 1, a2 = 0xffffffff, t0 = codes, a1 = &lencode, a3 = &next (from 0x8ef28 ..
     0x8ef38), t1 = &have, t2 = lens, s7 = (S+156)sh; the GARM homes for the rest (s4 = hold, s10 = next_in, s11 = the
     input left, t4 = left).  Slot 496 is stale in LENLENS, so vnext is free. *)
  Lemma ll_fill_loop : forall (N : nat) (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z)
      (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x1 x11 x15 x16 x22 x28 x30 x31 : word) (m : amem) (j : Z),
    (Z.to_nat (19 - j) <= N)%nat -> t_shave st <= j -> 0 <= j < 19 ->
    itcall_env AI rng_fs L RNG LB tp ly -> GARM2 cx ly 0x8f16c CODELENS ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LENLENS -> sinv cx st lf cf -> (forall i, 0 <= i < j -> lf (order_f i) <= 7) -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) v240 (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    evtF asegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (c_p cx + 1384)) (Z_to_bv 64 (c_p cx + 156)) (Z_to_bv 64 (c_p cx + 168)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               (Z_to_bv 64 (141376 + 2 * j)) x11 (Z_to_bv 64 4294967295) (Z_to_bv 64 (c_p cx + 160)) (Z_to_bv 64 (j + 1)) x15 x16 (Z_to_bv 64 (141376 + 2 * j))
               (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 2147450880)
               x22 (Z_to_bv 64 (Z.shiftr (c_p cx + 156) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly))
               (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) x28 (Z_to_bv 64 (c_osz cx - t_cout st)) x30 x31)
          FR (Z_to_bv 64 0x8efb4) fc None m (seg_rom asegs)).
  Proof.
    induction N as [|N IH]; intros until j; intros HN HSJ HJ ENV HCL CTX PAYR PLEN MODE SI L7 ARR VIS HID KA; [lia|].
    destruct (ll_mode_facts _ _ _ _ SI MODE) as (NC1 & NC2 & SH0 & SH1 & _ & RLF).
    pose proof (order_f_range j ltac:(lia)) as ORJ.
    inf_arm_open.
    destruct (order_check m j SHOR SHO6 ltac:(lia)) as (b & RDB & CK).
    zs. zs. zs. rewrite sxb_sval.
    ck_branchJ 15 0x8efc4 CK.
    pose proof (order_read m j _ MI ltac:(lia) eq_refl) as RDO.
    zs. rewrite (zx16_small (order_f j)) by lia. clear RDO.
    zs. setreg 11 (Z_to_bv 64 (2 * order_f j)) ltac:(rewrite shl1_2x; reflexivity).
    zs. zs. zs. zs. zs.
    assert (SOK : store_ok asegs m (Z_to_bv 64 (S + 168 + 2 * order_f j)) 2 = true)
      by (eapply (f16arr_store_ok asegs m (S + 168) 320 lf (order_f j)); [exact LENS| lia| reflexivity]).
    zstep.
    pose proof (f16arr_write asegs m (S + 168) 320 lf (order_f j) (Z_to_bv 64 0) 0 LENS ltac:(lia) eq_refl) as LENS'.
    store_done.
    pose proof (lens_rng_upd lf (order_f j) 0 RLF ltac:(lia)) as RLF'.
    pose proof (lens7_upd lf j 0 L7 ltac:(lia)) as L7'.
    zs. setreg 11 (Z_to_bv 64 (j + 1)) ltac:(rewrite land_m32 by lia; reflexivity).
    zs. zs. zs. zs.
    replace (141376 + 2 * j + 2) with (141376 + 2 * (j + 1)) by lia.
    zs. zbr0 KJ.
    -
      replace (j + 2) with (j + 1 + 1) by lia.
      eapply (IH (ICX u S D n 6335680 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
                 (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) (fupd lf (order_f j) 0) cf wf fo
                 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (j + 1));
        [lia| icx_cbn; lia| lia| exact ENV| exact HCL| exact CTX0| exact PAYR| exact PLEN| exact MODE
        | exact (proj1 (sinv_have _ _ lf cf shave (fupd lf (order_f j) 0) SI MODE SH0 SH1 RLF' ltac:(intros i Hi; apply L7'; icx_cbn; lia)))
        | exact L7'| exact ARR| inf_vis_close| inf_hid_close| exact KA].
    -
      zrunb [0x8f03c].
      assert (L19 : forall i, 0 <= i < 19 -> fupd lf (order_f j) 0 (order_f i) <= 7) by (intros i Hi; apply L7'; lia).
      destruct (sinv_have _ _ lf cf 19 (fupd lf (order_f j) 0) SI MODE ltac:(lia) ltac:(lia) RLF' L19) as (SI19 & ME19).
      unfold st_sh in SI19, ME19. icx_cbn.
      eapply (ll_call AI rng_fs L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (ICX u S D n 6335680 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
                (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist 19 nx whave wnext) (fupd lf (order_f j) 0) cf wf fo);
        [exact ENV| exact HCL| exact CTX0| exact PAYR| exact PLEN| exact MODE| reflexivity| exact SI19| exact ARR| inf_vis_close| inf_hid_close
        | eapply KALL_mono; [| exact KA]; exact ME19].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Qed.
  (* ll_fill at its 1.4 pc 0x8ef28, reached from the arm's bgeu at 0x8e798 (have >=
     ncode) and from the read loop's exit (0x8e84c -> 0x8ef24 mv a6,a3).  a6 = have, t1 = &have, t2 = lens, s7 =
     (S+156)sh, and the GARM homes for the rest.  0x8ef28 .. 0x8ef38 load a0 a2 a1 a3 t0, then bltu: have > 18 ->
     0x8efec (ll_call); else the fill setup -> 0x8ef64. *)
  Lemma ll_fill : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z)
      (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x1 x5 x10 x11 x12 x13 x14 x15 x17 x22 x28 x30 x31 : word) (m : amem),
    itcall_env AI rng_fs L RNG LB tp ly -> GARM2 cx ly 0x8f16c CODELENS ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LENLENS -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) v240 (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    evtF asegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (l_SPA ly)) gp tp x5 (Z_to_bv 64 (c_p cx + 156)) (Z_to_bv 64 (c_p cx + 168)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               x10 x11 x12 x13 x14 x15 (Z_to_bv 64 (t_shave st)) x17
               (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 2147450880)
               x22 (Z_to_bv 64 (Z.shiftr (c_p cx + 156) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly))
               (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) x28 (Z_to_bv 64 (c_osz cx - t_cout st)) x30 x31)
          FR (Z_to_bv 64 0x8ef78) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros ENV HCL CTX PAYR PLEN MODE SI ARR VIS HID KA.
    destruct (ll_mode_facts _ _ _ _ SI MODE) as (NC1 & NC2 & SH0 & SH1 & L7 & RLF).
    inf_arm_open.
    zs. zs. zs. zs. zs. zs. zbr0 KH.
    -
      eapply (ll_call AI rng_fs L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (ICX u S D n 6335680 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
                (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact ENV| exact HCL| exact CTX0| exact PAYR| exact PLEN| exact MODE| icx_cbn; lia| exact SI| exact ARR| exact VISf| exact HID| exact KA].
    - zs. zs. zs. zs.
      zs. setreg 17 (Z_to_bv 64 (2 * shave)) ltac:(rewrite shl1_2x; reflexivity).
      zs. zs. setreg 17 (Z_to_bv 64 (141376 + 2 * shave)) ltac:(f_equal; lia).
      zs. zs.
      eapply (ll_fill_loop (Z.to_nat (19 - shave)) (ICX u S D n 6335680 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
                (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ shave);
        [lia| icx_cbn; lia| lia| exact ENV| exact HCL| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact L7| exact ARR| exact VISf| exact HID| exact KA].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Qed.
End S.
End CANSEC1.
