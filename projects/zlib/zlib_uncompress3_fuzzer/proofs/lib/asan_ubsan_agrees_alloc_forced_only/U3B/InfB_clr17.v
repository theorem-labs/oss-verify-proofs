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
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_type InfPure_w7 InfPure_w7d InfPure_w7e InfAGlue_w7 InfAGlue_w7b InfPure_table InfPure_itab InfPure_lenlens InfPure_codelens UbFit2.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U3B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfBTables InfB_w7base InfB_w7tab InfB_w7pull InfB_w6base InfB_w6kit InfB_w6garm InfB_cldone_base InfB_clbase InfB_clbase2 InfB_w7tab16 InfB_clreg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U3B Require Import U2BKit U2BKit_p04 InfBTraps.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
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
  Variables (L : alayout) (RNG : footprint) (stA : astate) (LB : list ablock).
  Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (POST : machine_state -> Prop).
  Variables (LBc : list ablock) (m0 : amem) (payload : list Z) (fw : Z -> Z) (saved fk fksh : list cell).

  Notation KALLB cx ly B := (KALL cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh B).
  Notation VISC cx ly st cs lf cf wf fo v0 v8 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m :=
    (inf_vis cx ly (st_cin st cs) lf cf wf fo payload v0
        (Z_to_bv 64 (Z.shiftr (c_p cx + 152) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (c_p cx + 148) 3 + 2147450880)) v8 (Z_to_bv 64 (t_nlen st))
        (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m).
  Notation HIDm cx ly m := (inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m).
  Notation CLK cx ly N := (clchk_stmt cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh N).
  Notation CLP cx ly pc N := (clrep_stmt cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh pc N).

  Definition CLX_MS (cx : ictx) (ly : ilay) (st : ist) (ci H B c : Z) (x6 x10 x11 x13 x22 x23 x26 x30 x31 : word) (m : amem) : machine_state :=
    (MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (c_p cx + 1384)) x6 (Z_to_bv 64 (2 ^ t_lb st - 1)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
             x10 x11 (Z_to_bv 64 (t_lb st)) x13 (Z_to_bv 64 (code_bits c))
             (Z_to_bv 64 (Z.shiftr (c_p cx + 156) 3 + 2147450880)) (Z_to_bv 64 (t_shave st)) (Z_to_bv 64 (t_nlen st + t_ndist st))
             (Z_to_bv 64 (l_Zs ly)) x22 (Z_to_bv 64 (Z.shiftr c 8)) (Z_to_bv 64 2147450880) x23
             (Z_to_bv 64 H) (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x26 (Z_to_bv 64 (c_n cx - ci)) (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (c_q cx + ci)) (Z_to_bv 64 B) x30 x31)
        FR (Z_to_bv 64 0x8fd04) fc None m (seg_rom bsegs)).

  Lemma cl_x_chk : forall (N : nat) (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z)
      (v0 v8 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x6 x10 x11 x13 x22 x23 x26 x30 x31 : word) (m : amem) (cs ci H B c : Z),
    CLK cx ly N ->
    (Z.to_nat (t_nlen st + t_ndist st - t_shave st) <= S N)%nat -> t_shave st < t_nlen st + t_ndist st ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = CODELENS -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VISC cx ly st cs lf cf wf fo v0 v8 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    t_cin st <= ci <= c_n cx -> B = t_bits st + 8 * (ci - t_cin st) -> 0 <= H < 2 ^ B -> B <= 40 ->
    0 <= c < 4294967296 -> 1 <= code_bits c <= 15 -> code_bits c + 3 <= B ->
    evtF bsegs RNG POST (CLX_MS cx ly st ci H B c x6 x10 x11 x13 x22 x23 x26 x30 x31 m).
  Proof.
    intros until c. intros HCHK HN HJN CTX PAYR PLEN MODE SI ARR VIS HID KA HC HBE HH HB40 CR HHB HNB.
    pose proof (buf_ok_pulled _ _ _ _ ci H B SI HC HBE HH HB40) as BUF.
    pose proof (buf_ok_drop _ _ ci H B (code_bits c) BUF ltac:(clear - HHB HNB; lia)) as BUF1.
    pose proof (buf_ok_drop _ _ ci (H / 2 ^ code_bits c) (B - code_bits c) 3 BUF1 ltac:(clear - HHB HNB; lia)) as BUF2.
    change (2 ^ 3) with 8 in BUF2.
    pose proof (Z.mod_pos_bound (H / 2 ^ code_bits c) 8 ltac:(clear; lia)) as CPR.
    unfold CLX_MS.
    revert HCHK. inf_arm_open_s. intros HCHK.
    eapply (cl_x17 RNG POST) with (H := H) (B := B) (c := c); [exact CR| exact HHB| exact HH| exact HNB| exact HB40|]. intros x11'.
    zs.
    eapply (HCHK (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cs ci (H / 2 ^ code_bits c / 8) (B - code_bits c - 3) (H / 2 ^ code_bits c mod 8 + 3) 0);
      [exact HN| exact HJN| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| inf_vis_close_sn| inf_hid_close| exact KA| exact BUF2
      | clear - CPR; lia| clear; lia].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.

  Definition CLPULL_MS (cx : ictx) (ly : ilay) (st : ist) (cs ci H B c : Z) (x6 x10 x23 x26 x28 : word) (m : amem) : machine_state :=
    (MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (c_p cx + 1384)) x6 (Z_to_bv 64 (2 ^ t_lb st - 1)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
             x10 (Z_to_bv 64 (c_q cx + ci)) (Z_to_bv 64 (t_lb st)) (Z_to_bv 64 (c_q cx + ci)) (Z_to_bv 64 (code_bits c))
             (Z_to_bv 64 (Z.shiftr (c_p cx + 156) 3 + 2147450880)) (Z_to_bv 64 (t_shave st)) (Z_to_bv 64 (t_nlen st + t_ndist st))
             (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (code_bits c + 3)) (Z_to_bv 64 (Z.shiftr c 8)) (Z_to_bv 64 2147450880) x23
             (Z_to_bv 64 H) (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x26 (Z_to_bv 64 (c_n cx - ci)) (Z_to_bv 64 (l_F0 ly)) x28 (Z_to_bv 64 B) (Z_to_bv 64 (c_n cx - cs)) (Z_to_bv 64 B))
        FR (Z_to_bv 64 0x8fb94) fc None m (seg_rom bsegs)).

  Lemma cl_pull : forall (M N : nat) (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z)
      (v0 v8 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x6 x10 x23 x26 x28 : word) (m : amem) (cs ci H B c : Z),
    CLK cx ly N ->
    (Z.to_nat (t_nlen st + t_ndist st - t_shave st) <= S N)%nat -> t_shave st < t_nlen st + t_ndist st ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = CODELENS -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VISC cx ly st cs lf cf wf fo v0 v8 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    c_n cx - ci < Z.of_nat M ->
    t_cin st <= cs <= ci -> t_cin st <= ci <= c_n cx -> B = t_bits st + 8 * (ci - t_cin st) -> 0 <= H < 2 ^ B ->
    0 <= c < 4294967296 -> 1 <= code_bits c <= 15 -> B < code_bits c + 3 ->
    evtF bsegs RNG POST (CLPULL_MS cx ly st cs ci H B c x6 x10 x23 x26 x28 m).
  Proof.
    induction M as [|M IH]; intros until c; intros HCHK HN HJN CTX PAYR PLEN MODE SI ARR VIS HID KA HM HCS HC HBE HH CR HHB HBX; [lia|].
    pose proof KA as (KD & KB & KL & KLV).
    pose proof (sinv_bits_facts _ _ _ _ SI) as (CIN0 & CINN & BITS0 & BLE & HOLD0).
    unfold CLPULL_MS.
    revert IH HCHK. inf_arm_open_s. intros IH HCHK.
    match goal with HA : _ <= ATOP <= _ |- _ => rename HA into ATB end.
    pose proof (pow2_le_40 B ltac:(clear - HBX HHB HBE HC BITS0; lia)) as P40.
    zs. zbr0 KH.
    2: {
      zrung [0x93758].
      assert (ECI : ci = n) by (clear - KH HC NR CIN0; lia). subst ci.
      lazymatch goal with HF : rw_cells bsegs _ SPA _ |- _ =>
        replace (D + cs + (n - cs)) with (D + n) in HF by (clear; lia) end.
      replace (Z_to_bv 64 0) with (Z_to_bv 64 (n - n)) by (f_equal; clear; lia).
      destruct (sinv_pull _ _ lf cf n H B SI ltac:(gcbn; clear - HC; lia) ltac:(gcbn; clear; lia) ltac:(clear - HBE HC BITS0; lia) ltac:(clear - HBX HHB; lia) ltac:(clear - HH; lia) ltac:(clear - HH; lia)
                  ltac:(gcbn; clear - HBE BLE HC; lia) ltac:(gcbn; clear - HBE; lia)) as (SI1 & _).
      st_norm SI1.
      eapply (KLV (IST mode last flags n cout H B out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ret lf cf wf fo);
        [exact SI1| exact ARR| inf_vis_close| inf_hid_close]. }
    assert (CIR : 0 <= ci < n) by (clear - CIN0 HC KH; lia).
    destruct (pull_facts RNG _ m m D n payload ci UNP MU DJP RD RSD PAYB PAYR PLEN D16 D1 CIR) as (b & RDB & CK & ACP & RDP & ACB & BZR).
    eapply (cl_rg17 RNG POST) with (A := D + ci) (B := B) (av := n - ci); [clear - D1 CIR DL2 ATB; lia| clear - HBX HHB HBE HC BITS0; lia|]. intros x28'.
    zs. zs. zs. rewrite sxb_sval.
    eapply (cl_rck17 RNG POST) with (A := D + ci) (sb := sval b); [clear - D1 CIR DL2 ATB; lia| exact CK|]. intros y26.
    zs. cbv beta. rewrite (bz_val payload ci PAYR).
    eapply (cl_radv17 RNG POST) with (D := D) (n := n) (ci := ci) (H := H) (B := B) (c := bz payload ci);
      [exact BZR| clear - HBX HHB HBE HC BITS0; lia| exact HH| exact CIR| clear - NR; lia| clear - D1 DL2 ATB NR; lia|].
    pose proof (pull_bound H B (bz payload ci) ltac:(clear - HBE HC BITS0; lia) ltac:(clear - HH; lia) BZR) as PB.
    set (H1 := H + bz payload ci * 2 ^ B) in *.
    zs. zbr0 KB2.
    -
      eapply (IH N (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m cs (ci + 1) H1 (B + 8) c);
        [exact HCHK| exact HN| exact HJN| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA
        | | | | | | exact CR| exact HHB| ]; clear - HM HCS HC CIR HBE PB KB2 HBX HHB; gcbn; lia.
    - zs.
      eapply (cl_x_chk N (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m cs (ci + 1) H1 (B + 8) c);
        [exact HCHK| exact HN| exact HJN| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA
        | | | | | exact CR| exact HHB| ]; clear - HC CIR HBE PB KB2 HBX HHB; gcbn; lia.
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.

  Lemma cl_rep17 : forall (N : nat) (cx : ictx) (ly : ilay), CLK cx ly N -> CLP cx ly 0x8fb88 N.
  Proof.
    intros N cx ly HCHK. unfold clrep_stmt, CLREP_MS. intros until c. intros HN HJN CTX PAYR PLEN MODE SI ARR VIS HID KA HC HBE HH HB40 CR HHB HBX.
    pose proof (sinv_bits_facts _ _ _ _ SI) as (CIN0 & CINN & BITS0 & BLE & HOLD0).
    revert HCHK. inf_arm_open_s. intros HCHK.
    zs. zs. zbr0 KNB.
    -
      zs. zs.
      eapply (cl_x_chk N (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m ci ci H B c);
        [exact HCHK| exact HN| exact HJN| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA
        | exact HC| exact HBE| exact HH| exact HB40| exact CR| exact HHB| clear - KNB; lia].
    - zs.
      eapply (cl_pull (Datatypes.S (Z.to_nat (n - ci))) N (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m ci ci H B c);
        [exact HCHK| exact HN| exact HJN| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA
        | clear - HC; gcbn; lia| clear - HC; gcbn; lia| exact HC| exact HBE| exact HH| exact CR| exact HHB| clear - KNB; lia].
  Qed.
End S.
End CANSEC1.
