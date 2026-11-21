(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AObj U2AClient U2AStore U2AIface InfABase InfAKit InfAGlue InfATables InfPure InfPure_type InfPure_w7 InfPure_w7d InfPure_w7e InfAGlue_w7 InfAGlue_w7b InfA_w7base InfA_w7tab InfA_w7pull InfPure_table InfPure_lenlens InfPure_codelens InfPure_codelens2 InfA_w6base InfA_w6kit InfA_cldone_base InfA_clbase InfA_clbase2 InfA_clreg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
  Notation VIS cx ly st lf cf wf fo v0 v8 v16 v240 v504 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m :=
    (inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v240 v504 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m).
  Notation HIDm cx ly m := (inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m).
  Notation CLK cx ly N := (clchk_stmt cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh N).
  Notation CLP cx ly pc N := (clrep_stmt cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh pc N).

  (* the repeat-17 tail at 1.4's 0x8f718 (li t2,0): t4 = next_in (already in slot 496 on both paths), stored again at 0x8f7b0 before CLCHK *)
  Definition CLX_MS (cx : ictx) (ly : ilay) (st : ist) (ci H B hb : Z) (x7 x11 x19 x22 x23 x28 : word) (m : amem) : machine_state :=
    (MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (2 ^ t_lb st - 1)) (Z_to_bv 64 B) x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
             (Z_to_bv 64 (l_F0 ly)) x11 (Z_to_bv 64 (t_nlen st)) (Z_to_bv 64 hb) (Z_to_bv 64 (Z.shiftr (c_p cx + 156) 3 + 2147450880)) (Z_to_bv 64 (t_nlen st + t_ndist st)) (Z_to_bv 64 (c_p cx + 1384))
             (Z_to_bv 64 (t_shave st))
             (Z_to_bv 64 (l_Zs ly)) x19 (Z_to_bv 64 H) (Z_to_bv 64 2147450880)
             x22 x23 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly))
             (Z_to_bv 64 (Z.shiftr (c_p cx + 152) 3 + 2147450880)) (Z_to_bv 64 (c_n cx - ci)) x28 (Z_to_bv 64 (c_q cx + ci)) (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880)) (Z_to_bv 64 (c_p cx + 108)))
        FR (Z_to_bv 64 0x8f748) fc None m (seg_rom asegs)).

  Lemma cl_x17_chk : forall (N : nat) (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z)
      (v0 v240 j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x7 x11 x19 x22 x23 x28 : word) (m : amem) (ci H B hb : Z),
    CLK cx ly N ->
    (Z.to_nat (t_nlen st + t_ndist st - t_shave st) <= S N)%nat -> t_shave st < t_nlen st + t_ndist st ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = CODELENS -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3))
        v240 (Z_to_bv 64 (Z.shiftr (c_p cx + 148) 3 + 2147450880)) (Z_to_bv 64 (c_q cx + ci)) j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    t_cin st <= ci <= c_n cx -> B = t_bits st + 8 * (ci - t_cin st) -> 0 <= H < 2 ^ B -> B <= 40 -> 1 <= hb <= 15 -> hb + 3 <= B ->
    evtF asegs RNG POST (CLX_MS cx ly st ci H B hb x7 x11 x19 x22 x23 x28 m).
  Proof.
    intros until hb. intros HCHK HN HJN CTX PAYR PLEN MODE SI ARR VIS HID KA HC HBE HH HB40 HHB HNB.
    pose proof (buf_ok_pulled _ _ _ _ ci H B SI HC HBE HH HB40) as BUF.
    pose proof (buf_ok_drop _ _ ci H B hb BUF ltac:(clear - HHB HNB; lia)) as BUF1.
    pose proof (buf_ok_drop _ _ ci (H / 2 ^ hb) (B - hb) 3 BUF1 ltac:(clear - HHB HNB; lia)) as BUF2.
    change (2 ^ 3) with 8 in BUF2.
    pose proof (Z.mod_pos_bound (H / 2 ^ hb) 8 ltac:(clear; lia)) as CPR.
    unfold CLX_MS.
    revert HCHK. inf_arm_open. intros HCHK.
    eapply (cl_x17 RNG POST) with (H := H) (B := B) (hb := hb); [exact HH| clear - HHB; lia| exact HNB| exact HB40|].
    zs. (* sd t4,496(s1) at 0x8f7b0 *)
    eapply (HCHK (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ci (H / 2 ^ hb / 8) (B - hb - 3) (H / 2 ^ hb mod 8 + 3) 0);
      [exact HN| exact HJN| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| inf_vis_close| inf_hid_close| exact KA| exact BUF2
      | clear - CPR; lia| clear; lia].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Qed.

  (* the repeat-17 pull loop head at 1.4's 0x8f5ec (bnez s11): a1 = the next_in shadow cursor, t1 = t3 = B, t2 = hb + 3; next_in lives in slot 496, reloaded into t4 and stored back every byte (0x8f604 / 0x8f628) *)
  Definition CLPULL_MS (cx : ictx) (ly : ilay) (st : ist) (ci H B hb : Z) (x19 x22 x23 x29 : word) (m : amem) : machine_state :=
    (MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (2 ^ t_lb st - 1)) (Z_to_bv 64 B) (Z_to_bv 64 (hb + 3)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
             (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (c_q cx + ci)) (Z_to_bv 64 (t_nlen st)) (Z_to_bv 64 hb) (Z_to_bv 64 (Z.shiftr (c_p cx + 156) 3 + 2147450880)) (Z_to_bv 64 (t_nlen st + t_ndist st)) (Z_to_bv 64 (c_p cx + 1384))
             (Z_to_bv 64 (t_shave st))
             (Z_to_bv 64 (l_Zs ly)) x19 (Z_to_bv 64 H) (Z_to_bv 64 2147450880)
             x22 x23 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly))
             (Z_to_bv 64 (Z.shiftr (c_p cx + 152) 3 + 2147450880)) (Z_to_bv 64 (c_n cx - ci)) (Z_to_bv 64 B) x29 (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880)) (Z_to_bv 64 (c_p cx + 108)))
        FR (Z_to_bv 64 0x8f61c) fc None m (seg_rom asegs)).

  Lemma cl_pull17 : forall (M N : nat) (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z)
      (v0 v240 j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x19 x22 x23 x29 : word) (m : amem) (ci H B hb : Z),
    CLK cx ly N ->
    (Z.to_nat (t_nlen st + t_ndist st - t_shave st) <= S N)%nat -> t_shave st < t_nlen st + t_ndist st ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = CODELENS -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3))
        v240 (Z_to_bv 64 (Z.shiftr (c_p cx + 148) 3 + 2147450880)) (Z_to_bv 64 (c_q cx + ci)) j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    c_n cx - ci < Z.of_nat M ->
    t_cin st <= ci <= c_n cx -> B = t_bits st + 8 * (ci - t_cin st) -> 0 <= H < 2 ^ B -> 1 <= hb <= 15 -> B < hb + 3 ->
    evtF asegs RNG POST (CLPULL_MS cx ly st ci H B hb x19 x22 x23 x29 m).
  Proof.
    induction M as [|M IH]; intros until hb; intros HCHK HN HJN CTX PAYR PLEN MODE SI ARR VIS HID KA HM HC HBE HH HHB HBX; [lia|].
    pose proof KA as (KD & KB & KL & KLV).
    pose proof (sinv_bits_facts _ _ _ _ SI) as (CIN0 & CINN & BITS0 & BLE & HOLD0).
    unfold CLPULL_MS.
    revert IH HCHK. inf_arm_open. intros IH HCHK.
    match goal with HA : _ <= ATOP <= _ |- _ => rename HA into ATB end.
    pose proof (pow2_le_40 B ltac:(clear - HBX HHB HBE HC BITS0; lia)) as P40.
    zs. zbr0 KH.
    2: {
      zrunb [0x92900].
      assert (ECI : ci = n) by (clear - KH HC; lia). subst ci.
      replace (Z_to_bv 64 0) with (Z_to_bv 64 (n - n)) by (f_equal; clear; lia).
      assert (SPF : cin <= n /\ n <= n /\ 0 <= B /\ B <= 40 /\ 0 <= H /\ H < 2 ^ B /\ B <= 8 * n /\ 8 * (n - n) + B <= 8 * (n - cin) + bits) by (clear - CIN0 CINN BITS0 BLE HC HBE HH HBX HHB; lia).
      destruct (sinv_pull _ _ lf cf n H B SI ltac:(gcbn; tauto) ltac:(gcbn; tauto) ltac:(tauto) ltac:(tauto) ltac:(tauto) ltac:(tauto) ltac:(gcbn; tauto) ltac:(gcbn; tauto)) as (SI1 & _).
      st_norm SI1.
      eapply (KLV (IST mode last flags n cout H B out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ret lf cf wf fo);
        [exact SI1| exact ARR| inf_vis_close| exact HID]. }
    assert (CIR : 0 <= ci < n) by (clear - CIN0 HC KH; lia).
    destruct (pull_facts RNG _ m m D n payload ci UNP MU DJP RD RSD PAYB PAYR PLEN D16 D1 CIR) as (b & RDB & CK & ACP & RDP & ACB & BZR).
    zs. zs. zs. rewrite sxb_sval.
    ck_branchJc 30 0x8f634 CK. (* 1.4's shadow check 0x8f5f4 srl / add / lb, bnez; the partial check rejoins at 0x8f604 *)
    zs. zs. cbv beta. rewrite (bz_val payload ci PAYR). (* ld t4,496(s1); lbu t5,0(t4) *)
    eapply (cl_padv17 RNG POST) with (D := D) (n := n) (ci := ci) (H := H) (B := B) (c := bz payload ci);
      [exact BZR| clear - HBX HHB HBE HC BITS0; lia| exact HH| exact CIR| clear - NR; lia| clear - D1 DL2 ATB NR; lia|].
    pose proof (pull_bound H B (bz payload ci) ltac:(clear - HBE HC BITS0; lia) ltac:(clear - HH; lia) BZR) as PB.
    set (H1 := H + bz payload ci * 2 ^ B) in *.
    intros x30'. (* t5 = byte << B after the sll, free *)
    zs. zs. zs. zbr0 KB2. (* sd t4,496(s1); ld t5,448(s1); bltu t3,t2 *)
    -
      eapply (IH N (ICX u S D n 6336320 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ci + 1) H1 (B + 8) hb);
        [exact HCHK| exact HN| exact HJN| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| inf_vis_close| inf_hid_close| exact KA
        | | | | | exact HHB| ]; clear - HM HC CIR HBE PB KB2 HBX HHB; gcbn; lia.
    - zs.
      eapply (cl_x17_chk N (ICX u S D n 6336320 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ci + 1) H1 (B + 8) hb);
        [exact HCHK| exact HN| exact HJN| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| inf_vis_close| inf_hid_close| exact KA
        | | | | | exact HHB| ]; clear - HC CIR HBE PB KB2 HBX HHB; gcbn; lia.
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Qed.

  Lemma cl_rep17 : forall (N : nat) (cx : ictx) (ly : ilay), CLK cx ly N -> CLP cx ly 0x8f60c N.
  Proof.
    intros N cx ly HCHK. unfold clrep_stmt, CLREP_MS. intros until hb. intros HN HJN CTX PAYR PLEN MODE SI ARR VIS HID KA HC HBE HH HB40 HHB HBX.
    pose proof (sinv_bits_facts _ _ _ _ SI) as (CIN0 & CINN & BITS0 & BLE & HOLD0).
    revert HCHK. inf_arm_open. intros HCHK.
    zs. zs. zbr0 KNB.
    -
      zs.
      eapply (cl_x17_chk N (ICX u S D n 6336320 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m ci H B hb);
        [exact HCHK| exact HN| exact HJN| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA
        | exact HC| exact HBE| exact HH| exact HB40| exact HHB| clear - KNB; lia].
    - zs. zs.
      eapply (cl_pull17 (Datatypes.S (Z.to_nat (n - ci))) N (ICX u S D n 6336320 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m ci H B hb);
        [exact HCHK| exact HN| exact HJN| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA
        | clear - HC; gcbn; lia| exact HC| exact HBE| exact HH| exact HHB| clear - KNB; lia].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Qed.
End S.
End CANSEC1.
