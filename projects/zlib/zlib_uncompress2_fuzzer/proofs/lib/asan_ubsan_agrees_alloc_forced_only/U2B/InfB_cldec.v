(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AObj U2AStore InfAGlue InfPure InfPure_type InfPure_w7 InfPure_w7d InfPure_w7e InfAGlue_w7 InfAGlue_w7b InfPure_table InfPure_codelens.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfBTables InfB_w7base InfB_w7tab InfB_w7pull InfB_w6base InfB_w6kit InfB_w6garm InfB_cldone_base InfB_clbase InfB_w7tab16 InfB_clreg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2B Require Import U2BKit U2BKit_p04 InfBTraps.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
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
  Notation HIDm cx ly m := (inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m).
  Notation CLH cx ly N := (clhead_stmt cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh N).
  Notation CLR cx ly N := (clres_stmt cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh N).

  Definition CLDEC_MS (cx : ictx) (ly : ilay) (st : ist) (ci H B : Z) (x10 x14 x19 : word) (m : amem) : machine_state :=
    MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (c_p cx + 1384)) (Z_to_bv 64 (Z.shiftl (c_n cx - t_cin st) 32)) (Z_to_bv 64 (2 ^ t_lb st - 1))
            (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
            x10 (Z_to_bv 64 (c_q cx + ci)) (Z_to_bv 64 (t_lb st)) (Z_to_bv 64 (H mod 2 ^ t_lb st)) x14
            (Z_to_bv 64 (Z.shiftr (c_p cx + 156) 3 + 2147450880)) (Z_to_bv 64 (t_shave st)) (Z_to_bv 64 (t_nlen st + t_ndist st))
            (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (c_n cx - t_cin st)) x19 (Z_to_bv 64 2147450880) (Z_to_bv 64 1)
            (Z_to_bv 64 H) (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (- B)) (Z_to_bv 64 (c_n cx - ci)) (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (c_q cx + t_cin st))
            (Z_to_bv 64 B) (Z_to_bv 64 (c_n cx - ci)) (Z_to_bv 64 B))
       FR (Z_to_bv 64 0x8f900) fc None m (seg_rom bsegs).

  Lemma cl_decode : forall (M N : nat) (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z)
      (v0 v8 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x10 x14 x19 : word) (m : amem) (ci H B : Z),
    CLR cx ly N ->
    (Z.to_nat (t_nlen st + t_ndist st - t_shave st) <= S N)%nat -> t_shave st < t_nlen st + t_ndist st ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = CODELENS -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    inf_vis cx ly (st_cin st ci) lf cf wf fo payload v0
        (Z_to_bv 64 (Z.shiftr (c_p cx + 152) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (c_p cx + 148) 3 + 2147450880)) v8 (Z_to_bv 64 (t_nlen st))
        (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    c_n cx - ci < Z.of_nat M ->
    t_cin st <= ci <= c_n cx -> B = t_bits st + 8 * (ci - t_cin st) -> 0 <= H < 2 ^ B -> B <= 40 ->
    evtF bsegs RNG POST (CLDEC_MS cx ly st ci H B x10 x14 x19 m).
  Proof.
    induction M as [|M IH]; intros until B; intros HRES HN HJN CTX PAYR PLEN MODE SI ARR VIS HID KA HM HC HBE HH HB40; [lia|].
    pose proof KA as (KD & KB & KL & KLV).
    destruct (cl_facts _ _ _ _ SI MODE) as (NL1 & NL2 & ND1 & ND2 & SH0 & SH1 & L15 & LC0 & LB1 & LB15 & NX0 & NX1 & TOK & RLF & RCF).
    assert (CB15 : forall i, 0 <= i < 2 ^ t_lb st -> 1 <= code_bits (rdc cf (CDyn 0) i) <= 15 /\ 2 ^ t_lb st <= t_nx st).
    { intros i Hi. destruct (ctab_bits cf (t_lb st) (t_nx st) i TOK Hi) as (A & C). unfold rdc. rewrite Z.add_0_l. split; [lia| exact C]. }
    pose proof (sinv_bits_facts _ _ _ _ SI) as (CIN0 & CINN & BITS0 & BLE & HOLD0).
    unfold CLDEC_MS.
    revert IH HRES. inf_arm_open_s. intros IH HRES.
    match goal with HA : _ <= ATOP <= _ |- _ => rename HA into ATB end.
    pose proof (pow2_le_15 lb ltac:(clear - LB1 LB15; lia)) as P15.
    assert (IDX0 : 0 <= H mod 2 ^ lb < 2 ^ lb) by (apply mod_pow2_bound; clear - LB1; lia).
    destruct (CB15 _ IDX0) as (CBE & NXR).
    assert (IND0 : 0 <= H mod 2 ^ lb < nx) by (clear - IDX0 NXR; lia).
    remember (H mod 2 ^ lb) as i0 eqn:EI0. apply w7hide_in in EI0.
    pose proof (dtab_dyn m S cf 0 nx CODES RCF ltac:(clear; lia) NX0 ltac:(clear - NX1; lia)) as DT.
    pose proof (dtab16_dyn m S cf 0 nx CODES RCF ltac:(clear; lia) NX0 ltac:(clear - NX1; lia)) as DT16.
    replace (S + 1384 + 4 * 0) with (S + 1384) in DT, DT16 by (clear; lia).
    destruct (DT i0 IND0) as (RDR & RD0 & RD1 & RD2). pose proof (DT16 i0 IND0) as RDL. clear DT DT16.
    pose proof (tab_sh0 m S 897 (S + 1384 + 4 * i0) SHS S8 ltac:(clear - IND0 NX1; lia) ltac:(clear - S1; lia)) as RDS.
    pose proof (tab_sh_acc RNG S 897 (S + 1384 + 4 * i0) RSS S8 ltac:(clear - IND0 NX1; lia) ltac:(clear - S1; lia)) as ACS.
    pose proof (tab_sh0 m S 897 (S + 1384 + 4 * i0 + 3) SHS S8 ltac:(clear - IND0 NX1; lia) ltac:(clear - S1; lia)) as RDS3.
    pose proof (tab_sh_acc RNG S 897 (S + 1384 + 4 * i0 + 3) RSS S8 ltac:(clear - IND0 NX1; lia) ltac:(clear - S1; lia)) as ACS3.
    set (c0 := rdc cf (CDyn 0) i0) in *.
    zs. rewrite shl2. zs.
    setreg 13 (Z_to_bv 64 (S + 1384 + 4 * i0)) ltac:(f_equal; clear; lia).
    zs. zs. zs. zs.
    zs. zs. zs. zs. zs.
    zs. zs.
    pose proof (code_val_range c0) as CVR. pose proof (code_bits_range c0) as CBR.
    assert (LO16 : 0 <= Z.land c0 65535 < 65536) by (change 65535 with (Z.ones 16); rewrite Z.land_ones by (clear; lia); apply Z.mod_pos_bound; clear; lia).
    rewrite !zx16_small by (first [exact CVR | exact LO16]).
    eapply (cl_join RNG POST) with (c := c0); [exact RDR|]. intros x10'.
    pose proof (pow2_le_40 B ltac:(clear - HB40 HBE HC BITS0; lia)) as P40.
    zs. zbr0 KBB.
    -
      apply w7hide_out in EI0. subst c0 i0.
      eapply (HRES (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m ci H B);
        [exact HN| exact HJN| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA
        | | | | | ]; clear - HC HBE HH HB40 KBB; gcbn; lia.
    -
      zs. zbr0 KH.
      2: {
        zrung [0x9366c].
        assert (ECI : ci = n) by (clear - KH HC NR CIN0; lia). subst ci.
        replace (Z.shiftl (n - cin) 3 + bits) with B by (rewrite Z.shiftl_mul_pow2 by (clear; lia); clear - HBE; lia).
        lazymatch goal with HF : rw_cells bsegs _ SPA _ |- _ =>
          replace (D + cin + (n - cin) mod 4294967296) with (D + n) in HF by (rewrite Z.mod_small by (clear - NR HC CIN0; lia); clear; lia) end.
        replace (Z_to_bv 64 0) with (Z_to_bv 64 (n - n)) by (f_equal; clear; lia).
        destruct (sinv_pull _ _ lf cf n H B SI ltac:(gcbn; clear - HC; lia) ltac:(gcbn; clear; lia) ltac:(clear - HBE HC BITS0; lia) ltac:(exact HB40) ltac:(clear - HH; lia) ltac:(clear - HH; lia)
                    ltac:(gcbn; clear - HBE BLE HC; lia) ltac:(gcbn; clear - HBE; lia)) as (SI1 & _).
        st_norm SI1.
        eapply (KLV (IST mode last flags n cout H B out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ret lf cf wf fo);
          [exact SI1| exact ARR| inf_vis_close| inf_hid_close]. }
      assert (CIR : 0 <= ci < n) by (clear - CIN0 HC KH; lia).
      destruct (pull_facts RNG _ m m D n payload ci UNP MU DJP RD RSD PAYB PAYR PLEN D16 D1 CIR) as (b & RDB & CK & ACP & RDP & ACB & BZR).
      eapply (cl_pull_g RNG POST) with (A := D + ci) (B := B); [clear - D1 CIR DL2 ATB; lia| clear - HB40 HBE HC BITS0; lia|]. intros x10''.
      zs. zs. zs. rewrite sxb_sval.
      eapply (cl_ck_dec RNG POST) with (A := D + ci) (sb := sval b); [clear - D1 CIR DL2 ATB; lia| exact CK|]. intros y10.
      zs. zs. cbv beta. rewrite (bz_val payload ci PAYR).
      eapply (cl_pull_a RNG POST) with (H := H) (B := B) (c := bz payload ci) (lb := lb) (TA := S + 1384);
        [exact BZR| clear - HB40 HBE HC BITS0; lia| exact HH| clear - LB1 LB15; lia| clear - S1 S2 ATB; lia|]. intros z10.
      pose proof (pull_bound H B (bz payload ci) ltac:(clear - HBE HC BITS0; lia) ltac:(clear - HH; lia) BZR) as PB.
      set (H1 := H + bz payload ci * 2 ^ B) in *.
      assert (IDX1 : 0 <= H1 mod 2 ^ lb < 2 ^ lb) by (apply mod_pow2_bound; clear - LB1; lia).
      zs. zs. zs.
      eapply (cl_pull_b RNG POST) with (B := B) (av := n - ci) (EA := S + 1384 + 4 * (H1 mod 2 ^ lb)) (NX1 := D + ci + 1);
        [clear - HB40 HBE HC BITS0; lia| clear - CIR NR; lia| clear - S1 S2 ATB IDX1 P15; lia|]. intros w10.
      replace (D + ci + 1) with (D + (ci + 1)) by (clear; lia). replace (n - ci - 1) with (n - (ci + 1)) by (clear; lia).
      lazymatch goal with HF : rw_cells bsegs _ SPA _ |- _ => replace (D + ci + 1) with (D + (ci + 1)) in HF by (clear; lia) end.
      apply w7hide_out in EI0. subst c0 i0.
      eapply (IH N (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ci + 1) H1 (B + 8));
        [exact HRES| exact HN| exact HJN| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| inf_vis_close_sn| inf_hid_close| exact KA
        | | | | | ]; clear - HM HC CIR HBE PB KBB CBE HB40; gcbn; lia.
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.

  Lemma cl_head : forall (N : nat) (cx : ictx) (ly : ilay), CLR cx ly N -> CLH cx ly (S N).
  Proof.
    intros N cx ly HRES. unfold clhead_stmt, CLHEAD_MS. intros until m. intros HN HJN CTX PAYR PLEN MODE SI ARR VIS HID KA.
    destruct (cl_facts _ _ _ _ SI MODE) as (NL1 & NL2 & ND1 & ND2 & SH0 & SH1 & L15 & LC0 & LB1 & LB15 & NX0 & NX1 & TOK & RLF & RCF).
    pose proof (sinv_bits_facts _ _ _ _ SI) as (CIN0 & CINN & BITS0 & BLE & HOLD0).
    revert HRES. inf_arm_open. intros HRES.
    match goal with HA : _ <= ATOP <= _ |- _ => rename HA into ATB end.
    pose proof (pow2_le_40 bits ltac:(clear - BITS0; lia)) as P40.
    eapply (cl_hidx RNG POST) with (H := hold) (lb := lb) (TA := S + 1384);
      [clear - HOLD0 P40; lia| clear - LB1 LB15; lia| clear - S1 S2 ATB; lia|]. intros x11'.
    zs.
    eapply (cl_hregs RNG POST) with (B := bits) (av := n - cin) (NX := D + cin); [clear - BITS0; lia| clear - CIN0 CINN NR; lia|].
    zs. zs.
    eapply (cl_decode (Datatypes.S (Z.to_nat (n - cin))) N (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
              (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cin hold bits);
      [exact HRES| exact HN| exact HJN| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| inf_vis_close_sn| inf_hid_close| exact KA
      | | | | | ]; clear - CIN0 CINN HOLD0 BITS0; gcbn; lia.
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.
End S.
End CANSEC1.
