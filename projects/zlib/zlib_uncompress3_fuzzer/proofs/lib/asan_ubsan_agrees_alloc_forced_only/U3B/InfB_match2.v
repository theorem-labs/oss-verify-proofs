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
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_w7 InfPure_w7d InfPure_w7e InfPure_w7f InfAGlue_w7 InfAGlue_w7b.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U3B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfBTables InfB_w7base InfB_w7tab InfB_w7pull.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import InfPure_w7g.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U3B Require Import InfBGlue_p04 U2BCall InfB_match1.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U3B Require Import U2BKit U2BKit_p04 InfBTraps.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
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

  Notation KALLB cx ly B := (KALL cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh B).
  Notation VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m :=
    (inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m).
  Notation HIDm cx ly m := (inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m).
  Notation GARM cx ly Lb X := (garm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).

  Definition M_G (cx : ictx) (ly : ilay) (st : ist) (from c : Z) (x5 x6 x10 x11 x12 x16 x17 x19 x21 x22 x23 x26 x29 x30 x31 : word) (m : amem) : machine_state :=
    MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly)) x10 x11 x12
            (Z_to_bv 64 c) (Z_to_bv 64 from) (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3 + 2147450880)) x16 x17
            (Z_to_bv 64 (l_Zs ly)) x19 x21 (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 (t_hold st))
            (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x23 x26 (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (t_bits st)) x29 x30 x31)
       FR (Z_to_bv 64 0x9258c) fc None m (seg_rom bsegs).

  Lemma m_go_o : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (fi c : Z) (x5 x6 x10 x11 x12 x16 x17 x19 x21 x22 x23 x26 x29 x30 x31 : word) (m : amem),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = MATCH -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    0 <= fi <= t_cout st ->
    1 <= c <= t_length st -> c <= c_osz cx - t_cout st ->
    evtF bsegs RNG POST (M_G cx ly st (6341952 + fi) c x5 x6 x10 x11 x12 x16 x17 x19 x21 x22 x23 x26 x29 x30 x31 m).
  Proof.
    intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA HFI HC HCL.
    pose proof KA as (KD & KB & KL & KLV).
    destruct (sinv_match_facts _ _ _ _ SI MODE) as (LEN1 & LEN16 & OFF).
    pose proof (proj1 SI) as RN1. unfold IDefs.RNG in RN1. destruct RN1 as (_ & _ & COUT0 & COUTN & _).
    unfold M_G. inf_arm_open. subst mode.
    destruct (pay_out_sep _ _ _ _ _ CTX0) as (cOD & COD0 & COD1 & COD2). cbn [c_q c_n] in COD1, COD2.
    clear R13.
    zrung [0x925b4].

    replace (6341952 + fi) with (6341952 + fi + 0) by (clear; lia).
    replace (6341952 + cout) with (6341952 + cout + 0) by (clear; lia).
    replace (Z_to_bv 64 c) with (Z_to_bv 64 (c - 0)) by (f_equal; clear; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (sh0_mu _ _ _ _ _ SHO MU DJO) as SHOc;
      callqd (m_loop_o RNG FR fc (Datatypes.S (Z.to_nat c)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc mc osz cout fi c 0 fo) dropping OUT end.
    all: lazymatch goal with
         | |- evtF _ _ _ _ => idtac
         | |- munch _ _ _ => apply munch_refl
         | |- wmono _ _ _ => apply wmono_refl
         | |- mem_inv _ _ => eassumption
         | |- f8arr _ _ _ _ _ => exact OUT
         | |- shadow_bytes _ _ _ _ => exact SHOc
         | |- rng _ 6341952 _ => exact ROB
         | |- rng _ _ _ => exact ROBS
         | |- _ => clear - HFI HC HCL COUT0 COUTN OSZ LEN16; gcbn; lia
         end.

    lazymatch goal with PCX : f8arr bsegs _ 6341952 _ ?fx, PO : forall i : Z, 0 <= ?fx i < 256 |- _ =>
      assert (ARR' : inf_arr_ok (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) wf fx) by (split; [exact (proj1 ARR)| intros i _; apply PO]) end.
    zrung [0x92650].
    replace (6341952 + cout + c) with (6341952 + (cout + c)) in * by (clear; lia).
    replace (osz - cout - c) with (osz - (cout + c)) in * by (clear; lia).
    zs. zbr0 KLEN.
    -
      zrung [0x8e5ec].
      destruct (sinv_upd _ _ lf cf LEN c (len - c) SI (or_introl eq_refl) ltac:(clear - HC; lia) ltac:(clear - HCL; gcbn; lia) ltac:(clear - HC; lia) ltac:(clear - HC; gcbn; lia)
                  (or_intror eq_refl)) as (SI2 & ME2).
      unfold st_upd in SI2, ME2. st_norm SI2. st_norm ME2.
      lazymatch goal with PCX : f8arr bsegs _ 6341952 _ ?fx |- _ =>
        eapply (KD (IST LEN last flags cin (cout + c) hold bits out ret (len - c) offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fx);
          [exact SI2| exact ME2| exact ARR'| change LEN with 16200; inf_vis_close| inf_hid_close] end.
    -
      zrung [0x8e5ec].
      destruct (sinv_upd _ _ lf cf MATCH c (len - c) SI (or_introl eq_refl) ltac:(clear - HC; lia) ltac:(clear - HCL; gcbn; lia) ltac:(clear - HC; lia) ltac:(clear - HC; gcbn; lia)
                  ltac:(left; split; [reflexivity| split; [reflexivity| clear - KLEN HC R15; lia]])) as (SI2 & ME2).
      unfold st_upd in SI2, ME2. st_norm SI2. st_norm ME2.
      lazymatch goal with PCX : f8arr bsegs _ 6341952 _ ?fx |- _ =>
        eapply (KD (IST MATCH last flags cin (cout + c) hold bits out ret (len - c) offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fx);
          [exact SI2| exact ME2| exact ARR'| change MATCH with 16204; inf_vis_close| inf_hid_close] end.
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.

  Lemma m_go_w : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (wi c : Z) (x5 x6 x10 x11 x12 x16 x17 x19 x21 x22 x23 x26 x29 x30 x31 : word) (m : amem),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = MATCH -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    c_w cx <> 0 -> 0 <= wi -> wi + c <= 32768 ->
    1 <= c <= t_length st -> c <= c_osz cx - t_cout st ->
    evtF bsegs RNG POST (M_G cx ly st (c_w cx + wi) c x5 x6 x10 x11 x12 x16 x17 x19 x21 x22 x23 x26 x29 x30 x31 m).
  Proof.
    intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA WNZ HWI0 HWI1 HC HCL.
    pose proof KA as (KD & KB & KL & KLV).
    destruct (sinv_match_facts _ _ _ _ SI MODE) as (LEN1 & LEN16 & OFF).
    pose proof (proj1 SI) as RN1. unfold IDefs.RNG in RN1. destruct RN1 as (_ & _ & COUT0 & COUTN & _).
    pose proof HID as (AHW & _ & _ & _ & WINH & _). destruct (WINH WNZ) as (SHW & FW).
    pose proof CTX as (_ & _ & (ps & HPS & _) & (FuW & HFUW & ZSEW & _) & _).
    assert (WFACTS : 6675648 <= c_w cx /\ c_w cx + 32768 <= 140737488355328 /\ c_w cx mod 8 = 0 /\ rng RNG (c_w cx) 32768 /\ rng RNG (Z.shiftr (c_w cx) 3 + 2147450880) 4096
                     /\ (c_w cx + 32768 <= c_p cx \/ c_p cx + 7176 <= c_w cx) /\ c_w cx + 32768 <= ATOP).
    { destruct CTX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WDC & _).
      destruct WDC as [W0E|(W16 & WAB & (pw & HPW) & RW & RWS)]; [exfalso; exact (WNZ W0E)|].
      pose proof (ablk_lin _ _ WAB) as (WB1 & _ & WB3 & WB4). unfold AIMG_HI in WB1. change (2 ^ 47) with 140737488355328 in WB4.
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB pw (c_w cx) 32768) (HB ps (c_p cx) 7176) AHW HPW HPS ltac:(intros Y; inversion Y)) as DWS. cbn [ab_addr ab_size] in DWS.
      split; [lia|]. split; [lia|]. split; [clear - W16; Z.div_mod_to_equations; lia|]. split; [exact RW|]. split; [exact RWS|]. split; [exact DWS| exact WB3]. }
    destruct WFACTS as (WLO & WHI & W8 & RW & RWS & DWS & WTOP).
    assert (CWS : exists cW : Z, 0 <= cW <= 1 /\ c_w cx + 32768 <= c_p cx + cW * 2 ^ 48 /\ c_p cx + 7176 <= c_w cx + (1 - cW) * 2 ^ 48).
    { destruct CTX as (_ & SBW & _). pose proof (ablk_lin _ _ SBW) as (_ & SW0 & _ & SW4). change (2 ^ 47) with 140737488355328 in SW4.
      destruct DWS as [DW|DW]; [exists 0| exists 1]; lia. }
    destruct CWS as (cW & CW0 & CW1 & CW2). clear DWS.
    unfold M_G. inf_arm_open. subst mode.
    destruct (pay_out_sep _ _ _ _ _ CTX0) as (cOD & COD0 & COD1 & COD2). cbn [c_q c_n] in COD1, COD2.
    clear R13.
    assert (DJW : disjoint_from [(lo, SPA + 568); (Zs, Zs + 112); (S, S + 7176); (6341952, 6341952 + osz)] (Z.shiftr Wd 3 + 2147450880) (Z.shiftr Wd 3 + 2147450880 + 4096 - (Z.shiftr Wd 3 + 2147450880))).
    { cbn [disjoint_from]. rewrite !Z.shiftr_div_pow2 by (clear; lia). change (2 ^ 3) with 8.
      clear - WLO WHI LOC ZSE BU0 BU1 BU2 BS0 BS1 BS2 OSZ. pose proof atop_range. Z.div_mod_to_equations. lia. }
    zrung [0x925b4].
    replace (Wd + wi) with (Wd + wi + 0) by (clear; lia).
    replace (6341952 + cout) with (6341952 + cout + 0) by (clear; lia).
    replace (Z_to_bv 64 c) with (Z_to_bv 64 (c - 0)) by (f_equal; clear; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (sh0_mu _ _ _ _ _ SHO MU DJO) as SHOc; pose proof (sh0_mu _ _ _ _ _ SHW MU DJW) as SHWc;
      callqd (m_loop_w RNG FR fc (Datatypes.S (Z.to_nat c)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc mc osz cout Wd wi c 0 fo fw) dropping OUT end.
    all: lazymatch goal with
         | |- evtF _ _ _ _ => idtac
         | |- munch _ _ _ => apply munch_refl
         | |- wmono _ _ _ => apply wmono_refl
         | |- mem_inv _ _ => eassumption
         | |- f8arr _ _ 6341952 _ _ => exact OUT
         | |- f8arr _ _ _ _ _ => eassumption
         | |- shadow_bytes _ 2148243624 _ _ => exact SHOc
         | |- shadow_bytes _ _ _ _ => exact SHWc
         | |- rng _ 6341952 _ => exact ROB
         | |- rng _ 2148243624 _ => exact ROBS
         | |- rng _ (Z.shiftr _ _ + _) _ => exact RWS
         | |- rng _ _ _ => exact RW
         | |- _ mod 8 = 0 => exact W8
         | |- _ => clear - HWI0 HWI1 HC HCL COUT0 COUTN OSZ LEN16 WLO WHI; gcbn; lia
         end.

    lazymatch goal with PCX : f8arr bsegs _ 6341952 _ ?fx, PO : forall i : Z, 0 <= ?fx i < 256 |- _ =>
      assert (ARR' : inf_arr_ok (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) wf fx) by (split; [exact (proj1 ARR)| intros i _; apply PO]) end.
    zrung [0x92650].
    replace (6341952 + cout + c) with (6341952 + (cout + c)) in * by (clear; lia).
    replace (osz - cout - c) with (osz - (cout + c)) in * by (clear; lia).
    zs. zbr0 KLEN.
    -
      zrung [0x8e5ec].
      destruct (sinv_upd _ _ lf cf LEN c (len - c) SI (or_introl eq_refl) ltac:(clear - HC; lia) ltac:(clear - HCL; gcbn; lia) ltac:(clear - HC; lia) ltac:(clear - HC; gcbn; lia)
                  (or_intror eq_refl)) as (SI2 & ME2).
      unfold st_upd in SI2, ME2. st_norm SI2. st_norm ME2.
      lazymatch goal with PCX : f8arr bsegs _ 6341952 _ ?fx |- _ =>
        eapply (KD (IST LEN last flags cin (cout + c) hold bits out ret (len - c) offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fx);
          [exact SI2| exact ME2| exact ARR'| change LEN with 16200; inf_vis_close| inf_hid_close] end.
    -
      zrung [0x8e5ec].
      destruct (sinv_upd _ _ lf cf MATCH c (len - c) SI (or_introl eq_refl) ltac:(clear - HC; lia) ltac:(clear - HCL; gcbn; lia) ltac:(clear - HC; lia) ltac:(clear - HC; gcbn; lia)
                  ltac:(left; split; [reflexivity| split; [reflexivity| clear - KLEN HC R15; lia]])) as (SI2 & ME2).
      unfold st_upd in SI2, ME2. st_norm SI2. st_norm ME2.
      lazymatch goal with PCX : f8arr bsegs _ 6341952 _ ?fx |- _ =>
        eapply (KD (IST MATCH last flags cin (cout + c) hold bits out ret (len - c) offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fx);
          [exact SI2| exact ME2| exact ARR'| change MATCH with 16204; inf_vis_close| inf_hid_close] end.
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.
End S.
End CANSEC1.
