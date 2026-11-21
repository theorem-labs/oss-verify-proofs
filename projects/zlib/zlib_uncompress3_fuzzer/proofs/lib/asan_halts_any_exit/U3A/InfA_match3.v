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
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_w7 InfPure_w7d InfPure_w7e InfPure_w7f InfAGlue_w7 InfAGlue_w7b.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U3A Require Import U2AObj U2AClient U2AIface InfABase InfAKit InfATables InfA_w7base InfA_w7tab InfA_w7pull.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U2A Require Import InfPure_w7g.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U3A Require Import InfAGlue_p04 InfA_match1 InfA_match2.
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
  Notation GARM cx ly Lb X := (garm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).


  (* the 1.3.1 register homes of M_G, M_J moved to 1.4 by tools/regmap_text_gr.py (t2>s6 s4>s8 s5>s10 s6>t5 s7>s9 s8>s11 s9>s5 s10>s4 s11>s7 t3>t6 t4>t3 t5>t4 t6>t2) *)
  Definition M_J (cx : ictx) (ly : ilay) (st : ist) (from c : Z) (x1 x5 x6 x7 x11 x12 x15 x16 : word) (m : amem) : machine_state :=
    MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 (Z_to_bv 64 (c_p cx + 56)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
            (Z_to_bv 64 (l_F0 ly)) x11 x12 (Z_to_bv 64 c) (Z_to_bv 64 from) x15 x16 (Z_to_bv 64 (6336512 + t_cout st))
            (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 2147450880)
            x7 x1 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly)) (* 1.3.1 kept the mode pointer in s11 here; 1.4 keeps it in ra, and the x1 parameter names s7 (probe Pg30match3) *)
            (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 (c_p cx + 28)) (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880))
            (Z_to_bv 64 (c_p cx + 108)))
       FR (Z_to_bv 64 0x917d4) fc None m (seg_rom asegs).
  Definition M_G (cx : ictx) (ly : ilay) (st : ist) (from c : Z) (x1 x5 x6 x7 x11 x12 x15 x16 : word) (m : amem) : machine_state :=
    MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 (Z_to_bv 64 (c_p cx + 56)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
            (Z_to_bv 64 (l_F0 ly)) x11 x12 (Z_to_bv 64 c) (Z_to_bv 64 from) x15 x16 (Z_to_bv 64 (6336512 + t_cout st))
            (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 2147450880)
            x7 x1 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly)) (* 1.3.1 kept the mode pointer in s11 here; 1.4 keeps it in ra, and the x1 parameter names s7 (probe Pg30match3) *)
            (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 (c_p cx + 28)) (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880))
            (Z_to_bv 64 (c_p cx + 108)))
       FR (Z_to_bv 64 0x917dc) fc None m (seg_rom asegs).

  Lemma m_after : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf : Z -> Z) (v0 v8 v16 v240 j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word) (c : Z),
    inf_ctx cx ly AI RNG LB -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = MATCH -> sinv cx st lf cf -> KALLB cx ly (meas cx st) ->
    1 <= c <= t_length st -> t_length st < 65536 -> t_cout st + c <= c_osz cx ->
    forall fo' x1' x5' x7' x11 x12 x14 x16 x17 m', inf_arr_ok cx wf fo' ->
      VIS cx ly (st_le st MATCH (t_length st - c) (t_extra st)) lf cf wf fo' v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) v240 (Z_to_bv 64 (c_q cx + t_cin st)) j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m' -> HIDm cx ly m' ->
      evtF asegs RNG POST (M_A gp tp FR fc cx ly (st_le st MATCH (t_length st - c) (t_extra st)) c x1' x5' x7' x11 x12 x14 x16 x17 m').
  Proof.
    intros until c. intros CTX PLEN MODE SI KA HC LEN16 HCO. intros fo' x1' x5' x7' x11 x12 x14 x16 x17 m' ARR' VIS' HID'.
    pose proof (RNG_len_set _ _ lf cf (t_length st - c) (proj1 SI) ltac:(lia)) as RN1. rewrite MODE in RN1.
    eapply (m_tail AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly (st_le st MATCH (t_length st - c) (t_extra st)) lf cf wf fo'
              v0 v8 v240 j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad c (meas cx st)); (* m_tail no longer binds v16 *)
      [exact CTX| exact PLEN| exact RN1| exact ARR'| exact VIS'| exact HID'| exact KA| reflexivity| cbn [st_le t_length]; lia| lia| cbn [st_le t_cout]; exact HCO| lia| ].
    intros md HMD. cbn [st_le t_length] in HMD.
    destruct (sinv_upd cx st lf cf md c (t_length st - c) SI (or_introl MODE) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(destruct HMD as [(-> & NZ)|(-> & _)]; [left; split; [reflexivity| split; [exact MODE| lia]]| right; reflexivity])) as (SI2 & ME2).
    destruct st as [mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext]. exact (conj SI2 ME2).
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Qed.
  Lemma m_go_o : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v240 j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (fi c : Z) (x1 x5 x6 x7 x11 x12 x15 x16 : word) (m : amem),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = MATCH -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) v240 (Z_to_bv 64 (c_q cx + t_cin st)) j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    0 <= fi <= t_cout st ->
    1 <= c <= t_length st -> c <= c_osz cx - t_cout st ->
    evtF asegs RNG POST (M_G cx ly st (6336512 + fi) c x1 x5 x6 x7 x11 x12 x15 x16 m).
  Proof.
    intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA HFI HC HCL.
    destruct (sinv_match_facts _ _ _ _ SI MODE) as (LEN1 & LEN16 & OFF).
    pose proof (proj1 SI) as RN1. unfold IDefs.RNG in RN1. destruct RN1 as (_ & _ & COUT0 & COUTN & _).
    pose proof (m_after cx ly st lf cf wf v0 v8 v16 v240 j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad c CTX PLEN MODE SI KA HC LEN16 ltac:(lia)) as KAFT.
    pose proof (RNG_len_set _ _ lf cf (t_length st - c) (proj1 SI) ltac:(lia)) as RNL. rewrite MODE in RNL.
    unfold M_G. revert KAFT RNL. inf_arm_open. intros KAFT RNL. subst mode.
    clear R13.
    Time zrunb [0x917f4].
    zs.
    Time zrunb [0x91804].
    replace (6336512 + fi) with (6336512 + fi + 0) by (clear; lia).
    replace (6336512 + cout) with (6336512 + cout + 0) by (clear; lia).
    replace (Z_to_bv 64 c) with (Z_to_bv 64 (c - 0)) at 2 by (f_equal; clear; lia).
    eapply (m_loop_o AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (Datatypes.S (Z.to_nat c)) (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST MATCH last flags cin cout hold bits out ret (len - c) offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf
              v0 v8 v240 (Z_to_bv 64 (D + cin)) j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad fi c fo 0);
      [exact CTX0| exact PAYR| exact PLEN| exact RNL| exact ARR| inf_vis_close| inf_hid_close| clear - HFI; lia| clear - HFI; gcbn; lia
      | clear - HCL COUT0; gcbn; lia| clear - LEN16 HC; lia| clear - HC; lia| clear - HC; lia| exact KAFT].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Time Qed.

  Lemma m_go_w : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v240 j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (fi c : Z) (x1 x5 x6 x7 x11 x12 x15 x16 : word) (m : amem),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = MATCH -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) v240 (Z_to_bv 64 (c_q cx + t_cin st)) j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    c_w cx <> 0 -> 0 <= fi -> fi + c <= 32768 ->
    1 <= c <= t_length st -> c <= c_osz cx - t_cout st ->
    evtF asegs RNG POST (M_G cx ly st (c_w cx + fi) c x1 x5 x6 x7 x11 x12 x15 x16 m).
  Proof.
    intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA WNZ HWI0 HWI1 HC HCL.
    destruct (sinv_match_facts _ _ _ _ SI MODE) as (LEN1 & LEN16 & OFF).
    pose proof (proj1 SI) as RN1. unfold IDefs.RNG in RN1. destruct RN1 as (_ & _ & COUT0 & COUTN & _).
    pose proof (m_after cx ly st lf cf wf v0 v8 v16 v240 j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad c CTX PLEN MODE SI KA HC LEN16 ltac:(lia)) as KAFT.
    pose proof (RNG_len_set _ _ lf cf (t_length st - c) (proj1 SI) ltac:(lia)) as RNL. rewrite MODE in RNL.
    pose proof HID as (AHW & _ & _ & _ & WINH & _). destruct (WINH WNZ) as (SHW & FW).
    pose proof CTX as (_ & _ & (ps & HPS & _) & (FuW & HFUW & ZSEW & _) & _).
    assert (WFACTS : 6807552 <= c_w cx /\ c_w cx + 32768 <= 140737488355328 /\ c_w cx mod 8 = 0 /\ rng RNG (c_w cx) 32768 /\ rng RNG (Z.shiftr (c_w cx) 3 + 2147450880) 4096
                     /\ (c_w cx + 32768 <= c_p cx \/ c_p cx + 7176 <= c_w cx)).
    { destruct CTX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WDC & _).
      destruct WDC as [W0E|(W16 & WAB & (pw & HPW) & RW & RWS)]; [exfalso; exact (WNZ W0E)|].
      pose proof (ablk_lin _ _ WAB) as (WB1 & _ & _ & WB4). unfold AIMG_HI in WB1. change (2 ^ 47) with 140737488355328 in WB4.
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB pw (c_w cx) 32768) (HB ps (c_p cx) 7176) AHW HPW HPS ltac:(intros Y; inversion Y)) as DWS. cbn [ab_addr ab_size] in DWS.
      split; [lia|]. split; [lia|]. split; [clear - W16; Z.div_mod_to_equations; lia|]. split; [exact RW|]. split; [exact RWS| exact DWS]. }
    destruct WFACTS as (WLO & WHI & W8 & RW & RWS & DWS).
    assert (CWS : exists cW : Z, 0 <= cW <= 1 /\ c_w cx + 32768 <= c_p cx + cW * 2 ^ 48 /\ c_p cx + 7176 <= c_w cx + (1 - cW) * 2 ^ 48).
    { destruct CTX as (_ & SBW & _). pose proof (ablk_lin _ _ SBW) as (_ & SW0 & _ & SW4). change (2 ^ 47) with 140737488355328 in SW4.
      destruct DWS as [DW|DW]; [exists 0| exists 1]; lia. }
    destruct CWS as (cW & CW0 & CW1 & CW2). clear DWS.
    unfold M_G. revert KAFT RNL. inf_arm_open. intros KAFT RNL. subst mode.
    clear R13.
    Time zrunb [0x917f4].
    zs.
    Time zrunb [0x91804].
    replace (Wd + fi) with (Wd + fi + 0) by (clear; lia).
    assert (DJW : disjoint_from [(lo, SPA + 536); (Zs, Zs + 112); (S, S + 7176); (6336512, 6336512 + osz)] (Z.shiftr Wd 3 + 2147450880) (Z.shiftr Wd 3 + 2147450880 + 4096 - (Z.shiftr Wd 3 + 2147450880))).
    { cbn [disjoint_from]. rewrite !Z.shiftr_div_pow2 by (clear; lia). change (2 ^ 3) with 8.
      clear - WLO WHI LOC ZSE BU0 BU1 BU2 BS0 BS1 BS2 OSZ. pose proof atop_range. Z.div_mod_to_equations. lia. }
    replace (6336512 + cout) with (6336512 + cout + 0) by (clear; lia).
    replace (Z_to_bv 64 c) with (Z_to_bv 64 (c - 0)) at 2 by (f_equal; clear; lia).
    eapply (m_loop_w AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (Datatypes.S (Z.to_nat c)) (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST MATCH last flags cin cout hold bits out ret (len - c) offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf
              v0 v8 v240 (Z_to_bv 64 (D + cin)) j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad fi c fo 0);
      [exact CTX0| exact PAYR| exact PLEN| exact RNL| exact ARR| inf_vis_close| inf_hid_close| exact FW| exact (sh0_mu _ _ _ _ _ SHW MU DJW)| exact DJW| exact RW| exact RWS| exact W8| exact WLO| exact WHI| exact HWI0| exact HWI1
      | clear - HCL COUT0; gcbn; lia| clear - LEN16 HC; lia| clear - HC; lia| clear - HC; lia| exact KAFT].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Time Qed.
  Lemma m_join_o : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (fi c : Z) (x1 x5 x6 x7 x11 x12 x15 x16 : word) (m : amem),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = MATCH -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) v240 (Z_to_bv 64 (c_q cx + t_cin st)) j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    0 <= fi <= t_cout st ->
    1 <= c <= t_length st -> 1 <= c_osz cx - t_cout st ->
    evtF asegs RNG POST (M_J cx ly st (6336512 + fi) c x1 x5 x6 x7 x11 x12 x15 x16 m).
  Proof.
    intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA HFI HC HL1.
    destruct (sinv_match_facts _ _ _ _ SI MODE) as (LEN1 & LEN16 & OFF).
    pose proof (proj1 SI) as RN1. unfold IDefs.RNG in RN1. destruct RN1 as (_ & _ & COUT0 & COUTN & _).
    unfold M_J.
    inf_arm_open.
    clear R13.
    zs. zbr0 KC.
    -
      eapply (m_go_o (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fi c);
        [exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| exact HFI| exact HC| clear - KC; gcbn; lia].
    -
      zs.
      eapply (m_go_o (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fi (osz - cout));
        [exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| exact HFI| clear - KC HC HL1; gcbn; lia| clear; gcbn; lia].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Time Qed.

  Lemma m_join_w : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (fi c : Z) (x1 x5 x6 x7 x11 x12 x15 x16 : word) (m : amem),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = MATCH -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) v240 (Z_to_bv 64 (c_q cx + t_cin st)) j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    c_w cx <> 0 -> 0 <= fi -> fi + c <= 32768 ->
    1 <= c <= t_length st -> 1 <= c_osz cx - t_cout st ->
    evtF asegs RNG POST (M_J cx ly st (c_w cx + fi) c x1 x5 x6 x7 x11 x12 x15 x16 m).
  Proof.
    intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA WNZ HWI0 HWI1 HC HL1.
    destruct (sinv_match_facts _ _ _ _ SI MODE) as (LEN1 & LEN16 & OFF).
    pose proof (proj1 SI) as RN1. unfold IDefs.RNG in RN1. destruct RN1 as (_ & _ & COUT0 & COUTN & _).
    unfold M_J.
    inf_arm_open.
    clear R13.
    zs. zbr0 KC.
    -
      eapply (m_go_w (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fi c);
        [exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| exact WNZ| exact HWI0| exact HWI1| exact HC| clear - KC; gcbn; lia].
    -
      zs.
      eapply (m_go_w (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fi (osz - cout));
        [exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| exact WNZ| exact HWI0| clear - KC HWI1; gcbn; lia| clear - KC HC HL1; gcbn; lia| clear; gcbn; lia].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Time Qed.
End S.
End CANSEC1.
