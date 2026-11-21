(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_w7 InfPure_w7d InfPure_w7e InfPure_w7f InfAGlue_w7 InfAGlue_w7b.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U3A Require Import U2AObj U2AClient U2AIface InfABase InfAKit InfATables InfA_w7base InfA_w7tab InfA_w7pull.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U3A Require Import InfAGlue_p04.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
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


  (* the 1.3.1 register homes of M_A, M_L moved to 1.4 by tools/regmap_text_gr.py (ra>s6 t2>ra s4>s8 s5>s10 s6>t5 s7>s9 s8>s11 s9>s5 s10>s4 s11>s7 t3>t6 t4>t3 t5>t4 t6>t2) *)
  (* in M_L and M_A, ra = S+8 (the mode pointer; 1.4 stores the mode through ra at 0x91864, sw a1,0(ra)) and s7 is the free x7, from the g27 probe Pg27match2; the 1.3.1 homes map had put S+8 in s7 and a free word in ra *)
  Definition M_L (cx : ictx) (ly : ilay) (st : ist) (from copy k : Z) (x1 x5 x6 x7 : word) (m : amem) : machine_state :=
    MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 (Z_to_bv 64 (c_p cx + 56)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
            (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (from + k)) (Z_to_bv 64 (6336512 + t_cout st + k)) (Z_to_bv 64 copy) (Z_to_bv 64 (from + k))
            (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3 + 2147450880)) (Z_to_bv 64 (copy - k)) (Z_to_bv 64 (6336512 + t_cout st + k))
            (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 2147450880)
            x1 x7 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly))
            (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 (c_p cx + 28)) (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880))
            (Z_to_bv 64 (c_p cx + 108)))
       FR (Z_to_bv 64 0x91804) fc None m (seg_rom asegs).
  Definition M_A (cx : ictx) (ly : ilay) (st : ist) (copy : Z) (x1 x5 x7 x11 x12 x14 x16 x17 : word) (m : amem) : machine_state :=
    MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 (Z_to_bv 64 (6336512 + t_cout st + copy)) (Z_to_bv 64 (c_p cx + 56)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
            (Z_to_bv 64 (l_F0 ly)) x11 x12 (Z_to_bv 64 copy) x14
            (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3 + 2147450880)) x16 x17
            (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 2147450880)
            x1 x7 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly))
            (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 (c_p cx + 28)) (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880))
            (Z_to_bv 64 (c_p cx + 108)))
       FR (Z_to_bv 64 0x91864) fc None m (seg_rom asegs).

  Lemma m_loop_o : forall (N : nat) (cx : ictx) (ly : ilay) (st : ist) (lf cf wf : Z -> Z) (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (fi copy : Z) (fo : Z -> Z) (k : Z) (x1 x5 x6 x7 : word) (m : amem),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    IDefs.RNG cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m ->
    0 <= fi -> fi <= t_cout st -> t_cout st + copy <= c_osz cx -> copy < 2147483648 ->
    0 <= k < copy -> copy - k < Z.of_nat N ->
    (forall fo' x1' x5' x7' x11 x12 x14 x16 x17 m', inf_arr_ok cx wf fo' ->
       VIS cx ly st lf cf wf fo' v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m' -> HIDm cx ly m' ->
       evtF asegs RNG POST (M_A cx ly st copy x1' x5' x7' x11 x12 x14 x16 x17 m')) ->
    evtF asegs RNG POST (M_L cx ly st (6336512 + fi) copy k x1 x5 x6 x7 m).
  Proof.
    induction N as [|N IH]; intros until m; intros CTX PAYR PLEN SI ARR VIS HID HFI0 HFI1 HCO HC31 HK HN KA; [lia|].
    unfold M_A in KA. unfold M_L.
    pose proof SI as RN1. unfold IDefs.RNG in RN1. destruct RN1 as (_ & _ & COUT0 & COUTN & _).
    revert IH KA. inf_arm_open_rn. intros IH KA.
    destruct (pay_out_sep _ _ _ _ _ CTX0) as (cOD & COD0 & COD1 & COD2). cbn [c_q c_n] in COD1, COD2.
    pose proof (sh0_mu _ _ _ _ _ SHO MU DJO) as SHOk.
    assert (OSZ2 : osz <= 262144) by (clear - OSZ; lia).
    pose proof (tab_sh0 m 6336512 32768 (6336512 + fi + k) SHOk eq_refl ltac:(clear - HFI0 HFI1 HK HCO OSZ2 COUT0; lia) ltac:(clear; lia)) as RSH1.
    pose proof (tab_sh_acc RNG 6336512 32768 (6336512 + fi + k) ROBS eq_refl ltac:(clear - HFI0 HFI1 HK HCO OSZ2 COUT0; lia) ltac:(clear; lia)) as ASH1.
    pose proof (tab_sh0 m 6336512 32768 (6336512 + cout + k) SHOk eq_refl ltac:(clear - HK HCO OSZ2 COUT0; lia) ltac:(clear; lia)) as RSH2.
    pose proof (tab_sh_acc RNG 6336512 32768 (6336512 + cout + k) ROBS eq_refl ltac:(clear - HK HCO OSZ2 COUT0; lia) ltac:(clear; lia)) as ASH2.
    assert (RDS : ov_read_bytes asegs m (Z_to_bv 64 (6336512 + fi + k)) 1 = Some [Z_to_bv 8 (fo (fi + k))])
      by (eapply (f8arr_read asegs m 6336512 (Z.to_nat osz) fo (fi + k)); [exact OUT| clear - HFI0 HFI1 HK HCO COUT0; lia| unfold wa; f_equal; clear; lia]).
    assert (ADS : acc_in RNG (Z_to_bv 64 (6336512 + fi + k), 1%nat))
      by (apply (rng_acc_litZ RNG 6336512 262144 _ 1%nat 1 ROB eq_refl); [clear; lia| clear - HFI0 HFI1 HK HCO OSZ2 COUT0; lia]).
    Time zrunb [0x91830].
    replace (6336512 + cout + k) with (6336512 + (cout + k)) by (clear; lia).
    assert (SOK : store_ok asegs m (Z_to_bv 64 (6336512 + (cout + k))) 1 = true)
      by (eapply (f8arr_store_ok asegs m 6336512 (Z.to_nat osz) fo (cout + k)); [exact OUT| clear - HK HCO COUT0; lia| reflexivity]).
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bs) _) =>
      destruct (out_write asegs m 6336512 (Z.to_nat osz) fo (cout + k) bs OUT ltac:(clear - HK HCO COUT0; lia) (length_le1 _)) as (fo' & OUT' & FOR') end.
    store_done.
    assert (ARR' : inf_arr_ok (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) wf fo') by (split; [exact (proj1 ARR)| intros i _; apply FOR']).
    Time zrunb [0x91844].
    zs. zbr0 KL.
    -
      replace (6336512 + fi + k + 1) with (6336512 + fi + (k + 1)) by (clear; lia).
      replace (6336512 + (cout + k) + 1) with (6336512 + cout + (k + 1)) by (clear; lia).
      replace (copy - k + -1) with (copy - (k + 1)) by (clear; lia).
      eapply (IH (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fi copy fo' (k + 1));
        [exact CTX0| exact PAYR| exact PLEN| exact SI| exact ARR'| inf_vis_close| inf_hid_close| exact HFI0| exact HFI1| exact HCO| exact HC31
        | clear - HK KL; gcbn; lia| clear - HN; lia| exact KA].
    -
      zs.
      replace (6336512 + (cout + k) + 1) with (6336512 + cout + copy) by (clear - KL HK; lia).
      eapply (KA fo'); [exact ARR'| inf_vis_close| inf_hid_close].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Time Qed.

  Lemma m_loop_w : forall (N : nat) (cx : ictx) (ly : ilay) (st : ist) (lf cf wf : Z -> Z) (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (wi copy : Z) (fo : Z -> Z) (k : Z) (x1 x5 x6 x7 : word) (m : amem),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    IDefs.RNG cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m ->
    f8arr asegs m (c_w cx) (Z.to_nat 32768) fw ->
    shadow_bytes m (Z.shiftr (c_w cx) 3 + 2147450880) (Z.shiftr (c_w cx) 3 + 2147450880 + 4096) (fun _ => 0) ->
    disjoint_from [(l_lo ly, l_SPA ly + 536); (l_Zs ly, l_Zs ly + 112); (c_p cx, c_p cx + 7176); (6336512, 6336512 + c_osz cx)] (Z.shiftr (c_w cx) 3 + 2147450880) (Z.shiftr (c_w cx) 3 + 2147450880 + 4096 - (Z.shiftr (c_w cx) 3 + 2147450880)) ->
    rng RNG (c_w cx) 32768 -> rng RNG (Z.shiftr (c_w cx) 3 + 2147450880) 4096 -> c_w cx mod 8 = 0 -> 6807552 <= c_w cx -> c_w cx + 32768 <= 140737488355328 ->
    0 <= wi -> wi + copy <= 32768 -> t_cout st + copy <= c_osz cx -> copy < 2147483648 ->
    0 <= k < copy -> copy - k < Z.of_nat N ->
    (forall fo' x1' x5' x7' x11 x12 x14 x16 x17 m', inf_arr_ok cx wf fo' ->
       VIS cx ly st lf cf wf fo' v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m' -> HIDm cx ly m' ->
       evtF asegs RNG POST (M_A cx ly st copy x1' x5' x7' x11 x12 x14 x16 x17 m')) ->
    evtF asegs RNG POST (M_L cx ly st (c_w cx + wi) copy k x1 x5 x6 x7 m).
  Proof.
    induction N as [|N IH]; intros until m; intros CTX PAYR PLEN SI ARR VIS HID FW SHW DJW RW RWS W8 WLO WHI HWI0 HWI1 HCO HC31 HK HN KA; [lia|].
    unfold M_A in KA. unfold M_L.
    pose proof SI as RN1. unfold IDefs.RNG in RN1. destruct RN1 as (_ & _ & COUT0 & COUTN & _).
    revert IH KA. inf_arm_open_rn. intros IH KA.
    destruct (pay_out_sep _ _ _ _ _ CTX0) as (cOD & COD0 & COD1 & COD2). cbn [c_q c_n] in COD1, COD2.
    pose proof (sh0_mu _ _ _ _ _ SHO MU DJO) as SHOk.
    assert (OSZ2 : osz <= 262144) by (clear - OSZ; lia).
    pose proof (tab_sh0 m Wd 4096 (Wd + wi + k) SHW W8 ltac:(clear - HWI0 HWI1 HK; lia) ltac:(clear - WLO; lia)) as RSH1.
    pose proof (tab_sh_acc RNG Wd 4096 (Wd + wi + k) RWS W8 ltac:(clear - HWI0 HWI1 HK; lia) ltac:(clear - WLO; lia)) as ASH1.
    pose proof (tab_sh0 m 6336512 32768 (6336512 + cout + k) SHOk eq_refl ltac:(clear - HK HCO OSZ2 COUT0; lia) ltac:(clear; lia)) as RSH2.
    pose proof (tab_sh_acc RNG 6336512 32768 (6336512 + cout + k) ROBS eq_refl ltac:(clear - HK HCO OSZ2 COUT0; lia) ltac:(clear; lia)) as ASH2.
    assert (RDS : ov_read_bytes asegs m (Z_to_bv 64 (Wd + wi + k)) 1 = Some [Z_to_bv 8 (fw (wi + k))])
      by (eapply (f8arr_read asegs m Wd (Z.to_nat 32768) fw (wi + k)); [exact FW| clear - HWI0 HWI1 HK; lia| unfold wa; f_equal; clear; lia]).
    assert (ADS : acc_in RNG (Z_to_bv 64 (Wd + wi + k), 1%nat))
      by (apply (rng_acc_litZ RNG Wd 32768 _ 1%nat 1 RW eq_refl); [clear; lia| clear - HWI0 HWI1 HK; lia]).
    Time zrunb [0x91830].
    replace (6336512 + cout + k) with (6336512 + (cout + k)) by (clear; lia).
    assert (SOK : store_ok asegs m (Z_to_bv 64 (6336512 + (cout + k))) 1 = true)
      by (eapply (f8arr_store_ok asegs m 6336512 (Z.to_nat osz) fo (cout + k)); [exact OUT| clear - HK HCO COUT0; lia| reflexivity]).
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bs) _) =>
      destruct (out_write asegs m 6336512 (Z.to_nat osz) fo (cout + k) bs OUT ltac:(clear - HK HCO COUT0; lia) (length_le1 _)) as (fo' & OUT' & FOR') end.
    store_done.
    assert (ARR' : inf_arr_ok (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) wf fo') by (split; [exact (proj1 ARR)| intros i _; apply FOR']).
    Time zrunb [0x91844].
    zs. zbr0 KL.
    -
      replace (Wd + wi + k + 1) with (Wd + wi + (k + 1)) by (clear; lia).
      replace (6336512 + (cout + k) + 1) with (6336512 + cout + (k + 1)) by (clear; lia).
      replace (copy - k + -1) with (copy - (k + 1)) by (clear; lia).
      eapply (IH (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ wi copy fo' (k + 1));
        [exact CTX0| exact PAYR| exact PLEN| exact SI| exact ARR'| inf_vis_close| inf_hid_close| exact FW| exact (sh0_mu _ _ _ _ _ SHW MU DJW)| exact DJW| exact RW| exact RWS| exact W8| exact WLO| exact WHI| exact HWI0| exact HWI1| exact HCO| exact HC31
        | clear - HK KL; gcbn; lia| clear - HN; lia| exact KA].
    -
      zs.
      replace (6336512 + (cout + k) + 1) with (6336512 + cout + copy) by (clear - KL HK; lia).
      eapply (KA fo'); [exact ARR'| inf_vis_close| inf_hid_close].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Time Qed.
End S.
End CANSEC1.
