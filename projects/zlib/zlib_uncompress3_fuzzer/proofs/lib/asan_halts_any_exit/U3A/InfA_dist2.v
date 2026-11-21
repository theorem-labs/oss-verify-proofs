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
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_w7 InfPure_w7d InfAGlue_w7.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U3A Require Import U2AObj U2AClient U2AIface InfABase InfAKit InfATables InfA_w7base InfA_w7tab.
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

  (* the 1.3.1 register homes of DX_STMT, d_term moved to 1.4 by tools/regmap_text_gr.py (ra>s6 t2>ra s4>s8 s5>s10 s6>t5 s7>s9 s8>s11 s9>s5 s10>s4 s11>s7 t3>t6 t4>t3 t5>t4 t6>t2) *)
  Definition DX_STMT (cx : ictx) (ly : ilay) : Prop :=
    forall (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x1 x5 x6 x11 x13 x14 x15 x16 x17 x27 : word) (m : amem),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = DISTEXT -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    evtF asegs RNG POST
      (MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 (Z_to_bv 64 (c_p cx + 56)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               (Z_to_bv 64 (l_F0 ly)) x11 (Z_to_bv 64 (t_extra st)) x13 x14 x15 x16 x17
               (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 2147450880)
               x1 x27 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly))
               (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 (c_p cx + 28)) (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880))
               (Z_to_bv 64 (c_p cx + 108)))
          FR (Z_to_bv 64 0x91550) fc None m (seg_rom asegs)).

  Lemma d_term : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x5 x7 x11 x15 x16 x19 x22 : word) (m : amem) (op val hb ci H B : Z),
    DX_STMT cx ly ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = DIST -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    t_cin st <= ci <= c_n cx -> 0 <= hb <= B -> B <= 40 -> 0 <= H < 2 ^ B -> B <= 8 * ci -> 8 * (c_n cx - ci) + B <= 8 * (c_n cx - t_cin st) + t_bits st ->
    0 <= op < 256 -> 0 <= val < 65536 ->
    ((16 <= op <= 29 /\ 1 <= val /\ val + 2 ^ (op - 16) - 1 <= 32768) \/ Z.land op 64 <> 0) ->
    evtF asegs RNG POST
      (* ra holds &state->mode (S+8) throughout 1.4's inflate body (probe PgCsDist2) *)
      (MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 (Z_to_bv 64 val) (Z_to_bv 64 (c_p cx + 56)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               (Z_to_bv 64 (l_F0 ly)) x11 (Z_to_bv 64 op) (Z_to_bv 64 hb) (Z_to_bv 64 B) x15 x16 (Z_to_bv 64 (c_p cx + 7164))
               (Z_to_bv 64 (l_Zs ly)) x19 (Z_to_bv 64 H) (Z_to_bv 64 2147450880)
               x22 (Z_to_bv 64 (c_p cx + 116)) (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly)) (* s6 is free at 0x914b0 (left on one path, the arm's word on the other; probe Pg28dist3) *)
               (Z_to_bv 64 (c_q cx + ci)) (Z_to_bv 64 (c_n cx - ci)) (Z_to_bv 64 (c_p cx + 28)) (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880))
               (Z_to_bv 64 (c_p cx + 108)))
          FR (Z_to_bv 64 0x914e0) fc None m (seg_rom asegs)).
  Proof.
    intros until B. intros HDX CTX PAYR PLEN MODE SI ARR VIS HID KA HC HHB HB40 HH HBC HW HOP HVAL HTERM.
    pose proof KA as (KD & KB & KL & KLV).
    inf_arm_open.
    pose proof (pow2_le_40 B ltac:(lia)) as P40.
    pose proof (drop_bound H B hb ltac:(lia) HH) as DB.
    destruct (sinv_pull _ _ lf cf ci (H / 2 ^ hb) (B - hb) SI ltac:(icx_cbn; lia) ltac:(icx_cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(icx_cbn; lia) ltac:(icx_cbn; lia)) as (SI1 & ME1).
    zrunb [0x914f8].
    rewrite (srl_div H hb) by lia.
    zrunb [0x91508].
    zs. zbr0 KI.
    -
      zrunb [0x9191c].
      pose proof (sinv_bad_ofP _ _ lf cf SI1) as SIB. pose proof (meas_bad_ofP (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (st_pull (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ci (H / 2 ^ hb) (B - hb))) as MEB.
      st_norm SI1. st_norm ME1. unfold bad_ofP in SIB, MEB. st_norm SIB. st_norm MEB. subst mode. change (rank DIST) with 16 in MEB.
      eapply (KB (IST DIST last flags ci cout (H / 2 ^ hb) (B - hb) out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact SIB| unfold bad_of; icx_cbn; lia| exact ARR| change DIST with 16202; inf_vis_close| inf_hid_close].
    -
      destruct HTERM as [(OP1 & VAL1 & VAL2)|BADOP]; [| exfalso; lia].
      pose proof (op_land15 op OP1) as L15.
      zrunb [0x91550].
      rewrite L15 in *.
      destruct (sinv_to_distext _ _ lf cf val (op - 16) SI1 MODE ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (SI2 & ME2).
      st_norm SI1. st_norm ME1. st_norm SI2. st_norm ME2.
      eapply (HDX (IST DISTEXT last flags ci cout (H / 2 ^ hb) (B - hb) out ret len val (op - 16) lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI2| exact ARR| change DISTEXT with 16203; inf_vis_close| inf_hid_close| eapply KALL_mono; [| exact KA]; lia].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Time Qed.
End S.
End CANSEC1.
