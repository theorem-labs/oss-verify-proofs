(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
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
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_w7 InfPure_w7d InfAGlue_w7.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U1A Require Import U2AObj U2AClient U2AIface InfABase InfAKit InfATables InfA_w7base InfA_w7tab.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U1A Require Import InfA_dist1 InfA_dist2.
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

  Notation DXS cx ly := (DX_STMT AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly).

  (* the 1.3.1 register homes of D_E2 moved to 1.4 by tools/regmap_text_gr.py (t2>s6 s4>s8 s5>s10 s6>t5 s7>s9 s8>s11 s9>s5 s10>s4 s11>s7 t3>t6 t4>t3 t5>t4 t6>t2) *)
  Definition D_E2 (cx : ictx) (ly : ilay) (st : ist) (TA op val rb ci H B : Z) (x7 x13 : word) (m : amem) : machine_state :=
    MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (c_n cx - ci)) (Z_to_bv 64 val) (Z_to_bv 64 (c_p cx + 56)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
            (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 15) (Z_to_bv 64 op) x13 (Z_to_bv 64 B) (Z_to_bv 64 TA) (Z_to_bv 64 rb) (Z_to_bv 64 (c_q cx + ci))
            (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 H) (Z_to_bv 64 2147450880)
            x7 (Z_to_bv 64 (c_p cx + 116)) (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly))
            (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 (c_p cx + 28)) (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880))
            (Z_to_bv 64 (c_p cx + 108)))
       FR (Z_to_bv 64 0x9100c) fc None m (seg_rom asegs).

  Lemma d_root : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x6 x7 x12 x13 : word) (m : amem) (TA nd XT NS : Z) (rd : Z -> Z) (ci H B : Z),
    DXS cx ly ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = DIST -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    dtab m TA nd rd -> tab_ok DISTS rd (t_db st) nd = true ->
    shadow_bytes m (Z.shiftr XT 3 + 2147450880) (Z.shiftr XT 3 + 2147450880 + NS) (fun _ => 0) -> XT mod 8 = 0 -> 0 <= XT -> XT <= TA -> TA + 4 * nd <= XT + 8 * NS ->
    rng RNG (Z.shiftr XT 3 + 2147450880) NS -> rng RNG TA (4 * nd) -> 0 < TA -> TA + 4 * nd < 140737488355328 ->
    t_cin st <= ci <= c_n cx -> B = t_bits st + 8 * (ci - t_cin st) -> 0 <= H < 2 ^ B -> code_bits (rd (H mod 2 ^ t_db st)) <= B -> B <= 40 ->
    (forall x7' x13', 1 <= code_op (rd (H mod 2 ^ t_db st)) <= 15 ->
       evtF asegs RNG POST (D_E2 cx ly st TA (code_op (rd (H mod 2 ^ t_db st))) (code_val (rd (H mod 2 ^ t_db st))) (code_bits (rd (H mod 2 ^ t_db st))) ci H B x7' x13' m)) ->
    evtF asegs RNG POST (D_E1 gp tp FR fc cx ly st TA rd ci H B x6 x7 x12 x13 m).
  Proof.
    intros until B. intros HDX CTX PAYR PLEN MODE SI ARR VIS HID KA DT TOK SBT XT8 XT0 XTL XTH RXT RTA TAP TAH HC HBE HH HEB HB40 KSUB.
    destruct (tab_ok_root _ _ _ _ TOK) as (DB15 & NDR & ROOT).
    unfold D_E1. unfold D_E2 in KSUB.
    inf_arm_open.
    pose proof (pow2_le_15 db ltac:(lia)) as P15.
    assert (IDX : 0 <= H mod 2 ^ db < 2 ^ db) by (apply mod_pow2_bound; lia).
    pose proof (ROOT _ IDX) as ROK.
    set (e := rd (H mod 2 ^ db)) in *.
    destruct (DT (H mod 2 ^ db) ltac:(lia)) as (RDR & RD0 & RD1 & RD2). fold e in RD0, RD1, RD2, RDR.
    pose proof (code_op_range e) as OPR. pose proof (code_val_range e) as VALR. pose proof (code_bits_range e) as BITR.
    pose proof (tab_sh0 m XT NS (TA + 4 * (H mod 2 ^ db) + 2) SBT XT8 ltac:(lia) ltac:(lia)) as RDS2.
    pose proof (tab_sh_acc RNG XT NS (TA + 4 * (H mod 2 ^ db) + 2) RXT XT8 ltac:(lia) ltac:(lia)) as ACS2.
    pose proof (tab_sh0 m XT NS (TA + 4 * (H mod 2 ^ db)) SBT XT8 ltac:(lia) ltac:(lia)) as RDS0.
    pose proof (tab_sh_acc RNG XT NS (TA + 4 * (H mod 2 ^ db)) RXT XT8 ltac:(lia) ltac:(lia)) as ACS0.
    zrunb [0x90ff8].
    zs. cbv beta. rewrite (zx16_small (code_val e)) by lia.
    zrunb [0x91000]. zs. cbv beta. rewrite (u8_lit (code_op e)) by lia.
    zs. zs. zbr0 KOP.
    -
      destruct (root_term_or_link DISTS rd db nd e ltac:(lia) ROK) as [(TERM & _)|(LINK & _)]; [| exfalso; lia].
      destruct (term_dists _ _ TERM) as (TB & TCASE).
      zrunb [0x91180].
      eapply (d_term AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh
                (ICX u S D n 6335680 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m (code_op e) (code_val e) (code_bits e) ci H B); (* d_term binds s6 (x22) too *)
        [exact HDX| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| | | | | | | | | ]; icx_cbn; first [exact TCASE | lia].
    -
      destruct (root_term_or_link DISTS rd db nd e ltac:(lia) ROK) as [(TERM & _)|(LINK & _)].
      + exfalso. destruct (term_dists _ _ TERM) as (_ & [(O1 & _)|O64]); [lia|].
        apply O64. clear - KOP OPR. assert (C : 0 <= code_op e <= 15) by lia. revert C. generalize (code_op e). intros op C. zcases op 0 15; reflexivity.
      + eapply KSUB. exact LINK.
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Time Qed.
End S.
End CANSEC1.
