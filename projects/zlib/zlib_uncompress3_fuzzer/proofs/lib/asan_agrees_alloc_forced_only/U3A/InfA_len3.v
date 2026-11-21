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
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U3A Require Import InfA_w7lenr InfA_len2 InfA_len4 InfA_len5.
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

  Notation LXB cx ly := (LXB_STMT AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly).
  Notation LXZ cx ly := (LXZ_STMT AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly).

  (* the 1.3.1 register homes of L_E1 moved to 1.4 by tools/regmap_text_gr.py (t2>s6 s4>s8 s5>s10 s6>t5 s7>s9 s8>s11 s9>s5 s10>s4 s11>s7 t3>t6 t4>t3 t5>t4 t6>t2) *)
  (* at 0x90f64 t2 still holds the lenbits mask on both paths (0x90e84); 1.4 overwrites it with here.val at 0x90f88 *)
  Definition L_E1 (cx : ictx) (ly : ilay) (st : ist) (TA : Z) (rd : Z -> Z) (ci H B : Z) (x7 x12 x13 : word) (m : amem) : machine_state := (* s7 = S+116 from the arm (0x90e6c) to l_term's store at 0x9117c *)
    MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (c_q cx + ci)) (Z_to_bv 64 (c_n cx - ci)) (Z_to_bv 64 (2 ^ t_lb st - 1)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
            (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (TA + 4 * (H mod 2 ^ t_lb st))) x12 x13 (Z_to_bv 64 (Z.shiftr (c_p cx + 7164) 3 + 2147450880)) (Z_to_bv 64 B) (Z_to_bv 64 TA) (Z_to_bv 64 (code_bits (rd (H mod 2 ^ t_lb st))))
            (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 H) (Z_to_bv 64 2147450880)
            x7 (Z_to_bv 64 (c_p cx + 116)) (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly))
            (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 (c_p cx + 28)) (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880))
            (Z_to_bv 64 (c_p cx + 108)))
       FR (Z_to_bv 64 0x90f94) fc None m (seg_rom asegs).

  Lemma l_root : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x7 x12 x13 : word) (m : amem) (TA nd XT NS : Z) (rd : Z -> Z) (ci H B : Z),
    LXB cx ly -> LXZ cx ly ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LEN -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    dtab m TA nd rd -> tab_ok LENS rd (t_lb st) nd = true -> nd <= 65536 ->
    shadow_bytes m (Z.shiftr XT 3 + 2147450880) (Z.shiftr XT 3 + 2147450880 + NS) (fun _ => 0) -> XT mod 8 = 0 -> 0 <= XT -> XT <= TA -> TA + 4 * nd <= XT + 8 * NS ->
    rng RNG (Z.shiftr XT 3 + 2147450880) NS -> rng RNG TA (4 * nd) -> 0 < TA -> TA + 4 * nd < 140737488355328 ->
    t_cin st <= ci <= c_n cx -> B = t_bits st + 8 * (ci - t_cin st) -> 0 <= H < 2 ^ B -> code_bits (rd (H mod 2 ^ t_lb st)) <= B -> B <= 40 ->
    evtF asegs RNG POST (L_E1 cx ly st TA rd ci H B x7 x12 x13 m).
  Proof.
    intros until B. intros HLXB HLXZ CTX PAYR PLEN MODE SI ARR VIS HID KA DT TOK ND16 SBT XT8 XT0 XTL XTH RXT RTA TAP TAH HC HBE HH HEB HB40.
    destruct (tab_ok_root _ _ _ _ TOK) as (LB15 & NDR & ROOT).
    pose proof (sinv_bits_facts _ _ _ _ SI) as (CIN0 & CINN & BITS0 & BLE & HOLD0).
    unfold L_E1.
    inf_arm_open.
    pose proof (pow2_le_15 lb ltac:(lia)) as P15.
    assert (IDX : 0 <= H mod 2 ^ lb < 2 ^ lb) by (apply mod_pow2_bound; lia).
    pose proof (ROOT _ IDX) as ROK.
    assert (IND : 0 <= H mod 2 ^ lb < nd) by lia.
    remember (H mod 2 ^ lb) as i0 eqn:EI0. apply w7hide_in in EI0.
    set (e := rd i0) in *.
    destruct (DT i0 IND) as (RDR & RD0 & RD1 & RD2). fold e in RD0, RD1, RD2, RDR.
    pose proof (code_op_range e) as OPR. pose proof (code_val_range e) as VALR. pose proof (code_bits_range e) as BITR.
    pose proof (tab_sh0 m XT NS (TA + 4 * i0 + 2) SBT XT8 ltac:(lia) ltac:(lia)) as RDS2.
    pose proof (tab_sh_acc RNG XT NS (TA + 4 * i0 + 2) RXT XT8 ltac:(lia) ltac:(lia)) as ACS2.
    pose proof (tab_sh0 m XT NS (TA + 4 * i0) SBT XT8 ltac:(lia) ltac:(lia)) as RDS0.
    pose proof (tab_sh_acc RNG XT NS (TA + 4 * i0) RXT XT8 ltac:(lia) ltac:(lia)) as ACS0.
    zrunb [0x90fb8].
    zs. cbv beta. rewrite (zx16_small (code_val e)) by lia.
    zrunb [0x90fc4]. zs. cbv beta. rewrite (u8_lit (code_op e)) by lia.
    zs. zs.
    zs. zbr0 KOP.
    -
      destruct (root_term_or_link InflateState.LENS rd lb nd e ltac:(lia) ROK) as [(TERM & _)|(LINK & _)]; [| exfalso; destruct (op_m1_taken _ OPR KOP); lia].
      destruct (term_lens _ _ TERM) as (TB & TCASE).
      zrunb [0x91140].
      eapply (l_term AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh
                (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m (code_op e) (code_val e) (code_bits e) ci H B); (* l_term binds s6 (x22) for s7 (x27) *)
        [exact HLXB| exact HLXZ| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| | | | | | | | | ];
        first [exact TCASE | clear - HC HBE HH HEB HB40 TB OPR VALR CIN0 CINN BITS0 BLE; gcbn; lia].
    -
      pose proof (op_m1_not _ OPR KOP) as LINKOP.
      destruct (root_term_or_link InflateState.LENS rd lb nd e ltac:(lia) ROK) as [(_ & NL)|(_ & EB & OPL & VLO & VHI & SUB)]; [exfalso; exact (NL LINKOP)|].
      zs. (* 1.4 does mv s6,t4 at 0x90fa4 before the second level (L_E2, 0x90fa8) *)
      eapply (l_sub AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh
                (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m TA nd XT NS rd (code_op e) (code_val e) (code_bits e) ci H B);
        [exact HLXB| exact HLXZ| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| exact DT| exact SBT| exact XT8| exact XT0| exact XTL| exact XTH| exact RXT| exact RTA| exact TAP| exact TAH
        | | | | | | | | | | | | ];
        first [ intros j Hj; rewrite EB; exact (proj1 (SUB j Hj)) | clear - HC HBE HH HEB HB40 EB OPL VLO VHI LINKOP LB15 ND16 VALR; gcbn; lia ].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Time Qed.
End S.
End CANSEC1.
