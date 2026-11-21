(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow U2AKit U2AArr U2AObj U2AClient U2AStore U2AIface InfABase InfAKit InfAGlue InfATables InfPure InfPure_w7 InfPure_w7d InfPure_w7e InfPure_w7f InfAGlue_w7 InfAGlue_w7b InfA_w7base InfA_w7tab InfA_w7pull.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.U2A Require Import InfA_w7lenr InfA_len2 InfA_len4 InfA_len5 InfA_len3.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
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

  (* the 1.3.1 register homes of L_L1 moved to 1.4 by tools/regmap_text_gr.py (t2>s6 s4>s8 s5>s10 s6>t5 s7>s9 s8>s11 s9>s5 s10>s4 s11>s7 t3>t6 t4>t3 t5>t4 t6>t2) *)
  (* L_L1 restated from the 1.4 LEN first-level loop (0x90de8..0x90e64): t2 = the lenbits mask (0x90db8), t3 = B, t6 = S+108 at the head, s7 = S+116 (loaded at 0x90da0); s6 is the arm's free word, named by the x27 parameter *)
  Definition L_L1 (cx : ictx) (ly : ilay) (st : ist) (TA : Z) (rd : Z -> Z) (ci H B : Z) (x11 x13 x27 : word) (m : amem) : machine_state :=
    MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (c_q cx + ci)) (Z_to_bv 64 (c_n cx - ci)) (Z_to_bv 64 (2 ^ t_lb st - 1)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
            (Z_to_bv 64 (l_F0 ly)) x11 (Z_to_bv 64 (c_q cx + ci)) x13 (Z_to_bv 64 (Z.shiftr (c_p cx + 7164) 3 + 2147450880)) (Z_to_bv 64 B) (Z_to_bv 64 TA) (Z_to_bv 64 (code_bits (rd (H mod 2 ^ t_lb st))))
            (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 H) (Z_to_bv 64 2147450880)
            x27 (Z_to_bv 64 (c_p cx + 116)) (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly))
            (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 B) (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880))
            (Z_to_bv 64 (c_p cx + 108)))
       FR (Z_to_bv 64 0x90e2c) fc None m (seg_rom asegs).

  Lemma l_loop1 : forall (N : nat) (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x11 x13 x27 : word) (m : amem) (TA nd XT NS : Z) (rd : Z -> Z) (ci H B : Z),
    LXB cx ly -> LXZ cx ly ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LEN -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    dtab m TA nd rd -> tab_ok LENS rd (t_lb st) nd = true -> nd <= 65536 ->
    shadow_bytes m (Z.shiftr XT 3 + 2147450880) (Z.shiftr XT 3 + 2147450880 + NS) (fun _ => 0) -> XT mod 8 = 0 -> 0 <= XT -> XT <= TA -> TA + 4 * nd <= XT + 8 * NS ->
    rng RNG (Z.shiftr XT 3 + 2147450880) NS -> rng RNG TA (4 * nd) -> 0 < TA -> TA + 4 * nd < 140737488355328 ->
    c_n cx - ci < Z.of_nat N ->
    t_cin st <= ci <= c_n cx -> B = t_bits st + 8 * (ci - t_cin st) -> 0 <= H < 2 ^ B -> B < code_bits (rd (H mod 2 ^ t_lb st)) ->
    evtF asegs RNG POST (L_L1 cx ly st TA rd ci H B x11 x13 x27 m).
  Proof.
    induction N as [|N IH]; intros until B; intros HLXB HLXZ CTX PAYR PLEN MODE SI ARR VIS HID KA DT TOK ND16 SBT XT8 XT0 XTL XTH RXT RTA TAP TAH HN HC HBE HH HBX; [lia|].
    pose proof KA as (KD & KB & KL & KLV).
    destruct (tab_ok_root _ _ _ _ TOK) as (LB15 & NDR & ROOT).
    assert (CB15 : forall i, 0 <= i < 2 ^ t_lb st -> code_bits (rd i) <= 15).
    { intros i Hi. pose proof (ROOT _ Hi) as ROK. destruct (root_term_or_link InflateState.LENS rd (t_lb st) nd _ ltac:(lia) ROK) as [(TERM & _)|(_ & EB & _)].
      - pose proof (term_ok_bits _ _ _ TERM). lia.
      - lia. }
    pose proof (sinv_bits_facts _ _ _ _ SI) as (CIN0 & CINN & BITS0 & BLE & HOLD0).
    unfold L_L1.
    revert IH. inf_arm_open. intros IH.
    pose proof (pow2_le_15 lb ltac:(lia)) as P15.
    assert (CBE : code_bits (rd (H mod 2 ^ lb)) <= 15) by (apply CB15; apply mod_pow2_bound; lia).
    set (hb0 := code_bits (rd (H mod 2 ^ lb))) in *. clearbody hb0.
    pose proof (pow2_le_40 B ltac:(clear - HBX CBE HBE HC BITS0; lia)) as P40.
    zs. zbr0 KH.
    -
      assert (CIR : 0 <= ci < n) by (clear - CIN0 HC KH; lia).
      destruct (pull_facts RNG _ m m D n payload ci UNP MU DJP RD RSD PAYB PAYR PLEN D16 D1 CIR) as (b & RDB & CK & ACP & RDP & ACB & BZR).
      zs. (* 1.4 saves t4 in t6 first (0x90e04 mv t6,t4) *)
      zs. zs. zs. rewrite sxb_sval.
      ck_branchJc 13 0x90e48 CK.
      zs. cbv beta. rewrite (bz_val payload ci PAYR).
      zs. zs.
      rewrite (pull_hold H (bz payload ci) B) by (clear - HBX CBE HBE HC BITS0; lia).
      pose proof (pull_bound H B (bz payload ci) ltac:(clear - HBE HC BITS0; lia) ltac:(clear - HH; lia) BZR) as PB.
      set (H1 := H + bz payload ci * 2 ^ B) in *.
      assert (PB64 : 0 <= H1 < 18446744073709551616) by (pose proof (pow2_le_40 (B + 8) ltac:(clear - HBX CBE HBE HC BITS0; lia)) as P48; clear - PB P48; lia).
      eapply (len_root_b RNG POST) with (H := H1) (lb := lb) (TA := TA); [exact PB64| exact LB15| clear - TAP TAH NDR P15; lia|].
      assert (IDX1 : 0 <= H1 mod 2 ^ lb < 2 ^ lb) by (apply mod_pow2_bound; clear - LB15; lia).
      assert (CBE1 : code_bits (rd (H1 mod 2 ^ lb)) <= 15) by (apply CB15; exact IDX1).
      assert (IND1 : 0 <= H1 mod 2 ^ lb < nd) by (clear - IDX1 NDR; lia).
      remember (H1 mod 2 ^ lb) as i1 eqn:EI1. apply w7hide_in in EI1.
      destruct (DT i1 IND1) as (RDR & RD0 & RD1 & RD2).
      pose proof (tab_sh0 m XT NS (TA + 4 * i1 + 1) SBT XT8 ltac:(clear - IND1 XTL XTH; lia) ltac:(exact XT0)) as RDS.
      pose proof (tab_sh_acc RNG XT NS (TA + 4 * i1 + 1) RXT XT8 ltac:(clear - IND1 XTL XTH; lia) ltac:(exact XT0)) as ACS.
      zs. zs. zs. zs. zs. zs.
      cbv beta.
      rewrite u8_lit by (apply code_bits_range).
      pose proof (code_bits_range (rd i1)) as CBR1.
      set (hb1 := code_bits (rd i1)) in *.
      zrunb [0x90e94].
      replace (D + ci + 1) with (D + (ci + 1)) by (clear; lia). replace (n - ci + -1) with (n - (ci + 1)) by (clear; lia).
      zs. zbr0 KB2.
      +
        apply w7hide_out in EI1. subst hb1 i1.
        eapply (IH (ICX u S D n 6336320 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m TA nd XT NS rd (ci + 1) H1 (B + 8));
          [exact HLXB| exact HLXZ| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| exact DT| exact TOK| exact ND16| exact SBT| exact XT8| exact XT0| exact XTL| exact XTH| exact RXT| exact RTA| exact TAP| exact TAH
          | | | | | ]; clear - HN HC CIR HBE PB KB2 HBX CBE; gcbn; lia.
      +
        zrunb [0x90ec8].
        apply w7hide_out in EI1. subst hb1 i1.
        eapply (l_root AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh
                  (ICX u S D n 6336320 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m TA nd XT NS rd (ci + 1) H1 (B + 8));
          [exact HLXB| exact HLXZ| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| exact DT| exact TOK| exact ND16| exact SBT| exact XT8| exact XT0| exact XTL| exact XTH| exact RXT| exact RTA| exact TAP| exact TAH
          | | | | | ]; clear - HN HC CIR HBE PB KB2 HBX CBE; gcbn; lia.
    -
      zrunb [0x92900].
      assert (ECI : ci = n) by (clear - KH HC; lia). subst ci.
      replace (Z.shiftl (n - cin) 3 + bits) with B by (rewrite Z.shiftl_mul_pow2 by (clear; lia); clear - HBE; lia).
      replace (D + cin + (n - cin) mod 4294967296) with (D + n) by (rewrite Z.mod_small by (clear - NR HC CIN0; lia); clear; lia).
      replace (Z_to_bv 64 0) with (Z_to_bv 64 (n - n)) by (f_equal; clear; lia).
      assert (SPF : cin <= n /\ n <= n /\ 0 <= B /\ B <= 40 /\ 0 <= H /\ H < 2 ^ B /\ B <= 8 * n /\ 8 * (n - n) + B <= 8 * (n - cin) + bits) by (clear - CIN0 CINN BITS0 BLE HC HBE HH HBX CBE; lia).
      destruct (sinv_pull _ _ lf cf n H B SI ltac:(gcbn; tauto) ltac:(gcbn; tauto) ltac:(tauto) ltac:(tauto) ltac:(tauto) ltac:(tauto) ltac:(gcbn; tauto) ltac:(gcbn; tauto)) as (SI1 & _).
      st_norm SI1.
      eapply (KLV (IST mode last flags n cout H B out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ret lf cf wf fo);
        [exact SI1| exact ARR| inf_vis_close| exact HID].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Time Qed.
End S.
End CANSEC1.
