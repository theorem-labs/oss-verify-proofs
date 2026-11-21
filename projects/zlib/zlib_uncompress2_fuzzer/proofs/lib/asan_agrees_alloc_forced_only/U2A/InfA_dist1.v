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
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AObj U2AClient U2AStore U2AIface InfABase InfAKit InfAGlue InfATables InfPure InfPure_w7 InfAGlue_w7 InfA_w7base InfA_w7tab.
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
  Notation GARM cx ly Lb X := (garm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).

  (* the 1.3.1 register homes of D_E1, d_loop1 moved to 1.4 by tools/regmap_text_gr.py (ra>s6 t2>ra s4>s8 s5>s10 s6>t5 s7>s9 s8>s11 s9>s5 s10>s4 s11>s7 t3>t6 t4>t3 t5>t4 t6>t2) *)
  (* the 1.3.1 register homes of D_E1 moved to 1.4 by tools/regmap_text_gr.py (ra>t2 t2>t6 s4>s10 s5>s9 s6>ra s7>s11 s8>s4 s9>s7 s10>s5 s11>s8 t3>t4 t4>t5 t5>s6 t6>t3) *)
  (* the 1.3.1 register homes of D_E1 moved to 1.4 by tools/regmap_text_gr.py (s3>s10 s4>s8 s5>s6 s6>t5 s7>s9 s8>s11 s9>s5 s10>s4 s11>s7 t4>s3 t5>t4) *)
  (* D_E1 restated from the g27 call-site probe Pg27dist1 (s3 = bits, s6 = S+28, s10 = D+cin, as in d_loop1); the loop exit at 0x9120c jumps to 0x91238, ld t2,480(s1), so t2 is free at 0x9123c *)
  (* from the 1.4 DIST arm (0x91120..0x9123c, ARM_MS homes): t6 = S+108 throughout the loop, s6 is the arm's free word, and t2 = S+56 at 0x9123c on both paths (the arm's t2, or ld t2,480(s1) at 0x91238). D_E1's x7 parameter now names s6 *)
  Definition D_E1 (cx : ictx) (ly : ilay) (st : ist) (TA : Z) (rd : Z -> Z) (ci H B : Z) (x6 x7 x12 x13 : word) (m : amem) : machine_state :=
    MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (c_n cx - ci)) x6 (Z_to_bv 64 (c_p cx + 56)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
            (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (TA + 4 * (H mod 2 ^ t_db st))) x12 x13 (Z_to_bv 64 B) (Z_to_bv 64 TA) (Z_to_bv 64 (code_bits (rd (H mod 2 ^ t_db st)))) (Z_to_bv 64 (c_q cx + ci))
            (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 H) (Z_to_bv 64 2147450880)
            x7 (Z_to_bv 64 (c_p cx + 116)) (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly))
            (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 (c_p cx + 28)) (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880))
            (Z_to_bv 64 (c_p cx + 108)))
       FR (Z_to_bv 64 0x9126c) fc None m (seg_rom asegs).

  (* the 1.3.1 register homes of d_loop1 moved to 1.4 by tools/regmap_text_gr.py (ra>t2 t2>t6 s4>s10 s5>s9 s6>ra s7>s11 s8>s4 s9>s7 s10>s5 s11>s8 t3>t4 t4>t5 t5>s6 t6>t3) *)
  (* the 1.3.1 register homes of d_loop1 moved to 1.4 by tools/regmap_text_gr.py (s4>s8 s5>s10 s6>t5 s7>s9 s8>s11 s9>s5 s10>s4 s11>s7 t4>s6 t5>t4) *)
  Lemma d_loop1 : forall (N : nat) (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x11 x13 x22 : word) (m : amem) (TA nd XT NS : Z) (rd : Z -> Z) (ci H B : Z),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = DIST -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    dtab m TA nd rd -> 1 <= t_db st <= 15 -> 2 ^ t_db st <= nd -> (forall i, 0 <= i < 2 ^ t_db st -> code_bits (rd i) <= 15) ->
    shadow_bytes m (Z.shiftr XT 3 + 2147450880) (Z.shiftr XT 3 + 2147450880 + NS) (fun _ => 0) -> XT mod 8 = 0 -> 0 <= XT -> XT <= TA -> TA + 4 * nd <= XT + 8 * NS ->
    rng RNG (Z.shiftr XT 3 + 2147450880) NS -> rng RNG TA (4 * nd) -> 0 < TA -> TA + 4 * nd < 140737488355328 ->
    (forall ci' H' B' x6 x7 x12 x13', t_cin st <= ci' <= c_n cx -> B' = t_bits st + 8 * (ci' - t_cin st) -> 0 <= H' < 2 ^ B' -> code_bits (rd (H' mod 2 ^ t_db st)) <= B' -> B' <= 40 ->
       evtF asegs RNG POST (D_E1 cx ly st TA rd ci' H' B' x6 x7 x12 x13' m)) ->
    c_n cx - ci < Z.of_nat N ->
    t_cin st <= ci <= c_n cx -> B = t_bits st + 8 * (ci - t_cin st) -> 0 <= H < 2 ^ B -> B < code_bits (rd (H mod 2 ^ t_db st)) ->
    evtF asegs RNG POST
      (MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (c_n cx - ci)) (Z_to_bv 64 (2 ^ t_db st - 1)) (Z_to_bv 64 B) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               (Z_to_bv 64 (l_F0 ly)) x11 (Z_to_bv 64 (c_q cx + ci)) x13 (Z_to_bv 64 B) (Z_to_bv 64 TA) (Z_to_bv 64 (code_bits (rd (H mod 2 ^ t_db st)))) (Z_to_bv 64 (c_q cx + ci))
               (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 H) (Z_to_bv 64 2147450880)
               x22 (Z_to_bv 64 (c_p cx + 116)) (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly))
               (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 (c_p cx + 28)) (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880))
               (Z_to_bv 64 (c_p cx + 108)))
          FR (Z_to_bv 64 0x911d8) fc None m (seg_rom asegs)).
  Proof.
    induction N as [|N IH]; intros until B; intros CTX PAYR PLEN MODE SI ARR VIS HID KA DT DB15 NDR CB15 SBT XT8 XT0 XTL XTH RXT RTA TAP TAH KE1 HN HC HBE HH HBX; [lia|].
    pose proof KA as (KD & KB & KL & KLV).
    unfold D_E1 in KE1.
    inf_arm_open.
    pose proof (pow2_le_15 db ltac:(lia)) as P15.
    assert (IDX : 0 <= H mod 2 ^ db < 2 ^ db) by (apply mod_pow2_bound; lia).
    pose proof (CB15 _ IDX) as CBE.
    pose proof (pow2_le_40 B ltac:(lia)) as P40.
    zs. zbr0 KH.
    -
      destruct (unp_check_mu asegs _ _ _ _ _ (D + ci) 1 UNP MU DJP ltac:(lia) ltac:(lia) ltac:(lia) (mod8_room1 _)) as (b & RDB & CK).
      pose proof (pay_sh_acc RNG D n (D + ci) RSD ltac:(first [ apply mod16_mod8; assumption | Z.div_mod_to_equations; lia ]) ltac:(lia) ltac:(lia)) as ACP.
      zs. zs. zs. rewrite sxb_sval.
      ck_branchJ 13 0x911f0 CK.
      pose proof (pay_read asegs _ D payload ci PAYB ltac:(lia)) as RDP. fold (bz payload ci) in RDP.
      pose proof (bz_range payload ci PAYR) as BZR.
      zs. cbv beta. rewrite (bz_val payload ci PAYR).
      zs. zs.
      rewrite (pull_hold H (bz payload ci) B) by lia.
      pose proof (pull_bound H B (bz payload ci) ltac:(lia) ltac:(lia) BZR) as PB.
      set (H1 := H + bz payload ci * 2 ^ B) in *.
      assert (PB64 : 0 <= H1 < 18446744073709551616) by (pose proof (pow2_le_40 (B + 8) ltac:(lia)); lia).
      zs. rewrite (root_idx H1 db) by lia.
      assert (IDX1 : 0 <= H1 mod 2 ^ db < 2 ^ db) by (apply mod_pow2_bound; lia).
      zs. rewrite shl2. zs. zs.
      destruct (DT (H1 mod 2 ^ db) ltac:(lia)) as (RDR & RD0 & RD1 & RD2).
      pose proof (tab_sh0 m XT NS (TA + 4 * (H1 mod 2 ^ db) + 1) SBT XT8 ltac:(lia) ltac:(lia)) as RDS.
      pose proof (tab_sh_acc RNG XT NS (TA + 4 * (H1 mod 2 ^ db) + 1) RXT XT8 ltac:(lia) ltac:(lia)) as ACS.
      zs. zs. zs. zs. zs. zs.
      cbv beta.
      rewrite u8_lit by (apply code_bits_range).
      pose proof (CB15 _ IDX1) as CBE1. pose proof (code_bits_range (rd (H1 mod 2 ^ db))) as CBR1.
      zrunb [0x91238].
      replace (D + ci + 1) with (D + (ci + 1)) by lia. replace (n - ci + -1) with (n - (ci + 1)) by lia.
      zs. zbr0 KB2.
      +
        eapply (IH (ICX u S D n 6336320 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m TA nd XT NS rd (ci + 1) H1 (B + 8));
          [exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| exact DT| exact DB15| exact NDR| exact CB15| exact SBT| exact XT8| exact XT0| exact XTL| exact XTH| exact RXT| exact RTA| exact TAP| exact TAH| exact KE1| | | | | ]; icx_cbn; lia.
      +
        zs. zs.
        eapply (KE1 (ci + 1) H1 (B + 8)); icx_cbn; lia.
    -
      zrunb [0x92900].
      assert (ECI : ci = n) by lia. subst ci.
      replace (Z.shiftl (n - cin) 3 + bits) with B by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      replace (D + cin + (n - cin) mod 4294967296) with (D + n) by (rewrite Z.mod_small by lia; lia).
      replace (Z_to_bv 64 0) with (Z_to_bv 64 (n - n)) by (f_equal; lia).
      destruct (sinv_pull _ _ lf cf n H B SI ltac:(icx_cbn; lia) ltac:(icx_cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(icx_cbn; lia) ltac:(icx_cbn; lia)) as (SI1 & _).
      st_norm SI1.
      eapply (KLV (IST mode last flags n cout H B out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ret lf cf wf fo);
        [exact SI1| exact ARR| inf_vis_close| exact HID].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Time Qed.
End S.
End CANSEC1.
