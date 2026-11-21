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
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import InfPure_w7g.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U3A Require Import InfAGlue_p04 InfA_match1 InfA_match2 InfA_match3.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U3A Require Import InfA_garmv. (* garmV, slot 504 free down the LEN -> MATCH chain *)
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
  Notation GARM cx ly Lb X := (garmv_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).


  (* the 1.3.1 register homes of M_W moved to 1.4 by tools/regmap_text_gr.py (t2>s6 s4>s8 s5>s10 s6>t5 s7>s9 s8>s11 s9>s5 s10>s4 s11>s7 t3>t6 t4>t3 t5>t4 t6>t2) *)
  Definition M_W (cx : ictx) (ly : ilay) (st : ist) (wi c : Z) (x1 x5 x7 x12 x14 x15 x16 : word) (m : amem) : machine_state :=
    MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x14 (Z_to_bv 64 (c_p cx + 56)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
            (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 wi) x12 (Z_to_bv 64 c) (Z_to_bv 64 (c_p cx + 88)) x15 x16 (* 1.4 holds &state->window in a4 (ld a4,40(s1) at 0x91760); the x14 parameter names t1 *) (Z_to_bv 64 (6336512 + t_cout st))
            (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 2147450880)
            x7 x1 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly)) (* 1.3.1 kept the mode pointer in s11 here; 1.4 keeps it in ra, and the x1 parameter names s7 (probe Pg30match3) *)
            (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 (c_p cx + 28)) (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880))
            (Z_to_bv 64 (c_p cx + 108)))
       FR (Z_to_bv 64 0x91794) fc None m (seg_rom asegs).

  Lemma m_win : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (wi c : Z) (x1 x5 x7 x12 x14 x15 x16 : word) (m : amem),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = MATCH -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) v240 (Z_to_bv 64 (c_q cx + t_cin st)) j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    c_w cx <> 0 -> 0 <= wi -> wi + c <= 32768 -> 1 <= c -> 1 <= c_osz cx - t_cout st ->
    evtF asegs RNG POST (M_W cx ly st wi c x1 x5 x7 x12 x14 x15 x16 m).
  Proof.
    intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA WNZ HWI0 HWI1 HC1 HL1.
    destruct (sinv_match_facts _ _ _ _ SI MODE) as (LEN1 & LEN16 & OFF).
    unfold M_W.
    inf_arm_open.
    clear R13.
    Time zrunb [0x917c0].
    zs. zbr0 KCL.
    -
      Time zrunb [0x917d4].
      rewrite (Z.mod_small wi 4294967296) by (clear - HWI0 HWI1 HC1; lia).
      eapply (m_join_w AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ wi c);
        [exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| exact WNZ| exact HWI0| exact HWI1| clear - KCL HC1; gcbn; lia| exact HL1].
    -
      Time zrunb [0x917d4].
      rewrite (Z.mod_small wi 4294967296) by (clear - HWI0 HWI1 HC1; lia).
      eapply (m_join_w AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ wi len);
        [exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| exact WNZ| exact HWI0| clear - KCL HWI1; lia| clear - LEN1; gcbn; lia| exact HL1].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Time Qed.
  Theorem match_garm : forall cx ly, GARM cx ly 0x91680 MATCH.
  Proof.
    intros cx ly. unfold garmv_stmtA, GARM_MS. intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA.
    pose proof KA as (KD & KB & KL & KLV).
    destruct (sinv_match_facts _ _ _ _ SI MODE) as (LEN1 & LEN16 & OFF).
    destruct (sinv_match_win _ _ _ _ SI) as (WIN0 & WIN1).
    pose proof (proj1 SI) as RN1. unfold IDefs.RNG in RN1.
    destruct RN1 as (_ & _ & COUT0 & COUTN & _ & _ & _ & _ & _ & _ & OUT1 & OUT2 & OUT3 & _ & _ & _ & _ & OFF0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WH0 & WN0 & _).
    inf_arm_open.
    clear R13.
    assert (WHB : whave <= 32768 /\ wnext <= 32768) by (clear - WIN0 WIN1 WH0 WN0; destruct (Z.eq_dec Wd 0) as [E|E]; [destruct (WIN0 E); lia| destruct (WIN1 E); lia]).
    assert (OSZ2 : osz <= 262144) by (clear - OSZ; lia).
    zs. zbr0 KLEFT.
    2: {
      zs.
      eapply (KL (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo); [exact SI| exact ARR| exact VISf| exact HID]. }
    Time zrunb [0x9169c].
    zs. rewrite (zx32_small offset) by (clear - OFF OFF0; lia).
    Time zrunb [0x916bc].
    zs. zbr0 KOFF.
    -
      Time zrunb [0x917d4].
      replace (6336512 + cout - offset) with (6336512 + (cout - offset)) by (clear; lia).
      eapply (m_join_o AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (cout - offset) len);
        [exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| inf_vis_close| inf_hid_close| exact KA
        | clear - KOFF OUT3 OFF0; gcbn; lia| clear - LEN1; gcbn; lia| clear - KLEFT COUT0 COUTN; gcbn; lia].
    -
      Time zrunb [0x916d0].
      zs. zs. zs. zbr0 KWH.
      +
        assert (WNZ : Wd <> 0) by (intros E; destruct (WIN0 E) as (W1 & _); clear - W1 KWH KOFF; lia).
        destruct (WIN1 WNZ) as (WH32 & WN32).
        assert (WSZE : wsz (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) = 32768) by (unfold wsz; cbn [c_w]; destruct (Wd =? 0) eqn:EW; [apply Z.eqb_eq in EW; contradiction| reflexivity]).
        Time zrunb [0x91760].
        zs. zs. zbr0 KWN.
        *
          zs. zs. (* M_W sits after 1.4's ld a4,40(s1) at 0x91760 (probe Pg32match4) *)
          eapply (m_win (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (wnext - (offset - (out - (osz - cout)))) (offset - (out - (osz - cout))));
            [exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| inf_vis_close| inf_hid_close| exact KA| exact WNZ
            | clear - KWN; lia| clear - WN32; lia| clear - KOFF; lia| clear - KLEFT COUT0 COUTN; gcbn; lia].
        *
          Time zrunb [0x9177c]. rewrite WSZE in SSC. zs. rewrite <- WSZE in SSC. zs. zs. zs. zs.
          eapply (m_win (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (32768 - (offset - (out - (osz - cout)) - wnext)) (offset - (out - (osz - cout)) - wnext));
            [exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| inf_vis_close| inf_hid_close| exact KA| exact WNZ
            | clear - KWH WH32 WN0; lia| clear; lia| clear - KWN; lia| clear - KLEFT COUT0 COUTN; gcbn; lia].
      +
        Time zrunb [0x9191c].
        pose proof (sinv_bad_ofP _ _ lf cf SI) as SIB.
        pose proof (meas_bad_ofP (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)) as MEB.
        unfold bad_ofP in SIB, MEB. st_norm SIB. st_norm MEB. subst mode. change (rank MATCH) with 14 in MEB.
        eapply (KB (IST MATCH last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
          [exact SIB| unfold bad_of; icx_cbn; clear - MEB; lia| exact ARR| change MATCH with 16204; inf_vis_close| inf_hid_close].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Time Qed.
End S.
End CANSEC1.
