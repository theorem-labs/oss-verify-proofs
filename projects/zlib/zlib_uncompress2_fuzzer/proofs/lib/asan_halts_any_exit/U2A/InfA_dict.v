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
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow U2AKit U2AArr U2AObj U2AClient U2AStore U2AIface U2ACall InfABase InfAKit InfAGlue InfAGlue_w7 InfPure InfPure_w7 InfPure_head AdlUIface InfAEpiK InfA_w7base InfA_head.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.
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
  Hypothesis ADLN : adler32_null_stmtU.

  Notation KALLB cx ly B := (KALL cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh B).
  Notation HIDm cx ly m := (inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m).
  Notation GARM cx ly Lb X := (garm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).
  Notation KEPI cx ly := (LV_KEPI AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly).

  Lemma flags_not_m1 : forall cx st lf cf, sinv cx st lf cf -> t_mode st <> HEAD -> t_mode st <> BAD -> t_flags st <> -1.
  Proof. intros cx st lf cf (_ & _ & _ & Mo) H1 H2 Hf. destruct (proj1 (proj2 Mo) Hf) as [[E|E] _]; congruence. Qed.

  (* stated at the 1.4 DICT entry state, InfABase's ARM_MS (the 1.4 dispatch homes), with the frame
     cells pinned as arm_stmtA pins them (v16 = (S+108)>>3, v504 = (S+56)>>3) *)
  Lemma dict_body : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x22 : word) (m : amem),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = DICT -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    inf_vis cx ly st lf cf wf fo payload v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) v240 (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    GARM cx ly 0x8ed20 TYPE -> KEPI cx ly ->
    evtF asegs RNG POST
      (* a0 is free: F0 from the dispatch, the mode value on the fall-through from DICTID (1.4 0x8ec3c) *)
      (MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 (Z_to_bv 64 (c_p cx + 56)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 2147450880)
               x22 (Z_to_bv 64 (-3)) (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly))
               (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 (c_p cx + 28)) (Z_to_bv 64 (c_osz cx - t_cout st))
               (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880)) (Z_to_bv 64 (c_p cx + 108)))
          FR (Z_to_bv 64 0x8ec78) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA GT KE.
    pose proof HID as (AH0 & _). pose proof (AI_rtcells AI _ _ _ _ _ AH0) as ART. unfold artcells in ART.
    destruct ART as (_ & RTG & _ & _ & RTS & _).
    pose proof (flags_not_m1 _ _ _ _ SI ltac:(rewrite MODE; cbv; discriminate) ltac:(rewrite MODE; cbv; discriminate)) as FNM.
    inf_arm_open.
    pose proof (pow2_le_40 bits ltac:(lia)) as P40.
    Time zrunb [0x92c2c; 0x95b24; 0x8ed20].
    assert (MLT : (t_mode (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) <? CHECK) = true)
      by (cbn [t_mode]; rewrite MODE; reflexivity).
    if_cases KHD.
    -
      Time zrunb [0x92c2c; 0x95b24; 0x8ed20].
      callq (adler32_null_callz RNG gp tp FR fc ADLN lo).
      all: lazymatch goal with
           | |- evtF _ _ _ _ => idtac
           | |- stk _ _ _ _ => eassumption
           | |- mem_inv _ _ => eassumption
           | |- rw_cells _ _ _ _ => eassumption
           | |- rng _ ?l _ => first [ constr_eq l lo; eapply rng_sub'; [exact RSTK| lia] | exact RI ]
           | |- _ => unfold KHIGH; lia
           end.
      Time zrunb [0x92c2c; 0x95b24; 0x8ed20].
      show_mkR.
      assert (SI' : sinv (ICX u S D n 6336320 osz Wd cin0 cout0 W0 K0 zc)
                      (hd_st (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) TYPE flags cin hold bits) lf cf).
      { apply sinv_hd; [exact SI| exact MLT| cbv [HEAD DICTID DICT TYPE TYPEDO STORED CHECK LENGTH DONE BAD]; do 3 right; left; reflexivity| left; reflexivity
                        | intros X; exfalso; apply FNM; exact X| cbn [t_cin c_n]; lia| lia| lia| lia| cbn [t_cin t_bits c_n]; lia]. }
      assert (ME' : meas (ICX u S D n 6336320 osz Wd cin0 cout0 W0 K0 zc)
                      (hd_st (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) TYPE flags cin hold bits)
                    < meas (ICX u S D n 6336320 osz Wd cin0 cout0 W0 K0 zc) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)).
      { apply meas_hd. right. cbn [t_cin t_bits t_mode c_n]. split; [lia| rewrite MODE; vm_compute; reflexivity]. }
      eapply (GT (hd_st (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) TYPE flags cin hold bits) lf cf wf fo);
        [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI'| exact ARR| unfold hd_st; inf_vis_close| inf_hid_close| eapply KALL_mono; [| exact KA]; lia].
    -
      Time zrunb [0x92c2c; 0x95b24; 0x8ed20].
      show_mkR.
      eapply (KE (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) 2 lf cf wf fo);
        [exact SI| exact ARR| lia| inf_vis_close| inf_hid_close].
    (* v240 is a vestige binder at 1.4 *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.

  Theorem dict_arm : forall cx ly, GARM cx ly 0x8ed20 TYPE -> KEPI cx ly ->
    arm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh 0x8ec78 DICT.
  Proof.
    intros cx ly GT KE. unfold arm_stmtA, ARM_MS. intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA.
    eapply dict_body; eassumption.
  Qed.
End S.
End CANSEC1.
