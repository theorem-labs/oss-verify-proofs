(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjPjNum SjPjDig.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.A Require Import Layout Shadow RT_iface RT_iface2 D_defs D_kit Sj_akit Sj_acps Sj_hkit Sj_num_akit Sj_num_amem
     Sj_num_aframe Sj_num_lm_kit Sj_num_lm_pro Pj_defsA Pj_tocharsA_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zc_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section Pro.
  Variables (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (q lo NB : Z) (m0 : mem).
  Hypothesis ROOM : (lo + 160 + 0x10000 <= q)%Z.
  Hypothesis QTOP : (q + 16 <= 0x800000000000)%Z.
  Hypothesis Q16 : (q mod 16 = 0)%Z.
  Hypothesis LO : (0x6c9000 <= lo)%Z.
  Variable Q : machine_state -> Prop.

  Definition tc_call1_k : Prop :=
    forall (d : Z) xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 (xF : bvmap 5 word) (jl : list byte) (mm : mem),
      (d = 0 \/ d = 16)%Z ->
      rw_cells asegs mm (q - 128 - d) [CB (Z.to_nat (32 + d)) jl] ->
      rw_cells asegs mm (q + -96) [C8 (reg_get F 8); C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      mem_inv asegs mm -> munch [(q - 128 - d, q)]%Z m0 mm -> wmono asegs m0 mm -> stk asegs mm lo (q - 128 - d) ->
      evt asegs Q
        (MS (mkR (Z_to_bv 64 0xb8f5c) (Z_to_bv 64 (q - 128 - d)) gp (Z_to_bv 64 TPV_A) xt0 xt1 xt2 (Z_to_bv 64 q) (Z_to_bv 64 (q - 128 - d)) (Z_to_bv 64 128)
                 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 (Z_to_bv 64 NB) s4 s5 s6 s7 (Z_to_bv 64 2147450880) s9 s10 s11 xt3 xt4 xt5 xt6)
            xF (Z_to_bv 64 e_stack_malloc_1) fc None mm (seg_rom asegs)).

  Lemma tc_pro : tc_call1_k ->
    forall t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    mem_inv asegs m0 -> stk asegs m0 lo q -> client_consts m0 ->
    evt asegs Q
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV_A) t0 t1 t2 s0 s1 (Z_to_bv 64 NB) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PJ_TOCHARS_A) fc None m0 (seg_rom asegs)).
  Proof using ROOM QTOP Q16 LO.
    intros KC. intros until t6. intros MI ST (G1 & G2 & G3 & G4). unfold PJ_TOCHARS_A.
    unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in G1, G2, G3, G4.
    pose proof (munch_refl [(q - 128, q)]%Z m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    set (m := m0) in MI, ST, G1, G2, G3, G4, MU at 2, WM at 2 |- *. clearbody m.
    destruct (land_m32u (q + -128) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (d & Hd & LAND).
    zstep.
    carve_frame 128%nat ST.
    apply (rw_cells_split_CB asegs m _ [] 128 junk [] [8;24;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 14 nstep.
    zstep. rewrite LAND.
    do 9 zstep.
    zstep. if_cases KF; [exfalso; clear - KF; revert KF; vm_compute; intros KF; discriminate KF| clear KF].
    zstep. zstep.
    clear G1 G2 G3 G4.
    destruct (proj1 (num_rw_cells_app asegs _ _ [C8 (Z_to_bv 64 0); CB 24 j0] _) FR) as [LOCc SAVEDc]. clear FR.
    cbn [cells_size csize Nat.add] in SAVEDc. replace (q + -128 + Z.of_nat 32)%Z with (q + -96)%Z in SAVEDc by lia.
    destruct Hd as [-> | ->].
    -
      replace (q + -128 - 0)%Z with (q - 128 - 0)%Z by lia.
      destruct (rw_cells_forget asegs _ _ _ LOCc) as [jl LOCf]. cbn [cells_size csize Nat.add] in LOCf.
      eapply (KC 0%Z); [left; reflexivity| | exact SAVEDc| exact MI| | exact WM| ];
        [replace (q - 128 - 0)%Z with (q + -128)%Z by lia; exact LOCf
        | replace (q - 128 - 0)%Z with (q + -128)%Z by lia; exact MU
        | replace (q - 128 - 0)%Z with (q + -128)%Z by lia; exact ST].
    -
      destruct (stk_carve asegs m1 lo (q + -128) 16 ST ltac:(lia)) as [ST2 [jlo LOWc]]. clear ST. change (Z.of_nat 16) with 16%Z in ST2, LOWc.
      assert (LOCa : rw_cells asegs m1 (q + -128 - 16) ([CB 16 jlo] ++ [C8 (Z_to_bv 64 0); CB 24 j0])).
      { apply (proj2 (num_rw_cells_app asegs m1 (q + -128 - 16) [CB 16 jlo] [C8 (Z_to_bv 64 0); CB 24 j0])). split; [exact LOWc|].
        cbn [cells_size csize Nat.add]. replace (q + -128 - 16 + Z.of_nat 16)%Z with (q + -128)%Z by lia. exact LOCc. }
      destruct (rw_cells_forget asegs _ _ _ LOCa) as [jl LOCf]. cbn [app cells_size csize Nat.add] in LOCf.
      replace (q + -128 - 16)%Z with (q - 128 - 16)%Z in * by lia.
      eapply (KC 16%Z); [right; reflexivity| exact LOCf| exact SAVEDc| exact MI| | exact WM| exact ST2].
      eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros x Hx. lia.
  Qed.
End Pro.

Lemma ex_field_range : forall x, (0 <= ((2 * x) mod 18446744073709551616) ≫ 53 <= 2047)%Z.
Proof.
  intros x. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 53)%Z with 9007199254740992%Z.
  pose proof (Z.mod_pos_bound (2 * x) 18446744073709551616 ltac:(lia)). Z.div_mod_to_equations. lia.
Qed.

Section Hdr.
  Variable J : tcI.
  Hypothesis OK : tc_ok J.
  Variable mb : mem.
  Variable Q : machine_state -> Prop.

  Notation q := (ti_q J). Notation spq := (ti_spq J). Notation NB := (ti_NB J). Notation f := (ti_f J). Notation Sh := (ti_S J). Notation lo := (ti_lo J).
  Notation TCS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs9 xt3 xt4 xt5 xt6 xF xfc m :=
    (MS (mkR xra (Z_to_bv 64 spq) (ti_gp J) (Z_to_bv 64 TPV_A) xt0 xt1 xt2 (Z_to_bv 64 q) (Z_to_bv 64 spq) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
              (Z_to_bv 64 f) xs3 xs4 xs5 (Z_to_bv 64 Sh) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) xs9 (ti_s10 J) (ti_s11 J) xt3 xt4 xt5 xt6)
        xF (Z_to_bv 64 pc) xfc None m (seg_rom asegs)).

  Definition tc_rel_k : Prop :=
    forall (e : Z) xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs9 xt3 xt4 xt5 xt6 xF xfc (mm : mem),
      TINV J sh_poison mb mm -> frm0 xfc -> (NB < e <= NB + 27)%Z ->
      evt asegs Q (TCS 0xb945c xra xt0 xt1 xt2 (Z_to_bv 64 e) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs9 xt3 xt4 xt5 xt6 xF xfc mm).

  Definition tc_kern_k : Prop :=
    forall (EX sg : Z) xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs9 xt3 xt4 xt5 xt6 xF xfc (mm : mem),
      TINV J sh_poison mb mm -> frm0 xfc -> (0 <= EX <= 2047)%Z -> (0 <= sg <= 1)%Z ->
      evt asegs Q (TCS 0xe3a00 (Z_to_bv 64 0xb90d4) xt0 xt1 xt2 xa0 (Z_to_bv 64 EX) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (NB + sg)) xs4 (Z_to_bv 64 (f + 32)) xs9
                       xt3 xt4 xt5 xt6 xF xfc mm).

  Hypothesis KZ : tc_rel_k.
  Hypothesis KK : tc_kern_k.
  Hypothesis SHPN : nb_shz J mb.

  Ltac chk := zastep; zastep; zastep; zastep; if_false.

  Lemma tc_hdr : forall xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs9 xt3 xt4 xt5 xt6 xF (fc : bv 32) (jl jf js nb : list byte),
    frm0 fc ->
    rw_cells asegs mb spq [CB (Z.to_nat (32 + ti_d J)) jl] -> rw_cells asegs mb (q + -96) (tc_saved J) ->
    rw_cells asegs mb f [CB 120 jf] -> rw_cells asegs mb Sh [CB 16 js] -> rw_cells asegs mb NB [CB 40 nb] ->
    mem_inv asegs mb -> stk asegs mb lo spq ->
    evt asegs Q (MS (mkR (Z_to_bv 64 0xb8f5c) (Z_to_bv 64 spq) (ti_gp J) (Z_to_bv 64 TPV_A) xt0 xt1 xt2 (Z_to_bv 64 q) (Z_to_bv 64 spq) (Z_to_bv 64 f)
                          xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 NB) xs4 xs5 xs6 xs7 (Z_to_bv 64 2147450880) xs9 (ti_s10 J) (ti_s11 J) xt3 xt4 xt5 xt6)
                    xF (Z_to_bv 64 0xb8f5c) fc None mb (seg_rom asegs)).
  Proof using OK KZ KK SHPN.
    intros until nb. intros FRM LOC0 SAVED0 FRAME SHJ NBC MI0 ST0.

    assert (KKP : forall sg xa0 xa1 xa2 ya3 ya4 yF yfc mm, TINV J sh_poison mb mm -> frm0 yfc -> (0 <= sg <= 1)%Z ->
      evt asegs Q (TCS 0xb90b8 (Z_to_bv 64 0xb8f5c) xt0 xt1 xt2 xa0 xa1 xa2 ya3 ya4 xa5 xa6 xa7 (Z_to_bv 64 (NB + sg)) xs4 xs5 xs9 xt3 xt4 xt5 xt6 yF yfc mm)).
    { intros until mm. intros TI FRM' HSG. clear LOC0 SAVED0 FRAME SHJ NBC MI0 ST0. pose proof OK as OK'. destruct OK' as [_ _ _ _ _ Cnblo _ _ Cflo _ _ _ _ _ _ _ _ _ _].
      do 7 zastep.
      eapply evt_eq; [| eapply (KK _ sg)]; [num_st_eq | exact TI | exact FRM' | apply ex_field_range | exact HSG]. }

    assert (KZA : forall sg xa0 xa1 xa2 ya3 ya4 yF yfc mm, TINV J sh_poison mb mm -> frm0 yfc -> (0 <= sg <= 1)%Z ->
      evt asegs Q (TCS 0xb9024 (Z_to_bv 64 0xb8f5c) xt0 xt1 xt2 xa0 xa1 xa2 ya3 ya4 xa5 xa6 xa7 (Z_to_bv 64 (NB + sg)) xs4 xs5 xs9 xt3 xt4 xt5 xt6 yF yfc mm)).
    { intros until mm. intros TI FRM' HSG. clear LOC0 SAVED0 FRAME SHJ NBC MI0 ST0. ti_open TI. ti_env OK. unfold tc_W, ti_spq, ti_S in MU. unfold nb_shz, tc_W, ti_spq, ti_S in SHPN. unfold sh_poison, pz in SH.
      chk. zastep. zastep. astep. chk. zastep. zastep. astep. chk. zastep. zastep. astep.
      zastep. zastep. astep.
      zastep. if_cases K; zify_cond K.
      - clear K. eapply evt_eq; [| eapply (KZ (NB + sg + 3)%Z)]; [num_st_eq | ti_close | exact FRM' | clear - HSG; lia].
      - exfalso. clear - K Cflo. lia. }

    assert (KSZ : forall xa0 xa1 xa2 ya3 ya4 yF mm, TINV J sh_poison mb mm ->
      evt asegs Q (TCS 0xb9014 (Z_to_bv 64 0xb8f5c) xt0 xt1 xt2 xa0 xa1 xa2 ya3 ya4 xa5 xa6 xa7 (Z_to_bv 64 NB) xs4 xs5 xs9 xt3 xt4 xt5 xt6 yF fc mm)).
    { intros until mm. intros TI. clear LOC0 SAVED0 FRAME SHJ NBC MI0 ST0. pose proof TI as TI0. ti_open TI. ti_env OK. unfold tc_W, ti_spq, ti_S in MU. unfold nb_shz, tc_W, ti_spq, ti_S in SHPN. unfold sh_poison, pz in SH.
      zastep. if_cases KS; clear KS.
      -
        chk. zastep. astep. zastep. zastep. zastep. zastep.
        zastep. if_cases KZ0; clear KZ0.
        + eapply evt_eq; [| eapply (KZA 1%Z)]; [num_st_eq | ti_close | assumption | clear; lia].
        + eapply evt_eq; [| eapply (KKP 1%Z)]; [num_st_eq | ti_close | assumption | clear; lia].
      - zastep. zastep.
        zastep. if_cases KZ0; clear KZ0.
        + replace (Z_to_bv 64 NB) with (Z_to_bv 64 (NB + 0)) by (f_equal; lia).
          eapply evt_eq; [| eapply (KKP 0%Z)]; [num_st_eq | exact TI0 | assumption | clear; lia].
        + replace (Z_to_bv 64 NB) with (Z_to_bv 64 (NB + 0)) by (f_equal; lia).
          eapply evt_eq; [| eapply (KZA 0%Z)]; [num_st_eq | exact TI0 | assumption | clear; lia]. }

    rename LOC0 into LOC. rename SAVED0 into SAVED. rename MI0 into MI. rename ST0 into ST. ti_env OK. unfold nb_shz, tc_W, ti_spq, ti_S in SHPN.
    pose proof (munch_refl (tc_W J) mb) as MU. pose proof (wmono_refl asegs mb) as WM. unfold tc_W, ti_spq, ti_S in MU.
    apply (rw_cells_split_CB asegs _ _ [] _ jl [] [8; 7; 17; Z.to_nat (ti_d J)]%nat) in LOC; [| destruct (c_d J OK) as [E | E]; rewrite E; reflexivity].
    cbn [mk_CB_cells app] in LOC.
    apply (rw_cells_split_CB asegs _ _ [] 120 jf [] [8; 8; 8; 8; 40; 48]%nat) in FRAME; [| reflexivity]. cbn [mk_CB_cells app] in FRAME.
    apply (rw_cells_split_CB asegs _ _ [] 16 js [] (repeat 1%nat 16)) in SHJ; [| reflexivity]. cbn [repeat mk_CB_cells app] in SHJ.
    repeat match goal with H : rw_cells _ _ _ ?l |- _ => match l with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in H; clearbody j end end.
    destruct (proj1 (num_rw_cells_app asegs _ _ [_; _; _] _) FRAME) as [HDR FR1]. clear FRAME. cbn [cells_size csize Nat.add] in FR1.
    destruct (proj1 (num_rw_cells_app asegs _ _ [_] _) FR1) as [_ FR2]. clear FR1. cbn [cells_size csize Nat.add] in FR2.
    destruct (proj1 (num_rw_cells_app asegs _ _ [_] _) FR2) as [TMP _]. clear FR2.
    replace (f + Z.of_nat 24 + Z.of_nat 8)%Z with (f + 32)%Z in TMP by lia.
    pose proof (u8arr_of_rw_cells asegs _ _ _ _ TMP) as TA.
    lazymatch type of TA with u8arr _ _ _ ?tb => assert (TL : length tb = 40%nat) by (destruct TMP as [[Hwf _] _]; cbn in Hwf; tauto) end. clear TMP.
    pose proof (u8arr_of_rw_cells asegs _ _ _ _ NBC) as NA.
    assert (NL : length nb = 40%nat) by (destruct NBC as [[Hwf _] _]; cbn in Hwf; tauto). clear NBC.
    pose proof (tc_f8 J OK) as F8.
    zastep. zastep.
    zastep. if_cases KF; zify_cond KF; [clear KF | exfalso; clear - KF Cflo; lia].
    astep.
    do 9 zastep.
    astep. astep. astep.
    zastep. zastep.
    do 4 astep. zastep. do 12 astep.
    eapply evt_eq; [| eapply KSZ; ti_close]. num_st_eq.
  Qed.
End Hdr.
