(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjPjNum SjPjDig.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import Layout Shadow RT_iface RT_iface2 D_defs D_kit Sj_akit Sj_acps Sj_hkit Sj_num_akit Sj_num_amem
     Sj_num_aframe Sj_num_lm_kit Pj_defsA Pj_tocharsA_defs Pj_tocharsA_a Pj_tocharsA_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zc_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section Lay.
  Variable J : tcI.
  Hypothesis OK : tc_ok J.
  Variable mb : mem.
  Variable Q : machine_state -> Prop.
  Variables (e sg n : Z).
  Hypothesis HE : (SF_EMIN <= e <= SF_EMAX)%Z.
  Hypothesis HSG : (0 <= sg <= 1)%Z.
  Hypothesis HN : (1 <= n <= 20)%Z.
  Hypothesis SHPN : nb_shz J mb.

  Notation q := (ti_q J). Notation spq := (ti_spq J). Notation NB := (ti_NB J). Notation f := (ti_f J). Notation Sh := (ti_S J). Notation lo := (ti_lo J).
  Notation TCS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs9 xt3 xt4 xt5 xt6 xF xfc m :=
    (MS (mkR xra (Z_to_bv 64 spq) (ti_gp J) (Z_to_bv 64 TPV_A) xt0 xt1 xt2 (Z_to_bv 64 q) (Z_to_bv 64 spq) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
              (Z_to_bv 64 f) xs3 xs4 xs5 (Z_to_bv 64 Sh) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) xs9 (ti_s10 J) (ti_s11 J) xt3 xt4 xt5 xt6)
        xF (Z_to_bv 64 pc) xfc None m (seg_rom asegs)).

  Notation LS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xt3 xt4 xt5 xt6 xF xfc m :=
    (TCS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (NB + sg)) xs4 (Z_to_bv 64 n) (Z_to_bv 64 (n + e)) xt3 xt4 xt5 xt6 xF xfc m).

  Hypothesis KZ : tc_rel_k J mb Q.

  Definition tc_l1_k : Prop := forall xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm,
    TINV J sh_poison mb mm -> frm0 xfc -> (0 <= e)%Z -> (n + e <= 15)%Z ->
    evt asegs Q (LS e_asan_memset (Z_to_bv 64 0xbe368) xt0 xt1 xt2 (Z_to_bv 64 (NB + sg + n)) (Z_to_bv 64 48) (Z_to_bv 64 16) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (e mod 4294967296))
                    xt3 xt4 xt5 xt6 xF xfc mm).
  Definition tc_l2_k : Prop := forall xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm,
    TINV J sh_poison mb mm -> frm0 xfc -> (1 <= n + e <= 15)%Z ->
    evt asegs Q (LS e_asan_memmove (Z_to_bv 64 0xbe498) xt0 xt1 xt2 (Z_to_bv 64 (NB + sg + (n + e) + 1)) (Z_to_bv 64 (NB + sg + (n + e))) (Z_to_bv 64 16) xa3 xa4 xa5 xa6 xa7
                    (Z_to_bv 64 (NB + sg + (n + e))) xt3 xt4 xt5 xt6 xF xfc mm).
  Definition tc_l3_k : Prop := forall xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm,
    TINV J sh_poison mb mm -> frm0 xfc -> (-3 <= n + e <= 0)%Z ->
    evt asegs Q (LS e_asan_memcpy (Z_to_bv 64 0xbe3e0) xt0 xt1 xt2 (Z_to_bv 64 (spq + 15)) (Z_to_bv 64 (NB + sg)) (Z_to_bv 64 17) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (e mod 4294967296))
                    xt3 xt4 xt5 xt6 xF xfc mm).
  Definition tc_l4_k : Prop := forall xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm,
    TINV J sh_poison mb mm -> frm0 xfc -> (2 <= n)%Z ->
    evt asegs Q (LS e_asan_memmove (Z_to_bv 64 0xbe534) xt0 xt1 xt2 (Z_to_bv 64 (NB + sg + 2)) (Z_to_bv 64 (NB + sg + 1)) (Z_to_bv 64 16) xa3 xa4 xa5 xa6 xa7
                    (Z_to_bv 64 (NB + sg + 1)) xt3 xt4 xt5 xt6 xF xfc mm).

  Ltac mark_data :=
    repeat match goal with
    | x : word |- _ => lazymatch goal with _ : IsData x |- _ => fail | _ => idtac end; let M := fresh "DM" in assert (M : IsData x) by exact Logic.I
    end.
  Ltac lay_open TI :=
    ti_open TI; ti_env OK;
    match goal with M : munch _ mb _ |- _ => unfold tc_W, ti_spq, ti_S in M end;
    match goal with P : nb_shz _ _ |- _ => unfold nb_shz, tc_W, ti_spq, ti_S in P end;
    match goal with H : (SF_EMIN <= _ <= SF_EMAX)%Z |- _ => unfold SF_EMIN, SF_EMAX in H end;
    match goal with H : rw_cells _ _ _ sh_poison |- _ => unfold sh_poison, pz in H | H : rw_cells _ _ _ sh_zero |- _ => unfold sh_zero, pz in H end;
    pose proof (tc_f8 J OK) as F8; mark_data.

  Ltac cut_rel e tac := first [ eapply evt_eq; [| eapply (KZ e)]; [num_st_eq | ti_close | assumption | tac] | fail 100 "cut: release" ].

  Ltac chk := zastep; zastep; zastep; zastep; if_false.

  Ltac to_rel e tac := zastep; zastep; astep; zastep;
    let K := fresh "K" in if_cases K; zify_cond K;
    [clear K; cut_rel e tac | exfalso; match goal with C : (0x6d2000 <= ti_f J)%Z |- _ => clear - K C; lia end].

  Lemma tc_exp : forall (c : Z) (pt : word) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs5 xt3 xt4 xt5 xt6 xF xfc mm,
    TINV J sh_poison mb mm -> frm0 xfc -> (0 <= c <= 21)%Z ->
    evt asegs Q (TCS 0xbe550 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (NB + c)) xs4 xs5 pt xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK KZ SHPN.
    intros until mm. intros TI FRM HC.
    assert (K57 : forall d ya1 ya2 ya3 ya4 ya5 ya6 ys9 mm', TINV J sh_poison mb mm' -> (5 <= d <= 6)%Z ->
      evt asegs Q (TCS 0xbe638 xra xt0 xt1 xt2 (Z_to_bv 64 (NB + c + d)) ya1 ya2 ya3 ya4 ya5 ya6 xa7 (Z_to_bv 64 (NB + c)) xs4 xs5 ys9 xt3 xt4 xt5 xt6 xF xfc mm')).
    { intros until mm'. intros TI' HD. lay_open TI'.
      zastep. chk. astep. zastep. chk. zastep. astep.
      to_rel (NB + c + d)%Z ltac:(clear - HC HD; lia). }
    assert (K3d : forall ya0 ya1 ya2 ya3 ys9 mm', TINV J sh_poison mb mm' ->
      evt asegs Q (TCS 0xbe5d4 xra xt0 xt1 xt2 ya0 ya1 ya2 ya3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (NB + c)) xs4 xs5 ys9 xt3 xt4 xt5 xt6 xF xfc mm')).
    { intros until mm'. intros TI'. lay_open TI'.
      zastep. chk. do 19 astep. astep.
      eapply evt_eq; [| eapply (K57 6%Z); [ti_close | clear; lia]]. num_st_eq. }
    assert (K2d : forall ya0 ya1 ya2 ya3 ys9 mm', TINV J sh_poison mb mm' ->
      evt asegs Q (TCS 0xbe5ac xra xt0 xt1 xt2 ya0 ya1 ya2 ya3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (NB + c)) xs4 xs5 ys9 xt3 xt4 xt5 xt6 xF xfc mm')).
    { intros until mm'. intros TI'. lay_open TI'.
      do 10 astep.
      eapply evt_eq; [| eapply (K57 5%Z); [ti_close | clear; lia]]. num_st_eq. }
    assert (K4c4 : forall ya1 ya2 mm', TINV J sh_poison mb mm' ->
      evt asegs Q (TCS 0xbe580 xra xt0 xt1 xt2 (Z_to_bv 64 (NB + c + 2)) ya1 ya2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (NB + c)) xs4 xs5 pt xt3 xt4 xt5 xt6 xF xfc mm')).
    { intros until mm'. intros TI'. lay_open TI'.
      chk. zastep. astep. astep. astep. zastep. astep.
      zastep. if_cases KD; clear KD.
      - eapply evt_eq; [| eapply K3d; ti_close]. num_st_eq.
      - eapply evt_eq; [| eapply K2d; ti_close]. num_st_eq. }
    lay_open TI.
    zastep. chk. zastep. zastep. astep.
    zastep. if_cases KS.
    - clear KS. zastep. eapply evt_eq; [| eapply K4c4; ti_close]. num_st_eq.
    - clear KS. zastep. zastep. eapply evt_eq; [| eapply K4c4; ti_close]. num_st_eq.
  Qed.

End Lay.
