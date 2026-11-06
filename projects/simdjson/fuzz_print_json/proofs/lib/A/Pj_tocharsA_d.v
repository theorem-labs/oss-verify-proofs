(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast SFModel.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjPjNum SjPjDig.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.A Require Import Layout Shadow RT_iface RT_iface2 D_defs D_kit Sj_akit Sj_acps Sj_hkit Sj_num_akit Sj_num_amem
     Sj_num_aframe Sj_num_lm_kit Pj_defsA Pj_tocharsA_defs Pj_tocharsA_a Pj_tocharsA_b Pj_tocharsA_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zc_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section Disp.
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

  Hypothesis KZ : tc_rel_k J mb Q.
  Hypothesis KL1 : tc_l1_k J mb Q e sg n.
  Hypothesis KL2 : tc_l2_k J mb Q e sg n.
  Hypothesis KL3 : tc_l3_k J mb Q e sg n.
  Hypothesis KL4 : tc_l4_k J mb Q e sg n.

  Ltac mark_data :=
    repeat match goal with
    | x : word |- _ => lazymatch goal with _ : IsData x |- _ => fail | _ => idtac end; let M := fresh "DM" in assert (M : IsData x) by exact Logic.I
    end.
  Ltac disp_open TI :=
    pose proof (sh_zero_zc J _ ltac:(destruct TI as (_ & _ & _ & _ & SHx & _); exact SHx)) as ZC;
    ti_open TI; ti_env OK;
    match goal with M : munch _ mb _ |- _ => unfold tc_W, ti_spq, ti_S in M end;
    match goal with P : nb_shz _ _ |- _ => unfold nb_shz, tc_W, ti_spq, ti_S in P end;
    match goal with H : (SF_EMIN <= _ <= SF_EMAX)%Z |- _ => unfold SF_EMIN, SF_EMAX in H end;
    match goal with H : rw_cells _ _ _ sh_zero |- _ => unfold sh_zero, pz in H end;
    pose proof (tc_f8 J OK) as F8; mark_data.
  Ltac lay_open TI :=
    ti_open TI; ti_env OK;
    match goal with M : munch _ mb _ |- _ => unfold tc_W, ti_spq, ti_S in M end;
    match goal with P : nb_shz _ _ |- _ => unfold nb_shz, tc_W, ti_spq, ti_S in P end;
    match goal with H : (SF_EMIN <= _ <= SF_EMAX)%Z |- _ => unfold SF_EMIN, SF_EMAX in H end;
    match goal with H : rw_cells _ _ _ sh_poison |- _ => unfold sh_poison, pz in H end;
    pose proof (tc_f8 J OK) as F8; mark_data.
  Ltac chk := zastep; zastep; zastep; zastep; if_false.

  Lemma tc_c0 : forall xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm,
    TINV J sh_zero mb mm -> frm0 xfc ->
    evt asegs Q (TCS 0xb928c (Z_to_bv 64 0xb928c) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                     (Z_to_bv 64 (NB + sg)) (Z_to_bv 64 (e mod 4294967296)) (Z_to_bv 64 (f + 56 - n)) (Z_to_bv 64 (f + 56)) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK KZ KL1 KL2 KL3 KL4 SHPN HE HSG HN.
    intros until mm. intros TI FRM.

    assert (K2fc : forall ya0 ya1 ya2 mm', TINV J sh_poison mb mm' ->
      evt asegs Q (TCS 0xb934c (Z_to_bv 64 0xb928c) xt0 xt1 xt2 ya0 ya1 ya2 xa3 xa4 xa5 xa6 xa7
                       (Z_to_bv 64 (NB + sg)) (Z_to_bv 64 (e mod 4294967296)) (Z_to_bv 64 n) (Z_to_bv 64 (n + e)) xt3 xt4 xt5 xt6 xF xfc mm')).
    { intros until mm'. intros TI'. lay_open TI'.
      zastep. zastep.
      rewrite land_W64. change (2 ^ 64)%Z with 18446744073709551616%Z.
      rewrite swrap32_Z. change ((?x + 2147483648) mod 4294967296 - 2147483648)%Z with (sw32 x).
      rewrite (sw32_mod64_add (n + e) (-16)) by (clear - HE HN; lia).
      zastep. if_cases K; zify_cond K; rewrite land_W64 in K; change (2 ^ 64)%Z with 18446744073709551616%Z in K.
      {
        assert (P1 : (1 <= n + e <= 15)%Z) by (clear - K HE HN; Z.div_mod_to_equations; lia). clear K.
        do 5 zastep.
        eapply evt_eq; [| eapply KL2; [ti_close | exact FRM | exact P1]]. num_st_eq. }
      assert (P1 : (n + e <= 0 \/ 16 <= n + e)%Z) by (clear - K HE HN; Z.div_mod_to_equations; lia). clear K.
      zastep. zastep.
      rewrite land_W64. change (2 ^ 64)%Z with 18446744073709551616%Z.
      rewrite swrap32_Z. change ((?x + 2147483648) mod 4294967296 - 2147483648)%Z with (sw32 x).
      rewrite (sw32_mod64_add (n + e) 3) by (clear - HE HN; lia).
      zastep. if_cases K; zify_cond K; rewrite land_W64 in K; change (2 ^ 64)%Z with 18446744073709551616%Z in K.
      {
        clear K. zastep.
        zastep. if_cases K1; zify_cond K1.
        -
          eapply evt_eq; [| eapply (tc_exp J OK mb Q SHPN KZ sg (Z_to_bv 64 (n + e))); [ti_close | exact FRM | clear - HSG; lia]].
          replace (NB + sg)%Z with (NB + sg + 0)%Z at 1 by lia. num_st_eq.
        - do 5 zastep.
          eapply evt_eq; [| eapply KL4; [ti_close | exact FRM | clear - K1 HN; lia]]. num_st_eq. }

      assert (P3 : (-3 <= n + e <= 0)%Z) by (clear - K P1 HE HN; Z.div_mod_to_equations; lia). clear K.
      do 4 zastep.
      eapply evt_eq; [| eapply KL3; [ti_close | exact FRM | exact P3]]. num_st_eq. }
    disp_open TI.
    zastep. chk. zastep. zastep. zastep. zastep. astep. zastep. if_false.
    clear ZC. astep.
    zastep.
    replace (bv_swrap 32 (f + 56 - (f + 56 - n)))%Z with n by (replace (f + 56 - (f + 56 - n))%Z with n by lia; symmetry; apply swrap32_id; clear - HN; lia).
    zastep.
    replace (bv_swrap 32 (e mod 4294967296 + 0)) with e by (rewrite swrap32_Z; clear - HE; Z.div_mod_to_equations; lia).
    zastep. do 5 astep.
    zastep.
    replace (bv_swrap 32 (n + e mod 4294967296)) with (n + e)%Z by (rewrite swrap32_Z; symmetry; apply sw32_add_mod32; clear - HE HN; lia).
    zastep. if_cases K1; zify_cond K1; rewrite land_W64 in K1; change (2 ^ 64)%Z with 18446744073709551616%Z in K1.
    {   clear K1. eapply evt_eq; [| eapply K2fc; ti_close]. num_st_eq. }
    assert (E0 : (0 <= e)%Z) by (clear - K1 HE; Z.div_mod_to_equations; lia). clear K1.
    zastep.
    zastep. if_cases K2; zify_cond K2.
    {   clear K2. eapply evt_eq; [| eapply K2fc; ti_close]. num_st_eq. }
    rewrite signed_of_Z in K2 by (clear - HE HN; lia).

    do 4 zastep.
    eapply evt_eq; [| eapply KL1; [ti_close | exact FRM | exact E0 | clear - K2; lia]]. num_st_eq.
  Qed.
End Disp.
