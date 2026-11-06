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
     Sj_num_aframe Sj_num_lm_kit Pj_defsA Pj_tocharsA_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zc_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Definition sh_zero : list cell :=
  [pz (-15); pz (-15); pz (-15); pz (-15); pz 0; pz 0; pz 0; pz 0; pz 0; pz (-13); pz (-13); pz (-13); pz (-13); pz (-13); pz (-13); pz (-13)].

Lemma lor_2r_1 : forall r, (0 <= r)%Z -> Z.lor (2 * r) 1 = (2 * r + 1)%Z.
Proof.
  intros r Hr.
  assert (L : Z.land (2 * r) 1 = 0%Z).
  { change 1%Z with (Z.ones 1). rewrite Z.land_ones by lia. change (2 ^ 1)%Z with 2%Z. rewrite Z.mul_comm. apply Z.mod_mul. lia. }
  rewrite <- (Z.lxor_lor _ _ L). symmetry. apply Z.add_nocarry_lxor. exact L.
Qed.

Section Dig.
  Variable J : tcI.
  Hypothesis OK : tc_ok J.
  Variable mb : mem.
  Variable Q : machine_state -> Prop.
  Variables (e sg : Z).
  Hypothesis HE : (SF_EMIN <= e <= SF_EMAX)%Z.
  Hypothesis HSG : (0 <= sg <= 1)%Z.
  Hypothesis SHPN : nb_shz J mb.
  Hypothesis SHPD : dig_shz J mb.

  Notation q := (ti_q J). Notation spq := (ti_spq J). Notation NB := (ti_NB J). Notation f := (ti_f J). Notation Sh := (ti_S J). Notation lo := (ti_lo J).
  Notation TCS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs9 xt3 xt4 xt5 xt6 xF xfc m :=
    (MS (mkR xra (Z_to_bv 64 spq) (ti_gp J) (Z_to_bv 64 TPV_A) xt0 xt1 xt2 (Z_to_bv 64 q) (Z_to_bv 64 spq) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
              (Z_to_bv 64 f) xs3 xs4 xs5 (Z_to_bv 64 Sh) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) xs9 (ti_s10 J) (ti_s11 J) xt3 xt4 xt5 xt6)
        xF (Z_to_bv 64 pc) xfc None m (seg_rom asegs)).

  Notation DS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc m :=
    (TCS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (NB + sg)) (Z_to_bv 64 (e mod 4294967296)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 56))
         xt3 xt4 xt5 xt6 xF xfc m).

  Definition tc_copy_k : Prop :=
    forall (n : Z) xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc (mm : mem),
      TINV J sh_zero mb mm -> frm0 xfc -> (1 <= n <= 20)%Z ->
      evt asegs Q (TCS e_asan_memcpy (Z_to_bv 64 0xbe2f8) xt0 xt1 xt2 (Z_to_bv 64 (NB + sg)) (Z_to_bv 64 (f + 56 - n)) (Z_to_bv 64 16) xa3 xa4 xa5 xa6 xa7
                       (Z_to_bv 64 (NB + sg)) (Z_to_bv 64 (e mod 4294967296)) (Z_to_bv 64 (f + 56 - n)) (Z_to_bv 64 (f + 56)) xt3 xt4 xt5 xt6 xF xfc mm).
  Hypothesis KC : tc_copy_k.

  Lemma sh_zero_zc : forall (m : mem), rw_cells asegs m Sh sh_zero ->
    rw_cells asegs m (f / 8 + 2147450884) [CB 5 (repeat (Z_to_bv 8 0) 5)].
  Proof.
    intros m SH. unfold sh_zero, pz in SH.
    destruct (proj1 (num_rw_cells_app asegs m Sh [_; _; _; _] _) SH) as [_ SH1]. cbn [cells_size csize Nat.add] in SH1.
    destruct (proj1 (num_rw_cells_app asegs m _ [_; _; _; _; _] _) SH1) as [SH2 _].
    unfold ti_S in SH2. replace (f / 8 + 2147450880 + Z.of_nat 4)%Z with (f / 8 + 2147450884)%Z in SH2 by lia.
    pose proof (rw_cells_merge_all _ _ _ SH2) as M. cbn [cells_size csize Nat.add cells_bytes cbytes app] in M.
    exact M.
  Qed.

  Ltac dig_open TI :=
    pose proof (sh_zero_zc _ ltac:(destruct TI as (_ & _ & _ & _ & SHx & _); exact SHx)) as ZC;
    ti_open TI; ti_env OK;
    match goal with M : munch _ mb _ |- _ => unfold tc_W, ti_spq, ti_S in M end;
    match goal with P : nb_shz _ _ |- _ => unfold nb_shz, tc_W, ti_spq, ti_S in P end;
    match goal with P : dig_shz _ _ |- _ => unfold dig_shz, tc_W, ti_spq, ti_S in P end;
    match goal with H : (SF_EMIN <= _ <= SF_EMAX)%Z |- _ => unfold SF_EMIN, SF_EMAX in H end;
    match goal with H : rw_cells _ _ _ sh_zero |- _ => unfold sh_zero, pz in H end;
    pose proof (tc_f8 J OK) as F8.

  Ltac dig_table m :=
    let tb := fresh "tb" in let TL := fresh "TBL" in let TB := fresh "TB" in
    destruct (image_readable_b asegs m 200 0x29df0 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (tb & TL & TB).

  Lemma tc_22c : forall n xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm,
    TINV J sh_zero mb mm -> frm0 xfc -> (1 <= n <= 20)%Z ->
    evt asegs Q (TCS 0xbe2e8 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (NB + sg)) (Z_to_bv 64 (e mod 4294967296)) (Z_to_bv 64 (f + 56 - n)) (Z_to_bv 64 (f + 56))
                     xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK KC.
    intros until mm. intros TI FRM HN. ti_env OK.
    do 4 astep. unfold e_asan_memcpy in KC. apply KC; [exact TI| exact FRM| exact HN].
  Qed.

  Lemma tc_tail2 : forall (j w : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm,
    TINV J sh_zero mb mm -> frm0 xfc -> (10 <= w < 100)%Z -> (1 <= j <= 10)%Z ->
    evt asegs Q (DS 0xbe258 xra xt0 xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 (f + 36 + 2 * j)) (Z_to_bv 64 w) xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK KC SHPN SHPD.
    intros until mm. intros TI FRM HW HJ. dig_open TI. dig_table mm.
    zastep. zastep. zastep. zastep.
    rewrite shl1. rewrite (swrap32_id (2 * w)) by lia.

    zastep. zastep. zastep. zastep. if_false.

    zastep. zastep. zastep. zastep. astep. zastep. if_false.

    astep.

    zastep. rewrite (lor_2r_1 w) by lia. zastep. zastep. zastep. zastep. zastep. if_false.

    zastep. zastep. zastep. zastep. astep. zastep. if_false.
    astep. astep.
    eapply evt_eq; [| eapply (tc_22c (22 - 2 * j)%Z); [ti_close | exact FRM | lia]].
    num_st_eq.
  Qed.

  Lemma tc_tail1 : forall (j w : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm,
    TINV J sh_zero mb mm -> frm0 xfc -> (0 <= w < 10)%Z -> (1 <= j <= 10)%Z ->
    evt asegs Q (DS 0xbe2cc xra xt0 xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 (f + 36 + 2 * j)) (Z_to_bv 64 w) xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK KC SHPN SHPD.
    intros until mm. intros TI FRM HW HJ. dig_open TI.

    zastep. zastep. zastep. zastep. zastep. if_false.
    astep. astep.
    eapply evt_eq; [| eapply (tc_22c (21 - 2 * j)%Z); [ti_close | exact FRM | lia]].
    num_st_eq.
  Qed.

  Lemma tc_194 : forall (j w : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm,
    TINV J sh_zero mb mm -> frm0 xfc -> (0 <= w < 100)%Z -> (1 <= j <= 10)%Z ->
    evt asegs Q (DS 0xbe250 xra xt0 xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 (f + 36 + 2 * j)) (Z_to_bv 64 w) xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK KC SHPN SHPD.
    intros until mm. intros TI FRM HW HJ. pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ Cflo Cfhi _ _ _ _ _ _ _ _ _].
    zastep.
    zastep. if_cases K; zify_cond K.
    - eapply evt_eq; [| eapply (tc_tail1 j w); [exact TI | exact FRM | lia | lia]]. num_st_eq.
    - eapply evt_eq; [| eapply (tc_tail2 j w); [exact TI | exact FRM | lia | lia]]. num_st_eq.
  Qed.

  Lemma tc_loop : forall (fu : nat) (j w : Z) xra xt2 xa2 xa3 xa4 xt3 xt4 xt5 xt6 xF xfc mm,
    TINV J sh_zero mb mm -> frm0 xfc -> (100 <= w < 100 ^ j)%Z -> (w < 18446744073709551616)%Z -> (j <= 10)%Z -> (j <= Z.of_nat fu)%Z ->
    evt asegs Q (TCS 0xbe180 xra (Z_to_bv 64 624) (Z_to_bv 64 (f + 36 + 2 * j)) xt2 (Z_to_bv 64 w) (Z_to_bv 64 (f + 35 + 2 * j)) xa2 xa3 xa4
                     (Z_to_bv 64 100) (Z_to_bv 64 DIV100_MAGIC) (Z_to_bv 64 0x29df0)
                     (Z_to_bv 64 (NB + sg)) (Z_to_bv 64 (e mod 4294967296)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 56)) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK KC SHPN SHPD.
    induction fu as [|fu IH]; intros until mm; intros TI FRM HW W64 HJ HF.
    { exfalso. pose proof (pow100_ge2 w j HW). lia. }
    pose proof (pow100_ge2 w j HW) as J2.
    pose proof (pow100_step w j ltac:(lia) ltac:(lia)) as HQ.
    dig_open TI. dig_table mm. unfold DIV100_MAGIC in *.
    zstep. zstep. zstep.
    change 2951479051793528259%Z with DIV100_MAGIC. rewrite (div100_machine w) by lia.
    zastep. zastep.
    replace (w - w / 100 * 100)%Z with (w mod 100)%Z by (Z.div_mod_to_equations; lia).
    assert (R100 : (0 <= w mod 100 < 100)%Z) by (apply Z.mod_pos_bound; lia).
    set (r := (w mod 100)%Z) in *.
    rewrite (swrap32_id r) by lia.
    zastep. try rewrite (Z.mod_small r) by lia. rewrite shl1. rewrite (swrap32_id (2 * r)) by lia.
    zastep.

    zastep. zastep. zastep. zastep. if_false.

    zastep. zastep. zastep. zastep. astep. zastep. if_false.

    zastep. zastep. rewrite (lor_2r_1 r) by lia.
    astep.

    zastep. zastep. zastep. zastep. zastep. if_false.
    zastep. zastep. zastep. astep. zastep. if_false.
    astep.

    zastep. zastep. zastep. zastep.
    zastep. if_cases K; zify_cond K.
    -
      assert (W4 : (10000 <= w)%Z).
      { rewrite Z.shiftr_div_pow2 in K by lia. change (2 ^ 4)%Z with 16%Z in K. Z.div_mod_to_equations. lia. }
      eapply evt_eq; [| eapply (IH (j - 1)%Z (w / 100)%Z); [ti_close | exact FRM | | | lia | lia]].
      + num_st_eq.
      + split; [Z.div_mod_to_equations; lia| lia].
      + Z.div_mod_to_equations; lia.
    - assert (W4 : (w < 10000)%Z).
      { rewrite Z.shiftr_div_pow2 in K by lia. change (2 ^ 4)%Z with 16%Z in K. Z.div_mod_to_equations. lia. }
      assert (Q100 : (0 <= w / 100 < 100)%Z) by (Z.div_mod_to_equations; lia).
      zastep.
      eapply evt_eq; [| eapply (tc_194 (j - 1)%Z (w / 100)%Z); [ti_close | exact FRM | lia | lia]].
      num_st_eq.
  Qed.

  Lemma tc_dig : forall (wd : word) xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs9 xt3 xt4 xt5 xt6 xF xfc mm,
    TINV J sh_poison mb mm -> frm0 xfc ->
    evt asegs Q (TCS 0xbe140 xra xt0 xt1 xt2 wd (Z_to_bv 64 (e mod 4294967296)) xa2 xa3 xa4 xa5 xa6 xa7
                     (Z_to_bv 64 (NB + sg)) xs4 (Z_to_bv 64 (f + 32)) xs9 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK KC SHPN SHPD.
    intros until mm. intros TI FRM.
    pose proof (bv_unsigned_in_range 64 wd) as WR. unfold bv_modulus in WR. cbn in WR.
    rewrite <- (Z_to_bv_bv_unsigned wd). set (w := bv_unsigned wd) in *. clearbody w.
    ti_open TI. ti_env OK. unfold tc_W, ti_spq, ti_S in MU. unfold sh_poison, pz in SH.
    zastep.
    do 5 astep.
    zastep. zastep.
    zastep. if_cases K; zify_cond K.
    -
      zastep. zastep.
      eapply evt_eq; [| eapply (tc_194 10%Z w); [ti_close | exact FRM | lia | lia]]. num_st_eq.
    - do 7 zastep.
      eapply evt_eq; [| eapply (tc_loop 10%nat 10%Z w); [ti_close | exact FRM | | lia | lia | lia]].
      + num_st_eq.
      + change (100 ^ 10)%Z with 100000000000000000000%Z. lia.
  Qed.
End Dig.
