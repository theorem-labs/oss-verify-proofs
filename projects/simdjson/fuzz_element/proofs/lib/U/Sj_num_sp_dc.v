(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjNumber SjNumU.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_num_kitu Sj_num_kitn Sj_num_sp_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac nnorm ::= nnorm_u.
Local Ltac num_abstract_data ::= num_abstract_data_u.

Lemma magic_10000 : forall v, (0 <= v < 18446744073709551616 -> v * 3777893186295716171 / 18446744073709551616 / 2048 = v / 10000)%Z.
Proof. intros. Z.div_mod_to_equations. lia. Qed.
Lemma magic_100 : forall v, (0 <= v < 18446744073709551616 -> (v / 4) * 2951479051793528259 / 18446744073709551616 / 4 = v / 100)%Z.
Proof. intros. Z.div_mod_to_equations. lia. Qed.
Lemma magic_10 : forall v, (0 <= v < 18446744073709551616 -> v * 14757395258967641293 / 18446744073709551616 / 8 = v / 10)%Z.
Proof. intros. Z.div_mod_to_equations. lia. Qed.

Lemma magic_10000_m : forall v, (0 <= v < 18446744073709551616)%Z ->
  Z.shiftr (Z.shiftr (v * 3777893186295716171) 64 mod 18446744073709551616) 11 = (v / 10000)%Z.
Proof.
  intros v H. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 64)%Z with 18446744073709551616%Z. change (2 ^ 11)%Z with 2048%Z.
  rewrite Z.mod_small by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). apply magic_10000. exact H.
Qed.
Lemma magic_100_m : forall v, (0 <= v < 18446744073709551616)%Z ->
  Z.shiftr (Z.shiftr (Z.shiftr v 2 * 2951479051793528259) 64 mod 18446744073709551616) 2 = (v / 100)%Z.
Proof.
  intros v H. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 64)%Z with 18446744073709551616%Z. change (2 ^ 2)%Z with 4%Z.
  assert (Q : (0 <= v / 4 < 4611686018427387904)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite Z.mod_small by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). apply magic_100. exact H.
Qed.
Ltac shr2div :=
  repeat match goal with
  | H : context [Z.shiftr ?x 4] |- _ => rewrite (Z.shiftr_div_pow2 x 4) in H by lia; change (2 ^ 4)%Z with 16%Z in H
  end.

Lemma spu_sx32_small : forall x, (0 <= x < 2147483648)%Z -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x H. unfold sx32. rewrite unsigned_lit by lia. rewrite swrap32_id by lia. reflexivity. Qed.

Lemma spu_c8_split_lo : forall segs (m : mem) A d, rw_cells segs m A [C8 (Z_to_bv 64 d)] -> (0 <= d < 4294967296)%Z ->
  rw_cells segs m A [C4 (Z_to_bv 64 d); C4 (Z_to_bv 64 0)].
Proof.
  intros segs m A d [[Hwf Hb] Hw] Hd. split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes] in *. rewrite app_nil_r in Hb.
    replace (le4 (Z_to_bv 64 d) ++ le4 (Z_to_bv 64 0) ++ []) with (le8 (Z_to_bv 64 d)); [exact Hb|].
    unfold le8, word_to_le_bytes, le4. rewrite !unsigned_lit by lia.
    cbn [Z_to_le_bytes app]. rewrite !Z.shiftr_shiftr by lia.
    assert (HS : forall k, (32 <= k)%Z -> Z.shiftr d k = 0%Z).
    { intros k Hk. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. split; [lia|].
      assert (2 ^ 32 <= 2 ^ k)%Z by (apply Z.pow_le_mono_r; lia). change (2 ^ 32)%Z with 4294967296%Z in *. lia. }
    rewrite (HS (8 + 8 + 8 + 8)%Z), (HS (8 + 8 + 8 + 8 + 8)%Z), (HS (8 + 8 + 8 + 8 + 8 + 8)%Z), (HS (8 + 8 + 8 + 8 + 8 + 8 + 8)%Z) by lia. rewrite !Z.shiftr_0_l.
    reflexivity.
  - exact Hw.
Qed.

Definition spu_memset_stmt : Prop := memsetZ_stmt_g usegs 0xd0c68.
Definition spu_pm_stmt : Prop := pmu_stmt_g usegs 0x5ceb0 NUMU_GTOP.
Definition spu_pdc_stmt : Prop := pdcu_stmt_g usegs 0x5de4c NUMU_GTOP.
Definition spu_ndc_stmt : Prop := ndcu_stmt_g usegs 0x5e020 NUMU_GTOP.

Section SPUDC.
  Variable E : spuenv.
  Hypothesis OK : spu_ok E.
  Hypothesis HSET : spu_memset_stmt.
  Hypothesis HPM : spu_pm_stmt.
  Hypothesis HPDC : spu_pdc_stmt.
  Hypothesis HNDC : spu_ndc_stmt.
  Notation SPq := (q_SP E).
  Notation X := (q_SP E + -616)%Z.

  Lemma spu_08c : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm nb IP IL FPT FL,
    SPUINV E mm nb IP IL FPT FL -> frm0 xfc ->
    evt usegs (spu_post E) (SPS E 0x5cdd8 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 (q_OUT E)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK.
    intros until FL. intros INV FRM. pose proof INV as INV0. spu_open INV0. spu_env OK.
    pose proof (unsigned_lit8 nb ltac:(lia)) as HT8.
    assert (D1 : IsData xa0) by exact I. assert (D2 : IsData xa1) by exact I. assert (D3 : IsData xs3) by exact I.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5ceac%Z => u_trap pc
      | 0x5cdf4%Z => first [ eapply evt_eq; [| eapply (spu_0a8 E OK)]; [num_st_eq | exact INV | exact FRM] | fail 100 "cut" pc ]
      end).
  Qed.

  Definition SPUINVc (mm : mem) (nb IP IL FPT FL : Z) : Prop :=
    (exists j, rw_cells usegs mm (q_SP E + -704) [CB 16 j]) /\
    (exists j, rw_cells usegs mm (q_SP E + -688) [CB 24 j]) /\
    rw_cells usegs mm (q_SP E + -664) [C1 (Z_to_bv 8 nb)] /\ (0 <= nb <= 1)%Z /\
    (exists j, rw_cells usegs mm (q_SP E + -663) [CB 7 j]) /\
    rw_cells usegs mm (q_SP E + -656) [C8 (Z_to_bv 64 IP); C8 (Z_to_bv 64 IL); C8 (Z_to_bv 64 FPT); C8 (Z_to_bv 64 FL)] /\
    (exists j, rw_cells usegs mm (q_SP E + -624) [CB 8 j]) /\
    (exists j, rw_cells usegs mm (q_SP E + -118) [CB 6 j]) /\
    rw_cells usegs mm (q_SP E + -104) (spu_saved E) /\
    (exists v, rw_cells usegs mm (q_OUT E) [C8 v]) /\
    bytes_at usegs mm (q_A E) (q_txt E) /\
    mem_inv usegs mm /\ munch (spu_W E) (q_m0 E) mm /\ wmono usegs (q_m0 E) mm /\ stk usegs mm (q_lo E) (q_SP E + -704).
  Ltac spc_open H :=
    let j1 := fresh "j" in let j2 := fresh "j" in let j3 := fresh "j" in let j4 := fresh "j" in let j5 := fresh "j" in let v := fresh "v" in
    destruct H as ((j1 & PAD0) & (j2 & PNS) & NEG & ?NBR & (j3 & PNS2) & SPANS & (j4 & PERR) & (j5 & BGP) & SAVED & (v & OUTC) & TXT & MI & MU & WM & ST);
    unfold spu_saved in SAVED; unfold spu_W, SPATHU_STACK, NDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK in MU;
    let TXB := fresh "TXB" in pose proof (bytes_at_bound _ _ _ _ TXT) as TXB.

  Lemma spu_rejoin : forall mm nb IP IL FPT FL ws len dcs,
    SPUINVc mm nb IP IL FPT FL -> bigint_at usegs mm X ws len -> rw_cells usegs mm (q_SP E + -112) dcs -> cells_size dcs = 8%nat ->
    SPUINV E mm nb IP IL FPT FL.
  Proof using.
    intros until dcs. intros INV (WA & WL & XN & LEN) DG DS. spc_open INV.
    apply rw_cells_of_u64arr in WA. rewrite WL in WA. change (8 * 62)%nat with 496%nat in WA.
    lazymatch type of BGP with rw_cells _ _ _ [CB 6 ?jj] => assert (J : rw_cells usegs mm X ([CB 496 (u64s ws)] ++ [C2 (Z_to_bv 64 len)] ++ [CB 6 jj])) end.
    { apply num_rw_cells_app. split; [exact WA|]. cbn [cells_size csize Nat.add]. apply num_rw_cells_app. split.
      - replace (q_SP E + -616 + Z.of_nat 496)%Z with (q_SP E + -616 + 496)%Z by lia. exact XN.
      - cbn [cells_size csize Nat.add]. replace (q_SP E + -616 + Z.of_nat 496 + Z.of_nat 2)%Z with (q_SP E + -118)%Z by lia. exact BGP. }
    destruct (rw_cells_forget usegs mm X _ J) as [jb JB]. cbn [cells_size csize Nat.add app] in JB.
    destruct (rw_cells_forget usegs mm _ _ DG) as [jd JD]. rewrite DS in JD.
    split; [eexists; eassumption|]. split; [eexists; eassumption|]. split; [assumption|]. split; [lia|]. split; [eexists; eassumption|].
    split; [assumption|]. split; [eexists; eassumption|]. split; [exists jb; exact JB|]. split; [exists jd; exact JD|].
    split; [unfold spu_saved; assumption|]. split; [eexists; eassumption|].
    split; [assumption|]. split; [assumption|]. split; [unfold spu_W, SPATHU_STACK, NDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK; assumption|]. split; assumption.
  Qed.

  Lemma spu_010 : forall (sci p2 : Z) xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm nb IP IL FPT FL ws len dg,
    SPUINVc mm nb IP IL FPT FL -> frm0 xfc ->
    bigint_at usegs mm X ws len -> rw_cells usegs mm (q_SP E + -112) [C8 (Z_to_bv 64 dg)] ->
    (0 <= dg <= 770)%Z -> (19 * len <= 2 * dg + 76)%Z -> (dg < PMU_NORM_DG -> bignorm ws len)%Z ->
    (-342 <= sci <= 327)%Z -> (-1000000 <= p2 <= 1000000)%Z ->
    evt usegs (spu_post E) (SPS E 0x5cd5c xra xt0 xt1 xt2 xs0 (Z_to_bv 64 sci) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 p2) xs3 xs4 xs5 xs6 (Z_to_bv 64 (q_OUT E)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK HPDC HNDC.
    intros until dg. intros INV FRM BIG DG HDG HCNT HNRM HSCI HP2. pose proof INV as INV0. spc_open INV0. spu_env OK. unfold PMU_NORM_DG in HNRM.
    assert (LO0 : (0 <= q_lo E)%Z) by (destruct ST as [? _]; assumption).
    assert (D1 : IsData xs0) by exact I.
    apply spu_c8_split_lo in DG; [|lia].
    uwalk ltac:(fun pc => lazymatch pc with | 0x5ceac%Z => u_trap pc | 0x5cd6c%Z => idtac end).
    rewrite (spu_sx32_small dg) by lia.
    uwalk ltac:(fun pc => lazymatch pc with | 0x5ceac%Z => u_trap pc | 0x5de4c%Z => idtac | 0x5e020%Z => idtac end).
    -
      pose proof HNDC as HM. unfold spu_ndc_stmt, ndcu_stmt_g in HM.
      eapply evt_cut.
      { eapply evt_eq; [| eapply HM with (X := X) (p2 := (p2 + 32768)%Z) (e := (sci + 1 - dg)%Z) (lo := q_lo E) (ws := ws) (len := len)]; [num_st_eq | ..];
          rewrite ?unsigned_lit by lia; unfold NDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK, NUMU_GTOP, NDCU_RANGE;
          [ exact MI | exact ST | lia | lia | Z.div_mod_to_equations; lia | exact BIG | lia | lia | lia | lia ]. }
      cbv beta. intros ms' P. unfold bigu_post_g in P.
      destruct P as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & ws3 & len3 & -> & MUc & WMc & MIc & BIG3 & STc).
      rewrite !unsigned_lit in MUc, STc by lia. unfold NDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK in MUc.
      clear BIG ST. lazymatch type of MUc with munch _ ?mo ?mn => transport_after_call usegs mo mn MUc WMc end.
      clear MUc WMc MI HM. rename MIc into MI. rename STc into ST. num_ret_pc.
      assert (INVc : SPUINVc m3 nb IP IL FPT FL).
      { split; [eexists; eassumption|]. split; [eexists; eassumption|]. split; [assumption|]. split; [lia|]. split; [eexists; eassumption|].
        split; [assumption|]. split; [eexists; eassumption|]. split; [eexists; eassumption|]. split; [unfold spu_saved; assumption|]. split; [eexists; eassumption|].
        split; [assumption|]. split; [assumption|]. split; [unfold spu_W, SPATHU_STACK, NDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK; assumption|]. split; assumption. }
      pose proof (spu_rejoin m3 nb IP IL FPT FL ws3 len3 _ INVc BIG3 DG eq_refl) as INV3.
      eapply evt_eq; [| eapply spu_08c]; [num_st_eq | exact INV3 | exact FRM].
    -
      pose proof HPDC as HM. unfold spu_pdc_stmt, pdcu_stmt_g in HM.
      eapply evt_cut.
      { eapply evt_eq; [| eapply HM with (X := X) (e := (sci + 1 - dg)%Z) (lo := q_lo E) (ws := ws) (len := len)]; [num_st_eq | ..];
          rewrite ?unsigned_lit by lia; unfold PDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK, NUMU_GTOP;
          [ exact MI | exact ST | lia | lia | Z.div_mod_to_equations; lia | exact BIG | lia | lia | Z.div_mod_to_equations; lia | apply HNRM; lia | lia | lia ]. }
      cbv beta. intros ms' P. unfold bigu_post_g in P.
      destruct P as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & ws3 & len3 & -> & MUc & WMc & MIc & BIG3 & STc).
      rewrite !unsigned_lit in MUc, STc by lia. unfold PDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK in MUc.
      clear BIG ST. lazymatch type of MUc with munch _ ?mo ?mn => transport_after_call usegs mo mn MUc WMc end.
      clear MUc WMc MI HM. rename MIc into MI. rename STc into ST. num_ret_pc.
      assert (INVc : SPUINVc m3 nb IP IL FPT FL).
      { split; [eexists; eassumption|]. split; [eexists; eassumption|]. split; [assumption|]. split; [lia|]. split; [eexists; eassumption|].
        split; [assumption|]. split; [eexists; eassumption|]. split; [eexists; eassumption|]. split; [unfold spu_saved; assumption|]. split; [eexists; eassumption|].
        split; [assumption|]. split; [assumption|]. split; [unfold spu_W, SPATHU_STACK, NDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK; assumption|]. split; assumption. }
      pose proof (spu_rejoin m3 nb IP IL FPT FL ws3 len3 _ INVc BIG3 DG eq_refl) as INV3.
      zstep.
      eapply evt_eq; [| eapply spu_08c]; [num_st_eq | exact INV3 | exact FRM].
  Qed.

  Lemma spu_fe4 : forall (sci p2 : Z) xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm nb IP IL FPT FL,
    SPUINV E mm nb IP IL FPT FL -> frm0 xfc -> pm_spans_ok (q_A E) (q_txt E) IP IL FPT FL ->
    (-342 <= sci <= 327)%Z -> (-1000000 <= p2 <= 1000000)%Z ->
    evt usegs (spu_post E) (SPS E 0x5cd30 xra xt0 xt1 xt2 xs0 (Z_to_bv 64 sci) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 p2) xs3 xs4 xs5 xs6 (Z_to_bv 64 (q_OUT E)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until FL. intros INV FRM SPN HSCI HP2. spu_open INV. spu_env OK.
    assert (LO0 : (0 <= q_lo E)%Z) by (destruct ST as [? _]; assumption).
    assert (D1 : IsData xs0) by exact I. assert (D2 : IsData xa0) by exact I.
    uwalk ltac:(fun pc => lazymatch pc with | 0x5ceac%Z => u_trap pc | 0xd0c68%Z => idtac end).

    pose proof HSET as HS. unfold spu_memset_stmt, memsetZ_stmt_g in HS.
    eapply evt_cut.
    { eapply evt_eq; [| eapply HS with (D := X) (C := 0%Z) (N := 504%Z)]; [num_st_eq | ..]; [ exact BG | exact MI | lia | lia | lia | lia ]. }
    cbv beta. intros ms' P. unfold memsetZ_post_g in P.
    destruct P as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & -> & MUc & WMc & MIc & DSTc).
    clear BG. lazymatch type of MUc with munch _ ?mo ?mn => transport_after_call usegs mo mn MUc WMc end.
    clear MUc WMc MI HS. rename MIc into MI. num_ret_pc.
    change (Z.to_nat 504) with 504%nat in DSTc. change (0 mod 256)%Z with 0%Z in DSTc.
    apply (rw_cells_split_CB usegs m3 _ [] 504 _ [] [496;2;6]%nat) in DSTc; [|reflexivity].
    cbn [mk_CB_cells app] in DSTc.
    lazymatch type of DSTc with rw_cells _ _ _ [?c1; ?c2; ?c3] => change [c1; c2; c3] with ([c1] ++ [c2] ++ [c3]) in DSTc end.
    apply num_rw_cells_app in DSTc. destruct DSTc as [LIMBS REST]. apply num_rw_cells_app in REST. destruct REST as [LENC PADC].
    cbn [cells_size csize Nat.add Nat.mul] in LENC, PADC.
    replace (q_SP E + -616 + Z.of_nat 496)%Z with (X + 496)%Z in LENC by lia.
    replace (q_SP E + -616 + Z.of_nat 496 + Z.of_nat 2)%Z with (q_SP E + -118)%Z in PADC by lia.
    replace (firstn 2 (skipn 496 (repeat (Z_to_bv 8 0) 504))) with (le2 (Z_to_bv 64 0)) in LENC by (vm_compute; reflexivity).
    apply num_cb2_c2 in LENC.
    change 496%nat with (8 * 62)%nat in LIMBS.
    destruct (u64arr_of_rw_cells usegs m3 X 62 _ LIMBS) as (ws & WL & WA). clear LIMBS.
    destruct (rw_cells_forget usegs m3 _ _ DGC) as [jd JD]. cbn [cells_size csize Nat.add] in JD. clear DGC.
    uwalk ltac:(fun pc => lazymatch pc with | 0x5ceac%Z => u_trap pc | 0x5ceb0%Z => idtac end).

    replace (q_SP E + -656)%Z with (X - 40)%Z in SPANS by lia.
    replace (q_SP E + -112)%Z with (X + 504)%Z in JD by lia.
    pose proof HPM as HM. unfold spu_pm_stmt, pmu_stmt_g in HM.
    eapply evt_cut.
    { eapply evt_eq; [| eapply HM with (X := X) (A := q_A E) (IP := IP) (IL := IL) (FPT := FPT) (FL := FL) (lo := q_lo E) (ws := ws) (txt := q_txt E) (jd := jd)]; [num_st_eq | ..];
        rewrite ?unsigned_lit by lia; unfold PMU_STACK, NUMU_GTOP, NUM_TXT_MAX;
        [ exact MI | exact ST | lia | lia | split; [exact WA| split; [exact WL| split; [exact LENC| lia]]] | lia | lia | exact JD | exact SPANS | exact TXT | lia | lia | lia | exact SPN ]. }
    cbv beta. intros ms' P. unfold pmu_post_g in P.
    destruct P as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & ws4 & len4 & dg4 & -> & MUc & WMc & MIc & BIG4 & DG4 & SPANS4 & STc & HD4 & HC4 & HN4).
    rewrite !unsigned_lit in MUc, STc by lia. unfold PMU_STACK in MUc.
    clear WA LENC JD SPANS ST. lazymatch type of MUc with munch _ ?mo ?mn => transport_after_call usegs mo mn MUc WMc end.
    clear MUc WMc MI HM. rename MIc into MI. rename STc into ST. num_ret_pc.
    replace (X - 40)%Z with (q_SP E + -656)%Z in SPANS4 by lia.
    replace (q_SP E + -616 + 504)%Z with (q_SP E + -112)%Z in DG4 by lia.
    assert (INVc : SPUINVc m4 nb IP IL FPT FL).
    { split; [eexists; eassumption|]. split; [eexists; eassumption|]. split; [assumption|]. split; [lia|]. split; [eexists; eassumption|].
      split; [assumption|]. split; [eexists; eassumption|]. split; [eexists; eassumption|]. split; [unfold spu_saved; assumption|]. split; [eexists; eassumption|].
      split; [assumption|]. split; [assumption|]. split; [unfold spu_W, SPATHU_STACK, NDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK; assumption|]. split; assumption. }
    eapply evt_eq; [| eapply (spu_010 sci p2) with (ws := ws4) (len := len4) (dg := dg4)]; [num_st_eq | exact INVc | exact FRM | exact BIG4 | exact DG4 | lia | lia | exact HN4 | lia | lia].
  Qed.

  Lemma spu_LC : forall (s p2 v : Z) xra xt0 xt1 xt2 xs0 xa0 xa2 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm nb IP IL FPT FL,
    SPUINV E mm nb IP IL FPT FL -> frm0 xfc -> pm_spans_ok (q_A E) (q_txt E) IP IL FPT FL ->
    (-342 <= s <= 326)%Z -> (-1000000 <= p2 <= 1000000)%Z -> (0 <= v <= 99)%Z ->
    evt usegs (spu_post E) (SPS E 0x5cd14 xra xt0 xt1 xt2 xs0 (Z_to_bv 64 s) xa0 (Z_to_bv 64 v) xa2 (Z_to_bv 64 14757395258967641293) (Z_to_bv 64 99) xa5 xa6 xa7
                               (Z_to_bv 64 p2) xs3 xs4 xs5 xs6 (Z_to_bv 64 (q_OUT E)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until FL. intros INV FRM SPN HS HP2 HV. spu_env OK.
    ukstep.
    ukwalk ltac:(fun pc => lazymatch pc with
      | 0x5ceac%Z => u_trap pc
      | 0x5cd14%Z => first [ exfalso; lia | fail 100 "cut" pc ]
      | 0x5cd30%Z => first [ eapply evt_eq; [| eapply (spu_fe4 (s + 1)%Z p2)]; [num_st_eq | exact INV | exact FRM | exact SPN | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma spu_f9c : forall (s p2 v : Z) xra xt0 xt1 xt2 xs0 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm nb IP IL FPT FL,
    SPUINV E mm nb IP IL FPT FL -> frm0 xfc -> pm_spans_ok (q_A E) (q_txt E) IP IL FPT FL ->
    (-342 <= s <= 326)%Z -> (-1000000 <= p2 <= 1000000)%Z -> (0 <= v <= 99)%Z ->
    evt usegs (spu_post E) (SPS E 0x5cce8 xra xt0 xt1 xt2 xs0 (Z_to_bv 64 s) xa0 (Z_to_bv 64 v) xa2 xa3 xa4 xa5 xa6 xa7
                               (Z_to_bv 64 p2) xs3 xs4 xs5 xs6 (Z_to_bv 64 (q_OUT E)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until FL. intros INV FRM SPN HS HP2 HV. spu_env OK.
    ukwalk ltac:(fun pc => lazymatch pc with
      | 0x5cd14%Z => first [ eapply evt_eq; [| eapply (spu_LC s p2 v)]; [num_st_eq | exact INV | exact FRM | exact SPN | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x5cd30%Z => first [ eapply evt_eq; [| eapply (spu_fe4 s p2)]; [num_st_eq | exact INV | exact FRM | exact SPN | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.
  Lemma spu_fa8 : forall (s p2 v : Z) xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm nb IP IL FPT FL,
    SPUINV E mm nb IP IL FPT FL -> frm0 xfc -> pm_spans_ok (q_A E) (q_txt E) IP IL FPT FL ->
    (-342 <= s <= 326)%Z -> (-1000000 <= p2 <= 1000000)%Z -> (0 <= v <= 99)%Z ->
    evt usegs (spu_post E) (SPS E 0x5ccf4 xra xt0 xt1 xt2 xs0 (Z_to_bv 64 s) xa0 xa1 xa2 xa3 (Z_to_bv 64 v) xa5 xa6 xa7
                               (Z_to_bv 64 p2) xs3 xs4 xs5 xs6 (Z_to_bv 64 (q_OUT E)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until FL. intros INV FRM SPN HS HP2 HV. spu_env OK.
    ukwalk ltac:(fun pc => lazymatch pc with
      | 0x5cd14%Z => first [ eapply evt_eq; [| eapply (spu_LC s p2 v)]; [num_st_eq | exact INV | exact FRM | exact SPN | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x5cd30%Z => first [ eapply evt_eq; [| eapply (spu_fe4 s p2)]; [num_st_eq | exact INV | exact FRM | exact SPN | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma spu_f64 : forall (s p2 v : Z) xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm nb IP IL FPT FL,
    SPUINV E mm nb IP IL FPT FL -> frm0 xfc -> pm_spans_ok (q_A E) (q_txt E) IP IL FPT FL ->
    (-342 <= s <= 324)%Z -> (-1000000 <= p2 <= 1000000)%Z -> (0 <= v <= 9999)%Z ->
    evt usegs (spu_post E) (SPS E 0x5ccb0 xra xt0 xt1 xt2 xs0 (Z_to_bv 64 s) xa0 xa1 xa2 xa3 (Z_to_bv 64 v) xa5 xa6 xa7
                               (Z_to_bv 64 p2) xs3 xs4 xs5 xs6 (Z_to_bv 64 (q_OUT E)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until FL. intros INV FRM SPN HS HP2 HV. pose proof INV as INV0. spu_open INV0. spu_env OK.
    ukwalk ltac:(fun pc => lazymatch pc with
      | 0x5ceac%Z => u_trap pc
      | 0x5ccc4%Z => idtac
      | 0x5ccf4%Z => first [ eapply evt_eq; [| eapply (spu_fa8 s p2 v)]; [num_st_eq | exact INV | exact FRM | exact SPN | lia | lia | lia] | fail 100 "cut" pc ]
      end).
    ukstep.
    ukwalk ltac:(fun pc => lazymatch pc with
      | 0x5ceac%Z => u_trap pc
      | 0x5ccc4%Z => first [ exfalso; shr2div; Z.div_mod_to_equations; lia | fail 100 "cut" pc ]
      | 0x5cce8%Z => first [ rewrite !(magic_100_m v) by lia;
                             eapply evt_eq; [| eapply (spu_f9c (s + 2)%Z p2 (v / 100)%Z)]; [num_st_eq | exact INV | exact FRM | exact SPN | lia | lia | Z.div_mod_to_equations; lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Definition laB (n : nat) : Z := match n with O => 100000000 | 1%nat => 1000000000000 | 2%nat => 10000000000000000 | _ => 18446744073709551616 end.
  Lemma spu_LA : forall (n : nat) (s p2 v : Z) xra xt0 xt1 xt2 xs0 xa0 xa2 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm nb IP IL FPT FL,
    SPUINV E mm nb IP IL FPT FL -> frm0 xfc -> pm_spans_ok (q_A E) (q_txt E) IP IL FPT FL ->
    (-342 <= s)%Z -> (s + 4 * (Z.of_nat n + 1) <= 324)%Z -> (-1000000 <= p2 <= 1000000)%Z -> (0 <= v < laB n)%Z -> (n <= 3)%nat ->
    evt usegs (spu_post E) (SPS E 0x5cc94 xra xt0 xt1 xt2 xs0 (Z_to_bv 64 s) xa0 (Z_to_bv 64 3777893186295716171) xa2 (Z_to_bv 64 99999999) (Z_to_bv 64 v) xa5 xa6 xa7
                               (Z_to_bv 64 p2) xs3 xs4 xs5 xs6 (Z_to_bv 64 (q_OUT E)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros n. induction n as [|n IH]; intros until FL; intros INV FRM SPN HS1 HS2 HP2 HV Hn; spu_env OK.
    - cbn [laB] in HV. ukstep.
      ukwalk ltac:(fun pc => lazymatch pc with
        | 0x5ceac%Z => u_trap pc
        | 0x5cc94%Z => first [ exfalso; lia | fail 100 "cut" pc ]
        | 0x5ccb0%Z => first [ rewrite !(magic_10000_m v) by lia;
                               eapply evt_eq; [| eapply (spu_f64 (s + 4)%Z p2 (v / 10000)%Z)]; [num_st_eq | exact INV | exact FRM | exact SPN | lia | lia | Z.div_mod_to_equations; lia] | fail 100 "cut" pc ]
        end).
    - assert (HVB : (0 <= v < 18446744073709551616)%Z) by (destruct n as [|[|[|n]]]; cbn [laB] in HV; lia).
      ukstep.
      ukwalk ltac:(fun pc => lazymatch pc with
        | 0x5ceac%Z => u_trap pc
        | 0x5cc94%Z => first [ rewrite !(magic_10000_m v) by lia;
                               eapply evt_eq; [| eapply (IH (s + 4)%Z p2 (v / 10000)%Z)]; [num_st_eq | exact INV | exact FRM | exact SPN | lia | lia | lia | | lia];
                               destruct n as [|[|[|n]]]; cbn [laB] in HV |- *; [Z.div_mod_to_equations; lia .. | exfalso; lia] | fail 100 "cut" pc ]
        | 0x5ccb0%Z => first [ rewrite !(magic_10000_m v) by lia;
                               eapply evt_eq; [| eapply (spu_f64 (s + 4)%Z p2 (v / 10000)%Z)]; [num_st_eq | exact INV | exact FRM | exact SPN | lia | lia | Z.div_mod_to_equations; lia] | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma spu_f2c : forall (q p2 : Z) (wv : word) xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm nb IP IL FPT FL,
    SPUINV E mm nb IP IL FPT FL -> frm0 xfc -> pm_spans_ok (q_A E) (q_txt E) IP IL FPT FL ->
    (-342 <= q <= 308)%Z -> (-1000000 <= p2 <= 1000000)%Z ->
    evt usegs (spu_post E) (SPS E 0x5cc78 xra xt0 xt1 xt2 xs0 (Z_to_bv 64 q) xa0 xa1 xa2 xa3 wv xa5 xa6 xa7
                               (Z_to_bv 64 p2) xs3 xs4 xs5 xs6 (Z_to_bv 64 (q_OUT E)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until FL. intros INV FRM SPN HQ HP2. pose proof INV as INV0. spu_open INV0. spu_env OK.
    pose proof (bv_unsigned_in_range 64 wv) as WR. unfold bv_modulus in WR. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in WR.
    rewrite <- (Z_to_bv_bv_unsigned wv). set (wz := bv_unsigned wv) in *. clearbody wz.
    ukwalk ltac:(fun pc => lazymatch pc with
      | 0x5ceac%Z => u_trap pc
      | 0x5cc94%Z => first [ eapply evt_eq; [| eapply (spu_LA 3%nat q p2 wz)]; [num_st_eq | exact INV | exact FRM | exact SPN | lia | lia | lia | cbn [laB]; lia | lia] | fail 100 "cut" pc ]
      | 0x5ccb0%Z => first [ shr2div; eapply evt_eq; [| eapply (spu_f64 q p2 wz)]; [num_st_eq | exact INV | exact FRM | exact SPN | lia | lia | Z.div_mod_to_equations; lia] | fail 100 "cut" pc ]
      end).
  Qed.
End SPUDC.
