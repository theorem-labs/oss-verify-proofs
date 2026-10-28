(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit As0StepLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0MemIsZero_b Ba0RegionPoisoned_b Ba0AsanMemset_b Ba0AsanMemcpy_b Ba0MemcpyIcpt_b Ba0DiagChk_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

Section FPX_1. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Definition zsh (M : word -> option byte) (p n : Z) : Prop :=
  forall x : word, (SB + p / 8) - (SB + p / 8) mod 8 <= bv_unsigned x < (SB + (p + n - 1) / 8) - (SB + (p + n - 1) / 8) mod 8 + 8 -> M x = Some (Z_to_bv 8 0).
(* [comment removed for export] *)
Lemma zsh_of_hull : forall M p n, (forall x : word, SB + p / 8 - 7 <= bv_unsigned x < SB + (p + n - 1) / 8 + 8 -> M x = Some (Z_to_bv 8 0)) -> zsh M p n.
Proof.
  intros M p n H x Hx. apply H. pose proof (Z.mod_pos_bound (SB + p / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + (p + n - 1) / 8) 8 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma zsh_of_hullm : forall M p n m, 0 <= p -> n - 1 <= m -> p + m < 2 ^ 47 ->
  (forall x : word, SB + p / 8 - 7 <= bv_unsigned x < Z.min (SB + (p + m) / 8 + 8) (SB + 2 ^ 44) -> M x = Some (Z_to_bv 8 0)) -> zsh M p n.
Proof.
  intros M p n m Hp Hnm Hpm H x Hx. apply H.
  assert (Q1 : (p + n - 1) / 8 <= (p + m) / 8) by (apply Z.div_le_mono; lia).
  assert (Q2 : (p + m) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
  pose proof (Z.mod_pos_bound (SB + p / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + (p + n - 1) / 8) 8 ltac:(lia)).
  pose proof (Z.div_mod (SB + (p + n - 1) / 8) 8 ltac:(lia)). unfold SB in *. lia.
Qed.

Lemma zsh_words : forall M p n, zsh M p n -> 0 < n -> 0 <= p -> p + n + 8 <= HIGHEND ->
  let fS := SB + p / 8 in let lS := SB + (p + n - 1) / 8 in
  exists w0 w1, rdn ASEGS M (Z_to_bv 64 (fS - fS mod 8)) 8%nat = Some w0 /\ rdn ASEGS M (Z_to_bv 64 (lS - lS mod 8)) 8%nat = Some w1.
Proof.
  intros M p n HZ Hn Hp Hpn fS lS. unfold HIGHEND in *.
  assert (Pq : 0 <= p / 8 <= (p + n - 1) / 8 /\ (p + n - 1) / 8 <= 2 ^ 44).
  { split; [split; [apply Z.div_pos; lia | apply Z.div_le_mono; lia] | apply Z.div_le_upper_bound; lia]. }
  assert (FL : fS <= lS) by (subst fS lS; lia).
  pose proof (Z.mod_pos_bound fS 8 ltac:(lia)) as B0. pose proof (Z.mod_pos_bound lS 8 ltac:(lia)) as B1.
  pose proof (Z.div_mod fS 8 ltac:(lia)) as E0. pose proof (Z.div_mod lS 8 ltac:(lia)) as E1.
  pose proof (Z.div_le_mono fS lS 8 ltac:(lia) FL) as MONO.
  assert (R0 : 0 <= fS - fS mod 8 /\ lS - lS mod 8 + 8 < 2 ^ 63) by (subst fS lS; unfold SB in *; lia).
  unfold zsh in HZ. fold fS lS in HZ.
  exists (repeat (Z_to_bv 8 0) 8), (repeat (Z_to_bv 8 0) 8).
  split; apply rdn_zeros; try (rewrite u_Z2bv by lia; cbn; lia);
    intros i Hi; rewrite u_Z2bv by lia; apply HZ; rewrite u_Z2bv by (cbn in Hi; lia); cbn in Hi; lia.
Qed.

Theorem diag_memcpy : forall (M : word -> option byte) (s pd ps n : Z) (bs : list byte) (ret : word) regs,
  0 <= n <= 2 ^ 40 -> in_app8 ps n -> in_app8 pd n ->
  0x1000000 <= s - 2232 -> s < 2 ^ 64 ->
  SB + (ps + n - 1) / 8 + 8 <= s - 2232 -> SB + (pd + n - 1) / 8 + 8 <= s - 2232 ->
  (0 < n -> ps + n <= s - 2232 \/ s <= ps) -> (0 < n -> pd + n <= s - 2232 \/ s <= pd) -> (pd + n <= ps \/ ps + n <= pd) ->
  store_ok ASEGS M (Z_to_bv 64 (s - 2232)) 2232%nat = true ->
  store_ok ASEGS M (Z_to_bv 64 pd) (Z.to_nat n) = true ->
  rdn ASEGS M (Z_to_bv 64 ps) (Z.to_nat n) = Some bs ->
  ret_ok ret -> rt_layout_globs M -> mc_icpt_globs M -> zsh M ps n -> zsh M pd n ->
  getr regs 1 = ret -> getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 pd -> getr regs 11 = Z_to_bv 64 ps -> getr regs 12 = Z_to_bv 64 n ->
  exists regs' Mj,
    msteps ASEGS (mkst regs (0x77c90%bv : word) M (seg_rom ASEGS)) (mkst regs' ret (wbytes Mj (Z_to_bv 64 pd) bs) (seg_rom ASEGS))
    /\ getr regs' 10 = Z_to_bv 64 pd /\ keeps_cs regs regs'
    /\ (forall x : word, bv_unsigned x < s - 2232 \/ s <= bv_unsigned x -> Mj x = M x) /\ mem_grows M Mj.
Proof.
  intros M s pd ps n bs ret regs Hn HappS HappD Hs1 Hs2 HshS HshD HdjS HdjD Hover Hok Hdst Hsrc Hret HG HI HZS HZD H1 H2 H10 H11 H12.
  assert (Hpd : 0 <= pd /\ pd + n + 8 <= HIGHEND) by (unfold in_app8, LOWEND, HIGHBEG, HIGHEND in *; lia).
  assert (Hps : 0 <= ps /\ ps + n + 8 <= HIGHEND) by (unfold in_app8, LOWEND, HIGHBEG, HIGHEND in *; lia).
  set (fD := SB + pd / 8) in *. set (lD := SB + (pd + n - 1) / 8) in *.
  set (fS := SB + ps / 8) in *. set (lS := SB + (ps + n - 1) / 8) in *.
  destruct (@wrap_memcpy_run fx M (seg_rom ASEGS) (Z_to_bv 64 s) ret pd ps n s bs 0 fS lS (fS - fS mod 8) (lS - lS mod 8) 0 fD lD (fD - fD mod 8) (lD - lD mod 8))
    with (regs := regs) as (regs' & Mj & RUN & Q10 & Q2 & Q1 & KCS & OUT & GR).
  - apply u_Z2bv; lia.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - lia.
  - exact HappS.
  - exact HappD.
  - lia.
  - subst lS. lia.
  - subst lD. lia.
  - exact HdjS.
  - exact HdjD.
  - exact Hover.
  - exact Hok.
  - exact Hdst.
  - exact Hsrc.
  - exact Hret.
  - exact HG.
  - exact HI.
  - intros Hn0 x Hx. apply HZS. fold fS lS. pose proof (Z.mod_pos_bound fS 8 ltac:(lia)). pose proof (Z.mod_pos_bound lS 8 ltac:(lia)). lia.
  - intros Hn0. apply HZS. fold fS lS. assert (0 <= (ps + n - 1) / 8 <= 2 ^ 44) by (unfold HIGHEND in *; split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (ps / 8 <= (ps + n - 1) / 8) by (apply Z.div_le_mono; lia). assert (0 <= ps / 8) by (apply Z.div_pos; lia).
    pose proof (Z.mod_pos_bound fS 8 ltac:(lia)). pose proof (Z.mod_pos_bound lS 8 ltac:(lia)). rewrite u_Z2bv by (subst lS; unfold SB; lia). subst fS lS. unfold SB in *. lia.
  - left. reflexivity.
  - intros [Hn0 _]. exact (zsh_words M ps n HZS Hn0 (proj1 Hps) (proj2 Hps)).
  - intros Hn0 x Hx. apply HZD. fold fD lD. pose proof (Z.mod_pos_bound fD 8 ltac:(lia)). pose proof (Z.mod_pos_bound lD 8 ltac:(lia)). lia.
  - intros Hn0. apply HZD. fold fD lD. assert (0 <= (pd + n - 1) / 8 <= 2 ^ 44) by (unfold HIGHEND in *; split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (pd / 8 <= (pd + n - 1) / 8) by (apply Z.div_le_mono; lia). assert (0 <= pd / 8) by (apply Z.div_pos; lia).
    pose proof (Z.mod_pos_bound fD 8 ltac:(lia)). pose proof (Z.mod_pos_bound lD 8 ltac:(lia)). rewrite u_Z2bv by (subst lD; unfold SB; lia). subst fD lD. unfold SB in *. lia.
  - left. reflexivity.
  - intros [Hn0 _]. exact (zsh_words M pd n HZD Hn0 (proj1 Hpd) (proj2 Hpd)).
  - exact H10.
  - exact H11.
  - exact H12.
  - exact H2.
  - exact H1.
  - exists regs', Mj. split; [exact RUN|]. split; [exact Q10|]. split; [exact KCS|]. split; [|exact GR].
    intros x Hx. apply OUT. exact Hx.
Qed.
End FPX_1.
