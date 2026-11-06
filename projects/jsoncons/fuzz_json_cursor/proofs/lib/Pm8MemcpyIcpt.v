(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit As0StepLib Pm8MemIsZero Pm8RegionPoisoned Pm8AsanMemset Pm8AsanMemcpy.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8MemcpyBase Pm8Memcpy.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8_code_7e000_7f000 Pm8_code_80000_81000 .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Section FPX_1. Context {fx : PropExec.FPState}.

#[local] Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.
#[local] Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.
#[local] Ltac cond :=
  rwH; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
  first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
#[local] Ltac wval :=
  gres; rwH; unfold at_, v_addi, v_add, v_sub, v_srli; imm_norm; unorm; rewrite ?Z.shiftr_div_pow2 by lia;
  try change (2 ^ 3)%Z with 8%Z; first [reflexivity | f_equal; lia].
#[local] Ltac xval := gres; rwH; unfold v_xori; imm_norm; unorm; rewrite lxor_ones64 by lia; first [reflexivity | f_equal; lia].
#[local] Ltac vlit := gres; rwH; apply bv_eq; vm_compute; reflexivity.

#[local] Definition RIPL : list reg := [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24]%bv.

Section AMCI.
  Variable mem0 : word -> option byte.
  Variable rom : word -> option byte.
  Variables sp ra : word.
  Variables pd ps n s : Z.
  Variable bs : list byte.
  Variables kS fS lS faS laS : Z.
  Variables kD fD lD faD laD : Z.
  Hypothesis Hs_def : bv_unsigned sp = s.
  Hypothesis HfS_def : fS = (SB + ps / 8)%Z.           Hypothesis HlS_def : lS = (SB + (ps + n - 1) / 8)%Z.
  Hypothesis HfaS_def : faS = (fS - fS mod 8)%Z.       Hypothesis HlaS_def : laS = (lS - lS mod 8)%Z.
  Hypothesis HfD_def : fD = (SB + pd / 8)%Z.           Hypothesis HlD_def : lD = (SB + (pd + n - 1) / 8)%Z.
  Hypothesis HfaD_def : faD = (fD - fD mod 8)%Z.       Hypothesis HlaD_def : laD = (lD - lD mod 8)%Z.
  Hypothesis Hn : (0 <= n <= 2 ^ 40)%Z.
  Hypothesis HappS : in_app8 ps n.
  Hypothesis HappD : in_app8 pd n.
  Hypothesis Hs : (0x1000000 <= s - 2232)%Z /\ (s < 2 ^ 64)%Z.
  Hypothesis HshS : (lS + 8 <= s - 2232)%Z.
  Hypothesis HshD : (lD + 8 <= s - 2232)%Z.
  Hypothesis HdjS : (0 < n -> ps + n <= s - 2232 \/ s <= ps)%Z.
  Hypothesis HdjD : (0 < n -> pd + n <= s - 2232 \/ s <= pd)%Z.
  Hypothesis Hover : (pd + n <= ps \/ ps + n <= pd)%Z.
  Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (s - 2232)) 2232%nat = true.
  Hypothesis Hdst : store_ok ASEGS mem0 (Z_to_bv 64 pd) (Z.to_nat n) = true.
  Hypothesis Hsrc : rdn ASEGS mem0 (Z_to_bv 64 ps) (Z.to_nat n) = Some bs.
  Hypothesis Hret : ret_ok ra.
  Hypothesis HG : rt_layout_globs mem0.
  Hypothesis HI : mc_icpt_globs mem0.
  Hypothesis HZS : (0 < n)%Z -> forall x : word, (fS <= bv_unsigned x < lS)%Z -> mem0 x = Some (Z_to_bv 8 0).
  Hypothesis HLS : (0 < n)%Z -> mem0 (Z_to_bv 64 lS) = Some (Z_to_bv 8 kS).
  Hypothesis HkS : kS = 0%Z \/ ((ps + n - 1) mod 8 < kS <= 7)%Z.
  Hypothesis HWS : (0 < n <= 64)%Z -> exists w0 w1, rdn ASEGS mem0 (Z_to_bv 64 faS) 8%nat = Some w0 /\ rdn ASEGS mem0 (Z_to_bv 64 laS) 8%nat = Some w1.
  Hypothesis HZD : (0 < n)%Z -> forall x : word, (fD <= bv_unsigned x < lD)%Z -> mem0 x = Some (Z_to_bv 8 0).
  Hypothesis HLD : (0 < n)%Z -> mem0 (Z_to_bv 64 lD) = Some (Z_to_bv 8 kD).
  Hypothesis HkD : kD = 0%Z \/ ((pd + n - 1) mod 8 < kD <= 7)%Z.
  Hypothesis HWD : (0 < n <= 64)%Z -> exists w0 w1, rdn ASEGS mem0 (Z_to_bv 64 faD) 8%nat = Some w0 /\ rdn ASEGS mem0 (Z_to_bv 64 laD) 8%nat = Some w1.

  #[local] Ltac post := repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try (rewrite (zbv_wrap_up (n - 65)); f_equal; lia); try solve_keeps_but.

  #[local] Ltac hide_dj := try hide HdjS; try hide HdjD; try hide Hover; try hide HkS; try hide HkD; try hide HappS; try hide HappD.

  Lemma sp_s : sp = Z_to_bv 64 s.  Proof. hide_dj. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.
  Lemma pS_facts : (0 <= ps)%Z /\ (ps + n + 8 <= HIGHEND)%Z /\ (0 <= ps / 8 <= HIGHEND)%Z /\ (0 < n -> ps / 8 <= (ps + n - 1) / 8 <= HIGHEND)%Z.
  Proof.
    hide_dj.
    unhide HappS.
    unfold in_app8, LOWEND, HIGHBEG, HIGHEND in *. destruct HappS as [[H1 H2]|[H1 H2]];
    (repeat split; [lia | lia | apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia | intros; apply Z.div_le_mono; lia | intros; apply Z.div_le_upper_bound; lia]).
  Qed.
  Lemma pD_facts : (0 <= pd)%Z /\ (pd + n + 8 <= HIGHEND)%Z /\ (0 <= pd / 8 <= HIGHEND)%Z /\ (0 < n -> pd / 8 <= (pd + n - 1) / 8 <= HIGHEND)%Z.
  Proof.
    hide_dj.
    unhide HappD.
    unfold in_app8, LOWEND, HIGHBEG, HIGHEND in *. destruct HappD as [[H1 H2]|[H1 H2]];
    (repeat split; [lia | lia | apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia | intros; apply Z.div_le_mono; lia | intros; apply Z.div_le_upper_bound; lia]).
  Qed.
  Lemma flS_facts : (0 < n)%Z -> (SB <= fS <= lS)%Z /\ (lS + 8 <= s - 2232)%Z /\ (fS - 7 <= faS <= fS)%Z /\ (lS - 7 <= laS <= lS)%Z.
  Proof.
    hide_dj.
    intros Hn0. pose proof pS_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq Hn0). unfold SB, HIGHEND in *.
    pose proof (Z.mod_pos_bound fS 8 ltac:(lia)). pose proof (Z.mod_pos_bound lS 8 ltac:(lia)). repeat split; lia.
  Qed.
  Lemma flD_facts : (0 < n)%Z -> (SB <= fD <= lD)%Z /\ (lD + 8 <= s - 2232)%Z /\ (fD - 7 <= faD <= fD)%Z /\ (lD - 7 <= laD <= lD)%Z.
  Proof.
    hide_dj.
    intros Hn0. pose proof pD_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq Hn0). unfold SB, HIGHEND in *.
    pose proof (Z.mod_pos_bound fD 8 ltac:(lia)). pose proof (Z.mod_pos_bound lD 8 ltac:(lia)). repeat split; lia.
  Qed.

  Definition out_agree (M : word -> option byte) : Prop :=
    forall x : word, (bv_unsigned x < s - 2232 \/ s <= bv_unsigned x)%Z -> M x = mem0 x.
  Lemma out_agree_refl : out_agree mem0.  Proof. hide_dj. intros x _. reflexivity. Qed.
  Lemma out_agree_w : forall M k v, out_agree M -> (8 <= k <= 2232)%Z -> out_agree (wbytes M (Z_to_bv 64 (s - k)) (word_to_le_bytes 8 v)).
  Proof.
    hide_dj.
    intros M k v HF Hk x Hx. pose proof (u64_range x).
    destruct Hx as [Hx|Hx].
    - rewrite wbytes_below; [apply HF; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia].
    - rewrite wbytes_above; [apply HF; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia].
  Qed.
  Lemma out_agree_rdn : forall M (a : word) k, out_agree M -> (bv_unsigned a + Z.of_nat k <= s - 2232)%Z ->
    rdn ASEGS M a k = rdn ASEGS mem0 a k.
  Proof. hide_dj. intros M a k HF Ha. apply rdn_ext; [lia|]. intros x Hx. apply HF. lia. Qed.
  Lemma out_agree_globs : forall M, out_agree M -> rt_layout_globs M /\ mc_icpt_globs M.
  Proof.
    hide_dj.
    intros M HF. destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). destruct HI as (I1 & I2 & I3).
    unfold rt_layout_globs, mc_icpt_globs. rewrite !(out_agree_rdn M) by (first [exact HF | cbn [Z.of_nat Pos.to_nat]; imm_norm; lia]).
    repeat split; assumption.
  Qed.
  Lemma out_agree_store_ok : forall M k (j : nat), mem_grows mem0 M -> (Z.of_nat j <= k <= 2232)%Z ->
    store_ok ASEGS M (Z_to_bv 64 (s - k)) j = true.
  Proof.
    hide_dj.
    intros M k j HGr Hk. apply (store_ok_mono _ _ mem0 M _ HGr).
    apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 2232)) _ 2232%nat); [unorm; cbn [Z.of_nat Pos.to_nat]; lia | exact Hok | unorm; lia | unorm; cbn [Z.of_nat Pos.to_nat]; lia].
  Qed.

  Lemma out_agree_src : forall M, out_agree M -> rdn ASEGS M (Z_to_bv 64 ps) (Z.to_nat n) = Some bs.
  Proof.
    hide_dj.
    intros M HF. pose proof pS_facts as (Pp & Ppn & _). unhide HdjS. unfold HIGHEND in *.
    rewrite (rdn_ext ASEGS (Z.to_nat n) M mem0); [exact Hsrc | unorm; rewrite Z2Nat.id by lia; lia|].
    intros x Hx. rewrite u_Z2bv in Hx by lia. rewrite Z2Nat.id in Hx by lia. apply HF. lia.
  Qed.

  #[local] Ltac grows := first [apply mem_grows_refl | eapply mem_grows_trans; [ | apply wbytes_grows ]; grows].
  #[local] Ltac fsok := apply out_agree_store_ok; [grows | cbn [Z.of_nat Pos.to_nat]; lia].
  #[local] Ltac oagree := repeat (apply out_agree_w; [|lia]); apply out_agree_refl.

  Definition M10 (rg : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem0
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr rg 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr rg 9)))
      (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr rg 18)))
      (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr rg 19)))
      (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr rg 20)))
      (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr rg 21)))
      (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (getr rg 22)))
      (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (getr rg 23)))
      (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (getr rg 24)).
  Lemma M10_out_agree : forall rg, out_agree (M10 rg).  Proof. hide_dj. intros rg. unfold M10. oagree. Qed.
  Lemma M10_grows : forall rg, mem_grows mem0 (M10 rg).  Proof. hide_dj. intros rg. unfold M10. grows. Qed.

  Definition slots_ok (regs0 : bvmap 5 word) (M : word -> option byte) : Prop :=
    rdn ASEGS M (Z_to_bv 64 (s - 8)) 8%nat = Some (word_to_le_bytes 8 ra) /\
    rdn ASEGS M (Z_to_bv 64 (s - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 8)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 9)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 18)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 19)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 48)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 20)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 56)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 21)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 64)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 22)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 72)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 23)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 80)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 24)).
  Definition FR (regs0 : bvmap 5 word) (M : word -> option byte) : Prop := out_agree M /\ mem_grows mem0 M /\ slots_ok regs0 M.

  #[local] Ltac peel :=
    rewrite rdn_wbytes_out;
      [ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | cbn [Z.of_nat Pos.to_nat]; unorm; lia
        | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia ].
  #[local] Ltac slot := repeat peel; apply rdn_wbytes_hit8; unorm; lia.
  Lemma M10_FR : forall regs0, FR regs0 (M10 regs0).
  Proof. hide_dj. intros regs0. split; [apply M10_out_agree | split; [apply M10_grows|]]. unfold M10. repeat split; slot. Qed.

  Lemma rdn_slot_ext : forall (M1 M2 : word -> option byte) k,
    (forall x : word, (s - 2160 <= bv_unsigned x < s)%Z -> M1 x = M2 x) -> (8 <= k <= 2160)%Z ->
    rdn ASEGS M1 (Z_to_bv 64 (s - k)) 8%nat = rdn ASEGS M2 (Z_to_bv 64 (s - k)) 8%nat.
  Proof.
    hide_dj.
    intros M1 M2 k HE Hk. apply rdn_ext; [unorm; cbn [Z.of_nat Pos.to_nat]; lia|].
    intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. apply HE. lia.
  Qed.
  Lemma slots_ok_ext : forall regs0 (M1 M2 : word -> option byte),
    (forall x : word, (s - 2160 <= bv_unsigned x < s)%Z -> M2 x = M1 x) -> slots_ok regs0 M1 -> slots_ok regs0 M2.
  Proof.
    hide_dj.
    intros regs0 M1 M2 HE (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10). unfold slots_ok.
    rewrite !(rdn_slot_ext M2 M1) by (first [exact HE | lia]). repeat split; assumption.
  Qed.
  Lemma FR_region : forall regs0 M M', FR regs0 M -> frame_only M (s - 2160) M' -> mem_grows M M' -> FR regs0 M'.
  Proof.
    hide_dj.
    intros regs0 M M' (O & G & R) HF HGr. split; [|split].
    - intros x Hx. rewrite (HF x) by lia. apply O. exact Hx.
    - eapply mem_grows_trans; [exact G | exact HGr].
    - apply (slots_ok_ext regs0 M M'); [|exact R]. intros x Hx. apply HF. lia.
  Qed.

  Lemma rdnWS : forall M, out_agree M -> (0 < n <= 64)%Z -> exists w0 w1,
    rdn ASEGS M (Z_to_bv 64 faS) 8%nat = Some w0 /\ rdn ASEGS M (Z_to_bv 64 laS) 8%nat = Some w1
    /\ (0 <= bytes_le_to_Z w0 < 2 ^ 64)%Z /\ (0 <= bytes_le_to_Z w1 < 2 ^ 64)%Z.
  Proof.
    hide_dj.
    intros M HO Hn64. pose proof (flS_facts ltac:(lia)) as (F1 & F2 & F3 & F4). unfold SB in *.
    destruct (HWS Hn64) as (w0 & w1 & R0 & R1). exists w0, w1.
    rewrite !(out_agree_rdn M) by (first [exact HO | unorm; cbn [Z.of_nat Pos.to_nat]; lia]).
    split; [exact R0 | split; [exact R1 | split; [exact (bytes8_range _ _ _ _ R0) | exact (bytes8_range _ _ _ _ R1)]]].
  Qed.
  Lemma rdnWD : forall M, out_agree M -> (0 < n <= 64)%Z -> exists w0 w1,
    rdn ASEGS M (Z_to_bv 64 faD) 8%nat = Some w0 /\ rdn ASEGS M (Z_to_bv 64 laD) 8%nat = Some w1
    /\ (0 <= bytes_le_to_Z w0 < 2 ^ 64)%Z /\ (0 <= bytes_le_to_Z w1 < 2 ^ 64)%Z.
  Proof.
    hide_dj.
    intros M HO Hn64. pose proof (flD_facts ltac:(lia)) as (F1 & F2 & F3 & F4). unfold SB in *.
    destruct (HWD Hn64) as (w0 & w1 & R0 & R1). exists w0, w1.
    rewrite !(out_agree_rdn M) by (first [exact HO | unorm; cbn [Z.of_nat Pos.to_nat]; lia]).
    split; [exact R0 | split; [exact R1 | split; [exact (bytes8_range _ _ _ _ R0) | exact (bytes8_range _ _ _ _ R1)]]].
  Qed.
  Lemma rdn1S : forall M z, out_agree M -> (0 < n)%Z -> (fS <= z < lS)%Z -> rdn ASEGS M (Z_to_bv 64 z) 1%nat = Some [Z_to_bv 8 0].
  Proof.
    hide_dj.
    intros M z HO Hn0 Hz. pose proof (flS_facts ltac:(lia)) as (F1 & F2 & _). unfold SB in *.
    cbn [rdn]. rewrite HO by (unorm; lia). rewrite (HZS Hn0) by (unorm; lia). reflexivity.
  Qed.
  Lemma rdn1D : forall M z, out_agree M -> (0 < n)%Z -> (fD <= z < lD)%Z -> rdn ASEGS M (Z_to_bv 64 z) 1%nat = Some [Z_to_bv 8 0].
  Proof.
    hide_dj.
    intros M z HO Hn0 Hz. pose proof (flD_facts ltac:(lia)) as (F1 & F2 & _). unfold SB in *.
    cbn [rdn]. rewrite HO by (unorm; lia). rewrite (HZD Hn0) by (unorm; lia). reflexivity.
  Qed.
  Lemma rdnLS : forall M z, out_agree M -> (0 < n)%Z -> z = lS -> rdn ASEGS M (Z_to_bv 64 z) 1%nat = Some [Z_to_bv 8 kS].
  Proof.
    hide_dj.
    intros M z HO Hn0 ->. pose proof (flS_facts ltac:(lia)) as (F1 & F2 & _). unfold SB in *.
    cbn [rdn]. rewrite HO by (unorm; lia). rewrite (HLS Hn0). reflexivity.
  Qed.
  Lemma rdnLD : forall M z, out_agree M -> (0 < n)%Z -> z = lD -> rdn ASEGS M (Z_to_bv 64 z) 1%nat = Some [Z_to_bv 8 kD].
  Proof.
    hide_dj.
    intros M z HO Hn0 ->. pose proof (flD_facts ltac:(lia)) as (F1 & F2 & _). unfold SB in *.
    cbn [rdn]. rewrite HO by (unorm; lia). rewrite (HLD Hn0). reflexivity.
  Qed.
  #[local] Ltac maddr z := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 z) by (symmetry; wval) end.
  #[local] Ltac mlbu0 F D z RD :=
    chain_step; [reflexivity
      | eapply step_lbu; [exact F | reflexivity | exact D | maddr z; apply RD; [assumption | lia | lia]]
      | step_simpl; vnorm].
  #[local] Ltac mlbk F D z RD k :=
    chain_step; [reflexivity
      | eapply step_lb; [exact F | reflexivity | exact D | maddr z; apply RD; [assumption | lia | lia]]
      | step_simpl; vnorm; rewrite (v_lb_k k ltac:(lia))].
  #[local] Ltac mldw F D z R w :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := w) (v := Z_to_bv 64 (bytes_le_to_Z w)); [exact F | reflexivity | exact D | maddr z; exact R | unorm; reflexivity]
      | step_simpl; vnorm].

  Definition c1_post (rg : bvmap 5 word) : Prop :=
    getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 s
    /\ getr rg 19 = Z_to_bv 64 (ps + n) /\ getr rg 20 = Z_to_bv 64 (pd + n) /\ getr rg 2 = Z_to_bv 64 (s - 2160).

  Lemma c1_run : forall regs,
    getr regs 10 = Z_to_bv 64 pd -> getr regs 11 = Z_to_bv 64 ps -> getr regs 12 = Z_to_bv 64 n -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs',
      msteps ASEGS (mkst regs (0x80070 : word) mem0 rom) (mkst regs' (0x800d0 : word) (M10 regs) rom)
      /\ c1_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros regs H10 H11 H12 H2 H1. rewrite sp_s in H2.
    pose proof pS_facts as (PSp & PSn & _). pose proof pD_facts as (PDp & PDn & _). unfold HIGHEND in *.
    pose proof (out_agree_globs (M10 regs) (M10_out_agree regs)) as (_ & (I1 & I2 & I3)).
    unfold M10 in *.
    eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x800c4 : word) (M10 regs) rom) (fun rg => c1_post rg /\ keeps_but RIPL regs rg)).
    { unfold M10. eexists. split.
      - stepiv F_80020 D_80020 (Z_to_bv 64 (s - 2032)) ltac:(wval).
        stepsd F_80024 D_80024 (Z_to_bv 64 (s - 8)) ra ltac:(fsok).
        stepsd F_80028 D_80028 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(fsok).
        stepsd F_8002c D_8002c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(fsok).
        stepsd F_80030 D_80030 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(fsok).
        stepsd F_80034 D_80034 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(fsok).
        stepsd F_80038 D_80038 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(fsok).
        stepsd F_8003c D_8003c (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(fsok).
        stepsd F_80040 D_80040 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(fsok).
        stepsd F_80044 D_80044 (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(fsok).
        stepsd F_80048 D_80048 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(fsok).
        stepiv F_8004c D_8004c (Z_to_bv 64 s) ltac:(wval).
        stepiv F_80050 D_80050 (Z_to_bv 64 (s - 2160)) ltac:(wval).
        stepn F_80054 D_80054.
        mld F_80058 D_80058 (0x153ca0 : word) I1.
        mlbu F_8005c D_8005c (0x15d699 : word) I2.
        stepb_ft F_80060 D_80060 ltac:(cond).
        stepiv F_80064 D_80064 (Z_to_bv 64 (s - 2048)) ltac:(wval).
        stepiv F_80068 D_80068 (Z_to_bv 64 (s - 2152)) ltac:(wval).
        stepiv F_8006c D_8006c (Z_to_bv 64 (ps + n)) ltac:(wval).
        stepiv F_80070 D_80070 (Z_to_bv 64 (pd + n)) ltac:(wval).
        apply mst_refl.
      - unfold c1_post. post. }
    cbv beta. intros r1 ((Q10 & Q11 & Q12 & Q8 & Q19 & Q20 & Q2) & K1).
    destruct (Z.eq_dec pd ps) as [Heq|Hne].
    - eexists. split.
      + stepb_tk F_80074 D_80074 ltac:(cond).
        apply mst_refl.
      + split; [unfold c1_post; repeat split; assumption | exact K1].
    - unhide Hover. destruct Hover as [Hov|Hov].
      + eexists. split.
        * stepb_ft F_80074 D_80074 ltac:(cond).
          stepb_tk F_80078 D_80078 ltac:(cond).
          apply mst_refl.
        * split; [unfold c1_post; repeat split; assumption | exact K1].
      + eexists. split.
        * stepb_ft F_80074 D_80074 ltac:(cond).
          stepb_ft F_80078 D_80078 ltac:(cond).
          stepb_ft F_8007c D_8007c ltac:(cond).
          apply mst_refl.
        * split; [unfold c1_post; repeat split; assumption | exact K1].
  Qed.

  Definition cR_pre (rg : bvmap 5 word) : Prop :=
    getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 s
    /\ getr rg 19 = Z_to_bv 64 (ps + n) /\ getr rg 20 = Z_to_bv 64 (pd + n) /\ getr rg 2 = Z_to_bv 64 (s - 2160).
  Definition cR_post (rg : bvmap 5 word) : Prop :=
    getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 s
    /\ getr rg 22 = Z_to_bv 64 (n - 65) /\ getr rg 20 = Z_to_bv 64 (pd + n) /\ getr rg 2 = Z_to_bv 64 (s - 2160).

  Lemma cRz_run : forall M regs,
    cR_pre regs -> n = 0%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x800d0 : word) M rom) (mkst regs' (0x8011c : word) M rom)
      /\ cR_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros M regs (H10 & H11 & H12 & H8 & H19 & H20 & H2) Hn0. pose proof pS_facts as (Pp & Ppn & Pp8 & Pq). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq). unfold HIGHEND in *.
    eexists. split.
    - stepiv F_80080 D_80080 (Z_to_bv 64 (2 ^ 64 - 1 - ps)) ltac:(xval).
      stepb_ft F_80084 D_80084 ltac:(cond).
      stepiv F_80088 D_80088 (Z_to_bv 64 (2 ^ 64 + n - 65)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; rewrite (zbv_wrap_up (n + - 65)); f_equal; lia).
      stepn F_8008c D_8008c.
      stepb_tk F_80090 D_80090 ltac:(cond).
      stepb_ft F_8037c D_8037c ltac:(cond).
      stepn F_80380 D_80380.
      apply mst_refl.
    - unfold cR_post. post.
  Qed.

  Lemma ret_ok_5f4f0 : ret_ok (0x80420 : word).  Proof. hide_dj. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
  Lemma cRr_run : forall regs0 M regs,
    cR_pre regs -> FR regs0 M -> (64 < n)%Z ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x800d0 : word) M rom) (mkst regs' (0x8011c : word) M' rom)
      /\ cR_post regs' /\ keeps_but RIPL regs regs' /\ FR regs0 M'.
  Proof.
    hide_dj.
    intros regs0 M regs (H10 & H11 & H12 & H8 & H19 & H20 & H2) HFR Hn64. pose proof HFR as (HO & HGr & HR).
    pose proof pS_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq). unfold HIGHEND in *.
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x800d0 : word) M rom) (mkst r1 (0x826a0 : word) M rom)
              /\ (getr r1 10 = Z_to_bv 64 ps /\ getr r1 11 = Z_to_bv 64 n /\ getr r1 2 = Z_to_bv 64 (s - 2160) /\ getr r1 1 = (0x80420 : word)
                  /\ getr r1 23 = Z_to_bv 64 pd /\ getr r1 24 = Z_to_bv 64 ps /\ getr r1 9 = Z_to_bv 64 n /\ getr r1 8 = Z_to_bv 64 s /\ getr r1 22 = Z_to_bv 64 (n - 65) /\ getr r1 20 = Z_to_bv 64 (pd + n) /\ keeps_but RIPL regs r1)).
    { eexists. split.
      - stepiv F_80080 D_80080 (Z_to_bv 64 (2 ^ 64 - 1 - ps)) ltac:(xval).
        stepb_ft F_80084 D_80084 ltac:(cond).
        stepiv F_80088 D_80088 (Z_to_bv 64 (n - 65)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; f_equal; lia).
        stepn F_8008c D_8008c.
        stepb_tk F_80090 D_80090 ltac:(cond).
        stepb_tk F_8037c D_8037c ltac:(cond).
        stepiv F_803b8 D_803b8 (Z_to_bv 64 pd) ltac:(wval).
        stepiv F_803bc D_803bc (Z_to_bv 64 ps) ltac:(wval).
        stepiv F_803c0 D_803c0 (Z_to_bv 64 ps) ltac:(wval).
        stepiv F_803c4 D_803c4 (Z_to_bv 64 n) ltac:(wval).
        stepiv F_803c8 D_803c8 (Z_to_bv 64 n) ltac:(wval).
        stepn F_803cc D_803cc.
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q2 & Q1 & Q23 & Q24 & Q9 & Q8 & Q22 & Q20 & K1).
    pose proof (out_agree_globs M HO) as (HGM & _).
    pose proof (region_is_poisoned_run M rom (Z_to_bv 64 (s - 2160)) (0x80420 : word) ps n (s - 2160)
                  ltac:(unorm; reflexivity) ltac:(lia) HappS ltac:(lia) ltac:(unfold SB in *; lia)
                  ltac:(replace (s - 2160 - 72)%Z with (s - 2232)%Z by lia; apply out_agree_store_ok; [exact HGr | cbn; lia])
                  (ret_ok_5f4f0) HGM kS) as RP.
    specialize (RP ltac:(intros x Hx; rewrite (HO x) by (unfold SB in *; lia); apply HZS; [lia | unfold SB in *; lia])).
    specialize (RP ltac:(rewrite HO by (unfold SB in *; unorm; lia); rewrite <- HlS_def; apply HLS; lia) HkS).
    destruct (RP r1 Q10 Q11 Q2 Q1) as (r2 & M2 & RUN2 & V10 & V2 & V1 & K2 & F2 & G2).
    assert (S23 : getr r2 23 = Z_to_bv 64 pd) by (rewrite (K2 23%bv) by (cbv; tauto); exact Q23).
    assert (S24 : getr r2 24 = Z_to_bv 64 ps) by (rewrite (K2 24%bv) by (cbv; tauto); exact Q24).
    assert (S9 : getr r2 9 = Z_to_bv 64 n) by (rewrite (K2 9%bv) by (cbv; tauto); exact Q9).
    assert (S8 : getr r2 8 = Z_to_bv 64 s) by (rewrite (K2 8%bv) by (cbv; tauto); exact Q8).
    assert (S22 : getr r2 22 = Z_to_bv 64 (n - 65)) by (rewrite (K2 22%bv) by (cbv; tauto); exact Q22).
    assert (S20 : getr r2 20 = Z_to_bv 64 (pd + n)) by (rewrite (K2 20%bv) by (cbv; tauto); exact Q20).
    eexists. exists M2. split; [|split; [|split; [|eapply FR_region; eassumption]]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
      stepiv F_803d0 D_803d0 (Z_to_bv 64 ps) ltac:(wval).
      stepiv F_803d4 D_803d4 (Z_to_bv 64 n) ltac:(wval).
      stepiv F_803d8 D_803d8 (Z_to_bv 64 0) ltac:(wval).
      stepiv F_803dc D_803dc (Z_to_bv 64 pd) ltac:(wval).
      stepb_tk F_803e0 D_803e0 ltac:(cond).
      apply mst_refl.
    - unfold cR_post. post.
    - eapply keeps_but_trans; [exact K1|]. solve_keeps_but.
  Qed.

  Definition cRqa_post (u0 u1 : Z) (rg : bvmap 5 word) : Prop :=
    getr rg 13 = Z_to_bv 64 fS /\ getr rg 14 = Z_to_bv 64 lS /\ getr rg 19 = Z_to_bv 64 (ps + n - 1) /\ getr rg 15 = Z_to_bv 64 (Z.lor u1 u0)
    /\ getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 s
    /\ getr rg 22 = Z_to_bv 64 (n - 65) /\ getr rg 20 = Z_to_bv 64 (pd + n) /\ getr rg 2 = Z_to_bv 64 (s - 2160).
  Lemma cRqa_run : forall M regs w0 w1,
    cR_pre regs -> out_agree M -> (0 < n <= 64)%Z ->
    rdn ASEGS M (Z_to_bv 64 faS) 8%nat = Some w0 -> rdn ASEGS M (Z_to_bv 64 laS) 8%nat = Some w1 ->
    (0 <= bytes_le_to_Z w0 < 2 ^ 64)%Z -> (0 <= bytes_le_to_Z w1 < 2 ^ 64)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x800d0 : word) M rom) (mkst regs' (0x80118 : word) M rom)
      /\ cRqa_post (bytes_le_to_Z w0) (bytes_le_to_Z w1) regs' /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros M regs w0 w1 (H10 & H11 & H12 & H8 & H19 & H20 & H2) HO Hn64 R0 R1 B0 B1.
    pose proof pS_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq).
    pose proof (flS_facts ltac:(lia)) as (F1 & F2 & F3 & F4).
    pose proof (out_agree_globs M HO) as ((G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8) & _).
    unfold SB, HIGHEND in *.
    pose proof (Z.div_mod ps 8 ltac:(lia)) as Dp. pose proof (Z.mod_pos_bound ps 8 ltac:(lia)) as Mp.
    pose proof (Z.mod_pos_bound fS 8 ltac:(lia)) as Mf. pose proof (Z.mod_pos_bound lS 8 ltac:(lia)) as Ml.
    pose proof (lor_bound64 (bytes_le_to_Z w1) (bytes_le_to_Z w0) B1 B0) as BL.
    eexists. split.
    - stepiv F_80080 D_80080 (Z_to_bv 64 (2 ^ 64 - 1 - ps)) ltac:(xval).
      stepb_ft F_80084 D_80084 ltac:(cond).
      stepiv F_80088 D_80088 (Z_to_bv 64 (2 ^ 64 + n - 65)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; rewrite (zbv_wrap_up (n + - 65)); f_equal; lia).
      stepn F_8008c D_8008c.
      stepb_ft F_80090 D_80090 ltac:(cond).
      stepn F_80094 D_80094.
      mld F_80098 D_80098 (0x153138 : word) G1.
      mld F_8009c D_8009c (0x15c9b8 : word) G2.
      stepiv F_800a0 D_800a0 (Z_to_bv 64 (ps + n - 1)) ltac:(wval).
      stepiv F_800a4 D_800a4 (Z_to_bv 64 (ps / 8)) ltac:(wval).
      stepiv F_800a8 D_800a8 (Z_to_bv 64 ((ps + n - 1) / 8)) ltac:(wval).
      stepiv F_800ac D_800ac (Z_to_bv 64 fS) ltac:(wval).
      stepiv F_800b0 D_800b0 (Z_to_bv 64 lS) ltac:(wval).
      stepiv F_800b4 D_800b4 (Z_to_bv 64 faS)
        ltac:(gres; rwH; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; f_equal; lia).
      stepiv F_800b8 D_800b8 (Z_to_bv 64 laS)
        ltac:(gres; rwH; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; f_equal; lia).
      mldw F_800bc D_800bc faS R0 w0.
      mldw F_800c0 D_800c0 laS R1 w1.
      stepov F_800c4 D_800c4 (Z_to_bv 64 (Z.lor (bytes_le_to_Z w1) (bytes_le_to_Z w0))) ltac:(gres; rwH; unfold v_or; unorm; reflexivity).
      apply mst_refl.
    - unfold cRqa_post. split; [post | solve_keeps_but].
  Qed.

  Definition qlR_inv (rg : bvmap 5 word) (i : Z) : Prop :=
    getr rg 13 = Z_to_bv 64 (fS + i) /\ getr rg 14 = Z_to_bv 64 lS /\ getr rg 15 = Z_to_bv 64 0 /\ getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 s
    /\ getr rg 22 = Z_to_bv 64 (n - 65) /\ getr rg 20 = Z_to_bv 64 (pd + n) /\ getr rg 2 = Z_to_bv 64 (s - 2160).
  Definition qlR_post (rg : bvmap 5 word) : Prop :=
    getr rg 15 = Z_to_bv 64 0 /\ getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 s
    /\ getr rg 22 = Z_to_bv 64 (n - 65) /\ getr rg 20 = Z_to_bv 64 (pd + n) /\ getr rg 2 = Z_to_bv 64 (s - 2160).
  Lemma qloopR_run : forall M (q : nat) regs i,
    out_agree M -> (0 < n)%Z -> qlR_inv regs i -> (0 <= i)%Z -> (fS + i + Z.of_nat q + 1 = lS)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x803f0 : word) M rom) (mkst regs' (0x80400 : word) M rom)
      /\ qlR_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros M q. induction q as [|q IH]; intros regs i HO Hn0 (H13 & H14 & H15 & H10 & H11 & H12 & H8 & H22 & H20 & H2) Hi Hq;
      pose proof (flS_facts Hn0) as (F1 & F2 & _); unfold SB in *.
    - eexists. split.
      + mlbu0 F_803a0 D_803a0 (fS + i)%Z rdn1S.
        stepiv F_803a4 D_803a4 (Z_to_bv 64 (fS + i + 1)) ltac:(wval).
        stepov F_803a8 D_803a8 (Z_to_bv 64 0) ltac:(vlit).
        stepb_ft F_803ac D_803ac ltac:(cond).
        apply mst_refl.
      + unfold qlR_post. post.
    - eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x803f0 : word) M rom) (fun rg => qlR_inv rg (i + 1) /\ keeps_but RIPL regs rg)).
      + eexists. split.
        * mlbu0 F_803a0 D_803a0 (fS + i)%Z rdn1S.
          stepiv F_803a4 D_803a4 (Z_to_bv 64 (fS + i + 1)) ltac:(wval).
          stepov F_803a8 D_803a8 (Z_to_bv 64 0) ltac:(vlit).
          stepb_tk F_803ac D_803ac ltac:(cond).
          apply mst_refl.
        * unfold qlR_inv. post.
      + cbv beta. intros r1 (I1 & K1).
        destruct (IH r1 (i + 1)%Z HO Hn0 I1 ltac:(lia) ltac:(lia)) as (r2 & RUN & P2 & K2).
        exists r2. split; [exact RUN | split; [exact P2 | eapply keeps_but_trans; eassumption]].
  Qed.

  Lemma cRqf_run : forall M regs u0 u1,
    cRqa_post u0 u1 regs -> (0 <= Z.lor u1 u0 < 2 ^ 64)%Z -> Z.lor u1 u0 = 0%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x80118 : word) M rom) (mkst regs' (0x8011c : word) M rom)
      /\ cR_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros M regs u0 u1 (H13 & H14 & HL' & H15 & H10 & H11 & H12 & H8 & H22 & H20 & H2) BL E.
    eexists. split.
    - stepb_ft F_800c8 D_800c8 ltac:(cond).
      apply mst_refl.
    - unfold cR_post. post.
  Qed.

  Lemma cRqs_run : forall M regs u0 u1,
    cRqa_post u0 u1 regs -> out_agree M -> (0 < n <= 64)%Z -> (0 <= Z.lor u1 u0 < 2 ^ 64)%Z -> Z.lor u1 u0 <> 0%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x80118 : word) M rom) (mkst regs' (0x8011c : word) M rom)
      /\ cR_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros M regs u0 u1 (H13 & H14 & HL' & H15 & H10 & H11 & H12 & H8 & H22 & H20 & H2) HO Hn64 BL NE.
    pose proof pS_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq).
    pose proof (flS_facts ltac:(lia)) as (F1 & F2 & F3 & F4). unfold SB, HIGHEND in *.
    pose proof (Z.mod_pos_bound (ps + n - 1) 8 ltac:(lia)) as Mq.
    eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x803ec : word) M rom) (fun rg => qlR_inv rg 0 /\ keeps_but RIPL regs rg)).
    { unhide HkS. destruct HkS as [K0|K7].
      - eexists. split.
        + stepb_tk F_800c8 D_800c8 ltac:(cond).
          mlbk F_80384 D_80384 lS rdnLS kS.
          stepiv F_80388 D_80388 (Z_to_bv 64 ((ps + n - 1) mod 8))
            ltac:(gres; rwH; unfold v_andi; imm_norm; unorm; rewrite land7_mod8; reflexivity).
          stepov F_8038c D_8038c (Z_to_bv 64 0)
            ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (0 <? kS)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
          stepov F_80390 D_80390 (Z_to_bv 64 0)
            ltac:(gres; rwH; unfold v_slt, c_lts, bv_lts; rewrite !signed64_small by lia;
                  replace ((ps + n - 1) mod 8 <? kS)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
          stepiv F_80394 D_80394 (Z_to_bv 64 1) ltac:(vlit).
          stepov F_80398 D_80398 (Z_to_bv 64 0) ltac:(vlit).
          apply mst_refl.
        + unfold qlR_inv. post.
      - eexists. split.
        + stepb_tk F_800c8 D_800c8 ltac:(cond).
          mlbk F_80384 D_80384 lS rdnLS kS.
          stepiv F_80388 D_80388 (Z_to_bv 64 ((ps + n - 1) mod 8))
            ltac:(gres; rwH; unfold v_andi; imm_norm; unorm; rewrite land7_mod8; reflexivity).
          stepov F_8038c D_8038c (Z_to_bv 64 1)
            ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (0 <? kS)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
          stepov F_80390 D_80390 (Z_to_bv 64 1)
            ltac:(gres; rwH; unfold v_slt, c_lts, bv_lts; rewrite !signed64_small by lia;
                  replace ((ps + n - 1) mod 8 <? kS)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
          stepiv F_80394 D_80394 (Z_to_bv 64 0) ltac:(vlit).
          stepov F_80398 D_80398 (Z_to_bv 64 0) ltac:(vlit).
          apply mst_refl.
        + unfold qlR_inv. post. }
    cbv beta. intros r1 ((I13 & I14 & I15 & I10 & I11 & I12 & I8 & I22 & I20 & I2) & K1).
    eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x80400 : word) M rom) (fun rg => qlR_post rg /\ keeps_but RIPL regs rg)).
    { destruct (Z.lt_ge_cases fS lS) as [Hfl|Hfl].
      - eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x803f0 : word) M rom) (fun rg => qlR_inv rg 0 /\ keeps_but RIPL regs rg)).
        + eexists. split.
          * stepb_ft F_8039c D_8039c ltac:(cond).
            apply mst_refl.
          * split; [unfold qlR_inv; repeat split; assumption | exact K1].
        + cbv beta. intros r2 (I2' & K2).
          destruct (qloopR_run M (Z.to_nat (lS - fS - 1)) r2 0 HO ltac:(lia) I2' ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (r3 & RUN3 & P3 & K3).
          exists r3. split; [exact RUN3 | split; [exact P3 | eapply keeps_but_trans; eassumption]].
      - eexists. split.
        + stepb_tk F_8039c D_8039c ltac:(cond).
          apply mst_refl.
        + split; [unfold qlR_post; repeat split; assumption | exact K1]. }
    cbv beta. intros r4 ((J15 & J10 & J11 & J12 & J8 & J22 & J20 & J2) & K4).
    eexists. split.
    - stepiv F_803b0 D_803b0 (Z_to_bv 64 0) ltac:(vlit).
      stepb_tk F_803b4 D_803b4 ltac:(cond).
      apply mst_refl.
    - unfold cR_post. split; [post|]. eapply keeps_but_trans; [exact K4|]. solve_keeps_but.
  Qed.

  Lemma cR_run : forall regs0 M regs,
    cR_pre regs -> FR regs0 M ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x800d0 : word) M rom) (mkst regs' (0x8011c : word) M' rom)
      /\ cR_post regs' /\ keeps_but RIPL regs regs' /\ FR regs0 M'.
  Proof.
    hide_dj.
    intros regs0 M regs P1 HFR. pose proof HFR as (HO & HGr & HR).
    destruct (Z.eq_dec n 0) as [Hn0|Hn0].
    { destruct (cRz_run M regs P1 Hn0) as (r2 & RUN2 & P2 & K2). exists r2, M.
      split; [exact RUN2 | split; [exact P2 | split; [exact K2 | exact HFR]]]. }

    destruct (Z.le_gt_cases n 64) as [Hle|Hgt].
    - destruct (rdnWS M HO ltac:(lia)) as (w0 & w1 & R0 & R1 & B0 & B1).
      destruct (cRqa_run M regs w0 w1 P1 HO ltac:(lia) R0 R1 B0 B1) as (r2 & RUN2 & P2 & K2).
      pose proof (lor_bound64 _ _ B1 B0) as BL.
      destruct (Z.eq_dec (Z.lor (bytes_le_to_Z w1) (bytes_le_to_Z w0)) 0) as [E|NE].
      + destruct (cRqf_run M r2 _ _ P2 BL E) as (r3 & RUN3 & P3 & K3). exists r3, M.
        split; [eapply msteps_trans; [exact RUN2 | exact RUN3] | split; [exact P3 | split; [eapply keeps_but_trans; eassumption | exact HFR]]].
      + destruct (cRqs_run M r2 _ _ P2 HO ltac:(lia) BL NE) as (r3 & RUN3 & P3 & K3). exists r3, M.
        split; [eapply msteps_trans; [exact RUN2 | exact RUN3] | split; [exact P3 | split; [eapply keeps_but_trans; eassumption | exact HFR]]].
    - exact (cRr_run regs0 M regs P1 HFR Hgt).
  Qed.

  Definition cW_pre (rg : bvmap 5 word) : Prop :=
    getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 s
    /\ getr rg 22 = Z_to_bv 64 (n - 65) /\ getr rg 20 = Z_to_bv 64 (pd + n) /\ getr rg 2 = Z_to_bv 64 (s - 2160).
  Definition cW_post (rg : bvmap 5 word) : Prop :=
    getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 2 = Z_to_bv 64 (s - 2160).

  Lemma cWz_run : forall M regs,
    cW_pre regs -> n = 0%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x8011c : word) M rom) (mkst regs' (0x80164 : word) M rom)
      /\ cW_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros M regs (H10 & H11 & H12 & H8 & H22 & H20 & H2) Hn0. pose proof pD_facts as (Pp & Ppn & Pp8 & Pq). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq). unfold HIGHEND in *.
    rewrite (zbv_wrap_up (n - 65)) in H22.
    eexists. split.
    - stepiv F_800cc D_800cc (Z_to_bv 64 (2 ^ 64 - 1 - pd)) ltac:(xval).
      stepb_ft F_800d0 D_800d0 ltac:(cond).
      stepn F_800d4 D_800d4.
      stepb_tk F_800d8 D_800d8 ltac:(cond).
      stepb_ft F_80230 D_80230 ltac:(cond).
      stepn F_80234 D_80234.
      apply mst_refl.
    - unfold cW_post. post.
  Qed.

  Lemma ret_ok_5f5ec : ret_ok (0x8051c : word).  Proof. hide_dj. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
  Lemma cWr_run : forall regs0 M regs,
    cW_pre regs -> FR regs0 M -> (64 < n)%Z ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x8011c : word) M rom) (mkst regs' (0x80164 : word) M' rom)
      /\ cW_post regs' /\ keeps_but RIPL regs regs' /\ FR regs0 M'.
  Proof.
    hide_dj.
    intros regs0 M regs (H10 & H11 & H12 & H8 & H22 & H20 & H2) HFR Hn64. pose proof HFR as (HO & HGr & HR).
    pose proof pD_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq). unfold HIGHEND in *.
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x8011c : word) M rom) (mkst r1 (0x826a0 : word) M rom)
              /\ (getr r1 10 = Z_to_bv 64 pd /\ getr r1 11 = Z_to_bv 64 n /\ getr r1 2 = Z_to_bv 64 (s - 2160) /\ getr r1 1 = (0x8051c : word)
                  /\ getr r1 9 = Z_to_bv 64 pd /\ getr r1 22 = Z_to_bv 64 ps /\ getr r1 18 = Z_to_bv 64 n /\ keeps_but RIPL regs r1)).
    { eexists. split.
      - stepiv F_800cc D_800cc (Z_to_bv 64 (2 ^ 64 - 1 - pd)) ltac:(xval).
        stepb_ft F_800d0 D_800d0 ltac:(cond).
        stepn F_800d4 D_800d4.
        stepb_tk F_800d8 D_800d8 ltac:(cond).
        stepb_tk F_80230 D_80230 ltac:(cond).
        stepiv F_804b8 D_804b8 (Z_to_bv 64 pd) ltac:(wval).
        stepiv F_804bc D_804bc (Z_to_bv 64 ps) ltac:(wval).
        stepiv F_804c0 D_804c0 (Z_to_bv 64 n) ltac:(wval).
        stepiv F_804c4 D_804c4 (Z_to_bv 64 n) ltac:(wval).
        stepn F_804c8 D_804c8.
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q2 & Q1 & Q9 & Q22 & Q18 & K1).
    pose proof (out_agree_globs M HO) as (HGM & _).
    pose proof (region_is_poisoned_run M rom (Z_to_bv 64 (s - 2160)) (0x8051c : word) pd n (s - 2160)
                  ltac:(unorm; reflexivity) ltac:(lia) HappD ltac:(lia) ltac:(unfold SB in *; lia)
                  ltac:(replace (s - 2160 - 72)%Z with (s - 2232)%Z by lia; apply out_agree_store_ok; [exact HGr | cbn; lia])
                  (ret_ok_5f5ec) HGM kD) as RP.
    specialize (RP ltac:(intros x Hx; rewrite (HO x) by (unfold SB in *; lia); apply HZD; [lia | unfold SB in *; lia])).
    specialize (RP ltac:(rewrite HO by (unfold SB in *; unorm; lia); rewrite <- HlD_def; apply HLD; lia) HkD).
    destruct (RP r1 Q10 Q11 Q2 Q1) as (r2 & M2 & RUN2 & V10 & V2 & V1 & K2 & F2 & G2).
    assert (S9 : getr r2 9 = Z_to_bv 64 pd) by (rewrite (K2 9%bv) by (cbv; tauto); exact Q9).
    assert (S22 : getr r2 22 = Z_to_bv 64 ps) by (rewrite (K2 22%bv) by (cbv; tauto); exact Q22).
    assert (S18 : getr r2 18 = Z_to_bv 64 n) by (rewrite (K2 18%bv) by (cbv; tauto); exact Q18).
    eexists. exists M2. split; [|split; [|split; [|eapply FR_region; eassumption]]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
      stepiv F_804cc D_804cc (Z_to_bv 64 ps) ltac:(wval).
      stepiv F_804d0 D_804d0 (Z_to_bv 64 n) ltac:(wval).
      stepiv F_804d4 D_804d4 (Z_to_bv 64 0) ltac:(wval).
      stepiv F_804d8 D_804d8 (Z_to_bv 64 pd) ltac:(wval).
      stepb_tk F_804dc D_804dc ltac:(cond).
      apply mst_refl.
    - unfold cW_post. post.
    - eapply keeps_but_trans; [exact K1|]. solve_keeps_but.
  Qed.

  Definition cWqa_post (u0 u1 : Z) (rg : bvmap 5 word) : Prop :=
    getr rg 13 = Z_to_bv 64 fD /\ getr rg 14 = Z_to_bv 64 lD /\ getr rg 20 = Z_to_bv 64 (pd + n - 1) /\ getr rg 15 = Z_to_bv 64 (Z.lor u1 u0)
    /\ getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 2 = Z_to_bv 64 (s - 2160).
  Lemma cWqa_run : forall M regs w0 w1,
    cW_pre regs -> out_agree M -> (0 < n <= 64)%Z ->
    rdn ASEGS M (Z_to_bv 64 faD) 8%nat = Some w0 -> rdn ASEGS M (Z_to_bv 64 laD) 8%nat = Some w1 ->
    (0 <= bytes_le_to_Z w0 < 2 ^ 64)%Z -> (0 <= bytes_le_to_Z w1 < 2 ^ 64)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x8011c : word) M rom) (mkst regs' (0x80160 : word) M rom)
      /\ cWqa_post (bytes_le_to_Z w0) (bytes_le_to_Z w1) regs' /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros M regs w0 w1 (H10 & H11 & H12 & H8 & H22 & H20 & H2) HO Hn64 R0 R1 B0 B1.
    rewrite (zbv_wrap_up (n - 65)) in H22.
    pose proof pD_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq).
    pose proof (flD_facts ltac:(lia)) as (F1 & F2 & F3 & F4).
    pose proof (out_agree_globs M HO) as ((G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8) & _).
    unfold SB, HIGHEND in *.
    pose proof (Z.div_mod pd 8 ltac:(lia)) as Dp. pose proof (Z.mod_pos_bound pd 8 ltac:(lia)) as Mp.
    pose proof (Z.mod_pos_bound fD 8 ltac:(lia)) as Mf. pose proof (Z.mod_pos_bound lD 8 ltac:(lia)) as Ml.
    pose proof (lor_bound64 (bytes_le_to_Z w1) (bytes_le_to_Z w0) B1 B0) as BL.
    eexists. split.
    - stepiv F_800cc D_800cc (Z_to_bv 64 (2 ^ 64 - 1 - pd)) ltac:(xval).
      stepb_ft F_800d0 D_800d0 ltac:(cond).
      stepn F_800d4 D_800d4.
      stepb_ft F_800d8 D_800d8 ltac:(cond).
      stepn F_800dc D_800dc.
      mld F_800e0 D_800e0 (0x153138 : word) G1.
      mld F_800e4 D_800e4 (0x15c9b8 : word) G2.
      stepiv F_800e8 D_800e8 (Z_to_bv 64 (pd + n - 1)) ltac:(wval).
      stepiv F_800ec D_800ec (Z_to_bv 64 (pd / 8)) ltac:(wval).
      stepiv F_800f0 D_800f0 (Z_to_bv 64 ((pd + n - 1) / 8)) ltac:(wval).
      stepiv F_800f4 D_800f4 (Z_to_bv 64 fD) ltac:(wval).
      stepiv F_800f8 D_800f8 (Z_to_bv 64 lD) ltac:(wval).
      stepiv F_800fc D_800fc (Z_to_bv 64 faD)
        ltac:(gres; rwH; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; f_equal; lia).
      stepiv F_80100 D_80100 (Z_to_bv 64 laD)
        ltac:(gres; rwH; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; f_equal; lia).
      mldw F_80104 D_80104 faD R0 w0.
      mldw F_80108 D_80108 laD R1 w1.
      stepov F_8010c D_8010c (Z_to_bv 64 (Z.lor (bytes_le_to_Z w1) (bytes_le_to_Z w0))) ltac:(gres; rwH; unfold v_or; unorm; reflexivity).
      apply mst_refl.
    - unfold cWqa_post. split; [post | solve_keeps_but].
  Qed.

  Definition qlW_inv (rg : bvmap 5 word) (i : Z) : Prop :=
    getr rg 13 = Z_to_bv 64 (fD + i) /\ getr rg 14 = Z_to_bv 64 lD /\ getr rg 15 = Z_to_bv 64 0 /\ getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 2 = Z_to_bv 64 (s - 2160).
  Definition qlW_post (rg : bvmap 5 word) : Prop :=
    getr rg 15 = Z_to_bv 64 0 /\ getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 2 = Z_to_bv 64 (s - 2160).
  Lemma qloopW_run : forall M (q : nat) regs i,
    out_agree M -> (0 < n)%Z -> qlW_inv regs i -> (0 <= i)%Z -> (fD + i + Z.of_nat q + 1 = lD)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x804f0 : word) M rom) (mkst regs' (0x80500 : word) M rom)
      /\ qlW_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros M q. induction q as [|q IH]; intros regs i HO Hn0 (H13 & H14 & H15 & H10 & H11 & H12 & H2) Hi Hq;
      pose proof (flD_facts Hn0) as (F1 & F2 & _); unfold SB in *.
    - eexists. split.
      + mlbu0 F_804a0 D_804a0 (fD + i)%Z rdn1D.
        stepiv F_804a4 D_804a4 (Z_to_bv 64 (fD + i + 1)) ltac:(wval).
        stepov F_804a8 D_804a8 (Z_to_bv 64 0) ltac:(vlit).
        stepb_ft F_804ac D_804ac ltac:(cond).
        apply mst_refl.
      + unfold qlW_post. post.
    - eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x804f0 : word) M rom) (fun rg => qlW_inv rg (i + 1) /\ keeps_but RIPL regs rg)).
      + eexists. split.
        * mlbu0 F_804a0 D_804a0 (fD + i)%Z rdn1D.
          stepiv F_804a4 D_804a4 (Z_to_bv 64 (fD + i + 1)) ltac:(wval).
          stepov F_804a8 D_804a8 (Z_to_bv 64 0) ltac:(vlit).
          stepb_tk F_804ac D_804ac ltac:(cond).
          apply mst_refl.
        * unfold qlW_inv. post.
      + cbv beta. intros r1 (I1 & K1).
        destruct (IH r1 (i + 1)%Z HO Hn0 I1 ltac:(lia) ltac:(lia)) as (r2 & RUN & P2 & K2).
        exists r2. split; [exact RUN | split; [exact P2 | eapply keeps_but_trans; eassumption]].
  Qed.

  Lemma cWqf_run : forall M regs u0 u1,
    cWqa_post u0 u1 regs -> (0 <= Z.lor u1 u0 < 2 ^ 64)%Z -> Z.lor u1 u0 = 0%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x80160 : word) M rom) (mkst regs' (0x80164 : word) M rom)
      /\ cW_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros M regs u0 u1 (H13 & H14 & HL' & H15 & H10 & H11 & H12 & H2) BL E.
    eexists. split.
    - stepb_ft F_80110 D_80110 ltac:(cond).
      apply mst_refl.
    - unfold cW_post. post.
  Qed.

  Lemma cWqs_run : forall M regs u0 u1,
    cWqa_post u0 u1 regs -> out_agree M -> (0 < n <= 64)%Z -> (0 <= Z.lor u1 u0 < 2 ^ 64)%Z -> Z.lor u1 u0 <> 0%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x80160 : word) M rom) (mkst regs' (0x80164 : word) M rom)
      /\ cW_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros M regs u0 u1 (H13 & H14 & HL' & H15 & H10 & H11 & H12 & H2) HO Hn64 BL NE.
    pose proof pD_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq).
    pose proof (flD_facts ltac:(lia)) as (F1 & F2 & F3 & F4). unfold SB, HIGHEND in *.
    pose proof (Z.mod_pos_bound (pd + n - 1) 8 ltac:(lia)) as Mq.
    eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x804ec : word) M rom) (fun rg => qlW_inv rg 0 /\ keeps_but RIPL regs rg)).
    { unhide HkD. destruct HkD as [K0|K7].
      - eexists. split.
        + stepb_tk F_80110 D_80110 ltac:(cond).
          mlbk F_80484 D_80484 lD rdnLD kD.
          stepiv F_80488 D_80488 (Z_to_bv 64 ((pd + n - 1) mod 8))
            ltac:(gres; rwH; unfold v_andi; imm_norm; unorm; rewrite land7_mod8; reflexivity).
          stepov F_8048c D_8048c (Z_to_bv 64 0)
            ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (0 <? kD)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
          stepov F_80490 D_80490 (Z_to_bv 64 0)
            ltac:(gres; rwH; unfold v_slt, c_lts, bv_lts; rewrite !signed64_small by lia;
                  replace ((pd + n - 1) mod 8 <? kD)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
          stepiv F_80494 D_80494 (Z_to_bv 64 1) ltac:(vlit).
          stepov F_80498 D_80498 (Z_to_bv 64 0) ltac:(vlit).
          apply mst_refl.
        + unfold qlW_inv. post.
      - eexists. split.
        + stepb_tk F_80110 D_80110 ltac:(cond).
          mlbk F_80484 D_80484 lD rdnLD kD.
          stepiv F_80488 D_80488 (Z_to_bv 64 ((pd + n - 1) mod 8))
            ltac:(gres; rwH; unfold v_andi; imm_norm; unorm; rewrite land7_mod8; reflexivity).
          stepov F_8048c D_8048c (Z_to_bv 64 1)
            ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (0 <? kD)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
          stepov F_80490 D_80490 (Z_to_bv 64 1)
            ltac:(gres; rwH; unfold v_slt, c_lts, bv_lts; rewrite !signed64_small by lia;
                  replace ((pd + n - 1) mod 8 <? kD)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
          stepiv F_80494 D_80494 (Z_to_bv 64 0) ltac:(vlit).
          stepov F_80498 D_80498 (Z_to_bv 64 0) ltac:(vlit).
          apply mst_refl.
        + unfold qlW_inv. post. }
    cbv beta. intros r1 ((I13 & I14 & I15 & I10 & I11 & I12 & I2) & K1).
    eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x80500 : word) M rom) (fun rg => qlW_post rg /\ keeps_but RIPL regs rg)).
    { destruct (Z.lt_ge_cases fD lD) as [Hfl|Hfl].
      - eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x804f0 : word) M rom) (fun rg => qlW_inv rg 0 /\ keeps_but RIPL regs rg)).
        + eexists. split.
          * stepb_ft F_8049c D_8049c ltac:(cond).
            apply mst_refl.
          * split; [unfold qlW_inv; repeat split; assumption | exact K1].
        + cbv beta. intros r2 (I2' & K2).
          destruct (qloopW_run M (Z.to_nat (lD - fD - 1)) r2 0 HO ltac:(lia) I2' ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (r3 & RUN3 & P3 & K3).
          exists r3. split; [exact RUN3 | split; [exact P3 | eapply keeps_but_trans; eassumption]].
      - eexists. split.
        + stepb_tk F_8049c D_8049c ltac:(cond).
          apply mst_refl.
        + split; [unfold qlW_post; repeat split; assumption | exact K1]. }
    cbv beta. intros r4 ((J15 & J10 & J11 & J12 & J2) & K4).
    eexists. split.
    - stepiv F_804b0 D_804b0 (Z_to_bv 64 0) ltac:(vlit).
      stepb_tk F_804b4 D_804b4 ltac:(cond).
      apply mst_refl.
    - unfold cW_post. split; [post|]. eapply keeps_but_trans; [exact K4|]. solve_keeps_but.
  Qed.

  Lemma cW_run : forall regs0 M regs,
    cW_pre regs -> FR regs0 M ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x8011c : word) M rom) (mkst regs' (0x80164 : word) M' rom)
      /\ cW_post regs' /\ keeps_but RIPL regs regs' /\ FR regs0 M'.
  Proof.
    hide_dj.
    intros regs0 M regs P1 HFR. pose proof HFR as (HO & HGr & HR).
    destruct (Z.eq_dec n 0) as [Hn0|Hn0].
    { destruct (cWz_run M regs P1 Hn0) as (r2 & RUN2 & P2 & K2). exists r2, M.
      split; [exact RUN2 | split; [exact P2 | split; [exact K2 | exact HFR]]]. }

    destruct (Z.le_gt_cases n 64) as [Hle|Hgt].
    - destruct (rdnWD M HO ltac:(lia)) as (w0 & w1 & R0 & R1 & B0 & B1).
      destruct (cWqa_run M regs w0 w1 P1 HO ltac:(lia) R0 R1 B0 B1) as (r2 & RUN2 & P2 & K2).
      pose proof (lor_bound64 _ _ B1 B0) as BL.
      destruct (Z.eq_dec (Z.lor (bytes_le_to_Z w1) (bytes_le_to_Z w0)) 0) as [E|NE].
      + destruct (cWqf_run M r2 _ _ P2 BL E) as (r3 & RUN3 & P3 & K3). exists r3, M.
        split; [eapply msteps_trans; [exact RUN2 | exact RUN3] | split; [exact P3 | split; [eapply keeps_but_trans; eassumption | exact HFR]]].
      + destruct (cWqs_run M r2 _ _ P2 HO ltac:(lia) BL NE) as (r3 & RUN3 & P3 & K3). exists r3, M.
        split; [eapply msteps_trans; [exact RUN2 | exact RUN3] | split; [exact P3 | split; [eapply keeps_but_trans; eassumption | exact HFR]]].
    - exact (cWr_run regs0 M regs P1 HFR Hgt).
  Qed.

  Lemma ret_ok_5f240 : ret_ok (0x80170 : word).  Proof. hide_dj. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

  Lemma slots_ok_mc : forall regs0 M, slots_ok regs0 M -> slots_ok regs0 (wbytes M (Z_to_bv 64 pd) bs).
  Proof.
    hide_dj.
    intros regs0 M R. unhide HdjD.
    pose proof pD_facts as (Pp & Ppn & _). unfold HIGHEND in *.
    pose proof (rdn_length _ _ _ _ _ Hsrc) as LEN.
    apply (slots_ok_ext regs0 M); [|exact R]. intros x Hx. pose proof (u64_range x).
    destruct (Z_lt_le_dec 0 n) as [Np|Nz]; [| first [ rewrite (proj1 (length_zero_iff_nil bs) ltac:(lia)); reflexivity | replace (Z.to_nat n) with 0%nat by lia; reflexivity ] ].
    destruct (HdjD Np) as [Hd|Hd].
    - apply wbytes_above. rewrite LEN. unorm. lia.
    - apply wbytes_below; [rewrite LEN; unorm; lia | unorm; lia].
  Qed.

  Lemma c3_run : forall regs0 regs M,
    cW_post regs -> FR regs0 M ->
    exists regs',
      msteps ASEGS (mkst regs (0x80164 : word) M rom) (mkst regs' ra (wbytes M (Z_to_bv 64 pd) bs) rom)
      /\ getr regs' 10 = Z_to_bv 64 pd /\ getr regs' 2 = sp /\ getr regs' 1 = ra
      /\ getr regs' 8 = getr regs0 8 /\ getr regs' 9 = getr regs0 9 /\ getr regs' 18 = getr regs0 18
      /\ getr regs' 19 = getr regs0 19 /\ getr regs' 20 = getr regs0 20 /\ getr regs' 21 = getr regs0 21
      /\ getr regs' 22 = getr regs0 22 /\ getr regs' 23 = getr regs0 23 /\ getr regs' 24 = getr regs0 24
      /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros regs0 regs M (H10 & H11 & H12 & H2) (HO & HGr & HR).
    pose proof pS_facts as (PSp & PSn & _). pose proof pD_facts as (PDp & PDn & _). unfold HIGHEND in *.
    pose proof (out_agree_globs M HO) as (_ & (I1 & I2 & I3)).
    pose proof (rdn_length _ _ _ _ _ Hsrc) as LEN.
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x80164 : word) M rom) (mkst r1 (0x144f04 : word) M rom)
              /\ (getr r1 10 = Z_to_bv 64 pd /\ getr r1 11 = Z_to_bv 64 ps /\ getr r1 12 = Z_to_bv 64 n /\ getr r1 1 = (0x80170 : word)
                  /\ getr r1 2 = Z_to_bv 64 (s - 2160) /\ keeps_but RIPL regs r1)).
    { eexists. split.
      - stepn F_80114 D_80114.
        mld F_80118 D_80118 (0x155158 : word) I3.
        stepjr F_8011c D_8011c (Z_to_bv 64 0x144f04) ltac:(gres; reflexivity).
        vnorm. apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q12 & Q1 & Q2 & K1).
    assert (MC : mcH M (Z_to_bv 64 pd) (Z_to_bv 64 ps) n bs).
    { unhide Hover. constructor.
      - lia.
      - exact LEN.
      - rewrite LEN. apply out_agree_src. exact HO.
      - rewrite LEN. apply (store_ok_mono _ _ mem0 M _ HGr). exact Hdst.
      - unorm. lia.
      - unorm. lia.
      - unorm. lia. }
    destruct (ref_memcpy M (Z_to_bv 64 pd) (Z_to_bv 64 ps) n bs rom MC r1 (0x80170 : word) ret_ok_5f240 Q1 Q10 Q11 Q12) as (r2 & RUN2 & KP).
    pose proof (slots_ok_mc regs0 M HR) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10).
    assert (V2 : getr r2 2 = Z_to_bv 64 (s - 2160)) by (rewrite (KP 2%bv) by (cbv; tauto); exact Q2).
    assert (V10 : getr r2 10 = Z_to_bv 64 pd) by (rewrite (KP 10%bv) by (cbv; tauto); exact Q10).
    eexists. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
      stepiv F_80120 D_80120 (Z_to_bv 64 (s - 2032)) ltac:(wval).
      stepld F_80124 D_80124 ra ltac:(maddr (s - 8)%Z; exact R1).
      stepld F_80128 D_80128 (getr regs0 8) ltac:(maddr (s - 16)%Z; exact R2).
      stepld F_8012c D_8012c (getr regs0 9) ltac:(maddr (s - 24)%Z; exact R3).
      stepld F_80130 D_80130 (getr regs0 18) ltac:(maddr (s - 32)%Z; exact R4).
      stepld F_80134 D_80134 (getr regs0 19) ltac:(maddr (s - 40)%Z; exact R5).
      stepld F_80138 D_80138 (getr regs0 20) ltac:(maddr (s - 48)%Z; exact R6).
      stepld F_8013c D_8013c (getr regs0 21) ltac:(maddr (s - 56)%Z; exact R7).
      stepld F_80140 D_80140 (getr regs0 22) ltac:(maddr (s - 64)%Z; exact R8).
      stepld F_80144 D_80144 (getr regs0 23) ltac:(maddr (s - 72)%Z; exact R9).
      stepld F_80148 D_80148 (getr regs0 24) ltac:(maddr (s - 80)%Z; exact R10).
      stepiv F_8014c D_8014c (Z_to_bv 64 s) ltac:(wval).
      stepret F_80150 D_80150 ra ltac:(rwH; reflexivity).
      apply mst_refl.
    - repeat split; gres; try reflexivity; [exact V10 | symmetry; apply sp_s |].
      eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [apply keeps_but_cs; apply keeps_keeps_cs; exact KP|]. solve_keeps_but.
  Qed.

  Theorem memcpy_icpt_run : forall regs,
    getr regs 10 = Z_to_bv 64 pd -> getr regs 11 = Z_to_bv 64 ps -> getr regs 12 = Z_to_bv 64 n -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs' Mj,
      msteps ASEGS (mkst regs (0x80070 : word) mem0 rom) (mkst regs' ra (wbytes Mj (Z_to_bv 64 pd) bs) rom)
      /\ getr regs' 10 = Z_to_bv 64 pd /\ getr regs' 2 = sp /\ getr regs' 1 = ra /\ keeps_cs regs regs'
      /\ out_agree Mj /\ mem_grows mem0 Mj.
  Proof.
    hide_dj.
    intros regs H10 H11 H12 H2 H1.
    destruct (c1_run regs H10 H11 H12 H2 H1) as (r1 & RUN1 & P1 & K1).
    destruct (cR_run regs (M10 regs) r1 P1 (M10_FR regs)) as (r2 & M2 & RUN2 & P2 & K2 & F2).
    destruct (cW_run regs M2 r2 P2 F2) as (r3 & M3 & RUN3 & P3 & K3 & F3).
    destruct (c3_run regs r3 M3 P3 F3) as (r4 & RUN4 & Q10 & Q2 & Q1 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & K4).
    exists r4, M3. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. exact RUN4.
    - assert (KB : keeps_but RIPL regs r4).
      { eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [exact K2|]. eapply keeps_but_trans; [exact K3|]. exact K4. }
      destruct F3 as (HO & HGr & _).
      repeat split; try assumption.
      intros r Hr. destruct (decide (r = 1%bv)) as [->|N1]; [rewrite Q1, H1; reflexivity|].
      destruct (decide (r = 2%bv)) as [->|N2]; [rewrite Q2, H2; reflexivity|].
      destruct (decide (r = 8%bv)) as [->|N8]; [exact Q8|]. destruct (decide (r = 9%bv)) as [->|N9]; [exact Q9|].
      destruct (decide (r = 18%bv)) as [->|N18]; [exact Q18|]. destruct (decide (r = 19%bv)) as [->|N19]; [exact Q19|].
      destruct (decide (r = 20%bv)) as [->|N20]; [exact Q20|]. destruct (decide (r = 21%bv)) as [->|N21]; [exact Q21|].
      destruct (decide (r = 22%bv)) as [->|N22]; [exact Q22|]. destruct (decide (r = 23%bv)) as [->|N23]; [exact Q23|].
      destruct (decide (r = 24%bv)) as [->|N24]; [exact Q24|].
      apply KB; [exact Hr|]. cbv. intuition congruence.
  Qed.

  Corollary wrap_memcpy_run : forall regs,
    getr regs 10 = Z_to_bv 64 pd -> getr regs 11 = Z_to_bv 64 ps -> getr regs 12 = Z_to_bv 64 n -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs' Mj,
      msteps ASEGS (mkst regs (0x7ee70 : word) mem0 rom) (mkst regs' ra (wbytes Mj (Z_to_bv 64 pd) bs) rom)
      /\ getr regs' 10 = Z_to_bv 64 pd /\ getr regs' 2 = sp /\ getr regs' 1 = ra /\ keeps_cs regs regs'
      /\ out_agree Mj /\ mem_grows mem0 Mj.
  Proof.
    hide_dj.
    intros regs H10 H11 H12 H2 H1.
    destruct (memcpy_icpt_run regs H10 H11 H12 H2 H1) as (r' & M' & RUN & REST).
    exists r', M'. split; [|exact REST].
    eapply msteps_trans; [|exact RUN].
    stepn F_7ee20 D_7ee20.
    apply mst_refl.
  Qed.
End AMCI.
End FPX_1.
