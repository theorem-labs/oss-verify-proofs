(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit As0StepLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0MemIsZero_b Ba0RegionPoisoned_b Ba0AsanMemset_b Ba0AsanMemcpy_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.muslA Require Import Ba0MemcpyBase_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0IntMemmove_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r5df38_5f730_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

Section FPX_1. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Definition mm_icpt_globs (M : word -> option byte) : Prop :=
  rdn ASEGS M (0x138028 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x140919)) /\
  rdn ASEGS M (0x140919 : word) 1%nat = Some [Z_to_bv 8 1].

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

#[local] Definition RIPL : list reg := [1; 2; 8; 9; 18; 19; 20; 21; 22]%bv.      (* [comment removed for export] *)

Section AMM.
  Variable mem0 : word -> option byte.
  Variable rom : word -> option byte.
  Variables sp ra : word.
  Variables pd ps n s : Z.                         (* [comment removed for export] *)
  Variable bs : list byte.                         (* [comment removed for export] *)
  Variables kS fS lS faS laS : Z.                  (* [comment removed for export] *)
  Variables kD fD lD faD laD : Z.                  (* [comment removed for export] *)
  Hypothesis Hs_def : bv_unsigned sp = s.
  Hypothesis HfS_def : fS = (SB + ps / 8)%Z.           Hypothesis HlS_def : lS = (SB + (ps + n - 1) / 8)%Z.
  Hypothesis HfaS_def : faS = (fS - fS mod 8)%Z.       Hypothesis HlaS_def : laS = (lS - lS mod 8)%Z.
  Hypothesis HfD_def : fD = (SB + pd / 8)%Z.           Hypothesis HlD_def : lD = (SB + (pd + n - 1) / 8)%Z.
  Hypothesis HfaD_def : faD = (fD - fD mod 8)%Z.       Hypothesis HlaD_def : laD = (lD - lD mod 8)%Z.
  Hypothesis Hn : (0 <= n <= 2 ^ 40)%Z.
  Hypothesis HappS : in_app8 ps n.
  Hypothesis HappD : in_app8 pd n.
  Hypothesis Hs : (0x1000000 <= s - 2216)%Z /\ (s < 2 ^ 64)%Z.       (* [comment removed for export] *)
  Hypothesis HshS : (lS + 8 <= s - 2216)%Z.                           (* [comment removed for export] *)
  Hypothesis HshD : (lD + 8 <= s - 2216)%Z.
  Hypothesis HdjS : (0 < n -> ps + n <= s - 2216 \/ s <= ps)%Z.                (* [comment removed for export] *)
  Hypothesis HdjD : (0 < n -> pd + n <= s - 2216 \/ s <= pd)%Z.
  Hypothesis Hover : (pd + n <= ps \/ ps + n <= pd)%Z.                (* [comment removed for export] *)
  Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (s - 2216)) 2216%nat = true.
  Hypothesis Hdst : store_ok ASEGS mem0 (Z_to_bv 64 pd) (Z.to_nat n) = true.
  Hypothesis Hsrc : rdn ASEGS mem0 (Z_to_bv 64 ps) (Z.to_nat n) = Some bs.
  Hypothesis Hret : ret_ok ra.
  Hypothesis HG : rt_layout_globs mem0.
  Hypothesis HI : mm_icpt_globs mem0.
  Hypothesis HZS : (0 < n)%Z -> forall x : word, (fS <= bv_unsigned x < lS)%Z -> mem0 x = Some (Z_to_bv 8 0).
  Hypothesis HLS : (0 < n)%Z -> mem0 (Z_to_bv 64 lS) = Some (Z_to_bv 8 kS).
  Hypothesis HkS : kS = 0%Z \/ ((ps + n - 1) mod 8 < kS <= 7)%Z.
  Hypothesis HWS : (0 < n <= 64)%Z -> exists w0 w1, rdn ASEGS mem0 (Z_to_bv 64 faS) 8%nat = Some w0 /\ rdn ASEGS mem0 (Z_to_bv 64 laS) 8%nat = Some w1.
  Hypothesis HZD : (0 < n)%Z -> forall x : word, (fD <= bv_unsigned x < lD)%Z -> mem0 x = Some (Z_to_bv 8 0).
  Hypothesis HLD : (0 < n)%Z -> mem0 (Z_to_bv 64 lD) = Some (Z_to_bv 8 kD).
  Hypothesis HkD : kD = 0%Z \/ ((pd + n - 1) mod 8 < kD <= 7)%Z.
  Hypothesis HWD : (0 < n <= 64)%Z -> exists w0 w1, rdn ASEGS mem0 (Z_to_bv 64 faD) 8%nat = Some w0 /\ rdn ASEGS mem0 (Z_to_bv 64 laD) 8%nat = Some w1.

  #[local] Ltac post := repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try (rewrite (zbv_wrap_up (n - 65)); f_equal; lia); try solve_keeps_but.
  (* [comment removed for export] *)
  #[local] Ltac hide_dj := try hide HdjS; try hide HdjD; try hide Hover; try hide HkS; try hide HkD; try hide HappS; try hide HappD.

  #[using="Hs_def"] Lemma sp_s : sp = Z_to_bv 64 s.  Proof. hide_dj. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.
  #[using="pd fS lS fD lD Hn HappS"] Lemma pS_facts : (0 <= ps)%Z /\ (ps + n + 8 <= HIGHEND)%Z /\ (0 <= ps / 8 <= HIGHEND)%Z /\ (0 < n -> ps / 8 <= (ps + n - 1) / 8 <= HIGHEND)%Z.
  Proof.
    hide_dj.
    unhide HappS.
    unfold in_app8, LOWEND, HIGHBEG, HIGHEND in *. destruct HappS as [[H1 H2]|[H1 H2]];
    (repeat split; [lia | lia | apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia | intros; apply Z.div_le_mono; lia | intros; apply Z.div_le_upper_bound; lia]).
  Qed.
  #[using="ps fS lS fD lD Hn HappD"] Lemma pD_facts : (0 <= pd)%Z /\ (pd + n + 8 <= HIGHEND)%Z /\ (0 <= pd / 8 <= HIGHEND)%Z /\ (0 < n -> pd / 8 <= (pd + n - 1) / 8 <= HIGHEND)%Z.
  Proof.
    hide_dj.
    unhide HappD.
    unfold in_app8, LOWEND, HIGHBEG, HIGHEND in *. destruct HappD as [[H1 H2]|[H1 H2]];
    (repeat split; [lia | lia | apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia | intros; apply Z.div_le_mono; lia | intros; apply Z.div_le_upper_bound; lia]).
  Qed.
  #[using="pd ps fD lD HfS_def HlS_def HfaS_def HlaS_def HfD_def HlD_def Hn HappS HshS"] Lemma flS_facts : (0 < n)%Z -> (SB <= fS <= lS)%Z /\ (lS + 8 <= s - 2216)%Z /\ (fS - 7 <= faS <= fS)%Z /\ (lS - 7 <= laS <= lS)%Z.
  Proof.
    hide_dj.
    intros Hn0. pose proof pS_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq Hn0). unfold SB, HIGHEND in *.
    pose proof (Z.mod_pos_bound fS 8 ltac:(lia)). pose proof (Z.mod_pos_bound lS 8 ltac:(lia)). repeat split; lia.
  Qed.
  #[using="pd ps fS lS HfS_def HlS_def HfD_def HlD_def HfaD_def HlaD_def Hn HappD HshD"] Lemma flD_facts : (0 < n)%Z -> (SB <= fD <= lD)%Z /\ (lD + 8 <= s - 2216)%Z /\ (fD - 7 <= faD <= fD)%Z /\ (lD - 7 <= laD <= lD)%Z.
  Proof.
    hide_dj.
    intros Hn0. pose proof pD_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq Hn0). unfold SB, HIGHEND in *.
    pose proof (Z.mod_pos_bound fD 8 ltac:(lia)). pose proof (Z.mod_pos_bound lD 8 ltac:(lia)). repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Definition out_agree (M : word -> option byte) : Prop :=
    forall x : word, (bv_unsigned x < s - 2216 \/ s <= bv_unsigned x)%Z -> M x = mem0 x.
  #[using="Type"] Lemma out_agree_refl : out_agree mem0.  Proof. hide_dj. intros x _. reflexivity. Qed.
  #[using="pd ps n fS lS fD lD Hs"] Lemma out_agree_w : forall M k v, out_agree M -> (8 <= k <= 2216)%Z -> out_agree (wbytes M (Z_to_bv 64 (s - k)) (word_to_le_bytes 8 v)).
  Proof.
    hide_dj.
    intros M k v HF Hk x Hx. pose proof (u64_range x).
    destruct Hx as [Hx|Hx].
    - rewrite wbytes_below; [apply HF; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia].
    - rewrite wbytes_above; [apply HF; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia].
  Qed.
  #[using="pd ps n fS lS fD lD Hs"] Lemma out_agree_rdn : forall M (a : word) k, out_agree M -> (bv_unsigned a + Z.of_nat k <= s - 2216)%Z ->
    rdn ASEGS M a k = rdn ASEGS mem0 a k.
  Proof. hide_dj. intros M a k HF Ha. apply rdn_ext; [lia|]. intros x Hx. apply HF. lia. Qed.
  #[using="pd ps n fS lS fD lD Hs HG HI"] Lemma out_agree_globs : forall M, out_agree M -> rt_layout_globs M /\ mm_icpt_globs M.
  Proof.
    hide_dj.
    intros M HF. destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). destruct HI as (I1 & I2).
    unfold rt_layout_globs, mm_icpt_globs. rewrite !(out_agree_rdn M) by (first [exact HF | cbn [Z.of_nat Pos.to_nat]; imm_norm; lia]).
    repeat split; assumption.
  Qed.
  #[using="pd ps n fS lS fD lD Hs Hok"] Lemma out_agree_store_ok : forall M k (j : nat), mem_grows mem0 M -> (Z.of_nat j <= k <= 2216)%Z ->
    store_ok ASEGS M (Z_to_bv 64 (s - k)) j = true.
  Proof.
    hide_dj.
    intros M k j HGr Hk. apply (store_ok_mono _ _ mem0 M _ HGr).
    apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 2216)) _ 2216%nat); [unorm; cbn [Z.of_nat Pos.to_nat]; lia | exact Hok | unorm; lia | unorm; cbn [Z.of_nat Pos.to_nat]; lia].
  Qed.
  #[using="pd fS lS fD lD Hn HappS Hs HdjS Hsrc"] Lemma out_agree_src : forall M, out_agree M -> rdn ASEGS M (Z_to_bv 64 ps) (Z.to_nat n) = Some bs.
  Proof.
    hide_dj.
    intros M HF. pose proof pS_facts as (Pp & Ppn & _). unhide HdjS. unfold HIGHEND in *.
    rewrite (rdn_ext ASEGS (Z.to_nat n) M mem0); [exact Hsrc | unorm; rewrite Z2Nat.id by lia; lia|].
    intros x Hx. rewrite u_Z2bv in Hx by lia. rewrite Z2Nat.id in Hx by lia. apply HF. lia.
  Qed.

  #[local] Ltac grows := first [apply mem_grows_refl | eapply mem_grows_trans; [ | apply wbytes_grows ]; grows].
  #[local] Ltac fsok := apply out_agree_store_ok; [grows | cbn [Z.of_nat Pos.to_nat]; lia].
  #[local] Ltac oagree := repeat (apply out_agree_w; [|lia]); apply out_agree_refl.

  (* [comment removed for export] *)
  Definition M9 (rg : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem0
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr rg 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr rg 9)))
      (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr rg 18)))
      (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr rg 19)))
      (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr rg 20)))
      (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr rg 21)))
      (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (getr rg 22)).
  #[using="pd ps n fS lS fD lD Hs"] Lemma M9_out_agree : forall rg, out_agree (M9 rg).  Proof. hide_dj. intros rg. unfold M9. oagree. Qed.
  #[using="Type"] Lemma M9_grows : forall rg, mem_grows mem0 (M9 rg).  Proof. hide_dj. intros rg. unfold M9. grows. Qed.

  Definition slots_ok (regs0 : bvmap 5 word) (M : word -> option byte) : Prop :=
    rdn ASEGS M (Z_to_bv 64 (s - 8)) 8%nat = Some (word_to_le_bytes 8 ra) /\
    rdn ASEGS M (Z_to_bv 64 (s - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 8)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 9)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 18)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 19)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 48)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 20)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 56)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 21)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 64)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 22)).
  Definition FR (regs0 : bvmap 5 word) (M : word -> option byte) : Prop := out_agree M /\ mem_grows mem0 M /\ slots_ok regs0 M.

  #[local] Ltac peel :=
    rewrite rdn_wbytes_out;
      [ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | cbn [Z.of_nat Pos.to_nat]; unorm; lia
        | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia ].
  #[local] Ltac slot := repeat peel; apply rdn_wbytes_hit8; unorm; lia.
  #[using="pd ps n fS lS fD lD Hs"] Lemma M9_FR : forall regs0, FR regs0 (M9 regs0).
  Proof. hide_dj. intros regs0. split; [apply M9_out_agree | split; [apply M9_grows|]]. unfold M9. repeat split; slot. Qed.

  #[using="pd ps n fS lS fD lD Hs"] Lemma rdn_slot_ext : forall (M1 M2 : word -> option byte) k,
    (forall x : word, (s - 2144 <= bv_unsigned x < s)%Z -> M1 x = M2 x) -> (8 <= k <= 2144)%Z ->
    rdn ASEGS M1 (Z_to_bv 64 (s - k)) 8%nat = rdn ASEGS M2 (Z_to_bv 64 (s - k)) 8%nat.
  Proof.
    hide_dj.
    intros M1 M2 k HE Hk. apply rdn_ext; [unorm; cbn [Z.of_nat Pos.to_nat]; lia|].
    intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. apply HE. lia.
  Qed.
  #[using="pd ps n fS lS fD lD Hs"] Lemma slots_ok_ext : forall regs0 (M1 M2 : word -> option byte),
    (forall x : word, (s - 2144 <= bv_unsigned x < s)%Z -> M2 x = M1 x) -> slots_ok regs0 M1 -> slots_ok regs0 M2.
  Proof.
    hide_dj.
    intros regs0 M1 M2 HE (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8). unfold slots_ok.
    rewrite !(rdn_slot_ext M2 M1) by (first [exact HE | lia]). repeat split; assumption.
  Qed.
  #[using="pd ps n fS lS fD lD Hs"] Lemma FR_region : forall regs0 M M', FR regs0 M -> frame_only M (s - 2144) M' -> mem_grows M M' -> FR regs0 M'.
  Proof.
    hide_dj.
    intros regs0 M M' (O & G & R) HF HGr. split; [|split].
    - intros x Hx. rewrite (HF x) by lia. apply O. exact Hx.
    - eapply mem_grows_trans; [exact G | exact HGr].
    - apply (slots_ok_ext regs0 M M'); [|exact R]. intros x Hx. apply HF. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="pd ps fS lS fD lD HfS_def HlS_def HfaS_def HlaS_def HfD_def HlD_def Hn HappS Hs HshS HshD HWS"] Lemma rdnWS : forall M, out_agree M -> (0 < n <= 64)%Z -> exists w0 w1,
    rdn ASEGS M (Z_to_bv 64 faS) 8%nat = Some w0 /\ rdn ASEGS M (Z_to_bv 64 laS) 8%nat = Some w1
    /\ (0 <= bytes_le_to_Z w0 < 2 ^ 64)%Z /\ (0 <= bytes_le_to_Z w1 < 2 ^ 64)%Z.
  Proof.
    hide_dj.
    intros M HO Hn64. pose proof (flS_facts ltac:(lia)) as (F1 & F2 & F3 & F4). unfold SB in *.
    destruct (HWS Hn64) as (w0 & w1 & R0 & R1). exists w0, w1.
    rewrite !(out_agree_rdn M) by (first [exact HO | unorm; cbn [Z.of_nat Pos.to_nat]; lia]).
    split; [exact R0 | split; [exact R1 | split; [exact (bytes8_range _ _ _ _ R0) | exact (bytes8_range _ _ _ _ R1)]]].
  Qed.
  #[using="pd ps fS lS fD lD HfS_def HlS_def HfD_def HlD_def HfaD_def HlaD_def Hn HappD Hs HshS HshD HWD"] Lemma rdnWD : forall M, out_agree M -> (0 < n <= 64)%Z -> exists w0 w1,
    rdn ASEGS M (Z_to_bv 64 faD) 8%nat = Some w0 /\ rdn ASEGS M (Z_to_bv 64 laD) 8%nat = Some w1
    /\ (0 <= bytes_le_to_Z w0 < 2 ^ 64)%Z /\ (0 <= bytes_le_to_Z w1 < 2 ^ 64)%Z.
  Proof.
    hide_dj.
    intros M HO Hn64. pose proof (flD_facts ltac:(lia)) as (F1 & F2 & F3 & F4). unfold SB in *.
    destruct (HWD Hn64) as (w0 & w1 & R0 & R1). exists w0, w1.
    rewrite !(out_agree_rdn M) by (first [exact HO | unorm; cbn [Z.of_nat Pos.to_nat]; lia]).
    split; [exact R0 | split; [exact R1 | split; [exact (bytes8_range _ _ _ _ R0) | exact (bytes8_range _ _ _ _ R1)]]].
  Qed.
  #[using="pd ps faS laS fD lD HfS_def HlS_def HfaS_def HlaS_def HfD_def HlD_def Hn HappS Hs HshS HshD HZS"] Lemma rdn1S : forall M z, out_agree M -> (0 < n)%Z -> (fS <= z < lS)%Z -> rdn ASEGS M (Z_to_bv 64 z) 1%nat = Some [Z_to_bv 8 0].
  Proof.
    hide_dj.
    intros M z HO Hn0 Hz. pose proof (flS_facts ltac:(lia)) as (F1 & F2 & _). unfold SB in *.
    cbn [rdn]. rewrite HO by (unorm; lia). rewrite (HZS Hn0) by (unorm; lia). reflexivity.
  Qed.
  #[using="pd ps fS lS faD laD HfS_def HlS_def HfD_def HlD_def HfaD_def HlaD_def Hn HappD Hs HshD HZD"] Lemma rdn1D : forall M z, out_agree M -> (0 < n)%Z -> (fD <= z < lD)%Z -> rdn ASEGS M (Z_to_bv 64 z) 1%nat = Some [Z_to_bv 8 0].
  Proof.
    hide_dj.
    intros M z HO Hn0 Hz. pose proof (flD_facts ltac:(lia)) as (F1 & F2 & _). unfold SB in *.
    cbn [rdn]. rewrite HO by (unorm; lia). rewrite (HZD Hn0) by (unorm; lia). reflexivity.
  Qed.
  #[using="pd ps fS faS laS fD lD HfS_def HlS_def HfaS_def HlaS_def HfD_def HlD_def Hn HappS Hs HshS HLS"] Lemma rdnLS : forall M z, out_agree M -> (0 < n)%Z -> z = lS -> rdn ASEGS M (Z_to_bv 64 z) 1%nat = Some [Z_to_bv 8 kS].
  Proof.
    hide_dj.
    intros M z HO Hn0 ->. pose proof (flS_facts ltac:(lia)) as (F1 & F2 & _). unfold SB in *.
    cbn [rdn]. rewrite HO by (unorm; lia). rewrite (HLS Hn0). reflexivity.
  Qed.
  #[using="pd ps fS lS fD faD laD HfS_def HlS_def HfD_def HlD_def HfaD_def HlaD_def Hn HappD Hs HshD HLD"] Lemma rdnLD : forall M z, out_agree M -> (0 < n)%Z -> z = lD -> rdn ASEGS M (Z_to_bv 64 z) 1%nat = Some [Z_to_bv 8 kD].
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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition c1_post (rg : bvmap 5 word) : Prop :=
    getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 s
    /\ getr rg 2 = Z_to_bv 64 (s - 2144).

  #[using="fS lS fD lD Hs_def Hn HappS HappD Hs Hok HG HI"] Lemma c1_run : forall regs,
    getr regs 10 = Z_to_bv 64 pd -> getr regs 11 = Z_to_bv 64 ps -> getr regs 12 = Z_to_bv 64 n -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs',
      msteps ASEGS (mkst regs (0x78370 : word) mem0 rom) (mkst regs' (0x783ac : word) (M9 regs) rom)
      /\ c1_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros regs H10 H11 H12 H2 H1. rewrite sp_s in H2.
    pose proof pS_facts as (PSp & PSn & _). pose proof pD_facts as (PDp & PDn & _). unfold HIGHEND in *.
    pose proof (out_agree_globs (M9 regs) (M9_out_agree regs)) as (_ & (I1 & I2)).
    unfold M9 in *.
    eexists. split.
    - stepiv F_77f58 D_77f58 (Z_to_bv 64 (s - 2032)) ltac:(wval).                     (* [comment removed for export] *)
      stepsd F_77f5c D_77f5c (Z_to_bv 64 (s - 8)) ra ltac:(fsok).                        (* [comment removed for export] *)
      stepsd F_77f60 D_77f60 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(fsok).             (* [comment removed for export] *)
      stepsd F_77f64 D_77f64 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(fsok).             (* [comment removed for export] *)
      stepsd F_77f68 D_77f68 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(fsok).            (* [comment removed for export] *)
      stepsd F_77f6c D_77f6c (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(fsok).            (* [comment removed for export] *)
      stepsd F_77f70 D_77f70 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(fsok).            (* [comment removed for export] *)
      stepsd F_77f74 D_77f74 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(fsok).            (* [comment removed for export] *)
      stepsd F_77f78 D_77f78 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(fsok).            (* [comment removed for export] *)
      stepiv F_77f7c D_77f7c (Z_to_bv 64 s) ltac:(wval).                                  (* [comment removed for export] *)
      stepiv F_77f80 D_77f80 (Z_to_bv 64 (s - 2144)) ltac:(wval).                         (* [comment removed for export] *)
      stepn F_77f84 D_77f84.                                                               (* [comment removed for export] *)
      mld F_77f88 D_77f88 (0x138028 : word) I1.                                             (* [comment removed for export] *)
      mlbu F_77f8c D_77f8c (0x140919 : word) I2.                                            (* [comment removed for export] *)
      stepb_ft F_77f90 D_77f90 ltac:(cond).                                                (* [comment removed for export] *)
      apply mst_refl.
    - unfold c1_post. post.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition cR_pre (rg : bvmap 5 word) : Prop :=
    getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 s
    /\ getr rg 2 = Z_to_bv 64 (s - 2144).
  Definition cR_post (rg : bvmap 5 word) : Prop :=
    getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 s
    /\ getr rg 19 = Z_to_bv 64 (n - 65) /\ getr rg 2 = Z_to_bv 64 (s - 2144).

  (* [comment removed for export] *)
  #[using="fS lS fD lD Hn HappS HappD Hs"] Lemma cRz_run : forall M regs,
    cR_pre regs -> n = 0%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x783ac : word) M rom) (mkst regs' (0x78404 : word) M rom)
      /\ cR_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros M regs (H10 & H11 & H12 & H8 & H2) Hn0. pose proof pS_facts as (Pp & Ppn & Pp8 & Pq). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq). unfold HIGHEND in *.
    eexists. split.
    - stepiv F_77f94 D_77f94 (Z_to_bv 64 (2 ^ 64 - 1 - ps)) ltac:(xval).              (* [comment removed for export] *)
      stepiv F_77f98 D_77f98 (Z_to_bv 64 (s - 2048)) ltac:(wval).                                 (* [comment removed for export] *)
      stepiv F_77f9c D_77f9c (Z_to_bv 64 (s - 2136)) ltac:(wval).                                 (* [comment removed for export] *)
      stepb_ft F_77fa0 D_77fa0 ltac:(cond).                                            (* [comment removed for export] *)
      stepiv F_77fa4 D_77fa4 (Z_to_bv 64 (2 ^ 64 + n - 65)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; rewrite (zbv_wrap_up (n + - 65)); f_equal; lia).   (* [comment removed for export] *)
      stepn F_77fa8 D_77fa8.                                                               (* [comment removed for export] *)
      stepb_tk F_77fac D_77fac ltac:(cond).                                            (* [comment removed for export] *)
      stepb_ft F_780f0 D_780f0 ltac:(cond).                                              (* [comment removed for export] *)
      stepn F_780f4 D_780f4.                                                                 (* [comment removed for export] *)
      apply mst_refl.
    - unfold cR_post. post.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma ret_ok_781d0 : ret_ok (0x785e8 : word).  Proof. hide_dj. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
  #[using="kS fS lS faS laS fD lD faD laD HfS_def HlS_def HfD_def HlD_def Hn HappS HappD Hs HshS HshD Hok HG HI HZS HLS HkS HWS HWD"] Lemma cRr_run : forall regs0 M regs,
    cR_pre regs -> FR regs0 M -> (64 < n)%Z ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x783ac : word) M rom) (mkst regs' (0x78404 : word) M' rom)
      /\ cR_post regs' /\ keeps_but RIPL regs regs' /\ FR regs0 M'.
  Proof.
    hide_dj.
    intros regs0 M regs (H10 & H11 & H12 & H8 & H2) HFR Hn64. pose proof HFR as (HO & HGr & HR).
    pose proof pS_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq). unfold HIGHEND in *.
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x783ac : word) M rom) (mkst r1 (0x7b4c0 : word) M rom)
              /\ (getr r1 10 = Z_to_bv 64 ps /\ getr r1 11 = Z_to_bv 64 n /\ getr r1 2 = Z_to_bv 64 (s - 2144) /\ getr r1 1 = (0x785e8 : word)
                  /\ getr r1 21 = Z_to_bv 64 pd /\ getr r1 22 = Z_to_bv 64 ps /\ getr r1 9 = Z_to_bv 64 n /\ getr r1 8 = Z_to_bv 64 s /\ getr r1 19 = Z_to_bv 64 (n - 65) /\ keeps_but RIPL regs r1)).
    { eexists. split.
      - stepiv F_77f94 D_77f94 (Z_to_bv 64 (2 ^ 64 - 1 - ps)) ltac:(xval).
        stepiv F_77f98 D_77f98 (Z_to_bv 64 (s - 2048)) ltac:(wval).
        stepiv F_77f9c D_77f9c (Z_to_bv 64 (s - 2136)) ltac:(wval).
        stepb_ft F_77fa0 D_77fa0 ltac:(cond).
        stepiv F_77fa4 D_77fa4 (Z_to_bv 64 (n - 65)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; f_equal; lia).
        stepn F_77fa8 D_77fa8.
        stepb_tk F_77fac D_77fac ltac:(cond).                                          (* [comment removed for export] *)
        stepb_tk F_780f0 D_780f0 ltac:(cond).                                            (* [comment removed for export] *)
        stepiv F_781b8 D_781b8 (Z_to_bv 64 pd) ltac:(wval).                                (* [comment removed for export] *)
        stepiv F_781bc D_781bc (Z_to_bv 64 ps) ltac:(wval).                                (* [comment removed for export] *)
        stepiv F_781c0 D_781c0 (Z_to_bv 64 ps) ltac:(wval).                                (* [comment removed for export] *)
        stepiv F_781c4 D_781c4 (Z_to_bv 64 n) ltac:(wval).                                 (* [comment removed for export] *)
        stepiv F_781c8 D_781c8 (Z_to_bv 64 n) ltac:(wval).                                 (* [comment removed for export] *)
        stepn F_781cc D_781cc.                                                             (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q2 & Q1 & Q21 & Q22 & Q9 & Q8 & Q19 & K1).
    pose proof (out_agree_globs M HO) as (HGM & _).
    pose proof (region_is_poisoned_run M rom (Z_to_bv 64 (s - 2144)) (0x785e8 : word) ps n (s - 2144)
                  ltac:(unorm; reflexivity) ltac:(lia) HappS ltac:(lia) ltac:(unfold SB in *; lia)
                  ltac:(replace (s - 2144 - 72)%Z with (s - 2216)%Z by lia; apply out_agree_store_ok; [exact HGr | cbn; lia])
                  (ret_ok_781d0) HGM kS) as RP.
    specialize (RP ltac:(intros x Hx; rewrite (HO x) by (unfold SB in *; lia); apply HZS; [lia | unfold SB in *; lia])).
    specialize (RP ltac:(rewrite HO by (unfold SB in *; unorm; lia); rewrite <- HlS_def; apply HLS; lia) HkS).
    destruct (RP r1 Q10 Q11 Q2 Q1) as (r2 & M2 & RUN2 & V10 & V2 & V1 & K2 & F2 & G2).
    assert (S21 : getr r2 21 = Z_to_bv 64 pd) by (rewrite (K2 21%bv) by (cbv; tauto); exact Q21).
    assert (S22 : getr r2 22 = Z_to_bv 64 ps) by (rewrite (K2 22%bv) by (cbv; tauto); exact Q22).
    assert (S9 : getr r2 9 = Z_to_bv 64 n) by (rewrite (K2 9%bv) by (cbv; tauto); exact Q9).
    assert (S8 : getr r2 8 = Z_to_bv 64 s) by (rewrite (K2 8%bv) by (cbv; tauto); exact Q8).
    assert (S19 : getr r2 19 = Z_to_bv 64 (n - 65)) by (rewrite (K2 19%bv) by (cbv; tauto); exact Q19).
    eexists. exists M2. split; [|split; [|split; [|eapply FR_region; eassumption]]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
      stepiv F_781d0 D_781d0 (Z_to_bv 64 ps) ltac:(wval).                                  (* [comment removed for export] *)
      stepiv F_781d4 D_781d4 (Z_to_bv 64 n) ltac:(wval).                                   (* [comment removed for export] *)
      stepiv F_781d8 D_781d8 (Z_to_bv 64 0) ltac:(wval).                                   (* [comment removed for export] *)
      stepiv F_781dc D_781dc (Z_to_bv 64 pd) ltac:(wval).                                  (* [comment removed for export] *)
      stepb_tk F_781e0 D_781e0 ltac:(cond).                                          (* [comment removed for export] *)
      apply mst_refl.
    - unfold cR_post. post.
    - eapply keeps_but_trans; [exact K1|]. solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  Definition cRqa_post (u0 u1 : Z) (rg : bvmap 5 word) : Prop :=
    getr rg 13 = Z_to_bv 64 fS /\ getr rg 14 = Z_to_bv 64 lS /\ getr rg 15 = Z_to_bv 64 (ps + n - 1) /\ getr rg 16 = Z_to_bv 64 (Z.lor u1 u0)
    /\ getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 s
    /\ getr rg 19 = Z_to_bv 64 (n - 65) /\ getr rg 2 = Z_to_bv 64 (s - 2144).
  #[using="fD lD HfS_def HlS_def HfaS_def HlaS_def HfD_def HlD_def Hn HappS HappD Hs HshS HG HI"] Lemma cRqa_run : forall M regs w0 w1,
    cR_pre regs -> out_agree M -> (0 < n <= 64)%Z ->
    rdn ASEGS M (Z_to_bv 64 faS) 8%nat = Some w0 -> rdn ASEGS M (Z_to_bv 64 laS) 8%nat = Some w1 ->
    (0 <= bytes_le_to_Z w0 < 2 ^ 64)%Z -> (0 <= bytes_le_to_Z w1 < 2 ^ 64)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x783ac : word) M rom) (mkst regs' (0x78400 : word) M rom)
      /\ cRqa_post (bytes_le_to_Z w0) (bytes_le_to_Z w1) regs' /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros M regs w0 w1 (H10 & H11 & H12 & H8 & H2) HO Hn64 R0 R1 B0 B1.
    pose proof pS_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq).
    pose proof (flS_facts ltac:(lia)) as (F1 & F2 & F3 & F4).
    pose proof (out_agree_globs M HO) as ((G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8) & _).
    unfold SB, HIGHEND in *.
    pose proof (Z.div_mod ps 8 ltac:(lia)) as Dp. pose proof (Z.mod_pos_bound ps 8 ltac:(lia)) as Mp.
    pose proof (Z.mod_pos_bound fS 8 ltac:(lia)) as Mf. pose proof (Z.mod_pos_bound lS 8 ltac:(lia)) as Ml.
    pose proof (lor_bound64 (bytes_le_to_Z w1) (bytes_le_to_Z w0) B1 B0) as BL.
    eexists. split.
    - stepiv F_77f94 D_77f94 (Z_to_bv 64 (2 ^ 64 - 1 - ps)) ltac:(xval).
      stepiv F_77f98 D_77f98 (Z_to_bv 64 (s - 2048)) ltac:(wval).                                 (* [comment removed for export] *)
      stepiv F_77f9c D_77f9c (Z_to_bv 64 (s - 2136)) ltac:(wval).                                 (* [comment removed for export] *)
      stepb_ft F_77fa0 D_77fa0 ltac:(cond).
      stepiv F_77fa4 D_77fa4 (Z_to_bv 64 (2 ^ 64 + n - 65)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; rewrite (zbv_wrap_up (n + - 65)); f_equal; lia).
      stepn F_77fa8 D_77fa8.
      stepb_ft F_77fac D_77fac ltac:(cond).                                            (* [comment removed for export] *)
      stepn F_77fb0 D_77fb0.                                                         (* [comment removed for export] *)
      mld F_77fb4 D_77fb4 (0x1374c0 : word) G1.                                       (* [comment removed for export] *)
      stepiv F_77fb8 D_77fb8 (Z_to_bv 64 (ps + n)) ltac:(wval).                         (* [comment removed for export] *)
      mld F_77fbc D_77fbc (0x13fc38 : word) G2.                                           (* [comment removed for export] *)
      stepiv F_77fc0 D_77fc0 (Z_to_bv 64 (ps / 8)) ltac:(wval).                         (* [comment removed for export] *)
      stepiv F_77fc4 D_77fc4 (Z_to_bv 64 (ps + n - 1)) ltac:(wval).                     (* [comment removed for export] *)
      stepiv F_77fc8 D_77fc8 (Z_to_bv 64 ((ps + n - 1) / 8)) ltac:(wval).               (* [comment removed for export] *)
      stepiv F_77fcc D_77fcc (Z_to_bv 64 fS) ltac:(wval).                               (* [comment removed for export] *)
      stepiv F_77fd0 D_77fd0 (Z_to_bv 64 lS) ltac:(wval).                               (* [comment removed for export] *)
      stepiv F_77fd4 D_77fd4 (Z_to_bv 64 faS)
        ltac:(gres; rwH; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; f_equal; lia).
      stepiv F_77fd8 D_77fd8 (Z_to_bv 64 laS)
        ltac:(gres; rwH; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; f_equal; lia).
      mldw F_77fdc D_77fdc faS R0 w0.                                                    (* [comment removed for export] *)
      mldw F_77fe0 D_77fe0 laS R1 w1.                                                    (* [comment removed for export] *)
      stepov F_77fe4 D_77fe4 (Z_to_bv 64 (Z.lor (bytes_le_to_Z w1) (bytes_le_to_Z w0))) ltac:(gres; rwH; unfold v_or; unorm; reflexivity).
      apply mst_refl.
    - unfold cRqa_post. split; [post | solve_keeps_but].
  Qed.

  (* [comment removed for export] *)
  Definition qlR_inv (rg : bvmap 5 word) (i : Z) : Prop :=
    getr rg 13 = Z_to_bv 64 (fS + i) /\ getr rg 14 = Z_to_bv 64 lS /\ getr rg 15 = Z_to_bv 64 0 /\ getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 s
    /\ getr rg 19 = Z_to_bv 64 (n - 65) /\ getr rg 2 = Z_to_bv 64 (s - 2144).
  Definition qlR_post (rg : bvmap 5 word) : Prop :=
    getr rg 15 = Z_to_bv 64 0 /\ getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 s
    /\ getr rg 19 = Z_to_bv 64 (n - 65) /\ getr rg 2 = Z_to_bv 64 (s - 2144).
  #[using="faS laS fD lD HfS_def HlS_def HfaS_def HlaS_def HfD_def HlD_def Hn HappS Hs HshS HshD HZS"] Lemma qloopR_run : forall M (q : nat) regs i,
    out_agree M -> (0 < n)%Z -> qlR_inv regs i -> (0 <= i)%Z -> (fS + i + Z.of_nat q + 1 = lS)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x785b8 : word) M rom) (mkst regs' (0x785c8 : word) M rom)
      /\ qlR_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros M q. induction q as [|q IH]; intros regs i HO Hn0 (H13 & H14 & H15 & H10 & H11 & H12 & H8 & H19 & H2) Hi Hq; 
      pose proof (flS_facts Hn0) as (F1 & F2 & _); unfold SB in *.
    - eexists. split.
      + mlbu0 F_781a0 D_781a0 (fS + i)%Z rdn1S.                                      (* [comment removed for export] *)
        stepiv F_781a4 D_781a4 (Z_to_bv 64 (fS + i + 1)) ltac:(wval).                (* [comment removed for export] *)
        stepov F_781a8 D_781a8 (Z_to_bv 64 0) ltac:(vlit).                            (* [comment removed for export] *)
        stepb_ft F_781ac D_781ac ltac:(cond).                                        (* [comment removed for export] *)
        apply mst_refl.
      + unfold qlR_post. post.
    - eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x785b8 : word) M rom) (fun rg => qlR_inv rg (i + 1) /\ keeps_but RIPL regs rg)).
      + eexists. split.
        * mlbu0 F_781a0 D_781a0 (fS + i)%Z rdn1S.
          stepiv F_781a4 D_781a4 (Z_to_bv 64 (fS + i + 1)) ltac:(wval).
          stepov F_781a8 D_781a8 (Z_to_bv 64 0) ltac:(vlit).
          stepb_tk F_781ac D_781ac ltac:(cond).                                      (* [comment removed for export] *)
          apply mst_refl.
        * unfold qlR_inv. post.
      + cbv beta. intros r1 (I1 & K1).
        destruct (IH r1 (i + 1)%Z HO Hn0 I1 ltac:(lia) ltac:(lia)) as (r2 & RUN & P2 & K2).
        exists r2. split; [exact RUN | split; [exact P2 | eapply keeps_but_trans; eassumption]].
  Qed.

  (* [comment removed for export] *)
  #[using="fD lD"] Lemma cRqf_run : forall M regs u0 u1,
    cRqa_post u0 u1 regs -> (0 <= Z.lor u1 u0 < 2 ^ 64)%Z -> Z.lor u1 u0 = 0%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x78400 : word) M rom) (mkst regs' (0x78404 : word) M rom)
      /\ cR_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros M regs u0 u1 (H13 & H14 & HL' & H15 & H10 & H11 & H12 & H8 & H19 & H2) BL E.
    eexists. split.
    - stepb_ft F_77fe8 D_77fe8 ltac:(cond).                                           (* [comment removed for export] *)
      apply mst_refl.
    - unfold cR_post. post.
  Qed.

  (* [comment removed for export] *)
  #[using="kS faS laS fD lD HfS_def HlS_def HfaS_def HlaS_def HfD_def HlD_def Hn HappS HappD Hs HshS HshD HZS HLS HkS"] Lemma cRqs_run : forall M regs u0 u1,
    cRqa_post u0 u1 regs -> out_agree M -> (0 < n <= 64)%Z -> (0 <= Z.lor u1 u0 < 2 ^ 64)%Z -> Z.lor u1 u0 <> 0%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x78400 : word) M rom) (mkst regs' (0x78404 : word) M rom)
      /\ cR_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros M regs u0 u1 (H13 & H14 & HL' & H15 & H10 & H11 & H12 & H8 & H19 & H2) HO Hn64 BL NE.
    pose proof pS_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq).
    pose proof (flS_facts ltac:(lia)) as (F1 & F2 & F3 & F4). unfold SB, HIGHEND in *.
    pose proof (Z.mod_pos_bound (ps + n - 1) 8 ltac:(lia)) as Mq.
    eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x785b4 : word) M rom) (fun rg => qlR_inv rg 0 /\ keeps_but RIPL regs rg)).
    { unhide HkS. destruct HkS as [K0|K7].
      - eexists. split.
        + stepb_tk F_77fe8 D_77fe8 ltac:(cond).                                       (* [comment removed for export] *)
          mlbk F_78184 D_78184 lS rdnLS kS.                                             (* [comment removed for export] *)
          stepiv F_78188 D_78188 (Z_to_bv 64 ((ps + n - 1) mod 8))
            ltac:(gres; rwH; unfold v_andi; imm_norm; unorm; rewrite land7_mod8; reflexivity). (* [comment removed for export] *)
          stepov F_7818c D_7818c (Z_to_bv 64 0)
            ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (0 <? kS)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
          stepov F_78190 D_78190 (Z_to_bv 64 0)
            ltac:(gres; rwH; unfold v_slt, c_lts, bv_lts; rewrite !signed64_small by lia;
                  replace ((ps + n - 1) mod 8 <? kS)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
          stepiv F_78194 D_78194 (Z_to_bv 64 1) ltac:(vlit).
          stepov F_78198 D_78198 (Z_to_bv 64 0) ltac:(vlit).
          apply mst_refl.
        + unfold qlR_inv. post.
      - eexists. split.
        + stepb_tk F_77fe8 D_77fe8 ltac:(cond).
          mlbk F_78184 D_78184 lS rdnLS kS.
          stepiv F_78188 D_78188 (Z_to_bv 64 ((ps + n - 1) mod 8))
            ltac:(gres; rwH; unfold v_andi; imm_norm; unorm; rewrite land7_mod8; reflexivity).
          stepov F_7818c D_7818c (Z_to_bv 64 1)
            ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (0 <? kS)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
          stepov F_78190 D_78190 (Z_to_bv 64 1)
            ltac:(gres; rwH; unfold v_slt, c_lts, bv_lts; rewrite !signed64_small by lia;
                  replace ((ps + n - 1) mod 8 <? kS)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
          stepiv F_78194 D_78194 (Z_to_bv 64 0) ltac:(vlit).
          stepov F_78198 D_78198 (Z_to_bv 64 0) ltac:(vlit).
          apply mst_refl.
        + unfold qlR_inv. post. }
    cbv beta. intros r1 ((I13 & I14 & I15 & I10 & I11 & I12 & I8 & I19 & I2) & K1).
    eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x785c8 : word) M rom) (fun rg => qlR_post rg /\ keeps_but RIPL regs rg)).
    { destruct (Z.lt_ge_cases fS lS) as [Hfl|Hfl].
      - eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x785b8 : word) M rom) (fun rg => qlR_inv rg 0 /\ keeps_but RIPL regs rg)).
        + eexists. split.
          * stepb_ft F_7819c D_7819c ltac:(cond).                                   (* [comment removed for export] *)
            apply mst_refl.
          * split; [unfold qlR_inv; repeat split; assumption | exact K1].
        + cbv beta. intros r2 (I2' & K2).
          destruct (qloopR_run M (Z.to_nat (lS - fS - 1)) r2 0 HO ltac:(lia) I2' ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (r3 & RUN3 & P3 & K3).
          exists r3. split; [exact RUN3 | split; [exact P3 | eapply keeps_but_trans; eassumption]].
      - eexists. split.
        + stepb_tk F_7819c D_7819c ltac:(cond).                                     (* [comment removed for export] *)
          apply mst_refl.
        + split; [unfold qlR_post; repeat split; assumption | exact K1]. }
    cbv beta. intros r4 ((J15 & J10 & J11 & J12 & J8 & J19 & J2) & K4).
    eexists. split.
    - stepiv F_781b0 D_781b0 (Z_to_bv 64 0) ltac:(vlit).                             (* [comment removed for export] *)
      stepb_tk F_781b4 D_781b4 ltac:(cond).                                           (* [comment removed for export] *)
      apply mst_refl.
    - unfold cR_post. split; [post|]. eapply keeps_but_trans; [exact K4|]. solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  #[using="kS fS lS faS laS fD lD faD laD HfS_def HlS_def HfaS_def HlaS_def HfD_def HlD_def Hn HappS HappD Hs HshS HshD Hok HG HI HZS HLS HkS HWS HWD"] Lemma cR_run : forall regs0 M regs,
    cR_pre regs -> FR regs0 M ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x783ac : word) M rom) (mkst regs' (0x78404 : word) M' rom)
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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition cW_pre (rg : bvmap 5 word) : Prop :=
    getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 s
    /\ getr rg 19 = Z_to_bv 64 (n - 65) /\ getr rg 2 = Z_to_bv 64 (s - 2144).
  Definition cW_post (rg : bvmap 5 word) : Prop :=
    getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 2 = Z_to_bv 64 (s - 2144).

  (* [comment removed for export] *)
  #[using="fS lS fD lD Hn HappS HappD"] Lemma cWz_run : forall M regs,
    cW_pre regs -> n = 0%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x78404 : word) M rom) (mkst regs' (0x78450 : word) M rom)
      /\ cW_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros M regs (H10 & H11 & H12 & H8 & H19 & H2) Hn0. pose proof pD_facts as (Pp & Ppn & Pp8 & Pq). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq). unfold HIGHEND in *.
    rewrite (zbv_wrap_up (n - 65)) in H19.
    eexists. split.
    - stepiv F_77fec D_77fec (Z_to_bv 64 (2 ^ 64 - 1 - pd)) ltac:(xval).              (* [comment removed for export] *)
      stepb_ft F_77ff0 D_77ff0 ltac:(cond).                                            (* [comment removed for export] *)
      stepn F_77ff4 D_77ff4.                                                               (* [comment removed for export] *)
      stepb_tk F_77ff8 D_77ff8 ltac:(cond).                                            (* [comment removed for export] *)
      stepb_ft F_7817c D_7817c ltac:(cond).                                              (* [comment removed for export] *)
      stepn F_78180 D_78180.                                                                 (* [comment removed for export] *)
      apply mst_refl.
    - unfold cW_post. post.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma ret_ok_78270 : ret_ok (0x78688 : word).  Proof. hide_dj. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
  #[using="fS lS faS laS kD fD lD faD laD HfS_def HlS_def HfD_def HlD_def Hn HappS HappD Hs HshS HshD Hok HG HI HWS HZD HLD HkD HWD"] Lemma cWr_run : forall regs0 M regs,
    cW_pre regs -> FR regs0 M -> (64 < n)%Z ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x78404 : word) M rom) (mkst regs' (0x78450 : word) M' rom)
      /\ cW_post regs' /\ keeps_but RIPL regs regs' /\ FR regs0 M'.
  Proof.
    hide_dj.
    intros regs0 M regs (H10 & H11 & H12 & H8 & H19 & H2) HFR Hn64. pose proof HFR as (HO & HGr & HR).
    pose proof pD_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq). unfold HIGHEND in *.
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x78404 : word) M rom) (mkst r1 (0x7b4c0 : word) M rom)
              /\ (getr r1 10 = Z_to_bv 64 pd /\ getr r1 11 = Z_to_bv 64 n /\ getr r1 2 = Z_to_bv 64 (s - 2144) /\ getr r1 1 = (0x78688 : word)
                  /\ getr r1 9 = Z_to_bv 64 pd /\ getr r1 21 = Z_to_bv 64 ps /\ getr r1 18 = Z_to_bv 64 n /\ keeps_but RIPL regs r1)).
    { eexists. split.
      - stepiv F_77fec D_77fec (Z_to_bv 64 (2 ^ 64 - 1 - pd)) ltac:(xval).
        stepb_ft F_77ff0 D_77ff0 ltac:(cond).
        stepn F_77ff4 D_77ff4.
        stepb_tk F_77ff8 D_77ff8 ltac:(cond).                                          (* [comment removed for export] *)
        stepb_tk F_7817c D_7817c ltac:(cond).                                            (* [comment removed for export] *)
        stepiv F_7825c D_7825c (Z_to_bv 64 pd) ltac:(wval).                                (* [comment removed for export] *)
        stepiv F_78260 D_78260 (Z_to_bv 64 ps) ltac:(wval).                                (* [comment removed for export] *)
        stepiv F_78264 D_78264 (Z_to_bv 64 n) ltac:(wval).                                 (* [comment removed for export] *)
        stepiv F_78268 D_78268 (Z_to_bv 64 n) ltac:(wval).                                 (* [comment removed for export] *)
        stepn F_7826c D_7826c.                                                             (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q2 & Q1 & Q9 & Q21 & Q18 & K1).
    pose proof (out_agree_globs M HO) as (HGM & _).
    pose proof (region_is_poisoned_run M rom (Z_to_bv 64 (s - 2144)) (0x78688 : word) pd n (s - 2144)
                  ltac:(unorm; reflexivity) ltac:(lia) HappD ltac:(lia) ltac:(unfold SB in *; lia)
                  ltac:(replace (s - 2144 - 72)%Z with (s - 2216)%Z by lia; apply out_agree_store_ok; [exact HGr | cbn; lia])
                  (ret_ok_78270) HGM kD) as RP.
    specialize (RP ltac:(intros x Hx; rewrite (HO x) by (unfold SB in *; lia); apply HZD; [lia | unfold SB in *; lia])).
    specialize (RP ltac:(rewrite HO by (unfold SB in *; unorm; lia); rewrite <- HlD_def; apply HLD; lia) HkD).
    destruct (RP r1 Q10 Q11 Q2 Q1) as (r2 & M2 & RUN2 & V10 & V2 & V1 & K2 & F2 & G2).
    assert (S9 : getr r2 9 = Z_to_bv 64 pd) by (rewrite (K2 9%bv) by (cbv; tauto); exact Q9).
    assert (S21 : getr r2 21 = Z_to_bv 64 ps) by (rewrite (K2 21%bv) by (cbv; tauto); exact Q21).
    assert (S18 : getr r2 18 = Z_to_bv 64 n) by (rewrite (K2 18%bv) by (cbv; tauto); exact Q18).
    eexists. exists M2. split; [|split; [|split; [|eapply FR_region; eassumption]]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
      stepiv F_78270 D_78270 (Z_to_bv 64 ps) ltac:(wval).                                  (* [comment removed for export] *)
      stepiv F_78274 D_78274 (Z_to_bv 64 n) ltac:(wval).                                   (* [comment removed for export] *)
      stepiv F_78278 D_78278 (Z_to_bv 64 0) ltac:(wval).                                   (* [comment removed for export] *)
      stepiv F_7827c D_7827c (Z_to_bv 64 pd) ltac:(wval).                                  (* [comment removed for export] *)
      stepb_tk F_78280 D_78280 ltac:(cond).                                          (* [comment removed for export] *)
      apply mst_refl.
    - unfold cW_post. post.
    - eapply keeps_but_trans; [exact K1|]. solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  Definition cWqa_post (u0 u1 : Z) (rg : bvmap 5 word) : Prop :=
    getr rg 13 = Z_to_bv 64 fD /\ getr rg 14 = Z_to_bv 64 lD /\ getr rg 15 = Z_to_bv 64 (pd + n - 1) /\ getr rg 16 = Z_to_bv 64 (Z.lor u1 u0)
    /\ getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 2 = Z_to_bv 64 (s - 2144).
  #[using="fS lS HfS_def HlS_def HfD_def HlD_def HfaD_def HlaD_def Hn HappS HappD Hs HshD HG HI"] Lemma cWqa_run : forall M regs w0 w1,
    cW_pre regs -> out_agree M -> (0 < n <= 64)%Z ->
    rdn ASEGS M (Z_to_bv 64 faD) 8%nat = Some w0 -> rdn ASEGS M (Z_to_bv 64 laD) 8%nat = Some w1 ->
    (0 <= bytes_le_to_Z w0 < 2 ^ 64)%Z -> (0 <= bytes_le_to_Z w1 < 2 ^ 64)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x78404 : word) M rom) (mkst regs' (0x7844c : word) M rom)
      /\ cWqa_post (bytes_le_to_Z w0) (bytes_le_to_Z w1) regs' /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros M regs w0 w1 (H10 & H11 & H12 & H8 & H19 & H2) HO Hn64 R0 R1 B0 B1.
    rewrite (zbv_wrap_up (n - 65)) in H19.
    pose proof pD_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq).
    pose proof (flD_facts ltac:(lia)) as (F1 & F2 & F3 & F4).
    pose proof (out_agree_globs M HO) as ((G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8) & _).
    unfold SB, HIGHEND in *.
    pose proof (Z.div_mod pd 8 ltac:(lia)) as Dp. pose proof (Z.mod_pos_bound pd 8 ltac:(lia)) as Mp.
    pose proof (Z.mod_pos_bound fD 8 ltac:(lia)) as Mf. pose proof (Z.mod_pos_bound lD 8 ltac:(lia)) as Ml.
    pose proof (lor_bound64 (bytes_le_to_Z w1) (bytes_le_to_Z w0) B1 B0) as BL.
    eexists. split.
    - stepiv F_77fec D_77fec (Z_to_bv 64 (2 ^ 64 - 1 - pd)) ltac:(xval).
      stepb_ft F_77ff0 D_77ff0 ltac:(cond).
      stepn F_77ff4 D_77ff4.
      stepb_ft F_77ff8 D_77ff8 ltac:(cond).                                            (* [comment removed for export] *)
      stepn F_77ffc D_77ffc.                                                         (* [comment removed for export] *)
      mld F_78000 D_78000 (0x1374c0 : word) G1.                                       (* [comment removed for export] *)
      stepiv F_78004 D_78004 (Z_to_bv 64 (pd + n)) ltac:(wval).                         (* [comment removed for export] *)
      mld F_78008 D_78008 (0x13fc38 : word) G2.                                           (* [comment removed for export] *)
      stepiv F_7800c D_7800c (Z_to_bv 64 (pd / 8)) ltac:(wval).                         (* [comment removed for export] *)
      stepiv F_78010 D_78010 (Z_to_bv 64 (pd + n - 1)) ltac:(wval).                     (* [comment removed for export] *)
      stepiv F_78014 D_78014 (Z_to_bv 64 ((pd + n - 1) / 8)) ltac:(wval).               (* [comment removed for export] *)
      stepiv F_78018 D_78018 (Z_to_bv 64 fD) ltac:(wval).                               (* [comment removed for export] *)
      stepiv F_7801c D_7801c (Z_to_bv 64 lD) ltac:(wval).                               (* [comment removed for export] *)
      stepiv F_78020 D_78020 (Z_to_bv 64 faD)
        ltac:(gres; rwH; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; f_equal; lia).
      stepiv F_78024 D_78024 (Z_to_bv 64 laD)
        ltac:(gres; rwH; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; f_equal; lia).
      mldw F_78028 D_78028 faD R0 w0.                                                    (* [comment removed for export] *)
      mldw F_7802c D_7802c laD R1 w1.                                                    (* [comment removed for export] *)
      stepov F_78030 D_78030 (Z_to_bv 64 (Z.lor (bytes_le_to_Z w1) (bytes_le_to_Z w0))) ltac:(gres; rwH; unfold v_or; unorm; reflexivity).
      apply mst_refl.
    - unfold cWqa_post. split; [post | solve_keeps_but].
  Qed.

  (* [comment removed for export] *)
  Definition qlW_inv (rg : bvmap 5 word) (i : Z) : Prop :=
    getr rg 13 = Z_to_bv 64 (fD + i) /\ getr rg 14 = Z_to_bv 64 lD /\ getr rg 15 = Z_to_bv 64 0 /\ getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 2 = Z_to_bv 64 (s - 2144).
  Definition qlW_post (rg : bvmap 5 word) : Prop :=
    getr rg 15 = Z_to_bv 64 0 /\ getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 2 = Z_to_bv 64 (s - 2144).
  #[using="fS lS faD laD HfS_def HlS_def HfD_def HlD_def HfaD_def HlaD_def Hn HappD Hs HshD HZD"] Lemma qloopW_run : forall M (q : nat) regs i,
    out_agree M -> (0 < n)%Z -> qlW_inv regs i -> (0 <= i)%Z -> (fD + i + Z.of_nat q + 1 = lD)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x7865c : word) M rom) (mkst regs' (0x7866c : word) M rom)
      /\ qlW_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros M q. induction q as [|q IH]; intros regs i HO Hn0 (H13 & H14 & H15 & H10 & H11 & H12 & H2) Hi Hq; 
      pose proof (flD_facts Hn0) as (F1 & F2 & _); unfold SB in *.
    - eexists. split.
      + mlbu0 F_78244 D_78244 (fD + i)%Z rdn1D.                                      (* [comment removed for export] *)
        stepiv F_78248 D_78248 (Z_to_bv 64 (fD + i + 1)) ltac:(wval).                (* [comment removed for export] *)
        stepov F_7824c D_7824c (Z_to_bv 64 0) ltac:(vlit).                            (* [comment removed for export] *)
        stepb_ft F_78250 D_78250 ltac:(cond).                                        (* [comment removed for export] *)
        apply mst_refl.
      + unfold qlW_post. post.
    - eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x7865c : word) M rom) (fun rg => qlW_inv rg (i + 1) /\ keeps_but RIPL regs rg)).
      + eexists. split.
        * mlbu0 F_78244 D_78244 (fD + i)%Z rdn1D.
          stepiv F_78248 D_78248 (Z_to_bv 64 (fD + i + 1)) ltac:(wval).
          stepov F_7824c D_7824c (Z_to_bv 64 0) ltac:(vlit).
          stepb_tk F_78250 D_78250 ltac:(cond).                                      (* [comment removed for export] *)
          apply mst_refl.
        * unfold qlW_inv. post.
      + cbv beta. intros r1 (I1 & K1).
        destruct (IH r1 (i + 1)%Z HO Hn0 I1 ltac:(lia) ltac:(lia)) as (r2 & RUN & P2 & K2).
        exists r2. split; [exact RUN | split; [exact P2 | eapply keeps_but_trans; eassumption]].
  Qed.

  (* [comment removed for export] *)
  #[using="fS lS"] Lemma cWqf_run : forall M regs u0 u1,
    cWqa_post u0 u1 regs -> (0 <= Z.lor u1 u0 < 2 ^ 64)%Z -> Z.lor u1 u0 = 0%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x7844c : word) M rom) (mkst regs' (0x78450 : word) M rom)
      /\ cW_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros M regs u0 u1 (H13 & H14 & HL' & H15 & H10 & H11 & H12 & H2) BL E.
    eexists. split.
    - stepb_ft F_78034 D_78034 ltac:(cond).                                           (* [comment removed for export] *)
      apply mst_refl.
    - unfold cW_post. post.
  Qed.

  (* [comment removed for export] *)
  #[using="fS lS kD faD laD HfS_def HlS_def HfD_def HlD_def HfaD_def HlaD_def Hn HappS HappD Hs HshD HZD HLD HkD"] Lemma cWqs_run : forall M regs u0 u1,
    cWqa_post u0 u1 regs -> out_agree M -> (0 < n <= 64)%Z -> (0 <= Z.lor u1 u0 < 2 ^ 64)%Z -> Z.lor u1 u0 <> 0%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x7844c : word) M rom) (mkst regs' (0x78450 : word) M rom)
      /\ cW_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros M regs u0 u1 (H13 & H14 & HL' & H15 & H10 & H11 & H12 & H2) HO Hn64 BL NE.
    pose proof pD_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq).
    pose proof (flD_facts ltac:(lia)) as (F1 & F2 & F3 & F4). unfold SB, HIGHEND in *.
    pose proof (Z.mod_pos_bound (pd + n - 1) 8 ltac:(lia)) as Mq.
    eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x78658 : word) M rom) (fun rg => qlW_inv rg 0 /\ keeps_but RIPL regs rg)).
    { unhide HkD. destruct HkD as [K0|K7].
      - eexists. split.
        + stepb_tk F_78034 D_78034 ltac:(cond).                                       (* [comment removed for export] *)
          mlbk F_78228 D_78228 lD rdnLD kD.                                             (* [comment removed for export] *)
          stepiv F_7822c D_7822c (Z_to_bv 64 ((pd + n - 1) mod 8))
            ltac:(gres; rwH; unfold v_andi; imm_norm; unorm; rewrite land7_mod8; reflexivity). (* [comment removed for export] *)
          stepov F_78230 D_78230 (Z_to_bv 64 0)
            ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (0 <? kD)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
          stepov F_78234 D_78234 (Z_to_bv 64 0)
            ltac:(gres; rwH; unfold v_slt, c_lts, bv_lts; rewrite !signed64_small by lia;
                  replace ((pd + n - 1) mod 8 <? kD)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
          stepiv F_78238 D_78238 (Z_to_bv 64 1) ltac:(vlit).
          stepov F_7823c D_7823c (Z_to_bv 64 0) ltac:(vlit).
          apply mst_refl.
        + unfold qlW_inv. post.
      - eexists. split.
        + stepb_tk F_78034 D_78034 ltac:(cond).
          mlbk F_78228 D_78228 lD rdnLD kD.
          stepiv F_7822c D_7822c (Z_to_bv 64 ((pd + n - 1) mod 8))
            ltac:(gres; rwH; unfold v_andi; imm_norm; unorm; rewrite land7_mod8; reflexivity).
          stepov F_78230 D_78230 (Z_to_bv 64 1)
            ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (0 <? kD)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
          stepov F_78234 D_78234 (Z_to_bv 64 1)
            ltac:(gres; rwH; unfold v_slt, c_lts, bv_lts; rewrite !signed64_small by lia;
                  replace ((pd + n - 1) mod 8 <? kD)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
          stepiv F_78238 D_78238 (Z_to_bv 64 0) ltac:(vlit).
          stepov F_7823c D_7823c (Z_to_bv 64 0) ltac:(vlit).
          apply mst_refl.
        + unfold qlW_inv. post. }
    cbv beta. intros r1 ((I13 & I14 & I15 & I10 & I11 & I12 & I2) & K1).
    eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x7866c : word) M rom) (fun rg => qlW_post rg /\ keeps_but RIPL regs rg)).
    { destruct (Z.lt_ge_cases fD lD) as [Hfl|Hfl].
      - eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x7865c : word) M rom) (fun rg => qlW_inv rg 0 /\ keeps_but RIPL regs rg)).
        + eexists. split.
          * stepb_ft F_78240 D_78240 ltac:(cond).                                   (* [comment removed for export] *)
            apply mst_refl.
          * split; [unfold qlW_inv; repeat split; assumption | exact K1].
        + cbv beta. intros r2 (I2' & K2).
          destruct (qloopW_run M (Z.to_nat (lD - fD - 1)) r2 0 HO ltac:(lia) I2' ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (r3 & RUN3 & P3 & K3).
          exists r3. split; [exact RUN3 | split; [exact P3 | eapply keeps_but_trans; eassumption]].
      - eexists. split.
        + stepb_tk F_78240 D_78240 ltac:(cond).                                     (* [comment removed for export] *)
          apply mst_refl.
        + split; [unfold qlW_post; repeat split; assumption | exact K1]. }
    cbv beta. intros r4 ((J15 & J10 & J11 & J12 & J2) & K4).
    eexists. split.
    - stepiv F_78254 D_78254 (Z_to_bv 64 0) ltac:(vlit).                             (* [comment removed for export] *)
      stepb_tk F_78258 D_78258 ltac:(cond).                                           (* [comment removed for export] *)
      apply mst_refl.
    - unfold cW_post. split; [post|]. eapply keeps_but_trans; [exact K4|]. solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  #[using="fS lS faS laS kD fD lD faD laD HfS_def HlS_def HfD_def HlD_def HfaD_def HlaD_def Hn HappS HappD Hs HshS HshD Hok HG HI HWS HZD HLD HkD HWD"] Lemma cW_run : forall regs0 M regs,
    cW_pre regs -> FR regs0 M ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x78404 : word) M rom) (mkst regs' (0x78450 : word) M' rom)
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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma ret_ok_7803c : ret_ok (0x78454 : word).  Proof. hide_dj. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

  #[local] Notation MMR M := (mm_result M (Z_to_bv 64 pd) (Z_to_bv 64 ps) bs) (only parsing).

  #[using="fS lS fD lD Hn HappS HappD Hs HdjS Hover Hdst Hsrc"] Lemma mcH_M : forall M, out_agree M -> mem_grows mem0 M -> mcH M (Z_to_bv 64 pd) (Z_to_bv 64 ps) n bs.
  Proof.
    hide_dj.
    intros M HO HGr. pose proof pS_facts as (PSp & PSn & _). pose proof pD_facts as (PDp & PDn & _). unfold HIGHEND in *.
    pose proof (rdn_length _ _ _ _ _ Hsrc) as LEN. unhide Hover.
    constructor.
    - lia.
    - exact LEN.
    - rewrite LEN. apply out_agree_src. exact HO.
    - rewrite LEN. apply (store_ok_mono _ _ mem0 M _ HGr). exact Hdst.
    - unorm. lia.
    - unorm. lia.
    - unorm. lia.
  Qed.

  #[using="mem0 fS lS fD lD Hn HappD Hs HdjD Hsrc"] Lemma slots_ok_mm : forall regs0 M (MC : mcH M (Z_to_bv 64 pd) (Z_to_bv 64 ps) n bs), slots_ok regs0 M ->
    slots_ok regs0 (mm_result M (Z_to_bv 64 pd) (Z_to_bv 64 ps) bs).
  Proof.
    hide_dj.
    intros regs0 M MC R. pose proof pD_facts as (Pp & Ppn & _). unfold HIGHEND in *.
    pose proof (rdn_length _ _ _ _ _ Hsrc) as LEN. unhide HdjD.
    apply (slots_ok_ext regs0 M); [|exact R]. intros x Hx. pose proof (u64_range x).
    rewrite (mm_result_pw M (Z_to_bv 64 pd) (Z_to_bv 64 ps) n bs MC).
    destruct (Z_lt_le_dec 0 n) as [Np|Nz]; [| first [ rewrite (proj1 (length_zero_iff_nil bs) ltac:(lia)); reflexivity | replace (Z.to_nat n) with 0%nat by lia; reflexivity ] ].
    destruct (HdjD Np) as [Hd|Hd].
    - apply wbytes_above. rewrite LEN. unorm. lia.
    - apply wbytes_below; [rewrite LEN; unorm; lia | unorm; lia].
  Qed.

  #[using="fS lS faS laS fD lD faD laD Hs_def Hn HappS HappD Hs HdjS HdjD Hover Hdst Hsrc Hret HWS HWD"] Lemma c3_run : forall regs0 regs M,
    cW_post regs -> FR regs0 M ->
    exists regs',
      msteps ASEGS (mkst regs (0x78450 : word) M rom) (mkst regs' ra (mm_result M (Z_to_bv 64 pd) (Z_to_bv 64 ps) bs) rom)
      /\ getr regs' 10 = Z_to_bv 64 pd /\ getr regs' 2 = sp /\ getr regs' 1 = ra
      /\ getr regs' 8 = getr regs0 8 /\ getr regs' 9 = getr regs0 9 /\ getr regs' 18 = getr regs0 18
      /\ getr regs' 19 = getr regs0 19 /\ getr regs' 20 = getr regs0 20 /\ getr regs' 21 = getr regs0 21
      /\ getr regs' 22 = getr regs0 22
      /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros regs0 regs M (H10 & H11 & H12 & H2) (HO & HGr & HR).
    pose proof pS_facts as (PSp & PSn & _). pose proof pD_facts as (PDp & PDn & _). unfold HIGHEND in *.
    pose proof (mcH_M M HO HGr) as MC.
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x78450 : word) M rom) (mkst r1 (0x8b408 : word) M rom)
              /\ (getr r1 10 = Z_to_bv 64 pd /\ getr r1 11 = Z_to_bv 64 ps /\ getr r1 12 = Z_to_bv 64 n /\ getr r1 1 = (0x78454 : word)
                  /\ getr r1 2 = Z_to_bv 64 (s - 2144) /\ keeps_but RIPL regs r1)).
    { eexists. split.
      - stepn F_78038 D_78038.                                                             (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q12 & Q1 & Q2 & K1).
    destruct (int_memmove_run M (Z_to_bv 64 pd) (Z_to_bv 64 ps) n bs rom MC ltac:(lia) r1 (0x78454 : word) ret_ok_7803c Q1 Q10 Q11 Q12) as (r2 & RUN2 & KP).
    pose proof (slots_ok_mm regs0 M MC HR) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
    assert (V2 : getr r2 2 = Z_to_bv 64 (s - 2144)) by (rewrite (KP 2%bv) by (cbv; tauto); exact Q2).
    assert (V10 : getr r2 10 = Z_to_bv 64 pd) by (rewrite (KP 10%bv) by (cbv; tauto); exact Q10).
    eexists. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
      stepiv F_7803c D_7803c (Z_to_bv 64 (s - 2032)) ltac:(wval).                        (* [comment removed for export] *)
      stepld F_78040 D_78040 ra ltac:(maddr (s - 8)%Z; exact R1).                         (* [comment removed for export] *)
      stepld F_78044 D_78044 (getr regs0 8) ltac:(maddr (s - 16)%Z; exact R2).            (* [comment removed for export] *)
      stepld F_78048 D_78048 (getr regs0 9) ltac:(maddr (s - 24)%Z; exact R3).            (* [comment removed for export] *)
      stepld F_7804c D_7804c (getr regs0 18) ltac:(maddr (s - 32)%Z; exact R4).           (* [comment removed for export] *)
      stepld F_78050 D_78050 (getr regs0 19) ltac:(maddr (s - 40)%Z; exact R5).           (* [comment removed for export] *)
      stepld F_78054 D_78054 (getr regs0 20) ltac:(maddr (s - 48)%Z; exact R6).           (* [comment removed for export] *)
      stepld F_78058 D_78058 (getr regs0 21) ltac:(maddr (s - 56)%Z; exact R7).           (* [comment removed for export] *)
      stepld F_7805c D_7805c (getr regs0 22) ltac:(maddr (s - 64)%Z; exact R8).           (* [comment removed for export] *)
      stepiv F_78060 D_78060 (Z_to_bv 64 s) ltac:(wval).                                  (* [comment removed for export] *)
      stepret F_78064 D_78064 ra ltac:(rwH; reflexivity).
      apply mst_refl.
    - repeat split; gres; try reflexivity; [exact V10 | symmetry; apply sp_s |].
      eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [apply keeps_but_cs; apply keeps_keeps_cs; exact KP|]. solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  #[using="kS fS lS faS laS kD fD lD faD laD Hs_def HfS_def HlS_def HfaS_def HlaS_def HfD_def HlD_def HfaD_def HlaD_def Hn HappS HappD Hs HshS HshD HdjS HdjD Hover Hok Hdst Hsrc Hret HG HI HZS HLS HkS HWS HZD HLD HkD HWD"] Theorem asan_memmove_run : forall regs,
    getr regs 10 = Z_to_bv 64 pd -> getr regs 11 = Z_to_bv 64 ps -> getr regs 12 = Z_to_bv 64 n -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs' Mj,
      msteps ASEGS (mkst regs (0x78370 : word) mem0 rom) (mkst regs' ra (mm_result Mj (Z_to_bv 64 pd) (Z_to_bv 64 ps) bs) rom)
      /\ getr regs' 10 = Z_to_bv 64 pd /\ getr regs' 2 = sp /\ getr regs' 1 = ra /\ keeps_cs regs regs'
      /\ out_agree Mj /\ mem_grows mem0 Mj /\ mcH Mj (Z_to_bv 64 pd) (Z_to_bv 64 ps) n bs.
  Proof.
    hide_dj.
    intros regs H10 H11 H12 H2 H1.
    destruct (c1_run regs H10 H11 H12 H2 H1) as (r1 & RUN1 & P1 & K1).
    destruct (cR_run regs (M9 regs) r1 P1 (M9_FR regs)) as (r2 & M2 & RUN2 & P2 & K2 & F2).
    destruct (cW_run regs M2 r2 P2 F2) as (r3 & M3 & RUN3 & P3 & K3 & F3).
    destruct (c3_run regs r3 M3 P3 F3) as (r4 & RUN4 & Q10 & Q2 & Q1 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & K4).
    exists r4, M3. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. exact RUN4.
    - assert (KB : keeps_but RIPL regs r4).
      { eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [exact K2|]. eapply keeps_but_trans; [exact K3|]. exact K4. }
      destruct F3 as (HO & HGr & _). pose proof (mcH_M M3 HO HGr) as MC3.
      split; [exact Q10|]. split; [exact Q2|]. split; [exact Q1|]. split; [| split; [exact HO | split; [exact HGr | exact MC3]]].
      intros r Hr. destruct (decide (r = 1%bv)) as [->|N1]; [rewrite Q1, H1; reflexivity|].
      destruct (decide (r = 2%bv)) as [->|N2]; [rewrite Q2, H2; reflexivity|].
      destruct (decide (r = 8%bv)) as [->|N8]; [exact Q8|]. destruct (decide (r = 9%bv)) as [->|N9]; [exact Q9|].
      destruct (decide (r = 18%bv)) as [->|N18]; [exact Q18|]. destruct (decide (r = 19%bv)) as [->|N19]; [exact Q19|].
      destruct (decide (r = 20%bv)) as [->|N20]; [exact Q20|]. destruct (decide (r = 21%bv)) as [->|N21]; [exact Q21|].
      destruct (decide (r = 22%bv)) as [->|N22]; [exact Q22|].
      apply KB; [exact Hr|]. cbv. intuition congruence.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Corollary asan_memmove_result_pw : forall Mj x, mcH Mj (Z_to_bv 64 pd) (Z_to_bv 64 ps) n bs ->
    mm_result Mj (Z_to_bv 64 pd) (Z_to_bv 64 ps) bs x = wbytes Mj (Z_to_bv 64 pd) bs x.
  Proof. hide_dj. intros Mj x MC. apply (mm_result_pw _ _ _ _ _ MC). Qed.
End AMM.
End FPX_1.
