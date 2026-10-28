(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_RGl.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition LP_HEAD : Z := 0xe8ab8.
Definition LP_EXIT : Z := 0xe8be0.
Definition LP_TOP : Z := 0xe8a8c.

Lemma kbyte : forall E M (e ez : expr) (c j z : Z),
  edenot E e = Z_to_bv 64 c -> edenot E ez = Z_to_bv 64 z -> 0 <= c -> 0 <= j -> c + j + 1 < 2 ^ 64 ->
  rdn asegs M (Z_to_bv 64 (c + j)) 1 = Some [Z_to_bv 8 z] -> 0 <= z < 256 ->
  kentry_ok asegs E M (KWord (SA e j) 1 ez).
Proof.
  intros E M e ez c j z Ec Ez Hc Hj Hcj HZ Hz.
  cbn [kentry_ok]. split; [lia|]. split.
  - unfold flat, estart, elenZ. cbn [a_base a_off]. rewrite Ec, u64_of_Z by lia. lia.
  - unfold adenot. cbn [a_base a_off]. rewrite Ec. rewrite v_addi_Z by lia.
    rewrite rdn_HL, HZ, Ez. rewrite word_to_le_bytes_1 by lia. reflexivity.
Qed.

Lemma lxor_ones64m : forall w, 0 <= w < 2 ^ 64 -> Z.lxor w (Z.ones 64) = (Z.lnot w) mod 2 ^ 64.
Proof.
  intros w Hw. rewrite <- Z.land_ones by lia.
  apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
  destruct (Z.lt_ge_cases i 64).
  - rewrite Z.ones_spec_low by lia. rewrite xorb_true_r, andb_true_r. reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite xorb_false_r, andb_false_r.
    destruct (Z.eq_dec w 0) as [->|]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma w_xor_m1 : forall d, 0 <= d < 2 ^ 64 ->
  alu64 ALU_XOR (Z_to_bv 64 d) (Z_to_bv 64 (-1)) = Z_to_bv 64 (2 ^ 64 - 1 - d).
Proof.
  intros d Hd. apply bv_eq. cbn [alu64 alu]. rewrite bv_xor_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small d) by lia.
  change ((-1) mod 2 ^ 64) with (Z.ones 64). rewrite lxor_ones64m by lia.
  unfold Z.lnot. rewrite (Z.mod_small (2 ^ 64 - 1 - d)) by lia.
  replace (Z.pred (- d)) with ((2 ^ 64 - 1 - d) + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma w_negm1 : forall d, 0 <= d < 2 ^ 64 ->
  alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 (-1)) (Z_to_bv 64 d)) (Z_to_bv 64 (-1)) = Z_to_bv 64 (2 ^ 64 - 1 - d).
Proof.
  intros d Hd. apply bv_eq. cbn [mul_div alu64 alu].
  rewrite bv_add_unsigned, bv_mul_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1). rewrite (Z.mod_small d) by lia.
  rewrite Z.add_mod_idemp_l by lia.
  replace ((2 ^ 64 - 1) * d + (2 ^ 64 - 1)) with ((2 ^ 64 - 1 - d) + d * 2 ^ 64) by ring.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma rw_cells_munch : forall W m m' A cs, rw_cells asegs m A cs -> munch W m m' -> wmono asegs m m' ->
  (forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells asegs m' A cs.
Proof.
  intros W m m' A cs [[WF (B0 & B1 & B)] (W0 & W1 & WW)] MU WM OUT.
  pose proof (cells_bytes_length cs WF) as L.
  split; [split; [exact WF|] | split; [lia | split; [lia | intros i Hi; apply WM, WW, Hi]]].
  split; [lia|]. split; [lia|]. intros i Hi.
  unfold mrd. rewrite MU.
  - exact (B i Hi).
  - unfold wa. rewrite u64_of_Z by lia. apply OUT. lia.
Qed.

Lemma munch_step : forall W W2 m M M', munch W m M -> munch W2 M M' -> (forall x, outside W x -> outside W2 x) ->
  munch W m M'.
Proof. intros W W2 m M M' H1 H2 S x Hx. rewrite (H2 x (S _ Hx)). apply H1, Hx. Qed.

Lemma rdn1_munch : forall W M M' x, munch W M M' -> outside W x -> 0 <= x < 2 ^ 64 ->
  rdn asegs M' (Z_to_bv 64 x) 1 = rdn asegs M (Z_to_bv 64 x) 1.
Proof.
  intros W M M' x MU OUT Hx. apply rdn_ext; [rewrite u64_of_Z by lia; lia|].
  intros y Hy. rewrite u64_of_Z in Hy by lia. apply MU. replace (bv_unsigned y) with x by lia. exact OUT.
Qed.

Lemma shk_munch : forall W M M' x k, munch W M M' -> outside W (x / 8 + SHBASE) -> 0 <= x < 2 ^ 47 -> shk M x k -> shk M' x k.
Proof.
  intros W M M' x k MU OUT Hx S. unfold shk in *. rewrite <- S. apply (rdn1_munch W); [exact MU | exact OUT |].
  assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia). unfold SHBASE. lia.
Qed.

Lemma byte_of_bytes_at : forall M A ds i, bytes_at asegs M A ds -> 0 <= i < Z.of_nat (length ds) ->
  exists z, 0 <= z < 256 /\ rdn asegs M (Z_to_bv 64 (A + i)) 1 = Some [Z_to_bv 8 z].
Proof.
  intros M A ds i (B0 & B1 & B) Hi.
  destruct (nth_error ds (Z.to_nat i)) as [b|] eqn:Hb.
  2:{ apply nth_error_None in Hb. lia. }
  exists (bv_unsigned b). split; [pose proof (bv_unsigned_in_range _ b) as Rb; change (bv_modulus 8) with 256 in Rb; lia|].
  pose proof (B (Z.to_nat i) ltac:(lia)) as Hm. rewrite Z2Nat.id in Hm by lia. rewrite Hb in Hm.
  rewrite <- rdn_HL. apply rdn1_of_mrd.
  replace (Z_to_bv 8 (bv_unsigned b)) with b; [exact Hm|].
  apply bv_eq. rewrite Z_to_bv_unsigned. rewrite bv_wrap_small; [reflexivity | apply bv_unsigned_in_range].
Qed.

Lemma shk_last : forall M A n x, addressable M A n -> n mod 8 <> 0 -> A + 8 * (n / 8) <= x < A + n ->
  shk M x (n mod 8).
Proof.
  intros M A n x [Hn SH] H8 Hx.
  destruct (shk_of_SHAD M A (shadow_of n) x SH) as (b & Hb & Hs).
  { rewrite shadow_of_length by lia. unfold nsh. Z.div_mod_to_equations. lia. }
  replace (Z.to_nat ((x - A) / 8)) with (Z.to_nat (n / 8)) in Hb by (f_equal; Z.div_mod_to_equations; lia).
  rewrite shadow_of_nth_last in Hb by lia. injection Hb as <-.
  rewrite b8_unsigned in Hs by (pose proof (Z.mod_pos_bound n 8 ltac:(lia)); lia). exact Hs.
Qed.

Lemma lp_arith : forall N n, n = N / 4 -> 4 <= N ->
  1 <= n /\ 4 * n <= N < 4 * n + 4 /\ N / 8 = n / 2 /\ (4 * n) / 8 = n / 2 /\ 0 <= n / 2 /\ 8 * (n / 2) <= 4 * n
  /\ (Z.odd n = true -> 4 * (n - 1) = 8 * (n / 2) /\ 4 <= N mod 8 < 8 /\ (4 * n) mod 8 = 4 /\ N = 8 * (N / 8) + N mod 8)
  /\ (Z.odd n = false -> 4 * n = 8 * (n / 2)).
Proof.
  intros N n HN H4. subst n. rewrite Zodd_mod.
  destruct (Z.eqb_spec ((N / 4) mod 2) 1) as [E|E]; Z.div_mod_to_equations; repeat split; try lia; intros; try discriminate; lia.
Qed.

Lemma half_lb : forall n, 4 * n <= 8 * (n / 2) + 4.
Proof. intros n. Z.div_mod_to_equations. lia. Qed.

Lemma sh0_full : forall M A n x, addressable M A n -> A <= x < A + 8 * (n / 8) -> shk M x 0.
Proof.
  intros M A n x [Hn SH] Hx.
  destruct (shk_of_SHAD M A (shadow_of n) x SH) as (b & Hb & Hs).
  { rewrite shadow_of_length by lia. unfold nsh. Z.div_mod_to_equations. lia. }
  rewrite shadow_of_nth_full in Hb.
  - assert (b = b8 0) by congruence. subst b. rewrite b8_unsigned in Hs by lia. exact Hs.
  - exact Hn.
  - rewrite Z2Nat.id by (apply Z.div_pos; lia). apply Z.div_lt_upper_bound; lia.
Qed.

Lemma shk_tr : forall m M (P S1 k n x v : Z), munch [(P, P + 4 * k); (S1 - 16, S1); (S1 + 64, S1 + 80)] m M ->
  (P + 4 * n <= ALOWSH_LO \/ AHI_LO <= P) -> 0 <= k <= n -> 2 ^ 45 <= S1 -> 0 <= x < 2 ^ 47 -> shk m x v -> shk M x v.
Proof.
  intros m M P S1 k n x v MU PB K HS1 X Hs. apply (shk_munch _ m M x v MU); [| exact X | exact Hs].
  pose proof (div8_bound x X). cbn [outside]. unfold ALOWSH_LO, AHI_LO, SHBASE in *. repeat split; lia.
Qed.

Section TopL1.
  Context {HCEIL : HeapCeil}.

  Definition KL : list reg := [3; 4; 5; 6; 7; 28; 29; 30; 31]%bv.

  Definition lh (R : bvmap 5 word) (S1 SP N D k : Z) : Prop :=
    getr R 2 = Z_to_bv 64 S1 /\ getr R 8 = Z_to_bv 64 SP /\ getr R 9 = Z_to_bv 64 S1 /\ getr R 19 = Z_to_bv 64 SHBASE /\
    getr R 27 = Z_to_bv 64 N /\ getr R 20 = Z_to_bv 64 (4 * k) /\ getr R 25 = Z_to_bv 64 k /\
    getr R 26 = Z_to_bv 64 (D + 4 * k) /\ getr R 22 = Z_to_bv 64 (D + 4 * k + 1) /\
    getr R 24 = Z_to_bv 64 (2 ^ 64 - 1 - D).

  Definition IT_SR : list expr := srs sr_id
    [(2%bv, EVar 33); (8%bv, EVar 44); (9%bv, EVar 33); (19%bv, ELit SHBASE); (27%bv, EVar 35);
     (20%bv, EMd M_MUL (ELit 4) (EVar 32)); (25%bv, EVar 32);
     (26%bv, EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 32)));
     (22%bv, EAlu ALU_ADD (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 32))) (ELit 1));
     (24%bv, EAlu ALU_XOR (EVar 34) (ELit (-1)))].

  Definition IT_D : expr := EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 32)).
  Definition IT_DB (j : Z) : expr := EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 32)) (EVar 34)) (ELit j).
  Definition IT_PK : expr := EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 32)) (EVar 37).
  Definition IT_SH (b : expr) (v : expr) : kentry := KWord (SA (EAlu ALU_SRL b (ELit 3)) SHBASE) 1 v.

  Definition IT_KN : list kentry :=
    [ KWord (SA (ELit 0) GOT_SH) 8 (ELit SHCELL); KWord (SA (ELit 0) SHCELL) 8 (ELit SHBASE);
      KWord (SA (EVar 33) 88) 8 (EVar 34); KWord (SA (EVar 33) 72) 8 (ELit 1);
      KWord (SA (EVar 33) 64) 8 (EVar 35); KWord (SA (EVar 33) 80) 8 (EVar 36);
      KWord (SA (EVar 36) 0) 8 (EVar 37);
      KWord (SA IT_D 0) 1 (EVar 40); KWord (SA IT_D 1) 1 (EVar 41);
      KWord (SA IT_D 2) 1 (EVar 42); KWord (SA IT_D 3) 1 (EVar 43);
      KWr (SA (EAlu ALU_ADD (EVar 37) (EMd M_MUL (ELit 4) (EVar 32))) 0) (ELit 4);
      KWr (SA (EVar 33) (-16)) (ELit 16);
      KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 34) 1 (2 ^ 47); KRange (EVar 35) 4 (2 ^ 26);
      KRange (EVar 32) 0 (2 ^ 24); KRange (EVar 36) (2 ^ 22) (2 ^ 47); KAlign (EVar 36) 8;
      KRange (EVar 37) 1 (2 ^ 47); KAlign (EVar 37) 16;
      KRange (EVar 40) 0 255; KRange (EVar 41) 0 255; KRange (EVar 42) 0 255; KRange (EVar 43) 0 255 ].

  Definition IT_KNF : list kentry := IT_KN ++
    [ IT_SH (IT_DB 1) (ELit 0); IT_SH IT_D (ELit 0); IT_SH (IT_DB 2) (ELit 0); IT_SH (IT_DB 3) (ELit 0);
      IT_SH (EVar 36) (ELit 0); IT_SH IT_PK (ELit 0) ].

  Definition IT_KNO : list kentry := IT_KN ++
    [ KAlign (EVar 32) 2; KAlign (EVar 34) 8; KRange (EVar 38) 4 7;
      IT_SH (IT_DB 1) (EVar 38); IT_SH IT_D (EVar 38); IT_SH (IT_DB 2) (EVar 38); IT_SH (IT_DB 3) (EVar 38);
      IT_SH IT_PK (ELit 4); IT_SH (EVar 36) (ELit 0) ].

  Definition IT_DM : list bool := [false; false; false; false; false; true].
  Definition IT_DX : list bool := [false; false; false; false; false; false].

  Ltac it_regs :=
    apply regs_ok_srs; [apply regs_ok_seed|];
    repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | evs; rewrite ?w_xor_m1, ?w_mul, ?w_add by lia; assumption] |]);
    apply Forall_nil.

  Ltac it_kbase CG CS CF1 CF2 CV B0 B1 B2 B3 Z0 Z1 Z2 Z3 WP ST :=
    unfold GOT_SH, SHCELL, SHBASE in CG, CS;
    apply Forall_cons; [kword_cell CG 0%nat (C8 (Z_to_bv 64 SHCELL))|];
    apply Forall_cons; [kword_cell CS 0%nat (C8 (Z_to_bv 64 SHBASE))|];
    apply Forall_cons; [eapply (kword_of_rw_cells _ _ _ _ _ 8%nat); [exact CF2 | reflexivity | reflexivity | lia | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | reflexivity]|];
    apply Forall_cons; [eapply (kword_of_rw_cells _ _ _ _ _ 8%nat); [exact CF1 | reflexivity | reflexivity | lia | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | reflexivity]|];
    apply Forall_cons; [eapply (kword_of_rw_cells _ _ _ _ _ 0%nat); [exact CF1 | reflexivity | reflexivity | lia | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | reflexivity]|];
    apply Forall_cons; [eapply (kword_of_rw_cells _ _ _ _ _ 0%nat); [exact CF2 | reflexivity | reflexivity | lia | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | reflexivity]|];
    apply Forall_cons; [eapply (kword_of_rw_cells _ _ _ _ _ 0%nat); [exact CV | reflexivity | reflexivity | lia | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | reflexivity]|];
    apply Forall_cons; [eapply kbyte; [evs; rewrite ?w_mul, ?w_add by lia; reflexivity | evs; reflexivity | lia | lia | lia | exact B0 | exact Z0]|];
    apply Forall_cons; [eapply kbyte; [evs; rewrite ?w_mul, ?w_add by lia; reflexivity | evs; reflexivity | lia | lia | lia | exact B1 | exact Z1]|];
    apply Forall_cons; [eapply kbyte; [evs; rewrite ?w_mul, ?w_add by lia; reflexivity | evs; reflexivity | lia | lia | lia | exact B2 | exact Z2]|];
    apply Forall_cons; [eapply kbyte; [evs; rewrite ?w_mul, ?w_add by lia; reflexivity | evs; reflexivity | lia | lia | lia | exact B3 | exact Z3]|];
    apply Forall_cons; [eapply kwr_of_wr_at; [exact WP | | | ]; unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite ?w_mul, ?w_add, ?u64_of_Z by lia; lia|];
    apply Forall_cons; [eapply kwr_of_stk; [exact ST | | | ]; unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite ?u64_of_Z by lia; lia|];
    do 12 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; first [lia | split; [lia | assumption]]|]).

  Ltac it_sc := cbn [sc_denot]; unfold flat, estart, elenZ; cbn [a_base a_off]; evs;
    rewrite ?w_xor_m1, ?w_mul, ?w_add by lia; rewrite ?u64_of_Z by lia;
    first [ rewrite ?br_ltu, ?br_geu by lia; bool_lia | lia ].

  Ltac it_reg := first
    [ assumption
    | match goal with H : getr ?R ?r = _ |- getr ?R ?r = _ =>
        rewrite H; rewrite ?w_negm1, ?w_xor_m1, ?w_mul, ?w_add by lia; first [reflexivity | f_equal; lia] end ].

  Lemma it_full : forall (b : bool) R F fc M ro (S1 SP D N V P k lo : Z) (VC : list cell),
    lh R S1 SP N D k ->
    2 ^ 45 <= S1 -> S1 + 224 <= SP -> SP <= 2 ^ 47 -> lo <= S1 - 16 ->
    1 <= D -> D + N <= 2 ^ 47 -> 4 <= N < 2 ^ 26 -> 0 <= k -> 4 * k + 3 < N ->
    (if b then 4 * k + 7 < N else N <= 4 * k + 7) ->
    2 ^ 22 <= V -> V + 24 <= S1 - 16 -> V mod 8 = 0 ->
    1 <= P -> P + 4 * k + 4 <= 2 ^ 47 -> P mod 16 = 0 -> (P + 4 * k + 4 <= lo \/ SP <= P + 4 * k) ->
    rw_cells asegs M GOT_SH [C8 (Z_to_bv 64 SHCELL)] -> rw_cells asegs M SHCELL [C8 (Z_to_bv 64 SHBASE)] ->
    rw_cells asegs M (S1 + 64) [C8 (Z_to_bv 64 N); C8 (Z_to_bv 64 1)] ->
    rw_cells asegs M (S1 + 80) [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 D)] ->
    rw_cells asegs M V (C8 (Z_to_bv 64 P) :: VC) ->
    (forall j, 0 <= j < 4 -> exists z, 0 <= z < 256 /\ rdn asegs M (Z_to_bv 64 (D + 4 * k + j)) 1 = Some [Z_to_bv 8 z]) ->
    wr_at asegs M (P + 4 * k) 4 -> stk asegs M lo SP ->
    gz M (D + 4 * k) 4 -> gz M V 1 -> gz M (P + 4 * k) 1 ->
    exists R' M', CatSim.msteps asegs (MS R F (Z_to_bv 64 LP_HEAD) fc None M ro)
                    (MS R' F (Z_to_bv 64 (if b then LP_HEAD else LP_EXIT)) fc None M' ro)
      /\ lh R' S1 SP N D (k + 1) /\ kept_in KL R R'
      /\ munch [(P + 4 * k, P + 4 * k + 4); (S1 - 16, S1)] M M' /\ wmono asegs M M' /\ stk asegs M' lo SP.
  Proof.
    intros until VC. intros LH S1L S1H SPH LO D1 D2 HN K0 K3 KB V1 V2 V8 P1 P2 P16 PST CG CS CF1 CF2 CV BY WP ST GD GV GP.
    destruct (BY 0 ltac:(lia)) as (z0 & Z0 & B0). destruct (BY 1 ltac:(lia)) as (z1 & Z1 & B1).
    destruct (BY 2 ltac:(lia)) as (z2 & Z2 & B2). destruct (BY 3 ltac:(lia)) as (z3 & Z3 & B3).
    destruct LH as (H2 & H8 & H9 & H19 & H27 & H20 & H25 & H26 & H22 & H24).
    pose (E := Eseed R [Z_to_bv 64 k; Z_to_bv 64 S1; Z_to_bv 64 D; Z_to_bv 64 N; Z_to_bv 64 V; Z_to_bv 64 P;
                        Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 z0; Z_to_bv 64 z1; Z_to_bv 64 z2; Z_to_bv 64 z3; Z_to_bv 64 SP]).
    assert (HR : regs_ok E IT_SR R) by it_regs.
    assert (HK : know_ok asegs E M IT_KNF).
    { kn_eval. unfold know_ok. it_kbase CG CS CF1 CF2 CV B0 B1 B2 B3 Z0 Z1 Z2 Z3 WP ST.
      repeat (apply Forall_cons; [kshadow_tac|]). apply Forall_nil. }
    destruct b.
    - xrun_at (PropExec.mkFP F fc) asegs R LP_HEAD M ro HR HK 200%nat [LP_HEAD; LP_EXIT] (SCR IT_DM [] []) 60%N;
        [split_scs; it_sc | ].
      clear HK.
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E M lg) in Hms; set (M1 := mem_denot E M lg) in Hms end end.
      exists R', M1. split; [exact Hms|].
      rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 9%bv G9. rreg HR' 19%bv G19. rreg HR' 27%bv G27.
      rreg HR' 20%bv G20. rreg HR' 25%bv G25. rreg HR' 26%bv G26. rreg HR' 22%bv G22. rreg HR' 24%bv G24.
      split; [unfold lh; repeat match goal with |- _ /\ _ => split end; it_reg|].
      split; [intros r Hr; eapply (syms_id_sound R _ _ R' KL HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hr]|].
      split; [subst M1; apply munch_mem_denot; [exact Hlf|];
              repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?w_mul, ?w_add, ?u64_of_Z by lia;
                                          cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]); apply Forall_nil|].
      split; [subst M1; apply wmono_mem_denot|].
      subst M1; apply stk_mem_denot; exact ST.
    - xrun_at (PropExec.mkFP F fc) asegs R LP_HEAD M ro HR HK 200%nat [LP_HEAD; LP_EXIT] (SCR IT_DX [] []) 60%N;
        [split_scs; it_sc | ].
      clear HK.
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E M lg) in Hms; set (M1 := mem_denot E M lg) in Hms end end.
      exists R', M1. split; [exact Hms|].
      rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 9%bv G9. rreg HR' 19%bv G19. rreg HR' 27%bv G27.
      rreg HR' 20%bv G20. rreg HR' 25%bv G25. rreg HR' 26%bv G26. rreg HR' 22%bv G22. rreg HR' 24%bv G24.
      split; [unfold lh; repeat match goal with |- _ /\ _ => split end; it_reg|].
      split; [intros r Hr; eapply (syms_id_sound R _ _ R' KL HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hr]|].
      split; [subst M1; apply munch_mem_denot; [exact Hlf|];
              repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?w_mul, ?w_add, ?u64_of_Z by lia;
                                          cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]); apply Forall_nil|].
      split; [subst M1; apply wmono_mem_denot|].
      subst M1; apply stk_mem_denot; exact ST.
  Qed.

  Lemma it_odd : forall R F fc M ro (S1 SP D N V P k lo v : Z) (VC : list cell),
    lh R S1 SP N D k ->
    2 ^ 45 <= S1 -> S1 + 224 <= SP -> SP <= 2 ^ 47 -> lo <= S1 - 16 ->
    1 <= D -> D + N <= 2 ^ 47 -> 4 <= N < 2 ^ 26 -> 0 <= k -> 4 * k + 3 < N -> N <= 4 * k + 7 ->
    k mod 2 = 0 -> D mod 8 = 0 -> 4 <= v <= 7 ->
    2 ^ 22 <= V -> V + 24 <= S1 - 16 -> V mod 8 = 0 ->
    1 <= P -> P + 4 * k + 4 <= 2 ^ 47 -> P mod 16 = 0 -> (P + 4 * k + 4 <= lo \/ SP <= P + 4 * k) ->
    rw_cells asegs M GOT_SH [C8 (Z_to_bv 64 SHCELL)] -> rw_cells asegs M SHCELL [C8 (Z_to_bv 64 SHBASE)] ->
    rw_cells asegs M (S1 + 64) [C8 (Z_to_bv 64 N); C8 (Z_to_bv 64 1)] ->
    rw_cells asegs M (S1 + 80) [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 D)] ->
    rw_cells asegs M V (C8 (Z_to_bv 64 P) :: VC) ->
    (forall j, 0 <= j < 4 -> exists z, 0 <= z < 256 /\ rdn asegs M (Z_to_bv 64 (D + 4 * k + j)) 1 = Some [Z_to_bv 8 z]) ->
    wr_at asegs M (P + 4 * k) 4 -> stk asegs M lo SP ->
    (forall j, 0 <= j < 4 -> shk M (D + 4 * k + j) v) -> gz M V 1 -> shk M (P + 4 * k) 4 ->
    exists R' M', CatSim.msteps asegs (MS R F (Z_to_bv 64 LP_HEAD) fc None M ro) (MS R' F (Z_to_bv 64 LP_EXIT) fc None M' ro)
      /\ lh R' S1 SP N D (k + 1) /\ kept_in KL R R'
      /\ munch [(P + 4 * k, P + 4 * k + 4); (S1 - 16, S1)] M M' /\ wmono asegs M M' /\ stk asegs M' lo SP.
  Proof.
    intros until VC. intros LH S1L S1H SPH LO D1 D2 HN K0 K3 KB K2 D8 Hv V1 V2 V8 P1 P2 P16 PST CG CS CF1 CF2 CV BY WP ST SD GV SP4.
    destruct (BY 0 ltac:(lia)) as (z0 & Z0 & B0). destruct (BY 1 ltac:(lia)) as (z1 & Z1 & B1).
    destruct (BY 2 ltac:(lia)) as (z2 & Z2 & B2). destruct (BY 3 ltac:(lia)) as (z3 & Z3 & B3).
    destruct LH as (H2 & H8 & H9 & H19 & H27 & H20 & H25 & H26 & H22 & H24).
    pose (E := Eseed R [Z_to_bv 64 k; Z_to_bv 64 S1; Z_to_bv 64 D; Z_to_bv 64 N; Z_to_bv 64 V; Z_to_bv 64 P;
                        Z_to_bv 64 v; Z_to_bv 64 0; Z_to_bv 64 z0; Z_to_bv 64 z1; Z_to_bv 64 z2; Z_to_bv 64 z3; Z_to_bv 64 SP]).
    assert (HR : regs_ok E IT_SR R) by it_regs.
    assert (HK : know_ok asegs E M IT_KNO).
    { kn_eval. unfold know_ok. it_kbase CG CS CF1 CF2 CV B0 B1 B2 B3 Z0 Z1 Z2 Z3 WP ST.
      do 3 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; first [lia | split; [lia | assumption]]|]).
      do 4 (apply Forall_cons;
        [eapply (kshadow E M _ _ v); [evs; rewrite ?w_mul, ?w_add by lia; reflexivity | lia | lia | evs; reflexivity |];
         lazymatch goal with |- shk M ?x v => replace x with (D + 4 * k + (x - D - 4 * k)) by lia; apply SD; lia end|]).
      apply Forall_cons;
        [eapply (kshadow E M _ _ 4); [evs; rewrite ?w_mul, ?w_add by lia; reflexivity | lia | lia | evs; reflexivity |];
         lazymatch goal with |- shk M ?x 4 => replace x with (P + 4 * k) by lia; exact SP4 end|].
      apply Forall_cons; [kshadow_tac|]. apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R LP_HEAD M ro HR HK 200%nat [LP_HEAD; LP_EXIT] (SCR IT_DX [] []) 60%N;
      [split_scs; it_sc | ].
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E M lg) in Hms; set (M1 := mem_denot E M lg) in Hms end end.
    exists R', M1. split; [exact Hms|].
    rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 9%bv G9. rreg HR' 19%bv G19. rreg HR' 27%bv G27.
    rreg HR' 20%bv G20. rreg HR' 25%bv G25. rreg HR' 26%bv G26. rreg HR' 22%bv G22. rreg HR' 24%bv G24.
    split; [unfold lh; repeat match goal with |- _ /\ _ => split end; it_reg|].
    split; [intros r Hr; eapply (syms_id_sound R _ _ R' KL HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hr]|].
    split; [subst M1; apply munch_mem_denot; [exact Hlf|];
            repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?w_mul, ?w_add, ?u64_of_Z by lia;
                                        cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]); apply Forall_nil|].
    split; [subst M1; apply wmono_mem_denot|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.

  Lemma lp_ctx : forall (m M : mem) (S1 SP D N V P lo k : Z) (w1 w2 : word),
    2 ^ 45 <= S1 -> S1 + 224 <= SP -> lo <= S1 - 16 ->
    AIMG_TOP <= D -> D + N <= 2 ^ 47 -> 4 <= N ->
    AIMG_TOP <= V -> V + 24 <= S1 - 16 ->
    AIMG_TOP <= P -> P + 4 * (N / 4) <= 2 ^ 47 ->
    (D + N <= P \/ P + 4 * (N / 4) <= D) -> (V + 24 <= P \/ P + 4 * (N / 4) <= V) ->
    (P + 4 * (N / 4) <= lo \/ SP <= P) -> (D + N <= lo \/ SP <= D) ->
    0 <= k -> k < N / 4 ->
    munch [(P, P + 4 * k); (S1 - 16, S1); (S1 + 64, S1 + 80)] m M -> wmono asegs m M ->
    rw_cells asegs m GOT_SH [C8 (Z_to_bv 64 SHCELL)] -> rw_cells asegs m SHCELL [C8 (Z_to_bv 64 SHBASE)] ->
    rw_cells asegs m (S1 + 80) [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 D)] ->
    rw_cells asegs m V [C8 (Z_to_bv 64 P); C8 w1; C8 w2] ->
    (forall j, 0 <= j < N -> exists z, 0 <= z < 256 /\ rdn asegs m (Z_to_bv 64 (D + j)) 1 = Some [Z_to_bv 8 z]) ->
    wr_at asegs m P (4 * (N / 4)) ->
    rw_cells asegs M GOT_SH [C8 (Z_to_bv 64 SHCELL)] /\ rw_cells asegs M SHCELL [C8 (Z_to_bv 64 SHBASE)] /\
    rw_cells asegs M (S1 + 80) [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 D)] /\
    rw_cells asegs M V [C8 (Z_to_bv 64 P); C8 w1; C8 w2] /\
    (forall j, 0 <= j < 4 -> exists z, 0 <= z < 256 /\ rdn asegs M (Z_to_bv 64 (D + 4 * k + j)) 1 = Some [Z_to_bv 8 z]) /\
    wr_at asegs M (P + 4 * k) 4.
  Proof.
    intros m M S1 SP D N V P lo k w1 w2 S1L S1H LO D1 D2 HN V1 V2 P1 P2 PD PV PST DST K0 K1 MU WM CG CS CF CV BY WP.
    assert (Hn : 4 * (N / 4) <= N) by (apply Z.mul_div_le; lia).
    unfold AIMG_TOP in *.
    split; [eapply rw_cells_munch; [exact CG | exact MU | exact WM |]; intros x Hx; simpl in Hx; cbn [outside];
            unfold GOT_SH in *; repeat split; lia|].
    split; [eapply rw_cells_munch; [exact CS | exact MU | exact WM |]; intros x Hx; simpl in Hx; cbn [outside];
            unfold SHCELL in *; repeat split; lia|].
    split; [eapply rw_cells_munch; [exact CF | exact MU | exact WM |]; intros x Hx; simpl in Hx; cbn [outside]; repeat split; lia|].
    split; [eapply rw_cells_munch; [exact CV | exact MU | exact WM |]; intros x Hx; simpl in Hx; cbn [outside]; repeat split; lia|].
    split.
    - intros j Hj. destruct (BY (4 * k + j) ltac:(lia)) as (z & Hz & Bz). exists z. split; [exact Hz|].
      rewrite (rdn1_munch _ m M (D + 4 * k + j) MU); [| cbn [outside]; repeat split; lia | lia].
      replace (D + 4 * k + j) with (D + (4 * k + j)) by lia. exact Bz.
    - eapply wr_at_sub; [eapply wr_at_wm; [exact WP | exact WM] | lia | lia | lia].
  Qed.

  Lemma lp_loop : forall (m : mem) F fc ro (S1 SP D N V P lo : Z) (w1 w2 : word),
    2 ^ 45 <= S1 -> S1 + 224 <= SP -> SP <= 2 ^ 47 -> lo <= S1 - 16 ->
    D mod 16 = 0 -> AIMG_TOP <= D -> D + N <= 2 ^ 47 -> 4 <= N < 2 ^ 26 ->
    AIMG_TOP <= V -> V + 24 <= S1 - 16 -> V mod 8 = 0 ->
    AIMG_TOP <= P -> P + 4 * (N / 4) <= 2 ^ 47 -> P mod 16 = 0 ->
    (P + 4 * (N / 4) <= ALOWSH_LO \/ AHI_LO <= P) ->
    (D + N <= P \/ P + 4 * (N / 4) <= D) -> (V + 24 <= P \/ P + 4 * (N / 4) <= V) ->
    (P + 4 * (N / 4) <= lo \/ SP <= P) -> (D + N <= lo \/ SP <= D) ->
    rw_cells asegs m GOT_SH [C8 (Z_to_bv 64 SHCELL)] -> rw_cells asegs m SHCELL [C8 (Z_to_bv 64 SHBASE)] ->
    rw_cells asegs m (S1 + 80) [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 D)] ->
    rw_cells asegs m V [C8 (Z_to_bv 64 P); C8 w1; C8 w2] ->
    (forall j, 0 <= j < N -> exists z, 0 <= z < 256 /\ rdn asegs m (Z_to_bv 64 (D + j)) 1 = Some [Z_to_bv 8 z]) ->
    wr_at asegs m P (4 * (N / 4)) -> addressable m D N -> addressable m P (4 * (N / 4)) -> gz m V 1 ->
    forall (K : nat) R M k, k + Z.of_nat (S K) = N / 4 -> 0 <= k -> lh R S1 SP N D k ->
    munch [(P, P + 4 * k); (S1 - 16, S1); (S1 + 64, S1 + 80)] m M -> wmono asegs m M -> stk asegs M lo SP ->
    rw_cells asegs M (S1 + 64) [C8 (Z_to_bv 64 N); C8 (Z_to_bv 64 1)] ->
    exists R' M', CatSim.msteps asegs (MS R F (Z_to_bv 64 LP_HEAD) fc None M ro) (MS R' F (Z_to_bv 64 LP_EXIT) fc None M' ro)
      /\ lh R' S1 SP N D (N / 4) /\ kept_in KL R R'
      /\ munch [(P, P + 4 * (N / 4)); (S1 - 16, S1); (S1 + 64, S1 + 80)] m M' /\ wmono asegs m M' /\ stk asegs M' lo SP.
  Proof.
    intros m F fc ro S1 SP D N V P lo w1 w2 S1L S1H SPH LO D16 D1 D2 HN V1 V2 V8 P1 P2 P16 PB PD PV PST DST CG CS CF2 CV BY WP AD AP GV.
    pose proof (lp_arith N (N / 4) eq_refl ltac:(lia)) as (A1 & A2 & A3 & A4 & A5 & A6 & AO & AE).
    pose proof (half_lb (N / 4)) as AH.
    assert (D0 : 1 <= D) by (unfold AIMG_TOP in D1; lia).
    assert (P0 : 1 <= P) by (unfold AIMG_TOP in P1; lia).
    assert (V0 : 2 ^ 22 <= V) by (unfold AIMG_TOP in V1; lia).
    induction K as [|K IH]; intros R M k Hk K0 LH MU WM ST CF1.
    - destruct (lp_ctx m M S1 SP D N V P lo k w1 w2 S1L S1H LO D1 D2 ltac:(lia) V1 V2 P1 P2 PD PV PST DST K0 ltac:(lia)
                  MU WM CG CS CF2 CV BY WP) as (CG' & CS' & CF2' & CV' & BY' & WP').
      assert (GV' : gz M V 1).
      { intros i Hi. unfold sh0. eapply (shk_tr m M P S1 k (N / 4)); [exact MU | exact PB | lia | lia | lia | exact (GV i Hi)]. }
      assert (MUF : forall M', munch [(P + 4 * k, P + 4 * k + 4); (S1 - 16, S1)] M M' ->
                    munch [(P, P + 4 * (N / 4)); (S1 - 16, S1); (S1 + 64, S1 + 80)] m M').
      { intros M' MU'. apply (munch_step _ [(P + 4 * k, P + 4 * k + 4); (S1 - 16, S1)] m M M'); [| exact MU' |].
        - apply (munch_weaken [(P, P + 4 * k); (S1 - 16, S1); (S1 + 64, S1 + 80)]); [| exact MU].
          intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (X1 & X2 & X3 & _). repeat split; lia.
        - intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (X1 & X2 & X3 & _). repeat split; lia. }
      destruct (Z.odd (N / 4)) eqn:OD.
      + destruct (AO ltac:(first [exact OD | reflexivity])) as (O1 & O2 & O3 & O4).
        assert (SDo : forall j, 0 <= j < 4 -> shk M (D + 4 * k + j) (N mod 8)).
        { intros j Hj. eapply (shk_tr m M P S1 k (N / 4)); [exact MU | exact PB | lia | lia | lia |].
          apply (shk_last m D N); [exact AD | lia | lia]. }
        assert (SPo : shk M (P + 4 * k) 4).
        { pose proof (shk_last m P (4 * (N / 4)) (P + 4 * k) AP ltac:(lia) ltac:(lia)) as S4. rewrite O3 in S4.
          eapply (shk_tr m M P S1 k (N / 4)); [exact MU | exact PB | lia | lia | lia | exact S4]. }
        assert (K2 : k mod 2 = 0) by (replace k with (N / 4 / 2 * 2) by lia; apply Z.mod_mul; lia).
        assert (D8 : D mod 8 = 0) by (clear - D16; Z.div_mod_to_equations; lia).
        destruct (it_odd R F fc M ro S1 SP D N V P k lo (N mod 8) [C8 w1; C8 w2] LH S1L S1H SPH LO D0 D2 HN K0 ltac:(lia) ltac:(lia)
                    K2 D8 ltac:(lia) V0 V2 V8 P0 ltac:(lia) P16 ltac:(lia) CG' CS' CF1 CF2' CV' BY' WP' ST SDo GV' SPo)
          as (R' & M' & RUN & LH' & KP & MU' & WM' & ST').
        exists R', M'. split; [exact RUN|]. split; [replace (N / 4) with (k + 1) by lia; exact LH'|].
        split; [exact KP|]. split; [exact (MUF M' MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM') | exact ST'].
      + pose proof (AE ltac:(first [exact OD | reflexivity])) as E2.
        assert (GD : gz M (D + 4 * k) 4).
        { intros i Hi. unfold sh0. eapply (shk_tr m M P S1 k (N / 4)); [exact MU | exact PB | lia | lia | lia |].
          apply (sh0_full m D N); [exact AD | lia]. }
        assert (GP : gz M (P + 4 * k) 1).
        { intros i Hi. unfold sh0. eapply (shk_tr m M P S1 k (N / 4)); [exact MU | exact PB | lia | lia | lia |].
          apply (sh0_full m P (4 * (N / 4))); [exact AP | lia]. }
        destruct (it_full false R F fc M ro S1 SP D N V P k lo [C8 w1; C8 w2] LH S1L S1H SPH LO D0 D2 HN K0 ltac:(lia)
                    ltac:(cbn; lia) V0 V2 V8 P0 ltac:(lia) P16 ltac:(lia) CG' CS' CF1 CF2' CV' BY' WP' ST GD GV' GP)
          as (R' & M' & RUN & LH' & KP & MU' & WM' & ST').
        exists R', M'. split; [exact RUN|]. split; [replace (N / 4) with (k + 1) by lia; exact LH'|].
        split; [exact KP|]. split; [exact (MUF M' MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM') | exact ST'].
    - destruct (lp_ctx m M S1 SP D N V P lo k w1 w2 S1L S1H LO D1 D2 ltac:(lia) V1 V2 P1 P2 PD PV PST DST K0 ltac:(lia)
                  MU WM CG CS CF2 CV BY WP) as (CG' & CS' & CF2' & CV' & BY' & WP').
      assert (GV' : gz M V 1).
      { intros i Hi. unfold sh0. eapply (shk_tr m M P S1 k (N / 4)); [exact MU | exact PB | lia | lia | lia | exact (GV i Hi)]. }
      assert (GD : gz M (D + 4 * k) 4).
      { intros i Hi. unfold sh0. eapply (shk_tr m M P S1 k (N / 4)); [exact MU | exact PB | lia | lia | lia |].
        apply (sh0_full m D N); [exact AD | lia]. }
      assert (GP : gz M (P + 4 * k) 1).
      { intros i Hi. unfold sh0. eapply (shk_tr m M P S1 k (N / 4)); [exact MU | exact PB | lia | lia | lia |].
        apply (sh0_full m P (4 * (N / 4))); [exact AP | lia]. }
      destruct (it_full true R F fc M ro S1 SP D N V P k lo [C8 w1; C8 w2] LH S1L S1H SPH LO D0 D2 HN K0 ltac:(lia)
                  ltac:(cbn; lia) V0 V2 V8 P0 ltac:(lia) P16 ltac:(lia) CG' CS' CF1 CF2' CV' BY' WP' ST GD GV' GP)
        as (R1 & M1 & RUN1 & LH1 & KP1 & MU1 & WM1 & ST1).
      assert (MU1' : munch [(P, P + 4 * (k + 1)); (S1 - 16, S1); (S1 + 64, S1 + 80)] m M1).
      { apply (munch_step _ [(P + 4 * k, P + 4 * k + 4); (S1 - 16, S1)] m M M1); [| exact MU1 |].
        - apply (munch_weaken [(P, P + 4 * k); (S1 - 16, S1); (S1 + 64, S1 + 80)]); [| exact MU].
          intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (X1 & X2 & X3 & _). repeat split; lia.
        - intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (X1 & X2 & X3 & _). repeat split; lia. }
      assert (CF1' : rw_cells asegs M1 (S1 + 64) [C8 (Z_to_bv 64 N); C8 (Z_to_bv 64 1)]).
      { eapply rw_cells_munch; [exact CF1 | exact MU1 | exact WM1 |]. intros x Hx. simpl in Hx. cbn [outside]. repeat split; lia. }
      destruct (IH R1 M1 (k + 1) ltac:(lia) ltac:(lia) LH1 MU1' (wmono_trans asegs _ _ _ WM WM1) ST1 CF1')
        as (R' & M' & RUN2 & LH' & KP2 & MU2 & WM2 & ST2).
      exists R', M'. split; [exact (CatSim.msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact LH'|].
      split; [exact (kept_in_trans _ _ _ _ KP1 KP2)|]. split; [exact MU2|]. split; [exact WM2 | exact ST2].
  Qed.

  Lemma lp_pro : forall R F fc m ro (S1 SP D N V lo : Z),
    getr R 2 = Z_to_bv 64 S1 -> getr R 8 = Z_to_bv 64 SP -> getr R 9 = Z_to_bv 64 S1 ->
    getr R 22 = Z_to_bv 64 SHBASE -> getr R 27 = Z_to_bv 64 N ->
    4 <= N < 2 ^ 26 -> 1 <= D < 2 ^ 47 -> 2 ^ 45 <= S1 -> S1 + 224 <= SP -> SP <= 2 ^ 47 -> lo <= S1 - 16 ->
    rw_cells asegs m (S1 + 80) [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 D)] -> stk asegs m lo SP ->
    exists R' M', CatSim.msteps asegs (MS R F (Z_to_bv 64 LP_TOP) fc None m ro) (MS R' F (Z_to_bv 64 LP_HEAD) fc None M' ro)
      /\ lh R' S1 SP N D 0 /\ kept_in KL R R'
      /\ munch [(S1 + 64, S1 + 80)] m M' /\ wmono asegs m M' /\ stk asegs M' lo SP
      /\ rw_cells asegs M' (S1 + 64) [C8 (Z_to_bv 64 N); C8 (Z_to_bv 64 1)].
  Proof.
    intros R F fc m ro S1 SP D N V lo H2 H8 H9 H22 H27 HN HD S1L S1H SPH LO CF ST.
    pose (E := Eseed R [Z_to_bv 64 0; Z_to_bv 64 S1; Z_to_bv 64 D; Z_to_bv 64 N; Z_to_bv 64 SP]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 33); (8%bv, EVar 36); (9%bv, EVar 33); (22%bv, ELit SHBASE); (27%bv, EVar 35)]) R)
      by it_regs.
    assert (HK : know_ok asegs E m [ KWord (SA (EVar 33) 88) 8 (EVar 34); KWr (SA (EVar 33) 64) (ELit 16);
                                     KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 34) 1 (2 ^ 47); KRange (EVar 35) 4 (2 ^ 26) ]).
    { unfold know_ok.
      apply Forall_cons; [eapply (kword_of_rw_cells _ _ _ _ _ 8%nat); [exact CF | reflexivity | reflexivity | lia
        | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off Z.of_nat Pos.of_succ_nat Pos.succ]; lia
        | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | reflexivity]|].
      apply Forall_cons; [eapply kwr_of_stk; [exact ST | | | ]; unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite ?u64_of_Z by lia; lia|].
      do 3 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; lia|]).
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R LP_TOP m ro HR HK 40%nat [LP_HEAD; LP_EXIT] (SCR [] [] []) 50%N.
    { split_scs. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (W64 : wr_at asegs m (S1 + 64) 16).
    { destruct ST as (T0 & T1 & T). split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (T (S1 + 64 + i) ltac:(lia))). }
    assert (C1 : rw_cells asegs M1 (S1 + 64) [C8 (Z_to_bv 64 N)]).
    { replace (Z_to_bv 64 N) with (edenot E (EVar 35)) by (evs; reflexivity). subst M1.
      apply (rw_cells_mem_denot_C8 E m []);
        [exact Hlf | constructor | unfold estart; cbn [a_base a_off]; evs; rewrite ?u64_of_Z by lia; reflexivity
        | eapply wr_at_sub; [exact W64 | lia | lia | lia]]. }
    assert (C2 : rw_cells asegs M1 (S1 + 72) [C8 (Z_to_bv 64 1)]).
    { replace (Z_to_bv 64 1) with (edenot E (ELit 1)) by reflexivity. subst M1.
      eapply (rw_cells_mem_denot_C8 E m [_]);
        [exact Hlf | | unfold estart; cbn [a_base a_off]; evs; rewrite ?u64_of_Z by lia; reflexivity
        | eapply wr_at_sub; [exact W64 | lia | lia | lia]].
      apply Forall_cons; [| apply Forall_nil]. cbn [e_addr e_width]. unfold estart; cbn [a_base a_off]; evs; rewrite ?u64_of_Z by lia.
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
    exists R', M1. split; [exact Hms|].
    rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 9%bv G9. rreg HR' 19%bv G19. rreg HR' 27%bv G27.
    rreg HR' 20%bv G20. rreg HR' 25%bv G25. rreg HR' 26%bv G26. rreg HR' 22%bv G22. rreg HR' 24%bv G24.
    split; [unfold lh; repeat match goal with |- _ /\ _ => split end; it_reg|].
    split; [intros r Hr; eapply (syms_id_sound R _ _ R' KL HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hr]|].
    split; [subst M1; apply munch_mem_denot; [exact Hlf|];
            repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia;
                                        cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]); apply Forall_nil|].
    split; [subst M1; apply wmono_mem_denot|].
    split; [subst M1; apply stk_mem_denot; exact ST|].
    apply rw_cells_cons8_c; [exact C1 | replace (S1 + 64 + 8) with (S1 + 72) by lia; exact C2].
  Qed.

  Lemma hLP : forall (x1 gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff D N P lo : Z) (ds bs : list byte),
    4 <= N < 2 ^ 26 -> D mod 16 = 0 -> AIMG_TOP <= D -> D + N <= 2 ^ 47 ->
    S1 mod 32 = 0 -> 2 ^ 45 <= S1 -> S1 + 224 <= SP -> SP <= 2 ^ 47 -> lo <= S1 - 16 ->
    AIMG_TOP <= ff -> ff + 4096 <= lo -> ff mod 64 = 0 ->
    P mod 16 = 0 -> AIMG_TOP <= P -> P + 4 * (N / 4) <= 2 ^ 47 -> (P + 4 * (N / 4) <= ALOWSH_LO \/ AHI_LO <= P) ->
    (D + N <= P \/ P + 4 * (N / 4) <= D) ->
    (ff + 2696 <= P \/ P + 4 * (N / 4) <= ff + 2672) -> (ff + 2696 <= D \/ D + N <= ff + 2672) ->
    (P + 4 * (N / 4) <= lo \/ SP <= P) -> (D + N <= lo \/ SP <= D) ->
    stk asegs m lo SP -> mem_inv asegs m -> ACONST m ->
    rw_cells asegs m (S1 + 80) [C8 (Z_to_bv 64 (ff + 2672)); C8 (Z_to_bv 64 D)] ->
    rw_cells asegs m (ff + 2672) [C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 (P + 4 * (N / 4))); C8 (Z_to_bv 64 (P + 4 * (N / 4)))] ->
    SHAD m (ff + 2672) (repeat (b8 0) 3) ->
    bytes_at asegs m D ds -> Z.of_nat (length ds) = N -> addressable m D N ->
    rw_cells asegs m P [CB (Z.to_nat (4 * (N / 4))) bs] -> addressable m P (4 * (N / 4)) ->
    evt asegs (fun ms' => exists x1' x10' x11' x12' x13' x14' x15' x16' x17' x18' x19' x20' x21' x22' x23' x24' x25' x26' x27' m1,
        ms' = MS (mkR x1' (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10' x11' x12' x13' x14' x15' x16' x17'
                      x18' x19' x20' x21' x22' x23' x24' x25' x26' x27' x28 x29 x30 x31) F (Z_to_bv 64 LP_EXIT) fc None m1 (seg_rom asegs)
        /\ munch [(P, P + 4 * (N / 4)); (S1 - 16, S1); (S1 + 64, S1 + 80)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
        /\ stk asegs m1 lo SP)
      (MS (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 (Z_to_bv 64 SHBASE) x23 x24 x25 x26 (Z_to_bv 64 N) x28 x29 x30 x31)
          F (Z_to_bv 64 0xe8a8c) fc None m (seg_rom asegs)).
  Proof.
    intros until bs. intros HN HD HD0 HD1 HS1 HS1b HS1c HSP Hlo Hff0 Hff1 Hff2 HP HP0 HP1 PB PD PV DV PST DST ST MI AC CF CV SV BD BL AD RCP AP.
    remember (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 (Z_to_bv 64 SHBASE) x23 x24 x25 x26 (Z_to_bv 64 N) x28 x29 x30 x31) as R0 eqn:HR0.
    pose proof (lp_arith N (N / 4) eq_refl ltac:(lia)) as (A1 & A2 & _).
    assert (H2 : getr R0 2 = Z_to_bv 64 S1) by (subst R0; reflexivity).
    assert (H8 : getr R0 8 = Z_to_bv 64 SP) by (subst R0; reflexivity).
    assert (H9 : getr R0 9 = Z_to_bv 64 S1) by (subst R0; reflexivity).
    assert (H22 : getr R0 22 = Z_to_bv 64 SHBASE) by (subst R0; reflexivity).
    assert (H27 : getr R0 27 = Z_to_bv 64 N) by (subst R0; reflexivity).
    destruct (lp_pro R0 F fc m (seg_rom asegs) S1 SP D N (ff + 2672) lo H2 H8 H9 H22 H27 HN ltac:(unfold AIMG_TOP in HD0; lia)
                HS1b HS1c HSP Hlo CF ST)
      as (R1 & M1 & RUN1 & LH1 & KP1 & MU1 & WM1 & ST1 & CF1).
    destruct (ACONST_shbase m AC) as (CG & CS).
    assert (BY : forall j, 0 <= j < N -> exists z, 0 <= z < 256 /\ rdn asegs m (Z_to_bv 64 (D + j)) 1 = Some [Z_to_bv 8 z]).
    { intros j Hj. apply (byte_of_bytes_at m D ds j BD). lia. }
    assert (WP : wr_at asegs m P (4 * (N / 4))).
    { destruct RCP as [_ WR]. cbn [cells_size csize] in WR. rewrite Nat.add_0_r, Z2Nat.id in WR by lia. exact WR. }
    assert (GV : gz m (ff + 2672) 1).
    { intros i Hi. unfold sh0. destruct (shk_of_SHAD m (ff + 2672) (repeat (b8 0) 3) (ff + 2672 + i) SV) as (b & Hb & Hs).
      { simpl. lia. }
      replace (Z.to_nat ((ff + 2672 + i - (ff + 2672)) / 8)) with 0%nat in Hb
        by (replace (ff + 2672 + i - (ff + 2672)) with 0 by lia; reflexivity).
      cbn [nth_error repeat] in Hb. assert (b = b8 0) by congruence. subst b. rewrite b8_unsigned in Hs by lia. exact Hs. }
    assert (MU1' : munch [(P, P + 4 * 0); (S1 - 16, S1); (S1 + 64, S1 + 80)] m M1).
    { apply (munch_weaken [(S1 + 64, S1 + 80)]); [| exact MU1]. intros x Hx. cbn [outside] in Hx |- *.
      destruct Hx as (X1 & X2 & X3 & _). repeat split; lia. }
    destruct (lp_loop m F fc (seg_rom asegs) S1 SP D N (ff + 2672) P lo (Z_to_bv 64 (P + 4 * (N / 4))) (Z_to_bv 64 (P + 4 * (N / 4)))
                HS1b HS1c HSP Hlo HD HD0 HD1 HN ltac:(lia) ltac:(lia) ltac:(clear - Hff2; Z.div_mod_to_equations; lia)
                HP0 HP1 HP PB PD ltac:(lia) PST DST CG CS CF CV BY WP AD AP GV
                (Nat.pred (Z.to_nat (N / 4))) R1 M1 0 ltac:(rewrite Nat.succ_pred_pos by lia; rewrite Z2Nat.id by lia; lia) ltac:(lia)
                LH1 MU1' WM1 ST1 CF1)
      as (R' & M' & RUN2 & LH' & KP2 & MU2 & WM2 & ST2).
    pose proof (CatSim.msteps_trans _ _ _ _ RUN1 RUN2) as RUN.
    assert (HF : rfull R0) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ RUN HF) as HF'. cbn [ms_regs] in HF'.
    pose proof (msteps_mem_inv asegs _ _ RUN MI) as MI'. cbn [ms_mem] in MI'.
    pose proof (kept_in_trans _ _ _ _ KP1 KP2) as KP.
    destruct LH' as (G2 & G8 & G9 & _).
    eapply evt_of_msteps; [exact RUN|]. apply evt_done. cbv beta.
    exists (getr R' 1), (getr R' 10), (getr R' 11), (getr R' 12), (getr R' 13), (getr R' 14), (getr R' 15), (getr R' 16), (getr R' 17),
      (getr R' 18), (getr R' 19), (getr R' 20), (getr R' 21), (getr R' 22), (getr R' 23), (getr R' 24), (getr R' 25), (getr R' 26),
      (getr R' 27), M'.
    split; [| split; [exact MU2 | split; [exact WM2 | split; [exact MI' | exact ST2]]]].
    f_equal. etransitivity; [exact (rfull_eq R' HF')|]. f_equal.
    all: first [ exact G2 | exact G8 | exact G9
               | match goal with |- getr _ ?r = _ => rewrite (KP r ltac:(unfold KL; cbn [In]; auto 20)), HR0; reflexivity end ].
  Qed.

  Lemma hLP0 : forall (x1 gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 N : Z),
    0 <= N < 4 ->
    evt asegs (fun ms' =>
        ms' = MS (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) (Z_to_bv 64 4) x11 x12 x13 x14 x15 x16 x17
                      x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 N) x28 x29 x30 x31)
                 F (Z_to_bv 64 LP_EXIT) fc None m (seg_rom asegs))
      (MS (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 N) x28 x29 x30 x31)
          F (Z_to_bv 64 0xe8a8c) fc None m (seg_rom asegs)).
  Proof.
    intros until N. intros HN.
    remember (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 N) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 N]).
    assert (HR : regs_ok E (srs sr_id [(27%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
    assert (HK : know_ok asegs E m [ KRange (EVar 32) 0 3 ]).
    { unfold know_ok. apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia | apply Forall_nil]. }
    xrun_at (PropExec.mkFP F fc) asegs R 0xe8a8c m (seg_rom asegs) HR HK 10%nat [LP_HEAD; LP_EXIT] (SCR [] [] []) 40%N.
    { split_scs. }
    clear HK.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 10%bv L10. rreg HR' 27%bv L27.
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L10, L27. cbn [mem_denot]. apply evt_done. reflexivity.
  Qed.
End TopL1.
