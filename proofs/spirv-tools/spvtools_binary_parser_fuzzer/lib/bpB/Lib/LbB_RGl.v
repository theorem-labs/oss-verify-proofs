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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsStack0.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition L2_HEAD : Z := 0x1006e8.
Definition L2_EXIT : Z := 0x10070c.

Definition KS : list reg := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition kept_in (ks : list reg) (R R' : bvmap 5 word) : Prop := forall r, In r ks -> getr R' r = getr R r.

Lemma kept_in_trans : forall ks R1 R2 R3, kept_in ks R1 R2 -> kept_in ks R2 R3 -> kept_in ks R1 R3.
Proof. intros ks R1 R2 R3 A B r Hr. rewrite (B r Hr). apply A. exact Hr. Qed.

Lemma wr_at_wm : forall m m' a n, wr_at asegs m a n -> wmono asegs m m' -> wr_at asegs m' a n.
Proof.
  intros m m' a n (W1 & W2 & W) WM. split; [lia|]. split; [lia|]. intros t Ht. apply WM. apply W. exact Ht.
Qed.

Lemma wr_at_sub : forall m a n a' n', wr_at asegs m a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' ->
  wr_at asegs m a' n'.
Proof.
  intros m a n a' n' (W1 & W2 & W) Ha1 Ha2 Hn. split; [lia|]. split; [lia|]. intros t Ht.
  replace (a' + t) with (a + (a' - a + t)) by lia. apply W. lia.
Qed.

Lemma l2_trip : forall R F fc M ro (i b : Z) (w : word),
  1 <= i <= 310 -> 2 ^ 45 <= b -> b + 8 * 312 <= 2 ^ 47 ->
  getr R 10 = Z_to_bv 64 i -> getr R 11 = Z_to_bv 64 (b + 8 * i) -> getr R 12 = Z_to_bv 64 312 ->
  rw_cells asegs M (b + 8 * i - 8) [C8 w] -> wr_at asegs M (b + 8 * i) 8 ->
  exists R' M' w', CatSim.msteps asegs (MS R F (Z_to_bv 64 L2_HEAD) fc None M ro) (MS R' F (Z_to_bv 64 L2_HEAD) fc None M' ro)
    /\ getr R' 10 = Z_to_bv 64 (i + 1) /\ getr R' 11 = Z_to_bv 64 (b + 8 * (i + 1)) /\ getr R' 12 = Z_to_bv 64 312
    /\ kept_in KS R R' /\ rw_cells asegs M' (b + 8 * i) [C8 w'] /\ munch [(b + 8 * i, b + 8 * i + 8)] M M'
    /\ wmono asegs M M'.
Proof.
  intros R F fc M ro i b w Hi Hb0 Hb1 H10 H11 H12 RC WR.
  pose (E := Eseed R [Z_to_bv 64 i; Z_to_bv 64 (b + 8 * i); w]).
  assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (12%bv, ELit 312)]) R).
  { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs;
    [exact H10 | exact H11 | exact H12]. }
  assert (HK : know_ok asegs E M [KWord (SA (EVar 33) (-8)) 8 (EVar 34); KWr (SA (EVar 33) 0) (ELit 8);
                                  KRange (EVar 32) 1 310; KRange (EVar 33) (2 ^ 45) (2 ^ 47 - 8)]).
  { unfold know_ok. apply Forall_cons.
    { eapply (kword_of_rw_cells asegs E M (b + 8 * i - 8) _ 0%nat (C8 w)); [exact RC | reflexivity | reflexivity | lia
        | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia | lia | lia | evs; reflexivity]. }
    apply Forall_cons.
    { eapply kwr_of_wr_at; [exact WR | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
        | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
    do 2 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]). apply Forall_nil. }
  xrun_at (PropExec.mkFP F fc) asegs R L2_HEAD M ro HR HK 40%nat [L2_HEAD] (SCR [] [] []) 35%N.
  { split_scs. }
  lazymatch type of Hlf with log_flat _ ?lg =>
    lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
      change mm with (mem_denot E M lg) in Hms; set (M1 := mem_denot E M lg) in Hms end end.
  assert (HB : bv_unsigned (edenot E (EVar 33)) = b + 8 * i) by (evs; rewrite u64_of_Z by lia; reflexivity).
  assert (WS : forall a, b + 8 * i <= a -> a + 8 <= b + 8 * i + 8 -> wr_at asegs M a 8).
  { intros a Ha1 Ha2. eapply wr_at_sub; [exact WR | lia | lia | lia]. }
  assert (MU : munch [(b + 8 * i, b + 8 * i + 8)] M M1).
  { pose proof (munch_mem_denot_sb [(0, 8)] (EVar 33) E M _ Hlf ltac:(vm_cast_no_check (@eq_refl bool true))) as MU.
    rewrite HB in MU. cbn [map fst snd] in MU. eapply munch_eqW; [exact MU | f_equal; f_equal; lia]. }
  assert (WM : wmono asegs M M1) by (subst M1; apply wmono_mem_denot).
  assert (CP : exists w', rw_cells asegs M1 (b + 8 * i) [C8 w']) by (eexists; subst M1; lgcell2 Hlf HB WS 0%nat).
  destruct CP as (w' & CP).
  exists R', M1, w'. split; [exact Hms|].
  rreg HR' 10%bv G10. rreg HR' 11%bv G11. rreg HR' 12%bv G12.
  split; [rewrite G10, w_add by lia; reflexivity|].
  split; [rewrite G11, w_add by lia; f_equal; lia|].
  split; [exact G12|].
  split; [intros r Hr; eapply (syms_id_sound R _ _ R' KS HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hr]|].
  split; [exact CP|]. split; [exact MU | exact WM].
Qed.

Lemma l2_last : forall R F fc M ro (b : Z) (w : word),
  2 ^ 45 <= b -> b + 8 * 312 <= 2 ^ 47 ->
  getr R 10 = Z_to_bv 64 311 -> getr R 11 = Z_to_bv 64 (b + 8 * 311) -> getr R 12 = Z_to_bv 64 312 ->
  rw_cells asegs M (b + 8 * 311 - 8) [C8 w] -> wr_at asegs M (b + 8 * 311) 8 ->
  exists R' M', CatSim.msteps asegs (MS R F (Z_to_bv 64 L2_HEAD) fc None M ro) (MS R' F (Z_to_bv 64 L2_EXIT) fc None M' ro)
    /\ kept_in KS R R' /\ munch [(b + 8 * 311, b + 8 * 311 + 8)] M M' /\ wmono asegs M M'.
Proof.
  intros R F fc M ro b w Hb0 Hb1 H10 H11 H12 RC WR.
  pose (E := Eseed R [Z_to_bv 64 311; Z_to_bv 64 (b + 8 * 311); w]).
  assert (HR : regs_ok E (srs sr_id [(10%bv, ELit 311); (11%bv, EVar 33); (12%bv, ELit 312)]) R).
  { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs;
    [exact H10 | exact H11 | exact H12]. }
  assert (HK : know_ok asegs E M [KWord (SA (EVar 33) (-8)) 8 (EVar 34); KWr (SA (EVar 33) 0) (ELit 8);
                                  KRange (EVar 33) (2 ^ 45) (2 ^ 47 - 8)]).
  { unfold know_ok. apply Forall_cons.
    { eapply (kword_of_rw_cells asegs E M (b + 8 * 311 - 8) _ 0%nat (C8 w)); [exact RC | reflexivity | reflexivity | lia
        | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia | lia | lia | evs; reflexivity]. }
    apply Forall_cons.
    { eapply kwr_of_wr_at; [exact WR | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
        | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
    apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]. apply Forall_nil. }
  xrun_at (PropExec.mkFP F fc) asegs R L2_HEAD M ro HR HK 40%nat [L2_HEAD; L2_EXIT] (SCR [] [] []) 35%N.
  { split_scs. }
  lazymatch type of Hlf with log_flat _ ?lg =>
    lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
      change mm with (mem_denot E M lg) in Hms; set (M1 := mem_denot E M lg) in Hms end end.
  assert (HB : bv_unsigned (edenot E (EVar 33)) = b + 8 * 311) by (evs; rewrite u64_of_Z by lia; reflexivity).
  assert (MU : munch [(b + 8 * 311, b + 8 * 311 + 8)] M M1).
  { pose proof (munch_mem_denot_sb [(0, 8)] (EVar 33) E M _ Hlf ltac:(vm_cast_no_check (@eq_refl bool true))) as MU.
    rewrite HB in MU. cbn [map fst snd] in MU. eapply munch_eqW; [exact MU | f_equal; f_equal; lia]. }
  assert (WM : wmono asegs M M1) by (subst M1; apply wmono_mem_denot).
  exists R', M1. split; [exact Hms|].
  split; [intros r Hr; eapply (syms_id_sound R _ _ R' KS HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hr]|].
  split; [exact MU | exact WM].
Qed.

Lemma l2_loop : forall (k : nat) R F fc M ro (i b : Z) (w : word),
  1 <= i -> i + Z.of_nat k = 311 -> 2 ^ 45 <= b -> b + 8 * 312 <= 2 ^ 47 ->
  getr R 10 = Z_to_bv 64 i -> getr R 11 = Z_to_bv 64 (b + 8 * i) -> getr R 12 = Z_to_bv 64 312 ->
  rw_cells asegs M (b + 8 * i - 8) [C8 w] -> wr_at asegs M (b + 8 * i) (8 * (312 - i)) ->
  exists R' M', CatSim.msteps asegs (MS R F (Z_to_bv 64 L2_HEAD) fc None M ro) (MS R' F (Z_to_bv 64 L2_EXIT) fc None M' ro)
    /\ kept_in KS R R' /\ munch [(b + 8 * i, b + 8 * 312)] M M' /\ wmono asegs M M'.
Proof.
  induction k as [|k IH]; intros R F fc M ro i b w Hi Hk Hb0 Hb1 H10 H11 H12 RC WR.
  - assert (i = 311) by lia. subst i.
    destruct (l2_last R F fc M ro b w Hb0 Hb1 H10 H11 H12 RC ltac:(eapply wr_at_sub; [exact WR | lia | lia | lia]))
      as (R' & M' & RUN & GK & MU & WM).
    exists R', M'. split; [exact RUN|]. split; [exact GK|]. split; [|exact WM].
    eapply munch_eqW; [exact MU | f_equal; f_equal; lia].
  - destruct (l2_trip R F fc M ro i b w ltac:(lia) Hb0 Hb1 H10 H11 H12 RC ltac:(eapply wr_at_sub; [exact WR | lia | lia | lia]))
      as (R1 & M1 & w1 & RUN1 & G10 & G11 & G12 & GK & CP & MU1 & WM1).
    destruct (IH R1 F fc M1 ro (i + 1) b w1 ltac:(lia) ltac:(lia) Hb0 Hb1 G10 G11 G12
                ltac:(replace (b + 8 * (i + 1) - 8) with (b + 8 * i) by lia; exact CP)
                ltac:(eapply wr_at_wm; [eapply wr_at_sub; [exact WR | lia | lia | lia] | exact WM1]))
      as (R2 & M2 & RUN2 & GK2 & MU2 & WM2).
    exists R2, M2. split; [exact (CatSim.msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact (kept_in_trans _ _ _ _ GK GK2)|].
    split; [| exact (wmono_trans asegs _ _ _ WM1 WM2)].
    eapply munch_trans; eapply munch_weaken; [| exact MU1 | | exact MU2]; intros z Hz; cbn [outside] in Hz |- *; lia.
Qed.

Ltac lh_sc := cbn [sc_denot]; evs; rewrite w_and by lia;
  change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8;
  lazymatch goal with |- context [?x mod 8] => pose proof (Z.mod_pos_bound x 8 ltac:(lia)) end;
  rewrite br_lts_small by lia; apply Z.ltb_lt; lia.

Lemma lh_kn : forall E M c v z,
  edenot E (EVar 32) = Z_to_bv 64 c -> edenot E (EVar 34) = Z_to_bv 64 v -> edenot E (EVar 35) = Z_to_bv 64 z ->
  0 <= c -> c + 1 < 2 ^ 47 -> shk M c v -> 0 <= v < 8 ->
  rdn asegs M (Z_to_bv 64 c) 1 = Some [Z_to_bv 8 z] -> 0 <= z < 256 ->
  kentry_ok asegs E M (KWord (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) SHBASE) 1 (EVar 34))
  /\ kentry_ok asegs E M (KWord (SA (EVar 32) 0) 1 (EVar 35)).
Proof.
  intros E M c v z Ec Ev Ez Hc0 Hc1 HSH Hv HZ Hz. split.
  - eapply kshadow with (x := c) (k := v); [exact Ec | lia | lia | exact Ev | exact HSH].
  - cbn [kentry_ok]. split; [lia|]. split.
    + unfold flat, estart, elenZ. cbn [a_base a_off]. rewrite Ec, u64_of_Z by lia. lia.
    + unfold adenot. cbn [a_base a_off]. rewrite Ec. rewrite v_addi_Z by lia. replace (c + 0) with c by lia.
      rewrite rdn_HL, HZ, Ez. rewrite word_to_le_bytes_1 by lia. reflexivity.
Qed.

Definition LH_HEAD : Z := 0x100950.
Definition LH_EXIT : Z := 0x10098c.

Definition KSH : list reg := [1; 2; 3; 4; 8; 9; 10; 13; 14; 17; 18; 21; 22; 23; 24; 25; 26; 27]%bv.

Lemma lh_kn2 : forall E M e ev ez x v z,
  edenot E e = Z_to_bv 64 x -> edenot E ev = Z_to_bv 64 v -> edenot E ez = Z_to_bv 64 z ->
  0 <= x -> x + 1 < 2 ^ 47 -> shk M x v -> 0 <= v < 8 ->
  rdn asegs M (Z_to_bv 64 x) 1 = Some [Z_to_bv 8 z] -> 0 <= z < 256 ->
  kentry_ok asegs E M (KWord (SA (EAlu ALU_SRL e (ELit 3)) SHBASE) 1 ev)
  /\ kentry_ok asegs E M (KWord (SA e 0) 1 ez).
Proof.
  intros E M e ev ez x v z Ex Ev Ez Hx0 Hx1 HSH Hv HZ Hz. split.
  - eapply kshadow with (x := x) (k := v); [exact Ex | lia | lia | exact Ev | exact HSH].
  - cbn [kentry_ok]. split; [lia|]. split.
    + unfold flat, estart, elenZ. cbn [a_base a_off]. rewrite Ex, u64_of_Z by lia. lia.
    + unfold adenot. cbn [a_base a_off]. rewrite Ex. rewrite v_addi_Z by lia. replace (x + 0) with x by lia.
      rewrite rdn_HL, HZ, Ez. rewrite word_to_le_bytes_1 by lia. reflexivity.
Qed.

Ltac lh_sc2 :=
  cbn [sc_denot]; evs; rewrite ?w_add by lia;
  first [ rewrite br_ne by lia; first [ apply negb_true_iff, Z.eqb_neq; lia | apply negb_false_iff, Z.eqb_eq; lia ]
        | rewrite w_and by lia; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8;
          lazymatch goal with |- context [?y mod 8] => pose proof (Z.mod_pos_bound y 8 ltac:(lia)) end;
          rewrite br_lts_small by lia; apply Z.ltb_lt; lia ].

Definition LH_SR (last : bool) : list expr :=
  srs sr_id [(19%bv, EVar 32); (15%bv, EVar 33); (16%bv, if last then EAlu ALU_ADD (EVar 33) (ELit 1) else EVar 34);
             (5%bv, EVar 35); (20%bv, ELit SHBASE)].
Definition LH_KN : list kentry :=
  [ KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (EVar 33)) (ELit 3)) SHBASE) 1 (EVar 36);
    KWord (SA (EAlu ALU_ADD (EVar 32) (EVar 33)) 0) 1 (EVar 37);
    KRange (EVar 32) 0 (2 ^ 47); KRange (EVar 33) 0 (2 ^ 47); KRange (EVar 35) (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 1);
    KRange (EVar 36) 0 7; KRange (EVar 37) 0 255 ].

Lemma lh_kn_all : forall R M (c j n v z : Z),
  0 <= c -> 0 <= j -> c + j + 1 < 2 ^ 47 -> shk M (c + j) v -> 0 <= v < 8 ->
  rdn asegs M (Z_to_bv 64 (c + j)) 1 = Some [Z_to_bv 8 z] -> 0 <= z < 256 ->
  know_ok asegs (Eseed R [Z_to_bv 64 c; Z_to_bv 64 j; Z_to_bv 64 n; Z_to_bv 64 (2 ^ 64 - 1 - c); Z_to_bv 64 v; Z_to_bv 64 z])
    M LH_KN.
Proof.
  intros R M c j n v z Hc Hj Hcj HSH Hv HZ Hz.
  destruct (lh_kn2 (Eseed R [Z_to_bv 64 c; Z_to_bv 64 j; Z_to_bv 64 n; Z_to_bv 64 (2 ^ 64 - 1 - c); Z_to_bv 64 v; Z_to_bv 64 z])
              M (EAlu ALU_ADD (EVar 32) (EVar 33)) (EVar 36) (EVar 37) (c + j) v z
              ltac:(evs; rewrite w_add by lia; reflexivity) ltac:(evs; reflexivity) ltac:(evs; reflexivity)
              ltac:(lia) ltac:(lia) HSH Hv HZ Hz) as [K1 K2].
  unfold know_ok, LH_KN. apply Forall_cons; [exact K1|]. apply Forall_cons; [exact K2|].
  repeat (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]). apply Forall_nil.
Qed.

Lemma lh_mid : forall R F fc M ro (c j n v z : Z),
  getr R 19 = Z_to_bv 64 c -> getr R 15 = Z_to_bv 64 j -> getr R 16 = Z_to_bv 64 n ->
  getr R 5 = Z_to_bv 64 (2 ^ 64 - 1 - c) -> getr R 20 = Z_to_bv 64 SHBASE ->
  0 <= c -> 0 <= j -> j + 1 < n -> c + n < 2 ^ 47 ->
  shk M (c + j) v -> 0 <= v < 8 -> (v = 0 \/ (c + j) mod 8 < v) ->
  rdn asegs M (Z_to_bv 64 (c + j)) 1 = Some [Z_to_bv 8 z] -> 0 <= z < 256 ->
  exists R', CatSim.msteps asegs (MS R F (Z_to_bv 64 LH_HEAD) fc None M ro) (MS R' F (Z_to_bv 64 LH_HEAD) fc None M ro)
    /\ getr R' 19 = Z_to_bv 64 c /\ getr R' 15 = Z_to_bv 64 (j + 1) /\ getr R' 16 = Z_to_bv 64 n
    /\ getr R' 5 = Z_to_bv 64 (2 ^ 64 - 1 - c) /\ getr R' 20 = Z_to_bv 64 SHBASE /\ kept_in KSH R R'.
Proof.
  intros R F fc M ro c j n v z H19 H15 H16 H5 H20 Hc Hj Hjn Hcn HSH Hv Hvc HZ Hz.
  pose (E := Eseed R [Z_to_bv 64 c; Z_to_bv 64 j; Z_to_bv 64 n; Z_to_bv 64 (2 ^ 64 - 1 - c); Z_to_bv 64 v; Z_to_bv 64 z]).
  assert (HR : regs_ok E (LH_SR false) R).
  { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs;
    [exact H19 | exact H15 | exact H16 | exact H5 | exact H20]. }
  assert (HK : know_ok asegs E M LH_KN) by (subst E; apply lh_kn_all; (lia || assumption)).
  destruct Hvc as [Hv0|Hvc].
  - xrun_at (PropExec.mkFP F fc) asegs R LH_HEAD M ro HR HK 40%nat [LH_HEAD; LH_EXIT] (SCR [false; true] [] []) 38%N.
    { split_scs; lh_sc2. }
    exists R'. split; [exact Hms|].
    rreg HR' 19%bv G19. rreg HR' 15%bv G15. rreg HR' 16%bv G16. rreg HR' 5%bv G5. rreg HR' 20%bv G20.
    split; [exact G19|]. split; [rewrite G15, w_add by lia; reflexivity|]. split; [exact G16|].
    split; [exact G5|]. split; [exact G20|].
    intros r Hr. eapply (syms_id_sound R _ _ R' KSH HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hr].
  - xrun_at (PropExec.mkFP F fc) asegs R LH_HEAD M ro HR HK 40%nat [LH_HEAD; LH_EXIT] (SCR [true; true; true] [] []) 38%N.
    { split_scs; lh_sc2. }
    exists R'. split; [exact Hms|].
    rreg HR' 19%bv G19. rreg HR' 15%bv G15. rreg HR' 16%bv G16. rreg HR' 5%bv G5. rreg HR' 20%bv G20.
    split; [exact G19|]. split; [rewrite G15, w_add by lia; reflexivity|]. split; [exact G16|].
    split; [exact G5|]. split; [exact G20|].
    intros r Hr. eapply (syms_id_sound R _ _ R' KSH HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hr].
Qed.

Lemma lh_last : forall R F fc M ro (c j v z : Z),
  getr R 19 = Z_to_bv 64 c -> getr R 15 = Z_to_bv 64 j -> getr R 16 = Z_to_bv 64 (j + 1) ->
  getr R 5 = Z_to_bv 64 (2 ^ 64 - 1 - c) -> getr R 20 = Z_to_bv 64 SHBASE ->
  0 <= c -> 0 <= j -> c + j + 1 < 2 ^ 47 ->
  shk M (c + j) v -> 0 <= v < 8 -> (v = 0 \/ (c + j) mod 8 < v) ->
  rdn asegs M (Z_to_bv 64 (c + j)) 1 = Some [Z_to_bv 8 z] -> 0 <= z < 256 ->
  exists R', CatSim.msteps asegs (MS R F (Z_to_bv 64 LH_HEAD) fc None M ro) (MS R' F (Z_to_bv 64 LH_EXIT) fc None M ro)
    /\ getr R' 15 = Z_to_bv 64 (j + 1) /\ getr R' 20 = Z_to_bv 64 SHBASE /\ kept_in KSH R R'.
Proof.
  intros R F fc M ro c j v z H19 H15 H16 H5 H20 Hc Hj Hcj HSH Hv Hvc HZ Hz.
  pose (E := Eseed R [Z_to_bv 64 c; Z_to_bv 64 j; Z_to_bv 64 (j + 1); Z_to_bv 64 (2 ^ 64 - 1 - c); Z_to_bv 64 v; Z_to_bv 64 z]).
  assert (HR : regs_ok E (LH_SR true) R).
  { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs;
    [exact H19 | exact H15 | rewrite H16, w_add by lia; reflexivity | exact H5 | exact H20]. }
  assert (HK : know_ok asegs E M LH_KN) by (subst E; apply lh_kn_all; (lia || assumption)).
  destruct Hvc as [Hv0|Hvc].
  - xrun_at (PropExec.mkFP F fc) asegs R LH_HEAD M ro HR HK 40%nat [LH_HEAD; LH_EXIT] (SCR [false] [] []) 38%N.
    { split_scs; lh_sc2. }
    exists R'. split; [exact Hms|].
    rreg HR' 15%bv G15. rreg HR' 20%bv G20.
    split; [rewrite G15, w_add by lia; reflexivity|]. split; [exact G20|].
    intros r Hr. eapply (syms_id_sound R _ _ R' KSH HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hr].
  - xrun_at (PropExec.mkFP F fc) asegs R LH_HEAD M ro HR HK 40%nat [LH_HEAD; LH_EXIT] (SCR [true; true] [] []) 38%N.
    { split_scs; lh_sc2. }
    exists R'. split; [exact Hms|].
    rreg HR' 15%bv G15. rreg HR' 20%bv G20.
    split; [rewrite G15, w_add by lia; reflexivity|]. split; [exact G20|].
    intros r Hr. eapply (syms_id_sound R _ _ R' KSH HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hr].
Qed.

Lemma shk_of_accessible : forall M c n x, accessible M c n -> c <= x < c + n ->
  exists v, shk M x v /\ 0 <= v < 8 /\ (v = 0 \/ x mod 8 < v).
Proof.
  intros M c n x (A0 & A1 & AC) Hx. destruct (AC x Hx) as (v & Hv & Hrd & Hok).
  exists v. split; [| split; [exact Hv|]].
  - pose proof (shk_of_mrd M x (b8 v) ltac:(lia) Hrd) as K. unfold b8 in K. rewrite Z_to_bv_unsigned in K.
    rewrite bv_wrap_small in K by (change (bv_modulus 8) with 256; lia). exact K.
  - unfold byte_ok in Hok. lia.
Qed.

Lemma lh_loop : forall (k : nat) R F fc M ro (c j : Z),
  getr R 19 = Z_to_bv 64 c -> getr R 15 = Z_to_bv 64 j -> getr R 16 = Z_to_bv 64 (j + Z.of_nat (S k)) ->
  getr R 5 = Z_to_bv 64 (2 ^ 64 - 1 - c) -> getr R 20 = Z_to_bv 64 SHBASE ->
  0 <= c -> 0 <= j -> c + j + Z.of_nat (S k) < 2 ^ 47 ->
  accessible M (c + j) (Z.of_nat (S k)) ->
  (forall t, 0 <= t < Z.of_nat (S k) -> exists z, 0 <= z < 256 /\ rdn asegs M (Z_to_bv 64 (c + j + t)) 1 = Some [Z_to_bv 8 z]) ->
  exists R', CatSim.msteps asegs (MS R F (Z_to_bv 64 LH_HEAD) fc None M ro) (MS R' F (Z_to_bv 64 LH_EXIT) fc None M ro)
    /\ kept_in KSH R R' /\ getr R' 20 = Z_to_bv 64 SHBASE /\ getr R' 15 = Z_to_bv 64 (j + Z.of_nat (S k)).
Proof.
  induction k as [|k IH]; intros R F fc M ro c j H19 H15 H16 H5 H20 Hc Hj Hn ACC BYT.
  - destruct (shk_of_accessible M (c + j) _ (c + j) ACC ltac:(cbn; lia)) as (v & HSH & Hv & Hvc).
    destruct (BYT 0 ltac:(cbn; lia)) as (z & Hz & HZ). rewrite Z.add_0_r in HZ.
    destruct (lh_last R F fc M ro c j v z H19 H15 ltac:(rewrite H16; f_equal; lia) H5 H20 Hc Hj ltac:(cbn in Hn; lia)
                HSH Hv Hvc HZ Hz) as (R1 & RUN & G15 & G20 & GK).
    exists R1. split; [exact RUN|]. split; [exact GK|]. split; [exact G20|]. rewrite G15. f_equal; lia.
  - destruct (shk_of_accessible M (c + j) _ (c + j) ACC ltac:(lia)) as (v & HSH & Hv & Hvc).
    destruct (BYT 0 ltac:(lia)) as (z & Hz & HZ). rewrite Z.add_0_r in HZ.
    destruct (lh_mid R F fc M ro c j (j + Z.of_nat (S (S k))) v z H19 H15 H16 H5 H20 Hc Hj ltac:(lia) ltac:(lia)
                HSH Hv Hvc HZ Hz) as (R1 & RUN & G19 & G15 & G16 & G5 & G20 & GK).
    assert (ACC1 : accessible M (c + (j + 1)) (Z.of_nat (S k))).
    { destruct ACC as (A0 & A1 & AC). split; [lia|]. split; [lia|]. intros x Hx. apply AC. lia. }
    assert (BYT1 : forall t, 0 <= t < Z.of_nat (S k) ->
                   exists z, 0 <= z < 256 /\ rdn asegs M (Z_to_bv 64 (c + (j + 1) + t)) 1 = Some [Z_to_bv 8 z]).
    { intros t Ht. destruct (BYT (t + 1) ltac:(lia)) as (z' & Hz' & HZ'). exists z'. split; [exact Hz'|].
      replace (c + (j + 1) + t) with (c + j + (t + 1)) by lia. exact HZ'. }
    destruct (IH R1 F fc M ro c (j + 1) G19 G15 ltac:(rewrite G16; f_equal; lia) G5 G20 Hc ltac:(lia) ltac:(lia) ACC1 BYT1)
      as (R2 & RUN2 & GK2 & G20' & G15').
    exists R2. split; [exact (CatSim.msteps_trans _ _ _ _ RUN RUN2)|]. split; [exact (kept_in_trans _ _ _ _ GK GK2)|].
    split; [exact G20'|]. rewrite G15'. f_equal; lia.
Qed.