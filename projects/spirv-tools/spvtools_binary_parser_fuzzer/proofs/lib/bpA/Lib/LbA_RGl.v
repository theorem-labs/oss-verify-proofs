(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HMState HMem HCells HExec HLFrame HStep TacX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsStack0.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition L2_HEAD : Z := 0xfef48.
Definition L2_EXIT : Z := 0xfef64.

Definition KS : list reg := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition kept_in (ks : list reg) (R R' : bvmap 5 word) : Prop := forall r, In r ks -> getr R' r = getr R r.

Lemma kept_in_trans : forall ks R1 R2 R3, kept_in ks R1 R2 -> kept_in ks R2 R3 -> kept_in ks R1 R3.
Proof. intros ks R1 R2 R3 A B r Hr. rewrite (B r Hr). apply A. exact Hr. Qed.

Lemma l2_trip : forall R F fc M ro (i : Z),
  1 <= i <= 310 -> getr R 11 = Z_to_bv 64 i -> getr R 12 = Z_to_bv 64 (312 - i) ->
  exists R', CatSim.msteps asegs (MS R F (Z_to_bv 64 L2_HEAD) fc None M ro) (MS R' F (Z_to_bv 64 L2_HEAD) fc None M ro)
    /\ getr R' 11 = Z_to_bv 64 (i + 1) /\ getr R' 12 = Z_to_bv 64 (312 - (i + 1)) /\ kept_in KS R R'.
Proof.
  intros R F fc M ro i Hi H11 H12.
  pose (E := Eseed R [Z_to_bv 64 i; Z_to_bv 64 (312 - i)]).
  assert (HR : regs_ok E (srs sr_id [(11%bv, EVar 32); (12%bv, EVar 33)]) R).
  { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; [exact H11 | exact H12]. }
  assert (HK : know_ok asegs E M [KRange (EVar 32) 1 310; KRange (EVar 33) 2 311]).
  { unfold know_ok. apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|].
    apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia | apply Forall_nil]. }
  xrun_at (PropExec.mkFP F fc) asegs R L2_HEAD M ro HR HK 20%nat [L2_HEAD] (SCR [true] [] []) 40%N.
  { split_scs. }
  exists R'. split; [exact Hms|]. rreg HR' 11%bv G11. rreg HR' 12%bv G12.
  split; [rewrite G11, w_add by lia; reflexivity|]. split; [rewrite G12, w_addm by lia; f_equal; lia|].
  intros r Hr. eapply (syms_id_sound R _ _ R' KS HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hr].
Qed.

Lemma l2_last : forall R F fc M ro,
  getr R 11 = Z_to_bv 64 311 -> getr R 12 = Z_to_bv 64 1 ->
  exists R', CatSim.msteps asegs (MS R F (Z_to_bv 64 L2_HEAD) fc None M ro) (MS R' F (Z_to_bv 64 L2_EXIT) fc None M ro)
    /\ kept_in KS R R'.
Proof.
  intros R F fc M ro H11 H12.
  pose (E := Eseed R []).
  assert (HR : regs_ok E (srs sr_id [(11%bv, ELit 311); (12%bv, ELit 1)]) R).
  { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; [exact H11 | exact H12]. }
  assert (HK : know_ok asegs E M []) by (unfold know_ok; apply Forall_nil).
  xrun_at (PropExec.mkFP F fc) asegs R L2_HEAD M ro HR HK 20%nat [L2_HEAD; L2_EXIT] (SCR [] [] []) 40%N.
  { split_scs. }
  exists R'. split; [exact Hms|].
  intros r Hr. eapply (syms_id_sound R _ _ R' KS HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hr].
Qed.

Lemma l2_loop : forall (k : nat) R F fc M ro (i : Z),
  1 <= i -> i + Z.of_nat k = 311 -> getr R 11 = Z_to_bv 64 i -> getr R 12 = Z_to_bv 64 (312 - i) ->
  exists R', CatSim.msteps asegs (MS R F (Z_to_bv 64 L2_HEAD) fc None M ro) (MS R' F (Z_to_bv 64 L2_EXIT) fc None M ro)
    /\ kept_in KS R R'.
Proof.
  induction k as [|k IH]; intros R F fc M ro i Hi Hk H11 H12.
  - assert (i = 311) by lia. subst i. apply l2_last; [exact H11 | exact H12].
  - destruct (l2_trip R F fc M ro i ltac:(lia) H11 H12) as (R1 & RUN1 & G11 & G12 & GK).
    destruct (IH R1 F fc M ro (i + 1) ltac:(lia) ltac:(lia) G11 G12) as (R2 & RUN2 & GK2).
    exists R2. split; [exact (CatSim.msteps_trans _ _ _ _ RUN1 RUN2) | exact (kept_in_trans _ _ _ _ GK GK2)].
Qed.

Definition LH_HEAD : Z := 0xff198.
Definition LH_EXIT : Z := 0xff1d4.

Definition KSH : list reg := [1; 2; 3; 4; 8; 9; 10; 12; 13; 19; 21; 22; 23; 24; 25; 26; 27]%bv.

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

#[local] Definition HTLbARGl_0 : list (reg * expr) := [(18%bv, EVar 32); (16%bv, EVar 32); (14%bv, EVar 33); (20%bv, ELit 2147450880)].
Lemma lh_mid0 : forall R F fc M ro (c k v z : Z),
  getr R 18 = Z_to_bv 64 c -> getr R 16 = Z_to_bv 64 c -> getr R 14 = Z_to_bv 64 k -> getr R 20 = Z_to_bv 64 0x7fff8000 ->
  2 <= k <= 32 -> 0 <= c -> c + 1 < 2 ^ 47 ->
  shk M c v -> v = 0 ->
  rdn asegs M (Z_to_bv 64 c) 1 = Some [Z_to_bv 8 z] -> 0 <= z < 256 ->
  exists R', CatSim.msteps asegs (MS R F (Z_to_bv 64 LH_HEAD) fc None M ro) (MS R' F (Z_to_bv 64 LH_HEAD) fc None M ro)
    /\ getr R' 18 = Z_to_bv 64 (c + 1) /\ getr R' 16 = Z_to_bv 64 (c + 1) /\ getr R' 14 = Z_to_bv 64 (k - 1)
    /\ getr R' 20 = Z_to_bv 64 0x7fff8000 /\ getr R' 15 = getr R 15 /\ kept_in KSH R R'.
Proof.
  intros R F fc M ro c k v z H18 H16 H14 H20 Hk Hc0 Hc1 HSH Hv0 HZ Hz.
  subst v.
  pose (E := Eseed R [Z_to_bv 64 c; Z_to_bv 64 k; Z_to_bv 64 0; Z_to_bv 64 z]).
  assert (HR : regs_ok E (srs sr_id HTLbARGl_0) R).
  { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs;
    [exact H18 | exact H16 | exact H14 | exact H20]. }
  assert (HK : know_ok asegs E M
     [ KWord (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) SHBASE) 1 (EVar 34); KWord (SA (EVar 32) 0) 1 (EVar 35);
       KRange (EVar 32) 0 (2 ^ 47); KRange (EVar 33) 2 32; KRange (EVar 34) 0 0; KRange (EVar 35) 0 255 ]).
  { destruct (lh_kn E M c 0 z ltac:(evs; reflexivity) ltac:(evs; reflexivity) ltac:(evs; reflexivity) Hc0 Hc1 HSH ltac:(lia) HZ Hz) as [K1 K2].
    unfold know_ok. apply Forall_cons; [exact K1|]. apply Forall_cons; [exact K2|].
    repeat (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]). apply Forall_nil. }
  xrun_at (PropExec.mkFP F fc) asegs R LH_HEAD M ro HR HK 40%nat [LH_HEAD; LH_EXIT] (SCR [false] [] []) 40%N.
  { split_scs; lh_sc. }
  exists R'. split; [exact Hms|].
  rreg HR' 18%bv G18. rreg HR' 16%bv G16. rreg HR' 14%bv G14. rreg HR' 20%bv G20. rreg HR' 15%bv G15.
  split; [rewrite G18, w_add by lia; reflexivity|]. split; [rewrite G16, w_add by lia; reflexivity|].
  split; [rewrite G14; first [rewrite w_addm by lia; f_equal; lia | f_equal; lia]|]. split; [exact G20|].
  split; [rewrite G15; reflexivity|].
  intros r Hr. eapply (syms_id_sound R _ _ R' KSH HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hr].
Qed.

Lemma lh_mid1 : forall R F fc M ro (c k v z : Z),
  getr R 18 = Z_to_bv 64 c -> getr R 16 = Z_to_bv 64 c -> getr R 14 = Z_to_bv 64 k -> getr R 20 = Z_to_bv 64 0x7fff8000 ->
  2 <= k <= 32 -> 0 <= c -> c + 1 < 2 ^ 47 ->
  shk M c v -> 1 <= v < 8 -> c mod 8 < v ->
  rdn asegs M (Z_to_bv 64 c) 1 = Some [Z_to_bv 8 z] -> 0 <= z < 256 ->
  exists R', CatSim.msteps asegs (MS R F (Z_to_bv 64 LH_HEAD) fc None M ro) (MS R' F (Z_to_bv 64 LH_HEAD) fc None M ro)
    /\ getr R' 18 = Z_to_bv 64 (c + 1) /\ getr R' 16 = Z_to_bv 64 (c + 1) /\ getr R' 14 = Z_to_bv 64 (k - 1)
    /\ getr R' 20 = Z_to_bv 64 0x7fff8000 /\ getr R' 15 = getr R 15 /\ kept_in KSH R R'.
Proof.
  intros R F fc M ro c k v z H18 H16 H14 H20 Hk Hc0 Hc1 HSH Hv1 Hvc HZ Hz.

  pose (E := Eseed R [Z_to_bv 64 c; Z_to_bv 64 k; Z_to_bv 64 v; Z_to_bv 64 z]).
  assert (HR : regs_ok E (srs sr_id HTLbARGl_0) R).
  { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs;
    [exact H18 | exact H16 | exact H14 | exact H20]. }
  assert (HK : know_ok asegs E M
     [ KWord (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) SHBASE) 1 (EVar 34); KWord (SA (EVar 32) 0) 1 (EVar 35);
       KRange (EVar 32) 0 (2 ^ 47); KRange (EVar 33) 2 32; KRange (EVar 34) 1 7; KRange (EVar 35) 0 255 ]).
  { destruct (lh_kn E M c v z ltac:(evs; reflexivity) ltac:(evs; reflexivity) ltac:(evs; reflexivity) Hc0 Hc1 HSH ltac:(lia) HZ Hz) as [K1 K2].
    unfold know_ok. apply Forall_cons; [exact K1|]. apply Forall_cons; [exact K2|].
    repeat (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]). apply Forall_nil. }
  xrun_at (PropExec.mkFP F fc) asegs R LH_HEAD M ro HR HK 40%nat [LH_HEAD; LH_EXIT] (SCR [true; true] [] []) 40%N.
  { split_scs; lh_sc. }
  exists R'. split; [exact Hms|].
  rreg HR' 18%bv G18. rreg HR' 16%bv G16. rreg HR' 14%bv G14. rreg HR' 20%bv G20. rreg HR' 15%bv G15.
  split; [rewrite G18, w_add by lia; reflexivity|]. split; [rewrite G16, w_add by lia; reflexivity|].
  split; [rewrite G14; first [rewrite w_addm by lia; f_equal; lia | f_equal; lia]|]. split; [exact G20|].
  split; [rewrite G15; reflexivity|].
  intros r Hr. eapply (syms_id_sound R _ _ R' KSH HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hr].
Qed.

Lemma lh_last0 : forall R F fc M ro (c k v z : Z),
  getr R 18 = Z_to_bv 64 c -> getr R 16 = Z_to_bv 64 c -> getr R 14 = Z_to_bv 64 k -> getr R 20 = Z_to_bv 64 0x7fff8000 ->
  k = 1 -> 0 <= c -> c + 1 < 2 ^ 47 ->
  shk M c v -> v = 0 ->
  rdn asegs M (Z_to_bv 64 c) 1 = Some [Z_to_bv 8 z] -> 0 <= z < 256 ->
  exists R', CatSim.msteps asegs (MS R F (Z_to_bv 64 LH_HEAD) fc None M ro) (MS R' F (Z_to_bv 64 LH_EXIT) fc None M ro)
    /\ getr R' 18 = Z_to_bv 64 (c + 1) /\ getr R' 16 = Z_to_bv 64 (c + 1) /\ getr R' 14 = Z_to_bv 64 (k - 1)
    /\ getr R' 20 = Z_to_bv 64 0x7fff8000 /\ getr R' 15 = getr R 15 /\ kept_in KSH R R'.
Proof.
  intros R F fc M ro c k v z H18 H16 H14 H20 Hk Hc0 Hc1 HSH Hv0 HZ Hz.
  subst v.
  pose (E := Eseed R [Z_to_bv 64 c; Z_to_bv 64 k; Z_to_bv 64 0; Z_to_bv 64 z]).
  assert (HR : regs_ok E (srs sr_id HTLbARGl_0) R).
  { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs;
    [exact H18 | exact H16 | exact H14 | exact H20]. }
  assert (HK : know_ok asegs E M
     [ KWord (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) SHBASE) 1 (EVar 34); KWord (SA (EVar 32) 0) 1 (EVar 35);
       KRange (EVar 32) 0 (2 ^ 47); KRange (EVar 33) 1 1; KRange (EVar 34) 0 0; KRange (EVar 35) 0 255 ]).
  { destruct (lh_kn E M c 0 z ltac:(evs; reflexivity) ltac:(evs; reflexivity) ltac:(evs; reflexivity) Hc0 Hc1 HSH ltac:(lia) HZ Hz) as [K1 K2].
    unfold know_ok. apply Forall_cons; [exact K1|]. apply Forall_cons; [exact K2|].
    repeat (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]). apply Forall_nil. }
  xrun_at (PropExec.mkFP F fc) asegs R LH_HEAD M ro HR HK 40%nat [LH_HEAD; LH_EXIT] (SCR [false] [] []) 40%N.
  { split_scs; lh_sc. }
  exists R'. split; [exact Hms|].
  rreg HR' 18%bv G18. rreg HR' 16%bv G16. rreg HR' 14%bv G14. rreg HR' 20%bv G20. rreg HR' 15%bv G15.
  split; [rewrite G18, w_add by lia; reflexivity|]. split; [rewrite G16, w_add by lia; reflexivity|].
  split; [rewrite G14; first [rewrite w_addm by lia; f_equal; lia | f_equal; lia]|]. split; [exact G20|].
  split; [rewrite G15; reflexivity|].
  intros r Hr. eapply (syms_id_sound R _ _ R' KSH HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hr].
Qed.

Lemma lh_last1 : forall R F fc M ro (c k v z : Z),
  getr R 18 = Z_to_bv 64 c -> getr R 16 = Z_to_bv 64 c -> getr R 14 = Z_to_bv 64 k -> getr R 20 = Z_to_bv 64 0x7fff8000 ->
  k = 1 -> 0 <= c -> c + 1 < 2 ^ 47 ->
  shk M c v -> 1 <= v < 8 -> c mod 8 < v ->
  rdn asegs M (Z_to_bv 64 c) 1 = Some [Z_to_bv 8 z] -> 0 <= z < 256 ->
  exists R', CatSim.msteps asegs (MS R F (Z_to_bv 64 LH_HEAD) fc None M ro) (MS R' F (Z_to_bv 64 LH_EXIT) fc None M ro)
    /\ getr R' 18 = Z_to_bv 64 (c + 1) /\ getr R' 16 = Z_to_bv 64 (c + 1) /\ getr R' 14 = Z_to_bv 64 (k - 1)
    /\ getr R' 20 = Z_to_bv 64 0x7fff8000 /\ getr R' 15 = getr R 15 /\ kept_in KSH R R'.
Proof.
  intros R F fc M ro c k v z H18 H16 H14 H20 Hk Hc0 Hc1 HSH Hv1 Hvc HZ Hz.

  pose (E := Eseed R [Z_to_bv 64 c; Z_to_bv 64 k; Z_to_bv 64 v; Z_to_bv 64 z]).
  assert (HR : regs_ok E (srs sr_id HTLbARGl_0) R).
  { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs;
    [exact H18 | exact H16 | exact H14 | exact H20]. }
  assert (HK : know_ok asegs E M
     [ KWord (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) SHBASE) 1 (EVar 34); KWord (SA (EVar 32) 0) 1 (EVar 35);
       KRange (EVar 32) 0 (2 ^ 47); KRange (EVar 33) 1 1; KRange (EVar 34) 1 7; KRange (EVar 35) 0 255 ]).
  { destruct (lh_kn E M c v z ltac:(evs; reflexivity) ltac:(evs; reflexivity) ltac:(evs; reflexivity) Hc0 Hc1 HSH ltac:(lia) HZ Hz) as [K1 K2].
    unfold know_ok. apply Forall_cons; [exact K1|]. apply Forall_cons; [exact K2|].
    repeat (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]). apply Forall_nil. }
  xrun_at (PropExec.mkFP F fc) asegs R LH_HEAD M ro HR HK 40%nat [LH_HEAD; LH_EXIT] (SCR [true; true] [] []) 40%N.
  { split_scs; lh_sc. }
  exists R'. split; [exact Hms|].
  rreg HR' 18%bv G18. rreg HR' 16%bv G16. rreg HR' 14%bv G14. rreg HR' 20%bv G20. rreg HR' 15%bv G15.
  split; [rewrite G18, w_add by lia; reflexivity|]. split; [rewrite G16, w_add by lia; reflexivity|].
  split; [rewrite G14; first [rewrite w_addm by lia; f_equal; lia | f_equal; lia]|]. split; [exact G20|].
  split; [rewrite G15; reflexivity|].
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

Lemma lh_loop : forall (k : nat) R F fc M ro (c : Z),
  (Z.of_nat (S k) <= 32)%Z ->
  getr R 18 = Z_to_bv 64 c -> getr R 16 = Z_to_bv 64 c -> getr R 14 = Z_to_bv 64 (Z.of_nat (S k)) -> getr R 20 = Z_to_bv 64 0x7fff8000 ->
  0 <= c -> c + Z.of_nat (S k) < 2 ^ 47 ->
  accessible M c (Z.of_nat (S k)) ->
  (forall j, 0 <= j < Z.of_nat (S k) -> exists z, 0 <= z < 256 /\ rdn asegs M (Z_to_bv 64 (c + j)) 1 = Some [Z_to_bv 8 z]) ->
  exists R', CatSim.msteps asegs (MS R F (Z_to_bv 64 LH_HEAD) fc None M ro) (MS R' F (Z_to_bv 64 LH_EXIT) fc None M ro)
    /\ kept_in KSH R R' /\ getr R' 15 = getr R 15 /\ getr R' 20 = Z_to_bv 64 0x7fff8000.
Proof.
  induction k as [|k IH]; intros R F fc M ro c Hk H18 H16 H14 H20 Hc0 Hc1 ACC BYT.
  - destruct (shk_of_accessible M c _ c ACC ltac:(cbn; lia)) as (v & HSH & Hv & Hvc).
    destruct (BYT 0 ltac:(cbn; lia)) as (z & Hz & HZ). rewrite Z.add_0_r in HZ.
    destruct Hvc as [Hv0|Hvc].
    + destruct (lh_last0 R F fc M ro c 1 v z H18 H16 H14 H20 eq_refl Hc0 ltac:(lia) HSH Hv0 HZ Hz) as (R1 & RUN & _ & _ & _ & G20 & G15 & GK).
      exists R1. split; [exact RUN|]. split; [exact GK|]. split; [exact G15 | exact G20].
    + destruct (lh_last1 R F fc M ro c 1 v z H18 H16 H14 H20 eq_refl Hc0 ltac:(lia) HSH ltac:(lia) Hvc HZ Hz) as (R1 & RUN & _ & _ & _ & G20 & G15 & GK).
      exists R1. split; [exact RUN|]. split; [exact GK|]. split; [exact G15 | exact G20].
  - destruct (shk_of_accessible M c _ c ACC ltac:(lia)) as (v & HSH & Hv & Hvc).
    destruct (BYT 0 ltac:(lia)) as (z & Hz & HZ). rewrite Z.add_0_r in HZ.
    assert (NEXT : forall R1, getr R1 18 = Z_to_bv 64 (c + 1) -> getr R1 16 = Z_to_bv 64 (c + 1) ->
                   getr R1 14 = Z_to_bv 64 (Z.of_nat (S (S k)) - 1) -> getr R1 20 = Z_to_bv 64 0x7fff8000 ->
                   exists R', CatSim.msteps asegs (MS R1 F (Z_to_bv 64 LH_HEAD) fc None M ro) (MS R' F (Z_to_bv 64 LH_EXIT) fc None M ro)
                     /\ kept_in KSH R1 R' /\ getr R' 15 = getr R1 15 /\ getr R' 20 = Z_to_bv 64 0x7fff8000).
    { intros R1 G18 G16 G14 G20. apply (IH R1 F fc M ro (c + 1)); [lia | exact G18 | exact G16 | | exact G20 | lia | lia | |].
      - rewrite G14. f_equal. lia.
      - destruct ACC as (A0 & A1 & AC). split; [lia|]. split; [lia|]. intros x Hx. apply AC. lia.
      - intros j Hj. destruct (BYT (j + 1) ltac:(lia)) as (z' & Hz' & HZ'). exists z'. split; [exact Hz'|].
        replace (c + 1 + j) with (c + (j + 1)) by lia. exact HZ'. }
    destruct Hvc as [Hv0|Hvc].
    + destruct (lh_mid0 R F fc M ro c (Z.of_nat (S (S k))) v z H18 H16 H14 H20 ltac:(lia) Hc0 ltac:(lia) HSH Hv0 HZ Hz)
        as (R1 & RUN & G18 & G16 & G14 & G20 & G15 & GK).
      destruct (NEXT R1 G18 G16 G14 G20) as (R2 & RUN2 & GK2 & G15' & G20').
      exists R2. split; [exact (CatSim.msteps_trans _ _ _ _ RUN RUN2)|]. split; [exact (kept_in_trans _ _ _ _ GK GK2)|].
      split; [rewrite G15'; exact G15 | exact G20'].
    + destruct (lh_mid1 R F fc M ro c (Z.of_nat (S (S k))) v z H18 H16 H14 H20 ltac:(lia) Hc0 ltac:(lia) HSH ltac:(lia) Hvc HZ Hz)
        as (R1 & RUN & G18 & G16 & G14 & G20 & G15 & GK).
      destruct (NEXT R1 G18 G16 G14 G20) as (R2 & RUN2 & GK2 & G15' & G20').
      exists R2. split; [exact (CatSim.msteps_trans _ _ _ _ RUN RUN2)|]. split; [exact (kept_in_trans _ _ _ _ GK GK2)|].
      split; [rewrite G15'; exact G15 | exact G20'].
Qed.
