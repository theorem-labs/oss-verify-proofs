(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng AxBits AxMalloc MngZ MngWb AXF_maz AXG_mfmem.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngWb.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_mcc AXF_mcz.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMalloc OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_maz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_mfmem OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb.AxZ2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_mcc OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_mcz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_efbz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_efbz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_efbz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_nm2z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_nm2z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_efbz.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition nm_keep : list nat := [1;2;3;4;8;9;11;18;19;20;21;22;23;24;25;26;27]%nat.
Definition nm_keep3 : list nat := [1;2;3;4;8;9;11;18;19;20;21;22;23;24;26;27]%nat.

Ltac litr3 H := match type of H with getr _ ?r = _ => match goal with |- getr _ ?r0 = _ => replace r0 with r by (apply bv_eq; reflexivity) end end; rewrite H.

Section NM.
Context {fx : FPState}.

#[using="Type"] Theorem nm0_arm : forall (regs : bvmap 5 word) (m rom : word -> option byte) (u : Z),
  getr regs 14 = wa u -> 10 <= u <= 127 ->
  exists R, msteps SEGS (mkst regs (wa 0x52610) m rom) (mkst R (wa 0x52630) m rom)
    /\ getr R 10 = wa (cY u) /\ getr R 12 = wa 125612032 /\ getr R 14 = wa u
    /\ (forall k, In k nm_keep -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom u R14 Ru.
  set (E := Env (reg_ev regs (fun k => wa (nth (k - 32) [u] 0))) (fun _ => [])).
  assert (HR : regs_ok E OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm0.sr_nm0 regs).
  { apply (regs_ok_pin _ sr_id regs 14); [apply regs_ok_id|]. rewrite R14. reflexivity. }
  assert (Z32 : bv_unsigned (ev E 32) = u) by exact (u_wa_small _ (rng64 _ _ _ Ru eq_refl)).
  assert (HK : know_ok SEGS E m OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm0.kn_nm0).
  { unfold know_ok, OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm0.kn_nm0. repeat (first [apply Forall_nil | apply Forall_cons]).
    (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end). cbn [zeval edenot OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm0.e_u]. rewrite Z32, (mod64_of_range _ _ _ Ru eq_refl eq_refl). exact Ru. }
  assert (Hsc : scs_denot SEGS m E (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm0.RES_pnm0))) by (cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm0.RES_pnm0 fst snd]; apply Forall_nil).
  destruct (run_sound SEGS 100 [0x52630] OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm0.scr_pnm0 0x52610 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm0.sr_nm0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm0.kn_nm0 33 _ _ _ E m rom regs OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm0.RES_pnm0_ok HR HK Hsc)
    as (R & HR' & _ & Hms). clear HK Hsc.
  exists R. split.
  - cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm0.RES_pnm0 fst snd s_pc s_log s_regs mem_denot] in Hms. exact Hms.
  - clear Hms.      (* [comment removed for export] *)
    split; [srg' HR'; rewrite zeval2_sound; rewrite cY_eq; unfold Env0; apply wa_eqm; rewrite m64_ok, Z.mod_mod by lia;
            cbn [zeval2 edenot ev YX]; rewrite ?Z32; rewrite ?u_wa_small by lia; reflexivity|].
    split; [srg' HR'; reflexivity|].
    split; [srg' HR'; reflexivity|].
    intros k Hk. cbn [In nm_keep] in Hk.
    repeat (destruct Hk as [<-|Hk]; [ rewrite (HR' _); reflexivity |]). destruct Hk.
Qed.

#[using="Type"] Theorem nm0b_arm : forall (regs : bvmap 5 word) (m rom : word -> option byte) (y : Z),
  getr regs 10 = wa y -> 0 <= y <= 4294967295 ->
  exists R, msteps SEGS (mkst regs (wa 0x52630) m rom) (mkst R (wa 0x5264c) m rom)
    /\ getr R 10 = wa (cS y)
    /\ (forall k, In k (12%nat :: 14%nat :: nm_keep) -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom y R10 Ry.
  set (E := Env (reg_ev regs (fun k => wa (nth (k - 32) [y] 0))) (fun _ => [])).
  assert (HR : regs_ok E OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm0b.sr_nm0b regs).
  { apply (regs_ok_pin _ sr_id regs 10); [apply regs_ok_id|]. rewrite R10. reflexivity. }
  assert (Z32 : bv_unsigned (ev E 32) = y) by exact (u_wa_small _ (rng64 _ _ _ Ry eq_refl)).
  assert (HK : know_ok SEGS E m OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm0b.kn_nm0b).
  { unfold know_ok, OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm0b.kn_nm0b. repeat (first [apply Forall_nil | apply Forall_cons]).
    (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end). cbn [zeval edenot OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm0b.e_y]. rewrite Z32, (mod64_of_range _ _ _ Ry eq_refl eq_refl). exact Ry. }
  assert (Hsc : scs_denot SEGS m E (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm0b.RES_pnm0b))) by (cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm0b.RES_pnm0b fst snd]; apply Forall_nil).
  destruct (run_sound SEGS 100 [0x5264c] OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm0b.scr_pnm0b 0x52630 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm0b.sr_nm0b OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm0b.kn_nm0b 33 _ _ _ E m rom regs OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm0b.RES_pnm0b_ok HR HK Hsc)
    as (R & HR' & _ & Hms). clear HK Hsc.
  exists R. split.
  - cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm0b.RES_pnm0b fst snd s_pc s_log s_regs mem_denot] in Hms. exact Hms.
  - clear Hms.      (* [comment removed for export] *)
    split; [srg' HR'; rewrite zeval2_sound; rewrite cS_eq; unfold Env0; apply wa_eqm; rewrite m64_ok, Z.mod_mod by lia;
            cbn [zeval2 edenot ev SX]; rewrite ?Z32; rewrite ?u_wa_small by lia; reflexivity|].
    intros k Hk. cbn [In nm_keep] in Hk.
    repeat (destruct Hk as [<-|Hk]; [ rewrite (HR' _); reflexivity |]). destruct Hk.
Qed.

#[using="Type"] Theorem nm1_arm : forall (regs : bvmap 5 word) (m rom : word -> option byte) (s d : Z),
  getr regs 10 = wa s -> getr regs 12 = wa 125612032 ->
  0 <= s <= 4294967295 -> 0 <= d <= 31 -> 0 <= dbx s <= 31 ->
  rdn SEGS m (wa (dbx s + 90368)) 1 = Some (word_to_le_bytes 1 (wa d)) ->
  exists R, msteps SEGS (mkst regs (wa 0x5264c) m rom) (mkst R (wa 0x5267c) m rom)
    /\ getr R 10 = wa (124 - 4 * d)
    /\ (forall k, In k (14%nat :: nm_keep) -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom s0 d R10 R12 Rs Rd Rdbx Md.
  set (E := Env (reg_ev regs (fun k => wa (nth (k - 32) [s0; d] 0))) (fun _ => [])).
  assert (HR : regs_ok E OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm1.sr_nm1 regs).
  { apply (regs_ok_pin _ _ regs 12); [apply (regs_ok_pin _ sr_id regs 10); [apply regs_ok_id|] |].
    - rewrite R10. reflexivity.
    - rewrite R12. reflexivity. }
  assert (Z32 : bv_unsigned (ev E 32) = s0) by exact (u_wa_small _ (rng64 _ _ _ Rs eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = d) by exact (u_wa_small _ (rng64 _ _ _ Rd eq_refl)).
  assert (ZDB : zeval E OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm1.DBX = dbx s0).
  { change (zeval E OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm1.DBX) with (bv_unsigned (edenot E OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm1.DBX)). rewrite zeval2_u. rewrite dbx_eq. unfold Env0. rewrite m64_ok.
    cbn [zeval2 edenot ev OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm1.DBX OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_mc1.DBX]. rewrite ?Z32. rewrite ?u_wa_small by lia. reflexivity. }
  assert (HK : know_ok SEGS E m OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm1.kn_nm1).
  { unfold know_ok, OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm1.kn_nm1.
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) ].
    all: rewrite ?ZDB; cbn [zeval edenot OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm1.e_s OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm1.e_d]; rewrite ?Z32, ?Z33.
    all: rewrite ?(mod64_of_range _ _ _ Rs eq_refl eq_refl), ?(mod64_of_range _ _ _ Rd eq_refl eq_refl),
           ?(mod64_of_range _ _ _ Rdbx eq_refl eq_refl).
    all: first [ assumption | lia ]. }
  assert (Hsc : scs_denot SEGS m E (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm1.RES_pnm1))) by (cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm1.RES_pnm1 fst snd]; apply Forall_nil).
  destruct (run_sound SEGS 100 [0x5267c] OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm1.scr_pnm1 0x5264c OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm1.sr_nm1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm1.kn_nm1 34 _ _ _ E m rom regs OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm1.RES_pnm1_ok HR HK Hsc)
    as (R & HR' & _ & Hms). clear HK Hsc.
  assert (XV : edenot E (EAlu ALU_XOR (EMd M_MUL (ELit 4) (EVar 33)) (ELit 124)) = wa (124 - 4 * d)).
  { change (edenot E (EAlu ALU_XOR (EMd M_MUL (ELit 4) (EVar 33)) (ELit 124)))
      with (alu64 ALU_XOR (edenot E (EMd M_MUL (ELit 4) (EVar 33))) (edenot E (ELit 124))).
    rewrite alu_xor, !zeval_sound. unfold v_xor. rewrite !u_wa. cbn [zeval edenot]. rewrite Z33.
    rewrite (Z.mod_small (4 * d)) by lia. rewrite (Z.mod_small 124) by lia. rewrite xor124 by lia. reflexivity. }
  exists R. split.
  - cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm1.RES_pnm1 fst snd s_pc s_log s_regs mem_denot] in Hms. exact Hms.
  - clear Hms.      (* [comment removed for export] *)
    split; [srg' HR'; exact XV|].
    intros k Hk. cbn [In nm_keep] in Hk.
    repeat (destruct Hk as [<-|Hk]; [ rewrite (HR' _); reflexivity |]). destruct Hk.
Qed.

#[using="Type"] Theorem nm3_arm : forall (regs : bvmap 5 word) (m rom : word -> option byte) (u i2 t2 : Z),
  getr regs 12 = wa i2 -> getr regs 14 = wa u -> getr regs 25 = wa 98984 ->
  10 <= u <= 127 -> 0 <= i2 <= 47 -> 0 <= t2 <= 65535 ->
  rdn SEGS m (wa (2 * i2 + 98984)) 2 = Some (word_to_le_bytes 2 (wa t2)) ->
  exists R, msteps SEGS (mkst regs (wa 0x526ac) m rom) (mkst R (wa 0x526c4) m rom)
    /\ getr R 14 = wa (Z.lor i2 (if u <? t2 then 0 else 1)) /\ getr R 25 = wa 98984
    /\ (forall k, In k nm_keep3 -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom u i2 t2 R12 R14 R25 Ru Ri2 Rt2 Mt2.
  set (E := Env (reg_ev regs (fun k => wa (nth (k - 32) [u; i2; t2] 0))) (fun _ => [])).
  assert (HR : regs_ok E OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm3.sr_nm3 regs).
  { apply (regs_ok_pin _ _ regs 25); [apply (regs_ok_pin _ _ regs 14); [apply (regs_ok_pin _ sr_id regs 12); [apply regs_ok_id|] |] |].
    - rewrite R12. reflexivity.
    - rewrite R14. reflexivity.
    - rewrite R25. reflexivity. }
  assert (Z32 : bv_unsigned (ev E 32) = u) by exact (u_wa_small _ (rng64 _ _ _ Ru eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = i2) by exact (u_wa_small _ (rng64 _ _ _ Ri2 eq_refl)).
  assert (Z34 : bv_unsigned (ev E 34) = t2) by exact (u_wa_small _ (rng64 _ _ _ Rt2 eq_refl)).
  assert (HK : know_ok SEGS E m OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm3.kn_nm3).
  { unfold know_ok, OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm3.kn_nm3.
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) ].
    all: cbn [zeval edenot OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm3.e_u OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm3.e_i2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm3.e_t2]; rewrite ?Z32, ?Z33, ?Z34.
    all: rewrite ?(mod64_of_range _ _ _ Ru eq_refl eq_refl), ?(mod64_of_range _ _ _ Ri2 eq_refl eq_refl),
           ?(mod64_of_range _ _ _ Rt2 eq_refl eq_refl).
    all: first [ assumption | lia ]. }
  assert (Hsc : scs_denot SEGS m E (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm3.RES_pnm3))) by (cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm3.RES_pnm3 fst snd]; apply Forall_nil).
  destruct (run_sound SEGS 100 [0x526c4] OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm3.scr_pnm3 0x526ac OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm3.sr_nm3 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm3.kn_nm3 35 _ _ _ E m rom regs OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm3.RES_pnm3_ok HR HK Hsc)
    as (R & HR' & _ & Hms). clear HK Hsc.
  exists R. split.
  - cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.AXF_nm3.RES_pnm3 fst snd s_pc s_log s_regs mem_denot] in Hms. exact Hms.
  - clear Hms.      (* [comment removed for export] *)
    split.
    + srg' HR'. cbn [edenot]. rewrite alu_or, alu_xor. unfold v_or, v_xor.
      change (edenot E (EAlu ALU_SLTU (EVar 32) (EVar 34))) with (alu64 ALU_SLTU (ev E 32) (ev E 34)).
      cbn [edenot]. rewrite !u_wa.
      assert (SL : bv_unsigned (alu64 ALU_SLTU (ev E 32) (ev E 34)) = if u <? t2 then 1 else 0).
      { rewrite alu_sltu. unfold v_sltu, c_ltu, bv_ltu. rewrite Z32, Z34. destruct (u <? t2); reflexivity. }
      rewrite SL. rewrite Z33. destruct (u <? t2); reflexivity.
    + split; [srg' HR'; reflexivity|].
      intros k Hk. cbn [In nm_keep3] in Hk.
      repeat (destruct Hk as [<-|Hk]; [ rewrite (HR' _); reflexivity |]). destruct Hk.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem njm_arm : forall (regs : bvmap 5 word) (m rom : word -> option byte) (u : Z),
  getr regs 14 = wa u -> getr regs 25 = wa 98984 -> 10 <= u <= 127 ->
  (forall sc, 0 <= sc < 48 -> rdn SEGS m (wa (98984 + 2 * sc)) 2 = Some (word_to_le_bytes 2 (wa (znth sc size_classes)))) ->
  (forall j, 0 <= j < 32 -> rdn SEGS m (wa (90368 + j)) 1 = Some (word_to_le_bytes 1 (wa (znth j debruijn)))) ->
  exists R, msteps SEGS (mkst regs (wa 0x52610) m rom) (mkst R (wa 0x526c4) m rom)
    /\ getr R 14 = wa (class_of_units u)
    /\ (forall k, In k nm_keep -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom u R14 R25 Ru Mtab Mdb.
  pose proof (cls_facts u ltac:(lia)) as CK. cbv zeta in CK.
  set (y := cY u) in *. set (s := cS y) in *. set (ix := dbx s) in *. set (d := znth ix debruijn) in *.
  set (t1 := znth (121 - (124 - 4 * d)) size_classes) in *.
  set (i2 := (if u <? t1 then 120 else 122) - (124 - 4 * d)) in *. set (t2 := znth i2 size_classes) in *.
  destruct CK as ((C1 & C2 & C3 & C4 & C5 & C6) & C10).
  assert (SCR : forall sc, 0 <= sc <= 47 -> 0 <= znth sc size_classes <= 65535).
  { intros sc Hsc. assert (CC : forallb (fun sc => (0 <=? znth sc size_classes) && (znth sc size_classes <=? 65535)) (zseq 0 48) = true)
      by (vm_compute; reflexivity).
    rewrite forallb_forall in CC. specialize (CC sc ltac:(apply In_zseq; lia)). apply andb_true_iff in CC as [A B].
    apply Z.leb_le in A, B. lia. }
  destruct (nm0_arm regs m rom u R14 Ru) as (R1 & M1 & A10 & A12 & A14 & K1).
  destruct (nm0b_arm R1 m rom y A10 C1) as (R2 & M2 & B10 & K2).
  assert (R12' : getr R2 12 = wa 125612032) by (kp K2 12%nat; exact A12).
  assert (R14' : getr R2 14 = wa u) by (kp K2 14%nat; exact A14).
  destruct (nm1_arm R2 m rom s d B10 R12' C2 C4 C3 ltac:(rewrite Z.add_comm; apply Mdb; lia)) as (R3 & M3 & D10 & K3).
  assert (R14'' : getr R3 14 = wa u) by (kp K3 14%nat; exact R14').
  assert (R25' : getr R3 25 = wa 98984).
  { kp K3 25%nat. kp K2 25%nat. kp K1 25%nat. exact R25. }
  assert (Ei1 : 121 + -1 * (121 - (124 - 4 * d)) = 124 - 4 * d) by ring.
  assert (P2 : AXF_nm2z.nm2_pre R3 m u (121 - (124 - 4 * d)) t1).
  { constructor; try assumption; try lia.
    - rewrite Ei1. exact D10.
    - apply SCR. lia.
    - rewrite Z.add_comm. apply Mtab. lia. }
  assert (E2 : exists R4, msteps SEGS (mkst R3 (wa 0x5267c) m rom) (mkst R4 (wa 0x526ac) m rom) /\ getr R4 12 = wa i2 /\ getr R4 14 = wa u /\
                 getr R4 25 = wa 98984 /\
                 (forall k, In k nm_keep3 -> getr R4 (Z_to_bv 5 (Z.of_nat k)) = getr R3 (Z_to_bv 5 (Z.of_nat k)))).
  { destruct (Z.ltb_spec u t1) as [Lt|Ge].
    - destruct (AXF_nm2z.nm2_pnm2l R3 m rom u (121 - (124 - 4 * d)) t1 P2) as (R4 & M4 & E10 & E12 & E14 & E25 & K4).
      { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_nm2z.AXF_nm2.RES_pnm2l fst snd]. set (E := Ez R3 (AXF_nm2z.VALS_nm2 u (121 - (124 - 4 * d)) t1)).
        assert (Z32 : bv_unsigned (ev E 32) = u) by (apply zatom; [reflexivity | reflexivity | lia]).
        assert (Z34 : bv_unsigned (ev E 34) = t1) by (apply zatom; [reflexivity | reflexivity | pose proof (SCR (121 - (124 - 4 * d)) ltac:(lia)); lia]).
        repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z; cbn [zeval edenot]; rewrite ?Z32, ?Z34.
        rewrite br_ltu_z. rewrite !Z.mod_small by (pose proof (SCR (121 - (124 - 4 * d)) ltac:(lia)); lia). apply Z.ltb_lt. exact Lt. }
      exists R4. split; [exact M4|]. split; [rewrite E12; f_equal; unfold i2; replace (u <? t1) with true by (symmetry; apply Z.ltb_lt; exact Lt); ring|].
      split; [exact E14|]. split; [exact E25|].
      intros k Hk. apply K4. clear - Hk. cbn [In nm_keep3] in *. intuition lia.
    - destruct (AXF_nm2z.nm2_pnm2g R3 m rom u (121 - (124 - 4 * d)) t1 P2) as (R4 & M4 & E10 & E12 & E14 & E25 & K4).
      { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_nm2z.AXF_nm2.RES_pnm2g fst snd]. set (E := Ez R3 (AXF_nm2z.VALS_nm2 u (121 - (124 - 4 * d)) t1)).
        assert (Z32 : bv_unsigned (ev E 32) = u) by (apply zatom; [reflexivity | reflexivity | lia]).
        assert (Z34 : bv_unsigned (ev E 34) = t1) by (apply zatom; [reflexivity | reflexivity | pose proof (SCR (121 - (124 - 4 * d)) ltac:(lia)); lia]).
        repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z; cbn [zeval edenot]; rewrite ?Z32, ?Z34.
        rewrite br_ltu_z. rewrite !Z.mod_small by (pose proof (SCR (121 - (124 - 4 * d)) ltac:(lia)); lia). apply Z.ltb_ge. exact Ge. }
      exists R4. split; [exact M4|]. split; [rewrite E12; f_equal; unfold i2; replace (u <? t1) with false by (symmetry; apply Z.ltb_ge; exact Ge); ring|].
      split; [exact E14|]. split; [exact E25|].
      intros k Hk. apply K4. clear - Hk. cbn [In nm_keep3] in *. intuition lia. }
  destruct E2 as (R4 & M4 & E12 & E14 & E25 & K4).
  destruct (nm3_arm R4 m rom u i2 t2 E12 E14 E25 Ru ltac:(lia) (SCR i2 ltac:(lia)) ltac:(rewrite Z.add_comm; apply Mtab; lia))
    as (R5 & M5 & F14 & F25 & K5).
  exists R5. split; [exact (msteps_trans SEGS _ _ _ M1 (msteps_trans SEGS _ _ _ M2 (msteps_trans SEGS _ _ _ M3 (msteps_trans SEGS _ _ _ M4 M5))))|]. split.
  - rewrite F14. f_equal. exact C10.
  - intros k Hk. destruct (Nat.eq_dec k 25) as [->|H25].
    + litr3 F25. symmetry. litr3 R25. reflexivity.
    + assert (Hk3 : In k nm_keep3) by (clear - Hk H25; cbn [In nm_keep nm_keep3] in *; intuition lia).
      rewrite (K5 k Hk3), (K4 k Hk3), (K3 k ltac:(right; exact Hk)), (K2 k ltac:(right; right; exact Hk)), (K1 k Hk). reflexivity.
Qed.

End NM.
