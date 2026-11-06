(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng MngWb.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngWb.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb.AxZ2.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits AxMalloc AXF_maz AXG_mfmem AXF_mcc.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_efbz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_efbz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_efbz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_efbz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_efbz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_efbz.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Ltac srg' HR' := rewrite (HR' _); lazymatch goal with |- edenot _ (sr_get ?l ?r) = _ => let t := eval vm_compute in (sr_get l r) in change (sr_get l r) with t end.

Definition mc_keepb : list nat := [1;2;3;4;8;9;18;21;22;23;24;25;26;27]%nat.
Definition mc_keepc : list nat := [1;2;3;4;8;9;18;20;21;22;23;24;25;26;27]%nat.

(* [comment removed for export] *)
Lemma kp_lit : forall (R regs : bvmap 5 word) (l : list nat),
  (forall k, In k l -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) ->
  forall k r, In k l -> Z_to_bv 5 (Z.of_nat k) = r -> getr R r = getr regs r.
Proof. intros R regs l K k r Hk <-. exact (K k Hk). Qed.

Ltac kp K k := match goal with |- context [getr ?R ?r] => rewrite (kp_lit _ _ _ K k r ltac:(cbn; tauto) ltac:(apply bv_eq; reflexivity)) end.

Section MC.
Context {fx : FPState}.

#[using="Type"] Theorem mam1_arm : forall (regs : bvmap 5 word) (m rom : word -> option byte) (n : Z),
  getr regs 10 = wa n -> 157 <= n <= 131051 ->
  2^20 <= bv_unsigned (getr regs 2) <= 2^47 -> bv_unsigned (getr regs 2) mod 16 = 0 -> stk_ok SEGS m (getr regs 2) 1024 ->
  exists R, msteps SEGS (mkst regs (wa 0x530c8) m rom) (mkst R (wa 0x53e2c) (ma_mem m regs) rom)
         /\ ma_regs R regs n (Z.shiftr (n + 3) 4).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n HN Rn Rsp Asp HSTK.
  set (spz := bv_unsigned (getr regs 2)) in *.
  set (E := Env (reg_ev regs (fun k => wa (nth (k - 32) [n] 0))) (fun _ => [])).
  assert (HR : regs_ok E OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mam1.sr_mam1 regs).
  { apply (regs_ok_pin E sr_id regs 10). { apply regs_ok_id. } rewrite HN. reflexivity. }
  assert (Z2 : bv_unsigned (ev E 2) = spz) by reflexivity.
  assert (Z32 : bv_unsigned (ev E 32) = n) by exact (u_wa_small _ (rng64 _ _ _ Rn eq_refl)).
  assert (RSK : 0 <= 1024 <= spz) by (clear - Rsp; lia).
  assert (HK : know_ok SEGS E m OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mam1.kn_mam1).
  { unfold know_ok, OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mam1.kn_mam1.
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | exact HSTK | exact RSK])
               | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) ].
    all: cbn [zeval edenot OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mam1.e_n]; rewrite ?Z2, ?Z32.
    all: rewrite ?(mod64_of_range _ _ _ Rsp eq_refl eq_refl), ?(mod64_of_range _ _ _ Rn eq_refl eq_refl); first [assumption | lia]. }
  assert (Hsc : scs_denot SEGS m E (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mam1.RES_mam1))) by (cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mam1.RES_mam1 fst snd]; apply Forall_nil).
  destruct (run_sound SEGS 100 [0x53e2c] OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mam1.scr_mam1 0x530c8 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mam1.sr_mam1 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mam1.kn_mam1 33 _ _ _ E m rom regs OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mam1.RES_mam1_ok HR HK Hsc)
    as (R & HR' & _ & Hms). clear HK Hsc.
  exists R. split.
  - cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mam1.RES_mam1 fst snd s_pc s_log s_regs mem_denot] in Hms. exact Hms.
  - cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mam1.RES_mam1 fst snd s_regs] in HR'. clear Hms. unfold ma_regs.
    split; [srg' HR'; reflexivity|].
    split; [srg' HR'; reflexivity|].
    split; [srg' HR'; reflexivity|].
    split; [srg' HR'; rewrite zeval_sound; f_equal; cbn [zeval edenot]; rewrite Z32; litmods;
            rewrite (Z.mod_small (n + 3)) by lia; reflexivity|].
    split; [srg' HR'; rewrite zeval_sound; unfold v_addi; f_equal; cbn [zeval edenot]; rewrite Z2; reflexivity|].
    intros k Hk. cbn [In] in Hk.
    repeat (destruct Hk as [<-|Hk]; [ rewrite (HR' _); reflexivity |]). destruct Hk.
Qed.

#[using="Type"] Theorem mc0a_arm : forall (regs : bvmap 5 word) (m rom : word -> option byte) (u : Z),
  getr regs 19 = wa 98952 -> getr regs 20 = wa u -> 10 <= u <= 8190 ->
  exists R, msteps SEGS (mkst regs (wa 0x53e2c) m rom) (mkst R (wa 0x53e50) m rom)
    /\ getr R 10 = wa (cY u) /\ getr R 11 = wa 125613361 /\ getr R 19 = wa 98952 /\ getr R 20 = wa u
    /\ (forall k, In k mc_keepb -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom u R19 R20 Ru.
  set (E := Env (reg_ev regs (fun k => wa (nth (k - 32) [u] 0))) (fun _ => [])).
  assert (HR : regs_ok E OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc0a.sr_mc0a regs).
  { apply (regs_ok_pin _ _ regs 20); [apply (regs_ok_pin _ sr_id regs 19); [apply regs_ok_id|] |].
    - rewrite R19. reflexivity.
    - rewrite R20. reflexivity. }
  assert (Z32 : bv_unsigned (ev E 32) = u) by exact (u_wa_small _ (rng64 _ _ _ Ru eq_refl)).
  assert (HK : know_ok SEGS E m OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc0a.kn_mc0a).
  { unfold know_ok, OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc0a.kn_mc0a. repeat (first [apply Forall_nil | apply Forall_cons]).
    (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end). cbn [zeval edenot OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc0a.e_u]. rewrite Z32, (mod64_of_range _ _ _ Ru eq_refl eq_refl). exact Ru. }
  assert (Hsc : scs_denot SEGS m E (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc0a.RES_mc0a))) by (cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc0a.RES_mc0a fst snd]; apply Forall_nil).
  destruct (run_sound SEGS 100 [0x53e50] OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc0a.scr_mc0a 0x53e2c OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc0a.sr_mc0a OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc0a.kn_mc0a 33 _ _ _ E m rom regs OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc0a.RES_mc0a_ok HR HK Hsc)
    as (R & HR' & _ & Hms). clear HK Hsc.
  exists R. split.
  - cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc0a.RES_mc0a fst snd s_pc s_log s_regs mem_denot] in Hms. exact Hms.
  - clear Hms.      (* [comment removed for export] *)
    split; [srg' HR'; rewrite zeval2_sound; rewrite cY_eq; unfold Env0; apply wa_eqm; rewrite m64_ok, Z.mod_mod by lia;
            cbn [zeval2 edenot ev YX]; rewrite ?Z32; rewrite ?u_wa_small by lia; reflexivity|].
    split; [srg' HR'; reflexivity|].
    split; [srg' HR'; reflexivity|].
    split; [srg' HR'; reflexivity|].
    intros k Hk. cbn [In mc_keepb] in Hk.
    repeat (destruct Hk as [<-|Hk]; [ rewrite (HR' _); reflexivity |]). destruct Hk.
Qed.

#[using="Type"] Theorem mc0b_arm : forall (regs : bvmap 5 word) (m rom : word -> option byte) (y : Z),
  getr regs 10 = wa y -> getr regs 11 = wa 125613361 -> 0 <= y <= 4294967295 ->
  exists R, msteps SEGS (mkst regs (wa 0x53e50) m rom) (mkst R (wa 0x53e6c) m rom)
    /\ getr R 10 = wa (cS y) /\ getr R 11 = wa 125613361
    /\ (forall k, In k mc_keep20 -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom y R10 R11 Ry.
  set (E := Env (reg_ev regs (fun k => wa (nth (k - 32) [y] 0))) (fun _ => [])).
  assert (HR : regs_ok E OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc0b.sr_mc0b regs).
  { apply (regs_ok_pin _ _ regs 11); [apply (regs_ok_pin _ sr_id regs 10); [apply regs_ok_id|] |].
    - rewrite R10. reflexivity.
    - rewrite R11. reflexivity. }
  assert (Z32 : bv_unsigned (ev E 32) = y) by exact (u_wa_small _ (rng64 _ _ _ Ry eq_refl)).
  assert (HK : know_ok SEGS E m OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc0b.kn_mc0b).
  { unfold know_ok, OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc0b.kn_mc0b. repeat (first [apply Forall_nil | apply Forall_cons]).
    (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end). cbn [zeval edenot OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc0b.e_y]. rewrite Z32, (mod64_of_range _ _ _ Ry eq_refl eq_refl). exact Ry. }
  assert (Hsc : scs_denot SEGS m E (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc0b.RES_mc0b))) by (cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc0b.RES_mc0b fst snd]; apply Forall_nil).
  destruct (run_sound SEGS 100 [0x53e6c] OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc0b.scr_mc0b 0x53e50 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc0b.sr_mc0b OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc0b.kn_mc0b 33 _ _ _ E m rom regs OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc0b.RES_mc0b_ok HR HK Hsc)
    as (R & HR' & _ & Hms). clear HK Hsc.
  exists R. split.
  - cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc0b.RES_mc0b fst snd s_pc s_log s_regs mem_denot] in Hms. exact Hms.
  - clear Hms.      (* [comment removed for export] *)
    split; [srg' HR'; rewrite zeval2_sound; rewrite cS_eq; unfold Env0; apply wa_eqm; rewrite m64_ok, Z.mod_mod by lia;
            cbn [zeval2 edenot ev SX]; rewrite ?Z32; rewrite ?u_wa_small by lia; reflexivity|].
    split; [srg' HR'; reflexivity|].
    intros k Hk. cbn [In mc_keep20] in Hk.
    repeat (destruct Hk as [<-|Hk]; [ rewrite (HR' _); reflexivity |]). destruct Hk.
Qed.

#[using="Type"] Theorem mc1_arm : forall (regs : bvmap 5 word) (m rom : word -> option byte) (s d : Z),
  getr regs 10 = wa s -> getr regs 11 = wa 125613361 -> getr regs 19 = wa 98952 ->
  0 <= s <= 4294967295 -> 0 <= d <= 31 -> 0 <= dbx s <= 31 ->
  rdn SEGS m (wa (dbx s + 98952)) 1 = Some (word_to_le_bytes 1 (wa d)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53e6c) m rom) (mkst R (wa 0x53e9c) m rom)
    /\ getr R 10 = wa (124 - 4 * d) /\ getr R 11 = wa (121 - (124 - 4 * d)) /\ getr R 12 = wa 97932 /\ getr R 19 = wa 98952
    /\ (forall k, In k mc_keepc -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom s0 d R10 R11 R19 Rs Rd Rdbx Md.
  set (E := Env (reg_ev regs (fun k => wa (nth (k - 32) [s0; d] 0))) (fun _ => [])).
  assert (HR : regs_ok E OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc1.sr_mc1 regs).
  { apply (regs_ok_pin _ _ regs 19); [apply (regs_ok_pin _ _ regs 11); [apply (regs_ok_pin _ sr_id regs 10); [apply regs_ok_id|] |] |].
    - rewrite R10. reflexivity.
    - rewrite R11. reflexivity.
    - rewrite R19. reflexivity. }
  assert (Z32 : bv_unsigned (ev E 32) = s0) by exact (u_wa_small _ (rng64 _ _ _ Rs eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = d) by exact (u_wa_small _ (rng64 _ _ _ Rd eq_refl)).
  assert (ZDB : zeval E OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc1.DBX = dbx s0).
  { change (zeval E OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc1.DBX) with (bv_unsigned (edenot E OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc1.DBX)). rewrite zeval2_u. rewrite dbx_eq. unfold Env0. rewrite m64_ok.
    cbn [zeval2 edenot ev OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc1.DBX]. rewrite ?Z32. rewrite ?u_wa_small by lia. reflexivity. }
  assert (HK : know_ok SEGS E m OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc1.kn_mc1).
  { unfold know_ok, OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc1.kn_mc1.
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) ].
    all: rewrite ?ZDB; cbn [zeval edenot OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc1.e_s OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc1.e_d]; rewrite ?Z32, ?Z33.
    all: rewrite ?(mod64_of_range _ _ _ Rs eq_refl eq_refl), ?(mod64_of_range _ _ _ Rd eq_refl eq_refl),
           ?(mod64_of_range _ _ _ Rdbx eq_refl eq_refl).
    all: first [ assumption | lia ]. }
  assert (Hsc : scs_denot SEGS m E (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc1.RES_mc1))) by (cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc1.RES_mc1 fst snd]; apply Forall_nil).
  destruct (run_sound SEGS 100 [0x53e9c] OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc1.scr_mc1 0x53e6c OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc1.sr_mc1 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc1.kn_mc1 34 _ _ _ E m rom regs OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc1.RES_mc1_ok HR HK Hsc)
    as (R & HR' & _ & Hms). clear HK Hsc.
  assert (XV : edenot E (EAlu ALU_XOR (EMd M_MUL (ELit 4) (EVar 33)) (ELit 124)) = wa (124 - 4 * d)).
  { change (edenot E (EAlu ALU_XOR (EMd M_MUL (ELit 4) (EVar 33)) (ELit 124)))
      with (alu64 ALU_XOR (edenot E (EMd M_MUL (ELit 4) (EVar 33))) (edenot E (ELit 124))).
    rewrite alu_xor, !zeval_sound. unfold v_xor. rewrite !u_wa. cbn [zeval edenot]. rewrite Z33.
    rewrite (Z.mod_small (4 * d)) by lia. rewrite (Z.mod_small 124) by lia. rewrite xor124 by lia. reflexivity. }
  exists R. split.
  - cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc1.RES_mc1 fst snd s_pc s_log s_regs mem_denot] in Hms. exact Hms.
  - clear Hms.      (* [comment removed for export] *)
    split; [srg' HR'; exact XV|].
    split; [srg' HR'; rewrite zeval_sound; f_equal; cbn [zeval]; rewrite XV, u_wa_small by lia; ring|].
    split; [srg' HR'; reflexivity|].
    split; [srg' HR'; reflexivity|].
    intros k Hk. cbn [In mc_keepc] in Hk.
    repeat (destruct Hk as [<-|Hk]; [ rewrite (HR' _); reflexivity |]). destruct Hk.
Qed.

#[using="Type"] Theorem mc2_arm : forall (regs : bvmap 5 word) (m rom : word -> option byte) (u x i1 t1 : Z),
  getr regs 10 = wa x -> getr regs 11 = wa i1 -> getr regs 12 = wa 97932 -> getr regs 20 = wa u ->
  10 <= u <= 8190 -> 0 <= x <= 124 -> 0 <= i1 <= 47 -> 0 <= t1 <= 65535 ->
  rdn SEGS m (wa (2 * i1 + 98984)) 2 = Some (word_to_le_bytes 2 (wa t1)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53e9c) m rom) (mkst R (wa 0x53f14) m rom)
    /\ getr R 11 = wa 98984 /\ getr R 12 = wa ((if u <? t1 then 120 else 122) - x) /\ getr R 20 = wa u
    /\ (forall k, In k mc_keep -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom u x i1 t1 R10 R11 R12 R20 Ru Rx Ri1 Rt1 Mt1.
  set (E := Env (reg_ev regs (fun k => wa (nth (k - 32) [u; x; i1; t1] 0))) (fun _ => [])).
  assert (HR : regs_ok E OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc2.sr_mc2 regs).
  { apply (regs_ok_pin _ _ regs 20); [apply (regs_ok_pin _ _ regs 12); [apply (regs_ok_pin _ _ regs 11);
      [apply (regs_ok_pin _ sr_id regs 10); [apply regs_ok_id|] |] |] |].
    - rewrite R10. reflexivity.
    - rewrite R11. reflexivity.
    - rewrite R12. reflexivity.
    - rewrite R20. reflexivity. }
  assert (Z32 : bv_unsigned (ev E 32) = u) by exact (u_wa_small _ (rng64 _ _ _ Ru eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = x) by exact (u_wa_small _ (rng64 _ _ _ Rx eq_refl)).
  assert (Z34 : bv_unsigned (ev E 34) = i1) by exact (u_wa_small _ (rng64 _ _ _ Ri1 eq_refl)).
  assert (Z35 : bv_unsigned (ev E 35) = t1) by exact (u_wa_small _ (rng64 _ _ _ Rt1 eq_refl)).
  assert (HK : know_ok SEGS E m OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc2.kn_mc2).
  { unfold know_ok, OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc2.kn_mc2.
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) ].
    all: cbn [zeval edenot OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc2.e_u OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc2.e_x OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc2.e_i1 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc2.e_t1]; rewrite ?Z32, ?Z33, ?Z34, ?Z35.
    all: rewrite ?(mod64_of_range _ _ _ Ru eq_refl eq_refl), ?(mod64_of_range _ _ _ Rx eq_refl eq_refl),
           ?(mod64_of_range _ _ _ Ri1 eq_refl eq_refl), ?(mod64_of_range _ _ _ Rt1 eq_refl eq_refl).
    all: first [ assumption | lia ]. }
  destruct (u <? t1) eqn:C.
  - assert (Hsc : scs_denot SEGS m E (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc2.RES_mc2_T))).
    { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc2.RES_mc2_T fst snd]. apply Forall_cons; [|apply Forall_nil].
      apply sc_br_z. rewrite br_ltu_z. cbn [zeval edenot]. rewrite Z32, Z35.
      rewrite (mod64_of_range _ _ _ Ru eq_refl eq_refl), (mod64_of_range _ _ _ Rt1 eq_refl eq_refl). exact C. }
    destruct (run_sound SEGS 100 [0x53f14] OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc2.scr_mc2_T 0x53e9c OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc2.sr_mc2 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc2.kn_mc2 36 _ _ _ E m rom regs OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc2.RES_mc2_T_ok HR HK Hsc)
      as (R & HR' & _ & Hms). clear HK Hsc.
    exists R. split.
    + cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc2.RES_mc2_T fst snd s_pc s_log s_regs mem_denot] in Hms. exact Hms.
    + clear Hms.      (* [comment removed for export] *)
      split; [srg' HR'; reflexivity|].
      split; [srg' HR'; rewrite zeval_sound; f_equal; cbn [zeval edenot]; rewrite Z33; ring|].
      split; [srg' HR'; reflexivity|].
      intros k Hk. cbn [In mc_keep] in Hk.
      repeat (destruct Hk as [<-|Hk]; [ rewrite (HR' _); reflexivity |]). destruct Hk.
  - assert (Hsc : scs_denot SEGS m E (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc2.RES_mc2_F))).
    { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc2.RES_mc2_F fst snd]. apply Forall_cons; [|apply Forall_nil].
      apply sc_br_z. rewrite br_ltu_z. cbn [zeval edenot]. rewrite Z32, Z35.
      rewrite (mod64_of_range _ _ _ Ru eq_refl eq_refl), (mod64_of_range _ _ _ Rt1 eq_refl eq_refl). exact C. }
    destruct (run_sound SEGS 100 [0x53f14] OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc2.scr_mc2_F 0x53e9c OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc2.sr_mc2 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc2.kn_mc2 36 _ _ _ E m rom regs OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc2.RES_mc2_F_ok HR HK Hsc)
      as (R & HR' & _ & Hms). clear HK Hsc.
    exists R. split.
    + cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc2.RES_mc2_F fst snd s_pc s_log s_regs mem_denot] in Hms. exact Hms.
    + clear Hms.      (* [comment removed for export] *)
      split; [srg' HR'; reflexivity|].
      split; [srg' HR'; rewrite zeval_sound; f_equal; cbn [zeval edenot]; rewrite Z33; ring|].
      split; [srg' HR'; reflexivity|].
      intros k Hk. cbn [In mc_keep] in Hk.
      repeat (destruct Hk as [<-|Hk]; [ rewrite (HR' _); reflexivity |]). destruct Hk.
Qed.

#[using="Type"] Theorem mc3_arm : forall (regs : bvmap 5 word) (m rom : word -> option byte) (u i2 t2 : Z),
  getr regs 11 = wa 98984 -> getr regs 12 = wa i2 -> getr regs 20 = wa u ->
  10 <= u <= 8190 -> 0 <= i2 <= 47 -> 0 <= t2 <= 65535 ->
  rdn SEGS m (wa (2 * i2 + 98984)) 2 = Some (word_to_le_bytes 2 (wa t2)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53f14) m rom) (mkst R (wa 0x53f2c) m rom)
    /\ getr R 20 = wa (Z.lor i2 (if u <? t2 then 0 else 1))
    /\ (forall k, In k mc_keep -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom u i2 t2 R11 R12 R20 Ru Ri2 Rt2 Mt2.
  set (E := Env (reg_ev regs (fun k => wa (nth (k - 32) [u; i2; t2] 0))) (fun _ => [])).
  assert (HR : regs_ok E OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc3.sr_mc3 regs).
  { apply (regs_ok_pin _ _ regs 20); [apply (regs_ok_pin _ _ regs 12); [apply (regs_ok_pin _ sr_id regs 11); [apply regs_ok_id|] |] |].
    - rewrite R11. reflexivity.
    - rewrite R12. reflexivity.
    - rewrite R20. reflexivity. }
  assert (Z32 : bv_unsigned (ev E 32) = u) by exact (u_wa_small _ (rng64 _ _ _ Ru eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = i2) by exact (u_wa_small _ (rng64 _ _ _ Ri2 eq_refl)).
  assert (Z34 : bv_unsigned (ev E 34) = t2) by exact (u_wa_small _ (rng64 _ _ _ Rt2 eq_refl)).
  assert (HK : know_ok SEGS E m OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc3.kn_mc3).
  { unfold know_ok, OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc3.kn_mc3.
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) ].
    all: cbn [zeval edenot OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc3.e_u OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc3.e_i2 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc3.e_t2]; rewrite ?Z32, ?Z33, ?Z34.
    all: rewrite ?(mod64_of_range _ _ _ Ru eq_refl eq_refl), ?(mod64_of_range _ _ _ Ri2 eq_refl eq_refl),
           ?(mod64_of_range _ _ _ Rt2 eq_refl eq_refl).
    all: first [ assumption | lia ]. }
  assert (Hsc : scs_denot SEGS m E (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc3.RES_mc3))) by (cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc3.RES_mc3 fst snd]; apply Forall_nil).
  destruct (run_sound SEGS 100 [0x53f2c] OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc3.scr_mc3 0x53f14 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc3.sr_mc3 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc3.kn_mc3 35 _ _ _ E m rom regs OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc3.RES_mc3_ok HR HK Hsc)
    as (R & HR' & _ & Hms). clear HK Hsc.
  exists R. split.
  - cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc3.RES_mc3 fst snd s_pc s_log s_regs mem_denot] in Hms. exact Hms.
  - clear Hms.      (* [comment removed for export] *)
    split.
    + srg' HR'. cbn [edenot]. rewrite alu_or, alu_xor. unfold v_or, v_xor.
      change (edenot E (EAlu ALU_SLTU (EVar 32) (EVar 34))) with (alu64 ALU_SLTU (ev E 32) (ev E 34)).
      cbn [edenot]. rewrite !u_wa.
      assert (SL : bv_unsigned (alu64 ALU_SLTU (ev E 32) (ev E 34)) = if u <? t2 then 1 else 0).
      { rewrite alu_sltu. unfold v_sltu, c_ltu, bv_ltu. rewrite Z32, Z34. destruct (u <? t2); reflexivity. }
      rewrite SL. rewrite Z33. destruct (u <? t2); reflexivity.
    + intros k Hk. cbn [In mc_keep] in Hk.
      repeat (destruct Hk as [<-|Hk]; [ rewrite (HR' _); reflexivity |]). destruct Hk.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem mcls_arm : forall (regs : bvmap 5 word) (m rom : word -> option byte) (u : Z),
  getr regs 19 = wa 98952 -> getr regs 20 = wa u -> 10 <= u <= 8190 ->
  (forall sc, 0 <= sc < 48 -> rdn SEGS m (wa (98984 + 2 * sc)) 2 = Some (word_to_le_bytes 2 (wa (znth sc size_classes)))) ->
  (forall j, 0 <= j < 32 -> rdn SEGS m (wa (98952 + j)) 1 = Some (word_to_le_bytes 1 (wa (znth j debruijn)))) ->
  exists R, msteps SEGS (mkst regs (wa 0x53e2c) m rom) (mkst R (wa 0x53f2c) m rom)
    /\ getr R 20 = wa (class_of_units u)
    /\ (forall k, In k mc_keep -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom u R19 R20 Ru Mtab Mdb.
  pose proof (cls_facts u Ru) as CK. cbv zeta in CK.
  set (y := cY u) in *. set (s := cS y) in *. set (ix := dbx s) in *. set (d := znth ix debruijn) in *.
  set (t1 := znth (121 - (124 - 4 * d)) size_classes) in *.
  set (i2 := (if u <? t1 then 120 else 122) - (124 - 4 * d)) in *. set (t2 := znth i2 size_classes) in *.
  destruct CK as ((C1 & C2 & C3 & C4 & C5 & C6) & C10).
  assert (SCR : forall sc, 0 <= sc <= 47 -> 0 <= znth sc size_classes <= 65535).
  { intros sc Hsc. assert (CC : forallb (fun sc => (0 <=? znth sc size_classes) && (znth sc size_classes <=? 65535)) (zseq 0 48) = true)
      by (vm_compute; reflexivity).
    rewrite forallb_forall in CC. specialize (CC sc ltac:(apply In_zseq; lia)). apply andb_true_iff in CC as [A B].
    apply Z.leb_le in A, B. lia. }
  destruct (mc0a_arm regs m rom u R19 R20 Ru) as (R1 & M1 & A10 & A11 & A19 & A20 & K1).
  destruct (mc0b_arm R1 m rom y A10 A11 C1) as (R2 & M2 & B10 & B11 & K2).
  assert (R19' : getr R2 19 = wa 98952) by (kp K2 19%nat; exact A19).
  assert (R20' : getr R2 20 = wa u) by (kp K2 20%nat; exact A20).
  destruct (mc1_arm R2 m rom s d B10 B11 R19' C2 C4 C3 ltac:(rewrite Z.add_comm; apply Mdb; lia)) as (R3 & M3 & D10 & D11 & D12 & D19 & K3).
  assert (R20'' : getr R3 20 = wa u) by (kp K3 20%nat; exact R20').
  destruct (mc2_arm R3 m rom u (124 - 4 * d) (121 - (124 - 4 * d)) t1 D10 D11 D12 R20'' Ru ltac:(lia) ltac:(lia) (SCR (121 - (124 - 4 * d)) ltac:(lia))
              ltac:(rewrite Z.add_comm; apply Mtab; lia)) as (R4 & M4 & E11 & E12 & E20 & K4).
  destruct (mc3_arm R4 m rom u i2 t2 E11 E12 E20 Ru ltac:(lia) (SCR i2 ltac:(lia)) ltac:(rewrite Z.add_comm; apply Mtab; lia))
    as (R5 & M5 & F20 & K5).
  exists R5. split; [exact (msteps_trans SEGS _ _ _ M1 (msteps_trans SEGS _ _ _ M2 (msteps_trans SEGS _ _ _ M3 (msteps_trans SEGS _ _ _ M4 M5))))|]. split.
  - rewrite F20. f_equal. exact C10.
  - intros k Hk. cbn [mc_keep In] in Hk.
    destruct (Nat.eq_dec k 19) as [->|N19].
    + assert (D19' : getr R3 (Z_to_bv 5 (Z.of_nat 19)) = wa 98952) by exact D19.
      assert (R19'' : getr regs (Z_to_bv 5 (Z.of_nat 19)) = wa 98952) by exact R19.
      rewrite (K5 19%nat ltac:(cbn; tauto)), (K4 19%nat ltac:(cbn; tauto)), D19', R19''. reflexivity.
    + assert (Hk' : In k mc_keepb) by (cbn [mc_keepb In]; lia).
      assert (Hk'' : In k mc_keep20) by (cbn [mc_keep20 In]; lia).
      assert (Hkc : In k mc_keepc) by (cbn [mc_keepc In]; lia).
      assert (Hkk : In k mc_keep) by (cbn [mc_keep In]; lia).
      rewrite (K5 k Hkk), (K4 k Hkk), (K3 k Hkc), (K2 k Hk''), (K1 k Hk'). reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem mam_arm : forall (regs : bvmap 5 word) (m rom : word -> option byte) (n : Z),
  getr regs 10 = wa n -> 157 <= n <= 131051 ->
  2^20 <= bv_unsigned (getr regs 2) <= 2^47 -> bv_unsigned (getr regs 2) mod 16 = 0 -> stk_ok SEGS m (getr regs 2) 1024 ->
  (forall sc, 0 <= sc < 48 -> rdn SEGS m (wa (98984 + 2 * sc)) 2 = Some (word_to_le_bytes 2 (wa (znth sc size_classes)))) ->
  (forall j, 0 <= j < 32 -> rdn SEGS m (wa (98952 + j)) 1 = Some (word_to_le_bytes 1 (wa (znth j debruijn)))) ->
  exists R, msteps SEGS (mkst regs (wa 0x530c8) m rom) (mkst R (wa 0x53f2c) (ma_mem m regs) rom)
         /\ ma_regs R regs n (size_to_class n).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n HN Rn Rsp Asp HSTK Mtab Mdb.
  destruct (mam1_arm regs m rom n HN Rn Rsp Asp HSTK) as (R1 & M1 & (Q8 & Q9 & Q19 & Q20 & Q2 & K1)).
  assert (Ru : 10 <= Z.shiftr (n + 3) 4 <= 8190).
  { rewrite Z.shiftr_div_pow2 by lia. change (2^4) with 16. split; [apply Z.div_le_lower_bound; lia|].
    assert ((n + 3) / 16 < 8191) by (apply Z.div_lt_upper_bound; lia). lia. }
  (* [comment removed for export] *)
  assert (Rsp1 : 2^20 <= bv_unsigned (getr regs 2)) by lia.
  assert (MT' : forall sc, 0 <= sc < 48 -> rdn SEGS (ma_mem m regs) (wa (98984 + 2 * sc)) 2 = Some (word_to_le_bytes 2 (wa (znth sc size_classes)))).
  { intros sc Hsc. rewrite (rdn_frame' m (ma_mem m regs)) by (try lia; intros x Hx; apply (ma_mem_out m regs Rsp); lia). exact (Mtab sc Hsc). }
  assert (MD' : forall j, 0 <= j < 32 -> rdn SEGS (ma_mem m regs) (wa (98952 + j)) 1 = Some (word_to_le_bytes 1 (wa (znth j debruijn)))).
  { intros j Hj. rewrite (rdn_frame' m (ma_mem m regs)) by (try lia; intros x Hx; apply (ma_mem_out m regs Rsp); lia). exact (Mdb j Hj). }
  destruct (mcls_arm R1 (ma_mem m regs) rom (Z.shiftr (n + 3) 4) Q19 Q20 Ru MT' MD') as (R2 & M2 & S20 & K2).
  exists R2. split; [exact (msteps_trans SEGS _ _ _ M1 M2)|].
  unfold ma_regs. split; [kp K2 8%nat; exact Q8|]. split; [kp K2 9%nat; exact Q9|].
  split; [kp K2 19%nat; exact Q19|]. split.
  - rewrite S20. f_equal. unfold size_to_class, IB. replace (n + 4 - 1) with (n + 3) by ring. reflexivity.
  - split; [kp K2 2%nat; exact Q2|].
    intros k Hk. rewrite (K2 k ltac:(cbn [In] in Hk |- *; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [mc_keep In]; tauto ])). exact (K1 k Hk).
Qed.

End MC.
