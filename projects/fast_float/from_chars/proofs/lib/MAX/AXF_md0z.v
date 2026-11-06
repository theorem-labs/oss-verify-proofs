(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng AxBits MngWb AXF_maz.

Module AXF_md0.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_n := EVar 32.
Definition STK := SA (EVar 2) (-1024).
Definition sr_md0 := (sr_upd sr_id 10 (e_n)).
Definition kn_md0 : list kentry :=
  [ KRange (EVar 2) (2^20) (2^47);
    KAlign (EVar 2) 16;
    KWr STK (ELit 1024);
    KRange e_n 131052 (2^26) ].
Definition scr_md0 : scripts := SCR [] [] [].
Definition ss_md0 := SS 0x51310 sr_md0 [] kn_md0 33.
Definition RUN_md0 := sym_exec SEGS 100 true [0x53328] scr_md0 ss_md0 [].

Definition scr_pmd0 : scripts := SCR [] [] [].
Definition RES_pmd0 := Eval vm_compute in sym_exec SEGS 100 true [0x53328] scr_pmd0 ss_md0 [].
Lemma RES_pmd0_ok : sym_exec SEGS 100 true [0x53328] scr_pmd0 (SS 0x51310 sr_md0 [] kn_md0 33) [] = RES_pmd0.
Proof. vm_compute. reflexivity. Qed.
End AXF_md0.

Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_maz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_md0z.AXF_md0.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition md0_regs (R regs : bvmap 5 word) (n : Z) : Prop :=
  getr R 1 = wa 0x52018 /\ getr R 2 = v_addi (getr regs 2) (-48) /\ getr R 8 = wa n /\ getr R 9 = wa 614096 /\
  getr R 10 = wa 0 /\ getr R 11 = wa (n + 20) /\ getr R 12 = wa 3 /\ getr R 13 = wa 34 /\ getr R 14 = wa (2^64 - 1) /\
  getr R 15 = wa 0 /\ getr R 18 = wa (2^64 - 1) /\ getr R 19 = wa (n + 20) /\
  (forall k, In k [3;4;20;21;22;23;24;25;26;27]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).

Section MD0.
Context {fx : FPState}.

#[using="Type"] Theorem md0_arm : forall (regs : bvmap 5 word) (m rom : word -> option byte) (n : Z),
  getr regs 10 = wa n -> 131052 <= n <= 2^26 ->
  2^20 <= bv_unsigned (getr regs 2) <= 2^47 -> bv_unsigned (getr regs 2) mod 16 = 0 -> stk_ok SEGS m (getr regs 2) 1024 ->
  exists R, msteps SEGS (mkst regs (wa 0x51310) m rom) (mkst R (wa 0x53328) (ma_mem m regs) rom) /\ md0_regs R regs n.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n HN Rn Rsp Asp HSTK.
  set (spz := bv_unsigned (getr regs 2)) in *.
  set (E := Env (reg_ev regs (fun k => wa (nth (k - 32) [n] 0))) (fun _ => [])).
  assert (HR : regs_ok E sr_md0 regs).
  { apply (regs_ok_pin E sr_id regs 10). { apply regs_ok_id. } rewrite HN. reflexivity. }
  assert (Z2 : bv_unsigned (ev E 2) = spz) by reflexivity.
  assert (Z32 : bv_unsigned (ev E 32) = n) by exact (u_wa_small _ (rng64 _ _ _ Rn eq_refl)).
  assert (RSK : 0 <= 1024 <= spz) by (clear - Rsp; lia).
  assert (HK : know_ok SEGS E m kn_md0).
  { unfold know_ok, kn_md0.
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | exact HSTK | exact RSK])
               | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) ].
    all: cbn [zeval edenot e_n]; rewrite ?Z2, ?Z32.
    all: rewrite ?(mod64_of_range _ _ _ Rsp eq_refl eq_refl), ?(mod64_of_range _ _ _ Rn eq_refl eq_refl); first [assumption | lia]. }
  assert (Hsc : scs_denot SEGS m E (snd (fst RES_pmd0))) by (cbn [RES_pmd0 fst snd]; apply Forall_nil).
  destruct (run_sound SEGS 100 [0x53328] scr_pmd0 0x51310 sr_md0 kn_md0 33 _ _ _ E m rom regs RES_pmd0_ok HR HK Hsc)
    as (R & HR' & _ & Hms). clear HK Hsc.
  exists R. split.
  - cbn [RES_pmd0 fst snd s_pc s_log s_regs mem_denot] in Hms. exact Hms.
  - cbn [RES_pmd0 fst snd s_regs] in HR'. clear Hms. unfold md0_regs.
    Ltac srg HR' := rewrite (HR' _); lazymatch goal with |- edenot _ (sr_get ?l ?r) = _ => let t := eval vm_compute in (sr_get l r) in change (sr_get l r) with t end.
    split; [srg HR'; reflexivity|].
    split; [srg HR'; rewrite zeval_sound; unfold v_addi; f_equal; cbn [zeval edenot]; rewrite Z2; reflexivity|].
    split; [srg HR'; reflexivity|].
    split; [srg HR'; reflexivity|].
    split; [srg HR'; reflexivity|].
    split; [srg HR'; rewrite zeval_sound; f_equal; cbn [zeval edenot]; rewrite Z32; litmods; reflexivity|].
    split; [srg HR'; reflexivity|].
    split; [srg HR'; reflexivity|].
    split; [srg HR'; reflexivity|].
    split; [srg HR'; reflexivity|].
    split; [srg HR'; reflexivity|].
    split; [srg HR'; rewrite zeval_sound; f_equal; cbn [zeval edenot]; rewrite Z32; litmods; reflexivity|].
    intros k Hk. cbn [In] in Hk.
    repeat (destruct Hk as [<-|Hk]; [ rewrite (HR' _); reflexivity |]). destruct Hk.
Qed.

End MD0.
