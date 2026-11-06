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
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng AxBits MngWb.

Module AXF_ma.
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
Definition sr_ma := (sr_upd sr_id 10 (e_n)).
Definition kn_ma : list kentry :=
  [ KRange (EVar 2) (2^20) (2^47);
    KAlign (EVar 2) 16;
    KWr STK (ELit 1024);
    KRange e_n 1 156 ].
Definition scr_ma : scripts := SCR [] [] [].
Definition ss_ma := SS 0x51310 sr_ma [] kn_ma 33.
Definition RUN_ma := sym_exec SEGS 100 true [0x52174] scr_ma ss_ma [].

Definition RES_ma := Eval vm_compute in RUN_ma.
Lemma RES_ma_ok : sym_exec SEGS 100 true [0x52174] scr_ma (SS 0x51310 sr_ma [] kn_ma 33) [] = RES_ma.
Proof. vm_compute. reflexivity. Qed.
End AXF_ma.

Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_maz.AXF_ma.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ma_mem (m : word -> option byte) (regs : bvmap 5 word) : word -> option byte :=
  let sp := getr regs 2 in
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (v_addi sp (-8)) (word_to_le_bytes 8 (getr regs 1)))
    (v_addi sp (-16)) (word_to_le_bytes 8 (getr regs 8)))
    (v_addi sp (-24)) (word_to_le_bytes 8 (getr regs 9)))
    (v_addi sp (-32)) (word_to_le_bytes 8 (getr regs 18)))
    (v_addi sp (-40)) (word_to_le_bytes 8 (getr regs 19)))
    (v_addi sp (-48)) (word_to_le_bytes 8 (getr regs 20)).

(* [comment removed for export] *)
Definition ma_regs (R regs : bvmap 5 word) (n sc : Z) : Prop :=
  getr R 8 = wa n /\ getr R 9 = wa 614096 /\ getr R 19 = wa 90368 /\ getr R 20 = wa sc /\
  getr R 2 = v_addi (getr regs 2) (-48) /\
  (forall k, In k [1;3;4;18;21;22;23;24;25;26;27]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).

Section MA.
Context {fx : FPState}.

#[using="Type"] Theorem ma_arm : forall (regs : bvmap 5 word) (m rom : word -> option byte) (n : Z),
  getr regs 10 = wa n -> 1 <= n <= 156 ->
  2^20 <= bv_unsigned (getr regs 2) <= 2^47 -> bv_unsigned (getr regs 2) mod 16 = 0 -> stk_ok SEGS m (getr regs 2) 1024 ->
  exists R, msteps SEGS (mkst regs (wa 0x51310) m rom) (mkst R (wa 0x52174) (ma_mem m regs) rom)
         /\ ma_regs R regs n (Z.shiftr (n + 3) 4).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n HN Rn Rsp Asp HSTK.
  set (spz := bv_unsigned (getr regs 2)) in *.
  set (E := Env (reg_ev regs (fun k => wa (nth (k - 32) [n] 0))) (fun _ => [])).
  assert (HR : regs_ok E sr_ma regs).
  { apply (regs_ok_pin E sr_id regs 10). { apply regs_ok_id. } rewrite HN. reflexivity. }
  assert (Z2 : bv_unsigned (ev E 2) = spz) by reflexivity.
  assert (Z32 : bv_unsigned (ev E 32) = n) by exact (u_wa_small _ (rng64 _ _ _ Rn eq_refl)).
  assert (RSK : 0 <= 1024 <= spz) by (clear - Rsp; lia).
  assert (HK : know_ok SEGS E m kn_ma).
  { unfold know_ok, kn_ma.
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | exact HSTK | exact RSK])
               | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) ].
    all: cbn [zeval edenot e_n]; rewrite ?Z2, ?Z32.
    all: rewrite ?(mod64_of_range _ _ _ Rsp eq_refl eq_refl), ?(mod64_of_range _ _ _ Rn eq_refl eq_refl); first [assumption | lia]. }
  assert (Hsc : scs_denot SEGS m E (snd (fst RES_ma))) by (cbn [RES_ma fst snd]; apply Forall_nil).
  destruct (run_sound SEGS 100 [0x52174] scr_ma 0x51310 sr_ma kn_ma 33 _ _ _ E m rom regs RES_ma_ok HR HK Hsc)
    as (R & HR' & _ & Hms). clear HK Hsc.
  exists R. split.
  - cbn [RES_ma fst snd s_pc s_log s_regs mem_denot] in Hms. exact Hms.
  - cbn [RES_ma fst snd s_regs] in HR'. clear Hms. unfold ma_regs.
    Ltac srg HR' := rewrite (HR' _); lazymatch goal with |- edenot _ (sr_get ?l ?r) = _ => let t := eval vm_compute in (sr_get l r) in change (sr_get l r) with t end.
    split; [srg HR'; reflexivity|].
    split; [srg HR'; reflexivity|].
    split; [srg HR'; reflexivity|].
    split; [srg HR'; rewrite zeval_sound; f_equal; cbn [zeval edenot]; rewrite Z32; litmods;
            rewrite (Z.mod_small (n + 3)) by lia; reflexivity|].
    split; [srg HR'; rewrite zeval_sound; unfold v_addi; f_equal; cbn [zeval edenot]; rewrite Z2; reflexivity|].
    intros k Hk. cbn [In] in Hk.
    repeat (destruct Hk as [<-|Hk]; [ rewrite (HR' _); reflexivity |]). destruct Hk.
Qed.

End MA.
