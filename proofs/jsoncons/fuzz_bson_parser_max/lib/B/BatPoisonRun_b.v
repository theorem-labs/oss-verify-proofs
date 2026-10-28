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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MemsetLib As0StepLib
     ArtMem ArtRegs ArtAtomics ArtTac.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.muslA Require Import Ba0SumsMemset_code_b Ba0SumsMemset_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatPoison_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Definition art_poison_kept (r : reg) : Prop :=
  r <> 5%bv /\ r <> 6%bv /\ r <> 7%bv /\ r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv /\ r <> 15%bv /\ r <> 16%bv
  /\ r <> 17%bv /\ r <> 28%bv.

#[using="Type"] Theorem art_poison_hi_run : forall regs (M rom : word -> option byte) (raw : word) (sp p n v : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 v ->
  64 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 -> apart (sp - 64) 64 0x1366c8 0xc000 -> apart (sp - 64) 64 0x1d1768 256 ->
  art_layout M ->
  kHighMemBeg <= p -> p + n <= kHighMemEnd + 1 -> p mod 8 = 0 -> n mod 8 = 0 -> 8 <= n -> 0 <= v < 256 ->
  (v = 0 -> n / 8 < 65536) ->
  wrA M (SB + p / 8) (n / 8) ->
  exists regs',
    msteps ASEGS (mkst regs (0x7ab38 : word) M rom)
      (mkst regs' raw (Wf (art_poison_frame M sp (U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21)))
                          (SB + p / 8) (Z.to_nat (n / 8)) v) rom)
    /\ getr regs' 10 = Z_to_bv 64 (SB + p / 8) /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp
    /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
    /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21
    /\ (forall r : reg, art_poison_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp p n v H1 Hret H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo Hhi Hp8 Hn8 Hn Hv Hthr Wsh.
  pose proof (art_poison_hi_fn regs M rom raw sp p n v H1 H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo Hhi Hp8 Hn8 Hn Hv Hthr) as RUN1.
  unfold kHighMemBeg, kHighMemEnd, SB in *.
  match type of RUN1 with msteps _ _ (mkst ?R1 _ ?M1 _) =>
    assert (OK : store_ok ASEGS M1 (Z_to_bv 64 (2147450880 + p / 8)) (Z.to_nat (n / 8)) = true)
      by (unfold art_poison_frame; apply wr_wok with (a := 2147450880 + p / 8) (n := n / 8); [|lia|lia]; repeat apply wr_Wn; exact Wsh);
    destruct (memset_summary M1 (Z_to_bv 64 (2147450880 + p / 8)) (Z_to_bv 64 v) raw (n / 8) rom
               ltac:(lia) ltac:(rewrite art_u_lit by lia; lia) OK Hret R1
               ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; reflexivity))
      as (r2 & RUN2 & P10 & AG)
  end.
  exists r2. split.
  { eapply msteps_trans; [exact RUN1|]. unfold Wf. rewrite cbyte_cbz in RUN2. unfold cbz in RUN2. rewrite art_u_lit in RUN2 by lia.
    replace (v mod 256) with v in RUN2 by (symmetry; apply Z.mod_small; lia).
    replace (Z_to_bv 64 ms_base) with (0x129d04 : bv 64)%bv in RUN2 by (apply bv_eq; vm_compute; reflexivity). exact RUN2. }
  assert (K : forall r : reg, ~ In r ms_clob -> getr r2 r = getr _ r) by exact AG.
  cbn [ms_clob In] in K.
  zsplit;
    try (rewrite K by (intuition discriminate); gres; first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity | f_equal; lia]).
  intros r Hr. unfold art_poison_kept in Hr. destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?).
  rewrite K by (intuition congruence). kept_solve.
Qed.
End FPX.
