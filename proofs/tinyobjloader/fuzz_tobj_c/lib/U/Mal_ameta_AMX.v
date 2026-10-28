(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "astate"; "PGSZ"; "alloc_meta"; "init_state"; "st_avail_meta_count"; "st_free_meta_head"; "st_init_done"; "st_meta_alloc_shift"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta_AMX"; "Pam_init"; "am_pristine"; "@Corelib.Numbers.BinNums"; "Z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "NF"; "@Corelib.Init.Logic"; "and"; "eq"; "True"; "or"; "@Corelib.Init.Datatypes"; "option"; "list"; "prod"; "None"; "S"; "Some"; "bool"; "false"; "nat"; "pair"; "@Corelib.Init.Peano"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "IEC_U"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "LQP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AmPam"; "Pam_cnt"; "am_private_same"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "vm_insensitive"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM"; "J_am_pre"; "Pre_am"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAMT"; "Posts_amG"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_s"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "yields"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "TR_ang"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6.Mal_ameta_IN3"; "auxv_brk0_stmt"; "@Stdlib.ZArith.BinInt.Z"; "mul"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLayout MallocIface MallocIfaceI Contract ContractI ContractAM ContractDrv VmRoom TRRulesK ContractAMT DrvReach AmPam.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymSoundR SymSummary ExampleMemcpy.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6.Mal_ameta_IN3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6.Mal_ameta_sum.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].

Definition am_pristine (s : astate) : Prop := ltac2:(tb__ "0|1|
SeSfS18S7Vs;A1S19A3SeSfSbS8Vs;A1Z0M0A3SeSfSbS5Vs;A1G0A3SfS12S0A1S6Vs;A1S15S0A1A3A2A2A2").
Definition Pam_init (n : nat) (s : astate) : Prop := ltac2:(tb__ "0|0|
S11SeSaVs;A1S1cVn;U64A2A2S24Vn;Vs;A2A2").

Lemma Pam_init_start n : ltac2:(tb__ "0|0|
S1cVn;U64A2S9Vn;S4A2F_;").
Proof. intros Hn. left. split; [repeat split; reflexivity | exact Hn]. Qed.

Lemma Pam_init_am n s1 s2 ktr m : ltac2:(tb__ "0|1|
S9S16Vn;A1Vs1;A2S2cS14S12S0A1M0S1A2S3Vs1;A1Vktr;S1bG0S1S17S0Vm;A2Vs2;A4A4S9Vn;Vs2;A2F_;F_;").
Proof.
  intros [[(P1 & P2 & P3 & P4) Hn] | HC] HY.
  - destruct (alloc_meta_ok_step s1 s2 ktr m ltac:(lia) HY) as (I2 & _ & _ & F2).
    right. split; [exact I2|]. rewrite (F2 P4 ltac:(lia)). unfold METAS_PER_AREA. lia.
  - right. exact (Pam_cnt_am n s1 s2 ktr m HC HY).
Qed.

Lemma Pam_init_pure n s1 s2 : ltac2:(tb__ "0|0|
S9Vn;Vs1;A2S25Vs1;Vs2;A2S9Vn;Vs2;A2F_;F_;").
Proof.
  intros [[(P1 & P2 & P3 & P4) Hn] | HC] HS.
  - left. destruct HS as (E1 & E2 & E3 & E4). split; [|exact Hn]. unfold am_pristine. rewrite E1, E2, E3, E4. repeat split; assumption.
  - right. exact (Pam_cnt_pure n s1 s2 HC HS).
Qed.

Theorem AM_init : ltac2:(tb__ "0|0|
S2eOS1aS13S0A1S12S14S0SbA2A1SbSbF_;S2aS13S20A1S1fOF_;F_;S22S26R2A1S9R8S2bR4A1A2S2dScS2fZ2S2A2S21ScS27ScS1eR8R7R6R5R4A7S28S1dA1R3A4S23ScSdR3S29ScS1eS1dRaS10R8R7R6R5R4AaA4A4F_;F_;Frho1;FKc;FA;FU;FR;FX;Fn;FNG;F_;").
Proof.
  intros AB NG n X R U A Kc rho1 HVI [[(P1 & P2 & _ & _) _] | HC].
  - exact (am_IN_coop AB NG X R U A Kc rho1 HVI P1 P2).
  - apply ((trr_mono (tr_rules_angelic segsU Kc)) 0 (2 * PGSZ)); [unfold PGSZ; lia|].
    exact (AM_cnt segsU C_U IEC_U alloc_meta_avail_ex_P_proof NG n X R U A Kc rho1 HC).
Qed.
