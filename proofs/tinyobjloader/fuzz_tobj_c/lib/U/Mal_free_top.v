(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "@Corelib.Numbers.BinNums"; "Z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G3.Mal_fslow"; "rsv32_stmt"; "nt_contractR_P"; "nt_contractR_d_P"; "nt_contractR_ex_P"; "nt_contractR_exd_P"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_U"; "Pre_free"; "Pre_freeI"; "free_contract_U"; "free_contract_ex_U"; "@Corelib.Init.Datatypes"; "pair"; "prod"; "list"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "ameta"; "frame"; "sptr"; "FUser"; "astate"; "fkind"; "fr_kind"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv"; "free_drv_ex_U"; "J_free_drv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "@Corelib.Init.Logic"; "eq"; "or"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractS"; "J_free_S"; "free_drv_S_U"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickPost"; "quick_case"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "WF"; "frame_ptr"; "frames"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G2.Mal_free_quickE"; "J_free_drvST"; "J_free_drvT"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G1.Mal_fslow_I"; "slow_case"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymFrame SymSummary SymCall SymComplete ExampleMemcpy.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfInv MallocWfFrame MallocWfRepr MallocWfMain MallocLayout MallocFooter MallocIface MallocLaws Contract
  FreeQuickModel FreeQuickPost BlockView ContractDrv RoomS ContractS.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CallocLib.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt_R.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G1.Mal_fslow_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G2.Mal_free_quick2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G2.Mal_free_quickE OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G3.Mal_fslow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt_R.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import TopGlue.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma quick_or_slow : ltac2:(tb__ "0|2|
S15S13S11S1S12S24R5A1S2aSfSfSfS13S11A2M0S1A2M1S12A2SeG1S12SeG0S1SeS13S11R5R4A4R3A4R2A4S26R6A1A3S1fS16S17R3A1S14A3S20S23R8S25R6R5R4A3R7R6R5R4A6S29R8R7R6R5R4A5A2F_;F_;F_;Ffr;Fi;Fam;Fg;Fs;").
Proof.
  intros s g am i fr HW Hfr Hk. pose proof (frame_facts_of s g am i fr HW Hfr) as FF.
  destruct (Z.eq_dec (am_freed am) 0) as [F0 | Fnz]; [right; split; [exact Hfr | split; [exact Hk | left; exact F0]]|].
  destruct (Z.eq_dec (Z.lor (am_freed am) (am_avail am) + bit i) (ones (am_last am))) as [EA | NEA]; [right; split; [exact Hfr | split; [exact Hk | right; exact EA]]|].
  left. pose proof (inv_groups HW g am (ff_used _ _ _ _ _ FF)) as (Gm & _ & _ & Gcl & _).
  assert (Hsc : am_sc am < 48).
  { destruct Gcl as [(H63 & _ & _ & _ & Hf0 & _) | (Hsc & _)]; [exfalso; exact (Fnz Hf0) | lia]. }
  assert (Hl : 1 <= am_last am).
  { pose proof Gm as (Hl0 & _ & _ & _ & Hfnn & _ & Hhi & _). destruct (Z_lt_dec 0 (am_last am)); [lia|]. exfalso. apply Fnz.
    apply Z.bits_inj_0. intros nb. destruct (Z_lt_dec nb 0) as [Hn|Hn]; [apply Z.testbit_neg_r; lia|].
    destruct (Z.eq_dec nb 0) as [-> | Hn0].
    - pose proof (ff_i _ _ _ _ _ FF) as Hi. replace i with 0 in FF by lia. exact (ff_freed_i _ _ _ _ _ FF).
    - exact (proj2 (Hhi nb ltac:(lia))). }
  split; [exact Hfr|]. split; [exact Hk|]. split; [reflexivity|]. split; [exact Fnz|]. split; [exact NEA|]. split; [exact Hsc | exact Hl].
Qed.

Theorem free_contract_P_proof : ltac2:(tb__ "0|0|
S3S2S0A1ScF_;F_;").
Proof.
  intros NTC RSV. apply (free_contract_of_T segsU C_U EC_U). intros ok A Kc rho HS. apply triple_inh. intros w0 [_ (HMI & Hin & _)]. destruct A as [s L].
  unfold ma_blocks, blocks in Hin. cbn [ma_s ma_L] in Hin. apply in_map_iff in Hin as ([q n0] & E & Hub). cbn [fst snd] in E. injection E as E1 E2.
  destruct (user_block_frame s q n0 Hub) as (g & am & i & fr & Hfr & Hk & -> & ->).
  destruct (quick_or_slow s g am i fr (proj1 HMI) Hfr Hk) as [HQ | HSL].
  - exact (free_contract_quick ok (mkMA s L) Kc rho g am i fr HS HQ E1 E2).
  - exact (free_contract_slow_P ok (mkMA s L) Kc rho g am i fr NTC RSV HS HSL E1 E2).
Qed.

Theorem free_contract_ex_P_proof : ltac2:(tb__ "0|0|
S5S2S0A1SdF_;F_;").
Proof.
  intros NTC RSV. apply (free_contract_ex_of_T segsU C_U EC_U). intros A Kc rho HVI w0 Hw0. pose proof Hw0 as [_ (HMI & Hin & _)]. destruct A as [s L].
  unfold ma_blocks, blocks in Hin. cbn [ma_s ma_L] in Hin. apply in_map_iff in Hin as ([q n0] & E & Hub). cbn [fst snd] in E. injection E as E1 E2.
  destruct (user_block_frame s q n0 Hub) as (g & am & i & fr & Hfr & Hk & -> & ->).
  destruct (quick_or_slow s g am i fr (proj1 HMI) Hfr Hk) as [HQ | HSL].
  - exact (free_contract_quick_ex (mkMA s L) Kc rho g am i fr HQ E1 E2 w0 Hw0).
  - exact (free_contract_slow_ex_P (mkMA s L) Kc rho g am i fr NTC RSV HVI HSL E1 E2 w0 Hw0).
Qed.

Lemma SPJ_free_drv_T : ltac2:(tb__ "0|0|
S1eS1S1S10S19A1S18OF_;F_;S1bS1aS8S7S1dS7S0R6R5R4R3A6SaS9A1R2R1A5S8S7S28R7R6R5R4A4SbS9A1R3R2A5F_;Fw;Frho;FKc;FX;Fk;FA;").
Proof.
  intros A k X Kc rho w [Hsm [HJ HD]]. destruct (SPJ_free_T segsU C_U EC_U A Kc rho w (conj Hsm HJ)) as [Hsm' HJ'].
  split; [exact Hsm'|]. split; [exact HJ' | exact HD].
Qed.
Theorem free_drv_ex_P_proof : ltac2:(tb__ "0|0|
S6S2S0A1S1cF_;F_;").
Proof.
  intros NTC RSV A k X Kc rho HVI w0 Hw00. pose proof (SPJ_free_drv_T A k X Kc rho w0 Hw00) as Hw0. clear Hw00.
  pose proof Hw0 as [_ ((HMI & Hin & _) & _)]. destruct A as [s L].
  unfold ma_blocks, blocks in Hin. cbn [ma_s ma_L] in Hin. apply in_map_iff in Hin as ([q n0] & E & Hub). cbn [fst snd] in E. injection E as E1 E2.
  destruct (user_block_frame s q n0 Hub) as (g & am & i & fr & Hfr & Hk & -> & ->).
  destruct (quick_or_slow s g am i fr (proj1 HMI) Hfr Hk) as [HQ | HSL].
  - exact (free_drv_quick_ex (mkMA s L) k X Kc rho g am i fr HQ E1 E2 w0 Hw0).
  - exact (free_drv_slow_ex_P (mkMA s L) k X Kc rho g am i fr NTC RSV HVI HSL E1 E2 w0 Hw0).
Qed.

Theorem free_contract_P_closed : ltac2:(tb__ "0|0|
S2S0A1ScF_;").
Proof. intros RSV. exact (free_contract_P_proof nt_contractR_P_ok RSV). Qed.
Theorem free_contract_ex_P_closed : ltac2:(tb__ "0|0|
S2S0A1SdF_;").
Proof. intros RSV. exact (free_contract_ex_P_proof nt_contractR_ex_P_ok RSV). Qed.
Theorem free_drv_ex_P_closed : ltac2:(tb__ "0|0|
S2S0A1S1cF_;").
Proof. intros RSV. exact (free_drv_ex_P_proof nt_contractR_exd_P_ok RSV). Qed.

Lemma rsv32_P : rsv32_stmt C_U.
Proof.
  intros A rd wok vm g am i fr HMI Hin _.
  exact (ff_rsv32 _ _ _ _ _ (frame_facts_of (ma_s A) g am i fr (proj1 HMI) Hin)).
Qed.
Theorem free_contract_P_ok : free_contract_U.
Proof. exact (free_contract_P_closed rsv32_P). Qed.
Theorem free_contract_ex_P_ok : free_contract_ex_U.
Proof. exact (free_contract_ex_P_closed rsv32_P). Qed.
Theorem free_drv_ex_P_ok : free_drv_ex_U.
Proof. exact (free_drv_ex_P_closed rsv32_P). Qed.

Lemma SPJ_free_drvS_T : ltac2:(tb__ "0|0|
S1eS1S1S10S19A1S18OF_;F_;S1bS1aS8S7S21S7S0R6R5R4R3A6SaS9A1R2R1A5S8S7S27R7R6R5R4A4SbS9A1R3R2A5F_;Fw;Frho;FKc;FX;Fk;FA;").
Proof.
  intros A k X Kc rho w [Hsm [HJ HD]]. destruct (SPJ_free_T segsU C_U EC_U A Kc rho w (conj Hsm HJ)) as [Hsm' HJ'].
  split; [exact Hsm'|]. split; [exact HJ' | exact HD].
Qed.
Theorem free_drv_S_P_proof : ltac2:(tb__ "0|0|
S4S2S0A1S22F_;F_;").
Proof.
  intros NTC RSV ok A k X Kc rho HS. eapply triple_pre; [intros w Hw; exact (SPJ_free_drvS_T A k X Kc rho w Hw)|].
  apply triple_inh. intros w0 Hw0.
  pose proof Hw0 as [_ ((HMI & Hin & _) & _)]. destruct A as [s L].
  unfold ma_blocks, blocks in Hin. cbn [ma_s ma_L] in Hin. apply in_map_iff in Hin as ([q n0] & E & Hub). cbn [fst snd] in E. injection E as E1 E2.
  destruct (user_block_frame s q n0 Hub) as (g & am & i & fr & Hfr & Hk & -> & ->).
  destruct (quick_or_slow s g am i fr (proj1 HMI) Hfr Hk) as [HQ | HSL].
  - exact (U.Mal_free__G2.Mal_free_quickE.free_drv_quick_S ok (mkMA s L) k X Kc rho g am i fr HS HQ E1 E2).
  - pose proof (U.Mal_fslow__G3.Mal_fslow.free_drv_slow_S_P ok (mkMA s L) k X Kc rho g am i fr NTC RSV HS HSL E1 E2) as T. cbn [ma_s ma_L] in T.
    exact T.
Qed.
Theorem free_drv_S_P_ok : free_drv_S_U.
Proof. exact (free_drv_S_P_proof nt_contractR_d_P_ok rsv32_P). Qed.
