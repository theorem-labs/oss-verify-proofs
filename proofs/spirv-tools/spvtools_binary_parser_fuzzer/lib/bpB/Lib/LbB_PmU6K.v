(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Section U6K.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variable LINV : mem -> Prop.

  Lemma pmk_sh_ffu : forall w s LB LBs m mo c ins tbl ftbl TB spal E k v,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> env_world H w E -> 0 <= k < 11584 ->
    fsh_at ins k = v ->
    kentry_ok ASEGS E m (KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_FF) (ELit k)) (ELit 3)) SHBASE) 1 (ELit v)).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal E k v OK X HE Hk <-. pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & _).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    assert (EF : edenot E (EVar WV_FF) = Z_to_bv 64 (wa_ff w)) by (apply (ev_wv H w E _ 1 _ HE eq_refl); [lia | reflexivity]).
    assert (Hj : (Z.to_nat (k / 8) < 1448)%nat)
      by (apply Nat2Z.inj_lt; rewrite Z2Nat.id by (apply Z.div_pos; lia); change (Z.of_nat 1448) with 1448; apply Z.div_lt_upper_bound; lia).
    assert (Hv : 0 <= fsh_at ins k < 256) by (unfold fsh_at; apply fsh_pat_byte_range).
    apply (kshadow E m _ (wa_ff w + k) (fsh_at ins k)); [apply ev_add; [exact EF | lia | lia] | lia | exact Hv | cbn [edenot]; reflexivity |].
    pose proof (shk_of_fsh m (wa_ff w) ins (Z.to_nat (k / 8)) (fsh_at ins k) (xa_fsh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) Hj eq_refl Hv) as S.
    rewrite Z2Nat.id in S by (apply Z.div_pos; lia).
    unfold shk in *.
    replace ((wa_ff w + k) / 8) with ((wa_ff w + 8 * (k / 8)) / 8); [exact S|].
    clear - G2. Z.div_mod_to_equations. lia.
  Qed.

  Definition ffsh_disj (off : Z) (wd : nat) (lg : list sentry) : bool :=
    forallb (fun e' => match e_addr e' with
                       | SA b o =>
                           (expr_eqb b (EVar WV_FF) && ((o + Z.of_nat (e_width e') <=? off) || (off + Z.of_nat wd <=? o)))
                           || (expr_eqb b FSHB && (SHBASE <=? o) && (o + Z.of_nat (e_width e') <=? SHBASE + 1448))
                       end)%bool lg.

  Lemma rw_cells_log_nth_ff : forall (w : pmwA H) E M lg (k : nat) (off : Z) (wd : nat) (v : expr) (c : cell),
    pmw_okA H w -> env_world H w E ->
    log_flat E lg -> nth_error lg k = Some (SE (SA (EVar WV_FF) off) wd v) ->
    ffsh_disj off wd (firstn k lg) = true -> 0 <= off -> off + Z.of_nat wd <= 11584 ->
    wr_at asegs M (wa_ff w + off) (Z.of_nat wd) ->
    csize c = wd -> cell_wf c -> cbytes c = word_to_le_bytes wd (edenot E v) ->
    rw_cells asegs (mem_denot E M lg) (wa_ff w + off) [c].
  Proof.
    intros w E M lg k off wd v c OK HE Hf Hn Hd H0 H1 HW Hc Hwf Hb.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof (ev_ff H w E OK HE) as EF. pose proof (ev_fshb H w E OK HE) as EFS.
    eapply (rw_cells_log_nth E M lg k (SA (EVar WV_FF) off) wd v (wa_ff w + off) c Hf Hn);
      [| unfold estart; cbn [a_base a_off]; rewrite EF; reflexivity | exact HW | exact Hc | exact Hwf | exact Hb].
    apply Forall_forall. intros e' He'. unfold ffsh_disj in Hd. rewrite forallb_forall in Hd. specialize (Hd e' He').
    destruct (e_addr e') as [b o] eqn:Ea. unfold estart. cbn [a_base a_off]. rewrite EF.
    apply orb_true_iff in Hd. destruct Hd as [Hd|Hd].
    - apply andb_true_iff in Hd as [Hbe Ho]. apply expr_eqb_true in Hbe. subst b. rewrite EF.
      apply orb_true_iff in Ho. destruct Ho as [Ho|Ho]; apply Z.leb_le in Ho; [left|right]; lia.
    - apply andb_true_iff in Hd as [Hd Ho2]. apply andb_true_iff in Hd as [Hbe Ho1]. apply expr_eqb_true in Hbe. subst b.
      apply Z.leb_le in Ho1. apply Z.leb_le in Ho2. rewrite EFS. unfold SHBASE in *.
      rewrite G13 in G6. unfold SHBASE in G6. destruct G6 as [G6|G6]; [right | left]; lia.
  Qed.
End U6K.
