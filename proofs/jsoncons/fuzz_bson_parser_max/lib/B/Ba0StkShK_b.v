(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AgentLib AxSymExec3K AxSymExec3SoundK AxSymRun3K
  AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DefsK_b Ba0PlanImagesK_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HandoffBridgeK HandoffLedgerK HandoffBInvK HandoffCellsK HandoffRolesK.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0HandoffK_b Ba0HSK_0_b Ba0HSK_1_b Ba0MainTableK_b Ba0HandoffInstK_b Ba0ArtHandoffK_b Ba0ArtHandoffInstK_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIface HeapIfaceA HeapIfaceABx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition E_SHB : expr := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 512) (EVar 10)).
Definition E_SHL : expr := EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-512)) (EVar 10))) (ELit 17592187092992).
Definition K_STKSH : kentry := KZero (SA E_SHB 2146402304) E_SHL.

Definition stksh_chk (cs : acs) : bool :=
  let k := kn cs in (existsb (kentry_eqb K_STKSH) k && lin_nowrapR k E_SHB && lin_nowrapR k E_SHL)%bool.

Lemma stksh_chk_0 : stksh_chk HS_0 = true.   Proof. vm_compute. reflexivity. Qed.
Lemma stksh_chk_1 : stksh_chk HS_1 = true.   Proof. vm_compute. reflexivity. Qed.

Section StkSh.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
  #[local] Notation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
  #[local] Notation usp := (bv_unsigned sp).

  Variable cs : acs.
  Hypothesis SCHK : stksh_chk cs = true.
  Hypothesis GCHK : geo_chk cs = true.
  Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis HC : CSOK E cs R FULL model.

  Ltac LINEQS e H :=
    let Hn := fresh in
    assert (Hn : lin_nowrapR (kn cs) e = true)
      by (let G := fresh in pose proof SCHK as G; unfold stksh_chk in G; repeat (let X := fresh in apply andb_prop in G as [G X]); assumption);
    pose proof (hb_lin ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model e HC Hn) as H; clear Hn;
    unfold LZ in H;
    match type of H with context [lin_of ?x] => let l := eval vm_compute in (lin_of x) in change (lin_of x) with l in H end;
    cbv [AX2SK.lden AX2SK.tden fst snd AX2SK.uE] in H; cbn [edenot] in H;
    repeat match type of H with context [bv_unsigned (ev E ?n)] => change (bv_unsigned (ev E n)) with (VZ E n) in H end;
    rewrite ?Z.add_0_r in H.

  #[using="brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit SCHK GCHK R model HC"] Theorem stksh_main : forall x,
    in_shadow_of (usp - 8388608) (Z.max usp (uE E (topE cs)) - (usp - 8388608)) x -> byte_at FULL x 0.
  Proof.
    intros x Hx.
    assert (Hin : In K_STKSH (kn cs)).
    { apply hb_knb_In. pose proof SCHK as G. unfold stksh_chk in G. repeat (let X := fresh in apply andb_prop in G as [G X]). assumption. }
    destruct (hb_zero_k ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ _ HC Hin) as [Hf Hz].
    unfold estart, elenZ in Hz. cbn [a_base a_off] in Hz.
    remember (bv_unsigned (edenot E E_SHB)) as shb eqn:Eb. remember (bv_unsigned (edenot E E_SHL)) as shl eqn:El.
    LINEQS E_SHB L1. rewrite <- Eb in L1. LINEQS E_SHL L2. rewrite <- El in L2.
    pose proof (hbi_sp0 ASEGS0 ASAN0 APH0 sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit E cs R FULL model HC) as U0.
    destruct (geo_stk sp brk0 rdraw argv envp uid hw fs cs GCHK E R FULL model HC) as (_ & _ & _ & _ & TOP).
    assert (SR : 0x7fff80000000 <= usp <= 2 ^ 47) by (destruct Hsp as (H1 & H2 & H3); unfold sp_window_lo, sp_window_hi in H1, H2; lia).
    pose proof (Z.ge_le _ _ (Z.le_ge _ _ (proj1 (u64_range (ev E 6))))) as V6. change (bv_unsigned (ev E 6)) with (VZ E 6) in V6.
    unfold in_shadow_of, S, SB in Hx.
    set (mx := Z.max usp (uE E (topE cs))) in *.
    replace (usp - 8388608 + (mx - (usp - 8388608)) - 1) with (mx - 1) in Hx by ring.
    assert (D1 : shb - 1048576 <= (usp - 8388608) / 8).
    { replace (shb - 1048576) with ((8 * shb - 8388608) / 8) by (replace (8 * shb - 8388608) with ((shb - 1048576) * 8) by ring; apply Z.div_mul; lia).
      apply Z.div_le_mono; lia. }
    assert (D2 : (mx - 1) / 8 <= (2 ^ 47 - 1) / 8) by (apply Z.div_le_mono; lia).
    change ((2 ^ 47 - 1) / 8) with 17592186044415 in D2.
    unfold byte_at. replace x with (shb + 2146402304 + (x - (shb + 2146402304))) by ring. apply Hz. lia.
  Qed.
  (* [comment removed for export] *)
  #[using="brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit cs SCHK GCHK E R model HC"] Theorem stksh_main_hi : forall x,
    in_shadow_of (usp - 8388608) (2 ^ 47 - (usp - 8388608)) x -> byte_at FULL x 0.
  Proof.
    intros x Hx.
    assert (Hin : In K_STKSH (kn cs)).
    { apply hb_knb_In. pose proof SCHK as G. unfold stksh_chk in G. repeat (let X := fresh in apply andb_prop in G as [G X]). assumption. }
    destruct (hb_zero_k ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ _ HC Hin) as [Hf Hz].
    unfold estart, elenZ in Hz. cbn [a_base a_off] in Hz.
    remember (bv_unsigned (edenot E E_SHB)) as shb eqn:Eb. remember (bv_unsigned (edenot E E_SHL)) as shl eqn:El.
    LINEQS E_SHB L1. rewrite <- Eb in L1. LINEQS E_SHL L2. rewrite <- El in L2.
    pose proof (hbi_sp0 ASEGS0 ASAN0 APH0 sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit E cs R FULL model HC) as U0.
    destruct (geo_stk sp brk0 rdraw argv envp uid hw fs cs GCHK E R FULL model HC) as (_ & _ & _ & _ & TOP).
    assert (SR : 0x7fff80000000 <= usp <= 2 ^ 47) by (destruct Hsp as (H1 & H2 & H3); unfold sp_window_lo, sp_window_hi in H1, H2; lia).
    pose proof (Z.ge_le _ _ (Z.le_ge _ _ (proj1 (u64_range (ev E 6))))) as V6. change (bv_unsigned (ev E 6)) with (VZ E 6) in V6.
    unfold in_shadow_of, S, SB in Hx.
    set (mx := 2 ^ 47) in *.
    replace (usp - 8388608 + (mx - (usp - 8388608)) - 1) with (mx - 1) in Hx by ring.
    assert (D1 : shb - 1048576 <= (usp - 8388608) / 8).
    { replace (shb - 1048576) with ((8 * shb - 8388608) / 8) by (replace (8 * shb - 8388608) with ((shb - 1048576) * 8) by ring; apply Z.div_mul; lia).
      apply Z.div_le_mono; lia. }
    assert (D2 : (mx - 1) / 8 <= (2 ^ 47 - 1) / 8) by (apply Z.div_le_mono; lia).
    change ((2 ^ 47 - 1) / 8) with 17592186044415 in D2.
    unfold byte_at. replace x with (shb + 2146402304 + (x - (shb + 2146402304))) by ring. apply Hz. lia.
  Qed.
End StkSh.

(* [comment removed for export] *)
Theorem as0_stksh_main :
  forall sp brk0 rdraw argv envp uid hw fs, valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  forall h, (h < 2)%nat -> forall E R FULL model,
    APSK.cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT (SINV0 APH0 sp rdraw brk0 argv envp uid hw) (argH0 APH0 sp rdraw argv envp uid hw) fs E (HSA h) R FULL model ->
    forall x, in_shadow_of (bv_unsigned sp - 8388608) (Z.max (bv_unsigned sp) (APSK.uE E (topE (HSA h))) - (bv_unsigned sp - 8388608)) x -> byte_at FULL x 0.
Proof.
  intros sp brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit h Hh E R FULL model HC.
  destruct h as [|[|h]]; [| |lia].
  - exact (stksh_main sp brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit HS_0 stksh_chk_0 geo_chk_0 E R FULL model HC).
  - exact (stksh_main sp brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit HS_1 stksh_chk_1 geo_chk_1 E R FULL model HC).
Qed.

Theorem as0_stksh_main_hi :
  forall sp brk0 rdraw argv envp uid hw fs, valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  forall h, (h < 2)%nat -> forall E R FULL model,
    APSK.cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT (SINV0 APH0 sp rdraw brk0 argv envp uid hw) (argH0 APH0 sp rdraw argv envp uid hw) fs E (HSA h) R FULL model ->
    forall x, in_shadow_of (bv_unsigned sp - 8388608) (2 ^ 47 - (bv_unsigned sp - 8388608)) x -> byte_at FULL x 0.
Proof.
  intros sp brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit h Hh E R FULL model HC.
  destruct h as [|[|h]]; [| |lia].
  - exact (stksh_main_hi sp brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit HS_0 stksh_chk_0 geo_chk_0 E R FULL model HC).
  - exact (stksh_main_hi sp brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit HS_1 stksh_chk_1 geo_chk_1 E R FULL model HC).
Qed.
