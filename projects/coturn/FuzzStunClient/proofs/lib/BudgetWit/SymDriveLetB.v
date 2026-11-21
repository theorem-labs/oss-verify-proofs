(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* Modified by Theorem Labs, 2026-11: made from SymDriveLet.v: the R-typed declarations restated over the budget carrier, with twin modules imported last. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg MmapSim SymExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymCarryFast SymExecItab.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require SymExec3.
Import ListNotations.
Import SX2.
Import SX2S.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymDriveLet.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.BudgetWit Require Import Rzb SymDriveB.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.
Lemma rzb_run_C : forall segs fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R model T,
  sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
  carryC (s_log ss') kn [] = (kn', scs2, hs2) ->
  regs_ok E sr R -> know_ok segs E M kn ->
  scs_denot segs M E scs -> scs_denot segs M E scs2 ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall R' M', regs_ok E (s_regs ss') R' -> know_ok segs E M' kn' ->
     M' = mem_denot E M (s_log ss') ->
     Rzb.rzb segs (mkCfg (mkst R' (Z_to_bv 64 (s_pc ss')) M' rom) model) T) ->
  Rzb.rzb segs (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model) T.
Proof.
  intros segs fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R model T Hex Hc.
  rewrite carryC_eq in Hc. exact (SymDriveB.rzb_run segs fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R model T Hex Hc).
Qed.
Lemma rzb_run_CI : forall segs (t : SymExec3.SX2.itab), SymExec3.SX2.itab_sound segs t ->
  forall fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R model T,
  sym_execI segs t fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
  carryC (s_log ss') kn [] = (kn', scs2, hs2) ->
  regs_ok E sr R -> know_ok segs E M kn ->
  scs_denot segs M E scs -> scs_denot segs M E scs2 ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall R' M', regs_ok E (s_regs ss') R' -> know_ok segs E M' kn' ->
     M' = mem_denot E M (s_log ss') ->
     Rzb.rzb segs (mkCfg (mkst R' (Z_to_bv 64 (s_pc ss')) M' rom) model) T) ->
  Rzb.rzb segs (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model) T.
Proof.
  intros segs t Ht fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R model T Hex Hc.
  rewrite (sym_execI_eq segs t Ht) in Hex.
  exact (rzb_run_C segs fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R model T Hex Hc).
Qed.
Ltac l6_run HR HK fuel stops scr NX keep segs E sr R M kn pc rom model T pc1 SR LG knx nx1 scs scr' KN scs2 hs2 :=
  eapply (rzb_run_C segs fuel stops scr pc sr kn NX (SS pc1 SR LG knx nx1) scs scr' KN scs2 hs2 E M rom R model T);
  [ vm_cast_no_check (@eq_refl _ (SS pc1 SR LG knx nx1, scs, scr'))
  | vm_cast_no_check (@eq_refl _ (KN, scs2, hs2))
  | exact HR | exact HK
  | split_foralls
  | split_foralls
  | try reflexivity; try assumption
  | try reflexivity; try assumption
  | clear HR HK;
    let R' := fresh "R" in let M' := fresh "M" in let EQM := fresh "EQM" in
    intros R' M' HR HK EQM; cbn [s_pc s_regs s_log] in HR, EQM |- *;
    lazymatch keep with
    | true => idtac
    | false => clear EQM; try clear R; try clear M;
               try rename R' into R; try rename M' into M
    end ].
Ltac run_block_with_let HR HK fuel stops scr NX keep :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- Rzb.rzb _ (mkCfg (mkst R (Z_to_bv 64 ?pc) M ?rom) ?model) ?T =>
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn NX) []) in
        lazymatch r with
        | (SS ?pc1 ?sr1 ?log1 ?kn1 ?nx1, ?scs, ?scr') =>
          let c := eval vm_compute in (carryC log1 kn []) in
          lazymatch c with
          | (?kn', ?scs2, ?hs2) =>
            let lsr := l9_lits_sr in let llg := l9_lits_lg in let lkn := l9_lits_kn in
            l9_bind ident:(KSR) sr1 lsr ident:(SRl) ltac:(fun SR => l9_bind ident:(KLG) log1 llg ident:(LGl) ltac:(fun LG => l9_bind ident:(KKN) kn' lkn ident:(KNl) ltac:(fun KN =>
            first [ l6_same kn kn1;
                    l6_run HR HK fuel stops scr NX keep segs E sr R M kn pc rom model T pc1 SR LG kn nx1 scs scr' KN scs2 hs2
                  | l6_run HR HK fuel stops scr NX keep segs E sr R M kn pc rom model T pc1 SR LG kn1 nx1 scs scr' KN scs2 hs2 ])))
          end
        end
      end
    end
  end.
Ltac l6_runI TAB TABOK HR HK fuel stops scr NX keep segs E sr R M kn pc rom model T pc1 SR LG knx nx1 scs scr' KN scs2 hs2 :=
  eapply (rzb_run_CI segs TAB TABOK fuel stops scr pc sr kn NX (SS pc1 SR LG knx nx1) scs scr' KN scs2 hs2 E M rom R model T);
  [ vm_cast_no_check (@eq_refl _ (SS pc1 SR LG knx nx1, scs, scr'))
  | vm_cast_no_check (@eq_refl _ (KN, scs2, hs2))
  | exact HR | exact HK
  | split_foralls
  | split_foralls
  | try reflexivity; try assumption
  | try reflexivity; try assumption
  | clear HR HK;
    let R' := fresh "R" in let M' := fresh "M" in let EQM := fresh "EQM" in
    intros R' M' HR HK EQM; cbn [s_pc s_regs s_log] in HR, EQM |- *;
    lazymatch keep with
    | true => idtac
    | false => clear EQM; try clear R; try clear M;
               try rename R' into R; try rename M' into M
    end ].
Ltac run_block_with_letI TAB TABOK HR HK fuel stops scr NX keep :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ ?M ?kn =>
      lazymatch type of TABOK with SymExec3.SX2.itab_sound segs _ => idtac end;
      lazymatch goal with
      | |- Rzb.rzb _ (mkCfg (mkst R (Z_to_bv 64 ?pc) M ?rom) ?model) ?T =>
        let r := eval vm_compute in (sym_execI segs TAB fuel true stops scr (SS pc sr [] kn NX) []) in
        lazymatch r with
        | (SS ?pc1 ?sr1 ?log1 ?kn1 ?nx1, ?scs, ?scr') =>
          let c := eval vm_compute in (carryC log1 kn []) in
          lazymatch c with
          | (?kn', ?scs2, ?hs2) =>
            let lsr := l9_lits_sr in let llg := l9_lits_lg in let lkn := l9_lits_kn in
            l9_bind ident:(KSR) sr1 lsr ident:(SRl) ltac:(fun SR => l9_bind ident:(KLG) log1 llg ident:(LGl) ltac:(fun LG => l9_bind ident:(KKN) kn' lkn ident:(KNl) ltac:(fun KN =>
            first [ l6_same kn kn1;
                    l6_runI TAB TABOK HR HK fuel stops scr NX keep segs E sr R M kn pc rom model T pc1 SR LG kn nx1 scs scr' KN scs2 hs2
                  | l6_runI TAB TABOK HR HK fuel stops scr NX keep segs E sr R M kn pc rom model T pc1 SR LG kn1 nx1 scs scr' KN scs2 hs2 ])))
          end
        end
      end
    end
  end.
