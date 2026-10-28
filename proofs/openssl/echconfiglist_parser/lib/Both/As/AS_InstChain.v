(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsUnwind AsChain AW_MallocBase.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

  Theorem fch_of_achain : forall (m : mem) (sp s0 top bot ra lo : Z) (L : list (Z * Z)),
    achain m s0 L -> aceil <= lo -> lo + 16 <= sp -> sp mod 16 = 0 -> 0 <= ra < 2 ^ 64 ->
    exists CH : list (Z * Z),
         (goodframe bot sp top = true -> goodframe sp s0 top = true -> sp + 16 <= s0 /\ frame_chain asegs m top s0 CH)
      /\ (forall TRS pc0 md, 2 <= md -> trace_ok TRS pc0 (ra :: map snd L) ->
            In (utrace pc0 sp top bot md (icpt_chain ra s0 sp top CH)) TRS).
  Proof.
    intros m sp s0 top bot ra lo L AC CEIL LO SPA RA.
    assert (T1 : forall TRS pc0, trace_ok TRS pc0 (ra :: map snd L) -> In [pc0] TRS).
    { intros TRS pc0 [_ OK]. exact (OK 1%nat ltac:(lia)). }
    assert (T2 : forall TRS pc0, trace_ok TRS pc0 (ra :: map snd L) -> In [pc0; ra] TRS).
    { intros TRS pc0 [_ OK]. exact (OK 2%nat ltac:(lia)). }
    assert (NE : forall TRS pc0, trace_ok TRS pc0 (ra :: map snd L) -> (ra =? pc0) = false).
    { intros TRS pc0 [NI _]. apply Z.eqb_neq. intros E. apply NI. left. exact E. }
    destruct (goodframe bot sp top) eqn:G1.
    2:{ exists []. split; [intros F; discriminate F|]. intros TRS pc0 md MD TOK. unfold utrace. rewrite G1. destruct (top <? KPAGE); apply (T1 _ _ TOK). }
    destruct (goodframe sp s0 top) eqn:G2.
    2:{ exists []. split; [intros _ F; discriminate F|]. intros TRS pc0 md MD TOK. unfold utrace, icpt_chain. rewrite G1, G2.
        destruct (top <? KPAGE); [apply (T1 _ _ TOK)|].
        destruct (Z.lt_ge_cases ra KPAGE) as [LT|GE].
        - rewrite uloop_page by (cbn; lia). apply (T1 _ _ TOK).
        - rewrite uloop_last by (cbn; lia). unfold upush. rewrite (NE _ _ TOK). change ([pc0] ++ [ra]) with [pc0; ra]. apply (T2 _ _ TOK). }
    (* [comment removed for export] *)
    pose proof G2 as G2'. unfold goodframe in G2'. apply andb_true_iff in G2' as [G2a G2c]. apply andb_true_iff in G2a as [G2a G2b].
    apply Z.ltb_lt in G2a. apply Z.ltb_lt in G2b. apply Z.eqb_eq in G2c.
    inversion AC as [cur NIL E1 E2| cur L1 fp ra1 AC1 CUR RA1 AL16 LO16 HI REC E1 E2]; subst.
    { exfalso. destruct NIL as [NIL|NIL]; lia. }
    destruct (achain_frame_chain_gen top m L1 cur AC1 s0 ra1 REC ltac:(lia) CUR RA1) as (CHu & FC & UL).
    exists CHu. split.
    - intros _ _. split; [| exact FC]. clear - G2a SPA AL16. Z.div_mod_to_equations. lia.
    - intros TRS pc0 md MD TOK. unfold utrace, icpt_chain. rewrite G1, G2.
      destruct (top <? KPAGE); [apply (T1 _ _ TOK)|].
      destruct (Z.lt_ge_cases ra KPAGE) as [LT|GE].
      + rewrite uloop_page by (cbn; lia). apply (T1 _ _ TOK).
      + pose proof (frame_chain_nonnil _ _ _ _ _ FC) as NN. destruct CHu as [|x rest]; [congruence|].
        rewrite uloop_link by (cbn; lia). unfold upush. rewrite (NE _ _ TOK). change ([pc0] ++ [ra]) with [pc0; ra].
        destruct (UL pc0 md [pc0; ra] ltac:(intros K; apply (proj1 TOK); right; exact K)) as [j E]. rewrite E.
        change ([pc0; ra] ++ firstn j (ra1 :: map snd L1)) with (firstn (2 + j) (pc0 :: ra :: ra1 :: map snd L1)).
        apply (proj2 TOK). lia.
  Qed.
End HCW.
