(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr CellsX TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AsConst AsIface AsUnwind AsChain AW_MallocBase.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4list46Stdlib6ZArith6BinInt1Zjb2lehc4prod37Corelib4Init5Logiclf3andlf2eqhc4boolhc4true79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsUnwind~~~~~~oc9goodframejb3addjb3powhc4conshc3sndlf2ex37Corelib5Lists7ListDefv43map79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~hh15asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsdAW_MallocBase~~~~~~hl5aicpt_chain79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsChain~~~~~~hq66achain79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsIface~~~~~~hud3memhud8trace_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsShadow~~~~~~ijd5aceilocbframe_chainoc6utrace36Stdlib5Lists4Listipb2Injb2ltjb6modulo" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

  Theorem fch_of_achain : ltac2:(zQ "ha0!h9!j4!l3!l8!n3!n9!ne!o5!sa!t6!tc!u2!u9!uf!hgb!hkc!hp8!hu3!iia!ij1!inb!io4!ip2!iqe!ir4!ir9>1m$h2>2sp$0>2s0$0>3top$0>3bot$0>2ra$0>2lo$0>1L@1$1@2$3$0$0>0@4$h1?5HCEIL^8^6^1>0@2$2@1$h4?5HCEIL^3>0@2$2@2$9^4+h0^9>0@3$5$0@2$h9^a+h0Z>0@2$4@2$2Z^7@2$h8^7@2$a+2+k0>0@2$2^a@2$a+2+if@2$d@1$1@2$3$0$0\2CH@1$1@2$3$0$0@2$4>0@3$5$6@3$8^b^e^c$7>0@3$5$6@3$8^f^e^d$7@2$4@2$2@2$9^h0+h0^f@5$h5$f^h1^e^f^3>3TRS@1$1@1$1$0>3pc0$0>2md$0>0@2$2+2^1>0@3$h3^4^3@3$b$0^e@4$e@2$3$0$0$0@2$c$0$0^c@3$h7@1$1$0@6$h6^4^h3^h1^h0^3@5$h0^f^h2^h3^h1^6^5").
  Proof.
    intros m sp s0 top bot ra lo L AC CEIL LO SPA RA TOPU.
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
    inversion AC as [cur NIL E1 E2| cur NILH E1 E2| cur L1 fp ra1 AC1 CUR RA1 AL16 LO16 HI REC E1 E2]; subst.
    { exfalso. destruct NIL as [NIL|NIL]; lia. }
    { exfalso. unfold AAPP_HI in NILH. lia. }
    ndestruct (achain_frame_chain_gen top ltac:(unfold AAPP_HI; exact TOPU) m L1 cur AC1 s0 ra1 REC ltac:(lia) CUR RA1) as (CHu & FC & UL).
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
