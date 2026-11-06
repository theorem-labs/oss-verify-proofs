(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Amb
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare Frame AgentLib
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
  Spec RefExitBase LibTail LibDiagKn RefPrintfBufBase.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import RefReadErr_defs RefReadErr_tail.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14listk16length37Corelib4Init5Logicm92eq69OSSVerifyaboost_jsonafuzz_parse6images5Plain1M~~~~~~o2floaded_segmentshfbbv_unsigned46Stdlib6ZArith6BinInt1Zt83addhf7Z_to_bvk16optiont82let86of_natk14Some69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~hhe3rdn69OSSVerify6Proofsaboost_jsonafuzz_parse3libfRefReadErr_tail~~~~~~hm03ENV69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymRun~~~~~~hq97vals_evk13appk14consk13natk13nilm93not37Corelib4Init3Natigc3add3h5LinuxProcessSemanticsfLinuxProcessSem3Runii55mkCfg3h5LinuxProcessSemanticsfLinuxProcessSem5Stateila4m_fs3h5LinuxProcessSemantics5Riscv7Preludeip05bvmaphhe4mksthhe7seg_rom69OSSVerify6Proofsaboost_jsonafuzz_parse3libfRefReadErr_defs~~~~~~it25knRE0it25srRE069OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~ji6dhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~jme8realizes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec~~~~~~jr5emsg_read_errorjr55t_die79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~kg77know_okkg77regs_ok36Stdlib5Lists4Listkm22In69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymDrive~~~~~~knb9junk_vals79OSSVerify6Proofsaboost_jsonafuzz_parse3libaRefReadErr7ReadErr~~~~~~ks36valsREila5Modelii58valid_spk14Noneila8m_haltedk14prodila9m_vm_lazyila7FdEntryila9FdChannelila9fd_lookupila5m_fdsm91Ihhe4getrt83subhf2BVhf4BvWfit26RE_STKhq96stk_okm93and01Zt82lt69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9LibDiagKn~~~~~~lrc8cells_oklrcadiag_cells3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsmh2h0word_to_le_bytest83powlrc9canary_ok" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ReadErr.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable sp0 : word.                 (* [comment removed for export] *)
  Variable BL : ltac2:(zQ "30!l9!h9!jc@1$0@1$0@1$2@1$1#8").
  Variable model : ltac2:(zQ "10!lh2$0").
  Hypothesis Hvsp : ltac2:(zQ "10!lhb@1$0?3sp0").
  Hypothesis Hh : ltac2:(zQ "60!h9!jc!li7!hg0!nd!lie@3$4@1$3@1$1@1$0#k0@1$5?5model@1$2@1$1@1$0#k0").
  Hypothesis Hlazy : ltac2:(zQ "71!h9!jc!lja!l9!ig0!nd!lk1&@2$2@1$1@1$0#k0@1$1@1$0#k0@3$5@1$3~0@1$6?5model@1$4~0").
  Hypothesis Hfd2 : ltac2:(zQ "90!h9!lke!v6!hh7!hg0!nd!ll9!lm6!ln3@3$5@1$4$1@2$7@1$8?5model@2$2@1$0#k0+2@2$3$1@1$6@2$2@1$0#k0+2").

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  (* [comment removed for export] *)
  Theorem re_tail : ltac2:(zQ "i40!h9!jc!l9!m0!nd!r8!sa!v0!v6!hg0!hg9!hge!hh7!hl9!hq2!hu2!hud!hv3!hva!ig0!ig6!ihe!il1!io8!ir6!irf!is7!jh4!jhd!jld!jq9!juc!jve!kkc!kl7!kn5>4path@1$2@1$1@1$0#8>2pp@1$1@1$0#k0>2t8@1$2@1$1@1$0#8>4vals@1$2@1$1@1$0#k0>1R@2$h8@1$0#5@1$1@1$0#k0>1M>0@1$1@1$0#k0@1$9@1$1@1$0#8>0@1$h4@3$i3@1$1@1$0#8@2$8@1$0#8Z^6>0@2$a@1$b@2$3@1$1@1$0#8^7+jc>0@3$4$h2@2$3@1$1@1$0#k0^5Ni7>0@3$4@1$1@1$0#k0@2$f^6N0?3sp0>0@3$4@1$1@1$0#k0@2$f^7N2^9>0@2$a@2$6@1$0#k0?3sp0@2$6@1$0#k0^a>0@2$a@2$7@2$7@2$6@1$0#k0^b@1$b@2$3@1$1@1$0#8^c+8@2$7@2$6@1$0#k0?3sp0+kgggg0>0@3$i2@2$e?2BL^a$hc^9>0@4$i1$5@2$e?2BL^b^9$hb>0@3$4@1$9@1$2@1$1@1$0#8@4$d$5^a^e@2$h5@2$3@1$1@1$0#8^fN1@2$c@1$2@1$1@1$0#8@3$h0@1$1@1$0#8^f@3$h1@1$1@1$0#8@2$8@1$0#8Z@1$h3@1$1@1$0#8>0@3$4@1$9@1$2@1$1@1$0#8@4$d$5^b@2$8@1$0#k0@2$7@2$6@1$0#k0^f@1$b@2$3@1$1@1$0#8^h0N8@2$c@1$2@1$1@1$0#8^e@4$he$5$hd@2$h6@5$h9?2fx^d@2$8@1$0#k0+knlvc^c@1$ha$5?5model@2$i0@1$hf^h1@1$h7?5model").
  Proof.
    intros path pp t8 vals R M Hnonul HPl HL P0 P2 Hpp1 Hpp2 HR HK Hstr Ht8.
    unfold t_die.
    eapply (re_segBC sp0 BL model Hvsp Hh Hlazy path pp (Z.of_nat (length path)) _ t8 vals);
      try eassumption; try lia.
    intros vals' R' M' HL' Q0 Q2 Q113 HR' HK' Hstr'.
    eapply (re_segF sp0 BL model Hvsp Hh Hlazy Hfd2 path pp _ vals'); try eassumption; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Variables (pp : word) (tid can : Z) (R : bvmap 5 word) (M : word -> option byte).
  (* [comment removed for export] *)
  Hypothesis Rsp : ltac2:(zQ "a0!h9!lnc!nd!lo0!lo8!loe!lp3!v6!jc!sa@3$2@1$8@1$0#k0@2$3?1R@3$5@1$0#5+2Kv$1@2$6@1$0#5+2@2$7@1$0#k0@2$4@2$9@1$0#k0?3sp0+o0").
  Hypothesis Rtp : ltac2:(zQ "80!h9!lnc!nd!lo0!loe!lp3!v6!jc@3$2@1$7@1$0#k0@2$3?1R@3$4@1$0#5+4Kv$1@2$5@1$0#5+4@2$6@1$0#k0+hgrmr8").
  Hypothesis Rs2 : ltac2:(zQ "70!h9!lnc!nd!lo0!loe!lp3!jc@3$2@1$6@1$0#k0@2$3?1R@3$4@1$0#5+h2Kv$1@2$5@1$0#5+h2?2pp").
  (* [comment removed for export] *)
  Hypothesis Mstack : ltac2:(zQ "70!h9!lpa!lq4!r8!lo8!v6!sa@4$2$3?1M@2$5@1$0#k0@2$4@2$6@1$0#k0?3sp0+o0$1").
  (* [comment removed for export] *)
  Hypothesis Mro : ltac2:(zQ "a0!h9!jc!li7!hg0!lqe!nd!lr4!hg9!lr7!v6>1i$6>0@2$4@2$7+hggg0^1@2$8^1+vhgg0@3$5@1$3@1$1@1$0#8@1?1M@2$9@1$0#k0^2@1$2@1$1@1$0#8").
  (* [comment removed for export] *)
  Hypothesis Mcells : ltac2:(zQ "20!lv8!mg4@2$0?1M$1").
  (* [comment removed for export] *)
  Hypothesis Mtid : ltac2:(zQ "a0!h9!l9!v6!jc!hh7!hg0!nd!mk9!hl9!r8@3$6@1$5@1$1@1$3@1$0#8@4$8$9?1M@2$2@1$0#k0+hgrmh0N4@2$4@1$1@1$3@1$0#8@2$7N4@2$2@1$0#k0?3tid").
  Hypothesis Htid : ltac2:(zQ "30!lr7!lqe!mle@2$1@2$0Z?3tid@2$0?3tid@2$2+2+h6").
  (* [comment removed for export] *)
  Hypothesis Mcan : ltac2:(zQ "10!mm4@2$0?1M?3can").
  (* [comment removed for export] *)
  Hypothesis Hpp1 : ltac2:(zQ "30!h9!sa!hg9@2$2@2$1@1$0#k0?3sp0@2$1@1$0#k0?2pp").

  Definition valsRE : ltac2:(zQ "30!l9!h9!jc@1$0@1$2@1$1#k0") := ltac2:(zQ "70!h9!jc!hv3!v6!hud!ig0!kr6@3$4@1$1@1$0#k0@3$2@1$1@1$0#k0?3sp0@3$2@1$1@1$0#k0@2$3@1$0#k0?3can@3$2@1$1@1$0#k0?2pp@3$2@1$1@1$0#k0?2pp@3$2@1$1@1$0#k0?2pp@3$2@1$1@1$0#k0@2$3@1$0#k0?3tid@1$5@1$1@1$0#k0@3$4@1$1@1$0#k0@1$6?1R@3$2@1$1@1$0#k0@2$3@1$0#k0Z@1$5@1$1@1$0#k0").
  Let E : env := ENV BL valsRE.

  Lemma valsRE_len : ltac2:(zQ "60!m0!hva!nd!h9!lg8!jc@3$2$1@2$0@1$5@1$3#k0$4Ni7").
  Proof. unfold valsRE. rewrite !length_app, junk_vals_length. reflexivity. Qed.

  Lemma evRE_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold E, ENV. cbn [ev]. unfold valsRE.
    change (6 + i)%nat with (length [sp0; Z_to_bv 64 can; pp; pp; pp; Z_to_bv 64 tid] + i)%nat.
    unfold vals_ev. rewrite app_nth2_plus, app_nth1 by (rewrite junk_vals_length; exact Hi).
    unfold junk_vals. rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.

  Lemma spxRE_val : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
  Proof. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev E 0) with sp0.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

  Ltac reg_caseRE :=
    cbn [nth srRE0 allregs32];
    first [ rewrite spxRE_val
          | lazymatch goal with |- _ = edenot _ (EVar ?n) =>
              change (edenot E (EVar n)) with (ev E n);
              first [ rewrite (evRE_junk (n - 6)) by lia; reflexivity | idtac ]
            | |- _ => cbn [edenot] end ];
    first [ reflexivity
          | exact Rtp | exact Rs2
          | rewrite Rsp, alu_add; change (ev E 0) with sp0; unfold v_add; apply bv_eq;
            rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, Zplus_mod_idemp_r; f_equal; lia
          | idtac ].

  Lemma regs_okRE : regs_ok E srRE0 R.
  Proof.
    pose proof SPlo. pose proof SPhi.
    apply regs_ok_by_idx.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_caseRE.
  Qed.

  Lemma know_okRE : (bv_unsigned pp + 8 <= bv_unsigned sp0 + 4194304)%Z -> know_ok RSEGS E M knRE0.
  Proof.
    intros Hpp2. pose proof SPlo. pose proof SPhi. pose proof SPal.
    unfold knRE0. apply know_ok_app; [|apply know_ok_app; [apply diag_cells_know; exact Mcells|]].
    - repeat (apply Forall_cons); [ .. | apply Forall_nil ].
      + apply kalign_intro; [lia|]. change (edenot E (EVar 0)) with sp0. exact SPal.
      + apply krange_intro. change (edenot E (EVar 0)) with sp0. lia.
      + (* [comment removed for export] *) cbn [kentry_ok]. split; [apply flat_intro; cbn; unfold RE_STK; lia|].
        intros d m Hd Hm. unfold estart. cbn [a_base a_off]. change (edenot E (EVar 0)) with sp0.
        pose proof (Mstack (Z_to_bv 64 (bv_unsigned sp0 + (-128 - RE_STK) + d)) m) as Hs.
        rewrite !u_small in Hs by (unfold RE_STK in *; lia). apply Hs; unfold RE_STK in *; lia.
      + apply krange_intro. change (edenot E (EVar 2)) with pp. lia.
      + (* [comment removed for export] *) cbn [kentry_ok]. split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|].
        intros d m Hd Hm. unfold estart. cbn [a_base a_off edenot]. rewrite (u_small 0) by lia.
        apply store_ok_data; rewrite u_small by lia; lia.
      + apply kimg_intro; [lia|lia|exact Mro].
      + eapply (kword_intro RSEGS E M (ELit 0) (Z_to_bv 64 0) 0x10b610 4 (EVar 5) (Z_to_bv 64 tid));
          [reflexivity | reflexivity | lia | lia | rewrite (u_small 0) by lia; lia | rewrite (u_small 0) by lia; lia |].
        rewrite (u_small 0) by lia. exact Mtid.
      + apply (canary_know E M 1 can); [reflexivity | exact Mcan].
    - apply Forall_cons; [|apply Forall_nil].
      apply krange_intro. change (edenot E (EVar 5)) with (Z_to_bv 64 tid : word). rewrite u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem ref_read_error : ltac2:(zQ "hc0!h9!jc!l9!m0!r8!v0!v6!hge!sa!hh7!hg0!nd!hl9!hg9!hud!hv3!ig0!ig6!ihe!il1!io8!irf!is7!jld!jq9!juc!jve!kn5>4path@1$2@1$1@1$0#8>2t8@1$2@1$1@1$0#8>0@1$h1@3$hb@1$1@1$0#8@2$6@1$0#8Z^2>0@2$d@1$7@2$3@1$1@1$0#8^3+jc>0@2$d@2$5@2$5@2$8@1$0#k0?2pp@1$7@2$3@1$1@1$0#8^4+8@2$5@2$8@1$0#k0?3sp0+kgggg0>0@3$b@1$a@1$2@1$1@1$0#8@4$c$4?1M?2pp@2$h2@2$3@1$1@1$0#8^5N1@2$9@1$2@1$1@1$0#8@3$e@1$1@1$0#8^5@3$f@1$1@1$0#8@2$6@1$0#8Z@1$h0@1$1@1$0#8>0@3$b@1$a@1$2@1$1@1$0#8@4$c$4?1M@2$6@1$0#k0@2$5@2$8@1$0#k0?2pp@1$7@2$3@1$1@1$0#8^6N8@2$9@1$2@1$1@1$0#8^5@4$h8$4$h7@2$h3@5$h5?2fx?1R@2$6@1$0#k0+knlvc?1M@1$h6$4?5model@2$ha@1$h9^7@1$h4?5model").
  Proof.
    intros path t8 Hnonul HPl Hpp2 Hstr Ht8.
    eapply (re_tail path pp t8 valsRE R M); try eassumption.
    - apply valsRE_len.
    - reflexivity.
    - reflexivity.
    - apply regs_okRE.
    - apply know_okRE. lia.
  Qed.

End ReadErr.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
