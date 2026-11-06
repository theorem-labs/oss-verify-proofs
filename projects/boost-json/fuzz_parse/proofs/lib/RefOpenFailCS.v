(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import RefOpenFailCS_defs RefOpenFailCS_tail RefOpenFailCS_tail2.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14listk16length46Stdlib6ZArith6BinInt1Zm93addhfbbv_unsigned37Corelib4Init5Logicp52eq69OSSVerifyaboost_jsonafuzz_parse6images5Plain1M~~~~~~qefloaded_segmentsm92lem96of_nathf7Z_to_bvk16optionk14Some69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~hhe3rdn69OSSVerify6Proofsaboost_jsonafuzz_parse3libh2RefOpenFailCS_tail~~~~~~hm03ENV69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymRun~~~~~~hqd7vals_evk13appk14consk13natk13nilp53not37Corelib4Init3Natih03add3h5LinuxProcessSemanticsfLinuxProcessSem3Runii95mkCfg3h5LinuxProcessSemanticsfLinuxProcessSem5Stateile4m_fs3h5LinuxProcessSemantics5Riscv7Preludeip45bvmaphhe4mksthhe7seg_rom69OSSVerify6Proofsaboost_jsonafuzz_parse3libh2RefOpenFailCS_defs~~~~~~it64knB0it64srB069OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~jicdhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~jn48realizes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec~~~~~~jrbfmsg_cannot_openjrb5t_die79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~kge7know_okkge7regs_ok36Stdlib5Lists4Listkm92In69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymDrive~~~~~~ko29junk_vals79OSSVerify6Proofsaboost_jsonafuzz_parse3libdRefOpenFailCSaOpenFailCS~~~~~~ksa6valsOFile5Modelii98valid_spk14Noneile8m_haltedk14prodile9m_vm_lazyile7FdEntryile9FdChannelile9fd_lookupile5m_fdsp51Ihhe4getrm93subhf2BVhf4BvWfit66OF_STKhqd6stk_okp53and01Zm92lt69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9LibDiagKn~~~~~~ls98cells_okls9adiag_cells3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsmhfh0word_to_le_bytesm93powls99canary_ok" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section OpenFailCS.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable sp0 : word.                 (* [comment removed for export] *)
  Variable BL : ltac2:(zQ "30!l9!h9!jc@1$0@1$0@1$2@1$1#8").
  Variable model : ltac2:(zQ "10!lhf$0").
  Hypothesis Hvsp : ltac2:(zQ "10!li8@1$0?3sp0").
  Hypothesis Hh : ltac2:(zQ "60!h9!jc!lj4!hge!q9!ljb@3$4@1$3@1$1@1$0#k0@1$5?5model@1$2@1$1@1$0#k0").
  Hypothesis Hlazy : ltac2:(zQ "71!h9!jc!lk7!l9!ig4!q9!lke&@2$2@1$1@1$0#k0@1$1@1$0#k0@3$5@1$3~0@1$6?5model@1$4~0").
  Hypothesis Hfd2 : ltac2:(zQ "90!h9!llb!hg4!hh7!hge!q9!lm6!ln3!lo0@3$5@1$4$1@2$7@1$8?5model@2$2@1$0#k0+2@2$3$1@1$6@2$2@1$0#k0+2").

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  (* [comment removed for export] *)
  Theorem of_tail_cs : ltac2:(zQ "i40!h9!jc!l9!m0!o1!o7!q9!u4!v6!vb!hg4!hge!hh7!hl9!hq6!hu6!hv1!hv7!hve!ig4!iga!ii2!il5!ioc!ira!is3!isb!jhc!ji4!jm3!jqf!jv2!kg5!kl3!kle!knc>4path@1$2@1$1@1$0#8>2pp@1$1@1$0#k0>2t8@1$2@1$1@1$0#8>4vals@1$2@1$1@1$0#k0>1R@2$h8@1$0#5@1$1@1$0#k0>1M>0@1$1@1$0#k0@1$b@1$1@1$0#8>0@1$h4@3$i3@1$1@1$0#8@2$a@1$0#8Z^6>0@2$8@1$9@2$3@1$1@1$0#8^7+hvvvf>0@3$6$h2@2$3@1$1@1$0#k0^5Ni7>0@3$6@1$1@1$0#k0@2$f^6N0?3sp0>0@3$6@1$1@1$0#k0@2$f^7N2^9>0@2$8@2$5@1$0#k0?3sp0@2$5@1$0#k0^a>0@2$8@2$4@2$4@2$5@1$0#k0^b@1$9@2$3@1$1@1$0#8^c+8@2$4@2$5@1$0#k0?3sp0+kgggg0>0@2$8@2$4@2$4@2$5@1$0#k0^c@1$9@2$3@1$1@1$0#8^d+8+ogggggggggg0>0@3$i2@2$e?2BL^b$hc^a>0@4$i1$7@2$e?2BL^c^a$hb>0@3$6@1$b@1$2@1$1@1$0#8@4$d$7^b^f@2$h5@2$3@1$1@1$0#8^h0N1@2$c@1$2@1$1@1$0#8@3$h0@1$1@1$0#8^h0@3$h1@1$1@1$0#8@2$a@1$0#8Z@1$h3@1$1@1$0#8>0@3$6@1$b@1$2@1$1@1$0#8@4$d$7^c@2$a@1$0#k0@2$4@2$5@1$0#k0^h0@1$9@2$3@1$1@1$0#8^h1N8@2$c@1$2@1$1@1$0#8^f@4$he$7$hd@2$h6@5$h9?2fx^e@2$a@1$0#k0+knmm0^d@1$ha$7?5model@2$i0@1$hf^h2@1$h7?5model").
  Proof. exact (of_tail sp0 BL model Hvsp Hh Hlazy Hfd2). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Variables (pp : word) (tid can : Z) (R : bvmap 5 word) (M : word -> option byte).
  (* [comment removed for export] *)
  Hypothesis Rsp : ltac2:(zQ "a0!h9!lo9!q9!lod!lp5!lpb!lq0!hg4!jc!o7@3$2@1$8@1$0#k0@2$3?1R@3$5@1$0#5+2Kv$1@2$6@1$0#5+2@2$7@1$0#k0@2$4@2$9@1$0#k0?3sp0+o0").
  Hypothesis Rtp : ltac2:(zQ "80!h9!lo9!q9!lod!lpb!lq0!hg4!jc@3$2@1$7@1$0#k0@2$3?1R@3$4@1$0#5+4Kv$1@2$5@1$0#5+4@2$6@1$0#k0+hgrmr8").
  Hypothesis Rs2 : ltac2:(zQ "70!h9!lo9!q9!lod!lpb!lq0!jc@3$2@1$6@1$0#k0@2$3?1R@3$4@1$0#5+h2Kv$1@2$5@1$0#5+h2?2pp").
  (* [comment removed for export] *)
  Hypothesis Mstack : ltac2:(zQ "70!h9!lq7!lr1!u4!lp5!hg4!o7@4$2$3?1M@2$5@1$0#k0@2$4@2$6@1$0#k0?3sp0+o0$1").
  (* [comment removed for export] *)
  Hypothesis Mro : ltac2:(zQ "a0!h9!jc!lj4!hge!lrb!q9!ls1!v6!ls4!hg4>1i$6>0@2$4@2$7+hggg0^1@2$8^1+vhgg0@3$5@1$3@1$1@1$0#8@1?1M@2$9@1$0#k0^2@1$2@1$1@1$0#8").
  (* [comment removed for export] *)
  Hypothesis Mcells : ltac2:(zQ "20!mg5!mh1@2$0?1M$1").
  (* [comment removed for export] *)
  Hypothesis Mtid : ltac2:(zQ "a0!h9!l9!hg4!jc!hh7!hge!q9!ml6!hl9!u4@3$6@1$5@1$1@1$3@1$0#8@4$8$9?1M@2$2@1$0#k0+hgrmh0N4@2$4@1$1@1$3@1$0#8@2$7N4@2$2@1$0#k0?3tid").
  Hypothesis Htid : ltac2:(zQ "30!ls4!lrb!mmb@2$1@2$0Z?3tid@2$0?3tid@2$2+2+h6").
  (* [comment removed for export] *)
  Hypothesis Mcan : ltac2:(zQ "10!mn1@2$0?1M?3can").
  (* [comment removed for export] *)
  Hypothesis Hpp1 : ltac2:(zQ "30!h9!o7!v6@2$2@2$1@1$0#k0?3sp0@2$1@1$0#k0?2pp").

  Definition valsOF : ltac2:(zQ "30!l9!h9!jc@1$0@1$2@1$1#k0") := ltac2:(zQ "70!h9!jc!hv7!hg4!hv1!ig4!krd@3$4@1$1@1$0#k0@3$2@1$1@1$0#k0?3sp0@3$2@1$1@1$0#k0@2$3@1$0#k0?3can@3$2@1$1@1$0#k0?2pp@3$2@1$1@1$0#k0?2pp@3$2@1$1@1$0#k0?2pp@3$2@1$1@1$0#k0@2$3@1$0#k0?3tid@1$5@1$1@1$0#k0@3$4@1$1@1$0#k0@1$6?1R@3$2@1$1@1$0#k0@2$3@1$0#k0Z@1$5@1$1@1$0#k0").
  Let E : env := ENV BL valsOF.

  Lemma valsOF_len : ltac2:(zQ "60!m0!hve!q9!h9!lh5!jc@3$2$1@2$0@1$5@1$3#k0$4Ni7").
  Proof. unfold valsOF. rewrite !length_app, junk_vals_length. reflexivity. Qed.

  Lemma evOF_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold E, ENV. cbn [ev]. unfold valsOF.
    change (6 + i)%nat with (length [sp0; Z_to_bv 64 can; pp; pp; pp; Z_to_bv 64 tid] + i)%nat.
    unfold vals_ev. rewrite app_nth2_plus, app_nth1 by (rewrite junk_vals_length; exact Hi).
    unfold junk_vals. rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.

  Lemma spxOF_val : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
  Proof. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev E 0) with sp0.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

  Ltac reg_caseOF :=
    cbn [nth srB0 allregs32];
    first [ rewrite spxOF_val
          | lazymatch goal with |- _ = edenot _ (EVar ?n) =>
              change (edenot E (EVar n)) with (ev E n);
              first [ rewrite (evOF_junk (n - 6)) by lia; reflexivity | idtac ]
            | |- _ => cbn [edenot] end ];
    first [ reflexivity
          | exact Rtp | exact Rs2
          | rewrite Rsp, alu_add; change (ev E 0) with sp0; unfold v_add; apply bv_eq;
            rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, Zplus_mod_idemp_r; f_equal; lia
          | idtac ].

  Lemma regs_okOF : regs_ok E srB0 R.
  Proof.
    pose proof SPlo. pose proof SPhi.
    apply regs_ok_by_idx.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_caseOF.
  Qed.

  Lemma know_okOF : (bv_unsigned pp + 8 <= bv_unsigned sp0 + 4194304)%Z -> know_ok RSEGS E M knB0.
  Proof.
    intros Hpp2. pose proof SPlo. pose proof SPhi. pose proof SPal.
    unfold knB0. apply know_ok_app; [|apply know_ok_app; [apply diag_cells_know; exact Mcells|]].
    - repeat (apply Forall_cons); [ .. | apply Forall_nil ].
      + apply kalign_intro; [lia|]. change (edenot E (EVar 0)) with sp0. exact SPal.
      + apply krange_intro. change (edenot E (EVar 0)) with sp0. lia.
      + (* [comment removed for export] *) cbn [kentry_ok]. split; [apply flat_intro; cbn; unfold OF_STK; lia|].
        intros d m Hd Hm. unfold estart. cbn [a_base a_off]. change (edenot E (EVar 0)) with sp0.
        pose proof (Mstack (Z_to_bv 64 (bv_unsigned sp0 + (-128 - OF_STK) + d)) m) as Hs.
        rewrite !u_small in Hs by (unfold OF_STK in *; lia). apply Hs; unfold OF_STK in *; lia.
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
  Theorem ref_cannot_open : ltac2:(zQ "hc0!h9!jc!l9!o1!m0!u4!vb!hg4!o7!v6!hh7!hge!q9!hl9!hv1!hv7!ig4!iga!ii2!il5!ioc!is3!isb!jm3!jqf!jv2!kg5!knc>4path@1$2@1$1@1$0#8>2t8@1$2@1$1@1$0#8>0@1$h1@3$hb@1$1@1$0#8@2$7@1$0#8Z^2>0@2$9@1$6@2$4@1$1@1$0#8^3+hvvvf>0@2$9@2$3@2$3@2$8@1$0#k0?2pp@1$6@2$4@1$1@1$0#8^4+8@2$3@2$8@1$0#k0?3sp0+kgggg0>0@2$9@2$3@2$3@2$8@1$0#k0?2pp@1$6@2$4@1$1@1$0#8^5+8+ogggggggggg0>0@3$c@1$b@1$2@1$1@1$0#8@4$d$5?1M?2pp@2$h2@2$4@1$1@1$0#8^6N1@2$a@1$2@1$1@1$0#8@3$e@1$1@1$0#8^6@3$f@1$1@1$0#8@2$7@1$0#8Z@1$h0@1$1@1$0#8>0@3$c@1$b@1$2@1$1@1$0#8@4$d$5?1M@2$7@1$0#k0@2$3@2$8@1$0#k0?2pp@1$6@2$4@1$1@1$0#8^7N8@2$a@1$2@1$1@1$0#8^6@4$h8$5$h7@2$h3@5$h5?2fx?1R@2$7@1$0#k0+knmm0?1M@1$h6$5?5model@2$ha@1$h9^8@1$h4?5model").
  Proof.
    intros path t8 Hnonul HPl Hpp2 Hpp3 Hstr Ht8.
    eapply (of_tail_cs path pp t8 valsOF R M); try eassumption.
    - apply valsOF_len.
    - reflexivity.
    - reflexivity.
    - apply regs_okOF.
    - apply know_okOF. lia.
  Qed.
End OpenFailCS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
