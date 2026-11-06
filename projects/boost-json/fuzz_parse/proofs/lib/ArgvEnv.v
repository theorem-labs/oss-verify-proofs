(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec SeqExec StepTac.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos46Stdlib6ZArith6BinInt1Zhf2le35stdpp9bitvectorbdefinitionsjcbbv_unsignedjc2bv37Corelib4Init9Datatypesmc4list3h5LinuxProcessSemanticsfLinuxProcessSem6BvBaseob8len_wordmc6length37Corelib4Init5Logicse2eq01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib7ArgvEnv8Scaffold~~~~~~ua5argcNhf6of_nat3h5LinuxProcessSemanticsfLinuxProcessSembStackLayouthjeh1build_stack_byteshf3addhf2lthf3powhf3muljc7Z_to_bvmc6option69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~hr28wrap_memhr23rdnmc3nat3h5LinuxProcessSemanticsfLinuxProcessSem3Runig6h1entry_stack_imagehjecstack_to_memua4wmemmc4Someob8word_le869OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~in1ccat_argv_ptrmc3nilse3and37Corelib4Init5Peanois72lt37Corelib5Lists7ListDefiu13nth37Corelib4Init3Nativf3addivf3mulobbnat_to_wordjc6bv_add3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypejj67Segmentjj68PhdrInfohje9EntryDrawig6avalid_argvig6avalid_envp3h5LinuxProcessSemanticsfLinuxProcessSem5Statejqbcsp_window_lojqbcsp_window_hi" s.

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

Section Scaffold.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.

  (* [comment removed for export] *)
  Variable segs : ltac2:(zQ "20!o4!jmb@1$0$1").

  (* [comment removed for export] *)
  Variable ph : ltac2:(zQ "10!jn6$0").

  Variable sp : word.
  Variable av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.

  (* [comment removed for export] *)
  Variable rnd : ltac2:(zQ "10!jo2$0").

  (* [comment removed for export] *)
  Hypothesis Hva : ltac2:(zQ "10!jof@1$0?2av").
  Hypothesis Hve : ltac2:(zQ "10!jpd@1$0?2ev").
  Hypothesis Hsp_lo : ltac2:(zQ "40!h9!jt9!j7!l9@2$2$1@2$3@1$0#k0?2sp").
  Hypothesis Hsp_hi : ltac2:(zQ "40!h9!ju9!j7!l9@2$2@2$3@1$0#k0?2sp$1").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma sp_lo_num : ltac2:(zQ "30!h9!j7!l9@2$1+nvvvogggggg0@2$2@1$0#k0?2sp").
  Proof. exact Hsp_lo. Qed.

  Lemma sp_hi_num : ltac2:(zQ "30!h9!j7!l9@2$1@2$2@1$0#k0?2sp+ogggggggggg0").
  Proof. exact Hsp_hi. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition argcN : ltac2:(zQ "20!h9!m7@1$1@1$0#k0") := ltac2:(zQ "40!o4!h9!ra!m7@2$2@1$0@1$3@1$1#8?2av").

  Lemma u_argcN : ltac2:(zQ "90!h9!s5!o4!u2!u7!hid!hj5!m7!l9@3$3$4@2$8@1$0#k0$5@1$6@2$1@1$2@1$7@1$0#8?2av").
  Proof.
    pose proof (valid_argv_len av Hva).
    unfold argcN, len_word. apply u_Z2bv; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma bsb_nw : ltac2:(zQ "90!h9!s5!hn2!ho8!hoe!hj5!hp3!m7!l9@2$4@2$3@2$8@1$0#k0?2sp@1$5@2$1@1$7@1$0#8@7$2?2ph?2sp?2av?2ev?3uid?2hw?3rnd@2$6+2+k0").
  Proof.
    pose proof (bsb_bound ph sp av ev uid hw rnd Hva Hve). pose proof sp_hi_num. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition envp_ptr : ltac2:(zQ "20!h9!m7@1$1@1$0#k0") := ltac2:(zQ "90!h9!ho8!s5!o4!hp9!hj5!hpf!m7!l9@2$6@1$0#k0@2$1@2$1@2$1@2$8@1$0#k0?2sp+8@2$4+8@1$5@2$2@1$3@1$7@1$0#8?2av+8").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition wmem : ltac2:(zQ "30!h9!m7!hq9>0@1$1@1$0#k0@1$2@1$1@1$0#8") := ltac2:(zQ "10!hud@7$0?2ph?2sp?2av?2ev?3uid?2hw?3rnd").

  (* [comment removed for export] *)
  Lemma rdn_wmem_stack : ltac2:(zQ "f0!h9!l9!hv9!j7!m7!o4!ig0!hq9!u2!ij2!ik8!il8!ho8!hj5!hp3>1a@1$4@1$0#k0>1n$6>0@2$3@2$1@1$0#k0?2sp@2$1@1$0#k0^2>0@2$3@2$c@2$1@1$0#k0^3@1$d^2@2$e+2+k0@3$8@1$7@1$5@1$4@1$0#8@4$2?4segs$b^4^3@4$2?4segs@2$a?2sp@7$9?2ph?2sp?2av?2ev?3uid?2hw?3rnd^4^3").
  Proof. intros a n Ha Hn. unfold wmem. apply rdn_wrap_stack_above; assumption. Qed.

  (* [comment removed for export] *)
  Lemma read_argc_w : ltac2:(zQ "a0!o4!h9!m7!ilf!hq9!u2!im6!hid!il8!hv9@3$5@1$4@1$0@1$2@1$1#8@4$9?4segs$8?2spN8@2$3@1$0@1$2@1$1#8@1$6$7").
  Proof.
    pose proof sp_hi_num.
    rewrite rdn_wmem_stack by lia.
    apply read_argc. exact bsb_nw.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma argv_ptr_bounds_at : ltac2:(zQ "h01!h9!m7!l9!s5!o4!iqb!ho8!ig0!irb!is1!itb!iv8!j7!hoe!hj5!hp3&@2$2@1$0#k0@4$5?2sp?2av?2ev^2>1k$7>0@2$a^1@2$3@1$4@1$1@1$0#8?2av@2$9@2$c@2$2@1$0#k0?2sp~0@2$d@2$6@2$6~0@1$e@2$3@1$1@1$0#8@4$b@1$4@1$1@1$0#8^2?2av@1$8@1$1@1$0#8+1@2$f+2+k0").
  Proof.
    intros k Hk. apply argv_ptr_bounds; try assumption.
    pose proof sp_hi_num. unfold argv_layout_slack. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma read_argv_ptr_w : ltac2:(zQ "h10!h9!o4!m7!ilf!s5!ig0!hq9!u2!jh1!jh8!itb!jhf!im6!il8!iqb!hv9!jid>1k$5>0@2$a^1@2$4@1$1@1$2@1$0#8?2av@3$7@1$6@1$1@1$2@1$0#8@4$f?4segs$d@3$h0@1$0#k0?2sp@1$b@2$8N8@2$9N8^2N8@2$3@1$1@1$2@1$0#8@1$c@4$e?2sp?2av?2ev^2").
  Proof.
    intros k Hk. pose proof sp_lo_num. pose proof sp_hi_num.
    pose proof (valid_argv_len av Hva) as Hal.
    rewrite rdn_wmem_stack by (rewrite word_add_nat; u_norm; lia).
    apply read_argv_ptr_k; [ exact Hk | exact bsb_nw ].
  Qed.

End Scaffold.
(* [comment removed for export] *)
