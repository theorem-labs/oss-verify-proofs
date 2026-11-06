(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec CatSim SeqExec StoreOk AsanPopFree.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z04Npos35stdpp9bitvectorbdefinitionsi22bv37Corelib4Init9Datatypesk44Somek46option37Corelib4Init5Logicmc2eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticso5afetch_word69OSSVerify6Proofsaboost_jsonafuzz_parse3libbAsanPopFree~~~~~~s93PW069OSSVerify6Proofsaboost_jsonafuzz_parse3libbBothPopFree~~~~~~hgdh1asan_popfree_head69OSSVerifyaboost_jsonafuzz_parse6images9AsanUbsan1M~~~~~~hm1floaded_segmentsi27Z_to_bvs93PW146Stdlib6ZArith6BinInt1Zhre3adds93PW2s93PW3s93PW4s93PW5s93PW6s93PW7s9cpopfree_spec" s.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

#[local] Notation ASEGS := AsanUbsan.M.loaded_segments (only parsing).

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition asan_popfree_head : Z := 0x6e498.
End FPX1.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma PF0 : ltac2:(zQ "a0!hc!jf!lc!m3!o0!rc!hg7!hkb!hpb!hqe@3$4@1$3@1$1@1$0#i0@2$5$8@2$9@1$0#k0$7@2$2@1$1@1$0#i0$6"). Proof. vm_refl. Qed.
Lemma PF1 : ltac2:(zQ "b0!hc!jf!lc!m3!o0!rc!hr8!hkb!hpb!ht6!hqe@3$4@1$3@1$1@1$0#i0@2$5$8@2$a@1$0#k0@2$9$7+4@2$2@1$1@1$0#i0$6"). Proof. vm_refl. Qed.
Lemma PF2 : ltac2:(zQ "b0!hc!jf!lc!m3!o0!rc!htd!hkb!hpb!ht6!hqe@3$4@1$3@1$1@1$0#i0@2$5$8@2$a@1$0#k0@2$9$7+8@2$2@1$1@1$0#i0$6"). Proof. vm_refl. Qed.
Lemma PF3 : ltac2:(zQ "b0!hc!jf!lc!m3!o0!rc!hu3!hkb!hpb!ht6!hqe@3$4@1$3@1$1@1$0#i0@2$5$8@2$a@1$0#k0@2$9$7+c@2$2@1$1@1$0#i0$6"). Proof. vm_refl. Qed.
Lemma PF4 : ltac2:(zQ "b0!hc!jf!lc!m3!o0!rc!hu9!hkb!hpb!ht6!hqe@3$4@1$3@1$1@1$0#i0@2$5$8@2$a@1$0#k0@2$9$7+h0@2$2@1$1@1$0#i0$6"). Proof. vm_refl. Qed.
Lemma PF5 : ltac2:(zQ "b0!hc!jf!lc!m3!o0!rc!huf!hkb!hpb!ht6!hqe@3$4@1$3@1$1@1$0#i0@2$5$8@2$a@1$0#k0@2$9$7+h4@2$2@1$1@1$0#i0$6"). Proof. vm_refl. Qed.
Lemma PF6 : ltac2:(zQ "b0!hc!jf!lc!m3!o0!rc!hv5!hkb!hpb!ht6!hqe@3$4@1$3@1$1@1$0#i0@2$5$8@2$a@1$0#k0@2$9$7+h8@2$2@1$1@1$0#i0$6"). Proof. vm_refl. Qed.
Lemma PF7 : ltac2:(zQ "b0!hc!jf!lc!m3!o0!rc!hvb!hkb!hpb!ht6!hqe@3$4@1$3@1$1@1$0#i0@2$5$8@2$a@1$0#k0@2$9$7+hc@2$2@1$1@1$0#i0$6"). Proof. vm_refl. Qed.

Theorem asan_popfree_spec : ltac2:(zQ "30!ig1!hkb!hpb@3$0?2fx$2$1").
Proof.
  apply popfree_spec_of_code; [unfold asan_popfree_head; lia | exact PF0 | exact PF1 | exact PF2 | exact PF3 | exact PF4 | exact PF5 | exact PF6 | exact PF7].
Qed.

(* [comment removed for export] *)
End FPX2.
(* [comment removed for export] *)
