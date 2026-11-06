(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StreamExec FileSim ShapeAlg StoreOk.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "3h5LinuxProcessSemanticsfLinuxProcessSem5State05event69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~j56t_emit37Corelib4Init9Datatypesn94listn93appj54TSetj54t_eq37Corelib7Numbers7BinNumsqc4Npos35stdpp9bitvectorbdefinitionssc2bvn96length37Corelib4Init5Logicv72eq3h5LinuxProcessSemanticsfLinuxProcessSem6BvBasehh08len_word46Stdlib6ZArith6BinInt1Zhkb6of_natsc7Z_to_bvn96optionn94Somen94booln93natn94truev72ex3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehq07Segment3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshu08store_okhu05wview0eread_bytes_maphkb2lthkb3powqc1Zv73andhkb2lescbbv_unsigned69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~im76v_addihkb3addsc9bv_signed" s.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma t_emit_app : ltac2:(zQ "60!ie!n0!p1!p8!pe!q5>1a@1$2$0>1b@1$2$0>1T$4@2$5@2$1@3$3$0^3^2^1@2$1^3@2$1^2^1").
Proof.
  intros a b T tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & HT)].
    + apply is_prefix_app_split in Hp as [Hp | (b' & -> & Hp)].
      * left. exact Hp.
      * right. exists b'. split; [reflexivity | left; exact Hp].
    + right. exists (b ++ tr'). split; [rewrite app_assoc; reflexivity|].
      right. exists tr'. auto.
  - intros [Hp | (tr' & -> & [Hp | (tr'' & -> & HT)])].
    + left. apply is_prefix_app_r. exact Hp.
    + left. apply is_prefix_app_mono. exact Hp.
    + right. exists tr''. rewrite app_assoc. auto.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma len_word_of_nat : ltac2:(zQ "80!s5!u9!ue!p1!hgb!hjf!hm3!hmd>2bs@1$3@1$1@1$0#8@3$4@1$1@1$0#k0@2$5@1$1@1$0#8^1@2$7@1$0#k0@1$6@2$2@1$1@1$0#8^1").
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma read_bytes_map_of_store_ok : ltac2:(zQ "h20!s5!u9!p1!hn7!hgb!hm3!ho0!ho7!hoe!hp4!hpb!ht5!ih7!ii3!iic!ijc!ik2!hmd>4segs@1$2$b>3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8>1a@1$1@1$0#k0>1n$8>0@3$4$7@4$c^4^3^2^1$9>0@2$f@1$5^2@2$h0+2+k0@2$a@1$2@1$1@1$0#8\1w@1$2@1$1@1$0#8@3$4@1$3@1$2@1$1@1$0#8@3$e@2$d^7^6^5@2$h1@1$0#k0@1$5^4@2$6@1$2@1$1@1$0#8^1").
Proof.
  intros segs mem a n H Hn. rewrite read_bytes_map_eq. unfold word_to_nat.
  rewrite Z_to_bv_small by (unfold bv_modulus; lia). rewrite Nat2Z.id.
  apply store_ok_read_aux. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u64_lit : ltac2:(zQ "90!s5!ik9!ikd!hgb!il3!ijc!ik2!hmd!il9>1z$1>0@2$2@2$4Z^1@2$5^1@2$6+2+k0@3$3$1@2$8@1$0#k0@2$7@1$0#k0^2^2").
Proof. intros z Hz. apply Z_to_bv_small. unfold bv_modulus. lia. Qed.

(* [comment removed for export] *)

Lemma v_addi_lit : ltac2:(zQ "b0!s5!ik9!hmd!ikd!hgb!iq2!iqc!il3!ijc!ik2!u9>1a$1>1i$1>0@2$3@2$7Z^2@2$8^2@2$9+2+k0@3$4@1$a@1$0#k0@2$5@2$2@1$0#k0^3^2@2$2@1$0#k0@2$6^3^2").
Proof. intros a i Ha. unfold v_addi. rewrite u64_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma bv_signed_small : ltac2:(zQ "90!s5!ik9!ikd!hgb!il3!ijc!ik2!hmd!ir3>1z$1>0@2$2@2$4Z^1@2$5^1@2$6+2+jf@3$3$1@2$8@1$0#k0@2$7@1$0#k0^2^2").
Proof.
  intros z Hz. rewrite Z_to_bv_signed. unfold bv_swrap.
  unfold bv_wrap, bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z by reflexivity.
  replace (2 ^ 64 `div` 2)%Z with (2 ^ 63)%Z by reflexivity.
  rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
End FPX1.

(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
End FPX2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX3. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.

(* [comment removed for export] *)
End FPX3.

(* [comment removed for export] *)
(* [comment removed for export] *)
