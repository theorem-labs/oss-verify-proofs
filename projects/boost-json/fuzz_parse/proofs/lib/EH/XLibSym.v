(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec XCatExec XCatSim XStoreOk XSeqExec XHoare XAxSymExec3 XAxSymExec3B XAxSymExec3Sound XAxSymRun3.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~0aitab_sound37Corelib4Init9Datatypesl14listl13natl14prod37Corelib7Numbers7BinNumsnd1Z04itab99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XLibSym3FPX8WithSegs~~~~~~q0eitab_of_ranges3h5LinuxProcessSemantics5Riscv5Instrvb5instr06PTLeafq07itab_ofnd4Npos37Corelib4Init5Logichk03andhk02eq46Stdlib6ZArith6BinInt1Zhm12lehm12lthm13pow35stdpp9bitvectorbdefinitionshoc7Z_to_bvhocbbv_unsigned3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehs37Segment" s.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section FPX. Context {fx : XPropExec.FPState}.
Section WithSegs.
Variable segs : ltac2:(zQ "20!m9!hv8@1$0$1").

Fixpoint itab_of_ranges (rs : list (Z * nat)) (t : itab) : itab :=
  match rs with
  | [] => t
  | (lo, n) :: rs' => itab_of_ranges rs' (mk_itab_fuel segs n lo t)
  end.
Lemma itab_of_ranges_sound : ltac2:(zQ "70!k5!m9!n0!n6!p6!pa!ua>2rs@1$1@2$3$4$2>1t$5>0@2$0?4segs^1@2$0?4segs@2$6^3^2").
Proof. induction rs as [|[lo n] rs IH]; intros t Ht; cbn; [exact Ht|]. apply IH. apply mk_itab_fuel_sound. exact Ht. Qed.
Lemma itab_leaf_sound : ltac2:(zQ "30!hhf!hi7!k5@2$2?4segs@1$1$0").
Proof. intros pc i. unfold itab_lookup. destruct pc; try discriminate. rewrite pt_get_leaf. discriminate. Qed.
Definition itab_of : ltac2:(zQ "50!m9!n0!n6!p6!pa>2rs@1$0@2$2$3$1$4") := ltac2:(zQ "70!m9!n0!n6!p6!hhf!hi7!ua\2rs@1$0@2$2$3$1@2$6^1@1$5$4").
Lemma itab_of_sound : ltac2:(zQ "60!m9!n0!n6!p6!k5!hif>2rs@1$0@2$2$3$1@2$4?4segs@1$5^1").
Proof. intros rs. apply itab_of_ranges_sound, itab_leaf_sound. Qed.
End WithSegs.

(* [comment removed for export] *)

Lemma u64_of_Z : ltac2:(zQ "90!hj9!p6!hl4!hlb!hn9!hnf!ho5!hq9!hr4>1z$1>0@2$2@2$4Z^1@2$5^1@2$6+2+k0@3$3$1@2$8@1$0#k0@2$7@1$0#k0^2^2").
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Hz. Qed.

(* [comment removed for export] *)

End FPX.
(* [comment removed for export] *)
