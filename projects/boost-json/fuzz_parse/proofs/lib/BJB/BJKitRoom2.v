(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil AsanAllocModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Image CellsX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AsConst CidBits AsIface AsCXXHeap AsClsKit.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJB Require Import BJRep BJKitArith.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJB Require Import BJIface BJIfaceStr BJIfaceEsc BJKitRoom.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJB7BJIface~~~~~~hc5rc_al46Stdlib6ZArith6BinInt1Zm22le79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJB5BJRep~~~~~~nf6vstack37Corelib4Init5Logics43andhc7pv_costhc8pv_spent79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsIface~~~~~~v35as_Cfv35as_Cmm23add79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJBaBJIfaceEsc~~~~~~hk6apesc_spentm23subv33asrv3casan_rt_hyps" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section KIT.
  Context {HCEIL : HeapCeil}.
  Variable H : ltac2:(zQ "10!hpb$0").
  Hypothesis HH : ltac2:(zQ "10!hq1@2$0?5HCEIL?1H").
  Local Ltac costs := pose proof (ah_costs H HH) as (Cm0 & CmM & Cf0 & CfM & CmA & CfA).

  (* [comment removed for export] *)
  Lemma pv_cost_avail0 : ltac2:(zQ "a0!h9!la!na!rb!t8!te!u8!hj0!hj8!hk0>2st$3>1k$0>2lo$0>3AL0$0>2AL$0>3st1$3>2k1$0>0@6$6?1H^7^6^5^4^3>0@2$2@3$5?1H^8^7^5>0@2$4@2$2Z@2$1^4^3@2$2@2$1^4^3^7@2$2@2$9@2$8?1H@2$1^5^4@2$7?1H@2$1^5^4^6").
  Proof. intros st k lo AL0 AL st1 k1 SP C R. eapply pv_spent_avail; [exact HH| exact SP| exact C| lia| lia]. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pv_spent_call0 : ltac2:(zQ "60!h9!u8!rb!la!ho7!na>3st0$2>2k0$0>3lo1$0>3AL0$0>3AL1$0>3st1$2>2k1$0>3lo2$0>3AL2$0>0@6$1?1H^9^8^7^6^5>0@2$5@2$3^5^4^8>0@6$4?1H^6^5^4^7^3@6$1?1H^c^b^5^9^4").
  Proof.
    (intros st0 k0 lo1 AL0 AL1 st1 k1 lo2 AL2 nd_i7 L nd_i8; ndestruct nd_i7 as (q1 & A1 & A2 & A3); ndestruct nd_i8 as (q2 & B1 & B2 & B3)). costs.
    exists q2. split; [lia|]. split; [lia|].
    pose proof (CmA (rc_al st0 k0 + 256 - q1) (rc_al st1 k1 - q2) ltac:(lia) ltac:(lia)) as SA.
    pose proof (CfA (rc_al st0 k0 + 256 - q1) (rc_al st1 k1 - q2) ltac:(lia) ltac:(lia)) as SB.
    pose proof (CmM (rc_al st0 k0 + 256 - q1 + (rc_al st1 k1 - q2)) (rc_al st0 k0 + 256 - q2) ltac:(lia)) as MA.
    pose proof (CfM (rc_al st0 k0 + 256 - q1 + (rc_al st1 k1 - q2)) (rc_al st0 k0 + 256 - q2) ltac:(lia)) as MB.
    lia.
  Qed.
  (* [comment removed for export] *)
  Lemma pv_spent_callb : ltac2:(zQ "80!h9!u8!la!rb!ho7!hk0!na!hp5>3st0$3>2k0$0>3lo1$0>3AL0$0>3AL1$0>3st1$3>2k1$0>3lo2$0>3AL2$0>0@6$1?1H^9^8^7^6^5>0@2$6@2$2^5^4^8>0@6$4?1H^6^5^4^7^3@6$1?1H^c^b@2$5^5@2$7^a@2$2^7^6^9^4").
  Proof.
    (intros st0 k0 lo1 AL0 AL1 st1 k1 lo2 AL2 nd_i9 L nd_i10; ndestruct nd_i9 as (q1 & A1 & A2 & A3); ndestruct nd_i10 as (q2 & B1 & B2 & B3)). costs.
    exists (q2 + (q1 - rc_al st1 k1)). split; [lia|]. split; [lia|].
    pose proof (CmA (rc_al st0 k0 + 256 - q1) (rc_al st1 k1 - q2) ltac:(lia) ltac:(lia)) as SA.
    pose proof (CfA (rc_al st0 k0 + 256 - q1) (rc_al st1 k1 - q2) ltac:(lia) ltac:(lia)) as SB.
    replace (rc_al st0 k0 + 256 - q1 + (rc_al st1 k1 - q2)) with (rc_al st0 k0 + 256 - (q2 + (q1 - rc_al st1 k1))) in SA, SB by lia.
    lia.
  Qed.
End KIT.
(* [comment removed for export] *)
