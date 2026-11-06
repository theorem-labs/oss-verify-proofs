(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec HeapCeil MainMem SymExec2 SymExec2Sound.
Import SymExec2.SX2. Import SymExec2Sound.SX2S.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Mem Cells CellsX TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsIface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJB Require Import BJRep.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init5Logichc3and46Stdlib6ZArith6BinInt1Zj62lej62lthc2or79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsBjStat~~~~~~ldebj_static_addr04Npos35stdpp9bitvectorbdefinitionsr22bv37Corelib4Init9Datatypest46option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~v55asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~hj88bytes_athj82wat46lengtht44listhc2eqj63addj66of_nathj85wr_at79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~hr18rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hv84cellhv8acells_size" s.   (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition bj_static_addr : ltac2:(zQ "10!h9>1i$0P") := ltac2:(zQ "50!j0!ke!l3!l8!h9\1i$4@2$3@2$0@2$1+hrmro0^1@2$2^1+hrmro8@2$3@2$0@2$1+hqqqn0^1@2$2^1+hqqqp8@2$3@2$0@2$1+muvog0^1@2$2^1+muvog8@2$3@2$0@2$1+muvoi0^1@2$2^1+muvoj0@2$3@2$0@2$1+hrmqs0^1@2$2^1+hrmqt0@2$0@2$1+hqqmm0^1@2$2^1+hqqmm8").

Lemma bj_static_client {HCEIL : HeapCeil} : forall i, bj_static_addr i -> aimg_client i.
Proof. intros i Hi. unfold bj_static_addr, aimg_client in *. lia. Qed.
Lemma bj_static_lo : ltac2:(zQ "50!j0!h9!pb!ke!l3>1i$1>0@1$2^1@2$0@2$3+hqqmm0^2@2$4^2+muvoj0").
Proof. intros i Hi. unfold bj_static_addr in Hi. lia. Qed.

Section Agree.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Lemma bytes_at_agree : ltac2:(zQ "f0!qc!sf!uc!h9!hj0!hn2!hne!ho4!hod!j0!hp4!hp9!ke!l3!hpf>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>2m'>1x@1$1@1$0#k0@1$2@1$1@1$0#8>1a$3>2bs@1$8@1$1@1$0#8>0@4$5$4^4^2^1>0>1i$3>0@2$9@2$c^4^1@2$d^1@2$b^4@1$e@2$7@1$1@1$0#8^3@3$a@1$2@1$1@1$0#8@1^6@1$6^2@1^7@1$6^2@4$5$4^5^4^3").
  Proof.
    (intros m m' a bs nd_i1 Hag; ndestruct nd_i1 as (H0 & H1 & HB)). split; [exact H0|]. split; [exact H1|].
    intros i Hi. unfold mrd. rewrite (Hag (a + Z.of_nat i)) by lia. apply HB. exact Hi.
  Qed.
  Lemma wr_at_agree : ltac2:(zQ "c0!qc!sf!uc!h9!hj0!hne!hq8!j0!hp4!hp9!ke!l3>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>2m'>1x@1$1@1$0#k0@1$2@1$1@1$0#8>1a$3>1n$3>0@4$6$4^4^2^1>0>1i$3>0@2$7@2$a^4^1@2$b^1@2$9^4^3@3$8@1$2@1$1@1$0#8@1^6@1$5^2@1^7@1$5^2@4$6$4^5^4^3").
  Proof.
    (intros m m' a n nd_i2 Hag; ndestruct nd_i2 as (H0 & H1 & HB)). split; [exact H0|]. split; [exact H1|].
    intros i Hi. unfold wview. rewrite (Hag (a + i)) by lia. apply HB. exact Hi.
  Qed.
  Lemma rw_cells_agree : ltac2:(zQ "h00!qc!sf!uc!h9!hj0!hne!huc!hod!j0!hp4!ij4!ijc!hp9!ke!l3!hpf>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>2m'>1x@1$1@1$0#k0@1$2@1$1@1$0#8>1a$3>2cs@1$7$a>0@4$6$4^4^2^1>0>1i$3>0@2$8@2$d^4^1@2$e^1@2$c^4@1$f@1$b^3@3$9@1$2@1$1@1$0#8@1^6@1$5^2@1^7@1$5^2@4$6$4^5^4^3").
  Proof.
    intros m m' a cs [[Hwf HB] HW] Hag. split; [split; [exact Hwf|]|].
    - eapply bytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact Hag.
    - eapply wr_at_agree; [exact HW | exact Hag].
  Qed.
  Lemma bj_agree {HCEIL : HeapCeil} : forall m m', bj_statics m -> (forall i, bj_static_addr i -> m' (wa i) = m (wa i)) -> bj_statics m'.
  Proof.
    intros m m' BS AG. destruct (bj_statics_unfold _ BS) as (B1 & B2 & B3 & (salt & B4) & B5 & B6).
    apply (bj_statics_fold m' salt);
      (eapply rw_cells_agree; [eassumption|]; intros i Hi; apply AG; unfold bj_static_addr; cbn in Hi; lia).
  Qed.
  (* [comment removed for export] *)
End Agree.
(* [comment removed for export] *)
