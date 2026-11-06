(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import PropExec MState Mem.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemantics0dmachine_state37Corelib4Init5Logick62eq37Corelib7Numbers7BinNumslf4Npos35stdpp9bitvectorbdefinitionsnf2bv37Corelib4Init9Datatypesq14Noneq16optionk63and09MachineOk0emachine_result0ems_svc_pending04step89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec8WithSegs~~~~~~hg06mstepsk62exhg03evthg05mstepq14list3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehma7Segment" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : ltac2:(zQ "20!hm3!hpf@1$0$1").

Definition mstep : ltac2:(zQ "10!j7>2ms$0>3ms'$0P") := ltac2:(zQ "b0!j7!la!n8!pc!r9!s0!s9!sf!ta!ua!va\2ms$0\3ms'$0@2$6@3$1@1$5@1$3@1$2#k0@1$9^2@1$4@1$3@1$2#k0@3$1@1$8$0@2$a?4segs^2@2$7$0^1").

Inductive msteps : machine_state -> machine_state -> Prop :=
| msteps_refl : forall ms, msteps ms ms
| msteps_cons : forall ms ms1 ms2, mstep ms ms1 -> msteps ms1 ms2 -> msteps ms ms2.

Lemma msteps_trans : ltac2:(zQ "20!j7!hk4>1a$0>1b$0>1c$0>0@2$1^3^2>0@2$1^3^2@2$1^5^3").
Proof. intros a b c H; induction H; intros; [assumption|]. eapply msteps_cons; eauto. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Definition evt : ltac2:(zQ "10!j7>1Q>0$0P>2ms$0P") := ltac2:(zQ "40!j7!s9!hke!hk4\1Q>0$0P\2ms$0@2$2$0\3ms'$0@2$1@2$3^2^1@1^3^1").

Lemma evt_done : ltac2:(zQ "20!j7!hl3>1Q>0$0P>2ms$0>0@1^2^1@2$1^3^2").
Proof. intros Q ms H. exists ms. split; [apply msteps_refl|exact H]. Qed.

Lemma evt_step : ltac2:(zQ "30!j7!hl3!hla>1Q>0$0P>2ms$0>3ms1$0>0@2$2^2^1>0@2$1^4^2@2$1^5^4").
Proof. intros Q ms ms1 H (ms' & Hs & HQ). exists ms'. split; [eapply msteps_cons; eauto|exact HQ]. Qed.

(* [comment removed for export] *)
Lemma evt_cut : ltac2:(zQ "20!j7!hl3>1P>0$0P>1Q>0$0P>2ms$0>0@2$1^3^1>0>3ms'$0>0@1^5^1@2$1^5^2@2$1^4^3").
Proof.
  intros P Q ms (ms1 & H1 & HP) K. destruct (K ms1 HP) as (ms2 & H2 & HQ).
  exists ms2. split; [eapply msteps_trans; eauto| exact HQ].
Qed.

Lemma evt_mono : ltac2:(zQ "20!j7!hl3>1P>0$0P>1Q>0$0P>2ms$0>0@2$1^3^1>0>3ms'$0>0@1^5^1@1^5^2@2$1^4^3").
Proof. intros P Q ms H K. eapply evt_cut; [exact H|]. intros ms' HP. apply evt_done, K, HP. Qed.

(* [comment removed for export] *)
Lemma evt_eq : ltac2:(zQ "30!j7!hl3!la>1Q>0$0P>2ms$0>3ms'$0>0@3$2$0^2^1>0@2$1^4^2@2$1^5^4").
Proof. intros; subst; assumption. Qed.

End WithSegs.

Arguments mstep segs ms ms' /.
(* [comment removed for export] *)
