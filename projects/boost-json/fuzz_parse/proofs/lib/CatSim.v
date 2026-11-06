(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SimInv ExitSim.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14listk13natk16option37Corelib4Init5Logicmf2eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticso8dmachine_stateo8cms_read_byteo8h1ms_read_bytes_aux3h5LinuxProcessSemanticsfLinuxProcessSem5Statev3eread_bytes_auxo8dms_read_bytesv3eread_bytes_mapk13nilk14prodo88set_gpr03h5LinuxProcessSemanticsfLinuxProcessSem3Runhmbcapply_effectv37MemCopyv39mkEffectUv3cwith_copyinsv35Modelv37FdEntryhf7Z_to_bvk14Somev39FdChannelv39fd_lookupv35m_fdsk16length4h5LinuxProcessSemanticsfLinuxProcessSem3Sys7Uaccessih8crw_bytes_max46Stdlib6ZArith6BinInt1Zilc2leilc6of_nat37Corelib5Lists7ListDefio46Forall69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6CatSim~~~~~~iq5bbuf_modeled79OSSVerify6Proofsaboost_jsonafuzz_parse3lib6CatSim8WithSegs~~~~~~iud6msteps3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypejj97Segment" s.

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma read_aux_read_byte : ltac2:(zQ "a0!h9!jc!l9!m0!m6!o3!rf!sf!te!hi1>2ms$6>1k$3>1a@1$1@1$0#k0@3$5@1$4@1$2@1$1@1$0#8@3$9@1$7^3^1^2@3$8^3^1^2").
Proof.
  intros ms. induction k as [|k IH]; intro a; [reflexivity|].
  cbn [read_bytes_aux ms_read_bytes_aux].
  destruct (ms_read_byte ms a) as [b|]; [rewrite IH|]; reflexivity.
Qed.

Lemma read_bytes_map_read_byte : ltac2:(zQ "90!h9!jc!l9!m6!o3!rf!sf!hj2!hk2>2ms$5>1a@1$1@1$0#k0>3len@1$1@1$0#k0@3$4@1$3@1$2@1$1@1$0#8@3$8@1$6^3^2^1@3$7^3^2^1").
Proof. intros. rewrite read_bytes_map_eq. unfold ms_read_bytes.
  apply read_aux_read_byte. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma apply_effect_no_write : ltac2:(zQ "c2!h9!jc!hl3!hl9!rf!l9!m0!o3!hm0!hp7!hq7!hr1&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>2ms$4>1r@1$1@1$0#k0@3$7$4@2$9^2@6$b^1@1$2@2$3@1$1@1$0#k0@1$5@1$1@1$0#8~1~1@1$2$a@1$2@2$3@1$1@1$0#k0$6@2$8^2^1").
Proof.
  intros ms r. unfold apply_effect, set_gpr0.
  cbn [eff_ret eff_writes eff_zeros apply_zeros apply_writes].
  reflexivity.
Qed.

Lemma apply_effect_copyins_no_write : ltac2:(zQ "d2!h9!jc!hl3!hl9!l9!m0!rf!o3!hm0!hp7!hq7!hr1!hrd&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>2ms$6>1r@1$1@1$0#k0>7copyins@1$4@2$3@1$1@1$0#k0$5@3$7$6@2$9^3@2$c^1@6$b^2@1$2@2$3@1$1@1$0#k0@1$4@1$1@1$0#8~1~1@1$2$a@1$2@2$3@1$1@1$0#k0$5@2$8^3^2").
Proof.
  intros ms r copyins. unfold with_copyins, apply_effect, set_gpr0.
  cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies
       apply_unmaps apply_zeros apply_copies apply_writes].
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fd1chan : ltac2:(zQ "10!hsc>5model$0P") := ltac2:(zQ "a0!h9!ht4!hte!hu8!m6!o3!huf!hsc!hvb!ig7\5model$7@3$5@1$4$1@2$8@1$9^1@2$2@1$0#k0+1@2$3$1@1$6@2$2@1$0#k0+1").

(* [comment removed for export] *)
Definition buf_modeled : ltac2:(zQ "30!l9!h9!jc>1b@1$0@1$2@1$1#8P") := ltac2:(zQ "70!h9!jc!igf!l9!ikc!in4!ina\1b@1$3@1$1@1$0#8@2$5@1$6@2$2@1$1@1$0#8^1$4").

Definition bufs_modeled : ltac2:(zQ "30!l9!h9!jc>4bufs@1$0@1$0@1$2@1$1#8P") := ltac2:(zQ "50!l9!h9!jc!ipb!ite\4bufs@1$0@1$0@1$2@1$1#8@3$3@1$0@1$2@1$1#8$4^1").

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma is_prefix_app_mono {A} : forall (l a b : list A),
  is_prefix a b -> is_prefix (l ++ a) (l ++ b).
Proof.
  induction l as [|x l IH]; intros a b H; cbn; [exact H | split; [reflexivity | apply IH; exact H]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive wpick (ch : word) : list (list byte) -> list event -> Prop :=
| wp_nil : wpick ch [] []
| wp_cons : forall buf bufs n tr,
    (1 <= n)%nat -> (n <= length buf)%nat ->
    wpick ch bufs tr ->
    wpick ch (buf :: bufs) (map (WriteEv ch) (firstn n buf) ++ tr).

(* [comment removed for export] *)

Section WithSegs.
Variable segs : ltac2:(zQ "20!l9!jme@1$0$1").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive to_wexit : machine_state -> list (list byte) -> word -> Prop :=
| tw_exit : forall ms x8,
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    to_wexit ms [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
| tw_write : forall ms x8 buf bufs code,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 64%Z ->
    ms_gpr ms 0 = Z_to_bv 64 1 ->
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
    (1 <= length buf)%nat ->
    (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
       to_wexit (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) bufs code) ->
    to_wexit ms (buf :: bufs) code
| tw_step : forall ms ms' bufs code,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_wexit ms' bufs code ->
    to_wexit ms bufs code.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive msteps : machine_state -> machine_state -> Prop :=
| mst_refl : forall ms, msteps ms ms
| mst_step : forall ms ms' ms'',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    msteps ms' ms'' ->
    msteps ms ms''.

Lemma msteps_trans : ltac2:(zQ "20!rf!jif>2ms$0>3ms'$0>4ms''$0>0@2$1^3^2>0@2$1^3^2@2$1^5^3").
Proof.
  intros ms ms' ms'' H; induction H; [auto|].
  intro H2. eapply mst_step; eauto.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)


Section WithSegsCh.
Variable segs : ltac2:(zQ "20!l9!jme@1$0$1").
Variable fd ch : word.

(* [comment removed for export] *)
Inductive to_wexit_ch : machine_state -> list (list byte) -> word -> Prop :=
| twc_exit : forall ms x8,
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    to_wexit_ch ms [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
| twc_write : forall ms x8 buf bufs code,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 64%Z ->
    ms_gpr ms 0 = fd ->
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
    (1 <= length buf)%nat ->
    (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
       to_wexit_ch (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) bufs code) ->
    to_wexit_ch ms (buf :: bufs) code
| twc_step : forall ms ms' bufs code,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_wexit_ch ms' bufs code ->
    to_wexit_ch ms bufs code.

Hypothesis Hfd32 : fd32 fd = fd.


End WithSegsCh.

(* [comment removed for export] *)

(* [comment removed for export] *)
