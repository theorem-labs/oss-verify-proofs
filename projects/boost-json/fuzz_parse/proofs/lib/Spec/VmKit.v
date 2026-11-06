(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshfbbv_unsigned37Corelib4Init5Logicka3and46Stdlib6ZArith6BinInt1Zm42lem42ltm43powhf2bv01Zka2eqhf7Z_to_bv37Corelib4Init9Datatypesq34prod3h5LinuxProcessSemanticsfLinuxProcessSem5States2alive_bytesq34listq33appm43adds2biv_subtracts2dmaps_subtracts2h1maps_subtract_allq34consq34pairs26VmMapss2fvm_backed_bytess2dvm_live_bytesq33nils25Models29m_vm_lazys2h1m_vm_materializeds28m_vmmapss2fvm_backing_used" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma u64_range : ltac2:(zQ "70!h9!jc!le!nc!o1!o6!oc>1x@1$6@1$0#k0@2$2@2$3Z@2$1@1$0#k0^1@2$4@2$1@1$0#k0^1@2$5+2+k0").
Proof. intros x. pose proof (bv_unsigned_in_range 64 x) as H. unfold bv_modulus in H. exact H. Qed.
Lemma u64_lit : ltac2:(zQ "90!h9!p1!le!p4!nc!o1!o6!p9!jc>1z$1>0@2$2@2$4Z^1@2$5^1@2$6+2+k0@3$3$1@2$8@1$0#k0@2$7@1$0#k0^2^2").
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma live_bytes_app : ltac2:(zQ "92!h9!oc!rb!v0!vd!hg4!p4!p1!hga&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$4~0>2l1~1>2l2~1@3$6$7@1$3@3$5~0^2^1@2$8@1$3^2@1$3^1").
Proof. induction l1 as [|[a n] l1 IH]; intros l2; [reflexivity|]. cbn [live_bytes app]. rewrite IH. lia. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma live_bytes_iv_subtract_le : ltac2:(zQ "70!h9!p1!nc!oc!hh0!v0!jc>1a@1$3@1$0#k0>2sz@1$3@1$0#k0>2lo$1>2hi$1>0@2$2^2^1@2$2@1$5@4$4^5^4^3^2@2$6@1$0#k0^4").
Proof.
  intros a sz lo hi Hlh. pose proof (u64_range a). pose proof (u64_range sz).
  unfold iv_subtract.
  destruct (bv_unsigned a <? lo) eqn:E1; destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E2;
    cbn [app live_bytes];
    first [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1]; first [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2];
    rewrite ?u64_lit by lia; lia.
Qed.

Lemma live_bytes_maps_subtract_le : ltac2:(zQ "80!h9!p1!v0!nc!oc!vd!rb!hhe>1l@1$5@2$6@1$4@1$0#k0@1$4@1$0#k0>2lo$1>2hi$1>0@2$3^2^1@2$3@1$2@3$7^4^3^2@1$2^4").
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hlh; [cbn; lia|].
  cbn [maps_subtract live_bytes]. rewrite live_bytes_app.
  pose proof (live_bytes_iv_subtract_le a sz lo hi Hlh). specialize (IH lo hi Hlh). lia.
Qed.

Lemma maps_subtract_all_cons : ltac2:(zQ "b2!h9!oc!rb!vd!jc!hie!hk3!hka!p4!hhe!hga&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$3~0>4maps~1>1a@1$1@1$0#k0>1n@1$1@1$0#k0>4cuts~1@3$8~1@2$5^4@3$6~0@4$7@1$1@1$0#k0@1$1@1$0#k0^3^2^1@2$5@3$9^4@2$4@1$0#k0^3@2$a@2$4@1$0#k0^3@2$4@1$0#k0^2^1").
Proof. reflexivity. Qed.

Lemma live_bytes_maps_subtract_all_le : ltac2:(zQ "72!h9!oc!vd!rb!v0!hie!nc&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>4cuts~1>4maps~1@2$6@1$4@2$5^1^2@1$4^1").
Proof.
  induction cuts as [|[a n] cuts IH]; intros maps; [cbn; lia|].
  rewrite maps_subtract_all_cons. etransitivity; [apply IH|].
  apply live_bytes_maps_subtract_le. pose proof (u64_range n). lia.
Qed.

(* [comment removed for export] *)
Lemma vm_backed_bytes_le_live : ltac2:(zQ "40!hl1!hla!hmc!nc>1h$0@2$3@1$1^1@1$2^1").
Proof. intros h. unfold vm_backed_bytes, vm_backed_maps, vm_live_bytes. apply live_bytes_maps_subtract_all_le. Qed.

Lemma vm_backing_used_simple : ltac2:(zQ "d1!h9!oc!p4!vd!hnc!rb!p1!ho2!hoa!hp6!hqb!hla!hr6&@2$5@1$1@1$0#k0@1$1@1$0#k0>1m$7>0@3$2@1$3~0@1$8^1@1$4~0>0@3$2@1$3@1$1@1$0#k0@1$9^2@1$4@1$1@1$0#k0@3$2$6@1$c^3@1$b@1$a^3").
Proof.
  intros m Hl Hm. unfold vm_backing_used. rewrite Hl, Hm. cbn [maps_subtract_all length Z.of_nat Z.mul]. unfold vm_backed_bytes. lia.
Qed.

(* [comment removed for export] *)
Lemma vm_backing_used_le_live : ltac2:(zQ "d1!h9!oc!vd!hnc!rb!p4!ho2!hoa!hp6!hqb!hr6!hmc!nc&@2$4@1$1@1$0#k0@1$1@1$0#k0>1m$6>0@3$5@1$2~0@1$7^1@1$3~0>0@3$5@1$2@1$1@1$0#k0@1$8^2@1$3@1$1@1$0#k0@2$c@1$a^3@1$b@1$9^3").
Proof.
  intros m Hl Hm. rewrite (vm_backing_used_simple m Hl Hm). apply vm_backed_bytes_le_live.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
