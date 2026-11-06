(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State StackLayout Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import PlacementSearch.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init5Logichc2eq69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanCeil~~~~~~j5dalloc_ceilingj5ebottomup_floor3h5LinuxProcessSemanticsfLinuxProcessSem5Statep16VmMaps04Nposp1csp_window_lop1avm_init_sp46Stdlib6ZArith6BinInt1Zua2le35stdpp9bitvectorbdefinitionshg7bbv_unsignedp19alloc_topj5ainit_sp_okhg72bv37Corelib4Init9Datatypeshl24listhl24prod3h5LinuxProcessSemanticsfLinuxProcessSem3Runhna8valid_spp19ProcInputp1ainit_modelp18m_vmmapshl24boolhl24true5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Mm4Mmaphu6h2mmap_off_aligned_bhg77Z_to_bvhu6bmmap_anon_bhu6fmmap_flags_coreua7testbitp1fpage_round_up_Zp19page_sizeua6modulohl24conshl26lengthhl23nathl23nil37Corelib4Init5Peanoiqf2lt37Corelib5Lists7ListDefis96firstnis93nthis95skipn" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition alloc_ceiling : Z := 0x7fff7f800000.
Lemma alloc_ceiling_val : ltac2:(zQ "30!j0!h9!n0@3$0$1$2+nvvvnvogggg0").
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition bottomup_floor : Z := 0x2aaaaaaab000.
Lemma bottomup_floor_val : ltac2:(zQ "30!j0!h9!o0@3$0$1$2+iqqqqqqqrgg0").
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition init_sp_ok : ltac2:(zQ "10!rf>1h$0P") := ltac2:(zQ "60!s8!rf!se!td!hg2!hi4\1h$1@2$4$2@2$5@1$0#k0@1$3^1").

Lemma alloc_ceiling_le_alloc_top : ltac2:(zQ "50!rf!hj3!n0!hjf!hg2>1h$0>0@1$3^1@2$4$2@1$1^2").
Proof. intros h H. unfold init_sp_ok, sp_window_lo in H. unfold alloc_top, alloc_ceiling, stack_max_size. lia. Qed.

Lemma alloc_top_ge_of_ceiling : ltac2:(zQ "60!hg2!h9!rf!hj3!n0!hjf>1h$2>1z$1>0@1$5^2>0@2$0^2$4@2$0^3@1$3^4").
Proof. intros h z H Hz. pose proof (alloc_ceiling_le_alloc_top h H). lia. Qed.

Lemma init_sp_ok_init_model : ltac2:(zQ "a0!s8!hkc!hma!hn2!h9!hq6!hr2!hre!hsb!hjf>8reserved@1$2@2$3@1$1@1$0#k0@1$1@1$0#k0>4brk0@1$1@1$0#k0>5mbase@1$1@1$0#k0>2sp@1$1@1$0#k0>3lim$4>3inp$6>0@1$5^3@1$9@1$8@6$7^7^6^5^4^3^2").
Proof. (intros reserved brk0 mbase sp lim inp nd_i1; ndestruct nd_i1 as (Hlo & _ & _)). unfold init_sp_ok. cbn. exact Hlo. Qed.

(* [comment removed for export] *)
Lemma init_sp_ok_same : ltac2:(zQ "60!rf!td!hjf!j0!s8!hkc>1h$0>2h'$0>0@3$3@1$5@1$4#k0@1$1^1@1$1^2>0@1$2^3@1$2^3").
Proof. intros h h' E H. unfold init_sp_ok in *. rewrite E. exact H. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mmap_off_aligned_b_0 : ltac2:(zQ "60!ht6!hte!j0!s8!iha!ij1@3$2$0@1$4@2$5@1$3#k0Z$1").
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mmap_anon_b_of_core : ltac2:(zQ "90!j0!ht6!hte!h9!s8!ijc!ikb!ile!hkc>5flags@1$8@1$4#k0>1c$3>0@3$0$3@1$6^2^1>0@3$0$1@2$7^2+5$2@3$0$1@1$5^4$2").
Proof.
  intros flags c Hc Hb. unfold mmap_anon_b. apply negb_true_iff. apply Z.eqb_neq. intro H0.
  unfold mmap_flags_core in Hc.
  pose proof (Z.land_spec (bv_unsigned flags) MAP_ANONYMOUS 5) as HL. rewrite H0, Z.bits_0 in HL.
  pose proof (Z.ldiff_spec (bv_unsigned flags) MAP_NORESERVE 5) as HD. rewrite Hc, Hb in HD.
  change (Z.testbit MAP_ANONYMOUS 5) with true in HL. change (Z.testbit MAP_NORESERVE 5) with false in HD.
  destruct (Z.testbit (bv_unsigned flags) 5); discriminate.
Qed.

(* [comment removed for export] *)
Lemma page_round_up_Z_aligned' : ltac2:(zQ "50!h9!j0!im8!ina!io6>1z$0@3$1$0@2$4@1$2^1$3Z").
Proof. intro z. unfold page_round_up_Z. apply Z_mod_mult. Qed.

(* [comment removed for export] *)
Lemma firstn1_skipn_nth : ltac2:(zQ "c0!s8!hkc!hma!iof!ip7!iq1!iq8!j0!is3!iu0!iua!iv1>1l@1$2@1$1@1$0#8>1i$5>1d@1$1@1$0#8>0@2$8^2@2$4@1$1@1$0#8^3@3$7@1$2@1$1@1$0#8@3$9@1$1@1$0#8N1@3$b@1$1@1$0#8^3^4@3$3@1$1@1$0#8@4$a@1$1@1$0#8^3^4^2@1$6@1$1@1$0#8").
Proof.
  induction l as [|x l IH]; intros i d Hi; cbn in Hi; [lia|].
  destruct i as [|i]; cbn; [reflexivity|]. apply IH. lia.
Qed.
(* [comment removed for export] *)
