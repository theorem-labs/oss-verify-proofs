(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import CidBits CidBits2 AsIface.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init5Logichc2eq69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~j57rz_sizehc2or46Stdlib6ZArith6BinInt1Zo52le79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsIface~~~~~~q24aclshc3andj5aclass_sizeo53leb37Corelib4Init9Datatypesvf4andbvf4boolvf4true79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7CidBits~~~~~~hicdforall_rangeZq26acsizevf3nilq25blockq2bclass_bytesvf4consvf4listq28blk_sizeo53addo53eqbhc3notq26AK_CLSvf6lengtho53mulo56of_nat" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma rz_size_cases : ltac2:(zQ "40!h9!j0!n6!o0>1n$0@2$3@3$1$0@1$2^1+h0@2$3@3$1$0@1$2^1+i0@2$3@3$1$0@1$2^1+k0@2$3@3$1$0@1$2^1+o0@2$3@3$1$0@1$2^1+hg0@2$3@3$1$0@1$2^1+ig0@2$3@3$1$0@1$2^1+kg0@3$1$0@1$2^1+og0").
Proof.
  intros n. unfold rz_size, rz_log, kMinRedzoneLog, kMaxRedzoneLog.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; vm_compute; lia.
Qed.

Lemma rz_size_big : ltac2:(zQ "40!h9!j0!n6!pd>1n$0>0@2$3+vsg1^1@3$1$0@1$2^2+og0").
Proof.
  intros n Hn. unfold rz_size, rz_log, kMinRedzoneLog, kMaxRedzoneLog.
  repeat match goal with |- context [if ?b then _ else _] => destruct b eqn:? end;
    repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H end; try lia.
  vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma acls_big : ltac2:(zQ "40!h9!j0!tf!pd>1n$0>0@2$3+vsg1^1@3$1$0@1$2^2Z").
Proof.
  intros n Hn. unfold acls, compute_req. cbn [rq_primary rq_needed].
  rewrite (rz_size_big n Hn). unfold kMaxSize, round_up.
  replace (Z.max n 8) with n by lia.
  destruct ((n + 8 - 1) / 8 * 8 + 2048 <=? 65536) eqn:E; [|reflexivity].
  apply Z.leb_le in E. exfalso. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma acls_cases : ltac2:(zQ "60!tf!pd!h9!u6!j0!o0>1n$2>0@2$1+1^1@2$5@3$4$2@1$0^2Z@2$3@2$1+1@1$0^2@2$1@1$0^2+he").
Proof.
  intros n Hn. unfold acls, compute_req. cbn [rq_primary rq_needed].
  set (needed0 := round_up (Z.max n 8) 8 + rz_size n).
  destruct (needed0 <=? kMaxSize) eqn:E; [|left; reflexivity].
  right. apply Z.leb_le in E. unfold kMaxSize in E. apply class_id_le30.
  pose proof (rz_size_cases n). subst needed0. unfold round_up in *. Z.div_mod_to_equations. lia.
Qed.

Lemma acsize_chk : ltac2:(zQ "80!uc!v9!hh7!hhe!hi5!j0!h9!hm9@3$5$3@3$7\1c$6@2$2@2$1+i0@1$0^1@2$1@1$0^1+hggg0+1+he$4").
Proof. vm_compute. reflexivity. Qed.
Lemma acsize_le : ltac2:(zQ "40!pd!u6!hna!h9>1c$3>0@2$1@2$0+1^1@2$0^1+he@2$1@2$0+i0@1$2^2@2$0@1$2^2+hggg0").
Proof.
  intros c Hc. unfold acsize.
  pose proof (forall_rangeZ_spec (fun c => (32 <=? class_size c) && (class_size c <=? 65536)) 1 30 c acsize_chk ltac:(lia) ltac:(lia)) as C.
  cbn beta in C. apply andb_prop in C. destruct C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2. lia.
Qed.

Lemma class_bytes_nil : ltac2:(zQ "50!h9!ho3!j0!ho9!hp1>1c$0@3$2$0@2$4@1$1$3^1Z").
Proof. reflexivity. Qed.

Lemma class_bytes_cons : ltac2:(zQ "c0!h9!ho9!hhe!hp1!hpf!hq6!j0!tf!hna!hqd!hr8!hre>1b$1>2LB@1$5$1>1c$0@3$6$0@2$3@3$4$1^3^2^1@2$aM2\0$2$0@2$b@1$7@1$9^3^1@1$8^1Z@2$3^2^1").
Proof. reflexivity. Qed.

(* [comment removed for export] *)

Lemma class_bytes_nonneg : ltac2:(zQ "60!pd!hq6!u6!h9!ho9!hp1>2LB@1$1$4>1c$3>0@2$2@2$0+1^1@2$0^1+he@2$0Z@2$5^3^2").
Proof.
  intros LB c Hc. induction LB as [|b LB IH]; [rewrite class_bytes_nil; lia|].
  rewrite class_bytes_cons. pose proof (acsize_le c Hc). destruct (acls (blk_size b) =? c); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cls_conj_sec : ltac2:(zQ "b0!tf!h9!pd!hq6!j0!hs4!hsa!hna!ho9!hp1!hr8>2LB@1$3$8>1n$1>0@2$2+vsg1^1>0@1$5@3$4$1@1$0^2Z@2$2@2$a@2$9^4@1$0^3@1$7@1$0^3$6").
Proof. intros LB n Hn Hc. exfalso. apply Hc, acls_big, Hn. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma class_bytes_le_len : ltac2:(zQ "a0!pd!ho9!ht3!hq6!u6!h9!hna!hp1!htc!hu2>2LB@1$3$1>1c$5>0@2$4@2$0+1^1@2$0^1+he@2$0@2$7^3^2@2$8@1$9@2$2$1^3@1$6^2").
Proof.
  intros LB c Hc. pose proof (acsize_le c Hc) as HS. induction LB as [|b LB IH]; [rewrite class_bytes_nil; cbn; lia|].
  rewrite class_bytes_cons. cbn [length]. rewrite Nat2Z.inj_succ. destruct (acls (blk_size b) =? c); lia.
Qed.
Lemma cls_conj_small_list : ltac2:(zQ "d0!tf!pd!h9!ho9!ht3!hq6!j0!hs4!hsa!hna!hp1!hr8!hu2>2LB@1$5$3>1n$2>0@2$1+1^1>0@2$1@1$c@2$4$3^3+ju8>0@1$7@3$6$2@1$0^3Z@2$1@2$b@2$a^5@1$0^4@1$9@1$0^4$8").
Proof.
  intros LB n Hn HL Hc.
  destruct (acls_cases n Hn) as [Z0|RC]; [exfalso; exact (Hc Z0)|].
  pose proof (class_bytes_le_len LB _ RC). pose proof (acsize_le _ RC). unfold AK_CLS. nia.
Qed.
(* [comment removed for export] *)
