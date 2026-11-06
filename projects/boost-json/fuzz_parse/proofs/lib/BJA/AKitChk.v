(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Bytes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsWalk N8Kit.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4prodhc4bool46Stdlib6ZArith6BinInt1Zk23eqbhc4andbhc4listhc4true37Corelib4Init5Logicn52eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJA7AKitChk~~~~~~oeatriple_eqb36Stdlib5Lists4Listt92Int97existsb" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac deadbr0 := let K := fresh "K" in if_cases K; [exfalso; revert K; vm_compute; discriminate|]; clear K.
Ltac livebr1 := let K := fresh "K" in if_cases K; [clear K| exfalso; revert K; vm_compute; first [discriminate | congruence]].
Ltac win_side := cbn; first [right; aapp_unfold; lia | left; aapp_unfold; lia | aapp_unfold; lia].
Ltac hiw_tac := unfold wins_hi; repeat (apply Forall_cons; [win_side|]); apply Forall_nil.

Ltac chk_rd RD := st1; clear RD; st1; deadbr0.

(* [comment removed for export] *)
Ltac fold_div8 :=
  repeat match goal with |- context [(?n / 8)] => let v := eval vm_compute in (n / 8) in change (n / 8) with v end.

Ltac chk_obj PAD MU WM HW a w :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    let RD := fresh "RD" in
    pose proof (addressable_rd mc _ _ a w (AsWalk.addressable_transport_hi _ _ _ _ _ PAD MU WM ltac:(aapp_unfold; lia) HW)
                  ltac:(lia) ltac:(lia) ltac:(fold_div8; lia)) as RD;
    chk_rd RD
  end.


(* [comment removed for export] *)
Definition triple_eqb : ltac2:(zQ "30!h9!j4!jb>1x@2$1@2$1$0$0$0>1y@2$1@2$1$0$0$0$2") := ltac2:(zQ "50!h9!j4!jb!la!m0\1x@2$1@2$1$0$0$0\1y@2$1@2$1$0$0$0M1\1x@2$1@2$1$0$0$0$2^2\1p@2$1$0$0\1c$0M1\1p@2$1$0$0$2^2\1a$0\1b$0M1\1y@2$1@2$1$0$0$0$2^5\2p0@2$1$0$0\1f$0M1\2p0@2$1$0$0$2^2\1d$0\1e$0@2$4@2$4@2$3^6^2@2$3^5^1@2$3^7^3").
Lemma in_triple_b : ltac2:(zQ "90!h9!j4!jb!m7!me!o9!sc!uc!v1>1x@2$1@2$1$0$0$0>1l@1$3@2$1@2$1$0$0$0>0@3$5$2@3$8@2$1@2$1$0$0$0@1$6^2^1$4@3$7@2$1@2$1$0$0$0^3^2").
Proof.
  intros x l E. apply existsb_exists in E. ndestruct E as (y & IN & E).
  destruct x as [[a b] c], y as [[d e] f]. cbn in E.
  apply andb_prop in E. destruct E as [E E3]. apply andb_prop in E. destruct E as [E1 E2].
  apply Z.eqb_eq in E1, E2, E3. subst. exact IN.
Qed.
Ltac in_triple_tac := first [ apply in_triple_b; vm_compute; reflexivity | cbn; tauto ].
Ltac chk_glob AC MU WM ACW beg sz szrz a w :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    let RD := fresh "RD" in
    pose proof (addressable_rd mc _ _ a w (ACONST_global_addressable mc beg sz szrz (ACONST_frame _ _ _ AC MU WM ACW) ltac:(in_triple_tac) ltac:(lia))
                  ltac:(lia) ltac:(lia) ltac:(fold_div8; lia)) as RD;
    chk_rd RD
  end.

(* [comment removed for export] *)
Ltac aconst_win := first [ apply aconst_ok_high; acb; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia
                         | match goal with K : aapp ?A ?n |- _ => eapply (aconst_ok_aapp A n); [exact K| lia| lia] end ].
Ltac aconst_wins := repeat (apply Forall_cons; [aconst_win|]); apply Forall_nil.
