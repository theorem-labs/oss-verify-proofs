(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr CellsX TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsWalk AsStack0 CXXRep.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4pair79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsConst~~~~~~jb9aconst_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~o46AHI_LO46Stdlib6ZArith6BinInt1Zsb2leo44aappsb3add37Corelib4Init5Logicv53and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsIface~~~~~~hgf7AFS_HDRhgf3fszhc4list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As9AsCXXHeap~~~~~~hm5bfresh_framehgf3asrhgf6fframesb3sub" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section K.
  Context {HCEIL : HeapCeil}.

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma aconst_ok_hi : ltac2:(zQ "50!h9!j4!n8!s2!u3>2lo$0>2hi$0>0@2$4$3^2@1$2@4$1$0$0^3^2").
  Proof.
    intros lo hi L1. apply aconst_ok_high; cbn; [| unfold AHI_LO in *; lia].
    pose proof (sh_below_app AIMG_TOP ltac:(unfold AIMG_TOP, AAPP_HI; lia)). apply (Z.le_trans _ AHI_LO); [| exact L1].
    unfold sh, AIMG_TOP, AHI_LO. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma aconst_ok_aapp : ltac2:(zQ "60!h9!u3!j4!n8!u8!uf>1A$0>1n$0>2lo$0>2hi$0>0@3$4?5HCEIL^4^3>0@2$1^5^3>0@2$1^3@2$5^6^5@1$3@4$2$0$0^5^4").
  Proof.
    intros A n lo hi AP L1 L2. destruct AP as [[P1 P2]|[P1 P2]]; [| apply aconst_ok_hi; lia].
    apply aconst_ok_intro; unfold ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL, ACANPOISON_CELL,
      AF_DCO_CELL, AVERBOSITY_CELL, AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL, sh, AIMG_LO, AIMG_TOP, ALOWSH_LO in *; rewrite ?ASHADOW_BASE_val; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fresh_frame_aapp : ltac2:(zQ "b0!h9!u8!hg9!hkc!hl7!hle!hq4!hr3!hra!uf!hs4>1H$7>2LF@1$5$8>1k$0>2ff$0>2fp$0>0@6$6?5HCEIL^5^4^3^2^1@2$2@3$1?5HCEIL^3@1$4^4@2$2@3$1?5HCEIL^2+1@3$1?5HCEIL@2$a^3$3@2$9$3@1$4^4").
  Proof.
    intros H LF k ff fp FF.
    npose (fresh_frame_facts H LF k ff fp FF) as (K0 & K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13).
    pose proof (fsz_pos k ltac:(lia)) as FP. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE in *.
    split; [| split]; (eapply aapp_sub; [exact K13| lia| lia]).
  Qed.
End K.

(* [comment removed for export] *)
Definition placed : ltac2:(zQ "10!h9>1A$0>1n$0>1PPP") := ltac2:(zQ "10!h9\1A$0\1n$0\1PP^1").

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac side_split :=
  repeat match goal with
  | K : placed ?A _ _ |- ?G =>
      lazymatch G with context [A] =>
        unfold placed in K;
        first [ destruct K as [(? & ? & ? & ?)|(? & ?)] | destruct K as [K|K] ]
      end
  end.
Ltac side_split_all :=
  repeat match goal with
  | K : placed _ _ _ |- _ => unfold placed in K; first [ destruct K as [(? & ? & ? & ?)|(? & ?)] | destruct K as [K|K] ]
  end.
Ltac lia_t1 := zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker.
Ltac lia_t2 := zify_prune; Zify.zify; xlia zchecker.
Ltac lia_t3 := Zify.zify; xlia zchecker.

(* [comment removed for export] *)
Ltac lia_arith :=
  first [ lia_t1
        | progress side_split; lia_t1
        | lia_t2 ].

(* [comment removed for export] *)
Ltac aconst_via_aapp :=
  match goal with
  | K : aapp ?A ?n |- _ => solve [apply (aconst_ok_aapp A n _ _ K); cbn [fst snd]; unfold AFS_SIZE, AFS_HDR, AFS_FLAGS in *; rewrite ?fsz_0, ?fsz_1, ?fsz_2, ?fsz_3, ?fsz_4 in *; lia_arith]
  | K : aapp ?A ?n /\ _ |- _ => solve [apply (aconst_ok_aapp A n _ _ (proj1 K)); cbn [fst snd]; unfold AFS_SIZE, AFS_HDR, AFS_FLAGS in *; rewrite ?fsz_0, ?fsz_1, ?fsz_2, ?fsz_3, ?fsz_4 in *; lia_arith]
  | K : _ /\ aapp ?A ?n |- _ => solve [apply (aconst_ok_aapp A n _ _ (proj2 K)); cbn [fst snd]; unfold AFS_SIZE, AFS_HDR, AFS_FLAGS in *; rewrite ?fsz_0, ?fsz_1, ?fsz_2, ?fsz_3, ?fsz_4 in *; lia_arith]
  end.
(* [comment removed for export] *)
Ltac aconst_win := first [aconst_via_aapp | apply aconst_ok_hi].

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac aapp_win :=
  first [ assumption
        | match goal with
          | K : aapp ?A ?n |- _ => solve [apply (aapp_sub A n _ _ K); unfold AFS_SIZE, AFS_HDR, AFS_FLAGS in *; rewrite ?fsz_0, ?fsz_1, ?fsz_2, ?fsz_3, ?fsz_4 in *; lia_arith]
          | K : aapp ?A ?n /\ _ |- _ => solve [apply (aapp_sub A n _ _ (proj1 K)); unfold AFS_SIZE, AFS_HDR, AFS_FLAGS in *; rewrite ?fsz_0, ?fsz_1, ?fsz_2, ?fsz_3, ?fsz_4 in *; lia_arith]
          | K : _ /\ aapp ?A ?n |- _ => solve [apply (aapp_sub A n _ _ (proj2 K)); unfold AFS_SIZE, AFS_HDR, AFS_FLAGS in *; rewrite ?fsz_0, ?fsz_1, ?fsz_2, ?fsz_3, ?fsz_4 in *; lia_arith]
          | K : ablock_range _ ?A ?n |- _ =>
              solve [apply (aapp_sub A n _ _ (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 K))))))); unfold AFS_SIZE, AFS_HDR, AFS_FLAGS in *; rewrite ?fsz_0, ?fsz_1, ?fsz_2, ?fsz_3, ?fsz_4 in *; lia_arith]
          | K : rblock_range ?A ?n |- _ =>
              solve [apply (aapp_sub A n _ _ (proj1 (proj2 (proj2 (proj2 K))))); unfold AFS_SIZE, AFS_HDR, AFS_FLAGS in *; rewrite ?fsz_0, ?fsz_1, ?fsz_2, ?fsz_3, ?fsz_4 in *; lia_arith]
          end ].

Ltac lia ::=
  unfold AFS_SIZE, AFS_HDR, AFS_FLAGS in *;
  first [ lazymatch goal with
          | |- aapp _ _ => aapp_win
          | |- _ /\ _ => split; lia
          end
        | lia_t1
        | progress side_split; lia_t1
        | lia_t2
        | lia_t3
        | progress side_split; first [lia_t2 | lia_t3]
        | progress side_split_all; lia_t1 ].
(* [comment removed for export] *)
