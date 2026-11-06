(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require As0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr Bytes SysStep Exec CellsX TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep CXXLib CXXLib2.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsIface~~~~~~hc3mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsShadow~~~~~~lfaaccessible37Corelib4Init9Datatypesqa4list37Corelib4Init5Logics93andhccaclient_addrhc5apreshc5blocklf2sh46Stdlib6ZArith6BinInt1Zhg73addhg72lehg72ltqa4prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs6CXXRep~~~~~~hj97xclienthj95xpres04Nposlf4SHAD35stdpp9bitvectorbdefinitionshp62bvqa6lengthhj9dxclient_rangehg76of_natlfbaddressablelf3nshhc6fframes92exhc8blk_addrhc7ff_addr36Stdlib5Lists4Listih42Ins92orhc8blk_sizehc8ff_classhc3fszhc4bptrqa4pair89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5AsObj1K~~~~~~ilc4aobjhc6as_RFShc8as_RHEAPhc5as_Stlf4aapp79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~is48AIMG_TOPlf5aceilhcdaclient_range79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsConst~~~~~~ji39aconst_oklf6AHI_LOhch0aclient_write_okhccafs_write_oklf5shvishc3asrhccasan_rt_hyps" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac zs_wrap e ::= rewrite (unsigned_lit_wrap e).
Ltac zs_wrap_in e H ::= rewrite (unsigned_lit_wrap e) in H.
Ltac zs_idioms ::=
  match goal with
  | |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] =>
      rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])
  end.
Ltac zs_idioms_in H ::=
  match type of H with
  | context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] =>
      rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Section K.
  Context {HCEIL : HeapCeil}.
  Variable H : ltac2:(zQ "10!jq1$0").
  Hypothesis HH : ltac2:(zQ "10!jq7@2$0?5HCEIL?1H").

  (* [comment removed for export] *)
  Lemma apres_accessible : ltac2:(zQ "c0!h9!l9!pd!s2!td!u3!v2!va!hg2!hhf!hi6!hic>2LB@1$3$7>2SP$0>1m$1>2m'$1>1a$0>1n$0>0@6$6?5HCEIL?1H^6^5^4^3>0@3$2^5^3^2>0>1x$0>0@2$4@2$a^5^1@2$b^1@2$9^5^4@5$5?5HCEIL?1H^a^9@1$8^2@3$2^6^5^4").
  Proof.
    (intros LB SP m m' a n AP nd_i1 CL; ndestruct nd_i1 as (A0 & A1 & AC)). split; [exact A0|]. split; [exact A1|].
    intros x Hx. ndestruct (AC x Hx) as (v & V0 & RD & OK). exists v. split; [exact V0|]. split; [| exact OK].
    assert (SR : 0 <= sh x < 2^64). { unfold sh, AAPP_HI in *. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia. }
    destruct (AP (sh x) SR (CL x Hx)) as [E _]. unfold mrd in *. rewrite E. exact RD.
  Qed.

  (* [comment removed for export] *)
  Lemma xpres_accessible : ltac2:(zQ "d0!h9!s2!l9!pd!hj2!td!va!hg2!hn5!ho0!hhf!hi6!hic>2LB@1$1$6>2SP$0>1X@1$1@2$4$0$0>1m$2>2m'$2>1a$0>1n$0>0@7$9?5HCEIL?1H^7^6^5^4^3>0@3$3^5^3^2>0>1x$0>0@2$5@2$b^5^1@2$c^1@2$a^5^4@6$8?5HCEIL?1H^b^a^9@1$7^2@3$3^6^5^4").
  Proof.
    (intros LB SP X m m' a n XP nd_i2 CL; ndestruct nd_i2 as (A0 & A1 & AC)). split; [exact A0|]. split; [exact A1|].
    intros x Hx. ndestruct (AC x Hx) as (v & V0 & RD & OK). exists v. split; [exact V0|]. split; [| exact OK].
    assert (SR : 0 <= sh x < 2^64). { unfold sh, AAPP_HI in *. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia. }
    destruct (XP (sh x) SR (CL x Hx)) as [E _]. unfold mrd in *. rewrite E. exact RD.
  Qed.

  Lemma xpres_SHAD : ltac2:(zQ "d0!h9!s2!ho9!l9!hof!hr3!hr9!hj2!va!hg2!hs2!ho0!ht3>2LB@1$1$8>2SP$0>1X@1$1@2$7$0$0>1m$3>2m'$3>1A$0>3sbs@1$1@1$5@1$2#8>0@7$b?5HCEIL?1H^7^6^5^4^3>0@3$4^5^3^2>0@7$a?5HCEIL?1H^9^8^7@1$9^4@1$c@2$6@1$5@1$2#8^3@3$4^6^5^4").
  Proof.
    (intros LB SP X m m' A sbs XP nd_i3 XC; ndestruct nd_i3 as (A0 & A8 & [UB UW])). split; [exact A0|]. split; [exact A8|].
    split; [eapply xpres_bytes_at; eauto| eapply xpres_wr_at; eauto].
  Qed.

  Lemma xpres_addressable : ltac2:(zQ "a0!h9!s2!l9!htd!hj2!va!hub!hg2!hs2!ho0>2LB@1$1$5>2SP$0>1X@1$1@2$4$0$0>1m$2>2m'$2>1A$0>1n$0>0@7$9?5HCEIL?1H^7^6^5^4^3>0@3$3^5^3^2>0@7$8?5HCEIL?1H^9^8^7@1$7^4@1$6^3@3$3^6^5^4").
  Proof.
    intros LB SP X m m' A n XP [Hn SH] XC. split; [exact Hn|]. eapply xpres_SHAD; eauto. rewrite shadow_of_length by lia. exact XC.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition aobj : ltac2:(zQ "40!s2!h9!va!hv1>2LB@1$0$2>2LF@1$0$3>1A$1>1n$1P") := ltac2:(zQ "f0!td!va!hv1!hhf!hi6!s2!hva!h9!hvf!iga!ii7!iid!ij2!ijd!ik8\2LB@1$5$1\2LF@1$5$2\1A$7\1n$7@2$b@2$6$1\1b$1@2$0@3$a$1^1^5@2$0@2$4@1$8^1^3@2$4@2$3^3^2@2$3@1$8^1@1$c^1@2$6$2\1f$2@2$0@3$a$2^1^4@2$0@2$4@1$9^1^3@2$4@2$3^3^2@2$3@1$9^1@1$e@1$d^1").

  Lemma aobj_block : ltac2:(zQ "a0!h9!hj2!ike!s2!il5!hhf!hi6!hv1!ip9!ii7>2LB@1$3@2$1@2$1$2$0$0>2LF@1$3$7>1p$2>1A$0>1n$0>1a$0>1k$0>0@3$9@2$1@2$1$2$0$0@4$4@2$1$2$0$0@4$4$2$0^5^4^3^7>0@2$6^5^3>0@2$6@2$5^4^3@2$5^6^5@4$8^a^9^5^4").
  Proof. intros LB LF p A n a k IN H1 H2. left. exists (p, A, n). split; [exact IN| cbn; lia]. Qed.

  Lemma aobj_frame : ltac2:(zQ "b0!hv1!s2!h9!iga!hhf!hi6!va!ijd!ik8!ip9!ii7>2LB@1$1$6>2LF@1$1$0>1f$0>1a$2>1k$2>0@3$a$0^3^4>0@2$5@1$3^4^3>0@2$5@2$4^4^3@2$4@1$3^5@1$8@1$7^5@4$9^8^7^5^4").
  Proof. intros LB LF f a k IN H1 H2. right. exists f. auto. Qed.

  Lemma aobj_sub : ltac2:(zQ "70!h9!s2!ip9!hhf!hi6!va!hv1>2LB@1$1$5>2LF@1$1$6>1A$0>1n$0>2A'$0>2n'$0>0@4$2^6^5^4^3>0@2$4^5^3>0@2$4@2$3^4^3@2$3^6^5@4$2^9^8^5^4").
  Proof.
    intros LB LF A n A' n' [(b & Hb & H1 & H2)|(f & Hf & H1 & H2)] L1 L2; [left; exists b| right; exists f]; split; [assumption| lia| assumption| lia].
  Qed.

  Lemma aobj_LB_mono : ltac2:(zQ "60!va!s2!h9!ip9!ii7!hv1>2LB@1$1$0>3LB'@1$1$0>2LF@1$1$5>1A$2>1n$2>0@4$3^5^3^2^1>0>1b$0>0@3$4$0^1^7@3$4$0^2^7@4$3^6^5^4^3").
  Proof.
    intros LB LB' LF A n [(b & Hb & H1 & H2)|K] HL; [left| right; exact K]. exists b. split; [apply HL; exact Hb| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma aobj_aapp : ltac2:(zQ "a0!s2!h9!l9!iq1!iqa!ir5!va!hv1!ip9!ird>1s@1$5?1H>2LB@1$0$6>1m$2>2LF@1$0$7>2m1$2>1A$1>1n$1>0@4$4?1H^7^6^5>0@3$3?1H^5^4>0@4$8^8^6^4^3@3$9?5HCEIL^5^4").
  Proof.
    intros s LB m LF m1 A n RH RF [(b & Hb & H1 & H2)|(f & Hf & H1 & H2)].
    - pose proof (ah_blocks H HH _ _ _ b RH Hb) as (_ & _ & _ & _ & _ & _ & R7). eapply aapp_sub; [exact R7| lia| lia].
    - pose proof (proj2 (ah_RFS_range H HH _ _ RF) f Hf) as (K & R1 & R2 & R3 & R4); pose proof (proj1 (ah_RFS_range H HH _ _ RF)) as (F1 & F2 & F3 & F4).
      eapply aapp_sub; [exact F4| unfold AFS_HDR in *; lia| lia].
  Qed.
  (* [comment removed for export] *)
  Lemma aobj_range : ltac2:(zQ "e0!s2!h9!l9!hi6!td!ivf!iq1!iqa!ir5!va!hv1!ip9!jgb!hhf>1s@1$8?1H>2LB@1$0$9>1m$2>2LF@1$0$a>2m1$2>1A$1>1n$1>0@4$7?1H^7^6^5>0@3$6?1H^5^4>0@4$b^8^6^4^3@2$4@2$3$5^5@2$3@2$d^5^4@1$c?5HCEIL").
  Proof.
    intros s LB m LF m1 A n RH RF AO. pose proof (aobj_aapp _ _ _ _ _ _ _ RH RF AO) as AP.
    unfold aapp, aapp_lo, aapp_hi in AP. acb. unfold AIMG_TOP, ALOWSH_LO, AHI_LO in *. lia.
  Qed.

  Lemma aobj_client : ltac2:(zQ "a0!h9!s2!l9!jh3!iq1!iqa!ir5!va!hv1!ip9>1s@1$6?1H>2LB@1$1$7>1m$2>2LF@1$1$8>2m1$2>2SP$0>1A$0>1n$0>0@4$5?1H^8^7^6>0@3$4?1H^6^5>0@4$9^9^7^4^3@6$3?5HCEIL?1H^a^6^5^4").
  Proof.
    intros s LB m LF m1 SP A n RH RF [(b & Hb & H1 & H2)|(f & Hf & H1 & H2)].
    - right; right; left. exists b. auto.
    - pose proof (proj2 (ah_RFS_range H HH _ _ RF) f Hf) as (K & R1 & R2 & R3 & R4); pose proof (proj1 (ah_RFS_range H HH _ _ RF)) as (F1 & F2 & F3).
      right; right; right; right; left. unfold AFS_HDR in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma aobj_shclient : ltac2:(zQ "f0!h9!s2!l9!td!u3!iq1!iqa!ir5!va!hv1!ip9!hg2!hhf!hi6!hic>1s@1$7?1H>2LB@1$1$8>1m$2>2LF@1$1$9>2m1$2>2SP$0>1A$0>1n$0>1x$0>0@4$6?1H^9^8^7>0@3$5?1H^7^6>0@4$a^a^8^5^4>0@2$3@2$d^6^4@2$e^4@2$c^6^5@5$4?5HCEIL?1H^c^8@1$b^5").
  Proof.
    intros s LB m LF m1 SP A n x RH RF AO Hx. destruct AO as [(b & Hb & H1 & H2)|(f & Hf & H1 & H2)].
    - right; right; right; left. exists b. split; [exact Hb|].
      pose proof (ah_blocks H HH _ _ _ b RH Hb) as (_ & R2 & R3 & R4 & R5 & _).
      split; [apply sh_mono; lia|].
      rewrite (sh_rel (blk_addr b) x) by (first [Z.div_mod_to_equations; lia | lia]). unfold nsh. Z.div_mod_to_equations. lia.
    - pose proof (proj2 (ah_RFS_range H HH _ _ RF) f Hf) as (K & R1 & R2 & R3 & R4); pose proof (proj1 (ah_RFS_range H HH _ _ RF)) as (F1 & F2 & F3).
      right; right; right; right; right; left. unfold AFS_HDR in *.
      split; [apply sh_mono; lia|]. unfold AFS_SIZE, sh in *. Z.div_mod_to_equations. lia.
  Qed.

  Lemma aconst_ok_hi : ltac2:(zQ "50!h9!il5!jm0!jmd!hi6>2lo$0>2hi$0>0@2$4$3^2@1$2@4$1$0$0^3^2").
  Proof.
    intros lo hi L1. apply aconst_ok_high; cbn; [| unfold AHI_LO in *; lia].
    pose proof (sh_below_app AIMG_TOP ltac:(unfold AIMG_TOP, AAPP_HI; lia)). apply (Z.le_trans _ AHI_LO); [| exact L1].
    unfold sh, AIMG_TOP, AHI_LO. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma aconst_ok_aapp : ltac2:(zQ "60!h9!hi6!il5!jm0!ird!hhf>1A$0>1n$0>2lo$0>2hi$0>0@3$4?5HCEIL^4^3>0@2$1^5^3>0@2$1^3@2$5^6^5@1$3@4$2$0$0^5^4").
  Proof.
    intros A n lo hi AP L1 L2. destruct AP as [[P1 P2]|[P1 P2]]; [| apply aconst_ok_hi; lia].
    apply aconst_ok_intro; unfold ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL, ACANPOISON_CELL,
      AF_DCO_CELL, AVERBOSITY_CELL, AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL, sh, AIMG_LO, AIMG_TOP, ALOWSH_LO in *; rewrite ?ASHADOW_BASE_val; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma aobj_write_ok : ltac2:(zQ "f0!h9!il5!hhf!s2!td!l9!jm0!jn6!joa!iq1!iqa!ir5!va!hv1!ip9>1s@1$b?1H>2LB@1$3$c>1m$5>2LF@1$3$d>2m1$5>1A$0>1n$0>0@4$a?1H^7^6^5>0@3$9?1H^5^4>0@4$e^8^6^4^3@2$4@4$7?5HCEIL?1H^9@4$1$0$0^5@2$2^5^4@2$4@3$8?1H^7@4$1$0$0^5@2$2^5^4@1$6@4$1$0$0^5@2$2^5^4").
  Proof.
    intros s LB m LF m1 A n RH RF AO. pose proof (aobj_range _ _ _ _ _ _ _ RH RF AO) as [L1 L2].
    assert (AC : aconst_ok (A, A + n)).
    { eapply aconst_ok_aapp; [eapply aobj_aapp; [exact RH| exact RF| exact AO] | lia| lia]. }
    destruct AO as [(b & Hb & H1 & H2)|(f & Hf & H1 & H2)].
    - split; [right; right; left; exists b; auto|]. split; [| exact AC].
      left. cbn. pose proof (ah_blocks H HH _ _ _ b RH Hb) as (_ & _ & _ & R4 & R5 & R6 & _). unfold AFS_SIZE, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP in *. lia.
    - split; [| split; [right; exists f; auto| exact AC]].
      pose proof (proj2 (ah_RFS_range H HH _ _ RF) f Hf) as (K & R1 & R2 & R3 & R4); pose proof (proj1 (ah_RFS_range H HH _ _ RF)) as (F1 & F2 & F3).
      right; right; right; right; left. cbn. unfold AFS_HDR in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma aobj_shvis : ltac2:(zQ "c0!s2!h9!iq1!iqa!ir5!va!hv1!l9!ip9!jp9!hhf!hi6>1s@1$4?1H>2LB@1$0$5>1m$7>2LF@1$0$6>1A$1>1n$1>0@4$3?1H^6^5^4>0@3$2?1H^4^5>0@4$8^7^5^4^3>0@2$bZ^4@3$9^8^6@2$a^6^5").
  Proof.
    intros s LB m LF A n RH RF AO Hn. pose proof (aobj_range _ _ _ _ _ _ _ RH RF AO) as [L1 L2].
    destruct AO as [(b & Hb & H1 & H2)|(f & Hf & H1 & H2)].
    - destruct b as [[p Ab] nb]. cbn in H1, H2. pose proof (ah_blocks H HH _ _ _ _ RH Hb) as (_ & _ & R3 & R4 & R5 & _). cbn in R3, R4, R5.
      eapply shvis_sub; [eapply (ah_blk_shvis H HH); [exact RH| exact Hb] | | | | |]; acb; unfold AIMG_TOP in *; lia.
    - pose proof (proj2 (ah_RFS_range H HH _ _ RF) f Hf) as (K & R1 & R2 & R3 & R4); pose proof (proj1 (ah_RFS_range H HH _ _ RF)) as (F1 & F2 & F3).
      eapply shvis_sub; [eapply (ah_frm_shvis H HH); [exact RF| exact Hf] | | | | |]; acb; unfold AIMG_TOP, AFS_HDR in *; lia.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma stack_window_ok' : ltac2:(zQ "e0!h9!il5!s2!td!jm0!jn6!joa!iqa!ir5!va!hv1!l9!jgb!hi6>1s@1$8?1H>2LB@1$2$9>1m$b>2LF@1$2$a>3lo'$0>2SP$0>0@4$7?1H^6^5^4>0@2$d@1$c?5HCEIL^3@2$3@4$5?5HCEIL?1H^7@4$1$0$0^4^3@2$3@3$6?1H^5@4$1$0$0^4^3@1$4@4$1$0$0^4^3").
  Proof.
    intros s LB m LF lo' SP RH CE. pose proof (ah_fsb H HH _ _ _ RH) as (F1 & F2 & F3).
    apply (stack_window_ok H); [exact CE| exact F2].
  Qed.

  Lemma block_window_ok : ltac2:(zQ "h10!h9!il5!hhf!ike!hj2!s2!td!hi6!jm0!jn6!joa!iqa!ir5!va!hv1!l9!ii7>1s@1$c?1H>2LB@1$5$d>1m$f>2LF@1$5$e>1p$3>1A$0>1n$0>1a$0>1k$0>0@4$b?1H^9^8^7>0@3$h0@2$4@2$4$3$0$0@4$1@2$4$3$0$0@4$1$3$0^6^5^4^9>0@2$7^6^4>0@2$7@2$2^5^4@2$2^7^6@2$6@4$9?5HCEIL?1H^c@4$1$0$0^6@2$2^6^5@2$6@3$a?1H^a@4$1$0$0^6@2$2^6^5@1$8@4$1$0$0^6@2$2^6^5").
  Proof.
    intros s LB m LF p A n a k RH IN H1 H2. pose proof (ah_blocks H HH _ _ _ _ RH IN) as (R1 & R2 & R3 & R4 & R5 & R6). cbn in *.
    split; [right; right; left; exists (p, A, n); cbn; auto|]. split.
    - left. cbn. unfold AFS_SIZE, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP in *. lia.
    - destruct R6 as [R6 R7]. eapply aconst_ok_aapp; [exact R7| lia| lia].
  Qed.
End K.
(* [comment removed for export] *)
