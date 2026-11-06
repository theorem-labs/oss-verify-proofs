(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc. (* [comment removed for export] *) (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr Bytes SysStep CellsX TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~02b837Corelib4Init5Logicjf2eq37Corelib7Numbers7BinNumsl84Nposl81Z46Stdlib6ZArith6BinInt1Znc6modulo35stdpp9bitvectorbdefinitionspd2bv37Corelib4Init9Datatypesrf4list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~te5asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hi14cellhi1bcells_bytes79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~hn48rw_cellsrf6optionhi18cells_wfrf3nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ht68bytes_atrf6length37Corelib4Init3Natii53add37Corelib4Init5Peanoije2le37Corelib5Lists7ListDefil86firstnil85skipnnc3addnc6of_natrf4prodjf3and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsIface~~~~~~ipe3asripe5block79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As6CXXRep~~~~~~iub7xclientiub5xpres79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~jjb3ivljjb5munchjjb7outsidejjb5wmononc2lenc2ltnc3powipedaclient_range36Stdlib5Lists4Listjrc2Inipecaclient_addrjf2oripe8as_RHEAPipe5as_Stipe3mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~kg65aceilipe4bptrrf4pairrf4consipecasan_rt_hyps" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma b8_mod256 : ltac2:(zQ "60!jb!l3!n1!n8!p4!ra>1z$3@3$1@1$5@1$2#8@1$0@2$4^1+hg0@1$0^1").
Proof. intros z. unfold b8. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod. change (2^8) with 256. rewrite Z.mod_mod by lia. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rw_cells_recut : ltac2:(zQ "b0!t7!n1!ra!hh9!hld!hm5!hqf!hrb!l3!n8!hs4>1m>0@1$2@1$1#k0@1$7@1$2@1$1#8>1A$9>2cs@1$0$4>3cs'@1$0$4>0@4$6$3^4^3^2>0@1$a^2>0@3$8@1$0@1$2@1$1#8@1$5^3@1$5^4@4$6$3^7^6^4").
Proof.
  intros m A cs cs' [[WF B] W] WF' E. split; [split; [exact WF'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' WF'), E, (cells_bytes_length cs WF). exact W.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma bytes_at_sub : ltac2:(zQ "f0!n1!ra!ht0!hh9!ih0!ihc!t7!hrb!ij7!il2!imf!in9!n8!io2!io8>1m>0@1$1@1$0#k0@1$7@1$1@1$0#8>1A$c>2bs@1$6@1$1@1$0#8>1k$2>1j$2>0@4$4$3^5^4^3>0@2$9@2$8^3^2@2$5@1$1@1$0#8^4@4$4$3^7@2$d^6@1$e^4@3$a@1$1@1$0#8^3@3$b@1$1@1$0#8^4^5").
Proof.
  intros m A bs k j B H.
  rewrite <- (firstn_skipn k bs) in B. apply bytes_at_app in B. destruct B as [_ B].
  rewrite firstn_length_le in B by lia.
  rewrite <- (firstn_skipn j (skipn k bs)) in B. apply bytes_at_app in B. destruct B as [B _]. exact B.
Qed.

(* [comment removed for export] *)
Lemma xpres_of_munch_gen : ltac2:(zQ "h31!n1!n8!ra!t7!hrb!ip1!ip8!hh9!itb!iu2!ji7!jj2!jn7!jne!jo7!jp2!jpb!jq0!jq5&>0@1$2@1$0#k0@1$4@1$2@1$0#8>2HI$8>2LB@1$3$9>2SP$1>1X@1$3@2$5$1$1>1W@1$3$c>1m~0>2m'~0>0@3$d^3^2^1>0@3$f$7^3^2>0>1a$1>0@2$6@2$h0Z^1@2$h1^1@2$h2+2+k0>0@6$a?5HCEIL^b^a^9^8^2@2$e^8^3@7$b?5HCEIL^a^9^8^7^5^4").
Proof.
  intros HI LB SP X W m m' MU WM HO a Ha Hc. split.
  - unfold wa. apply MU. rewrite unsigned_lit by lia. apply HO; assumption.
  - intros Hw. apply WM. exact Hw.
Qed.

(* [comment removed for export] *)
Section WithH.
  Variable HI : ltac2:(zQ "10!itb$0").
  Hypothesis HH : ltac2:(zQ "10!km3@2$0?5HCEIL?2HI").

  Lemma aclient_range_sub : ltac2:(zQ "60!n8!jpb!jqb!io2!t7!iu2>2LB@1$4$5>2SP$0>1A$0>1n$0>2A'$0>2n'$0>0@6$2?5HCEIL?2HI^6^5^4^3>0@2$1^5^3>0@2$1@2$3^4^3@2$3^6^5>0@2$1Z^4@6$2?5HCEIL?2HI^a^9^6^5").
  Proof.
    intros LB SP A n A' n' HR H1 H2 H3. unfold aclient_range in *.
    destruct HR as [K|[K|[(b & Hb & K1 & K2)|[(b & Hb & K1 & K2)|[K|[K|K]]]]]].
    - left. lia.
    - right; left. intros a Ha. apply K. lia.
    - right; right; left. exists b. split; [exact Hb| lia].
    - right; right; right; left. exists b. split; [exact Hb| lia].
    - right; right; right; right; left. lia.
    - right; right; right; right; right; left. lia.
    - right; right; right; right; right; right. lia.
  Qed.

  Lemma aclient_range_LB_mono : ltac2:(zQ "50!iu2!n8!t7!jqb!jsf>2LB@1$2$0>3LB'@1$2$0>2SP$1>1A$1>1n$1>0@6$3?5HCEIL?2HI^5^3^2^1>0>1b$0>0@3$4$0^1^7@3$4$0^2^7@6$3?5HCEIL?2HI^6^5^4^3").
  Proof.
    intros LB LB' SP A n HR HL. unfold aclient_range in *.
    destruct HR as [K|[K|[(b & Hb & K1 & K2)|[(b & Hb & K1 & K2)|K]]]]; [left; exact K| right; left; exact K| | | right; right; right; right; exact K].
    - right; right; left. exists b. split; [apply HL; exact Hb| lia].
    - right; right; right; left. exists b. split; [apply HL; exact Hb| lia].
  Qed.

  (* [comment removed for export] *)

  Lemma aclient_addr_range : ltac2:(zQ "50!n8!t7!jt5!jqb!iu2>2LB@1$1$4>2SP$0>1a$0>0@5$2?5HCEIL?2HI^3^2^1@6$3?5HCEIL?2HI^4^3^2+1").
  Proof.
    intros LB SP a Hc. unfold aclient_addr, aclient_range in *.
    destruct Hc as [K|[K|[(b & Hb & K)|[(b & Hb & K)|[K|[K|K]]]]]]; [left; lia| right; left; intros x Hx; replace x with a by lia; exact K| | | right; right; right; right; left; lia| right; right; right; right; right; left; lia| right; right; right; right; right; right; lia].
    - right; right; left. exists b. split; [exact Hb| lia].
    - right; right; right; left. exists b. split; [exact Hb| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma aclient_range_off_frame : ltac2:(zQ "c0!n8!jpb!t7!ju5!jqb!jua!jv6!iu2!jvf!kk4!io2!jq0>1s@1$6?2HI>2LB@1$2$7>1m$8>2SP$0>1A$0>1n$0>2lo$0>0@4$5?2HI^7^6^5>0@6$4?5HCEIL?2HI^7^5^4^3>0@2$1@1$9?5HCEIL^3>0@2$bZ^5@2$3@2$1@2$a^7^6^5@2$1^8^7").
  Proof.
    intros s LB m SP A n lo HP HR CE Hn. pose proof (ah_fsb HI HH _ _ _ HP) as (F1 & F2 & F3).
    unfold aclient_range in HR.
    destruct HR as [K|[K|[(b & Hb & K1 & K2)|[(b & Hb & K1 & K2)|[K|[K|K]]]]]]; [right; exact K| left | left | left | left | left | left].
    - pose proof (K (A + n - 1) ltac:(lia)) as KA. acb; unfold aimg_client in *. lia.
    - pose proof (ah_blocks HI HH _ _ _ b HP Hb) as (_ & _ & _ & _ & R & _). acb. lia.
    - pose proof (ah_blocks HI HH _ _ _ b HP Hb) as (_ & _ & R0 & R1 & R & _).
      pose proof (sh_nsh_high (blk_addr b) (blk_size b) ltac:(unfold AIMG_TOP in *; lia) R0 ltac:(acb; unfold AAPP_HI in *; lia)).
      acb; unfold AHI_LO in *. lia.
    - acb. lia.
    - pose proof (sh_below_app (as_FSB HI + AFS_SIZE) ltac:(acb; unfold AIMG_TOP, AAPP_HI, AFS_SIZE in *; lia)).
      acb; unfold AHI_LO in *. lia.
    - acb; unfold AHI_LO in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fresh_block_disjoint_client : ltac2:(zQ "f0!n8!ip1!kkd!jpb!kl5!io2!klc!t7!ju5!jqb!jua!jv6!jvf!kk4!jq0>2s'@1$b?2HI>2LB@1$7@2$1@2$1$2$0$0>2m'$c>1p$2>1A$0>1n$0>2SP$0>1a$0>1k$0>0@4$a?2HI^9@3$6@2$1@2$1$2$0$0@4$4@2$1$2$0$0@4$4$2$0^6^5^4^8^7>0@6$9?5HCEIL?2HI^9^4^3^2>0@2$3@1$d?5HCEIL^5>0@2$eZ^4@2$8@2$3@2$5^6^5^9@2$3@2$5^9^8^6").
  Proof.
    intros s' LB m' p A n SP a k HP HR CE Hk.
    pose proof (ah_blocks HI HH _ _ _ (p, A, n) HP (or_introl eq_refl)) as (R1 & R2 & R3 & R4 & R5 & R6 & R7). cbn in R1, R2, R3, R4, R5, R6, R7.
    pose proof (ah_fsb HI HH _ _ _ HP) as (F1 & F2 & F3 & F4).
    unfold aclient_range in HR.
    destruct HR as [K|[K|[(b & Hb & K1 & K2)|[(b & Hb & K1 & K2)|[K|[K|K]]]]]].
    - right. acb. lia.
    - left. pose proof (K (a + k - 1) ltac:(lia)) as KA. acb; unfold aimg_client, AIMG_TOP in *. lia.
    - pose proof (ah_nodup HI HH _ _ _ HP) as ND. cbn in ND. inversion ND; subst.
      assert (NE : blk_id (p, A, n) <> blk_id b).
      { cbn. intros E. apply H1. apply in_map_iff. exists b. split; [symmetry; exact E| exact Hb]. }
      destruct (ah_disj HI HH _ _ _ (p, A, n) b HP (or_introl eq_refl) (or_intror Hb) NE) as [D|D]; cbn in D; lia.
    - pose proof (ah_blocks HI HH _ _ _ b HP (or_intror Hb)) as (_ & _ & Q0 & Q1 & Q & _).
      pose proof (aapp_disjoint_sh A n (blk_addr b) (blk_size b) R7 ltac:(unfold AIMG_TOP in *; lia) ltac:(acb; unfold AAPP_HI in *; lia) Q0). lia.
    - unfold AFS_SIZE in *. lia.
    - pose proof (aapp_disjoint_sh A n (as_FSB HI) AFS_SIZE R7 ltac:(unfold AIMG_TOP in *; lia) ltac:(acb; unfold AAPP_HI, AFS_SIZE in *; lia) ltac:(unfold AFS_SIZE; lia)).
      replace (nsh AFS_SIZE) with (AFS_SIZE / 8) in * by reflexivity.
      assert (sh (as_FSB HI + AFS_SIZE) = sh (as_FSB HI) + AFS_SIZE / 8) by (unfold sh, AFS_SIZE; Z.div_mod_to_equations; lia). lia.
    - assert (L : ALOWSH_LO < sh aceil) by (acb; unfold sh, ALOWSH_LO; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
      clear R2 F3. aapp_unfold. lia.
  Qed.

  Lemma fresh_block_outside : ltac2:(zQ "e0!n8!ip1!kkd!jpb!kl5!io2!klc!t7!ju5!jt5!jua!jv6!jvf!kk4>2s'@1$b?2HI>2LB@1$7@2$1@2$1$2$0$0>2m'$c>1p$2>1A$0>1n$0>2SP$0>1a$0>0@4$a?2HI^8@3$6@2$1@2$1$2$0$0@4$4@2$1$2$0$0@4$4$2$0^5^4^3^7^6>0@2$3@1$d?5HCEIL^3>0@5$9?5HCEIL?2HI^9^4^3@2$8@2$3@2$5^4+1^7@2$3@2$5^7^6^4").
  Proof.
    intros s' LB m' p A n SP a HP CE HC.
    eapply fresh_block_disjoint_client; [exact HP| apply aclient_addr_range; exact HC| exact CE| lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End WithH.

End HCW.

(* [comment removed for export] *)
