(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep Frame Cells TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs RMalloc_iface_stmt RF_aligned_alloc_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4listhc4prodhc4conshc4pairhc3nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Refh2RMalloc_iface_stmt~~~~~~l63mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~q64cellhc3fsthc3sndq62C879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~va8rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~hk02wz79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~ho15rsegs37Corelib4Init5Logichs63and37Corelib5Lists7ListDefhu16Forallq62C479OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref6RHeapX~~~~~~ig7eEH_IMG_WORDS1889OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref6RHeapX2HC~~~~~~il68img_wordig7h1RMALLOC_REPLACEDX46Stdlib6ZArith6BinInt1Zir82leir82lths62orir83addil68img_addrl65blockl6crclient_addr04Npos79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~jh28bytes_at35stdpp9bitvectorbdefinitionsjl82bvhc6lengthl6arheap_presir86of_natjh25wr_atq6acells_sizeil67eh_imgRhs65Falsel68blk_addrl68blk_sizel6crblock_rangel6h0rclient_write_ok36Stdlib5Lists4Listjve2In79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~kh77outsidehc6optionkh73ivlkh75munchkh75wmono79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~ko06PStatel6crmalloc_stmt99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref6RHeapX2HC1X~~~~~~kt56RHEAPXl6arfree_stmtl6h0RHEAP_frame_stmtl6h6RHEAP_block_range_stmtl6haRHEAP_blocks_disjoint_stmtl6h7RHEAP_blocks_nodup_stmt36Stdlib7SortingbPermutationlp5bPermutation79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Refh5RF_aligned_alloc_stmt~~~~~~ls0fraligned16_stmtig7cEH_IMG_WORDSl68RGOT_SSPl6aRSSP_GUARD" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition EH_IMG_WORDS : ltac2:(zQ "30!h9!j4!jb@1$1@2$2$0$0") := ltac2:(zQ "50!h9!jb!k2!k9!l0@3$2@2$1$0$0@4$3$0$0+vokt8+tknuc@3$2@2$1$0$0@4$3$0$0+voku0+tkoi4@3$2@2$1$0$0@4$3$0$0+voku8+tkos0@3$2@2$1$0$0@4$3$0$0+volg8+tkpu4@3$2@2$1$0$0@4$3$0$0+volh0+tkqsc@3$2@2$1$0$0@4$3$0$0+volh8+tkqv4@3$2@2$1$0$0@4$3$0$0+volj0+tkrq0@3$2@2$1$0$0@4$3$0$0+vomg0+vppq8@3$2@2$1$0$0@4$3$0$0+vomh8Z@3$2@2$1$0$0@4$3$0$0+voml8+vomg0@3$2@2$1$0$0@4$3$0$0+vomn0+pitqc@3$2@2$1$0$0@4$3$0$0+vomr8+vluq8@3$2@2$1$0$0@4$3$0$0+voms8+vppg0@3$2@2$1$0$0@4$3$0$0+vomt0+vpov8@3$2@2$1$0$0@4$3$0$0+vomt8+hgpso8@3$2@2$1$0$0@4$3$0$0+vonn0+hirmv8@3$2@2$1$0$0@4$3$0$0+vpnv0+pkuq8@3$2@2$1$0$0@4$3$0$0+vpov8+nnsq8@3$2@2$1$0$0@4$3$0$0+vppg0+nntr4@1$4@2$1$0$0").
(* [comment removed for export] *)
Definition EH_IMG_WORDS18 : ltac2:(zQ "30!h9!j4!jb@1$1@2$2$0$0") := ltac2:(zQ "50!h9!jb!k2!k9!l0@3$2@2$1$0$0@4$3$0$0+vokt8+tknuc@3$2@2$1$0$0@4$3$0$0+voku0+tkoi4@3$2@2$1$0$0@4$3$0$0+voku8+tkos0@3$2@2$1$0$0@4$3$0$0+volg8+tkpu4@3$2@2$1$0$0@4$3$0$0+volh0+tkqsc@3$2@2$1$0$0@4$3$0$0+volh8+tkqv4@3$2@2$1$0$0@4$3$0$0+volj0+tkrq0@3$2@2$1$0$0@4$3$0$0+vomg0+vppq8@3$2@2$1$0$0@4$3$0$0+vomh8Z@3$2@2$1$0$0@4$3$0$0+voml8+vomg0@3$2@2$1$0$0@4$3$0$0+vomn0+pitqc@3$2@2$1$0$0@4$3$0$0+vomr8+vluq8@3$2@2$1$0$0@4$3$0$0+voms8+vppg0@3$2@2$1$0$0@4$3$0$0+vomt0+vpov8@3$2@2$1$0$0@4$3$0$0+vomt8+hgpso8@3$2@2$1$0$0@4$3$0$0+vpnv0+pkuq8@3$2@2$1$0$0@4$3$0$0+vpov8+nnsq8@3$2@2$1$0$0@4$3$0$0+vppg0+nntr4@1$4@2$1$0$0").
Definition RMALLOC_REPLACEDX : Z := 0x12be68.   (* [comment removed for export] *)

Section HC.
  Context {HCEIL : HeapCeil}.

Definition img_word : ltac2:(zQ "30!h9!jb!q0>1m$2>2av@2$1$0$0P") := ltac2:(zQ "c0!h9!u2!k2!u9!l0!jb!uf!v5!hj5!hnb!q0!hrd\1m$a\2av@2$5$0$0@4$8$b^2@3$3$0$0^1@3$2$1@1$7@1$9@3$6$0$0^1@1$4$1").
Definition eh_imgR : ltac2:(zQ "10!q0>1m$0P") := ltac2:(zQ "f0!h9!u2!k2!l0!jb!hta!hv8!ig2!hj5!hnb!ik4!ip6!iq2!q0!hrd\1m$d@2$5@3$6@2$4$0$0@1$b^1$a@4$8$e^1$c@3$2$1@1$7@1$9Z@1$3$1").

(* [comment removed for export] *)
Definition img_addr : ltac2:(zQ "10!h9>1a$0P") := ltac2:(zQ "70!hta!it0!it6!itc!iq2!h9!iu2\1a$5@2$3@2$0@2$1+vokt8^1@2$2^1+volj8@2$3@2$0@2$1+vomg0^1@2$2^1+vomu0@2$3@2$0@2$1+vpnv0^1@2$2^1+vpnv8@2$3@2$0@2$1+vpov8^1@2$2^1+vppg8@2$0@2$1$4^1@2$2^1@2$6$4+4").

Lemma img_words18_inside : ltac2:(zQ "a0!h9!u9!jb!hta!hv8!ik4!iu9!iu2!it0!it6@3$4@2$2$0$0\2av@2$2$0$0>1a$0>0@2$3@2$8@3$1$0$0^2^1@2$9^1@2$7@3$1$0$0^2+8@1$6^2$5").
Proof. unfold EH_IMG_WORDS18, img_addr, RMALLOC_REPLACEDX. repeat (constructor; [cbn [fst snd]; intros; lia|]). constructor. Qed.

Lemma img_addr_client : ltac2:(zQ "50!h9!j4!iu9!iv5!ivd>2LB@1$1$3>2SP$0>1a$0>0@1$2^1@3$4^4^3^2").
Proof.
  intros LB SP a Ha. right. left. unfold img_addr, ralloc_static, RMALLOC_REPLACEDX, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK in *. lia.
Qed.

Lemma img_bytes_at_pres : ltac2:(zQ "h00!h9!j4!jgc!jkc!q0!hrd!jn5!jnb!hta!iu9!iv5!jo4!iu2!it0!it6!jp1>2LB@1$1$a>2SP$0>1m$4>2m'$4>1A$0>2bs@1$1@1$6@1$2#8>0@4$b^6^5^4^3>0@4$3$5^5^3^2>0>1a$0>0@2$8@2$d^5^1@2$e^1@2$c^5@1$f@2$7@1$6@1$2#8^4@1$9^2@4$3$5^6^5^4").
Proof.
  (intros LB SP m m' A bs HP nd_i1 HA; ndestruct nd_i1 as (H0 & H1 & HB)). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) (img_addr_client LB SP _ (HA (A + Z.of_nat i) ltac:(lia)))) as [E _].
  rewrite E. reflexivity.
Qed.

Lemma img_wr_at_pres : ltac2:(zQ "c0!h9!jpb!q0!hrd!j4!hta!iu9!iv5!jo4!iu2!it0!it6>2LB@1$4$7>2SP$0>1m$2>2m'$2>1A$0>1n$0>0@4$8^6^5^4^3>0@4$1$3^5^3^2>0>1a$0>0@2$5@2$a^5^1@2$b^1@2$9^5^4@1$6^2@4$1$3^6^5^4").
Proof.
  (intros LB SP m m' A n HP nd_i2 HA; ndestruct nd_i2 as (H0 & H1 & HW)). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) (img_addr_client LB SP _ (HA (A + i) ltac:(lia)))) as [_ W].
  apply W. apply HW. exact Hi.
Qed.

Lemma img_rw_cells_pres : ltac2:(zQ "f0!h9!j4!hj5!q0!hrd!hta!u2!jq4!iu9!iv5!jo4!iu2!it0!it6!jp1>2LB@1$1$9>2SP$0>1m$3>2m'$3>1A$0>2cs@1$1$6>0@4$a^6^5^4^3>0@4$2$4^5^3^2>0>1a$0>0@2$5@2$c^5^1@2$d^1@2$b^5@1$e@1$7^4@1$8^2@4$2$4^6^5^4").
Proof.
  intros LB SP m m' A cs HP [[Hwf HB] HW] HA. split; [split; [exact Hwf|]|].
  - eapply img_bytes_at_pres; eauto. rewrite cells_bytes_length by assumption. exact HA.
  - eapply img_wr_at_pres; eauto.
Qed.

Lemma eh_imgR_rheap_pres : ltac2:(zQ "60!jr1!q0!j4!h9!iv5!jo4>2LB@1$2$4>2SP$3>1m$1>2m'$1>0@1$0^2>0@4$5^5^4^3^2@1$0^3").
Proof.
  intros LB SP m m' [HF HR] HP. split.
  - apply Forall_forall. intros av Hav.
    pose proof (proj1 (Forall_forall _ _) HF av Hav) as C. pose proof (proj1 (Forall_forall _ _) img_words18_inside av Hav) as I.
    unfold img_word in *. eapply img_rw_cells_pres; [exact HP| exact C|]. cbn [cells_size csize Nat.add]. intros a Ha. apply I. lia.
  - eapply img_rw_cells_pres; [exact HP| exact HR|]. cbn [cells_size csize Nat.add]. intros a Ha. unfold img_addr. lia.
Qed.

(* [comment removed for export] *)
Lemma write_ok_disjoint_img : ltac2:(zQ "h00!h9!iv5!u9!j4!jb!uf!jrc!hta!iu9!js5!jt0!jtb!jua!kh1!it0!it6>2LB@1$3$1>2iv@2$4$0$0>1a$0>0>1b$1>0@3$d$1^1^4@3$b?5HCEIL@1$9^2@1$a^2>0@3$c?5HCEIL^4^3>0@1$8^3>0@2$7@2$e@3$2$0$0^5^4@2$f^4@3$5$0$0^5$6").
Proof.
  intros LB iv a BR HW Ha Hin. hcb.
  unfold img_addr, RMALLOC_REPLACEDX in Ha. unfold rclient_write_ok, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RVMLOCK in HW.
  destruct HW as [H|[H|(b & Hb & H1 & H2)]]; [lia| lia|].
  npose (BR b Hb) as (R1 & R2 & R3 & R4 & R5). lia.
Qed.

Lemma outside_of_write_ok : ltac2:(zQ "c0!h9!iv5!j4!jb!hv8!kl3!iu9!js5!jt0!jtb!jua!kh1>2LB@1$2$1>1W@1$2@2$3$0$0>1a$0>0>1b$1>0@3$b$1^1^4@3$9?5HCEIL@1$7^2@1$8^2>0@3$4@2$3$0$0@2$a?5HCEIL^4^3>0@1$6^3@2$5^5^4").
Proof.
  intros LB W a BR FW Ha. induction W as [|[lo hi] W IH]; [exact I|]. cbn.
  split; [| apply IH; exact (Forall_inv_tail FW)].
  intros Hin. eapply (write_ok_disjoint_img LB (lo, hi) a BR (Forall_inv FW) Ha). cbn. exact Hin.
Qed.

Lemma img_rw_cells_frame : ltac2:(zQ "ha1!jgc!h9!jn5!j4!iv5!hrd!kle!hj5!jb!hta!hv8!u2!jq4!km7!kme!kn7!iu9!js5!jt0!jtb!jua!kh1!iu2!it0!it6!jp1&>0@1$2@1$0#k0@1$6@1$2@1$0#8>2LB@1$3$4>1W@1$3$d>1m~0>2m'~0>1A$1>2cs@1$3$b>0>1b$4>0@3$h5$4^1^7@3$h3?5HCEIL@1$h1^2@1$h2^2>0@4$7$5^5^3^2>0@3$e^7^6^5>0@3$f$5^7^6>0@3$a@2$8$1$1@2$h4?5HCEIL^a^9>0>1a$1>0@2$9@2$h7^8^1@2$h8^1@2$h6^8@1$h9@1$c^7@1$h0^2@4$7$5^9^8^7").
Proof.
  intros LB W m m' A cs BR [[Hwf (H0 & H1 & HB)] (W0 & W1 & HW)] MU WM FW HA.
  rewrite cells_bytes_length in H1, HB by assumption.
  assert (EQ : forall a, A <= a < A + Z.of_nat (cells_size cs) -> m' (wa a) = m (wa a)).
  { intros a Ha. apply MU. unfold wa. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64)%Z with (2^64)%Z. rewrite Z.mod_small by lia.
    eapply outside_of_write_ok; [exact BR| exact FW| apply HA; exact Ha]. }
  split; [split; [exact Hwf|]|].
  - split; [exact H0|]. rewrite cells_bytes_length by assumption. split; [exact H1|].
    intros i Hi. rewrite <- (HB i Hi). unfold mrd. rewrite (EQ (A + Z.of_nat i)) by lia. reflexivity.
  - split; [exact W0|]. split; [exact W1|]. intros i Hi. apply WM. apply HW. exact Hi.
Qed.

Lemma eh_imgR_frame : ltac2:(zQ "h30!iv5!j4!jgc!h9!jr1!jn5!kle!jb!hv8!km7!kme!kn7!js5!jt0!q0!jtb!jua!hrd!kh1>2LB@1$1$0>1W@1$1$9>1m$e>2m'>0@1$5@1$2#k0@1$6@1$5@1$2#8>0>1b$0>0@3$h2$0^1^5@3$f?5HCEIL@1$c^2@1$d^2>0@1$4^3>0@3$a^5^4^3>0@3$b$h1^5^4>0@3$8@2$7$3$3@2$h0?5HCEIL^8^7@1$4^6").
Proof.
  intros LB W m m' BR [HF HR] MU WM FW. split.
  - apply Forall_forall. intros av Hav.
    pose proof (proj1 (Forall_forall _ _) HF av Hav) as C. pose proof (proj1 (Forall_forall _ _) img_words18_inside av Hav) as I.
    unfold img_word in *. eapply img_rw_cells_frame; [exact BR| exact C| exact MU| exact WM| exact FW|]. cbn [cells_size csize Nat.add]. intros a Ha. apply I. lia.
  - eapply img_rw_cells_frame; [exact BR| exact HR| exact MU| exact WM| exact FW|]. cbn [cells_size csize Nat.add]. intros a Ha. unfold img_addr. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section X.
  Context (RHEAP : PState -> list block -> mem -> Prop)
          (rauxv_ok : mem -> Z -> Prop)
          (raddr_exposed : PState -> Z -> Prop)
          (lb_remove : bptr -> list block -> list block).

  Definition RHEAPX : ltac2:(zQ "40!j4!iv5!q0!krc>1s$3>2LB@1$0$1>1m$2P") := ltac2:(zQ "60!j4!hta!jr1!iv5!q0!krc\1s$5\2LB@1$0$3\1m$4@2$1@3?5RHEAP^3^2^1@1$2^1").


  Lemma rmalloc_stmt_X : ltac2:(zQ "20!ks6!lh7>0@4$0?5HCEIL?5RHEAP?8rauxv_ok?draddr_exposed@4$0?5HCEIL$1?8rauxv_ok?draddr_exposed").
  Proof.
    intros SPEC. unfold rmalloc_stmt. intros until errv. intros [HR IMG]. intros.
    eapply implM_mono; [eapply SPEC; eauto|].
    intros r s' ms' HQ. unfold rmalloc_post in *.
    ndestruct HQ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & E & MI & ST & ERR & AUX & PRES & FA & SO & HM).
    nexists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', errv'.
    split; [exact E|]. split; [exact MI|]. split; [exact ST|]. split; [exact ERR|]. split; [exact AUX|]. split; [exact PRES|].
    split; [exact FA|]. split; [exact SO|].
    destruct r as [p|].
    - ndestruct HM as (A & junk & EA & RNG & HR' & CELLS & EXP). exists A, junk. split; [exact EA|]. split; [exact RNG|].
      split; [split; [exact HR'| eapply eh_imgR_rheap_pres; [exact IMG| exact PRES]]|]. split; [exact CELLS| exact EXP].
    - destruct HM as [EA HR']. split; [exact EA|]. split; [exact HR'|]. eapply eh_imgR_rheap_pres; [exact IMG| exact PRES].
  Qed.

  Lemma rfree_stmt_X : ltac2:(zQ "20!li1!lh7>0@4$0?5HCEIL?5RHEAP?8rauxv_ok?9lb_remove@4$0?5HCEIL$1?8rauxv_ok?9lb_remove").
  Proof.
    intros SPEC. unfold rfree_stmt. intros until errv. intros [HR IMG]. intros.
    eapply implM_mono; [eapply SPEC; eauto|].
    intros r s' ms' HQ. unfold rfree_post in *.
    ndestruct HQ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MI & ST & ERR & AUX & PRES & FA & SO & HR').
    nexists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact E|]. split; [exact MI|]. split; [exact ST|]. split; [exact ERR|]. split; [exact AUX|]. split; [exact PRES|].
    split; [exact FA|]. split; [exact SO|]. split; [exact HR'|]. eapply eh_imgR_rheap_pres; [exact IMG| exact PRES].
  Qed.

  Lemma RHEAP_frame_X : ltac2:(zQ "30!lie!lh7!lk2>0@2$0?5HCEIL?5RHEAP>0@2$2?5HCEIL?5RHEAP@2$0?5HCEIL$1").
  Proof.
    intros FR BR s LB m m' W [HR IMG] MU WM FW. split; [eapply FR; eauto|].
    eapply eh_imgR_frame; [| exact IMG| exact MU| exact WM| exact FW]. intros b Hb. eapply BR; [exact HR| exact Hb].
  Qed.

  Lemma RHEAP_block_range_X : ltac2:(zQ "20!lk2!lh7>0@2$0?5HCEIL?5RHEAP@2$0?5HCEIL$1").
  Proof. intros H s LB m b [HR _] Hb. eapply H; eauto. Qed.
  Lemma RHEAP_blocks_disjoint_X : ltac2:(zQ "20!llc!lh7>0@1$0?5RHEAP@1$0$1").
  Proof. intros H s LB m b1 b2 [HR _]. eapply H; eauto. Qed.
  Lemma RHEAP_blocks_nodup_X : ltac2:(zQ "20!lna!lh7>0@1$0?5RHEAP@1$0$1").
  Proof. intros H s LB m [HR _]. eapply H; eauto. Qed.
  Lemma RHEAP_perm_X : ltac2:(zQ "60!iv5!j4!lh7!q0!krc!lr1>0>1s$4>2LB@1$1$0>3LB'@1$1$0>1m$3>0@3?5RHEAP^4^3^1>0@3$5$0^4^3@3?5RHEAP^6^4^3>1s$4>2LB@1$1$0>3LB'@1$1$0>1m$3>0@3$2^4^3^1>0@3$5$0^4^3@3$2^6^4^3").
  Proof. intros H s LB LB' m [HR IMG] P. split; [eapply H; eauto| exact IMG]. Qed.

  Lemma raligned16_stmt_X : ltac2:(zQ "20!mgd!lh7>0@4$0?5HCEIL?5RHEAP?8rauxv_ok?draddr_exposed@4$0?5HCEIL$1?8rauxv_ok?draddr_exposed").
  Proof.
    intros SPEC. unfold raligned16_stmt. intros until errv. intros [HR IMG]. intros.
    eapply implM_mono; [eapply SPEC; eauto|].
    intros r s' ms' [HQ CELL]. split; [| exact CELL]. unfold rmalloc_post in *.
    ndestruct HQ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & E & MI & ST & ERR & AUX & PRES & FA & SO & HM).
    nexists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', errv'.
    split; [exact E|]. split; [exact MI|]. split; [exact ST|]. split; [exact ERR|]. split; [exact AUX|]. split; [exact PRES|].
    split; [exact FA|]. split; [exact SO|].
    destruct r as [p|].
    - ndestruct HM as (A & junk & EA & RNG & HR' & CELLS & EXP). exists A, junk. split; [exact EA|]. split; [exact RNG|].
      split; [split; [exact HR'| eapply eh_imgR_rheap_pres; [exact IMG| exact PRES]]|]. split; [exact CELLS| exact EXP].
    - destruct HM as [EA HR']. split; [exact EA|]. split; [exact HR'|]. eapply eh_imgR_rheap_pres; [exact IMG| exact PRES].
  Qed.

  (* [comment removed for export] *)
  Lemma eh_img_words_of : ltac2:(zQ "h00!h9!u2!k2!l0!jb!hv8!v5!hj5!hnb!mi0!jr1!ip6!mj0!mjb!q0!hrd>1m$e>0@1$a^1>0@4$7$f^2$c@3$2$1@1$6@1$8$d@1$3$1@3$5@2$4$0$0@1$b^3$9").
  Proof.
    intros m [HF _] G. unfold EH_IMG_WORDS. unfold EH_IMG_WORDS18 in HF.
    repeat match type of HF with Forall _ (_ :: _) => pose proof (Forall_inv HF); apply Forall_inv_tail in HF end.
    repeat (constructor; [first [assumption | exact G]|]). constructor.
  Qed.
End X.
End HC.
(* [comment removed for export] *)
