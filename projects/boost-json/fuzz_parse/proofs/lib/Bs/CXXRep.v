(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep CellsX TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AsConst AsIface AsCXXHeap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init5Logichc3and46Stdlib6ZArith6BinInt1Zj62lehc2eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsShadow~~~~~~l84aappl85aceilj63addj62ltj66modulo79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsIface~~~~~~r9cablock_ranger93asr89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs6CXXRep2RB~~~~~~hgbcrblock_range37Corelib4Init9Datatypeshla4listhla4prodr95blockhc3notr9caclient_addr89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs6CXXRep5WithH~~~~~~hpf7rin_ivsr93mem04Npos35stdpp9bitvectorbdefinitionshv82bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ihb2wahla6optionhla4None3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsimd5wview79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~iqd5asegshpf7xclientj63powhpf5xpres36Stdlib5Lists4Listjgb2Inr95apreshla3apphc3iffhc2orhla3fsthla3snd37Corelib5Lists7ListDefjkc6Forallr98as_RHEAPr95as_Str9casan_rt_hyps79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~jof3ivljof5munchjof5wmonor9daclient_rangehpfdxclient_rangeihb8bytes_athla6lengthj66of_natihb5wr_at79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~kid8rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~kn44cellkn4acells_sizejof3stk" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section RB.
  Context {HCEIL : HeapCeil}.
  (* [comment removed for export] *)
  Definition rblock_range : ltac2:(zQ "10!h9>1A$0>1n$0P") := ltac2:(zQ "90!j0!h9!ke!l3!p6!pd!q5!qb!r0\1A$1\1n$1@2$0@2$7Z^2@2$0@3$3$1@2$8^2+h0Z@2$0@2$2Z^1@2$0@3$4?5HCEIL^2^1@2$2@2$6^2^1@1$5?5HCEIL").

  Lemma ablock_rblock : ltac2:(zQ "40!h9!v6!hg5!hka>1H$2>1A$0>1n$0>0@4$1?5HCEIL^3^2^1@2$3^3^2").
  Proof. (intros H A n nd_i1; ndestruct nd_i1 as (R1 & R2 & R3 & R4 & R5 & _ & R7)). repeat split; assumption. Qed.
End RB.

Section WithH.
  Context {HCEIL : HeapCeil}.
  Variable HI : ltac2:(zQ "10!hg5$0").

(* [comment removed for export] *)
(* [comment removed for export] *)

Record srep := mkS { sb : list byte ;            (* [comment removed for export] *)
                     sown : option block }.      (* [comment removed for export] *)

  (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint rin_ivs (X : list (Z * Z)) (a : Z) : Prop :=
  match X with [] => False | iv :: X' => (fst iv <= a < snd iv) \/ rin_ivs X' a end.

Definition xclient : ltac2:(zQ "40!h9!hn2!hna!ho2>2LB@1$1$3>2SP$0>1X@1$1@2$2$0$0>1a$0P") := ltac2:(zQ "80!h9!hn2!hna!j0!hoa!hp0!ho2!hu1\2LB@1$1$6\2SP$0\1X@1$1@2$2$0$0\1a$0@2$3@5$5?5HCEIL?2HI^4^3^1@1$4@2$7^2^1").

Definition xpres : ltac2:(zQ "50!h9!hn2!huc!hna!ho2>2LB@1$1$4>2SP$0>1X@1$1@2$3$0$0>1m$2>2m'$2P") := ltac2:(zQ "h30!hv2!ih5!h9!il5!ilb!l3!im5!hn2!j0!hoa!iq4!iu8!huc!hna!ho2!iv1!ke!qb!ivc\2LB@1$7$e\2SP$2\1X@1$7@2$d$2$2\1m$c\2m'$c>1a$2>0@2$8@2$h0Z^1@2$h1^1@2$h2+2+k0>0@4$f^7^6^5^2@2$8@3$5@1$4@1$1@1$0#8@1^4@1$3^3@1^5@1$3^3>0@1$9@3$5@1$4@1$1@1$0#8@3$a$b^5@1$3^3@1$6@1$1@1$0#8@1$9@3$5@1$4@1$1@1$0#8@3$a$b^5@1$3^4@1$6@1$1@1$0#8").

Lemma xpres_refl : ltac2:(zQ "60!h9!hn2!hna!ho2!huc!jg2>2LB@1$1$3>2SP$0>1X@1$1@2$2$0$0>1m$4@5$5^4^3^2^1^1").
Proof. intros LB SP X m a _ _. auto. Qed.

Lemma xpres_trans : ltac2:(zQ "60!h9!huc!jg2!hn2!hna!ho2>2LB@1$3$5>2SP$0>1X@1$3@2$4$0$0>2m1$1>2m2$1>2m3$1>0@5$2^6^5^4^3^2>0@5$2^7^6^5^3^2@5$2^8^7^6^5^3").
Proof.
  intros LB SP X m1 m2 m3 H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2].
  split; [congruence| auto].
Qed.

Lemma xpres_weaken : ltac2:(zQ "90!h9!ho2!hn2!hna!huc!hu1!jg2!jhe!ke>2LB@1$2$1>3LB'@1$2$1>2SP$0>3SP'$0>1X@1$2@2$3$0$0>2X'@1$2@2$3$0$0>1m$4>2m'$4>0@5$6^8^6^4^2^1>0@2$8^7^6>0>1b$1>0@3$7$1^1^a@3$7$1^2^c>0>1a$0>0@2$5^8^1@2$5^8^2@5$6^b^9^7^6^5").
Proof.
  intros LB LB' SP SP' X X' m m' H0 HS HL HX a Ha [Hc Hx]. apply H0; [exact Ha|]. split; [| intros K; apply Hx, HX, K].
  eapply aclient_addr_weaken; eauto.
Qed.

(* [comment removed for export] *)
Lemma xpres_of_apres : ltac2:(zQ "70!h9!hn2!huc!hna!ji4!ho2!jg2>2LB@1$1$5>2SP$0>1X@1$1@2$3$0$0>1m$2>2m'$2>0@6$4?5HCEIL?2HI^5^4^2^1@5$6^6^5^4^3^2").
Proof. intros LB SP X m m' H0 a Ha [Hc _]. apply H0; assumption. Qed.

Lemma rin_ivs_app : ltac2:(zQ "70!h9!hna!hu1!hn2!jic!jj3!jj9>2X1@1$3@2$1$0$0>2X2@1$3@2$1$0$0>1a$0@2$5@2$2@3$4@2$1$0$0^3^2^1@2$6@2$2^3^1@2$2^2^1").
Proof. induction X1 as [|iv X1 IH]; intros; cbn; [tauto|]. rewrite IH. tauto. Qed.

(* [comment removed for export] *)
Lemma xpres_of_munch : ltac2:(zQ "h91!h9!hv2!ih5!hn2!hna!ke!jje!ilb!jk5!j0!jj9!jm3!iu8!jmd!jn8!jo0!ho2!huc!pd!hu1!jg2!jsb!jt2!jtb!qb&>0@1$2@1$1#k0@1$7@1$2@1$1#8>1s@1$e?2HI>2LB@1$3$h0>2SP$0>1X@1$3@2$4$0$0>1W@1$3$h5>2m0$h1>1m~0>2m'~0>0@2$f?5HCEIL?2HI>0@4$d?2HI^9^8^4>0@3$h6^6^4^3>0@3$h7$c^5^4>0@3$b@2$4$0$0\2iv@2$4$0$0@2$a@2$9@2$5@1$h2?5HCEIL@3$6$0$0^1@2$5@3$8$0$0^1^b>1a$0>0@2$9@2$5@3$6$0$0^2^1@2$h8^1@3$8$0$0^2@2$h3^c^2^8@5$h4^c^b^a^7^6").
Proof.
  intros s LB SP X W m0 m m' HH RH MU WM FW a Ha [Hc Hx].
  assert (OUT : outside W a).
  { clear MU WM. induction W as [|[lo hi] W IH]; [exact I|]. cbn.
    pose proof (Forall_inv FW) as H1. cbn in H1.
    split; [| apply IH; apply (Forall_inv_tail FW)].
    destruct H1 as [[H1 H2]|H1].
    - intros K. assert (SP <= a \/ a < aceil) as [C|C]; [| lia | lia].
      pose proof (apres_of_munch HI HH s LB SP [(lo, hi)] m0 m m RH (munch_refl _ m) (wmono_refl asegs m)
                    ltac:(constructor; [cbn; lia| constructor])) as AP.
      (* [comment removed for export] *)
      unfold aclient_addr in Hc. destruct Hc as [Hc|Hc]; [left; exact Hc| right].
      pose proof (ah_fsb HI HH _ _ _ RH) as (F1 & F2 & F3).
      destruct Hc as [Hc|[(b & Hb & Hr)|[(b & Hb & Hr)|[Hc|[Hc|Hc]]]]].
      + acb; unfold aimg_client, ATLS_PRIV_LO, ATLS_PRIV_HI, ATSD0, ATP in *. lia.
      + pose proof (ah_blocks HI HH _ _ _ _ RH Hb) as (_ & _ & _ & _ & R & _). lia.
      + pose proof (ah_blocks HI HH _ _ _ _ RH Hb) as (_ & _ & R0 & R1 & R & _).
        pose proof (sh_below_aceil (blk_addr b + blk_size b + 8) ltac:(acb; unfold AIMG_TOP, AAPP_HI in *; lia)).
        unfold nsh, sh in *. rewrite ASHADOW_BASE_val in *. Z.div_mod_to_equations. lia.
      + lia.
      + pose proof (sh_below_aceil (as_FSB HI + AFS_SIZE) ltac:(acb; unfold AIMG_TOP, AAPP_HI, AFS_SIZE in *; lia)).
        acb; unfold AFS_SIZE in *. lia.
      + acb; unfold AHI_LO in *. lia.
    - intros R. apply Hx. apply H1. exact R. }
  split.
  - unfold wa. apply MU. rewrite unsigned_lit by lia. exact OUT.
  - intros Hw. apply WM. exact Hw.
Qed.

(* [comment removed for export] *)
Definition xclient_range : ltac2:(zQ "40!h9!hn2!hna!ho2>2LB@1$1$3>2SP$0>1X@1$1@2$2$0$0>1A$0>1n$0P") := ltac2:(zQ "c0!h9!hna!hn2!ke!jje!jk5!j0!jj9!jm3!ju4!ho2!q5\2LB@1$2$a\2SP$0\1X@1$2@2$1$0$0\1A$0\1n$0@2$6@6$9?5HCEIL?2HI^5^4^2^1@3$8@2$1$0$0\2iv@2$1$0$0@2$7@2$3@2$b^3^2@3$4$0$0^1@2$3@3$5$0$0^1^3^3").

Lemma xclient_range_addr : ltac2:(zQ "a0!h9!hn2!hna!j0!ho2!iv1!jv4!q5!ke!qb>2LB@1$1$4>2SP$0>1X@1$1@2$2$0$0>1A$0>1n$0>1a$0>0@5$6^6^5^4^3^2>0@2$3@2$8^4^2@2$9^2@2$7^4^3@4$5^8^7^6^3").
Proof.
  intros LB SP X A n a [HR HX] Ha. split; [eapply aclient_range_addr; eauto|].
  induction X as [|iv X IH]; cbn; [tauto|]. pose proof (Forall_inv HX) as H1. cbn in H1. pose proof (Forall_inv_tail HX) as H2.
  intros [K|K]; [lia| exact (IH H2 K)].
Qed.

Lemma xpres_bytes_at : ltac2:(zQ "d0!h9!hn2!hv2!iu8!huc!kg5!ih5!kh1!hna!ho2!jv4!jg2!khb>2LB@1$1$9>2SP$0>1X@1$1@2$8$0$0>1m$4>2m'$4>1A$0>2bs@1$1@1$6@1$2#8>0@5$b^7^6^5^4^3>0@4$5$3^5^3^2>0@5$a^9^8^7^4@1$c@2$7@1$6@1$2#8^3@4$5$3^6^5^4").
Proof.
  (intros LB SP X m m' A bs HP nd_i2 HR; ndestruct nd_i2 as (H0 & H1 & HB)). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply xclient_range_addr; [exact HR|lia])) as [E _].
  rewrite E. reflexivity.
Qed.

Lemma xpres_wr_at : ltac2:(zQ "90!h9!hn2!iu8!huc!ki4!hna!ho2!jv4!jg2>2LB@1$1$6>2SP$0>1X@1$1@2$5$0$0>1m$3>2m'$3>1A$0>1n$0>0@5$8^7^6^5^4^3>0@4$4$2^5^3^2>0@5$7^9^8^7^4^3@4$4$2^6^5^4").
Proof.
  (intros LB SP X m m' A n HP nd_i3 HR; ndestruct nd_i3 as (H0 & H1 & HW)). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(eapply xclient_range_addr; [exact HR|lia])) as [_ W].
  apply W. apply HW. exact Hi.
Qed.

Lemma xpres_rw_cells : ltac2:(zQ "c0!h9!hn2!iu8!huc!km8!hna!ho2!jv4!jg2!kr0!kr8!khb>2LB@1$1$6>2SP$0>1X@1$1@2$5$0$0>1m$3>2m'$3>1A$0>2cs@1$1$9>0@5$8^7^6^5^4^3>0@4$4$2^5^3^2>0@5$7^9^8^7^4@1$b@1$a^3@4$4$2^6^5^4").
Proof.
  intros LB SP X m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply xpres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply xpres_wr_at; eauto.
Qed.

Lemma xpres_stk : ltac2:(zQ "d0!h9!hna!ke!hn2!iu8!huc!ks6!jje!jk5!jj9!jm3!ho2!jg2>2LB@1$3$b>2SP$0>1X@1$3@2$1$0$0>1m$5>2m'$5>2lo$0>2hi$0>0@5$c^7^6^5^4^3>0@4$6$4^5^3^2>0@2$2^8^4>0@3$a@2$1$0$0\2iv@2$1$0$0@2$9@2$2^5@3$7$0$0^1@2$2@3$8$0$0^1^6^8@4$6$4^7^6^5").
Proof.
  intros LB SP X m m' lo hi HP ST HS HX. ndestruct ST as (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|].
  intros i Hi.
  assert (XC : xclient LB SP X i).
  { split; [left; lia|]. clear HP HW. induction X as [|iv X IH]; cbn; [tauto|].
    pose proof (Forall_inv HX) as K1. cbn in K1. pose proof (Forall_inv_tail HX) as K2. intros [K|K]; [lia| exact (IH K2 K)]. }
  destruct (HP i ltac:(lia) XC) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithH.

Arguments xpres {HCEIL} HI LB SP X m m'.
Arguments xclient {HCEIL} HI LB SP X a.
Arguments xclient_range {HCEIL} HI LB SP X A n.
(* [comment removed for export] *)
