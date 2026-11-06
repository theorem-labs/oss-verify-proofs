(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep CellsX TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4listhc4prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh2RMalloc_iface_stmt~~~~~~k25block37Corelib4Init5Logicp53andp53not89OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU7BJFrame3HCW~~~~~~r57rin_ivsk2crclient_addrk23mem04Npos35stdpp9bitvectorbdefinitionshhd2bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~hk02wahc6optionp52eqhc4None3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshp55wview79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~ht55rsegsr57xclient46Stdlib6ZArith6BinInt1Zii52leii52ltii53powr55xpres36Stdlib5Lists4Listil82Ink2arheap_preshc3appp53iffp52orhc3fsthc3snd69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~ipb5hceil37Corelib5Lists7ListDefitf6Forall79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~jg03ivljg05munchjg05wmonok28blk_addrk28blk_sizeii53addk2drclient_ranger5dxclient_rangehk08bytes_athc6lengthii56of_nathk05wr_at79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~jra8rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~kg14cellkg1acells_size" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

Fixpoint rin_ivs (X : list (Z * Z)) (a : Z) : Prop :=
  match X with [] => False | iv :: X' => (fst iv <= a < snd iv) \/ rin_ivs X' a end.

Definition xclient : ltac2:(zQ "40!h9!j4!jb!od>2LB@1$1$3>2SP$0>1X@1$1@2$2$0$0>1a$0P") := ltac2:(zQ "80!h9!j4!jb!q9!qf!v8!od!hg2\2LB@1$1$6\2SP$0\1X@1$1@2$2$0$0\1a$0@2$3@3$7^4^3^1@1$4@2$5^2^1").

Definition xpres : ltac2:(zQ "50!h9!j4!hh1!jb!od>2LB@1$1$4>2SP$0>1X@1$1@2$3$0$0>1m$2>2m'$2P") := ltac2:(zQ "h30!hh7!hja!h9!hna!ho0!ho9!hoe!j4!q9!qf!hsc!hh1!ih2!jb!ihb!od!ijd!ik3!ik9\2LB@1$7$f\2SP$2\1X@1$7@2$d$2$2\1m$b\2m'$b>1a$2>0@2$8@2$h0Z^1@2$h1^1@2$h2+2+k0>0@4$e^7^6^5^2@2$8@3$5@1$4@1$1@1$0#8@1^4@1$3^3@1^5@1$3^3>0@1$9@3$5@1$4@1$1@1$0#8@3$a$c^5@1$3^3@1$6@1$1@1$0#8@1$9@3$5@1$4@1$1@1$0#8@3$a$c^5@1$3^4@1$6@1$1@1$0#8").

Lemma xpres_refl : ltac2:(zQ "60!h9!j4!jb!il0!od!hh1>2LB@1$1$4>2SP$0>1X@1$1@2$2$0$0>1m$5@5$3^4^3^2^1^1").
Proof. intros LB SP X m a _ _. auto. Qed.

Lemma xpres_trans : ltac2:(zQ "60!h9!il0!hh1!j4!jb!od>2LB@1$3$5>2SP$0>1X@1$3@2$4$0$0>2m1$2>2m2$2>2m3$2>0@5$1^6^5^4^3^2>0@5$1^7^6^5^3^2@5$1^8^7^6^5^3").
Proof.
  intros LB SP X m1 m2 m3 H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2].
  split; [congruence| auto].
Qed.

Lemma xpres_weaken : ltac2:(zQ "90!h9!od!j4!jb!v8!il0!hh1!imb!ijd>2LB@1$2$1>3LB'@1$2$1>2SP$0>3SP'$0>1X@1$2@2$3$0$0>2X'@1$2@2$3$0$0>1m$6>2m'$6>0@5$5^8^6^4^2^1>0@2$8^7^6>0>1b$1>0@3$7$1^1^a@3$7$1^2^c>0>1a$0>0@2$4^8^1@2$4^8^2@5$5^b^9^7^6^5").
Proof.
  intros LB LB' SP SP' X X' m m' H HS HL HX a Ha [Hc Hx]. apply H; [exact Ha|]. split; [| intros K; apply Hx, HX, K].
  destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right].
  exists b. split; [apply HL; exact Hb| exact Hr].
Qed.

Lemma xpres_of_heap_pres : ltac2:(zQ "70!h9!j4!hh1!jb!il0!od!in1>2LB@1$1$5>2SP$0>1X@1$1@2$3$0$0>1m$2>2m'$2>0@4$6^5^4^2^1@5$4^6^5^4^3^2").
Proof. intros LB SP X m m' H a Ha [Hc _]. apply H; assumption. Qed.

Lemma rin_ivs_app : ltac2:(zQ "70!h9!jb!v8!j4!ine!io4!ioa>2X1@1$3@2$1$0$0>2X2@1$3@2$1$0$0>1a$0@2$5@2$2@3$4@2$1$0$0^3^2^1@2$6@2$2^3^1@2$2^2^1").
Proof. induction X1 as [|iv X1 IH]; intros; cbn; [tauto|]. rewrite IH. tauto. Qed.

(* [comment removed for export] *)
Lemma xpres_of_munch : ltac2:(zQ "h91!h9!hh7!ijd!hja!j4!jb!od!iof!ho0!ip5!q9!it6!ioa!iv6!jjc!jk3!jkc!v8!il0!jl5!jm0!ih2!imb!jmb!ik3&>0@1$3@1$1#k0@1$8@1$3@1$1#8>2LB@1$4$6>2SP$0>1X@1$4@2$5$0$0>1W@1$4$e>1m~0>2m'~0>0@3$f^3^2^1>0@3$h0$h5^3^2>0@3$d@2$5$0$0\2iv@2$5$0$0@2$c@2$a@2$2@1$b?5HCEIL@3$7$0$0^1@2$2@3$9$0$0^1^8>1a$0>0@2$a@2$2@3$7$0$0^2^1@2$h8^1@3$9$0$0^2@2$h1^9^2^5>0>1b$6>0@3$h6$6^1^a@2$2@2$h7@1$h3^2@1$h4^2@1$b?5HCEIL@5$h2^a^9^8^6^5").
Proof.
  intros LB SP X W m m' MU WM FW HB a Ha [Hc Hx].
  assert (OUT : outside W a).
  { clear MU WM. induction W as [|[lo hi] W IH]; [exact I|]. cbn.
    pose proof (Forall_inv FW) as H1. cbn in H1.
    split; [| apply IH; apply (Forall_inv_tail FW)].
    destruct H1 as [[H1 H2]|H1].
    - destruct Hc as [Hc|[[Hc _]|(b & Hb & Hr)]]; [lia| hcb; lia|]. pose proof (HB b Hb). lia.
    - intros R. apply Hx. apply H1. exact R. }
  split.
  - unfold wa. apply MU. rewrite unsigned_lit by lia. exact OUT.
  - intros Hw. apply WM. exact Hw.
Qed.

(* [comment removed for export] *)
Definition xclient_range : ltac2:(zQ "40!h9!j4!jb!od>2LB@1$1$3>2SP$0>1X@1$1@2$2$0$0>1A$0>1n$0P") := ltac2:(zQ "c0!h9!jb!j4!ijd!iof!ip5!q9!ioa!iv6!od!jn2!jmb\2LB@1$2$9\2SP$0\1X@1$2@2$1$0$0\1A$0\1n$0@2$6@4$a^5^4^2^1@3$8@2$1$0$0\2iv@2$1$0$0@2$7@2$3@2$b^3^2@3$4$0$0^1@2$3@3$5$0$0^1^3^3").

Lemma xclient_range_addr : ltac2:(zQ "a0!h9!j4!jb!q9!ihb!jo2!od!jmb!ijd!ik3>2LB@1$1$6>2SP$0>1X@1$1@2$2$0$0>1A$0>1n$0>1a$0>0@5$5^6^5^4^3^2>0@2$3@2$8^4^2@2$9^2@2$7^4^3@4$4^8^7^6^3").
Proof.
  intros LB SP X A n a [HR HX] Ha. split; [eapply rclient_range_addr; eauto|].
  induction X as [|iv X IH]; cbn; [tauto|]. pose proof (Forall_inv HX) as H1. cbn in H1. pose proof (Forall_inv_tail HX) as H2.
  intros [K|K]; [lia| exact (IH H2 K)].
Qed.

Lemma xpres_bytes_at : ltac2:(zQ "d0!h9!j4!hh7!jp2!hh1!ih2!hja!jpe!jb!jo2!il0!od!jq7>2LB@1$1$b>2SP$0>1X@1$1@2$8$0$0>1m$4>2m'$4>1A$0>2bs@1$1@1$6@1$2#8>0@5$a^7^6^5^4^3>0@4$3$5^5^3^2>0@5$9^9^8^7^4@1$c@2$7@1$6@1$2#8^3@4$3$5^6^5^4").
Proof.
  (intros LB SP X m m' A bs HP nd_i1 HR; ndestruct nd_i1 as (H0 & H1 & HB)). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply xclient_range_addr; [exact HR|lia])) as [E _].
  rewrite E. reflexivity.
Qed.

Lemma xpres_wr_at : ltac2:(zQ "90!h9!j4!jr1!hh1!ih2!jb!jo2!il0!od>2LB@1$1$8>2SP$0>1X@1$1@2$5$0$0>1m$3>2m'$3>1A$0>1n$0>0@5$7^7^6^5^4^3>0@4$2$4^5^3^2>0@5$6^9^8^7^4^3@4$2$4^6^5^4").
Proof.
  (intros LB SP X m m' A n HP nd_i2 HR; ndestruct nd_i2 as (H0 & H1 & HW)). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(eapply xclient_range_addr; [exact HR|lia])) as [_ W].
  apply W. apply HW. exact Hi.
Qed.

Lemma xpres_rw_cells : ltac2:(zQ "c0!h9!j4!jv5!hh1!ih2!jb!kjd!kk5!jo2!il0!od!jq7>2LB@1$1$a>2SP$0>1X@1$1@2$5$0$0>1m$3>2m'$3>1A$0>2cs@1$1$6>0@5$9^7^6^5^4^3>0@4$2$4^5^3^2>0@5$8^9^8^7^4@1$b@1$7^3@4$2$4^6^5^4").
Proof.
  intros LB SP X m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply xpres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply xpres_wr_at; eauto.
Qed.


End HCW.
(* [comment removed for export] *)
