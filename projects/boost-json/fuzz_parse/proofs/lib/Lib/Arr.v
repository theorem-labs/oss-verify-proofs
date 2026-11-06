(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk16lengthk14listk13nat37Corelib4Init5Logicmf2eq37Corelib4Init3Nato83mul79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~q04u32sq04u64sk13app79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ue9upd_bytesk16option01Zmf3andue8bytes_atue5wr_at46Stdlib6ZArith6BinInt1Zhl96of_nathl93mulk14Somek14consk13nil3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshp6dov_read_bytes89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr8WithSegs~~~~~~hte5u8arrue2wa36Stdlib5Lists4Listiif9nth_errorhl93addhl92lehl96to_nathte4u8rok14boolk14truehp68store_okhl92lthp6cwrite_to_memq03updmf2exue3le4hte6u32arrue3le8hte6u64arrmf2orhl93pow79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~it54cellit52CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~jhf8rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~jm6ddisjoint_fromjm63ivljm65munchjm65wmono3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypejsc7Segment" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Fixpoint u32s (ws : list word) : list byte :=
  match ws with [] => [] | w :: ws' => le4 w ++ u32s ws' end.
Fixpoint u64s (ws : list word) : list byte :=
  match ws with [] => [] | w :: ws' => le8 w ++ u64s ws' end.

Lemma u32s_length : ltac2:(zQ "80!h9!jc!l9!m2!m9!o3!pa!ta>2ws@1$3@1$1@1$0#k0@3$5$4@2$2@1$1@1$0#8@1$7^1@2$6N4@2$2@1$1@1$0#k0^1").
Proof. induction ws; cbn -[le4]; [reflexivity|]. rewrite app_length, length_le4, IHws. lia. Qed.
Lemma u64s_length : ltac2:(zQ "80!h9!jc!l9!m2!m9!o3!pa!u1>2ws@1$3@1$1@1$0#k0@3$5$4@2$2@1$1@1$0#8@1$7^1@2$6N8@2$2@1$1@1$0#k0^1").
Proof. induction ws; cbn -[le8]; [reflexivity|]. rewrite app_length, length_le8, IHws. lia. Qed.

Lemma u32s_app : ltac2:(zQ "60!h9!jc!m2!ta!u8!o3>1a@1$2@1$1@1$0#k0>1b@1$2@1$1@1$0#k0@3$5@1$2@1$1@1$0#8@1$3@3$4@1$1@1$0#k0^2^1@3$4@1$1@1$0#8@1$3^2@1$3^1").
Proof. induction a; intros; cbn -[le4]; [reflexivity|]. rewrite IHa, app_assoc. reflexivity. Qed.
Lemma u64s_app : ltac2:(zQ "60!h9!jc!m2!u1!u8!o3>1a@1$2@1$1@1$0#k0>1b@1$2@1$1@1$0#k0@3$5@1$2@1$1@1$0#8@1$3@3$4@1$1@1$0#k0^2^1@3$4@1$1@1$0#8@1$3^2@1$3^1").
Proof. induction a; intros; cbn -[le8]; [reflexivity|]. rewrite IHa, app_assoc. reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint upd {X} (l : list X) (i : nat) (x : X) : list X :=
  match l, i with
  | [], _ => []
  | _ :: l', O => x :: l'
  | y :: l', S i' => y :: upd l' i' x
  end.

Lemma upd_length : forall {X} (l : list X) i x, length (upd l i x) = length l.
Proof. induction l; intros [|i] x; cbn; auto. Qed.

Lemma upd_app_split : forall {X} (l : list X) i x, (i < length l)%nat ->
  exists pre y post, l = pre ++ y :: post /\ length pre = i /\ upd l i x = pre ++ x :: post.
Proof.
  induction l as [|z l IH]; intros i x Hi; cbn in Hi; [lia|].
  destruct i as [|i].
  - exists [], z, l. repeat split; reflexivity.
  - destruct (IH i x ltac:(lia)) as (pre & y & post & E & Hlen & Hupd).
    exists (z :: pre), y, post. split; [rewrite E at 1; reflexivity|]. split; [cbn; lia|].
    cbn. rewrite Hupd. reflexivity.
Qed.

Lemma nth_error_split : forall {X} (l : list X) i y, nth_error l i = Some y ->
  exists pre post, l = pre ++ y :: post /\ length pre = i.
Proof.
  induction l as [|z l IH]; intros [|i] y H; cbn in H; try discriminate.
  - inversion H; subst. exists [], l. split; reflexivity.
  - destruct (IH i y H) as (pre & post & -> & Hlen). exists (z :: pre), post. split; [reflexivity| cbn; lia].
Qed.

Lemma nth_error_lt : forall {X} (l : list X) i y, nth_error l i = Some y -> (i < length l)%nat.
Proof. intros X l i y H. apply nth_error_Some. rewrite H. discriminate. Qed.

Lemma upd_bytes_mid : ltac2:(zQ "80!h9!jc!m2!u8!l9!o3!m9!hi8>1a@1$2@1$1@1$0#8>1b@1$2@1$1@1$0#8>1c@1$2@1$1@1$0#8>2bs@1$2@1$1@1$0#8>0@3$5$6@2$4@1$1@1$0#8^1@2$4@1$1@1$0#8^3@3$5@1$2@1$1@1$0#8@3$7@3$3@1$1@1$0#8^5@3$3@1$1@1$0#8^4^3@2$4@1$1@1$0#8^5^2@3$3@1$1@1$0#8^5@3$3@1$1@1$0#8^2^3").
Proof.
  intros a b c bs H. unfold upd_bytes.
  rewrite firstn_app, firstn_all2, Nat.sub_diag, firstn_O, app_nil_r by lia.
  rewrite skipn_app, skipn_all2 by lia. cbn [app].
  replace (length a + length bs - length a)%nat with (length b) by lia.
  rewrite skipn_app, skipn_all2, Nat.sub_diag by lia. reflexivity.
Qed.

Section WithSegs.
Variable segs : ltac2:(zQ "20!m2!kg1@1$0$1").

Definition u8arr : ltac2:(zQ "50!h9!jc!m2!hj4!hjd>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1A$4>2bs@1$2@1$1@1$0#8P") := ltac2:(zQ "a0!h9!jc!l9!m2!hj4!hk0!hjd!hk6!hl1!hn1\1m>0@1$1@1$0#k0@1$4@1$1@1$0#8\1A$6\2bs@1$3@1$1@1$0#8@2$5@4$7?4segs^3^2^1@4$8?4segs^3^2@1$9@2$2@1$1@1$0#8^1").
Definition u32arr : ltac2:(zQ "50!h9!jc!m2!hj4!hjd>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1A$4>2ws@1$2@1$1@1$0#k0P") := ltac2:(zQ "c0!h9!jc!l9!m2!hj4!hk0!hjd!ta!hk6!hl1!hnb!hn1\1m>0@1$1@1$0#k0@1$4@1$1@1$0#8\1A$6\2ws@1$3@1$1@1$0#k0@2$5@4$8?4segs^3^2@1$7^1@4$9?4segs^3^2@2$a+4@1$b@2$2@1$1@1$0#k0^1").
Definition u64arr : ltac2:(zQ "50!h9!jc!m2!hj4!hjd>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1A$4>2ws@1$2@1$1@1$0#k0P") := ltac2:(zQ "c0!h9!jc!l9!m2!hj4!hk0!hjd!u1!hk6!hl1!hnb!hn1\1m>0@1$1@1$0#k0@1$4@1$1@1$0#8\1A$6\2ws@1$3@1$1@1$0#k0@2$5@4$8?4segs^3^2@1$7^1@4$9?4segs^3^2@2$a+8@1$b@2$2@1$1@1$0#k0^1").

(* [comment removed for export] *)
Definition u8ro : ltac2:(zQ "50!h9!jc!m2!hj4!hjd>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1A$4>2bs@1$2@1$1@1$0#8P") := ltac2:(zQ "60!h9!jc!m2!hj4!hjd!hk6\1m>0@1$1@1$0#k0@1$3@1$1@1$0#8\1A$4\2bs@1$2@1$1@1$0#8@4$5?4segs^3^2^1").

(* [comment removed for export] *)
Lemma u8arr_read : ltac2:(zQ "h00!h9!jc!m2!hj4!o3!ho2!hjd!ho9!hp0!hsd!ii1!iia!ik2!ikf!il6!ilc>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1A$6>2bs@1$2@1$1@1$0#8>1i$6>1b@1$1@1$0#8>1a@1$1@1$0#k0>0@3$a^6^5^4>0@3$4@1$3@1$1@1$0#8@3$c@1$1@1$0#8^5@1$f^4@2$5@1$1@1$0#8^3>0@2$eZ^5>0@3$4@1$1@1$0#k0^4@1$b@2$d^8^6@3$4@1$3@1$2@1$1@1$0#8@4$9?4segs^a^5N1@2$5@1$2@1$1@1$0#8@3$7@1$1@1$0#8^6@1$8@1$1@1$0#8").
Proof.
  intros m A bs i b a [Hb _] Hn Hi ->.
  pose proof (nth_error_lt _ _ _ Hn).
  rewrite (bytes_at_read segs m A bs i 1 Hb) by lia.
  destruct (nth_error_split _ _ _ Hn) as (pre & post & E & Hlen). rewrite E at 1.
  rewrite skipn_app, skipn_all2, Hlen, Nat.sub_diag by lia. reflexivity.
Qed.

Lemma u8ro_read : ltac2:(zQ "h00!h9!jc!m2!hj4!o3!ho2!hjd!ho9!hp0!hsd!im6!iia!ik2!ikf!il6!ilc>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1A$6>2bs@1$2@1$1@1$0#8>1i$6>1b@1$1@1$0#8>1a@1$1@1$0#k0>0@3$a^6^5^4>0@3$4@1$3@1$1@1$0#8@3$c@1$1@1$0#8^5@1$f^4@2$5@1$1@1$0#8^3>0@2$eZ^5>0@3$4@1$1@1$0#k0^4@1$b@2$d^8^6@3$4@1$3@1$2@1$1@1$0#8@4$9?4segs^a^5N1@2$5@1$2@1$1@1$0#8@3$7@1$1@1$0#8^6@1$8@1$1@1$0#8").
Proof.
  intros m A bs i b a Hb Hn Hi ->.
  pose proof (nth_error_lt _ _ _ Hn).
  rewrite (bytes_at_read segs m A bs i 1 Hb) by lia.
  destruct (nth_error_split _ _ _ Hn) as (pre & post & E & Hlen). rewrite E at 1.
  rewrite skipn_app, skipn_all2, Hlen, Nat.sub_diag by lia. reflexivity.
Qed.

Lemma u8arr_store_ok : ltac2:(zQ "h10!h9!jc!o3!hjd!ime!l9!m2!hj4!in5!hk0!inc!ii1!iia!ikf!il6!io8!hn1>1m>0@1$1@1$0#k0@1$7@1$1@1$0#8>1A$3>2bs@1$6@1$1@1$0#8>1i$3>1a@1$1@1$0#k0>0@3$b^5^4^3>0@2$9@2$eZ^3@2$f^3@1$h0@2$5@1$1@1$0#8^4>0@3$2@1$1@1$0#k0^3@1$c@2$d^6^4@3$2$4@4$a?4segs^8^4N1$8").
Proof. intros m A bs i a [_ Hw] Hi ->. eapply wr_at_store_ok; eauto; lia. Qed.

Lemma u8arr_write : ltac2:(zQ "h20!h9!jc!hjd!ii1!ho9!l9!m2!hp0!hj4!hk0!ioe!ipe!iia!ikf!il6!io8!hn1!ilc>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>1A$2>2bs@1$6@1$1@1$0#8>1i$2>1b@1$1@1$0#8>0@3$3^5^4^3>0@2$9@2$eZ^3@2$f^3@1$h0@2$5@1$1@1$0#8^4@3$3@3$a^7@1$c@2$d^6^4@3$4@1$1@1$0#8^3@1$7@1$1@1$0#8^6@4$b@1$1@1$0#8^5@1$h1^4^3").
Proof.
  intros m A bs i b [Hb Hw] Hi. split.
  - eapply bytes_at_ext. { apply (bytes_at_write_inside segs m A bs i [b] Hb); [lia| cbn; lia]. }
    destruct (upd_app_split bs (Z.to_nat i) b ltac:(lia)) as (pre & y & post & E & Hlen & Hupd).
    rewrite Hupd. rewrite E at 1. unfold upd_bytes. rewrite firstn_app, firstn_all2, Hlen, Nat.sub_diag by lia. cbn.
    rewrite app_nil_r. f_equal. change (y :: post) with ([y] ++ post). rewrite app_assoc, skipn_app.
    rewrite skipn_all2 by (rewrite app_length, Hlen; cbn; lia). rewrite app_length, Hlen. cbn.
    replace (Z.to_nat i + 1 - (Z.to_nat i + 1))%nat with 0%nat by lia. reflexivity.
  - rewrite upd_length. apply wr_at_write. exact Hw.
Qed.

(* [comment removed for export] *)
Lemma u32s_split : ltac2:(zQ "h00!h9!jc!m2!o3!ta!u8!m9!hk0!l9!iq4!ho2!ho9!hj4!pa!iq9!ik2>2ws@1$2@1$1@1$0#k0>1i$6>1w@1$1@1$0#k0>0@3$3@1$c@1$1@1$0#k0@3$f@1$1@1$0#k0^3^2@2$a@1$1@1$0#k0^1@2$9@1$2@1$1@1$0#k0\3pre@1$2@1$1@1$0#k0@2$9@1$2@1$1@1$0#k0\4post@1$2@1$1@1$0#k0@2$7@3$3@1$2@1$1@1$0#k0^6@3$5@1$1@1$0#k0^2@3$b@1$1@1$0#k0^4^1@2$7@3$3$6@2$8@1$1@1$0#k0^2^5@2$7@3$3@1$2@1$1@1$0#8@1$4^6@3$5@1$1@1$0#8@1$4^2@3$5@1$1@1$0#8@1$e^4@1$4^1@3$3$6@2$8@1$1@1$0#8@1$4^2@2$dN4^5").
Proof.
  intros ws i w H. destruct (nth_error_split _ _ _ H) as (pre & post & -> & Hlen).
  exists pre, post. rewrite u32s_app. cbn -[le4]. rewrite u32s_length. repeat split; lia.
Qed.

Lemma u32arr_read : ltac2:(zQ "h00!h9!jc!m2!hj4!o3!ho2!hjd!hsd!iqf!iq9!iia!ik2!ikf!il6!hnb!ilc>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1A$6>2ws@1$2@1$1@1$0#k0>1i$6>1w@1$1@1$0#k0>1a@1$1@1$0#k0>0@3$8^6^5^4>0@3$4@1$3@1$1@1$0#k0@3$b@1$1@1$0#k0^5@1$f^4@2$5@1$1@1$0#k0^3>0@2$dZ^5>0@3$4@1$1@1$0#k0^4@1$a@2$c^8@2$e+4^6@3$4@1$3@1$2@1$1@1$0#8@4$7?4segs^a^5N4@2$5@1$2@1$1@1$0#8@1$9^6").
Proof.
  intros m A ws i w a [Hb _] Hn Hi ->.
  destruct (u32s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (4 * i)%Z with (Z.of_nat (4 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read segs m A (u32s ws) (4 * Z.to_nat i) 4 Hb).
  2:{ rewrite Eu, !app_length, length_le4, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le4; lia).
  rewrite length_le4, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma u64s_split : ltac2:(zQ "h00!h9!jc!m2!o3!u1!u8!m9!hk0!l9!iq4!ho2!ho9!hj4!pa!ir9!ik2>2ws@1$2@1$1@1$0#k0>1i$6>1w@1$1@1$0#k0>0@3$3@1$c@1$1@1$0#k0@3$f@1$1@1$0#k0^3^2@2$a@1$1@1$0#k0^1@2$9@1$2@1$1@1$0#k0\3pre@1$2@1$1@1$0#k0@2$9@1$2@1$1@1$0#k0\4post@1$2@1$1@1$0#k0@2$7@3$3@1$2@1$1@1$0#k0^6@3$5@1$1@1$0#k0^2@3$b@1$1@1$0#k0^4^1@2$7@3$3$6@2$8@1$1@1$0#k0^2^5@2$7@3$3@1$2@1$1@1$0#8@1$4^6@3$5@1$1@1$0#8@1$4^2@3$5@1$1@1$0#8@1$e^4@1$4^1@3$3$6@2$8@1$1@1$0#8@1$4^2@2$dN8^5").
Proof.
  intros ws i w H. destruct (nth_error_split _ _ _ H) as (pre & post & -> & Hlen).
  exists pre, post. rewrite u64s_app. cbn -[le8]. rewrite u64s_length. repeat split; lia.
Qed.

Lemma u64arr_read : ltac2:(zQ "h00!h9!jc!m2!hj4!o3!ho2!hjd!hsd!irf!ir9!iia!ik2!ikf!il6!hnb!ilc>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1A$6>2ws@1$2@1$1@1$0#k0>1i$6>1w@1$1@1$0#k0>1a@1$1@1$0#k0>0@3$8^6^5^4>0@3$4@1$3@1$1@1$0#k0@3$b@1$1@1$0#k0^5@1$f^4@2$5@1$1@1$0#k0^3>0@2$dZ^5>0@3$4@1$1@1$0#k0^4@1$a@2$c^8@2$e+8^6@3$4@1$3@1$2@1$1@1$0#8@4$7?4segs^a^5N8@2$5@1$2@1$1@1$0#8@1$9^6").
Proof.
  intros m A ws i w a [Hb _] Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read segs m A (u64s ws) (8 * Z.to_nat i) 8 Hb).
  2:{ rewrite Eu, !app_length, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
  rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

Lemma u64arr_store_ok : ltac2:(zQ "h20!h9!jc!o3!hjd!ime!l9!m2!hj4!in5!hk0!inc!irf!iia!ikf!il6!io8!hnb!hn1>1m>0@1$1@1$0#k0@1$7@1$1@1$0#8>1A$3>2ws@1$6@1$1@1$0#k0>1i$3>1a@1$1@1$0#k0>0@3$b^5^4^3>0@2$9@2$eZ^3@2$f^3@1$h1@2$5@1$1@1$0#k0^4>0@3$2@1$1@1$0#k0^3@1$c@2$d^6@2$h0+8^4@3$2$4@4$a?4segs^8^4N8$8").
Proof. intros m A ws i a [_ Hw] Hi ->. eapply wr_at_store_ok; eauto; lia. Qed.

Lemma u64arr_write : ltac2:(zQ "h20!h9!jc!hjd!irf!l9!m2!hj4!hk0!ioe!ipe!ir9!iia!ikf!il6!io8!hnb!hn1!ilc>1m>0@1$1@1$0#k0@1$6@1$1@1$0#8>1A$2>2ws@1$5@1$1@1$0#k0>1i$2>1v@1$1@1$0#k0>0@3$3^5^4^3>0@2$7@2$dZ^3@2$e^3@1$h0@2$4@1$1@1$0#k0^4@3$3@3$8^7@1$b@2$c^6@2$f+8^4@1$a^3^6@4$9@1$1@1$0#k0^5@1$h1^4^3").
Proof.
  intros m A ws i v [Hb Hw] Hi.
  destruct (upd_app_split ws (Z.to_nat i) v ltac:(lia)) as (pre & y & post & E & Hlen & Hupd).
  split.
  - eapply bytes_at_ext.
    { apply (bytes_at_write_inside segs m A (u64s ws) (8 * i) (le8 v) Hb); [lia|].
      rewrite length_le8, u64s_length. lia. }
    rewrite Hupd, E, !u64s_app. cbn [u64s].
    replace (Z.to_nat (8 * i)) with (length (u64s pre)) by (rewrite u64s_length; lia).
    apply upd_bytes_mid. rewrite !length_le8. reflexivity.
  - rewrite upd_length. apply wr_at_write. exact Hw.
Qed.

(* [comment removed for export] *)
Lemma u8arr_frame : ltac2:(zQ "e0!h9!jc!il6!l9!ikf!hn1!m2!hjd!ii1!hj4!is9!ioe!iia!ise>1m>0@1$1@1$0#k0@1$9@1$1@1$0#8>1A$7>2bs@1$6@1$1@1$0#8>1a$7>2xs@1$6@1$1@1$0#8>0@3$8^5^4^3>0@2$2Z^3>0@2$2@2$4^4@1$5@2$3@1$1@1$0#8^3@2$d+2+k0>0@2$a@2$2@2$4^7@1$5@2$3@1$1@1$0#8^6^5@2$2@2$4^5@1$5@2$3@1$1@1$0#8^4^7@3$8@3$b^9@1$c^6^5^8^7").
Proof. intros m A bs a xs [Hb Hw] ? ? ?. split; [apply bytes_at_write_other; assumption| apply wr_at_write; assumption]. Qed.

Lemma u32arr_frame : ltac2:(zQ "f0!h9!jc!il6!l9!ikf!hn1!m2!hjd!iqf!hj4!is9!ioe!iia!hnb!ise>1m>0@1$1@1$0#k0@1$9@1$1@1$0#8>1A$7>2ws@1$6@1$1@1$0#k0>1a$7>2xs@1$6@1$1@1$0#8>0@3$8^5^4^3>0@2$2Z^3>0@2$2@2$4^4@1$5@2$3@1$1@1$0#8^3@2$e+2+k0>0@2$a@2$2@2$4^7@2$d+4@1$5@2$3@1$1@1$0#k0^6^5@2$2@2$4^5@1$5@2$3@1$1@1$0#8^4^7@3$8@3$b^9@1$c^6^5^8^7").
Proof.
  intros m A ws a xs [Hb Hw] ? ? ?. split; [|apply wr_at_write; assumption].
  apply bytes_at_write_other; try assumption. rewrite u32s_length. lia.
Qed.

Lemma u64arr_frame : ltac2:(zQ "f0!h9!jc!il6!l9!ikf!hn1!m2!hjd!irf!hj4!is9!ioe!iia!hnb!ise>1m>0@1$1@1$0#k0@1$9@1$1@1$0#8>1A$7>2ws@1$6@1$1@1$0#k0>1a$7>2xs@1$6@1$1@1$0#8>0@3$8^5^4^3>0@2$2Z^3>0@2$2@2$4^4@1$5@2$3@1$1@1$0#8^3@2$e+2+k0>0@2$a@2$2@2$4^7@2$d+8@1$5@2$3@1$1@1$0#k0^6^5@2$2@2$4^5@1$5@2$3@1$1@1$0#8^4^7@3$8@3$b^9@1$c^6^5^8^7").
Proof.
  intros m A ws a xs [Hb Hw] ? ? ?. split; [|apply wr_at_write; assumption].
  apply bytes_at_write_other; try assumption. rewrite u64s_length. lia.
Qed.

Lemma u8arr_bound : ltac2:(zQ "c0!h9!jc!il6!l9!m2!hj4!hk0!hjd!ii1!ikf!hn1!ise>1m>0@1$1@1$0#k0@1$5@1$1@1$0#8>1A$7>2bs@1$4@1$1@1$0#8>0@3$8^3^2^1@2$6@2$2Z^3@2$2@2$9^3@1$a@2$3@1$1@1$0#8^2@2$b+2+k0").
Proof. intros m A bs [Hb _]. eapply bytes_at_bound; eauto. Qed.
Lemma u32arr_bound : ltac2:(zQ "d0!h9!jc!il6!l9!m2!hj4!hk0!hjd!iqf!ikf!hnb!hn1!ise>1m>0@1$1@1$0#k0@1$5@1$1@1$0#8>1A$7>2ws@1$4@1$1@1$0#k0>0@3$8^3^2^1@2$6@2$2Z^3@2$2@2$9^3@2$a+4@1$b@2$3@1$1@1$0#k0^2@2$c+2+k0").
Proof. intros m A ws [Hb _]. pose proof (bytes_at_bound _ _ _ _ Hb). rewrite u32s_length in H. lia. Qed.
Lemma u64arr_bound : ltac2:(zQ "d0!h9!jc!il6!l9!m2!hj4!hk0!hjd!irf!ikf!hnb!hn1!ise>1m>0@1$1@1$0#k0@1$5@1$1@1$0#8>1A$7>2ws@1$4@1$1@1$0#k0>0@3$8^3^2^1@2$6@2$2Z^3@2$2@2$9^3@2$a+8@1$b@2$3@1$1@1$0#k0^2@2$c+2+k0").
Proof. intros m A ws [Hb _]. pose proof (bytes_at_bound _ _ _ _ Hb). rewrite u64s_length in H. lia. Qed.

Lemma u8ro_frame : ltac2:(zQ "e0!h9!jc!il6!l9!ikf!hn1!m2!hjd!im6!hj4!is9!ioe!iia!ise>1m>0@1$1@1$0#k0@1$9@1$1@1$0#8>1A$7>2bs@1$6@1$1@1$0#8>1a$7>2xs@1$6@1$1@1$0#8>0@3$8^5^4^3>0@2$2Z^3>0@2$2@2$4^4@1$5@2$3@1$1@1$0#8^3@2$d+2+k0>0@2$a@2$2@2$4^7@1$5@2$3@1$1@1$0#8^6^5@2$2@2$4^5@1$5@2$3@1$1@1$0#8^4^7@3$8@3$b^9@1$c^6^5^8^7").
Proof. intros m A bs a xs Hb ? ? ?. unfold u8ro. apply bytes_at_write_other; assumption. Qed.

(* [comment removed for export] *)
Lemma u8arr_of_rw_cells : ltac2:(zQ "c0!h9!jc!jh1!ho9!m2!m9!hp0!hj4!hjd!ii1!jh9!jla>1m>0@1$1@1$0#k0@1$7@1$1@1$0#8>1A$8>1n$5>2bs@1$4@1$1@1$0#8>0@4$b?4segs^4^3@3$3$2@2$a^2^1@1$6$2@3$9^5^4^2").
Proof.
  intros m A n bs [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as [Hn _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw. subst n.
  split; assumption.
Qed.

Lemma rw_cells_of_u8arr : ltac2:(zQ "c0!h9!jc!jh1!ho9!l9!m2!hp0!hj4!hjd!ii1!jh9!jla>1m>0@1$1@1$0#k0@1$7@1$1@1$0#8>1A$8>2bs@1$5@1$1@1$0#8>0@3$9^3^2^1@4$b?4segs^4^3@3$3$2@2$a@2$4@1$1@1$0#8^2^2@1$6$2").
Proof.
  intros m A bs [Hb Hw]. split.
  - split. { cbn. split; [reflexivity|exact I]. }
    cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma u8arr_transport : ltac2:(zQ "c1!h9!jc!m2!hj4!ii1!l9!hjd!jq2!jr3!jra!js3!hn1&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1W@1$2$8>1m~0>2m'~0>1A$6>2bs@1$2@1$1@1$0#8>0@3$4^4^2^1>0@3$9^6^5^4>0@3$a?4segs^6^5>0@3$7^8^5@1$b@2$5@1$1@1$0#8^4@3$4^7^6^5").
Proof.
  intros W m m' A bs [Hb Hw] MU WM Hd. split.
  - eapply bytes_at_transport; eauto.
  - eapply wr_at_transport; eauto.
Qed.
Lemma u32arr_transport : ltac2:(zQ "d1!h9!jc!m2!hj4!iqf!l9!hjd!jq2!jr3!jra!js3!hnb!hn1&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1W@1$2$8>1m~0>2m'~0>1A$6>2ws@1$2@1$1@1$0#k0>0@3$4^4^2^1>0@3$9^6^5^4>0@3$a?4segs^6^5>0@3$7^8^5@2$b+4@1$c@2$5@1$1@1$0#k0^4@3$4^7^6^5").
Proof.
  intros W m m' A ws [Hb Hw] MU WM Hd. split.
  - eapply bytes_at_transport; eauto. rewrite u32s_length, Nat2Z.inj_mul. exact Hd.
  - eapply wr_at_transport; eauto.
Qed.
Lemma u64arr_transport : ltac2:(zQ "d1!h9!jc!m2!hj4!irf!l9!hjd!jq2!jr3!jra!js3!hnb!hn1&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1W@1$2$8>1m~0>2m'~0>1A$6>2ws@1$2@1$1@1$0#k0>0@3$4^4^2^1>0@3$9^6^5^4>0@3$a?4segs^6^5>0@3$7^8^5@2$b+8@1$c@2$5@1$1@1$0#k0^4@3$4^7^6^5").
Proof.
  intros W m m' A ws [Hb Hw] MU WM Hd. split.
  - eapply bytes_at_transport; eauto. rewrite u64s_length, Nat2Z.inj_mul. exact Hd.
  - eapply wr_at_transport; eauto.
Qed.
Lemma u8ro_transport : ltac2:(zQ "b1!h9!jc!m2!hj4!im6!l9!hjd!jq2!jr3!jra!hn1&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1W@1$2$8>1m~0>2m'~0>1A$6>2bs@1$2@1$1@1$0#8>0@3$4^4^2^1>0@3$9^6^5^4>0@3$7^7^4@1$a@2$5@1$1@1$0#8^3@3$4^6^5^4").
Proof. intros W m m' A bs Hb MU Hd. eapply bytes_at_transport; eauto. Qed.

End WithSegs.
(* [comment removed for export] *)
