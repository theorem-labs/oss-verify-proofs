(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import PropExec MState Mem.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes03nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hd4cell37Corelib7Numbers7BinNumsm04Npos35stdpp9bitvectorbdefinitionso02bv04list04cons03nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~r33le2r33le4r33le837Corelib4Init5Logicvf4True06lengthvf2eqhd6cbyteshd7cell_wfhd5csizehdbcells_byteshdacells_sizehd8cells_wf03appvf3andvf3iff37Corelib4Init3Nathn93addvf2ex04Some06optionhd7cell_athd8cell_updm01Zr38bytes_at3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshs9dov_read_bytes89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells8WithSegs~~~~~~ih18cells_atr32wa46Stdlib6ZArith6BinInt1Zim73addim76of_naths9cwrite_to_memim72levf2orim73pow37Corelib5Lists7ListDefir26firstnir25skipn37Corelib4Init5Peanoitc2le04boolhd2CBhn93sub46Stdlib5Arith8PeanoNat3Natjg83eqbhd9cb_pieceshd8cb_split04truehdbcb_split_okhd8cells_at3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypejm07Segment" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Inductive cell : Type :=
| C8 (v : word)            (* [comment removed for export] *)
| C4 (v : word)            (* [comment removed for export] *)
| C2 (v : word)            (* [comment removed for export] *)
| C1 (b : byte)            (* [comment removed for export] *)
| CB (n : nat) (bs : list byte).  (* [comment removed for export] *)

Definition csize : ltac2:(zQ "20!h8!l9>1c$1$0") := ltac2:(zQ "50!n9!pd!l9!h8!q2\1c$2M2\1c$2$3^1\1v@1$1@1$0#k0N8\1v@1$1@1$0#k0N4\1v@1$1@1$0#k0N2\1b@1$1@1$0#8N1\1n$3\2bs@1$4@1$1@1$0#8^2").
Definition cbytes : ltac2:(zQ "40!q2!n9!l9!pd>1c$2@1$0@1$3@1$1#8") := ltac2:(zQ "a0!n9!pd!l9!q2!q8!h8!qe!ud!v3!v9\1c$2M2\1c$2@1$3@1$1@1$0#8^1\1v@1$1@1$0#k0@1$9^1\1v@1$1@1$0#k0@1$8^1\1v@1$1@1$0#k0@1$7^1\1b@1$1@1$0#8@3$4@1$1@1$0#8^1@1$6@1$1@1$0#8\1n$5\2bs@1$3@1$1@1$0#8^1").
Fixpoint cells_size (cs : list cell) : nat :=
  match cs with [] => 0 | c :: cs' => csize c + cells_size cs' end.
Fixpoint cells_bytes (cs : list cell) : list byte :=
  match cs with [] => [] | c :: cs' => cbytes c ++ cells_bytes cs' end.
Definition cell_wf : ltac2:(zQ "10!l9>1c$0P") := ltac2:(zQ "80!n9!pd!hh3!l9!h8!hha!q2!hi2\1c$3M3\1c$3P^1\1v@1$1@1$0#k0$2\1v@1$1@1$0#k0$2\1v@1$1@1$0#k0$2\1b@1$1@1$0#8$2\1n$4\2bs@1$6@1$1@1$0#8@3$7$4@2$5@1$1@1$0#8^1^2").
Fixpoint cells_wf (cs : list cell) : Prop :=
  match cs with [] => True | c :: cs' => cell_wf c /\ cells_wf cs' end.

Lemma cbytes_length : ltac2:(zQ "90!hha!h8!hi2!n9!hi7!l9!hj0!hja!pd>1c$5>0@1$6^1@3$2$1@2$0@1$8@1$3#8@1$4^2@1$7^2").
Proof.
  intros [v|v|v|b|n bs] H; cbn -[le8 le4 le2].
  - apply length_le8. - apply length_le4. - apply length_le2. - reflexivity. - exact H.
Qed.

Lemma cells_bytes_length : ltac2:(zQ "a0!hha!q2!h8!hi2!n9!l9!hk2!hl0!hld!pd>2cs@1$1$5>0@1$8^1@3$3$2@2$0@1$9@1$4#8@1$6^2@1$7^2").
Proof.
  induction cs as [|c cs IH]; intros H; [reflexivity|].
  cbn [cells_bytes cells_size]. destruct H as [H1 H2]. rewrite app_length, cbytes_length, IH by assumption. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint cell_at (cs : list cell) (k : nat) : option cell :=
  match cs with
  | [] => None
  | c :: cs' => if Nat.eqb k 0 then Some c
                else if Nat.ltb k (csize c) then None
                else cell_at cs' (k - csize c)
  end.

Fixpoint cell_upd (cs : list cell) (k : nat) (c' : cell) : list cell :=
  match cs with
  | [] => []
  | c :: cs' => if Nat.eqb k 0 then c' :: cs'
                else c :: cell_upd cs' (k - csize c) c'
  end.

Lemma cells_wf_app : ltac2:(zQ "60!l9!hld!q2!hm8!hmd!hn3>1a@1$2$0>1b@1$2$0@2$5@1$1@3$3$0^2^1@2$4@1$1^2@1$1^1").
Proof. induction a as [|c a IH]; intros b; cbn; [tauto|]. rewrite IH. tauto. Qed.
Lemma cells_bytes_app : ltac2:(zQ "70!q2!l9!hk2!hm8!n9!pd!hi2>1a@1$0$1>1b@1$0$1@3$6@1$0@1$5@1$4#8@1$2@3$3$1^2^1@3$3@1$5@1$4#8@1$2^2@1$2^1").
Proof. induction a; intros; cbn; [reflexivity|]. rewrite IHa, app_assoc. reflexivity. Qed.
Lemma cells_size_app : ltac2:(zQ "70!l9!hl0!q2!hm8!h8!hi2!hob>1a@1$2$0>1b@1$2$0@3$5$4@1$1@3$3$0^2^1@2$6@1$1^2@1$1^1").
Proof. induction a; intros; cbn; [reflexivity|]. rewrite IHa. lia. Qed.

Lemma cell_at_split : ltac2:(zQ "d0!l9!q2!hi2!hm8!q8!h8!hmd!hp2!hp7!hpd!hq5!hqf!hl0>2cs@1$1$0>1k$5>1c$0>2c'$0>0@3$2@1$9$0@2$a^4^3@2$8$0^2@2$7@1$1$0\3pre@1$1$0@2$7@1$1$0\4post@1$1$0@2$6@3$2@1$1$0^7@3$3$0^2@3$4$0^5^1@2$6@3$2$5@1$c^2^6@3$2@1$1$0@3$b^7^6^4@3$3$0^2@3$4$0^4^1").
Proof.
  induction cs as [|c0 cs IH]; intros k c c' H; [discriminate|].
  cbn [cell_at cell_upd] in *. destruct (Nat.eqb_spec k 0).
  - inversion H; subst. exists [], cs. repeat split; auto.
  - destruct (Nat.ltb_spec0 k (csize c0)); [discriminate|].
    destruct (IH _ _ c' H) as (pre & post & -> & Hsz & Hupd).
    exists (c0 :: pre), post. repeat split; auto.
    + cbn. lia.
    + cbn. rewrite Hupd. reflexivity.
Qed.

Lemma skipn_app_exact : forall {X} (a b : list X), skipn (length a) (a ++ b) = b.
Proof. intros X a b. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. Qed.
Lemma firstn_app_exact : forall {X} (a b : list X), firstn (length a) (a ++ b) = a.
Proof. intros X a b. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn. apply app_nil_r. Qed.

Section WithSegs.
Variable segs : ltac2:(zQ "20!q2!jp5@1$0$1").

Definition cells_at : ltac2:(zQ "60!n9!pd!q2!hpd!hra!l9>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1A$4>2cs@1$2$5P") := ltac2:(zQ "a0!n9!pd!q2!hpd!hmd!hra!l9!hk2!hld!hre\1m>0@1$1@1$0#k0@1$3@1$1@1$0#8\1A$5\2cs@1$2$6@2$4@1$8^1@4$9?4segs^3^2@1$7^1").

Lemma cells_at_read : ltac2:(zQ "h10!n9!l9!pd!q2!hpd!hp7!hi2!h8!hra!ig0!il6!hi7!hq5!hja!im2!inf!io6>1m>0@1$2@1$0#k0@1$4@1$2@1$0#8>1A$8>2cs@1$3$1>1k$7>1c$1>0@3$a^5^4^3>0@3$6@1$4$1@2$c^4^3@2$5$1^2@3$6@1$4@1$3@1$2@1$0#8@4$9?4segs^7@1$e@2$f^6@1$h0^4@1$d^3@2$5@1$3@1$2@1$0#8@1$b^3").
Proof.
  intros m A cs k c [Hwf Hb] Hc.
  destruct (cell_at_split _ _ _ c Hc) as (pre & post & Ecs & Hsz & _).
  rewrite Ecs in Hwf, Hb. apply cells_wf_app in Hwf. destruct Hwf as [Hwpre [Hwc Hwpost]].
  rewrite cells_bytes_app in Hb. cbn [cells_bytes] in Hb.
  apply bytes_at_app in Hb. destruct Hb as [_ Hb].
  rewrite cells_bytes_length in Hb by assumption. rewrite Hsz in Hb.
  apply bytes_at_app in Hb. destruct Hb as [Hb _].
  rewrite <- (cbytes_length c) by assumption.
  rewrite <- (Z.add_0_r (A + Z.of_nat k)). change 0%Z with (Z.of_nat 0).
  rewrite (bytes_at_ov_read segs _ _ _ 0 (length (cbytes c)) Hb) by lia.
  cbn [skipn]. rewrite firstn_all. reflexivity.
Qed.

Lemma cells_at_write : ltac2:(zQ "h30!l9!h8!hpd!hi2!n9!il6!hja!pd!hp7!q2!hra!ip0!hi7!hq5!hqf!hj0!im2!inf!io6>1m>0@1$7@1$4#k0@1$2@1$7@1$4#8>1A$a>2cs@1$9$0>1k$1>1c$0>2c'$0>0@3$5^6^5^4>0@3$3@1$2$0@2$d^5^4@2$8$0^3>0@3$3$1@1$6^3@1$6^4>0@1$f^4@3$5@3$b^a@1$h0@2$h1^9@1$h2^7@1$c^5^9@3$e^8^7^5").
Proof.
  intros m A cs k c c' [Hwf Hb] Hc Hsz Hwf'.
  destruct (cell_at_split _ _ _ c' Hc) as (pre & post & Ecs & Hszp & Hupd).
  rewrite Hupd. rewrite Ecs in Hwf, Hb. apply cells_wf_app in Hwf. destruct Hwf as [Hwpre [Hwc Hwpost]].
  split. { apply cells_wf_app. cbn. tauto. }
  rewrite cells_bytes_app in *. cbn [cells_bytes] in *.
  pose proof (cells_bytes_length pre Hwpre) as Lpre.
  pose proof (cbytes_length c Hwc) as Lc. pose proof (cbytes_length c' Hwf') as Lc'.
  replace (A + Z.of_nat k)%Z with (A + Z.of_nat (length (cells_bytes pre)))%Z by (rewrite Lpre, Hszp; reflexivity).
  pose proof (bytes_at_bound _ _ _ _ Hb) as HB. rewrite !app_length in HB.
  replace (cells_bytes pre ++ cbytes c' ++ cells_bytes post)
     with (upd_bytes (cells_bytes pre ++ cbytes c ++ cells_bytes post) (Z.to_nat (Z.of_nat (length (cells_bytes pre)))) (cbytes c')).
  - apply bytes_at_write_inside; [exact Hb| lia |]. rewrite !app_length. lia.
  - unfold upd_bytes. rewrite Nat2Z.id. rewrite firstn_app_exact. f_equal. f_equal.
    replace (length (cells_bytes pre) + length (cbytes c'))%nat with (length (cells_bytes pre ++ cbytes c)) by (rewrite app_length; lia).
    rewrite app_assoc. apply skipn_app_exact.
Qed.

Lemma cells_at_frame : ltac2:(zQ "h00!n9!pd!iq0!inf!io6!hha!q2!hra!il6!hpd!iq6!ip0!l9!hl0!im2!iqb>1m>0@1$1@1$0#k0@1$9@1$1@1$0#8>1A$7>2cs@1$6$c>1a$7>2bs@1$6@1$1@1$0#8>0@3$8^5^4^3>0@2$2Z^3>0@2$2@2$3^4@1$4@2$5@1$1@1$0#8^3@2$f+2+k0>0@2$a@2$2@2$3^7@1$4@1$d^6^5@2$2@2$3^5@1$4@2$5@1$1@1$0#8^4^7@3$8@3$b^9@1$e^6^5^8^7").
Proof.
  intros m A cs a bs [Hwf Hb] Ha Hl Hd. split; [assumption|].
  apply bytes_at_write_other; try assumption. rewrite cells_bytes_length by assumption. exact Hd.
Qed.

Lemma cells_at_bound : ltac2:(zQ "d0!n9!iq0!pd!q2!hpd!hmd!hra!il6!l9!hl0!inf!io6!iqb>1m>0@1$2@1$0#k0@1$4@1$2@1$0#8>1A$6>2cs@1$3$8>0@3$7^3^2^1@2$5@2$1Z^3@2$1@2$a^3@1$b@1$9^2@2$c+2+k0").
Proof. intros m A cs [Hwf Hb]. rewrite <- cells_bytes_length by assumption. eapply bytes_at_bound; eauto. Qed.

Lemma cells_at_wf : ltac2:(zQ "80!n9!pd!q2!hpd!hra!il6!l9!hld>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1A$4>2cs@1$2$6>0@3$5^3^2^1@1$7^2").
Proof. intros m A cs [H _]; exact H. Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma CB3_bytes : ltac2:(zQ "b0!n9!pd!hm8!q2!h8!hob!is9!it3!hha!hi2!iv0>1k$4>1n$4>2bs@1$3@1$1@1$0#8>0@2$a@2$5^3^2@2$8@1$1@1$0#8^1@3$9@1$3@1$1@1$0#8@3$2@1$1@1$0#8@3$6@1$1@1$0#8^4^2@3$2@1$1@1$0#8@3$6@1$1@1$0#8^3@3$7@1$1@1$0#8^4^2@3$7@1$1@1$0#8@2$5^4^3^2^2").
Proof.
  intros k n bs H. rewrite <- (firstn_skipn k bs) at 4. f_equal.
  rewrite <- (firstn_skipn n (skipn k bs)) at 2. f_equal. rewrite skipn_skipn. f_equal. lia.
Qed.

Definition cb_pieces : ltac2:(zQ "50!h8!q2!n9!l9!pd>1k$0>1n$0>2sz$0>2bs@1$1@1$4@1$2#8@1$1$3") := ltac2:(zQ "f0!l9!n9!pd!iv6!qe!q8!q2!h8!ivc!hob!jg1!is9!it3!ji3!hm8\1k$7\1n$7\2sz$7\2bs@1$6@1$2@1$1#8@3$e$0M3\0$3@1$6$0@2$d^4N0@1$4$0@3$5$0@2$8^4@3$b@1$2@1$1#8^4^1@1$4$0@3$5$0@2$8^3@3$b@1$2@1$1#8^3@3$c@1$2@1$1#8^4^1M3\0$3@1$6$0@2$d@2$9^4^3^2@1$4$0@3$5$0@2$8@2$a@2$a^2^4^3@3$c@1$2@1$1#8@2$9^4^3^1@1$4$0").

Lemma cb_pieces_props : ltac2:(zQ "d0!h8!hi2!n9!jia!pd!q2!hmd!hha!hob!iv0!hk2!hl0!hld>1k$0>1n$0>2sz$0>2bs@1$5@1$4@1$2#8>0@3$1$0@2$7@1$4@1$2#8^1^2>0@2$9@2$8^5^4^3@2$6@1$c@4$3^6^5^4^3@2$6@3$1@1$5@1$4@1$2#8@1$a@4$3^6^5^4^3^3@3$1$0@1$b@4$3^6^5^4^3^4").
Proof.
  intros k n sz bs Hl Hkn. unfold cb_pieces.
  destruct (Nat.eqb_spec k 0); destruct (Nat.eqb_spec (k + n) sz); subst; cbn -[firstn skipn Nat.sub];
  rewrite ?firstn_length, ?skipn_length, ?app_nil_r.
  - cbn [skipn]. repeat split; try lia. apply firstn_all2. lia.
  - cbn [skipn Nat.add]. repeat split; try lia. apply firstn_skipn.
  - repeat split; try lia. rewrite <- (firstn_skipn k bs) at 3. f_equal. apply firstn_all2. rewrite skipn_length. lia.
  - repeat split; try lia. apply CB3_bytes. lia.
Qed.

Fixpoint cb_split (cs : list cell) (k n : nat) : list cell :=
  match cs with
  | [] => []
  | c :: cs' =>
      if Nat.ltb k (csize c) then
        match c with
        | CB sz bs => if (Nat.eqb k 0 && Nat.eqb n sz)%bool then c :: cs' else cb_pieces k n sz bs ++ cs'
        | _ => c :: cs'
        end
      else c :: cb_split cs' (k - csize c) n
  end.

Fixpoint cb_split_ok (cs : list cell) (k n : nat) : bool :=
  match cs with
  | [] => true
  | c :: cs' =>
      if Nat.ltb k (csize c) then
        match c with
        | CB sz bs => Nat.leb (k + n) sz
        | _ => true
        end
      else cb_split_ok cs' (k - csize c) n
  end.

Lemma cb_split_props : ltac2:(zQ "e0!h8!hi2!jj6!q2!hmd!hk2!hl0!hld!iv6!jk1!n9!jk7!l9!pd>2cs@1$3$c>1k$0>1n$0>0@1$7^3>0@3$1$8@3$b^4^3^2$9@2$4@1$7@3$2^5^4^3@2$4@3$1@1$3@1$d@1$a#8@1$5@3$2^5^4^3@1$5^5@3$1$0@1$6@3$2^5^4^3@1$6^5").
Proof.
  induction cs as [|c cs IH]; intros k n Hwf Hok; [cbn; tauto|].
  cbn [cells_wf] in Hwf. destruct Hwf as [Hc Hcs].
  cbn [cb_split cb_split_ok] in *.
  destruct (Nat.ltb k (csize c)) eqn:LT.
  - destruct c as [v|v|v|b|sz bs]; try (cbn; tauto).
    cbn [cell_wf] in Hc. apply Nat.leb_le in Hok.
    destruct (Nat.eqb k 0 && Nat.eqb n sz)%bool; [cbn; tauto|].
    destruct (cb_pieces_props k n sz bs Hc Hok) as (A1 & A2 & A3).
    rewrite cells_bytes_app, cells_size_app, A2, A3. split; [|split; [reflexivity|cbn; lia]].
    apply cells_wf_app. cbn. tauto.
  - cbn. destruct (IH (k - csize c)%nat n Hcs Hok) as (A1 & A2 & A3). rewrite A2, A3. tauto.
Qed.

Lemma cells_at_cb_split : ltac2:(zQ "e0!q2!h8!n9!jl5!pd!iv6!hpd!jk1!hi2!hra!jp5!jj6!jk7!l9>4segs@1$0$a>1m>0@1$4@1$2#k0@1$6@1$4@1$2#8>1A$9>2cs@1$0$d>1k$1>1n$1>0@4$3^6^5^4^3>0@3$8$5@3$c^4^3^2$7@4$3^8^7^6@3$b^5^4^3").
Proof.
  intros segs m A cs k n [Hwf Hb] Hok. destruct (cb_split_props cs k n Hwf Hok) as (A1 & A2 & A3).
  split; [exact A1|]. rewrite A2. exact Hb.
Qed.

Lemma cells_size_cb_split : ltac2:(zQ "a0!h8!hi2!hl0!iv6!q2!jk1!jj6!jk7!l9!hld>2cs@1$4$8>1k$0>1n$0>0@1$9^3>0@3$1$3@3$7^4^3^2$5@3$1$0@1$2@3$6^5^4^3@1$2^5").
Proof. intros. eapply cb_split_props; eauto. Qed.
