(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import PlacementSearch.  (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos01Z37Corelib4Init5Logici23andi22eq46Stdlib6ZArith6BinInt1Zk12lek12ltk13pow35stdpp9bitvectorbdefinitionsm97Z_to_bvm9bbv_unsigned69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanCeil~~~~~~pedalloc_ceilingm92bv37Corelib4Init9Datatypesue4boolue4prodi22exue5falseue4listue4pairue4true3h5LinuxProcessSemanticsfLinuxProcessSem5Statehj6aiv_overlaphj6bregion_free36Stdlib5Lists4Listho12In69OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsanPlacement~~~~~~hpaagap_weightue3fstue3sndk13addk13ltbho16filterhpa7live_atue6length37Corelib4Init5Peanoihe2lthj69page_sizepeebottomup_floork16modulo79OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsanPlacement3Gap~~~~~~ilf8scan_invi22orilf6gap_atue3natihe2lehpa8gw_sizesk13mulk16of_natue3apphj67vm_mapshj6bvm_reservedhj66VmMaps" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fg_u64_lit : ltac2:(zQ "90!h9!hf!j6!jc!l9!le!m3!o6!p0>1z$1>0@2$2@2$4Z^1@2$5^1@2$6+2+k0@3$3$1@2$8@1$0#k0@2$7@1$0#k0^2^2").
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold bv_modulus. exact Hz.
Qed.

Lemma fg_alloc_ceiling_val : ltac2:(zQ "30!jc!hf!t9@3$0$1$2+nvvvnvogggg0").
Proof. reflexivity. Qed.

(* [comment removed for export] *)

Lemma fg_region_free_false : ltac2:(zQ "e1!h9!u9!hg6!hgd!jc!hh4!hh9!hi1!hi8!hif!j6!hm4!hn2!hp4&@2$3@1$1@1$0#k0@1$1@1$0#k0>4maps@1$7~0>2lo@1$1@1$0#k0>1n@1$1@1$0#k0>0@3$4$2@3$c^3^2^1$6@2$5@1$1@1$0#k0\1b@1$1@1$0#k0@2$5@1$1@1$0#k0\1s@1$1@1$0#k0@2$a@3$d~0@4$8@1$1@1$0#k0@1$1@1$0#k0^2^1^6@3$4$2@4$b^5^4^2^1$9").
Proof.
  induction maps as [|[b s] r IH]; intros lo n H; [discriminate|].
  cbn in H. apply andb_false_iff in H as [H|H].
  - apply negb_false_iff in H. exists b, s. split; [now left|exact H].
  - ndestruct (IH lo n H) as (b' & s' & Hin & Hov).
    exists b', s'. split; [now right|exact Hov].
Qed.

(* [comment removed for export] *)
Fixpoint gap_weight (nZ : Z) (l : list (word * word)) : Z :=
  match l with
  | [] => 0
  | (_, s) :: r => bv_unsigned s + nZ + 4095 + gap_weight nZ r
  end.

Lemma gap_weight_nonneg : ltac2:(zQ "70!h9!l9!u9!hi1!hgd!hf!hta>2nZ$5>1l@1$3@2$4@1$2@1$0#k0@1$2@1$0#k0>0@2$1Z^2@2$1Z@2$6^3^2").
Proof.
  induction l as [|[b s] l IH]; intros HnZ; cbn; [lia|].
  pose proof (bv_unsigned_in_range 64 s). specialize (IH HnZ). lia.
Qed.

(* [comment removed for export] *)
Definition live_at : ltac2:(zQ "50!h9!u9!hg6!hgd!hf>1c$4>1p@2$3@1$1@1$0#k0@1$1@1$0#k0$2") := ltac2:(zQ "90!h9!u9!p0!hu8!hgd!hue!hf!hv4!hva\1c$6\1p@2$4@1$1@1$0#k0@1$1@1$0#k0@2$8^2@2$7@2$2@1$0#k0@3$3@1$1@1$0#k0@1$1@1$0#k0^1@2$2@1$0#k0@3$5@1$1@1$0#k0@1$1@1$0#k0^1").

Lemma gap_weight_filter_le : ltac2:(zQ "91!h9!u9!hgd!hta!l9!hg6!hi1!hf!ig0&@2$2@1$1@1$0#k0@1$1@1$0#k0>2nZ$7>1f>0~0$5>1l@1$6~0>0@2$4Z^3@2$4@2$3^4@3$8~0^3^2@2$3^4^2").
Proof.
  induction l as [|[b s] l IH]; intros HnZ; cbn; [lia|].
  pose proof (bv_unsigned_in_range 64 s). specialize (IH HnZ).
  destruct (f (b, s)); cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma live_weight_step : ltac2:(zQ "h43!h9!u9!hgd!iga!ig0!hi8!hf!hv4!l9!hg6!ih5!jc!hta!hh9!hi1!hif!j6!ij2!hp4!p0&@2$2@1$1@1$0#k0@1$1@1$0#k0&@3$4~0@1$3^8^a&@3$4~0@1$3^9^a>2nZ$6>1l@1$e~0>1c$6>2c'$6>1b@1$1@1$0#k0>1s@1$1@1$0#k0>0@2$8Z^6>0@2$8^5^4>0@3$h2~0@4$5@1$1@1$0#k0@1$1@1$0#k0^4^3^7>0@3$b$9@2$3^7@4$5@1$1@1$0#k0@1$1@1$0#k0^5^4$f>0@3$b$9@2$3^7@4$5@1$1@1$0#k0@1$1@1$0#k0^6^5$d@2$h0@2$8@2$7@2$c^b~1@2$7@2$7@2$h3@1$0#k0^6^b+vvf@2$c^b~2@2$h1@2$a~0~1@2$a~0~2").
Proof.
  intros nZ l c c' b s HnZ Hcc'.
  induction l as [|[b0 s0] l IH]; intros Hin Hlive Hdead; [contradiction|].
  assert (Hmono : forall p, live_at c' p = true -> live_at c p = true).
  { intros [x y] H. unfold live_at in *. cbn in *. apply Z.ltb_lt in H. apply Z.ltb_lt. lia. }
  assert (Hle : gap_weight nZ (List.filter (live_at c') l) <= gap_weight nZ (List.filter (live_at c) l)
                /\ (length (List.filter (live_at c') l) <= length (List.filter (live_at c) l))%nat).
  { clear IH Hin. induction l as [|[x y] l IHl]; cbn; [split; [lia|constructor]|].
    pose proof (bv_unsigned_in_range 64 y).
    destruct (live_at c' (x, y)) eqn:E'.
    - rewrite (Hmono _ E'). cbn. destruct IHl; split; [lia|]. apply le_n_S. assumption.
    - destruct (live_at c (x, y)); cbn; destruct IHl; split; try lia. }
  destruct Hin as [Heq|Hin].
  - injection Heq as -> ->. cbn. rewrite Hlive, Hdead. cbn.
    destruct Hle as [Hw Hl]. split; [lia|]. apply Nat.lt_succ_r in Hl. exact Hl.
  - destruct (IH Hin Hlive Hdead) as [Hw Hl]. cbn.
    pose proof (bv_unsigned_in_range 64 s0).
    destruct (live_at c' (b0, s0)) eqn:E'.
    + rewrite (Hmono _ E'). cbn. split; [lia|]. apply Nat.succ_lt_mono in Hl. exact Hl.
    + destruct (live_at c (b0, s0)); cbn; split; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Gap.
  Variable L : ltac2:(zQ "40!h9!u9!hi1!hgd@1$2@2$3@1$1@1$0#k0@1$1@1$0#k0").
  Variable nZ : Z.
  Hypothesis HnZ : ltac2:(zQ "10!l9@2$0Z?2nZ").

  (* [comment removed for export] *)
  Definition scan_inv : ltac2:(zQ "10!hf>1c$0P") := ltac2:(zQ "f0!j6!h9!hf!hv4!l9!u9!hgd!jc!ij8!t9!ik5!hta!iga!ig0!il6\1c$2@2$0@3$7$2@2$e^1$8Z@2$0@2$4$a^1@2$4@2$3@2$3^1?2nZ@2$b?2nZ@3$d@2$6@1$5@1$1#k0@1$5@1$1#k0@1$c^1?1L$9").

  Definition gap_at : ltac2:(zQ "10!hf>1c$0P") := ltac2:(zQ "e0!j6!jc!h9!hf!l9!o6!hg6!hif!ij8!hn2!t9!ik5!hv4!il6\1c$3@2$0@3$1$3@2$d^1$8Z@2$0@2$4$b^1@2$0@2$4@2$c^1?2nZ$a@3$1$6@3$9?1L@2$5@1$2#k0^1@2$5@1$2#k0?2nZ$7").

  Lemma scan_ok_or_step : ltac2:(zQ "d1!h9!u9!hgd!hf!ih5!iq3!iga!ig0!j6!hh4!iqf!ij2!ir4&@2$2@1$1@1$0#k0@1$1@1$0#k0>1c$3>0@1$5^1@2$a@1$c^2@2$9$3\2c'$3@2$8@1$5^1@2$b@2$4~0@3$7~0@1$6^1?1L@2$4~0@3$7~0@1$6^3?1L").
  Proof.
    (intros c nd_i1; ndestruct nd_i1 as (Hal & Hfl & Hw)).
    pose proof fg_alloc_ceiling_val as Hcv. pose proof bottomup_floor_val as Hfv.
    pose proof (gap_weight_nonneg nZ (List.filter (live_at c) L) HnZ) as Hw0.
    assert (Hc64 : 0 <= c < 2 ^ 64) by lia.
    assert (Hcu : bv_unsigned (Z_to_bv 64 c) = c) by (apply fg_u64_lit; lia).
    assert (Hnu : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply fg_u64_lit; lia).
    destruct (region_free L (Z_to_bv 64 c) (Z_to_bv 64 nZ)) eqn:Hfree.
    - left. split; [exact Hal|]. split; [exact Hfl|]. split; [lia | exact Hfree].
    - right.
      destruct (fg_region_free_false _ _ _ Hfree) as (b & s & Hin & Hov).
      unfold iv_overlap in Hov. rewrite Hcu, Hnu in Hov.
      apply andb_true_iff in Hov as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
      set (B := bv_unsigned b) in *. set (S := bv_unsigned s) in *.
      set (c' := page_round_up_Z (B + S)).
      pose proof (page_round_up_Z_ge (B + S)) as Hge.
      assert (Hle : c' <= B + S + 4095).
      { unfold c', page_round_up_Z, page_size.
        pose proof (Z.mul_div_le (B + S + 4096 - 1) 4096 ltac:(lia)). lia. }
      assert (Hlive : live_at c (b, s) = true) by (unfold live_at; cbn; apply Z.ltb_lt; lia).
      assert (Hdead : live_at c' (b, s) = false) by (unfold live_at; cbn; apply Z.ltb_ge; lia).
      destruct (live_weight_step nZ L c c' b s HnZ ltac:(lia) Hin Hlive Hdead) as [Hws Hlen].
      exists c'. split; [|exact Hlen].
      split; [apply page_round_up_Z_aligned|].
      split; lia.
  Qed.

  Lemma scan : ltac2:(zQ "c1!h9!u9!hf!hgd!ih5!ire!hh4!is4!ir4!iq3!iga!ig0&@2$3@1$1@1$0#k0@1$1@1$0#k0>1k$5>1c$2>0@2$7@2$4~0@3$b~0@1$a^1?1L^2>0@1$9^2@2$6$2\1g$2@1$8^1").
  Proof.
    induction k as [|k IH]; intros c Hk Hinv.
    - destruct (scan_ok_or_step c Hinv) as [Hok|(c' & _ & Hlt)]; [|lia].
      exists c. exact Hok.
    - destruct (scan_ok_or_step c Hinv) as [Hok|(c' & Hinv' & Hlt)].
      + exists c. exact Hok.
      + apply (IH c'); [lia|exact Hinv'].
  Qed.

  (* [comment removed for export] *)
  Theorem free_gap_of_slack : ltac2:(zQ "h00!j6!hf!hv4!l9!jc!h9!t9!ik5!o6!hg6!hif!hh4!ij8!hn2!hta!il6>0@2$3@2$2@2$2$7?2nZ@2$e?2nZ?1L$6@2$b$1\1g$1@2$0@3$4$1@2$f^1$cZ@2$0@2$3$7^1@2$0@2$3@2$2^1?2nZ$6@3$4$9@3$d?1L@2$8@1$5#k0^1@2$8@1$5#k0?2nZ$a").
  Proof.
    intros Hslack.
    assert (Hinv : scan_inv bottomup_floor).
    { split; [rewrite bottomup_floor_val; reflexivity|]. split; [lia|].
      pose proof (gap_weight_filter_le nZ (live_at bottomup_floor) L HnZ). lia. }
    exact (scan _ bottomup_floor (le_n _) Hinv).
  Qed.
End Gap.

(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint gw_sizes (l : list (word * word)) : Z :=
  match l with [] => 0 | iv :: r => bv_unsigned (snd iv) + gw_sizes r end.

Lemma gap_weight_sizes : ltac2:(zQ "c1!h9!u9!hgd!hf!hv4!ih5!hi1!jc!hta!isa!it6!itc&@2$2@1$1@1$0#k0@1$1@1$0#k0>2nZ$3>1l@1$6~0@3$7$3@2$8^2^1@2$4@1$9^1@2$a@1$b@2$5~0^1@2$4^2+vvf").
Proof.
  intros nZ l. induction l as [|[b s] l IH]; cbn -[Z.of_nat Z.mul Z.add]; [reflexivity|].
  rewrite IH, Nat2Z.inj_succ. lia.
Qed.

Theorem free_gap_of_totals : ltac2:(zQ "h91!h9!u9!hf!hv4!l9!hgd!iu5!j6!iub!iv6!jc!t9!ik5!o6!hg6!ih5!hif!hh4!jg5!ij8!hn2!isa!il6!it6!itc&@2$5@1$1@1$0#k0@1$1@1$0#k0>1h$h2>2nZ$2>3tot$2>0@2$4Z^2>0@2$4@1$h5@3$6~0@1$9^4@1$8^4^2>0@2$4@2$3@2$3@2$3$c^4^3@2$h7@1$h8@2$f~0@3$6~0@1$9^5@1$8^5@2$3^4+vvf$b@2$h1$2\1g$2@2$7@3$a$2@2$h6^1$h3Z@2$7@2$4$c^1@2$7@2$4@2$3^1^6$b@3$a$e@3$h4@3$6~0@1$9^7@1$8^7@2$d@1$0#k0^1@2$d@1$0#k0^6$h0").
Proof.
  intros h nZ tot HnZ Htot Hband.
  ndestruct (free_gap_of_slack (vm_reserved h ++ vm_maps h) nZ HnZ) as (g & Hal & Hfl & Hc & Hfree).
  { rewrite gap_weight_sizes. lia. }
  exists g. split; [exact Hal|]. split; [exact Hfl|]. split; [exact Hc|]. exact Hfree.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
