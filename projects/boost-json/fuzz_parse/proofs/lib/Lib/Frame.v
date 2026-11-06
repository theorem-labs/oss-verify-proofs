(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import PropExec MState Mem Cells Exec Step.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv3h5LinuxProcessSemantics5Riscv7Preludek15bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~mf5Wrd64k16TEmptyk15TNode37Corelib4Init9Datatypess54Somes54None01Zs54prods54list37Corelib4Init5Logicvc3andvc3not79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~hhc6insidehhc3ivlhhc7outside46Stdlib6ZArith6BinInt1Zhn43addhn42lehn42lthhcddisjoint_froms56optionvc2eqhfbbv_unsigned3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshsc5wview89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame8WithSegs~~~~~~igc5munchigc5wmonoigc6sub_fps56lengthhn46of_nathsccwrite_to_mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ip02wahn43powip08bytes_atip05wr_at79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~iuc8rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~jj34celljj3acells_sizeiuc8ro_cellsvc2exip03mrdigc3stks53nathn43subhn46to_nats54conss53niljj32CBvc2or3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypejt37Segment" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mkR : ltac2:(zQ "30!h9!jc!m7>2x1@1$1@1$0#k0>2x2@1$1@1$0#k0>2x3@1$1@1$0#k0>2x4@1$1@1$0#k0>2x5@1$1@1$0#k0>2x6@1$1@1$0#k0>2x7@1$1@1$0#k0>2x8@1$1@1$0#k0>2x9@1$1@1$0#k0>3x10@1$1@1$0#k0>3x11@1$1@1$0#k0>3x12@1$1@1$0#k0>3x13@1$1@1$0#k0>3x14@1$1@1$0#k0>3x15@1$1@1$0#k0>3x16@1$1@1$0#k0>3x17@1$1@1$0#k0>3x18@1$1@1$0#k0>3x19@1$1@1$0#k0>3x20@1$1@1$0#k0>3x21@1$1@1$0#k0>3x22@1$1@1$0#k0>3x23@1$1@1$0#k0>3x24@1$1@1$0#k0>3x25@1$1@1$0#k0>3x26@1$1@1$0#k0>3x27@1$1@1$0#k0>3x28@1$1@1$0#k0>3x29@1$1@1$0#k0>3x30@1$1@1$0#k0>3x31@1$1@1$0#k0@2$2@1$0#5@1$1@1$0#k0") := ltac2:(zQ "70!qc!r4!rd!td!h9!jc!u4\2x1@1$5@1$4#k0\2x2@1$5@1$4#k0\2x3@1$5@1$4#k0\2x4@1$5@1$4#k0\2x5@1$5@1$4#k0\2x6@1$5@1$4#k0\2x7@1$5@1$4#k0\2x8@1$5@1$4#k0\2x9@1$5@1$4#k0\3x10@1$5@1$4#k0\3x11@1$5@1$4#k0\3x12@1$5@1$4#k0\3x13@1$5@1$4#k0\3x14@1$5@1$4#k0\3x15@1$5@1$4#k0\3x16@1$5@1$4#k0\3x17@1$5@1$4#k0\3x18@1$5@1$4#k0\3x19@1$5@1$4#k0\3x20@1$5@1$4#k0\3x21@1$5@1$4#k0\3x22@1$5@1$4#k0\3x23@1$5@1$4#k0\3x24@1$5@1$4#k0\3x25@1$5@1$4#k0\3x26@1$5@1$4#k0\3x27@1$5@1$4#k0\3x28@1$5@1$4#k0\3x29@1$5@1$4#k0\3x30@1$5@1$4#k0\3x31@1$5@1$4#k0@4$2$0@4$2$0@4$2$0@4$2$0@4$2$0@4$2$0@1$1$0@2$3$0^1@1$1$0@2$3$0^h1@1$1$0@2$3$0^h9@4$2$0@1$1$0@2$3$0^9@1$1$0@2$3$0^hd@4$2$0@4$2$0@1$1$0@2$3$0^d@1$1$0@2$3$0^h5@4$2$0@1$1$0@2$3$0^5@1$1$0@2$3$0^hf@4$2$0@4$2$0@4$2$0@1$1$0@2$3$0^f@1$1$0@2$3$0^h7@4$2$0@1$1$0@2$3$0^7@1$1$0@2$3$0^hb@4$2$0@4$2$0@1$1$0@2$3$0^b@1$1$0@2$3$0^h3@4$2$0@1$1$0@2$3$0^3@1$1$0@1$6$0@4$2$0@4$2$0@4$2$0@4$2$0@1$1$0@2$3$0^h0@1$1$0@2$3$0^h8@4$2$0@1$1$0@2$3$0^8@1$1$0@2$3$0^hc@4$2$0@4$2$0@1$1$0@2$3$0^c@1$1$0@2$3$0^h4@4$2$0@1$1$0@2$3$0^4@1$1$0@2$3$0^he@4$2$0@4$2$0@4$2$0@1$1$0@2$3$0^e@1$1$0@2$3$0^h6@4$2$0@1$1$0@2$3$0^6@1$1$0@2$3$0^ha@4$2$0@4$2$0@1$1$0@2$3$0^a@1$1$0@2$3$0^h2@4$2$0@1$1$0@2$3$0^2@1$1$0").

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ivl : ltac2:(zQ "00S") := ltac2:(zQ "20!ub!ue@2$1$0$0").   (* [comment removed for export] *)

Fixpoint outside (W : list ivl) (x : Z) : Prop :=
  match W with
  | [] => True
  | (lo, hi) :: W' => ~ (lo <= x < hi)%Z /\ outside W' x
  end.

Fixpoint inside (W : list ivl) (a : Z) (n : Z) : Prop :=
  match W with
  | [] => False
  | (lo, hi) :: W' => (lo <= a /\ a + n <= hi)%Z \/ inside W' a n
  end.

Fixpoint disjoint_from (W : list ivl) (a : Z) (n : Z) : Prop :=
  match W with
  | [] => True
  | (lo, hi) :: W' => (a + n <= lo \/ hi <= a)%Z /\ disjoint_from W' a n
  end.

Lemma inside_not_outside : ltac2:(zQ "a0!ub!v5!hh0!hh6!hl8!hm2!hm9!hoc!hp3!hp9>1W@1$1$5>1a$0>1n$0>1x$0>0@3$4^4^3^2>0@2$2@2$8^4^2@2$9^2@2$7^4^3@1$3@2$6^6^3").
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros a n x Hin Hx; [tauto|].
  intros [H1 H2]. destruct Hin as [Hin|Hin]; [lia|]. exact (IH _ _ _ Hin Hx H2).
Qed.

Lemma disjoint_outside : ltac2:(zQ "90!ub!v5!hh0!hpf!hm2!hm9!hoc!hp3!hp9>1W@1$1$4>1a$0>1n$0>1x$0>0@3$3^4^3^2>0@2$2@2$7^4^2@2$8^2@2$6^4^3@2$5^6^3").
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros a n x Hd Hx; [exact I|].
  destruct Hd as [H1 H2]. split; [lia|]. eauto.
Qed.

Section WithSegs.
Variable segs : ltac2:(zQ "20!v5!kg8@1$0$1").

(* [comment removed for export] *)
Definition munch : ltac2:(zQ "51!h9!jc!hr0!v5!hm2&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1W@1$3$4>1m~0>2m'~0P") := ltac2:(zQ "81!h9!jc!hr0!v5!hr9!hm2!hm9!hre&>0@1$1@1$0#k0@1$2@1$1@1$0#8\1W@1$3$5\1m~0\2m'~0>1x@1$1@1$0#k0>0@2$6^4@2$7@1$0#k0^1@3$4@1$2@1$1@1$0#8@1^3^2@1^4^2").
Definition wmono : ltac2:(zQ "31!h9!jc!hr0&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1m~0>2m'~0P") := ltac2:(zQ "71!h9!jc!hr0!u4!hr9!hh6!ig3&>0@1$1@1$0#k0@1$2@1$1@1$0#8\1m~0\2m'~0>1x@1$1@1$0#k0>0@1$5@3$4@1$2@1$1@1$0#8@3$6?4segs^3^1@1$3@1$1@1$0#8@1$5@3$4@1$2@1$1@1$0#8@3$6?4segs^3^2@1$3@1$1@1$0#8").

Lemma munch_refl : ltac2:(zQ "60!h9!jc!v5!hr0!il1!hm2>1W@1$2$5>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8@3$4^2^1^1"). Proof. intros W m x _; reflexivity. Qed.
Lemma wmono_refl : ltac2:(zQ "40!h9!jc!hr0!ila>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8@2$3^1^1"). Proof. intros m x H; exact H. Qed.
Lemma wmono_trans : ltac2:(zQ "41!h9!jc!hr0!ila&>0@1$1@1$0#k0@1$2@1$1@1$0#8>2m1~0>2m2~0>2m3~0>0@2$3^3^2>0@2$3^3^2@2$3^5^3").
Proof. intros m1 m2 m3 H1 H2 x Hx. apply H2, H1, Hx. Qed.
Lemma munch_trans : ltac2:(zQ "61!h9!jc!hr0!il1!v5!hm2&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1W@1$4$5>2m1~0>2m2~0>2m3~0>0@3$3^4^3^2>0@3$3^5^3^2@3$3^6^5^3").
Proof. intros W m1 m2 m3 H1 H2 x Hx. rewrite (H2 x Hx). apply H1, Hx. Qed.

(* [comment removed for export] *)
Definition sub_fp : ltac2:(zQ "20!v5!hm2>1W@1$0$1>2W'@1$0$1P") := ltac2:(zQ "40!v5!hm2!hm9!ub\1W@1$0$1\2W'@1$0$1>1x$3>0@2$2^2^1@2$2^4^2").
Lemma munch_weaken : ltac2:(zQ "71!h9!jc!v5!hr0!il1!hm2!im3&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1W@1$2$5>2W'@1$2$5>1m~0>2m'~0>0@2$6^4^3>0@3$4^5^3^2@3$4^5^4^3").
Proof. intros W W' m m' Hs H x Hx. apply H, Hs, Hx. Qed.

(* [comment removed for export] *)
Lemma munch_write : ltac2:(zQ "f1!h9!jc!imd!v5!hr0!il1!hp3!in6!ub!io0!hl8!hm2!isa!hoc!it0&>0@1$1@1$0#k0@1$4@1$1@1$0#8>1W@1$3$b>2m0~0>1m~0>1a$8>2bs@1$3@1$1@1$0#8>0@3$5^5^4^3>0@2$6Z^3>0@2$6@2$d^4@1$7@2$2@1$1@1$0#8^3@2$e+2+k0>0@3$a^8^5@1$7@2$2@1$1@1$0#8^4@3$5^9^8@3$9^7@1$c^6^5").
Proof.
  intros W m0 m a bs H Ha Hl Hin x Hx. rewrite write_to_mem_spec by lia.
  pose proof (bv_unsigned_in_range 64 x).
  destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat (length bs))); cbn [andb];
    try (apply H; exact Hx).
  exfalso. eapply (inside_not_outside W a _ (bv_unsigned x) Hin); [lia| exact Hx].
Qed.

Lemma wmono_write : ltac2:(zQ "61!h9!jc!hr0!ila!v5!io0&>0@1$1@1$0#k0@1$2@1$1@1$0#8>2m0~0>1m~0>1a@1$1@1$0#k0>2bs@1$4@1$1@1$0#8>0@2$3^4^3@2$3^5@3$5^4^3^2").
Proof. intros m0 m a bs H x Hx. apply wview_write_mono. apply H, Hx. Qed.

(* [comment removed for export] *)
Lemma bytes_at_transport : ltac2:(zQ "b1!h9!jc!v5!hr0!it7!imd!ub!il1!hpf!hm2!in6&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1W@1$2$9>1m~0>2m'~0>1A$6>2bs@1$2@1$1@1$0#8>0@4$4?4segs^4^2^1>0@3$7^6^5^4>0@3$8^7^4@1$a@2$5@1$1@1$0#8^3@4$4?4segs^6^5^4").
Proof.
  intros W m m' A bs (Ha & Hl & H) Hm Hd. split; [lia|]. split; [lia|].
  intros i Hi. unfold mrd. rewrite Hm.
  - apply H. exact Hi.
  - eapply disjoint_outside; [exact Hd|]. rewrite wa_unsigned by lia. lia.
Qed.

Lemma wr_at_transport : ltac2:(zQ "61!h9!jc!hr0!ub!iu3!ila&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1m~0>2m'~0>1A$3>1n$3>0@4$4?4segs^4^2^1>0@2$5^5^4@4$4?4segs^5^4^3").
Proof. intros m m' A n (Ha & Hn & H) Hw. split; [lia|]. split; [lia|]. intros i Hi. apply Hw, H, Hi. Qed.

Lemma rw_cells_transport : ltac2:(zQ "d1!h9!jc!v5!hr0!ji7!ub!jmf!jn7!il1!ila!hpf!hm2!in6&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1W@1$2$b>1m~0>2m'~0>1A$5>2cs@1$2$6>0@4$4?4segs^4^2^1>0@3$8^6^5^4>0@2$9^6^5>0@3$a^8^5@1$c@1$7^4@4$4?4segs^7^6^5").
Proof.
  intros W m m' A cs [[Hwf Hb] Hw] Hm Hmono Hd. split; [split; [exact Hwf|]|].
  - eapply bytes_at_transport; eauto. rewrite cells_bytes_length by assumption. exact Hd.
  - eapply wr_at_transport; eauto.
Qed.

Lemma ro_cells_transport : ltac2:(zQ "c1!h9!jc!v5!hr0!jo5!ub!jmf!jn7!il1!hpf!hm2!in6&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1W@1$2$a>1m~0>2m'~0>1A$5>2cs@1$2$6>0@4$4?4segs^4^2^1>0@3$8^6^5^4>0@3$9^7^4@1$b@1$7^3@4$4?4segs^6^5^4").
Proof.
  intros W m m' A cs [Hwf Hb] Hm Hd. split; [exact Hwf|].
  eapply bytes_at_transport; eauto. rewrite cells_bytes_length by assumption. exact Hd.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stk : ltac2:(zQ "40!h9!ub!jc!hr0>1m>0@1$2@1$0#k0@1$3@1$2@1$0#8>2lo$1>2hi$1P") := ltac2:(zQ "h00!h9!jc!hh0!hr0!ub!hp3!hr9!isa!u4!td!jp1!hh6!ig3!jp6!hp9!it0\1m>0@1$1@1$0#k0@1$3@1$1@1$0#8\2lo$4\2hi$4@2$2@2$5Z^2@2$2@2$5^1@2$f+2+k0>1a$4>0@2$2@2$5^3^1@2$e^1^2@2$2@1$b@3$6@1$3@1$1@1$0#8@3$c?4segs^5@1$7^2@1$8@1$1@1$0#8@2$a@1$1@1$0#8\1b@1$1@1$0#8@3$6@1$3@1$1@1$0#8@3$d?4segs^6@1$7^3@2$9@1$1@1$0#8^1").

Lemma stk_split : ltac2:(zQ "70!ub!jpd!hh0!h9!hp3!jc!hr0>1m>0@1$5@1$3#k0@1$6@1$5@1$3#8>2lo$0>3mid$0>2hi$0>0@3$1^4^3^1>0@2$2@2$4^4^3@2$4^3^2@2$2@3$1^6^5^4@3$1^6^4^3").
Proof. intros m lo mid hi (H1 & H2 & H) Hm. split; (split; [lia|]; split; [lia|]); intros a Ha; apply H; lia. Qed.

Lemma stk_merge : ltac2:(zQ "70!ub!jpd!h9!hp3!jc!hr0!hh0>1m>0@1$4@1$2#k0@1$5@1$4@1$2#8>2lo$0>3mid$0>2hi$0>0@3$1^4^3^2>0@3$1^5^3^2>0@2$6@2$3^5^4@2$3^4^3@3$1^7^6^4").
Proof.
  intros m lo mid hi (A1 & A2 & A) (B1 & B2 & B) Hm. split; [lia|]. split; [lia|].
  intros a Ha. destruct (Z.ltb_spec0 a mid); [apply A | apply B]; lia.
Qed.

Lemma stk_empty : ltac2:(zQ "80!h9!hp3!jc!hr0!hh0!ub!jpd!it0>1m>0@1$2@1$0#k0@1$3@1$2@1$0#8>2lo$5>0@2$4@2$1Z^1@2$1^1@2$7+2+k0@3$6^3^2^2").
Proof. intros. split; [lia|]. split; [lia|]. intros a Ha. lia. Qed.

(* [comment removed for export] *)
Lemma stk_bytes : ltac2:(zQ "f0!h9!jc!v5!ub!imd!jq4!hr0!hh0!hr9!jp1!jpd!it7!hp3!jqa!jr1>1m>0@1$1@1$0#k0@1$6@1$1@1$0#8>2lo$3>2hi$3>0@3$a^3^2^1>0@2$c^3^2@2$9@1$2@1$1@1$0#8\2bs@1$2@1$1@1$0#8@2$7@3$8$5@2$4@1$1@1$0#8^1@1$e@2$d^4^5@4$b?4segs^6^5^1").
Proof.
  intros m lo hi (H1 & H2 & H) Hle.
  set (n := Z.to_nat (hi - lo)).
  assert (G : forall k, (k <= n)%nat -> exists bs, length bs = k /\ forall i, (i < k)%nat -> mrd segs m (wa (lo + Z.of_nat i)) = nth_error bs i).
  { induction k as [|k IH]; intros Hk.
    - exists []. split; [reflexivity|]. intros i Hi; lia.
    - destruct (IH ltac:(lia)) as (bs & Hlen & Hbs).
      destruct (H (lo + Z.of_nat k)%Z ltac:(lia)) as [_ (b & Hb)].
      exists (bs ++ [b]). split. { rewrite app_length; cbn; lia. }
      intros i Hi. destruct (Nat.eqb_spec i k).
      + subst i. rewrite nth_error_app2 by lia. rewrite Hlen, Nat.sub_diag. exact Hb.
      + rewrite nth_error_app1 by lia. apply Hbs. lia. }
  destruct (G n ltac:(lia)) as (bs & Hlen & Hbs). exists bs. split; [exact Hlen|].
  split; [lia|]. split; [lia|]. intros i Hi. apply Hbs. lia.
Qed.

Lemma stk_carve : ltac2:(zQ "h10!h9!jc!in6!jqa!v5!ub!jmf!jpd!jrb!jq4!js2!hr0!hh0!jp1!js8!ji7!hp3>1m>0@1$1@1$0#k0@1$b@1$1@1$0#8>2lo$5>2hi$5>1n$9>0@3$7^4^3^2>0@2$h0^4@2$3^3@1$2^2@2$c@3$7^6^5@2$3^4@1$2^3@2$d@1$4@1$1@1$0#8\4junk@1$4@1$1@1$0#8@4$f?4segs^7@2$3^5@1$2^4@3$8$6@2$e^4^1@1$a$6").
Proof.
  intros m lo hi n Hs Hle. pose proof Hs as (H1 & H2 & H).
  destruct (stk_split m lo (hi - Z.of_nat n) hi Hs ltac:(lia)) as [Hlo Hhi].
  split; [exact Hlo|].
  destruct (stk_bytes m (hi - Z.of_nat n) hi Hhi ltac:(lia)) as (bs & Hlen & Hb).
  exists bs. split.
  - split. { cbn. split; [lia|exact I]. }
    cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
    intros i Hi. apply H. lia.
Qed.

(* [comment removed for export] *)
Lemma stk_of_rw_cells : ltac2:(zQ "b0!h9!jc!v5!hr0!ub!jmf!jn7!jpd!ji7!hoc!in6>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1A$4>2cs@1$2$5>0@4$8?4segs^3^2^1@3$7^4^3@2$9^3@1$a@1$6^2").
Proof.
  intros m A cs [[Hwf (Ha & Hl & Hb)] (_ & _ & Hw)].
  rewrite cells_bytes_length in Hl, Hb by assumption.
  split; [lia|]. split; [lia|]. intros a Hr. split.
  - replace a with (A + (a - A))%Z by lia. apply Hw. lia.
  - replace a with (A + Z.of_nat (Z.to_nat (a - A)))%Z by lia. rewrite Hb by lia.
    destruct (nth_error (cells_bytes cs) (Z.to_nat (a - A))) eqn:E; [eexists; reflexivity|].
    apply nth_error_None in E. rewrite cells_bytes_length in E by assumption. lia.
Qed.

Lemma stk_release : ltac2:(zQ "c0!h9!ub!jpd!jc!v5!hr0!jmf!jn7!ji7!hoc!hp3!in6>1m>0@1$3@1$0#k0@1$5@1$3@1$0#8>2lo$1>1A$1>2cs@1$4$6>0@3$2^4^3^2>0@4$8?4segs^5^3^2>0@2$a^5^4@3$2^7^6@2$9^5@1$b@1$7^4").
Proof.
  intros m lo A cs Hs Hc Hle. pose proof (rw_cells_bound segs m A cs Hc).
  eapply stk_merge; [exact Hs | apply stk_of_rw_cells; exact Hc | lia].
Qed.

(* [comment removed for export] *)
Lemma stk_write : ltac2:(zQ "d0!h9!jc!ub!jpd!hp3!imd!v5!hr0!io0!isa!hoc!in6!it0>1m>0@1$1@1$0#k0@1$7@1$1@1$0#8>2lo$2>2hi$2>1a$2>2bs@1$6@1$1@1$0#8>0@3$3^5^4^3>0@2$4Z^3>0@2$4@2$a^4@1$b@2$5@1$1@1$0#8^3@2$c+2+k0@3$3@3$8^8@1$9^5^4^7^6").
Proof.
  intros m lo hi a bs (H1 & H2 & H) Ha Hl. split; [lia|]. split; [lia|]. intros x Hx.
  destruct (H x Hx) as [Hw (b & Hb)]. split.
  - apply wview_write_mono. exact Hw.
  - unfold mrd. rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
    destruct (Z.leb_spec0 a x); destruct (Z.ltb_spec0 x (a + Z.of_nat (length bs))); cbn [andb]; try (eexists; exact Hb).
    destruct (nth_error bs (Z.to_nat (x - a))) eqn:E; [eexists; reflexivity|]. apply nth_error_None in E. lia.
Qed.

Lemma stk_transport : ltac2:(zQ "h21!h9!jc!hr0!ub!jpd!td!v5!hh0!hr9!jp1!jse!il1!ila!hm2!hm9!isa!hp3!hp9&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1W@1$6$d>1m~0>2m'~0>2lo$3>2hi$3>0@3$4^4^2^1>0@3$b^6^5^4>0@2$c^6^5>0>1x$3>0@2$7@2$h0^6^1@2$h1^1^5@2$a@2$e^a^2@2$9@1$1@1$0#8\1b@1$1@1$0#8@3$8@1$2@1$1@1$0#8@1^9@1$f^3@2$5@1$1@1$0#8^1@3$4^7^6^5").
Proof.
  intros W m m' lo hi (H1 & H2 & H) Hm Hw Hcase. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hwa (b & Hb)]. split; [apply Hw; exact Hwa|].
  destruct (Hcase a Ha) as [Ho | (b' & Hb')].
  - exists b. unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
  - exists b'. unfold mrd. rewrite Hb'. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma stk_transport_disjoint : ltac2:(zQ "b1!h9!jc!hr0!ub!jpd!v5!il1!ila!hpf!hm2!jqa&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1W@1$5$9>1m~0>2m'~0>2lo$3>2hi$3>0@3$4^4^2^1>0@3$6^6^5^4>0@2$7^6^5>0@3$8^8^5@2$a^4^5@3$4^7^6^5").
Proof.
  intros. eapply stk_transport; eauto. intros x Hx. left. eapply disjoint_outside; eauto. lia.
Qed.

End WithSegs.
(* [comment removed for export] *)
