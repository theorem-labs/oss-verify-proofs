(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image Mem Cells Step Frame Arr CellsX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AllocWf AllocKit AllocRep.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsShadow~~~~~~03mem37Corelib4Init9Datatypesk34list37Corelib7Numbers7BinNumsm24Nposm21Z35stdpp9bitvectorbdefinitionso62bvk34boolk34andbk36lengthk36option36Stdlib5Lists4Lists89nth_error46Stdlib6ZArith6BinInt1Zu73addu73lebu73ltbu76of_natu73subu76to_nato6bbv_unsignedu72le" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

  Definition ghost : ltac2:(zQ "50!je!lb!nb!o2!q3>1m$0>2lo$3>2bs@1$1@1$4@1$2#8$0") := ltac2:(zQ "h10!nb!q3!q8!o2!qf!r6!lb!rf!je!tb!vf!hg5!hgb!hh1!hha!hi0!hi9\1m$8\2lo$3\2bs@1$6@1$1@1$0#8\1x@1$1@1$0#k0=1z$3@2$h0@1$0#k0^1M2\0$2@1$7@1$1@1$0#8@2$4@2$b^4^1@2$c^1@2$a^4@1$d@2$5@1$1@1$0#8^3@3$9@1$1@1$0#8^3@1$f@2$e^1^4@1^5^2").

  Variables (m : mem) (lo : Z) (bs : list byte).
  Let n := Z.of_nat (length bs).
  Let g := ghost m lo bs.
  Hypothesis LO0 : ltac2:(zQ "10!hj7@2$0Z?2lo").
  Hypothesis HI64 : lo + n <= 2 ^ 64.

  Lemma ghost_out : forall x : word, ~ (lo <= bv_unsigned x < lo + n) -> g x = m x.
  Proof.
    intros x Hx. unfold g, ghost. destruct (Z.leb_spec lo (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (lo + Z.of_nat (length bs))); cbn [andb]; try reflexivity.
    exfalso. apply Hx. subst n. lia.
  Qed.
  Lemma ghost_in : forall i, (i < length bs)%nat -> g (wa (lo + Z.of_nat i)) = nth_error bs i.
  Proof.
    intros i Hi. unfold g, ghost. rewrite wa_unsigned by (subst n; lia).
    replace (lo <=? lo + Z.of_nat i) with true by (symmetry; apply Z.leb_le; lia).
    replace (lo + Z.of_nat i <? lo + Z.of_nat (length bs)) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
    f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma munch_ghost : munch [(lo, lo + n)] m g.
  Proof. intros x Hx. cbn [outside] in Hx. apply ghost_out. lia. Qed.
  Lemma agree_ghost : agree_on (fun a => ~ (lo <= a < lo + n)) m g.
  Proof. intros x Hx Hr. apply ghost_out. rewrite wa_unsigned by lia. exact Hx. Qed.

  (* [comment removed for export] *)
  Lemma wmono_ghost : wmono asegs m g.
  Proof.
    intros x Hw. unfold wview in *. unfold g, ghost.
    destruct ((lo <=? bv_unsigned x) && (bv_unsigned x <? lo + Z.of_nat (length bs))) eqn:C; [| exact Hw].
    apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
    destruct (nth_error bs (Z.to_nat (bv_unsigned x - lo))) eqn:E; [discriminate|].
    apply nth_error_None in E. exfalso. lia.
  Qed.
  Hypothesis WR : wr_at asegs m lo n.
  Lemma wmono_ghost' : wmono asegs g m.
  Proof.
    intros x Hw. destruct (Z.le_gt_cases lo (bv_unsigned x)) as [L|L]; [destruct (Z.lt_ge_cases (bv_unsigned x) (lo + n)) as [R|R]|].
    - ndestruct WR as (_ & _ & W). specialize (W (bv_unsigned x - lo) ltac:(lia)). replace (lo + (bv_unsigned x - lo)) with (bv_unsigned x) in W by lia.
      unfold wa in W. rewrite Z_to_bv_bv_unsigned in W. exact W.
    - unfold wview in *. rewrite <- (ghost_out x ltac:(lia)). exact Hw.
    - unfold wview in *. rewrite <- (ghost_out x ltac:(lia)). exact Hw.
  Qed.

  (* [comment removed for export] *)
  Lemma mem_inv_ghost : mem_inv asegs m -> mem_inv asegs g.
  Proof.
    intros MI x b Hx. destruct (Z.le_gt_cases lo (bv_unsigned x)) as [L|L]; [destruct (Z.lt_ge_cases (bv_unsigned x) (lo + n)) as [R|R]|].
    - ndestruct WR as (_ & _ & W). specialize (W (bv_unsigned x - lo) ltac:(lia)). replace (lo + (bv_unsigned x - lo)) with (bv_unsigned x) in W by lia.
      unfold wa in W. rewrite Z_to_bv_bv_unsigned in W. unfold wview in W. unfold ro_addr.
      destruct (m x) as [b0|] eqn:E; [exact (MI x b0 E)|].
      destruct (find_segment asegs (bv_unsigned x) 1) as [seg|]; [| reflexivity]. destruct (seg_writable seg); [reflexivity| exfalso; apply W; reflexivity].
    - rewrite (ghost_out x ltac:(lia)) in Hx. exact (MI x b Hx).
    - rewrite (ghost_out x ltac:(lia)) in Hx. exact (MI x b Hx).
  Qed.

  (* [comment removed for export] *)
  Lemma u8arr_ghost : u8arr asegs g lo bs.
  Proof.
    split.
    - split; [exact LO0|]. split; [exact HI64|]. intros i Hi. unfold mrd. rewrite (ghost_in i Hi).
      destruct (nth_error bs i) eqn:E; [reflexivity|]. apply nth_error_None in E. lia.
    - eapply wr_at_transport; [exact WR| exact wmono_ghost].
  Qed.
End HCW.
(* [comment removed for export] *)
