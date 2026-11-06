(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr CellsX TacX Frame.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z46Stdlib6ZArith6BinInt1Zhc3addhc2le37Corelib4Init5Logicjf2orjf4True37Corelib4Init9Datatypeslf4list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~ne3ivlne6insidehc6of_natjf3and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~t85csizejf2eq04Npost84cellhc3pow35stdpp9bitvectorbdefinitionshj42bvlf4boollf3natlf6optionlf4truet8acells_size79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~ho18rw_cellshc3leblf6lengtht86cbytest87cell_wf79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib7StoreDj~~~~~~huaachunk_disj3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsij6cwrite_to_mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ind2waho18ro_cellsind8bytes_at79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~it55u8arrit54u8roit56u32arrhc3mulit56u64arrne5munchhua8chunk_inne3stk3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypejl47Segment" s.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition chunk_disj : ltac2:(zQ "10!h9>2A2$0>2s2$0>1A$0>1S$0P") := ltac2:(zQ "40!h9!j4!ja!l3\2A2$0\2s2$0\1A$0\1S$0@2$3@2$2@2$1^4^3^2@2$2@2$1^2^1^4").
Definition chunk_nodj : ltac2:(zQ "10!h9>2A2$0>2s2$0>1A$0>1S$0P") := ltac2:(zQ "20!h9!l8\2A2$0\2s2$0\1A$0\1S$0$1").
Definition chunk_in : ltac2:(zQ "30!h9!n7!ra>1W@1$1$2>1A$0>1S$0P") := ltac2:(zQ "40!h9!n7!s0!ra\1W@1$1$3\1A$0\1S$0@3$2^3^2^1").

Lemma inside_sub : ltac2:(zQ "60!h9!s0!j4!ja!n7!ra>1W@1$4$5>1A$0>1S$0>1k$0>1n$0>0@3$1^5^4^3>0@2$3Z^3>0@2$3@2$2^4^3^5@3$1^8@2$2^7^5^4").
Proof. induction W as [|[lo hi] W IH]; cbn; intros A S k n H Hk Hn; [exact H|]. destruct H as [H|H]; [left; lia| right; eauto]. Qed.

Section WithSegs.
  Variable segs : ltac2:(zQ "20!n7!jo9@1$0$1").

  Lemma tgt_bounds : ltac2:(zQ "h30!s9!j4!ja!t2!h9!hh4!hhc!hi1!hi7!hie!hl1!hl7!n7!hle!hm4!hmd!hn4!hrc!hs8>2mT>0@1$a@1$7#k0@1$e@1$a@1$7#8>1A$4>3csT@1$c$8>1S$4>2kn$d>2c'$8>0@4$h1?4segs^6^5^4>0@3$6$4@1$0@1$h0^5^4>0@3$6$b@2$h2@2$1@1$0^4@1$0@1$5^3^5$f@2$3@2$2Z^8@2$3@2$2@2$1^8^6@2$9+2+k0@2$3@2$2Z@2$1^8@1$0^5@2$3@2$2@2$1@2$1^8@1$0^5@1$0@1$5^4@2$9+2+k0@2$2@2$1@1$0^5@1$0@1$5^4^6").
  Proof. intros mT A csT S kn c' HT ES HK. apply Z.leb_le in HK. pose proof (rw_cells_bound segs mT A csT HT). lia. Qed.

  (* [comment removed for export] *)
  Lemma dj_core : ltac2:(zQ "h82!s9!j4!h9!hi1!ja!hl1!hse!t2!hhc!ht7!hi7!hl7!n7!hle!hm4!hmd!l3!hu0!hn4!hh4!hrc!ii8!hs8!hie&@1$0@2$6@1$5@1$3#8@1$9^8&@2$1@2$1^c@1$0^9~0>2mT>0@1$5@1$3#k0@1$e@1$5@1$3#8>1A$2>3csT@1$c$a>1S$2>2kn$d>2c'$a>2A2$2>2s2$2>0@4$h4?4segs^8^7^6>0@3$8$2@1$0@1$h2^7^6>0@3$8$b@2$h6@2$1@1$0^6@1$0@1$h3^5^7$f>0@1$h1^6>0@4$h5^6^5^b^9@2$7@2$4Z@2$1^c@1$0^9@2$7@2$4~1@2$h7+2+k0@2$h0@2$4@2$1^7^6@2$1^c@1$0^9@2$4~1^7").
  Proof.
    intros mT A csT S kn c' A2 s2 HT ES HK WF DJ. rewrite (cbytes_length c' WF).
    destruct (tgt_bounds mT A csT S kn c' HT ES HK) as (B1 & B2 & B3 & B4 & B5). unfold chunk_disj in DJ. lia.
  Qed.

  Lemma rw_cells_frame_dj : ltac2:(zQ "h51!h9!s9!hi1!hl1!hhc!hi7!hrc!n7!hm4!hn4!j4!hl7!hle!hmd!imd!ht7!hu0!hh4!ir7!ii8!hs8&>0@1$3@1$2#k0@1$8@1$3@1$2#8>2mT~0>1A$0>3csT@1$7$5>1S$0>2kn$c>2c'$5>1m~0>2A2$0>3cs2@1$7$5>2s2$0>0@4$6?4segs^a^9^8>0@3$4$0@1$1@1$9^9^8>0@3$4$b@2$h4@2$a@1$1^8@1$1@1$h1^7^9$d>0@1$h0^8>0@3$4$0@1$1@1$9^6^5>0@4$h3^8^6^e^c>0@4$6?4segs^a^9^8@4$6?4segs@3$e^b@1$h2@2$a^h0@1$1^d@1$f^c^a^9").
  Proof.
    intros mT A csT S kn c' m A2 cs2 s2 HT ES HK WF E2 DJ H. destruct (dj_core mT A csT S kn c' A2 s2 HT ES HK WF DJ) as (P1 & P2 & P3).
    apply rw_cells_frame; [exact H| exact P1| exact P2| rewrite E2; exact P3].
  Qed.
  Lemma ro_cells_frame_dj : ltac2:(zQ "h61!h9!s9!hi1!hl1!hhc!hi7!n7!hm4!hn4!ird!j4!hl7!hle!hmd!imd!ht7!hu0!hh4!ir7!hrc!ii8!hs8&>0@1$3@1$2#k0@1$7@1$3@1$2#8>2mT~0>1A$0>3csT@1$6$5>1S$0>2kn$c>2c'$5>1m~0>2A2$0>3cs2@1$6$5>2s2$0>0@4$h3?4segs^a^9^8>0@3$4$0@1$1@1$8^9^8>0@3$4$b@2$h5@2$a@1$1^8@1$1@1$h1^7^9$d>0@1$h0^8>0@3$4$0@1$1@1$8^6^5>0@4$h4^8^6^e^c>0@4$9?4segs^a^9^8@4$9?4segs@3$e^b@1$h2@2$a^h0@1$1^d@1$f^c^a^9").
  Proof.
    intros mT A csT S kn c' m A2 cs2 s2 HT ES HK WF E2 DJ H. destruct (dj_core mT A csT S kn c' A2 s2 HT ES HK WF DJ) as (P1 & P2 & P3).
    apply ro_cells_frame; [exact H| exact P1| exact P2| rewrite E2; exact P3].
  Qed.
  Lemma bytes_at_frame_dj : ltac2:(zQ "h71!hi1!h9!hl1!s9!hhc!n7!hm4!hi7!is9!j4!hl7!hse!hle!hmd!imd!ht7!hu0!hn4!hh4!ir7!hrc!ii8!hs8&>0@1$2@1$0#k0@1$6@1$2@1$0#8>2mT~0>1A$1>3csT@1$5$7>1S$1>2kn$c>2c'$7>1m~0>2A2$1>3bs2@1$5@1$2@1$0#8>2s2$1>0@4$h4?4segs^a^9^8>0@3$4$1@1$3@1$h1^9^8>0@3$4$a@2$h6@2$9@1$3^8@1$3@1$h2^7^9$d>0@1$h0^8>0@3$4$1@1$3@2$b@1$2@1$0#8^6^5>0@4$h5^8^6^e^c>0@4$8?4segs^a^9^8@4$8?4segs@3$e^b@1$h3@2$9^h0@1$3^d@1$f^c^a^9").
  Proof.
    intros mT A csT S kn c' m A2 bs2 s2 HT ES HK WF E2 DJ H. destruct (dj_core mT A csT S kn c' A2 s2 HT ES HK WF DJ) as (P1 & P2 & P3).
    apply bytes_at_write_other; [exact H| exact P1| exact P2| rewrite E2; exact P3].
  Qed.
  Lemma u8arr_frame_dj : ltac2:(zQ "h71!hi1!h9!hl1!s9!hhc!n7!hm4!jgf!hi7!j4!hl7!hse!hle!hmd!imd!ht7!hu0!hn4!hh4!ir7!hrc!ii8!hs8&>0@1$2@1$0#k0@1$6@1$2@1$0#8>2mT~0>1A$1>3csT@1$5$8>1S$1>2kn$c>2c'$8>1m~0>2A2$1>3bs2@1$5@1$2@1$0#8>2s2$1>0@4$h4?4segs^a^9^8>0@3$4$1@1$3@1$h1^9^8>0@3$4$a@2$h6@2$9@1$3^8@1$3@1$h2^7^9$d>0@1$h0^8>0@3$4$1@1$3@2$b@1$2@1$0#8^6^5>0@4$h5^8^6^e^c>0@4$7?4segs^a^9^8@4$7?4segs@3$e^b@1$h3@2$9^h0@1$3^d@1$f^c^a^9").
  Proof.
    intros mT A csT S kn c' m A2 bs2 s2 HT ES HK WF E2 DJ H. destruct (dj_core mT A csT S kn c' A2 s2 HT ES HK WF DJ) as (P1 & P2 & P3).
    apply u8arr_frame; [exact H| exact P1| exact P2| rewrite E2; exact P3].
  Qed.
  Lemma u8ro_frame_dj : ltac2:(zQ "h71!hi1!h9!hl1!s9!hhc!n7!hm4!jh8!hi7!j4!hl7!hse!hle!hmd!imd!ht7!hu0!hn4!hh4!ir7!hrc!ii8!hs8&>0@1$2@1$0#k0@1$6@1$2@1$0#8>2mT~0>1A$1>3csT@1$5$8>1S$1>2kn$c>2c'$8>1m~0>2A2$1>3bs2@1$5@1$2@1$0#8>2s2$1>0@4$h4?4segs^a^9^8>0@3$4$1@1$3@1$h1^9^8>0@3$4$a@2$h6@2$9@1$3^8@1$3@1$h2^7^9$d>0@1$h0^8>0@3$4$1@1$3@2$b@1$2@1$0#8^6^5>0@4$h5^8^6^e^c>0@4$7?4segs^a^9^8@4$7?4segs@3$e^b@1$h3@2$9^h0@1$3^d@1$f^c^a^9").
  Proof.
    intros mT A csT S kn c' m A2 bs2 s2 HT ES HK WF E2 DJ H. destruct (dj_core mT A csT S kn c' A2 s2 HT ES HK WF DJ) as (P1 & P2 & P3).
    apply u8ro_frame; [exact H| exact P1| exact P2| rewrite E2; exact P3].
  Qed.
  Lemma u32arr_frame_dj : ltac2:(zQ "h81!hi1!h9!hl1!s9!hhc!n7!hm4!ji0!hi7!j4!hl7!hse!hle!hmd!imd!ht7!hu0!hn4!hh4!ir7!hrc!ii8!hs8!jia&>0@1$2@1$0#k0@1$6@1$2@1$0#8>2mT~0>1A$1>3csT@1$5$8>1S$1>2kn$c>2c'$8>1m~0>2A2$1>2ws@1$5@1$2@1$0#k0>2s2$1>0@4$h4?4segs^a^9^8>0@3$4$1@1$3@1$h1^9^8>0@3$4$a@2$h6@2$9@1$3^8@1$3@1$h2^7^9$d>0@1$h0^8>0@3$4$1@2$h7+4@1$3@2$b@1$2@1$0#k0^6^5>0@4$h5^8^6^e^c>0@4$7?4segs^a^9^8@4$7?4segs@3$e^b@1$h3@2$9^h0@1$3^d@1$f^c^a^9").
  Proof.
    intros mT A csT S kn c' m A2 ws s2 HT ES HK WF E2 DJ H. destruct (dj_core mT A csT S kn c' A2 s2 HT ES HK WF DJ) as (P1 & P2 & P3).
    apply u32arr_frame; [exact H| exact P1| exact P2| rewrite E2; exact P3].
  Qed.
  Lemma u64arr_frame_dj : ltac2:(zQ "h81!hi1!h9!hl1!s9!hhc!n7!hm4!jj0!hi7!j4!hl7!hse!hle!hmd!imd!ht7!hu0!hn4!hh4!ir7!hrc!ii8!hs8!jia&>0@1$2@1$0#k0@1$6@1$2@1$0#8>2mT~0>1A$1>3csT@1$5$8>1S$1>2kn$c>2c'$8>1m~0>2A2$1>2ws@1$5@1$2@1$0#k0>2s2$1>0@4$h4?4segs^a^9^8>0@3$4$1@1$3@1$h1^9^8>0@3$4$a@2$h6@2$9@1$3^8@1$3@1$h2^7^9$d>0@1$h0^8>0@3$4$1@2$h7+8@1$3@2$b@1$2@1$0#k0^6^5>0@4$h5^8^6^e^c>0@4$7?4segs^a^9^8@4$7?4segs@3$e^b@1$h3@2$9^h0@1$3^d@1$f^c^a^9").
  Proof.
    intros mT A csT S kn c' m A2 ws s2 HT ES HK WF E2 DJ H. destruct (dj_core mT A csT S kn c' A2 s2 HT ES HK WF DJ) as (P1 & P2 & P3).
    apply u64arr_frame; [exact H| exact P1| exact P2| rewrite E2; exact P3].
  Qed.
  Lemma munch_write_in : ltac2:(zQ "h71!hi1!hl1!s9!hm4!h9!n7!hhc!hi7!jja!j4!hl7!hle!hmd!imd!ht7!hu0!hn4!hh4!ra!ir7!hrc!jk2!hs8&>0@1$1@1$0#k0@1$3@1$1@1$0#8>2mT~0>1A$4>3csT@1$5$7>1S$4>2kn$b>2c'$7>1W@1$5$h2>2m0~0>1m~0>0@4$h4?4segs^9^8^7>0@3$6$4@1$2@1$h0^8^7>0@3$6$a@2$h6@2$9@1$2^7@1$2@1$h1^6^8$c>0@1$f^7>0@3$h5^7^c^a>0@3$8^8^7^6@3$8^9^8@3$d^7@1$h3@2$9^e@1$2^b@1$e^a").
  Proof.
    intros mT A csT S kn c' W m0 m HT ES HK WF IN H.
    destruct (tgt_bounds mT A csT S kn c' HT ES HK) as (B1 & B2 & B3 & B4 & B5).
    apply munch_write; [exact H| exact B3| rewrite (cbytes_length c' WF); exact B4|].
    rewrite (cbytes_length c' WF). apply (inside_sub W A S); [exact IN| lia| exact B5].
  Qed.
  Lemma stk_write_in : ltac2:(zQ "h51!h9!hi1!s9!hl1!hm4!hhc!hi7!jke!j4!hl7!n7!hle!hmd!imd!ht7!hu0!hn4!hh4!ir7!hrc!hs8&>0@1$3@1$1#k0@1$4@1$3@1$1#8>2mT~0>1A$0>3csT@1$a$6>1S$0>2kn$b>2c'$6>1m~0>2lo$0>2hi$0>0@4$h3?4segs^9^8^7>0@3$5$0@1$2@1$h0^8^7>0@3$5$9@2$h4@2$8@1$2^7@1$2@1$h1^6^8$c>0@1$f^7>0@4$7?4segs^7^6^5@4$7?4segs@3$d^8@1$h2@2$8^d@1$2^a@1$e^9^7^6").
  Proof.
    intros mT A csT S kn c' m lo hi HT ES HK WF H.
    destruct (tgt_bounds mT A csT S kn c' HT ES HK) as (B1 & B2 & B3 & B4 & B5).
    apply stk_write; [exact H| exact B3| rewrite (cbytes_length c' WF); exact B4].
  Qed.
End WithSegs.

(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Module N8Lit.
  Import Ltac2.
  Ltac2 rec nat_lit (t : constr) : bool :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.Constructor _ _ => Constr.equal t 'O
    | Constr.Unsafe.App f args =>
        if Constr.equal f 'S then (if Int.equal (Array.length args) 1 then nat_lit (Array.get args 0) else false) else false
    | _ => false
    end.
  Ltac2 cell_lit (c : constr) : bool :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.App f args =>
        if Constr.equal f 'C8 then true else if Constr.equal f 'C4 then true else if Constr.equal f 'C2 then true
        else if Constr.equal f 'C1 then true
        else if Constr.equal f 'CB then (if Int.equal (Array.length args) 2 then nat_lit (Array.get args 0) else false)
        else false
    | _ => false
    end.
  (* [comment removed for export] *)
  Ltac2 rec list_lit (chk : constr -> bool) (l : constr) : bool :=
    match Constr.Unsafe.kind l with
    | Constr.Unsafe.App f args =>
        if Int.equal (Array.length args) 3 then
          (if Constr.equal f '@cons then (if chk (Array.get args 1) then list_lit chk (Array.get args 2) else false) else false)
        else if Int.equal (Array.length args) 1 then Constr.equal f '@nil
        else false
    | _ => false
    end.
  Ltac2 cells_lit (cs : constr) : unit := if list_lit cell_lit cs then () else Control.zero (Tactic_failure None).
  Ltac2 plain_list_lit (l : constr) : unit := if list_lit (fun _ => true) l then () else Control.zero (Tactic_failure None).
End N8Lit.
Ltac n8_cells_lit cs := let f := ltac2:(c |- N8Lit.cells_lit (Option.get (Ltac1.to_constr c))) in f cs.
Ltac n8_list_lit l := let f := ltac2:(c |- N8Lit.plain_list_lit (Option.get (Ltac1.to_constr c))) in f l.

Ltac dj_size_cells cs :=
  match goal with
  | _ => let _ := constr:(ltac:(n8_cells_lit cs; exact I) : True) in eval lazy in (Z.of_nat (cells_size cs))
  | _ => constr:(Z.of_nat (cells_size cs))
  end.
Ltac dj_size_len t xs :=      (* [comment removed for export] *)
  match goal with
  | _ => let _ := constr:(ltac:(n8_list_lit xs; exact I) : True) in eval lazy in t
  | _ => t
  end.

(* [comment removed for export] *)

Definition chunk_noin : ltac2:(zQ "30!h9!n7!ra>1W@1$1$2>1A$0>1S$0P") := ltac2:(zQ "40!h9!n7!l8!ra\1W@1$1$3\1A$0\1S$0$2").

(* [comment removed for export] *)
Ltac dj_ensure A2 s2 A S :=
  lazymatch goal with
  | _ : chunk_disj A2 s2 A S |- _ => idtac
  | _ : chunk_nodj A2 s2 A S |- _ => idtac
  | _ => let DJ := fresh "DJc" in
         first [ assert (DJ : chunk_disj A2 s2 A S) by (unfold chunk_disj; simpl_arr_sizes; simpl_sizes; lia)
               | pose proof (I : chunk_nodj A2 s2 A S) as DJ ]
  end.
Ltac in_ensure W A S :=
  lazymatch goal with
  | _ : chunk_in W A S |- _ => idtac
  | _ : chunk_noin W A S |- _ => idtac
  | _ => let DJ := fresh "INc" in
         first [ assert (DJ : chunk_in W A S) by (unfold chunk_in; cbn [inside]; lia)
               | pose proof (I : chunk_noin W A S) as DJ ]
  end.

(* [comment removed for export] *)
Ltac tc1_orig_rw segs m a bs H A2 cs2 :=
  first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
        | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ].
Ltac tc1_orig_ro segs m a bs H A2 cs2 :=
  first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
        | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ].
Ltac tc1_orig_ba segs m a bs H A2 bs2 :=
  first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H; [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
        | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ].
Ltac tc1_orig_u8 segs m a bs H A2 xs :=
  first [ apply (u8arr_frame segs m A2 xs a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
        | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ].
Ltac tc1_orig_u32 segs m a bs H A2 xs :=
  first [ apply (u32arr_frame segs m A2 xs a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
        | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ].
Ltac tc1_orig_u64 segs m a bs H A2 xs :=
  first [ apply (u64arr_frame segs m A2 xs a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
        | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ].
Ltac tc1_orig_u8ro segs m a bs H A2 xs :=
  first [ apply (u8ro_frame segs m A2 xs a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
        | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ].

(* [comment removed for export] *)
Ltac transport_chunks_dj segs m a bs mT A csT S kn c' HT ES HK :=
  repeat match goal with
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      let s2 := dj_size_cells cs2 in
      dj_ensure A2 s2 A S;
      lazymatch goal with
      | DJ : chunk_disj A2 s2 A S |- _ =>
          apply (rw_cells_frame_dj segs mT A csT S kn c' m A2 cs2 s2 HT ES HK I (@eq_refl Z s2) DJ) in H
      | _ => transport_chunk1_default segs m a bs H ltac:(tc1_orig_rw segs m a bs H A2 cs2)   (* [comment removed for export] *)
      end
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      let s2 := dj_size_cells cs2 in
      dj_ensure A2 s2 A S;
      lazymatch goal with
      | DJ : chunk_disj A2 s2 A S |- _ =>
          apply (ro_cells_frame_dj segs mT A csT S kn c' m A2 cs2 s2 HT ES HK I (@eq_refl Z s2) DJ) in H
      | _ => transport_chunk1_default segs m a bs H ltac:(tc1_orig_ro segs m a bs H A2 cs2)   (* [comment removed for export] *)
      end
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      let s2 := dj_size_len (Z.of_nat (length bs2)) bs2 in
      dj_ensure A2 s2 A S;
      lazymatch goal with
      | DJ : chunk_disj A2 s2 A S |- _ =>
          apply (bytes_at_frame_dj segs mT A csT S kn c' m A2 bs2 s2 HT ES HK I (@eq_refl Z s2) DJ) in H
      | _ => transport_chunk1_default segs m a bs H ltac:(tc1_orig_ba segs m a bs H A2 bs2)   (* [comment removed for export] *)
      end
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : u8arr segs m ?A2 ?xs |- _ =>
      let s2 := dj_size_len (Z.of_nat (length xs)) xs in
      dj_ensure A2 s2 A S;
      lazymatch goal with
      | DJ : chunk_disj A2 s2 A S |- _ =>
          apply (u8arr_frame_dj segs mT A csT S kn c' m A2 xs s2 HT ES HK I (@eq_refl Z s2) DJ) in H
      | _ => transport_chunk1_default segs m a bs H ltac:(tc1_orig_u8 segs m a bs H A2 xs)   (* [comment removed for export] *)
      end
  | H : u32arr segs m ?A2 ?xs |- _ =>
      let s2 := dj_size_len (4 * Z.of_nat (length xs)) xs in
      dj_ensure A2 s2 A S;
      lazymatch goal with
      | DJ : chunk_disj A2 s2 A S |- _ =>
          apply (u32arr_frame_dj segs mT A csT S kn c' m A2 xs s2 HT ES HK I (@eq_refl Z s2) DJ) in H
      | _ => transport_chunk1_default segs m a bs H ltac:(tc1_orig_u32 segs m a bs H A2 xs)   (* [comment removed for export] *)
      end
  | H : u64arr segs m ?A2 ?xs |- _ =>
      let s2 := dj_size_len (8 * Z.of_nat (length xs)) xs in
      dj_ensure A2 s2 A S;
      lazymatch goal with
      | DJ : chunk_disj A2 s2 A S |- _ =>
          apply (u64arr_frame_dj segs mT A csT S kn c' m A2 xs s2 HT ES HK I (@eq_refl Z s2) DJ) in H
      | _ => transport_chunk1_default segs m a bs H ltac:(tc1_orig_u64 segs m a bs H A2 xs)   (* [comment removed for export] *)
      end
  | H : u8ro segs m ?A2 ?xs |- _ =>
      let s2 := dj_size_len (Z.of_nat (length xs)) xs in
      dj_ensure A2 s2 A S;
      lazymatch goal with
      | DJ : chunk_disj A2 s2 A S |- _ =>
          apply (u8ro_frame_dj segs mT A csT S kn c' m A2 xs s2 HT ES HK I (@eq_refl Z s2) DJ) in H
      | _ => transport_chunk1_default segs m a bs H ltac:(tc1_orig_u8ro segs m a bs H A2 xs)   (* [comment removed for export] *)
      end
  | MU : munch ?Wq ?mq m |- _ =>
      in_ensure Wq A S;
      lazymatch goal with
      | IN : chunk_in Wq A S |- _ => apply (munch_write_in segs mT A csT S kn c' Wq mq m HT ES HK I IN) in MU
      | _ => footprint_after_store segs m a bs   (* [comment removed for export] *)
      end
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | STq : stk segs m ?loq ?hiq |- _ => apply (stk_write_in segs mT A csT S kn c' m loq hiq HT ES HK I) in STq
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac transport_chunks_n8 segs m a bs :=
  first
    [ lazymatch a with
      | (?A + Z.of_nat ?kn)%Z =>
        lazymatch bs with
        | cbytes ?c' =>
          lazymatch goal with
          | HT : rw_cells segs (write_to_mem m (wa a) bs) A ?csT |- _ =>
              let S := dj_size_cells csT in
              is_Zlit S;
              let ES := fresh "TCs" in let HK := fresh "TCk" in
              assert (ES : Z.of_nat (cells_size csT) = S) by reflexivity;
              assert (HK : (Z.of_nat kn + Z.of_nat (csize c') <=? S) = true) by reflexivity;
              transport_chunks_dj segs m a bs (write_to_mem m (wa a) bs) A csT S kn c' HT ES HK;
              clear ES HK
          end
        end
      end
    | transport_chunks_default segs m a bs ].
(* [comment removed for export] *)
