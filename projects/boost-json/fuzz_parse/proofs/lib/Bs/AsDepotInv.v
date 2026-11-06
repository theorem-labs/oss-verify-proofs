(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require As0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr ZBridge CellsX TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z46Stdlib6ZArith6BinInt1Zhc4land79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsaAsDepotInv~~~~~~jb6bucket37Corelib4Init5Logico43andhc2lehc2lthc3powjb5depotjb7d_chainjb6d_hashjb9find_hashhc3add37Corelib4Init9Datatypestb4booljb5d_idshc3eqbtb4constb4listjb8d_framesjb4d_nbjb4d_sbjb7mkDepotjb6d_findjb8d_inserttb3nat37Corelib5Lists7ListDefhl33maphl33seqhc6of_nathc6to_natjb5idseq04Npos35stdpp9bitvectorbdefinitionshp82bvtb6option89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsaAsDepotInv5Cells~~~~~~hs49depot_memjb4d_wf79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~ihe3ivltb4prodtb4pairhc3multb3nilo43iff36Stdlib5Lists4Listio12Ino42eqo42exjb3d_Ko43nottb3appio12hdjb7link_ofio15NoDup79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~isf5u8arrtb6lengthtb4true3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsji28store_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~jm52waji2cwrite_to_memjm59upd_bytestb4Someji2dov_read_bytesjm58bytes_atio19nth_errorhc3opphp88bv_swrapisf6u64arrisf4u64s3h5LinuxProcessSemanticsfLinuxProcessSem6BvBasekh7dZ_to_le_bytes37Corelib4Init3Natkl73addhc6shiftr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~kn92wzjm53le4jm53le879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~ks84cellks82C479OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~lh28rw_cellsks82C8jb9depot_memihe5munchihe5wmono89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsaAsDepotInvaDepotFrame~~~~~~lnd5put_Whc3sub3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypelt77Segment" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Notation DEP        := 2748504 (only parsing).   (* [comment removed for export] *)
Notation DEP_NUI    := 6942808 (only parsing).   (* [comment removed for export] *)
Notation DEP_MAP1   := 6942824 (only parsing).   (* [comment removed for export] *)
Notation SSB        := 2682952 (only parsing).   (* [comment removed for export] *)
Notation SSB_DATA   := 2682968 (only parsing).   (* [comment removed for export] *)
Notation SSB_STORED := 2682976 (only parsing).   (* [comment removed for export] *)
Notation LIM_IDS    := 65536 (only parsing).     (* [comment removed for export] *)
Notation LIM_FRAMES := 32768 (only parsing).     (* [comment removed for export] *)
Notation MASK20     := 1048575 (only parsing).
Definition bucket : ltac2:(zQ "10!h9>1h$0$0") := ltac2:(zQ "20!h9!j4\1h$0@2$1^1+vvvvf").

Lemma bucket_range : ltac2:(zQ "60!nb!p8!h9!pe!q3!q8>1h$2@2$1@2$3Z@1$0^1@2$4@1$0^1@2$5+2+h4").
Proof.
  intros h. unfold bucket. change 1048575 with (Z.ones 20). rewrite Z.land_ones by lia.
  apply Z.mod_pos_bound. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record depot : Type := mkDepot {
  d_ids : Z; d_frames : Z; d_hash : Z -> Z; d_chain : Z -> list Z; d_nb : Z; d_sb : Z }.

(* [comment removed for export] *)
Fixpoint link_of (l : list Z) (id : Z) : Z :=
  match l with
  | [] => 0
  | x :: rest => if x =? id then hd 0 rest else link_of rest id
  end.

(* [comment removed for export] *)
Fixpoint find_hash (hs : Z -> Z) (h : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: rest => if hs x =? h then x else find_hash hs h rest
  end.

Definition d_find : ltac2:(zQ "20!h9!qe>1d$1>1h$0$0") := ltac2:(zQ "60!h9!nb!r6!s0!qe!s9\1d$4\1h$0@3$5@1$3^2^1@2$2^2@1$1^1").

Definition d_insert : ltac2:(zQ "20!h9!qe>1d$1>1h$0>1n$0$1") := ltac2:(zQ "f0!h9!t5!v3!va!r6!hg2!hg8!hgf!nb!hh6!s0!hi1!hi8!qe!hif\1d$d\1h$0\1n$0@6$e@2$1@1$3^3+1@2$1@2$1@1$9^3^1+1\2id$0M2\0$2$0@2$5^1@2$1@1$3^4+1^3@2$a^4^1\1b$0M2\0$2@1$7$0@2$5^1@1$8^3@3$6$0@2$1@1$3^4+1@2$4^4^1@2$4^4^1@1$b^3@1$c^3").

(* [comment removed for export] *)
Definition d_put : ltac2:(zQ "20!h9!qe>1d$1>1h$0>1n$0$1") := ltac2:(zQ "60!v3!h9!qe!hj9!hk2!hg2\1d$2\1h$1\1n$1M0\0$0$2@2$5@2$3^3^2Z@3$4^3^2^1^3").
Definition d_putid : ltac2:(zQ "20!h9!qe>1d$1>1h$0$0") := ltac2:(zQ "70!v3!h9!hj9!va!qe!t5!hg2\1d$4\1h$1M0\0$0$1@2$6@2$2^2^1Z@2$5@1$3^2+1@2$2^2^1").

(* [comment removed for export] *)
Definition idseq : ltac2:(zQ "20!h9!hgf>1k$0@1$1$0") := ltac2:(zQ "60!h9!hkd!hma!hn1!hn8!ho1\1k$0@4$2$1$0$4@2$3N1@1$5^1").
Definition d_K : ltac2:(zQ "30!hgf!h9!qe>1d$2@1$0$1") := ltac2:(zQ "60!h9!hma!s0!va!qe!hoa\1d$4@4$1$0$0@1$2^1@1$5@1$3^1").

Record d_wf (d : depot) : Prop := mkWf {
  wf_ids    : 1 <= d_ids d < LIM_IDS;
  wf_frames : 0 <= d_frames d <= LIM_FRAMES;
  wf_hash   : forall id, 1 <= id <= d_ids d -> 0 <= d_hash d id < 2^64;
  wf_in     : forall id, 1 <= id <= d_ids d -> In id (d_chain d (bucket (d_hash d id)));
  wf_chain  : forall b id, In id (d_chain d b) -> 1 <= id <= d_ids d /\ bucket (d_hash d id) = b;
  wf_nodup  : forall b, List.NoDup (d_chain d b);
  wf_nb     : AIMG_TOP <= d_nb d /\ d_nb d + 16 * LIM_IDS <= 2^47;
  wf_sb     : AIMG_TOP <= d_sb d /\ d_sb d + 8 * LIM_FRAMES <= 2^47;
  wf_nbsb   : d_nb d + 16 * LIM_IDS <= d_sb d \/ d_sb d + 8 * LIM_FRAMES <= d_nb d
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Cells.
Variable segs : ltac2:(zQ "20!hgf!mgc@1$0$1").

Record depot_mem (d : depot) (m : word -> option byte) : Prop := mkDM {
  dm_tab   : forall b, 0 <= b < 2^20 -> rw_cells segs m (DEP + 4 * b) [C4 (wz (hd 0 (d_chain d b)))];
  dm_nui   : rw_cells segs m DEP_NUI [C4 (wz (d_ids d))];
  dm_map1  : rw_cells segs m DEP_MAP1 [C8 (wz (d_nb d))];
  dm_node  : forall id, 1 <= id <= d_ids d ->
               rw_cells segs m (d_nb d + 16 * id) [C8 (wz (d_hash d id)); C4 (wz (link_of (d_chain d (bucket (d_hash d id))) id))];
  dm_sid   : forall id, 1 <= id <= d_ids d -> exists sid, rw_cells segs m (d_nb d + 16 * id + 12) [C4 sid];
  dm_free  : forall id, d_ids d < id < LIM_IDS -> exists j1 j2 j3, rw_cells segs m (d_nb d + 16 * id) [C8 j1; C4 j2; C4 j3];
  dm_tf    : rw_cells segs m SSB [C8 (wz (d_frames d))];
  dm_data  : rw_cells segs m SSB_DATA [C8 (wz (d_sb d))];
  dm_stored: rw_cells segs m SSB_STORED [C4 (wz (d_frames d))];
  dm_space : exists junk, u8arr segs m (d_sb d + 8 * d_frames d) junk /\ Z.of_nat (length junk) = 8 * (LIM_FRAMES - d_frames d)
}.

Definition DEPOT : ltac2:(zQ "40!hp2!hr5!hrb!qe>1d$3>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8P") := ltac2:(zQ "70!hp2!hr5!hrb!p8!iga!ih7!qe\1d$6\1m>0@1$1@1$0#k0@1$2@1$1@1$0#8@2$3@1$5^2@2$4^2^1").

(* [comment removed for export] *)
Definition depot_W : ltac2:(zQ "30!hgf!qe!ila>1d$1@1$0$2") := ltac2:(zQ "a0!h9!im1!hg8!im8!t5!hi1!hi8!imf!in5!qe\1d$9@3$2@2$1$0$0@4$3$0$0+ipvgl8@2$4+mpvgm8+8@3$2@2$1$0$0@4$3$0$0+iovgk8@2$4+iovgk8+hc@3$2@2$1$0$0@4$3$0$0@1$5^1@2$4@1$5^1@2$7+h0+hggg0@3$2@2$1$0$0@4$3$0$0@1$6^1@2$4@1$6^1@2$7+8+ogg0@1$8@2$1$0$0").

End Cells.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_idseq : ltac2:(zQ "60!h9!pe!p8!inb!hoa!ip4>1k$0>2id$0@2$3@3$5$0^1@1$4^2@2$2@2$1+1^1@2$1^1^2").
Proof.
  intros k id. unfold idseq. rewrite in_map_iff. split.
  - (intros nd_i1; ndestruct nd_i1 as (x & <- & Hx)). apply in_seq in Hx. lia.
  - intros H. exists (Z.to_nat id). split; [lia|]. apply in_seq. lia.
Qed.

Lemma in_d_K : ltac2:(zQ "b0!h9!p8!pe!ipa!ipf!inb!iq4!s0!va!qe!ip4>1d$9>1h$0@2$5@3$a$0^1@1$6^2@2$4$0\2id$0@2$1@2$1@2$2+1^1@2$2^1@1$8^3@3$3$0@2$7^3^1^2").
Proof.
  intros d h. unfold d_K. rewrite in_map_iff. split.
  - (intros nd_i2; ndestruct nd_i2 as (id & E & Hin)). apply in_idseq in Hin. exists id. auto.
  - (intros nd_i3; ndestruct nd_i3 as (id & Hid & E)). exists id. split; [exact E|]. apply in_idseq. exact Hid.
Qed.

Lemma find_hash_some : ltac2:(zQ "70!h9!s9!ipa!iqa!ip4!hgf!p8>2hs>0$0$0>1h$0>1l@1$5$0>0@1$3@3$2$0@3$1^3^2^1Z>0@1$3@3$4$0Z^2@2$6@3$4$0@3$1^5^4^3^3@3$2$0@1^5@3$1^5^4^3^4").
Proof.
  induction l as [|x l IH]; intros H N0; cbn in *. { congruence. }
  destruct (Z.eqb_spec (hs x) h).
  - auto.
  - destruct (IH H) as [A B]. { tauto. } auto.
Qed.

Lemma find_hash_none : ltac2:(zQ "60!h9!ipa!iqa!ip4!hgf!s9>2hs>0$0$0>1h$0>1l@1$4$0>0@3$1$0@3$5^3^2^1Z>0@1$2@3$3$0Z^2>1x$0>0@3$3$0^1^4@1$2@3$1$0@1^7^2^6").
Proof.
  induction l as [|y l IH]; intros H N0 x Hx; cbn in *. { tauto. }
  destruct (Z.eqb_spec (hs y) h). { subst. exfalso. tauto. }
  destruct Hx as [<-|Hx]; [assumption|]. apply IH; tauto.
Qed.

Lemma find_hash_app_skip : ltac2:(zQ "70!h9!hgf!ipa!s9!ir0!iqa!ip4>2hs>1x$0$0>1h$0>2l1@1$1$0>2l2@1$1$0>0>1x$0>0@3$6$0^1^3@1$5@3$2$0@1^6^2^5@3$2$0@3$3^5^4@3$4$0^3^2@3$3^5^4^2").
Proof.
  induction l1 as [|x l1 IH]; intros l2 H; cbn. { reflexivity. }
  destruct (Z.eqb_spec (hs x) h). { exfalso. apply (H x); cbn; auto. }
  apply IH. intros y Hy. apply H. cbn; auto.
Qed.

Lemma chain_no0 : ltac2:(zQ "60!h9!iqa!r6!ih7!qe!ip4>1d$4>1b$0>0@1$3^2@1$1@3$5$0Z@2$2^3^2").
Proof. intros d b W H. pose proof (wf_chain d W b 0 H). lia. Qed.

Lemma d_find_K : ltac2:(zQ "90!h9!ipa!inb!iqa!iq4!hj9!ih7!qe!ip4>1d$7>1h$0>0@1$6^2@2$2@1$3@3$1$0@2$5^3^2Z@3$8$0^2@1$4^3").
Proof.
  intros d h W. unfold d_find. split.
  - intros H. destruct (find_hash_some _ _ _ H (chain_no0 d _ W)) as [A B].
    apply in_d_K. exists (find_hash (d_hash d) h (d_chain d (bucket h))). split; [|exact B].
    apply (wf_chain d W (bucket h)). exact A.
  - intros H E. apply in_d_K in H. ndestruct H as (id & Hid & Hh).
    pose proof (wf_in d W id Hid) as I. rewrite Hh in I.
    exact (find_hash_none _ _ _ E (chain_no0 d _ W) id I Hh).
Qed.

Lemma d_find_range : ltac2:(zQ "a0!hj9!h9!p8!ipa!pe!iqa!s0!va!ih7!qe>1d$9>1h$1>0@1$8^2>0@1$5@3$3$1@2$0^3^2Z@2$2@2$2@2$4+1@2$0^4^3@2$4@2$0^4^3@1$7^4@3$3$1@2$6^4@2$0^4^3^3").
Proof.
  intros d h W H. unfold d_find in *. destruct (find_hash_some _ _ _ H (chain_no0 d _ W)) as [A B].
  split; [|exact B]. apply (wf_chain d W (bucket h)). exact A.
Qed.

Lemma chain_hd_range : ltac2:(zQ "80!h9!r6!ir6!pe!p8!va!ih7!qe>1d$7>1b$0>0@1$6^2@2$4@2$3Z@3$2$0Z@2$1^3^2@2$3@3$2$0Z@2$1^3^2@1$5^3").
Proof.
  intros d b W. destruct (d_chain d b) as [|x l] eqn:E; cbn. { pose proof (wf_ids d W). lia. }
  assert (In x (d_chain d b)) by (rewrite E; left; reflexivity). pose proof (wf_chain d W b x H). lia.
Qed.

Lemma link_of_app : ltac2:(zQ "90!h9!hgf!ir0!hg8!ipa!iqa!irc!ip4!ir6>2l1@1$1$0>1i$0>2l2@1$1$0>0@1$5@3$7$0^2^3@3$4$0@2$6@3$2$0^4@3$3$0^3^2^3@3$8$0Z^2").
Proof.
  induction l1 as [|x l1 IH]; intros i l2 H; cbn. { rewrite Z.eqb_refl. reflexivity. }
  destruct (Z.eqb_spec x i). { exfalso. apply H. cbn. auto. }
  apply IH. intros I. apply H. cbn. auto.
Qed.

Lemma link_of_cons_other : ltac2:(zQ "60!h9!ipa!irc!hg8!hgf!iqa>1x$0>1l@1$4$0>1i$0>0@1$5@3$1$0^3^1@3$1$0@2$2@3$3$0^4^3^2@2$2^3^2").
Proof. intros. cbn. destruct (Z.eqb_spec x i); [contradiction|reflexivity]. Qed.

Lemma NoDup_app_cons : ltac2:(zQ "80!h9!ir0!hgf!is6!hg8!p8!iqa!ip4>2l1@1$2$0>1x$0>2l2@1$2$0>0@2$3$0@3$1$0^3@3$4$0^2^1@2$5@1$6@3$7$0^3^4@2$3$0@3$1$0^4^2").
Proof.
  intros l1 x l2 H. split.
  - intros I. apply NoDup_remove_2 in H. apply H. apply in_or_app. auto.
  - apply NoDup_remove_1 in H. exact H.
Qed.

(* [comment removed for export] *)
Lemma d_insert_wf : ltac2:(zQ "d0!h9!t5!pe!ih7!q3!p8!ipa!hj9!hh6!va!hk2!qe!q8>1d$b>1h$0>1n$0>0@1$3^3>0@3$6$0@2$7^4^3Z>0@2$5@2$2Z^4@2$4^4@2$c+2+k0>0@2$2Z^4>0@2$4@2$1@1$9^7+1+hggg0>0@2$2@2$1@2$1@1$8^8^6+1+ogg0@1$3@3$a^9^8^7").
Proof.
  intros d h n W NF Hh Hn CI CF. pose proof W as [I1 I2 I3 I4 I5 I6 I7 I8 I9].
  constructor; cbn; try assumption; try lia.
  - intros id Hid. destruct (Z.eqb_spec id (d_ids d + 1)); [lia|]. apply I3. lia.
  - intros id Hid. destruct (Z.eqb_spec id (d_ids d + 1)).
    + rewrite Z.eqb_refl. cbn. auto.
    + destruct (Z.eqb_spec (bucket (d_hash d id)) (bucket h)); [cbn; right|]; apply I4; lia.
  - intros b id Hin. destruct (Z.eqb_spec b (bucket h)).
    + destruct Hin as [<-|Hin]. { rewrite Z.eqb_refl. lia. }
      pose proof (I5 b id Hin) as [A B]. destruct (Z.eqb_spec id (d_ids d + 1)); lia.
    + pose proof (I5 b id Hin) as [A B]. destruct (Z.eqb_spec id (d_ids d + 1)); lia.
  - intros b. destruct (Z.eqb_spec b (bucket h)); [|apply I6].
    constructor; [|apply I6]. intros Hin. pose proof (I5 b _ Hin). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MemHelpers.
Variable segs : ltac2:(zQ "20!hgf!mgc@1$0$1").

Lemma u8arr_app : ltac2:(zQ "c0!hp2!hr5!jg9!hgf!ir0!jh2!hrb!p8!inb!h9!t5!hn8>1m>0@1$1@1$0#k0@1$6@1$1@1$0#8>1A$9>3bs1@1$3@1$1@1$0#8>3bs2@1$3@1$1@1$0#8@2$8@4$2?4segs^4^3@3$4@1$1@1$0#8^2^1@2$7@4$2?4segs^4^3^2@4$2?4segs^4@2$a^3@1$b@2$5@1$1@1$0#8^2^1").
Proof.
  intros m A bs1 bs2. unfold u8arr. rewrite length_app, Nat2Z.inj_add, bytes_at_app, wr_at_app by lia. tauto.
Qed.

(* [comment removed for export] *)
Lemma u8arr_store_ok_n : ltac2:(zQ "h00!hp2!hr5!ipa!h9!t5!pe!hn8!v3!jh2!hgf!hkd!hrb!jhb!jl9!jg9!jpf>1m>0@1$1@1$0#k0@1$b@1$1@1$0#8>1A$3>2bs@1$9@1$1@1$0#8>1i$3>1k$a>1a@1$1@1$0#k0>0@4$e?4segs^6^5^4>0@2$5Z^4>0@2$5@2$4^5@1$6^4@1$6@2$8@1$1@1$0#8^6>0@3$2@1$1@1$0#k0^4@1$f@2$4^8^6@3$2$7@4$d?4segs^a^5^6$c").
Proof. intros m A bs i k a [_ Hw] Hi Hk ->. eapply wr_at_store_ok; eauto. Qed.

Lemma u8arr_write_n : ltac2:(zQ "e0!hp2!hr5!jh2!hgf!h9!jg9!t5!pe!hn8!hrb!jq5!jr5!jpf!ho1>1m>0@1$1@1$0#k0@1$9@1$1@1$0#8>1A$4>2bs@1$3@1$1@1$0#8>1i$4>2xs@1$3@1$1@1$0#8>0@4$5?4segs^5^4^3>0@2$7Z^3>0@2$7@2$6^4@1$8@2$2@1$1@1$0#8^3@1$8@2$2@1$1@1$0#8^5@4$5?4segs@3$a^8@1$c@2$6^7^5^4^7@3$b^6@1$d^5^4").
Proof.
  intros m A bs i xs [Hb Hw] Hi Hl. split.
  - apply bytes_at_write_inside; [exact Hb|lia|lia].
  - rewrite upd_bytes_length by lia. apply wr_at_write. exact Hw.
Qed.

Lemma bytes_at_read1 : ltac2:(zQ "h00!hp2!hr5!hgf!hrb!ipa!js2!h9!hg8!in5!js9!jta!jpf!ju6!t5!pe!ho1>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1A$6>2bs@1$2@1$1@1$0#8>1k$6>1b@1$1@1$0#8>1a@1$1@1$0#k0>0@4$a?4segs^6^5^4>0@3$4@1$3@1$1@1$0#8@3$c@1$1@1$0#8^5@1$f^4@2$5@1$1@1$0#8^3>0@2$eZ^5>0@3$4@1$1@1$0#k0^4@1$b@2$d^8^6@3$4@1$3@1$2@1$1@1$0#8@4$9?4segs^a^5N1@2$5@1$2@1$1@1$0#8@3$7@1$1@1$0#8^6@1$8@1$1@1$0#8").
Proof.
  intros m A bs k b a Hb Hn Hk ->. rewrite (bytes_at_read segs m A bs k 1 Hb Hk).
  2:{ pose proof (nth_error_lt _ _ _ Hn). lia. }
  f_equal. ndestruct (nth_error_split bs (Z.to_nat k) b Hn) as (l1 & l2 & -> & L).
  rewrite skipn_app, skipn_all2, L, Nat.sub_diag by lia. reflexivity.
Qed.

Lemma swrap32_small : ltac2:(zQ "90!h9!q8!p8!ipa!hp2!pe!q3!jv3!jv9>1z$0>0@2$2@2$5@1$7@2$1+2+hf^1@2$6^1@2$1+2+hf@3$3$0@2$8@1$4#i0^2^2").
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma list_split3 : forall {X} (l : list X) (a b : nat), (a + b <= length l)%nat ->
  exists l1 l2 l3, l = l1 ++ l2 ++ l3 /\ length l1 = a /\ length l2 = b.
Proof.
  intros X l a b H. nexists (firstn a l), (firstn b (skipn a l)), (skipn b (skipn a l)).
  split. { rewrite (firstn_skipn b (skipn a l)). symmetry. apply firstn_skipn. }
  split. { apply firstn_length_le. lia. } { apply firstn_length_le. rewrite length_skipn. lia. }
Qed.

Lemma u64arr_u8arr : ltac2:(zQ "90!hp2!hr5!hgf!hrb!inb!h9!kg5!kgf!jg9>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1A$5>2ws@1$2@1$1@1$0#k0@2$4@4$6?4segs^3^2^1@4$8?4segs^3^2@1$7^1").
Proof. intros. unfold u64arr, u8arr. rewrite u64s_length, Nat2Z.inj_mul. change (Z.of_nat 8) with 8. tauto. Qed.

(* [comment removed for export] *)
Lemma Z_to_le_bytes_add : ltac2:(zQ "c0!kk6!hkd!hp2!hr5!ir0!hgf!ipa!km9!h9!imf!hn8!kn0>1a$1>1b$1>1z$8@3$6@1$5@1$3@1$2#8@2$0@2$7^3^2^1@3$4@1$3@1$2#8@2$0^3^1@2$0^2@2$b^1@2$9+8@1$a^3").
Proof.
  induction a as [|a IH]; intros b z; cbn [Z_to_le_bytes Nat.add app].
  - rewrite Z.shiftr_0_r. reflexivity.
  - f_equal. rewrite IH. f_equal. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Lemma le8_le4_le4 : ltac2:(zQ "e0!kr4!hp2!kra!hr5!ir0!hgf!p8!ipa!h9!ks1!pe!q3!q8!kn0>1x$8>0@2$6@2$aZ^1@2$b^1@2$c+2+k0@3$7@1$5@1$3@1$1#8@1$9@1$0^2@3$4@1$3@1$1#8@1$2@1$0^2@1$2@1$0@2$d^2+i0").
Proof.
  intros x Hx. unfold le8, le4, word_to_le_bytes, wz. rewrite !unsigned_lit; [|split; [apply Z.shiftr_nonneg; lia|]|lia].
  2:{ rewrite Z.shiftr_div_pow2 by lia. apply Z.div_lt_upper_bound; [lia|]. change (2^32*2^64) with (2^96). lia. }
  change 8%nat with (4 + 4)%nat at 1. rewrite Z_to_le_bytes_add. reflexivity.
Qed.

Lemma rw_cells_C8_C4C4 : ltac2:(zQ "h20!lg4!hg8!kr4!ir0!hgf!hp2!h9!lgc!lkd!hr5!hrb!p8!inb!ll9!pe!q3!q8!kn0>1m>0@1$9@1$5#k0@1$a@1$9@1$5#8>1A$6>3pre@1$4$0>1x$6>4post@1$4$0>0@2$b@2$eZ^2@2$f^2@2$h0+2+k0@2$c@4$8?4segs^6^5@3$3$0^4@3$1$0@1$d@1$2^3^2@4$8?4segs^6^5@3$3$0^4@3$1$0@1$7@1$2^3@3$1$0@1$7@1$2@2$h1^3+i0^2").
Proof.
  intros m A pre x post Hx. unfold rw_cells, cells_at.
  rewrite !cells_wf_app, !cells_bytes_app, !cells_size_app. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize].
  rewrite (le8_le4_le4 x Hx), <- app_assoc. cbn [app].
  replace (8 + cells_size post)%nat with (4 + (4 + cells_size post))%nat by lia. tauto.
Qed.

End MemHelpers.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac head_of t := lazymatch t with ?h _ => head_of h | _ => t end.
Ltac post_callU segs m :=
  let ms' := fresh "ms'" in let PO := fresh "PO" in
  intros ms' PO;
  (let h := head_of ltac:(type of PO) in try unfold h in PO);
  rewrite ?unsigned_lit in PO by lia; rewrite ?Z.add_0_r in PO; revert ms' PO; post_call segs m.
Tactic Notation "callU" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_callU segs m ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section DepotFrame.
Variable segs : ltac2:(zQ "20!hgf!mgc@1$0$1").

(* [comment removed for export] *)
Lemma depot_mem_stack : ltac2:(zQ "h21!h9!hp2!hr5!t5!pe!hrb!im1!llf!imf!hg8!in5!im8!hi1!hi8!ih7!qe!lmb!ln4&>0@1$2@1$1#k0@1$5@1$2@1$1#8>1d$f>1m~0>2m'~0>2lo$0>2hi$0>0@1$e^5>0@3$7?4segs^6^5>0@3$h0@3$9@2$6$0$0@4$b$0$0^4^3@1$a@2$6$0$0^6^5>0@3$h1?4segs^7^6>0@2$4@2$3+mpvgm8+8^6>0@2$4@2$3@1$c^a@2$8+h0+hggg0^7>0@2$4@2$3@1$d^b@2$8+8+ogg0^8@3$7?4segs^c^a").
Proof.
  intros d m m' lo hi W DM MU WM L1 L2 L3.
  pose proof (wf_ids d W) as I1. pose proof (wf_frames d W) as I2. pose proof (wf_nb d W) as I3. pose proof (wf_sb d W) as I4.
  destruct DM as [T1 T2 T3 T4 T5 T6 T7 T8 T9 T10].
  constructor.
  - intros b Hb. eapply rw_cells_transport; [apply T1; exact Hb|exact MU|exact WM|]. cbn. lia.
  - eapply rw_cells_transport; [exact T2|exact MU|exact WM|]. cbn. lia.
  - eapply rw_cells_transport; [exact T3|exact MU|exact WM|]. cbn. lia.
  - intros id Hid. eapply rw_cells_transport; [apply T4; exact Hid|exact MU|exact WM|]. cbn. lia.
  - intros id Hid. destruct (T5 id Hid) as [sid H]. exists sid. eapply rw_cells_transport; [exact H|exact MU|exact WM|]. cbn. lia.
  - intros id Hid. ndestruct (T6 id Hid) as (j1 & j2 & j3 & H). nexists j1, j2, j3. eapply rw_cells_transport; [exact H|exact MU|exact WM|]. cbn. lia.
  - eapply rw_cells_transport; [exact T7|exact MU|exact WM|]. cbn. lia.
  - eapply rw_cells_transport; [exact T8|exact MU|exact WM|]. cbn. lia.
  - eapply rw_cells_transport; [exact T9|exact MU|exact WM|]. cbn. lia.
  - ndestruct T10 as (junk & U & L). exists junk. split; [|exact L]. eapply u8arr_transport; [exact U|exact MU|exact WM|]. cbn. lia.
Qed.

(* [comment removed for export] *)
Definition put_W : ltac2:(zQ "30!h9!hgf!ila>2lo$0>3spv$0>2b0$0>2nb$0>2id$0>2sb$0>2fr$0>1n$0@1$1$2") := ltac2:(zQ "70!h9!t5!im1!hg8!im8!imf!in5\2lo$0\3spv$0\2b0$0\2nb$0\2id$0\2sb$0\2fr$0\1n$0@3$3@2$2$0$0@4$4$0$0^8^7@3$3@2$2$0$0@4$4$0$0@2$1+ipvgl8@2$5+4^6@2$1@2$1+ipvgl8@2$5+4^6+4@3$3@2$2$0$0@4$4$0$0+mpvgl8@2$1+mpvgl8+4@3$3@2$2$0$0@4$4$0$0@2$1^5@2$5+h0^4@2$1@2$1^5@2$5+h0^4+h0@3$3@2$2$0$0@4$4$0$0+iovgk8@2$1+iovgk8+8@3$3@2$2$0$0@4$4$0$0+iovgm0@2$1+iovgm0+4@3$3@2$2$0$0@4$4$0$0@2$1^3@2$5+8^2@2$1@2$1^3@2$5+8^2@2$5+8@2$1^1+1@1$6@2$2$0$0").

Lemma depot_insert_mem : ltac2:(zQ "i61!t5!lg4!hg8!hp2!h9!hr5!hh6!kr4!pe!imf!in5!va!lgc!lkd!nb!hi1!hi8!hrb!ipa!llf!ll9!q3!jh2!hgf!p8!ls8!r6!hj9!hk2!ih7!qe!jg9!lmb!ln4!ir6!hn8!q8!lt1&>0@1$5@1$3#k0@1$h1@1$5@1$3#8>1d$he>1h$4>1n$4>1m~0>2m'~0>2lo$4>3spv$4>3sid@1$5@1$3#k0>4junk@1$h7@1$5@1$3#8>0@1$hd^9>0@3$h3?4segs^a^7>0@3$h2$4@2$hb^b^aZ>0@2$h8@2$8Z^b@2$h5^b@2$i4+2+k0>0@2$8+1^b>0@2$h5@2$0@1$b^e+1+hggg0>0@2$8@2$0@2$0@1$6^f^d+1+ogg0>0@2$8@2$0+mpvgm8+8^b>0@2$8@2$0@1$f^h1@2$9+h0+hggg0^c>0@2$8@2$0@1$h0^h2@2$9+8+ogg0^d>0@3$i0@8$h9^e^d@1$e^h2@1$f^h3@2$0@1$b^h3+1@1$h0^h3@1$6^h3^h1^h0^f>0@3$i1?4segs^h1^h0>0@4$d?4segs^h1@2$0+ipvgl8@2$9+4@1$e^h4@3$2$1@1$c@1$7@2$0@1$b^h5+1@1$a$1>0@4$d?4segs^h2+mpvgl8@3$2$1@1$c@1$7@2$0@1$b^h6+1@1$a$1>0@4$d?4segs^h3@2$0@1$f^h7@2$9+h0@2$0@1$b^h7+1@3$2$1@1$h4@1$7^h6@3$2$1@1$c@1$7@3$i2$4Z@2$ha^h7@1$e^h6@3$2$1@1$c^h0@1$a$1>0@4$d?4segs^h4+iovgk8@3$2$1@1$h4@1$7@2$0@2$0@1$6^h8^h6+1@1$a$1>0@4$d?4segs^h5+iovgm0@3$2$1@1$c@1$7@2$0@2$0@1$6^h9^h7+1@1$a$1>0@4$hf?4segs^h6@2$0@1$h0^ha@2$9+8@1$6^ha^h2>0@3$h2$4@1$i3@2$h6@1$5@1$3#8^h3@2$9+8@2$i5+ogg0@1$6^hb@3$h3?4segs@3$hc^hc^hb^ha^h8").
Proof.
  intros d h n m m' lo spv sid junk W DM NF Hh Hn CI CF L1 L2 L3 MU WM TAB NUI ND TF STO SP LJ.
  pose proof (wf_ids d W) as I1. pose proof (wf_frames d W) as I2. pose proof (wf_nb d W) as I3. pose proof (wf_sb d W) as I4.
  pose proof (wf_nbsb d W) as I5. pose proof (bucket_range h) as BR.
  destruct DM as [T1 T2 T3 T4 T5 T6 T7 T8 T9 T10].
  unfold put_W in MU. unfold AIMG_TOP in *.
  constructor; cbn [d_insert d_ids d_frames d_hash d_chain d_nb d_sb].
  - intros b Hb. destruct (Z.eqb_spec b (bucket h)) as [->|NE]. { exact TAB. }
    eapply rw_cells_transport; [apply T1; exact Hb|exact MU|exact WM|]. cbn -[bucket]. lia.
  - exact NUI.
  - eapply rw_cells_transport; [exact T3|exact MU|exact WM|]. cbn -[bucket]. lia.
  - intros id Hid. destruct (Z.eqb_spec id (d_ids d + 1)) as [->|NE].
    + rewrite Z.eqb_refl. cbn [link_of]. rewrite Z.eqb_refl.
      apply (proj1 (rw_cells_app segs m' _ [C8 (wz h); C4 (wz (hd 0 (d_chain d (bucket h))))] [C4 sid])) in ND. apply ND.
    + assert (Hid' : 1 <= id <= d_ids d) by lia.
      assert (E : link_of (if bucket (d_hash d id) =? bucket h then d_ids d + 1 :: d_chain d (bucket (d_hash d id)) else d_chain d (bucket (d_hash d id))) id
                  = link_of (d_chain d (bucket (d_hash d id))) id).
      { destruct (Z.eqb_spec (bucket (d_hash d id)) (bucket h)); [|reflexivity]. apply link_of_cons_other. lia. }
      rewrite E. eapply rw_cells_transport; [apply T4; exact Hid'|exact MU|exact WM|]. cbn -[bucket]. lia.
  - intros id Hid. destruct (Z.eqb_spec id (d_ids d + 1)) as [->|NE].
    + exists sid. apply (proj1 (rw_cells_app segs m' _ [C8 (wz h); C4 (wz (hd 0 (d_chain d (bucket h))))] [C4 sid])) in ND.
      destruct ND as [_ ND]. cbn [cells_size csize Nat.add] in ND.
      replace (d_nb d + 16 * (d_ids d + 1) + Z.of_nat 12) with (d_nb d + 16 * (d_ids d + 1) + 12) in ND by lia. exact ND.
    + destruct (T5 id ltac:(lia)) as [sid' H]. exists sid'. eapply rw_cells_transport; [exact H|exact MU|exact WM|]. cbn -[bucket]. lia.
  - intros id Hid. ndestruct (T6 id ltac:(lia)) as (j1 & j2 & j3 & H). nexists j1, j2, j3.
    eapply rw_cells_transport; [exact H|exact MU|exact WM|]. cbn -[bucket]. lia.
  - exact TF.
  - eapply rw_cells_transport; [exact T8|exact MU|exact WM|]. cbn -[bucket]. lia.
  - exact STO.
  - ndestruct (list_split3 junk (Z.to_nat (8 * (n + 1))) 0 ltac:(lia)) as (ja & jb & jc & EJ & LA & LB).
    destruct jb; [|cbn in LB; lia]. cbn [app] in EJ. subst junk.
    apply u8arr_app in SP. destruct SP as [_ SP]. rewrite length_app in LJ.
    exists jc. split.
    + replace (d_sb d + 8 * (d_frames d + n + 1)) with (d_sb d + 8 * d_frames d + Z.of_nat (length ja)) by lia. exact SP.
    + lia.
Qed.

End DepotFrame.
(* [comment removed for export] *)
