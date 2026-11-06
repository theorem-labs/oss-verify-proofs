(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require BJ0Gc2. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep TacX ZBridge Exec CellsX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require Import BJRep BJFrame BJKitVS.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes06length03nat37Corelib4Init5Logici52eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ5BJRep~~~~~~je2jvje3jvsje7jvs_lenjeblist_of_jvs04prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ9BJKitDtor~~~~~~q2blist_of_kvsje3kvsje7kvs_len79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Refh2RMalloc_iface_stmt~~~~~~vf5block04listjeablocks_jvsje8blocks_v36Stdlib5Lists4Listhmf8flat_map04cons03fst03sndq29blocks_kvjeablocks_kvs37Corelib4Init5Peanohr72le37Corelib5Lists7ListDefht16Forallje7jheightjeajvs_heightjeakvs_heighti53iff37Corelib7Numbers7BinNumsihc4Npos89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ9BJKitDtor1K~~~~~~ijd6vhdrslje5vhdrs35stdpp9bitvectorbdefinitionsip02bvje5vdeepje6vdeepsvf3memijd6shdrslje5shdrsi53andje5kdeepje6sdeeps37Corelib4Init3Nativ33mulijd9slot_tailhr72ltht16firstnht13nthht15skipnje4vhdri52ex03app79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~jka4cell03niljka2CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~jp98rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~ju05rsegs06optioniv33addihc1Z46Stdlib6ZArith6BinInt1Zkj93addkj96of_natjkabcells_bytesjkaacells_sizejka8cells_wf" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint list_of_kvs (l : kvs) : list (block * jv) :=
  match l with KVnil => [] | KVcons b v r => (b, v) :: list_of_kvs r end.

Lemma jvs_len_list : ltac2:(zQ "70!h8!i0!j9!n9!ne!o4!oe>2es$4@3$2$1@1$5^1@2$0$3@1$6^1").
Proof. induction es; cbn; [reflexivity| now rewrite IHes]. Qed.
Lemma kvs_len_list : ltac2:(zQ "90!h8!i0!pc!j9!u1!n9!uf!v5!hk9>2ss$6@3$3$1@1$7^1@2$0@2$2$8$5@1$4^1").
Proof. induction ss; cbn; [reflexivity| now rewrite IHss]. Qed.

Lemma blocks_jvs_list : ltac2:(zQ "90!hk9!hl1!j9!hl7!hm4!n9!ne!oe!ho2>2es$6@3$2@1$1$0@1$3^1@4$8$5$0$4@1$7^1").
Proof. induction es; cbn; [reflexivity| now rewrite IHes]. Qed.
Definition blocks_kv : ltac2:(zQ "40!hk9!hl1!pc!n9>2bv@2$2$0$3@1$1$0") := ltac2:(zQ "70!hk9!n9!hoe!hp4!pc!hp9!hm4\2bv@2$4$0$1@3$2$0@3$3$0$1^1@1$6@3$5$0$1^1").
Lemma blocks_kvs_list : ltac2:(zQ "a0!hk9!hl1!pc!j9!hpe!u1!hqa!n9!uf!ho2>2ss$8@3$3@1$1$0@1$6^1@4$9@2$2$0$7$0$4@1$5^1").
Proof. induction ss; cbn; [reflexivity| now rewrite IHss]. Qed.

Lemma jheight_list : ltac2:(zQ "70!n9!hsb!hu8!hv2!ne!hvc!oe>2es$4@3$2$0\1v$0@2$1@1$3^1@1$5^2@1$6^1").
Proof.
  induction es as [|v r IH]; cbn; [constructor|]. constructor; [lia|].
  eapply Forall_impl; [|exact IH]. cbn. intros a Ha. lia.
Qed.
Lemma kheight_list : ltac2:(zQ "a0!n9!hk9!pc!hp9!hsb!hu8!u1!hv2!uf!ig9>2ss$8@3$5@2$2$1$0\2bv@2$2$1$0@2$4@1$7@3$3$1$0^1@1$9^2@1$6^1").
Proof.
  induction ss as [|b v r IH]; cbn; [constructor|]. constructor; [cbn; lia|].
  eapply Forall_impl; [|exact IH]. cbn. intros a Ha. lia.
Qed.

Section K.
  Context {HCEIL : HeapCeil}.

  Fixpoint vhdrsl (l : list jv) (bs : list byte) : Prop :=
    match l with
    | [] => bs = []
    | v :: r => exists hb rest, bs = hb ++ rest /\ length hb = 24%nat /\ vhdr v hb /\ vhdrsl r rest
    end.
  Definition slot_tail (b : block) (j4 : list byte) : list byte :=
    let '(p, K, ksz) := b in cells_bytes [C8 (wz K); C4 (wz (ksz - 1)); CB 4 j4].
  Fixpoint shdrsl (l : list (block * jv)) (bs : list byte) : Prop :=
    match l with
    | [] => bs = []
    | (b, v) :: r => exists hb j4 rest, bs = hb ++ slot_tail b j4 ++ rest /\ length hb = 24%nat /\ length j4 = 4%nat /\
                     vhdr v hb /\ shdrsl r rest
    end.

  Lemma vhdrs_list : ltac2:(zQ "80!hl1!ih6!ij5!ine!ne!oe!io8!iqd>2es$4>2bs@1$0@1$7@1$2#8@2$1@2$6^2^1@2$3@1$5^2^1").
  Proof.
    induction es as [|v r IH]; intros bs; cbn; [tauto|].
    split; (intros nd_i1; ndestruct nd_i1 as (hb & rest & E & L & Hh & Hr)); exists hb, rest; (split; [exact E|]); (split; [exact L|]); (split; [exact Hh|]); apply IH; exact Hr.
  Qed.
  Lemma vdeeps_list : ltac2:(zQ "80!ih6!hu8!n9!ne!oe!ir3!irb!is4>1m$7>2es$3@2$0@3$6?5HCEIL^2^1@3$1$2@2$5?5HCEIL^2@1$4^1").
  Proof.
    induction es as [|v r IH]; intros; cbn.
    - split; [intros; constructor| intros; exact I].
    - split. { intros [D R]. constructor; [exact D| apply IH; exact R]. }
      intros F. split; [exact (Forall_inv F)| apply IH; exact (Forall_inv_tail F)].
  Qed.
  Lemma shdrs_list : ltac2:(zQ "80!hl1!ih6!ij5!isa!u1!uf!it4!iqd>2ss$5>2bs@1$0@1$7@1$2#8@2$1@2$6^2^1@2$3@1$4^2^1").
  Proof.
    induction ss as [|[[p K] ksz] v r IH]; intros bs; cbn; [tauto|].
    split.
    - (intros nd_i2; ndestruct nd_i2 as (hb & _ & j4 & rest & E & L & L4 & Hh & Hr)). nexists hb, j4, rest. cbn [slot_tail].
      split; [exact E|]. split; [exact L|]. split; [exact L4|]. split; [exact Hh|]. apply IH. exact Hr.
    - (intros nd_i3; ndestruct nd_i3 as (hb & j4 & rest & E & L & L4 & Hh & Hr)). nexists hb, (wz 0), j4, rest.
      split; [exact E|]. split; [exact L|]. split; [exact L4|]. split; [exact Hh|]. apply IH. exact Hr.
  Qed.
  Lemma sdeeps_list : ltac2:(zQ "e0!n9!hk9!pc!hp4!hp9!itc!ih6!hu8!u1!iu2!uf!iua!ir3!is4>1m$d>2ss$a@2$6@3$b?5HCEIL^2^1@3$7@2$2$1$0\2bv@2$2$1$0@2$5@3$9?5HCEIL^3@3$3$1$0^1@3$c?5HCEIL^3@3$4$1$0^1@1$8^1").
  Proof.
    induction ss as [|[[p K] ksz] v r IH]; intros; cbn.
    - split; [intros; constructor| intros; exact I].
    - split. { (intros nd_i4; ndestruct nd_i4 as (Dk & Dv & R)). constructor; [cbn; split; [exact Dk| exact Dv]| apply IH; exact R]. }
      intros F. pose proof (Forall_inv F) as [Dk Dv]. cbn in Dk, Dv. split; [exact Dk|]. split; [exact Dv|]. apply IH. exact (Forall_inv_tail F).
  Qed.

  Lemma vhdrsl_length : ltac2:(zQ "90!h8!hl1!ij5!n9!iqd!i0!j9!jg5!ine>1l@1$1$3>2bs@1$1@1$4@1$2#8>0@2$8^2^1@3$6$5@2$0@1$4@1$2#8^2@2$7Nh8@2$0$3^3").
  Proof.
    induction l as [|v r IH]; intros bs Hh; cbn in Hh.
    - subst bs. reflexivity.
    - ndestruct Hh as (hb & rest & -> & L & _ & Hr). rewrite length_app, L, (IH _ Hr). cbn [length]. lia.
  Qed.
  Lemma slot_tail_length : ltac2:(zQ "80!ij5!iqd!h8!i0!j9!hl1!jgc!hk9>1b$7>2j4@1$5@1$1@1$0#8>0@3$4$3@2$2@1$1@1$0#8^1N4@3$4$3@2$2@1$1@1$0#8@2$6^3^2Nh0").
  Proof.
    intros [[p K] ksz] j4 L4. unfold slot_tail. cbn [cells_bytes cbytes].
    rewrite !length_app, length_le8, length_le4, L4. reflexivity.
  Qed.
  Lemma shdrsl_length : ltac2:(zQ "b0!h8!hl1!pc!ij5!n9!hk9!iqd!i0!j9!jg5!isa>1l@1$1@2$2$5$4>2bs@1$1@1$6@1$3#8>0@2$a^2^1@3$8$7@2$0@1$6@1$3#8^2@2$9Ni8@2$0@2$2$5$4^3").
  Proof.
    induction l as [|[b v] r IH]; intros bs Hh; cbn [shdrsl] in Hh.
    - subst bs. reflexivity.
    - ndestruct Hh as (hb & j4 & rest & -> & L & L4 & _ & Hr). rewrite !length_app, L, (IH _ Hr), (slot_tail_length _ _ L4).
      cbn [length]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma vhdrsl_nth : ltac2:(zQ "d0!n9!ij5!iqd!hl1!h8!i0!jg5!jh9!jhf!ji9!jj0!ine!jj9>1l@1$3$0>2bs@1$3@1$2@1$1#8>1k$5>1d$0>0@2$b^4^3>0@2$7^3@2$4$0^5@2$c@4$9$0^4^6^3@3$8@1$2@1$1#8Nh8@3$a@1$2@1$1#8@2$6Nh8^4^5").
  Proof.
    induction l as [|v r IH]; intros bs k d Hh Hk; cbn in Hk; [lia|].
    cbn [vhdrsl] in Hh. ndestruct Hh as (hb & rest & -> & L & Hv & Hr).
    destruct k as [|k].
    - cbn [nth]. rewrite Nat.mul_0_r, skipn_O, firstn_app, L, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 by lia. exact Hv.
    - cbn [nth]. replace (24 * S k)%nat with (length hb + 24 * k)%nat by lia.
      rewrite skipn_app, skipn_all2 by lia. cbn [app]. replace (length hb + 24 * k - length hb)%nat with (24 * k)%nat by lia.
      apply IH; [exact Hr| lia].
  Qed.

  Lemma shdrsl_nth : ltac2:(zQ "h60!ij5!iqd!hl1!n9!hk9!pc!h8!i0!itc!j9!jk0!ji9!jk5!hp4!hp9!jg5!jh9!jhf!jj0!isa!jgc!jj9>1l@1$2@2$5$4$3>2bs@1$2@1$1@1$0#8>1k$7>1d@2$5$4$3>0@2$h3^4^3>0@2$h0^3@2$6@2$5$4$3^5@2$a@1$2@1$1@1$0#8\2hb@1$2@1$1@1$0#8@2$a@1$2@1$1@1$0#8\2j4@1$2@1$1@1$0#8@2$8@3$9@1$2@1$1@1$0#8@3$h1@1$1@1$0#8Ni8@3$h2@1$1@1$0#8@2$fNi8^6^7@3$c@1$1@1$0#8^2@2$h4@3$d$4$3@4$b@2$5$4$3^6^8^5^1@2$8@3$9$7@2$6@1$1@1$0#8^2Nh8@2$8@3$9$7@2$6@1$1@1$0#8^1N4@2$h5@3$e$4$3@4$b@2$5$4$3^6^8^5^2").
  Proof.
    induction l as [|[b v] r IH]; intros bs k d Hh Hk; cbn in Hk; [lia|].
    cbn [shdrsl] in Hh. ndestruct Hh as (hb & j4 & rest & -> & L & L4 & Hv & Hr).
    pose proof (slot_tail_length b j4 L4) as LT.
    destruct k as [|k].
    - exists hb, j4. cbn [nth fst snd]. rewrite Nat.mul_0_r, skipn_O. rewrite app_assoc, firstn_app, length_app, L, LT.
      replace (40 - (24 + 16))%nat with 0%nat by lia. rewrite firstn_O, app_nil_r, firstn_all2 by (rewrite length_app, L, LT; lia).
      split; [reflexivity|]. split; [first [exact L| reflexivity]|]. split; [first [exact L4| reflexivity]| exact Hv].
    - cbn [nth]. rewrite app_assoc. replace (40 * S k)%nat with (length (hb ++ slot_tail b j4) + 40 * k)%nat by (rewrite length_app, L, LT; lia).
      rewrite skipn_app, skipn_all2 by lia. cbn [app].
      replace (length (hb ++ slot_tail b j4) + 40 * k - length (hb ++ slot_tail b j4))%nat with (40 * k)%nat by lia.
      apply IH; [exact Hr| lia].
  Qed.

  Lemma firstn_S_snoc : forall {A} (l : list A) k d, (k < length l)%nat -> firstn (S k) l = firstn k l ++ [nth k l d].
  Proof.
    induction l as [|x r IH]; intros k d Hk; cbn in Hk; [lia|].
    destruct k as [|k]; cbn; [reflexivity|]. f_equal. apply IH. lia.
  Qed.
  Lemma Forall_nth' : forall {A} (P : A -> Prop) k l d, Forall P l -> (k < length l)%nat -> P (nth k l d).
  Proof.
    intros A P k l d F. revert k. induction F as [|x r Hx Hr IH]; intros k Hk; cbn in Hk; [lia|].
    destruct k; cbn; [exact Hx| apply IH; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma rw_cells_CB_sub : ltac2:(zQ "h20!ij5!iqd!jo6!i0!hoe!joe!jp3!jt4!khc!hl1!ki5!kid!hsb!jhf!jj0!kj4!kl1!kl8>1m>0@1$1@1$0#k0@1$a@1$1@1$0#8>1A$f>1n$3>2bs@1$9@1$1@1$0#8>1k$3>1j$3>0@4$7$8^6^5@3$4$2@2$6^4^3@1$5$2>0@2$c@2$b^3^2^5@4$7$8^8@2$h0^7@1$h1^4@3$4$2@2$6^3@3$d@1$1@1$0#8^3@3$e@1$1@1$0#8^4^5@1$5$2").
  Proof.
    intros m A n bs k j R Hkj.
    destruct (rw_cells_CB_split _ _ _ _ k _ R ltac:(lia)) as [_ R2].
    destruct (rw_cells_CB_split _ _ _ _ j _ R2 ltac:(lia)) as [R3 _]. exact R3.
  Qed.

  (* [comment removed for export] *)
  Lemma rw_cells_of_CB : ltac2:(zQ "h00!jo6!i0!ij5!jt4!khc!iqd!hoe!hl1!joe!ki5!j9!kj4!jp3!km2!kn1!knf>1m>0@1$5@1$2#k0@1$9@1$5@1$2#8>1A$b>2cs@1$7$0>1n$1>0@4$3$4^4^3@3$6$0@2$c^1@1$d^2@1$8$0>0@1$f^3>0@3$a$1@1$e^4^3@4$3$4^7^6^5").
  Proof.
    intros m A cs n [[W B] R] WF SZ. split; [split|].
    - exact WF.
    - cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
    - cbn [cells_size csize] in R. rewrite Nat.add_0_r in R. rewrite SZ. exact R.
  Qed.
End K.
(* [comment removed for export] *)
