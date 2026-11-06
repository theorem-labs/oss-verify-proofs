(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep TacX ZBridge Exec CellsX Mem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsObj.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJA Require Import BJRep BJKitVS.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes06length03nat37Corelib4Init5Logici52eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJA5BJRep~~~~~~je2jvje3jvsje7jvs_lenjeblist_of_jvs04prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsIface~~~~~~q35block79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJA9BJKitDtor~~~~~~u8blist_of_kvsje3kvsje7kvs_len04listjeablocks_jvsje8blocks_v36Stdlib5Lists4Listhm48flat_map04cons03fst03sndu89blocks_kvjeablocks_kvs37Corelib4Init5Peanohqc2le37Corelib5Lists7ListDefhs66Forallje7jheightjeajvs_heightjeakvs_heighti53iff37Corelib7Numbers7BinNumsih14Npos89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJA9BJKitDtor1K~~~~~~ij26vhdrslje5vhdrs35stdpp9bitvectorbdefinitionsio62bvq33memje5vdeepje6vdeepsij26shdrslje5shdrsi53andje5kdeepje6sdeeps37Corelib4Init3Natiu93mulij29slot_tailhqc2lths66firstnhs63nthhs65skipnje4vhdri52ex03app79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~jk04cell03nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~jo95asegsjk02CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~jt38rw_cells06optioniu93addih11Z46Stdlib6ZArith6BinInt1Zkie3addkie6of_natjk0bcells_bytesjk0acells_sizejk08cells_wfjk02C879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~ko62wz" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint list_of_kvs (l : kvs) : list (block * jv) :=
  match l with KVnil => [] | KVcons b v r => (b, v) :: list_of_kvs r end.

Lemma jvs_len_list : ltac2:(zQ "70!h8!i0!j9!na!nf!o5!of>2es$4@3$2$1@1$5^1@2$0$3@1$6^1").
Proof. induction es; cbn; [reflexivity| now rewrite IHes]. Qed.
Lemma kvs_len_list : ltac2:(zQ "90!h8!i0!pd!j9!u0!hi8!na!hj6!hjc>2ss$7@3$3$1@1$8^1@2$0@2$2$4$6@1$5^1").
Proof. induction ss; cbn; [reflexivity| now rewrite IHss]. Qed.

Lemma blocks_jvs_list : ltac2:(zQ "90!u0!hk6!j9!hkc!hl9!na!nf!of!hn7>2es$6@3$2@1$1$0@1$3^1@4$8$5$0$4@1$7^1").
Proof. induction es; cbn; [reflexivity| now rewrite IHes]. Qed.
Definition blocks_kv : ltac2:(zQ "40!u0!hk6!pd!na>2bv@2$2$0$3@1$1$0") := ltac2:(zQ "70!u0!na!ho3!ho9!pd!hoe!hl9\2bv@2$4$0$1@3$2$0@3$3$0$1^1@1$6@3$5$0$1^1").
Lemma blocks_kvs_list : ltac2:(zQ "a0!u0!hk6!pd!j9!hp3!hi8!hpf!na!hj6!hn7>2ss$8@3$3@1$1$0@1$6^1@4$9@2$2$0$7$0$4@1$5^1").
Proof. induction ss; cbn; [reflexivity| now rewrite IHss]. Qed.

Lemma jheight_list : ltac2:(zQ "70!na!hs0!htd!hu7!nf!hv1!of>2es$4@3$2$0\1v$0@2$1@1$3^1@1$5^2@1$6^1").
Proof.
  induction es as [|v r IH]; cbn; [constructor|]. constructor; [lia|].
  eapply Forall_impl; [|exact IH]. cbn. intros a Ha. lia.
Qed.
Lemma kheight_list : ltac2:(zQ "a0!u0!na!pd!hoe!hs0!htd!hi8!hu7!hj6!hve>2ss$8@3$5@2$2$0$1\2bv@2$2$0$1@2$4@1$7@3$3$0$1^1@1$9^2@1$6^1").
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

  Lemma vhdrs_list : ltac2:(zQ "80!hk6!igb!iia!in4!nf!of!ine!iq3>2es$4>2bs@1$0@1$7@1$2#8@2$1@2$6^2^1@2$3@1$5^2^1").
  Proof.
    induction es as [|v r IH]; intros bs; cbn; [tauto|].
    split; (intros nd_i1; ndestruct nd_i1 as (hb & rest & E & L & Hh & Hr)); exists hb, rest; (split; [exact E|]); (split; [exact L|]); (split; [exact Hh|]); apply IH; exact Hr.
  Qed.
  Lemma vdeeps_list : ltac2:(zQ "80!igb!htd!iq9!na!nf!of!iqf!ir7>1m$2>2es$4@2$0@3$7?5HCEIL^2^1@3$1$3@2$6?5HCEIL^2@1$5^1").
  Proof.
    induction es as [|v r IH]; intros; cbn.
    - split; [intros; constructor| intros; exact I].
    - split. { intros [D R]. constructor; [exact D| apply IH; exact R]. }
      intros F. split; [exact (Forall_inv F)| apply IH; exact (Forall_inv_tail F)].
  Qed.
  Lemma shdrs_list : ltac2:(zQ "80!hk6!igb!iia!is0!hi8!hj6!isa!iq3>2ss$5>2bs@1$0@1$7@1$2#8@2$1@2$6^2^1@2$3@1$4^2^1").
  Proof.
    induction ss as [|[[p K] ksz] v r IH]; intros bs; cbn; [tauto|].
    split.
    - (intros nd_i2; ndestruct nd_i2 as (hb & _ & j4 & rest & E & L & L4 & Hh & Hr)). nexists hb, j4, rest. cbn [slot_tail].
      split; [exact E|]. split; [exact L|]. split; [exact L4|]. split; [exact Hh|]. apply IH. exact Hr.
    - (intros nd_i3; ndestruct nd_i3 as (hb & j4 & rest & E & L & L4 & Hh & Hr)). nexists hb, (wz 0), j4, rest.
      split; [exact E|]. split; [exact L|]. split; [exact L4|]. split; [exact Hh|]. apply IH. exact Hr.
  Qed.
  Lemma sdeeps_list : ltac2:(zQ "e0!u0!na!pd!ho9!hoe!it2!igb!htd!iq9!hi8!it8!hj6!iu0!iqf>1m$8>2ss$b@2$6@3$c?5HCEIL^2^1@3$7@2$2$0$1\2bv@2$2$0$1@2$5@3$a?5HCEIL^3@3$3$0$1^1@3$d?5HCEIL^3@3$4$0$1^1@1$9^1").
  Proof.
    induction ss as [|[[p K] ksz] v r IH]; intros; cbn.
    - split; [intros; constructor| intros; exact I].
    - split. { (intros nd_i4; ndestruct nd_i4 as (Dk & Dv & R)). constructor; [cbn; split; [exact Dk| exact Dv]| apply IH; exact R]. }
      intros F. pose proof (Forall_inv F) as [Dk Dv]. cbn in Dk, Dv. split; [exact Dk|]. split; [exact Dv|]. apply IH. exact (Forall_inv_tail F).
  Qed.

  Lemma vhdrsl_length : ltac2:(zQ "90!h8!hk6!iia!na!iq3!i0!j9!ivb!in4>1l@1$1$3>2bs@1$1@1$4@1$2#8>0@2$8^2^1@3$6$5@2$0@1$4@1$2#8^2@2$7Nh8@2$0$3^3").
  Proof.
    induction l as [|v r IH]; intros bs Hh; cbn in Hh.
    - subst bs. reflexivity.
    - ndestruct Hh as (hb & rest & -> & L & _ & Hr). rewrite length_app, L, (IH _ Hr). cbn [length]. lia.
  Qed.
  Lemma slot_tail_length : ltac2:(zQ "80!iia!iq3!h8!i0!j9!hk6!u0!jg2>1b$6>2j4@1$5@1$1@1$0#8>0@3$4$3@2$2@1$1@1$0#8^1N4@3$4$3@2$2@1$1@1$0#8@2$7^3^2Nh0").
  Proof.
    intros [[p K] ksz] j4 L4. unfold slot_tail. cbn [cells_bytes cbytes].
    rewrite !length_app, length_le8, length_le4, L4. reflexivity.
  Qed.
  Lemma shdrsl_length : ltac2:(zQ "b0!h8!hk6!pd!iia!u0!na!iq3!i0!j9!ivb!is0>1l@1$1@2$2$4$5>2bs@1$1@1$6@1$3#8>0@2$a^2^1@3$8$7@2$0@1$6@1$3#8^2@2$9Ni8@2$0@2$2$4$5^3").
  Proof.
    induction l as [|[b v] r IH]; intros bs Hh; cbn [shdrsl] in Hh.
    - subst bs. reflexivity.
    - ndestruct Hh as (hb & j4 & rest & -> & L & L4 & _ & Hr). rewrite !length_app, L, (IH _ Hr), (slot_tail_length _ _ L4).
      cbn [length]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma vhdrsl_nth : ltac2:(zQ "d0!na!iia!iq3!hk6!h8!i0!ivb!jgf!jh5!jhf!ji6!in4!jif>1l@1$3$0>2bs@1$3@1$2@1$1#8>1k$5>1d$0>0@2$b^4^3>0@2$7^3@2$4$0^5@2$c@4$9$0^4^6^3@3$8@1$2@1$1#8Nh8@3$a@1$2@1$1#8@2$6Nh8^4^5").
  Proof.
    induction l as [|v r IH]; intros bs k d Hh Hk; cbn in Hk; [lia|].
    cbn [vhdrsl] in Hh. ndestruct Hh as (hb & rest & -> & L & Hv & Hr).
    destruct k as [|k].
    - cbn [nth]. rewrite Nat.mul_0_r, skipn_O, firstn_app, L, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 by lia. exact Hv.
    - cbn [nth]. replace (24 * S k)%nat with (length hb + 24 * k)%nat by lia.
      rewrite skipn_app, skipn_all2 by lia. cbn [app]. replace (length hb + 24 * k - length hb)%nat with (24 * k)%nat by lia.
      apply IH; [exact Hr| lia].
  Qed.

  Lemma shdrsl_nth : ltac2:(zQ "h60!iia!iq3!hk6!u0!na!pd!h8!i0!it2!j9!jj6!jhf!jjb!ho9!hoe!ivb!jgf!jh5!ji6!is0!jg2!jif>1l@1$2@2$5$3$4>2bs@1$2@1$1@1$0#8>1k$7>1d@2$5$3$4>0@2$h3^4^3>0@2$h0^3@2$6@2$5$3$4^5@2$a@1$2@1$1@1$0#8\2hb@1$2@1$1@1$0#8@2$a@1$2@1$1@1$0#8\2j4@1$2@1$1@1$0#8@2$8@3$9@1$2@1$1@1$0#8@3$h1@1$1@1$0#8Ni8@3$h2@1$1@1$0#8@2$fNi8^6^7@3$c@1$1@1$0#8^2@2$h4@3$d$3$4@4$b@2$5$3$4^6^8^5^1@2$8@3$9$7@2$6@1$1@1$0#8^2Nh8@2$8@3$9$7@2$6@1$1@1$0#8^1N4@2$h5@3$e$3$4@4$b@2$5$3$4^6^8^5^2").
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
  Lemma Forall_firstn' : forall {A} (P : A -> Prop) k l, Forall P l -> Forall P (firstn k l).
  Proof.
    intros A P k l F. revert k. induction F as [|x r Hx Hr IH]; intros k; destruct k; cbn; try constructor; auto.
  Qed.
  Lemma Forall_nth' : forall {A} (P : A -> Prop) k l d, Forall P l -> (k < length l)%nat -> P (nth k l d).
  Proof.
    intros A P k l d F. revert k. induction F as [|x r Hx Hr IH]; intros k Hk; cbn in Hk; [lia|].
    destruct k; cbn; [exact Hx| apply IH; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma rw_cells_CB_sub : ltac2:(zQ "h20!iia!iq3!jnc!i0!ho3!jo4!js4!jsd!kge!hk6!kha!ki2!hs0!jh5!ji6!ki9!kk6!kkd>1m>0@1$1@1$0#k0@1$a@1$1@1$0#8>1A$f>1n$3>2bs@1$9@1$1@1$0#8>1k$3>1j$3>0@4$8$6^6^5@3$4$2@2$7^4^3@1$5$2>0@2$c@2$b^3^2^5@4$8$6^8@2$h0^7@1$h1^4@3$4$2@2$7^3@3$d@1$1@1$0#8^3@3$e@1$1@1$0#8^4^5@1$5$2").
  Proof.
    intros m A n bs k j R Hkj.
    destruct (rw_cells_CB_split _ _ _ _ k _ R ltac:(lia)) as [_ R2].
    destruct (rw_cells_CB_split _ _ _ _ j _ R2 ltac:(lia)) as [R3 _]. exact R3.
  Qed.

  (* [comment removed for export] *)
  Lemma rw_cells_of_CB : ltac2:(zQ "h00!jnc!i0!iia!js4!kge!iq3!ho3!hk6!jo4!kha!j9!ki9!jsd!kl7!km6!kn4>1m>0@1$5@1$2#k0@1$9@1$5@1$2#8>1A$b>2cs@1$7$0>1n$1>0@4$4$3^4^3@3$6$0@2$c^1@1$d^2@1$8$0>0@1$f^3>0@3$a$1@1$e^4^3@4$4$3^7^6^5").
  Proof.
    intros m A cs n [[W B] R] WF SZ. split; [split|].
    - exact WF.
    - cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
    - cbn [cells_size csize] in R. rewrite Nat.add_0_r in R. rewrite SZ. exact R.
  Qed.

  (* [comment removed for export] *)
  Lemma vhdr_sp_word : ltac2:(zQ "h10!iia!iq3!hk6!j9!jnc!ho3!h8!i0!jo4!it2!jj6!na!jif!ko0!jsd!kl7!ks1>1v$b>2hb@1$2@1$1@1$0#8>0@2$c^2^1>0@3$3$7@2$6@1$1@1$0#8^2Nh8@2$a@1$2@1$1@1$0#8\5hrest@1$2@1$1@1$0#8@2$9@3$3@1$2@1$1@1$0#8^4@1$f@3$5$4@1$d@1$h0Z@3$5$4@2$eNh0^1@1$8$4@3$3$7@2$6@1$1@1$0#8^1Nh0").
  Proof.
    intros v hb VH LEN.
    assert (EX : exists rest, hb = le8 (wz 0) ++ rest).
    { destruct v as [k|n|[[p' K'] sz'] n|[[[p' T'] sz']|] cap' es'|[[[p' T'] sz']|] cap' ss']; cbn [vhdr] in VH.
      - ndestruct VH as (_ & j7 & pay & _ & _ & ->). eexists. cbn [cells_bytes cbytes]. reflexivity.
      - ndestruct VH as (_ & bs & _ & ->). eexists. cbn [cells_bytes cbytes]. reflexivity.
      - ndestruct VH as (j7 & _ & ->). eexists. unfold val_hdr. cbn [cells_bytes cbytes]. reflexivity.
      - first [ndestruct VH as (j7 & _ & ->) | ndestruct VH as (_ & _ & j7 & _ & ->)]. eexists. unfold val_hdr. cbn [cells_bytes cbytes]. reflexivity.
      - first [ndestruct VH as (j7 & _ & ->) | ndestruct VH as (_ & _ & j7 & _ & ->)]. eexists. unfold val_hdr. cbn [cells_bytes cbytes]. reflexivity.
      - first [ndestruct VH as (j7 & _ & ->) | ndestruct VH as (_ & _ & j7 & _ & ->)]. eexists. unfold val_hdr. cbn [cells_bytes cbytes]. reflexivity.
      - first [ndestruct VH as (j7 & _ & ->) | ndestruct VH as (_ & _ & j7 & _ & ->)]. eexists. unfold val_hdr. cbn [cells_bytes cbytes]. reflexivity. }
    destruct EX as [rest ->]. exists rest. rewrite length_app, length_le8 in LEN.
    split; [| lia]. cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
  Qed.
End K.
