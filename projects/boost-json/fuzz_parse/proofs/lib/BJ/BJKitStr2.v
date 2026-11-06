(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require BJ0Gc2. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require Import BJRep BJFrame BJKitVS.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ5BJRep~~~~~~06vstack04mkVS06vs_buf06vs_cap08vs_items07vs_temp37Corelib4Init9Datatypesmc4list37Corelib4Init5Logicob2eq89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ9BJKitStr21K~~~~~~q45vs_zc06vsitem37Corelib7Numbers7BinNumsv51Z08vs_chars04vs_n09blocks_vs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Refh2RMalloc_iface_stmt~~~~~~hid5block79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~ho04cellmc4consho02C879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~ht12wzmc3nilv54Npos08vs_begin06vs_end06vs_hdr06vs_topho02C1ho02CBht12b835stdpp9bitvectorbdefinitionsil32bvmc4prod69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~ind5hceil46Stdlib6ZArith6BinInt1Zis12lemc3fst37Corelib5Lists7ListDefiu56Forall79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~jg6ddisjoint_fromis13addmc4pairob3and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ7BJFrame~~~~~~jm77rin_ivs36Stdlib5Lists4Listjqf2Inis12lt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~jse5rsegs05vs_atis13mulmc6lengthmc6optionob2ex79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ7BJKitVS~~~~~~kj8cblocks_belowjg63ivljg65munchjg65wmono79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~kpe8bytes_at79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~ku48rw_cellshid3memis16of_nat" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section K.
  Context {HCEIL : HeapCeil}.

  (* [comment removed for export] *)
  Definition vs_zc : ltac2:(zQ "10!jb>2st$0$0") := ltac2:(zQ "60!k3!k9!l1!l9!m3!jb\2st$5@5$0@1$1^1@1$2^1@1$3^1Z@1$4^1").

  Lemma vs_zc_items : ltac2:(zQ "60!l9!o4!pf!u5!ud!jb>2st$5@3$2@1$1$4@1$0@1$3^1@1$0^1").  Proof. reflexivity. Qed.
  Lemma vs_zc_chars : ltac2:(zQ "50!pf!hge!u5!hh2!jb>2st$4@3$0$1@1$3@1$2^1Z").            Proof. reflexivity. Qed.
  Lemma vs_zc_temp : ltac2:(zQ "50!m3!pf!hge!u5!jb>2st$4@3$1$2@1$0@1$3^1@1$0^1").    Proof. reflexivity. Qed.
  Lemma vs_zc_n : ltac2:(zQ "50!hhc!pf!hge!u5!jb>2st$4@3$1$2@1$0@1$3^1@1$0^1").          Proof. reflexivity. Qed.
  Lemma blocks_vs_zc : ltac2:(zQ "60!hi2!o4!pf!u5!jb!hn7>2st$4@3$2@1$1$5@1$0@1$3^1@1$0^1"). Proof. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma vs_hdr_zc : ltac2:(zQ "h30!hrc!hs4!hsb!igc!o4!ih2!pf!ih8!u5!ihf!ii9!ij1!m3!ij9!jb!ik1!ik7!ikd!in0>2st$e>5junk7@1$4@1$h2@1$7#8@3$6@1$4$0@2$b@1$8^2^1@3$1$0@1$2@1$3Z@3$1$0@1$2@1$3@1$c^2@3$1$0@1$2@1$3@1$9^2@3$1$0@1$2@1$3@1$d^2@3$1$0@1$2@1$3@1$a^2@3$1$0@1$2@1$3Z@3$1$0@1$f@1$h1+1@3$1$0@2$h0N7^1@3$1$0@1$2@1$3Z@1$5$0").
  Proof. reflexivity. Qed.

  Lemma disjoint_from_above : ltac2:(zQ "90!hge!in6!ir8!it9!itf!o4!ivc!jk2!jl3>1W@1$5@2$1$0$0>1A$0>1k$0>0@3$6@2$1$0$0\2iv@2$1$0$0@2$3@1$2?5HCEIL@3$4$0$0^1^3>0@2$3@2$8^3^2@1$2?5HCEIL@3$7^5^4^3").
  Proof.
    induction W as [|[lo hi] W IH]; intros A k FW HA; [exact I|]. cbn.
    pose proof (Forall_inv FW) as H1. cbn in H1. split; [left; lia| apply IH; [apply (Forall_inv_tail FW)| exact HA]].
  Qed.

  Lemma rin_ivs_in : ltac2:(zQ "90!hge!in6!o4!jla!jm1!jq4!js2!it9!js8>1W@1$2@2$1$0$0>2lo$0>2hi$0>1a$0>0@3$6@2$1$0$0@4$3$0$0^3^2^4>0@2$4@2$7^4^2@2$8^2^3@2$5^6^3").
  Proof.
    induction W as [|iv W IH]; intros lo hi a HI Ha; [destruct HI|]. cbn. destruct HI as [->|HI]; [left; cbn; lia| right; eapply IH; eauto].
  Qed.

  Lemma vs_at_zc : ltac2:(zQ "i30!hge!ih8!in0!o4!jm1!hh2!kga!jl3!in6!u5!kh3!it9!kha!itf!ki1!kia!pf!kj3!ivc!kn5!hi2!l1!ij1!hhc!ij9!jb!ir8!ko5!koc!kp5!kt8!lhf!lib!js8!lj2>1m$i0>2m'>0@1$2@1$1#k0@1$f@1$2@1$1#8>1a$0>2st$h9>1W@1$3$hb>6junk7'@1$3@1$2@1$1#8>0@4$a?5HCEIL^6^4^3>0@2$i1Z@1$5^4>0@3$hc^4^8^7>0@3$hd$6^9^8>0@3$h2@2$8$0$0\2iv@2$8$0$0@2$b@1$ha?5HCEIL@3$d$0$0^1^6>0@2$h3?5HCEIL@1$h4^8>0@4$hf$6^b^a@2$h6@1$9^9^7@2$4@4$a?5HCEIL^c^b@1$9^a@2$4@2$h1@1$3@1$2@1$1#8\4part@1$3@1$2@1$1#8@2$4@4$he$6^d@2$7@1$h8^b+h8^1@3$h0$0@1$i2@2$e@1$2@1$1#8^1@1$5^b@2$b@2$7@2$c+h8@2$7@1$h7^a+1@1$5^a@2$c+h8@1$h5^a").
  Proof.
    intros m m' a st W junk7' V CH MU WM FW BB HDR'.
    destruct st as [buf cap items chars temp]. cbv [vs_chars vs_cap vs_n vs_items vs_top vs_begin vs_buf blocks_vs vs_zc vs_temp] in CH, BB, HDR' |- *.
    destruct buf as [[[p B] sz]|].
    2:{ exfalso. ndestruct V as (_ & _ & (_ & _ & CH0)). cbv [vs_chars] in CH0. lia. }
    destruct (vs_at_some_elim _ _ _ _ _ _ _ _ _ V) as (SZ & CH0 & (junk7 & HDR) & CAP16 & NLE & CAP32 & BR & BT & ITEMS & ROOMI & (junk & JK)).
    subst sz. npose BR as (Q1 & Q2 & Q3 & Q4 & Q5). hcb.
    specialize (ROOMI CH).
    set (cur := Z.of_nat (length items)) in *.
    apply items_at_raw in ITEMS. ndestruct ITEMS as (bs & LEN & RB & IH & ID).
    assert (HBL : forall b, In b ((p, B, 24 * cap) :: blocks_items items) -> blk_addr b + blk_size b <= hceil).
    { intros b Hb. ndestruct (BB b Hb) as (_ & _ & _ & R4 & _). exact R4. }
    assert (XP : xpres ((p, B, 24 * cap) :: blocks_items items) (2^64) W m m').
    { eapply xpres_of_munch; [exact MU| exact WM| | exact HBL].
      apply Forall_forall. intros [lo hi] HI. right. intros x Hx. eapply rin_ivs_in; [exact HI| exact Hx]. }
    assert (XH : X_above_hceil W).
    { unfold X_above_hceil. apply Forall_forall. intros iv HI. left. exact (proj1 (Forall_forall _ _) FW iv HI). }
    assert (RB' : rw_cells rsegs m' B [CB (24 * length items)%nat bs]).
    { eapply rw_cells_transport; [exact RB| exact MU| exact WM|]. apply disjoint_from_above; [exact FW|]. cbn [cells_size csize Nat.add]. lia. }
    assert (JK' : rw_cells rsegs m' (B + 24 * cur) [CB (Z.to_nat (24 * (cap - cur))) junk]).
    { eapply rw_cells_transport; [exact JK| exact MU| exact WM|]. apply disjoint_from_above; [exact FW|]. cbn [cells_size csize Nat.add]. lia. }
    split.
    - eapply vs_at_some_intro with (junk7 := junk7') (junk := junk); try lia.
      + unfold vs_hdr in HDR'. cbv [vs_temp vs_begin vs_top vs_end vs_n vs_buf vs_cap vs_items] in HDR'. fold cur in HDR'. exact HDR'.
      + exact BR.
      + eapply (items_at_relocate ((p, B, 24 * cap) :: blocks_items items) (2^64) W m m' B B items bs);
          [exact RB| exact IH| exact ID| exact RB'| exact XP| exact XH| exact BB| intros b Hb; right; exact Hb].
      + fold cur. exact JK'.
    - split; [| lia].
      (* [comment removed for export] *)
      destruct (rw_cells_CB_split _ _ _ _ 24%nat _ JK' ltac:(lia)) as [_ JK2]. change (Z.of_nat 24) with 24 in JK2.
      destruct (rw_cells_CB_split _ _ _ _ (Z.to_nat chars) _ JK2 ltac:(lia)) as [PART _].
      pose proof PART as [[[LP _] PB] _]. cbn in LP. cbn [cells_bytes cbytes app] in PB. rewrite app_nil_r in PB.
      eexists. split; [exact PB|]. rewrite LP. lia.
  Qed.
End K.
(* [comment removed for export] *)
