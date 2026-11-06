(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep Exec TacX CellsX FP.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import BJFrame HeapMF_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJU Require Import BJRep BJHeap BJIface BJIfaceObj BJKitVS BJKitW BJKitStr BJKitDtor.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list04prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJU5BJRep~~~~~~i42jv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh2RMalloc_iface_stmt~~~~~~m55block37Corelib4Init5Logicr82eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJU9BJKitDtor~~~~~~t1blist_of_kvs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJU8BJKitObj~~~~~~hhfbkvs_of_list06length03nati47kvs_lent19blocks_kvi4ablocks_kvs36Stdlib5Lists4Listhpd8flat_map79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJUaBJIfaceObj~~~~~~hrc7kvitemsi4cblocks_items37Corelib4Init5Peanoih72le03snd37Corelib5Lists7ListDefij66Foralli47jheighti4akvs_height37Corelib7Numbers7BinNumsime4Npost16shdrsl35stdpp9bitvectorbdefinitionsip82bv03app37Corelib4Init3Natis03mulij66firstnij65skipnr83andr82exi44vhdr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ive3le879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~jjf2wzm56blk_id79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~jo94bptrhpd2Inr83notij63maphpd5NoDupime1Z46Stdlib6ZArith6BinInt1Zjue2le03fstm53memr82or69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~khc5hceilm58blk_addr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~kmb5munchkmb5wmono79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU7BJFrame~~~~~~kr97rin_ivskr95xpres79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUcHeapMF_iface~~~~~~lgc8hs_RHEAPm58blk_size79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~lm75rsegsjo96PStatejue3addjue2lt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~ls44cell04cons03nili4abj_staticsls42C479OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~mi68rw_cellslgc7eh_idlelgcbhs_rauxv_okip8bbv_unsignedm54RATPi45kdeepi45vdeep79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJU7BJKitVS~~~~~~mqdcblocks_belowlgc3hmflgc3ehklgccheap_mf_hyps" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint kvs_of_list (l : list (block * jv)) : kvs :=
  match l with [] => KVnil | (b, v) :: r => KVcons b v (kvs_of_list r) end.
Lemma list_of_kvs_of_list : ltac2:(zQ "70!h8!he!m0!r0!sc!hh1!hle>1l@1$0@2$1$3$2@3$4@1$0@2$1$3$2@1$5@1$6^1^1").
Proof. induction l as [|[b v] l IH]; cbn; [reflexivity| now rewrite IH]. Qed.
Lemma kvs_len_of_list : ltac2:(zQ "90!he!m0!r0!hmd!h8!hn5!sc!hle!hna>1l@1$4@2$0$2$1@3$6$5@1$8@1$7^1@2$3@2$0$2$1^1").
Proof. induction l as [|[b v] l IH]; cbn; [reflexivity| now rewrite IH]. Qed.
Lemma blocks_kvs_of_list : ltac2:(zQ "90!r0!h8!he!m0!sc!ho4!hle!hp0!hr0>1l@1$1@2$2$0$3@3$4@1$1$0@1$7@1$6^1@4$8@2$2$0$3$0$5^1").
Proof. induction l as [|[b v] l IH]; cbn; [reflexivity| now rewrite IH]. Qed.
Lemma blocks_items_kvitems : ltac2:(zQ "90!r0!h8!he!m0!sc!hvd!ho4!ig8!hr0>1l@1$1@2$2$0$3@3$4@1$1$0@1$7@1$5^1@4$8@2$2$0$3$0$6^1").
Proof. induction l as [|[b v] l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma kvs_height_of_list : ltac2:(zQ "b0!m0!r0!he!iib!h8!hn5!ij1!ikd!hle!il7!im1>1l@1$4@2$2$1$0>1h$5>0@3$7@2$2$1$0\2bv@2$2$1$0@2$3@1$9@3$6$1$0^1^2^2@2$3@1$a@1$8^3^2").
Proof.
  induction l as [|[b v] l IH]; intros h F; cbn; [lia|].
  pose proof (Forall_inv F) as F1. cbn in F1. pose proof (IH h (Forall_inv_tail F)). lia.
Qed.
Lemma flat_map_app' : forall {A B} (f : A -> list B) l1 l2, flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof. intros A B f l1 l2. induction l1; cbn; [reflexivity|]. rewrite IHl1, app_assoc. reflexivity. Qed.

Section K.
  Context {HCEIL : HeapCeil}.
  Lemma shdrsl_app : ltac2:(zQ "80!h8!he!io7!iof!m0!r0!ir5!irb>2l1@1$0@2$1$5$4>2l2@1$0@2$1$5$4>2b1@1$0@1$6@1$2#8>2b2@1$0@1$6@1$2#8>0@2$3^4^2>0@2$3^4^2@2$3@3$7@2$1$5$4^6^5@3$7@1$6@1$2#8^4^3").
  Proof.
    induction l1 as [|[b v] r IH]; intros l2 b1 b2 H1 H2; cbn in H1 |- *.
    - subst b1. exact H2.
    - ndestruct H1 as (hb & j4 & rest & -> & L & L4 & V & R). nexists hb, j4, (rest ++ b2).
      rewrite <- !app_assoc. split; [reflexivity|]. split; [exact L|]. split; [exact L4|]. split; [exact V|]. apply IH; assumption.
  Qed.
  Lemma shdrsl_split : ltac2:(zQ "e0!he!m0!r0!io7!iof!ir5!h8!it2!it9!iu3!hmd!hn5!iuc!iib>1l@1$6@2$0$2$1>2bs@1$6@1$5@1$3#8>1k$b>0@2$4^3^2>0@2$d^2@2$a@2$0$2$1^4@2$c@2$4@3$8@2$0$2$1^3^5@3$8@1$5@1$3#8@2$7Ni8^3^4@2$4@3$9@2$0$2$1^3^5@3$9@1$5@1$3#8@2$7Ni8^3^4").
  Proof.
    induction l as [|[b v] r IH]; intros bs k Hs Hk; cbn in Hk.
    - cbn in Hs. subst bs. rewrite !firstn_nil, !skipn_nil. destruct k; cbn; auto.
    - destruct k as [|k]; [cbn; rewrite skipn_O; split; [reflexivity| exact Hs]|].
      cbn [shdrsl] in Hs. ndestruct Hs as (hb & j4 & rest & -> & L & L4 & V & R).
      pose proof (slot_tail_length b j4 L4) as LT.
      replace (40 * S k)%nat with (length (hb ++ slot_tail b j4) + 40 * k)%nat by (rewrite length_app, L, LT; lia).
      rewrite app_assoc, firstn_app_2, skipn_app. rewrite (skipn_all2 (hb ++ slot_tail b j4)) by lia. cbn [firstn skipn].
      replace (length (hb ++ slot_tail b j4) + 40 * k - length (hb ++ slot_tail b j4))%nat with (40 * k)%nat by lia. cbn [app].
      destruct (IH rest k R ltac:(lia)) as [A1 A2]. split; [| exact A2].
      nexists hb, j4, (firstn (40 * k) rest). rewrite <- app_assoc. split; [reflexivity|]. split; [exact L|]. split; [exact L4|]. split; [exact V| exact A1].
  Qed.
  (* [comment removed for export] *)
  Lemma vhdr_word0 : ltac2:(zQ "d0!io7!ir5!h8!sc!hmd!hn5!irb!iuc!iv2!m0!iv7!jj8!jna>1v$9>2hb@1$2@1$1@1$0#8>0@2$a^2^1>0@3$3$5@2$4@1$1@1$0#8^2Nh8@2$8@1$2@1$1@1$0#8\4rest@1$2@1$1@1$0#8@2$7@3$3@1$2@1$1@1$0#8^4@3$6@1$1@1$0#8@1$b@1$cZ^1@3$3$5@2$4@1$1@1$0#8^1Nh0").
  Proof.
    intros v hb V L.
    assert (G : forall cs, hb = cells_bytes (C8 (wz 0) :: cs) -> exists rest, hb = le8 (wz 0) ++ rest /\ length rest = 16%nat).
    { intros cs E. exists (cells_bytes cs). assert (E' : hb = le8 (wz 0) ++ cells_bytes cs) by (rewrite E; reflexivity).
      split; [exact E'|]. rewrite E', length_app, length_le8 in L. lia. }
    destruct v as [k|nn|[[p T] sz] nn|[[[p T] sz]|] cap es|[[[p T] sz]|] cap ss]; cbn [vhdr] in V.
    - ndestruct V as (_ & j7 & pay & L7 & LP & E). eapply G. exact E.
    - ndestruct V as (_ & bs & LB & E). eapply G. exact E.
    - ndestruct V as (j7 & L7 & E). eapply G. exact E.
    - ndestruct V as (j7 & L7 & E). eapply G. exact E.
    - ndestruct V as (_ & _ & j7 & L7 & E). eapply G. exact E.
    - ndestruct V as (j7 & L7 & E). eapply G. exact E.
    - ndestruct V as (_ & _ & j7 & L7 & E). eapply G. exact E.
  Qed.
End K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section KW.
  Context {HCEIL : HeapCeil}.
  Variable H : ltac2:(zQ "10!mvb$0").
  Variable E : ltac2:(zQ "10!ng2$0").
  Hypothesis HH : ltac2:(zQ "10!ng9@3$0?5HCEIL?1H?1E").

  (* [comment removed for export] *)
  Lemma nodup_ids_app : ltac2:(zQ "a0!r0!jo0!js5!h8!jsd!irb!sc!jt3!jt9!ju0>2l1@1$3$0>2l2@1$3$0>1b$0>1c$0>0@2$9$2@4$8$0$2$1@3$5$0^4^3>0@3$4$0^3^5>0@3$4$0^3^5@1$7@3$6$2@1$1^5@1$1^4").
  Proof.
    intros l1 l2 b0 c0 ND Hb Hc EQ. revert ND Hb. induction l1 as [|x l1 IH1]; intros ND Hb; [exact Hb|].
    cbn in ND. apply List.NoDup_cons_iff in ND as [NI ND1]. destruct Hb as [<-|Hb]; [| exact (IH1 ND1 Hb)].
    apply NI. rewrite map_app. apply in_or_app. right. rewrite EQ. apply in_map. exact Hc.
  Qed.

  (* [comment removed for export] *)
  Lemma xpres_of_munch_scr : ltac2:(zQ "hd0!ju9!r0!kg6!iuc!h8!he!jsd!kgc!ij1!kh1!kh7!kl7!km0!jo0!sc!iv2!jt3!ikd!kq7!kr0!kv8!lg3!ll0!llc!lq4!lqd!js5!lr7!lre>2sx$h9>4FULL@1$4$1>5LBsub@1$4$1>2mz$9>2ma$9>2mb$9>2Wv@1$4@2$5$0$0>2SP$0>1X@1$4@2$5$0$0>0@4$h6?1H^9^8^6>0@3$h2^4^6^5>0@3$h3$h8^7^6>0@2$2@1$b?5HCEIL^5>0>1b$1>0@3$6$1^1^c@3$6$1^2^e>0@3$h1@2$5$0$0\2iv@2$5$0$0@2$a@2$3@2$2@1$b?5HCEIL@3$7$0$0^1@2$2@3$8$0$0^1^8@2$a>1a$0>0@2$3@2$2@3$7$0$0^2^1@2$hc^1@3$8$0$0^2@2$h4^9^2@2$f$1\1c$1@2$3@3$6$1^1^f@2$3>1b$1>0@3$6$1^1^f@1$h0@3$e$ha@1$d^2@1$d^3@2$3@2$2@1$c^1@3$7$0$0^2@2$2@3$8$0$0^2@2$hb@1$c^1@1$h7^1^8@5$h5^d^8^7^b^a").
  Proof.
    intros sx FULL LBsub mz ma mb Wv SP X HPx MU WM HS SUB FW a Ha [HC HX]. hcb.
    assert (HBLx : forall b, In b FULL -> blk_addr b + blk_size b <= hceil).
    { intros b Hb. eapply (hh_blocks_below H E HH); [exact HPx| exact Hb]. }
    assert (OUT : outside Wv a).
    { clear MU WM. induction Wv as [|[lo' hi'] Wv IH]; [exact I|]. cbn.
      pose proof (Forall_inv FW) as H1. cbn in H1.
      split; [| apply IH; apply (Forall_inv_tail FW)].
      destruct H1 as [[H1 H2]|[H1|(c & Hc & NE & H1 & H2)]].
      - destruct HC as [Hd|[[Hd _]|(b & Hb & Hr)]]; [lia| lia|]. pose proof (HBLx b (SUB b Hb)). unfold in_block in Hr. lia.
      - intros R. apply HX. apply H1. exact R.
      - destruct HC as [Hd|[[Hd Hd2]|(b & Hb & Hr)]].
        + pose proof (HBLx c Hc). lia.
        + pose proof (hh_blocks H E HH _ _ _ c HPx Hc) as (R1 & R2 & R3 & R4 & R5). unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK in Hd2. lia.
        + destruct (hh_disj H E HH _ _ _ b c HPx (SUB _ Hb) Hc (NE _ Hb)) as [Dj|Dj]; unfold in_block in Hr; lia. }
    split.
    - unfold wa. apply MU. rewrite unsigned_lit by lia. exact OUT.
    - intros Hw. apply WM. exact Hw.
  Qed.

  (* [comment removed for export] *)
  Lemma env_munch : ltac2:(zQ "he0!ju9!io7!ir5!iuc!mg0!kg6!he!lq4!mg8!mge!ij1!iv2!mh3!mi0!mm1!mmd!mn8!kh1!lr7!mo7!kgc!h8!sc!kh7!ikd!kl7!kq7!kr0!jna!mp6>1m$h1>2m'$h1>1W@1$h5@2$6$0$0>1B$0>2tp@1$2@1$1#k0>0@3$h6@1$2@1$1#k0^1@1$hc$hd>0@2$5@1$h9?5HCEIL^3>0@3$ha^5^7^6>0@3$hb$7^8^7>0@3$h8@2$6$0$0\2iv@2$6$0$0@2$h7@2$3@2$5+hjhgg0@3$h4$0$0^1@2$5@3$a$0$0^1^7@2$5@3$a$0$0^1+hggg0^7@2$3>0@3$h0?1H^a^7@3$h0?1H^a^8@2$3>0@2$b@1$2@1$1#k0\1e@1$2@1$1#k0@4$e$7^b@2$h2@2$h3@1$1#k0^7-q4@3$8$4@1$d^1@1$9$4@2$b@1$2@1$1#k0\1e@1$2@1$1#k0@4$e$7^b@2$h2@2$h3@1$1#k0^8-q4@3$8$4@1$d^1@1$9$4@2$3>0@1$c^a@1$c^a>0@2$f?1E^a@2$f?1E^a").
  Proof.
    intros m m' W B tp TP HB MU WM FW. hcb.
    assert (WIN : Forall (fun iv : Z * Z => 1249280 <= fst iv \/ snd iv <= 999424) W).
    { eapply Forall_impl; [| exact FW]. cbv beta. intros iv [K0|K0]; lia. }
    split. { intros AU. eapply (hh_rauxv_frame H E HH); [exact AU| exact MU| exact WM|]. eapply Forall_impl; [| exact FW]. cbv beta. unfold RAUXV_CELL. intros iv [K0|K0]; lia. }
    split. { intros [e ER]. exists e. eapply rw_cells_transport; [exact ER| exact MU| exact WM|]. rewrite TP. unfold RATP. rewrite unsigned_lit by lia. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
             clear MU WM WIN. induction W as [|[lo' hi'] W IH]; cbn; [exact I|]. pose proof (Forall_inv FW) as F1. cbn [fst snd] in F1.
             split; [lia| exact (IH (Forall_inv_tail FW))]. }
    split. { intros BSx. destruct (bj_statics_raw_of m BSx) as [salt' BSR']. eapply bj_statics_of_raw. eapply statics_raw_munch; [exact BSR'| exact MU| exact WM| exact WIN]. }
    intros IDx. eapply idle_munch; [exact (hh_static_range H E HH)| exact (hh_idle_frame H E HH)| exact IDx| exact MU| exact WIN].
  Qed.

  (* [comment removed for export] *)
  Lemma kvdeep_xpres : ltac2:(zQ "h22!r0!m0!he!ju9!kgc!h8!ij1!iuc!ikd!mpd!mq5!kh1!jsd!mge!ho4!mub!lg3!hr0&@2$7@3$9?5HCEIL^7@3$4$0$1^1@3$a?5HCEIL^7@3$6$0$1^1&\2bv@2$2$0$1~0>2LB@1$5$0>2SP$3>2ma$b>2mb$b>2l0@1$5@2$2$0$1>0@5$h0^5^4@1$d@2$2$3$3^3^2>0@2$f?5HCEIL^6>0>1c$0>0@3$c$0^1@4$h1@2$2$0$1$0$e^4@3$c$0^2^9>0@3$8@2$2$0$1~1^4@3$8@2$2$0$1~1^5").
  Proof.
    intros LB SP ma mb l0 XPx BBx SUBx Dx. apply Forall_forall. intros [b0 vq] Hin. pose proof (proj1 (Forall_forall _ _) Dx _ Hin) as [Kd Vd]. cbn [fst snd] in Kd, Vd |- *.
    assert (INl : forall c, In c (blocks_kv (b0, vq)) -> In c LB). { intros c Hc. apply SUBx. apply in_flat_map. exists (b0, vq). split; assumption. }
    split.
    - eapply kdeep_xpres; [exact XPx| constructor| exact BBx| exact Kd| apply INl; cbn; left; reflexivity].
    - eapply vdeep_xpres; [exact XPx| constructor| exact BBx| exact Vd| intros c Hc; apply INl; cbn; right; exact Hc].
  Qed.
End KW.
