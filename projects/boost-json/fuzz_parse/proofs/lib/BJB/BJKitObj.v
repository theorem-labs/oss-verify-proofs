(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep Exec TacX CellsX FP.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsObj AsStack0 AsWalk.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJB Require Import BJRep AXpres BJIface BJIfaceObj BJKitVS BJKitDtor BJKitPA.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list04prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJB5BJRep~~~~~~i42jv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsIface~~~~~~m55block37Corelib4Init5Logicqa2eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJB9BJKitDtor~~~~~~s3blist_of_kvs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJB8BJKitObj~~~~~~hh1bkvs_of_list06length03nati47kvs_lens39blocks_kvi4ablocks_kvs36Stdlib5Lists4Listhof8flat_map79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJBaBJIfaceObj~~~~~~hqe7kvitemsi4cblocks_items37Corelib4Init5Peanoig92le03snd37Corelib5Lists7ListDefii86Foralli47jheighti4akvs_height04cons03fstii83mapi48blocks_vhof6concat37Corelib7Numbers7BinNumsio74Nposs36shdrsl35stdpp9bitvectorbdefinitionsir12bv03app37Corelib4Init3Natit93mulii86firstnii85skipnqa3andqa2exi44vhdr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~jh73le879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~jl82wzm56blk_idm54bptrhof2Inqa3nothof5NoDupio71Z46Stdlib6ZArith6BinInt1Zjs32lem53memqa2orm58blk_addr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsShadow~~~~~~jv75aceil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~kje5asegsm58as_RHEAPm55as_Stm58blk_size79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs6CXXRep~~~~~~kq07rin_ivskq05xpres79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~kv05munchkv05wmonojs33addjs32lti45kdeepi45vdeep79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJB7BJKitVS~~~~~~llbdX_above_hceilllbcblocks_below79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~lra4cell03nili4abj_statics79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsConst~~~~~~mh06ACONSTm5bas_rauxv_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsStack0~~~~~~mm56stack0lra2C479OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~mr38rw_cellsir1bbv_unsignedm53ATPm53asrm5casan_rt_hyps" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint kvs_of_list (l : list (block * jv)) : kvs :=
  match l with [] => KVnil | (b, v) :: r => KVcons b v (kvs_of_list r) end.
Lemma list_of_kvs_of_list : ltac2:(zQ "70!h8!he!m0!q2!re!hg3!hl0>1l@1$0@2$1$3$2@3$4@1$0@2$1$3$2@1$5@1$6^1^1").
Proof. induction l as [|[b v] l IH]; cbn; [reflexivity| now rewrite IH]. Qed.
Lemma kvs_len_of_list : ltac2:(zQ "90!he!m0!q2!hlf!h8!hm7!re!hl0!hmc>1l@1$4@2$0$2$1@3$6$5@1$8@1$7^1@2$3@2$0$2$1^1").
Proof. induction l as [|[b v] l IH]; cbn; [reflexivity| now rewrite IH]. Qed.
Lemma blocks_kvs_of_list : ltac2:(zQ "90!q2!h8!he!m0!re!hn6!hl0!ho2!hq2>1l@1$1@2$2$0$3@3$4@1$1$0@1$7@1$6^1@4$8@2$2$0$3$0$5^1").
Proof. induction l as [|[b v] l IH]; cbn; [reflexivity| now rewrite IH]. Qed.
Lemma blocks_items_kvitems : ltac2:(zQ "90!q2!h8!he!m0!re!huf!hn6!hva!hq2>1l@1$1@2$2$0$3@3$4@1$1$0@1$7@1$5^1@4$8@2$2$0$3$0$6^1").
Proof. induction l as [|[b v] l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma kvs_height_of_list : ltac2:(zQ "b0!m0!q2!he!ihd!h8!hm7!ii3!ijf!hl0!ik9!il3>1l@1$4@2$2$1$0>1h$5>0@3$7@2$2$1$0\2bv@2$2$1$0@2$3@1$9@3$6$1$0^1^2^2@2$3@1$a@1$8^3^2").
Proof.
  induction l as [|[b v] l IH]; intros h F; cbn; [lia|].
  pose proof (Forall_inv F) as F1. cbn in F1. pose proof (IH h (Forall_inv_tail F)). lia.
Qed.
Lemma flat_map_app' : forall {A B} (f : A -> list B) l1 l2, flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof. intros A B f l1 l2. induction l1; cbn; [reflexivity|]. rewrite IHl1, app_assoc. reflexivity. Qed.
(* [comment removed for export] *)
Lemma concat_map_blocks_kv : ltac2:(zQ "d0!q2!m0!he!h8!im0!im6!ii3!re!imb!hn6!in2!ind!hq2>1l@1$3@2$2$0$1@3$7@1$3$0@2$b$0@4$8@2$2$0$1@1$3$0\2bv@2$2$0$1@3$4$0@3$5$0$1^1@1$a@3$6$0$1^1^1@4$c@2$2$0$1$0$9^1").
Proof. induction l as [|[b v] l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Section K.
  Context {HCEIL : HeapCeil}.
  Lemma shdrsl_app : ltac2:(zQ "80!h8!he!iq0!iq8!m0!q2!ise!it4>2l1@1$0@2$1$5$4>2l2@1$0@2$1$5$4>2b1@1$0@1$6@1$2#8>2b2@1$0@1$6@1$2#8>0@2$3^4^2>0@2$3^4^2@2$3@3$7@2$1$5$4^6^5@3$7@1$6@1$2#8^4^3").
  Proof.
    induction l1 as [|[b v] r IH]; intros l2 b1 b2 H1 H2; cbn in H1 |- *.
    - subst b1. exact H2.
    - ndestruct H1 as (hb & j4 & rest & -> & L & L4 & V & R). nexists hb, j4, (rest ++ b2).
      rewrite <- !app_assoc. split; [reflexivity|]. split; [exact L|]. split; [exact L4|]. split; [exact V|]. apply IH; assumption.
  Qed.
  Lemma shdrsl_split : ltac2:(zQ "e0!he!m0!q2!iq0!iq8!ise!h8!iub!iv2!ivc!hlf!hm7!jg5!ihd>1l@1$6@2$0$2$1>2bs@1$6@1$5@1$3#8>1k$b>0@2$4^3^2>0@2$d^2@2$a@2$0$2$1^4@2$c@2$4@3$8@2$0$2$1^3^5@3$8@1$5@1$3#8@2$7Ni8^3^4@2$4@3$9@2$0$2$1^3^5@3$9@1$5@1$3#8@2$7Ni8^3^4").
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
  Lemma vhdr_word0 : ltac2:(zQ "d0!iq0!ise!h8!re!hlf!hm7!it4!jg5!jgb!m0!jh0!jl1!jp3>1v$9>2hb@1$2@1$1@1$0#8>0@2$a^2^1>0@3$3$5@2$4@1$1@1$0#8^2Nh8@2$8@1$2@1$1@1$0#8\4rest@1$2@1$1@1$0#8@2$7@3$3@1$2@1$1@1$0#8^4@3$6@1$1@1$0#8@1$b@1$cZ^1@3$3$5@2$4@1$1@1$0#8^1Nh0").
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
  Variable H : ltac2:(zQ "10!ngf$0").
  Hypothesis RT : ltac2:(zQ "10!nh5@2$0?5HCEIL?1H").

  (* [comment removed for export] *)
  Lemma nodup_ids_app : ltac2:(zQ "a0!q2!jp9!jq2!h8!jq9!it4!re!jqf!imb!jr5>2l1@1$3$0>2l2@1$3$0>1b$0>1c$0>0@2$9$2@4$8$0$2$1@3$5$0^4^3>0@3$4$0^3^5>0@3$4$0^3^5@1$7@3$6$2@1$1^5@1$1^4").
  Proof.
    intros l1 l2 b0 c0 ND Hb Hc EQ. revert ND Hb. induction l1 as [|x l1 IH1]; intros ND Hb; [exact Hb|].
    cbn in ND. apply List.NoDup_cons_iff in ND as [NI ND1]. destruct Hb as [<-|Hb]; [| exact (IH1 ND1 Hb)].
    apply NI. rewrite map_app. apply in_or_app. right. rewrite EQ. apply in_map. exact Hc.
  Qed.

  (* [comment removed for export] *)
  Lemma xpres_of_munch_scr : ltac2:(zQ "hd0!jre!q2!jtb!jg5!h8!he!jq9!im6!ii3!ju1!ju7!juc!jp9!kj5!re!jgb!jqf!ijf!kn9!ko2!kod!kp5!jq2!ktc!ku7!lic!lj5!lje!lk5>2sx@1$h4?1H>4FULL@1$4$1>5LBsub@1$4$1>2mz$9>2ma$9>2mb$9>2Wv@1$4@2$5$0$0>2SP$0>1X@1$4@2$5$0$0>0@4$h3?1H^9^8^6>0@3$h9^4^6^5>0@3$ha$h2^7^6>0@2$2@1$d?5HCEIL^5>0>1b$1>0@3$6$1^1^c@3$6$1^2^e>0@3$h1@2$5$0$0\2iv@2$5$0$0@2$a@2$3@2$2@1$d?5HCEIL@3$7$0$0^1@2$2@3$8$0$0^1^8@2$a>1a$0>0@2$3@2$2@3$7$0$0^2^1@2$hc^1@3$8$0$0^2@2$h7^9^2@2$f$1\1c$1@2$3@3$6$1^1^f@2$3>1b$1>0@3$6$1^1^f@1$h0@3$e$h6@1$c^2@1$c^3@2$3@2$2@1$b^1@3$7$0$0^2@2$2@3$8$0$0^2@2$hb@1$b^1@1$h5^1^8@7$h8?5HCEIL?1H^d^8^7^b^a").
  Proof.
    intros sx FULL LBsub mz ma mb Wv SP X HPx MU WM HS SUB FW.
    intros a Ha [HC HX]. acb.
    pose proof (ah_fsb H RT _ _ _ HPx) as (F1 & F2 & F3).
    assert (OUT : outside Wv a).
    { clear MU WM. induction Wv as [|[lo' hi'] Wv IH]; [exact I|]. cbn.
      pose proof (Forall_inv FW) as H1. cbn in H1.
      split; [| apply IH; apply (Forall_inv_tail FW)].
      destruct H1 as [[H1 H2]|[H1|(c & Hc & NE & H1 & H2)]].
      - (* [comment removed for export] *)
        intros K. assert (SP <= a \/ a < aceil) as [C|C]; [| lia | lia].
        unfold aclient_addr in HC. destruct HC as [Hc|Hc]; [left; exact Hc| right].
        destruct Hc as [Hc|[(b & Hb & Hr)|[(b & Hb & Hr)|[Hc|[Hc|Hc]]]]].
        + unfold aimg_client, ATLS_PRIV_LO, ATLS_PRIV_HI, ATSD0, ATP in *. lia.
        + pose proof (ah_blocks H RT _ _ _ _ HPx (SUB _ Hb)) as (_ & _ & _ & _ & R & _). unfold in_block in Hr |- *. lia.
        + pose proof (ah_blocks H RT _ _ _ _ HPx (SUB _ Hb)) as (_ & _ & R0 & R1 & R & _).
          pose proof (sh_below_aceil (blk_addr b + blk_size b + 8) ltac:(unfold AIMG_TOP, AAPP_HI in *; lia)).
          unfold in_block_sh, nsh, sh in *. rewrite ASHADOW_BASE_val in *. Z.div_mod_to_equations. lia.
        + lia.
        + pose proof (sh_below_aceil (as_FSB H + AFS_SIZE) ltac:(unfold AIMG_TOP, AAPP_HI, AFS_SIZE in *; lia)).
          unfold AFS_SIZE in *. lia.
        + unfold AHI_LO in *. lia.
      - intros R. apply HX. apply H1. exact R.
      - (* [comment removed for export] *)
        pose proof (ah_blocks H RT _ _ _ _ HPx Hc) as BRc. pose proof (ablock_facts H _ _ BRc) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
        cbn [blk_addr blk_size] in *.
        destruct HC as [Hd|[Hd|[(b & Hb & Hr)|[(b & Hb & Hr)|[Hd|[Hd|Hd]]]]]].
        + lia.
        + unfold aimg_client in Hd. unfold AIMG_TOP in *. lia.
        + destruct (ah_disj H RT _ _ _ b c HPx (SUB _ Hb) Hc (NE _ Hb)) as [Dj|Dj]; unfold in_block in Hr; lia.
        + pose proof (ablock_facts H _ _ (ah_blocks H RT _ _ _ _ HPx (SUB _ Hb))) as (_ & _ & _ & _ & _ & _ & S1 & S2 & _).
          unfold in_block_sh in Hr. unfold ALOWSH_LO, AHI_LO in *. lia.
        + unfold AFS_SIZE in *. lia.
        + unfold sh in *. rewrite ?ASHADOW_BASE_val in *. unfold ALOWSH_LO, AHI_LO, AFS_SIZE, AIMG_TOP, AAPP_HI in *. Z.div_mod_to_equations. lia.
        + unfold sh in *. rewrite ?ASHADOW_BASE_val in *. unfold ALOWSH_LO, AHI_LO, AIMG_TOP, AAPP_HI in *. Z.div_mod_to_equations. lia. }
    split.
    - unfold wa. apply MU. rewrite unsigned_lit by lia. exact OUT.
    - intros Hw. apply WM. exact Hw.
  Qed.

  (* [comment removed for export] *)
  Lemma kvdeep_xpres : ltac2:(zQ "h22!q2!m0!he!h8!jre!im6!ii3!jg5!ijf!lkb!ll3!ju1!jq9!hn6!lp9!lqa!ku7!hq2&@2$7@3$9?5HCEIL^8@3$5$0$1^1@3$a?5HCEIL^8@3$6$0$1^1&\2bv@2$2$0$1~0>2LB@1$3$0>2SP$4>1X@1$3@2$2$4$4>2ma$b>2mb$b>2l0@1$3@2$2$0$1>0@7$h0?5HCEIL?1H^6^5^4^3^2>0@3$e?5HCEIL?1H^5>0@3$f?5HCEIL?1H^8>0>1c$0>0@3$c$0^1@4$h1@2$2$0$1$0$d^5@3$c$0^2^b>0@3$8@2$2$0$1~1^5@3$8@2$2$0$1~1^6").
  Proof.
    intros LB SP X ma mb l0 XPx HX BBx SUBx Dx. apply Forall_forall. intros [b0 vq] Hin. pose proof (proj1 (Forall_forall _ _) Dx _ Hin) as [Kd Vd]. cbn [fst snd] in Kd, Vd |- *.
    assert (INl : forall c, In c (blocks_kv (b0, vq)) -> In c LB). { intros c Hc. apply SUBx. apply in_flat_map. exists (b0, vq). split; assumption. }
    split.
    - eapply (kdeep_xpres H); [exact XPx| exact HX| exact BBx| exact Kd| apply INl; cbn; left; reflexivity].
    - eapply (vdeep_xpres H); [exact XPx| exact HX| exact BBx| exact Vd| intros c Hc; apply INl; cbn; right; exact Hc].
  Qed.

  (* [comment removed for export] *)
  Lemma env_frame : ltac2:(zQ "i50!jre!iq0!jg5!ise!q2!lv6!jtb!he!jgb!kn9!ju1!lje!im0!im6!h8!lve!ii3!mg3!mkd!ml7!juc!mq3!mqd!mue!mva!re!ju7!ijf!ng9!ko2!kod!kp5!kj5!lic!lj5!jp3!jq9>1s@1$he?1H>2LB@1$e$4>2m0$a>1m$a>2m'$a>1W@1$e@2$7$0$0>1B$0>2tp@1$3@1$1#k0>0@4$hd?1H^8^7^6>0@3$h9@1$3@1$1#k0^2@1$i3$hc>0@3$i1^5^7^6>0@3$i2$9^8^7>0@3$hb@2$7$0$0\2iv@2$7$0$0@2$ha@2$2@2$6@1$i0?5HCEIL@3$d$0$0^1@2$6@3$h0$0$0^1^7@2$8$4\1b$4@2$2@3$i4$4^1^d@2$2@2$6@1$h4^1@3$d$0$0^2@2$6@3$h0$0$0^2@2$b@1$h4^1@1$hf^1^7@2$2>0@3$h3?1H^a^7@3$h3?1H^a^8@2$2>0@2$8@1$3@1$1#k0\1e@1$3@1$1#k0@4$h7$9^b@2$b@2$h8@1$1#k0^7-q4@3$c$5@1$h6^1@1$f$5@2$8@1$3@1$1#k0\1e@1$3@1$1#k0@4$h7$9^b@2$b@2$h8@1$1#k0^8-q4@3$c$5@1$h6^1@1$f$5@2$2>0@1$h1^a@1$h1^a@2$2>0@1$h2^a@1$h2^a>2lo$0>2hi$0>0@4$h5?5HCEIL^c^2^1@4$h5?5HCEIL^c^3^2").
  Proof.
    intros s LB m0 m m' W B tp HP TP MU WM FW. acb.
    assert (WOK : Forall (aclient_write_ok H LB) W).
    { eapply Forall_impl; [| exact FW]. cbv beta. intros [l h] [[K1 K2]|(b & Hb & K1 & K2)]; [left; cbn; exact K1|].
      destruct b as [[p A] n]. cbn in K1, K2. replace h with (l + (h - l)) by lia.
      exact (proj1 (block_window_ok H RT s LB m0 [] p A n l (h - l) HP Hb K1 ltac:(lia))). }
    assert (ACW : Forall aconst_ok W).
    { eapply Forall_impl; [| exact FW]. cbv beta. intros [l h] [[K1 K2]|(b & Hb & K1 & K2)].
      - cbn in K1, K2. apply aconst_ok_high; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia.
      - destruct b as [[p A] n]. cbn in K1, K2. replace h with (l + (h - l)) by lia.
        exact (proj2 (proj2 (block_window_ok H RT s LB m0 [] p A n l (h - l) HP Hb K1 ltac:(lia)))). }
    assert (LOW : Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W).
    { eapply Forall_impl; [| exact FW]. cbv beta. intros [l h] [[K1 K2]|(b & Hb & K1 & K2)]; cbn.
      - cbn in K1, K2. unfold AIMG_TOP in *. lia.
      - cbn in K1, K2. pose proof (ah_blocks H RT _ _ _ _ HP Hb) as (_ & _ & _ & R4 & _). lia. }
    assert (S0W : Forall stack0_ok W).
    { eapply Forall_impl; [| exact FW]. cbv beta. intros [l h] [[K1 K2]|(b & Hb & K1 & K2)].
      - left. cbn in K1, K2 |- *. unfold AHI_LO in *. lia.
      - pose proof (ah_blocks H RT _ _ _ _ HP Hb) as (_ & _ & _ & _ & _ & _ & APPb). eapply stack0_ok_aapp; [exact APPb| exact K1| exact K2]. }
    split. { intros AU. eapply (ah_rauxv_frame H RT); [exact AU| exact MU| exact WM| exact WOK]. }
    split. { intros [e ER]. exists e. eapply rw_cells_transport; [exact ER| exact MU| exact WM|]. rewrite TP. unfold ATP, wz. rewrite unsigned_lit by lia.
             cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
             clear MU WM WOK ACW S0W FW. induction W as [|[lo' hi'] W IH]; cbn; [exact I|]. pose proof (Forall_inv LOW) as F1. cbn [fst snd] in F1.
             split; [unfold AIMG_TOP in F1; lia| exact (IH (Forall_inv_tail LOW))]. }
    split. { intros BSx. eapply bj_statics_frame; [exact BSx| exact MU| exact WM| exact LOW]. }
    split. { intros AC. eapply ACONST_frame; [exact AC| exact MU| exact WM| exact ACW]. }
    intros lo hi SK. eapply stack0_transport; [exact SK| exact MU| exact WM| exact S0W].
  Qed.
End KW.
