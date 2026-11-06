(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require RefU0Gc5. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_malloc_free MallocTree MallocModel_B F_ntf_B F_am_K.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes03nat37Corelib7Numbers7BinNumshd4Nposhd1Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~k15zeros79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ob8bytes_at79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~t05rsegs46Stdlib6ZArith6BinInt1Zhh53addhh52lehh56of_nat35stdpp9bitvectorbdefinitionshk42bv06option04list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hn5acells_size37Corelib4Init5Logichrf2eqhn54cellhn5bcells_byteshn58cells_wfob5wr_at79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~ig48rw_cellshd1N35stdpp7numbers1Nikf6eq_dec79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~ima4area35stdpp7numbers1Zir06eq_decima4aptr25stdpp9countableit3bN_countable04consit3bZ_countableit3eprod_countable25stdpp9decidablejhabprod_eq_dec04prodk12wzima4concima6region25stdpp4gmapjl74gmap04Some03nilhn52C4hn52C879OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUaRMallocRep~~~~~~jo25rmrepima7a_checkima8a_nslotsima7s_areas25stdpp4basejuf6lookupjl7bgmap_lookup03fst04pair79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~khf5munchkhf5wmonoima6mkAreaima6mstateima9s_regionsima9set_areasjuf6insertjuf7is_Some25stdpp8fin_mapskr0amap_insertjl7h2gmap_partial_alterima4meta03sndima6NSLOTS04Nonehrf3andima8AREA_HDRima9META_SIZEhh52lthh53mulhrf3notk15lr_lok1ameta_cellshn52CBima7RKGroupima4aaddima5meta0ima6r_baseima6r_kindima5r_lenima5rkindimabround_up_pgima7s_metashh56modulo79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUcRMallocKit_B~~~~~~lr78rrepfoot" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Lemma rbytes_at_zeros_sub : ltac2:(zQ "b0!h8!j6!jd!o3!s5!hgd!hid!hj4!hja!hm1!hm7>1m>0@1$9@1$1#k0@1$a@1$9@1$1#8>1A$2>1n$0>3off$2>1k$0>0@4$4$5^5^4@1$3^3>0@2$7Z^3>0@2$7@2$6^4@1$8^3@1$8^5@4$4$5^8@2$6^7^5@1$3^4").
Proof. intros m A n off k. try hcb. try hsb.
  (intros nd_i1 Hoff Hk; ndestruct nd_i1 as (H0 & H1 & HB)). rewrite zeros_length in H1, HB. split; [lia|]. rewrite zeros_length. split; [lia|].
  intros i Hi. replace (A + off + Z.of_nat i) with (A + Z.of_nat (Z.to_nat off + i)) by lia.
  rewrite HB by lia. unfold zeros. rewrite !nth_error_repeat by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rrw_cells_of_zeros : ltac2:(zQ "h30!j6!hgd!hja!hm1!hmf!jd!o3!hr1!hid!hj4!h8!hm7!ht3!ht9!hu1!hv0!s5!hvc!ijf>1m>0@1$3@1$0#k0@1$b@1$3@1$0#8>1A$5>1n$a>3off$5>2cs@1$4$d>0@4$h0$1^5^4@1$6^3>0@4$h1$1^6^5@1$2^4>0@1$f^3>0@3$c@1$4@1$3@1$0#8@1$e^4@1$6@1$7^4>0@2$9Z^6>0@2$9@2$8^7@1$2@1$7^6@1$2^8@4$h2$1^b@2$8^a^8^7").
Proof. intros m A n off cs. try hcb. try hsb.
  intros HB HW WF E Hoff Hsz. apply rw_cells_of_bytes; [exact WF| |].
  - rewrite E. apply (rbytes_at_zeros_sub m A n off); assumption.
  - eapply wr_at_sub; [exact HW| lia| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rmrep_set_area_next : ltac2:(zQ "ie2!jd!ikb!im0!iq8!is1!isb!iu4!iv3!ht9!iv9!jg8!jib!jja!j6!jk0!jk5!jkd!hm1!jm3!hm7!jmb!jn1!jn6!jnc!js4!hgd!jsd!jt8!ju4!hid!jvb!kg5!kh4!kh9!ht3!klb!km4!ijf!kmd!kn7!ko1!koe!kpb!kq5!ks0!kse&>0@1$h1@1$d#k0@1$h3@1$h1@1$d#8&@4$h2$5@4$b$1$2$0$4@6$a$1$2$6$0$4$9$3>2st$i7>1m~0>2m'~0>1a$5>2ar$3>1p@2$c$1$0>0@4$h8?5HCEIL?4HSEC^6^5>0@3$i2@1$h3$3@6$he$5$3~1@4$hf$5@4$b$1$2$0$4@6$a$1$2$6$0$4$9$3^4@1$hc^7@2$h4$3^3>0@2$ib$h0@6$he$1$h0@4$h2$1$2$6$h0@4$hf$1$2$6$h0@3$i0$1$0^3@1$i8^8>0@3$i3@3$7@2$c$0$0@4$i1$0$0@2$hd@2$f^9^6+8@2$hd@2$f^9^6+h0@1$h5@2$c$0$0^8^7>0@3$i4$h9^9^8>0@4$i5$h9^9@2$f^b^8@3$7$8@1$h7@1$e@1$ha^7@3$7$8@1$h7@1$e@2$f^b^6@3$7$8@1$h6@1$e@1$hb^7@3$7$8@1$h6@1$eZ@1$h5$8@4$h8?5HCEIL?4HSEC@2$i9@7$ia$5$3~1@4$ic$5$3~1@4$id$5@4$b$1$2$0$4@6$a$1$2$6$0$4$9$3^9@3$i6@1$ha^8@2$h4@2$c$1$0^7@1$hb^8@1$hc^c^c^a").
Proof. try hcb. try hsb.
  intros st m m' a ar p MR Ha Hp MU WM CH.
  npose MR as (WF & CX & GL & AR & GR & SH). npose WF as (Hres & WR & DJ & WA & WG).
  ndestruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in RBC.
  set (st' := set_areas _ st).
  assert (Hconc : forall q, conc st' q = conc st q) by (intros; reflexivity).
  assert (AG : forall A cs, rw_cells rsegs m A cs -> (A + Z.of_nat (cells_size cs) <= conc st a + 8 \/ conc st a + 16 <= A) -> rw_cells rsegs m' A cs).
  { intros A cs H HD. pose proof (rw_cells_bound rsegs m A cs H). eapply rrw_cells_agree; [exact H| | exact WM].
    intros x Hx. apply MU. rewrite wa_unsigned by lia. cbn. lia. }
  split; [|split; [|split; [|split; [|split]]]].
  - (* [comment removed for export] *) split; [exact Hres|]. split; [exact WR|]. split; [exact DJ|]. split; [| exact WG].
    intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. destruct (decide (a' = a)) as [->|NE].
    + rewrite lookup_insert_eq in Ha'. exact (WA a ar Ha).
    + rewrite lookup_insert_ne in Ha' by congruence. exact (WA a' ar' Ha').
  - (* [comment removed for export] *) ndestruct CX as (C1 & C2 & C3 & C4 & C5 & C6). pose proof (rreserved_disjoint _ _ (proj2 (proj2 (proj2 (proj2 (WR _ _ Hra)))))) as (_ & _ & DA3 & DA).
    unfold rmrep_ctx. change (ctx_head_cells st') with (ctx_head_cells st). change (actives st') with (actives st).
    change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st).
    change (ctx_tail_cells st') with (ctx_tail_cells st).
    split; [apply AG; [exact C1| cbn; unfold RCTX; lia]|].
    split; [eapply ru64arr_agree; [exact C2| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite actives_length in Hx; unfold RCTX in Hx; lia); rewrite actives_length in Hx; cbn; unfold RCTX in Hx; lia| exact WM]|].
    split; [eapply ru64arr_agree; [exact C3| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite usages_length in Hx; unfold RCTX in Hx; lia); rewrite usages_length in Hx; cbn; unfold RCTX in Hx; lia| exact WM]|].
    split; [eapply ru8arr_agree; [exact C4| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite unmap_seqs_length in Hx; unfold RCTX in Hx; lia); rewrite unmap_seqs_length in Hx; cbn; unfold RCTX in Hx; lia| exact WM]|].
    split; [eapply ru8arr_agree; [exact C5| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite bouncess_length in Hx; unfold RCTX in Hx; lia); rewrite bouncess_length in Hx; cbn; unfold RCTX in Hx; lia| exact WM]|].
    apply AG; [exact C6| cbn; unfold RCTX; lia].
  - (* [comment removed for export] *) ndestruct GL as (G1 & G2 & G3 & G4 & G5 & G6). pose proof (rreserved_disjoint _ _ (proj2 (proj2 (proj2 (proj2 (WR _ _ Hra)))))) as (_ & _ & DA3 & DA).
    split; [apply AG; [exact G1| cbn; unfold RMLOCK; lia]|]. split; [apply AG; [exact G2| cbn; unfold RNEED_LOCKS; lia]|].
    split; [apply AG; [exact G3| cbn; unfold RPAGE_SIZE; lia]|]. split; [apply AG; [exact G4| cbn; unfold RGOT_SSP; lia]|].
    split; [apply AG; [exact G5| cbn; unfold RSSP_GUARD; lia]|]. apply AG; [exact G6| cbn; lia].
  - (* [comment removed for export] *) intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. unfold rarea_rep. rewrite !Hconc.
    change (get_meta_rec st') with (get_meta_rec st).
    assert (MC : forall r, meta_cells st' r = meta_cells st r) by (intros; reflexivity).
    destruct (decide (a' = a)) as [->|NE].
    + rewrite lookup_insert_eq in Ha'. inversion Ha'; subst ar'. cbn [a_check a_next a_nslots]. ndestruct (AR a ar Ha) as (A1 & A2 & A3).
      split; [unfold pw; cbn [oconc]; rewrite Hconc; exact CH|]. split.
      * intros k Hk. rewrite MC. apply AG; [apply A2; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add]. unfold AREA_HDR, META_SIZE. lia.
      * apply AG; [exact A3| cbn; lia].
    + rewrite lookup_insert_ne in Ha' by congruence. ndestruct (AR a' ar' Ha') as (A1 & A2 & A3).
      ndestruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
      assert (DIS : conc st a' + 4096 <= conc st a \/ conc st a + 4096 <= conc st a').
      { destruct (N.eq_dec (fst a') (fst a)) as [E|NE2].
        - rewrite E, Hra in Hra'. assert (ra' = ra) by congruence. subst ra'.
          assert (snd a' <> snd a) by (intros E2; apply NE; destruct a, a'; cbn in *; congruence).
          Z.div_mod_to_equations. lia.
        - pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra').
          destruct (DJ _ _ _ _ Hra' Hra NE2); lia. }
      change (pw st' (a_next ar')) with (pw st (a_next ar')).
      split; [apply AG; [exact A1| cbn; lia]|]. split.
      * intros k Hk. rewrite MC. apply AG; [apply A2; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add]. unfold AREA_HDR, META_SIZE, NSLOTS in *. lia.
      * apply AG; [exact A3| cbn; lia].
  - (* [comment removed for export] *) intros b gh Hb. ndestruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [| exact Hw8].
    rewrite Hconc. change (pw st' (g_meta gh)) with (pw st (g_meta gh)). apply AG; [exact R|].
    ndestruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RBb & RBCb).
    assert (NE : fst b <> fst a) by (intros E; rewrite E, Hra in Hrb; assert (rb = ra) by congruence; subst; exact (NK Krb)).
    pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group rb Krb).
    cbn. destruct (DJ _ _ _ _ Hrb Hra NE); lia.
  - (* [comment removed for export] *) intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB]. change (get_shadow st' rid) with (get_shadow st rid). split.
    + eapply wr_at_transport; [exact HWr| exact WM].
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [B V]. split; [| exact V].
      eapply rbytes_at_agree; [exact B|]. cbn. intros x Hx. apply MU. rewrite wa_unsigned by (destruct (WR _ _ Hr) as (? & ? & ? & RC & ?); hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in RC; pose proof (round_up_pg_ge (r_len r)); lia).
      assert (NE : rid <> fst a) by (intros E; rewrite E, Hra in Hr; assert (r = ra) by congruence; subst; exact (NK Hk)).
      pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group r Hk). cbn. destruct (DJ _ _ _ _ Hr Hra NE); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rmrep_new_area : ltac2:(zQ "k01!jd!ikb!im0!is1!isb!iq8!iu4!ht9!iv9!jg8!jib!jkd!hid!iv3!ht3!ku5!hj4!jm3!hm7!kud!jk0!kv2!kvc!ijf!hgd!jk5!jvb!kg5!jn1!lg2!j6!jn6!jnc!js4!lg9!lh5!ju4!li2!li8!hm1!jmb!kh4!lif!lj6!lje!o3!lkb!ll1!llc!lm4!kmd!kn7!lmd!ln7!lo1!loa!lp3!lq2!ko1!koe!lqd!kpb!ks0!kse&@4$h1$4@4$a$1$2$0$3@6$9$1$2$6$0$3$8$5>2st$j3>1m>0@1$i7@1$he#k0@1$h2@1$i7@1$he#8>1p$4>1r$b>3chk$0>0@4$i1?5HCEIL?4HSEC^5^4>0@3$e@1$h2$5@6$ha$4$5~0@4$hb$4@4$a$1$2$0$3@6$9$1$2$6$0$3$8$5^4@1$i4^6@1$h6$5>0@3$e@1$h2$b@6$ha$1$b@4$h1$1$2$6$b@4$hb$1$2$6$b@3$i9$1$0^5@1$ja^7@2$i8$b^4>0@1$ia@3$e$j7@1$j5^5$if>0@2$h0Z@3$h3$1$0^7>0@2$h0@2$c@3$h3$1$0^8+hgg0@1$j8@1$j6^7>0@3$e$0@2$jc@3$h3$1$0^9+hgg0Z>0@2$h0@1$ib^9@2$c@1$j4^9@3$h3$1$0^a>0>1k$0>0@2$hd@2$h0Z^1@2$i5^1$h5@3$e@1$h2$f@6$ha$4$f@4$h1$4@4$a$1$2$0$3@6$9$1$2$6$0$3$8$f@4$hb$4@4$a$1$2$0$3@6$9$1$2$6$0$3$8$f@2$j0^d@2$c$i2@2$i6$i3^2@1$j9^f@1$h6$f>0@4$h7$h8^d@2$h9^e^c@3$d$7@1$i0@1$h4^a@3$d$7@1$i0@1$h4Z@3$d$7@1$hf@1$h4$h5@3$d$7@1$hf@1$h4Z@1$hc$7>0>1k$0>0@2$hd@2$h0Z^1@2$i5^1$h5@4$h7$h8^h0@2$c@2$c@2$h9^h1^f$i2@2$i6$i3^2@2$ic^h1$j1>0@4$h7$h8^f@2$c@2$h9^h0^e+vu0@3$d$7@2$ieNi0@1$idNi0@1$hc$7@4$i1?5HCEIL?4HSEC@2$jb@7$jd$4$5~0@4$je$4$5~0@4$jf$4@4$a$1$2$0$3@6$9$1$2$6$0$3$8$5^f@3$j2^d@1$h6$4$h5@1$i4^h1^h1^h0").
Proof. try hcb. try hsb.
  intros st m p r chk MR Hnone Hr NK S0 S1 SAL SLR FRESH HDR SLOTS PAD.
  npose MR as (WF & CX & GL & AR & GR & SH). npose WF as (Hres & WR & DJ & WA & WG).
  set (st' := set_areas _ st).
  assert (Hconc : forall q, conc st' q = conc st q) by (intros; reflexivity).
  split; [|split; [|split; [|split; [|split]]]].
  - split; [exact Hres|]. split; [exact WR|]. split; [exact DJ|]. split; [| exact WG].
    intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. destruct (decide (a' = p)) as [->|NE].
    + exists r. repeat split; assumption.
    + rewrite lookup_insert_ne in Ha' by congruence. exact (WA a' ar' Ha').
  - exact CX.
  - exact GL.
  - intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. unfold rarea_rep. rewrite !Hconc.
    change (get_meta_rec st') with (get_meta_rec st). change (meta_cells st') with (meta_cells st).
    destruct (decide (a' = p)) as [->|NE].
    + rewrite lookup_insert_eq in Ha'. inversion Ha'; subst ar'. cbn [a_check a_next a_nslots].
      split; [exact HDR|]. split; [| exact PAD].
      intros k Hk. unfold get_meta_rec. rewrite (FRESH k Hk). cbn [default]. apply SLOTS. exact Hk.
    + rewrite lookup_insert_ne in Ha' by congruence. exact (AR a' ar' Ha').
  - exact GR.
  - exact SH.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rfresh_page_avoids : ltac2:(zQ "i90!ikb!jd!jkd!im0!iq8!kud!ht3!isb!hj4!iu4!is1!hm7!hid!lif!j6!jk5!jvb!hm1!iv9!jg8!jib!jm3!kg5!kvc!jmb!kh4!lg2!lj6!lvb!js4!ll1!kn7!lmd!ln7!lo1!loa!lp3!ju4!ko1!li2!lqd>2st$hf>1m>0@1$h1@1$e#k0@1$b@1$h1@1$e#8>1p$7>1r$2>1a$1>0@4$hd?5HCEIL?4HSEC^5^4>0@3$6@1$b$2@6$h0$0$2@4$h5$0$3$9$2@4$h6$0$3$9$2@3$h9$0$1^4@1$i6^6@2$h8$2^3>0@1$d@3$6$i3@1$i1^4$he>0@2$8Z@3$5$0$1^6>0@2$8@2$c@3$5$0$1^7+hgg0@1$i4@1$i2^6>0@3$6$1@2$i8@3$5$0$1^8+hgg0Z>0@2$8@1$hb^8@2$c@1$i0^8@3$5$0$1^9>0@3$6@1$b$4@6$h0$7$4@4$h5$7@4$h4$0$3$1$a@6$h3$0$3$9$1$a$h2$4@4$h6$7@4$h4$0$3$1$a@6$h3$0$3$9$1$a$h2$4^a@1$i5^c@1$h7$4>0@2$ha@2$8@2$f^d^b^9@2$i7^9@2$c@2$f^d^b+hgg0@1$d@2$hc^e^a").
Proof. try hcb. try hsb.
  intros st m p r a MR Hr NK S0 S1 SAL SLR ANone Ha.
  pose proof MR as (WF & _). npose WF as (Hres & WR & DJ & WA & WG).
  pose proof (conc_region' st p r Hr) as Cp.
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (DR1 & _ & DR23 & DR2). hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in RBC.
  pose proof (lr_lo_ge r) as LRG. pose proof (round_up_pg_ge (r_len r)) as RU.
  intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
  - unfold RCTX in C. lia.
  - unfold RMLOCK in C. lia.
  - unfold RNEED_LOCKS in C. lia.
  - unfold RPAGE_SIZE in C. lia.
  - ndestruct C as (ak & ar & Hak & Hin).
    ndestruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NKa & _).
    destruct (N.eq_dec (fst ak) (fst p)) as [E|NE].
    + rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra.
      assert (NEo : snd ak <> snd p).
      { intros E2. assert (ak = p) by (destruct ak, p; cbn in *; congruence). subst ak. rewrite ANone in Hak. discriminate. }
      Z.div_mod_to_equations. lia.
    + pose proof (rarea_lr_lo st ak ar ra WF Hak Hra). destruct (DJ _ _ _ _ Hra Hr NE); lia.
  - ndestruct C as (b & gh & Hb & Hin). ndestruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _).
    assert (NE : fst b <> fst p) by (intros E; rewrite E, Hr in Hrb; assert (rb = r) by congruence; subst; exact (NK Krb)).
    pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hr NE); lia.
  - ndestruct C as (rid & rg & v & Hrg & Krg & Hin & _).
    assert (NE : rid <> fst p) by (intros E; rewrite E, Hr in Hrg; assert (rg = r) by congruence; subst; exact (NK Krg)).
    pose proof (lr_lo_group rg Krg). destruct (DJ _ _ _ _ Hrg Hr NE); lia.
  - unfold RGOT_SSP in C. lia.
  - unfold RSSP_GUARD in C. lia.
Qed.

End HCW.


