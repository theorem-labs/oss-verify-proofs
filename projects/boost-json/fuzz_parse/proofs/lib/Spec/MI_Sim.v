(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow
  MI_Pres1 MI_Pres2 MI_Read MI_WFree MI_WFree2 MI_WNtf2 MI_WGroup MI_Cnt MI_TF2 MI_WAMeta2 MI_WSlot MI_WSlot2 MI_WSlot3 MI_WEnframe MI_WEnframe2 MI_WMalloc.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4KInv~~~~~~07ld_live37Corelib4Init9Datatypesk54list37Corelib4Init5Logicm42eq37Corelib7Numbers7BinNumsnd1Z0aevent_post04mled79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~qc4cptrqc2evqc4aptrk54prodm43andqc6mstate79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Inv~~~~~~hh32MRk54pairnd1N35stdpp7numbers1Nhm26eq_dec35stdpp7numbers1Zhnd6eq_deck54Somek56optionm42exqc4aaddqcbm_sizeclass46Stdlib6ZArith6BinInt1Zhs22lek54boolk55falsehh34INVLhh34tbithh32x0qc1Mqc9free_tailqc5strip25stdpp9countableihdbN_countableihdbZ_countableihdeprod_countable25stdpp9decidableilebprod_eq_deck53fstm42or79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Ext~~~~~~io97ctrl_eqhh39bl_removehh33blkhh35hostshh36sstart79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec9MI_WFree2~~~~~~iv95xpendqc4UNITqc7dec_hdrqc9dec_slotsqc8free_hdrqc5lheadqc7m_availqc7m_freedqcam_last_idxqc7s_slotsqc4wr16qc3wr879OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec5STree~~~~~~jqb4SRet36Stdlib5Lists4Listjv02Inhs22lths23mul25stdpp4basekh66lookup25stdpp4gmapkic4gmapkicbgmap_lookup79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4SpecaMallocCtrl~~~~~~kkf6hdr_okqc6regionqc9s_regionsqc8s_secretqc4freekkf6followkkf4prun05cpath79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Sim~~~~~~ktb6lafterqc5cfreeqc4optrm45Falsek54consm43not37Corelib5Lists7ListDeflk73maphh35bslot79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4SpecaMI_WAMeta2~~~~~~lme5AREAS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec8MI_WSlot~~~~~~lr92GPqc4FUELqc7cmallocqc6malloc" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Set Implicit Arguments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint lafter {R} (L : mled) (t : M R) (ans : list Z) {struct t} : mled :=
  match t, ans with
  | SRet _, _ => L
  | SVis (EUndef _) _, _ => L
  | SVis e k, a :: ans' => lafter (event_post L e a) (k a) ans'
  | SVis _ _, [] => L
  end.

(* [comment removed for export] *)
Fixpoint followk {R} (t : M R) (ans : list Z) {struct t} : option (R * list Z) :=
  match t, ans with
  | SRet r, _ => Some (r, ans)
  | SVis (EUndef _) _, _ => None
  | SVis _ k, a :: ans' => followk (k a) ans'
  | SVis _ _, [] => None
  end.

Lemma ptree_follow_lafter {R} : forall (t : M R) L Post ans r,
  ptree L t Post -> follow t ans = Some r -> cpath L t (lafter L t ans) r /\ Post (lafter L t ans) r.
Proof.
  induction t as [r0|e k IH]; intros L Post ans r H Hf; cbn [ptree follow lafter] in *.
  - inversion Hf; subst. split; [constructor| exact H].
  - destruct e; try (destruct H; fail); try contradiction.
    all: destruct H as [He Hk]; destruct ans as [|a ans']; [discriminate|];
      specialize (Hk a); case_ans;
      [ destruct (IH a _ _ _ _ Hk Hf) as [Hp HP]; split; [econstructor; eauto| exact HP]
      | destruct (rejects_inv _ Hk) as (w & k' & E); rewrite E in Hf; cbn in Hf; discriminate ].
Qed.

Lemma followk_follow {R} : forall (t : M R) ans x rest, followk t ans = Some (x, rest) -> follow t ans = Some x.
Proof.
  induction t as [r0|e k IH]; intros ans x rest H; cbn [followk follow] in *.
  - inversion H. reflexivity.
  - destruct e; try discriminate; destruct ans as [|a ans']; try discriminate; eapply IH; exact H.
Qed.

Lemma follow_sbind {R S} : forall (t : M R) (k : R -> M S) ans,
  follow (sbind t k) ans = match followk t ans with Some (x, rest) => follow (k x) rest | None => None end.
Proof.
  induction t as [r0|e k0 IH]; intros k ans; cbn [sbind followk follow]; [reflexivity|].
  destruct e; destruct ans as [|a ans']; cbn [follow]; try reflexivity; apply IH.
Qed.

Lemma lafter_sbind {R S} : forall (t : M R) (k : R -> M S) L ans x rest,
  followk t ans = Some (x, rest) -> lafter L (sbind t k) ans = lafter (lafter L t ans) (k x) rest.
Proof.
  induction t as [r0|e k0 IH]; intros k L ans x rest H; cbn [sbind followk lafter] in *.
  - inversion H. reflexivity.
  - destruct e; try discriminate; destruct ans as [|a ans']; try discriminate; cbn [lafter]; apply IH; exact H.
Qed.

Lemma strel_followk {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) :
  strel RR t1 t2 -> forall ans x1 rest, followk t1 ans = Some (x1, rest) ->
  exists x2, followk t2 ans = Some (x2, rest) /\ RR x1 x2.
Proof.
  induction 1 as [r1 r2 Hr|e k1 k2 Hk IH]; intros ans x1 rest H; cbn [followk] in *.
  - inversion H. subst. eauto.
  - destruct e; try discriminate; destruct ans as [|a ans']; try discriminate; eapply IH; exact H.
Qed.

Lemma strel_lafter {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) :
  strel RR t1 t2 -> forall L ans, lafter L t1 ans = lafter L t2 ans.
Proof.
  induction 1 as [r1 r2 Hr|e k1 k2 Hk IH]; intros L ans; cbn [lafter]; [reflexivity|].
  destruct e; destruct ans; try reflexivity; apply IH.
Qed.

Lemma strel_follow_some {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) ans r1 :
  strel RR t1 t2 -> follow t1 ans = Some r1 -> exists r2, follow t2 ans = Some r2 /\ RR r1 r2.
Proof.
  intros H Hf. pose proof (strel_follow H ans) as F. rewrite Hf in F.
  destruct (follow t2 ans) as [r2|]; [exists r2; auto| destruct F].
Qed.

Lemma steq_follow {R} (t1 t2 : M R) ans : steq t1 t2 -> follow t1 ans = follow t2 ans.
Proof.
  intros H. apply strel_eq_steq in H. pose proof (strel_follow H ans) as F.
  destruct (follow t1 ans), (follow t2 ans); cbn in F; try reflexivity; [congruence| destruct F| destruct F].
Qed.

Lemma ptree_followk {R} (t : M R) L Post ans x rest :
  ptree L t Post -> followk t ans = Some (x, rest) -> Post (lafter L t ans) x.
Proof. intros HP Hf. exact (proj2 (ptree_follow_lafter t L Post ans HP (followk_follow _ _ Hf))). Qed.

(* [comment removed for export] *)
Lemma event_post_live : ltac2:(zQ "80!jc!ld!n8!p6!pa!q6!ua!v1>1L$5>1e$7>1z$3@3$2@1$1$6@1$0@3$4^3^2^1@1$0^3").
Proof. intros L e z.
  destruct e as [rq|a len prot flags|a len|a len prot|p c h|w]; cbn; try reflexivity.
  - destruct (rq =? 0); [reflexivity|]. destruct (z =? rq); [| reflexivity]. destruct (ld_brk L); try reflexivity; destruct (ld_brkreg L) as [[b l]|]; reflexivity.
  - destruct (Z.land flags MAP_FIXED =? 0); [| reflexivity]. destruct (is_err z); [reflexivity|]. destruct (prot =? PROT_NONE); reflexivity.
  - destruct ((z =? 0) || (z =? TWO64 - ENOSYS)); reflexivity.
Qed.

Lemma cpath_live {R} L (t : M R) L' r : cpath L t L' r -> ld_live L' = ld_live L.
Proof. induction 1; [reflexivity|]. rewrite IHcpath. apply event_post_live. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Unset Implicit Arguments.

Section SIM.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Hypothesis Hpans : ltac2:(zQ "50!p6!hg4!v6!hta!kg9>1o?1O>1p$2>1c$0>1h$0@2$1@2$3Z@4?4pans^4^3^2^1@2$4@4?4pans^4^3^2^1+hg0").
Local Notation PRUN := (prun pans pupd).

Lemma prun_ret {R} o (x : R) : PRUN o (SRet x) = SRet (o, x).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma free_prefix : ltac2:(zQ "jb0!p6!v6!vd!hg4!hga!n8!hl1!ua!hl7!hle!hn3!hoe!hp8!hpf!hq8!hqd!hr4!hta!hu0!hu7!ld!huf!hv7!hvf!ig5!ig9!ih5!iie!ijd!ikc!imf!ine!io4!q6!is7!it2!itf!iu6!iuf!jja!jk3!jka!jl4!v1!jm0!jmb!jn3!jnd!jo7!jp4!jpe!jq5!ju8!kg3!kg9!kgf!ki2!kj8!kk0>2st$4>1L$i1>2BL@1$h4$i4>2LS>0$id@1$h4$1>1c$7>3off$0>1n$0>0@5$h5$h7^7^6^5^4>0@3$j5@2$2@2$2$7$0$0@4$8@2$2$7$0$0@4$8$7$0^4^3^2^6@2$e$1\1m$1@2$e$1\2bm$1@2$e$0\1i$0=1p$1@2$f^8@2$j7$i8^7=3st1$4@3$j2@2$f^1-2Z@3$j3@2$f^1-3+vf^d@2$3@3$5@1$h8@1$d@2$2@2$2$4$1$0@2$ic^e^2@4$j4$ib$0@1$d@2$2@2$2$4$1$0@2$c@2$2@2$2$4$1$0@4$8@2$2$4$1$0@4$8$4$1^1^5^3@2$3@2$i2^e^1@2$3@3$5$4@1$ha^1@1$ha^e@2$3@3$5@1$d@2$2$1$0@6$j8$7@2$2$1$0@4$j9$1@4$he$9$a$0$b@6$hd$9$a$hb$0$b$hc@2$2$1$0@4$ja$1@4$he$9$a$0$b@6$hd$9$a$hb$0$b$hc@2$2$1$0^a@1$j1^e@2$c@2$2$1$0@4$8$1$0^5^3@2$3@5$h5@2$i7$h7@2$c$7^a^1^d@2$i3^a^c^b@2$3@3$i5^1^4^5@2$3@2$3@2$h1Z^3@2$h1^3@1$j0@2$6^1^5@2$3@3$5$7^a@4$8$9$0@3$hf$9$0^4@2$i6@2$6^1^5^3@2$3@3$5$h2@2$h6@1$ie@2$6^1^5^3$h3@2$3@3$5$h2@2$h6@1$if@2$6^1^5^3$h3@2$3@2$i0@2$3@2$h1Z@1$h0@2$6^1^5@2$j6@1$h0@2$6^1^5+j0@3$5$0@1$h0@2$6^1^5+jf@3$5@1$h8$4@4$h9@1$i9$4^1^5^3@4$h9@1$ia$4^1^5^3").
Proof. intros st L BL LS c off n.
  intros INV Hk.
  destruct (block_facts x0 st L BL LS INV c off n Hk) as (m & bm & i & ai & a & ar & ka & BF).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  exists m, bm, i. cbn zeta.
  set (p := aadd c (UNIT * off)).
  set (st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st)).
  pose proof (free_hdr_eq st c off n m bm i ai a ar ka BF) as FH. fold p in FH. fold st1 in FH.
  assert (CE1 : ctrl_eq st st1) by (eapply ctrl_eq_trans; [apply ctrl_eq_wr8| apply ctrl_eq_wr16]).
  assert (TK1 : s_tick st1 = s_tick st) by reflexivity.
  pose proof (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) as Hs. pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as Ec.
  pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as Hm. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi.
  assert (STR1 : strip st1 = strip st).
  { destruct CE1 as [C1 C2 C3 C4 C5 C6 C7 C8 C9]. unfold strip. rewrite C1, C2, C3, C4, C5, C6, C7, C8, C9. reflexivity. }
  assert (INV1 : INVL (xpend x0 (Some c)) st1 L (bl_remove c BL) LS).
  { change c with (bslot ((c, off), n)) at 1 2.
    apply (INVL_remove_block x0 st st1 L BL LS ((c, off), n) INV Hk eq_refl CE1 TK1).
    - intros m' i' Hs' q Hq. cbn [bslot fst snd] in Hs', Hq. rewrite Hs in Hs'. inversion Hs'. subst m' i'.
      subst st1. unfold wr16. rewrite !cell_read_wr8_other; [reflexivity| | |];
        intros ->; apply Hq; unfold inT; subst p; rewrite Ec; cbn [fst snd aadd]; rewrite sstart_succ;
        pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [SG _]; pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF); pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF);
        pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF); unfold UNIT, IB in *; lia.
    - subst st1. unfold wr16. set (P := fun rid : N => exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup).
      change (forall rid sh, s_shadow (wr8 (aadd (aadd p (-2)) 1) (Z.shiftr 0 8) (wr8 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st))) !! rid = Some sh -> P rid).
      assert (HP : P (fst bm)) by (destruct (ig_region _ _ _ IG _ _ Hm) as (r & Hr & Hkr); exists r; auto).
      assert (Efst : forall d1 d2, fst (aadd (aadd p d1) d2) = fst bm) by (intros; subst p; rewrite Ec; reflexivity).
      assert (Efst1 : forall d1, fst (aadd p d1) = fst bm) by (intros; subst p; rewrite Ec; reflexivity).
      apply (wr8_dom _ _ _ P); [apply (wr8_dom _ _ _ P); [apply (wr8_dom _ _ _ P); [exact (ish_dom _ _ ISH)|]|]|]; rewrite ?Efst, ?Efst1; exact HP.
    - subst st1. unfold wr16. apply wr8_tks; [cbn; lia|]. apply wr8_tks; [cbn; lia|]. apply wr8_tks; [cbn; lia|]. exact (ish_ticks _ _ ISH). }
  assert (Hm1 : hosts st1 bm m). { exists ai. rewrite (ce_groups _ _ CE1). exact Hm. }
  assert (MR1 : forall x, MR st1 x = MR st x) by (intros; apply MR_ext; exact (ce_metas _ _ CE1)).
  assert (SC : 0 <= m_sizeclass (MR st1 m) < 48 \/ m_sizeclass (MR st1 m) = 63).
  { rewrite MR1. destruct (g_sc _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hm)) as [[? ?]|[? ?]]; lia. }
  split; [exact FH|]. split; [exact CE1|]. split; [exact STR1|]. split; [exact Hs|]. split; [exact INV1|]. split; [exact Hm1|].
  rewrite !MR1. split; [exact Hi|]. split; [exact Ec|].
  split; [exact (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF)|]. split; [exact (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF)|]. split; [rewrite <- MR1; exact SC|].
  unfold free_tail.
  rewrite (ntf_slots_agree mstate FUEL (xpend x0 (Some c)) st1 L (bl_remove c BL) LS m bm i _ (ret st1) INV1 Hm1); [reflexivity| | | | | |].
  - rewrite MR1. exact Hi.
  - cbn. rewrite MR1, Ec. reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold FUEL. lia.
  - unfold FUEL. lia.
Qed.

(* [comment removed for export] *)
Theorem INVL_hdr_ok : ltac2:(zQ "h10!p6!ua!vd!ld!hl7!q6!huf!itf!hvf!jk3!hqd!v6!jmb!hga!kp1!kg3!kgf>2st$d>1L$5>2BL@1$3$7>2LS>0$c@1$3$b>1c$1>3off$0>1n$0>0@5$6$8^7^6^5^4>0@3$f@2$2@2$2$1$0$0@4$4@2$2$1$0$0@4$4$1$0^4^3^2^6@6$e?1O?4pans?4pupd^9@2$a^5@2$h0$9^4^5").
Proof. intros st L BL LS c off n.
  intros INV Hk. destruct (free_prefix st L BL LS c off n INV Hk) as (m & bm & i & FH & CE1 & STR1 & Hs & INV1 & Hm1 & Hi & Ec & NA & NF & SC & AGREE).
  cbn zeta in FH, AGREE, STR1.
  eexists _, m, i. split; [| split; [exact STR1| split; [exact Hs|]]].
  - intros o. rewrite FH. reflexivity.
  - intros o. rewrite AGREE, <- STR1. apply free_tail_slots_control.
Qed.

(* [comment removed for export] *)
Theorem free_leaf_facts : ltac2:(zQ "i00!kpb!p6!hle!hga!vd!hp8!n8!ua!iie!hn3!ld!hpf!hl7!v6!kq4!kr0!ki2!kj8!kk0!hg4!q6!huf!itf!hvf!jk3!hqd!krb!jmb!ks2!ksc!kg3!kgf>2st$3>1L$h4>2BL@1$a$h6>2LS>0$hb@1$a$d>1c$7>3off$1>1n$1>1o?1O>3ans@1$a$1>2o'?1O>3st'$3>0@5$h5$h7^b^a^9^8>0@3$he@2$4@2$4$7$1$1@4$c@2$4$7$1$1@4$c$7$1^8^7^6^a>0@3$6@1$b@2$4?1O$3@3$hc@2$4?1O$3@6$hd?1O?4pans?4pupd$3^6@2$ha^d@2$5$d@2$h9^9@2$hf$h8^8^5@2$5@2$4?1O$3@4$c?1O$3^4^3@2$h3>3rid$2>1r$0>0@3$6@1$b$0@6$h0$2$0@4$h1$2$9$8$0@4$h2$2$9$8$0^2@1$e^6@2$5$0^1@3$6@1$b$0@6$h0$2$0@4$h1$2$9$8$0@4$h2$2$9$8$0^3@1$e^h1@2$5$0^2@3$6$1@1$f^4@1$f^e").
Proof. intros st L BL LS c off n o ans o' st'.
  intros INV Hk Hf. destruct (free_prefix st L BL LS c off n INV Hk) as (m & bm & i & FH & CE1 & STR1 & Hs & INV1 & Hm1 & Hi & Ec & NA & NF & SC & AGREE).
  cbn zeta in *.
  set (st1 := wr16 (aadd (aadd c (UNIT * off)) (-2)) 0 (wr8 (aadd (aadd c (UNIT * off)) (-3)) 255 st)) in *.
  unfold free in Hf. rewrite FH in Hf. cbn [sbind] in Hf. unfold free_tail in Hf.
  rewrite (guard_true 60) in Hf by (unfold testbit; rewrite Z.lor_spec; fold (MR st1 m); unfold tbit in NA, NF; rewrite NA, NF; reflexivity).
  fold (MR st1 m) in Hf.
  pose proof (ce_regions _ _ CE1) as RG1. pose proof (ce_secret _ _ CE1) as SE1.
  destruct (negb ((m_freed (MR st1 m) =? 0) || (Z.lor (m_freed (MR st1 m)) (m_avail (MR st1 m)) + bit i =? mask_upto (m_last_idx (MR st1 m))))).
  - rewrite prun_ret in Hf. cbn [follow] in Hf. inversion Hf. subst st'. split; [intros rid r H; rewrite <- RG1; exact H| rewrite <- SE1; reflexivity].
  - destruct (ntf_spec2 mstate FUEL dec_hdr dec_hdr (dec_hdr_ok _) (dec_hdr_ok _) (xpend x0 (Some c)) st1 L (bl_remove c BL) LS m bm i
                (fun st2 mi => match mi with
                               | Some (base, len) => if negb (len =? 0)
                                   then SVis (EMunmap (conc st2 base) len) (fun ru => if munmap_answer_ok ru then ret (drop_region (fst base) st2) else bad_answer (ret st1))
                                   else ret st2
                               | None => ret st2 end) (ret st1) INV1 Hm1 Hi ltac:(cbn; rewrite Ec; reflexivity) eq_refl eq_refl ltac:(unfold FUEL; lia) ltac:(unfold FUEL; lia))
      as (st2 & mi & LS2 & EQ & _ & [RG2 SE2] & _).
    rewrite EQ in Hf.
    assert (K2 : (forall rid r, s_regions st2 !! rid = Some r -> s_regions st !! rid = Some r) /\ s_secret st2 = s_secret st).
    { split; [intros rid r H; rewrite <- RG1, <- RG2; exact H| rewrite <- SE1, <- SE2; reflexivity]. }
    destruct mi as [[base len]|].
    + destruct (negb (len =? 0)).
      * unfold prun in Hf. rewrite (eruns_vis_keep) in Hf by reflexivity. destruct ans as [|a ans']; [cbn [follow] in Hf; discriminate Hf|]. cbn [follow] in Hf.
        destruct (munmap_answer_ok a).
        -- change (eruns (psel pans) pupd (pupd o (EMunmap (conc st2 base) len) a) (ret (drop_region (fst base) st2))) with
             (PRUN (pupd o (EMunmap (conc st2 base) len) a) (SRet (drop_region (fst base) st2))) in Hf.
           rewrite prun_ret in Hf. cbn [follow] in Hf. inversion Hf. subst st'.
           split; [| exact (proj2 K2)]. intros rid r H. unfold drop_region in H. cbn in H.
           destruct (N.eq_dec rid (fst base)) as [->|NE]; [rewrite lookup_delete_eq in H; discriminate H|]. rewrite lookup_delete_ne in H by congruence. apply (proj1 K2). exact H.
        -- unfold bad_answer in Hf. rewrite eruns_vis_keep in Hf by reflexivity. cbn [follow] in Hf. discriminate Hf.
      * rewrite prun_ret in Hf. cbn [follow] in Hf. inversion Hf. subst st'. exact K2.
    + rewrite prun_ret in Hf. cbn [follow] in Hf. inversion Hf. subst st'. exact K2.
Qed.

(* [comment removed for export] *)
Theorem free_sim : ltac2:(zQ "hf0!hga!p6!ld!vd!ua!hp8!v6!hl7!hg4!n8!jmb!ih5!hpf!jc!q6!huf!hvf!ks2!hq8!kt4!it2!itf!lh9!ig5!jk3!hqd!li3!krb!ksc!kg3!kgf>2st$0>1L$e>2BL@1$2$h5>2LS>0$a@1$2$6>1c$4>3off$1>1n$1>1o?1O>3ans@1$2$1>2o'?1O>3st'$0>0@5$f$h0^b^a^9^8>0@3$hd@2$3@2$3$4$1$1@4$7@2$3$4$1$1@4$7$4$1^8^7^6^a>0@3$9@1$c@2$3?1O$0@3$h1@2$3?1O$0@6$hc?1O?4pans?4pupd$0^6@2$hb^d@2$5$6@2$h9^9@2$he$h8^8^5@2$5@2$3?1O$0@4$7?1O$0^4^3=1t@1$h7$0@2$ha@1$b^e@2$5$4^a=2L'$e@4$h6$0^e^1^7@2$8@3$9@1$c$0@3$h1$0^2^8@2$5$0@1$b^6@2$8@5$h3$0^f^2^1@1$b^6@2$8@3$9@1$2$4@1$d^1@1$d^f@2$h2>0$a@1$2$6\3LS'>0$a@1$2$6@5$f$h0^7^2@2$h4^d^f^1").
Proof. intros st L BL LS c off n o ans o' st'.
  intros INV Hk Hf. cbn zeta.
  pose proof (free_control pans pupd st (aadd c (UNIT * off)) c o (INVL_hdr_ok st L BL LS c off n INV Hk)) as REL.
  pose proof (ftree_prun pans pupd Hpans (free st (Some (aadd c (UNIT * off)))) L _ o (free_INVL_closed st L BL LS c off n INV Hk)) as PT.
  destruct (strel_follow_some ans REL Hf) as (cs' & Hf2 & FR). unfold FREL in FR. cbn in FR. subst cs'.
  split; [exact Hf2|].
  pose proof (ptree_strel REL L _ (fun _ _ => True) ltac:(intros; exact I) PT) as PT2.
  destruct (ptree_follow_lafter _ L _ ans PT2 Hf2) as [CP _].
  split; [exact CP|]. split; [exact (cpath_live CP)|].
  destruct (ptree_follow_lafter _ L _ ans PT Hf) as [_ POST]. cbn in POST.
  rewrite <- (strel_lafter REL L ans). exact POST.
Qed.

(* [comment removed for export] *)
Theorem malloc_sim : ltac2:(zQ "i80!ua!hpf!vd!hga!hg4!p6!ld!v6!lib!hl7!jmb!n8!hq8!huf!hvf!ih5!hta!hp8!lj2!jc!q6!itf!ks2!lja!lk1!lle!kt4!lm5!lh9!lr0!lv9!lvf!ig5!jk3!hqd!mg6!mh0!ksc!kg3!kgf>2st$3>1L$h4>2BL@1$6$h5>2LS>0$a@1$6$7>1n$5>1o?1O>3ans@1$6$5>2o'?1O>3st'$3>1r$8>0@5$d$e^a^9^8^7>0@2$h0Z^7>0@3$b@1$1@2$2?1O@2$2$3$8@3$h6@2$2?1O@2$2$3$8@6$i5?1O?4pans?4pupd@2$2$3$8^7@2$i4^c^8^6@2$h1@2$2?1O@2$2$3$8@4$9?1O@2$2$3$8^5@4$9$3$8^4^3=1t@1$i0@2$2$3@1$1$0@2$i3@1$f^d^9=2L'$h4@4$hc@2$2$3@1$1$0^d^1^8@2$c@1$1$0\2rc@1$1$0@2$4@3$b@1$1@2$2$3@1$1$0@3$h6@2$2$3@1$1$0^3^a@2$h1@2$2$3@1$1$0@4$9$3@1$1$0@1$f^8^1@2$4@5$ha@2$2$3@1$1$0^f^3^2@4$9$3@1$1$0@1$f^8^1@2$4@3$b@1$6$0@1$h3^2@1$h3^f@2$4@2$he^h0^8@2$4@4$hd$hf^e^h0^8M1\1r@1$1$7P^7\2pf$7M1\2rc@1$1$0P^2\1c$0@2$c$5\3off$5@2$c>0$a@1$6$7\3LS'>0$a@1$6$7@2$4@3$b$7^4@2$i2^3@2$i7$i1^2@2$4@2$4@2$h0Z^2@2$h0^2+vf@2$4@5$d$e^c^6@3$h7@2$2@2$2$0$5$5@4$9@2$2$0$5$5@4$9$0$5^3^2^h0^h2^1@1$h8@3$i6$0^3@4$h9$h5$0$hb^h2$h2M1\2rc@1$1$0P^1\1c$0$h2@2$c>0$a@1$6$7\3LS'>0$a@1$6$7@5$d$e^9^3^f^1").
Proof. intros st L BL LS n o ans o' st' r.
  intros INV Hn Hf. cbn zeta.
  set (st0 := set_tick (N.succ (s_tick st)) st).
  assert (INV0 : INVL x0 st0 L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV]).
  assert (TF0' : TF0 st0) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| cbn; lia]).
  set (K := fun x : mstate * option (aptr * Z) => let '(st1, r) := x in
        match r with
        | None => ret (st1, @None aptr)
        | Some (g, idx) => enframe_full st1 g idx n (c_mmap_counter (ctx st1)) (fun st2 p => ret (havoc p n st2, Some p))
        end).
  assert (E1 : steq (PRUN o (malloc st n)) (sbind (PRUN o (malloc_core full_lay st0 n)) (fun x => PRUN (fst x) (K (snd x))))).
  { unfold malloc, prun. apply eruns_sbind. }
  rewrite (steq_follow ans E1) in Hf. rewrite follow_sbind in Hf.
  destruct (followk (PRUN o (malloc_core full_lay st0 n)) ans) as [[[o1 [st1 rg]] rest]|] eqn:FK; [| discriminate].
  (* [comment removed for export] *)
  pose proof (ftree_prun pans pupd Hpans (malloc_core full_lay st0 n) L _ o (malloc_core_ft st0 L BL LS n INV0 TF0' Hn)) as PTC.
  pose proof (ptree_followk _ L _ ans PTC FK) as CP. cbn [snd fst] in CP.
  set (L1 := lafter L (PRUN o (malloc_core full_lay st0 n)) ans) in *.
  destruct CP as (LIVE1 & GP1 & AR1 & CP).
  assert (AR0 : AREAS FUEL BL st st1) by (eapply AREAS_trans; [apply AREAS_eq; reflexivity| exact AR1]).
  (* [comment removed for export] *)
  pose proof (malloc_core_ctrl pans pupd n o st0 (strip st) ltac:(unfold st0; rewrite strip_set_tick; reflexivity)) as RELC.
  destruct (strel_followk RELC ans FK) as ([cst1 rg'] & FK2 & [CR1 CR2]). cbn in CR1, CR2. subst rg'.
  assert (FT : follow (cmalloc (strip st) n) ans
               = Some (strip cst1, match rg with Some (g, idx) => Some (slot_of cst1 g idx) | None => None end)).
  { unfold cmalloc. rewrite follow_sbind, FK2. reflexivity. }
  assert (LT : lafter L (cmalloc (strip st) n) ans = L1).
  { unfold cmalloc. rewrite (lafter_sbind _ _ L ans FK2). cbn [lafter]. unfold L1. symmetry. apply (strel_lafter RELC). }
  rewrite LT.
  (* [comment removed for export] *)
  assert (PT2 : ptree L (cmalloc (strip st) n) (fun _ _ => True)).
  { eapply (ptree_strel (malloc_control pans pupd Hpans st n o)); [intros; exact I|].
    eapply ptree_mono; [intros; exact I|]. exact (ftree_prun pans pupd Hpans (malloc st n) L _ o (malloc_INVL st L BL LS n INV Hn)). }
  assert (SS1 : strip cst1 = strip st1) by (rewrite <- CR1; apply strip_strip).
  assert (GP0 : GP st st1) by (eapply GP_trans; [apply GP_eq; reflexivity| exact GP1]).
  destruct rg as [[g idx]|].
  - destruct CP as (LS1 & bg & Hg & Hidx & INV1 & FIT & TF1 & RES32 & BIG).
    set (c0 := (fst bg, sstart (MR st1 g) idx)) in *.
    assert (Ec0 : slot_of cst1 g idx = c0).
    { rewrite <- CR1, slot_of_strip. unfold slot_of. exact (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV1))) _ _ idx Hg). }
    rewrite Ec0 in FT.
    (* [comment removed for export] *)
    pose proof (enframe_ft (xpend x0 (Some c0)) st1 L1 BL LS1 g bg idx n INV1 Hg Hidx eq_refl Hn FIT TF1 RES32 BIG (c_mmap_counter (ctx st1))
      (fun _ res => exists off, 0 <= off <= 255 /\ snd res = Some (aadd c0 (UNIT * off))
                      /\ INVL x0 (fst res) L1 (((c0, off), n) :: BL) LS1 /\ strip (fst res) = strip st1 /\ GP st1 (fst res))) as EF.
    cbn [fst snd] in EF.
    specialize (EF ltac:(intros off st2 Ho Hf2 INV2 CE TK; exists off; split; [exact Ho|]; split; [reflexivity|]; split; [exact INV2|];
                         split; [destruct CE as [C1 C2 C3 C4 C5 C6 C7 C8 C9]; unfold strip; rewrite C1, C2, C3, C4, C5, C6, C7, C8, C9; reflexivity| apply GP_eq; [exact (ce_regions _ _ CE)| exact (ce_secret _ _ CE)]])).
    pose proof (ftree_prun pans pupd Hpans _ L1 _ o1 EF) as PTE.
    cbn [K fst snd] in Hf.
    destruct (ptree_follow_lafter _ L1 _ rest PTE Hf) as [_ (off & Ho & Er & INV2 & SS2 & GP2)]. cbn [fst snd] in Er, INV2, SS2, GP2. subst r.
    exists (Some c0). split; [rewrite FT, SS1, SS2; reflexivity|].
    split; [rewrite <- LT; pose proof (ptree_follow_lafter _ L _ ans PT2 ltac:(rewrite FT, SS1; reflexivity)) as [C _]; rewrite SS2; exact C|].
    split; [exact LIVE1|]. split; [exact (GP_trans _ _ _ GP0 GP2)|].
    split; [apply (AREAS_eq_r _ _ _ _ _ AR0); apply (f_equal s_areas) in SS2; rewrite !s_areas_strip in SS2; exact SS2|].
    exists off, LS1. split; [reflexivity|]. split; [exact Ho|]. split; [exact INV2|].
    pose proof (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV2))))))) as ND. cbn [map bslot fst] in ND.
    apply NoDup_cons in ND as [NI _]. intros Hin. apply NI. apply list_elem_of_In. exact Hin.
  - destruct CP as (LS1 & INV1). cbn [K fst snd] in Hf. rewrite prun_ret in Hf. cbn [follow] in Hf. inversion Hf. subst o' st' r.
    exists None. split; [rewrite FT, SS1; reflexivity|].
    split; [rewrite <- LT; pose proof (ptree_follow_lafter _ L _ ans PT2 ltac:(rewrite FT, SS1; reflexivity)) as [C _]; exact C|].
    split; [exact LIVE1|]. split; [exact GP0|]. split; [exact AR0|]. exists LS1. exact INV1.
Qed.
End SIM.
(* [comment removed for export] *)
