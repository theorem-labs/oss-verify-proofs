(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk HeapIface L5Defs L5Core PmLayout PmModel PmModelFacts PgSrc PgV8 PnModel PnModelFacts.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNOF.

Definition apart (p k q m : Z) : Prop := p + k <= q \/ q + m <= p.

Lemma outside_app W1 W2 a : L5.outside W1 a -> L5.outside W2 a -> L5.outside (W1 ++ W2) a.
Proof. intros H1 H2 r Hr. apply in_app_or in Hr. destruct Hr as [Hr|Hr]; [apply H1| apply H2]; exact Hr. Qed.
Lemma outside_cons r W a : ~ L5.in_rng r a -> L5.outside W a -> L5.outside (r :: W) a.
Proof. intros H1 H2 r' [<-|Hr]; [exact H1| apply H2; exact Hr]. Qed.
Lemma outside_nil a : L5.outside [] a.
Proof. intros r []. Qed.
Lemma outside_Forall W a : Forall (fun r => ~ L5.in_rng r a) W -> L5.outside W a.
Proof. intros F r Hr. rewrite Forall_forall in F. apply F. exact Hr. Qed.

Section Upd.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable A : pm_addrs.
Variable vp : Z.
Let T3 : (word -> option byte) -> Z -> Z -> Prop := fun _ _ _ => True.
Let T4 : (word -> option byte) -> Z -> Z -> Z -> Prop := fun _ _ _ _ => True.
Variable L : heap_layout.
Variables (LBX : list (Z * Z)) (sp scr : Z) (Wx : list L5.range) (M M' : word -> option byte).
Variables (op ois lo hi : Z) (s : PNM.bpst) (src src' : PM.srcst).

Let X : list (Z * Z) := PM.src_own src ++ PNM.brest_own s.
Let W : list L5.range := PGS.W_srcG (op + PNM.OFF_SRC) ois src ++ Wx.

Hypothesis Hceil : hl_ceil L <= lo.
Hypothesis Hsp : sp <= lo.
Hypothesis Hscr : 0 <= scr.
Hypothesis Herr : hl_errno L + 4 <= lo.
Hypothesis Hlay : lo <= op /\ op + PNM.PSIZE <= hi /\ lo <= ois /\ ois + 272 <= hi /\ hi <= 2 ^ 64 /\ 0 <= lo.
Hypothesis Hdis : op + PNM.PSIZE <= ois \/ ois + 272 <= op.
Hypothesis HA : forall b, In b X -> apart (fst b) (snd b) lo (hi - lo) /\ (fst b + snd b <= hl_errno L \/ hl_errno L + 4 <= fst b)
                                   /\ 0 <= fst b /\ 0 <= snd b /\ fst b + snd b <= 2 ^ 64.
Hypothesis HN : List.NoDup (map fst X).
Hypothesis HE : forall b1 b2, In b1 X -> In b2 X -> fst b1 <> fst b2 -> apart (fst b1) (snd b1) (fst b2) (snd b2).
Hypothesis HC : Forall (fun r => (apart (fst r) (snd r) lo (hi - lo) /\ (forall b, In b (PNM.brest_own s) -> apart (fst r) (snd r) (fst b) (snd b)))
                                \/ PNM.bwin op s (fst r) (snd r)) Wx.
Hypothesis HP : L5C.hpres L (X ++ LBX) sp scr W M M'.
Hypothesis HOW : PNM.bparser_at segs A T3 T4 vp M op ois (PNM.with_srcB s src).
Hypothesis HSRC : PM.src_fields_at segs T3 M' (op + PNM.OFF_SRC) ois (ois + 16) src'.
Hypothesis HQC : PM.sr_qc src' = PM.sr_qc src.

(* [comment removed for export] *)
Lemma frame_client a : lo <= a < hi -> 0 <= a < 2 ^ 64 /\ client_addr L (X ++ LBX) sp scr a /\ ~ in_errno L a.
Proof.
  intros Ha. destruct Hlay as (H1 & H2 & H3 & H4 & H5 & H6). split; [lia|]. split.
  - right. left. split; [lia| lia].
  - unfold in_errno. lia.
Qed.
(* [comment removed for export] *)
Lemma blk_client b a : In b X -> fst b <= a < fst b + snd b -> 0 <= a < 2 ^ 64 /\ client_addr L (X ++ LBX) sp scr a /\ ~ in_errno L a.
Proof.
  intros Hin Ha. destruct (HA b Hin) as (_ & Her & H0 & H1 & H2). split; [lia|]. split.
  - left. exists b. split; [apply in_or_app; left; exact Hin| exact Ha].
  - unfold in_errno. lia.
Qed.

Lemma chunk_in : In (PM.sr_qc src, PM.CHUNK) X.
Proof. unfold X, PM.src_own. apply in_or_app. left. left. reflexivity. Qed.
Lemma rest_in b : In b (PNM.brest_own s) -> In b X.
Proof. intros H. unfold X. apply in_or_app. right. exact H. Qed.

(* [comment removed for export] *)
Lemma wsrcf_in_frame r : In r (PGS.W_srcfG (op + PNM.OFF_SRC) ois) -> lo <= fst r /\ fst r + snd r <= hi.
Proof.
  destruct Hlay as (H1 & H2 & H3 & H4 & H5 & H6). unfold PGS.W_srcfG, PNM.OFF_SRC, PNM.PSIZE in *.
  intros [<-|[<-|[<-|[]]]]; cbn [fst snd]; lia.
Qed.

(* [comment removed for export] *)
Definition named (a : Z) : Prop :=
  op <= a < op + PNM.PSIZE /\ ~ (op + 272 <= a < op + 312)
  /\ ((exists n, PNM.b_nb s = PM.VShort n) -> ~ (op + PNM.OFF_NB + 1 <= a < op + PNM.OFF_NB + 24))
  /\ ((exists n, PNM.b_tb s = PM.VShort n) -> ~ (op + PNM.OFF_TB + 1 <= a < op + PNM.OFF_TB + 24)).

Lemma named_kept a : named a -> L5C.kept L (X ++ LBX) sp scr W a.
Proof.
  intros (Ha & Hs & Hnb & Htb). destruct Hlay as (H1 & H2 & H3 & H4 & H5 & H6).
  unfold PNM.PSIZE, PNM.OFF_NB, PNM.OFF_TB in *.
  destruct (frame_client a ltac:(lia)) as (R & C & E). split; [exact R|]. split; [exact C|]. split; [exact E|].
  unfold W, PGS.W_srcG. apply outside_app; [apply outside_app|].
  - intros r Hr. pose proof Hr as Hr'. unfold PGS.W_srcfG, PNM.OFF_SRC in Hr'. unfold L5.in_rng.
    destruct Hr' as [<-|[<-|[<-|[]]]]; cbn [fst snd]; lia.
  - apply outside_cons; [|apply outside_nil]. unfold L5.in_rng. cbn [fst snd].
    destruct (HA _ chunk_in) as (Hap & _). unfold apart in Hap. cbn [fst snd] in Hap. lia.
  - apply outside_Forall. eapply Forall_impl; [|exact HC]. intros r [(Hap & _)|Hw]; unfold L5.in_rng.
    + unfold apart in Hap. lia.
    + destruct Hw as [((n & En) & W0 & W1 & W2)|[((n & En) & W0 & W1 & W2)|(B & m & Hin & W0 & W1 & W2)]].
      * specialize (Hnb (ex_intro _ n En)). unfold PNM.OFF_NB in *. lia.
      * specialize (Htb (ex_intro _ n En)). unfold PNM.OFF_TB in *. lia.
      * assert (HinX : In (B, m) X).
        { apply rest_in. unfold PNM.brest_own. apply in_or_app. right. exact Hin. }
        destruct (HA _ HinX) as (Hap & _). unfold apart in Hap. cbn [fst snd] in Hap. lia.
Qed.
Lemma named_ag a0 n : (forall a, a0 <= a < a0 + n -> named a) -> L5C.agree_on M M' a0 n.
Proof. intros HN' a Ha. apply (L5C.hpres_kept L (X ++ LBX) sp scr W M M' a HP). apply named_kept. apply HN'. exact Ha. Qed.

(* [comment removed for export] *)
Lemma stk_in : In (PNM.b_sb s, PNM.BSZ * 2 ^ PNM.b_sk s) X.
Proof. apply rest_in. unfold PNM.brest_own, PNM.bvec_own. apply in_or_app. left. left. reflexivity. Qed.
Lemma stk_kept a : PNM.b_sb s <= a < PNM.b_sb s + PNM.BSZ * 2 ^ PNM.b_sk s -> L5C.kept L (X ++ LBX) sp scr W a.
Proof.
  intros Ha. destruct (blk_client _ a stk_in Ha) as (R & C & E). split; [exact R|]. split; [exact C|]. split; [exact E|].
  destruct (HA _ stk_in) as (Hapf & _). cbn [fst snd] in Hapf. unfold apart in Hapf.
  assert (HQ : PM.sr_qc src <> PNM.b_sb s).
  { unfold X, PM.src_own, PNM.brest_own, PNM.bvec_own in HN. cbn [map app] in HN. apply NoDup_cons_iff in HN as [NI _]. intros E0. apply NI. left. symmetry. exact E0. }
  unfold W, PGS.W_srcG. apply outside_app; [apply outside_app|].
  - intros r Hr. pose proof (wsrcf_in_frame r Hr) as (F1 & F2). unfold L5.in_rng. lia.
  - apply outside_cons; [|apply outside_nil]. unfold L5.in_rng. cbn [fst snd].
    pose proof (HE _ _ chunk_in stk_in HQ) as Hap. unfold apart in Hap. cbn [fst snd] in Hap. lia.
  - apply outside_Forall. eapply Forall_impl; [|exact HC]. intros r [(Hap & Hapb)|Hw]; unfold L5.in_rng.
    + pose proof (Hapb _ (or_introl eq_refl)) as H'. unfold apart in H'. cbn [fst snd] in H'. lia.
    + destruct Hlay as (H1 & H2 & H3 & H4 & H5 & H6). unfold PNM.PSIZE in *.
      destruct Hw as [((n & En) & W0 & W1 & W2)|[((n & En) & W0 & W1 & W2)|(B & m & Hin & W0 & W1 & W2)]].
      * unfold PNM.OFF_NB in *. lia.
      * unfold PNM.OFF_TB in *. lia.
      * assert (HinX : In (B, m) X).
        { apply rest_in. unfold PNM.brest_own. apply in_or_app. right. exact Hin. }
        assert (HB : B <> PNM.b_sb s).
        { unfold X, PM.src_own, PNM.brest_own, PNM.bvec_own in HN. cbn [map app] in HN.
          apply NoDup_cons_iff in HN as [_ ND]. apply NoDup_cons_iff in ND as [NI _]. intros E0. apply NI. subst B.
          apply in_map_iff. exists (PNM.b_sb s, m). split; [reflexivity| exact Hin]. }
        pose proof (HE _ _ HinX stk_in HB) as H'. unfold apart in H'. cbn [fst snd] in H'. lia.
Qed.

(* [comment removed for export] *)
Lemma blk_dkr b : In b X -> PNMF.dkr M M' (fst b) (snd b).
Proof.
  intros Hin a Ha D. destruct (blk_client b a Hin Ha) as (R & C & E).
  exact (L5C.hpres_cdef L (X ++ LBX) sp scr W M M' a HP R C E D).
Qed.
Lemma frame_dkr : PNMF.dkr M M' op PNM.PSIZE.
Proof.
  intros a Ha D. destruct Hlay as (H1 & H2 & H3 & H4 & H5 & H6).
  destruct (frame_client a ltac:(lia)) as (R & C & E).
  exact (L5C.hpres_cdef L (X ++ LBX) sp scr W M M' a HP R C E D).
Qed.

(* [comment removed for export] *)
Theorem src_owner_upd : PNM.bparser_at segs A T3 T4 vp M' op ois (PNM.with_srcB s src').
Proof.
  destruct Hlay as (H1 & H2 & H3 & H4 & H5 & H6).
  assert (E : PNM.with_srcB s src' = PNM.with_srcB (PNM.with_srcB s src) src') by (destruct s; reflexivity).
  rewrite E. clear E.
  assert (HB : forall b n c, PNM.b_bb s = PGV8.V8Blk b n c -> In (b, c) X).
  { intros b n c Eb. apply rest_in. unfold PNM.brest_own. apply in_or_app. right. apply in_or_app. left. rewrite Eb. left. reflexivity. }
  assert (HNB : forall c n p, PNM.b_nb s = PM.VLong c n p -> In (p, c) X).
  { intros c n p Eb. apply rest_in. unfold PNM.brest_own. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. rewrite Eb. left. reflexivity. }
  assert (HTB : forall c n p, PNM.b_tb s = PM.VLong c n p -> In (p, c) X).
  { intros c n p Eb. apply rest_in. unfold PNM.brest_own. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. rewrite Eb. left. reflexivity. }
  destruct (HA _ stk_in) as (_ & _ & Hs0 & _ & Hs1). cbn [fst snd] in Hs0, Hs1.
  unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *.
  apply (PNMF.bparser_at_frame segs A vp M M' op ois (PNM.with_srcB s src) src'); cbn [PNM.with_srcB PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk].
  - lia.
  - unfold PNM.PSIZE. lia.
  - exact frame_dkr.
  - apply named_ag. intros a Ha. unfold named, PNM.PSIZE, PNM.OFF_NB, PNM.OFF_TB. split; [lia|]. split; [lia|]. split; intros _; lia.
  - apply named_ag. intros a Ha. unfold named, PNM.PSIZE, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_SRC in *. split; [lia|]. split; [lia|]. split; intros _; lia.
  - unfold PNM.OFF_SRC. exact HSRC.
  - apply named_ag. intros a Ha. unfold named, PNM.PSIZE, PNM.OFF_NB, PNM.OFF_TB. split; [lia|]. split; [lia|]. split; intros _; lia.
  - apply named_ag. intros a Ha. unfold named, PNM.PSIZE, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_BB in *. split; [lia|]. split; [lia|]. split; intros _; lia.
  - intros b n c Eb. exact (blk_dkr _ (HB b n c Eb)).
  - apply named_ag. intros a Ha. unfold named, PNM.PSIZE, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_BB in *.
    destruct (PNM.b_nb s) as [n0|c0 n0 p0] eqn:Enb; cbn [PNMF.vs_cells fst snd] in Ha.
    + split; [lia|]. split; [lia|]. split; intros _; lia.
    + split; [lia|]. split; [lia|]. split; [intros (n1 & En1); discriminate En1| intros _; lia].
  - intros c n p Eb. exact (blk_dkr _ (HNB c n p Eb)).
  - apply named_ag. intros a Ha. unfold named, PNM.PSIZE, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_BB in *.
    destruct (PNM.b_tb s) as [n0|c0 n0 p0] eqn:Etb; cbn [PNMF.vs_cells fst snd] in Ha.
    + split; [lia|]. split; [lia|]. split; intros _; lia.
    + split; [lia|]. split; [lia|]. split; [intros _; lia| intros (n1 & En1); discriminate En1].
  - intros c n p Eb. exact (blk_dkr _ (HTB c n p Eb)).
  - apply named_ag. intros a Ha. unfold named, PNM.PSIZE, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *. split; [lia|]. split; [lia|]. split; intros _; lia.
  - exact Hs0.
  - exact Hs1.
  - intros a Ha. apply (L5C.hpres_kept L (X ++ LBX) sp scr W M M' a HP). apply stk_kept. exact Ha.
  - exact HOW.
Qed.

End Upd.
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Laws.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable A : pm_addrs.
Variable vp : Z.
Let T3 : (word -> option byte) -> Z -> Z -> Prop := fun _ _ _ => True.
Let T4 : (word -> option byte) -> Z -> Z -> Z -> Prop := fun _ _ _ _ => True.
Variables (op ois lo hi : Z) (s : PNM.bpst).
Hypothesis Hlay : lo <= op /\ op + PNM.PSIZE <= hi /\ lo <= ois /\ ois + 272 <= hi /\ hi <= 2 ^ 47 /\ 4096 <= lo.
Hypothesis Hdis : op + PNM.PSIZE <= ois \/ ois + 272 <= op.
Let O := PNM.src_owner segs A T3 T4 vp op ois lo hi s.

Lemma src_owner_src M src OB : PGS.ow_at O M src OB ->
  PM.src_fields_at segs T3 M (PGS.ow_os O) (PGS.ow_ois O) (PGS.ow_ois O + 16) src /\ PM.nullis_at segs A T3 M (PGS.ow_os O + 8)
  /\ L5.defined M (PGS.ow_os O) 296.
Proof.
  intros ((_ & D & _ & _ & _ & _ & _ & NI & SRC & _) & _). cbn [O PNM.src_owner PGS.ow_os PGS.ow_ois].
  cbn [PNM.with_srcB PNM.b_src] in SRC. split; [exact SRC|]. split; [exact NI|].
  intros i Hi. unfold PNM.PSIZE, PNM.OFF_SRC in *. replace (op + 16 + i) with (op + (16 + i)) by lia. apply D. lia.
Qed.

Lemma src_owner_win M src OB p k : PGS.ow_at O M src OB -> PGS.ow_win O M src OB p k ->
  0 <= k /\ L5.defined M p k
  /\ (PGS.in_blk OB p k \/ (4096 <= p /\ p + k <= 2 ^ 47 /\ PGS.ow_lo O <= p /\ p + k <= PGS.ow_hi O /\ k < PM.CHUNK
                            /\ (p + k <= PGS.ow_os O \/ PGS.ow_os O + 296 <= p) /\ (p + k <= PGS.ow_ois O \/ PGS.ow_ois O + 272 <= p))).
Proof.
  intros ((_ & D & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB & NB & TB & _) & EOB) Hw.
  cbn [O PNM.src_owner PGS.ow_win PGS.ow_os PGS.ow_ois PGS.ow_lo PGS.ow_hi] in *.
  cbn [PNM.with_srcB PNM.b_bb PNM.b_nb PNM.b_tb] in BB, NB, TB.
  unfold PNM.bwin, PNM.sso_win, PNM.blk_win in Hw.
  destruct Hlay as (H1 & H2 & H3 & H4 & H5 & H6). unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_NB, PNM.OFF_TB in *.
  destruct Hw as [((n & En) & K0 & W1 & W2)|[((n & En) & K0 & W1 & W2)|(B & m & Hin & K0 & W1 & W2)]].
  - split; [exact K0|]. split.
    + intros i Hi. replace (p + i) with (op + (p - op + i)) by lia. apply D. lia.
    + right. unfold PM.CHUNK. repeat split; lia.
  - split; [exact K0|]. split.
    + intros i Hi. replace (p + i) with (op + (p - op + i)) by lia. apply D. lia.
    + right. unfold PM.CHUNK. repeat split; lia.
  - split; [exact K0|]. split.
    + apply in_app_or in Hin. destruct Hin as [Hin|Hin].
      * destruct (PNM.b_bb s) as [|b0 n0 c0]; cbn in Hin; [destruct Hin|]. destruct Hin as [E0|[]]. injection E0 as E1 E2. subst b0 c0.
        destruct BB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & DB & _). intros i Hi. replace (p + i) with (B + (p - B + i)) by lia. apply DB. lia.
      * apply in_app_or in Hin. destruct Hin as [Hin|Hin].
        -- destruct (PNM.b_nb s) as [n0|c0 n0 q0]; cbn in Hin; [destruct Hin|]. destruct Hin as [E0|[]]. injection E0 as E1 E2. subst q0 c0.
           destruct NB as (_ & _ & _ & _ & _ & _ & _ & _ & DB & _). intros i Hi. replace (p + i) with (B + (p - B + i)) by lia. apply DB. lia.
        -- destruct (PNM.b_tb s) as [n0|c0 n0 q0]; cbn in Hin; [destruct Hin|]. destruct Hin as [E0|[]]. injection E0 as E1 E2. subst q0 c0.
           destruct TB as (_ & _ & _ & _ & _ & _ & _ & _ & DB & _). intros i Hi. replace (p + i) with (B + (p - B + i)) by lia. apply DB. lia.
    + left. subst OB. exists B, m. split; [|lia]. unfold PNM.brest_own. apply in_or_app. right. exact Hin.
Qed.

End Laws.
(* [comment removed for export] *)
(* [comment removed for export] *)
Section BUpd.
Local Ltac lu := unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *; lia.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable A : pm_addrs.
Variable vp : Z.
Let T3 : (word -> option byte) -> Z -> Z -> Prop := fun _ _ _ => True.
Let T4 : (word -> option byte) -> Z -> Z -> Z -> Prop := fun _ _ _ _ => True.
Variable L : heap_layout.
Variables (LBX OB : list (Z * Z)) (sp scr : Z) (Wx : list L5.range) (M M' : word -> option byte).
Variables (op ois lo hi ob : Z) (s : PNM.bpst).
(* [comment removed for export] *)
Let W : list L5.range := PGS.W_srcfG (op + PNM.OFF_SRC) ois ++ [(ob, 24)] ++ Wx.

Hypothesis Hceil : hl_ceil L <= lo.
Hypothesis Hsp : sp <= lo.
Hypothesis Hscr : 0 <= scr.
Hypothesis Herr : hl_errno L + 4 <= lo.
Hypothesis Hlay : lo <= op /\ op + PNM.PSIZE <= hi /\ lo <= ois /\ ois + 272 <= hi /\ hi <= 2 ^ 64 /\ 0 <= lo.
Hypothesis Hdis : op + PNM.PSIZE <= ois \/ ois + 272 <= op.
Hypothesis Hob : ob = op + PNM.OFF_TB \/ ob = op + PNM.OFF_BB.
Hypothesis HA : forall b, In b OB -> apart (fst b) (snd b) lo (hi - lo) /\ (fst b + snd b <= hl_errno L \/ hl_errno L + 4 <= fst b)
                                    /\ 0 <= fst b /\ 0 <= snd b /\ fst b + snd b <= 2 ^ 64.
Hypothesis HC : Forall (fun r => apart (fst r) (snd r) lo (hi - lo) /\ (forall b, In b OB -> apart (fst r) (snd r) (fst b) (snd b))) Wx.
Hypothesis HP : L5C.hpres L (OB ++ LBX) sp scr W M M'.

Lemma frame_clientB a : lo <= a < hi -> 0 <= a < 2 ^ 64 /\ client_addr L (OB ++ LBX) sp scr a /\ ~ in_errno L a.
Proof.
  intros Ha. destruct Hlay as (H1 & H2 & H3 & H4 & H5 & H6). split; [lia|]. split.
  - right. left. split; [lia| lia].
  - unfold in_errno. lia.
Qed.
Lemma blk_clientB b a : In b OB -> fst b <= a < fst b + snd b -> 0 <= a < 2 ^ 64 /\ client_addr L (OB ++ LBX) sp scr a /\ ~ in_errno L a.
Proof.
  intros Hin Ha. destruct (HA b Hin) as (_ & Her & H0 & H1 & H2). split; [lia|]. split.
  - left. exists b. split; [apply in_or_app; left; exact Hin| exact Ha].
  - unfold in_errno. lia.
Qed.
(* [comment removed for export] *)
Lemma cellB_kept a : op <= a < op + PNM.PSIZE -> ~ (op + 272 <= a < op + 312) -> ~ (ob <= a < ob + 24) -> L5C.kept L (OB ++ LBX) sp scr W a.
Proof.
  intros Ha Hs Hb. destruct Hlay as (H1 & H2 & H3 & H4 & H5 & H6). unfold PNM.PSIZE in *.
  destruct (frame_clientB a ltac:(lia)) as (R & C & E). split; [exact R|]. split; [exact C|]. split; [exact E|].
  unfold W. apply outside_app; [|apply outside_app].
  - intros r Hr. pose proof Hr as Hr'. unfold PGS.W_srcfG, PNM.OFF_SRC in Hr'. unfold L5.in_rng.
    destruct Hr' as [<-|[<-|[<-|[]]]]; cbn [fst snd]; lia.
  - apply outside_cons; [|apply outside_nil]. unfold L5.in_rng. cbn [fst snd]. lia.
  - apply outside_Forall. eapply Forall_impl; [|exact HC]. intros r (Hap & _). unfold L5.in_rng. unfold apart in Hap. lia.
Qed.
Lemma cellB_ag a0 n : op <= a0 -> a0 + n <= op + PNM.PSIZE -> (a0 + n <= op + 272 \/ op + 312 <= a0) -> (a0 + n <= ob \/ ob + 24 <= a0) ->
  L5C.agree_on M M' a0 n.
Proof. intros H1 H2 H3 H4 a Ha. apply (L5C.hpres_kept L (OB ++ LBX) sp scr W M M' a HP). apply cellB_kept; lia. Qed.
Lemma blkB_kept b a : In b OB -> fst b <= a < fst b + snd b -> L5C.kept L (OB ++ LBX) sp scr W a.
Proof.
  intros Hin Ha. destruct (blk_clientB b a Hin Ha) as (R & C & E). split; [exact R|]. split; [exact C|]. split; [exact E|].
  destruct (HA _ Hin) as (Hapf & _). unfold apart in Hapf. destruct Hlay as (H1 & H2 & H3 & H4 & H5 & H6). unfold PNM.PSIZE in *.
  unfold W. apply outside_app; [|apply outside_app].
  - intros r Hr. pose proof Hr as Hr'. unfold PGS.W_srcfG, PNM.OFF_SRC in Hr'. unfold L5.in_rng.
    destruct Hr' as [<-|[<-|[<-|[]]]]; cbn [fst snd]; lia.
  - apply outside_cons; [|apply outside_nil]. unfold L5.in_rng. cbn [fst snd]. unfold PNM.OFF_TB, PNM.OFF_BB in Hob. lia.
  - apply outside_Forall. eapply Forall_impl; [|exact HC]. intros r (_ & Hapb). unfold L5.in_rng.
    pose proof (Hapb _ Hin) as H'. unfold apart in H'. lia.
Qed.
Lemma blkB_dkr b : In b OB -> PNMF.dkr M M' (fst b) (snd b).
Proof.
  intros Hin a Ha D. destruct (blk_clientB b a Hin Ha) as (R & C & E).
  exact (L5C.hpres_cdef L (OB ++ LBX) sp scr W M M' a HP R C E D).
Qed.
Lemma frameB_dkr : PNMF.dkr M M' op PNM.PSIZE.
Proof.
  intros a Ha D. destruct Hlay as (H1 & H2 & H3 & H4 & H5 & H6).
  destruct (frame_clientB a ltac:(lia)) as (R & C & E).
  exact (L5C.hpres_cdef L (OB ++ LBX) sp scr W M M' a HP R C E D).
Qed.

(* [comment removed for export] *)
Theorem txt_owner_upd (src src' : PM.srcst) (tb tb' : PM.vstr) (tg tg' : Z) :
  ob = op + PNM.OFF_TB -> OB = PNM.txt_rest_own s ->
  PGS.tw_at (PNM.txt_owner segs A T3 T4 vp op ois lo hi s) M src tb tg OB ->
  PM.src_fields_at segs T3 M' (op + PNM.OFF_SRC) ois (ois + 16) src' ->
  PM.vstr_at segs T3 M' (op + PNM.OFF_TB) tb' -> PM.tb_ok tb' tg' ->
  PGS.tw_at (PNM.txt_owner segs A T3 T4 vp op ois lo hi s) M' src' tb' tg' OB.
Proof.
  intros Eob EOB (PA & _ & _) SRC' TB' TBOK. cbn [PNM.txt_owner PGS.tw_at].
  split; [|split; [exact TBOK| exact EOB]].
  destruct Hlay as (H1 & H2 & H3 & H4 & H5 & H6).
  assert (HBB : forall b n c, PNM.b_bb s = PGV8.V8Blk b n c -> In (b, c) OB).
  { intros b n c Eb. rewrite EOB. unfold PNM.txt_rest_own. apply in_or_app. right. apply in_or_app. left. rewrite Eb. left. reflexivity. }
  assert (HNB : forall c n p, PNM.b_nb s = PM.VLong c n p -> In (p, c) OB).
  { intros c n p Eb. rewrite EOB. unfold PNM.txt_rest_own. apply in_or_app. right. apply in_or_app. right. rewrite Eb. left. reflexivity. }
  assert (HSB : In (PNM.b_sb s, PNM.BSZ * 2 ^ PNM.b_sk s) OB).
  { rewrite EOB. unfold PNM.txt_rest_own, PNM.bvec_own. apply in_or_app. left. left. reflexivity. }
  destruct (HA _ HSB) as (_ & _ & Hs0 & _ & Hs1). cbn [fst snd] in Hs0, Hs1.
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB & _).
  assert (E : PNM.with_src_tb s src' tb' tg' =
              PNM.BPST (PNM.b_more (PNM.with_src_tb s src tb tg)) (PNM.b_done (PNM.with_src_tb s src tb tg)) src' (PNM.b_bb (PNM.with_src_tb s src tb tg))
                       (PNM.b_nb (PNM.with_src_tb s src tb tg)) tb' (PNM.b_ng (PNM.with_src_tb s src tb tg)) tg' (PNM.b_bg (PNM.with_src_tb s src tb tg))
                       (PNM.b_sb (PNM.with_src_tb s src tb tg)) (PNM.b_sk (PNM.with_src_tb s src tb tg)) (PNM.b_stk (PNM.with_src_tb s src tb tg)))
    by (destruct s; reflexivity).
  rewrite E. clear E.
  cbn [PNM.with_src_tb PNM.b_bb PNM.b_nb PNM.b_sb PNM.b_sk] in BB |- *.
  unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *.
  apply (PNMF.bparser_at_frame_gen segs A vp M M' op ois (PNM.with_src_tb s src tb tg)); cbn [PNM.with_src_tb PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk].
  - lia.
  - unfold PNM.PSIZE. lia.
  - exact frameB_dkr.
  - apply cellB_ag; unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *; lia.
  - apply cellB_ag; unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *; lia.
  - exact SRC'.
  - apply cellB_ag; unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *; lia.
  - apply (PNMF.v8_at_keep segs M M'); [lu|lu| apply cellB_ag; unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *; lia| |exact BB].
    intros b n c Eb. exact (blkB_dkr _ (HBB b n c Eb)).
  - destruct (PNM.b_nb s) as [n0|c0 n0 p0]; cbn [PNMF.vs_cells fst snd]; apply cellB_ag; unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *; lia.
  - intros c n p Eb. exact (blkB_dkr _ (HNB c n p Eb)).
  - exact TB'.
  - apply cellB_ag; unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *; lia.
  - exact Hs0.
  - exact Hs1.
  - intros a Ha. apply (L5C.hpres_kept L (OB ++ LBX) sp scr W M M' a HP). exact (blkB_kept _ a HSB Ha).
  - exact PA.
Qed.

(* [comment removed for export] *)
Theorem vec_owner_upd (src src' : PM.srcst) (x x' : PGV8.v8) (g g' : Z) :
  ob = op + PNM.OFF_BB -> OB = PNM.vec_rest_own s ->
  PGV8.vw_at (PNM.vec_owner segs A T3 T4 vp op ois lo hi s) M src x g OB ->
  PM.src_fields_at segs T3 M' (op + PNM.OFF_SRC) ois (ois + 16) src' ->
  PGV8.v8_at segs T3 T4 M' (op + PNM.OFF_BB) x' -> PGV8.v8_ok x' g' ->
  PGV8.vw_at (PNM.vec_owner segs A T3 T4 vp op ois lo hi s) M' src' x' g' OB.
Proof.
  intros Eob EOB (PA & _ & _) SRC' BB' V8OK. cbn [PNM.vec_owner PGV8.vw_at].
  split; [|split; [exact V8OK| exact EOB]].
  destruct Hlay as (H1 & H2 & H3 & H4 & H5 & H6).
  assert (HNB : forall c n p, PNM.b_nb s = PM.VLong c n p -> In (p, c) OB).
  { intros c n p Eb. rewrite EOB. unfold PNM.vec_rest_own. apply in_or_app. right. apply in_or_app. left. rewrite Eb. left. reflexivity. }
  assert (HTB : forall c n p, PNM.b_tb s = PM.VLong c n p -> In (p, c) OB).
  { intros c n p Eb. rewrite EOB. unfold PNM.vec_rest_own. apply in_or_app. right. apply in_or_app. right. rewrite Eb. left. reflexivity. }
  assert (HSB : In (PNM.b_sb s, PNM.BSZ * 2 ^ PNM.b_sk s) OB).
  { rewrite EOB. unfold PNM.vec_rest_own, PNM.bvec_own. apply in_or_app. left. left. reflexivity. }
  destruct (HA _ HSB) as (_ & _ & Hs0 & _ & Hs1). cbn [fst snd] in Hs0, Hs1.
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TB & _).
  assert (E : PNM.with_src_bb s src' x' g' =
              PNM.BPST (PNM.b_more (PNM.with_src_bb s src x g)) (PNM.b_done (PNM.with_src_bb s src x g)) src' x'
                       (PNM.b_nb (PNM.with_src_bb s src x g)) (PNM.b_tb (PNM.with_src_bb s src x g)) (PNM.b_ng (PNM.with_src_bb s src x g))
                       (PNM.b_tg (PNM.with_src_bb s src x g)) g'
                       (PNM.b_sb (PNM.with_src_bb s src x g)) (PNM.b_sk (PNM.with_src_bb s src x g)) (PNM.b_stk (PNM.with_src_bb s src x g)))
    by (destruct s; reflexivity).
  rewrite E. clear E.
  cbn [PNM.with_src_bb PNM.b_tb PNM.b_nb PNM.b_sb PNM.b_sk PNM.b_tg] in TB |- *.
  unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *.
  apply (PNMF.bparser_at_frame_gen segs A vp M M' op ois (PNM.with_src_bb s src x g)); cbn [PNM.with_src_bb PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk].
  - lia.
  - unfold PNM.PSIZE. lia.
  - exact frameB_dkr.
  - apply cellB_ag; unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *; lia.
  - apply cellB_ag; unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *; lia.
  - exact SRC'.
  - apply cellB_ag; unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *; lia.
  - exact BB'.
  - destruct (PNM.b_nb s) as [n0|c0 n0 p0]; cbn [PNMF.vs_cells fst snd]; apply cellB_ag; unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *; lia.
  - intros c n p Eb. exact (blkB_dkr _ (HNB c n p Eb)).
  - apply (PNMF.vstr_at_keep segs M M'); [lu|lu| | |intros c n p Eb; exact (blkB_dkr _ (HTB c n p Eb))| exact TB].
    + destruct (PNM.b_tb s) as [n0|c0 n0 p0]; cbn [PNMF.vs_cells fst snd]; apply cellB_ag; unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *; lia.
    + apply (PNMF.dkr_sub M M' op 416); [exact frameB_dkr| lu| lu].
  - apply cellB_ag; unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *; lia.
  - exact Hs0.
  - exact Hs1.
  - intros a Ha. apply (L5C.hpres_kept L (OB ++ LBX) sp scr W M M' a HP). exact (blkB_kept _ a HSB Ha).
  - exact PA.
Qed.

End BUpd.
End PNOF.
