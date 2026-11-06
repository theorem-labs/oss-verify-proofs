(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import PropExec FastWord FastWordSem ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxLazy AxLin AxVal AxMem AxMemC AxZZ AxState AxStep AxFetch AxEntryRel AxSys AxOcc AxJoin AxJoinSound AxRun.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.

Section RunSound.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIM : Z.
Variable H : htable.
Variable MR : valuation -> amodel -> Model -> Prop.
Hypothesis MR_mat : forall ρ am m pages, MR ρ am m -> MR ρ am (with_vm_backing (m_vm_lazy m) pages m).
Hypothesis Hlow : segs_low segs.
Variable KT : valuation -> list byte -> TSet.
Variable sys : astate amodel -> option (list (astate amodel)).
Variable sum : Z -> astate amodel -> option (list (astate amodel)).

Notation AST := (astate amodel).
Notation RR ρ := (R segs amodel (MR ρ) LIM ρ).
Notation Snd := (Sound segs cfg LIM MR KT).

Hypothesis H_sys : forall (A : AST) (l : list AST), sys A = Some l -> (forall B, In B l -> Snd B) ->
  forall ρ c, RR ρ A c -> (exists w, fetch_word segs (ms_pc_val (cfg_ms c)) = Some w /\ is_ecall w = true) ->
  forall o, pieces_val ρ (am_out (a_model A)) o -> realizes_cfg segs cfg c (KT ρ o).
Hypothesis H_join : forall A B J : AST, ajoin segs A B = Some J -> Snd J -> Snd A /\ Snd B.
Hypothesis H_split : forall (A : AST) f cuts, split_ok A f cuts = true -> (forall B, In B (split_children A f cuts) -> Snd B) -> Snd A.
Hypothesis H_fresh : forall (A : AST) v h k, fresh_ok A v h k = true -> Snd (fresh_child A v h k) -> Snd A.
Hypothesis H_floor : forall (A B : AST) r k, floor_child A r k = Some B -> Snd B -> Snd A.
Hypothesis H_split_reg : forall (A : AST) r f cuts, (r <? 32)%uint63 = true -> xform (a_facts A) (canon_v (a_facts A) (aget (a_regs A) r)) = Some f ->
  split_ok A f cuts = true -> (forall B, In B (split_children_reg A r f cuts) -> Snd B) -> Snd A.
Hypothesis H_sum : forall k (A : AST) l, sum k A = Some l -> (forall B, In B l -> Snd B) -> Snd A.
Hypothesis H_join_nm : forall A B J : AST, a_mem B = a_mem A -> a_model B = a_model A -> ajoin_nm A B = Some J -> Snd J -> Snd A /\ Snd B.
Hypothesis H_align : forall (A : AST) r k l, align_children A r k = Some l -> (forall B, In B l -> Snd B) -> Snd A.

Definition items_sound (l : list item) : Prop := forall it, In it l -> Snd (it_st it).

Definition rs_sound (rs : rstate) : Prop :=
  items_sound (rs_work rs) /\ items_sound (rs_parked rs) /\ (forall B, In B (rs_final rs) -> Snd B).

Lemma step_next_sound (ic ic' : itrie icent) (A A' : AST) :
  ICok segs ic -> astep segs amodel LIM ic A = (ic', ANext A') -> Snd A' -> Snd A.
Proof.
  intros Hic Hst HS ρ c HR o Ho.
  destruct (astep_next_node segs cfg amodel MR LIM MR_mat Hlow ic ic' A A' ρ c Hic HR Hst) as [c' [Hnode HR']].
  apply (rzc_silent1 segs cfg c c' _ Hnode). apply (HS ρ c' HR' o).
  destruct (astep_cases segs amodel LIM ic A ic' _ Hst) as [[w [i [d [_ Er]]]]|[[w [_ Er]]|[_ [Er _]]]]; try discriminate.
  pose proof (astep_d_model segs amodel LIM A d) as Hm. destruct (astep_d segs amodel LIM A d); try discriminate.
  injection Er as <-. rewrite Hm. exact Ho.
Qed.

Lemma step_fork_sound (ic ic' : itrie icent) (A : AST) (l : list AST) :
  ICok segs ic -> astep segs amodel LIM ic A = (ic', AFork l) -> (forall B, In B l -> Snd B) -> Snd A.
Proof.
  intros Hic Hst HS ρ c HR o Ho.
  destruct (astep_fork_node segs cfg amodel MR LIM MR_mat ic ic' A l ρ c Hic HR Hst) as [c' [Hnode [A' [HIn HR']]]].
  apply (rzc_silent1 segs cfg c c' _ Hnode). apply (HS A' HIn ρ c' HR' o).
  destruct (astep_cases segs amodel LIM ic A ic' _ Hst) as [[w [i [d [_ Er]]]]|[[w [_ Er]]|[_ [Er _]]]]; try discriminate.
  pose proof (astep_d_model segs amodel LIM A d) as Hm. destruct (astep_d segs amodel LIM A d); try discriminate.
  injection Er as <-. rewrite (Hm A' HIn). exact Ho.
Qed.

Lemma step_ecall_sound (ic ic' : itrie icent) (A A' : AST) (l : list AST) :
  ICok segs ic -> astep segs amodel LIM ic A = (ic', AEcall A') -> sys A = Some l -> (forall B, In B l -> Snd B) -> Snd A.
Proof.
  intros Hic Hst Hsys HS ρ c HR o Ho.
  destruct (astep_ecall_inv segs amodel MR LIM ic ic' A A' ρ c Hic HR Hst) as [_ Hw].
  exact (H_sys A l Hsys HS ρ c HR Hw o Ho).
Qed.

Lemma park_sound (it : item) : forall l, items_sound (park segs it l) -> items_sound l /\ Snd (it_st it).
Proof.
  induction l as [|p r IH]; intros HS; cbn [park] in HS.
  - split; [intros x []|]. apply HS. left. reflexivity.
  - destruct (Nat.eqb (it_n p) (it_n it) &&& ints_eqb (it_dj p) (it_dj it)).
    + destruct (ajoin segs (it_st p) (it_st it)) as [J|] eqn:EJ.
      * destruct (H_join _ _ J EJ (HS (IT (it_n p) (it_dj p) J) (or_introl eq_refl))) as [S1 S2].
        split; [|exact S2]. intros x [<-|Hx]; [exact S1 | apply HS; right; exact Hx].
      * destruct (IH (fun x Hx => HS x (or_intror Hx))) as [I1 I2]. split; [|exact I2].
        intros x [<-|Hx]; [apply HS; left; reflexivity | exact (I1 x Hx)].
    + destruct (IH (fun x Hx => HS x (or_intror Hx))) as [I1 I2]. split; [|exact I2].
      intros x [<-|Hx]; [apply HS; left; reflexivity | exact (I1 x Hx)].
Qed.

Lemma push_sound (n : nat) (dj : list int) (l : list AST) (w : list item) :
  items_sound (push n dj l w) -> (forall B, In B l -> Snd B) /\ items_sound w.
Proof.
  unfold push. intros HS. split.
  - intros B HB. apply (HS (IT n dj B)). apply in_or_app. left. apply in_map. exact HB.
  - intros x Hx. apply HS. apply in_or_app. right. exact Hx.
Qed.

Lemma push_tag_sound (dj : list int) (l : list AST) (w : list item) : forall i,
  items_sound (push_tag i dj l w) -> (forall B, In B l -> Snd B) /\ items_sound w.
Proof.
  induction l as [|B r IH]; intros i HS; cbn [push_tag] in HS.
  - split; [intros B [] | exact HS].
  - destruct (IH (S i) (fun x Hx => HS x (or_intror Hx))) as [H1 H2].
    split; [|exact H2]. intros B' [<-|HB]; [exact (HS _ (or_introl eq_refl)) | exact (H1 B' HB)].
Qed.

Lemma fork_push_sound (tag : bool) (dj : list int) (l : list AST) (w : list item) :
  items_sound (fork_push tag dj l w) -> (forall B, In B l -> Snd B) /\ items_sound w.
Proof.
  unfold fork_push. destruct tag; [|apply push_sound].
  destruct l as [|a [|b r]]; first [apply push_sound | apply push_tag_sound].
Qed.

Lemma rstep_plain_sound (tag : bool) (rs : rstate) (it : item) :
  ICok segs (rs_ic rs) -> rs_status (rstep_plain segs LIM sys tag rs it) = RRun -> rs_sound (rstep_plain segs LIM sys tag rs it) ->
  rs_sound rs /\ Snd (it_st it).
Proof.
  intros Hic Hst HS. unfold rstep_plain in *.
  set (A := it_st it) in *. set (n := it_n it) in *. set (dj := it_dj it) in *.
  destruct (astep segs amodel LIM (rs_ic rs) A) as [ic' r] eqn:Est.
  destruct r as [A'|l|A'|code A'|r k].
  + destruct HS as [Hw [Hp Hf]]. cbn [rs_work rs_parked rs_final] in *.
    split; [split; [exact (fun x Hx => Hw x (or_intror Hx)) | split; assumption] | exact (step_next_sound _ _ A A' Hic Est (Hw _ (or_introl eq_refl)))].
  + destruct HS as [Hw [Hp Hf]]. cbn [rs_work rs_parked rs_final] in *. destruct (fork_push_sound _ _ _ _ Hw) as [Hc Hw'].
    split; [split; [exact Hw' | split; assumption] | exact (step_fork_sound _ _ A l Hic Est Hc)].
  + destruct (sys A) as [l|] eqn:Esys.
    * destruct HS as [Hw [Hp Hf]]. cbn [rs_work rs_parked rs_final] in *. destruct (push_sound _ _ _ _ Hw) as [Hc Hw'].
      split; [split; [exact Hw' | split; assumption] | exact (step_ecall_sound _ _ A A' l Hic Est Esys Hc)].
    * destruct HS as [Hw [Hp Hf]]. cbn [rs_work rs_parked rs_final] in *.
      split; [split; [exact Hw | split; [exact Hp | exact (fun B HB => Hf B (or_intror HB))]] | exact (Hf A (or_introl eq_refl))].
  + discriminate Hst.
  + destruct (floor_child A r k) as [B|] eqn:Efl; [|discriminate Hst].
    destruct HS as [Hw [Hp Hf]]. cbn [rs_work rs_parked rs_final] in *.
    split; [split; [exact (fun x Hx => Hw x (or_intror Hx)) | split; assumption] | exact (H_floor A B r k Efl (Hw _ (or_introl eq_refl)))].
Qed.

Lemma rstep_plain_ic (tag : bool) (rs : rstate) (it : item) : ICok segs (rs_ic rs) -> ICok segs (rs_ic (rstep_plain segs LIM sys tag rs it)).
Proof.
  intros Hic. unfold rstep_plain.
  pose proof (astep_ic segs amodel LIM (rs_ic rs) (it_st it) Hic) as Hic'.
  destruct (astep segs amodel LIM (rs_ic rs) (it_st it)) as [ic' r]. cbn [fst] in Hic'.
  destruct r; cbn [rs_ic]; try exact Hic'.
  + destruct (sys _); exact Hic'.
  + destruct (floor_child _ _ _); exact Hic'.
Qed.

Lemma mini_sound : forall (k : nat) (T : w64) (ic ic' : itrie icent) (C D : AST),
  ICok segs ic -> mini segs LIM k T ic C = (ic', Some D) ->
  (Snd D -> Snd C) /\ a_mem D = a_mem C /\ a_model D = a_model C.
Proof.
  induction k as [|k IH]; intros T ic ic' C D Hic Hm; cbn [mini] in Hm.
  - destruct (w_eqb (a_pc C) T); [|discriminate]. injection Hm as _ <-. split; [exact (fun X => X) | split; reflexivity].
  - destruct (w_eqb (a_pc C) T); [injection Hm as _ <-; split; [exact (fun X => X) | split; reflexivity]|].
    destruct (nomem_at segs amodel ic C) eqn:En; [|discriminate].
    destruct (astep segs amodel LIM ic C) as [ic1 r] eqn:Est. destruct r as [C'| | | |]; try discriminate.
    pose proof (astep_ic segs amodel LIM ic C Hic) as Hic1. rewrite Est in Hic1. cbn [fst] in Hic1.
    destruct (IH T ic1 ic' C' D Hic1 Hm) as [HS [Em Emod]].
    destruct (astep_nomem segs amodel LIM ic ic1 C C' En Est) as [Em1 Emod1].
    split; [intros X; exact (step_next_sound ic ic1 C C' Hic Est (HS X))|]. split; congruence.
Qed.

Lemma mini_ic : forall (k : nat) (T : w64) (ic : itrie icent) (C : AST), ICok segs ic -> ICok segs (fst (mini segs LIM k T ic C)).
Proof.
  induction k as [|k IH]; intros T ic C Hic; cbn [mini].
  - destruct (w_eqb (a_pc C) T); exact Hic.
  - destruct (w_eqb (a_pc C) T); [exact Hic|]. destruct (nomem_at segs amodel ic C); [|exact Hic].
    pose proof (astep_ic segs amodel LIM ic C Hic) as Hic1.
    destruct (astep segs amodel LIM ic C) as [ic1 r]. cbn [fst] in Hic1. destruct r; try exact Hic1. apply IH. exact Hic1.
Qed.

Lemma rstep_forkjoin_sound (T : Z) (k : nat) (rs : rstate) (it : item) :
  ICok segs (rs_ic rs) -> rs_status (rstep_forkjoin segs LIM sys T k rs it) = RRun -> rs_sound (rstep_forkjoin segs LIM sys T k rs it) ->
  rs_sound rs /\ Snd (it_st it).
Proof.
  intros Hic Hst HS. unfold rstep_forkjoin in *.
  destruct (astep segs amodel LIM (rs_ic rs) (it_st it)) as [ic1 r] eqn:Est.
  assert (Hplain : rs_status (rstep_plain segs LIM sys false rs it) = RRun -> rs_sound (rstep_plain segs LIM sys false rs it) -> rs_sound rs /\ Snd (it_st it))
    by (intros X Y; exact (rstep_plain_sound false rs it Hic X Y)).
  destruct r as [A'|l|A'|code A'|r0 k0]; try exact (Hplain Hst HS).
  destruct l as [|Ca [|Cb [|Cc l']]]; try exact (Hplain Hst HS).
  pose proof (astep_ic segs amodel LIM (rs_ic rs) (it_st it) Hic) as Hic1. rewrite Est in Hic1. cbn [fst] in Hic1.
  destruct (mini segs LIM k (wofZ T) ic1 Ca) as [ic2 o1] eqn:E1.
  pose proof (mini_ic k (wofZ T) ic1 Ca Hic1) as Hic2. rewrite E1 in Hic2. cbn [fst] in Hic2.
  destruct (mini segs LIM k (wofZ T) ic2 Cb) as [ic3 o2] eqn:E2.
  assert (Hpush : forall rs', rs_work rs' = push 0 (it_dj it) [Ca; Cb] (rs_work rs) -> rs_parked rs' = rs_parked rs -> rs_final rs' = rs_final rs ->
                  rs_sound rs' -> rs_sound rs /\ Snd (it_st it)).
  { intros rs' Ew Ep Ef [Hw [Hp Hf]]. rewrite Ew in Hw. rewrite Ep in Hp. rewrite Ef in Hf. destruct (push_sound _ _ _ _ Hw) as [Hc Hw'].
    split; [split; [exact Hw' | split; assumption] | exact (step_fork_sound _ _ (it_st it) [Ca; Cb] Hic Est Hc)]. }
  destruct o1 as [Da|]; [|(refine (Hpush _ _ _ _ HS); reflexivity)].
  destruct o2 as [Db|]; [|(refine (Hpush _ _ _ _ HS); reflexivity)].
  destruct (ajoin_nm Da Db) as [J|] eqn:EJ; [|(refine (Hpush _ _ _ _ HS); reflexivity)].
  destruct HS as [Hw [Hp Hf]]. cbn [rs_work rs_parked rs_final] in *.
  destruct (mini_sound k (wofZ T) ic1 ic2 Ca Da Hic1 E1) as [HSa [Ema Emoda]].
  destruct (mini_sound k (wofZ T) ic2 ic3 Cb Db Hic2 E2) as [HSb [Emb Emodb]].
  destruct (astep_fork_mem segs amodel LIM (rs_ic rs) ic1 (it_st it) [Ca; Cb] Est Ca (or_introl eq_refl)) as [Fa Ga].
  destruct (astep_fork_mem segs amodel LIM (rs_ic rs) ic1 (it_st it) [Ca; Cb] Est Cb (or_intror (or_introl eq_refl))) as [Fb Gb].
  destruct (H_join_nm Da Db J ltac:(congruence) ltac:(congruence) EJ (Hw _ (or_introl eq_refl))) as [Sa Sb].
  split; [split; [exact (fun x Hx => Hw x (or_intror Hx)) | split; assumption]|].
  apply (step_fork_sound _ _ (it_st it) [Ca; Cb] Hic Est). intros B [<-|[<-|[]]]; [exact (HSa Sa) | exact (HSb Sb)].
Qed.

Lemma rstep_forkjoin_ic (T : Z) (k : nat) (rs : rstate) (it : item) : ICok segs (rs_ic rs) -> ICok segs (rs_ic (rstep_forkjoin segs LIM sys T k rs it)).
Proof.
  intros Hic. unfold rstep_forkjoin.
  pose proof (astep_ic segs amodel LIM (rs_ic rs) (it_st it) Hic) as Hic1.
  destruct (astep segs amodel LIM (rs_ic rs) (it_st it)) as [ic1 r] eqn:Est. cbn [fst] in Hic1.
  assert (Hplain : ICok segs (rs_ic (rstep_plain segs LIM sys false rs it))) by exact (rstep_plain_ic false rs it Hic).
  destruct r as [A'|l|A'|code A'|r0 k0]; try exact Hplain.
  destruct l as [|Ca [|Cb [|Cc l']]]; try exact Hplain.
  pose proof (mini_ic k (wofZ T) ic1 Ca Hic1) as Hic2.
  destruct (mini segs LIM k (wofZ T) ic1 Ca) as [ic2 o1]. cbn [fst] in Hic2.
  pose proof (mini_ic k (wofZ T) ic2 Cb Hic2) as Hic3.
  destruct (mini segs LIM k (wofZ T) ic2 Cb) as [ic3 o2]. cbn [fst] in Hic3.
  destruct o1 as [Da|]; [|exact Hic3]. destruct o2 as [Db|]; [|exact Hic3]. destruct (ajoin_nm Da Db); exact Hic3.
Qed.

Lemma rstep_item_sound (rs : rstate) (it : item) :
  ICok segs (rs_ic rs) -> rs_status (rstep_item segs LIM H sys sum rs it) = RRun -> rs_sound (rstep_item segs LIM H sys sum rs it) ->
  rs_sound rs /\ Snd (it_st it).
Proof.
  intros Hic Hst HS. unfold rstep_item in *.
  set (A := it_st it) in *. set (n := it_n it) in *. set (dj := it_dj it) in *.
  destruct (match dj with d :: dj' => if (dj_key d =? ic_key (a_pc A))%uint63 then Some dj' else None | [] => None end) as [dj'|].
  { destruct HS as [Hw [Hp Hf]]. cbn [rs_work rs_parked rs_final] in *. destruct (park_sound _ _ Hp) as [P1 P2].
    split; [split; [exact Hw | split; [exact P1 | exact Hf]] | exact P2]. }
  destruct (nth_error (hints_at H (a_pc A)) n) as [h|].
  - destruct h as [f cuts|r cuts|f cuts| |v h k|r k|k| | | |T0 k0| |ra ka].
    +   destruct (split_ok A f cuts) eqn:Eok; [|discriminate Hst].
      destruct HS as [Hw [Hp Hf]]. cbn [rs_work rs_parked rs_final] in *. destruct (push_sound _ _ _ _ Hw) as [Hc Hw'].
      split; [split; [exact Hw' | split; assumption] | exact (H_split A f cuts Eok Hc)].
    +   destruct (negb (r <? 32)%uint63) eqn:Er; [discriminate Hst|]. apply negb_false_iff in Er.
      destruct (xform (a_facts A) (canon_v (a_facts A) (aget (a_regs A) r))) as [f|] eqn:Exf; [|discriminate Hst].
      destruct (snd f) eqn:Esf.
      * destruct HS as [Hw [Hp Hf]]. cbn [rs_work rs_parked rs_final] in *.
        split; [split; [exact (fun x Hx => Hw x (or_intror Hx)) | split; assumption] | exact (Hw _ (or_introl eq_refl))].
      * destruct (split_ok A f cuts) eqn:Eok; [|discriminate Hst].
        destruct HS as [Hw [Hp Hf]]. cbn [rs_work rs_parked rs_final] in *. destruct (push_sound _ _ _ _ Hw) as [Hc Hw'].
        split; [split; [exact Hw' | split; assumption] | exact (H_split_reg A r f cuts Er Exf Eok Hc)].
    +   destruct (aget (a_regs A) 1%uint63) as [ra| | | | |]; try discriminate Hst.
      destruct (split_ok A f cuts) eqn:Eok; [|discriminate Hst].
      destruct HS as [Hw [Hp Hf]]. cbn [rs_work rs_parked rs_final] in *. destruct (push_sound _ _ _ _ Hw) as [Hc Hw'].
      split; [split; [exact Hw' | split; assumption] | exact (H_split A f cuts Eok Hc)].
    +   destruct HS as [Hw [Hp Hf]]. cbn [rs_work rs_parked rs_final] in *. destruct (park_sound _ _ Hp) as [P1 P2].
      split; [split; [exact Hw | split; [exact P1 | exact Hf]] | exact P2].
    +   destruct (fresh_ok A v h k) eqn:Eok; [|discriminate Hst].
      destruct HS as [Hw [Hp Hf]]. cbn [rs_work rs_parked rs_final] in *.
      split; [split; [exact (fun x Hx => Hw x (or_intror Hx)) | split; assumption] | exact (H_fresh A v h k Eok (Hw _ (or_introl eq_refl)))].
    +   destruct (floor_child A r k) as [B|] eqn:Efl; [|discriminate Hst].
      destruct HS as [Hw [Hp Hf]]. cbn [rs_work rs_parked rs_final] in *.
      split; [split; [exact (fun x Hx => Hw x (or_intror Hx)) | split; assumption] | exact (H_floor A B r k Efl (Hw _ (or_introl eq_refl)))].
    +   destruct (sum k A) as [l|] eqn:Esum.
      * destruct HS as [Hw [Hp Hf]]. cbn [rs_work rs_parked rs_final] in *. destruct (push_sound _ _ _ _ Hw) as [Hc Hw'].
        split; [split; [exact Hw' | split; assumption] | exact (H_sum k A l Esum Hc)].
      * destruct HS as [Hw [Hp Hf]]. cbn [rs_work rs_parked rs_final] in *.
        split; [split; [exact (fun x Hx => Hw x (or_intror Hx)) | split; assumption] | exact (Hw _ (or_introl eq_refl))].
    +   destruct HS as [Hw [Hp Hf]]. cbn [rs_work rs_parked rs_final] in *.
      split; [split; [exact Hw | split; [exact Hp | exact (fun B HB => Hf B (or_intror HB))]] | exact (Hf A (or_introl eq_refl))].
    +   destruct (aget (a_regs A) 1%uint63) as [ra| | | | |]; try discriminate Hst.
      destruct HS as [Hw [Hp Hf]]. cbn [rs_work rs_parked rs_final] in *.
      split; [split; [exact (fun x Hx => Hw x (or_intror Hx)) | split; assumption] | exact (Hw _ (or_introl eq_refl))].
    +   exact (rstep_plain_sound true rs it Hic Hst HS).
    +   exact (rstep_forkjoin_sound T0 k0 rs it Hic Hst HS).
    +   destruct (aget (a_regs A) 1%uint63) as [ra| | | | |]; try discriminate Hst.
      destruct HS as [Hw [Hp Hf]]. cbn [rs_work rs_parked rs_final] in *.
      split; [split; [exact (fun x Hx => Hw x (or_intror Hx)) | split; assumption] | exact (Hw _ (or_introl eq_refl))].
    +
      assert (Hskip : rs_sound (RS RRun (IT (S n) dj A :: rs_work rs) (rs_parked rs) (rs_final rs) (rs_ic rs) (rs_count rs + 1) []) ->
                      rs_sound rs /\ Snd A).
      { intros [Hw [Hp Hf]]. cbn [rs_work rs_parked rs_final] in *.
        split; [split; [exact (fun x Hx => Hw x (or_intror Hx)) | split; assumption] | exact (Hw _ (or_introl eq_refl))]. }
      destruct (align_children A ra ka) as [l|] eqn:Eal; [|exact (Hskip HS)].
      destruct (aget (a_regs A) 1%uint63) as [ra0| | | | |]; try exact (Hskip HS).
      destruct HS as [Hw [Hp Hf]]. cbn [rs_work rs_parked rs_final] in *. destruct (push_sound _ _ _ _ Hw) as [Hc Hw'].
      split; [split; [exact Hw' | split; assumption] | exact (H_align A ra ka l Eal Hc)].
  - exact (rstep_plain_sound false rs it Hic Hst HS).
Qed.

Lemma rstep_item_ic (rs : rstate) (it : item) : ICok segs (rs_ic rs) -> ICok segs (rs_ic (rstep_item segs LIM H sys sum rs it)).
Proof.
  intros Hic. unfold rstep_item.
  destruct (match it_dj it with d :: dj' => if (dj_key d =? ic_key (a_pc (it_st it)))%uint63 then Some dj' else None | [] => None end); [exact Hic|].
  destruct (nth_error (hints_at H (a_pc (it_st it))) (it_n it)) as [h|].
  - destruct h; cbn [rs_ic]; try exact Hic.
    + destruct (split_ok _ _ _); exact Hic.
    + destruct (negb _); [exact Hic|]. destruct (xform _ _) as [f|]; [|exact Hic]. destruct (snd f); [exact Hic|]. destruct (split_ok _ _ _); exact Hic.
    + destruct (aget _ _); try exact Hic. destruct (split_ok _ _ _); exact Hic.
    + destruct (fresh_ok _ _ _ _); exact Hic.
    + destruct (floor_child _ _ _); exact Hic.
    + destruct (sum _ _); exact Hic.
    + destruct (aget _ _); exact Hic.
    + exact (rstep_plain_ic true rs it Hic).
    + exact (rstep_forkjoin_ic T k rs it Hic).
    + destruct (aget _ _); exact Hic.
    + destruct (align_children _ _ _); [destruct (aget _ _)|]; exact Hic.
  - exact (rstep_plain_ic false rs it Hic).
Qed.

Lemma rstep_sound (rs : rstate) :
  ICok segs (rs_ic rs) -> rs_status (rstep segs LIM H sys sum rs) = RRun -> rs_sound (rstep segs LIM H sys sum rs) ->
  rs_sound rs /\ rs_status rs = RRun.
Proof.
  intros Hic Hst HS. unfold rstep in *. destruct (rs_status rs) eqn:Es; [|rewrite Es in Hst; discriminate Hst|rewrite Es in Hst; discriminate Hst]. split; [|reflexivity].
  destruct rs as [st w p f ic cnt dbg]. cbn [rs_status rs_work rs_parked rs_final rs_ic rs_count] in *.
  destruct w as [|it w].
  - destruct p as [|q p]; [exact HS|]. destruct HS as [Hw [_ Hf]]. cbn [rs_work rs_parked rs_final] in *.
    split; [intros x [] | split; [exact Hw | exact Hf]].
  - destruct (rstep_item_sound (RS RRun w p f ic cnt []) it Hic Hst HS) as [[Hw [Hp Hf]] Hit]. cbn [rs_work rs_parked rs_final] in *.
    split; [|split; assumption]. intros x [<-|Hx]; [exact Hit | exact (Hw x Hx)].
Qed.

Lemma rstep_ic (rs : rstate) : ICok segs (rs_ic rs) -> ICok segs (rs_ic (rstep segs LIM H sys sum rs)).
Proof.
  intros Hic. unfold rstep. destruct (rs_status rs); try exact Hic. destruct (rs_work rs) as [|it w].
  - destruct (rs_parked rs); exact Hic.
  - apply rstep_item_ic. exact Hic.
Qed.

Lemma riter_ic : forall (p : positive) (rs : rstate), ICok segs (rs_ic rs) -> ICok segs (rs_ic (riter segs LIM H sys sum p rs)).
Proof.
  induction p as [q IH|q IH|]; intros rs Hic; cbn [riter]; destruct (rdone rs); try exact Hic.
  - apply rstep_ic. apply IH. apply IH. exact Hic.
  - apply IH. apply IH. exact Hic.
  - apply rstep_ic. exact Hic.
Qed.

Lemma riter_sound : forall (p : positive) (rs : rstate),
  ICok segs (rs_ic rs) -> rs_status (riter segs LIM H sys sum p rs) = RRun -> rs_sound (riter segs LIM H sys sum p rs) ->
  rs_sound rs /\ rs_status rs = RRun.
Proof.
  induction p as [q IH|q IH|]; intros rs Hic Hst HS; cbn [riter] in *.
  - destruct (rdone rs) eqn:Ed; [split; [exact HS | exact Hst]|].
    pose proof (riter_ic q rs Hic) as Hic1. pose proof (riter_ic q _ Hic1) as Hic2.
    destruct (rstep_sound _ Hic2 Hst HS) as [HS2 Hst2].
    destruct (IH _ Hic1 Hst2 HS2) as [HS1 Hst1]. exact (IH rs Hic Hst1 HS1).
  - destruct (rdone rs) eqn:Ed; [split; [exact HS | exact Hst]|].
    pose proof (riter_ic q rs Hic) as Hic1.
    destruct (IH _ Hic1 Hst HS) as [HS1 Hst1]. exact (IH rs Hic Hst1 HS1).
  - destruct (rdone rs) eqn:Ed; [split; [exact HS | exact Hst]|]. exact (rstep_sound rs Hic Hst HS).
Qed.

Theorem run_sound (ic : itrie icent) (p : positive) (A0 : AST) :
  ICok segs ic ->
  rs_status (run segs LIM H sys sum p ic A0) = RRun ->
  rs_work (run segs LIM H sys sum p ic A0) = [] ->
  rs_parked (run segs LIM H sys sum p ic A0) = [] ->
  (forall B, In B (rs_final (run segs LIM H sys sum p ic A0)) -> Snd B) ->
  Snd A0.
Proof.
  intros Hic Hst Hw Hp Hf. unfold run in *.
  destruct (riter_sound p (RS RRun [IT 0 [] A0] [] [] ic 0 []) Hic Hst) as [[HS _] _].
  - split; [rewrite Hw; intros x [] | split; [rewrite Hp; intros x [] | exact Hf]].
  - exact (HS (IT 0 [] A0) (or_introl eq_refl)).
Qed.

End RunSound.
