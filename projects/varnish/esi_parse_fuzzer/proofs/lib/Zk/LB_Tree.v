(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Decode.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc Mall7vg KInv KLink.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require LB_Ljn7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall7vg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLink OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Sim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Ljn7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.LB_Dead.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.

Module KRoom.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect Mremap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import AgentLib RelSpec MmapSim AllocSim RefNodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require PropExec MState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Monad MSafe STree Malloc MProg KInv KNodes KLink.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dest4xs.Prelim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Monad OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MSafe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MProg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KNodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLink.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pwdisj_nodup_elo : forall l, pwdisj l -> (forall e, In e l -> elo e < ehi e) -> NoDup (map elo l).
Proof.
  induction l as [|e l IH]; intros HP HN; [constructor|].
  inversion HP as [|e' l' Hd Hl]; subst. cbn. constructor.
  - intros Hin. apply (proj1 (list_elem_of_In _ _)) in Hin. apply in_map_iff in Hin as (e2 & Ee & Hin2).
    specialize (Hd e2 Hin2). pose proof (HN e (or_introl eq_refl)) as N1. pose proof (HN e2 (or_intror Hin2)) as N2.
    unfold edisj in Hd. lia.
  - apply IH; [exact Hl| intros e2 H2; apply HN; right; exact H2].
Qed.

(* [comment removed for export] *)
Definition brk_pages (start : Z) (K : nat) : list Z := map (fun i => start + Z.of_nat i * PGSZ) (seq 0 K).

Lemma in_brk_pages start K x : start <= x -> x < start + Z.of_nat K * PGSZ -> (x - start) mod PGSZ = 0 -> In x (brk_pages start K).
Proof.
  intros H1 H2 H3. unfold brk_pages. apply in_map_iff. exists (Z.to_nat ((x - start) / PGSZ)).
  pose proof (Z.div_mod (x - start) PGSZ ltac:(unfold PGSZ; lia)) as DM. rewrite H3 in DM.
  assert (0 <= (x - start) / PGSZ) by (apply Z.div_pos; unfold PGSZ in *; lia).
  split; [rewrite Z2Nat.id by lia; unfold PGSZ in *; lia|].
  apply in_seq. split; [lia|]. cbn [Nat.add].
  assert ((x - start) / PGSZ < Z.of_nat K) by (apply Z.div_lt_upper_bound; unfold PGSZ in *; lia). lia.
Qed.

Section CEIL.
Context {Clg : Ceiling}.

Theorem maps_len_bound L pbrk mo (K : nat) :
  KL L pbrk mo -> brk_extent L <= Z.of_nat K * PGSZ ->
  (length (vm_maps (m_vmmaps mo)) <= length (ld_groups L) + length (ld_metas L) + K)%nat.
Proof.
  intros HK HE. set (maps := vm_maps (m_vmmaps mo)).
  pose proof (kl_wf _ _ _ HK) as [NE PW]. fold maps in NE, PW.
  pose proof (pwdisj_nodup_elo maps PW ltac:(intros e He; exact (proj1 (NE e He)))) as ND.
  set (start := bv_unsigned (vm_start_brk (m_vmmaps mo))).
  set (cands := map (fun bl : Z * Z => elo (went (fst bl) (mmap_len (snd bl)))) (ld_groups L)
              ++ map (fun blk : Z * Z * Z => elo (went (fst (fst blk)) (mmap_len (snd (fst blk))))) (ld_metas L)
              ++ brk_pages start K).
  assert (INCL : incl (map elo maps) cands).
  { intros x Hx. apply in_map_iff in Hx as (e & <- & He).
    destruct (kl_complete _ _ _ HK e He) as [(b & l & Hin & ->)|[(b & l & k & Hin & ->)|(X1 & X2 & X3 & X4)]]; unfold cands.
    - apply in_app_iff. left. apply in_map_iff. exists (b, l). auto.
    - apply in_app_iff. right. apply in_app_iff. left. apply in_map_iff. exists (b, l, k). auto.
    - apply in_app_iff. right. apply in_app_iff. right.
      pose proof (kl_brkb _ _ _ HK) as BB. pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4). fold start in BB, S1, S2, S3, S4, X1.
      apply in_brk_pages; [exact X1| lia|]. rewrite Zminus_mod, X3. unfold PGSZ in *. rewrite S2. reflexivity. }
  apply NoDup_ListNoDup in ND. pose proof (NoDup_incl_length ND INCL) as LEN. rewrite length_map in LEN. unfold cands in LEN.
  rewrite !length_app, !length_map, length_seq in LEN. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition room (N C : Z) (mo : Model) : Prop :=
  let h := m_vmmaps mo in
  0 < N /\ N mod page_size = 0
  /\ Forall (fun p => bv_unsigned (snd p) <= N) (vm_reserved h ++ vm_maps h)
  /\ Z.of_nat (length (vm_reserved h ++ vm_maps h)) <= C
  /\ bottomup_floor + C * (2 * N) + N <= alloc_ceiling.

Lemma rlen_mmap_len : forall len, 0 < len < LEN_MAX -> rlen len = mmap_len len /\ 0 <= mmap_len len.
Proof.
  intros len Hlen. unfold LEN_MAX in Hlen. rewrite (rlen_eq len) by lia.
  pose proof (mmap_len_ge len ltac:(lia)). split; [reflexivity | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma KL_mprotect_budget : forall L pbrk mo (a n : word),
  KL L pbrk mo -> vm_live_bytes (m_vmmaps mo) <= vm_limit (m_vmmaps mo) ->
  mprotect_budget_ok mo a n = true.
Proof.
  intros L pbrk mo a n HK Hb. unfold mprotect_budget_ok, vm_backing_within_limit. apply Z.leb_le.
  rewrite mprotect_model_next_eq.
  etransitivity; [apply vm_backing_used_le_live| ].
  - unfold mprotect_model. rewrite with_vmmaps_lazy'. exact (kl_minv _ _ _ HK).
  - unfold mprotect_model. cbn. exact (kl_mat _ _ _ HK).
  - unfold mprotect_model. rewrite with_vmmaps_vm. cbn [vm_limit]. unfold vm_live_bytes in *. cbn [vm_maps]. exact Hb.
Qed.

Lemma KL_mprotect_nf : forall L pbrk mo a len prot,
  KL L pbrk mo -> vm_live_bytes (m_vmmaps mo) <= vm_limit (m_vmmaps mo) ->
  nrefusable (NMprotect a len prot) mo = false.
Proof.
  intros L pbrk mo a len prot HK Hb. cbn [nrefusable].
  apply mprotect_not_refusable. exact (KL_mprotect_budget L pbrk mo _ _ HK Hb).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

End CEIL.
End KRoom.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.

Set Implicit Arguments.

Section LBCEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint fbnd {R} (B : Z) (L : mled) (t : M R) {struct t} : Prop :=
  match t with
  | SRet _ => True
  | SVis (EPeek _ _ _) k => forall v, fbnd B L (k v)
  | SVis (EUndef _) _ => True
  | SVis e k => BOUNDX L e B /\ forall a, answer_ok L e a = true -> fbnd B (event_post L e a) (k a)
  end.

(* [comment removed for export] *)


(* [comment removed for export] *)
Lemma fbnd_strel {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) B :
  strel RR t1 t2 -> forall L, fbnd B L t1 -> fbnd B L t2.
Proof.
  induction 1 as [r1 r2 Hr|e k1 k2 Hk IH]; intros L H; cbn [fbnd] in *; [exact I|].
  destruct e; try (destruct H as [HB H1]; split; [exact HB|]; intros a Ha; apply IH; apply H1; exact Ha).
  - intros v. apply IH. apply H.
  - exact I.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section PRUN.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).

(* [comment removed for export] *)
End PRUN.

(* [comment removed for export] *)
Lemma qtree_intro {R} B : forall (t : M R) L Post, ctree_ok L t Post -> fbnd B L t -> qtree B L t Post.
Proof.
  induction t as [r|e k IH]; intros L Post HC HB; cbn [ctree_ok fbnd qtree] in *; [exact HC|].
  destruct HC as [He Hk].
  destruct e; try (destruct HB as [HB1 HB2]; split; [exact He|]; split; [exact HB1|]; intros z Hz; apply IH; [apply Hk; exact Hz| apply HB2; exact Hz]);
    cbn in He; destruct He.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint fqtree {R} (B : Z) (L : mled) (t : M R) (Post : mled -> R -> Prop) {struct t} : Prop :=
  match t with
  | SRet r => Post L r
  | SVis (EPeek _ _ _) k => forall v, 0 <= v < 256 -> fqtree B L (k v) Post
  | SVis (EUndef _) _ => False
  | SVis e k => event_pre L e /\ BOUNDX L e B /\ forall a, if answer_ok L e a then fqtree B (event_post L e a) (k a) Post else rejects (k a)
  end.

Lemma fqtree_ftree {R} B (t : M R) : forall L Post, fqtree B L t Post -> ftree L t Post.
Proof.
  induction t as [r|e k IH]; intros L Post H; cbn [fqtree ftree] in *; [exact H|].
  destruct e; try (destruct H as (He & HB & Hk); split; [exact He|]; intros a; specialize (Hk a); case_ans; [apply IH; exact Hk| exact Hk]).
  - intros v Hv. apply IH. apply H. exact Hv.
  - exact H.
Qed.

(* [comment removed for export] *)
Fixpoint fbnd8 {R} (B : Z) (L : mled) (t : M R) {struct t} : Prop :=
  match t with
  | SRet _ => True
  | SVis (EPeek _ _ _) k => forall v, 0 <= v < 256 -> fbnd8 B L (k v)
  | SVis (EUndef _) _ => True
  | SVis e k => BOUNDX L e B /\ forall a, answer_ok L e a = true -> fbnd8 B (event_post L e a) (k a)
  end.

(* [comment removed for export] *)

Section PRUN8.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.

Lemma fbnd8_prun {R} B : forall (t : M R) L o, fbnd8 B L t -> fbnd B L (prun pans pupd o t).
Proof.
  induction t as [r|e k IH]; intros L o H; cbn [fbnd8 fbnd] in *; [exact I|].
  unfold prun. destruct e; cbn [eruns psel]; try (destruct H as [HB Hk]; split; [exact HB|]; intros a Ha; apply IH; apply Hk; exact Ha).
  - apply IH. apply H. apply Hpans.
  - exact I.
Qed.
End PRUN8.

(* [comment removed for export] *)
Lemma fqtree_ret {R} B L (r : R) Post : Post L r -> fqtree B L (SRet r) Post.
Proof. intros H. exact H. Qed.

(* [comment removed for export] *)
Lemma fqtree_vis {R} B L e (k : Z -> M R) Post :
  is_peek e = false -> is_undef e = false ->
  event_pre L e -> BOUND L e B -> XB L e B ->
  (forall a, answer_ok L e a = true -> fqtree B (event_post L e a) (k a) Post) ->
  (forall a, answer_ok L e a = false -> rejects (k a)) ->
  fqtree B L (SVis e k) Post.
Proof.
  intros Hp Hu He HB HX Hk Hr. destruct e; cbn in Hp, Hu; try discriminate; cbn [fqtree]; split; auto; split; try (split; assumption);
  intros a; case_ans; auto.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma fqtree_guard {R} B L tag (c : bool) (k bail : M R) Post :
  c = true -> fqtree B L k Post -> fqtree B L (guard tag c k bail) Post.
Proof. intros -> H. exact H. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CTRL.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.

(* [comment removed for export] *)
(* [comment removed for export] *)
End CTRL.

(* [comment removed for export] *)
Lemma lbytes_event_post_munmap L a len z : (forall g, In g (ld_groups L) -> 0 <= snd g) ->
  gm (event_post L (EMunmap a len) z) + BB (event_post L (EMunmap a len) z) <= gm L + BB L.
Proof.
  intros POS. cbn [event_post]. rewrite BB_set_groups.
  assert (H : forall l, (forall g, In g l -> 0 <= snd g) ->
    fold_right Z.add 0 (map (fun g : Z * Z => mmap_len (snd g)) (g_remove a l)) <= fold_right Z.add 0 (map (fun g : Z * Z => mmap_len (snd g)) l)).
  { induction l as [|[b l0] l IH]; intros P0; cbn; [lia|]. pose proof (P0 (b, l0) (or_introl eq_refl)) as Hl0. cbn in Hl0.
    destruct (b =? a); cbn.
    - assert (0 <= mmap_len l0) by (unfold mmap_len, page_round_up_Z; rewrite page_size_eq; apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]).
      lia.
    - specialize (IH ltac:(intros g Hg; apply P0; right; exact Hg)). lia. }
  unfold gm. cbn [ld_groups ld_metas set_groups]. specialize (H (ld_groups L) POS). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma fbnd8_bind {R S} B (t : M R) (f : R -> M S) (Post : mled -> R -> Prop) : forall L,
  fqtree B L t Post -> (forall L' r, Post L' r -> fbnd8 B L' (f r)) -> fbnd8 B L (sbind t f).
Proof.
  induction t as [r|e k IH]; intros L FT Hf; cbn [fbnd8 fqtree sbind] in *.
  - apply Hf. exact FT.
  - destruct e; try (destruct FT as (_ & HB & FK); split; [exact HB|]; intros a Ha; specialize (FK a); rewrite Ha in FK;
      apply IH; [exact FK| exact Hf]).
    + intros v Hv. apply IH; [apply FT; exact Hv| exact Hf].
    + destruct FT.
Qed.

(* [comment removed for export] *)

Lemma fbnd8_rd8 {R} B L st q (k : Z -> M R) : (forall v, fbnd8 B L (k v)) -> fbnd8 B L (rd8 st q k).
Proof.
  intros H. unfold rd8. destruct (cell_read _ _) as [v|h]; [apply H|].
  cbn [fbnd8]. intros v Hv. destruct (peek_answer_ok v); [apply H| exact I].
Qed.

Lemma fbnd8_rd16 {R} B L st q (k : Z -> M R) : (forall v, fbnd8 B L (k v)) -> fbnd8 B L (rd16 st q k).
Proof. intros H. unfold rd16. apply fbnd8_rd8. intros b0. apply fbnd8_rd8. intros b1. apply H. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fbnd8_enframe_full B L st g idx n ctr (k : mstate -> aptr -> M (mstate * optr)) :
  (forall st' p, fbnd8 B L (k st' p)) -> fbnd8 B L (enframe_full st g idx n ctr k).
Proof.
  intros Hk. unfold enframe_full, enframe_read_off. apply fbnd8_rd8. intros b3.
  destruct (negb (b3 =? 0)).
  - apply fbnd8_rd16. intros o16. destruct (enframe_at _ _ _ _ _). apply Hk.
  - destruct (enframe_at _ _ _ _ _). apply Hk.
Qed.

Section CTRL8.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.

(* [comment removed for export] *)
Theorem qtree_of_full8 {R1 R2} (RR : (O * R1)%type -> R2 -> Prop) B (t : M R1) (tc : M R2) L Post (PostC : mled -> R2 -> Prop) o :
  ftree L t Post -> fbnd8 B L t -> strel RR (prun pans pupd o t) tc ->
  (forall L' x r2, RR x r2 -> Post L' (snd x) -> PostC L' r2) ->
  qtree B L tc PostC.
Proof.
  intros FT FB REL HP. apply qtree_intro.
  - apply ptree_ctree_ok. eapply (ptree_strel REL); [exact HP|]. exact (ftree_prun pans pupd Hpans t L Post o FT).
  - eapply (@fbnd_strel _ _ RR _ tc B REL). apply (fbnd8_prun pans pupd Hpans). exact FB.
Qed.
End CTRL8.

End LBCEIL.
