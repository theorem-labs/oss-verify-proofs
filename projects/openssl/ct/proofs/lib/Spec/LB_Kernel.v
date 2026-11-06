(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim Monad MSafe STree Malloc Prog KInv KStep.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Relim Unforced.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Section WithCeiling. Context {CE__ : Ceiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition gm (L : mled) : Z :=
  fold_right Z.add 0 (map (fun g : Z * Z => mmap_len (snd g)) (ld_groups L))
  + fold_right Z.add 0 (map (fun m : Z * Z * Z => mmap_len (snd (fst m))) (ld_metas L)).

(* [comment removed for export] *)
Definition BB (L : mled) : Z :=
  match ld_brk L with
  | BPGuard _ => 2 * PGSZ
  | _ => match ld_brkreg L with Some (_, l) => l | None => 0 end
  end.

(* [comment removed for export] *)
Definition LI (L : mled) (mo : Model) : Prop := vm_live_bytes (m_vmmaps mo) <= gm L + BB L /\ GK (m_vmmaps mo).

Lemma live_bytes_cons e l : live_bytes (e :: l) = bv_unsigned (snd e) + live_bytes l.
Proof. destruct e; reflexivity. Qed.

Lemma live_bytes_app l1 l2 : live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a n] l1 IH]; cbn; [reflexivity| rewrite IH; lia]. Qed.

Lemma live_bytes_nonneg l : 0 <= live_bytes l.
Proof. induction l as [|[a n] l IH]; cbn; [lia|]. pose proof (bv_unsigned_in_range 64 n). lia. Qed.

Lemma live_bytes_filter_le f l : live_bytes (List.filter f l) <= live_bytes l.
Proof. induction l as [|[a n] l IH]; cbn; [lia|]. pose proof (bv_unsigned_in_range 64 n). destruct (f (a, n)); cbn; lia. Qed.

(* [comment removed for export] *)
Lemma live_bytes_remove_notin l aw : (forall e', In e' l -> fst e' <> aw) -> live_bytes (map_remove l aw) = live_bytes l.
Proof.
  unfold map_remove. induction l as [|[a n] l IH]; intros NI; [reflexivity|]. cbn [List.filter fst].
  destruct (bv_eqb a aw) eqn:E; [exfalso; apply bv_eqb_eq in E; exact (NI (a, n) (or_introl eq_refl) E)|]. cbn [negb].
  rewrite !live_bytes_cons. rewrite IH; [reflexivity|]. intros e' He'. apply NI. right. exact He'.
Qed.

Lemma live_bytes_remove maps aw nw : vmwf maps -> In (aw, nw) maps ->
  live_bytes (map_remove maps aw) = live_bytes maps - bv_unsigned nw.
Proof.
  intros [Hne Hpw] Hin. induction maps as [|e l IH]; [destruct Hin|].
  inversion Hpw as [|e0 l0 Hd Hpw']; subst.
  assert (SAME : forall e', In e' l -> fst e' = fst e -> False).
  { intros e' He' E. specialize (Hd e' He'). unfold edisj, elo, ehi in Hd. rewrite E in Hd.
    pose proof (Hne e (or_introl eq_refl)) as N1. pose proof (Hne e' (or_intror He')) as N2. unfold elo, ehi in N1, N2. rewrite E in N2. lia. }
  unfold map_remove. cbn [List.filter]. destruct Hin as [->|Hin].
  - cbn [fst]. rewrite bv_eqb_refl. cbn [negb]. rewrite live_bytes_cons. cbn [snd].
    fold (map_remove l aw). rewrite live_bytes_remove_notin; [lia|]. intros e' He' E. exact (SAME e' He' E).
  - destruct (bv_eqb (fst e) aw) eqn:E.
    + exfalso. apply bv_eqb_eq in E. exact (SAME _ Hin (eq_sym E)).
    + cbn [negb]. rewrite !live_bytes_cons. fold (map_remove l aw). rewrite IH; [lia| intros x Hx; apply Hne; right; exact Hx| exact Hpw'| exact Hin].
Qed.

(* [comment removed for export] *)
Lemma live_bytes_iv_subtract a sz lo hi : lo <= hi ->
  live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz.
Proof.
  intros Hlh. pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 sz) as Rs. unfold bv_modulus in *.
  unfold iv_subtract.
  destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn -[Z_to_bv bv_unsigned Z.sub Z.add Z.min Z.max];
    rewrite ?unsigned_lit by lia; cbn [live_bytes]; try lia.
Qed.

Lemma live_bytes_subtract maps lo hi : lo <= hi -> live_bytes (maps_subtract maps lo hi) <= live_bytes maps.
Proof.
  intros H. induction maps as [|[a sz] l IH]; cbn -[iv_subtract]; [lia|]. rewrite live_bytes_app. pose proof (live_bytes_iv_subtract a sz lo hi H). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma gm_set_brkph ph L : gm (set_brkph ph L) = gm L. Proof. reflexivity. Qed.
Lemma gm_set_brkreg v L : gm (set_brkreg v L) = gm L. Proof. reflexivity. Qed.
Lemma gm_set_live v L : gm (set_live v L) = gm L. Proof. reflexivity. Qed.
Lemma BB_set_live v L : BB (set_live v L) = BB L. Proof. reflexivity. Qed.
Lemma gm_add_group a len L : gm (set_groups ((a, len) :: ld_groups L) L) = gm L + mmap_len len.
Proof. unfold gm. cbn. lia. Qed.
Lemma gm_add_meta a len L : gm (set_metas ((a, len, 0) :: ld_metas L) L) = gm L + mmap_len len.
Proof. unfold gm. cbn. lia. Qed.
Lemma BB_set_groups v L : BB (set_groups v L) = BB L. Proof. reflexivity. Qed.
Lemma BB_set_metas v L : BB (set_metas v L) = BB L. Proof. reflexivity. Qed.

Lemma sum_map_app {A} (f : A -> Z) l1 l2 : fold_right Z.add 0 (map f (l1 ++ l2)) = fold_right Z.add 0 (map f l1) + fold_right Z.add 0 (map f l2).
Proof. induction l1 as [|x l1 IH]; cbn; [lia| rewrite IH; lia]. Qed.

Lemma gm_remove_group L pbrk mo a l0 : KL L pbrk mo -> In (a, l0) (ld_groups L) ->
  gm (set_groups (g_remove a (ld_groups L)) L) = gm L - mmap_len l0.
Proof.
  intros HK Hin. destruct (g_remove_split a l0 (ld_groups L) _ Hin (kl_distinct _ _ _ HK)) as (g1 & g2 & Eg & Ezz).
  unfold gm. cbn [ld_groups ld_metas set_groups]. rewrite Ezz, Eg, !sum_map_app. cbn. lia.
Qed.

Lemma gm_bump a L : gm (set_metas (map (bump_meta a) (ld_metas L)) L) = gm L.
Proof.
  unfold gm. cbn [ld_groups ld_metas set_metas]. f_equal.
  induction (ld_metas L) as [|[[b l] k] ms IH]; cbn; [reflexivity|]. rewrite IH. unfold bump_meta. destruct (b + (1 + k) * PGSZ =? a); reflexivity.
Qed.

Lemma LI_intro L mo : vm_live_bytes (m_vmmaps mo) <= gm L + BB L -> GK (m_vmmaps mo) -> LI L mo. Proof. intros H G. split; assumption. Qed.
Lemma LI_elim L mo : LI L mo -> vm_live_bytes (m_vmmaps mo) <= gm L + BB L. Proof. intros H. exact (proj1 H). Qed.
Lemma LI_gk L mo : LI L mo -> GK (m_vmmaps mo). Proof. intros H. exact (proj2 H). Qed.

(* [comment removed for export] *)
Lemma LI_same_vm L L' mo mo' : LI L mo -> vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mo) -> gm L' = gm L -> BB L' = BB L ->
  vm_limit (m_vmmaps mo') = vm_limit (m_vmmaps mo) -> vm_start_brk (m_vmmaps mo') = vm_start_brk (m_vmmaps mo) -> LI L' mo'.
Proof.
  intros [H G] E1 E2 E3 E4 E5. split.
  - unfold vm_live_bytes in *. rewrite E1, E2, E3. exact H.
  - apply (GK_ext (m_vmmaps mo)); [exact G| rewrite E1; apply incl_refl| exact E4| exact E5].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma li_brk0 L pbrk mo rsp mo' evs z : KL L pbrk mo -> LI L mo -> ld_brk L = BPUntried ->
  nstep (NBrk 0) mo rsp mo' evs -> LI (set_brkph (BPQueried z) L) mo'.
Proof.
  intros HK HL Hph Hst. destruct (nstep_brk_inv 0 mo rsp mo' evs Hst) as (r & Hok & -> & _ & _).
  apply brk_r_ok_query in Hok. subst r. destruct (brk_model_next_query (m_vmmaps mo)) as (_ & E2 & _).
  pose proof (kl_phase _ _ _ HK) as P. rewrite Hph in P. destruct P as [_ Hreg].
  apply (LI_same_vm L _ mo); [exact HL| rewrite m_vmmaps_with_brk_next; exact E2| reflexivity| | rewrite m_vmmaps_with_brk_next; reflexivity| rewrite m_vmmaps_with_brk_next; reflexivity]. unfold BB. cbn. rewrite Hreg, Hph. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma li_brk_grow L pbrk mo rsp mo' evs req a :
  KL L pbrk mo -> LI L mo ->
  ((exists cur, ld_brk L = BPQueried cur /\ req = round_up_pg cur + 2 * PGSZ)
   \/ (exists b l, ld_brk L = BPLive /\ ld_brkreg L = Some (b, l) /\ req = b + l + PGSZ)) ->
  nstep (NBrk req) mo rsp mo' evs -> dec_brk pbrk req rsp = Some a ->
  LI (event_post L (EBrk req) (match a with BrkGrown => req | BrkSame => pbrk end)) mo'.
Proof.
  intros HK HL Hpre Hst Hd. pose proof alloc_ceiling_lt as Hcl.
  pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4). pose proof (kl_phase _ _ _ HK) as P.
  set (h := m_vmmaps mo) in *.
  (* [comment removed for export] *)
  assert (PH : bv_unsigned (vm_brk h) = pbrk /\ 0 < pbrk /\ pbrk < req < 2^64 /\ req <> 0
               /\ BB (set_brkph BPDead L) = BB L
               /\ gm (if req =? req then match ld_brk L with BPQueried cur => set_brkph (BPGuard cur) L | _ => match ld_brkreg L with Some (b, l) => set_brkreg (Some (b, l + PGSZ)) L | None => L end end else set_brkph BPDead L) = gm L
               /\ BB (if req =? req then match ld_brk L with BPQueried cur => set_brkph (BPGuard cur) L | _ => match ld_brkreg L with Some (b, l) => set_brkreg (Some (b, l + PGSZ)) L | None => L end end else set_brkph BPDead L) = BB L + (req - pbrk)).
  { rewrite Z.eqb_refl. destruct Hpre as [(cur & Hph & ->)|(b & l & Hph & Hreg & ->)]; rewrite Hph in P |- *.
    - destruct P as (Ecur & Ebrk & Epbrk & Hreg). unfold BB. cbn. rewrite !Hph, !Hreg. cbn. rewrite ?Hph, ?Hreg.
      rewrite (round_up_pg_aligned cur) by (rewrite Ecur; unfold PGSZ in S2; exact S2). unfold PGSZ in *. repeat split; try reflexivity; lia.
    - destruct P as (b' & l' & Hreg' & Ebrk & Epbrk). rewrite Hreg in Hreg'. inversion Hreg'; subst b' l'.
      pose proof (kl_brkreg _ _ _ HK b l Hreg) as (R1 & R2 & R3 & R4 & R5 & _). unfold BB. cbn. rewrite !Hph, !Hreg. cbn. rewrite ?Hph, ?Hreg. unfold PGSZ in *. repeat split; try reflexivity; lia. }
  destruct PH as (Ebrk & Hp0 & Hreq & NZ & BBd & GMg & BBg).
  destruct (nstep_brk_inv req mo rsp mo' evs Hst) as (r & Hok & Emo' & Ersp & _). fold h in Hok, Emo', Ersp.
  unfold event_post. rewrite (proj2 (Z.eqb_neq _ _) NZ).
  pose proof (dec_brk_Some _ _ _ _ Hd) as SH.
  destruct a.
  - (* [comment removed for export] *)
    destruct SH as [SH _].   (* [comment removed for export] *)
    rewrite Ersp in SH. assert (Er : r = Z_to_bv 64 req) by (inversion SH; reflexivity). subst r.
    destruct (brk_model_next_grown h req ltac:(lia) ltac:(lia)) as (_ & Emaps & _ & _ & _).
    pose proof (LI_gk _ _ HL) as HG. apply LI_elim in HL.
    split.
    + rewrite GMg, BBg. rewrite Emo', m_vmmaps_with_brk_next. unfold vm_live_bytes. fold h.
      rewrite Emaps, live_bytes_cons. cbn [snd]. rewrite unsigned_lit by lia. rewrite Ebrk. unfold vm_live_bytes in HL. fold h in HL. lia.
    + (* [comment removed for export] *)
      rewrite Emo', m_vmmaps_with_brk_next.
      apply (GK_cons h _ (vm_brk h, Z_to_bv 64 (req - bv_unsigned (vm_brk h))) HG Emaps); [| reflexivity| reflexivity].
      cbn [snd]. rewrite unsigned_lit by lia. rewrite Ebrk.
      destruct Hpre as [(cur & Hph & ->)|(b & l & Hph & Hreg & ->)]; rewrite Hph in P.
      * destruct P as (Ecur & Ebrk' & Epbrk & _). pose proof (round_up_pg_ge cur). unfold PGSZ in *. lia.
      * destruct P as (b' & l' & Hreg' & _ & Epbrk). rewrite Hreg in Hreg'. inversion Hreg'; subst b' l'. unfold PGSZ. lia.
  - (* [comment removed for export] *)
    rewrite Ersp in SH. unfold eff0 in SH. assert (Er : r = Z_to_bv 64 pbrk) by (inversion SH; reflexivity).
    assert (Er' : r = vm_brk h) by (rewrite Er, <- Ebrk; apply Z_to_bv_bv_unsigned). clear Er. subst r.
    destruct (brk_model_next_same h (Z_to_bv 64 req)) as (_ & Emaps & _ & _ & _).
    replace (pbrk =? req) with false by (symmetry; apply Z.eqb_neq; lia).
    apply (LI_same_vm L _ mo); [exact HL| rewrite Emo', m_vmmaps_with_brk_next; exact Emaps| reflexivity| exact BBd| rewrite Emo', m_vmmaps_with_brk_next; reflexivity| rewrite Emo', m_vmmaps_with_brk_next; reflexivity].
Qed.

Definition mm_val (x : mmap_ans) : Z := match x with MmErr e => neg_errno e | MmOk a => a end.

Lemma mm_post_eq L len prot z : prot = PROT_NONE \/ prot = PROT_RW ->
  event_post L (EMmap 0 len prot MAPF) z
  = (if is_err z then L else if prot =? PROT_NONE then set_metas ((z, len, 0) :: ld_metas L) L else set_groups ((z, len) :: ld_groups L) L).
Proof. intros _. reflexivity. Qed.

(* [comment removed for export] *)
Lemma li_mmap_core L mo mo' len z :
  LI L mo -> 0 < len < LEN_MAX ->
  ((is_err z = true /\ vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mo))
   \/ (is_err z = false /\ vm_maps (m_vmmaps mo') = (Z_to_bv 64 z, Z_to_bv 64 (mmap_len len)) :: vm_maps (m_vmmaps mo))) ->
  vm_limit (m_vmmaps mo') = vm_limit (m_vmmaps mo) -> vm_start_brk (m_vmmaps mo') = vm_start_brk (m_vmmaps mo) ->
  forall prot, prot = PROT_NONE \/ prot = PROT_RW -> LI (event_post L (EMmap 0 len prot MAPF) z) mo'.
Proof.
  intros HL Hlen CASES Elim Ebrk prot Hprot. rewrite (mm_post_eq L len prot z Hprot).
  pose proof (mmap_len_ge len ltac:(lia)) as ML. unfold LEN_MAX in Hlen.
  destruct CASES as [[-> E]|[-> E]].
  - apply (LI_same_vm L _ mo); [exact HL| exact E| reflexivity| reflexivity| exact Elim| exact Ebrk].
  - pose proof (LI_gk _ _ HL) as HG. apply LI_elim in HL. split.
    + unfold vm_live_bytes in *. rewrite E, live_bytes_cons. cbn [snd]. rewrite unsigned_lit by lia.
      destruct Hprot as [-> | ->]; cbn [Z.eqb PROT_NONE PROT_RW Pos.eqb].
      * rewrite gm_add_meta, BB_set_metas. lia.
      * rewrite gm_add_group, BB_set_groups. lia.
    + apply (GK_cons (m_vmmaps mo) _ _ HG E); [| exact Elim| exact Ebrk].
      cbn [snd]. rewrite unsigned_lit by lia. pose proof (mmap_len_aligned len) as MA. unfold PGSZ. lia.
Qed.

Lemma mmap_ok_not_err len avoid a : mmap_addr_ok len avoid a = true -> 0 < len -> is_err a = false /\ 0 <= a < 2^64.
Proof.
  intros H Hlen. unfold mmap_addr_ok in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.ltb_lt in H2. apply Z.leb_le in H3. pose proof alloc_ceiling_lt. pose proof (mmap_len_ge len Hlen).
  unfold is_err, TWO64. split; [apply Z.ltb_ge; lia| lia].
Qed.

Lemma li_mmap_rw L pbrk mo rsp mo' evs len x :
  KL L pbrk mo -> LI L mo -> 0 < len < LEN_MAX ->
  nstep (NMmap 0 len PROT_RW MAPF) mo rsp mo' evs -> dec_mmap len [] rsp = Some x ->
  LI (event_post L (EMmap 0 len PROT_RW MAPF) (mm_val x)) mo'.
Proof.
  intros HK HL Hlen Hst Hd. pose proof (mmap_len_ge len ltac:(lia)) as ML. unfold LEN_MAX in Hlen.
  destruct (nstep_dec_mmap len [] mo rsp mo' evs ltac:(lia) ltac:(lia) (kl_top _ _ _ HK) ltac:(constructor) Hst) as (_ & _ & x' & Hd' & Hx).
  rewrite Hd in Hd'. assert (x' = x) by congruence. subst x'.
  destruct x as [e|a]; cbn [mm_val].
  - destruct Hx as [-> ->]. apply (li_mmap_core L mo mo len _ HL ltac:(unfold LEN_MAX; lia)); [| reflexivity| reflexivity| right; reflexivity].
    left. split; [apply is_err_neg; unfold ENOMEM; lia| reflexivity].
  - destruct Hx as (Hok & _ & _ & E).
    apply (li_mmap_core L mo mo' len _ HL ltac:(unfold LEN_MAX; lia)); [| rewrite E; reflexivity| rewrite E; reflexivity| right; reflexivity].
    right. destruct (mmap_ok_not_err _ _ _ Hok ltac:(lia)) as [NE Ha]. split; [exact NE|]. rewrite E. reflexivity.
Qed.

Lemma li_mmap_none L pbrk mo rsp mo' evs len x :
  KL L pbrk mo -> LI L mo -> 0 < len < LEN_MAX ->
  nstep (NMmap 0 len PROT_NONE MAPF) mo rsp mo' evs -> dec_mmap_none len [] rsp = Some x ->
  LI (event_post L (EMmap 0 len PROT_NONE MAPF) (mm_val x)) mo'.
Proof.
  intros HK HL Hlen Hst Hd. pose proof (mmap_len_ge len ltac:(lia)) as ML. unfold LEN_MAX in Hlen.
  destruct (nstep_dec_mmap_none len [] mo rsp mo' evs ltac:(lia) ltac:(lia) (kl_top _ _ _ HK) ltac:(constructor) Hst) as (_ & _ & x' & Hd' & Hx).
  rewrite Hd in Hd'. assert (x' = x) by congruence. subst x'.
  destruct x as [e|a]; cbn [mm_val].
  - destruct Hx as [-> ->]. apply (li_mmap_core L mo mo len _ HL ltac:(unfold LEN_MAX; lia)); [| reflexivity| reflexivity| left; reflexivity].
    left. split; [apply is_err_neg; unfold ENOMEM; lia| reflexivity].
  - destruct Hx as (Hok & _ & E).
    apply (li_mmap_core L mo mo' len _ HL ltac:(unfold LEN_MAX; lia)); [| rewrite E; reflexivity| rewrite E; reflexivity| left; reflexivity].
    right. destruct (mmap_ok_not_err _ _ _ Hok ltac:(lia)) as [NE Ha]. split; [exact NE|]. rewrite E. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma li_mmap_fixed L pbrk mo rsp mo' evs cur z :
  KL L pbrk mo -> LI L mo -> ld_brk L = BPGuard cur ->
  nstep (NMmap (round_up_pg cur) PGSZ PROT_NONE MAPFX) mo rsp mo' evs ->
  LI (event_post L (EMmap (round_up_pg cur) PGSZ PROT_NONE MAPFX) z) mo'.
Proof.
  intros HK HL Hph Hst. pose proof alloc_ceiling_lt as Hcl.
  pose proof (kl_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as (Ecur & Ebrk & Epbrk & Ereg & Hceil & (e0 & He0 & He0l & He0h) & Dg & Dm).
  pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4).
  set (a := round_up_pg cur) in *.
  assert (Ha : a = cur). { subst a. apply round_up_pg_aligned. rewrite Ecur. exact S2. }
  set (h := m_vmmaps mo) in *. set (aw := Z_to_bv 64 a). set (nw := Z_to_bv 64 PGSZ).
  assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia).
  assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia).
  assert (Uhi : bv_unsigned (aw + nw)%bv = a + PGSZ).
  { rewrite bv_add_unsigned, Ua, Un. apply bv_wrap_small. unfold bv_modulus, PGSZ in *. lia. }
  assert (Hrf : region_free (vm_reserved h) aw nw = true).
  { apply region_free_above. intros e He. rewrite Ua, Ha, Ecur. apply (kl_resv_top _ _ _ HK). exact He. }
  assert (Hmc : map_contains (vm_maps h) aw nw = true).
  { unfold map_contains. apply existsb_exists. exists e0. split; [exact He0|]. rewrite Ua, Un. unfold elo, ehi in *.
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by (unfold PGSZ in *; lia). reflexivity. }
  pose proof (nstep_mmap_fixed_inv a mo rsp mo' evs (kl_top _ _ _ HK) ltac:(lia) ltac:(lia) ltac:(rewrite Ha, Ecur; exact S2) Hrf Hmc Hst) as (_ & _ & x & Hd & Hx).
  fold h aw nw in Hx.
  assert (POST : event_post L (EMmap a PGSZ PROT_NONE MAPFX) z = set_brkph BPLive (set_brkreg (Some (a, 2 * PGSZ)) L)) by reflexivity.
  rewrite POST. pose proof (LI_gk _ _ HL) as HG. split.
  { rewrite gm_set_brkph, gm_set_brkreg.
  assert (E2 : BB (set_brkph BPLive (set_brkreg (Some (a, 2 * PGSZ)) L)) = 2 * PGSZ) by reflexivity. rewrite E2.
  apply LI_elim in HL. unfold BB in HL. rewrite Hph in HL.
  assert (LE : vm_live_bytes (m_vmmaps mo') <= vm_live_bytes h).
  { unfold vm_live_bytes. destruct x as [e| |e].
    - destruct Hx.   (* [comment removed for export] *)
    - rewrite Hx. cbn [vm_maps]. lia.
    - destruct Hx. }
  subst h. lia. }
  (* [comment removed for export] *)
  destruct x as [e| |e].
  - destruct Hx.
  - rewrite Hx. apply (GK_ext h); [exact HG| apply incl_refl| reflexivity| reflexivity].
  - destruct Hx.
Qed.

(* [comment removed for export] *)
Lemma nstep_munmap_exact a len l0 mo rsp mo' evs :
  let h := m_vmmaps mo in let aw := Z_to_bv 64 a in let nw := Z_to_bv 64 (mmap_len l0) in
  0 < a -> a mod PGSZ = 0 -> 0 < l0 -> a + mmap_len l0 <= alloc_ceiling -> 0 < len < 2^64 -> mmap_len len = mmap_len l0 ->
  In (aw, nw) (vm_maps h) ->
  nstep (NMunmap a len) mo rsp mo' evs ->
  vm_maps (m_vmmaps mo') = map_remove (vm_maps h) aw
  /\ vm_limit (m_vmmaps mo') = vm_limit h /\ vm_start_brk (m_vmmaps mo') = vm_start_brk h.   (* [comment removed for export] *)
Proof.
  intros h aw nw Ha Hal Hl0 Hceil Hlen Hmm Hin Hst. pose proof alloc_ceiling_lt as Hcl. pose proof (mmap_len_ge l0 Hl0) as ML.
  apply nstep_munmap_chk in Hst. destruct rsp as [r ws zs us cs ci]. unfold check_munmap in Hst.
  fold h in Hst. rewrite (unsigned_lit a) in Hst by lia. rewrite page_size_eq in Hst. unfold PGSZ in Hal. rewrite Hal in Hst.
  rewrite w_is0_lit in Hst by lia. replace (len =? 0) with false in Hst by (symmetry; apply Z.eqb_neq; lia). cbn [negb orb Z.eqb] in Hst.
  cbv zeta in Hst. rewrite (unsigned_lit len) in Hst by lia. fold (mmap_len len) in Hst. rewrite Hmm in Hst. fold aw nw in Hst.
  replace (TASK_SIZE <? a + mmap_len l0) with false in Hst by (symmetry; apply Z.ltb_ge; ceil_bounds; unfold TASK_SIZE; lia).
  assert (Hhas : map_has (vm_maps h) aw nw = true).
  { unfold map_has. apply existsb_exists. exists (aw, nw). split; [exact Hin|]. cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity. }
  rewrite Hhas in Hst. destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  destruct (w_is0 r && listNN_eqb us [(aw, nw)]); [|discriminate]. inversion Hst; subst. rewrite m_vmmaps_with_mmap_destroyed. split; [|split]; reflexivity.
Qed.

Lemma li_munmap L pbrk mo rsp mo' evs a l0 len z :
  KL L pbrk mo -> LI L mo -> In (a, l0) (ld_groups L) -> (len = l0 \/ len = round_up_pg l0) ->
  nstep (NMunmap a len) mo rsp mo' evs ->
  LI (event_post L (EMunmap a len) z) mo'.
Proof.
  intros HK HL Hin Hlen Hst. pose proof alloc_ceiling_lt as Hcl.
  pose proof (kl_groups _ _ _ HK a l0 Hin) as (A1 & A2 & A3 & A4 & A5 & A6). unfold LEN_MAX in A1.
  pose proof (mmap_len_ge l0 ltac:(lia)) as ML.
  assert (Hnn : mmap_len (mmap_len l0) = mmap_len l0) by (apply mmap_len_of_aligned; [lia| apply mmap_len_aligned]).
  rewrite round_up_pg_eq in Hlen. fold (mmap_len l0) in Hlen.
  assert (Hlen3 : 0 < len < 2^64 /\ mmap_len len = mmap_len l0).
  { destruct Hlen as [-> | ->]; [split; [lia| reflexivity]| split; [lia| exact Hnn]]. }
  destruct Hlen3 as [Hlen1 Hlen2].
  pose proof (nstep_munmap_exact a len l0 mo rsp mo' evs A2 ltac:(unfold PGSZ in A3; exact A3) ltac:(lia) A4 Hlen1 Hlen2 A5 Hst) as (Emaps & Elim & Ebrk).
  unfold went, wz in A5. pose proof (LI_gk _ _ HL) as HG. split.
  { unfold vm_live_bytes. rewrite Emaps, (live_bytes_remove _ _ _ (kl_wf _ _ _ HK) A5).
  change (event_post L (EMunmap a len) z) with (set_groups (g_remove a (ld_groups L)) L).
  rewrite (gm_remove_group L pbrk mo a l0 HK Hin), BB_set_groups. rewrite unsigned_lit by lia.
  apply LI_elim in HL. unfold vm_live_bytes in HL. lia. }
  (* [comment removed for export] *)
  apply (GK_ext (m_vmmaps mo)); [exact HG| rewrite Emaps; intros y Hy; apply filter_In in Hy; exact (proj1 Hy)| |].
  - exact Elim.
  - exact Ebrk.
Qed.

(* [comment removed for export] *)
Lemma li_mprotect L pbrk mo rsp mo' evs b l k z :
  KL L pbrk mo -> LI L mo -> In (b, l, k) (ld_metas L) -> (2 + k) * PGSZ <= round_up_pg l ->
  nstep (NMprotect (b + (1 + k) * PGSZ) PGSZ PROT_RW) mo rsp mo' evs ->
  LI (event_post L (EMprotect (b + (1 + k) * PGSZ) PGSZ PROT_RW) z) mo'.
Proof.
  intros HK HL Hin Hk Hst. pose proof alloc_ceiling_lt as Hcl.
  pose proof (kl_metas _ _ _ HK b l k Hin) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). unfold LEN_MAX in A1.
  rewrite round_up_pg_eq in Hk. fold (mmap_len l) in Hk.
  destruct (nstep_dec_mprotect (b + (1 + k) * PGSZ) PGSZ mo rsp mo' evs ltac:(unfold PGSZ in *; lia) ltac:(unfold PGSZ; lia) ltac:(vm_compute; reflexivity) Hst) as (_ & _ & x & _ & Hx).
  assert (Emaps : vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mo)).
  { destruct x as [e|[|]]; [destruct Hx as [_ ->]; reflexivity| destruct Hx as (_ & _ & _ & E); rewrite E; reflexivity| rewrite Hx; reflexivity]. }
  assert (Ekeep : vm_limit (m_vmmaps mo') = vm_limit (m_vmmaps mo) /\ vm_start_brk (m_vmmaps mo') = vm_start_brk (m_vmmaps mo)).
  { destruct x as [e|[|]]; [destruct Hx as [_ ->]; split; reflexivity| destruct Hx as (_ & _ & _ & E); rewrite E; split; reflexivity| rewrite Hx; split; reflexivity]. }
  apply (LI_same_vm L _ mo); [exact HL| exact Emaps| | | exact (proj1 Ekeep)| exact (proj2 Ekeep)];
    unfold event_post; destruct (mprotect_answer_ok z && _) eqn:E || destruct ((z =? 0) || (z =? TWO64 - ENOSYS)); rewrite ?gm_bump; reflexivity.
Qed.

End WithCeiling.
