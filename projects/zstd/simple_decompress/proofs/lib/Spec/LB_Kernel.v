(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad MSafe STree Malloc Prog KInv KStep KLink KEv.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

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

Definition LI (L : mled) (mo : Model) : Prop := vm_live_bytes (m_vmmaps mo) <= gm L + BB L.

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
Lemma live_bytes_iv_subtract a sz lo hi : 0 <= lo -> lo <= hi -> hi < 2^64 ->
  live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz.
Proof.
  intros Hlo Hlh Hhi. pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 sz) as Rs. unfold bv_modulus in *.
  unfold iv_subtract.
  destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn;
    rewrite ?unsigned_lit; try lia.
Qed.

Lemma live_bytes_subtract maps lo hi : 0 <= lo -> lo <= hi -> hi < 2^64 -> live_bytes (maps_subtract maps lo hi) <= live_bytes maps.
Proof.
  intros H1 H2 H3. induction maps as [|[a sz] l IH]; cbn; [lia|]. rewrite live_bytes_app. pose proof (live_bytes_iv_subtract a sz lo hi H1 H2 H3). lia.
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

Lemma LI_intro L mo : vm_live_bytes (m_vmmaps mo) <= gm L + BB L -> LI L mo. Proof. intros H. exact H. Qed.
Lemma LI_elim L mo : LI L mo -> vm_live_bytes (m_vmmaps mo) <= gm L + BB L. Proof. intros H. exact H. Qed.

Lemma LI_same_vm L L' mo mo' : LI L mo -> vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mo) -> gm L' = gm L -> BB L' = BB L -> LI L' mo'.
Proof. intros H E1 E2 E3. unfold LI, vm_live_bytes in *. rewrite E1, E2, E3. exact H. Qed.

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
  apply (LI_same_vm L _ mo); [exact HL| rewrite with_brk_next_noshrink by lia; rewrite m_vmmaps_with_vmmaps; exact E2| reflexivity|]. unfold BB. cbn. rewrite Hreg, Hph. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma li_brk_grow L pbrk mo rsp mo' evs req a :
  KL L pbrk mo -> LI L mo ->
  ((exists cur, ld_brk L = BPQueried cur /\ req = round_up_pg cur + 2 * PGSZ)
   \/ (exists b l, ld_brk L = BPLive /\ ld_brkreg L = Some (b, l) /\ req = b + l + PGSZ)) ->
  nstep (NBrk req) mo rsp mo' evs -> dec_brk pbrk req rsp = Some a ->
  LI (event_post L (EBrk req) (match a with BrkGrown => req | BrkSame => pbrk end)) mo'.
Proof.
  intros HK HL Hpre Hst Hd. pose proof (KL_atop_lt _ _ _ HK) as Hcl.
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
  pose proof (dec_brk_Some _ _ _ _ Hd) as (ci & SH).
  destruct a.
  - (* [comment removed for export] *)
    rewrite Ersp in SH. assert (Er : r = Z_to_bv 64 req) by (inversion SH; reflexivity). subst r.
    destruct (brk_model_next_grown h req ltac:(lia) ltac:(lia)) as (_ & Emaps & _ & _ & _).
    unfold LI. rewrite GMg, BBg. rewrite Emo', with_brk_next_noshrink by (rewrite unsigned_lit by lia; fold h; lia). rewrite m_vmmaps_with_vmmaps. unfold vm_live_bytes. fold h.
    rewrite Emaps, live_bytes_cons. cbn [snd]. rewrite unsigned_lit by lia. rewrite Ebrk. apply LI_elim in HL. unfold vm_live_bytes in HL. fold h in HL. lia.
  - (* [comment removed for export] *)
    rewrite Ersp in SH. unfold eff0_ci in SH. assert (Er : r = Z_to_bv 64 pbrk) by (inversion SH; reflexivity).
    assert (Er' : r = vm_brk h) by (rewrite Er, <- Ebrk; apply Z_to_bv_bv_unsigned). clear Er. subst r.
    destruct (brk_model_next_same h (Z_to_bv 64 req)) as (_ & Emaps & _ & _ & _).
    replace (pbrk =? req) with false by (symmetry; apply Z.eqb_neq; lia).
    apply (LI_same_vm L _ mo); [exact HL| rewrite Emo', with_brk_next_noshrink by (fold h; lia); rewrite m_vmmaps_with_vmmaps; exact Emaps| reflexivity| exact BBd].
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
  forall prot, prot = PROT_NONE \/ prot = PROT_RW -> LI (event_post L (EMmap 0 len prot MAPF) z) mo'.
Proof.
  intros HL Hlen CASES prot Hprot. rewrite (mm_post_eq L len prot z Hprot).
  pose proof (mmap_len_ge len ltac:(lia)) as ML. unfold LEN_MAX in Hlen.
  destruct CASES as [[-> E]|[-> E]].
  - apply (LI_same_vm L _ mo); [exact HL| exact E| reflexivity| reflexivity].
  - unfold LI, vm_live_bytes in *. rewrite E, live_bytes_cons. cbn [snd]. rewrite unsigned_lit by lia.
    destruct Hprot as [-> | ->]; cbn [Z.eqb PROT_NONE PROT_RW Pos.eqb].
    + rewrite gm_add_meta, BB_set_metas. lia.
    + rewrite gm_add_group, BB_set_groups. lia.
Qed.

Lemma mmap_ok_not_err atop len avoid a : mmap_addr_ok atop len avoid a = true -> 0 < len -> atop < 2^63 -> is_err a = false /\ 0 <= a < 2^64.
Proof.
  intros H Hlen Hat. unfold mmap_addr_ok in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.ltb_lt in H2. apply Z.leb_le in H3. pose proof (mmap_len_ge len Hlen).
  unfold is_err, TWO64. split; [apply Z.ltb_ge; lia| lia].
Qed.

Lemma li_mmap_rw L pbrk mo rsp mo' evs len x :
  KL L pbrk mo -> LI L mo -> 0 < len < LEN_MAX ->
  nstep (NMmap 0 len PROT_RW MAPF) mo rsp mo' evs -> dec_mmap (ld_atop L) len [] rsp = Some x ->
  LI (event_post L (EMmap 0 len PROT_RW MAPF) (mm_val x)) mo'.
Proof.
  intros HK HL Hlen Hst Hd. pose proof (mmap_len_ge len ltac:(lia)) as ML. unfold LEN_MAX in Hlen.
  destruct (nstep_dec_mmap (ld_atop L) len [] mo rsp mo' evs ltac:(lia) ltac:(lia) ltac:(constructor) ltac:(rewrite (kl_atop _ _ _ HK); lia) Hst) as (_ & _ & x' & Hd' & Hx).
  rewrite Hd in Hd'. assert (x' = x) by congruence. subst x'.
  apply (li_mmap_core L mo mo' len (mm_val x) HL ltac:(unfold LEN_MAX; lia)); [| right; reflexivity].
  destruct x as [e|a]; cbn [mm_val].
  - destruct Hx as [-> ->]. left. split; [apply is_err_neg; unfold ENOMEM; lia| reflexivity].
  - destruct Hx as (Hok & _ & E). right. destruct (mmap_ok_not_err _ _ _ _ Hok ltac:(lia) (proj2 (KL_atop_lt _ _ _ HK))) as [NE Ha]. split; [exact NE|]. rewrite E. reflexivity.
Qed.

Lemma li_mmap_none L pbrk mo rsp mo' evs len x :
  KL L pbrk mo -> LI L mo -> 0 < len < LEN_MAX ->
  nstep (NMmap 0 len PROT_NONE MAPF) mo rsp mo' evs -> dec_mmap_none (ld_atop L) len [] rsp = Some x ->
  LI (event_post L (EMmap 0 len PROT_NONE MAPF) (mm_val x)) mo'.
Proof.
  intros HK HL Hlen Hst Hd. pose proof (mmap_len_ge len ltac:(lia)) as ML. unfold LEN_MAX in Hlen.
  destruct (nstep_dec_mmap_none (ld_atop L) len [] mo rsp mo' evs ltac:(lia) ltac:(lia) ltac:(constructor) ltac:(rewrite (kl_atop _ _ _ HK); lia) Hst) as (_ & _ & x' & Hd' & Hx).
  rewrite Hd in Hd'. assert (x' = x) by congruence. subst x'.
  apply (li_mmap_core L mo mo' len (mm_val x) HL ltac:(unfold LEN_MAX; lia)); [| left; reflexivity].
  destruct x as [e|a]; cbn [mm_val].
  - destruct Hx as [-> ->]. left. split; [apply is_err_neg; unfold ENOMEM; lia| reflexivity].
  - destruct Hx as (Hok & _ & E). right. destruct (mmap_ok_not_err _ _ _ _ Hok ltac:(lia) (proj2 (KL_atop_lt _ _ _ HK))) as [NE Ha]. split; [exact NE|]. rewrite E. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma li_mmap_fixed L pbrk mo rsp mo' evs cur z :
  KL L pbrk mo -> LI L mo -> ld_brk L = BPGuard cur ->
  nstep (NMmap (round_up_pg cur) PGSZ PROT_NONE MAPFX) mo rsp mo' evs ->
  LI (event_post L (EMmap (round_up_pg cur) PGSZ PROT_NONE MAPFX) z) mo'.
Proof.
  intros HK HL Hph Hst. pose proof (KL_atop_lt _ _ _ HK) as Hcl. pose proof (kl_atop _ _ _ HK) as HKtop.
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
  pose proof (nstep_mmap_fixed_inv a mo rsp mo' evs ltac:(lia) ltac:(unfold h; rewrite <- HKtop; lia) ltac:(rewrite Ha, Ecur; exact S2) Hrf Hmc Hst) as (_ & _ & x & Hd & Hx).
  fold h aw nw in Hx.
  assert (POST : event_post L (EMmap a PGSZ PROT_NONE MAPFX) z = set_brkph BPLive (set_brkreg (Some (a, 2 * PGSZ)) L)) by reflexivity.
  rewrite POST. unfold LI. rewrite gm_set_brkph, gm_set_brkreg.
  assert (E2 : BB (set_brkph BPLive (set_brkreg (Some (a, 2 * PGSZ)) L)) = 2 * PGSZ) by reflexivity. rewrite E2.
  apply LI_elim in HL. unfold BB in HL. rewrite Hph in HL.
  assert (LE : vm_live_bytes (m_vmmaps mo') <= vm_live_bytes h).
  { unfold vm_live_bytes. destruct x as [e| |e].
    - destruct Hx as [_ ->]. subst h. lia.
    - rewrite Hx. cbn [vm_maps]. lia.
    - destruct Hx as [_ E]. rewrite E. cbn [vm_maps]. apply live_bytes_subtract; unfold PGSZ in *; lia. }
  subst h. lia.
Qed.

(* [comment removed for export] *)
Lemma nstep_munmap_exact a len l0 mo rsp mo' evs :
  let h := m_vmmaps mo in let aw := Z_to_bv 64 a in let nw := Z_to_bv 64 (mmap_len l0) in
  0 < a -> a mod PGSZ = 0 -> 0 < l0 -> a + mmap_len l0 <= alloc_ceiling -> 0 < len < 2^64 -> mmap_len len = mmap_len l0 ->
  In (aw, nw) (vm_maps h) ->
  nstep (NMunmap a len) mo rsp mo' evs ->
  vm_maps (m_vmmaps mo') = map_remove (vm_maps h) aw.
Proof.
  intros h aw nw Ha Hal Hl0 Hceil Hlen Hmm Hin Hst. pose proof alloc_ceiling_lt as Hcl. pose proof (mmap_len_ge l0 Hl0) as ML.
  apply nstep_munmap_iff in Hst. destruct rsp as [r ws zs us cs ci]. unfold check_munmap in Hst.
  fold h in Hst. rewrite (unsigned_lit a) in Hst by lia. rewrite page_size_eq in Hst. unfold PGSZ in Hal. rewrite Hal in Hst.
  rewrite w_is0_lit in Hst by lia. replace (len =? 0) with false in Hst by (symmetry; apply Z.eqb_neq; lia). cbn [negb orb Z.eqb] in Hst.
  cbv zeta in Hst. rewrite (unsigned_lit len) in Hst by lia. fold (mmap_len len) in Hst. rewrite Hmm in Hst. fold aw nw in Hst.
  assert (Hhas : map_has (vm_maps h) aw nw = true).
  { unfold map_has. apply existsb_exists. exists (aw, nw). split; [exact Hin|]. cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity. }
  (* [comment removed for export] *)
  replace (TASK_SIZE <? a + mmap_len l0) with false in Hst by (symmetry; apply Z.ltb_ge; rewrite (proj2 (proj2 (proj2 max_write_lt))); rewrite alloc_ceiling_val in Hceil; lia).
  rewrite Hhas in Hst. destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
  destruct (w_is0 r && listNN_eqb us [(aw, nw)]); [|discriminate]. injection Hst as <-. rewrite m_vmmaps_with_mmap_destroyed. reflexivity.
Qed.

Lemma li_munmap L pbrk mo rsp mo' evs a l0 len z :
  KL L pbrk mo -> LI L mo -> In (a, l0) (ld_groups L) -> (len = l0 \/ len = round_up_pg l0) ->
  nstep (NMunmap a len) mo rsp mo' evs ->
  LI (event_post L (EMunmap a len) z) mo'.
Proof.
  intros HK HL Hin Hlen Hst. pose proof alloc_ceiling_lt as Hcl. pose proof (KL_atop_range _ _ _ HK) as HKat.
  pose proof (kl_groups _ _ _ HK a l0 Hin) as (A1 & A2 & A3 & A4 & A5 & A6). unfold LEN_MAX in A1.
  pose proof (mmap_len_ge l0 ltac:(lia)) as ML.
  assert (Hnn : mmap_len (mmap_len l0) = mmap_len l0) by (apply mmap_len_of_aligned; [lia| apply mmap_len_aligned]).
  rewrite round_up_pg_eq in Hlen. fold (mmap_len l0) in Hlen.
  assert (Hlen3 : 0 < len < 2^64 /\ mmap_len len = mmap_len l0).
  { destruct Hlen as [-> | ->]; [split; [lia| reflexivity]| split; [lia| exact Hnn]]. }
  destruct Hlen3 as [Hlen1 Hlen2].
  pose proof (nstep_munmap_exact a len l0 mo rsp mo' evs A2 ltac:(unfold PGSZ in A3; exact A3) ltac:(lia) ltac:(lia) Hlen1 Hlen2 A5 Hst) as Emaps.
  unfold went, wz in A5. unfold LI, vm_live_bytes. rewrite Emaps, (live_bytes_remove _ _ _ (kl_wf _ _ _ HK) A5).
  change (event_post L (EMunmap a len) z) with (set_groups (g_remove a (ld_groups L)) L).
  rewrite (gm_remove_group L pbrk mo a l0 HK Hin), BB_set_groups. rewrite unsigned_lit by lia.
  apply LI_elim in HL. unfold vm_live_bytes in HL. lia.
Qed.

(* [comment removed for export] *)
Lemma li_mprotect L pbrk mo rsp mo' evs b l k z :
  KL L pbrk mo -> LI L mo -> In (b, l, k) (ld_metas L) -> (2 + k) * PGSZ <= round_up_pg l ->
  nstep (NMprotect (b + (1 + k) * PGSZ) PGSZ PROT_RW) mo rsp mo' evs ->
  LI (event_post L (EMprotect (b + (1 + k) * PGSZ) PGSZ PROT_RW) z) mo'.
Proof.
  intros HK HL Hin Hk Hst. pose proof alloc_ceiling_lt as Hcl. pose proof (KL_atop_range _ _ _ HK) as HKat.
  pose proof (kl_metas _ _ _ HK b l k Hin) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). unfold LEN_MAX in A1.
  rewrite round_up_pg_eq in Hk. fold (mmap_len l) in Hk.
  destruct (nstep_dec_mprotect (b + (1 + k) * PGSZ) PGSZ mo rsp mo' evs ltac:(unfold PGSZ in *; lia) ltac:(unfold PGSZ; lia) ltac:(vm_compute; reflexivity) Hst) as (_ & _ & x & _ & Hx).
  assert (Emaps : vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mo)).
  { destruct x as [e|[|]]; [destruct Hx as [_ ->]; reflexivity| destruct Hx as (_ & _ & E); rewrite E; reflexivity| rewrite Hx; reflexivity]. }
  apply (LI_same_vm L _ mo); [exact HL| exact Emaps| |]; unfold event_post; destruct (mprotect_answer_ok z && _) eqn:E || destruct ((z =? 0) || (z =? TWO64 - ENOSYS)); rewrite ?gm_bump; reflexivity.
Qed.

