(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import PropExec MState ITree Nodes Decode NodesMM.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import Prelim Monad MSafe STree Malloc Prog KInv KStep KLink.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Definition gm (L : mled) : Z :=
  fold_right Z.add 0 (map (fun g : Z * Z => mmap_len (snd g)) (ld_groups L))
  + fold_right Z.add 0 (map (fun m : Z * Z * Z => mmap_len (snd (fst m))) (ld_metas L)).

Definition BB (L : mled) : Z :=
  match ld_brk L with
  | BPGuard _ => 2 * PGSZ
  | _ => match ld_brkreg L with Some (_, l) => l | None => 0 end
  end.

Definition gc (L : mled) : Z := Z.of_nat (length (ld_groups L)) + Z.of_nat (length (ld_metas L)).

Definition CB (L : mled) : Z :=
  match ld_brk L with
  | BPUntried | BPQueried _ => 0
  | BPGuard _ => 1
  | _ => match ld_brkreg L with Some (_, l) => l / PGSZ | None => 0 end
  end.

Definition nmaps (mo : Model) : Z := Z.of_nat (length (vm_maps (m_vmmaps mo))).

Definition LI (L : mled) (mo : Model) : Prop :=
  vm_live_bytes (m_vmmaps mo) <= gm L + BB L /\ nmaps mo <= gc L + CB L.

Lemma live_bytes_cons e l : live_bytes (e :: l) = bv_unsigned (snd e) + live_bytes l.
Proof. destruct e; reflexivity. Qed.

Lemma live_bytes_app l1 l2 : live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a n] l1 IH]; cbn; [reflexivity| rewrite IH; lia]. Qed.

Lemma length_filter_le {A} (f : A -> bool) l : (length (List.filter f l) <= length l)%nat.
Proof. induction l as [|x l IH]; cbn; [lia|]. destruct (f x); cbn; lia. Qed.

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

Lemma length_remove_In maps aw nw : In (aw, nw) maps -> (length (map_remove maps aw) + 1 <= length maps)%nat.
Proof.
  unfold map_remove. induction maps as [|[a n] l IH]; intros Hin; [destruct Hin|]. cbn [List.filter fst].
  destruct Hin as [E|Hin].
  - injection E as -> ->. rewrite bv_eqb_refl. cbn [negb length]. pose proof (length_filter_le (fun e : word * word => negb (bv_eqb (fst e) aw)) l). lia.
  - specialize (IH Hin). destruct (bv_eqb a aw); cbn [negb length]; lia.
Qed.

Lemma live_bytes_iv_subtract a sz lo hi : lo <= hi -> 0 <= lo -> hi <= 2^64 ->
  live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz.
Proof.
  intros Hlh Hlo Hhi. pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 sz) as Rs. unfold bv_modulus in *.
  unfold iv_subtract.
  destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn;
    rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; try lia;
    try pose proof (Z.mod_le (Z.min (bv_unsigned sz) (lo - bv_unsigned a)) (2 ^ 64%N) ltac:(lia) ltac:(lia));
    try pose proof (Z.mod_le (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi) (2 ^ 64%N) ltac:(lia) ltac:(lia)); lia.
Qed.

Lemma live_bytes_subtract maps lo hi : lo <= hi -> 0 <= lo -> hi <= 2^64 -> live_bytes (maps_subtract maps lo hi) <= live_bytes maps.
Proof.
  intros H H0 H1. induction maps as [|[a sz] l IH]; cbn; [lia|]. rewrite live_bytes_app. pose proof (live_bytes_iv_subtract a sz lo hi H H0 H1). lia.
Qed.

Lemma length_iv_subtract a sz lo hi :
  length (iv_subtract a sz lo hi) = ((if (bv_unsigned a <? lo)%Z then 1 else 0) + (if (hi <? bv_unsigned a + bv_unsigned sz)%Z then 1 else 0))%nat.
Proof. unfold iv_subtract. destruct (bv_unsigned a <? lo)%Z; destruct (hi <? bv_unsigned a + bv_unsigned sz)%Z; reflexivity. Qed.

Lemma length_maps_subtract maps lo hi : vmwf maps -> lo < hi ->
  (length (maps_subtract maps lo hi) <= length maps + 1)%nat.
Proof.
  intros [Hne Hpw] Hlh.

  enough (G : (length (maps_subtract maps lo hi) <= length maps + (if existsb (fun e : word * word => ((bv_unsigned (fst e) <? lo) && (hi <? bv_unsigned (fst e) + bv_unsigned (snd e)))%Z) maps then 1 else 0))%nat).
  { destruct (existsb _ maps); lia. }
  induction maps as [|[a sz] l IH]; [cbn; lia|].
  inversion Hpw as [|e0 l0 Hd Hpw']; subst.
  assert (Hne' : forall e, In e l -> elo e < ehi e <= 2 ^ 64) by (intros e He; apply Hne; right; exact He).
  specialize (IH Hne' Hpw').
  cbn [maps_subtract existsb fst snd length]. rewrite length_app, length_iv_subtract.
  destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn [andb orb].
  2:{ destruct (existsb _ l); lia. }
  2:{ destruct (existsb _ l); lia. }
  2:{ destruct (existsb _ l); lia. }

  enough (EXF : existsb (fun e : word * word => ((bv_unsigned (fst e) <? lo) && (hi <? bv_unsigned (fst e) + bv_unsigned (snd e)))%Z) l = false) by (rewrite EXF in IH; lia).
  apply Bool.not_true_iff_false. intros EX. apply existsb_exists in EX as ([a' sz'] & Hin & Hb). cbn [fst snd] in Hb.
  apply andb_prop in Hb as [B1 B2]. apply Z.ltb_lt in B1. apply Z.ltb_lt in B2.
  specialize (Hd _ Hin). unfold edisj, elo, ehi in Hd. cbn in Hd. lia.
Qed.

Lemma gm_set_brkph ph L : gm (set_brkph ph L) = gm L. Proof. reflexivity. Qed.
Lemma gm_set_brkreg v L : gm (set_brkreg v L) = gm L. Proof. reflexivity. Qed.

Lemma gm_add_group a len L : gm (set_groups ((a, len) :: ld_groups L) L) = gm L + mmap_len len.
Proof. unfold gm. cbn. lia. Qed.
Lemma gm_add_meta a len L : gm (set_metas ((a, len, 0) :: ld_metas L) L) = gm L + mmap_len len.
Proof. unfold gm. cbn. lia. Qed.
Lemma BB_set_groups v L : BB (set_groups v L) = BB L. Proof. reflexivity. Qed.
Lemma BB_set_metas v L : BB (set_metas v L) = BB L. Proof. reflexivity. Qed.
Lemma gc_set_brkph ph L : gc (set_brkph ph L) = gc L. Proof. reflexivity. Qed.
Lemma gc_set_brkreg v L : gc (set_brkreg v L) = gc L. Proof. reflexivity. Qed.

Lemma gc_add_group a len L : gc (set_groups ((a, len) :: ld_groups L) L) = gc L + 1.
Proof. unfold gc. cbn [ld_groups ld_metas set_groups length]. lia. Qed.
Lemma gc_add_meta a len L : gc (set_metas ((a, len, 0) :: ld_metas L) L) = gc L + 1.
Proof. unfold gc. cbn [ld_groups ld_metas set_metas length]. lia. Qed.
Lemma CB_set_groups v L : CB (set_groups v L) = CB L. Proof. reflexivity. Qed.
Lemma CB_set_metas v L : CB (set_metas v L) = CB L. Proof. reflexivity. Qed.

Lemma sum_map_app {A} (f : A -> Z) l1 l2 : fold_right Z.add 0 (map f (l1 ++ l2)) = fold_right Z.add 0 (map f l1) + fold_right Z.add 0 (map f l2).
Proof. induction l1 as [|x l1 IH]; cbn; [lia| rewrite IH; lia]. Qed.

Lemma gm_remove_group L pbrk mo a l0 : KL L pbrk mo -> In (a, l0) (ld_groups L) ->
  gm (set_groups (g_remove a (ld_groups L)) L) = gm L - mmap_len l0.
Proof.
  intros HK Hin. destruct (g_remove_split a l0 (ld_groups L) _ Hin (kl_distinct _ _ _ HK)) as (g1 & g2 & Eg & Ezz).
  unfold gm. cbn [ld_groups ld_metas set_groups]. rewrite Ezz, Eg, !sum_map_app. cbn. lia.
Qed.

Lemma gc_remove_group L pbrk mo a l0 : KL L pbrk mo -> In (a, l0) (ld_groups L) ->
  gc (set_groups (g_remove a (ld_groups L)) L) = gc L - 1.
Proof.
  intros HK Hin. destruct (g_remove_split a l0 (ld_groups L) _ Hin (kl_distinct _ _ _ HK)) as (g1 & g2 & Eg & Ezz).
  unfold gc. cbn [ld_groups ld_metas set_groups]. rewrite Ezz, Eg, !length_app. cbn [length]. lia.
Qed.

Lemma gm_bump a L : gm (set_metas (map (bump_meta a) (ld_metas L)) L) = gm L.
Proof.
  unfold gm. cbn [ld_groups ld_metas set_metas]. f_equal.
  induction (ld_metas L) as [|[[b l] k] ms IH]; cbn; [reflexivity|]. rewrite IH. unfold bump_meta. destruct (b + (1 + k) * PGSZ =? a); reflexivity.
Qed.
Lemma gc_bump a L : gc (set_metas (map (bump_meta a) (ld_metas L)) L) = gc L.
Proof. unfold gc. cbn [ld_groups ld_metas set_metas]. rewrite length_map. reflexivity. Qed.

Lemma LI_elim L mo : LI L mo -> vm_live_bytes (m_vmmaps mo) <= gm L + BB L. Proof. intros [H _]. exact H. Qed.
Lemma LI_count L mo : LI L mo -> nmaps mo <= gc L + CB L. Proof. intros [_ H]. exact H. Qed.

Lemma LI_same_vm L L' mo mo' : LI L mo -> vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mo) -> gm L' = gm L -> BB L' = BB L ->
  gc L' = gc L -> CB L <= CB L' -> LI L' mo'.
Proof. intros [H1 H2] E1 E2 E3 E4 E5. unfold LI, vm_live_bytes, nmaps in *. rewrite E1, E2, E3, E4. lia. Qed.

Lemma li_brk0 L pbrk mo rsp mo' evs z : KL L pbrk mo -> LI L mo -> ld_brk L = BPUntried ->
  nstep (NBrk 0) mo rsp mo' evs -> LI (set_brkph (BPQueried z) L) mo'.
Proof.
  intros HK HL Hph Hst. destruct (nstep_brk0_inv mo rsp mo' evs Hst) as (_ & _ & ->).
  pose proof (kl_phase _ _ _ HK) as P. rewrite Hph in P. destruct P as [_ Hreg].
  apply (LI_same_vm L _ mo); [exact HL| reflexivity| reflexivity| | reflexivity |]; unfold BB, CB; cbn; rewrite ?Hreg, Hph; [reflexivity| lia].
Qed.

Lemma li_brk_grow L pbrk mo rsp mo' evs req a :
  KL L pbrk mo -> LI L mo ->
  ((exists cur, ld_brk L = BPQueried cur /\ req = round_up_pg cur + 2 * PGSZ)
   \/ (exists b l, ld_brk L = BPLive /\ ld_brkreg L = Some (b, l) /\ req = b + l + PGSZ)) ->
  nstep (NBrk req) mo rsp mo' evs -> dec_brk pbrk req rsp = Some a ->
  LI (event_post L (EBrk req) (match a with BrkGrown => req | BrkSame => pbrk end)) mo'.
Proof.
  intros HK HL Hpre Hst Hd. pose proof alloc_ceiling_lt as Hcl.
  pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4). pose proof (kl_phase _ _ _ HK) as P.

  assert (PH : bv_unsigned (vm_brk (m_vmmaps mo)) = pbrk /\ 0 < pbrk /\ pbrk < req < 2^64 /\ req <> 0
               /\ pbrk mod 4096 = 0 /\ req mod 4096 = 0
               /\ BB (set_brkph BPDead L) = BB L /\ CB L <= CB (set_brkph BPDead L)
               /\ gm (if req =? req then match ld_brk L with BPQueried cur => set_brkph (BPGuard cur) L | _ => match ld_brkreg L with Some (b, l) => set_brkreg (Some (b, l + PGSZ)) L | None => L end end else set_brkph BPDead L) = gm L
               /\ BB (if req =? req then match ld_brk L with BPQueried cur => set_brkph (BPGuard cur) L | _ => match ld_brkreg L with Some (b, l) => set_brkreg (Some (b, l + PGSZ)) L | None => L end end else set_brkph BPDead L) = BB L + (req - pbrk)
               /\ gc (if req =? req then match ld_brk L with BPQueried cur => set_brkph (BPGuard cur) L | _ => match ld_brkreg L with Some (b, l) => set_brkreg (Some (b, l + PGSZ)) L | None => L end end else set_brkph BPDead L) = gc L
               /\ CB L + 1 <= CB (if req =? req then match ld_brk L with BPQueried cur => set_brkph (BPGuard cur) L | _ => match ld_brkreg L with Some (b, l) => set_brkreg (Some (b, l + PGSZ)) L | None => L end end else set_brkph BPDead L)).
  { rewrite Z.eqb_refl. destruct Hpre as [(cur & Hph & ->)|(b & l & Hph & Hreg & ->)]; rewrite Hph in P |- *.
    - destruct P as (Ecur & Ebrk & Epbrk & Hreg). unfold BB, CB. cbn. rewrite !Hph, !Hreg. cbn. rewrite ?Hph, ?Hreg.
      rewrite (round_up_pg_aligned cur) by (rewrite Ecur; unfold PGSZ in S2; exact S2). unfold PGSZ in *.
      assert (cur mod 4096 = 0) by (rewrite Ecur; exact S2).
      repeat split; try reflexivity; try lia; rewrite Z.add_mod, H by lia; reflexivity.
    - destruct P as (b' & l' & Hreg' & Ebrk & Epbrk). rewrite Hreg in Hreg'. inversion Hreg'; subst b' l'.
      pose proof (kl_brkreg _ _ _ HK b l Hreg) as (R1 & R2 & R3 & R4 & R5 & _). unfold BB, CB. cbn. rewrite !Hph, !Hreg. cbn. rewrite ?Hph, ?Hreg. unfold PGSZ in *.
      repeat split; try reflexivity; try lia;
        first [ rewrite Z.add_mod, R2, R4 by lia; reflexivity
              | rewrite Z.add_mod, (Z.add_mod b l), R2, R4 by lia; reflexivity
              | replace (l + 4096) with (l + 1 * 4096) by lia; rewrite Z.div_add by lia; lia ]. }
  destruct PH as (Ebrk & Hp0 & Hreq & NZ & Hbal & Hral & BBd & CBd & GMg & BBg & GCg & CBg).
  destruct (nstep_dec_brk req mo rsp mo' evs ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Ebrk; exact Hbal) Hral Hst) as (_ & _ & a' & Hd' & Ha).
  rewrite Ebrk in Hd'. rewrite Hd in Hd'. assert (a' = a) by congruence. subst a'.
  unfold event_post. rewrite (proj2 (Z.eqb_neq _ _) NZ).
  destruct a.
  -
    destruct Ha as (_ & _ & _ & ->).
    unfold LI, vm_live_bytes, nmaps. rewrite GMg, BBg, GCg. unfold kbrk_grow_model. cbv zeta. rewrite with_vmmaps_vmmaps. cbn [vm_maps length].
    rewrite live_bytes_cons. cbn [snd]. rewrite unsigned_lit by lia. rewrite Ebrk. destruct HL as [HL1 HL2]. unfold vm_live_bytes, nmaps in HL1, HL2. split; [lia|].
    rewrite Nat2Z.inj_succ. lia.
  -
    destruct Ha as [_ ->]. replace (pbrk =? req) with false by (symmetry; apply Z.eqb_neq; lia).
    apply (LI_same_vm L _ mo); [exact HL| reflexivity| reflexivity| exact BBd| reflexivity| exact CBd].
Qed.

Definition mm_val (x : mmap_ans) : Z := match x with MmErr e => neg_errno e | MmOk a => a end.

Lemma mm_post_eq L len prot z : prot = PROT_NONE \/ prot = PROT_RW ->
  event_post L (EMmap 0 len prot MAPF) z
  = (if is_err z then L else if prot =? PROT_NONE then set_metas ((z, len, 0) :: ld_metas L) L else set_groups ((z, len) :: ld_groups L) L).
Proof. intros _. reflexivity. Qed.

Lemma li_mmap_core L mo mo' len z :
  LI L mo -> 0 < len < LEN_MAX ->
  ((is_err z = true /\ vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mo))
   \/ (is_err z = false /\ vm_maps (m_vmmaps mo') = (Z_to_bv 64 z, Z_to_bv 64 (mmap_len len)) :: vm_maps (m_vmmaps mo))) ->
  forall prot, prot = PROT_NONE \/ prot = PROT_RW -> LI (event_post L (EMmap 0 len prot MAPF) z) mo'.
Proof.
  intros HL Hlen CASES prot Hprot. rewrite (mm_post_eq L len prot z Hprot).
  pose proof (mmap_len_ge len ltac:(lia)) as ML. unfold LEN_MAX in Hlen.
  destruct CASES as [[-> E]|[-> E]].
  - apply (LI_same_vm L _ mo); [exact HL| exact E| reflexivity| reflexivity| reflexivity| lia].
  - unfold LI, vm_live_bytes, nmaps in *. rewrite E, live_bytes_cons. cbn [snd length]. rewrite unsigned_lit by lia. rewrite Nat2Z.inj_succ.
    destruct Hprot as [-> | ->]; cbn [Z.eqb PROT_NONE PROT_RW Pos.eqb].
    + rewrite gm_add_meta, BB_set_metas, gc_add_meta, CB_set_metas. lia.
    + rewrite gm_add_group, BB_set_groups, gc_add_group, CB_set_groups. lia.
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
  destruct (nstep_dec_mmap len [] mo rsp mo' evs ltac:(lia) ltac:(lia) ltac:(constructor) Hst) as (_ & _ & x' & Hd' & Hx).
  rewrite Hd in Hd'. assert (x' = x) by congruence. subst x'.
  apply (li_mmap_core L mo mo' len (mm_val x) HL ltac:(unfold LEN_MAX; lia)); [| right; reflexivity].
  destruct x as [e|a]; cbn [mm_val].
  - destruct Hx as [-> ->]. left. split; [apply is_err_neg; unfold ENOMEM; lia| reflexivity].
  - destruct Hx as (Hok & _ & _ & E). right. destruct (mmap_ok_not_err _ _ _ Hok ltac:(lia)) as [NE Ha]. split; [exact NE|]. rewrite E. reflexivity.
Qed.

Lemma li_mmap_none L pbrk mo rsp mo' evs len x :
  KL L pbrk mo -> LI L mo -> 0 < len < LEN_MAX ->
  nstep (NMmap 0 len PROT_NONE MAPF) mo rsp mo' evs -> dec_mmap_none len [] rsp = Some x ->
  LI (event_post L (EMmap 0 len PROT_NONE MAPF) (mm_val x)) mo'.
Proof.
  intros HK HL Hlen Hst Hd. pose proof (mmap_len_ge len ltac:(lia)) as ML. unfold LEN_MAX in Hlen.
  destruct (nstep_dec_mmap_none len [] mo rsp mo' evs ltac:(lia) ltac:(lia) ltac:(constructor) Hst) as (_ & _ & x' & Hd' & Hx).
  rewrite Hd in Hd'. assert (x' = x) by congruence. subst x'.
  apply (li_mmap_core L mo mo' len (mm_val x) HL ltac:(unfold LEN_MAX; lia)); [| left; reflexivity].
  destruct x as [e|a]; cbn [mm_val].
  - destruct Hx as [-> ->]. left. split; [apply is_err_neg; unfold ENOMEM; lia| reflexivity].
  - destruct Hx as (Hok & _ & _ & E). right. destruct (mmap_ok_not_err _ _ _ Hok ltac:(lia)) as [NE Ha]. split; [exact NE|]. rewrite E. reflexivity.
Qed.

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
  pose proof (nstep_mmap_fixed_inv a PGSZ mo rsp mo' evs (kl_minv _ _ _ HK) Hst) as (_ & _ & Hcase).
  change (mmap_len PGSZ) with PGSZ in Hcase. rewrite !unsigned_lit in Hcase by (unfold PGSZ in *; lia).
  assert (POST : event_post L (EMmap a PGSZ PROT_NONE MAPFX) z = set_brkph BPLive (set_brkreg (Some (a, 2 * PGSZ)) L)) by reflexivity.
  rewrite POST. unfold LI, nmaps. rewrite gm_set_brkph, gm_set_brkreg, gc_set_brkph, gc_set_brkreg.
  assert (E2 : BB (set_brkph BPLive (set_brkreg (Some (a, 2 * PGSZ)) L)) = 2 * PGSZ) by reflexivity. rewrite E2.
  assert (E3 : CB (set_brkph BPLive (set_brkreg (Some (a, 2 * PGSZ)) L)) = 2) by reflexivity. rewrite E3.
  destruct HL as [HL1 HL2]. unfold BB, CB, nmaps in HL1, HL2. rewrite Hph in HL1, HL2.
  assert (LE : vm_live_bytes (m_vmmaps mo') <= vm_live_bytes (m_vmmaps mo)
               /\ (length (vm_maps (m_vmmaps mo')) <= length (vm_maps (m_vmmaps mo)) + 1)%nat).
  { unfold vm_live_bytes. destruct Hcase as [[_ ->] | [[_ ->] | [_ ->]]]; rewrite ?with_vmmaps_vmmaps; cbn [vm_maps].
    - lia.
    - lia.
    - split; [apply live_bytes_subtract; unfold PGSZ in *; lia|].
      apply length_maps_subtract; [exact (kl_wf _ _ _ HK)| unfold PGSZ; lia]. }
  destruct LE as [LE1 LE2]. split; [lia|]. rewrite Nat2Z.inj_le, Nat2Z.inj_add in LE2. cbn in LE2. lia.
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
  destruct (nstep_dec_munmap a len mo rsp mo' evs (kl_minv _ _ _ HK) Hst) as (_ & _ & _ & Emaps). rewrite Hlen2 in Emaps.
  unfold went, wz in A5. unfold LI, vm_live_bytes, nmaps. rewrite Emaps. cbn [vm_maps].
  rewrite (live_bytes_remove _ _ _ (kl_wf _ _ _ HK) A5).
  pose proof (length_remove_In _ _ _ A5) as LR.
  change (event_post L (EMunmap a len) z) with (set_groups (g_remove a (ld_groups L)) L).
  rewrite (gm_remove_group L pbrk mo a l0 HK Hin), BB_set_groups, (gc_remove_group L pbrk mo a l0 HK Hin), CB_set_groups. rewrite unsigned_lit by lia.
  destruct HL as [HL1 HL2]. unfold vm_live_bytes, nmaps in HL1, HL2. split; [lia|]. lia.
Qed.

Lemma li_mprotect L pbrk mo rsp mo' evs b l k z :
  KL L pbrk mo -> LI L mo -> In (b, l, k) (ld_metas L) -> (2 + k) * PGSZ <= round_up_pg l ->
  nstep (NMprotect (b + (1 + k) * PGSZ) PGSZ PROT_RW) mo rsp mo' evs ->
  LI (event_post L (EMprotect (b + (1 + k) * PGSZ) PGSZ PROT_RW) z) mo'.
Proof.
  intros HK HL Hin Hk Hst. pose proof alloc_ceiling_lt as Hcl.
  destruct (nstep_dec_mprotect (b + (1 + k) * PGSZ) PGSZ mo rsp mo' evs Hst) as (_ & _ & x & _ & Hx).
  assert (Emaps : vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mo)).
  { destruct x as [e|[|]]; [destruct Hx as [_ ->]; reflexivity| destruct Hx as (_ & E); rewrite E; reflexivity| destruct Hx]. }
  apply (LI_same_vm L _ mo); [exact HL| exact Emaps| | | |]; unfold event_post; destruct ((z =? 0) || (z =? TWO64 - ENOSYS)); rewrite ?gm_bump, ?gc_bump; try reflexivity; lia.
Qed.

End AC_1.
