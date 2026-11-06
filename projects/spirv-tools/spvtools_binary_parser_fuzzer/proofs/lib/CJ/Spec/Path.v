(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs.

From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import PropExec MState ITree Nodes Decode NodesMM Gap.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import Prelim Monad MSafe STree Malloc MallocCtrl Prog KInv KStep KLink
  MI_Kit MPos CtxMono LB_Logic LB_Kernel LB_Embed LB_Raw LB_Count.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Lemma nstep_exists n mo : nsafe n mo -> exists eff mo', nstep n mo eff mo' [].
Proof.
  intros Hs. unfold nstep. destruct n; try (exfalso; exact Hs); cbv zeta.
  - destruct (req =? 0); eexists; eexists; [split; [reflexivity|]; split; reflexivity| split; [reflexivity|]; left; split; reflexivity].
  - cbn in Hs. destruct Hs as [_ [(-> & -> & ->)|[(-> & -> & ->)|(-> & -> & _)]]].
    + exists (efferr ENOMEM), mo. split; [reflexivity|]. change ((MAP_ANON_PRIV =? MAP_ANON_PRIV) && (PROT_RW_Z =? PROT_RW_Z)) with true. cbv iota.
      left. exists ENOMEM. split; [left; reflexivity|]. auto.
    + exists (efferr ENOMEM), mo. split; [reflexivity|]. change ((MAP_ANON_PRIV =? MAP_ANON_PRIV) && (0 =? PROT_RW_Z)) with false.
      change ((MAP_ANON_PRIV =? MAP_ANON_PRIV) && (0 =? 0)) with true. cbv iota.
      left. exists ENOMEM. split; [left; reflexivity|]. auto.
    + exists (efferr ENOMEM), mo. split; [reflexivity|].
      change ((MAP_ANON_PRIV_FIXED =? MAP_ANON_PRIV) && (0 =? PROT_RW_Z)) with false.
      change ((MAP_ANON_PRIV_FIXED =? MAP_ANON_PRIV) && (0 =? 0)) with false.
      change ((MAP_ANON_PRIV_FIXED =? MAP_ANON_PRIV_FIXED) && (0 =? 0)) with true. cbv iota.
      left. exists ENOMEM. split; [left; reflexivity|]. auto.
  - eexists; eexists. split; [reflexivity|]. split; reflexivity.
  - exists (efferr ENOMEM), mo. split; [reflexivity|]. left. exists ENOMEM. split; [left; reflexivity|]. auto.
Qed.

Lemma twf_leaf_exists {R} : forall (t : itree node R) mo (Q : R -> Model -> Prop),
  twf t mo Q -> exists r mo', tpath nstep t mo [] r mo' /\ Q r mo'.
Proof.
  induction t as [r|n k IH]; intros mo Q H; cbn in H.
  - exists r, mo. cbn. auto.
  - destruct H as [Hs Hk]. destruct (nstep_exists n mo Hs) as (eff & mo1 & Hst).
    destruct (IH eff mo1 Q (Hk _ _ _ Hst)) as (r & mo' & Hp & HQ).
    exists r, mo'. split; [| exact HQ]. cbn. exists eff, mo1, [], []. auto.
Qed.

Lemma etwf_leaf_exists {A} (t : itree node (exc A)) mo (Q : A -> Model -> Prop) :
  etwf t mo Q -> exists a mo', tpath nstep t mo [] (Ok a) mo' /\ Q a mo'.
Proof.
  intros H. destruct (twf_leaf_exists t mo _ H) as (r & mo' & Hp & HQ). destruct r as [|a]; [destruct HQ|]. exists a, mo'. auto.
Qed.

Definition node_of (e : ev) : node :=
  match e with
  | EBrk r => NBrk r
  | EMmap a l p f => NMmap a l p f
  | EMunmap a l => NMunmap a l
  | EMprotect a l p => NMprotect a l p
  | _ => NSetTid
  end.

Definition is_sys (e : ev) : bool := match e with EPeek _ _ _ | EUndef _ => false | _ => true end.

Lemma ev_step_vis e (s : PState) : is_sys e = true ->
  exists kk, ev_step e s = Vis (node_of e) kk /\ forall r, exists v, kk r = Ret v.
Proof.
  intros Hs. destruct e as [req|a len prot flags|a len|a len prot|? ? ?|?]; try discriminate Hs; unfold ev_step.
  - destruct (req =? 0) eqn:E.
    + apply Z.eqb_eq in E. subst req. eexists. split; [reflexivity|]. intros r. cbn. destruct (dec_brk0 r); eexists; reflexivity.
    + eexists. split; [reflexivity|]. intros r. cbn. destruct (dec_brk _ _ r) as [[|]|]; eexists; reflexivity.
  - destruct (negb _); [| destruct (prot =? 0)]; eexists; (split; [reflexivity|]); intros r; cbn;
      [destruct (dec_mmap_fixed _ _ r)| destruct (dec_mmap_none _ _ r)| destruct (dec_mmap _ _ r)]; eexists; reflexivity.
  - eexists. split; [reflexivity|]. intros r. cbn. destruct (dec_munmap _ _ r); eexists; reflexivity.
  - eexists. split; [reflexivity|]. intros r. cbn. destruct (dec_mprotect_rw _ _ r); eexists; reflexivity.
Qed.

Lemma membed_step {R} e (k : Z -> stree ev Z R) s mo kk eff mo1 z s1 r mo' :
  ev_step e s = Vis (node_of e) kk -> nstep (node_of e) mo eff mo1 [] -> kk eff = Ret (Ok (z, s1)) ->
  tpath nstep (membed (k z) s1) mo1 [] r mo' -> tpath nstep (membed (SVis e k) s) mo [] r mo'.
Proof.
  intros Hv Hst Hk Hp. cbn [membed]. unfold mbind. apply (proj2 (tpath_ebind _ _ _ _ _ _ _ _)). right.
  exists [], (z, s1), mo1, []. split; [| split; [exact Hp| reflexivity]].
  rewrite Hv. cbn. exists eff, mo1, [], []. split; [exact Hst|]. rewrite Hk. cbn. auto.
Qed.

Lemma etwf_vis_ret {A} nd (kk : resp -> itree node (exc A)) mo (Q : A -> Model -> Prop) eff mo1 v :
  etwf (Vis nd kk) mo Q -> nstep nd mo eff mo1 [] -> kk eff = Ret v -> exists x, v = Ok x /\ Q x mo1.
Proof.
  intros [_ Hk] Hst Hv. specialize (Hk eff mo1 [] Hst). rewrite Hv in Hk. cbn in Hk. destruct v as [|x]; [destruct Hk|]. exists x. auto.
Qed.

Lemma tpath_membed_follow {R} : forall (t : stree ev Z R) s mo r s' mo',
  tpath nstep (membed t s) mo [] (Ok (r, s')) mo' -> exists ans, follow t ans = Some r.
Proof.
  induction t as [r0|e k IH]; intros s mo r s' mo' Hp.
  - cbn in Hp. destruct Hp as (E & _ & _). inversion E; subst. exists []. reflexivity.
  - cbn [membed] in Hp. unfold mbind in Hp. apply (proj1 (tpath_ebind _ _ _ _ _ _ _ _)) in Hp.
    destruct Hp as [[_ E]|(tr1 & [z s1] & mo1 & tr2 & H1 & H2 & Etr)]; [discriminate E|].
    destruct tr1; [| discriminate Etr]. destruct tr2; [| discriminate Etr]. cbn [fst snd] in H2.
    destruct (IH z s1 mo1 r s' mo' H2) as [ans Hf].
    destruct (is_sys e) eqn:Hs.
    + exists (z :: ans). destruct e; try discriminate Hs; exact Hf.
    + exfalso. destruct e; try discriminate Hs; cbn in H1; destruct H1 as (E & _); discriminate E.
Qed.

Lemma unsigned_Z_to_bv_le v : 0 <= v -> bv_unsigned (Z_to_bv 64 v) <= v.
Proof. intros Hv. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_le; lia. Qed.

Lemma live_bytes_iv_subtract' a sz lo hi : lo <= hi -> live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz.
Proof.
  intros Hlh. pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 sz) as Rs. unfold bv_modulus in *.
  unfold iv_subtract.
  destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn -[Z_to_bv bv_unsigned Z.min Z.max Z.add Z.sub].
  - pose proof (unsigned_Z_to_bv_le (bv_unsigned sz `min` (lo - bv_unsigned a)) ltac:(lia)).
    pose proof (unsigned_Z_to_bv_le (bv_unsigned a + bv_unsigned sz - bv_unsigned a `max` hi) ltac:(lia)). lia.
  - pose proof (unsigned_Z_to_bv_le (bv_unsigned sz `min` (lo - bv_unsigned a)) ltac:(lia)). lia.
  - pose proof (unsigned_Z_to_bv_le (bv_unsigned a + bv_unsigned sz - bv_unsigned a `max` hi) ltac:(lia)). lia.
  - lia.
Qed.

Lemma live_bytes_subtract' maps lo hi : lo <= hi -> live_bytes (maps_subtract maps lo hi) <= live_bytes maps.
Proof.
  intros H. induction maps as [|[a sz] l IH]; cbn; [lia|]. rewrite live_bytes_app. pose proof (live_bytes_iv_subtract' a sz lo hi H). lia.
Qed.

Lemma live_bytes_subtract_all cuts : forall maps, live_bytes (maps_subtract_all maps cuts) <= live_bytes maps.
Proof.
  induction cuts as [|[a n] cuts IH]; intros maps; cbn; [lia|].
  eapply Z.le_trans; [apply IH|]. apply live_bytes_subtract'. pose proof (bv_unsigned_in_range 64 n). lia.
Qed.

Lemma vm_backing_le_live mo : minv mo -> vm_backing_used mo <= vm_live_bytes (m_vmmaps mo).
Proof.
  intros [Hl Hm]. unfold vm_backing_used. rewrite Hl, Hm. cbn [maps_subtract_all length Z.of_nat]. rewrite Z.mul_0_l, Z.add_0_r.
  unfold vm_backed_maps, vm_live_bytes. apply live_bytes_subtract_all.
Qed.

Definition mmval (x : mmap_ans) : Z := match x with MmErr e => neg_errno e | MmOk a => a end.
Definition rgval (x : range_ans) : Z := match x with RgErr e => neg_errno e | RgDone _ => 0 end.
Definition fxval (addr : Z) (x : fixed_ans) : Z := match x with FxKept e => neg_errno e | FxDone => addr | FxLost e => neg_errno e end.

Definition oret {A} (s : PState) (o : option A) (f : A -> Z) : itree node (exc (Z * PState)) :=
  match o with Some x => Ret (Ok (f x, s)) | None => Ret Unr end.

Lemma ev_step_mmap_shape len prot s : prot = PROT_NONE \/ prot = PROT_RW ->
  exists kk, ev_step (EMmap 0 len prot MAPF) s = Vis (NMmap 0 len prot MAPF) kk /\
    forall rsp, kk rsp = oret s ((if prot =? 0 then dec_mmap_none len [] else dec_mmap len []) rsp) mmval.
Proof.
  intros Hp. unfold ev_step. change (Z.land MAPF MAP_FIXED_Z =? 0) with true. cbn [negb].
  destruct Hp as [-> | ->].
  - change (PROT_NONE =? 0) with true. cbv iota. eexists. split; [reflexivity|]. intros rsp. cbn. destruct (dec_mmap_none len [] rsp) as [[e|a]|]; reflexivity.
  - change (PROT_RW =? 0) with false. cbv iota. eexists. split; [reflexivity|]. intros rsp. cbn. destruct (dec_mmap len [] rsp) as [[e|a]|]; reflexivity.
Qed.

Lemma ev_step_munmap_shape a len s :
  exists kk, ev_step (EMunmap a len) s = Vis (NMunmap a len) kk /\ forall rsp, kk rsp = oret s (dec_munmap a len rsp) rgval.
Proof. unfold ev_step. eexists. split; [reflexivity|]. intros rsp. cbn. destruct (dec_munmap a len rsp) as [[e|b]|]; reflexivity. Qed.

Lemma ev_step_mprotect_shape a len prot s :
  exists kk, ev_step (EMprotect a len prot) s = Vis (NMprotect a len prot) kk /\ forall rsp, kk rsp = oret s (dec_mprotect_rw a len rsp) rgval.
Proof. unfold ev_step. eexists. split; [reflexivity|]. intros rsp. cbn. destruct (dec_mprotect_rw a len rsp) as [[e|b]|]; reflexivity. Qed.

Lemma dec_mmap_err len avoid : dec_mmap len avoid (efferr ENOMEM) = Some (MmErr ENOMEM).
Proof. unfold dec_mmap, efferr, eff0. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins]. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity. Qed.
Lemma dec_mmap_none_err len avoid : dec_mmap_none len avoid (efferr ENOMEM) = Some (MmErr ENOMEM).
Proof. unfold dec_mmap_none, efferr, eff0. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins]. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity. Qed.

Lemma dec_mmap_grant len (aw : word) : mmap_addr_ok len [] (bv_unsigned aw) = true ->
  dec_mmap len [] (mkEffect aw [] [(aw, Z_to_bv 64 (mmap_len len))]) = Some (MmOk (bv_unsigned aw)).
Proof. intros H. unfold dec_mmap. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins]. rewrite !bv_eqb_refl, H. reflexivity. Qed.
Lemma dec_mmap_none_grant len (aw : word) : mmap_addr_ok len [] (bv_unsigned aw) = true ->
  dec_mmap_none len [] (mkEffectU aw [] [] [(aw, Z_to_bv 64 (mmap_len len))] [] []) = Some (MmOk (bv_unsigned aw)).
Proof. intros H. unfold dec_mmap_none. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins]. rewrite !bv_eqb_refl, H. reflexivity. Qed.
Lemma dec_mprotect_rw_ok a len : dec_mprotect_rw a len (mkEffect (Z_to_bv 64 0) [] [(Z_to_bv 64 a, Z_to_bv 64 (mmap_len len))]) = Some (RgDone true).
Proof. unfold dec_mprotect_rw, dec_mprotect. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins]. change (bv_unsigned (Z_to_bv 64 0) =? 0) with true. rewrite !bv_eqb_refl. reflexivity. Qed.

Definition G0 : PState -> Model -> Prop := fun _ _ => True.
Lemma frame_ok_G0 : frame_ok G0. Proof. intros ? ? ? ? _ _ _ _. exact I. Qed.

Lemma child_inv B L e s mo kk eff mo1 v :
  event_pre L e -> KL L (ps_brk s) mo -> LI L mo -> BOUND L e B ->
  ev_step e s = Vis (node_of e) kk -> nstep (node_of e) mo eff mo1 [] -> kk eff = Ret v ->
  exists z s1, v = Ok (z, s1) /\ answer_ok L e z = true /\ KL (event_post L e z) (ps_brk s1) mo1
               /\ LI (event_post L e z) mo1 /\ ps_m s1 = ps_m s.
Proof.
  intros Hpre HK HLI HB Hvis Hst Hk.
  pose proof (ev_step_spec L e G0 s frame_ok_G0 Hpre s mo (conj eq_refl (conj HK I))) as ES. rewrite Hvis in ES.
  destruct (etwf_vis_ret _ _ _ _ _ _ _ ES Hst Hk) as ([z s1] & -> & Hpost).
  pose proof (ev_step_L B L e G0 s frame_ok_G0 Hpre s mo (conj eq_refl (conj HK (conj HLI (conj I HB))))) as EL.
  rewrite Hvis in EL. cbn in EL. specialize (EL eff mo1 [] Hst). rewrite Hk in EL. cbn in EL. destruct EL as [_ [_ HLI']].
  destruct Hpost as (Ha & HK' & _ & Hm & _). exists z, s1. auto 10.
Qed.

Section PATH.
Variables (n SMAX ETOT NR RBY : Z).
Hypothesis SMAX0 : 0 <= SMAX.
Hypothesis NR0 : 0 <= NR.
Hypothesis RBY0 : 0 <= RBY.

Definition LENMAX : Z := Z.max (Z.max (2 ^ (SMAX + 1)) 2 * PGSZ) (LRW n).
Definition GAPOK : Prop := forall n', 0 < n' <= mmap_len LENMAX ->
  (RBY + LBUDGET) / n' + 2 * (NR + ETOT) < (alloc_ceiling - bottomup_floor) / n'.
Hypothesis HGAP : GAPOK.

Definition RSV (h : VmMaps) : Prop :=
  zlen (vm_reserved h) <= NR /\ Gap.zsum (fun e => bv_unsigned (snd e)) (vm_reserved h) <= RBY.

Record NI (D : nat) (L : mled) (s : PState) (mo : Model) : Prop := mkNI {
  ni_kl : KL L (ps_brk s) mo;
  ni_li : LI L mo;
  ni_lim : LBUDGET <= vm_limit (m_vmmaps mo);
  ni_rsv : RSV (m_vmmaps mo);
  ni_cnt : gc L + CB L + Z.of_nat D <= ETOT }.

Lemma zlen_app' {A} (l1 l2 : list A) : zlen (l1 ++ l2) = zlen l1 + zlen l2.
Proof. unfold zlen. rewrite length_app. lia. Qed.

Lemma mmap_len_facts len : 0 < len -> len <= mmap_len len /\ mmap_len len mod page_size = 0 /\ mmap_len len < len + page_size /\ 0 < mmap_len len.
Proof.
  intros Hl. unfold mmap_len, page_round_up_Z, page_size.
  pose proof (Z.div_mod (len + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (len + 4096 - 1) 4096 ltac:(lia)).
  split; [lia|]. split; [apply Z_mod_mult|]. lia.
Qed.

Lemma mmap_len_mono a b : 0 < a <= b -> mmap_len a <= mmap_len b.
Proof. intros H. unfold mmap_len, page_round_up_Z, page_size. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia. Qed.

Lemma gap_for L D s mo len :
  NI D L s mo -> 0 < len <= LENMAX -> gm L + BB L <= LBUDGET ->
  exists a, bottomup_floor <= a /\ a + mmap_len len <= alloc_ceiling /\ a mod page_size = 0 /\ 0 < a /\
            region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true.
Proof.
  intros [HK HLI Hlim [R1 R2] HC] Hlen HGB. destruct (mmap_len_facts len ltac:(lia)) as (M1 & M2 & M3 & M4).
  apply (kgap_exists _ (mmap_len len) (NR + ETOT) (RBY + LBUDGET)); [exact M4| exact M2| | | unfold LBUDGET; lia|].
  - rewrite zlen_app'. pose proof (LI_count _ _ HLI) as C. unfold nmaps in C. unfold zlen in *. lia.
  - rewrite Gap.zsum_app. pose proof (LI_elim _ _ HLI) as LB. unfold vm_live_bytes in LB.
    assert (E : forall l, Gap.zsum (fun e : word * word => bv_unsigned (snd e)) l = live_bytes l).
    { induction l as [|[x y] l IH]; [reflexivity|]. cbn [Gap.zsum]. rewrite live_bytes_cons, IH. reflexivity. }
    rewrite (E (vm_maps (m_vmmaps mo))). lia.
  - apply HGAP. split; [exact M4|]. apply mmap_len_mono. lia.
Qed.

Definition TT : mled -> mstate * option cptr -> Prop := fun _ _ => True.
Definition LEAF (t : stree ev Z (mstate * option cptr)) (s : PState) (mo : Model) : Prop :=
  forall r s' mo', tpath nstep (membed t s) mo [] (Ok (r, s')) mo' -> cshift (fst r) <= SMAX.

Lemma LEAF_child e k s mo kk eff mo1 z s1 :
  ev_step e s = Vis (node_of e) kk -> nstep (node_of e) mo eff mo1 [] -> kk eff = Ret (Ok (z, s1)) ->
  LEAF (SVis e k) s mo -> LEAF (k z) s1 mo1.
Proof. intros Hv Hst Hk HL r s' mo' Hp. apply (HL r s' mo'). eapply membed_step; eauto. Qed.

Lemma nstep_mmap_refuse len prot mo : prot = PROT_NONE \/ prot = PROT_RW ->
  nstep (NMmap 0 len prot MAPF) mo (efferr ENOMEM) mo [].
Proof.
  intros Hp. split; [reflexivity|]. cbv zeta. destruct Hp as [-> | ->].
  - change ((MAPF =? MAP_ANON_PRIV) && (PROT_NONE =? PROT_RW_Z)) with false. change ((MAPF =? MAP_ANON_PRIV) && (PROT_NONE =? 0)) with true. cbv iota.
    left. exists ENOMEM. split; [left; reflexivity|]. auto.
  - change ((MAPF =? MAP_ANON_PRIV) && (PROT_RW =? PROT_RW_Z)) with true. cbv iota.
    left. exists ENOMEM. split; [left; reflexivity|]. auto.
Qed.

Lemma pow_le_SMAX c : c <= SMAX -> Z.max (2 ^ (c + 1)) 2 <= Z.max (2 ^ (SMAX + 1)) 2.
Proof.
  intros Hc. destruct (Z.neg_nonneg_cases (c + 1)) as [Hn|Hn].
  - rewrite (Z.pow_neg_r 2 _ Hn). pose proof (Z.pow_nonneg 2 (SMAX + 1)). lia.
  - assert (2 ^ (c + 1) <= 2 ^ (SMAX + 1)) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma nonfixed_len_bound L D s mo len prot (k : Z -> stree ev Z (mstate * option cptr)) :
  let e := EMmap 0 len prot MAPF in
  NI (S D) L s mo -> brk_quiet L -> (prot = PROT_NONE \/ prot = PROT_RW) -> 0 < len < LEN_MAX -> BOUND L e LBUDGET ->
  (forall z, answer_ok L e z = true -> ctree_ok (event_post L e z) (k z) TT) ->
  (forall z, lall (CE n e) (k z)) -> LEAF (SVis e k) s mo ->
  len <= LENMAX /\ gm L + BB L <= LBUDGET.
Proof.
  intros e HNI Hq Hp Hlen HB HC NK1 HL. pose proof HNI as [HK HLI Hlim HR HCnt].
  assert (Hpre : event_pre L e) by (left; unfold e; repeat split; auto; lia).
  destruct (ev_step_mmap_shape len prot s Hp) as (kk & Hvis & Hkk).
  pose proof (nstep_mmap_refuse len prot mo Hp) as Hst.
  assert (Hk : kk (efferr ENOMEM) = Ret (Ok (neg_errno ENOMEM, s))).
  { rewrite Hkk. destruct Hp as [-> | ->]; [change (PROT_NONE =? 0) with true | change (PROT_RW =? 0) with false]; cbv iota beta;
      [rewrite dec_mmap_none_err | rewrite dec_mmap_err]; reflexivity. }
  destruct (child_inv LBUDGET L e s mo kk _ _ _ Hpre HK HLI HB Hvis Hst Hk) as (z & s1 & Ez & Ha & HK1 & HLI1 & Hm).
  assert (z = neg_errno ENOMEM /\ s1 = s) as [-> ->] by (inversion Ez; auto).
  assert (EP : event_post L e (neg_errno ENOMEM) = L).
  { unfold e, event_post. change (Z.land MAPF MAP_FIXED =? 0) with true. rewrite is_err_neg by (unfold ENOMEM; lia). reflexivity. }
  split.
  2:{ specialize (HB _ Ha). rewrite EP in HB. exact HB. }
  rewrite EP in HK1. specialize (HC _ Ha). rewrite EP in HC.
  pose proof (membed_spec (k (neg_errno ENOMEM)) TT G0 L s frame_ok_G0 HC s mo (conj eq_refl (conj HK1 I))) as TW.
  destruct (etwf_leaf_exists _ _ _ TW) as ([r s'] & mo' & Hp2 & _).
  assert (HS : cshift (fst r) <= SMAX).
  { apply (HL r s' mo'). eapply membed_step; eauto. }
  destruct (tpath_membed_follow _ _ _ _ _ _ Hp2) as [ans Hf].
  pose proof (lall_follow _ _ _ _ (NK1 (neg_errno ENOMEM)) Hf) as HCE. unfold CE, evr, e in HCE. cbn [fst] in HCE.
  specialize (HCE ltac:(reflexivity)). destruct HCE as [H1 H2].
  unfold LENMAX. destruct Hp as [-> | ->].
  - specialize (H1 eq_refl). pose proof (pow_le_SMAX _ HS). unfold PGSZ in *. nia.
  - specialize (H2 ltac:(discriminate)). lia.
Qed.

Lemma alloc_ceiling_lt64 : alloc_ceiling < 2 ^ 63.
Proof. pose proof ac_bounds_lit. lia. Qed.

Lemma node_mmap_grant L D s mo len prot :
  let e := EMmap 0 len prot MAPF in
  NI (S D) L s mo -> brk_quiet L -> (prot = PROT_NONE \/ prot = PROT_RW) -> 0 < len < LEN_MAX -> BOUND L e LBUDGET ->
  len <= LENMAX -> gm L + BB L <= LBUDGET ->
  exists kk eff mo1 a, ev_step e s = Vis (node_of e) kk /\ nstep (node_of e) mo eff mo1 [] /\ kk eff = Ret (Ok (a, s)) /\ is_err a = false
    /\ vm_limit (m_vmmaps mo1) = vm_limit (m_vmmaps mo) /\ vm_reserved (m_vmmaps mo1) = vm_reserved (m_vmmaps mo).
Proof.
  intros e HNI Hq Hp Hlen HB HLM HGB. pose proof HNI as [HK HLI Hlim HR HCnt].
  pose proof alloc_ceiling_lt64 as HC63.
  destruct (gap_for L (S D) s mo len HNI ltac:(lia) HGB) as (a0 & F1 & F2 & F3 & F4 & F5).
  pose proof bottomup_floor_val as HF.
  destruct (mmap_len_facts len ltac:(lia)) as (M1 & M2 & M3 & M4).
  set (nZ := mmap_len len) in *. set (aw := Z_to_bv 64 a0). set (nw := Z_to_bv 64 nZ).
  assert (Ua : bv_unsigned aw = a0) by (subst aw; apply unsigned_lit; lia).
  change (Z_to_bv 64 a0) with aw in F5. change (Z_to_bv 64 nZ) with nw in F5.
  assert (Hok : mmap_addr_ok len [] a0 = true).
  { rewrite <- Ua. apply (mmap_addr_ok_of_grant len [] aw mo); rewrite ?Ua; [lia| pose proof alloc_ceiling_State; fold nZ; lia| exact F3| exact F4| exact F2| exact F5| constructor]. }
  set (mo1 := if prot =? PROT_NONE then knoaccess_model aw nw mo else kmmap_model aw nw mo).
  assert (Hvm : m_vmmaps mo1 = mkVmMapsFull (vm_reserved (m_vmmaps mo)) ((aw, nw) :: vm_maps (m_vmmaps mo))
                 (if prot =? PROT_NONE then (aw, nw) :: vm_noaccess (m_vmmaps mo) else vm_noaccess (m_vmmaps mo))
                 (vm_start_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo)) (vm_limit (m_vmmaps mo)) (vm_mmap_base (m_vmmaps mo)) (vm_init_sp (m_vmmaps mo))).
  { subst mo1. destruct (prot =? PROT_NONE); unfold knoaccess_model, kmmap_model; rewrite with_vmmaps_vmmaps; reflexivity. }
  assert (Hmi1 : minv mo1 /\ m_halted mo1 = None).
  { subst mo1. destruct (prot =? PROT_NONE); unfold knoaccess_model, kmmap_model;
      (split; [apply minv_with_vmmaps; exact (kl_minv _ _ _ HK)| rewrite halted_with_vmmaps; exact (kl_halt _ _ _ HK)]). }
  destruct Hmi1 as [Hmi1 Hh1].
  destruct (KL_mmap_new L (ps_brk s) mo mo1 a0 len (prot =? PROT_NONE) HK Hq Hlen Hok F5 Hmi1 Hh1 Hvm) as (_ & Hans & Herr).
  assert (Hansw : answer_ok L e a0 = true).
  { unfold e, answer_ok. change (Z.land MAPF MAP_FIXED =? 0) with true. exact Hans. }

  assert (HBUD : vm_backing_used mo + nZ <= vm_limit (m_vmmaps mo)).
  { pose proof (vm_backing_le_live mo (kl_minv _ _ _ HK)) as VB. pose proof (LI_elim _ _ HLI) as LE.
    specialize (HB a0 Hansw). unfold e, event_post in HB. change (Z.land MAPF MAP_FIXED =? 0) with true in HB. rewrite Herr in HB. cbv iota in HB.
    destruct Hp as [-> | ->].
    - change (PROT_NONE =? PROT_NONE) with true in HB. cbv iota in HB. rewrite gm_add_meta, BB_set_metas in HB. fold nZ in HB. lia.
    - change (PROT_RW =? PROT_NONE) with false in HB. cbv iota in HB. rewrite gm_add_group, BB_set_groups in HB. fold nZ in HB. lia. }
  destruct (ev_step_mmap_shape len prot s Hp) as (kk & Hvis & Hkk).
  destruct Hp as [-> | ->].
  -
    exists kk, (mkEffectU aw [] [] [(aw, nw)] [] []), mo1, a0.
    assert (G : kgrant_ok_na (Z_to_bv 64 0) mo aw nZ = true).
    { unfold kgrant_ok_na. change (Z_to_bv 64 nZ) with nw. rewrite F5, Ua. rewrite (proj2 (Z.eqb_eq _ _) F3), (proj2 (Z.ltb_lt _ _) F4).
      rewrite (proj2 (Z.leb_le _ _) F2). reflexivity. }
    split; [exact Hvis|]. split.
    { split; [reflexivity|]. cbv zeta. change ((MAPF =? MAP_ANON_PRIV) && (PROT_NONE =? PROT_RW_Z)) with false.
      change ((MAPF =? MAP_ANON_PRIV) && (PROT_NONE =? 0)) with true. cbv iota. right. exists aw. split; [exact G|]. split; [reflexivity|].
      subst mo1. change (PROT_NONE =? PROT_NONE) with true. reflexivity. }
    split; [rewrite Hkk; change (PROT_NONE =? 0) with true; cbv iota beta; fold nZ; rewrite (dec_mmap_none_grant len aw ltac:(rewrite Ua; exact Hok)), Ua; reflexivity|].
    split; [exact Herr|]. rewrite Hvm. split; reflexivity.
  -
    exists kk, (mkEffect aw [] [(aw, nw)]), mo1, a0.
    assert (G : kgrant_ok (Z_to_bv 64 0) mo aw nZ = true).
    { unfold kgrant_ok. rewrite (proj2 (Z.leb_le _ _) HBUD). change (Z_to_bv 64 nZ) with nw. rewrite F5, Ua. rewrite (proj2 (Z.eqb_eq _ _) F3), (proj2 (Z.ltb_lt _ _) F4).
      rewrite (proj2 (Z.leb_le _ _) F2). reflexivity. }
    split; [exact Hvis|]. split.
    { split; [reflexivity|]. cbv zeta. change ((MAPF =? MAP_ANON_PRIV) && (PROT_RW =? PROT_RW_Z)) with true. cbv iota.
      right. exists aw. split; [exact G|]. split; [reflexivity|]. subst mo1. change (PROT_RW =? PROT_NONE) with false. reflexivity. }
    split; [rewrite Hkk; change (PROT_RW =? 0) with false; cbv iota beta; fold nZ; rewrite (dec_mmap_grant len aw ltac:(rewrite Ua; exact Hok)), Ua; reflexivity|].
    split; [exact Herr|]. rewrite Hvm. split; reflexivity.
Qed.

Lemma node_mprotect L D s mo a len prot :
  let e := EMprotect a len prot in
  NI (S D) L s mo -> event_pre L e -> BOUND L e LBUDGET ->
  exists kk eff mo1, ev_step e s = Vis (node_of e) kk /\ nstep (node_of e) mo eff mo1 [] /\ kk eff = Ret (Ok (0, s))
    /\ vm_limit (m_vmmaps mo1) = vm_limit (m_vmmaps mo) /\ vm_reserved (m_vmmaps mo1) = vm_reserved (m_vmmaps mo).
Proof.
  intros e HNI Hpre HB. pose proof HNI as [HK HLI Hlim HR HCnt].
  cbn [event_pre e] in Hpre. destruct Hpre as (Hq & -> & -> & b & l & k & Hin & Ea & Hk2).
  destruct (ev_step_mprotect_shape a PGSZ PROT_RW s) as (kk & Hvis & Hkk).
  set (aw := Z_to_bv 64 a). set (nw := Z_to_bv 64 (page_round_up_Z PGSZ)).
  set (mo1 := kmprotect_model aw nw mo).
  assert (HBUD : mprotect_budget_ok mo aw nw = true).
  { unfold mprotect_budget_ok, vm_backing_within_limit. apply Z.leb_le.
    assert (MI1 : minv (mprotect_model_next mo aw nw)) by (unfold mprotect_model_next; apply minv_with_vmmaps; exact (kl_minv _ _ _ HK)).
    pose proof (vm_backing_le_live _ MI1) as VB. unfold mprotect_model_next in VB |- *. rewrite with_vmmaps_vmmaps in VB |- *. cbn [vm_limit vm_maps] in VB |- *.
    pose proof (LI_elim _ _ HLI) as LE. unfold vm_live_bytes in VB, LE. cbn [vm_maps] in VB.

    assert (HGB : gm L + BB L <= LBUDGET).
    { specialize (HB (neg_errno ENOMEM)). unfold e, answer_ok, event_post in HB. unfold mprotect_answer_ok in HB.
      rewrite is_errno_form_neg in HB by (unfold ENOMEM; lia). rewrite orb_true_r in HB. specialize (HB eq_refl).
      replace ((neg_errno ENOMEM =? 0) || (neg_errno ENOMEM =? TWO64 - ENOSYS)) with false in HB; [exact HB|].
      unfold neg_errno, ENOMEM, ENOSYS, TWO64. reflexivity. }
    lia. }
  exists kk, (mkEffect (Z_to_bv 64 0) [] [(aw, nw)]), mo1.
  split; [exact Hvis|]. split.
  { split; [reflexivity|]. cbv zeta. right. split; [exact HBUD|]. split; reflexivity. }
  split.
  { rewrite Hkk. subst aw nw. change (page_round_up_Z PGSZ) with (mmap_len PGSZ). rewrite dec_mprotect_rw_ok. reflexivity. }
  subst mo1. unfold kmprotect_model. rewrite with_vmmaps_vmmaps. split; reflexivity.
Qed.

Lemma node_munmap L D s mo a len :
  let e := EMunmap a len in
  NI (S D) L s mo ->
  exists kk eff mo1, ev_step e s = Vis (node_of e) kk /\ nstep (node_of e) mo eff mo1 [] /\ kk eff = Ret (Ok (0, s))
    /\ vm_limit (m_vmmaps mo1) = vm_limit (m_vmmaps mo) /\ vm_reserved (m_vmmaps mo1) = vm_reserved (m_vmmaps mo).
Proof.
  intros e HNI. pose proof HNI as [HK HLI Hlim HR HCnt].
  destruct (ev_step_munmap_shape a len s) as (kk & Hvis & Hkk).
  set (aw := Z_to_bv 64 a). set (nw := Z_to_bv 64 (page_round_up_Z len)).
  assert (Hst : nstep (NMunmap a len) mo (mkEffectU (Z_to_bv 64 0) [] [] [(aw, nw)] [] []) (kmunmap_model aw nw mo) []).
  { split; [reflexivity|]. cbv zeta. split; reflexivity. }
  pose proof (nstep_dec_munmap a len mo _ _ _ (kl_minv _ _ _ HK) Hst) as (_ & _ & Hdec & Hvm).
  exists kk, (mkEffectU (Z_to_bv 64 0) [] [] [(aw, nw)] [] []), (kmunmap_model aw nw mo).
  split; [exact Hvis|]. split; [exact Hst|]. split; [rewrite Hkk, Hdec; reflexivity|]. rewrite Hvm. split; reflexivity.
Qed.

Lemma g_remove_length a l : (length (g_remove a l) <= length l)%nat.
Proof. induction l as [|y l IH]; cbn; [lia|]. destruct (fst y =? a); cbn; lia. Qed.

Lemma NI_child D L L' s s1 mo mo1 :
  NI (S D) L s mo -> KL L' (ps_brk s1) mo1 -> LI L' mo1 ->
  vm_limit (m_vmmaps mo1) = vm_limit (m_vmmaps mo) -> vm_reserved (m_vmmaps mo1) = vm_reserved (m_vmmaps mo) ->
  gc L' + CB L' <= gc L + CB L + 1 -> NI D L' s1 mo1.
Proof.
  intros [HK HLI Hlim HR HC] HK1 HLI1 E1 E2 HCC. constructor; [exact HK1| exact HLI1| rewrite E1; exact Hlim| unfold RSV in *; rewrite E2; exact HR| lia].
Qed.

End PATH.

End AC_1.
