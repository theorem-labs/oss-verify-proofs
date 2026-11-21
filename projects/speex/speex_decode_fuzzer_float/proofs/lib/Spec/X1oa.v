(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (nstep_munmap_inv_has reads munmap's maps_subtract cut as the old map_remove under the new vmwf premise, with the new maps_subtract_exact, iv_subtract_self, map_remove_cons, map_remove_id and map_has_In; KL_init reads the launch's reserved ledger as the image's reservations followed by the vDSO/vvar pair, which the placement base and the brk window keep apart, proves KL's two new vDSO fields, and takes the launch's channel-reader fact for minv). *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c5 X1by X1bs X1c2 X1bn X1c7.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1qs X1rc X1ra X1qu X1r3 X1r4 X1og X1oh X1oi X1of X1pe X1r9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require X1pu.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
Ltac kl_open HK := destruct HK as [Kminv Khalt Kceil Kwf Kresv Krt Kstart Kgr Kme Kdis Kreg Kph Kvdi Kvda Kvdd].
Local Notation MP := (X1qx.M PState).

Definition LIM : Z := 2^34.
Definition esz (e : word * word) : Z := bv_unsigned (snd e).

Lemma live_bytes_app : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a n] l1 IH]; intros; cbn; [reflexivity| rewrite IH; lia]. Qed.
Lemma live_bytes_nonneg : forall l, 0 <= live_bytes l.
Proof. induction l as [|[a n] l IH]; cbn; [lia|]. pose proof (bv_unsigned_in_range 64 n). lia. Qed.
Lemma live_bytes_filter_le : forall f l, live_bytes (List.filter f l) <= live_bytes l.
Proof.
induction l as [|[a n] l IH]; cbn; [lia|]. pose proof (bv_unsigned_in_range 64 n). destruct (f (a, n)); cbn; lia.
Qed.
Lemma live_bytes_cons : forall e l, live_bytes (e :: l) = esz e + live_bytes l.
Proof. intros [a n] l. reflexivity. Qed.

Lemma vmwf_tail : forall e l, vmwf (e :: l) -> vmwf l.
Proof. intros e l [Hb Hp]. inversion Hp; subst. split; [intros x Hx; apply Hb; right; exact Hx| assumption]. Qed.

Lemma live_bytes_remove : forall maps a n, vmwf maps -> In (a, n) maps ->
live_bytes (map_remove maps a) = live_bytes maps - bv_unsigned n.
Proof.
induction maps as [|[a0 n0] maps IH]; intros a n Hw Hin; [destruct Hin|].
pose proof (vmwf_tail _ _ Hw) as Hw'. destruct Hw as [Hb Hp]. inversion Hp; subst.
unfold map_remove. cbn [List.filter fst]. destruct Hin as [E|Hin].
- injection E as -> ->. rewrite bv_eqb_refl. cbn [negb]. rewrite live_bytes_cons. unfold esz; cbn [snd].
enough (List.filter (fun p : word * word => negb (bv_eqb (fst p) a)) maps = maps) as -> by lia.
apply List.forallb_filter_id. apply forallb_forall. intros [a' n'] Hin'. cbn [fst].
destruct (bv_eqb a' a) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. subst a'. exfalso.
pose proof (H1 _ Hin') as D. pose proof (Hb (a, n) (or_introl eq_refl)). pose proof (Hb (a, n') (or_intror Hin')). unfold edisj, elo, ehi in *. cbn in *. lia.
- destruct (bv_eqb a0 a) eqn:E.
+ apply bv_eqb_eq in E. subst a0. exfalso.
pose proof (H1 _ Hin) as D. pose proof (Hb (a, n0) (or_introl eq_refl)). pose proof (Hb (a, n) (or_intror Hin)). unfold edisj, elo, ehi in *. cbn in *. lia.
+ cbn [negb]. rewrite !live_bytes_cons. fold (map_remove maps a). rewrite (IH a n Hw' Hin). lia.
Qed.

Lemma live_bytes_iv_subtract_in : forall a sz lo hi,
bv_unsigned a <= lo -> lo < hi -> hi <= bv_unsigned a + bv_unsigned sz -> bv_unsigned a + bv_unsigned sz <= 2^64 ->
live_bytes (iv_subtract a sz lo hi) = bv_unsigned sz - (hi - lo).
Proof.
intros a sz lo hi H1 H2 H3 H4. unfold iv_subtract.
pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn -[Z.min Z.max Z_to_bv bv_unsigned Z.sub Z.add];
rewrite ?unsigned_lit by lia; lia.
Qed.

Lemma maps_subtract_disjoint_id : forall maps lo hi, vmwf maps -> lo < hi ->
(forall e, In e maps -> ehi e <= lo \/ hi <= elo e) -> maps_subtract maps lo hi = maps.
Proof.
induction maps as [|[a sz] maps IH]; intros lo hi Hw Hlh Hd; [reflexivity|]. cbn.
pose proof (proj1 Hw (a, sz) (or_introl eq_refl)) as W. unfold elo, ehi in W; cbn in W.
rewrite iv_subtract_disjoint; [| lia| exact Hlh| specialize (Hd (a, sz) (or_introl eq_refl)); unfold elo, ehi in Hd; cbn in Hd; lia].
cbn. f_equal. apply IH; [eapply vmwf_tail; exact Hw| exact Hlh| intros e He; apply Hd; right; exact He].
Qed.

Lemma live_bytes_subtract : forall maps lo hi, vmwf maps -> lo < hi ->
(exists m, In m maps /\ elo m <= lo /\ hi <= ehi m) ->
live_bytes (maps_subtract maps lo hi) = live_bytes maps - (hi - lo).
Proof.
intros maps lo hi Hw Hlh (m0 & Hin & C1 & C2).
revert Hw Hin. induction maps as [|[a sz] maps IH]; intros Hw Hin; [destruct Hin|].
pose proof (vmwf_tail _ _ Hw) as Hw'. destruct Hw as [Hbd Hp]. inversion Hp; subst. cbn [maps_subtract]. rewrite live_bytes_app, !live_bytes_cons. unfold esz; cbn [snd].
destruct Hin as [E|Hin].
- subst m0. pose proof (Hbd (a, sz) (or_introl eq_refl)) as W. unfold elo, ehi in W, C1, C2; cbn in W, C1, C2.
rewrite live_bytes_iv_subtract_in by lia.
rewrite maps_subtract_disjoint_id; [lia| exact Hw'| exact Hlh|].
intros e He. pose proof (H1 e He) as D. unfold edisj, elo, ehi in D |- *. cbn in D. lia.
- pose proof (H1 _ Hin) as D. pose proof (Hbd (a, sz) (or_introl eq_refl)) as W. unfold edisj, elo, ehi in D, W, C1, C2; cbn in D, W.
rewrite iv_subtract_disjoint; [| lia| exact Hlh| lia]. rewrite live_bytes_cons. unfold esz; cbn [snd].
rewrite (IH Hw' Hin). cbn [live_bytes]. lia.
Qed.

(* ------------------------------------------------------------------
   The exact-munmap post-state bridge.

   At LPS 75d69e00 [Mmap.munmap_spec]'s exact arm leaves
   [mmap_fixed_destroyed_next h addr n], which cuts the request out of
   [vm_maps] with [maps_subtract]
   (75d69e00:theories/LinuxProcessSem/Sys/Mm/Mmap.v:1488); before the
   revision it removed the whole entry with [map_remove].  The two
   agree exactly when the request IS one of the entries AND the ledger
   is well formed, because [maps_subtract] also cuts every OTHER entry
   that meets the range, and only pairwise disjointness rules those
   out.  [vmwf] is defined in [Spec.X1og], above [Lib], which is why
   this bridge cannot be stated beside [munmap_out] in [Lib.X1c7].
   ------------------------------------------------------------------ *)

Lemma map_remove_cons : forall (e : word * word) l (a : word),
map_remove (e :: l) a = if bv_eqb (fst e) a then map_remove l a else e :: map_remove l a.
Proof. intros [a0 n0] l a. unfold map_remove. cbn [List.filter fst]. destruct (bv_eqb a0 a); reflexivity. Qed.

Lemma map_remove_id : forall l (a : word), (forall e, In e l -> fst e <> a) -> map_remove l a = l.
Proof.
intros l a H. unfold map_remove. apply List.forallb_filter_id. apply forallb_forall.
intros e He. apply Bool.negb_true_iff. destruct (bv_eqb (fst e) a) eqn:Ea; [|reflexivity].
exfalso. apply (H e He). apply bv_eqb_eq. exact Ea.
Qed.

Lemma iv_subtract_self : forall (a sz : word),
iv_subtract a sz (bv_unsigned a) (bv_unsigned a + bv_unsigned sz) = [].
Proof. intros a sz. unfold iv_subtract. rewrite !Z.ltb_irrefl. reflexivity. Qed.

Lemma maps_subtract_exact : forall maps (aw nw : word),
vmwf maps -> In (aw, nw) maps ->
maps_subtract maps (bv_unsigned aw) (bv_unsigned aw + bv_unsigned nw) = map_remove maps aw.
Proof.
induction maps as [|[a0 n0] maps IH]; intros aw nw Hw Hin; [destruct Hin|].
pose proof (vmwf_tail _ _ Hw) as Hw'.
destruct Hw as [Hb Hp]. inversion Hp as [|e0 l0 Hd0 Hp0]; subst.
rewrite map_remove_cons. cbn [maps_subtract fst].
destruct Hin as [E|Hin].
- injection E as -> ->. rewrite bv_eqb_refl.
rewrite iv_subtract_self. cbn [app].
pose proof (Hb (aw, nw) (or_introl eq_refl)) as W0. unfold elo, ehi in W0; cbn [fst snd] in W0.
rewrite (maps_subtract_disjoint_id maps (bv_unsigned aw) (bv_unsigned aw + bv_unsigned nw) Hw' ltac:(lia)).
+ symmetry. apply map_remove_id. intros e He Ea.
pose proof (Hd0 e He) as D. pose proof (Hb e (or_intror He)) as We.
unfold edisj, elo, ehi in D, We. cbn [fst snd] in D, We. rewrite Ea in D, We. lia.
+ intros e He. pose proof (Hd0 e He) as D. unfold edisj, elo, ehi in D |- *. cbn [fst snd] in D |- *. lia.
- pose proof (Hb (aw, nw) (or_intror Hin)) as W1. unfold elo, ehi in W1; cbn [fst snd] in W1.
pose proof (Hd0 (aw, nw) Hin) as D0. unfold edisj, elo, ehi in D0; cbn [fst snd] in D0.
pose proof (Hb (a0, n0) (or_introl eq_refl)) as W0. unfold elo, ehi in W0; cbn [fst snd] in W0.
assert (Ea0 : bv_eqb a0 aw = false).
{ destruct (bv_eqb a0 aw) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. exfalso. rewrite E in W0, D0. lia. }
rewrite Ea0. rewrite (iv_subtract_disjoint a0 n0 (bv_unsigned aw) (bv_unsigned aw + bv_unsigned nw)
ltac:(lia) ltac:(lia) ltac:(lia)). cbn [app].
f_equal. exact (IH aw nw Hw' Hin).
Qed.

Lemma map_has_In : forall maps (lo n : word), map_has maps lo n = true -> In (lo, n) maps.
Proof.
intros maps lo n H. unfold map_has in H. apply existsb_exists in H as ([a sz] & Hin & E).
apply andb_prop in E as [E1 E2]. cbn [fst snd] in E1, E2.
apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst. exact Hin.
Qed.

(* The [vmwf] premise is new at LPS 75d69e00: without it the model's
   [maps_subtract] post-state is NOT the old [map_remove] one.  Every
   caller holds it as [kl_wf] of its [KL]. *)
Lemma nstep_munmap_inv_has : forall a len mo rsp mo' evs,
let h := m_vmmaps mo in let n := mmap_len len in let aw := Z_to_bv 64 a in let nw := Z_to_bv 64 n in
0 <= a -> a mod 4096 = 0 -> 0 < len -> a + n <= TASK_SIZE   -> vmwf (vm_maps h) -> map_has (vm_maps h) aw nw = true ->
nstep (NMunmap a len) mo rsp mo' evs ->
evs = [] /\ vm_only mo mo' /\ rsp = mkEffectU (Z_to_bv 64 0) [] [] [(aw, nw)] [] []
/\ mo' = with_mmap_destroyed aw nw (mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) aw) (maps_subtract (vm_noaccess h) a (a + n))
(vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo.
Proof.
intros a len mo rsp mo' evs h n aw nw Ha Hal Hlen Hb Hwf Hhas H. pose proof (mmap_len_ge len Hlen) as Hn. fold n in Hn.
pose proof Hb as Hb'. unfold TASK_SIZE in Hb'.
pose proof (nstep_mm_vm_only (NMunmap a len) mo rsp mo' evs I H) as [Hv ->]. split; [reflexivity|]. split; [exact Hv|].
apply (proj1 (nstep_munmap_iff _ _ _ _ _ _)) in H as [_ H].
unfold munmap_out, munmap_grant, munmap_next in H. cbv zeta in H. fold aw h in H.
assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; lia). rewrite Ua, page_size_eq, Hal in H.
rewrite w_is0_lit in H by lia. replace (len =? 0) with false in H by (symmetry; apply Z.eqb_neq; lia). cbn [Z.eqb negb orb] in H.
rewrite (unsigned_lit len) in H by lia. fold (mmap_len len) in H. fold n nw in H.
replace (TASK_SIZE <? a + n) with false in H by (symmetry; apply Z.ltb_ge; lia). rewrite Hhas in H.
assert (Un : bv_unsigned nw = n) by (subst nw; apply unsigned_lit; lia).
assert (Emaps : mmap_fixed_destroyed_next h aw nw
= mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) aw) (maps_subtract (vm_noaccess h) a (a + n))
(vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
{ unfold mmap_fixed_destroyed_next.
  rewrite (maps_subtract_exact (vm_maps h) aw nw Hwf (map_has_In _ _ _ Hhas)).
  rewrite Ua, Un. reflexivity. }
rewrite Emaps in H. apply Ok_inj in H as (-> & -> & _). auto.
Qed.

Lemma reserved_top_ge' : forall l e, In e l -> bv_unsigned (fst e) + bv_unsigned (snd e) <= reserved_top l.
Proof.
induction l as [|[a sz] l IH]; intros e Hin; [destruct Hin|].
cbn [reserved_top]. destruct Hin as [<-|Hin]; cbn [fst snd]; [lia|]. specialize (IH e Hin). lia.
Qed.

Lemma KL_init : forall segs brk0 mbase sp lim inp,
valid_brk segs brk0 -> 0 < reserved_top (segments_reserved segs) -> valid_sp sp ->
(* [State.init_model] reserves the launch's vDSO/vvar pair just below the placement
   base, which [Run.valid_mmap_base] keeps above [State.mmap_base_min]; the brk
   window stays below 2^40, so the pair is far above the brk guard. *)
valid_mmap_base mbase ->
reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo ->
reserved_top (segments_reserved segs) + brk_aslr_max + PGSZ <= 2^40 ->
(* the launch's reader of the standard channels ([Run.valid_input]), which [minv] carries *)
in_channel_reader inp = true ->
KL (led_init (bv_unsigned sp - stack_max_size) (reservedZ segs)) 0 (init_model (segments_reserved segs) brk0 mbase sp lim inp).
Proof.
intros segs brk0 mbase sp lim inp (Hlo & Hhi & Hal) Hpos (Hsl & Hsh & Hs16) (Hmb1 & Hmb2 & Hmb3) Hceil H40 Hrdr.
pose proof (vdso_len_bounds (in_kernel inp)) as Hvl.
assert (HV1 : mmap_base_min - page_size
<= page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size))).
{ unfold page_round_down_Z, page_size, mmap_base_min, sp_window_lo, sp_window_hi, stack_max_size in *. lia. }
assert (HV2 : page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)) < two_pow_64).
{ unfold page_round_down_Z, page_size, mmap_base_max, sp_window_lo, sp_window_hi, stack_max_size, two_pow_64 in *. lia. }
assert (Hresv : exists lo hi,
vm_reserved (m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp)) = lo ++ hi
/\ ld_resv (led_init (bv_unsigned sp - stack_max_size) (reservedZ segs)) = map wwZ lo).
{ exists (segments_reserved segs),
(vdso_reserved (in_kernel inp) (vdso_top (m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp)))).
split; [apply vm_reserved_init_model| unfold reservedZ, wwZ; reflexivity]. }
assert (Hrtop : forall e,
In e (vm_reserved (m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp))) ->
ehi e <= bv_unsigned (vm_start_brk (m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp)))
\/ In e (vdso_reserved (m_kernel (init_model (segments_reserved segs) brk0 mbase sp lim inp))
(vdso_top (m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp))))).
{ rewrite m_kernel_init_model, vdso_top_init_model, m_vmmaps_init_model.
cbn [vm_reserved vm_start_brk]. intros e Hin.
unfold init_reserved in Hin. apply in_app_or in Hin as [Hin|Hin].
- left. pose proof (reserved_top_ge' _ _ Hin). unfold ehi. lia.
- right. exact Hin. }
assert (Hvdi : incl (vdso_reserved (m_kernel (init_model (segments_reserved segs) brk0 mbase sp lim inp))
(vdso_top (m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp))))
(vm_reserved (m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp)))).
{ rewrite vm_reserved_init_model, m_kernel_init_model. apply incl_appr, incl_refl. }
assert (Hvda : forall e,
In e (vdso_reserved (m_kernel (init_model (segments_reserved segs) brk0 mbase sp lim inp))
(vdso_top (m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp)))) ->
bv_unsigned (vm_start_brk (m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp))) + 4 * PGSZ <= elo e).
{ rewrite m_kernel_init_model, vdso_top_init_model, m_vmmaps_init_model. cbn [vm_start_brk].
intros [ea en] Hin.
pose proof (vdso_reserved_above (in_kernel inp) _ ea en HV2 Hin) as [Hge _].
unfold elo. cbn [fst]. change (2^40) with 1099511627776 in H40.
unfold PGSZ, mmap_base_min, page_size in *. lia. }
assert (Hvdd : forall r,
In r (vm_reserved (m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp))) ->
forall e, In e (vm_maps (m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp))) -> edisj e r).
{ rewrite m_vmmaps_init_model. cbn [vm_maps]. intros r Hr e []. }
unfold sp_window_lo in Hsl. unfold sp_window_hi in Hsh. unfold alloc_ceiling_lo in Hceil.
constructor; try exact Hresv; try exact Hrtop; try exact Hvdi; try exact Hvda; try exact Hvdd;
rewrite ?m_vmmaps_init_model; cbn -[Z.pow Z.mul Z.add Z.sub init_model].
- apply minv_init. exact Hrdr.
- apply m_halted_init_model.
- unfold alloc_top, stack_max_size, alloc_ceiling_lo, alloc_ceiling_hi. cbn [vm_init_sp]. lia.
- split; [intros e []| apply pwdisj_nil].
- unfold PGSZ in *. unfold page_size in Hal. unfold stack_max_size. lia.
- intros b l [].
- intros b l k [].
- apply List.NoDup_nil.
- intros b l H. discriminate.
- split; reflexivity.
Qed.
