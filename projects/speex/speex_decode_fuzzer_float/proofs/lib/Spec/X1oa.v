(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
Ltac kl_open HK := destruct HK as [Kminv Khalt Kceil Kwf Kresv Krt Kstart Kgr Kme Kdis Kreg Kph].
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

Lemma nstep_munmap_inv_has : forall a len mo rsp mo' evs,
let h := m_vmmaps mo in let n := mmap_len len in let aw := Z_to_bv 64 a in let nw := Z_to_bv 64 n in
0 <= a -> a mod 4096 = 0 -> 0 < len -> a + n <= TASK_SIZE   -> map_has (vm_maps h) aw nw = true ->
nstep (NMunmap a len) mo rsp mo' evs ->
evs = [] /\ vm_only mo mo' /\ rsp = mkEffectU (Z_to_bv 64 0) [] [] [(aw, nw)] [] []
/\ mo' = with_mmap_destroyed aw nw (mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) aw) (maps_subtract (vm_noaccess h) a (a + n))
(vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo.
Proof.
intros a len mo rsp mo' evs h n aw nw Ha Hal Hlen Hb Hhas H. pose proof (mmap_len_ge len Hlen) as Hn. fold n in Hn.
pose proof Hb as Hb'. unfold TASK_SIZE in Hb'.
pose proof (nstep_mm_vm_only (NMunmap a len) mo rsp mo' evs I H) as [Hv ->]. split; [reflexivity|]. split; [exact Hv|].
apply (proj1 (nstep_munmap_iff _ _ _ _ _ _)) in H as [_ H]. unfold munmap_out in H. cbv zeta in H. fold aw h in H.
assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; lia). rewrite Ua, page_size_eq, Hal in H.
rewrite w_is0_lit in H by lia. replace (len =? 0) with false in H by (symmetry; apply Z.eqb_neq; lia). cbn [Z.eqb negb orb] in H.
rewrite (unsigned_lit len) in H by lia. fold (mmap_len len) in H. fold n nw in H.
replace (TASK_SIZE <? a + n) with false in H by (symmetry; apply Z.ltb_ge; lia). rewrite Hhas in H.
apply Ok_inj in H as (-> & -> & _). subst nw. rewrite (unsigned_lit n) by lia. auto.
Qed.

Lemma reserved_top_ge' : forall l e, In e l -> bv_unsigned (fst e) + bv_unsigned (snd e) <= reserved_top l.
Proof.
induction l as [|[a sz] l IH]; intros e Hin; [destruct Hin|].
cbn [reserved_top]. destruct Hin as [<-|Hin]; cbn [fst snd]; [lia|]. specialize (IH e Hin). lia.
Qed.

Lemma KL_init : forall segs brk0 mbase sp lim inp,
valid_brk segs brk0 -> 0 < reserved_top (segments_reserved segs) -> valid_sp sp ->
reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo ->
KL (led_init (bv_unsigned sp - stack_max_size) (reservedZ segs)) 0 (init_model (segments_reserved segs) brk0 mbase sp lim inp).
Proof.
intros segs brk0 mbase sp lim inp (Hlo & Hhi & Hal) Hpos (Hsl & Hsh & _) Hceil.
unfold sp_window_lo in Hsl. unfold sp_window_hi in Hsh. unfold alloc_ceiling_lo in Hceil.
constructor; rewrite ?m_vmmaps_init_model; cbn -[Z.pow Z.mul Z.add Z.sub init_model].
- apply minv_init.
- apply m_halted_init_model.
- unfold alloc_top, stack_max_size, alloc_ceiling_lo, alloc_ceiling_hi. cbn [vm_init_sp]. lia.
- split; [intros e []| apply pwdisj_nil].
- unfold reservedZ, wwZ. reflexivity.
- intros e Hin. pose proof (reserved_top_ge' _ _ Hin). unfold ehi. lia.
- unfold PGSZ in *. unfold page_size in Hal. unfold stack_max_size. lia.
- intros b l [].
- intros b l k [].
- apply List.NoDup_nil.
- intros b l H. discriminate.
- split; reflexivity.
Qed.
