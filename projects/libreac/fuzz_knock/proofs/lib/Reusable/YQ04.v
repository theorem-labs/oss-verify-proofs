(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YQ04.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Run Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import SyscallTable.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import VmMapsDisjoint.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YQ00 YQ03.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Set Default Proof Mode "Classic".
Fixpoint zsum (f : Z -> Z) (lo : Z) (n : nat) : Z :=
match n with O => 0 | S k => f lo + zsum f (lo + 1) k end.
Lemma zsum_le : forall f g lo n, (forall x, lo <= x < lo + Z.of_nat n -> f x <= g x) -> zsum f lo n <= zsum g lo n.
Proof.
intros f g lo n; revert lo; induction n as [|k IH]; intros lo H; cbn [zsum]; [lia|].
assert (f lo <= g lo) by (apply H; lia).
assert (zsum f (lo + 1) k <= zsum g (lo + 1) k) by (apply IH; intros x Hx; apply H; lia). lia.
Qed.
Lemma zsum_ext : forall f g lo n, (forall x, lo <= x < lo + Z.of_nat n -> f x = g x) -> zsum f lo n = zsum g lo n.
Proof.
intros f g lo n H. pose proof (zsum_le f g lo n ltac:(intros x Hx; rewrite (H x Hx); lia)).
pose proof (zsum_le g f lo n ltac:(intros x Hx; rewrite (H x Hx); lia)). lia.
Qed.
Lemma zsum_add : forall f g lo n, zsum (fun x => f x + g x) lo n = zsum f lo n + zsum g lo n.
Proof. intros f g lo n; revert lo; induction n as [|k IH]; intros lo; cbn [zsum]; [lia|]. rewrite IH. lia. Qed.
Lemma zsum_le_all : forall f g lo n, (forall x, f x <= g x) -> zsum f lo n <= zsum g lo n.
Proof. intros f g lo n H. apply zsum_le. intros x _. apply H. Qed.
Lemma zsum_ext_all : forall f g lo n, (forall x, f x = g x) -> zsum f lo n = zsum g lo n.
Proof. intros f g lo n H. apply zsum_ext. intros x _. apply H. Qed.
Lemma zsum_nonneg : forall f lo n, (forall x, lo <= x < lo + Z.of_nat n -> 0 <= f x) -> 0 <= zsum f lo n.
Proof. intros f lo n H. pose proof (zsum_le (fun _ => 0) f lo n H) as H'. revert H'. generalize (zsum f lo n). intros z.
assert (E : forall lo' k, zsum (fun _ => 0) lo' k = 0) by (intros lo' k; revert lo'; induction k as [|k IH]; intros; cbn [zsum]; [lia| rewrite IH; lia]).
rewrite E. lia.
Qed.
Lemma zsum_zero : forall f lo n, (forall x, lo <= x < lo + Z.of_nat n -> f x = 0) -> zsum f lo n = 0.
Proof. intros f lo n; revert lo; induction n as [|k IH]; intros lo H; cbn [zsum]; [lia|]. rewrite H by lia. rewrite IH; [lia|]. intros x Hx; apply H; lia. Qed.
Lemma zsum_indicator : forall n lo a b, lo <= a -> a <= b -> b <= lo + Z.of_nat n ->
zsum (fun x => if (a <=? x) && (x <? b) then 1 else 0) lo n = b - a.
Proof.
induction n as [|k IH]; intros lo a b H1 H2 H3; cbn [zsum]; [lia|].
destruct (Z.eq_dec a b) as [->|NE].
- destruct (Z.leb_spec b lo); destruct (Z.ltb_spec lo b); cbn [andb]; try lia.
all: rewrite zsum_zero; [lia|]; intros x Hx; destruct (Z.leb_spec b x); destruct (Z.ltb_spec x b); cbn [andb]; lia.
- destruct (Z.leb_spec a lo); destruct (Z.ltb_spec lo b); cbn [andb]; try lia.
+ rewrite (zsum_ext _ (fun x => if (a + 1 <=? x) && (x <? b) then 1 else 0)).
* rewrite (IH (lo + 1) (a + 1) b); lia.
* intros x Hx. destruct (Z.leb_spec a x); destruct (Z.leb_spec (a + 1) x); cbn [andb]; try reflexivity; lia.
+ rewrite (IH (lo + 1) a b); lia.
Qed.
Definition plo (p : word * word) : Z := bv_unsigned (fst p).
Definition psz (p : word * word) : Z := bv_unsigned (snd p).
Definition phi (p : word * word) : Z := plo p + psz p.
Definition nwr (P : list (word * word)) : Prop := Forall (fun p => phi p <= 2 ^ 64) P.
Definition N64 : nat := Z.to_nat (2 ^ 64).
Lemma N64_Z : Z.of_nat N64 = 2 ^ 64.
Proof. unfold N64. rewrite Z2Nat.id; [reflexivity|]. apply Z.pow_nonneg. discriminate. Qed.
Global Opaque N64.
Definition cov (C : list (word * word)) (x : Z) : bool := existsb (fun c => owns_b c x) C.
Lemma owners_cons : forall p P x, owners (p :: P) x = ((if owns_b p x then 1 else 0) + owners P x)%nat.
Proof. reflexivity. Qed.
Lemma owns_b_spec : forall a sz x, owns_b (a, sz) x = ((bv_unsigned a <=? x) && (x <? bv_unsigned a + bv_unsigned sz))%bool.
Proof. reflexivity. Qed.
Lemma cov_cons : forall c C x, cov (c :: C) x = (owns_b c x || cov C x)%bool.
Proof. reflexivity. Qed.
Lemma live_bytes_zsum : forall P, nwr P -> live_bytes P = zsum (fun x => Z.of_nat (owners P x)) 0 N64.
Proof.
induction P as [|[a sz] P IH]; intros NW.
- cbn [live_bytes owners]. symmetry. apply zsum_zero. intros; reflexivity.
- inversion NW as [|p P' Hp HP]; subst. cbn [live_bytes]. rewrite (IH HP).
unfold phi, plo, psz in Hp; cbn [fst snd] in Hp. pose proof (word_range a). pose proof (word_range sz).
rewrite (zsum_ext_all (fun x => Z.of_nat (owners ((a, sz) :: P) x)) (fun x => (if (bv_unsigned a <=? x) && (x <? bv_unsigned a + bv_unsigned sz) then 1 else 0) + Z.of_nat (owners P x))).
+ rewrite zsum_add, zsum_indicator; rewrite ?N64_Z; [lia|lia|lia|]. unfold phi, plo, psz in Hp. lia.
+ intros x. rewrite owners_cons, owns_b_spec. destruct (_ && _)%bool; lia.
Qed.
Lemma owners_iv_subtract : forall a sz lo hi x, 0 <= lo -> lo <= hi -> (hi < 2 ^ 64 \/ bv_unsigned a + bv_unsigned sz <= 2 ^ 64) ->
owners (iv_subtract a sz lo hi) x = if (lo <=? x) && (x <? hi) then 0%nat else owners [(a, sz)] x.
Proof.
intros a sz lo hi x Hlo Hlh Hw. pose proof (word_range a) as Ra. pose proof (word_range sz) as Rs.
unfold iv_subtract. cbv zeta.
destruct (Z.ltb_spec (bv_unsigned a) lo) as [L1|L1]; destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)) as [R1|R1]; cbn [app owners];
rewrite ?owns_b_spec; cbn [fst snd]; rewrite ?u64 by lia.
all: repeat match goal with |- context [Z.leb ?u ?v] => destruct (Z.leb_spec u v) | |- context [Z.ltb ?u ?v] => destruct (Z.ltb_spec u v) end; cbn; try lia.
Qed.
Lemma owners_maps_subtract : forall P lo hi x, 0 <= lo -> lo <= hi -> (hi < 2 ^ 64 \/ nwr P) ->
owners (maps_subtract P lo hi) x = if (lo <=? x) && (x <? hi) then 0%nat else owners P x.
Proof.
induction P as [|[a sz] P IH]; intros lo hi x Hlo Hlh Hw; cbn [maps_subtract owners]; [destruct (_ && _)%bool; reflexivity|].
rewrite owners_app, owners_iv_subtract; try assumption.
2:{ destruct Hw as [Hw|Hw]; [left; exact Hw | right]. inversion Hw; subst. exact H1. }
rewrite IH; try assumption. 2:{ destruct Hw as [Hw|Hw]; [left; exact Hw | right]. inversion Hw; subst. exact H2. }
cbn [owners]. destruct (_ && _)%bool; lia.
Qed.
Lemma nwr_iv_subtract : forall a sz lo hi, 0 <= lo -> lo <= hi -> bv_unsigned a + bv_unsigned sz <= 2 ^ 64 -> nwr (iv_subtract a sz lo hi).
Proof.
intros a sz lo hi Hlo Hlh Hw. pose proof (word_range a) as Ra. pose proof (word_range sz) as Rs. unfold nwr, iv_subtract. cbv zeta.
destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn [app];
repeat constructor; unfold phi, plo, psz; cbn [fst snd]; rewrite ?u64 by lia; lia.
Qed.
Lemma nwr_app : forall P Q, nwr P -> nwr Q -> nwr (P ++ Q).
Proof. intros. apply Forall_app. split; assumption. Qed.
Lemma nwr_maps_subtract : forall P lo hi, 0 <= lo -> lo <= hi -> nwr P -> nwr (maps_subtract P lo hi).
Proof.
induction P as [|[a sz] P IH]; intros lo hi Hlo Hlh NW; cbn [maps_subtract]; [constructor|].
inversion NW; subst. apply nwr_app; [apply nwr_iv_subtract; try assumption; exact H1 | apply IH; assumption].
Qed.
Lemma owners_maps_subtract_all : forall C P x, nwr P ->
owners (maps_subtract_all P C) x = if cov C x then 0%nat else owners P x.
Proof.
induction C as [|[a n] C IH]; intros P x NW; cbn [maps_subtract_all cov existsb]; [reflexivity|].
pose proof (word_range a). pose proof (word_range n).
rewrite IH by (apply nwr_maps_subtract; [lia|lia|exact NW]).
rewrite owners_maps_subtract; [|lia|lia|right; exact NW].
unfold cov. rewrite owns_b_spec. destruct (existsb _ C), ((bv_unsigned a <=? x) && (x <? bv_unsigned a + bv_unsigned n))%bool; reflexivity.
Qed.
Lemma nwr_maps_subtract_all : forall C P, nwr P -> nwr (maps_subtract_all P C).
Proof.
induction C as [|[a n] C IH]; intros P NW; cbn [maps_subtract_all]; [exact NW|].
pose proof (word_range a). pose proof (word_range n). apply IH. apply nwr_maps_subtract; [lia|lia|exact NW].
Qed.
Lemma nwr_filter : forall f P, nwr P -> nwr (List.filter f P).
Proof. intros f P H. unfold nwr in *. rewrite Forall_forall in H |- *. intros p Hp. apply List.filter_In in Hp as [Hp _]. exact (H p Hp). Qed.
Definition WF (m : Model) : Prop := nwr (vm_maps (m_vmmaps m)).
Section MV.
Variable m : Model.
Hypothesis HWF : WF m.
Lemma filter_length_le {A} : forall (f : A -> bool) l, (length (List.filter f l) <= length l)%nat.
Proof. intros f l. induction l as [|y l IH]; cbn; [lia|]. destruct (f y); cbn; lia. Qed.
Theorem MV_OK_wf : MV_OK m.
Proof.
unfold MV_OK. intros old old_size new_size dst. cbv zeta. intros SU LT NEQ ALD POS TOP FREE.
set (h := m_vmmaps m) in *.
set (onz := page_round_up_Z (bv_unsigned old_size)) in *. set (nnz := page_round_up_Z (bv_unsigned new_size)) in *.
set (old_n := Z_to_bv 64 onz) in *. set (new_n := Z_to_bv 64 nnz) in *.
pose proof (alloc_top_lt h) as ATOP. unfold two_pow_64 in ATOP. pose proof (word_range dst) as Rd.
assert (Honz : 0 <= onz) by (subst onz; unfold page_round_up_Z, page_size; pose proof (word_range old_size); apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia|lia]).
assert (Rn : bv_unsigned new_n = nnz) by (subst new_n; apply u64; lia).
unfold vm_backing_used, mremap_move_charge, mremap_model_next, vm_resize_backing, mremap_maps_next, vm_backed_maps.
cbv zeta. fold h.
change (m_vmmaps (with_vm_backing ?lz ?mt ?mm)) with (m_vmmaps mm).
change (m_vm_lazy (with_vm_backing ?lz ?mt ?mm)) with lz.
change (m_vm_materialized (with_vm_backing ?lz ?mt ?mm)) with mt.
change (m_vmmaps (with_vmmaps ?hh m)) with hh. cbn [vm_maps vm_noaccess].
change (m_vm_lazy (with_vmmaps ?hh m)) with (m_vm_lazy m). change (m_vm_materialized (with_vmmaps ?hh m)) with (m_vm_materialized m).
set (M := map_remove (vm_maps h) old). set (NA := vm_noaccess h). set (LZ := m_vm_lazy m). set (MT := m_vm_materialized m).
set (sl := mremap_source_lazy_b m old old_n).
set (olo := bv_unsigned old). set (dlo := bv_unsigned dst).
set (KL := maps_subtract LZ olo (olo + bv_unsigned old_n)).
set (KL' := maps_subtract KL dlo (dlo + bv_unsigned new_n)).
rewrite length_app.
match goal with |- context [List.map (move_page_base old dst) ?l] => set (FL := l) in * end.
pose proof (filter_length_le (page_outside_range dlo (dlo + bv_unsigned new_n)) (List.filter (page_outside_range olo (olo + bv_unsigned old_n)) MT)) as LEN1.
assert (LEN2 : length (if sl then List.map (move_page_base old dst) FL else []) = length (if sl then FL else [])) by (destruct sl; [apply length_map | reflexivity]).
rewrite LEN2.
assert (NWM : nwr M) by (subst M; unfold map_remove; apply nwr_filter; exact HWF).
assert (NWD : nwr ((dst, new_n) :: M)) by (constructor; [unfold phi, plo, psz; cbn [fst snd]; fold dlo; rewrite Rn; lia | exact NWM]).
rewrite (live_bytes_zsum (maps_subtract_all (maps_subtract_all ((dst, new_n) :: M) NA) _)) by (apply nwr_maps_subtract_all, nwr_maps_subtract_all; exact NWD).
rewrite (live_bytes_zsum (maps_subtract_all (maps_subtract_all M NA) KL)) by (apply nwr_maps_subtract_all, nwr_maps_subtract_all; exact NWM).
assert (IND : zsum (fun x => if (dlo <=? x) && (x <? dlo + nnz) then 1 else 0) 0 N64 = nnz) by (rewrite zsum_indicator; rewrite ?N64_Z; lia).
assert (FREE_M : forall x, dlo <= x < dlo + nnz -> owners M x = 0%nat).
{ intros x Hx. pose proof (owners_filter_le (fun p => negb (bv_eqb (fst p) old)) (vm_maps h) x) as LE.
change (List.filter (fun p => negb (bv_eqb (fst p) old)) (vm_maps h)) with M in LE.
rewrite (region_free_no_owner (vm_maps h) dst new_n x (region_free_app_r _ _ _ _ FREE)) in LE; [lia|].
apply owns_intro; fold dlo; [lia | rewrite Rn; lia]. }
enough (PW : forall x,
Z.of_nat (owners (maps_subtract_all (maps_subtract_all ((dst, new_n) :: M) NA) (if sl then lazy_interior dst new_n ++ KL' else KL')) x)
<= (if sl then 0 else if (dlo <=? x) && (x <? dlo + nnz) then 1 else 0) + Z.of_nat (owners (maps_subtract_all (maps_subtract_all M NA) KL) x)).
{ pose proof (zsum_le_all _ _ 0 N64 PW) as ZL. rewrite zsum_add in ZL.
clearbody sl. destruct sl.
- rewrite (zsum_zero (fun x => if true then 0 else if (dlo <=? x) && (x <? dlo + nnz) then 1 else 0)) in ZL; [|intros; reflexivity].
unfold page_size. lia.
- rewrite IND in ZL. unfold page_size. lia. }
intros x. clear IND LEN1 LEN2 FL.
rewrite !owners_maps_subtract_all; try (exact NWD || exact NWM || (apply nwr_maps_subtract_all; (exact NWD || exact NWM))).
rewrite owners_cons, owns_b_spec. cbn [fst snd]. fold dlo. rewrite Rn.
assert (CE : forall C, cov C x = negb (Nat.eqb (owners C x) 0)).
{ intros C; induction C as [|c C IH]; [reflexivity|]. rewrite cov_cons, owners_cons, IH. destruct (owns_b c x), (owners C x); reflexivity. }
assert (CKL' : cov KL' x = (negb ((dlo <=? x) && (x <? dlo + nnz)) && cov KL x)%bool).
{ rewrite !CE. subst KL'. rewrite owners_maps_subtract; [| lia | rewrite Rn; lia | left; rewrite Rn; lia]. rewrite Rn.
destruct ((dlo <=? x) && (x <? dlo + nnz))%bool, (owners KL x); reflexivity. }
clearbody sl. destruct sl.
-
unfold cov. rewrite existsb_app. fold (cov KL' x) (cov KL x) (cov NA x). rewrite CKL'.
assert (CI : existsb (fun c => owns_b c x) (lazy_interior dst new_n) = ((dlo <=? x) && (x <? dlo + nnz))%bool).
{ unfold lazy_interior. cbv zeta. fold dlo. rewrite Rn.
set (kd := dlo / page_size). set (kn := (bv_unsigned new_size + page_size - 1) / page_size).
assert (E1 : dlo = kd * page_size) by (pose proof (Z.div_mod dlo page_size ltac:(unfold page_size; lia)); unfold page_size in *; lia).
assert (E2 : nnz = kn * page_size) by reflexivity.
assert (E3 : (dlo + page_size - 1) / page_size = kd).
{ rewrite E1. replace (kd * page_size + page_size - 1) with (kd * page_size + (page_size - 1)) by lia.
rewrite Z.div_add_l by (unfold page_size; lia). rewrite Z.div_small by (unfold page_size; lia). lia. }
assert (E4 : (dlo + nnz) / page_size = kd + kn).
{ rewrite E1, E2. replace (kd * page_size + kn * page_size) with ((kd + kn) * page_size) by lia. apply Z.div_mul. unfold page_size; lia. }
rewrite E3, E4.
assert (TST : (kd + kn) * page_size = dlo + nnz) by (clear - E1 E2; lia).
rewrite TST. clear TST. rewrite <- E1.
destruct (Z.ltb_spec dlo (dlo + nnz)) as [LTk|LTk]; [|exfalso; clear - LT Honz LTk; lia].
cbn [existsb orb]. rewrite owns_b_spec. cbn [fst snd].
replace (dlo + nnz - dlo) with nnz by (clear; lia).
rewrite (u64 dlo) by (clear - Rd; lia). rewrite (u64 nnz) by (clear - TOP ATOP Rd LT Honz; lia).
destruct ((dlo <=? x) && (x <? dlo + nnz))%bool; reflexivity. }
rewrite CI. destruct (Z.leb_spec dlo x); destruct (Z.ltb_spec x (dlo + nnz)); cbn [negb andb orb];
destruct (cov KL x), (cov NA x); cbn [negb andb orb]; lia.
-
rewrite CKL'. destruct (Z.leb_spec dlo x); destruct (Z.ltb_spec x (dlo + nnz)); cbn [negb andb orb].
+ rewrite (FREE_M x) by lia. destruct (cov NA x); cbn; lia.
+ destruct (cov KL x), (cov NA x); cbn [negb andb orb]; lia.
+ destruct (cov KL x), (cov NA x); cbn [negb andb orb]; lia.
+ destruct (cov KL x), (cov NA x); cbn [negb andb orb]; lia.
Qed.
End MV.
