From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05 YM00 YM01 YO0i PlaceCap.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable.Z Require Import Placement.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition gap_end (p : word * word) : Z := bv_unsigned (fst p) + bv_unsigned (snd p).
Lemma gap_free_all : forall (l : list (word * word)) (lo n : word),
(forall p, In p l -> iv_overlap lo n (fst p) (snd p) = false) -> region_free l lo n = true.
Proof.
induction l as [|[b s] r IH]; intros lo n H; cbn [region_free]; [reflexivity|].
pose proof (H (b, s) (or_introl eq_refl)) as E. cbn [fst snd] in E. rewrite E. cbn [negb andb].
apply IH. intros p Hp. apply H. right. exact Hp.
Qed.
Lemma gap_free_mem : forall (l : list (word * word)) (lo n : word) p,
region_free l lo n = true -> In p l -> iv_overlap lo n (fst p) (snd p) = false.
Proof.
induction l as [|[b s] r IH]; intros lo n p H Hp; [destruct Hp|].
cbn [region_free] in H. apply andb_true_iff in H as [H1 H2].
destruct Hp as [E | Hp].
- subst p. cbn [fst snd]. apply negb_true_iff. exact H1.
- exact (IH lo n p H2 Hp).
Qed.
Lemma gap_free_hit : forall (l : list (word * word)) (lo n : word),
region_free l lo n = false -> exists p, In p l /\ iv_overlap lo n (fst p) (snd p) = true.
Proof.
induction l as [|[b s] r IH]; intros lo n H; cbn [region_free] in H; [discriminate|].
destruct (iv_overlap lo n b s) eqn:E.
- exists (b, s). split; [left; reflexivity | exact E].
- cbn [negb andb] in H. destruct (IH lo n H) as (p & Hp & Hq). exists p. split; [right; exact Hp | exact Hq].
Qed.
Lemma gap_filter_le : forall (f : word * word -> bool) (r : list (word * word)),
(length (List.filter f r) <= length r)%nat /\ ivs_bytes (List.filter f r) <= ivs_bytes r.
Proof.
intros f r. induction r as [|p r IH]; [cbn; lia|].
change (List.filter f (p :: r)) with (if f p then p :: List.filter f r else List.filter f r).
pose proof (u64_bounds (snd p)). destruct (f p); cbn [length ivs_bytes]; lia.
Qed.
Lemma gap_filter_drop : forall (f : word * word -> bool) (r : list (word * word)) p,
In p r -> f p = false ->
(length (List.filter f r) < length r)%nat /\ ivs_bytes (List.filter f r) + bv_unsigned (snd p) <= ivs_bytes r.
Proof.
intros f r p Hp Hf. induction r as [|q r IH]; [destruct Hp|].
pose proof (gap_filter_le f r) as L. pose proof (u64_bounds (snd q)).
change (List.filter f (q :: r)) with (if f q then q :: List.filter f r else List.filter f r).
destruct Hp as [E | Hp].
- subst q. rewrite Hf. cbn [length ivs_bytes]. lia.
- destruct (IH Hp) as [H1 H2]. destruct (f q); cbn [length ivs_bytes]; lia.
Qed.
Lemma gap_sweep {rc : RunCeil} : forall (nZ : Z) (ivs : list (word * word)), 0 < nZ ->
forall (k : nat) (r : list (word * word)) (lo : Z),
(length r <= k)%nat -> lo mod page_size = 0 -> page_size <= lo ->
lo + Z.of_nat (length r) * (nZ + page_size) + ivs_bytes r + nZ <= alloc_ceiling ->
(forall p, In p ivs -> In p r \/ gap_end p <= lo) ->
exists a : word,
bv_unsigned a mod page_size = 0 /\ 0 < bv_unsigned a /\
bv_unsigned a + nZ <= alloc_ceiling /\
region_free ivs a (Z_to_bv 64 nZ) = true.
Proof.
intros nZ ivs HnZ k. induction k as [|k IH]; intros r lo Hk Hal Hlo Hfit Hcov.
all: pose proof alloc_ceiling_lt as Hc; pose proof (ivs_bytes_nonneg r) as Hb;
assert (Hm : 0 <= Z.of_nat (length r) * (nZ + page_size)) by (unfold page_size; nia);
assert (Ulo : bv_unsigned (Z_to_bv 64 lo) = lo) by (apply Z_to_bv64_small; unfold page_size in *; lia);
assert (Un : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply Z_to_bv64_small; unfold page_size in *; lia);
destruct (region_free r (Z_to_bv 64 lo) (Z_to_bv 64 nZ)) eqn:Hf.
1,3: exists (Z_to_bv 64 lo); rewrite Ulo; split; [exact Hal|]; split; [unfold page_size in *; lia|]; split; [lia|];
apply gap_free_all; intros p Hp; destruct (Hcov p Hp) as [Hr | He];
[exact (gap_free_mem r _ _ p Hf Hr)
| unfold iv_overlap; rewrite Ulo; apply andb_false_iff; left; apply Z.ltb_ge; unfold gap_end in He; lia].
- destruct r as [|q r]; [cbn in Hf; discriminate Hf | cbn [length] in Hk; lia].
- destruct (gap_free_hit r _ _ Hf) as ([b s] & Hin & Hov). cbn [fst snd] in Hov.
unfold iv_overlap in Hov. rewrite Ulo, Un in Hov. apply andb_true_iff in Hov as [H1 H2].
apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
pose proof (u64_bounds b) as Ub. pose proof (u64_bounds s) as Us.
assert (Hx : exists lo', lo' mod page_size = 0 /\
bv_unsigned b + bv_unsigned s <= lo' <= bv_unsigned b + bv_unsigned s + 4095).
{ exists ((bv_unsigned b + bv_unsigned s + 4095) / 4096 * 4096). split; [unfold page_size; apply Z_mod_mult|].
pose proof (Z_div_mod_eq_full (bv_unsigned b + bv_unsigned s + 4095) 4096).
pose proof (Z.mod_pos_bound (bv_unsigned b + bv_unsigned s + 4095) 4096 ltac:(lia)). lia. }
destruct Hx as (lo' & Hal' & R1 & R2).
assert (Hfb : (lo' <? gap_end (b, s)) = false) by (unfold gap_end; cbn [fst snd]; apply Z.ltb_ge; lia).
destruct (gap_filter_drop (fun q => lo' <? gap_end q) r (b, s) Hin Hfb) as [D1 D2]. cbn [snd] in D2.
set (r' := List.filter (fun q => lo' <? gap_end q) r) in *.
pose proof (ivs_bytes_nonneg r') as Hb'.
assert (D3 : Z.of_nat (length r') + 1 <= Z.of_nat (length r)) by lia.
assert (Hm' : (Z.of_nat (length r') + 1) * (nZ + page_size) <= Z.of_nat (length r) * (nZ + page_size)).
{ apply Z.mul_le_mono_nonneg_r; [unfold page_size; lia | exact D3]. }
apply (IH r' lo').
+ lia.
+ exact Hal'.
+ unfold page_size in *. lia.
+ unfold page_size in *. nia.
+ intros p Hp. destruct (Hcov p Hp) as [Hr | He].
* destruct (lo' <? gap_end p) eqn:Ef.
-- left. unfold r'. apply List.filter_In. split; [exact Hr | exact Ef].
-- right. apply Z.ltb_ge in Ef. exact Ef.
* right. lia.
Qed.
(* [gap_sweep] with the floor it starts from in its conclusion: the sweep only moves up,
   so the address it finds is at or above [lo].  727298f3's grant test is Linux's own
   placement ([Checks.Placement.linux_place_is]), whose bottom-up fallback window starts at
   [Mmap.task_unmapped_base]; a gap found from that floor is a gap of that window. *)
Lemma gap_sweep_ge {rc : RunCeil} : forall (nZ : Z) (ivs : list (word * word)), 0 < nZ ->
forall (k : nat) (r : list (word * word)) (lo : Z),
(length r <= k)%nat -> lo mod page_size = 0 -> page_size <= lo ->
lo + Z.of_nat (length r) * (nZ + page_size) + ivs_bytes r + nZ <= alloc_ceiling ->
(forall p, In p ivs -> In p r \/ gap_end p <= lo) ->
exists a : word,
bv_unsigned a mod page_size = 0 /\ lo <= bv_unsigned a /\
bv_unsigned a + nZ <= alloc_ceiling /\
region_free ivs a (Z_to_bv 64 nZ) = true.
Proof.
intros nZ ivs HnZ k. induction k as [|k IH]; intros r lo Hk Hal Hlo Hfit Hcov.
all: pose proof alloc_ceiling_lt as Hc; pose proof (ivs_bytes_nonneg r) as Hb;
assert (Hm : 0 <= Z.of_nat (length r) * (nZ + page_size)) by (unfold page_size; nia);
assert (Ulo : bv_unsigned (Z_to_bv 64 lo) = lo) by (apply Z_to_bv64_small; unfold page_size in *; lia);
assert (Un : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply Z_to_bv64_small; unfold page_size in *; lia);
destruct (region_free r (Z_to_bv 64 lo) (Z_to_bv 64 nZ)) eqn:Hf.
1,3: exists (Z_to_bv 64 lo); rewrite Ulo; split; [exact Hal|]; split; [lia|]; split; [lia|];
apply gap_free_all; intros p Hp; destruct (Hcov p Hp) as [Hr | He];
[exact (gap_free_mem r _ _ p Hf Hr)
| unfold iv_overlap; rewrite Ulo; apply andb_false_iff; left; apply Z.ltb_ge; unfold gap_end in He; lia].
- destruct r as [|q r]; [cbn in Hf; discriminate Hf | cbn [length] in Hk; lia].
- destruct (gap_free_hit r _ _ Hf) as ([b s] & Hin & Hov). cbn [fst snd] in Hov.
unfold iv_overlap in Hov. rewrite Ulo, Un in Hov. apply andb_true_iff in Hov as [H1 H2].
apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
pose proof (u64_bounds b) as Ub. pose proof (u64_bounds s) as Us.
assert (Hx : exists lo', lo' mod page_size = 0 /\
bv_unsigned b + bv_unsigned s <= lo' <= bv_unsigned b + bv_unsigned s + 4095).
{ exists ((bv_unsigned b + bv_unsigned s + 4095) / 4096 * 4096). split; [unfold page_size; apply Z_mod_mult|].
pose proof (Z_div_mod_eq_full (bv_unsigned b + bv_unsigned s + 4095) 4096).
pose proof (Z.mod_pos_bound (bv_unsigned b + bv_unsigned s + 4095) 4096 ltac:(lia)). lia. }
destruct Hx as (lo' & Hal' & R1 & R2).
assert (Hfb : (lo' <? gap_end (b, s)) = false) by (unfold gap_end; cbn [fst snd]; apply Z.ltb_ge; lia).
destruct (gap_filter_drop (fun q => lo' <? gap_end q) r (b, s) Hin Hfb) as [D1 D2]. cbn [snd] in D2.
set (r' := List.filter (fun q => lo' <? gap_end q) r) in *.
pose proof (ivs_bytes_nonneg r') as Hb'.
assert (D3 : Z.of_nat (length r') + 1 <= Z.of_nat (length r)) by lia.
assert (Hm' : (Z.of_nat (length r') + 1) * (nZ + page_size) <= Z.of_nat (length r) * (nZ + page_size)).
{ apply Z.mul_le_mono_nonneg_r; [unfold page_size; lia | exact D3]. }
assert (P1 : (length r' <= k)%nat) by lia.
assert (P3 : page_size <= lo') by (unfold page_size in *; lia).
assert (P4 : lo' + Z.of_nat (length r') * (nZ + page_size) + ivs_bytes r' + nZ <= alloc_ceiling)
  by (unfold page_size in *; nia).
assert (P5 : forall p, In p ivs -> In p r' \/ gap_end p <= lo').
{ intros p Hp. destruct (Hcov p Hp) as [Hr | He].
- destruct (lo' <? gap_end p) eqn:Ef.
+ left. unfold r'. apply List.filter_In. split; [exact Hr | exact Ef].
+ right. apply Z.ltb_ge in Ef. exact Ef.
- right. lia. }
destruct (IH r' lo' P1 Hal' P3 P4 P5) as (a & A1 & A2 & A3 & A4).
exists a. split; [exact A1|]. split; [lia|]. split; [exact A3 | exact A4].
Qed.
Theorem region_free_exists_gap {rc : RunCeil} : forall (ivs : list (word * word)) (nZ : Z),
0 < nZ ->
(Z.of_nat (length ivs) + 1) * (nZ + page_size) + ivs_bytes ivs <= alloc_ceiling ->
exists a : word,
bv_unsigned a mod page_size = 0 /\ 0 < bv_unsigned a /\
bv_unsigned a + nZ <= alloc_ceiling /\
region_free ivs a (Z_to_bv 64 nZ) = true.
Proof.
intros ivs nZ HnZ Hfit.
apply (gap_sweep nZ ivs HnZ (length ivs) ivs page_size); [lia | reflexivity | lia | | intros p Hp; left; exact Hp].
unfold page_size in *. nia.
Qed.
Lemma place_floor_eq : LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.task_unmapped_base = PLACE_FLOOR.
Proof. reflexivity. Qed.
(* A gap for [nZ] bytes at or above Linux's bottom-up floor, under the slot budget: the sweep
   starts at [PLACE_FLOOR], which [slot_cap] leaves out of the ceiling. *)
Corollary region_free_exists_cap_ge {rc : RunCeil} : forall (ivs : list (word * word)) (R nZ : Z),
0 < nZ <= R ->
Z.of_nat (length ivs) <= slot_cap R ->
ivs_bytes ivs <= SLOT_BYTES ->
exists a : word,
bv_unsigned a mod page_size = 0 /\ PLACE_FLOOR <= bv_unsigned a /\
bv_unsigned a + nZ <= alloc_ceiling /\
region_free ivs a (Z_to_bv 64 nZ) = true.
Proof.
intros ivs R nZ HnZ Hc Hb.
pose proof alloc_ceiling_val as Hcv. pose proof (slot_round_ge R) as HR.
unfold slot_cap in Hc.
assert (Hd : 0 < page_round R + PGSZ) by (unfold PGSZ; lia).
pose proof (Z.mul_div_le (CEIL_MIN - SLOT_BYTES - PLACE_FLOOR) (page_round R + PGSZ) Hd) as M.
set (d := page_round R + PGSZ) in *. set (q := (CEIL_MIN - SLOT_BYTES - PLACE_FLOOR) / d) in *.
assert (P : (Z.of_nat (length ivs) + 1) * (nZ + page_size) <= q * d).
{ apply Z.mul_le_mono_nonneg; [lia | lia | unfold page_size; lia | unfold d, PGSZ, page_size; lia]. }
clearbody q. clearbody d.
assert (E : (Z.of_nat (length ivs) + 1) * (nZ + page_size) = Z.of_nat (length ivs) * (nZ + page_size) + nZ + page_size) by ring.
assert (Hps : page_size = 4096) by reflexivity.
destruct (gap_sweep_ge nZ ivs (proj1 HnZ) (length ivs) ivs PLACE_FLOOR) as (a & A1 & A2 & A3 & A4).
- lia.
- unfold PLACE_FLOOR. rewrite Hps. reflexivity.
- unfold PLACE_FLOOR. lia.
- unfold SLOT_BYTES, PLACE_FLOOR in *. lia.
- intros p Hp. left. exact Hp.
- exists a. split; [exact A1|]. split; [exact A2|]. split; [exact A3 | exact A4].
Qed.
(* The producer's route at 727298f3: a page-aligned gap in Linux's bottom-up window, below
   [alloc_top], is what [Z.Placement.linux_place_is_of_fit] turns into the address the
   placement rule itself gives for the call. *)
Lemma place_exists_cap {rc : RunCeil} : forall (h : VmMaps) (thp : bool) (hint : word) (R nZ : Z),
0 < nZ <= R -> nZ mod page_size = 0 ->
Z.of_nat (length (vm_reserved h ++ vm_maps h)) <= slot_cap R ->
ivs_bytes (vm_reserved h ++ vm_maps h) <= SLOT_BYTES ->
alloc_ceiling <= alloc_top h ->
exists a : word, LinuxProcessSemantics.LinuxProcessSem.Checks.Placement.linux_place_is h thp hint nZ a = true.
Proof.
intros h thp hint R nZ HnZ Hnal Hc Hb Htop.
destruct (region_free_exists_cap_ge _ R nZ HnZ Hc Hb) as (a & A1 & A2 & A3 & A4).
apply (linux_place_is_of_fit h thp hint nZ (bv_unsigned a) (proj1 HnZ) Hnal).
assert (RT : Z_to_bv 64 (bv_unsigned a) = a).
{ apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. }
unfold LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.gap_fits. rewrite RT, place_floor_eq.
split; [exact A1|]. split; [exact A2|]. split; [lia | exact A4].
Qed.
