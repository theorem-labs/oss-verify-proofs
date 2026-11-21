(* The placement policy finds room: under every claimed policy, an mmap or a moved mremap of a modest length has
   a policy address, and that address is one lps can return.  A counting fact over the current ledger, whatever
   placed it: a guarded fit exists in the policy's search window once the window holds the ledger's bytes, the
   two vDSO mappings and one gap per obstacle. *)
From Stdlib Require Import ZArith List Lia Bool Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM00 YM01 PlaceGap.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import RoomShapesDraft.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* The sweep of PlaceGap.gap_sweep in a window [lo, hi): the gap it finds starts at or above lo. *)
Lemma gap_sweep_win : forall (nZ hi : Z) (ivs : list (word * word)), 0 < nZ -> hi < 2 ^ 64 ->
  forall (k : nat) (r : list (word * word)) (lo : Z),
  (length r <= k)%nat -> lo mod page_size = 0 -> page_size <= lo ->
  lo + Z.of_nat (length r) * (nZ + page_size) + ivs_bytes r + nZ <= hi ->
  (forall p, In p ivs -> In p r \/ gap_end p <= lo) ->
  exists a : word,
    bv_unsigned a mod page_size = 0 /\ lo <= bv_unsigned a /\
    bv_unsigned a + nZ <= hi /\ region_free ivs a (Z_to_bv 64 nZ) = true.
Proof.
intros nZ hi ivs HnZ Hhi k. induction k as [|k IH]; intros r lo Hk Hal Hlo Hfit Hcov.
all: pose proof (ivs_bytes_nonneg r) as Hb;
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
destruct (IH r' lo') as (a & A1 & A2 & A3 & A4).
+ lia.
+ exact Hal'.
+ unfold page_size in *. lia.
+ unfold page_size in *. nia.
+ intros p Hp. destruct (Hcov p Hp) as [Hr | He].
* destruct (lo' <? gap_end p) eqn:Ef.
-- left. unfold r'. apply List.filter_In. split; [exact Hr | exact Ef].
-- right. apply Z.ltb_ge in Ef. exact Ef.
* right. lia.
+ exists a. split; [exact A1|]. split; [lia|]. split; [exact A3 | exact A4].
Qed.

(* The two vDSO mappings, as ledger-shaped obstacles. *)
Definition vdso_ivs (p : policy) : list (word * word) :=
  [(Z_to_bv 64 (p_vdso p), Z_to_bv 64 (p_vvar p)); (Z_to_bv 64 (p_vdso p + p_vvar p), Z_to_bv 64 (p_text p))].

Lemma task_unmapped_base_val : task_unmapped_base = 183251939328.
Proof. vm_compute. reflexivity. Qed.

(* The bounds policy_ok gives on the vDSO and the bases. *)
Lemma policy_vdso_bounds : forall p, policy_ok p ->
  page_size <= p_vdso p /\ 0 < p_vvar p <= 8 * page_size /\ 0 < p_text p <= 16 * page_size /\
  vdso_end p <= task_unmapped_base + legacy_rnd_max + TASK_SIZE.
Proof.
intros p (V & T & D & B & BR & M & _). destruct V as [V1 V2]. destruct T as [T1 T2]. destruct M as [[M1 M2] _].
rewrite task_unmapped_base_val in *. unfold vdso_end, legacy_rnd_max, TASK_SIZE, page_size in *.
destruct (p_legacy p) eqn:L; try rewrite L in B; try rewrite L in BR; destruct BR as [[BR1 BR2] _];
  (split; [lia | split; [lia | split; lia]]).
Qed.

Lemma policy_min_bounds : forall p, policy_ok p -> page_size <= p_min p <= 16 * page_size /\ p_min p mod page_size = 0.
Proof. intros p (_ & _ & _ & _ & _ & [M1 M2] & _). split; [exact M1 | exact M2]. Qed.

Lemma policy_base_bounds : forall p, policy_ok p ->
  p_base p mod page_size = 0 /\ page_size <= p_base p /\
  (p_legacy p = true -> p_base p <= task_unmapped_base + legacy_rnd_max).
Proof.
intros p (_ & _ & _ & _ & BR & _). rewrite task_unmapped_base_val in *. unfold legacy_rnd_max, page_size in *.
destruct (p_legacy p) eqn:L; try rewrite L in BR; destruct BR as [[B1 B2] B3].
- split; [exact B3|]. split; [lia|]. intros _. lia.
- split; [exact B3|]. split; [lia|]. discriminate.
Qed.

Lemma region_free_vdso_away : forall p (a : word) n, policy_ok p -> 0 <= n < 2 ^ 64 ->
  region_free (vdso_ivs p) a (Z_to_bv 64 n) = true ->
  away n a (p_vdso p) (p_vdso p + p_vvar p) /\ away n a (p_vdso p + p_vvar p) (vdso_end p).
Proof.
intros p a n Hp Hn H. pose proof (policy_vdso_bounds p Hp) as (D & V & T & E).
unfold vdso_end in E. rewrite task_unmapped_base_val in E. unfold TASK_SIZE, legacy_rnd_max, page_size in *.
unfold vdso_ivs in H. cbn [region_free] in H. rewrite !andb_true_iff, !negb_true_iff in H.
destruct H as (H1 & H2 & _). unfold iv_overlap in H1, H2.
repeat (rewrite Z_to_bv64_small in H1 by lia). repeat (rewrite Z_to_bv64_small in H2 by lia).
apply andb_false_iff in H1, H2. unfold away, vdso_end.
split; [destruct H1 as [H1 | H1] | destruct H2 as [H2 | H2]]; apply Z.ltb_ge in H1 || apply Z.ltb_ge in H2; lia.
Qed.

(* P3: a guarded fit of n bytes in [lo, hi), hi under alloc_top and under the stack's low end less the guard. *)
Theorem policy_fit_exists : forall h p s st n lo hi,
  policy_ok p -> 0 < n -> lo mod page_size = 0 -> page_size <= lo ->
  hi <= alloc_top h -> hi <= st - p_guard p ->
  lo + (Z.of_nat (length (vm_reserved h ++ vm_maps h)) + 2) * (n + page_size)
     + ivs_bytes (vm_reserved h ++ vm_maps h) + p_vvar p + p_text p + n <= hi ->
  exists a, fits h p s st true n lo (alloc_top h) a.
Proof.
intros h p s st n lo hi Hp Hn Hal Hlo Htop Hst Hfit.
set (L := vm_reserved h ++ vm_maps h) in *.
pose proof (policy_vdso_bounds p Hp) as (D & V & T & E).
assert (Hat : alloc_top h < 2 ^ 64) by (pose proof (alloc_top_lt h) as X; unfold two_pow_64 in X; lia).
assert (Hvb : ivs_bytes (vdso_ivs p) = p_vvar p + p_text p).
{ unfold vdso_ivs. cbn [ivs_bytes snd].
  rewrite task_unmapped_base_val in E. unfold vdso_end, TASK_SIZE, legacy_rnd_max, page_size in *.
  rewrite !Z_to_bv64_small by lia. lia. }
assert (Hlen : Z.of_nat (length (L ++ vdso_ivs p)) = Z.of_nat (length L) + 2).
{ rewrite length_app. unfold vdso_ivs. cbn [length]. lia. }
destruct (gap_sweep_win n hi (L ++ vdso_ivs p) Hn ltac:(lia) (length (L ++ vdso_ivs p)) (L ++ vdso_ivs p) lo
  (Nat.le_refl _) Hal Hlo) as (a & A1 & A2 & A3 & A4).
- rewrite Hlen, ivs_bytes_app, Hvb. lia.
- intros q Hq. left. exact Hq.
- rewrite region_free_app in A4. apply andb_true_iff in A4 as [F1 F2].
  destruct (region_free_vdso_away p a n Hp ltac:(lia) F2) as [W1 W2].
  exists a. unfold fits. split; [exact A1|]. split; [exact A2|]. split; [unfold page_size in *; lia|].
  split; [lia|]. split; [exact F1|]. split.
  + unfold off_vdso. cbv zeta. split; intros _.
    * replace (vdso_end p - p_text p - p_vvar p) with (p_vdso p) by (unfold vdso_end; lia).
      replace (vdso_end p - p_text p) with (p_vdso p + p_vvar p) by (unfold vdso_end; lia). exact W1.
    * replace (vdso_end p - p_text p) with (p_vdso p + p_vvar p) by (unfold vdso_end; lia). exact W2.
  + intros _. unfold clear_of_stack. left. lia.
Qed.

(* What lps's fresh-grant choice asks of an address (the guard of mmap_spec's fresh arms, mremap_fresh_b's
   placement part). *)
Definition lps_free (h : VmMaps) (n : Z) (a : word) : Prop :=
  bv_unsigned a mod page_size = 0 /\ 0 < bv_unsigned a /\ bv_unsigned a + n <= alloc_top h /\
  region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 n) = true.

Lemma fits_lps_free : forall h p s st g n lo top a, top <= alloc_top h -> fits h p s st g n lo top a -> lps_free h n a.
Proof.
intros h p s st g n lo top a Ht (A1 & _ & A3 & A4 & A5 & _). unfold lps_free.
split; [exact A1|]. split; [exact A3|]. split; [lia | exact A5].
Qed.

(* The bottom of the policy's search window: the legacy base, or TASK_UNMAPPED_BASE where the top-down search
   falls back to its bottom-up pass. *)
Definition win_lo (p : policy) : Z :=
  if p_legacy p then Z.max (p_min p) (p_base p) else Z.max (p_min p) task_unmapped_base.

(* Room for n bytes in the window, below alloc_top and below the stack's low end less the guard. *)
Definition win_room (h : VmMaps) (p : policy) (st n : Z) : Prop :=
  win_lo p + (Z.of_nat (length (vm_reserved h ++ vm_maps h)) + 2) * (n + page_size)
    + ivs_bytes (vm_reserved h ++ vm_maps h) + p_vvar p + p_text p + n <= Z.min (alloc_top h) (st - p_guard p).

(* The window's size under every claimed policy, less one page of rounding: the legacy base is at most
   TASK_UNMAPPED_BASE + 2^45 (the top-down fallback starts at TASK_UNMAPPED_BASE), and the window's top is at least
   the run's ceiling less the stack guard and the stack's low-end rounding. *)
Definition WNUM : Z := 140735332483072 - page_size - stack_guard_max - (task_unmapped_base + legacy_rnd_max).

Lemma policy_guard_bounds : forall p, policy_ok p -> 0 <= p_guard p <= stack_guard_max.
Proof. intros p (_ & _ & _ & _ & _ & _ & G & _). exact G. Qed.

(* The counting premise from counts of the ledger: K entries, B bytes. *)
Theorem win_room_of_counts : forall h p st n K B,
  policy_ok p -> page_round_down_Z (alloc_top h) <= st -> 140735332483072 <= alloc_top h -> 0 <= n ->
  Z.of_nat (length (vm_reserved h ++ vm_maps h)) <= K -> ivs_bytes (vm_reserved h ++ vm_maps h) <= B ->
  (K + 2) * (n + page_size) + B + 24 * page_size + n <= WNUM ->
  win_room h p st n.
Proof.
intros h p st n K B Hp Hst Hc Hn HK HB H. unfold win_room, WNUM in *.
pose proof (policy_min_bounds p Hp) as ([M1 M2] & _). pose proof (policy_base_bounds p Hp) as (_ & _ & BL).
pose proof (policy_vdso_bounds p Hp) as (_ & [V1 V2] & [T1 T2] & _). pose proof (policy_guard_bounds p Hp) as [G1 G2].
assert (Hlo : win_lo p <= task_unmapped_base + legacy_rnd_max).
{ unfold win_lo. rewrite task_unmapped_base_val in *. unfold legacy_rnd_max, page_size in *.
  destruct (p_legacy p) eqn:L.
  - specialize (BL eq_refl). apply Z.max_lub; lia.
  - apply Z.max_lub; lia. }
assert (Hrd : alloc_top h - 4095 <= page_round_down_Z (alloc_top h)).
{ unfold page_round_down_Z, page_size. pose proof (Z_div_mod_eq_full (alloc_top h) 4096).
  pose proof (Z.mod_pos_bound (alloc_top h) 4096 ltac:(lia)). lia. }
assert (HKm : (Z.of_nat (length (vm_reserved h ++ vm_maps h)) + 2) * (n + page_size) <= (K + 2) * (n + page_size)).
{ apply Z.mul_le_mono_nonneg_r; unfold page_size; lia. }
unfold stack_guard_max, page_size in *. lia.
Qed.

Lemma win_lo_page : forall p, policy_ok p -> win_lo p mod page_size = 0 /\ page_size <= win_lo p.
Proof.
intros p Hp. pose proof (policy_min_bounds p Hp) as ([M1 M2] & M3). pose proof (policy_base_bounds p Hp) as (B1 & B2 & _).
assert (T : task_unmapped_base mod page_size = 0) by (vm_compute; reflexivity).
assert (T2 : page_size <= task_unmapped_base) by (rewrite task_unmapped_base_val; unfold page_size; lia).
unfold win_lo. destruct (p_legacy p).
- destruct (Z.max_spec (p_min p) (p_base p)) as [[_ E] | [_ E]]; rewrite E; split; first [assumption | lia].
- destruct (Z.max_spec (p_min p) task_unmapped_base) as [[_ E] | [_ E]]; rewrite E; split; first [assumption | lia].
Qed.

(* P4a: under every claimed policy the plain search answers. *)
Theorem policy_search_exists : forall h p s st n, policy_ok p -> 0 < n -> win_room h p st n ->
  exists a, search_addr h p s st n a.
Proof.
intros h p s st n Hp Hn H. destruct (win_lo_page p Hp) as [Hal Hlo].
destruct (policy_fit_exists h p s st n (win_lo p) (Z.min (alloc_top h) (st - p_guard p)) Hp Hn Hal Hlo
  (Z.le_min_l _ _) (Z.le_min_r _ _) H) as (a & Ha).
unfold win_lo in Ha. destruct (p_legacy p) eqn:L.
- exact (search_addr_exists_legacy h p s st n a L Ha).
- exact (search_addr_exists_topdown h p s st n a L ltac:(lia) Ha).
Qed.

Lemma region_free_sub : forall l (r a : word) m n, 0 < n < 2 ^ 64 -> 0 <= m < 2 ^ 64 ->
  bv_unsigned r <= bv_unsigned a -> bv_unsigned a + n <= bv_unsigned r + m ->
  region_free l r (Z_to_bv 64 m) = true -> region_free l a (Z_to_bv 64 n) = true.
Proof.
intros l r a m n Hn Hm H1 H2 H. apply gap_free_all. intros q Hq.
pose proof (gap_free_mem l r _ q H Hq) as E. unfold iv_overlap in *.
rewrite Z_to_bv64_small in * by lia.
apply andb_false_iff in E. apply andb_false_iff.
destruct E as [E | E]; apply Z.ltb_ge in E; [left | right]; apply Z.ltb_ge; lia.
Qed.

Lemma thp_align_bounds : forall p r, 0 <= r ->
  r <= thp_align p r <= r + pmd_size /\ thp_align p r mod pmd_size = 0.
Proof.
intros p r Hr. unfold thp_align, pmd_size.
pose proof (Z.mod_pos_bound r 0x200000 ltac:(lia)) as M.
pose proof (Z_div_mod_eq_full r 0x200000) as D.
set (q := r / 0x200000) in *. set (m := r mod 0x200000) in *.
destruct (p_legacy p).
- destruct (Z.eq_dec m 0) as [E | E].
  + rewrite E, Z.sub_0_r, Z_mod_same_full, Z.add_0_r. split; [lia|]. rewrite D, E, Z.add_0_r.
    rewrite Z.mul_comm. apply Z_mod_mult.
  + rewrite (Z.mod_small (0x200000 - m)) by lia. split; [lia|].
    replace (r + (0x200000 - m)) with ((q + 1) * 0x200000) by lia. apply Z_mod_mult.
- split; [lia|]. replace (r + (0x200000 - m)) with ((q + 1) * 0x200000) by lia. apply Z_mod_mult.
Qed.

Lemma pmd_page : forall z, z mod pmd_size = 0 -> z mod page_size = 0.
Proof.
intros z H. unfold pmd_size, page_size in *. apply Z.mod_divide in H; [|lia]. destruct H as [k ->].
replace (k * 2097152) with ((k * 512) * 4096) by lia. apply Z_mod_mult.
Qed.

(* P4b: the policy's fresh address exists, and lps may return it.  Room for the plain length suffices: when the
   2 MiB-padded search answers, its range holds the aligned address; when it does not, the plain search is used. *)
Theorem policy_fresh_exists : forall h p s st n, policy_ok p -> 0 < n -> win_room h p st n ->
  exists a, fresh_addr h p s st n a /\ lps_free h n a.
Proof.
intros h p s st n Hp Hn Hplain.
assert (Hat : alloc_top h < 2 ^ 64) by (pose proof (alloc_top_lt h) as X; unfold two_pow_64 in X; lia).
assert (Plain : exists a, search_addr h p s st n a /\ lps_free h n a).
{ destruct (policy_search_exists h p s st n Hp Hn Hplain) as (a & Ha). exists a. split; [exact Ha|].
  exact (fits_lps_free h p s st true n (p_min p) (alloc_top h) a (Z.le_refl _) (search_addr_fits h p s st n a Ha)). }
unfold fresh_addr.
destruct (andb (p_thp p) (andb (Z.ltb 0 n) (Z.eqb (n mod pmd_size) 0))).
- destruct (classic (exists ret, search_addr h p s st (n + pmd_size) ret)) as [(ret & Hr) | Hno].
  + pose proof (fits_lps_free h p s st true (n + pmd_size) (p_min p) (alloc_top h) ret (Z.le_refl _)
      (search_addr_fits h p s st (n + pmd_size) ret Hr)) as (R1 & R2 & R3 & R4).
    pose proof (u64_bounds ret) as Ur.
    destruct (thp_align_bounds p (bv_unsigned ret) ltac:(lia)) as [[T1 T2] T3].
    assert (Ua : bv_unsigned (Z_to_bv 64 (thp_align p (bv_unsigned ret))) = thp_align p (bv_unsigned ret)).
    { apply Z_to_bv64_small. unfold pmd_size in *. lia. }
    exists (Z_to_bv 64 (thp_align p (bv_unsigned ret))). split.
    * left. exists ret. split; [exact Hr | exact Ua].
    * unfold lps_free. rewrite Ua. split; [exact (pmd_page _ T3)|]. split; [lia|]. split; [lia|].
      apply (region_free_sub _ ret _ (n + pmd_size) n); [unfold pmd_size in *; lia | unfold pmd_size in *; lia | lia | lia | exact R4].
  + destruct Plain as (a & Ha & Hf). exists a. split; [right; split; [intros ret Hr; apply Hno; exists ret; exact Hr | exact Ha] | exact Hf].
- exact Plain.
Qed.

(* P4c: the address the policy gives an mmap with hint [hint], and lps may return it. *)
Theorem policy_mmap_addr_exists : forall h p s st hint n, policy_ok p -> 0 < n -> win_room h p st n ->
  exists a, mmap_addr h p s st hint n a /\ lps_free h n a.
Proof.
intros h p s st hint n Hp Hn Hplain. unfold mmap_addr. cbv zeta.
destruct (Z.eqb (page_round_down_Z (bv_unsigned hint)) 0).
- exact (policy_fresh_exists h p s st n Hp Hn Hplain).
- destruct (classic (exists w, bv_unsigned w = Z.max (page_round_down_Z (bv_unsigned hint)) (p_min p)
                               /\ fits h p s st true n (p_min p) (alloc_top h) w)) as [(w & Hw & Hf) | Hno].
  + exists w. split; [left; split; [exists w; split; [exact Hw | exact Hf] | exact Hw]|].
    exact (fits_lps_free h p s st true n (p_min p) (alloc_top h) w (Z.le_refl _) Hf).
  + destruct (policy_search_exists h p s st n Hp Hn Hplain) as (a & Ha). exists a. split.
    * right. split; [exact Hno | exact Ha].
    * exact (fits_lps_free h p s st true n (p_min p) (alloc_top h) a (Z.le_refl _) (search_addr_fits h p s st n a Ha)).
Qed.

(* ** Allocator nodes: the policy's step is one of lps's (under the alloc-forced-only filter) *)

From LinuxProcessSemantics.Riscv Require Import Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0v YP0n YN02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.Z Require Import Placement.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Uniform.
Local Open Scope Z_scope.

(* ========================================================================
   08b1429, the revision: [grant_ok] (Reusable/YK0v.v:102-107) and [place_ok]
   (Reusable/YP0n.v:1648-1649) no longer admit ANY free range.  Their leading
   conjunct is [Checks.Placement.linux_place_is], which PINS the address:

     Definition linux_place_is (h : VmMaps) (thp : bool) (hint : word) (nZ : Z)
         (r : word) : bool :=
       match linux_place_b h thp hint nZ with
       | Some a => (a =? bv_unsigned r)%Z
       | None => false
       end.
     75d69e00:theories/LinuxProcessSem/Checks/Placement.v:1012-1017

   and [linux_place_unique] (:776) makes that one address unique.  So an mmap
   node's only non-error answer is now Linux's address, and [canonical_ret]'s
   mmap arm (RoomShapesDraft.v:387-390) has to hold OF THAT ADDRESS.  The
   lemmas below carry as far as that is possible; what is left is named
   [PolicyAdmitsLinuxPick] and reported at the foot of this file.
   ======================================================================== *)

Lemma page_round_up_aligned : forall z, page_round_up_Z z mod page_size = 0.
Proof. intro z. unfold page_round_up_Z. apply Z_mod_mult. Qed.

(* The unit's TASK_UNMAPPED_BASE is the model's
   (75d69e00:theories/LinuxProcessSem/Sys/Mm/Mmap.v:1105), as a closed computation. *)
Lemma tub_model_eq : task_unmapped_base = Mmap.task_unmapped_base.
Proof. vm_compute. reflexivity. Qed.

(* Every claimed policy searches at or above TASK_UNMAPPED_BASE: a legacy base is drawn
   from [task_unmapped_base, task_unmapped_base + 2^45] and the top-down window's
   fallback floor is TASK_UNMAPPED_BASE itself. *)
Lemma tub_le_win_lo : forall p, policy_ok p -> task_unmapped_base <= win_lo p.
Proof.
intros p (_ & _ & _ & _ & BR & _). unfold win_lo.
destruct (p_legacy p) eqn:L; try rewrite L in BR; destruct BR as [[B1 B2] _]; lia.
Qed.

(* Room in the policy's window is room in Linux's BOTTOM-UP window, so Linux's search
   cannot come back empty.  This is ALL that [win_room] gives about Linux's answer: that
   it exists.  It says nothing about where it lands, which is the donor's own reading of
   [linux_place_exists] (75d69e00:theories/LinuxProcessSem/Checks/Placement.v:858-866). *)
Lemma policy_place_available : forall h p st n thp hint,
  policy_ok p -> 0 < n -> n mod page_size = 0 -> win_room h p st n ->
  vm_place_available h thp hint n = true.
Proof.
intros h p st n thp hint Hp Hn Hnal HW.
destruct (win_lo_page p Hp) as [Hal Hlo].
destruct (policy_fit_exists h p full_strip st n (win_lo p) (Z.min (alloc_top h) (st - p_guard p))
  Hp Hn Hal Hlo (Z.le_min_l _ _) (Z.le_min_r _ _) HW) as (a & A1 & A2 & A3 & A4 & A5 & _).
pose proof (tub_le_win_lo p Hp) as Htub.
assert (Ht1 : task_unmapped_base <= bv_unsigned a) by lia.
assert (Hgapb : Checks.Placement.gap_fits_b (vm_reserved h ++ vm_maps h)
                  task_unmapped_base (alloc_top h) n (bv_unsigned a) = true).
{ unfold Checks.Placement.gap_fits_b.
  rewrite (proj2 (Z.eqb_eq _ _) A1), (proj2 (Z.leb_le _ _) Ht1), (proj2 (Z.leb_le _ _) A4).
  cbn [andb]. rewrite Z_to_bv_bv_unsigned. exact A5. }
pose proof (proj1 (Checks.Placement.gap_fits_b_iff _ _ _ _ _) Hgapb) as Hgap.
rewrite tub_model_eq in Hgap.
unfold vm_place_available.
destruct (Checks.Placement.linux_place_b h thp hint n) as [q|] eqn:Hq; [reflexivity|].
exfalso.
destruct (Checks.Placement.linux_place_exists h thp hint n Hn Hnal
            ltac:(exists (bv_unsigned a); right; exact Hgap)) as (b & Hb).
exact (proj1 (proj2 (Checks.Placement.linux_place_b_spec h thp hint n Hn Hnal)) Hq b Hb).
Qed.

(* THE OBLIGATION THE REVISION LEAVES, as one named statement: the policy admits the
   address Linux picks.  Both mmap nodes need exactly this and nothing else.

   POLICY-PINNED-TO-MODEL (conjuncts (5) and (6) on the arm-by-arm derivation in
   [pick_is_policy_addr] below).
   The old form of this statement, quantified over every [policy_ok] policy with
   nothing tying it to the model, is FALSE at the revision and was reported here rather than
   proved: [Checks.Placement.linux_place_is] (75d69e00:Checks/Placement.v:1012-1017)
   PINS the address and [linux_place_unique] (:776) makes it unique, so two policies
   with different windows pin two different addresses and at most one can be Linux's.
   [RoomShapesDraft.policy_pinned_h] carries the six conjuncts that tie the policy to
   the model; they are conjuncts of the predicate the producers already build, never a
   free-standing hypothesis, so the obligation moves INWARD to the producers. *)
Definition PolicyAdmitsLinuxPick : Prop :=
  forall h p s st thp hint n,
    policy_ok p -> policy_pinned_h h thp p s ->
    page_round_down_Z (alloc_top h) <= st ->
    0 < n -> n mod page_size = 0 -> win_room h p st n ->
    mmap_addr h p s st hint n (vm_place_pick h thp hint n).

Section N.
Context {fx : YK11.FPState}.
Variable segs : list Segment.

Lemma ret_of_adv : forall regs pc mem rom eff1 eff2,
  advance_past_svc (apply_effect (pend_at regs pc mem rom) eff1)
  = advance_past_svc (apply_effect (pend_at regs pc mem rom) eff2) -> eff_ret eff1 = eff_ret eff2.
Proof.
intros regs pc mem rom eff1 eff2 E. rewrite !adv_pend in E. unfold mkst in E.
apply (f_equal (fun ms => reg_get (ms_regs ms) 10)) in E. cbn [ms_regs] in E.
rewrite !regupd_same in E. exact E.
Qed.

(* A step from a pending system call to an advanced configuration is the policy's when its answer is. *)
Lemma canon_step_of_sstep : forall p s st regs pc mem rom model e c2,
  sstep_cfg segs ACFG (mkCfg (pend_at regs pc mem rom) model) e (SNext c2) ->
  ms_svc_pending (cfg_ms c2) = None ->
  (forall eff m'', c2 = mkCfg (advance_past_svc (apply_effect (pend_at regs pc mem rom) eff)) m'' ->
     canonical_ret p s st (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) model (eff_ret eff)) ->
  canon_can_step p s st segs ACFG (mkCfg (pend_at regs pc mem rom) model).
Proof.
intros p s st regs pc mem rom model e c2 H Hn Hc.
exists e, c2. split; [exact H|].
intros x8 len (_ & Hsv & _). cbn [cfg_ms] in Hsv. rewrite pend_svc in Hsv. injection Hsv as <-.
remember (mkCfg (pend_at regs pc mem rom) model) as c0 eqn:Ec.
remember (SNext c2) as r0 eqn:Er.
destruct H; try discriminate Er; injection Ec as -> ->.
- rewrite pend_svc in H0. discriminate H0.
- (* 727298f3: the vDSO-call arm, like the instruction arm, needs no syscall pending *)
  rewrite pend_svc in H0. discriminate H0.
- injection Er as <-. rewrite pend_svc in H0. injection H0 as <-.
  exists eff, model', evs, model''. split; [exact H1|]. split; [reflexivity|].
  exact (Hc eff model'' eq_refl).
- injection Er as <-. cbn [cfg_ms] in Hn. rewrite pend_svc in Hn. discriminate Hn.
- injection Er as <-. cbn [cfg_ms] in Hn. rewrite pend_svc in Hn. discriminate Hn.
Qed.

Lemma errno_answer_enomem : errno_answer (errno_ret ENOMEM).
Proof. unfold errno_answer. vm_compute. reflexivity. Qed.

Lemma page_round_up_pos : forall w : word, w <> Z_to_bv 64 0 -> 0 < page_round_up_Z (bv_unsigned w).
Proof.
intros w Hw. assert (L0 : 0 < bv_unsigned w).
{ pose proof (u64_bounds w). destruct (Z.eq_dec (bv_unsigned w) 0) as [E|E]; [|lia].
  exfalso. apply Hw. apply bv_eq. rewrite E, Z_to_bv64_small; [reflexivity | lia]. }
unfold page_round_up_Z, page_size. pose proof (Z.div_le_mono 4096 (bv_unsigned w + 4096 - 1) 4096 ltac:(lia) ltac:(lia)) as D.
rewrite Z.div_same in D by lia. lia.
Qed.

(* P5, mmap PROT_READ|PROT_WRITE: with room in the window, Linux's address is a grant, or, when
   the budget refuses, the refusal is lps's only answer.  Everything but [Hadm] is proved here. *)
Lemma canon_fit_mmap_rw_from_pick : forall regs pc mem rom model,
  PolicyAdmitsLinuxPick ->
  m_halted model = None -> m_vm_lazy model = [] ->
  bv_unsigned (getr regs 17) = 222 ->
  getr regs 11 <> Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 3 ->
  getr regs 13 = Z_to_bv 64 34 -> getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  place_declined_b (m_kernel model) (m_vmmaps model) (getr regs 10)
    (page_round_up_Z (bv_unsigned (getr regs 11))) = false ->
  (forall p st, policy_ok p -> page_round_down_Z (alloc_top (m_vmmaps model)) <= st ->
     vm_limit (m_vmmaps model) <= AgreeLim.LIM_AG ->
     win_room (m_vmmaps model) p st (page_round_up_Z (bv_unsigned (getr regs 11)))) ->
  canon_fit_at segs (mkCfg (pend_at regs pc mem rom) model).
Proof.
intros regs pc mem rom model Hadm Hh Hlz Hno Hlen Hprot Hflags Hfd Hoff Hdecl HW p s st Hp Hpin Hst Hlim x8 len _ _.
destruct (node_mmap_rw04 segs regs pc mem rom model Hh Hlz Hno Hlen Hprot Hflags Hfd Hoff Hdecl) as [Hs _].
pose proof (page_round_up_pos (getr regs 11) Hlen) as Hn.
assert (Hnal : page_round_up_Z (bv_unsigned (getr regs 11)) mod page_size = 0)
  by apply page_round_up_aligned.
set (nZ := page_round_up_Z (bv_unsigned (getr regs 11))) in *.
cbn [cfg_model] in Hst, Hlim.
pose proof (HW p st Hp Hst Hlim) as HR.
destruct (vm_backing_used model + nZ <=? vm_limit (m_vmmaps model)) eqn:Hb.
- pose proof (policy_place_available (m_vmmaps model) p st nZ (kb_thp (m_kernel model))
    (getr regs 10) Hp Hn Hnal HR) as Hav.
  pose proof (vm_place_pick_ok (m_vmmaps model) (kb_thp (m_kernel model)) (getr regs 10) nZ
    Hn Hnal Hav) as Hpl.
  set (g := vm_place_pick (m_vmmaps model) (kb_thp (m_kernel model)) (getr regs 10) nZ) in *.
  assert (G : grant_ok (getr regs 10) model g nZ = true)
    by exact (grant_ok_intro (getr regs 10) model g nZ Hn Hnal Hpl (proj1 (Z.leb_le _ _) Hb)).
  apply (canon_step_of_sstep p s st regs pc mem rom model [] _ (Hs (inr (exist _ g G))) eq_refl).
  intros eff m'' E. apply (f_equal cfg_ms) in E. cbn [cfg_ms] in E. apply ret_of_adv in E. rewrite <- E.
  cbn [mmap_rw_ef04 eff_ret proj1_sig].
  right. left. split; [rewrite si_sysno; exact Hno|]. rewrite si_arg0, si_arg1.
  exact (Hadm (m_vmmaps model) p s st (kb_thp (m_kernel model)) (getr regs 10) nZ Hp Hpin Hst Hn Hnal HR).
- assert (Hr : mmap_grant_refusable (Z_to_bv 64 34) (getr regs 10) model nZ = true).
  { unfold mmap_grant_refusable, Mmap.mmap_noreserve_backed_ok.
    replace (Mmap.mmap_noreserve_b (Z_to_bv 64 34)) with false by (vm_compute; reflexivity).
    cbv beta iota. rewrite Hb. reflexivity. }
  apply (canon_step_of_sstep p s st regs pc mem rom model [] _ (Hs (inl (exist _ ENOMEM (conj ENOMEM_in_mmap_errnos Hr)))) eq_refl).
  intros eff m'' E. apply (f_equal cfg_ms) in E. cbn [cfg_ms] in E. apply ret_of_adv in E. rewrite <- E. cbn [mmap_rw_ef04 eff_ret proj1_sig].
  left. exact errno_answer_enomem.
Qed.

(* P5, mmap PROT_NONE: Linux's address is a reservation lps may grant (no budget for a
   reservation).  Same single obligation [Hadm]. *)
Lemma canon_fit_mmap_none_from_pick : forall regs pc mem rom model,
  PolicyAdmitsLinuxPick ->
  m_halted model = None -> m_vm_lazy model = [] ->
  bv_unsigned (getr regs 17) = 222 ->
  getr regs 11 <> Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 34 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  place_declined_b (m_kernel model) (m_vmmaps model) (getr regs 10)
    (page_round_up_Z (bv_unsigned (getr regs 11))) = false ->
  (forall p st, policy_ok p -> page_round_down_Z (alloc_top (m_vmmaps model)) <= st ->
     vm_limit (m_vmmaps model) <= AgreeLim.LIM_AG ->
     win_room (m_vmmaps model) p st (page_round_up_Z (bv_unsigned (getr regs 11)))) ->
  canon_fit_at segs (mkCfg (pend_at regs pc mem rom) model).
Proof.
intros regs pc mem rom model Hadm Hh Hlz Hno Hlen Hprot Hflags Hfd Hoff Hdecl HW p s st Hp Hpin Hst Hlim x8 len _ _.
destruct (node_mmap_none04 segs regs pc mem rom model Hh Hlz Hno Hlen Hprot Hflags Hfd Hoff Hdecl) as [Hs _].
pose proof (page_round_up_pos (getr regs 11) Hlen) as Hn.
assert (Hnal : page_round_up_Z (bv_unsigned (getr regs 11)) mod page_size = 0)
  by apply page_round_up_aligned.
set (nZ := page_round_up_Z (bv_unsigned (getr regs 11))) in *.
cbn [cfg_model] in Hst, Hlim.
pose proof (HW p st Hp Hst Hlim) as HR.
pose proof (policy_place_available (m_vmmaps model) p st nZ (kb_thp (m_kernel model))
  (getr regs 10) Hp Hn Hnal HR) as Hav.
pose proof (vm_place_pick_ok (m_vmmaps model) (kb_thp (m_kernel model)) (getr regs 10) nZ
  Hn Hnal Hav) as Hpl.
set (g := vm_place_pick (m_vmmaps model) (kb_thp (m_kernel model)) (getr regs 10) nZ) in *.
assert (G : place_ok (getr regs 10) model g nZ = true) by exact Hpl.
apply (canon_step_of_sstep p s st regs pc mem rom model [] _ (Hs (inr (exist _ g G))) eq_refl).
intros eff m'' E. apply (f_equal cfg_ms) in E. cbn [cfg_ms] in E. apply ret_of_adv in E. rewrite <- E.
cbn [mmap_none_ef04 eff_ret proj1_sig].
right. left. split; [rewrite si_sysno; exact Hno|]. rewrite si_arg0, si_arg1.
exact (Hadm (m_vmmaps model) p s st (kb_thp (m_kernel model)) (getr regs 10) nZ Hp Hpin Hst Hn Hnal HR).
Qed.

(* P1, brk: canonical_ret's brk arm takes every answer, and every step of a brk node is a syscall step. *)
Theorem canon_fit_brk : forall regs pc mem rom model,
  m_halted model = None -> m_vm_lazy model = [] ->
  bv_unsigned (getr regs 17) = 214 ->
  canon_fit_at segs (mkCfg (pend_at regs pc mem rom) model).
Proof.
intros regs pc mem rom model Hh Hlz Hno p s st Hp _ Hst _ x8 len _ (e & c' & Hs).
destruct (node_brk segs regs pc mem rom model Hh Hlz Hno) as [_ [Hc _]].
destruct (Hc e (SNext c') Hs) as (i & -> & E). injection E as ->.
apply (canon_step_of_sstep p s st regs pc mem rom model [] _ Hs).
- unfold brk_nx. cbv zeta. destruct i; reflexivity.
- intros eff m'' _. right. right. right. rewrite si_sysno. exact Hno.
Qed.

(* Non-placement nodes (munmap, mprotect, MAP_FIXED, brk query, instructions). *)
Lemma canon_fit_svc_nonplacement : forall ms model,
  (forall x8, ms_svc_pending ms = Some x8 -> RoomShapesDraft.placement_len (sys_input segs ms x8) model = None) ->
  canon_fit_at segs (mkCfg ms model).
Proof.
intros ms model H. apply canon_fit_at_nonplacement. intros x8 len (_ & Hs & Hl). cbn [cfg_ms cfg_model] in *.
rewrite (H x8 Hs) in Hl. discriminate Hl.
Qed.

(* ========================================================================
   POLICY-PINNED-TO-MODEL: [PolicyAdmitsLinuxPick], PROVED.

   WHAT WAS FALSE, AND WHY IT IS NOT ANY MORE.  The old statement quantified
   over EVERY [policy_ok p] with nothing tying [p] to the model.  The revision PINS the
   address -- [Checks.Placement.linux_place_is]
   (75d69e00:theories/LinuxProcessSem/Checks/Placement.v:1012-1017) decides one
   address and [linux_place_unique] (:776) makes it the only one -- so two
   policies with different windows pin two different addresses and at most one
   can be Linux's.  [RoomShapesDraft.policy_pinned_h] carries six conjuncts
   that tie the policy to the model, and [canon_fit_at] now builds them, so the
   obligation sits with the producers rather than with a hypothesis.

   THE ARM-BY-ARM DERIVATION, separating what the four model-tying conjuncts of
   the central ruling already close from the two this unit had to add.

   CLOSED BY [p_legacy = false], [p_min = page_size],
   [p_base = vm_mmap_base], [p_thp = kb_thp], with no further conjunct:
     - THP.  [RoomShapesDraft.thp_align]'s non-legacy branch is
       [ret + (pmd_size - ret mod pmd_size)], which at [ret mod pmd = 0] is
       [ret + pmd]: the model's two-case [Mmap.thp_align]
       (75d69e00:Sys/Mm/Mmap.v:1151-1153).  [pin_thp_align] below.
     - THE HINT.  [mmap_addr]'s [down] IS [Mmap.hint_address] (:1164-1165), and
       [Z.max down page_size] is [down] for a nonzero page multiple.  Same
       window [[page_size, alloc_top)].
     - THE WINDOW TOP.  [State.mmap_top h] is
       [Z.min (vm_mmap_base h) (page_round_down_Z (alloc_top h))] (State.v:3466)
       where [RoomShapesDraft.mmap_top h p] is [Z.min (alloc_top h) (p_base p)].
       Every candidate and every length here is page-aligned, so the two windows
       admit exactly the same fits.  [pin_top_iff] below -- a proof, not a pin.
     - TASK_UNMAPPED_BASE.  [tub_model_eq] above, by [vm_compute].

   THE TWO THIS UNIT ADDED (on this derivation):
     (5) [p_guard p = 0].  [search_addr]'s first arm (RoomShapesDraft.v:329)
       conjoins [clear_of_stack] and the hint arm asks [fits] with [g = true],
       while Linux's [topdown_search] (75d69e00:Sys/Mm/Mmap.v:1139-1143) has NO
       stack-clearance test at all.  [policy_ok] admits a guard up to 256 MiB,
       and for a nonzero guard the policy abandons an address Linux takes.  This
       is a pin on the POLICY, not on the model: it declines to model a knob the
       model does not have.  With it, [pin_clear_of_stack] below PROVES (it does
       not assume) that [clear_of_stack] holds of every candidate, from the
       candidate being page-aligned and ending at or below [alloc_top h] and
       from the [page_round_down_Z (alloc_top ...) <= st] that [canon_fit_at]
       already carries.  That is also what makes [first_unclear] equivalent to
       "the top-down window has no fit", which is exactly Linux's fallback
       condition.
     (6) [vdso_in_ledger].  [fits] asks [off_vdso], a policy-only constraint
       Linux's [gap_fits] does not know, so the policy's [highest_fit] would
       range over a strictly smaller set than [highest_gap].  Pinning the STRIP
       is the wrong cure -- [s] is the live-vDSO state [strip_next] tracks.  The
       conjunct puts the live mappings in the LEDGER, and [pin_off_vdso] below
       then reaches [off_vdso] from the [region_free] that
       [Checks.Placement.linux_place_is_admissible] (:1038) hands out.  THIS IS
       THE MODEL'S OWN STEP, not this unit's invention:
       [Checks.Placement.linux_place_misses_vdso] (:1189-1208) is the same
       argument, and [State.init_model] builds exactly that ledger shape, so the
       conjunct is not satisfiable only for an empty strip.
   ======================================================================== *)

(* A page multiple at or below [A] is at or below [A] rounded down. *)
Lemma pin_align_le_prd : forall e A, e mod page_size = 0 -> e <= A -> e <= page_round_down_Z A.
Proof.
intros e A He HA. unfold page_round_down_Z, page_size in *.
pose proof (Z_div_mod_eq_full e 4096) as Ee.
pose proof (Z.div_le_mono e A 4096 ltac:(lia) HA) as D.
nia.
Qed.

Lemma pin_e_le_st : forall (h : VmMaps) st n (a : word),
  bv_unsigned a mod page_size = 0 -> n mod page_size = 0 ->
  bv_unsigned a + n <= alloc_top h -> page_round_down_Z (alloc_top h) <= st ->
  bv_unsigned a + n <= st.
Proof.
intros h st n a Ha Hn Hle Hst.
assert (Hm : (bv_unsigned a + n) mod page_size = 0)
  by (rewrite Zplus_mod, Ha, Hn; apply Zmod_0_l).
pose proof (pin_align_le_prd _ _ Hm Hle). lia.
Qed.

(* Conjunct (5) at work: with a zero guard every candidate clears the stack. *)
Lemma pin_clear_of_stack : forall h p s st n (a : word),
  p_guard p = 0 -> page_round_down_Z (alloc_top h) <= st ->
  bv_unsigned a mod page_size = 0 -> n mod page_size = 0 ->
  bv_unsigned a + n <= alloc_top h ->
  clear_of_stack h p s st n a.
Proof.
intros h p s st n a Hg Hst Ha Hn Hle. unfold clear_of_stack. cbv zeta. left.
rewrite Hg. pose proof (pin_e_le_st h st n a Ha Hn Hle Hst). lia.
Qed.

(* Conjunct (6) at work, by the step of [Checks.Placement.linux_place_misses_vdso]
   (75d69e00:theories/LinuxProcessSem/Checks/Placement.v:1189-1208): a range free of
   the reserved list (and of any list [l] after it) misses every reserved entry, and
   the live vDSO mappings are reserved entries.  [l] is the live mappings for an mmap
   and the mappings with the source cut out for an mremap grown in place. *)
Lemma pin_off_vdso : forall h p s (l : list (word * word)) n (a : word),
  vdso_in_ledger h p s -> 0 < n -> n < 2 ^ 64 ->
  region_free (vm_reserved h ++ l) a (Z_to_bv 64 n) = true ->
  off_vdso h p s n a.
Proof.
intros h p s l n a [Hv Ht] Hn Hn64 Hfree.
assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply Z_to_bv64_small; lia).
unfold off_vdso. cbv zeta. split.
- intros Hs. destruct (Hv Hs) as ([b sz] & Hin & L1 & L2). cbn [fst snd] in L1, L2.
  pose proof (region_free_In _ _ _ _ _ Hfree (in_or_app _ _ _ (or_introl Hin))) as Hov.
  unfold iv_overlap in Hov. rewrite Un in Hov.
  apply andb_false_iff in Hov as [Hf|Hf]; apply Z.ltb_ge in Hf; unfold away; lia.
- intros Hs. destruct (Ht Hs) as ([b sz] & Hin & L1 & L2). cbn [fst snd] in L1, L2.
  pose proof (region_free_In _ _ _ _ _ Hfree (in_or_app _ _ _ (or_introl Hin))) as Hov.
  unfold iv_overlap in Hov. rewrite Un in Hov.
  apply andb_false_iff in Hov as [Hf|Hf]; apply Z.ltb_ge in Hf; unfold away; lia.
Qed.

(* A policy fit is a Linux gap: the policy only ever asks for MORE. *)
Lemma pin_gap_of_fits : forall h p s st gb n lo top (a : word),
  fits h p s st gb n lo top a ->
  Mmap.gap_fits (vm_reserved h ++ vm_maps h) lo top n (bv_unsigned a).
Proof.
intros h p s st gb n lo top a (Hal & Hlo & _ & Hhi & Hfree & _ & _).
unfold Mmap.gap_fits.
split; [exact Hal|]. split; [exact Hlo|]. split; [exact Hhi|].
rewrite Z_to_bv_bv_unsigned. exact Hfree.
Qed.

(* and, under the pin, a Linux gap is a policy fit. *)
Lemma pin_fits_of_gap : forall h thp p s st gb n lo top (a : word),
  policy_pinned_h h thp p s -> page_round_down_Z (alloc_top h) <= st ->
  0 < n -> n mod page_size = 0 -> n < 2 ^ 64 ->
  top <= alloc_top h -> page_size <= lo ->
  Mmap.gap_fits (vm_reserved h ++ vm_maps h) lo top n (bv_unsigned a) ->
  fits h p s st gb n lo top a.
Proof.
intros h thp p s st gb n lo top a (Hleg & Hmin & Hbase & Hthp & Hg & Hvd)
  Hst Hn Hnal Hn64 Htop Hlop (Hal & Hlo & Hhi & Hfree).
rewrite Z_to_bv_bv_unsigned in Hfree.
unfold fits.
split; [exact Hal|]. split; [exact Hlo|].
split; [unfold page_size in Hlop; lia|].
split; [exact Hhi|]. split; [exact Hfree|]. split.
- exact (pin_off_vdso h p s (vm_maps h) n a Hvd Hn Hn64 Hfree).
- intros _. exact (pin_clear_of_stack h p s st n a Hg Hst Hal Hnal ltac:(lia)).
Qed.

(* The two window tops admit the same page-aligned ranges. *)
Lemma pin_top_iff : forall h p e, p_base p = bv_unsigned (vm_mmap_base h) ->
  e mod page_size = 0 ->
  (e <= mmap_top h p <-> e <= State.mmap_top h).
Proof.
intros h p e Hb He. unfold mmap_top, State.mmap_top. rewrite Hb.
pose proof (page_round_down_Z_le (alloc_top h)) as H1.
split; intro H.
- apply Z.min_glb; [lia|]. apply pin_align_le_prd; [exact He | lia].
- lia.
Qed.

Lemma pin_mmap_top_le : forall h p, mmap_top h p <= alloc_top h.
Proof. intros h p. unfold mmap_top. lia. Qed.

Lemma pin_pmd_eq : pmd_size = Mmap.pmd_size.
Proof. vm_compute. reflexivity. Qed.

Lemma pin_thp_align : forall p ret, p_legacy p = false -> thp_align p ret = Mmap.thp_align ret.
Proof.
intros p ret Hleg. unfold thp_align, Mmap.thp_align. rewrite Hleg, pin_pmd_eq.
destruct (Z.eqb_spec (ret mod Mmap.pmd_size) 0) as [E|E]; [rewrite E; lia | reflexivity].
Qed.

(* One fit in Linux's top-down window means a HIGHEST one, by the model's own
   decision procedure (75d69e00:Checks/Placement.v:493). *)
Lemma pin_highest_exists : forall h n a0,
  0 < n -> n mod page_size = 0 ->
  Mmap.gap_fits (vm_reserved h ++ vm_maps h) page_size (State.mmap_top h) n a0 ->
  exists A, Mmap.highest_gap (vm_reserved h ++ vm_maps h) page_size (State.mmap_top h) n A.
Proof.
intros h n a0 Hn Hnal Hg.
destruct (Checks.Placement.highest_gap_b_spec (vm_reserved h ++ vm_maps h) page_size
            (State.mmap_top h) n ltac:(unfold page_size; lia) Hn Hnal
            (Checks.Placement.mmap_top_lt_two_pow_64 h)) as [H1 H2].
destruct (Checks.Placement.highest_gap_b (vm_reserved h ++ vm_maps h) page_size
            (State.mmap_top h) n) as [A|] eqn:Hb.
- exists A. apply H1. reflexivity.
- exfalso. exact (proj1 H2 eq_refl a0 Hg).
Qed.

(* Every address Linux's search can return is a real 64-bit address. *)
Lemma pin_ts_bounds : forall h n a, 0 < n -> Mmap.topdown_search h n a ->
  page_size <= a /\ a + n <= alloc_top h /\ a < 2 ^ 64.
Proof.
intros h n a Hn Hts.
destruct (Checks.Placement.topdown_search_admissible h n a Hn Hts) as (_ & Hlo & Hhi & _).
pose proof (Checks.Placement.alloc_top_lt_two_pow_64 h) as Hb.
unfold two_pow_64 in Hb. unfold page_size in *. lia.
Qed.

(* THE BRIDGE.  Under the pin the policy's search and Linux's are the same
   relation. *)
Lemma pin_search_iff : forall h thp p s st n (a : word),
  policy_ok p -> policy_pinned_h h thp p s -> page_round_down_Z (alloc_top h) <= st ->
  0 < n -> n mod page_size = 0 -> n < 2 ^ 64 ->
  (search_addr h p s st n a <-> Mmap.topdown_search h n (bv_unsigned a)).
Proof.
intros h thp p s st n a Hp Hpin Hst Hn Hnal Hn64.
pose proof Hpin as Hpin'.
destruct Hpin' as (Hleg & Hmin & Hbase & Hthp & Hg & Hvd).
pose proof (pin_mmap_top_le h p) as Hmt.
pose proof (Checks.Placement.alloc_top_lt_two_pow_64 h) as Hb64. unfold two_pow_64 in Hb64.
(* a fit in the policy's top window is a gap in Linux's, and conversely *)
assert (TOPF : forall (b : word) gb, fits h p s st gb n page_size (mmap_top h p) b ->
          Mmap.gap_fits (vm_reserved h ++ vm_maps h) page_size (State.mmap_top h) n (bv_unsigned b)).
{ intros b gb Hf. pose proof (pin_gap_of_fits _ _ _ _ _ _ _ _ _ Hf) as (H1 & H2 & H3 & H4).
  split; [exact H1|]. split; [exact H2|].
  split; [apply (proj1 (pin_top_iff h p _ Hbase ltac:(rewrite Zplus_mod, H1, Hnal; apply Zmod_0_l))); exact H3 | exact H4]. }
assert (TOPB : forall (b : word) gb,
          Mmap.gap_fits (vm_reserved h ++ vm_maps h) page_size (State.mmap_top h) n (bv_unsigned b) ->
          fits h p s st gb n page_size (mmap_top h p) b).
{ intros b gb (H1 & H2 & H3 & H4).
  apply (pin_fits_of_gap h thp p s st gb n page_size (mmap_top h p) b Hpin Hst Hn Hnal Hn64 Hmt
          ltac:(lia)).
  split; [exact H1|]. split; [exact H2|].
  split; [apply (proj2 (pin_top_iff h p _ Hbase ltac:(rewrite Zplus_mod, H1, Hnal; apply Zmod_0_l))); exact H3 | exact H4]. }
(* with a zero guard, no candidate is ever refused for the stack *)
assert (CLR : forall (b : word), Mmap.gap_fits (vm_reserved h ++ vm_maps h) page_size (State.mmap_top h) n (bv_unsigned b) ->
          clear_of_stack h p s st n b).
{ intros b (H1 & H2 & H3 & H4).
  pose proof (page_round_down_Z_le (alloc_top h)) as Hpd.
  apply (pin_clear_of_stack h p s st n b Hg Hst H1 Hnal). unfold State.mmap_top in H3. lia. }
(* the policy's second arm is impossible under the pin *)
assert (NOA2 : forall (b : word),
          (forall a1 : word, highest_fit h p s st false n page_size (mmap_top h p) a1 ->
             ~ clear_of_stack h p s st n a1) ->
          ~ Mmap.gap_fits (vm_reserved h ++ vm_maps h) page_size (State.mmap_top h) n (bv_unsigned b)).
{ intros b Hfu Hgf. destruct (pin_highest_exists h n _ Hn Hnal Hgf) as (A & HA1 & HA2).
  assert (HAb : bv_unsigned (Z_to_bv 64 A) = A).
  { apply Z_to_bv64_small. destruct HA1 as (_ & Hlo & Hhi & _).
    unfold State.mmap_top in Hhi. unfold page_size in Hlo.
    pose proof (page_round_down_Z_le (alloc_top h)). lia. }
  apply (Hfu (Z_to_bv 64 A)).
  - split; [apply TOPB; rewrite HAb; exact HA1|].
    intros a' Ha'. rewrite HAb. exact (HA2 _ (TOPF a' false Ha')).
  - apply CLR. rewrite HAb. exact HA1. }
unfold search_addr, Mmap.topdown_search. cbv zeta. rewrite Hleg, Hmin.
assert (TUB : Z.max page_size task_unmapped_base = Mmap.task_unmapped_base).
{ rewrite tub_model_eq. unfold page_size, Mmap.task_unmapped_base. lia. }
rewrite TUB.
(* the bottom-up window is the same on both sides *)
assert (LOWF : forall (b : word), fits h p s st true n Mmap.task_unmapped_base (alloc_top h) b <->
          Mmap.gap_fits (vm_reserved h ++ vm_maps h) Mmap.task_unmapped_base (alloc_top h) n (bv_unsigned b)).
{ intros b. split.
  - intro Hf. exact (pin_gap_of_fits _ _ _ _ _ _ _ _ _ Hf).
  - intro Hgf. apply (pin_fits_of_gap h thp p s st true n Mmap.task_unmapped_base (alloc_top h) b
      Hpin Hst Hn Hnal Hn64 ltac:(lia) ltac:(unfold page_size, Mmap.task_unmapped_base; lia) Hgf). }
split.
- intros [[H1 H2] | [[Hfu H1] | (Hfu & Hno & H1)]].
  + left. split; [apply TOPF with (gb := false); exact (proj1 H1)|].
    intros a' Ha'.
    assert (Ha'b : bv_unsigned (Z_to_bv 64 a') = a').
    { apply Z_to_bv64_small. destruct Ha' as (_ & Hlo & Hhi & _).
      unfold State.mmap_top in Hhi. unfold page_size in Hlo.
      pose proof (page_round_down_Z_le (alloc_top h)). lia. }
    rewrite <- Ha'b. apply (proj2 H1). apply TOPB. rewrite Ha'b. exact Ha'.
  + exfalso. destruct H1 as [Hf _].
    apply (NOA2 a Hfu).
    apply TOPF with (gb := false).
    destruct Hf as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [lia|].
    split; [exact A5|]. split; [exact A6 | exact A7].
  + right. split.
    * intros a'. destruct (Z_lt_le_dec a' (2 ^ 64)) as [Hlt|Hge].
      -- destruct (Z_le_dec 0 a') as [H0|H0].
         ++ intro Hgf. apply (NOA2 (Z_to_bv 64 a') Hfu).
            rewrite (Z_to_bv64_small a' ltac:(lia)). exact Hgf.
         ++ intros (Hal & Hlo & _ & _). unfold page_size in Hlo. lia.
      -- intros (_ & _ & Hhi & _). unfold State.mmap_top in Hhi.
         pose proof (page_round_down_Z_le (alloc_top h)). lia.
    * split; [exact (proj1 (LOWF a) (proj1 H1))|].
      intros a' Ha'.
      assert (Ha'b : bv_unsigned (Z_to_bv 64 a') = a').
      { apply Z_to_bv64_small. destruct Ha' as (_ & Hlo & Hhi & _).
        unfold Mmap.task_unmapped_base in Hlo. lia. }
      rewrite <- Ha'b. apply (proj2 H1). apply (proj2 (LOWF _)). rewrite Ha'b. exact Ha'.
- intros [[H1 H2] | [Hno [H1 H2]]].
  + left. split; [split; [apply TOPB with (gb := false); exact H1|]|].
    * intros a' Ha'. exact (H2 _ (TOPF a' false Ha')).
    * apply CLR. exact H1.
  + right. right.
    assert (FU : forall a1 : word, highest_fit h p s st false n page_size (mmap_top h p) a1 ->
              ~ clear_of_stack h p s st n a1).
    { intros a1 [Hf _] _. exact (Hno _ (TOPF a1 false Hf)). }
    split; [exact FU|]. split.
    * intros a' Hf. apply (Hno (bv_unsigned a')).
      destruct Hf as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
      split; [exact A1|]. split; [exact A2|].
      split; [apply (proj1 (pin_top_iff h p _ Hbase ltac:(rewrite Zplus_mod, A1, Hnal; apply Zmod_0_l))); lia|].
      rewrite Z_to_bv_bv_unsigned. exact A5.
    * split; [exact (proj2 (LOWF a) H1)|].
      intros a' Ha'. exact (H2 _ (proj1 (LOWF a') Ha')).
Qed.

Lemma policy_admits_linux_pick : PolicyAdmitsLinuxPick.
Proof.
unfold PolicyAdmitsLinuxPick.
intros h p s st thp hint n Hp Hpin Hst Hn Hnal HW.
pose proof Hpin as Hpin'.
destruct Hpin' as (Hleg & Hmin & Hbase & Hthp & Hg & Hvd).
pose proof (Checks.Placement.alloc_top_lt_two_pow_64 h) as Hb64. unfold two_pow_64 in Hb64.
(* Both bounds from one place.  The [n + pmd_size] instantiation of
   [pin_search_iff] needs [n + pmd_size < 2 ^ 64], which does NOT follow from
   [n < 2 ^ 64].  It follows
   from Linux's own answer: the pick ends at or below [alloc_top h], it starts
   at or above [page_size], and [State.alloc_top_room] leaves a whole stack's
   width above [alloc_top h]. *)
assert (Hnb : n + pmd_size < 2 ^ 64 /\ n < 2 ^ 64).
{ pose proof (policy_place_available h p st n thp hint Hp Hn Hnal HW) as Hav0.
  destruct (Checks.Placement.linux_place_b h thp hint n) as [q|] eqn:Hq;
    [|unfold vm_place_available in Hav0; rewrite Hq in Hav0; discriminate].
  pose proof (proj1 (proj1 (Checks.Placement.linux_place_b_spec h thp hint n Hn Hnal) q) Hq) as Hpl0.
  destruct (Checks.Placement.linux_place_admissible h thp hint n q Hn Hnal Hpl0) as (_ & Hpos0 & Htop0 & _).
  pose proof (alloc_top_room h) as Hroom. unfold two_pow_64, stack_max_size in Hroom.
  unfold page_size in Hpos0. unfold pmd_size. lia. }
destruct Hnb as [Hnpmd Hn64].
pose proof (policy_place_available h p st n thp hint Hp Hn Hnal HW) as Hav.
pose proof (vm_place_pick_ok h thp hint n Hn Hnal Hav) as Hpk.
set (r := vm_place_pick h thp hint n) in *.
pose proof (proj1 (Checks.Placement.linux_place_is_iff h thp hint n r Hn Hnal) Hpk) as HL.
unfold Mmap.linux_place in HL. cbv zeta in HL.
unfold mmap_addr. cbv zeta. rewrite Hmin.
(* [mmap_addr]'s [down] IS the model's [hint_address]. *)
change (page_round_down_Z (bv_unsigned hint)) with (Mmap.hint_address hint) in *.
(* An `eqn:` destruct, NOT `Z.eqb_spec`, and NO follow-up rewrite in either
   branch.  A probe that printed HL and the goal here showed it: the
   destruct replaces the scrutinee in HL as well as in the goal, and both
   conditionals then reduce by iota on their own.  HL arrives as the branch's
   own disjunction and the goal as [fresh_addr h p s st n r] directly, so
   `rewrite E` has nothing to find on either side.  `Z.eqb_spec` fails the
   other way round -- it substitutes [hint_address hint := 0] and destroys the
   term the rewrite was looking for.  Three rounds guessed at this; one probe
   settled it. *)
destruct (Mmap.hint_address hint =? 0)%Z eqn:E.
-
  unfold fresh_addr. cbv zeta. rewrite Hthp, pin_pmd_eq.
  replace (0 <? n) with true by (symmetry; apply Z.ltb_lt; exact Hn).
  cbn [andb].
  destruct (thp && (n mod Mmap.pmd_size =? 0))%bool eqn:Hthpb.
  + destruct HL as [(ret & Hret & Hra) | [Hno Hts]].
    * left. destruct (pin_ts_bounds h (n + Mmap.pmd_size) ret ltac:(unfold Mmap.pmd_size; lia) Hret)
        as (Rlo & Rhi & R64).
      exists (Z_to_bv 64 ret). rewrite (Z_to_bv64_small ret ltac:(unfold page_size in Rlo; lia)).
      split.
      -- apply (proj2 (pin_search_iff h thp p s st (n + pmd_size) (Z_to_bv 64 ret) Hp Hpin Hst
           ltac:(unfold pmd_size; lia) ltac:(rewrite Zplus_mod, Hnal; vm_compute; reflexivity)
           Hnpmd)).
         rewrite (Z_to_bv64_small ret ltac:(unfold page_size in Rlo; lia)), pin_pmd_eq. exact Hret.
      -- rewrite (pin_thp_align p ret Hleg). exact Hra.
    * right. split.
      -- intros ret Hret. apply (Hno (bv_unsigned ret)).
         rewrite <- pin_pmd_eq.
         apply (proj1 (pin_search_iff h thp p s st (n + pmd_size) ret Hp Hpin Hst
           ltac:(unfold pmd_size; lia) ltac:(rewrite Zplus_mod, Hnal; vm_compute; reflexivity)
           Hnpmd)). exact Hret.
      -- apply (proj2 (pin_search_iff h thp p s st n r Hp Hpin Hst Hn Hnal Hn64)). exact Hts.
  + apply (proj2 (pin_search_iff h thp p s st n r Hp Hpin Hst Hn Hnal Hn64)). exact HL.
- assert (Ene : Mmap.hint_address hint <> 0)
    by (intro Z0; rewrite (proj2 (Z.eqb_eq _ _) Z0) in E; discriminate E).
  assert (Hdp : Mmap.hint_address hint mod page_size = 0)
    by (unfold Mmap.hint_address; apply Checks.Placement.page_round_down_Z_mod).
  assert (Hdpos : page_size <= Mmap.hint_address hint).
  { unfold Mmap.hint_address, page_round_down_Z, page_size in *.
    pose proof (u64_bounds hint) as Ub.
    pose proof (Z.div_pos (bv_unsigned hint) 4096 ltac:(lia) ltac:(lia)).
    nia. }
  replace (Z.max (Mmap.hint_address hint) page_size) with (Mmap.hint_address hint) by lia.
  destruct HL as [[Hgf ->] | [Hnf Hts]].
  + (* The 64-bit bound for the hint, named ONCE rather than re-derived inside two
       `ltac:()` terms.  An inline `destruct Hgf` there consumes the very
       hypothesis the bullet goes on to use, and a side goal is the wrong place to take a hypothesis apart. *)
    assert (Hd0 : 4096 <= Mmap.hint_address hint) by (unfold page_size in Hdpos; exact Hdpos).
    assert (Hhb : 0 <= Mmap.hint_address hint < 2 ^ 64).
    { destruct Hgf as (_ & _ & Hhi & _). lia. }
    left. split.
    * exists (Z_to_bv 64 (Mmap.hint_address hint)).
      rewrite (Z_to_bv64_small (Mmap.hint_address hint) ltac:(lia)).
      split; [reflexivity|].
      apply (pin_fits_of_gap h thp p s st true n page_size (alloc_top h) _ Hpin Hst Hn Hnal Hn64
        ltac:(lia) ltac:(lia)).
      rewrite (Z_to_bv64_small (Mmap.hint_address hint) ltac:(lia)).
      exact Hgf.
    * (* HL's left disjunct already rewrote [bv_unsigned r] to the hint, and the
         [replace] above put the goal's [Z.max] into the same form, so there is
         nothing left to rewrite. *)
      reflexivity.
  + right. split.
    * intros (w & Hw & Hf). apply Hnf. rewrite <- Hw.
      exact (pin_gap_of_fits _ _ _ _ _ _ _ _ _ Hf).
    * apply (proj2 (pin_search_iff h thp p s st n r Hp Hpin Hst Hn Hnal Hn64)). exact Hts.
Qed.

(* P5, mmap PROT_READ|PROT_WRITE. *)
Theorem canon_fit_mmap_rw : forall regs pc mem rom model,
  m_halted model = None -> m_vm_lazy model = [] ->
  bv_unsigned (getr regs 17) = 222 ->
  getr regs 11 <> Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 3 ->
  getr regs 13 = Z_to_bv 64 34 -> getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  Mmap.place_declined_b (m_kernel model) (m_vmmaps model) (getr regs 10)
    (page_round_up_Z (bv_unsigned (getr regs 11))) = false ->
  (forall p st, policy_ok p -> page_round_down_Z (alloc_top (m_vmmaps model)) <= st ->
     vm_limit (m_vmmaps model) <= AgreeLim.LIM_AG ->
     win_room (m_vmmaps model) p st (page_round_up_Z (bv_unsigned (getr regs 11)))) ->
  canon_fit_at segs (mkCfg (pend_at regs pc mem rom) model).
Proof.
intros regs pc mem rom model.
exact (canon_fit_mmap_rw_from_pick regs pc mem rom model policy_admits_linux_pick).
Qed.

(* P5, mmap PROT_NONE. *)
Theorem canon_fit_mmap_none : forall regs pc mem rom model,
  m_halted model = None -> m_vm_lazy model = [] ->
  bv_unsigned (getr regs 17) = 222 ->
  getr regs 11 <> Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 34 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  Mmap.place_declined_b (m_kernel model) (m_vmmaps model) (getr regs 10)
    (page_round_up_Z (bv_unsigned (getr regs 11))) = false ->
  (forall p st, policy_ok p -> page_round_down_Z (alloc_top (m_vmmaps model)) <= st ->
     vm_limit (m_vmmaps model) <= AgreeLim.LIM_AG ->
     win_room (m_vmmaps model) p st (page_round_up_Z (bv_unsigned (getr regs 11)))) ->
  canon_fit_at segs (mkCfg (pend_at regs pc mem rom) model).
Proof.
intros regs pc mem rom model.
exact (canon_fit_mmap_none_from_pick regs pc mem rom model policy_admits_linux_pick).
Qed.

End N.
