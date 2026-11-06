(* The placement policy finds room: under every claimed policy, an mmap or a moved mremap of a modest length has
   a policy address, and that address is one lps can return.  A counting fact over the current ledger, whatever
   placed it: a guarded fit exists in the policy's search window once the window holds the ledger's bytes, the
   two vDSO mappings and one gap per obstacle. *)
From Stdlib Require Import ZArith List Lia Bool Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YM00 YM01 PlaceGap.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import RoomShapesDraft.
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
  exists a, search_addr h p s (p_min p) st n a.
Proof.
intros h p s st n Hp Hn H. destruct (win_lo_page p Hp) as [Hal Hlo].
destruct (policy_fit_exists h p s st n (win_lo p) (Z.min (alloc_top h) (st - p_guard p)) Hp Hn Hal Hlo
  (Z.le_min_l _ _) (Z.le_min_r _ _) H) as (a & Ha).
unfold win_lo in Ha. destruct (p_legacy p) eqn:L.
- exact (search_addr_exists_legacy h p s (p_min p) st n a L Ha).
- exact (search_addr_exists_topdown h p s (p_min p) st n a L ltac:(lia) Ha).
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
  exists a, fresh_addr h p s st (p_min p) n a /\ lps_free h n a.
Proof.
intros h p s st n Hp Hn Hplain.
assert (Hat : alloc_top h < 2 ^ 64) by (pose proof (alloc_top_lt h) as X; unfold two_pow_64 in X; lia).
assert (Plain : exists a, search_addr h p s (p_min p) st n a /\ lps_free h n a).
{ destruct (policy_search_exists h p s st n Hp Hn Hplain) as (a & Ha). exists a. split; [exact Ha|].
  exact (fits_lps_free h p s st true n (p_min p) (alloc_top h) a (Z.le_refl _) (search_addr_fits h p s (p_min p) st n a Ha)). }
unfold fresh_addr, fresh_addr_at.
destruct (andb (p_thp p) (andb (Z.ltb 0 n) (Z.eqb (n mod pmd_size) 0))).
- destruct (classic (exists ret, search_addr h p s (p_min p) st (n + pmd_size) ret)) as [(ret & Hr) | Hno].
  + pose proof (fits_lps_free h p s st true (n + pmd_size) (p_min p) (alloc_top h) ret (Z.le_refl _)
      (search_addr_fits h p s (p_min p) st (n + pmd_size) ret Hr)) as (R1 & R2 & R3 & R4).
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
  exists a, mmap_addr h p s st (p_min p) hint n a /\ lps_free h n a.
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
    * exact (fits_lps_free h p s st true n (p_min p) (alloc_top h) a (Z.le_refl _) (search_addr_fits h p s (p_min p) st n a Ha)).
Qed.

(* ** Allocator nodes: the policy's step is one of lps's (under the alloc-forced-only filter) *)

From LinuxProcessSemantics.Riscv Require Import Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0v YP0n YN02.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable.Z Require Import Placement.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Uniform.
Local Open Scope Z_scope.

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
     canonical_ret p s st (p_min p) (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) model (eff_ret eff)) ->
  canon_can_step p s st segs ACFG (mkCfg (pend_at regs pc mem rom) model).
Proof.
intros p s st regs pc mem rom model e c2 H Hn Hc.
exists e, c2. split; [exact H|].
intros x8 len (_ & Hsv & _). cbn [cfg_ms] in Hsv. rewrite pend_svc in Hsv. injection Hsv as <-.
remember (mkCfg (pend_at regs pc mem rom) model) as c0 eqn:Ec.
remember (SNext c2) as r0 eqn:Er.
destruct H; try discriminate Er; injection Ec as -> ->.
- rewrite pend_svc in H0. discriminate H0.
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

(* P5, mmap PROT_READ|PROT_WRITE: with room in the window, the policy's address is a grant, or, when the
   budget refuses, the refusal is lps's only answer. *)
Theorem canon_fit_mmap_rw : forall regs pc mem rom model,
  m_halted model = None -> m_vm_lazy model = [] ->
  bv_unsigned (getr regs 17) = 222 ->
  getr regs 11 <> Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 3 ->
  getr regs 13 = Z_to_bv 64 34 -> getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  (forall p st, policy_ok p -> page_round_down_Z (alloc_top (m_vmmaps model)) <= st ->
     vm_limit (m_vmmaps model) <= AgreeLim.LIM_AG ->
     win_room (m_vmmaps model) p st (page_round_up_Z (bv_unsigned (getr regs 11)))) ->
  canon_fit_at segs (mkCfg (pend_at regs pc mem rom) model).
Proof.
intros regs pc mem rom model Hh Hlz Hno Hlen Hprot Hflags Hfd Hoff HW p s st Hp Hst Hlim x8 len _ _.
destruct (node_mmap_rw04 segs regs pc mem rom model Hh Hlz Hno Hlen Hprot Hflags Hfd Hoff) as [Hs _].
pose proof (page_round_up_pos (getr regs 11) Hlen) as Hn.
set (nZ := page_round_up_Z (bv_unsigned (getr regs 11))) in *.
cbn [cfg_model] in Hst, Hlim.
destruct (policy_mmap_addr_exists (m_vmmaps model) p s st (getr regs 10) nZ Hp Hn (HW p st Hp Hst Hlim))
  as (a & Ha & F1 & F2 & F3 & F4).
destruct (vm_backing_used model + nZ <=? vm_limit (m_vmmaps model)) eqn:Hb.
- assert (G : grant_ok (getr regs 10) model a nZ = true).
  { unfold grant_ok. rewrite F4, Hb. rewrite (proj2 (Z.eqb_eq _ _) F1), (proj2 (Z.ltb_lt _ _) F2), (proj2 (Z.leb_le _ _) F3).
    reflexivity. }
  apply (canon_step_of_sstep p s st regs pc mem rom model [] _ (Hs (inr (exist _ a G))) eq_refl).
  intros eff m'' E. apply (f_equal cfg_ms) in E. cbn [cfg_ms] in E. apply ret_of_adv in E. rewrite <- E. cbn [mmap_rw_ef04 eff_ret proj1_sig].
  right. left. split; [rewrite si_sysno; exact Hno|]. rewrite si_arg0, si_arg1. exact Ha.
- assert (Hr : mmap_grant_refusable (Z_to_bv 64 34) model nZ = true).
  { unfold mmap_grant_refusable, Mmap.mmap_noreserve_backed_ok.
    replace (Mmap.mmap_noreserve_b (Z_to_bv 64 34)) with false by (vm_compute; reflexivity).
    cbv beta iota. rewrite Hb. reflexivity. }
  apply (canon_step_of_sstep p s st regs pc mem rom model [] _ (Hs (inl (exist _ ENOMEM (conj ENOMEM_in_mmap_errnos Hr)))) eq_refl).
  intros eff m'' E. apply (f_equal cfg_ms) in E. cbn [cfg_ms] in E. apply ret_of_adv in E. rewrite <- E. cbn [mmap_rw_ef04 eff_ret proj1_sig].
  left. exact errno_answer_enomem.
Qed.

(* P5, mmap PROT_NONE: the policy's address is a reservation lps may grant (no budget for a reservation). *)
Theorem canon_fit_mmap_none : forall regs pc mem rom model,
  m_halted model = None -> m_vm_lazy model = [] ->
  bv_unsigned (getr regs 17) = 222 ->
  getr regs 11 <> Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 34 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  (forall p st, policy_ok p -> page_round_down_Z (alloc_top (m_vmmaps model)) <= st ->
     vm_limit (m_vmmaps model) <= AgreeLim.LIM_AG ->
     win_room (m_vmmaps model) p st (page_round_up_Z (bv_unsigned (getr regs 11)))) ->
  canon_fit_at segs (mkCfg (pend_at regs pc mem rom) model).
Proof.
intros regs pc mem rom model Hh Hlz Hno Hlen Hprot Hflags Hfd Hoff HW p s st Hp Hst Hlim x8 len _ _.
destruct (node_mmap_none04 segs regs pc mem rom model Hh Hlz Hno Hlen Hprot Hflags Hfd Hoff) as [Hs _].
pose proof (page_round_up_pos (getr regs 11) Hlen) as Hn.
set (nZ := page_round_up_Z (bv_unsigned (getr regs 11))) in *.
cbn [cfg_model] in Hst, Hlim.
destruct (policy_mmap_addr_exists (m_vmmaps model) p s st (getr regs 10) nZ Hp Hn (HW p st Hp Hst Hlim))
  as (a & Ha & F1 & F2 & F3 & F4).
assert (G : place_ok (getr regs 10) model a nZ = true).
{ unfold place_ok. rewrite F4. rewrite (proj2 (Z.eqb_eq _ _) F1), (proj2 (Z.ltb_lt _ _) F2), (proj2 (Z.leb_le _ _) F3).
  reflexivity. }
apply (canon_step_of_sstep p s st regs pc mem rom model [] _ (Hs (inr (exist _ a G))) eq_refl).
intros eff m'' E. apply (f_equal cfg_ms) in E. cbn [cfg_ms] in E. apply ret_of_adv in E. rewrite <- E. cbn [mmap_none_ef04 eff_ret proj1_sig].
right. left. split; [rewrite si_sysno; exact Hno|]. rewrite si_arg0, si_arg1. exact Ha.
Qed.

(* P1, brk: canonical_ret's brk arm takes every answer, and every step of a brk node is a syscall step. *)
Theorem canon_fit_brk : forall regs pc mem rom model,
  m_halted model = None -> m_vm_lazy model = [] ->
  bv_unsigned (getr regs 17) = 214 ->
  canon_fit_at segs (mkCfg (pend_at regs pc mem rom) model).
Proof.
intros regs pc mem rom model Hh Hlz Hno p s st Hp Hst _ x8 len _ (e & c' & Hs).
destruct (node_brk segs regs pc mem rom model Hh Hlz Hno) as [_ Hc].
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

End N.
