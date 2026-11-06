(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatSim ShapeSet RealizesCfg AllocNodesCfg PlacementCount.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv MallocWfKf.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngU.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngU MngMeas MngWk MngRz MngRz2 MngBudM.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngU.MngLedger OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngU OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMeas OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWk OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngRz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngRz2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngBudM.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition CH (q : kreq) : Z :=
  match q with
  | KBrkGrow n => PGSZ * Z.max 0 n + PGSZ
  | KMmapRW len => Z.max 0 (page_round len) + PGSZ
  | KMmapNone _ => PGSZ
  | KMprotect _ => PGSZ
  | _ => 0
  end.

Lemma CH_nonneg : forall q, 0 <= CH q.
Proof. intros []; cbn [CH]; unfold PGSZ; lia. Qed.

Definition BI (UB0 : Z) (x : kf) (md : Model) (B : Z) : Prop := Um md + B <= UB0 /\ 0 <= B /\ UB0 <= 2 ^ 30.

Lemma BI_step : forall UB0 x x' md md' B c, BI UB0 x md B -> c <= B -> 0 <= c -> Um md' <= Um md + c -> BI UB0 x' md' (B - c).
Proof. intros UB0 x x' md md' B c (H1 & H2 & H3) Hc Hc0 HU. unfold BI. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Um_eq : forall md, m_vm_lazy md = [] -> inrange (vm_maps (m_vmmaps md)) ->
  Um md = Wt (vm_maps (m_vmmaps md)) (cutall (vm_noaccess (m_vmmaps md)) (fun _ => 1)) +
          Z.of_nat (length (m_vm_materialized md)) * 4096 + 4096 * Z.of_nat (length (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md))).
Proof.
  intros md Hl Hr. unfold Um, vm_backing_used. rewrite Hl. cbn [maps_subtract_all]. unfold vm_backed_maps.
  rewrite live_bytes_Wt, (msa_Wt _ _ _ Hr). unfold page_size. ring.
Qed.

Lemma cut_le1 : forall C z, 0 <= cutall C (fun _ => 1) z <= 1.
Proof. intros C z. rewrite cutall_spec. destruct (inC C z); lia. Qed.

Lemma sumr_le_len : forall f a n, (forall z, f z <= 1) -> sumr f a (Z.to_nat n) <= Z.max 0 n.
Proof.
  intros f a n H. pose proof (sumr_le f (fun _ => 1) (Z.to_nat n) a H) as S. rewrite sumr_one in S. lia.
Qed.

Lemma inrange_cons : forall e l, bv_unsigned (fst e) + bv_unsigned (snd e) <= 2 ^ 64 -> inrange l -> inrange (e :: l).
Proof. intros e l H1 H2 p [<-|Hp]; [exact H1 | exact (H2 p Hp)]. Qed.

Lemma mns_b : forall flags, bv_unsigned flags = 34 \/ bv_unsigned flags = 50 -> mmap_noreserve_b flags = false.
Proof. intros flags [H|H]; unfold mmap_noreserve_b; rewrite H; reflexivity. Qed.

Lemma vmmaps_with : forall h m, m_vmmaps (with_vmmaps h m) = h.
Proof. reflexivity. Qed.
Lemma mat_with : forall h m, m_vm_materialized (with_vmmaps h m) = m_vm_materialized m.
Proof. reflexivity. Qed.

Section Nodes.
Variables (HTOP : Z) (FORB : list (Z * Z)) (L : layout) (x : kf) (md : Model).
Hypothesis HL : LINK HTOP FORB L x md.

Let Hlz := lk_lazy _ _ _ _ _ HL.
Let Hrg := maps_inrange HTOP FORB L x md HL.

#[using="HTOP FORB L x HL Hlz Hrg"] Lemma Um_rw : forall a n, 0 <= bv_unsigned a + bv_unsigned n <= 2 ^ 64 ->
  Um (fresh_rw_next (w64 34) a n md) <= Um md + bv_unsigned n + 4096.
Proof. LiaFast.lf_pins (fun (HTOP FORB L x HL Hlz Hrg : LiaFast.U) => LiaFast.u0).
  intros a n Han.
  assert (E : fresh_rw_next (w64 34) a n md = with_vmmaps (m_vmmaps (fresh_rw_next (w64 34) a n md)) md)
    by (unfold fresh_rw_next, with_mmap_backing; rewrite (mns_b (w64 34) ltac:(left; reflexivity)); reflexivity).
  rewrite E. rewrite (Um_eq (with_vmmaps _ md) Hlz) by (rewrite rw_vmmaps; apply inrange_cons; [cbn [fst snd]; lia | exact Hrg]).
  rewrite (Um_eq md Hlz Hrg). rewrite vmmaps_with, rw_vmmaps. cbn [vm_maps vm_noaccess vm_reserved].
  rewrite ?mat_with. rewrite Wt_cons. cbn [fst snd].
  rewrite !length_app. cbn [length]. rewrite Nat2Z.inj_add, Nat2Z.inj_succ.
  pose proof (sumr_le_len (cutall (vm_noaccess (m_vmmaps md)) (fun _ => 1)) (bv_unsigned a) (bv_unsigned n) (fun z => proj2 (cut_le1 _ z))).
  pose proof (urange n). unfold m_vm_materialized. lia.
Qed.

#[using="HTOP FORB L x HL Hlz Hrg"] Lemma Um_na : forall a n, 0 <= bv_unsigned a + bv_unsigned n <= 2 ^ 64 ->
  Um (fresh_na_next (w64 34) a n md) <= Um md + 4096.
Proof. LiaFast.lf_pins (fun (HTOP FORB L x HL Hlz Hrg : LiaFast.U) => LiaFast.u0).
  intros a n Han.
  assert (E : fresh_na_next (w64 34) a n md = with_vmmaps (m_vmmaps (fresh_na_next (w64 34) a n md)) md)
    by (unfold fresh_na_next, with_mmap_backing; rewrite (mns_b (w64 34) ltac:(left; reflexivity)); reflexivity).
  rewrite E. rewrite (Um_eq (with_vmmaps _ md) Hlz) by (rewrite na_vmmaps; apply inrange_cons; [cbn [fst snd]; lia | exact Hrg]).
  rewrite (Um_eq md Hlz Hrg). rewrite vmmaps_with, na_vmmaps. cbn [vm_maps vm_noaccess vm_reserved].
  rewrite ?mat_with. rewrite Wt_cons. cbn [fst snd cutall].
  assert (Z0 : sumr (cutf (bv_unsigned a) (bv_unsigned a + bv_unsigned n) (cutall (vm_noaccess (m_vmmaps md)) (fun _ => 1)))
                 (bv_unsigned a) (Z.to_nat (bv_unsigned n)) = 0).
  { apply sumr_zero. intros z Hz. pose proof (urange n) as Rn. rewrite Z2Nat.id in Hz by lia. unfold cutf.
    replace (inI (bv_unsigned a) (bv_unsigned a + bv_unsigned n) z) with true by (symmetry; apply inI_true; lia). reflexivity. }
  rewrite Z0.
  assert (W : Wt (vm_maps (m_vmmaps md)) (cutf (bv_unsigned a) (bv_unsigned a + bv_unsigned n) (cutall (vm_noaccess (m_vmmaps md)) (fun _ => 1))) <=
              Wt (vm_maps (m_vmmaps md)) (cutall (vm_noaccess (m_vmmaps md)) (fun _ => 1))).
  { apply Wt_mono. intros z. unfold cutf. destruct (inI _ _ z); [pose proof (cut_le1 (vm_noaccess (m_vmmaps md)) z); lia | lia]. }
  rewrite !length_app. cbn [length]. lia.
Qed.

#[using="HTOP FORB L x HL Hlz Hrg"] Lemma Um_pr : forall a, 0 <= a -> a + PGSZ < 2 ^ 64 ->
  Um (mprotect_model_next md (w64 a) (w64 PGSZ)) <= Um md + PGSZ.
Proof. LiaFast.lf_pins (fun (HTOP FORB L x HL Hlz Hrg : LiaFast.U) => LiaFast.u0).
  intros a Ha1 Ha2.
  assert (UA : bv_unsigned (w64 a) = a) by (apply u_w64; unfold PGSZ in *; lia). change (bv_unsigned (w64 PGSZ)) with PGSZ.
  rewrite (Um_eq (mprotect_model_next md (w64 a) (w64 PGSZ)) Hlz) by (rewrite pr_vmmaps; exact Hrg).
  rewrite (Um_eq md Hlz Hrg). rewrite pr_vmmaps. cbn [vm_maps vm_noaccess vm_reserved].
  replace (m_vm_materialized (mprotect_model_next md (w64 a) (w64 PGSZ))) with (m_vm_materialized md) by reflexivity. rewrite UA.
  change (bv_unsigned (w64 PGSZ)) with PGSZ.
  assert (P : forall z, cutall (maps_subtract (vm_noaccess (m_vmmaps md)) a (a + PGSZ)) (fun _ => 1) z <=
                        cutall (vm_noaccess (m_vmmaps md)) (fun _ => 1) z + ind (inI a (a + PGSZ) z)).
  { intros z. rewrite !cutall_spec. rewrite inC_subtract by (unfold PGSZ in *; lia).
    destruct (inC (vm_noaccess (m_vmmaps md)) z); destruct (inI a (a + PGSZ) z); cbn; lia. }
  pose proof (Wt_mono (vm_maps (m_vmmaps md)) _ _ P) as W. rewrite Wt_add in W.
  pose proof (Wt_disj_le (vm_maps (m_vmmaps md)) (fun z => ind (inI a (a + PGSZ) z)) a (a + PGSZ) (lk_mdisj _ _ _ _ _ HL)
                ltac:(unfold PGSZ; lia) ltac:(intros z; apply ind_range)
                ltac:(intros z Hz; cbv beta; replace (inI a (a + PGSZ) z) with false by (symmetry; apply inI_false; lia); reflexivity)) as D.
  rewrite sumr_ind_full in D by (unfold PGSZ; lia). unfold m_vm_materialized. lia.
Qed.

#[using="HTOP FORB L x HL Hlz Hrg"] Lemma Um_guard : forall a, 0 <= a -> a + PGSZ < 2 ^ 64 ->
  Um (fixed_na_next (w64 50) (w64 a) (w64 PGSZ) md) <= Um md.
Proof. LiaFast.lf_pins (fun (HTOP FORB L x HL Hlz Hrg : LiaFast.U) => LiaFast.u0).
  intros a Ha1 Ha2.
  assert (UA : bv_unsigned (w64 a) = a) by (apply u_w64; unfold PGSZ in *; lia).
  rewrite (Um_eq (fixed_na_next (w64 50) (w64 a) (w64 PGSZ) md) (guard_lazy _ _ _ Hlz)) by (rewrite guard_vmmaps; exact Hrg).
  rewrite (Um_eq md Hlz Hrg). rewrite guard_vmmaps. cbn [vm_maps vm_noaccess vm_reserved cutall fst snd]. rewrite UA.
  change (bv_unsigned (w64 PGSZ)) with PGSZ.
  assert (P : forall z, cutf a (a + PGSZ) (cutall (maps_subtract (vm_noaccess (m_vmmaps md)) a (a + PGSZ)) (fun _ => 1)) z <=
                        cutall (vm_noaccess (m_vmmaps md)) (fun _ => 1) z).
  { intros z. unfold cutf. rewrite !cutall_spec. rewrite inC_subtract by (unfold PGSZ in *; lia).
    destruct (inC (vm_noaccess (m_vmmaps md)) z); destruct (inI a (a + PGSZ) z); cbn; lia. }
  pose proof (Wt_mono (vm_maps (m_vmmaps md)) _ _ P) as W.
  assert (M : (length (m_vm_materialized (fixed_na_next (w64 50) (w64 a) (w64 PGSZ) md)) <= length (m_vm_materialized md))%nat).
  { unfold fixed_na_next, with_mmap_replacement, with_mmap_backing. rewrite (mns_b (w64 50) ltac:(right; reflexivity)).
    unfold vm_forget_range, with_vm_backing, m_vm_materialized, with_vmmaps. cbn [m_vm vmst_materialized].
    apply filter_length_le'. }
  lia.
Qed.

#[using="Type"] Lemma brk_next_eq : forall cur req, vm_brk (m_vmmaps md) = w64 cur -> PGSZ <= cur -> cur < req -> req + PGSZ < 2 ^ 64 ->
  cur mod PGSZ = 0 -> req mod PGSZ = 0 ->
  with_brk_next md (w64 req) (w64 req) = with_vmmaps (m_vmmaps (with_brk_next md (w64 req) (w64 req))) md.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros cur req Hv Hc0 Hcr Hr64 Hal Har. unfold with_brk_next.
  replace (brk_unmaps (w64 req) (vm_brk (m_vmmaps md))) with (@nil (word * word)).
  - reflexivity.
  - unfold brk_unmaps, brk_page_range. rewrite Hv. rewrite !u_w64 by (unfold PGSZ in *; lia). rewrite !page_round_up_aligned by assumption.
    replace (0 <? cur) with true by (symmetry; apply Z.ltb_lt; unfold PGSZ in *; lia).
    replace (req <? cur) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

#[using="HTOP FORB L x HL Hlz Hrg"] Lemma Um_brk : forall cur req, vm_brk (m_vmmaps md) = w64 cur -> PGSZ <= cur -> cur < req -> req + PGSZ < 2 ^ 64 ->
  cur mod PGSZ = 0 -> req mod PGSZ = 0 ->
  Um (with_brk_next md (w64 req) (w64 req)) <= Um md + (req - cur) + 4096.
Proof. LiaFast.lf_pins (fun (HTOP FORB L x HL Hlz Hrg : LiaFast.U) => LiaFast.u0).
  intros cur req Hv Hc0 Hcr Hr64 Hal Har.
  pose proof (brk_next_vmmaps md cur req Hv Hc0 Hcr Hr64 Hal Har) as VM.
  rewrite (brk_next_eq cur req Hv Hc0 Hcr Hr64 Hal Har).
  assert (RC : 0 <= cur < 2 ^ 64 /\ 0 <= req - cur < 2 ^ 64) by (unfold PGSZ in *; lia).
  assert (IR : inrange ((w64 cur, w64 (req - cur)) :: vm_maps (m_vmmaps md))).
  { apply inrange_cons; [cbn [fst snd]; rewrite (u_w64 cur), (u_w64 (req - cur)) by lia; unfold PGSZ in *; lia | exact Hrg]. }
  rewrite (Um_eq (with_vmmaps (m_vmmaps (with_brk_next md (w64 req) (w64 req))) md) Hlz) by (rewrite vmmaps_with, VM; exact IR).
  rewrite (Um_eq md Hlz Hrg). rewrite vmmaps_with, VM. cbn [vm_maps vm_noaccess vm_reserved].
  rewrite ?mat_with. rewrite Wt_cons. cbn [fst snd].
  rewrite !length_app. cbn [length].
  rewrite (u_w64 cur) by lia. rewrite (u_w64 (req - cur)) by lia.
  pose proof (sumr_le_len (cutall (vm_noaccess (m_vmmaps md)) (fun _ => 1)) cur (req - cur) (fun z => proj2 (cut_le1 _ z))).
  lia.
Qed.

End Nodes.

(* [comment removed for export] *)
Lemma backing_le_Um : forall md, vm_backing_used md <= Um md.
Proof. intros md. unfold Um. pose proof (Nat2Z.is_nonneg (length (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)))). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma amgm : forall u v, 0 <= u -> 0 <= v -> 4 * (u * v) <= (u + v) * (u + v).
Proof. intros u v Hu Hv. pose proof (Z.square_nonneg (u - v)). nia. Qed.

(* [comment removed for export] *)
Lemma rcnt_small : forall o c, 0 <= c -> 0 <= o -> PGSZ * o <= 2 ^ 30 -> 2 * PGSZ * (2 ^ c - 1) <= 2 * PGSZ * (o + c) -> c <= 18.
Proof.
  intros o c Hc Ho Hob H. destruct (Z_le_gt_dec c 18) as [E|E]; [exact E|]. exfalso.
  assert (P : 2 ^ c = 2 ^ 19 * 2 ^ (c - 19)) by (rewrite <- Z.pow_add_r by lia; f_equal; ring).
  pose proof (Z.pow_gt_lin_r 2 (c - 19) ltac:(lia) ltac:(lia)) as G.
  set (Q := 2 ^ (c - 19)) in *. unfold PGSZ in *. lia.
Qed.

Lemma rcnt_nonneg : forall rs, 0 <= rcnt rs.
Proof. intros rs. unfold rcnt. induction rs as [|rg rs IH]; cbn [fold_right]; [lia|]. destruct (rg_kind rg); lia. Qed.
Lemma ropen_nonneg : forall rs, 0 <= ropen rs.
Proof. intros rs. unfold ropen. induction rs as [|rg rs IH]; cbn [fold_right]; [lia|]. destruct (rg_kind rg); lia. Qed.

Section Place.
Variables (HTOP : Z) (FORB : list (Z * Z)) (L : layout) (x : kf) (md : Model).
Hypothesis HL : LINK HTOP FORB L x md.

Let Hlz := lk_lazy _ _ _ _ _ HL.
Let Hrg := maps_inrange HTOP FORB L x md HL.

(* [comment removed for export] *)
#[using="HTOP FORB L x HL Hlz Hrg"] Lemma place_bound : forall nZ c, 0 < nZ -> 0 <= c <= 2 ^ 18 ->
  Um md + nZ + 4096 <= 2 ^ 30 \/
  (nZ <= Wt (vm_maps (m_vmmaps md)) (cutall (vm_noaccess (m_vmmaps md)) (fun _ => 1)) + c /\ Um md + 4096 <= 2 ^ 30) ->
  page_size + ledger_size (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md))
   + Z.of_nat (length (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md))) * (nZ + page_size) + nZ
   <= alloc_top (m_vmmaps md).
Proof. LiaFast.lf_pins (fun (HTOP FORB L x HL Hlz Hrg : LiaFast.U) => LiaFast.u0).
  intros nZ c HnZ Hc HB.
  pose proof (Um_eq md Hlz Hrg) as UE.
  set (b := Wt (vm_maps (m_vmmaps md)) (cutall (vm_noaccess (m_vmmaps md)) (fun _ => 1))) in *.
  set (k := Z.of_nat (length (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)))) in *.
  assert (Hb0 : 0 <= b) by (apply Wt_nonneg; intros z; exact (proj1 (cut_le1 _ z))).
  assert (Hk0 : 0 <= k) by (unfold k; lia).
  pose proof (Nat2Z.is_nonneg (length (m_vm_materialized md))) as Hm0.
  rewrite ledger_size_app. pose proof (lk_rsz _ _ _ _ _ HL) as RZ.
  pose proof (ledger_bound HTOP FORB L x md HL) as LB. fold b in LB.
  pose proof (lk_k2 _ _ _ _ _ HL) as K2. pose proof (lk_k1 _ _ _ _ _ HL) as K1.
  pose proof (opened_backed HTOP FORB L x md HL) as OB. fold b in OB.
  pose proof (rcnt_nonneg (kf_regions x)) as C0. pose proof (ropen_nonneg (kf_regions x)) as O0.
  pose proof (lk_atop _ _ _ _ _ HL) as AT.
  assert (Hb1 : b <= 2 ^ 30) by (destruct HB as [HB|(_ & HB)]; lia).
  assert (C18 : rcnt (kf_regions x) <= 18).
  { apply (rcnt_small (ropen (kf_regions x))); [exact C0 | exact O0 | lia|]. rewrite <- K1. exact K2. }
  set (v := if Z_le_dec (Um md + nZ + 4096) (2 ^ 30) then nZ else b + c).
  assert (Hv : nZ <= v /\ 4096 * k + v <= 2 ^ 30 + c).
  { unfold v. destruct (Z_le_dec (Um md + nZ + 4096) (2 ^ 30)) as [E|E]; [lia|]. destruct HB as [HB|(HB1 & HB2)]; [lia|]. lia. }
  assert (AM : 4 * ((4096 * k) * v) <= (4096 * k + v) * (4096 * k + v)) by (apply amgm; lia).
  assert (SQ : (4096 * k + v) * (4096 * k + v) <= (2 ^ 30 + 2 ^ 18) * (2 ^ 30 + 2 ^ 18)) by (apply Z.mul_le_mono_nonneg; lia).
  assert (KV : k * nZ <= k * v) by (apply Z.mul_le_mono_nonneg_l; lia).
  replace (4 * (4096 * k * v)) with (16384 * (k * v)) in AM by ring.
  rewrite Z.mul_add_distr_l. unfold page_size.
  set (P := k * v) in *. set (P' := k * nZ) in *. unfold PGSZ in *. lia.
Qed.

#[using="HTOP FORB L x HL Hlz Hrg"] Theorem place_rw : forall nZ, 0 < nZ -> Um md + nZ + 4096 <= 2 ^ 30 -> exists a, place_ok md nZ a.
Proof. LiaFast.lf_pins (fun (HTOP FORB L x HL Hlz Hrg : LiaFast.U) => LiaFast.u0). intros nZ H1 H2. apply place_ok_exists; [exact H1|]. exact (place_bound nZ 0 H1 ltac:(lia) (or_introl H2)). Qed.

#[using="HTOP FORB L x HL Hlz Hrg"] Theorem rw_guard : forall nZ, 0 < nZ -> Um md + nZ + 4096 <= 2 ^ 30 -> exists a, fresh_rw_guard (w64 34) md nZ a.
Proof. LiaFast.lf_pins (fun (HTOP FORB L x HL Hlz Hrg : LiaFast.U) => LiaFast.u0).
  intros nZ H1 H2. apply fresh_rw_guard_exists; [exact H1| |exact (place_bound nZ 0 H1 ltac:(lia) (or_introl H2))].
  unfold mmap_noreserve_backed_ok. rewrite (mns_b (w64 34) ltac:(left; reflexivity)). apply Z.leb_le.
  pose proof (backing_le_Um md). pose proof (lk_lim _ _ _ _ _ HL). lia.
Qed.

#[using="HTOP FORB L HL Hlz Hrg"] Theorem place_na : forall s len, kf_of s = x -> req_ok s (KMmapNone len) -> Um md + 4096 <= 2 ^ 30 ->
  exists a, place_ok md (page_round len) a.
Proof. LiaFast.lf_pins (fun (HTOP FORB L HL Hlz Hrg : LiaFast.U) => LiaFast.u0).
  intros s len Hx Hrq HU. destruct Hrq as (Hlen & Hav & Hsh & F6 & F1 & F2 & _).
  change (resv_total s) with (rtot (kf_regions (kf_of s))) in F6, F1. change (resv_count s) with (rcnt (kf_regions (kf_of s))) in F1, F2.
  change (resv_opened s) with (ropen (kf_regions (kf_of s))) in F1. rewrite Hx in F6, F1, F2.
  rewrite Z.shiftl_mul_pow2 in Hlen by exact Hsh.
  assert (EN : page_round len = len) by (rewrite Hlen; apply page_round_mult; pose proof (Z.pow_pos_nonneg 2 (st_meta_alloc_shift s) ltac:(lia) Hsh); lia).
  rewrite EN. pose proof (Z.pow_pos_nonneg 2 (st_meta_alloc_shift s) ltac:(lia) Hsh) as P0.
  pose proof (opened_backed HTOP FORB L x md HL) as OB.
  pose proof (Um_eq md Hlz Hrg) as UE. pose proof (Nat2Z.is_nonneg (length (m_vm_materialized md))) as Hm0.
  pose proof (Nat2Z.is_nonneg (length (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)))) as Hk0.
  assert (Hb0 : 0 <= Wt (vm_maps (m_vmmaps md)) (cutall (vm_noaccess (m_vmmaps md)) (fun _ => 1)))
    by (apply Wt_nonneg; intros z; exact (proj1 (cut_le1 _ z))).
  pose proof (ropen_nonneg (kf_regions x)) as O0.
  assert (C18 : st_meta_alloc_shift s <= 18).
  { apply (rcnt_small (ropen (kf_regions x))); [exact Hsh | exact O0 | lia|]. clear - F6 F1 F2 O0 Hsh. unfold PGSZ in *. lia. }
  assert (HL0 : 0 < len) by (rewrite Hlen; unfold PGSZ; lia).
  apply place_ok_exists; [exact HL0|].
  apply (place_bound len (PGSZ * 20) HL0 ltac:(unfold PGSZ; lia)). right. split; [|exact HU].
  rewrite Hlen. rewrite <- F2 in *. unfold PGSZ in *. lia.
Qed.

End Place.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Obl.
Variables (FORB : list (Z * Z)) (HTOP : Z) (UB0 : Z).

#[using="Type"] Lemma ob_junk_B : forall x md B b, BI UB0 x md B -> CH (KJunk b) <= B -> BI UB0 x md (B - CH (KJunk b)).
Proof. LiaFast.lf_pins LiaFast.u0. intros x md B b HB Hc. cbn [CH]. rewrite Z.sub_0_r. exact HB. Qed.

#[using="Type"] Lemma ob_query_B : forall L x md B, LINK HTOP FORB L x md -> BI UB0 x md B -> CH KBrkQuery <= B ->
  BI UB0 (kstep x KBrkQuery 1) md (B - CH KBrkQuery).
Proof. LiaFast.lf_pins LiaFast.u0. intros L x md B _ HB Hc. apply (BI_step UB0 x _ md md B _ HB Hc (CH_nonneg _)). cbn [CH]. lia. Qed.

#[using="Type"] Lemma ob_brk_refuse_B : forall L x md B n, LINK HTOP FORB L x md -> BI UB0 x md B -> CH (KBrkGrow n) <= B ->
  BI UB0 (kstep x (KBrkGrow n) 0) md (B - CH (KBrkGrow n)).
Proof. LiaFast.lf_pins LiaFast.u0. intros L x md B n _ HB Hc. apply (BI_step UB0 x _ md md B _ HB Hc (CH_nonneg _)). pose proof (CH_nonneg (KBrkGrow n)). lia. Qed.

#[using="Type"] Lemma ob_brk_grant_B : forall L x md B n cur, LINK HTOP FORB L x md -> BI UB0 x md B -> CH (KBrkGrow n) <= B ->
  vm_brk (m_vmmaps md) = w64 cur -> PGSZ <= cur -> cur mod PGSZ = 0 -> 1 <= n -> cur + PGSZ * n + PGSZ < 2 ^ 64 ->
  BI UB0 (kstep x (KBrkGrow n) 1) (with_brk_next md (w64 (cur + PGSZ * n)) (w64 (cur + PGSZ * n))) (B - CH (KBrkGrow n)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L x md B n cur HL HB Hc Hv H1 H2 Hn H3. apply (BI_step UB0 x _ md _ B _ HB Hc (CH_nonneg _)).
  pose proof (Um_brk HTOP FORB L x md HL cur (cur + PGSZ * n) Hv H1 ltac:(unfold PGSZ in *; lia) ltac:(unfold PGSZ in *; lia) H2
                ltac:(apply mod_add0; [exact H2 | rewrite Z.mul_comm; apply Z.mod_mul; unfold PGSZ; lia])) as U.
  cbn [CH]. replace (Z.max 0 n) with n by lia. unfold PGSZ in *. lia.
Qed.

#[using="Type"] Lemma ob_guard_B : forall L x md B a, LINK HTOP FORB L x md -> BI UB0 x md B -> CH KGuard <= B -> 0 <= a -> a + PGSZ < 2 ^ 64 ->
  BI UB0 (kstep x KGuard 1) (fixed_na_next (w64 50) (w64 a) (w64 PGSZ) md) (B - CH KGuard).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L x md B a HL HB Hc H1 H2. apply (BI_step UB0 x _ md _ B _ HB Hc (CH_nonneg _)).
  pose proof (Um_guard HTOP FORB L x md HL a H1 H2). cbn [CH]. lia.
Qed.

#[using="Type"] Lemma ob_rw_B : forall L x md B len, LINK HTOP FORB L x md -> BI UB0 x md B -> CH (KMmapRW len) <= B -> 1 <= len < 2 ^ 63 ->
  exists a, fresh_rw_guard (w64 34) md (page_round len) a.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L x md B len HL (HB1 & HB2 & HB3) Hc Hl. destruct (page_round_props len ltac:(lia)) as (P1 & P2 & P3).
  cbn [CH] in Hc. replace (Z.max 0 (page_round len)) with (page_round len) in Hc by lia.
  apply (rw_guard HTOP FORB L x md HL); [lia|]. unfold PGSZ in *. lia.
Qed.

#[using="Type"] Lemma ob_rw'_B : forall L x md B len a, LINK HTOP FORB L x md -> BI UB0 x md B -> CH (KMmapRW len) <= B -> 1 <= len < 2 ^ 63 ->
  fresh_rw_guard (w64 34) md (page_round len) a ->
  BI UB0 (kstep x (KMmapRW len) 1) (fresh_rw_next (w64 34) a (w64 (page_round len)) md) (B - CH (KMmapRW len)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L x md B len a HL HB Hc Hl Ha. apply (BI_step UB0 x _ md _ B _ HB Hc (CH_nonneg _)).
  destruct (page_round_props len ltac:(lia)) as (P1 & P2 & P3). destruct Ha as (A1 & A2 & A3 & _).
  pose proof (alloc_top_lt (m_vmmaps md)) as AT. pose proof (urange a) as RA.
  assert (UN : bv_unsigned (w64 (page_round len)) = page_round len) by (apply u_w64; unfold two_pow_64, PGSZ in *; lia).
  pose proof (Um_rw HTOP FORB L x md HL a (w64 (page_round len)) ltac:(rewrite UN; unfold two_pow_64, PGSZ in *; lia)) as U.
  rewrite UN in U. cbn [CH]. replace (Z.max 0 (page_round len)) with (page_round len) by lia. unfold PGSZ. lia.
Qed.

#[using="Type"] Lemma ob_na_B : forall L x md B s len, LINK HTOP FORB L x md -> BI UB0 x md B -> CH (KMmapNone len) <= B ->
  kf_of s = x -> req_ok s (KMmapNone len) -> exists a, place_ok md (page_round len) a.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L x md B s len HL (HB1 & HB2 & HB3) Hc Hx Hrq. cbn [CH] in Hc.
  apply (place_na HTOP FORB L x md HL s len Hx Hrq). unfold PGSZ in *. lia.
Qed.

#[using="Type"] Lemma ob_na'_B : forall L x md B len a, LINK HTOP FORB L x md -> BI UB0 x md B -> CH (KMmapNone len) <= B -> 1 <= len < 2 ^ 63 ->
  place_ok md (page_round len) a ->
  BI UB0 (kstep x (KMmapNone len) 1) (fresh_na_next (w64 34) a (w64 (page_round len)) md) (B - CH (KMmapNone len)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L x md B len a HL HB Hc Hl Ha. apply (BI_step UB0 x _ md _ B _ HB Hc (CH_nonneg _)).
  destruct (page_round_props len ltac:(lia)) as (P1 & P2 & P3). destruct Ha as (A1 & A2 & A3 & _).
  pose proof (alloc_top_lt (m_vmmaps md)) as AT. pose proof (urange a) as RA.
  assert (UN : bv_unsigned (w64 (page_round len)) = page_round len) by (apply u_w64; unfold two_pow_64, PGSZ in *; lia).
  pose proof (Um_na HTOP FORB L x md HL a (w64 (page_round len)) ltac:(rewrite UN; unfold two_pow_64, PGSZ in *; lia)) as U.
  cbn [CH]. unfold PGSZ. lia.
Qed.

#[using="Type"] Lemma ob_pr_B : forall L x md B p, LINK HTOP FORB L x md -> BI UB0 x md B -> CH (KMprotect p) <= B ->
  0 <= loc_addr L (LMem p) -> loc_addr L (LMem p) + PGSZ < 2 ^ 64 ->
  mprotect_budget_ok md (w64 (loc_addr L (LMem p))) (w64 PGSZ) = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L x md B p HL (HB1 & HB2 & HB3) Hc H1 H2. cbn [CH] in Hc.
  unfold mprotect_budget_ok, vm_backing_within_limit. apply Z.leb_le.
  pose proof (Um_pr HTOP FORB L x md HL (loc_addr L (LMem p)) H1 H2) as U.
  pose proof (backing_le_Um (mprotect_model_next md (w64 (loc_addr L (LMem p))) (w64 PGSZ))) as BU.
  pose proof (lk_lim _ _ _ _ _ HL) as LM.
  change (vm_limit (m_vmmaps (mprotect_model_next md (w64 (loc_addr L (LMem p))) (w64 PGSZ)))) with (vm_limit (m_vmmaps md)).
  unfold PGSZ in *. lia.
Qed.

#[using="Type"] Lemma ob_pr'_B : forall L x md B p, LINK HTOP FORB L x md -> BI UB0 x md B -> CH (KMprotect p) <= B ->
  0 <= loc_addr L (LMem p) -> loc_addr L (LMem p) + PGSZ < 2 ^ 64 ->
  BI UB0 (kstep x (KMprotect p) 1) (mprotect_model_next md (w64 (loc_addr L (LMem p))) (w64 PGSZ)) (B - CH (KMprotect p)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L x md B p HL HB Hc H1 H2. apply (BI_step UB0 x _ md _ B _ HB Hc (CH_nonneg _)).
  pose proof (Um_pr HTOP FORB L x md HL (loc_addr L (LMem p)) H1 H2). cbn [CH]. lia.
Qed.

#[using="Type"] Lemma ob_munmap_B : forall L x md B r len rg, LINK HTOP FORB L x md -> BI UB0 x md B -> CH (KMunmap r len) <= B ->
  nth_error (kf_regions x) r = Some rg -> rg_kind rg = RkMap -> rg_live rg = true -> rg_len rg = page_round len ->
  BI UB0 (kstep x (KMunmap r len) 1) (munmap_next (w64 (ly_reg L r)) (w64 (page_round len)) md) (B - CH (KMunmap r len)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L x md B r len rg HL HB Hc H1 H2 H3 H4. apply (BI_step UB0 x _ md _ B _ HB Hc (CH_nonneg _)).
  pose proof (lk_maps _ _ _ _ _ HL r rg (conj H1 (conj H2 H3))) as Hh. apply map_has_In in Hh. rewrite H4 in Hh.
  destruct (lk_rgeo _ _ _ _ _ HL r rg H1 H3) as (G1 & G2 & G3 & G4 & G5). pose proof (alloc_top_lt (m_vmmaps md)) as AT.
  pose proof (U_munmap_next md (w64 (ly_reg L r)) (w64 (page_round len)) (lk_lazy _ _ _ _ _ HL) (lk_mdisj _ _ _ _ _ HL)
                (maps_inrange HTOP FORB L x md HL) Hh
                ltac:(rewrite !u_w64 by (rewrite <- ?H4; unfold two_pow_64, PGSZ in *; lia); rewrite <- H4; unfold two_pow_64, PGSZ in *; lia)) as U.
  cbn [CH]. lia.
Qed.

End Obl.

(* [comment removed for export] *)
Theorem tree_rz_B : forall segs cfg (Hoff : sc_alloc cfg = false) FORB HTOP (HTOPB : HTOP <= 2 ^ 47) (fx : FPState) rom UB0
  {A} (t : itree astate A) L regs pc m x md B (Q : @wpost A) (QK : kf -> A -> Prop) K,
  wk segs FORB HTOP rom L regs pc m t Q -> rk x t QK -> reqs_ok t -> safe t -> rb CH B t ->
  LINK HTOP FORB L x md -> BI UB0 x md B ->
  (forall L' r regs' pc' m' x' md' B', Q L' r regs' pc' m' -> QK x' r -> LINK HTOP FORB L' x' md' -> BI UB0 x' md' B' ->
     vm_only md md' -> realizes_cfg segs cfg (mkCfg (@mkst fx regs' pc' m' rom) md') K) ->
  realizes_cfg segs cfg (mkCfg (@mkst fx regs pc m rom) md) K.
Proof.
  intros segs cfg Hoff FORB HTOP HTOPB fx rom UB0 A t L regs pc m x md B Q QK K Hw Hrk Hreq Hsafe Hrb HL HB HK.
  exact (@tree_rz segs cfg Hoff FORB HTOP HTOPB fx rom CH (BI UB0)
           (ob_junk_B UB0) (ob_query_B FORB HTOP UB0) (ob_brk_refuse_B FORB HTOP UB0) (ob_brk_grant_B FORB HTOP UB0)
           (ob_guard_B FORB HTOP UB0) (ob_rw_B FORB HTOP UB0) (ob_rw'_B FORB HTOP UB0) (ob_na_B FORB HTOP UB0)
           (ob_na'_B FORB HTOP UB0) (ob_pr_B FORB HTOP UB0) (ob_pr'_B FORB HTOP UB0) (ob_munmap_B FORB HTOP UB0)
           A t L regs pc m x md B Q QK K Hw Hrk Hreq Hsafe Hrb HL HB HK).
Qed.
