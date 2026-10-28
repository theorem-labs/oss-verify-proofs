(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac Image ZBridge SysStep SFMisc.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import F_syscalls.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition CTX : Z := 0x1a188.
Definition MLOCK : Z := 0x1a0d0.
Definition LIBC : Z := 0x1a120.
Definition NEED_LOCKS : Z := 0x1a123.     (* [comment removed for export] *)
Definition PAGE_SIZE_A : Z := 0x1a150.    (* [comment removed for export] *)
Definition SIZE_CLASSES : Z := 0x18170.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)      (* [comment removed for export] *)
(* [comment removed for export] *)        (* [comment removed for export] *)
Definition alloc_meta_entry : Z := 0x15fd4.
Definition alloc_slot_entry : Z := 0x162e0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition agent_reserved : list (Z * Z) := [(0x10000, 0x9000); (0x19000, 0x2000)].

Definition wz (z : Z) : word := Z_to_bv 64 z.
Definition b8 (z : Z) : byte := Z_to_bv 8 z.
(* [comment removed for export] *)
Definition pw (st : mstate) (p : optr) : word := wz (oconc st p).

(* [comment removed for export] *)
Definition meta_word (mr : meta) : Z :=
  m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr.

Definition meta_cells (st : mstate) (mr : meta) : list cell :=
  [C8 (pw st (m_prev mr)); C8 (pw st (m_next mr)); C8 (pw st (m_mem mr));
   C4 (wz (m_avail mr)); C4 (wz (m_freed mr)); C8 (wz (meta_word mr))].

Definition brk_word (st : mstate) : Z :=
  match c_brk (ctx st) with
  | BrkUntried => 0
  | BrkDead => 2^64 - 1
  | BrkLive rid off => conc st (rid, off)
  end.

Definition ctx_head_cells (st : mstate) : list cell :=
  let c := ctx st in
  [C8 (wz (c_secret c)); C4 (wz (c_init_done c)); C4 (wz (c_mmap_counter c));
   C8 (pw st (c_free_meta_head c)); C8 (pw st (c_avail_meta c));
   C8 (wz (c_avail_meta_count c)); C8 (wz (c_avail_meta_area_count c)); C8 (wz (c_meta_alloc_shift c));
   C8 (pw st (c_meta_area_head c)); C8 (pw st (c_meta_area_tail c)); C8 (pw st (c_avail_meta_areas c))].

Definition actives (st : mstate) : list word := map (fun i => pw st (active st (Z.of_nat i))) (seq 0 48).
Definition usages (st : mstate) : list word := map (fun i => wz (usage st (Z.of_nat i))) (seq 0 48).
Definition unmap_seqs (st : mstate) : list byte := map (fun i => b8 (unmap_seq st (Z.of_nat i))) (seq 0 32).
Definition bouncess (st : mstate) : list byte := map (fun i => b8 (bounces st (Z.of_nat i))) (seq 0 32).
Definition zeros (n : nat) : list byte := repeat (b8 0) n.
Definition ctx_tail_cells (st : mstate) : list cell :=
  [C1 (b8 (c_seq (ctx st))); CB 7 (zeros 7); C8 (wz (brk_word st))].

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lr_lo (r : region) : Z :=
  match r_kind r with RKBrk => r_base r + 4096 | _ => r_base r end.

Lemma lr_lo_ge r : r_base r <= lr_lo r.
Proof. unfold lr_lo. destruct (r_kind r); lia. Qed.
Lemma lr_lo_group r : r_kind r = RKGroup -> lr_lo r = r_base r.
Proof. unfold lr_lo. intros ->. reflexivity. Qed.
(* [comment removed for export] *)

Section MREP.
Variable st : mstate.
Variable m : word -> option byte.

Definition mrep_ctx : Prop :=
  rw_cells asegs m CTX (ctx_head_cells st)
  /\ u64arr asegs m (CTX + 80) (actives st)
  /\ u64arr asegs m (CTX + 464) (usages st)
  /\ u8arr asegs m (CTX + 848) (unmap_seqs st)
  /\ u8arr asegs m (CTX + 880) (bouncess st)
  /\ rw_cells asegs m (CTX + 912) (ctx_tail_cells st).

Definition mrep_globals : Prop :=
  rw_cells asegs m MLOCK [C4 (wz 0)]
  /\ rw_cells asegs m NEED_LOCKS [C1 (b8 0)]
  /\ rw_cells asegs m PAGE_SIZE_A [C8 (wz 4096)].

(* [comment removed for export] *)
Definition area_rep (a : aptr) (ar : area) : Prop :=
  rw_cells asegs m (conc st a) [C8 (wz (a_check ar)); C8 (pw st (a_next ar)); C4 (wz (a_nslots ar)); C4 (wz 0)]
  /\ (forall k, 0 <= k < NSLOTS ->
        rw_cells asegs m (conc st a + AREA_HDR + META_SIZE * k)
                 (meta_cells st (get_meta_rec st (aadd a (AREA_HDR + META_SIZE * k)))))
  /\ rw_cells asegs m (conc st a + 4064) [CB 32 (zeros 32)].
Definition mrep_areas : Prop :=
  forall a ar, (s_areas st) !! a = Some ar -> area_rep a ar.

(* [comment removed for export] *)
Definition group_rep (b : aptr) (gh : ghdr) : Prop :=
  exists w8 : byte,
    rw_cells asegs m (conc st b) [C8 (pw st (g_meta gh)); C1 w8]
    /\ Z.land (bv_unsigned w8) 31 = g_active_idx gh.
Definition mrep_groups : Prop :=
  forall b gh, (s_groups st) !! b = Some gh -> group_rep b gh.

(* [comment removed for export] *)
Definition shadow_rep (rid : N) (r : region) : Prop :=
  wr_at asegs m (r_base r) (round_up_pg (r_len r))
  /\ forall o v, 0 <= o < round_up_pg (r_len r) ->
       cell_read (get_shadow st rid) o = Known v ->
       bytes_at asegs m (r_base r + o) [b8 v] /\ 0 <= v < 256.
Definition mrep_shadow : Prop :=
  forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> shadow_rep rid r.

(* [comment removed for export] *)
Definition regions_wf : Prop :=
  s_reserved st = agent_reserved
  /\ (forall rid r, (s_regions st) !! rid = Some r ->
        0 < r_base r /\ r_base r mod 4096 = 0 /\ 0 <= r_len r
        /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
        /\ ranges_free agent_reserved (r_base r) (round_up_pg (r_len r)) = true)
  /\ (forall rid1 r1 rid2 r2, (s_regions st) !! rid1 = Some r1 -> (s_regions st) !! rid2 = Some r2 -> rid1 <> rid2 ->
        r_base r1 + round_up_pg (r_len r1) <= lr_lo r2 \/ r_base r2 + round_up_pg (r_len r2) <= lr_lo r1)
  (* [comment removed for export] *)
  /\ (forall a ar, (s_areas st) !! a = Some ar ->
        exists r, (s_regions st) !! (fst a) = Some r /\ 0 <= snd a /\ snd a + 4096 <= round_up_pg (r_len r) /\ snd a mod 4096 = 0
                  /\ r_kind r <> RKGroup /\ lr_lo r <= r_base r + snd a)
  /\ (forall b gh, (s_groups st) !! b = Some gh ->
        exists r, (s_regions st) !! (fst b) = Some r /\ r_kind r = RKGroup /\ 0 <= snd b /\ snd b + 16 <= round_up_pg (r_len r) /\ snd b mod 16 = 0).

Definition mrep : Prop :=
  regions_wf /\ mrep_ctx /\ mrep_globals /\ mrep_areas /\ mrep_groups /\ mrep_shadow.

End MREP.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma conc_aadd : forall st p d,
  is_Some ((s_regions st) !! (fst p)) -> conc st (aadd p d) = conc st p + d.
Proof.
  intros st [rid off] d [r Hr]. unfold conc, aadd, get_region. cbn. rewrite Hr. lia.
Qed.

Lemma conc_region : forall st rid off r,
  (s_regions st) !! rid = Some r -> conc st (rid, off) = r_base r + off.
Proof. intros. unfold conc, get_region. cbn. rewrite H. reflexivity. Qed.

Lemma round_up_pg_ge : forall x, x <= round_up_pg x.
Proof. intros. unfold round_up_pg, PGSZ. assert (0 <= Z.land (-x) (4096 - 1)) by (apply Z.land_nonneg; right; lia). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma wz_unsigned x : 0 <= x < 2^64 -> bv_unsigned (wz x) = x.
Proof. intros. unfold wz. apply unsigned_lit. lia. Qed.
Lemma b8_unsigned x : 0 <= x < 256 -> bv_unsigned (b8 x) = x.
Proof. intros. unfold b8. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn. apply Z.mod_small. lia. Qed.
Lemma zxb_b8 x : 0 <= x < 256 -> zxb (b8 x) = wz x.
Proof. intros. unfold zxb, wz. rewrite b8_unsigned by lia. reflexivity. Qed.
Lemma zx16_wz x : 0 <= x < 65536 -> zx16 (wz x) = wz x.
Proof. intros. unfold zx16, wz. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma sx32_wz x : 0 <= x < 2^31 -> sx32 (wz x) = wz x.
Proof. intros. unfold sx32, wz. rewrite unsigned_lit by lia. rewrite swrap32_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma land_ldiff_distr x a b : Z.land x (Z.ldiff a b) = Z.ldiff (Z.land x a) b.
Proof. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec. destruct (Z.testbit x n), (Z.testbit a n), (Z.testbit b n); reflexivity. Qed.

Lemma land_pgmask x : 0 <= x < 2^64 -> Z.land x 18446744073709547520 = x - x mod 4096.
Proof.
  intros Hx.
  assert (E : 18446744073709547520 = Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity. rewrite E.
  rewrite land_ldiff_distr. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^12) with 4096. pose proof (Z.div_mod x 4096). lia.
Qed.

(* [comment removed for export] *)
Lemma mod_mod_pow2 z a b : 0 <= a <= b -> (z mod 2^b) mod 2^a = z mod 2^a.
Proof. intros. apply Z.mod_mod_divide. exists (2^(b-a)). rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.

Lemma swrap32_mod32 z : (bv_swrap 32 z) mod 2^32 = z mod 2^32.
Proof.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2^32). change (2^32 `div` 2) with (2^31).
  rewrite Zminus_mod, Z.mod_mod by lia. rewrite <- Zminus_mod.
  replace (z + 2^31 - 2^31) with z by lia. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma signed_wz_small x : 0 <= x < 2^63 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros. rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64 / 2)%Z with (2^63)%Z. lia.
Qed.
End ACeilS1.


Ltac nrm := rewrite ?zxb_b8, ?zx16_wz, ?b8_unsigned, ?wz_unsigned by lia.
Ltac st1 := step; try nrm.
(* [comment removed for export] *)
Section ACeilS2. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma size_class_range sc : 0 <= sc < 48 -> 1 <= size_class sc <= 8191.
Proof.
  intros H. unfold size_class.
  assert (F : Forall (fun x => 1 <= x <= 8191) size_classes).
  { unfold size_classes. repeat (constructor; [lia|]). constructor. }
  apply (Forall_nth (fun x => 1 <= x <= 8191) size_classes); [exact F|]. cbn. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma conc_region' : forall st (q : aptr) r,
  (s_regions st) !! (fst q) = Some r -> conc st q = r_base r + snd q.
Proof. intros st [rid off] r H. apply conc_region. exact H. Qed.

(* [comment removed for export] *)
Definition meta_slot (st : mstate) (g : aptr) : Prop :=
  exists a ar k, (s_areas st) !! a = Some ar /\ 0 <= k < NSLOTS /\ g = aadd a (AREA_HDR + META_SIZE * k).

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma le2_lohi : forall lo hi, 0 <= lo < 256 -> 0 <= hi < 256 -> le2 (wz (lo + 256 * hi)) = [b8 lo; b8 hi].
Proof.
  intros lo hi Hl Hh. unfold le2, wz, b8. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  f_equal; [apply Z_to_bv8_mod; rewrite <- Zplus_mod_idemp_r; replace (256 * hi) with (hi * 2^8) by lia; rewrite Z_mod_mult; rewrite Z.add_0_r; reflexivity|].
  f_equal. apply Z_to_bv8_mod. rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
  replace (lo + 256 * hi) with (lo + hi * 256) by lia. rewrite Z.div_add, Z.div_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ticks_ok (st : mstate) : Prop :=
  (forall rid sh u hl ch, (s_shadow st) !! rid = Some sh -> (r_hav sh) !! u = Some hl -> In ch hl -> (snd ch <= s_tick st)%N)
  /\ (forall rid sh pg t, (s_shadow st) !! rid = Some sh -> (r_havp sh) !! pg = Some t -> (t <= s_tick st)%N).


(* [comment removed for export] *)
Lemma reserved_disjoint : forall b n, ranges_free agent_reserved b n = true ->
  (b + n <= 0x10000 \/ 0x19000 <= b) /\ (b + n <= 0x19000 \/ 0x1b000 <= b).
Proof.
  intros b n H. unfold ranges_free, agent_reserved in H. cbn [forallb fst snd] in H.
  unfold iv_disjoint in H. rewrite !Bool.andb_true_iff, !Bool.orb_true_iff, !Z.leb_le in H. lia.
Qed.

(* [comment removed for export] *)
Definition wr_in (st : mstate) (rid : N) (a len : Z) : Prop :=
  exists r, (s_regions st) !! rid = Some r /\ lr_lo r <= a /\ a + len <= r_base r + round_up_pg (r_len r) /\ 0 <= len.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma area_lr_lo : forall st a ar r, regions_wf st -> (s_areas st) !! a = Some ar -> (s_regions st) !! (fst a) = Some r ->
  lr_lo r <= r_base r + snd a.
Proof.
  (intros st a ar r; cps_intros (_ & _ & _ & WA & _); intros Ha Hr). cps_destruct (WA a ar Ha) as (r0 & Hr0 & _ & _ & _ & _ & LO).
  rewrite Hr in Hr0. inversion Hr0; subst. exact LO.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mrep_ctx_ext : forall st st' m,
  ctx st' = ctx st -> (forall p, conc st' p = conc st p) -> mrep_ctx st m -> mrep_ctx st' m.
Proof.
  intros st st' m Hc Hconc H.
  assert (Hpw : forall p, pw st' p = pw st p). { intros [p|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity. }
  assert (E1 : ctx_head_cells st' = ctx_head_cells st) by (unfold ctx_head_cells; rewrite Hc, !Hpw; reflexivity).
  assert (E2 : actives st' = actives st). { unfold actives. apply map_ext. intros. unfold active. rewrite Hc. apply Hpw. }
  assert (E3 : usages st' = usages st). { unfold usages. apply map_ext. intros. unfold usage. rewrite Hc. reflexivity. }
  assert (E4 : unmap_seqs st' = unmap_seqs st). { unfold unmap_seqs. apply map_ext. intros. unfold unmap_seq. rewrite Hc. reflexivity. }
  assert (E5 : bouncess st' = bouncess st). { unfold bouncess. apply map_ext. intros. unfold bounces. rewrite Hc. reflexivity. }
  assert (E6 : ctx_tail_cells st' = ctx_tail_cells st). { unfold ctx_tail_cells, brk_word. rewrite Hc. destruct (c_brk (ctx st)); rewrite ?Hconc; reflexivity. }
  unfold mrep_ctx in *. rewrite E1, E2, E3, E4, E5, E6. exact H.
Qed.

Lemma area_rep_ext : forall st st' m a ar,
  (forall p, conc st' p = conc st p) ->
  (forall k, 0 <= k < NSLOTS -> get_meta_rec st' (aadd a (AREA_HDR + META_SIZE * k)) = get_meta_rec st (aadd a (AREA_HDR + META_SIZE * k))) ->
  area_rep st m a ar -> area_rep st' m a ar.
Proof.
  (intros st st' m a ar Hconc Hm; cps_intros (H1 & H2 & H3)).
  assert (Hpw : forall p, pw st' p = pw st p). { intros [p|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity. }
  assert (Hmc : forall mr, meta_cells st' mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !Hpw; reflexivity).
  unfold area_rep. rewrite !Hconc, Hpw. split; [exact H1|]. split; [|exact H3].
  intros k Hk. rewrite Hmc, Hm by exact Hk. apply H2. exact Hk.
Qed.

Lemma group_rep_ext : forall st st' m b gh,
  (forall p, conc st' p = conc st p) -> group_rep st m b gh -> group_rep st' m b gh.
Proof.
  (intros st st' m b gh Hconc; cps_intros (w8 & H1 & H2)).
  assert (Hpw : forall p, pw st' p = pw st p). { intros [p|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity. }
  exists w8. rewrite Hconc, Hpw. auto.
Qed.

Lemma shadow_rep_ext : forall st st' m rid r,
  get_shadow st' rid = get_shadow st rid -> shadow_rep st m rid r -> shadow_rep st' m rid r.
Proof. intros st st' m rid r Hs [H1 H2]. split; [exact H1|]. intros o v Ho Hc. rewrite Hs in Hc. eauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma area_conc : forall st a ar, regions_wf st -> (s_areas st) !! a = Some ar ->
  exists r, (s_regions st) !! (fst a) = Some r /\ conc st a = r_base r + snd a
            /\ 0 <= snd a /\ snd a + 4096 <= round_up_pg (r_len r) /\ snd a mod 4096 = 0 /\ r_kind r <> RKGroup
            /\ 0 < r_base r /\ r_base r mod 4096 = 0 /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling.
Proof.
  (intros st a ar; cps_intros (_ & WR & _ & WA & _); intros Ha). cps_destruct (WA a ar Ha) as (r & Hr & A0 & A1 & AL & NK & _).
  cps_destruct (WR _ r Hr) as (B0 & BAL & _ & BC & _).
  exists r. rewrite (conc_region' st a r Hr). repeat split; auto.
Qed.

Lemma group_conc : forall st b gh, regions_wf st -> (s_groups st) !! b = Some gh ->
  exists r, (s_regions st) !! (fst b) = Some r /\ conc st b = r_base r + snd b
            /\ r_kind r = RKGroup /\ 0 <= snd b /\ snd b + 16 <= round_up_pg (r_len r) /\ snd b mod 16 = 0
            /\ 0 < r_base r /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling.
Proof.
  (intros st b gh; cps_intros (_ & WR & _ & _ & WG); intros Hb). cps_destruct (WG b gh Hb) as (r & Hr & K & B0 & B1 & AL).
  cps_destruct (WR _ r Hr) as (R0 & _ & _ & RC & _).
  exists r. rewrite (conc_region' st b r Hr). repeat split; auto.
Qed.

(* [comment removed for export] *)
Lemma s_shadow_wr8 : forall st p v,
  s_shadow (wr8 p v st) =
  <[fst p := mkShadow (<[snd p := (Z.land v 255, s_tick st)]> (r_cells (get_shadow st (fst p)))) (r_hav (get_shadow st (fst p))) (r_havp (get_shadow st (fst p)))]> (s_shadow st).
Proof. intros. reflexivity. Qed.

Lemma get_shadow_unfold : forall st rid, get_shadow st rid = default shadow0 ((s_shadow st) !! rid).
Proof. reflexivity. Qed.

Lemma get_shadow_wr8_same : forall st p v,
  get_shadow (wr8 p v st) (fst p) =
  mkShadow (<[snd p := (Z.land v 255, s_tick st)]> (r_cells (get_shadow st (fst p)))) (r_hav (get_shadow st (fst p))) (r_havp (get_shadow st (fst p))).
Proof. intros. rewrite (get_shadow_unfold (wr8 p v st)), s_shadow_wr8, lookup_insert_eq. reflexivity. Qed.

Lemma get_shadow_wr8_other : forall st p v rid, rid <> fst p ->
  get_shadow (wr8 p v st) rid = get_shadow st rid.
Proof. intros. rewrite (get_shadow_unfold (wr8 p v st)), s_shadow_wr8, lookup_insert_ne by congruence. reflexivity. Qed.

Lemma cell_read_wr8_other : forall st p v o, o <> snd p ->
  cell_read (get_shadow (wr8 p v st) (fst p)) o = cell_read (get_shadow st (fst p)) o.
Proof. intros. rewrite get_shadow_wr8_same. unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite lookup_insert_ne by congruence. reflexivity. Qed.

Lemma cell_read_wr8_same : forall st p v,
  ticks_ok st -> 0 <= v < 256 ->
  cell_read (get_shadow (wr8 p v st) (fst p)) (snd p) = Known v.
Proof.
  intros st p v [T1 T2] Hv. rewrite get_shadow_wr8_same. unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite lookup_insert_eq.
  replace (Z.land v 255) with v by (change 255 with (Z.ones 8); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
  unfold get_shadow. destruct (s_shadow st !! fst p) as [sh|] eqn:E; cbn.
  - assert (SP : stale_pg (r_havp sh !! (snd p `div` 4096)) (Some (s_tick st)) = false).
    { unfold stale_pg. destruct (r_havp sh !! (snd p `div` 4096)) eqn:E2; [|reflexivity].
      apply N.ltb_ge. eapply T2; eauto. }
    assert (SU : stale (default [] (r_hav sh !! (snd p `div` 16))) (snd p `mod` 16) (Some (s_tick st)) = false).
    { unfold stale. apply Bool.not_true_iff_false. rewrite existsb_exists. cps_intros ([cov t] & Hin & Hb).
      destruct (r_hav sh !! (snd p `div` 16)) eqn:E3; cbn in Hin; [|contradiction].
      apply Bool.andb_true_iff in Hb. destruct Hb as [_ Hb]. apply N.ltb_lt in Hb.
      pose proof (T1 _ _ _ _ _ E E3 Hin) as HT. cbn [snd] in HT. exfalso. apply (N.lt_irrefl t). eapply N.le_lt_trans; [exact HT | exact Hb]. }
    rewrite SP, SU. reflexivity.
  - rewrite lookup_empty. cbn. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ticks_ok_wr8 : forall st p v, ticks_ok st -> ticks_ok (wr8 p v st).
Proof.
  intros st p v [T1 T2]. split.
  - intros rid sh u hl ch Hs Hu Hin. cbn [s_tick wr8 upd_shadow set_shadow] in *.
    rewrite s_shadow_wr8 in Hs. destruct (N.eq_dec rid (fst p)) as [->|NE].
    + rewrite lookup_insert_eq in Hs. inversion Hs; subst sh. cbn in Hu.
      unfold get_shadow in Hu. destruct (s_shadow st !! fst p) as [sh0|] eqn:E; cbn in Hu.
      * eapply T1; eauto.
      * rewrite lookup_empty in Hu. discriminate.
    + rewrite lookup_insert_ne in Hs by congruence. eapply T1; eauto.
  - intros rid sh pg t Hs Hp. cbn [s_tick wr8 upd_shadow set_shadow] in *.
    rewrite s_shadow_wr8 in Hs. destruct (N.eq_dec rid (fst p)) as [->|NE].
    + rewrite lookup_insert_eq in Hs. inversion Hs; subst sh. cbn in Hp.
      unfold get_shadow in Hp. destruct (s_shadow st !! fst p) as [sh0|] eqn:E; cbn in Hp.
      * eapply T2; eauto.
      * rewrite lookup_empty in Hp. discriminate.
    + rewrite lookup_insert_ne in Hs by congruence. eapply T2; eauto.
Qed.

Lemma wr8_mod : forall st p v, wr8 p v st = wr8 p (v mod 256) st.
Proof.
  intros. unfold wr8, upd_shadow. cbn beta.
  replace (Z.land (v mod 256) 255) with (Z.land v 255); [reflexivity|].
  change 255 with (Z.ones 8). rewrite !Z.land_ones by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma le2_split : forall v, 0 <= v < 65536 -> le2 (wz v) = [b8 (v mod 256); b8 (v / 256)].
Proof.
  intros v Hv. replace v with (v mod 256 + 256 * (v / 256)) at 1 by (pose proof (Z.div_mod v 256); lia).
  rewrite le2_lohi; [reflexivity| |]; [pose proof (Z.mod_pos_bound v 256); lia | split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]].
Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)
Lemma get_meta_rec_upd : forall st g f g',
  get_meta_rec (upd_meta g f st) g' = if aptr_eqb g' g then f (get_meta_rec st g) else get_meta_rec st g'.
Proof.
  intros. unfold get_meta_rec at 1. unfold upd_meta, put_meta. cbn [s_metas set_metas].
  unfold aptr_eqb. destruct g as [gr go], g' as [gr' go']. cbn [fst snd].
  destruct (N.eqb_spec gr' gr); destruct (Z.eqb_spec go' go); cbn [andb]; subst;
    first [rewrite lookup_insert_eq; reflexivity | rewrite lookup_insert_ne by congruence; reflexivity].
Qed.

Lemma aptr_eqb_refl : forall g, aptr_eqb g g = true.
Proof. intros [a b]. unfold aptr_eqb. cbn. rewrite N.eqb_refl, Z.eqb_refl. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma map_seq_upd : forall {X} (f g : nat -> X) (j : nat) (x : X) n s,
  (forall i, (s <= i < s + n)%nat -> g i = if Nat.eqb i j then x else f i) ->
  (s <= j)%nat ->
  map g (seq s n) = upd (map f (seq s n)) (j - s) x.
Proof.
  intros X f g j x n. induction n as [|n IH]; intros s Hg Hj; [reflexivity|].
  cbn [seq map]. destruct (Nat.eq_dec j s) as [->|NE].
  - rewrite Nat.sub_diag. cbn [upd]. rewrite Hg by lia. rewrite Nat.eqb_refl. f_equal.
    apply map_ext_in. intros i Hi. apply in_seq in Hi. rewrite Hg by lia.
    destruct (Nat.eqb_spec i s); [lia|reflexivity].
  - replace (j - s)%nat with (S (j - S s)) by lia. cbn [upd]. f_equal.
    + rewrite Hg by lia. destruct (Nat.eqb_spec s j); [lia|reflexivity].
    + apply IH; [intros; apply Hg; lia|lia].
Qed.

Lemma active_set_active : forall st sc v i,
  active (set_active sc v st) i = if Z.eqb i sc then v else active st i.
Proof.
  intros. unfold active, set_active, upd_ctx. cbn [ctx s_ctx c_active set_active_map].
  destruct v as [p|]; destruct (Z.eqb_spec i sc); subst.
  - rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
  - rewrite lookup_delete_eq. reflexivity.
  - rewrite lookup_delete_ne by congruence. reflexivity.
Qed.

Lemma actives_set_active : forall st sc v, 0 <= sc < 48 ->
  actives (set_active sc v st) = upd (actives st) (Z.to_nat sc) (pw st v).
Proof.
  intros st sc v Hsc. unfold actives.
  replace (Z.to_nat sc) with (Z.to_nat sc - 0)%nat by lia.
  apply (map_seq_upd (fun i => pw st (active st (Z.of_nat i))) (fun i => pw (set_active sc v st) (active (set_active sc v st) (Z.of_nat i)))); [|lia].
  intros i Hi. rewrite active_set_active.
  assert (Hpw : forall q, pw (set_active sc v st) q = pw st q) by (intros [q|]; reflexivity).
  rewrite Hpw. destruct (Z.eqb_spec (Z.of_nat i) sc); destruct (Nat.eqb_spec i (Z.to_nat sc)); try reflexivity; lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sh_ticks (sh : shadow) (t : N) : Prop :=
  (forall u hl ch, (r_hav sh) !! u = Some hl -> In ch hl -> (snd ch <= t)%N)
  /\ (forall pg t', (r_havp sh) !! pg = Some t' -> (t' <= t)%N).

Definition shadow_le (sh sh' : shadow) : Prop :=
  r_cells sh' = r_cells sh /\ forall o v, cell_read sh' o = Known v -> cell_read sh o = Known v.

Lemma shadow_le_refl : forall sh, shadow_le sh sh. Proof. intros; split; auto. Qed.
Lemma shadow_le_trans : forall a b c, shadow_le a b -> shadow_le b c -> shadow_le a c.
Proof. intros a b c [E1 H1] [E2 H2]. split; [congruence|]. eauto. Qed.

Lemma In_filter_bool : forall {A} (f : A -> bool) (l : list A) x,
  In x (filter (fun y => f y) l) <-> In x l /\ f x = true.
Proof.
  intros A f l x. rewrite <- !list_elem_of_In. rewrite list_elem_of_filter.
  unfold Is_true. destruct (f x); intuition congruence.
Qed.

Lemma stale_hav_add : forall hl cov t b tc,
  (forall ch, In ch hl -> (snd ch <= t)%N) ->
  stale (hav_add cov t hl) b tc = false -> stale hl b tc = false.
Proof.
  intros hl cov t b tc Ht Hs. unfold stale in *.
  apply Bool.not_true_iff_false. apply Bool.not_true_iff_false in Hs. rewrite existsb_exists in *.
  cps_intros ([c' h'] & Hin & Hb). apply Hs. cbn [fst snd] in Hb.
  apply Bool.andb_true_iff in Hb. destruct Hb as [Hb1 Hb2]. apply Z.ltb_lt in Hb1.
  destruct (Z.ltb_spec cov c').
  - exists (c', h'). split; [|cbn [fst snd]; rewrite (proj2 (Z.ltb_lt _ _) Hb1), Hb2; reflexivity].
    unfold hav_add. right. apply In_filter_bool. split; [exact Hin|]. cbn. apply Z.ltb_lt. assumption.
  - exists (cov, t). split; [unfold hav_add; left; reflexivity|]. cbn [fst snd].
    rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [andb].
    destruct tc as [tc|]; [|reflexivity]. apply N.ltb_lt. apply N.ltb_lt in Hb2.
    pose proof (Ht _ Hin) as Hh. cbn [snd] in Hh. eapply N.lt_le_trans; [exact Hb2|exact Hh].
Qed.

Lemma hav_unit_step : forall cells hav havp u cov t,
  sh_ticks (mkShadow cells hav havp) t ->
  shadow_le (mkShadow cells hav havp) (mkShadow cells (<[u := hav_add cov t (default [] (hav !! u))]> hav) havp)
  /\ sh_ticks (mkShadow cells (<[u := hav_add cov t (default [] (hav !! u))]> hav) havp) t.
Proof.
  intros cells hav havp u cov t [T1 T2]. cbn [r_hav r_havp] in T1, T2.
  assert (Hl : forall ch, In ch (default [] (hav !! u)) -> (snd ch <= t)%N).
  { intros ch Hin. destruct (hav !! u) eqn:E2; cbn in Hin; [eapply T1; eauto| contradiction]. }
  split.
  - split; [reflexivity|]. intros o v Hc. unfold cell_read in *. cbn [r_cells r_hav r_havp] in *.
    destruct (Z.eq_dec (o / 16) u) as [E|NE].
    + rewrite E, lookup_insert_eq in Hc. cbn [default from_option id] in Hc. rewrite E.
      destruct (cells !! o) as [[v0 tc]|].
      * destruct (stale_pg (havp !! (o / 4096)) (Some tc)) eqn:SP; [cbn in Hc; discriminate|].
        destruct (stale (hav_add cov t (default [] (hav !! u))) (o mod 16) (Some tc)) eqn:SU; [cbn in Hc; discriminate|].
        rewrite (stale_hav_add _ _ _ _ _ Hl SU). exact Hc.
      * destruct (stale_pg (havp !! (o / 4096)) None) eqn:SP; [cbn in Hc; discriminate|].
        destruct (stale (hav_add cov t (default [] (hav !! u))) (o mod 16) None) eqn:SU; [cbn in Hc; discriminate|].
        rewrite (stale_hav_add _ _ _ _ _ Hl SU). exact Hc.
    + rewrite lookup_insert_ne in Hc by congruence. exact Hc.
  - split; cbn [r_hav r_havp]; [|exact T2].
    intros u' hl ch Hu Hin. destruct (Z.eq_dec u' u) as [->|NE].
    + rewrite lookup_insert_eq in Hu. inversion Hu; subst hl. unfold hav_add in Hin. destruct Hin as [<-|Hin]; [cbn; lia|].
      apply In_filter_bool in Hin. destruct Hin as [Hin _]. apply Hl. exact Hin.
    + rewrite lookup_insert_ne in Hu by congruence. eapply T1; eauto.
Qed.

Lemma hav_page_step : forall cells hav havp pg t,
  sh_ticks (mkShadow cells hav havp) t ->
  shadow_le (mkShadow cells hav havp) (mkShadow cells hav (<[pg := t]> havp))
  /\ sh_ticks (mkShadow cells hav (<[pg := t]> havp)) t.
Proof.
  intros cells hav havp pg t [T1 T2]. cbn [r_hav r_havp] in T1, T2. split.
  - split; [reflexivity|]. intros o v Hc. unfold cell_read in *. cbn [r_cells r_hav r_havp] in *.
    destruct (Z.eq_dec (o / 4096) pg) as [E|NE].
    + rewrite E, lookup_insert_eq in Hc. rewrite E.
      destruct (cells !! o) as [[v0 tc]|]; cbn [stale_pg orb] in Hc.
      * destruct (N.ltb_spec tc t); [discriminate|].
        destruct (havp !! pg) as [h|] eqn:E2; cbn [stale_pg].
        -- pose proof (T2 _ _ E2). replace (tc <? h)%N with false by (symmetry; apply N.ltb_ge; lia). exact Hc.
        -- exact Hc.
      * discriminate.
    + rewrite lookup_insert_ne in Hc by congruence. exact Hc.
  - split; cbn [r_hav r_havp]; [exact T1|].
    intros pg' t' Hp. destruct (Z.eq_dec pg' pg) as [->|NE].
    + rewrite lookup_insert_eq in Hp. inversion Hp; subst. lia.
    + rewrite lookup_insert_ne in Hp by congruence. eapply T2; eauto.
Qed.

Lemma Z_iter_invariant : forall {A} (f : A -> A) (Inv : A -> Prop) n x,
  (forall y, Inv y -> Inv (f y)) -> Inv x -> Inv (Z.iter n f x).
Proof.
  intros A f Inv n x Hf Hx. destruct n; cbn; auto. apply Pos.iter_invariant; auto.
Qed.

Lemma havoc_units_le : forall cells hav havp x y t,
  sh_ticks (mkShadow cells hav havp) t ->
  shadow_le (mkShadow cells hav havp) (mkShadow cells (havoc_units x y t hav) havp)
  /\ sh_ticks (mkShadow cells (havoc_units x y t hav) havp) t.
Proof.
  intros cells hav havp x y t T. unfold havoc_units.
  set (f := fun acc : Z * gmap Z (list (Z * N)) => _).
  apply (Z_iter_invariant f (fun acc => shadow_le (mkShadow cells hav havp) (mkShadow cells (snd acc) havp)
                                         /\ sh_ticks (mkShadow cells (snd acc) havp) t)).
  - intros [u h] [HL HT]. unfold f. cbn [fst snd].
    destruct (hav_unit_step cells h havp u (if u =? (y - 1) / 16 then (let r := y mod 16 in if r =? 0 then 16 else r) else 16) t HT) as [HL2 HT2].
    split; [eapply shadow_le_trans; eauto| exact HT2].
  - cbn [snd]. split; [apply shadow_le_refl| exact T].
Qed.

Lemma havoc_pages_le : forall cells hav havp p0 p1 t,
  sh_ticks (mkShadow cells hav havp) t ->
  shadow_le (mkShadow cells hav havp) (mkShadow cells hav (havoc_pages p0 p1 t havp))
  /\ sh_ticks (mkShadow cells hav (havoc_pages p0 p1 t havp)) t.
Proof.
  intros cells hav havp p0 p1 t T. unfold havoc_pages.
  set (f := fun acc : Z * gmap Z N => _).
  apply (Z_iter_invariant f (fun acc => shadow_le (mkShadow cells hav havp) (mkShadow cells hav (snd acc))
                                         /\ sh_ticks (mkShadow cells hav (snd acc)) t)).
  - intros [pg h] [HL HT]. unfold f. cbn [fst snd].
    destruct (hav_page_step cells hav h pg t HT) as [HL2 HT2].
    split; [eapply shadow_le_trans; eauto| exact HT2].
  - cbn [snd]. split; [apply shadow_le_refl| exact T].
Qed.

Lemma sh_ticks_of_ticks_ok : forall st rid, ticks_ok st -> sh_ticks (get_shadow st rid) (s_tick st).
Proof.
  intros st rid [T1 T2]. unfold get_shadow. destruct (s_shadow st !! rid) as [sh|] eqn:E; cbn.
  - split; [intros; eapply T1; eauto | intros; eapply T2; eauto].
  - split; cbn; intros; rewrite lookup_empty in *; discriminate.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_high (W : list (Z * Z)) : Prop := forall lo hi, In (lo, hi) W -> alloc_ceiling <= lo.

Lemma W_high_disjoint : forall W a n, W_high W -> a + n <= alloc_ceiling -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n HW Hn; cbn; [exact I|].
  split. { left. pose proof (HW lo hi ltac:(left; reflexivity)). lia. }
  apply IH; [| exact Hn]. intros lo' hi' Hin. apply (HW lo' hi'). right; exact Hin.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ticks_ok_set_tick : forall st t, (s_tick st <= t)%N -> ticks_ok st -> ticks_ok (set_tick t st).
Proof.
  intros st t Ht [T1 T2]. split; cbn.
  - intros rid sh u hl ch H1 H2 H3. pose proof (T1 rid sh u hl ch H1 H2 H3). lia.
  - intros rid sh pg t' H1 H2. pose proof (T2 rid sh pg t' H1 H2). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

End ACeilS2.
