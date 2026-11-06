(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Export ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc Mall7vg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mall7vg.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall7vg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall7vg.MallocRC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac addr_diff_ok k :=
  let ok := eval vm_compute in (andb (Z.leb 0 k) (Z.leb k 8192))%Z in
  lazymatch ok with true => idtac | false => fail end.

Ltac solve_load ::=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        addr_diff_ok k;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | H : ro_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        addr_diff_ok k;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
        cbv delta [wa] in HR;
        first [ rewrite HR
              | replace (ov_read_bytes segs m a n) with (Some bs)
                  by (rewrite <- HR; f_equal; word_eq_tac) ]
    end
  end;
  load_post.

Ltac solve_store ::=
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
    rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        addr_diff_ok k;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
          cbv beta iota;
          match goal with
          | |- context [write_to_mem m a ?bs] =>
              replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
          end
        end
    | HS : store_ok segs m ?a' n = true |- _ =>
        cbv delta [wa] in HS;
        first [ rewrite HS
              | replace (store_ok segs m a n) with true
                  by (rewrite <- HS; f_equal; word_eq_tac);
                try replace (write_to_mem m a) with (write_to_mem m a')
                  by (f_equal; word_eq_tac) ];
        cbv beta iota
    end
  end.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Class RunRandom := {
  run_secret : Z;
  run_guard : Z;
  run_secret_range : 0 <= run_secret < 2^64;
  run_guard_range : 0 <= run_guard < 2^64 }.
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition CTX : Z := 0x62800.
Definition MLOCK : Z := 0x627f8.
Definition LIBC : Z := 0x62788.
Definition NEED_LOCKS : Z := 0x6278b.     (* [comment removed for export] *)
Definition PAGE_SIZE_A : Z := 0x627b8.    (* [comment removed for export] *)
Definition AUXV_CELL : Z := 0x62790.      (* [comment removed for export] *)
Definition GOT_SSP : Z := 0x307c8.        (* [comment removed for export] *)
Definition SSP_GUARD : Z := 0x62768.      (* [comment removed for export] *)
Definition MALLOC_REPLACED : Z := 0x62ba0.
Definition PTP : Z := 0x424f8.            (* [comment removed for export] *)
Definition PERRNO : Z := 0x42454.         (* [comment removed for export] *)
Definition SMALL_CNT : Z := 0x14d08.
Definition MED_CNT : Z := 0x14d23.
Definition SIZE_CLASSES : Z := 0x14ca8.
Definition DEBRUIJN : Z := 0x14c88.

Definition get_meta_entry : Z := 0x23534.
Definition malloc_entry : Z := 0x23cf4.      (* [comment removed for export] *)
Definition free_entry : Z := 0x23368.        (* [comment removed for export] *)
Definition alloc_meta_entry : Z := 0x23a1c.
Definition alloc_slot_entry : Z := 0x24064.
Definition nontrivial_free_entry : Z := 0x23644.
Definition mmap_entry : Z := 0x25418.
Definition munmap_entry : Z := 0x25620.
Definition mprotect_entry : Z := 0x25504.
Definition mremap_entry : Z := 0x2554c.
Definition enframe_entry : Z := 0x24908.
Definition realloc_entry : Z := 0x24bd4.      (* [comment removed for export] *)
Definition calloc_entry : Z := 0x230ec.
Definition allzerop_entry : Z := 0x24a58.
Definition lock_entry : Z := 0x2b800.
Definition unlock_entry : Z := 0x2ba88.

(* [comment removed for export] *)
Definition p0_reserved : list (Z * Z) := [(0x10000, 0x7000); (0x17000, 0x19000); (0x30000, 0x1000); (0x31000, 0x33000)].

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
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)
Variable st : mstate.
Variable m : word -> option byte.

Definition mrep_ctx : Prop :=
  rw_cells rsegs m CTX (ctx_head_cells st)
  /\ u64arr rsegs m (CTX + 80) (actives st)
  /\ u64arr rsegs m (CTX + 464) (usages st)
  /\ u8arr rsegs m (CTX + 848) (unmap_seqs st)
  /\ u8arr rsegs m (CTX + 880) (bouncess st)
  /\ rw_cells rsegs m (CTX + 912) (ctx_tail_cells st).

(* [comment removed for export] *)
Definition mrep_globals : Prop :=
  rw_cells rsegs m MLOCK [C4 (wz 0)]
  /\ rw_cells rsegs m NEED_LOCKS [C1 (b8 0)]
  /\ rw_cells rsegs m PAGE_SIZE_A [C8 (wz 4096)]
  /\ rw_cells rsegs m GOT_SSP [C8 (wz SSP_GUARD)]
  /\ rw_cells rsegs m SSP_GUARD [C8 (wz run_guard)].   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition area_rep (a : aptr) (ar : area) : Prop :=
  rw_cells rsegs m (conc st a) [C8 (wz (a_check ar)); C8 (pw st (a_next ar)); C4 (wz (a_nslots ar)); C4 (wz 0)]
  /\ (forall k, 0 <= k < NSLOTS ->
        rw_cells rsegs m (conc st a + AREA_HDR + META_SIZE * k)
                 (meta_cells st (get_meta_rec st (aadd a (AREA_HDR + META_SIZE * k)))))
  /\ rw_cells rsegs m (conc st a + 4064) [CB 32 (zeros 32)].
Definition mrep_areas : Prop :=
  forall a ar, (s_areas st) !! a = Some ar -> area_rep a ar.

(* [comment removed for export] *)
Definition group_rep (b : aptr) (gh : ghdr) : Prop :=
  exists w8 : byte,
    rw_cells rsegs m (conc st b) [C8 (pw st (g_meta gh)); C1 w8]
    /\ Z.land (bv_unsigned w8) 31 = g_active_idx gh.
Definition mrep_groups : Prop :=
  forall b gh, (s_groups st) !! b = Some gh -> group_rep b gh.

(* [comment removed for export] *)
Definition shadow_rep (rid : N) (r : region) : Prop :=
  wr_at rsegs m (r_base r) (round_up_pg (r_len r))
  /\ forall o v, 0 <= o < round_up_pg (r_len r) ->
       cell_read (get_shadow st rid) o = Known v ->
       bytes_at rsegs m (r_base r + o) [b8 v] /\ 0 <= v < 256.
Definition mrep_shadow : Prop :=
  forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> shadow_rep rid r.

(* [comment removed for export] *)
Definition regions_wf : Prop :=
  s_reserved st = p0_reserved
  /\ (forall rid r, (s_regions st) !! rid = Some r ->
        0 < r_base r /\ r_base r mod 4096 = 0 /\ 0 <= r_len r
        /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
        /\ ranges_free p0_reserved (r_base r) (round_up_pg (r_len r)) = true)
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
Definition mrep_W (st : mstate) : list (Z * Z) :=
  (CTX, CTX + 928)
  :: map (fun kr : N * region => (r_base (snd kr), r_base (snd kr) + round_up_pg (r_len (snd kr)))) (map_to_list (s_regions st)).

Definition blocks_preserved (L : list (Z * Z)) (m m' : word -> option byte) : Prop :=
  forall a, (exists bl, In bl L /\ fst bl <= a < fst bl + snd bl) -> m' (wa a) = m (wa a).

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
Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Lemma mrep_shadow_read : forall st m rid r o v,
  mrep st m -> (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
  0 <= o < round_up_pg (r_len r) ->
  cell_read (get_shadow st rid) o = Known v ->
  ov_read_bytes rsegs m (wa (r_base r + o)) 1 = Some [b8 v] /\ 0 <= v < 256.
Proof.
  (intros st m rid r o v; (first [ intro dR_49; dand6 dR_49 as WF _ _ _ _ SH | intros (WF & _ & _ & _ & _ & SH) ]); intros Hr Hk Ho Hc).
  destruct (SH rid r Hr Hk) as [HW HB]. destruct (HB o v Ho Hc) as [Hm Hv]. split; [|exact Hv].
  rewrite <- (Z.add_0_r (r_base r + o)). apply (bytes_at_read rsegs m _ [b8 v] 0 1 Hm); [lia|cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma mrep_shadow_read2 : forall st m rid r o v0 v1,
  mrep st m -> (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
  0 <= o -> o + 2 <= round_up_pg (r_len r) ->
  cell_read (get_shadow st rid) o = Known v0 ->
  cell_read (get_shadow st rid) (o + 1) = Known v1 ->
  ov_read_bytes rsegs m (wa (r_base r + o)) 2 = Some [b8 v0; b8 v1] /\ 0 <= v0 < 256 /\ 0 <= v1 < 256.
Proof.
  intros st m rid r o v0 v1 MR Hr Hk Ho Ho2 H0 H1.
  (first [ pose proof (MR) as dR_1; dand6 dR_1 as WF _ _ _ _ SH | pose proof MR as (WF & _ & _ & _ & _ & SH) ]).
  destruct (SH rid r Hr Hk) as [HW HB].
  destruct (HB o v0 ltac:(lia) H0) as [B0 V0]. destruct (HB (o + 1) v1 ltac:(lia) H1) as [B1 V1].
  split; [|split; assumption].
  assert (B : bytes_at rsegs m (r_base r + o) ([b8 v0] ++ [b8 v1])).
  { apply bytes_at_app. split; [exact B0|]. cbn [length Z.of_nat Pos.of_succ_nat].
    replace (r_base r + o + 1) with (r_base r + (o + 1)) by lia. exact B1. }
  rewrite <- (Z.add_0_r (r_base r + o)). apply (bytes_at_read rsegs m _ _ 0 2 B); [lia|cbn; lia].
Qed.

End CEIL.

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

Ltac nrm := rewrite ?zxb_b8, ?zx16_wz, ?b8_unsigned, ?wz_unsigned by lia.
Ltac st1 := step; try nrm.
Ltac showpc := match goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC" pc end.

(* [comment removed for export] *)
Definition size_classes_bytes : list byte :=
  Eval vm_compute in (match image_bytes rsegs SIZE_CLASSES 96 with Some bs => bs | None => [] end).

Lemma size_classes_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m SIZE_CLASSES [CB 96 size_classes_bytes].
Proof. intros m MI. apply (ro_cells_image rsegs m); [exact MI | vm_compute; reflexivity | unfold SIZE_CLASSES; lia | unfold SIZE_CLASSES; cbn; lia]. Qed.

Lemma size_classes_read : forall m sc, mem_inv rsegs m -> 0 <= sc < 48 ->
  ov_read_bytes rsegs m (wa (SIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc))).
Proof.
  intros m sc MI Hsc.
  destruct (size_classes_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  rewrite (bytes_at_read rsegs m SIZE_CLASSES size_classes_bytes (2 * sc) 2 B) by (cbn; lia).
  assert (Hn : exists n, sc = Z.of_nat n /\ (n < 48)%nat) by (exists (Z.to_nat sc); split; [lia|lia]).
  (first [ dex1 Hn as n; destruct Hn as [-> Hn] | dand3 Hn as n -> Hn | destruct Hn as (n & -> & Hn) ]).
  replace (Z.to_nat (2 * Z.of_nat n)) with (2 * n)%nat by lia.
  Ltac solve_bytes := vm_compute; f_equal; repeat first [ reflexivity | apply f_equal2; [apply bv_eq; reflexivity|] ].
  do 48 (destruct n as [|n]; [solve_bytes |]). lia.
Qed.

(* [comment removed for export] *)

Lemma size_class_range sc : 0 <= sc < 48 -> 1 <= size_class sc <= 8191.
Proof.
  intros H. unfold size_class.
  assert (F : Forall (fun x => 1 <= x <= 8191) size_classes).
  { unfold size_classes. repeat (constructor; [lia|]). constructor. }
  apply (Forall_nth (fun x => 1 <= x <= 8191) size_classes); [exact F|]. cbn. lia.
Qed.

(* [comment removed for export] *)

Lemma conc_region' : forall st (q : aptr) r,
  (s_regions st) !! (fst q) = Some r -> conc st q = r_base r + snd q.
Proof. intros st [rid off] r H. apply conc_region. exact H. Qed.

(* [comment removed for export] *)
Definition meta_slot (st : mstate) (g : aptr) : Prop :=
  exists a ar k, (s_areas st) !! a = Some ar /\ 0 <= k < NSLOTS /\ g = aadd a (AREA_HDR + META_SIZE * k).

Section CEIL2.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Lemma mrep_meta_chunk : forall st m g,
  mrep st m -> meta_slot st g ->
  rw_cells rsegs m (conc st g) (meta_cells st (get_meta_rec st g)).
Proof.
  (intros st m g MR; (first [ intro dR_50; dex3 dR_50 as a ar k; dand3 dR_50 as Ha Hk -> | intro dR_50; dand6 dR_50 as a ar k Ha Hk -> | intros (a & ar & k & Ha & Hk & ->) ])).
  (first [ pose proof (MR) as dR_3; dand6 dR_3 as WF _ _ AR _ _ | pose proof MR as (WF & _ & _ & AR & _ & _) ]).
  (first [ pose proof ((AR a ar Ha)) as dR_4; dand3 dR_4 as _ SL _ | destruct (AR a ar Ha) as (_ & SL & _) ]).
  (first [ dand5 WF as _ _ _ WA _ | destruct WF as (_ & _ & _ & WA & _) ]). (first [ pose proof ((WA a ar Ha)) as dR_6; dex1 dR_6 as r; destruct dR_6 as [Hr _] | pose proof ((WA a ar Ha)) as dR_6; dand3 dR_6 as r Hr _ | destruct (WA a ar Ha) as (r & Hr & _) ]).
  rewrite conc_aadd by (rewrite Hr; eauto).
  replace (conc st a + (AREA_HDR + META_SIZE * k)) with (conc st a + AREA_HDR + META_SIZE * k) by lia. apply SL. exact Hk.
Qed.

Lemma mrep_group_read : forall st m b gh,
  mrep st m -> (s_groups st) !! b = Some gh ->
  ov_read_bytes rsegs m (wa (conc st b)) 8 = Some (le8 (pw st (g_meta gh)))
  /\ exists w8 : byte, ov_read_bytes rsegs m (wa (conc st b + 8)) 1 = Some [w8] /\ Z.land (bv_unsigned w8) 31 = g_active_idx gh.
Proof.
  intros st m b gh MR Hb. (first [ pose proof (MR) as dR_7; dand6 dR_7 as _ _ _ _ GR _ | pose proof MR as (_ & _ & _ & _ & GR & _) ]).
  (first [ pose proof ((GR b gh Hb)) as dR_8; dex1 dR_8 as w8; destruct dR_8 as [RW Hw8] | pose proof ((GR b gh Hb)) as dR_8; dand3 dR_8 as w8 RW Hw8 | destruct (GR b gh Hb) as (w8 & RW & Hw8) ]). split.
  - rewrite <- (Z.add_0_r (conc st b)). apply (rw_cells_read_at rsegs m _ _ 0 (C8 (pw st (g_meta gh))) 8 _ RW); reflexivity.
  - exists w8. split; [|exact Hw8].
    apply (rw_cells_read_at rsegs m _ _ 8 (C1 w8) 1 _ RW); reflexivity.
Qed.

Lemma mrep_area_check_read : forall st m a ar,
  mrep st m -> (s_areas st) !! a = Some ar ->
  ov_read_bytes rsegs m (wa (conc st a)) 8 = Some (le8 (wz (a_check ar))).
Proof.
  intros st m a ar MR Ha. (first [ pose proof (MR) as dR_9; dand6 dR_9 as _ _ _ AR _ _ | pose proof MR as (_ & _ & _ & AR & _ & _) ]).
  (first [ pose proof ((AR a ar Ha)) as dR_10; dand3 dR_10 as HD _ _ | destruct (AR a ar Ha) as (HD & _ & _) ]).
  rewrite <- (Z.add_0_r (conc st a)). apply (rw_cells_read_at rsegs m _ _ 0 (C8 (wz (a_check ar))) 8 _ HD); reflexivity.
Qed.

Lemma mrep_ctx_secret_read : forall st m,
  mrep st m -> ov_read_bytes rsegs m (wa CTX) 8 = Some (le8 (wz (c_secret (ctx st)))).
Proof.
  (intros st m; (first [ intro dR_51; dand3 dR_51 as _ (HD & _) _ | intros (_ & (HD & _) & _) ])).
  rewrite <- (Z.add_0_r CTX). apply (rw_cells_read_at rsegs m _ _ 0 (C8 (wz (c_secret (ctx st)))) 8 _ HD); reflexivity.
Qed.

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
Definition ticks_ok (st : mstate) : Prop :=
  (forall rid sh u hl ch, (s_shadow st) !! rid = Some sh -> (r_hav sh) !! u = Some hl -> In ch hl -> (snd ch <= s_tick st)%N)
  /\ (forall rid sh pg t, (s_shadow st) !! rid = Some sh -> (r_havp sh) !! pg = Some t -> (t <= s_tick st)%N).


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma reserved_disjoint : forall b n, ranges_free p0_reserved b n = true ->
  (b + n <= 0x10000 \/ 0x17000 <= b) /\
  ((b + n <= 0x17000 \/ 0x30000 <= b) /\ (b + n <= 0x30000 \/ 0x31000 <= b) /\ (b + n <= 0x31000 \/ 0x64000 <= b)).
Proof.
  intros b n H. unfold ranges_free, p0_reserved in H. cbn [forallb fst snd] in H.
  unfold iv_disjoint in H. rewrite !Bool.andb_true_iff, !Bool.orb_true_iff, !Z.leb_le in H. lia.
Qed.
Lemma reserved_disjoint4 : forall b n, ranges_free p0_reserved b n = true ->
  (b + n <= 0x10000 \/ 0x17000 <= b) /\ (b + n <= 0x17000 \/ 0x30000 <= b)
  /\ (b + n <= 0x30000 \/ 0x31000 <= b) /\ (b + n <= 0x31000 \/ 0x64000 <= b).
Proof.
  intros b n H. unfold ranges_free, p0_reserved in H. cbn [forallb fst snd] in H.
  unfold iv_disjoint in H. rewrite !Bool.andb_true_iff, !Bool.orb_true_iff, !Z.leb_le in H. lia.
Qed.

(* [comment removed for export] *)
Definition wr_in (st : mstate) (rid : N) (a len : Z) : Prop :=
  exists r, (s_regions st) !! rid = Some r /\ lr_lo r <= a /\ a + len <= r_base r + round_up_pg (r_len r) /\ 0 <= len.

Lemma wr_in_image : forall st rid a len,
  regions_wf st -> wr_in st rid a len ->
  (a + len <= 0x31000 \/ 0x64000 <= a) /\ 0 <= a /\ (a + len <= 2^64 /\ (a + len <= 0x30000 \/ 0x31000 <= a)).
Proof.
  (intros st rid a len; (first [ intro dR_52; dand3 dR_52 as _ WR _ | intros (_ & WR & _) ]); (first [ intro dR_53; dex1 dR_53 as r; dand4 dR_53 as Hr H1 H2 H3 | intro dR_53; dand5 dR_53 as r Hr H1 H2 H3 | intros (r & Hr & H1 & H2 & H3) ])).
  (first [ pose proof ((WR rid r Hr)) as dR_11; dand5 dR_11 as B0 _ L0 BC RF | destruct (WR rid r Hr) as (B0 & _ & L0 & BC & RF) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  (first [ pose proof ((reserved_disjoint4 _ _ RF)) as dR_12; dand4 dR_12 as _ _ D3 D2 | destruct (reserved_disjoint4 _ _ RF) as (_ & _ & D3 & D2) ]). pose proof (round_up_pg_ge (r_len r)). pose proof (lr_lo_ge r). lia.
Qed.

Lemma wr_in_other : forall st rid a len rid' r',
  regions_wf st -> wr_in st rid a len -> (s_regions st) !! rid' = Some r' -> rid' <> rid ->
  a + len <= lr_lo r' \/ r_base r' + round_up_pg (r_len r') <= a.
Proof.
  (intros st rid a len rid' r'; (first [ intro dR_54; dand4 dR_54 as _ _ DJ _ | intros (_ & _ & DJ & _) ]); (first [ intro dR_55; dex1 dR_55 as r; dand4 dR_55 as Hr H1 H2 H3 | intro dR_55; dand5 dR_55 as r Hr H1 H2 H3 | intros (r & Hr & H1 & H2 & H3) ]); intros Hr' Hne).
  destruct (DJ rid r rid' r' Hr Hr' ltac:(congruence)); lia.
Qed.

(* [comment removed for export] *)
Lemma area_lr_lo : forall st a ar r, regions_wf st -> (s_areas st) !! a = Some ar -> (s_regions st) !! (fst a) = Some r ->
  lr_lo r <= r_base r + snd a.
Proof.
  (intros st a ar r; (first [ intro dR_56; dand5 dR_56 as _ _ _ WA _ | intros (_ & _ & _ & WA & _) ]); intros Ha Hr). (first [ pose proof ((WA a ar Ha)) as dR_13; dex1 dR_13 as r0; dand6 dR_13 as Hr0 _ _ _ _ LO | pose proof ((WA a ar Ha)) as dR_13; dand7 dR_13 as r0 Hr0 _ _ _ _ LO | destruct (WA a ar Ha) as (r0 & Hr0 & _ & _ & _ & _ & LO) ]).
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
  (intros st st' m a ar Hconc Hm; (first [ intro dR_59; dand3 dR_59 as H1 H2 H3 | intros (H1 & H2 & H3) ])).
  assert (Hpw : forall p, pw st' p = pw st p). { intros [p|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity. }
  assert (Hmc : forall mr, meta_cells st' mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !Hpw; reflexivity).
  unfold area_rep. rewrite !Hconc, Hpw. split; [exact H1|]. split; [|exact H3].
  intros k Hk. rewrite Hmc, Hm by exact Hk. apply H2. exact Hk.
Qed.

Lemma group_rep_ext : forall st st' m b gh,
  (forall p, conc st' p = conc st p) -> group_rep st m b gh -> group_rep st' m b gh.
Proof.
  (intros st st' m b gh Hconc; (first [ intro dR_60; dex1 dR_60 as w8; destruct dR_60 as [H1 H2] | intro dR_60; dand3 dR_60 as w8 H1 H2 | intros (w8 & H1 & H2) ])).
  assert (Hpw : forall p, pw st' p = pw st p). { intros [p|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity. }
  exists w8. rewrite Hconc, Hpw. auto.
Qed.

Lemma shadow_rep_ext : forall st st' m rid r,
  get_shadow st' rid = get_shadow st rid -> shadow_rep st m rid r -> shadow_rep st' m rid r.
Proof. intros st st' m rid r Hs [H1 H2]. split; [exact H1|]. intros o v Ho Hc. rewrite Hs in Hc. eauto. Qed.

(* [comment removed for export] *)
Lemma mrep_ctx_frame : forall st m a bs rid,
  regions_wf st -> wr_in st rid a (Z.of_nat (length bs)) -> mrep_ctx st m ->
  mrep_ctx st (write_to_mem m (wa a) bs).
Proof.
  (intros st m a bs rid WF WI; (first [ intro dR_61; dand6 dR_61 as H1 H2 H3 H4 H5 H6 | intros (H1 & H2 & H3 & H4 & H5 & H6) ])).
  (first [ pose proof ((wr_in_image st rid a _ WF WI)) as dR_14; dand3 dR_14 as D A0 A1 | destruct (wr_in_image st rid a _ WF WI) as (D & A0 & A1) ]).
  assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
  assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
  assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
  assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
  unfold mrep_ctx. unfold CTX in *. split; [|split; [|split; [|split; [|split]]]].
  - apply rw_cells_frame; [exact H1|lia|lia|cbn; lia].
  - apply u64arr_frame; [exact H2|lia|lia|rewrite L1; cbn; lia].
  - apply u64arr_frame; [exact H3|lia|lia|rewrite L2; cbn; lia].
  - apply u8arr_frame; [exact H4|lia|lia|rewrite L3; cbn; lia].
  - apply u8arr_frame; [exact H5|lia|lia|rewrite L4; cbn; lia].
  - apply rw_cells_frame; [exact H6|lia|lia|cbn; lia].
Qed.

Lemma mrep_globals_frame : forall st m a bs rid,
  regions_wf st -> wr_in st rid a (Z.of_nat (length bs)) -> mrep_globals m ->
  mrep_globals (write_to_mem m (wa a) bs).
Proof.
  (intros st m a bs rid WF WI; (first [ intro dR_62; dand5 dR_62 as H1 H2 H3 H4 H5 | intros (H1 & H2 & H3 & H4 & H5) ])).
  (first [ pose proof ((wr_in_image st rid a _ WF WI)) as dR_15; dand3 dR_15 as D A0 A1 | destruct (wr_in_image st rid a _ WF WI) as (D & A0 & A1) ]).
  unfold mrep_globals. unfold MLOCK, NEED_LOCKS, PAGE_SIZE_A, GOT_SSP, SSP_GUARD in *.
  split; [|split; [|split; [|split]]].
  - apply rw_cells_frame; [exact H1|lia|lia|cbn; lia].
  - apply rw_cells_frame; [exact H2|lia|lia|cbn; lia].
  - apply rw_cells_frame; [exact H3|lia|lia|cbn; lia].
  - apply rw_cells_frame; [exact H4|lia|lia|cbn; lia].
  - apply rw_cells_frame; [exact H5|lia|lia|cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma area_rep_frame : forall st m a bs ar0 ar,
  regions_wf st -> (s_areas st) !! ar0 = Some ar ->
  0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  (conc st ar0 + 4096 <= a \/ a + Z.of_nat (length bs) <= conc st ar0) ->
  area_rep st m ar0 ar -> area_rep st (write_to_mem m (wa a) bs) ar0 ar.
Proof.
  (intros st m a bs ar0 ar WF Har A0 A1 D; (first [ intro dR_63; dand3 dR_63 as H1 H2 H3 | intros (H1 & H2 & H3) ])).
  unfold area_rep. split; [|split].
  - apply rw_cells_frame; [exact H1|lia|lia|cbn; lia].
  - intros k Hk. apply rw_cells_frame; [apply H2; exact Hk|lia|lia|]. unfold AREA_HDR, META_SIZE, NSLOTS in *. cbn. lia.
  - apply rw_cells_frame; [exact H3|lia|lia|cbn; lia].
Qed.

Lemma group_rep_frame : forall st m a bs b gh,
  0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  (conc st b + 9 <= a \/ a + Z.of_nat (length bs) <= conc st b) ->
  group_rep st m b gh -> group_rep st (write_to_mem m (wa a) bs) b gh.
Proof.
  (intros st m a bs b gh A0 A1 D; (first [ intro dR_64; dex1 dR_64 as w8; destruct dR_64 as [H1 H2] | intro dR_64; dand3 dR_64 as w8 H1 H2 | intros (w8 & H1 & H2) ])). exists w8. split; [|exact H2].
  apply rw_cells_frame; [exact H1|lia|lia|cbn; lia].
Qed.

Lemma shadow_rep_frame : forall st m a bs rid r,
  0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  (r_base r + round_up_pg (r_len r) <= a \/ a + Z.of_nat (length bs) <= r_base r) ->
  shadow_rep st m rid r -> shadow_rep st (write_to_mem m (wa a) bs) rid r.
Proof.
  intros st m a bs rid r A0 A1 D [HW HB]. split; [apply wr_at_write; exact HW|].
  intros o v Ho Hc. destruct (HB o v Ho Hc) as [Hb Hv]. split; [|exact Hv].
  apply bytes_at_write_other; [exact Hb|lia|lia|cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma area_conc : forall st a ar, regions_wf st -> (s_areas st) !! a = Some ar ->
  exists r, (s_regions st) !! (fst a) = Some r /\ conc st a = r_base r + snd a
            /\ 0 <= snd a /\ snd a + 4096 <= round_up_pg (r_len r) /\ snd a mod 4096 = 0 /\ r_kind r <> RKGroup
            /\ 0 < r_base r /\ r_base r mod 4096 = 0 /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling.
Proof.
  (intros st a ar; (first [ intro dR_65; dand5 dR_65 as _ WR _ WA _ | intros (_ & WR & _ & WA & _) ]); intros Ha). (first [ pose proof ((WA a ar Ha)) as dR_16; dex1 dR_16 as r; dand6 dR_16 as Hr A0 A1 AL NK _ | pose proof ((WA a ar Ha)) as dR_16; dand7 dR_16 as r Hr A0 A1 AL NK _ | destruct (WA a ar Ha) as (r & Hr & A0 & A1 & AL & NK & _) ]).
  (first [ pose proof ((WR _ r Hr)) as dR_17; dand5 dR_17 as B0 BAL _ BC _ | destruct (WR _ r Hr) as (B0 & BAL & _ & BC & _) ]).
  exists r. rewrite (conc_region' st a r Hr). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto.
Qed.

Lemma group_conc : forall st b gh, regions_wf st -> (s_groups st) !! b = Some gh ->
  exists r, (s_regions st) !! (fst b) = Some r /\ conc st b = r_base r + snd b
            /\ r_kind r = RKGroup /\ 0 <= snd b /\ snd b + 16 <= round_up_pg (r_len r) /\ snd b mod 16 = 0
            /\ 0 < r_base r /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling.
Proof.
  (intros st b gh; (first [ intro dR_66; dand5 dR_66 as _ WR _ _ WG | intros (_ & WR & _ & _ & WG) ]); intros Hb). (first [ pose proof ((WG b gh Hb)) as dR_18; dex1 dR_18 as r; dand5 dR_18 as Hr K B0 B1 AL | pose proof ((WG b gh Hb)) as dR_18; dand6 dR_18 as r Hr K B0 B1 AL | destruct (WG b gh Hb) as (r & Hr & K & B0 & B1 & AL) ]).
  (first [ pose proof ((WR _ r Hr)) as dR_19; dand5 dR_19 as R0 _ _ RC _ | destruct (WR _ r Hr) as (R0 & _ & _ & RC & _) ]).
  exists r. rewrite (conc_region' st b r Hr). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto.
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
    { unfold stale. apply Bool.not_true_iff_false. rewrite existsb_exists. ((first [ intro dR_67; dand3 dR_67 as [cov t] Hin Hb | intros ([cov t] & Hin & Hb) ])).
      destruct (r_hav sh !! (snd p `div` 16)) eqn:E3; cbn in Hin; [|contradiction].
      apply Bool.andb_true_iff in Hb. destruct Hb as [_ Hb]. apply N.ltb_lt in Hb.
      pose proof (T1 _ _ _ _ _ E E3 Hin) as HT. cbn [snd] in HT. exfalso. apply (N.lt_irrefl t). eapply N.le_lt_trans; [exact HT | exact Hb]. }
    rewrite SP, SU. reflexivity.
  - rewrite lookup_empty. cbn. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mrep_wr8 : forall st m p v r,
  mrep st m -> ticks_ok st ->
  (s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup -> 0 <= snd p < round_up_pg (r_len r) ->
  (forall b gh, (s_groups st) !! b = Some gh -> fst b = fst p -> ~ (snd b <= snd p < snd b + 9)) ->
  0 <= v < 256 ->
  mrep (wr8 p v st) (write_to_mem m (wa (r_base r + snd p)) [b8 v]).
Proof.
  intros st m p v r MR TK Hr Hk Ho Hgrp Hv.
  (first [ pose proof (MR) as dR_20; dand6 dR_20 as WF CX GL AR GR SH | pose proof MR as (WF & CX & GL & AR & GR & SH) ]). pose proof (lr_lo_group r Hk) as LRr.
  assert (WI : wr_in st (fst p) (r_base r + snd p) (Z.of_nat (length [b8 v]))).
  { exists r. cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto; lia. }
  (first [ pose proof ((wr_in_image st _ _ _ WF WI)) as dR_21; dand3 dR_21 as D A0 A1 | destruct (wr_in_image st _ _ _ WF WI) as (D & A0 & A1) ]). cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat] in D, A1.
  assert (Hconc : forall q, conc (wr8 p v st) q = conc st q) by (intros; reflexivity).
  split; [|split; [|split; [|split; [|split]]]].
  - (* [comment removed for export] *) exact WF.
  - eapply mrep_ctx_ext; [reflexivity|exact Hconc|]. eapply mrep_ctx_frame; eauto.
  - eapply mrep_globals_frame; eauto.
  - intros a ar Ha. cbn in Ha. eapply area_rep_ext; [exact Hconc|intros; reflexivity|].
    (first [ pose proof ((area_conc st a ar WF Ha)) as dR_22; dex1 dR_22 as ra; dand7 dR_22 as Hra Ca Sa0 Sa1 SaL NK _ | pose proof ((area_conc st a ar WF Ha)) as dR_22; dand8 dR_22 as ra Hra Ca Sa0 Sa1 SaL NK _ | destruct (area_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & _) ]).
    pose proof (area_lr_lo st a ar ra WF Ha Hra) as LRa.
    apply area_rep_frame; [exact WF|exact Ha|lia|cbn; lia| |exact (AR a ar Ha)]. rewrite Ca. cbn.
    destruct (N.eq_dec (fst a) (fst p)) as [E|NE].
    + rewrite E in Hra. rewrite Hr in Hra. inversion Hra; subst ra. congruence.
    + destruct (wr_in_other st _ _ _ _ ra WF WI Hra NE); cbn in *; lia.
  - intros b gh Hb. cbn in Hb. eapply group_rep_ext; [exact Hconc|].
    (first [ pose proof ((group_conc st b gh WF Hb)) as dR_23; dex1 dR_23 as rb; dand6 dR_23 as Hrb Cb Kb Sb0 Sb1 _ | pose proof ((group_conc st b gh WF Hb)) as dR_23; dand7 dR_23 as rb Hrb Cb Kb Sb0 Sb1 _ | destruct (group_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _) ]). pose proof (lr_lo_group rb Kb) as LRb.
    apply group_rep_frame; [lia|cbn; lia| |exact (GR b gh Hb)]. rewrite Cb. cbn.
    destruct (N.eq_dec (fst b) (fst p)) as [E|NE].
    + rewrite E in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb. specialize (Hgrp b gh Hb E). lia.
    + destruct (wr_in_other st _ _ _ _ rb WF WI Hrb NE); cbn in *; lia.
  - intros rid r' Hr' Hk'. cbn in Hr'.
    destruct (N.eq_dec rid (fst p)) as [E|NE].
    + subst rid. rewrite Hr in Hr'. inversion Hr'; subst r'.
      destruct (SH (fst p) r Hr Hk) as [HW HB]. split; [apply wr_at_write; exact HW|].
      intros o v' Ho' Hc.
      destruct (Z.eq_dec o (snd p)) as [->|NEo].
      * rewrite cell_read_wr8_same in Hc by assumption. inversion Hc; subst v'. split; [|lia].
        apply bytes_at_write_same; cbn; lia.
      * rewrite cell_read_wr8_other in Hc by exact NEo. destruct (HB o v' Ho' Hc) as [Hb Hv']. split; [|exact Hv'].
        apply bytes_at_write_other; [exact Hb|lia|cbn; lia|cbn; lia].
    + eapply shadow_rep_ext; [apply get_shadow_wr8_other; exact NE|].
      pose proof (lr_lo_group r' Hk') as LR'.
      apply shadow_rep_frame; [lia|cbn; lia| |exact (SH rid r' Hr' Hk')].
      destruct (wr_in_other st _ _ _ _ r' WF WI Hr' NE); cbn in *; lia.
Qed.

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

Lemma mrep_wr16 : forall st m p v r,
  mrep st m -> ticks_ok st ->
  (s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup -> 0 <= snd p -> snd p + 2 <= round_up_pg (r_len r) ->
  (forall b gh, (s_groups st) !! b = Some gh -> fst b = fst p -> snd p + 2 <= snd b \/ snd b + 9 <= snd p) ->
  0 <= v < 65536 ->
  mrep (wr16 p v st) (write_to_mem m (wa (r_base r + snd p)) (le2 (wz v))).
Proof.
  intros st m p v r MR TK Hr Hk Ho Ho2 Hg Hv.
  rewrite le2_split by lia.
  change (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256); b8 (v / 256)])
    with (write_to_mem (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)]) (wa (r_base r + snd p) + 1) [b8 (v / 256)]).
  rewrite wa_succ. unfold wr16. rewrite (wr8_mod st p v).
  replace (r_base r + snd p + 1) with (r_base r + snd (aadd p 1)) by (unfold aadd; cbn; lia).
  replace (Z.shiftr v 8) with (v / 256) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  pose proof (Z.mod_pos_bound v 256 ltac:(lia)).
  assert (Hd : 0 <= v / 256 < 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  apply (mrep_wr8 (wr8 p (v mod 256) st) _ (aadd p 1) (v / 256) r).
  - apply mrep_wr8; auto; [lia|]. intros b gh Hb E. specialize (Hg b gh Hb E). lia.
  - apply ticks_ok_wr8. exact TK.
  - cbn. exact Hr.
  - exact Hk.
  - cbn. lia.
  - intros b gh Hb E. cbn in Hb, E |- *. specialize (Hg b gh Hb E). lia.
  - exact Hd.
Qed.


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
Lemma mrep_meta_store4 : forall st m g (f : meta -> meta) (off : nat) v,
  mrep st m -> meta_slot st g -> 0 <= v < 2^32 ->
  (forall mr, cell_at (meta_cells st mr) off = Some (C4 (wz (match off with 24%nat => m_avail mr | _ => m_freed mr end)))) ->
  (forall mr, cell_upd (meta_cells st mr) off (C4 (wz v)) = meta_cells st (f mr)) ->
  (off = 24%nat \/ off = 28%nat) ->
  mrep (upd_meta g f st) (write_to_mem m (wa (conc st g + Z.of_nat off)) (le4 (wz v))).
Proof.
  (intros st m g f off v MR; (first [ intro dR_68; dex3 dR_68 as a ar k; dand3 dR_68 as Ha Hk Eg | intro dR_68; dand6 dR_68 as a ar k Ha Hk Eg | intros (a & ar & k & Ha & Hk & Eg) ]); intros Hv Hat Hupd Hoff).
  (first [ pose proof (MR) as dR_24; dand6 dR_24 as WF CX GL AR GR SH | pose proof MR as (WF & CX & GL & AR & GR & SH) ]).
  (first [ pose proof ((area_conc st a ar WF Ha)) as dR_25; dex1 dR_25 as ra; dand9 dR_25 as Hra Ca Sa0 Sa1 SaL NK RB0 RBAL RBC | pose proof ((area_conc st a ar WF Ha)) as dR_25; dand10 dR_25 as ra Hra Ca Sa0 Sa1 SaL NK RB0 RBAL RBC | destruct (area_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  pose proof (area_lr_lo st a ar ra WF Ha Hra) as LRa.
  assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
  unfold AREA_HDR, META_SIZE, NSLOTS in *.
  assert (WI : wr_in st (fst a) (conc st g + Z.of_nat off) (Z.of_nat (length (le4 (wz v))))).
  { exists ra. rewrite length_le4. cbn [Z.of_nat Pos.of_succ_nat Pos.to_nat]. split; [exact Hra|]. rewrite HG, Ca. destruct Hoff; subst; cbn; lia. }
  assert (Hconc : forall q, conc (upd_meta g f st) q = conc st q) by (intros; reflexivity).
  split; [|split; [|split; [|split; [|split]]]].
  - exact WF.
  - eapply mrep_ctx_ext; [reflexivity|exact Hconc|]. eapply mrep_ctx_frame; eauto.
  - eapply mrep_globals_frame; eauto.
  - intros a' ar' Ha'. cbn in Ha'.
    assert (Hpw : forall q, pw (upd_meta g f st) q = pw st q) by (intros [q|]; reflexivity).
    assert (Hmc : forall mr, meta_cells (upd_meta g f st) mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !Hpw; reflexivity).
    (first [ pose proof ((area_conc st a' ar' WF Ha')) as dR_26; dex1 dR_26 as ra'; dand7 dR_26 as Hra' Ca' Sa0' Sa1' SaL' NK' _ | pose proof ((area_conc st a' ar' WF Ha')) as dR_26; dand8 dR_26 as ra' Hra' Ca' Sa0' Sa1' SaL' NK' _ | destruct (area_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _) ]).
    pose proof (area_lr_lo st a' ar' ra' WF Ha' Hra') as LRa'.
    destruct (decide (a' = a)) as [->|NEa].
    + (* [comment removed for export] *)
      rewrite Ha in Ha'. inversion Ha'; subst ar'.
      (first [ pose proof ((AR a ar Ha)) as dR_27; dand3 dR_27 as HD SL PD | destruct (AR a ar Ha) as (HD & SL & PD) ]). unfold area_rep. rewrite !Hconc, Hpw. rewrite length_le4 in *.
      split; [|split].
      * apply rw_cells_frame; [exact HD|lia|rewrite length_le4; cbn in *; lia|]. rewrite length_le4, HG. cbn. destruct Hoff; subst; cbn; lia.
      * intros k' Hk'. rewrite Hmc, get_meta_rec_upd.
        destruct (Z.eq_dec k' k) as [->|NEk].
        -- rewrite <- Eg, aptr_eqb_refl.
           replace (conc st g + Z.of_nat off) with (conc st a + 24 + 40 * k + Z.of_nat off) by (rewrite HG; lia).
           rewrite <- Hupd. unfold le4. change (Z_to_le_bytes 4 (bv_unsigned (wz v))) with (cbytes (C4 (wz v))).
           eapply rw_cells_write; [ | apply Hat | reflexivity | exact I].
           rewrite Eg. replace (24 + 40 * k) with (AREA_HDR + META_SIZE * k) by reflexivity. apply SL. unfold NSLOTS. lia.
        -- replace (aptr_eqb (aadd a (24 + 40 * k')) g) with false.
           2:{ symmetry. rewrite Eg. unfold aptr_eqb, aadd. cbn. rewrite N.eqb_refl. cbn. apply Z.eqb_neq. lia. }
           apply rw_cells_frame; [apply SL; lia|lia|rewrite length_le4; cbn in *; lia|].
           rewrite length_le4, HG. cbn [cells_size meta_cells csize Nat.add length]. unfold AREA_HDR, META_SIZE. destruct Hoff; subst; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; nia.
      * apply rw_cells_frame; [exact PD|lia|rewrite length_le4; cbn in *; lia|]. rewrite length_le4, HG. cbn. destruct Hoff; subst; cbn; lia.
    + (* [comment removed for export] *)
      assert (PG : fst a' <> fst a \/ (fst a' = fst a /\ (snd a' + 4096 <= snd a \/ snd a + 4096 <= snd a'))).
      { destruct (N.eq_dec (fst a') (fst a)) as [E|NE]; [right|left; exact NE]. split; [exact E|].
        assert (snd a' <> snd a) by (intros E2; apply NEa; destruct a, a'; cbn in *; congruence).
        Z.div_mod_to_equations. nia. }
      eapply area_rep_ext; [exact Hconc| |].
      { intros k0 Hk0. rewrite get_meta_rec_upd.
        replace (aptr_eqb (aadd a' (AREA_HDR + META_SIZE * k0)) g) with false; [reflexivity|].
        symmetry. rewrite Eg. unfold aptr_eqb, aadd, AREA_HDR, META_SIZE. cbn [fst snd].
        destruct PG as [NE|[E PG]].
        - rewrite (proj2 (N.eqb_neq _ _) NE). reflexivity.
        - rewrite E, N.eqb_refl. cbn [andb]. apply Z.eqb_neq. unfold NSLOTS in *. lia. }
      apply area_rep_frame; [exact WF|exact Ha'|lia|rewrite length_le4; cbn in *; lia| |exact (AR a' ar' Ha')].
      rewrite length_le4, Ca', HG, Ca. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat].
      destruct PG as [NE|[E PG]].
      * destruct (wr_in_other st _ _ _ _ ra' WF WI Hra' NE); rewrite ?HG, ?Ca in *; cbn in *; lia.
      * rewrite E, Hra in Hra'. inversion Hra'; subst ra'. destruct Hoff; subst; cbn; lia.
  - intros b gh Hb. cbn in Hb. eapply group_rep_ext; [exact Hconc|].
    (first [ pose proof ((group_conc st b gh WF Hb)) as dR_28; dex1 dR_28 as rb; dand6 dR_28 as Hrb Cb Kb Sb0 Sb1 _ | pose proof ((group_conc st b gh WF Hb)) as dR_28; dand7 dR_28 as rb Hrb Cb Kb Sb0 Sb1 _ | destruct (group_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _) ]). pose proof (lr_lo_group rb Kb) as LRb.
    apply group_rep_frame; [lia|rewrite length_le4; cbn in *; lia| |exact (GR b gh Hb)]. rewrite Cb, length_le4. cbn.
    assert (NE : fst b <> fst a) by (intros E; rewrite E, Hra in Hrb; inversion Hrb; subst; congruence).
    destruct (wr_in_other st _ _ _ _ rb WF WI Hrb NE); cbn in *; lia.
  - intros rid r' Hr' Hk'. cbn in Hr'.
    eapply shadow_rep_ext; [reflexivity|]. pose proof (lr_lo_group r' Hk') as LR'.
    apply shadow_rep_frame; [lia|rewrite length_le4; cbn in *; lia| |exact (SH rid r' Hr' Hk')]. rewrite length_le4. cbn.
    assert (NE : rid <> fst a) by (intros E; subst; rewrite Hra in Hr'; inversion Hr'; subst; congruence).
    destruct (wr_in_other st _ _ _ _ r' WF WI Hr' NE); cbn in *; lia.
Qed.

Lemma mrep_meta_set_avail : forall st m g v,
  mrep st m -> meta_slot st g -> 0 <= v < 2^32 ->
  mrep (upd_meta g (m_set_avail v) st) (write_to_mem m (wa (conc st g + 24)) (le4 (wz v))).
Proof.
  intros. change 24 with (Z.of_nat 24).
  apply (mrep_meta_store4 st m g (m_set_avail v) 24%nat v); auto; intros; reflexivity.
Qed.

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

Lemma mrep_set_active : forall st m sc v,
  mrep st m -> 0 <= sc < 48 ->
  mrep (set_active sc v st) (write_to_mem m (wa (CTX + 80 + 8 * sc)) (le8 (pw st v))).
Proof.
  intros st m sc v MR Hsc. (first [ pose proof (MR) as dR_29; dand6 dR_29 as WF (C1 & C2 & C3 & C4 & C5 & C6) (G1 & G2 & G3 & G4 & G5) AR GR SH | pose proof MR as (WF & (C1 & C2 & C3 & C4 & C5 & C6) & (G1 & G2 & G3 & G4 & G5) & AR & GR & SH) ]).
  assert (Hconc : forall q, conc (set_active sc v st) q = conc st q) by (intros; reflexivity).
  assert (Hpw : forall q, pw (set_active sc v st) q = pw st q) by (intros [q|]; reflexivity).
  assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
  pose proof (length_le8 (pw st v)) as L8.
  unfold CTX in *.
  split; [|split; [|split; [|split; [|split]]]].
  - exact WF.
  - unfold mrep_ctx.
    change (ctx_head_cells (set_active sc v st)) with (ctx_head_cells st).
    change (usages (set_active sc v st)) with (usages st).
    change (unmap_seqs (set_active sc v st)) with (unmap_seqs st).
    change (bouncess (set_active sc v st)) with (bouncess st).
    assert (E6 : ctx_tail_cells (set_active sc v st) = ctx_tail_cells st).
    { unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx set_active upd_ctx c_seq c_brk set_active_map]. destruct (c_brk (s_ctx st)); reflexivity. }
    rewrite E6, actives_set_active by lia. unfold CTX.
    assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
    assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
    assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
    split; [|split; [|split; [|split; [|split]]]].
    + apply rw_cells_frame; [exact C1|lia|rewrite L8; lia|rewrite L8; cbn; lia].
    + replace (403456 + 80 + 8 * sc) with ((403456 + 80) + 8 * sc) by lia. apply u64arr_write; [exact C2| rewrite L1; lia].
    + apply u64arr_frame; [exact C3|lia|rewrite L8; lia|rewrite L8, L2; lia].
    + apply u8arr_frame; [exact C4|lia|rewrite L8; lia|rewrite L8, L3; lia].
    + apply u8arr_frame; [exact C5|lia|rewrite L8; lia|rewrite L8, L4; lia].
    + apply rw_cells_frame; [exact C6|lia|rewrite L8; lia|rewrite L8; cbn; lia].
  - unfold mrep_globals, MLOCK, NEED_LOCKS, PAGE_SIZE_A, GOT_SSP, SSP_GUARD in *. split; [|split; [|split; [|split]]].
    + apply rw_cells_frame; [exact G1|lia|rewrite L8; lia|rewrite L8; cbn; lia].
    + apply rw_cells_frame; [exact G2|lia|rewrite L8; lia|rewrite L8; cbn; lia].
    + apply rw_cells_frame; [exact G3|lia|rewrite L8; lia|rewrite L8; cbn; lia].
    + apply rw_cells_frame; [exact G4|lia|rewrite L8; lia|rewrite L8; cbn; lia].
    + apply rw_cells_frame; [exact G5|lia|rewrite L8; lia|rewrite L8; cbn; lia].
  - intros a ar Ha. cbn in Ha. eapply area_rep_ext; [exact Hconc|intros; reflexivity|].
    (first [ pose proof ((area_conc st a ar WF Ha)) as dR_30; dex1 dR_30 as ra; dand5 dR_30 as Hra Ca Sa0 Sa1 _ | pose proof ((area_conc st a ar WF Ha)) as dR_30; dand6 dR_30 as ra Hra Ca Sa0 Sa1 _ | destruct (area_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & _) ]).
    (first [ dand3 WF as _ WR _ | destruct WF as (_ & WR & _) ]). (first [ pose proof ((WR _ ra Hra)) as dR_32; dand5 dR_32 as _ _ _ _ RF | destruct (WR _ ra Hra) as (_ & _ & _ & _ & RF) ]). destruct (reserved_disjoint _ _ RF) as [_ D].
    apply area_rep_frame; [exact (proj1 MR)|exact Ha|lia|rewrite L8; lia| |exact (AR a ar Ha)].
    rewrite L8, Ca. pose proof (round_up_pg_ge (r_len ra)). cbn. lia.
  - intros b gh Hb. cbn in Hb. eapply group_rep_ext; [exact Hconc|].
    (first [ pose proof ((group_conc st b gh WF Hb)) as dR_33; dex1 dR_33 as rb; dand6 dR_33 as Hrb Cb _ Sb0 Sb1 _ | pose proof ((group_conc st b gh WF Hb)) as dR_33; dand7 dR_33 as rb Hrb Cb _ Sb0 Sb1 _ | destruct (group_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _) ]).
    (first [ dand3 WF as _ WR _ | destruct WF as (_ & WR & _) ]). (first [ pose proof ((WR _ rb Hrb)) as dR_35; dand5 dR_35 as _ _ _ _ RF | destruct (WR _ rb Hrb) as (_ & _ & _ & _ & RF) ]). destruct (reserved_disjoint _ _ RF) as [_ D].
    apply group_rep_frame; [lia|rewrite L8; lia| |exact (GR b gh Hb)]. rewrite L8, Cb. cbn. lia.
  - intros rid r' Hr' Hk'. cbn in Hr'. eapply shadow_rep_ext; [reflexivity|].
    (first [ dand3 WF as _ WR _ | destruct WF as (_ & WR & _) ]). (first [ pose proof ((WR _ r' Hr')) as dR_37; dand5 dR_37 as _ _ _ _ RF | destruct (WR _ r' Hr') as (_ & _ & _ & _ & RF) ]). destruct (reserved_disjoint _ _ RF) as [_ D].
    apply shadow_rep_frame; [lia|rewrite L8; lia| |exact (SH rid r' Hr' Hk')]. rewrite L8. cbn. lia.
Qed.

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
  ((first [ intro dR_69; dand3 dR_69 as [c' h'] Hin Hb | intros ([c' h'] & Hin & Hb) ])). apply Hs. cbn [fst snd] in Hb.
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

Lemma shadow_rep_le : forall st st' m rid r,
  shadow_le (get_shadow st rid) (get_shadow st' rid) -> shadow_rep st m rid r -> shadow_rep st' m rid r.
Proof. intros st st' m rid r [_ HL] [HW HB]. split; [exact HW|]. intros o v Ho Hc. apply HB; auto. Qed.

(* [comment removed for export] *)
Lemma mrep_upd_shadow : forall st m rid f,
  mrep st m -> ticks_ok st ->
  (shadow_le (get_shadow st rid) (f (get_shadow st rid)) /\ sh_ticks (f (get_shadow st rid)) (s_tick st)) ->
  mrep (upd_shadow rid f st) m /\ ticks_ok (upd_shadow rid f st).
Proof.
  intros st m rid f MR TK [HL HT]. (first [ pose proof (MR) as dR_38; dand6 dR_38 as WF CX GL AR GR SH | pose proof MR as (WF & CX & GL & AR & GR & SH) ]).
  assert (Hconc : forall q, conc (upd_shadow rid f st) q = conc st q) by (intros; reflexivity).
  assert (GS : forall rid', get_shadow (upd_shadow rid f st) rid' = if N.eqb rid' rid then f (get_shadow st rid) else get_shadow st rid').
  { intros rid'. rewrite (get_shadow_unfold (upd_shadow rid f st)). unfold upd_shadow, set_shadow. cbn [s_shadow].
    destruct (N.eqb_spec rid' rid); [subst; rewrite lookup_insert_eq; reflexivity| rewrite lookup_insert_ne by congruence; reflexivity]. }
  split.
  - split; [exact WF|]. split; [eapply mrep_ctx_ext; [reflexivity|exact Hconc|exact CX]|]. split; [exact GL|].
    split; [intros a ar Ha; eapply area_rep_ext; [exact Hconc|intros; reflexivity|exact (AR a ar Ha)]|].
    split; [intros b gh Hb; eapply group_rep_ext; [exact Hconc|exact (GR b gh Hb)]|].
    intros rid' r' Hr' Hk'. cbn in Hr'. eapply shadow_rep_le; [|exact (SH rid' r' Hr' Hk')].
    rewrite GS. destruct (N.eqb_spec rid' rid); [subst; exact HL| apply shadow_le_refl].
  - destruct TK as [T1 T2]. destruct HT as [HT1 HT2]. split.
    + intros rid' sh u hl ch Hs Hu Hin. cbn [s_tick upd_shadow set_shadow] in *.
      pose proof (GS rid') as G. rewrite (get_shadow_unfold (upd_shadow rid f st)) in G. cbn [s_shadow upd_shadow set_shadow] in G. rewrite Hs in G. cbn in G.
      destruct (N.eqb_spec rid' rid); [subst sh; eapply HT1; eauto|].
      unfold get_shadow in G. destruct (s_shadow st !! rid') eqn:E; cbn in G; [subst; eapply T1; eauto| subst; rewrite lookup_empty in Hu; discriminate].
    + intros rid' sh pg t Hs Hp. cbn [s_tick upd_shadow set_shadow] in *.
      pose proof (GS rid') as G. rewrite (get_shadow_unfold (upd_shadow rid f st)) in G. cbn [s_shadow upd_shadow set_shadow] in G. rewrite Hs in G. cbn in G.
      destruct (N.eqb_spec rid' rid); [subst sh; eapply HT2; eauto|].
      unfold get_shadow in G. destruct (s_shadow st !! rid') eqn:E; cbn in G; [subst; eapply T2; eauto| subst; rewrite lookup_empty in Hp; discriminate].
Qed.

Lemma mrep_havoc : forall st m p n, mrep st m -> ticks_ok st -> mrep (havoc p n st) m /\ ticks_ok (havoc p n st).
Proof.
  intros st m p n MR TK. unfold havoc. destruct (n <=? 0); [auto|].
  apply mrep_upd_shadow; [exact MR|exact TK|].
  pose proof (sh_ticks_of_ticks_ok st (fst p) TK) as T0.
  set (sh := get_shadow st (fst p)) in *. destruct sh as [cells hav havp]. cbn [r_cells r_hav r_havp].
  destruct ((snd p + 4095) / 4096 <? (snd p + n) / 4096).
  - destruct (havoc_pages_le cells hav havp ((snd p + 4095) / 4096) ((snd p + n) / 4096) (s_tick st) T0) as [L1 T1].
    set (hav1 := if snd p <? (snd p + 4095) / 4096 * 4096 then havoc_units (snd p) ((snd p + 4095) / 4096 * 4096) (s_tick st) hav else hav).
    assert (S1 : shadow_le (mkShadow cells hav havp) (mkShadow cells hav1 havp) /\ sh_ticks (mkShadow cells hav1 havp) (s_tick st)).
    { subst hav1. destruct (snd p <? _); [apply havoc_units_le; exact T0| split; [apply shadow_le_refl|exact T0]]. }
    destruct S1 as [L2 T2].
    set (hav2 := if (snd p + n) / 4096 * 4096 <? snd p + n then havoc_units ((snd p + n) / 4096 * 4096) (snd p + n) (s_tick st) hav1 else hav1).
    assert (S2 : shadow_le (mkShadow cells hav1 havp) (mkShadow cells hav2 havp) /\ sh_ticks (mkShadow cells hav2 havp) (s_tick st)).
    { subst hav2. destruct (_ <? snd p + n); [apply havoc_units_le; exact T2| split; [apply shadow_le_refl|exact T2]]. }
    destruct S2 as [L3 T3].
    destruct (havoc_pages_le cells hav2 havp ((snd p + 4095) / 4096) ((snd p + n) / 4096) (s_tick st) T3) as [L4 T4].
    split; [|exact T4]. eapply shadow_le_trans; [exact L2|]. eapply shadow_le_trans; [exact L3|exact L4].
  - apply havoc_units_le. exact T0.
Qed.

Lemma mrep_hdr_havoc : forall st m b, mrep st m -> ticks_ok st -> mrep (hdr_havoc b st) m /\ ticks_ok (hdr_havoc b st).
Proof.
  intros st m b MR TK. unfold hdr_havoc.
  apply mrep_upd_shadow; [exact MR|exact TK|].
  pose proof (sh_ticks_of_ticks_ok st (fst b) TK) as T0.
  set (sh := get_shadow st (fst b)) in *. destruct sh as [cells hav havp]. cbn [r_cells r_hav r_havp].
  apply hav_unit_step. exact T0.
Qed.

(* [comment removed for export] *)
Definition W_high (W : list (Z * Z)) : Prop := forall lo hi, In (lo, hi) W -> alloc_ceiling <= lo.

Lemma W_high_disjoint : forall W a n, W_high W -> a + n <= alloc_ceiling -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n HW Hn; cbn; [exact I|].
  split. { left. pose proof (HW lo hi ltac:(left; reflexivity)). lia. }
  apply IH; [| exact Hn]. intros lo' hi' Hin. apply (HW lo' hi'). right; exact Hin.
Qed.

Lemma mrep_transport_high : forall st m m' W,
  mrep st m -> munch W m m' -> wmono rsegs m m' -> W_high W -> mrep st m'.
Proof.
  (intros st m m' W; (first [ intro dR_70; dand6 dR_70 as WF CX GL AR GR SH | intros (WF & CX & GL & AR & GR & SH) ]); intros MU WM HW).
  (first [ pose proof (WF) as dR_39; dand5 dR_39 as Hres WR DJ WA WG | pose proof WF as (Hres & WR & DJ & WA & WG) ]).
  assert (D : forall a n, a + n <= alloc_ceiling -> disjoint_from W a n) by (intros; apply W_high_disjoint; assumption).
  (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  assert (TC : forall A cs, rw_cells rsegs m A cs -> A + Z.of_nat (cells_size cs) <= alloc_ceiling -> rw_cells rsegs m' A cs).
  { intros A cs H HB. eapply rw_cells_transport; eauto. }
  split; [exact WF|]. split; [|split; [|split; [|split]]].
  - (* [comment removed for export] *) (first [ dand6 CX as C1 C2 C3 C4 C5 C6 | destruct CX as (C1 & C2 & C3 & C4 & C5 & C6) ]). unfold mrep_ctx.
    split; [|split; [|split; [|split; [|split]]]].
    + apply TC; [exact C1 | unfold CTX; cbn; lia].
    + eapply u64arr_transport; eauto. apply D. unfold actives. rewrite map_length, seq_length. unfold CTX; cbn; lia.
    + eapply u64arr_transport; eauto. apply D. unfold usages. rewrite map_length, seq_length. unfold CTX; cbn; lia.
    + eapply u8arr_transport; eauto. apply D. unfold unmap_seqs. rewrite map_length, seq_length. unfold CTX; cbn; lia.
    + eapply u8arr_transport; eauto. apply D. unfold bouncess. rewrite map_length, seq_length. unfold CTX; cbn; lia.
    + apply TC; [exact C6 | unfold CTX; cbn; lia].
  - (* [comment removed for export] *) (first [ dand5 GL as G1 G2 G3 G4 G5 | destruct GL as (G1 & G2 & G3 & G4 & G5) ]). split; [|split; [|split; [|split]]].
    + apply TC; [exact G1 | unfold MLOCK; cbn; lia].
    + apply TC; [exact G2 | unfold NEED_LOCKS; cbn; lia].
    + apply TC; [exact G3 | unfold PAGE_SIZE_A; cbn; lia].
    + apply TC; [exact G4 | unfold GOT_SSP; cbn; lia].
    + apply TC; [exact G5 | unfold SSP_GUARD; cbn; lia].
  - (* [comment removed for export] *) intros a ar Ha. (first [ pose proof ((AR a ar Ha)) as dR_42; dand3 dR_42 as A1 A2 A3 | destruct (AR a ar Ha) as (A1 & A2 & A3) ]).
    (first [ pose proof ((area_conc st a ar WF Ha)) as dR_43; dex1 dR_43 as ra; dand9 dR_43 as Hra Ca Sa0 Sa1 SaL NK RB0 RBAL RBC | pose proof ((area_conc st a ar WF Ha)) as dR_43; dand10 dR_43 as ra Hra Ca Sa0 Sa1 SaL NK RB0 RBAL RBC | destruct (area_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    split; [|split].
    + apply TC; [exact A1 | cbn; lia].
    + intros k Hk. apply TC; [apply A2; exact Hk |]. unfold meta_cells; cbn [cells_size csize Nat.add]. unfold AREA_HDR, META_SIZE, NSLOTS in *. lia.
    + apply TC; [exact A3 | cbn; lia].
  - (* [comment removed for export] *) intros b gh Hb. (first [ pose proof ((GR b gh Hb)) as dR_44; dex1 dR_44 as w8; destruct dR_44 as [R Hw8] | pose proof ((GR b gh Hb)) as dR_44; dand3 dR_44 as w8 R Hw8 | destruct (GR b gh Hb) as (w8 & R & Hw8) ]). exists w8. split; [|exact Hw8].
    (first [ pose proof ((group_conc st b gh WF Hb)) as dR_45; dex1 dR_45 as rb; dand8 dR_45 as Hrb Cb Sb0 Sb1 SbL RB0 RBAL RBC | pose proof ((group_conc st b gh WF Hb)) as dR_45; dand9 dR_45 as rb Hrb Cb Sb0 Sb1 SbL RB0 RBAL RBC | destruct (group_conc st b gh WF Hb) as (rb & Hrb & Cb & Sb0 & Sb1 & SbL & RB0 & RBAL & RBC) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    apply TC; [exact R | cbn; lia].
  - (* [comment removed for export] *) intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB].
    (first [ pose proof ((WR rid r Hr)) as dR_46; dand5 dR_46 as B0 BAL L0 BC _ | destruct (WR rid r Hr) as (B0 & BAL & L0 & BC & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    split.
    + eapply wr_at_transport; eauto.
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      eapply bytes_at_transport; eauto. apply D. cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma mrep_set_tick : forall st m t, mrep st m -> mrep (set_tick t st) m.
Proof.
  (intros st m t; (first [ intro dR_71; dand6 dR_71 as WF CX GL AR GR SH | intros (WF & CX & GL & AR & GR & SH) ])).
  split; [exact WF|]. split; [|split; [exact GL|split; [|split]]].
  - eapply mrep_ctx_ext; [reflexivity | intros; reflexivity | exact CX].
  - intros a ar Ha. eapply area_rep_ext; [intros; reflexivity | intros; reflexivity | exact (AR a ar Ha)].
  - intros b gh Hb. eapply group_rep_ext; [intros; reflexivity | exact (GR b gh Hb)].
  - intros rid r Hr Hk. eapply shadow_rep_ext; [reflexivity | exact (SH rid r Hr Hk)].
Qed.

End CEIL2.

Lemma ticks_ok_set_tick : forall st t, (s_tick st <= t)%N -> ticks_ok st -> ticks_ok (set_tick t st).
Proof.
  intros st t Ht [T1 T2]. split; cbn.
  - intros rid sh u hl ch H1 H2 H3. pose proof (T1 rid sh u hl ch H1 H2 H3). lia.
  - intros rid sh pg t' H1 H2. pose proof (T2 rid sh pg t' H1 H2). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p0_find_segment_none : forall z n, 1 <= n -> (z + n <= 0x10000 \/ 0x64000 <= z) ->
  find_segment rsegs z n = None.
Proof.
  intros z n Hn Hz. unfold rsegs, Ubsan.M.loaded_segments, Ubsan.Ubsan_loaded_segments. cbn [find_segment].
  replace (Z.of_N (seg_base Ubsan.Ubsan_segment_000)) with 0x10000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Ubsan.Ubsan_segment_000)) with 0x7000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Ubsan.Ubsan_segment_001)) with 0x17000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Ubsan.Ubsan_segment_001)) with 0x19000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Ubsan.Ubsan_segment_002)) with 0x30000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Ubsan.Ubsan_segment_002)) with 0x1000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Ubsan.Ubsan_segment_003)) with 0x31000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Ubsan.Ubsan_segment_003)) with 0x33000%Z by (vm_compute; reflexivity).
  destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + n) (0x10000 + 0x7000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0x17000 z); destruct (Z.leb_spec0 (z + n) (0x17000 + 0x19000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0x30000 z); destruct (Z.leb_spec0 (z + n) (0x30000 + 0x1000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0x31000 z); destruct (Z.leb_spec0 (z + n) (0x31000 + 0x33000)); cbn [andb]; try lia.
  all: reflexivity.
Qed.
Lemma p0_ro_addr_false : forall x : word,
  (bv_unsigned x + 1 <= 0x10000 \/ 0x64000 <= bv_unsigned x)%Z -> ro_addr rsegs x = false.
Proof. intros x Hx. unfold ro_addr. rewrite p0_find_segment_none by lia. reflexivity. Qed.
Lemma p0_memory_read_none : forall (x : word) n,
  (1 <= Z.of_N n)%Z -> (bv_unsigned x + Z.of_N n <= 0x10000 \/ 0x64000 <= bv_unsigned x)%Z -> memory_read rsegs x n = None.
Proof. intros x n Hn Hx. unfold memory_read. rewrite p0_find_segment_none by lia. reflexivity. Qed.
Lemma p0_wview_overlay : forall m (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x64000 <= bv_unsigned x)%Z -> wview rsegs m x = m x.
Proof.
  intros m x Hx. unfold wview. destruct (m x); [reflexivity|]. rewrite p0_find_segment_none by lia. reflexivity.
Qed.
Lemma p0_seg_rom_none : forall (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x64000 <= bv_unsigned x)%Z -> seg_rom rsegs x = None.
Proof. intros x Hx. unfold seg_rom. rewrite p0_memory_read_none by (cbn; lia). reflexivity. Qed.
Lemma p0_mrd_overlay : forall m (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x64000 <= bv_unsigned x)%Z -> mrd rsegs m x = m x.
Proof. intros m x Hx. unfold mrd. destruct (m x); [reflexivity|]. apply p0_seg_rom_none. exact Hx. Qed.
Lemma reserved_disjoint1 : forall b n, ranges_free p0_reserved b n = true -> 0 < n ->
  b + n <= 0x10000 \/ 0x64000 <= b.
Proof. intros b n H Hn. pose proof (reserved_disjoint b n H). lia. Qed.

Lemma wr_at_bytes_exist : forall m a n,
  wr_at rsegs m a n -> 0 <= n -> (a + n <= 0x10000 \/ 0x64000 <= a) ->
  exists bs, length bs = Z.to_nat n /\ bytes_at rsegs m a bs.
Proof.
  (intros m a n; (first [ intro dR_72; dand3 dR_72 as A0 An W | intros (A0 & An & W) ]); intros Hn Himg).
  assert (G : forall i, 0 <= i < n -> exists b, mrd rsegs m (wa (a + i)) = Some b).
  { intros i Hi. specialize (W i Hi). unfold wview in W. unfold mrd.
    destruct (m (wa (a + i))) as [b|]; [exists b; reflexivity|].
    exfalso. apply W.
    unfold rsegs, Ubsan.M.loaded_segments, Ubsan.Ubsan_loaded_segments. cbn [find_segment].
    replace (Z.of_N (seg_base Ubsan.Ubsan_segment_000)) with 0x10000%Z by (vm_compute; reflexivity).
    replace (Z.of_N (seg_size Ubsan.Ubsan_segment_000)) with 0x7000%Z by (vm_compute; reflexivity).
    replace (Z.of_N (seg_base Ubsan.Ubsan_segment_001)) with 0x17000%Z by (vm_compute; reflexivity).
    replace (Z.of_N (seg_size Ubsan.Ubsan_segment_001)) with 0x19000%Z by (vm_compute; reflexivity).
    replace (Z.of_N (seg_base Ubsan.Ubsan_segment_002)) with 0x30000%Z by (vm_compute; reflexivity).
    replace (Z.of_N (seg_size Ubsan.Ubsan_segment_002)) with 0x1000%Z by (vm_compute; reflexivity).
    replace (Z.of_N (seg_base Ubsan.Ubsan_segment_003)) with 0x31000%Z by (vm_compute; reflexivity).
    replace (Z.of_N (seg_size Ubsan.Ubsan_segment_003)) with 0x33000%Z by (vm_compute; reflexivity).
    rewrite wa_unsigned by lia.
    destruct (Z.leb_spec0 0x10000 (a + i)); destruct (Z.leb_spec0 (a + i + 1) (0x10000 + 0x7000)); cbn [andb]; try lia.
    all: destruct (Z.leb_spec0 0x17000 (a + i)); destruct (Z.leb_spec0 (a + i + 1) (0x17000 + 0x19000)); cbn [andb]; try lia.
    all: destruct (Z.leb_spec0 0x30000 (a + i)); destruct (Z.leb_spec0 (a + i + 1) (0x30000 + 0x1000)); cbn [andb]; try lia.
    all: destruct (Z.leb_spec0 0x31000 (a + i)); destruct (Z.leb_spec0 (a + i + 1) (0x31000 + 0x33000)); cbn [andb]; try reflexivity; lia. }
  (* [comment removed for export] *)
  assert (REC : forall k, (k <= Z.to_nat n)%nat -> exists bs, length bs = k /\ bytes_at rsegs m (a + (n - Z.of_nat k)) bs).
  { induction k as [|k IH]; intros Hk.
    - exists []. split; [reflexivity|]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
    - (first [ pose proof ((IH ltac:(lia))) as dR_47; dex1 dR_47 as bs; destruct dR_47 as [L B] | pose proof ((IH ltac:(lia))) as dR_47; dand3 dR_47 as bs L B | destruct (IH ltac:(lia)) as (bs & L & B) ]). destruct (G (n - Z.of_nat (S k)) ltac:(lia)) as (b & Hb).
      exists (b :: bs). split; [cbn; lia|].
      change (b :: bs) with ([b] ++ bs). apply bytes_at_app. split.
      + split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. destruct i; [|lia]. cbn. rewrite Z.add_0_r. exact Hb.
      + cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. replace (a + (n - Z.of_nat (S k)) + 1) with (a + (n - Z.of_nat k)) by lia. exact B. }
  (first [ pose proof ((REC (Z.to_nat n) ltac:(lia))) as dR_48; dex1 dR_48 as bs; destruct dR_48 as [L B] | pose proof ((REC (Z.to_nat n) ltac:(lia))) as dR_48; dand3 dR_48 as bs L B | destruct (REC (Z.to_nat n) ltac:(lia)) as (bs & L & B) ]). exists bs. split; [exact L|].
  replace (a + (n - Z.of_nat (Z.to_nat n))) with a in B by lia. exact B.
Qed.

