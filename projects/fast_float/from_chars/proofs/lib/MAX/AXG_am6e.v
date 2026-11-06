(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMeta.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng AxBits MngZ MngRepr MngHeap MngImage MngWb MngWk MngGeoX MngLt MngSurgery MngExc MngNtfPre MngNtfC MngNtfM MngNtfS MngGM MngCtx2.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngHeap.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngMW0 MngMW1 MngMW2 MngShift AXG_am1 AXG_am3 AXG_am4 AXG_am5 AXG_am6 AXG_am7 AXG_am6b AXG_amr0 AXG_amr AXG_am6c AXG_am6d.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngRepr OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngImage OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWk OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGeoX OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngLt OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngSurgery OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngExc OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfPre OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfC OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfS OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngCtx2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap.MngMWP OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngShift OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am3 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am4 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am5 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am6 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am7 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am6b OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_amr0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_amr OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am6c OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am6d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition s_bng (s : astate) : astate :=
  set_brk (BrkCur (length (st_regions s)) 2) (set_avail_meta_areas (SP (length (st_regions s)) PGSZ) (set_avail_meta_area_count 1
    (set_regions (st_regions s ++ [mkRegion RkBrk (2 * PGSZ) [] true]) s))).

Lemma alloc_meta_bn : forall s, st_init_done s = true -> st_free_meta_head s = None -> st_avail_meta_count s = 0 ->
  st_avail_meta_area_count s = 0 -> st_brk s = BrkNever ->
  exists Kq Kg Kd K1 K2, alloc_meta s = IAsk KBrkQuery s Kq /\ Kq 1 = IAsk (KBrkGrow 2) s Kg /\
    Kg 1 = IAsk KGuard (s_bng s) Kd /\
    Kd 1 = IRet (Some (padd (SP (length (st_regions s)) PGSZ) AREA_HDR), s_opn (SP (length (st_regions s)) PGSZ) (s_bng s)) /\
    Kg 0 = IAsk (KMmapNone (Z.shiftl 2 (st_meta_alloc_shift s) * PGSZ)) (set_brk BrkDead s) K1 /\
    K1 1 = IAsk (KMprotect (SP (length (st_regions s)) PGSZ)) (s_resv (set_brk BrkDead s)) K2 /\
    K2 1 = IRet (Some (padd (SP (length (st_regions s)) PGSZ) AREA_HDR),
                 s_opn (SP (length (st_regions s)) PGSZ) (s_res1 (s_resv (set_brk BrkDead s)) (length (st_regions s)) (rg_resv (set_brk BrkDead s)) PGSZ)).
Proof.
  intros s Hi Hf Hc Hac Hb. do 5 eexists. split; [|split; [|split; [|split; [|split; [|split]]]]].
  - unfold alloc_meta. cbn. rewrite set_init_done_same by exact Hi. rewrite Hf. cbn. rewrite Hc. cbn.
    unfold area_from_brk. cbn. rewrite Hac, Hb. cbn. reflexivity.
  - cbn. reflexivity.
  - cbn. unfold new_region. cbn. reflexivity.
  - cbn. unfold area_from_mmap. cbn. unfold ret, s_opn, s_take, open_st, s_bng. cbn. reflexivity.
  - cbn. unfold area_from_mmap. cbn. rewrite Hac. cbn. reflexivity.
  - cbn. reflexivity.
  - cbn. unfold s_resv, rg_resv. cbn. rewrite nth_middle.
    unfold ret, s_opn, s_take, open_st, s_res1, rw_page. cbn. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma region_of_bng : forall s k, region_of (s_bng s) k =
  if Nat.eqb k (length (st_regions s)) then Some (mkRegion RkBrk (2 * PGSZ) [] true) else region_of s k.
Proof.
  intros s k. unfold s_bng, region_of. cbn [st_regions set_brk set_avail_meta_areas set_avail_meta_area_count set_regions].
  destruct (Nat.eqb k (length (st_regions s))) eqn:E.
  - apply Nat.eqb_eq in E. subst k. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
  - apply Nat.eqb_neq in E. destruct (Nat.lt_ge_cases k (length (st_regions s))) as [Hl|Hl].
    + rewrite nth_error_app1 by exact Hl. reflexivity.
    + rewrite nth_error_app2 by exact Hl. rewrite (proj2 (nth_error_None (st_regions s) k)) by exact Hl.
      destruct (k - length (st_regions s))%nat as [|k'] eqn:Ek; [lia|]. cbn. destruct k'; reflexivity.
Qed.

Lemma RMONO_bng : forall s, RMONO s (s_bng s).
Proof.
  intros s. split.
  - unfold s_bng. cbn [st_regions set_brk set_avail_meta_areas set_avail_meta_area_count set_regions]. rewrite length_app. cbn. lia.
  - intros k rgk Hrk Hl. rewrite (region_of_bng s k). replace (Nat.eqb k (length (st_regions s))) with false
      by (symmetry; apply Nat.eqb_neq; pose proof (region_of_lt _ _ _ Hrk); lia).
    exists rgk. split; [exact Hrk|]. split; [exact Hl|]. split; [reflexivity | lia].
Qed.

Lemma bng_cov_ctx : forall s c, In c (ctx_cells (s_bng s)) ->
  In c (ctx_cells s) \/ c = brk_cell (VP (SP (length (st_regions s)) (PGSZ * 2))) \/ c = ac_cell 1 \/ c = ama_cell (SP (length (st_regions s)) PGSZ).
Proof.
  intros s c Hc. unfold s_bng, ctx_cells in Hc.
  cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count
      st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_seq st_brk st_active st_usage
      st_unmap_seq st_bounces set_brk set_avail_meta_areas set_avail_meta_area_count set_regions] in Hc.
  rewrite andb_false_r in Hc.
  apply in_app_iff in Hc as [Hc|Hc]; [|left; unfold ctx_cells; apply in_app_iff; right; exact Hc].
  cbn [In] in Hc.
  repeat (destruct Hc as [<-|Hc]; [first [ (left; unfold ctx_cells; apply in_app_iff; left; cbn [In]; solve [memb])
                                        | (right; left; reflexivity) | (right; right; left; reflexivity) | (right; right; right; reflexivity) ] |]).
  destruct Hc.
Qed.

Lemma bng_rev_ctx : forall s c, In c (ctx_cells s) ->
  In c (ctx_cells (s_bng s)) \/ ((mc_loc c = LCtx CTX_brk \/ mc_loc c = LCtx CTX_avail_meta_area_count \/
     mc_loc c = LCtx CTX_avail_meta_areas) /\ mc_w c = 8%nat).
Proof.
  intros s c Hc. unfold ctx_cells in Hc.
  apply in_app_iff in Hc as [Hc|Hc]; [|left; unfold ctx_cells; apply in_app_iff; right; exact Hc].
  cbn [In] in Hc.
  repeat (destruct Hc as [<-|Hc]; [first [ (left; unfold ctx_cells, s_bng; apply in_app_iff; left;
       cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count
            st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_seq st_brk
            set_brk set_avail_meta_areas set_avail_meta_area_count set_regions In]; rewrite ?andb_false_r; solve [memb])
     | (right; split; [cbn [mc_loc]; first [ (left; reflexivity) | (right; left; reflexivity) | (right; right; reflexivity) ] | reflexivity]) ] |]).
  destruct Hc.
Qed.

Lemma bng_areas_cells : forall s l, areas_cells (s_bng s) l = areas_cells s l.
Proof. intros. apply areas_cells_ext. intros q. reflexivity. Qed.

Lemma bng_cov : forall s c, In c (image (s_bng s)) ->
  In c (image s) \/ c = brk_cell (VP (SP (length (st_regions s)) (PGSZ * 2))) \/ c = ac_cell 1 \/ c = ama_cell (SP (length (st_regions s)) PGSZ).
Proof.
  intros s c Hc. unfold image in Hc. apply in_app_iff in Hc as [Hc|Hc].
  - destruct (bng_cov_ctx s c Hc) as [H|H]; [left; apply ctx_in_image; exact H | right; exact H].
  - left. unfold image. apply in_app_iff. right. replace (st_areas (s_bng s)) with (st_areas s) in Hc by reflexivity.
    rewrite bng_areas_cells in Hc. exact Hc.
Qed.

Lemma bng_rev : forall s c, In c (image s) ->
  In c (image (s_bng s)) \/ ((mc_loc c = LCtx CTX_brk \/ mc_loc c = LCtx CTX_avail_meta_area_count \/
     mc_loc c = LCtx CTX_avail_meta_areas) /\ mc_w c = 8%nat).
Proof.
  intros s c Hc. unfold image in Hc. apply in_app_iff in Hc as [Hc|Hc].
  - destruct (bng_rev_ctx s c Hc) as [H|H]; [left; apply ctx_in_image; exact H | right; exact H].
  - left. unfold image. apply in_app_iff. right. replace (st_areas (s_bng s)) with (st_areas s) by reflexivity.
    rewrite bng_areas_cells. exact Hc.
Qed.

Lemma bng_cells_in : forall s,
  In (brk_cell (VP (SP (length (st_regions s)) (PGSZ * 2)))) (image (s_bng s)) /\ In (ac_cell 1) (image (s_bng s)) /\
  In (ama_cell (SP (length (st_regions s)) PGSZ)) (image (s_bng s)).
Proof.
  intros s. split; [|split]; apply ctx_in_image; unfold ctx_cells, s_bng; apply in_app_iff; left;
    cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count
         st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_seq st_brk
         set_brk set_avail_meta_areas set_avail_meta_area_count set_regions In]; rewrite ?andb_false_r; solve [memb].
Qed.

Lemma bng_ctx_loc : forall s c o, In c (image (s_bng s)) -> mc_loc c = LCtx o ->
  (o = CTX_brk -> c = brk_cell (VP (SP (length (st_regions s)) (PGSZ * 2)))) /\ (o = CTX_avail_meta_area_count -> c = ac_cell 1).
Proof.
  intros s c o Hc Hl. pose proof (lctx_in_ctx _ c o Hc Hl) as Hx. clear Hc.
  unfold ctx_cells, s_bng in Hx.
  cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count
       st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_seq st_brk st_active st_usage
       st_unmap_seq st_bounces set_brk set_avail_meta_areas set_avail_meta_area_count set_regions] in Hx.
  rewrite andb_false_r in Hx.
  apply in_app_iff in Hx as [Hx|Hx].
  - cbn [In] in Hx.
    repeat (destruct Hx as [<-|Hx]; [cbn [mc_loc] in Hl; injection Hl as <-; unfold CTX_brk, CTX_avail_meta_area_count;
             split; intros E; first [reflexivity | (unfold CTX_secret, CTX_init_done, CTX_mmap_counter, CTX_free_meta_head, CTX_avail_meta,
               CTX_avail_meta_count, CTX_meta_alloc_shift, CTX_meta_area_head, CTX_meta_area_tail, CTX_avail_meta_areas, CTX_seq, CTX_brk in E; lia)] |]).
    destruct Hx.
  - repeat (apply in_app_iff in Hx as [Hx|Hx]); apply in_map_iff in Hx as (k & <- & Hk); apply in_seq in Hk; cbn [mc_loc] in Hl; injection Hl as <-.
    all: split; intros E; unfold CTX_active, CTX_usage, CTX_unmap_seq, CTX_bounces, CTX_brk, CTX_avail_meta_area_count in *; lia.
Qed.

Lemma bng_footprint : forall s f, In f (footprint (s_bng s)) -> In f (footprint s).
Proof.
  intros s f H. unfold footprint in *. destruct H as [H|H]; [left; exact H|]. right.
  apply in_app_iff in H as [H|H]; [apply in_app_iff; left; exact H|]. apply in_app_iff. right.
  apply in_flat_map in H as (k & Hk & Hin). apply in_flat_map. exists k.
  destruct (region_of (s_bng s) k) as [rgk|] eqn:E; [|destruct Hin].
  rewrite (region_of_bng s k) in E. destruct (Nat.eqb k (length (st_regions s))) eqn:Ek.
  - injection E as <-. cbn in Hin. destruct Hin.
  - apply Nat.eqb_neq in Ek. split; [|rewrite E; exact Hin].
    apply in_seq in Hk. apply in_seq. replace (length (st_regions (s_bng s))) with (S (length (st_regions s))) in Hk
      by (unfold s_bng; cbn [st_regions set_brk set_avail_meta_areas set_avail_meta_area_count set_regions]; rewrite length_app; cbn; lia).
    lia.
Qed.

(* [comment removed for export] *)
Lemma rgeoA_bng : forall HTOP L s b, rgeoA HTOP L s ->
  PGSZ <= b -> b mod PGSZ = 0 -> b + 2 * PGSZ <= HTOP -> ranges_disjoint (b, 2 * PGSZ) (0x10000, 0x87000) ->
  rgeoA HTOP (set_reg_addr L (length (st_regions s)) b) (s_bng s).
Proof.
  intros HTOP L s b HG H1 H2 H3 H4 k rgk Hk Hlk. rewrite (region_of_bng s k) in Hk. unfold set_reg_addr. cbn [ly_reg].
  destruct (Nat.eqb k (length (st_regions s))) eqn:E.
  - injection Hk as <-. cbn [rg_len]. auto.
  - exact (HG k rgk Hk Hlk).
Qed.

Lemma rdisj_bng : forall L s b, rdisj L s ->
  (forall k rgk, region_of s k = Some rgk -> rg_live rgk = true -> ranges_disjoint (b, 2 * PGSZ) (ly_reg L k, rg_len rgk)) ->
  rdisj (set_reg_addr L (length (st_regions s)) b) (s_bng s).
Proof.
  intros L s b HD FR7 r1 r2 rg1 rg2 Hne H1 H2 L1 L2. rewrite (region_of_bng s r1) in H1. rewrite (region_of_bng s r2) in H2.
  unfold set_reg_addr. cbn [ly_reg].
  destruct (Nat.eqb r1 (length (st_regions s))) eqn:E1; destruct (Nat.eqb r2 (length (st_regions s))) eqn:E2.
  - apply Nat.eqb_eq in E1, E2. congruence.
  - injection H1 as <-. cbn [rg_len]. exact (FR7 r2 rg2 H2 L2).
  - injection H2 as <-. cbn [rg_len]. pose proof (FR7 r1 rg1 H1 L1) as D. clear - D. unfold ranges_disjoint in *. cbn [fst snd] in *. lia.
  - exact (HD r1 r2 rg1 rg2 Hne H1 H2 L1 L2).
Qed.

(* [comment removed for export] *)
Lemma wbytes_twice8 : forall (m : word -> option byte) a v1 v2 x, 0 <= a -> a + 8 <= 2^64 -> 0 <= x < 2^64 ->
  wbytes (wbytes m (wa a) (word_to_le_bytes 8 (wa v1))) (wa a) (word_to_le_bytes 8 (wa v2)) (wa x) =
  wbytes m (wa a) (word_to_le_bytes 8 (wa v2)) (wa x).
Proof.
  intros m a v1 v2 x H0 H1 Hx. destruct (Z_lt_le_dec x a) as [D|D]; [rewrite !MngWb.wbytes_out by side; reflexivity|].
  destruct (Z_lt_le_dec x (a + 8)) as [D2|D2]; [|rewrite !MngWb.wbytes_out by side; reflexivity].
  replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia.
  rewrite !(MngWb.wbytes_at_wa) by (first [lia | (cbn [length word_to_le_bytes Z_to_le_bytes]; lia) | (cbn [length word_to_le_bytes Z_to_le_bytes]; lia)]).
  reflexivity.
Qed.

Lemma GROW_ext : forall sp0 K L s m L' s' m1 m2, GROW sp0 K L s m L' s' m1 -> (forall x, 0 <= x < 2^64 -> m2 (wa x) = m1 (wa x)) ->
  GROW sp0 K L s m L' s' m2.
Proof.
  intros sp0 K L s m L' s' m1 m2 (E & RM & IM & SI1 & CH) HE. split; [exact E|]. split; [exact RM|]. split; [exact IM|]. split.
  - intros x Hx Hnc. rewrite (HE x ltac:(lia)). exact (SI1 x Hx Hnc).
  - intros x Hx Hne. rewrite (HE x Hx) in Hne. exact (CH x Hx Hne).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section BNG.
Variables (HTOP : Z) (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (L : layout) (s : astate).
Variables (m m5 : word -> option byte) (sp0 K b : Z).
Let L' := set_reg_addr L (length (st_regions s)) b.
Hypothesis C : CUT HTOP X R U L' s m sp0 K.
Hypothesis Hb : st_brk s = BrkNever.
Hypothesis HFP : forall f, In f (footprint s) -> ranges_disjoint (b, 2 * PGSZ) (crange L' f).
Hypothesis HIMG : b + 8192 <= 0x10000 \/ 0x97000 <= b.
Hypothesis Hb0 : 0 <= b.
Hypothesis Hbt : b + 8192 <= HTOP.
Hypothesis HOUT : forall x, 0 <= x < 2^64 -> ~ (b <= x < b + 8192) -> ~ (sp0 - K <= x < sp0) -> ~ (615024 <= x < 615032) -> m5 (wa x) = m (wa x).
Hypothesis HSTK : stk_ok SEGS (bcg_mem m5 (b + 8192)) (wa sp0) K.

#[using="HOUT"] Lemma bng_mout : forall x, 0 <= x < 2^64 -> ~ (615024 <= x < 615032) -> ~ (614144 <= x < 614152) -> ~ (b <= x < b + 8192) ->
  ~ (sp0 - K <= x < sp0) -> bcg_mem m5 (b + 8192) (wa x) = m (wa x).
Proof. LiaFast.lf_pins (fun (HOUT : LiaFast.U) => LiaFast.u0).
  intros x Hx H1 H2 H3 H4. unfold bcg_mem. rewrite !MngWb.wbytes_out by side. exact (HOUT x Hx H3 H4 H1).
Qed.

#[using="X R U m C Hb HFP HIMG HOUT HSTK"] Theorem pcut_bng : PCUT HTOP L' OEXC (s_bng s) (bcg_mem m5 (b + 8192)) sp0 K.
Proof. LiaFast.lf_pins (fun (X R U m C Hb HFP HIMG HOUT HSTK : LiaFast.U) => LiaFast.u0).
  pose proof C as [HI HX N HG HD HT HTB].
  pose proof N as [HR HEX HZU HK' Hctx Henv HSTK0 HK1 Hsp1 Hsp2 Hsp3 HCe HMP HMD].
  pose proof (PCUT_of_CUT HTOP X R U L' s m sp0 K C) as P0.
  pose proof (layout_of_geo HTOP HTB X R U s L' HI Hctx HG HD) as HL.
  pose proof (image_cells_disjoint_X X R U s L' HI (XNU_of_XNM X s HX) HL) as HPW.
  set (cb := MCell (LCtx CTX_brk) 8 (VZ 0)).
  set (ca := MCell (LCtx CTX_avail_meta_area_count) 8 (VZ (st_avail_meta_area_count s))).
  assert (Icb : In cb (image s)).
  { apply ctx_in_image. unfold ctx_cells. apply in_app_iff. left. rewrite Hb. cbn [In]. unfold cb. memb. }
  assert (Ica : In ca (image s)) by (apply ctx_in_image; unfold ca; in_ctx13).
  assert (Rcb : cell_range L' cb = (615024, 8)) by (unfold cb, cell_range; cbn [mc_loc mc_w loc_addr]; rewrite Hctx; reflexivity).
  assert (Rca : cell_range L' ca = (614144, 8)) by (unfold ca, cell_range; cbn [mc_loc mc_w loc_addr]; rewrite Hctx; reflexivity).
  assert (KEEP : forall c, In c (image s) -> mc_loc c <> LCtx CTX_brk -> mc_loc c <> LCtx CTX_avail_meta_area_count ->
                   cell_holds L' (bview SEGS (bcg_mem m5 (b + 8192))) c).
  { intros c Hc N1 N2. pose proof (pc_cells _ _ _ _ _ _ _ P0 c Hc ltac:(intros [])) as H0.
    assert (Dcb : ranges_disjoint (cell_range L' c) (cell_range L' cb) \/ ranges_disjoint (cell_range L' cb) (cell_range L' c)).
    { apply (pairwise_map_In _ (cell_range L') _ _ _ HPW Hc Icb). intros E. apply N1. rewrite E. reflexivity. }
    assert (Dca : ranges_disjoint (cell_range L' c) (cell_range L' ca) \/ ranges_disjoint (cell_range L' ca) (cell_range L' c)).
    { apply (pairwise_map_In _ (cell_range L') _ _ _ HPW Hc Ica). intros E. apply N2. rewrite E. reflexivity. }
    rewrite Rcb in Dcb. rewrite Rca in Dca.
    destruct (image_in_footprint_X X R U s L' c HI (XNU_of_XNM X s HX) HL Hc) as (f & Hf & Hincl).
    pose proof (HFP f Hf) as Df.
    pose proof (cells_below HTOP X R U s L' (sp0 - K) HTB HI HX HG HD Hctx HT ltac:(lia) c Hc) as Bc.
    apply (cell_holds_frame L' (bview SEGS m) (bview SEGS (bcg_mem m5 (b + 8192))) c (image_cell_width s c Hc) H0).
    intros a Ha.
    destruct (Z_lt_le_dec a 0) as [Ha0|Ha0]; [unfold bview; replace ((0 <=? a) && (a <? 2^64)) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia); reflexivity|].
    destruct (Z_lt_le_dec a (2^64)) as [Ha1|Ha1]; [|unfold bview; replace ((0 <=? a) && (a <? 2^64)) with false by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia); reflexivity].
    apply MngWb.bview_ext. apply bng_mout; [lia | | | |].
    - clear - Dcb Ha. unfold ranges_disjoint, in_rng in *. destruct (cell_range L' c) as [lo n]. cbn [fst snd] in *. lia.
    - clear - Dca Ha. unfold ranges_disjoint, in_rng in *. destruct (cell_range L' c) as [lo n]. cbn [fst snd] in *. lia.
    - clear - Df Hincl Ha. unfold ranges_disjoint, range_incl, in_rng in *. destruct (cell_range L' c) as [lo n]. destruct (crange L' f) as [lo' n'].
      cbn [fst snd] in *. unfold PGSZ in *. lia.
    - clear - Bc Ha. unfold in_rng, cell_range in Ha. cbn [fst snd] in Ha. lia. }
  assert (EL' : ly_reg L' (length (st_regions s)) = b) by (unfold L', set_reg_addr; cbn [ly_reg]; rewrite Nat.eqb_refl; reflexivity).
  constructor.
  - intros c Hc Hne.
    assert (CASE : c = brk_cell (VP (SP (length (st_regions s)) (PGSZ * 2))) \/ c = ac_cell 1 \/
                   (In c (image s) /\ mc_loc c <> LCtx CTX_brk /\ mc_loc c <> LCtx CTX_avail_meta_area_count)).
    { destruct (bng_cov s c Hc) as [Ho | [E | [E | E]]].
      - destruct (loc_eq_dec (mc_loc c) (LCtx CTX_brk)) as [El|El]; [left; exact (proj1 (bng_ctx_loc s c CTX_brk Hc El) eq_refl)|].
        destruct (loc_eq_dec (mc_loc c) (LCtx CTX_avail_meta_area_count)) as [El2|El2];
          [right; left; exact (proj2 (bng_ctx_loc s c CTX_avail_meta_area_count Hc El2) eq_refl)|].
        right; right. auto.
      - left; exact E.
      - right; left; exact E.
      - exfalso. apply Hne. rewrite E. cbn [ama_cell mc_loc]. unfold OEXC. cbn [In]. right; right; left; reflexivity. }
    destruct CASE as [-> | [-> | (Ho & N1 & N2)]].
    + assert (H1 : cell_holds L' (bview SEGS (wbytes m5 (wa (0 + 615024)) (word_to_le_bytes 8 (wa (b + 8192))))) (brk_cell (VP (SP (length (st_regions s)) (PGSZ * 2))))).
      { replace (wa (0 + 615024)) with (wa (loc_addr L' (mc_loc (brk_cell (VP (SP (length (st_regions s)) (PGSZ * 2))))))) by (cbn [mc_loc brk_cell loc_addr]; rewrite Hctx; reflexivity).
        change 8%nat with (mc_w (brk_cell (VP (SP (length (st_regions s)) (PGSZ * 2))))).
        apply holds_wb; cbn [mc_val mc_w mc_loc brk_cell loc_addr sval_num]; rewrite ?Hctx; unfold CTX_brk;
          first [ (intros z E; discriminate E) | (rewrite EL'; unfold PGSZ; f_equal; ring) | lia ]. }
      apply (cell_holds_frame L' _ _ (brk_cell (VP (SP (length (st_regions s)) (PGSZ * 2)))) ltac:(cbn; lia) H1).
      intros a Ha. unfold in_rng, cell_range in Ha. cbn [fst snd mc_loc mc_w brk_cell loc_addr] in Ha.
      rewrite Hctx in Ha. unfold CTX_brk in Ha. unfold bcg_mem. apply MngWb.bview_ext. rewrite MngWb.wbytes_out by side. reflexivity.
    + unfold bcg_mem.
      replace (wa (0 + 614144)) with (wa (loc_addr L' (mc_loc (ac_cell 1)))) by (cbn [mc_loc ac_cell loc_addr]; rewrite Hctx; reflexivity).
      change 8%nat with (mc_w (ac_cell 1)).
      apply holds_wb; cbn [mc_val mc_w mc_loc ac_cell loc_addr sval_num]; rewrite ?Hctx; unfold CTX_avail_meta_area_count;
        first [ (intros z E; discriminate E) | lia | reflexivity ].
    + exact (KEEP c Ho N1 N2).
  - apply Forall_forall. intros f Hf x Hx. pose proof (bng_footprint s f Hf) as Hf0.
    pose proof (proj1 (Forall_forall _ _) (pc_fp _ _ _ _ _ _ _ P0) f Hf0 x Hx) as H0.
    pose proof (HFP f Hf0) as Df. pose proof (fp_below HTOP X R U s L' (sp0 - K) HI HG Hctx HT ltac:(lia) f Hf0) as Bf.
    assert (Rx : 0 <= x < 2^64).
    { destruct (Z_lt_le_dec x 0) as [D|D]; [unfold bview in H0; replace ((0 <=? x) && (x <? 2^64)) with false in H0 by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia); exfalso; exact (H0 eq_refl)|].
      destruct (Z_lt_le_dec x (2^64)) as [D2|D2]; [lia|]. unfold bview in H0; replace ((0 <=? x) && (x <? 2^64)) with false in H0 by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia). exfalso; exact (H0 eq_refl). }
    destruct (decide (614144 <= x < 614152)) as [D1|D1].
    { replace x with (614144 + Z.of_nat (Z.to_nat (x - 614144))) by lia. set (k := Z.to_nat (x - 614144)).
      assert (Hk : (k < 8)%nat) by (unfold k; lia).
      assert (E : bcg_mem m5 (b + 8192) (wa (614144 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa 1)) (Z_to_bv 8 0)))
        by (unfold bcg_mem; apply MngWb.wbytes_at_wa; cbn [length word_to_le_bytes Z_to_le_bytes]; lia).
      rewrite (MngWb.bview_some_byte SEGS _ (614144 + Z.of_nat k) _ ltac:(lia) E). discriminate. }
    destruct (decide (615024 <= x < 615032)) as [D2|D2].
    { replace x with (615024 + Z.of_nat (Z.to_nat (x - 615024))) by lia. set (k := Z.to_nat (x - 615024)).
      assert (Hk : (k < 8)%nat) by (unfold k; lia).
      assert (E : bcg_mem m5 (b + 8192) (wa (615024 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa (b + 8192))) (Z_to_bv 8 0))).
      { unfold bcg_mem. rewrite MngWb.wbytes_out by (first [side | lia]). apply MngWb.wbytes_at_wa; cbn [length word_to_le_bytes Z_to_le_bytes]; lia. }
      rewrite (MngWb.bview_some_byte SEGS _ (615024 + Z.of_nat k) _ ltac:(lia) E). discriminate. }
    rewrite (MngWb.bview_ext SEGS m (bcg_mem m5 (b + 8192)) x); [exact H0|]. apply bng_mout; [exact Rx | exact D2 | exact D1 | |].
    + clear - Df Hx. unfold ranges_disjoint, crange, in_rng in *. cbn [fst snd] in *. unfold PGSZ in *. lia.
    + clear - Bf Hx. unfold crange, in_rng in *. cbn [fst snd] in *. lia.
  - exact Hctx.
  - destruct Henv as (E1 & E2 & can & Rc & E3). split; [|split].
    + rewrite (rdn_frame_n m (bcg_mem m5 (b + 8192)) 408992 8) by (try lia; intros x Hx; cbn in Hx; apply bng_mout; clear - Hx HIMG Hsp1 HK1 HT Hbt; unfold PGSZ in *; lia). exact E1.
    + intros sc Hsc. rewrite (rdn_frame_n m (bcg_mem m5 (b + 8192)) (98984 + 2 * sc) 2) by (try lia; intros x Hx; cbn in Hx; apply bng_mout; clear - Hx Hsc HIMG Hsp1 HK1 HT Hbt; unfold PGSZ in *; lia).
      exact (E2 sc Hsc).
    + exists can. split; [exact Rc|]. rewrite (rdn_frame_n m (bcg_mem m5 (b + 8192)) 613952 8) by (try lia; intros x Hx; cbn in Hx; apply bng_mout; clear - Hx HIMG Hsp1 HK1 HT Hbt; unfold PGSZ in *; lia). exact E3.
  - exact HSTK.
  - exact HK1.
  - exact Hsp1.
  - exact Hsp2.
  - exact Hsp3.
  - exact HT.
  - exact HTB.
Qed.
#[using="HTOP X R U C HIMG HOUT"] Theorem grow_bng : GROW sp0 K L s m L' (s_bng s) (bcg_mem m5 (b + 8192)).
Proof. LiaFast.lf_pins (fun (HTOP X R U C HIMG HOUT : LiaFast.U) => LiaFast.u0).
  pose proof C as [HI HX N HG HD HT HTB].
  pose proof (nc_ctx _ _ _ _ _ _ _ N) as Hctx. pose proof (nc_sp1 _ _ _ _ _ _ _ N) as Hsp1. pose proof (nc_K _ _ _ _ _ _ _ N) as HK1.
  assert (Hctx0 : ly_ctx L = 0x95ed8) by exact Hctx.
  pose proof (bng_cells_in s) as (I1 & I2 & I3).
  assert (EL' : ly_reg L' (length (st_regions s)) = b) by (unfold L', set_reg_addr; cbn [ly_reg]; rewrite Nat.eqb_refl; reflexivity).
  split; [apply lext_set_new|]. split; [exact (RMONO_bng s)|].
  split.
  { intros c Hc. destruct (bng_rev s c Hc) as [H|(El & Ew)].
    - exists c. split; [exact H|]. exact (cell_range_ext X R U s L L' HI HX (lext_set_new L s b) c Hc).
    - destruct El as [El|[El|El]].
      + exists (brk_cell (VP (SP (length (st_regions s)) (PGSZ * 2)))). split; [exact I1|]. unfold cell_range. rewrite El, Ew. reflexivity.
      + exists (ac_cell 1). split; [exact I2|]. unfold cell_range. rewrite El, Ew. reflexivity.
      + exists (ama_cell (SP (length (st_regions s)) PGSZ)). split; [exact I3|]. unfold cell_range. rewrite El, Ew. reflexivity. }
  split.
  { intros x Hx Hnc. apply bng_mout; clear - Hx Hnc HIMG Hsp1 HK1; unfold PGSZ in *; lia. }
  intros x Hx Hne.
  destruct (decide (sp0 - K <= x < sp0)) as [D0|D0]; [left; exact D0|].
  destruct (decide (615024 <= x < 615032)) as [D1|D1].
  { right. left. exists (brk_cell (VP (SP (length (st_regions s)) (PGSZ * 2)))). split; [exact I1|]. unfold in_rng, cell_range. cbn [fst snd mc_loc mc_w brk_cell loc_addr].
    unfold L', set_reg_addr. cbn [ly_ctx]. rewrite Hctx0. unfold CTX_brk. cbn [Z.of_nat Pos.of_succ_nat]. lia. }
  destruct (decide (614144 <= x < 614152)) as [D2|D2].
  { right. left. exists (ac_cell 1). split; [exact I2|]. unfold in_rng, cell_range. cbn [fst snd mc_loc mc_w ac_cell loc_addr].
    unfold L', set_reg_addr. cbn [ly_ctx]. rewrite Hctx0. unfold CTX_avail_meta_area_count. cbn [Z.of_nat Pos.of_succ_nat]. lia. }
  destruct (decide (b <= x < b + 8192)) as [D3|D3].
  { right. right. left. exists (length (st_regions s)), (mkRegion RkBrk (2 * PGSZ) [] true).
    split; [rewrite (region_of_bng s), Nat.eqb_refl; reflexivity|]. cbn [rg_live rg_len]. split; [reflexivity|]. split; [lia|].
    rewrite EL'. unfold PGSZ. lia. }
  exfalso. apply Hne. exact (bng_mout x Hx D1 D2 D3 D0).
Qed.
End BNG.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ecall_51a44 : exists w, fetch_word SEGS (wa 0x51dec) = Some w /\ is_ecall w = true.
Proof. eexists. split; [vm_compute; reflexivity | vm_compute; reflexivity]. Qed.
Lemma add4_51a44 : bv_add (wa 0x51dec) (w64 4) = wa 0x51df0.
Proof. apply bv_eq. reflexivity. Qed.
Lemma ecall_51a68 : exists w, fetch_word SEGS (wa 0x51e10) = Some w /\ is_ecall w = true.
Proof. eexists. split; [vm_compute; reflexivity | vm_compute; reflexivity]. Qed.
Lemma add4_51a68 : bv_add (wa 0x51e10) (w64 4) = wa 0x51e14.
Proof. apply bv_eq. reflexivity. Qed.

Lemma kout_brk_query : forall FORB HTOP L s eff ans L', koutcome FORB HTOP L s KBrkQuery eff ans L' ->
  eff = mkEffect (w64 (ly_brk0 L)) [] [] /\ ans = 1 /\ L' = L.
Proof. intros FORB HTOP L s eff ans L' H. inversion H; subst. auto. Qed.

Lemma kout_guard : forall FORB HTOP L s eff ans L', koutcome FORB HTOP L s KGuard eff ans L' ->
  eff = mkEffectU (w64 (brk_base L s)) [] [] [(w64 (brk_base L s), w64 PGSZ)] [] [] /\ ans = 1 /\ L' = L.
Proof. intros FORB HTOP L s eff ans L' H. inversion H; subst. auto. Qed.

Lemma mmap_saves_frame : forall m m' spc ra v8 v9 v18 v19 v20 v21, mmap_saves m spc ra v8 v9 v18 v19 v20 v21 -> 56 <= spc <= 2^47 ->
  (forall x, spc - 56 <= x < spc -> m' (wa x) = m (wa x)) -> mmap_saves m' spc ra v8 v9 v18 v19 v20 v21.
Proof.
  intros m m' spc ra v8 v9 v18 v19 v20 v21 (S1 & S2 & S3 & S4 & S5 & S6 & S7) Hs HF.
  repeat split; (rewrite (rdn_frame_n m m') by (first [(intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; apply HF; lia) | lia])); assumption.
Qed.

Ltac regne := intros E; apply (f_equal bv_unsigned) in E; cbv in E; discriminate E.

Section WKN.
Context {fx : FPState}.
Variable FORB : list (Z * Z).
Hypothesis HFORB : forall a n, 0 < n -> Forall (fun r => ranges_disjoint (a, n) r) FORB -> ranges_disjoint (a, n) (0x10000, 0x87000).
Hypothesis WOR : forall HTOP X R U L0 s0 m0 (regs0 : bvmap 5 word) L s m Rg rom sp0 K can ra r o rg
    (Kt : Z -> itree astate (option sptr * astate)),
  CUT HTOP X R U L s m sp0 K -> GROW sp0 K L0 s0 m0 L s m -> 1152 <= K ->
  am_frame Rg m sp0 can ra (bv_unsigned (getr regs0 8)) (bv_unsigned (getr regs0 9))
    (bv_unsigned (getr regs0 18)) (bv_unsigned (getr regs0 19)) (bv_unsigned (getr regs0 20)) ->
  getr regs0 1 = wa ra -> getr regs0 2 = wa sp0 -> (ra = 0x524e8 \/ ra = 0x5210c) ->
  (forall k, In k [3;4;21;22;23;24;25;26;27]%nat -> getr Rg (Z_to_bv 5 (Z.of_nat k)) = getr regs0 (Z_to_bv 5 (Z.of_nat k))) ->
  getr Rg 1 = wa 335712 -> getr Rg 9 = wa (ly_reg L r + o) -> getr Rg 10 = wa (ly_reg L r + o) ->
  getr Rg 11 = wa 4096 -> getr Rg 12 = wa 3 ->
  st_init_done s = true -> st_free_meta_head s = None -> st_avail_meta_count s = 0 -> 0 < st_avail_meta_area_count s ->
  st_avail_meta_areas s = SP r o -> region_of s r = Some rg ->
  rdn SEGS m (wa 614032) 8 = Some (word_to_le_bytes 8 (wa 4096)) ->
  Kt 1 = IRet (Some (padd (SP r o) AREA_HDR), s_opn (SP r o) (s_res1 s r rg o)) ->
  wk SEGS FORB HTOP rom L Rg (wa 0x53414) m (IAsk (KMprotect (SP r o)) s Kt)
     (am_qpost HTOP X R U L0 s0 m0 regs0 sp0 K ra).

#[using="HFORB WOR"] Theorem wk_bn_tail : forall HTOP X R U L0 s0 m0 (regs : bvmap 5 word) L s m1 Rq rom sp0 K can ra,
  CUT HTOP X R U L s m1 sp0 K -> GROW sp0 K L0 s0 m0 L s m1 -> 1152 <= K ->
  am_frame Rq m1 sp0 can ra (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
    (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 20)) ->
  getr regs 1 = wa ra -> getr regs 2 = wa sp0 -> (ra = 0x524e8 \/ ra = 0x5210c) ->
  getr Rq 8 = wa 4096 ->
  (forall k, In k [3;4;21;22;23;24;25;26;27]%nat -> getr Rq (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) ->
  rdn SEGS m1 (wa 614032) 8 = Some (word_to_le_bytes 8 (wa 4096)) ->
  PGSZ <= ly_brk0 L -> ly_brk0 L mod PGSZ = 0 -> ly_brk0 L <= HTOP ->
  st_init_done s = true -> st_free_meta_head s = None -> st_avail_meta_count s = 0 -> st_avail_meta_area_count s = 0 ->
  st_brk s = BrkNever ->
  wk SEGS FORB HTOP rom L Rq (wa 0x51db0) m1 (alloc_meta s) (am_qpost HTOP X R U L0 s0 m0 regs sp0 K ra).
Proof. LiaFast.lf_pins (fun (HFORB WOR : LiaFast.U) => LiaFast.u0).
  intros HTOP X R U L0 s0 m0 regs L s m1 Rq rom sp0 K can ra C1 GR0 HK Fq R1 R2 Hra Q8 KA0 Mpg1 B1 B2 B3 Hi Hf Hc Hac Hb.
  pose proof C1 as [HI HX N1 HG HD HT HTB].
  pose proof (nc_ctx _ _ _ _ _ _ _ N1) as Hctx. pose proof (nc_sp1 _ _ _ _ _ _ _ N1) as Hsp1. pose proof (nc_sp2 _ _ _ _ _ _ _ N1) as Hsp2.
  pose proof (nc_sp3 _ _ _ _ _ _ _ N1) as Hsp3. pose proof (nc_stk _ _ _ _ _ _ _ N1) as HSTK1.
  destruct (alloc_meta_bn s Hi Hf Hc Hac Hb) as (Kq & Kg & Kd & K1 & K2 & Et & EKq & EKg1 & EKd & EKg0 & EK1 & EK2). rewrite Et.
  change (hide (ra = 0x524e8 \/ ra = 0x5210c)) in Hra.
  set (b := ly_brk0 L) in *.
  assert (Ebk : brk_cur L s = b) by (unfold brk_cur; rewrite Hb; reflexivity).
  unfold PGSZ in B1, B2.
  assert (Mac : rdn SEGS m1 (wa (0 + 614144)) 8 = Some (word_to_le_bytes 8 (wa 0))).
  { pose proof (nc_ctx_rd L s m1 sp0 K (MCell (LCtx CTX_avail_meta_area_count) 8 (VZ (st_avail_meta_area_count s))) N1 ltac:(in_ctx13)
                  ltac:(intros z E; discriminate E) ltac:(cbn; lia)) as H. cbn [mc_loc mc_w mc_val loc_addr sval_num] in H. rewrite Hctx, Hac in H. exact H. }
  assert (Mbk : rdn SEGS m1 (wa (0 + 615024)) 8 = Some (word_to_le_bytes 8 (wa 0))).
  { pose proof (nc_ctx_rd L s m1 sp0 K (MCell (LCtx CTX_brk) 8 (match st_brk s with BrkNever => VZ 0 | BrkDead => VZ (-1) | BrkCur r p => VP (SP r (PGSZ * p)) end))
                  N1 ltac:(in_ctx13) ltac:(rewrite Hb; intros z E; discriminate E) ltac:(cbn; lia)) as H.
    cbn [mc_loc mc_w mc_val loc_addr] in H. rewrite Hctx, Hb in H. cbn [sval_num] in H. exact H. }
  set (av := sval_num L (if (match st_areas s with [] => true | _ => false end) && (st_avail_meta_area_count s =? 0) then VZ 0 else VP (st_avail_meta_areas s))).
  assert (Mar : rdn SEGS m1 (wa (0 + 614176)) 8 = Some (word_to_le_bytes 8 (wa (av mod 2^64)))).
  { pose proof (nc_ctx_rd L s m1 sp0 K (MCell (LCtx CTX_avail_meta_areas) 8
        (if (match st_areas s with [] => true | _ => false end) && (st_avail_meta_area_count s =? 0) then VZ 0 else VP (st_avail_meta_areas s)))
                  N1 ltac:(in_ctx13) ltac:(destruct (_ && _); intros z E; discriminate E) ltac:(cbn; lia)) as H.
    cbn [mc_loc mc_w mc_val loc_addr] in H. rewrite Hctx in H. fold av in H. rewrite (wa_mod64 av) in H. exact H. }
  assert (Msh : rdn SEGS m1 (wa (0 + 614152)) 8 = Some (word_to_le_bytes 8 (wa (st_meta_alloc_shift s)))).
  { pose proof (nc_ctx_rd L s m1 sp0 K (MCell (LCtx CTX_meta_alloc_shift) 8 (VZ (st_meta_alloc_shift s))) N1 ltac:(in_ctx13)
                  ltac:(intros z E; discriminate E) ltac:(cbn; lia)) as H. cbn [mc_loc mc_w mc_val loc_addr sval_num] in H. rewrite Hctx in H. exact H. }
  pose proof (inv_ctx HI) as CT. unfold ctx_ok in CT. destruct CT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Csh & _).
  pose proof (shift_le_34 X R U s HTOP L HI HG HD HTB) as S34.
  assert (Rar : 0 <= av mod 2^64 <= 2^64-1) by (pose proof (Z.mod_pos_bound av (2^64) ltac:(lia)); lia).
  assert (Rsh : 0 <= st_meta_alloc_shift s <= 34) by lia.
  assert (W5 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m1 (wa (0 + 615024 + d)) k = true).
  { intros d k Hd Hk'. pose proof (nc_ctx_wr L s m1 sp0 K (MCell (LCtx CTX_brk) 8 (match st_brk s with BrkNever => VZ 0 | BrkDead => VZ (-1) | BrkCur r p => VP (SP r (PGSZ * p)) end))
      N1 ltac:(in_ctx13) ltac:(destruct (st_brk s); intros z E; discriminate E) d k Hd ltac:(cbn [mc_w]; lia)) as W.
    cbn [mc_loc loc_addr] in W. rewrite Hctx in W. exact W. }
  destruct (seg_bnq Rq m1 rom sp0 can _ _ _ _ _ _ (av mod 2^64) (st_meta_alloc_shift s) Fq Q8 Mac Mbk Rar Mar Rsh Msh)
    as (Rb1 & Hms3 & A17 & A10 & A11 & A8 & A19 & Ka1).
  (* [comment removed for export] *)
  cbn [wk]. exists Rb1, (wa 0x51dec), m1. split; [exact Hms3|]. split.
  { split; [exact ecall_51a44|]. exists SYS_brk, [0]. split; [reflexivity|].
    split; [rewrite A17; reflexivity|]. cbn [args_match]. split; [|exact I].
    match type of A10 with getr _ ?r0 = _ => match goal with |- bv_unsigned (getr _ ?r1) = _ =>
      replace r1 with r0 by (apply bv_eq; reflexivity) end end. rewrite A10. reflexivity. }
  intros eff ans L' Ho. destruct (kout_brk_query FORB HTOP L s eff ans L' Ho) as (-> & -> & ->).
  rewrite EKq. cbn [wk]. rewrite add4_51a44. cbn [eff_ret].
  change (mem_after m1 (mkEffect (w64 (ly_brk0 L)) [] [])) with m1. fold b.
  (* [comment removed for export] *)
  set (Rb1' := regupd Rb1 10 (w64 b)).
  assert (P8 : getr Rb1' 8 = wa 4096) by (unfold Rb1'; rewrite getr_other by regne; exact A8).
  assert (P10 : getr Rb1' 10 = wa b) by (unfold Rb1'; rewrite getr_same by regne; reflexivity).
  assert (P11 : getr Rb1' 11 = wa 4095) by (unfold Rb1'; rewrite getr_other by regne; exact A11).
  assert (P19 : getr Rb1' 19 = wa 614096) by (unfold Rb1'; rewrite getr_other by regne; exact A19).
  destruct (seg_bnx Rb1' m1 rom b P8 P10 P11 P19 ltac:(clear - B1 B3 HTB; lia) B2 W5) as (Rb2 & Hms4 & D8 & D9 & D10 & D17 & D19 & Kd2).
  set (m2 := wbytes m1 (wa (0 + 615024)) (word_to_le_bytes 8 (wa b))) in *.
  assert (KR2 : forall k, In k [1;2;3;4;18;20;21;22;23;24;25;26;27]%nat -> getr Rb2 (Z_to_bv 5 (Z.of_nat k)) = getr Rq (Z_to_bv 5 (Z.of_nat k))).
  { intros k Hk'. rewrite (Kd2 k Hk'). unfold Rb1'. rewrite getr_other; [exact (Ka1 k Hk')|]. clear - Hk'. cbn [In] in Hk'.
    repeat (destruct Hk' as [<-|Hk']; [regne|]). destruct Hk'. }
  assert (MO2 : forall x, 0 <= x < 2^64 -> ~ (615024 <= x < 615032) -> m2 (wa x) = m1 (wa x)) by (intros x Hx Hn; unfold m2; rewrite MngWb.wbytes_out by side; reflexivity).
  assert (MG2 : mem_grows m1 m2) by apply wbytes_grows.
  exists Rb2, (wa 0x51e10), m2. split; [exact Hms4|]. split.
  { split; [exact ecall_51a68|]. exists SYS_brk, [brk_cur L s + PGSZ * 2]. split; [reflexivity|].
    split; [rewrite D17; reflexivity|]. cbn [args_match]. split; [|exact I].
    rewrite Ebk. match type of D10 with getr _ ?r0 = _ => match goal with |- bv_unsigned (getr _ ?r1) = _ =>
      replace r1 with r0 by (apply bv_eq; reflexivity) end end.
    rewrite D10, u_wa; unfold PGSZ; f_equal; try ring. }
  intros eff' ans' L'' Ho'. destruct (kout_brk_grow FORB HTOP L s 2 eff' ans' L'' Ho') as [(-> & -> & ->) | (FR & -> & -> & EL')].
  - (* [comment removed for export] *)
    rewrite EKg0, add4_51a68. cbn [eff_ret]. rewrite Ebk.
    change (mem_after m2 (mkEffect (w64 b) [] [])) with m2.
    set (Rr := regupd Rb2 10 (w64 b)).
    assert (S8 : getr Rr 8 = wa 4096) by (unfold Rr; rewrite getr_other by regne; exact D8).
    assert (S9 : getr Rr 9 = wa (b + 8192)) by (unfold Rr; rewrite getr_other by regne; exact D9).
    assert (S10 : getr Rr 10 = wa b) by (unfold Rr; rewrite getr_same by regne; reflexivity).
    assert (S19 : getr Rr 19 = wa 614096) by (unfold Rr; rewrite getr_other by regne; exact D19).
    assert (M1 : rdn SEGS m2 (wa (0 + 615024)) 8 = Some (word_to_le_bytes 8 (wa b))) by (unfold m2; apply rdn_wbytes_hit8; side).
    assert (M3 : rdn SEGS m2 (wa (0 + 614144)) 8 = Some (word_to_le_bytes 8 (wa 0))).
    { rewrite (rdn_frame_n m1 m2) by (first [(intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; apply MO2; lia) | lia]). exact Mac. }
    assert (M4 : rdn SEGS m2 (wa (0 + 614152)) 8 = Some (word_to_le_bytes 8 (wa (st_meta_alloc_shift s)))).
    { rewrite (rdn_frame_n m1 m2) by (first [(intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; apply MO2; lia) | lia]). exact Msh. }
    assert (W5' : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m2 (wa (0 + 615024 + d)) k = true)
      by (intros d k Hd Hk'; apply (store_ok_mono SEGS k m1 m2 _ MG2); exact (W5 d k Hd Hk')).
    destruct (seg_bnr Rr m2 rom b b (st_meta_alloc_shift s) S8 S9 S10 S19 ltac:(clear - B1 B3 HTB; lia) ltac:(clear - B1 B3 HTB; lia) ltac:(lia) Rsh M1 M3 M4 W5')
      as (Rm & Hms5 & E1 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E19 & E20 & Ke).
    apply (wk_msteps SEGS FORB HTOP rom _ _ _ _ _ _ _ _ _ Hms5).
    set (m2d := wbytes m2 (wa (0 + 615024)) (word_to_le_bytes 8 (wa 18446744073709551615))).
    destruct (cut_dead HTOP X R U L s m1 sp0 K C1 ltac:(rewrite Hb; discriminate) Hi) as (C2 & G2).
    assert (EQ : forall x, 0 <= x < 2^64 -> m2d (wa x) = wbytes m1 (wa (0 + 615024)) (word_to_le_bytes 8 (wa 18446744073709551615)) (wa x))
      by (intros x Hx; unfold m2d, m2; apply wbytes_twice8; lia).
    assert (C2' : CUT HTOP X R U L (set_brk BrkDead s) m2d sp0 K).
    { apply (CUT_stack _ _ _ _ _ _ _ _ _ _ C2).
      - intros x Hx. rewrite <- (wa_u x) in Hx |- *. rewrite EQ by apply OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngU.MngLedger.u_range. exact Hx.
      - intros x Hx _. apply EQ. exact Hx. }
    assert (G2' : GROW sp0 K L s m1 L (set_brk BrkDead s) m2d) by (apply (GROW_ext _ _ _ _ _ _ _ _ _ G2); exact EQ).
    assert (MF : forall x, sp0 - 56 <= x < sp0 \/ 613952 <= x < 613960 \/ 614032 <= x < 614040 -> m2d (wa x) = m1 (wa x)).
    { intros x Hx. unfold m2d, m2. rewrite !MngWb.wbytes_out by side. reflexivity. }
    assert (Fm : am_frame Rm m2d sp0 can ra (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
                   (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 20))).
    { apply (am_frame_mem Rm m1); [| intros x Hx; apply MF; lia | intros x Hx; apply MF; lia].
      apply (am_frame_regs Rq Rm m1 sp0 can _ _ _ _ _ _ Fq).
      - regk Ke 2%nat. unfold Rr. rewrite getr_other by regne. exact (KR2 2%nat ltac:(cbn [In]; memb)).
      - regk Ke 18%nat. unfold Rr. rewrite getr_other by regne. exact (KR2 18%nat ltac:(cbn [In]; memb)).
      - rewrite E19. exact (eq_sym (mf_R19 _ _ _ _ _ _ _ _ _ _ Fq)). }
    assert (KA : forall k, In k [3;4;21;22;23;24;25;26;27]%nat -> getr Rm (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
    { intros k Hk'. rewrite (Ke k ltac:(clear - Hk'; klist Hk')). unfold Rr. rewrite getr_other.
      - rewrite (KR2 k ltac:(clear - Hk'; klist Hk')). exact (KA0 k Hk').
      - clear - Hk'. cbn [In] in Hk'. repeat (destruct Hk' as [<-|Hk']; [regne|]). destruct Hk'. }
    assert (Mpg2 : rdn SEGS m2d (wa 614032) 8 = Some (word_to_le_bytes 8 (wa 4096))).
    { rewrite (rdn_frame_n m1 m2d) by (first [(intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; apply MF; lia) | lia]). exact Mpg1. }
    exact (wk_resv_tail FORB HFORB WOR HTOP X R U L0 s0 m0 regs L (set_brk BrkDead s) m2d Rm rom sp0 K can ra K1 K2 C2'
             (GROW_trans sp0 K L0 s0 m0 L s m1 L _ _ GR0 G2') HK Fm R1 R2 Hra E1 E8 E9 E10 E11 E12 E13 E14 E15 E20 KA Hi Hf Hc Hac Mpg2 EK1 EK2).
  - (* [comment removed for export] *)
    rewrite Hb in EL'. subst L''.
    set (L' := set_reg_addr L (length (st_regions s)) b).
    rewrite EKg1. cbn [wk]. rewrite add4_51a68. cbn [eff_ret]. rewrite Ebk in FR |- *.
    set (m3 := mem_after m2 (mkEffect (w64 (b + PGSZ * 2)) [] [(w64 b, w64 (PGSZ * 2))])).
    pose proof FR as (FR1 & FR2 & FR3 & FR4 & FR5 & FR6 & FR7).
    assert (HIMG : ranges_disjoint (b, PGSZ * 2) (0x10000, 0x87000)) by (apply HFORB; [unfold PGSZ; lia | exact FR5]).
    unfold ranges_disjoint in HIMG. cbn [fst snd] in HIMG. unfold PGSZ in HIMG, FR4.
    assert (Rb : 4096 <= b <= 2^47 - 8192) by (clear - B1 FR4 HT Hsp2 HK; lia).
    assert (MA3 : forall x, 0 <= x < 2^64 -> m3 (wa x) = if (b <=? x) && (x <? b + PGSZ * 2) then Some (Z_to_bv 8 0) else m2 (wa x)).
    { intros x Hx. unfold m3. apply mem_after_zero; [clear - Rb; lia | clear; unfold PGSZ; lia | exact Hx]. }
    assert (HOUT3 : forall x, 0 <= x < 2^64 -> ~ (b <= x < b + 8192) -> m3 (wa x) = m2 (wa x)).
    { intros x Hx Hn. rewrite MA3 by exact Hx. replace ((b <=? x) && (x <? b + PGSZ * 2)) with false; [reflexivity|]. symmetry. apply andb_false_iff.
      unfold PGSZ. destruct (Z_le_gt_dec b x); [right; apply Z.ltb_ge; clear - Hn l; lia | left; apply Z.leb_gt; clear - g; lia]. }
    assert (MG3 : mem_grows m2 m3) by (unfold m3; apply mem_after_zero_grows; [clear - Rb; lia | clear; unfold PGSZ; lia]).
    assert (OFF : forall x, (613952 <= x < 613960 \/ 614032 <= x < 614040 \/ 614144 <= x < 614160 \/ 615024 <= x < 615032 \/ sp0 - 1152 <= x < sp0) ->
                    ~ (b <= x < b + 8192)).
    { intros x Hx. clear - Hx HIMG FR4 HT HK. lia. }
    (* [comment removed for export] *)
    set (Rg1 := regupd Rb2 10 (w64 (b + PGSZ * 2))).
    assert (T8 : getr Rg1 8 = wa 4096) by (unfold Rg1; rewrite getr_other by regne; exact D8).
    assert (T9 : getr Rg1 9 = wa (b + 8192)) by (unfold Rg1; rewrite getr_other by regne; exact D9).
    assert (T10 : getr Rg1 10 = wa (b + 8192)) by (unfold Rg1; rewrite getr_same by regne; reflexivity).
    assert (T19 : getr Rg1 19 = wa 614096) by (unfold Rg1; rewrite getr_other by regne; exact D19).
    assert (Mb3 : rdn SEGS m3 (wa (0 + 615024)) 8 = Some (word_to_le_bytes 8 (wa b))).
    { rewrite (rdn_frame_n m2 m3) by (first [(intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; apply HOUT3; [lia | apply OFF; lia]) | lia]).
      unfold m2; apply rdn_wbytes_hit8; side. }
    assert (Mac3 : rdn SEGS m3 (wa (0 + 614144)) 8 = Some (word_to_le_bytes 8 (wa 0))).
    { rewrite (rdn_frame_n m1 m3) by (first [(intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; rewrite HOUT3 by (first [lia | apply OFF; lia]); apply MO2; lia) | lia]). exact Mac. }
    assert (Msh3 : rdn SEGS m3 (wa (0 + 614152)) 8 = Some (word_to_le_bytes 8 (wa (st_meta_alloc_shift s)))).
    { rewrite (rdn_frame_n m1 m3) by (first [(intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; rewrite HOUT3 by (first [lia | apply OFF; lia]); apply MO2; lia) | lia]). exact Msh. }
    assert (W53 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m3 (wa (0 + 615024 + d)) k = true)
      by (intros d k Hd Hk'; apply (store_ok_mono SEGS k m1 m3 _ (mem_grows_trans m1 m2 m3 MG2 MG3)); exact (W5 d k Hd Hk')).
    destruct (seg_bng Rg1 m3 rom b (st_meta_alloc_shift s) T8 T9 T10 T19 Rb Rsh Mb3 Mac3 Msh3 W53)
      as (Rg2 & Hms5 & G1' & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G19 & Kg2).
    assert (KR3 : forall k, In k [2;3;4;18;20;21;22;23;24;25;26;27]%nat -> getr Rg2 (Z_to_bv 5 (Z.of_nat k)) = getr Rq (Z_to_bv 5 (Z.of_nat k))).
    { intros k Hk'. rewrite (Kg2 k Hk'). unfold Rg1. rewrite getr_other; [apply KR2; clear - Hk'; klist Hk'|]. clear - Hk'. cbn [In] in Hk'.
      repeat (destruct Hk' as [<-|Hk']; [regne|]). destruct Hk'. }
    assert (G2' : getr Rg2 2 = wa (sp0 + -64)) by (regk KR3 2%nat; exact (mf_R2 _ _ _ _ _ _ _ _ _ _ Fq)).
    assert (G18 : getr Rg2 18 = wa 613952) by (regk KR3 18%nat; exact (mf_R18 _ _ _ _ _ _ _ _ _ _ Fq)).
    assert (STK3 : stk_ok SEGS m3 (wa (sp0 + -64)) 1024).
    { apply (stk_ok_grows SEGS m1 m3); [|exact (mem_grows_trans m1 m2 m3 MG2 MG3)].
      apply (stk_ok_mono' m1 (wa (sp0 + -64)) (K - 64) 1024); [|clear - HK; lia].
      replace (sp0 + -64) with (sp0 - 64) by ring. apply stk_ok_shift; [exact HSTK1 | clear - HK; lia | clear - HK Hsp1; lia | clear - Hsp2; lia]. }
    destruct (seg_gmw Rg2 m3 rom sp0 b G1' G2' G8 G9 G10 G11 G12 G13 G14 G15 G18 G19 Rb STK3 ltac:(clear - Hsp1 Hsp2 HK; lia) Hsp3)
      as (Rg3 & m4 & Hms6 & H17 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H2 & Kh3 & SV4 & MO4 & MG4).
    assert (EBB : brk_base L' (s_bng s) = b) by (unfold brk_base, s_bng, L', set_reg_addr; cbn [st_brk set_brk ly_reg]; rewrite Nat.eqb_refl; reflexivity).
    exists Rg3, (wa 0x533ec), m4. split; [exact (msteps_trans SEGS _ _ _ Hms5 Hms6)|]. split.
    { split; [exact ecall_52ecc|]. exists SYS_mmap, [brk_base L' (s_bng s); PGSZ; 0; 50; 2 ^ 64 - 1; 0]. split; [reflexivity|].
      split; [rewrite H17; reflexivity|]. cbn [args_match]. rewrite EBB.
      Ltac argk' T := match type of T with getr _ ?r0 = _ => match goal with |- bv_unsigned (getr _ ?r1) = _ =>
        replace r1 with r0 by (apply bv_eq; reflexivity) end end; rewrite T, u_wa; first [reflexivity | (f_equal; unfold PGSZ; ring)].
      split; [argk' H10|]. split; [argk' H11|]. split; [argk' H12|]. split; [argk' H13|]. split; [argk' H14|]. split; [argk' H15|]. exact I. }
    intros eff3 ans3 L3 Ho3. destruct (kout_guard FORB HTOP L' (s_bng s) eff3 ans3 L3 Ho3) as (-> & -> & ->).
    rewrite EKd. cbn [wk]. rewrite add4_52ecc. cbn [eff_ret]. rewrite EBB.
    set (m5 := mem_after m4 (mkEffectU (w64 b) [] [] [(w64 b, w64 PGSZ)] [] [])).
    assert (MA5 : forall x, 0 <= x < 2^64 -> m5 (wa x) = if (b <=? x) && (x <? b + PGSZ) then None else m4 (wa x)).
    { intros x Hx. unfold m5. apply mem_after_unmap; [clear - Rb; lia | clear; unfold PGSZ; lia | exact Hx]. }
    assert (HOUT5a : forall x, 0 <= x < 2^64 -> ~ (b <= x < b + 4096) -> m5 (wa x) = m4 (wa x)).
    { intros x Hx Hn. rewrite MA5 by exact Hx. replace ((b <=? x) && (x <? b + PGSZ)) with false; [reflexivity|]. symmetry. apply andb_false_iff.
      unfold PGSZ. destruct (Z_le_gt_dec b x); [right; apply Z.ltb_ge; clear - Hn l; lia | left; apply Z.leb_gt; clear - g; lia]. }
    (* [comment removed for export] *)
    set (Rg4 := regupd Rg3 10 (w64 b)).
    assert (U2 : getr Rg4 2 = wa (sp0 + -64 + -64)) by (unfold Rg4; rewrite getr_other by regne; exact H2).
    assert (U10 : getr Rg4 10 = wa b) by (unfold Rg4; rewrite getr_same by regne; reflexivity).
    assert (U16 : getr Rg4 16 = wa b) by (unfold Rg4; rewrite getr_other by regne; exact H16).
    set (v20 := bv_unsigned (getr Rg2 20)). set (v21 := bv_unsigned (getr Rg2 21)).
    assert (Rv20 : 0 <= v20 <= 2^64-1) by (pose proof (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngU.MngLedger.u_range (getr Rg2 20)); unfold v20; lia).
    assert (Rv21 : 0 <= v21 <= 2^64-1) by (pose proof (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngU.MngLedger.u_range (getr Rg2 21)); unfold v21; lia).
    assert (SV5 : mmap_saves m5 (sp0 + -64) 335412 4096 (b + 8192) 613952 614096 v20 v21).
    { apply (mmap_saves_frame m4 m5 _ _ _ _ _ _ _ _ SV4); [clear - Hsp1 Hsp2 HK; lia|].
      intros x Hx. apply HOUT5a; [clear - Hx Hsp1 Hsp2 HK; lia | intros Hb'; clear - Hx Hb' HT FR4 HK; lia]. }
    destruct (seg_gmr Rg4 m5 rom sp0 b v20 v21 U2 U10 U16 ltac:(clear - Hsp1 Hsp2 HK; lia) Hsp3 Rb Rv20 Rv21 SV5)
      as (Rg5 & Hms7 & V1 & V2 & V8 & V9 & V10 & V18 & V19 & V20 & V21 & Kv5).
    (* [comment removed for export] *)
    assert (MO5 : forall x, 0 <= x < 2^64 -> (613952 <= x < 613960 \/ 614032 <= x < 614040 \/ 614144 <= x < 614160 \/ 615024 <= x < 615032 \/ sp0 - 56 <= x < sp0) ->
                    m5 (wa x) = m2 (wa x)).
    { intros x Hx Hr. rewrite HOUT5a by (first [(intros Hb'; apply (OFF x); [lia | lia]) | lia]). rewrite MO4 by (first [(clear - Hr Hsp1 HK; lia) | lia]).
      apply HOUT3; [lia | apply OFF; lia]. }
    assert (W7a : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m5 (wa (0 + 615024 + d)) k = true).
    { intros d k Hd Hk'. apply (store_ok_eqm k m2 m5); [rewrite u_wa_small by lia; lia| |].
      - intros x Hx. rewrite u_wa_small in Hx by lia. rewrite <- (wa_u x). apply MO5; [apply OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngU.MngLedger.u_range | lia].
      - exact (store_ok_mono SEGS k m1 m2 _ MG2 (W5 d k Hd Hk')). }
    assert (W7b : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m5 (wa (0 + 614144 + d)) k = true).
    { intros d k Hd Hk'. apply (store_ok_eqm k m1 m5); [rewrite u_wa_small by lia; lia| |].
      - intros x Hx. rewrite u_wa_small in Hx by lia. rewrite <- (wa_u x). rewrite MO5 by (first [apply OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngU.MngLedger.u_range | lia]). apply MO2; [apply OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngU.MngLedger.u_range | lia].
      - exact (nc_acsh_wr L s m1 sp0 K d k N1 Hd ltac:(lia)). }
    destruct (seg_bn7 Rg5 m5 rom (b + 8192) V8 V9 V19 ltac:(clear - Rb; lia) W7a W7b) as (Rg6 & Hms8 & Y8 & Y9 & Y19 & Ky6).
    change (wbytes (wbytes m5 (wa (0 + 615024)) (word_to_le_bytes 8 (wa (b + 8192)))) (wa (0 + 614144)) (word_to_le_bytes 8 (wa 1)))
      with (bcg_mem m5 (b + 8192)) in Hms8.
    (* [comment removed for export] *)
    assert (HE' : lext L L' s) by apply lext_set_new.
    destruct (NC_transport X R U s L L' HI HX HE' HTOP m1 m1 sp0 K HTB N1 HG HD ltac:(intros; reflexivity) ltac:(intros; reflexivity) ltac:(intros; reflexivity))
      as (N1' & HG' & HD').
    assert (C1' : CUT HTOP X R U L' s m1 sp0 K) by (constructor; assumption).
    assert (HFP' : forall f, In f (footprint s) -> ranges_disjoint (b, 2 * PGSZ) (crange L' f)).
    { intros f Hf0. rewrite (crange_ext X R U s L L' HI HE' f Hf0). replace (2 * PGSZ) with (PGSZ * 2) by ring. exact (FR6 f Hf0). }
    assert (HIMG' : b + 8192 <= 0x10000 \/ 0x97000 <= b) by (clear - HIMG; lia).
    assert (HOUT5 : forall x, 0 <= x < 2^64 -> ~ (b <= x < b + 8192) -> ~ (sp0 - K <= x < sp0) -> ~ (615024 <= x < 615032) -> m5 (wa x) = m1 (wa x)).
    { intros x Hx Z1 Z2 Z3. rewrite HOUT5a by (first [(clear - Z1; lia) | lia]). rewrite MO4 by (first [(clear - Z2 HK; lia) | lia]).
      rewrite HOUT3 by assumption. apply MO2; assumption. }
    assert (MG4' : mem_grows m1 m4) by exact (mem_grows_trans m1 m3 m4 (mem_grows_trans m1 m2 m3 MG2 MG3) MG4).
    assert (HSTK6 : stk_ok SEGS (bcg_mem m5 (b + 8192)) (wa sp0) K).
    { apply (stk_ok_eqm m4); [exact (stk_ok_grows SEGS m1 m4 (wa sp0) K HSTK1 MG4') | clear - Hsp1 Hsp2 HK; lia |].
      intros x Hx. unfold bcg_mem. rewrite !MngWb.wbytes_out by (first [side | (clear - Hx Hsp1 HK; lia)]).
      apply HOUT5a; [clear - Hx Hsp1 Hsp2 HK; lia | (intros Hb'; clear - Hx Hb' HT FR4; lia)]. }
    pose proof (pcut_bng HTOP X R U L s m1 m5 sp0 K b C1' Hb HFP' HIMG' HOUT5 HSTK6) as P1.
    pose proof (grow_bng HTOP X R U L s m1 m5 sp0 K b C1' HIMG' HOUT5) as GR2.
    fold L' in P1, GR2.
    assert (HIo : Inv X R U (open_st (st_avail_meta_areas (s_bng s)) (s_bng s))) by exact (Inv_open_brk_first X R U s HI Hb Hac Hc Hi).
    assert (HX1 : XNM X (s_bng s)) by exact HX.
    assert (HG1 : rgeoA HTOP L' (s_bng s)).
    { apply (rgeoA_bng HTOP L s b HG); unfold PGSZ; [lia | exact B2 | clear - FR4; lia |]. unfold ranges_disjoint. cbn [fst snd]. clear - HIMG; lia. }
    assert (HD1 : rdisj L' (s_bng s)).
    { apply (rdisj_bng L s b HD). intros k rgk Hk' Lk. replace (2 * PGSZ) with (PGSZ * 2) by ring. exact (FR7 k rgk Hk' Lk). }
    pose proof (inv_areas HI) as (A1' & A2' & A3 & A4 & _).
    assert (Epa : loc_addr L' (LMem (st_avail_meta_areas (s_bng s))) = b + 4096).
    { unfold s_bng, L', set_reg_addr. cbn [st_avail_meta_areas set_brk set_avail_meta_areas loc_addr ly_reg]. rewrite Nat.eqb_refl. reflexivity. }
    assert (ZP6 : ZP (bcg_mem m5 (b + 8192)) (loc_addr L' (LMem (st_avail_meta_areas (s_bng s))))).
    { rewrite Epa. intros x Hx. unfold bcg_mem. rewrite !MngWb.wbytes_out by (first [side | (clear - Hx HIMG; unfold PGSZ in *; lia)]).
      rewrite HOUT5a by (first [(unfold PGSZ in Hx; lia) | lia]). rewrite MO4 by (first [(clear - Hx FR4 HT HK; unfold PGSZ in *; lia) | lia]).
      rewrite MA3 by (clear - Hx Rb; unfold PGSZ in *; lia).
      replace ((b <=? x) && (x <? b + PGSZ * 2)) with true; [reflexivity|]. symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; clear - Hx; unfold PGSZ in *; lia. }
    assert (MF6 : forall x, sp0 - 56 <= x < sp0 \/ 613952 <= x < 613960 -> bcg_mem m5 (b + 8192) (wa x) = m1 (wa x)).
    { intros x Hx. unfold bcg_mem. rewrite !MngWb.wbytes_out by (first [side | (clear - Hx Hsp1 HK; lia)]). rewrite MO5 by (first [(clear - Hx Hsp1 HK; lia) | lia]).
      apply MO2; [clear - Hx Hsp1 Hsp2 HK; lia | clear - Hx Hsp1 HK; lia]. }
    assert (F6 : am_frame Rg6 (bcg_mem m5 (b + 8192)) sp0 can ra (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
                   (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 20))).
    { apply (am_frame_mem Rg6 m1); [| intros x Hx; apply MF6; lia | intros x Hx; apply MF6; lia].
      apply (am_frame_regs Rq Rg6 m1 sp0 can _ _ _ _ _ _ Fq).
      - regk Ky6 2%nat. litr2 V2. exact (eq_sym (mf_R2 _ _ _ _ _ _ _ _ _ _ Fq)).
      - regk Ky6 18%nat. litr2 V18. exact (eq_sym (mf_R18 _ _ _ _ _ _ _ _ _ _ Fq)).
      - rewrite Y19. exact (eq_sym (mf_R19 _ _ _ _ _ _ _ _ _ _ Fq)). }
    assert (R69 : getr Rg6 9 = wa (loc_addr L' (LMem (st_avail_meta_areas (s_bng s))))) by (rewrite Y9, Epa; f_equal; ring).
    destruct (open_tail HTOP X R U L' (s_bng s) (bcg_mem m5 (b + 8192)) Rg6 rom sp0 K can ra _ _ _ _ _ P1 HK HIo HX1 HG1 HD1 Hi ltac:(cbn; lia)
                A3 A4 ZP6 F6 R69 Hra)
      as (R7 & m7 & Hms9 & Q1 & Q2 & Q8' & Q9' & Q10' & Q18' & Q19' & Q20' & QK & CC & GG).
    exists R7, (wa ra), m7. split; [exact (msteps_trans SEGS _ _ _ Hms7 (msteps_trans SEGS _ _ _ Hms8 Hms9))|].
    exists (padd (SP (length (st_regions s)) PGSZ) AREA_HDR), (s_opn (SP (length (st_regions s)) PGSZ) (s_bng s)).
    split; [reflexivity|]. split; [reflexivity|]. split; [exact Q10'|].
    split.
    { assert (KK : forall k, In k [3;4;21;22;23;24;25;26;27]%nat -> getr R7 (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
      { intros k Hk'. rewrite (QK k Hk'), (Ky6 k ltac:(clear - Hk'; klist Hk')).
        assert (E5 : getr Rg5 (Z_to_bv 5 (Z.of_nat k)) = getr Rg2 (Z_to_bv 5 (Z.of_nat k))).
        { destruct (Nat.eq_dec k 21) as [->|Hn21].
          - litr2 V21. unfold v21. apply wa_u.
          - assert (Hk2 : In k [3;4;22;23;24;25;26;27]%nat) by (clear - Hk' Hn21; cbn [In] in *; intuition congruence).
            rewrite (Kv5 k Hk2). unfold Rg4. rewrite getr_other; [exact (Kh3 k Hk2)|]. clear - Hk2. cbn [In] in Hk2.
            repeat (destruct Hk2 as [<-|Hk2]; [regne|]). destruct Hk2. }
        rewrite E5, (KR3 k ltac:(clear - Hk'; klist Hk')). exact (KA0 k Hk'). }
      intros k Hk'. cbn [In] in Hk'.
      destruct Hk' as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]].
      - litr2 Q1. exact (eq_sym R1).
      - litr2 Q2. exact (eq_sym R2).
      - apply KK. cbn [In]. memb.
      - apply KK. cbn [In]. memb.
      - litr2 Q8'. apply wa_u.
      - litr2 Q9'. apply wa_u.
      - litr2 Q18'. apply wa_u.
      - litr2 Q19'. apply wa_u.
      - litr2 Q20'. apply wa_u.
      - apply KK. cbn [In]. memb.
      - apply KK. cbn [In]. memb.
      - apply KK. cbn [In]. memb.
      - apply KK. cbn [In]. memb.
      - apply KK. cbn [In]. memb.
      - apply KK. cbn [In]. memb.
      - apply KK. cbn [In]. memb. }
    split; [exact CC|].
    exact (GROW_trans sp0 K L0 s0 m0 L s m1 L' _ _ GR0 (GROW_trans sp0 K L s m1 L' (s_bng s) (bcg_mem m5 (b + 8192)) L' _ _ GR2 GG)).
Qed.
#[using="HFORB WOR"] Theorem wk_bn : forall HTOP X R U L s m (regs : bvmap 5 word) rom sp0 K ra,
  CUT HTOP X R U L s m sp0 K -> 1152 <= K -> getr regs 2 = wa sp0 -> getr regs 1 = wa ra -> (ra = 0x524e8 \/ ra = 0x5210c) ->
  rdn SEGS m (wa 614032) 8 = Some (word_to_le_bytes 8 (wa 4096)) ->
  PGSZ <= ly_brk0 L -> ly_brk0 L mod PGSZ = 0 -> ly_brk0 L <= HTOP ->
  st_init_done s = true -> st_free_meta_head s = None -> st_avail_meta_count s = 0 -> st_avail_meta_area_count s = 0 ->
  st_brk s = BrkNever ->
  wk SEGS FORB HTOP rom L regs (wa 0x51ca8) m (alloc_meta s) (am_qpost HTOP X R U L s m regs sp0 K ra).
Proof. LiaFast.lf_pins (fun (HFORB WOR : LiaFast.U) => LiaFast.u0).
  intros HTOP X R U L s m regs rom sp0 K ra C HK R2 R1 Hra Mpg B1 B2 B3 Hi Hf Hc Hac Hb.
  pose proof C as [HI HX N HG HD HT HTB].
  pose proof (nc_sp1 _ _ _ _ _ _ _ N) as Hsp1.
  destruct (seg_amp L s m regs rom sp0 K N R2) as (Rg & can & Hms1 & F1 & Kp1 & MO1 & MG1).
  set (m1 := am_mem0 m regs sp0 can) in *.
  assert (C1 : CUT HTOP X R U L s m1 sp0 K) by (apply (CUT_stack HTOP X R U L s m m1 sp0 K C MG1); intros x Hx Hn; apply MO1; [exact Hx | clear - Hn HK; lia]).
  assert (GR1 : GROW sp0 K L s m L s m1).
  { apply GROW_stack; [|clear - Hsp1; lia]. intros x Hx Hne. destruct (range_dec x (sp0 - 56) 56) as [I|I]; [clear - I HK; lia|]. exfalso. apply Hne. apply MO1; [exact Hx | clear - I; lia]. }
  assert (Mpg1 : rdn SEGS m1 (wa 614032) 8 = Some (word_to_le_bytes 8 (wa 4096))).
  { rewrite (rdn_frame_n m m1 614032 8) by (try lia; intros x Hx; apply MO1; cbn in Hx; lia). exact Mpg. }
  destruct (seg_amq HTOP X R U L s m1 Rg rom sp0 K sp0 can _ _ _ _ _ _ F1 C1 Hi Hf Hc Mpg1) as (Rq & Hms2 & Q8 & Fq & Kq2).
  assert (Rra : bv_unsigned (getr regs 1) = ra) by (rewrite R1; apply u_wa_small; clear - Hra; destruct Hra as [-> | ->]; lia).
  rewrite Rra in Fq.
  apply (wk_msteps SEGS FORB HTOP rom _ _ _ _ _ _ _ _ _ (msteps_trans SEGS _ _ _ Hms1 Hms2)).
  apply (wk_bn_tail HTOP X R U L s m regs L s m1 Rq rom sp0 K can ra C1 GR1 HK Fq R1 R2 Hra Q8); try assumption.
  intros k Hk'. rewrite (Kq2 k ltac:(clear - Hk'; klist Hk')), (Kp1 k ltac:(clear - Hk'; klist Hk')). reflexivity.
Qed.
End WKN.
