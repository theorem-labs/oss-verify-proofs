(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMeta.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngImage MngWb MngWk MngGeoX MngLt MngSurgery MngExc MngNtfPre MngNtfC MngGM MngCtx2.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ MngNtfM MngNtfS MngShift MngMWP MngMW0 MngMW1 MngShift AXG_am1 AXG_am3 AXG_am4 AXG_am5 AXG_am6.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition s_resv (s : astate) : astate :=
  let n := Z.shiftl 2 (st_meta_alloc_shift s) in
  set_meta_alloc_shift (st_meta_alloc_shift s + 1)
    (set_avail_meta_area_count (n - 1)
      (set_avail_meta_areas (SP (length (st_regions s)) PGSZ)
        (set_regions (st_regions s ++ [mkRegion RkMetaRes (n * PGSZ) [] true]) s))).

Definition rg_resv (s : astate) : region := mkRegion RkMetaRes (Z.shiftl 2 (st_meta_alloc_shift s) * PGSZ) [] true.

Lemma alloc_meta_resv : forall s, st_init_done s = true -> st_free_meta_head s = None -> st_avail_meta_count s = 0 ->
  st_avail_meta_area_count s = 0 -> st_brk s = BrkDead ->
  exists K1 K2, alloc_meta s = IAsk (KMmapNone (Z.shiftl 2 (st_meta_alloc_shift s) * PGSZ)) s K1 /\
    K1 1 = IAsk (KMprotect (SP (length (st_regions s)) PGSZ)) (s_resv s) K2 /\
    K2 1 = IRet (Some (padd (SP (length (st_regions s)) PGSZ) AREA_HDR),
                 s_opn (SP (length (st_regions s)) PGSZ) (s_res1 (s_resv s) (length (st_regions s)) (rg_resv s) PGSZ)).
Proof.
  intros s Hi Hf Hc Hac Hb. do 2 eexists. split; [|split].
  - unfold alloc_meta. cbn. rewrite set_init_done_same by exact Hi. rewrite Hf. cbn. rewrite Hc. cbn.
    unfold area_from_brk. cbn. rewrite Hac, Hb. cbn. unfold area_from_mmap. cbn. rewrite Hac. cbn. reflexivity.
  - cbn. reflexivity.
  - cbn. unfold s_resv, rg_resv. cbn. rewrite nth_middle.
    unfold ret, s_opn, s_take, open_st, s_res1, rw_page. cbn. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sh_cell (v : Z) : mcell := MCell (LCtx CTX_meta_alloc_shift) 8 (VZ v).

Lemma shl2_pos : forall sh, 0 <= sh -> 2 <= Z.shiftl 2 sh.
Proof. intros sh H. rewrite Z.shiftl_mul_pow2 by exact H. pose proof (Z.pow_pos_nonneg 2 sh ltac:(lia) H). lia. Qed.

Lemma resv_cov_ctx : forall s c, 0 <= st_meta_alloc_shift s -> In c (ctx_cells (s_resv s)) ->
  In c (ctx_cells s) \/ c = ac_cell (Z.shiftl 2 (st_meta_alloc_shift s) - 1) \/ c = sh_cell (st_meta_alloc_shift s + 1) \/
  c = ama_cell (SP (length (st_regions s)) PGSZ).
Proof.
  intros s c Hsh Hc. pose proof (shl2_pos _ Hsh) as P2.
  assert (E : (Z.shiftl 2 (st_meta_alloc_shift s) - 1 =? 0) = false) by (apply Z.eqb_neq; lia).
  unfold s_resv, ctx_cells in Hc.
  cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count
      st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_seq st_brk st_active st_usage
      st_unmap_seq st_bounces set_meta_alloc_shift set_avail_meta_area_count set_avail_meta_areas set_regions] in Hc.
  rewrite E, andb_false_r in Hc.
  apply in_app_iff in Hc as [Hc|Hc]; [|left; unfold ctx_cells; apply in_app_iff; right; exact Hc].
  cbn [In] in Hc.
  repeat (destruct Hc as [<-|Hc]; [first [ (left; unfold ctx_cells; apply in_app_iff; left; cbn [In]; solve [memb])
                                        | (right; left; reflexivity) | (right; right; left; reflexivity) | (right; right; right; reflexivity) ] |]).
  destruct Hc.
Qed.

Lemma resv_rev_ctx : forall s c, 0 <= st_meta_alloc_shift s -> In c (ctx_cells s) ->
  In c (ctx_cells (s_resv s)) \/ ((mc_loc c = LCtx CTX_avail_meta_area_count \/ mc_loc c = LCtx CTX_meta_alloc_shift \/
     mc_loc c = LCtx CTX_avail_meta_areas) /\ mc_w c = 8%nat).
Proof.
  intros s c Hsh Hc. pose proof (shl2_pos _ Hsh) as P2.
  assert (E : (Z.shiftl 2 (st_meta_alloc_shift s) - 1 =? 0) = false) by (apply Z.eqb_neq; lia).
  unfold ctx_cells in Hc.
  apply in_app_iff in Hc as [Hc|Hc]; [|left; unfold ctx_cells; apply in_app_iff; right; exact Hc].
  cbn [In] in Hc.
  repeat (destruct Hc as [<-|Hc]; [first [ (left; unfold ctx_cells, s_resv; apply in_app_iff; left;
       cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count
            st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_seq st_brk
            set_meta_alloc_shift set_avail_meta_area_count set_avail_meta_areas set_regions In]; rewrite ?E, ?andb_false_r; solve [memb])
     | (right; split; [cbn [mc_loc]; first [ (left; reflexivity) | (right; left; reflexivity) | (right; right; reflexivity) ] | reflexivity]) ] |]).
  destruct Hc.
Qed.

Lemma resv_areas_cells : forall s l, areas_cells (s_resv s) l = areas_cells s l.
Proof. intros s l. apply areas_cells_ext. intros q. reflexivity. Qed.

Lemma resv_used : forall s, used_metas (s_resv s) = used_metas s.
Proof. reflexivity. Qed.

Lemma resv_cov : forall s c, 0 <= st_meta_alloc_shift s -> In c (image (s_resv s)) ->
  In c (image s) \/ c = ac_cell (Z.shiftl 2 (st_meta_alloc_shift s) - 1) \/ c = sh_cell (st_meta_alloc_shift s + 1) \/
  c = ama_cell (SP (length (st_regions s)) PGSZ).
Proof.
  intros s c Hsh Hc. unfold image in Hc. apply in_app_iff in Hc as [Hc|Hc].
  - destruct (resv_cov_ctx s c Hsh Hc) as [H|H]; [left; apply ctx_in_image; exact H | right; exact H].
  - left. unfold image. apply in_app_iff. right. replace (st_areas (s_resv s)) with (st_areas s) in Hc by reflexivity.
    rewrite resv_areas_cells, resv_used in Hc. exact Hc.
Qed.

Lemma resv_rev : forall s c, 0 <= st_meta_alloc_shift s -> In c (image s) ->
  In c (image (s_resv s)) \/ ((mc_loc c = LCtx CTX_avail_meta_area_count \/ mc_loc c = LCtx CTX_meta_alloc_shift \/
     mc_loc c = LCtx CTX_avail_meta_areas) /\ mc_w c = 8%nat).
Proof.
  intros s c Hsh Hc. unfold image in Hc. apply in_app_iff in Hc as [Hc|Hc].
  - destruct (resv_rev_ctx s c Hsh Hc) as [H|H]; [left; apply ctx_in_image; exact H | right; exact H].
  - left. unfold image. apply in_app_iff. right. replace (st_areas (s_resv s)) with (st_areas s) by reflexivity.
    rewrite resv_areas_cells, resv_used. exact Hc.
Qed.

Lemma resv_cells_in : forall s, 0 <= st_meta_alloc_shift s ->
  In (ac_cell (Z.shiftl 2 (st_meta_alloc_shift s) - 1)) (image (s_resv s)) /\ In (sh_cell (st_meta_alloc_shift s + 1)) (image (s_resv s)) /\
  In (ama_cell (SP (length (st_regions s)) PGSZ)) (image (s_resv s)).
Proof.
  intros s Hsh. pose proof (shl2_pos _ Hsh) as P2.
  assert (E : (Z.shiftl 2 (st_meta_alloc_shift s) - 1 =? 0) = false) by (apply Z.eqb_neq; lia).
  split; [|split]; apply ctx_in_image; unfold ctx_cells, s_resv; apply in_app_iff; left;
    cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count
         st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_seq st_brk
         set_meta_alloc_shift set_avail_meta_area_count set_avail_meta_areas set_regions In]; rewrite ?E, ?andb_false_r; solve [memb].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma region_of_resv : forall s k rg, region_of (s_resv s) k = Some rg ->
  (region_of s k = Some rg /\ (k < length (st_regions s))%nat) \/ (k = length (st_regions s) /\ rg = rg_resv s).
Proof.
  intros s k rg H. unfold region_of, s_resv in H. cbn [st_regions set_meta_alloc_shift set_avail_meta_area_count set_avail_meta_areas set_regions] in H.
  destruct (Nat.lt_ge_cases k (length (st_regions s))) as [Hl|Hl].
  - left. rewrite nth_error_app1 in H by exact Hl. split; [exact H | exact Hl].
  - right. rewrite nth_error_app2 in H by exact Hl. destruct (k - length (st_regions s))%nat as [|j] eqn:E.
    + cbn in H. injection H as <-. split; [lia | reflexivity].
    + cbn in H. destruct j; discriminate H.
Qed.

Lemma resv_footprint : forall s rg, In rg (footprint (s_resv s)) -> In rg (footprint s).
Proof.
  intros s rg H. unfold footprint in *. destruct H as [H|H]; [left; exact H|]. right.
  apply in_app_iff in H as [H|H]; [apply in_app_iff; left; exact H|]. apply in_app_iff. right.
  apply in_flat_map in H as (k & Hk & Hin). apply in_flat_map. exists k.
  destruct (region_of (s_resv s) k) as [rg0|] eqn:E; [|destruct Hin].
  destruct (region_of_resv s k rg0 E) as [(E' & Hl)|(-> & ->)].
  - split; [apply in_seq; lia|]. rewrite E'. exact Hin.
  - exfalso. cbn [rg_resv rg_kind] in Hin. exact Hin.
Qed.

Lemma RMONO_resv : forall s, RMONO s (s_resv s).
Proof.
  intros s. split.
  - unfold s_resv. cbn [st_regions set_meta_alloc_shift set_avail_meta_area_count set_avail_meta_areas set_regions]. rewrite length_app. cbn. lia.
  - intros r rg Hr Hl. exists rg. split; [|split; [exact Hl|]; split; [reflexivity | lia]].
    unfold region_of, s_resv. cbn [st_regions set_meta_alloc_shift set_avail_meta_area_count set_avail_meta_areas set_regions].
    rewrite nth_error_app1 by exact (region_of_lt _ _ _ Hr). exact Hr.
Qed.

Section RESV.
Variables (HTOP : Z) (FORB : list (Z * Z)) (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (L : layout) (s : astate).
Variables (m1 m1' : word -> option byte) (sp0 K a : Z).
Hypothesis C : CUT HTOP X R U L s m1 sp0 K.
Hypothesis Hi : st_init_done s = true.
Hypothesis Hac : st_avail_meta_area_count s = 0.
Hypothesis FR : fresh_range FORB HTOP L s a (Z.shiftl 2 (st_meta_alloc_shift s) * PGSZ).
Hypothesis HIMG : ranges_disjoint (a, Z.shiftl 2 (st_meta_alloc_shift s) * PGSZ) (0x10000, 0x89000).
Hypothesis HM1 : forall x, 0 <= x < 2^64 -> ~ (a <= x < a + Z.shiftl 2 (st_meta_alloc_shift s) * PGSZ) -> m1' (wa x) = m1 (wa x).

Local Notation sh := (st_meta_alloc_shift s).
Local Notation r := (length (st_regions s)).
Local Notation L' := (set_reg_addr L (length (st_regions s)) a).

#[using="Type"] Lemma L'_reg_new : ly_reg L' r = a.
Proof. LiaFast.lf_pins LiaFast.u0. unfold set_reg_addr. cbn [ly_reg]. rewrite Nat.eqb_refl. reflexivity. Qed.

#[using="Type"] Lemma L'_reg_old : forall k, k <> r -> ly_reg L' k = ly_reg L k.
Proof. LiaFast.lf_pins LiaFast.u0. intros k Hk. unfold set_reg_addr. cbn [ly_reg]. rewrite (proj2 (Nat.eqb_neq k _) Hk). reflexivity. Qed.

#[using="FORB X R U m1 sp0 K C FR HIMG"] Lemma resv_geo : rgeoA HTOP L' (s_resv s) /\ rdisj L' (s_resv s).
Proof. LiaFast.lf_pins (fun (FORB X R U m1 sp0 K C FR HIMG : LiaFast.U) => LiaFast.u0).
  pose proof C as [HI HX N HG HD HT HTB]. destruct FR as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  split.
  - intros k rg Hk Hl. destruct (region_of_resv s k rg Hk) as [(E & Hlt)|(-> & ->)].
    + rewrite L'_reg_old by lia. exact (HG k rg E Hl).
    + rewrite L'_reg_new. cbn [rg_resv rg_len]. unfold PGSZ in *. split; [lia|]. split; [exact F2|]. split; [lia | exact HIMG].
  - intros k1 k2 rg1 rg2 Hne H1 H2 L1 L2.
    destruct (region_of_resv s k1 rg1 H1) as [(E1 & Hl1)|(-> & ->)]; destruct (region_of_resv s k2 rg2 H2) as [(E2 & Hl2)|(-> & ->)].
    + rewrite !L'_reg_old by lia. exact (HD k1 k2 rg1 rg2 Hne E1 E2 L1 L2).
    + rewrite L'_reg_new, L'_reg_old by lia. cbn [rg_resv rg_len]. apply ranges_disjoint_sym'. exact (F7 k1 rg1 E1 L1).
    + rewrite L'_reg_new, L'_reg_old by lia. cbn [rg_resv rg_len]. exact (F7 k2 rg2 E2 L2).
    + exfalso. exact (Hne eq_refl).
Qed.

#[using="FORB C Hi Hac FR HIMG HM1"] Theorem cut_resv : CUT HTOP X R U L' (s_resv s) (rvx_mem m1' a sh) sp0 K /\ GROW sp0 K L s m1 L' (s_resv s) (rvx_mem m1' a sh).
Proof. LiaFast.lf_pins (fun (FORB C Hi Hac FR HIMG HM1 : LiaFast.U) => LiaFast.u0).
  pose proof C as [HI HX N HG HD HT HTB]. pose proof (nc_ctx _ _ _ _ _ _ _ N) as Hctx.
  pose proof (inv_ctx HI) as CT. unfold ctx_ok in CT. destruct CT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Csh & _).
  pose proof (shl2_pos sh Csh) as P2.
  destruct FR as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  pose proof (shift_le_34 X R U s HTOP L HI HG HD HTB) as S34.
  destruct resv_geo as (HG' & HD').
  assert (HCtx' : ly_ctx L' = 0x97c98) by exact Hctx.
  set (Cnew := [ac_cell (Z.shiftl 2 sh - 1); sh_cell (sh + 1); ama_cell (SP r PGSZ)]).
  assert (EQ1 : loc_addr L' (LCtx CTX_avail_meta_area_count) = 621760) by (cbn [loc_addr]; rewrite HCtx'; reflexivity).
  assert (EQ2 : loc_addr L' (LCtx CTX_meta_alloc_shift) = 621768) by (cbn [loc_addr]; rewrite HCtx'; reflexivity).
  assert (EQ3 : loc_addr L' (LCtx CTX_avail_meta_areas) = 621792) by (cbn [loc_addr]; rewrite HCtx'; reflexivity).
  assert (VA : sval_num L' (VP (SP r PGSZ)) = a + 4096) by (cbn [sval_num loc_addr]; rewrite L'_reg_new; reflexivity).
  assert (Hnr : 2 ^ 35 < 2 ^ 64) by (apply Z.pow_lt_mono_r; lia).
  assert (Rn : Z.shiftl 2 sh <= 2 ^ 35) by (rewrite Z.shiftl_mul_pow2 by exact Csh; pose proof (Z.pow_le_mono_r 2 sh 34 ltac:(lia) S34); lia).
  apply (effect_step HTOP X R U X R U L L' s (s_resv s) m1 m1' (rvx_mem m1' a sh) sp0 K Cnew a (Z.shiftl 2 sh * PGSZ) C (lext_set_new L s a)).
  - unfold PGSZ in *. lia.
  - exact F3.
  - exact F4.
  - unfold ranges_disjoint in HIMG. cbn [fst snd] in HIMG. lia.
  - exact HM1.
  - exact F6.
  - exists r, (rg_resv s). split; [unfold region_of, s_resv; cbn [st_regions set_meta_alloc_shift set_avail_meta_area_count set_avail_meta_areas set_regions];
      rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity|].
    split; [reflexivity|]. split; [left; lia|]. rewrite L'_reg_new. cbn [rg_resv rg_len]. lia.
  - exact (Inv_new_resv X R U s HI Hac Hi).
  - exact HX.
  - exact HG'.
  - exact HD'.
  - exact (RMONO_resv s).
  - intros rg Hrg. left. exact (resv_footprint s rg Hrg).
  - intros c Hc. destruct (resv_cov s c Csh Hc) as [H|H]; [left; exact H | right; unfold Cnew; cbn [In]; destruct H as [ -> | [ -> | -> ] ]; memb].
  - intros c Hc. unfold Cnew in Hc. destruct (resv_cells_in s Csh) as (I1 & I2 & I3).
    cbn [In] in Hc. destruct Hc as [<-|[<-|[<-|[]]]]; assumption.
  - intros c Hc. destruct (resv_rev s c Csh Hc) as [H|([Hl|[Hl|Hl]] & Hw)]; [left; exact H|right..].
    + exists (ac_cell (Z.shiftl 2 sh - 1)). split; [unfold Cnew; cbn [In]; left; reflexivity|]. unfold cell_range. rewrite Hl, Hw. reflexivity.
    + exists (sh_cell (sh + 1)). split; [unfold Cnew; cbn [In]; right; left; reflexivity|]. unfold cell_range. rewrite Hl, Hw. reflexivity.
    + exists (ama_cell (SP r PGSZ)). split; [unfold Cnew; cbn [In]; right; right; left; reflexivity|]. unfold cell_range. rewrite Hl, Hw. reflexivity.
  - unfold Cnew, rvx_mem.
    replace (wa (0 + 621760)) with (wa (loc_addr L' (LCtx CTX_avail_meta_area_count))) by (rewrite EQ1; reflexivity).
    replace (wa (0 + 621768)) with (wa (loc_addr L' (LCtx CTX_meta_alloc_shift))) by (rewrite EQ2; reflexivity).
    replace (wa (0 + 621792)) with (wa (loc_addr L' (LCtx CTX_avail_meta_areas))) by (rewrite EQ3; reflexivity).
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + eapply (cell_holds_frame L' _ _ (ac_cell (Z.shiftl 2 sh - 1)) ltac:(cbn; lia)).
      * refine (holds_wb L' m1' (ac_cell (Z.shiftl 2 sh - 1)) (Z.shiftl 2 sh + -1) _ _ _ _ _).
        all: cbn [mc_val mc_w mc_loc ac_cell]; rewrite ?EQ1; first [ (intros z E; discriminate E) | lia | (cbn [sval_num]; f_equal; lia) ].
      * intros x Hx. unfold in_rng, cell_range in Hx. cbn [ac_cell mc_loc mc_w fst snd] in Hx. rewrite EQ1 in Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx.
        apply MngWb.bview_ext. rewrite EQ2, EQ3. rewrite !MngWb.wbytes_out by side. reflexivity.
    + eapply (cell_holds_frame L' _ _ (sh_cell (sh + 1)) ltac:(cbn; lia)).
      * refine (holds_wb L' (wbytes m1' (wa (loc_addr L' (LCtx CTX_avail_meta_area_count))) (word_to_le_bytes 8 (wa (Z.shiftl 2 sh + -1))))
                  (sh_cell (sh + 1)) (sh + 1) _ _ _ _ _).
        all: cbn [mc_val mc_w mc_loc sh_cell]; rewrite ?EQ2; first [ (intros z E; discriminate E) | lia | (cbn [sval_num]; reflexivity) ].
      * intros x Hx. unfold in_rng, cell_range in Hx. cbn [sh_cell mc_loc mc_w fst snd] in Hx. rewrite EQ2 in Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx.
        apply MngWb.bview_ext. rewrite EQ3. rewrite !MngWb.wbytes_out by side. reflexivity.
    + refine (holds_wb L' _ (ama_cell (SP r PGSZ)) (a + 4096) _ _ _ _ _).
      all: cbn [mc_val mc_w mc_loc ama_cell]; rewrite ?EQ3; first [ (intros z E; discriminate E) | lia | (rewrite VA; reflexivity) ].
  - unfold rvx_mem. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
  - intros x Hx Hne. right. unfold rvx_mem in Hne.
    destruct (range_dec x 621792 8) as [I3|I3]; [exists (ama_cell (SP r PGSZ)); split; [unfold Cnew; cbn [In]; right; right; left; reflexivity|];
                                                  unfold in_rng, cell_range; cbn [ama_cell mc_loc mc_w fst snd]; rewrite EQ3; cbn; lia|].
    destruct (range_dec x 621768 8) as [I2|I2]; [exists (sh_cell (sh + 1)); split; [unfold Cnew; cbn [In]; right; left; reflexivity|];
                                                  unfold in_rng, cell_range; cbn [sh_cell mc_loc mc_w fst snd]; rewrite EQ2; cbn; lia|].
    destruct (range_dec x 621760 8) as [I1|I1]; [exists (ac_cell (Z.shiftl 2 sh - 1)); split; [unfold Cnew; cbn [In]; left; reflexivity|];
                                                  unfold in_rng, cell_range; cbn [ac_cell mc_loc mc_w fst snd]; rewrite EQ1; cbn; lia|].
    exfalso. apply Hne. rewrite !MngWb.wbytes_out by side. reflexivity.
Qed.
End RESV.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ecall_52ecc : exists w, fetch_word SEGS (wa 0x551a4) = Some w /\ is_ecall w = true.
Proof. eexists. split; [vm_compute; reflexivity | vm_compute; reflexivity]. Qed.

Lemma add4_52ecc : bv_add (wa 0x551a4) (w64 4) = wa 0x551a8.
Proof. apply bv_eq. reflexivity. Qed.

Lemma kout_mmap_na : forall FORB HTOP L s len eff ans L', koutcome FORB HTOP L s (KMmapNone len) eff ans L' ->
  exists a, fresh_range FORB HTOP L s a len /\ eff = mkEffectU (w64 a) [] [] [(w64 a, w64 len)] [] [] /\ ans = 1 /\
    L' = set_reg_addr L (length (st_regions s)) a.
Proof. intros FORB HTOP L s len eff ans L' H. inversion H; subst. exists a. auto. Qed.

Lemma wa_mod64 : forall v, wa v = wa (v mod 2^64).
Proof. intros v. apply bv_eq. rewrite !u_wa. rewrite Z.mod_mod by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma nc_acsh_wr : forall L s m sp0 K d k, NC L [] [] s m sp0 K -> 0 <= d -> d + Z.of_nat k <= 16 ->
  store_ok SEGS m (wa (621760 + d)) k = true.
Proof.
  intros L s m sp0 K d k N Hd Hk. pose proof (nc_ctx _ _ _ _ _ _ _ N) as Hctx.
  apply (store_ok_of_bytes SEGS m 621760 16); [|exact Hd | exact Hk].
  intros j Hj. destruct (Z_lt_le_dec j 8) as [D|D].
  - pose proof (holds_wview SEGS L m (MCell (LCtx CTX_avail_meta_area_count) 8 (VZ (st_avail_meta_area_count s))) j
      (nc_ctx_holds L s m sp0 K (MCell (LCtx CTX_avail_meta_area_count) 8 (VZ (st_avail_meta_area_count s))) N ltac:(in_ctx13))
      ltac:(intros z E; discriminate) ltac:(cbn; lia)) as W.
    cbn [mc_loc loc_addr] in W. rewrite Hctx in W. exact W.
  - pose proof (holds_wview SEGS L m (MCell (LCtx CTX_meta_alloc_shift) 8 (VZ (st_meta_alloc_shift s))) (j - 8)
      (nc_ctx_holds L s m sp0 K (MCell (LCtx CTX_meta_alloc_shift) 8 (VZ (st_meta_alloc_shift s))) N ltac:(in_ctx13))
      ltac:(intros z E; discriminate) ltac:(cbn; lia)) as W.
    cbn [mc_loc loc_addr] in W. rewrite Hctx in W. unfold CTX_meta_alloc_shift in W. replace (621760 + j) with (0x97c98 + 48 + (j - 8)) by ring. exact W.
Qed.

Lemma nc_ama_wr : forall L s m sp0 K d k, NC L [] [] s m sp0 K -> 0 <= d -> d + Z.of_nat k <= 8 ->
  store_ok SEGS m (wa (621792 + d)) k = true.
Proof.
  intros L s m sp0 K d k N Hd Hk. pose proof (nc_ctx _ _ _ _ _ _ _ N) as Hctx.
  pose proof (nc_ctx_wr L s m sp0 K (MCell (LCtx CTX_avail_meta_areas) 8
      (if (match st_areas s with [] => true | _ => false end) && (st_avail_meta_area_count s =? 0) then VZ 0 else VP (st_avail_meta_areas s)))
      N ltac:(in_ctx13) ltac:(destruct (_ && _); intros z E; discriminate E) d k Hd ltac:(cbn [mc_w]; lia)) as W.
  cbn [mc_loc loc_addr] in W. rewrite Hctx in W. exact W.
Qed.

Section WKD.
Context {fx : FPState}.
Variable FORB : list (Z * Z).
Hypothesis HFORB : forall a n, 0 < n -> Forall (fun r => ranges_disjoint (a, n) r) FORB -> ranges_disjoint (a, n) (0x10000, 0x89000).

(* [comment removed for export] *)
Hypothesis WOR : forall HTOP X R U L0 s0 m0 (regs0 : bvmap 5 word) L s m Rg rom sp0 K can ra r o rg
    (Kt : Z -> itree astate (option sptr * astate)),
  CUT HTOP X R U L s m sp0 K -> GROW sp0 K L0 s0 m0 L s m -> 1152 <= K ->
  am_frame Rg m sp0 can ra (bv_unsigned (getr regs0 8)) (bv_unsigned (getr regs0 9))
    (bv_unsigned (getr regs0 18)) (bv_unsigned (getr regs0 19)) (bv_unsigned (getr regs0 20)) ->
  getr regs0 1 = wa ra -> getr regs0 2 = wa sp0 -> (ra = 0x542a0 \/ ra = 0x53ec4) ->
  (forall k, In k [3;4;21;22;23;24;25;26;27]%nat -> getr Rg (Z_to_bv 5 (Z.of_nat k)) = getr regs0 (Z_to_bv 5 (Z.of_nat k))) ->
  getr Rg 1 = wa 343320 -> getr Rg 9 = wa (ly_reg L r + o) -> getr Rg 10 = wa (ly_reg L r + o) ->
  getr Rg 11 = wa 4096 -> getr Rg 12 = wa 3 ->
  st_init_done s = true -> st_free_meta_head s = None -> st_avail_meta_count s = 0 -> 0 < st_avail_meta_area_count s ->
  st_avail_meta_areas s = SP r o -> region_of s r = Some rg ->
  rdn SEGS m (wa 621648) 8 = Some (word_to_le_bytes 8 (wa 4096)) ->
  Kt 1 = IRet (Some (padd (SP r o) AREA_HDR), s_opn (SP r o) (s_res1 s r rg o)) ->
  wk SEGS FORB HTOP rom L Rg (wa 0x551cc) m (IAsk (KMprotect (SP r o)) s Kt)
     (am_qpost HTOP X R U L0 s0 m0 regs0 sp0 K ra).

(* [comment removed for export] *)
#[using="HFORB WOR"] Theorem wk_resv_tail : forall HTOP X R U L0 s0 m0 (regs0 : bvmap 5 word) L s m Rm rom sp0 K can ra K1 K2,
  CUT HTOP X R U L s m sp0 K -> GROW sp0 K L0 s0 m0 L s m -> 1152 <= K ->
  am_frame Rm m sp0 can ra (bv_unsigned (getr regs0 8)) (bv_unsigned (getr regs0 9))
    (bv_unsigned (getr regs0 18)) (bv_unsigned (getr regs0 19)) (bv_unsigned (getr regs0 20)) ->
  getr regs0 1 = wa ra -> getr regs0 2 = wa sp0 -> (ra = 0x542a0 \/ ra = 0x53ec4) ->
  getr Rm 1 = wa 343108 -> getr Rm 8 = wa 4096 -> getr Rm 9 = wa (Z.shiftl 2 (st_meta_alloc_shift s)) -> getr Rm 10 = wa 0 ->
  getr Rm 11 = wa (4096 * Z.shiftl 2 (st_meta_alloc_shift s)) -> getr Rm 12 = wa 0 -> getr Rm 13 = wa 34 ->
  getr Rm 14 = wa 18446744073709551615 -> getr Rm 15 = wa 0 -> getr Rm 20 = wa 18446744073709551615 ->
  (forall k, In k [3;4;21;22;23;24;25;26;27]%nat -> getr Rm (Z_to_bv 5 (Z.of_nat k)) = getr regs0 (Z_to_bv 5 (Z.of_nat k))) ->
  st_init_done s = true -> st_free_meta_head s = None -> st_avail_meta_count s = 0 -> st_avail_meta_area_count s = 0 ->
  rdn SEGS m (wa 621648) 8 = Some (word_to_le_bytes 8 (wa 4096)) ->
  K1 1 = IAsk (KMprotect (SP (length (st_regions s)) PGSZ)) (s_resv s) K2 ->
  K2 1 = IRet (Some (padd (SP (length (st_regions s)) PGSZ) AREA_HDR),
               s_opn (SP (length (st_regions s)) PGSZ) (s_res1 (s_resv s) (length (st_regions s)) (rg_resv s) PGSZ)) ->
  wk SEGS FORB HTOP rom L Rm (wa 0x550e0) m (IAsk (KMmapNone (Z.shiftl 2 (st_meta_alloc_shift s) * PGSZ)) s K1)
     (am_qpost HTOP X R U L0 s0 m0 regs0 sp0 K ra).
Proof. LiaFast.lf_pins (fun (HFORB WOR : LiaFast.U) => LiaFast.u0).
  intros HTOP X R U L0 s0 m0 regs0 L s m Rm rom sp0 K can ra K1 K2 C G0 HK Fm R1 R2 Hra
    A1 A8 A9 A10 A11 A12 A13 A14 A15 A20 KA Hi Hf Hc Hac Mpg EK1 EK2.
  pose proof C as [HI HX N HG HD HT HTB].
  pose proof (nc_ctx _ _ _ _ _ _ _ N) as Hctx. pose proof (nc_sp1 _ _ _ _ _ _ _ N) as Hsp1. pose proof (nc_sp2 _ _ _ _ _ _ _ N) as Hsp2.
  pose proof (nc_sp3 _ _ _ _ _ _ _ N) as Hsp3. pose proof (nc_stk _ _ _ _ _ _ _ N) as HSTK.
  pose proof (inv_ctx HI) as CT. unfold ctx_ok in CT. destruct CT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Csh & _).
  pose proof (shift_le_34 X R U s HTOP L HI HG HD HTB) as S34.
  assert (STK1 : stk_ok SEGS m (wa (sp0 + -64)) 1024).
  { apply (stk_ok_mono' m (wa (sp0 + -64)) (K - 64) 1024); [|lia].
    replace (sp0 + -64) with (sp0 - 64) by ring. apply stk_ok_shift; [exact HSTK | lia | lia | lia]. }
  destruct (seg_mmw Rm m rom sp0 (st_meta_alloc_shift s) A1 (mf_R2 _ _ _ _ _ _ _ _ _ _ Fm) A8 A9 A10 A11 A12 A13 A14 A15
              (mf_R18 _ _ _ _ _ _ _ _ _ _ Fm) (mf_R19 _ _ _ _ _ _ _ _ _ _ Fm) A20 ltac:(lia) STK1 ltac:(lia) Hsp3)
    as (R3 & m2 & Hms3 & T17 & T10 & T11 & T12 & T13 & T14 & T15 & T16 & T2 & Kb & SV & MO2 & MG2).
  assert (C2 : CUT HTOP X R U L s m2 sp0 K) by (apply (CUT_stack HTOP X R U L s m m2 sp0 K C MG2); intros x Hx Hn; apply MO2; [exact Hx | lia]).
  pose proof C2 as [_ _ N2 _ _ _ _].
  set (len := Z.shiftl 2 (st_meta_alloc_shift s) * PGSZ).
  assert (Rlen : 8192 <= len <= 2^47).
  { unfold len. rewrite Z.shiftl_mul_pow2 by exact Csh. pose proof (Z.pow_le_mono_r 2 (st_meta_alloc_shift s) 34 ltac:(lia) S34).
    pose proof (Z.pow_pos_nonneg 2 (st_meta_alloc_shift s) ltac:(lia) Csh). unfold PGSZ. lia. }
  cbn [wk].
  exists R3, (wa 0x551a4), m2. split; [exact Hms3|]. split.
  { split; [exact ecall_52ecc|]. exists SYS_mmap, [0; len; 0; 34; 2 ^ 64 - 1; 0]. split; [reflexivity|].
    split; [rewrite T17; reflexivity|].
    cbn [args_match].
    Ltac argk T := match type of T with getr _ ?r0 = _ => match goal with |- bv_unsigned (getr _ ?r1) = _ =>
      replace r1 with r0 by (apply bv_eq; reflexivity) end end; rewrite T, u_wa; first [reflexivity | (f_equal; unfold PGSZ; ring)].
    unfold len. split; [argk T10|]. split; [argk T11|]. split; [argk T12|]. split; [argk T13|]. split; [argk T14|]. split; [argk T15|]. exact I. }
  intros eff ans L' Ho. destruct (kout_mmap_na FORB HTOP L s _ eff ans L' Ho) as (a & FR & -> & -> & ->).
  rewrite EK1, add4_52ecc. cbn [eff_ret].
  pose proof FR as (FR1 & FR2 & FR3 & FR4 & FR5 & FR6 & FR7).
  assert (HIMG : ranges_disjoint (a, len) (0x10000, 0x89000)) by (apply HFORB; [lia | exact FR5]).
  set (m3 := mem_after m2 (mkEffectU (w64 a) [] [] [(w64 a, w64 len)] [] [])).
  assert (Ra : 4096 <= a <= 2^47) by (unfold PGSZ in *; lia).
  assert (HM3 : forall x, 0 <= x < 2^64 -> ~ (a <= x < a + len) -> m3 (wa x) = m2 (wa x)).
  { intros x Hx Hn. unfold m3. rewrite mem_after_unmap by lia.
    replace ((a <=? x) && (x <? a + len)) with false by (symmetry; apply andb_false_iff; destruct (Z_le_dec a x); [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia]).
    reflexivity. }
  set (R4 := regupd R3 10 (w64 a)).
  assert (R4_2 : getr R4 2 = wa (sp0 + -64 + -64)) by (unfold R4; rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; discriminate E); exact T2).
  assert (R4_10 : getr R4 10 = wa a) by (unfold R4; rewrite getr_same by (intros E; apply (f_equal bv_unsigned) in E; discriminate E); reflexivity).
  assert (R4_16 : getr R4 16 = wa 0) by (unfold R4; rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; discriminate E); exact T16).
  assert (Hlo : a + len <= sp0 - 1152) by lia.
  assert (FM3 : forall x, 0 <= x < 2^64 -> (0x10000 <= x < 0x99000 \/ sp0 - 1152 <= x) -> m3 (wa x) = m2 (wa x)).
  { intros x Hx Hr. apply HM3; [exact Hx|]. unfold ranges_disjoint in HIMG. cbn [fst snd] in HIMG. lia. }
  assert (SV3 : mmap_saves m3 (sp0 + -64) 343108 4096 (Z.shiftl 2 (st_meta_alloc_shift s)) 621568 621712 18446744073709551615 (bv_unsigned (getr Rm 21))).
  { destruct SV as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
    repeat split; (rewrite (rdn_frame_n m2 m3) by (try lia; intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; apply FM3; lia)); assumption. }
  assert (Msh : rdn SEGS m (wa (0 + 621768)) 8 = Some (word_to_le_bytes 8 (wa (st_meta_alloc_shift s)))).
  { pose proof (nc_ctx_rd L s m sp0 K (MCell (LCtx CTX_meta_alloc_shift) 8 (VZ (st_meta_alloc_shift s))) N ltac:(in_ctx13)
                  ltac:(intros z E; discriminate E) ltac:(cbn; lia)) as H. cbn [mc_loc mc_w mc_val loc_addr sval_num] in H. rewrite Hctx in H. exact H. }
  assert (Msh3 : rdn SEGS m3 (wa (0 + 621768)) 8 = Some (word_to_le_bytes 8 (wa (st_meta_alloc_shift s)))).
  { rewrite (rdn_frame_n m m3) by (try lia; intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; rewrite FM3 by lia; apply MO2; lia). exact Msh. }
  assert (W1 : forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m3 (wa (0 + 621760 + d)) k = true).
  { intros d k Hd Hk. apply (store_ok_eqm k m2 m3); [rewrite u_wa_small by lia; lia| |].
    - intros x Hx. rewrite u_wa_small in Hx by lia. rewrite <- (wa_u x). apply FM3; [apply OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngU.MngLedger.u_range | lia].
    - exact (nc_acsh_wr L s m2 sp0 K d k N2 Hd Hk). }
  assert (W2 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m3 (wa (0 + 621792 + d)) k = true).
  { intros d k Hd Hk. apply (store_ok_eqm k m2 m3); [rewrite u_wa_small by lia; lia| |].
    - intros x Hx. rewrite u_wa_small in Hx by lia. rewrite <- (wa_u x). apply FM3; [apply OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngU.MngLedger.u_range | lia].
    - exact (nc_ama_wr L s m2 sp0 K d k N2 Hd Hk). }
  assert (Rsp' : 2^20 + 1024 <= sp0 <= 2^47) by lia.
  assert (Rv21 : 0 <= bv_unsigned (getr Rm 21) <= 2^64-1) by (pose proof (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngU.MngLedger.u_range (getr Rm 21)); lia).
  assert (Aa : a mod 4096 = 0) by (unfold PGSZ in *; exact FR2).
  assert (Rsh : 0 <= st_meta_alloc_shift s <= 34) by lia.
  destruct (seg_rvx R4 m3 rom sp0 a (st_meta_alloc_shift s) (bv_unsigned (getr Rm 21)) R4_2 R4_10 R4_16 Rsp' Hsp3
              Rv21 SV3 Ra Aa Rsh Msh3 W1 W2)
    as (R5 & Hms4 & U1 & U2 & U8 & U9 & U10 & U11 & U12 & U18 & U19 & U20 & U21 & Ku).
  apply (wk_msteps SEGS FORB HTOP rom _ _ _ _ _ _ _ _ _ Hms4).
  set (m4 := rvx_mem m3 a (st_meta_alloc_shift s)).
  destruct (cut_resv HTOP FORB X R U L s m2 m3 sp0 K a C2 Hi Hac FR HIMG HM3) as (C4 & G4). fold m4 in C4, G4.
  assert (G1 : GROW sp0 K L s m L s m2).
  { apply GROW_stack; [|lia]. intros x Hx Hne. destruct (range_dec x (sp0 - 128) 64) as [I|I]; [lia|]. exfalso. apply Hne. apply MO2; [exact Hx | lia]. }
  assert (MF4 : forall x, sp0 - 56 <= x < sp0 \/ 621568 <= x < 621576 -> m4 (wa x) = m (wa x)).
  { intros x Hx. unfold m4, rvx_mem. rewrite !MngWb.wbytes_out by side. rewrite FM3 by lia. apply MO2; lia. }
  assert (F4 : am_frame R5 m4 sp0 can ra (bv_unsigned (getr regs0 8)) (bv_unsigned (getr regs0 9))
                 (bv_unsigned (getr regs0 18)) (bv_unsigned (getr regs0 19)) (bv_unsigned (getr regs0 20))).
  { apply (am_frame_mem R5 m); [| intros x Hx; apply MF4; lia | intros x Hx; apply MF4; lia].
    apply (am_frame_regs Rm R5 m sp0 can _ _ _ _ _ _ Fm).
    - rewrite U2. exact (eq_sym (mf_R2 _ _ _ _ _ _ _ _ _ _ Fm)).
    - rewrite U18. exact (eq_sym (mf_R18 _ _ _ _ _ _ _ _ _ _ Fm)).
    - rewrite U19. exact (eq_sym (mf_R19 _ _ _ _ _ _ _ _ _ _ Fm)). }
  assert (KP : forall k, In k [3;4;21;22;23;24;25;26;27]%nat -> getr R5 (Z_to_bv 5 (Z.of_nat k)) = getr regs0 (Z_to_bv 5 (Z.of_nat k))).
  { intros k Hk'. destruct (Nat.eq_dec k 21) as [->|Hn21].
    - match type of U21 with getr _ ?r0 = _ => replace (Z_to_bv 5 (Z.of_nat 21)) with r0 by (apply bv_eq; reflexivity) end.
      rewrite U21, wa_u. etransitivity; [|exact (KA 21%nat ltac:(cbn [In]; memb))]. reflexivity.
    - assert (Hk2 : In k [3;4;22;23;24;25;26;27]%nat) by (clear - Hk' Hn21; cbn [In] in *; intuition congruence).
      rewrite (Ku k Hk2). unfold R4. rewrite getr_other.
      + rewrite (Kb k ltac:(clear - Hk2; klist Hk2)). exact (KA k ltac:(clear - Hk2; klist Hk2)).
      + intros E. apply (f_equal bv_unsigned) in E. clear - Hk2 E. cbn [In] in Hk2.
        repeat (destruct Hk2 as [<-|Hk2]; [discriminate E|]). destruct Hk2. }
  assert (Mpg4 : rdn SEGS m4 (wa 621648) 8 = Some (word_to_le_bytes 8 (wa 4096))).
  { rewrite (rdn_frame_n m m4) by (try lia; intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; unfold m4, rvx_mem; rewrite !MngWb.wbytes_out by side;
                                   rewrite FM3 by lia; apply MO2; lia). exact Mpg. }
  apply (WOR HTOP X R U L0 s0 m0 regs0 _ (s_resv s) m4 R5 rom sp0 K can ra (length (st_regions s)) PGSZ (rg_resv s) K2 C4
           (GROW_trans sp0 K L0 s0 m0 L s m _ _ _ G0 (GROW_trans sp0 K L s m L s m2 _ _ _ G1 G4)) HK F4 R1 R2 Hra KP U1).
  - rewrite L'_reg_new. exact U9.
  - rewrite L'_reg_new. exact U10.
  - exact U11.
  - exact U12.
  - exact Hi.
  - exact Hf.
  - exact Hc.
  - cbn [s_resv st_avail_meta_area_count set_meta_alloc_shift set_avail_meta_area_count]. pose proof (shl2_pos _ Csh). lia.
  - reflexivity.
  - unfold region_of, s_resv. cbn [st_regions set_meta_alloc_shift set_avail_meta_area_count set_avail_meta_areas set_regions].
    rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
  - exact Mpg4.
  - exact EK2.
Qed.

(* [comment removed for export] *)
#[using="HFORB WOR"] Theorem wk_dead : forall HTOP X R U L s m (regs : bvmap 5 word) rom sp0 K ra,
  CUT HTOP X R U L s m sp0 K -> 1152 <= K -> getr regs 2 = wa sp0 -> getr regs 1 = wa ra -> (ra = 0x542a0 \/ ra = 0x53ec4) ->
  rdn SEGS m (wa 621648) 8 = Some (word_to_le_bytes 8 (wa 4096)) ->
  st_init_done s = true -> st_free_meta_head s = None -> st_avail_meta_count s = 0 -> st_avail_meta_area_count s = 0 ->
  st_brk s = BrkDead ->
  wk SEGS FORB HTOP rom L regs (wa 0x53a60) m (alloc_meta s) (am_qpost HTOP X R U L s m regs sp0 K ra).
Proof. LiaFast.lf_pins (fun (HFORB WOR : LiaFast.U) => LiaFast.u0).
  intros HTOP X R U L s m regs rom sp0 K ra C HK R2 R1 Hra Mpg Hi Hf Hc Hac Hb.
  pose proof C as [HI HX N HG HD HT HTB].
  pose proof (nc_ctx _ _ _ _ _ _ _ N) as Hctx. pose proof (nc_sp1 _ _ _ _ _ _ _ N) as Hsp1.
  destruct (alloc_meta_resv s Hi Hf Hc Hac Hb) as (K1 & K2 & Et & EK1 & EK2). rewrite Et.
  destruct (seg_amp L s m regs rom sp0 K N R2) as (Rg & can & Hms1 & F1 & Kp1 & MO1 & MG1).
  set (m1 := am_mem0 m regs sp0 can) in *.
  assert (C1 : CUT HTOP X R U L s m1 sp0 K) by (apply (CUT_stack HTOP X R U L s m m1 sp0 K C MG1); intros x Hx Hn; apply MO1; [exact Hx | lia]).
  assert (G1 : GROW sp0 K L s m L s m1).
  { apply GROW_stack; [|lia]. intros x Hx Hne. destruct (range_dec x (sp0 - 56) 56) as [I|I]; [lia|]. exfalso. apply Hne. apply MO1; [exact Hx | lia]. }
  assert (Mpg1 : rdn SEGS m1 (wa 621648) 8 = Some (word_to_le_bytes 8 (wa 4096))).
  { rewrite (rdn_frame_n m m1 621648 8) by (try lia; intros x Hx; apply MO1; cbn in Hx; lia). exact Mpg. }
  destruct (seg_amq HTOP X R U L s m1 Rg rom sp0 K sp0 can _ _ _ _ _ _ F1 C1 Hi Hf Hc Mpg1) as (Rq & Hms2 & Q8 & Fq & Kq).
  pose proof C1 as [_ _ N1 _ _ _ _].
  assert (Mac : rdn SEGS m1 (wa (0 + 621760)) 8 = Some (word_to_le_bytes 8 (wa 0))).
  { pose proof (nc_ctx_rd L s m1 sp0 K (MCell (LCtx CTX_avail_meta_area_count) 8 (VZ (st_avail_meta_area_count s))) N1 ltac:(in_ctx13)
                  ltac:(intros z E; discriminate E) ltac:(cbn; lia)) as H. cbn [mc_loc mc_w mc_val loc_addr sval_num] in H. rewrite Hctx, Hac in H. exact H. }
  assert (Mbk : rdn SEGS m1 (wa (0 + 622640)) 8 = Some (word_to_le_bytes 8 (wa 18446744073709551615))).
  { pose proof (nc_ctx_rd L s m1 sp0 K (MCell (LCtx CTX_brk) 8 (match st_brk s with BrkNever => VZ 0 | BrkDead => VZ (-1) | BrkCur r p => VP (SP r (PGSZ * p)) end))
                  N1 ltac:(in_ctx13) ltac:(rewrite Hb; intros z E; discriminate E) ltac:(cbn; lia)) as H.
    cbn [mc_loc mc_w mc_val loc_addr] in H. rewrite Hctx, Hb in H. cbn [sval_num] in H. rewrite (wa_mod64 (-1)) in H. exact H. }
  set (av := sval_num L (if (match st_areas s with [] => true | _ => false end) && (st_avail_meta_area_count s =? 0) then VZ 0 else VP (st_avail_meta_areas s))).
  assert (Mar : rdn SEGS m1 (wa (0 + 621792)) 8 = Some (word_to_le_bytes 8 (wa (av mod 2^64)))).
  { pose proof (nc_ctx_rd L s m1 sp0 K (MCell (LCtx CTX_avail_meta_areas) 8
        (if (match st_areas s with [] => true | _ => false end) && (st_avail_meta_area_count s =? 0) then VZ 0 else VP (st_avail_meta_areas s)))
                  N1 ltac:(in_ctx13) ltac:(destruct (_ && _); intros z E; discriminate E) ltac:(cbn; lia)) as H.
    cbn [mc_loc mc_w mc_val loc_addr] in H. rewrite Hctx in H. fold av in H. rewrite (wa_mod64 av) in H. exact H. }
  assert (Msh : rdn SEGS m1 (wa (0 + 621768)) 8 = Some (word_to_le_bytes 8 (wa (st_meta_alloc_shift s)))).
  { pose proof (nc_ctx_rd L s m1 sp0 K (MCell (LCtx CTX_meta_alloc_shift) 8 (VZ (st_meta_alloc_shift s))) N1 ltac:(in_ctx13)
                  ltac:(intros z E; discriminate E) ltac:(cbn; lia)) as H. cbn [mc_loc mc_w mc_val loc_addr sval_num] in H. rewrite Hctx in H. exact H. }
  pose proof (inv_ctx HI) as CT. unfold ctx_ok in CT. destruct CT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Csh & _).
  pose proof (shift_le_34 X R U s HTOP L HI HG HD HTB) as S34.
  assert (Rar : 0 <= av mod 2^64 <= 2^64-1) by (pose proof (Z.mod_pos_bound av (2^64) ltac:(lia)); lia).
  assert (Rsh : 0 <= st_meta_alloc_shift s <= 34) by lia.
  destruct (seg_bdx Rq m1 rom sp0 can _ _ _ _ _ _ (av mod 2^64) (st_meta_alloc_shift s) Fq Q8 Mac Mbk Rar Mar Rsh Msh)
    as (Rm & Hms3 & A1 & A2 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A18 & A19 & A20 & Kb).
  apply (wk_msteps SEGS FORB HTOP rom _ _ _ _ _ _ _ _ _ (msteps_trans SEGS _ _ _ Hms1 (msteps_trans SEGS _ _ _ Hms2 Hms3))).
  assert (Rra : bv_unsigned (getr regs 1) = ra) by (rewrite R1; apply u_wa_small; destruct Hra as [->| ->]; lia).
  assert (Fm : am_frame Rm m1 sp0 can ra (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
                 (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 20))).
  { rewrite <- Rra. apply (am_frame_regs Rq Rm m1 sp0 can _ _ _ _ _ _ Fq).
    - rewrite A2. exact (eq_sym (mf_R2 _ _ _ _ _ _ _ _ _ _ Fq)).
    - rewrite A18. exact (eq_sym (mf_R18 _ _ _ _ _ _ _ _ _ _ Fq)).
    - rewrite A19. exact (eq_sym (mf_R19 _ _ _ _ _ _ _ _ _ _ Fq)). }
  apply (wk_resv_tail HTOP X R U L s m regs L s m1 Rm rom sp0 K can ra K1 K2 C1 G1 HK Fm R1 R2 Hra A1 A8 A9 A10 A11 A12 A13 A14 A15 A20); try assumption.
  intros k Hk'. rewrite (Kb k Hk'). rewrite (Kq k ltac:(clear - Hk'; klist Hk')). exact (Kp1 k ltac:(clear - Hk'; klist Hk')).
Qed.
End WKD.
