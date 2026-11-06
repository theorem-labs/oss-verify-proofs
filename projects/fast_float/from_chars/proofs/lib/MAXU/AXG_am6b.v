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
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ MngNtfM MngNtfS MngMWP MngMW0 MngMW1 MngShift AXG_am1 AXG_am3 AXG_am4 AXG_am5 AXG_am6 AXG_am7.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition s_bcg (s : astate) (r : nat) (p : Z) (rg : region) : astate :=
  set_brk (BrkCur r (p + 1)) (set_avail_meta_areas (SP r (PGSZ * p)) (set_avail_meta_area_count 1
    (set_regions (lupd (st_regions s) r (mkRegion RkBrk (rg_len rg + PGSZ) [] true)) s))).

Lemma alloc_meta_bc : forall s r p rg, st_init_done s = true -> st_free_meta_head s = None -> st_avail_meta_count s = 0 ->
  st_avail_meta_area_count s = 0 -> st_brk s = BrkCur r p -> region_of s r = Some rg ->
  exists Kb K1 K2, alloc_meta s = IAsk (KBrkGrow 1) s Kb /\
    Kb 1 = IRet (Some (padd (SP r (PGSZ * p)) AREA_HDR), s_opn (SP r (PGSZ * p)) (s_bcg s r p rg)) /\
    Kb 0 = IAsk (KMmapNone (Z.shiftl 2 (st_meta_alloc_shift s) * PGSZ)) (set_brk BrkDead s) K1 /\
    K1 1 = IAsk (KMprotect (SP (length (st_regions s)) PGSZ)) (s_resv (set_brk BrkDead s)) K2 /\
    K2 1 = IRet (Some (padd (SP (length (st_regions s)) PGSZ) AREA_HDR),
                 s_opn (SP (length (st_regions s)) PGSZ) (s_res1 (s_resv (set_brk BrkDead s)) (length (st_regions s)) (rg_resv (set_brk BrkDead s)) PGSZ)).
Proof.
  intros s r p rg Hi Hf Hc Hac Hb Hr. do 3 eexists. split; [|split; [|split; [|split]]].
  - unfold alloc_meta. cbn. rewrite set_init_done_same by exact Hi. rewrite Hf. cbn. rewrite Hc. cbn.
    unfold area_from_brk. cbn. rewrite Hac, Hb. cbn. reflexivity.
  - cbn. unfold region_of in Hr. rewrite (nth_of_nth_error' _ _ _ _ Hr).
    unfold ret, s_opn, s_take, open_st, s_bcg. cbn. reflexivity.
  - cbn. unfold area_from_mmap. cbn. rewrite Hac. cbn. reflexivity.
  - cbn. reflexivity.
  - cbn. unfold s_resv, rg_resv. cbn. rewrite nth_middle.
    unfold ret, s_opn, s_take, open_st, s_res1, rw_page. cbn. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition brk_cell (v : sval) : mcell := MCell (LCtx CTX_brk) 8 v.

Lemma dead_cov_ctx : forall s c, In c (ctx_cells (set_brk BrkDead s)) -> In c (ctx_cells s) \/ c = brk_cell (VZ (-1)).
Proof.
  intros s c Hc. unfold ctx_cells in Hc.
  cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count
      st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_seq st_brk st_active st_usage
      st_unmap_seq st_bounces set_brk] in Hc.
  apply in_app_iff in Hc as [Hc|Hc]; [|left; unfold ctx_cells; apply in_app_iff; right; exact Hc].
  cbn [In] in Hc.
  repeat (destruct Hc as [<-|Hc]; [first [ (left; unfold ctx_cells; apply in_app_iff; left; cbn [In]; solve [memb])
                                        | (right; reflexivity) ] |]).
  destruct Hc.
Qed.

Lemma dead_rev_ctx : forall s c, In c (ctx_cells s) ->
  In c (ctx_cells (set_brk BrkDead s)) \/ (mc_loc c = LCtx CTX_brk /\ mc_w c = 8%nat).
Proof.
  intros s c Hc. unfold ctx_cells in Hc.
  apply in_app_iff in Hc as [Hc|Hc]; [|left; unfold ctx_cells; apply in_app_iff; right; exact Hc].
  cbn [In] in Hc.
  repeat (destruct Hc as [<-|Hc]; [first [ (left; unfold ctx_cells; apply in_app_iff; left;
       cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count
            st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_seq st_brk set_brk In]; solve [memb])
     | (right; split; reflexivity) ] |]).
  destruct Hc.
Qed.

Lemma dead_areas_cells : forall s l, areas_cells (set_brk BrkDead s) l = areas_cells s l.
Proof. intros s l. apply areas_cells_ext. intros q. reflexivity. Qed.

Lemma dead_cov : forall s c, In c (image (set_brk BrkDead s)) -> In c (image s) \/ c = brk_cell (VZ (-1)).
Proof.
  intros s c Hc. unfold image in Hc. apply in_app_iff in Hc as [Hc|Hc].
  - destruct (dead_cov_ctx s c Hc) as [H|H]; [left; apply ctx_in_image; exact H | right; exact H].
  - left. unfold image. apply in_app_iff. right. replace (st_areas (set_brk BrkDead s)) with (st_areas s) in Hc by reflexivity.
    rewrite dead_areas_cells in Hc. exact Hc.
Qed.

Lemma dead_rev : forall s c, In c (image s) -> In c (image (set_brk BrkDead s)) \/ (mc_loc c = LCtx CTX_brk /\ mc_w c = 8%nat).
Proof.
  intros s c Hc. unfold image in Hc. apply in_app_iff in Hc as [Hc|Hc].
  - destruct (dead_rev_ctx s c Hc) as [H|H]; [left; apply ctx_in_image; exact H | right; exact H].
  - left. unfold image. apply in_app_iff. right. replace (st_areas (set_brk BrkDead s)) with (st_areas s) by reflexivity.
    rewrite dead_areas_cells. exact Hc.
Qed.

Lemma dead_in : forall s, In (brk_cell (VZ (-1))) (image (set_brk BrkDead s)).
Proof.
  intros s. apply ctx_in_image. unfold ctx_cells. apply in_app_iff. left.
  cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count
       st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_seq st_brk set_brk In]. solve [memb].
Qed.

Theorem cut_dead : forall HTOP X R U L s m sp0 K, CUT HTOP X R U L s m sp0 K -> st_brk s <> BrkDead -> st_init_done s = true ->
  CUT HTOP X R U L (set_brk BrkDead s) (wbytes m (wa (0 + 622640)) (word_to_le_bytes 8 (wa 18446744073709551615))) sp0 K /\
  GROW sp0 K L s m L (set_brk BrkDead s) (wbytes m (wa (0 + 622640)) (word_to_le_bytes 8 (wa 18446744073709551615))).
Proof.
  intros HTOP X R U L s m sp0 K C Hb Hi. pose proof C as [HI HX N HG HD HT HTB]. pose proof (nc_ctx _ _ _ _ _ _ _ N) as Hctx.
  assert (EQ : loc_addr L (LCtx CTX_brk) = 622640) by (cbn [loc_addr]; rewrite Hctx; reflexivity).
  apply (silent_step' HTOP X R U X R U L s (set_brk BrkDead s) m _ sp0 K [brk_cell (VZ (-1))] C).
  - exact (Inv_brk_dead X R U s HI Hb Hi).
  - exact HX.
  - exact HG.
  - exact HD.
  - exact (RMONO_refl s).
  - intros rg Hrg. left. exact Hrg.
  - intros c Hc. destruct (dead_cov s c Hc) as [H|H]; [left; exact H | right; cbn [In]; left; symmetry; exact H].
  - intros c [<-|[]]. exact (dead_in s).
  - intros c Hc. destruct (dead_rev s c Hc) as [H|(Hl & Hw)]; [left; exact H | right].
    exists (brk_cell (VZ (-1))). split; [left; reflexivity|]. unfold cell_range. rewrite Hl, Hw. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    replace (wa (0 + 622640)) with (wa (loc_addr L (mc_loc (brk_cell (VZ (-1)))))) by (cbn [mc_loc brk_cell]; rewrite EQ; reflexivity).
    refine (holds_wb L m (brk_cell (VZ (-1))) 18446744073709551615 _ _ _ _ _);
      cbn [mc_val mc_w mc_loc brk_cell]; rewrite ?EQ; first [ (intros z E; discriminate E) | lia | reflexivity ].
  - apply wbytes_grows.
  - intros x Hx Hne. right. exists (brk_cell (VZ (-1))). split; [left; reflexivity|].
    unfold in_rng, cell_range. cbn [brk_cell mc_loc mc_w fst snd]. rewrite EQ. cbn [Z.of_nat Pos.of_succ_nat].
    destruct (range_dec x 622640 8) as [I|I]; [lia|]. exfalso. apply Hne. rewrite MngWb.wbytes_out by side. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WKB.
Context {fx : FPState}.
Variable FORB : list (Z * Z).
Hypothesis HFORB : forall a n, 0 < n -> Forall (fun r => ranges_disjoint (a, n) r) FORB -> ranges_disjoint (a, n) (0x10000, 0x89000).
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

#[using="HFORB WOR"] Theorem wk_bc_ref : forall HTOP X R U L0 s0 m0 (regs0 : bvmap 5 word) L s m Rq rom sp0 K can ra K1 K2 res nb,
  CUT HTOP X R U L s m sp0 K -> GROW sp0 K L0 s0 m0 L s m -> 1152 <= K ->
  am_frame Rq m sp0 can ra (bv_unsigned (getr regs0 8)) (bv_unsigned (getr regs0 9))
    (bv_unsigned (getr regs0 18)) (bv_unsigned (getr regs0 19)) (bv_unsigned (getr regs0 20)) ->
  getr regs0 1 = wa ra -> getr regs0 2 = wa sp0 -> (ra = 0x542a0 \/ ra = 0x53ec4) ->
  getr Rq 8 = wa 4096 -> getr Rq 9 = wa nb -> getr Rq 10 = wa res -> 0 <= res <= 2^64-1 -> 8192 <= nb <= 2^47 -> res <> nb ->
  (forall k, In k [3;4;21;22;23;24;25;26;27]%nat -> getr Rq (Z_to_bv 5 (Z.of_nat k)) = getr regs0 (Z_to_bv 5 (Z.of_nat k))) ->
  st_init_done s = true -> st_free_meta_head s = None -> st_avail_meta_count s = 0 -> st_avail_meta_area_count s = 0 ->
  st_brk s <> BrkDead ->
  rdn SEGS m (wa 621648) 8 = Some (word_to_le_bytes 8 (wa 4096)) ->
  K1 1 = IAsk (KMprotect (SP (length (st_regions s)) PGSZ)) (s_resv (set_brk BrkDead s)) K2 ->
  K2 1 = IRet (Some (padd (SP (length (st_regions s)) PGSZ) AREA_HDR),
               s_opn (SP (length (st_regions s)) PGSZ) (s_res1 (s_resv (set_brk BrkDead s)) (length (st_regions s)) (rg_resv (set_brk BrkDead s)) PGSZ)) ->
  wk SEGS FORB HTOP rom L Rq (wa 0x53b90) m (IAsk (KMmapNone (Z.shiftl 2 (st_meta_alloc_shift s) * PGSZ)) (set_brk BrkDead s) K1)
     (am_qpost HTOP X R U L0 s0 m0 regs0 sp0 K ra).
Proof. LiaFast.lf_pins (fun (HFORB WOR : LiaFast.U) => LiaFast.u0).
  intros HTOP X R U L0 s0 m0 regs0 L s m Rq rom sp0 K can ra K1 K2 res nb C G0 HK Fq R1 R2 Hra Q8 Q9 Q10 Rres Rnb Hne KA
    Hi Hf Hc Hac Hb Mpg EK1 EK2.
  pose proof C as [HI HX N HG HD HT HTB]. pose proof (nc_ctx _ _ _ _ _ _ _ N) as Hctx. pose proof (nc_sp1 _ _ _ _ _ _ _ N) as Hsp1.
  pose proof (nc_sp2 _ _ _ _ _ _ _ N) as Hsp2.
  pose proof (inv_ctx HI) as CT. unfold ctx_ok in CT. destruct CT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Csh & _).
  pose proof (shift_le_34 X R U s HTOP L HI HG HD HTB) as S34.
  assert (M3 : rdn SEGS m (wa (0 + 621760)) 8 = Some (word_to_le_bytes 8 (wa 0))).
  { pose proof (nc_ctx_rd L s m sp0 K (MCell (LCtx CTX_avail_meta_area_count) 8 (VZ (st_avail_meta_area_count s))) N ltac:(in_ctx13)
                  ltac:(intros z E; discriminate E) ltac:(cbn; lia)) as H. cbn [mc_loc mc_w mc_val loc_addr sval_num] in H. rewrite Hctx, Hac in H. exact H. }
  assert (M4 : rdn SEGS m (wa (0 + 621768)) 8 = Some (word_to_le_bytes 8 (wa (st_meta_alloc_shift s)))).
  { pose proof (nc_ctx_rd L s m sp0 K (MCell (LCtx CTX_meta_alloc_shift) 8 (VZ (st_meta_alloc_shift s))) N ltac:(in_ctx13)
                  ltac:(intros z E; discriminate E) ltac:(cbn; lia)) as H. cbn [mc_loc mc_w mc_val loc_addr sval_num] in H. rewrite Hctx in H. exact H. }
  assert (W5 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 622640 + d)) k = true).
  { intros d k Hd Hk. pose proof (nc_ctx_wr L s m sp0 K (MCell (LCtx CTX_brk) 8 (match st_brk s with BrkNever => VZ 0 | BrkDead => VZ (-1) | BrkCur r p => VP (SP r (PGSZ * p)) end))
      N ltac:(in_ctx13) ltac:(destruct (st_brk s); intros z E; discriminate E) d k Hd ltac:(cbn [mc_w]; lia)) as W.
    cbn [mc_loc loc_addr] in W. rewrite Hctx in W. exact W. }
  assert (W6 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 621760 + d)) k = true).
  { intros d k Hd Hk. exact (nc_acsh_wr L s m sp0 K d k N Hd ltac:(lia)). }
  destruct (seg_bcr Rq m rom res nb (st_meta_alloc_shift s) Q8 Q9 Q10 (mf_R19 _ _ _ _ _ _ _ _ _ _ Fq) Rres Rnb Hne ltac:(lia) M3 M4 W5 W6)
    as (Rm & Hms & A1 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A19 & A20 & Km).
  apply (wk_msteps SEGS FORB HTOP rom _ _ _ _ _ _ _ _ _ Hms).
  set (m2 := wbytes m (wa (0 + 622640)) (word_to_le_bytes 8 (wa 18446744073709551615))).
  destruct (cut_dead HTOP X R U L s m sp0 K C Hb Hi) as (C2 & G2). fold m2 in C2, G2.
  assert (MF : forall x, sp0 - 56 <= x < sp0 \/ 621568 <= x < 621576 -> m2 (wa x) = m (wa x))
    by (intros x Hx; unfold m2; rewrite MngWb.wbytes_out by side; reflexivity).
  assert (Fm : am_frame Rm m2 sp0 can ra (bv_unsigned (getr regs0 8)) (bv_unsigned (getr regs0 9))
                 (bv_unsigned (getr regs0 18)) (bv_unsigned (getr regs0 19)) (bv_unsigned (getr regs0 20))).
  { apply (am_frame_mem Rm m); [| intros x Hx; apply MF; lia | intros x Hx; apply MF; lia].
    apply (am_frame_regs Rq Rm m sp0 can _ _ _ _ _ _ Fq).
    - regk Km 2%nat. reflexivity.
    - regk Km 18%nat. reflexivity.
    - rewrite A19. exact (eq_sym (mf_R19 _ _ _ _ _ _ _ _ _ _ Fq)). }
  assert (Mpg2 : rdn SEGS m2 (wa 621648) 8 = Some (word_to_le_bytes 8 (wa 4096))).
  { rewrite (rdn_frame_n m m2) by (try lia; intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; unfold m2; rewrite MngWb.wbytes_out by side; reflexivity). exact Mpg. }
  apply (wk_resv_tail FORB HFORB WOR HTOP X R U L0 s0 m0 regs0 L (set_brk BrkDead s) m2 Rm rom sp0 K can ra K1 K2 C2
           (GROW_trans sp0 K L0 s0 m0 L s m _ _ _ G0 G2) HK Fm R1 R2 Hra A1 A8 A9 A10 A11 A12 A13 A14 A15 A20).
  - intros k Hk'. rewrite (Km k ltac:(clear - Hk'; klist Hk')). exact (KA k Hk').
  - exact Hi.
  - exact Hf.
  - exact Hc.
  - exact Hac.
  - exact Mpg2.
  - exact EK1.
  - exact EK2.
Qed.
End WKB.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bcg_cov_ctx : forall s r p rg c, In c (ctx_cells (s_bcg s r p rg)) ->
  In c (ctx_cells s) \/ c = brk_cell (VP (SP r (PGSZ * (p + 1)))) \/ c = ac_cell 1 \/ c = ama_cell (SP r (PGSZ * p)).
Proof.
  intros s r p rg c Hc. unfold s_bcg, ctx_cells in Hc.
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

Lemma bcg_rev_ctx : forall s r p rg c, In c (ctx_cells s) ->
  In c (ctx_cells (s_bcg s r p rg)) \/ ((mc_loc c = LCtx CTX_brk \/ mc_loc c = LCtx CTX_avail_meta_area_count \/
     mc_loc c = LCtx CTX_avail_meta_areas) /\ mc_w c = 8%nat).
Proof.
  intros s r p rg c Hc. unfold ctx_cells in Hc.
  apply in_app_iff in Hc as [Hc|Hc]; [|left; unfold ctx_cells; apply in_app_iff; right; exact Hc].
  cbn [In] in Hc.
  repeat (destruct Hc as [<-|Hc]; [first [ (left; unfold ctx_cells, s_bcg; apply in_app_iff; left;
       cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count
            st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_seq st_brk
            set_brk set_avail_meta_areas set_avail_meta_area_count set_regions In]; rewrite ?andb_false_r; solve [memb])
     | (right; split; [cbn [mc_loc]; first [ (left; reflexivity) | (right; left; reflexivity) | (right; right; reflexivity) ] | reflexivity]) ] |]).
  destruct Hc.
Qed.

Lemma bcg_areas_cells : forall s r p rg l, areas_cells (s_bcg s r p rg) l = areas_cells s l.
Proof. intros. apply areas_cells_ext. intros q. reflexivity. Qed.

Lemma bcg_cov : forall s r p rg c, In c (image (s_bcg s r p rg)) ->
  In c (image s) \/ c = brk_cell (VP (SP r (PGSZ * (p + 1)))) \/ c = ac_cell 1 \/ c = ama_cell (SP r (PGSZ * p)).
Proof.
  intros s r p rg c Hc. unfold image in Hc. apply in_app_iff in Hc as [Hc|Hc].
  - destruct (bcg_cov_ctx s r p rg c Hc) as [H|H]; [left; apply ctx_in_image; exact H | right; exact H].
  - left. unfold image. apply in_app_iff. right. replace (st_areas (s_bcg s r p rg)) with (st_areas s) in Hc by reflexivity.
    rewrite bcg_areas_cells in Hc. exact Hc.
Qed.

Lemma bcg_rev : forall s r p rg c, In c (image s) ->
  In c (image (s_bcg s r p rg)) \/ ((mc_loc c = LCtx CTX_brk \/ mc_loc c = LCtx CTX_avail_meta_area_count \/
     mc_loc c = LCtx CTX_avail_meta_areas) /\ mc_w c = 8%nat).
Proof.
  intros s r p rg c Hc. unfold image in Hc. apply in_app_iff in Hc as [Hc|Hc].
  - destruct (bcg_rev_ctx s r p rg c Hc) as [H|H]; [left; apply ctx_in_image; exact H | right; exact H].
  - left. unfold image. apply in_app_iff. right. replace (st_areas (s_bcg s r p rg)) with (st_areas s) by reflexivity.
    rewrite bcg_areas_cells. exact Hc.
Qed.

Lemma bcg_cells_in : forall s r p rg,
  In (brk_cell (VP (SP r (PGSZ * (p + 1))))) (image (s_bcg s r p rg)) /\ In (ac_cell 1) (image (s_bcg s r p rg)) /\
  In (ama_cell (SP r (PGSZ * p))) (image (s_bcg s r p rg)).
Proof.
  intros s r p rg. split; [|split]; apply ctx_in_image; unfold ctx_cells, s_bcg; apply in_app_iff; left;
    cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count
         st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_seq st_brk
         set_brk set_avail_meta_areas set_avail_meta_area_count set_regions In]; rewrite ?andb_false_r; solve [memb].
Qed.

(* [comment removed for export] *)
Lemma bcg_ctx_loc : forall s r p rg c o, In c (image (s_bcg s r p rg)) -> mc_loc c = LCtx o ->
  (o = CTX_brk -> c = brk_cell (VP (SP r (PGSZ * (p + 1))))) /\ (o = CTX_avail_meta_area_count -> c = ac_cell 1).
Proof.
  intros s r p rg c o Hc Hl. pose proof (lctx_in_ctx _ c o Hc Hl) as Hx. clear Hc.
  unfold ctx_cells, s_bcg in Hx.
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

Lemma region_of_bcg : forall s r p rg k rgk, region_of s r = Some rg -> region_of (s_bcg s r p rg) k = Some rgk ->
  (k = r /\ rgk = mkRegion RkBrk (rg_len rg + PGSZ) [] true) \/ (k <> r /\ region_of s k = Some rgk).
Proof.
  intros s r p rg k rgk Hr H. unfold region_of, s_bcg in *. cbn [st_regions set_brk set_avail_meta_areas set_avail_meta_area_count set_regions] in H.
  destruct (MngRz2.nth_lupd_cases _ r _ k rgk H) as [(-> & -> & _)|(Hne & H')]; [left; auto | right; auto].
Qed.

Lemma bcg_footprint : forall s r p rg f, region_of s r = Some rg -> rg_kind rg = RkBrk -> In f (footprint (s_bcg s r p rg)) -> In f (footprint s).
Proof.
  intros s r p rg f Hr Hkd H. unfold footprint in *. destruct H as [H|H]; [left; exact H|]. right.
  apply in_app_iff in H as [H|H]; [apply in_app_iff; left; exact H|]. apply in_app_iff. right.
  apply in_flat_map in H as (k & Hk & Hin). apply in_flat_map. exists k.
  replace (length (st_regions (s_bcg s r p rg))) with (length (st_regions s)) in Hk
    by (unfold s_bcg; cbn [st_regions set_brk set_avail_meta_areas set_avail_meta_area_count set_regions]; rewrite length_lupd; reflexivity).
  split; [exact Hk|].
  destruct (region_of (s_bcg s r p rg) k) as [rgk|] eqn:E; [|destruct Hin].
  destruct (region_of_bcg s r p rg k rgk Hr E) as [(-> & ->)|(_ & E')]; [cbn in Hin; destruct Hin | rewrite E'; exact Hin].
Qed.
