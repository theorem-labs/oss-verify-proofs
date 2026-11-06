(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FPInv CatExec StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac RegsEquiv Bridge.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface HIfaceInit.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfKf.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngOwn MngL4.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngRz2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section I.
Variable HTOP : Z.

(* [comment removed for export] *)
#[using="Type"] Theorem heap_initI : forall (L : layout) can auxv rnd typs m md,
  ly_ctx L = 0x95ed8 -> 2^20 <= HTOP -> env m can -> KRO m -> page_env m -> init_env L m auxv rnd typs ->
  0x97000 <= auxv -> 0x97000 <= rnd ->
  MngRz2.LINK HTOP FORB_P L (MallocWfKf.kf_of init_state) md ->
  (forall x, 0x95ed8 <= x < 0x96278 -> bview SEGS m x = Some 0) ->
  exists hs0, HeapI HTOP hs0 m md /\ blocks hs0 = [] /\ hs_L hs0 = L /\ hs_s hs0 = init_state /\ hs_can hs0 = can /\
              hs_auxv hs0 = auxv /\ hs_rnd hs0 = rnd /\ hs_typs hs0 = typs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L can auxv rnd typs m md Hctx HT Henv Hkro Hpg Hini Ha Hr HLk HZ.
  exists (mkHS L init_state can auxv rnd typs).
  split; [|split; [unfold blocks; cbn [hs_s]; rewrite user_blocks_init; reflexivity | repeat split]].
  constructor; cbn [hs_L hs_s hs_can hs_auxv hs_rnd hs_typs]; try assumption.
  - reflexivity.
  - exact (heap0_init L m Hctx HZ).
  - exact (LINKv_of HTOP L init_state md HLk).
  - split; assumption.
Qed.

#[using="Type"] Lemma HeapI_blocks : forall hs m md, HeapI HTOP hs m md -> blocks hs = [].
Proof. LiaFast.lf_pins LiaFast.u0. intros hs m md HP. unfold blocks. rewrite (hq_s HTOP hs m md HP). rewrite user_blocks_init. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma HeapI_HAP : forall hs m md, HeapI HTOP hs m md ->
  forall rg, In rg (footprint (hs_s hs)) -> fst rg <> LCtx 0 -> ranges_disjoint (crange (hs_L hs) rg) (0x10000, 0x87000).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hs m md HP rg Hrg E. rewrite (hq_s HTOP hs m md HP) in Hrg. rewrite footprint_init in Hrg.
  destruct Hrg as [<-|[]]. exfalso. apply E. reflexivity.
Qed.

#[using="Type"] Lemma HeapI_b1 : forall hs m md, HeapI HTOP hs m md -> forall b, In b (user_blocks (hs_s hs)) -> 1 <= snd b.
Proof. LiaFast.lf_pins LiaFast.u0. intros hs m md HP b Hb. rewrite (hq_s HTOP hs m md HP) in Hb. rewrite user_blocks_init in Hb. destruct Hb. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma init_env_kept : forall L m m' auxv rnd typs,
  init_env L m auxv rnd typs ->
  (forall x, 613992 <= x < 614000 -> m' (wa x) = m (wa x)) ->
  (forall x, auxv <= x < auxv + 16 * Z.of_nat (length typs) + 8 -> m' (wa x) = m (wa x)) ->
  (forall x, rnd + 8 <= x < rnd + 16 -> m' (wa x) = m (wa x)) ->
  init_env L m' auxv rnd typs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L m m' auxv rnd typs (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11) K1 K2 K3.
  split; [rewrite (rdn_frame m m') by (first [lia | intros x Hx; apply K1; cbn in Hx; lia]); exact A1|].
  split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
  split.
  { intros i Hi. destruct (A5 i Hi) as (T1 & T2 & T3). split; [exact T1|]. split.
    - rewrite (rdn_frame m m') by (first [lia | intros x Hx; apply K2; cbn in Hx; lia]). exact T2.
    - intros E. rewrite (rdn_frame m m') by (first [lia | intros x Hx; apply K2; cbn in Hx; lia]). exact (T3 E). }
  split; [rewrite (rdn_frame m m') by (first [lia | intros x Hx; apply K2; cbn in Hx; lia]); exact A6|].
  split; [exact A7|]. split; [exact A8|]. split; [exact A9|]. split; [exact A10|].
  rewrite (rdn_frame m m') by (first [lia | intros x Hx; apply K3; cbn in Hx; lia]). exact A11.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem heap_frame_init_L4 : heap_frame_init SEGS HS owned (HeapI HTOP) INIT.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hs m m' md W HP MU Hwm HWo.
  pose proof HP as [Hs H0 Hctx Henv Hkro Hled HT20 Hpg Hini Himg].
  assert (KO : forall x, 0 <= x < 2^64 -> (~ outside (owned hs) x \/ ~ outside (INIT hs) x) -> m' (wa x) = m (wa x)).
  { intros x Hx Ho. apply MU. rewrite u_wa_small by exact Hx.
    destruct (outside_dec W x) as [A|A]; [exact A|]. exfalso. destruct (HWo x A) as (B1 & B2). destruct Ho as [Ho|Ho]; [exact (Ho B1) | exact (Ho B2)]. }
  destruct (core_kept hs m m' H0 Hctx Henv Hkro Hpg (HeapI_HAP hs m md HP) (HeapI_b1 hs m md HP) Hwm
              (fun x Hx Ho _ => KO x Hx (or_introl Ho))) as (H0' & Henv' & Hkro' & Hpg').
  pose proof Hini as (_ & B2 & _ & B4 & _ & _ & _ & B8 & _ & B10 & _).
  constructor; try assumption.
  apply (init_env_kept (hs_L hs) m m' _ _ _ Hini).
  - intros x Hx. apply KO; [lia|]. left. apply owned_static. unfold STATIC_P, ERRNO. cbn [outside]. lia.
  - intros x Hx. apply KO; [lia|]. right. unfold INIT. cbn [outside]. lia.
  - intros x Hx. apply KO; [lia|]. right. unfold INIT. cbn [outside]. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem heapI_need_locks : forall hs m md, HeapI HTOP hs m md -> rdn SEGS m (wa 0x95e63) 1 = Some [Z_to_bv 8 0].
Proof. LiaFast.lf_pins LiaFast.u0. intros hs m md HP. destruct HP as [_ _ _ (E1 & _) _ _ _ _ _ _]. exact E1. Qed.

#[using="Type"] Theorem heapI_model_vm : forall hs m md md', HeapI HTOP hs m md -> m_vmmaps md' = m_vmmaps md -> HeapI HTOP hs m md'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hs m md md' HP E. destruct HP as [Hs H0 Hctx Henv Hkro Hled HT20 Hpg Hini Himg].
  constructor; try assumption.
  intros md0 E0 Hh Hl. apply Hled; [rewrite E0, E; reflexivity | exact Hh | exact Hl].
Qed.

#[using="Type"] Theorem heapI_errno_frame : forall hs m m' md, HeapI HTOP hs m md -> munch [(ERRNO, ERRNO + 4)] m m' -> mem_grows m m' ->
  HeapI HTOP hs m' md.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hs m m' md HP MU Hwm. pose proof HP as [Hs H0 Hctx Henv Hkro Hled HT20 Hpg Hini Himg].
  assert (KE : forall x, 0 <= x < 2^64 -> ~ (ERRNO <= x < ERRNO + 4) -> m' (wa x) = m (wa x)).
  { intros x Hx He. apply MU. rewrite u_wa_small by exact Hx. cbn [outside]. split; [lia | exact I]. }
  destruct (core_kept hs m m' H0 Hctx Henv Hkro Hpg (HeapI_HAP hs m md HP) (HeapI_b1 hs m md HP) Hwm
              (fun x Hx _ He => KE x Hx He)) as (H0' & Henv' & Hkro' & Hpg').
  pose proof Hini as (_ & B2 & _ & B4 & _ & _ & _ & B8 & _ & B10 & _).
  constructor; try assumption.
  apply (init_env_kept (hs_L hs) m m' _ _ _ Hini).
  - intros x Hx. apply KE; [lia | unfold ERRNO; lia].
  - intros x Hx. apply KE; [lia|]. unfold ERRNO. lia.
  - intros x Hx. apply KE; [lia|]. unfold ERRNO. lia.
Qed.

#[using="Type"] Theorem heapI_cells_frame : forall hs m m' md, HeapI HTOP hs m md ->
  munch [(0x63da0, 0x63da8); (0x95e40, 0x95e48)] m m' -> mem_grows m m' ->
  (forall a, 0x63da0 <= a < 0x63da8 \/ 0x95e40 <= a < 0x95e48 -> mrd SEGS m' (wa a) = mrd SEGS m (wa a)) -> HeapI HTOP hs m' md.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hs m m' md HP MU Hwm Hv. pose proof HP as [Hs H0 Hctx Henv Hkro Hled HT20 Hpg Hini Himg].
  assert (KE : forall x, 0 <= x < 2^64 -> ~ (0x63da0 <= x < 0x63da8) -> ~ (0x95e40 <= x < 0x95e48) -> m' (wa x) = m (wa x)).
  { intros x Hx H1 H2. apply MU. rewrite u_wa_small by exact Hx. cbn [outside]. tauto. }
  destruct (core_cells hs m m' H0 Hctx Henv Hkro Hpg (HeapI_HAP hs m md HP) MU Hwm Hv) as (H0' & Henv' & Hkro' & Hpg').
  pose proof Hini as (_ & B2 & _ & B4 & _ & _ & _ & B8 & _ & B10 & _).
  constructor; try assumption.
  apply (init_env_kept (hs_L hs) m m' _ _ _ Hini).
  - intros x Hx. apply KE; lia.
  - intros x Hx. apply KE; lia.
  - intros x Hx. apply KE; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem heapI_owned : forall hs m md, HeapI HTOP hs m md -> forall x, ~ outside (owned hs) x ->
  0 <= x < HTOP /\ (~ outside STATIC_P x \/ x < 0x10000 \/ 0x97000 <= x).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hs m md HP x Ho. pose proof HP as [Hs H0 Hctx Henv Hkro Hled HT20 Hpg Hini Himg].
  assert (HS0 : ~ outside STATIC_P x).
  { intros HSo. apply Ho. unfold owned. apply outside_app2. split.
    2:{ apply outside_app2. split; [exact HSo|]. unfold regs_ivl. rewrite Hs. cbn. exact I. }
    rewrite outside_filter, outside_flat_map. intros rg Hrg. rewrite Hs, footprint_init in Hrg. destruct Hrg as [<-|[]].
    rewrite (HeapI_blocks hs m md HP). unfold fivl. cbn [carve fst snd loc_addr]. rewrite Hctx.
    unfold STATIC_P in HSo. cbn [outside] in HSo |- *. unfold CTX_SIZE. tauto. }
  pose proof (static_in_image x HS0). split; [lia | left; exact HS0].
Qed.

End I.
