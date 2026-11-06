(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from parts of lib/DGif0.v (DMspec's drain leaf / contract as DIface takes it, DMiface.di_rchunk_t), lib/DIfaceR.v (drain_leaf_g / drain_spec_g, dr_rchunk_t, DIfaceR, drain_spec_b, dealloc_leaf_b) and lib/MnRecycle.v (de_rchunk_m_t, MnDrain.de_drain_m_t, DIfaceREm), each restated over YG0dH.amreal' at YGcfRehidePost.RZ_cf with YGcfRehidePost's re-hide posts (acall_post_x_rh, dealloc_post_rh); every other conjunct is unchanged, and each twin has its [_rh_of] weakening from the released statement. *)
(* F1 priming row R3 (re-hide at a secondary recycle): the re-hide twins of the drain / Recycle / Deallocate
   contracts.  QuarantineCallback::Recycle's secondary arm hides the dead shadow hull's interior at its return
   (YA0nR.SRr'_rehide_ret), so Recycle and every contract that binds across it (the drain, Deallocate's drain arm)
   are stated over YG0dH.amreal' at the fixed zone YGcfRehidePost.RZ_cf: the continuation world W' is existential,
   with wle' RZ_cf W W' (YA0nH.SRrG), and the call post is YGcfRehidePost.acall_post_x_rh (the hidden set grows only
   inside the post's exact dead set, and the view frame holds outside it) or, for Deallocate, YGcfRehidePost.dealloc_post_rh.
   Every other conjunct is unchanged: the raw frame, errno and memnorm are memory facts, and the re-hide step
   changes no memory.  Enqueue and CacheDealloc re-hide nothing; their released contracts stay as they are, with
   round 3 part 3's memory predicate MP at Put's call of Enqueue in the same place (DGif0.di_enqueue, DIfaceR.enq_spec_g).
   Each [_rh_of] gives the twin from the released statement (a walk that re-hides nothing): the lift
   YG0dH.amreal_amreal' and the post's weakening (acall_post_x_rh_of / dealloc_post_rh_of).
   A new file, so that DGif0.v / DIfaceR.v / MnRecycle.v and every consumer of them stay byte-unchanged: the twins
   need YGcfRehidePost, and loading it from those files changed how their consumers read the name ImgBase.
   rule 24: no function proved (kind: re-typing of existing contracts to the re-hide forms). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YG0dH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DeallocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG DGif0 DIfaceR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ErrnoG MemnormT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import MnEnq MnDrain MnRecycle.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg} {DI : DImg}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. The drain contract (DGif0.v's DMspec.drain_leaf_cf / drain_spec_cf).                                          *)
Section rh.
Variable B : asyms.
Variable ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable dbody : astate -> M unit.
Variable L24 : Z.
Variable QB : astate -> Prop.
(* DMspec.drain_leaf_cf at acall_post_x_rh. *)
Definition drain_leaf_cf_rh (inst : Z) (ly : alayout) (X : astate) (W : world im_segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model)
(r : unit * astate) (W' : world im_segs) (c' : config) : Prop :=
exists regs' mem' md',
c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
YGcfRehidePost.acall_post_x_rh B ARX AOX inst YFeuC.DSTACK ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md'.
(* DMspec.drain_spec_cf over amreal'. *)
Definition drain_spec_cf_rh : Prop :=
forall inst ly X W regs mem md,
drain_pre_cf B ARX L24 QB inst ly X W regs mem md ->
amreal' im_segs YGcfRehidePost.RZ_cf (dbody X X) W (cfg_at im_segs dg_drain regs mem md)
  (drain_leaf_cf_rh inst ly X W regs mem md).
Lemma drain_leaf_cf_rh_of : forall inst ly X W regs mem md r W' c',
drain_leaf_cf B ARX AOX inst ly X W regs mem md r W' c' -> drain_leaf_cf_rh inst ly X W regs mem md r W' c'.
Proof.
intros inst ly X W regs mem md r W' c' (regs' & mem' & md' & Hc & HP).
exists regs', mem', md'. split; [exact Hc|].
exact (YGcfRehidePost.acall_post_x_rh_of B ARX AOX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP).
Qed.
Lemma drain_spec_cf_rh_of : drain_spec_cf B ARX AOX dbody L24 QB -> drain_spec_cf_rh.
Proof.
intros H inst ly X W regs mem md PRE.
eapply amreal'_mono; [| exact (amreal_amreal' im_segs YGcfRehidePost.RZ_cf _ _ _ _ (H inst ly X W regs mem md PRE))].
intros r W' c' HL. exact (drain_leaf_cf_rh_of inst ly X W regs mem md r W' c' HL).
Qed.

(* DIfaceR.drain_leaf_g / drain_spec_g (the extra conjunct [XR] unchanged) at the twins. *)
Definition drain_leaf_g_rh (XR : fxrel) (inst : Z) (ly : alayout) (X : astate) (W : world im_segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model)
(r : unit * astate) (W' : world im_segs) (c' : config) : Prop :=
exists regs' mem' md',
c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
YGcfRehidePost.acall_post_x_rh B ARX AOX inst YFeuC.DSTACK ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
XR inst YFeuC.DSTACK ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md'.
Definition drain_spec_g_rh (XR : fxrel) : Prop :=
forall inst ly X W regs mem md,
drain_pre_cf B ARX L24 QB inst ly X W regs mem md ->
amreal' im_segs YGcfRehidePost.RZ_cf (dbody X X) W (cfg_at im_segs dg_drain regs mem md)
  (drain_leaf_g_rh XR inst ly X W regs mem md).
Definition drain_leaf_raw_cf_rh := drain_leaf_g_rh (acall_raw_x B AOX).
Definition drain_spec_raw_cf_rh : Prop := drain_spec_g_rh (acall_raw_x B AOX).

Lemma drain_leaf_g_rh_of : forall XR inst ly X W regs mem md r W' c',
drain_leaf_g B ARX AOX XR inst ly X W regs mem md r W' c' -> drain_leaf_g_rh XR inst ly X W regs mem md r W' c'.
Proof.
intros XR inst ly X W regs mem md r W' c' (regs' & mem' & md' & Hc & HP & HX).
exists regs', mem', md'. split; [exact Hc|]. split; [|exact HX].
exact (YGcfRehidePost.acall_post_x_rh_of B ARX AOX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP).
Qed.
Lemma drain_spec_g_rh_of : forall XR, drain_spec_g B ARX AOX dbody L24 QB XR -> drain_spec_g_rh XR.
Proof.
intros XR H inst ly X W regs mem md PRE.
eapply amreal'_mono; [| exact (amreal_amreal' im_segs YGcfRehidePost.RZ_cf _ _ _ _ (H inst ly X W regs mem md PRE))].
intros r W' c' HL. exact (drain_leaf_g_rh_of XR inst ly X W regs mem md r W' c' HL).
Qed.
End rh.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. Recycle (DMiface.di_rchunk_t, DIfaceR.dr_rchunk_t, MnRecycle.de_rchunk_m_t).  CacheDealloc (di_cdealloc_t,     *)
(*    dr_cdealloc_t, de_cdealloc_m_t) stays released: it re-hides nothing.                                          *)
Section rch.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
(* the view form: DMiface.di_rchunk_t *)
Definition di_rchunk_rh_t : Prop :=
forall inst ly X k ks zs cbp W regs mem md,
rcc_pre_x B ARXr inst ly X k cbp W regs mem md -> DRq X (k :: ks) zs ->
amreal' im_segs YGcfRehidePost.RZ_cf (recycle_chunk k X) W (cfg_at im_segs dg_rchunk regs mem md)
(fun r W' c' => exists regs' mem' md',
  c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
  YGcfRehidePost.acall_post_x_rh B ARXr AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  (forall a, 0 <= a < 2 ^ 64 -> YFeuC.puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
   aview im_segs (w_H W') mem' a = aview im_segs (w_H W) mem a) /\
  (forall a, YFeuC.puser ly X a -> YFeuC.puser ly (snd r) a) /\
  DRq (snd r) ks zs /\ st_cache_inited (snd r) = true /\ (forall a, AOX ly (snd r) a -> AOX ly X a)).
Lemma di_rchunk_rh_of : di_rchunk_t B ARXr AOX DRq -> di_rchunk_rh_t.
Proof.
intros H inst ly X k ks zs cbp W regs mem md P D.
eapply amreal'_mono; [| exact (amreal_amreal' im_segs YGcfRehidePost.RZ_cf _ _ _ _ (H inst ly X k ks zs cbp W regs mem md P D))].
intros r W' c' (regs' & mem' & md' & Hc & HP & HT).
exists regs', mem', md'. split; [exact Hc|].
split; [exact (YGcfRehidePost.acall_post_x_rh_of B ARXr AOX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP) | exact HT].
Qed.
(* the raw form: DIfaceR.dr_rchunk_t *)
Definition dr_rchunk_rh_t : Prop :=
forall inst ly X k ks zs cbp W regs mem md,
rcc_pre_x B ARXr inst ly X k cbp W regs mem md -> DRq X (k :: ks) zs ->
amreal' im_segs YGcfRehidePost.RZ_cf (recycle_chunk k X) W (cfg_at im_segs dg_rchunk regs mem md)
(fun r W' c' => exists regs' mem' md',
  c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
  YGcfRehidePost.acall_post_x_rh B ARXr AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  acall_raw_x B AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  (forall a, 0 <= a < 2 ^ 64 -> YFeuC.puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
   aview im_segs (w_H W') mem' a = aview im_segs (w_H W) mem a) /\
  (forall a, YFeuC.puser ly X a -> YFeuC.puser ly (snd r) a) /\
  DRq (snd r) ks zs /\ st_cache_inited (snd r) = true /\ (forall a, AOX ly (snd r) a -> AOX ly X a)).
Lemma dr_rchunk_rh_of : dr_rchunk_t B ARXr AOX DRq -> dr_rchunk_rh_t.
Proof.
intros H inst ly X k ks zs cbp W regs mem md P D.
eapply amreal'_mono; [| exact (amreal_amreal' im_segs YGcfRehidePost.RZ_cf _ _ _ _ (H inst ly X k ks zs cbp W regs mem md P D))].
intros r W' c' (regs' & mem' & md' & Hc & HP & HT).
exists regs', mem', md'. split; [exact Hc|].
split; [exact (YGcfRehidePost.acall_post_x_rh_of B ARXr AOX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP) | exact HT].
Qed.
(* the memnorm form: MnRecycle.de_rchunk_m_t (H4's head, DMwalkIFRh.rchunk_m_rh_t) *)
Definition de_rchunk_m_rh_t : Prop :=
forall inst ly X k ks zs cbp W regs mem md,
rcc_pre_x B ARXr inst ly X k cbp W regs mem md -> DRq X (k :: ks) zs ->
amreal' im_segs YGcfRehidePost.RZ_cf (recycle_chunk k X) W (cfg_at im_segs dg_rchunk regs mem md)
(fun r W' c' => exists regs' mem' md',
  c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
  YGcfRehidePost.acall_post_x_rh B ARXr AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  acall_raw_x B AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  ErrnoG.errno_kept B mem mem' /\
  MemnormT.memnorm_keep im_segs mem mem' /\
  (forall a, 0 <= a < 2 ^ 64 -> YFeuC.puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
   aview im_segs (w_H W') mem' a = aview im_segs (w_H W) mem a) /\
  (forall a, YFeuC.puser ly X a -> YFeuC.puser ly (snd r) a) /\
  DRq (snd r) ks zs /\ st_cache_inited (snd r) = true /\ (forall a, AOX ly (snd r) a -> AOX ly X a)).
Lemma de_rchunk_m_rh_of : de_rchunk_m_t B ARXr AOX DRq -> de_rchunk_m_rh_t.
Proof.
intros H inst ly X k ks zs cbp W regs mem md P D.
eapply amreal'_mono; [| exact (amreal_amreal' im_segs YGcfRehidePost.RZ_cf _ _ _ _ (H inst ly X k ks zs cbp W regs mem md P D))].
intros r W' c' (regs' & mem' & md' & Hc & HP & HT).
exists regs', mem', md'. split; [exact Hc|].
split; [exact (YGcfRehidePost.acall_post_x_rh_of B ARXr AOX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP) | exact HT].
Qed.
End rch.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. The records (DGif0.DIface's drain and Recycle fields, DIfaceR.DIfaceR, MnRecycle.DIfaceREm), the arms' drain   *)
(*    contract (DIfaceR.drain_spec_b) and the Deallocate leaf (DIfaceR.dealloc_leaf_b), over DIface's parameters.   *)
Section b.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable ft : sptr -> list Z -> M unit.
Variable ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable ARXr : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable lpost : astate -> Prop.
Variable fpre : alayout -> astate -> world im_segs -> (word -> option byte) -> sptr -> Z -> Prop.
Variable dpost : Z -> alayout -> astate -> world im_segs -> list Z -> Z -> (word -> option byte) -> Prop.
Variable dbody : astate -> M unit.
Variable L24 : Z.
Variable QB : astate -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
(* DGif0.DIface's memory predicate at Put's call of Enqueue (di_enqueue's premise). *)
Variable MP : (word -> option byte) -> Prop.

(* DGif0.DIface at the twins of its drain and Recycle fields (dih_drain, dih_rchunk); every other field is DIface's,
   word for word, renamed di_* -> dih_* so that a file importing both reads each name once.  DIface's text is
   unchanged.  An instance whose Recycle re-hides discharges this record; DIface gives it (DIface_rh_of). *)
Record DIface_rh : Prop := {
  dih_inst : forall inst ly S W mem md, ARX inst ly S W mem md -> dg_inst_ok inst;
  (* (view) *)
  dih_view_n : forall inst ly S W mem md n, ARX inst ly S W mem md -> rpre S n -> dview_n B W ly inst mem;
  dih_view : forall inst ly S W mem md p n, ARX inst ly S W mem md -> rpre S n -> fpre ly S W mem p n -> In (p, n) (blocks S) ->
    dview B W ly inst mem S p n;
  (* (shape) *)
  dih_shape_n : forall n tr S, rpre S n -> ft PNull tr S = ret tt (dtick S);
  dih_shape : forall p n tr S k, p <> PNull -> rpre S n -> In (p, n) (blocks S) -> find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
    ft p tr S = (depot_put tr ;; modify (fun s => set_chunks (upd_chunk (st_chunks s) (qk k)) s) ;; enqueue (qk k) ;; dmd dbody) (dtick S);
  (* the depot callee (QuarantineChunk's call), entered with the depot zone and the constant cells outside the
     internal allocator's zone as at [mem0] *)
  dih_depot : forall inst ly S W mem0 md0 tr (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (buf : Z),
    ARX inst ly S W mem0 md0 -> U tr S ->
    (forall x : word, dg_dzone ly (bv_unsigned x) \/ (dg_czone ly (bv_unsigned x) /\ ~ dg_izone (bv_unsigned x)) -> mem x = mem0 x) ->
    getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
    getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 im_tp -> YK0s.ret_ok (getr regs 1) ->
    (forall i, (i < length tr)%nat -> val_mem im_segs (mrestrict (w_H W) mem) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
    buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly ->
    buf + 8 * 30 <= bv_unsigned (getr regs 2) - YFl0C.DEP_STK \/ bv_unsigned (getr regs 2) <= buf ->
    bv_unsigned (getr regs 2) mod 16 = 0 -> ly_stk_lo ly <= bv_unsigned (getr regs 2) - YFl0C.DEP_STK ->
    bv_unsigned (getr regs 2) <= ly_stk_hi ly ->
    (forall a, bv_unsigned (getr regs 2) - YFl0C.DEP_STK <= a < bv_unsigned (getr regs 2) -> apresent (w_H W) mem a) ->
    SRr im_segs W (mkCfg (mkst regs (Z_to_bv 64 dg_depot) mem (seg_rom im_segs)) md)
    (fun W' c' => W' = W /\ exists z regs' mem' mat,
      c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md) mat md) /\
      regs_preserved regs regs' /\
      (forall x : word, ~ (bv_unsigned (getr regs 2) - YFl0C.DEP_STK <= bv_unsigned x < bv_unsigned (getr regs 2)) ->
         ~ dg_dzone ly (bv_unsigned x) -> mem' x = mem x) /\
      (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
      dpost inst ly S W tr z mem');
  dih_dpost_aok : forall inst ly S W tr z m, dpost inst ly S W tr z m -> aok S (KDepot tr) z;
  (* QuarantineCache::Enqueue at Put's call (sp = Deallocate's entry sp - 80), arms mid and drain: from the entry
     state, the depot's answer [z] and the memory at the call, at which MP holds; the post is over ARX of the enqueued
     state, whose owned set is the quarantined state's, and gives lpost when no drain follows *)
  dih_enqueue : forall inst ly S W mem0 md0 p n tr k z hb1 sp0 (regs : bvmap 5 word) (mem : word -> option byte) mat,
    ARX inst ly S W mem0 md0 -> rpre S n -> fpre ly S W mem0 p n -> In (p, n) (blocks S) -> U tr S ->
    find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
    ly_stk_lo ly + DGbaseC.DFSTACK <= sp0 -> sp0 <= ly_stk_hi ly -> ly_bot ly < sp0 -> sp0 mod 16 = 0 ->
    0 <= hb1 < 256 -> val_mem im_segs (mrestrict (w_H W) mem0) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1) ->
    dmem_m W ly sp0 mem0 (sptr_addr B ly p) (req_size n) hb1 (dpost inst ly S W tr z) mem ->
    MP mem ->
    YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs -> spZ regs = sp0 - 80 ->
    getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
    getr regs 10 = w64 (ly_T ly + t_qc) -> getr regs 11 = w64 (ly_T ly + t_cache) ->
    getr regs 13 = w64 (sptr_addr B ly p - kChunkHeaderSize) -> getr regs 14 = w64 (req_size n) ->
    amreal im_segs (enqueue (qk k) (qx S k z tr)) W
      (cfg_at im_segs dg_enqueue regs mem (with_vm_backing (m_vm_lazy md0) mat md0))
      (fun r W' c' => exists regs' mem' md' nb,
        c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
        acall_post_x B ARX AOX inst YFewC.QSTACK ly (qx S k z tr) W regs mem (with_vm_backing (m_vm_lazy md0) mat md0) (fun _ => False)
          ly (snd r) W' regs' mem' md' /\
        st_qthread (snd r) = qc_push (st_qthread (qx S k z tr)) (qk k) nb /\
        match nb with None => need_new_batch (st_qthread (qx S k z tr)) = false | Some _ => need_new_batch (st_qthread (qx S k z tr)) = true end /\
        st_chunks (snd r) = st_chunks (qx S k z tr) /\ st_qglobal (snd r) = st_qglobal (qx S k z tr) /\
        (forall a, AOX ly (snd r) a -> AOX ly (qx S k z tr) a) /\
        (* the thread cache's byte count, which Put reads after Enqueue returns *)
        val_mem im_segs (mrestrict (w_H W') mem') (ly_T ly + t_qc + 24) 8 (qc_bytes (st_qthread (snd r))) /\
        (qc_bytes (st_qthread (snd r)) <= kQuarantineCacheMax -> lpost (snd r)) /\
        (kQuarantineCacheMax < qc_bytes (st_qthread (snd r)) -> QB (snd r) /\ Z.of_nat (length (all_batches (snd r))) <= L24));
  (* Quarantine::Drain at Put's call (a0 = inst + o_quar), arm drain: DMspec's contract at the re-hide twin *)
  dih_drain : drain_spec_cf_rh B ARX AOX dbody L24 QB;
  (* lpost at the end of a granted path of the drain tree from the enqueued state [X'] (ARX at X': the drain
     tree's lpost needs the state's well-formedness) *)
  dih_lpost_d : forall inst ly S W mem md p n tr k z nb X' (W' : world im_segs) (mem' : word -> option byte) (md' : Model) trc r,
    ARX inst ly S W mem md -> rpre S n -> In (p, n) (blocks S) -> U tr S ->
    find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
    st_qthread X' = qc_push (st_qthread (qx S k z tr)) (qk k) nb ->
    match nb with None => need_new_batch (st_qthread (qx S k z tr)) = false | Some _ => need_new_batch (st_qthread (qx S k z tr)) = true end ->
    st_chunks X' = st_chunks (qx S k z tr) -> st_qglobal X' = st_qglobal (qx S k z tr) ->
    ARX inst ly X' W' mem' md' ->
    kQuarantineCacheMax < qc_bytes (st_qthread X') ->
    apath (dbody X' X') trc r -> gflag trc = true -> lpost (snd r);
  (* the real-merge drain's reads of the machine (DMiface; h-verbs-5's DMdrain consumes them) *)
  dih_qview : di_qview_t B ARX L24 QB;
  dih_qowned : di_qowned_t ARX AOX L24 QB;
  dih_requar_x : di_requar_x_t B ARX AOX L24 QB;
  dih_requar_r : di_requar_r_t B ARX ARXr AOX L24 QB DRq;
  dih_requar_e : di_requar_e_t ARX ARXr DRq;
  dih_rchunk : di_rchunk_rh_t B ARXr AOX DRq;
  dih_cdealloc : di_cdealloc_t B ARXr AOX DRq;
  dih_frame_r : di_frame_t ARXr AOX;
  dih_rview : di_rview_t B ARXr DRq;
  (* (post) the arm whose last batch has room: the memory at Deallocate's return gives ARX and lpost of the final
     state *)
  dih_post_c : forall inst ly S W mem0 md0 p n tr k lastb initr hb1 z sp0 mem' mat,
    ARX inst ly S W mem0 md0 -> rpre S n -> fpre ly S W mem0 p n -> In (p, n) (blocks S) -> U tr S ->
    find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
    rev (qc_list (st_qthread S)) = lastb :: initr -> Z.of_nat (length (b_items lastb)) < kBatchSlots ->
    qc_bytes (st_qthread S) + req_size n <= kQuarantineCacheMax ->
    ly_stk_lo ly + DGbaseC.DFSTACK <= sp0 -> sp0 <= ly_stk_hi ly -> ly_bot ly < sp0 -> sp0 mod 16 = 0 ->
    0 <= hb1 < 256 -> val_mem im_segs (mrestrict (w_H W) mem0) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1) ->
    dmem_c W ly sp0 mem0 (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) lastb (dpost inst ly S W tr z) mem' ->
    (exists trc, apath (ft p tr S) trc (tt, qfin_c S k z tr) /\ gflag trc = true) ->
    ARX inst ly (qfin_c S k z tr) W mem' (with_vm_backing (m_vm_lazy md0) mat md0) /\ lpost (qfin_c S k z tr);
  (* (post) the NULL arm *)
  dih_post_n : forall inst ly S W mem0 md0 n tr sp0 mem' mat,
    ARX inst ly S W mem0 md0 -> rpre S n -> fpre ly S W mem0 PNull n -> U tr S ->
    ly_stk_lo ly + DGbaseC.DFSTACK <= sp0 -> sp0 <= ly_stk_hi ly -> ly_bot ly < sp0 -> sp0 mod 16 = 0 ->
    dmem_n W ly sp0 mem0 mem' ->
    (exists trc, apath (ft PNull tr S) trc (tt, dtick S) /\ gflag trc = true) ->
    ARX inst ly (dtick S) W mem' (with_vm_backing (m_vm_lazy md0) mat md0) /\ lpost (dtick S);
  (* (laws) *)
  dih_frame : di_frame_t ARX AOX;
  dih_stack : di_stack_t ARX AOX;
  (* (owned) *)
  dih_owned : forall inst ly S W mem md p n k a,
    ARX inst ly S W mem md -> rpre S n -> In (p, n) (blocks S) -> find_user (st_chunks S) p = Some k ->
    0 <= a < 2 ^ 64 -> dwrites ly (sptr_addr B ly p) (req_size n) a ->
    AOX ly S a \/ (sptr_addr B ly p <= a < sptr_addr B ly p + req_size n);
  dih_owned_b : forall inst ly S W mem md lastb initr a,
    ARX inst ly S W mem md -> rev (qc_list (st_qthread S)) = lastb :: initr -> 0 <= a < 2 ^ 64 -> bwrites ly lastb a -> AOX ly S a;
  dih_owned_i : forall inst ly S W mem md a, ARX inst ly S W mem md -> dg_izone a -> AOX ly S a;
  dih_owned_x : forall inst ly S W mem md p n k z tr a,
    ARX inst ly S W mem md -> rpre S n -> In (p, n) (blocks S) -> find_user (st_chunks S) p = Some k ->
    AOX ly (qx S k z tr) a -> AOX ly S a \/ (sptr_addr B ly p <= a < sptr_addr B ly p + req_size n)
}.
Lemma DIface_rh_of : DIface B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP -> DIface_rh.
Proof.
intros IF. constructor.
all: try exact (drain_spec_cf_rh_of B ARX AOX dbody L24 QB (di_drain B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF)).
all: try exact (di_rchunk_rh_of B ARXr AOX DRq (di_rchunk B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF)).
all: destruct IF; assumption.
Qed.

(* DIfaceR.DIfaceR at the twins of its drain and Recycle fields; Enqueue and CacheDealloc stay released. *)
Record DIfaceR_rh : Prop := {
  drh_enqueue : enq_spec_g B U ARX AOX rpre lpost fpre dpost L24 QB MP (acall_raw_x B AOX);
  drh_drain : drain_spec_raw_cf_rh B ARX AOX dbody L24 QB;
  drh_rchunk : dr_rchunk_rh_t B ARXr AOX DRq;
  drh_cdealloc : dr_cdealloc_t B ARXr AOX DRq
}.
Lemma DIfaceR_rh_of : DIfaceR B U ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP -> DIfaceR_rh.
Proof.
intros [HE HD HR HC]. constructor.
- exact HE.
- exact (drain_spec_g_rh_of B ARX AOX dbody L24 QB (acall_raw_x B AOX) HD).
- exact (dr_rchunk_rh_of B ARXr AOX DRq HR).
- exact HC.
Qed.

(* MnDrain.de_drain_m_t at the twin, and MnRecycle.DIfaceREm at the twins of its drain and Recycle fields. *)
Definition de_drain_m_rh_t : Prop := drain_spec_g_rh B ARX AOX dbody L24 QB (acall_raw_em_x B AOX).
Lemma de_drain_m_rh_of : de_drain_m_t B ARX AOX dbody L24 QB -> de_drain_m_rh_t.
Proof. exact (drain_spec_g_rh_of B ARX AOX dbody L24 QB (acall_raw_em_x B AOX)). Qed.
Record DIfaceREm_rh : Prop := {
  demh_enqueue : de_enqueue_m_t B U ARX AOX rpre lpost fpre dpost L24 QB MP;
  demh_drain : de_drain_m_rh_t;
  demh_rchunk : de_rchunk_m_rh_t B ARXr AOX DRq;
  demh_cdealloc : de_cdealloc_m_t B ARXr AOX DRq
}.
Lemma DIfaceREm_rh_of : DIfaceREm B U ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP -> DIfaceREm_rh.
Proof.
intros [HE HD HR HC]. constructor.
- exact HE.
- exact (de_drain_m_rh_of HD).
- exact (de_rchunk_m_rh_of B ARXr AOX DRq HR).
- exact HC.
Qed.

(* DIfaceR.drain_spec_b (the arms' drain contract, raw conjunct when [rawb = true]) at the twin. *)
Definition drain_spec_b_rh (rawb : bool) : Prop :=
  drain_spec_g_rh B ARX AOX dbody L24 QB (rawif rawb (acall_raw_x B AOX)).
Lemma drain_spec_b_rh_of : forall rawb, drain_spec_b B ARX AOX dbody L24 QB rawb -> drain_spec_b_rh rawb.
Proof. intros rawb. exact (drain_spec_g_rh_of B ARX AOX dbody L24 QB (rawif rawb (acall_raw_x B AOX))). Qed.
Lemma drain_spec_b_rh_false : DIface_rh -> drain_spec_b_rh false.
Proof.
intros IF inst ly X W regs mem md PRE.
eapply amreal'_mono; [| exact (dih_drain IF inst ly X W regs mem md PRE)].
intros r W' c' (regs' & mem' & md' & Hc & HP).
exists regs', mem', md'. split; [exact Hc|]. split; [exact HP | intros X0; discriminate X0].
Qed.
Lemma drain_spec_b_rh_true : DIfaceR_rh -> drain_spec_b_rh true.
Proof.
intros IR inst ly X W regs mem md PRE.
eapply amreal'_mono; [| exact (drh_drain IR inst ly X W regs mem md PRE)].
intros r W' c' (regs' & mem' & md' & Hc & HP & HX).
exists regs', mem', md'. split; [exact Hc|]. split; [exact HP | intros _; exact HX].
Qed.

(* DIfaceR.dealloc_leaf_b at the free path's re-hide post (YGcfRehidePost.dealloc_post_rh); the raw frame, lpost and
   the path clause are unchanged. *)
Definition dealloc_leaf_b_rh (rawb : bool) (inst : Z) (ly : alayout) (S : astate) (W : world im_segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n : Z) (tr : list Z)
(r : unit * astate) (W' : world im_segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
YGcfRehidePost.dealloc_post_rh im_segs B ARX AOX inst ly S W regs mem md
  (fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) ly' (snd r) W' regs' mem' md' /\
(rawb = true -> forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX ly' (snd r) (bv_unsigned x) ->
  ~ ascratch B DFSTACK_G regs (bv_unsigned x) ->
  ~ (p <> PNull /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n) -> mem' x = mem x) /\
lpost (snd r) /\
(exists trc, apath (ft p tr S) trc r /\ gflag trc = true).
Lemma dealloc_leaf_b_rh_of : forall rawb inst ly S W regs mem md p n tr r W' c',
dealloc_leaf_b B ft ARX AOX lpost rawb inst ly S W regs mem md p n tr r W' c' ->
dealloc_leaf_b_rh rawb inst ly S W regs mem md p n tr r W' c'.
Proof.
intros rawb inst ly S W regs mem md p n tr r W' c' (ly' & regs' & mem' & md' & Hc & HP & HR & HL & HT).
exists ly', regs', mem', md'. split; [exact Hc|].
split; [exact (YGcfRehidePost.dealloc_post_rh_of im_segs B ARX AOX _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP)|].
split; [exact HR|]. split; [exact HL | exact HT].
Qed.
End b.
End a.
