(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs ImgFacts.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import F_malloc_free F_malloc_fast F_free F_free_K F_free_spec MallocTree MallocKit_A MallocBlocks MallocHINV
  MallocFacts_A MallocFacts_B MallocFacts_inv MallocFacts_inv2 MallocFacts_inv3 Malloc_iface Malloc_fp F_malloc_entry.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl Prog KInv MI_Inv MI_Ext MI_Geom MI_WRealloc MI_WRealloc2.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import RMallocRep RMallocTree RMallocKit_A RMallocKit_B RMalloc_iface RMalloc_ifaceP RF_free_spec
  RF_realloc_A RF_realloc_C RF_realloc_ip.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation RAREACH := (AREACH_from p0_reserved).

Definition rrip_spec_post {HGW : HasGuard} {HCEIL : HasCeiling} (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (k : bptr) (A sz n' lo : Z) (old : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' junk,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ (forall B, rauxv_ok m B -> bv_unsigned sp <= B -> rauxv_ok m' B)
    /\ (forall ev, rw_cells rsegs m RERRNO [C4 ev] -> rw_cells rsegs m' RERRNO [C4 ev])
    /\ rheap_pres (lb_remove k LB) (bv_unsigned sp) m m'
    /\ RHEAP s ((k, A, n') :: lb_remove k LB) m'
    /\ rblock_range A n'
    /\ rw_cells rsegs m' A [CB (Z.to_nat n') (firstn (Z.to_nat (Z.min n' sz)) old ++ junk)].

Lemma bytes_at_firstn m a bs k : bytes_at rsegs m a bs -> bytes_at rsegs m a (firstn k bs).
Proof.
  intros H. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

Theorem rrealloc_walk_spec {HGW : HasGuard} {HCEIL : HasCeiling} : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (s : PState) (LB : list block) (k : bptr) (A sz n' lo : Z) (old : list byte),
  RHEAP s LB m -> In (k, A, sz) LB -> rw_cells rsegs m A [CB (Z.to_nat sz) old] ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 -> mem_inv rsegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n' -> 0 <= n' < MMAP_THRESHOLD ->
  evt rsegs (fun ms' => rrip_spec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB k A sz n' lo old m ms'
                        \/ rrgen_prefix_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A sz n' m ms')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 rrealloc_sym) fc None m (seg_rom rsegs)).
Proof.
  intros until old. intros HP Hin CELLS ST LO SLO MI A0 A1 N.
  destruct HP as (st & LB0 & PERM & Hst & HMR & [BL AR]).
  assert (Hin0 : In (k, A, sz) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]).
  pose proof (areach_cinv_proof _ _ AR) as C.
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) (k, A, sz) Hin0) as BK.
  destruct BK as [(g & i & b & SL & HBg & FB & Ii & NFR & (off & O0 & OA & OS & OK & HK)) NG SZ].
  cbn [blk_addr blk_slot blk_size fst snd] in OA, SL, NG, OS, SZ.
  eapply evt_mono.
  { eapply (rrealloc_walk gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB0 lo LO ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m st (k, A, sz) off n' g i);
      cbn [blk_addr blk_slot fst snd]; try eassumption. }
  cbn [blk_addr blk_slot blk_size fst snd].
  intros ms' [[IP POST]|[NIP POST]]; [left| right; exact POST]. subst a0.
  destruct POST as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & -> & MI' & ST' & MRz & TKz & CEz & PE & WR' & GEO).
  destruct GEO as (G1 & G3 & G4 & G5 & G6 & (r & Hr & Kr & HAP & ETOP & RBC)). change (blk_slot (k, A, sz)) with (fst k) in Hr, HAP.
  set (stride := get_stride (get_meta_rec st g)) in *.
  set (E := A - UNIT * off + stride - IB) in *.

  pose proof HMR as (WF & _). pose proof WF as (Hres & CE & WR & DJ & WA & WG).
  pose proof (ci_nodup _ _ C) as NDS.
  assert (NDSL : List.NoDup (map blk_slot LB)) by (eapply NoDup_map_perm; [exact PERM| exact NDS]).
  pose proof (lb_remove_lbrm LB k A sz NDSL Hin) as ELB.
  destruct (areach_inv _ st LB0 AR) as (L & LS & BL0 & INV & _ & _ & _ & _).
  ceil_facts. unfold UNIT, IB in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) (k, A, sz) Hin0) as [(r0 & Hr0 & _ & A16 & AEND & AL & _) _ _].
  cbn [blk_addr blk_slot blk_size fst snd] in Hr0, A16, AEND, AL. rewrite Hr in Hr0. assert (r0 = r) by congruence. subst r0.
  assert (S16 : 16 <= stride) by (destruct (ci_gmetas _ _ C b g HBg) as [_ _ _ _ _ _ _ _ _ _ GS _]; unfold UNIT in GS; exact (proj1 GS)).

  assert (NFP : forall a, 0 <= a < 2^64 -> rclient_addr (lb_remove k LB) (bv_unsigned sp) a ->
                ~ (lo <= a < bv_unsigned sp \/ A - 3 <= a < A \/ A + n' <= a < E)).
  { intros a Ha CA X.
    destruct CA as [CA|[[CA NS]|(b' & Hb' & Hab)]]; [lia| unfold E in X; lia|].
    rewrite ELB in Hb'. pose proof (In_lbrm_perm _ _ _ _ (Permutation_sym PERM) Hb') as Hb0. unfold lbrm in Hb0.
    apply In_filter_iff in Hb0. destruct Hb0 as [Hb0 NEQ]. cbn [blk_slot fst snd] in NEQ.
    destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) b' Hb0) as [(r' & Hr' & Kr' & A16' & AEND' & _ & _) _ _].
    destruct (WR _ _ Hr') as (_ & _ & _ & RBC' & _). ceil_facts.
    destruct X as [X|X]; [lia|].
    destruct (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) b' Hb0) as [(g' & i' & bb' & SL' & _ & FB' & _ & _ & (off' & O0' & OA' & OS' & _)) NG' SZ'].
    destruct (N.eq_dec (fst (blk_slot b')) (fst (fst k))) as [EQ|NE].
    -
      assert (r' = r) by (rewrite EQ in Hr'; rewrite Hr in Hr'; congruence). subst r'.
      assert (NEQ' : blk_slot b' <> fst k) by (intros EE; rewrite EE, aptr_eqb_refl in NEQ; cbn in NEQ; congruence).
      pose proof (blk_slots_sep x0 st L BL0 LS INV (fst k) g i (blk_slot b') g' i' SL NG SL' NG' NEQ' EQ) as SEP.
      change (MR st g) with (get_meta_rec st g) in SEP. change (MR st g') with (get_meta_rec st g') in SEP. fold stride in SEP. unfold UNIT, IB in OS'.
      rewrite (conc_region' st (blk_slot b') r ltac:(rewrite EQ; exact Hr)) in OA'. unfold UNIT in OA'.
      unfold E in X, G1. clear -SEP OA' OS' X Hab HAP O0 O0' SZ' S16 N G1.
      lia.
    -
      destruct (DJ _ _ _ _ Hr' Hr NE) as [D|D]; rewrite lr_lo_group in D by assumption; unfold E in X; lia. }

  assert (HAc : A = conc st (fst k) + 16 * off) by exact OA.
  assert (LENold : length old = Z.to_nat sz).
  { destruct CELLS as [[WFc _] _]. cbn in WFc. exact (proj1 WFc). }
  destruct CELLS as [[_ OLD] _]. cbn [cells_bytes cbytes app] in OLD. rewrite app_nil_r in OLD.
  destruct (rwr_at_bytes_exist m' A n' WR' ltac:(lia) ltac:(unfold E in G5, G6; lia)) as (bs & LBS & BS).
  set (mn := Z.to_nat (Z.min n' sz)).
  assert (BS1 : bytes_at rsegs m' A (firstn mn old)).
  { eapply rpres_except_bytes_at; [exact PE| apply bytes_at_firstn; exact OLD|].
    rewrite firstn_length. intros a Ha [X|[X|X]]; unfold mn, E in *; lia. }
  assert (BS2 : bytes_at rsegs m' (A + Z.of_nat mn) (skipn mn bs)).
  { rewrite <- (firstn_skipn mn bs) in BS. apply bytes_at_app in BS. destruct BS as [_ BS]. rewrite firstn_length, LBS in BS.
    replace (Z.of_nat (mn `min` Z.to_nat n')) with (Z.of_nat mn) in BS by (unfold mn; lia). exact BS. }
  unfold rrip_spec_post. do 14 eexists. exists m', (skipn mn bs). split; [reflexivity|].
  split; [exact MI'|]. split; [exact ST'|]. split; [| split; [| split; [| split; [| split]]]].
  -   intros B AV HB. eapply rauxv_ok_pres; [exact AV| exact PE| |]; intros a Ha [X|[X|X]]; unfold E, RAUXV_CELL in *; lia.
  -   intros ev ERR. eapply rpres_except_rw_cells; [exact PE| exact ERR|]. cbn. intros a Ha [X|[X|X]]; unfold E, RERRNO, RATP in *; lia.
  -   intros a Ha CA. apply PE; [exact Ha|]. exact (NFP a Ha CA).
  -
    exists (mresize st (fst k) off sz n'), ((k, A, n') :: lbrm LB0 (k, A, sz)). split; [| split; [| split; [exact MRz| split]]].
    + rewrite ELB. apply perm_skip. apply lbrm_perm. exact PERM.
    + rewrite (mresize_eq st (fst k) off sz n' g i SL), rs_st3_strip. exact Hst.
    +   unfold brk_link in BL |- *. rewrite <- (ce_ctx _ _ CEz) || idtac.
      change (ctx (mresize st (fst k) off sz n')) with (s_ctx (mresize st (fst k) off sz n')). rewrite (ce_ctx _ _ CEz). change (s_ctx st) with (ctx st).
      destruct (c_brk (ctx st)) as [| |brid boff] eqn:HB0; [exact Logic.I| exact Logic.I|].
      unfold conc, get_region in BL |- *. rewrite (ce_regions _ _ CEz). exact BL.
    + change ((k, A, n') :: lbrm LB0 (k, A, sz)) with ((blk_id (k, A, sz), blk_addr (k, A, sz), n') :: lbrm LB0 (k, A, sz)).
      change (fst k) with (blk_slot (k, A, sz)). change sz with (blk_size (k, A, sz)) at 1.
      apply (areach_resize st LB0 (k, A, sz) off n' AR Hin0 O0 OA (proj1 N)).
      exists g, i. split; [exact SL|]. split; [unfold UNIT, IB; exact (proj1 IP)|].
      split; [pose proof (size_to_class_props n' N) as (SCR' & _); pose proof (proj2 IP) as CLS'; split; [intros _; exact CLS'| intros H63; exfalso; clear -SCR' CLS' H63; lia]|].

      pose proof (areach_facts_proof _ _ AR) as MF.
      destruct (ci_gmetas _ _ C b g HBg) as [_ _ _ _ _ GSC _ _ GMEM _ _ _].
      assert (HmemS : m_mem (get_meta_rec (strip st) g) = Some b) by (rewrite get_meta_rec_strip; exact GMEM).
      destruct (mf_gmeta _ _ MF g b HmemS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S31 & _). rewrite get_meta_rec_strip in S31.
      pose proof (size_to_class_props n' N) as (SCR & _ & _). pose proof (proj2 IP) as CLS.
      fold stride in S31 |- *. unfold UNIT, IB. clear -S31 GSC SCR CLS O0 N. lia.
  -   ceil_facts; unfold rblock_range. unfold E in *. repeat split; try lia. all: clear -G4; Z.div_mod_to_equations; lia.
  -   split; [split|].
    + cbn. rewrite app_length, firstn_length, skipn_length, LENold, LBS. split; [unfold mn; lia| exact Logic.I].
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact BS1|]. rewrite firstn_length, LENold.
      replace (Z.of_nat (mn `min` Z.to_nat sz)) with (Z.of_nat mn) by (unfold mn; lia). exact BS2.
    + cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact WR'.
Qed.
