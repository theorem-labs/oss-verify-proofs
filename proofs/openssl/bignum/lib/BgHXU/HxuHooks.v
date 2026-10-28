(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From Stdlib Require Import Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Frame.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface RRealloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Stdio HexModel Target Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Exit Printf_wfile F_memset Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Common Require Import FastWord FastWordSem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound HxToolkit HxGlue.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgHXU Require Import HxuInit HxuImage HxuInv.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Lemma nf_regs (rho : valuation) (S : sstate) (F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) :
  Rregs rho (s_regs S) (Core (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv) ->
  den rho (rget S X1) x1 /\ den rho (rget S X2) x2 /\ den rho (rget S X4) x4 /\ den rho (rget S X10) x10
  /\ den rho (rget S X11) x11 /\ den rho (rget S X12) x12.
Proof.
  intros H. repeat split.
  - exact (H (Z_to_bv 5 1)). - exact (H (Z_to_bv 5 2)). - exact (H (Z_to_bv 5 4)). - exact (H (Z_to_bv 5 10)).
  - exact (H (Z_to_bv 5 11)). - exact (H (Z_to_bv 5 12)).
Qed.

Lemma ret_pc_wbv (ra : w64) : ret_pc (wbv ra) = wbv (w_and ra w_notone).
Proof. rewrite wbv_and, wbv_notone. reflexivity. Qed.

Lemma R_return (rho : valuation) (S : sstate) (res : hval) (M' : HxMem.mem) (abs : abstab) (nx : int) (ra : w64)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
    (F F' : bvmap 5 word) (pc : word) (fc fc' : bv 32) (rv : option word) (m' ro : word -> option byte) :
  Rregs rho (s_regs S) (Core (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv) ->
  x1 = wbv ra -> den rho res a0' -> Rmem bgusegs rho M' m' ->
  R bgusegs rho (SS (w_and ra w_notone) (rf_set (havoc_caller_saved (s_regs S)) X10 res) RNone M' abs nx)
    (MS (mkR x1 x2 x3 x4 t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')
        F' (ret_pc x1) fc' None m' ro).
Proof.
  intros HRg E1 Hd HRm. unfold R. cbn [ms_svc_pending ms_pc_val ms_resv ms_mem MS s_pc s_regs s_resv s_mem].
  split; [reflexivity|]. split; [rewrite E1; apply ret_pc_wbv|]. split.
  { unfold core_of. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv MS]. eapply (Rregs_return rho (s_regs S) res); [exact HRg | exact Hd]. }
  split; [reflexivity | exact HRm].
Qed.

Section Hooks.
Context {CE__ : Ceiling} {RN__ : RunRnd} {LM : LibModel} {LSP : LibSpec}.
Variables (LB : list block) (lo B sp0 : Z) (m0 : word -> option byte) (F0 : bvmap 5 word) (fc0 : bv 32) (s0 : PState).
Variable ls0 : LS.
Variable POST : LS -> PState -> machine_state -> Prop.

Hypothesis H_LIBW : LIBW = LIBW_HX.
Hypothesis H_lo1 : alloc_ceiling <= lo.
Hypothesis H_lo2 : GLOBALS_TOP <= lo.
Hypothesis H_lo3 : lo <= sp0 - to_Z STK.
Hypothesis H_sp0B : sp0 <= B.
Hypothesis H_sp064 : sp0 < 2 ^ 64.

Hypothesis MALLOC : rmalloc_stmt.
Hypothesis REALLOC : rrealloc_stmt.

Notation FInvP := (FInv LB lo B sp0 m0 F0 fc0 s0).
Notation FMemP := (FMem LB lo B sp0 m0).
Notation JP := (J ls0 POST).
Notation InvP := (Inv bgusegs ghost FInvP).

Lemma ro_kept (m m' : word -> option byte) (a : Z) :
  mem_inv bgusegs m -> mem_inv bgusegs m' -> 65536 <= a < 921600 ->
  mrd bgusegs m' (wa a) = mrd bgusegs m (wa a) /\ (wview bgusegs m (wa a) <> None -> wview bgusegs m' (wa a) <> None).
Proof.
  intros MI MI' Ha. pose proof (ro_addr_seg0 a Ha) as Hro.
  assert (N : forall mm, mem_inv bgusegs mm -> mm (wa a) = None).
  { intros mm Hmm. destruct (mm (wa a)) as [b|] eqn:E; [|reflexivity]. pose proof (mem_inv_ro bgusegs mm _ _ Hmm E). congruence. }
  unfold mrd. rewrite (N m MI), (N m' MI'). split; [reflexivity|].
  intros Hw. exfalso. apply Hw. unfold wview. rewrite (N m MI). unfold ro_addr in Hro.
  destruct (find_segment bgusegs (bv_unsigned (wa a)) 1) as [sg|]; [|reflexivity]. destruct (seg_writable sg); [discriminate | reflexivity].
Qed.

Lemma ssp_kept (s s' : PState) (L L' : list block) (m m' : word -> option byte) (a : Z) :
  RHEAP s L m -> RHEAP s' L' m' -> (got_ssp <= a < got_ssp + 8 \/ ssp_guard <= a < ssp_guard + 8) ->
  mrd bgusegs m' (wa a) = mrd bgusegs m (wa a) /\ (wview bgusegs m (wa a) <> None -> wview bgusegs m' (wa a) <> None).
Proof.
  intros H H' Ha. destruct (RHEAP_ssp _ _ _ H) as [G1 G2]. destruct (RHEAP_ssp _ _ _ H') as [G1' G2'].
  assert (X : forall A (v : word), rw_cells bgusegs m A [C8 v] -> rw_cells bgusegs m' A [C8 v] -> A <= a < A + 8 ->
              mrd bgusegs m' (wa a) = mrd bgusegs m (wa a) /\ (wview bgusegs m (wa a) <> None -> wview bgusegs m' (wa a) <> None)).
  { intros A v [[_ (_ & _ & Hb)] _] [[_ (_ & _ & Hb')] (_ & _ & Hw')] HA.
    cbn [cells_bytes cbytes] in Hb, Hb'. rewrite app_nil_r in Hb, Hb'. rewrite length_le8 in Hb, Hb'. cbn [cells_size csize] in Hw'.
    specialize (Hb (Z.to_nat (a - A)) ltac:(lia)). specialize (Hb' (Z.to_nat (a - A)) ltac:(lia)).
    rewrite Z2Nat.id in Hb, Hb' by lia. replace (A + (a - A)) with a in Hb, Hb' by lia.
    split; [congruence|]. intros _. specialize (Hw' (a - A) ltac:(lia)). replace (A + (a - A)) with a in Hw' by lia. exact Hw'. }
  destruct Ha as [Ha|Ha]; [exact (X _ _ G1 G1' Ha) | exact (X _ _ G2 G2' Ha)].
Qed.

Lemma pres_kept (L : list block) (SP : Z) (m m' : word -> option byte) (a : Z) :
  rheap_pres L SP m m' -> 0 <= a < 2 ^ 64 -> rclient_addr L SP a ->
  mrd bgusegs m' (wa a) = mrd bgusegs m (wa a) /\ (wview bgusegs m (wa a) <> None -> wview bgusegs m' (wa a) <> None).
Proof. intros HP Ha Hc. destruct (HP a Ha Hc) as [E W]. split; [unfold mrd; rewrite E; reflexivity | exact W]. Qed.

Lemma old_region_kept (g : ghost) (rho rho2 : valuation) (cd : acd) (M : HxMem.mem) (nx : int) (m m' : word -> option byte)
    (s' : PState) (L' LBk : list block) (spc : Z) (rge : region) :
  FMemP g rho cd M nx m -> Rmem bgusegs rho2 M m -> agree_below nx rho rho2 ->
  mem_inv bgusegs m' -> RHEAP s' L' m' -> rheap_pres LBk spc m m' ->
  mget M T_ERRNO = Some rge -> rg_abs rge = Some ERRNO_INT -> rg_size rge = 4%uint63 -> rg_wr rge = true ->
  forall t3 rg3, mget M t3 = Some rg3 -> t3 <> 1%uint63 -> t3 <> T_ERRNO ->
    (forall k p3 n3, nth_error (rev (a_tags cd)) k = Some t3 -> nth_error (g_env g) k = Some (Some (p3, n3)) -> In (p3, rho t3, n3) LBk) ->
    bytes_kept bgusegs rho2 t3 rg3 m m'.
Proof.
  intros HF [HRg Hsep] Hag MI' Hheap' Hpres Ege Eae Ese Ewe t3 rg3 Eg3 Hn1 Hne Hblk i Hi.
  destruct HF as (Hops & Hlen & Hn & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & Hheap & Hrho1 & Hmi & Hstk & Haux & Hagr).
  destruct (HRg t3 rg3 Eg3) as (B0 & B1 & _). unfold two63 in B1.
  pose proof (Hcls t3 rg3 Eg3) as C. unfold rbase in *. destruct (rg_abs rg3) as [a0|] eqn:Ea.
  - destruct C as [(_ & C & _)|C]; [lia|]. destruct (static_facts _ _ _ C) as (S1 & S2 & S3 & _ & S5).
    destruct S5 as [[E1 E2]|[[E1 E2]|[[E1 [E2 E3]]|[E1 E2]]]].
    + exfalso. destruct (Hsep t3 T_ERRNO rg3 rge Eg3 Ege Hne (or_intror Ewe)) as [D|D]; unfold rbase in D; rewrite Ea, Eae, ?Ese in D;
        change (to_Z ERRNO_INT) with RMallocRep.RERRNO in D; change (to_Z 4%uint63) with 4 in D; lia.
    + apply ro_kept; [exact Hmi | exact MI' | lia].
    + eapply ssp_kept; [exact Hheap | exact Hheap' | lia].
    + apply (pres_kept LBk spc); [exact Hpres | lia |]. right; left. split; [lia | apply E2; lia].
  - destruct C as [[C _]|(k & p3 & n3 & Hk & He & Es)]; [contradiction|].
    assert (E3 : rho2 t3 = rho t3) by (apply Hag; exact (Htags t3 rg3 Eg3)).
    apply (pres_kept LBk spc); [exact Hpres | lia |]. right; right. exists (p3, rho t3, n3). split; [exact (Hblk k p3 n3 Hk He)|].
    cbn [blk_addr blk_size fst snd]. lia.
Qed.

Lemma stack_after_call (rho2 : valuation) (rgs : region) (o : int) (m m' : word -> option byte) (LBk : list block) :
  region_ok bgusegs rho2 1%uint63 rgs m -> rg_abs rgs = None -> rg_dflt rgs = DUnk -> rg_size rgs = STK -> rho2 1%uint63 = sp0 - to_Z STK ->
  to_Z o mod 8 = 0 -> to_Z o <= to_Z STK ->
  stk bgusegs m' lo (sp0 - to_Z STK + to_Z o) -> rheap_pres LBk (sp0 - to_Z STK + to_Z o) m m' ->
  region_ok bgusegs rho2 1%uint63 (drop_below rgs o) m'.
Proof.
  intros Hok Eabs Edf Esz Erho Ho8 Ho Hstk' Hpres. pose proof (region_mapped bgusegs rho2 _ rgs m Hok) as Hmap.
  pose proof Hok as (B0 & B1 & _). unfold two63 in B1. unfold rbase in *. rewrite Eabs in *. rewrite Esz, Erho in *.
  pose proof (to_Z_bounded o) as Bo.
  assert (KEPT : forall i, to_Z o <= i < to_Z STK ->
            mrd bgusegs m' (wa (sp0 - to_Z STK + i)) = mrd bgusegs m (wa (sp0 - to_Z STK + i))
            /\ (wview bgusegs m (wa (sp0 - to_Z STK + i)) <> None -> wview bgusegs m' (wa (sp0 - to_Z STK + i)) <> None)).
  { intros i Hi. apply (pres_kept LBk (sp0 - to_Z STK + to_Z o)); [exact Hpres | lia | left; lia]. }
  apply (region_ok_drop bgusegs rho2 1%uint63 rgs o m m' Hok Edf Ho8); unfold rbase; rewrite Eabs, ?Esz, Erho.
  - intros i Hi. destruct (Z_lt_le_dec i (to_Z o)) as [L|L].
    + destruct Hstk' as (_ & _ & Hs). destruct (Hs (sp0 - to_Z STK + i) ltac:(lia)) as [Hw Hb]. split; [exact Hb | intros _; exact Hw].
    + destruct (KEPT i ltac:(lia)) as [E W]. destruct (Hmap i Hi) as [[b Hb] Hw]. split; [exists b; rewrite E; exact Hb|].
      intros Hwr. apply W, Hw, Hwr.
  - intros i Hi. exact (proj1 (KEPT i Hi)).
Qed.

Lemma errno_after_call (rho2 : valuation) (rge : region) (m m' : word -> option byte) (errv' : word) :
  region_ok bgusegs rho2 T_ERRNO rge m -> rg_abs rge = Some ERRNO_INT -> rg_size rge = 4%uint63 ->
  rw_cells bgusegs m' RMallocRep.RERRNO [C4 errv'] ->
  region_ok bgusegs rho2 T_ERRNO (RG (rg_abs rge) (rg_size rge) (rg_al rge) (rg_wr rge) DUnk (rg_d rge) IEmpty) m'.
Proof.
  intros Hok Ea Es Herr. apply (region_ok_reset bgusegs rho2 T_ERRNO rge m m' Hok).
  unfold rbase. rewrite Ea, Es. change (to_Z ERRNO_INT) with RMallocRep.RERRNO. change (to_Z 4%uint63) with 4.
  intros i Hi. destruct (rw_C4_bytes bgusegs m' _ _ Herr i Hi) as [Hb Hw]. split; [exact Hb | intros _; exact Hw].
Qed.

Lemma new_block_apart (g : ghost) (rho rho2 : valuation) (cd : acd) (M : HxMem.mem) (nx : int) (m m' : word -> option byte)
    (s' : PState) (p : bptr) (A n : Z) (Lrest : list block) :
  FMemP g rho cd M nx m -> Rmem bgusegs rho2 M m -> agree_below nx rho rho2 ->
  RHEAP s' ((p, A, n) :: Lrest) m' ->
  forall t2 rg2, mget M t2 = Some rg2 ->
    (forall k p2 n2, nth_error (rev (a_tags cd)) k = Some t2 -> nth_error (g_env g) k = Some (Some (p2, n2)) -> In (p2, rho t2, n2) Lrest) ->
    A + n <= rbase rho2 t2 rg2 \/ rbase rho2 t2 rg2 + to_Z (rg_size rg2) <= A.
Proof.
  intros HF [HRg _] Hag Hheap' t2 rg2 Eg2 Hblk.
  destruct HF as (Hops & Hlen & Hn & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & Hheap & Hrho1 & Hmi & Hstk & Haux & Hagr).
  destruct (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ (p, A, n) Hheap' (or_introl eq_refl)) as (R1 & R2 & R3 & R4 & R5).
  cbn [blk_addr blk_size fst snd] in R1, R2, R3, R4, R5. unfold GLOBALS_TOP in H_lo2.
  pose proof (Hcls t2 rg2 Eg2) as C. unfold rbase. destruct (rg_abs rg2) as [a0|] eqn:Ea.
  - destruct C as [(C1 & C2 & _)|C]; [right; lia|]. destruct (static_facts _ _ _ C) as (S1 & S2 & S3 & _). lia.
  - destruct C as [[-> Es]|(k & p2 & n2 & Hk & He & Es)].
    + left. rewrite (Hag 1%uint63) by (change (to_Z 1%uint63) with 1; change (to_Z NEXT0) with 29 in Hnx0; lia). lia.
    + rewrite (Hag t2 (Htags t2 rg2 Eg2)), Es. pose proof (Hblk k p2 n2 Hk He) as Hin.
      assert (Hne : blk_id (p, A, n) <> blk_id (p2, rho t2, n2)).
      { pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ Hheap') as ND. cbn [map] in ND. apply List.NoDup_cons_iff in ND as [Hni _].
        intros E. apply Hni. cbn [blk_id fst] in E |- *. rewrite E. exact (in_map blk_id Lrest (p2, rho t2, n2) Hin). }
      destruct (RMalloc_ifaceP.RHEAP_blocks_disjoint_proof _ _ _ _ _ Hheap' (or_introl eq_refl) (or_intror Hin) Hne) as [D|D];
        cbn [blk_addr blk_size fst snd] in D; [left | right]; lia.
Qed.
Definition hkp_malloc := hk_at PC_MALLOC (hk_malloc_v T_ERRNO ERRNO_INT TPV 1).

Lemma hkp_malloc_ok : hook_ok' bgusegs ghost JP FInvP hkp_malloc.
Proof.
  intros g rho cd S cd' S' ms [HRn HF] Hh K.
  unfold hkp_malloc, hk_at in Hh. destruct (w_eqb (s_pc S) PC_MALLOC) eqn:Epc; [|discriminate].
  apply w_eqb_true_iff in Epc.
  unfold hk_malloc_v in Hh. destruct (tp_ok TPV S && sp_ok 1 S) eqn:Eg; [|discriminate].
  apply andb_prop in Eg as [Etp Esp].
  destruct (reset_errno T_ERRNO ERRNO_INT (s_mem S)) as [M1|] eqn:Ere; [|discriminate].
  unfold hk_malloc in Hh. cbn [s_pc s_regs s_resv s_mem s_abs s_next] in Hh.
  destruct (a_ops cd) as [|[[c n] x] rest] eqn:Eops; [discriminate|]. destruct c; try discriminate.
  unfold hk_return, clobber_stack, rget in Hh. cbn [s_pc s_regs s_resv s_mem s_abs s_next] in Hh.
  destruct (zval (rf_get vzero (s_regs S) X10)) as [n'|] eqn:Ea0; [|discriminate].
  destruct ((n =? n') && (0 <? n) && (n <? 4294967296)) eqn:En; [|discriminate].
  apply andb_prop in En as [En En3]. apply andb_prop in En as [En1 En2].
  apply Z.eqb_eq in En1. subst n'. apply Z.ltb_lt in En2, En3.
  destruct (rf_get vzero (s_regs S) X1) as [ra| | |] eqn:Era; try discriminate.
  destruct (rf_get vzero (s_regs S) X2) as [|ts o| |] eqn:Esp2; try discriminate.
  destruct (wh o) eqn:Eho; [discriminate|].
  set (t := s_next S) in *. set (M2 := new_region M1 t (of_Z n) 4 DUnk) in *.
  destruct (mget M2 ts) as [rgs|] eqn:Egs; [|discriminate].
  destruct (rg_abs rgs) eqn:Eabs; [discriminate|]. destruct (rg_dflt rgs) eqn:Edf; try discriminate.
  destruct ((wl o land 15 =? 0)%uint63 && (HK_STACK <=? wl o)%uint63 && (wl o <=? rg_size rgs)%uint63 && rg_wr rgs) eqn:Eck; [|discriminate].
  destruct (s_resv S) eqn:Erv; try discriminate.
  injection Hh as <- <-.

  destruct HF as [HM (Hfr & Hfc & Hro & Hnf & Hps)].
  pose proof (Rn_R bgusegs rho S ms HRn) as (Hsvc & Hpc & HRg & Hrv & HRm).
  destruct Hnf as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20
                   & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & Eregs).
  rewrite Erv in Hrv. cbn [Rresv] in Hrv.
  assert (Ems : ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F0 (wbv PC_MALLOC) fc0 None (ms_mem ms) (seg_rom bgusegs)).
  { rewrite (MS_eta ms Hsvc) at 1. rewrite Eregs, Hfr, Hfc, Hro, Hrv, Hpc, Epc. reflexivity. }
  unfold core_of in HRg. rewrite Eregs in HRg.
  set (m := ms_mem ms) in *. clearbody m. clear Hsvc Hpc Hrv Hfr Hfc Hro Eregs. subst ms.
  destruct (nf_regs rho S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HRg) as (D1 & D2 & D4 & D10 & _ & _).
  unfold rget in D1, D2, D4, D10. rewrite Era in D1. rewrite Esp2 in D2.
  unfold tp_ok, rget in Etp. destruct (rf_get vzero (s_regs S) X4) as [tpw| | |] eqn:Etp4; try discriminate.
  apply w_eqb_true_iff in Etp. subst tpw.
  unfold sp_ok, rget in Esp. rewrite Esp2 in Esp. apply Uint63.eqb_spec in Esp. subst ts.
  unfold zval in Ea0. destruct (rf_get vzero (s_regs S) X10) as [a0w| | |] eqn:Ea10; try discriminate. injection Ea0 as Ea0.
  cbn [den] in D1, D2, D4, D10.

  pose proof HM as (Hops & Hlen & Hn & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & Hheap & Hrho1 & Hmi & Hstk & Haux & Hagr).
  fold t in Htl, Htags, Hnx0, Hnx.
  assert (Ht20 : to_Z t < to_Z TAGLIM) by (change (to_Z TAGLIM) with (2 ^ 20); lia).
  assert (Ht29 : 29 <= to_Z t) by (change (to_Z NEXT0) with 29 in Hnx0; lia).

  destruct (reset_errno_inv _ _ _ _ Ere) as (rge & Ege & Eae & Ede & Ese & Ewe & EM1).
  set (rge' := RG (rg_abs rge) (rg_size rge) (rg_al rge) (rg_wr rge) DUnk (rg_d rge) IEmpty) in *.
  assert (Egs1 : mget M1 1 = Some rgs).
  { unfold M2 in Egs. rewrite new_region_eq in Egs. rewrite mget_mset in Egs by exact Ht20.
    destruct (Z.eqb_spec (to_Z t) (to_Z 1%uint63)) as [E|E]; [change (to_Z 1%uint63) with 1 in E; lia | exact Egs]. }
  assert (Egs0 : mget (s_mem S) 1 = Some rgs).
  { rewrite EM1 in Egs1. rewrite mget_mset in Egs1 by (exact (mget_lt _ _ _ Ege)).
    destruct (Z.eqb_spec (to_Z T_ERRNO) (to_Z 1%uint63)) as [E|E]; [discriminate E | exact Egs1]. }
  assert (Essz : rg_size rgs = STK).
  { pose proof (Hcls 1%uint63 rgs Egs0) as C. rewrite Eabs in C. destruct C as [[_ C]|(k & p & n0 & Hk & _)]; [exact C|].
    exfalso. apply nth_error_In in Hk. specialize (Htl _ Hk). change (to_Z NEXT0) with 29 in Htl. change (to_Z 1%uint63) with 1 in Htl. lia. }
  apply andb_prop in Eck as [Eck Ewr]. apply andb_prop in Eck as [Eck Eo3]. apply andb_prop in Eck as [Eo1 Eo2].
  apply Uint63.eqb_spec in Eo1. apply leb_spec in Eo2, Eo3. rewrite Essz in Eo3. change (to_Z HK_STACK) with 16384 in Eo2.
  pose proof STK_Z as ESTK. pose proof (to_Z_bounded (wl o)) as Bo.
  assert (EwZo : wZ o = to_Z (wl o)) by (unfold wZ; rewrite Eho; lia).
  assert (Eo16 : to_Z (wl o) mod 16 = 0).
  { pose proof (f_equal to_Z Eo1) as E. rewrite land_spec' in E. change (to_Z 15%uint63) with (Z.ones 4) in E.
    rewrite Z.land_ones in E by lia. exact E. }
  set (spc := sp0 - to_Z STK + to_Z (wl o)).
  assert (Esp : bv_unsigned x2 = spc).
  { rewrite D2. unfold pword. rewrite Z_to_bv_unsigned, Hrho1, EwZo. apply bv_wrap_small. unfold bv_modulus. unfold GLOBALS_TOP in H_lo2. lia. }

  assert (Herr : exists errv : word, rw_cells bgusegs m RMallocRep.RERRNO [C4 errv]).
  { destruct HRm as [HRg0 _]. pose proof (region_mapped bgusegs rho T_ERRNO rge m (HRg0 _ _ Ege)) as Hb.
    unfold rbase in Hb. rewrite Eae, Ese in Hb. change (to_Z ERRNO_INT) with RMallocRep.RERRNO in Hb. change (to_Z 4%uint63) with 4 in Hb.
    apply bytes_rw_C4; [unfold RMallocRep.RERRNO; lia | unfold RMallocRep.RERRNO; lia|].
    intros i Hi. destruct (Hb i Hi) as [Hm Hw]. split; [exact Hm | exact (Hw Ewe)]. }
  destruct Herr as [errv Herr].

  unfold J. rewrite Hops, Eops. cbn [map dec_op Z.eqb run_ops lbind].
  eapply implM_interp_malloc.
  { eapply (MALLOC x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
                           F0 fc0 m (g_s g) _ n lo B errv Hheap Haux).
    - rewrite Esp. unfold spc. lia.
    - rewrite Esp. exact (proj1 (stk_split bgusegs _ lo spc sp0 Hstk ltac:(unfold spc; lia))).
    - exact H_lo1.
    - rewrite Esp. unfold spc, RMALLOC_STACK. lia.
    - rewrite D4. change (bv_unsigned (wbv TPV) + -164) with RMallocRep.RERRNO. exact Herr.
    - exact Hmi.
    - rewrite D4. reflexivity.
    - rewrite D10. apply bv_eq. rewrite wbv_unsigned, Ea0, Z_to_bv_unsigned. symmetry. apply bv_wrap_small. unfold bv_modulus. lia.
    - lia. }
  intros r s' ms' HP. destruct r as [p|]; [|cbn [lbind]; apply implM_interp_unr].
  destruct HP as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & Ems' & Hmi' & Hstk'
                  & Herr' & Haux' & Hpres & Hfa & Hso & A & junk & Ea0' & Hrange & Hheap' & Hblk & _).
  rewrite Esp in Hstk', Hpres. rewrite D4 in Herr'. change (bv_unsigned (wbv TPV) + -164) with RMallocRep.RERRNO in Herr'.
  destruct Hrange as (R1 & R2 & R3 & R4 & R5).
  set (rho' := fun t' : int => if (t' =? t)%uint63 then A else rho t').
  assert (Hag' : agree_below t rho rho').
  { intros t' Ht'. unfold rho'. destruct (t' =? t)%uint63 eqn:E; [apply Uint63.eqb_spec in E; subst t'; lia | reflexivity]. }
  assert (Erho't : rho' t = A) by (unfold rho'; rewrite Uint63.eqb_refl; reflexivity).
  assert (Et1 : to_Z (t + 1)%uint63 = to_Z t + 1).
  { rewrite add_spec. change (to_Z 1%uint63) with 1. apply Z.mod_small. rewrite wB_eq. unfold two63. change (to_Z TAGLIM) with (2 ^ 20) in Ht20. lia. }
  apply (K (GH s' (g_env g ++ [Some (p, n)]) (map dec_op rest)) rho' ms' Hag').
  subst ms'. split.
  -
    intros rho2 Hag2. cbn [s_next] in Hag2.
    assert (Hag02 : agree_below t rho rho2).
    { intros t' Ht'. rewrite (Hag2 t') by (rewrite Et1; lia). apply Hag'. exact Ht'. }
    assert (Erho2t : rho2 t = A) by (rewrite (Hag2 t) by (rewrite Et1; lia); exact Erho't).
    assert (Erho21 : rho2 1%uint63 = sp0 - to_Z STK) by (rewrite (Hag02 1%uint63) by (change (to_Z 1%uint63) with 1; lia); exact Hrho1).
    pose proof (HRn rho2 Hag02) as (_ & _ & HRg2 & _ & HRm2). change (Rmem bgusegs rho2 (s_mem S) m) in HRm2.
    pose proof HRm2 as [HRok2 Hsep2].
    unfold R. cbn [ms_svc_pending ms_pc_val ms_resv ms_mem MS s_pc s_regs s_resv s_mem].
    split; [reflexivity|]. split; [rewrite D1; apply ret_pc_wbv|]. split.
    { unfold core_of in HRg2 |- *. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv MS] in HRg2 |- *.
      eapply (Rregs_return rho2 (s_regs S) (VP t w_zero)); [exact HRg2|].
      cbn [den]. unfold pword. rewrite Erho2t. rewrite Ea0'. f_equal. change (wZ w_zero) with 0. lia. }
    split; [reflexivity|].
    split.
    + intros t3 rg3 G3.
      destruct (mget_mset_cases M2 1%uint63 t3 _ rg3 ltac:(change (to_Z 1%uint63) with 1; change (to_Z TAGLIM) with (2 ^ 20); lia) G3) as [[-> ->]|[N1 G3']].
      * apply (stack_after_call rho2 rgs (wl o) m m' (live_blocks rho (rev (a_tags cd)) (g_env g) ++ LB) (HRok2 _ _ Egs0) Eabs Edf Essz Erho21); try exact Hstk'; try exact Hpres; [|lia].
        pose proof (Z.mod_divide (to_Z (wl o)) 16 ltac:(lia)) as [X _]. destruct (X Eo16) as [q Eq]. rewrite Eq.
        replace (q * 16) with ((q * 2) * 8) by ring. apply Z.mod_mul. lia.
      * unfold M2 in G3'. rewrite new_region_eq in G3'. destruct (mget_mset_cases M1 t t3 _ rg3 Ht20 G3') as [[-> ->]|[N2 G3'']].
        -- assert (En62 : to_Z (of_Z n) = n) by (apply of_Z_small; lia).
           destruct (depth_for_ok (of_Z n) ltac:(rewrite En62; lia)) as [Hd1 Hd2].
           apply region_ok_fresh; unfold rbase; cbn [rg_abs]; rewrite ?En62, ?Erho2t; try assumption; try lia.
           ++ unfold two63. lia.
           ++ change (to_Z 4%uint63) with 4. lia.
           ++ intros i Hi. destruct (rw_CB_bytes bgusegs m' A _ _ Hblk i ltac:(lia)) as [Hb Hw]. split; [exact Hb | intros _; exact Hw].
        -- rewrite EM1 in G3''. destruct (mget_mset_cases (s_mem S) T_ERRNO t3 _ rg3 (mget_lt _ _ _ Ege) G3'') as [[-> ->]|[N3 G3''']].
           ++ exact (errno_after_call rho2 rge m m' errv' (HRok2 _ _ Ege) Eae Ese Herr').
           ++ apply (region_ok_frame bgusegs rho2 t3 rg3 m m' (HRok2 _ _ G3''')).
              apply (old_region_kept g rho rho2 cd (s_mem S) t m m' s' _ _ _ rge HM HRm2 Hag02 Hmi' Hheap' Hpres Ege Eae Ese Ewe t3 rg3 G3''' N1 N3).
              intros k p3 n3 Hk He. apply in_or_app. left. exact (live_blocks_in rho _ _ k t3 p3 n3 Hk He).
    +
      assert (Sep1 : regions_sep rho2 M1).
      { rewrite EM1. apply (regions_sep_mset_same rho2 (s_mem S) T_ERRNO rge rge' Ege); [|exact Hsep2]. unfold rge'. repeat split. cbn [rg_dflt]. symmetry. exact Ede. }
      assert (Hfresh : mget M1 t = None).
      { rewrite EM1. rewrite mget_mset by exact (mget_lt _ _ _ Ege). destruct (Z.eqb_spec (to_Z T_ERRNO) (to_Z t)) as [E|E]; [change (to_Z T_ERRNO) with 9 in E; lia|].
        destruct (mget (s_mem S) t) as [rgx|] eqn:Ex; [|reflexivity]. pose proof (Htags t rgx Ex). lia. }
      apply (regions_sep_mset_same rho2 M2 1%uint63 rgs (drop_below rgs (wl o)) Egs); [repeat split|].
      unfold M2. rewrite new_region_eq. apply (regions_sep_new rho2 M1 t _ Sep1 Hfresh Ht20).
      intros t2 rg2 G2.
      assert (EB : rbase rho2 t (RG None (of_Z n) 4 true DUnk (depth_for 60 (of_Z n) 0) IEmpty) = A) by (unfold rbase; cbn [rg_abs]; exact Erho2t).
      rewrite EB. cbn [rg_size]. rewrite of_Z_small by lia.
      assert (X : forall rgx, mget (s_mem S) t2 = Some rgx -> A + n <= rbase rho2 t2 rgx \/ rbase rho2 t2 rgx + to_Z (rg_size rgx) <= A).
      { intros rgx Gx. apply (new_block_apart g rho rho2 cd (s_mem S) t m m' s' p A n _ HM HRm2 Hag02 Hheap' t2 rgx Gx).
        intros k p2 n2 Hk He. apply in_or_app. left. exact (live_blocks_in rho _ _ k t2 p2 n2 Hk He). }
      rewrite EM1 in G2. destruct (mget_mset_cases (s_mem S) T_ERRNO t2 _ rg2 (mget_lt _ _ _ Ege) G2) as [[-> ->]|[N3 G2']]; [exact (X rge Ege) | exact (X rg2 G2')].
  -
    split; [|cbn [ms_fregs ms_fcsr ms_rom ms_regs MS g_s]; repeat (split; [reflexivity|]); split; [do 31 eexists; reflexivity | destruct Hps as [P1 P2]; split; congruence]].
    unfold FMem. cbn [a_ops a_tags a_n g_s g_env g_ops s_mem s_next ms_mem MS rev]. change (to_Z NEXT0) with 29 in *.
    set (tl := rev (a_tags cd)) in *. set (newrg := RG None (of_Z n) 4 true DUnk (depth_for 60 (of_Z n) 0) IEmpty).
    assert (Hcases : forall t3 rg3, mget (mset M2 1 (drop_below rgs (wl o))) t3 = Some rg3 ->
              (t3 = 1%uint63 /\ rg3 = drop_below rgs (wl o)) \/ (t3 = t /\ rg3 = newrg) \/ (t3 = T_ERRNO /\ rg3 = rge')
              \/ (t3 <> 1%uint63 /\ t3 <> t /\ t3 <> T_ERRNO /\ mget (s_mem S) t3 = Some rg3)).
    { intros t3 rg3 G3.
      destruct (mget_mset_cases M2 1%uint63 t3 _ rg3 ltac:(change (to_Z 1%uint63) with 1; change (to_Z TAGLIM) with (2 ^ 20); lia) G3) as [[-> ->]|[N1 G3']]; [left; auto|].
      unfold M2 in G3'. rewrite new_region_eq in G3'. destruct (mget_mset_cases M1 t t3 _ rg3 Ht20 G3') as [[-> ->]|[N2 G3'']]; [right; left; auto|].
      rewrite EM1 in G3''. destruct (mget_mset_cases (s_mem S) T_ERRNO t3 _ rg3 (mget_lt _ _ _ Ege) G3'') as [[-> ->]|[N3 G3''']]; [right; right; left; auto|].
      right; right; right. auto. }
    split; [reflexivity|].
    split; [rewrite !length_app; cbn [length]; lia|].
    split; [rewrite length_app; cbn [length]; lia|].
    split.
    { apply (Permutation_NoDup (l := t :: tl)); [apply Permutation_cons_append|]. constructor; [|exact Hnd].
      intros Hin. specialize (Htl t Hin). lia. }
    split.
    { intros t' Hin. apply in_app_or in Hin. destruct Hin as [Hin|[<-|[]]]; [specialize (Htl t' Hin); lia | lia]. }
    split.
    { intros t3 rg3 G3. destruct (Hcases t3 rg3 G3) as [[-> _]|[[-> _]|[[-> _]|(_ & _ & _ & G)]]].
      - change (to_Z 1%uint63) with 1. lia.
      - lia.
      - change (to_Z T_ERRNO) with 9. lia.
      - specialize (Htags t3 rg3 G). lia. }
    split; [lia|]. split; [rewrite Eops in Hnx; cbn [length] in Hnx; lia|].
    split.
    { intros t3 rg3 G3. destruct (Hcases t3 rg3 G3) as [[-> ->]|[[-> ->]|[[-> ->]|(N1 & N2 & N3 & G)]]].
      - cbn [drop_below rg_abs rg_size]. rewrite Eabs. left. split; [reflexivity | exact Essz].
      - cbn [newrg rg_abs rg_size]. right. exists (length tl), p, n.
        split; [rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity|].
        split; [rewrite nth_error_app2 by lia; rewrite Hlen, Nat.sub_diag; reflexivity|]. apply of_Z_small. lia.
      - pose proof (Hcls T_ERRNO rge Ege) as C. rewrite Eae in C. cbn [rge' rg_abs rg_size rg_wr]. rewrite Eae. exact C.
      - pose proof (Hcls t3 rg3 G) as C. destruct (rg_abs rg3); [exact C|]. destruct C as [C|(k & p3 & n3 & Hk & He & Es)]; [left; exact C|].
        right. exists k, p3, n3. split; [rewrite nth_error_app1 by (apply nth_error_Some; congruence); exact Hk|].
        split; [rewrite nth_error_app1 by (apply nth_error_Some; congruence); exact He | exact Es]. }
    split.
    { intros k0 t3 p3 n3 Hk He.
      assert (Hnew : mget (mset M2 1 (drop_below rgs (wl o))) t = Some newrg).
      { rewrite mget_mset by (change (to_Z 1%uint63) with 1; change (to_Z TAGLIM) with (2 ^ 20); lia).
        destruct (Z.eqb_spec (to_Z 1%uint63) (to_Z t)) as [E|E]; [change (to_Z 1%uint63) with 1 in E; lia|].
        unfold M2. rewrite new_region_eq. rewrite mget_mset by exact Ht20. rewrite Z.eqb_refl. reflexivity. }
      destruct (Nat.lt_ge_cases k0 (length tl)) as [L|L].
      - rewrite nth_error_app1 in Hk by exact L. rewrite nth_error_app1 in He by lia.
        destruct (Hlink k0 t3 p3 n3 Hk He) as (rg3 & G3 & Ea3 & Es3 & Ew3). exists rg3. repeat split; try assumption.
        assert (N1 : t3 <> 1%uint63) by (intros ->; apply nth_error_In in Hk; specialize (Htl _ Hk); change (to_Z 1%uint63) with 1 in Htl; lia).
        assert (N2 : t3 <> t) by (intros ->; apply nth_error_In in Hk; specialize (Htl _ Hk); lia).
        assert (N3 : t3 <> T_ERRNO) by (intros ->; apply nth_error_In in Hk; specialize (Htl _ Hk); change (to_Z T_ERRNO) with 9 in Htl; lia).
        rewrite mget_mset by (change (to_Z 1%uint63) with 1; change (to_Z TAGLIM) with (2 ^ 20); lia).
        destruct (Z.eqb_spec (to_Z 1%uint63) (to_Z t3)) as [E|E]; [apply to_Z_inj in E; congruence|].
        unfold M2. rewrite new_region_eq. rewrite mget_mset by exact Ht20.
        destruct (Z.eqb_spec (to_Z t) (to_Z t3)) as [E'|E']; [apply to_Z_inj in E'; congruence|].
        rewrite EM1. rewrite mget_mset by exact (mget_lt _ _ _ Ege).
        destruct (Z.eqb_spec (to_Z T_ERRNO) (to_Z t3)) as [E''|E'']; [apply to_Z_inj in E''; congruence | exact G3].
      - rewrite nth_error_app2 in Hk by exact L. rewrite nth_error_app2 in He by lia. rewrite Hlen in He.
        destruct (k0 - length tl)%nat as [|j] eqn:Ej; [|destruct j; discriminate]. cbn in Hk, He. injection Hk as <-. injection He as <- <-.
        exists newrg. split; [exact Hnew|]. cbn [newrg rg_abs rg_size rg_wr]. repeat split. apply of_Z_small. lia. }
    split.
    { rewrite live_blocks_snoc by exact Hlen. rewrite Erho't.
      rewrite (live_blocks_agree rho rho') by (intros t' Hin; apply Hag'; specialize (Htl t' Hin); lia).
      eapply RHEAP_perm; [exact Hheap'|]. rewrite <- app_assoc. cbn [app]. apply Permutation_middle. }
    split; [rewrite (Hag' 1%uint63) by (change (to_Z 1%uint63) with 1; lia); exact Hrho1|].
    split; [exact Hmi'|].
    split.
    { apply (stk_merge bgusegs m' lo spc sp0 Hstk'); [|unfold spc; lia].
      apply (rheap_pres_stk _ spc m m' spc sp0 Hpres); [|lia]. exact (proj2 (stk_split bgusegs _ lo spc sp0 Hstk ltac:(unfold spc; lia))). }
    split; [exact Haux'|].
    eapply agree_on_trans; [exact Hagr|]. eapply agree_on_mono; [exact (agree_of_heap_pres _ _ _ _ Hpres)|].
    intros a [_ Hc]. destruct Hc as [Hc|[(b & Hb & Hr)|Hc]]; [left; unfold spc; lia | right; right; exists b; split; [apply in_or_app; right; exact Hb | exact Hr] | right; left; exact Hc].
Qed.

Lemma inv_nf (g : ghost) (rho : valuation) (cd : acd) (S : sstate) (ms : machine_state) :
  InvP g rho cd S ms -> s_resv S = RNone ->
  exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F0 (wbv (s_pc S)) fc0 None (ms_mem ms) (seg_rom bgusegs).
Proof.
  intros [HRn [_ (Hfr & Hfc & Hro & Hnf & _)]] Erv. pose proof (Rn_R bgusegs rho S ms HRn) as (Hsvc & Hpc & _ & Hrv & _).
  destruct Hnf as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20
                   & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & Eregs).
  rewrite Erv in Hrv. cbn [Rresv] in Hrv.
  exists x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31.
  rewrite (MS_eta ms Hsvc) at 1. rewrite Eregs, Hfr, Hfc, Hro, Hrv, Hpc. reflexivity.
Qed.

Definition hkp_free := hk_at PC_FREE hk_free_null.

Lemma hkp_free_ok : hook_ok' bgusegs ghost JP FInvP hkp_free.
Proof.
  intros g rho cd S cd' S' ms HI Hh K.
  unfold hkp_free, hk_at in Hh. destruct (w_eqb (s_pc S) PC_FREE) eqn:Epc; [|discriminate]. apply w_eqb_true_iff in Epc.
  unfold hk_free_null in Hh. destruct (rget S X10) as [w| | |] eqn:Ea; try discriminate. destruct (is_zero w) eqn:Ez; [|discriminate].
  apply is_zero_spec in Ez. subst w.
  destruct (hk_return S VU (s_mem S) (s_next S)) as [S1|] eqn:Ehr; [|discriminate]. injection Hh as <- <-.
  destruct (hk_return_inv _ _ _ _ _ Ehr) as (ra & M' & Era & Ecl & Erv & ->).
  destruct (clobber_stack_inv _ _ _ Ecl) as (ts & o & rgs & Esp & Eho & Egs & Eabs & Edf & Eo16 & Eo & Ewr & ->).
  destruct (inv_nf g rho cd S ms HI Erv) as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20
                   & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & Ems).
  set (m := ms_mem ms) in *. clearbody m. subst ms. destruct HI as [HRn [HM (_ & _ & _ & _ & Hps)]]. rewrite Epc in *.
  pose proof (Rn_R bgusegs rho S _ HRn) as (_ & _ & HRg & _ & _). unfold core_of in HRg. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv MS] in HRg.
  destruct (nf_regs rho S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HRg) as (D1 & _ & _ & D10 & _ & _).
  rewrite Era in D1. rewrite Ea in D10. cbn [den] in D1, D10.
  assert (Eo8 : to_Z (wl o) mod 8 = 0).
  { pose proof (Z.mod_divide (to_Z (wl o)) 16 ltac:(lia)) as [X _]. destruct (X Eo16) as [q Eq]. rewrite Eq.
    replace (q * 16) with ((q * 2) * 8) by ring. apply Z.mod_mul. lia. }
  apply J_evt. eapply evt_mono.
  { apply (rfree_null_spec x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F0 fc0 m).
    rewrite D10. exact wbv_zero. }
  intros ms' ->. apply (K g rho _ (agree_below_refl _ _)). split.
  - intros rho2 Hag2. cbn [s_next] in Hag2. pose proof (HRn rho2 Hag2) as (_ & _ & HRg2 & _ & HRm2).
    unfold core_of in HRg2. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem MS] in HRg2, HRm2.
    eapply R_return; [exact HRg2 | exact D1 | exact I |]. exact (Rmem_clobber bgusegs rho2 _ ts rgs (wl o) m HRm2 Egs Edf Eo8).
  - split; [|cbn [ms_fregs ms_fcsr ms_rom ms_regs MS]; repeat (split; [reflexivity|]); split; [do 31 eexists; reflexivity | exact Hps]].
    cbn [s_mem s_next ms_mem MS] in HM |- *. eapply FMem_dirs; [exact HM|]. exact (same_dirs_mset _ ts rgs _ Egs (same_dir_drop_below rgs (wl o))).
Qed.

Definition hkp_memset := hk_at PC_MEMSET (@hk_memset8 acd).

Lemma hkp_memset_ok : hook_ok' bgusegs ghost JP FInvP hkp_memset.
Proof.
  intros g rho cd S cd' S' ms HI Hh K.
  unfold hkp_memset, hk_at in Hh. destruct (w_eqb (s_pc S) PC_MEMSET) eqn:Epc; [|discriminate]. apply w_eqb_true_iff in Epc.
  unfold hk_memset8 in Hh.
  destruct (rget S X10) as [|t o| |] eqn:Ea0; try discriminate. destruct (rget S X11) as [c| | |] eqn:Ea1; try discriminate.
  destruct (rget S X12) as [n| | |] eqn:Ea2; try discriminate. destruct (wh o || wh n) eqn:Eh; [discriminate|].
  apply orb_false_elim in Eh as [Eho Ehn].
  destruct (mget (s_mem S) t) as [rg|] eqn:Eg; [|discriminate]. destruct (rg_abs rg) eqn:Eabs; [discriminate|].
  destruct ((wl o land 7 =? 0)%uint63 && (wl n land 7 =? 0)%uint63 && (wl o <=? rg_size rg)%uint63 && (wl n <=? rg_size rg)%uint63
            && (wl o + wl n <=? rg_size rg)%uint63 && rg_wr rg) eqn:Eck; [|discriminate].
  apply andb_prop in Eck as [Eck Ewr]. apply andb_prop in Eck as [Eck Ec5]. apply andb_prop in Eck as [Eck Ec4].
  apply andb_prop in Eck as [Eck Ec3]. apply andb_prop in Eck as [Ec1 Ec2].
  apply Uint63.eqb_spec in Ec1, Ec2. apply leb_spec in Ec3, Ec4, Ec5. cbv zeta in Hh.
  set (rg' := RG None (rg_size rg) (rg_al rg) (rg_wr rg) (rg_dflt rg) (rg_d rg)
                 (fill_cells (rg_d rg) (rg_cells rg) (wl o >> 3)%uint63 (Z.to_nat (to_Z (wl n >> 3)%uint63)) (rep8 (wl c)))) in *.
  destruct (hk_return S (VP t o) (mset (s_mem S) t rg') (s_next S)) as [S1|] eqn:Ehr; [|discriminate]. injection Hh as <- <-.
  destruct (hk_return_inv _ _ _ _ _ Ehr) as (ra & M' & Era & Ecl & Erv & ->).
  destruct (clobber_stack_inv _ _ _ Ecl) as (ts & os & rgs & Esp & Ehos & Egs & Eabss & Edfs & Eo16 & Eos & Ewrs & ->).
  destruct (inv_nf g rho cd S ms HI Erv) as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20
                   & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & Ems).
  set (m := ms_mem ms) in *. clearbody m. subst ms. destruct HI as [HRn [HM (_ & _ & _ & _ & Hps)]]. rewrite Epc in *.
  pose proof (Rn_R bgusegs rho S _ HRn) as (_ & _ & HRg & _ & HRm). unfold core_of in HRg. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem MS] in HRg, HRm.
  destruct (nf_regs rho S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HRg) as (D1 & _ & _ & D10 & D11 & D12).
  rewrite Era in D1. rewrite Ea0 in D10. rewrite Ea1 in D11. rewrite Ea2 in D12. cbn [den] in D1, D10, D11, D12.

  pose proof (to_Z_bounded (wl o)) as Bo. pose proof (to_Z_bounded (wl n)) as Bn. pose proof (to_Z_bounded (rg_size rg)) as Bs.
  destruct (proj1 HRm t rg Eg) as (B0 & B1 & B2 & B3 & B4 & _). unfold two63 in B1. unfold rbase in B0, B1. rewrite Eabs in B0, B1.
  assert (Eon : to_Z (wl o + wl n)%uint63 = to_Z (wl o) + to_Z (wl n)) by (rewrite add_spec; apply Z.mod_small; rewrite wB_eq; unfold two63; lia).
  rewrite Eon in Ec5.
  assert (Eo8 : to_Z (wl o) mod 8 = 0) by (rewrite <- phi_land7, Ec1; reflexivity).
  assert (En8 : to_Z (wl n) mod 8 = 0) by (rewrite <- phi_land7, Ec2; reflexivity).
  assert (EwZo : wZ o = to_Z (wl o)) by (unfold wZ; rewrite Eho; lia).
  assert (EwZn : wZ n = to_Z (wl n)) by (unfold wZ; rewrite Ehn; lia).
  set (A := rho t + to_Z (wl o)).
  assert (EA : bv_unsigned x10 = A).
  { rewrite D10. unfold pword. rewrite Z_to_bv_unsigned, EwZo. apply bv_wrap_small. unfold bv_modulus. fold A. unfold A. lia. }
  assert (EN : bv_unsigned x12 = to_Z (wl n)) by (rewrite D12, wbv_unsigned; exact EwZn).
  pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmi & _).
  assert (Hmap : forall i, 0 <= i < to_Z (wl n) -> (exists b, mrd bgusegs m (wa (A + i)) = Some b) /\ wview bgusegs m (wa (A + i)) <> None).
  { intros i Hi. destruct (region_mapped bgusegs rho t rg m (proj1 HRm t rg Eg) (to_Z (wl o) + i) ltac:(lia)) as [Hb Hw].
    unfold rbase in Hb, Hw. rewrite Eabs in Hb, Hw. unfold A. rewrite <- Z.add_assoc. split; [exact Hb | exact (Hw Ewr)]. }
  destruct (bytes_rw_CB bgusegs m A (Z.to_nat (to_Z (wl n))) ltac:(unfold A; lia) ltac:(rewrite Z2Nat.id by lia; unfold A; lia)) as [junk Hjunk].
  { intros i Hi. apply Hmap. lia. }
  apply J_evt. eapply evt_mono.
  { apply (memset_spec x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F0 fc0 m junk);
      [rewrite EA, EN; exact Hjunk | exact Hmi]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & RW).
  rewrite EA, EN in MU, RW.
  assert (Hmap' : forall i, 0 <= i < to_Z (wl n) -> mrd bgusegs m' (wa (A + i)) = Some (Z_to_bv 8 (bv_unsigned x11 mod 256)) /\ wview bgusegs m' (wa (A + i)) <> None).
  { intros i Hi. destruct RW as [[_ (_ & _ & Hb)] (_ & _ & Hw)]. cbn [cells_bytes cbytes cells_size csize] in Hb, Hw. rewrite app_nil_r, repeat_length in Hb.
    rewrite Nat.add_0_r, Z2Nat.id in Hw by lia. split; [|apply Hw; lia].
    specialize (Hb (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in Hb by lia. rewrite Hb. apply nth_error_repeat. lia. }
  assert (Hout : forall a, 0 <= a < 2 ^ 64 -> ~ (A <= a < A + to_Z (wl n)) ->
            mrd bgusegs m' (wa a) = mrd bgusegs m (wa a) /\ (wview bgusegs m (wa a) <> None -> wview bgusegs m' (wa a) <> None)).
  { intros a Ha Hna. split; [|apply WM]. unfold mrd. rewrite MU; [reflexivity|]. rewrite wa_unsigned by lia. cbn [outside]. split; [exact Hna | exact I]. }
  assert (Eo8s : to_Z (wl os) mod 8 = 0).
  { pose proof (Z.mod_divide (to_Z (wl os)) 16 ltac:(lia)) as [X _]. destruct (X Eo16) as [q Eq]. rewrite Eq.
    replace (q * 16) with ((q * 2) * 8) by ring. apply Z.mod_mul. lia. }
  assert (Hsd : same_dir rg rg') by (repeat split; cbn [rg' rg_abs]; symmetry; exact Eabs).
  apply (K g rho _ (agree_below_refl _ _)). split.
  -
    intros rho2 Hag2. cbn [s_next] in Hag2. pose proof (HRn rho2 Hag2) as (_ & _ & HRg2 & _ & HRm2).
    unfold core_of in HRg2. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem MS] in HRg2, HRm2.
    destruct (nf_regs rho2 S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HRg2) as (_ & _ & _ & D10' & _ & _).
    rewrite Ea0 in D10'.
    eapply R_return; [exact HRg2 | exact D1 | exact D10' |].
    apply (Rmem_clobber bgusegs rho2 _ ts rgs (wl os) m'); [|exact Egs | exact Edfs | exact Eo8s].
    assert (Et : rho2 t = rho t).
    { apply Hag2. destruct HM as (_ & _ & _ & _ & _ & Htags & _). exact (Htags t rg Eg). }
    assert (EB : rbase rho2 t rg = rho t) by (unfold rbase; rewrite Eabs; exact Et).
    assert (Erg' : rg' = RG (rg_abs rg) (rg_size rg) (rg_al rg) (rg_wr rg) (rg_dflt rg) (rg_d rg)
                            (fill_cells (rg_d rg) (rg_cells rg) (wl o >> 3)%uint63 (Z.to_nat (to_Z (wl n >> 3)%uint63)) (rep8 (wl c))))
      by (unfold rg'; rewrite Eabs; reflexivity).
    assert (Ek0 : 8 * to_Z (wl o >> 3)%uint63 = to_Z (wl o)) by (rewrite phi_shr3; pose proof (Z.div_mod (to_Z (wl o)) 8 ltac:(lia)); lia).
    assert (Ecnt : 8 * Z.of_nat (Z.to_nat (to_Z (wl n >> 3)%uint63)) = to_Z (wl n)).
    { rewrite Z2Nat.id by (pose proof (to_Z_bounded (wl n >> 3)%uint63); lia). rewrite phi_shr3. pose proof (Z.div_mod (to_Z (wl n)) 8 ltac:(lia)). lia. }
    apply (Rmem_replace bgusegs rho2 (s_mem S) t rg rg' m m' HRm2 Eg Hsd).
    + intros i Hi. rewrite EB. pose proof (proj1 HRm2 t rg Eg) as Hok2. destruct Hok2 as (_ & _ & _ & _ & _ & _ & _ & Hby). rewrite EB in Hby.
      rewrite Erg'. rewrite (rg_kb_fill bgusegs rg (wl o >> 3)%uint63 _ (wl c) i Hi B3 B4) by lia. rewrite Ek0.
      replace (8 * (to_Z (wl o >> 3)%uint63 + Z.of_nat (Z.to_nat (to_Z (wl n >> 3)%uint63)))) with (to_Z (wl o) + to_Z (wl n)) by lia.
      destruct ((to_Z (wl o) <=? i) && (i <? to_Z (wl o) + to_Z (wl n))) eqn:Ein.
      * apply andb_prop in Ein as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
        destruct (Hmap' (i - to_Z (wl o)) ltac:(lia)) as [Hb Hw]. unfold A in Hb, Hw. replace (rho t + to_Z (wl o) + (i - to_Z (wl o))) with (rho t + i) in Hb, Hw by lia.
        eexists. split; [exact Hb|]. split; [|intros _; exact Hw].
        cbn [kb_ok]. rewrite Z_to_bv_unsigned, D11, wbv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_mod by lia.
        rewrite land_spec'. change (to_Z 255%uint63) with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
        unfold wZ. destruct (wh c); [|reflexivity]. unfold two63. rewrite Z.add_comm. change 9223372036854775808 with (36028797018963968 * 256). apply Z.mod_add. lia.
      * destruct (Hby i Hi) as (b & Eb & Kb & Wb). destruct (Hout (rho t + i) ltac:(lia)) as [E W].
        { apply andb_false_iff in Ein. rewrite Z.leb_gt, Z.ltb_ge in Ein. unfold A. lia. }
        exists b. split; [rewrite E; exact Eb|]. split; [exact Kb | intros Hwr; apply W, Wb, Hwr].
    + intros t2 rg2 G2 Hne i Hi. pose proof (proj1 HRm2 t2 rg2 G2) as (C0 & C1 & _). unfold two63 in C1.
      apply Hout; [lia|]. destruct (proj2 HRm2 t2 t rg2 rg G2 Eg Hne (or_intror Ewr)) as [D|D]; rewrite EB in D; unfold A; lia.
  -
    split; [|cbn [ms_fregs ms_fcsr ms_rom ms_regs MS]; repeat (split; [reflexivity|]); split; [do 31 eexists; reflexivity | exact Hps]].
    cbn [s_mem s_next ms_mem MS] in HM |- *.
    apply (FMem_write LB lo B sp0 m0 H_LIBW H_lo1 H_lo2 H_lo3 H_sp0B H_sp064 g rho cd (s_mem S) _ (s_next S) m m' t rg A (A + to_Z (wl n)) HM Eg Ewr);
      try (unfold rbase; rewrite Eabs; unfold A; lia); try assumption.
    + lia.
    + unfold A. lia.
    + intros a Ha. destruct (Hmap' (a - A) ltac:(lia)) as [Hb _]. replace (A + (a - A)) with a in Hb by lia. eexists. exact Hb.
    + eapply same_dirs_trans; [exact (same_dirs_mset _ t rg rg' Eg Hsd)|]. exact (same_dirs_mset _ ts rgs _ Egs (same_dir_drop_below rgs (wl os))).
Qed.

Definition hkp_realloc := hk_at PC_REALLOC (hk_realloc_v T_ERRNO ERRNO_INT TPV 1).

Lemma hkp_realloc_ok : hook_ok' bgusegs ghost JP FInvP hkp_realloc.
Proof.
  intros g rho cd S cd' S' ms HI Hh K.
  unfold hkp_realloc, hk_at in Hh. destruct (w_eqb (s_pc S) PC_REALLOC) eqn:Epc; [|discriminate]. apply w_eqb_true_iff in Epc.
  unfold hk_realloc_v in Hh. destruct (tp_ok TPV S && sp_ok 1 S) eqn:Eg; [|discriminate]. apply andb_prop in Eg as [Etp Esp].
  destruct (reset_errno T_ERRNO ERRNO_INT (s_mem S)) as [M1|] eqn:Ere; [|discriminate].
  unfold hk_realloc in Hh. cbn [s_pc s_regs s_resv s_mem s_abs s_next] in Hh.
  destruct (a_ops cd) as [|[[c k] n] rest] eqn:Eops; [discriminate|].
  destruct c as [|c|c]; try discriminate. destruct c as [c|c|]; try discriminate. destruct c; try discriminate.
  unfold rget in Hh. cbn [s_pc s_regs s_resv s_mem s_abs s_next] in Hh.
  destruct (rf_get vzero (s_regs S) X10) as [|t o| |] eqn:Ea10; try discriminate.
  destruct (zval (rf_get vzero (s_regs S) X11)) as [n'|] eqn:Ea1; [|discriminate].
  destruct (tag_of cd k) as [t'|] eqn:Etag; [|discriminate].
  destruct (mget M1 t) as [rg|] eqn:Eg1; [|discriminate].
  destruct ((t =? t')%uint63 && is_zero o && (n =? n') && (0 <? n) && (n <? 4294967296) && negb (rg_size rg =? 0)%uint63
            && (rg_size rg <=? of_Z n)%uint63) eqn:Eck; [|discriminate].
  apply andb_prop in Eck as [Eck Ec7]. apply andb_prop in Eck as [Eck Ec6]. apply andb_prop in Eck as [Eck Ec5].
  apply andb_prop in Eck as [Eck Ec4]. apply andb_prop in Eck as [Eck Ec3]. apply andb_prop in Eck as [Ec1 Ec2].
  apply Uint63.eqb_spec in Ec1. subst t'. apply is_zero_spec in Ec2. subst o. apply Z.eqb_eq in Ec3. subst n'.
  apply Z.ltb_lt in Ec4, Ec5. apply leb_spec in Ec7. cbv zeta in Hh.
  set (t2 := s_next S) in *.
  set (rg2 := RG None (of_Z n) 4 true DUnk (depth_for 60 (of_Z n) 0) (copy_cells rg (rg_size rg) (depth_for 60 (of_Z n) 0))) in *.
  destruct (hk_return (SS (s_pc S) (s_regs S) (s_resv S) M1 (s_abs S) t2) (VP t2 w_zero) (mset (kill_region M1 t rg) t2 rg2) (t2 + 1)%uint63) as [S1|] eqn:Ehr; [|discriminate].
  injection Hh as <- <-.
  destruct (hk_return_inv _ _ _ _ _ Ehr) as (ra & M' & Era & Ecl & Erv & ->). cbn [s_regs s_resv s_abs] in *.
  destruct (clobber_stack_inv _ _ _ Ecl) as (ts & os & rgs & Esp2 & Ehos & Egs & Eabss & Edfs & Eo16 & Eos & Ewrs & ->).
  unfold rget in Era, Esp2. cbn [s_regs] in Era, Esp2.

  destruct (inv_nf g rho cd S ms HI Erv) as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20
                   & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & Ems).
  set (m := ms_mem ms) in *. clearbody m. subst ms. destruct HI as [HRn [HM (_ & _ & _ & _ & Hps)]]. rewrite Epc in *.
  pose proof (Rn_R bgusegs rho S _ HRn) as (_ & _ & HRg & _ & HRm). unfold core_of in HRg. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem MS] in HRg, HRm.
  destruct (nf_regs rho S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HRg) as (D1 & D2 & D4 & D10 & D11 & _).
  unfold rget in D1, D2, D4, D10, D11. rewrite Era in D1. rewrite Esp2 in D2. rewrite Ea10 in D10.
  unfold tp_ok, rget in Etp. destruct (rf_get vzero (s_regs S) X4) as [tpw| | |] eqn:Etp4; try discriminate.
  apply w_eqb_true_iff in Etp. subst tpw.
  unfold sp_ok, rget in Esp. rewrite Esp2 in Esp. apply Uint63.eqb_spec in Esp. subst ts.
  unfold zval in Ea1. destruct (rf_get vzero (s_regs S) X11) as [a1w| | |] eqn:Ea11; try discriminate. injection Ea1 as Ea1.
  cbn [den] in D1, D2, D4, D10, D11.

  pose proof HM as (Hops & Hlen & Hn & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & Hheap & Hrho1 & Hmi & Hstk & Haux & Hagr).
  cbn [s_mem s_next ms_mem MS] in Htl, Htags, Hnx0, Hnx, Hcls, Hlink, Hheap, Hmi, Hstk, Haux, Hagr. fold t2 in Htl, Htags, Hnx0, Hnx.
  change (to_Z NEXT0) with 29 in *.
  assert (Ht20 : to_Z t2 < to_Z TAGLIM) by (change (to_Z TAGLIM) with (2 ^ 20); lia).

  unfold J. rewrite Hops, Eops. change (map dec_op ((2, k, n) :: rest)) with (OpRealloc (Z.to_nat k) n :: map dec_op rest).
  cbn [run_ops]. destruct (nth (Z.to_nat k) (g_env g) None) as [[p n0]|] eqn:Enth; [|cbn [lbind]; apply implM_interp_unr].
  assert (Henv : nth_error (g_env g) (Z.to_nat k) = Some (Some (p, n0))).
  { destruct (nth_error (g_env g) (Z.to_nat k)) as [e|] eqn:E.
    - rewrite (nth_error_nth _ _ None E) in Enth. congruence.
    - apply nth_error_None in E. rewrite nth_overflow in Enth by exact E. discriminate. }
  assert (Hklt : (Z.to_nat k < length (a_tags cd))%nat).
  { rewrite <- length_rev, <- Hlen. apply nth_error_Some. congruence. }
  destruct (tag_of_nth cd k t ltac:(rewrite Hn, length_rev; reflexivity) Etag Hklt) as [Hk0 Htlk].
  set (tl := rev (a_tags cd)) in *.
  assert (Ht29 : 29 <= to_Z t < to_Z t2) by (apply Htl; exact (nth_error_In _ _ Htlk)).

  destruct (reset_errno_inv _ _ _ _ Ere) as (rge & Ege & Eae & Ede & Ese & Ewe & EM1).
  set (rge' := RG (rg_abs rge) (rg_size rge) (rg_al rge) (rg_wr rge) DUnk (rg_d rge) IEmpty) in *.
  assert (Eg : mget (s_mem S) t = Some rg).
  { rewrite EM1 in Eg1. rewrite mget_mset in Eg1 by exact (mget_lt _ _ _ Ege).
    destruct (Z.eqb_spec (to_Z T_ERRNO) (to_Z t)) as [E|E]; [change (to_Z T_ERRNO) with 9 in E; lia | exact Eg1]. }
  destruct (Hlink _ _ _ _ Htlk Henv) as (rg0 & Eg0 & Eabs & Esz & Ewr). rewrite Eg in Eg0. injection Eg0 as <-.
  assert (Egs0 : mget (s_mem S) 1 = Some rgs).
  { rewrite mget_mset in Egs by exact Ht20.
    destruct (Z.eqb_spec (to_Z t2) (to_Z 1%uint63)) as [E|E]; [change (to_Z 1%uint63) with 1 in E; lia|].
    rewrite kill_region_eq in Egs. rewrite mget_mset in Egs by (rewrite EM1 in Eg1; exact (mget_lt _ _ _ Eg1)).
    destruct (Z.eqb_spec (to_Z t) (to_Z 1%uint63)) as [E'|E']; [change (to_Z 1%uint63) with 1 in E'; lia|].
    rewrite EM1 in Egs. rewrite mget_mset in Egs by exact (mget_lt _ _ _ Ege).
    destruct (Z.eqb_spec (to_Z T_ERRNO) (to_Z 1%uint63)) as [E''|E'']; [discriminate E'' | exact Egs]. }
  assert (Essz : rg_size rgs = STK).
  { pose proof (Hcls 1%uint63 rgs Egs0) as C. rewrite Eabss in C. destruct C as [[_ C]|(k1 & p1 & n1 & Hk1 & _)]; [exact C|].
    exfalso. apply nth_error_In in Hk1. specialize (Htl _ Hk1). change (to_Z 1%uint63) with 1 in Htl. lia. }
  rewrite Essz in Eos. pose proof STK_Z as ESTK. pose proof (to_Z_bounded (wl os)) as Bo.
  assert (EwZo : wZ os = to_Z (wl os)) by (unfold wZ; rewrite Ehos; lia).
  set (spc := sp0 - to_Z STK + to_Z (wl os)).
  assert (Esp : bv_unsigned x2 = spc).
  { rewrite D2. unfold pword. rewrite Z_to_bv_unsigned, Hrho1, EwZo. apply bv_wrap_small. unfold bv_modulus. unfold GLOBALS_TOP in H_lo2. lia. }
  assert (Eo8s : to_Z (wl os) mod 8 = 0).
  { pose proof (Z.mod_divide (to_Z (wl os)) 16 ltac:(lia)) as [X _]. destruct (X Eo16) as [q Eq]. rewrite Eq.
    replace (q * 16) with ((q * 2) * 8) by ring. apply Z.mod_mul. lia. }

  assert (Herr : exists errv : word, rw_cells bgusegs m RMallocRep.RERRNO [C4 errv]).
  { pose proof (region_mapped bgusegs rho T_ERRNO rge m (proj1 HRm _ _ Ege)) as Hb.
    unfold rbase in Hb. rewrite Eae, Ese in Hb. change (to_Z ERRNO_INT) with RMallocRep.RERRNO in Hb. change (to_Z 4%uint63) with 4 in Hb.
    apply bytes_rw_C4; [unfold RMallocRep.RERRNO; lia | unfold RMallocRep.RERRNO; lia|].
    intros i Hi. destruct (Hb i Hi) as [Hm Hw]. split; [exact Hm | exact (Hw Ewe)]. }
  destruct Herr as [errv Herr].
  pose proof (proj1 HRm t rg Eg) as Hokt. pose proof Hokt as (T0 & T1 & T2 & T3 & T4 & _). unfold two63 in T1. unfold rbase in T0, T1. rewrite Eabs in T0, T1.
  pose proof (to_Z_bounded (rg_size rg)) as Bsz.
  assert (Hold : exists old, rw_cells bgusegs m (rho t) [CB (Z.to_nat n0) old]).
  { apply bytes_rw_CB; [lia | rewrite Z2Nat.id by lia; lia|]. intros i Hi. rewrite Z2Nat.id in Hi by lia.
    destruct (region_mapped bgusegs rho t rg m Hokt i ltac:(lia)) as [Hb Hw]. unfold rbase in Hb, Hw. rewrite Eabs in Hb, Hw. split; [exact Hb | exact (Hw Ewr)]. }
  destruct Hold as [old Hold].
  assert (Hin : In (p, rho t, n0) (live_blocks rho tl (g_env g) ++ LB)) by (apply in_or_app; left; exact (live_blocks_in rho _ _ _ t p n0 Htlk Henv)).
  cbn [lbind]. eapply implM_interp_realloc.
  { eapply (REALLOC x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
                    F0 fc0 m (g_s g) _ p (rho t) n0 n lo B errv old Hheap Hin Haux).
    - rewrite Esp. unfold spc. lia.
    - rewrite Esp. exact (proj1 (stk_split bgusegs _ lo spc sp0 Hstk ltac:(unfold spc; lia))).
    - exact H_lo1.
    - rewrite Esp. unfold spc, RREALLOC_STACK. lia.
    - rewrite D4. change (bv_unsigned (wbv TPV) + -164) with RMallocRep.RERRNO. exact Herr.
    - exact Hold.
    - exact Hmi.
    - rewrite D4. reflexivity.
    - rewrite D10. unfold pword. change (wZ w_zero) with 0. rewrite Z.add_0_r. reflexivity.
    - rewrite D11. apply bv_eq. rewrite wbv_unsigned, Ea1, Z_to_bv_unsigned. symmetry. apply bv_wrap_small. unfold bv_modulus. lia.
    - lia. }
  intros r s' ms' HP. destruct r as [q|]; [|apply implM_interp_unr].
  destruct HP as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & Ems' & Hmi' & Hstk'
                  & Herr' & Haux' & Hpres & Hfa & Hso & A' & junk & Ea0' & Hrange & Hheap' & Hblk & Hn0n).
  rewrite Esp in Hstk', Hpres. rewrite D4 in Herr'. change (bv_unsigned (wbv TPV) + -164) with RMallocRep.RERRNO in Herr'.
  destruct Hrange as (R1 & R2 & R3 & R4 & R5).
  set (OW := live_blocks rho tl (g_env g)) in *.

  assert (Hnd' : List.NoDup (map blk_id (OW ++ LB))) by exact (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ Hheap).
  assert (Hrm : lb_remove p (OW ++ LB) = live_blocks rho tl (set_nth (Z.to_nat k) None (g_env g)) ++ LB).
  { rewrite lb_remove_app. f_equal.
    - apply (lb_remove_live rho tl (g_env g) (Z.to_nat k) t p n0); [|exact Htlk | exact Henv].
      pose proof Hnd' as Hnd''. rewrite map_app in Hnd''. exact (List.NoDup_app_remove_r _ _ Hnd'').
    - apply lb_remove_notin. intros Hp. apply in_map_iff in Hp as (b & Eb & Hb).
      exact (nodup_map_app blk_id OW LB (p, rho t, n0) b Hnd' (live_blocks_in rho _ _ _ t p n0 Htlk Henv) Hb (eq_sym Eb)). }
  rewrite Hrm in Hheap', Hpres.
  set (env1 := set_nth (Z.to_nat k) None (g_env g)) in *.
  assert (Hlen1 : length env1 = length tl) by (unfold env1; rewrite set_nth_length; exact Hlen).

  assert (Hother : forall k3 t3 p3 n3, nth_error tl k3 = Some t3 -> nth_error (g_env g) k3 = Some (Some (p3, n3)) -> t3 <> t ->
                     nth_error env1 k3 = Some (Some (p3, n3))).
  { intros k3 t3 p3 n3 Hk3 He3 Hne. unfold env1. rewrite nth_error_set_nth_ne; [exact He3|]. intros E. rewrite <- E in Hk3. rewrite Htlk in Hk3. congruence. }
  assert (Hother' : forall k3 t3 p3 n3, nth_error tl k3 = Some t3 -> nth_error (g_env g) k3 = Some (Some (p3, n3)) -> t3 <> t ->
                     In (p3, rho t3, n3) (live_blocks rho tl env1 ++ LB)).
  { intros k3 t3 p3 n3 Hk3 He3 Hne. apply in_or_app. left. exact (live_blocks_in rho tl env1 k3 t3 p3 n3 Hk3 (Hother k3 t3 p3 n3 Hk3 He3 Hne)). }
  set (rho' := fun t' : int => if (t' =? t2)%uint63 then A' else rho t').
  assert (Hag' : agree_below t2 rho rho').
  { intros t' Ht'. unfold rho'. destruct (t' =? t2)%uint63 eqn:E; [apply Uint63.eqb_spec in E; subst t'; lia | reflexivity]. }
  assert (Erho't : rho' t2 = A') by (unfold rho'; rewrite Uint63.eqb_refl; reflexivity).
  assert (Et1 : to_Z (t2 + 1)%uint63 = to_Z t2 + 1).
  { rewrite add_spec. change (to_Z 1%uint63) with 1. apply Z.mod_small. rewrite wB_eq. unfold two63. change (to_Z TAGLIM) with (2 ^ 20) in Ht20. lia. }
  set (Mk := kill_region M1 t rg) in *.
  assert (Hcases : forall t3 rg3, mget (mset (mset Mk t2 rg2) 1 (drop_below rgs (wl os))) t3 = Some rg3 ->
            (t3 = 1%uint63 /\ rg3 = drop_below rgs (wl os)) \/ (t3 = t2 /\ rg3 = rg2)
            \/ (t3 = t /\ rg3 = RG (Some 0%uint63) 0 0 false DUnk 0 IEmpty) \/ (t3 = T_ERRNO /\ rg3 = rge')
            \/ (t3 <> 1%uint63 /\ t3 <> t2 /\ t3 <> t /\ t3 <> T_ERRNO /\ mget (s_mem S) t3 = Some rg3)).
  { intros t3 rg3 G3.
    destruct (mget_mset_cases (mset Mk t2 rg2) 1%uint63 t3 _ rg3 ltac:(change (to_Z 1%uint63) with 1; change (to_Z TAGLIM) with (2 ^ 20); lia) G3) as [[-> ->]|[N1 G3a]]; [left; auto|].
    destruct (mget_mset_cases Mk t2 t3 _ rg3 Ht20 G3a) as [[-> ->]|[N2 G3b]]; [right; left; auto|].
    unfold Mk in G3b. rewrite kill_region_eq in G3b.
    destruct (mget_mset_cases M1 t t3 _ rg3 (mget_lt _ _ _ Eg1) G3b) as [[-> ->]|[N3 G3c]]; [right; right; left; auto|].
    rewrite EM1 in G3c. destruct (mget_mset_cases (s_mem S) T_ERRNO t3 _ rg3 (mget_lt _ _ _ Ege) G3c) as [[-> ->]|[N4 G3d]]; [right; right; right; left; auto|].
    right; right; right; right. auto. }
  apply (K (GH s' (env1 ++ [Some (q, n)]) (map dec_op rest)) rho' ms' Hag').
  subst ms'. split.
  -
    intros rho2 Hag2. cbn [s_next] in Hag2.
    assert (Hag02 : agree_below t2 rho rho2).
    { intros t' Ht'. rewrite (Hag2 t') by (rewrite Et1; lia). apply Hag'. exact Ht'. }
    assert (Erho2t : rho2 t2 = A') by (rewrite (Hag2 t2) by (rewrite Et1; lia); exact Erho't).
    assert (Erho21 : rho2 1%uint63 = sp0 - to_Z STK) by (rewrite (Hag02 1%uint63) by (change (to_Z 1%uint63) with 1; lia); exact Hrho1).
    assert (Erho2o : rho2 t = rho t) by (apply Hag02; lia).
    pose proof (HRn rho2 Hag02) as (_ & _ & HRg2 & _ & HRm2). change (Rmem bgusegs rho2 (s_mem S) m) in HRm2.
    unfold core_of in HRg2. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv MS] in HRg2.
    pose proof HRm2 as [HRok2 Hsep2].
    eapply R_return; [exact HRg2 | exact D1 | |].
    { cbn [den]. unfold pword. rewrite Erho2t, Ea0'. f_equal. change (wZ w_zero) with 0. lia. }

    assert (HRm1 : Rmem bgusegs rho2 M1 m).
    { rewrite EM1. apply (Rmem_replace bgusegs rho2 (s_mem S) T_ERRNO rge rge' m m HRm2 Ege).
      - unfold rge'. repeat split. cbn [rg_dflt]. symmetry. exact Ede.
      - intros i Hi. destruct (region_mapped bgusegs rho2 _ rge m (HRok2 _ _ Ege) i Hi) as [[b Hb] Hw]. exists b. split; [exact Hb|]. split; [|exact Hw].
        unfold rg_kb, rd_cell. cbn [rge' rg_d rg_cells rg_dflt]. rewrite iget_empty. cbn [dflt_cell cell_kb]. change (to_Z 0%uint63) with 0. rewrite Z.bits_0. exact I.
      - intros t3 rg3 _ _ i _. split; [reflexivity | auto]. }
    assert (En62 : to_Z (of_Z n) = n) by (apply of_Z_small; lia).
    destruct (depth_for_ok (of_Z n) ltac:(rewrite En62; lia)) as [Hd1 Hd2].
    split.
    + intros t3 rg3 G3. destruct (Hcases t3 rg3 G3) as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|(N1 & N2 & N3 & N4 & G)]]]].
      * apply (stack_after_call rho2 rgs (wl os) m m' (live_blocks rho tl env1 ++ LB) (HRok2 _ _ Egs0) Eabss Edfs Essz Erho21 Eo8s); [lia | exact Hstk' | exact Hpres].
      *
        pose proof (HRok2 _ _ Eg) as Hokt2.
        unfold region_ok. unfold rbase. cbn [rg2 rg_abs rg_size rg_al rg_wr rg_d]. rewrite Erho2t, En62. change (to_Z 4%uint63) with 4.
        split; [split; [lia | left; exact R1]|]. split; [unfold two63; lia|]. split; [lia|]. split; [rewrite En62 in Hd1; exact Hd1|]. split; [exact Hd2|]. split; [lia|]. split; [exact R2|].
        intros i Hi. destruct (rw_cells_bytes bgusegs m' A' _ Hblk i) as (Hb & Hsome & Hw).
        { cbn [cells_size csize]. lia. }
        destruct (nth_error (cells_bytes [CB (Z.to_nat n0) old; CB (Z.to_nat (n - n0)) junk]) (Z.to_nat i)) as [b|] eqn:Enb; [|congruence].
        exists b. split; [exact Hb|]. split; [|intros _; exact Hw].
        destruct (rg_kb_copy bgusegs rg (rg_size rg) None (of_Z n) 4 true (depth_for 60 (of_Z n) 0) i ltac:(rewrite En62; exact Hi) Hd1 Hd2 Ec7) as [->|[Hi8 ->]]; [exact I|].
        assert (Hi0 : i < n0) by (pose proof (Z.div_mod (to_Z (rg_size rg)) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (to_Z (rg_size rg)) 8 ltac:(lia)); lia).
        destruct Hokt2 as (_ & _ & _ & _ & _ & _ & _ & Hby). destruct (Hby i ltac:(lia)) as (b0 & Eb0 & Kb0 & _).
        unfold rbase in Eb0. rewrite Eabs, Erho2o in Eb0.
        destruct (rw_cells_bytes bgusegs m (rho t) _ Hold i) as (Hbo & _ & _); [cbn [cells_size csize]; lia|].
        cbn [cells_bytes cbytes] in Enb, Hbo. rewrite app_nil_r in Hbo.
        assert (Hlo : length old = Z.to_nat n0) by (destruct Hold as [[[Hl _] _] _]; exact Hl).
        rewrite nth_error_app1 in Enb by lia. rewrite Enb in Hbo. rewrite Hbo in Eb0. injection Eb0 as <-. exact Kb0.
      *
        apply (region_ok_fresh_gen bgusegs rho2 t (Some 0%uint63) 0%uint63 0%uint63 false 0%nat m'); unfold rbase; cbn [rg_abs];
          change (to_Z 0%uint63) with 0; try (unfold two63); try lia; try reflexivity; try (intros i Hi; lia).
      * exact (errno_after_call rho2 rge m m' errv' (HRok2 _ _ Ege) Eae Ese Herr').
      * apply (region_ok_frame bgusegs rho2 t3 rg3 m m' (HRok2 _ _ G)).
        apply (old_region_kept g rho rho2 cd (s_mem S) t2 m m' s' _ _ _ rge HM HRm2 Hag02 Hmi' Hheap' Hpres Ege Eae Ese Ewe t3 rg3 G N1 N4).
        intros k3 p3 n3 Hk3 He3. exact (Hother' k3 t3 p3 n3 Hk3 He3 N3).
    +
      apply (regions_sep_mset_same rho2 (mset Mk t2 rg2) 1%uint63 rgs (drop_below rgs (wl os)) Egs); [repeat split|].
      assert (Hfresh : mget Mk t2 = None).
      { unfold Mk. rewrite kill_region_eq. rewrite mget_mset by exact (mget_lt _ _ _ Eg1).
        destruct (Z.eqb_spec (to_Z t) (to_Z t2)) as [E|E]; [lia|].
        rewrite EM1. rewrite mget_mset by exact (mget_lt _ _ _ Ege). destruct (Z.eqb_spec (to_Z T_ERRNO) (to_Z t2)) as [E'|E']; [change (to_Z T_ERRNO) with 9 in E'; lia|].
        destruct (mget (s_mem S) t2) as [rgx|] eqn:Ex; [|reflexivity]. pose proof (Htags t2 rgx Ex). lia. }
      apply (regions_sep_new rho2 Mk t2 rg2 (regions_sep_kill bgusegs rho2 M1 t rg m HRm1 Eg1) Hfresh Ht20).
      intros t3 rg3 G3. assert (EB : rbase rho2 t2 rg2 = A') by (unfold rbase; cbn [rg2 rg_abs]; exact Erho2t).
      rewrite EB. cbn [rg2 rg_size]. rewrite En62.
      assert (X : forall rgx, mget (s_mem S) t3 = Some rgx -> t3 <> t -> A' + n <= rbase rho2 t3 rgx \/ rbase rho2 t3 rgx + to_Z (rg_size rgx) <= A').
      { intros rgx Gx Hne. apply (new_block_apart g rho rho2 cd (s_mem S) t2 m m' s' q A' n _ HM HRm2 Hag02 Hheap' t3 rgx Gx).
        intros k3 p3 n3 Hk3 He3. exact (Hother' k3 t3 p3 n3 Hk3 He3 Hne). }
      unfold Mk in G3. rewrite kill_region_eq in G3.
      destruct (mget_mset_cases M1 t t3 _ rg3 (mget_lt _ _ _ Eg1) G3) as [[-> ->]|[N3 G3c]].
      * right. unfold rbase. cbn [rg_abs rg_size]. change (to_Z 1%uint63) with 1. change (to_Z 0%uint63) with 0. lia.
      * rewrite EM1 in G3c. destruct (mget_mset_cases (s_mem S) T_ERRNO t3 _ rg3 (mget_lt _ _ _ Ege) G3c) as [[-> ->]|[N4 G3d]]; [exact (X rge Ege N3) | exact (X rg3 G3d N3)].
  -
    split; [|cbn [ms_fregs ms_fcsr ms_rom ms_regs MS g_s]; repeat (split; [reflexivity|]); split; [do 31 eexists; reflexivity | destruct Hps as [P1 P2]; split; congruence]].
    unfold FMem. cbn [a_ops a_tags a_n g_s g_env g_ops s_mem s_next ms_mem MS rev]. fold tl. change (to_Z NEXT0) with 29.
    assert (En62 : to_Z (of_Z n) = n) by (apply of_Z_small; lia).
    assert (Hnew : mget (mset (mset Mk t2 rg2) 1 (drop_below rgs (wl os))) t2 = Some rg2).
    { rewrite mget_mset by (change (to_Z 1%uint63) with 1; change (to_Z TAGLIM) with (2 ^ 20); lia).
      destruct (Z.eqb_spec (to_Z 1%uint63) (to_Z t2)) as [E|E]; [change (to_Z 1%uint63) with 1 in E; lia|].
      rewrite mget_mset by exact Ht20. rewrite Z.eqb_refl. reflexivity. }
    split; [reflexivity|].
    split; [rewrite !length_app; cbn [length]; lia|].
    split; [rewrite length_app; cbn [length]; lia|].
    split.
    { apply (Permutation_NoDup (l := t2 :: tl)); [apply Permutation_cons_append|]. constructor; [|exact Hnd].
      intros Hin2. specialize (Htl t2 Hin2). lia. }
    split.
    { intros t' Hin2. apply in_app_or in Hin2. destruct Hin2 as [Hin2|[<-|[]]]; [specialize (Htl t' Hin2); lia | lia]. }
    split.
    { intros t3 rg3 G3. destruct (Hcases t3 rg3 G3) as [[-> _]|[[-> _]|[[-> _]|[[-> _]|(_ & _ & _ & _ & G)]]]].
      - change (to_Z 1%uint63) with 1. lia.
      - lia.
      - lia.
      - change (to_Z T_ERRNO) with 9. lia.
      - specialize (Htags t3 rg3 G). lia. }
    split; [lia|]. split; [rewrite Eops in Hnx; cbn [length] in Hnx; lia|].
    split.
    { intros t3 rg3 G3. destruct (Hcases t3 rg3 G3) as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|(N1 & N2 & N3 & N4 & G)]]]].
      - cbn [drop_below rg_abs rg_size]. rewrite Eabss. left. split; [reflexivity | exact Essz].
      - cbn [rg2 rg_abs rg_size]. right. exists (length tl), q, n.
        split; [rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity|].
        split; [rewrite nth_error_app2 by lia; rewrite Hlen1, Nat.sub_diag; reflexivity | exact En62].
      - cbn [rg_abs rg_size rg_wr]. left. repeat split.
      - pose proof (Hcls T_ERRNO rge Ege) as C. rewrite Eae in C. cbn [rge' rg_abs rg_size rg_wr]. rewrite Eae. exact C.
      - pose proof (Hcls t3 rg3 G) as C. destruct (rg_abs rg3); [exact C|]. destruct C as [C|(k3 & p3 & n3 & Hk3 & He3 & Es3)]; [left; exact C|].
        right. exists k3, p3, n3. split; [rewrite nth_error_app1 by (apply nth_error_Some; congruence); exact Hk3|].
        split; [|exact Es3]. rewrite nth_error_app1 by (rewrite Hlen1; apply nth_error_Some; congruence). exact (Hother k3 t3 p3 n3 Hk3 He3 N3). }
    split.
    { intros k0 t3 p3 n3 Hk3 He3. destruct (Nat.lt_ge_cases k0 (length tl)) as [L|L].
      - rewrite nth_error_app1 in Hk3 by exact L. rewrite nth_error_app1 in He3 by lia.
        assert (Hk0k : k0 <> Z.to_nat k).
        { intros ->. unfold env1 in He3. rewrite (nth_error_set_nth_same None _ _ _ Henv) in He3. discriminate. }
        unfold env1 in He3. rewrite nth_error_set_nth_ne in He3 by (intros E; apply Hk0k; symmetry; exact E).
        destruct (Hlink k0 t3 p3 n3 Hk3 He3) as (rg3 & G3 & Ea3 & Es3 & Ew3). exists rg3. repeat split; try assumption.
        assert (N0 : t3 <> t).
        { intros ->. apply Hk0k. apply (proj1 (List.NoDup_nth_error tl) Hnd); [apply nth_error_Some; congruence | congruence]. }
        assert (N1 : t3 <> 1%uint63) by (intros ->; apply nth_error_In in Hk3; specialize (Htl _ Hk3); change (to_Z 1%uint63) with 1 in Htl; lia).
        assert (N2 : t3 <> t2) by (intros ->; apply nth_error_In in Hk3; specialize (Htl _ Hk3); lia).
        assert (N3 : t3 <> T_ERRNO) by (intros ->; apply nth_error_In in Hk3; specialize (Htl _ Hk3); change (to_Z T_ERRNO) with 9 in Htl; lia).
        rewrite mget_mset by (change (to_Z 1%uint63) with 1; change (to_Z TAGLIM) with (2 ^ 20); lia).
        destruct (Z.eqb_spec (to_Z 1%uint63) (to_Z t3)) as [E|E]; [apply to_Z_inj in E; congruence|].
        rewrite mget_mset by exact Ht20.
        destruct (Z.eqb_spec (to_Z t2) (to_Z t3)) as [E'|E']; [apply to_Z_inj in E'; congruence|].
        unfold Mk. rewrite kill_region_eq. rewrite mget_mset by exact (mget_lt _ _ _ Eg1).
        destruct (Z.eqb_spec (to_Z t) (to_Z t3)) as [E0|E0]; [apply to_Z_inj in E0; congruence|].
        rewrite EM1. rewrite mget_mset by exact (mget_lt _ _ _ Ege).
        destruct (Z.eqb_spec (to_Z T_ERRNO) (to_Z t3)) as [E''|E'']; [apply to_Z_inj in E''; congruence | exact G3].
      - rewrite nth_error_app2 in Hk3 by exact L. rewrite nth_error_app2 in He3 by lia. rewrite Hlen1 in He3.
        destruct (k0 - length tl)%nat as [|j] eqn:Ej; [|destruct j; discriminate]. cbn in Hk3, He3. injection Hk3 as <-. injection He3 as <- <-.
        exists rg2. split; [exact Hnew|]. cbn [rg2 rg_abs rg_size rg_wr]. repeat split. exact En62. }
    split.
    { rewrite live_blocks_snoc by exact Hlen1. rewrite Erho't.
      rewrite (live_blocks_agree rho rho') by (intros t' Hin2; apply Hag'; specialize (Htl t' Hin2); lia).
      eapply RHEAP_perm; [exact Hheap'|]. rewrite <- app_assoc. cbn [app]. apply Permutation_middle. }
    split; [rewrite (Hag' 1%uint63) by (change (to_Z 1%uint63) with 1; lia); exact Hrho1|].
    split; [exact Hmi'|].
    split.
    { apply (stk_merge bgusegs m' lo spc sp0 Hstk'); [|unfold spc; lia].
      apply (rheap_pres_stk _ spc m m' spc sp0 Hpres); [|lia]. exact (proj2 (stk_split bgusegs _ lo spc sp0 Hstk ltac:(unfold spc; lia))). }
    split; [exact Haux'|].
    eapply agree_on_trans; [exact Hagr|]. eapply agree_on_mono; [exact (agree_of_heap_pres _ _ _ _ Hpres)|].
    intros a [_ Hc]. destruct Hc as [Hc|[(b & Hb & Hr)|Hc]]; [left; unfold spc; lia | right; right; exists b; split; [apply in_or_app; right; exact Hb | exact Hr] | right; left; exact Hc].
Qed.

End Hooks.
