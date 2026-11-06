(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.glaze.binary_reflection.images Require Import Ubsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnframeBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKN OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaM OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhPolicy OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaS OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKA OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapWF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaR OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocKBig OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnfr OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNtf OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnframeBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKN.UbMhEnframe OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhKX OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhGap OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaM.UbMhRsegs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhExt OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhCover OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN.UbMhNtfLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2.UbMhNest OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhList OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapK.UbMhAcct OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhPolicy OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaS.UbMhMSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKA.UbMhASpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapWF.UbMhMmapW OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapWF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaR OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocK.UbMhMallocW OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocKBig OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnfr OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNtf OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKA OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocK.UbMhMallocKT OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocK.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import PuAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
#[local] Ltac mh_lia_nx := rnfix; first [ solve [hclr; lean zlia] | pa_arith_concl; lia_goal_ok; lia_hsep; first [ with_img1f_ zlia | with_img1_ zlia | lia_pairs; with_img2 zlia ] ].
#[local] Ltac lia ::= first [ solve [ rnfix; pa_tiers ltac:(zlia) ] | solve [ rnfix; pa_big; lia_goal_ok; lia_hsep; pa_tierB ltac:(zlia) ] | mh_lia_nx ].
#[local] Ltac lia_fast ::= first [ solve [ rnfix; pa_tiers ltac:(zlia) ] | solve [ rnfix; pa_big; lia_goal_ok; lia_hsep; pa_tierB ltac:(zlia) ] | first [ solve [ clear_disj; rnfix; zlia ] | solve [ with_disj1 ltac:(rnfix; zlia) ] | lia ] ].
Definition BSTK : Z := 192.     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section SpecR.
  Context {RN : mh_run}.
  Context {fx : FPState}.

  Definition gkeep (st st' : mst) (x : Z) : Prop :=
    is_group st x /\ s_kind st' x = s_kind st x /\ g_W st' x = g_W st x /\ s_slot st' x 0 = s_slot st x 0.

  Lemma lone_gkeep : forall st st' x, gkeep st st' x -> lone st x -> lone st' x.
  Proof using.
    intros st st' x (G & K & W & S) (L0 & K0 & ML & SC & p & n & off & res & S0).
    unfold lone. unfold g_stride, g_lastidx, g_maplen, g_sc in *. rewrite W, K, S.
    split; [exact L0|]. split; [exact K0|]. split; [exact ML|]. split; [exact SC|]. exists p, n, off, res. exact S0.
  Qed.

  Lemma lone_all_keep : forall st st',
    (forall x, is_group st' x -> lone st' x \/ gkeep st st' x) ->
    (forall g, is_group st g -> lone st g) -> (forall g, is_group st' g -> lone st' g).
  Proof using.
    intros st st' H LO g Hg. destruct (H g Hg) as [X|X]; [exact X|].
    exact (lone_gkeep st st' g X (LO g (proj1 X))).
  Qed.

  Definition malloc_postkR (st : mst) (stk : Z) (L : list (Z * Z)) (n sp : Z) (regs : bvmap 5 word) (M : mem) (mdl : Model)
             (rom : word -> option byte) (c' : config) : Prop :=
    exists regs' M' mdl' (p : Z) st',
      c' = mkCfg (mkst regs' (getr regs 1) M' rom) mdl' /\
      cs_same regs regs' /\ getr regs' 10 = Z_to_bv 64 p /\
      p mod 16 = 0 /\ HEAPLO + 16 <= p /\ p + n <= CEIL /\ (p + n <= IMG_LO \/ IMG_HI <= p) /\ ~ In (p, n) L /\
      (forall b k, In (b, k) L -> p + n <= b \/ b + k <= p) /\
      (forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> m_wr stk L sp a) /\
      defined M' (sp - stk) sp /\ defined M' p (p + n) /\
      WF st' ((p, n) :: L) /\ REP st' M' /\ LEDGER st' (m_vmmaps mdl') /\ nojunk st' /\ nolimbo st' /\
      m_halted mdl' = None /\ m_vm_lazy mdl' = [] /\ m_vm_materialized mdl' = [] /\
      m_fs mdl' = m_fs mdl /\ m_fds mdl' = m_fds mdl /\
      vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl) /\
      (forall x, is_group st' x -> lone st' x \/ gkeep st st' x).

  Definition malloc_failkR (st : mst) (stk : Z) (L : list (Z * Z)) (sp : Z) (regs : bvmap 5 word) (M : mem) (mdl : Model)
             (rom : word -> option byte) (c' : config) : Prop :=
    exists regs' M' mdl' st',
      c' = mkCfg (mkst regs' (getr regs 1) M' rom) mdl' /\
      cs_same regs regs' /\ getr regs' 10 = Z_to_bv 64 0 /\
      (forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> m_wr stk L sp a) /\
      defined M' (sp - stk) sp /\
      WF st' L /\ REP st' M' /\ LEDGER st' (m_vmmaps mdl') /\ nojunk st' /\ nolimbo st' /\
      m_halted mdl' = None /\ m_vm_lazy mdl' = [] /\ m_vm_materialized mdl' = [] /\
      m_fs mdl' = m_fs mdl /\ m_fds mdl' = m_fds mdl /\
      vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl) /\
      (forall x, is_group st' x -> gkeep st st' x).

  Lemma postkR_postk : forall st stk L n sp regs M mdl rom c',
    malloc_postkR st stk L n sp regs M mdl rom c' -> malloc_postk stk L n sp regs M mdl rom c'.
  Proof using.
    intros st stk L n sp regs M mdl rom c' (regs' & M' & mdl' & p & st' & X). exists regs', M', mdl', p, st'.
    repeat match goal with |- _ /\ _ => split; [apply (proj1 X) | apply proj2 in X] end. exact (proj1 X).
  Qed.

  Lemma failkR_failk : forall st stk L sp regs M mdl rom c',
    malloc_failkR st stk L sp regs M mdl rom c' -> malloc_failk stk L sp regs M mdl rom c'.
  Proof using.
    intros st stk L sp regs M mdl rom c' (regs' & M' & mdl' & st' & X). exists regs', M', mdl', st'.
    repeat match goal with |- _ /\ _ => split; [apply (proj1 X) | apply proj2 in X] end. exact (proj1 X).
  Qed.
End SpecR.

(* [comment removed for export] *)
Lemma kcs15 : forall r r' : bvmap 5 word, MemsetLibF.RefMemcpyLib.keeps_cs r r' ->
  getr r' 2%bv = getr r 2%bv /\ getr r' 3%bv = getr r 3%bv /\ getr r' 4%bv = getr r 4%bv /\ getr r' 8%bv = getr r 8%bv /\
  getr r' 9%bv = getr r 9%bv /\ getr r' 18%bv = getr r 18%bv /\ getr r' 19%bv = getr r 19%bv /\ getr r' 20%bv = getr r 20%bv /\
  getr r' 21%bv = getr r 21%bv /\ getr r' 22%bv = getr r 22%bv /\ getr r' 23%bv = getr r 23%bv /\ getr r' 24%bv = getr r 24%bv /\
  getr r' 25%bv = getr r 25%bv /\ getr r' 26%bv = getr r 26%bv /\ getr r' 27%bv = getr r 27%bv.
Proof. intros r r' K. repeat split; apply K; apply in_regs_dec; reflexivity. Qed.

Section Big.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (M : mem) (mdl : Model) (regs : bvmap 5 word) (rom : word -> option byte).
  Variables (n sp : Z) (F : kfam) (bo : bool).
  Hypothesis HL : kfam_laws RSEGS F.
  Hypothesis HAM : AM_SPEC3.
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  Hypothesis HLG : LEDGER st (m_vmmaps mdl).
  Hypothesis NJ : nojunk st.
  Hypothesis NLB : nolimbo st.
  Hypothesis Hh : m_halted mdl = None.
  Hypothesis Hlz : m_vm_lazy mdl = [].
  Hypothesis Hmat : m_vm_materialized mdl = [].
  Hypothesis HCR : Z.of_nat (length (s_regions st)) <= 240.
  Hypothesis HCA : s_flist st = [] -> c_avail_cnt (s_ctx st) = 0 -> Z.of_nat (length (s_areas st)) + 1 <= AREAMAX.
  Hypothesis HBUD : RSUM (s_regions st) + (n + 4116) + 2 ^ 24 <= vm_limit (m_vmmaps mdl).
  Hypothesis HLL : Z.of_nat (length L) + 1 <= LMAX.
  Hypothesis Hn : MMAP_THRESHOLD <= n /\ n + 4116 <= 2 ^ 35.
  Hypothesis R10 : getr regs 10 = Z_to_bv 64 n.
  Hypothesis Rra : ret_ok (getr regs 1).
  Hypothesis R2 : getr regs 2 = Z_to_bv 64 sp.
  Hypothesis R4 : getr regs 4 = Z_to_bv 64 TPV.
  Hypothesis Hsp : CEIL + BSTK <= sp /\ sp < 2 ^ 64.
  Hypothesis DEF : defined M (sp - BSTK) sp.
  Hypothesis HQ : forall c', malloc_postkR st BSTK L n sp regs M mdl rom c' -> Kok F c'.
  Hypothesis HQF : forall c', malloc_failkR st BSTK L sp regs M mdl rom c' -> Kf F c'.

  #[local] Notation cx := (s_ctx st).
  (* [comment removed for export] *)
  Definition ml : Z := (n + 4115) / 4096.
  Definition len : Z := 4096 * ml.

  Lemma len_eq : page_round_up_Z (n + 20) = len.
  Proof using L st. unfold page_round_up_Z, page_size, len, ml. replace (n + 20 + 4096 - 1) with (n + 4115) by lia. lia. Qed.
  Lemma len_rng : n + 20 <= len <= n + 4115 /\ 0 < ml /\ len <= 2 ^ 35 /\ len mod 4096 = 0.
  Proof using Hn L st.
    pose proof (page_round_up_Z_bounds (n + 20) ltac:(unfold MMAP_THRESHOLD in Hn; lia)) as B. rewrite len_eq in B.
    unfold page_size in B. unfold len, ml in *. unfold MMAP_THRESHOLD in Hn.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    repeat split; try lia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


  Lemma rdn_agreeZ : forall (Ma Mb : mem) a k, 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
    agree_on (fun x => a <= x < a + Z.of_nat k) Ma Mb -> rdn RSEGS Mb (Z_to_bv 64 a) k = rdn RSEGS Ma (Z_to_bv 64 a) k.
  Proof using L st.
    intros Ma Mb a k Ha Hk AG. destruct k as [|k']; [reflexivity|].
    apply rdn_ext; [rewrite u64_lit by lia; lia|].
    intros x Hx. rewrite u64_lit in Hx by lia. pose proof (u64_range x).
    replace x with (Z_to_bv 64 (bv_unsigned x)) by (apply bv_eq; rewrite u64_lit by lia; reflexivity).
    apply AG; lia.
  Qed.

  Lemma land_hi_lo : forall h y, 0 <= h -> 0 <= y < 4096 -> Z.land (4096 * h) y = 0.
  Proof using L st.
    intros h y Xh Xy.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    rewrite <- (Z.mod_small y 4096) by lia. change 4096 with (2 ^ 12) at 2.
    rewrite <- (Z.land_ones y 12) by lia.
    rewrite (Z.land_comm y (Z.ones 12)), Z.land_assoc, Z.land_ones by lia.
    replace ((4096 * h) mod 2 ^ 12) with 0 by (change (2 ^ 12) with 4096; lia).
    apply Z.land_0_l.
  Qed.
  Lemma lor_hi_lo : forall h y, 0 <= h -> 0 <= y < 4096 -> Z.lor (4096 * h) y = 4096 * h + y.
  Proof using L st.
    intros h y Xh Xy. rewrite <- Z.lxor_lor by (apply land_hi_lo; lia). symmetry. apply Z.add_nocarry_lxor. apply land_hi_lo; lia.
  Qed.
  Lemma Wbig_mkW : Wbig n = mkW 0 1 63 ml.
  Proof using Hn L st.
    unfold Wbig, mkW, ml. pose proof Hn as [N1 _]. unfold MMAP_THRESHOLD in N1.
    set (x := n + 4115). set (q := x / 2048).
    assert (E1 : x - x mod 2048 = 2048 * q) by (subst q; lia).
    assert (E2 : x / 4096 = q / 2) by (subst q; rewrite (Z.div_div x 2048 2) by lia; reflexivity).
    rewrite E1, E2.
    assert (Hq : 0 <= q) by (subst q; apply Z.div_pos; lia).
    assert (E3 : 2048 * q = 4096 * (q / 2) + 2048 * (q mod 2)) by lia.
    rewrite E3. assert (R : q mod 2 = 0 \/ q mod 2 = 1) by lia.
    destruct R as [R|R]; rewrite R.
    - rewrite Z.mul_0_r, Z.add_0_r. rewrite lor_hi_lo by lia. lia.
    - rewrite Z.mul_1_r. rewrite <- (lor_hi_lo (q / 2) 2048) by lia. rewrite <- Z.lor_assoc. change (Z.lor 2048 4064) with 4064.
      rewrite lor_hi_lo by lia. lia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Lemma XSUM_one : forall a l, 0 <= a < 2 ^ 64 -> 0 <= l < 2 ^ 64 -> XSUM [(Z_to_bv 64 a, Z_to_bv 64 l)] = l.
  Proof using L st. intros a l Ha Hl. unfold XSUM, live_bytes. cbn [fold_right fst snd map]. rewrite ?u64_lit by lia. cbn. rewrite ?u64_lit by lia. lia. Qed.

  (* [comment removed for export] *)
  Definition pol (s : mst) (q : Z -> Z) (sq : Z) : mst := UbMhPolicy.st' s (c_usage (s_ctx s)) q (c_bounces (s_ctx s)) sq.


  (* [comment removed for export] *)
  Lemma kat_ecall_munmap_ru : forall rg (pc : word) mm rom0 model w (a : word) (len0 len' : Z) (Q : config -> Prop),
    fetch_word RSEGS pc = Some w -> is_ecall w = true ->
    m_halted model = None -> m_vm_lazy model = [] ->
    getr rg 17 = Z_to_bv 64 215 ->
    getr rg 10 = a -> bv_unsigned a mod 4096 = 0 ->
    getr rg 11 = Z_to_bv 64 len0 -> 0 < len0 <= len' -> page_round_up_Z len0 = len' ->
    bv_unsigned a + len' <= CEIL ->
    map_has (vm_maps (m_vmmaps model)) a (Z_to_bv 64 len') = true ->
    kat RSEGS (mkCfg (mkst (regupd rg 10 (Z_to_bv 64 0)) (v_addi pc 4) (unfill a (Z_to_bv 64 len') mm) rom0)
                     (munmap_model a (Z_to_bv 64 len') model)) Q ->
    kat RSEGS (mkCfg (mkst rg pc mm rom0) model) Q.
  Proof using L st.
    intros rg pc mm rom0 model w a len0 len' Q XF XE Xh Xlazy X17 X10 Xal X11 Xlen Xpr Xce Xhas Xk.
    assert (Xnw : bv_unsigned a + len' < 2 ^ 64) by (ceil; lia).
    pose proof (u64_range a) as XRa.
    set (ms := {| ms_regs := rg; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := Some (getr rg 17);
                  ms_resv := None; ms_fcsr := fp_csr; ms_mem := mm; ms_rom := rom0 |}).
    assert (Xu1 : bv_unsigned (ms_gpr ms 1) = len0).
    { unfold ms, ms_gpr. cbn [ms_regs]. rewrite arg_reg_1. change (reg_get rg 11) with (getr rg 11). rewrite X11. apply u_Z2bv; lia. }
    assert (X0 : ms_gpr ms 0 = a).
    { unfold ms, ms_gpr. cbn [ms_regs]. rewrite arg_reg_0. change (reg_get rg 10) with (getr rg 10). exact X10. }
    assert (Xprw : page_round_up (ms_gpr ms 1) = Z_to_bv 64 len') by (unfold page_round_up; rewrite Xu1, Xpr; reflexivity).
    assert (Xargs : munmap_args_ok ms model).
    { unfold munmap_args_ok. rewrite X0, Xu1, Xprw, Xpr. split; [exact Xal|]. split.
      - intros Hz. apply (f_equal bv_unsigned) in Hz. rewrite Xu1 in Hz. change (bv_unsigned (Z_to_bv 64 0)) with 0 in Hz. lia.
      - split; [unfold TASK_SIZE; ceil; lia | exact Xhas]. }
    eapply kat_step; [exact Xh | exact Xlazy | reflexivity | |].
    { apply (step_ecall RSEGS rg pc mm rom0 w XF XE). }
    change (kat RSEGS (mkCfg ms model) Q).
    eapply (kat_munmap RSEGS ms model (getr rg 17)); [exact Xh | exact Xlazy | reflexivity | rewrite X17; apply u_Z2bv; lia | exact Xargs |].
    unfold munmap_eff. rewrite X0, Xprw. unfold ms. rewrite adv_munmap. exact Xk.
  Qed.

  (* [comment removed for export] *)
  Lemma LEDGERX_unmapX : forall (stx : mst) (p0 len' : Z) vm,
    WF stx L -> LEDGERX stx [(Z_to_bv 64 p0, Z_to_bv 64 len')] vm ->
    0 <= p0 -> 0 < len' -> p0 + len' <= CEIL ->
    (forall r, In r (s_regions stx) -> p0 + len' <= rg_base r \/ rg_base r + rg_len r <= p0) ->
    LEDGER stx (mkVmMapsFull (vm_reserved vm) (map_remove (vm_maps vm) (Z_to_bv 64 p0))
                    (maps_subtract (vm_noaccess vm) p0 (p0 + len'))
                    (vm_start_brk vm) (vm_brk vm) (vm_limit vm) (vm_mmap_base vm) (vm_init_sp vm)).
  Proof using st.
    intros stx p0 len' vm XWF LX Xp0 Xlen Xce XAP. destruct LX as [XLM XLN XLB XLR XLT]. ceil.
    constructor; cbn [vm_maps vm_noaccess vm_brk vm_start_brk vm_reserved vm_init_sp vm_limit vm_mmap_base].
    - unfold map_remove. eapply Permutation_trans. { apply perm_filter. exact XLM. }
      cbn [List.filter app fst]. rewrite bv_eqb_refl. cbn [negb].
      rewrite filter_all; [apply Permutation_refl|].
      intros e He. apply in_map_iff in He. destruct He as (r & <- & Hr). cbn [region_entry fst].
      destruct (wr_rng stx (WF_regions stx L XWF) r Hr) as (Q1 & Q2 & Q3 & Q4 & Q5). pose proof (XAP r Hr) as D. unfold HEAPLO in Q1.
      rewrite bv_eqb_neq; [reflexivity|]. intros E. apply (f_equal bv_unsigned) in E. rewrite !u_Z2bv in E by lia. lia.
    - rewrite maps_subtract_apart; [exact XLN | lia |].
      intros e He. apply (Permutation_in _ XLN) in He. unfold noacc_of in He. apply in_app_iff in He. destruct He as [He|He].
      + destruct (guard_inside stx L XWF e He) as (b0 & -> & Hin).
        destruct (wr_rng stx (WF_regions stx L XWF) _ Hin) as (W1 & W2 & W3 & W4 & W5). cbn [rg_base rg_len] in W1, W2, W3, W4, W5.
        pose proof (XAP _ Hin) as D. cbn [rg_base rg_len] in D. unfold HEAPLO in W1.
        exists b0, 4096. split; [reflexivity|]. lia.
      + apply in_flat_map in He. destruct He as (r & Hr & He).
        destruct (nr_inside stx L XWF r e Hr He) as (x & y & -> & X1 & X2 & X3 & X4 & X5).
        pose proof (XAP r Hr) as D. exists x, y. split; [reflexivity|]. lia.
    - exact XLB.
    - exact XLR.
    - exact XLT.
  Qed.

  Lemma w8_zero_nth : forall j, nth j (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 8 0) = Z_to_bv 8 0.
  Proof using. intros j. change (word_to_le_bytes 8 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0) 8). apply nth_repeat. Qed.

  (* [comment removed for export] *)
  Lemma step_seq_run : forall (sx : mst) (Mx : mem) rx (p0 : Z),
    WF sx L -> REP sx Mx -> 0 <= p0 < 2 ^ 64 - 1 ->
    getr rx 10 = Z_to_bv 64 p0 -> getr rx 18 = Z_to_bv 64 (2 ^ 64 - 1) -> getr rx 9 = Z_to_bv 64 MLOCK ->
    exists rx' Mx' q sq,
      msteps RSEGS (mkst rx (0x66fd8 : word) Mx rom) (mkst rx' (0x66c68 : word) Mx' rom) /\
      getr rx' 20 = Z_to_bv 64 p0 /\ getr rx' 1 = Z_to_bv 64 0x670cc /\ keeps_but [1; 10; 11; 20]%bv rx rx' /\
      WF (pol sx q sq) L /\ REP (pol sx q sq) Mx' /\
      (forall y, 0 <= y < 2 ^ 64 -> Mx' (Z_to_bv 64 y) <> Mx (Z_to_bv 64 y) -> CTX + 848 <= y < CTX + 913) /\
      mem_grows Mx Mx'.
  Proof using st.
    intros sx Mx rx p0 XWF XREP Hp0 X10 X18 X9.
    pose proof (rp_statics sx Mx XREP) as [Snl _ _ _ _ _ _ _].
    pose proof (rc_seq sx Mx (rp_ctx sx Mx XREP)) as Cseq. pose proof (wc_seq sx (WF_ctx sx L XWF)) as Rseq.
    pose proof (ctx_store_ok sx Mx XREP) as SOKc.
    assert (Mnl : rdn RSEGS Mx (Z_to_bv 64 A_NEED_LOCKS) 1%nat = Some [Z_to_bv 8 0]) by exact (cell1_rdn Mx A_NEED_LOCKS 0 ltac:(lia) Snl).
    assert (Mseq : rdn RSEGS Mx (Z_to_bv 64 ctx_seq) 1%nat = Some [Z_to_bv 8 (c_seq (s_ctx sx))]) by exact (cell1_rdn Mx ctx_seq _ Rseq Cseq).
    destruct (Z.eq_dec (c_seq (s_ctx sx)) 255) as [E255|N255].
    - destruct (mBig1b Mx p0 (c_seq (s_ctx sx)) Hp0 Rseq Mnl Mseq SOKc rx rom X10 X18 X9 E255) as (rx' & RUN & Y20 & Y1 & KY).
      exists rx', (m_S2 Mx), (fun _ => 0), 1. split; [exact RUN|]. split; [exact Y20|]. split; [exact Y1|]. split; [exact KY|].
      assert (WR : forall y, 0 <= y < 2 ^ 64 -> m_S2 Mx (Z_to_bv 64 y) <> Mx (Z_to_bv 64 y) -> CTX + 848 <= y < CTX + 880 \/ y = CTX + 912).
      { intros y Hy NE. unfold m_S2, ctx_unmap_seq, ctx_seq, CTX in NE. unfold CTX. wdiff NE Mx y. }
      assert (GR : mem_grows Mx (m_S2 Mx)) by (intros z Hz; unfold m_S2; repeat apply (wbytes_grows _ _ _ z); exact Hz).
      destruct (policy_close sx L Mx (m_S2 Mx) (CEIL + MSTK) (c_usage (s_ctx sx)) (fun _ => 0) (c_bounces (s_ctx sx)) 1
                  (fun y => CTX + 848 <= y < CTX + 880 \/ y = CTX + 912) XWF XREP
                  (wc_usage sx (WF_ctx sx L XWF)) ltac:(intros; lia) (wc_bnc sx (WF_ctx sx L XWF)) ltac:(lia) ltac:(lia)) as [PW PR].
      + intros y Hy NE. right. pose proof (WR y Hy NE). unfold CTX in *. lia.
      + exact GR.
      + intros sc Hsc. right. split; [reflexivity|]. intros y Hy [W|W]; unfold ctx_usage, CTX in *; lia.
      + intros i Hi. left. unfold cell. apply byte_at_rdn1. unfold byte_at, m_S2.
        unfold ctx_unmap_seq, ctx_seq, CTX.
        rewrite wbytes_outZ by (cbn; lia).
        assert (IN : forall (Mb : mem) b, b <= 700056 + 848 + i < b + 8 -> 0 <= b -> b + 8 < 2 ^ 64 ->
                  wbytes Mb (Z_to_bv 64 b) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 (700056 + 848 + i)) = Some (Z_to_bv 8 0)).
        { intros Mb b Hb Hb0 Hb8. rewrite wbytes_inside; [rewrite w8_zero_nth; reflexivity | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia |].
          rewrite length_N_to_le_bytes, !u_Z2bv by lia. cbn. lia. }
        destruct (Z.lt_ge_cases i 24); [|apply IN; lia].
        rewrite wbytes_outZ by (wd_lenlit; rewrite ?length_N_to_le_bytes; cbn; lia).
        destruct (Z.lt_ge_cases i 16); [|apply IN; lia].
        rewrite wbytes_outZ by (wd_lenlit; rewrite ?length_N_to_le_bytes; cbn; lia).
        destruct (Z.lt_ge_cases i 8); [|apply IN; lia].
        rewrite wbytes_outZ by (wd_lenlit; rewrite ?length_N_to_le_bytes; cbn; lia).
        apply IN; lia.
      + intros i Hi. right. split; [reflexivity|]. intros [W|W]; unfold ctx_bounces, CTX in *; lia.
      + left. unfold cell, m_S2. unfold ctx_seq, ctx_unmap_seq, CTX.
        pose proof (rdn_wbytes_hit RSEGS (word_to_le_bytes 1 (Z_to_bv 64 1))) as RH. rewrite length_N_to_le_bytes in RH. apply RH. zsimp. lia.
      + split; [exact PW|]. split; [exact PR|]. split; [|exact GR]. intros y Hy NE. destruct (WR y Hy NE); lia.
    - destruct (mBig1a Mx p0 (c_seq (s_ctx sx)) Hp0 Rseq Mnl Mseq SOKc rx rom X10 X18 X9 N255) as (rx' & RUN & Y20 & Y1 & KY).
      exists rx', (m_S1 Mx (c_seq (s_ctx sx))), (c_unmap_seq (s_ctx sx)), (c_seq (s_ctx sx) + 1).
      split; [exact RUN|]. split; [exact Y20|]. split; [exact Y1|]. split; [exact KY|].
      assert (WR : forall y, 0 <= y < 2 ^ 64 -> m_S1 Mx (c_seq (s_ctx sx)) (Z_to_bv 64 y) <> Mx (Z_to_bv 64 y) -> y = CTX + 912).
      { intros y Hy NE. unfold m_S1, ctx_seq, CTX in NE. unfold CTX. wdiff NE Mx y. }
      assert (GR : mem_grows Mx (m_S1 Mx (c_seq (s_ctx sx)))) by (intros z Hz; unfold m_S1; apply (wbytes_grows _ _ _ z); exact Hz).
      destruct (policy_close sx L Mx (m_S1 Mx (c_seq (s_ctx sx))) (CEIL + MSTK) (c_usage (s_ctx sx)) (c_unmap_seq (s_ctx sx)) (c_bounces (s_ctx sx)) (c_seq (s_ctx sx) + 1)
                  (fun y => y = CTX + 912) XWF XREP
                  (wc_usage sx (WF_ctx sx L XWF)) (wc_useq sx (WF_ctx sx L XWF)) (wc_bnc sx (WF_ctx sx L XWF)) ltac:(lia) ltac:(lia)) as [PW PR].
      + intros y Hy NE. right. pose proof (WR y Hy NE). unfold CTX in *. lia.
      + exact GR.
      + intros sc Hsc. right. split; [reflexivity|]. intros y Hy W; unfold ctx_usage, CTX in *; lia.
      + intros i Hi. right. split; [reflexivity|]. intros W; unfold ctx_unmap_seq, CTX in *; lia.
      + intros i Hi. right. split; [reflexivity|]. intros W; unfold ctx_bounces, CTX in *; lia.
      + left. unfold cell, m_S1. unfold ctx_seq, CTX.
        pose proof (rdn_wbytes_hit RSEGS (word_to_le_bytes 1 (Z_to_bv 64 (c_seq (s_ctx sx) + 1)))) as RH. rewrite length_N_to_le_bytes in RH. apply RH. zsimp. lia.
      + split; [exact PW|]. split; [exact PR|]. split; [|exact GR]. intros y Hy NE. rewrite (WR y Hy NE). unfold CTX. lia.
  Qed.

  Theorem malloc_big_kfx : kat RSEGS (mkCfg (mkst regs (0x66f40%bv : word) M rom) mdl) (kfx F bo).
  Proof using HQF HQ DEF Hsp R4 R2 Rra R10 Hn HLL HBUD HCA HCR Hmat Hlz Hh NLB NJ HLG HREP HWF HAM HL sp n L st RN.
    pose proof Hsp as [S1 S2]. ceil; unfold BSTK in S1. pose proof Hn as [N1 N2]. unfold MMAP_THRESHOLD in N1.
    pose proof len_rng as (L1 & L2 & L3 & L4). assert (LEN : len = 4096 * ml) by reflexivity.
    pose proof (rp_statics st M HREP) as [Snl Spg Slock Scan Sgot Serr Sctz Ssc].
    pose proof (rp_ctx st M HREP) as RC.
    (* [comment removed for export] *)
    assert (SOK48 : store_ok RSEGS M (Z_to_bv 64 (sp - 48)) 48%nat = true).
    { eapply store_ok_defined; [exact DEF | unfold BSTK; lia | unfold BSTK; cbn; lia | unfold BSTK; lia | lia]. }
    destruct (mPro M sp n ltac:(ceil; lia) ltac:(lia) SOK48 regs rom R2 R10) as (r1 & RUN1 & A2 & A8 & A9 & A10 & K1).
    eapply kat_msteps; [exact Hh | exact Hlz | exact RUN1 |].
    set (M1 := mal_frame M sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20)).
    (* [comment removed for export] *)
    destruct (mBig0 M1 n ltac:(unfold MMAP_THRESHOLD; lia) r1 rom A8 A10) as (r2 & RUN2 & B10 & B11 & B12 & B13 & B14 & B15 & B19 & B18 & B1 & K2).
    eapply kat_msteps; [exact Hh | exact Hlz | exact RUN2 |].
    (* [comment removed for export] *)
    assert (SOK64 : store_ok RSEGS M1 (Z_to_bv 64 (sp - 48 - 64)) 64%nat = true).
    { eapply (store_ok_defined M1 (sp - BSTK) sp); [| unfold BSTK; lia | unfold BSTK; cbn; lia | unfold BSTK; lia | lia].
      intros y Hy. unfold M1, mal_frame. repeat apply (wbytes_grows _ _ _ (Z_to_bv 64 y)). apply DEF. exact Hy. }
    assert (B2 : getr r2 2 = Z_to_bv 64 (sp - 48)) by (kept_rw K2; exact A2).
    destruct (mmW1_34 M1 (sp - 48) 0 (n + 20) 3 34 ltac:(lia) SOK64 ltac:(lia) r2 rom eq_refl B2 B10 B11 B12 B13 B14 B15)
      as (r3 & RUN3 & C2 & C17 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & K3).
    eapply kat_msteps; [exact Hh | exact Hlz | exact RUN3 |].
    set (M2 := mm_frame M1 (sp - 48) (getr r2 1) (getr r2 8) (getr r2 9) (getr r2 18) (getr r2 19) (getr r2 20) (getr r2 21)).
    (* [comment removed for export] *)
    assert (M1W : forall y, 0 <= y < 2 ^ 64 -> M1 (Z_to_bv 64 y) <> M (Z_to_bv 64 y) -> sp - 48 <= y < sp).
    { intros y Hy NE. unfold M1, mal_frame in NE. wdiff NE M y. }
    assert (M2W : forall y, 0 <= y < 2 ^ 64 -> M2 (Z_to_bv 64 y) <> M1 (Z_to_bv 64 y) -> sp - 112 <= y < sp - 48).
    { intros y Hy NE. unfold M2, mm_frame in NE. wdiff NE M1 y. }
    assert (G12 : mem_grows M M2).
    { intros z Hz. unfold M2, mm_frame. repeat apply (wbytes_grows _ _ _ z). unfold M1, mal_frame. repeat apply (wbytes_grows _ _ _ z). exact Hz. }
    assert (REP2 : REP st M2).
    { apply (REP_frame st L M HWF HREP M2 G12).
      intros y Hy NE. left. destruct (decide (M2 (Z_to_bv 64 y) = M1 (Z_to_bv 64 y))) as [E1|NE1].
      + rewrite E1 in NE. pose proof (M1W y Hy NE). ceil. lia.
      + pose proof (M2W y Hy NE1). ceil. lia. }
    (* [comment removed for export] *)
    pose proof (proj1 (LEDGERX_nil st _) HLG) as HLX.
    destruct (ledgerx_grant_rw st L [] mdl HWF HLX xok_nil Hlz Hmat (getr r3 10) len ltac:(lia) ltac:(cbn [length Z.of_nat]; lia)
                ltac:(rewrite XSUM_nil; lia)) as (a0 & GR0 & _).
    apply (kat_of_kfx F bo).
    apply (as_kfx_mmap_rw F r3 (0x683ac%bv : word) M2 rom mdl W_68358 (n + 20) HL Hh Hlz F_68358 E_68358 C17 C11 ltac:(lia) C12 C13 C14 C15 false bo).
    { rewrite len_eq. exists a0. exact GR0. }
    { (* [comment removed for export] *)
      unfold mmrw_fail. replace (errno_ret ENOMEM) with (Z_to_bv 64 (2 ^ 64 - 12)) by (apply bv_eq; reflexivity).
      replace (v_addi (0x683ac%bv : word) 4) with (0x683b0%bv : word) by (apply bv_eq; reflexivity).
      assert (SOKe : store_ok RSEGS M2 (Z_to_bv 64 A_ERRNO) 4%nat = true).
      { eapply store_ok_mono; [exact G12|]. apply store_ok_wseg. vm_compute. reflexivity. }
      assert (SOK16 : store_ok RSEGS M2 (Z_to_bv 64 (sp - 48 - 80)) 16%nat = true).
      { eapply store_ok_mono; [exact G12|]. eapply (store_ok_defined M (sp - BSTK) sp); [exact DEF | unfold BSTK; lia | unfold BSTK; cbn; lia | unfold BSTK; lia | lia]. }
      destruct (mmW2f M2 (sp - 48) 0 ltac:(unfold A_ERRNO, TPV; lia) SOK16 SOKe ltac:(lia)
                  (regupd r3 10 (Z_to_bv 64 (2 ^ 64 - 12))) rom (getr r2 1) (getr r2 8) (getr r2 9) (getr r2 18) (getr r2 19) (getr r2 20) (getr r2 21)
                  ltac:(rewrite B1; apply ret_ok_even; reflexivity)
                  ltac:(gres; exact C2) ltac:(gres; reflexivity) ltac:(gres; exact C16) ltac:(gres; kept_rw K3; kept_rw K2; kept_rw K1; exact R4)
                  ltac:(unfold M2, mm_frame; rdn_solve) ltac:(unfold M2, mm_frame; rdn_solve) ltac:(unfold M2, mm_frame; rdn_solve)
                  ltac:(unfold M2, mm_frame; rdn_solve) ltac:(unfold M2, mm_frame; rdn_solve) ltac:(unfold M2, mm_frame; rdn_solve)
                  ltac:(unfold M2, mm_frame; rdn_solve))
        as (rf & RUNf & Z2 & Z10 & Z1 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Kf').
      eapply (kf_msteps RSEGS F HL); [exact Hh | exact Hlz | exact RUNf |].
      rewrite B1. replace (Z_to_bv 64 421848) with (0x66fd8%bv : word) by (apply bv_eq; reflexivity).
      set (Mf := mm_ffail M2 (sp - 48) (getr (regupd r3 10 (Z_to_bv 64 (2 ^ 64 - 12))) 8)) in *.
      set (Ms := wbytes (wbytes M2 (Z_to_bv 64 (sp - 48 - 72)) (word_to_le_bytes 8 (Z_to_bv 64 0x683d0)))
                        (Z_to_bv 64 (sp - 48 - 80)) (word_to_le_bytes 8 (getr (regupd r3 10 (Z_to_bv 64 (2 ^ 64 - 12))) 8))).
      assert (EMf : Mf = wbytes Ms (Z_to_bv 64 A_ERRNO) errno12) by reflexivity.
      assert (MsW : forall y, 0 <= y < 2 ^ 64 -> Ms (Z_to_bv 64 y) <> M (Z_to_bv 64 y) -> sp - 128 <= y < sp).
      { intros y Hy NE. destruct (decide (Ms (Z_to_bv 64 y) = M2 (Z_to_bv 64 y))) as [E0|NE0].
        - rewrite E0 in NE. destruct (decide (M2 (Z_to_bv 64 y) = M1 (Z_to_bv 64 y))) as [E1|NE1].
          + rewrite E1 in NE. pose proof (M1W y Hy NE). lia.
          + pose proof (M2W y Hy NE1). lia.
        - unfold Ms in NE0. revert NE0. generalize M2. intros Mb NE0. wdiff NE0 Mb y. }
      assert (MfW : forall y, 0 <= y < 2 ^ 64 -> Mf (Z_to_bv 64 y) <> M (Z_to_bv 64 y) ->
                    (sp - 128 <= y < sp) \/ (A_ERRNO <= y < A_ERRNO + 4)).
      { intros y Hy NE. rewrite EMf in NE. destruct (decide (wbytes Ms (Z_to_bv 64 A_ERRNO) errno12 (Z_to_bv 64 y) = Ms (Z_to_bv 64 y))) as [E0|NE0].
        - rewrite E0 in NE. left. exact (MsW y Hy NE).
        - right. unfold errno12, A_ERRNO, TPV in NE0 |- *. revert NE0. generalize Ms. intros Mb NE0. wdiff NE0 Mb y. }
      assert (Gs : mem_grows M Ms).
      { eapply mem_grows_trans; [exact G12|]. unfold Ms. do 2 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. }
      assert (Gf : mem_grows M Mf).
      { eapply mem_grows_trans; [exact Gs|]. rewrite EMf. apply wbytes_grows. }
      assert (REPs : REP st Ms).
      { apply (REP_frame st L M HWF HREP Ms Gs). intros y Hy NE. left. pose proof (MsW y Hy NE). ceil. lia. }
      assert (REPf : REP (set_errno st 12) Mf).
      { apply (REP_set_errno st L Ms Mf 12 HWF REPs). split.
        - unfold cell. rewrite EMf. unfold errno12, A_ERRNO, TPV. pose proof (rdn_wbytes_hit RSEGS (word_to_le_bytes 4 (Z_to_bv 64 12))) as RH.
          rewrite length_N_to_le_bytes in RH. apply RH. zsimp; lia.
        - intros a NE. pose proof (u64_range a) as AR.
          assert (Eaa : a = Z_to_bv 64 (bv_unsigned a)) by (apply bv_eq; rewrite u_Z2bv by lia; reflexivity).
          rewrite Eaa, EMf in NE |- *. unfold errno12, A_ERRNO, TPV in NE |- *.
          pose proof (wbytes_diff_g Ms (568208 - 164) (word_to_le_bytes 4 (Z_to_bv 64 12)) (bv_unsigned a) ltac:(lia) ltac:(rewrite length_N_to_le_bytes; cbn; lia) AR NE) as IN.
          rewrite length_N_to_le_bytes in IN. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in IN. split; [rewrite u_Z2bv by lia; lia|].
          apply wbytes_inside_some; wd_lenlit; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
      (* [comment removed for export] *)
      assert (STKf : forall dd v, 8 <= dd <= 48 -> rdn RSEGS M1 (Z_to_bv 64 (sp - dd)) 8%nat = Some (word_to_le_bytes 8 v) ->
                     rdn RSEGS Mf (Z_to_bv 64 (sp - dd)) 8%nat = Some (word_to_le_bytes 8 v)).
      { intros dd v Hd R. rewrite (rdn_agreeZ M1 Mf (sp - dd) 8 ltac:(lia) ltac:(cbn; lia)); [exact R|]. intros y Hr Hy. cbn in Hy.
        rewrite EMf. unfold Ms, M2, mm_frame, errno12, A_ERRNO, TPV. ceil.
        rewrite !wbytes_outZ by (wd_lenlit; rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia). reflexivity. }
      destruct (tY1 Mf sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) ltac:(ceil; unfold BSTK in *; lia) Rra
                  (STKf 8 _ ltac:(lia) ltac:(unfold M1, mal_frame; rdn_solve)) (STKf 16 _ ltac:(lia) ltac:(unfold M1, mal_frame; rdn_solve))
                  (STKf 24 _ ltac:(lia) ltac:(unfold M1, mal_frame; rdn_solve)) (STKf 32 _ ltac:(lia) ltac:(unfold M1, mal_frame; rdn_solve))
                  (STKf 40 _ ltac:(lia) ltac:(unfold M1, mal_frame; rdn_solve)) (STKf 48 _ ltac:(lia) ltac:(unfold M1, mal_frame; rdn_solve))
                  rf rom ltac:(rewrite Z2; reflexivity) Z10 ltac:(rewrite Z18; exact B18))
        as (r9 & RUN9 & E2 & E10 & E1 & E8 & E9 & E18 & E19 & E20 & K9).
      eapply (kf_msteps RSEGS F HL); [exact Hh | exact Hlz | exact RUN9 |].
      apply HQF. unfold malloc_failk.
      exists r9, Mf, mdl, (set_errno st 12).
      split; [reflexivity|].
      split.
      { unfold cs_same. rewrite E2, E8, E9, E18, E19, E20, R2. repeat split; try reflexivity.
        all: kept_rw K9; first [rewrite Z21 | kept_rw Kf'; gres]; kept_rw K3; kept_rw K2; kept_rw K1; reflexivity. }
      split; [exact E10|].
      split.
      { intros a Ha NE. destruct (MfW a Ha NE) as [A|A]; [left; unfold BSTK; lia | right; right; right; exact A]. }
      split; [eapply defined_grows; [exact Gf | exact DEF]|].
      split; [apply WF_set_errno; [exact HWF | lia]|]. split; [exact REPf|]. split; [apply LEDGER_set_errno; exact HLG|].
      split; [exact NJ|]. split; [exact NLB|].
      split; [exact Hh|]. split; [exact Hlz|]. split; [exact Hmat|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      intros x Hx. split; [exact Hx|]. split; [reflexivity|]. split; reflexivity. }
    (* [comment removed for export] *)
    intros aw GR. apply (kfx_of_kat F HL false). unfold mmrw_grant. rewrite len_eq in GR |- *.
    replace (v_addi (0x683ac%bv : word) 4) with (0x683b0%bv : word) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    pose proof GR as GR'. unfold grant_ok in GR'. rewrite !Bool.andb_true_iff in GR'. destruct GR' as [[[[GA1 GA2] GA3] GA4] GA5].
    apply Z.eqb_eq in GA1. apply Z.ltb_lt in GA2. apply Z.leb_le in GA3. unfold page_size in GA1.
    set (p0 := bv_unsigned aw) in *.
    assert (Ea : aw = Z_to_bv 64 p0) by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
    pose proof GA4 as GA4'. rewrite (lx_res st [] _ HLX) in GA4'.
    destruct (grant_range_hz (m_vmmaps mdl) (vm_maps (m_vmmaps mdl)) aw (Z_to_bv 64 len) (lx_top st [] _ HLX) GA4'
                ltac:(rewrite u_Z2bv by lia; lia) ltac:(fold p0; lia) ltac:(rewrite u_Z2bv by lia; exact (proj2 (proj2 (proj2 len_rng)))) ltac:(rewrite u_Z2bv by lia; fold p0; lia)) as [HCE IMGF].
    rewrite u_Z2bv in HCE by lia. rewrite u_Z2bv in IMGF by lia. fold p0 in HCE, IMGF.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (HP0 : p0 mod 4096 = 0 /\ HEAPLO <= p0 /\ p0 + len <= CEIL) by (unfold HEAPLO; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (HRF : region_free (vm_reserved (m_vmmaps mdl) ++ vm_maps (m_vmmaps mdl)) (Z_to_bv 64 p0) (Z_to_bv 64 len) = true) by (rewrite <- Ea; exact GA4).
    pose proof (proj1 (rf_apart st L [] _ HWF HLX xok_nil p0 len ltac:(lia) ltac:(lia) (proj2 (proj2 HP0)) HRF)) as AP.
    rewrite Ea. set (M3 := zfill (Z_to_bv 64 p0) (Z_to_bv 64 len) M2).
    set (mdl1 := mmap_model (Z_to_bv 64 p0) (Z_to_bv 64 len) mdl).
    pose (h1 := mkVmMapsFull (vm_reserved (m_vmmaps mdl)) ((Z_to_bv 64 p0, Z_to_bv 64 len) :: vm_maps (m_vmmaps mdl)) (vm_noaccess (m_vmmaps mdl))
               (vm_start_brk (m_vmmaps mdl)) (vm_brk (m_vmmaps mdl)) (vm_limit (m_vmmaps mdl)) (vm_mmap_base (m_vmmaps mdl)) (vm_init_sp (m_vmmaps mdl))).
    pose proof (with_vmmaps_facts h1 mdl) as MF. change (with_vmmaps h1 mdl) with mdl1 in MF. destruct MF as (MF1 & MF2 & MF3 & MF4 & MF5 & MF6).
    assert (HLX1 : LEDGERX st [(Z_to_bv 64 p0, Z_to_bv 64 len)] (m_vmmaps mdl1)).
    { rewrite MF1. destruct HLG as [G1 G2 G3 G4 G5]. constructor; cbn [h1 vm_maps vm_noaccess vm_brk vm_start_brk vm_reserved vm_mmap_base vm_init_sp app].
      - apply perm_skip. exact G1.
      - exact G2.
      - exact G3.
      - exact G4.
      - exact G5. }
    assert (M3W : forall y, 0 <= y < 2 ^ 64 -> M3 (Z_to_bv 64 y) <> M (Z_to_bv 64 y) -> (sp - 112 <= y < sp) \/ (p0 <= y < p0 + len)).
    { intros y Hy NE. unfold M3 in NE.
      destruct (decide (zfill (Z_to_bv 64 p0) (Z_to_bv 64 len) M2 (Z_to_bv 64 y) = M2 (Z_to_bv 64 y))) as [E0|NE0].
      - rewrite E0 in NE. destruct (decide (M2 (Z_to_bv 64 y) = M1 (Z_to_bv 64 y))) as [E1|NE1].
        + rewrite E1 in NE. left. pose proof (M1W y Hy NE). lia.
        + left. pose proof (M2W y Hy NE1). lia.
      - right. exact (zfill_diffZ _ p0 len y ltac:(lia) ltac:(lia) ltac:(ceil; lia) Hy NE0). }
    assert (G3 : mem_grows M M3).
    { intros z Hz. unfold M3. apply zfill_grows. unfold M2, mm_frame. repeat apply (wbytes_grows _ _ _ z). unfold M1, mal_frame. repeat apply (wbytes_grows _ _ _ z). exact Hz. }
    assert (REP3 : REP st M3).
    { apply (REP_agree_but st L M2 M3 p0 (p0 + len) HWF REP2).
      - intros y Hy NE. exact (zfill_diffZ _ p0 len y ltac:(lia) ltac:(lia) ltac:(ceil; lia) Hy NE).
      - exact (conj (proj1 (proj2 HP0)) IMGF).
      - intros y Hy. split.
        + intros [D|[D|[D|(x & Hx & Kx & D)]]]; [unfold A_ERRNO, TPV, HEAPLO in *; lia | unfold CTX_END, CTX, HEAPLO in *; lia | |].
          * destruct D as (ar & Har & R). destruct (area_in_region st L HWF ar Har) as (r & Hr & _ & Q1 & Q2). destruct (AP r Hr); lia.
          * pose proof (wg_kind st L x (wG_each st L (WF_groups st L HWF) x Hx)) as KD. rewrite Kx in KD. destruct KD as (Y1 & Y2 & _).
            destruct (AP _ Y2); cbn [rg_base rg_len] in *; lia.
        + intros (x & Hx & G). pose proof (gcell_in_span st L HWF x y Hx G).
          destruct (ge_inreg st (WF_geom st L HWF) x Hx) as (r & Hr & Q1 & Q2). destruct (AP r Hr); lia. }
    (* [comment removed for export] *)
    assert (STK2 : forall d v, 8 <= d <= 56 -> rdn RSEGS M2 (Z_to_bv 64 (sp - 48 - d)) 8%nat = Some (word_to_le_bytes 8 v) ->
                   rdn RSEGS M3 (Z_to_bv 64 (sp - 48 - d)) 8%nat = Some (word_to_le_bytes 8 v)).
    { intros d v Hd R. unfold M3. rewrite rdn_zfill_outZ by (ceil; cbn; lia). exact R. }
    destruct (mmW2 (sp - 48) 0 ltac:(lia) ltac:(lia) (regupd r3 10 (Z_to_bv 64 p0)) rom M3 p0
                (getr r2 1) (getr r2 8) (getr r2 9) (getr r2 18) (getr r2 19) (getr r2 20) (getr r2 21)
                ltac:(lia) ltac:(right; lia) ltac:(rewrite B1; apply ret_ok_even; reflexivity)
                ltac:(gres; exact C2) ltac:(gres; reflexivity) ltac:(gres; exact C16)
                (STK2 8 _ ltac:(lia) ltac:(unfold M2, mm_frame; rdn_solve)) (STK2 16 _ ltac:(lia) ltac:(unfold M2, mm_frame; rdn_solve))
                (STK2 24 _ ltac:(lia) ltac:(unfold M2, mm_frame; rdn_solve)) (STK2 32 _ ltac:(lia) ltac:(unfold M2, mm_frame; rdn_solve))
                (STK2 40 _ ltac:(lia) ltac:(unfold M2, mm_frame; rdn_solve)) (STK2 48 _ ltac:(lia) ltac:(unfold M2, mm_frame; rdn_solve))
                (STK2 56 _ ltac:(lia) ltac:(unfold M2, mm_frame; rdn_solve)))
      as (r4 & RUN4 & D2 & D10 & D1 & D8 & D9 & D18 & D19 & D20 & D21 & K4).
    eapply kat_msteps; [rewrite MF2; exact Hh | rewrite MF3; exact Hlz | exact RUN4 |].
    rewrite B1. replace (Z_to_bv 64 421848) with (0x66fd8%bv : word) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    destruct (step_seq_run st M3 r4 p0 HWF REP3 ltac:(ceil; lia) D10 ltac:(rewrite D18; exact B18) ltac:(rewrite D9; kept_rw K2; exact A9))
      as (r5 & M5 & q5 & sq5 & RUN5 & E20 & E1 & K5 & WF5 & REP5 & M5W & G5).
    eapply kat_msteps; [rewrite MF2; exact Hh | rewrite MF3; exact Hlz | exact RUN5 |].
    set (st5 := pol st q5 sq5) in *.
    (* [comment removed for export] *)
    assert (XOK : xok [(Z_to_bv 64 p0, Z_to_bv 64 len)]).
    { intros e [<-|[]]. exists p0, len. repeat split; try lia. all: exact (proj1 HP0). }
    assert (E5_2 : getr r5 2 = Z_to_bv 64 (sp - 48)) by (kept_rw K5; exact D2).
    assert (DEF5 : defined M5 (sp - 48 - AMSTK) (sp - 48)).
    { intros y Hy. apply G5. apply G3. apply DEF. unfold AMSTK, BSTK in *. lia. }
    apply (kat_of_kfx F false). replace (0x66c68%bv : word) with (Z_to_bv 64 AM_ENTRY) by (apply bv_eq; reflexivity).
    apply (HAM F false false st5 L [(Z_to_bv 64 p0, Z_to_bv 64 len)] M5 mdl1 r5 rom (sp - 48) HL (fun E => E) WF5 REP5).
    { apply (LEDGERX_same st st5); [reflexivity | reflexivity | exact HLX1]. }
    { exact XOK. }
    { rewrite MF2. exact Hh. }
    { rewrite MF3. exact Hlz. }
    { rewrite MF4. exact Hmat. }
    { exact HCA. }
    { cbn [length Z.of_nat Pos.of_succ_nat]. change (s_regions st5) with (s_regions st). lia. }
    { rewrite MF1. cbn [h1 vm_limit]. change (s_regions st5) with (s_regions st). rewrite XSUM_one by (ceil; lia). lia. }
    { exact E5_2. }
    { rewrite E1. apply ret_ok_even. reflexivity. }
    { ceil; unfold AMSTK, BSTK in *. lia. }
    { lia. }
    { kept_rw K5. rewrite D21 || (kept_rw K4; gres). all: try (kept_rw K3; kept_rw K2; kept_rw K1; exact R4). }
    { exact DEF5. }
    2: { (* [comment removed for export] *)
      intros c' PF. apply (kf_of_kat F HL).
      (* [comment removed for export] *)
      destruct PF as (st6 & M6 & mdl6 & r6 & -> & WF6 & REP6 & LG6 & Hh6 & Hlz6 & Hmat6 & Hfs6 & Hfds6 & Hvl6 &
                      Elim & Efl & Ear & Emeta & Eerr & KEEP & REG & F10 & F2 & K6 & M6W & DEF6).
      destruct KEEP as (Egrp & Eslot & Ealist & Eai & Ekind & Ecan & Eact & Eus & Ebn & Euq & Esq & Ectr & Esec & Emg & Elm6 & MU6).
      destruct REG as (RS6 & RL6 & RX6).
      rewrite E1. replace (Z_to_bv 64 422092) with (0x670cc%bv : word) by (apply bv_eq; reflexivity).
      assert (AP6 : forall r, In r (s_regions st6) -> p0 + len <= rg_base r \/ rg_base r + rg_len r <= p0).
      { intros r Hr. destruct (RX6 r Hr) as [(r0 & Hr0 & Eb & El)|XX].
        - rewrite <- Eb, <- El. apply AP. exact Hr0.
        - destruct (XX _ (or_introl eq_refl)) as (ea & en & Ee & Hea & Hen0 & Hen & D).
          pose proof (f_equal fst Ee) as Eea. pose proof (f_equal snd Ee) as Een. cbn [fst snd] in Eea, Een.
          apply (f_equal bv_unsigned) in Eea. apply (f_equal bv_unsigned) in Een. rewrite !u64_lit in Eea, Een by (ceil; unfold HEAPLO in *; lia). lia. }
      assert (RGW : forall r, In r (s_regions st6) -> rg_base r + rg_len r <= CEIL).
      { intros r Hr. pose proof (wr_rng st6 (WF_regions st6 L WF6) r Hr). lia. }
      (* [comment removed for export] *)
      assert (AG16 : forall y, sp - 48 <= y < sp -> M6 (Z_to_bv 64 y) = M1 (Z_to_bv 64 y)).
      { intros y Hy. ceil.
        destruct (decide (M6 (Z_to_bv 64 y) = M5 (Z_to_bv 64 y))) as [E6|NE6];
          [|exfalso; destruct (M6W y ltac:(lia) NE6) as [X1|[X1|[X1|(r & Hr' & _ & X1)]]]; [unfold AMSTK in *; lia | unfold CTX_END, CTX in *; lia | unfold A_ERRNO, TPV in *; lia | pose proof (RGW r Hr'); lia]].
        destruct (decide (M5 (Z_to_bv 64 y) = M3 (Z_to_bv 64 y))) as [E5|NE5];
          [|exfalso; pose proof (M5W y ltac:(lia) NE5); unfold CTX in *; lia].
        destruct (decide (M3 (Z_to_bv 64 y) = M2 (Z_to_bv 64 y))) as [E3|NE3];
          [|exfalso; pose proof (zfill_diffZ _ p0 len y ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) NE3); lia].
        destruct (decide (M2 (Z_to_bv 64 y) = M1 (Z_to_bv 64 y))) as [E2'|NE2'];
          [|exfalso; pose proof (M2W y ltac:(lia) NE2'); lia].
        rewrite E6, E5, E3, E2'. reflexivity. }
      assert (STK6 : forall dd v, 8 <= dd <= 48 -> rdn RSEGS M1 (Z_to_bv 64 (sp - dd)) 8%nat = Some (word_to_le_bytes 8 v) ->
                     rdn RSEGS M6 (Z_to_bv 64 (sp - dd)) 8%nat = Some (word_to_le_bytes 8 v)).
      { intros dd v Hd R. rewrite (rdn_agreeZ M1 M6 (sp - dd) 8 ltac:(lia) ltac:(cbn; lia)); [exact R|]. intros y Hr Hy. cbn in Hy. apply AG16. lia. }
      assert (DEF6' : defined M6 (sp - BSTK) sp).
      { intros y Hy. destruct (Z.lt_ge_cases y (sp - 48)) as [LO|HI]; [apply DEF6; unfold AMSTK, BSTK in *; lia|].
        rewrite (AG16 y ltac:(lia)). unfold M1, mal_frame. repeat apply (wbytes_grows _ _ _ (Z_to_bv 64 y)). apply DEF. lia. }
      pose proof (rc_lock st6 M6 (rp_statics st6 M6 REP6)) as Mlk6.
      (* [comment removed for export] *)
      destruct (tY2a M6 sp Mlk6 r6 rom p0 (n + 20) ltac:(rewrite F2; exact E5_2) F10 ltac:(kept_rw K6; exact E20)
                  ltac:(kept_rw K6; kept_rw K5; rewrite D19; exact B19)) as (r7 & RUN7 & G2 & G10 & G11 & G1 & K7).
      eapply kat_msteps; [exact Hh6 | exact Hlz6 | exact RUN7 |].
      (* [comment removed for export] *)
      assert (SOK32 : store_ok RSEGS M6 (Z_to_bv 64 (sp - 48 - 32)) 32%nat = true).
      { eapply (store_ok_defined M6 (sp - BSTK) sp); [exact DEF6' | unfold BSTK; lia | unfold BSTK; cbn; lia | unfold BSTK; lia | lia]. }
      destruct (mUnm1 M6 (sp - 48) p0 (n + 20) ltac:(ceil; unfold BSTK in *; lia) SOK32 r7 rom G2 G10 G11)
        as (r8 & RUN8 & H2 & H17 & H10 & H11 & H8 & H9 & K8).
      eapply kat_msteps; [exact Hh6 | exact Hlz6 | exact RUN8 |].
      set (M8 := mu_frame M6 (sp - 48) (getr r7 1) (getr r7 8) (getr r7 9)) in *.
      assert (M8W : forall y, 0 <= y < 2 ^ 64 -> M8 (Z_to_bv 64 y) <> M6 (Z_to_bv 64 y) -> sp - 80 <= y < sp - 48).
      { intros y Hy NE. unfold M8, mu_frame in NE. ceil. wdiff NE M6 y. }
      assert (G68 : mem_grows M6 M8) by (intros z Hz; unfold M8, mu_frame; repeat apply (wbytes_grows _ _ _ z); exact Hz).
      (* [comment removed for export] *)
      assert (INX : In (Z_to_bv 64 p0, Z_to_bv 64 len) (vm_maps (m_vmmaps mdl6))).
      { apply (Permutation_in _ (Permutation_sym (lx_maps st6 _ _ LG6))). apply in_app_iff. left. left. reflexivity. }
      apply (kat_ecall_munmap_ru r8 (0x68518%bv : word) M8 rom mdl6 W_684c4 (Z_to_bv 64 p0) (n + 20) len (Kf F) F_684c4 E_684c4 Hh6 Hlz6 H17 H10
               ltac:(rewrite u_Z2bv by lia; exact (proj1 HP0)) H11 ltac:(lia) len_eq ltac:(rewrite u_Z2bv by lia; lia) (map_has_In _ _ _ INX)).
      replace (v_addi (0x68518%bv : word) 4) with (0x6851c%bv : word) by (apply bv_eq; reflexivity).
      rewrite (munmap_model_eq (Z_to_bv 64 p0) (Z_to_bv 64 len) mdl6 Hlz6 Hmat6).
      set (h9 := mkVmMapsFull (vm_reserved (m_vmmaps mdl6)) (map_remove (vm_maps (m_vmmaps mdl6)) (Z_to_bv 64 p0))
                  (maps_subtract (vm_noaccess (m_vmmaps mdl6)) (bv_unsigned (Z_to_bv 64 p0)) (bv_unsigned (Z_to_bv 64 p0) + bv_unsigned (Z_to_bv 64 len)))
                  (vm_start_brk (m_vmmaps mdl6)) (vm_brk (m_vmmaps mdl6)) (vm_limit (m_vmmaps mdl6)) (vm_mmap_base (m_vmmaps mdl6)) (vm_init_sp (m_vmmaps mdl6))).
      pose proof (with_vmmaps_facts h9 mdl6) as MF9. destruct MF9 as (MF91 & MF92 & MF93 & MF94 & MF95 & MF96).
      set (mdl9 := with_vmmaps h9 mdl6) in *.
      set (M9 := unfill (Z_to_bv 64 p0) (Z_to_bv 64 len) M8).
      assert (M9out : forall y, 0 <= y < 2 ^ 64 -> ~ (p0 <= y < p0 + len) -> M9 (Z_to_bv 64 y) = M8 (Z_to_bv 64 y)).
      { intros y Hy OUT. unfold M9. apply unfill_outZ; ceil; lia. }
      assert (M9W : forall y, 0 <= y < 2 ^ 64 -> M9 (Z_to_bv 64 y) <> M8 (Z_to_bv 64 y) -> p0 <= y < p0 + len).
      { intros y Hy NE. unfold M9 in NE. exact (unfill_diffZ _ p0 len y ltac:(lia) ltac:(lia) ltac:(ceil; lia) Hy NE). }
      (* [comment removed for export] *)
      assert (STK9 : forall dd v, 8 <= dd <= 24 -> rdn RSEGS M8 (Z_to_bv 64 (sp - 48 - dd)) 8%nat = Some (word_to_le_bytes 8 v) ->
                     rdn RSEGS M9 (Z_to_bv 64 (sp - 48 - dd)) 8%nat = Some (word_to_le_bytes 8 v)).
      { intros dd v Hd R. unfold M9. rewrite rdn_unfill_outZ by (ceil; cbn; lia). exact R. }
      destruct (mUnm2 (sp - 48) ltac:(ceil; unfold BSTK in *; lia) (regupd r8 10 (Z_to_bv 64 0)) rom M9 (0x671a4%bv : word) (getr r7 8) (getr r7 9)
                  ltac:(apply ret_ok_even; reflexivity) ltac:(gres; exact H2) ltac:(gres; reflexivity)
                  (STK9 8 _ ltac:(lia) ltac:(unfold M8, mu_frame; rewrite G1; rdn_solve)) (STK9 16 _ ltac:(lia) ltac:(unfold M8, mu_frame; rdn_solve))
                  (STK9 24 _ ltac:(lia) ltac:(unfold M8, mu_frame; rdn_solve)))
        as (r9 & RUN9 & I2 & I10 & I1 & I8 & I9 & K9).
      eapply kat_msteps; [exact Hh6 | exact Hlz6 | exact RUN9 |].
      (* [comment removed for export] *)
      assert (STK9m : forall dd v, 8 <= dd <= 48 -> rdn RSEGS M1 (Z_to_bv 64 (sp - dd)) 8%nat = Some (word_to_le_bytes 8 v) ->
                      rdn RSEGS M9 (Z_to_bv 64 (sp - dd)) 8%nat = Some (word_to_le_bytes 8 v)).
      { intros dd v Hd R. rewrite (rdn_agreeZ M6 M9 (sp - dd) 8 ltac:(lia) ltac:(cbn; lia)); [exact (STK6 dd v Hd R)|].
        intros y Hr Hy. cbn in Hy. rewrite (M9out y Hr) by (ceil; lia).
        destruct (decide (M8 (Z_to_bv 64 y) = M6 (Z_to_bv 64 y))) as [E|NE]; [exact E|]. exfalso. pose proof (M8W y Hr NE). lia. }
      destruct (tY2b M9 sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) ltac:(ceil; unfold BSTK in *; lia) Rra
                  (STK9m 8 _ ltac:(lia) ltac:(unfold M1, mal_frame; rdn_solve)) (STK9m 16 _ ltac:(lia) ltac:(unfold M1, mal_frame; rdn_solve))
                  (STK9m 24 _ ltac:(lia) ltac:(unfold M1, mal_frame; rdn_solve)) (STK9m 32 _ ltac:(lia) ltac:(unfold M1, mal_frame; rdn_solve))
                  (STK9m 40 _ ltac:(lia) ltac:(unfold M1, mal_frame; rdn_solve)) (STK9m 48 _ ltac:(lia) ltac:(unfold M1, mal_frame; rdn_solve))
                  r9 rom I2)
        as (r10 & RUN10 & J2 & J10 & J1 & J8 & J9 & J18 & J19 & J20 & K10).
      eapply kat_msteps; [exact Hh6 | exact Hlz6 | exact RUN10 |].
      apply kat_refl. apply HQF. unfold malloc_failk.
      exists r10, M9, mdl9, st6.
      split; [reflexivity|].
      split.
      { unfold cs_same. rewrite J2, J8, J9, J18, J19, J20, R2. repeat split; try reflexivity.
        all: kept_rw K10; kept_rw K9; gres; kept_rw K8; kept_rw K7; kept_rw K6; kept_rw K5.
        all: first [ rewrite D21 | kept_rw K4; gres ].
        all: kept_rw K3; kept_rw K2; kept_rw K1; reflexivity. }
      split; [exact J10|].
      assert (APP6 : forall a, app_of L a -> appb st6 a).
      { intros a (bq & k & Hin & Ha). destruct (wL_in st6 L (WF_live st6 L WF6) bq k Hin) as (x & jx & o2 & rr2 & Hx & Hj & Hs).
        exists x, jx, bq, k, o2, rr2. repeat split; try assumption; lia. }
      assert (NAPP0 : forall a, p0 <= a < p0 + len -> ~ app_of L a).
      { intros a Ha Ap. destruct (appb_in_span st6 L WF6 a (APP6 a Ap)) as (x & Hx & Ra).
        destruct (group_in_top st6 L WF6 x Hx) as (t & Ht & Kt & T1 & T2 & Hin). unfold g_map_end in T2.
        destruct (AP6 _ Hin); cbn [rg_base rg_len] in *; lia. }
      split.
      { (* [comment removed for export] *)
        intros a Ha NE.
        destruct (decide (M9 (Z_to_bv 64 a) = M8 (Z_to_bv 64 a))) as [E9|NE9].
        2:{ pose proof (M9W a Ha NE9) as W. right; left. split; [ceil; unfold HEAPLO in *; lia|]. split; [lia | apply NAPP0; lia]. }
        rewrite E9 in NE.
        destruct (decide (M8 (Z_to_bv 64 a) = M6 (Z_to_bv 64 a))) as [E8|NE8].
        2:{ pose proof (M8W a Ha NE8). left. unfold BSTK. lia. }
        rewrite E8 in NE.
        destruct (decide (M6 (Z_to_bv 64 a) = M5 (Z_to_bv 64 a))) as [E6|NE6].
        2:{ destruct (M6W a Ha NE6) as [W|[W|[W|(r & Hr & Hk' & W)]]].
            - left. unfold AMSTK, BSTK in *. lia.
            - right; right; left. exact W.
            - right; right; right. exact W.
            - right; left. exact (nongroup_nonapp L 0%nat st6 r a WF6 Hr Hk' W). }
        rewrite E6 in NE.
        destruct (decide (M5 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a))) as [E5|NE5].
        2:{ pose proof (M5W a Ha NE5). right; right; left. unfold CTX_END, CTX in *. lia. }
        rewrite E5 in NE.
        destruct (M3W a Ha NE) as [W|W]; [left; unfold BSTK; lia | right; left]. split; [ceil; unfold HEAPLO in *; lia |]. split; [lia | apply NAPP0; lia]. }
      split.
      { intros y Hy. rewrite (M9out y ltac:(ceil; unfold BSTK in *; lia)) by (ceil; unfold BSTK in *; lia). apply G68. apply DEF6'. exact Hy. }
      split; [exact WF6|].
      split.
      { (* [comment removed for export] *)
        assert (REP8 : REP st6 M8).
        { apply (REP_frame st6 L M6 WF6 REP6 M8 G68). intros y Hy NE8. left. pose proof (M8W y Hy NE8). ceil; unfold BSTK in *. lia. }
        apply (REP_agree_but st6 L M8 M9 p0 (p0 + len) WF6 REP8).
        - intros y Hy NE. exact (M9W y Hy NE).
        - exact (conj (proj1 (proj2 HP0)) IMGF).
        - intros y Hy. split.
          + intros [D|[D|[D|(x & Hx & Kx & D)]]]; [unfold A_ERRNO, TPV, HEAPLO in *; lia | unfold CTX_END, CTX, HEAPLO in *; lia | |].
            * destruct D as (ar & Har & R). destruct (area_in_region st6 L WF6 ar Har) as (r & Hr & _ & Q1 & Q2). destruct (AP6 r Hr); lia.
            * pose proof (wg_kind st6 L x (wG_each st6 L (WF_groups st6 L WF6) x Hx)) as KD. rewrite Kx in KD. destruct KD as (Y1 & Y2 & _).
              destruct (AP6 _ Y2); cbn [rg_base rg_len] in *; lia.
          + intros (x & Hx & G). pose proof (gcell_in_span st6 L WF6 x y Hx G).
            destruct (ge_inreg st6 (WF_geom st6 L WF6) x Hx) as (r & Hr & Q1 & Q2). destruct (AP6 r Hr); lia. }
      split.
      { unfold mdl9 in MF91 |- *. rewrite MF91. unfold h9. rewrite ?u_Z2bv by (ceil; lia).
        apply (LEDGERX_unmapX st6 p0 len (m_vmmaps mdl6) WF6 LG6 ltac:(lia) ltac:(lia) ltac:(lia) AP6). }
      split.
      { intros x k o Hx Hk E. rewrite Eslot in E. change (s_slot st5 x k) with (s_slot st x k) in E.
        assert (Gx : is_group st x) by (unfold is_group in Hx |- *; rewrite Egrp in Hx; exact Hx).
        apply (NJ x k o Gx); [|exact E]. unfold g_lastidx, g_W in Hk |- *. rewrite Emeta in Hk. exact Hk. }
      split; [unfold nolimbo; rewrite Elim; exact NLB|].
      split; [rewrite MF92; exact Hh6|]. split; [rewrite MF93; exact Hlz6|]. split; [rewrite MF94; exact Hmat6|].
      split; [rewrite MF95, Hfs6; exact MF5|]. split; [rewrite MF96, Hfds6; exact MF6|].
      split; [rewrite MF91; unfold h9; cbn [vm_limit]; rewrite Hvl6, MF1; reflexivity|].
      intros x Hx. assert (Gx : is_group st x) by (unfold is_group in Hx |- *; rewrite Egrp in Hx; exact Hx).
      split; [exact Gx|]. split; [rewrite Ekind; reflexivity|]. split; [unfold g_W; rewrite Emeta; reflexivity|]. rewrite Eslot; reflexivity. }
    intros c' POST. apply (kfx_of_kat F HL false).
    destruct POST as (st6 & M6 & mdl6 & r6 & mm & -> & WF6 & REP6 & LG6 & Hh6 & Hlz6 & Hmat6 & Hfs6 & Hfds6 & Hvl6 &
                      Elim & Um & Zm & NLm6 & Efl & Eerr & KEEP & REG & F10 & F2 & K6 & M6W & DEF6).
    destruct KEEP as (Egrp & Eslot & Ealist & Eai & Ekind & Ecan & Eact & Eus & Ebn & Euq & Esq & Ectr & Esec & Emeta & Elm6 & MU6).
    destruct REG as (RS6 & RL6 & RX6).
    rewrite E1. replace (Z_to_bv 64 422092) with (0x670cc%bv : word) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    assert (LIM6 : In mm (s_limbo st6)) by (rewrite Elim; left; reflexivity).
    destruct (wG_limbo st6 L (WF_groups st6 L WF6) mm LIM6) as (U6 & NG6 & NL6 & NF6).
    destruct (metaU_rng st6 L WF6 mm U6) as (MR1 & MR2 & MR8).
    assert (AP6 : forall r, In r (s_regions st6) -> p0 + len <= rg_base r \/ rg_base r + rg_len r <= p0).
    { intros r Hr. destruct (RX6 r Hr) as [(r0 & Hr0 & Eb & El)|XX].
      - rewrite <- Eb, <- El. apply AP. exact Hr0.
      - destruct (XX _ (or_introl eq_refl)) as (ea & en & Ee & Hea & Hen0 & Hen & D).
        pose proof (f_equal fst Ee) as Eea. pose proof (f_equal snd Ee) as Een. cbn [fst snd] in Eea, Een.
        apply (f_equal bv_unsigned) in Eea. apply (f_equal bv_unsigned) in Een. rewrite !u64_lit in Eea, Een by (ceil; unfold HEAPLO in *; lia). lia. }
    assert (Hgp : mm + 40 <= p0 \/ p0 + len <= mm).
    { destruct (metaU_area st6 L WF6 mm U6) as (ar & k & Har & Hk & Emm & _ & _ & _ & Q1 & Q2 & _).
      destruct (area_in_region st6 L WF6 ar Har) as (r & Hr & _ & W1 & W2). destruct (AP6 r Hr); lia. }
    set (ctr := c_mmap_ctr (s_ctx st6)).
    pose proof (wc_ctr st6 (WF_ctx st6 L WF6)) as Hctr. fold ctr in Hctr.
    (* [comment removed for export] *)
    assert (Z6 : forall y, p0 <= y < p0 + len -> M6 (Z_to_bv 64 y) = Some (Z_to_bv 8 0)).
    { intros y Hy.
      assert (E3 : M3 (Z_to_bv 64 y) = Some (Z_to_bv 8 0)) by (unfold M3; apply zfill_inZ; ceil; lia).
      assert (E5 : M5 (Z_to_bv 64 y) = M3 (Z_to_bv 64 y)).
      { destruct (decide (M5 (Z_to_bv 64 y) = M3 (Z_to_bv 64 y))) as [E|NE]; [exact E|]. exfalso.
        pose proof (M5W y ltac:(ceil; lia) NE). unfold CTX, HEAPLO in *. lia. }
      destruct (decide (M6 (Z_to_bv 64 y) = M5 (Z_to_bv 64 y))) as [E|NE]; [rewrite E, E5; exact E3|]. exfalso.
      destruct (M6W y ltac:(ceil; lia) NE) as [[X1|[X1|[X1|(r & Hr & _ & X1)]]]|HOLE]; [ceil; unfold AMSTK in *; lia | unfold CTX_END, CTX, HEAPLO in *; lia | unfold A_ERRNO, TPV, HEAPLO in *; lia | |
        (* [comment removed for export] *)
        exfalso; exact (am_holeR_X _ _ _ HOLE p0 len ltac:(left; reflexivity) ltac:(unfold HEAPLO in *; lia) ltac:(lia) ltac:(lia) Hy)].
      destruct (AP6 r Hr); lia. }
    assert (SOKg : store_ok RSEGS M6 (Z_to_bv 64 mm) 40%nat = true) by exact (meta_store_ok st6 L M6 WF6 REP6 mm U6).
    assert (SOKp : store_ok RSEGS M6 (Z_to_bv 64 p0) 8%nat = true).
    { eapply (store_ok_defined M6 p0 (p0 + len)); [| lia | cbn; lia | lia | ceil; lia]. intros y Hy. rewrite (Z6 y Hy). discriminate. }
    pose proof (ctx_store_ok st6 M6 REP6) as SOKc6.
    pose proof (rc_ctr st6 M6 (rp_ctx st6 M6 REP6)) as Cctr. fold ctr in Cctr.
    assert (F20 : getr r6 20 = Z_to_bv 64 p0) by (kept_rw K6; exact E20).
    assert (F8 : getr r6 8 = Z_to_bv 64 n) by (kept_rw K6; kept_rw K5; rewrite D8; kept_rw K2; exact A8).
    assert (F9 : getr r6 9 = Z_to_bv 64 MLOCK) by (kept_rw K6; kept_rw K5; rewrite D9; kept_rw K2; exact A9).
    (* [comment removed for export] *)
    destruct (mBig2 M6 mm p0 n ctr ltac:(lia) ltac:(lia) ltac:(lia) Hctr SOKg SOKp SOKc6 Cctr r6 rom F10 F20 F8 F9)
      as (r7 & RUN7 & H18 & H19 & H10 & H20 & H1 & K7).
    eapply kat_msteps; [exact Hh6 | exact Hlz6 | exact RUN7 |].
    set (M7 := m_B2 M6 mm p0 n ctr) in *.
    set (ctr' := (ctr + 1) mod 2 ^ 32) in *.
    pose proof (Z.mod_pos_bound (ctr + 1) (2 ^ 32) ltac:(lia)) as Hctr'. fold ctr' in Hctr'.
    (* [comment removed for export] *)
    assert (M7W : forall y, 0 <= y < 2 ^ 64 -> M7 (Z_to_bv 64 y) <> M6 (Z_to_bv 64 y) ->
                  (mm <= y < mm + 40) \/ (p0 <= y < p0 + len) \/ (ctx_mmap_counter <= y < ctx_mmap_counter + 4)).
    { intros y Hy NE. unfold M7, m_B2, ctx_mmap_counter, CTX in NE. ceil; unfold ctx_mmap_counter, CTX, HEAPLO in *. wdiff NE M6 y. }
    assert (G7 : mem_grows M6 M7) by (intros z Hz; unfold M7, m_B2; repeat apply (wbytes_grows _ _ _ z); exact Hz).
    destruct (meta_cells st6 L M6 WF6 REP6 mm U6) as (ar6 & k6 & _ & _ & _ & _ & _ & _ & RM6 & _). rewrite Zm in RM6.
    destruct RM6 as [Rp6 Rn6 _ _ _ _]. cbn [mr_prev mr_next meta_zero] in Rp6, Rn6.
    assert (HMmeta : rep_meta M7 mm (MR 0 0 p0 0 0 (UbMhMallocKBig.W ml))).
    { unfold M7, m_B2. unfold UbMhMallocKBig.W. rewrite <- Wbig_mkW. ceil; unfold ctx_mmap_counter, CTX, HEAPLO in *.
      pose proof (rdn_wbytes_hit RSEGS (word_to_le_bytes 4 (Z_to_bv 64 0))) as RH4. rewrite length_N_to_le_bytes in RH4.
      constructor; cbn [mr_prev mr_next mr_mem mr_avail mr_freed mr_W]; unfold cell.
      - do 6 rdn_peel1. exact Rp6.
      - do 6 rdn_peel1. exact Rn6.
      - rdn_solve.
      - rdn_peel1. apply RH4. zsimp. lia.
      - do 2 rdn_peel1. apply RH4. zsimp. lia.
      - rdn_solve. }
    assert (HMa : cell M7 p0 8 mm) by (unfold cell, M7, m_B2; ceil; unfold ctx_mmap_counter, CTX, HEAPLO in *; rdn_solve).
    assert (HMz : forall y, p0 + 8 <= y < p0 + 4096 * ml -> M7 (Z_to_bv 64 y) = Some (Z_to_bv 8 0)).
    { intros y Hy. fold len in Hy. destruct (decide (M7 (Z_to_bv 64 y) = M6 (Z_to_bv 64 y))) as [E|NE]; [rewrite E; apply Z6; lia|]. exfalso.
      destruct (M7W y ltac:(ceil; lia) NE) as [X1|[X1|X1]]; [lia | | unfold ctx_mmap_counter, CTX, HEAPLO in *; lia].
      (* [comment removed for export] *)
      unfold M7, m_B2 in NE. ceil; unfold ctx_mmap_counter, CTX, HEAPLO in *.
      rewrite !wbytes_outZ in NE by (wd_lenlit; rewrite ?length_N_to_le_bytes; cbn; lia). exact (NE eq_refl). }
    assert (HMdef : defined M7 p0 (p0 + 4096 * ml)) by (intros y Hy; apply G7; fold len in Hy; rewrite (Z6 y Hy); discriminate).
    assert (HMctr : cell M7 ctx_mmap_counter 4 ctr').
    { unfold cell, M7, m_B2. pose proof (rdn_wbytes_hit RSEGS (word_to_le_bytes 4 (Z_to_bv 64 ctr'))) as RH. rewrite length_N_to_le_bytes in RH. apply RH.
      unfold ctx_mmap_counter, CTX. zsimp. lia. }
    assert (AP6' : forall r, In r (s_regions st6) -> rg_base r + rg_len r <= p0 \/ p0 + 4096 * ml <= rg_base r).
    { intros r Hr. fold len. destruct (AP6 r Hr); lia. }
    destruct (big_close st6 L M6 M7 mm p0 ml ctr' WF6 REP6 U6 NG6 NL6 NF6 ltac:(fold len; exact HP0) ltac:(fold len; exact IMGF) ltac:(fold len; lia) AP6' Hctr' sp sp ltac:(ceil; lia)
                ltac:(intros y Hy NE; destruct (M7W y Hy NE) as [X1|[X1|X1]]; [left; exact X1 | right; left; fold len; exact X1 | right; right; left; exact X1])
                G7 HMmeta HMa HMz HMdef HMctr) as [WF7 REP7].
    pose proof (t_ledger st6 mm p0 ml ctr' _ ltac:(fold len; exact LG6)) as LG7.
    destruct (big_facts st6 L mm p0 ml ctr' WF6 NG6 ltac:(fold len; lia)) as (Gm & Sm0 & Lm & STm & SSm & SCm & Km & MEMm & R63 & LIM7 & REG7 & SLOT7 & ISG7).
    set (st7 := UbMhMallocKBig.st' st6 mm p0 ml ctr') in *.
    (* [comment removed for export] *)
    assert (Mlk : rdn RSEGS M7 (Z_to_bv 64 MLOCK) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0))) by exact (rc_lock st7 M7 (rp_statics st7 M7 REP7)).
    destruct (mU M7 Mlk r7 rom (Z_to_bv 64 0x67270) H10 H1 ltac:(apply ret_ok_even; reflexivity)) as (r8 & RUN8 & K8).
    eapply kat_msteps; [exact Hh6 | exact Hlz6 | exact RUN8 |].
    replace (Z_to_bv 64 0x67270) with (0x67270%bv : word) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    assert (RGW : forall r, In r (s_regions st6) -> rg_base r + rg_len r <= CEIL).
    { intros r Hr. pose proof (wr_rng st6 (WF_regions st6 L WF6) r Hr). lia. }
    assert (AG17 : agree_on (fun y => sp - 48 <= y < sp) M1 M7).
    { intros y Hr Hy. cbv beta in Hy.
      destruct (decide (M7 (Z_to_bv 64 y) = M6 (Z_to_bv 64 y))) as [E7|NE7];
        [|exfalso; destruct (M7W y Hr NE7) as [X1|[X1|X1]]; ceil; unfold ctx_mmap_counter, CTX in *; lia].
      destruct (decide (M6 (Z_to_bv 64 y) = M5 (Z_to_bv 64 y))) as [E6|NE6];
        [|exfalso; destruct (M6W y Hr NE6) as [[X1|[X1|[X1|(r & Hr' & _ & X1)]]]|HOLE]; [unfold AMSTK in *; lia | ceil; unfold CTX_END, CTX in *; lia | ceil; unfold A_ERRNO, TPV in *; lia | pose proof (RGW r Hr'); ceil; lia | destruct (am_holeR_rng _ _ _ HOLE) as [HB0 _]; ceil; lia]].
      destruct (decide (M5 (Z_to_bv 64 y) = M3 (Z_to_bv 64 y))) as [E5|NE5];
        [|exfalso; pose proof (M5W y Hr NE5); ceil; unfold CTX in *; lia].
      destruct (decide (M3 (Z_to_bv 64 y) = M2 (Z_to_bv 64 y))) as [E3|NE3];
        [|exfalso; pose proof (zfill_diffZ _ p0 len y ltac:(lia) ltac:(lia) ltac:(ceil; lia) Hr NE3); ceil; lia].
      destruct (decide (M2 (Z_to_bv 64 y) = M1 (Z_to_bv 64 y))) as [E2'|NE2'];
        [|exfalso; pose proof (M2W y Hr NE2'); lia].
      rewrite E7, E6, E5, E3, E2'. reflexivity. }
    assert (STK7 : forall d v, 8 <= d <= 48 -> rdn RSEGS M1 (Z_to_bv 64 (sp - d)) 8%nat = Some (word_to_le_bytes 8 v) ->
                   rdn RSEGS M7 (Z_to_bv 64 (sp - d)) 8%nat = Some (word_to_le_bytes 8 v)).
    { intros d v Hd R. rewrite (rdn_agreeZ M1 M7 (sp - d) 8 ltac:(lia) ltac:(cbn; lia)); [exact R|].
      eapply agree_on_mono; [exact AG17|]. cbn. intros; lia. }
    assert (G2 : getr r8 2 = Z_to_bv 64 (sp - 48)) by (kept_rw K8; kept_rw K7; rewrite F2; exact E5_2).
    destruct (mBig3 M7 sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) ltac:(ceil; lia)
                (STK7 8 _ ltac:(lia) ltac:(unfold M1, mal_frame; rdn_solve)) (STK7 16 _ ltac:(lia) ltac:(unfold M1, mal_frame; rdn_solve))
                (STK7 24 _ ltac:(lia) ltac:(unfold M1, mal_frame; rdn_solve)) (STK7 32 _ ltac:(lia) ltac:(unfold M1, mal_frame; rdn_solve))
                (STK7 40 _ ltac:(lia) ltac:(unfold M1, mal_frame; rdn_solve)) (STK7 48 _ ltac:(lia) ltac:(unfold M1, mal_frame; rdn_solve))
                r8 rom G2) as (r9 & RUN9 & I10 & I11 & I12 & I13 & I2 & I1 & I8 & I9 & I18 & I19 & I20 & K9).
    eapply kat_msteps; [exact Hh6 | exact Hlz6 | exact RUN9 |].
    (* [comment removed for export] *)
    set (strideT := g_stride st7 mm). set (startT := g_slot_start st7 mm 0).
    set (cT := getr r9 13).
    set (offT := enframe_off (slack_of strideT n) ((if 0 =? 0 then bv_unsigned cT else 0 + 1) mod 256)).
    pose proof (mkW_fields 0 1 63 ml ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (WF1 & WF2 & WF3 & WF4).
    destruct HMmeta as [_ _ Rme _ _ RWm]. cbn [mr_mem mr_W] in Rme, RWm. unfold UbMhMallocKBig.W in RWm.
    assert (EFH : efH M7 cT mm p0 (mkW 0 1 63 ml) 0 n 0 0 strideT startT offT).
    { pose proof HP0 as (HP1 & HP2 & HP3). ceil; unfold HEAPLO in HP2, HP3, MR1, MR2. constructor.
      - rewrite WF1, WF3, WF4. subst strideT. rewrite STm. unfold slot_stride, UNIT.
        replace (negb (ml =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia). cbn [andb Z.eqb]. lia.
      - subst startT strideT. rewrite SSm. unfold slot_start, UNIT. lia.
      - reflexivity.
      - lia.
      - lia.
      - unfold mkW. lia.
      - lia.
      - subst strideT. rewrite STm. fold len. lia.
      - rewrite WF1, WF4. intros [A|A]; exfalso; lia.
      - subst strideT. rewrite STm. fold len. lia.
      - lia.
      - subst startT strideT. rewrite SSm, STm. fold len. ceil. lia.
      - subst startT strideT. rewrite SSm, STm. fold len. lia.
      - lia.
      - lia.
      - exact Rme.
      - exact RWm.
      - subst startT. rewrite SSm. replace (p0 + 16 - 4) with (p0 + 12) by lia. apply HMz. fold len. lia.
      - subst startT. rewrite SSm. replace (p0 + 16 - 3) with (p0 + 13) by lia. apply HMz. fold len. lia.
      - intros NE. exfalso. exact (NE eq_refl).
      - subst startT strideT. rewrite SSm, STm. eapply (store_ok_defined M7 p0 (p0 + 4096 * ml)); [exact HMdef | lia | rewrite Z2Nat.id by lia; lia | lia | ceil; lia].
      - intros j Hj. exact (rc_tab_sc st7 M7 (rp_statics st7 M7 REP7) (SCT + j) ltac:(unfold SCT, A_TAB_SC, A_TAB_MED; lia)). }
    assert (I10' : getr r9 10 = Z_to_bv 64 mm) by (rewrite I10; kept_rw K8; exact H18).
    assert (I11' : getr r9 11 = Z_to_bv 64 0) by (rewrite I11; kept_rw K8; exact H19).
    assert (I12' : getr r9 12 = Z_to_bv 64 n) by (rewrite I12; kept_rw K8; kept_rw K7; exact F8).
    destruct (ref_enframe r9 M7 rom (getr regs 1) cT mm p0 (mkW 0 1 63 ml) 0 n 0 0 strideT startT offT EFH I1 Rra I10' I11' I12' eq_refl)
      as (r10 & M8 & RUN10 & KCS & J10 & FRM & POST).
    eapply kat_msteps; [exact Hh6 | exact Hlz6 | exact RUN10 |].
    (* [comment removed for export] *)
    destruct FRM as [FR1 G8].
    assert (M8W : forall a, 0 <= a < 2 ^ 64 -> M8 (Z_to_bv 64 a) <> M7 (Z_to_bv 64 a) -> startT - 3 <= a < startT + strideT - 4).
    { intros a Ha NE. destruct (decide (startT - 3 <= a < startT + strideT - 4)) as [IN|OUT]; [exact IN|]. exfalso. apply NE. apply FR1.
      cbn [outside]. split; [|exact I]. unfold in_rng. subst startT strideT. rewrite SSm, STm in *. fold len in OUT. rewrite !u64_lit by (ceil; lia). lia. }
    assert (Hn7 : 0 <= n /\ n + 4 <= strideT) by (subst strideT; rewrite STm; fold len; lia).
    destruct (enframe_close st7 L M7 M8 mm 0 n offT WF7 REP7 Gm ltac:(rewrite Lm; lia) Sm0 Hn7 ltac:(change (g_stride st7 mm - n < 2 ^ 31); rewrite STm; fold len; lia) POST M8W G8
                ltac:(intros _ b l Hin; rewrite (R63 b l Hin); fold len; lia) HLL ltac:(rewrite SCm; lia)) as [WF8 REP8].
    pose proof (UbMhEnfr.L_apart st7 L M8 mm 0 n offT WF7 Gm ltac:(rewrite Lm; lia) Sm0 Hn7 POST) as APL.
    pose proof (UbMhEnfr.p_notin_L st7 L M8 mm 0 n offT WF7 Gm ltac:(rewrite Lm; lia) Sm0 Hn7 POST) as NIL.
    pose proof (UbMhEnfr.e_ledger st7 mm 0 n offT _ LG7) as LG8.
    set (st8 := UbMhEnfr.st' st7 mm 0 n offT) in *.
    pose proof (Pr _ _ _ _ _ _ POST) as (PR1 & PR2 & PR3). unfold P_r in PR1. unfold P_q in PR3.
    (* [comment removed for export] *)
    apply kat_refl. apply (kw_of_ok RSEGS F HL). apply HQ. unfold malloc_postk.
    exists r10, M8, mdl6, (startT + 16 * offT), st8.
    assert (APP6 : forall a, app_of L a -> appb st6 a).
    { intros a (b & k & Hin & Ha). destruct (wL_in st6 L (WF_live st6 L WF6) b k Hin) as (x & j & o2 & rr2 & Hx & Hj & Hs).
      exists x, j, b, k, o2, rr2. repeat split; try assumption; lia. }
    assert (APPR : forall a, appb st6 a -> exists t, In (RG (g_mem st6 t) (4096 * g_maplen st6 t) (RGroup t)) (s_regions st6) /\
                                           g_mem st6 t <= a < g_mem st6 t + 4096 * g_maplen st6 t).
    { intros a Ap. destruct (appb_in_span st6 L WF6 a Ap) as (x & Hx & Ra).
      destruct (group_in_top st6 L WF6 x Hx) as (t & Ht & Kt & T1 & T2 & Hin). exists t. split; [exact Hin|]. unfold g_map_end in T2. lia. }
    assert (NAPP0 : forall a, p0 <= a < p0 + len -> ~ app_of L a).
    { intros a Ha Ap. destruct (APPR a (APP6 a Ap)) as (t & Hin & Rt). destruct (AP6 _ Hin); cbn [rg_base rg_len] in *; lia. }
    pose proof HP0 as (HP1 & HP2 & HP3).
    split; [reflexivity|].
    split.
    { (* [comment removed for export] *)
      unfold cs_same.
      (* [comment removed for export] *)
      destruct (kcs15 _ _ KCS) as (KC2 & KC3 & KC4 & KC8 & KC9 & KC18 & KC19 & KC20 & KC21 & KC22 & KC23 & KC24 & KC25 & KC26 & KC27).
      rewrite KC2, KC3, KC4, KC8, KC9, KC18, KC19, KC20, KC21, KC22, KC23, KC24, KC25, KC26, KC27.
      clear KC2 KC3 KC4 KC8 KC9 KC18 KC19 KC20 KC21 KC22 KC23 KC24 KC25 KC26 KC27.
      rewrite I2, I8, I9, I18, I19, I20, R2.
      repeat split; try reflexivity.
      all: kept_rw K9; kept_rw K8; kept_rw K7; kept_rw K6; kept_rw K5.
      all: first [ rewrite D21 | kept_rw K4; gres ].
      all: kept_rw K3; kept_rw K2; kept_rw K1; reflexivity. }
    split; [exact J10|].
    split. { subst startT. rewrite SSm. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - HP1 PR2. lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    split. { subst startT. rewrite SSm. unfold HEAPLO in *. lia. }
    split. { subst startT strideT. rewrite SSm, STm in *. ceil. lia. }
    split. { subst startT strideT. rewrite SSm, STm in *. lia. }
    split; [exact NIL|].
    split; [exact APL|].
    split.
    { (* [comment removed for export] *)
      intros a Ha NE.
      destruct (metaU_area st6 L WF6 mm U6) as (ar & k & Har & Hk & Emm & _ & _ & _ & Q1 & Q2 & _).
      destruct (decide (M8 (Z_to_bv 64 a) = M7 (Z_to_bv 64 a))) as [E8|NE8].
      2:{ pose proof (M8W a Ha NE8) as W. subst startT strideT. rewrite SSm, STm in W. right; left.
          split; [ceil; unfold HEAPLO in *; lia |]. split; [lia | apply NAPP0; lia]. }
      rewrite E8 in NE.
      destruct (decide (M7 (Z_to_bv 64 a) = M6 (Z_to_bv 64 a))) as [E7|NE7].
      2:{ destruct (M7W a Ha NE7) as [W|[W|W]].
          - right; left. split; [ceil; unfold HEAPLO in *; lia|]. split; [pose proof (metaU_img st6 L WF6 mm U6); lia|]. intros Ap.
            apply (ge_app_area st6 (WF_geom st6 L WF6) a (APP6 a Ap)). exists ar. split; [exact Har | lia].
          - right; left. split; [ceil; unfold HEAPLO in *; lia |]. split; [lia | apply NAPP0; lia].
          - right; right; left. unfold ctx_mmap_counter, CTX_END, CTX in *. lia. }
      rewrite E7 in NE.
      destruct (decide (M6 (Z_to_bv 64 a) = M5 (Z_to_bv 64 a))) as [E6|NE6].
      2:{ destruct (M6W a Ha NE6) as [[W|[W|[W|(r & Hr & Hk' & W)]]]|HOLE].
          - left. unfold AMSTK, BSTK in *. lia.
          - right; right; left. exact W.
          - right; right; right. exact W.
          - right; left. pose proof (wr_rng st6 (WF_regions st6 L WF6) r Hr) as (X1 & X2 & _). split; [lia|]. split; [pose proof (region_img st6 L WF6 r Hr); lia|].
            intros Ap. destruct (APPR a (APP6 a Ap)) as (t & Hin & Rt).
            assert (Hne : RG (g_mem st6 t) (4096 * g_maplen st6 t) (RGroup t) <> r) by (intros <-; exact (Hk' t eq_refl)).
            destruct (wr_disj st6 (WF_regions st6 L WF6) _ _ Hin Hr Hne); cbn [rg_base rg_len] in *; lia.
          - (* [comment removed for export] *)
            right; left. exact (am_holeR_nonapp st6 L _ a WF6 HOLE). }
      rewrite E6 in NE.
      destruct (decide (M5 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a))) as [E5|NE5].
      2:{ pose proof (M5W a Ha NE5). right; right; left. unfold CTX_END, CTX in *. lia. }
      rewrite E5 in NE.
      destruct (M3W a Ha NE) as [W|W]; [left; unfold BSTK; lia | right; left]. split; [ceil; unfold HEAPLO in *; lia |]. split; [lia | apply NAPP0; lia]. }
    split.
    { intros y Hy. apply G8. apply G7. destruct (Z.lt_ge_cases y (sp - 48)) as [LO|HI]; [apply DEF6; unfold AMSTK, BSTK in *; lia|].
      destruct (decide (M6 (Z_to_bv 64 y) = M5 (Z_to_bv 64 y))) as [E|NE6].
      - rewrite E. apply G5. apply G3. apply DEF. lia.
      - exfalso. destruct (M6W y ltac:(lia) NE6) as [[W|[W|[W|(r & Hr & _ & W)]]]|HOLE]; [lia | ceil; unfold CTX_END, CTX in *; lia | ceil; unfold A_ERRNO, TPV in *; lia | pose proof (RGW r Hr); ceil; lia | destruct (am_holeR_rng _ _ _ HOLE) as [HB0 _]; ceil; lia]. }
    split.
    { intros y Hy. apply G8. apply HMdef. subst startT strideT. rewrite SSm, STm in *. fold len. lia. }
    split; [exact WF8|]. split; [exact REP8|]. split; [exact LG8|].
    split.
    { intros x k o Hx Hk. cbn [s_slot st8 UbMhEnfr.st' set_slot]. unfold is_group in Hx. cbn [s_groups st8 UbMhEnfr.st' set_slot] in Hx.
      change (In x (s_groups st7)) with (is_group st7 x) in Hx.
      destruct (Z.eqb_spec x mm) as [->|Hxm]; cbn [andb].
      - change (g_lastidx st8 mm) with (g_lastidx st7 mm) in Hk. rewrite Lm in Hk. replace k with 0 by lia. cbn. discriminate.
      - apply ISG7 in Hx. destruct Hx as [E|Hx]; [exfalso; exact (Hxm E)|].
        rewrite (SLOT7 x k ltac:(apply ISG7; right; exact Hx) Hxm). rewrite Eslot. change (s_slot st5 x k) with (s_slot st x k).
        assert (Gx : is_group st x) by (unfold is_group in Hx |- *; rewrite Egrp in Hx; exact Hx).
        apply (NJ x k o); [exact Gx|].
        unfold g_lastidx, g_W in Hk |- *. cbn [s_meta st8 UbMhEnfr.st' set_slot st7 UbMhMallocKBig.st'] in Hk. unfold UbMhMallocKBig.b_meta in Hk.
        rewrite (proj2 (Z.eqb_neq x mm) Hxm) in Hk. rewrite (Emeta x Gx) in Hk. exact Hk. }
    split.
    { unfold nolimbo. cbn [s_limbo st8 UbMhEnfr.st' set_slot]. rewrite LIM7, Elim. change (s_limbo st5) with (s_limbo st). rewrite NLB.
      unfold zremove. cbn. rewrite Z.eqb_refl. reflexivity. }
    split; [exact Hh6|]. split; [exact Hlz6|]. split; [exact Hmat6|].
    split; [rewrite Hfs6; exact MF5|]. split; [rewrite Hfds6; exact MF6|].
    split; [rewrite Hvl6, MF1; reflexivity|].
    (* [comment removed for export] *)
    intros x Hx. unfold is_group in Hx. cbn [s_groups st8 UbMhEnfr.st' set_slot] in Hx.
    change (In x (s_groups st7)) with (is_group st7 x) in Hx.
    destruct (Z.eqb_spec x mm) as [->|Hxm].
    - left. split; [change (g_lastidx st8 mm) with (g_lastidx st7 mm); exact Lm|].
      split; [change (s_kind st8 mm) with (s_kind st7 mm); exact Km|].
      split. { change (g_maplen st8 mm) with (g_maplen st7 mm). unfold g_maplen, g_W. cbn [s_meta st7 UbMhMallocKBig.st']. unfold UbMhMallocKBig.b_meta.
               rewrite Z.eqb_refl. cbn [mr_W]. unfold UbMhMallocKBig.W. rewrite (proj2 (proj2 (proj2 (mkW_fields 0 1 63 ml ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))))). lia. }
      split; [left; change (g_sc st8 mm) with (g_sc st7 mm); rewrite SCm; lia|].
      cbn [s_slot st8 UbMhEnfr.st' set_slot]. rewrite !Z.eqb_refl. cbn [andb]. eexists _, _, _, _. reflexivity.
    - right. apply ISG7 in Hx. destruct Hx as [E|Hx]; [exfalso; exact (Hxm E)|].
      assert (Gx : is_group st x) by (unfold is_group in Hx |- *; rewrite Egrp in Hx; exact Hx).
      split; [exact Gx|].
      split. { cbn [s_kind st8 UbMhEnfr.st' set_slot st7 UbMhMallocKBig.st']. unfold UbMhMallocKBig.b_kind. rewrite (proj2 (Z.eqb_neq x mm) Hxm).
               rewrite Ekind. reflexivity. }
      split. { unfold g_W. cbn [s_meta st8 UbMhEnfr.st' set_slot st7 UbMhMallocKBig.st']. unfold UbMhMallocKBig.b_meta. rewrite (proj2 (Z.eqb_neq x mm) Hxm).
               rewrite (Emeta x Gx). reflexivity. }
      cbn [s_slot st8 UbMhEnfr.st' set_slot]. rewrite (proj2 (Z.eqb_neq x mm) Hxm). cbn [andb].
      change (s_slot st7 x 0 = s_slot st x 0). rewrite (SLOT7 x 0 ltac:(apply ISG7; right; exact Hx) Hxm). rewrite Eslot. reflexivity.
  Qed.
End Big.