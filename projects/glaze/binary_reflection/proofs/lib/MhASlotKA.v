(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.glaze.binary_reflection.images.Plain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhMmapK OSSVerify.Proofs.glaze.binary_reflection.lib.MhNtf OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Module MhASpec3.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.glaze.binary_reflection.images.Plain.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhKX OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhMmapK.MhAcct OSSVerify.Proofs.glaze.binary_reflection.lib.MhNtf OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaS.MhMSpec3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition AS_ENTRY : Z := 0x62c40.
Definition AS_CLOB : list reg := AM_CLOB.
(* [comment removed for export] *)
Definition ASSTK (d : nat) : Z := 144 * (Z.of_nat d + 1) + AMSTK.

(* [comment removed for export] *)
Definition dle (a b : nat) : Prop := (a <= b)%nat.

Lemma ASSTK_S : forall d, ASSTK (S d) = ASSTK d + 144.
Proof. intros d. unfold ASSTK. rewrite Nat2Z.inj_succ. lia. Qed.
Lemma ASSTK_ge : forall d, 288 <= ASSTK d.
Proof. intros d. unfold ASSTK, AMSTK. lia. Qed.


Section Spec.
  Context {fx : FPState} {RN : run_ceil}.

  (* [comment removed for export] *)
  Definition as_wr (d : nat) (sp : Z) (L : list (Z * Z)) (a : Z) : Prop :=
    (sp - ASSTK d <= a < sp) \/
    (HEAPLO <= a < CEIL /\ (a < IMG_LO \/ IMG_HI <= a) /\ ~ app_of L a) \/
    (CTX <= a < CTX_END) \/ (A_ERRNO <= a < A_ERRNO + 4).

  (* [comment removed for export] *)
  Definition as_ok (st : mst) (L : list (Z * Z)) (sc req : Z) (d : nat) (sp : Z)
             (regs : bvmap 5 word) (M : mem) (mdl : Model) (rom : word -> option byte) (c' : config) : Prop :=
    exists st' M' mdl' regs' (g idx : Z),
      c' = mkCfg (mkst regs' (getr regs 1) M' rom) mdl' /\
      WF st' L /\ REP st' M' /\ LEDGER st' (m_vmmaps mdl') /\
      m_halted mdl' = None /\ m_vm_lazy mdl' = [] /\ m_vm_materialized mdl' = [] /\
      m_fs mdl' = m_fs mdl /\ m_fds mdl' = m_fds mdl /\ vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl) /\
      (* [comment removed for export] *)
      s_limbo st' = s_limbo st /\ s_canary st' = s_canary st /\ (s_errno st' = s_errno st \/ s_errno st' = 12) /\
      head_of (s_alist st' sc) = g /\ is_group st' g /\ g_sc st' g = sc /\
      0 <= idx <= g_lastidx st' g /\ s_slot st' g idx = SJunk 0 /\ only_junk st' g idx /\
      req + 4 <= g_stride st' g /\ (16 * size_class sc <= g_stride st' g \/ 4080 <= g_stride st' g) /\
      (forall k, 0 <= k < sc -> s_alist st' k = s_alist st k) /\
      (forall x, In x (s_limbo st) -> s_meta st' x = s_meta st x) /\ (forall x, metaU st x -> metaU st' x) /\
      (* [comment removed for export] *)
      getr regs' 10 = Z_to_bv 64 idx /\ getr regs' 2 = getr regs 2 /\ keeps_but AS_CLOB regs regs' /\
      (* [comment removed for export] *)
      (forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> as_wr d sp L a) /\
      defined M' (sp - ASSTK d) sp.

  (* [comment removed for export] *)
  Definition as_fail (st : mst) (L : list (Z * Z)) (sc : Z) (d : nat) (sp : Z)
             (regs : bvmap 5 word) (M : mem) (mdl : Model) (rom : word -> option byte) (c' : config) : Prop :=
    exists st' M' mdl' regs',
      c' = mkCfg (mkst regs' (getr regs 1) M' rom) mdl' /\
      WF st' L /\ REP st' M' /\ LEDGER st' (m_vmmaps mdl') /\
      m_halted mdl' = None /\ m_vm_lazy mdl' = [] /\ m_vm_materialized mdl' = [] /\
      m_fs mdl' = m_fs mdl /\ m_fds mdl' = m_fds mdl /\ vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl) /\
      (* [comment removed for export] *)
      nojunk st' /\ s_limbo st' = s_limbo st /\ s_canary st' = s_canary st /\
      (forall x, In x (s_limbo st) -> s_meta st' x = s_meta st x) /\ (forall x, metaU st x -> metaU st' x) /\
      (* [comment removed for export] *)
      getr regs' 10 = Z_to_bv 64 (2 ^ 64 - 1) /\ getr regs' 2 = getr regs 2 /\ keeps_but AS_CLOB regs regs' /\
      (* [comment removed for export] *)
      (forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> as_wr d sp L a) /\
      defined M' (sp - ASSTK d) sp.

  (* [comment removed for export] *)
  Definition AS_SPEC3 (d : nat) : Prop :=
    forall (F : kfam) (bi bo : bool) st L (M : mem) mdl regs rom sp sc req,
      kfam_laws RSEGS F -> (bo = true -> bi = true \/ agf st) ->
      WF st L -> REP st M -> LEDGER st (m_vmmaps mdl) -> nojunk st ->
      m_halted mdl = None -> m_vm_lazy mdl = [] -> m_vm_materialized mdl = [] ->
      0 <= sc < 48 -> dle (dbound (16 * size_class sc)) d ->
      zlen (s_limbo st) + Z.of_nat d + 1 <= 8 ->
      0 <= req /\ req + 4 <= 16 * size_class sc ->
      PHI L + MBASE <= vm_limit (m_vmmaps mdl) ->
      getr regs 10 = Z_to_bv 64 sc -> getr regs 11 = Z_to_bv 64 req ->
      getr regs 2 = Z_to_bv 64 sp -> ret_ok (getr regs 1) -> getr regs 4 = Z_to_bv 64 TPV ->
      CEIL + ASSTK d <= sp -> sp < 2 ^ 64 ->
      defined M (sp - ASSTK d) sp ->
      (forall c', as_ok st L sc req d sp regs M mdl rom c' -> kfx F bi c') ->
      (forall c', as_fail st L sc d sp regs M mdl rom c' -> Kf F c') ->
      kfx F bo (mkCfg (mkst regs (Z_to_bv 64 AS_ENTRY) M rom) mdl).
End Spec.

(* [comment removed for export] *)
Section KatClass.
  Context {fx : FPState}.
  Variable F : kfam.
  Hypothesis HL : kfam_laws RSEGS F.

  Lemma kfx_of_kat : forall b c, kat RSEGS c (kfx F b) -> kfx F b c.
  Proof using HL. intros b c H. exact (H (kfx F b) (kfx_closed RSEGS F HL b) (fun c' X => X)). Qed.
  Lemma kat_of_kfx : forall b c, kfx F b c -> kat RSEGS c (kfx F b).
  Proof using. intros b c H K HK HQ. exact (HQ c H). Qed.
  Lemma kf_of_kat : forall c, kat RSEGS c (Kf F) -> Kf F c.
  Proof using HL. intros c H. exact (H (Kf F) (kl_f RSEGS F HL) (fun c' X => X)). Qed.


End KatClass.
End MhASpec3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhEnframeBase OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaN OSSVerify.Proofs.glaze.binary_reflection.lib.MhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.MhNtf2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module MhEfh.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.glaze.binary_reflection.images.Plain.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhEnframeBase OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaN.MhNtfLib OSSVerify.Proofs.glaze.binary_reflection.lib.MhNest2.MhNest OSSVerify.Proofs.glaze.binary_reflection.lib.MhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhCover OSSVerify.Proofs.glaze.binary_reflection.lib.MhNtf2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Efh.
  Context {RN : mh_run}.
  Context {fx : FPState}.

  Lemma byte_of_def : forall (M : mem) a, M (Z_to_bv 64 a) <> None ->
    exists h, 0 <= h < 256 /\ M (Z_to_bv 64 a) = Some (Z_to_bv 8 h).
  Proof using.
    intros M a H. destruct (M (Z_to_bv 64 a)) as [b|] eqn:E; [|exfalso; exact (H eq_refl)].
    exists (bv_unsigned b). split; [exact (u8_range b)|]. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
  Qed.

  Lemma rdn2_of_def : forall (M : mem) a, 0 <= a -> a + 2 <= 2 ^ 64 ->
    M (Z_to_bv 64 a) <> None -> M (Z_to_bv 64 (a + 1)) <> None ->
    exists v, 0 <= v < 65536 /\ rdn RSEGS M (Z_to_bv 64 a) 2%nat = Some (word_to_le_bytes 2 (Z_to_bv 64 v)).
  Proof using.
    intros M a Ha Ha2 D0 D1.
    destruct (byte_of_def M a D0) as (b0 & Hb0 & E0). destruct (byte_of_def M (a + 1) D1) as (b1 & Hb1 & E1).
    exists (b0 + 256 * b1). split; [lia|].
    cbn [rdn]. rewrite E0.
    replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1))
      by (apply bv_eq; rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod; change (bv_unsigned (1 : word)) with 1%Z;
          rewrite (Z.mod_small a) by lia; reflexivity).
    rewrite E1.
    unfold word_to_le_bytes. cbn [Z_to_le_bytes]. rewrite u_Z2bv by lia.
    do 2 f_equal; [|f_equal]; apply bv_eq; rewrite !Z_to_bv_unsigned, !bv_wrap8_mod; [|rewrite Z.shiftr_div_pow2 by lia].
    - change (2 ^ 8) with 256. rewrite Z.mul_comm, Z.mod_add by lia. reflexivity.
    - change (2 ^ 8) with 256. replace ((b0 + 256 * b1) / 256) with b1 by (symmetry; rewrite Z.mul_comm, Z.div_add by lia; rewrite Z.div_small by lia; lia). reflexivity.
  Qed.

  Variables (st : mst) (L : list (Z * Z)) (M : mem).
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.

  (* [comment removed for export] *)
  Lemma meta_apart_span : forall g, is_group st g -> g + 40 <= g_mem st g \/ gspan st g <= g.
  Proof using HREP HWF M L RN.
    intros g Hg.
    destruct (G_meta_cells st L M HWF HREP g Hg) as (ar & k & Har & Hk & Eg & _ & Lo & Hi & _ & _ & _ & _).
    destruct (wa_rng st (WF_areas st L HWF) ar Har) as (Hal & Alo & Ahi).
    assert (IN : ar + 24 <= g /\ g + 40 <= ar + 4096) by (rewrite Eg; unfold meta_addr, AREA_HDR, META_SZ, NSLOTS in *; lia).
    destruct (Z.lt_ge_cases (g_mem st g) (g + 40)) as [A|A]; [|left; exact A].
    destruct (Z.lt_ge_cases g (gspan st g)) as [B|B]; [|right; exact B].
    exfalso.
    (* [comment removed for export] *)
    set (y := Z.max (g_mem st g) ar).
    apply (ge_area st (WF_geom st L HWF) g y Hg).
    - pose proof (gspan_gt st L HWF g Hg). subst y. lia.
    - exists ar. split; [exact Har|]. subst y. lia.
  Qed.

  Theorem efH_junk : forall g idx n (c : word),
    is_group st g -> 0 <= idx <= g_lastidx st g -> g_sc st g < 48 -> 0 <= n -> n + 4 <= g_stride st g ->
    exists h3 o16,
      efH M c g (g_mem st g) (g_W st g) idx n h3 o16 (g_stride st g) (g_slot_start st g idx)
          (enframe_off (slack_of (g_stride st g) n) ((if h3 =? 0 then bv_unsigned c else o16 + 1) mod 256)).
  Proof using HREP HWF L RN.
    intros g idx n c Hg Hidx Hsc Hn0 Hn.
    pose proof (wG_each st L (WF_groups st L HWF) g Hg) as WG.
    pose proof (wg_stride st L g WG) as [S16 Smod]. pose proof (wg_mem st L g WG) as (M0 & M16 & M47).
    pose proof (wg_Wr st L g WG) as WR. pose proof (wg_q st L g WG Hsc) as Q20. pose proof (wg_sc st L g WG) as SC.
    pose proof (glast_rng st g) as GL.
    destruct (G_meta_cells st L M HWF HREP g Hg) as (ar & k & Har & Hk & Eg & _ & Lo & Hi & _ & RM & _ & _).
    pose proof (slot_in_span st L HWF g idx Hg Hidx) as [SP1 SP2].
    pose proof (group_range st L HWF g Hg) as [GR1 GR2].
    pose proof (group_bytes_defined st L M 8 g HWF HREP (wg_depth st L g WG) Hg) as DEF.
    assert (Ess : g_slot_start st g idx = g_mem st g + 16 + g_stride st g * idx) by (unfold g_slot_start, UNIT; lia).
    assert (Ese : g_slot_end st g idx = g_slot_start st g idx + g_stride st g - 4) by (unfold g_slot_end, IB; lia).
    set (start := g_slot_start st g idx) in *.
    assert (D3 : M (Z_to_bv 64 (start - 3)) <> None) by (apply DEF; lia).
    assert (D2 : M (Z_to_bv 64 (start - 2)) <> None) by (apply DEF; lia).
    assert (D1 : M (Z_to_bv 64 (start - 1)) <> None) by (apply DEF; lia).
    destruct (byte_of_def M (start - 3) D3) as (h3 & Hh3 & E3).
    destruct (rdn2_of_def M (start - 2) ltac:(unfold HEAPLO in *; lia) ltac:(ceil; lia) D2
               ltac:(replace (start - 2 + 1) with (start - 1) by lia; exact D1)) as (o16 & Ho16 & E2).
    exists h3, o16.
    assert (SI : g_stride st g * idx <= g_stride st g * g_lastidx st g) by (apply Z.mul_le_mono_nonneg_l; lia).
    assert (SC' : g_stride st g * (g_lastidx st g + 1) <= 2 ^ 20) by (unfold g_cnt in Q20; lia).
    constructor.
    - unfold g_stride. reflexivity.
    - subst start. unfold slot_start, UNIT. exact Ess.
    - reflexivity.
    - ceil; unfold HEAPLO in *. lia.
    - lia.
    - exact WR.
    - lia.
    - lia.
    - intros _. unfold g_sc in Hsc. exact Hsc.
    - lia.
    - (* [comment removed for export] *)
      destruct (Z.lt_ge_cases (g_stride st g) 4096) as [A|A]; nia.
    - ceil. lia.
    - (* [comment removed for export] *)
      destruct (meta_apart_span g Hg) as [A|A]; [left | right]; lia.
    - exact Hh3.
    - exact Ho16.
    - exact (rm_mem M g _ RM).
    - exact (rm_W M g _ RM).
    - (* [comment removed for export] *)
      pose proof (rg_hdr0 st M g (rp_groups st M HREP g Hg) idx ltac:(unfold g_cnt; lia) ltac:(left; unfold g_cnt; lia)) as Z4.
      exact Z4.
    - exact E3.
    - intros _. exact E2.
    - eapply (store_ok_defined M (g_mem st g) (gspan st g)); [exact DEF | lia | rewrite Z2Nat.id by lia; lia | unfold HEAPLO in *; lia | ceil; lia].
    - intros j Hj. exact (rc_tab_sc st M (rp_statics st M HREP) (SCT + j) ltac:(unfold SCT, A_TAB_SC, A_TAB_MED; lia)).
  Qed.
End Efh.
End MhEfh.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.glaze.binary_reflection.images Require Import Plain.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaN OSSVerify.Proofs.glaze.binary_reflection.lib.MhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.MhMmapK OSSVerify.Proofs.glaze.binary_reflection.lib.MhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.MhNtf OSSVerify.Proofs.glaze.binary_reflection.lib.MhNtf2 OSSVerify.Proofs.glaze.binary_reflection.lib.MhCount OSSVerify.Proofs.glaze.binary_reflection.lib.MhBudget OSSVerify.Proofs.glaze.binary_reflection.lib.MhMallocH2 OSSVerify.Proofs.glaze.binary_reflection.lib.MhTake OSSVerify.Proofs.glaze.binary_reflection.lib.MhActivate OSSVerify.Proofs.glaze.binary_reflection.lib.MhPolicy OSSVerify.Proofs.glaze.binary_reflection.lib.MhAidx OSSVerify.Proofs.glaze.binary_reflection.lib.MhEnframeBase OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys OSSVerify.Proofs.glaze.binary_reflection.lib.MhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaS. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhExt OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhList OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaN.MhNtfLib OSSVerify.Proofs.glaze.binary_reflection.lib.MhNest2.MhNest OSSVerify.Proofs.glaze.binary_reflection.lib.MhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhCover OSSVerify.Proofs.glaze.binary_reflection.lib.MhMmapK.MhAcct OSSVerify.Proofs.glaze.binary_reflection.lib.MhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.MhNtf OSSVerify.Proofs.glaze.binary_reflection.lib.MhNtf2 OSSVerify.Proofs.glaze.binary_reflection.lib.MhCount.MhCountSpec OSSVerify.Proofs.glaze.binary_reflection.lib.MhBudget OSSVerify.Proofs.glaze.binary_reflection.lib.MhMallocH2.MhCtz OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac.MhBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhTake OSSVerify.Proofs.glaze.binary_reflection.lib.MhActivate OSSVerify.Proofs.glaze.binary_reflection.lib.MhPolicy OSSVerify.Proofs.glaze.binary_reflection.lib.MhAidx OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.MhEnframeBase MhEfh OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhKX OSSVerify.Proofs.glaze.binary_reflection.lib.MhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaS.MhMSpec3 MhASpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhMallocH2.MhASlotW1 OSSVerify.Proofs.glaze.binary_reflection.lib.MhMallocH2.MhASlotW2 OSSVerify.Proofs.glaze.binary_reflection.lib.MhMallocH2.MhASlotW3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AS_SAVED : list reg := [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%bv.
Definition BIG : list reg := AS_CLOB ++ AS_SAVED.

Lemma keeps_big : forall (r0 r1 r2 : bvmap 5 word) cl,
  keeps_but BIG r0 r1 -> keeps_but cl r1 r2 -> forallb (fun r => existsb (fun x => bv_eqb x r) BIG) cl = true -> keeps_but BIG r0 r2.
Proof.
  intros r0 r1 r2 cl K1 K2 Hcl. eapply keeps_but_trans; [exact K1|].
  eapply keeps_but_mono; [exact K2|]. intros r Hr.
  pose proof (proj1 (forallb_forall _ _) Hcl r Hr) as X. cbn beta in X. apply in_regs_dec in X. exact X.
Qed.

Lemma keeps_final_as : forall (regs r' : bvmap 5 word),
  keeps_but BIG regs r' ->
  getr r' 1 = getr regs 1 -> getr r' 2 = getr regs 2 -> getr r' 8 = getr regs 8 -> getr r' 9 = getr regs 9 ->
  getr r' 18 = getr regs 18 -> getr r' 19 = getr regs 19 -> getr r' 20 = getr regs 20 -> getr r' 21 = getr regs 21 ->
  getr r' 22 = getr regs 22 -> getr r' 23 = getr regs 23 -> getr r' 24 = getr regs 24 -> getr r' 25 = getr regs 25 ->
  keeps_but AS_CLOB regs r'.
Proof.
  intros regs r' K E1 E2 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 r Hr.
  destruct (in_dec (fun x y : reg => bv_eq_dec _ x y) r BIG) as [I|NI]; [|exact (K r NI)].
  unfold BIG in I. apply in_app_or in I. destruct I as [I|I]; [exfalso; exact (Hr I)|].
  destruct I as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]; assumption.
Qed.

(* [comment removed for export] *)
Lemma keeps_cs_big : forall (r0 r1 r2 : bvmap 5 word), keeps_but BIG r0 r1 -> keeps_cs r1 r2 -> keeps_but BIG r0 r2.
Proof.
  intros r0 r1 r2 K KC r Hr. rewrite <- (K r Hr).
  destruct (bv_eq_dec _ r 0%bv) as [->|NZ]; [reflexivity|].
  apply KC.
  (* [comment removed for export] *)
  assert (E : exists k, (k < 32)%nat /\ r = Z_to_bv 5 (Z.of_nat k)).
  { exists (Z.to_nat (bv_unsigned r)). pose proof (bv_unsigned_in_range 5 r) as R. change (bv_modulus 5) with 32 in R.
    split; [lia|]. apply bv_eq. rewrite Z_to_bv_unsigned, Z2Nat.id by lia. symmetry. apply bv_wrap_small. change (bv_modulus 5) with 32. lia. }
  destruct E as (k & Hk & ->).
  enum_nat k 32%nat ltac:(first [exfalso; apply Hr; apply in_regs_dec; reflexivity | apply in_regs_dec; reflexivity | exfalso; apply NZ; apply bv_eq; reflexivity]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Generic.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Lemma rdn_agreeZ : forall (Ma Mb : mem) a k, 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
    (forall y, a <= y < a + Z.of_nat k -> Mb (Z_to_bv 64 y) = Ma (Z_to_bv 64 y)) ->
    rdn RSEGS Mb (Z_to_bv 64 a) k = rdn RSEGS Ma (Z_to_bv 64 a) k.
  Proof using.
    intros Ma Mb a k. revert a. induction k as [|k IH]; intros a Ha Hk AG; [reflexivity|].
    cbn [rdn]. rewrite (AG a) by lia.
    replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1))
      by (apply bv_eq; rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod; change (bv_unsigned (1 : word)) with 1%Z;
          rewrite (Z.mod_small a) by lia; reflexivity).
    rewrite (IH (a + 1)); [reflexivity | lia | lia |]. intros y Hy. apply AG. lia.
  Qed.

  Lemma cell_hit : forall (Mx : mem) a n v, 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
    cell (wbytes Mx (Z_to_bv 64 a) (word_to_le_bytes n (Z_to_bv 64 v))) a n v.
  Proof using.
    intros Mx a n v Ha Hn. unfold cell. pose proof (rdn_wbytes_hit RSEGS (word_to_le_bytes n (Z_to_bv 64 v)) Mx (Z_to_bv 64 a)) as RH.
    rewrite !length_N_to_le_bytes in RH. apply RH. rewrite u_Z2bv by lia. lia.
  Qed.

  Lemma cell_hit1 : forall (Mx : mem) a v, 0 <= a -> a + 1 < 2 ^ 64 ->
    rdn RSEGS (wbytes Mx (Z_to_bv 64 a) [Z_to_bv 8 v]) (Z_to_bv 64 a) 1%nat = Some [Z_to_bv 8 v].
  Proof using.
    intros Mx a v Ha H1. pose proof (rdn_wbytes_hit RSEGS [Z_to_bv 8 v] Mx (Z_to_bv 64 a)) as RH. apply RH. cbn. rewrite u_Z2bv by lia. lia.
  Qed.

  Lemma byte_hit : forall (Mx : mem) (a : word) (v : byte), wbytes Mx a [v] a = Some v.
  Proof using. intros Mx a v. cbn [wbytes]. rewrite bv_eqb_refl. reflexivity. Qed.

  Lemma cell_peel : forall (Mx : mem) a n v b bs, cell Mx a n v ->
    a + Z.of_nat n <= b \/ b + Z.of_nat (length bs) <= a ->
    0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> 0 <= b -> b + Z.of_nat (length bs) <= 2 ^ 64 ->
    cell (wbytes Mx (Z_to_bv 64 b) bs) a n v.
  Proof using.
    intros Mx a n v b bs C D Ha Han Hb Hbn. unfold cell in *.
    destruct n as [|n']; [cbn; cbn in C; exact C|].
    destruct bs as [|b0 bs']; [cbn [wbytes]; exact C|].
    rewrite rdn_wbytes_out; [exact C | rewrite !u_Z2bv by (cbn [length] in *; lia); exact D | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by (cbn [length] in *; lia); lia].
  Qed.

  Lemma lo_bits_nz : forall fr n k, 0 <= k < n -> Z.testbit fr k = true -> lo_bits fr n <> 0.
  Proof using.
    intros fr n k Hk Hb E. assert (T : Z.testbit (lo_bits fr n) k = true) by (unfold lo_bits; rewrite Z.mod_pow2_bits_low by lia; exact Hb).
    rewrite E, Z.bits_0 in T. discriminate T.
  Qed.
End Generic.

Lemma zremove_head : forall g rest, ~ In g rest -> zremove g (g :: rest) = rest.
Proof.
  intros g rest NI. change (zremove g (g :: rest)) with (if negb (g =? g) then g :: zremove g rest else zremove g rest).
  rewrite Z.eqb_refl. cbn [negb]. apply zremove_notin. exact NI.
Qed.

(* [comment removed for export] *)
Ltac peel := apply cell_peel; [ | wd_lenlit; rewrite ?length_N_to_le_bytes; cbn [length]; lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | wd_lenlit; rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
Ltac hit := apply cell_hit; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
Ltac cellw := first [hit | (peel; cellw)].
Ltac inCS := cbn; repeat (first [left; reflexivity | right]).
(* [comment removed for export] *)
Ltac wdiff2 NE Mbase a :=
  repeat match type of NE with wbytes ?Mb (Z_to_bv 64 ?b) _ _ <> _ =>
    destruct (decide (Mb (Z_to_bv 64 a) = Mbase (Z_to_bv 64 a))) as [?E2|?NE2];
    [ (rewrite <- E2 in NE || idtac); apply wbytes_diff_g in NE;
      [ rewrite length_N_to_le_bytes in NE; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in NE; lia | lia
      | rewrite length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia | assumption ]
    | clear NE; rename NE2 into NE ] end;
  exfalso; exact (NE eq_refl).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ASA.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (M : mem) (mdl : Model)
            (regs : bvmap 5 word) (rom : word -> option byte) (sp sc req : Z) (Q : config -> Prop) (d : nat).
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  Hypothesis HLG : LEDGER st (m_vmmaps mdl).
  Hypothesis NJ : nojunk st.
  Hypothesis Hh : m_halted mdl = None.
  Hypothesis Hlz : m_vm_lazy mdl = [].
  Hypothesis Hmat : m_vm_materialized mdl = [].
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hd : dle (dbound (16 * size_class sc)) d.
  Hypothesis Hlimbo : zlen (s_limbo st) + Z.of_nat d + 1 <= 8.
  Hypothesis Hreq : 0 <= req /\ req + 4 <= 16 * size_class sc.
  Hypothesis HBUD : PHI L + MBASE <= vm_limit (m_vmmaps mdl).
  Hypothesis R10 : getr regs 10 = Z_to_bv 64 sc.
  Hypothesis R11 : getr regs 11 = Z_to_bv 64 req.
  Hypothesis R2 : getr regs 2 = Z_to_bv 64 sp.
  Hypothesis Rra : ret_ok (getr regs 1).
  Hypothesis Hsp : CEIL + ASSTK d <= sp /\ sp < 2 ^ 64.
  Hypothesis DEF : defined M (sp - ASSTK d) sp.
  Hypothesis HQ : forall c', as_ok st L sc req d sp regs M mdl rom c' -> Q c'.
  Hypothesis IHd : forall d', (d' < d)%nat -> AS_SPEC3 d'.

  Definition can : Z := s_canary st.
  (* [comment removed for export] *)
  Definition spc : Z := sp - ASSTK d + MSTK.
  Lemma spc_ok : CEIL + MSTK <= spc. Proof using Hsp. unfold spc. lia. Qed.

  Lemma scl_rng : 1 <= size_class sc <= 8191. Proof using Hsc d. pose proof (size_class_pos sc Hsc). lia. Qed.
  Lemma stk272 : 288 <= ASSTK d. Proof using. apply ASSTK_ge. Qed.

  (* [comment removed for export] *)
  Definition stk_ok (Mc : mem) : Prop :=
    rdn RSEGS Mc (Z_to_bv 64 (sp - 96)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 can)) /\
    rdn RSEGS Mc (Z_to_bv 64 (sp - 8)) 8%nat = Some (word_to_le_bytes 8 (getr regs 1)) /\
    rdn RSEGS Mc (Z_to_bv 64 (sp - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs 8)) /\
    rdn RSEGS Mc (Z_to_bv 64 (sp - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs 9)) /\
    rdn RSEGS Mc (Z_to_bv 64 (sp - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs 18)) /\
    rdn RSEGS Mc (Z_to_bv 64 (sp - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs 19)) /\
    rdn RSEGS Mc (Z_to_bv 64 (sp - 48)) 8%nat = Some (word_to_le_bytes 8 (getr regs 20)) /\
    rdn RSEGS Mc (Z_to_bv 64 (sp - 56)) 8%nat = Some (word_to_le_bytes 8 (getr regs 21)) /\
    rdn RSEGS Mc (Z_to_bv 64 (sp - 64)) 8%nat = Some (word_to_le_bytes 8 (getr regs 22)) /\
    rdn RSEGS Mc (Z_to_bv 64 (sp - 72)) 8%nat = Some (word_to_le_bytes 8 (getr regs 23)) /\
    rdn RSEGS Mc (Z_to_bv 64 (sp - 80)) 8%nat = Some (word_to_le_bytes 8 (getr regs 24)) /\
    rdn RSEGS Mc (Z_to_bv 64 (sp - 88)) 8%nat = Some (word_to_le_bytes 8 (getr regs 25)).

  (* [comment removed for export] *)
  Definition WOK (a : Z) : Prop :=
    (sp - ASSTK d <= a < sp - 144) \/ (HEAPLO <= a < CEIL /\ (a < IMG_LO \/ IMG_HI <= a) /\ ~ app_of L a) \/ (CTX <= a < CTX_END) \/ (A_ERRNO <= a < A_ERRNO + 4).

  (* [comment removed for export] *)
  Record pt (s1 : mst) (Mc : mem) (mdl1 : Model) (r : bvmap 5 word) : Prop := PT {
    p_wf : WF s1 L; p_rep : REP s1 Mc; p_lg : LEDGER s1 (m_vmmaps mdl1);
    p_h : m_halted mdl1 = None; p_lz : m_vm_lazy mdl1 = []; p_mat : m_vm_materialized mdl1 = [];
    p_fs : m_fs mdl1 = m_fs mdl; p_fds : m_fds mdl1 = m_fds mdl; p_lim : vm_limit (m_vmmaps mdl1) = vm_limit (m_vmmaps mdl);
    p_can : s_canary s1 = s_canary st; p_err : s_errno s1 = s_errno st \/ s_errno s1 = 12;
    p_below : forall k, 0 <= k < sc -> s_alist s1 k = s_alist st k;
    p_lmeta : forall x, In x (s_limbo st) -> s_meta s1 x = s_meta st x;
    p_mU : forall x, metaU st x -> metaU s1 x;
    p_fr : forall a, 0 <= a < 2 ^ 64 -> Mc (Z_to_bv 64 a) <> M (Z_to_bv 64 a) ->
             (sp - ASSTK d <= a < sp) \/ (HEAPLO <= a < CEIL /\ (a < IMG_LO \/ IMG_HI <= a) /\ ~ app_of L a) \/ (CTX <= a < CTX_END) \/ (A_ERRNO <= a < A_ERRNO + 4);
    p_def : defined Mc (sp - ASSTK d) sp; p_stk : stk_ok Mc;
    p_r2 : getr r 2 = Z_to_bv 64 (sp - 144); p_r8 : getr r 8 = Z_to_bv 64 sc;
    p_r20 : getr r 20 = Z_to_bv 64 A_CANARY; p_r21 : getr r 21 = Z_to_bv 64 (ctx_active sc); p_r22 : getr r 22 = Z_to_bv 64 MLOCK; p_r23 : getr r 23 = Z_to_bv 64 (MLOCK + 8 * sc);
    p_K : keeps_but BIG regs r }.

  (* [comment removed for export] *)
  Record ptE (s1 : mst) (Mc : mem) (mdl1 : Model) (r : bvmap 5 word) : Prop := PTE {
    q_wf : WF s1 L; q_rep : REP s1 Mc; q_lg : LEDGER s1 (m_vmmaps mdl1);
    q_h : m_halted mdl1 = None; q_lz : m_vm_lazy mdl1 = []; q_mat : m_vm_materialized mdl1 = [];
    q_fs : m_fs mdl1 = m_fs mdl; q_fds : m_fds mdl1 = m_fds mdl; q_lim : vm_limit (m_vmmaps mdl1) = vm_limit (m_vmmaps mdl);
    q_can : s_canary s1 = s_canary st; q_err : s_errno s1 = s_errno st \/ s_errno s1 = 12;
    q_below : forall k, 0 <= k < sc -> s_alist s1 k = s_alist st k;
    q_lmeta : forall x, In x (s_limbo st) -> s_meta s1 x = s_meta st x;
    q_mU : forall x, metaU st x -> metaU s1 x;
    q_fr : forall a, 0 <= a < 2 ^ 64 -> Mc (Z_to_bv 64 a) <> M (Z_to_bv 64 a) ->
             (sp - ASSTK d <= a < sp) \/ (HEAPLO <= a < CEIL /\ (a < IMG_LO \/ IMG_HI <= a) /\ ~ app_of L a) \/ (CTX <= a < CTX_END) \/ (A_ERRNO <= a < A_ERRNO + 4);
    q_def : defined Mc (sp - ASSTK d) sp; q_stk : stk_ok Mc;
    q_r2 : getr r 2 = Z_to_bv 64 (sp - 144); q_r20 : getr r 20 = Z_to_bv 64 A_CANARY; q_K : keeps_but BIG regs r }.

  Lemma pt_ptE : forall s1 Mc mdl1 r, pt s1 Mc mdl1 r -> ptE s1 Mc mdl1 r.
  Proof using. intros s1 Mc mdl1 r P. destruct P; constructor; assumption. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)





  Lemma stk_transfer : forall (Ma Mb : mem),
    (forall y, sp - 96 <= y < sp -> Mb (Z_to_bv 64 y) = Ma (Z_to_bv 64 y)) -> stk_ok Ma -> stk_ok Mb.
  Proof using Hsp Hreq Hsc d req sc RN.
    intros Ma Mb AG S. unfold stk_ok in *. ceil. pose proof stk272.
    repeat match goal with |- _ /\ _ => split end;
    match goal with |- rdn RSEGS Mb (Z_to_bv 64 ?a) ?k = _ =>
      rewrite (rdn_agreeZ Ma Mb a k ltac:(lia) ltac:(cbn; lia)) by (intros y Hy; apply AG; cbn in Hy; lia); tauto end.
  Qed.

  Lemma WOK_not_frame : forall a, WOK a -> ~ (sp - 144 <= a < sp).
  Proof using Hsp. intros a [A|[A|[A|A]]] B; ceil; unfold A_ERRNO, TPV, CTX_END, CTX, HEAPLO in *; pose proof stk272; lia. Qed.

  (* [comment removed for export] *)
  Lemma pt_step : forall s1 Mc mdl1 r s2 Mc' r',
    pt s1 Mc mdl1 r ->
    WF s2 L -> REP s2 Mc' -> s_regions s2 = s_regions s1 -> s_brk s2 = s_brk s1 ->
    s_canary s2 = s_canary s1 -> s_errno s2 = s_errno s1 ->
    (forall k, 0 <= k < sc -> s_alist s2 k = s_alist s1 k) -> (forall x, In x (s_limbo st) -> s_meta s2 x = s_meta s1 x) ->
    (forall x, metaU s1 x -> metaU s2 x) ->
    mem_grows Mc Mc' -> (forall a, 0 <= a < 2 ^ 64 -> Mc' (Z_to_bv 64 a) <> Mc (Z_to_bv 64 a) -> WOK a) ->
    getr r' 2 = getr r 2 -> getr r' 8 = getr r 8 -> getr r' 20 = getr r 20 -> getr r' 21 = getr r 21 ->
    getr r' 22 = getr r 22 -> getr r' 23 = getr r 23 -> keeps_but BIG regs r' ->
    pt s2 Mc' mdl1 r'.
  Proof using Hsp Hreq Hsc req.
    intros s1 Mc mdl1 r s2 Mc' r' P W2 R2' ER EB EC EE HBl HLm HmU G WW E2 E8 E20 E21 E22 E23 K'.
    destruct P as [W1 RP1 LG1 Hh1 Hlz1 Hmat1 Hfs1 Hfds1 Hlim1 Hcan1 Herr1 BL1 LM1 MU1 FR1 DF1 SK1 Q2 Q8 Q20 Q21 Q22 Q23 KB].
    assert (BL2 : forall k, 0 <= k < sc -> s_alist s2 k = s_alist st k) by (intros k Hk; rewrite (HBl k Hk); exact (BL1 k Hk)).
    assert (LM2 : forall x, In x (s_limbo st) -> s_meta s2 x = s_meta st x) by (intros x Hx; rewrite (HLm x Hx); exact (LM1 x Hx)).
    assert (MU2 : forall x, metaU st x -> metaU s2 x) by (intros x Hx; exact (HmU x (MU1 x Hx))).
    constructor; try assumption; try congruence; try (rewrite EE; exact Herr1); try (destruct EE as [EE'|EE']; [rewrite EE'; exact Herr1 | right; exact EE']).
    - apply (LEDGER_same s1); [exact ER | exact EB | exact LG1].
    - intros a Ha NE. destruct (decide (Mc' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a))) as [E|NE2].
      + apply FR1; [exact Ha | congruence].
      + destruct (WW a Ha NE2) as [A|[A|[A|A]]]; [left; lia | right; left; exact A | right; right; left; exact A | right; right; right; exact A].
    - eapply defined_grows; [exact G | exact DF1].
    - apply (stk_transfer Mc Mc'); [|exact SK1]. intros y Hy.
      destruct (decide (Mc' (Z_to_bv 64 y) = Mc (Z_to_bv 64 y))) as [E|NE]; [exact E|]. exfalso.
      apply (WOK_not_frame y (WW y ltac:(ceil; pose proof stk272; lia) NE)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pt_step2 : forall s1 Mc mdl1 r s2 Mc' mdl2 r',
    pt s1 Mc mdl1 r ->
    WF s2 L -> REP s2 Mc' -> LEDGER s2 (m_vmmaps mdl2) ->
    m_halted mdl2 = None -> m_vm_lazy mdl2 = [] -> m_vm_materialized mdl2 = [] ->
    m_fs mdl2 = m_fs mdl1 -> m_fds mdl2 = m_fds mdl1 -> vm_limit (m_vmmaps mdl2) = vm_limit (m_vmmaps mdl1) ->
    s_canary s2 = s_canary s1 -> (s_errno s2 = s_errno s1 \/ s_errno s2 = 12) ->
    (forall k, 0 <= k < sc -> s_alist s2 k = s_alist s1 k) -> (forall x, In x (s_limbo st) -> s_meta s2 x = s_meta s1 x) ->
    (forall x, metaU s1 x -> metaU s2 x) ->
    defined Mc' (sp - ASSTK d) sp -> (forall a, 0 <= a < 2 ^ 64 -> Mc' (Z_to_bv 64 a) <> Mc (Z_to_bv 64 a) -> WOK a) ->
    getr r' 2 = getr r 2 -> getr r' 8 = getr r 8 -> getr r' 20 = getr r 20 -> getr r' 21 = getr r 21 ->
    getr r' 22 = getr r 22 -> getr r' 23 = getr r 23 -> keeps_but BIG regs r' ->
    pt s2 Mc' mdl2 r'.
  Proof using Hsp Hreq Hsc req.
    intros s1 Mc mdl1 r s2 Mc' mdl2 r' P W2 R2' LG2 Hh2 Hlz2 Hmat2 Hfs2 Hfds2 Hlim2 EC EE HBl HLm HmU DF2 WW E2 E8 E20 E21 E22 E23 K'.
    destruct P as [W1 RP1 LG1 Hh1 Hlz1 Hmat1 Hfs1 Hfds1 Hlim1 Hcan1 Herr1 BL1 LM1 MU1 FR1 DF1 SK1 Q2 Q8 Q20 Q21 Q22 Q23 KB].
    assert (BL2 : forall k, 0 <= k < sc -> s_alist s2 k = s_alist st k) by (intros k Hk; rewrite (HBl k Hk); exact (BL1 k Hk)).
    assert (LM2 : forall x, In x (s_limbo st) -> s_meta s2 x = s_meta st x) by (intros x Hx; rewrite (HLm x Hx); exact (LM1 x Hx)).
    assert (MU2 : forall x, metaU st x -> metaU s2 x) by (intros x Hx; exact (HmU x (MU1 x Hx))).
    constructor; try assumption; try congruence; try (rewrite EE; exact Herr1); try (destruct EE as [EE'|EE']; [rewrite EE'; exact Herr1 | right; exact EE']).
    - intros a Ha NE. destruct (decide (Mc' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a))) as [E|NE2].
      + apply FR1; [exact Ha | congruence].
      + destruct (WW a Ha NE2) as [A|[A|[A|A]]]; [left; lia | right; left; exact A | right; right; left; exact A | right; right; right; exact A].
    - apply (stk_transfer Mc Mc'); [|exact SK1]. intros y Hy.
      destruct (decide (Mc' (Z_to_bv 64 y) = Mc (Z_to_bv 64 y))) as [E|NE]; [exact E|]. exfalso.
      apply (WOK_not_frame y (WW y ltac:(ceil; pose proof stk272; lia) NE)). lia.
  Qed.

  (* [comment removed for export] *)
  Definition gbr (s2 : mst) (M2 : mem) (mdl2 : Model) (r : bvmap 5 word) (m cnt : Z) : Prop :=
    pt s2 M2 mdl2 r /\ nojunk s2 /\ s_limbo s2 = m :: s_limbo st /\ s_alist s2 sc = [] /\
    metaU s2 m /\ s_meta s2 m = meta_zero /\ ~ In m (s_limbo st) /\
    getr r 9 = Z_to_bv 64 m /\ getr r 10 = Z_to_bv 64 (c_usage (s_ctx s2) sc) /\ getr r 11 = Z_to_bv 64 4096 /\ getr r 18 = Z_to_bv 64 req /\
    getr r 19 = Z_to_bv 64 cnt /\ getr r 24 = Z_to_bv 64 (16 * size_class sc) /\ getr r 25 = Z_to_bv 64 A_TAB_SC /\
    getr r 14 = Z_to_bv 64 (16 * size_class sc * cnt) /\ getr r 12 = Z_to_bv 64 (16 * size_class sc + 16) /\
    1 <= cnt <= 32 /\ 16 * size_class sc * cnt < 2 ^ 20 /\ (sc = 7 -> cnt <= 31) /\ (cnt = 1 -> 2048 < 16 * size_class sc + 16).

  (* [comment removed for export] *)
  Lemma pt_regs : forall s1 Mc mdl1 r r',
    pt s1 Mc mdl1 r ->
    getr r' 2 = getr r 2 -> getr r' 8 = getr r 8 -> getr r' 20 = getr r 20 -> getr r' 21 = getr r 21 ->
    getr r' 22 = getr r 22 -> getr r' 23 = getr r 23 -> keeps_but BIG regs r' ->
    pt s1 Mc mdl1 r'.
  Proof using.
    intros s1 Mc mdl1 r r' P E2 E8 E20 E21 E22 E23 K'. destruct P. constructor; try assumption; congruence.
  Qed.

  (* [comment removed for export] *)
  Lemma ptE_step : forall s1 Mc mdl1 r s2 Mc' r',
    pt s1 Mc mdl1 r ->
    WF s2 L -> REP s2 Mc' -> s_regions s2 = s_regions s1 -> s_brk s2 = s_brk s1 ->
    s_canary s2 = s_canary s1 -> s_errno s2 = s_errno s1 ->
    (forall k, 0 <= k < sc -> s_alist s2 k = s_alist s1 k) -> (forall x, In x (s_limbo st) -> s_meta s2 x = s_meta s1 x) ->
    (forall x, metaU s1 x -> metaU s2 x) ->
    mem_grows Mc Mc' -> (forall a, 0 <= a < 2 ^ 64 -> Mc' (Z_to_bv 64 a) <> Mc (Z_to_bv 64 a) -> WOK a) ->
    getr r' 2 = getr r 2 -> getr r' 20 = getr r 20 -> keeps_but BIG regs r' ->
    ptE s2 Mc' mdl1 r'.
  Proof using Hsp Hreq Hsc req.
    intros s1 Mc mdl1 r s2 Mc' r' P W2 R2' ER EB EC EE HBl HLm HmU G WW E2 E20 K'.
    destruct P as [W1 RP1 LG1 Hh1 Hlz1 Hmat1 Hfs1 Hfds1 Hlim1 Hcan1 Herr1 BL1 LM1 MU1 FR1 DF1 SK1 Q2 Q8 Q20 Q21 Q22 Q23 KB].
    assert (BL2 : forall k, 0 <= k < sc -> s_alist s2 k = s_alist st k) by (intros k Hk; rewrite (HBl k Hk); exact (BL1 k Hk)).
    assert (LM2 : forall x, In x (s_limbo st) -> s_meta s2 x = s_meta st x) by (intros x Hx; rewrite (HLm x Hx); exact (LM1 x Hx)).
    assert (MU2 : forall x, metaU st x -> metaU s2 x) by (intros x Hx; exact (HmU x (MU1 x Hx))).
    constructor; try assumption; try congruence; try (rewrite EE; exact Herr1); try (destruct EE as [EE'|EE']; [rewrite EE'; exact Herr1 | right; exact EE']).
    - apply (LEDGER_same s1); [exact ER | exact EB | exact LG1].
    - intros a Ha NE. destruct (decide (Mc' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a))) as [E|NE2].
      + apply FR1; [exact Ha | congruence].
      + destruct (WW a Ha NE2) as [A|[A|[A|A]]]; [left; lia | right; left; exact A | right; right; left; exact A | right; right; right; exact A].
    - eapply defined_grows; [exact G | exact DF1].
    - apply (stk_transfer Mc Mc'); [|exact SK1]. intros y Hy.
      destruct (decide (Mc' (Z_to_bv 64 y) = Mc (Z_to_bv 64 y))) as [E|NE]; [exact E|]. exfalso.
      apply (WOK_not_frame y (WW y ltac:(ceil; pose proof stk272; lia) NE)). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma app_appb : forall s1 a, WF s1 L -> app_of L a -> appb s1 a.
  Proof using d.
    intros s1 a W (b & k & Hin & Ha). destruct (wL_in s1 L (WF_live s1 L W) b k Hin) as (x & j & o2 & rr2 & Hx & Hj & Hs).
    exists x, j, b, k, o2, rr2. repeat split; try assumption; lia.
  Qed.

  Lemma meta_WOK : forall s1 x a, WF s1 L -> metaU s1 x -> x <= a < x + 40 -> WOK a.
  Proof using.
    intros s1 x a W U Ha. right; left.
    destruct (metaU_area s1 L W x U) as (ar0 & k0 & Har0 & _ & _ & _ & Hlo & Hhi & Q1 & Q2 & _).
    split; [lia|]. split; [lia|]. intros AP.
    apply (ge_app_area s1 (WF_geom s1 L W) a (app_appb s1 a W AP)). exists ar0. split; [exact Har0 | lia].
  Qed.

  Lemma gcell_WOK : forall s1 x a, WF s1 L -> is_group s1 x -> gcell s1 x a -> WOK a.
  Proof using.
    intros s1 x a W Hx G. right; left. pose proof (gcell_in_span s1 L W x a Hx G). destruct (group_range s1 L W x Hx).
    split; [lia|]. split; [lia|]. intros AP. exact (ge_app_cell s1 (WF_geom s1 L W) x a Hx G (app_appb s1 a W AP)).
  Qed.

  Lemma garbage_WOK : forall s1 x k a, WF s1 L -> is_group s1 x -> garbage s1 x k a -> WOK a.
  Proof using.
    intros s1 x k a W Hx G. right; left. pose proof (garbage_in_span s1 L W x k a Hx G). destruct (group_range s1 L W x Hx).
    split; [lia|]. split; [lia|]. intros AP. exact (ge_garb_app s1 (WF_geom s1 L W) x k a Hx G (app_appb s1 a W AP)).
  Qed.

  Lemma ctx_WOK : forall a, CTX <= a < CTX_END -> WOK a.
  Proof using. intros a Ha. right; right; left. exact Ha. Qed.

  Lemma active_WOK : forall j a, 0 <= j < 48 -> ctx_active j <= a < ctx_active j + 8 -> WOK a.
  Proof using. intros j a Hj Ha. apply ctx_WOK. unfold ctx_active, CTX_END in *. lia. Qed.

  (* [comment removed for export] *)
  Lemma nongroup_nonapp : forall s1 r a, WF s1 L -> In r (s_regions s1) -> (forall x, rg_kind r <> RGroup x) ->
    rg_base r <= a < rg_base r + rg_len r -> HEAPLO <= a < CEIL /\ (a < IMG_LO \/ IMG_HI <= a) /\ ~ app_of L a.
  Proof using d.
    intros s1 r a W Hr NK Ha. destruct (wr_rng s1 (WF_regions s1 L W) r Hr) as (Q1 & Q2 & _). split; [lia|]. split; [lia|].
    intros AP. destruct (appb_in_span s1 L W a (app_appb s1 a W AP)) as (x & Hx & Ra).
    destruct (group_in_top s1 L W x Hx) as (t & Ht & Kt & T1 & T2 & Hin). unfold g_map_end in T2.
    assert (NE : r <> RG (g_mem s1 t) (4096 * g_maplen s1 t) (RGroup t)) by (intros ->; exact (NK t eq_refl)).
    destruct (wr_disj s1 (WF_regions s1 L W) _ _ Hr Hin NE); cbn [rg_base rg_len] in *; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fresh_nonapp : forall s1 b len a, WF s1 L ->
    (forall r, In r (s_regions s1) -> rg_base r + rg_len r <= b \/ b + len <= rg_base r) ->
    b <= a < b + len -> ~ app_of L a.
  Proof using d.
    intros s1 b len a W AP Ha X. destruct (appb_in_span s1 L W a (app_appb s1 a W X)) as (x & Hx & Ra).
    destruct (group_in_top s1 L W x Hx) as (t & Ht & Kt & T1 & T2 & Hin). unfold g_map_end in T2.
    destruct (AP _ Hin); cbn [rg_base rg_len] in *; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma budget : forall s1 mdl1, WF s1 L -> nojunk s1 -> zlen (s_limbo s1) <= 8 ->
    vm_limit (m_vmmaps mdl1) = vm_limit (m_vmmaps mdl) ->
    (s_flist s1 = [] -> c_avail_cnt (s_ctx s1) = 0 -> Z.of_nat (length (s_areas s1)) + 1 <= AREAMAX) /\
    Z.of_nat (length (s_regions s1)) <= 240 /\
    RSUM (s_regions s1) + 2 ^ 27 <= vm_limit (m_vmmaps mdl1).
  Proof using HBUD d.
    intros s1 mdl1 W NJ1 Hl EL.
    assert (J : junk_in s1 []) by (intros x k o Hx Hk E; exfalso; exact (NJ1 x k o Hx Hk E)).
    unfold zlen in Hl.
    split; [exact (areas_room s1 L [] W J ltac:(cbn; lia) Hl)|].
    split; [exact (regions_room s1 L [] W J ltac:(cbn; lia))|].
    pose proof (rsum_MBASE s1 L [] W J ltac:(cbn; lia) Hl ltac:(intros m off Hm _; exact (NJ1 m 0 off Hm ltac:(pose proof (glast_rng s1 m); lia)))) as B.
    rewrite EL. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition M1 : mem := as_frame M sp can (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20)
                                  (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25).

  Lemma SOK144 : store_ok RSEGS M (Z_to_bv 64 (sp - 144)) 144%nat = true.
  Proof using DEF Hsp d RN. ceil. pose proof stk272. eapply store_ok_defined; [exact DEF | lia | cbn; lia | lia | lia]. Qed.

  Lemma M1_writes : forall a, 0 <= a < 2 ^ 64 -> M1 (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> sp - 96 <= a < sp.
  Proof using Hsp d RN. intros a Ha NE. ceil; unfold M1, as_frame in *. pose proof stk272. wdiff NE M a. Qed.
  Lemma M1_grows : mem_grows M M1.
  Proof using. unfold M1, as_frame. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma M1_REP : REP st M1.
  Proof using Hsp HREP HWF d L RN.
    apply (REP_frame st L M HWF HREP M1 M1_grows). intros a Hr NE. left. pose proof (M1_writes a Hr NE). ceil. pose proof stk272. lia.
  Qed.
  Lemma M1_stk : stk_ok M1.
  Proof using Hsp d RN. ceil; unfold stk_ok, M1, as_frame in *. pose proof stk272. repeat match goal with |- _ /\ _ => split end; rdn_solve. Qed.

  Lemma as_head :
    (forall r1, getr r1 2 = Z_to_bv 64 (sp - 144) -> getr r1 8 = Z_to_bv 64 sc -> getr r1 18 = Z_to_bv 64 req ->
                getr r1 20 = Z_to_bv 64 A_CANARY -> getr r1 22 = Z_to_bv 64 MLOCK -> getr r1 23 = Z_to_bv 64 (MLOCK + 8 * sc) ->
                keeps_but BIG regs r1 -> getr r1 10 = Z_to_bv 64 can ->
                kat RSEGS (mkCfg (mkst r1 (0x62c98%bv : word) M1 rom) mdl) Q) ->
    kat RSEGS (mkCfg (mkst regs (0x62c40%bv : word) M rom) mdl) Q.
  Proof using DEF Hsp R2 R11 R10 Hsc Hlz Hh HREP d RN.
    intros HK. pose proof (rp_statics st M HREP) as [Snl Spg Slk Scan Sgot Serr Sctz Ssc].
    pose proof scl_rng. assert (Hsp' : CEIL + 144 <= sp < 2 ^ 64) by (ceil; pose proof stk272; lia).
    destruct (aPro M sp sc req can Hsp' Hsc SOK144 Sgot Scan regs rom R2 R10 R11)
      as (r1 & RUN & E2' & E8 & E18 & E20 & E10 & E22 & E23 & K).
    eapply kat_msteps; [exact Hh | exact Hlz | exact RUN |]. fold M1. apply HK; try assumption.
    eapply keeps_but_mono; [exact K|]. intros r Hr. apply in_regs_dec.
    cbn in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma pt_first : forall r1,
    getr r1 2 = Z_to_bv 64 (sp - 144) -> getr r1 8 = Z_to_bv 64 sc ->
    getr r1 20 = Z_to_bv 64 A_CANARY -> getr r1 21 = Z_to_bv 64 (ctx_active sc) -> getr r1 22 = Z_to_bv 64 MLOCK -> getr r1 23 = Z_to_bv 64 (MLOCK + 8 * sc) ->
    keeps_but BIG regs r1 -> pt st M1 mdl r1.
  Proof using DEF Hsp Hmat Hlz Hh HLG HREP HWF.
    intros r1 E2 E8 E20 E21 E22 E23 K. constructor; try assumption; try (left; reflexivity).
    - exact M1_REP.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - intros; reflexivity.
    - intros; reflexivity.
    - intros x Ux; exact Ux.
    - intros a Ha NE. left. pose proof (M1_writes a Ha NE). pose proof stk272. lia.
    - unfold M1, as_frame. repeat apply defined_wbytes. exact DEF.
    - exact M1_stk.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma L_E : forall s1 Mc mdl1 r (g idx : Z),
    ptE s1 Mc mdl1 r -> s_limbo s1 = s_limbo st ->
    head_of (s_alist s1 sc) = g -> is_group s1 g -> g_sc s1 g = sc -> 0 <= idx <= g_lastidx s1 g ->
    s_slot s1 g idx = SJunk 0 -> only_junk s1 g idx -> req + 4 <= g_stride s1 g -> (16 * size_class sc <= g_stride s1 g \/ 4080 <= g_stride s1 g) ->
    getr r 10 = Z_to_bv 64 idx ->
    kat RSEGS (mkCfg (mkst r (0x634a0%bv : word) Mc rom) mdl1) Q.
  Proof using HQ Hsp Rra R2.
    intros s1 Mc mdl1 r g idx P EL Hhd Hg Hgsc Hidx Hsl OJ Hstr Hbig A10.
    pose proof P as [W1 RP1 LG1 Hh1 Hlz1 Hmat1 Hfs1 Hfds1 Hlim1 Hcan1 Herr1 BL1 LM1 MU1 FR1 DF1 SK1 Q2 Q20 KB].
    pose proof SK1 as (Kc & K1 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25).
    pose proof (rc_canary s1 Mc (rp_statics s1 Mc RP1)) as CAN. rewrite Hcan1 in CAN. fold can in CAN.
    assert (Hsp' : CEIL + 144 <= sp < 2 ^ 64) by (ceil; pose proof stk272; lia).
    destruct (aEpi Mc sp can (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
                (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) Hsp' Rra CAN Kc K1 K8 K9 K18 K19 K20 K21 K22 K23 K24 K25
                r rom Q2 Q20) as (r' & RUN & E2 & E10 & E1 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & K').
    eapply kat_msteps; [exact Hh1 | exact Hlz1 | exact RUN |].
    apply kat_refl. apply HQ. unfold as_ok.
    exists s1, Mc, mdl1, r', g, idx.
    split; [reflexivity|].
    split; [exact W1|]. split; [exact RP1|]. split; [exact LG1|].
    split; [exact Hh1|]. split; [exact Hlz1|]. split; [exact Hmat1|]. split; [exact Hfs1|]. split; [exact Hfds1|]. split; [exact Hlim1|].
    split; [exact EL|]. split; [exact Hcan1|]. split; [exact Herr1|].
    split; [exact Hhd|]. split; [exact Hg|]. split; [exact Hgsc|]. split; [exact Hidx|]. split; [exact Hsl|]. split; [exact OJ|]. split; [exact Hstr|]. split; [exact Hbig|].
    split; [exact BL1|]. split; [exact LM1|]. split; [exact MU1|].
    split; [rewrite E10; exact A10|]. split; [rewrite E2, R2; reflexivity|].
    split.
    { apply keeps_final_as; try assumption.
      - eapply keeps_big; [exact KB | exact K' | reflexivity].
      - rewrite E2, R2. reflexivity. }
    split; [exact FR1 | exact DF1].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma L_T : forall s1 Mc mdl1 r g mask,
    pt s1 Mc mdl1 r -> nojunk s1 -> s_limbo s1 = s_limbo st ->
    head_of (s_alist s1 sc) = g -> is_group s1 g -> g_sc s1 g = sc ->
    mr_avail (s_meta s1 g) = mask -> mask <> 0 ->
    getr r 10 = Z_to_bv 64 g -> getr r 11 = s32 mask ->
    kat RSEGS (mkCfg (mkst r (0x62de0%bv : word) Mc rom) mdl1) Q.
  Proof using HQ Hsp Rra R2 Hreq Hsc req.
    intros s1 Mc mdl1 r g mask P NJ1 EL Hhd Hg Hgsc Hav Hnz A10 A11. pose proof P as [W1 RP1 LG1 Hh1 Hlz1 Hmat1 Hfs1 Hfds1 Hlim1 Hcan1 Herr1 BL1 LM1 MU1 FR1 DF1 SK1 Q2 Q8 Q20 Q21 Q22 Q23 KB].
    pose proof (wG_each s1 L (WF_groups s1 L W1) g Hg) as WG.
    pose proof (wg_avr s1 L g WG) as AVR. rewrite Hav in AVR.
    destruct (lowbit_pow2 mask ltac:(lia)) as (i & Hi & Hlow & Hbit & _).
    pose proof (proj1 (wg_av s1 L g WG i ltac:(lia))) as AVi. rewrite Hav in AVi.
    destruct (AVi Hbit) as [Hil Hsli].
    destruct (G_meta_cells s1 L Mc W1 RP1 g Hg) as (ar1 & k1 & _ & _ & _ & _ & Rlo & Rhi & _ & RM1 & _ & _).
    pose proof (meta_store_ok s1 L Mc W1 RP1 g (group_metaU s1 L W1 g Hg)) as SOKg.
    assert (SOK24 : store_ok RSEGS Mc (Z_to_bv 64 (g + 24)) 4%nat = true) by (ceil; unfold HEAPLO in *; sok 40%nat SOKg).
    pose proof (rc_tab_ctz s1 Mc (rp_statics s1 Mc RP1)) as CTZ.
    destruct (aTake Mc g mask i ltac:(unfold HEAPLO in *; lia) AVR Hi Hlow Hbit SOK24 CTZ r rom A10 A11) as (r' & RUN & E10 & K').
    eapply kat_msteps; [exact Hh1 | exact Hlz1 | exact RUN |].
    (* [comment removed for export] *)
    set (Mc' := m_take Mc g mask i) in *.
    assert (G' : mem_grows Mc Mc') by (unfold Mc', m_take; apply wbytes_grows).
    assert (W' : forall a, 0 <= a < 2 ^ 64 -> Mc' (Z_to_bv 64 a) <> Mc (Z_to_bv 64 a) -> g + 24 <= a < g + 28).
    { intros a Ha NE. ceil; unfold Mc', m_take, HEAPLO in *. wdiff NE Mc a. }
    assert (Hhd' : g = head_of (s_alist s1 (g_sc s1 g))) by (rewrite Hgsc; symmetry; exact Hhd).
    destruct (take_close s1 L Mc Mc' g i spc W1 RP1 Hg ltac:(lia) Hsli Hhd' spc_ok
                ltac:(intros a Ha NE; right; exact (W' a Ha NE)) G'
                ltac:(unfold Mc', m_take; rewrite Hav; apply cell_hit; ceil; unfold HEAPLO in *; cbn; lia)) as [W2 RP2].
    set (s2 := MhTake.st' s1 g i) in *.
    assert (P2 : pt s2 Mc' mdl1 r').
    { apply (pt_step s1 Mc mdl1 r s2 Mc' r' P W2 RP2 eq_refl eq_refl eq_refl eq_refl
               ltac:(intros; reflexivity)
               ltac:(intros x Hx; apply MhTake.e_meta_other; intros ->; exact (proj1 (proj2 (wG_limbo s1 L (WF_groups s1 L W1) g ltac:(rewrite EL; exact Hx))) Hg))
               ltac:(intros x Ux; exact Ux) G').
      - intros a Ha NE. apply (meta_WOK s1 g a W1 (group_metaU s1 L W1 g Hg)). pose proof (W' a Ha NE). lia.
      - kept_rw K'; reflexivity.
      - kept_rw K'; reflexivity.
      - kept_rw K'; reflexivity.
      - kept_rw K'; reflexivity.
      - kept_rw K'; reflexivity.
      - kept_rw K'; reflexivity.
      - eapply keeps_big; [exact KB | exact K' | reflexivity]. }
    apply (L_E s2 Mc' mdl1 r' g i (pt_ptE _ _ _ _ P2)).
    - exact EL.
    - exact Hhd.
    - exact Hg.
    - change (g_sc s2 g) with (g_sc (MhTake.st' s1 g i) g). rewrite (MhTake.e_gsc s1 g i). exact Hgsc.
    - change (g_lastidx s2 g) with (g_lastidx (MhTake.st' s1 g i) g). rewrite (MhTake.e_glast s1 g i). lia.
    - apply MhTake.e_slot_mi.
    - intros x k o Hx Hk E. change (is_group s1 x) in Hx.
      change (g_lastidx s2 x) with (g_lastidx (MhTake.st' s1 g i) x) in Hk. rewrite (MhTake.e_glast s1 g i) in Hk.
      change (s_slot s2 x k) with (s_slot (MhTake.st' s1 g i) x k) in E. rewrite (MhTake.e_slot s1 g i) in E.
      destruct (Z.eqb_spec x g) as [Ex|Nx]; [destruct (Z.eqb_spec k i) as [Ek|Nk]; [split; assumption|]|]; cbn [andb] in E;
        exfalso; exact (NJ1 x k o Hx Hk E).
    - change (g_stride s2 g) with (g_stride (MhTake.st' s1 g i) g). rewrite (MhTake.e_gstride s1 g i).
      (* [comment removed for export] *)
      destruct (Z.lt_ge_cases (g_stride s1 g) (UNIT * size_class (g_sc s1 g))) as [LT|GE].
      + exfalso. destruct (wg_fit s1 L g WG ltac:(lia) LT i ltac:(lia)) as [X _].
        exact (X Hsli).
      + rewrite Hgsc in GE. unfold UNIT in GE. lia.
    - change (g_stride s2 g) with (g_stride (MhTake.st' s1 g i) g). rewrite (MhTake.e_gstride s1 g i). left.
      destruct (Z.lt_ge_cases (g_stride s1 g) (UNIT * size_class (g_sc s1 g))) as [LT|GE].
      + exfalso. destruct (wg_fit s1 L g WG ltac:(lia) LT i ltac:(lia)) as [X _]. exact (X Hsli).
      + rewrite Hgsc in GE. unfold UNIT in GE. lia.
    - exact E10.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma L_A8 : forall s1 Mc mdl1 r g,
    pt s1 Mc mdl1 r -> nojunk s1 -> s_limbo s1 = s_limbo st ->
    head_of (s_alist s1 sc) = g -> is_group s1 g -> g_sc s1 g = sc ->
    mr_avail (s_meta s1 g) = 0 -> lo_bits (mr_freed (s_meta s1 g)) (s_ai s1 g + 1) <> 0 ->
    getr r 10 = Z_to_bv 64 g ->
    kat RSEGS (mkCfg (mkst r (0x62d68%bv : word) Mc rom) mdl1) Q.
  Proof using HQ Hsp Rra R2 Hreq Hsc req.
    intros s1 Mc mdl1 r g P NJ1 EL Hhd Hg Hgsc Hav0 Hlo A10.
    pose proof P as [W1 RP1 LG1 Hh1 Hlz1 Hmat1 Hfs1 Hfds1 Hlim1 Hcan1 Herr1 BL1 LM1 MU1 FR1 DF1 SK1 Q2 Q8 Q20 Q21 Q22 Q23 KB].
    pose proof (wG_each s1 L (WF_groups s1 L W1) g Hg) as WG.
    pose proof (wg_frr s1 L g WG) as FRR. pose proof (wg_Wr s1 L g WG) as WR. pose proof (wg_ai s1 L g WG) as AIR.
    pose proof (wg_mem s1 L g WG) as (GM1 & GM2 & GM3). pose proof (wg_stride s1 L g WG) as [S16 _]. pose proof (glast_rng s1 g) as GL.
    destruct (G_meta_cells s1 L Mc W1 RP1 g Hg) as (ar1 & k1 & _ & _ & _ & _ & Rlo & Rhi & G8 & RM1 & _ & _).
    destruct RM1 as [_ _ Rme _ Rfr RW].
    pose proof (meta_store_ok s1 L Mc W1 RP1 g (group_metaU s1 L W1 g Hg)) as SOKg.
    assert (SOK24 : store_ok RSEGS Mc (Z_to_bv 64 (g + 24)) 8%nat = true) by (ceil; unfold HEAPLO in *; sok 40%nat SOKg).
    destruct (rg_aidx s1 Mc g (rp_groups s1 Mc RP1 g Hg)) as (b & Hb & Bat & Bmod).
    pose proof (byte_at_rdn1 Mc _ _ Bat) as Rb.
    destruct (group_range s1 L W1 g Hg) as [GR1 GR2].
    assert (SPAN16 : g_mem s1 g + 16 <= gspan s1 g) by (unfold gspan, g_span_end, g_cnt, UNIT, IB; nia).
    assert (Hmemg : HEAPLO <= g_mem s1 g /\ g_mem s1 g + 16 <= CEIL /\ (g_mem s1 g + 16 <= IMG_LO \/ IMG_HI <= g_mem s1 g)) by lia.
    pose proof (rdn_lo4 Mc (g + 32) (g_W s1 g) WR (RW : rdn RSEGS Mc (Z_to_bv 64 (g + 32)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (g_W s1 g))))) as RW4.
    assert (Hlo' : lo_bits (mr_freed (s_meta s1 g)) (b mod 32 + 1) <> 0) by (rewrite Bmod; exact Hlo).
    assert (Escw : w_sizeclass (g_W s1 g) = sc) by (unfold g_sc in Hgsc; exact Hgsc).
    pose proof (ctx_store_ok s1 Mc RP1) as SOKc.
    (* [comment removed for export] *)
    set (Ma := m_act8 Mc g b (mr_freed (s_meta s1 g))).
    assert (GA : mem_grows Mc Ma) by (unfold Ma, m_act8; eapply mem_grows_trans; apply wbytes_grows).
    assert (WA : forall a, 0 <= a < 2 ^ 64 -> Ma (Z_to_bv 64 a) <> Mc (Z_to_bv 64 a) -> g + 24 <= a < g + 32).
    { intros a Ha NE. ceil; unfold Ma, m_act8, HEAPLO in *. wdiff NE Mc a. }
    assert (Hhd' : g = head_of (s_alist s1 (g_sc s1 g))) by (rewrite Hgsc; symmetry; exact Hhd).
    destruct (activate_close s1 L Mc Ma g spc W1 RP1 Hg Hhd' Hav0 spc_ok ltac:(intros a Ha NE; right; exact (WA a Ha NE)) GA
                ltac:(unfold MhActivate.av', Ma, m_act8; rewrite <- Bmod; apply cell_hit; ceil; unfold HEAPLO in *; cbn; lia)
                ltac:(unfold MhActivate.fr', Ma, m_act8; rewrite <- Bmod; apply cell_peel; [apply cell_hit| | | | |]; wd_lenlit; rewrite ?length_N_to_le_bytes; ceil; unfold HEAPLO in *; cbn; lia))
      as [W2 RP2].
    set (s2 := MhActivate.st' s1 g) in *.
    assert (CONT : forall r' (Mb : mem),
      getr r' 10 = Z_to_bv 64 g -> getr r' 11 = s32 (lo_bits (mr_freed (s_meta s1 g)) (b mod 32 + 1)) -> keeps_but clobA8 r r' ->
      ((Mb = Ma /\ (c_bounces (s_ctx s1) (sc - 7) = 0 \/ ~ 7 <= sc <= 38)) \/ (7 <= sc <= 38 /\ Mb = wbytes Ma (Z_to_bv 64 (ctx_bounces (sc - 7))) (word_to_le_bytes 1 (Z_to_bv 64 (c_bounces (s_ctx s1) (sc - 7) - 1))) /\ c_bounces (s_ctx s1) (sc - 7) <> 0)) ->
      kat RSEGS (mkCfg (mkst r' (0x62de0%bv : word) Mb rom) mdl1) Q).
    { intros r' Mb E10 E11 K' HMb.
      (* [comment removed for export] *)
      set (bfun := fun i => if (i =? sc - 7) && negb (c_bounces (s_ctx s1) (sc - 7) =? 0) && (7 <=? sc) && (sc <=? 38) then c_bounces (s_ctx s1) (sc - 7) - 1 else c_bounces (s_ctx s2) i).
      pose proof (wc_bnc s2 (WF_ctx s2 L W2)) as BR. change (s_ctx s2) with (s_ctx s1) in BR.
      assert (GB : mem_grows Ma Mb) by (destruct HMb as [[-> _] | (_ & -> & _)]; [apply mem_grows_refl | apply wbytes_grows]).
      assert (WB : forall a, 0 <= a < 2 ^ 64 -> Mb (Z_to_bv 64 a) <> Ma (Z_to_bv 64 a) -> 7 <= sc <= 38 /\ a = ctx_bounces (sc - 7) /\ c_bounces (s_ctx s1) (sc - 7) <> 0).
      { intros a Ha NE. destruct HMb as [[-> _] | (R7 & -> & NZ)]; [exfalso; exact (NE eq_refl)|].
        unfold ctx_bounces, CTX in *. split; [exact R7|]. split; [|exact NZ]. wdiff NE Ma a. }
      set (WSb := fun a => 7 <= sc <= 38 /\ a = ctx_bounces (sc - 7) /\ c_bounces (s_ctx s1) (sc - 7) <> 0).
      assert (HPb : forall i, 0 <= bfun i < 256).
      { intros i; subst bfun; cbv beta. destruct (Z.eqb_spec i (sc - 7)); cbn [andb]; [|apply BR].
        destruct (Z.eqb_spec (c_bounces (s_ctx s1) (sc - 7)) 0); cbn [negb andb]; [apply BR|].
        destruct ((7 <=? sc) && (sc <=? 38))%bool; [pose proof (BR (sc - 7)); lia | apply BR]. }
      assert (HPwr : forall a, 0 <= a < 2 ^ 64 -> Mb (Z_to_bv 64 a) <> Ma (Z_to_bv 64 a) -> (spc - MSTK <= a < spc) \/ (CTX + 464 <= a < CTX + 913 /\ WSb a)).
      { intros a Ha NE; right. destruct (WB a Ha NE) as (R7 & -> & NZ). subst WSb; cbv beta. unfold ctx_bounces, CTX. split; [lia|]. split; [lia|]. split; [reflexivity | exact NZ]. }
      assert (HPu : forall j, 0 <= j < 48 -> cell Mb (ctx_usage j) 8 (c_usage (s_ctx s2) j) \/ (c_usage (s_ctx s2) j = c_usage (s_ctx s2) j /\ forall a, ctx_usage j <= a < ctx_usage j + 8 -> ~ WSb a)).
      { intros j Hj; right; split; [reflexivity|]. intros a Ha (R7 & E & _). unfold ctx_usage, ctx_bounces in *. lia. }
      assert (HPq : forall j, 0 <= j < 32 -> cell Mb (ctx_unmap_seq j) 1 (c_unmap_seq (s_ctx s2) j) \/ (c_unmap_seq (s_ctx s2) j = c_unmap_seq (s_ctx s2) j /\ ~ WSb (ctx_unmap_seq j))).
      { intros j Hj; right; split; [reflexivity|]. intros (R7 & E & _). unfold ctx_unmap_seq, ctx_bounces in *. lia. }
      assert (HPbn : forall j, 0 <= j < 32 -> cell Mb (ctx_bounces j) 1 (bfun j) \/ (bfun j = c_bounces (s_ctx s2) j /\ ~ WSb (ctx_bounces j))).
      { intros j Hj; subst bfun WSb; cbv beta.
        destruct (Z.eqb_spec j (sc - 7)) as [->|NEj]; cbn [andb].
        - destruct (Z.eqb_spec (c_bounces (s_ctx s1) (sc - 7)) 0) as [Z0|NZ]; cbn [negb andb].
          + right; split; [reflexivity|]. intros (_ & _ & X). exact (X Z0).
          + destruct (Z.leb_spec 7 sc); cbn [andb]; [destruct (Z.leb_spec sc 38); cbn [andb]|].
            * left. destruct HMb as [[-> X] | (_ & -> & _)].
              { exfalso. destruct X as [X|X]; [exact (NZ X) | apply X; lia]. }
              unfold cell. rewrite w2le1 by (pose proof (BR (sc - 7)); lia). apply cell_hit1; unfold ctx_bounces, CTX; cbn; lia.
            * right; split; [reflexivity|]. intros (X & _). lia.
            * right; split; [reflexivity|]. intros (X & _). lia.
        - right; split; [reflexivity|]. intros (R7 & E & _). unfold ctx_bounces in E. lia. }
      assert (HPs : cell Mb ctx_seq 1 (c_seq (s_ctx s2)) \/ (c_seq (s_ctx s2) = c_seq (s_ctx s2) /\ ~ WSb ctx_seq)).
      { right; split; [reflexivity|]. subst WSb; cbv beta. intros (R7 & E & _). unfold ctx_seq, ctx_bounces in E. lia. }
      destruct (policy_close s2 L Ma Mb spc (c_usage (s_ctx s2)) (c_unmap_seq (s_ctx s2)) bfun (c_seq (s_ctx s2)) WSb W2 RP2
                  (wc_usage s2 (WF_ctx s2 L W2)) (wc_useq s2 (WF_ctx s2 L W2)) HPb (wc_seq s2 (WF_ctx s2 L W2)) spc_ok HPwr GB HPu HPq HPbn HPs)
        as [W3 RP3].
      set (s3 := MhPolicy.st' s2 (c_usage (s_ctx s2)) (c_unmap_seq (s_ctx s2)) bfun (c_seq (s_ctx s2))) in *.
      assert (P3 : pt s3 Mb mdl1 r').
      { apply (pt_step s1 Mc mdl1 r s3 Mb r' P W3 RP3 eq_refl eq_refl eq_refl eq_refl
                 ltac:(intros; reflexivity)
                 ltac:(intros x Hx; change (s_meta s3 x) with (s_meta (MhActivate.st' s1 g) x); apply MhActivate.e_meta_other; intros ->; exact (proj1 (proj2 (wG_limbo s1 L (WF_groups s1 L W1) g ltac:(rewrite EL; exact Hx))) Hg))
                 ltac:(intros x Ux; exact Ux) (mem_grows_trans _ _ _ GA GB)).
        - intros a Ha NE. destruct (decide (Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a))) as [E|NE2].
          + rewrite E in NE. apply (meta_WOK s1 g a W1 (group_metaU s1 L W1 g Hg)). pose proof (WA a Ha NE). lia.
          + destruct (WB a Ha NE2) as (R7 & -> & _). apply ctx_WOK. unfold ctx_bounces, CTX_END. lia.
        - kept_rw K'; reflexivity.
        - kept_rw K'; reflexivity.
        - kept_rw K'; reflexivity.
        - kept_rw K'; reflexivity.
        - kept_rw K'; reflexivity.
        - kept_rw K'; reflexivity.
        - eapply keeps_big; [exact KB | exact K' | reflexivity]. }
      apply (L_T s3 Mb mdl1 r' g (lo_bits (mr_freed (s_meta s1 g)) (s_ai s1 g + 1)) P3).
      - intros x k o Hx Hk E. change (is_group s1 x) in Hx.
        change (g_lastidx s3 x) with (g_lastidx (MhActivate.st' s1 g) x) in Hk. rewrite (MhActivate.e_glast s1 g) in Hk.
        change (s_slot s3 x k) with (MhActivate.a_slot s1 g x k) in E.
        destruct (MhActivate.a_slot_cases s1 g x k) as [[Ea _]|(_ & _ & _ & Ea)]; rewrite Ea in E; [exact (NJ1 x k o Hx Hk E) | discriminate E].
      - exact EL.
      - exact Hhd.
      - exact Hg.
      - change (g_sc s3 g) with (g_sc (MhActivate.st' s1 g) g). rewrite (MhActivate.e_gsc s1 g). exact Hgsc.
      - change (mr_avail (s_meta s3 g)) with (mr_avail (s_meta (MhActivate.st' s1 g) g)). rewrite (MhActivate.e_avail_h s1 g). reflexivity.
      - exact Hlo.
      - exact E10.
      - rewrite E11, Bmod. reflexivity. }
    (* [comment removed for export] *)
    destruct (decide (7 <= sc <= 38)) as [IN|OUT].
    - pose proof (wc_bnc s1 (WF_ctx s1 L W1) (sc - 7)) as BNR.
      pose proof (cell1_rdn Mc _ _ BNR (rc_bnc s1 Mc (rp_ctx s1 Mc RP1) (sc - 7) ltac:(lia))) as Rbn.
      assert (SOKb : store_ok RSEGS Mc (Z_to_bv 64 (ctx_bounces (sc - 7))) 1%nat = true) by (unfold ctx_bounces, CTX in *; sok 928%nat SOKc).
      destruct (Z.eq_dec (c_bounces (s_ctx s1) (sc - 7)) 0) as [BZ|BNZ].
      + destruct (aAct8z Mc g (g_mem s1 g) b (mr_freed (s_meta s1 g)) (g_W s1 g) (c_bounces (s_ctx s1) (sc - 7))
                    ltac:(unfold HEAPLO in *; lia) Hmemg Hb FRR WR BNR Rme Rb Rfr RW4 SOK24
                    ltac:(rewrite Escw; intros _; exact Rbn) ltac:(rewrite Escw; intros _; exact SOKb) Hlo' r rom A10 Q22 ltac:(rewrite Escw; exact IN) BZ)
          as (r' & RUN & E10 & E11 & K').
        eapply kat_msteps; [exact Hh1 | exact Hlz1 | exact RUN |]. apply (CONT r' _ E10 E11 K'). left. split; [reflexivity | left; exact BZ].
      + destruct (aAct8d Mc g (g_mem s1 g) b (mr_freed (s_meta s1 g)) (g_W s1 g) (c_bounces (s_ctx s1) (sc - 7))
                    ltac:(unfold HEAPLO in *; lia) Hmemg Hb FRR WR BNR Rme Rb Rfr RW4 SOK24
                    ltac:(rewrite Escw; intros _; exact Rbn) ltac:(rewrite Escw; intros _; exact SOKb) Hlo' r rom A10 Q22 ltac:(rewrite Escw; exact IN) BNZ)
          as (r' & RUN & E10 & E11 & K').
        eapply kat_msteps; [exact Hh1 | exact Hlz1 | exact RUN |]. apply (CONT r' _ E10 E11 K'). right.
        split; [exact IN|]. split; [|exact BNZ]. unfold m_act8d. rewrite Escw. reflexivity.
    - destruct (aAct8n Mc g (g_mem s1 g) b (mr_freed (s_meta s1 g)) (g_W s1 g) 0
                  ltac:(unfold HEAPLO in *; lia) Hmemg Hb FRR WR ltac:(lia) Rme Rb Rfr RW4 SOK24 Hlo' r rom A10 Q22 ltac:(rewrite Escw; lia))
        as (r' & RUN & E10 & E11 & K').
      eapply kat_msteps; [exact Hh1 | exact Hlz1 | exact RUN |]. apply (CONT r' _ E10 E11 K'). left. split; [reflexivity | right; exact OUT].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma lo_zero_partial : forall s1 g, WF s1 L -> is_group s1 g ->
    mr_freed (s_meta s1 g) <> 0 -> lo_bits (mr_freed (s_meta s1 g)) (s_ai s1 g + 1) = 0 ->
    s_ai s1 g < g_lastidx s1 g /\ Z.testbit (mr_freed (s_meta s1 g)) (s_ai s1 g + 1) = true.
  Proof using d.
    intros s1 g W Hg NZ LO. pose proof (wG_each s1 L (WF_groups s1 L W) g Hg) as WG.
    pose proof (wg_frr s1 L g WG) as FRR. pose proof (wg_ai s1 L g WG) as AIR. pose proof (glast_rng s1 g) as GL.
    (* [comment removed for export] *)
    assert (EX : exists i, 0 <= i /\ Z.testbit (mr_freed (s_meta s1 g)) i = true).
    { destruct (Z.eq_dec (mr_freed (s_meta s1 g)) 0) as [E|NE]; [exfalso; exact (NZ E)|].
      destruct (lowbit_pow2 (mr_freed (s_meta s1 g)) ltac:(lia)) as (i & Hi & _ & Hb & _). exists i. split; [lia | exact Hb]. }
    destruct EX as (i & Hi0 & Hbi).
    pose proof (proj1 (wg_fr s1 L g WG i Hi0) Hbi) as [Hil Hsl].
    assert (Hia : s_ai s1 g + 1 <= i).
    { destruct (Z.lt_ge_cases i (s_ai s1 g + 1)) as [LT|GE]; [|lia]. exfalso.
      assert (T : Z.testbit (lo_bits (mr_freed (s_meta s1 g)) (s_ai s1 g + 1)) i = true).
      { unfold lo_bits. rewrite Z.mod_pow2_bits_low by lia. exact Hbi. }
      rewrite LO, Z.bits_0 in T. discriminate T. }
    split; [lia|].
    apply (proj2 (wg_fr s1 L g WG (s_ai s1 g + 1) ltac:(lia))). split; [lia|].
    apply (wg_high s1 L g WG). lia.
  Qed.


  (* [comment removed for export] *)
  Lemma full_ai_lo : forall s1 g, WF s1 L -> is_group s1 g -> mr_freed (s_meta s1 g) <> 0 -> s_ai s1 g = g_lastidx s1 g ->
    lo_bits (mr_freed (s_meta s1 g)) (s_ai s1 g + 1) <> 0.
  Proof using d.
    intros s1 g W Hg NZ EA. pose proof (wG_each s1 L (WF_groups s1 L W) g Hg) as WG. pose proof (wg_frr s1 L g WG) as FRR.
    destruct (lowbit_pow2 (mr_freed (s_meta s1 g)) ltac:(lia)) as (i & Hi & _ & Hb & _).
    pose proof (proj1 (wg_fr s1 L g WG i ltac:(lia)) Hb) as [Hil _].
    apply (lo_bits_nz _ _ i); [lia | exact Hb].
  Qed.

  (* [comment removed for export] *)
  Lemma next_of_head : forall s1 g rest, WF s1 L -> s_alist s1 sc = g :: rest ->
    (mr_next (s_meta s1 g) = g <-> rest = []) /\ In (mr_next (s_meta s1 g)) (g :: rest) /\
    (rest <> [] -> mr_next (s_meta s1 g) = head_of rest /\ mr_next (s_meta s1 g) <> g).
  Proof using Hsp Hreq Hsc d req sp.
    intros s1 g rest W Hl. pose proof (WF_lists s1 L W) as WL.
    pose proof (proj1 (dll_dllf s1 _) (wl_adll s1 WL sc Hsc)) as D. rewrite Hl in D.
    pose proof (wl_anodup s1 WL sc) as ND. rewrite Hl in ND. apply NoDup_ListNoDup in ND.
    pose proof (dllf_self_iff _ _ _ g D ND ltac:(left; reflexivity)) as SI.
    destruct (dllf_links_In _ _ _ g D ltac:(left; reflexivity)) as [IN _].
    assert (E1 : zlen (g :: rest) = 1 <-> rest = []).
    { rewrite zlen_cons. split; [|intros ->; reflexivity]. intros E. destruct rest; [reflexivity|]. rewrite zlen_cons in E. pose proof (zlen_nonneg rest). lia. }
    split; [tauto|]. split; [exact IN|].
    intros NE. pose proof (D 0 ltac:(rewrite zlen_cons; pose proof (zlen_nonneg rest); lia)) as [N0 _].
    rewrite znth_cons0 in N0. rewrite zlen_cons in N0.
    assert (LR : 0 < zlen rest) by (destruct rest as [|y l]; [exfalso; exact (NE eq_refl)|]; rewrite zlen_cons; pose proof (zlen_nonneg l); lia).
    rewrite Z.mod_small in N0 by lia. rewrite znth_cons_S in N0 by lia. replace (0 + 1 - 1) with 0 in N0 by lia.
    split.
    - rewrite N0. destruct rest; [exfalso; exact (NE eq_refl)|]. reflexivity.
    - intros E. apply NE. tauto.
  Qed.

  Lemma head_facts : forall s1 g, WF s1 L -> head_of (s_alist s1 sc) = g -> g <> 0 ->
    exists rest, s_alist s1 sc = g :: rest /\ is_group s1 g /\ g_sc s1 g = sc.
  Proof using.
    intros s1 g W Hhd NZ. destruct (s_alist s1 sc) as [|g' rest] eqn:El; [cbn in Hhd; exfalso; exact (NZ (eq_sym Hhd))|].
    cbn in Hhd. subst g'. exists rest. split; [reflexivity|].
    destruct (wl_aU s1 (WF_lists s1 L W) sc g ltac:(rewrite El; left; reflexivity)) as (_ & G & S). split; assumption.
  Qed.

  Lemma member_facts : forall s1 x, WF s1 L -> In x (s_alist s1 sc) -> is_group s1 x /\ g_sc s1 x = sc /\ metaU s1 x /\
    HEAPLO + 24 <= x /\ x + 40 <= CEIL.
  Proof using.
    intros s1 x W Hin. destruct (wl_aU s1 (WF_lists s1 L W) sc x Hin) as (_ & G & S).
    pose proof (group_metaU s1 L W x G) as U. destruct (metaU_rng s1 L W x U) as (A & B & _). repeat split; try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma L_chk : forall s1 Mc mdl1 r g,
    pt s1 Mc mdl1 r -> nojunk s1 -> s_limbo s1 = s_limbo st ->
    head_of (s_alist s1 sc) = g -> is_group s1 g -> g_sc s1 g = sc ->
    mr_avail (s_meta s1 g) = 0 -> lo_bits (mr_freed (s_meta s1 g)) (s_ai s1 g + 1) <> 0 ->
    getr r 10 = Z_to_bv 64 g ->
    kat RSEGS (mkCfg (mkst r (0x62d5c%bv : word) Mc rom) mdl1) Q.
  Proof using HQ Hsp Rra R2 Hreq Hsc req.
    intros s1 Mc mdl1 r g P NJ1 EL Hhd Hg Hgsc Hav0 Hlo A10.
    pose proof P as [W1 RP1 LG1 Hh1 Hlz1 Hmat1 Hfs1 Hfds1 Hlim1 Hcan1 Herr1 BL1 LM1 MU1 FR1 DF1 SK1 Q2 Q8 Q20 Q21 Q22 Q23 KB].
    destruct (G_meta_cells s1 L Mc W1 RP1 g Hg) as (ar1 & k1 & _ & _ & _ & _ & Rlo & Rhi & _ & RM1 & _ & _).
    pose proof (rm_avail Mc g _ RM1) as Rav. rewrite Hav0 in Rav.
    destruct (aChk Mc g ltac:(unfold HEAPLO in *; lia) Rav r rom A10) as (r' & RUN & K').
    eapply kat_msteps; [exact Hh1 | exact Hlz1 | exact RUN |].
    apply (L_A8 s1 Mc mdl1 r' g); try assumption.
    - apply (pt_regs s1 Mc mdl1 r r' P); try (kept_rw K'; reflexivity). eapply keeps_big; [exact KB | exact K' | reflexivity].
    - kept_rw K'. exact A10.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma L_grow : forall s1 Mc mdl1 r g b,
    pt s1 Mc mdl1 r -> nojunk s1 -> s_limbo s1 = s_limbo st ->
    s_alist s1 sc = [g] -> is_group s1 g -> g_sc s1 g = sc ->
    mr_avail (s_meta s1 g) = 0 -> mr_freed (s_meta s1 g) <> 0 -> lo_bits (mr_freed (s_meta s1 g)) (s_ai s1 g + 1) = 0 ->
    byte_at Mc (g_mem s1 g + 8) b -> 0 <= b < 256 -> b mod 32 = s_ai s1 g ->
    getr r 10 = Z_to_bv 64 g -> getr r 11 = Z_to_bv 64 (g_mem s1 g) -> getr r 12 = Z_to_bv 64 b ->
    kat RSEGS (mkCfg (mkst r (0x63114%bv : word) Mc rom) mdl1) Q.
  Proof using HQ Hsp Rra R2 Hreq Hsc req.
    intros s1 Mc mdl1 r g b P NJ1 EL Hl Hg Hgsc Hav0 Hfr Hlo Bat Hb Bmod A10 A11 A12.
    pose proof P as [W1 RP1 LG1 Hh1 Hlz1 Hmat1 Hfs1 Hfds1 Hlim1 Hcan1 Herr1 BL1 LM1 MU1 FR1 DF1 SK1 Q2 Q8 Q20 Q21 Q22 Q23 KB].
    pose proof (wG_each s1 L (WF_groups s1 L W1) g Hg) as WG.
    pose proof (wg_frr s1 L g WG) as FRR. pose proof (wg_Wr s1 L g WG) as WR. pose proof (wg_ai s1 L g WG) as AIR.
    pose proof (wg_mem s1 L g WG) as (GM1 & GM2 & GM3). pose proof (wg_stride s1 L g WG) as [S16 _]. pose proof (glast_rng s1 g) as GL.
    destruct (G_meta_cells s1 L Mc W1 RP1 g Hg) as (ar1 & k1 & _ & _ & _ & _ & Rlo & Rhi & G8 & RM1 & _ & _).
    destruct RM1 as [_ _ Rme Rav Rfr RW]. rewrite Hav0 in Rav.
    destruct (group_range s1 L W1 g Hg) as [GR1 GR2].
    assert (SPAN16 : g_mem s1 g + 16 <= gspan s1 g) by (unfold gspan, g_span_end, g_cnt, UNIT, IB; nia).
    assert (Hmemg : HEAPLO <= g_mem s1 g /\ g_mem s1 g + 16 <= CEIL /\ (g_mem s1 g + 16 <= IMG_LO \/ IMG_HI <= g_mem s1 g)) by lia.
    destruct (lo_zero_partial s1 g W1 Hg Hfr Hlo) as [PART Tb].
    assert (Escw : w_sizeclass (g_W s1 g) = sc) by (unfold g_sc in Hgsc; exact Hgsc).
    assert (Elast : w_lastidx (g_W s1 g) = g_lastidx s1 g) by reflexivity.
    (* [comment removed for export] *)
    assert (Estr : g_stride s1 g = 16 * size_class sc).
    { unfold g_stride, slot_stride. rewrite <- Hgsc. unfold g_sc, g_lastidx, g_maplen, UNIT.
      replace (w_lastidx (g_W s1 g) =? 0) with false by (symmetry; apply Z.eqb_neq; unfold g_lastidx in *; lia). rewrite Bool.andb_false_r. reflexivity. }
    pose proof (wg_pnd s1 L g WG PART) as PND. rewrite Estr in PND.
    pose proof scl_rng as SCL.
    assert (TERM : gl_ok GFUEL (span0_of b (g_W s1 g)) (16 * size_class (w_sizeclass (g_W s1 g))) = true).
    { rewrite Escw. apply gl_ok_GFUEL; [lia | exact PND | unfold span0_of; rewrite Escw; pose proof (Z.mod_pos_bound b 32); nia]. }
    destruct (sc_entry_rom sc Hsc) as [_ TBL].
    pose proof (sc_tbl_read Mc sc ltac:(intros j Hj; exact (rc_tab_sc s1 Mc (rp_statics s1 Mc RP1) (SCT + j) ltac:(unfold SCT, A_TAB_SC, A_TAB_MED; lia))) Hsc) as RT.
    unfold SCT in RT.
    pose proof (meta_apart_span s1 L Mc W1 RP1 g Hg) as APART.
    assert (SOK8 : store_ok RSEGS Mc (Z_to_bv 64 (g_mem s1 g + 8)) 1%nat = true).
    { pose proof (group_bytes_defined s1 L Mc 8 g W1 RP1 (wg_depth s1 L g WG) Hg) as DEFg.
      eapply (store_ok_defined Mc (g_mem s1 g) (gspan s1 g)); [exact DEFg | lia | cbn; lia | unfold HEAPLO in *; lia | ceil; lia]. }
    destruct (aGrow Mc g (g_mem s1 g) b (g_W s1 g) (sc_entry sc) ltac:(unfold HEAPLO in *; lia) Hmemg ltac:(lia) Hb WR ltac:(rewrite Escw; lia)
                RW ltac:(rewrite Escw; exact RT) ltac:(rewrite Escw; exact TBL) Rav SOK8 TERM r rom A10 A11 A12) as (r' & RUN & E10 & K').
    eapply kat_msteps; [exact Hh1 | exact Hlz1 | exact RUN |].
    (* [comment removed for export] *)
    destruct (grow_facts g (g_mem s1 g) b (g_W s1 g) ltac:(unfold HEAPLO in *; lia) Hmemg ltac:(lia) Hb WR ltac:(rewrite Bmod, Elast; exact PART)) as (A1 & A2 & A3 & A4).
    rewrite Elast in A1. rewrite Bmod in A2.
    set (Mg := m_grow Mc (g_mem s1 g) b (g_W s1 g)) in *.
    assert (GG : mem_grows Mc Mg) by (unfold Mg, m_grow; apply wbytes_grows).
    assert (WG' : forall a, 0 <= a < 2 ^ 64 -> Mg (Z_to_bv 64 a) <> Mc (Z_to_bv 64 a) -> a = g_mem s1 g + 8).
    { intros a Ha NE. ceil; unfold Mg, m_grow, HEAPLO in *. wdiff NE Mc a. }
    assert (Hpart : forall x, is_group s1 x -> x <> g -> g_sc s1 x = g_sc s1 g -> s_ai s1 x = g_lastidx s1 x).
    { intros x Hx Hne Hs. pose proof (wg_ai s1 L x (wG_each s1 L (WF_groups s1 L W1) x Hx)) as AX.
      destruct (Z.lt_ge_cases (s_ai s1 x) (g_lastidx s1 x)) as [LT|GE]; [|lia]. exfalso.
      pose proof (wg_partial s1 L x (wG_each s1 L (WF_groups s1 L W1) x Hx) LT) as IN. rewrite Hs, Hgsc, Hl in IN.
      destruct IN as [E|[]]. exact (Hne (eq_sym E)). }
    destruct (aidx_close s1 L Mc Mg g (gaidx_of b (g_W s1 g)) (gbyte_of b (g_W s1 g)) spc W1 RP1 Hg ltac:(rewrite Hgsc, Hl; left; reflexivity)
                ltac:(lia) Hpart spc_ok ltac:(intros a Ha NE; right; exact (WG' a Ha NE)) GG ltac:(lia)
                ltac:(unfold byte_at, Mg, m_grow; rewrite w2le1 by lia; apply byte_hit)) as [W2 RP2].
    set (s2 := MhAidx.st' s1 g (gaidx_of b (g_W s1 g))) in *.
    assert (P2 : pt s2 Mg mdl1 r').
    { apply (pt_step s1 Mc mdl1 r s2 Mg r' P W2 RP2 eq_refl eq_refl eq_refl eq_refl
               ltac:(intros; reflexivity) ltac:(intros; reflexivity) ltac:(intros x Ux; exact Ux) GG).
      - intros a Ha NE. rewrite (WG' a Ha NE). apply (gcell_WOK s1 g _ W1 Hg). left. lia.
      - kept_rw K'; reflexivity.
      - kept_rw K'; reflexivity.
      - kept_rw K'; reflexivity.
      - kept_rw K'; reflexivity.
      - kept_rw K'; reflexivity.
      - kept_rw K'; reflexivity.
      - eapply keeps_big; [exact KB | exact K' | reflexivity]. }
    apply (L_A8 s2 Mg mdl1 r' g P2).
    - exact NJ1.
    - exact EL.
    - change (s_alist s2 sc) with (s_alist s1 sc). rewrite Hl. reflexivity.
    - exact Hg.
    - exact Hgsc.
    - exact Hav0.
    - change (s_ai s2 g) with (fupd (s_ai s1) g (gaidx_of b (g_W s1 g)) g). unfold fupd. rewrite Z.eqb_refl.
      change (s_meta s2 g) with (s_meta s1 g). apply (lo_bits_nz _ _ (s_ai s1 g + 1)); [lia | exact Tb].
    - exact E10.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rot_close : forall s1 Mc mdl1 r g rest r' cl,
    pt s1 Mc mdl1 r -> s_alist s1 sc = g :: rest -> mr_avail (s_meta s1 g) = 0 -> mr_freed (s_meta s1 g) <> 0 ->
    getr r' 2 = getr r 2 -> getr r' 8 = getr r 8 -> getr r' 20 = getr r 20 -> getr r' 21 = getr r 21 ->
    getr r' 22 = getr r 22 -> getr r' 23 = getr r 23 -> keeps_but cl r r' -> forallb (fun x => existsb (fun y => bv_eqb y x) BIG) cl = true ->
    let nx := mr_next (s_meta s1 g) in
    let s2 := MhRotate.st' s1 sc g rest in
    pt s2 (wbytes Mc (Z_to_bv 64 (ctx_active sc)) (word_to_le_bytes 8 (Z_to_bv 64 nx))) mdl1 r' /\
    s_alist s2 sc = rest ++ [g] /\ s_slot s2 = s_slot s1 /\ s_meta s2 = s_meta s1 /\ s_groups s2 = s_groups s1 /\ s_ai s2 = s_ai s1 /\
    s_limbo s2 = s_limbo s1 /\ s_kind s2 = s_kind s1 /\
    head_of (rest ++ [g]) = nx /\ In nx (g :: rest) /\ is_group s1 nx /\ g_sc s1 nx = sc /\
    mr_avail (s_meta s1 nx) = 0 /\ mr_freed (s_meta s1 nx) <> 0 /\
    (rest <> [] -> nx <> g) /\ (rest = [] -> nx = g).
  Proof using Hsp Hreq Hsc req.
    intros s1 Mc mdl1 r g rest r' cl P Hl Hav0 Hfr E2 E8 E20 E21 E22 E23 K Hcl nx s2.
    pose proof P as [W1 RP1 LG1 Hh1 Hlz1 Hmat1 Hfs1 Hfds1 Hlim1 Hcan1 Herr1 BL1 LM1 MU1 FR1 DF1 SK1 Q2 Q8 Q20 Q21 Q22 Q23 KB].
    set (M' := wbytes Mc (Z_to_bv 64 (ctx_active sc)) (word_to_le_bytes 8 (Z_to_bv 64 nx))).
    assert (G' : mem_grows Mc M') by (unfold M'; apply wbytes_grows).
    assert (W' : forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> Mc (Z_to_bv 64 a) -> ctx_active sc <= a < ctx_active sc + 8).
    { intros a Ha NE. unfold M', ctx_active, CTX in *. wdiff NE Mc a. }
    pose proof (MhRotate.nh_next s1 L sc g rest W1 Hsc Hl) as NH.
    destruct (rotate_close s1 L Mc M' sc g rest spc W1 RP1 Hsc Hl Hav0 Hfr spc_ok ltac:(intros a Ha NE; right; exact (W' a Ha NE)) G'
                ltac:(rewrite NH; unfold M'; apply cell_hit; unfold ctx_active, CTX; cbn; lia)) as [W2 RP2].
    destruct (next_of_head s1 g rest W1 Hl) as (SELF & IN & NE).
    destruct (member_facts s1 nx W1 ltac:(rewrite Hl; exact IN)) as (Gnx & Snx & Unx & _).
    assert (AVF : mr_avail (s_meta s1 nx) = 0 /\ mr_freed (s_meta s1 nx) <> 0).
    { destruct rest as [|y rest'].
      - assert (Enx : nx = g) by (apply (proj2 SELF); reflexivity). rewrite Enx. split; assumption.
      - destruct (NE ltac:(discriminate)) as [_ NEg].
        exact (wl_rest s1 (WF_lists s1 L W1) sc nx ltac:(rewrite Hl; exact IN) ltac:(rewrite Hl; cbn; intros E; exact (NEg E))). }
    split.
    { apply (pt_step s1 Mc mdl1 r s2 M' r' P W2 RP2 eq_refl eq_refl eq_refl eq_refl
               ltac:(intros k Hk; apply MhRotate.e_alist_other; lia) ltac:(intros; reflexivity) ltac:(intros x Ux; exact Ux) G'); try assumption.
      - intros a Ha NEa. apply (active_WOK sc a Hsc (W' a Ha NEa)).
      - eapply keeps_big; [exact KB | exact K | exact Hcl]. }
    split; [apply MhRotate.e_alist_sc|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    split; [unfold MhRotate.nh, MhRotate.l' in NH; exact NH|]. split; [exact IN|]. split; [exact Gnx|]. split; [exact Snx|]. split; [exact (proj1 AVF)|]. split; [exact (proj2 AVF)|].
    split; [intros Hne; exact (proj2 (NE Hne)) | intros E; exact (proj2 SELF E)].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma L_A6 : forall s1 Mc mdl1 r g rest,
    pt s1 Mc mdl1 r -> nojunk s1 -> s_limbo s1 = s_limbo st ->
    s_alist s1 sc = g :: rest -> mr_avail (s_meta s1 g) = 0 -> mr_freed (s_meta s1 g) <> 0 ->
    getr r 10 = Z_to_bv 64 g -> getr r 13 = s32 (mr_freed (s_meta s1 g)) -> getr r 14 = Z_to_bv 64 2 ->
    kat RSEGS (mkCfg (mkst r (0x62d34%bv : word) Mc rom) mdl1) Q.
  Proof using HQ Hsp Rra R2 Hreq Hsc req.
    intros s1 Mc mdl1 r g rest P NJ1 EL Hl Hav0 Hfr A10 A13 A14.
    pose proof P as [W1 RP1 LG1 Hh1 Hlz1 Hmat1 Hfs1 Hfds1 Hlim1 Hcan1 Herr1 BL1 LM1 MU1 FR1 DF1 SK1 Q2 Q8 Q20 Q21 Q22 Q23 KB].
    destruct (member_facts s1 g W1 ltac:(rewrite Hl; left; reflexivity)) as (Hg & Hgsc & Ug & _).
    pose proof (wG_each s1 L (WF_groups s1 L W1) g Hg) as WG.
    pose proof (wg_frr s1 L g WG) as FRR. pose proof (wg_ai s1 L g WG) as AIR.
    pose proof (wg_mem s1 L g WG) as (GM1 & GM2 & GM3). pose proof (wg_stride s1 L g WG) as [S16 _]. pose proof (glast_rng s1 g) as GL.
    destruct (G_meta_cells s1 L Mc W1 RP1 g Hg) as (ar1 & k1 & _ & _ & _ & _ & Rlo & Rhi & G8 & RM1 & _ & _).
    destruct RM1 as [_ Rnx Rme Rav Rfr RW].
    destruct (rg_aidx s1 Mc g (rp_groups s1 Mc RP1 g Hg)) as (b & Hb & Bat & Bmod).
    pose proof (byte_at_rdn1 Mc _ _ Bat) as Rb.
    destruct (group_range s1 L W1 g Hg) as [GR1 GR2].
    assert (SPAN16 : g_mem s1 g + 16 <= gspan s1 g) by (unfold gspan, g_span_end, g_cnt, UNIT, IB; nia).
    assert (Hmemg : HEAPLO <= g_mem s1 g /\ g_mem s1 g + 16 <= CEIL /\ (g_mem s1 g + 16 <= IMG_LO \/ IMG_HI <= g_mem s1 g)) by lia.
    assert (Hhd : head_of (s_alist s1 sc) = g) by (rewrite Hl; reflexivity).
    assert (ELO : Z.land (act_of b) (mr_freed (s_meta s1 g)) = lo_bits (mr_freed (s_meta s1 g)) (s_ai s1 g + 1)).
    { rewrite Z.land_comm, land_act_lo by lia. rewrite Bmod. reflexivity. }
    destruct (Z.eq_dec (lo_bits (mr_freed (s_meta s1 g)) (s_ai s1 g + 1)) 0) as [LO0|LONZ].
    - (* [comment removed for export] *)
      destruct (next_of_head s1 g rest W1 Hl) as (SELF & IN & NE).
      destruct rest as [|y rest'].
      + assert (Enx : mr_next (s_meta s1 g) = g) by (apply (proj2 SELF); reflexivity).
        destruct (aAct0g Mc g (g_mem s1 g) b (mr_freed (s_meta s1 g)) (mr_next (s_meta s1 g)) ltac:(unfold HEAPLO in *; lia) Hmemg Hb
                    ltac:(rewrite Enx; unfold HEAPLO in *; lia) Rme Rb Rnx r rom A10 A13 A14 ltac:(rewrite ELO; exact LO0) Enx)
          as (r' & RUN & E10 & E11 & E12 & K').
        eapply kat_msteps; [exact Hh1 | exact Hlz1 | exact RUN |].
        apply (L_grow s1 Mc mdl1 r' g b); try assumption.
        apply (pt_regs s1 Mc mdl1 r r' P); try (kept_rw K'; reflexivity). eapply keeps_big; [exact KB | exact K' | reflexivity].
      + destruct (NE ltac:(discriminate)) as [Enx NEg].
        destruct (member_facts s1 (mr_next (s_meta s1 g)) W1 ltac:(rewrite Hl; exact IN)) as (Gnx & Snx & Unx & Xlo & Xhi).
        pose proof (ctx_store_ok s1 Mc RP1) as SOKc.
        assert (SOKa : store_ok RSEGS Mc (Z_to_bv 64 (ctx_active sc)) 8%nat = true) by (unfold ctx_active, CTX in *; sok 928%nat SOKc).
        destruct (aAct0r Mc sc g (g_mem s1 g) b (mr_freed (s_meta s1 g)) (mr_next (s_meta s1 g)) Hsc ltac:(unfold HEAPLO in *; lia) Hmemg Hb
                    ltac:(unfold HEAPLO in *; lia) Rme Rb Rnx SOKa r rom A10 A13 A14 Q21 ltac:(rewrite ELO; exact LO0) NEg)
          as (r' & RUN & E10 & K').
        eapply kat_msteps; [exact Hh1 | exact Hlz1 | exact RUN |].
        destruct (rot_close s1 Mc mdl1 r g (y :: rest') r' _ P Hl Hav0 Hfr
                    ltac:(kept_rw K'; reflexivity) ltac:(kept_rw K'; reflexivity) ltac:(kept_rw K'; reflexivity)
                    ltac:(kept_rw K'; reflexivity) ltac:(kept_rw K'; reflexivity) ltac:(kept_rw K'; reflexivity) K' eq_refl)
          as (P2 & AL2 & SL2 & MT2 & GR2' & AI2 & LB2 & KD2 & HD2 & _ & _ & _ & AV2 & FR2 & _ & _).
        set (s2 := MhRotate.st' s1 sc g (y :: rest')) in *. set (nx := mr_next (s_meta s1 g)) in *.
        apply (L_chk s2 _ mdl1 r' nx P2).
        * intros x k o Hx Hk E. rewrite SL2 in E. exact (NJ1 x k o Hx Hk E).
        * rewrite LB2. exact EL.
        * rewrite AL2. exact HD2.
        * exact Gnx.
        * exact Snx.
        * rewrite MT2. exact AV2.
        * rewrite MT2, AI2. (* [comment removed for export] *)
          destruct (lo_zero_partial s1 g W1 Hg Hfr LO0) as [PART _].
          apply (full_ai_lo s1 nx W1 Gnx FR2).
          pose proof (wg_ai s1 L nx (wG_each s1 L (WF_groups s1 L W1) nx Gnx)) as AX.
          destruct (Z.lt_ge_cases (s_ai s1 nx) (g_lastidx s1 nx)) as [LT|GE]; [|lia]. exfalso.
          apply NEg. symmetry. apply (wG_onepartial s1 L (WF_groups s1 L W1) g nx Hg Gnx PART LT). rewrite Hgsc, Snx. reflexivity.
        * exact E10.
    - destruct (aAct0a Mc g (g_mem s1 g) b (mr_freed (s_meta s1 g)) ltac:(unfold HEAPLO in *; lia) Hmemg Hb FRR Rme Rb r rom A10 A13 A14
                  ltac:(rewrite ELO; exact LONZ)) as (r' & RUN & E10 & K').
      eapply kat_msteps; [exact Hh1 | exact Hlz1 | exact RUN |].
      apply (L_chk s1 Mc mdl1 r' g); try assumption.
      apply (pt_regs s1 Mc mdl1 r r' P); try (kept_rw K'; reflexivity). eapply keeps_big; [exact KB | exact K' | reflexivity].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma L_A5 : forall s1 Mc mdl1 r g rest,
    pt s1 Mc mdl1 r -> nojunk s1 -> s_limbo s1 = s_limbo st ->
    s_alist s1 sc = g :: rest -> mr_avail (s_meta s1 g) = 0 -> mr_freed (s_meta s1 g) <> 0 ->
    getr r 10 = Z_to_bv 64 g ->
    kat RSEGS (mkCfg (mkst r (0x62d08%bv : word) Mc rom) mdl1) Q.
  Proof using HQ Hsp Rra R2 Hreq Hsc req.
    intros s1 Mc mdl1 r g rest P NJ1 EL Hl Hav0 Hfr A10.
    pose proof P as [W1 RP1 LG1 Hh1 Hlz1 Hmat1 Hfs1 Hfds1 Hlim1 Hcan1 Herr1 BL1 LM1 MU1 FR1 DF1 SK1 Q2 Q8 Q20 Q21 Q22 Q23 KB].
    destruct (member_facts s1 g W1 ltac:(rewrite Hl; left; reflexivity)) as (Hg & Hgsc & Ug & _).
    pose proof (wG_each s1 L (WF_groups s1 L W1) g Hg) as WG.
    pose proof (wg_frr s1 L g WG) as FRR. pose proof (wg_Wr s1 L g WG) as WR.
    destruct (G_meta_cells s1 L Mc W1 RP1 g Hg) as (ar1 & k1 & _ & _ & _ & _ & Rlo & Rhi & G8 & RM1 & _ & _).
    destruct RM1 as [_ Rnx Rme Rav Rfr RW].
    assert (WF32 : Z.land (g_W s1 g) 32 = 32).
    { rewrite (land_32_freeable (g_W s1 g)) by lia. pose proof (wg_freeable s1 L g WG) as F. unfold w_freeable in F. rewrite F. reflexivity. }
    destruct (Z.eq_dec (mr_freed (s_meta s1 g)) (all_mask_of (g_W s1 g))) as [ALL|NALL].
    - (* [comment removed for export] *)
      destruct (next_of_head s1 g rest W1 Hl) as (SELF & IN & NE).
      destruct (member_facts s1 (mr_next (s_meta s1 g)) W1 ltac:(rewrite Hl; exact IN)) as (Gnx & Snx & Unx & Xlo & Xhi).
      destruct (G_meta_cells s1 L Mc W1 RP1 _ Gnx) as (ar2 & k2 & _ & _ & _ & _ & _ & _ & _ & RM2 & _ & _).
      pose proof (rm_freed Mc _ _ RM2) as Rfr2.
      pose proof (wg_frr s1 L _ (wG_each s1 L (WF_groups s1 L W1) _ Gnx)) as FRR2.
      pose proof (ctx_store_ok s1 Mc RP1) as SOKc.
      assert (SOKa : store_ok RSEGS Mc (Z_to_bv 64 (ctx_active sc)) 8%nat = true) by (unfold ctx_active, CTX in *; sok 928%nat SOKc).
      destruct (aSkipY Mc sc g (mr_freed (s_meta s1 g)) (g_W s1 g) (mr_next (s_meta s1 g)) (mr_freed (s_meta s1 (mr_next (s_meta s1 g))))
                  Hsc ltac:(unfold HEAPLO in *; lia) ltac:(unfold HEAPLO in *; lia) FRR FRR2 WR WF32 Rfr RW Rnx Rfr2 SOKa
                  r rom A10 Q21 ALL ltac:(unfold CTX_END, CTX, HEAPLO in *; lia)) as (r' & RUN & E10 & E13 & E14 & K').
      eapply kat_msteps; [exact Hh1 | exact Hlz1 | exact RUN |].
      destruct (rot_close s1 Mc mdl1 r g rest r' _ P Hl Hav0 Hfr
                  ltac:(kept_rw K'; reflexivity) ltac:(kept_rw K'; reflexivity) ltac:(kept_rw K'; reflexivity)
                  ltac:(kept_rw K'; reflexivity) ltac:(kept_rw K'; reflexivity) ltac:(kept_rw K'; reflexivity) K' eq_refl)
        as (P2 & AL2 & SL2 & MT2 & GR2' & AI2 & LB2 & KD2 & HD2 & _ & _ & _ & AV2 & FR2 & _ & _).
      set (s2 := MhRotate.st' s1 sc g rest) in *. set (nx := mr_next (s_meta s1 g)) in *.
      destruct (rest ++ [g]) as [|h2 rest2] eqn:EL2; [destruct rest; discriminate EL2|]. cbn in HD2. subst h2.
      apply (L_A6 s2 _ mdl1 r' nx rest2 P2).
      + intros x k o Hx Hk E. rewrite SL2 in E. exact (NJ1 x k o Hx Hk E).
      + rewrite LB2. exact EL.
      + exact AL2.
      + rewrite MT2. exact AV2.
      + rewrite MT2. exact FR2.
      + exact E10.
      + rewrite MT2. exact E13.
      + exact E14.
    - destruct (aSkipN Mc g (mr_freed (s_meta s1 g)) (g_W s1 g) ltac:(unfold HEAPLO in *; lia) FRR WR WF32 Rfr RW r rom A10 NALL)
        as (r' & RUN & E10 & E13 & E14 & K').
      eapply kat_msteps; [exact Hh1 | exact Hlz1 | exact RUN |].
      apply (L_A6 s1 Mc mdl1 r' g rest); try assumption.
      apply (pt_regs s1 Mc mdl1 r r' P); try (kept_rw K'; reflexivity). eapply keeps_big; [exact KB | exact K' | reflexivity].
  Qed.
End ASA.
