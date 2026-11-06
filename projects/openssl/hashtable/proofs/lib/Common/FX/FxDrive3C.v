(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cfg Require Import
  ShapeAlgBase ShapeCfg NodesCfg LedgerCfg AllocCfg LazyCfg LazyAccCfg AllocLazyCfg EagerCfg CountCfg.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain FxRun FxRn
  FxLazy FxSys FxDrive FxCellFrame FxDrive3 FxDrive3N FxDrive3S.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Drive3CDefs.
Local Open Scope uint63_scope.
Variable Lim : Z.
Variable keep : list int.

Definition commit_ledger3 (L3 : fledger3) (t off nZi : int) : fledger3 :=
  FL3 (fl3 L3) (fl_all L3) (fl_ops L3 ++ [(OpCommit, (t, off, nZi))]) (fl_sub t off nZi (fl_lazy L3))
      (fl_allow L3) (fl_Ab L3) (fl_E L3 + to_Z nZi)%Z (fl_ex L3) (fl_ord L3) (fl_res L3).

(* [comment removed for export] *)
Definition ord_has (ords : list (int * int * Z)) (ta tb : int) (P : Z -> bool) : bool :=
  existsb (fun o => (fst (fst o) =? ta) && (snd (fst o) =? tb) && P (snd o)) ords.
Definition ord_covers (L3 : fledger3) (t off nZi : int) (e : fent) : bool :=
  match e with
  | (tg, og, lg) =>
      (og =? 0) && negb (tg =? t) && lazy_tag_free tg L3
      && ord_has (fl_ord L3) tg t (fun d1 => (0 <=? d1 + to_Z off)%Z)
      && ord_has (fl_ord L3) t tg (fun d2 => (to_Z off + to_Z nZi - d2 <=? to_Z lg)%Z)
  end.
Definition in_region_b (rg : region) (off nZi : int) : bool :=
  ((to_Z (rg_lo rg) <=? to_Z off) && (to_Z off + to_Z nZi <=? to_Z (rg_len rg)))%Z.

Definition commit_cover (F : fstate) (L3 : fledger3) (t off nZi : int) (rg : region) : bool :=
  match List.find (ent_covers t off nZi) (fl_maps (fl3 L3)) with
  | Some _ => true
  | None => in_region_b rg off nZi
            && match List.find (ord_covers L3 t off nZi) (fl_all L3) with Some _ => true | None => false end
  end.

Definition sys_commit3 (F : fstate) (L3 : fledger3) (n : int) (t off len : int) : option dres3 :=
  let nZi := pg_up len in
  if range_ok keep F n t off len && negb (t =? 0) then
    match iget t (f_mem F) with
    | Some rg =>
        let L3' := commit_ledger3 L3 t off nZi in
        if commit_cover F L3 t off nZi rg && pages_valid rg && acct_ok Lim L3'
        then Some (D3One (fx_commit F t (off >> 12) (Z.to_nat (to_Z (nZi >> 12)))) L3' n) else None
    | None => None
    end
  else None.
End Drive3CDefs.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma page_in_ranges_subtract_out (p : word) : forall l lo hi,
  lo <= hi -> hi < 2 ^ 64 ->
  page_in_ranges p (maps_subtract l lo hi) = true ->
  bv_unsigned p + 4096 <= lo \/ hi <= bv_unsigned p.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hle Hhi H; [discriminate H|].
  cbn [maps_subtract] in H. unfold page_in_ranges in H. rewrite existsb_app in H.
  apply orb_true_iff in H as [H|H]; [|exact (IH lo hi Hle Hhi H)].
  pose proof (u64_range a) as Ha. pose proof (u64_range sz) as Hs.
  unfold iv_subtract in H. cbv zeta in H. rewrite existsb_app in H.
  set (A := bv_unsigned a) in *. set (Z_ := bv_unsigned sz) in *.
  apply orb_true_iff in H as [H|H].
  - destruct (A <? lo) eqn:El; [|discriminate H]. apply Z.ltb_lt in El. cbn [existsb fst snd] in H.
    rewrite orb_false_r in H. apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1, H2.
    rewrite u64_lit in H2 by lia. fold A in H1, H2. unfold page_size in H2. left. lia.
  - destruct (hi <? A + Z_) eqn:Er; [|discriminate H]. apply Z.ltb_lt in Er. cbn [existsb fst snd] in H.
    rewrite orb_false_r in H. apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1, H2.
    rewrite !u64_lit in H1 by lia. right. lia.
Qed.

(* [comment removed for export] *)
Lemma ent_sub_other t off sz e : fent_tag e <> t -> ent_sub t off sz e = [e].
Proof.
  destruct e as [[t' eo] el]. cbn [fent_tag fst]. intros Hne. unfold ent_sub.
  destruct (t' =? t)%uint63 eqn:Et; [apply Uint63.eqb_spec in Et; contradiction | reflexivity].
Qed.

Lemma ent_sub_piece t off sz e e' :
  In e' (ent_sub t off sz e) -> fent_tag e = t ->
  to_Z (snd (fst e)) + to_Z (snd e) < 2 ^ 63 -> to_Z off + to_Z sz < 2 ^ 63 -> 0 < to_Z (snd e) ->
  fent_tag e' = t /\ 0 < to_Z (snd e')
  /\ to_Z (snd (fst e)) <= to_Z (snd (fst e'))
  /\ to_Z (snd (fst e')) + to_Z (snd e') <= to_Z (snd (fst e)) + to_Z (snd e)
  /\ (to_Z (snd (fst e')) + to_Z (snd e') <= to_Z off \/ to_Z off + to_Z sz <= to_Z (snd (fst e'))).
Proof.
  destruct e as [[t' eo] el]. cbn [fst snd fent_tag]. intros Hin -> Hb1 Hb2 Hpos. unfold ent_sub in Hin.
  pose proof (i63_range eo) as Heo. pose proof (i63_range el) as Hel.
  pose proof (i63_range off) as Hoff. pose proof (i63_range sz) as Hsz.
  rewrite Uint63.eqb_refl in Hin. cbn [negb] in Hin.
  assert (Eadd1 : to_Z (eo + el)%uint63 = to_Z eo + to_Z el).
  { rewrite add_spec. apply Z.mod_small. change wB with (2 ^ 63). lia. }
  assert (Eadd2 : to_Z (off + sz)%uint63 = to_Z off + to_Z sz).
  { rewrite add_spec. apply Z.mod_small. change wB with (2 ^ 63). lia. }
  apply in_app_iff in Hin as [Hin|Hin].
  - destruct (eo <? off)%uint63 eqn:E1; [|destruct Hin]. apply ltb_spec in E1.
    destruct Hin as [<- | []]. cbn [fst snd fent_tag].
    assert (Esub : to_Z (off - eo)%uint63 = to_Z off - to_Z eo).
    { rewrite sub_spec. apply Z.mod_small. change wB with (2 ^ 63). lia. }
    destruct (el <? off - eo)%uint63 eqn:E2.
    + apply ltb_spec in E2. rewrite Esub in E2. repeat split; lia.
    + apply Bool.not_true_iff_false in E2. rewrite ltb_spec, Esub in E2. rewrite Esub. repeat split; lia.
  - destruct (off + sz <? eo + el)%uint63 eqn:E1; [|destruct Hin]. apply ltb_spec in E1.
    rewrite Eadd1, Eadd2 in E1. destruct Hin as [<- | []]. cbn [fst snd fent_tag].
    destruct (eo <? off + sz)%uint63 eqn:E2.
    + apply ltb_spec in E2. rewrite Eadd2 in E2.
      assert (Esub : to_Z (eo + el - (off + sz))%uint63 = to_Z eo + to_Z el - (to_Z off + to_Z sz)).
      { rewrite sub_spec, Eadd1, Eadd2. apply Z.mod_small. change wB with (2 ^ 63). lia. }
      rewrite Esub, Eadd2. repeat split; lia.
    + apply Bool.not_true_iff_false in E2. rewrite ltb_spec, Eadd2 in E2.
      assert (Esub : to_Z (eo + el - eo)%uint63 = to_Z el).
      { rewrite sub_spec, Eadd1. replace (to_Z eo + to_Z el - to_Z eo) with (to_Z el) by lia.
        apply Z.mod_small. change wB with (2 ^ 63). lia. }
      rewrite Esub. repeat split; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Drive3C.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.
Variable IM : fimage.
Variable code : itrie finstr.
Hypothesis Hcode : code_ok segs code.
Hypothesis Halloc : sc_alloc cfg = false.
Variable R0 : list (word * word).
Variable Rb Rc Lim : Z.
Hypothesis HRb : live_bytes R0 <= Rb.
Hypothesis HRc : Z.of_nat (length R0) <= Rc.
Variable keep : list int.
Variable mem0 : word -> option byte.
Variable XI : (int -> word) -> Model -> Prop.
Variable xtags : list int.
Hypothesis XI_rho : forall rho rho' m, (forall t, In t xtags -> rho' t = rho t) -> XI rho m -> XI rho' m.
Hypothesis XI_vm : forall rho m m', same_but_vm m m' -> XI rho m -> XI rho m'.
Variable fr0 : bvmap 5 word.
Variable fc0 : bv 32.
Variable rom0 : word -> option byte.
Variable hi : word -> Prop.
Variable wb0 : word.
Variable na0 lz0 : list (word * word).
Variable brk0 : word.
(* [comment removed for export] *)
Variable A0 : list (Z * Z).

Local Abbreviation DI := (DInv cfg segs IM R0 BIG RTgt keep mem0 XI xtags).
Local Abbreviation D3 := (DInv3 cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).
Local Abbreviation NE := (node_ext cfg segs IM R0 BIG RTgt keep mem0 XI xtags).
Local Abbreviation Rn := (FxRn.Rn segs IM).
Local Abbreviation erase := (FxDrive3.erase wb0).
Local Abbreviation SOK := (sys_ok3 cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).

(* [comment removed for export] *)
Lemma commit_model_facts a nZ m :
  vm_maps (m_vmmaps (mmap_commit_model a nZ m)) = vm_maps (m_vmmaps m)
  /\ vm_noaccess (m_vmmaps (mmap_commit_model a nZ m))
     = maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned (Z_to_bv 64 nZ))
  /\ m_vm_lazy (mmap_commit_model a nZ m)
     = maps_subtract (m_vm_lazy m) (bv_unsigned a) (bv_unsigned a + nZ)
  /\ m_vm_materialized (mmap_commit_model a nZ m)
     = List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + nZ)) (m_vm_materialized m)
  /\ vm_limit (m_vmmaps (mmap_commit_model a nZ m)) = vm_limit (m_vmmaps m)
  /\ vm_brk (m_vmmaps (mmap_commit_model a nZ m)) = vm_brk (m_vmmaps m)
  /\ vm_start_brk (m_vmmaps (mmap_commit_model a nZ m)) = vm_start_brk (m_vmmaps m)
  /\ vm_mmap_base (m_vmmaps (mmap_commit_model a nZ m)) = vm_mmap_base (m_vmmaps m)
  /\ erase (mmap_commit_model a nZ m) = erase m.
Proof. destruct m as [fd [maps lazy mat] io fs proc lim tm]; repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma commit_core n rho F L3 ms m t off len rg ec eo el :
  D3 n rho F L3 ms m -> at_ecall F ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  bv_unsigned (ms_reg ms 17) = 222 ->
  ms_gpr (ms_pend ms) 0 = adr rho t (to_Z off) ->
  bv_unsigned (ms_gpr (ms_pend ms) 1) = to_Z len ->
  bv_unsigned (ms_gpr (ms_pend ms) 2) = 3 ->
  bv_unsigned (ms_gpr (ms_pend ms) 3) = 50 ->
  bv_unsigned (ms_gpr (ms_pend ms) 5) = 0 ->
  range_ok keep F n t off len = true -> t <> 0%uint63 -> iget t (f_mem F) = Some rg ->
  pages_valid rg = true -> acct_ok Lim (commit_ledger3 L3 t off (pg_up len)) = true ->
  to_Z (rg_lo rg) <= to_Z eo -> to_Z eo <= to_Z off ->
  to_Z off + page_round_up_Z (to_Z len) <= to_Z eo + to_Z el -> to_Z eo + to_Z el <= to_Z (rg_len rg) ->
  In ec (fl_all L3) ->
  e_lo (den rho ec) <= bv_unsigned (rho t) + to_Z off ->
  bv_unsigned (rho t) + to_Z off + page_round_up_Z (to_Z len) <= e_hi (den rho ec) ->
  (forall e0, In e0 (fl_lazy L3) -> fent_tag e0 <> t -> fent_tag e0 <> fent_tag ec) ->
  SOK n rho F L3 (D3One (fx_commit F t (off >> 12)%uint63 (Z.to_nat (to_Z (pg_up len >> 12)%uint63)))
                        (commit_ledger3 L3 t off (pg_up len)) n) ms m.
Proof.
  intros (HDI & HL & HS & HX) Hat Hstep Hx8 Ha0 Ha1 Ha2 Ha3 Ha5 Hrange Ht0 Hg0 Hpv Hacct He1 He2 He3 He4
         HecAll Hqlo0 Hqhi0 Hectag.
  pose proof HDI as (HRn & H0 & Hh & Hnl & Hli & Hcov & Hmir & Hbud & HXI & Hxt & Hfr).
  change (m_halted (erase m)) with (m_halted m) in Hh.
  destruct (range_facts_of R0 keep mem0 rho F n t off len Hrange) as [rg1 RF].
  destruct RF as [rf_get0 rf_lt0 rf_keep0 rf_len0 rf_nZ0 rf_sum0 rf_add0 rf_pn0 rf_k0 rf_kpos0 rf_al0 rf_offal0].
  rewrite Hg0 in rf_get0. injection rf_get0 as <-. pose proof Hg0 as rf_get0.
  set (nZi := pg_up len) in *. set (nZ := page_round_up_Z (to_Z len)) in *.
  set (pn := (off >> 12)%uint63) in *. set (k := Z.to_nat (to_Z (nZi >> 12)%uint63)) in *.
  assert (HnZpos : 0 < nZ) by (apply page_round_up_Z_pos; lia).
  pose proof (Rn_R _ _ _ _ _ _ HRn H0) as HR.
  pose proof (R_regions_sep _ _ _ _ _ HR) as Hsep.
  assert (Hregs : forall t' rg', iget t' (f_mem F) = Some rg' -> region_ok rho t' rg')
    by (intros t' rg' Hg'; exact (R_region_ok _ _ _ _ _ _ _ HR Hg')).
  assert (Hl62 : forall t' rg', iget t' (f_mem F) = Some rg' -> to_Z (rg_len rg') <= 2 ^ 62).
  { intros t' rg' Hg'. exact (proj1 (proj2 (Hregs t' rg' Hg'))). }
  destruct Hmir as (Hm1 & _ & _).
  change (vm_maps (m_vmmaps (erase m))) with (vm_maps (m_vmmaps m)) in Hm1.
  destruct (range_addr segs IM R0 rho F ms t off nZ eo el rg HR rf_get0 rf_al0 rf_offal0 He1 He2 HnZpos He3 He4)
    as (Hau & Hamod & Ha63 & _ & _).
  set (addr := adr rho t (to_Z off)) in *. set (q := den rho ec) in *.
  assert (HqIn : In q (vm_maps (m_vmmaps m))).
  { rewrite (lp_maps _ _ _ _ _ _ _ _ _ _ _ HL). apply in_map. exact HecAll. }

  pose proof (i63_range off) as Hoff0. pose proof (i63_range eo) as Heo0. pose proof (i63_range el) as Hel0.
  assert (HnZw : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply u64_lit; lia).
  set (lo := bv_unsigned addr) in *. set (hi' := lo + nZ).
  assert (Hqlo : e_lo q <= lo) by (rewrite Hau; exact Hqlo0).
  assert (Hqhi : hi' <= e_hi q) by (unfold hi'; rewrite Hau; lia).
  (* [comment removed for export] *)
  change (m_vmmaps (erase m)) with (erase_vm wb0 (m_vmmaps m)) in Hli.
  pose proof (li_disj _ _ _ _ _ Hli) as Hpw0. pose proof (li_top _ _ _ _ _ Hli) as Htopm.
  pose proof (li_disj_R _ _ _ _ _ Hli) as HdR. pose proof (li_reserved _ _ _ _ _ Hli) as HresR.
  change (vm_maps (erase_vm wb0 (m_vmmaps m))) with (vm_maps (m_vmmaps m)) in Hpw0, Htopm, HdR.
  change (alloc_top (erase_vm wb0 (m_vmmaps m))) with (alloc_top (m_vmmaps m)) in Htopm.
  change (vm_reserved (erase_vm wb0 (m_vmmaps m))) with (vm_reserved (m_vmmaps m)) in HresR.
  pose proof (alloc_top_lt (m_vmmaps m)) as Hattop. unfold two_pow_64 in Hattop.
  pose proof (proj1 (Forall_forall _ _) Htopm q HqIn) as [Hq0 Hqtop].
  assert (Hhi64 : hi' < 2 ^ 64) by (unfold hi', lo; lia).
  assert (Hlohi : lo < hi') by (unfold hi'; lia).
  (* [comment removed for export] *)
  assert (Hargs : mmap_commit_args (ms_pend ms) m (to_Z len)).
  { unfold mmap_commit_args. cbv zeta. rewrite Ha0. fold addr. fold nZ.
    split; [exact Ha1|]. split; [lia|]. split; [exact Ha2|]. split; [exact Ha3|]. split; [exact Ha5|].
    split; [exact Hamod|]. split; [unfold lo in *; lia|]. split; [unfold lo in *; lia|].
    assert (Hin : e_inside (addr, Z_to_bv 64 nZ) q).
    { unfold e_inside. split; [exact Hqlo|]. unfold e_hi at 1, e_lo at 1, e_sz at 1. cbn [fst snd]. rewrite HnZw. fold lo. exact Hqhi. }
    split.
    - rewrite HresR. apply region_free_iff. apply Forall_forall. intros r Hr.
      pose proof (proj1 (Forall_forall _ _) (proj1 (Forall_forall _ _) HdR q HqIn) r Hr) as Hd.
      apply e_disj_sym. eapply e_disj_inside; [apply e_disj_sym; exact Hd | exact Hin].
    - eapply map_contains_intro; [exact HqIn | exact Hin]. }
  destruct (commit_model_facts addr nZ m) as (Fm & Fna & Flz & Fmat & Flim & Fbrk & Fsb & Fmb & Fer).
  set (m' := mmap_commit_model addr nZ m) in *. rewrite HnZw in Fna. fold lo hi' in Fna, Flz, Fmat.
  destruct HL as [Hpi Hreg Hpw Hml Hsub HAb Hlim Hex Hexna Hexlz H9a H9b Htags HE Hacc Hwfna Hwflz HopsR Hord Hopsf Hres].
  apply Z.leb_le in Hacct. unfold acct_ok in Hacct. cbn [commit_ledger3 fl_E fl_Ab] in Hacct.
  fold nZi in Hacct. rewrite rf_nZ0 in Hacct. fold nZ in Hacct.
  (* [comment removed for export] *)
  assert (HE' : eager_used m' <= fl_E L3 + nZ).
  { rewrite (Cnt.eager_used_eu m'), Fm, Fna, Flz. rewrite (Cnt.eager_used_eu m) in HE.
    assert (Hwfm : Cnt.ivs_wf (vm_maps (m_vmmaps m))).
    { apply Cnt.ivs_wf_Forall. eapply Forall_impl; [|exact Htopm]. intros p [_ Hp]. lia. }
    pose proof (Cnt.eu_commit_le (vm_maps (m_vmmaps m)) (vm_noaccess (m_vmmaps m)) (m_vm_lazy m) q lo hi'
                  Hwfm (proj2 (Cnt.ivs_wf_Forall _) Hwfna) (proj2 (Cnt.ivs_wf_Forall _) Hwflz) Hpw0 HqIn Hlohi
                  Hqlo Hqhi) as H1.
    unfold hi' in H1 at 3. lia. }
  assert (Hpi' : page_inv (allowed A0 rho L3) m').
  { destruct Hpi as [P1 P2 P3 P4]. constructor; rewrite ?Fmat.
    - apply List.NoDup_filter. exact P1.
    - apply Forall_forall. intros p Hp. apply List.filter_In in Hp as [Hp _]. exact (proj1 (Forall_forall _ _) P2 p Hp).
    - apply Forall_forall. intros p Hp. apply List.filter_In in Hp as [Hp _]. exact (proj1 (Forall_forall _ _) P3 p Hp).
    - rewrite Flim. clear - HE' HAb Hacct Hlim. lia. }   (* [comment removed for export] *)
  assert (Hbudget : vm_backing_within_limit m' = true).
  { unfold vm_backing_within_limit. apply Z.leb_le.
    pose proof (page_inv_lazy_inv _ _ Hpi') as Hu. unfold lazy_inv in Hu. rewrite Flim.
    clear - Hu HE' HAb Hacct Hlim. lia. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof (mmap_commit_step_iff_lz cfg segs (ms_pend ms) _ m (to_Z len) Halloc Hh
                (ms_pend_svc ms) Hx8 Hargs) as Hiff. cbv zeta in Hiff. rewrite Ha0 in Hiff. fold addr nZ m' in Hiff.
  specialize (Hiff Hbudget).
  set (ms' := sysret (ms_pend ms) addr (apply_zeros (ms_mem (ms_pend ms)) [(addr, Z_to_bv 64 nZ)])) in *.
  exists unit, tt, (fun _ => mkCfg ms' m').
  split.
  { intros e st. rewrite Hiff. split.
    - intros [-> ->]. exists tt. split; reflexivity.
    - intros (_ & -> & ->). split; reflexivity. }
  intros _. cbn [cfg_ms cfg_model].
  pose proof (i63_range pn) as Hpn0.
  pose proof (fx_commit_sound segs IM n rho F ms t rg pn k HRn Hat rf_get0 rf_lt0 rf_kpos0
                ltac:(lia) ltac:(lia) ltac:(lia)) as HRn'.
  rewrite rf_pn0, rf_k0 in HRn'. fold addr in HRn'.
  change (ms_mem ms) with (ms_mem (ms_pend ms)) in HRn'. fold ms' in HRn'.
  set (F' := fx_commit F t pn k) in *.
  set (L3' := commit_ledger3 L3 t off nZi).
  exists F', L3', n, rho. split; [reflexivity|].
  (* [comment removed for export] *)
  assert (Hmemout : forall x, ~ (lo <= bv_unsigned x < hi') -> ms_mem ms' x = ms_mem ms x).
  { intros x Hx. unfold ms'. rewrite sysret_mem, apply_zeros_one, HnZw. fold lo hi'.
    replace ((lo <=? bv_unsigned x) && (bv_unsigned x <? hi')) with false; [reflexivity|].
    symmetry. apply not_true_iff_false. intros Hb. apply andb_true_iff in Hb as [B1 B2].
    apply Z.leb_le in B1. apply Z.ltb_lt in B2. apply Hx. lia. }
  assert (Hin_rg : forall x, lo <= x < hi' -> in_ival rho t rg x).
  { intros x Hx. unfold in_ival, hi', lo in *. rewrite Hau in Hx. lia. }
  assert (Hshape : same_shape (f_mem F) (f_mem F')).
  { apply upd_region_shape. intros r. cbn. repeat split; reflexivity. }
  assert (Hother : forall t', t' <> t -> iget t' (f_mem F') = iget t' (f_mem F)).
  { intros t' Hne. cbn [F' fx_commit fx_sysret f_mem]. rewrite upd_region_get.
    destruct (t' =? t)%uint63 eqn:E; [apply Uint63.eqb_spec in E; contradiction | reflexivity]. }
  assert (Hgt' : iget t (f_mem F') = Some (RGK (rg_lo rg) (rg_len rg) (rg_align rg) (rg_dflt rg)
                                             (zero_pages k pn (rg_pages rg)) (rg_clo rg) (rg_chi rg) (rg_kind rg))).
  { cbn [F' fx_commit fx_sysret f_mem]. rewrite upd_region_get, Uint63.eqb_refl, rf_get0. reflexivity. }
  (* [comment removed for export] *)
  assert (HDI' : DI n rho F' (fl3 L3) ms' (erase m')).
  { rewrite Fer.
    pose proof (DInv_repage cfg segs IM R0 BIG RTgt keep mem0 XI xtags XI_vm n rho F (fl3 L3) ms (erase m)
                  F' (fl_na (fl3 L3)) ms' (erase m) t rg HDI rf_get0 rf_keep0 HRn' Hshape Hother) as HDr.
    assert (Ena : fl_na (fl3 L3) = []).
    { destruct (fl_na (fl3 L3)) as [|e0 l0] eqn:E; [reflexivity|]. exfalso.
      destruct HDI as (_ & _ & _ & _ & _ & _ & (_ & Hm2 & _) & _). rewrite E in Hm2.
      pose proof (Forall_inv Hm2) as Hok. destruct e0 as [[t0 o0] l00]. destruct Hok as (_ & _ & _ & _ & Hin0).
      exact Hin0. }
    replace (fl3 L3) with (FL (fl_maps (fl3 L3)) (fl_na (fl3 L3)) (fl_brk (fl3 L3)) (fl_c (fl3 L3)) (fl_S (fl3 L3)))
      by (destruct (fl3 L3); reflexivity).
    apply HDr; try reflexivity; try exact I; try apply same_but_vm_refl.
    - exact Hh.
    - exact Hnl.
    - exact (proj1 (proj2 (proj2 (proj2 (proj2 HDI))))).
    - rewrite Ena. constructor.
    - intros x Hx. apply Hmemout. intros Hc. apply Hx. exact (Hin_rg _ Hc). }
  assert (Hne : NE n rho F (fl3 L3) ms (erase m) n rho F' (fl3 L3) ms' (erase m')).
  { rewrite Fer. apply (node_ext_repage cfg segs IM R0 BIG RTgt keep mem0 XI xtags n rho F (fl3 L3) ms (erase m)
                         F' (fl3 L3) ms' (erase m) t rg rf_get0 Hshape);
      try reflexivity; try apply same_but_vm_refl;
      try (unfold ms'; rewrite ?sysret_fregs, ?sysret_fcsr, ?sysret_rom; reflexivity);
      try (intros x Hx; apply Hmemout; intros Hc; apply Hx; exact (Hin_rg _ Hc));
      try (intros _ Hex0; exact Hex0). }
  (* [comment removed for export] *)
  assert (Hden : e_lo (den rho (t, off, nZi)) = lo /\ e_hi (den rho (t, off, nZi)) = hi').
  { unfold e_hi, e_lo, e_sz. cbn [den fst snd]. fold addr. rewrite rf_nZ0. fold nZ. rewrite HnZw. fold lo.
    split; reflexivity. }
  set (rg' := RGK (rg_lo rg) (rg_len rg) (rg_align rg) (rg_dflt rg) (zero_pages k pn (rg_pages rg))
                  (rg_clo rg) (rg_chi rg) (rg_kind rg)) in *.
  assert (Hk61 : to_Z pn + Z.of_nat k < 2 ^ 61) by lia.
  assert (Hpa_out : forall q', ~ (to_Z pn <= to_Z q' < to_Z pn + Z.of_nat k) -> page_at IM rg' t q' = page_at IM rg t q').
  { intros q' Hq'. unfold page_at, page_in_region. cbn [rg' rg_pages rg_dflt rg_lo rg_len].
    rewrite (iget_zero_pages k pn (rg_pages rg) q' Hk61).
    replace ((to_Z pn <=? to_Z q') && (to_Z q' <? to_Z pn + Z.of_nat k)) with false; [reflexivity|].
    symmetry. apply not_true_iff_false. intros Hb. apply andb_true_iff in Hb as [B1 B2].
    apply Z.leb_le in B1. apply Z.ltb_lt in B2. apply Hq'. lia. }
  assert (Hexp_out : forall q', ~ (to_Z pn <= to_Z q' < to_Z pn + Z.of_nat k) -> iget q' (rg_pages rg') = iget q' (rg_pages rg)).
  { intros q' Hq'. cbn [rg' rg_pages]. rewrite (iget_zero_pages k pn (rg_pages rg) q' Hk61).
    replace ((to_Z pn <=? to_Z q') && (to_Z q' <? to_Z pn + Z.of_nat k)) with false; [reflexivity|].
    symmetry. apply not_true_iff_false. intros Hb. apply andb_true_iff in Hb as [B1 B2].
    apply Z.leb_le in B1. apply Z.ltb_lt in B2. apply Hq'. lia. }
  pose proof (region_ok_nowrap rho t rg (Hregs t rg rf_get0)) as Hnwrap.
  pose proof (u64 (rho t)) as Hrt.
  assert (Haddr_in : forall q' j, to_Z pn <= to_Z q' < to_Z pn + Z.of_nat k -> 0 <= j < 4096 ->
            lo <= bv_unsigned (adr rho t (to_Z q' * 4096 + j)) < hi').
  { intros q' j Hq' Hj. rewrite adr_unsigned by lia. unfold hi'. lia. }
  split.
  2:{ (* [comment removed for export] *)
      split; [exact (dext_node _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hne Fsb Fmb)|].
      exists [(OpCommit, (t, off, nZi))]. split; [reflexivity|].
      split; [constructor; [cbn [snd fent_tag fst]; exact rf_lt0 | constructor]|].
      assert (Htouch : forall x : word, lo <= bv_unsigned x < hi' -> touched rho [(OpCommit, (t, off, nZi))] (bv_unsigned x)).
      { intros x Hx. exists (OpCommit, (t, off, nZi)). split; [left; reflexivity|]. cbn [snd].
        rewrite (proj1 Hden), (proj2 Hden). exact Hx. }
      split; [|split].
      - intros x Hnt _. apply Hmemout. intros Hc. exact (Hnt (Htouch x Hc)).
      - intros x (t1 & rg1 & pn1 & p1 & j & Hg1 & Hpn1 & Hp1 & Hw & Hj & Hjl & ->).
        destruct (t1 =? t)%uint63 eqn:E.
        + apply Uint63.eqb_spec in E. subst t1. rewrite Hgt' in Hg1. injection Hg1 as <-.
          destruct (Z_le_gt_dec (to_Z pn) (to_Z pn1)) as [H1|H1];
            [destruct (Z_lt_le_dec (to_Z pn1) (to_Z pn + Z.of_nat k)) as [H2|H2]|].
          * right. apply Htouch. apply Haddr_in; [lia | exact Hj].
          * left. rewrite Hpa_out in Hp1 by lia. exists t, rg, pn1, p1, j. repeat (split; [assumption|]). reflexivity.
          * left. rewrite Hpa_out in Hp1 by lia. exists t, rg, pn1, p1, j. repeat (split; [assumption|]). reflexivity.
        + apply eqb_false_spec in E. left. rewrite (Hother t1 E) in Hg1.
          exists t1, rg1, pn1, p1, j. repeat (split; [assumption|]). reflexivity.
      - intros x (t1 & rg1 & pn1 & p1 & ci & Hg1 & Hp1 & Hci & j & Hj & ->).
        destruct (t1 =? t)%uint63 eqn:E.
        + apply Uint63.eqb_spec in E. subst t1. rewrite rf_get0 in Hg1. injection Hg1 as <-.
          destruct (Z_le_gt_dec (to_Z pn) (to_Z pn1)) as [H1|H1];
            [destruct (Z_lt_le_dec (to_Z pn1) (to_Z pn + Z.of_nat k)) as [H2|H2]|].
          * (* [comment removed for export] *)
            right. apply Htouch.
            pose proof (proj1 (iall_spec _ _) Hpv pn1 p1 Hp1) as Hb. apply andb_true_iff in Hb as [_ Hb2].
            destruct (iget ci (pg_cells p1)) as [c|] eqn:Ec; [|congruence].
            pose proof (proj1 (iall_spec _ _) Hb2 ci c Ec) as Hb3. apply andb_true_iff in Hb3 as [Hb3 _].
            apply ltb_spec in Hb3. change (to_Z 512) with 512 in Hb3. pose proof (i63_range ci) as Hci0.
            replace (to_Z pn1 * 4096 + to_Z ci * 8 + j) with (to_Z pn1 * 4096 + (to_Z ci * 8 + j)) by lia.
            apply Haddr_in; lia.
          * left. exists t, rg', pn1, p1, ci. split; [exact Hgt'|]. rewrite Hexp_out by lia.
            split; [exact Hp1|]. split; [exact Hci|]. exists j. split; [exact Hj | reflexivity].
          * left. exists t, rg', pn1, p1, ci. split; [exact Hgt'|]. rewrite Hexp_out by lia.
            split; [exact Hp1|]. split; [exact Hci|]. exists j. split; [exact Hj | reflexivity].
        + apply eqb_false_spec in E. left. exists t1, rg1, pn1, p1, ci. rewrite (Hother t1 E).
          split; [exact Hg1|]. split; [exact Hp1|]. split; [exact Hci|]. exists j. split; [exact Hj | reflexivity]. }
  split; [exact HDI'|].
  apply Forall_app in Htags as [Ht1 Htags]. apply Forall_app in Htags as [Ht2 Ht3].
  split.
  { (* [comment removed for export] *)
    constructor; unfold FxDrive3.allowed; cbn [L3' commit_ledger3 fl3 fl_all fl_ops fl_lazy fl_allow fl_Ab fl_E fl_ex].
    - exact Hpi'.
    - (* [comment removed for export] *)
      rewrite Flz. intros t1 rg1 pn1 p1 x Hg1 Hpn1 Hp1 Hx Hxl Hlzp.
      pose proof (page_in_ranges_subtract_out _ _ lo hi' ltac:(lia) Hhi64 Hlzp) as Hout.
      pose proof (page_in_ranges_subtract _ _ lo hi' ltac:(lia) Hhi64 Hlzp) as Hlz0.
      destruct (t1 =? t)%uint63 eqn:E.
      + apply Uint63.eqb_spec in E. subst t1. rewrite Hgt' in Hg1. injection Hg1 as <-.
        destruct (Z_le_gt_dec (to_Z pn) (to_Z pn1)) as [H1|H1];
          [destruct (Z_lt_le_dec (to_Z pn1) (to_Z pn + Z.of_nat k)) as [H2|H2]|].
        * exfalso. pose proof (i63_range pn1) as Hpn10.
          set (z := bv_unsigned (rho t) + to_Z pn1 * 4096 + x) in *.
          assert (Hz : lo <= z < hi') by (unfold z, hi'; lia).
          assert (Epb : bv_unsigned (page_base_of z) = z / 4096 * 4096).
          { unfold page_base_of, page_size. apply u64_lit. pose proof (u64 addr) as Hadr0. fold lo in Hadr0.
            unfold hi' in Hz. clear - Hz Ha63 Hadr0. Z.div_mod_to_equations. lia. }
          rewrite Epb in Hout. clear - Hout Hz. Z.div_mod_to_equations. lia.
        * rewrite Hpa_out in Hp1 by lia. exact (Hreg t rg pn1 p1 x rf_get0 Hpn1 Hp1 Hx Hxl Hlz0).
        * rewrite Hpa_out in Hp1 by lia. exact (Hreg t rg pn1 p1 x rf_get0 Hpn1 Hp1 Hx Hxl Hlz0).
      + apply eqb_false_spec in E. rewrite (Hother t1 E) in Hg1.
        exact (Hreg t1 rg1 pn1 p1 x Hg1 Hpn1 Hp1 Hx Hxl Hlz0).
    - (* [comment removed for export] *)
      rewrite Flz. intros e' p He' Hp H1 H2. apply in_flat_map in He' as (e0 & He0 & Hin').
      destruct (Uint63.eqb (fent_tag e0) t) eqn:Et.
      + apply Uint63.eqb_spec in Et.
        destruct (proj1 (Forall_forall _ _) Hsub e0 He0) as (Hpe & e2 & He2' & Hw).
        assert (Hb2 : to_Z (snd (fst e0)) + to_Z (snd e0) < 2 ^ 63).
        { destruct (proj1 (Forall_forall _ _) H9b e2 He2') as [Hinm | [Et0 | Hno]];
            [| rewrite (proj1 Hw), Et in Et0; contradiction | rewrite (proj1 Hw), Et, rf_get0 in Hno; discriminate Hno].
          pose proof (proj1 (Forall_forall _ _) Hm1 e2 Hinm) as Hok. apply ent_ok_iff in Hok as [Hine _].
          destruct e2 as [[t2 o2] l2]. destruct Hine as (rg2 & Hg2 & _ & Hb). pose proof (Hl62 _ _ Hg2).
          destruct Hw as (_ & _ & Hw2). cbn [fst snd] in Hw2. lia. }
        destruct (ent_sub_piece t off nZi e0 e' Hin' Et Hb2 ltac:(rewrite rf_nZ0; fold nZ; lia) Hpe)
          as (Et' & Hpe' & Q1 & Q2 & Q3).
        destruct e0 as [[t0 o0] l0], e' as [[t1 o1] l1]. cbn [fent_tag fst snd] in *. subst t0 t1.
        pose proof (i63_range o0). pose proof (i63_range l0). pose proof (i63_range o1). pose proof (i63_range l1).
        unfold e_hi, e_lo, e_sz in H1, H2. cbn [den fst snd] in H1, H2.
        rewrite adr_unsigned in H1, H2 by lia. rewrite u64_lit in H2 by lia.
        apply page_in_ranges_subtract_keep.
        * rewrite rf_nZ0 in Q3. fold nZ in Q3. unfold hi'. rewrite Hau. destruct Q3; [left | right]; lia.
        * apply (Hpw (t, o0, l0) p He0 Hp); unfold e_hi, e_lo, e_sz; cbn [den fst snd];
            rewrite adr_unsigned by lia; rewrite ?u64_lit by lia; lia.
      + apply eqb_false_spec in Et. rewrite (ent_sub_other t off nZi e0 Et) in Hin'. destruct Hin' as [<- | []].
        apply page_in_ranges_subtract_keep; [|exact (Hpw e0 p He0 Hp H1 H2)].
        (* [comment removed for export] *)
        destruct (lazy_cov_inside rho (fl_all L3) (fl_lazy L3) (vm_maps (m_vmmaps m)) e0 Hsub Hex) as (e2 & He2' & Et2 & Hins); [|exact He0|].
        { intros p0 Hp0. pose proof (proj1 (Forall_forall _ _) Htopm p0 Hp0) as [_ Hh0]. lia. }
        assert (Hneq : den rho e2 <> q).
        { intros Eq.
          assert (E2 : e2 <> ec) by (intros ->; apply (Hectag e0 He0 Et); symmetry; exact Et2).
          pose proof Hpw0 as Hpwd. rewrite Hex in Hpwd.
          pose proof (pw_disj_map_In (den rho) _ e2 ec Hpwd He2' HecAll E2) as Hd.
          fold q in Hd. rewrite Eq in Hd. unfold e_disj in Hd. lia. }
        pose proof (pw_disj_In _ _ _ Hpw0 ltac:(rewrite Hex; apply in_map; exact He2') HqIn Hneq) as Hd.
        unfold e_disj in Hd. unfold e_inside in Hins. unfold hi' in *. rewrite Hau in *.
        destruct Hd as [Hd|Hd]; [left | right]; lia.
    - (* [comment removed for export] *)
      unfold mat_lazy. rewrite Fmat, Flz. apply Forall_forall. intros p Hp.
      apply List.filter_In in Hp as [Hp Hout].
      apply page_in_ranges_subtract_keep; [|exact (proj1 (Forall_forall _ _) Hml p Hp)].
      unfold page_outside_range in Hout. apply negb_true_iff in Hout. apply andb_false_iff in Hout.
      destruct Hpi as [_ P2 _ _]. pose proof (proj1 (Forall_forall _ _) P2 p Hp) as Hpal.
      unfold page_aligned, page_size in Hpal.
      destruct Hout as [Hout|Hout]; [left; apply Z.leb_gt in Hout | right; apply Z.ltb_ge in Hout; exact Hout].
      unfold page_size in Hamod. fold lo in Hamod. clear - Hout Hpal Hamod. Z.div_mod_to_equations. lia.
    - (* [comment removed for export] *)
      apply Forall_forall. intros e' He'. apply in_flat_map in He' as (e0 & He0 & Hin').
      destruct (proj1 (Forall_forall _ _) Hsub e0 He0) as (Hpe & e2 & He2' & Hw).
      destruct (Uint63.eqb (fent_tag e0) t) eqn:Et.
      + apply Uint63.eqb_spec in Et.
        assert (Hb2 : to_Z (snd (fst e0)) + to_Z (snd e0) < 2 ^ 63).
        { destruct (proj1 (Forall_forall _ _) H9b e2 He2') as [Hinm | [Et0 | Hno]];
            [| rewrite (proj1 Hw), Et in Et0; contradiction | rewrite (proj1 Hw), Et, rf_get0 in Hno; discriminate Hno].
          pose proof (proj1 (Forall_forall _ _) Hm1 e2 Hinm) as Hok. apply ent_ok_iff in Hok as [Hine _].
          destruct e2 as [[t2 o2] l2]. destruct Hine as (rg2 & Hg2 & _ & Hb). pose proof (Hl62 _ _ Hg2).
          destruct Hw as (_ & _ & Hw2). cbn [fst snd] in Hw2. lia. }
        destruct (ent_sub_piece t off nZi e0 e' Hin' Et Hb2 ltac:(rewrite rf_nZ0; fold nZ; lia) Hpe)
          as (Et' & Hpe' & Q1 & Q2 & _).
        split; [exact Hpe'|]. exists e2. split; [exact He2'|].
        destruct Hw as (W1 & W2 & W3). unfold ent_within. rewrite W1, Et, Et'. repeat split; lia.
      + apply eqb_false_spec in Et. rewrite (ent_sub_other t off nZi e0 Et) in Hin'. destruct Hin' as [<- | []].
        split; [exact Hpe|]. exists e2. split; [exact He2' | exact Hw].
    - exact HAb.
    - rewrite Flim. exact Hlim.
    - rewrite Fm. exact Hex.
    - rewrite Fna, Hexna, na_apply_snoc. unfold na_step. cbn [fst snd]. rewrite (proj1 Hden), (proj2 Hden). reflexivity.
    - rewrite Flz, Hexlz, lz_apply_snoc. unfold lz_step. cbn [fst snd]. rewrite (proj1 Hden), (proj2 Hden). reflexivity.
    - exact H9a.
    - eapply Forall_impl; [|exact H9b]. intros e0 [He0|[He0|He0]]; [left; exact He0 | right; left; exact He0 |].
      right; right. cbn [F' fx_commit fx_sysret f_mem]. rewrite upd_region_get.
      destruct (fent_tag e0 =? t)%uint63 eqn:E0; [|exact He0].
      apply Uint63.eqb_spec in E0. rewrite E0, rf_get0 in He0. discriminate He0.
    - rewrite !Forall_app. split; [exact Ht1|]. split; [|exact Ht3].
      rewrite map_app, Forall_app. split; [exact Ht2|]. constructor; [cbn [snd fent_tag fst]; exact rf_lt0 | constructor].
    - rewrite rf_nZ0. fold nZ. exact HE'.
    - rewrite rf_nZ0. fold nZ. exact Hacct.
    - rewrite Fna. apply Cnt.ivs_wf_Forall. apply Cnt.maps_subtract_wf; [apply Cnt.ivs_wf_Forall; exact Hwfna | lia].
    - rewrite Flz. apply Cnt.ivs_wf_Forall. apply Cnt.maps_subtract_wf; [apply Cnt.ivs_wf_Forall; exact Hwflz | lia].
    - intros o x p Ho Hp Hx. apply in_app_iff in Ho as [Ho | [<- | []]]; [exact (HopsR o x p Ho Hp Hx)|].
      cbn [snd] in Hx. rewrite (proj1 Hden), (proj2 Hden) in Hx.
      pose proof (proj1 (Forall_forall _ _) (proj1 (Forall_forall _ _) HdR q HqIn) p Hp) as Hd.
      unfold e_disj in Hd. unfold hi' in Hx, Hqhi. rewrite Hau in Hx, Hqlo, Hqhi. lia.
    - (* [comment removed for export] *) exact Hord.
    - (* [comment removed for export] *)
      assert (Etop : alloc_top (m_vmmaps m') = alloc_top (m_vmmaps m)).
      { change (alloc_top (m_vmmaps m')) with (alloc_top (m_vmmaps (erase m'))).
        change (alloc_top (m_vmmaps m)) with (alloc_top (m_vmmaps (erase m))). rewrite Fer. reflexivity. }
      rewrite Forall_app. split.
      + eapply Forall_impl; [|exact Hopsf]. intros o. apply op_ok_model. exact Etop.
      + constructor; [|constructor]. exact I.
    - (* [comment removed for export] *) exact Hres. }
  split.
  { (* [comment removed for export] *)
    destruct HS as [Hz Hcovs Hsp Hexc].
    assert (Hkinds : same_kinds (f_mem F) (f_mem F')).
    { intros t0. cbn [F' fx_commit fx_sysret f_mem]. rewrite upd_region_get.
      destruct (t0 =? t)%uint63 eqn:E; [|reflexivity]. apply Uint63.eqb_spec in E. subst t0.
      rewrite rf_get0. reflexivity. }
    constructor; cbn [L3' commit_ledger3 fl_all fl_ex].
    - intros x Hx Hno Hnex.
      pose proof (no_region_shape' rho _ _ _ Hshape Hno) as Hno0.
      destruct (Hz x Hx Hno0 Hnex) as [Z1 Z2]. unfold rview, wview in *.
      rewrite (Hmemout x); [split; assumption|].
      intros Hc. exact (Hno0 t rg rf_get0 (Hin_rg _ Hc)).
    - exact Hcovs.
    - intros t1 rg1 Hg1. destruct (same_shape_get _ _ _ _ Hshape Hg1) as (rg10 & Hg10 & _).
      exact (span_ok_shape R0 rho _ _ t1 rg10 rg1 Hshape Hkinds Hg10 Hg1 (Hsp t1 rg10 Hg10)).
    - exact Hexc. }
  exact (xpart_node _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HX Hne Fbrk).
Qed.

Lemma ord_has_sound n rho ords ta tb P :
  ord_has ords ta tb P = true -> Forall (ord_ok n rho) ords ->
  exists d, P d = true /\ bv_unsigned (rho ta) + d <= bv_unsigned (rho tb).
Proof.
  intros H Hall. unfold ord_has in H. apply existsb_exists in H as (o & Ho & Hc).
  apply andb_true_iff in Hc as [Hc HP]. apply andb_true_iff in Hc as [E1 E2].
  apply Uint63.eqb_spec in E1, E2. subst ta tb.
  destruct (proj1 (Forall_forall _ _) Hall o Ho) as (_ & _ & Hd). exists (snd o). split; [exact HP | exact Hd].
Qed.

Theorem sys_commit3_sound n rho F L3 ms m t off len res :
  sys_commit3 Lim keep F L3 n t off len = Some res ->
  D3 n rho F L3 ms m -> at_ecall F ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  bv_unsigned (ms_reg ms 17) = 222 ->
  ms_gpr (ms_pend ms) 0 = adr rho t (to_Z off) ->
  bv_unsigned (ms_gpr (ms_pend ms) 1) = to_Z len ->
  bv_unsigned (ms_gpr (ms_pend ms) 2) = 3 ->
  bv_unsigned (ms_gpr (ms_pend ms) 3) = 50 ->
  bv_unsigned (ms_gpr (ms_pend ms) 5) = 0 ->
  SOK n rho F L3 res ms m.
Proof.
  intros Hsys HD Hat Hstep Hx8 Ha0 Ha1 Ha2 Ha3 Ha5.
  unfold sys_commit3 in Hsys. cbv zeta in Hsys.
  destruct (range_ok keep F n t off len && negb (t =? 0)%uint63) eqn:Hchk; [|discriminate].
  apply andb_true_iff in Hchk as [Hrange Ht0]. apply negb_true_iff in Ht0. apply eqb_false_spec in Ht0.
  destruct (iget t (f_mem F)) as [rg|] eqn:Hg0; [|discriminate].
  match type of Hsys with (if ?c then _ else _) = _ => destruct c eqn:Hchk2; [|discriminate] end.
  apply andb_true_iff in Hchk2 as [Hchk2 Hacct]. apply andb_true_iff in Hchk2 as [Hcov Hpv]. injection Hsys as <-.
  pose proof HD as (HDI & HL & _ & _).
  pose proof HDI as (HRn & H0 & _ & _ & _ & _ & Hmir & _).
  pose proof (Rn_R _ _ _ _ _ _ HRn H0) as HR.
  destruct (range_facts_of R0 keep mem0 rho F n t off len Hrange) as [rg1 RF].
  destruct RF as [Hg1 _ _ _ HnZ Hsum _ _ _ _ _ _].
  rewrite Hg0 in Hg1. injection Hg1 as <-.
  pose proof (R_region_ok _ _ _ _ _ _ _ HR Hg0) as Hrok.
  unfold commit_cover in Hcov.
  destruct (List.find (ent_covers t off (pg_up len)) (fl_maps (fl3 L3))) as [e|] eqn:Hfind.
  - (* [comment removed for export] *)
    destruct Hmir as (Hm1 & _ & _).
    change (vm_maps (m_vmmaps (FxDrive3.erase wb0 m))) with (vm_maps (m_vmmaps m)) in Hm1.
    apply find_some in Hfind as [HeIn Hecov].
    destruct (ent_covers_sound R0 rho (f_mem F) _ t off (pg_up len) e Hecov
                (proj1 (Forall_forall _ _) Hm1 _ HeIn)
                (fun rg' Hg' => proj1 (proj2 (R_region_ok _ _ _ _ _ _ _ HR Hg'))) ltac:(rewrite HnZ; lia))
      as (eo & el & rg' & -> & Hg' & He1 & He2 & He3 & He4 & _).
    rewrite Hg0 in Hg'. injection Hg' as <-. rewrite HnZ in He3.
    destruct (ent_range R0 rho t eo el rg Hrok He1 He4) as [Elo Ehi].
    apply (commit_core n rho F L3 ms m t off len rg (t, eo, el) eo el); try assumption.
    + exact (proj1 (Forall_forall _ _) (lp_v2in _ _ _ _ _ _ _ _ _ _ _ HL) _ HeIn).
    + cbn [den]. rewrite Elo. lia.
    + cbn [den]. rewrite Ehi. lia.
    + intros e0 _ Hne. cbn [fent_tag fst]. exact Hne.
  - (* [comment removed for export] *)
    apply andb_true_iff in Hcov as [Hinr Hcov].
    destruct (List.find (ord_covers L3 t off (pg_up len)) (fl_all L3)) as [[[tg og] lg]|] eqn:Hfo; [|discriminate].
    apply find_some in Hfo as [HeAll Hoc]. cbn [ord_covers] in Hoc.
    apply andb_true_iff in Hoc as [Hoc Hf2]. apply andb_true_iff in Hoc as [Hoc Hf1].
    apply andb_true_iff in Hoc as [Hoc Hlzf]. apply andb_true_iff in Hoc as [Hog _].
    apply Uint63.eqb_spec in Hog. subst og.
    pose proof (lp_ord _ _ _ _ _ _ _ _ _ _ _ HL) as Hord.
    destruct (ord_has_sound n rho _ _ _ _ Hf1 Hord) as (d1 & P1 & F1).
    destruct (ord_has_sound n rho _ _ _ _ Hf2 Hord) as (d2 & P2 & F2).
    apply Z.leb_le in P1, P2. rewrite HnZ in P2.
    unfold in_region_b in Hinr. apply andb_true_iff in Hinr as [I1 I2]. apply Z.leb_le in I1, I2. rewrite HnZ in I2.
    pose proof (i63_range lg) as Hlg.
    assert (Elo : e_lo (den rho (tg, 0%uint63, lg)) = bv_unsigned (rho tg)).
    { unfold e_lo. cbn [den fst]. rewrite to_Z_0, adr_0. reflexivity. }
    assert (Ehi : e_hi (den rho (tg, 0%uint63, lg)) = bv_unsigned (rho tg) + to_Z lg).
    { unfold e_hi, e_sz. rewrite Elo. cbn [den snd]. rewrite u64_lit by lia. reflexivity. }
    apply (commit_core n rho F L3 ms m t off len rg (tg, 0%uint63, lg) off (pg_up len)); try assumption.
    + lia.
    + rewrite HnZ. lia.
    + rewrite HnZ. exact I2.
    + rewrite Elo. lia.
    + rewrite Ehi. lia.
    + intros e0 He0 _. cbn [fent_tag fst]. exact (lazy_tag_free_sound tg L3 e0 Hlzf He0).
Qed.

End Drive3C.
