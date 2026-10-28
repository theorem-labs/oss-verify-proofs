(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep SFModel.
From OssFuzzTheorems.openssl.pem.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import F_malloc_free F_malloc_fast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocKit_A.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RF_get_meta RF_realloc_head.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Module DJ.
  Import Ltac2.
  Ltac2 prune_reld () : unit :=
    let bad := SF2.bad_heads () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then SF2.clean bad ty else SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_reld1 () : unit := Control.enter prune_reld.
End DJ.
Local Ltac dj_prune := ltac2:(DJ.prune_reld1 ()).
Local Ltac dj_one := first [ Zify.zify; xlia zchecker | sf_unhide; dj_prune; Zify.zify; xlia zchecker | tlia ].
Local Ltac tslia ::= first [ exact I | repeat lazymatch goal with |- _ /\ _ => split end; first [ exact I | dj_one ] ].
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma rknown_read4 : forall st m rid r o v,
  rmrep st m -> (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= o -> o + 4 <= round_up_pg (r_len r) -> 0 <= v < 2^32 ->
  cell_read (get_shadow st rid) o = Known (Z.land (Z.shiftr v 0) 255) ->
  cell_read (get_shadow st rid) (o + 1) = Known (Z.land (Z.shiftr v 8) 255) ->
  cell_read (get_shadow st rid) (o + 2) = Known (Z.land (Z.shiftr v 16) 255) ->
  cell_read (get_shadow st rid) (o + 3) = Known (Z.land (Z.shiftr v 24) 255) ->
  ov_read_bytes usegs m (wa (r_base r + o)) 4 = Some (le4 (wz v)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st m rid r o v MR Hr Hk Ho Ho4 Hv H0 H1 H2 H3.
  pose proof MR as (WF & _ & _ & _ & _ & SH). destruct (SH rid r Hr Hk) as [HW HB].
  destruct (HB o _ ltac:(lia) H0) as [B0 _]. destruct (HB (o + 1) _ ltac:(lia) H1) as [B1 _].
  destruct (HB (o + 2) _ ltac:(lia) H2) as [B2 _]. destruct (HB (o + 3) _ ltac:(lia) H3) as [B3 _].
  assert (B : bytes_at usegs m (r_base r + o) (le4 (wz v))).
  { rewrite le4_bytes by lia.
    change [b8 (v mod 256); b8 (v / 256 mod 256); b8 (v / 65536 mod 256); b8 (v / 16777216)]
      with ([b8 (v mod 256)] ++ [b8 (v / 256 mod 256)] ++ [b8 (v / 65536 mod 256)] ++ [b8 (v / 16777216)]).
    rewrite Z.shiftr_0_r in B0. change 255 with (Z.ones 8) in B0, B1, B2, B3. rewrite Z.land_ones in B0, B1, B2, B3 by lia.
    rewrite !Z.shiftr_div_pow2 in B1, B2, B3 by lia. change (2 ^ 8) with 256 in *. change (2 ^ 16) with 65536 in *. change (2 ^ 24) with 16777216 in *.
    replace (v / 16777216 mod 256) with (v / 16777216) in B3 by (symmetry; apply Z.mod_small; Z.div_mod_to_equations; lia).
    apply bytes_at_app. split; [exact B0|]. cbn [length Z.of_nat Pos.of_succ_nat].
    apply bytes_at_app. split; [replace (r_base r + o + 1) with (r_base r + (o + 1)) by lia; exact B1|]. cbn [length Z.of_nat Pos.of_succ_nat].
    apply bytes_at_app. split; [replace (r_base r + o + 1 + 1) with (r_base r + (o + 2)) by lia; exact B2|]. cbn [length Z.of_nat Pos.of_succ_nat].
    replace (r_base r + o + 1 + 1 + 1) with (r_base r + (o + 3)) by lia. exact B3. }
  rewrite <- (Z.add_0_r (r_base r + o)). rewrite (bytes_at_read usegs m _ _ 0 4 B) by (rewrite ?length_le4; cbn; lia).
  cbn [Z.to_nat skipn]. rewrite firstn_all2 by (rewrite length_le4; cbn; lia). reflexivity.
Qed.

Lemma rrealloc_head_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    st (p : aptr) r g gh ar (b3 lo hi res : Z),
  let sh := get_shadow st (fst p) in
  let po := snd p in
  let off16 := lo + 256 * hi in
  let idx := Z.land b3 31 in
  let base := aadd p (- (UNIT * off16) - UNIT) in
  let mr := get_meta_rec st g in
  let stride := get_stride mr in
  let eo := snd base + UNIT + stride * idx + stride - IB in
  rmrep st m -> mem_inv usegs m ->
  (s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
  bv_unsigned a0 = r_base r + po -> po mod 16 = 0 ->
  16 <= po -> 16 * off16 + 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
  cell_read sh (po - 4) = Known 0 -> cell_read sh (po - 3) = Known b3 ->
  cell_read sh (po - 2) = Known lo -> cell_read sh (po - 1) = Known hi ->
  (s_groups st) !! base = Some gh -> g_meta gh = Some g -> meta_slot st g -> 0 <= snd g ->
  m_mem mr = Some base ->
  (s_areas st) !! (area_of g) = Some ar -> a_check ar = c_secret (ctx st) -> c_init_done (ctx st) <> 0 ->
  0 <= m_avail mr < 2^32 -> 0 <= m_freed mr < 2^32 -> 0 <= c_secret (ctx st) < 2^64 ->
  0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
  idx <= m_last_idx mr -> Z.testbit (m_avail mr) idx = false -> Z.testbit (m_freed mr) idx = false ->
  (m_sizeclass mr < 48 -> size_class (m_sizeclass mr) * idx <= off16 < size_class (m_sizeclass mr) * (idx + 1)) ->
  (48 <= m_sizeclass mr -> m_sizeclass mr = 63) ->
  (m_maplen mr <> 0 -> off16 <= m_maplen mr * 256 - 1) ->
  (m_maplen mr = 0 \/ m_last_idx mr <> 0 -> m_sizeclass mr < 48) ->
  UNIT <= stride -> po <= eo -> eo + 4 <= round_up_pg (r_len r) ->
  0 <= res <= eo - po -> res < 2^32 -> b3 = idx + 32 * Z.min res 5 ->
  (5 <= res -> cell_read sh (eo - 4) = Known (Z.land (Z.shiftr res 0) 255) /\ cell_read sh (eo - 4 + 1) = Known (Z.land (Z.shiftr res 8) 255)
               /\ cell_read sh (eo - 4 + 2) = Known (Z.land (Z.shiftr res 16) 255) /\ cell_read sh (eo - 4 + 3) = Known (Z.land (Z.shiftr res 24) 255)
               /\ cell_read sh (eo - 5) = Known 0) ->
  cell_read sh (eo - res) = Known 0 -> cell_read sh eo = Known 0 ->
  evt usegs (rrh_post ra sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 F fc m (conc st g) (conc st base) (m_sizeclass mr) (meta_word mr)
               (r_base r + eo) (r_base r + po) res)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b2768) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until res. intros sh po off16 idx base mr stride eo MR MI Hr Hk HP AL P16 PLO PHI C4 C3 C2 C1 Hgh Hg MS G0 Hmem Har Hchk INIT
         AV FR SE LI FB SC ML Hidx Hav Hfr Hsc Hsc63 Hml Hst S16 PE EHI RES R32 EB3 FOOT CAN CEND.
  pose proof MR as (WF & CX & GL & AR & GR & SH).
  destruct WF as (Hres & WR & DISJ & WA & WG).
  destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & _). unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in BC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  (* [comment removed for export] *)
  destruct (rmrep_shadow_read st m (fst p) r (po - 4) 0 MR Hr Hk ltac:(lia) C4) as [R4 _].
  destruct (rmrep_shadow_read st m (fst p) r (po - 3) b3 MR Hr Hk ltac:(lia) C3) as [R3 B3].
  destruct (rmrep_shadow_read2 st m (fst p) r (po - 2) lo hi MR Hr Hk ltac:(lia) ltac:(lia) C2 ltac:(replace (po - 2 + 1) with (po - 1) by lia; exact C1)) as (R2 & LO & HI).
  rewrite <- le2_lohi in R2 by lia.
  (* [comment removed for export] *)
  destruct (rmrep_group_read st m base gh MR Hgh) as [RG _]. rewrite Hg in RG. cbn [pw oconc] in RG.
  (* [comment removed for export] *)
  pose proof (rmrep_meta_chunk st m g MR MS) as MM. fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.
  (* [comment removed for export] *)
  pose proof (rmrep_area_check_read st m (area_of g) ar MR Har) as RA. rewrite Hchk in RA.
  pose proof (rmrep_ctx_secret_read st m MR) as RC. rewrite (rsec_init _ _ INIT) in RC.
  rewrite <- (wz_mod64 (c_secret (ctx st) + bv_unsigned rr_secret)) in RA, RC.
  (* [comment removed for export] *)
  destruct (WG base gh Hgh) as (rb & Hrb & _ & Bb0 & _). cbn [base aadd fst] in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb.
  assert (HB : conc st base = (r_base r + po) - 16 * off16 - 16).
  { unfold base. rewrite conc_aadd by (rewrite Hr; eauto). rewrite (conc_region' st p r Hr). unfold po, UNIT. lia. }
  assert (SB : snd base = po - 16 * off16 - 16) by (unfold base, aadd, po, UNIT; cbn [snd]; lia).
  destruct MS as (a & ara & k & Ha & Hkk & Eg).
  destruct (WA a ara Ha) as (rg & Hrg & A0 & A1 & AAL & ANG & _).
  assert (HG : conc st g = r_base rg + snd a + (AREA_HDR + META_SIZE * k)).
  { rewrite Eg, conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a rg Hrg). reflexivity. }
  destruct (WR (fst a) rg Hrg) as (RB0 & RBAL & RL0 & RBC & _). unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in RBC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  assert (Hm : (r_base rg + snd a + (AREA_HDR + META_SIZE * k)) mod 4096 = AREA_HDR + META_SIZE * k).
  { unfold AREA_HDR, META_SIZE, NSLOTS in *.
    replace (r_base rg + snd a + (24 + 40 * k)) with ((24 + 40 * k) + (snd a / 4096 + r_base rg / 4096) * 4096) by (Z.div_mod_to_equations; nia).
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (HA : conc st (area_of g) = conc st g - conc st g mod 4096).
  { rewrite HG, Hm. unfold area_of. rewrite Eg. unfold aadd. cbn [fst snd]. rewrite (conc_region st (fst a) _ rg Hrg).
    replace ((snd a + (AREA_HDR + META_SIZE * k)) mod 4096) with (AREA_HDR + META_SIZE * k); [lia|].
    unfold AREA_HDR, META_SIZE, NSLOTS in *.
    replace (snd a + (24 + 40 * k)) with ((24 + 40 * k) + (snd a / 4096) * 4096) by (Z.div_mod_to_equations; nia).
    rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
  (* [comment removed for export] *)
  assert (IDX : 0 <= idx < 32). { unfold idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  assert (SI0 : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
  assert (EOR : 0 <= eo /\ eo + 4 <= round_up_pg (r_len r)) by (unfold eo, UNIT, IB in *; lia).
  destruct (rmrep_shadow_read st m (fst p) r (eo - res) 0 MR Hr Hk ltac:(lia) CAN) as [RCAN _].
  destruct (rmrep_shadow_read st m (fst p) r eo 0 MR Hr Hk ltac:(lia) CEND) as [REND _].
  assert (RSV0 : Z.shiftr b3 5 = Z.min res 5).
  { rewrite EB3, Z.shiftr_div_pow2 by lia. change (2^5) with 32. rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  assert (EE : conc st base + 16 + stride * idx + stride - 4 = r_base r + eo) by (rewrite HB; unfold eo, UNIT, IB; rewrite SB; lia).
  assert (P16' : (r_base r + po) mod 16 = 0) by (clear -BAL AL; Z.div_mod_to_equations; lia).
  assert (RSVE : (if 160 <=? b3 then res else Z.shiftr b3 5) = res) by (destruct (Z.leb_spec 160 b3); [reflexivity| rewrite RSV0, EB3 in *; lia]).
  eapply evt_mono.
  { eapply (rrealloc_head_walk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
            (r_base r + po) (conc st g) (conc st base) (conc st (area_of g)) b3 off16 (m_avail mr) (m_freed mr)
            (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) ((c_secret (ctx st) + bv_unsigned rr_secret) mod 2^64) res
            (pw st (m_prev mr)) (pw st (m_next mr)));
    try (change (if (m_last_idx mr =? 0) && negb (m_maplen mr =? 0) then m_maplen mr * 4096 - 16 else 16 * size_class (m_sizeclass mr)) with stride);
    rewrite ?EE, ?RSVE.
    - exact HP.
    - exact P16'.
    - lia.
    - lia.
    - exact HB.
    - exact HA.
    - lia.
    - lia.
    - replace (r_base r + po - 4) with (r_base r + (po - 4)) by lia. exact R4.
    - replace (r_base r + po - 3) with (r_base r + (po - 3)) by lia. exact R3.
    - replace (r_base r + po - 2) with (r_base r + (po - 2)) by lia. exact R2.
    - exact RG.
    - exact MM.
    - exact RA.
    - exact RC.
    - intros Hlt. apply rsize_classes_read; [exact MI | lia].
    - exact B3.
    - lia.
    - exact AV.
    - exact FR.
    - apply rsec_range.
    - exact LI.
    - exact FB.
    - exact SC.
    - exact ML.
    - exact Hidx.
    - exact Hav.
    - exact Hfr.
    - exact Hsc.
    - exact Hsc63.
    - exact Hml.
    - exact Hst.
    - unfold UNIT in S16. exact S16.
    - lia.
    - lia.
    - intros H160. assert (R5 : 5 <= res) by (rewrite EB3 in H160; lia).
      destruct (FOOT R5) as (F0 & F1 & F2 & F3 & F5).
      split; [rewrite RSV0; lia|]. split; [lia|]. split.
      + replace (r_base r + eo - 4) with (r_base r + (eo - 4)) by lia.
        apply (rknown_read4 st m (fst p) r (eo - 4) res MR Hr Hk); try assumption; lia.
      + replace (r_base r + eo - 5) with (r_base r + (eo - 5)) by lia.
        exact (proj1 (rmrep_shadow_read st m (fst p) r (eo - 5) 0 MR Hr Hk ltac:(lia) F5)).
    - lia.
    - replace (r_base r + eo - res) with (r_base r + (eo - res)) by lia. exact RCAN.
    - exact REND. }
  intros ms' PO. cbv zeta in PO.
  change (if (m_last_idx mr =? 0) && negb (m_maplen mr =? 0) then m_maplen mr * 4096 - 16 else 16 * size_class (m_sizeclass mr)) with stride in PO.
  rewrite EE in PO.
  rewrite RSVE in PO. exact PO.
Qed.
End WithCeiling0.
