(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OssFuzzTheorems.openssl.ct.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import F_malloc_free MallocTree MallocModel_B F_ntf_B MallocKit_B MallocKit_B3 F_am_A F_am_K F_am_C. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_ntf_A RF_am_A RF_am_K.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import CeilWin.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
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
(* [comment removed for export] *)
Module DJR.
  Import Ltac2.
  Ltac2 is_hidden (t : constr) : constr option := lazy_match! t with sf_hide ?p => Some p | _ => None end.
  Ltac2 unhide_rel () : unit :=
    let gv := SF2.vars_of [] (Control.goal ()) in
    let rm := List.map_filter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => None
      | None =>
          match is_hidden ty with
          | Some p => if SF2.meets (SF2.vars_of [] p) gv
                      then (let c := Control.hyp id in ltac1:(c |- unfold sf_hide in c) (Ltac1.of_constr c); None)
                      else Some id
          | None => None
          end
      end) (Control.hyps ()) in
    match rm with [] => () | _ :: _ => Std.clear rm end.
  Ltac2 unhide_rel1 () : unit := Control.enter unhide_rel.
End DJR.
Local Ltac dj_unhide_rel := ltac2:(DJR.unhide_rel1 ()).
Local Ltac dj_one := first [ Zify.zify; xlia zchecker | dj_unhide_rel; Zify.zify; xlia zchecker | sf_unhide; dj_prune; Zify.zify; xlia zchecker | tlia ].
Local Ltac tslia ::= first [ exact I | repeat lazymatch goal with |- _ /\ _ => split end; first [ exact I | dj_one ] ].
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma ram_carve2 : forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
    (m0 m : word -> option byte) (junk : list byte) (lo : Z) (st0 st : mstate) (p : aptr) (r : region),
  rmrep st m -> mem_inv ctusegs m -> s_regions st = s_regions st0 ->
  (s_regions st) !! (fst p) = Some r -> r_kind r <> RKGroup -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
  pgal (snd p) -> lr_lo r <= r_base r + snd p ->
  (s_areas st) !! p = None -> (forall k, 0 <= k < NSLOTS -> (s_metas st) !! (aadd p (AREA_HDR + META_SIZE * k)) = None) ->
  0 <= c_secret (ctx st) < 2^64 -> c_init_done (ctx st) <> 0 ->
  rw_cells ctusegs m (conc st p) [C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0)] ->
  rw_cells ctusegs m (conc st p + 24) [CB 4072 (zeros 4072)] ->
  rpres_except (ram_fp st0 lo (bv_unsigned sp)) m0 m -> wmono ctusegs m0 m ->
  rw_cells ctusegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
  stk ctusegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  let stC := upd_ctx (set_meta_area_tail (Some p)) st in
  let stD := set_areas (<[p := mkArea (c_secret (ctx st)) None NSLOTS]> (s_areas stC)) stC in
  evt ctusegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st0 m0
               (am_took stD (aadd p AREA_HDR) 100) (Z_to_bv 64 (conc st p + 24)))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (conc st p)) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b3ca4) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until r. intros MR MI ER0 Hr NK S0 S1 SAL SLR ANone FRESH SEC INI HDR0 REST PE0 WM0 FR ST LO LOLE stC stD.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR as (WF & (C1 & _) & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  pose proof (conc_region' st p r Hr) as Cp.
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (DR1 & _ & DR23 & DR2). unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in RBC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  pose proof (lr_lo_ge r) as LRG. pose proof (round_up_pg_ge (r_len r)) as RU.
  unfold rctx_head_cells in C1.
  unfold RCTX, RMLOCK, RSSP_GUARD, OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  (* [comment removed for export] *)
  assert (PD : conc st p + 4096 <= 0x2c2000 \/ 0x355000 <= conc st p) by lia.
  assert (PB : 0 <= conc st p /\ conc st p + 4096 <= lo) by lia.
  clear RBAL RL0 RB0 RF DR1 DR23 DR2 LRG RU Hres DJ WA WG.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 928); (conc st p, conc st p + 4096)]%Z m) as MU.
  pose proof (wmono_refl ctusegs m) as WM. unfold RCTX in MU.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(RCTX + 64, RCTX + 72)]%Z mX) as MUc; pose proof (wmono_refl ctusegs mX) as WMc end.
  unfold RCTX in MUc.
  st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRC : rmrep stC mX) end.
  { eapply (rmrep_ctx_frameW st stC _ _ _ MR MUc WMc); try reflexivity.
    - intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - left. unfold rctx_head_cells, RCTX. cbn [ctx stC upd_ctx s_ctx set_meta_area_tail c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
            c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
      unfold pw at 4. cbn [oconc]. change (conc stC p) with (conc st p). exact C1.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia. }
  clear MUc WMc.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(conc st p, conc st p + 4096)]%Z mX) as MUp; pose proof (wmono_refl ctusegs mX) as WMp end.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRC3 : rmrep stC mX) end.
  { eapply rmrep_transport_unowned; [exact MRC | exact MUp | exact WMp |].
    intros lo' hi' a [E|[]] Ha. inversion E; subst lo' hi'. eapply (rfresh_page_avoids stC _ p r a MRC); try assumption. }
  clear MUp WMp MRC.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRD : rmrep stD mX) end.
  { unfold stD. eapply (rmrep_new_area stC _ p r (c_secret (ctx st))); try first [exact MRC3 | exact Hr | exact NK | exact S0 | exact S1 | exact SLR | exact ANone | exact FRESH | idtac].
    - exact SAL.
    - change (conc stC p) with (conc st p). rewrite (rsec_init _ _ INI) in HDR0. exact HDR0.
    - intros k Hk. change (conc stC p) with (conc st p). rewrite meta_cells_meta0.
      destruct REST as [[_ B] W]. cbn [cells_bytes cbytes cells_size csize Nat.add] in B, W. rewrite app_nil_r in B.
      replace (conc st p + AREA_HDR + META_SIZE * k) with ((conc st p + 24) + 40 * k) by (unfold AREA_HDR, META_SIZE; lia).
      eapply (rrw_cells_of_zeros _ (conc st p + 24) 4072 (40 * k)); [exact B| exact W| cbn; tauto| reflexivity| lia| cbn [cells_size csize Nat.add]; unfold NSLOTS in Hk; lia].
    - change (conc stC p) with (conc st p).
      destruct REST as [[_ B] W]. cbn [cells_bytes cbytes cells_size csize Nat.add] in B, W. rewrite app_nil_r in B.
      replace (conc st p + 4064) with ((conc st p + 24) + 4040) by lia.
      eapply (rrw_cells_of_zeros _ (conc st p + 24) 4072 4040); [exact B| exact W| cbn; split; [reflexivity| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity| lia| cbn [cells_size csize Nat.add]; lia]. }
  clear MRC3 HDR0 REST.
  assert (MSq : meta_slot stD (aadd p AREA_HDR)).
  { exists p, (mkArea (c_secret (ctx st)) None NSLOTS), 0. split; [| split; [unfold NSLOTS; lia| unfold AREA_HDR, META_SIZE; rewrite Z.mul_0_r, Z.add_0_r; reflexivity]].
    unfold stD. cbn [s_areas set_areas]. rewrite lookup_insert_eq. reflexivity. }
  assert (CQ : conc st p + 24 = conc stD (aadd p AREA_HDR)).
  { change (conc stD (aadd p AREA_HDR)) with (conc st (aadd p AREA_HDR)). rewrite (conc_aadd st p AREA_HDR) by (rewrite Hr; eauto). reflexivity. }
  rewrite CQ. change (Z_to_bv 64 3486312) with (Z_to_bv 64 RSSP_GUARD). change (Z_to_bv 64 3487016) with (Z_to_bv 64 RMLOCK).
  eapply evt_mono.
  { eapply (ram_b0 sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo 100 stD (aadd p AREA_HDR));
      [exact MRD | assumption | exact MSq | lia | | | unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia | lia].
    - lazymatch goal with H : rw_cells ctusegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
    - lazymatch goal with H : stk ctusegs ?mX lo _ |- _ => exact H end. }
  intros ms' RP. unfold ram_ret_post in RP |- *.
  destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
  do 15 eexists. split; [reflexivity|].
  split.
  { eapply rpres_except_trans; [exact PE0|].
    apply (rpres_except_of_munch_cov (ram_fp st0 lo (bv_unsigned sp))) in MU; [|exact WM|].
    - eapply rpres_except_trans; [exact MU|]. eapply rpres_except_mono; [exact PE'|]. intros a Ha.
      apply (proj1 (ram_fp_same st0 stD lo _ a ltac:(rewrite <- ER0; reflexivity))). exact Ha.
    - cbn [ivs_covered]. split; [|split; [|split; [|exact I]]].
      + intros x Hx. apply ram_fp_stack. lia.
      + intros x Hx. apply ram_fp_ctx. unfold RCTX. lia.
      + intros x Hx. eapply (ram_fp_region st0 lo _ x (fst p) r); [rewrite <- ER0; exact Hr| exact NK|].
        pose proof (lr_lo_ge r). lia. }
  (* [comment removed for export] *)
  split; [eapply wmono_trans; [exact WM0| exact WM']|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed.

(* [comment removed for export] *)
Lemma ram_carve_walk : forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
    (m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (p : aptr) (r : region),
  rmrep st m -> mem_inv ctusegs m ->
  (s_regions st) !! (fst p) = Some r -> r_kind r <> RKGroup -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
  pgal (snd p) -> lr_lo r <= r_base r + snd p ->
  (s_areas st) !! p = None -> (forall k, 0 <= k < NSLOTS -> (s_metas st) !! (aadd p (AREA_HDR + META_SIZE * k)) = None) ->
  (forall tl, c_meta_area_tail (ctx st) = Some tl -> is_Some ((s_areas st) !! tl)) ->
  1 <= c_avail_meta_area_count (ctx st) < 2^64 -> 0 <= c_secret (ctx st) < 2^64 -> c_init_done (ctx st) <> 0 ->
  bytes_at ctusegs m (conc st p) (zeros 4096) -> wr_at ctusegs m (conc st p) 4096 ->
  rw_cells ctusegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
  stk ctusegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  evt ctusegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo (carve_st st p) m
               (am_took (carve_st st p) (aadd p AREA_HDR) 100) (Z_to_bv 64 (conc st p + 24)))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (conc st p)) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b3c78) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until r. intros MR MI Hr NK S0 S1 SAL SLR ANone FRESH TL CNT SEC INI ZB ZW FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR as (WF & (C1 & _) & _ & AR & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  pose proof (conc_region' st p r Hr) as Cp.
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (DR1 & _ & DR23 & DR2). unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in RBC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  pose proof (lr_lo_ge r) as LRG. pose proof (round_up_pg_ge (r_len r)) as RU.
  unfold rctx_head_cells in C1.
  (* [comment removed for export] *)
  assert (HDR0 : rw_cells ctusegs m (conc st p) [C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0)]).
  { rewrite <- (Z.add_0_r (conc st p)). eapply (rrw_cells_of_zeros m (conc st p) 4096 0); [exact ZB| exact ZW| cbn; tauto| reflexivity| lia| cbn; lia]. }
  assert (REST : rw_cells ctusegs m (conc st p + 24) [CB 4072 (zeros 4072)]).
  { eapply (rrw_cells_of_zeros m (conc st p) 4096 24); [exact ZB| exact ZW| cbn [cells_wf]; split; [first [reflexivity | apply zeros_length]| exact I] | cbn [cells_bytes cbytes cells_size csize Nat.add]; rewrite app_nil_r; reflexivity| lia| cbn; lia]. }
  clear ZB ZW.
  unfold RCTX, RMLOCK, RSSP_GUARD, OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  assert (PD : conc st p + 4096 <= 0x2c2000 \/ 0x355000 <= conc st p) by lia.
  assert (PB : 0 <= conc st p /\ conc st p + 4096 <= lo) by lia.
  clear RBAL RL0 RF DR1 DR23 DR2 RU.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 928); (conc st p, conc st p + 4096)]%Z m) as MU0.
  pose proof (wmono_refl ctusegs m) as WM0. unfold RCTX in MU0.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(RCTX + 40, RCTX + 48); (RCTX + 72, RCTX + 80)]%Z mX) as MUc; pose proof (wmono_refl ctusegs mX) as WMc end.
  unfold RCTX in MUc.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1.
  set (st1 := upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR1 : rmrep st1 mX) end.
  { eapply (rmrep_ctx_frameW st st1 _ _ _ MR MUc WMc); try reflexivity.
    - intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - left. unfold rctx_head_cells, RCTX. cbn [ctx st1 upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
            c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
      unfold pw at 5. cbn [oconc]. change (conc st1 (aadd p 4096)) with (conc st (aadd p 4096)).
      rewrite (conc_aadd st p 4096) by (rewrite Hr; eauto). unfold wz at 6 7.
      lazymatch goal with H : rw_cells ctusegs ?mX 3487024 _ |- _ => exact H end.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia. }
  clear MUc WMc.
  (* [comment removed for export] *)
  st1.
  destruct (c_meta_area_tail (ctx st)) as [tl|] eqn:HT.
  - (* [comment removed for export] *)
    destruct (TL tl eq_refl) as [ar Har].
    destruct (rarea_conc st tl ar WF Har) as (rt & Hrt & Ct & St0 & St1 & StL & NKt & RBt & RBAt & RBCt). unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in RBCt; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
    pose proof (rarea_lr_lo st tl ar rt WF Har Hrt) as LRt.
    destruct (WR _ _ Hrt) as (_ & _ & _ & _ & RFt). destruct (rreserved_disjoint _ _ RFt) as (DT1 & _ & DT23 & DT2).
    assert (TD : conc st tl + 4096 <= 0x2c2000 \/ 0x355000 <= conc st tl) by lia.
    assert (TB : 0 < conc st tl /\ conc st tl + 4096 <= lo) by lia.
    assert (TP : conc st tl + 4096 <= conc st p \/ conc st p + 4096 <= conc st tl).
    { destruct (N.eq_dec (fst tl) (fst p)) as [E|NE].
      - rewrite E, Hr in Hrt. assert (rt = r) by congruence. subst rt.
        assert (NEo : snd tl <> snd p) by (intros E2; assert (tl = p) by (destruct tl, p; cbn in *; congruence); subst tl; rewrite ANone in Har; discriminate).
        unfold pgal in SAL. clear - Ct Cp NEo SAL StL E. Z.div_mod_to_equations. lia.
      - destruct (DJ _ _ _ _ Hrt Hr NE); lia. }
    clear RBAt StL RFt DT1 DT23 DT2 St0 St1 LRt RBt RBCt DJ WA WG.
    unfold pw. cbn [oconc]. unfold wz.
    assert (CF : bv_eqb (Z_to_bv 64 (conc st tl)) (Z_to_bv 64 0) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
    rewrite CF. clear CF.
    pose proof MR1 as (_ & _ & _ & AR1 & _). destruct (AR1 tl ar Har) as (ARh & _ & _). clear AR1.
    change (conc st1 tl) with (conc st tl) in ARh.
    apply (munch_grow2 _ (conc st tl, conc st tl + 4096)) in MU0.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (munch_refl [(conc st tl + 8, conc st tl + 16)]%Z mX) as MUa; pose proof (wmono_refl ctusegs mX) as WMa end.
    (* [comment removed for export] *)
    st1. st1.
    set (st2 := set_areas (<[tl := mkArea (a_check ar) (Some p) (a_nslots ar)]> (s_areas st1)) st1).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR2 : rmrep st2 mX) end.
    { eapply (rmrep_set_area_next st1 _ _ tl ar p MR1 Har); [cbn; rewrite Hr; eauto| exact MUa| exact WMa|].
      change (conc st1 tl) with (conc st tl). change (conc st1 p) with (conc st p). unfold wz at 2. exact ARh. }
    clear MUa WMa ARh MR1.
    rewrite (carve_st_some st p tl ar HT Har ANone). cbv zeta. fold st1. fold st2.
    change (Z_to_bv 64 3486312) with (Z_to_bv 64 RSSP_GUARD). change (Z_to_bv 64 3487016) with (Z_to_bv 64 RMLOCK).
    eapply evt_mono.
    { eapply (ram_carve2 sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc m _ junk lo st st2 p r);
        first [exact MR2 | reflexivity | exact Hr | exact NK | exact S0 | exact S1 | exact SAL | exact SLR | exact FRESH | exact SEC | exact INI | exact WM0 | idtac].
      - lazymatch goal with H : mem_inv ctusegs ?mX |- _ => exact H end.
      - cbn [s_areas set_areas upd_ctx st2 st1]. rewrite lookup_insert_ne; [exact ANone|]. intros ->. rewrite ANone in Har; discriminate.
      - lazymatch goal with H : rw_cells ctusegs ?mX (conc st p) _ |- _ => exact H end.
      - lazymatch goal with H : rw_cells ctusegs ?mX (conc st p + 24) _ |- _ => exact H end.
      - apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU0; [exact MU0|exact WM0|].
        cbn [ivs_covered]. split; [|split; [|split; [|split; [|exact I]]]].
        + intros x Hx. apply ram_fp_stack. lia.
        + intros x Hx. eapply ram_fp_area; [exact MR| exact Har| lia].
        + intros x Hx. apply ram_fp_ctx. unfold RCTX. lia.
        + intros x Hx. eapply (ram_fp_region st lo _ x (fst p) r); [exact Hr| exact NK| lia].
      - lazymatch goal with H : rw_cells ctusegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
      - lazymatch goal with H : stk ctusegs ?mX lo _ |- _ => exact H end.
      - unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia.
      - lia. }
    intros ms' RP. exact RP.
  - (* [comment removed for export] *)
    unfold pw. cbn [oconc]. unfold wz.
    change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true. cbv iota.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (munch_refl [(RCTX + 56, RCTX + 64)]%Z mX) as MUc; pose proof (wmono_refl ctusegs mX) as WMc end.
    unfold RCTX in MUc.
    (* [comment removed for export] *)
    st1.
    set (st2 := upd_ctx (set_meta_area_head (Some p)) st1).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR2 : rmrep st2 mX) end.
    { eapply (rmrep_ctx_frameW st1 st2 _ _ _ MR1 MUc WMc); try reflexivity.
      - intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - left. unfold rctx_head_cells, RCTX. cbn [ctx st2 st1 upd_ctx s_ctx set_meta_area_head set_avail_meta_areas set_avail_meta_area_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
              c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
        rewrite HT. unfold pw. cbn [oconc]. change (conc st2 ?q) with (conc st q). change (conc st2 p) with (conc st p).
        rewrite (conc_aadd st p 4096) by (rewrite Hr; eauto). unfold wz.
        lazymatch goal with H : rw_cells ctusegs ?mX 3487024 _ |- _ => exact H end.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia. }
    clear MUc WMc MR1.
    rewrite (carve_st_none st p HT ANone). cbv zeta. fold st1. fold st2.
    change (Z_to_bv 64 3486312) with (Z_to_bv 64 RSSP_GUARD). change (Z_to_bv 64 3487016) with (Z_to_bv 64 RMLOCK).
    eapply evt_mono.
    { eapply (ram_carve2 sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc m _ junk lo st st2 p r);
        first [exact MR2 | reflexivity | exact Hr | exact NK | exact S0 | exact S1 | exact SAL | exact SLR | exact ANone | exact FRESH | exact SEC | exact INI | exact WM0 | idtac].
      - lazymatch goal with H : mem_inv ctusegs ?mX |- _ => exact H end.
      - lazymatch goal with H : rw_cells ctusegs ?mX (conc st p) _ |- _ => exact H end.
      - lazymatch goal with H : rw_cells ctusegs ?mX (conc st p + 24) _ |- _ => exact H end.
      - apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU0; [exact MU0|exact WM0|].
        cbn [ivs_covered]. split; [|split; [|split; [|exact I]]].
        + intros x Hx. apply ram_fp_stack. lia.
        + intros x Hx. apply ram_fp_ctx. unfold RCTX. lia.
        + intros x Hx. eapply (ram_fp_region st lo _ x (fst p) r); [exact Hr| exact NK| lia].
      - lazymatch goal with H : rw_cells ctusegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
      - lazymatch goal with H : stk ctusegs ?mX lo _ |- _ => exact H end.
      - unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia.
      - lia. }
    intros ms' RP. exact RP.
Qed.
End WithCeiling0.
