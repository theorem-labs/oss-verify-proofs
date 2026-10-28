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
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep SFModel.
From OssFuzzTheorems.openssl.ct.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import F_malloc_free F_malloc_fast.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Malloc MallocCtrl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import CeilWin.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
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
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma land_pow2_testbit a i : 0 <= a -> 0 <= i -> Z.land a (2 ^ i) = 0 <-> Z.testbit a i = false.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros Ha Hi. split.
  - intros H. destruct (Z.testbit a i) eqn:E; [|reflexivity]. exfalso.
    assert (T : Z.testbit (Z.land a (2 ^ i)) i = true) by (rewrite Z.land_spec, E, Z.pow2_bits_true by lia; reflexivity).
    rewrite H, Z.bits_0 in T. discriminate.
  - intros H. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.eq_dec n i) as [->|NE]; [rewrite H; reflexivity|].
    rewrite (Z.pow2_bits_false i n) by lia. apply andb_false_r.
Qed.

Lemma sllw1_word' i : 0 <= i < 32 -> Z_to_bv 64 (bv_swrap 32 (Z.shiftl 1 (i mod 32))) = wz (sxv (2 ^ i)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros Hi. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l. unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity. Qed.

Definition rget_meta_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 a7 gw : word) (off16 : Z)
   (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a2 a3 a4 a5,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 gw (wz off16) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom ctusegs).


Lemma rget_meta_tail : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gw : word) F fc m
   (off16 mword maplen : Z),
  0 <= off16 < 65536 -> 0 <= mword < 2^64 -> 0 <= maplen < 2^40 -> Z.shiftr mword 12 = maplen ->
  (maplen <> 0 -> off16 <= maplen * 256 - 1) ->
  evt ctusegs (rget_meta_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 a7 gw off16 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 gw (wz off16) (wz mword) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b366c) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until maplen. intros O16 MW ML MW4 Hml.
  st1. rewrite MW4. st1. if_cases K; zify_cond K; rewrite ?wz_unsigned in K by lia.
  - st1. unfold rget_meta_post. finish.
  - st1. st1. st1. if_cases K2; zify_cond K2.
    + st1. unfold rget_meta_post. finish.
    + exfalso. rewrite Z.shiftl_mul_pow2 in K2 by lia. change (2^8) with 256 in K2. change 18446744073709551615 with (Z.ones 64) in K2.
      rewrite Z.land_ones, wz_unsigned in K2 by lia. rewrite Z.mod_small in K2 by lia. lia.
Qed.

Lemma rget_meta_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
   (P G B A : Z) (b3 off16 avail freed last_idx freeable sc maplen secret: Z) (prev next : word),
  let idx := Z.land b3 31 in
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  bv_unsigned a0 = P -> P mod 16 = 0 -> 16 * off16 + 16 <= P -> P + 16 <= 2^64 ->
  B = P - 16 * off16 - 16 -> A = G - G mod 4096 -> 0 <= G -> G + 40 <= 2^64 ->
  ov_read_bytes ctusegs m (wa (P - 4)) 1 = Some [b8 0] ->
  ov_read_bytes ctusegs m (wa (P - 3)) 1 = Some [b8 b3] ->
  ov_read_bytes ctusegs m (wa (P - 2)) 2 = Some (le2 (wz off16)) ->
  ov_read_bytes ctusegs m (wa B) 8 = Some (le8 (wz G)) ->
  rw_cells ctusegs m G [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
  ov_read_bytes ctusegs m (wa A) 8 = Some (le8 (wz secret)) ->
  ov_read_bytes ctusegs m (wa RCTX) 8 = Some (le8 (wz secret)) ->
  (sc < 48 -> ov_read_bytes ctusegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
  0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= secret < 2^64 ->
  0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
  idx <= last_idx -> Z.testbit avail idx = false -> Z.testbit freed idx = false ->
  (sc < 48 -> size_class sc * idx <= off16 < size_class sc * (idx + 1)) ->
  (48 <= sc -> sc = 63) ->
  (maplen <> 0 -> off16 <= maplen * 256 - 1) ->
  evt ctusegs (rget_meta_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 a7 (wz G) off16 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b3578) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until next. intros idx mword HP AL PLO PHI HB HA GLO GHI R4 R3 R2 RG MM RA RC RS B3 O16 AV FR SE LI FB SC ML
    Hidx Hav Hfr Hsc Hsc63 Hml.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  st1. st1. if_cases K; zify_cond K. 2:{ exfalso. change 15 with (2^4 - 1) in K. rewrite zb_land_mask in K by lia. lia. }
  st1. st1. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
  st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
  st1.
  (* [comment removed for export] *)
  assert (RG' : ov_read_bytes ctusegs m (Z_to_bv 64 (P - off16 * 16 + -16)) 8 = Some (le8 (wz G))).
  { replace (P - off16 * 16 + -16) with B by lia. exact RG. }
  st1.
  set (gw := wz G) in *. assert (HG : bv_unsigned gw = G) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. clearbody gw.
  assert (GW : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
  st1. st1. st1. fold idx. st1. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite wz_unsigned in K3 by lia. lia. }
  (* [comment removed for export] *)
  assert (MW1 : Z.land mword 31 = last_idx).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  st1. st1. rewrite MW1. st1. if_cases K4; zify_cond K4. 2:{ exfalso. lia. }
  (* [comment removed for export] *)
  st1. rewrite sx32_wz_sxv by lia. st1. st1.
  rewrite sllw1_word' by lia.
  assert (P2 : 0 <= 2 ^ idx < 2^32) by (split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
  pose proof (sxv_range avail) as SXA. pose proof (sxv_range (2 ^ idx)) as SXI.
  assert (LA : Z.land avail (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit avail idx ltac:(lia) ltac:(lia))); exact Hav).
  assert (LF : Z.land freed (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit freed idx ltac:(lia) ltac:(lia))); exact Hfr).
  st1. rewrite sxv_land, LA, (sxv_small 0) by lia. st1. if_cases K5; zify_cond K5. 2:{ exfalso. apply K5. reflexivity. }
  (* [comment removed for export] *)
  pose proof (sxv_range freed) as SXF.
  st1. rewrite sx32_wz_sxv by lia. st1. rewrite sxv_land, LF, (sxv_small 0) by lia. st1. if_cases K6; zify_cond K6. 2:{ exfalso. apply K6. reflexivity. }
  (* [comment removed for export] *)
  st1. st1. st1. rewrite land_pgmask by lia. rewrite HG, <- HA. st1. unfold RCTX in RC. st1. st1.
  if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned in K7 by lia. lia. }
  (* [comment removed for export] *)
  assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl mword 52))) 58 = sc).
  { rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. subst mword.
    replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) * 2 ^ 52)
      with ((last_idx + 32 * freeable + 64 * sc) * 2^52 + maplen * 2^64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
    replace ((last_idx + 32 * freeable + 64 * sc) * 2 ^ 52) with ((last_idx + 32 * freeable) * 2^52 + sc * 2^58) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  st1. st1. rewrite MW2. st1. st1. if_cases K8; zify_cond K8.
  - (* [comment removed for export] *) specialize (Hsc63 ltac:(rewrite ?wz_unsigned in K8 by lia; lia)).
    st1. st1. if_cases K9; zify_cond K9. 2:{ exfalso. rewrite ?wz_unsigned in K9 by lia. lia. }
    rewrite GW. eapply rget_meta_tail; eauto.
    subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.div_add, Z.div_small by lia. lia.
  - specialize (RS ltac:(rewrite ?wz_unsigned in K8 by lia; lia)). specialize (Hsc ltac:(rewrite ?wz_unsigned in K8 by lia; lia)).
    st1. st1. st1. st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2.
    assert (RS' : ov_read_bytes ctusegs m (Z_to_bv 64 (467628 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
    { replace (Z_to_bv 64 (467628 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
    clear RS. pose proof (size_class_range sc ltac:(lia)) as SZ. st1.
    try rewrite (Z.mod_small (size_class sc)) by lia. fold idx.
    st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }
    st1. st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
    st1. rewrite GW. eapply rget_meta_tail; eauto.
    subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.div_add, Z.div_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma rget_meta_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    st (p : aptr) r g gh ar (b3 lo hi : Z),
  let sh := get_shadow st (fst p) in
  let po := snd p in
  let off16 := lo + 256 * hi in
  let idx := Z.land b3 31 in
  let base := aadd p (- (UNIT * off16) - UNIT) in
  let mr := get_meta_rec st g in
  rmrep st m -> mem_inv ctusegs m ->
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
  evt ctusegs (rget_meta_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 a7 (wz (conc st g)) off16 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rget_meta_entry) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until hi. intros sh po off16 idx base mr MR MI Hr Hk HP AL P16 PLO PHI C4 C3 C2 C1 Hgh Hg MS G0 Hmem Har Hchk INIT
         AV FR SE LI FB SC ML Hidx Hav Hfr Hsc Hsc63 Hml.
  pose proof MR as (WF & CX & GL & AR & GR & SH).
  destruct WF as (Hres & WR & DISJ & WA & WG).
  destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & _). unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in BC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
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
  (* [comment removed for export] *)
  rewrite <- (wz_mod64 (c_secret (ctx st) + bv_unsigned rr_secret)) in RA, RC.
  (* [comment removed for export] *)
  destruct (WG base gh Hgh) as (rb & Hrb & _ & Bb0 & _). cbn [base aadd fst] in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb.
  assert (HB : conc st base = (r_base r + po) - 16 * off16 - 16).
  { unfold base. rewrite conc_aadd by (rewrite Hr; eauto). rewrite (conc_region' st p r Hr). unfold po, UNIT. lia. }
  destruct MS as (a & ara & k & Ha & Hkk & Eg).
  destruct (WA a ara Ha) as (rg & Hrg & A0 & A1 & AAL & ANG & _).
  assert (HG : conc st g = r_base rg + snd a + (AREA_HDR + META_SIZE * k)).
  { rewrite Eg, conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a rg Hrg). reflexivity. }
  destruct (WR (fst a) rg Hrg) as (RB0 & RBAL & RL0 & RBC & _). unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in RBC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
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
  unfold rget_meta_entry.
  eapply (rget_meta_walk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
            (r_base r + po) (conc st g) (conc st base) (conc st (area_of g)) b3 off16 (m_avail mr) (m_freed mr)
            (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) ((c_secret (ctx st) + bv_unsigned rr_secret) mod 2^64)
            (pw st (m_prev mr)) (pw st (m_next mr))); try eassumption; try lia; try apply rsec_range.
  - replace (r_base r + po - 4) with (r_base r + (po - 4)) by lia. exact R4.
  - replace (r_base r + po - 3) with (r_base r + (po - 3)) by lia. exact R3.
  - replace (r_base r + po - 2) with (r_base r + (po - 2)) by lia. exact R2.
  - intros Hlt. apply rsize_classes_read; [exact MI | lia].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition runlock_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (ret_pc ra) fc None m (seg_rom ctusegs).

Lemma runlock_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m,
  bv_unsigned a0 = RMLOCK ->
  rw_cells ctusegs m (bv_unsigned a0) [C4 (wz 0)] ->
  evt ctusegs (runlock_post ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 runlock_entry) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until m. intros HA LK. unfold runlock_entry.
  step. rewrite sx32_wz by lia. step. if_cases K; zify_cond K.
  { exfalso. rewrite wz_unsigned in K by lia. lia. }
  step. apply evt_done. reflexivity.
Qed.
End WithCeiling0.
