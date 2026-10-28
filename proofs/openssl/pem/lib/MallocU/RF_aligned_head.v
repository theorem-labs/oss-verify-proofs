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
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RF_get_meta.
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
Definition rah_regs (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 a0 : word) (t0 t1 t2 t3 : word)
    (idx len B stride adj : Z) : bvmap 5 word :=
  mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 63) s1 a0 (wz idx) (Z_to_bv 64 len) (wz (B + 16 + stride * (idx + 1))) (wz (B + 16 + stride * (idx + 1) + -4))
      (wz (B + 16)) (wz stride) (wz adj) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

Definition rah_post (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 a0 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (idx len B stride P : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 t3,
    (P mod 64 = 0
     /\ ms' = MS (rah_regs ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 a0 t0 t1 t2 t3 idx len B stride 0)
                 F (Z_to_bv 64 0x2b2678) fc None m (seg_rom usegs))
    \/ (P mod 64 <> 0
        /\ ms' = MS (rah_regs ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 a0 t0 t1 t2 t3 idx len B stride (64 - P mod 64))
                    F (Z_to_bv 64 0x2b2610) fc None m (seg_rom usegs)).

Lemma raligned_head_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
   (P G B A len : Z) (b3 off16 avail freed last_idx freeable sc maplen secret : Z) (prev next : word),
  let idx := Z.land b3 31 in
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  let stride := if (last_idx =? 0) && negb (maplen =? 0) then maplen * 4096 - 16 else 16 * size_class sc in
  s0 = Z_to_bv 64 64 -> s1 = Z_to_bv 64 len ->
  bv_unsigned a0 = P -> P <> 0 -> P mod 16 = 0 -> 16 * off16 + 16 <= P -> P + 16 <= 2^64 ->
  B = P - 16 * off16 - 16 -> A = G - G mod 4096 -> 0 <= G -> G + 40 <= 2^64 ->
  ov_read_bytes usegs m (wa (P - 4)) 1 = Some [b8 0] ->
  ov_read_bytes usegs m (wa (P - 3)) 1 = Some [b8 b3] ->
  ov_read_bytes usegs m (wa (P - 2)) 2 = Some (le2 (wz off16)) ->
  ov_read_bytes usegs m (wa B) 8 = Some (le8 (wz G)) ->
  rw_cells usegs m G [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
  ov_read_bytes usegs m (wa A) 8 = Some (le8 (wz secret)) ->
  ov_read_bytes usegs m (wa RCTX) 8 = Some (le8 (wz secret)) ->
  ov_read_bytes usegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc))) ->
  0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= secret < 2^64 ->
  0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 48 -> 0 <= maplen < 2^40 ->
  idx <= last_idx -> Z.testbit avail idx = false -> Z.testbit freed idx = false ->
  size_class sc * idx <= off16 < size_class sc * (idx + 1) ->
  (maplen <> 0 -> off16 <= maplen * 256 - 1) ->
  16 <= stride < 2^20 -> 0 <= B -> B + 16 + stride * (idx + 1) <= 2^63 ->
  evt usegs (rah_post ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 a0 F fc m idx len B stride P)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b24cc) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until next. intros idx mword stride HS0 HS1 HP PNZ AL PLO PHI HB HA GLO GHI R4 R3 R2 RG MM RA RC RS B3 O16 AV FR SE LI FB SC ML
    Hidx Hav Hfr Hsc Hml S16 B0 BHI. subst s0 s1.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  (* [comment removed for export] *)
  st1. if_cases KN; zify_cond KN. { exfalso. lia. }
  st1. st1. if_cases K; zify_cond K. 2:{ exfalso. change 15 with (2^4 - 1) in K. rewrite zb_land_mask in K by lia. lia. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
  (* [comment removed for export] *)
  st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
  st1.
  assert (RG' : ov_read_bytes usegs m (Z_to_bv 64 (P - off16 * 16 + -16)) 8 = Some (le8 (wz G))).
  { replace (P - off16 * 16 + -16) with B by lia. exact RG. }
  st1.
  set (gw := wz G) in *. assert (HG : bv_unsigned gw = G) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. clearbody gw.
  assert (GW : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  st1. st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite wz_unsigned in K3 by lia. lia. }
  assert (MW1 : Z.land mword 31 = last_idx).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  (* [comment removed for export] *)
  st1. st1. rewrite MW1. st1. if_cases K4; zify_cond K4. 2:{ exfalso. fold idx in K4. rewrite ?wz_unsigned, ?unsigned_lit in K4 by lia. lia. }
  fold idx.
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
  st1. st1. rewrite land_pgmask by lia. rewrite HG, <- HA. st1. st1. unfold RCTX in RC. st1. st1.
  if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned in K7 by lia. lia. }
  (* [comment removed for export] *)
  assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl mword 52))) 58 = sc).
  { rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. subst mword.
    replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) * 2 ^ 52)
      with ((last_idx + 32 * freeable + 64 * sc) * 2^52 + maplen * 2^64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
    replace ((last_idx + 32 * freeable + 64 * sc) * 2 ^ 52) with ((last_idx + 32 * freeable) * 2^52 + sc * 2^58) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  assert (MW4 : Z.shiftr mword 12 = maplen).
  { subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.div_add, Z.div_small by lia. lia. }
  st1. st1. st1. st1. rewrite MW2. st1. st1. st1.
  rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2.
  assert (RS' : ov_read_bytes usegs m (Z_to_bv 64 (467140 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
  { replace (Z_to_bv 64 (467140 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
  clear RS. pose proof (size_class_range sc ltac:(lia)) as SZ.
  st1. if_cases K8; zify_cond K8. { exfalso. rewrite ?unsigned_lit in K8 by lia. lia. }
  (* [comment removed for export] *)
  st1. st1. try rewrite (Z.mod_small (size_class sc)) by lia.
  st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }
  (* [comment removed for export] *)
  st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
  st1.
  (* [comment removed for export] *)
  st1. rewrite MW4. st1. rewrite HP.
  assert (SI1 : 0 <= stride * (idx + 1)) by (apply Z.mul_nonneg_nonneg; lia).
  assert (ADJ : Z.land 63 (bv_unsigned (Z_to_bv 64 (0 - P))) = (0 - P) mod 64).
  { rewrite unsigned_lit_wrap. change 63 with (2^6 - 1). rewrite zb_land_mask_l by lia. change (2^6) with 64.
    change (2^64) with (64 * 288230376151711744). rewrite Z.rem_mul_r by lia.
    rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia. }
  assert (L63 : forall x, Z.land x 63 = x mod 64) by (intros x; change 63 with (2^6 - 1); apply zb_land_mask; lia).
  (* [comment removed for export] *)
  assert (FIN : forall (x5 x6 x13 x28 : word),
    evt usegs (rah_post ra sp gp tp (Z_to_bv 64 len) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 a0 F fc m idx len B stride P)
      (MS (mkR ra sp gp tp x5 x6 (Z_to_bv 64 (0 - P)) (Z_to_bv 64 64) (Z_to_bv 64 len) a0 (Z_to_bv 64 idx) (Z_to_bv 64 len) x13 (wz B)
               (wz mword) (wz stride) (Z_to_bv 64 (idx + 1)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
          F (Z_to_bv 64 0x2b25f4) fc None m (seg_rom usegs))).
  { intros x5 x6 x13 x28.
    (* [comment removed for export] *)
    st1. st1. st1. st1. st1. rewrite ?ADJ. st1. st1.
    if_cases KA; zify_cond KA.
    - assert (PM : P mod 64 = 0 /\ (0 - P) mod 64 = 0).
      { rewrite ?unsigned_lit in KA by (pose proof (Z.mod_pos_bound (0 - P) 64); lia). rewrite ?L63 in KA. clear - KA. Z.div_mod_to_equations. lia. }
      rewrite (proj2 PM).
      apply evt_done. unfold rah_post. exists x5, x6, (Z_to_bv 64 (0 - P)), x28. left.
      split; [exact (proj1 PM)|]. reflexivity.
    - assert (PM : P mod 64 <> 0 /\ (0 - P) mod 64 = 64 - P mod 64).
      { rewrite ?unsigned_lit in KA by (pose proof (Z.mod_pos_bound (0 - P) 64); lia). rewrite ?L63 in KA. clear - KA. Z.div_mod_to_equations. lia. }
      rewrite (proj2 PM).
      apply evt_done. unfold rah_post. exists x5, x6, (Z_to_bv 64 (0 - P)), x28. right.
      split; [exact (proj1 PM)|]. reflexivity. }
  replace (0 + - P) with (0 - P) by lia.
  assert (CLS : forall (y28 : word), stride = 16 * size_class sc ->
    evt usegs (rah_post ra sp gp tp (Z_to_bv 64 len) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 a0 F fc m idx len B stride P)
      (MS (mkR ra sp gp tp (Z_to_bv 64 467140) (Z_to_bv 64 (sc * 2)) (Z_to_bv 64 (0 - P)) (Z_to_bv 64 64) (Z_to_bv 64 len) a0 (Z_to_bv 64 idx) (Z_to_bv 64 len)
               (wz off16) (wz B) (wz mword) (Z_to_bv 64 last_idx) (Z_to_bv 64 (idx + 1)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 t4 t5 t6)
          F (Z_to_bv 64 0x2b25e8) fc None m (seg_rom usegs))).
  { intros y28 EST.
    (* [comment removed for export] *)
    st1. st1. try rewrite (Z.mod_small (size_class sc)) by lia. st1.
    rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16. replace (size_class sc * 16) with stride by lia.
    apply FIN. }
  (* [comment removed for export] *)
  st1. if_cases Km; zify_cond Km; rewrite ?wz_unsigned, ?unsigned_lit in Km by lia.
  - (* [comment removed for export] *)
    apply CLS. unfold stride. replace (maplen =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
    cbn [negb]. rewrite andb_false_r. reflexivity.
  - (* [comment removed for export] *)
    st1. st1. st1. if_cases Kq; zify_cond Kq.
    2:{ exfalso. rewrite Z.shiftl_mul_pow2 in Kq by lia. change (2^8) with 256 in Kq.
        change 18446744073709551615 with (Z.ones 64) in Kq. rewrite Z.land_ones in Kq by lia.
        rewrite ?wz_unsigned, ?unsigned_lit in Kq by lia. specialize (Hml ltac:(lia)). rewrite Z.mod_small in Kq by lia. lia. }
    (* [comment removed for export] *)
    st1. if_cases Kl; zify_cond Kl; rewrite ?unsigned_lit in Kl by lia.
    + (* [comment removed for export] *)
      st1. st1. rewrite land_pgmask by lia. st1. st1.
      assert (EST : stride = maplen * 4096 - 16).
      { unfold stride. replace (last_idx =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
        replace (maplen =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
      replace (mword - mword mod 4096 + -16) with stride.
      2:{ rewrite EST. subst mword. replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
          rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia. }
      apply FIN.
    + apply CLS. unfold stride. replace (last_idx =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.
End WithCeiling0.
