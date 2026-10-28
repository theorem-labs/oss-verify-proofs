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
Definition rrh_post (ra sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (G B sc mword E P rsv : Z) : machine_state -> Prop :=
  fun ms' => exists t1 t2 t3 t4,
    ms' = MS (mkR ra sp gp tp (wz E) t1 t2 s0 (wz G) a0 a1 (wz B) (wz sc) (wz mword) (Z_to_bv 64 0x720c4) (wz (E + 4)) (wz (E - P))
                  (wz (E - rsv)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x2b28f4) fc None m (seg_rom usegs).

Lemma rr_zx32_wz x : 0 <= x < 2^32 -> zx32 (wz x) = wz x.
Proof. intros. unfold zx32, wz. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rrh_tail : forall (ra sp gp tp t1 t2 s0 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m
   (P G B sc mword b3 idx stride r32 : Z),
  let E := B + 16 + stride * idx + stride - 4 in
  let rsv0 := Z.shiftr b3 5 in
  let rsv := if 160 <=? b3 then r32 else rsv0 in
  bv_unsigned a0 = P -> 0 <= B -> 0 <= b3 < 256 -> 0 <= idx < 32 -> 16 <= stride -> P <= E -> E + 5 <= 2^64 -> 0 <= P ->
  (160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ ov_read_bytes usegs m (wa (E - 4)) 4 = Some (le4 (wz r32))
                /\ ov_read_bytes usegs m (wa (E - 5)) 1 = Some [b8 0]) ->
  rsv <= E - P -> ov_read_bytes usegs m (wa (E - rsv)) 1 = Some [b8 0] -> ov_read_bytes usegs m (wa E) 1 = Some [b8 0] ->
  evt usegs (rrh_post ra sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 F fc m G B sc mword E P rsv)
      (MS (mkR ra sp gp tp (wz idx) t1 t2 s0 (wz G) a0 a1 (wz B) (wz sc) (wz mword) (Z_to_bv 64 0x720c4) (wz stride) (wz b3)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b2884) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until r32. intros E rsv0 rsv HP B0 B3 IDX S16 PE EHI P0 BIG RSVLE RCAN REND.
  assert (SI0 : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (RSV0 : 0 <= rsv0 < 8).
  { unfold rsv0. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  assert (RSVR : 0 <= rsv < 2^32).
  { unfold rsv. destruct (Z.leb_spec 160 b3); [destruct (BIG ltac:(lia)) as (_ & ? & _); lia| lia]. }
  st1. st1. st1. st1. st1. st1. st1.
  replace (B + stride * idx + 16 + stride + -4) with E by (unfold E; lia).
  replace (B + stride * idx + 16 + stride) with (E + 4) by (unfold E; lia).
  fold rsv0.
  assert (FIN : forall (x7 t1' t2' t3' : word), 
     evt usegs (rrh_post ra sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 F fc m G B sc mword E P rsv)
       (MS (mkR ra sp gp tp (wz E) t1' (wz rsv) s0 (wz G) a0 a1 (wz B) (wz sc) (wz mword) (Z_to_bv 64 0x720c4) (wz (E + 4)) x7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6) F (Z_to_bv 64 0x2b28cc) fc None m (seg_rom usegs))).
  { intros x7 t1' t2' t3'.
    (* [comment removed for export] *)
    st1. rewrite HP. st1. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. }
    (* [comment removed for export] *)
    st1. replace (E + - rsv) with (E - rsv) by lia. change (Z_to_bv 64 (E - rsv)) with (wa (E - rsv)).
    st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }
    (* [comment removed for export] *)
    change (wz E) with (wa E).
    st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. reflexivity. }
    unfold rrh_post. apply evt_done. do 4 eexists. reflexivity. }
  (* [comment removed for export] *)
  st1. if_cases Kb; zify_cond Kb; rewrite ?wz_unsigned in Kb by lia.
  - replace (Z_to_bv 64 rsv0) with (wz rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [lia| reflexivity]).
    apply FIN; exact (wz 0).
  - destruct (BIG ltac:(lia)) as (R5 & R32 & RD4 & RD5).
    (* [comment removed for export] *)
    st1. st1. if_cases K5; zify_cond K5. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K5 by lia. lia. }
    (* [comment removed for export] *)
    replace (E - 4) with (E + 4 + -8) in RD4 by lia.
    st1. rewrite rr_zx32_wz by lia. st1. st1. if_cases K6; zify_cond K6. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K6 by lia. lia. }
    (* [comment removed for export] *)
    replace (E - 5) with (E + 4 + -9) in RD5 by lia.
    st1. st1. if_cases K7; zify_cond K7. 2:{ exfalso. apply K7. rewrite ?wz_unsigned by lia. reflexivity. }
    replace (wz r32) with (wz rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [reflexivity| lia]).
    apply FIN; exact (wz 0).
Qed.

Lemma rrealloc_head_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
   (P G B A : Z) (b3 off16 avail freed last_idx freeable sc maplen secret r32 : Z) (prev next : word),
  let idx := Z.land b3 31 in
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  let stride := if (last_idx =? 0) && negb (maplen =? 0) then maplen * 4096 - 16 else 16 * size_class sc in
  let E := B + 16 + stride * idx + stride - 4 in
  let rsv0 := Z.shiftr b3 5 in
  let rsv := if 160 <=? b3 then r32 else rsv0 in
  bv_unsigned a0 = P -> P mod 16 = 0 -> 16 * off16 + 16 <= P -> P + 16 <= 2^64 ->
  B = P - 16 * off16 - 16 -> A = G - G mod 4096 -> 0 <= G -> G + 40 <= 2^64 ->
  ov_read_bytes usegs m (wa (P - 4)) 1 = Some [b8 0] ->
  ov_read_bytes usegs m (wa (P - 3)) 1 = Some [b8 b3] ->
  ov_read_bytes usegs m (wa (P - 2)) 2 = Some (le2 (wz off16)) ->
  ov_read_bytes usegs m (wa B) 8 = Some (le8 (wz G)) ->
  rw_cells usegs m G [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
  ov_read_bytes usegs m (wa A) 8 = Some (le8 (wz secret)) ->
  ov_read_bytes usegs m (wa RCTX) 8 = Some (le8 (wz secret)) ->
  (sc < 48 -> ov_read_bytes usegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
  0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= secret < 2^64 ->
  0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
  idx <= last_idx -> Z.testbit avail idx = false -> Z.testbit freed idx = false ->
  (sc < 48 -> size_class sc * idx <= off16 < size_class sc * (idx + 1)) ->
  (48 <= sc -> sc = 63) ->
  (maplen <> 0 -> off16 <= maplen * 256 - 1) ->
  (maplen = 0 \/ last_idx <> 0 -> sc < 48) ->
  16 <= stride -> P <= E -> E + 5 <= 2^64 ->
  (160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ ov_read_bytes usegs m (wa (E - 4)) 4 = Some (le4 (wz r32))
                /\ ov_read_bytes usegs m (wa (E - 5)) 1 = Some [b8 0]) ->
  rsv <= E - P -> ov_read_bytes usegs m (wa (E - rsv)) 1 = Some [b8 0] -> ov_read_bytes usegs m (wa E) 1 = Some [b8 0] ->
  evt usegs (rrh_post ra sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 F fc m G B sc mword E P rsv)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b2768) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until next. intros idx mword stride E rsv0 rsv HP AL PLO PHI HB HA GLO GHI R4 R3 R2 RG MM RA RC RS B3 O16 AV FR SE LI FB SC ML
    Hidx Hav Hfr Hsc Hsc63 Hml Hst S16 PE EHI BIG RSVLE RCAN REND.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  st1. st1. if_cases K; zify_cond K. 2:{ exfalso. change 15 with (2^4 - 1) in K. rewrite zb_land_mask in K by lia. lia. }
  st1. st1. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
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
  st1. st1. st1. fold idx. st1. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite wz_unsigned in K3 by lia. lia. }
  assert (MW1 : Z.land mword 31 = last_idx).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  (* [comment removed for export] *)
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
  assert (MW4 : Z.shiftr mword 12 = maplen).
  { subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.div_add, Z.div_small by lia. lia. }
  st1. st1. st1. st1. rewrite MW2. st1. st1. st1.
  rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2.
  assert (RS' : sc < 48 -> ov_read_bytes usegs m (Z_to_bv 64 (467140 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
  { intros H48. replace (Z_to_bv 64 (467140 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact (RS H48). }
  clear RS.
  (* [comment removed for export] *)
  assert (MID : forall (x28 x29 : word),
    evt usegs (rrh_post ra sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 F fc m G B sc mword E P rsv)
      (MS (mkR ra sp gp tp (Z_to_bv 64 idx) (Z_to_bv 64 last_idx) (Z_to_bv 64 (sc * 2)) s0 gw a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 0x720c4)
               (wz off16) (wz b3) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6) F (Z_to_bv 64 0x2b285c) fc None m (seg_rom usegs))).
  { intros x28 x29.
    assert (CLS : forall (y5 y28 : word), sc < 48 -> stride = 16 * size_class sc ->
      evt usegs (rrh_post ra sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 F fc m G B sc mword E P rsv)
        (MS (mkR ra sp gp tp (Z_to_bv 64 idx) (Z_to_bv 64 last_idx) (Z_to_bv 64 (sc * 2)) s0 gw a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 0x720c4)
                 (wz off16) (wz b3) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 x29 t5 t6) F (Z_to_bv 64 0x2b2878) fc None m (seg_rom usegs))).
    { intros y5 y28 H48 EST. specialize (RS' H48). pose proof (size_class_range sc ltac:(lia)) as SZ.
      (* [comment removed for export] *)
      st1. st1. try rewrite (Z.mod_small (size_class sc)) by lia. st1.
      rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16. replace (size_class sc * 16) with stride by lia.
      rewrite GW. unfold E, rsv, rsv0.
      eapply (rrh_tail ra sp gp tp _ _ s0 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ t5 t6 F fc m P G B sc mword b3 idx stride r32); eauto; lia. }
    (* [comment removed for export] *)
    st1. rewrite MW4. st1. if_cases Km; zify_cond Km; rewrite ?wz_unsigned in Km by lia.
    - (* [comment removed for export] *)
      apply (CLS (wz 0)); [apply Hst; left; lia|]. unfold stride. replace (maplen =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb]. rewrite andb_false_r. reflexivity.
    - (* [comment removed for export] *)
      st1. st1. st1. if_cases Kq; zify_cond Kq.
      2:{ exfalso. rewrite Z.shiftl_mul_pow2 in Kq by lia. change (2^8) with 256 in Kq.
          change 18446744073709551615 with (Z.ones 64) in Kq. rewrite Z.land_ones in Kq by lia.
          rewrite ?wz_unsigned in Kq by lia. specialize (Hml ltac:(lia)). rewrite Z.mod_small in Kq by lia. lia. }
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
        rewrite GW. unfold E, rsv, rsv0.
        eapply (rrh_tail ra sp gp tp _ _ s0 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ t5 t6 F fc m P G B sc mword b3 idx stride r32); eauto; lia.
      + apply (CLS (wz 0)); [apply Hst; right; lia|]. unfold stride. replace (last_idx =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  (* [comment removed for export] *)
  if_cases K8; zify_cond K8.
  - (* [comment removed for export] *)
    specialize (Hsc63 ltac:(rewrite ?unsigned_lit in K8 by lia; lia)).
    st1. st1. if_cases K9; zify_cond K9. 2:{ exfalso. rewrite ?unsigned_lit in K9 by lia. lia. }
    apply MID.
  - assert (H48 : sc < 48) by (rewrite ?unsigned_lit in K8 by lia; lia).
    specialize (Hsc H48). pose proof (RS' H48) as RSs. pose proof (size_class_range sc ltac:(lia)) as SZ.
    (* [comment removed for export] *)
    st1. st1. try rewrite (Z.mod_small (size_class sc)) by lia.
    st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }
    (* [comment removed for export] *)
    st1. st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
    st1. apply MID.
Qed.
End WithCeiling0.
