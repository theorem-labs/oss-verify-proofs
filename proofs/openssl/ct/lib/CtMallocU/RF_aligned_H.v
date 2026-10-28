(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Znumtheory.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep SFModel.
From OssFuzzTheorems.openssl.ct.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RF_enframe RF_get_meta RF_aligned_B.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Malloc MallocCtrl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
(* [comment removed for export] *)
Definition hid (P : Prop) : Prop := P.
Ltac hide H := lazymatch type of H with ?T => change T with (hid T) in H end.
Ltac unhide := unfold hid in *.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma raligned_h2 : forall (ra sp gp tp t2 s1 a3 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (ra0 s0v s1v : word) F fc (m : word -> option byte) (P Bb idx n al mp b3 q : Z) (last_idx freeable sc maplen : Z) (junk : list byte),
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  let stride := if (last_idx =? 0) && negb (maplen =? 0) then 4096 * maplen - 16 else 16 * size_class sc in
  let S0 := Bb + 16 in let S := S0 + stride * idx in let E := S0 + stride * (idx + 1) - 4 in
  let adj := (- P) mod al in let P' := P + adj in
  (sc < 48 -> ov_read_bytes ctusegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
  0 <= q < 65536 -> 0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
  (maplen <> 0 -> q <= maplen * 256 - 1) -> (maplen = 0 \/ last_idx <> 0 -> sc < 48) -> 0 < P ->
  (* [comment removed for export] *)
  rw_cells ctusegs m (bv_unsigned sp) [CB 8 junk; C8 s1v; C8 (Z_to_bv 64 mp); C8 (Z_to_bv 64 0x2b4c40); C8 s0v; C8 ra0] ->
  wr_at ctusegs m mp 8 -> 0 <= mp -> mp + 8 <= 2^64 -> bv_unsigned sp + 48 <= mp \/ mp + 8 <= bv_unsigned sp ->
  mem_inv ctusegs m -> bv_unsigned sp + 48 <= 2^64 ->
  wr_at ctusegs m (S - 3) (E - S + 3) -> bytes_at ctusegs m (P - 3) [b8 b3] -> Z.land b3 31 = idx -> 0 <= b3 < 256 ->
  0 <= Bb -> Bb mod 16 = 0 -> 16 <= stride -> stride mod 16 = 0 -> 0 <= idx < 32 -> E + 5 <= 2^63 ->
  S <= P -> P mod 16 = 0 -> P - S <= 16 * 255 -> 0 <= n -> (al = 32 \/ al = 64) -> P + n + al - 16 <= E ->
  E - P - n + al < 2^31 -> (idx = 0 \/ stride * (idx + 1) < 2^20) ->
  (E <= bv_unsigned sp \/ bv_unsigned sp + 48 <= S - 3) -> (E <= mp \/ mp + 8 <= S - 3) ->
  evt ctusegs (raligned_ret_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 s0v s1v F fc
               (raligned_mem m P S E n idx b3 adj ((P' - S0) / 16)) P' mp)
      (MS (mkR ra sp gp tp (Z_to_bv 64 467628) (Z_to_bv 64 (sc * 2)) t2 (Z_to_bv 64 al) s1 (Z_to_bv 64 P) (Z_to_bv 64 idx) (Z_to_bv 64 n) (wz q) (Z_to_bv 64 Bb) (wz mword)
               (Z_to_bv 64 last_idx) (Z_to_bv 64 (idx + 1)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b4e14) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until junk. intros mword stride S0 S E adj P' RS Q16 LI FB SC ML Hml SC48 P0.
  intros FR WMP MP0 MP1 MPD MI SPB W BK B31 B3 BB0 BB16 S16 SM16 IDX E63 SP P16 OFF N0 HAL PNE R31 Q20 DJF DJM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (PR : 0 < P < 2^63) by (clear - P0 PNE N0 HAL E63; lia).
  hide MP0; hide MP1; hide MPD; hide SPB; hide BB0; hide BB16; hide S16; hide SM16; hide IDX; hide E63; hide SP; hide P16; hide OFF; hide N0;
  hide HAL; hide PNE; hide R31; hide Q20; hide DJF; hide DJM; hide SPR; hide B31; hide B3.
  assert (MW4 : Z.shiftr mword 12 = maplen).
  { subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.div_add, Z.div_small by lia. lia. }
  assert (GO : forall x5 x6 x13 x15 x28,
    evt ctusegs (raligned_ret_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 s0v s1v F fc (raligned_mem m P S E n idx b3 adj ((P' - S0) / 16)) P' mp)
      (MS (mkR ra sp gp tp x5 x6 (Z_to_bv 64 (- P)) (Z_to_bv 64 al) s1 (Z_to_bv 64 P) (Z_to_bv 64 idx) (Z_to_bv 64 n) x13 (Z_to_bv 64 Bb) x15
               (Z_to_bv 64 stride) (Z_to_bv 64 (idx + 1)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
          F (Z_to_bv 64 0x2b4e40) fc None m (seg_rom ctusegs))).
  { intros. unhide. subst S E S0. eapply (raligned_store_walk) with (Bb := Bb) (stride := stride) (idx := idx) (b3 := b3); try eassumption; try lia. }
  (* [comment removed for export] *)
  st1. rewrite ?(wz_unsigned mword), MW4 by lia. st1. replace (0 - P) with (- P) by lia.
  st1. if_cases K; zify_cond K; rewrite ?wz_unsigned, ?unsigned_lit in K by lia.
  - (* [comment removed for export] *)
    assert (STR : stride = 16 * size_class sc).
    { unfold stride. rewrite (proj2 (Z.eqb_eq _ _) K), andb_false_r. reflexivity. }
    assert (SCLT : sc < 48) by (apply SC48; left; exact K).
    assert (RS' : ov_read_bytes ctusegs m (Z_to_bv 64 (467628 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
    { replace (Z_to_bv 64 (467628 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact (RS SCLT). }
    pose proof (size_class_range sc ltac:(lia)) as SZ.
    st1. st1. try rewrite (Z.mod_small (size_class sc)) by lia.
    st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
    replace (Z_to_bv 64 (size_class sc * 16)) with (Z_to_bv 64 stride) by (rewrite STR; f_equal; lia).
    apply GO.
  - (* [comment removed for export] *)
    st1. st1. st1. if_cases K2; zify_cond K2.
    2:{ exfalso. rewrite Z.shiftl_mul_pow2 in K2 by lia. change (2^8) with 256 in K2. change 18446744073709551615 with (Z.ones 64) in K2.
        rewrite Z.land_ones, wz_unsigned in K2 by lia. rewrite Z.mod_small in K2 by lia. specialize (Hml K). lia. }
    (* [comment removed for export] *)
    assert (MW1 : Z.land mword 31 = last_idx).
    { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
      replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
    + (* [comment removed for export] *)
      assert (STR : stride = 4096 * maplen - 16).
      { unfold stride. rewrite (proj2 (Z.eqb_eq _ _) K3). replace (maplen =? 0) with false by (symmetry; apply Z.eqb_neq; exact K). reflexivity. }
      assert (MWP : mword - mword mod 4096 = 4096 * maplen).
      { subst mword. replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
        rewrite Z.mod_add, Z.mod_small by lia. lia. }
      st1. st1. rewrite ?(wz_unsigned mword), land_pgmask by lia. rewrite MWP. st1.
      replace (Z_to_bv 64 (4096 * maplen + -16)) with (Z_to_bv 64 stride) by (rewrite STR; f_equal; lia).
      st1. apply GO.
    + (* [comment removed for export] *)
      assert (STR : stride = 16 * size_class sc).
      { unfold stride. rewrite (proj2 (Z.eqb_neq _ _) K3). reflexivity. }
      assert (SCLT : sc < 48) by (apply SC48; right; exact K3).
      assert (RS' : ov_read_bytes ctusegs m (Z_to_bv 64 (467628 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
      { replace (Z_to_bv 64 (467628 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact (RS SCLT). }
      pose proof (size_class_range sc ltac:(lia)) as SZ.
      st1. st1. try rewrite (Z.mod_small (size_class sc)) by lia.
      st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
      replace (Z_to_bv 64 (size_class sc * 16)) with (Z_to_bv 64 stride) by (rewrite STR; f_equal; lia).
      apply GO.
Qed.

(* [comment removed for export] *)
Lemma raligned_hdr_walk : forall (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (ra0 s0v s1v : word) F fc (m : word -> option byte) (P Bb G A n al mp b3 q : Z) (avail freed last_idx freeable sc maplen secret : Z) (prev next : word) (junk : list byte),
  let idx := Z.land b3 31 in
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  let stride := if (last_idx =? 0) && negb (maplen =? 0) then 4096 * maplen - 16 else 16 * size_class sc in
  let S0 := Bb + 16 in let S := S0 + stride * idx in let E := S0 + stride * (idx + 1) - 4 in
  let adj := (- P) mod al in let P' := P + adj in
  (* [comment removed for export] *)
  P mod 16 = 0 -> 16 * q + 16 <= P -> P + 16 <= 2^64 -> Bb = P - 16 * q - 16 -> A = G - G mod 4096 -> 0 <= G -> G + 40 <= 2^64 ->
  ov_read_bytes ctusegs m (wa (P - 4)) 1 = Some [b8 0] ->
  ov_read_bytes ctusegs m (wa (P - 3)) 1 = Some [b8 b3] ->
  ov_read_bytes ctusegs m (wa (P - 2)) 2 = Some (le2 (wz q)) ->
  ov_read_bytes ctusegs m (wa Bb) 8 = Some (le8 (wz G)) ->
  rw_cells ctusegs m G [C8 prev; C8 next; C8 (wz Bb); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
  ov_read_bytes ctusegs m (wa A) 8 = Some (le8 (wz secret)) ->
  ov_read_bytes ctusegs m (wa RCTX) 8 = Some (le8 (wz secret)) ->
  (sc < 48 -> ov_read_bytes ctusegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
  0 <= b3 < 256 -> 0 <= q < 65536 -> 0 <= avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= secret < 2^64 ->
  0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
  idx <= last_idx -> Z.testbit avail idx = false -> Z.testbit freed idx = false ->
  (sc < 48 -> size_class sc * idx <= q < size_class sc * (idx + 1)) -> (48 <= sc -> sc = 63) ->
  (maplen <> 0 -> q <= maplen * 256 - 1) -> (maplen = 0 \/ last_idx <> 0 -> sc < 48) -> 0 < P ->
  (* [comment removed for export] *)
  rw_cells ctusegs m (bv_unsigned sp) [CB 8 junk; C8 s1v; C8 (Z_to_bv 64 mp); C8 (Z_to_bv 64 0x2b4c40); C8 s0v; C8 ra0] ->
  wr_at ctusegs m mp 8 -> 0 <= mp -> mp + 8 <= 2^64 -> bv_unsigned sp + 48 <= mp \/ mp + 8 <= bv_unsigned sp ->
  mem_inv ctusegs m -> bv_unsigned sp + 48 <= 2^64 ->
  wr_at ctusegs m (S - 3) (E - S + 3) -> bytes_at ctusegs m (P - 3) [b8 b3] ->
  0 <= Bb -> Bb mod 16 = 0 -> 16 <= stride -> stride mod 16 = 0 -> E + 5 <= 2^63 ->
  S <= P -> P - S <= 16 * 255 -> 0 <= n -> (al = 32 \/ al = 64) -> P + n + al - 16 <= E ->
  E - P - n + al < 2^31 -> (idx = 0 \/ stride * (idx + 1) < 2^20) ->
  (E <= bv_unsigned sp \/ bv_unsigned sp + 48 <= S - 3) -> (E <= mp \/ mp + 8 <= S - 3) ->
  evt ctusegs (raligned_ret_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 s0v s1v F fc
               (raligned_mem m P S E n idx b3 adj ((P' - S0) / 16)) P' mp)
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 al) (Z_to_bv 64 n) (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b4d18) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until junk. intros idx mword stride S0 S E adj P' AL PLO PHI HB HA GLO GHI R4 R3 R2 RG MM RA RC RS B3 Q16 AV FRD SE LI FB SC ML
    Hidx Hav Hfr Hsc Hsc63 Hml SC48 P0.
  intros FR WMP MP0 MP1 MPD MI SPB W BK BB0 BB16 S16 SM16 E63 SP OFF N0 HAL PNE R31 Q20 DJF DJM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  assert (NR : 0 <= n < 2^63) by (clear - P0 PNE N0 HAL E63; lia).
  hide MP0; hide MP1; hide MPD; hide SPB; hide BB0; hide BB16; hide S16; hide SM16; hide E63; hide SP; hide OFF; hide N0;
  hide HAL; hide PNE; hide R31; hide Q20; hide DJF; hide DJM; hide SPR; hide Hml; hide SC48.
  (* [comment removed for export] *)
  st1. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by lia; lia|]. clear KZ.
  (* [comment removed for export] *)
  st1. st1. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. change 15 with (2^4 - 1) in K. rewrite zb_land_mask in K by lia. lia. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. fold idx. st1. st1. try (if_cases K2; zify_cond K2; [| exfalso; apply K2; rewrite ?zxb_b8, ?wz_unsigned, ?unsigned_lit by lia; reflexivity]).
  (* [comment removed for export] *)
  st1. rewrite ?(wz_unsigned q), Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
  st1. rewrite ?(unsigned_lit P) by lia.
  assert (RG' : ov_read_bytes ctusegs m (Z_to_bv 64 (P - q * 16 + -16)) 8 = Some (le8 (wz G))).
  { replace (P - q * 16 + -16) with Bb by lia. exact RG. }
  st1.
  set (gw := wz G) in *. assert (HG : bv_unsigned gw = G) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. clearbody gw.
  assert (GW : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  st1. st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K3 by lia. lia. }
  (* [comment removed for export] *)
  assert (MW1 : Z.land mword 31 = last_idx).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  st1. st1. rewrite ?(wz_unsigned mword), MW1 by lia. st1. if_cases K4; zify_cond K4. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K4 by lia. lia. }
  (* [comment removed for export] *)
  st1. rewrite sx32_wz_sxv by lia. st1. st1.
  rewrite ?(unsigned_lit idx) by lia. rewrite sllw1_word' by lia.
  assert (P2 : 0 <= 2 ^ idx < 2^32) by (split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
  pose proof (sxv_range avail) as SXA. pose proof (sxv_range (2 ^ idx)) as SXI.
  assert (LA : Z.land avail (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit avail idx ltac:(lia) ltac:(lia))); exact Hav).
  assert (LF : Z.land freed (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit freed idx ltac:(lia) ltac:(lia))); exact Hfr).
  st1. rewrite sxv_land, LA, (sxv_small 0) by lia. st1. if_cases K5; zify_cond K5. 2:{ exfalso. apply K5. reflexivity. }
  (* [comment removed for export] *)
  pose proof (sxv_range freed) as SXF.
  st1. rewrite sx32_wz_sxv by lia. st1. rewrite sxv_land, LF, (sxv_small 0) by lia. st1. if_cases K6; zify_cond K6. 2:{ exfalso. apply K6. reflexivity. }
  (* [comment removed for export] *)
  st1. st1. rewrite land_pgmask by lia. rewrite HG, <- HA. st1. unfold RCTX in RC. st1. st1. st1.
  if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned in K7 by lia. lia. }
  (* [comment removed for export] *)
  assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl mword 52))) 58 = sc).
  { rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. subst mword.
    replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) * 2 ^ 52)
      with ((last_idx + 32 * freeable + 64 * sc) * 2^52 + maplen * 2^64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
    replace ((last_idx + 32 * freeable + 64 * sc) * 2 ^ 52) with ((last_idx + 32 * freeable) * 2^52 + sc * 2^58) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  assert (TAIL : forall x7 x28,
    evt ctusegs (raligned_ret_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 s0v s1v F fc (raligned_mem m P S E n idx b3 adj ((P' - S0) / 16)) P' mp)
      (MS (mkR ra sp gp tp (Z_to_bv 64 467628) (Z_to_bv 64 (sc * 2)) x7 (Z_to_bv 64 al) (Z_to_bv 64 n) (Z_to_bv 64 P) (Z_to_bv 64 idx) (Z_to_bv 64 n) (wz q) (Z_to_bv 64 Bb) (wz mword)
               (Z_to_bv 64 last_idx) (Z_to_bv 64 (idx + 1)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6) F (Z_to_bv 64 0x2b4e14) fc None m (seg_rom ctusegs))).
  { intros. unhide. subst S E S0 P' adj. eapply raligned_h2; try eassumption; try lia. }
  st1. rewrite ?(wz_unsigned mword) by lia. st1. st1. st1. rewrite MW2. st1. st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2.
  st1. rewrite ?(unsigned_lit idx) by lia. st1. if_cases K8; zify_cond K8.
  - (* [comment removed for export] *)
    specialize (Hsc63 ltac:(rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia; lia)).
    st1. st1. if_cases K9; zify_cond K9. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia. lia. }
    rewrite ?GW. apply TAIL.
  - (* [comment removed for export] *)
    assert (SCLT : sc < 48) by (rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia; lia).
    specialize (RS SCLT). specialize (Hsc SCLT).
    assert (RS' : ov_read_bytes ctusegs m (Z_to_bv 64 (467628 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
    { replace (Z_to_bv 64 (467628 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
    pose proof (size_class_range sc ltac:(lia)) as SZ.
    st1. st1. try rewrite (Z.mod_small (size_class sc)) by lia.
    st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }
    st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
    st1. rewrite ?GW. apply TAIL.
Qed.
End WithCeiling0.
