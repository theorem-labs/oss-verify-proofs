(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import MRep MRepAux W_ge3a6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Definition allzerop_res (sc last_idx maplen : Z) : Z :=
  if 48 <=? sc then 1
  else if (maplen =? 0) || negb (last_idx =? 0) then 0
  else if maplen * 4096 - 16 <? 16 * size_class sc then 1 else 0.

Definition allzerop_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a7 : word) (res : Z)
   (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 a4 a5 a6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz res) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom rsegs).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma testbit_split_k k x y i : 0 <= k -> 0 <= x < 2^k -> 0 <= i ->
  Z.testbit (x + 2^k * y) i = if i <? k then Z.testbit x i else Z.testbit y (i - k).
Proof.
  intros Hk Hx Hi. destruct (Z.ltb_spec0 i k).
  - rewrite <- (Z.mod_pow2_bits_low _ k) by lia.
    rewrite (Z.mul_comm (2^k) y), Z.mod_add, Z.mod_small by lia. reflexivity.
  - replace i with ((i - k) + k) at 1 by lia. rewrite <- Z.div_pow2_bits by lia.
    rewrite (Z.mul_comm (2^k) y), Z.div_add, Z.div_small, Z.add_0_l by lia. reflexivity.
Qed.

Lemma land_split_k k x y x' y' : 0 <= k -> 0 <= x < 2^k -> 0 <= x' < 2^k ->
  Z.land (x + 2^k * y) (x' + 2^k * y') = Z.land x x' + 2^k * Z.land y y'.
Proof.
  intros Hk Hx Hx'.
  pose proof (land_lt_pow2 x x' k ltac:(lia) ltac:(lia)) as Hl.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, !testbit_split_k by lia.
  destruct (i <? k); rewrite Z.land_spec; reflexivity.
Qed.

Lemma mword_c00 last_idx freeable sc maplen :
  0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen ->
  Z.land (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) 3072 = 1024 * (sc / 16).
Proof.
  intros LI FB SC ML.
  replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen)
     with ((last_idx + 32 * freeable + 64 * (sc mod 16)) + 2^10 * (sc / 16 + 4 * maplen)) by (Z.div_mod_to_equations; lia).
  change 3072 with (0 + 2^10 * 3).
  rewrite land_split_k by (Z.div_mod_to_equations; lia). rewrite Z.land_0_r.
  change 3 with (2^2 - 1). rewrite zb_land_mask by lia. change (2^2) with 4. change (2^10) with 1024.
  rewrite (Z.mul_comm 4 maplen), Z.mod_add by lia. rewrite Z.mod_small by (Z.div_mod_to_equations; lia). lia.
Qed.

Lemma mword_maplen last_idx freeable sc maplen :
  0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen ->
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  mword - mword mod 4096 = 4096 * maplen.
Proof.
  intros LI FB SC ML mword. subst mword.
  replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
  rewrite Z.mod_add, Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma allzerop_tail88 : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m
   (last_idx freeable sc maplen : Z),
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
  (sc < 48 -> ov_read_bytes rsegs m (wa (SIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
  evt rsegs (allzerop_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a7 (allzerop_res sc last_idx maplen) F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz mword) a1 (wz last_idx) (wz maplen) (wz sc) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x24b64) fc None m (seg_rom rsegs)).
Proof.
  intros until maplen. intros mword LI FB SC ML RS.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (MWC : Z.land mword 3072 = 1024 * (sc / 16)) by (subst mword; apply mword_c00; lia).
  assert (MWM : mword - mword mod 4096 = 4096 * maplen) by (subst mword; apply mword_maplen; lia).
  assert (RS' : sc < 48 -> ov_read_bytes rsegs m (Z_to_bv 64 (85160 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
  { intros H. replace (Z_to_bv 64 (85160 + sc * 2)) with (wa (SIZE_CLASSES + 2 * sc)) by (unfold wa, SIZE_CLASSES; f_equal; lia). exact (RS H). }
  clear RS.
  st1. st1. st1. rewrite MWC. st1. if_cases K; zify_cond K; rewrite ?wz_unsigned, ?unsigned_lit in K by (Z.div_mod_to_equations; lia).
  - (* [comment removed for export] *)
    assert (SC48 : sc < 48) by (Z.div_mod_to_equations; lia).
    specialize (RS' SC48). pose proof (size_class_range sc ltac:(lia)) as SZ.
    replace (allzerop_res sc last_idx maplen)
       with (if (maplen =? 0) || negb (last_idx =? 0) then 0 else if maplen * 4096 - 16 <? 16 * size_class sc then 1 else 0)
       by (unfold allzerop_res; destruct (Z.leb_spec0 48 sc); [lia| reflexivity]).
    st1. if_cases K2; zify_cond K2; rewrite ?wz_unsigned in K2 by lia.
    + (* [comment removed for export] *)
      st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2.
      st1. st1. st1. st1. try rewrite (Z.mod_small (size_class sc)) by lia. st1. st1. rewrite v_sltu_b2z, Z.ltb_irrefl. cbn [Z.b2z]. st1.
      rewrite (proj2 (Z.eqb_eq maplen 0) K2). cbn [orb]. unfold allzerop_post. finish.
    + (* [comment removed for export] *)
      st1. if_cases K3; zify_cond K3; rewrite ?wz_unsigned in K3 by lia.
      * (* [comment removed for export] *)
        st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2.
        st1. st1. st1. st1. try rewrite (Z.mod_small (size_class sc)) by lia. st1. st1. rewrite v_sltu_b2z, Z.ltb_irrefl. cbn [Z.b2z]. st1.
        replace ((maplen =? 0) || negb (last_idx =? 0)) with true by (symmetry; apply orb_true_intro; right; apply (proj2 (negb_true_iff _)); apply Z.eqb_neq; lia).
        unfold allzerop_post. finish.
      * (* [comment removed for export] *)
        st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2.
        st1. st1. st1. st1. try rewrite (Z.mod_small (size_class sc)) by lia.
        st1. st1. rewrite land_pgmask by lia. rewrite MWM.
        st1. st1. st1.
        rewrite v_sltu_b2z, Z.shiftl_mul_pow2, !unsigned_lit by lia. change (2^4) with 16.
        replace (Z.b2z (4096 * maplen + -16 <? size_class sc * 16)) with (if maplen * 4096 - 16 <? 16 * size_class sc then 1 else 0)
          by (replace (4096 * maplen + -16 <? size_class sc * 16) with (maplen * 4096 - 16 <? 16 * size_class sc) by (f_equal; lia);
              destruct (maplen * 4096 - 16 <? 16 * size_class sc); reflexivity).
        st1.
        replace ((maplen =? 0) || negb (last_idx =? 0)) with false by (symmetry; apply orb_false_intro; [apply Z.eqb_neq; lia| apply (proj2 (negb_false_iff _)); apply Z.eqb_eq; lia]).
        unfold allzerop_post. finish.
  - (* [comment removed for export] *)
    st1. st1.
    replace (allzerop_res sc last_idx maplen) with 1 by (unfold allzerop_res; destruct (Z.leb_spec0 48 sc); [reflexivity| Z.div_mod_to_equations; lia]).
    unfold allzerop_post. finish.
Qed.


(* [comment removed for export] *)
Lemma allzerop_tail : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m
   (off16 last_idx freeable sc maplen : Z),
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  0 <= off16 < 65536 -> 0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
  (maplen <> 0 -> off16 <= maplen * 256 - 1) ->
  (sc < 48 -> ov_read_bytes rsegs m (wa (SIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
  evt rsegs (allzerop_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a7 (allzerop_res sc last_idx maplen) F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz mword) (wz off16) (wz last_idx) a3 (wz sc) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x24b4c) fc None m (seg_rom rsegs)).
Proof.
  intros until maplen. intros mword O16 LI FB SC ML Hml RS.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (MW4 : Z.shiftr mword 12 = maplen).
  { subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.div_add, Z.div_small by lia. lia. }
  st1. rewrite MW4. st1. if_cases K; zify_cond K; rewrite ?wz_unsigned in K by lia.
  - eapply allzerop_tail88; eauto.
  - st1. st1. st1. if_cases K2; zify_cond K2.
    + eapply allzerop_tail88; eauto.
    + exfalso. rewrite Z.shiftl_mul_pow2 in K2 by lia. change (2^8) with 256 in K2.
      rewrite wz_unsigned in K2 by lia. rewrite Z.mod_small in K2 by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma allzerop_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
   (P G B A : Z) (b3 off16 avail freed last_idx freeable sc maplen secret: Z) (prev next : word),
  let idx := Z.land b3 31 in
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  bv_unsigned a0 = P -> P mod 16 = 0 -> 16 * off16 + 16 <= P -> P + 16 <= 2^64 ->
  B = P - 16 * off16 - 16 -> A = G - G mod 4096 -> 0 <= G -> G + 40 <= 2^64 ->
  ov_read_bytes rsegs m (wa (P - 4)) 1 = Some [b8 0] ->
  ov_read_bytes rsegs m (wa (P - 3)) 1 = Some [b8 b3] ->
  ov_read_bytes rsegs m (wa (P - 2)) 2 = Some (le2 (wz off16)) ->
  ov_read_bytes rsegs m (wa B) 8 = Some (le8 (wz G)) ->
  rw_cells rsegs m G [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
  ov_read_bytes rsegs m (wa A) 8 = Some (le8 (wz secret)) ->
  ov_read_bytes rsegs m (wa CTX) 8 = Some (le8 (wz secret)) ->
  (sc < 48 -> ov_read_bytes rsegs m (wa (SIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
  0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= secret < 2^64 ->
  0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
  idx <= last_idx -> Z.testbit avail idx = false -> Z.testbit freed idx = false ->
  (sc < 48 -> size_class sc * idx <= off16 < size_class sc * (idx + 1)) ->
  (48 <= sc -> sc = 63) ->
  (maplen <> 0 -> off16 <= maplen * 256 - 1) ->
  evt rsegs (allzerop_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a7 (allzerop_res sc last_idx maplen) F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x24a58) fc None m (seg_rom rsegs)).
Proof.
  intros until next. intros idx mword HP AL PLO PHI HB HA GLO GHI R4 R3 R2 RG MM RA RC RS B3 O16 AV FR SE LI FB SC ML
    Hidx Hav Hfr Hsc Hsc63 Hml.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  st1. st1. if_cases K; zify_cond K. 2:{ exfalso. change 15 with (2^4 - 1) in K. rewrite zb_land_mask in K by lia. lia. }
  st1. st1. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
  st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
  st1.
  (* [comment removed for export] *)
  assert (RG' : ov_read_bytes rsegs m (Z_to_bv 64 (P - off16 * 16 + -16)) 8 = Some (le8 (wz G))).
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
  st1. st1. rewrite land_pgmask by lia. rewrite HG, <- HA. st1. st1. unfold CTX in RC. st1. st1.
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
    eapply allzerop_tail; eauto.
  - pose proof (RS ltac:(rewrite ?wz_unsigned in K8 by lia; lia)) as RS0. specialize (Hsc ltac:(rewrite ?wz_unsigned in K8 by lia; lia)).
    st1. st1. st1. st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2.
    assert (RS' : ov_read_bytes rsegs m (Z_to_bv 64 (85160 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
    { replace (Z_to_bv 64 (85160 + sc * 2)) with (wa (SIZE_CLASSES + 2 * sc)) by (unfold wa, SIZE_CLASSES; f_equal; lia). exact RS0. }
    clear RS0. pose proof (size_class_range sc ltac:(lia)) as SZ. st1.
    try rewrite (Z.mod_small (size_class sc)) by lia. fold idx.
    st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }
    st1. st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
    st1. eapply allzerop_tail; eauto.
Qed.


(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Lemma allzerop_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    st (p : aptr) r g gh ar (b3 lo hi : Z),
  let sh := get_shadow st (fst p) in
  let po := snd p in
  let off16 := lo + 256 * hi in
  let idx := Z.land b3 31 in
  let base := aadd p (- (UNIT * off16) - UNIT) in
  let mr := get_meta_rec st g in
  mrep st m -> mem_inv rsegs m ->
  (s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
  bv_unsigned a0 = r_base r + po -> po mod 16 = 0 ->
  16 <= po -> 16 * off16 + 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
  cell_read sh (po - 4) = Known 0 -> cell_read sh (po - 3) = Known b3 ->
  cell_read sh (po - 2) = Known lo -> cell_read sh (po - 1) = Known hi ->
  (s_groups st) !! base = Some gh -> g_meta gh = Some g -> meta_slot st g -> 0 <= snd g ->
  m_mem mr = Some base ->
  (s_areas st) !! (area_of g) = Some ar -> a_check ar = c_secret (ctx st) ->
  0 <= m_avail mr < 2^32 -> 0 <= m_freed mr < 2^32 -> 0 <= c_secret (ctx st) < 2^64 ->
  0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
  idx <= m_last_idx mr -> Z.testbit (m_avail mr) idx = false -> Z.testbit (m_freed mr) idx = false ->
  (m_sizeclass mr < 48 -> size_class (m_sizeclass mr) * idx <= off16 < size_class (m_sizeclass mr) * (idx + 1)) ->
  (48 <= m_sizeclass mr -> m_sizeclass mr = 63) ->
  (m_maplen mr <> 0 -> off16 <= m_maplen mr * 256 - 1) ->
  evt rsegs (allzerop_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a7
               (allzerop_res (m_sizeclass mr) (m_last_idx mr) (m_maplen mr)) F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 allzerop_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until hi. intros sh po off16 idx base mr MR MI Hr Hk HP AL P16 PLO PHI C4 C3 C2 C1 Hgh Hg MS G0 Hmem Har Hchk
         AV FR SE LI FB SC ML Hidx Hav Hfr Hsc Hsc63 Hml.
  (first [ pose proof (MR) as dR_1; dand6 dR_1 as WF CX GL AR GR SH | pose proof MR as (WF & CX & GL & AR & GR & SH) ]).
  (first [ dand5 WF as Hres WR DISJ WA WG | destruct WF as (Hres & WR & DISJ & WA & WG) ]).
  (first [ pose proof ((WR (fst p) r Hr)) as dR_3; dand5 dR_3 as B0 BAL L0 BC _ | destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  (* [comment removed for export] *)
  destruct (mrep_shadow_read (Clg:=Clg) (Rr:=Rr) st m (fst p) r (po - 4) 0 MR Hr Hk ltac:(lia) C4) as [R4 _].
  destruct (mrep_shadow_read (Clg:=Clg) (Rr:=Rr) st m (fst p) r (po - 3) b3 MR Hr Hk ltac:(lia) C3) as [R3 B3].
  (first [ pose proof ((mrep_shadow_read2 (Clg:=Clg) (Rr:=Rr) st m (fst p) r (po - 2) lo hi MR Hr Hk ltac:(lia) ltac:(lia) C2 ltac:(replace (po - 2 + 1) with (po - 1) by lia; exact C1))) as dR_4; dand3 dR_4 as R2 LO HI | destruct (mrep_shadow_read2 (Clg:=Clg) (Rr:=Rr) st m (fst p) r (po - 2) lo hi MR Hr Hk ltac:(lia) ltac:(lia) C2 ltac:(replace (po - 2 + 1) with (po - 1) by lia; exact C1)) as (R2 & LO & HI) ]).
  rewrite <- le2_lohi in R2 by lia.
  (* [comment removed for export] *)
  destruct (mrep_group_read st m base gh MR Hgh) as [RG _]. rewrite Hg in RG. cbn [pw oconc] in RG.
  (* [comment removed for export] *)
  pose proof (mrep_meta_chunk st m g MR MS) as MM. fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.
  (* [comment removed for export] *)
  pose proof (mrep_area_check_read st m (area_of g) ar MR Har) as RA. rewrite Hchk in RA.
  pose proof (mrep_ctx_secret_read st m MR) as RC.
  (* [comment removed for export] *)
  (first [ pose proof ((WG base gh Hgh)) as dR_5; dex1 dR_5 as rb; dand4 dR_5 as Hrb _ Bb0 _ | pose proof ((WG base gh Hgh)) as dR_5; dand5 dR_5 as rb Hrb _ Bb0 _ | destruct (WG base gh Hgh) as (rb & Hrb & _ & Bb0 & _) ]). cbn [base aadd fst] in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb.
  assert (HB : conc st base = (r_base r + po) - 16 * off16 - 16).
  { unfold base. rewrite conc_aadd by (rewrite Hr; eauto). rewrite (conc_region' st p r Hr). unfold po, UNIT. lia. }
  (first [ dex3 MS as a ara k; dand3 MS as Ha Hkk Eg | dand6 MS as a ara k Ha Hkk Eg | destruct MS as (a & ara & k & Ha & Hkk & Eg) ]).
  (first [ pose proof ((WA a ara Ha)) as dR_7; dex1 dR_7 as rg; dand6 dR_7 as Hrg A0 A1 AAL ANG _ | pose proof ((WA a ara Ha)) as dR_7; dand7 dR_7 as rg Hrg A0 A1 AAL ANG _ | destruct (WA a ara Ha) as (rg & Hrg & A0 & A1 & AAL & ANG & _) ]).
  assert (HG : conc st g = r_base rg + snd a + (AREA_HDR + META_SIZE * k)).
  { rewrite Eg, conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a rg Hrg). reflexivity. }
  (first [ pose proof ((WR (fst a) rg Hrg)) as dR_8; dand5 dR_8 as RB0 RBAL RL0 RBC _ | destruct (WR (fst a) rg Hrg) as (RB0 & RBAL & RL0 & RBC & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
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
  unfold allzerop_entry.
  eapply (allzerop_walk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
            (r_base r + po) (conc st g) (conc st base) (conc st (area_of g)) b3 off16 (m_avail mr) (m_freed mr)
            (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (c_secret (ctx st))
            (pw st (m_prev mr)) (pw st (m_next mr))); try eassumption; try lia.
  - replace (r_base r + po - 4) with (r_base r + (po - 4)) by lia. exact R4.
  - replace (r_base r + po - 3) with (r_base r + (po - 3)) by lia. exact R3.
  - replace (r_base r + po - 2) with (r_base r + (po - 2)) by lia. exact R2.
  - intros Hlt. apply size_classes_read; [exact MI | lia].
Qed.

End CEIL.
