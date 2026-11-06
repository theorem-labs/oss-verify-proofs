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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRep MRepAux W_ge3a6 W_al5bs.

Module W_re997.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import MRep MRepAux W_ge3a6 W_al5bs.
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

(* [comment removed for export] *)
Definition SIZE_OVF : Z := 0x7fffffffffffefff.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition realloc_entry_post (sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra : word)
   (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists m1,
    ms' = MS (mkR ra (wz (bv_unsigned sp - 64)) gp tp t0 t1 t2 s0 s1 a0 a1 (wz SIZE_OVF) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x2488c) fc None m1 (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
    /\ rw_cells rsegs m1 (bv_unsigned sp - 64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma realloc_entry_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
   (j0 j1 j2 j3 j4 j5 j6 j7 : word) (P N : Z),
  bv_unsigned a0 = P -> P <> 0 -> bv_unsigned a1 = N -> N < SIZE_OVF ->
  64 <= bv_unsigned sp ->
  rw_cells rsegs m (bv_unsigned sp - 64) [C8 j0; C8 j1; C8 j2; C8 j3; C8 j4; C8 j5; C8 j6; C8 j7] -> mem_inv rsegs m ->
  evt rsegs (realloc_entry_post sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 realloc_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until N. intros HA0 PNZ HA1 NOV SPLO FR MI.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (bv_unsigned_in_range _ a0) as A0R. change (bv_modulus 64) with (2^64) in A0R.
  pose proof (bv_unsigned_in_range _ a1) as A1R. change (bv_modulus 64) with (2^64) in A1R.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) in FR by lia.
  unfold realloc_entry, SIZE_OVF in *.
  step. if_cases K; zify_cond K. { exfalso. lia. }
  step. step. step. step. step. step. step. step. step.
  step. step. step. step. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
  replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) in * by lia.
  apply evt_done. unfold realloc_entry_post. eexists. split; [reflexivity|].
  split; [exact MU| split; [exact WM| split; [exact MI| exact FR]]].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stride_of (sc last_idx maplen : Z) : Z :=
  if (last_idx =? 0) && negb (maplen =? 0) then maplen * 4096 - 16 else 16 * size_class sc.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition realloc_getmeta_post (ra sp gp tp s0 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 : word)
   (G B b3 sc mword stride idx last_idx : Z) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t2 t3 t4,
    ms' = MS (mkR ra sp gp tp (wz idx) (wz last_idx) t2 s0 (wz G) a0 a1 (wz B) (wz sc) (wz mword) (wz SIZE_CLASSES) (wz stride) (wz b3)
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x249a8) fc None m (seg_rom rsegs).

(* [comment removed for export] *)
Lemma realloc_gm_tail : forall (ra sp gp tp s0 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m
   (G B b3 off16 last_idx freeable sc maplen idx : Z),
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  0 <= off16 < 65536 -> 0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
  (maplen <> 0 -> off16 <= maplen * 256 - 1) ->
  (maplen = 0 \/ last_idx <> 0 -> sc < 48) ->
  (sc < 48 -> ov_read_bytes rsegs m (wa (SIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
  evt rsegs (realloc_getmeta_post ra sp gp tp s0 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 G B b3 sc mword (stride_of sc last_idx maplen) idx last_idx F fc m)
      (MS (mkR ra sp gp tp (wz idx) (wz last_idx) (Z_to_bv 64 (sc * 2)) s0 (wz G) a0 a1 (wz B) (wz sc) (wz mword) (wz SIZE_CLASSES) (wz off16) (wz b3)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x24980) fc None m (seg_rom rsegs)).
Proof.
  intros until idx. intros mword O16 LI FB SC ML Hml SC48 RS.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (MW4 : Z.shiftr mword 12 = maplen).
  { subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.div_add, Z.div_small by lia. lia. }
  assert (MWM : mword - mword mod 4096 = 4096 * maplen) by (subst mword; apply mword_maplen; lia).
  assert (RS' : sc < 48 -> ov_read_bytes rsegs m (Z_to_bv 64 (85160 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
  { intros H. replace (Z_to_bv 64 (85160 + sc * 2)) with (wa (SIZE_CLASSES + 2 * sc)) by (unfold wa, SIZE_CLASSES; f_equal; lia). exact (RS H). }
  clear RS.
  (* [comment removed for export] *)
  assert (NOM : forall t3' t4', sc < 48 -> stride_of sc last_idx maplen = 16 * size_class sc ->
    evt rsegs (realloc_getmeta_post ra sp gp tp s0 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 G B b3 sc mword (stride_of sc last_idx maplen) idx last_idx F fc m)
      (MS (mkR ra sp gp tp (wz idx) (wz last_idx) (Z_to_bv 64 (sc * 2)) s0 (wz G) a0 a1 (wz B) (wz sc) (wz mword) (wz SIZE_CLASSES) (wz off16) (wz b3)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6) F (Z_to_bv 64 0x2499c) fc None m (seg_rom rsegs))).
  { intros t3' t4' H48 HS. specialize (RS' H48). pose proof (size_class_range sc ltac:(lia)) as SZ. unfold SIZE_CLASSES.
    st1. st1. try rewrite (Z.mod_small (size_class sc)) by lia. st1.
    rewrite Z.shiftl_mul_pow2, ?unsigned_lit by lia. change (2^4) with 16. rewrite HS.
    replace (size_class sc * 16) with (16 * size_class sc) by lia.
    apply evt_done. unfold realloc_getmeta_post, SIZE_CLASSES. do 3 eexists. reflexivity. }
  st1. rewrite MW4. st1. if_cases K; zify_cond K; rewrite ?wz_unsigned in K by lia.
  - (* [comment removed for export] *) apply NOM; [lia|]. unfold stride_of. rewrite (proj2 (Z.eqb_eq maplen 0) K). cbn [negb andb]. destruct (last_idx =? 0); reflexivity.
  - st1. st1. st1. if_cases K2; zify_cond K2.
    2:{ exfalso. rewrite Z.shiftl_mul_pow2 in K2 by lia. change (2^8) with 256 in K2.
        rewrite wz_unsigned in K2 by lia. rewrite Z.mod_small in K2 by lia. lia. }
    st1. if_cases K3; zify_cond K3; rewrite ?wz_unsigned in K3 by lia.
    + (* [comment removed for export] *)
      st1. st1. rewrite land_pgmask by lia. rewrite MWM. st1. st1.
      replace (stride_of sc last_idx maplen) with (maplen * 4096 - 16)
        by (unfold stride_of; rewrite (proj2 (Z.eqb_eq last_idx 0) K3), (proj2 (Z.eqb_neq maplen 0) K); reflexivity).
      replace (4096 * maplen + -16) with (maplen * 4096 - 16) by lia.
      apply evt_done. unfold realloc_getmeta_post. do 3 eexists. reflexivity.
    + apply NOM; [lia|]. unfold stride_of. rewrite (proj2 (Z.eqb_neq last_idx 0) K3). reflexivity.
Qed.


(* [comment removed for export] *)
Lemma realloc_getmeta_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
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
  (maplen = 0 \/ last_idx <> 0 -> sc < 48) ->
  evt rsegs (realloc_getmeta_post ra sp gp tp s0 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 G B b3 sc mword (stride_of sc last_idx maplen) idx last_idx F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2488c) fc None m (seg_rom rsegs)).
Proof.
  intros until next. intros idx mword HP AL PLO PHI HB HA GLO GHI R4 R3 R2 RG MM RA RC RS B3 O16 AV FR SE LI FB SC ML
    Hidx Hav Hfr Hsc Hsc63 Hml SC48.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  (* [comment removed for export] *)
  st1. st1. if_cases K; zify_cond K. 2:{ exfalso. change 15 with (2^4 - 1) in K. rewrite zb_land_mask in K by lia. lia. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
  (* [comment removed for export] *)
  st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
  st1.
  assert (RG' : ov_read_bytes rsegs m (Z_to_bv 64 (P - off16 * 16 + -16)) 8 = Some (le8 (wz G))).
  { replace (P - off16 * 16 + -16) with B by lia. exact RG. }
  st1.
  set (gw := wz G) in *. assert (HG : bv_unsigned gw = G) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. clearbody gw.
  assert (GW : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
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
  st1. st1. st1. rewrite land_pgmask by lia. rewrite HG, <- HA. st1. unfold CTX in RC. st1. st1.
  if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned in K7 by lia. lia. }
  (* [comment removed for export] *)
  assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl mword 52))) 58 = sc).
  { rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. subst mword.
    replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) * 2 ^ 52)
      with ((last_idx + 32 * freeable + 64 * sc) * 2^52 + maplen * 2^64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
    replace ((last_idx + 32 * freeable + 64 * sc) * 2 ^ 52) with ((last_idx + 32 * freeable) * 2^52 + sc * 2^58) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  st1. st1. st1. st1. rewrite MW2. st1. rewrite (Z.shiftl_mul_pow2 sc 1), ?(unsigned_lit sc) by lia. change (2^1) with 2.
  st1. st1. if_cases K8; zify_cond K8.
  - (* [comment removed for export] *) specialize (Hsc63 ltac:(rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia; lia)).
    st1. st1. if_cases K9; zify_cond K9. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia. lia. }
    rewrite GW. eapply realloc_gm_tail; eauto.
  - pose proof (RS ltac:(rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia; lia)) as RS0. specialize (Hsc ltac:(rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia; lia)).
    assert (RS' : ov_read_bytes rsegs m (Z_to_bv 64 (85160 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
    { replace (Z_to_bv 64 (85160 + sc * 2)) with (wa (SIZE_CLASSES + 2 * sc)) by (unfold wa, SIZE_CLASSES; f_equal; lia). exact RS0. }
    clear RS0. pose proof (size_class_range sc ltac:(lia)) as SZ.
    (* [comment removed for export] *)
    st1. st1. try rewrite (Z.mod_small (size_class sc)) by lia. fold idx.
    st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }
    (* [comment removed for export] *)
    st1. st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
    st1. rewrite GW. eapply realloc_gm_tail; eauto.
Qed.


Lemma stride_of_get_stride mr : stride_of (m_sizeclass mr) (m_last_idx mr) (m_maplen mr) = get_stride mr.
Proof. unfold stride_of, get_stride, UNIT. reflexivity. Qed.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling} {Rr : MRep.RunRandom}.  (* [comment removed for export] *)

Lemma realloc_getmeta_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
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
  (m_maplen mr = 0 \/ m_last_idx mr <> 0 -> m_sizeclass mr < 48) ->
  evt rsegs (realloc_getmeta_post ra sp gp tp s0 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6
               (conc st g) (conc st base) b3 (m_sizeclass mr) (meta_word mr) (get_stride mr) idx (m_last_idx mr) F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2488c) fc None m (seg_rom rsegs)).
Proof.
  intros until hi. intros sh po off16 idx base mr MR MI Hr Hk HP AL P16 PLO PHI C4 C3 C2 C1 Hgh Hg MS G0 Hmem Har Hchk
         AV FR SE LI FB SC ML Hidx Hav Hfr Hsc Hsc63 Hml SC48.
  (first [ pose proof (MR) as dR_1; dand6 dR_1 as WF CX GL AR GR SH | pose proof MR as (WF & CX & GL & AR & GR & SH) ]).
  (first [ dand5 WF as Hres WR DISJ WA WG | destruct WF as (Hres & WR & DISJ & WA & WG) ]).
  (first [ pose proof ((WR (fst p) r Hr)) as dR_3; dand5 dR_3 as B0 BAL L0 BC _ | destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  destruct (mrep_shadow_read (Clg:=Clg) st m (fst p) r (po - 4) 0 MR Hr Hk ltac:(lia) C4) as [R4 _].
  destruct (mrep_shadow_read (Clg:=Clg) st m (fst p) r (po - 3) b3 MR Hr Hk ltac:(lia) C3) as [R3 B3].
  (first [ pose proof ((mrep_shadow_read2 (Clg:=Clg) st m (fst p) r (po - 2) lo hi MR Hr Hk ltac:(lia) ltac:(lia) C2 ltac:(replace (po - 2 + 1) with (po - 1) by lia; exact C1))) as dR_4; dand3 dR_4 as R2 LO HI | destruct (mrep_shadow_read2 (Clg:=Clg) st m (fst p) r (po - 2) lo hi MR Hr Hk ltac:(lia) ltac:(lia) C2 ltac:(replace (po - 2 + 1) with (po - 1) by lia; exact C1)) as (R2 & LO & HI) ]).
  rewrite <- le2_lohi in R2 by lia.
  destruct (mrep_group_read st m base gh MR Hgh) as [RG _]. rewrite Hg in RG. cbn [pw oconc] in RG.
  pose proof (mrep_meta_chunk st m g MR MS) as MM. fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.
  pose proof (mrep_area_check_read st m (area_of g) ar MR Har) as RA. rewrite Hchk in RA.
  pose proof (mrep_ctx_secret_read st m MR) as RC.
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
  rewrite <- stride_of_get_stride. unfold meta_word.
  eapply (realloc_getmeta_walk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
            (r_base r + po) (conc st g) (conc st base) (conc st (area_of g)) b3 off16 (m_avail mr) (m_freed mr)
            (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (c_secret (ctx st))
            (pw st (m_prev mr)) (pw st (m_next mr))); try eassumption; try lia.
  - replace (r_base r + po - 4) with (r_base r + (po - 4)) by lia. exact R4.
  - replace (r_base r + po - 3) with (r_base r + (po - 3)) by lia. exact R3.
  - replace (r_base r + po - 2) with (r_base r + (po - 2)) by lia. exact R2.
  - intros Hlt. apply size_classes_read; [exact MI | lia].
Qed.

End CEIL.
End W_re997.


Module W_reagh.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRep MRepAux W_ge3a6 W_al5bs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RF_m8yt.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_al5bs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_rejt8.W_re997 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_m8yt.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)

Lemma zx32_wz_r x : 0 <= x < 2^32 -> zx32 (wz x) = wz x.
Proof. intros. unfold zx32, wz. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition realloc_geom_post (ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 : word)
   (S E P rsv : Z) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t2 t3 t4,
    ms' = MS (mkR ra sp gp tp (wz E) (wz S) t2 s0 s1 a0 a1 a2 a3 a4 a5 (wz (E + 4)) (wz (E - P))
                  (wz (E - rsv)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x24a18) fc None m (seg_rom rsegs).

Lemma realloc_geom_walk : forall (ra sp gp tp t1 t2 s0 s1 a0 a1 a3 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
   (P B stride idx b3 r32 : Z),
  let S := B + 16 + stride * idx in
  let E := S + stride - 4 in
  let rsv0 := Z.shiftr b3 5 in
  let rsv := if 160 <=? b3 then r32 else rsv0 in
  bv_unsigned a0 = P -> 0 <= B -> 0 <= idx -> 16 <= stride -> E + 5 <= 2^64 -> 0 <= b3 < 256 ->
  P <= E -> rsv <= E - P ->
  (160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32
               /\ ov_read_bytes rsegs m (wa (E - 4)) 4 = Some (le4 (wz r32)) /\ ov_read_bytes rsegs m (wa (E - 5)) 1 = Some [b8 0]) ->
  ov_read_bytes rsegs m (wa (E - rsv)) 1 = Some [b8 0] ->
  ov_read_bytes rsegs m (wa E) 1 = Some [b8 0] ->
  evt rsegs (realloc_geom_post ra sp gp tp s0 s1 a0 a1 (wz B) a3 a4 a5 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 S E P rsv F fc m)
      (MS (mkR ra sp gp tp (wz idx) t1 t2 s0 s1 a0 a1 (wz B) a3 a4 a5 (wz stride) (wz b3) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x249a8) fc None m (seg_rom rsegs)).
Proof.
  intros until r32. intros S E rsv0 rsv HP B0 I0 S16 EHI B3 PE RSV BIG RZ EZ.
  pose proof (bv_unsigned_in_range _ a0) as A0R. change (bv_modulus 64) with (2^64) in A0R.
  assert (SI0 : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (RSV0 : 0 <= rsv0 < 8).
  { unfold rsv0. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  assert (RSVR : 0 <= rsv < 2^32).
  { unfold rsv. destruct (Z.leb_spec 160 b3); [destruct (BIG ltac:(lia)) as (_ & ? & _); lia| lia]. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1.
  replace (B + stride * idx + 16 + stride + -4) with E by (unfold E, S; lia).
  replace (B + stride * idx + 16 + stride) with (E + 4) by (unfold E, S; lia).
  replace (B + stride * idx + 16) with S by (unfold S; lia). fold rsv0.
  (* [comment removed for export] *)
  assert (J : forall a7', evt rsegs (realloc_geom_post ra sp gp tp s0 s1 a0 a1 (wz B) a3 a4 a5 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 S E P rsv F fc m)
      (MS (mkR ra sp gp tp (wz E) (wz S) (wz rsv) s0 s1 a0 a1 (wz B) a3 a4 a5 (wz (E + 4)) a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz 160) t4 t5 t6)
          F (Z_to_bv 64 0x249f0) fc None m (seg_rom rsegs))).
  { intros a7'.
    (* [comment removed for export] *)
    st1. rewrite ?HP. st1. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. }
    (* [comment removed for export] *)
    st1. st1. rewrite ?zxb_b8 by lia. st1. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia. lia. }
    (* [comment removed for export] *)
    st1. rewrite ?zxb_b8 by lia. st1. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K3 by lia. lia. }
    apply evt_done. unfold realloc_geom_post. do 3 eexists. reflexivity. }
  (* [comment removed for export] *)
  st1. if_cases Kb; zify_cond Kb; rewrite ?wz_unsigned, ?unsigned_lit in Kb by lia.
  - (* [comment removed for export] *)
    replace (Z_to_bv 64 rsv0) with (wz rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [lia| reflexivity]).
    apply J.
  - destruct (BIG ltac:(lia)) as (R5 & R32 & RD4 & RD5).
    (* [comment removed for export] *)
    st1. st1. if_cases K5; zify_cond K5. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K5 by lia. lia. }
    (* [comment removed for export] *)
    st1. rewrite zx32_wz_r by lia. st1. st1. if_cases K6; zify_cond K6. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K6 by lia. lia. }
    (* [comment removed for export] *)
    st1. rewrite ?zxb_b8 by lia. st1. if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K7 by lia. lia. }
   
    replace (wz r32) with (wz rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [reflexivity| lia]).
    apply J.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition realloc_stc_post (ra sp gp tp t0 t2 s0 s1 a0 a1 a3 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (N : Z)
   (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t1 a4 a5 a7,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (wz (size_to_class N + 1)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x24bb8) fc None m (seg_rom rsegs).

Lemma realloc_stc_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (N : Z),
  bv_unsigned a1 = N -> 0 <= N < MMAP_THRESHOLD -> mem_inv rsegs m ->
  evt rsegs (realloc_stc_post ra sp gp tp t0 t2 s0 s1 a0 a1 a3 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 N F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 (wz SIZE_CLASSES) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x24a28) fc None m (seg_rom rsegs)).
Proof.
  intros until N. intros HA1 NR MI.
  pose proof (size_to_class_props N NR) as (SCR & SFIT & LG). unfold MMAP_THRESHOLD in NR.
  assert (EA1 : a1 = Z_to_bv 64 N) by (rewrite <- HA1; symmetry; apply Z_to_bv_bv_unsigned). subst a1.
  unfold SIZE_CLASSES.
  (* [comment removed for export] *)
  step. step. step.
  rewrite (unsigned_lit (N + 3)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  set (q := (N + 3) / 16) in *. assert (QR : 0 <= q < 8191) by (subst q; Z.div_mod_to_equations; lia).
  assert (STC : size_to_class N = stc_q q) by (apply size_to_class_q; lia).
  step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit N) in K2 by lia.
  - (* [comment removed for export] *)
    step. rewrite (unsigned_lit q), swrap32_small by lia.
    apply evt_done. unfold realloc_stc_post. do 4 eexists.
    rewrite STC. unfold stc_q. replace (q <? 10) with true by (symmetry; apply Z.ltb_lt; subst q; Z.div_mod_to_equations; lia). reflexivity.
  - (* [comment removed for export] *)
    assert (Q10 : 10 <= q) by (subst q; Z.div_mod_to_equations; lia).
    step. rewrite ?(unsigned_lit q) by lia. set (x := q + 1) in *. assert (XR : 11 <= x < 8192) by lia.
    destruct (clz_pow_eq x XR) as [PW RV4].
    (* [comment removed for export] *)
    step.
    step. rewrite (unsigned_lit x), srliw_small by lia.
    pose proof (shiftr_small 13 x 1 ltac:(lia) ltac:(lia)) as R1. pose proof (shiftr_small 13 x 2 ltac:(lia) ltac:(lia)) as R2.
    step. rewrite (unsigned_lit (Z.shiftr x 2)), (unsigned_lit x) by lia.
    set (v1 := Z.lor (Z.shiftr x 2) x). assert (RX : 0 <= x < 2 ^ 13) by lia. pose proof (lor_small 13 _ _ ltac:(lia) R2 RX) as RV1. fold v1 in RV1.
    step. rewrite (unsigned_lit x), srliw_small by lia.
    step. rewrite (unsigned_lit v1), (unsigned_lit (Z.shiftr x 1)) by lia.
    set (v2 := Z.lor v1 (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) RV1 R1) as RV2. fold v2 in RV2.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit v2), srliw_small by lia. pose proof (shiftr_small 13 v2 2 RV2 ltac:(lia)) as R3.
    step. rewrite (unsigned_lit (Z.shiftr v2 2)), (unsigned_lit (Z.shiftr x 1)) by lia.
    set (w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) R3 R1) as RW2. fold w2 in RW2.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit w2) by lia. pose proof (shiftr_small 13 w2 4 RW2 ltac:(lia)) as R4.
    step. rewrite (unsigned_lit (Z.shiftr w2 4)), (unsigned_lit w2) by lia.
    set (w3 := Z.lor (Z.shiftr w2 4) w2). pose proof (lor_small 13 _ _ ltac:(lia) R4 RW2) as RW3. fold w3 in RW3.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit w3) by lia. pose proof (shiftr_small 13 w3 8 RW3 ltac:(lia)) as R5.
    step. rewrite (unsigned_lit (Z.shiftr w3 8)), (unsigned_lit w3) by lia.
    set (w4 := Z.lor (Z.shiftr w3 8) w3). pose proof (lor_small 13 _ _ ltac:(lia) R5 RW3) as RW4. fold w4 in RW4.
    assert (EW4 : w4 = rclz_v4 x) by reflexivity.
    (* [comment removed for export] *)
    step. step. rewrite (unsigned_lit w4) by lia.
    step. rewrite (unsigned_lit (w4 + 1)) by lia. rewrite (unsigned_lit (Z.lxor w4 18446744073709551615)) by (rewrite zb_lxor_ones by lia; lia).
    change (Z.land (w4 + 1) (Z.lxor w4 18446744073709551615)) with (clz_pow x). rewrite PW.
    set (k := Z.log2 x) in *.
    assert (P2 : 0 < 2 ^ k < 2 ^ 13) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
    assert (EK : k = Z.log2 x) by reflexivity. clearbody k. clear PW RV4 EW4 RW4 R5 RW3 R4 RW2 R3 RV2 RV1 R1 R2. subst w4 w3 w2 v2 v1.
    assert (EX : x = q + 1) by reflexivity. clearbody x.
    assert (K13 : 3 <= k <= 12) by (apply LG; lia).
    (* [comment removed for export] *)
    step. step. step.
    step. rewrite (unsigned_lit (2 ^ k)) by lia. change 125613361 with rDB32.
    step. rewrite (mul_srliw27 k) by lia.
    pose proof (rdbi_range k) as DR.
    step. rewrite ?(unsigned_lit (rdbi k)) by lia.
    pose proof (rdebruijn_read m k MI ltac:(lia)) as DBR. unfold DEBRUIJN in DBR.
    step. rewrite ?zxb_b8 by lia. clear DBR.
    (* [comment removed for export] *)
    step. rewrite (wz_unsigned k), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    step. rewrite (unsigned_lit (k * 4)), lxor_4k_124 by lia.
    set (i := 4 * k - 4). assert (IR : 8 <= i <= 44) by lia.
    replace (124 - 4 * k) with (120 - i) by lia.
    assert (STQ : stc_q q = (let i1 := if size_class (i + 1) <? x then i + 2 else i in if size_class i1 <? x then i1 + 1 else i1)).
    { unfold stc_q. replace (q <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite <- EX, <- EK. reflexivity. }
    assert (IEV : Z.even i = true) by (subst i; rewrite Z.even_sub, Z.even_mul; reflexivity).
    clearbody i. clear EK.
    pose proof (size_class_range (i + 1) ltac:(lia)) as SR1.
    step. step. rewrite (unsigned_lit (120 - i)) by lia. replace (121 + - (120 - i)) with (i + 1) by lia.
    step. rewrite (unsigned_lit (i + 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
    step. replace (85160 + (i + 1) * 2) with (85160 + 2 * (i + 1)) by lia.
    pose proof (size_classes_read m (i + 1) MI ltac:(lia)) as RS1. unfold SIZE_CLASSES in RS1.
    step. rewrite ?zx16_wz by lia. clear RS1.
   
    (* [comment removed for export] *)
    assert (J1 : forall (i1 c : Z) (t1' : word),
      i1 = (if size_class (i + 1) <? x then i + 2 else i) -> c = i1 - i + 120 ->
      evt rsegs (realloc_stc_post ra sp gp tp t0 t2 s0 s1 a0 (Z_to_bv 64 N) a3 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 N F fc m)
        (MS (mkR ra sp gp tp t0 t1' t2 s0 s1 a0 (Z_to_bv 64 N) (Z_to_bv 64 q) a3 (Z_to_bv 64 (120 - i)) (wz 85160) a6 (Z_to_bv 64 c)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x24b98) fc None m (seg_rom rsegs))).
    { intros i1 c t1' Hi1 Hc.
      assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
      { subst i1. destruct (size_class (i + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
      destruct I1R as [I1R I1E].
      pose proof (size_class_range i1 ltac:(lia)) as SR2.
      step. rewrite ?(unsigned_lit c), ?(unsigned_lit (120 - i)) by lia. replace (c + - (120 - i)) with i1 by lia.
      step. rewrite ?(unsigned_lit i1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
      step. rewrite ?(unsigned_lit (i1 * 2)) by lia. replace (85160 + i1 * 2) with (85160 + 2 * i1) by lia.
      pose proof (size_classes_read m i1 MI ltac:(lia)) as RS2. unfold SIZE_CLASSES in RS2.
      step. rewrite ?zx16_wz by lia. clear RS2.
      step. rewrite ?v_sltu_b2z, ?(unsigned_lit q), ?(wz_unsigned (size_class i1)) by lia.
      step. step.
      destruct (Z.ltb_spec q (size_class i1)) as [LT|GE]; cbn [Z.b2z].
      * rewrite ?(unsigned_lit 1), ?(unsigned_lit i1) by lia. change (Z.lxor 1 1) with 0. rewrite ?(unsigned_lit 0), Z.lor_0_r by lia.
        step. rewrite ?(unsigned_lit i1), swrap32_small by lia.
        apply evt_done. unfold realloc_stc_post. do 4 eexists. rewrite STC, STQ. cbv zeta. rewrite <- Hi1.
        replace (size_class i1 <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
      * rewrite ?(unsigned_lit 0), ?(unsigned_lit i1) by lia. change (Z.lxor 0 1) with 1. rewrite ?(unsigned_lit 1), (lor_even_1 i1 ltac:(lia) I1E) by lia.
        step. rewrite ?(unsigned_lit (i1 + 1)), swrap32_small by lia.
        apply evt_done. unfold realloc_stc_post. do 4 eexists. rewrite STC, STQ. cbv zeta. rewrite <- Hi1.
        replace (size_class i1 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    step. if_cases K3; zify_cond K3; rewrite ?(unsigned_lit q), ?(wz_unsigned (size_class (i + 1))) in K3 by lia.
    + (* [comment removed for export] *)
      step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with false by (symmetry; apply Z.ltb_ge; lia). lia.
    + (* [comment removed for export] *)
      step. step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition inplace_ok (N AV sc : Z) : Prop := N <= AV /\ N < MMAP_THRESHOLD /\ sc <= size_to_class N + 1.

(* [comment removed for export] *)
Definition realloc_inplace_pre (ra sp gp tp t0 s0 s1 a0 a1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word) (N sc : Z)
   (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t1 t2 t3 a4 a5 a7,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (wz (size_to_class N + 1)) (wz sc) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x24bfc) fc None m (seg_rom rsegs).

Lemma realloc_decide_inplace : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
   (N AV sc : Z),
  bv_unsigned a1 = N -> 0 <= AV < 2^64 -> 0 <= sc < 64 -> inplace_ok N AV sc -> mem_inv rsegs m ->
  evt rsegs (realloc_inplace_pre ra sp gp tp t0 s0 s1 a0 a1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 N sc F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (wz sc) a4 (wz SIZE_CLASSES) a6 (wz AV) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x24a18) fc None m (seg_rom rsegs)).
Proof.
  intros until sc. intros HA1 AVR SC (LE & NT & CL) MI. unfold MMAP_THRESHOLD in NT.
  pose proof (bv_unsigned_in_range _ a1) as A1R. change (bv_modulus 64) with (2^64) in A1R.
  pose proof (size_to_class_props N ltac:(unfold MMAP_THRESHOLD; lia)) as (SCR & _).
  step. step. step. if_cases K1; zify_cond K1; rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. { exfalso. lia. }
  step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia. { exfalso. lia. }
  eapply evt_cut. { eapply realloc_stc_walk; [exact HA1| unfold MMAP_THRESHOLD; lia| exact MI]. }
  intros ms' (t1' & a4' & a5' & a7' & ->). change (wz 150456) with (Z_to_bv 64 0x24bb8).
  step. if_cases K3; zify_cond K3; rewrite ?signed_wz_small in K3 by lia. 2:{ exfalso. lia. }
  apply evt_done. unfold realloc_inplace_pre. do 6 eexists. reflexivity.
Qed.


(* [comment removed for export] *)
Definition realloc_mremap_pre (ra sp gp tp t0 t1 s0 s1 a0 a1 a2 a4 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word) (sc : Z)
   (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t2 t3 a5,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (wz sc) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x24ad4) fc None m (seg_rom rsegs).

Lemma realloc_decide_mremap : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
   (N sc : Z),
  bv_unsigned a1 = N -> MMAP_THRESHOLD <= N -> sc = 63 ->
  evt rsegs (realloc_mremap_pre ra sp gp tp t0 t1 s0 s1 a0 a1 a2 a4 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 sc F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (wz sc) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x24a18) fc None m (seg_rom rsegs)).
Proof.
  intros until sc. intros HA1 NT SC. unfold MMAP_THRESHOLD in NT.
  pose proof (bv_unsigned_in_range _ a1) as A1R. change (bv_modulus 64) with (2^64) in A1R.
  step. step. step. if_cases K1; zify_cond K1; rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. 2:{ exfalso. lia. }
  (* [comment removed for export] *)
  step. step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia. { exfalso. lia. }
  step. step. if_cases K3; zify_cond K3; rewrite ?wz_unsigned, ?unsigned_lit in K3 by lia. { exfalso. lia. }
  step. step. if_cases K4; zify_cond K4; rewrite ?wz_unsigned, ?unsigned_lit in K4 by lia. 2:{ exfalso. lia. }
  apply evt_done. unfold realloc_mremap_pre. do 3 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Definition realloc_fallback_pre (ra sp gp tp t0 s0 s1 a0 a1 a3 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word)
   (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t1 t2 t3 a2 a4 a5 a7,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x24bbc) fc None m (seg_rom rsegs).

Lemma realloc_decide_fallback : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
   (N AV sc : Z),
  bv_unsigned a1 = N -> 0 <= AV < 2^64 -> 0 <= sc < 64 ->
  ~ inplace_ok N AV sc -> ~ (MMAP_THRESHOLD <= N /\ 48 <= sc) -> mem_inv rsegs m ->
  evt rsegs (realloc_fallback_pre ra sp gp tp t0 s0 s1 a0 a1 (wz sc) a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (wz sc) a4 (wz SIZE_CLASSES) a6 (wz AV) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x24a18) fc None m (seg_rom rsegs)).
Proof.
  intros until sc. intros HA1 AVR SC NIP NMM MI. unfold inplace_ok, MMAP_THRESHOLD in NIP, NMM.
  pose proof (bv_unsigned_in_range _ a1) as A1R. change (bv_modulus 64) with (2^64) in A1R.
  (* [comment removed for export] *)
  assert (BIGJ : forall t3', (131052 <= N \/ AV < N) ->
    evt rsegs (realloc_fallback_pre ra sp gp tp t0 s0 s1 a0 a1 (wz sc) a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 (Z_to_bv 64 131072) s0 s1 a0 a1 a2 (wz sc) a4 (wz SIZE_CLASSES) a6 (wz AV) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
          F (Z_to_bv 64 0x24ab8) fc None m (seg_rom rsegs))).
  { intros t3' HB.
    step. step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia.
    { apply evt_done. unfold realloc_fallback_pre. do 7 eexists. reflexivity. }
    step. step. if_cases K3; zify_cond K3; rewrite ?wz_unsigned, ?unsigned_lit in K3 by lia.
    { apply evt_done. unfold realloc_fallback_pre. do 7 eexists. reflexivity. }
    exfalso. lia. }
  step. step. step. if_cases K1; zify_cond K1; rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. { apply BIGJ. lia. }
  step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia. { apply BIGJ. lia. }
  pose proof (size_to_class_props N ltac:(unfold MMAP_THRESHOLD; lia)) as (SCR & _).
  eapply evt_cut. { eapply realloc_stc_walk; [exact HA1| unfold MMAP_THRESHOLD; lia| exact MI]. }
  intros ms' (t1' & a4' & a5' & a7' & ->). change (wz 150456) with (Z_to_bv 64 0x24bb8).
  step. if_cases K3; zify_cond K3; rewrite ?signed_wz_small in K3 by lia. { exfalso. lia. }
  apply evt_done. unfold realloc_fallback_pre. do 7 eexists. reflexivity.
Qed.
End W_reagh.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RF_egfy.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_al5bs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_rejt8.W_re997 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_rejt8.W_reagh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_egfy.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg.
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

(* [comment removed for export] *)
Ltac sdk :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m ?a ?bs) ?ro) =>
    let E := addr_expr a in
    (lazymatch a with
     | wa _ => idtac
     | Z_to_bv 64 _ => change (write_to_mem m a bs) with (write_to_mem m (wa E) bs)
     | _ => replace (write_to_mem m a bs) with (write_to_mem m (wa E) bs) by (f_equal; addr_eq_tac)
     end);
    (try lazymatch goal with
     | HI : mem_inv segs m, HS : store_ok segs m ?a' ?n = true |- _ =>
        apply (mem_inv_store segs m (wa E) bs) in HI;
        [ | first [ exact HS
                  | replace (wa E) with a' by (first [reflexivity | addr_eq_tac | symmetry; addr_eq_tac]);
                    first [ exact HS | simpl_sizes; exact HS ] ] ]
     end);
    transport_chunks segs m E bs;
    repeat match goal with
    | STq : stk segs m ?loq ?hiq |- _ =>
        first [ apply (stk_write segs m loq hiq E bs) in STq; [ | lia | simpl_sizes; slia ]
              | fail 100 "sdk: cannot transport stk hypothesis" STq ]
    | MU : munch ?Wq ?mq m |- _ =>
        first [ apply (munch_write Wq mq m E bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
              | fail 100 "sdk: store outside the declared footprint" ]
    | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa E) bs) in WMo
    | W : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa E) bs) in W
    end;
    repeat match goal with
    | H : store_ok segs m _ _ = true |- _ => clear H
    | H : ov_read_bytes segs m _ _ = Some _ |- _ => clear H
    end;
    let m' := fresh "m" in let Eq := fresh "EQ" m' in
    remember (write_to_mem m (wa E) bs) as m' eqn:Eq
  end.
(* [comment removed for export] *)
Ltac sok off len addr := lazymatch goal with W : wr_at rsegs ?mc (?P - 3) _ |- _ =>
    let H := fresh "SO" in
    pose proof (wr_at_store_ok rsegs mc _ _ off len W ltac:(lia) ltac:(lia)) as H;
    replace (P - 3 + off) with addr in H by lia; change (wa addr) with (Z_to_bv 64 addr) in H end.
Ltac read_b3 := lazymatch goal with BKc : bytes_at rsegs ?mc (?P - 3) [b8 ?k] |- _ =>
      pose proof (bytes_at_read rsegs mc (P - 3) [b8 k] 0 1 BKc ltac:(lia) ltac:(cbn; lia)) as RK;
      cbv [take drop Z.to_nat] in RK; replace (P - 3 + 0) with (P + -3) in RK by lia;
      change (wa (P + -3)) with (Z_to_bv 64 (P + -3)) in RK end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition set_size_mem (m : mem) (P E n b3 : Z) : mem :=
  let r := E - P - n in
  let m1 := if r =? 0 then m else write_to_mem m (wa (E - r)) [b8 0] in
  let '(m2, r') := if 5 <=? r then (write_to_mem (write_to_mem m1 (wa (E - 5)) [b8 0]) (wa (E - 4)) (le4 (wz r)), 5) else (m1, r) in
  write_to_mem m2 (wa (P - 3)) [b8 (Z.land b3 31 + Z.shiftl r' 5)].

Definition realloc_inplace_post (sp gp tp a0 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 RA S0 S1 S2 S3 S4 S5 S6 : word)
   (P E n b3 : Z) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 m',
    ms' = MS (mkR RA (wz (bv_unsigned sp + 64)) gp tp t0 t1 t2 S0 S1 a0 a1 a2 a3 a4 a5 a6 a7 S2 S3 S4 S5 S6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc RA) fc None m' (seg_rom rsegs)
    /\ m' = set_size_mem m P E n b3 /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' (bv_unsigned sp) [C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 RA].

Lemma realloc_inplace_walk : forall (ra sp gp tp t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
   (RA S0 S1 S2 S3 S4 S5 S6 : word) (P E n b3 : Z),
  bv_unsigned a0 = P -> bv_unsigned a1 = n -> 0 <= n -> 3 <= P -> P + n <= E -> E - P - n < 2^31 -> E + 5 <= 2^64 ->
  E + 1 <= bv_unsigned sp -> bv_unsigned sp + 64 <= 2^64 -> 0 <= b3 < 256 ->
  mem_inv rsegs m ->
  wr_at rsegs m (P - 3) (E - P + 3) ->
  bytes_at rsegs m (P - 3) [b8 b3] ->
  rw_cells rsegs m (bv_unsigned sp) [C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 RA] ->
  evt rsegs (realloc_inplace_post sp gp tp a0 a3 a4 a5 (wz (E + 4)) a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 RA S0 S1 S2 S3 S4 S5 S6 P E n b3 F fc m)
      (MS (mkR ra sp gp tp (wz E) t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 (wz (E + 4)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x24bfc) fc None m (seg_rom rsegs)).
Proof.
  intros until b3. intros HP HN N0 P3 PNE RS E5 ESP SPHI B3 MI WR BK FR.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  set (r := E - P - n).
  assert (K31 : 0 <= Z.land b3 31 < 32).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  (* [comment removed for export] *)
  assert (TAIL : forall (t0' a2' : word) (r' : Z) (mc : mem),
    0 <= r' < 8 -> mem_inv rsegs mc -> wr_at rsegs mc (P - 3) (E - P + 3) -> bytes_at rsegs mc (P - 3) [b8 b3] ->
    rw_cells rsegs mc (bv_unsigned sp) [C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 RA] ->
    (forall mf, mf = write_to_mem mc (wa (P - 3)) [b8 (Z.land b3 31 + Z.shiftl r' 5)] -> mf = set_size_mem m P E n b3) ->
    evt rsegs (realloc_inplace_post sp gp tp a0 a3 a4 a5 (wz (E + 4)) a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 RA S0 S1 S2 S3 S4 S5 S6 P E n b3 F fc m)
      (MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0 (wz r') a2' a3 a4 a5 (wz (E + 4)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x24c38) fc None mc (seg_rom rsegs))).
  { intros t0' a2' r' mc R8 MIc WRc BKc FRc HF. cbv delta [wz].
    (* [comment removed for export] *)
    read_b3. step. clear RK. rewrite ?zxb_b8 by lia.
    step. rewrite ?(wz_unsigned b3) by lia.
    step. rewrite ?(unsigned_lit r'), Z.shiftl_mul_pow2 by lia.
    step. rewrite ?(unsigned_lit (r' * 2 ^ 5)), ?(unsigned_lit (Z.land b3 31)) by lia.
    rewrite (lor_shl5 r' (Z.land b3 31)) by lia.
    replace (Z.land (Z.land b3 31) 31) with (Z.land b3 31) by (rewrite <- Z.land_assoc; reflexivity).
    sok 0 1%nat (P + -3).
    step. rewrite (le1_wz (Z.land b3 31 + Z.shiftl r' 5)) by (rewrite Z.shiftl_mul_pow2 by lia; lia). sdk.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. step. step. step.
    apply evt_done. unfold realloc_inplace_post. do 6 eexists. split; [reflexivity|].
    split; [apply HF; assumption|]. split; assumption. }
  cbv delta [wz].
  (* [comment removed for export] *)
  step. rewrite HN, HP. step. rewrite ?(unsigned_lit E), ?(unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
  replace (E - (n + P)) with r by lia.
  (* [comment removed for export] *)
  step. if_cases KR; zify_cond KR; rewrite ?(unsigned_lit r) in KR by lia.
  - (* [comment removed for export] *)
    step. step.
    apply (TAIL _ _ 0 m); [lia| exact MI| exact WR| exact BK| exact FR|].
    intros mf ->. unfold set_size_mem. fold r. rewrite KR. reflexivity.
  - (* [comment removed for export] *)
    step. rewrite ?(unsigned_lit E), ?(unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
    replace (E - (n + P)) with r by lia.
    step. rewrite ?(unsigned_lit r), (swrap32_small (0 - r)) by lia.
    step. replace (E + (0 - r)) with (E - r + 0) by lia.
    step.
    sok (n + 3) 1%nat (E - r + 0).
    step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
    (* [comment removed for export] *)
    step. if_cases K5; zify_cond K5; rewrite ?signed_wz_small in K5 by lia.
    + (* [comment removed for export] *)
      step.
      eapply (TAIL _ _ r); [lia| exact MI| exact WR| exact BK| exact FR|].
      intros mf ->. unfold set_size_mem. fold r.
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with false by (symmetry; apply Z.leb_gt; lia). cbv beta iota zeta.
      repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
      repeat (f_equal; try (unfold wa; f_equal; lia)).
    + (* [comment removed for export] *)
      sok (E - P - 2) 1%nat (E + 4 + -9).
      step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
      sok (E - P - 1) 4%nat (E + 4 + -8).
      step. change (le4 (Z_to_bv 64 r)) with (le4 (wz r)). sdk.
      step.
      eapply (TAIL _ _ 5); [lia| exact MI| exact WR| exact BK| exact FR|].
      intros mf ->. unfold set_size_mem. fold r.
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with true by (symmetry; apply Z.leb_le; lia). cbv beta iota zeta.
      repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
      repeat (f_equal; try (unfold wa; f_equal; lia)).
Qed.
