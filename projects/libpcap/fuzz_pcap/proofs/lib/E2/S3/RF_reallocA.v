(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_free_A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_get_meta__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_get_meta.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac ulia := unfold UNIT, IB in *; ceil_facts; lia.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Definition rrealloc_sym : Z := 0x1a138.     (* [comment removed for export] *)
Definition rrealloc_entry : Z := 0x1a13c.

Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Lemma zx32_wz_r x : 0 <= x < 2^32 -> zx32 (wz x) = wz x.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts. intros. unfold zx32, wz. rewrite wz_unsigned by lia. f_equal. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
Definition rrealloc_frame (ra s0 s1 s2 s3 s4 s5 s6 : word) : list cell :=
  [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition rrpro_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a0 a1 a3 a4 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a2 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1a194) fc None m' (seg_rom ssegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ stk ssegs m' lo (bv_unsigned sp + -64)
    /\ rw_cells ssegs m' (bv_unsigned sp + -64) (rrealloc_frame ra s0 s1 s2 s3 s4 s5 s6).

Lemma rrealloc_pro_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (lo P n : Z),
  mem_inv ssegs m -> stk ssegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  bv_unsigned a0 = P -> 0 < P -> bv_unsigned a1 = n -> 0 <= n < 2^32 ->
  evt ssegs (rrpro_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a0 a1 a3 a4 a5 a6 a7 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rrealloc_entry) fc None m (seg_rom ssegs)).
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros until n. intros MI ST LO SLO HP P0 HN N.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MUs. pose proof (wmono_refl ssegs m) as WM.
  unfold rrealloc_entry in *; ceil_facts.
  st1. if_cases K0; zify_cond K0. { exfalso. lia. }
  carve_frame 64%nat ST.
  st1. st1. st1. st1. st1. st1. st1. st1. st1.
  st1. st1. st1. st1. if_cases K1; zify_cond K1.
  2:{ exfalso. revert K1. rewrite HN. clear -N. intros K1. lia. }
  unfold rrpro_post. finish.
Qed.

(* [comment removed for export] *)
Definition rrhdrA_post (ra sp gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (G B : Z) (b3 sc mword stride : Z) : machine_state -> Prop :=
  fun ms' => exists t2 t3 t4,
    ms' = MS (mkR ra sp gp tp (Z_to_bv 64 (Z.land b3 31)) (Z_to_bv 64 (Z.land mword 31)) t2 s0 (wz G)
                  a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 RSIZE_CLASSES) (Z_to_bv 64 stride) (wz b3)
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1a2b0) fc None m (seg_rom ssegs).

(* [comment removed for export] *)
Lemma rrealloc_hdrA_tail : forall ra sp gp tp s0 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
   (G B : Z) (b3 off16 last_idx freeable sc maplen : Z),
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  let stride := if (last_idx =? 0) && negb (maplen =? 0) then maplen * 4096 - 16 else 16 * size_class sc in
  (sc < 48 -> ov_read_bytes ssegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
  0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 -> 0 <= G < 2^64 ->
  (maplen <> 0 -> off16 <= maplen * 256 - 1) ->
  (maplen = 0 \/ last_idx <> 0 -> sc < 48) ->
  evt ssegs (rrhdrA_post ra sp gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 F fc m G B b3 sc mword stride)
      (MS (mkR ra sp gp tp (Z_to_bv 64 (Z.land b3 31)) (Z_to_bv 64 last_idx) (Z_to_bv 64 (sc * 2)) s0 (wz G)
                a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 RSIZE_CLASSES) (wz off16) (wz b3)
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1a288) fc None m (seg_rom ssegs)).
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros until maplen. intros mword stride RS B3 O16 LI FB SC ML GR Hml SC48.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (MW1 : Z.land mword 31 = last_idx).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (MW12 : Z.shiftr mword 12 = maplen).
  { subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.div_add, Z.div_small by lia. lia. }
  assert (MWP : mword - mword mod 4096 = 4096 * maplen).
  { subst mword. replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.mod_add, Z.mod_small by lia. lia. }
  (* [comment removed for export] *)
  assert (KS : forall t3v, (maplen = 0 \/ last_idx <> 0) ->
    evt ssegs (rrhdrA_post ra sp gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 F fc m G B b3 sc mword stride)
      (MS (mkR ra sp gp tp (Z_to_bv 64 (Z.land b3 31)) (Z_to_bv 64 last_idx) (Z_to_bv 64 (sc * 2)) s0 (wz G)
                a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 RSIZE_CLASSES) (wz off16) (wz b3)
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4 t5 t6) F (Z_to_bv 64 0x1a2a4) fc None m (seg_rom ssegs))).
  { intros t3v COND. specialize (SC48 COND). specialize (RS SC48).
    assert (STR : stride = 16 * size_class sc).
    { unfold stride. destruct COND as [C|C]; [rewrite (proj2 (Z.eqb_eq _ _) C), andb_false_r; reflexivity|].
      rewrite (proj2 (Z.eqb_neq _ _) C). reflexivity. }
    pose proof (size_class_range sc ltac:(lia)) as SZ.
    (* [comment removed for export] *)
    st1. try rewrite (unsigned_lit (sc * 2)) by lia.
    assert (RS' : ov_read_bytes ssegs m (Z_to_bv 64 (RSIZE_CLASSES + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
    { replace (Z_to_bv 64 (RSIZE_CLASSES + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa; f_equal; lia). exact RS. }
    unfold RSIZE_CLASSES in RS'. unfold RSIZE_CLASSES.
    st1. try rewrite (Z.mod_small (size_class sc)) by lia.
    st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
    replace (Z_to_bv 64 (size_class sc * 16)) with (Z_to_bv 64 stride) by (rewrite STR; f_equal; lia).
    unfold rrhdrA_post. rewrite <- MW1. apply evt_done. do 3 eexists. reflexivity. }
  (* [comment removed for export] *)
  st1. rewrite MW12. st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
  - apply KS. left. exact Km.
  - (* [comment removed for export] *)
    st1. st1. st1. if_cases Ko; zify_cond Ko.
    2:{ exfalso. rewrite Z.shiftl_mul_pow2 in Ko by lia. change (2^8) with 256 in Ko. change 18446744073709551615 with (Z.ones 64) in Ko.
        rewrite Z.land_ones, ?wz_unsigned in Ko by lia. rewrite Z.mod_small in Ko by lia. lia. }
    (* [comment removed for export] *)
    st1. if_cases Kl; zify_cond Kl; rewrite ?unsigned_lit in Kl by lia.
    + (* [comment removed for export] *)
      st1. st1. rewrite land_pgmask by lia. rewrite ?(wz_unsigned mword), MWP by lia. st1. st1.
      replace (Z_to_bv 64 (4096 * maplen + -16)) with (Z_to_bv 64 stride).
      2:{ unfold stride. rewrite (proj2 (Z.eqb_eq _ _) Kl). replace (maplen =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. f_equal. lia. }
      unfold rrhdrA_post. rewrite <- MW1. apply evt_done. do 3 eexists. reflexivity.
    + apply KS. right. exact Kl.
Qed.

Lemma rrealloc_hdrA_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
   (P G B A : Z) (b3 off16 avail freed last_idx freeable sc maplen secret: Z) (prev next : word),
  let idx := Z.land b3 31 in
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  let stride := if (last_idx =? 0) && negb (maplen =? 0) then maplen * 4096 - 16 else 16 * size_class sc in
  bv_unsigned a0 = P -> P mod 16 = 0 -> 16 * off16 + 16 <= P -> P + 16 <= alloc_ceiling ->
  B = P - 16 * off16 - 16 -> A = G - G mod 4096 -> 0 <= G -> G + 40 <= alloc_ceiling ->
  ov_read_bytes ssegs m (wa (P - 4)) 1 = Some [b8 0] ->
  ov_read_bytes ssegs m (wa (P - 3)) 1 = Some [b8 b3] ->
  ov_read_bytes ssegs m (wa (P - 2)) 2 = Some (le2 (wz off16)) ->
  ov_read_bytes ssegs m (wa B) 8 = Some (le8 (wz G)) ->
  rw_cells ssegs m G [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
  ov_read_bytes ssegs m (wa A) 8 = Some (le8 (wz secret)) ->
  ov_read_bytes ssegs m (wa RCTX) 8 = Some (le8 (wz secret)) ->
  (sc < 48 -> ov_read_bytes ssegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
  0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= secret < 2^64 ->
  0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
  idx <= last_idx -> Z.testbit avail idx = false -> Z.testbit freed idx = false ->
  (sc < 48 -> size_class sc * idx <= off16 < size_class sc * (idx + 1)) ->
  (48 <= sc -> sc = 63) ->
  (maplen <> 0 -> off16 <= maplen * 256 - 1) ->
  (maplen = 0 \/ last_idx <> 0 -> sc < 48) ->
  evt ssegs (rrhdrA_post ra sp gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 F fc m G B b3 sc mword stride)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1a194) fc None m (seg_rom ssegs)).
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros until next. intros idx mword stride HP AL PLO PHI HB HA GLO GHI R4 R3 R2 RG MM RA RC RS B3 O16 AV FR SE LI FB SC ML
    Hidx Hav Hfr Hsc Hsc63 Hml SC48.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  ceil_facts.
  (* [comment removed for export] *)
  st1. st1. if_cases K; zify_cond K. 2:{ exfalso. change 15 with (2^4 - 1) in K. rewrite zb_land_mask in K by lia. lia. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
  (* [comment removed for export] *)
  st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
  st1.
  assert (RG' : ov_read_bytes ssegs m (Z_to_bv 64 (P - off16 * 16 + -16)) 8 = Some (le8 (wz G))).
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
  st1. st1. st1. st1. rewrite MW2. st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2. st1. st1. if_cases K8; zify_cond K8.
  - (* [comment removed for export] *) specialize (Hsc63 ltac:(rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia; lia)).
    st1. st1. if_cases K9; zify_cond K9. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia. lia. }
    rewrite GW. subst idx.
    eapply (rrealloc_hdrA_tail ra sp gp tp s0 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ t4 t5 t6 F fc m G B b3 off16 last_idx freeable sc maplen);
      fastfirst (first [ noevar_assumption |exact RS| lia| exact Hml| exact SC48]).
  - assert (SC' : sc < 48) by (rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia; lia).
    specialize (RS SC'). specialize (Hsc SC').
    (* [comment removed for export] *)
    st1.
    assert (RS' : ov_read_bytes ssegs m (Z_to_bv 64 (70188 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
    { replace (Z_to_bv 64 (70188 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
    pose proof (size_class_range sc ltac:(lia)) as SZ. st1.
    try rewrite (Z.mod_small (size_class sc)) by lia. fold idx.
    st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }
    (* [comment removed for export] *)
    st1. st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
    st1. rewrite GW. subst idx.
    eapply (rrealloc_hdrA_tail ra sp gp tp s0 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ t5 t6 F fc m G B b3 off16 last_idx freeable sc maplen);
      fastfirst (first [ noevar_assumption |intros; exact RS| lia| exact Hml| exact SC48]).
Qed.

(* [comment removed for export] *)
Lemma rrealloc_hdrA_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    st (p : aptr) r g gh ar (b3 lo hi : Z),
  let sh := get_shadow st (fst p) in
  let po := snd p in
  let off16 := lo + 256 * hi in
  let idx := Z.land b3 31 in
  let base := aadd p (- (UNIT * off16) - UNIT) in
  let mr := get_meta_rec st g in
  rmrep st m -> mem_inv ssegs m ->
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
  evt ssegs (rrhdrA_post ra sp gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 F fc m (conc st g) (conc st base) b3 (m_sizeclass mr) (meta_word mr) (get_stride mr))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1a194) fc None m (seg_rom ssegs)).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros until hi. intros sh po off16 idx base mr MR MI Hr Hk HP AL P16 PLO PHI C4 C3 C2 C1 Hgh Hg MS G0 Hmem Har Hchk
         AV FR SE LI FB SC ML Hidx Hav Hfr Hsc Hsc63 Hml SC48.
  pose proof MR as (WF & CX & GL & AR & GR & SH).
  destruct WF as (Hres & WR & DISJ & WA & WG).
  destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & _). ceil_facts.
  destruct (rmrep_shadow_read st m (fst p) r (po - 4) 0 MR Hr Hk ltac:(lia) C4) as [R4 _].
  destruct (rmrep_shadow_read st m (fst p) r (po - 3) b3 MR Hr Hk ltac:(lia) C3) as [R3 B3].
  destruct (rmrep_shadow_read2 st m (fst p) r (po - 2) lo hi MR Hr Hk ltac:(lia) ltac:(lia) C2 ltac:(replace (po - 2 + 1) with (po - 1) by lia; exact C1)) as (R2 & LO & HI).
  rewrite <- le2_lohi in R2 by lia.
  destruct (rmrep_group_read st m base gh MR Hgh) as [RG _]. rewrite Hg in RG. cbn [pw oconc] in RG.
  pose proof (rmrep_meta_chunk st m g MR MS) as MM. fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.
  pose proof (rmrep_area_check_read st m (area_of g) ar MR Har) as RA. rewrite Hchk in RA.
  pose proof (rmrep_ctx_secret_read st m MR) as RC.
  destruct (WG base gh Hgh) as (rb & Hrb & _ & Bb0 & _). cbn [base aadd fst] in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb.
  assert (HB : conc st base = (r_base r + po) - 16 * off16 - 16).
  { unfold base. rewrite conc_aadd by (rewrite Hr; eauto). rewrite (conc_region' st p r Hr). unfold po, UNIT. lia. }
  destruct MS as (a & ara & k & Ha & Hkk & Eg).
  destruct (WA a ara Ha) as (rg & Hrg & A0 & A1 & AAL & ANG & _).
  assert (HG : conc st g = r_base rg + snd a + (AREA_HDR + META_SIZE * k)).
  { rewrite Eg, conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a rg Hrg). reflexivity. }
  destruct (WR (fst a) rg Hrg) as (RB0 & RBAL & RL0 & RBC & _). ceil_facts.
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
  change (meta_word mr) with (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr).
  replace (get_stride mr) with (if (m_last_idx mr =? 0) && negb (m_maplen mr =? 0) then m_maplen mr * 4096 - 16 else 16 * size_class (m_sizeclass mr))
    by (unfold get_stride, UNIT; reflexivity).
  eapply (rrealloc_hdrA_walk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
            (r_base r + po) (conc st g) (conc st base) (conc st (area_of g)) b3 off16 (m_avail mr) (m_freed mr)
            (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (c_secret (ctx st))
            (pw st (m_prev mr)) (pw st (m_next mr))); try eassumption; try lia.
  - unfold AREA_HDR, META_SIZE, NSLOTS in *. ceil_facts. pose proof (round_up_pg_ge (r_len rg)). lia.
  - replace (r_base r + po - 4) with (r_base r + (po - 4)) by lia. exact R4.
  - replace (r_base r + po - 3) with (r_base r + (po - 3)) by lia. exact R3.
  - replace (r_base r + po - 2) with (r_base r + (po - 2)) by lia. exact R2.
  - intros Hlt. apply rsize_classes_read; [exact MI | lia].
Qed.

(* [comment removed for export] *)
Definition rrhdrB_post (ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 a2 a3 a4 a5 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (P C0 E rsv : Z) : machine_state -> Prop :=
  fun ms' => exists t2 t3 t4,
    ms' = MS (mkR ra sp gp tp (Z_to_bv 64 E) (Z_to_bv 64 C0) t2 s0 s1
                  a0 a1 a2 a3 a4 a5 (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - P)) (Z_to_bv 64 (E - rsv))
                  s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1a320) fc None m (seg_rom ssegs).

Lemma rrealloc_hdrB_walk : forall ra sp gp tp t1 t2 s0 s1 a0 a1 a3 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
   (P B : Z) (b3 stride r32 : Z),
  let idx := Z.land b3 31 in
  let C0 := B + 16 + stride * idx in
  let E := C0 + stride - 4 in
  let rsv0 := Z.shiftr b3 5 in
  let rsv := if 160 <=? b3 then r32 else rsv0 in
  bv_unsigned a0 = P -> 0 <= B -> 16 <= stride -> 0 <= stride * idx -> P <= E -> E + 5 <= 2^64 -> 0 <= b3 < 256 ->
  (160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at ssegs m (E - 4) (le4 (wz r32)) /\ bytes_at ssegs m (E - 5) [b8 0]) ->
  rsv <= E - P -> bytes_at ssegs m (E - rsv) [b8 0] -> bytes_at ssegs m E [b8 0] ->
  evt ssegs (rrhdrB_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 (wz B) a3 a4 a5 F fc m P C0 E rsv)
      (MS (mkR ra sp gp tp (Z_to_bv 64 idx) t1 t2 s0 s1 a0 a1 (wz B) a3 a4 a5 (Z_to_bv 64 stride) (wz b3)
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1a2b0) fc None m (seg_rom ssegs)).
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros until r32. intros idx C0 E rsv0 rsv HP B0 S16 SI0 PE EHI B3 BIG RSVLE RB0r RE0.
  assert (IDX : 0 <= idx < 32).
  { unfold idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  assert (RSV0 : 0 <= rsv0 < 8).
  { unfold rsv0. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  assert (RSVR : 0 <= rsv < 2^32).
  { unfold rsv. destruct (Z.leb_spec 160 b3); [destruct (BIG ltac:(lia)) as (_ & ? & _); lia| lia]. }
  pose proof (bv_unsigned_in_range _ a0) as PR. change (bv_modulus 64) with (2^64) in PR.
  pose proof (bytes_at_read ssegs m _ _ 0 1 RB0r ltac:(lia) ltac:(cbn; lia)) as RDr. cbn [firstn skipn Z.to_nat] in RDr. rewrite Z.add_0_r in RDr.
  pose proof (bytes_at_read ssegs m _ _ 0 1 RE0 ltac:(lia) ltac:(cbn; lia)) as RDe. cbn [firstn skipn Z.to_nat] in RDe. rewrite Z.add_0_r in RDe.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1.
  replace (B + stride * idx + 16 + stride + -4) with E by (unfold E, C0; lia).
  replace (B + stride * idx + 16 + stride) with (E + 4) by (unfold E, C0; lia).
  replace (B + stride * idx + 16) with C0 by (unfold C0; lia).
  fold rsv0.
  (* [comment removed for export] *)
  assert (KT : forall t3v a7v,
    evt ssegs (rrhdrB_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 (wz B) a3 a4 a5 F fc m P C0 E rsv)
      (MS (mkR ra sp gp tp (Z_to_bv 64 E) (Z_to_bv 64 C0) (Z_to_bv 64 rsv) s0 s1 a0 a1 (wz B) a3 a4 a5 (Z_to_bv 64 (E + 4)) a7v
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4 t5 t6) F (Z_to_bv 64 0x1a2f8) fc None m (seg_rom ssegs))).
  { intros t3v a7v.
    (* [comment removed for export] *)
    st1. st1. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. }
    (* [comment removed for export] *)
    st1. replace (E + - rsv) with (E - rsv) by lia. change (Z_to_bv 64 (E - rsv)) with (wa (E - rsv)).
    st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }
    (* [comment removed for export] *)
    change (Z_to_bv 64 E) with (wa E).
    st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. reflexivity. }
    replace (E + - bv_unsigned a0) with (E - P) by lia.
    unfold rrhdrB_post. apply evt_done. do 3 eexists. reflexivity. }
  (* [comment removed for export] *)
  st1. if_cases Kb; zify_cond Kb; rewrite ?wz_unsigned in Kb by lia.
  - replace (Z_to_bv 64 rsv0) with (Z_to_bv 64 rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [lia| reflexivity]). apply KT.
  - destruct (BIG ltac:(lia)) as (R5 & R32 & RB4 & RB5).
    pose proof (bytes_at_read ssegs m _ _ 0 4 RB4 ltac:(lia) ltac:(rewrite length_le4; cbn; lia)) as RD4.
    cbn [skipn Z.to_nat] in RD4. rewrite firstn_all2 in RD4 by (rewrite length_le4; lia). rewrite Z.add_0_r in RD4.
    replace (E - 4) with (E + 4 + -8) in RD4 by lia.
    pose proof (bytes_at_read ssegs m _ _ 0 1 RB5 ltac:(lia) ltac:(cbn; lia)) as RD5. cbn [firstn skipn Z.to_nat] in RD5. rewrite Z.add_0_r in RD5.
    replace (E - 5) with (E + 4 + -9) in RD5 by lia.
    (* [comment removed for export] *)
    st1. st1. if_cases K5; zify_cond K5. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K5 by lia. lia. }
    (* [comment removed for export] *)
    st1. rewrite zx32_wz_r by lia. st1. st1. if_cases K6; zify_cond K6. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K6 by lia. lia. }
    (* [comment removed for export] *)
    st1. st1. if_cases K7; zify_cond K7. 2:{ exfalso. apply K7. rewrite ?wz_unsigned by lia. reflexivity. }
    replace (wz r32) with (Z_to_bv 64 rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [reflexivity| lia]). apply KT.
Qed.
End PORT.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_free_A.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_get_meta.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac ulia := unfold UNIT, IB in *; ceil_facts; lia.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Definition rrealloc_sym : Z := 0x1a8f8.     (* [comment removed for export] *)
Definition rrealloc_entry : Z := 0x1a8fc.

Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Lemma zx32_wz_r x : 0 <= x < 2^32 -> zx32 (wz x) = wz x.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts. intros. unfold zx32, wz. rewrite wz_unsigned by lia. f_equal. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
Definition rrealloc_frame (ra s0 s1 s2 s3 s4 s5 s6 : word) : list cell :=
  [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition rrpro_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a0 a1 a3 a4 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a2 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1a954) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp + -64)
    /\ rw_cells usegs m' (bv_unsigned sp + -64) (rrealloc_frame ra s0 s1 s2 s3 s4 s5 s6).

Definition rrealloc_pro_walk__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (lo P n : Z),
  mem_inv usegs m -> stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  bv_unsigned a0 = P -> 0 < P -> bv_unsigned a1 = n -> 0 <= n < 2^32 ->
  evt usegs (rrpro_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a0 a1 a3 a4 a5 a6 a7 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rrealloc_entry) fc None m (seg_rom usegs)).
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo P n : ltac2:(SecDiet.SzSec.tyM 'rrealloc_pro_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rrealloc_pro_walk__body : ltac2:(SecDiet.SzSec.bodyP 'rrealloc_pro_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
 intros MI ST LO SLO HP P0 HN N.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MUs. pose proof (wmono_refl usegs m) as WM.
  unfold rrealloc_entry in *; ceil_facts.
  st1. if_cases K0; zify_cond K0. { exfalso. lia. }
  carve_frame 64%nat ST.
  st1. st1. st1. st1. st1. st1. st1. st1. st1.
  st1. st1. st1. st1. if_cases K1; zify_cond K1.
  2:{ exfalso. revert K1. rewrite HN. clear -N. intros K1. lia. }
  unfold rrpro_post. finish.
Qed.
End Sz1.
Lemma rrealloc_pro_walk : ltac:(let t := eval cbv delta [rrealloc_pro_walk__stmt] in rrealloc_pro_walk__stmt in exact t).
Proof using MSECV TLSFACTS. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo P n. ltac2:(SecDiet.SzSec.closeP 'rrealloc_pro_walk__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
Definition rrhdrA_post (ra sp gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (G B : Z) (b3 sc mword stride : Z) : machine_state -> Prop :=
  fun ms' => exists t2 t3 t4,
    ms' = MS (mkR ra sp gp tp (Z_to_bv 64 (Z.land b3 31)) (Z_to_bv 64 (Z.land mword 31)) t2 s0 (wz G)
                  a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 RSIZE_CLASSES) (Z_to_bv 64 stride) (wz b3)
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1aa70) fc None m (seg_rom usegs).

(* [comment removed for export] *)
Definition rrealloc_hdrA_tail__stmt : Prop := forall ra sp gp tp s0 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
   (G B : Z) (b3 off16 last_idx freeable sc maplen : Z),
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  let stride := if (last_idx =? 0) && negb (maplen =? 0) then maplen * 4096 - 16 else 16 * size_class sc in
  (sc < 48 -> ov_read_bytes usegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
  0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 -> 0 <= G < 2^64 ->
  (maplen <> 0 -> off16 <= maplen * 256 - 1) ->
  (maplen = 0 \/ last_idx <> 0 -> sc < 48) ->
  evt usegs (rrhdrA_post ra sp gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 F fc m G B b3 sc mword stride)
      (MS (mkR ra sp gp tp (Z_to_bv 64 (Z.land b3 31)) (Z_to_bv 64 last_idx) (Z_to_bv 64 (sc * 2)) s0 (wz G)
                a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 RSIZE_CLASSES) (wz off16) (wz b3)
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1aa48) fc None m (seg_rom usegs)).
Section Sz2.
Variables ra sp gp tp s0 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m G B b3 off16 last_idx freeable sc maplen : ltac2:(SecDiet.SzSec.tyM 'rrealloc_hdrA_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rrealloc_hdrA_tail__body : ltac2:(SecDiet.SzSec.bodyP 'rrealloc_hdrA_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
 intros mword stride RS B3 O16 LI FB SC ML GR Hml SC48.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (MW1 : Z.land mword 31 = last_idx).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (MW12 : Z.shiftr mword 12 = maplen).
  { subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.div_add, Z.div_small by lia. lia. }
  assert (MWP : mword - mword mod 4096 = 4096 * maplen).
  { subst mword. replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.mod_add, Z.mod_small by lia. lia. }
  (* [comment removed for export] *)
  assert (KS : forall t3v, (maplen = 0 \/ last_idx <> 0) ->
    evt usegs (rrhdrA_post ra sp gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 F fc m G B b3 sc mword stride)
      (MS (mkR ra sp gp tp (Z_to_bv 64 (Z.land b3 31)) (Z_to_bv 64 last_idx) (Z_to_bv 64 (sc * 2)) s0 (wz G)
                a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 RSIZE_CLASSES) (wz off16) (wz b3)
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4 t5 t6) F (Z_to_bv 64 0x1aa64) fc None m (seg_rom usegs))).
  { intros t3v COND. specialize (SC48 COND). specialize (RS SC48).
    assert (STR : stride = 16 * size_class sc).
    { unfold stride. destruct COND as [C|C]; [rewrite (proj2 (Z.eqb_eq _ _) C), andb_false_r; reflexivity|].
      rewrite (proj2 (Z.eqb_neq _ _) C). reflexivity. }
    pose proof (size_class_range sc ltac:(lia)) as SZ.
    (* [comment removed for export] *)
    st1. try rewrite (unsigned_lit (sc * 2)) by lia.
    assert (RS' : ov_read_bytes usegs m (Z_to_bv 64 (RSIZE_CLASSES + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
    { replace (Z_to_bv 64 (RSIZE_CLASSES + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa; f_equal; lia). exact RS. }
    unfold RSIZE_CLASSES in RS'. unfold RSIZE_CLASSES.
    st1. try rewrite (Z.mod_small (size_class sc)) by lia.
    st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
    replace (Z_to_bv 64 (size_class sc * 16)) with (Z_to_bv 64 stride) by (rewrite STR; f_equal; lia).
    unfold rrhdrA_post. rewrite <- MW1. apply evt_done. do 3 eexists. reflexivity. }
  (* [comment removed for export] *)
  st1. rewrite MW12. st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
  - apply KS. left. exact Km.
  - (* [comment removed for export] *)
    st1. st1. st1. if_cases Ko; zify_cond Ko.
    2:{ exfalso. rewrite Z.shiftl_mul_pow2 in Ko by lia. change (2^8) with 256 in Ko. change 18446744073709551615 with (Z.ones 64) in Ko.
        rewrite Z.land_ones, ?wz_unsigned in Ko by lia. rewrite Z.mod_small in Ko by lia. lia. }
    (* [comment removed for export] *)
    st1. if_cases Kl; zify_cond Kl; rewrite ?unsigned_lit in Kl by lia.
    + (* [comment removed for export] *)
      st1. st1. rewrite land_pgmask by lia. rewrite ?(wz_unsigned mword), MWP by lia. st1. st1.
      replace (Z_to_bv 64 (4096 * maplen + -16)) with (Z_to_bv 64 stride).
      2:{ unfold stride. rewrite (proj2 (Z.eqb_eq _ _) Kl). replace (maplen =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. f_equal. lia. }
      unfold rrhdrA_post. rewrite <- MW1. apply evt_done. do 3 eexists. reflexivity.
    + apply KS. right. exact Kl.
Qed.
End Sz2.
Lemma rrealloc_hdrA_tail : ltac:(let t := eval cbv delta [rrealloc_hdrA_tail__stmt] in rrealloc_hdrA_tail__stmt in exact t).
Proof using MSECV TLSFACTS. intros ra sp gp tp s0 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m G B b3 off16 last_idx freeable sc maplen. ltac2:(SecDiet.SzSec.closeP 'rrealloc_hdrA_tail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

Definition rrealloc_hdrA_walk__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
   (P G B A : Z) (b3 off16 avail freed last_idx freeable sc maplen secret: Z) (prev next : word),
  let idx := Z.land b3 31 in
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  let stride := if (last_idx =? 0) && negb (maplen =? 0) then maplen * 4096 - 16 else 16 * size_class sc in
  bv_unsigned a0 = P -> P mod 16 = 0 -> 16 * off16 + 16 <= P -> P + 16 <= alloc_ceiling ->
  B = P - 16 * off16 - 16 -> A = G - G mod 4096 -> 0 <= G -> G + 40 <= alloc_ceiling ->
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
  evt usegs (rrhdrA_post ra sp gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 F fc m G B b3 sc mword stride)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1a954) fc None m (seg_rom usegs)).
Section Sz3.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P G B A b3 off16 avail freed last_idx freeable sc maplen secret prev next : ltac2:(SecDiet.SzSec.tyM 'rrealloc_hdrA_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rrealloc_hdrA_walk__body : ltac2:(SecDiet.SzSec.bodyP 'rrealloc_hdrA_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
 intros idx mword stride HP AL PLO PHI HB HA GLO GHI R4 R3 R2 RG MM RA RC RS B3 O16 AV FR SE LI FB SC ML
    Hidx Hav Hfr Hsc Hsc63 Hml SC48.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  ceil_facts.
  (* [comment removed for export] *)
  st1. st1. if_cases K; zify_cond K. 2:{ exfalso. change 15 with (2^4 - 1) in K. rewrite zb_land_mask in K by lia. lia. }
  (* [comment removed for export] *)
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
  st1. st1. st1. st1. rewrite MW2. st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2. st1. st1. if_cases K8; zify_cond K8.
  - (* [comment removed for export] *) specialize (Hsc63 ltac:(rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia; lia)).
    st1. st1. if_cases K9; zify_cond K9. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia. lia. }
    rewrite GW. subst idx.
    eapply (rrealloc_hdrA_tail ra sp gp tp s0 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ t4 t5 t6 F fc m G B b3 off16 last_idx freeable sc maplen);
      fastfirst (first [ noevar_assumption |exact RS| lia| exact Hml| exact SC48]).
  - assert (SC' : sc < 48) by (rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia; lia).
    specialize (RS SC'). specialize (Hsc SC').
    (* [comment removed for export] *)
    st1.
    assert (RS' : ov_read_bytes usegs m (Z_to_bv 64 (70188 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
    { replace (Z_to_bv 64 (70188 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
    pose proof (size_class_range sc ltac:(lia)) as SZ. st1.
    try rewrite (Z.mod_small (size_class sc)) by lia. fold idx.
    st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }
    (* [comment removed for export] *)
    st1. st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
    st1. rewrite GW. subst idx.
    eapply (rrealloc_hdrA_tail ra sp gp tp s0 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ t5 t6 F fc m G B b3 off16 last_idx freeable sc maplen);
      fastfirst (first [ noevar_assumption |intros; exact RS| lia| exact Hml| exact SC48]).
Qed.
End Sz3.
Lemma rrealloc_hdrA_walk : ltac:(let t := eval cbv delta [rrealloc_hdrA_walk__stmt] in rrealloc_hdrA_walk__stmt in exact t).
Proof using MSECV TLSFACTS. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P G B A b3 off16 avail freed last_idx freeable sc maplen secret prev next. ltac2:(SecDiet.SzSec.closeP 'rrealloc_hdrA_walk__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
Definition rrealloc_hdrA_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    st (p : aptr) r g gh ar (b3 lo hi : Z),
  let sh := get_shadow st (fst p) in
  let po := snd p in
  let off16 := lo + 256 * hi in
  let idx := Z.land b3 31 in
  let base := aadd p (- (UNIT * off16) - UNIT) in
  let mr := get_meta_rec st g in
  rmrep st m -> mem_inv usegs m ->
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
  evt usegs (rrhdrA_post ra sp gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 F fc m (conc st g) (conc st base) b3 (m_sizeclass mr) (meta_word mr) (get_stride mr))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1a954) fc None m (seg_rom usegs)).
Section Sz4.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st p r g gh ar b3 lo hi : ltac2:(SecDiet.SzSec.tyM 'rrealloc_hdrA_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rrealloc_hdrA_spec__body : ltac2:(SecDiet.SzSec.bodyP 'rrealloc_hdrA_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
 intros sh po off16 idx base mr MR MI Hr Hk HP AL P16 PLO PHI C4 C3 C2 C1 Hgh Hg MS G0 Hmem Har Hchk
         AV FR SE LI FB SC ML Hidx Hav Hfr Hsc Hsc63 Hml SC48.
  pose proof MR as (WF & CX & GL & AR & GR & SH).
  destruct WF as (Hres & WR & DISJ & WA & WG).
  destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & _). ceil_facts.
  destruct (rmrep_shadow_read st m (fst p) r (po - 4) 0 MR Hr Hk ltac:(lia) C4) as [R4 _].
  destruct (rmrep_shadow_read st m (fst p) r (po - 3) b3 MR Hr Hk ltac:(lia) C3) as [R3 B3].
  destruct (rmrep_shadow_read2 st m (fst p) r (po - 2) lo hi MR Hr Hk ltac:(lia) ltac:(lia) C2 ltac:(replace (po - 2 + 1) with (po - 1) by lia; exact C1)) as (R2 & LO & HI).
  rewrite <- le2_lohi in R2 by lia.
  destruct (rmrep_group_read st m base gh MR Hgh) as [RG _]. rewrite Hg in RG. cbn [pw oconc] in RG.
  pose proof (rmrep_meta_chunk st m g MR MS) as MM. fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.
  pose proof (rmrep_area_check_read st m (area_of g) ar MR Har) as RA. rewrite Hchk in RA.
  pose proof (rmrep_ctx_secret_read st m MR) as RC.
  destruct (WG base gh Hgh) as (rb & Hrb & _ & Bb0 & _). cbn [base aadd fst] in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb.
  assert (HB : conc st base = (r_base r + po) - 16 * off16 - 16).
  { unfold base. rewrite conc_aadd by (rewrite Hr; eauto). rewrite (conc_region' st p r Hr). unfold po, UNIT. lia. }
  destruct MS as (a & ara & k & Ha & Hkk & Eg).
  destruct (WA a ara Ha) as (rg & Hrg & A0 & A1 & AAL & ANG & _).
  assert (HG : conc st g = r_base rg + snd a + (AREA_HDR + META_SIZE * k)).
  { rewrite Eg, conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a rg Hrg). reflexivity. }
  destruct (WR (fst a) rg Hrg) as (RB0 & RBAL & RL0 & RBC & _). ceil_facts.
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
  change (meta_word mr) with (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr).
  replace (get_stride mr) with (if (m_last_idx mr =? 0) && negb (m_maplen mr =? 0) then m_maplen mr * 4096 - 16 else 16 * size_class (m_sizeclass mr))
    by (unfold get_stride, UNIT; reflexivity).
  eapply (rrealloc_hdrA_walk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
            (r_base r + po) (conc st g) (conc st base) (conc st (area_of g)) b3 off16 (m_avail mr) (m_freed mr)
            (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (c_secret (ctx st))
            (pw st (m_prev mr)) (pw st (m_next mr))); try eassumption; try lia.
  - unfold AREA_HDR, META_SIZE, NSLOTS in *. ceil_facts. pose proof (round_up_pg_ge (r_len rg)). lia.
  - replace (r_base r + po - 4) with (r_base r + (po - 4)) by lia. exact R4.
  - replace (r_base r + po - 3) with (r_base r + (po - 3)) by lia. exact R3.
  - replace (r_base r + po - 2) with (r_base r + (po - 2)) by lia. exact R2.
  - intros Hlt. apply rsize_classes_read; [exact MI | lia].
Qed.
End Sz4.
Lemma rrealloc_hdrA_spec : ltac:(let t := eval cbv delta [rrealloc_hdrA_spec__stmt] in rrealloc_hdrA_spec__stmt in exact t).
Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st p r g gh ar b3 lo hi. ltac2:(SecDiet.SzSec.closeP 'rrealloc_hdrA_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
Definition rrhdrB_post (ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 a2 a3 a4 a5 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (P C0 E rsv : Z) : machine_state -> Prop :=
  fun ms' => exists t2 t3 t4,
    ms' = MS (mkR ra sp gp tp (Z_to_bv 64 E) (Z_to_bv 64 C0) t2 s0 s1
                  a0 a1 a2 a3 a4 a5 (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - P)) (Z_to_bv 64 (E - rsv))
                  s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1aae0) fc None m (seg_rom usegs).

Definition rrealloc_hdrB_walk__stmt : Prop := forall ra sp gp tp t1 t2 s0 s1 a0 a1 a3 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
   (P B : Z) (b3 stride r32 : Z),
  let idx := Z.land b3 31 in
  let C0 := B + 16 + stride * idx in
  let E := C0 + stride - 4 in
  let rsv0 := Z.shiftr b3 5 in
  let rsv := if 160 <=? b3 then r32 else rsv0 in
  bv_unsigned a0 = P -> 0 <= B -> 16 <= stride -> 0 <= stride * idx -> P <= E -> E + 5 <= 2^64 -> 0 <= b3 < 256 ->
  (160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at usegs m (E - 4) (le4 (wz r32)) /\ bytes_at usegs m (E - 5) [b8 0]) ->
  rsv <= E - P -> bytes_at usegs m (E - rsv) [b8 0] -> bytes_at usegs m E [b8 0] ->
  evt usegs (rrhdrB_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 (wz B) a3 a4 a5 F fc m P C0 E rsv)
      (MS (mkR ra sp gp tp (Z_to_bv 64 idx) t1 t2 s0 s1 a0 a1 (wz B) a3 a4 a5 (Z_to_bv 64 stride) (wz b3)
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1aa70) fc None m (seg_rom usegs)).
Section Sz5.
Variables ra sp gp tp t1 t2 s0 s1 a0 a1 a3 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P B b3 stride r32 : ltac2:(SecDiet.SzSec.tyM 'rrealloc_hdrB_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rrealloc_hdrB_walk__body : ltac2:(SecDiet.SzSec.bodyP 'rrealloc_hdrB_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
 intros idx C0 E rsv0 rsv HP B0 S16 SI0 PE EHI B3 BIG RSVLE RB0r RE0.
  assert (IDX : 0 <= idx < 32).
  { unfold idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  assert (RSV0 : 0 <= rsv0 < 8).
  { unfold rsv0. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  assert (RSVR : 0 <= rsv < 2^32).
  { unfold rsv. destruct (Z.leb_spec 160 b3); [destruct (BIG ltac:(lia)) as (_ & ? & _); lia| lia]. }
  pose proof (bv_unsigned_in_range _ a0) as PR. change (bv_modulus 64) with (2^64) in PR.
  pose proof (bytes_at_read usegs m _ _ 0 1 RB0r ltac:(lia) ltac:(cbn; lia)) as RDr. cbn [firstn skipn Z.to_nat] in RDr. rewrite Z.add_0_r in RDr.
  pose proof (bytes_at_read usegs m _ _ 0 1 RE0 ltac:(lia) ltac:(cbn; lia)) as RDe. cbn [firstn skipn Z.to_nat] in RDe. rewrite Z.add_0_r in RDe.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1.
  replace (B + stride * idx + 16 + stride + -4) with E by (unfold E, C0; lia).
  replace (B + stride * idx + 16 + stride) with (E + 4) by (unfold E, C0; lia).
  replace (B + stride * idx + 16) with C0 by (unfold C0; lia).
  fold rsv0.
  (* [comment removed for export] *)
  assert (KT : forall t3v a7v,
    evt usegs (rrhdrB_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 (wz B) a3 a4 a5 F fc m P C0 E rsv)
      (MS (mkR ra sp gp tp (Z_to_bv 64 E) (Z_to_bv 64 C0) (Z_to_bv 64 rsv) s0 s1 a0 a1 (wz B) a3 a4 a5 (Z_to_bv 64 (E + 4)) a7v
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4 t5 t6) F (Z_to_bv 64 0x1aab8) fc None m (seg_rom usegs))).
  { intros t3v a7v.
    (* [comment removed for export] *)
    st1. st1. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. }
    (* [comment removed for export] *)
    st1. replace (E + - rsv) with (E - rsv) by lia. change (Z_to_bv 64 (E - rsv)) with (wa (E - rsv)).
    st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }
    (* [comment removed for export] *)
    change (Z_to_bv 64 E) with (wa E).
    st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. reflexivity. }
    replace (E + - bv_unsigned a0) with (E - P) by lia.
    unfold rrhdrB_post. apply evt_done. do 3 eexists. reflexivity. }
  (* [comment removed for export] *)
  st1. if_cases Kb; zify_cond Kb; rewrite ?wz_unsigned in Kb by lia.
  - replace (Z_to_bv 64 rsv0) with (Z_to_bv 64 rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [lia| reflexivity]). apply KT.
  - destruct (BIG ltac:(lia)) as (R5 & R32 & RB4 & RB5).
    pose proof (bytes_at_read usegs m _ _ 0 4 RB4 ltac:(lia) ltac:(rewrite length_le4; cbn; lia)) as RD4.
    cbn [skipn Z.to_nat] in RD4. rewrite firstn_all2 in RD4 by (rewrite length_le4; lia). rewrite Z.add_0_r in RD4.
    replace (E - 4) with (E + 4 + -8) in RD4 by lia.
    pose proof (bytes_at_read usegs m _ _ 0 1 RB5 ltac:(lia) ltac:(cbn; lia)) as RD5. cbn [firstn skipn Z.to_nat] in RD5. rewrite Z.add_0_r in RD5.
    replace (E - 5) with (E + 4 + -9) in RD5 by lia.
    (* [comment removed for export] *)
    st1. st1. if_cases K5; zify_cond K5. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K5 by lia. lia. }
    (* [comment removed for export] *)
    st1. rewrite zx32_wz_r by lia. st1. st1. if_cases K6; zify_cond K6. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K6 by lia. lia. }
    (* [comment removed for export] *)
    st1. st1. if_cases K7; zify_cond K7. 2:{ exfalso. apply K7. rewrite ?wz_unsigned by lia. reflexivity. }
    replace (wz r32) with (Z_to_bv 64 rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [reflexivity| lia]). apply KT.
Qed.
End Sz5.
Lemma rrealloc_hdrB_walk : ltac:(let t := eval cbv delta [rrealloc_hdrB_walk__stmt] in rrealloc_hdrB_walk__stmt in exact t).
Proof using MSECV TLSFACTS. intros ra sp gp tp t1 t2 s0 s1 a0 a1 a3 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P B b3 stride r32. ltac2:(SecDiet.SzSec.closeP 'rrealloc_hdrB_walk__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End PORT.

End WithCeil.
End TwB.
