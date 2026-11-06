(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_place BF_kit BF_unwind BF_depot1 BF_depot2 BF_depot3.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanSizeClass AsanConsts AsanState AsanOps AsanDepot.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
Ltac cstep := stepA; try first [if_true | if_false].

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac tlia ::= first [ Zify.zify; xlia zchecker
  | sf_unhide; first [ zify_prune_plain; Zify.zify; xlia zchecker
                     | LiaA.zify_prune_keep_or; Zify.zify; xlia zchecker
                     | Zify.zify; xlia zchecker ] ].
Ltac transport_after_call ::= transport_after_call_fast.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section PUTH.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : mem).
Variables (lo hi A len : Z) (ws : list word) (NB : list Z) (HS : list Z) (N : Z).
Definition keyZ : list Z := map bv_unsigned (firstn (Z.to_nat len) ws).
Definition h : Z := depot_hash keyZ.
Definition bkt : Z := bucket_of h.
Definition head : Z := bucket_head HS bkt.
Definition kb : Z := (N + 1) / kDepotNodesPerBlock.
Definition TBA : Z := TD + 4 * bkt.

Hypothesis SK : stk bsegs m lo (bv_unsigned sp).
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 224.
Hypothesis SPH : bv_unsigned sp <= hi.
Hypothesis HI : hi < 2^47.
Hypothesis MI : mem_inv bsegs m.
(* [comment removed for export] *)
Hypothesis TR : u64arr bsegs m A ws.
Hypothesis LEN : 1 <= len <= Z.of_nat (length ws).
Hypothesis LWS : Z.of_nat (length ws) <= 30.
Hypothesis TA : bv_unsigned sp <= A /\ A + 8 * Z.of_nat (length ws) <= hi.
(* [comment removed for export] *)
Hypothesis HN : 0 <= N /\ N + 2 < 2^31 /\ N = zlen HS.
Hypothesis HSR : forall i, 0 <= nth_hash HS i < 2^64.
Hypothesis TABK : rw_cells bsegs m (TD + 4 * bkt) [C4 (Z_to_bv 64 head)].
Hypothesis NUQ : rw_cells bsegs m (TD + 0x400000) [C4 (Z_to_bv 64 N)].
Hypothesis HM1 : forall k, 0 <= k < kNodesMap1 -> rw_cells bsegs m (TD + 0x400010 + 8 * k) [C8 (Z_to_bv 64 (nthz NB k))].
Hypothesis HND : forall i, 1 <= i <= N -> exists sid,
  rw_cells bsegs m (nthz NB (i / kDepotNodesPerBlock) + 16 * (i mod kDepotNodesPerBlock))
           [C8 (Z_to_bv 64 (nth_hash HS i)); C4 (Z_to_bv 64 (node_link HS i)); C4 sid].
Hypothesis NBC : forall i, 1 <= i <= N -> i / kDepotNodesPerBlock < zlen NB.            (* [comment removed for export] *)
Hypothesis KBLE : kb <= zlen NB.                                                          (* [comment removed for export] *)
Hypothesis NBR : forall blk, In blk NB -> placed blk kDepotNodeBlockBytes.          (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis PSTK : forall a n, lo <= a -> a + Z.of_nat n <= hi -> P (Z_to_bv 64 a, n).
Hypothesis PDAT : forall a n, 0xa5000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n).
Hypothesis PRO : forall a n, 0x10000 <= a -> a + Z.of_nat n <= 0x31000 -> P (Z_to_bv 64 a, n).
Hypothesis PNB : forall blk a n, In blk NB -> blk <= a -> a + Z.of_nat n <= blk + kDepotNodeBlockBytes -> P (Z_to_bv 64 a, n).

(* [comment removed for export] *)
Definition put_frame (j8 : list byte) : list cell :=
  [CB 8 j8; C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 len); C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition put_regs (rax x10 x11 a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) : bvmap 5 word :=
  mkR rax (Z_to_bv 64 (bv_unsigned sp - 112)) gp tp t0' t1' t2' (Z_to_bv 64 0) (Z_to_bv 64 (N + 1)) x10 x11 a2' a3' a4' a5' a6' a7'
      (Z_to_bv 64 TBA) (Z_to_bv 64 h) (Z_to_bv 64 (TD + 0x400008)) (Z_to_bv 64 head) (Z_to_bv 64 65535) (Z_to_bv 64 (N + 1))
      (Z_to_bv 64 (TD + 0x400010)) (Z_to_bv 64 head) s10 s11 t3' t4' t5' t6'.

Definition put_head_post : machine_state -> Prop :=
  fun ms' =>
    (* [comment removed for export] *)
    (exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' (id : Z),
       ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 id) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs)
       /\ 1 <= id <= N /\ nth_hash HS id = h
       /\ munch [(bv_unsigned sp - 224, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp))
    \/
    (* [comment removed for export] *)
    (exists (a2' a3' a4' a5' a6' : word) m' (j8 : list byte) (wl : word),
       (forall j, 1 <= j <= N -> nth_hash HS j <> h)
       /\ munch [(bv_unsigned sp - 224, bv_unsigned sp); (TBA, TBA + 4); (TD + 0x400000, TD + 0x400000 + 4)] m m'
       /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp - 112)
       /\ rw_cells bsegs m' (bv_unsigned sp - 112) (put_frame j8)
       /\ rw_cells bsegs m' TBA [C4 wl]
       /\ rw_cells bsegs m' (TD + 0x400000) [C4 (Z_to_bv 64 (N + 1))]
       /\ ( (kb < zlen NB /\ ms' = MS (put_regs (Z_to_bv 64 0x73f10) (Z_to_bv 64 (nthz NB kb)) (Z_to_bv 64 kb) a2' a3' a4' a5' a6' a7 t0 t1 t2 t3 t4 t5 t6)
                                     F (Z_to_bv 64 0x73f78) fc None m' (seg_rom bsegs))
         \/ (kb = zlen NB /\ ms' = MS (put_regs (Z_to_bv 64 0x74010) (Z_to_bv 64 (TD + 0x400008)) (Z_to_bv 64 kb) a2' a3' a4' a5' a6' a7 t0 t1 t2 t3 t4 t5 t6)
                                     F (Z_to_bv 64 0x74594) fc None m' (seg_rom bsegs)) )).

Lemma put_head :
  evtA bsegs P put_head_post
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 len) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x73d70) fc None m (seg_rom bsegs)).
Proof. aceil.
  pose proof LOC as LOC0. aceil.
  assert (NBR' : forall blk, In blk NB -> 0x603000 <= blk /\ blk + kDepotNodeBlockBytes <= alloc_ceiling)
    by (intros blk Hblk; pose proof (NBR blk Hblk) as X; plopen X; split; assumption).
  aceil.
  unfold kDepotNodeBlockBytes in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (PSTK' : forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n)) by (intros; apply PSTK; lia).
  pose proof (depot_hash_range keyZ) as HR. fold h in HR.
  pose proof (bucket_head_spec HS bkt) as (BH1 & BH2 & BH3). fold head in BH1, BH2, BH3.
  assert (BKR : 0 <= bkt < 2^20) by (unfold bkt, bucket_of, kTabSize; apply Z.mod_pos_bound; lia).
  assert (KB0 : 0 <= kb < kNodesMap1).
  { unfold kb, kDepotNodesPerBlock, kNodesMap1. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  unfold TBA in *. unfold TD in *.
  assert (MU : munch [(bv_unsigned sp - 224, bv_unsigned sp); (1639576 + 4 * bkt, 1639576 + 4 * bkt + 4); (1639576 + 0x400000, 1639576 + 0x400000 + 4)] m m) by apply munch_refl.
  assert (MU2 : munch [(bv_unsigned sp - 224, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  change (1639576 + 4194304) with 5833880 in NUQ. change (1639576 + 4194304) with 5833880 in MU. change (5833880 + 4) with 5833884 in MU.
  change (1639576 + 4194320) with 5833896 in HM1. 
  do 8 cstep.    (* [comment removed for export] *)
  carve_frame 112%nat SK.
  do 12 cstep.   (* [comment removed for export] *)
  do 4 cstep.    (* [comment removed for export] *)
  cstep.         (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  cstep.         (* [comment removed for export] *)
  rewrite Z.add_0_r. rewrite (bv_swrap_small 32 len) by (change (bv_half_modulus 32) with (2^31); lia).
  zstepA. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. }
  zstepA. if_cases K1; zify_cond K1. { exfalso. revert K1. rewrite ?unsigned_lit by lia. lia. }
  (* [comment removed for export] *)
  eapply (hash_walk P); [assumption| exact TR| exact LEN| lia| lia| intros; apply PSTK; lia| | exact PRO].
  intros x10' x11' x12' x14' x15' x16'. cbv beta.
  change (BF_depot1.keyZ ws len) with keyZ. fold h.
  do 2 zstepA.   (* [comment removed for export] *)
  change 42 with (44 - 2). rewrite (shl_shr_field h 44 2) by lia. change (2^(64-44)) with kTabSize. change (2^2) with 4.
  change (h mod kTabSize) with bkt.
  zstepA.        (* [comment removed for export] *)
  replace (Z_to_bv 64 (1639576 + bkt * 4)) with (Z_to_bv 64 (1639576 + 4 * bkt)) by (f_equal; lia).
  set (TBAv := 1639576 + 4 * bkt) in *. assert (HTBA : TBAv = 1639576 + 4 * bkt) by reflexivity. clearbody TBAv.
  zstepA.        (* [comment removed for export] *)
  assert (SXH : sx32 (Z_to_bv 64 head) = Z_to_bv 64 head).
  { unfold sx32. rewrite Z_to_bv_small by (change (bv_modulus 64) with (2^64)%Z; lia).
    rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia). reflexivity. }
  rewrite SXH.
  do 3 zstepA.   (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  change 2147483647 with (Z.ones 31). rewrite (Z.land_ones head 31) by lia. rewrite (Z.mod_small head (2^31)) by lia.
  do 3 zstepA.   (* [comment removed for export] *)
  change (Z.ones 31) with 2147483647.
  (* [comment removed for export] *)
  match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mf end.
  assert (AGF : forall a0 cs, a0 + Z.of_nat (cells_size cs) <= alloc_ceiling -> rw_cells bsegs m a0 cs -> rw_cells bsegs mf a0 cs).
  { intros a0 cs Ha H. eapply (rw_cells_agree bsegs); [| exact H]. intros x Hx. apply MU2. rewrite wa_unsigned by (pose proof (rw_cells_bound _ _ _ _ H); lia). cbn. lia. }
  assert (HM1f : forall k, 0 <= k < kNodesMap1 -> rw_cells bsegs mf (5833896 + 8 * k) [C8 (Z_to_bv 64 (nthz NB k))]).
  { intros k Hk. apply AGF; [cbn; unfold kNodesMap1 in Hk; lia| exact (HM1 k Hk)]. }
  assert (HNDf : forall i, 1 <= i <= N -> exists sid,
    rw_cells bsegs mf (nthz NB (i / kDepotNodesPerBlock) + 16 * (i mod kDepotNodesPerBlock)) [C8 (Z_to_bv 64 (nth_hash HS i)); C4 (Z_to_bv 64 (node_link HS i)); C4 sid]).
  { intros i Hi. destruct (HND i Hi) as (sid & H). exists sid. apply AGF; [| exact H]. cbn.
    pose proof (NBC i ltac:(lia)) as BC. unfold nthz.
    assert (0 <= i / kDepotNodesPerBlock) by (apply Z.div_pos; unfold kDepotNodesPerBlock; lia).
    replace ((0 <=? i / kDepotNodesPerBlock) && (i / kDepotNodesPerBlock <? zlen NB)) with true
      by (symmetry; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
    pose proof (NBR' (nth (Z.to_nat (i / kDepotNodesPerBlock)) NB 0) ltac:(apply nth_In; unfold zlen in BC; lia)) as [R1 R2].
    pose proof (Z.mod_pos_bound i kDepotNodesPerBlock ltac:(unfold kDepotNodesPerBlock; lia)). unfold kDepotNodesPerBlock in *. lia. }
  eapply (find_loop P) with (TD := 1639576) (NB := NB) (HS := HS) (N := N) (h := h) (n := Z.to_nat head) (cur := head);
    [cbn; lia| lia| exact HR| exact HSR| exact HM1f| exact HNDf| intros; apply NBC; lia| exact NBR| exact PDAT| exact PNB
    | reflexivity| | | |].
  - (* [comment removed for export] *) destruct (Z.eq_dec head 0) as [->|NZ]; [left; reflexivity| right]. split; [lia|]. apply BH2. lia.
  - (* [comment removed for export] *) intros j Hj Hbj EQ. pose proof (BH3 j ltac:(lia) Hbj). lia.
  - (* [comment removed for export] *) intros i x11 x12h Hi EQ. cbv beta.
    do 13 cstep.
    release_frame FR SK (bv_unsigned sp). apply evtA_done. unfold put_head_post. left.
    do 16 eexists. split; [cbv delta [mkR]; reflexivity|]. split; [exact Hi|]. split; [exact EQ|].
    split; [exact MU2|]. split; [assumption|]. split; [assumption| exact SK].
  - (* [comment removed for export] *) intros NONE x10'' x12''. cbv beta. clear MU2.
    cstep.       (* [comment removed for export] *)
    cstep.       (* [comment removed for export] *)
    call_spA (lock_walk P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo TBAv head);
      [exact SK| exact LOC0| lia| lia| assumption| reflexivity| lia| lia
      | rewrite HTBA; replace (1639576 + 4 * bkt) with ((409894 + bkt) * 4) by lia; apply Z_mod_mult| lia| exact TABK
      | intros; apply PSTK; lia| exact PDAT|].
    destruct POST as (wl & TABL). rename PC into SKl.
    match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into ml end.
    (* [comment removed for export] *)
    assert (HM1l : forall k, 0 <= k < kNodesMap1 -> rw_cells bsegs ml (5833896 + 8 * k) [C8 (Z_to_bv 64 (nthz NB k))]).
    { intros k Hk. eapply (rw_cells_agree bsegs); [| exact (HM1 k Hk)]. intros xx Hxx. apply MU.
      rewrite wa_unsigned by (cbn in Hxx; unfold kNodesMap1 in Hk; lia). cbn in Hxx |- *. unfold kNodesMap1 in Hk. lia. }
    (* [comment removed for export] *)
    cstep.       (* [comment removed for export] *)
    zstepA. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
    pose proof (HM1l kb KB0) as M1.
    set (MA := 5833896 + 8 * kb) in *. assert (HMA : MA = 5833896 + 8 * kb) by reflexivity. clearbody MA.
    do 3 cstep.  (* [comment removed for export] *)
    remember 1 as one eqn:HONE.
    zstepA.      (* [comment removed for export] *)
    subst one.
    assert (SXN : sx32 (Z_to_bv 64 N) = Z_to_bv 64 N).
    { unfold sx32. rewrite Z_to_bv_small by (change (bv_modulus 64) with (2^64)%Z; lia).
      rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia). reflexivity. }
    rewrite SXN.
    zstepA.      (* [comment removed for export] *)
    rewrite (bv_swrap_small 32 (N + 1)) by (change (bv_half_modulus 32) with (2^31); lia).
    do 2 zstepA. (* [comment removed for export] *)
    rewrite (Z.mod_small (N + 1) 4294967296) by lia.
    zstepA. if_cases K3; zify_cond K3. { exfalso. lia. }
    cstep.       (* [comment removed for export] *)
    do 3 zstepA. (* [comment removed for export] *)
    rewrite Z.shiftr_div_pow2 by lia. change (2^16) with kDepotNodesPerBlock. fold kb.
    replace (Z_to_bv 64 (5833896 + Z.shiftl kb 3)) with (Z_to_bv 64 MA) by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstepA.      (* [comment removed for export] *)
    all: try lazymatch goal with |- P _ => apply PDAT; unfold kNodesMap1 in KB0; lia end.
    match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mz end.
    destruct (Z_lt_le_dec kb (zlen NB)) as [KLT|KGE].
    + (* [comment removed for export] *)
      assert (BIN : In (nthz NB kb) NB).
      { unfold nthz. replace ((0 <=? kb) && (kb <? zlen NB)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
        apply nth_In. unfold zlen in KLT. lia. }
      pose proof (NBR' _ BIN) as [BR1 BR2].
      zstepA. if_cases K4; zify_cond K4. { exfalso. revert K4. rewrite ?unsigned_lit by lia. lia. }
      apply evtA_done. unfold put_head_post. right.
      unfold put_regs, put_frame. unfold TBA, TD. rewrite <- !HTBA.
      do 5 eexists. exists mz. eexists. exists wl.
      split; [exact NONE|].
      split; [eapply munch_weaken; [| exact MU]; intros xx Hxx; cbn [outside] in Hxx |- *; clear -CEILB Hxx; lia|].
      split; [assumption|]. split; [assumption|]. split; [replace (bv_unsigned sp - 112) with (bv_unsigned sp + -112) by lia; exact SKl|].
      split; [replace (bv_unsigned sp - 112) with (bv_unsigned sp + -112) by lia; exact FR|].
      split; [exact TABL|]. split; [exact NUQ|].
      left. split; [exact KLT|]. replace (bv_unsigned sp - 112) with (bv_unsigned sp + -112) by lia. cbv delta [mkR]. reflexivity.
    + (* [comment removed for export] *)
      assert (KEQ : kb = zlen NB) by lia.
      assert (NZ : nthz NB kb = 0).
      { unfold nthz. replace (kb <? zlen NB) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r. reflexivity. }
      rewrite NZ.
      zstepA. if_cases K4; zify_cond K4. 2:{ exfalso. revert K4. rewrite ?unsigned_lit by lia. lia. }
      cstep.     (* [comment removed for export] *)
      cstep.     (* [comment removed for export] *)
      apply evtA_done. unfold put_head_post. right.
      unfold put_regs, put_frame. unfold TBA, TD. rewrite <- !HTBA.
      do 5 eexists. exists mz. eexists. exists wl.
      split; [exact NONE|].
      split; [eapply munch_weaken; [| exact MU]; intros xx Hxx; cbn [outside] in Hxx |- *; clear -CEILB Hxx; lia|].
      split; [assumption|]. split; [assumption|]. split; [replace (bv_unsigned sp - 112) with (bv_unsigned sp + -112) by lia; exact SKl|].
      split; [replace (bv_unsigned sp - 112) with (bv_unsigned sp + -112) by lia; exact FR|].
      split; [exact TABL|]. split; [exact NUQ|].
      right. split; [exact KEQ|]. replace (bv_unsigned sp - 112) with (bv_unsigned sp + -112) by lia. cbv delta [mkR]. reflexivity.
Qed.
End PUTH.
End RC__1.
