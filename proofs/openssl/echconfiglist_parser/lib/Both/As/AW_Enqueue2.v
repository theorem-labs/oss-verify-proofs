(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics F_memset
     AsDepotInv AsDepotHash AsDepotPut AsUnwind CidBits AW_Combined AW_PoisonShadow AW_Leaves AW_DepotFrame AW_AllocBase AllocWalkKit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_MallocBase AW_Put1 AW_Enqueue1 AllocTacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocPerfKit.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocStoreDj.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_rx8 segs m a bs.   (* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition enq_new_W (lo spv TH B LA : Z) : list ivl :=
  [(lo, spv + -2208); (TH + 2128, TH + 2132); (TH + 2784, TH + 2792); (B, B + 32); (TH + 80, TH + 112); (LA, LA + Z.min 8 LA)].

Definition enq_new_post (sp gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : mem) (lo U size TH qcache : Z) (k hdq LA qbytes B cnt : Z) (chunks : list Z) (j0 j1 j3 : word) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j2 : word) m',
    ms' = MS (enq_regs sp gp tp s7 s8 s9 s10 s11 U size TH qcache t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
             F (Z_to_bv 64 0x19b46c) fc None m' (seg_rom asegs)
    /\ munch (enq_new_W lo (bv_unsigned sp) TH B LA) m0 m'
    /\ wmono asegs m0 m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2208)
    /\ rw_cells asegs m' (TH + OT_TQ) [C8 (wz (k + 1)); C8 (wz (if k =? 0 then B else hdq)); C8 (wz B); C8 (wz (qbytes + (size + kBatchSize)))]
    /\ (k <> 0 -> rw_cells asegs m' LA [C8 (wz B)])
    /\ rw_cells asegs m' B [C8 (wz 0); C8 (wz (size + kBatchSize)); C8 (wz 1); C8 (wz (U + -16))]
    /\ stk asegs m' (B + 32) (B + kBatchSize)
    /\ rw_cells asegs m' (TH + 2128) [C4 (wz (cnt - 1))]
    /\ u32arr asegs m' (TH + 2144) (wlist (rev (tl chunks)))
    /\ stk asegs m' (TH + 2144 + 4 * (cnt - 1)) (TH + 2208)
    /\ rw_cells asegs m' (TH + 2768) [C8 j0; C8 j1; C8 j2; C8 j3].
End HCW.

Section EnqNewTail.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (sp gp tp t0 t1 t2 xa2 xa6 xa7 t3 t4 t5 t6 xra xs0 xs1 xs2 xs3 xs4 xs5 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m m0 : mem).
  Variables (lo U size TH qcache sb : Z) (k hdq LA qbytes : Z) (cnt : Z) (chunks : list Z) (B : Z) (jk : list byte) (j0 j1 j2 j3 : word).
  Let W := enq_new_W lo (bv_unsigned sp) TH B LA.
  (* [comment removed for export] *)
  Let W2 : list ivl := [(TH + 2128, TH + 2132); (TH + 2784, TH + 2792); (B, B + 32)].
  Let POST := enq_new_post sp gp tp s7 s8 s9 s10 s11 F fc m0 lo U size TH qcache k hdq LA qbytes B cnt chunks j0 j1 j3.

  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 2944 <= bv_unsigned sp.
  Hypothesis SPT : hidden (bv_unsigned sp + 16 <= 2^47).
  Hypothesis UR : hidden (aapp U 8 /\ AIMG_TOP + 16 <= U /\ U + 8 <= aceil).   (* [comment removed for export] *)
  Hypothesis SZ : 1 <= size < 2^32.
  Hypothesis THR : hidden (akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).
  Hypothesis SBR : hidden (AHI_LO <= sb /\ sb + kSpaceSize + kPageSize <= aceil /\ sb mod 65536 = 0).
  (* [comment removed for export] *)
  Hypothesis CNT : cnt = zlen chunks. Hypothesis HIT : 1 <= cnt <= 2.
  Hypothesis CPS : Forall (fun cp => 0 <= cp < 2^32) chunks.
  Hypothesis HB : B = sb + kBatchClass * 2^32 + hd 0 chunks * 16.
  Hypothesis BR : hidden (AHI_LO <= B /\ B + kBatchSize <= aceil /\ (TH + 4096 <= B \/ B + kBatchSize <= TH)).
  (* [comment removed for export] *)
  Hypothesis KR : 0 <= k /\ k + 1 < 2^64. Hypothesis QB : 0 <= qbytes /\ qbytes + size + kBatchSize < 2^64.
  Hypothesis HDQ : 0 <= hdq < 2^64. Hypothesis QCR : 0 <= qcache < 2^64.
  Hypothesis LAh : k <> 0 -> rw_cells asegs m LA [C8 (wz 0)]
                   /\ AHI_LO <= LA /\ LA + kBatchSize <= aceil /\ (TH + 4096 <= LA \/ LA + kBatchSize <= TH) /\ (B + kBatchSize <= LA \/ LA + kBatchSize <= B).
  (* [comment removed for export] *)
  Hypothesis MU : munch W m0 m. Hypothesis WM : wmono asegs m0 m.

  Theorem enq_new_tail :
    mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -2272) ->
    rw_cells asegs m (bv_unsigned sp + -2272)
      [CB 8 jk; C8 (wz (U + -16)); C8 (wz (TH + OT_CACHE)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (wz size);
       C8 (wz (TH + OT_TQ)); C8 (wz (AINST + OI_Q)); C8 (wz 0x19b46c)] ->
    rw_cells asegs m (TH + OT_TQ) [C8 (wz k); C8 (wz hdq); C8 (wz LA); C8 (wz qbytes)] ->
    rw_cells asegs m (TH + 2128) [C4 (wz cnt)] ->
    rw_cells asegs m (TH + 2136) [C8 (wz kBatchSize)] ->
    u32arr asegs m (TH + 2144) (wlist (rev chunks)) ->
    stk asegs m (TH + 2144 + 4 * cnt) (TH + 2208) ->
    rw_cells asegs m (TH + 2768) [C8 j0; C8 j1; C8 j2; C8 j3] ->
    rw_cells asegs m (AINST + OI_SPACEBEG) [C8 (wz sb)] ->
    stk asegs m B (B + kBatchSize) ->
    evt asegs POST
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2272)) gp tp t0 t1 t2 xs0 xs1
               (wz (TH + OT_TQ)) (wz (TH + OT_CACHE)) xa2 (wz (U + -16)) (wz size) (wz cnt) xa6 xa7
               xs2 xs3 xs4 xs5 (wz qcache) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19b4b8) fc None m (seg_rom asegs)).
  Proof.
    intros MI ST FR TQ PC1 PC2 PC3 PC4 STATS INST BJ.
    pose proof (munch_refl W2 m) as MU2. pose proof (wmono_refl asegs m) as WM2.
    unfold W, enq_new_W in MU. unfold W2 in MU2.
    unfold AINST, OI_Q, OI_SPACEBEG, OT_TQ, OT_CACHE, kBatchSize, kBatchCount, kBatchClass, kSpaceSize, kPageSize, wz in *.
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR.
    assert (BND : aceil <= lo /\ 4096 <= TH /\ TH + 4096 <= aceil /\ bv_unsigned sp + 16 <= 140737488355328
               /\ 12599312 <= U /\ U + 8 <= aceil /\ 140735193776128 <= aceil /\ 17594333495296 <= B /\ B + 8192 <= aceil
               /\ 17594333495296 <= sb /\ sb + 137438953472 + 4096 <= aceil)
      by (clear - LO THR SPT UR BR SBR; try acb; destruct THR as [THR']; destruct UR as [UR']; destruct BR as [BR']; destruct SPT as [SPT']; destruct SBR as [SBR'];
          unfold AHI_LO in *; acb; change (2^47)%Z with 140737488355328%Z in SPT'; aunf; change (2^37)%Z with 137438953472%Z in SBR'; lia).
    region_sides. name_bands.
    assert (PLh : hidden (TH + 4096 <= B \/ B + 8192 <= TH)) by (destruct BR as [BR']; constructor; clear - BR'; try acb; lia).
    replace (6976152 + 728) with 6976880 in FR by reflexivity. replace (6976152 + 32) with 6976184 in INST by reflexivity.
    assert (LENC : Z.of_nat (length (wlist (rev chunks))) = cnt) by (unfold wlist; rewrite length_map, length_rev; unfold zlen in CNT; lia).
    assert (CP : 0 <= hd 0 chunks < 2^32).
    { apply (Forall_forall _ _) with (x := hd 0 chunks) in CPS; [lia|]. destruct chunks; [unfold zlen in CNT; cbn in CNT; lia| left; reflexivity]. }
    (* [comment removed for export] *)
    step. step. st1.
    step. rewrite shl32_shr30 by lia. step. step. step. step.
    (* [comment removed for export] *)
    assert (NTH : nth_error (wlist (rev chunks)) (Z.to_nat (cnt - 1)) = Some (wz (hd 0 chunks))).
    { destruct chunks as [|cp rest]; [cbn in CNT; unfold zlen in CNT; cbn in CNT; lia|]. unfold wlist. cbn [rev hd]. rewrite map_app. cbn [map].
      rewrite nth_error_app2 by (rewrite length_map, length_rev; unfold zlen in CNT; cbn in CNT; lia).
      rewrite length_map, length_rev. replace (Z.to_nat (cnt - 1) - length rest)%nat with 0%nat by (unfold zlen in CNT; cbn in CNT; lia). reflexivity. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (u32arr_read asegs mc _ _ (cnt - 1) _ (wa (TH + 2144 + 4 * (cnt - 1))) PC3 NTH ltac:(hci; lia) ltac:(hci; unfold wa; f_equal; lia)) as RD end.
    step. rewrite zx32_wz by lia. clear RD NTH.
    (* [comment removed for export] *)
    assert (AL8 : (TH + 2784) mod 8 = 0) by (clear - THR; destruct THR as [THR']; destruct THR' as (X1 & X2 & X3); Z.div_mod_to_equations; aunf; lia).
    assert (ALR : 0 <= TH + 2784 < 2^64) by lia.
    astep.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step.
    match goal with |- context [Z_to_bv 64 (?x + (sb + 103079215104))] =>
      replace (Z_to_bv 64 (x + (sb + 103079215104))) with (Z_to_bv 64 B)
        by (rewrite HB; unfold wz; rewrite (unsigned_lit (hd 0 chunks)), Z.shiftl_mul_pow2 by lia; f_equal; lia) end.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    step. step. step. step.
    (* [comment removed for export] *)
    destruct (stk_split asegs _ B (B + 32) (B + 8192) BJ ltac:(hci; lia)) as [SL BJ']. clear BJ.
    destruct (stk_cells _ _ _ SL ltac:(hci; lia)) as [bj SJ]. clear SL.
    replace (B + 32 - B) with 32 in SJ by lia. change (Z.to_nat 32) with 32%nat in SJ.
    apply (rw_cells_split_CB asegs _ _ [] 32 bj [] [8;8;8;8]%nat) in SJ; [| reflexivity]. cbn [mk_CB_cells app] in SJ.
    repeat match type of SJ with context [CB ?n (take ?k ?l)] => let J := fresh "jb" in remember (take k l) as J in SJ end.
    repeat match goal with H : _ = take _ _ |- _ => clear H end.
    st1. st1. st1. st1.
    (* [comment removed for export] *)
    destruct chunks as [|cp rest]; [unfold zlen in CNT; cbn in CNT; lia|]; unfold wlist in PC3; cbn [rev] in PC3;
      rewrite map_app in PC3; apply u32arr_snoc in PC3; destruct PC3 as [PA PB3]; rewrite length_map, length_rev in PB3;
      replace (Z.of_nat (length rest)) with (cnt - 1) in PB3 by (unfold zlen in CNT; cbn in CNT; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (PC4' : stk asegs mc (TH + 2144 + 4 * (cnt - 1)) (TH + 2208)) end.
    { eapply stk_merge; [eapply stk_of_rw_cells; exact PB3| | cbn; lia]. cbn [cells_size csize Nat.add].
      replace (TH + 2144 + 4 * (cnt - 1) + Z.of_nat 4) with (TH + 2144 + 4 * cnt) by lia. exact PC4. }
    clear PB3 PC4. replace (cnt + -1) with (cnt - 1) in PC1 by lia.
    remember (map wz (rev rest)) as restw eqn:RW.
    assert (LENR : Z.of_nat (length restw) = cnt - 1) by (subst restw; rewrite length_map, length_rev; unfold zlen in CNT; cbn in CNT; lia).
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in K by lia.
      clear MU2 WM2 LAh. st1.
      (* [comment removed for export] *)
      st1. st1. step. step. st1.
      do 9 step.
      release_frame FR ST (bv_unsigned sp + -2208).
      apply evt_done. unfold POST, enq_new_post, enq_regs, enq_new_W, wz, AINST, OI_Q, OT_TQ, OT_CACHE, kBatchSize.
      replace (6976152 + 728) with 6976880 by reflexivity.
      do 14 eexists. eexists. eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
      split. { rewrite K. cbn [Z.eqb Z.add]. exact TQ. }
      split. { intros NZ. exfalso. exact (NZ K). }
      split; [exact SJ|]. split; [exact BJ'|]. split; [exact PC1|]. split; [cbn [tl]; unfold wlist; rewrite <- RW; exact PA|]. split; [exact PC4'|].
      exact STATS.
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in K by lia.
      destruct (LAh K) as (LC & LA1 & LA2 & LA3 & LA4).
      assert (LARh : hidden (17594333495296 <= LA /\ LA + 8192 <= aceil /\ (TH + 4096 <= LA \/ LA + 8192 <= TH) /\ (B + 8192 <= LA \/ LA + 8192 <= B)))
        by (constructor; unfold AHI_LO in LA1; clear - LA1 LA2 LA3 LA4; lia).
      assert (LAB : 17594333495296 <= LA /\ LA + 8192 <= aceil) by (unfold AHI_LO in LA1; clear - LA1 LA2; lia).
      clear LA1 LA2 LA3 LA4.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        eapply (rw_cells_transport asegs _ m mc) in LC; [| exact MU2| exact WM2| ] end.
      2:{ cbn [disjoint_from cells_size csize length Nat.add Nat.mul]. destruct LARh as [X]. clear - X BND; lia. }
      clear MU2 WM2.
      (* [comment removed for export] *)
      match goal with H : region_tabled |- _ => clear H end.
      step. st1. step. step.
      (* [comment removed for export] *)
      st1. st1. step. step. st1.
      do 9 step.
      release_frame FR ST (bv_unsigned sp + -2208).
      apply evt_done. unfold POST, enq_new_post, enq_regs, enq_new_W, wz, AINST, OI_Q, OT_TQ, OT_CACHE, kBatchSize.
      replace (6976152 + 728) with 6976880 by reflexivity.
      do 14 eexists. eexists. eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
      split. { replace (k =? 0) with false by (symmetry; apply Z.eqb_neq; exact K). exact TQ. }
      split. { intros _. exact LC. }
      split; [exact SJ|]. split; [exact BJ'|]. split; [exact PC1|]. split; [cbn [tl]; unfold wlist; rewrite <- RW; exact PA|]. split; [exact PC4'|].
      exact STATS.
  Qed.


End EnqNewTail.

Section EnqRefillPost.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (sp gp tp t0 t1 t2 xa2 xa6 xa7 t3 t4 t5 t6 xra xs0 xs1 xs2 xs3 xs4 xs5 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m m0 : mem).
  Variables (lo U size TH qcache sb : Z) (k hdq LA qbytes : Z) (cnt : Z) (chunks : list Z) (B : Z) (jk : list byte) (j0 j1 j2 j3 : word).
  Let W := enq_new_W lo (bv_unsigned sp) TH B LA.
  Let POST := enq_new_post sp gp tp s7 s8 s9 s10 s11 F fc m0 lo U size TH qcache k hdq LA qbytes B cnt chunks j0 j1 j3.

  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 2944 <= bv_unsigned sp.
  Hypothesis SPT : hidden (bv_unsigned sp + 16 <= 2^47).
  Hypothesis UR : hidden (aapp U 8 /\ AIMG_TOP + 16 <= U /\ U + 8 <= aceil).   (* [comment removed for export] *)
  Hypothesis SZ : 1 <= size < 2^32.
  Hypothesis THR : hidden (akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).
  Hypothesis SBR : hidden (AHI_LO <= sb /\ sb + kSpaceSize + kPageSize <= aceil /\ sb mod 65536 = 0).
  (* [comment removed for export] *)
  Hypothesis CNT : cnt = zlen chunks. Hypothesis HIT : 1 <= cnt <= 2.
  Hypothesis CPS : Forall (fun cp => 0 <= cp < 2^32) chunks.
  Hypothesis HB : B = sb + kBatchClass * 2^32 + hd 0 chunks * 16.
  Hypothesis BR : hidden (AHI_LO <= B /\ B + kBatchSize <= aceil /\ (TH + 4096 <= B \/ B + kBatchSize <= TH)).
  (* [comment removed for export] *)
  Hypothesis KR : 0 <= k /\ k + 1 < 2^64. Hypothesis QB : 0 <= qbytes /\ qbytes + size + kBatchSize < 2^64.
  Hypothesis HDQ : 0 <= hdq < 2^64. Hypothesis QCR : 0 <= qcache < 2^64.
  Hypothesis LAh : k <> 0 -> rw_cells asegs m LA [C8 (wz 0)]
                   /\ AHI_LO <= LA /\ LA + kBatchSize <= aceil /\ (TH + 4096 <= LA \/ LA + kBatchSize <= TH) /\ (B + kBatchSize <= LA \/ LA + kBatchSize <= B).
  (* [comment removed for export] *)
  Hypothesis MU : munch W m0 m. Hypothesis WM : wmono asegs m0 m.

  (* [comment removed for export] *)
  Theorem enq_refill_post : forall (xa1 xa2' xa3 xa4 xa5 : word),
    mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -2272) ->
    rw_cells asegs m (bv_unsigned sp + -2272)
      [CB 8 jk; C8 (wz (U + -16)); C8 (wz (TH + OT_CACHE)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (wz size);
       C8 (wz (TH + OT_TQ)); C8 (wz (AINST + OI_Q)); C8 (wz 0x19b46c)] ->
    rw_cells asegs m (TH + OT_TQ) [C8 (wz k); C8 (wz hdq); C8 (wz LA); C8 (wz qbytes)] ->
    rw_cells asegs m (TH + 2128) [C4 (wz cnt)] ->
    rw_cells asegs m (TH + 2136) [C8 (wz kBatchSize)] ->
    u32arr asegs m (TH + 2144) (wlist (rev chunks)) ->
    stk asegs m (TH + 2144 + 4 * cnt) (TH + 2208) ->
    rw_cells asegs m (TH + 2768) [C8 j0; C8 j1; C8 j2; C8 j3] ->
    rw_cells asegs m (AINST + OI_SPACEBEG) [C8 (wz sb)] ->
    stk asegs m B (B + kBatchSize) ->
    evt asegs POST
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2272)) gp tp t0 t1 t2 (wz (TH + 2128)) (wz (TH + OT_CACHE))
               (wz 1) xa1 xa2' xa3 xa4 xa5 xa6 xa7
               (wz (U + -16)) (wz (TH + OT_TQ)) (Z_to_bv 64 (bv_unsigned sp + -2128)) (wz size) (wz qcache) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19b5cc) fc None m (seg_rom asegs)).
  Proof.
    intros until xa5. intros MI ST FR TQ PC1 PC2 PC3 PC4 STATS INST BJ.
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR.
    assert (BND : aceil <= lo /\ 4096 <= TH /\ TH + 4096 <= aceil)
      by (clear - LO THR; destruct THR as [THR']; unfold AHI_LO in *; aunf; lia).
    region_sides. name_bands.
    unfold AINST, OI_Q, OI_SPACEBEG, OT_TQ, OT_CACHE, kBatchSize, wz in *.
    (* [comment removed for export] *)
    step. step. if_cases K; [exfalso; revert K; vm_compute; discriminate|]. clear K.
    step. step. step. step. rewrite sx32_wz by lia. step. step.
    eapply enq_new_tail; try eassumption.
  Qed.

End EnqRefillPost.
Section HCW.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.

(* [comment removed for export] *)
Definition enq_refill_pre_post (sp gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo U size TH qcache : Z) (jk : list byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR (wz 0x19b5cc) (Z_to_bv 64 (bv_unsigned sp + -2272)) gp tp t0 t1 t2 (wz (TH + 2128)) (wz (TH + OT_CACHE))
                  (wz (TH + OT_CACHE)) (wz (TH + 2128)) (wz AINST) (wz kBatchClass) (wz size) (wz AINST) a6 a7
                  (wz (U + -16)) (wz (TH + OT_TQ)) (Z_to_bv 64 (bv_unsigned sp + -2128)) (wz size) (wz qcache) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x19bdac) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp + -2208)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2272)
    /\ rw_cells asegs m' (bv_unsigned sp + -2272)
         [CB 8 jk; C8 (wz (U + -16)); C8 (wz (TH + OT_CACHE)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (wz size);
          C8 (wz (TH + OT_TQ)); C8 (wz (AINST + OI_Q)); C8 (wz 0x19b46c)].
End HCW.

Section EnqNewHead.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (sp gp tp t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo U size TH qcache sb : Z) (k hdq LA qbytes : Z) (cnt : Z) (chunks : list Z) (B : Z) (j0 j1 j2 j3 : word).
  Let W := enq_new_W lo (bv_unsigned sp) TH B LA.
  Let POST := enq_new_post sp gp tp s7 s8 s9 s10 s11 F fc m lo U size TH qcache k hdq LA qbytes B cnt chunks j0 j1 j3.

  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 2944 <= bv_unsigned sp.
  Hypothesis SPT : hidden (bv_unsigned sp + 16 <= 2^47).
  Hypothesis UR : hidden (aapp U 8 /\ AIMG_TOP + 16 <= U /\ U + 8 <= aceil).   (* [comment removed for export] *)
  Hypothesis SZ : 1 <= size < 2^32.
  Hypothesis THR : hidden (akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).
  Hypothesis SBR : hidden (AHI_LO <= sb /\ sb + kSpaceSize + kPageSize <= aceil /\ sb mod 65536 = 0).
  Hypothesis KR : 0 <= k /\ k + 1 < 2^64. Hypothesis QB : 0 <= qbytes /\ qbytes + size + kBatchSize < 2^64.
  Hypothesis HDQ : 0 <= hdq < 2^64. Hypothesis QCR : 0 <= qcache < 2^64.

  Ltac prepH :=
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR;
    assert (BND : aceil <= lo /\ 4096 <= TH /\ TH + 4096 <= aceil /\ bv_unsigned sp + 16 <= 140737488355328
               /\ 12599312 <= U /\ U + 8 <= aceil /\ 140735193776128 <= aceil /\ 17594333495296 <= sb /\ sb + 137438953472 + 4096 <= aceil)
      by (clear - LO THR SPT UR SBR; try acb; destruct THR as [THR']; destruct UR as [UR']; destruct SPT as [SPT']; destruct SBR as [SBR'];
          unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, ALOWSH_LO in *; unfold AHI_LO, kSpaceSize, kPageSize in *; acb; change (2^47)%Z with 140737488355328%Z in SPT'; change (2^37)%Z with 137438953472%Z in SBR'; aunf; lia);
    region_sides; name_bands.

  (* [comment removed for export] *)
  Section Hit.
    Hypothesis CNT : cnt = zlen chunks. Hypothesis HIT : 1 <= cnt <= 2.
    Hypothesis CPS : Forall (fun cp => 0 <= cp < 2^32) chunks.
    Hypothesis HB : B = sb + kBatchClass * 2^32 + hd 0 chunks * 16.
    Hypothesis BR : hidden (AHI_LO <= B /\ B + kBatchSize <= aceil /\ (TH + 4096 <= B \/ B + kBatchSize <= TH)).
    (* [comment removed for export] *)
    Hypothesis LAh : k <> 0 -> (rw_cells asegs m LA [C8 (wz 0)] /\ rw_cells asegs m (LA + 16) [C8 (wz kBatchCount)])
                     /\ AHI_LO <= LA /\ LA + kBatchSize <= aceil /\ (TH + 4096 <= LA \/ LA + kBatchSize <= TH) /\ (B + kBatchSize <= LA \/ LA + kBatchSize <= B).

    Theorem enq_new_hit :
      mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -2208) ->
      rw_cells asegs m (TH + OT_TQ) [C8 (wz k); C8 (wz hdq); C8 (wz LA); C8 (wz qbytes)] ->
      rw_cells asegs m (TH + 2128) [C4 (wz cnt)] ->
      rw_cells asegs m (TH + 2136) [C8 (wz kBatchSize)] ->
      u32arr asegs m (TH + 2144) (wlist (rev chunks)) ->
      stk asegs m (TH + 2144 + 4 * cnt) (TH + 2208) ->
      rw_cells asegs m (TH + 2768) [C8 j0; C8 j1; C8 j2; C8 j3] ->
      rw_cells asegs m (AINST + OI_SPACEBEG) [C8 (wz sb)] ->
      stk asegs m B (B + kBatchSize) ->
      evt asegs POST
        (MS (mkR (wz 0x19b46c) (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0 t1 t2 (wz (AINST + OI_Q)) (wz (TH + OT_TQ))
                 (wz (TH + OT_TQ)) (wz (TH + OT_CACHE)) (Z_to_bv 64 (bv_unsigned sp + -2128)) (wz (U + -16)) (wz size) a5 a6 a7
                 (wz size) (Z_to_bv 64 (bv_unsigned sp + -2128)) (wz (TH + OT_CACHE)) (wz (U + -16)) (wz qcache) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x19b478) fc None m (seg_rom asegs)).
    Proof.
      intros MI ST TQ PC1 PC2 PC3 PC4 STATS INST BJ.
      pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
      pose proof (munch_refl [(lo, bv_unsigned sp + -2208)] m) as MU2. pose proof (wmono_refl asegs m) as WM2.   (* [comment removed for export] *)
      unfold W, enq_new_W in MU. prepH.
      unfold AINST, OI_Q, OI_SPACEBEG, OT_TQ, OT_CACHE, kBatchSize, kBatchCount, kBatchClass, kSpaceSize, kPageSize, wz in *.
      assert (PLh : hidden (TH + 4096 <= B \/ B + 8192 <= TH)) by (destruct BR as [BR']; constructor; clear - BR'; try acb; lia).
      replace (6976152 + 728) with 6976880 by reflexivity. replace (6976152 + 32) with 6976184 in INST by reflexivity.
      assert (LENC : Z.of_nat (length (wlist (rev chunks))) = cnt) by (unfold wlist; rewrite length_map, length_rev; unfold zlen in CNT; lia).
      (* [comment removed for export] *)
      step. carve_frame 64%nat ST. do 7 st1.
      step. step. if_cases K; zify_cond K.
      - (* [comment removed for export] *)
        rewrite ?unsigned_lit in K by lia.
        (* [comment removed for export] *)
        step. rewrite sx32_wz by lia. step. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.
        clear MU2 WM2. eapply enq_new_tail; try eassumption; try reflexivity.
        { intros NZ. exfalso. exact (NZ K). }
      - (* [comment removed for export] *)
        rewrite ?unsigned_lit in K by lia.
        destruct (LAh K) as ([LC LCC] & LA1 & LA2 & LA3 & LA4).
        assert (LARh : hidden (17594333495296 <= LA /\ LA + 8192 <= aceil /\ (TH + 4096 <= LA \/ LA + 8192 <= TH) /\ (B + 8192 <= LA \/ LA + 8192 <= B)))
          by (constructor; unfold AHI_LO in LA1; clear - LA1 LA2 LA3 LA4; lia).
        assert (LAB : 17594333495296 <= LA /\ LA + 8192 <= aceil) by (unfold AHI_LO in LA1; clear - LA1 LA2; lia).
        match goal with H : region_tabled |- _ => clear H end.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
          eapply (rw_cells_transport asegs _ m mc) in LCC; [| exact MU2| exact WM2| cbn [disjoint_from cells_size csize length Nat.add Nat.mul]; clear - LAB BND; lia] end.
        step. step. step. step. if_cases K2; zify_cond K2. { exfalso. apply K2. reflexivity. } clear K2.
        (* [comment removed for export] *)
        step. rewrite sx32_wz by lia. step. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
          eapply (rw_cells_transport asegs _ m mc) in LC; [| exact MU2| exact WM2| cbn [disjoint_from cells_size csize length Nat.add Nat.mul]; clear - LAB BND; lia] end.
        clear MU2 WM2. eapply enq_new_tail; try eassumption; try reflexivity.
        { intros _. split; [exact LC| split; [exact LA1| split; [exact LA2| split; [exact LA3| exact LA4]]]]. }
    Qed.
  End Hit.

  (* [comment removed for export] *)
  Section Miss.
    Let POSTR := enq_refill_pre_post sp gp tp s7 s8 s9 s10 s11 F fc m lo U size TH qcache.
    Hypothesis LAh : k <> 0 -> (rw_cells asegs m LA [C8 (wz 0)] /\ rw_cells asegs m (LA + 16) [C8 (wz kBatchCount)])
                     /\ AHI_LO <= LA /\ LA + kBatchSize <= aceil /\ (TH + 4096 <= LA \/ LA + kBatchSize <= TH).

    Theorem enq_refill_pre :
      mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -2208) ->
      rw_cells asegs m (TH + OT_TQ) [C8 (wz k); C8 (wz hdq); C8 (wz LA); C8 (wz qbytes)] ->
      rw_cells asegs m (TH + 2128) [C4 (wz 0)] ->
      evt asegs (fun ms' => exists jk, POSTR jk ms')
        (MS (mkR (wz 0x19b46c) (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0 t1 t2 (wz (AINST + OI_Q)) (wz (TH + OT_TQ))
                 (wz (TH + OT_TQ)) (wz (TH + OT_CACHE)) (Z_to_bv 64 (bv_unsigned sp + -2128)) (wz (U + -16)) (wz size) a5 a6 a7
                 (wz size) (Z_to_bv 64 (bv_unsigned sp + -2128)) (wz (TH + OT_CACHE)) (wz (U + -16)) (wz qcache) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x19b478) fc None m (seg_rom asegs)).
    Proof.
      intros MI ST TQ PC1.
      pose proof (munch_refl [(lo, bv_unsigned sp + -2208)] m) as MU. pose proof (wmono_refl asegs m) as WM.
      prepH.
      unfold AINST, OI_Q, OI_SPACEBEG, OT_TQ, OT_CACHE, kBatchSize, kBatchCount, kBatchClass, kSpaceSize, kPageSize, wz in *.
      replace (6976152 + 728) with 6976880 by reflexivity.
      (* [comment removed for export] *)
      step. carve_frame 64%nat ST. do 7 st1.
      repeat match type of FR with context [CB ?n (take ?kk ?l)] => let J := fresh "jk" in remember (take kk l) as J in FR end.
      repeat match goal with H : _ = take _ _ |- _ => clear H end.
      (* [comment removed for export] *)
      step.
      join_open JT JOIN.
      { step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
        (* [comment removed for export] *)
        2: destruct (LAh K) as ([LC LCC] & LA1 & LA2 & LA3).
        2: assert (LAB : 17594333495296 <= LA /\ LA + 8192 <= aceil) by (unfold AHI_LO in LA1; clear - LA1 LA2; lia).
        2: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
            eapply (rw_cells_transport asegs _ m mc) in LCC; [| exact MU| exact WM| cbn [disjoint_from cells_size csize length Nat.add Nat.mul]; clear - LAB BND; lia] end.
        2: step; step; step; step; if_cases K2; zify_cond K2; [exfalso; apply K2; reflexivity|]; clear K2.
        1: join_here3 JT JOIN (15%bv : bv 5) (16%bv : bv 5) (17%bv : bv 5).
        join_again JT JOIN. }
      subst JT. intros x15j x16j x17j.
      (* [comment removed for export] *)
      all: step; change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0); step; if_cases K3; zify_cond K3; [| exfalso; apply K3; reflexivity]; clear K3.
      all: do 13 step.
      all: apply evt_done; exists jk; unfold POSTR, enq_refill_pre_post, wz, AINST, OI_Q, OT_TQ, OT_CACHE, kBatchClass;
           replace (6976152 + 728) with 6976880 by reflexivity.
      all: do 10 eexists; split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact ST| exact FR].
    Qed.
  End Miss.
End EnqNewHead.
