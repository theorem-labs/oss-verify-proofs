(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AllocWalkKit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_Leaves AW_LargeAlloc1 AW_LargeAlloc2 AW_LargeAlloc3 AW_GetBlockBegin AllocTacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocPerfKit.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocStoreDj. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import LiaGuard.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_rx8 segs m a bs.   (* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

Definition recycle_sec1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo a TH : Z)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (AINST + 64)) (wz (AINST + 688)) (wz (a + 4096)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1997e0) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (6976832, 6976836); (TH + 2840, TH + 2856)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' 6976832 [C8 (wz 0)]
    /\ stk asegs m' (TH + 2800) (TH + 3168).
End HCW.

Section Rec1.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo a msz sz idx pa nres nch srt TSD CTX TH sb n actx : Z) (chunks : list Z) (ob0 ob1 : byte).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 80 <= bv_unsigned sp.
  Hypothesis Ha1 : a1 = wz (a + 6128).
  Hypothesis AR : aapp a msz /\ a + msz <= aceil /\ a mod 4096 = 0 /\ 0x2000 <= msz.
  Hypothesis SBX : hidden (a + msz <= sb \/ sb + kSpaceSize <= a).
  Hypothesis SBR : hidden (AHI_LO <= sb /\ sb + kSpaceSize <= aceil).
  Hypothesis TPR : hidden (12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP).
  Hypothesis RNG : hidden (12109808 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).
  Hypothesis PLC : hidden ((CTX + 160 <= TH \/ TH + 4096 <= CTX) /\ (TH + 4096 <= a \/ a + msz <= TH) /\ (CTX + 160 <= a \/ a + msz <= CTX)).
  Hypothesis PAR : aapp pa (8 * nch) /\ pa + 8 * nch <= aceil.
  Hypothesis NCH : zlen chunks = nch /\ 1 <= nch.
  Hypothesis INA : In a chunks.
  Hypothesis DISJ : Forall (fun c => 0 <= c < 2^47 /\ (c <= a + 6128 -> c <= a)) chunks.
  Hypothesis NR : 0 <= n < 2^32.
  Hypothesis ENV : SENV tp TSD CTX TH m.
  Hypothesis SB32 : rw_cells asegs m (AINST + 32) [C8 (wz sb)].
  Hypothesis INST64 : rw_cells asegs m (AINST + 64) [C8 (wz 4096); C8 (wz pa); C8 (wz pa)].
  Hypothesis NRES : rw_cells asegs m (AINST + 112) [C8 (wz nres); C8 (wz nch); C8 (wz srt)].
  Hypothesis MTX : rw_cells asegs m (AINST + 680) [C8 (wz 0)].
  Hypothesis PA : u64arr asegs m pa (wlist chunks).
  Hypothesis HDR : rw_cells asegs m a [C8 (wz a); C8 (wz msz); C8 (wz sz); C8 (wz idx)].
  Hypothesis CHDR : rw_cells asegs m (a + 6128) [C1 ob0; C1 ob1; C2 (wz 0); C4 (wz n); C8 (wz actx)].
  Hypothesis TST : stk asegs m (TH + 2800) (TH + 3168).

  (* [comment removed for export] *)
  Let ARE : 12599296 <= a /\ a + msz <= aceil. Proof. exact (aapp_env _ _ (proj1 AR) ltac:(lia)). Qed.   (* [comment removed for export] *)
  Let PAE : 12599296 <= pa /\ pa + 8 * nch <= aceil. Proof. exact (aapp_env _ _ (proj1 PAR) ltac:(lia)). Qed.   (* [comment removed for export] *)
  Lemma recycle_sec1c : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (mX : mem),
    mem_inv asegs mX -> munch [(bv_unsigned sp - 80, bv_unsigned sp); (6976832, 6976836); (TH + 2840, TH + 2856)]%Z m mX -> wmono asegs m mX ->
    stk asegs mX lo (bv_unsigned sp + -48) ->
    rw_cells asegs mX (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs mX 6976832 [C8 (Z_to_bv 64 0)] -> stk asegs mX (TH + 2800) (TH + 3168) ->
    SENV tp TSD CTX TH mX -> rw_cells asegs mX 6976184 [C8 (Z_to_bv 64 sb)] ->
    rw_cells asegs mX (a + 6128) [C1 ob0; C1 ob1; C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
    evt asegs (recycle_sec1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo a TH)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 a0 (Z_to_bv 64 (a + 6128)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (a + 4096)) (Z_to_bv 64 6976152) (Z_to_bv 64 137438953472) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x199380) fc None mX (seg_rom asegs)).
  Proof.
    intros until mX. intros MIX MU WM ST1 FR MTX1 TST1 ENV1 SB1 CHDR1.
    clear MI ST ENV SB32 INST64 NRES MTX PA HDR CHDR TST.
    pose proof RNG as R; destruct R as [RNG']. pose proof TPR as R; destruct R as [TPR']. pose proof SBR as R; destruct R as [SBR'].
    pose proof AR as R; destruct R as (AHI & CE & AL & MSZ). pose proof PAR as R; destruct R as [PLO PHI]. pose proof NCH as R; destruct R as [LEN NCH1].
    unfold AHI_LO, AIMG_TOP, kSpaceSize, AINST in *. acb.
    change (6976152 + 684) with 6976836 in *. change (6976152 + 688) with 6976840 in *. change (6976152 + 64) with 6976216 in *.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof (bv_unsigned_in_range _ ob0) as OB0. pose proof (bv_unsigned_in_range _ ob1) as OB1. change (bv_modulus 8) with 256 in OB0, OB1.
    open_senv ENV1.
    region_table.
    (* [comment removed for export] *)
    step. callN getcurthreadstats_spec. all: rewrite ?unsigned_lit by lia. all: try eassumption; try (first [clear - HI RXb0 RXb RNG'; lia | (lia_guard; lia)]).
    all: try (unfold ATSDINIT; eassumption). all: try (acb; (lia_guard; lia)). all: try (unfold AIMG_TOP; lia).
    (* [comment removed for export] *)
    lazymatch goal with H : stk _ _ (TH + 2800) (TH + 3168) |- _ =>
      destruct (stk_split asegs _ (TH + 2800) (TH + 2840) (TH + 3168) H ltac:(hci; lia)) as [TS1 TS2]; clear H end.
    destruct (stk_split asegs _ (TH + 2840) (TH + 2856) (TH + 3168) TS2 ltac:(hci; lia)) as [TS3 TS4]. clear TS2.
    destruct (stk_cells _ _ _ TS3 ltac:(hci; lia)) as [sj SJ]. replace (TH + 2856 - (TH + 2840)) with 16 in SJ by lia. change (Z.to_nat 16) with 16%nat in SJ.
    apply (rw_cells_split_CB asegs _ _ [] 16 sj [] [8;8]%nat) in SJ; [| reflexivity]. cbn [mk_CB_cells app] in SJ.
    repeat match type of SJ with context [CB ?k (take ?i ?l)] => let J := fresh "jk" in remember (take i l) as J in SJ end.
    repeat match type of SJ with context [CB ?k (drop ?i ?l)] => let J := fresh "jk" in remember (drop i l) as J in SJ end.
    repeat match goal with H : _ = take _ _ |- _ => clear H | H : _ = drop _ _ |- _ => clear H end.
    unfold wz.
    step. step. step. step. step. step. step. step. st1. st1.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    step.
    pose proof SBX as R; destruct R as [SBX'].
    (* [comment removed for export] *)
    join_open JT JOIN.
    { step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
      2: step; step; if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia; [clear K2| exfalso; clear - K K2 SBX' MSZ; try acb; lia].
      1: join_here1 JT JOIN (20%bv : bv 5).
      join_again JT JOIN. }
    subst JT. intros x20. clear SBX'.
    (* [comment removed for export] *)
    all: do 9 step; step; step.
    all: lazymatch goal with H : stk _ _ lo _ |- _ => release_frame FR H (bv_unsigned sp) end.
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
           assert (TST' : stk asegs mm (TH + 2800) (TH + 3168))
             by (apply (stk_merge asegs _ _ (TH + 2840)); [exact TS1| |lia]; apply (stk_merge asegs _ _ (TH + 2856)); [exact TS3| exact TS4|lia]) end.
    all: apply evt_done; unfold recycle_sec1_post, AINST; do 13 eexists; split; [reflexivity|].
    all: repeat match goal with |- _ /\ _ => split end; try assumption.
  Qed.

  Theorem recycle_sec1 :
    evt asegs (recycle_sec1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo a TH)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x199214) fc None m (seg_rom asegs)).
  Proof.
    subst a1. pose proof ENV as ENV0. open_senv ENV.
    pose proof RNG as R; destruct R as [RNG']. pose proof TPR as R; destruct R as [TPR']. pose proof SBR as R; destruct R as [SBR'].
    destruct AR as (AHI & CE & AL & MSZ). destruct PAR as [PLO PHI]. destruct NCH as [LEN NCH1].
    unfold AHI_LO, AIMG_TOP, kSpaceSize, AINST in *. acb.
    change (6976152 + 32) with 6976184 in *. change (6976152 + 64) with 6976216 in *. change (6976152 + 112) with 6976264 in *.
    change (6976152 + 680) with 6976832 in *. change (6976152 + 684) with 6976836 in *. change (6976152 + 688) with 6976840 in *.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (6976832, 6976836); (TH + 2840, TH + 2856)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (LENW : Z.of_nat (length (wlist chunks)) = nch) by (unfold wlist; rewrite length_map; unfold zlen in LEN; lia).
    unfold wz in *. region_table.
    (* [comment removed for export] *)
    step. carve_frame 48%nat ST. spill_frame ltac:(do 6 step). step. step. step. step.
    (* [comment removed for export] *)
    step. step. step.
    pose proof SBX as R; destruct R as [SBX'].
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    join_open JT JOIN.
    { step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
      2: step; step; if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia; [clear K2| exfalso; clear - K K2 SBX' MSZ; try acb; lia].
      1: join_here1 JT JOIN (11%bv : bv 5).
      join_again JT JOIN. }
    subst JT. intros x11j.
    (* [comment removed for export] *)
    all: step; step; step.
    all: callN (get_block_begin_spec _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo (a + 6128) a msz sz idx pa nres nch srt chunks);
         rewrite ?unsigned_lit by lia; try eassumption; try reflexivity; try (first [clear - HI; lia | lia]).
    all: try (unfold AHI_LO; acb; lia).
    all: try (split; [exact AHI| clear - CE AL MSZ; lia]).   (* [comment removed for export] *)
    all: try (unfold AINST; first [change (6976152 + 64) with 6976216 | change (6976152 + 112) with 6976264 | change (6976152 + 680) with 6976832]; eassumption).
    all: unfold wz.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    all: pose proof SBX as R; destruct R as [SBX2]; step; step; step.
    join_open JT2 JOIN2.
    { step; if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia;
         [ step; if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia; [clear K3 K4 SBX2| exfalso; clear - K3 K4 SBX2 MSZ; try acb; lia] | step; clear K3 SBX2 ].
      1: join_here JT2 JOIN2.
      join_again JT2 JOIN2. }
    subst JT2. clear SBX2.
    all: senv_at ENV0 MU WM ENV9.
    all: eapply recycle_sec1c; try eassumption.
  Qed.
End Rec1.

