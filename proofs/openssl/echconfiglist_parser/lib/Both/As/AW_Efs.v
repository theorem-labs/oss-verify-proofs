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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics F_memset AllocWalkKit AW_DepotFrame AW_Leaves AW_PoisonShadow AW_MmapFixed.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N8Store.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

End HCW.


Ltac deadK K := first [ exfalso; apply K; reflexivity
                      | exfalso; revert K; vm_compute; discriminate
                      | exfalso; revert K; rewrite ?unsigned_lit by lia; lia ].

(* [comment removed for export] *)
Section HCW2.
  Context {HCEIL : HeapCeil}.

Lemma rw_cells_C8_zero_bytes : forall mm A, rw_cells asegs mm A [C8 (wz 0)] -> rw_cells asegs mm A [C1 (b8 0); CB 7 (repeat (b8 0) 7)].
Proof.
  intros mm A [[Hwf Hb] Hw]. split; [split|].
  - cbn. repeat split; reflexivity.
  - cbn [cells_bytes cbytes app] in *. exact Hb.
  - exact Hw.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kWriterLock : Z := 1152921504606846976.
Definition rinfo_cells (nf mfa au mu : Z) : list cell :=
  [C8 (wz kWriterLock); C4 (wz 0); C4 (wz 0); C8 (wz nf); C8 (wz mfa); C8 (wz au); C8 (wz 0); C8 (wz mu); C8 (wz 0)].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition efs_fast_post (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists (a1 a2 a3 a4 a5 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).
End HCW2.

Section Fast.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo R rbeg nfreed nf mfa au mu : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 48 <= bv_unsigned sp.
  Hypothesis Ha1 : a1 = wz R. Hypothesis Ha3 : a3 = wz nfreed.
  Hypothesis RR : AHI_LO <= R /\ R + 128 <= aceil.
  Hypothesis NF : 0 <= nfreed /\ 4 * nfreed <= mfa /\ mfa <= kFreeArraySize.
  Hypothesis RI : rw_cells asegs m R (rinfo_cells nf mfa au mu).

  Theorem efs_fast_spec :
    evt asegs (efs_fast_post ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x199e78) fc None m (seg_rom asegs)).
  Proof.
    unfold rinfo_cells, AHI_LO, kFreeArraySize in *. subst a1 a3.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. acb.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold wz in *.
    (* [comment removed for export] *)
    step. carve_frame 48%nat ST. do 5 step. step. step. step. step. (* [comment removed for export] *)
    rewrite (unsigned_lit nfreed) by lia. rewrite (Z.shiftl_mul_pow2 nfreed 2) by lia. change (2^2) with 4.
    if_cases K; zify_cond K. 2:{ exfalso. revert K. rewrite ?unsigned_lit by lia. clear - NF; try acb. lia. } clear K.
    (* [comment removed for export] *)
    step. do 5 step. step. step. release_frame FR ST (bv_unsigned sp). finish.
  Qed.
End Fast.
Section HCW2.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition efs_new (nfreed : Z) : Z := round_up (4 * nfreed) kFreeArrayMapSize.

Definition efs_seg1_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 a6 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo R FAB mfa nfreed : Z) : machine_state -> Prop :=
  fun ms' => exists m' (j8 j44 : list byte),
    let cur := FAB + mfa in let sz := efs_new nfreed - mfa in
    ms' = MS (mkR (wz 0x1d36d8) (Z_to_bv 64 (bv_unsigned sp + -176)) gp tp t0 t1 t2 (wz sz) (wz 1) (wz cur) (wz sz) (wz 3) (wz 50) (Z_to_bv 64 (-1)) (wz 0) a6 (wz 222)
                  (wz cur) (wz 0x2cd48) (wz APAGESZ) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1d1904) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 448, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -176)
    /\ rw_cells asegs m' (bv_unsigned sp + -176) [C4 (wz 50); CB 44 j44; C8 s4; C8 (wz R); C8 (wz sz); C8 (wz cur); C8 (wz sz); C8 (wz 0x1dcd98);
                                                  C8 (wz sz); C8 (wz cur); C8 (wz (efs_new nfreed)); C8 (wz 0x199f18)]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 j8; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
End HCW2.

Section Seg1.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo R rbeg nfreed nf mfa au mu : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 448 <= bv_unsigned sp.
  Hypothesis Ha0 : a0 = wz AINST. Hypothesis Ha1 : a1 = wz R. Hypothesis Ha2 : a2 = wz rbeg. Hypothesis Ha3 : a3 = wz nfreed.
  Hypothesis RR : AHI_LO <= R /\ R + 128 <= aceil.
  Hypothesis RB : AHI_LO <= rbeg /\ rbeg + 2^32 <= aceil /\ rbeg mod 65536 = 0.
  Hypothesis NF : 0 <= nfreed /\ mfa < 4 * nfreed /\ 4 * nfreed <= kFreeArraySize /\ 0 <= mfa /\ mfa mod kFreeArrayMapSize = 0.
  Hypothesis RI : rw_cells asegs m R (rinfo_cells nf mfa au mu).
  Hypothesis PMH : rw_cells asegs m (AINST + 56) [C8 (wz 0)].
  Hypothesis GOT : rw_cells asegs m AGOT_LO (map (fun v => C8 (wz v)) AGOT_VALS).
  Hypothesis PSC : rw_cells asegs m APAGESZ [C8 (wz 4096)].
  Hypothesis DPM : rw_cells asegs m (ACFLAGS + 260) [C1 (b8 0)].

  Theorem efs_seg1 :
    evt asegs (efs_seg1_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 a6 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo R (rbeg + kFreeArrayOffset) mfa nfreed)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x199e78) fc None m (seg_rom asegs)).
  Proof.
    apply rw_cells_C8_zero_bytes in PMH.
    unfold rinfo_cells, AHI_LO, kFreeArraySize, kFreeArrayMapSize, kFreeArrayOffset, AINST, AGOT_LO, AGOT_VALS, APAGESZ, ACFLAGS in *. cbn [map] in GOT.
    subst a0 a1 a2 a3. change (6976152 + 56) with 6976208 in PMH. change (7586856 + 260) with 7587116 in DPM.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. acb.
    pose proof (munch_refl [(bv_unsigned sp - 448, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NEW : 4 * nfreed <= efs_new nfreed < 4 * nfreed + 262144 /\ efs_new nfreed mod 262144 = 0 /\ efs_new nfreed <= 536870912)
      by (unfold efs_new, round_up, kFreeArrayMapSize; clear - NF; try acb; Z.div_mod_to_equations; lia).
    unfold wz in *.
    (* [comment removed for export] *)
    step. carve_frame 48%nat ST. do 5 step. step. step. step. step.
    rewrite (unsigned_lit nfreed) by lia. rewrite (Z.shiftl_mul_pow2 nfreed 2) by lia. change (2^2) with 4.
    if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by lia. clear - NF; try acb. lia. } clear K.
    (* [comment removed for export] *)
    step. step. step. step. step.
    match goal with |- context [Z_to_bv 64 (Z.land ?x 18446744073709289472)] =>
      replace (Z_to_bv 64 (Z.land x 18446744073709289472)) with (Z_to_bv 64 (efs_new nfreed)) end.
    2:{ rewrite (unsigned_lit (nfreed * 4 + 262143)) by (clear - NF; try acb; lia). change 18446744073709289472 with (2^64 - 2^18)%Z. rewrite StrFun.land_align_down by (clear - NF; try acb; lia).
        f_equal. unfold efs_new, round_up, kFreeArrayMapSize. clear - NF; try acb. Z.div_mod_to_equations. lia. }
    step. step. step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by lia. clear - NEW; try acb. lia. } clear K.
    (* [comment removed for export] *)
    step. rewrite zxb_b8 by lia. step. step. step. step. step. if_cases K; zify_cond K. 2:{ deadK K. } clear K.
    (* [comment removed for export] *)
    step. step. step. step. step. step.
    rewrite (unsigned_lit (efs_new nfreed)) by (clear - NEW NF; try acb; lia). rewrite (unsigned_lit mfa) by (clear - NF; try acb; lia).
    replace (mfa + (rbeg + 3758096384)) with (rbeg + 3758096384 + mfa) by (clear; lia).
    step. callD (map_or_die_seg1 _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo (rbeg + 3758096384 + mfa) (efs_new nfreed - mfa) 183624).
    all: rewrite ?unsigned_lit by lia. all: try eassumption; try reflexivity; try (clear - HI; try acb; lia).
    { clear - RB NF NEW; try acb. lia. }
    { clear - NF NEW; try acb. Z.div_mod_to_equations. lia. }
    replace (bv_unsigned sp + -48 + -128) with (bv_unsigned sp + -176) in * by lia.
    apply evt_done. unfold efs_seg1_post. cbv zeta. exists x, (take 8 (take 16 (take 24 (take 32 (take 40 junk))))), x0.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact PC|]. split; [exact POST| exact FR].
  Qed.
End Seg1.
Section HCW2.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition efs_seg2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo R TH cur sz nf au mu newfa : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 208, bv_unsigned sp); (sh cur, sh cur + sz / 8); (TH + 2800, TH + 3168); (R + 24, R + 32)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' R (rinfo_cells nf newfa au mu)
    /\ poisoned m' cur (Z.to_nat (sz / 8)) 0xfa
    /\ stk asegs m' (TH + 2800) (TH + 3168).
End HCW2.

Section Seg2.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo R cur sz newfa nf mfa au mu TSD CTX TH : Z) (j8 j44 sbs : list byte).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp + -176).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 448 <= bv_unsigned sp. Hypothesis SPT : bv_unsigned sp + 16 <= 2^47. Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis F176 : rw_cells asegs m (bv_unsigned sp + -176) [C4 (wz 50); CB 44 j44; C8 s4; C8 (wz R); C8 (wz sz); C8 (wz cur); C8 (wz sz); C8 (wz 0x1dcd98);
                                                             C8 (wz sz); C8 (wz cur); C8 (wz newfa); C8 (wz 0x199f18)].
  Hypothesis F48 : rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j8; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis RR : AHI_LO <= R /\ R + 128 <= aceil.
  Hypothesis CUR : AHI_LO <= cur /\ cur + sz <= aceil /\ cur mod 4096 = 0 /\ sz mod 4096 = 0 /\ 0 < sz /\ 0 <= newfa < 2^64.
  Hypothesis TPR : 4096 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP.
  Hypothesis RNG : 12109808 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil.
  Hypothesis SEP : hidden ((TH + 4096 <= R \/ R + 128 <= TH) /\ (TH + 4096 <= cur \/ cur + sz <= TH) /\ (R + 128 <= cur \/ cur + sz <= R)).
  Hypothesis RI : rw_cells asegs m R (rinfo_cells nf mfa au mu).
  Hypothesis TST : stk asegs m (TH + 2800) (TH + 3168).
  Hypothesis SH : u8arr asegs m (sh cur) sbs. Hypothesis SHL : Z.of_nat (length sbs) = sz / 8.
  Hypothesis GOT : rw_cells asegs m AGOT_LO (map (fun v => C8 (wz v)) AGOT_VALS).
  Hypothesis MLIM : rw_cells asegs m (ACFLAGS + 144) [C8 (wz 0)].
  Hypothesis CTHR : rw_cells asegs m (ACFLAGS + 120) [C8 (wz 0xffffffffffffffff)].
  Hypothesis CCAN : rw_cells asegs m ACANPOISON [C1 (b8 1)].
  Hypothesis CSHB : rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)].
  Hypothesis CHME : rw_cells asegs m AHIGHMEMEND [C8 (wz (2^47 - 1)); C8 (wz 0); C8 (wz 0)].
  Hypothesis CRMS : rw_cells asegs m AREALMEMSET [C8 (wz AMEMSET)].
  Hypothesis CTSDI : rw_cells asegs m ATSDINIT [C1 (b8 1); CB 3 [b8 0; b8 0; b8 0]; C4 (wz 0)].
  Hypothesis CTP : rw_cells asegs m (bv_unsigned tp + -88) [C8 (wz TSD)].
  Hypothesis CTSD : rw_cells asegs m TSD [C8 (wz CTX)].
  Hypothesis CCTX : rw_cells asegs m (CTX + 152) [C8 (wz TH)].

  Theorem efs_seg2 :
    evt asegs (efs_seg2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo R TH cur sz nf au mu newfa)
      (MS (mkR (wz 0x1d36d8) (Z_to_bv 64 (bv_unsigned sp + -176)) gp tp t0 t1 t2 (wz sz) (wz 1) (wz cur) a1 a2 a3 a4 a5 a6 a7
               (wz cur) (wz 0x2cd48) (wz APAGESZ) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1d1908) fc None m (seg_rom asegs)).
  Proof.
    unfold rinfo_cells, AHI_LO, AIMG_TOP, AGOT_LO, AGOT_VALS, APAGESZ, ACFLAGS, ACANPOISON, ASHBASE_CELL, ASHADOW_BASE, AHIGHMEMEND, AREALMEMSET, AMEMSET, ATSDINIT in *.
    cbn [map] in GOT. change (7586856 + 144) with 7587000 in MLIM. change (7586856 + 120) with 7586976 in CTHR.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. acb.
    pose proof SEP as SEPx. destruct SEPx as [SEPx].
    pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp); (sh cur, sh cur + sz / 8); (TH + 2800, TH + 3168); (R + 24, R + 32)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    assert (SHR : 2148314624 <= sh cur /\ sh cur + sz / 8 <= 17594333495296) by (clear - CUR; try acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    callD (map_seg2 (wz 0x199f18) gp tp t0 t1 t2 (wz newfa) (wz cur) a1 a2 a3 a4 a5 a6 a7 (wz sz) (wz R) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (bv_unsigned sp + -176) lo cur sz).
    all: rewrite ?unsigned_lit by lia. all: try eassumption; try reflexivity; try (clear - HI; try acb; lia); try (clear - CUR; try acb; lia); try (clear - SPT; try acb; lia); try (clear - SPA; try acb; Z.div_mod_to_equations; lia).
    clear ST. rename POST into ST. replace (bv_unsigned sp + -176 + 128) with (bv_unsigned sp + -48) in * by lia.
    replace (ret_pc (wz 1679128)) with (Z_to_bv 64 1679128) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    unfold wz. step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by lia. clear - CUR; try acb. lia. } clear K.
    step. step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
    step. step. step. step.
    (* [comment removed for export] *)
    pose proof (aapp_lit _ _ (proj1 (proj2 (proj2 RNG)))) as CTXS.
    pose proof (akobj_lit _ _ (proj1 (proj2 (proj2 (proj2 (proj2 RNG)))))) as THS.
    callD (poison_shadow_spec _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo cur sz 250 sbs).
    all: rewrite ?unsigned_lit by (first [clear - ACEILB SPR HI LO; lia | lia]). all: try reflexivity; try eassumption.
    all: try (unfold AHI_LO, ALOWSH_LO; acb; clear - CUR RR; try acb; lia).
    all: try (clear - HI; try acb; lia). all: try (clear; lia).
    all: try (unfold ACANPOISON, AGOT_LO, AGOT_VALS, ASHBASE_CELL, ASHADOW_BASE, AHIGHMEMEND, ACFLAGS, AREALMEMSET, AMEMSET, wz; cbn [map]; eassumption).
    rename PC into ST. destruct POST as (P0 & P8 & PU). remember (poison_bytes (Z.to_nat (sz / 8)) 250) as pb eqn:EPB.
    assert (LPB : Z.of_nat (length pb) = sz / 8) by (subst pb; unfold poison_bytes; rewrite repeat_length; clear - CUR; try acb; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    step. callD (getcurthreadstats_spec _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo TSD CTX TH).
    all: rewrite ?unsigned_lit by (first [clear - ACEILB SPR HI LO; lia | lia]). all: try eassumption.
    all: try (clear - HI; try acb; lia). all: try (clear - TPR; try acb; unfold AIMG_TOP; lia). all: try (acb; clear - RNG; try acb; aunf; lia).
    all: try (unfold ATSDINIT, wz; eassumption).
    rename POST into ST. unfold wz. clear CTXS.
    (* [comment removed for export] *)
    destruct (stk_split asegs _ _ (TH + 2872) _ TST ltac:(hci; clear; lia)) as [TS1 TS2].
    destruct (stk_split asegs _ _ (TH + 2888) _ TS2 ltac:(hci; clear; lia)) as [TS3 TS4]. clear TS2 TST.
    destruct (stk_cells _ _ _ TS3 ltac:(hci; clear; lia)) as [jst JST]. clear TS3.
    replace (TH + 2888 - (TH + 2872)) with 16 in JST by (clear; lia). change (Z.to_nat 16) with 16%nat in JST.
    apply (rw_cells_split_CB asegs _ _ [] 16 jst [] [8;8]%nat) in JST; [| reflexivity]. cbn [mk_CB_cells app] in JST.
    (* [comment removed for export] *)
    step. step. step. step. step. step.
    (* [comment removed for export] *)
    step. step. step. step. do 5 step. step. step.
    release_frame F48 ST (bv_unsigned sp).
    pose proof (stk_of_rw_cells asegs _ _ _ JST) as TS2. cbn [cells_size csize Nat.add] in TS2.
    assert (TSTn : stk asegs m0 (TH + 2800) (TH + 3168)).
    { eapply stk_merge; [exact TS1| |clear; lia]. eapply stk_merge; [| exact TS4| clear; lia].
      replace (TH + 2888) with (TH + 2872 + Z.of_nat 16) by (clear; lia). exact TS2. }
    apply evt_done. unfold efs_seg2_post. do 14 eexists. exists m0.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact ST|].
    split; [exact RI|]. split; [| exact TSTn]. unfold poisoned, SHAD. subst pb. split; [exact P0|]. split; [exact P8|]. exact PU.
  Qed.
End Seg2.

