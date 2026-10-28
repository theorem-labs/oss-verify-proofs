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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AllocWalkKit F_memset.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_Leaves AW_PoisonShadow AW_MmapFixed AW_SecMmap CidBits SecMsb AW_Combined AW_AllocBase AW_LargeAlloc1 AllocTacX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition large_alloc_seg2b_post (sp gp tp t0 t1 t2 a6 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo size msz a pa nres : Z) (stat : word) : machine_state -> Prop :=
  fun ms' => exists m' (j44 : list byte),
    ms' = MS (mkR (wz 0x1d36d8) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 (wz 0x20000) (wz 0) (wz (pa + 8 * nres)) (wz 0x20000) (wz 3) (wz 50) (Z_to_bv 64 (-1)) (wz 0) a6 (wz 222)
                  (wz (pa + 8 * nres)) (wz 0) (wz APAGESZ) (wz a) (wz (a + msz)) (wz (a + 4096 + size)) (wz 7) (wz (a + 4096)) s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1d1904) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 464, bv_unsigned sp + -96)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -192)
    /\ rw_cells asegs m' (bv_unsigned sp + -192) [C4 (wz 50); CB 44 j44; C8 (wz (a + 4096)); C8 (wz (clzbits msz)); C8 (wz msz); C8 (wz (AINST + 64)); C8 stat; C8 (wz 0x19bd90)].

Section Seg2b.
  Variables (sp gp tp t0 t1 t2 a1 a2 a5 a6 a7 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (stat : word) (lo size msz a pa nres TSD CTX TH : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp + -96).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 464 <= bv_unsigned sp.
  Hypothesis SZ : 0x10000 < size /\ size <= 2^41. Hypothesis MSZ : size + 4096 <= msz /\ msz < size + 8192.
  Hypothesis AR : aapp a msz /\ a + msz <= aceil.
  Hypothesis PAR : aapp pa kPtrArrayReserve /\ pa + kPtrArrayReserve <= aceil /\ pa mod 4096 = 0.
  Hypothesis NCH : 0 <= nres /\ nres + 16384 <= 2^20. Hypothesis NRQ : exists q, nres = 512 * q.
  Hypothesis ENV : SENV tp TSD CTX TH m.
  Hypothesis INST64 : rw_cells asegs m 6976216 [C8 (wz 4096); C8 (wz pa); C8 (wz pa)].
  Hypothesis NRES : rw_cells asegs m 6976264 [C8 (wz nres); C8 (wz nres); C8 (wz 0)].

  Let ARE : 12599296 <= a /\ a + msz <= aceil. Proof. exact (aapp_env _ _ (proj1 AR) ltac:(lia)). Qed.   (* [comment removed for export] *)
  Let PAE : 12599296 <= pa /\ pa + kPtrArrayReserve <= aceil. Proof. exact (aapp_env _ _ (proj1 PAR) ltac:(clear; hci; unfold kPtrArrayReserve; lia)). Qed.   (* [comment removed for export] *)
  Theorem large_alloc_seg2b :
    evt asegs (large_alloc_seg2b_post sp gp tp t0 t1 t2 a6 s10 s11 t3 t4 t5 t6 F fc m lo size msz a pa nres stat)
      (MS (mkR (wz 0x19ba5c) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2
               stat (wz (AINST + 64)) (wz (a + 4096)) a1 a2 (wz nres) (wz nres) a5 a6 a7
               (wz msz) (wz (clzbits msz)) (wz a) (wz a) (wz (a + msz)) (wz (a + 4096 + size)) (wz 7) (wz (a + 4096)) s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19bb94) fc None m (seg_rom asegs)).
  Proof.
    destruct NRQ as [nq NQ].
    assert (BEGAL : (pa + 8 * nres) mod 4096 = 0).
    { rewrite NQ. replace (pa + 8 * (512 * nq)) with (pa + nq * 4096) by lia. rewrite Z_mod_plus_full. destruct PAR as (_ & _ & E). exact E. }
    assert (BND : aceil <= lo /\ 12599296 <= pa /\ pa + 8388608 <= aceil /\ 140735332483072 <= aceil).   (* [comment removed for export] *)
    { unfold AHI_LO, kPtrArrayReserve in *. acb. aunf. lia. }
    unfold AINST, APAGESZ in *. change (6976152 + 64) with 6976216 in *.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 464, bv_unsigned sp + -96)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    region_table.
    pose proof (se_got _ _ _ _ _ ENV) as Egot. unfold AGOT_VALS in Egot; cbn [map] in Egot. pose proof (se_psc _ _ _ _ _ ENV) as Epsc.
    unfold wz in *.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
    (* [comment removed for export] *)
    step. step. step. rewrite (unsigned_lit nres), Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
    step. try rewrite (unsigned_lit pa) by lia. replace (nres * 8 + pa) with (pa + 8 * nres) by lia.
    step. step. step. step. step.
    callN map_or_die0_seg1; rewrite ?unsigned_lit by lia; try eassumption; try reflexivity; try (acb; lia); try lia.
    replace (bv_unsigned sp + -96 + -96) with (bv_unsigned sp + -192) in * by lia.
    apply evt_done. unfold large_alloc_seg2b_post, AINST. change (6976152 + 64) with 6976216. exists x, x0.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. exact POST.
  Qed.
End Seg2b.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition large_alloc_seg4_post (sp gp tp t0 t1 t2 a6 a7 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo size msz a nres : Z) (stat : word) : machine_state -> Prop :=
  fun ms' => exists (a1 a2 a4 a5 : word) m',
    ms' = MS (mkR (wz 0x19bd90) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2
                  stat (wz (AINST + 64)) (wz (a + 4096)) a1 a2 (wz nres) a4 a5 a6 a7
                  (wz msz) (wz (clzbits msz)) (wz (a + 4096)) (wz a) (wz (a + msz)) (wz (a + 4096 + size)) (wz 7) (wz (a + 4096)) s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x19bb98) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 192, bv_unsigned sp + -96); (6976264, 6976272)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -96)
    /\ rw_cells asegs m' 6976264 [C8 (wz (nres + 16384)); C8 (wz nres); C8 (wz 0)].

Section Seg4.
  Variables (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (stat : word) (j44 : list byte) (lo size msz a pa nres TSD CTX TH : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp + -192).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 464 <= bv_unsigned sp. Hypothesis SPH : bv_unsigned sp + 16 <= 2^47.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0).
  Hypothesis AR : aapp a msz /\ a + msz <= aceil. Hypothesis MSZ : size + 4096 <= msz.
  Hypothesis PAR : aapp pa kPtrArrayReserve /\ pa + kPtrArrayReserve <= aceil.
  Hypothesis NCH : 0 <= nres /\ nres + 16384 <= 2^20.
  Hypothesis ENV : SENV tp TSD CTX TH m.
  Hypothesis FR2 : rw_cells asegs m (bv_unsigned sp + -192) [C4 (wz 50); CB 44 j44; C8 (wz (a + 4096)); C8 (wz (clzbits msz)); C8 (wz msz); C8 (wz (AINST + 64)); C8 stat; C8 (wz 0x19bd90)].
  Hypothesis NRES : rw_cells asegs m 6976264 [C8 (wz nres); C8 (wz nres); C8 (wz 0)].

  Let ARE : 12599296 <= a /\ a + msz <= aceil. Proof. pose proof (proj1 AR) as X. clear - X. aunf. lia. Qed.   (* [comment removed for export] *)
  Let PAE : 12599296 <= pa /\ pa + kPtrArrayReserve <= aceil. Proof. exact (aapp_env _ _ (proj1 PAR) ltac:(clear; hci; unfold kPtrArrayReserve; lia)). Qed.   (* [comment removed for export] *)
  Theorem large_alloc_seg4 :
    evt asegs (large_alloc_seg4_post sp gp tp t0 t1 t2 a6 a7 s10 s11 t3 t4 t5 t6 F fc m lo size msz a nres stat)
      (MS (mkR (wz 0x1d36d8) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 (wz 0x20000) (wz 0) (wz (pa + 8 * nres)) a1 a2 a3 a4 a5 a6 a7
                  (wz (pa + 8 * nres)) (wz 0) (wz APAGESZ) (wz a) (wz (a + msz)) (wz (a + 4096 + size)) (wz 7) (wz (a + 4096)) s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1d1908) fc None m (seg_rom asegs)).
  Proof.
    assert (BND : aceil <= lo /\ 12599296 <= pa /\ pa + 8388608 <= aceil /\ 12599296 <= a /\ a + msz <= aceil /\ 140735332483072 <= aceil).   (* [comment removed for export] *)
    { unfold AHI_LO, kPtrArrayReserve in *. acb. aunf. lia. }
    assert (SPQ : exists spq, bv_unsigned sp = 16 * spq) by (destruct SPA as [SPA']; exists (bv_unsigned sp / 16); Z.div_mod_to_equations; lia).
    region_sides. name_bands.
    destruct SPQ as [spq SPQ].
    unfold AINST, APAGESZ in *. change (6976152 + 64) with 6976216 in *.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp + -96); (6976264, 6976272)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    region_table.
    pose proof (se_got _ _ _ _ _ ENV) as Egot. unfold AGOT_VALS in Egot; cbn [map] in Egot. pose proof (se_mlim _ _ _ _ _ ENV) as Emlim.
    unfold wz in *.
    callN mmap_fixed_seg2; rewrite ?unsigned_lit by lia; try eassumption; try reflexivity; try (acb; lia); try lia.
    replace (bv_unsigned sp + -192 + 96) with (bv_unsigned sp + -96) in * by lia.
    replace (ret_pc (Z_to_bv 64 1686928)) with (Z_to_bv 64 1686928) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    clear Egot Emlim.
    (* [comment removed for export] *)
    step. step. step. step. step. try rewrite (unsigned_lit nres) by lia. st1. step.
    apply evt_done. unfold large_alloc_seg4_post, AINST. change (6976152 + 64) with 6976216. do 5 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. exact NRES.
  Qed.
End Seg4.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Seg2c.
  Variables (sp gp tp t0 t1 t2 a1 a2 a5 a6 a7 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (stat : word) (size msz a nres nch : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis NCH : 0 <= nch < nres /\ nres <= 2^20.

  Theorem large_alloc_seg2c :
    evt asegs (fun ms' => ms' = MS (mkR (wz 0x19ba5c) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2
                                       stat (wz (AINST + 64)) (wz (a + 4096)) a1 a2 (wz nch) (wz nres) a5 a6 a7
                                       (wz msz) (wz (clzbits msz)) (wz a) (wz a) (wz (a + msz)) (wz (a + 4096 + size)) (wz 7) (wz (a + 4096)) s10 s11 t3 t4 t5 t6)
                                  F (Z_to_bv 64 0x19bb98) fc None m (seg_rom asegs)
                          /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m)
      (MS (mkR (wz 0x19ba5c) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2
               stat (wz (AINST + 64)) (wz (a + 4096)) a1 a2 (wz nch) (wz nres) a5 a6 a7
               (wz msz) (wz (clzbits msz)) (wz a) (wz a) (wz (a + msz)) (wz (a + 4096 + size)) (wz 7) (wz (a + 4096)) s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19bb94) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold wz.
    step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by lia. lia. } clear K.
    apply evt_done. split; [reflexivity|]. split; [exact MU|]. split; [exact WM| exact MI].
  Qed.
End Seg2c.

End HCW.

