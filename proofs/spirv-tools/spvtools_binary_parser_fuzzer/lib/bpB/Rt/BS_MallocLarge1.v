(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BStrFun.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BsAtomics BsDepotInv BsDepotHash BsDepotPut BsUnwind BllocWalkKit BW_PoisonShadow BW_Leaves BW_DepotFrame BW_AllocBase BW_MallocBase BW_MallocPre BW_AllocPreSec BllocTacX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

Definition malloc_large_head_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo size needed TSD CTX TH sb : Z) (T : list Z) (d : depot) : machine_state -> Prop :=
  fun ms' => exists (x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 : word) (jk j8 : list byte) (rest : list word) m',
    ms' = MS (mkR (wz 0x9273c) (Z_to_bv 64 (bv_unsigned sp + -2272)) gp tp x5 x6 x7 (wz 0) (wz size) (wz AINST) (wz (TH + 208)) (wz needed) (wz 8) x14 x15 x16 x17
                  (wz 8) (wz needed) (wz 2048) (wz size) (wz AINST) (wz (bv_unsigned sp + -2128)) (Z_to_bv 64 (-8)) (wz 7) (wz TH) (wz 1) x28 x29 x30 x31)
             F (Z_to_bv 64 0x96bf4) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (TH + 3168, TH + 3169)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ AENV tp TSD CTX TH sb (bv_unsigned sp + -2128) T rest m' /\ length rest = (255 - length T)%nat
    /\ Forall (fun x => 0 <= x < 2^64) T /\ (1 <= length T <= 30)%nat
    /\ stk asegs m' lo (bv_unsigned sp + -2272)
    /\ aframe (Z_to_bv 64 (bv_unsigned sp + -2144)) (wz 0x9246c) sp (wz size) (wz 0xba3ac) (wz 1)
              (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81)) s6 s7 s8 s9 s10 s11 m' j8
    /\ rw_cells asegs m' (bv_unsigned sp + -2144) [C8 sp; C8 (wz 0xba418)]
    /\ rw_cells asegs m' (bv_unsigned sp + -72) [C8 sp]
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [CB 8 jk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' (TH + 3168) [C1 (b8 0)]
    /\ DEPOT asegs d m'.

Section Head.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo size needed : Z) (d : depot).
  Variables (TSD CTX TH TOP BOT : Z) (CH : list (Z * Z)).
  Variables (sb : Z).
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) TOP CH.
  Let T := utrace 0xba3ac (bv_unsigned sp) TOP BOT 30 CHI.
  Hypothesis DNEED : hidden (needed = round_up (Z.max size 8) 8 + 4096).
  Let POST := malloc_large_head_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo size needed TSD CTX TH sb T d.

  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 2496 <= bv_unsigned sp.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0).
  Hypothesis SPT : hidden (bv_unsigned sp + 16 <= 2^47).
  Hypothesis SZ : 64512 < size < 2^32.
  Hypothesis TPR : hidden (6762376 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP).
  Hypothesis RNG : hidden (6762288 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).
  Hypothesis PLC : hidden ((TH + 4096 <= sb \/ sb + kSpaceSize + 4096 <= TH) /\ (CTX + 160 <= sb \/ sb + kSpaceSize + 4096 <= CTX)
                /\ (CTX + 160 <= TH \/ TH + 4096 <= CTX)).
  Hypothesis PLCD : hidden ((TH + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= TH) /\ (TH + 4096 <= d_sb d \/ d_sb d + 8 * 32768 <= TH)
                /\ (sb + kSpaceSize + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= sb) /\ (sb + kSpaceSize + 4096 <= d_sb d \/ d_sb d + 8 * 32768 <= sb)
                /\ (CTX + 160 <= d_nb d \/ d_nb d + 16 * 65536 <= CTX) /\ (CTX + 160 <= d_sb d \/ d_sb d + 8 * 32768 <= CTX)
                /\ aapp (d_nb d) (16 * 65536) /\ aapp (d_sb d) (8 * 32768)).
  Hypothesis SBR : hidden (AHI_LO <= sb /\ sb + kSpaceSize <= aceil).
  Hypothesis TBR : hidden (4096 <= TOP <= 2^47 /\ 0 <= BOT < TOP).
  Hypothesis DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 32768 <= lo.
  Hypothesis FCH : goodframe BOT (bv_unsigned sp) TOP = true -> goodframe (bv_unsigned sp) (bv_unsigned s0) TOP = true ->
                   bv_unsigned sp + 16 <= bv_unsigned s0 /\ frame_chain asegs m TOP (bv_unsigned s0) CH.
  Hypothesis Ha0 : a0 = wz size.

  Theorem malloc_large_head :
    IENV tp TSD CTX TH sb TOP BOT m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) ->
    rw_cells asegs m (TH + 3168) [C1 (b8 0)] ->
    DEPOT asegs d m ->
    evt asegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xba2e4) fc None m (seg_rom asegs)).
  Proof.
    intros ENV MI ST UNW DEP.
    pose proof (munch_refl [(lo, bv_unsigned sp); (TH + 3168, TH + 3169)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
    pose proof SPT as R; destruct R as [SPT']. pose proof SPA as R; destruct R as [SPA'].
    unfold wz in *. unfold AINST.

    callD (malloc_pre ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo size d TSD CTX TH TOP BOT CH sb).
    all: rewrite ?unsigned_lit by lia.
    { exact LO. } { exact HI. } { exact SPA. } { exact SPT. } { exact TPR. } { exact RNG. } { exact PLC. } { exact PLCD. } { exact TBR. }
    { exact DLO. } { exact FCH. } { exact Ha0. } { exact ENV. } { exact MI. } { exact ST. } { exact UNW. } { exact DEP. }
    all: pose proof RNG as R; destruct R as [RNG']; pose proof TPR as R; destruct R as [TPR']; pose proof PLCD as R; destruct R as [PLCD'];
         unfold AHI_LO, AIMG_TOP, kSpaceSize in RNG', TPR', PLCD'; acb.
    all: try (repeat (first [apply Forall_nil | apply Forall_cons; [cbn [fst snd]; clear - RNG' TPR' PLCD' LO HI DLO SPR; try acb; aunf; lia|]])).
    repeat match goal with H : context [utrace 0xba3ac _ _ _ _ _] |- _ => progress (fold CHI in H; fold T in H) end.
    lazymatch goal with H : IENV _ _ _ _ _ _ _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into ENV1 end.
    pose proof ENV1 as E. open_ienv E.
    lazymatch goal with H : u64arr asegs ?mm (bv_unsigned sp + -2128 + 16) (map wz T ++ ?rest) |- _ =>
      assert (AE : AENV tp TSD CTX TH sb (bv_unsigned sp + -2128) T rest mm)
        by (econstructor; try eassumption; replace (bv_unsigned sp + -2128 + 16) with (bv_unsigned sp + -2128 + 16) by lia; eassumption) end.
    clear Etsdi Etp Etsd Ectx Elsan Egot2 Ethr Etid Einit Eafl Ecan Egot Eshb Ehme Ethresh Erms Efill Epart Ehooks Einst1 Einst2 Emcs Epsc Ecfu Estk Et40.

    lazymatch goal with H : AENV tp TSD CTX TH sb _ T ?rest ?mm |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
      callD (@allocate_pre_sec _ (Z_to_bv 64 0x9246c) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp _ _ _ sp (Z_to_bv 64 size) (Z_to_bv 64 AINST)
               (Z_to_bv 64 size) (Z_to_bv 64 8) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 1) (Z_to_bv 64 1) _ _
               (Z_to_bv 64 0xba3ac) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81)) s6 s7 s8 s9 s10 s11 _ _ _ _
               F fc mm lo size needed (bv_unsigned sp + -2128) T rest TSD CTX TH sb) end.
    all: rewrite ?unsigned_lit by lia.
    { exact DNEED. }
    { exact LO. }
    { clear - HI; try acb; lia. }
    { constructor. replace (bv_unsigned sp + -2144) with (bv_unsigned sp + (-134) * 16) by lia. rewrite Z_mod_plus_full. exact SPA'. }
    { exact SZ. }
    { exact TPR. }
    { exact RNG. }
    { exact SBR. }
    { constructor. clear - SPT'; try acb. lia. }
    { reflexivity. } { reflexivity. } { reflexivity. } { reflexivity. } { reflexivity. } { reflexivity. }
    { exact AE. }
    { assumption. }
    { assumption. }
    replace (bv_unsigned sp + -2144 + -128) with (bv_unsigned sp + -2272) in * by lia.
    clear AE ENV1.
    apply evt_done. unfold POST, malloc_large_head_post, wz, AINST.
    lazymatch goal with H : rw_cells asegs ?mm (bv_unsigned sp + -64) (CB 8 ?jk :: _), H2 : aframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm2 ?j8,
                         H3 : u64arr asegs _ _ (map _ T ++ ?rest) |- _ =>
      do 11 eexists; exists jk, j8, rest, mm2 end.
    split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try assumption; try exact (conj PC10 POST0).
  Qed.
End Head.

End HCW.

