(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 1137 of its 1175 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_block.v; 1090 of its 1202 lines of code are new or changed and 1063 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P5.v, with its module paths, module names, addresses and numbers changed; 1009 of its 1131 lines of code are new or changed and 1080 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A3.v, with its module paths, module names and addresses changed; 258 of its 469 lines of code are new or changed and 920 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/A3.v a3_evt_mid (:286), a3_evt (:428) at a working branch
     3803efccea0 (blob 58a6459b5bc00a145c2dbe52aefe900a1fafd88a);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: both source runs call asan_set_shadow_f8 (jal 0x55144 at 0x8121c), so each is split at that call and
     no <run>_of_F is written.  The stretches re-run these source lines:
       a3_evt_mid_pre_F  = A3.v:286-428, the 68 `a3_sb` shadow stores and the four instructions 0x81210..0x8121c,
                           up to the callee entry 0x55144 (meta_fill_f8);
       a3_evt_mid_post_F = A3.v:376-424, the bookkeeping the source does after `eapply evt_cut`, stated over the
                           post-call machine state (no MemNorm.evt_normalize: the walk composes the callee itself);
       a3_evt_pre_F      = A3.v:461-567, the spill word, the nine register instructions, the three header stores
                           and 0x810f8/0x810fc, then a3_evt_mid_pre_F;
       a3_evt_post_F     = A3.v:570-598, the same bookkeeping for the whole-segment Q.
     a3_lib_evt (A3.v:93) is the UL/lib.Lib engine bridge; every _F here is stated on the lib.Lib ExecF engine, so
     it has no _F twin (nothing to bridge).
   The statements are on the lib.Lib copies of MS / mkR / getr; the source states the UL copies, which are the
   same definitions (UL's MS is the same record, UL's mkR the same tree through #[local] Abbreviations). *)
(* rule 24: no function proved. *)
(* Route (C) (a Theorem Labs lane 09:38Z, amendment 10:34Z; a Theorem Labs lane, 2026-10-29): a3_evt_mid_pre_F_on and a3_evt_pre_F_on
   carry the proofs; a3_evt_mid_pre_F and a3_evt_pre_F keep their statements as corollaries.  The premise
   `shadow_rw m` becomes `B.ShadowRwOn.shadow_rw_on R m`, R the 68 shadow bytes the run stores into,
   [S(fr), S(fr) + 68) (the `rng RNG (Sfr fr) 68` row and the 68 `sb r,k(s3)` stores, k = 0..67); the run reads no
   shadow byte.  The post `shadow_rw m'` becomes `forall P, shadow_rw_on P m -> shadow_rw_on P m'`: every store keeps
   every present byte (B.Prog.MemMono.rd_mono) and every writable byte (wmono), so no P is excluded. *)
(* Segment A3 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B): the footprint twins of cut Inv_B810c4
   (0x810c4) -> cut Inv_B81220 (0x81220).  Accesses: the spill word [A + 336, A + 344), the frame header
   [fr, fr + 24) and the first 68 shadow bytes [S(fr), S(fr) + 68).  The remaining 187 shadow bytes
   [S(fr) + 68, S(fr) + 255) are written by the callee, so they are not in these footprints. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06 YN2e.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge Cells Step Exec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require asan_set_shadow_c MemMono.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ShadowRwOn ShadowRwOnT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require A3.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.

(* ---- Route (C): the store invariant of the 68 frame-shadow stores.  A3.a3_J carries shadow_rw; a3f_J carries
   rd_mono instead, and each store takes its shadow byte's writability from the run's narrowed premise over the
   run's start memory m0 (wmono carries it to the current memory). ---- *)
Definition a3_evt_mid_pre_F_shadow_R (Sh : Z) : Z -> Prop := fun a => Sh <= a < Sh + 68.

Definition a3f_J (m0 : word -> option byte) (Sh : Z) (m : word -> option byte) : Prop :=
  munch [(Sh, Sh + 392)] m0 m /\ wmono rsegs m0 m /\ B.Prog.MemMono.rd_mono m0 m /\ ro_agree rsegs m.

Lemma a3f_J_init : forall m Sh, ro_agree rsegs m -> a3f_J m Sh m.
Proof.
  intros m Sh HRO. split; [apply munch_refl|]. split; [apply wmono_refl|].
  split; [apply B.Prog.MemMono.rd_mono_refl | exact HRO].
Qed.

Lemma a3f_J_store_ok : forall (P : Z -> Prop) m0 Sh m a, a3f_J m0 Sh m -> B.ShadowRwOn.shadow_rw_on P m0 -> P a ->
  in_shadow a -> store_ok rsegs m (wa a) 1 = true.
Proof.
  intros P m0 Sh m a (_ & WM & _ & _) HP Pa Ha.
  pose proof (in_shadow_range a Ha) as Hr.
  apply (B.Prog.MemMono.wv_store_ok m0 m a 1); [| exact WM | lia | lia].
  intros i Hi. replace i with 0 by lia. rewrite Z.add_0_r. exact (proj1 (HP a Pa Ha)).
Qed.

Lemma a3f_J_store : forall m0 Sh m a bs, a3f_J m0 Sh m -> Sh <= a < Sh + 392 -> in_shadow a ->
  length bs = 1%nat -> a3f_J m0 Sh (write_to_mem m (wa a) bs).
Proof.
  intros m0 Sh m a bs (MU & WM & RD & HRO) Hin Ha Hl.
  pose proof (in_shadow_range a Ha) as Hr.
  assert (HGT : AC.GT <= a).
  { unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, AC.GT in Ha |- *. lia. }
  split; [|split; [|split]].
  - apply munch_write; [exact MU | lia | rewrite Hl; lia | rewrite Hl; cbn [inside]; left; lia].
  - apply wmono_write. exact WM.
  - apply B.Prog.MemMono.rd_mono_write. exact RD.
  - apply A3.a3_ro_write; [exact HRO | lia | rewrite Hl; lia | exact HGT].
Qed.

(* A3.v's a3_sb with the evtF goal pattern (four arguments; pilot fix (2)): one frame-shadow store
   `sb r,k(s3)` (s3 = Sh), store_ok from the invariant and the narrowed premise, one step, the invariant again. *)
Ltac a3f_sb Sh k :=
  lazymatch goal with
  | HJ : a3f_J ?m0 Sh ?mc, HSR : B.ShadowRwOn.shadow_rw_on (a3_evt_mid_pre_F_shadow_R Sh) ?m0,
    HSH : forall i, 0 <= i < 392 -> in_shadow (Sh + i) |- _ =>
      let HS := fresh "HS" in
      assert (HS : store_ok rsegs mc (wa (Sh + k)) 1 = true)
        by (exact (a3f_J_store_ok (a3_evt_mid_pre_F_shadow_R Sh) m0 Sh mc (Sh + k) HJ HSR
                     ltac:(unfold a3_evt_mid_pre_F_shadow_R; lia) (HSH k ltac:(lia))));
      step;
      lazymatch goal with
      | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem mc ?aa ?bb) _) =>
          let HJ' := fresh "HJn" in
          assert (HJ' : a3f_J m0 Sh (write_to_mem mc aa bb))
            by (apply (a3f_J_store m0 Sh mc (Sh + k) bb HJ);
                [ lia | exact (HSH k ltac:(lia))
                | first [ reflexivity | apply length_le1 | apply length_Z_to_le_bytes ] ]);
          clear HS; clear HJ;
          let m' := fresh "mc" in
          set (m' := write_to_mem mc aa bb) in *; clearbody m'
      end
  end.

(* ---- a3_evt_mid, part 1: 0x81100 (the first shadow store) to the callee entry 0x55144. ---- *)
Lemma a3_evt_mid_pre_F_on :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sh : Z),
    s3 = Z_to_bv 64 Sh -> s4 = Z_to_bv 64 (-8) -> s5 = Z_to_bv 64 (-14) ->
    (forall i, 0 <= i < 392 -> in_shadow (Sh + i)) ->
    B.ShadowRwOn.shadow_rw_on (a3_evt_mid_pre_F_shadow_R Sh) m -> ro_agree rsegs m -> asan_cells m ->
    rng RNG Sh 68 ->
    evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x55144) fc None m' (seg_rom rsegs) /\
         getr R 1 = Z_to_bv 64 0x81220 /\ getr R 10 = Z_to_bv 64 (Sh + 68) /\
         getr R 11 = Z_to_bv 64 187 /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = Z_to_bv 64 Sh /\ getr R 20 = Z_to_bv 64 (-8) /\
         getr R 21 = Z_to_bv 64 (-14) /\ getr R 22 = s6 /\ getr R 24 = s8 /\ getr R 25 = s9 /\
         getr R 26 = s10 /\ getr R 27 = Z_to_bv 64 (Sh + 68) /\
         munch [(Sh, Sh + 392)] m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\
         (forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m') /\
         asan_cells m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81100) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sh -> -> -> HSH HSR HRO HAC RSH.
  pose proof (HSH 0 ltac:(lia)) as Hin0. rewrite Z.add_0_r in Hin0.
  pose proof (HSH 391 ltac:(lia)) as Hin379.
  assert (HSlo : LOWMEM_END <= Sh)
    by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin0 |- *; lia).
  assert (HShi : Sh + 392 <= HIGHMEM_BEG)
    by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin379 |- *; lia).
  assert (HGT : AC.GT <= Sh) by (unfold AC.GT, LOWMEM_END in *; lia).
  unfold LOWMEM_END in HSlo. unfold HIGHMEM_BEG in HShi. unfold AC.GT in HGT.
  pose proof (a3f_J_init m Sh HRO) as HJ.
  (* the 68 frame-shadow stores *)
  a3f_sb Sh 4. a3f_sb Sh 5. a3f_sb Sh 6. a3f_sb Sh 7.
  a3f_sb Sh 0. a3f_sb Sh 1. a3f_sb Sh 2. a3f_sb Sh 3.
  a3f_sb Sh 12. a3f_sb Sh 13. a3f_sb Sh 14. a3f_sb Sh 15.
  a3f_sb Sh 8. a3f_sb Sh 9. a3f_sb Sh 10. a3f_sb Sh 11.
  a3f_sb Sh 20. a3f_sb Sh 21. a3f_sb Sh 22. a3f_sb Sh 23.
  a3f_sb Sh 16. a3f_sb Sh 17. a3f_sb Sh 18. a3f_sb Sh 19.
  a3f_sb Sh 28. a3f_sb Sh 29. a3f_sb Sh 30. a3f_sb Sh 31.
  a3f_sb Sh 24. a3f_sb Sh 25. a3f_sb Sh 26. a3f_sb Sh 27.
  a3f_sb Sh 36. a3f_sb Sh 37. a3f_sb Sh 38. a3f_sb Sh 39.
  a3f_sb Sh 32. a3f_sb Sh 33. a3f_sb Sh 34. a3f_sb Sh 35.
  a3f_sb Sh 44. a3f_sb Sh 45. a3f_sb Sh 46. a3f_sb Sh 47.
  a3f_sb Sh 40. a3f_sb Sh 41. a3f_sb Sh 42. a3f_sb Sh 43.
  a3f_sb Sh 52. a3f_sb Sh 53. a3f_sb Sh 54. a3f_sb Sh 55.
  a3f_sb Sh 48. a3f_sb Sh 49. a3f_sb Sh 50. a3f_sb Sh 51.
  a3f_sb Sh 60. a3f_sb Sh 61. a3f_sb Sh 62. a3f_sb Sh 63.
  a3f_sb Sh 56. a3f_sb Sh 57. a3f_sb Sh 58. a3f_sb Sh 59.
  a3f_sb Sh 64. a3f_sb Sh 65. a3f_sb Sh 66. a3f_sb Sh 67.
  (* 0x81210..0x8121c: addi s11,s3,68 ; li a1,187 ; mv a0,s11 ; jal 0x55144 *)
  step. step. step. step.
  lazymatch goal with
  | HJ : a3f_J m Sh ?mcx |- _ => pose proof HJ as HJf; set (mf := mcx) in *
  end.
  pose proof HJf as (MUc & WMc & RDc & ROc).
  assert (SWc : forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P mf)
    by (intros P HP; exact (B.ShadowRwOnT.shadow_rw_on_mem_mono P m mf HP WMc RDc)).
  assert (ACc : asan_cells mf)
    by (apply (A3.a3_asan_keep [(Sh, Sh + 392)] m mf HAC MUc);
        intros x Hx; cbn [outside]; split; [unfold AC.GT in *; lia | exact I]).
  apply evtF_done.
  eexists. eexists.
  split; [reflexivity|].
  repeat (split; [first [ reflexivity
                        | rewrite !MState.unsigned_lit by lia; reflexivity
                        | assumption ]|]).
  assumption.
Qed.

(* The old statement, from the narrowed one (B.ShadowRwOn.shadow_rw_on_of_shadow_rw; the post at P := fun _ => True,
   B.ShadowRwOn.shadow_rw_of_on_all). *)
Lemma a3_evt_mid_pre_F :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sh : Z),
    s3 = Z_to_bv 64 Sh -> s4 = Z_to_bv 64 (-8) -> s5 = Z_to_bv 64 (-14) ->
    (forall i, 0 <= i < 392 -> in_shadow (Sh + i)) ->
    shadow_rw m -> ro_agree rsegs m -> asan_cells m ->
    rng RNG Sh 68 ->
    evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x55144) fc None m' (seg_rom rsegs) /\
         getr R 1 = Z_to_bv 64 0x81220 /\ getr R 10 = Z_to_bv 64 (Sh + 68) /\
         getr R 11 = Z_to_bv 64 187 /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = Z_to_bv 64 Sh /\ getr R 20 = Z_to_bv 64 (-8) /\
         getr R 21 = Z_to_bv 64 (-14) /\ getr R 22 = s6 /\ getr R 24 = s8 /\ getr R 25 = s9 /\
         getr R 26 = s10 /\ getr R 27 = Z_to_bv 64 (Sh + 68) /\
         munch [(Sh, Sh + 392)] m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\ shadow_rw m' /\
         asan_cells m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81100) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sh E3 E4 E5 HSH HSW HRO HAC RSH.
  eapply evtF_mono;
    [exact (a3_evt_mid_pre_F_on RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              t3 t4 t5 t6 F fc m Sh E3 E4 E5 HSH (B.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSW) HRO HAC RSH)|].
  intros ms' (R & m' & Ems & G1 & G10 & G11 & G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G24 & G25 &
              G26 & G27 & MU & WM & RO & SW & AC).
  exists R, m'. do 21 (split; [assumption|]).
  split; [exact (B.ShadowRwOn.shadow_rw_of_on_all m' (SW _ (B.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSW)))|].
  exact AC.
Qed.

(* ---- a3_evt_mid, part 2: the return at 0x81220 is the run's end, so the post stretch takes no step; it is the
   bookkeeping the source does on the callee's post facts, stated over the post-call machine state. ---- *)
Lemma a3_evt_mid_post_F :
  forall (RNG : footprint) (R F : bvmap 5 word) (fc : bv 32) (m mf m' : word -> option byte)
         (sp gp tp s0 s1 s2 s6 s8 s9 s10 : word) (Sh : Z),
    (* what the run carries at the call *)
    munch [(Sh, Sh + 392)] m mf -> wmono rsegs m mf ->
    (* the callee post facts, over the post-call state *)
    munch [(Sh + 68, Sh + 68 + 187)] mf m' -> wmono rsegs mf m' -> ro_agree rsegs m' -> shadow_rw m' ->
    getr R 2 = sp -> getr R 3 = gp -> getr R 4 = tp -> getr R 8 = s0 -> getr R 9 = s1 ->
    getr R 18 = s2 -> getr R 19 = Z_to_bv 64 Sh -> getr R 20 = Z_to_bv 64 (-8) ->
    getr R 21 = Z_to_bv 64 (-14) -> getr R 22 = s6 -> getr R 24 = s8 -> getr R 25 = s9 ->
    getr R 26 = s10 -> getr R 27 = Z_to_bv 64 (Sh + 68) ->
    evtF rsegs RNG
      (fun ms' => exists (R' : bvmap 5 word) (m'' : word -> option byte),
         ms' = MS R' F (Z_to_bv 64 0x81220) fc None m'' (seg_rom rsegs) /\
         getr R' 2 = sp /\ getr R' 3 = gp /\ getr R' 4 = tp /\ getr R' 8 = s0 /\ getr R' 9 = s1 /\
         getr R' 18 = s2 /\ getr R' 19 = Z_to_bv 64 Sh /\ getr R' 20 = Z_to_bv 64 (-8) /\
         getr R' 21 = Z_to_bv 64 (-14) /\ getr R' 22 = s6 /\ getr R' 24 = s8 /\ getr R' 25 = s9 /\
         getr R' 26 = s10 /\ getr R' 27 = Z_to_bv 64 (Sh + 68) /\
         munch [(Sh, Sh + 392)] m m'' /\ wmono rsegs m m'' /\ ro_agree rsegs m'' /\ shadow_rw m'')
      (MS R F (Z_to_bv 64 0x81220) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG R F fc m mf m' sp gp tp s0 s1 s2 s6 s8 s9 s10 Sh
    MUc WMc MU' WM' RO' SW' G2 G3 G4 G8 G9 G18 G19 G20 G21 G22 G24 G25 G26 G27.
  apply evtF_done. exists R, m'.
  split; [reflexivity|].
  do 14 (split; [assumption|]).
  split.
  { eapply munch_trans; [exact MUc|].
    eapply (munch_weaken [(Sh + 68, Sh + 68 + 187)] [(Sh, Sh + 392)]); [| exact MU'].
    unfold sub_fp. cbn [outside]. intros x (Hx & _). split; [lia | exact I]. }
  split; [exact (wmono_trans rsegs m mf m' WMc WM')|].
  split; [exact RO' | exact SW'].
Qed.

(* ---- a3_evt, part 1: 0x810c4 (the spill of the frame base) to the callee entry 0x55144. ---- *)
(* The shadow bytes the run stores into: the 68 `sb r,k(s3)` of [S(fr), S(fr) + 68) (the `rng RNG (Sfr fr) 68` row).
   The spill word and the header words are application memory; the run reads no shadow byte. *)
Definition a3_evt_pre_F_shadow_R (fr : Z) : Z -> Prop := fun a => Sfr fr <= a < Sfr fr + 68.

Lemma a3_evt_pre_F_on :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A fr : Z),
    s1 = Z_to_bv 64 A -> s9 = Z_to_bv 64 fr -> s10 = Z_to_bv 64 ASAN_K ->
    AC.GT <= fr -> fr + 3136 <= A -> HIGHMEM_BEG <= A -> A + 344 <= 2 ^ 64 ->
    (fr + 3136 <= LOWMEM_END \/ HIGHMEM_BEG <= fr) ->
    (forall i, 0 <= i < 392 -> in_shadow (Sfr fr + i)) ->
    wr_at rsegs m fr 24 -> wr_at rsegs m (A + 336) 8 ->
    B.ShadowRwOn.shadow_rw_on (a3_evt_pre_F_shadow_R fr) m -> ro_agree rsegs m -> asan_cells m ->
    rng RNG (A + 336) 8 -> rng RNG fr 24 -> rng RNG (Sfr fr) 68 ->
    evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x55144) fc None m' (seg_rom rsegs) /\
         getr R 1 = Z_to_bv 64 0x81220 /\ getr R 10 = Z_to_bv 64 (Sfr fr + 68) /\
         getr R 11 = Z_to_bv 64 187 /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = Z_to_bv 64 (Sfr fr) /\ getr R 20 = Z_to_bv 64 (-8) /\
         getr R 21 = Z_to_bv 64 (-14) /\ getr R 22 = s6 /\ getr R 24 = s8 /\ getr R 25 = s9 /\
         getr R 26 = s10 /\ getr R 27 = Z_to_bv 64 (Sfr fr + 68) /\
         munch [(A + 336, A + 344); (fr, fr + 24); (Sfr fr, Sfr fr + 392)] m m' /\
         wmono rsegs m m' /\ ro_agree rsegs m' /\
         (forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m') /\ asan_cells m' /\
         q64 m' (A + 336) fr /\ q64 m' fr 0x41b58ab3 /\ q64 m' (fr + 8) 0x17e9c /\ q64 m' (fr + 16) AF.ENTRY)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x810c4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A fr -> -> -> HfrGT HfrA HAhi HA64 Hfrsep HSH HWh HWs HSR HRO HAC RSP RHD RSH.
  pose proof (HSH 0 ltac:(lia)) as Hin0. rewrite Z.add_0_r in Hin0.
  pose proof (HSH 391 ltac:(lia)) as Hin379.
  assert (HSlo : LOWMEM_END <= Sfr fr)
    by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin0 |- *; lia).
  assert (HShi : Sfr fr + 392 <= HIGHMEM_BEG)
    by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin379 |- *; lia).
  unfold LOWMEM_END in HSlo, Hfrsep. unfold HIGHMEM_BEG in HShi, HAhi, Hfrsep. unfold AC.GT in HfrGT.
  (* 0x810c4: sd s9,336(s1) -- the frame base spilled to [A + 336] *)
  assert (HS1 : store_ok rsegs m (wa (A + 336)) 8 = true)
    by (eapply (A3.a3_store_ok_at m (A + 336) 8 0 8%nat); [exact HWs | lia | cbn; lia | lia]).
  step.
  set (m1 := write_to_mem m (Z_to_bv 64 (A + 336)) (le8 (Z_to_bv 64 fr))) in *.
  assert (MU1 : munch [(A + 336, A + 344); (fr, fr + 24); (Sfr fr, Sfr fr + 392)] m m1).
  { unfold m1. apply munch_write;
      [apply munch_refl | lia | rewrite length_le8; lia | rewrite length_le8; cbn [inside]; left; lia]. }
  assert (WM1 : wmono rsegs m m1) by (unfold m1; apply wmono_write, wmono_refl).
  assert (RO1 : ro_agree rsegs m1)
    by (unfold m1; apply A3.a3_ro_write; [exact HRO | lia | rewrite length_le8; lia | unfold AC.GT; lia]).
  assert (RD1 : B.Prog.MemMono.rd_mono m m1)
    by (unfold m1; apply B.Prog.MemMono.rd_mono_write, B.Prog.MemMono.rd_mono_refl).
  assert (Q336 : q64 m1 (A + 336) fr)
    by (unfold q64, m1; apply bytes_at_write_same; [lia | rewrite length_le8; lia]).
  assert (HWh1 : wr_at rsegs m1 fr 24) by (unfold m1; apply wr_at_write; exact HWh).
  clearbody m1. clear HS1.
  (* the nine register instructions 0x810c8-0x810e8 *)
  do 9 step.
  (* 0x810ec: sd a0,0(s9) -- the sink head word *)
  assert (HS2 : store_ok rsegs m1 (wa fr) 8 = true)
    by (eapply (A3.a3_store_ok_at m1 fr 24 0 8%nat); [exact HWh1 | lia | cbn; lia | lia]).
  step.
  set (m2 := write_to_mem m1 (Z_to_bv 64 fr) (le8 (Z_to_bv 64 1102416563))) in *.
  assert (MU2 : munch [(A + 336, A + 344); (fr, fr + 24); (Sfr fr, Sfr fr + 392)] m m2).
  { unfold m2. apply munch_write;
      [exact MU1 | lia | rewrite length_le8; lia | rewrite length_le8; cbn [inside]; right; left; lia]. }
  assert (WM2 : wmono rsegs m m2) by (unfold m2; apply wmono_write, WM1).
  assert (RO2 : ro_agree rsegs m2)
    by (unfold m2; apply A3.a3_ro_write; [exact RO1 | lia | rewrite length_le8; lia | unfold AC.GT; lia]).
  assert (RD2 : B.Prog.MemMono.rd_mono m m2) by (unfold m2; apply B.Prog.MemMono.rd_mono_write, RD1).
  assert (Q336b : q64 m2 (A + 336) fr).
  { unfold q64, m2. apply bytes_at_write_other;
      [exact Q336 | lia | rewrite length_le8; lia | rewrite !length_le8; lia]. }
  assert (Qh0 : q64 m2 fr 0x41b58ab3)
    by (unfold q64, m2; apply bytes_at_write_same; [lia | rewrite length_le8; lia]).
  assert (HWh2 : wr_at rsegs m2 fr 24) by (unfold m2; apply wr_at_write; exact HWh1).
  clearbody m2. clear HS2.
  (* 0x810f0: sd a1,8(s9) -- the description word *)
  assert (HS3 : store_ok rsegs m2 (wa (fr + 8)) 8 = true)
    by (eapply (A3.a3_store_ok_at m2 fr 24 8 8%nat); [exact HWh2 | lia | cbn; lia | lia]).
  step.
  set (m3 := write_to_mem m2 (Z_to_bv 64 (fr + 8)) (le8 (Z_to_bv 64 97948))) in *.
  assert (MU3 : munch [(A + 336, A + 344); (fr, fr + 24); (Sfr fr, Sfr fr + 392)] m m3).
  { unfold m3. apply munch_write;
      [exact MU2 | lia | rewrite length_le8; lia | rewrite length_le8; cbn [inside]; right; left; lia]. }
  assert (WM3 : wmono rsegs m m3) by (unfold m3; apply wmono_write, WM2).
  assert (RO3 : ro_agree rsegs m3)
    by (unfold m3; apply A3.a3_ro_write; [exact RO2 | lia | rewrite length_le8; lia | unfold AC.GT; lia]).
  assert (RD3 : B.Prog.MemMono.rd_mono m m3) by (unfold m3; apply B.Prog.MemMono.rd_mono_write, RD2).
  assert (Q336c : q64 m3 (A + 336) fr).
  { unfold q64, m3. apply bytes_at_write_other;
      [exact Q336b | lia | rewrite length_le8; lia | rewrite !length_le8; lia]. }
  assert (Qh0b : q64 m3 fr 0x41b58ab3).
  { unfold q64, m3. apply bytes_at_write_other;
      [exact Qh0 | lia | rewrite length_le8; lia | rewrite !length_le8; lia]. }
  assert (Qh8 : q64 m3 (fr + 8) 0x17e9c)
    by (unfold q64, m3; apply bytes_at_write_same; [lia | rewrite length_le8; lia]).
  assert (HWh3 : wr_at rsegs m3 fr 24) by (unfold m3; apply wr_at_write; exact HWh2).
  clearbody m3. clear HS3.
  (* 0x810f4: sd a2,16(s9) -- the entry word *)
  assert (HS4 : store_ok rsegs m3 (wa (fr + 16)) 8 = true)
    by (eapply (A3.a3_store_ok_at m3 fr 24 16 8%nat); [exact HWh3 | lia | cbn; lia | lia]).
  step.
  set (m4 := write_to_mem m3 (Z_to_bv 64 (fr + 16)) (le8 (Z_to_bv 64 528408))) in *.
  assert (MU4 : munch [(A + 336, A + 344); (fr, fr + 24); (Sfr fr, Sfr fr + 392)] m m4).
  { unfold m4. apply munch_write;
      [exact MU3 | lia | rewrite length_le8; lia | rewrite length_le8; cbn [inside]; right; left; lia]. }
  assert (WM4 : wmono rsegs m m4) by (unfold m4; apply wmono_write, WM3).
  assert (RO4 : ro_agree rsegs m4)
    by (unfold m4; apply A3.a3_ro_write; [exact RO3 | lia | rewrite length_le8; lia | unfold AC.GT; lia]).
  assert (RD4 : B.Prog.MemMono.rd_mono m m4) by (unfold m4; apply B.Prog.MemMono.rd_mono_write, RD3).
  assert (Q336d : q64 m4 (A + 336) fr).
  { unfold q64, m4. apply bytes_at_write_other;
      [exact Q336c | lia | rewrite length_le8; lia | rewrite !length_le8; lia]. }
  assert (Qh0c : q64 m4 fr 0x41b58ab3).
  { unfold q64, m4. apply bytes_at_write_other;
      [exact Qh0b | lia | rewrite length_le8; lia | rewrite !length_le8; lia]. }
  assert (Qh8b : q64 m4 (fr + 8) 0x17e9c).
  { unfold q64, m4. apply bytes_at_write_other;
      [exact Qh8 | lia | rewrite length_le8; lia | rewrite !length_le8; lia]. }
  assert (Qh16 : q64 m4 (fr + 16) AF.ENTRY)
    by (unfold q64, m4, AF.ENTRY; apply bytes_at_write_same; [lia | rewrite length_le8; lia]).
  assert (AC4 : asan_cells m4).
  { apply (A3.a3_asan_keep [(A + 336, A + 344); (fr, fr + 24); (Sfr fr, Sfr fr + 392)] m m4 HAC MU4).
    intros x Hx. cbn [outside]. unfold AC.GT in Hx.
    split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  clearbody m4. clear HS4.
  (* 0x810f8: li a0,-15 ; 0x810fc: add s3,s3,s10 (s3 = S(fr)) *)
  step. step.
  eapply evtF_cut.
  - eapply (a3_evt_mid_pre_F_on RNG) with (Sh := Sfr fr).
    + rewrite !MState.unsigned_lit by (try unfold ASAN_K; lia).
      rewrite Z.shiftr_div_pow2 by lia. unfold Sfr, shadow_addr. reflexivity.
    + reflexivity.
    + reflexivity.
    + exact HSH.
    + exact (B.ShadowRwOnT.shadow_rw_on_mem_mono (a3_evt_pre_F_shadow_R fr) m m4 HSR WM4 RD4).
    + exact RO4.
    + exact AC4.
    + exact RSH.
  - intros ms' (R & m' & Ems & G1 & G10 & G11 & G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G24 &
                G25 & G26 & G27 & MUm & WMm & ROm & SWm & ACm).
    apply evtF_done.
    assert (MUw : munch [(A + 336, A + 344); (fr, fr + 24); (Sfr fr, Sfr fr + 392)] m4 m').
    { eapply (munch_weaken [(Sfr fr, Sfr fr + 392)]); [| exact MUm].
      unfold sub_fp. cbn [outside]. intros x (_ & _ & Hx & _). split; [exact Hx | exact I]. }
    exists R, m'.
    split; [exact Ems|].
    split; [exact G1|]. split; [exact G10|]. split; [exact G11|].
    split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G8|]. split; [exact G9|].
    split; [exact G18|]. split; [exact G19|]. split; [exact G20|]. split; [exact G21|]. split; [exact G22|].
    split; [exact G24|]. split; [exact G25|]. split; [exact G26|]. split; [exact G27|].
    split; [exact (munch_trans _ m m4 m' MU4 MUw)|].
    split; [exact (wmono_trans rsegs m m4 m' WM4 WMm)|].
    split; [exact ROm|].
    split; [intros P HP; exact (SWm P (B.ShadowRwOnT.shadow_rw_on_mem_mono P m m4 HP WM4 RD4))|].
    split; [exact ACm|].
    split.
    { unfold q64 in Q336d |- *.
      eapply (fl_bytes [(Sfr fr, Sfr fr + 392)] m4 m'); [exact Q336d | exact MUm|].
      rewrite length_le8. intros x Hx. split; [lia | exact I]. }
    split.
    { unfold q64 in Qh0c |- *.
      eapply (fl_bytes [(Sfr fr, Sfr fr + 392)] m4 m'); [exact Qh0c | exact MUm|].
      rewrite length_le8. intros x Hx. split; [lia | exact I]. }
    split.
    { unfold q64 in Qh8b |- *.
      eapply (fl_bytes [(Sfr fr, Sfr fr + 392)] m4 m'); [exact Qh8b | exact MUm|].
      rewrite length_le8. intros x Hx. split; [lia | exact I]. }
    { unfold q64 in Qh16 |- *.
      eapply (fl_bytes [(Sfr fr, Sfr fr + 392)] m4 m'); [exact Qh16 | exact MUm|].
      rewrite length_le8. intros x Hx. split; [unfold AF.ENTRY in Hx; lia | exact I]. }
Qed.

(* The old statement, from the narrowed one (B.ShadowRwOn.shadow_rw_on_of_shadow_rw; the post at P := fun _ => True,
   B.ShadowRwOn.shadow_rw_of_on_all). *)
Lemma a3_evt_pre_F :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A fr : Z),
    s1 = Z_to_bv 64 A -> s9 = Z_to_bv 64 fr -> s10 = Z_to_bv 64 ASAN_K ->
    AC.GT <= fr -> fr + 3136 <= A -> HIGHMEM_BEG <= A -> A + 344 <= 2 ^ 64 ->
    (fr + 3136 <= LOWMEM_END \/ HIGHMEM_BEG <= fr) ->
    (forall i, 0 <= i < 392 -> in_shadow (Sfr fr + i)) ->
    wr_at rsegs m fr 24 -> wr_at rsegs m (A + 336) 8 ->
    shadow_rw m -> ro_agree rsegs m -> asan_cells m ->
    rng RNG (A + 336) 8 -> rng RNG fr 24 -> rng RNG (Sfr fr) 68 ->
    evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x55144) fc None m' (seg_rom rsegs) /\
         getr R 1 = Z_to_bv 64 0x81220 /\ getr R 10 = Z_to_bv 64 (Sfr fr + 68) /\
         getr R 11 = Z_to_bv 64 187 /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = Z_to_bv 64 (Sfr fr) /\ getr R 20 = Z_to_bv 64 (-8) /\
         getr R 21 = Z_to_bv 64 (-14) /\ getr R 22 = s6 /\ getr R 24 = s8 /\ getr R 25 = s9 /\
         getr R 26 = s10 /\ getr R 27 = Z_to_bv 64 (Sfr fr + 68) /\
         munch [(A + 336, A + 344); (fr, fr + 24); (Sfr fr, Sfr fr + 392)] m m' /\
         wmono rsegs m m' /\ ro_agree rsegs m' /\ shadow_rw m' /\ asan_cells m' /\
         q64 m' (A + 336) fr /\ q64 m' fr 0x41b58ab3 /\ q64 m' (fr + 8) 0x17e9c /\ q64 m' (fr + 16) AF.ENTRY)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x810c4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A fr E1 E9 E10 HfrGT HfrA HAhi HA64 Hfrsep HSH HWh HWs HSW HRO HAC RSP RHD RSH.
  eapply evtF_mono;
    [exact (a3_evt_pre_F_on RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              t3 t4 t5 t6 F fc m A fr E1 E9 E10 HfrGT HfrA HAhi HA64 Hfrsep HSH HWh HWs
              (B.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSW) HRO HAC RSP RHD RSH)|].
  intros ms' (R & m' & Ems & G1 & G10 & G11 & G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G24 & G25 &
              G26 & G27 & MU & WM & RO & SW & AC & Q1 & Q2 & Q3 & Q4).
  exists R, m'. do 21 (split; [assumption|]).
  split; [exact (B.ShadowRwOn.shadow_rw_of_on_all m' (SW _ (B.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSW)))|].
  do 4 (split; [assumption|]). exact Q4.
Qed.

(* ---- a3_evt, part 2: the post stretch of the whole segment run; the return pc 0x81220 is the run's end. ---- *)
Lemma a3_evt_post_F :
  forall (RNG : footprint) (R F : bvmap 5 word) (fc : bv 32) (m mf m' : word -> option byte)
         (sp gp tp s0 s1 s2 s6 s8 s9 s10 : word) (A fr : Z),
    (* the geometry the run carries (A3.v:428-437: the frame, the spill word and the frame shadow are apart) *)
    AC.GT <= fr -> fr + 3136 <= A -> HIGHMEM_BEG <= A -> A + 344 <= 2 ^ 64 ->
    (fr + 3136 <= LOWMEM_END \/ HIGHMEM_BEG <= fr) ->
    (forall i, 0 <= i < 392 -> in_shadow (Sfr fr + i)) ->
    (* what the run carries at the call *)
    munch [(A + 336, A + 344); (fr, fr + 24); (Sfr fr, Sfr fr + 392)] m mf -> wmono rsegs m mf ->
    q64 mf (A + 336) fr -> q64 mf fr 0x41b58ab3 -> q64 mf (fr + 8) 0x17e9c -> q64 mf (fr + 16) AF.ENTRY ->
    (* the callee post facts, over the post-call state *)
    munch [(Sfr fr + 68, Sfr fr + 68 + 187)] mf m' -> wmono rsegs mf m' -> ro_agree rsegs m' -> shadow_rw m' ->
    getr R 2 = sp -> getr R 3 = gp -> getr R 4 = tp -> getr R 8 = s0 -> getr R 9 = s1 ->
    getr R 18 = s2 -> getr R 19 = Z_to_bv 64 (Sfr fr) -> getr R 20 = Z_to_bv 64 (-8) ->
    getr R 21 = Z_to_bv 64 (-14) -> getr R 22 = s6 -> getr R 24 = s8 -> getr R 25 = s9 ->
    getr R 26 = s10 -> getr R 27 = Z_to_bv 64 (Sfr fr + 68) ->
    evtF rsegs RNG
      (fun ms' => exists (R' : bvmap 5 word) (m'' : word -> option byte),
         ms' = MS R' F (Z_to_bv 64 0x81220) fc None m'' (seg_rom rsegs) /\
         getr R' 2 = sp /\ getr R' 3 = gp /\ getr R' 4 = tp /\ getr R' 8 = s0 /\ getr R' 9 = s1 /\
         getr R' 18 = s2 /\ getr R' 19 = Z_to_bv 64 (Sfr fr) /\ getr R' 20 = Z_to_bv 64 (-8) /\
         getr R' 21 = Z_to_bv 64 (-14) /\ getr R' 22 = s6 /\ getr R' 24 = s8 /\ getr R' 25 = s9 /\
         getr R' 26 = s10 /\ getr R' 27 = Z_to_bv 64 (Sfr fr + 68) /\
         munch [(A + 336, A + 344); (fr, fr + 24); (Sfr fr, Sfr fr + 392)] m m'' /\
         wmono rsegs m m'' /\ ro_agree rsegs m'' /\ shadow_rw m'' /\
         q64 m'' (A + 336) fr /\ q64 m'' fr 0x41b58ab3 /\ q64 m'' (fr + 8) 0x17e9c /\ q64 m'' (fr + 16) AF.ENTRY)
      (MS R F (Z_to_bv 64 0x81220) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG R F fc m mf m' sp gp tp s0 s1 s2 s6 s8 s9 s10 A fr
    HfrGT HfrA HAhi HA64 Hfrsep HSH
    MU4 WM4 Q336d Qh0c Qh8b Qh16 MUm WMm ROm SWm G2 G3 G4 G8 G9 G18 G19 G20 G21 G22 G24 G25 G26 G27.
  pose proof (HSH 0 ltac:(lia)) as Hin0. rewrite Z.add_0_r in Hin0.
  pose proof (HSH 391 ltac:(lia)) as Hin379.
  assert (HSlo : LOWMEM_END <= Sfr fr)
    by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin0 |- *; lia).
  assert (HShi : Sfr fr + 392 <= HIGHMEM_BEG)
    by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin379 |- *; lia).
  unfold LOWMEM_END in HSlo, Hfrsep. unfold HIGHMEM_BEG in HShi, HAhi, Hfrsep. unfold AC.GT in HfrGT.
  apply evtF_done. exists R, m'.
  split; [reflexivity|].
  do 14 (split; [assumption|]).
  assert (MUw : munch [(A + 336, A + 344); (fr, fr + 24); (Sfr fr, Sfr fr + 392)] mf m').
  { eapply (munch_weaken [(Sfr fr + 68, Sfr fr + 68 + 187)]); [| exact MUm].
    unfold sub_fp. cbn [outside]. intros x (_ & _ & Hx & _). split; [lia | exact I]. }
  split; [exact (munch_trans _ m mf m' MU4 MUw)|].
  split; [exact (wmono_trans rsegs m mf m' WM4 WMm)|].
  split; [exact ROm|].
  split; [exact SWm|].
  split.
  { unfold q64 in Q336d |- *.
    eapply (fl_bytes [(Sfr fr + 68, Sfr fr + 68 + 187)] mf m'); [exact Q336d | exact MUm|].
    rewrite length_le8. intros x Hx. split; [lia | exact I]. }
  split.
  { unfold q64 in Qh0c |- *.
    eapply (fl_bytes [(Sfr fr + 68, Sfr fr + 68 + 187)] mf m'); [exact Qh0c | exact MUm|].
    rewrite length_le8. intros x Hx. split; [lia | exact I]. }
  split.
  { unfold q64 in Qh8b |- *.
    eapply (fl_bytes [(Sfr fr + 68, Sfr fr + 68 + 187)] mf m'); [exact Qh8b | exact MUm|].
    rewrite length_le8. intros x Hx. split; [lia | exact I]. }
  { unfold q64 in Qh16 |- *.
    eapply (fl_bytes [(Sfr fr + 68, Sfr fr + 68 + 187)] mf m'); [exact Qh16 | exact MUm|].
    rewrite length_le8. intros x Hx. split; [unfold AF.ENTRY in Hx; lia | exact I]. }
Qed.
