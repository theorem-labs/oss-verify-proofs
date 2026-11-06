(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module names changed; 85 of its 151 lines of code are new or changed and 3787 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match_lib.v, with its module paths and module names changed; 717 of its 758 lines of code are new or changed and 110 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F31.v, with its module names and numbers changed; 139 of its 189 lines of code are new or changed and 708 lines of the source are left out. *)
(* Segment F33 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): 0x8285c-0x82868, the head of row_of_block
   (plan-asan section 2 row F33; ubsan twin W01).
   rule 24: no function proved.
   v1.9 STATUS (2026-10-28): UNVERIFIED.  No build without probes has checked this file on v1.9.0.  It closed only
   in an ITERATION-ONLY build on the v1.9 bytes (FACTS 0bfe9aa0d452) with lib/A/Tk/AW/SmLeaf.v's walks admitted.
   It waits for lib/A/Tk/AW Sm* on v1.9 and for Seg/Tac_slot.v / Tac_fsfree.v re-fit to the regenerated Contract.v
   and FrameAPI.v.

     0x8285c  beqz a0,828bc   -- NOT taken: a0 = BOX_CATALOGUE = 0x9e800, the catalogue's result (F32).
     0x82860  ld s8,0(s8)     -- s8 = fr + 32 (the count variable); the catalogue wrote 11 there (F32), so s8 = 11.
     0x82864  beqz s8,828bc   -- NOT taken: s8 = 11.
     0x82868  mv s4,a0        -- s4 = BOX_CATALOGUE, the row pointer of row 0.

   Cuts: all three are SlotInv.v's official bodies (push 6c, kept through push 14E, v1.9 names and pcs of
   a working branch 0a1d413d7c3).  The entry Inv_A8285c_at is
   F32's exit term for term: the frame-loop skeleton written out (exists phi, CUTST g 0x8285c (hb1 phi
   (AC.a_size (flen g j))) with FLSI) with LK, the pass-through bundle FLSX, t_rowsel = true, the
   catalogue's result a0 / s8 / count word and the hand-on bundle LT.  The exit Inv_A8286c_at (the row loop head
   W00, row i = 0) carries RL (its rows-left / row-pointer registers and its own FLSX) and LT; the exit
   Inv_A828bc_at (the target of both branches) is not reached here.  No memory is written, so FRA moves by
   Tac_slot's sl_fra_move, ENT by ent_mat, and FLSI / FLSX / LK / LT by register equalities alone (registers 9,
   18, 21, 22, 23 and 25 are not written). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm
  AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcParse.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_box_catalogue_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5.
Import ListNotations.
(* The plain lib/Prog files also load lib/Reusable/YK11, so the short name YK11 may be the plain one here; the
   slot's cuts are stated with the image-A one, which this alias names. *)
Module AYK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Import AYK.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module CATc := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_catalogue_c.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* ========================= byte / engine helpers (F32's, renamed) ========================= *)

Lemma f33_rd8 : forall m a bs, bytes_at rsegs m a bs -> length bs = 8%nat ->
  ov_read_bytes rsegs m (wa a) 8 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (bytes_at_ov_read rsegs m a bs 0 8 H ltac:(lia)) as HH.
  cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by lia. exact HH.
Qed.

Lemma f33_eqb_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

(* A branch arm the facts in context exclude. *)
Ltac f33_bad HC :=
  exfalso;
  first [ congruence
        | discriminate HC
        | (rewrite ?f33_eqb_lit in HC by lia; apply Z.eqb_eq in HC; lia)
        | (vm_compute in HC; discriminate HC) ].
Ltac f33_nt := let H := fresh "HC" in first [ if_cases H; [f33_bad H | clear H] | idtac ].

(* ========================= the official bundles across a register change ========================= *)

(* FLSI / FLSX / LK / LT read registers 9 (the spill base s1), 18, 21, 22, 23 and 25 only; the run below writes
   none of them and no memory (F32's f32_*_regs, renamed). *)
Lemma f33_spill_regs : forall regs regs' m off v,
  getr regs' 9 = getr regs 9 -> spill regs m off v -> spill regs' m off v.
Proof.
  intros regs regs' m off v E (A & HA & Hq). exists A. split; [unfold rg in *; rewrite E; exact HA | exact Hq].
Qed.

(* Push 14E: FLSI = FLSH (PRO with its four new spills 184 / 256 / 264 / 272 at the end) /\ spills 216 / 224 /
   248 /\ f1_IN /\ FLC (ten spills and two addressable ranges); every spill moves by register 9, the rest is
   memory only.  v1.9: PRO's [A + 200] is [A + 208] and PRO gains [A + 32] = fr + 2880 as its 16th conjunct; FLC's
   slots are renumbered (208 / 64 / 72 / 80 / 56 / 48 -> 192 / 80 / 88 / 96 / 72 / 64) and FLC gains
   [A + 56] = fr + 2889 and [A + 48] = fr + 2890 as its 13th and 14th; both additions are at the end. *)
Lemma f33_flsi_regs : forall g j fr regs regs' m,
  getr regs' 9 = getr regs 9 -> FLSI g j fr regs m -> FLSI g j fr regs' m.
Proof.
  intros g j fr regs regs' m E
    (((P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Ha & Hb & Hin & P184 & P256 & P264 & P272 &
       P32) &
      S128 & Hs & S144 & Ha17) &
     S216 & S224 & S248 & HIN &
     (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & Cfr & Crec & C72 & C64 & C56 & C48)).
  pose proof (f33_spill_regs regs regs' m) as T. unfold FLSI, FLSH, PRO, FLC.
  split.
  { split.
    { split; [exact (T _ _ E P40)|]. split; [exact (T _ _ E P120)|]. split; [exact (T _ _ E P136)|].
      split; [exact (T _ _ E P160)|]. split; [exact (T _ _ E P168)|]. split; [exact (T _ _ E P176)|].
      split; [exact (T _ _ E P208)|]. split; [exact (T _ _ E P248)|].
      split; [exact Ha|]. split; [exact Hb|]. split; [exact Hin|].
      split; [exact (T _ _ E P184)|]. split; [exact (T _ _ E P256)|].
      split; [exact (T _ _ E P264)|]. split; [exact (T _ _ E P272) | exact (T _ _ E P32)]. }
    split; [exact (T _ _ E S128)|]. split; [exact Hs|].
    split; [exact (T _ _ E S144) | exact Ha17]. }
  split; [exact (T _ _ E S216)|]. split; [exact (T _ _ E S224)|]. split; [exact (T _ _ E S248)|].
  split; [exact HIN|].
  split; [exact (T _ _ E C256)|]. split; [exact (T _ _ E C184)|]. split; [exact (T _ _ E C192)|].
  split; [exact (T _ _ E C80)|]. split; [exact (T _ _ E C88)|]. split; [exact (T _ _ E C96)|].
  split; [exact (T _ _ E C272)|]. split; [exact (T _ _ E C264)|].
  split; [exact Cfr|]. split; [exact Crec|].
  split; [exact (T _ _ E C72)|]. split; [exact (T _ _ E C64)|].
  split; [exact (T _ _ E C56) | exact (T _ _ E C48)].
Qed.

Lemma f33_lk_regs : forall g fr j regs regs' m,
  getr regs' 21 = getr regs 21 -> LK g fr j regs m -> LK g fr j regs' m.
Proof.
  intros g fr j regs regs' m E (Hj & H21 & HO). split; [exact Hj|].
  split; [unfold rg in *; rewrite E; exact H21 | exact HO].
Qed.

Lemma f33_flsx_regs : forall g j phi fr regs regs' m,
  getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 -> getr regs' 22 = getr regs 22 ->
  getr regs' 23 = getr regs 23 -> getr regs' 25 = getr regs 25 ->
  FLSX g j phi fr regs m -> FLSX g j phi fr regs' m.
Proof.
  intros g j phi fr regs regs' m E9 E18 E22 E23 E25 (HI & H18 & H22 & H23 & H25 & Hrec & H152 & H280).
  unfold FLSX.
  split; [exact (f33_flsi_regs g j fr regs regs' m E9 HI)|].
  split; [unfold rg in *; rewrite E18; exact H18|]. split; [unfold rg in *; rewrite E22; exact H22|].
  split; [unfold rg in *; rewrite E23; exact H23|]. split; [unfold rg in *; rewrite E25; exact H25|].
  split; [exact Hrec|].
  split; [exact (f33_spill_regs regs regs' m _ _ E9 H152) | exact (f33_spill_regs regs regs' m _ _ E9 H280)].
Qed.

(* v1.9: FSb takes fr; its positions 3 / 4 are the body bytes at fr + 2880 and their addressability, memory only. *)
Lemma f33_lt_regs : forall g fr j regs regs' m,
  getr regs' 9 = getr regs 9 -> LT g fr j regs m -> LT g fr j regs' m.
Proof.
  intros g fr j regs regs' m E (HID & HFG & (Q104 & Q112 & Qbody & Qad & HFI)).
  pose proof (f33_spill_regs regs regs' m) as T. unfold LT, IFS, FSj, FSb.
  split; [exact HID|]. split; [exact HFG|].
  split; [exact (T _ _ E Q104)|]. split; [exact (T _ _ E Q112)|].
  split; [exact Qbody|]. split; [exact Qad | exact HFI].
Qed.

(* ========================= the machine run ========================= *)

(* 0x8285c -> 0x8286c with a0 <> 0 and the 8 bytes at s8 = c holding 11: both branches to 0x828bc fall through,
   s8 = 11 and s4 = a0. *)
Lemma f33_evt :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte) (T c : Z),
    x10 = Z_to_bv 64 T -> 0 < T < 2 ^ 64 ->
    x24 = Z_to_bv 64 c ->
    ov_read_bytes rsegs m (wa c) 8 = Some (le8 (Z_to_bv 64 11)) ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 T) x11 x12 x13 x14 x15 x16 x17 x18 x19
                              (Z_to_bv 64 T) x21 x22 x23 (Z_to_bv 64 11) x25 x26 x27 x28 x29 x30 x31)
                           Fr (Z_to_bv 64 0x8286c) fcs None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x8285c) fcs None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m T c E10 HT E24 RD.
  subst x10 x24.
  (* 0x8285c beqz a0,828bc: not taken *)
  step. f33_nt.
  (* 0x82860 ld s8,0(s8) = 11; 0x82864 beqz s8,828bc: not taken *)
  step. step. f33_nt.
  (* 0x82868 mv s4,a0 *)
  step. apply evt_done. reflexivity.
Qed.

Section F33.
Context {fx : AYK.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* ===================== the segment lemma ===================== *)

(* Entry Inv_A8285c_at j; exits Inv_A8286c_at j 0 (the row loop head at row 0) and Inv_A828bc_at j (the target of
   `beqz a0` at 0x8285c and `beqz s8` at 0x82864, not taken here). *)
Lemma seg_F33 : forall j,
  Hat2 B APIf ra (Inv_A8286c_at B APIf ra) j 0%nat -> Hat B APIf ra (Inv_A828bc_at B APIf ra) j ->
  Hat B APIf ra (Inv_A8285c_at B APIf ra) j.
Proof.
  intros j H7c0 _ g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI &
    HLK & HFLSX & Hsel & H10 & H24 & Hcnt & HLT).
  subst c. rewrite SEGS.
  pose proof HFRA as (_ & _ & _ & _ & _ & _ & _ & Hhalt & _).
  assert (RDc : ov_read_bytes rsegs mem (wa (fr + 32)) 8 = Some (le8 (Z_to_bv 64 11)))
    by (apply f33_rd8; [exact Hcnt | apply length_le8]).
  apply (@sl_run_lib fx regs (Z_to_bv 64 0x8285c) mem md
    (fun R0 pc' mem' => pc' = Z_to_bv 64 0x8286c /\ mem' = mem /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 19 = getr regs 19 /\ getr R0 21 = getr regs 21 /\ getr R0 22 = getr regs 22 /\
       getr R0 23 = getr regs 23 /\ getr R0 25 = getr regs 25 /\ getr R0 26 = getr regs 26 /\
       getr R0 20 = Z_to_bv 64 CATc.BOX_CATALOGUE /\ getr R0 24 = Z_to_bv 64 11)
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply LE.evt_mono.
    { unfold Regs6ss.mkR_of. apply f33_evt with (T := CATc.BOX_CATALOGUE) (c := fr + 32).
      - unfold rg in H10. exact H10.
      - unfold CATc.BOX_CATALOGUE. lia.
      - unfold rg in H24. exact H24.
      - exact RDc. }
    { intros ms' E. eexists _, _, _. split; [exact E|].
      split; [reflexivity|]. split; [reflexivity|]. repeat split; reflexivity. }
  - intros R0 pc' mem' regs' md'
      (Hpc & Hmem & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E21 & E22 & E23 & E25 & E26 & E20 & E24) Hreg Hmat.
    subst pc' mem'.
    assert (HIexit : Inv_A8286c_at B APIf ra g j 0%nat
                       (mkCfg (mkst regs' (Z_to_bv 64 0x8286c) mem (seg_rom rsegs)) md')).
    { exists phi, regs', mem, md', fr. rewrite SEGS. split; [reflexivity|].
      split.
      { apply (sl_fra_move B APIf ra g fr _ regs regs' mem md md' HFRA);
          [ rewrite Hreg; exact E2 | rewrite Hreg; exact E3 | rewrite Hreg; exact E4
          | rewrite Hreg; exact E8 | rewrite Hreg; exact E9 | rewrite Hreg; exact E19
          | rewrite Hreg; exact E26 | exact Hmat ]. }
      split; [exact (ent_mat APIf g _ mem md md' HENT Hmat)|].
      split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB|].
      split; [apply (f33_flsi_regs g j fr regs); [rewrite Hreg; exact E9 | exact HFLSI]|].
      split; [apply (f33_lk_regs g fr j regs); [rewrite Hreg; exact E21 | exact HLK]|].
      split; [lia|].
      split.
      { (* RL at row 0: s4 = the catalogue, s8 = 11 rows left, no row before row 0 *)
        split; [lia|].
        split.
        { unfold rg. rewrite Hreg, E20.
          first [ reflexivity | (f_equal; unfold CATc.BOX_CATALOGUE, CAT, CAT_ROW; lia) ]. }
        split.
        { unfold rg. rewrite Hreg, E24.
          first [ reflexivity | (f_equal; unfold CAT_N; lia) ]. }
        split; [intros i' Hi'; lia|].
        split; [exact Hsel|].
        apply (f33_flsx_regs g j phi fr regs); try (rewrite Hreg; assumption); exact HFLSX. }
      apply (f33_lt_regs g fr j regs); [rewrite Hreg; exact E9 | exact HLT]. }
    pose proof (H7c0 g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

End F33.
(* b8refit: applied map b8refit-v190.tsv sha256=7153b913f625df27 kinds=frame,pc,slot. Do not apply it again. *)
