(* Segment A03 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13288, 0x1329c] and [0x13e10, 0x13e14],
   K13288 -> K132a0 (n >= 7, mode odd) or K13598 (n = 6 with c0 = 6, or n >= 7 with mode even, c0 = 7). *)
(* libreac v1.9.0 (internal path, sha256 9e0909d16182...), on the v1.9 cut bundle
   lib/Prog/SlotInv.v. rule 24: no function proved. The plain segment table
   (v190-segment-table-plain.md (a working note, not in this delivery)) has S_A03 CHANGED with kinds branch-target,
   new-call, new-insert, register; the memset of `first` (NEW 0x13598 .. 0x135a4) and the TARGET kind of
   0x1329c / 0x13e14 are not on this segment: SlotInv.v keeps K13598 at 0x13598, which both branches reach, so the
   memset is in S_P01. What remains: the register renaming s7 -> s11 (0x13290 `addi s11,s11,-2`, 0x13e10 `li
   s11,0`; the left count of CUR) and the n = 6 stub moved 0x13ddc / 0x13de0 -> 0x13e10 / 0x13e14 (0x13288 `beqz
   a1,0x13e10`); `our` sp+60 -> sp+76 only through OURb. Statements: seg_A03 unchanged; a03_evt6 / a03_evt7 take
   and return the left count in s11 (was s7). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel RcIdentLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b1 Tac_b4.
Import ListNotations.
Open Scope Z_scope.

Lemma a03_ne0 : forall x, 0 < x < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = false.
Proof.
  intros x Hx. unfold bv_eqb. rewrite !MState.unsigned_lit by lia. apply Z.eqb_neq. lia.
Qed.

(* beqz of (b & 1): taken exactly when b is even. *)
Lemma a03_par : forall b : byte,
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (zxb b)) 1)) (Z_to_bv 64 0) = negb (Z.odd (bv_unsigned b)).
Proof.
  intros b. rewrite RcIdentLib.zxb_u. pose proof (b4_byte_nn b) as Hb.
  change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. change (2 ^ 1) with 2.
  rewrite Zmod_odd. unfold bv_eqb.
  destruct (Z.odd (bv_unsigned b)); rewrite !MState.unsigned_lit by lia; reflexivity.
Qed.

Ltac a03_w := first [ reflexivity
                    | (rewrite ?MState.unsigned_lit by lia; f_equal; lia)
                    | (apply bv_eq; rewrite ?MState.unsigned_lit by lia; lia) ].

(* n = 6: beqz a1 -> 0x13e10: s11 = 0; j 0x13598. *)
Lemma a03_evt6 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a1 = Z_to_bv 64 0 ->
    evt rsegs
      (fun ms' => exists s11' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11'
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13598) fc None m (seg_rom rsegs) /\ s11' = Z_to_bv 64 0)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13288) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ->.
  step. if_true. step. step.
  apply evt_done. eexists. split; [reflexivity|]. a03_w.
Qed.

(* n >= 7: s0 = in[6] (lbu 1(a2), a2 = p + 5), s11 = n - 7, s5 = p + 7; beqz (s0 & 1) -> 0x13598, else 0x132a0. *)
Lemma a03_evt7 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (x q y : Z) (b : byte),
    a1 = Z_to_bv 64 x -> a2 = Z_to_bv 64 q -> s11 = Z_to_bv 64 y ->
    0 < x < 2 ^ 64 -> 0 <= q -> q + 2 < 2 ^ 64 -> 2 <= y < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (q + 1)) 1 = Some [b] ->
    evt rsegs
      (fun ms' => exists s0' a0' s5' s11' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0' s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5' s6 s7 s8 s9 s10 s11'
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 (if Z.odd (bv_unsigned b) then 0x132a0 else 0x13598)) fc None m (seg_rom rsegs) /\
         s0' = zxb b /\ s5' = Z_to_bv 64 (q + 2) /\ s11' = Z_to_bv 64 (y - 2))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13288) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m x q y b -> -> -> Hx Hq0 Hq1 Hy HR.
  step. if_false_by (a03_ne0 x Hx).
  step. step. step. step. step.
  destruct (Z.odd (bv_unsigned b)) eqn:Eo.
  - if_false_by (eq_trans (a03_par b) (f_equal negb Eo)).
    apply evt_done. do 4 eexists. split; [reflexivity|].
    split; [a03_w|]. split; a03_w.
  - if_true_by (eq_trans (a03_par b) (f_equal negb Eo)).
    apply evt_done. do 4 eexists. split; [reflexivity|].
    split; [a03_w|]. split; a03_w.
Qed.

Section A03.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_A03 : Hcut B APIf ra (Inv_K132a0 B APIf ra empty) -> Hcut B APIf ra (Inv_K13598 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13288 B APIf ra empty).
Proof.
  intros Ha0 H98 g c (L & A & regs & mem & md & -> & HFR & HP & (Hn6 & HOUR & H11 & H12 & H21 & H27)).
  pose proof (sl_fr_bnd B APIf ra empty FF g _ L A regs mem md HFR) as (Hsp & _ & HS1 & HS2 & HMI).
  destruct (b4_in_all B APIf ra empty FF g [] L A regs mem md HFR HP ltac:(lia)) as (Hp0 & Hpn & _).
  pose proof alloc_ceiling_value as Hac.
  assert (KO : forall m', Frame.munch [] mem m' -> OURb g m').
  { intros m' MU. apply (b4_OUR_keep g mem m'); [|exact HOUR].
    apply (b4_keep_munch [] mem m' _ _ MU I); unfold spk, fsp, SLOT_FRAME, SLOT_K, SLOT_STACK, SL_TOP in *; lia. }
  unfold rg in H11, H12, H21, H27.
  destruct (Z.eq_dec (g_n g) 6) as [E6|E6].
  - (* n = 6 *)
    eapply (b4_mid B APIf ra empty FF g [] L A regs mem md _ []); [exact HFR | exact HP | | | |].
    + intros x Hx O. exfalso. apply O. exact I.
    + rewrite sl_mkR_of. apply a03_evt6. rewrite H11. f_equal. lia.
    + intros ms (? & -> & _).
      do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
      split; [reflexivity|]. split; reflexivity.
    + intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
      destruct HQ as (s11' & HE & E11).
      injection HE; intros; subst.
      apply H98. exists L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      unfold PB, CUR, rg. rewrite !(sl_getr_eqv _ _ _ Hx).
      replace (c0 (g_in g)) with 6 by (unfold c0, g_n in *; lia).
      split; [|exact (KO m' MU')].
      split; [lia|]. split.
      * exact H21.
      * replace (g_n g - 6) with 0 by lia. reflexivity.
  - (* n >= 7 *)
    set (b := RcIdentModel.nthb (g_in g) (Z.to_nat 6)).
    pose proof (b4_in_rd B APIf ra empty FF g [] L A regs mem md 6 HFR HP ltac:(lia)) as HR.
    fold b in HR.
    assert (Emode : mode (g_in g) = bv_unsigned b).
    { unfold mode. replace (7 <=? nlen (g_in g)) with true by (symmetry; apply Z.leb_le; unfold g_n in *; lia).
      reflexivity. }
    eapply (b4_mid B APIf ra empty FF g [] L A regs mem md _ []); [exact HFR | exact HP | | | |].
    + intros x Hx O. exfalso. apply O. exact I.
    + rewrite sl_mkR_of.
      apply a03_evt7 with (x := g_n g - 6) (q := g_p g + 5) (y := g_n g - 5) (b := b);
        [exact H11 | exact H12 | exact H27 | lia | lia | lia | lia |].
      replace (g_p g + 5 + 1) with (g_p g + 6) by lia. exact HR.
    + intros ms (? & ? & ? & ? & -> & _).
      do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
      split; [reflexivity|]. split; reflexivity.
    + intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
      destruct HQ as (s0' & a0' & s5' & s11' & HE & E0 & E5 & E11).
      injection HE; intros; subst.
      assert (HRA : RA g regs' m').
      { unfold RA, CUR, rg. rewrite !(sl_getr_eqv _ _ _ Hx).
        split; [lia|]. split; [|exact (KO m' MU')].
        split; [lia|]. split.
        - replace (g_p g + 7) with (g_p g + 5 + 2) by lia. reflexivity.
        - replace (g_n g - 7) with (g_n g - 5 - 2) by lia. reflexivity. }
      destruct (Z.odd (bv_unsigned b)) eqn:Eo.
      * apply Ha0. exists L, A, regs', m', md.
        split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
        split; [exact HRA|]. split.
        -- unfold rg. rewrite (sl_getr_eqv _ _ _ Hx), Emode. reflexivity.
        -- unfold rt_on. rewrite Emode. exact Eo.
      * apply H98. exists L, A, regs', m', md.
        split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
        destruct HRA as (_ & HC & HO). unfold PB.
        replace (c0 (g_in g)) with 7 by (unfold c0, g_n in *; lia).
        split; [exact HC | exact HO].
Qed.

End A03.
