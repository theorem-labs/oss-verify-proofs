(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode Tac InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanCtrlProps.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase AKit ARep F_apoison APoisonR_iface AFrameD.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma poison_cells_frameD : forall W m m', poison_cells m -> munch W m m' ->
  disjoint_from W 0xc72f8 48 -> disjoint_from W 0xc7328 8 -> disjoint_from W 0xc91b0 16 -> disjoint_from W 0xcfcf8 8 ->
  disjoint_from W 0xd09e0 24 -> disjoint_from W 0xcf55c 1 -> disjoint_from W 0x1618a0 8 -> poison_cells m'.
Proof.
  intros W m m' (P1 & P2 & P3 & P4 & P5 & P6 & P7) MU D1 D2 D3 D4 D5 D6 D7. unfold poison_cells.
  repeat lazymatch goal with |- _ /\ _ => split end;
    (eapply cells_frameD; [eassumption | exact MU | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; assumption]).
Qed.
Lemma premap_cells_frameD : forall W m m', premap_cells m -> munch W m m' ->
  disjoint_from W 0xc72e8 8 -> disjoint_from W 0x15f7a0 8 -> disjoint_from W 0x1618b8 8 -> disjoint_from W 0x161900 8 ->
  disjoint_from W 0x161918 8 -> disjoint_from W 0x622cf0 8 -> disjoint_from W 0x622f70 8 -> premap_cells m'.
Proof.
  intros W m m' (P1 & P2 & P3 & P4 & P5 & P6 & P7) MU D1 D2 D3 D4 D5 D6 D7. unfold premap_cells.
  repeat lazymatch goal with |- _ /\ _ => split end;
    first [ apply premap_canary_any      (* [comment removed for export] *)
          | (eapply cells_frameD; [eassumption | exact MU | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; assumption]) ].
Qed.
(* [comment removed for export] *)
Lemma poison_cells_highD : forall W m m', poison_cells m -> munch W m m' -> Forall (fun iv => AIMG_HI <= fst iv) W -> poison_cells m'.
Proof.
  intros W m m' PC MU HW.
  assert (D : forall A n, A + n <= AIMG_HI -> disjoint_from W A n).
  { intros A n HA. clear MU PC. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| apply IH]. }
  unfold AIMG_HI in D. eapply poison_cells_frameD; [exact PC | exact MU | ..]; apply D; lia.
Qed.
Lemma premap_cells_highD : forall W m m', premap_cells m -> munch W m m' ->
  Forall (fun iv => AIMG_HI <= fst iv /\ (snd iv <= 0x622cf0 \/ 0x622f78 <= fst iv)) W -> premap_cells m'.
Proof.
  intros W m m' PC MU HW.
  assert (D : forall A n, (A + n <= AIMG_HI \/ (0x622cf0 <= A /\ A + n <= 0x622f78)) -> 0 < n -> disjoint_from W A n).
  { intros A n HA HN. clear MU PC. induction HW as [|[lo hi] W [H1 H1'] H2 IH]; cbn in *; [exact I|]. split; [unfold AIMG_HI in *; lia| apply IH]. }
  unfold AIMG_HI in D. eapply premap_cells_frameD; [exact PC | exact MU | ..]; apply D; lia.
Qed.

Definition poison0_post (RNG : footprint) (sp : word) (addr size lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG'
  /\ munch [(bv_unsigned sp - PZR_STACK, bv_unsigned sp); (shad addr, shad addr + shlen size)] m m' /\ wmono bsegs m m'
  /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
  /\ rw_cells bsegs m' (shad addr) [CB (Z.to_nat (shlen size)) (zeros (shlen size))]
  /\ poison_cells m' /\ premap_cells m' /\ arelro0 m'.

(* [comment removed for export] *)
Lemma poison0_spec_gen : forall (R : Type) (k : AM R) (Q : R -> footprint -> machine_state -> Prop) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (addr size lo : Z) (junk : list byte),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PZR_STACK ->
  mem_inv bsegs m ->
  poison_cells m -> premap_cells m -> arelro0 m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 0 ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> ablk addr (addr + size) -> addr + size <= 2^47 ->
  rw_cells bsegs m (shad addr) [CB (Z.to_nat (shlen size)) junk] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) (shlen size) ->
  (forall RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      poison0_post RNG sp addr size lo m RNG' m' ->
      implS bsegs RNG' (aembed ATOP k) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (aembed ATOP (poison0 addr size k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x55d68) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros ST CEIL LO MI PC PRM RR -> -> -> AL SL SPOS HI HCE DST RIMG RSTK RSH KONT.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). word_range sp SPR. unfold PZR_STACK in *.
  pose proof HI as HI'. unfold ablk, AIMG_HI, KLS in HI'. pose proof atop_range as ATR.
  assert (SHR : 0x800bca00 <= shad addr /\ shad addr + shlen size <= 0x10007fff8000 /\ 0 < shlen size).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8. clear -AL SL SPOS HI' HCE ATR. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  rewrite (poison0_eq _ addr size k).
  iprefix.
  eapply evtF_cut.
  { eapply (poison_shadow_any RNG) with (addr := addr) (size := size) (v := 0) (lo := lo); try eassumption; try reflexivity.
    all: try (clear -CEIL LO LO0 SPR AL SL SPOS HI HI' HCE ATR; first [exact HI | lia]). }
  cbv beta. intros ms' PO. unfold poison_post in PO. destruct_exs PO. destruct PO as (-> & MUp & WMp & MIp & STp & SHZ).
  apply evtF_done. eapply KONT. unfold poison0_post, PZR_STACK.
  split; [apply fp_le_refl|].
  split. { eapply munch_weaken; [| exact MUp]. intros xq Hq. cbn in Hq |- *. clear -Hq. lia. }
  split; [exact WMp|]. split; [exact MIp|]. split; [exact STp|].
  split. { unfold zeros. rewrite ?unsigned_lit in SHZ by (clear; lia). exact SHZ. }
  split; [eapply poison_cells_highD; [exact PC | exact MUp |] | split; [eapply premap_cells_highD; [exact PRM | exact MUp |] | eapply arelro0_munch; [exact RR | exact MUp |]]];
    (repeat (apply Forall_cons; [cbn; unfold AIMG_HI, ARELRO_LO, ARELRO_HI; clear -CEIL LO SPR SHR; lia|]); apply Forall_nil).
Qed.

(* [comment removed for export] *)
Lemma poison0_spec : forall (R : Type) (k : AM R) (Q : R -> footprint -> machine_state -> Prop) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (addr size lo : Z) (junk : list byte),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PZR_STACK ->
  mem_inv bsegs m ->
  poison_cells m -> premap_cells m -> arelro0 m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 0 ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> ablk addr (addr + size) -> addr + size <= ATOP ->     (* [comment removed for export] *)
  rw_cells bsegs m (shad addr) [CB (Z.to_nat (shlen size)) junk] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) (shlen size) ->
  (forall RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      poison0_post RNG sp addr size lo m RNG' m' ->
      implS bsegs RNG' (aembed ATOP k) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (aembed ATOP (poison0 addr size k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x55d68) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros ST CEIL LO MI PC PRM RR E0 E1 E2 AL SL SPOS HI HCE DST RIMG RSTK RSH KONT.
  pose proof atop_range as ATR.
  eapply (poison0_spec_gen R k Q RNG) with (addr := addr) (size := size) (lo := lo) (junk := junk); try eassumption.
  clear -HCE ATR. lia.
Qed.
End CANSEC1.
