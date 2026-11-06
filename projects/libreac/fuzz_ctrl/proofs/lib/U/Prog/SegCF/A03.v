(* Segment A03 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x13340, 0x1335c] and
   [0x136cc, 0x136e0], U13340 -> U13360 (n >= 7, mode odd), U136e4 (n <= 6 by 0x136cc, or mode even). Both arms
   into U136e4 zero the local `first` (memset(sp+36, 0, 40) at 0x136d4, new in v1.9). The UBSan check T02
   (cursor + 1 wraps) is not taken by PB. v1.9 keeps the cursor in s7 and left in s6 (v1.8: s6, s7). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF memset_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u1.
Import ListNotations.
Open Scope Z_scope.

(* memset(sp+36, 0, 40) at 0x136d4 (the `first` zeroing both arms into U136e4 share), back at 0x136e4. *)
Lemma a03m_evt : memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv : Z) (junk : list byte),
    sp = Z_to_bv 64 spv -> 0 < spv -> spv + 1936 <= 2 ^ 64 ->
    rw_cells rsegs m (spv + 36) [Cells.CB 40 junk] -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x136e4) sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x136e4) fc None m' (seg_rom rsegs) /\
         munch [(spv + 36, spv + 76)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 36) (repeat (Z_to_bv 8 0) 40))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x136d4) fc None m (seg_rom rsegs)).
Proof.
  intros MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv junk -> Hsp0 Hsp HC MI.
  step. step. step. step.
  eapply evt_cut.
  { eapply MSET with (junk := junk).
    - rewrite !MState.unsigned_lit by lia. exact HC.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MUc & WMc & _ & HZ).
  subst ms'. rewrite !MState.unsigned_lit in MUc, HZ by lia.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  apply evt_done. do 16 eexists. split; [reflexivity|].
  split; [|split; [exact WMc | exact (sl_rw_bytes _ _ _ _ HZ)]].
  eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x [Hx _]. split; [lia | exact I].
Qed.

(* left = 0 (n <= 6): beqz a1 to 0x136cc, s6 = 0, s7 = a0, then the memset into 0x136e4. *)
Lemma a03z_evt : memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv : Z) (junk : list byte),
    a1 = Z_to_bv 64 0 -> sp = Z_to_bv 64 spv -> 0 < spv -> spv + 1936 <= 2 ^ 64 ->
    rw_cells rsegs m (spv + 36) [Cells.CB 40 junk] -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x136e4) sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 (Z_to_bv 64 0) a0 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x136e4) fc None m' (seg_rom rsegs) /\
         munch [(spv + 36, spv + 76)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 36) (repeat (Z_to_bv 8 0) 40))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13340) fc None m (seg_rom rsegs)).
Proof.
  intros MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv junk -> Hspe Hsp0 Hsp HC MI.
  step. if_true. step. step.
  exact (a03m_evt MSET ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 0) a0
           s8 s9 s10 s11 t3 t4 t5 t6 F fc m spv junk Hspe Hsp0 Hsp HC MI).
Qed.

(* left >= 1 (n >= 7): T02 not taken (q + 1 >= 2), the mode byte b = in[6], s6 = left - 1, s7 = q + 1; mode odd
   falls into 0x13360, mode even goes to the memset at 0x136d4 and on to 0x136e4. *)
Lemma a03_evt : memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q l spv : Z) (b : byte) (par : bool)
         (junk : list byte),
    a0 = Z_to_bv 64 q -> a1 = Z_to_bv 64 l -> 1 <= l -> 1 <= q -> q + l < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa q) 1 = Some [b] -> Z.odd (bv_unsigned b) = par ->
    sp = Z_to_bv 64 spv -> 0 < spv -> spv + 1936 <= 2 ^ 64 ->
    rw_cells rsegs m (spv + 36) [Cells.CB 40 junk] -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' (zxb b) s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5
                       (Z_to_bv 64 (l + -1)) (Z_to_bv 64 (q + 1)) s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 (if par then 0x13360 else 0x136e4)) fc None m' (seg_rom rsegs) /\
         munch [(spv + 36, spv + 76)] m m' /\ wmono rsegs m m' /\
         (par = false -> bytes_at rsegs m' (spv + 36) (repeat (Z_to_bv 8 0) 40)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13340) fc None m (seg_rom rsegs)).
Proof.
  intros MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m q l spv b par junk -> -> Hl Hq Hql HR Hpar Hspe Hsp0 Hsp HC MI.
  pose proof (u1_byte_rng b) as Hb.
  step. if_false_by (u1_beq0 l ltac:(lia)).
  step. step. step.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false;
      [cbv iota | symmetry; unfold bv_ltu, bv_leu, bv_lts, bv_eqb; rewrite !MState.unsigned_lit by lia; solve_cond]
  end.
  step. step. step.
  try rewrite RcIdentLib.zxb_u. try rewrite (MState.unsigned_lit (bv_unsigned b)) by lia.
  rewrite u1_land1, Hpar.
  destruct par; cbv iota.
  - step. if_false. apply evt_done. do 17 eexists. split; [reflexivity|].
    split; [apply munch_refl|]. split; [apply wmono_refl|]. intros Hf. discriminate.
  - step. if_true.
    eapply evt_cut; [eapply (a03m_evt MSET); [exact Hspe | lia | lia | exact HC | exact MI]|].
    intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                E & MU & WM & HZ).
    subst ms'. apply evt_done. do 17 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. intros _. exact HZ.
Qed.

Section A03.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis MSET : memset_contract.

Lemma seg_A03 : Hcut B APIf ra (Inv_U13360 B APIf ra empty) -> Hcut B APIf ra (Inv_U136e4 B APIf ra empty) ->
  Hcut B APIf ra (Inv_U13340 B APIf ra empty).
Proof.
  intros H1 H2 g c (L & A & regs & mem & md & -> & HFR & HP & (HOUR & H10 & H11)).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  pose proof HFR as (HGV & _).
  pose proof HGV as ((Hn0 & Hn26) & _).
  pose proof alloc_ceiling_value as Hac.
  assert (Hlen : g_n g = nlen (g_in g)) by reflexivity.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 36) 40 ST ltac:(lia) ltac:(lia)) as (junk & HC).
  (* the run writes only `first` [sp+36, sp+76) *)
  assert (HW : forall m', Frame.munch [(g_S g - 1936 + 36, g_S g - 1936 + 76)] (normalize rsegs mem) m' ->
     Frame.wmono rsegs (normalize rsegs mem) m' ->
     exists W, Frame.munch W (normalize rsegs mem) m' /\ Frame.wmono rsegs (normalize rsegs mem) m' /\
       (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> g_S g - SLOT_K <= x < g_S g - 104)).
  { intros m' MU WM. exists [(g_S g - 1936 + 36, g_S g - 1936 + 76)]. split; [exact MU|]. split; [exact WM|].
    intros z Hz O. apply (sl_fp1 g (g_S g - 1936 + 36) (g_S g - 1936 + 76) z);
      [unfold SLOT_K, SLOT_STACK; lia | lia | exact Hz | exact O]. }
  destruct (Z_le_gt_dec (g_n g) 6) as [Hle|Hgt].
  - (* n <= 6: left = 0 after the six bytes *)
    replace (Z.min 6 (g_n g)) with (g_n g) in H10, H11 by lia.
    replace (g_n g - g_n g) with 0 in H11 by lia.
    eapply (sl_mid B APIf ra empty FF g [] L A regs mem md); [exact HFR | exact HP | | |].
    + rewrite sl_mkR_of.
      apply (a03z_evt MSET) with (spv := g_S g - 1936) (junk := junk);
        [exact H11 | exact Hsp | lia | lia | exact HC | exact (mem_inv_normalize rsegs mem)].
    + intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & MU & WM & _).
      do 3 eexists. split; [reflexivity|].
      split; [exact (HW m' MU WM)|]. split; [reflexivity | split; reflexivity].
    + intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
      destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & MU & _ & HZ).
      injection HE; intros; subst.
      apply H2. exists L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      unfold PB, CUR, OURb, FIRST0, rg, c0 in *. rewrite !(sl_getr_eqv _ _ _ Hx).
      replace (Z.min (nlen (g_in g)) 7) with (g_n g) by (unfold g_n; lia).
      split; [split; [lia|]; split; [exact H10 | replace (g_n g - g_n g) with 0 by lia; reflexivity]|].
      split.
      { apply (u1_keep _ mem m'' m' _ _ HMI MU Hrel); [|exact HOUR].
        rewrite OUR_length. cbn [disjoint_from]. split; [|exact I]. unfold spk, fsp, SLOT_FRAME. lia. }
      exact (u1_out _ _ _ _ Hrel HZ).
  - (* n >= 7: the mode byte in[6] *)
    replace (Z.min 6 (g_n g)) with 6 in H10, H11 by lia.
    destruct (u1_pb B empty g (g_n g - 1) HGV ltac:(lia)) as (Hp0 & Hpn & Hac47).
    pose proof (u1_in_rd B APIf ra empty FF g [] L A regs mem md 6 HFR HP ltac:(lia)) as HR.
    change (Z.to_nat 6) with 6%nat in HR.
    set (bm := RcIdentModel.nthb (g_in g) 6) in *.
    assert (Hmode : mode (g_in g) = bv_unsigned bm).
    { unfold mode. rewrite (proj2 (Z.leb_le 7 (nlen (g_in g)))) by (unfold g_n in Hgt; lia). reflexivity. }
    eapply (sl_mid B APIf ra empty FF g [] L A regs mem md); [exact HFR | exact HP | | |].
    + rewrite sl_mkR_of.
      apply (a03_evt MSET) with (q := g_p g + 6) (l := g_n g - 6) (b := bm) (par := Z.odd (bv_unsigned bm))
        (spv := g_S g - 1936) (junk := junk);
        [exact H10 | exact H11 | lia | lia | lia | exact HR | reflexivity | exact Hsp | lia | lia | exact HC
        | exact (mem_inv_normalize rsegs mem)].
    + intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & MU & WM & _).
      do 3 eexists. split; [reflexivity|].
      split; [exact (HW m' MU WM)|]. split; [reflexivity | split; reflexivity].
    + intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
      destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & MU & _ & HZ).
      injection HE; intros; subst.
      assert (HOUR' : OURb g m').
      { unfold OURb in *. apply (u1_keep _ mem m'' m' _ _ HMI MU Hrel); [|exact HOUR].
        rewrite OUR_length. cbn [disjoint_from]. split; [|exact I]. unfold spk, fsp, SLOT_FRAME. lia. }
      destruct (Z.odd (bv_unsigned bm)) eqn:Ep.
      * (* mode odd: the round trip *)
        apply H1. exists L, A, regs', m', md.
        split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
        unfold RA, CUR, rg, rt_on in *. rewrite !(sl_getr_eqv _ _ _ Hx).
        split.
        { split; [lia|]. split; [|exact HOUR'].
          split; [lia|]. split.
          - transitivity (Z_to_bv 64 (g_p g + 6 + 1)); [reflexivity | f_equal; lia].
          - transitivity (Z_to_bv 64 (g_n g - 6 + -1)); [reflexivity | f_equal; lia]. }
        split.
        { transitivity (zxb bm); [reflexivity|]. rewrite Hmode. reflexivity. }
        rewrite Hmode. exact Ep.
      * (* mode even: P01 *)
        apply H2. exists L, A, regs', m', md.
        split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
        unfold PB, CUR, FIRST0, rg, c0 in *. rewrite !(sl_getr_eqv _ _ _ Hx).
        replace (Z.min (nlen (g_in g)) 7) with 7 by (unfold g_n in Hgt; lia).
        split; [split; [lia|]; split|].
        { transitivity (Z_to_bv 64 (g_p g + 6 + 1)); [reflexivity | f_equal; lia]. }
        { transitivity (Z_to_bv 64 (g_n g - 6 + -1)); [reflexivity | f_equal; lia]. }
        split; [exact HOUR'|].
        exact (u1_out _ _ _ _ Hrel (HZ eq_refl)).
Qed.

End A03.
