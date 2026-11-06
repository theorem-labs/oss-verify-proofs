(* Segment R02 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x132ac, 0x132d0], K132ac -> K132d4
   (#1, #2: catalogue pointer and count non-zero; m = T + 296 ((mode >> 1) mod count); reac_identity_init(id)).
   libreac v1.9.0: T = 0x1ed30 (BOX_CATALOGUE), count sp+1792, id sp+154, frame 1936. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv reac_identity_init_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b1.
Import ListNotations.
Open Scope Z_scope.

Lemma r02_evt : reac_identity_init_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv md : Z) (idb : list byte),
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 0x1ed30 -> s0 = Z_to_bv 64 md ->
    0 <= md < 256 -> 0 < spv -> spv + 1936 <= 2 ^ 64 -> spv mod 2 = 0 ->
    ov_read_bytes rsegs m (wa (spv + 1792)) 8 = Some (le8 (Z_to_bv 64 11)) ->
    rw_cells rsegs m (spv + 154) [Cells.CB 38 idb] -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x132d4) sp gp tp t0' t1' t2' (Z_to_bv 64 (0x1ed30 + 296 * ((md / 2) mod 11))) s1
                       (Z_to_bv 64 (spv + 154)) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x132d4) fc None m' (seg_rom rsegs) /\
         munch [(spv + 154, spv + 192)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 154) (repeat (Z_to_bv 8 0) 38))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x132ac) fc None m (seg_rom rsegs)).
Proof.
  intros INIT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv md idb -> -> -> Hmd Hsp0 Hsp Hal HR HC MI.
  step. if_false_by (b1_beq0 0x1ed30 ltac:(lia)).
  step. step. if_false_by (b1_beq0 11 ltac:(lia)).
  step. step. step. step. step.
  rewrite (MState.unsigned_lit md) by lia. rewrite Z.shiftr_div_pow2 by lia.
  rewrite b1_remu by (try (pose proof (Z.div_pos md (2 ^ 1)); pose proof (Z.div_le_upper_bound md (2 ^ 1) md)); lia).
  rewrite (MState.unsigned_lit (md / 2 ^ 1 mod 11)) by (pose proof (Z.mod_pos_bound (md / 2 ^ 1) 11); lia).
  replace (126256 + md / 2 ^ 1 mod 11 * 296) with (0x1ed30 + 296 * ((md / 2) mod 11)) by (change (2 ^ 1) with 2; lia).
  step. step.
  eapply evt_cut.
  { eapply INIT with (id := spv + 154) (idb := idb);
      [reflexivity | lia | intros _; split; [lia | exact HC] | exact MI]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MUc & WMc & _ & _ & HZ).
  subst ms'. specialize (HZ ltac:(lia)).
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [replace (spv + 192) with (spv + 154 + 38) by lia; exact MUc|].
  split; [exact WMc | exact (sl_rw_bytes _ _ _ _ HZ)].
Qed.

Section R02.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis INIT : reac_identity_init_contract.

Lemma seg_R02 : Hcut B APIf ra (Inv_K132d4 B APIf ra empty) -> Hcut B APIf ra (Inv_K132ac B APIf ra empty).
Proof.
  intros H g c (L & A & regs & mem & md & -> & HFR & HP & (Hn7 & HCUR & HOUR) & Hs0 & Hon & H10 & Hq).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  pose proof alloc_ceiling_value as Hac.
  pose proof (b1_mode_rng (g_in g)) as Hmd.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 154) 38 ST ltac:(lia) ltac:(lia)) as (idb & HC).
  pose proof (b1_ld8 _ _ _ (bytes_at_normalize rsegs mem _ _ HMI Hq)) as HR.
  eapply (sl_mid B APIf ra empty FF g [] L A regs mem md); [exact HFR | exact HP | | |].
  - rewrite sl_mkR_of.
    apply (r02_evt INIT) with (spv := g_S g - 1936) (md := mode (g_in g)) (idb := idb);
      [exact Hsp | exact H10 | exact Hs0 | exact Hmd | lia | lia | lia | exact HR | exact HC
      | exact (mem_inv_normalize rsegs mem)].
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & MU & WM & _).
    do 3 eexists. split; [reflexivity|].
    split; [|split; [reflexivity | split; reflexivity]].
    exists [(g_S g - 1936 + 154, g_S g - 1936 + 192)]. split; [exact MU|]. split; [exact WM|].
    intros z Hz O. apply (sl_fp1 g (g_S g - 1936 + 154) (g_S g - 1936 + 192) z);
      [unfold SLOT_K, SLOT_STACK; lia | lia | exact Hz | exact O].
  - intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & MU & _ & HZ).
    injection HE; intros; subst.
    apply H. exists L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    destruct HCUR as (Hc7 & Hp7 & Hn7').
    unfold RA, CUR, OURb, IDB, rg in *. rewrite !(sl_getr_eqv _ _ _ Hx).
    split.
    { split; [exact Hn7|]. split; [split; [exact Hc7|]; split; [exact Hp7 | exact Hn7']|].
      apply (b1_keep _ mem m'' m' _ _ HMI MU Hrel); [|exact HOUR].
      rewrite OUR_length. cbn [disjoint_from]. split; [|exact I]. unfold spk, fsp, SLOT_FRAME. lia. }
    split; [reflexivity|].
    exact (b1_out _ _ _ _ Hrel HZ).
Qed.

End R02.
