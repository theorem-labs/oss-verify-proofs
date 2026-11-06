(* Segment F06 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13748, 0x13764], K13748 (len = 0) and K1374c
   (1 <= len <= 49) -> K137c8. #41 is not taken: len < 50 gives k = 0 (struct P2.1); s6 = s2 = s0 = s1 = 0 and
   TF = 0 at sp+24. *)
(* libreac v1.9.0 (CHANGED code, new-insert; segment table 5a S_F06): v1.8 [0x1373c, 0x13758] K1373c / K13740 ->
   K137bc. The same 8 instructions with v1.9.0's registers: 0x13758 `sd zero,24(sp)` (type_filler; v1.8 sp+48),
   0x1375c `li s0,0` (is_8819; v1.8 `li s11,0`), 0x13760 `li s1,0` (sum_ok; v1.8 `li s0,0`), 0x13764 `j 0x137c8`.
   The table's "0x13750 mv s11,zero -> no counterpart / new 0x13760 mv s1,zero" is this renaming. Statements kept on
   the renamed cuts (f06_k restated on K137c8's v1.9 registers). rule 24: no function proved. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b1 Tac_b4.
Import ListNotations.
Open Scope Z_scope.

(* 0x1374c with k = 0: #41 not taken, the five zeros, to 0x137c8. *)
Lemma f06_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv : Z) (junk : list byte),
    sp = Z_to_bv 64 spv -> s7 = Z_to_bv 64 0 -> 0 <= spv -> spv + 1936 < 2 ^ 64 ->
    Step.rw_cells rsegs m (spv + 24) [Cells.CB 8 junk] ->
    evt rsegs
      (fun ms' => exists m' : word -> option byte,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 0) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) s3
                       s4 s5 (Z_to_bv 64 0) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x137c8) fc None m' (seg_rom rsegs) /\
         munch [(spv + 24, spv + 32)] m m' /\ wmono rsegs m m' /\ q64 m' (spv + 24) 0)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1374c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv junk Esp E7 Hs0 Hs1 HC.
  subst sp s7.
  pose proof (Step.rw_cells_store_ok rsegs m (spv + 24) [Cells.CB 8 junk] 0 (Cells.CB 8 junk) 8 HC
                eq_refl eq_refl) as HS.
  pose proof (munch_refl [(spv + 24, spv + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. if_false.
  step. step. step. step. step. step.
  apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
  pose proof (sl_cells_bytes _ _ _ HC) as HB. cbn [Cells.cells_bytes Cells.cbytes] in HB.
  rewrite app_nil_r in HB. exact HB.
Qed.

(* 0x13748 (len = 0): s7 = a0 = 0, then the same. *)
Lemma f06c_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv : Z) (junk : list byte),
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 0 -> 0 <= spv -> spv + 1936 < 2 ^ 64 ->
    Step.rw_cells rsegs m (spv + 24) [Cells.CB 8 junk] ->
    evt rsegs
      (fun ms' => exists m' : word -> option byte,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 0) s3 s4 s5 (Z_to_bv 64 0) (Z_to_bv 64 0) s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x137c8) fc None m' (seg_rom rsegs) /\
         munch [(spv + 24, spv + 32)] m m' /\ wmono rsegs m m' /\ q64 m' (spv + 24) 0)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13748) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv junk Esp E0 Hs0 Hs1 HC.
  subst a0.
  step.
  apply (f06_evt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ junk Esp eq_refl Hs0 Hs1 HC).
Qed.

Section F06.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* K137c8 from the state of K13748 / K1374c after the run: FT kept, FV of a frame shorter than 50 bytes. *)
Lemma f06_k : forall g j phi L A regs mem md regs' m',
  FR B APIf ra empty g (hb1 phi (t_len (g_in g) j)) L A regs mem md ->
  FR B APIf ra empty g (hb1 phi (t_len (g_in g) j)) L A regs' m' md ->
  Permutation (blocks L A) (hb1 phi (t_len (g_in g) j) ++ blocks (g_L g) (g_A g)) ->
  FT g j phi regs mem -> t_len (g_in g) j < 50 -> IFS g j regs mem -> V9 phi regs ->
  bytes_at rsegs mem (spk g 1752) (t_B (g_in g) j) ->
  Frame.munch [(spk g 24, spk g 32)] mem m' -> q64 m' (spk g 24) 0 ->
  YK11.getr regs' 19 = YK11.getr regs 19 -> YK11.getr regs' 20 = YK11.getr regs 20 ->
  YK11.getr regs' 21 = YK11.getr regs 21 -> YK11.getr regs' 25 = YK11.getr regs 25 ->
  YK11.getr regs' 26 = YK11.getr regs 26 -> YK11.getr regs' 27 = YK11.getr regs 27 ->
  rg regs' 23 0 -> rg regs' 8 0 -> rg regs' 18 0 -> rg regs' 9 0 -> rg regs' 22 0 ->
  Inv_K137c8_at B APIf ra empty g j
    (mkCfg (YK11.mkst regs' (Z_to_bv 64 0x137c8) m' (YK11.seg_rom (ms_segs B))) md).
Proof.
  intros g j phi L A regs mem md regs' m' HFR HFR' HP HFT Hs HIFS H25 HB MU H24 E19 E20 E21 E25 E26 E27
    R23 R8 R18 R9 R22.
  destruct (b4_small (g_in g) j Hs) as (Ebig & Esum & E88 & ETF & Ek & EB).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (_ & _ & HS1 & HS2 & _).
  destruct (b1_hb B APIf ra empty FF g phi _ L A regs mem md HFR HP) as (_ & Hphi0 & Hphin).
  pose proof alloc_ceiling_value as Hac.
  pose proof HFR as ((_ & _ & _ & _ & HSC & _) & _).
  pose proof (b4_len_range (g_in g) j) as (Hl0 & _).
  unfold SLOT_K, SLOT_STACK, SL_TOP in *.
  assert (K1 : b4_keep mem m' (spk g 8) (spk g 24)).
  { apply (b4_keep_munch _ mem m' _ _ MU); unfold spk, fsp, SLOT_FRAME in *; cbn [disjoint_from];
      repeat split; lia. }
  assert (K2 : b4_keep mem m' (spk g 32) (spk g 1788)).
  { apply (b4_keep_munch _ mem m' _ _ MU); unfold spk, fsp, SLOT_FRAME in *; cbn [disjoint_from];
      repeat split; lia. }
  assert (KH : b4_keep mem m' phi (phi + t_len (g_in g) j)).
  { apply (b4_keep_munch _ mem m' _ _ MU); unfold spk, fsp, SLOT_FRAME in *; cbn [disjoint_from];
      repeat split; lia. }
  unfold Inv_K137c8_at, FCUT, CUTST. exists phi, L, A, regs', m', md.
  split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
  split; [split|].
  - apply (b4_FT_keep2 g j phi regs regs' mem m' KH);
      [exact K1
      | eapply b4_keep_sub; [exact K2 | unfold spk; lia | unfold spk; lia]
      | exact E20 | exact E21 | exact E26 | exact E27 | exact HFT].
  - unfold FV, V7, V9, V0, V2, VC, rg in *. rewrite Ek, Esum, Ebig, E88, ETF. unfold b2z.
    split; [exact R23|]. split; [rewrite E25; exact H25|]. split; [exact R9|]. split; [exact R18|].
    split; [exact R8|]. split; [exact R22|]. split; [exact H24|].
    eapply b4_ba_keep; [exact HB | exact K2 | unfold spk; lia | rewrite EB, repeat_length; unfold spk; lia].
  - apply (b4_IFS_keep2 g j regs regs' mem m');
      [eapply b4_keep_sub; [exact K1 | unfold spk; lia | lia]
      | eapply b4_keep_sub; [exact K2 | unfold spk; lia | unfold spk; lia] | exact E19 | exact HIFS].
Qed.

Lemma seg_F06 : forall j : nat, Hat B APIf ra (Inv_K137c8_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_K13748_at B APIf ra empty) j /\ Hat B APIf ra (Inv_K1374c_at B APIf ra empty) j.
Proof.
  intros j H. split.
  - intros g c (phi & L & A & regs & mem & md & -> & HFR & HP & (HFT & Hz & HIFS & H25 & H10 & HB)).
    destruct (b4_small (g_in g) j ltac:(lia)) as (_ & _ & _ & _ & Ek & _).
    rewrite Ek in H10.
    destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & _ & HS1 & HS2 & _).
    pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
    unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
    destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 24) 8 ST ltac:(lia) ltac:(lia)) as (junk & HC).
    set (W := [(g_S g - 1936 + 24, g_S g - 1936 + 32)]).
    eapply (b4_mid B APIf ra empty FF g _ L A regs mem md _ W); [exact HFR | exact HP | | | |].
    + intros x Hx O. refine (b4_fp g W x _ Hx O). unfold W, SLOT_K, SLOT_STACK.
      apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil].
    + rewrite sl_mkR_of. apply f06c_evt with (spv := g_S g - 1936) (junk := junk); [exact Hsp | exact H10 | lia | lia | exact HC].
    + intros ms (m' & -> & MU & WM & _).
      do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      split; [reflexivity|]. split; reflexivity.
    + intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
      destruct HQ as (m'' & HE & _ & _ & H24). injection HE; intros; subst.
      apply H. apply (f06_k g j phi L A regs mem md regs' m' HFR HFR' HP HFT ltac:(lia) HIFS H25 HB MU'
                        (b1_out _ _ _ _ Hrel H24));
        unfold rg; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity.
  - intros g c (phi & L & A & regs & mem & md & -> & HFR & HP & (HFT & Hl & HIFS & H25 & H23 & HB)).
    destruct (b4_small (g_in g) j ltac:(lia)) as (_ & _ & _ & _ & Ek & _).
    unfold V7 in H23. rewrite Ek in H23.
    destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & _ & HS1 & HS2 & _).
    pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
    unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
    destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 24) 8 ST ltac:(lia) ltac:(lia)) as (junk & HC).
    set (W := [(g_S g - 1936 + 24, g_S g - 1936 + 32)]).
    eapply (b4_mid B APIf ra empty FF g _ L A regs mem md _ W); [exact HFR | exact HP | | | |].
    + intros x Hx O. refine (b4_fp g W x _ Hx O). unfold W, SLOT_K, SLOT_STACK.
      apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil].
    + rewrite sl_mkR_of. apply f06_evt with (spv := g_S g - 1936) (junk := junk); [exact Hsp | exact H23 | lia | lia | exact HC].
    + intros ms (m' & -> & MU & WM & _).
      do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      split; [reflexivity|]. split; reflexivity.
    + intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
      destruct HQ as (m'' & HE & _ & _ & H24). injection HE; intros; subst.
      apply H. apply (f06_k g j phi L A regs mem md regs' m' HFR HFR' HP HFT ltac:(lia) HIFS H25 HB MU'
                        (b1_out _ _ _ _ Hrel H24));
        unfold rg; rewrite (sl_getr_eqv _ _ _ Hx); first [reflexivity | exact H23].
Qed.

End F06.
