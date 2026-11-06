(* Segment C05 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan): [0x140d0, 0x140d8], the match check and free(Φ).
   U140d0 -> U140dc: 0x140d0 `bne a0,s9` (#93) is not taken, a0 = want = want_m = s9 (C4.12, u8_want_eq); free of
   the one live harness block Φ (FF's allocator, u8_free_call) keeps the frame bytes [sp, S), so LK, FC and IFS(j + 1)
   hold at 0x140dc, the return point of the free call (v1.9.0 has no `li a2,1` there: the cut U140dc of the bundle,
   v1.8 U140e8). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract Img0 FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u8m Tac_u8.
Import ListNotations.
Open Scope Z_scope.

(* 0x140d0 `bne a0,s9` not taken (a0 = s9), `mv a0,s7`, `jal free`. *)
Lemma c05_k :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0 = s9 ->
    evt rsegs
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x140dc) sp gp tp t0 t1 t2 s0 s1 s7 a1 a2 a3 a4 a5 a6 a7
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x17280) fc None m
                     (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x140d0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m E. subst a0. step.
  if_cases HC; [exfalso; unfold bv_eqb in HC; rewrite Z.eqb_refl in HC; discriminate HC|].
  step. step. apply evt_done. reflexivity.
Qed.

(* The frame bytes [sp, S) kept by free carry the bundles of the frame slots. *)
Lemma c05_ba : forall g mem mem' a bs, bytes_at rsegs mem a bs ->
  (forall x, fsp g <= x < g_S g -> mbyte rsegs mem' x = mbyte rsegs mem x) ->
  fsp g <= a -> a + Z.of_nat (length bs) <= g_S g -> bytes_at rsegs mem' a bs.
Proof. intros g mem mem' a bs H HK H1 H2. apply (u8_ba_mbyte mem); [exact H|]. intros i Hi. apply HK. lia. Qed.

Lemma c05_q64 : forall g mem mem' a v, q64 mem a v ->
  (forall x, fsp g <= x < g_S g -> mbyte rsegs mem' x = mbyte rsegs mem x) ->
  fsp g <= a -> a + 8 <= g_S g -> q64 mem' a v.
Proof.
  unfold q64. intros g mem mem' a v H HK H1 H2. apply (c05_ba g mem); [exact H | exact HK | exact H1|].
  rewrite length_le8. lia.
Qed.

Lemma c05_LK : forall g j regs regs' mem mem', LK g j regs mem ->
  YK11.getr regs' 8 = YK11.getr regs 8 -> YK11.getr regs' 9 = YK11.getr regs 9 ->
  YK11.getr regs' 18 = YK11.getr regs 18 ->
  (forall x, fsp g <= x < g_S g -> mbyte rsegs mem' x = mbyte rsegs mem x) -> LK g j regs' mem'.
Proof.
  intros g j regs regs' mem mem' (Hj & H9 & HOUR & HM7 & HOVF & H18) E8 E9 E18 HK.
  split; [exact Hj|]. split; [exact (u8_rg _ _ _ _ E9 H9)|].
  split; [unfold OURb in *; apply (c05_ba g mem); [exact HOUR | exact HK | unfold spk; lia |];
          rewrite OUR_length; unfold spk, fsp, SLOT_FRAME; lia|].
  split; [unfold M7 in *; apply (c05_q64 g mem);
          [exact HM7 | exact HK | unfold spk; lia | unfold spk, fsp, SLOT_FRAME; lia]|].
  split; [unfold OVF in *; exact (u8_rg _ _ _ _ E8 HOVF)|].
  unfold S2 in *. exact (u8_rg _ _ _ _ E18 H18).
Qed.

Lemma c05_FC : forall g j regs regs' mem mem', FC g j regs mem ->
  YK11.getr regs' 21 = YK11.getr regs 21 -> YK11.getr regs' 22 = YK11.getr regs 22 ->
  (forall x, fsp g <= x < g_S g -> mbyte rsegs mem' x = mbyte rsegs mem x) -> FC g j regs' mem'.
Proof.
  intros g j regs regs' mem mem' (H24 & H21 & H22) E21 E22 HK.
  split; [apply (c05_q64 g mem); [exact H24 | exact HK | unfold spk; lia | unfold spk, fsp, SLOT_FRAME; lia]|].
  split; [exact (u8_rg _ _ _ _ E21 H21) | exact (u8_rg _ _ _ _ E22 H22)].
Qed.

Lemma c05_IFS : forall g j mem mem', IFS g j mem ->
  (forall x, fsp g <= x < g_S g -> mbyte rsegs mem' x = mbyte rsegs mem x) -> IFS g j mem'.
Proof.
  intros g j mem mem' HI HK. pose proof (u8_tbody_len (g_in g) j) as Hbl.
  unfold IFS, IDj, IDb, IDB, FGj, FGb, FGB, FSj, FSb, q64, u32, u16, b8 in *.
  u8_bundle HI ltac:(fun H => apply (c05_ba g mem _ _ _ H HK); [unfold spk; lia|];
    rewrite ?length_le8, ?length_le4, ?length_le2, ?u8_tID_len, ?u8_tFG_len; cbn [length];
    unfold spk, fsp, SLOT_FRAME; lia).
Qed.

Section C05.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_C05 : forall j : nat, Hat B APIf ra (Inv_U140dc_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U140d0_at B APIf ra empty) j.
Proof.
  intros j H1 g c (phi & L & A & regs & mem & md & -> & HF & HP & (HC7 & H25 & H10)).
  pose proof HC7 as ((HLK & HFC & H23 & _ & _) & _ & HIFS).
  assert (Hin : In (phi, t_len (g_in g) j) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  destruct (u8_in_blocks L A _ _ Hin) as (p & Hp & Ep).
  assert (E1025 : YK11.getr regs 10 = YK11.getr regs 25)
    by (unfold rg in *; rewrite H10, H25, u8_want_eq; reflexivity).
  eapply (u8_run_to B APIf ra empty FF); [exact HF | unfold rmk; apply c05_k; exact E1025 | intros regs_c HG].
  unfold hb1 in HF, HP. rewrite <- Ep in HF, HP.
  apply (u8_free_call B APIf ra empty FF g L A regs mem md regs_c p (t_len (g_in g) j)).
  - exact HF.
  - exact HP.
  - exact Hp.
  - rewrite HG. reflexivity.
  - rewrite HG. reflexivity.
  - rewrite HG. reflexivity.
  - rewrite HG. apply ret_ok_even. reflexivity.
  - rewrite HG. transitivity (YK11.getr regs 23); [reflexivity|]. rewrite Ep. exact H23.
  - intros L' A' regs' mem' md' HF' HP' RP' HKEEP.
    replace (YK11.getr regs_c 1) with (Z_to_bv 64 0x140dc) by (rewrite HG; reflexivity).
    apply (H1 g). apply (u8_cut_close B APIf ra empty _ _ _ _ L' A'); [exact HF' | exact HP' |].
    split; [|split].
    + apply (c05_LK g j regs regs' mem mem' HLK); [| | | exact HKEEP].
      * etransitivity; [exact (RP' 8 ltac:(unfold callee_saved; lia))|].
        etransitivity; [apply HG|]. reflexivity.
      * etransitivity; [exact (RP' 9 ltac:(unfold callee_saved; lia))|].
        etransitivity; [apply HG|]. reflexivity.
      * etransitivity; [exact (RP' 18 ltac:(unfold callee_saved; lia))|].
        etransitivity; [apply HG|]. reflexivity.
    + apply (c05_FC g j regs regs' mem mem' HFC); [| | exact HKEEP].
      * etransitivity; [exact (RP' 21 ltac:(unfold callee_saved; lia))|].
        etransitivity; [apply HG|]. reflexivity.
      * etransitivity; [exact (RP' 22 ltac:(unfold callee_saved; lia))|].
        etransitivity; [apply HG|]. reflexivity.
    + exact (c05_IFS g (S j) mem mem' HIFS HKEEP).
Qed.

End C05.
