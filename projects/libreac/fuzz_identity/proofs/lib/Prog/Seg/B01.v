From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require MState Exec Regs6ss RegisterBridge Step.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP URzKP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Step Exec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sb1.
Import ListNotations.
Open Scope Z_scope.

Section B01.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Ltac go := repeat (lazymatch goal with
  | |- evt _ _ (MState.MS _ _ (Z_to_bv 64 87424) _ _ _ _) => fail
  | |- evt _ _ (MState.MS _ _ (if _ then _ else _) _ _ _ _) => fail
  | _ => step end).
Ltac br H := if_cases H; zify_cond H; try (exfalso; lia).
Ltac reads PAY c := try (pose proof (PAY c ltac:(lia))); try (pose proof (PAY (c + 1) ltac:(lia)));
  try (pose proof (PAY (c + 2) ltac:(lia))).
Ltac stepx PAY c := lazymatch goal with
  | |- evt _ _ (MState.MS _ _ (Z_to_bv 64 87424) _ _ _ _) => fail
  | |- evt _ _ (MState.MS _ _ (if _ then _ else _) _ _ _ _) =>
      let H := fresh "HB" in if_cases H; zify_cond H; try (exfalso; lia); reads PAY c
  | _ => step
  end.

Ltac stk_tr STK H := eapply (t_stack_keep B APIf ra empty FF _ _ _ _ _ STK H);
  unfold spk, fsp, SLOT_FRAME; rewrite ?length_le8, ?length_le4, ?rec_id_length, ?t_hwb_len; cbn [length];
  unfold RcIdentModel.ID_SIZE; lia.

Lemma seg_B01 : forall i,
  Hrec B APIf ra (Inv_K13068_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K12fc4_at B APIf ra empty) i.
Proof.
  intros i HX g c (L & A & regs & mem & md & -> & HFR & HP & (HREC & HCUR & HID)).
  pose proof (ff_segs B APIf ra empty FF) as SEG.
  pose proof (t_md B APIf ra empty FF L A mem md ltac:(apply HFR)) as [Hh Hl].
  eapply (kb_run_rz B regs _ mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x15580 /\ mem' = mem /\
       Sem.reg_get R 1 = Z_to_bv 64 0x13068 /\ Sem.reg_get R 2 = getr regs 2 /\ Sem.reg_get R 3 = getr regs 3 /\
       Sem.reg_get R 4 = getr regs 4 /\ Sem.reg_get R 19 = getr regs 19 /\
       Sem.reg_get R 10 = Z_to_bv 64 (rec_k (g_in g) i) /\ Sem.reg_get R 21 = Z_to_bv 64 (rec_k (g_in g) i) /\
       Sem.reg_get R 23 = Z_to_bv 64 (rec_addr (g_in g) i) /\
       Sem.reg_get R 20 = Z_to_bv 64 (g_p g + rec_body (g_in g) i) /\
       Sem.reg_get R 26 = Z_to_bv 64 (rec_Lp (g_in g) i))); [exact Hh | exact Hl | |].
  - destruct HCUR as (Hc & HS4 & HS10). destruct HREC as (HiN & HS3 & HNR & HG16 & HHW).
    pose proof HFR as (HGV & _). pose proof HGV as (Gn & _).
    pose proof (t_payload B APIf ra empty FF _ _ _ _ _ _ _ _ HFR HP) as PAY.
    set (c := rec_c (g_in g) i) in *.
    rewrite SEG. unfold KindBGlue.rmk. rewrite HS4, HS10. unfold Frame.mkR.
    repeat (stepx PAY c).
    all: apply evt_done; do 3 eexists; split; [reflexivity|]; simp_regs.
    all: split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|].
    all: split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|].
    all: unfold rec_k, rec_addr, rec_body, rec_Lp, rec_raw, h_k, h_Lp, h_left, h_h, h_w, h_body, h_raw, h_lo, h_hi.
    all: fold c; unfold g_n in *.
    all: try rewrite (t_inb_past (g_in g) (c + 2)) by lia; try rewrite (t_inb_past (g_in g) (c + 1)) by lia;
      try rewrite (t_inb_past (g_in g) c) by lia.
    all: unfold inb, RcIdentModel.bz, Mem.zxb in *.
    all: set (lo := bv_unsigned (RcIdentModel.nthb (g_in g) (Z.to_nat c))) in *;
      set (hi := bv_unsigned (RcIdentModel.nthb (g_in g) (Z.to_nat (c + 1)))) in *;
      set (w := bv_unsigned (RcIdentModel.nthb (g_in g) (Z.to_nat (c + 2)))) in *.
    all: assert (Rlo : 0 <= lo < 256) by apply bz_range; assert (Rhi : 0 <= hi < 256) by apply bz_range;
      assert (Rw : 0 <= w < 256) by apply bz_range.
    all: rewrite ?(t_unsigned lo) in * by lia; rewrite ?(t_unsigned hi) in * by lia; rewrite ?(t_unsigned w) in * by lia.
    all: rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 in * by lia; change (2 ^ 6) with 64 in *; change (2 ^ 8) with 256 in *.
    all: rewrite ?(t_unsigned (hi / 64)) in * by (Z.div_mod_to_equations; lia).
    all: rewrite ?(t_unsigned (hi * 256)) in * by lia.
    all: rewrite ?(KindBGlue.kb_lor_low (hi * 256) lo 8) in * by (change (2 ^ 8) with 256; first [lia | Z.div_mod_to_equations; lia]).
    all: rewrite ?(t_signed (hi / 64)) in * by (Z.div_mod_to_equations; lia); rewrite ?(t_signed 1) in * by lia.
    all: unfold h_h, h_left.
    all: repeat split.
    all: f_equal.
    all: try (unfold pick; rewrite ?t_raw_div by lia).
    all: unfold RcIdentModel.ADDR_FIRMWARE, RcIdentModel.ADDR_REAC_VERSION, RcIdentModel.ADDR_MODEL_NAME.
    all: repeat match goal with |- context [?x =? ?y] => destruct (Z.eqb_spec x y) end.
    all: first [lia | Z.div_mod_to_equations; lia].
  - intros R pc' mem' regs' (-> & -> & K1 & K2 & K3 & K4 & K19 & K10 & K21 & K23 & K20 & K26) HG.
    assert (GR : forall r, bv_eqb r 0 = false -> getr regs' r = Sem.reg_get R r)
      by (intros r Hr; rewrite HG; exact (t_getr_R R r Hr)).
    assert (E1 : getr regs' 1 = Z_to_bv 64 0x13068) by (rewrite GR by reflexivity; exact K1).
    assert (E2 : getr regs' 2 = getr regs 2) by (rewrite GR by reflexivity; exact K2).
    assert (E3 : getr regs' 3 = getr regs 3) by (rewrite GR by reflexivity; exact K3).
    assert (E4 : getr regs' 4 = getr regs 4) by (rewrite GR by reflexivity; exact K4).
    assert (E10 : getr regs' 10 = Z_to_bv 64 (rec_k (g_in g) i)) by (rewrite GR by reflexivity; exact K10).
    pose proof HFR as (HGV & _ & _ & _ & _ & _ & HMI & _ & HMR & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRES & _).
    pose proof HGV as (_ & _ & _ & _ & _ & _ & GROOM & _).
    pose proof (nrec_range (g_in g)) as NRR. pose proof (rec_k_range (g_in g) i) as KR.
    destruct HREC as (HiN & HS3 & HNR & HG16 & HHW).
    replace (Z_to_bv 64 87424) with (Z_to_bv 64 (ms_malloc B)) by (rewrite (ff_malloc B APIf ra empty FF); reflexivity).
    eapply rz_bind; [apply (rz_malloc L A regs' mem md (rec_k (g_in g) i) (sb_hb (g_b g) [])) | ].
    + apply (CP_of_FR B APIf ra empty FF g _ _ L A regs regs' mem md HFR E2 E4).
      rewrite E1. apply t_ret_ok_lit; lia.
    + exact HMI.
    + exact E10.
    + exact HRES.
    + exact (rz_room_of L A mem md (g_b g) 0 0 (rec_k (g_in g) i) HMR GROOM ltac:(lia) ltac:(lia) ltac:(lia)).
    + intros c' HMret.
      destruct (FR_malloc B APIf ra empty FF g _ _ L A regs regs' mem md _ c' HFR HP E2 E3 E4 HMret)
        as (L' & A' & R2 & mem' & md' & res & -> & HFR' & HP' & HPRES & R10 & NZ & AL & FRESH & STK & HBK).
      rewrite E1. apply (HX g). exists res, L', A', R2, mem', md'. split; [reflexivity|].
      split; [exact HFR'|]. split; [exact HP'|].
      assert (PR : forall r : Z, callee_saved r -> bv_eqb (Z_to_bv 5 r) 0 = false ->
        getr R2 (Z_to_bv 5 r) = Sem.reg_get R (Z_to_bv 5 r)).
      { intros r Hr Hz. rewrite (HPRES r Hr). apply GR. exact Hz. }
      unfold NRb, G16, HWb, IDb, q64, u32 in *. destruct HHW as (HW1 & HW2 & HW3).
      split; [split; [split; [exact HiN|] |] |].
      * split; [etransitivity; [exact (PR 19 ltac:(unfold callee_saved; lia) eq_refl)|]; etransitivity; [exact K19|]; exact HS3|].
        split; [stk_tr STK HNR|]. split; [stk_tr STK HG16|].
        split; [stk_tr STK HW1|]. split; [stk_tr STK HW2|]. stk_tr STK HW3.
      * split; [etransitivity; [exact (PR 23 ltac:(unfold callee_saved; lia) eq_refl)|]; exact K23|].
        split; [etransitivity; [exact (PR 21 ltac:(unfold callee_saved; lia) eq_refl)|]; exact K21|].
        etransitivity; [exact (PR 20 ltac:(unfold callee_saved; lia) eq_refl)|]; exact K20.
      * split; [stk_tr STK HID|].
        split; [etransitivity; [exact (PR 26 ltac:(unfold callee_saved; lia) eq_refl)|]; exact K26|].
        exact R10.
Qed.
End B01.
