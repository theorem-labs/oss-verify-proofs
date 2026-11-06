From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require MState Exec Regs6ss RegisterBridge Step.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Step Exec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uab1.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.

Section B01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.

Ltac reads PAY c := try (pose proof (PAY c ltac:(lia))); try (pose proof (PAY (c + 1) ltac:(lia)));
  try (pose proof (PAY (c + 2) ltac:(lia))).
Ltac xtrap := match goal with H : Z.lxor (Z.b2z (?a <? ?b)) (Z.b2z (?c <? ?d)) = 0 |- _ =>
  rewrite (proj2 (Z.ltb_lt a b)) in H by lia; rewrite (proj2 (Z.ltb_ge c d)) in H by lia; discriminate H end.
Ltac stepx PAY c := lazymatch goal with
  | |- evt _ _ (MState.MS _ _ (Z_to_bv 64 88756) _ _ _ _) => fail
  | |- evt _ _ (MState.MS _ _ (Z_to_bv 64 81488) _ _ _ _) => fail
  | |- evt _ _ (MState.MS _ _ (if _ then _ else _) _ _ _ _) =>
      let H := fresh "HB" in if_cases H; zify_cond H; try (exfalso; lia); try xtrap;
        try (exfalso; rewrite Z.mod_small in H by lia; lia); reads PAY c
  | _ => step
  end.

Ltac stk_tr STK H := eapply (t_stack_keep B APIf ra empty FF _ _ _ _ _ STK H);
  unfold spk, fsp, SLOT_FRAME; rewrite ?length_le8, ?length_le4, ?rec_id_length, ?t_hwb_len; cbn [length];
  unfold RcIdentModel.ID_SIZE; lia.

Lemma seg_B01 : forall i,
  Hrec B APIf ra (Inv_U130fc_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U13058_at B APIf ra empty) i.
Proof.
  intros i HX g c (L & A & regs & mem & md & -> & HFR & HP & (HREC & HCUR & HID & HA2)).
  pose proof (ff_segs B APIf ra empty FF) as SEG.
  pose proof (t_md B APIf ra empty FF L A mem md ltac:(apply HFR)) as [Hh Hl].
  eapply (kb_run_rz B regs _ mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x15ab4 /\ mem' = mem /\
       Sem.reg_get R 1 = Z_to_bv 64 0x130fc /\ Sem.reg_get R 2 = getr regs 2 /\ Sem.reg_get R 3 = getr regs 3 /\
       Sem.reg_get R 4 = getr regs 4 /\ Sem.reg_get R 9 = getr regs 9 /\
       Sem.reg_get R 10 = Z_to_bv 64 (rec_k (g_in g) i) /\ Sem.reg_get R 20 = Z_to_bv 64 (rec_k (g_in g) i) /\
       Sem.reg_get R 22 = Z_to_bv 64 (rec_addr (g_in g) i) /\
       Sem.reg_get R 23 = Z_to_bv 64 (g_p g + rec_body (g_in g) i) /\
       Sem.reg_get R 25 = Z_to_bv 64 (rec_Lp (g_in g) i) /\
       Sem.reg_get R 26 = Z_to_bv 64 (g_p g + rec_c (g_in g) (S i)))); [exact Hh | exact Hl | |].
  - destruct HCUR as (Hc & HS10 & HS9). destruct HREC as (HiN & HS1 & HNR & HG24 & HHW & HEV).
    pose proof HFR as (HGV & _). pose proof HGV as (Gn & Gpl & _ & _ & _ & _ & _ & _ & _ & HPB).
    pose proof (t_pbnd B APIf ra empty FF g _ _ L A regs mem md HFR HP) as PBD.
    assert (HPBx : 0 < g_n g -> 4096 <= g_p g) by (intros Hn; destruct HPB as [HPB|HPB]; lia).
    assert (Hp0 : 0 < g_p g).
    { destruct Gpl as [[Gn0 Gpe]|[Gn1 _]]; [|apply HPBx in Gn1; lia].
      rewrite Gpe. destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        _ & HE & _). lia. }
    pose proof (t_payload B APIf ra empty FF _ _ _ _ _ _ _ _ HFR HP) as PAY.
    pose proof (rec_bounds (g_in g) i) as RB. cbn [rec_c] in RB.
    cbn [rec_c].
    set (c := rec_c (g_in g) i) in *.
    pose proof (bv_unsigned_in_range 8 (RcIdentModel.nthb (g_in g) (Z.to_nat (c + 2)))) as RW2.
    change (bv_modulus 8) with 256 in RW2.
    rewrite SEG. unfold KindBGlue.rmk. rewrite HS10, HS9, HA2. unfold Frame.mkR.
    repeat (stepx PAY c).
    all: apply evt_done; do 3 eexists; split; [reflexivity|]; simp_regs.
    all: split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|].
    all: split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|].
    all: unfold rec_k, rec_addr, rec_body, rec_Lp, rec_raw, h_next, h_k, h_Lp, h_left, h_h, h_w, h_body, h_raw, h_lo, h_hi in *.
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
  - intros R pc' mem' regs' (-> & -> & K1 & K2 & K3 & K4 & K9 & K10 & K20 & K22 & K23 & K25 & K26) HG.
    assert (GR : forall r, bv_eqb r 0 = false -> getr regs' r = Sem.reg_get R r)
      by (intros r Hr; rewrite HG; exact (t_getr_R R r Hr)).
    assert (E1 : getr regs' 1 = Z_to_bv 64 0x130fc) by (rewrite GR by reflexivity; exact K1).
    assert (E2 : getr regs' 2 = getr regs 2) by (rewrite GR by reflexivity; exact K2).
    assert (E3 : getr regs' 3 = getr regs 3) by (rewrite GR by reflexivity; exact K3).
    assert (E4 : getr regs' 4 = getr regs 4) by (rewrite GR by reflexivity; exact K4).
    assert (E10 : getr regs' 10 = Z_to_bv 64 (rec_k (g_in g) i)) by (rewrite GR by reflexivity; exact K10).
    pose proof HFR as (HGV & _ & _ & _ & _ & _ & HMI & _ & HMR & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRES & _).
    pose proof HGV as (_ & _ & _ & _ & _ & _ & GROOM & _).
    pose proof (nrec_range (g_in g)) as NRR. pose proof (rec_k_range (g_in g) i) as KR.
    destruct HREC as (HiN & HS1 & HNR & HG24 & HHW & HEV).
    replace (Z_to_bv 64 88756) with (Z_to_bv 64 (ms_malloc B)) by (rewrite (ff_malloc B APIf ra empty FF); reflexivity).
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
      unfold NRb, G24, HWb, EVb, IDb, q64, u32 in *. destruct HHW as (HW1 & HW2 & HW3).
      split; [split; [split; [exact HiN|] |] |].
      * split; [etransitivity; [exact (PR 9 ltac:(unfold callee_saved; lia) eq_refl)|]; etransitivity; [exact K9|]; exact HS1|].
        split; [stk_tr STK HNR|]. split; [stk_tr STK HG24|].
        split; [split; [stk_tr STK HW1|]; split; [stk_tr STK HW2 | stk_tr STK HW3]|]. stk_tr STK HEV.
      * split; [etransitivity; [exact (PR 22 ltac:(unfold callee_saved; lia) eq_refl)|]; exact K22|].
        split; [etransitivity; [exact (PR 20 ltac:(unfold callee_saved; lia) eq_refl)|]; exact K20|].
        etransitivity; [exact (PR 26 ltac:(unfold callee_saved; lia) eq_refl)|]; exact K26.
      * split; [etransitivity; [exact (PR 23 ltac:(unfold callee_saved; lia) eq_refl)|]; exact K23|].
        split; [etransitivity; [exact (PR 25 ltac:(unfold callee_saved; lia) eq_refl)|]; exact K25|].
        split; [stk_tr STK HID|].
        exact R10.
Qed.
End B01.
