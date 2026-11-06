From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require RcIdentModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Tac_si.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Exec Step Tac.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0 Contract FrameAPI KindBGlue MemNorm.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU reac_box_catalogue_defect_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uhj UTac_uhj_i UTac_uhj_j.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.


Local Ltac OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.Step.mem_after_store_opt ::= idtac.

Section J01.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis DEF : reac_box_catalogue_defect_contract.

Lemma seg_J01 : Hcut B APIf ra (Inv_U13ebc B APIf ra empty) -> Hcut B APIf ra (Inv_U13e70 B APIf ra empty).
Proof.
  intros HX g c (nm & tk & dp & HC).
  eapply (seg_go B APIf ra empty FF); [exact HX | | exact HC | ].
  { intros c' HC'. unfold Inv_U13ebc. exists nm, tk, dp. exact HC'. }
  intros L A regs mem md HFR HPM ((HI & R0) & HQ & E10).
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  destruct (FR_parts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (_ & PS & _ & _ & HMR & _).
  unfold SLOT_K, SLOT_STACK in PS.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & HMI & HRL & _).
  pose proof HI as (HID & E9 & HQ56 & HQ48 & E20 & E21 & E22 & E23 & E24 & E25 & E19 & HO & HE).
  destruct (HO R0) as (C1 & C2 & C3).
  destruct (HE R0) as (HNM & HDP).
  destruct (nr0_fits (g_in g) R0) as (Wk & F1 & F2 & F3).
  destruct (caps_range (g_in g)) as (K1 & K2 & K3 & K4 & K5 & K6).
  destruct (nmb_in _ _ _ _ _ _ HPM) as (N1 & N2 & N3).
  pose proof (blk_range B APIf _ _ _ _ _ _ HMR N3) as [BD1 BD2].
  pose proof YM05.alloc_ceiling_value as [AC1 AC2].
  unfold bsz in BD2.
  pose proof (Z.mod_pos_bound (t_row (g_in g)) 11 ltac:(lia)) as RM.
  set (r := t_row (g_in g) mod CAT_N).
  assert (Hr : 0 <= r < 11) by (unfold r, CAT_N; lia).
  assert (HCE : cat_entry mem (cat_row r) (catI r) (catO r) (catP r) (catS r) /\
    (catP r <> 0 -> catP r + Z.of_nat (length (catS r)) + 1 <= 2 ^ 40)).
  { eapply sj_cat_entry; first [exact FF | exact HRL | exact HMI | exact Hr]. }
  destruct HCE as (HCE & HCL).
  pose proof HCE as (CI & CO & CP & CB8 & CB16 & CB20 & CS).
  pose proof (rd8 _ _ _ (bytes_at_normalize rsegs mem _ _ HRO HQ)) as RQ. unfold spk, fsp, SLOT_FRAME in RQ.
  pose proof (rd8 _ _ _ (bytes_at_normalize rsegs mem _ _ HRO HQ48)) as R48. unfold spk, fsp, SLOT_FRAME in R48.
  pose proof (rd8 _ _ _ (bytes_at_normalize rsegs mem _ _ HRO HQ56)) as R56. unfold spk, fsp, SLOT_FRAME in R56.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO C3) as C3n.
  assert (CEe : cat_e (g_in g) = CAT + CAT_ROW * r) by reflexivity.
  assert (CEP : CAT <= cat_e (g_in g) < CAT + CAT_ROW * CAT_N) by (rewrite CEe; unfold CAT_ROW, CAT_N; lia).
  unfold CAT, CAT_ROW, CAT_N in CEP, CEe.
  assert (HIc : IRc g nm tk dp regs mem).
  { unfold IRc. split; [exact HID|]. split; [exact HQ56|]. split; [exact HQ48|]. split; [exact E20|].
    split; [exact E21|]. split; [exact E22|]. split; [exact E24|]. split; [exact E25|]. split; [exact HO|].
    split; [exact R0|]. split; [exact HNM | exact HDP]. }
  unfold rmk, Frame.mkR. rewrite E2, E10, E9, E22.
  step. step. unfold CAT_N. eqb_off.
  step. step. step.
  rewrite ?sj_remu by (unfold CAT_N; lia).
  step. step. step.
  rewrite ?MState.unsigned_lit by (unfold CAT, CAT_N in *; lia).
  unfold CAT, CAT_ROW, CAT_N.
  step. ltu_off.
  step. step. step. step.
  unfold PropExec.v_xor, PropExec.v_sltu, PropExec.c_ltu, PropExec.v_sltiu.
  repeat match goal with
  | |- context [bv_ltu ?a ?b] =>
      first [ replace (bv_ltu a b) with true by (symmetry; unfold bv_ltu; apply Z.ltb_lt; zarith)
            | replace (bv_ltu a b) with false by (symmetry; unfold bv_ltu; apply Z.ltb_ge; zarith) ]
  | |- context [?x <? ?y] =>
      first [ replace (x <? y) with true by (symmetry; apply Z.ltb_lt; zarith)
            | replace (x <? y) with false by (symmetry; apply Z.ltb_ge; zarith) ]
  end.
  cbv iota.
  lazymatch goal with |- context [bv_eqb ?a ?b] => replace (bv_eqb a b) with false by (vm_compute; reflexivity) end.
  cbv iota.
  step. step. step. step. step. step.
  eapply Exec.evt_cut.
  { eapply DEF with (lo := g_S g - 65536) (e := cat_e (g_in g)) (i := t_in (g_in g)) (o := t_out (g_in g))
      (d := dp) (I := catI r) (O := catO r) (P := catP r) (sP := catS r) (sd := n_EXP_DP (g_in g));
      rewrite ?(MState.unsigned_lit (g_S g - 384)) by lia; unfold REAC_BOX_CATALOGUE_DEFECT_FRAME.
    all: try first [reflexivity | lia | exact HMI0].
    - rewrite CEe. unfold r, CAT_N. f_equal. lia.
    - intros _. split; [exact (bytes_at_normalize rsegs mem _ _ HRO CB8)|].
      split; [exact (bytes_at_normalize rsegs mem _ _ HRO CB16)|].
      split; [exact (bytes_at_normalize rsegs mem _ _ HRO CB20)|].
      split; [rewrite CEe; Z.div_mod_to_equations; lia | left; lia].
    - intros _ HP0. destruct (CS HP0) as (HCS & HN). split; [exact (bytes_at_normalize rsegs mem _ _ HRO HCS)|].
      split; [exact HN|]. left. pose proof (HCL HP0). lia.
    - intros _. split; [exact C3n|]. split; [apply Tac_si.nzb_notin, Tac_si.nzb_EXP_DP, Wk|].
      left. unfold n_ld in F3. lia.
    - exact (proj1 (Frame.stk_split rsegs (normalize rsegs mem) (g_S g - 65536) (g_S g - 384) (g_S g) HSTK0
        ltac:(lia))). }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
    -> & MU & WM & MI' & STK').
  rewrite (MState.unsigned_lit (g_S g - 384)) in MU, STK' by lia. unfold REAC_BOX_CATALOGUE_DEFECT_FRAME in MU.
  rewrite (MState.ret_pc_even 0x13ebc) by (lia || reflexivity).
  assert (STK2 : Frame.stk rsegs m' (g_S g - 65536) (g_S g)).
  { apply (Frame.stk_merge rsegs m' (g_S g - 65536) (g_S g - 384) (g_S g) STK'); [|lia].
    apply (Frame.stk_transport_disjoint rsegs _ (normalize rsegs mem) m' _ _
      (proj2 (Frame.stk_split rsegs (normalize rsegs mem) (g_S g - 65536) (g_S g - 384) (g_S g) HSTK0 ltac:(lia)))
      MU WM). cbn. lia. }
  assert (FW : Forall (fun iv => g_S g - 65536 <= fst iv /\ snd iv <= g_S g - 104) [(g_S g - 384 - 16, g_S g - 384)])
    by (repeat (apply Forall_cons; [cbn [fst snd]; split; lia|]); apply Forall_nil).
  apply (fin_mem g mem regs 0x13ebc _ _ m' (munch_SWIN g _ _ _ MU FW) WM STK2);
    [rewrite E2; reflexivity | reflexivity | reflexivity |].
  intros R' m'' HG HREL. cbv beta.
  assert (KMm : KM _ mem m'') by exact (KM_of _ mem m' m'' HRO MU HREL).
  assert (HO' : OUTS g nm tk dp m'')
    by exact (OUTS_keep B APIf ra empty FF g _ nm tk dp L A regs mem md m' m'' HFR HPM (munch_SWIN g _ _ _ MU FW)
      HREL HO).
  split; [|split; [|split; [|exists (catI r), (catO r), (catP r), (catS r)]]].
  - apply (IRc_keep g nm tk dp regs mem R' m'' _ HIc KMm HO'); try (cbn; unfold spk, fsp, SLOT_FRAME, n_ld in *; lia);
      kr HG.
  - kr HG.
  - rg HG.
  - split; [|split; [|split]].
    + apply (cat_entry_keep _ mem m'' _ _ _ _ _ KMm HCE); try (cbn; unfold cat_row, CAT, CAT_ROW in *; lia).
      intros HP0. pose proof (HCL HP0). unfold zlen. cbn [disjoint_from]. lia.
    + rewrite HG. try greg2. first [reflexivity | f_equal; lia].
    + rewrite HG. try greg2. rewrite CEe. unfold r, CAT_N. first [reflexivity | f_equal; lia].
    + rewrite HG. try greg2. reflexivity.
Qed.

End J01.
