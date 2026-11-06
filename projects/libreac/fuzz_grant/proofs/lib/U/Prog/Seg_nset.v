From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Tac Bytes ZBridge Step Arr Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import HeadampModel SlotNeeds_c LLVMFuzzerTestOneInput_c GrantSlotPlan SlotBridge SegSetModel.
Import ListNotations.
Open Scope Z_scope.

Theorem seg_nset_holds : seg_nset.
Proof.
  unfold seg_nset. intros x t ms H.
  apply evt_canon; [eqv_inv_tac|].
  destruct H as (((Hpc & HF & Hfc & Hrv & Hsvc & Hro & Hgp & Htp & HPL & HST & HMI & Hp0 & Hpn & Hpd & Hrow & Hrs & Hrp) &
                  Hsp & HSV & HS16 & Hsv12 & HS63) &
                 Hn & Hs0 & (Hs27 & Hs25) & HSL & (HTb & HT16 & HTl & HT) & (Hwl & Hstl & HWS & HSTA)).
  unfold slots in HSL.
  pose proof HTb as HTb'. unfold blk in HTb'.
  rewrite canon_rg by exact Hsvc.
  rewrite Hpc, HF, Hfc, Hrv, Hro, Hs27, Hs25, Hs0, Hsp.
  assert (ESPL : SPL x = x_S x - 608) by reflexivity.
  assert (ELS : LLVM_STACK = 8800) by reflexivity.
  assert (ELR : length CTRL_HEADAMP_BYTES = 24%nat) by reflexivity.
  rewrite ELS in Hrs.
  assert (HSlo : 8800 <= x_S x) by (destruct HST as (H0 & _); rewrite ELS in H0; lia).
  assert (Exn : x_n x = Z.of_nat (length (x_pl x))) by reflexivity.
  assert (ESZ : cells_size (map C8 (rev (x_sv x) ++ [x_ra x])) = 104%nat) by (apply saved_size; exact Hsv12).
  pose proof (header_le (x_pl x)) as Hh.
  unfold hd in *.
  set (h := h_pos (header (x_pl x))) in *.
  set (m0 := ms_mem ms) in *.
  assert (MU : munch [(x_S x - 8800, x_S x)] m0 m0) by apply munch_refl.
  assert (WM : wmono rsegs m0 m0) by apply wmono_refl.
  unfold w64, PC_SET0.
  zstep.
  if_cases HC1; zify_cond HC1.
  - assert (Eh : h = length (x_pl x)) by lia.
    assert (Ens : nset (x_pl x) = 0)
      by (unfold nset; change (h_pos (header (x_pl x))) with h; rewrite rd8_ge by lia; reflexivity).
    assert (Epe : pos_end (x_pl x) = h).
    { unfold pos_end. rewrite Ens. change (Z.to_nat 0) with O. unfold cells_upto, pos_cells. cbn [cells snd].
      change (h_pos (header (x_pl x))) with h. rewrite rd8_ge by lia. reflexivity. }
    assert (ETe : tables_end (x_pl x) = (T0, Z144, Z144)) by (unfold tables_end; rewrite Ens; reflexivity).
    apply evt_done. split; [split; [exact MU | exact WM]|].
    left. split; [exact Ens|].
    unfold At_unset0, T_end, ws_end, st_end. rewrite Epe, ETe. cbn [fst snd].
    pose proof I1_T0. pose proof Hrel_T0.
    fin_at.
  - assert (Hlt : (h < length (x_pl x))%nat) by lia.
    destruct (CB_bytes _ _ _ _ HPL) as (HPB & _ & _).
    assert (HR : ov_read_bytes rsegs m0 (wa (x_p x + Z.of_nat h)) 1 = Some [nth h (x_pl x) (Z_to_bv 8 0)]).
    { rewrite (bytes_at_read rsegs m0 (x_p x) (x_pl x) (Z.of_nat h) 1 HPB) by lia.
      rewrite Nat2Z.id. rewrite (firstn1_skipn_nth (x_pl x) h (Z_to_bv 8 0)) by lia. reflexivity. }
    pose proof (bv_unsigned_in_range 8 (nth h (x_pl x) (Z_to_bv 8 0))) as Hb8.
    replace (bv_modulus 8) with 256 in Hb8 by reflexivity.
    assert (Ens : nset (x_pl x) = bv_unsigned (nth h (x_pl x) (Z_to_bv 8 0)))
      by (unfold nset; change (h_pos (header (x_pl x))) with h; rewrite rd8_lt by lia; reflexivity).
    assert (Epc : pos_cells (x_pl x) = S h)
      by (unfold pos_cells; change (h_pos (header (x_pl x))) with h; rewrite rd8_lt by lia; reflexivity).
    zstep. zstep. zstep. brx.
    zstep. zstep. zstep.
    if_cases HC2; zify_cond HC2.
    + assert (Ens0 : nset (x_pl x) = 0) by lia.
      assert (Epe : pos_end (x_pl x) = S h)
        by (unfold pos_end; rewrite Ens0; change (Z.to_nat 0) with O; unfold cells_upto; cbn [cells snd]; exact Epc).
      assert (ETe : tables_end (x_pl x) = (T0, Z144, Z144)) by (unfold tables_end; rewrite Ens0; reflexivity).
      zstep.
      apply evt_done. split; [split; [exact MU | exact WM]|].
      left. split; [exact Ens0|].
      unfold At_unset0, T_end, ws_end, st_end. rewrite Epe, ETe. cbn [fst snd].
      pose proof I1_T0. pose proof Hrel_T0.
      fin_at.
    + destruct (stk_cell m0 _ _ (SPL x + 40) 8 HST ltac:(lia) ltac:(lia)) as [junk40 C40].
      destruct (stk_cell m0 _ _ (SPL x + 48) 8 HST ltac:(lia) ltac:(lia)) as [junk48 C48].
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      rewrite wnot_lxor in * by lia.
      apply evt_done. split; [split; [exact MU | exact WM]|].
      right. split; [lia|].
      unfold At_set. rewrite tables_at_0.
      change (snd (cells_upto (x_pl x) 0)) with (pos_cells (x_pl x)). rewrite Epc, Ens.
      pose proof I1_T0. pose proof Hrel_T0.
      fin_at.
Qed.
