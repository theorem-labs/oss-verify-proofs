From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import HeadampModel GrantModel GrantSweepModel SlotNeeds_c LLVMFuzzerTestOneInput_c GrantSlotPlan SlotBridge SegCLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Theorem seg_raw_holds : seg_raw.
Proof.
  unfold seg_raw. intros x t pc ms H.
  apply evt_canon; [apply eqv_and; [apply eqv_kept | apply eqv_At_mallocSW2] |].
  destruct x as [Sx ra gp tp sv p pl F fc].
  unfold At_raw, at_after_admit, body, common, cur5, slots, cslot, table, arrays, SPL, x_n, hd in H.
  cbn [x_S x_ra x_gp x_tp x_sv x_p x_pl x_F x_fc] in H.
  destruct H as ((((Hpc & HF & Hfc & Hrv & Hsvc & Hro & Hgp & Htp & HPL & HST & HMI & Hp0 & Hpn & Hpd & Hrow & Hrs & Hrp) & Hsp & HSV & HS16 & HSVl & HS63) & Hn & Hs0 & Hs9 & HSL & HCS & (HTb & HT16 & HTl & HT) & (HWl & HSTl & HWS & HSTA) & HH & HI) & Hwhich).
  rewrite canon_MS by exact Hsvc. unfold mkR_of.
  rewrite Hpc, HF, Hfc, Hrv, Hro.
  assert (E2 : Sem.reg_get (ms_regs ms) 2 = w64 (Sx - LLVM_FRAME)) by exact Hsp.
  assert (E3 : Sem.reg_get (ms_regs ms) 3 = gp) by exact Hgp.
  assert (E4 : Sem.reg_get (ms_regs ms) 4 = tp) by exact Htp.
  assert (E8 : Sem.reg_get (ms_regs ms) 8 = w64 t) by exact Hs0.
  assert (E25 : Sem.reg_get (ms_regs ms) 25 = w64 (Z.of_nat (length pl) - Z.of_nat (pos_end pl))) by exact Hs9.
  rewrite E2, E3, E4, E8, E25. clear E2 E3 E4 E8 E25 Hsp Hgp Htp Hs0 Hs9.
  destruct Hwhich as [(-> & Hok & Hs21 & _) | (-> & Hok)].
  1: (assert (E21 : Sem.reg_get (ms_regs ms) 21 = w64 (p + Z.of_nat (pos_end pl))) by exact Hs21;
      rewrite E21; clear E21 Hs21).
  all: repeat match goal with |- context [Sem.reg_get (ms_regs ?M) ?k] =>
    let v := fresh "r" in generalize (Sem.reg_get (ms_regs M) k) as v; intro v end.
  all: change (YK11.seg_rom rsegs) with (PropExec.seg_rom rsegs).
  all: unfold kept; cbn [x_S].
  all: revert HPL HST HMI HSV HSL HCS HT HWS HSTA Hrow.
  all: generalize (ms_mem ms) as m0; intros m0 HPL HST HMI HSV HSL HCS HT HWS HSTA Hrow.
  all: assert (HRL : length CTRL_HEADAMP_BYTES = 24%nat) by reflexivity.
  all: clear Hpc HF Hfc Hrv Hsvc Hro.
  all: unfold w64 in *; rewrite ?LLVM_STACK_val, ?LLVM_FRAME_val in *.
  all: pose proof (pos_end_le pl) as PE.
  all: pose proof (rw_cells_CB_bytes _ _ _ _ HPL) as [PB _].
  all: destruct (stk_cells m0 (Sx - 8800) Sx (Sx - 608 + 66) 2 HST ltac:(lia) ltac:(lia)) as [junk RAWC].
  all: pose proof (munch_refl [(Sx - 608 + 66, Sx - 608 + 68)] m0) as MUf.
  all: pose proof (munch_refl [(Sx - 8800, Sx)] m0) as MUc.
  all: pose proof (wmono_refl rsegs m0) as WM.
  all: apply frz_in in HPL, HSV, HSL, HT, HWS, HSTA.
  all: unfold PC_RAW_NOK, PC_FREE_SW1_RET.
  2: stp.
  all: apply frz_in in HCS.
  all: (destruct (Nat.eq_dec (pos_end pl) (length pl)) as [Q0|Q0];
   [replace (Z.of_nat (length pl) - Z.of_nat (pos_end pl)) with 0 by lia
   |destruct (Nat.eq_dec (S (pos_end pl)) (length pl)) as [Q1|Q1];
    [replace (Z.of_nat (length pl) - Z.of_nat (pos_end pl)) with 1 by lia;
     pose proof (bytes_byte_read m0 p pl (pos_end pl) PB ltac:(lia)) as PR0
    |pose proof (bytes_byte_read m0 p pl (pos_end pl) PB ltac:(lia)) as PR0]]).
  all: gz 0x1396c.
  all: try (match goal with
    | PB : bytes_at rsegs ?m ?pp ?pl0, Q1 : S (pos_end ?pl0) <> length ?pl0 |- evt _ _ (MS _ _ (Z_to_bv 64 80212) _ _ _ _) =>
        pose proof (bytes_byte_read m pp pl0 (S (pos_end pl0)) PB ltac:(lia)) as PR1 end; gz 0x1396c).
  all: apply evt_done; split; [split; assumption|].
  all: unfold blk, x_n in HTb; cbn [x_S x_p x_pl] in HTb; rewrite ?LLVM_STACK_val in HTb.
  all: thaw MUf WM.
  all: unfold At_mallocSW2, body, common, cur5, table, arrays, SPL, x_n, hd, pos_raw;
    cbn [x_S x_ra x_gp x_tp x_sv x_p x_pl x_F x_fc ms_pc_val ms_fregs ms_fcsr ms_resv ms_svc_pending ms_rom ms_mem MS].
  all: first [rewrite (raw_rd_0 pl) by lia | rewrite (raw_rd_1 pl) by lia | rewrite (raw_rd_2 pl) by lia];
    cbv beta iota zeta; cbn [snd].
  all: splits.
  all: try fin1.
  all: try (apply rw_cells_two; unfold pbz; rewrite ?Z_to_bv8_unsigned; exact RAWC).
Qed.
