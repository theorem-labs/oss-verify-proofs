(* The slot LLVMFuzzerTestOneInput, plain image, op_write arm, segment B1, second piece: kernel's return
   (0x13fc4, cut c1b1_13fc4) to the entry of model_write (0x15c50, cut c1b1_15c50).
   0x13fc4 lw a0, 0x20c(s1); 0x13fc8 sw a0, 0(s0); 0x13fcc lw a0, 0x210(s1); 0x13fd0 sw zero, 8(s0);
   0x13fd4 sw a0, 4(s0); 0x13fd8 sw zero, 0(s10); 0x13fdc lw s4, 0x218(s1); 0x13fe0 ld a0, 0x38(sp);
   0x13fe4 sw zero, 0x2a8(a0); 0x13fe8 mv a0, s0; 0x13fec mv a1, s2; 0x13ff0 mv a2, s5;
   0x13ff4 jal model_write (0x15c50, ra 0x13ff8).
   s1 = g_nl + 0x40000, s0 = md, s10 = md + MD_N_REQ, the frame cell sp + 0x38 = g_nl + 0x42000. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem kernel_c model_write_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC1Defs LC1Call LC1B1Lib LC1B1GM.
Local Open Scope Z_scope.

Lemma c1b1_seg_G : forall E i gp own m0 ms, lenv_ok E -> c1b1_13fc4 E i gp own m0 ms ->
  evt rsegs (c1b1_15c50 E i gp own m0) ms.
Proof.
  intros E i gp own m0 ms HE H.
  destruct H as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s4 & t3 & t4 & t5 & t6 & F & fc &
    mk & P & N & kbs & mbs & gbs & nb & s & t & sl & -> & FRM & Hi & Hnb & HN & HL & NX & HC & HO & HOS & HA & MI &
    TM & ST & HF).
  destruct (c1b1_lenv E HE) as (S1 & S2 & M1 & M2 & M3 & _).
  destruct (c1b1_lh_split _ _ _ _ _ _ _ _ HL)
    as ((FL & _) & _ & NK & NW & _ & _ & _ & _ & _ & _ & MD & _).
  destruct FL as [j0 FL].
  destruct NW as (_ & _ & _ & _ & _ & W6 & _ & _ & _ & W10 & W11 & _).
  destruct NK as [NKu NKl]. destruct MD as [MDu MDl]. unfold NK_SIZE in NKl. unfold MD_SIZE in MDl.
  (* the cells the code reads and writes *)
  assert (RD1 : rw_cells rsegs mk 466316 [C4 (Z_to_bv 64 (nk_socket_errno kbs)); C4 (Z_to_bv 64 (nk_send_errno kbs));
                                          C4 (Z_to_bv 64 (nk_open kbs)); C4 (Z_to_bv 64 (nk_opened kbs))]).
  { change (rw_cells rsegs mk 466316 (c1b1_u32c kbs 262668 4)).
    eapply c1b1_u8_u32c; [exact NKu | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | reflexivity]. }
  assert (RD2 : rw_cells rsegs mk 474664 [C4 (Z_to_bv 64 (nk_n_sent kbs))]).
  { change (rw_cells rsegs mk 474664 (c1b1_u32c kbs 271016 1)).
    eapply c1b1_u8_u32c; [exact NKu | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | reflexivity]. }
  assert (MD1 : rw_cells rsegs mk (e_md E) [C4 (Z_to_bv 64 (md_socket_errno mbs)); C4 (Z_to_bv 64 (md_send_errno mbs));
                                            C4 (Z_to_bv 64 (md_next mbs))]).
  { change (rw_cells rsegs mk (e_md E) (c1b1_u32c mbs 0 3)).
    eapply c1b1_u8_u32c; [exact MDu | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia]. }
  assert (MD2 : rw_cells rsegs mk (e_md E + 8336) [C4 (Z_to_bv 64 (md_n_req mbs))]).
  { change (rw_cells rsegs mk (e_md E + 8336) (c1b1_u32c mbs 8336 1)).
    eapply c1b1_u8_u32c; [exact MDu | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | reflexivity]. }
  unfold c1b1_lo in FL. change (wz GNL42) with (Z_to_bv 64 473984) in FL.
  (* the facts the walk tactics must leave alone *)
  assert (KP : c1b1_keep (lh_mem E i P N kbs mbs gbs mk /\
                 bytes_at rsegs mk (e_S E - SLOT_FRAME + FO_B256) (le8 (wz own)) /\ (own = 0 \/ own = s) /\
                 al_ok E mk s t sl /\ MemNorm.task_mem rsegs mk /\ seg_fp (e_S E) (c1_hp E) m0 mk))
    by exact (conj HL (conj HO (conj HOS (conj HA (conj TM HF))))).
  clear HL HO HOS HA TM HF NKu MDu.
  pose proof (munch_refl [(e_md E, e_md E + 12); (e_md E + 8336, e_md E + 8336 + 4); (474664, 474664 + 4)] mk) as MU.
  pose proof (wmono_refl rsegs mk) as WM.
  unfold wz, GNL40, A_G_NL, MD_N_REQ, SLOT_FRAME, FO_P in *.
  step. rewrite (c1b1_sx32_wz (nk_socket_errno kbs)) by lia.
  step.
  step. rewrite (c1b1_sx32_wz (nk_send_errno kbs)) by lia.
  step.
  step.
  step.
  step. rewrite (c1b1_sx32_wz (nk_opened kbs)) by lia.
  step.
  step.
  step. step. step.
  step.
  unfold c1b1_keep in KP. destruct KP as (HL & HO & HOS & HA & TM & HF).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (c1b1_begin_mem E i P N kbs mbs gbs mk mm own s t sl m0 _ _ _ HE HL NX HC HO HA TM HF MU WM
                MD1 MD2 RD2 ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
      as (kbs' & mbs' & HL' & NS & ER & EK & EOP & HO' & HA' & TM' & HF');
    apply evt_done; unfold c1b1_15c50;
    exists t0, t1, t2, a3, a4, a5, a6, a7, s3, t3, t4, t5, t6, F, fc, mm, P, N, kbs', mbs', gbs, nb, s, t, sl
  end.
  rewrite EOP.
  split; [reflexivity|].
  refine (conj FRM (conj Hi (conj Hnb (conj HN (conj HL' (conj NS (conj ER (conj EK (conj HC (conj HO'
    (conj HOS (conj HA' (conj MI (conj TM' (conj ST HF'))))))))))))))).
Qed.
