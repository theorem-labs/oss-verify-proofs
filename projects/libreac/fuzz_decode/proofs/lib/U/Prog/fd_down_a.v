From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import ReacDecodeLib reac_frame_inspect_c
  reac_frame_counter_c memset_c reac_decode_c fd_down_q fd_down_a1 fd_down_a2.
Import ListNotations.
Open Scope Z_scope.

Lemma ud_st1 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (Sp mode nch ns len frame lo : Z) (fr junk junk8 : list byte),
  x2 = Z_to_bv 64 Sp -> x9 = Z_to_bv 64 len -> x19 = Z_to_bv 64 mode -> x25 = Z_to_bv 64 frame ->
  0 <= Sp < 2 ^ 63 -> -128 <= nch <= 127 -> -128 <= ns <= 127 -> Z.of_nat (length fr) = len ->
  bytes_at rsegs m (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)) ->
  rw_cells rsegs m (Sp + 40) [CB 16 junk] -> rw_cells rsegs m (Sp + 8) [CB 32 junk8] ->
  bytes_at rsegs m frame fr -> stk rsegs m lo Sp -> mem_inv rsegs m ->
  (mode + 12 <= Sp + 8 \/ Sp + 56 <= mode + 4) -> frame + len <= lo -> lo <= Sp ->
  evt rsegs (q_dmalloc F fc x3 x4 m Sp mode nch ns len frame lo fr junk8)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x12f10) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m Sp mode nch ns len frame lo fr junk junk8 E2 E9 E19 E25 HSp Hnch Hns HLEN HM HS HS8 HFR ST MI
    DMS DFL DLO.
  subst x2 x9 x19 x25.
  pose proof (bytes_at_bound _ _ _ _ HM) as HMB. rewrite length_app, !length_le4 in HMB.
  pose proof (rw_cells_bound _ _ _ _ HS) as HSB. cbn [cells_size csize Nat.add] in HSB.
  pose proof HM as HM0.
  apply bytes_at_app in HM. destruct HM as [HM1 HM2]. rewrite length_le4 in HM2.
  replace (mode + 4 + Z.of_nat 4) with (mode + 8) in HM2 by lia.
  pose proof (rd_all _ _ _ HM1) as HR1. rewrite length_le4 in HR1.
  pose proof (rd_all _ _ _ HM2) as HR2. rewrite length_le4 in HR2.
  pose proof (munch_refl [(Sp + 40, Sp + 56)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  clear HM1 HM2.
  st. rewrite sx32_lit by lia. st. rewrite sx32_lit by lia. clear HR1 HR2.
  st. st. st. st.
  unfold v_slt, c_lts. rewrite !lts0_lit by lia.
  destruct (Z.ltb_spec 0 nch) as [P1|P1]; destruct (Z.ltb_spec 0 ns) as [P2|P2].
  2-4: st; st; st; cnd true; st; cnd false; st; st; st; st;
    apply evt_done; unfold q_dmalloc, fd_olen, fd_fits; eexists; eexists; split; [reflexivity|].
  - st. st. st. cnd false.
    st. st. st. st. st. cnd true.
    st. st. st. st. st. st. st. st. st.
    assert (PB : 0 < nch * ns <= 127 * 127) by nia.
    rewrite (unsigned_lit (nch * ns)) by lia. unfold v_sltiu.
    change (bv_wrap 64 481) with 481. change (bv_wrap 64 1) with 1.
    rewrite (unsigned_lit (ns * nch)) by nia.
    rewrite (unsigned_lit (nch * ns * 2 + nch * ns)) by lia.
    rewrite (proj2 (Z.ltb_ge (nch * ns * 2 + nch * ns) 1)) by lia. cbn iota. usub.
    replace (nch * ns * 2 + nch * ns + 0) with (fd_olen nch ns)
      by (unfold fd_olen; rewrite (proj2 (Z.ltb_lt 0 nch)), (proj2 (Z.ltb_lt 0 ns)) by lia; cbn [andb]; lia).
    replace (if ns * nch <? 481 then Z_to_bv 64 1 else Z_to_bv 64 0) with (Z_to_bv 64 (fd_fits nch ns))
      by (unfold fd_fits; rewrite (proj2 (Z.ltb_lt 0 nch)), (proj2 (Z.ltb_lt 0 ns)) by lia; cbn [andb];
          rewrite (Z.mul_comm ns nch); destruct (nch * ns <? 481); reflexivity).
    apply evt_done. unfold q_dmalloc. eexists. eexists. split; [reflexivity|].
    repeat (split; [first [reflexivity | eassumption]|]). eassumption.
  - rewrite (proj2 (Z.ltb_lt 0 nch) P1), (proj2 (Z.ltb_ge 0 ns) P2). cbn [andb].
    repeat (split; [first [reflexivity | eassumption]|]). eassumption.
  - rewrite (proj2 (Z.ltb_ge 0 nch) P1), (proj2 (Z.ltb_lt 0 ns) P2). cbn [andb].
    repeat (split; [first [reflexivity | eassumption]|]). eassumption.
  - rewrite (proj2 (Z.ltb_ge 0 nch) P1), (proj2 (Z.ltb_ge 0 ns) P2). cbn [andb].
    repeat (split; [first [reflexivity | eassumption]|]). eassumption.
Qed.

Section D2.
Context (IHI : reac_frame_inspect_contract) (IHC : reac_frame_counter_contract) (IMS : memset_contract)
  (IDE : reac_decode_contract).

Lemma ud_st2a : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (Sp mode nch ns len frame out lo : Z) (fr junk junk8 : list byte),
  x2 = Z_to_bv 64 Sp -> x9 = Z_to_bv 64 len -> x10 = Z_to_bv 64 out -> x18 = Z_to_bv 64 (fd_fits nch ns) ->
  x19 = Z_to_bv 64 mode -> x23 = Z_to_bv 64 (fd_olen nch ns) -> x25 = Z_to_bv 64 frame ->
  0 <= Sp < 2 ^ 63 -> -128 <= nch <= 127 -> -128 <= ns <= 127 -> Z.of_nat (length fr) = len -> 0 <= len < 2 ^ 26 ->
  4096 <= out < 2 ^ 60 -> 4096 <= frame < 2 ^ 60 -> 0 <= mode < 2 ^ 60 -> mode <> 0 /\ mode mod 4 = 0 -> lo + 4096 <= Sp ->
  (out + fd_olen nch ns <= frame \/ frame + len <= out) -> out + fd_olen nch ns <= lo ->
  (out + fd_olen nch ns <= mode + 4 \/ mode + 12 <= out) -> frame + len + 1500 <= lo ->
  (mode + 12 <= lo \/ Sp + 56 <= mode + 4) ->
  bytes_at rsegs m (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)) ->
  rw_cells rsegs m (Sp + 8) [CB 32 junk8] -> rw_cells rsegs m (Sp + 40) [C8 (Z_to_bv 64 nch); C8 (Z_to_bv 64 ns)] ->
  bytes_at rsegs m frame fr -> rw_cells rsegs m out [CB (Z.to_nat (fd_olen nch ns)) junk] ->
  stk rsegs m lo Sp -> mem_inv rsegs m ->
  evt rsegs (q_dJ F fc x3 x4 m Sp mode nch ns len frame out lo fr)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x12f74) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m Sp mode nch ns len frame out lo fr junk junk8 E2 E9 E10 E18 E19 E23 E25
    HSp Hnch Hns HLEN HLB HOP HFP HMP HMA LO DOF DOS DOM DFS DMS HM HS8 HS40 HFR HO ST MI.
  subst x2 x9 x10 x18 x19 x23 x25.
  pose proof (bytes_at_bound _ _ _ _ HFR) as HFB. rewrite HLEN in HFB.
  pose proof (bytes_at_bound _ _ _ _ HM) as HMB. rewrite length_app, !length_le4 in HMB.
  pose proof (ud_olen_bounds nch ns Hnch Hns) as OL.
  pose proof (munch_refl [(lo, Sp + 56); (out, out + fd_olen nch ns)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  st. cnd false.
  st. st. st. st. st.
  eapply evt_cut; [eapply IHI with (bs := fr) |].
  { rewrite !unsigned_lit by lia. intros L. split; [lia|]. split; [exact HFR | lia]. }
  intros ms' (a1' & a2' & ->).
  replace (ret_pc (Z_to_bv 64 0x12f8c)) with (Z_to_bv 64 0x12f8c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite (unsigned_lit len) by lia.
  st. st. st.
  eapply ud_segW.
  all: try first [ eassumption | lia ].
  intros y11 y12. eapply ud_segC.
  all: try first [ eassumption | lia ].
  intros y1 y8 y10 y11' y12'. eapply ud_segD.
  all: try first [ eassumption | lia ].
  intros u1 u5 u6 u7 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 m' MU' WM' MI' ST' HFR' HM' HS8' HS40' HB' HW'.
  apply evt_done. unfold q_dJ. do 3 eexists. split; [reflexivity|].
  repeat (split; [reflexivity|]).
  split.
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU']. intros x. cbn [outside].
    intros (H1 & H2 & _). repeat split; try exact I; lia. }
  split; [eapply wmono_trans; [exact WM | exact WM']|].
  split; [exact MI'|]. split; [exact ST'|].
  split.
  { unfold dcells. pose proof (ud_rw_cells_join _ _ _ [C8 (Z_to_bv 64 nch); C8 (Z_to_bv 64 ns)] HS8') as J.
    cbn [cells_size csize Nat.add] in J.
    replace (Sp + 8 + Z.of_nat 32) with (Sp + 40) in J by lia. exact (J HS40'). }
  split; [exact HM'|]. split; [exact HFR'|]. split; [exact HB'|]. exact HW'.
Qed.

End D2.
