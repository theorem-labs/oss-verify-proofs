From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import ReacDecodeLib SlotLoops SlotDown SlotDownB
  SlotUp reac_frame_inspect_c reac_decode_c reac_upstream_channels_c reac_upstream_decode_c check_braid_c
  reac_upstream_decode fd_up_q.
Import ListNotations.
Open Scope Z_scope.

Lemma braid_map_up : forall m out frame fr nch ns,
  bytes_at rsegs m out (braid_out fr nch ns) -> bytes_at rsegs m frame fr ->
  50 + 3 * nch * ns <= Z.of_nat (length fr) -> 0 < nch -> nch mod 2 = 0 -> 0 < ns ->
  braid_map m (frame + 50) out nch ns.
Proof.
  intros m out frame fr nch ns HB HF HL Hnch Hev Hns ch s j Hch Hs Hj.
  exists (nth (Z.to_nat (50 + braid_pos s ch nch j)) fr (Z_to_bv 8 0)).
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  assert (ch - ch mod 2 <= nch - 2) by (Z.div_mod_to_equations; lia).
  assert (s * nch <= (ns - 1) * nch) by nia.
  assert (ch * ns <= (nch - 1) * ns) by nia.
  assert (BP : 0 <= braid_pos s ch nch j <= 3 * nch * ns - 1).
  { rewrite braid_pos_lin' by lia. destruct (Z.eqb_spec j 0); destruct (Z.eqb_spec j 1); nia. }
  pose proof (bytes_at_bound _ _ _ _ HB) as BB. unfold braid_out in BB. rewrite length_mapseq, Z2Nat.id in BB by nia.
  split.
  - destruct HB as (_ & _ & HB3).
    replace (out + 3 * (ch * ns + s) + j) with (out + Z.of_nat (Z.to_nat (3 * (ch * ns + s) + j))) by nia.
    unfold mrd in *. rewrite HB3 by (unfold braid_out; rewrite length_mapseq; nia).
    unfold braid_out. rewrite nth_error_mapseq by nia. cbn [Nat.add].
    rewrite Z2Nat.id by nia. rewrite braid_byte_at' by lia. reflexivity.
  - destruct HF as (_ & _ & HF3).
    replace (frame + 50 + 3 * (s * nch + 2 * (ch / 2)) + braid_off ch j)
      with (frame + Z.of_nat (Z.to_nat (50 + braid_pos s ch nch j))) by (rewrite Z2Nat.id by lia; rewrite braid_pos_off by lia; lia).
    rewrite HF3 by lia. apply nth_error_nth'. lia.
Qed.

Lemma up_ok_facts : forall raw out len bs, 0 <= len < 2 ^ 26 -> up_ok raw out len bs = true ->
  2 <= upstream_result len <= 40 /\ upstream_result len mod 2 = 0 /\ len = 52 + 36 * upstream_result len /\
  up_olen len = 36 * upstream_result len /\ up_nch len = upstream_result len.
Proof.
  intros raw out len bs HL OK. rewrite up_ok_true in OK. destruct OK as (_ & _ & U3 & _).
  apply up_nch_pos in U3. destruct U3 as (V1 & V2 & V3 & V4 & V5).
  assert (UR : upstream_result len = (len - 52) / 36).
  { rewrite (upstream_result_q len) by lia.
    assert (2 <= (len - 52) / 36) by (apply Z.div_le_lower_bound; lia).
    rewrite (proj2 (Z.leb_le 2 _)), (proj2 (Z.leb_le _ 40)), (proj2 (Z.eqb_eq _ 0)) by lia. reflexivity. }
  assert (2 <= (len - 52) / 36) by (apply Z.div_le_lower_bound; lia).
  rewrite UR. split; [lia|]. split; [exact V3|]. split; [Z.div_mod_to_equations; lia|].
  split; [unfold up_olen; rewrite UR, (proj2 (Z.ltb_lt 0 _)) by lia; reflexivity | exact V5].
Qed.

Section UE.
Context (IUC : reac_upstream_channels_contract) (ICB : check_braid_contract).

Lemma stU1 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (Sp len frame : Z),
  x2 = Z_to_bv 64 Sp -> x8 = Z_to_bv 64 (frame + 50) -> x25 = Z_to_bv 64 len -> x26 = Z_to_bv 64 frame ->
  0 <= len < 2 ^ 26 -> mem_inv rsegs m ->
  evt rsegs (q_umalloc F fc x3 x4 m Sp len frame)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x130fc) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m Sp len frame E2 E8 E25 E26 HLB MI.
  subst x2 x8 x25 x26.
  eapply (seg_UA IUC); [exact HLB | exact MI |].
  intros y11 y12 y13. apply evt_done. unfold q_umalloc. eexists. split; [reflexivity|].
  repeat (split; [reflexivity|]). reflexivity.
Qed.

Lemma stU3 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (Sp len frame out lo : Z) (fr : list byte),
  x2 = Z_to_bv 64 Sp -> x8 = Z_to_bv 64 (frame + 50) -> x19 = Z_to_bv 64 (upstream_result len) ->
  x20 = Z_to_bv 64 out -> x25 = Z_to_bv 64 len -> x26 = Z_to_bv 64 frame ->
  0 <= len < 2 ^ 26 -> Z.of_nat (length fr) = len -> 0 < out -> out + up_olen len <= lo -> 0 < frame ->
  frame + len + 1500 <= lo -> lo + 4096 <= Sp -> Sp < 2 ^ 63 ->
  up_ok frame out len fr = true ->
  bytes_at rsegs m out (braid_out fr (upstream_result len) 12) -> bytes_at rsegs m frame fr -> stk rsegs m lo Sp ->
  evt rsegs (q_ufree F fc x3 x4 m Sp len frame out lo)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13290) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m Sp len frame out lo fr E2 E8 E19 E20 E25 E26 HLB HLEN HOP DOS HFP DFS LO HSp OK HB HFR ST.
  subst x2 x8 x19 x20 x25 x26.
  destruct (up_ok_facts frame out len fr HLB OK) as (N1 & N2 & N3 & N4 & N5).
  set (nch := upstream_result len) in *.
  assert (U : bv_unsigned (Z_to_bv 64 Sp) = Sp) by (apply unsigned_lit; lia).
  do 5 step.
  eapply evt_cut.
  { eapply (ICB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m (frame + 50) out nch 12 lo).
    all: unfold CHECK_BRAID_FRAME; rewrite ?U; try lia; try exact ST.
    apply (braid_map_up m out frame fr); [exact HB | exact HFR | lia | lia | exact N2 | lia]. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'
    & -> & MU & WM & ST').
  replace (ret_pc (Z_to_bv 64 0x132a4)) with (Z_to_bv 64 0x132a4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  unfold CHECK_BRAID_FRAME in MU. rewrite U in MU.
  do 2 step.
  apply evt_done. unfold q_ufree. eexists. exists m'. split; [reflexivity|].
  repeat (split; [reflexivity|]).
  split; [|exact WM].
  eapply munch_weaken; [|exact MU]. intros x. cbn [outside]. intros (H1 & H2 & _).
  repeat split; try exact I; lia.
Qed.

End UE.
