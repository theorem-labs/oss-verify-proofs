From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import ReacDecodeLib SlotLoops SlotDown SlotDownB
  SlotDownT SlotCmp reac_frame_inspect_c reac_frame_counter_c memset_c reac_decode_c reac_decode_plain_le_c
  bcmp_c check_braid_c fd_down_evt.
Import ListNotations.
Open Scope Z_scope.

Definition q_malloc1 (F : bvmap 5 word) (fc : bv 32) (gp tp : word) (m0 : word -> option byte)
    (Sp mode nch ns len frame lo : Z) (fr junk8 : list byte) (ms : machine_state) : Prop :=
  exists R m', ms = MS R F (Z_to_bv 64 0x147c4) fc None m' (seg_rom rsegs) /\
    reg_get R 1 = Z_to_bv 64 0x12eb4 /\ reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\
    reg_get R 10 = Z_to_bv 64 (fd_olen nch ns) /\ reg_get R 18 = Z_to_bv 64 mode /\ reg_get R 20 = Z_to_bv 64 ns /\
    reg_get R 22 = Z_to_bv 64 (fd_olen nch ns) /\ reg_get R 23 = Z_to_bv 64 (fd_fits nch ns) /\
    reg_get R 25 = Z_to_bv 64 len /\ reg_get R 26 = Z_to_bv 64 frame /\
    munch [(Sp + 32, Sp + 40)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\
    rw_cells rsegs m' (Sp + 32) [C8 (Z_to_bv 64 nch)] /\ rw_cells rsegs m' (Sp + 8) [CB 24 junk8] /\
    bytes_at rsegs m' (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)) /\ bytes_at rsegs m' frame fr /\
    stk rsegs m' lo Sp.

Definition q_free (F : bvmap 5 word) (fc : bv 32) (gp tp : word) (m0 : word -> option byte)
    (Sp len frame out olen lo : Z) (fr : list byte) (ms : machine_state) : Prop :=
  exists R m', ms = MS R F (Z_to_bv 64 0x14684) fc None m' (seg_rom rsegs) /\
    reg_get R 1 = Z_to_bv 64 0x130fc /\ reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\
    reg_get R 8 = Z_to_bv 64 (frame + 50) /\ reg_get R 10 = Z_to_bv 64 out /\
    reg_get R 25 = Z_to_bv 64 len /\ reg_get R 26 = Z_to_bv 64 frame /\
    munch [(lo, Sp + 32); (out, out + olen)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\
    bytes_at rsegs m' frame fr /\ stk rsegs m' lo Sp.

Definition q_crt (F : bvmap 5 word) (fc : bv 32) (gp tp : word) (m0 : word -> option byte)
    (Sp mode nch ns len frame out lo : Z) (fr junk8 : list byte) (ms : machine_state) : Prop :=
  exists R m', ms = MS R F (Z_to_bv 64 0x132f8) fc None m' (seg_rom rsegs) /\
    reg_get R 1 = Z_to_bv 64 0x12fd0 /\ reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\
    reg_get R 10 = Z_to_bv 64 (frame + 50) /\ reg_get R 11 = Z_to_bv 64 out /\ reg_get R 12 = Z_to_bv 64 nch /\
    reg_get R 13 = Z_to_bv 64 ns /\ reg_get R 18 = Z_to_bv 64 mode /\ reg_get R 19 = Z_to_bv 64 out /\
    reg_get R 20 = Z_to_bv 64 ns /\ reg_get R 22 = Z_to_bv 64 (fd_olen nch ns) /\
    reg_get R 23 = Z_to_bv 64 (pokz len fr nch ns) /\ reg_get R 25 = Z_to_bv 64 len /\
    reg_get R 26 = Z_to_bv 64 frame /\
    decode_ok len fr nch ns = true /\ ns <= 12 /\
    munch [(lo, Sp + 32); (out, out + fd_olen nch ns)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\
    stk rsegs m' lo Sp /\ bytes_at rsegs m' frame fr /\
    bytes_at rsegs m' (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)) /\
    rw_cells rsegs m' (Sp + 32) [C8 (Z_to_bv 64 nch)] /\ rw_cells rsegs m' (Sp + 8) [CB 24 junk8] /\
    bytes_at rsegs m' out (braid_out fr nch ns) /\ wr_at rsegs m' out (fd_olen nch ns).

Ltac side' := lazymatch goal with |- forall _, _ => fail | |- _ => first [eassumption | lia | (left; lia) | (right; lia)] end.

Section ST.
Context (IHI : reac_frame_inspect_contract) (IHC : reac_frame_counter_contract) (IMS : memset_contract)
  (IDE : reac_decode_contract) (ICB : check_braid_contract) (IPL : reac_decode_plain_le_contract)
  (BC : bcmp_contract).

Lemma st1 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (Sp mode nch ns len frame lo : Z) (fr junk junk8 : list byte),
  x2 = Z_to_bv 64 Sp -> x18 = Z_to_bv 64 mode -> x25 = Z_to_bv 64 len -> x26 = Z_to_bv 64 frame ->
  0 <= Sp < 2 ^ 63 -> -128 <= nch <= 127 -> -128 <= ns <= 127 -> Z.of_nat (length fr) = len ->
  bytes_at rsegs m (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)) ->
  rw_cells rsegs m (Sp + 32) [CB 8 junk] -> rw_cells rsegs m (Sp + 8) [CB 24 junk8] ->
  bytes_at rsegs m frame fr -> stk rsegs m lo Sp -> mem_inv rsegs m ->
  (mode + 12 <= Sp + 32 \/ Sp + 40 <= mode + 4) -> frame + len <= lo -> lo <= Sp ->
  evt rsegs (q_malloc1 F fc x3 x4 m Sp mode nch ns len frame lo fr junk8)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x12e5c) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m Sp mode nch ns len frame lo fr junk junk8 E2 E18 E25 E26 HSp Hnch Hns HLEN HM HS HS8 HFR ST MI
    DMS DFL DLO.
  subst x2 x18 x25 x26.
  assert (U : bv_unsigned (Z_to_bv 64 Sp) = Sp) by (apply unsigned_lit; lia).
  pose proof (bytes_at_bound _ _ _ _ HM) as HMB. rewrite length_app, !length_le4 in HMB.
  eapply seg_DA with (junk := junk). all: try rewrite U. all: try side'. all: try side'.
  intros y10 y11 y20 y22 y23 m' E10 E20 E22 E23 HS' MU WM HM' MI'.
  try rewrite U in HS', MU.
  apply wv in E10. apply wv in E22. apply wv in E23. subst y10 y20 y22 y23.
  apply evt_done. unfold q_malloc1. eexists. exists m'. split; [reflexivity|].
  repeat (split; [reflexivity|]).
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact HS'|].
  split.
  { eapply rw_cells_transport; [exact HS8 | exact MU | exact WM |]. cbn [disjoint_from cells_size csize].
    split; [lia | exact I]. }
  split; [exact HM'|].
  split.
  { eapply bytes_at_transport; [exact HFR | exact MU |]. cbn [disjoint_from]. split; [lia | exact I]. }
  eapply stk_transport_disjoint; [exact ST | exact MU | exact WM |]. cbn [disjoint_from]. split; [lia | exact I].
Qed.

Lemma st2 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (Sp mode nch ns len frame out lo : Z) (fr junk junk8 : list byte),
  x2 = Z_to_bv 64 Sp -> x10 = Z_to_bv 64 out -> x18 = Z_to_bv 64 mode -> x20 = Z_to_bv 64 ns ->
  x22 = Z_to_bv 64 (fd_olen nch ns) -> x23 = Z_to_bv 64 (fd_fits nch ns) -> x25 = Z_to_bv 64 len ->
  x26 = Z_to_bv 64 frame ->
  0 <= Sp < 2 ^ 63 -> -128 <= nch <= 127 -> -128 <= ns <= 127 -> Z.of_nat (length fr) = len -> 0 <= len < 2 ^ 26 ->
  4096 <= out < 2 ^ 60 -> 4096 <= frame < 2 ^ 60 -> 0 <= mode < 2 ^ 60 -> lo + 4096 <= Sp ->
  (out + fd_olen nch ns <= frame \/ frame + len <= out) -> out + fd_olen nch ns <= lo ->
  (out + fd_olen nch ns <= mode + 4 \/ mode + 12 <= out) -> frame + len + 1500 <= lo ->
  (mode + 12 <= lo \/ Sp + 40 <= mode + 4) ->
  bytes_at rsegs m (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)) ->
  rw_cells rsegs m (Sp + 8) [CB 24 junk8] -> rw_cells rsegs m (Sp + 32) [C8 (Z_to_bv 64 nch)] ->
  bytes_at rsegs m frame fr -> rw_cells rsegs m out [CB (Z.to_nat (fd_olen nch ns)) junk] ->
  stk rsegs m lo Sp -> mem_inv rsegs m ->
  evt rsegs (fun ms => q_crt F fc x3 x4 m Sp mode nch ns len frame out lo fr junk8 ms \/
                       q_free F fc x3 x4 m Sp len frame out (fd_olen nch ns) lo fr ms)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x12eb4) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m Sp mode nch ns len frame out lo fr junk junk8 E2 E10 E18 E20 E22 E23 E25 E26 HSp Hnch Hns HLEN HLB
    HOP HFP HMP LO DOF DOS DOM DFS DMS HM HS8 HS HFR HO ST MI.
  subst x2 x10 x18 x20 x22 x23 x25 x26.
  assert (U : bv_unsigned (Z_to_bv 64 Sp) = Sp) by (apply unsigned_lit; lia).
  eapply dn_mid with (junk := junk) (lo := lo) (fr := fr) (junk8 := junk8).
  all: try rewrite U. all: try side'. all: try side'.
  - unfold dn_crt_k, dn_W. rewrite !U.
    intros OK Hns12 y8 y9 u5 u6 u7 u14 u15 u16 u17 u28 u29 u30 u31 m' MU WM MI' ST' HFR' HM' HS' HS8' HB' HW'.
    apply evt_done. left. unfold q_crt. eexists. exists m'. split; [reflexivity|].
    repeat (split; [reflexivity|]).
    repeat (split; [assumption|]). assumption.
  - unfold dn_free_k, dn_W. rewrite !U.
    intros z5 z6 z7 z9 z11 z12 z13 z14 z15 z16 z17 z18 z21 z22 z23 z24 z27 z28 z29 z30 z31 m' MU WM MI' HFR' ST'.
    apply evt_done. right. unfold q_free. eexists. exists m'. split; [reflexivity|].
    repeat (split; [reflexivity|]).
    repeat (split; [assumption|]). assumption.
Qed.

Lemma st3 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (Sp mode nch ns len frame out lo : Z) (fr junk8 : list byte),
  x2 = Z_to_bv 64 Sp -> x18 = Z_to_bv 64 mode -> x19 = Z_to_bv 64 out -> x20 = Z_to_bv 64 ns ->
  x22 = Z_to_bv 64 (fd_olen nch ns) -> x23 = Z_to_bv 64 (pokz len fr nch ns) -> x25 = Z_to_bv 64 len ->
  x26 = Z_to_bv 64 frame ->
  0 <= Sp < 2 ^ 63 -> -128 <= nch <= 127 -> -128 <= ns <= 127 -> Z.of_nat (length fr) = len -> 0 <= len < 2 ^ 26 ->
  4096 <= out < 2 ^ 60 -> 4096 <= frame < 2 ^ 60 -> 0 <= mode < 2 ^ 60 -> lo + 4096 <= Sp ->
  (out + fd_olen nch ns <= frame \/ frame + len <= out) -> out + fd_olen nch ns <= lo ->
  (out + fd_olen nch ns <= mode + 4 \/ mode + 12 <= out) -> frame + len + 1500 <= lo ->
  (mode + 12 <= lo \/ Sp + 40 <= mode + 4) ->
  decode_ok len fr nch ns = true ->
  bytes_at rsegs m (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)) ->
  rw_cells rsegs m (Sp + 8) [CB 24 junk8] -> rw_cells rsegs m (Sp + 32) [C8 (Z_to_bv 64 nch)] ->
  bytes_at rsegs m frame fr -> bytes_at rsegs m out (braid_out fr nch ns) -> wr_at rsegs m out (fd_olen nch ns) ->
  stk rsegs m lo Sp -> mem_inv rsegs m ->
  evt rsegs (q_free F fc x3 x4 m Sp len frame out (fd_olen nch ns) lo fr)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x12fd0) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m Sp mode nch ns len frame out lo fr junk8 E2 E18 E19 E20 E22 E23 E25 E26 HSp Hnch Hns HLEN HLB
    HOP HFP HMP LO DOF DOS DOM DFS DMS OK HM HS8 HS HFR HB HW ST MI.
  subst x2 x18 x19 x20 x22 x23 x25 x26.
  assert (U : bv_unsigned (Z_to_bv 64 Sp) = Sp) by (apply unsigned_lit; lia).
  eapply dn_post with (lo := lo) (fr := fr) (junk8 := junk8).
  all: try rewrite U. all: try side'. all: try side'.
  unfold dn_free_k, dn_W. rewrite !U.
  intros z5 z6 z7 z9 z11 z12 z13 z14 z15 z16 z17 z18 z21 z22 z23 z24 z27 z28 z29 z30 z31 m' MU WM MI' HFR' ST'.
  apply evt_done. unfold q_free. eexists. exists m'. split; [reflexivity|].
  repeat (split; [reflexivity|]).
  repeat (split; [assumption|]). assumption.
Qed.

End ST.
