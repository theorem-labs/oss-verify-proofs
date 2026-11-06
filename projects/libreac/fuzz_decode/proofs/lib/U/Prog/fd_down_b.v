From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import ReacDecodeLib reac_frame_inspect_c
  reac_decode_c reac_decode_plain_le_c bcmp_c memset_c check_braid_c fd_down_q fd_down_b2.
Import ListNotations.
Open Scope Z_scope.

Ltac side_b := lazymatch goal with |- forall _, _ => fail | |- _ => first [eassumption | lia | (left; lia) | (right; lia)] end.

Section ST.
Context (ICB : check_braid_contract) (IMS : memset_contract) (IPL : reac_decode_plain_le_contract)
  (BC : bcmp_contract).

Lemma ud_st2b : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (Sp mode nch ns len frame out lo : Z) (fr junk : list byte),
  x2 = Z_to_bv 64 Sp -> x9 = Z_to_bv 64 len -> x10 = Z_to_bv 64 (dres len fr nch ns) -> x19 = Z_to_bv 64 mode ->
  x22 = Z_to_bv 64 out -> x23 = Z_to_bv 64 (fd_olen nch ns) -> x24 = Z_to_bv 64 (pokz len fr nch ns) ->
  x25 = Z_to_bv 64 frame ->
  0 <= Sp < 2 ^ 63 -> -128 <= nch <= 127 -> -128 <= ns <= 127 -> Z.of_nat (length fr) = len -> 0 <= len < 2 ^ 26 ->
  4096 <= out < 2 ^ 60 -> 4096 <= frame < 2 ^ 60 -> 0 <= mode < 2 ^ 60 -> mode <> 0 /\ mode mod 4 = 0 ->
  lo + 4096 <= Sp ->
  (out + fd_olen nch ns <= frame \/ frame + len <= out) -> out + fd_olen nch ns <= lo ->
  (out + fd_olen nch ns <= mode + 4 \/ mode + 12 <= out) -> frame + len + 1500 <= lo ->
  (mode + 12 <= lo \/ Sp + 56 <= mode + 4) ->
  bytes_at rsegs m (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)) -> dcells m Sp len frame nch ns junk ->
  bytes_at rsegs m frame fr -> bytes_at rsegs m out (dout len fr nch ns) -> wr_at rsegs m out (fd_olen nch ns) ->
  stk rsegs m lo Sp -> mem_inv rsegs m ->
  evt rsegs (fun ms => q_dcrt F fc x3 x4 m Sp mode nch ns len frame out lo fr ms \/
                       q_dfree F fc x3 x4 m Sp len frame out (fd_olen nch ns) lo fr ms)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x130ec) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m Sp mode nch ns len frame out lo fr junk E2 E9 E10 E19 E22 E23 E24 E25 HSp Hnch Hns HLEN HLB
    HOP HFP HMP HMA LO DOF DOS DOM DFS DMS HM HS HFR HB HW ST MI.
  subst x2 x9 x10 x19 x22 x23 x24 x25.
  assert (U : bv_unsigned (Z_to_bv 64 Sp) = Sp) by (apply unsigned_lit; lia).
  unfold dcells in HS.
  eapply (dt_head ICB IMS IPL BC) with (sp := Z_to_bv 64 Sp) (lo := lo) (fr := fr) (junk := junk).
  all: try rewrite U. all: try side_b. all: try side_b.
  - unfold dt_crt_k. intros OK H12 u5 u6 u7 u8 u14 u15 u16 u17 u20 u21 u26 u27 u28 u29 u30 u31.
    apply evt_done. left. unfold q_dcrt. eexists. exists m, junk. split; [reflexivity|].
    repeat (split; [reflexivity|]).
    split; [exact OK|]. split; [exact H12|].
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|].
    split; [exact HS|]. split; [exact HM|]. split; [exact HFR|].
    split; [unfold dout in HB; rewrite OK in HB; exact HB | exact HW].
  - unfold dt_free_k, dt_W. rewrite !U.
    intros z5 z6 z7 z9 z11 z12 z13 z14 z15 z16 z17 z19 z20 z21 z22 z23 z24 z26 z27 z28 z29 z30 z31 m' MU WM MI' HFR' ST'.
    apply evt_done. right. unfold q_dfree. eexists. exists m'. split; [reflexivity|].
    repeat (split; [reflexivity|]).
    repeat (split; [assumption|]). assumption.
Qed.

Lemma ud_st3 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (Sp mode nch ns len frame out lo : Z) (fr junk : list byte),
  x2 = Z_to_bv 64 Sp -> x9 = Z_to_bv 64 len -> x18 = Z_to_bv 64 (frame + 50) -> x19 = Z_to_bv 64 mode ->
  x22 = Z_to_bv 64 out -> x23 = Z_to_bv 64 (fd_olen nch ns) -> x24 = Z_to_bv 64 (pokz len fr nch ns) ->
  x25 = Z_to_bv 64 frame ->
  0 <= Sp < 2 ^ 63 -> -128 <= nch <= 127 -> -128 <= ns <= 127 -> Z.of_nat (length fr) = len -> 0 <= len < 2 ^ 26 ->
  4096 <= out < 2 ^ 60 -> 4096 <= frame < 2 ^ 60 -> 0 <= mode < 2 ^ 60 -> mode <> 0 /\ mode mod 4 = 0 ->
  lo + 4096 <= Sp ->
  (out + fd_olen nch ns <= frame \/ frame + len <= out) -> out + fd_olen nch ns <= lo ->
  (out + fd_olen nch ns <= mode + 4 \/ mode + 12 <= out) -> frame + len + 1500 <= lo ->
  (mode + 12 <= lo \/ Sp + 56 <= mode + 4) ->
  decode_ok len fr nch ns = true ->
  bytes_at rsegs m (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)) -> dcells m Sp len frame nch ns junk ->
  bytes_at rsegs m frame fr -> bytes_at rsegs m out (braid_out fr nch ns) -> wr_at rsegs m out (fd_olen nch ns) ->
  stk rsegs m lo Sp -> mem_inv rsegs m ->
  evt rsegs (q_dfree F fc x3 x4 m Sp len frame out (fd_olen nch ns) lo fr)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13124) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m Sp mode nch ns len frame out lo fr junk E2 E9 E18 E19 E22 E23 E24 E25 HSp Hnch Hns HLEN HLB
    HOP HFP HMP HMA LO DOF DOS DOM DFS DMS OK HM HS HFR HB HW ST MI.
  subst x2 x9 x18 x19 x22 x23 x24 x25.
  assert (U : bv_unsigned (Z_to_bv 64 Sp) = Sp) by (apply unsigned_lit; lia).
  unfold dcells in HS.
  eapply (dt_b0 ICB IMS IPL BC) with (sp := Z_to_bv 64 Sp) (lo := lo) (fr := fr) (junk := junk).
  all: try rewrite U. all: try side_b. all: try side_b.
  unfold dt_free_k, dt_W. rewrite !U.
  intros z5 z6 z7 z9 z11 z12 z13 z14 z15 z16 z17 z19 z20 z21 z22 z23 z24 z26 z27 z28 z29 z30 z31 m' MU WM MI' HFR' ST'.
  apply evt_done. unfold q_dfree. eexists. exists m'. split; [reflexivity|].
  repeat (split; [reflexivity|]).
  repeat (split; [assumption|]). assumption.
Qed.

End ST.
