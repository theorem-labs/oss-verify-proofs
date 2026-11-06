(* rule 24: no function proved. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/F10.v (not in this delivery) seg_F10 (the two inline sl_run runs of the segment proof, F10.v (not in this delivery);
     sl_run is lib/B/Prog/Seg/Tac_slot.v:156) at a working branch
     3803efccea0 (blob 2aa249a7d9208fc8227ce2b0b91cf9af939f4888);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: seg_F10_ok_run / seg_F10_ne_run (evtF_evt + rng_all) re-derive the source statements in the lib.Lib
     Exec.evt form; the segment proof states them in the UL engine's Exec.evt form and Tac_slot.sl_run carries
     them to lib.Lib with SmLib.ul_entry, and the two evt definitions are the same (lib/B/Tk/UL/Exec.v:37,
     lib/Lib/Exec.v:109). The stretch 0x821ec -> 0x8226c / 0x82308 has no call, so there is no _pre_F / _post_F
     split. *)

(* The footprint twins of segment F10 (S_F10), 0x821ec (the return point of reac_ctrl_identity_reply) to the two
   exits. Two runs, one per arm of `bne a0,s6` at 0x821f0:
     seg_F10_ok_F  a0 = 1 (reply_ok): falls through to 0x8226c. It reads the three spill words [A+296, A+304)
                   (pn), [A+304, A+312) (pp) and [A+312, A+320) (blk), the two reply cells [pp, pp+8) and
                   [pn, pn+8), the record byte Phi+26 and its shadow byte ((Phi+26) >> 3) + ASAN_K. No write.
     seg_F10_ne_F  a0 = 0 (reply_args, ir false): `bne` taken to 0x82308. It reads and writes no memory.
   The source proof's own premises are kept (the cut's register values as `rg` facts, the spill and cell bytes,
   the record byte and its shadow byte, the length and Phi bounds); `rng` premises are added one per access. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs F5 F4.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module LE10 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* The lib.Lib twins of F10.v's f10_rd8 / f10_eqb0_false / f10_sub_lit (the F10 originals are stated over the UL
   engine's Mem.wa and inside its section). f10_ltu_false, f10_zxb_eq and f10_mlia are F4.v's f4_ltu_false,
   f4_zxb_eq and f4_mlia, which are the same statements over lib.Lib. *)
Lemma f10F_rd8 : forall m a bs, bytes_at rsegs m a bs -> length bs = 8%nat ->
  ov_read_bytes rsegs m (wa a) 8 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (bytes_at_ov_read rsegs m a bs 0 8 H ltac:(lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by lia. exact HH.
Qed.

Lemma f10F_eqb0_false : forall v, 0 < v < 2 ^ 64 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = false.
Proof.
  intros v Hv. apply Bool.not_true_iff_false. intro HC. apply bv_eqb_eq in HC.
  apply (f_equal bv_unsigned) in HC. rewrite !MState.unsigned_lit in HC by lia. lia.
Qed.

Lemma f10F_sub_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) - bv_unsigned (Z_to_bv 64 y)) = Z_to_bv 64 (x - y).
Proof. intros x y Hx Hy. rewrite !MState.unsigned_lit by lia. reflexivity. Qed.

Section F10F.

Variables (Fr : bvmap 5 word) (fc : bv 32).

(* ---- arm 1: a0 = 1 (reply_ok), 0x821ec -> 0x8226c (F10.v:239-283) ---- *)
Lemma seg_F10_ok_F :
  forall (RNG : footprint) (regs : bvmap 5 word) (mem : word -> option byte)
         (A p len pp pn irs : Z) (b26 : byte),
    rg regs 10 1 -> rg regs 18 p -> rg regs 20 len -> rg regs 9 A -> rg regs 26 ASAN_K ->
    rg regs 22 1 -> rg regs 25 1 ->
    0 < p /\ p + 64 <= 2 ^ 64 ->
    50 <= len /\ len < 2 ^ 64 ->
    13 <= irs <= 23 ->
    bytes_at rsegs mem (A + 304) (le8 (Z_to_bv 64 pp)) ->
    bytes_at rsegs mem (A + 296) (le8 (Z_to_bv 64 pn)) ->
    bytes_at rsegs mem (A + 312) (le8 (Z_to_bv 64 (p + 18))) ->
    bytes_at rsegs mem pp (le8 (Z_to_bv 64 (p + 38))) ->
    bytes_at rsegs mem pn (le8 (Z_to_bv 64 (irs - 13))) ->
    bytes_at rsegs mem (Z.shiftr (p + 26) 3 + ASAN_K) [Z_to_bv 8 0] ->
    bytes_at rsegs mem (p + 26) [b26] -> bv_unsigned b26 = irs ->
    rng RNG (A + 296) 8 -> rng RNG (A + 304) 8 -> rng RNG (A + 312) 8 ->
    rng RNG pp 8 -> rng RNG pn 8 ->
    rng RNG (Z.shiftr (p + 26) 3 + ASAN_K) 1 -> rng RNG (p + 26) 1 ->
    evtF rsegs RNG
      (fun ms => exists R pc' mem', ms = MS R Fr pc' fc None mem' (seg_rom rsegs) /\
         (pc' = Z_to_bv 64 0x8226c /\ mem' = mem /\
          getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
          getr R 8 = getr regs 8 /\ getr R 19 = getr regs 19 /\ getr R 21 = getr regs 21 /\
          getr R 22 = getr regs 22 /\ getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\
          getr R 27 = getr regs 27 /\
          getr R 9 = Z_to_bv 64 A /\ getr R 26 = Z_to_bv 64 ASAN_K /\ getr R 18 = Z_to_bv 64 p /\
          getr R 20 = Z_to_bv 64 len /\ getr R 11 = Z_to_bv 64 (irs - 13)))
      (MS (Regs6ss.mkR_of regs) Fr (Z_to_bv 64 0x821ec) fc None mem (seg_rom rsegs)).
Proof.
  intros RNG regs mem A p len pp pn irs b26 Ha0 Hs2 Hs4 H9 Hr26 Hs6 Hs9 Hpb Hlen Hirs
    Q304 Q296 Q312 Qpp Qpn Hsh26 Hb26 Hb26v
    R296 R304 R312 Rpp Rpn Rsh R26.
  pose proof (f10F_rd8 mem _ _ Q304 ltac:(apply length_le8)) as RD304.
  pose proof (f10F_rd8 mem _ _ Q296 ltac:(apply length_le8)) as RD296.
  pose proof (f10F_rd8 mem _ _ Q312 ltac:(apply length_le8)) as RD312.
  pose proof (f10F_rd8 mem _ _ Qpp ltac:(apply length_le8)) as RDpp.
  pose proof (f10F_rd8 mem _ _ Qpn ltac:(apply length_le8)) as RDpn.
  pose proof (f4_rd1 mem _ _ Hsh26) as RDsh.
  pose proof (f4_rd1 mem _ _ Hb26) as RD26.
  rewrite c_mkR_expand.
  c_slot Ha0. c_slot Hs2. c_slot Hs4. c_slot H9. c_slot Hr26. c_slot Hs6. c_slot Hs9.
  (* 0x821ec bltz a0 (a0 = 1) not taken ; 0x821f0 bne a0,s6 (s6 = 1) not taken *)
  step. if_false. step. if_false.
  (* 0x821f4 beqz s9 (s9 = sum_ok = 1) not taken *)
  step. if_false.
  (* 0x821f8 ld a0,304(s1) = pp ; 0x821fc ld a0,0(a0) = p+38 ; 0x82200 bltu a0,s2 not taken *)
  step. step. step. rewrite (f4_ltu_false (p + 38) p) by (clear - Hpb; f4_mlia). cbn [negb]. cbv iota.
  (* 0x82204 sub a2,a0,s2 = 38 ; 0x82208 bltu s4,a2 not taken (len >= 50) *)
  step. rewrite (f10F_sub_lit (p + 38) p) by lia. replace (p + 38 - p) with 38 by lia.
  step. rewrite (f4_ltu_false len 38) by (clear - Hlen; f4_mlia). cbn [negb]. cbv iota.
  (* 0x8220c ld a1,296(s1) = pn ; 0x82210 ld a1,0(a1) = irs-13 ; 0x82214 addi a3,a1,2 ;
     0x82218 sub a2,s4,a2 = len-38 ; 0x8221c bltu a2,a3 not taken *)
  step. step. step. step. rewrite (MState.unsigned_lit len) by lia.
  step. rewrite (f4_ltu_false (len - 38) (irs - 13 + 2)) by (clear - Hlen Hirs; f4_mlia).
  cbn [negb]. cbv iota.
  (* 0x82220 ld a2,312(s1) = blk = p+18 ; 0x82224 beqz a2 (T20) not taken: blk <> 0 *)
  step. step. rewrite (f10F_eqb0_false (p + 18)) by lia. cbn [negb]. cbv iota.
  (* 0x82228 li a2,-21 ; 0x8222c ld a3,312(s1) ; 0x82230 bltu a2,a3 (T21) not taken *)
  step. step. step. rewrite (f4_ltu_false _ (p + 18)) by (clear - Hpb; f4_mlia). cbn [negb]. cbv iota.
  (* 0x82234 ld a2,312(s1) ; 0x82238 addi a2,a2,20 = p+38 ; 0x8223c bne a0,a2 not taken *)
  step. step. step. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  (* 0x82240 ld a0,312(s1) ; 0x82244 addi a0,a0,8 = p+26 ; 0x82248 li a2,9 ;
     0x8224c bltu a0,a2 (T22) not taken: p+26 >= 9 *)
  step. step. step. step. rewrite (f4_ltu_false (p + 26) 9) by (clear - Hpb; f4_mlia). cbn [negb]. cbv iota.
  (* 0x82250 srli ; add ; lb a2 = shadow byte of p+26 = 0 ; 0x8225c bnez a2 not taken *)
  step. step. rewrite (MState.unsigned_lit (p + 26)) by lia.
  step. step. if_false.
  (* 0x82260 lbu a0,0(a0) = b26 = irs ; 0x82264 addi a2,a1,13 ; 0x82268 bne a2,a0 not taken *)
  step. step. step.
  rewrite (f4_zxb_eq b26 (irs - 13 + 13)) by lia.
  rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  (* land at 0x8226c *)
  finish. all: simp_regs; try reflexivity.
Qed.

(* ---- arm 2: a0 = 0 (reply_args, ir false), 0x821ec -> 0x82308 (F10.v:325-337) ---- *)
Lemma seg_F10_ne_F :
  forall (RNG : footprint) (regs : bvmap 5 word) (mem : word -> option byte),
    rg regs 10 0 -> rg regs 22 1 ->
    evtF rsegs RNG
      (fun ms => exists R pc' mem', ms = MS R Fr pc' fc None mem' (seg_rom rsegs) /\
         (pc' = Z_to_bv 64 0x82308 /\ mem' = mem /\
          getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
          getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
          getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\ getr R 21 = getr regs 21 /\
          getr R 22 = getr regs 22 /\ getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\
          getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27))
      (MS (Regs6ss.mkR_of regs) Fr (Z_to_bv 64 0x821ec) fc None mem (seg_rom rsegs)).
Proof.
  intros RNG regs mem Ha0 Hs6.
  rewrite c_mkR_expand. c_slot Ha0. c_slot Hs6.
  (* 0x821ec bltz a0 (a0 = 0) not taken ; 0x821f0 bne a0,s6 (s6 = 1) taken *)
  step. if_false. step. if_true.
  finish. all: simp_regs; try reflexivity.
Qed.

(* ---- the source runs (lib.Lib Exec.evt, the form Tac_slot.sl_run consumes): the `_of_F` compares ---- *)
Lemma seg_F10_ok_run :
  forall (regs : bvmap 5 word) (mem : word -> option byte)
         (A p len pp pn irs : Z) (b26 : byte),
    rg regs 10 1 -> rg regs 18 p -> rg regs 20 len -> rg regs 9 A -> rg regs 26 ASAN_K ->
    rg regs 22 1 -> rg regs 25 1 ->
    0 < p /\ p + 64 <= 2 ^ 64 ->
    50 <= len /\ len < 2 ^ 64 ->
    13 <= irs <= 23 ->
    0 <= A /\ A + 320 <= 2 ^ 64 ->
    0 <= pp /\ pp + 8 <= 2 ^ 64 -> 0 <= pn /\ pn + 8 <= 2 ^ 64 ->
    bytes_at rsegs mem (A + 304) (le8 (Z_to_bv 64 pp)) ->
    bytes_at rsegs mem (A + 296) (le8 (Z_to_bv 64 pn)) ->
    bytes_at rsegs mem (A + 312) (le8 (Z_to_bv 64 (p + 18))) ->
    bytes_at rsegs mem pp (le8 (Z_to_bv 64 (p + 38))) ->
    bytes_at rsegs mem pn (le8 (Z_to_bv 64 (irs - 13))) ->
    bytes_at rsegs mem (Z.shiftr (p + 26) 3 + ASAN_K) [Z_to_bv 8 0] ->
    bytes_at rsegs mem (p + 26) [b26] -> bv_unsigned b26 = irs ->
    LE10.evt rsegs
      (fun ms => exists R pc' mem', ms = MS R Fr pc' fc None mem' (seg_rom rsegs) /\
         (pc' = Z_to_bv 64 0x8226c /\ mem' = mem /\
          getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
          getr R 8 = getr regs 8 /\ getr R 19 = getr regs 19 /\ getr R 21 = getr regs 21 /\
          getr R 22 = getr regs 22 /\ getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\
          getr R 27 = getr regs 27 /\
          getr R 9 = Z_to_bv 64 A /\ getr R 26 = Z_to_bv 64 ASAN_K /\ getr R 18 = Z_to_bv 64 p /\
          getr R 20 = Z_to_bv 64 len /\ getr R 11 = Z_to_bv 64 (irs - 13)))
      (MS (Regs6ss.mkR_of regs) Fr (Z_to_bv 64 0x821ec) fc None mem (seg_rom rsegs)).
Proof.
  intros regs mem A p len pp pn irs b26 Ha0 Hs2 Hs4 H9 Hr26 Hs6 Hs9 Hpb Hlen Hirs HA Hpp Hpn
    Q304 Q296 Q312 Qpp Qpn Hsh26 Hb26 Hb26v.
  assert (Hsp : 0 <= Z.shiftr (p + 26) 3 <= 2 ^ 61).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. }
  apply (evtF_evt rsegs RNG_all). eapply seg_F10_ok_F; try eassumption;
    apply rng_all; unfold ASAN_K in *; lia.
Qed.

Lemma seg_F10_ne_run :
  forall (regs : bvmap 5 word) (mem : word -> option byte),
    rg regs 10 0 -> rg regs 22 1 ->
    LE10.evt rsegs
      (fun ms => exists R pc' mem', ms = MS R Fr pc' fc None mem' (seg_rom rsegs) /\
         (pc' = Z_to_bv 64 0x82308 /\ mem' = mem /\
          getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
          getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
          getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\ getr R 21 = getr regs 21 /\
          getr R 22 = getr regs 22 /\ getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\
          getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27))
      (MS (Regs6ss.mkR_of regs) Fr (Z_to_bv 64 0x821ec) fc None mem (seg_rom rsegs)).
Proof.
  intros. apply (evtF_evt rsegs RNG_all). eapply seg_F10_ne_F; eassumption.
Qed.

End F10F.
