From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FuzzProducer.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg frame_kit.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation PZD_RESERVE_TAIL := 0x2d790 (only parsing).

Definition zd_reserve_tail_post (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (P D size1 slice : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 a4 a5 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fst (producer_contract size1 slice))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(P, P + 16)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' P [C8 (Z_to_bv 64 (D + fst (producer_contract size1 slice))); C8 (Z_to_bv 64 (snd (producer_contract size1 slice)))].

Definition zd_reserve_tail_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P D size1 slice : Z),
  rw_cells usegs m P [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 size1)] ->
  0 < P -> P mod 8 = 0 -> 0 < D -> 0 <= size1 -> D + size1 < 2^64 -> 0 <= slice < 2^64 ->
  mem_inv usegs m ->
  evt usegs (zd_reserve_tail_post ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc P D size1 slice m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 slice) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_RESERVE_TAIL) fc None m (seg_rom usegs)).

Ltac xnorm :=
  repeat match goal with
  | |- context [Z.ltb 0 ?x] => replace (Z.ltb 0 x) with true by (symmetry; apply Z.ltb_lt; lia)
  | |- context [Z.ltb ?x 1] => replace (Z.ltb x 1) with false by (symmetry; apply Z.ltb_ge; lia)
  end;
  cbn [Z.b2z Z.lxor].

Lemma zd_reserve_tail_proof : zd_reserve_tail_stmt.
Proof.
  intros until slice. intros PR PNZ PAL DNZ S1 DS SL MI.
  pose proof (rw_cells_bound _ _ _ _ PR) as PB. cbn [cells_size csize Nat.add Z.of_nat] in PB.
  pose proof (munch_refl [(P, P + 16)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold zd_reserve_tail_post, producer_contract.
  change (2^64) with 18446744073709551616 in *.
  zstep. fck.
  zstep. zstep. fck.
  zstep.
  zstep. if_cases KM; zify_cond KM.
  - replace (Z.min slice size1) with slice by lia.
    zstep. zstep. zstep. zstep. fck.
    zstep. zstep. zstep. zstep. xnorm. fck.
    zstep. zstep. zstep. zstep.
    apply evt_done. cbn [fst snd]. do 5 eexists. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    replace (D + (size1 - slice)) with (size1 - slice + D) by lia. eassumption.
  - replace (Z.min slice size1) with size1 by lia.
    zstep.
    zstep. zstep. zstep. zstep. fck.
    zstep. zstep. zstep. zstep. xnorm. fck.
    zstep. zstep. zstep. zstep.
    apply evt_done. cbn [fst snd]. do 5 eexists. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    replace (D + (size1 - size1)) with (size1 - size1 + D) by lia. eassumption.
Qed.
