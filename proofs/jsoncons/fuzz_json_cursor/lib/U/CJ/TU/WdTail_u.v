(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Tac ZBridge FP.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Bridge Require Import BrMem.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.TUB Require Import DgWalkB_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.TU Require Import G3Lem_u WdHead_u.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WT.
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable SP : Z.
Variables wd o dp : Z.
Variable m0 : word -> option byte.
Definition SPD : Z := (SP - 560)%Z.
Hypothesis SPR : (2 ^ 41 + 9600 <= SP /\ SP <= 2 ^ 47)%Z.
Hypothesis ORNG : (SP <= o /\ o + 24 <= 2 ^ 47)%Z.
Hypothesis DPR : (0 <= dp < 256)%Z.
Definition WT_W : list (Z * Z) := [(SP - 9600, SP); (o, o + 24); (0xd675c, 0xd6760)]%Z.

Definition FRT (jd jg txt : list byte) (fs0b : word) (j2 dig : list byte) (kw lw fs0w : word) (j3 : list byte) : list cell :=
  [CB 8 jd; CB 4 jg; CB 100 txt; C8 fs0b; C8 s3; C8 s2; C8 (Z_to_bv 64 dp); C8 (Z_to_bv 64 o); C8 (Z_to_bv 64 0x45178);
   CB 4 j2; CB 100 dig; C4 kw; C4 lw; C8 fs0w; C8 (Z_to_bv 64 wd); C8 (Z_to_bv 64 o); C8 (Z_to_bv 64 0x436fc);
   CB 232 j3; C8 s1; C8 s0; C8 ra].
Definition tmem (m m' : word -> option byte) : Prop :=
  (exists jd jg txt fs0b j2 dig kw lw fs0w j3, rw_cells rsegs m' SPD (FRT jd jg txt fs0b j2 dig kw lw fs0w j3))
  /\ (exists bs, u8arr rsegs m' o bs /\ estr bs) /\ stk rsegs m' (SP - 9600) SPD
  /\ munch WT_W m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'.

Definition wpDS (m : word -> option byte) (n : Z) (bits : word) : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m',
    ms' = MS (mkR (Z_to_bv 64 0x45218) (Z_to_bv 64 SPD) gp tp t0' t1' t2' (Z_to_bv 64 o) (Z_to_bv 64 dp)
                  (Z_to_bv 64 (SPD + 12)) (Z_to_bv 64 n) (Z_to_bv 64 SPD) a3' a4' a5' a6' a7' bits (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F' (Z_to_bv 64 0x3f4e8) fc' None m' (seg_rom rsegs)
    /\ frm0 fc' /\ tmem m m' /\ munch [(SPD, SPD + 8)]%Z m m'.

Definition wpDBE (m' : word -> option byte) (n : Z) (bits : word) : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' F' fc',
    ms' = MS (mkR (Z_to_bv 64 0x4528c) (Z_to_bv 64 SPD) gp tp t0' t1' t2' (Z_to_bv 64 o) (Z_to_bv 64 dp)
                  (Z_to_bv 64 (SPD + 12)) (Z_to_bv 64 n) (Z_to_bv 64 dp) (Z_to_bv 64 o) a4' a5' a6' a7' bits (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F' (Z_to_bv 64 0x43d90) fc' None m' (seg_rom rsegs)
    /\ (1 <= n <= 25)%Z /\ frm0 fc' /\ tmem m0 m'.

Definition wpSN2 (m' : word -> option byte) (bits : word) : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' F' fc' s3',
    ms' = MS (mkR (Z_to_bv 64 0x45270) (Z_to_bv 64 SPD) gp tp t0' t1' t2' (Z_to_bv 64 o) (Z_to_bv 64 dp)
                  (Z_to_bv 64 (SPD + 12)) (Z_to_bv 64 100) (Z_to_bv 64 0x130d8) (Z_to_bv 64 17) bits a5' a6' a7' bits s3' s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F' (Z_to_bv 64 0xacd08) fc' None m' (seg_rom rsegs)
    /\ frm0 fc' /\ tmem m0 m'.

Lemma wt_sn1 : forall rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 bits F fc (m : word -> option byte) (n : Z),
  frm0 fc -> (1 <= n <= 25)%Z -> tmem m0 m ->
  evt rsegs (wpDS m n bits) (MS (mkR rav (Z_to_bv 64 SPD) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 dp) (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7
                                     bits s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x451fc) fc None m (seg_rom rsegs)).
Proof.
  intros until n. intros FRM Hn ((jd & jg & txt & fs0b & j2 & dig & kw & lw & fs0w & j3 & FR) & (bs & BU & ES) & ST & MU & WM & MI).
  pose proof (munch_refl [(SPD, SPD + 8)]%Z m) as MU1. pose proof (wmono_refl rsegs m) as WM1.
  unfold SPD, WT_W, FRT in *.
  zstep. if_cases K1; [scond K1; lia|].
  do 2 zstep. fix_lit8. mem_after_store.
  do 4 zstep.
  apply evt_done. unfold wpDS. exs. split; [reflexivity|].
  split; [eassumption|]. split.
  - split; [|split; [exists bs; split; assumption|]].
    + lazymatch goal with H : rw_cells _ ?mm _ (C8 ?x :: ?rest) |- _ =>
        apply (rw_cells_merge rsegs mm _ [] [C8 x] rest) in H; cbn [cells_size csize Nat.add cells_bytes cbytes app] in H end.
      do 10 eexists. unfold FRT, SPD. rewrite app_nil_r in *. eassumption.
    + split; [unfold SPD; eassumption|]. split; [unfold WT_W; eassumption|]. split; eassumption.
  - unfold SPD. eassumption.
Qed.

Lemma wt_ds : forall rav t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 bits F fc (m : word -> option byte) (n c : Z),
  frm0 fc -> (1 <= n <= 25)%Z -> (c = 0 \/ c = 34)%Z -> tmem m0 m ->
  evt rsegs (fun ms => wpDBE m n bits ms \/ wpSN2 m bits ms)
            (MS (mkR rav (Z_to_bv 64 SPD) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 dp) a0 (Z_to_bv 64 c) a2 a3 a4 a5 a6 a7
                     bits (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x45218) fc None m (seg_rom rsegs)).
Proof.
  intros until c. intros FRM Hn Hc ((jd & jg & txt & fs0b & j2 & dig & kw & lw & fs0w & j3 & FR) & (bs & BU & ES) & ST & MU & WM & MI).
  unfold SPD, WT_W, FRT in *.
  zstep. zstep.
  zstep. if_cases K1; [| exfalso; rewrite Z.add_0_r, swrap32_small' in K1 by lia; apply Bool.negb_false_iff in K1; unfold bv_eqb in K1;
                        apply Z.eqb_eq in K1; rewrite !unsigned_lit in K1 by lia; lia].
  do 2 zstep.
  destruct (feq_d _ _) eqn:FQ; cbn [bword] in *.
  -
    zstep. if_cases K2; [|vm_compute in K2; discriminate].
    do 5 zstep.
    apply evt_done. left. unfold wpDBE. exs. split; [reflexivity|]. split; [lia|]. split; [eassumption|].
    split; [do 10 eexists; unfold FRT, SPD; eassumption|]. split; [exists bs; split; assumption|].
    split; [unfold SPD; eassumption|]. split; [unfold WT_W; eassumption|]. split; eassumption.
  - zstep. if_cases K2; [vm_compute in K2; discriminate|].
    do 7 zstep.
    apply evt_done. right. unfold wpSN2. exs. split; [reflexivity|]. split; [eassumption|].
    split; [do 10 eexists; unfold FRT, SPD; eassumption|]. split; [exists bs; split; assumption|].
    split; [unfold SPD; eassumption|]. split; [unfold WT_W; eassumption|]. split; eassumption.
Qed.

Lemma wt_sn2 : forall rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 bits s3' F fc (m : word -> option byte) (n : Z),
  frm0 fc -> (1 <= n <= 25)%Z -> tmem m0 m ->
  evt rsegs (wpDBE m n bits) (MS (mkR rav (Z_to_bv 64 SPD) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 dp) (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7
                                    bits s3' s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 0x45270) fc None m (seg_rom rsegs)).
Proof.
  intros until n. intros FRM Hn ((jd & jg & txt & fs0b & j2 & dig & kw & lw & fs0w & j3 & FR) & (bs & BU & ES) & ST & MU & WM & MI).
  unfold SPD, WT_W, FRT in *.
  zstep. zstep. if_cases K1; [scond K1; lia|].
  do 5 zstep.
  apply evt_done. unfold wpDBE. exs. split; [reflexivity|]. split; [lia|]. split; [eassumption|].
  split; [do 10 eexists; unfold FRT, SPD; eassumption|]. split; [exists bs; split; assumption|].
  split; [unfold SPD; eassumption|]. split; [unfold WT_W; eassumption|]. split; eassumption.
Qed.

End WT.
