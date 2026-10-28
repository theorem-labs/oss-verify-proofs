(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit
     Sj_num_akit Pj_rtkA Pj_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition PJ_COPY_G_A : Z := 0xb6df4.
Definition PJ_COPY_S_A : Z := 0xb6e90.
Definition PJ_COPY_STACK_A : Z := 48 + RT_STACK.

Lemma b2z_pos : forall x, (0 < x)%Z -> Z.b2z (0 <? x) = 1%Z.
Proof. intros x H. rewrite (proj2 (Z.ltb_lt 0 x) H). reflexivity. Qed.
Lemma b2z_lt1 : forall x, (0 < x)%Z -> Z.b2z (x <? 1) = 0%Z.
Proof. intros x H. rewrite (proj2 (Z.ltb_ge x 1)) by lia. reflexivity. Qed.
Lemma slti0_nonneg : forall x, (0 <= x < 9223372036854775808)%Z -> Z.b2z (Z.lxor x 9223372036854775808 <? 9223372036854775808) = 0%Z.
Proof.
  intros x H. change 9223372036854775808%Z with (2^63)%Z. rewrite ZBridge.zb_lxor_pow2_small by lia.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
Qed.
Lemma b2z_ltu_false : forall a b, (b <= a)%Z -> Z.b2z (a <? b) = 0%Z.
Proof. intros a b H. rewrite (proj2 (Z.ltb_ge a b) H). reflexivity. Qed.

Ltac gref G := exfalso; rewrite ?unsigned_lit in G by lia; lia.
Ltac gtrap := let G := fresh "G" in zstep; if_cases G; zify_cond G; [gref G|]; try clear G.

Ltac unz := rewrite ?b2z_pos, ?b2z_lt1 by lia.

Ltac uov := rewrite ?slti0_nonneg by lia; rewrite ?b2z_ltu_false by lia; change (Z.lxor (Z.lxor 0 0) 1) with 1%Z.

Definition cp_regs (pc : Z) (ra : word) (q : Z) (gp tp t0 t1 t2 : word) (a0 a1 a2 a3 a4 a5 a6 a7 : word) (Src Dst N : Z) (s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 (q - 48)) gp tp t0 t1 t2 (Z_to_bv 64 (Src + N)) (Z_to_bv 64 N) a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 Src) (Z_to_bv 64 Dst) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom bsegs).

Lemma copy_walk0 : forall (pc q lo Src Dst N : Z) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  pc = PJ_COPY_G_A \/ pc = PJ_COPY_S_A ->
  stk bsegs m lo q -> lo <= q - 48 -> 0x6e0000 <= lo -> q < 2^63 -> 0 <= Src -> 0 <= N -> Src + N < 2^63 -> 0 <= Dst < 2^63 -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (j0 : list byte),
      munch [(q - 48, q)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (q - 48)
      /\ rw_cells bsegs m1 (q - 48) [CB 8 j0; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ ((N = 0 /\ ms = cp_regs (pc + 60) ra q gp tp t0 t1 t2 (Z_to_bv 64 Src) (Z_to_bv 64 (Src + N)) (Z_to_bv 64 Dst) a3 a4 a5 a6 a7 Src Dst N s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1)
          \/ (N <> 0 /\ ms = cp_regs e_asan_memmove (Z_to_bv 64 (pc + 60)) q gp tp t0 t1 t2 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 Src Dst N
                                     s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1)))
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Src) (Z_to_bv 64 (Src + N)) (Z_to_bv 64 Dst) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros HPC ST LO GLO QH S0 N0 SNH DR MI. unfold cp_regs, e_asan_memmove.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(q - 48, q)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  destruct HPC as [-> | ->]; unfold PJ_COPY_G_A, PJ_COPY_S_A.
  all: zstep; carve_frame 48%nat ST.
  all: apply (rw_cells_split_CB bsegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]; cbn [mk_CB_cells app] in FR.
  all: repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.

  all: do 5 zstep; zstep; zstep; zstep; zstep.
  all: try replace (Src + N + - Src) with N by lia; try replace (Src + N - Src) with N by lia.
  all: replace (q + -48) with (q - 48) in * by lia.

  all: zstep; if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  1,3: apply evt_done; do 2 eexists; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact ST|]; split; [exact FR|];
       left; split; [lia| cbv delta [mkR]; reflexivity].

  all: zstep; zstep; zstep; zstep.
  all: apply evt_done; do 2 eexists; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact ST|]; split; [exact FR|];
       right; split; [lia| cbv delta [mkR]; reflexivity].
Qed.

Lemma copy_walk1 : forall (pc q lo Src Dst N : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (cra cs0 cs1 cs2 cs3 : word) (j0 : list byte) F fc (m : mem),
  pc = PJ_COPY_G_A \/ pc = PJ_COPY_S_A ->
  stk bsegs m lo (q - 48) -> 0 <= lo -> lo <= q - 48 -> q < 2^63 ->
  0 < Src -> 0 <= N -> Src + N < 2^63 -> 0 < Dst -> Dst + N < 2^63 ->
  rw_cells bsegs m (q - 48) [CB 8 j0; C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists a2',
      ms = MS (mkR cra (Z_to_bv 64 q) gp tp t0 t1 t2 cs0 cs1 (Z_to_bv 64 (Src + N)) (Z_to_bv 64 (Dst + N)) a2' a3 a4 a5 a6 a7 cs2 cs3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc cra) fc None m (seg_rom bsegs)
      /\ stk bsegs m lo q)
    (cp_regs (pc + 60) ra q gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 Src Dst N s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros HPC ST LO0 LO QH S0 N0 SNH D0 DNH FR MI. unfold cp_regs.
  assert (EU : bv_unsigned (Z_to_bv 64 (q - 48)) = q - 48) by (apply unsigned_lit; lia).
  destruct HPC as [-> | ->]; unfold PJ_COPY_G_A, PJ_COPY_S_A.
  all: cbn [Z.add].
  all:
       zstep; gtrap;

       zstep; zstep; zstep; unz; change (Z.lxor 1 0) with 1%Z; zstep; if_false;

       zstep; zstep; unz; zstep; if_false;

       zstep; zstep; zstep; zstep; uov; zstep; if_false;
       gtrap;

       zstep; do 5 zstep; zstep;
       release_frame FR ST q;
       zstep; replace (q - 48 + 48) with q by lia; try replace (N + Dst) with (Dst + N) by lia;
       apply evt_done; eexists; split; [cbv delta [mkR]; reflexivity| exact ST].
Qed.

Lemma acc_agree : forall (m m' : mem) a n, acc bsegs m a n -> 0 <= a ->
  agree_on (fun x => SHB <= x <= shad (a + n)) m m' -> acc bsegs m' a n.
Proof.
  intros m m' a n H Ha AG i Hi. destruct (H i Hi) as (b & Hb & Hok). exists b. split; [| exact Hok].
  apply (bytes_at_agree bsegs m m' _ _ Hb). apply (agree_sub _ _ m m' AG). intros x Hx. cbn [length Z.of_nat] in Hx.
  unfold shad, SHB in *. split; [Z.div_mod_to_equations; lia|].
  assert ((a + i) / 8 <= (a + n) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

Section Copy.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Notation aevt := (aevt RT PMc).
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition copy_cpsA (entry : Z) : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (q lo Src Dst N : Z) (src : list byte)
         (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  bytes_at bsegs m Src src -> Z.of_nat (length src) = N -> N < 2^40 ->
  0 < Src -> Src + N <= lo -> 0 < Dst -> Dst + N <= lo ->
  (0 < N -> acc bsegs m Src N /\ rng_class RT Σ Src N) -> (0 < N -> acc bsegs m Dst N /\ rng_class RT Σ Dst N) ->
  (forall sp i, 0 <= i < N -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp (Dst + i)) -> wr_at bsegs m Dst N ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo q -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + PJ_COPY_STACK_A <= q ->
  q + 16 <= USTACK_TOP -> q mod 16 = 0 ->
  (forall t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     ART RT Σ m' -> mem_inv bsegs m' -> stk bsegs m' lo q -> wmono bsegs m m' -> bytes_at bsegs m' Dst src ->
     (forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> ~ (Dst <= bv_unsigned a < Dst + N) -> m' a = m a) ->
     aevt Σ K (MS (mkR ra (wz q) gp tp t0' t1' t2' s0 s1 (wz (Src + N)) (wz (Dst + N)) a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz Src) (wz (Src + N)) (wz Dst) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz entry) fc None m (seg_rom bsegs)).

Local Ltac ul := unfold PJ_COPY_STACK_A in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Theorem copy_okA : forall entry, entry = PJ_COPY_G_A \/ entry = PJ_COPY_S_A -> copy_cpsA entry.
Proof using AF RC FDO MST.
  intros entry HPC Σ K q lo Src Dst N src ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    BY0 LEN N40 S0 SLO D0 DLO SRCOK DSTOK CLD WR0 ART0 MI0 ST0 SPLO LOQ QT Q16 HK.
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  assert (N0 : 0 <= N) by lia.
  assert (EU : bv_unsigned (Z_to_bv 64 (q - 48)) = q - 48) by (apply unsigned_lit; ul).

  assert (CSEP : forall sp a, lo + RT_STACK <= sp -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp a -> sp <= a \/ a < lo).
  { intros sp a Hsp Ha. destruct (aclient_split_c RT AF Σ m sp a ART0 Ha) as [H|H]; [left; exact H| right; ul]. }

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (copy_walk0 entry q lo Src Dst N ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m HPC ST0);
                   [ul| ul| ul| ul| ul| ul| ul| exact MI0]|].
  cbv beta. intros ms1 (m1 & j0 & MU1 & WM1 & MI1 & ST1 & FR1 & ALT).
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 (q - 48) ART0 ltac:(ul)); [| exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ul. }
  assert (PRES1 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> m1 a = m a).
  { intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. destruct (CSEP q _ ltac:(ul) Ha); ul. }
  destruct ALT as [(NZ & ->)|(NZ & ->)]; apply evt_done; unfold cp_regs.
  -
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [eapply (copy_walk1 entry q lo Src Dst N ra gp tp t0 t1 t2 _ _ _ a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 j0 F fc m1 HPC ST1);
                     [ul| ul| ul| ul| ul| ul| ul| ul| exact FR1| exact MI1]|].
    cbv beta. intros ms2 (a2' & -> & ST2). apply evt_done.
    apply (HK t0 t1 t2 a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 F m1 ART1 MI1 ST2 WM1).
    + assert (E0 : src = []) by (destruct src; [reflexivity| cbn [length] in LEN; lia]). rewrite E0.
      split; [lia|]. split; [cbn [length Z.of_nat]; ul|]. intros i Hi. cbn [length] in Hi. lia.
    + intros a Ha _. exact (PRES1 a Ha).
  -
    destruct (SRCOK ltac:(lia)) as [ACS RCS]. destruct (DSTOK ltac:(lia)) as [ACD RCD].
    assert (SHAG : agree_on (fun x => SHB <= x <= shad (lo + 0)) m m1).
    { intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. unfold shad, SHB in Ha. ul. }
    assert (BY1 : bytes_at bsegs m1 Src src).
    { apply (bytes_at_agree bsegs m m1 _ _ BY0). intros a Ha. apply MU1. cbn [outside]. split; [ul| exact I]. }
    assert (CS : checked_src RT Σ m1 (Z_to_bv 64 (q - 48)) lo Src (Z.of_nat (length src))).
    { unfold checked_src. rewrite EU, LEN. split; [| left; lia]. intros _. split; [| exact RCS].
      apply (acc_agree m m1 _ _ ACS ltac:(lia)). apply (agree_sub _ _ m m1 SHAG). intros x Hx. unfold shad in *.
      assert ((Src + N) / 8 <= (lo + 0) / 8) by (apply Z.div_le_mono; lia). lia. }
    assert (CD : checked_dst RT Σ m1 (Z_to_bv 64 (q - 48)) Dst (Z.of_nat (length src))).
    { unfold checked_dst. rewrite EU, LEN. split; [| split; [intros i Hi; exact (CLD _ i Hi)| exact (wr_at_transport bsegs m m1 _ _ WR0 WM1)]].
      intros _. split; [| exact RCD].
      apply (acc_agree m m1 _ _ ACD ltac:(lia)). apply (agree_sub _ _ m m1 SHAG). intros x Hx. unfold shad in *.
      assert ((Dst + N) / 8 <= (lo + 0) / 8) by (apply Z.div_le_mono; lia). lia. }
    assert (COK : call_ok RT Σ m1 (Z_to_bv 64 (q - 48)) lo).
    { unfold call_ok. rewrite EU. split; [exact ST1|]. split; [lia|]. split; [ul|]. split; [ul| Z.div_mod_to_equations; lia]. }
    eapply (aevt_memmoveP RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 Dst Src src lo
              eq_refl eq_refl ltac:(rewrite LEN; reflexivity) ltac:(ul) ltac:(ul) ltac:(rewrite LEN; lia) BY1 CS CD ART1 MI1 COK).
    intros w0 w1 w2 b1 b2 b3 b4 b5 b6 b7 w3 w4 w5 w6 F2 m2 (ART2 & MI2 & WM2 & ST2) PRES2 BY2. rewrite EU in ST2, PRES2. rewrite LEN in PRES2.
    rewrite (ret_pc_even (entry + 60)) by (destruct HPC as [-> | ->]; unfold PJ_COPY_G_A, PJ_COPY_S_A; lia).
    assert (FR2 : rw_cells bsegs m2 (q - 48) [CB 8 j0; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply rw_cells_agree_nw; [exact FR1|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply PRES2; [left; ul| ul]. }
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [eapply (copy_walk1 entry q lo Src Dst N (Z_to_bv 64 (entry + 60)) gp tp w0 w1 w2 _ _ _ b3 b4 b5 b6 b7 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6
                               ra s0 s1 s2 s3 j0 F2 fc m2 HPC ST2); [ul| ul| ul| ul| ul| ul| ul| ul| exact FR2| exact MI2]|].
    cbv beta. intros ms3 (a2' & -> & ST3). apply evt_done.
    apply (HK w0 w1 w2 a2' b3 b4 b5 b6 b7 w3 w4 w5 w6 F2 m2 ART2 MI2 ST3 (wmono_trans _ _ _ _ WM1 WM2) BY2).
    intros a Ha Hn. rewrite <- (PRES1 a Ha). apply PRES2; [| exact Hn].
    apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| lia].
Qed.

End Copy.
