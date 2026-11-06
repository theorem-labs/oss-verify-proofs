(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtRepP/W_c2i_ibuf.v, with its module paths and module names changed; 330 of its 352 lines of code are new or changed and 506 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 (Z_to_bv 64 ?z) => constr:(C1 (Z_to_bv 8 z))
  end.

Lemma le1_lit8 : forall z, 0 <= z < 256 -> le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros z Hz. rewrite <- (le1_zxb (Z_to_bv 8 z)). unfold zxb. do 2 f_equal.
  rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

Ltac mem_after_store_opt ::=
  try fix_lit_store;
  rewrite ?le1_zxb; rewrite ?le1_lit8 by lia;
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.

Ltac munch_by MU :=
  let x := fresh "x" in let H := fresh "H" in
  intros x H; apply MU; cbn [outside] in H |- *; lia.

Ltac cfact H :=
  zify_cond H; unfold zxb in H; rewrite ?unsigned_lit in H by lia;
  try (apply andb_false_iff in H; destruct H as [H|H]; zify_bool H).

Ltac zl := first [ lia | Z.div_mod_to_equations; lia ].

Ltac weq := first [ reflexivity | word_eq_tac | (rewrite ?unsigned_lit by lia; reflexivity) ].

Definition at_call (rav spv gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v a0v a1v a2v : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (W : list ivl)
    (FR : (word -> option byte) -> Prop) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR rav spv gp tp t0 t1 t2 s0v s1v a0v a1v a2v a3 a4 a5 a6 a7
                  s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
             F (Z_to_bv 64 0x154b8) fc None m' (seg_rom rsegs) /\
    munch W m0 m' /\ wmono rsegs m0 m' /\ FR m'.

Definition saved (f : Z) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : word -> option byte) : Prop :=
  exists j, rw_cells rsegs m f [CB 8 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2;
                                C8 s1; C8 s0; C8 ra].

Lemma ts_pro : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (t s : Z) (j : list byte),
  0 <= t < 2 ^ 64 -> 0 <= s < 2 ^ 64 ->
  rw_cells rsegs m (bv_unsigned sp + -112) [CB 112 j] -> mem_inv rsegs m ->
  evt rsegs (at_call (Z_to_bv 64 0x15928) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp
               (Z_to_bv 64 t) (Z_to_bv 64 s) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               (Z_to_bv 64 t) (Z_to_bv 64 0x10394) (Z_to_bv 64 1) F fc m
               [(bv_unsigned sp + -112, bv_unsigned sp + -112 + 112)]
               (saved (bv_unsigned sp + -112) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 t) (Z_to_bv 64 s) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x158d4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m t s j
    Ht Hs FRJ MI.
  pose proof (rw_cells_bound _ _ _ _ FRJ) as FB. cbn [cells_size csize] in FB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp + -112 + 112)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  apply (rw_cells_split_CB rsegs _ _ [] 112%nat j [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRJ;
    [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FRJ.
  do 21 step.
  apply evt_done. unfold at_call, saved.
  do 13 eexists. split; [reflexivity|]. split; [munch_by MU|]. split; [exact WM|].
  eexists. exact FRJ.
Qed.

Lemma ts_epi : forall ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) (f t : Z),
  0 <= t < 2 ^ 64 -> 0 <= f -> f + 112 < 2 ^ 64 ->
  saved f rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v m ->
  evt rsegs (at_call rav (Z_to_bv 64 (f + 112)) gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v
               (Z_to_bv 64 t) (Z_to_bv 64 0x10394) (Z_to_bv 64 1) F fc m [] (fun m' => m' = m))
    (MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 (Z_to_bv 64 t) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15a20) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v f t Ht Hf Hf1 [j FR].
  do 19 step.
  apply evt_done. unfold at_call.
  do 13 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. reflexivity.
Qed.

Lemma ts_first : forall (Q : machine_state -> Prop) ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7
    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (p : Z) (c : byte),
  0 < p < 2 ^ 64 ->
  ov_read_bytes rsegs m (wa p) 1 = Some [c] ->
  (bv_unsigned c = 0 -> forall x0 : word, x0 = zxb c ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 p) x0 a1 a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x15a20) fc None m (seg_rom rsegs))) ->
  (bv_unsigned c <> 0 -> forall x0 x1 x2 y2 y6 y11 : word, x0 = zxb c ->
     y2 = Z_to_bv 64 0x102e9 -> y6 = Z_to_bv 64 (2 ^ 64 - 1) -> y11 = Z_to_bv 64 0x104a8 ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 p) x0 x1 x2 a3 a4 a5 a6 a7
                          y2 (Z_to_bv 64 92) (Z_to_bv 64 9) (Z_to_bv 64 48) y6
                          (Z_to_bv 64 34) (Z_to_bv 64 32) (Z_to_bv 64 13) (Z_to_bv 64 10) y11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x15964) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 p) a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x15928) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p c
    Hp RD KE KL.
  assert (HZ : 0 <= bv_unsigned c < 256) by (pose proof (bv_unsigned_in_range 8 c) as H; unfold bv_modulus in H; exact H).
  step. if_cases HB; cfact HB; try (exfalso; zl).
  step.
  step. if_cases HC; cfact HC.
  - first [ eapply KE; [zl | weq] | exfalso; zl ].
  - do 12 step. eapply KL; [zl | weq | weq | weq | weq].
Qed.

Lemma ts_next : forall (Q : machine_state -> Prop) ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7
    s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (p : Z) (c : byte),
  0 <= p -> p + 1 < 2 ^ 64 ->
  ov_read_bytes rsegs m (wa (p + 1)) 1 = Some [c] ->
  (bv_unsigned c = 0 -> forall x0 y1 : word, x0 = zxb c -> y1 = Z_to_bv 64 (p + 1) ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 y1 x0 a1 a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 (Z_to_bv 64 (2 ^ 64 - 1)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x15a20) fc None m (seg_rom rsegs))) ->
  (bv_unsigned c <> 0 -> forall x0 y1 : word, x0 = zxb c -> y1 = Z_to_bv 64 (p + 1) ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 y1 x0 a1 a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 (Z_to_bv 64 (2 ^ 64 - 1)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x15964) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 p) a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 (Z_to_bv 64 (2 ^ 64 - 1)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x159e8) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p c
    Hp Hp1 RD KE KL.
  assert (HZ : 0 <= bv_unsigned c < 256) by (pose proof (bv_unsigned_in_range 8 c) as H; unfold bv_modulus in H; exact H).
  step. if_cases HB; cfact HB; try (exfalso; zl).
  step. step.
  step. if_cases HC; cfact HC;
    first [ eapply KE; [zl | weq | weq] | exfalso; zl | step; eapply KL; [zl | weq | weq] ].
Qed.

Lemma ts_call2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (at_call (Z_to_bv 64 0x159e8) sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0 s1 (Z_to_bv 64 1)
               F fc m [] (fun m' => m' = m))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x159d8) fc None m (seg_rom rsegs)).
Proof.
  intros. do 4 step.
  apply evt_done. unfold at_call.
  do 13 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. reflexivity.
Qed.

Lemma slot_bytes : forall m f j b2 b3 b4 b5 b6 b7,
  rw_cells rsegs m f [CB 2 j; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7] ->
  bytes_at rsegs m (f + 2) [b2; b3; b4; b5; b6; b7].
Proof.
  intros m f j b2 b3 b4 b5 b6 b7 [[Hwf Hb] _]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  cbn [cells_bytes cbytes] in Hb.
  change (j ++ [b2] ++ [b3] ++ [b4] ++ [b5] ++ [b6] ++ [b7] ++ []) with (j ++ [b2; b3; b4; b5; b6; b7]) in Hb.
  apply bytes_at_app in Hb. destruct Hb as [_ Hb]. rewrite Hl in Hb. exact Hb.
Qed.

Lemma bytes_at_prefix : forall m a l1 l2, bytes_at rsegs m a (l1 ++ l2) -> bytes_at rsegs m a l1.
Proof. intros m a l1 l2 H. apply bytes_at_app in H. exact (proj1 H). Qed.

Lemma esc_ctrl : forall c, c < 32 -> c <> 9 -> c <> 10 -> c <> 13 ->
  esc c = [92; 117; 48; 48; hexd (c / 16); hexd (c mod 16)].
Proof.
  intros c H1 H2 H3 H4. unfold esc.
  rewrite (proj2 (Z.eqb_neq c 34)) by lia. rewrite (proj2 (Z.eqb_neq c 92)) by lia.
  rewrite (proj2 (Z.eqb_neq c 10)) by lia. rewrite (proj2 (Z.eqb_neq c 9)) by lia.
  rewrite (proj2 (Z.eqb_neq c 13)) by lia. reflexivity.
Qed.

Lemma land_low : forall x k m, m = Z.ones k -> 0 <= k -> 0 <= x < 2 ^ k -> Z.land x m = x.
Proof. intros x k m -> Hk Hx. rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma land_low_mod : forall x, 0 <= x -> Z.land x 15 = x mod 16.
Proof. intros x Hx. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma unsigned_zxb : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof.
  intros b. unfold zxb. apply unsigned_lit.
  pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. lia.
Qed.

Notation hexl := [Z_to_bv 8 48; Z_to_bv 8 49; Z_to_bv 8 50; Z_to_bv 8 51; Z_to_bv 8 52; Z_to_bv 8 53;
                  Z_to_bv 8 54; Z_to_bv 8 55; Z_to_bv 8 56; Z_to_bv 8 57; Z_to_bv 8 97; Z_to_bv 8 98;
                  Z_to_bv 8 99; Z_to_bv 8 100; Z_to_bv 8 101; Z_to_bv 8 102].

Lemma hex_read : forall m a x, bytes_at rsegs m a hexl -> 0 <= x < 16 ->
  ov_read_bytes rsegs m (wa (a + x)) 1 = Some [Z_to_bv 8 (hexd x)].
Proof.
  intros m a x H Hx. rewrite (bytes_at_read rsegs m a hexl x 1 H) by (cbn [length]; lia).
  assert (E : x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/ x = 8 \/ x = 9 \/ x = 10 \/
              x = 11 \/ x = 12 \/ x = 13 \/ x = 14 \/ x = 15) by lia.
  repeat destruct E as [E|E]; subst x; reflexivity.
Qed.

Lemma ts_mid : forall (Q : machine_state -> Prop) ra gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (f p : Z) (c eb : byte) (j0 j1 : list byte),
  0x104a8 + 16 <= f -> f + 112 < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> 1 <= bv_unsigned c -> a1 = zxb eb ->
  rw_cells rsegs m f [CB 2 j0; C1 (Z_to_bv 8 92); CB 5 j1] ->
  munch [(f, f + 8)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  bytes_at rsegs m 0x104a8 hexl ->
  (bv_unsigned c = 34 \/ bv_unsigned c = 92 -> forall (r1 x1 x2 x3 : word) (m' : word -> option byte),
     munch [(f, f + 8)] m0 m' -> wmono rsegs m0 m' ->
     r1 = Z_to_bv 64 0x159d8 -> x1 = Z_to_bv 64 0x102e9 -> x2 = Z_to_bv 64 1 ->
     evt rsegs Q (MS (mkR r1 (Z_to_bv 64 f) gp tp t0 t1 t2 s0 (Z_to_bv 64 p) s0 x1 x2 x3 a4 a5 a6 a7
                          (Z_to_bv 64 0x102e9) (Z_to_bv 64 92) (Z_to_bv 64 9) (Z_to_bv 64 48)
                          (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 34) (Z_to_bv 64 32) (Z_to_bv 64 13)
                          (Z_to_bv 64 10) (Z_to_bv 64 0x104a8) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x154b8) fc None m' (seg_rom rsegs))) ->
  (32 <= bv_unsigned c -> bv_unsigned c <> 34 -> bv_unsigned c <> 92 ->
   forall (r1 x2 x3 : word) (m' : word -> option byte),
     munch [(f, f + 8)] m0 m' -> wmono rsegs m0 m' ->
     r1 = Z_to_bv 64 0x159e8 -> x2 = Z_to_bv 64 1 ->
     evt rsegs Q (MS (mkR r1 (Z_to_bv 64 f) gp tp t0 t1 t2 s0 (Z_to_bv 64 p) s0 (Z_to_bv 64 p) x2 x3 a4 a5 a6 a7
                          (Z_to_bv 64 0x102e9) (Z_to_bv 64 92) (Z_to_bv 64 9) (Z_to_bv 64 48)
                          (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 34) (Z_to_bv 64 32) (Z_to_bv 64 13)
                          (Z_to_bv 64 10) (Z_to_bv 64 0x104a8) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x154b8) fc None m' (seg_rom rsegs))) ->
  (bv_unsigned c < 32 -> forall (r1 x1 x2 x3 : word) (m' : word -> option byte),
     munch [(f, f + 8)] m0 m' -> wmono rsegs m0 m' ->
     bytes_at rsegs m' (f + 2) [Z_to_bv 8 92; eb; Z_to_bv 8 48; Z_to_bv 8 48;
                                Z_to_bv 8 (hexd (bv_unsigned c / 16)); Z_to_bv 8 (hexd (bv_unsigned c mod 16))] ->
     r1 = Z_to_bv 64 0x159e8 -> x1 = Z_to_bv 64 (f + 2) -> x2 = Z_to_bv 64 (if bv_unsigned eb =? 117 then 6 else 2) ->
     evt rsegs Q (MS (mkR r1 (Z_to_bv 64 f) gp tp t0 t1 t2 s0 (Z_to_bv 64 p) s0 x1 x2 x3 a4 a5 a6 a7
                          (Z_to_bv 64 0x102e9) (Z_to_bv 64 92) (Z_to_bv 64 9) (Z_to_bv 64 48)
                          (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 34) (Z_to_bv 64 32) (Z_to_bv 64 13)
                          (Z_to_bv 64 10) (Z_to_bv 64 0x104a8) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x154b8) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 s0 (Z_to_bv 64 p) (zxb c) a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 0x102e9) (Z_to_bv 64 92) (Z_to_bv 64 9) (Z_to_bv 64 48)
                       (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 34) (Z_to_bv 64 32) (Z_to_bv 64 13)
                       (Z_to_bv 64 10) (Z_to_bv 64 0x104a8) t3 t4 t5 t6)
                  F (Z_to_bv 64 0x15990) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m0 m f p c eb j0 j1
    Hf Hf1 Hp Hc E1 RC MU WM MI HX KB KP KC.
  subst a1.
  assert (HZ : 0 <= bv_unsigned c < 256) by (pose proof (bv_unsigned_in_range 8 c) as H; unfold bv_modulus in H; exact H).
  assert (HE : 0 <= bv_unsigned eb < 256) by (pose proof (bv_unsigned_in_range 8 eb) as H; unfold bv_modulus in H; exact H).
  pose proof (hex_read m 0x104a8 (bv_unsigned c / 16) HX ltac:(zl)) as H1.
  pose proof (hex_read m 0x104a8 (bv_unsigned c mod 16) HX ltac:(zl)) as H2.
  clear HX.
  do 5 step.
  rewrite unsigned_zxb.
  rewrite (land_low (bv_unsigned c) 8 255) by (first [reflexivity | lia]).
  rewrite (unsigned_lit (bv_unsigned c)) by lia.
  rewrite (land_low_mod (bv_unsigned c)) by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  step. step.
  do 5 step.
  step. if_cases HC1.
  - cfact HC1. do 4 step.
    eapply KB; [zl | eassumption | eassumption | weq | weq | weq].
  - cfact HC1. step. if_cases HC2.
    + cfact HC2. step. if_cases HC3.
      * cfact HC3. do 4 step.
        eapply KP; [zl | zl | zl | eassumption | eassumption | weq | weq].
      * cfact HC3. step. step. if_cases HC4.
        -- cfact HC4. do 5 step.
           eapply KC; [zl | eassumption | eassumption | | weq | weq | ].
           ++ match goal with H : rw_cells rsegs _ f _ |- _ => exact (slot_bytes _ _ _ _ _ _ _ _ _ H) end.
           ++ rewrite (proj2 (Z.eqb_eq (bv_unsigned eb) 117)) by zl. reflexivity.
        -- cfact HC4. do 6 step.
           eapply KC; [zl | eassumption | eassumption | | weq | weq | ].
           ++ match goal with H : rw_cells rsegs _ f _ |- _ => exact (slot_bytes _ _ _ _ _ _ _ _ _ H) end.
           ++ rewrite (proj2 (Z.eqb_neq (bv_unsigned eb) 117)) by zl. reflexivity.
    + cfact HC2. do 4 step.
      eapply KB; [zl | eassumption | eassumption | weq | weq | weq].
Qed.

Lemma ts_body : forall (Q : machine_state -> Prop) ra gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f p : Z) (c : byte) (j : list byte),
  0x104a8 + 16 <= f -> f + 112 < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> 1 <= bv_unsigned c ->
  rw_cells rsegs m f [CB 8 j] -> mem_inv rsegs m -> bytes_at rsegs m 0x104a8 hexl ->
  (bv_unsigned c = 34 \/ bv_unsigned c = 92 -> forall (r1 x1 x2 x3 : word) (m' : word -> option byte),
     munch [(f, f + 8)] m m' -> wmono rsegs m m' ->
     r1 = Z_to_bv 64 0x159d8 -> x1 = Z_to_bv 64 0x102e9 -> x2 = Z_to_bv 64 1 ->
     evt rsegs Q (MS (mkR r1 (Z_to_bv 64 f) gp tp t0 t1 t2 s0 (Z_to_bv 64 p) s0 x1 x2 x3 a4 a5 a6 a7
                          (Z_to_bv 64 0x102e9) (Z_to_bv 64 92) (Z_to_bv 64 9) (Z_to_bv 64 48)
                          (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 34) (Z_to_bv 64 32) (Z_to_bv 64 13)
                          (Z_to_bv 64 10) (Z_to_bv 64 0x104a8) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x154b8) fc None m' (seg_rom rsegs))) ->
  (32 <= bv_unsigned c -> bv_unsigned c <> 34 -> bv_unsigned c <> 92 ->
   forall (r1 x2 x3 : word) (m' : word -> option byte),
     munch [(f, f + 8)] m m' -> wmono rsegs m m' ->
     r1 = Z_to_bv 64 0x159e8 -> x2 = Z_to_bv 64 1 ->
     evt rsegs Q (MS (mkR r1 (Z_to_bv 64 f) gp tp t0 t1 t2 s0 (Z_to_bv 64 p) s0 (Z_to_bv 64 p) x2 x3 a4 a5 a6 a7
                          (Z_to_bv 64 0x102e9) (Z_to_bv 64 92) (Z_to_bv 64 9) (Z_to_bv 64 48)
                          (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 34) (Z_to_bv 64 32) (Z_to_bv 64 13)
                          (Z_to_bv 64 10) (Z_to_bv 64 0x104a8) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x154b8) fc None m' (seg_rom rsegs))) ->
  (bv_unsigned c < 32 -> forall (r1 x1 x2 x3 : word) (m' : word -> option byte),
     munch [(f, f + 8)] m m' -> wmono rsegs m m' ->
     bytes_at rsegs m' (f + 2) (map (Z_to_bv 8) (esc (bv_unsigned c))) ->
     r1 = Z_to_bv 64 0x159e8 -> x1 = Z_to_bv 64 (f + 2) ->
     x2 = Z_to_bv 64 (Z.of_nat (length (esc (bv_unsigned c)))) ->
     evt rsegs Q (MS (mkR r1 (Z_to_bv 64 f) gp tp t0 t1 t2 s0 (Z_to_bv 64 p) s0 x1 x2 x3 a4 a5 a6 a7
                          (Z_to_bv 64 0x102e9) (Z_to_bv 64 92) (Z_to_bv 64 9) (Z_to_bv 64 48)
                          (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 34) (Z_to_bv 64 32) (Z_to_bv 64 13)
                          (Z_to_bv 64 10) (Z_to_bv 64 0x104a8) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x154b8) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 s0 (Z_to_bv 64 p) (zxb c) a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 0x102e9) (Z_to_bv 64 92) (Z_to_bv 64 9) (Z_to_bv 64 48)
                       (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 34) (Z_to_bv 64 32) (Z_to_bv 64 13)
                       (Z_to_bv 64 10) (Z_to_bv 64 0x104a8) t3 t4 t5 t6)
                  F (Z_to_bv 64 0x15964) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m f p c j
    Hf Hf1 Hp Hc RC MI HX KB KP KC.
  assert (HZ : 0 <= bv_unsigned c < 256) by (pose proof (bv_unsigned_in_range 8 c) as H; unfold bv_modulus in H; exact H).
  pose proof (munch_refl [(f, f + 8)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  step.
  step. if_cases HC1.
  - cfact HC1. step. step.
    eapply ts_mid with (m0 := m) (eb := Z_to_bv 8 116);
      [zl | zl | zl | zl | weq | eassumption | eassumption | eassumption | eassumption | eassumption
      | exact KB | exact KP | ].
    intros Hl r1 x1 x2 x3 m' MU' WM' HB E1 E2 E3. apply (KC Hl r1 x1 x2 x3 m' MU' WM'); [| exact E1 | exact E2 |].
    + replace (bv_unsigned c) with 9 by zl. cbn [esc Z.eqb Pos.eqb map].
      exact (bytes_at_prefix _ _ [_; _] _ HB).
    + rewrite E3. replace (bv_unsigned c) with 9 by zl. reflexivity.
  - cfact HC1. step. if_cases HC2.
    + cfact HC2. step. if_cases HC3.
      * cfact HC3. step.
        eapply ts_mid with (m0 := m) (eb := Z_to_bv 8 114);
          [zl | zl | zl | zl | weq | eassumption | eassumption | eassumption | eassumption | eassumption
          | exact KB | exact KP | ].
        intros Hl r1 x1 x2 x3 m' MU' WM' HB E1 E2 E3. apply (KC Hl r1 x1 x2 x3 m' MU' WM'); [| exact E1 | exact E2 |].
        -- replace (bv_unsigned c) with 13 by zl. cbn [esc Z.eqb Pos.eqb map].
           exact (bytes_at_prefix _ _ [_; _] _ HB).
        -- rewrite E3. replace (bv_unsigned c) with 13 by zl. reflexivity.
      * cfact HC3. step. step.
        eapply ts_mid with (m0 := m) (eb := Z_to_bv 8 117);
          [zl | zl | zl | zl | weq | eassumption | eassumption | eassumption | eassumption | eassumption
          | exact KB | exact KP | ].
        intros Hl r1 x1 x2 x3 m' MU' WM' HB E1 E2 E3. apply (KC Hl r1 x1 x2 x3 m' MU' WM'); [| exact E1 | exact E2 |].
        -- rewrite esc_ctrl by zl. exact HB.
        -- rewrite E3. rewrite esc_ctrl by zl. reflexivity.
    + cfact HC2. step. step.
      eapply ts_mid with (m0 := m) (eb := Z_to_bv 8 110);
        [zl | zl | zl | zl | weq | eassumption | eassumption | eassumption | eassumption | eassumption
        | exact KB | exact KP | ].
      intros Hl r1 x1 x2 x3 m' MU' WM' HB E1 E2 E3. apply (KC Hl r1 x1 x2 x3 m' MU' WM'); [| exact E1 | exact E2 |].
      * replace (bv_unsigned c) with 10 by zl. cbn [esc Z.eqb Pos.eqb map].
        exact (bytes_at_prefix _ _ [_; _] _ HB).
      * rewrite E3. replace (bv_unsigned c) with 10 by zl. reflexivity.
Qed.
