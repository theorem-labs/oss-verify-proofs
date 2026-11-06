From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge FP Image.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import printf_facts_c snprintf_c reac_rate_drivable_csv_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import dcsv_lib.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg RateCsv.
Import ListNotations.
Open Scope Z_scope.

(** The states and invariants of the walk of reac_rate_drivable_csv (UBSan image, 0x14dcc). S0 is the entry sp;
    the frame is [S0 - 176, S0): sp + 0 .. 7 unused, buflen at S0 - 168, buf at S0 - 160, cell[16] at S0 - 152,
    tmp[32] at S0 - 136, the caller's s11 .. s0 and ra at S0 - 104 .. S0 - 1. *)

(** The saved registers, as the prologue stores them (s11 at sp + 0x48 .. ra at sp + 0xa8). *)
Definition dsv (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma dsv_size : forall ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11,
  cells_size (dsv ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) = 104%nat.
Proof. reflexivity. Qed.

(** What no pass of the loop writes: the frame's low words (buflen, buf), the saved registers, the guard cells and
    the caller's buffer. *)
Definition dkeep (S0 lo n buf : Z) (sv : list cell) (canary : word) (junk : list byte) (m : word -> option byte)
    : Prop :=
  (exists j0, rw_cells rsegs m (S0 + -176) [CB 8 j0; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 buf)]) /\
  rw_cells rsegs m (S0 + -104) sv /\
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) /\ bytes_at rsegs m GUARD (le8 canary) /\
  (0 < n -> rw_cells rsegs m buf [CB (Z.to_nat n) junk]).

(** Memory at the loop head after i passes: tmp holds csv_prefix mask i and its NUL. *)
Definition dmem (S0 lo n buf : Z) (mask : word) (sv : list cell) (m0 : word -> option byte) (canary : word)
    (junk : list byte) (i : nat) (m : word -> option byte) : Prop :=
  dkeep S0 lo n buf sv canary junk m /\
  stk rsegs m lo (S0 + -176) /\ stk rsegs m (S0 + -152) (S0 + -104) /\
  bytes_at rsegs m (S0 + -136) (csv_bytes (csv_prefix (bv_unsigned mask) i ++ [0])) /\
  mem_inv rsegs m /\ wmono rsegs m0 m /\ munch [(lo, S0)] m0 m.

(** The loop-head invariant: s2 = len, s6 = r6 (passes left), s9 = r9 (ordered + 4 i). *)
Definition dok (S0 lo n buf : Z) (mask : word) (sv : list cell) (m0 : word -> option byte) (canary : word)
    (junk : list byte) (F0 : bvmap 5 word) (i : nat) (len r6 r9 : Z) (m : word -> option byte) (F : bvmap 5 word)
    (fc : bv 32) : Prop :=
  len = Z.of_nat (length (csv_prefix (bv_unsigned mask) i)) /\ r6 = 3 - Z.of_nat i /\
  r9 = 0x10644 + 4 * Z.of_nat i /\ dmem S0 lo n buf mask sv m0 canary junk i m /\ frm0 fc /\
  (forall k : reg, bv_unsigned k <> 10 -> reg_get F k = reg_get F0 k).

(** The machine state in the loop: s0 = x8 (96000 in the loop), s3 = mask, s4 = "%s%d", s5 = 48000, s7 = "",
    s8 = ~(sp + 0x28), s10 = 44100, s11 = ",". *)
Definition dst (gp tp mask : word) (S0 : Z) (pc len r6 r9 : Z) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
    : machine_state :=
  MS (mkR x1 (Z_to_bv 64 (S0 + -176)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
          (Z_to_bv 64 len) mask (Z_to_bv 64 0x10470) (Z_to_bv 64 48000) (Z_to_bv 64 r6) (Z_to_bv 64 0x1032e)
          (Z_to_bv 64 (18446744073709551615 - (S0 + -136))) (Z_to_bv 64 r9) (Z_to_bv 64 44100)
          (Z_to_bv 64 0x10373) x28 x29 x30 x31)
     F (Z_to_bv 64 pc) fc None m (seg_rom rsegs).

(** The contract's post, with sp = S0. *)
Definition dpost (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F0 : bvmap 5 word)
    (m0 : word -> option byte) (lo S0 buf n : Z) (L : list Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word)
                    (fc' : bv 32) (m' : word -> option byte),
    ms' = MS (mkR ra (Z_to_bv 64 S0) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (Z.of_nat (length L))) a1' a2' a3' a4' a5'
                  a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F' (ret_pc ra) fc' None m' (seg_rom rsegs) /\
    frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F0 k) /\
    wmono rsegs m0 m' /\ mem_inv rsegs m' /\ MemNorm.task_mem rsegs m' /\ stk rsegs m' lo S0 /\
    (n = 0 -> munch [(lo, S0)] m0 m') /\
    (0 < n -> munch [(lo, S0); (buf, buf + n)] m0 m' /\ bytes_at rsegs m' buf (csv_bytes (csv_cut L n ++ [0]))).

(** [dkeep] survives a write footprint inside [lo, S0 - 176) and cell + tmp. *)
Lemma dkeep_tr : forall S0 lo n buf sv canary junk W m m',
  dkeep S0 lo n buf sv canary junk m -> munch W m m' -> wmono rsegs m m' ->
  (forall y, ~ outside W y -> lo <= y < S0 + -176 \/ S0 + -152 <= y < S0 + -104) ->
  cells_size sv = 104%nat -> 0x50cc8 <= lo -> lo + 6112 <= S0 -> (0 < n -> buf + n <= lo \/ S0 <= buf) ->
  dkeep S0 lo n buf sv canary junk m'.
Proof.
  intros S0 lo n buf sv canary junk W m m' ((j0 & FA) & FS & GG & GD & HB) MU WM HW Hsv HI HK HBL.
  assert (O : forall x, ~ (lo <= x < S0 + -176 \/ S0 + -152 <= x < S0 + -104) -> outside W x).
  { intros x Hx. exact (outside_of W (fun y => lo <= y < S0 + -176 \/ S0 + -152 <= y < S0 + -104) x HW Hx). }
  unfold dkeep, GOT_GUARD, GUARD in *.
  split; [exists j0; eapply rw_cells_tr; [exact FA | exact MU | exact WM |];
          intros x Hx; apply O; cbn [cells_size csize] in Hx; lia|].
  split; [eapply rw_cells_tr; [exact FS | exact MU | exact WM |]; intros x Hx; apply O; rewrite Hsv in Hx; lia|].
  split; [eapply bytes_at_tr; [exact GG | exact MU |]; intros x Hx; apply O; rewrite length_le8 in Hx; lia|].
  split; [eapply bytes_at_tr; [exact GD | exact MU |]; intros x Hx; apply O; rewrite length_le8 in Hx; lia|].
  intros Hn. specialize (HBL Hn). eapply rw_cells_tr; [exact (HB Hn) | exact MU | exact WM |].
  intros x Hx; apply O; cbn [cells_size csize] in Hx; lia.
Qed.

Lemma csv_prefix_clear : forall mask i, Z.testbit mask (Z.of_nat i) = false ->
  csv_prefix mask (S i) = csv_prefix mask i.
Proof. intros mask i H. rewrite csv_prefix_S, H. reflexivity. Qed.

Lemma csv_prefix_set : forall mask i, Z.testbit mask (Z.of_nat i) = true ->
  csv_prefix mask (S i) =
  csv_prefix mask i ++ sep_str (Z.of_nat (length (csv_prefix mask i))) ++ csv_dec (nth i closed_list 0).
Proof. intros mask i H. rewrite csv_prefix_S, H, sep_str_prefix. reflexivity. Qed.

Lemma dmem_same : forall S0 lo n buf mask sv m0 canary junk i j m,
  csv_prefix (bv_unsigned mask) j = csv_prefix (bv_unsigned mask) i ->
  dmem S0 lo n buf mask sv m0 canary junk i m -> dmem S0 lo n buf mask sv m0 canary junk j m.
Proof. intros S0 lo n buf mask sv m0 canary junk i j m E D. unfold dmem in *. rewrite E. exact D. Qed.
