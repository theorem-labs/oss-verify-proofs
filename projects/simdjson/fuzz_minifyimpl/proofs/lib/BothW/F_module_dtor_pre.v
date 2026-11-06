(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg F_syscalls StdioFiles Stdio_kit MonadF F_memset AExit F_stdio_exit.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StrwF SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require DrvAgree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition SHOFF : Z := 0x7fff8000.
Definition shd (a : Z) : Z := SHOFF + Z.shiftr a 3.
Definition shn (l : Z) : Z := Z.shiftr l 3.

(* [comment removed for export] *)
End CANSEC1.
Ltac sort_lits :=
  repeat (match goal with H : rw_cells bsegs _ (Zpos ?p) _ |- _ =>
            tryif (match goal with H' : rw_cells bsegs _ (Zpos ?p') _ |- _ =>
                     lazymatch eval vm_compute in (Z.ltb (Zpos p') (Zpos p)) with true => idtac | false => fail end end)
            then fail
            else (move H at bottom; lazymatch type of H with ?T => change T with (sf_hide T) in H end)
          end); sf_unhide.
Ltac hstep := sort_lits; zstep; fix_lit_store.
Ltac astep := hstep; try (first [if_true | if_false]).
Ltac at_pc p := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
Ltac steps_to p := repeat (tryif at_pc p then fail else astep).

Section CANSEC2. Context {rc : runConstT}.
Lemma unsigned_lit8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mdtor_rt (m : mem) : Prop :=
     rw_cells bsegs m 0x173cb8 [C8 (Z_to_bv 64 0x20cf20)]                                        (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x173cc8 [C8 (Z_to_bv 64 0x20efa8); C8 (Z_to_bv 64 0x17ac78); C8 (Z_to_bv 64 0x17d478);
                                C8 (Z_to_bv 64 0x17e168); C8 (Z_to_bv 64 0x17e170); C8 (Z_to_bv 64 0x17e160)]  (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x173cf8 [C8 (Z_to_bv 64 0x175d20)]                                        (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x175d18 [C8 (Z_to_bv 64 0x165dd8); C8 (Z_to_bv 64 0x1661dc)]              (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x17d478 [C8 (Z_to_bv 64 0x7fff8000)]                                      (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x17e158 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]                              (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x17ccdc [C1 (Z_to_bv 8 1)]                                                (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x20f020 [C8 (Z_to_bv 64 18446744073709551615)]                          (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x17ac90 [C4 (Z_to_bv 64 1)].                                              (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rt_clear (iv : Z * Z) : Prop :=
  let (lo, hi) := iv in
  lo <= hi /\
  (hi <= 0x173cb8 \/ (0x173d00 <= lo /\ hi <= 0x175d18) \/ (0x175d28 <= lo /\ hi <= 0x17ac90) \/ (0x17ac94 <= lo /\ hi <= 0x17ccdc)
   \/ (0x17ccdd <= lo /\ hi <= 0x17d478) \/ (0x17d480 <= lo /\ hi <= 0x17e158) \/ (0x17e15a <= lo /\ hi <= 0x20f020) \/ 0x20f028 <= lo).

Lemma mdtor_rt_frame : forall m m' W,
  mdtor_rt m -> munch W m m' -> wmono bsegs m m' ->
  Forall rt_clear W -> mdtor_rt m'.
Proof.
  intros m m' W PC MU WM HW.
  assert (D : forall A n, 0 <= n ->
             ((0x173cb8 <= A /\ A + n <= 0x173d00) \/ (0x175d18 <= A /\ A + n <= 0x175d28) \/ (0x17ac90 <= A /\ A + n <= 0x17ac94)
              \/ (0x17ccdc <= A /\ A + n <= 0x17ccdd) \/ (0x17d478 <= A /\ A + n <= 0x17d480) \/ (0x17e158 <= A /\ A + n <= 0x17e15a)
              \/ (0x20f020 <= A /\ A + n <= 0x20f028)) -> disjoint_from W A n).
  { intros A n Hn HA. clear MU. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| exact IH]. }
  unfold mdtor_rt in *.
  destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  repeat match goal with |- _ /\ _ => split end; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply D; cbn; lia]).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gdesc (m : mem) (d beg sz swr nm md odr : Z) : Prop :=
     rw_cells bsegs m d [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 swr); C8 (Z_to_bv 64 nm); C8 (Z_to_bv 64 md);
                         C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 odr)]
  /\ rw_cells bsegs m (d + 16) [C1 (Z_to_bv 8 (swr mod 256))].

(* [comment removed for export] *)
Definition GLOBALS : list (Z * Z * Z * Z * Z * Z * Z) :=
  [(0x178bd0, 0x23720, 53, 96, 0x1dc98, 0x236db, 18446744073709551615);
   (0x178c10, 0x23780, 10, 32, 0x15055, 0x236db, 18446744073709551615);
   (0x178c50, 0x237a0, 7, 32, 0x1505c, 0x236db, 18446744073709551615);
   (0x178c90, 0x237c0, 13, 32, 0x1162c, 0x236db, 18446744073709551615);
   (0x178cd0, 0x237e0, 55, 96, 0x19b0e, 0x236db, 18446744073709551615);
   (0x178d10, 0x23840, 11, 32, 0x19b16, 0x236db, 18446744073709551615);
   (0x178d50, 0x23e20, 18, 64, 0x1dc98, 0x2c620, 18446744073709551615);
   (0x178d90, 0x23e60, 56, 96, 0x20a31, 0x2c620, 18446744073709551615);
   (0x178dd0, 0x23ec0, 67, 128, 0x22d3c, 0x2c620, 18446744073709551615);
   (0x178e10, 0x23f40, 157, 192, 0x15055, 0x2c620, 18446744073709551615);
   (0x178e50, 0x24000, 81, 128, 0x13db5, 0x2c620, 18446744073709551615);
   (0x178e90, 0x24080, 45, 96, 0x1eda1, 0x2c620, 18446744073709551615);
   (0x178ed0, 0x240e0, 73, 128, 0x19b62, 0x2c620, 18446744073709551615);
   (0x178f10, 0x24160, 73, 128, 0x1bdaf, 0x2c620, 18446744073709551615);
   (0x178f50, 0x241e0, 73, 128, 0x11634, 0x2c620, 18446744073709551615);
   (0x178f90, 0x24260, 45, 96, 0x173b1, 0x2c620, 18446744073709551615);
   (0x178fd0, 0x242c0, 73, 128, 0x21dfe, 0x2c620, 18446744073709551615);
   (0x179010, 0x24340, 41, 96, 0x1163b, 0x2c620, 18446744073709551615);
   (0x179050, 0x243a0, 29, 64, 0x1b666, 0x2c620, 18446744073709551615);
   (0x179090, 0x243e0, 21, 64, 0x21e06, 0x2c620, 18446744073709551615);
   (0x1790d0, 0x24420, 96, 128, 0x1fdcc, 0x2c620, 18446744073709551615);
   (0x179110, 0x244a0, 55, 96, 0x1dc9d, 0x2c620, 18446744073709551615);
   (0x179150, 0x24500, 172, 224, 0x1ae2f, 0x2c620, 18446744073709551615);
   (0x179190, 0x245e0, 67, 128, 0x1d34c, 0x2c620, 18446744073709551615);
   (0x1791d0, 0x24660, 97, 160, 0x11e7c, 0x2c620, 18446744073709551615);
   (0x179210, 0x24700, 95, 128, 0x11e84, 0x2c620, 18446744073709551615);
   (0x179250, 0x24780, 72, 128, 0x18fc1, 0x2c620, 18446744073709551615);
   (0x179290, 0x24800, 34, 96, 0x1b66e, 0x2c620, 18446744073709551615);
   (0x1792d0, 0x24860, 51, 96, 0x1505c, 0x2c620, 18446744073709551615);
   (0x179310, 0x248c0, 51, 96, 0x144d3, 0x2c620, 18446744073709551615);
   (0x179350, 0x24920, 108, 160, 0x13dbc, 0x2c620, 18446744073709551615);
   (0x179390, 0x249c0, 77, 128, 0x17d9f, 0x2c620, 18446744073709551615);
   (0x1793d0, 0x24a40, 97, 160, 0x10bb3, 0x2c620, 18446744073709551615);
   (0x179410, 0x24ae0, 207, 256, 0x18fc9, 0x2c620, 18446744073709551615);
   (0x179450, 0x24be0, 132, 192, 0x18526, 0x2c620, 18446744073709551615);
   (0x179490, 0x24ca0, 177, 224, 0x10bbb, 0x2c620, 18446744073709551615);
   (0x1794d0, 0x24d80, 63, 96, 0x13dc4, 0x2c620, 18446744073709551615);
   (0x179510, 0x24de0, 65, 128, 0x11643, 0x2c620, 18446744073709551615);
   (0x179550, 0x24e60, 78, 128, 0x127a1, 0x2c620, 18446744073709551615);
   (0x179590, 0x24ee0, 256, 320, 0x22d43, 0x2c620, 7011585);
   (0x1795d0, 0x25020, 3544, 4416, 0x1b676, 0x2c620, 7011586);
   (0x179610, 0x26160, 184, 224, 0x21e0e, 0x2c620, 7011587);
   (0x179650, 0x26240, 10416, 13024, 0x17da7, 0x2c620, 7011588);
   (0x179690, 0x29520, 9, 32, 0x18fd1, 0x2c620, 18446744073709551615);
   (0x1796d0, 0x29540, 37, 96, 0x11ed1, 0x2c620, 7011591);
   (0x179710, 0x295c0, 48, 96, 0x173b8, 0x2c620, 7011594);
   (0x179750, 0x29660, 12, 32, 0x18fd9, 0x2c620, 18446744073709551615);
   (0x179790, 0x29680, 48, 96, 0x1162c, 0x2c620, 18446744073709551615);
   (0x1797d0, 0x29720, 32, 64, 0x22d97, 0x2c620, 18446744073709551615);
   (0x179810, 0x29760, 256, 320, 0x20a38, 0x2c620, 18446744073709551615);
   (0x179850, 0x298a0, 256, 320, 0x17457, 0x2c620, 18446744073709551615);
   (0x179890, 0x2c2a0, 160, 192, 0x1fe4e, 0x2c620, 18446744073709551615);
   (0x1798d0, 0x2c5e0, 1, 32, 0x1fe78, 0x2c620, 18446744073709551615);
   (0x179910, 0x2c600, 1, 32, 0x1f5d5, 0x2c620, 18446744073709551615);
   (0x179950, 0x16dd60, 528, 672, 0x1a321, 0x2c620, 7011584);
   (0x179990, 0x16e000, 64, 96, 0x1b699, 0x2c620, 7011589);
   (0x1799d0, 0x16e060, 24, 64, 0x127a9, 0x2c620, 7011590);
   (0x179a10, 0x16e0c0, 96, 128, 0x1fdd4, 0x2c620, 7011592);
   (0x179a50, 0x16e140, 24, 64, 0x144db, 0x2c620, 7011593);
   (0x179a90, 0x178460, 768, 960, 0x22d78, 0x2c620, 18446744073709551615);
   (0x179ad0, 0x6afb00, 24, 64, 0x1dc70, 0x236db, 18446744073709551615);
   (0x179b10, 0x6afb40, 8, 32, 0x12766, 0x236db, 18446744073709551615);
   (0x179b50, 0x6afb60, 48, 96, 0x1595f, 0x2c620, 18446744073709551615);
   (0x179b90, 0x6afbc0, 8, 32, 0x15064, 0x2c620, 18446744073709551615);
   (0x179bd0, 0x6afbe0, 1, 32, 0x11e8c, 0x2c620, 18446744073709551615);
   (0x179c10, 0x6afc00, 8, 32, 0x1f57d, 0x2c620, 18446744073709551615);
   (0x179c50, 0x6afc20, 16, 32, 0x173f8, 0x2c620, 18446744073709551615);
   (0x179c90, 0x6afc40, 8, 32, 0x13dcc, 0x2c620, 18446744073709551615);
   (0x179cd0, 0x6afc60, 8, 32, 0x127d9, 0x2c620, 18446744073709551615);
   (0x179d10, 0x6afc80, 48, 96, 0x1fe0d, 0x2c620, 18446744073709551615);
   (0x179d50, 0x6afce0, 8, 32, 0x1d354, 0x2c620, 18446744073709551615)]%Z.
Definition gdesc_t (m : mem) (g : Z * Z * Z * Z * Z * Z * Z) : Prop :=
  let '(d, beg, sz, swr, nm, md, odr) := g in gdesc m d beg sz swr nm md odr.
(* [comment removed for export] *)
Definition GODRS : list Z := [0x6afd01; 0x6afd02; 0x6afd03; 0x6afd04; 0x6afd07; 0x6afd0a; 0x6afd00; 0x6afd05; 0x6afd06; 0x6afd08; 0x6afd09]%Z.
(* [comment removed for export] *)
Definition GSHADOWS : list (Z * Z) :=
  [(0x7fffc6e4, 12);
   (0x7fffc6f0, 4);
   (0x7fffc6f4, 4);
   (0x7fffc6f8, 4);
   (0x7fffc6fc, 12);
   (0x7fffc708, 4);
   (0x7fffc7c4, 8);
   (0x7fffc7cc, 12);
   (0x7fffc7d8, 16);
   (0x7fffc7e8, 24);
   (0x7fffc800, 16);
   (0x7fffc810, 12);
   (0x7fffc81c, 16);
   (0x7fffc82c, 16);
   (0x7fffc83c, 16);
   (0x7fffc84c, 12);
   (0x7fffc858, 16);
   (0x7fffc868, 12);
   (0x7fffc874, 8);
   (0x7fffc87c, 8);
   (0x7fffc884, 16);
   (0x7fffc894, 12);
   (0x7fffc8a0, 28);
   (0x7fffc8bc, 16);
   (0x7fffc8cc, 20);
   (0x7fffc8e0, 16);
   (0x7fffc8f0, 16);
   (0x7fffc900, 12);
   (0x7fffc90c, 12);
   (0x7fffc918, 12);
   (0x7fffc924, 20);
   (0x7fffc938, 16);
   (0x7fffc948, 20);
   (0x7fffc95c, 32);
   (0x7fffc97c, 24);
   (0x7fffc994, 28);
   (0x7fffc9b0, 12);
   (0x7fffc9bc, 16);
   (0x7fffc9cc, 16);
   (0x7fffc9dc, 40);
   (0x7fffca04, 552);
   (0x7fffcc2c, 28);
   (0x7fffcc48, 1628);
   (0x7fffd2a4, 4);
   (0x7fffd2a8, 12);
   (0x7fffd2b8, 12);
   (0x7fffd2cc, 4);
   (0x7fffd2d0, 12);
   (0x7fffd2e4, 8);
   (0x7fffd2ec, 40);
   (0x7fffd314, 40);
   (0x7fffd854, 24);
   (0x7fffd8bc, 4);
   (0x7fffd8c0, 4);
   (0x80025bac, 84);
   (0x80025c00, 12);
   (0x80025c0c, 8);
   (0x80025c18, 16);
   (0x80025c28, 8);
   (0x8002708c, 120);
   (0x800cdf60, 8);
   (0x800cdf68, 4);
   (0x800cdf6c, 12);
   (0x800cdf78, 4);
   (0x800cdf7c, 4);
   (0x800cdf80, 4);
   (0x800cdf84, 4);
   (0x800cdf88, 4);
   (0x800cdf8c, 4);
   (0x800cdf90, 12);
   (0x800cdf9c, 4)]%Z.
Definition GARR_SH : Z := 0x8002717a.       (* [comment removed for export] *)

Definition mdtor_pre (m : mem) : Prop :=
     mdtor_rt m
  /\ rw_cells bsegs m 0x174998 [C8 (Z_to_bv 64 0x178bd0); C8 (Z_to_bv 64 0x179d90)]     (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x179dc0 [C8 (Z_to_bv 64 1)]                                     (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x17ad30 [C8 (Z_to_bv 64 0)]                                     (* [comment removed for export] *)
  /\ Forall (gdesc_t m) GLOBALS
  /\ Forall (fun o => exists b, rw_cells bsegs m o [C1 b]) GODRS
  /\ Forall (fun p => exists j, rw_cells bsegs m (fst p) [CB (Z.to_nat (snd p)) j]) GSHADOWS
  /\ (exists j, rw_cells bsegs m GARR_SH [CB 568 j]).

Lemma mdtor_pre_frame : forall sp m m',
  mdtor_pre m -> KHIGH <= sp - 48 - MDTOR_DEPTH -> munch (AEXIT_W1 sp) m m' -> wmono bsegs m m' -> mdtor_pre m'.
Proof.
  intros sp m m' P KH MU WM. unfold KHIGH, MDTOR_DEPTH in KH.
  assert (D : forall A n, 0 <= n -> A + n <= 0x800d2800 -> 0x6d211c <= A \/ (0x179e11 <= A /\ A + n <= 0x6d1ef8) \/ A + n <= 0x179e10 ->
              disjoint_from (AEXIT_W1 sp) A n).
  { intros A n Hn HA HO. unfold AEXIT_W1, MDTOR_DEPTH. cbn. lia. }
  unfold mdtor_pre in *.
  destruct P as (RT & G1 & G2 & G3 & GL & OD & SHS & [j5 S5]).
  assert (RT' : mdtor_rt m').
  { eapply mdtor_rt_frame; [exact RT | exact MU | exact WM | ]. unfold AEXIT_W1, MDTOR_DEPTH.
    repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
  refine (conj RT' _).
  split; [eapply rw_cells_transport; [exact G1 | exact MU | exact WM | apply D; cbn; lia]|].
  split; [eapply rw_cells_transport; [exact G2 | exact MU | exact WM | apply D; cbn; lia]|].
  split; [eapply rw_cells_transport; [exact G3 | exact MU | exact WM | apply D; cbn; lia]|].
  split.
  { unfold GLOBALS in *.
    repeat lazymatch goal with
    | |- Forall _ (_ :: _) =>
        let X := fresh "X" in pose proof (Forall_inv GL) as X; apply Forall_inv_tail in GL;
        apply Forall_cons;
        [ unfold gdesc_t, gdesc in X |- *;
          let X1 := fresh "XA" in let X2 := fresh "XB" in destruct X as [X1 X2];
          split; [eapply rw_cells_transport; [exact X1 | exact MU | exact WM | apply D; cbn; lia] | eapply rw_cells_transport; [exact X2 | exact MU | exact WM | apply D; cbn; lia]] | clear X ]
    | |- Forall _ [] => apply Forall_nil
    end. }
  split.
  { unfold GODRS in *.
    repeat lazymatch goal with
    | |- Forall _ (_ :: _) =>
        let X := fresh "X" in pose proof (Forall_inv OD) as X; apply Forall_inv_tail in OD;
        apply Forall_cons;
        [ let b := fresh "b" in let Y := fresh "Y" in destruct X as [b Y]; exists b;
          eapply rw_cells_transport; [exact Y | exact MU | exact WM | apply D; cbn; lia] | clear X ]
    | |- Forall _ [] => apply Forall_nil
    end. }
  split.
  { unfold GSHADOWS in *.
    repeat lazymatch goal with
    | |- Forall _ (_ :: _) =>
        let X := fresh "X" in pose proof (Forall_inv SHS) as X; apply Forall_inv_tail in SHS;
        apply Forall_cons;
        [ cbn [fst snd] in X |- *; let j := fresh "j" in let Y := fresh "Y" in destruct X as [j Y]; exists j;
          eapply rw_cells_transport; [exact Y | exact MU | exact WM | apply D; cbn [disjoint_from cells_size csize]; rewrite ?Nat2Z.inj_add, ?Z2Nat.id by lia; cbn; lia] | clear X ]
    | |- Forall _ [] => apply Forall_nil
    end. }
  exists j5. unfold GARR_SH in *. eapply rw_cells_transport; [exact S5 | exact MU | exact WM | apply D; cbn; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mdtor_stat (m : mem) : Prop :=
     rw_cells bsegs m 0x179dc0 [C8 (Z_to_bv 64 1)]
  /\ rw_cells bsegs m 0x17ad30 [C8 (Z_to_bv 64 0)]
  /\ Forall (gdesc_t m) GLOBALS
  /\ Forall (fun o => exists b, rw_cells bsegs m o [C1 b]) GODRS
  /\ Forall (fun p => exists j, rw_cells bsegs m (fst p) [CB (Z.to_nat (snd p)) j]) GSHADOWS
  /\ (exists j, rw_cells bsegs m GARR_SH [CB 568 j]).
Lemma mdtor_pre_of_stat : forall m, mdtor_rt m -> rw_cells bsegs m 0x174998 [C8 (Z_to_bv 64 0x178bd0); C8 (Z_to_bv 64 0x179d90)] -> mdtor_stat m -> mdtor_pre m.
Proof. intros m RT G (A & B & C & D & E & F). exact (conj RT (conj G (conj A (conj B (conj C (conj D (conj E F))))))). Qed.
Lemma mdtor_stat_of_pre : forall m, mdtor_pre m -> mdtor_stat m.
Proof. intros m (_ & _ & A & B & C & D & E & F). exact (conj A (conj B (conj C (conj D (conj E F))))). Qed.

Definition mdtor_stat_app (a : Z) : Prop :=
  (0x178bd0 <= a < 0x179d90) \/ (0x179dc0 <= a < 0x179dc0 + 8) \/ (0x17ad30 <= a < 0x17ad30 + 8) \/ (0x6afd00 <= a < 0x6afd0b).
Definition mdtor_stat_sh (a : Z) : Prop :=
  (0x7fffc6e4 <= a < 0x7fffd33c) \/ (0x7fffd854 <= a < 0x7fffd8c4) \/ (0x80025bac <= a < 0x80025c30) \/ (0x8002708c <= a < 0x80027104) \/ (0x800cdf60 <= a < 0x800cdfa0) \/ (0x8002717a <= a < 0x800273b2).
Lemma mdtor_stat_magree : forall (P : Z -> Prop) m m',
  DrvAgree.magree bsegs P m m' -> (forall a, mdtor_stat_app a \/ mdtor_stat_sh a -> P a) -> mdtor_stat m -> mdtor_stat m'.
Proof.
  intros P m m' AG HP (G2 & G3 & GL & OD & SHS & [j5 S5]).
  assert (HA : forall a, mdtor_stat_app a -> P a) by (intros a H; apply HP; left; exact H).
  assert (HS : forall a, mdtor_stat_sh a -> P a) by (intros a H; apply HP; right; exact H).
  unfold mdtor_stat.
  split; [eapply DrvAgree.rw_cells_magree; [exact AG | exact G2 | intros a Ha; apply HA; unfold mdtor_stat_app; cbn in Ha; lia]|].
  split; [eapply DrvAgree.rw_cells_magree; [exact AG | exact G3 | intros a Ha; apply HA; unfold mdtor_stat_app; cbn in Ha; lia]|].
  split.
  { unfold GLOBALS in *.
    repeat lazymatch goal with
    | |- Forall _ (_ :: _) =>
        let X := fresh "X" in pose proof (Forall_inv GL) as X; apply Forall_inv_tail in GL;
        apply Forall_cons;
        [ unfold gdesc_t, gdesc in X |- *;
          let X1 := fresh "XA" in let X2 := fresh "XB" in destruct X as [X1 X2];
          split; [eapply DrvAgree.rw_cells_magree; [exact AG | exact X1 | intros a Ha; apply HA; unfold mdtor_stat_app; cbn in Ha; lia]
                 | eapply DrvAgree.rw_cells_magree; [exact AG | exact X2 | intros a Ha; apply HA; unfold mdtor_stat_app; cbn in Ha; lia]] | clear X ]
    | |- Forall _ [] => apply Forall_nil
    end. }
  split.
  { unfold GODRS in *.
    repeat lazymatch goal with
    | |- Forall _ (_ :: _) =>
        let X := fresh "X" in pose proof (Forall_inv OD) as X; apply Forall_inv_tail in OD;
        apply Forall_cons;
        [ let b := fresh "b" in let Y := fresh "Y" in destruct X as [b Y]; exists b;
          eapply DrvAgree.rw_cells_magree; [exact AG | exact Y | intros a Ha; apply HA; unfold mdtor_stat_app; cbn in Ha; lia] | clear X ]
    | |- Forall _ [] => apply Forall_nil
    end. }
  split.
  { unfold GSHADOWS in *.
    repeat lazymatch goal with
    | |- Forall _ (_ :: _) =>
        let X := fresh "X" in pose proof (Forall_inv SHS) as X; apply Forall_inv_tail in SHS;
        apply Forall_cons;
        [ cbn [fst snd] in X |- *; let j := fresh "j" in let Y := fresh "Y" in destruct X as [j Y]; exists j;
          eapply DrvAgree.rw_cells_magree; [exact AG | exact Y | intros a Ha; apply HS; unfold mdtor_stat_sh;
            cbn [cells_size csize] in Ha; rewrite ?Nat.add_0_r, ?Z2Nat.id in Ha by lia; lia] | clear X ]
    | |- Forall _ [] => apply Forall_nil
    end. }
  exists j5. unfold GARR_SH in *. eapply DrvAgree.rw_cells_magree; [exact AG | exact S5 | intros a Ha; apply HS; unfold mdtor_stat_sh; cbn in Ha; lia].
Qed.
End CANSEC2.
