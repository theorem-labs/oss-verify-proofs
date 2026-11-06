(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg F_syscalls StdioFiles Stdio_kit MonadF F_memset AExit F_stdio_exit.
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
  repeat (match goal with H : rw_cells asegs _ (Zpos ?p) _ |- _ =>
            tryif (match goal with H' : rw_cells asegs _ (Zpos ?p') _ |- _ =>
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
     rw_cells asegs m 0x166ff8 [C8 (Z_to_bv 64 0x1ffe60)]                                        (* [comment removed for export] *)
  /\ rw_cells asegs m 0x167008 [C8 (Z_to_bv 64 0x201ee8); C8 (Z_to_bv 64 0x16dbb8); C8 (Z_to_bv 64 0x1703b8);
                                C8 (Z_to_bv 64 0x1710a8); C8 (Z_to_bv 64 0x1710b0); C8 (Z_to_bv 64 0x1710a0)]  (* [comment removed for export] *)
  /\ rw_cells asegs m 0x167038 [C8 (Z_to_bv 64 0x169060)]                                        (* [comment removed for export] *)
  /\ rw_cells asegs m 0x169058 [C8 (Z_to_bv 64 0x159104); C8 (Z_to_bv 64 0x159508)]              (* [comment removed for export] *)
  /\ rw_cells asegs m 0x1703b8 [C8 (Z_to_bv 64 0x7fff8000)]                                      (* [comment removed for export] *)
  /\ rw_cells asegs m 0x171098 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]                              (* [comment removed for export] *)
  /\ rw_cells asegs m 0x16fc1c [C1 (Z_to_bv 8 1)]                                                (* [comment removed for export] *)
  /\ rw_cells asegs m 0x201f60 [C8 (Z_to_bv 64 18446744073709551615)]                          (* [comment removed for export] *)
  /\ rw_cells asegs m 0x16dbd0 [C4 (Z_to_bv 64 1)].                                              (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rt_clear (iv : Z * Z) : Prop :=
  let (lo, hi) := iv in
  lo <= hi /\
  (hi <= 0x166ff8 \/ (0x167040 <= lo /\ hi <= 0x169058) \/ (0x169068 <= lo /\ hi <= 0x16dbd0) \/ (0x16dbd4 <= lo /\ hi <= 0x16fc1c)
   \/ (0x16fc1d <= lo /\ hi <= 0x1703b8) \/ (0x1703c0 <= lo /\ hi <= 0x171098) \/ (0x17109a <= lo /\ hi <= 0x201f60) \/ 0x201f68 <= lo).

Lemma mdtor_rt_frame : forall m m' W,
  mdtor_rt m -> munch W m m' -> wmono asegs m m' ->
  Forall rt_clear W -> mdtor_rt m'.
Proof.
  intros m m' W PC MU WM HW.
  assert (D : forall A n, 0 <= n ->
             ((0x166ff8 <= A /\ A + n <= 0x167040) \/ (0x169058 <= A /\ A + n <= 0x169068) \/ (0x16dbd0 <= A /\ A + n <= 0x16dbd4)
              \/ (0x16fc1c <= A /\ A + n <= 0x16fc1d) \/ (0x1703b8 <= A /\ A + n <= 0x1703c0) \/ (0x171098 <= A /\ A + n <= 0x17109a)
              \/ (0x201f60 <= A /\ A + n <= 0x201f68)) -> disjoint_from W A n).
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
     rw_cells asegs m d [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 swr); C8 (Z_to_bv 64 nm); C8 (Z_to_bv 64 md);
                         C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 odr)]
  /\ rw_cells asegs m (d + 16) [C1 (Z_to_bv 8 (swr mod 256))].

(* [comment removed for export] *)
Definition GLOBALS : list (Z * Z * Z * Z * Z * Z * Z) :=
  [(0x16bb40, 0x23680, 53, 96, 0x1dd8e, 0x23820, 18446744073709551615);
   (0x16bb80, 0x236e0, 10, 32, 0x20a46, 0x23820, 18446744073709551615);
   (0x16bbc0, 0x23700, 7, 32, 0x22ccc, 0x23820, 18446744073709551615);
   (0x16bc00, 0x23720, 13, 32, 0x1501f, 0x23820, 18446744073709551615);
   (0x16bc40, 0x23740, 55, 96, 0x21e13, 0x23820, 18446744073709551615);
   (0x16bc80, 0x237a0, 59, 96, 0x11611, 0x23820, 18446744073709551615);
   (0x16bcc0, 0x23800, 11, 32, 0x19bd1, 0x23820, 18446744073709551615);
   (0x16bd00, 0x23e20, 18, 64, 0x1dd8e, 0x2c9c0, 18446744073709551615);
   (0x16bd40, 0x23e60, 56, 96, 0x20a46, 0x2c9c0, 18446744073709551615);
   (0x16bd80, 0x23ec0, 67, 128, 0x22ccc, 0x2c9c0, 18446744073709551615);
   (0x16bdc0, 0x23f40, 157, 192, 0x1501f, 0x2c9c0, 18446744073709551615);
   (0x16be00, 0x24000, 81, 128, 0x13d7f, 0x2c9c0, 18446744073709551615);
   (0x16be40, 0x24080, 45, 96, 0x1ee97, 0x2c9c0, 18446744073709551615);
   (0x16be80, 0x240e0, 73, 128, 0x19c1d, 0x2c9c0, 18446744073709551615);
   (0x16bec0, 0x24160, 73, 128, 0x1be9d, 0x2c9c0, 18446744073709551615);
   (0x16bf00, 0x241e0, 73, 128, 0x11619, 0x2c9c0, 18446744073709551615);
   (0x16bf40, 0x24260, 45, 96, 0x173f8, 0x2c9c0, 18446744073709551615);
   (0x16bf80, 0x242c0, 73, 128, 0x21e13, 0x2c9c0, 18446744073709551615);
   (0x16bfc0, 0x24340, 41, 96, 0x11611, 0x2c9c0, 18446744073709551615);
   (0x16c000, 0x243a0, 29, 64, 0x1b6dc, 0x2c9c0, 18446744073709551615);
   (0x16c040, 0x243e0, 21, 64, 0x21e1b, 0x2c9c0, 18446744073709551615);
   (0x16c080, 0x24420, 96, 128, 0x1fe41, 0x2c9c0, 18446744073709551615);
   (0x16c0c0, 0x244a0, 55, 96, 0x1dd93, 0x2c9c0, 18446744073709551615);
   (0x16c100, 0x24500, 172, 224, 0x1ae70, 0x2c9c0, 18446744073709551615);
   (0x16c140, 0x245e0, 67, 128, 0x1d43a, 0x2c9c0, 18446744073709551615);
   (0x16c180, 0x24660, 97, 160, 0x11e59, 0x2c9c0, 18446744073709551615);
   (0x16c1c0, 0x24700, 95, 128, 0x11e61, 0x2c9c0, 18446744073709551615);
   (0x16c200, 0x24780, 72, 128, 0x1908c, 0x2c9c0, 18446744073709551615);
   (0x16c240, 0x24800, 34, 96, 0x1b6e4, 0x2c9c0, 18446744073709551615);
   (0x16c280, 0x24860, 51, 96, 0x15026, 0x2c9c0, 18446744073709551615);
   (0x16c2c0, 0x248c0, 51, 96, 0x1449d, 0x2c9c0, 18446744073709551615);
   (0x16c300, 0x24920, 108, 160, 0x13d86, 0x2c9c0, 18446744073709551615);
   (0x16c340, 0x249c0, 77, 128, 0x17de6, 0x2c9c0, 18446744073709551615);
   (0x16c380, 0x24a40, 97, 160, 0x10b98, 0x2c9c0, 18446744073709551615);
   (0x16c3c0, 0x24ae0, 207, 256, 0x19094, 0x2c9c0, 18446744073709551615);
   (0x16c400, 0x24be0, 132, 192, 0x1856d, 0x2c9c0, 18446744073709551615);
   (0x16c440, 0x24ca0, 177, 224, 0x10ba0, 0x2c9c0, 18446744073709551615);
   (0x16c480, 0x24d80, 63, 96, 0x13d8e, 0x2c9c0, 18446744073709551615);
   (0x16c4c0, 0x24de0, 65, 128, 0x11620, 0x2c9c0, 18446744073709551615);
   (0x16c500, 0x24e60, 78, 128, 0x1276b, 0x2c9c0, 18446744073709551615);
   (0x16c540, 0x24ee0, 256, 320, 0x22cd3, 0x2c9c0, 6958145);
   (0x16c580, 0x25020, 3544, 4416, 0x1b6ec, 0x2c9c0, 6958146);
   (0x16c5c0, 0x26160, 184, 224, 0x21e23, 0x2c9c0, 6958147);
   (0x16c600, 0x26240, 10416, 13024, 0x17dee, 0x2c9c0, 6958148);
   (0x16c640, 0x29520, 9, 32, 0x1fe49, 0x2c9c0, 18446744073709551615);
   (0x16c680, 0x29540, 768, 960, 0x22d08, 0x2c9c0, 18446744073709551615);
   (0x16c6c0, 0x29900, 37, 96, 0x11eae, 0x2c9c0, 6958151);
   (0x16c700, 0x29980, 48, 96, 0x173ff, 0x2c9c0, 6958154);
   (0x16c740, 0x29a20, 12, 32, 0x1909c, 0x2c9c0, 18446744073709551615);
   (0x16c780, 0x29a40, 48, 96, 0x1d442, 0x2c9c0, 18446744073709551615);
   (0x16c7c0, 0x29ae0, 32, 64, 0x1ae78, 0x2c9c0, 18446744073709551615);
   (0x16c800, 0x29b20, 256, 320, 0x20a4d, 0x2c9c0, 18446744073709551615);
   (0x16c840, 0x29c60, 256, 320, 0x1749e, 0x2c9c0, 18446744073709551615);
   (0x16c880, 0x2c660, 160, 192, 0x1fecb, 0x2c9c0, 18446744073709551615);
   (0x16c8c0, 0x2c9a0, 1, 32, 0x1fef5, 0x2c9c0, 18446744073709551615);
   (0x16c900, 0x1610a0, 528, 672, 0x1a362, 0x2c9c0, 6958144);
   (0x16c940, 0x161340, 64, 96, 0x1b70f, 0x2c9c0, 6958149);
   (0x16c980, 0x1613a0, 24, 64, 0x12773, 0x2c9c0, 6958150);
   (0x16c9c0, 0x161400, 96, 128, 0x1fe51, 0x2c9c0, 6958152);
   (0x16ca00, 0x161480, 24, 64, 0x144a5, 0x2c9c0, 6958153);
   (0x16ca40, 0x6a2a40, 24, 64, 0x1dd66, 0x23820, 18446744073709551615);
   (0x16ca80, 0x6a2a80, 8, 32, 0x12730, 0x23820, 18446744073709551615);
   (0x16cac0, 0x6a2aa0, 48, 96, 0x15929, 0x2c9c0, 18446744073709551615);
   (0x16cb00, 0x6a2b00, 8, 32, 0x1502e, 0x2c9c0, 18446744073709551615);
   (0x16cb40, 0x6a2b20, 1, 32, 0x11e69, 0x2c9c0, 18446744073709551615);
   (0x16cb80, 0x6a2b40, 8, 32, 0x1f673, 0x2c9c0, 18446744073709551615);
   (0x16cbc0, 0x6a2b60, 16, 32, 0x1743f, 0x2c9c0, 18446744073709551615);
   (0x16cc00, 0x6a2b80, 8, 32, 0x13d96, 0x2c9c0, 18446744073709551615);
   (0x16cc40, 0x6a2ba0, 8, 32, 0x127a3, 0x2c9c0, 18446744073709551615);
   (0x16cc80, 0x6a2bc0, 48, 96, 0x1fe8a, 0x2c9c0, 18446744073709551615);
   (0x16ccc0, 0x6a2c20, 8, 32, 0x1d44a, 0x2c9c0, 18446744073709551615)]%Z.
Definition gdesc_t (m : mem) (g : Z * Z * Z * Z * Z * Z * Z) : Prop :=
  let '(d, beg, sz, swr, nm, md, odr) := g in gdesc m d beg sz swr nm md odr.
(* [comment removed for export] *)
Definition GODRS : list Z := [0x6a2c41; 0x6a2c42; 0x6a2c43; 0x6a2c44; 0x6a2c47; 0x6a2c4a; 0x6a2c40; 0x6a2c45; 0x6a2c46; 0x6a2c48; 0x6a2c49]%Z.
(* [comment removed for export] *)
Definition GSHADOWS : list (Z * Z) :=
  [(0x7fffc6d0, 12);
   (0x7fffc6dc, 4);
   (0x7fffc6e0, 4);
   (0x7fffc6e4, 4);
   (0x7fffc6e8, 12);
   (0x7fffc6f4, 12);
   (0x7fffc700, 4);
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
   (0x7fffd2a8, 120);
   (0x7fffd320, 12);
   (0x7fffd330, 12);
   (0x7fffd344, 4);
   (0x7fffd348, 12);
   (0x7fffd35c, 8);
   (0x7fffd364, 40);
   (0x7fffd38c, 40);
   (0x7fffd8cc, 24);
   (0x7fffd934, 4);
   (0x80024214, 84);
   (0x80024268, 12);
   (0x80024274, 8);
   (0x80024280, 16);
   (0x80024290, 8);
   (0x800cc548, 8);
   (0x800cc550, 4);
   (0x800cc554, 12);
   (0x800cc560, 4);
   (0x800cc564, 4);
   (0x800cc568, 4);
   (0x800cc56c, 4);
   (0x800cc570, 4);
   (0x800cc574, 4);
   (0x800cc578, 12);
   (0x800cc584, 4)]%Z.
Definition GARR_SH : Z := 0x80025768.       (* [comment removed for export] *)

Definition mdtor_pre (m : mem) : Prop :=
     mdtor_rt m
  /\ rw_cells asegs m 0x167cd8 [C8 (Z_to_bv 64 0x16bb40); C8 (Z_to_bv 64 0x16cd00)]     (* [comment removed for export] *)
  /\ rw_cells asegs m 0x16cd00 [C8 (Z_to_bv 64 1)]                                     (* [comment removed for export] *)
  /\ rw_cells asegs m 0x16dc70 [C8 (Z_to_bv 64 0)]                                     (* [comment removed for export] *)
  /\ Forall (gdesc_t m) GLOBALS
  /\ Forall (fun o => exists b, rw_cells asegs m o [C1 b]) GODRS
  /\ Forall (fun p => exists j, rw_cells asegs m (fst p) [CB (Z.to_nat (snd p)) j]) GSHADOWS
  /\ (exists j, rw_cells asegs m GARR_SH [CB 568 j]).

Lemma mdtor_pre_frame : forall sp m m',
  mdtor_pre m -> KHIGH <= sp - 48 - MDTOR_DEPTH -> munch (AEXIT_W1 sp) m m' -> wmono asegs m m' -> mdtor_pre m'.
Proof.
  intros sp m m' P KH MU WM. unfold KHIGH, MDTOR_DEPTH in KH.
  assert (D : forall A n, 0 <= n -> A + n <= 0x800d0e00 -> 0x6c505c <= A \/ (0x16cd51 <= A /\ A + n <= 0x6c4e38) \/ A + n <= 0x16cd50 ->
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
     rw_cells asegs m 0x16cd00 [C8 (Z_to_bv 64 1)]
  /\ rw_cells asegs m 0x16dc70 [C8 (Z_to_bv 64 0)]
  /\ Forall (gdesc_t m) GLOBALS
  /\ Forall (fun o => exists b, rw_cells asegs m o [C1 b]) GODRS
  /\ Forall (fun p => exists j, rw_cells asegs m (fst p) [CB (Z.to_nat (snd p)) j]) GSHADOWS
  /\ (exists j, rw_cells asegs m GARR_SH [CB 568 j]).
Lemma mdtor_pre_of_stat : forall m, mdtor_rt m -> rw_cells asegs m 0x167cd8 [C8 (Z_to_bv 64 0x16bb40); C8 (Z_to_bv 64 0x16cd00)] -> mdtor_stat m -> mdtor_pre m.
Proof. intros m RT G (A & B & C & D & E & F). exact (conj RT (conj G (conj A (conj B (conj C (conj D (conj E F))))))). Qed.
Lemma mdtor_stat_of_pre : forall m, mdtor_pre m -> mdtor_stat m.
Proof. intros m (_ & _ & A & B & C & D & E & F). exact (conj A (conj B (conj C (conj D (conj E F))))). Qed.

Definition mdtor_stat_app (a : Z) : Prop :=
  (0x16bb40 <= a < 0x16cd00) \/ (0x16cd00 <= a < 0x16cd00 + 8) \/ (0x16dc70 <= a < 0x16dc70 + 8) \/ (0x6a2c40 <= a < 0x6a2c4b).
Definition mdtor_stat_sh (a : Z) : Prop :=
  (0x7fffc6d0 <= a < 0x7fffd3b4) \/ (0x7fffd8cc <= a < 0x7fffd938) \/ (0x80024214 <= a < 0x80024298) \/ (0x800cc548 <= a < 0x800cc588) \/ (0x80025768 <= a < 0x800259a0).
Lemma mdtor_stat_magree : forall (P : Z -> Prop) m m',
  DrvAgree.magree asegs P m m' -> (forall a, mdtor_stat_app a \/ mdtor_stat_sh a -> P a) -> mdtor_stat m -> mdtor_stat m'.
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
