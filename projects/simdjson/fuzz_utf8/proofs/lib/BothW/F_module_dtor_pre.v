(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import Shadow ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import BImg F_syscalls StdioFiles Stdio_kit MonadF F_memset AExit F_stdio_exit.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import StrwF SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require DrvAgree.
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
     rw_cells bsegs m 0x171fd8 [C8 (Z_to_bv 64 0x20ab20)]                                        (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x171fe8 [C8 (Z_to_bv 64 0x20cba8); C8 (Z_to_bv 64 0x178878); C8 (Z_to_bv 64 0x17b078);
                                C8 (Z_to_bv 64 0x17bd68); C8 (Z_to_bv 64 0x17bd70); C8 (Z_to_bv 64 0x17bd60)]  (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x172018 [C8 (Z_to_bv 64 0x174060)]                                        (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x174058 [C8 (Z_to_bv 64 0x16438c); C8 (Z_to_bv 64 0x164790)]              (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x17b078 [C8 (Z_to_bv 64 0x7fff8000)]                                      (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x17bd58 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]                              (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x17a8dc [C1 (Z_to_bv 8 1)]                                                (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x20cc20 [C8 (Z_to_bv 64 18446744073709551615)]                          (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x178890 [C4 (Z_to_bv 64 1)].                                              (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rt_clear (iv : Z * Z) : Prop :=
  let (lo, hi) := iv in
  lo <= hi /\
  (hi <= 0x171fd8 \/ (0x172020 <= lo /\ hi <= 0x174058) \/ (0x174068 <= lo /\ hi <= 0x178890) \/ (0x178894 <= lo /\ hi <= 0x17a8dc)
   \/ (0x17a8dd <= lo /\ hi <= 0x17b078) \/ (0x17b080 <= lo /\ hi <= 0x17bd58) \/ (0x17bd5a <= lo /\ hi <= 0x20cc20) \/ 0x20cc28 <= lo).

Lemma mdtor_rt_frame : forall m m' W,
  mdtor_rt m -> munch W m m' -> wmono bsegs m m' ->
  Forall rt_clear W -> mdtor_rt m'.
Proof.
  intros m m' W PC MU WM HW.
  assert (D : forall A n, 0 <= n ->
             ((0x171fd8 <= A /\ A + n <= 0x172020) \/ (0x174058 <= A /\ A + n <= 0x174068) \/ (0x178890 <= A /\ A + n <= 0x178894)
              \/ (0x17a8dc <= A /\ A + n <= 0x17a8dd) \/ (0x17b078 <= A /\ A + n <= 0x17b080) \/ (0x17bd58 <= A /\ A + n <= 0x17bd5a)
              \/ (0x20cc20 <= A /\ A + n <= 0x20cc28)) -> disjoint_from W A n).
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
  [(0x176f10, 0x23660, 7, 32, 0x1dc3d, 0x237e0, 18446744073709551615);
   (0x176f50, 0x23680, 9, 32, 0x14fae, 0x237e0, 18446744073709551615);
   (0x176f90, 0x236a0, 3, 32, 0x13d26, 0x237e0, 18446744073709551615);
   (0x176fd0, 0x236c0, 2, 32, 0x1ed3e, 0x237e0, 18446744073709551615);
   (0x177010, 0x236e0, 10, 32, 0x19afb, 0x237e0, 18446744073709551615);
   (0x177050, 0x23700, 60, 96, 0x1bd55, 0x237e0, 18446744073709551615);
   (0x177090, 0x23760, 19, 64, 0x1161c, 0x237e0, 18446744073709551615);
   (0x1770d0, 0x237a0, 7, 32, 0x18f43, 0x237e0, 18446744073709551615);
   (0x177110, 0x237c0, 13, 32, 0x11623, 0x237e0, 18446744073709551615);
   (0x177150, 0x23de0, 256, 320, 0x22caa, 0x2b520, 7002464);
   (0x177190, 0x23f20, 3544, 4416, 0x1b61c, 0x2b520, 7002465);
   (0x1771d0, 0x25060, 184, 224, 0x21d3a, 0x2b520, 7002466);
   (0x177210, 0x25140, 10416, 13024, 0x17d1b, 0x2b520, 7002467);
   (0x177250, 0x28420, 9, 32, 0x18f4b, 0x2b520, 18446744073709551615);
   (0x177290, 0x28440, 37, 96, 0x11ea9, 0x2b520, 7002470);
   (0x1772d0, 0x284c0, 48, 96, 0x17334, 0x2b520, 7002473);
   (0x177310, 0x28560, 12, 32, 0x18f53, 0x2b520, 18446744073709551615);
   (0x177350, 0x28580, 48, 96, 0x1162b, 0x2b520, 18446744073709551615);
   (0x177390, 0x28620, 32, 64, 0x22cfe, 0x2b520, 18446744073709551615);
   (0x1773d0, 0x28660, 256, 320, 0x20974, 0x2b520, 18446744073709551615);
   (0x177410, 0x287a0, 256, 320, 0x173d3, 0x2b520, 18446744073709551615);
   (0x177450, 0x2b1a0, 160, 192, 0x1fdf9, 0x2b520, 18446744073709551615);
   (0x177490, 0x2b4e0, 1, 32, 0x1fe23, 0x2b520, 18446744073709551615);
   (0x1774d0, 0x2b500, 1, 32, 0x1f588, 0x2b520, 18446744073709551615);
   (0x177510, 0x16c320, 64, 96, 0x1b63f, 0x2b520, 7002468);
   (0x177550, 0x16c380, 24, 64, 0x1273e, 0x2b520, 7002469);
   (0x177590, 0x16c3e0, 96, 128, 0x1fd7f, 0x2b520, 7002471);
   (0x1775d0, 0x16c460, 24, 64, 0x14434, 0x2b520, 7002472);
   (0x177610, 0x1767a0, 768, 960, 0x22cdf, 0x2b520, 18446744073709551615);
   (0x177650, 0x6ad700, 24, 64, 0x1d2f2, 0x237e0, 18446744073709551615);
   (0x177690, 0x6ad740, 8, 32, 0x225d5, 0x237e0, 18446744073709551615);
   (0x1776d0, 0x6ad760, 24, 64, 0x14fb5, 0x237e0, 18446744073709551615);
   (0x177710, 0x6ad7a0, 8, 32, 0x19b02, 0x237e0, 18446744073709551615);
   (0x177750, 0x6ad7c0, 48, 96, 0x158e2, 0x2b520, 18446744073709551615);
   (0x177790, 0x6ad820, 8, 32, 0x14fe7, 0x2b520, 18446744073709551615);
   (0x1777d0, 0x6ad840, 1, 32, 0x11e64, 0x2b520, 18446744073709551615);
   (0x177810, 0x6ad860, 8, 32, 0x1f530, 0x2b520, 18446744073709551615);
   (0x177850, 0x6ad880, 16, 32, 0x17374, 0x2b520, 18446744073709551615);
   (0x177890, 0x6ad8a0, 8, 32, 0x13d2d, 0x2b520, 18446744073709551615);
   (0x1778d0, 0x6ad8c0, 8, 32, 0x1276e, 0x2b520, 18446744073709551615);
   (0x177910, 0x6ad8e0, 48, 96, 0x1fdb8, 0x2b520, 18446744073709551615);
   (0x177950, 0x6ad940, 8, 32, 0x1d321, 0x2b520, 18446744073709551615)]%Z.
Definition gdesc_t (m : mem) (g : Z * Z * Z * Z * Z * Z * Z) : Prop :=
  let '(d, beg, sz, swr, nm, md, odr) := g in gdesc m d beg sz swr nm md odr.
(* [comment removed for export] *)
Definition GODRS : list Z := [0x6ad960; 0x6ad961; 0x6ad962; 0x6ad963; 0x6ad966; 0x6ad969; 0x6ad964; 0x6ad965; 0x6ad967; 0x6ad968]%Z.
(* [comment removed for export] *)
Definition GSHADOWS : list (Z * Z) :=
  [(0x7fffc6cc, 4);
   (0x7fffc6d0, 4);
   (0x7fffc6d4, 4);
   (0x7fffc6d8, 4);
   (0x7fffc6dc, 4);
   (0x7fffc6e0, 12);
   (0x7fffc6ec, 8);
   (0x7fffc6f4, 4);
   (0x7fffc6f8, 4);
   (0x7fffc7bc, 40);
   (0x7fffc7e4, 552);
   (0x7fffca0c, 28);
   (0x7fffca28, 1628);
   (0x7fffd084, 4);
   (0x7fffd088, 12);
   (0x7fffd098, 12);
   (0x7fffd0ac, 4);
   (0x7fffd0b0, 12);
   (0x7fffd0c4, 8);
   (0x7fffd0cc, 40);
   (0x7fffd0f4, 40);
   (0x7fffd634, 24);
   (0x7fffd69c, 4);
   (0x7fffd6a0, 4);
   (0x80025864, 12);
   (0x80025870, 8);
   (0x8002587c, 16);
   (0x8002588c, 8);
   (0x80026cf4, 120);
   (0x800cdae0, 8);
   (0x800cdae8, 4);
   (0x800cdaec, 8);
   (0x800cdaf4, 4);
   (0x800cdaf8, 12);
   (0x800cdb04, 4);
   (0x800cdb08, 4);
   (0x800cdb0c, 4);
   (0x800cdb10, 4);
   (0x800cdb14, 4);
   (0x800cdb18, 4);
   (0x800cdb1c, 12);
   (0x800cdb28, 4)]%Z.
Definition GARR_SH : Z := 0x80026de2.       (* [comment removed for export] *)

Definition mdtor_pre (m : mem) : Prop :=
     mdtor_rt m
  /\ rw_cells bsegs m 0x172cb8 [C8 (Z_to_bv 64 0x176f10); C8 (Z_to_bv 64 0x177990)]     (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x1779c0 [C8 (Z_to_bv 64 1)]                                     (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x178930 [C8 (Z_to_bv 64 0)]                                     (* [comment removed for export] *)
  /\ Forall (gdesc_t m) GLOBALS
  /\ Forall (fun o => exists b, rw_cells bsegs m o [C1 b]) GODRS
  /\ Forall (fun p => exists j, rw_cells bsegs m (fst p) [CB (Z.to_nat (snd p)) j]) GSHADOWS
  /\ (exists j, rw_cells bsegs m GARR_SH [CB 336 j]).

Lemma mdtor_pre_frame : forall sp m m',
  mdtor_pre m -> KHIGH <= sp - 48 - MDTOR_DEPTH -> munch (AEXIT_W1 sp) m m' -> wmono bsegs m m' -> mdtor_pre m'.
Proof.
  intros sp m m' P KH MU WM. unfold KHIGH, MDTOR_DEPTH in KH.
  assert (D : forall A n, 0 <= n -> A + n <= 0x800d2400 -> 0x6cfd7c <= A \/ (0x177a11 <= A /\ A + n <= 0x6cfb58) \/ A + n <= 0x177a10 ->
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
     rw_cells bsegs m 0x1779c0 [C8 (Z_to_bv 64 1)]
  /\ rw_cells bsegs m 0x178930 [C8 (Z_to_bv 64 0)]
  /\ Forall (gdesc_t m) GLOBALS
  /\ Forall (fun o => exists b, rw_cells bsegs m o [C1 b]) GODRS
  /\ Forall (fun p => exists j, rw_cells bsegs m (fst p) [CB (Z.to_nat (snd p)) j]) GSHADOWS
  /\ (exists j, rw_cells bsegs m GARR_SH [CB 336 j]).
Lemma mdtor_pre_of_stat : forall m, mdtor_rt m -> rw_cells bsegs m 0x172cb8 [C8 (Z_to_bv 64 0x176f10); C8 (Z_to_bv 64 0x177990)] -> mdtor_stat m -> mdtor_pre m.
Proof. intros m RT G (A & B & C & D & E & F). exact (conj RT (conj G (conj A (conj B (conj C (conj D (conj E F))))))). Qed.
Lemma mdtor_stat_of_pre : forall m, mdtor_pre m -> mdtor_stat m.
Proof. intros m (_ & _ & A & B & C & D & E & F). exact (conj A (conj B (conj C (conj D (conj E F))))). Qed.

Definition mdtor_stat_app (a : Z) : Prop :=
  (0x176f10 <= a < 0x177990) \/ (0x1779c0 <= a < 0x1779c0 + 8) \/ (0x178930 <= a < 0x178930 + 8) \/ (0x6ad960 <= a < 0x6ad96a).
Definition mdtor_stat_sh (a : Z) : Prop :=
  (0x7fffc6cc <= a < 0x7fffd11c) \/ (0x7fffd634 <= a < 0x7fffd6a4) \/ (0x80025864 <= a < 0x80025894) \/ (0x80026cf4 <= a < 0x80026d6c) \/ (0x800cdae0 <= a < 0x800cdb2c) \/ (0x80026de2 <= a < 0x80026f32).
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
