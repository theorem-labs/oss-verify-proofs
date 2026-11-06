(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import Shadow ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Import AImg F_syscalls StdioFiles Stdio_kit MonadF F_memset AExit F_stdio_exit.
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
     rw_cells asegs m 0x166098 [C8 (Z_to_bv 64 0x1fe7a0)]                                        (* [comment removed for export] *)
  /\ rw_cells asegs m 0x1660a8 [C8 (Z_to_bv 64 0x200828); C8 (Z_to_bv 64 0x16c4f8); C8 (Z_to_bv 64 0x16ecf8);
                                C8 (Z_to_bv 64 0x16f9e8); C8 (Z_to_bv 64 0x16f9f0); C8 (Z_to_bv 64 0x16f9e0)]  (* [comment removed for export] *)
  /\ rw_cells asegs m 0x1660d8 [C8 (Z_to_bv 64 0x168108)]                                        (* [comment removed for export] *)
  /\ rw_cells asegs m 0x168100 [C8 (Z_to_bv 64 0x158454); C8 (Z_to_bv 64 0x158858)]              (* [comment removed for export] *)
  /\ rw_cells asegs m 0x16ecf8 [C8 (Z_to_bv 64 0x7fff8000)]                                      (* [comment removed for export] *)
  /\ rw_cells asegs m 0x16f9d8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]                              (* [comment removed for export] *)
  /\ rw_cells asegs m 0x16e55c [C1 (Z_to_bv 8 1)]                                                (* [comment removed for export] *)
  /\ rw_cells asegs m 0x2008a0 [C8 (Z_to_bv 64 18446744073709551615)]                          (* [comment removed for export] *)
  /\ rw_cells asegs m 0x16c510 [C4 (Z_to_bv 64 1)].                                              (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rt_clear (iv : Z * Z) : Prop :=
  let (lo, hi) := iv in
  lo <= hi /\
  (hi <= 0x166098 \/ (0x1660e0 <= lo /\ hi <= 0x168100) \/ (0x168110 <= lo /\ hi <= 0x16c510) \/ (0x16c514 <= lo /\ hi <= 0x16e55c)
   \/ (0x16e55d <= lo /\ hi <= 0x16ecf8) \/ (0x16ed00 <= lo /\ hi <= 0x16f9d8) \/ (0x16f9da <= lo /\ hi <= 0x2008a0) \/ 0x2008a8 <= lo).

Lemma mdtor_rt_frame : forall m m' W,
  mdtor_rt m -> munch W m m' -> wmono asegs m m' ->
  Forall rt_clear W -> mdtor_rt m'.
Proof.
  intros m m' W PC MU WM HW.
  assert (D : forall A n, 0 <= n ->
             ((0x166098 <= A /\ A + n <= 0x1660e0) \/ (0x168100 <= A /\ A + n <= 0x168110) \/ (0x16c510 <= A /\ A + n <= 0x16c514)
              \/ (0x16e55c <= A /\ A + n <= 0x16e55d) \/ (0x16ecf8 <= A /\ A + n <= 0x16ed00) \/ (0x16f9d8 <= A /\ A + n <= 0x16f9da)
              \/ (0x2008a0 <= A /\ A + n <= 0x2008a8)) -> disjoint_from W A n).
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
  [(0x16abe0, 0x23600, 7, 32, 0x1dceb, 0x23780, 18446744073709551615);
   (0x16ac20, 0x23620, 9, 32, 0x20993, 0x23780, 18446744073709551615);
   (0x16ac60, 0x23640, 3, 32, 0x22c4b, 0x23780, 18446744073709551615);
   (0x16aca0, 0x23660, 2, 32, 0x14f83, 0x23780, 18446744073709551615);
   (0x16ace0, 0x23680, 10, 32, 0x13cfb, 0x23780, 18446744073709551615);
   (0x16ad20, 0x236a0, 60, 96, 0x1edec, 0x23780, 18446744073709551615);
   (0x16ad60, 0x23700, 19, 64, 0x19b16, 0x23780, 18446744073709551615);
   (0x16ada0, 0x23740, 7, 32, 0x1bce6, 0x23780, 18446744073709551615);
   (0x16ade0, 0x23760, 13, 32, 0x11601, 0x23780, 18446744073709551615);
   (0x16ae20, 0x23d80, 256, 320, 0x22c52, 0x2b860, 6952416);
   (0x16ae60, 0x23ec0, 3544, 4416, 0x1b5ad, 0x2b860, 6952417);
   (0x16aea0, 0x25000, 184, 224, 0x21d60, 0x2b860, 6952418);
   (0x16aee0, 0x250e0, 10416, 13024, 0x17cf0, 0x2b860, 6952419);
   (0x16af20, 0x283c0, 9, 32, 0x1fd96, 0x2b860, 18446744073709551615);
   (0x16af60, 0x283e0, 768, 960, 0x22c87, 0x2b860, 18446744073709551615);
   (0x16afa0, 0x287a0, 37, 96, 0x11e7e, 0x2b860, 6952422);
   (0x16afe0, 0x28820, 48, 96, 0x17309, 0x2b860, 6952425);
   (0x16b020, 0x288c0, 12, 32, 0x18f9c, 0x2b860, 18446744073709551615);
   (0x16b060, 0x288e0, 48, 96, 0x1d3c7, 0x2b860, 18446744073709551615);
   (0x16b0a0, 0x28980, 32, 64, 0x1ad49, 0x2b860, 18446744073709551615);
   (0x16b0e0, 0x289c0, 256, 320, 0x2099a, 0x2b860, 18446744073709551615);
   (0x16b120, 0x28b00, 256, 320, 0x173a8, 0x2b860, 18446744073709551615);
   (0x16b160, 0x2b500, 160, 192, 0x1fe18, 0x2b860, 18446744073709551615);
   (0x16b1a0, 0x2b840, 1, 32, 0x1fe42, 0x2b860, 18446744073709551615);
   (0x16b1e0, 0x1603e0, 64, 96, 0x1b5d0, 0x2b860, 6952420);
   (0x16b220, 0x160440, 24, 64, 0x12713, 0x2b860, 6952421);
   (0x16b260, 0x1604a0, 96, 128, 0x1fd9e, 0x2b860, 6952423);
   (0x16b2a0, 0x160520, 24, 64, 0x14409, 0x2b860, 6952424);
   (0x16b2e0, 0x6a1380, 24, 64, 0x1d398, 0x23780, 18446744073709551615);
   (0x16b320, 0x6a13c0, 8, 32, 0x225fb, 0x23780, 18446744073709551615);
   (0x16b360, 0x6a13e0, 24, 64, 0x14f8a, 0x23780, 18446744073709551615);
   (0x16b3a0, 0x6a1420, 8, 32, 0x19ad1, 0x23780, 18446744073709551615);
   (0x16b3e0, 0x6a1440, 48, 96, 0x158b7, 0x2b860, 18446744073709551615);
   (0x16b420, 0x6a14a0, 8, 32, 0x14fbc, 0x2b860, 18446744073709551615);
   (0x16b460, 0x6a14c0, 1, 32, 0x11e39, 0x2b860, 18446744073709551615);
   (0x16b4a0, 0x6a14e0, 8, 32, 0x1f5c8, 0x2b860, 18446744073709551615);
   (0x16b4e0, 0x6a1500, 16, 32, 0x17349, 0x2b860, 18446744073709551615);
   (0x16b520, 0x6a1520, 8, 32, 0x13d02, 0x2b860, 18446744073709551615);
   (0x16b560, 0x6a1540, 8, 32, 0x12743, 0x2b860, 18446744073709551615);
   (0x16b5a0, 0x6a1560, 48, 96, 0x1fdd7, 0x2b860, 18446744073709551615);
   (0x16b5e0, 0x6a15c0, 8, 32, 0x1d3cf, 0x2b860, 18446744073709551615)]%Z.
Definition gdesc_t (m : mem) (g : Z * Z * Z * Z * Z * Z * Z) : Prop :=
  let '(d, beg, sz, swr, nm, md, odr) := g in gdesc m d beg sz swr nm md odr.
(* [comment removed for export] *)
Definition GODRS : list Z := [0x6a15e0; 0x6a15e1; 0x6a15e2; 0x6a15e3; 0x6a15e6; 0x6a15e9; 0x6a15e4; 0x6a15e5; 0x6a15e7; 0x6a15e8]%Z.
(* [comment removed for export] *)
Definition GSHADOWS : list (Z * Z) :=
  [(0x7fffc6c0, 4);
   (0x7fffc6c4, 4);
   (0x7fffc6c8, 4);
   (0x7fffc6cc, 4);
   (0x7fffc6d0, 4);
   (0x7fffc6d4, 12);
   (0x7fffc6e0, 8);
   (0x7fffc6e8, 4);
   (0x7fffc6ec, 4);
   (0x7fffc7b0, 40);
   (0x7fffc7d8, 552);
   (0x7fffca00, 28);
   (0x7fffca1c, 1628);
   (0x7fffd078, 4);
   (0x7fffd07c, 120);
   (0x7fffd0f4, 12);
   (0x7fffd104, 12);
   (0x7fffd118, 4);
   (0x7fffd11c, 12);
   (0x7fffd130, 8);
   (0x7fffd138, 40);
   (0x7fffd160, 40);
   (0x7fffd6a0, 24);
   (0x7fffd708, 4);
   (0x8002407c, 12);
   (0x80024088, 8);
   (0x80024094, 16);
   (0x800240a4, 8);
   (0x800cc270, 8);
   (0x800cc278, 4);
   (0x800cc27c, 8);
   (0x800cc284, 4);
   (0x800cc288, 12);
   (0x800cc294, 4);
   (0x800cc298, 4);
   (0x800cc29c, 4);
   (0x800cc2a0, 4);
   (0x800cc2a4, 4);
   (0x800cc2a8, 4);
   (0x800cc2ac, 12);
   (0x800cc2b8, 4)]%Z.
Definition GARR_SH : Z := 0x8002557c.       (* [comment removed for export] *)

Definition mdtor_pre (m : mem) : Prop :=
     mdtor_rt m
  /\ rw_cells asegs m 0x166d78 [C8 (Z_to_bv 64 0x16abe0); C8 (Z_to_bv 64 0x16b620)]     (* [comment removed for export] *)
  /\ rw_cells asegs m 0x16b640 [C8 (Z_to_bv 64 1)]                                     (* [comment removed for export] *)
  /\ rw_cells asegs m 0x16c5b0 [C8 (Z_to_bv 64 0)]                                     (* [comment removed for export] *)
  /\ Forall (gdesc_t m) GLOBALS
  /\ Forall (fun o => exists b, rw_cells asegs m o [C1 b]) GODRS
  /\ Forall (fun p => exists j, rw_cells asegs m (fst p) [CB (Z.to_nat (snd p)) j]) GSHADOWS
  /\ (exists j, rw_cells asegs m GARR_SH [CB 328 j]).

Lemma mdtor_pre_frame : forall sp m m',
  mdtor_pre m -> KHIGH <= sp - 48 - MDTOR_DEPTH -> munch (AEXIT_W1 sp) m m' -> wmono asegs m m' -> mdtor_pre m'.
Proof.
  intros sp m m' P KH MU WM. unfold KHIGH, MDTOR_DEPTH in KH.
  assert (D : forall A n, 0 <= n -> A + n <= 0x800d0c00 -> 0x6c39fc <= A \/ (0x16b691 <= A /\ A + n <= 0x6c37d8) \/ A + n <= 0x16b690 ->
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
     rw_cells asegs m 0x16b640 [C8 (Z_to_bv 64 1)]
  /\ rw_cells asegs m 0x16c5b0 [C8 (Z_to_bv 64 0)]
  /\ Forall (gdesc_t m) GLOBALS
  /\ Forall (fun o => exists b, rw_cells asegs m o [C1 b]) GODRS
  /\ Forall (fun p => exists j, rw_cells asegs m (fst p) [CB (Z.to_nat (snd p)) j]) GSHADOWS
  /\ (exists j, rw_cells asegs m GARR_SH [CB 328 j]).
Lemma mdtor_pre_of_stat : forall m, mdtor_rt m -> rw_cells asegs m 0x166d78 [C8 (Z_to_bv 64 0x16abe0); C8 (Z_to_bv 64 0x16b620)] -> mdtor_stat m -> mdtor_pre m.
Proof. intros m RT G (A & B & C & D & E & F). exact (conj RT (conj G (conj A (conj B (conj C (conj D (conj E F))))))). Qed.
Lemma mdtor_stat_of_pre : forall m, mdtor_pre m -> mdtor_stat m.
Proof. intros m (_ & _ & A & B & C & D & E & F). exact (conj A (conj B (conj C (conj D (conj E F))))). Qed.

Definition mdtor_stat_app (a : Z) : Prop :=
  (0x16abe0 <= a < 0x16b620) \/ (0x16b640 <= a < 0x16b640 + 8) \/ (0x16c5b0 <= a < 0x16c5b0 + 8) \/ (0x6a15e0 <= a < 0x6a15ea).
Definition mdtor_stat_sh (a : Z) : Prop :=
  (0x7fffc6c0 <= a < 0x7fffd188) \/ (0x7fffd6a0 <= a < 0x7fffd70c) \/ (0x8002407c <= a < 0x800240ac) \/ (0x800cc270 <= a < 0x800cc2bc) \/ (0x8002557c <= a < 0x800256c4).
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
