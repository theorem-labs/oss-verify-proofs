(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg F_syscalls StdioFiles Stdio_kit MonadF F_memset AExit F_stdio_exit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import StrwF SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require DrvAgree.
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
     rw_cells bsegs m 0x112a60 [C8 (Z_to_bv 64 0x1ab120)]                                        (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x112a70 [C8 (Z_to_bv 64 0x1ad1a8); C8 (Z_to_bv 64 0x118e78); C8 (Z_to_bv 64 0x11b678);
                                C8 (Z_to_bv 64 0x11c368); C8 (Z_to_bv 64 0x11c370); C8 (Z_to_bv 64 0x11c360)]  (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x112aa0 [C8 (Z_to_bv 64 0x1149c8)]                                        (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x1149c0 [C8 (Z_to_bv 64 0x108898); C8 (Z_to_bv 64 0x108c9c)]              (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x11b678 [C8 (Z_to_bv 64 0x7fff8000)]                                      (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x11c358 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]                              (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x11aedc [C1 (Z_to_bv 8 1)]                                                (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x1ad220 [C8 (Z_to_bv 64 18446744073709551615)]                          (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x118e90 [C4 (Z_to_bv 64 1)].                                              (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rt_clear (iv : Z * Z) : Prop :=
  let (lo, hi) := iv in
  lo <= hi /\
  (hi <= 0x112a60 \/ (0x112aa8 <= lo /\ hi <= 0x1149c0) \/ (0x1149d0 <= lo /\ hi <= 0x118e90) \/ (0x118e94 <= lo /\ hi <= 0x11aedc)
   \/ (0x11aedd <= lo /\ hi <= 0x11b678) \/ (0x11b680 <= lo /\ hi <= 0x11c358) \/ (0x11c35a <= lo /\ hi <= 0x1ad220) \/ 0x1ad228 <= lo).

Lemma mdtor_rt_frame : forall m m' W,
  mdtor_rt m -> munch W m m' -> wmono bsegs m m' ->
  Forall rt_clear W -> mdtor_rt m'.
Proof.
  intros m m' W PC MU WM HW.
  assert (D : forall A n, 0 <= n ->
             ((0x112a60 <= A /\ A + n <= 0x112aa8) \/ (0x1149c0 <= A /\ A + n <= 0x1149d0) \/ (0x118e90 <= A /\ A + n <= 0x118e94)
              \/ (0x11aedc <= A /\ A + n <= 0x11aedd) \/ (0x11b678 <= A /\ A + n <= 0x11b680) \/ (0x11c358 <= A /\ A + n <= 0x11c35a)
              \/ (0x1ad220 <= A /\ A + n <= 0x1ad228)) -> disjoint_from W A n).
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
  [(0x117800, 0x22f40, 13, 32, 0x1cded, 0x22f80, 18446744073709551615);
   (0x117840, 0x22f60, 4, 32, 0x168a0, 0x22f80, 18446744073709551615);
   (0x117880, 0x23580, 256, 320, 0x225ac, 0x2acc0, 6610592);
   (0x1178c0, 0x236c0, 3544, 4416, 0x1b15e, 0x2acc0, 6610593);
   (0x117900, 0x24800, 184, 224, 0x216c8, 0x2acc0, 6610594);
   (0x117940, 0x248e0, 10416, 13024, 0x17a4e, 0x2acc0, 6610595);
   (0x117980, 0x27bc0, 9, 32, 0x18c1e, 0x2acc0, 18446744073709551615);
   (0x1179c0, 0x27be0, 37, 96, 0x11db0, 0x2acc0, 6610598);
   (0x117a00, 0x27c60, 48, 96, 0x170a6, 0x2acc0, 6610601);
   (0x117a40, 0x27d00, 12, 32, 0x18c26, 0x2acc0, 18446744073709551615);
   (0x117a80, 0x27d20, 48, 96, 0x11581, 0x2acc0, 18446744073709551615);
   (0x117ac0, 0x27dc0, 32, 64, 0x22600, 0x2acc0, 18446744073709551615);
   (0x117b00, 0x27e00, 256, 320, 0x2032d, 0x2acc0, 18446744073709551615);
   (0x117b40, 0x27f40, 256, 320, 0x17145, 0x2acc0, 18446744073709551615);
   (0x117b80, 0x2a940, 160, 192, 0x1f7b2, 0x2acc0, 18446744073709551615);
   (0x117bc0, 0x2ac80, 1, 32, 0x1f7dc, 0x2acc0, 18446744073709551615);
   (0x117c00, 0x2aca0, 1, 32, 0x1ef6f, 0x2acc0, 18446744073709551615);
   (0x117c40, 0x10f600, 64, 96, 0x1b181, 0x2acc0, 6610596);
   (0x117c80, 0x10f660, 24, 64, 0x12628, 0x2acc0, 6610597);
   (0x117cc0, 0x10f6c0, 96, 128, 0x1f738, 0x2acc0, 6610599);
   (0x117d00, 0x10f740, 24, 64, 0x142dd, 0x2acc0, 6610600);
   (0x117d40, 0x117100, 768, 960, 0x225e1, 0x2acc0, 18446744073709551615);
   (0x117d80, 0x64dd00, 48, 96, 0x156f9, 0x2acc0, 18446744073709551615);
   (0x117dc0, 0x64dd60, 8, 32, 0x14e0e, 0x2acc0, 18446744073709551615);
   (0x117e00, 0x64dd80, 8, 32, 0x1c2e1, 0x2acc0, 18446744073709551615);
   (0x117e40, 0x64dda0, 8, 32, 0x21f80, 0x2acc0, 18446744073709551615);
   (0x117e80, 0x64ddc0, 16, 32, 0x170e6, 0x2acc0, 18446744073709551615);
   (0x117ec0, 0x64dde0, 8, 32, 0x13be8, 0x2acc0, 18446744073709551615);
   (0x117f00, 0x64de00, 8, 32, 0x12658, 0x2acc0, 18446744073709551615);
   (0x117f40, 0x64de20, 48, 96, 0x1f771, 0x2acc0, 18446744073709551615);
   (0x117f80, 0x64de80, 8, 32, 0x1cdf5, 0x2acc0, 18446744073709551615)]%Z.
Definition gdesc_t (m : mem) (g : Z * Z * Z * Z * Z * Z * Z) : Prop :=
  let '(d, beg, sz, swr, nm, md, odr) := g in gdesc m d beg sz swr nm md odr.
(* [comment removed for export] *)
Definition GODRS : list Z := [0x64dea0; 0x64dea1; 0x64dea2; 0x64dea3; 0x64dea6; 0x64dea9; 0x64dea4; 0x64dea5; 0x64dea7; 0x64dea8]%Z.
(* [comment removed for export] *)
Definition GSHADOWS : list (Z * Z) :=
  [(0x7fffc5e8, 4);
   (0x7fffc5ec, 4);
   (0x7fffc6b0, 40);
   (0x7fffc6d8, 552);
   (0x7fffc900, 28);
   (0x7fffc91c, 1628);
   (0x7fffcf78, 4);
   (0x7fffcf7c, 12);
   (0x7fffcf8c, 12);
   (0x7fffcfa0, 4);
   (0x7fffcfa4, 12);
   (0x7fffcfb8, 8);
   (0x7fffcfc0, 40);
   (0x7fffcfe8, 40);
   (0x7fffd528, 24);
   (0x7fffd590, 4);
   (0x7fffd594, 4);
   (0x80019ec0, 12);
   (0x80019ecc, 8);
   (0x80019ed8, 16);
   (0x80019ee8, 8);
   (0x8001ae20, 120);
   (0x800c1ba0, 12);
   (0x800c1bac, 4);
   (0x800c1bb0, 4);
   (0x800c1bb4, 4);
   (0x800c1bb8, 4);
   (0x800c1bbc, 4);
   (0x800c1bc0, 4);
   (0x800c1bc4, 12);
   (0x800c1bd0, 4)]%Z.
Definition GARR_SH : Z := 0x8001af00.       (* [comment removed for export] *)

Definition mdtor_pre (m : mem) : Prop :=
     mdtor_rt m
  /\ rw_cells bsegs m 0x113728 [C8 (Z_to_bv 64 0x117800); C8 (Z_to_bv 64 0x117fc0)]     (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x117fc0 [C8 (Z_to_bv 64 1)]                                     (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x118f30 [C8 (Z_to_bv 64 0)]                                     (* [comment removed for export] *)
  /\ Forall (gdesc_t m) GLOBALS
  /\ Forall (fun o => exists b, rw_cells bsegs m o [C1 b]) GODRS
  /\ Forall (fun p => exists j, rw_cells bsegs m (fst p) [CB (Z.to_nat (snd p)) j]) GSHADOWS
  /\ (exists j, rw_cells bsegs m GARR_SH [CB 248 j]).

Lemma mdtor_pre_frame : forall sp m m',
  mdtor_pre m -> KHIGH <= sp - 48 - MDTOR_DEPTH -> munch (AEXIT_W1 sp) m m' -> wmono bsegs m m' -> mdtor_pre m'.
Proof.
  intros sp m m' P KH MU WM. unfold KHIGH, MDTOR_DEPTH in KH.
  assert (D : forall A n, 0 <= n -> A + n <= 0x800c6200 -> 0x66ec64 <= A \/ (0x118011 <= A /\ A + n <= 0x66ea40) \/ A + n <= 0x118010 ->
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
     rw_cells bsegs m 0x117fc0 [C8 (Z_to_bv 64 1)]
  /\ rw_cells bsegs m 0x118f30 [C8 (Z_to_bv 64 0)]
  /\ Forall (gdesc_t m) GLOBALS
  /\ Forall (fun o => exists b, rw_cells bsegs m o [C1 b]) GODRS
  /\ Forall (fun p => exists j, rw_cells bsegs m (fst p) [CB (Z.to_nat (snd p)) j]) GSHADOWS
  /\ (exists j, rw_cells bsegs m GARR_SH [CB 248 j]).
Lemma mdtor_pre_of_stat : forall m, mdtor_rt m -> rw_cells bsegs m 0x113728 [C8 (Z_to_bv 64 0x117800); C8 (Z_to_bv 64 0x117fc0)] -> mdtor_stat m -> mdtor_pre m.
Proof. intros m RT G (A & B & C & D & E & F). exact (conj RT (conj G (conj A (conj B (conj C (conj D (conj E F))))))). Qed.
Lemma mdtor_stat_of_pre : forall m, mdtor_pre m -> mdtor_stat m.
Proof. intros m (_ & _ & A & B & C & D & E & F). exact (conj A (conj B (conj C (conj D (conj E F))))). Qed.

Definition mdtor_stat_app (a : Z) : Prop :=
  (0x117800 <= a < 0x117fc0) \/ (0x117fc0 <= a < 0x117fc0 + 8) \/ (0x118f30 <= a < 0x118f30 + 8) \/ (0x64dea0 <= a < 0x64deaa).
Definition mdtor_stat_sh (a : Z) : Prop :=
  (0x7fffc5e8 <= a < 0x7fffd010) \/ (0x7fffd528 <= a < 0x7fffd598) \/ (0x80019ec0 <= a < 0x80019ef0) \/ (0x8001ae20 <= a < 0x8001ae98) \/ (0x800c1ba0 <= a < 0x800c1bd4) \/ (0x8001af00 <= a < 0x8001aff8).
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
