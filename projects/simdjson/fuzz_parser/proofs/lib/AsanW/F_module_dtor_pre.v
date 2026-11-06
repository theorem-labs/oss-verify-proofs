(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg F_syscalls StdioFiles Stdio_kit MonadF F_memset AExit F_stdio_exit.
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
     rw_cells asegs m 0x1072e0 [C8 (Z_to_bv 64 0x19f5a0)]                                        (* [comment removed for export] *)
  /\ rw_cells asegs m 0x1072f0 [C8 (Z_to_bv 64 0x1a1628); C8 (Z_to_bv 64 0x10d2f8); C8 (Z_to_bv 64 0x10faf8);
                                C8 (Z_to_bv 64 0x1107e8); C8 (Z_to_bv 64 0x1107f0); C8 (Z_to_bv 64 0x1107e0)]  (* [comment removed for export] *)
  /\ rw_cells asegs m 0x107320 [C8 (Z_to_bv 64 0x109248)]                                        (* [comment removed for export] *)
  /\ rw_cells asegs m 0x109240 [C8 (Z_to_bv 64 0xfd118); C8 (Z_to_bv 64 0xfd51c)]              (* [comment removed for export] *)
  /\ rw_cells asegs m 0x10faf8 [C8 (Z_to_bv 64 0x7fff8000)]                                      (* [comment removed for export] *)
  /\ rw_cells asegs m 0x1107d8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]                              (* [comment removed for export] *)
  /\ rw_cells asegs m 0x10f35c [C1 (Z_to_bv 8 1)]                                                (* [comment removed for export] *)
  /\ rw_cells asegs m 0x1a16a0 [C8 (Z_to_bv 64 18446744073709551615)]                          (* [comment removed for export] *)
  /\ rw_cells asegs m 0x10d310 [C4 (Z_to_bv 64 1)].                                              (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rt_clear (iv : Z * Z) : Prop :=
  let (lo, hi) := iv in
  lo <= hi /\
  (hi <= 0x1072e0 \/ (0x107328 <= lo /\ hi <= 0x109240) \/ (0x109250 <= lo /\ hi <= 0x10d310) \/ (0x10d314 <= lo /\ hi <= 0x10f35c)
   \/ (0x10f35d <= lo /\ hi <= 0x10faf8) \/ (0x10fb00 <= lo /\ hi <= 0x1107d8) \/ (0x1107da <= lo /\ hi <= 0x1a16a0) \/ 0x1a16a8 <= lo).

Lemma mdtor_rt_frame : forall m m' W,
  mdtor_rt m -> munch W m m' -> wmono asegs m m' ->
  Forall rt_clear W -> mdtor_rt m'.
Proof.
  intros m m' W PC MU WM HW.
  assert (D : forall A n, 0 <= n ->
             ((0x1072e0 <= A /\ A + n <= 0x107328) \/ (0x109240 <= A /\ A + n <= 0x109250) \/ (0x10d310 <= A /\ A + n <= 0x10d314)
              \/ (0x10f35c <= A /\ A + n <= 0x10f35d) \/ (0x10faf8 <= A /\ A + n <= 0x10fb00) \/ (0x1107d8 <= A /\ A + n <= 0x1107da)
              \/ (0x1a16a0 <= A /\ A + n <= 0x1a16a8)) -> disjoint_from W A n).
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
  [(0x10bcc0, 0x22ec0, 13, 32, 0x2033f, 0x22f00, 18446744073709551615);
   (0x10bd00, 0x22ee0, 4, 32, 0x11566, 0x22f00, 18446744073709551615);
   (0x10bd40, 0x23500, 256, 320, 0x22540, 0x2afe0, 6562592);
   (0x10bd80, 0x23640, 3544, 4416, 0x1b171, 0x2afe0, 6562593);
   (0x10bdc0, 0x24780, 184, 224, 0x216e1, 0x2afe0, 6562594);
   (0x10be00, 0x24860, 10416, 13024, 0x17a2a, 0x2afe0, 6562595);
   (0x10be40, 0x27b40, 9, 32, 0x1f742, 0x2afe0, 18446744073709551615);
   (0x10be80, 0x27b60, 768, 960, 0x22575, 0x2afe0, 18446744073709551615);
   (0x10bec0, 0x27f20, 37, 96, 0x11d94, 0x2afe0, 6562598);
   (0x10bf00, 0x27fa0, 48, 96, 0x17082, 0x2afe0, 6562601);
   (0x10bf40, 0x28040, 12, 32, 0x18c7e, 0x2afe0, 18446744073709551615);
   (0x10bf80, 0x28060, 48, 96, 0x1ce78, 0x2afe0, 18446744073709551615);
   (0x10bfc0, 0x28100, 32, 64, 0x1a940, 0x2afe0, 18446744073709551615);
   (0x10c000, 0x28140, 256, 320, 0x20346, 0x2afe0, 18446744073709551615);
   (0x10c040, 0x28280, 256, 320, 0x17121, 0x2afe0, 18446744073709551615);
   (0x10c080, 0x2ac80, 160, 192, 0x1f7c4, 0x2afe0, 18446744073709551615);
   (0x10c0c0, 0x2afc0, 1, 32, 0x1f7ee, 0x2afe0, 18446744073709551615);
   (0x10c100, 0x103e80, 64, 96, 0x1b194, 0x2afe0, 6562596);
   (0x10c140, 0x103ee0, 24, 64, 0x1260c, 0x2afe0, 6562597);
   (0x10c180, 0x103f40, 96, 128, 0x1f74a, 0x2afe0, 6562599);
   (0x10c1c0, 0x103fc0, 24, 64, 0x142c1, 0x2afe0, 6562600);
   (0x10c200, 0x642180, 48, 96, 0x156dd, 0x2afe0, 18446744073709551615);
   (0x10c240, 0x6421e0, 8, 32, 0x14df2, 0x2afe0, 18446744073709551615);
   (0x10c280, 0x642200, 8, 32, 0x1c36c, 0x2afe0, 18446744073709551615);
   (0x10c2c0, 0x642220, 8, 32, 0x21f14, 0x2afe0, 18446744073709551615);
   (0x10c300, 0x642240, 16, 32, 0x170c2, 0x2afe0, 18446744073709551615);
   (0x10c340, 0x642260, 8, 32, 0x13bcc, 0x2afe0, 18446744073709551615);
   (0x10c380, 0x642280, 8, 32, 0x1263c, 0x2afe0, 18446744073709551615);
   (0x10c3c0, 0x6422a0, 48, 96, 0x1f783, 0x2afe0, 18446744073709551615);
   (0x10c400, 0x642300, 8, 32, 0x1ce80, 0x2afe0, 18446744073709551615)]%Z.
Definition gdesc_t (m : mem) (g : Z * Z * Z * Z * Z * Z * Z) : Prop :=
  let '(d, beg, sz, swr, nm, md, odr) := g in gdesc m d beg sz swr nm md odr.
(* [comment removed for export] *)
Definition GODRS : list Z := [0x642320; 0x642321; 0x642322; 0x642323; 0x642326; 0x642329; 0x642324; 0x642325; 0x642327; 0x642328]%Z.
(* [comment removed for export] *)
Definition GSHADOWS : list (Z * Z) :=
  [(0x7fffc5d8, 4);
   (0x7fffc5dc, 4);
   (0x7fffc6a0, 40);
   (0x7fffc6c8, 552);
   (0x7fffc8f0, 28);
   (0x7fffc90c, 1628);
   (0x7fffcf68, 4);
   (0x7fffcf6c, 120);
   (0x7fffcfe4, 12);
   (0x7fffcff4, 12);
   (0x7fffd008, 4);
   (0x7fffd00c, 12);
   (0x7fffd020, 8);
   (0x7fffd028, 40);
   (0x7fffd050, 40);
   (0x7fffd590, 24);
   (0x7fffd5f8, 4);
   (0x800187d0, 12);
   (0x800187dc, 8);
   (0x800187e8, 16);
   (0x800187f8, 8);
   (0x800c0430, 12);
   (0x800c043c, 4);
   (0x800c0440, 4);
   (0x800c0444, 4);
   (0x800c0448, 4);
   (0x800c044c, 4);
   (0x800c0450, 4);
   (0x800c0454, 12);
   (0x800c0460, 4)]%Z.
Definition GARR_SH : Z := 0x80019798.       (* [comment removed for export] *)

Definition mdtor_pre (m : mem) : Prop :=
     mdtor_rt m
  /\ rw_cells asegs m 0x107fa8 [C8 (Z_to_bv 64 0x10bcc0); C8 (Z_to_bv 64 0x10c440)]     (* [comment removed for export] *)
  /\ rw_cells asegs m 0x10c440 [C8 (Z_to_bv 64 1)]                                     (* [comment removed for export] *)
  /\ rw_cells asegs m 0x10d3b0 [C8 (Z_to_bv 64 0)]                                     (* [comment removed for export] *)
  /\ Forall (gdesc_t m) GLOBALS
  /\ Forall (fun o => exists b, rw_cells asegs m o [C1 b]) GODRS
  /\ Forall (fun p => exists j, rw_cells asegs m (fst p) [CB (Z.to_nat (snd p)) j]) GSHADOWS
  /\ (exists j, rw_cells asegs m GARR_SH [CB 240 j]).

Lemma mdtor_pre_frame : forall sp m m',
  mdtor_pre m -> KHIGH <= sp - 48 - MDTOR_DEPTH -> munch (AEXIT_W1 sp) m m' -> wmono asegs m m' -> mdtor_pre m'.
Proof.
  intros sp m m' P KH MU WM. unfold KHIGH, MDTOR_DEPTH in KH.
  assert (D : forall A n, 0 <= n -> A + n <= 0x800c4a00 -> 0x6630e4 <= A \/ (0x10c491 <= A /\ A + n <= 0x662ec0) \/ A + n <= 0x10c490 ->
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
     rw_cells asegs m 0x10c440 [C8 (Z_to_bv 64 1)]
  /\ rw_cells asegs m 0x10d3b0 [C8 (Z_to_bv 64 0)]
  /\ Forall (gdesc_t m) GLOBALS
  /\ Forall (fun o => exists b, rw_cells asegs m o [C1 b]) GODRS
  /\ Forall (fun p => exists j, rw_cells asegs m (fst p) [CB (Z.to_nat (snd p)) j]) GSHADOWS
  /\ (exists j, rw_cells asegs m GARR_SH [CB 240 j]).
Lemma mdtor_pre_of_stat : forall m, mdtor_rt m -> rw_cells asegs m 0x107fa8 [C8 (Z_to_bv 64 0x10bcc0); C8 (Z_to_bv 64 0x10c440)] -> mdtor_stat m -> mdtor_pre m.
Proof. intros m RT G (A & B & C & D & E & F). exact (conj RT (conj G (conj A (conj B (conj C (conj D (conj E F))))))). Qed.
Lemma mdtor_stat_of_pre : forall m, mdtor_pre m -> mdtor_stat m.
Proof. intros m (_ & _ & A & B & C & D & E & F). exact (conj A (conj B (conj C (conj D (conj E F))))). Qed.

Definition mdtor_stat_app (a : Z) : Prop :=
  (0x10bcc0 <= a < 0x10c440) \/ (0x10c440 <= a < 0x10c440 + 8) \/ (0x10d3b0 <= a < 0x10d3b0 + 8) \/ (0x642320 <= a < 0x64232a).
Definition mdtor_stat_sh (a : Z) : Prop :=
  (0x7fffc5d8 <= a < 0x7fffd078) \/ (0x7fffd590 <= a < 0x7fffd5fc) \/ (0x800187d0 <= a < 0x80018800) \/ (0x800c0430 <= a < 0x800c0464) \/ (0x80019798 <= a < 0x80019888).
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
