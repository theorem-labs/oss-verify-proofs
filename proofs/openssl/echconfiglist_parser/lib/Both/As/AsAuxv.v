(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsIface AsCXXHeap ECH_Xpres.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition AAUXV_CELL : Z := 0xc01f28.

(* [comment removed for export] *)
Definition aauxv_list (x3 x4 x5 x16 x6 x11 x12 x23 x25 x0 : Z) : list word :=
  map wz [3; x3; 4; x4; 5; x5; 16; x16; 6; x6; 11; x11; 12; x12; 23; x23; 25; x25; 0; x0].

Lemma aauxv_list_length : forall x3 x4 x5 x16 x6 x11 x12 x23 x25 x0,
  length (aauxv_list x3 x4 x5 x16 x6 x11 x12 x23 x25 x0) = 20%nat.
Proof. intros. reflexivity. Qed.

Section HCW.
  Context {HCEIL : HeapCeil}.

  Definition aauxv_ok (m : mem) (B : Z) : Prop :=
    exists av x3 x4 x5 x16 x6 x11 x12 x23 x25 x0,
      rw_cells asegs m AAUXV_CELL [C8 (wz av)]
      /\ bytes_at asegs m av (u64s (aauxv_list x3 x4 x5 x16 x6 x11 x12 x23 x25 x0))
      /\ aceil <= B /\ B <= av /\ av + 160 <= 2^63
      /\ 0 <= x3 < 2^64 /\ 0 <= x4 < 2^64 /\ 0 <= x5 < 2^64 /\ 0 <= x16 < 2^64 /\ 0 <= x6 < 2^64
      /\ 0 <= x11 < 2^64 /\ 0 <= x12 < 2^64 /\ 0 <= x23 < 2^64 /\ 0 <= x25 < 2^64 /\ 0 <= x0 < 2^64.

  (* [comment removed for export] *)
  Definition aauxv_win_ok (B : Z) (iv : Z * Z) : Prop :=
    snd iv <= B /\ (snd iv <= AAUXV_CELL \/ AAUXV_CELL + 8 <= fst iv).

  Lemma aauxv_win_ok_intro : forall B lo hi,
    hi <= B -> (hi <= AAUXV_CELL \/ AAUXV_CELL + 8 <= lo) -> aauxv_win_ok B (lo, hi).
  Proof. intros B lo hi H1 H2. exact (conj H1 H2). Qed.

  (* [comment removed for export] *)
  Lemma aauxv_win_ok_low : forall B lo hi,
    aceil <= B -> hi <= aceil -> (hi <= AAUXV_CELL \/ AAUXV_CELL + 8 <= lo) -> aauxv_win_ok B (lo, hi).
  Proof. intros B lo hi H1 H2 H3. split; cbn; lia. Qed.

  (* [comment removed for export] *)
  Lemma aauxv_win_ok_stack : forall B lo hi, aceil <= lo -> hi <= B -> aauxv_win_ok B (lo, hi).
  Proof. intros B lo hi H1 H2. pose proof aceil_facts. unfold aauxv_win_ok, AAUXV_CELL. cbn. lia. Qed.

  Lemma aauxv_ok_bounds : forall m B, aauxv_ok m B -> aceil <= B.
  Proof. intros m B (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & x25 & x0 & _ & _ & H & _). exact H. Qed.

  Lemma aauxv_ok_weaken : forall m B B', aauxv_ok m B -> aceil <= B' <= B -> aauxv_ok m B'.
  Proof.
    intros m B B' (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & x25 & x0 & C & A & H) HB.
    exists av, x3, x4, x5, x16, x6, x11, x12, x23, x25, x0. split; [exact C|]. split; [exact A|]. lia.
  Qed.

  Lemma Forall_disjoint_from_aux : forall (P : Z * Z -> Prop) W a n,
    Forall P W -> (forall lo hi, P (lo, hi) -> a + n <= lo \/ hi <= a) -> disjoint_from W a n.
  Proof.
    intros P W a n F HP. induction F as [|[lo hi] W Hx F IH]; cbn; [exact I|]. split; [apply (HP _ _ Hx)| exact IH].
  Qed.

  (* [comment removed for export] *)
  Lemma aauxv_ok_frame : forall m m' B W,
    aauxv_ok m B -> munch W m m' -> wmono asegs m m' -> Forall (aauxv_win_ok B) W -> aauxv_ok m' B.
  Proof.
    intros m m' B W (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & x25 & x0 & C & A & H) MU WM FW.
    exists av, x3, x4, x5, x16, x6, x11, x12, x23, x25, x0. split; [|split; [|exact H]].
    - eapply rw_cells_transport; eauto. eapply Forall_disjoint_from_aux; [exact FW|]. intros lo hi [X1 X2]. cbn in X1, X2 |- *. lia.
    - eapply bytes_at_transport; eauto. eapply Forall_disjoint_from_aux; [exact FW|]. intros lo hi [X1 X2]. cbn in X1, X2 |- *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma aauxv_ok_apres : forall (H : asr) LB SP m m' B,
    aauxv_ok m B -> apres H LB SP m m' -> SP <= B -> aauxv_ok m' B.
  Proof.
    intros H LB SP m m' B (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & x25 & x0 & C & A & HB) HP HSP.
    exists av, x3, x4, x5, x16, x6, x11, x12, x23, x25, x0. split; [|split; [|exact HB]].
    - eapply apres_rw_cells; [exact HP| exact C|]. right; left. intros a Ha. cbn in Ha. unfold AAUXV_CELL in Ha. unfold aimg_client. lia.
    - eapply apres_bytes_at; [exact HP| exact A|]. left. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma aauxv_ok_xpres : forall (H : asr) LB SP X m m' B,
    aauxv_ok m B -> xpres H LB SP X m m' -> SP <= B -> Forall (aauxv_win_ok B) X -> aauxv_ok m' B.
  Proof.
    intros H LB SP X m m' B (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & x25 & x0 & C & A & HB) HP HSP FX.
    exists av, x3, x4, x5, x16, x6, x11, x12, x23, x25, x0. split; [|split; [|exact HB]].
    - eapply xpres_rw_cells; [exact HP| exact C|]. split.
      + right; left. intros a Ha. cbn in Ha. unfold aimg_client, AAUXV_CELL in *. lia.
      + apply Forall_forall. intros [lo hi] Hin. pose proof (proj1 (Forall_forall _ _) FX _ Hin) as [_ K]. cbn in K |- *. lia.
    - eapply xpres_bytes_at; [exact HP| exact A|]. split.
      + left. lia.
      + apply Forall_forall. intros [lo hi] Hin. pose proof (proj1 (Forall_forall _ _) FX _ Hin) as [K _]. cbn in K |- *. lia.
  Qed.
End HCW.
