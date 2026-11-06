(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-29: a PROVED gate that every region of the memory-checking image A' (lib/A/AD2j.v
   IMG_REGIONS) stays off the program's ledger cells: no byte of a ledger cell is in the extent [r_lo, r_hi) of any
   region, and every region is at an absolute address (r_base = None).
   - GENERIC PART (no image number): the boolean checker ledger_disjoint over any region list and any cell list
     ((address, width) pairs), and its soundness lemma ledger_disjoint_sound, proved for all inputs. The image B'
     twin is one instantiation of the same lemma with B''s region list and B''s cells.
   - A' INSTANCE: AD2j_ledger_disjoint, closed by ledger_disjoint_sound and computation.
   The cell list is PRH_Base.prh_pst (PRH_Base.v:438-441) at PRH_Img.prh_img_A, the image A' record that
   provenance/gen_prh_img.py generated from A''s unstripped twin bff8519bbe3e (PRH_Img.v:1-3): one cell per row of
   lib/Prog/LedgerCells.v, in the same order, by symbol, at the object's own width (the asan_globals record):
     LedgerCells.v :14 row 1 g_live        = pi_g_live 0x5dd560 / pi_gz_live 8              (PRH_Img.v:146-147)
     LedgerCells.v :15 row 2 g_peak        = pi_g_peak 0x5dd580 / pi_gz_peak 8              (PRH_Img.v:148-149)
     LedgerCells.v :16 row 3 g_count       = pi_g_count 0x5dd5a0 / pi_gz_count 8            (PRH_Img.v:150-151)
     LedgerCells.v :17 row 4 g_fail_at     = pi_g_fail 0xa65c0 / pi_gz_fail 8               (PRH_Img.v:152-153)
     LedgerCells.v :18 row 5 g_ran_out     = pi_g_ran_out 0x5dd5c0 / pi_gz_ran_out 1        (PRH_Img.v:154-155)
     LedgerCells.v :19 row 6 g_most        = pi_g_most 0xa65e0 / pi_gz_most 8               (PRH_Img.v:156-157)
     LedgerCells.v :20 row 7 g_own_ran_out = pi_g_own_ran_out 0x5dd540 / pi_gz_own_ran_out 1 (PRH_Img.v:158-159)
   LedgerCells.v's own list (GL_cells, :46-49) is NOT used: it holds the PLAIN build's addresses (its header, :2), not
   image A''s. The numbers above are the record's, for the reader; this file states no address. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD2j PRH_Base PRH_Img.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- generic part ---- *)

(* THE PROPERTY: every region is at an absolute address, and no byte x of a cell (a, n), a <= x < a + n, is in the
   region's extent [r_lo, r_hi) *)
Definition ledger_off (regs : list YP09.region) (cells : list (Z * Z)) : Prop :=
  forall r, In r regs ->
    YP09.r_base r = None /\
    (forall a n, In (a, n) cells -> forall x, a <= x < a + n -> ~ (YP09.r_lo r <= x < YP09.r_hi r)).

(* THE CHECKER: the cell ends at or below the region's lo, or starts at or above its hi *)
Definition cell_off_b (r : YP09.region) (c : Z * Z) : bool :=
  (fst c + snd c <=? YP09.r_lo r) || (YP09.r_hi r <=? fst c).

Definition region_off_b (cells : list (Z * Z)) (r : YP09.region) : bool :=
  match YP09.r_base r with
  | None => forallb (cell_off_b r) cells
  | Some _ => false
  end.

Definition ledger_disjoint (regs : list YP09.region) (cells : list (Z * Z)) : bool :=
  forallb (region_off_b cells) regs.

Lemma cell_off_b_sound : forall r a n, cell_off_b r (a, n) = true ->
  forall x, a <= x < a + n -> ~ (YP09.r_lo r <= x < YP09.r_hi r).
Proof.
  intros r a n H x Hx Hr. unfold cell_off_b in H. cbn [fst snd] in H.
  apply orb_true_iff in H. destruct H as [H | H]; apply Z.leb_le in H; lia.
Qed.

(* SOUNDNESS, for every region list and every cell list *)
Lemma ledger_disjoint_sound : forall regs cells, ledger_disjoint regs cells = true -> ledger_off regs cells.
Proof.
  intros regs cells H r Hr. unfold ledger_disjoint in H. rewrite forallb_forall in H.
  specialize (H r Hr). unfold region_off_b in H. revert H.
  destruct (YP09.r_base r) as [b |]; intro H; [discriminate H |].
  split; [reflexivity |].
  intros a n Hin. rewrite forallb_forall in H.
  exact (cell_off_b_sound r a n (H (a, n) Hin)).
Qed.

(* ---- the image A' instance ---- *)

Lemma AD2j_ledger_disjoint : ledger_off AD2j.IMG_REGIONS (@PRH_Base.prh_pst PRH_Img.prh_img_A).
Proof. apply ledger_disjoint_sound. vm_compute. reflexivity. Qed.
