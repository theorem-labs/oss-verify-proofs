(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-29: the image B' twin of lib/A/AD2jLedgerGate.v (blob cfd762260605 on
   origin/cold/g-ph-verbs-p102-AD2jGate 2a5be4cd01e2). A PROVED gate that every region of the
   memory-checking image B' (lib/Reusable/YD2j.v IMG_REGIONS) stays off the program's ledger cells: no byte
   of a ledger cell is in the extent [r_lo, r_hi) of any region, and every region is at an absolute address
   (r_base = None).
   - The GENERIC PART is NOT restated here. ledger_off / cell_off_b / region_off_b / ledger_disjoint and the
     soundness lemma ledger_disjoint_sound are proved for ALL region lists and ALL cell lists in the A file,
     with no image number in them; this file is the second instantiation of that one lemma, with B''s region
     list and B''s cells, exactly as the A file's header says its twin would be.
   - B' INSTANCE: YD2j_ledger_disjoint, closed by AD2jLedgerGate.ledger_disjoint_sound and computation.
   The cell list is PRH_Base.prh_pst (PRH_Base.v:448-451) at PRH_ImgB.prh_img_B, the image B' record that
   provenance/gen_prh_img.py (sha256 6f17b81ee32316bf) generated from B''s unstripped twin
   c90d4fa54d43160baf62e5aa387211a798dddbad13d2619d85acbf37aee0c175 (PRH_ImgB.v:1-3): one cell per row of
   lib/Prog/LedgerCells.v, in the same order, by symbol, at the object's own width (the asan_globals record):
     LedgerCells.v :14 row 1 g_live        = pi_g_live 0x5ddda0 / pi_gz_live 8               (PRH_ImgB.v:147-148)
     LedgerCells.v :15 row 2 g_peak        = pi_g_peak 0x5dddc0 / pi_gz_peak 8               (PRH_ImgB.v:149-150)
     LedgerCells.v :16 row 3 g_count       = pi_g_count 0x5ddde0 / pi_gz_count 8             (PRH_ImgB.v:151-152)
     LedgerCells.v :17 row 4 g_fail_at     = pi_g_fail 0xa6e00 / pi_gz_fail 8                (PRH_ImgB.v:153-154)
     LedgerCells.v :18 row 5 g_ran_out     = pi_g_ran_out 0x5dde00 / pi_gz_ran_out 1         (PRH_ImgB.v:155-156)
     LedgerCells.v :19 row 6 g_most        = pi_g_most 0xa6e20 / pi_gz_most 8                (PRH_ImgB.v:157-158)
     LedgerCells.v :20 row 7 g_own_ran_out = pi_g_own_ran_out 0x5ddd80 / pi_gz_own_ran_out 1 (PRH_ImgB.v:159-160)
   LedgerCells.v's own list (GL_cells, :46-49) is NOT used: it holds the PLAIN build's addresses (its header,
   :2), not image B''s. The numbers above are the record's, for the reader; this file states no address.
   WHY lib/B and not lib/Reusable next to YD2j: the A gate sits in lib/A because both of its inputs (AD2j and
   PRH_Img) are lib/A files. B''s two inputs are split - YD2j is in lib/Reusable, PRH_ImgB is in lib/B - and
   the layering runs one way only: lib/B files Require lib/Reusable (PALibB.v, PAImg_prog.v, Listing_prog.v
   and others), and no lib/Reusable file Requires lib/B. A gate in lib/Reusable would invert that, so it goes
   on the lib/B side, beside the image record it instantiates. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YP09 YD2j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Base AD2jLedgerGate.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PRH_ImgB.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- the image B' instance ---- *)

Lemma YD2j_ledger_disjoint :
  AD2jLedgerGate.ledger_off YD2j.IMG_REGIONS (@PRH_Base.prh_pst PRH_ImgB.prh_img_B).
Proof. apply AD2jLedgerGate.ledger_disjoint_sound. vm_compute. reflexivity. Qed.
