(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition SH_OFF : Z := 0x7fff8000.
Definition sh (z : Z) : Z := z / 8 + SH_OFF.

Definition SH_LO : Z := 0x7fff7000.          (* [comment removed for export] *)
Definition GAP_LO : Z := 0x8fff7000.         (* [comment removed for export] *)
Definition HI_LO : Z := 0x2008fff7000.       (* [comment removed for export] *)
Definition HI_HI : Z := 0x10007fff8000.      (* [comment removed for export] *)
Definition MEM_END : Z := 2 ^ 47.
Lemma shadow_consts :
  GAP_LO = SH_LO + 2 ^ 28 /\ HI_LO = GAP_LO + 2 ^ 41 /\ HI_HI = HI_LO + 0xdfff0001000 /\ HI_HI = sh MEM_END
  /\ sh 0 = SH_LO + 4096 /\ HI_LO = sh HI_HI.
Proof. unfold GAP_LO, SH_LO, HI_LO, HI_HI, sh, SH_OFF, MEM_END. repeat split; reflexivity. Qed.

Lemma sh_mono : forall x y, x <= y -> sh x <= sh y.
Proof. intros x y H. unfold sh. apply Z.add_le_mono_r. apply Z.div_le_mono; lia. Qed.

(* [comment removed for export] *)
Definition app_range (a n : Z) : Prop := 0 <= a /\ 0 <= n /\ a + n <= MEM_END /\ (a + n <= SH_LO \/ HI_HI <= a).

(* [comment removed for export] *)
Lemma shadow_of_app_range : forall a n, app_range a n -> 0 < n ->
     (SH_LO <= sh a /\ sh (a + n - 1) + 1 <= GAP_LO)
  \/ (HI_LO <= sh a /\ sh (a + n - 1) + 1 <= HI_HI).
Proof.
  intros a n (Ha & Hn & Hend & Hap) Hpos. unfold sh, SH_LO, GAP_LO, HI_LO, HI_HI, SH_OFF, MEM_END in *.
  destruct Hap as [Hlow | Hhigh].
  - left. split.
    + assert (0 <= a / 8) by (apply Z.div_pos; lia). lia.
    + assert ((a + n - 1) / 8 <= (2147446784 - 1) / 8) by (apply Z.div_le_mono; lia).
      change ((2147446784 - 1) / 8) with 268430847 in H. lia.
  - right. split.
    + assert (0x10007fff8000 / 8 <= a / 8) by (apply Z.div_le_mono; lia).
      change (0x10007fff8000 / 8) with 0x2000ffff000 in H. lia.
    + assert ((a + n - 1) / 8 <= (2 ^ 47 - 1) / 8) by (apply Z.div_le_mono; lia).
      change ((2 ^ 47 - 1) / 8) with 17592186044415 in H. lia.
Qed.

(* [comment removed for export] *)
Definition sh_lo_page (a : Z) : Z := sh a / 4096 * 4096.
Definition sh_hi_page (a n : Z) : Z := (sh (a + n - 1) / 4096 + 1) * 4096.
Lemma sh_window : forall a n, 0 < n -> sh_lo_page a <= sh a /\ sh (a + n - 1) < sh_hi_page a n
  /\ sh_lo_page a mod 4096 = 0 /\ sh_hi_page a n mod 4096 = 0.
Proof.
  intros a n Hn. unfold sh_lo_page, sh_hi_page.
  pose proof (Z.div_mod (sh a) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (sh a) 4096 ltac:(lia)).
  pose proof (Z.div_mod (sh (a + n - 1)) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (sh (a + n - 1)) 4096 ltac:(lia)).
  repeat split; try lia; apply Z_mod_mult.
Qed.
