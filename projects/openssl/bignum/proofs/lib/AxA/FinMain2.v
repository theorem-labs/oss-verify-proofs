(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Bool List.
From Stdlib Require Import Uint63.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import FastWord.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import ExTrie AxLazy AxLin AxMem AxZZ AxScan AxState AxSys AxLz AxRun.
From OSSVerify.Proofs.openssl.bignum.lib.AxA Require Import AxExportH FinMain1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition ent_wins (am : amodel) (e : aent) : list (lin * Z) :=
  if lzfull e then []
  else if ae_na e then map (fun x => (snd (fst x), snd x)) (List.filter (fun x => aent_eqb (fst (fst x)) e) (am_exp am))
  else [(ae_base e, ae_size e)].

Definition sh_wins (R : region) : list (lin * Z) :=
  if negb (is_shadow R) ||| iall cell_is0 (rg_cells R) then [] else [((wZ (rg_bo R), rg_ts R), to_Z (rg_n R))].

Definition win_of (B : AST) : list (lin * Z) :=
  ((sh_lo, []), 4096) :: flat_map (ent_wins (a_model B)) (am_maps (a_model B)) ++ flat_map sh_wins (a_mem B).

Definition wins_bytes (W : list (lin * Z)) : Z := fold_right (fun w z => snd w + 8192 + z) 0 W.

Definition fin_win (LIM : Z) (B : AST) : bool :=
  let W := win_of B in
  forallb w_ok W && hz_ok B W && (a_budget B + (JUNK + wins_bytes W) <=? LIM).

From Stdlib Require Import Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From OSSVerify.Proofs.openssl.bignum.lib.AS Require Import AsanAcct.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require RzCPS.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxModelRel.
From OSSVerify.Proofs.openssl.bignum.lib.AxA Require Import AxExportM.
Local Open Scope Z_scope.

Definition w_pos (B : AST) (w : lin * Z) : bool :=
  match lrange (a_facts B) (fst w) with Some (lo, _) => 1 <=? lo + snd w | None => false end.

Definition fin_win2 (LIM : Z) (B : AST) : bool := fin_win LIM B && forallb (w_pos B) (win_of B).

Lemma pdn_lb (z : Z) : z - 4095 <= pdn z.
Proof. unfold pdn. pose proof (Z.div_mod z 4096 ltac:(lia)) as D. pose proof (Z.mod_pos_bound z 4096 ltac:(lia)) as M. lia. Qed.

Lemma hull_bytes (ρ : valuation) (W : list (lin * Z)) : forallb w_ok W = true -> A_bytes (map (den_w ρ) W) <= wins_bytes W.
Proof.
  induction W as [|w r IH]; intros H; [cbn; lia|]. cbn [forallb] in H. apply andb_prop in H as [H1 H2]. specialize (IH H2).
  cbn [map A_bytes wins_bytes fold_right]. unfold den_w at 1 2. cbn [fst snd].
  pose proof (pdn_lb (leval ρ (fst w))). destruct (pup_spec (leval ρ (fst w) + snd w)) as (_ & _ & P3). fold (wins_bytes r). lia.
Qed.

Section Capstone.
Variable segs : list Segment.
Hypothesis Hlow : segs_low segs.
Variable fs0 : Fs.Fs.
Variable LIM : Z.
Variable ρ : valuation.
Variable B : AST.
Variable ms : machine_state.
Variable model : Model.
Hypothesis HR : R segs amodel (MR segs fs0 ρ) LIM ρ B (mkCfg ms model).
Variables (main_pc top : Z).
Hypothesis Htop : top <= 2 ^ 47.
Hypothesis Hfm : fin_model main_pc top B = true.
Hypothesis Hfw : fin_win2 LIM B = true.

Definition A_main : list (Z * Z) := A' ρ (win_of B) JUNK.

End Capstone.
