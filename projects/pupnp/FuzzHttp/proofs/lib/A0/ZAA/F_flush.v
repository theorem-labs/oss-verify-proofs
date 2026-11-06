(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep SysMm.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ LZPages.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import PEnv LJ LJU F_mm_A F_mm_B F_poison AFrame.
Import ITree.Exc.
Import ListNotations.
Open Scope Z_scope.

Section FL.
Context {HC : HasCeiling}.
Variable E : penv.

Definition memtoshadow_entry : Z := 0x58384.

#[using="Type"] Lemma memtoshadow_spec : forall (ra sp gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (x : Z),
  mem_inv asegs m -> poison_env E m -> a0 = wz x -> 0 <= x ->
  (x < 0x7fff8000 \/ 0x10007fff8000 <= x <= 0x7fffffffffff) ->
  evt asegs (fun ms' => exists x5' a1' a2' a3' a4' a5' a6' a7',
      ms' = MS (mkR ra sp gp tp x5' x6 x7 s0 s1 (wz (sh x)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (ret_pc ra) fc None m (seg_rom asegs)
      /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m /\ poison_env E m)
    (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (wz memtoshadow_entry) fc None m (seg_rom asegs)).
Proof.
  intros until x. intros MI PE -> X0 AM. unfold memtoshadow_entry. pose proof PE as PE0. pe_split PE.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [] mm) as MU; pose proof (wmono_refl asegs mm) as WM end.
  do 2 zstep.
  zstep.
  do 4 zstep.
  change (Z.land ((Z.b2z (2147450880 <? 2147450879) + -1) mod 18446744073709551616) 2147450879) with 2147450879.
  zstep. if_cases KL; zify_cond KL.
  -   do 3 zstep.
    rewrite (Z.shiftr_div_pow2 x 3) by lia. change (2 ^ 3) with 8.
    replace (2147450880 + x / 8) with (sh x) by (unfold sh, SHADOW_OFF; lia).
    finish.
  -
    do 4 zstep.
    do 3 zstep.
    zstep. replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; vm_compute; reflexivity).
    if_true_z.
    do 5 zstep.
    zstep. if_false_z.
    zstep. if_false_z.
    do 3 zstep.
    rewrite (Z.shiftr_div_pow2 x 3) by lia. change (2 ^ 3) with 8.
    replace (2147450880 + x / 8) with (sh x) by (unfold sh, SHADOW_OFF; lia).
    finish.
Qed.

Definition flush_entry : Z := 0x58338.

Definition flush_range (p n : Z) : option (Z * Z) :=
  let pb := pgup (sh p) in let pe := pgdn (sh (p + n)) in
  if pe <=? pb then None else Some (pb, pe - pb).

Definition flush_tree (p n : Z) : itree nodeL (exc unit) :=
  match flush_range p n with None => Ret (Ok tt) | Some (a, l) => t_madv a l end.

#[using="Type"] Lemma fl_pgup_ge x : x <= pgup x. Proof. clear. unfold pgup. Z.div_mod_to_equations. lia. Qed.
#[using="Type"] Lemma fl_pgup_lt x : pgup x < x + 4096. Proof. clear. unfold pgup. Z.div_mod_to_equations. lia. Qed.
#[using="Type"] Lemma fl_pgdn_le x : pgdn x <= x. Proof. clear. unfold pgdn. Z.div_mod_to_equations. lia. Qed.
#[using="Type"] Lemma fl_pgdn_gt x : x - 4096 < pgdn x. Proof. clear. unfold pgdn. Z.div_mod_to_equations. lia. Qed.

#[using="Type"] Lemma firstn_repeat_le : forall (b : byte) k n, (k <= n)%nat -> firstn k (repeat b n) = repeat b k.
Proof. intros b k. induction k as [|k IH]; intros n Hk; [reflexivity|]. destruct n as [|n]; [lia|]. cbn. f_equal. apply IH. lia. Qed.
#[using="Type"] Lemma skipn_repeat_sub : forall (b : byte) k n, skipn k (repeat b n) = repeat b (n - k).
Proof. intros b k. induction k as [|k IH]; intros n; [rewrite Nat.sub_0_r; reflexivity|]. destruct n as [|n]; [reflexivity|]. cbn. apply IH. Qed.

#[using="Type"] Lemma rw_cells_CB3_split : forall (mm : word -> option byte) A n1 n2 n3 (b : byte),
  rw_cells asegs mm A [CB (n1 + n2 + n3) (repeat b (n1 + n2 + n3))] ->
  rw_cells asegs mm A [CB n1 (repeat b n1)]
  /\ rw_cells asegs mm (A + Z.of_nat n1) [CB n2 (repeat b n2)]
  /\ rw_cells asegs mm (A + Z.of_nat n1 + Z.of_nat n2) [CB n3 (repeat b n3)].
Proof.
  intros mm A n1 n2 n3 b R.
  pose proof (rw_cells_split_CB asegs mm A [] _ _ [] [n1; n2; n3] R ltac:(cbn [sum_nat]; lia)) as SP.
  cbn [mk_CB_cells app] in SP.
  rewrite (firstn_repeat_le b n1) in SP by lia. rewrite (skipn_repeat_sub b n1) in SP.
  rewrite (firstn_repeat_le b n2) in SP by lia. rewrite (skipn_repeat_sub b n2) in SP.
  rewrite (firstn_repeat_le b n3) in SP by lia.
  pose proof (rw_cells_take3 asegs mm A [_] [_] [_] SP) as (S1 & S2 & S3).
  cbn [cells_size csize] in S2, S3. rewrite ?Nat.add_0_r in S2. rewrite !Nat.add_0_r in S3. split; [exact S1| split; [exact S2| exact S3]].
Qed.

Definition flush_H (p n : Z) (H : word -> bool) : word -> bool :=
  match flush_range p n with None => H | Some (a, l) => hide_range a (a + l) H end.
Definition flush_edges (p n : Z) (m' : word -> option byte) : Prop :=
  match flush_range p n with
  | None => rw_cells asegs m' (sh p) [CB (Z.to_nat (n / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (n / 8)))]
  | Some (a, l) =>
      rw_cells asegs m' (sh p) [CB (Z.to_nat (a - sh p)) (repeat (Z_to_bv 8 0) (Z.to_nat (a - sh p)))]
      /\ rw_cells asegs m' (a + l) [CB (Z.to_nat (sh p + n / 8 - (a + l))) (repeat (Z_to_bv 8 0) (Z.to_nat (sh p + n / 8 - (a + l))))]
  end.

Definition flush_postA (ra : word) (q : Z) (gp tp x6 x7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo p n : Z) (H : word -> bool) (m : word -> option byte)
  : unit -> (word -> bool) -> machine_state -> Prop :=
  fun _ H' ms' => exists x5 a0 a1 a2 a3 a4 a5 a6 a7 m',
    ms' = MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ H' = flush_H p n H
    /\ munch [(q - 32, q); (sh p, sh p + n / 8)] m m' /\ wmono_but [(sh p, sh p + n / 8)] m m' /\ mem_inv asegs m' /\ stk asegs m' lo q /\ poison_env E m'
    /\ flush_edges p n m'.

#[using="Type"] Lemma flush_shadow_specA : forall (ra gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (H : word -> bool) (q lo p n : Z),
  mem_inv asegs m -> mclean H m -> poison_env E m -> stk asegs m lo q -> 0x10007fff8000 <= lo -> lo <= q - 32 -> q <= 2^47 ->
  a0 = wz p -> a1 = wz n -> 0 <= n -> 0x609000 <= p -> p mod 8 = 0 -> n mod 8 = 0 ->
  (p + n < 0x7fff8000 \/ (0x10007fff8000 <= p /\ p + n <= 0x7fffffffffff)) ->
  rw_cells asegs m (sh p) [CB (Z.to_nat (n / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (n / 8)))] ->
  implA H (flush_tree p n)
        (flush_postA ra q gp tp x6 x7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 F fc lo p n H m)
    (MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (wz flush_entry) fc None m (seg_rom asegs)).
Proof.
  intros until n. intros MI C PE ST LO LOQ QHI -> -> N0 P0 P8 N8 AM SHZ. unfold flush_entry.
  assert (SHE : sh (p + n) = sh p + n / 8) by (unfold sh; clear - P8 N8; Z.div_mod_to_equations; lia).
  assert (SHB : 0x7fff8000 <= sh p /\ sh p + n / 8 <= 0x10007fff8000) by (unfold sh, SHADOW_OFF; clear - N0 P0 AM N8; Z.div_mod_to_equations; nia).
  lazymatch goal with |- ITreeLZ.implL _ _ _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (munch_refl [(q - 32, q); (sh p, sh p + n / 8)] mm) as MU; pose proof (wmono_refl asegs mm) as WM end.
  lz_go.
  carve_frame 32%nat ST.
  do 5 zstep.
  do 3 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch goal with MIx : mem_inv asegs mm |- _ =>
    pose proof (poison_env_frame E _ _ mm PE MU WM ltac:(unfold above_img; repeat constructor; cbn [fst]; lia)) as PEc;
    call (memtoshadow_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm p MIx PEc eq_refl ltac:(lia) ltac:(clear - AM N0; lia)) end end.
  clear PEc. do 3 zstep.
  replace (n + p) with (p + n) by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch goal with MIx : mem_inv asegs mm |- _ =>
    pose proof (poison_env_frame E _ _ mm PE MU WM ltac:(unfold above_img; repeat constructor; cbn [fst]; lia)) as PEc;
    call (memtoshadow_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm (p + n) MIx PEc eq_refl ltac:(lia) ltac:(clear - AM N0 P0; lia)) end end.
  clear PEc.
  do 2 zstep.
  do 4 zstep.
  zstep.   replace (q + -32 + 32) with q by lia.
  zstep.
  release_frame FR ST q.

  carve_frame 32%nat ST.
  do 5 zstep.
  clear POST POST0.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (poison_env_frame E _ _ mm PE MU WM ltac:(unfold above_img; repeat constructor; cbn [fst]; lia)) as PE2 end.
  pose proof PE2 as PE3. pe_split PE2.
  do 4 zstep.
  zstep.
  zstep. if_true_z.
  do 2 zstep.
  change (Z.land 4096 (4096 + -1)) with 0.
  zstep. if_false_z.
  do 5 zstep.
  rewrite ?(Z.mod_small (sh p + 4095)), ?(Z.mod_small (sh (p + n))) by lia. rewrite !land_m4096 by lia.
  replace ((sh p + 4095) / 4096 * 4096) with (pgup (sh p)) by (unfold pgup; f_equal; f_equal; lia).
  replace (sh (p + n) / 4096 * 4096) with (pgdn (sh (p + n))) by reflexivity.
  pose proof (fl_pgup_ge (sh p)) as G1. pose proof (fl_pgdn_le (sh (p + n))) as G2. pose proof (fl_pgup_lt (sh p)) as G3. pose proof (fl_pgdn_gt (sh (p + n))) as G4.
  unfold flush_tree, flush_range.
  zstep. if_cases K; zify_cond K.
  -
    replace (pgdn (sh (p + n)) <=? pgup (sh p)) with true by (symmetry; apply Z.leb_le; clear - K SHB SHE N0; unfold pgup, pgdn; replace (sh p + 4096 - 1) with (sh p + 4095) by lia; Z.div_mod_to_equations; lia).
    do 4 zstep.
    zstep. replace (q + -32 + 32) with q by lia. zstep.
    release_frame FR ST q.
    lz_ret. unfold flush_postA, flush_H, flush_edges, flush_range.
    replace (pgdn (sh (p + n)) <=? pgup (sh p)) with true by (symmetry; apply Z.leb_le; clear - K SHB SHE N0; unfold pgup, pgdn; replace (sh p + 4096 - 1) with (sh p + 4095) by lia; Z.div_mod_to_equations; lia).
    finish. reflexivity. apply wmono_but_of_wmono; assumption.
  -
    replace (pgdn (sh (p + n)) <=? pgup (sh p)) with false by (symmetry; apply Z.leb_gt; clear - K SHB SHE N0; unfold pgup, pgdn; replace (sh p + 4096 - 1) with (sh p + 4095) by lia; Z.div_mod_to_equations; lia).
    do 2 zstep.
    do 4 zstep.
    zstep. replace (q + -32 + 32) with q by lia. zstep.
    release_frame FR ST q.

    assert (LT : pgup (sh p) < pgdn (sh (p + n))) by (clear - K SHB SHE N0; unfold pgup, pgdn; replace (sh p + 4096 - 1) with (sh p + 4095) by lia; Z.div_mod_to_equations; lia).
    clear K. set (pb := pgup (sh p)) in *. set (pe := pgdn (sh (p + n))) in *.
    assert (PBM : pb mod 4096 = 0) by (subst pb; apply pgup_mod).
    assert (PDM : (pe - pb) mod 4096 = 0) by (subst pb pe; apply pg_diff_mod).
    assert (LZE : lenZ (pe - pb) = pe - pb).
    { pose proof (lenZ_bound (pe - pb) ltac:(clear - LT G1 G2 SHB SHE; lia)) as LB. pose proof (LZPages.lenZ_aligned (pe - pb)) as LA.
      unfold page_size in LA. clear - LB LA PDM. Z.div_mod_to_equations. lia. }
    lazymatch goal with SZ : rw_cells asegs ?mm (sh p) [CB (Z.to_nat (n / 8)) _] |- _ =>
      replace (Z.to_nat (n / 8)) with (Z.to_nat (pb - sh p) + Z.to_nat (pe - pb) + Z.to_nat (sh p + n / 8 - pe))%nat in SZ
        by (clear - LT G1 G2 SHB SHE; lia);
      pose proof (rw_cells_CB3_split mm (sh p) _ _ _ _ SZ) as (S1 & S2 & S3); clear SZ end.
    rewrite (Z2Nat.id (pb - sh p)) in S2, S3 by (clear - G1; lia). rewrite (Z2Nat.id (pe - pb)) in S3 by (clear - LT; lia).
    replace (sh p + (pb - sh p)) with pb in S2, S3 by lia. replace (pb + (pe - pb)) with pe in S3 by lia.
    lz_here. clear S2.

    lazymatch goal with |- ITreeLZ.implL _ _ _ _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mF end.
    lazymatch goal with MIx : mem_inv asegs mF, MCx : mclean H mF, STx : stk asegs mF lo q |- _ =>
      rename MIx into MIF; rename MCx into MCF; rename STx into STF end.
    eapply implA_mono.
    { eapply (imadvise_dontneed_spec E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mF H pb (pe - pb));
        [ exact MIF | exact MCF | exact PE3
        | f_equal; subst pb; clear; unfold pgup; replace (sh p + 4096 - 1) with (sh p + 4095) by lia; Z.div_mod_to_equations; lia
        | f_equal; subst pb pe; clear - LT SHB SHE N0; unfold pgup, pgdn in *; replace (sh p + 4096 - 1) with (sh p + 4095) in * by lia; Z.div_mod_to_equations; lia
        | reflexivity
        | exact PBM | clear - G1 SHB; lia | clear - LT G1 G2 SHB SHE; lia | rewrite LZE; clear - LT G1 G2 SHB SHE; lia ]. }
    intros u H' ms' (y3 & m' & -> & -> & MUd & WBd & MId & PEd). rewrite LZE in MUd, WBd.
    replace (pb + (pe - pb)) with pe in MUd, WBd by lia.
    unfold flush_postA, flush_H, flush_edges, flush_range. fold pb pe.
    replace (pe <=? pb) with false by (symmetry; apply Z.leb_gt; exact LT).
    rewrite LZE. replace (pb + (pe - pb)) with pe by lia.
    do 10 eexists. split; [reflexivity|]. split; [reflexivity|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUd]. unfold sub_fp. cbn [outside]. intros xo (_ & O2 & _).
             split; [intros R; apply O2; clear - R G1 G2 SHE; lia| exact I]. }
    split. { eapply wmono_but_wmono_l; [exact WM|]. eapply wmono_but_weaken; [| exact WBd]. unfold sub_fp. cbn [outside]. intros xo (O2 & _).
             split; [intros R; apply O2; clear - R G1 G2 SHE; lia| exact I]. }
    split; [exact MId|].
    split. { apply (stk_transport_but _ mF m' MUd WBd lo q STF). cbn [disjoint_from]. split; [clear - LO SHB SHE G2; lia| exact I]. }
    split; [exact PEd|].
    split.
    + apply (rw_cells_transport_but _ mF m' MUd WBd _ _ S1). cbn [cells_size csize disjoint_from]. rewrite Nat.add_0_r, Z2Nat.id by (clear - G1; lia). split; [clear; lia| exact I].
    + apply (rw_cells_transport_but _ mF m' MUd WBd _ _ S3). cbn [cells_size csize disjoint_from]. rewrite Nat.add_0_r, Z2Nat.id by (clear - G2 SHE; lia). split; [clear - LT; lia| exact I].
Qed.
End FL.
