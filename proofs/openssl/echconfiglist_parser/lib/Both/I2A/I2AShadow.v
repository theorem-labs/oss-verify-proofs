(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_Xpres AsStack0.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import FxSteps FxAcc.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain
  FxRun FxRn FxImage FxHandoff FxHandoff2 FxCellFrame FxRoFrame FxGeom FxGeomA I2Canon I2Mach I2Image I2Run I2RunA.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2A Require Import I2AInv I2ANodeLib I2ANodeMem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac slia := Zify.zify; xlia zchecker.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma to_Z_add_small : forall a b : int, to_Z a + to_Z b < 2 ^ 63 -> to_Z (a + b)%uint63 = to_Z a + to_Z b.
Proof. intros a b H. pose proof (i63_range a). pose proof (i63_range b). rewrite Uint63.add_spec. change wB with (2 ^ 63). apply Z.mod_small. slia. Qed.
Lemma to_Z_mul_small : forall a b : int, to_Z a * to_Z b < 2 ^ 63 -> to_Z (a * b)%uint63 = to_Z a * to_Z b.
Proof. intros a b H. pose proof (i63_range a). pose proof (i63_range b). rewrite Uint63.mul_spec. change wB with (2 ^ 63). apply Z.mod_small. slia. Qed.
Lemma to_Z_sub_small : forall a b : int, to_Z b <= to_Z a -> to_Z (a - b)%uint63 = to_Z a - to_Z b.
Proof. intros a b H. pose proof (i63_range a). pose proof (i63_range b). rewrite Uint63.sub_spec. change wB with (2 ^ 63). apply Z.mod_small. slia. Qed.

Lemma sget_SL : forall (j : int) s0 s1 s2 s3 s4 s5 s6 s7, 0 <= to_Z j < 8 ->
  sget j (SL s0 s1 s2 s3 s4 s5 s6 s7) = nth (Z.to_nat (to_Z j)) [s0; s1; s2; s3; s4; s5; s6; s7] SU.
Proof.
  intros j s0 s1 s2 s3 s4 s5 s6 s7 Hj.
  assert (Hc : (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7)%uint63).
  { assert (E : j = of_Z (to_Z j)) by (rewrite of_to_Z; reflexivity). rewrite E.
    assert (K : to_Z j = 0 \/ to_Z j = 1 \/ to_Z j = 2 \/ to_Z j = 3 \/ to_Z j = 4 \/ to_Z j = 5 \/ to_Z j = 6 \/ to_Z j = 7) by slia.
    destruct K as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; cbn; tauto. }
  destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sh_byte_full : forall n s : int, to_Z n <= 2 ^ 40 -> to_Z s < 2 ^ 40 -> (to_Z s + 1) * 8 <= to_Z n -> to_Z (sh_byte n s) = 0.
Proof.
  intros n s Hn Hs H. unfold sh_byte. pose proof (i63_range s). pose proof (i63_range n).
  assert (E : to_Z ((s + 1) * 8)%uint63 = (to_Z s + 1) * 8).
  { rewrite to_Z_mul_small; rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; change (to_Z 8%uint63) with 8; slia. }
  destruct (Uint63.leb ((s + 1) * 8) n)%uint63 eqn:El; [reflexivity|].
  exfalso. assert (K : ~ to_Z ((s + 1) * 8)%uint63 <= to_Z n) by (intros K; apply Uint63.leb_spec in K; congruence). rewrite E in K. exact (K H).
Qed.
Lemma sh_byte_last : forall n s : int, to_Z n <= 2 ^ 40 -> to_Z s < 2 ^ 40 -> to_Z n < (to_Z s + 1) * 8 -> to_Z s * 8 <= to_Z n ->
  to_Z (sh_byte n s) = to_Z n - to_Z s * 8.
Proof.
  intros n s Hn Hs H Hle. unfold sh_byte. pose proof (i63_range s). pose proof (i63_range n).
  assert (E : to_Z ((s + 1) * 8)%uint63 = (to_Z s + 1) * 8).
  { rewrite to_Z_mul_small; rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; change (to_Z 8%uint63) with 8; slia. }
  destruct (Uint63.leb ((s + 1) * 8) n)%uint63 eqn:El.
  - apply Uint63.leb_spec in El. rewrite E in El. slia.
  - assert (E8 : to_Z (s * 8)%uint63 = to_Z s * 8) by (rewrite to_Z_mul_small; change (to_Z 8%uint63) with 8; slia).
    rewrite to_Z_sub_small by (rewrite E8; slia). rewrite E8. reflexivity.
Qed.

Lemma shadow_of_byte : forall (n : Z) (s : nat), 0 <= n -> Z.of_nat s < nsh n ->
  nth_error (shadow_of n) s = Some (b8 (if (Z.of_nat s + 1) * 8 <=? n then 0 else n - Z.of_nat s * 8)).
Proof.
  intros n s Hn Hs. unfold nsh in Hs.
  destruct (Z.leb_spec ((Z.of_nat s + 1) * 8) n) as [Hle|Hgt].
  - apply shadow_of_nth_full; [exact Hn | Z.div_mod_to_equations; slia].
  - assert (Es : s = Z.to_nat (n / 8)) by (Z.div_mod_to_equations; slia).
    assert (Hm : n mod 8 <> 0) by (Z.div_mod_to_equations; slia).
    rewrite Es, (shadow_of_nth_last n Hn Hm). f_equal. f_equal. Z.div_mod_to_equations. slia.
Qed.

Lemma nth_wbytes8_w0 : forall j, (j < 8)%nat -> nth_error (wbytes8 w0) j = Some (b8 0).
Proof. intros j Hj. destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; try reflexivity. lia. Qed.

Lemma leb8_spec : forall (ci n : int), to_Z ci < 2 ^ 40 -> to_Z n < 2 ^ 50 ->
  (((ci + 1) * 8 <=? n >> 3) = true)%uint63 <-> (to_Z ci + 1) * 8 <= to_Z n / 8.
Proof.
  intros ci n Hci Hn. pose proof (i63_range ci). pose proof (i63_range n).
  assert (E : to_Z ((ci + 1) * 8)%uint63 = (to_Z ci + 1) * 8).
  { rewrite to_Z_mul_small; rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; change (to_Z 8%uint63) with 8; slia. }
  rewrite <- E, <- to_Z_lsr3. split; intros K; [apply Uint63.leb_spec; exact K | apply Uint63.leb_spec in K; exact K].
Qed.

Lemma nsh_eq : forall n : int, to_Z n < 2 ^ 62 -> to_Z ((n + 7) >> 3)%uint63 = (to_Z n + 7) / 8.
Proof. intros n Hn. rewrite to_Z_lsr3, to_Z_add_small; change (to_Z 7%uint63) with 7; [reflexivity | slia]. Qed.
Lemma ncells_eq : forall n : int, to_Z n < 2 ^ 62 -> to_Z ((((n + 7) >> 3) + 7) >> 3)%uint63 = ((to_Z n + 7) / 8 + 7) / 8.
Proof.
  intros n Hn. pose proof (i63_range n). rewrite to_Z_lsr3, to_Z_add_small; rewrite (nsh_eq n Hn); change (to_Z 7%uint63) with 7; [reflexivity|].
  Z.div_mod_to_equations. slia.
Qed.

(* [comment removed for export] *)
Section Sh.
  Variable IM : fimage.
  Variable rho : int -> word.
  Hypothesis Hrho0 : rho 0%uint63 = Z_to_bv 64 0.

  (* [comment removed for export] *)
  Lemma sh_cells_inv : forall n ci c, to_Z n < 2 ^ 62 -> iget ci (sh_cells n) = Some c ->
    to_Z ci < (((to_Z n + 7) / 8) + 7) / 8 /\ c = sh_cell n ci.
  Proof.
    intros n ci c Hn H. unfold sh_cells in H. pose proof (i63_range n). pose proof (i63_range ci).
    destruct (iget_iof_list_map_In (fun ci0 : int => ci0) (fun ci0 => sh_cell n ci0) _ _ _ H) as (x & Hin & <- & ->).
    split; [|reflexivity]. unfold iseq in Hin. apply in_map_iff in Hin as (k & <- & Hk). apply in_seq in Hk.
    rewrite (ncells_eq n Hn) in Hk. rewrite Uint63.of_Z_spec. change wB with (2 ^ 63).
    rewrite Z.mod_small; Z.div_mod_to_equations; slia.
  Qed.
  Lemma sh_cells_none : forall n ci, to_Z n < 2 ^ 62 -> iget ci (sh_cells n) = None -> (((to_Z n + 7) / 8) + 7) / 8 <= to_Z ci.
  Proof.
    intros n ci Hn H. pose proof (i63_range n). pose proof (i63_range ci).
    destruct (Z_lt_dec (to_Z ci) ((((to_Z n + 7) / 8) + 7) / 8)) as [Hlt|]; [|slia]. exfalso.
    apply (iget_iof_list_map_None (fun ci0 : int => ci0) (fun ci0 => sh_cell n ci0) _ _ H ci); [|reflexivity].
    apply in_iseq. rewrite (ncells_eq n Hn). slia.
  Qed.

  (* [comment removed for export] *)
  Lemma sh_region_part : forall (wr : bool) m t n A,
    rho (t + 1)%uint63 = wa (sh A) -> bv_unsigned (rho t) = A -> to_Z t + 1 < 2 ^ 60 ->
    1 <= to_Z n <= 32768 -> A + to_Z n <= AAPP_HI ->
    SHAD m A (shadow_of (to_Z n)) ->
    mem_part asegs IM rho m (t + 1)%uint63 (sh_region wr t n).
  Proof.
    intros wr m t n A Hr1 HrA Ht Hn Hhi SH.
    pose proof (i63_range t). pose proof (i63_range n). pose proof SH as (HA0 & HA8 & [HBy HW]).
    rewrite (shadow_of_length (to_Z n)) in HW by slia.
    assert (Et1 : to_Z (t + 1)%uint63 = to_Z t + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; slia).
    assert (Elen : to_Z ((n + 7) >> 3)%uint63 = nsh (to_Z n)) by (unfold nsh; apply nsh_eq; slia).
    assert (HshA : sh A = 2147450880 + A / 8) by (unfold sh; rewrite ASHADOW_BASE_val; reflexivity).
    assert (HshAlo : 0 < sh A /\ 0 <= nsh (to_Z n) /\ sh A + nsh (to_Z n) < 2 ^ 62).
    { unfold nsh, AAPP_HI in *. rewrite HshA. Z.div_mod_to_equations. slia. }
    assert (Hur1 : bv_unsigned (rho (t + 1)%uint63) = sh A) by (rewrite Hr1; apply wa_unsigned; slia).
    split.
    - (* [comment removed for export] *)
      unfold region_ok, sh_region. cbn [rg_lo rg_len rg_align rg_clo rg_chi rg_kind rg_dflt]. rewrite Et1, Elen, Hur1.
      change (to_Z 0%uint63) with 0. unfold clo_dflt, chi_dflt. change (to_Z 0) with 0. change (to_Z 9223372036854775807) with (2 ^ 63 - 1).
      pose proof (i63_range ((n + 7) >> 3)%uint63). change (2 ^ 0) with 1.
      repeat split; try slia.
      rewrite Hur1, HrA, HshA. unfold shadow_K. change (to_Z 2147450880) with 2147450880. slia.
    - intros pn p Hpn Hp. pose proof (i63_range pn).
      unfold page_at, sh_region in Hp. cbn [rg_pages rg_dflt] in Hp. rewrite iget_iset, iget_iempty in Hp.
      destruct (pn =? 0)%uint63 eqn:Epn.
      2:{ destruct (t + 1 =? 0)%uint63 eqn:E0; [apply Uint63.eqb_spec in E0; apply (f_equal to_Z) in E0; rewrite Et1 in E0; change (to_Z 0%uint63) with 0 in E0; slia|].
          destruct wr; [|discriminate].
          destruct (page_in_region _ pn) eqn:Hpir; [|discriminate].
          destruct (page_in_region_spec _ _ Hpir) as (_ & _ & Hlt & _). cbn [rg_len] in Hlt. rewrite Elen in Hlt.
          apply Uint63.eqb_false_spec in Epn. exfalso. apply Epn. apply to_Z_inj. change (to_Z 0%uint63) with 0. unfold nsh in Hlt. slia. }
      apply Uint63.eqb_spec in Epn. subst pn. injection Hp as <-.
      cbn [rg_lo rg_len]. change (to_Z 0%uint63) with 0. rewrite Elen.
      assert (HBl : blim (RGK 0%uint63 ((n + 7) >> 3)%uint63 0%uint63 (if wr then Some PKUnk else None) (iset 0%uint63 (PG wr PKUnk (sh_cells n)) iempty) clo_dflt chi_dflt (RK_shadow t)) 0%uint63
                   = nsh (to_Z n)).
      { unfold blim. cbn [rg_len]. rewrite Elen. change (to_Z 0%uint63) with 0. unfold nsh in *. slia. }
      rewrite HBl. split; [| unfold sh_region; cbn [rg_lo]; change (to_Z 0%uint63) with 0; unfold nsh; slia].
      assert (Hadr : forall z, 0 <= z -> z < nsh (to_Z n) -> adr rho (t + 1)%uint63 z = wa (sh A + z)).
      { intros z Hz0 Hz. rewrite (adr_eq_wa rho (t + 1)%uint63 (sh A) z Hr1); [reflexivity | slia | slia | slia]. }
      pose proof HBy as (_ & _ & HBi). rewrite <- (Nat2Z.id (length (shadow_of (to_Z n)))), shadow_of_length in HBi by slia.
      assert (HBz : forall i : Z, 0 <= i < nsh (to_Z n) -> mrd asegs m (wa (sh A + i)) = nth_error (shadow_of (to_Z n)) (Z.to_nat i)).
      { intros i Hi. rewrite <- (HBi (Z.to_nat i)) by slia. f_equal. f_equal. slia. }
      change (to_Z 0%uint63) with 0.
      split; [|split; [|split]].
      + (* [comment removed for export] *) intros _ j Hj. rewrite Z.mul_0_l, Z.add_0_l. rewrite Hadr by slia. destruct HW as (_ & _ & W). apply W. slia.
      + (* [comment removed for export] *)
        intros ci v Hci Hc. pose proof (i63_range ci).
        unfold cell_at in Hc. cbn [pg_cells pg_kind] in Hc.
        destruct (iget ci (sh_cells n)) as [c|] eqn:Hg; [| discriminate].
        destruct (sh_cells_inv n _ _ ltac:(slia) Hg) as [Hcilt ->].
        unfold sh_cell in Hc.
        destruct (((ci + 1) * 8 <=? n >> 3))%uint63 eqn:Ecv; [|discriminate]. injection Hc as <-.
        pose proof (proj1 (leb8_spec ci n ltac:(slia) ltac:(slia)) Ecv) as EcvZ.
        intros j Hj. rewrite (fk_dv_conc rho _ Hrho0), wbv_w_zero. rewrite Z.mul_0_l, Z.add_0_l.
        rewrite Hadr by (unfold nsh in *; Z.div_mod_to_equations; slia).
        change (rview asegs m (wa (sh A + (to_Z ci * 8 + Z.of_nat j)))) with (mrd asegs m (wa (sh A + (to_Z ci * 8 + Z.of_nat j)))).
        rewrite HBz by (unfold nsh in *; Z.div_mod_to_equations; slia).
        rewrite shadow_of_nth_full by (try slia; rewrite Z2Nat.id by slia; Z.div_mod_to_equations; slia).
        symmetry. apply nth_wbytes8_w0. exact Hj.
      + (* [comment removed for export] *)
        intros ci sl Hci0 Hci Hg. pose proof (i63_range ci).
        cbn [pg_cells] in Hg. destruct (sh_cells_inv n _ _ ltac:(slia) Hg) as [Hcilt Ec]. unfold sh_cell in Ec.
        destruct (((ci + 1) * 8 <=? n >> 3))%uint63 eqn:Ecv; [discriminate|]. injection Ec as Esl.
        assert (Encv : ~ (to_Z ci + 1) * 8 <= to_Z n / 8).
        { intros K. pose proof (proj2 (leb8_spec ci n ltac:(slia) ltac:(slia)) K). congruence. }
        intros j Hj. rewrite Z.mul_0_l, Z.add_0_l.
        assert (Esg : sget j sl = sh_slot n ((n + 7) >> 3)%uint63 (ci * 8 + j)%uint63).
        { rewrite Esl. rewrite sget_SL by exact Hj.
          assert (K : to_Z j = 0 \/ to_Z j = 1 \/ to_Z j = 2 \/ to_Z j = 3 \/ to_Z j = 4 \/ to_Z j = 5 \/ to_Z j = 6 \/ to_Z j = 7) by slia.
          assert (Ej : forall z : int, to_Z j = to_Z z -> j = z) by (intros z Hz; apply to_Z_inj; exact Hz).
          destruct K as [K|[K|[K|[K|[K|[K|[K|K]]]]]]];
            [ rewrite (Ej 0%uint63 K) | rewrite (Ej 1%uint63 K) | rewrite (Ej 2%uint63 K) | rewrite (Ej 3%uint63 K)
            | rewrite (Ej 4%uint63 K) | rewrite (Ej 5%uint63 K) | rewrite (Ej 6%uint63 K) | rewrite (Ej 7%uint63 K) ]; cbn [Z.to_nat to_Z nth];
            try reflexivity.
          cbn. replace (ci * 8 + 0)%uint63 with (ci * 8)%uint63; [reflexivity|]. apply to_Z_inj. rewrite to_Z_add_small; [| change (to_Z 0%uint63) with 0; pose proof (i63_range (ci * 8)%uint63); slia]. change (to_Z 0%uint63) with 0. slia. }
        rewrite Esg. unfold sh_slot.
        assert (Es : to_Z (ci * 8 + j)%uint63 = to_Z ci * 8 + to_Z j).
        { rewrite to_Z_add_small; rewrite to_Z_mul_small; change (to_Z 8%uint63) with 8; slia. }
        destruct ((ci * 8 + j <? (n + 7) >> 3))%uint63 eqn:Elt.
        * apply Uint63.ltb_spec in Elt. rewrite Es, Elen in Elt. split; [| intros K; exfalso; slia]. intros _.
          cbn [slot_ok]. rewrite Hadr by slia.
          change (rview asegs m (wa (sh A + (to_Z ci * 8 + to_Z j)))) with (mrd asegs m (wa (sh A + (to_Z ci * 8 + to_Z j)))).
          rewrite HBz by slia.
          rewrite shadow_of_byte by (try slia; rewrite Z2Nat.id by slia; exact Elt).
          rewrite Z2Nat.id by slia. f_equal. unfold b8. f_equal.
          destruct (Z.leb_spec ((to_Z ci * 8 + to_Z j + 1) * 8) (to_Z n)) as [Hle|Hgt].
          -- rewrite sh_byte_full; [reflexivity | slia | rewrite Es; slia | rewrite Es; slia].
          -- rewrite sh_byte_last; [rewrite Es; reflexivity | slia | rewrite Es; slia | rewrite Es; slia | rewrite Es; unfold nsh in Elt; Z.div_mod_to_equations; slia].
        * split; [intros K; exfalso | intros _; reflexivity].
          assert (K' : ((ci * 8 + j <? (n + 7) >> 3) = true)%uint63); [|congruence]. apply Uint63.ltb_spec. rewrite Es, Elen. exact K.
      + (* [comment removed for export] *)
        intros ci Hci0 Hcut. pose proof (i63_range ci). unfold cell_at. cbn [pg_cells pg_kind].
        destruct (iget ci (sh_cells n)) as [c|] eqn:Hg; [|reflexivity].
        destruct (sh_cells_inv n _ _ ltac:(slia) Hg) as [Hcilt ->]. unfold sh_cell.
        destruct (((ci + 1) * 8 <=? n >> 3))%uint63 eqn:Ecv; [|reflexivity]. exfalso.
        apply (proj1 (leb8_spec ci n ltac:(slia) ltac:(slia))) in Ecv. unfold nsh in Hcut. Z.div_mod_to_equations. slia.
  Qed.
End Sh.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma abs_pages_inv : forall (L : list (int * cell)) pn p ci c,
  iget pn (abs_pages L) = Some p -> iget ci (pg_cells p) = Some c ->
  exists a, In (a, c) L /\ (a >> 12)%uint63 = pn /\ ((a land 4095) >> 3)%uint63 = ci.
Proof.
  induction L as [|[a0 c0] L IH]; intros pn p ci c Hp Hc; cbn [abs_pages fold_right] in Hp.
  - rewrite iget_iempty in Hp. discriminate.
  - fold (abs_pages L) in Hp. cbn [fst snd] in Hp. rewrite iget_iset in Hp.
    destruct (pn =? a0 >> 12)%uint63 eqn:Epn.
    + apply Uint63.eqb_spec in Epn. injection Hp as <-. cbn [pg_cells] in Hc. rewrite iget_iset in Hc.
      destruct (ci =? (a0 land 4095) >> 3)%uint63 eqn:Eci.
      * apply Uint63.eqb_spec in Eci. injection Hc as <-. exists a0. split; [left; reflexivity | split; congruence].
      * destruct (iget (a0 >> 12)%uint63 (abs_pages L)) as [p'|] eqn:Hp'.
        -- destruct (IH _ _ _ _ Hp' Hc) as (a & Hin & Ha & Hb). exists a. split; [right; exact Hin | split; congruence].
        -- cbn [pg_cells] in Hc. rewrite iget_iempty in Hc. discriminate.
    + destruct (IH _ _ _ _ Hp Hc) as (a & Hin & Ha & Hb). exists a. split; [right; exact Hin | split; assumption].
Qed.

Lemma abs_pages_nonempty : forall (L : list (int * cell)) pn p,
  iget pn (abs_pages L) = Some p -> exists a c, In (a, c) L /\ (a >> 12)%uint63 = pn.
Proof.
  induction L as [|[a0 c0] L IH]; intros pn p Hp; cbn [abs_pages fold_right] in Hp.
  - rewrite iget_iempty in Hp. discriminate.
  - fold (abs_pages L) in Hp. cbn [fst snd] in Hp. rewrite iget_iset in Hp.
    destruct (pn =? a0 >> 12)%uint63 eqn:Epn.
    + apply Uint63.eqb_spec in Epn. exists a0, c0. split; [left; reflexivity | congruence].
    + destruct (IH _ _ Hp) as (a & c & Hin & Ha). exists a, c. split; [right; exact Hin | exact Ha].
Qed.

Section Abs.
  Variable IM : fimage.
  Variable rho : int -> word.
  Hypothesis Hrho0 : rho 0%uint63 = Z_to_bv 64 0.

  (* [comment removed for export] *)
  Definition abs_cell_ok (m : mem) (a : Z) (c : cell) : Prop :=
    match c with
    | CV (FV t w) => t = 0%uint63 /\ bytes_at asegs m a (Z_to_le_bytes 8 (wZ w))
    | CB sl => forall j : int, 0 <= to_Z j < 8 ->
               match sget j sl with
               | SK b => mrd asegs m (wa (a + to_Z j)) = Some (Z_to_bv 8 (to_Z b))
               | SU => True
               | SV _ _ => False
               end
    | CU => False
    end.
  Lemma abs_region_part : forall m (lo len : int) (L : list (int * cell)),
    rho 3%uint63 = Z_to_bv 64 0 ->
    to_Z lo mod 4096 = 0 -> to_Z len mod 8 = 0 -> 0 < to_Z lo -> to_Z len <= 2 ^ 62 ->
    (forall a c, In (a, c) L -> to_Z a mod 8 = 0 /\ to_Z lo <= to_Z a /\ to_Z a + 8 <= to_Z len /\ abs_cell_ok m (to_Z a) c) ->
    mem_part asegs IM rho m 3%uint63 (abs_region lo len L).
  Proof.
    intros m lo len L Hr3 Hlo Hlen Hlo0 Hlen62 HL. pose proof (i63_range lo). pose proof (i63_range len).
    assert (Hu3 : bv_unsigned (rho 3%uint63) = 0) by (rewrite Hr3; reflexivity).
    assert (Hadr : forall z, 0 <= z < 2 ^ 64 -> adr rho 3%uint63 z = wa z).
    { intros z Hz. rewrite (adr_eq_wa rho 3%uint63 0 z); [f_equal; slia | rewrite Hr3; reflexivity | slia | slia | slia]. }
    split.
    - unfold region_ok, abs_region. cbn [rg_lo rg_len rg_align rg_clo rg_chi rg_kind rg_dflt]. rewrite Hu3.
      change (to_Z 0%uint63) with 0. change (to_Z 3%uint63) with 3. change (2 ^ 0) with 1. cbn [rkind_ok].
      repeat split; try slia.
    - intros pn p Hpn Hp. pose proof (i63_range pn).
      unfold page_at, abs_region in Hp. cbn [rg_pages rg_dflt] in Hp. change ((3 =? 0)%uint63) with false in Hp. cbv iota in Hp.
      destruct (iget pn (abs_pages L)) as [p0|] eqn:Hg; [|discriminate]. injection Hp as <-.
      destruct (abs_pages_nonempty _ _ _ Hg) as (a1 & c1 & Hin1 & Ha1).
      destruct (HL a1 c1 Hin1) as (A8 & Alo & Ahi & _). pose proof (i63_range a1).
      apply (f_equal to_Z) in Ha1. rewrite to_Z_lsr12 in Ha1.
      assert (Hpnrng : to_Z lo <= to_Z pn * 4096 /\ to_Z pn * 4096 < to_Z len) by (rewrite <- Ha1; Z.div_mod_to_equations; slia).
      cbn [rg_lo rg_len]. split; [|exact Hpnrng].
      (* [comment removed for export] *)
      set (B := blim (abs_region lo len L) pn) in |- *.
      assert (HBmin : B = Z.min 4096 (to_Z len - to_Z pn * 4096)) by reflexivity.
      assert (HcB : forall a c ci, In (a, c) L -> to_Z a = to_Z pn * 4096 + to_Z ci * 8 -> 0 <= to_Z ci -> to_Z ci * 8 < B -> to_Z ci * 8 + 8 <= B).
      { intros a c ci Hin Ea Hci0 HciB. destruct (HL a c Hin) as (C8 & Clo & Chi & _). rewrite HBmin in HciB |- *. clear - Chi Ea Hci0 HciB.
        slia. }
      clearbody B. destruct (abs_pages_shape _ _ _ Hg) as [Hwr Hkd].
      split; [|split; [|split]].
      + intros Hw. rewrite Hwr in Hw. discriminate.
      + intros ci v Hci Hc. pose proof (i63_range ci). unfold cell_at in Hc. rewrite Hkd in Hc.
        destruct (iget ci (pg_cells p0)) as [c|] eqn:Hcg; [|discriminate]. destruct c as [v'| |sl]; try discriminate. injection Hc as <-.
        destruct (abs_pages_inv _ _ _ _ _ Hg Hcg) as (a & Hin & Ha & Hb).
        destruct (HL a _ Hin) as (B8 & Blo & Bhi & HC). destruct v' as [t w]. cbn [abs_cell_ok] in HC. destruct HC as [-> HBy]. pose proof (i63_range a).
        apply (f_equal to_Z) in Ha. rewrite to_Z_lsr12 in Ha. apply (f_equal to_Z) in Hb. rewrite to_Z_lsr3, to_Z_land4095 in Hb.
        assert (Ea : to_Z a = to_Z pn * 4096 + to_Z ci * 8) by (rewrite <- Ha, <- Hb; Z.div_mod_to_equations; slia).
        intros j Hj. rewrite Hadr by slia. rewrite (fk_dv_conc rho _ Hrho0). unfold wbytes8. rewrite wbv_unsigned.
        destruct HBy as (_ & _ & HBi). rewrite length_Z_to_le_bytes in HBi.
        change (rview asegs m (wa (to_Z pn * 4096 + to_Z ci * 8 + Z.of_nat j))) with (mrd asegs m (wa (to_Z pn * 4096 + to_Z ci * 8 + Z.of_nat j))).
        rewrite <- Ea. exact (HBi j Hj).
      + intros ci sl Hci0 Hci Hcg. pose proof (i63_range ci).
        destruct (abs_pages_inv _ _ _ _ _ Hg Hcg) as (a & Hin & Ha & Hb). destruct (HL a _ Hin) as (B8 & Blo & Bhi & HC). cbn [abs_cell_ok] in HC.
        pose proof (i63_range a).
        apply (f_equal to_Z) in Ha. rewrite to_Z_lsr12 in Ha. apply (f_equal to_Z) in Hb. rewrite to_Z_lsr3, to_Z_land4095 in Hb.
        assert (Ea : to_Z a = to_Z pn * 4096 + to_Z ci * 8) by (rewrite <- Ha, <- Hb; Z.div_mod_to_equations; slia).
        intros j Hj. pose proof (i63_range j). pose proof (HcB a _ ci Hin Ea Hci0 Hci) as HcBa.
        split; [| intros HBj; exfalso; clear - HcBa Hj HBj; slia]. intros _.
        specialize (HC j Hj). rewrite Hadr by slia.
        destruct (sget j sl) as [b|v k|]; cbn [slot_ok]; [| exact (False_ind _ HC) | exact I].
        change (rview asegs m (wa (to_Z pn * 4096 + to_Z ci * 8 + to_Z j))) with (mrd asegs m (wa (to_Z pn * 4096 + to_Z ci * 8 + to_Z j))).
        rewrite <- Ea. exact HC.
      + intros ci Hci Hcut. pose proof (i63_range ci). unfold cell_at. rewrite Hkd.
        destruct (iget ci (pg_cells p0)) as [c|] eqn:Hcg; [|reflexivity].
        destruct (abs_pages_inv _ _ _ _ _ Hg Hcg) as (a & Hin & Ha & Hb). destruct (HL a _ Hin) as (B8 & Blo & Bhi & _). pose proof (i63_range a).
        apply (f_equal to_Z) in Ha. rewrite to_Z_lsr12 in Ha. apply (f_equal to_Z) in Hb. rewrite to_Z_lsr3, to_Z_land4095 in Hb.
        assert (Ea : to_Z a = to_Z pn * 4096 + to_Z ci * 8) by (rewrite <- Ha, <- Hb; Z.div_mod_to_equations; slia).
        pose proof (HcB a _ ci Hin Ea Hci ltac:(clear - Hcut; slia)) as HcBa. exfalso. clear - HcBa Hcut. slia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma flag_region_part : forall m t fp,
    rho (t + 2)%uint63 = wa fp -> to_Z t + 2 < 2 ^ 60 -> 0 < fp -> fp + 1 < 2 ^ 62 ->
    rw_cells asegs m fp [C1 (b8 1)] ->
    mem_part asegs IM rho m (t + 2)%uint63 flag_region.
  Proof.
    intros m t fp Hr Ht Hfp0 Hfp [[_ (_ & _ & HBy)] _]. pose proof (i63_range t). cbn [cells_bytes cbytes app length] in HBy.
    assert (Et2 : to_Z (t + 2)%uint63 = to_Z t + 2) by (rewrite to_Z_add_small; change (to_Z 2%uint63) with 2; slia).
    assert (Hu : bv_unsigned (rho (t + 2)%uint63) = fp) by (rewrite Hr; apply wa_unsigned; slia).
    split.
    - unfold region_ok, flag_region. cbn [rg_lo rg_len rg_align rg_clo rg_chi rg_kind rg_dflt]. rewrite Et2, Hu.
      change (to_Z 0%uint63) with 0. change (to_Z 1%uint63) with 1. unfold clo_dflt, chi_dflt. change (to_Z 0) with 0.
      change (to_Z 9223372036854775807) with (2 ^ 63 - 1). change (2 ^ 0) with 1. cbn [rkind_ok].
      repeat split; try slia.
    - intros pn p Hpn Hp. pose proof (i63_range pn).
      unfold page_at, flag_region in Hp. cbn [rg_pages rg_dflt] in Hp. rewrite iget_iset, iget_iempty in Hp.
      destruct (pn =? 0)%uint63 eqn:Epn.
      2:{ destruct (t + 2 =? 0)%uint63 eqn:E0; [apply Uint63.eqb_spec in E0; apply (f_equal to_Z) in E0; rewrite Et2 in E0; change (to_Z 0%uint63) with 0 in E0; slia | discriminate]. }
      apply Uint63.eqb_spec in Epn. subst pn. injection Hp as <-. cbn [flag_region rg_lo rg_len]. change (to_Z 0%uint63) with 0. change (to_Z 1%uint63) with 1.
      split; [| slia].
      assert (HB : blim (RGK 0%uint63 1%uint63 0%uint63 None (iset 0%uint63 (PG false PKUnk (iset 0%uint63 (CB (SL (SK 1) SU SU SU SU SU SU SU)) iempty)) iempty) clo_dflt chi_dflt RK_plain) 0%uint63 = 1).
      { unfold blim. cbn [rg_len]. change (to_Z 1%uint63) with 1. change (to_Z 0%uint63) with 0. slia. }
      rewrite HB. split; [|split; [|split]].
      + intros Hw. discriminate Hw.
      + intros ci v Hci Hc. exfalso. slia.
      + intros ci sl Hci0 Hci Hcg. pose proof (i63_range ci).
        assert (Hcg' : iget ci (iset 0%uint63 (CB (SL (SK 1) SU SU SU SU SU SU SU)) iempty) = Some (CB sl)) by exact Hcg.
        clear Hcg. rename Hcg' into Hcg. rewrite iget_iset in Hcg.
        destruct (ci =? 0)%uint63 eqn:Eci; [|rewrite iget_iempty in Hcg; discriminate]. apply Uint63.eqb_spec in Eci. subst ci. injection Hcg as <-.
        intros j Hj. rewrite sget_SL by exact Hj. change (to_Z 0%uint63) with 0.
        assert (K : to_Z j = 0 \/ 1 <= to_Z j) by slia. destruct K as [Ej|Hj1].
        * assert (j = 0%uint63) as -> by (apply to_Z_inj; exact Ej). change (to_Z 0%uint63) with 0.
          replace (nth (Z.to_nat 0) [SK 1%uint63; SU; SU; SU; SU; SU; SU; SU] SU) with (SK 1%uint63) by reflexivity.
          split; [|intros; exfalso; slia]. intros _. cbn [slot_ok]. change (to_Z 1%uint63) with 1.
          rewrite (adr_eq_wa rho (t + 2)%uint63 fp (0 * 4096 + 0 * 8 + 0) Hr) by slia.
          change (rview asegs m (wa (fp + (0 * 4096 + 0 * 8 + 0)))) with (mrd asegs m (wa (fp + (0 * 4096 + 0 * 8 + 0)))).
          replace (fp + (0 * 4096 + 0 * 8 + 0)) with (fp + Z.of_nat 0) by slia. rewrite (HBy 0%nat) by (cbn; lia). reflexivity.
        * split; [intros; exfalso; slia|]. intros _.
          assert (K : to_Z j = 1 \/ to_Z j = 2 \/ to_Z j = 3 \/ to_Z j = 4 \/ to_Z j = 5 \/ to_Z j = 6 \/ to_Z j = 7) by slia.
          destruct K as [K|[K|[K|[K|[K|[K|K]]]]]]; rewrite K; reflexivity.
      + intros ci Hci Hcut. pose proof (i63_range ci). unfold cell_at.
        change (pg_cells _) with (iset 0%uint63 (CB (SL (SK 1) SU SU SU SU SU SU SU)) iempty). change (pg_kind _) with PKUnk.
        rewrite iget_iset, iget_iempty. destruct (ci =? 0)%uint63; reflexivity.
  Qed.
End Abs.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section StackSh.
  Context {HCEIL : HeapCeil}.
  Variable IM : fimage.
  Variable rho : int -> word.
  Hypothesis Hrho0 : rho 0%uint63 = Z_to_bv 64 0.

  Lemma stack_shadow_SHAD : forall m lo shi sp0 cs,
    stack0 m lo shi -> lo <= sp0 - cs -> sp0 <= shi -> (sp0 - cs) mod 8 = 0 -> cs mod 8 = 0 -> 0 <= cs ->
    SHAD m (sp0 - cs) (shadow_of cs).
  Proof.
    intros m lo shi sp0 cs (g & G1 & G2 & G3 & AD) Hlo Hshi Hal Hcs Hcs0.
    pose proof AD as [_ SH]. pose proof (SHAD_aligned _ _ _ SH) as [g0 g8].
    destruct (addressable_split8 m g (shi - g) (sp0 - cs - g) AD G3 ltac:(Z.div_mod_to_equations; slia) ltac:(slia)) as [_ A2].
    replace (g + (sp0 - cs - g)) with (sp0 - cs) in A2 by slia.
    destruct (addressable_split8 m (sp0 - cs) (shi - g - (sp0 - cs - g)) cs A2 ltac:(Z.div_mod_to_equations; slia) Hcs ltac:(slia)) as [[_ A3] _].
    exact A3.
  Qed.

  Lemma stack_sh_region_part : forall m lo shi sp0 (cs : int),
    rho 1%uint63 = wa (sp0 - to_Z cs) -> rho 2%uint63 = wa (sh (sp0 - to_Z cs)) ->
    stack0 m lo shi -> lo <= sp0 - to_Z cs -> sp0 <= shi -> (sp0 - to_Z cs) mod 8 = 0 -> to_Z cs mod 8 = 0 ->
    1 <= to_Z cs <= 32768 ->
    mem_part asegs IM rho m 2%uint63 (sh_region false 1%uint63 cs).
  Proof.
    intros m lo shi sp0 cs Hr1 Hr2 ST Hlo Hshi Hal Hcs8 Hcs.
    pose proof (stack0_bounds _ _ _ ST) as [B1 B2]. pose proof aceil_facts as AF.
    change 2%uint63 with (1 + 1)%uint63.
    apply (sh_region_part IM rho Hrho0 false m 1%uint63 cs (sp0 - to_Z cs)).
    - exact Hr2.
    - rewrite Hr1. apply wa_unsigned. unfold AAPP_HI in *. slia.
    - change (to_Z 1%uint63) with 1. slia.
    - exact Hcs.
    - slia.
    - eapply stack_shadow_SHAD; [exact ST | exact Hlo | exact Hshi | exact Hal | exact Hcs8 | slia].
  Qed.
End StackSh.
