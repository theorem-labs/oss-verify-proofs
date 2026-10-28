(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prog.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import FxSteps FxAcc.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain
  FxRun FxRn FxImage FxHandoff FxCellFrame FxRoFrame FxGeom I2Canon I2Mach I2Image I2Run I2RunA FxGeomA.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2A Require Import I2AInv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac slia := Zify.zify; xlia zchecker.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rho_ext (rho : int -> word) (t : int) (l : list word) : int -> word :=
  fun x => let d := to_Z x - to_Z t in
           if ((0 <=? d) && (d <? Z.of_nat (length l)))%Z then nth (Z.to_nat d) l w0 else rho x.

Lemma rho_ext_old : forall rho t l x, to_Z x < to_Z t -> rho_ext rho t l x = rho x.
Proof.
  intros rho t l x Hx. unfold rho_ext. cbv zeta.
  destruct (Z.leb_spec0 0 (to_Z x - to_Z t)); [slia|]. reflexivity.
Qed.

Lemma rho_ext_high : forall rho t l x, to_Z t + Z.of_nat (length l) <= to_Z x -> rho_ext rho t l x = rho x.
Proof.
  intros rho t l x Hx. unfold rho_ext. cbv zeta.
  destruct (Z.leb_spec0 0 (to_Z x - to_Z t)); [|reflexivity].
  destruct (Z.ltb_spec0 (to_Z x - to_Z t) (Z.of_nat (length l))); [slia | reflexivity].
Qed.

Lemma rho_ext_new : forall rho t l (k : nat), (k < length l)%nat -> to_Z t + Z.of_nat k < 2 ^ 63 ->
  rho_ext rho t l (t + of_Z (Z.of_nat k))%uint63 = nth k l w0.
Proof.
  intros rho t l k Hk Hb. unfold rho_ext. cbv zeta. pose proof (i63_range t).
  rewrite Uint63.add_spec, Uint63.of_Z_spec. change wB with (2 ^ 63).
  rewrite (Z.mod_small (Z.of_nat k)) by slia. rewrite Z.mod_small by slia.
  replace (to_Z t + Z.of_nat k - to_Z t) with (Z.of_nat k) by slia.
  destruct (Z.leb_spec0 0 (Z.of_nat k)); [|slia]. destruct (Z.ltb_spec0 (Z.of_nat k) (Z.of_nat (length l))); [|slia].
  cbn [andb]. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma rho_ext_at : forall rho t l x (k : nat), (k < length l)%nat -> to_Z x = to_Z t + Z.of_nat k ->
  rho_ext rho t l x = nth k l w0.
Proof.
  intros rho t l x k Hk Hx. unfold rho_ext. cbv zeta. rewrite Hx.
  replace (to_Z t + Z.of_nat k - to_Z t) with (Z.of_nat k) by slia.
  destruct (Z.leb_spec0 0 (Z.of_nat k)); [|slia]. destruct (Z.ltb_spec0 (Z.of_nat k) (Z.of_nat (length l))); [|slia].
  cbn [andb]. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma agree_ext : forall n rho t l, to_Z n <= to_Z t -> 0 < to_Z t -> rho 0%uint63 = Z_to_bv 64 0 ->
  agree n rho (rho_ext rho t l).
Proof.
  intros n rho t l Hn Ht H0. split.
  - rewrite rho_ext_old; [exact H0 | change (to_Z 0%uint63) with 0; slia].
  - intros x Hx. apply rho_ext_old. slia.
Qed.

Lemma agree_trans : forall n1 n2 r1 r2 r3, agree n1 r1 r2 -> agree n2 r2 r3 -> to_Z n1 <= to_Z n2 -> agree n1 r1 r3.
Proof.
  intros n1 n2 r1 r2 r3 [H0 H1] [H0' H2] Hle. split; [exact H0'|]. intros t Ht. rewrite H2 by slia. apply H1. exact Ht.
Qed.

Lemma agree_weaken : forall n n' r1 r2, agree n' r1 r2 -> to_Z n <= to_Z n' -> agree n r1 r2.
Proof. intros n n' r1 r2 [H0 H1] Hle. split; [exact H0|]. intros t Ht. apply H1. slia. Qed.

Lemma agree_refl : forall n rho, rho 0%uint63 = Z_to_bv 64 0 -> agree n rho rho.
Proof. intros n rho H. split; [exact H | intros; reflexivity]. Qed.

(* [comment removed for export] *)
Lemma dv_agree : forall n rho rho' v, agree n rho rho' -> to_Z (vtag v) < to_Z n -> dv rho' v = dv rho v.
Proof.
  intros n rho rho' [t w] [H0 H1] Hv. cbn [vtag] in Hv. unfold dv. cbn [vtag vw].
  rewrite (H1 (vbase t)); [reflexivity|].
  destruct (fk_tag_decomp t) as [E Hb0]. pose proof (fk_vkind_le5 t) as Hk. nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Pages.
  Variable segs : list Segment.
  Variable IM : fimage.
  Variable rho : int -> word.

  Lemma page_ok_transfer : forall m m' t pn B p,
    (forall j, 0 <= j < B ->
        rview segs m' (adr rho t (to_Z pn * 4096 + j)) = rview segs m (adr rho t (to_Z pn * 4096 + j))
        /\ (wview segs m (adr rho t (to_Z pn * 4096 + j)) <> None -> wview segs m' (adr rho t (to_Z pn * 4096 + j)) <> None)) ->
    page_ok segs IM rho m t pn B p -> page_ok segs IM rho m' t pn B p.
  Proof.
    intros m m' t pn B p Hm (Hwr & Hcells & Hslots & Hcut).
    assert (Hrv : forall j, 0 <= j < B -> rview segs m' (adr rho t (to_Z pn * 4096 + j)) = rview segs m (adr rho t (to_Z pn * 4096 + j))).
    { intros j Hj. exact (proj1 (Hm j Hj)). }
    split; [|split; [|split]].
    - intros Hw j Hj. apply (proj2 (Hm j Hj)). exact (Hwr Hw j Hj).
    - intros ci v Hci Hc j Hj. rewrite <- (Hcells ci v Hci Hc j Hj).
      replace (to_Z pn * 4096 + to_Z ci * 8 + Z.of_nat j) with (to_Z pn * 4096 + (to_Z ci * 8 + Z.of_nat j)) by slia.
      apply Hrv. Z.div_mod_to_equations. slia.
    - intros ci sl Hci Hcb Hg j Hj. destruct (Hslots ci sl Hci Hcb Hg j Hj) as [Hin Hout]. split; [|exact Hout].
      intros Hjb. specialize (Hin Hjb).
      rewrite slot_ok_val in Hin |- *.
      replace (to_Z pn * 4096 + to_Z ci * 8 + to_Z j) with (to_Z pn * 4096 + (to_Z ci * 8 + to_Z j)) in Hin |- * by slia.
      rewrite Hrv by slia. exact Hin.
    - exact Hcut.
  Qed.

  Lemma rview_eq_of_mem : forall m m' x, m' x = m x -> rview segs m' x = rview segs m x.
  Proof. intros m m' x E. unfold rview. rewrite E. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma page_ok_dflt : forall m t pn B,
    (forall j, 0 <= j < B -> wview segs m (adr rho t (to_Z pn * 4096 + j)) <> None) ->
    page_ok segs IM rho m t pn B (PG true PKUnk iempty).
  Proof.
    intros m t pn B Hw. split; [|split; [|split]].
    - intros _ j Hj. exact (Hw j Hj).
    - intros ci v Hci Hc. unfold cell_at in Hc. cbn [pg_cells pg_kind] in Hc. rewrite iget_iempty in Hc. discriminate.
    - intros ci sl Hci Hcb Hg. cbn [pg_cells] in Hg. rewrite iget_iempty in Hg. discriminate.
    - intros ci Hci Hcut. unfold cell_at. cbn [pg_cells pg_kind]. rewrite iget_iempty. reflexivity.
  Qed.
End Pages.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rget_FS : forall pc regs M rv k, FxState.rget (FS pc regs M rv) k = FxState.rget (FS 0 regs iempty None) k.
Proof. reflexivity. Qed.

Lemma rget_regs : forall pc regs M rv k,
  FxState.rget (FS pc regs M rv) k = if (k =? 0)%uint63 then fv0 else match iget k regs with Some v => v | None => fv0 end.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma iget_clobber_notin : forall rs t regs k, ~ In k rs -> iget k (clobber rs t regs) = iget k regs.
Proof.
  induction rs as [|r rs IH]; intros t regs k Hn; [reflexivity|]. cbn [clobber].
  rewrite IH by (intros Hin; apply Hn; right; exact Hin). rewrite iget_iset.
  destruct (k =? r)%uint63 eqn:E; [|reflexivity]. apply Uint63.eqb_spec in E. exfalso. apply Hn. left. symmetry. exact E.
Qed.

Lemma iget_clobber_in : forall rs t regs (i : nat) k,
  List.NoDup rs -> nth_error rs i = Some k -> to_Z t + Z.of_nat (length rs) < 2 ^ 63 ->
  iget k (clobber rs t regs) = Some (FV (of_Z (to_Z t + Z.of_nat i)) w_zero).
Proof.
  induction rs as [|r rs IH]; intros t regs i k Hnd Hi Ht; [destruct i; discriminate|].
  cbn [clobber]. pose proof (proj1 (NoDup_cons_iff r rs) Hnd) as [Hnin Hnd']. cbn [length] in Ht. pose proof (i63_range t). destruct i as [|i].
  - cbn in Hi. injection Hi as ->. rewrite (iget_clobber_notin rs _ _ k Hnin). rewrite iget_iset_same.
    f_equal. f_equal. apply to_Z_inj. rewrite Uint63.of_Z_spec. cbn [Z.of_nat]. rewrite Z.add_0_r. symmetry. apply Z.mod_small. change wB with (2 ^ 63). slia.
  - cbn in Hi.
    assert (Et1 : to_Z (t + 1)%uint63 = to_Z t + 1).
    { rewrite Uint63.add_spec. change (to_Z 1%uint63) with 1. change wB with (2 ^ 63). apply Z.mod_small. slia. }
    rewrite (IH (t + 1)%uint63 _ i k Hnd' Hi ltac:(rewrite Et1; slia)).
    f_equal. f_equal. f_equal. rewrite Et1. slia.
Qed.

(* [comment removed for export] *)
Definition regs_match (rho : int -> word) (F : fstate) (l : list word) : Prop :=
  forall k : nat, (1 <= k <= 31)%nat -> nth (k - 1) l w0 = dv rho (FxState.rget F (of_Z (Z.of_nat k))).

Lemma R_regs_of_match : forall rho F l Fr pc fc rsv m rom,
  rho 0%uint63 = Z_to_bv 64 0 -> length l = 31%nat -> regs_match rho F l ->
  forall r : reg, Sem.rget (core_of (MS (mkRl l) Fr pc fc rsv m rom)) r = dv rho (FxState.rget F (ireg r)).
Proof.
  intros rho F l Fr pc fc rsv m rom H0 Hlen HM r.
  unfold Sem.rget. cbn [core_of c_regs MS ms_regs].
  pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32 in Hr.
  destruct (is_x0 r) eqn:Ex.
  - unfold is_x0 in Ex. apply Z.eqb_eq in Ex. unfold ireg. rewrite Ex. change (of_Z 0) with 0%uint63.
    unfold FxState.rget. change (0 =? 0)%uint63 with true. cbv iota. symmetry. apply dv_fv0. exact H0.
  - rewrite (reg_get_mkRl l r Ex). unfold is_x0 in Ex. apply Z.eqb_neq in Ex.
    specialize (HM (Z.to_nat (bv_unsigned r)) ltac:(slia)).
    replace (Z.to_nat (bv_unsigned r) - 1)%nat with (Z.to_nat (bv_unsigned r - 1)) in HM by slia.
    rewrite HM. unfold ireg. rewrite Z2Nat.id by slia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma regs_match_intro : forall rho F l,
  (Forall (fun k : nat => nth (k - 1) l w0 = dv rho (FxState.rget F (of_Z (Z.of_nat k)))) (seq 1 31)) ->
  regs_match rho F l.
Proof.
  intros rho F l H k Hk. rewrite Forall_forall in H. apply H. apply in_seq. slia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma Z_to_le_bytes_of_bytes : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256 in Hb.
  assert (Hnn : 0 <= bytes_le_to_Z bs).
  { clear IH. induction bs as [|c cs IHc]; cbn; [slia|]. apply Z.lor_nonneg. split; [apply bv_unsigned_in_range|]. apply Z.shiftl_nonneg. exact IHc. }
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
    rewrite <- Z.land_ones by slia. rewrite Z.land_lor_distr_l.
    rewrite (Z.land_ones (bv_unsigned b) 8) by slia. rewrite Z.mod_small by slia.
    replace (Z.land (Z.shiftl (bytes_le_to_Z bs) 8) (Z.ones 8)) with 0; [rewrite Z.lor_0_r; reflexivity|].
    symmetry. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8).
    + rewrite Z.shiftl_spec_low by slia. reflexivity.
    + rewrite Z.ones_spec_high by slia. apply andb_false_r.
  - rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by slia.
    rewrite (Z.shiftr_eq_0 (bv_unsigned b) 8); [rewrite Z.lor_0_l; exact IH | slia |].
    destruct (Z.eq_dec (bv_unsigned b) 0) as [->|]; [cbn; slia|]. apply Z.log2_lt_pow2; slia.
Qed.

Lemma bytes_le_to_Z_nonneg : forall bs, 0 <= bytes_le_to_Z bs.
Proof.
  induction bs as [|c cs IHc]; cbn; [slia|]. apply Z.lor_nonneg. split; [apply bv_unsigned_in_range|]. apply Z.shiftl_nonneg. exact IHc.
Qed.

Lemma bytes_le_to_Z_bound : forall bs, 0 <= bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof.
  intros bs. pose proof (bytes_le_to_Z_nonneg bs) as H0.
  pose proof (bytes_le_to_Z_of_le_bytes (length bs) (bytes_le_to_Z bs) H0) as E.
  rewrite Z_to_le_bytes_of_bytes in E.
  pose proof (Z.mod_pos_bound (bytes_le_to_Z bs) (2 ^ (8 * Z.of_nat (length bs))) ltac:(apply Z.pow_pos_nonneg; slia)).
  slia.
Qed.

Section Errno.
  Variable segs : list Segment.

  Lemma rw_c4_of_cb4 : forall m a bs, length bs = 4%nat ->
    rw_cells segs m a [Cells.CB 4 bs] -> rw_cells segs m a [C4 (le_bytes_to_word bs)].
  Proof.
    intros m a bs Hlen [[Hwf Hb] Hw]. split; [split|].
    - cbn. split; exact I.
    - cbn [cells_bytes cbytes] in Hb |- *. rewrite app_nil_r in Hb |- *. unfold le4, le_bytes_to_word.
      rewrite Z_to_bv_unsigned.
      assert (Hnn : 0 <= bytes_le_to_Z bs < 2 ^ 32).
      { pose proof (bytes_le_to_Z_bound bs) as E. rewrite Hlen in E. exact E. }
      unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by slia.
      replace 4%nat with (length bs) at 1 by exact Hlen. rewrite Z_to_le_bytes_of_bytes. exact Hb.
    - exact Hw.
  Qed.

  Lemma rw_c4_of_stk : forall m a, stk segs m a (a + 4) -> exists v, rw_cells segs m a [C4 v].
  Proof.
    intros m a Hs. destruct (stk_carve segs m a (a + 4) 4 Hs ltac:(slia)) as [_ (junk & Hrw)].
    replace (a + 4 - Z.of_nat 4) with a in Hrw by slia.
    pose proof Hrw as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [Hlen _].
    exists (le_bytes_to_word junk). apply rw_c4_of_cb4; [exact Hlen | exact Hrw].
  Qed.

  (* [comment removed for export] *)
  Lemma nth_error_le4_le8 : forall (v : word) (j : nat), (j < 4)%nat -> nth_error (le4 v) j = nth_error (wbytes8 v) j.
  Proof.
    intros v j Hj. unfold le4, wbytes8.
    do 4 (destruct j as [|j]; [reflexivity|]). slia.
  Qed.
End Errno.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Inv.
  Open Scope uint63_scope.

  Lemma conc63_inv : forall v n, conc63 v = Some n -> v = FV 0 (W64 0 n).
  Proof.
    intros [t [top lo]] n H. unfold conc63 in H.
    destruct ((t =? 0) && (top =? 0))%uint63 eqn:E; [|discriminate]. apply andb_true_iff in E as [E1 E2].
    apply Uint63.eqb_spec in E1. apply Uint63.eqb_spec in E2. subst. injection H as ->. reflexivity.
  Qed.

  Lemma base_tag_inv : forall v t, base_tag v = Some t -> v = FV t (W64 0 0) /\ t <> 0.
  Proof.
    intros [t0 [top lo]] t H. unfold base_tag in H.
    destruct (negb (t0 =? 0) && (top =? 0) && (lo =? 0))%uint63 eqn:E; [|discriminate].
    rewrite !andb_true_iff in E. destruct E as [[E1 E2] E3]. apply negb_true_iff in E1.
    apply Uint63.eqb_spec in E2. apply Uint63.eqb_spec in E3. subst. injection H as ->.
    split; [reflexivity|]. intros ->. rewrite Uint63.eqb_refl in E1. discriminate.
  Qed.

  Lemma call_sp_inv : forall K F off, call_sp K F = Some off ->
    FxState.rget F 2 = FV 1 (W64 0 off)
    /\ (to_Z (c_mstack K) <= to_Z off)%Z /\ (to_Z off <= to_Z (c_stack K))%Z /\ (to_Z off mod 16 = 0)%Z.
  Proof.
    intros K F off H. unfold call_sp in H. destruct (FxState.rget F 2) as [t [top o]].
    destruct ((t =? 1) && (top =? 0) && (c_mstack K <=? o) && (o <=? c_stack K) && (o land 15 =? 0))%uint63 eqn:E; [|discriminate].
    injection H as ->. rewrite !andb_true_iff in E. destruct E as [[[[E1 E2] E3] E4] E5].
    apply Uint63.eqb_spec in E1. apply Uint63.eqb_spec in E2. subst.
    apply Uint63.leb_spec in E3. apply Uint63.leb_spec in E4.
    apply Uint63.eqb_spec in E5. apply (f_equal to_Z) in E5.
    rewrite (i63_land_ones off 15%uint63 4 eq_refl ltac:(slia)) in E5. change (to_Z 0) with 0%Z in E5. change (2 ^ 4)%Z with 16%Z in E5.
    repeat split; try assumption; reflexivity.
  Qed.

  Lemma call_link_inv : forall F l, call_link F = Some l ->
    FxState.rget F 1 = FV 0 (W64 0 l) /\ (to_Z l mod 2 = 0)%Z /\ (to_Z l < 4611686018427387900)%Z.
  Proof.
    intros F l H. unfold call_link in H. destruct (conc63 (FxState.rget F 1)) as [l0|] eqn:E; [|discriminate].
    destruct (((l0 land 1) =? 0) && (l0 <? 4611686018427387900))%uint63 eqn:E2; [|discriminate]. injection H as ->.
    apply andb_true_iff in E2 as [E2 E3]. apply Uint63.eqb_spec in E2. apply (f_equal to_Z) in E2.
    rewrite i63_land1 in E2. change (to_Z 0) with 0%Z in E2. apply Uint63.ltb_spec in E3.
    split; [exact (conc63_inv _ _ E)|]. split; [exact E2 | exact E3].
  Qed.

  Lemma tp_ok_inv : forall K F, tp_ok K F = true -> FxState.rget F 4 = FV 0 (W64 0 (c_tp K)).
  Proof.
    intros K F H. unfold tp_ok in H. destruct (conc63 (FxState.rget F 4)) as [v|] eqn:E; [|discriminate].
    apply Uint63.eqb_spec in H. subst v. exact (conc63_inv _ _ E).
  Qed.

  Lemma resv_none_inv : forall F, resv_none F = true -> f_resv F = None.
  Proof. intros F H. unfold resv_none in H. destruct (f_resv F); [discriminate | reflexivity]. Qed.

  Lemma err_page_ok_inv : forall K M, err_page_ok K M = true ->
    exists rg0 p, iget 0 M = Some rg0 /\ in_region rg0 (c_errcell K) 8 = true
                  /\ iget (c_errcell K >> 12) (rg_pages rg0) = Some p /\ pg_wr p = true.
  Proof.
    intros K M H. unfold err_page_ok in H. destruct (iget 0 M) as [rg0|] eqn:E0; [|discriminate].
    apply andb_true_iff in H as [H1 H2]. destruct (iget (c_errcell K >> 12) (rg_pages rg0)) as [p|] eqn:Ep; [|discriminate].
    exists rg0, p. split; [first [reflexivity | eassumption]|]. split; [exact H1|]. split; [first [reflexivity | eassumption] | exact H2].
  Qed.

  Lemma call_ok_inv : forall K st off l, call_ok K st = Some (off, l) ->
    call_sp K (i_F st) = Some off /\ call_link (i_F st) = Some l
    /\ tp_ok K (i_F st) = true /\ resv_none (i_F st) = true /\ err_page_ok K (f_mem (i_F st)) = true
    /\ (to_Z (i_n st) < to_Z two59)%Z /\ (2 <= to_Z (i_n st))%Z.
  Proof.
    intros K st off l H. unfold call_ok in H.
    destruct (call_sp K (i_F st)) as [off'|] eqn:E1; [|discriminate].
    destruct (call_link (i_F st)) as [l'|] eqn:E2; [|discriminate].
    destruct (tp_ok K (i_F st) && resv_none (i_F st) && err_page_ok K (f_mem (i_F st)) && (i_n st <? two59) && (2 <=? i_n st))%uint63 eqn:E; [|discriminate].
    injection H as -> ->. rewrite !andb_true_iff in E. destruct E as [[[[E3 E4] E5] E6] E7].
    apply Uint63.ltb_spec in E6. apply Uint63.leb_spec in E7. change (to_Z 2) with 2%Z in E7.
    repeat split; assumption || reflexivity.
  Qed.

  Lemma drop_stack_inv : forall off M M1, drop_stack off M = Some M1 ->
    exists rg1, iget 1 M = Some rg1 /\ M1 = iset 1 (drop_below off rg1) M.
  Proof.
    intros off M M1 H. unfold drop_stack in H. destruct (iget 1 M) as [rg1|] eqn:E; [|discriminate].
    injection H as <-. exists rg1. split; first [reflexivity | eassumption].
  Qed.

  Definition err_region (K : i2consts) (te : int) (rg0 : region) (p : page) : region :=
    RGK (rg_lo rg0) (rg_len rg0) (rg_align rg0) (rg_dflt rg0)
        (iset (c_errcell K >> 12) (PG true (pg_kind p) (iset ((c_errcell K land 4095) >> 3) (err_cell K te) (pg_cells p))) (rg_pages rg0))
        (rg_clo rg0) (rg_chi rg0) (rg_kind rg0).

  Lemma set_errno_inv : forall K te M M2, set_errno K te M = Some M2 ->
    exists rg0 p, iget 0 M = Some rg0 /\ iget (c_errcell K >> 12) (rg_pages rg0) = Some p /\ pg_wr p = true
                  /\ M2 = iset 0 (err_region K te rg0 p) M.
  Proof.
    intros K te M M2 H. unfold set_errno in H. destruct (iget 0 M) as [rg0|] eqn:E0; [|discriminate].
    cbv zeta in H. destruct (iget (c_errcell K >> 12) (rg_pages rg0)) as [p|] eqn:Ep; [|discriminate].
    destruct (pg_wr p) eqn:Ew; [|discriminate]. injection H as <-.
    exists rg0, p. split; [reflexivity|]. split; [exact Ep|]. split; [exact Ew | reflexivity].
  Qed.
End Inv.
