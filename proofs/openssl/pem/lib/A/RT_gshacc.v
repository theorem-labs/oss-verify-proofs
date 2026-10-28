(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Mem Frame Cells ImageA.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Start Require Import AsanRegModel AsanGshModel A_RegConsts A_Gsh.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem RT_state RT_rep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma gsh_sorted_al : forall a p d, GSM.sortedb p a = true -> In d a -> RGM.d_beg d mod 8 = 0.
Proof.
  induction a as [|e r IH]; intros p d H Hin; [destruct Hin|]. cbn [GSM.sortedb] in H.
  apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3].
  apply andb_prop in H as [H1 H2]. destruct Hin as [<-|Hin]; [apply Z.eqb_eq in H2; exact H2 | exact (IH _ d H6 Hin)].
Qed.

Theorem gsh_acc : forall (m : mem) (d : RGM.desc) (a n : Z), gsh_rep m -> In d A_GTAB ->
  RGM.d_beg d <= a -> a + n <= RGM.d_beg d + RGM.d_size d -> RGM.d_beg d + RGM.d_size d <= SEGTOP_A ->
  (RGM.d_beg d + RGM.d_size d <= RGM.c_tab A_RGC \/ RGM.c_tabend A_RGC <= RGM.d_beg d) ->
  acc asegs m a n.
Proof.
  intros m d a n GS Hin H1 H2 H3 HT i Hi.
  pose proof (GSM.sorted_in _ _ _ A_GTAB_sorted Hin) as (S1 & S2 & S3 & _). pose proof (gsh_sorted_al _ _ _ A_GTAB_sorted Hin) as S8.
  change (RGM.l_ilo A_RGL) with 0x10000 in S1.
  set (beg := RGM.d_beg d) in *. set (sz := RGM.d_size d) in *. set (swr := RGM.d_swr d) in *.
  pose proof (Z.div_mod (a + i) 8 ltac:(lia)) as DA. pose proof (Z.mod_pos_bound (a + i) 8 ltac:(lia)) as RA.
  pose proof (Z.div_mod beg 8 ltac:(lia)) as DB. rewrite S8 in DB.
  pose proof (Z.div_mod sz 8 ltac:(lia)) as DS. pose proof (Z.mod_pos_bound sz 8 ltac:(lia)) as RS.
  pose proof (Z.div_mod swr 8 ltac:(lia)) as DW. rewrite S2 in DW.
  assert (ESHg : forall x, RGM.shad (RGM.c_lay A_RGC) x = shad x) by (intros x; unfold RGM.shad, shad; change (RGM.l_shb (RGM.c_lay A_RGC)) with SHB; lia).
  assert (ES8 : 8 * (SEGTOP_A / 8) = SEGTOP_A) by reflexivity.
  assert (HX : shad 0x10000 <= shad (a + i) < shad SEGTOP_A).
  { unfold shad. split; [apply Z.add_le_mono_r; apply Z.div_le_mono; lia | lia]. }
  pose proof (GS (shad (a + i)) HX) as CELL.
  (* [comment removed for export] *)
  assert (EW : GSM.gshw A_RGC A_GTAB (shad (a + i)) = GSM.gsh (RGM.c_lay A_RGC) A_GTAB (shad (a + i))).
  { unfold GSM.gshw. rewrite !ESHg. set (CT := RGM.c_tab A_RGC) in *. set (CE := RGM.c_tabend A_RGC) in *.
    assert (ET8 : 8 * (CT / 8) = CT) by reflexivity.
    destruct HT as [HT|HT].
    - rewrite (proj2 (Z.leb_gt (shad CT) (shad (a + i)))); [reflexivity | unfold shad; lia].
    - rewrite (proj2 (Z.ltb_ge (shad (a + i)) (shad CE))); [rewrite andb_false_r; reflexivity|].
      unfold shad. apply Z.add_le_mono_r. apply Z.div_le_mono; lia. }
  rewrite EW in CELL. clear EW.
  assert (ESH : RGM.shad (RGM.c_lay A_RGC) beg = shad beg) by apply ESHg.
  assert (EWL : GSM.wr_lo (RGM.c_lay A_RGC) d = shad beg + sz / 8) by (unfold GSM.wr_lo; fold beg sz; rewrite ESH; reflexivity).
  assert (EWH : GSM.wr_hi (RGM.c_lay A_RGC) d = shad beg + swr / 8) by (unfold GSM.wr_hi; fold beg swr; rewrite ESH; reflexivity).
  destruct (Z_lt_ge_dec (shad (a + i)) (shad beg + sz / 8)) as [LT|GE].
  - (* [comment removed for export] *)
    rewrite (GSM.gsh_obj (RGM.c_lay A_RGC) A_GTAB _ d (shad (a + i)) A_GTAB_sorted Hin) in CELL
      by (rewrite ESH, EWL; split; [unfold shad; lia | exact LT]).
    exists (Z_to_bv 8 0). split; [|left; reflexivity].
    split; [unfold shad, SHB; lia|]. split; [unfold shad, SHB, SEGTOP_A in *; cbn [length]; lia|].
    intros j Hj. cbn [length] in Hj. assert (j = 0%nat) by lia. subst j. cbn [nth_error Z.of_nat]. rewrite Z.add_0_r. unfold mrd, wa. rewrite CELL. reflexivity.
  - (* [comment removed for export] *)
    assert (EQ : shad (a + i) = shad beg + sz / 8) by (unfold shad in *; lia).
    assert (NZ : sz mod 8 <> 0) by (unfold shad in *; lia).
    rewrite EQ, <- EWL in CELL.
    rewrite (GSM.gsh_partial (RGM.c_lay A_RGC) A_GTAB _ d A_GTAB_sorted Hin NZ ltac:(rewrite EWL, EWH; lia)) in CELL.
    fold sz in CELL. exists (Z_to_bv 8 (sz mod 8)). split.
    + rewrite EQ, <- EWL. split; [rewrite EWL; unfold shad, SHB; lia|]. split; [rewrite EWL; unfold shad, SHB, SEGTOP_A in *; cbn [length]; lia|].
      intros j Hj. cbn [length] in Hj. assert (j = 0%nat) by lia. subst j. cbn [nth_error Z.of_nat]. rewrite Z.add_0_r. unfold mrd, wa. rewrite CELL. reflexivity.
    + right. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite (Z.mod_small (sz mod 8) 256) by lia.
      split; [lia|]. unfold shad in *. lia.
Qed.

(* [comment removed for export] *)
Theorem gsh_byte : forall (m : mem) (d : RGM.desc) (g : Z), gsh_rep m -> In d A_GTAB ->
  RGM.d_beg d <= g -> g < RGM.d_beg d + RGM.d_size d -> g mod 8 = 0 -> RGM.d_beg d + RGM.d_size d <= SEGTOP_A ->
  (RGM.d_beg d + RGM.d_size d <= RGM.c_tab A_RGC \/ RGM.c_tabend A_RGC <= RGM.d_beg d) ->
  ro_cells asegs m (g / 8 + 2147450880)
    [C1 (Z_to_bv 8 (if RGM.d_beg d + RGM.d_size d - g <? 8 then RGM.d_beg d + RGM.d_size d - g else 0))].
Proof.
  intros m d g GS Hin H1 H2 G8 H3 HT.
  pose proof (GSM.sorted_in _ _ _ A_GTAB_sorted Hin) as (S1 & S2 & S3 & _). pose proof (gsh_sorted_al _ _ _ A_GTAB_sorted Hin) as S8.
  change (RGM.l_ilo A_RGL) with 0x10000 in S1.
  set (beg := RGM.d_beg d) in *. set (sz := RGM.d_size d) in *. set (swr := RGM.d_swr d) in *.
  pose proof (Z.div_mod g 8 ltac:(lia)) as DA. rewrite G8 in DA.
  pose proof (Z.div_mod beg 8 ltac:(lia)) as DB. rewrite S8 in DB.
  pose proof (Z.div_mod sz 8 ltac:(lia)) as DS. pose proof (Z.mod_pos_bound sz 8 ltac:(lia)) as RS.
  pose proof (Z.div_mod swr 8 ltac:(lia)) as DW. rewrite S2 in DW.
  assert (ESHg : forall x, RGM.shad (RGM.c_lay A_RGC) x = shad x) by (intros x; unfold RGM.shad, shad; change (RGM.l_shb (RGM.c_lay A_RGC)) with SHB; lia).
  assert (ES8 : 8 * (SEGTOP_A / 8) = SEGTOP_A) by reflexivity.
  change (g / 8 + 2147450880) with (shad g).
  assert (HX : shad 0x10000 <= shad g < shad SEGTOP_A).
  { unfold shad. split; [apply Z.add_le_mono_r; apply Z.div_le_mono; lia | lia]. }
  pose proof (GS (shad g) HX) as CELL.
  assert (EW : GSM.gshw A_RGC A_GTAB (shad g) = GSM.gsh (RGM.c_lay A_RGC) A_GTAB (shad g)).
  { unfold GSM.gshw. rewrite !ESHg. set (CT := RGM.c_tab A_RGC) in *. set (CE := RGM.c_tabend A_RGC) in *.
    assert (ET8 : 8 * (CT / 8) = CT) by reflexivity.
    destruct HT as [HT|HT].
    - rewrite (proj2 (Z.leb_gt (shad CT) (shad g))); [reflexivity | unfold shad; lia].
    - rewrite (proj2 (Z.ltb_ge (shad g) (shad CE))); [rewrite andb_false_r; reflexivity|].
      unfold shad. apply Z.add_le_mono_r. apply Z.div_le_mono; lia. }
  rewrite EW in CELL. clear EW.
  assert (ESH : RGM.shad (RGM.c_lay A_RGC) beg = shad beg) by apply ESHg.
  assert (EWL : GSM.wr_lo (RGM.c_lay A_RGC) d = shad beg + sz / 8) by (unfold GSM.wr_lo; fold beg sz; rewrite ESH; reflexivity).
  assert (EWH : GSM.wr_hi (RGM.c_lay A_RGC) d = shad beg + swr / 8) by (unfold GSM.wr_hi; fold beg swr; rewrite ESH; reflexivity).
  assert (CELLS : forall v, m (Z_to_bv 64 (shad g)) = Some (Z_to_bv 8 v) -> ro_cells asegs m (shad g) [C1 (Z_to_bv 8 v)]).
  { intros v CV. unfold ro_cells, cells_at. cbn [cells_wf cells_bytes cbytes]. rewrite app_nil_r. split; [split; [reflexivity| exact I]|].
    split; [unfold shad, SHB; lia|]. split; [unfold shad, SHB, SEGTOP_A in *; cbn [length]; lia|].
    intros j Hj. cbn [length] in Hj. assert (j = 0%nat) by lia. subst j. cbn [nth_error Z.of_nat]. rewrite Z.add_0_r. unfold mrd, wa. rewrite CV. reflexivity. }
  destruct (Z_lt_ge_dec (shad g) (shad beg + sz / 8)) as [LT|GE].
  - rewrite (GSM.gsh_obj (RGM.c_lay A_RGC) A_GTAB _ d (shad g) A_GTAB_sorted Hin) in CELL
      by (rewrite ESH, EWL; split; [unfold shad; lia | exact LT]).
    replace (beg + sz - g <? 8) with false by (symmetry; apply Z.ltb_ge; unfold shad in *; lia).
    exact (CELLS 0 CELL).
  - assert (EQ : shad g = shad beg + sz / 8) by (unfold shad in *; lia).
    assert (NZ : sz mod 8 <> 0) by (unfold shad in *; lia).
    rewrite EQ, <- EWL in CELL.
    rewrite (GSM.gsh_partial (RGM.c_lay A_RGC) A_GTAB _ d A_GTAB_sorted Hin NZ ltac:(rewrite EWL, EWH; lia)) in CELL.
    fold sz in CELL. rewrite EWL, <- EQ in CELL.
    replace (beg + sz - g <? 8) with true by (symmetry; apply Z.ltb_lt; unfold shad in *; lia).
    replace (beg + sz - g) with (sz mod 8) by (unfold shad in *; lia).
    exact (CELLS _ CELL).
Qed.

(* [comment removed for export] *)
Definition A_GOBJ (b s : Z) : Prop :=
  exists d, In d A_GTAB /\ RGM.d_beg d = b /\ RGM.d_size d = s /\ b + s <= SEGTOP_A /\ (b + s <= RGM.c_tab A_RGC \/ RGM.c_tabend A_RGC <= b).

Theorem rta_acc_global : RT_iface_pem.acc_global_fact RTA A_GOBJ.
Proof.
  intros Σ m b s a n HA (d & Hin & <- & <- & H3 & HT) H1 H2.
  destruct (ART_shadow Σ m HA) as (_ & _ & _ & _ & _ & GS).
  exact (gsh_acc m d a n GS Hin H1 H2 H3 HT).
Qed.

Theorem rta_gsh_byte : RT_iface_pem.gsh_byte_fact RTA A_GOBJ.
Proof.
  intros Σ m b s g HA (d & Hin & <- & <- & H3 & HT) H1 H2 G8.
  destruct (ART_shadow Σ m HA) as (_ & _ & _ & _ & _ & GS).
  exact (gsh_byte m d g GS Hin H1 H2 G8 H3 HT).
Qed.
