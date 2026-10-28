(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim Canon Stdio.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_iface D_defs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import FX_Layout FX_Exit FX_Stdio_iface I_iodefs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import X_aexdefs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import X_xdefs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_auxv.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import HandoffKit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import HandoffImage.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Local Instance hc_fx : PropExec.FPState := PropExec.fx0.

Fixpoint cells_wfb (cs : list cell) : bool :=
  match cs with
  | [] => true
  | CB n bs :: r => (Nat.eqb (length bs) n && cells_wfb r)%bool
  | _ :: r => cells_wfb r
  end.

Lemma cells_wfb_sound : forall cs, cells_wfb cs = true -> cells_wf cs.
Proof.
  induction cs as [|c r IH]; intros H; [exact I|].
  destruct c; cbn [cells_wfb cells_wf cell_wf] in *;
    try (split; [exact I| exact (IH H)]).
  apply andb_prop in H as [H1 H2]. split; [apply Nat.eqb_eq; exact H1| exact (IH H2)].
Qed.

Fixpoint blist_eqb (xs ys : list byte) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => (bv_eqb x y && blist_eqb xs' ys')%bool
  | _, _ => false
  end.

Lemma blist_eqb_eq : forall xs ys, blist_eqb xs ys = true -> xs = ys.
Proof.
  induction xs as [|x xs IH]; intros [|y ys] H; cbn [blist_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply bv_eqb_eq in H1. subst y. rewrite (IH ys H2). reflexivity.
Qed.

Definition hs_bytes (ch : acs) (a n : Z) : option (list byte) :=
  match AP.hs_table asegs (klit_cut a (a + n) (kn ch)) a n with Some zs => Some (map (Z_to_bv 8) zs) | None => None end.

Definition hs_cells (ch : acs) (a : Z) (cs : list cell) : bool :=
  (cells_wfb cs && Z.leb 0 a && Z.leb (a + Z.of_nat (cells_size cs)) (2 ^ 47)
   && match hs_bytes ch a (Z.of_nat (cells_size cs)) with
      | Some bs => blist_eqb (cells_bytes cs) bs
      | None => false
      end)%bool.

Definition hs_rw_cells (ch : acs) (a : Z) (cs : list cell) : bool :=
  (hs_cells ch a cs && seg_rw_ok asegs a (Z.of_nat (cells_size cs)))%bool.

Definition dec_le (bs : list byte) : Z := fold_right (fun b acc => bv_unsigned b + 256 * acc) 0 bs.
Definition hs_word (ch : acs) (a : Z) (n : nat) : word :=
  match hs_bytes ch a (Z.of_nat n) with Some bs => Z_to_bv 64 (dec_le bs) | None => Z_to_bv 64 0 end.
Definition hs_blob (ch : acs) (a : Z) (n : nat) : list byte :=
  match hs_bytes ch a (Z.of_nat n) with Some bs => bs | None => [] end.
Definition hs_byte (ch : acs) (a : Z) : byte := nth 0 (hs_blob ch a 1) (Z_to_bv 8 0).

Section Cells.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok asegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.

#[local] Notation m := (mH FULL model A').

Lemma hi_ro_cells : forall a cs, hs_cells ch a cs = true -> ro_cells asegs m a cs.
Proof.
  intros a cs H. unfold hs_cells in H.
  apply andb_prop in H as [H Hb]. apply andb_prop in H as [H Hhi]. apply andb_prop in H as [Hwf Hlo].
  apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
  unfold hs_bytes in Hb. destruct (AP.hs_table asegs (klit_cut a (a + Z.of_nat (cells_size cs)) (kn ch)) a (Z.of_nat (cells_size cs))) as [zs|] eqn:Ht; [|discriminate].
  apply blist_eqb_eq in Hb.
  pose proof (hi_lit_cut asegs A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA'
                _ _ a (Z.of_nat (cells_size cs)) zs Ht Hlo ltac:(lia) Hhi) as Hl.
  unfold ro_cells, cells_at. split; [exact (cells_wfb_sound cs Hwf)|]. rewrite Hb. exact Hl.
Qed.

Lemma hi_rw_cells : forall a cs, hs_rw_cells ch a cs = true -> rw_cells asegs m a cs.
Proof.
  intros a cs H. unfold hs_rw_cells in H. apply andb_prop in H as [H Hs].
  split; [exact (hi_ro_cells a cs H)|].
  exact (proj1 (seg_rw_ok_sound asegs a (Z.of_nat (cells_size cs)) Hs m)).
Qed.

End Cells.

Definition out_cells (ch : acs) : list cell :=
  file_cells (hs_word ch RSTDOUT 4) 0 0 0 F_STDOUT_WRITE RSTDOUT_BUF 1024 1 (hs_word ch (RSTDOUT + 136) 4) 10
    (hs_blob ch (RSTDOUT + 152) 80).
Definition hs_out_ok (ch : acs) : bool :=
  (hs_rw_cells ch RSTDOUT (out_cells ch) && Z.eqb (Z.land (bv_unsigned (hs_word ch RSTDOUT 4)) 72) 0
   && seg_rw_ok asegs RSTDOUT_BUF 1024)%bool.

Definition err_wend (ch : acs) : Z := bv_unsigned (hs_word ch (RSTDERR + 32) 8).
Definition err_e (ch : acs) : Z := bv_unsigned (hs_word ch (RSTDERR + 40) 8).
Definition err_cells (ch : acs) : list cell :=
  file_cells (hs_word ch RSTDERR 4) (err_wend ch) (err_e ch) (err_e ch) F_STDIO_WRITE 0x6c8680 0 2
    (hs_word ch (RSTDERR + 136) 4) 0xffffffff (hs_blob ch (RSTDERR + 152) 80).
Definition hs_err_ok (ch : acs) : bool :=
  (hs_rw_cells ch RSTDERR (err_cells ch) && Z.eqb (Z.land (bv_unsigned (hs_word ch RSTDERR 4)) 40) 0
   && (Z.eqb (err_wend ch) 0 || (Z.eqb (err_wend ch) 0x6c8680 && Z.eqb (err_e ch) 0x6c8680)) && Z.ltb (err_e ch) (2 ^ 63))%bool.

Section Stdio.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok asegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.

#[local] Notation m := (mH FULL model A').
#[local] Notation RWC := (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA').

Lemma hi_blob : forall a (n : nat), seg_rw_ok asegs a (Z.of_nat n) = true -> exists bs, rw_cells asegs m a [CB n bs].
Proof.
  intros a n H. destruct (seg_rw_ok_sound asegs a (Z.of_nat n) H m) as [W S].
  destruct (stk_bytes asegs m a n S) as (bs & Hl & Hb). exists bs.
  split; [split; [split; [exact Hl| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact Hb]|].
  cbn [cells_size csize]. rewrite Nat.add_0_r. exact W.
Qed.

Theorem hi_out : hs_out_ok ch = true -> OUT_repA stdout_init m.
Proof.
  intros H. unfold hs_out_ok in H. apply andb_prop in H as [H Hbuf]. apply andb_prop in H as [Hc Hfl].
  destruct (hi_blob RSTDOUT_BUF 1024 Hbuf) as [bs Hb].
  unfold OUT_repA, stdout_file.
  exists (hs_word ch RSTDOUT 4), (hs_word ch (RSTDOUT + 136) 4), (hs_blob ch (RSTDOUT + 152) 80), bs.
  cbn [so_active so_first so_lbf_nl so_buf stdout_init].
  split; [exact (RWC _ _ Hc)|]. split; [apply Z.eqb_eq; exact Hfl|]. split; [exact Hb|].
  split; [reflexivity|]. split; [unfold zlength; cbn; lia|]. intros _. reflexivity.
Qed.

Theorem hi_err : hs_err_ok ch = true -> ERR_repA m.
Proof.
  intros H. unfold hs_err_ok in H.
  apply andb_prop in H as [H He]. apply andb_prop in H as [H Hw]. apply andb_prop in H as [Hc Hfl].
  unfold ERR_repA, stderr_wfile0.
  exists (hs_word ch RSTDERR 4), (hs_word ch (RSTDERR + 136) 4), (err_e ch), (err_wend ch), (hs_blob ch (RSTDERR + 152) 80).
  split; [exact (RWC _ _ Hc)|]. split; [apply Z.eqb_eq; exact Hfl|].
  split.
  - apply orb_prop in Hw as [Hw|Hw]; [left; apply Z.eqb_eq; exact Hw|].
    apply andb_prop in Hw as [H1 H2]. right. split; apply Z.eqb_eq; assumption.
  - apply Z.ltb_lt in He. unfold err_e in *. pose proof (u64_range (hs_word ch (RSTDERR + 40) 8)). lia.
Qed.

End Stdio.

Definition x_tidE (ch : acs) : expr := match kw_find (kn ch) (ELit 0) 0x6a7dc0 4 with Some v => v | None => ELit 0 end.
Definition hs_tid_ok (ch : acs) : bool :=
  (match kw_find (kn ch) (ELit 0) 0x6a7dc0 4 with Some _ => true | None => false end
   && fact_ok (kn ch) (KRange (x_tidE ch) 1 (2 ^ 31 - 1)) && seg_rw_ok asegs 0x6a7dc0 4)%bool.

Definition x_aex (ch : acs) : list cell :=
  [C1 (Z_to_bv 8 0); CB 3 (hs_blob ch 0x6c7eb9 3); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); CB 4 (hs_blob ch 0x6c7ec4 4);
   C8 (Z_to_bv 64 0x6c7ed0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x14b448); C8 (hs_word ch 0x6c7ee0 8)].
Definition hs_aex_ok (ch : acs) : bool :=
  (hs_rw_cells ch 0x6c7eb8 (x_aex ch)
   && hs_rw_cells ch 0x6a6290 [C1 (Z_to_bv 8 0)]
   && hs_rw_cells ch 0x6a6294 [C1 (Z_to_bv 8 0)])%bool.
Definition x_libc (ch : acs) : list cell :=
  [C1 (hs_byte ch 0x6c80f8); C1 (hs_byte ch 0x6c80f9); C1 (hs_byte ch 0x6c80fa); C1 (Z_to_bv 8 0); C4 (hs_word ch 0x6c80fc 4)].
Definition x_stdin (ch : acs) : list cell :=
  [CB 8 (hs_blob ch 0x16ec18 8); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 (hs_blob ch 0x16ec30 16); C8 (Z_to_bv 64 0);
   CB 8 (hs_blob ch 0x16ec48 8); C8 (Z_to_bv 64 0); CB 76 (hs_blob ch 0x16ec58 76); C4 (Z_to_bv 64 0xffffffff);
   CB 88 (hs_blob ch 0x16eca8 88)].
Fixpoint hs_gds (ch : acs) (a : Z) (gs : list gdesc) : bool :=
  match gs with
  | [] => true
  | g :: gs' => (hs_cells ch a (gd_cells g) && hs_gds ch (a + 64) gs')%bool
  end.

Definition hs_xenv_ok (ch : acs) : bool :=
  (hs_tid_ok ch
   && hs_rw_cells ch 0x16e978 [C8 (Z_to_bv 64 0x1679d8); C8 (Z_to_bv 64 0x106ecc)]
   && hs_rw_cells ch 0x16e990 [C8 (Z_to_bv 64 0xe9ccc); C8 (Z_to_bv 64 0xe9dd8)]
   && hs_aex_ok ch
   && hs_rw_cells ch 0x6c7fd8 [C8 (Z_to_bv 64 0xa0bc8); C8 (hs_word ch 0x6c7fe0 8)]
   && hs_rw_cells ch 0x6c80d8 [C4 (Z_to_bv 64 0)]
   && hs_rw_cells ch 0x6c80f8 (x_libc ch)
   && hs_rw_cells ch 0x6c8670 [C8 (Z_to_bv 64 0)]
   && hs_rw_cells ch 0x16eb20 [C8 (Z_to_bv 64 0x16ea38)]
   && hs_rw_cells ch 0x16ec10 [C8 (Z_to_bv 64 0x16eb28)]
   && hs_rw_cells ch 0x16ec18 (x_stdin ch) && hs_rw_cells ch 0x16ed00 [C8 (Z_to_bv 64 0x16ec18)]
   && hs_gds ch 0x16ed30 asan_gds
   && negb (Z.eqb (bv_unsigned (hs_word ch 0x170580 8)) 0) && hs_rw_cells ch 0x170580 [C8 (hs_word ch 0x170580 8)]
   && hs_rw_cells ch 0x1705d0 [C1 (Z_to_bv 8 0)]
   && hs_rw_cells ch 0x6a6460 [C1 (hs_byte ch 0x6a6460)]
   && hs_rw_cells ch 0x6a6461 [C1 (hs_byte ch 0x6a6461)]
   && hs_rw_cells ch 0x6a6462 [C1 (hs_byte ch 0x6a6462)]
   && hs_rw_cells ch 0x6a6463 [C1 (hs_byte ch 0x6a6463)]
   && hs_rw_cells ch 0x6a6464 [C1 (hs_byte ch 0x6a6464)]
   && hs_rw_cells ch 0x6a6465 [C1 (hs_byte ch 0x6a6465)]
   && hs_rw_cells ch 0x6a6466 [C1 (hs_byte ch 0x6a6466)]
   && hs_rw_cells ch 0x6a6467 [C1 (hs_byte ch 0x6a6467)]
   && hs_rw_cells ch 0x6a6468 [C1 (hs_byte ch 0x6a6468)]
   && hs_rw_cells ch 0x6a6469 [C1 (hs_byte ch 0x6a6469)]
   && hs_rw_cells ch 0x6a646a [C1 (hs_byte ch 0x6a646a)])%bool.

Section Xenv.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok asegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.

#[local] Notation m := (mH FULL model A').
#[local] Notation RWC := (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA').
#[local] Notation ROC := (hi_ro_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA').

Lemma hi_gds : forall gs a, hs_gds ch a gs = true -> gds_at m a gs.
Proof.
  induction gs as [|g gs IH]; intros a H; [exact I|].
  cbn [hs_gds] in H. apply andb_prop in H as [H1 H2]. split; [exact (ROC _ _ H1)| exact (IH _ H2)].
Qed.

Lemma clx_u64_lit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite u_lit64. unfold two64. apply Z.mod_small. exact Hz. Qed.

Lemma hi_tid : hs_tid_ok ch = true -> exists tid : Z, 1 <= tid < 2 ^ 31 /\ rw_cells asegs m 0x6a7dc0 [C4 (Z_to_bv 64 tid)].
Proof.
  intros H. unfold hs_tid_ok in H. apply andb_prop in H as [H Hs]. apply andb_prop in H as [Hf Hr].
  unfold x_tidE in Hr. destruct (kw_find (kn ch) (ELit 0) 0x6a7dc0 4) as [v|] eqn:Hk; [|discriminate].
  apply kw_find_in in Hk.
  pose proof (APS.fact_ok_sound asegs E (APS.Mr A argH E ch model FULL) (kn ch) _ (APS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) Hr) as Kr.
  cbn [kentry_ok] in Kr.
  exists (bv_unsigned (edenot E v)). split; [lia|].
  pose proof (hk_kword asegs A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ 4 v Hk) as X.
  unfold estart in X. cbn [a_base a_off edenot] in X. rewrite clx_u64_lit in X by lia. rewrite !Z.add_0_l in X.
  split; [split; [repeat split|]| exact (proj1 (seg_rw_ok_sound asegs _ _ Hs m))].
  rewrite Z_to_bv_bv_unsigned. change (cells_bytes [C4 (edenot E v)]) with (le4 (edenot E v) ++ []). rewrite app_nil_r.
  exact (X ltac:(lia)).
Qed.

Theorem hi_xenv : hs_xenv_ok ch = true -> XENVA m.
Proof.
  intros H. unfold hs_xenv_ok in H.
  apply andb_prop in H as [H H27].
  apply andb_prop in H as [H H26].
  apply andb_prop in H as [H H25].
  apply andb_prop in H as [H H24].
  apply andb_prop in H as [H H23].
  apply andb_prop in H as [H H22].
  apply andb_prop in H as [H H21].
  apply andb_prop in H as [H H20].
  apply andb_prop in H as [H H19].
  apply andb_prop in H as [H H18].
  apply andb_prop in H as [H H17].
  apply andb_prop in H as [H H16].
  apply andb_prop in H as [H H15].
  apply andb_prop in H as [H H14].
  apply andb_prop in H as [H H13].
  apply andb_prop in H as [H H12].
  apply andb_prop in H as [H H11].
  apply andb_prop in H as [H H10].
  apply andb_prop in H as [H H9].
  apply andb_prop in H as [H H8].
  apply andb_prop in H as [H H7].
  apply andb_prop in H as [H H6].
  apply andb_prop in H as [H H5].
  apply andb_prop in H as [H H4].
  apply andb_prop in H as [H HX2]. apply andb_prop in H as [H HX1].
  rename H into H1.
  unfold XENVA. split; cycle 1.
  {
    left. unfold hs_aex_ok in H4. apply andb_prop in H4 as [H4 H4c]. apply andb_prop in H4 as [H4a H4b].
    split; [exists (hs_blob ch 0x6c7eb9 3), (hs_blob ch 0x6c7ec4 4), (hs_word ch 0x6c7ee0 8); exact (RWC _ _ H4a)|].
    split; [exists (hs_word ch 0x6c7fe0 8); exact (RWC _ _ H5)|].
    split; [exact (RWC _ _ H4b)| exact (RWC _ _ H4c)]. }

  split; [exact (hi_tid H1)|].
  split; [exact (RWC _ _ H6)|].
  split; [exists (hs_byte ch 0x6c80f8), (hs_byte ch 0x6c80f9), (hs_byte ch 0x6c80fa), (hs_word ch 0x6c80fc 4); exact (RWC _ _ H7)|].
  split; [exact (RWC _ _ H8)|]. split; [exact (RWC _ _ H9)|]. split; [exact (RWC _ _ H10)|].
  split; [unfold stdin_file; exists (hs_blob ch 0x16ec18 8), (hs_blob ch 0x16ec30 16), (hs_blob ch 0x16ec48 8), (hs_blob ch 0x16ec58 76),
                             (hs_blob ch 0x16eca8 88); exact (RWC _ _ H11)|].
  split; [exact (RWC _ _ H12)|].
  split; [exact (hi_gds _ _ H13)|].
  split; [exists (hs_word ch 0x170580 8); split; [apply negb_true_iff in H14; apply Z.eqb_neq in H14; exact H14| exact (RWC _ _ H15)]|].
  split; [exact (RWC _ _ H16)|].
  split; cycle 1. { split; [exact (RWC _ _ HX1)| exact (RWC _ _ HX2)]. }
  exists (hs_byte ch 0x6a6460), (hs_byte ch 0x6a6461), (hs_byte ch 0x6a6462), (hs_byte ch 0x6a6463), (hs_byte ch 0x6a6464), (hs_byte ch 0x6a6465), (hs_byte ch 0x6a6466), (hs_byte ch 0x6a6467), (hs_byte ch 0x6a6468), (hs_byte ch 0x6a6469), (hs_byte ch 0x6a646a).
  split; [exact (RWC _ _ H17)|].
  split; [exact (RWC _ _ H18)|].
  split; [exact (RWC _ _ H19)|].
  split; [exact (RWC _ _ H20)|].
  split; [exact (RWC _ _ H21)|].
  split; [exact (RWC _ _ H22)|].
  split; [exact (RWC _ _ H23)|].
  split; [exact (RWC _ _ H24)|].
  split; [exact (RWC _ _ H25)|].
  split; [exact (RWC _ _ H26)|].
  exact (RWC _ _ H27).
Qed.

End Xenv.

Definition hs_clx_ok (ch : acs) : bool := (hs_out_ok ch && hs_err_ok ch && hs_xenv_ok ch)%bool.

Section Clx.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok asegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.

#[local] Notation m := (mH FULL model A').

Theorem hi_clx : forall LIB : mem -> Prop, LIB m -> hs_clx_ok ch = true ->
  CLX OUT_repA ERR_repA XENVA LIB stdout_init m.
Proof.
  intros LIB HL H. unfold hs_clx_ok in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  destruct (hi_clx_statics m) as (G & Er & Ss & _).
  unfold CLX.
  split; [exact (hi_out A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' H1)|].
  split; [exact (hi_err A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' H2)|].
  split; [exact (hi_xenv A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' H3)|].
  split; [exact HL|]. exact (conj G (conj Er Ss)).
Qed.

End Clx.
