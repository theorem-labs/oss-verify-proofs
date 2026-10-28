(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim Canon Stdio.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_iface D_defs FX_Layout FX_Exit FX_Stdio_iface I_iodefs X_aexdefs X_xdefs D_auxv.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import HandoffKit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import HandoffImage.
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
  match AP.hs_table bsegs (klit_cut a (a + n) (kn ch)) a n with Some zs => Some (map (Z_to_bv 8) zs) | None => None end.

Definition hs_cells (ch : acs) (a : Z) (cs : list cell) : bool :=
  (cells_wfb cs && Z.leb 0 a && Z.leb (a + Z.of_nat (cells_size cs)) (2 ^ 47)
   && match hs_bytes ch a (Z.of_nat (cells_size cs)) with
      | Some bs => blist_eqb (cells_bytes cs) bs
      | None => false
      end)%bool.

Definition hs_rw_cells (ch : acs) (a : Z) (cs : list cell) : bool :=
  (hs_cells ch a cs && seg_rw_ok bsegs a (Z.of_nat (cells_size cs)))%bool.

Definition dec_le (bs : list byte) : Z := fold_right (fun b acc => bv_unsigned b + 256 * acc) 0 bs.
Definition hs_word (ch : acs) (a : Z) (n : nat) : word :=
  match hs_bytes ch a (Z.of_nat n) with Some bs => Z_to_bv 64 (dec_le bs) | None => Z_to_bv 64 0 end.
Definition hs_blob (ch : acs) (a : Z) (n : nat) : list byte :=
  match hs_bytes ch a (Z.of_nat n) with Some bs => bs | None => [] end.
Definition hs_byte (ch : acs) (a : Z) : byte := nth 0 (hs_blob ch a 1) (Z_to_bv 8 0).

Section Cells.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.

#[local] Notation m := (mH FULL model A').

Lemma hi_ro_cells : forall a cs, hs_cells ch a cs = true -> ro_cells bsegs m a cs.
Proof.
  intros a cs H. unfold hs_cells in H.
  apply andb_prop in H as [H Hb]. apply andb_prop in H as [H Hhi]. apply andb_prop in H as [Hwf Hlo].
  apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
  unfold hs_bytes in Hb. destruct (AP.hs_table bsegs (klit_cut a (a + Z.of_nat (cells_size cs)) (kn ch)) a (Z.of_nat (cells_size cs))) as [zs|] eqn:Ht; [|discriminate].
  apply blist_eqb_eq in Hb.
  pose proof (hi_lit_cut bsegs A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA'
                _ _ a (Z.of_nat (cells_size cs)) zs Ht Hlo ltac:(lia) Hhi) as Hl.
  unfold ro_cells, cells_at. split; [exact (cells_wfb_sound cs Hwf)|]. rewrite Hb. exact Hl.
Qed.

Lemma hi_rw_cells : forall a cs, hs_rw_cells ch a cs = true -> rw_cells bsegs m a cs.
Proof.
  intros a cs H. unfold hs_rw_cells in H. apply andb_prop in H as [H Hs].
  split; [exact (hi_ro_cells a cs H)|].
  exact (proj1 (seg_rw_ok_sound bsegs a (Z.of_nat (cells_size cs)) Hs m)).
Qed.

End Cells.

Definition out_cells (ch : acs) : list cell :=
  file_cells (hs_word ch RSTDOUT 4) 0 0 0 F_STDOUT_WRITE RSTDOUT_BUF 1024 1 (hs_word ch (RSTDOUT + 136) 4) 10
    (hs_blob ch (RSTDOUT + 152) 80).
Definition hs_out_ok (ch : acs) : bool :=
  (hs_rw_cells ch RSTDOUT (out_cells ch) && Z.eqb (Z.land (bv_unsigned (hs_word ch RSTDOUT 4)) 72) 0
   && seg_rw_ok bsegs RSTDOUT_BUF 1024)%bool.

Definition err_wend (ch : acs) : Z := bv_unsigned (hs_word ch (RSTDERR + 32) 8).
Definition err_e (ch : acs) : Z := bv_unsigned (hs_word ch (RSTDERR + 40) 8).
Definition err_cells (ch : acs) : list cell :=
  file_cells (hs_word ch RSTDERR 4) (err_wend ch) (err_e ch) (err_e ch) F_STDIO_WRITE 0x6cbb80 0 2
    (hs_word ch (RSTDERR + 136) 4) 0xffffffff (hs_blob ch (RSTDERR + 152) 80).
Definition hs_err_ok (ch : acs) : bool :=
  (hs_rw_cells ch RSTDERR (err_cells ch) && Z.eqb (Z.land (bv_unsigned (hs_word ch RSTDERR 4)) 40) 0
   && (Z.eqb (err_wend ch) 0 || (Z.eqb (err_wend ch) 0x6cbb80 && Z.eqb (err_e ch) 0x6cbb80)) && Z.ltb (err_e ch) (2 ^ 63))%bool.

Section Stdio.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.

#[local] Notation m := (mH FULL model A').
#[local] Notation RWC := (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA').

Lemma hi_blob : forall a (n : nat), seg_rw_ok bsegs a (Z.of_nat n) = true -> exists bs, rw_cells bsegs m a [CB n bs].
Proof.
  intros a n H. destruct (seg_rw_ok_sound bsegs a (Z.of_nat n) H m) as [W S].
  destruct (stk_bytes bsegs m a n S) as (bs & Hl & Hb). exists bs.
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

Definition x_tidE (ch : acs) : expr := match kw_find (kn ch) (ELit 0) 0x6ab2c0 4 with Some v => v | None => ELit 0 end.
Definition hs_tid_ok (ch : acs) : bool :=
  (match kw_find (kn ch) (ELit 0) 0x6ab2c0 4 with Some _ => true | None => false end
   && fact_ok (kn ch) (KRange (x_tidE ch) 1 (2 ^ 31 - 1)) && seg_rw_ok bsegs 0x6ab2c0 4)%bool.

Definition x_aex (ch : acs) : list cell :=
  [C1 (Z_to_bv 8 0); CB 3 (hs_blob ch 0x6cb3b9 3); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); CB 4 (hs_blob ch 0x6cb3c4 4);
   C8 (Z_to_bv 64 0x6cb3d0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x14f7a8); C8 (hs_word ch 0x6cb3e0 8)].
Definition hs_aex_ok (ch : acs) : bool :=
  (hs_rw_cells ch 0x6cb3b8 (x_aex ch)
   && hs_rw_cells ch 0x6a9790 [C1 (Z_to_bv 8 0)]
   && hs_rw_cells ch 0x6a9794 [C1 (Z_to_bv 8 0)])%bool.
Definition x_libc (ch : acs) : list cell :=
  [C1 (hs_byte ch 0x6cb5f8); C1 (hs_byte ch 0x6cb5f9); C1 (hs_byte ch 0x6cb5fa); C1 (Z_to_bv 8 0); C4 (hs_word ch 0x6cb5fc 4)].
Definition x_stdin (ch : acs) : list cell :=
  [CB 8 (hs_blob ch 0x172f70 8); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 (hs_blob ch 0x172f88 16); C8 (Z_to_bv 64 0);
   CB 8 (hs_blob ch 0x172fa0 8); C8 (Z_to_bv 64 0); CB 76 (hs_blob ch 0x172fb0 76); C4 (Z_to_bv 64 0xffffffff);
   CB 88 (hs_blob ch 0x173000 88)].
Fixpoint hs_gds (ch : acs) (a : Z) (gs : list gdesc) : bool :=
  match gs with
  | [] => true
  | g :: gs' => (hs_cells ch a (gd_cells g) && hs_gds ch (a + 64) gs')%bool
  end.

Definition hs_xenv_ok (ch : acs) : bool :=
  (hs_tid_ok ch
   && hs_rw_cells ch 0x172908 [C8 (Z_to_bv 64 0x10b67c)]
   && hs_rw_cells ch 0x172ce8 [C8 (Z_to_bv 64 0xee47c); C8 (Z_to_bv 64 0xee588)]
   && hs_aex_ok ch
   && hs_rw_cells ch 0x6cb4d8 [C8 (Z_to_bv 64 0x9dc08); C8 (hs_word ch 0x6cb4e0 8)]
   && hs_rw_cells ch 0x6cb5d8 [C4 (Z_to_bv 64 0)]
   && hs_rw_cells ch 0x6cb5f8 (x_libc ch)
   && hs_rw_cells ch 0x6cbb70 [C8 (Z_to_bv 64 0)]
   && hs_rw_cells ch 0x172e78 [C8 (Z_to_bv 64 0x172d90)]
   && hs_rw_cells ch 0x172f68 [C8 (Z_to_bv 64 0x172e80)]
   && hs_rw_cells ch 0x172f70 (x_stdin ch) && hs_rw_cells ch 0x173058 [C8 (Z_to_bv 64 0x172f70)]
   && hs_gds ch 0x173090 asan_gds
   && negb (Z.eqb (bv_unsigned (hs_word ch 0x173a80 8)) 0) && hs_rw_cells ch 0x173a80 [C8 (hs_word ch 0x173a80 8)]
   && hs_rw_cells ch 0x173ad0 [C1 (Z_to_bv 8 0)]
   && hs_rw_cells ch 0x6a9960 [C1 (hs_byte ch 0x6a9960)]
   && hs_rw_cells ch 0x6a9961 [C1 (hs_byte ch 0x6a9961)]
   && hs_rw_cells ch 0x6a9962 [C1 (hs_byte ch 0x6a9962)]
   && hs_rw_cells ch 0x6a9963 [C1 (hs_byte ch 0x6a9963)]
   && hs_rw_cells ch 0x6a9964 [C1 (hs_byte ch 0x6a9964)]
   && hs_rw_cells ch 0x6a9965 [C1 (hs_byte ch 0x6a9965)]
   && hs_rw_cells ch 0x6a9966 [C1 (hs_byte ch 0x6a9966)]
   && hs_rw_cells ch 0x6a9967 [C1 (hs_byte ch 0x6a9967)]
   && hs_rw_cells ch 0x6a9968 [C1 (hs_byte ch 0x6a9968)]
   && hs_rw_cells ch 0x6a9969 [C1 (hs_byte ch 0x6a9969)]
   && hs_rw_cells ch 0x6a996a [C1 (hs_byte ch 0x6a996a)])%bool.

Section Xenv.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
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

Lemma hi_tid : hs_tid_ok ch = true -> exists tid : Z, 1 <= tid < 2 ^ 31 /\ rw_cells bsegs m 0x6ab2c0 [C4 (Z_to_bv 64 tid)].
Proof.
  intros H. unfold hs_tid_ok in H. apply andb_prop in H as [H Hs]. apply andb_prop in H as [Hf Hr].
  unfold x_tidE in Hr. destruct (kw_find (kn ch) (ELit 0) 0x6ab2c0 4) as [v|] eqn:Hk; [|discriminate].
  apply kw_find_in in Hk.
  pose proof (APS.fact_ok_sound bsegs E (APS.Mr A argH E ch model FULL) (kn ch) _ (APS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) Hr) as Kr.
  cbn [kentry_ok] in Kr.
  exists (bv_unsigned (edenot E v)). split; [lia|].
  pose proof (hk_kword bsegs A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ 4 v Hk) as X.
  unfold estart in X. cbn [a_base a_off edenot] in X. rewrite clx_u64_lit in X by lia. rewrite !Z.add_0_l in X.
  split; [split; [repeat split|]| exact (proj1 (seg_rw_ok_sound bsegs _ _ Hs m))].
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
    split; [exists (hs_blob ch 0x6cb3b9 3), (hs_blob ch 0x6cb3c4 4), (hs_word ch 0x6cb3e0 8); exact (RWC _ _ H4a)|].
    split; [exists (hs_word ch 0x6cb4e0 8); exact (RWC _ _ H5)|].
    split; [exact (RWC _ _ H4b)| exact (RWC _ _ H4c)]. }

  split; [exact (hi_tid H1)|].
  split; [exact (RWC _ _ H6)|].
  split; [exists (hs_byte ch 0x6cb5f8), (hs_byte ch 0x6cb5f9), (hs_byte ch 0x6cb5fa), (hs_word ch 0x6cb5fc 4); exact (RWC _ _ H7)|].
  split; [exact (RWC _ _ H8)|]. split; [exact (RWC _ _ H9)|]. split; [exact (RWC _ _ H10)|].
  split; [unfold stdin_file; exists (hs_blob ch 0x172f70 8), (hs_blob ch 0x172f88 16), (hs_blob ch 0x172fa0 8), (hs_blob ch 0x172fb0 76),
                             (hs_blob ch 0x173000 88); exact (RWC _ _ H11)|].
  split; [exact (RWC _ _ H12)|].
  split; [exact (hi_gds _ _ H13)|].
  split; [exists (hs_word ch 0x173a80 8); split; [apply negb_true_iff in H14; apply Z.eqb_neq in H14; exact H14| exact (RWC _ _ H15)]|].
  split; [exact (RWC _ _ H16)|].
  split; cycle 1. { split; [exact (RWC _ _ HX1)| exact (RWC _ _ HX2)]. }
  exists (hs_byte ch 0x6a9960), (hs_byte ch 0x6a9961), (hs_byte ch 0x6a9962), (hs_byte ch 0x6a9963), (hs_byte ch 0x6a9964), (hs_byte ch 0x6a9965), (hs_byte ch 0x6a9966), (hs_byte ch 0x6a9967), (hs_byte ch 0x6a9968), (hs_byte ch 0x6a9969), (hs_byte ch 0x6a996a).
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
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
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
