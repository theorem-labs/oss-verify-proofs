(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Canon Stdio.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_iface D_defs FX_Layout FX_Exit FX_Stdio_iface I_iodefs X_xdefs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import X_gdefs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import HandoffKit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import HandoffImage HandoffCells.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition out_cells (ch : acs) : list cell :=
  file_cells (hs_word ch RSTDOUT 4) 0 0 0 F_STDOUT_WRITE RSTDOUT_BUF 1024 1 (hs_word ch (RSTDOUT + 136) 4) 10
    (hs_blob ch (RSTDOUT + 152) 80).
Definition hs_out_ok (ch : acs) : bool :=
  (hs_rw_cells ch RSTDOUT (out_cells ch) && Z.eqb (Z.land (bv_unsigned (hs_word ch RSTDOUT 4)) 72) 0
   && seg_rw_ok asegs RSTDOUT_BUF 1024)%bool.

(* [comment removed for export] *)
Definition err_wend (ch : acs) : Z := bv_unsigned (hs_word ch (RSTDERR + 32) 8).
Definition err_e (ch : acs) : Z := bv_unsigned (hs_word ch (RSTDERR + 40) 8).
Definition err_cells (ch : acs) : list cell :=
  file_cells (hs_word ch RSTDERR 4) (err_wend ch) (err_e ch) (err_e ch) F_STDIO_WRITE 0xbc45f8 0 2
    (hs_word ch (RSTDERR + 136) 4) 0xffffffff (hs_blob ch (RSTDERR + 152) 80).
Definition hs_err_ok (ch : acs) : bool :=
  (hs_rw_cells ch RSTDERR (err_cells ch) && Z.eqb (Z.land (bv_unsigned (hs_word ch RSTDERR 4)) 40) 0
   && (Z.eqb (err_wend ch) 0 || (Z.eqb (err_wend ch) 0xbc45f8 && Z.eqb (err_e ch) 0xbc45f8)) && Z.ltb (err_e ch) (2 ^ 63))%bool.

Section Stdio.
Variables (A : atable) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (ISP : Z) (FS0 : Fs.Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok asegs A LIMIT SINV argH ISP FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.

#[local] Notation m := (mH FULL model A').
#[local] Notation RWC := (hi_rw_cells A LIMIT SINV argH ISP FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA').

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition x_tidE (ch : acs) : expr := match kw_find (kn ch) (ELit 0) 0xba3e48 4 with Some v => v | None => ELit 0 end.
Definition hs_tid_ok (ch : acs) : bool :=
  (match kw_find (kn ch) (ELit 0) 0xba3e48 4 with Some _ => true | None => false end
   && fact_ok (kn ch) (KRange (x_tidE ch) 1 (2 ^ 31 - 1)) && seg_rw_ok asegs 0xba3e48 4)%bool.
(* [comment removed for export] *)
Definition x_atexit (ch : acs) : list cell := ax_cells false (Z_to_bv 8 0) (hs_blob ch 0xbc3f41 3) (hs_blob ch 0xbc3f4c 4).
Definition x_libc (ch : acs) : list cell :=
  [C1 (hs_byte ch 0xbc4180); C1 (hs_byte ch 0xbc4181); C1 (hs_byte ch 0xbc4182); C1 (Z_to_bv 8 0); C4 (hs_word ch 0xbc4184 4)].
Definition x_stdin (ch : acs) : list cell :=
  [CB 8 (hs_blob ch 0x5aa858 8); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 (hs_blob ch 0x5aa870 16); C8 (Z_to_bv 64 0);
   CB 8 (hs_blob ch 0x5aa888 8); C8 (Z_to_bv 64 0); CB 76 (hs_blob ch 0x5aa898 76); C4 (Z_to_bv 64 0xffffffff);
   CB 88 (hs_blob ch 0x5aa8e8 88)].
Definition hs_xenv_ok (ch : acs) : bool :=
  (hs_tid_ok ch
   && hs_rw_cells ch 0xbc3f40 (x_atexit ch)
   && hs_rw_cells ch 0xbc4060 (ax_acells false)
   && hs_rw_cells ch AX_INCB [C1 (Z_to_bv 8 0)]              (* [comment removed for export] *)
   && hs_rw_cells ch 0xbc4160 [C4 (Z_to_bv 64 0)]
   && hs_rw_cells ch 0xbc4180 (x_libc ch)
   && hs_rw_cells ch 0xbc45e8 [C8 (Z_to_bv 64 0)]
   && hs_rw_cells ch 0x5aa850 [C8 (Z_to_bv 64 0x5aa768)]
   && hs_rw_cells ch 0x5aaa30 [C8 (Z_to_bv 64 0x5aa948)]
   && hs_rw_cells ch 0x5aa858 (x_stdin ch) && hs_rw_cells ch 0x5aa940 [C8 (Z_to_bv 64 0x5aa858)]
   && kimg_cover (kn ch) GT_LO GT_HI (S (length (kn ch)))   (* [comment removed for export] *)
   && negb (Z.eqb (bv_unsigned (hs_word ch 0x669480 8)) 0) && hs_rw_cells ch 0x669480 [C8 (hs_word ch 0x669480 8)]
   && hs_rw_cells ch 0x6694d0 [C1 (Z_to_bv 8 0)]
   && seg_rw_ok asegs ODR_LO (ODR_HI - ODR_LO)             (* [comment removed for export] *)
   && hs_rw_cells ch 0xb9f1e0 [C1 (Z_to_bv 8 0)])%bool.    (* [comment removed for export] *)

Section Xenv.
Variables (A : atable) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (ISP : Z) (FS0 : Fs.Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok asegs A LIMIT SINV argH ISP FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.

Hypothesis Hsegtop : img_hi A = SEGTOP_A.
Hypothesis Hseglo : img_lo A = 0x10000.

#[local] Notation m := (mH FULL model A').
#[local] Notation RWC := (hi_rw_cells A LIMIT SINV argH ISP FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA').
#[local] Notation ROC := (hi_ro_cells A LIMIT SINV argH ISP FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA').

(* [comment removed for export] *)
Lemma hi_gtab : kimg_cover (kn ch) GT_LO GT_HI (S (length (kn ch))) = true -> gtab_at m.
Proof.
  intros H. apply gtab_at_of_overlay_none. intros x Hx.
  destruct (kimg_cover_sound _ _ _ _ H x Hx) as (lo & h & Hk & Hr).
  pose proof (hk_kimg asegs A LIMIT SINV argH ISP FS0 E ch R FULL model HC lo h Hk x Hr) as HN.
  assert (Hin : APS.in_hull A (bv_unsigned (wa x)) = true).
  { rewrite wa_unsigned by (unfold GT_LO, GT_HI in Hx; lia). unfold APS.in_hull. rewrite Hseglo, Hsegtop. unfold GT_LO, GT_HI, SEGTOP_A in *.
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  destruct (hk_hull asegs A LIMIT SINV argH ISP FS0 HULL_ok argH_high E ch R FULL model HC A' HA' (wa x) Hin) as [E1 E2].
  rewrite E1, <- E2. exact HN.
Qed.

Lemma clx_u64_lit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite u_lit64. unfold two64. apply Z.mod_small. exact Hz. Qed.

Lemma hi_tid : hs_tid_ok ch = true -> exists tid : Z, 1 <= tid < 2 ^ 31 /\ rw_cells asegs m 0xba3e48 [C4 (Z_to_bv 64 tid)].
Proof.
  intros H. unfold hs_tid_ok in H. apply andb_prop in H as [H Hs]. apply andb_prop in H as [Hf Hr].
  unfold x_tidE in Hr. destruct (kw_find (kn ch) (ELit 0) 0xba3e48 4) as [v|] eqn:Hk; [|discriminate].
  apply kw_find_in in Hk.
  pose proof (APS.fact_ok_sound asegs E (APS.Mr A argH E ch model FULL) (kn ch) _ (APS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) Hr) as Kr.
  cbn [kentry_ok] in Kr.
  exists (bv_unsigned (edenot E v)). split; [lia|].
  pose proof (hk_kword asegs A LIMIT SINV argH ISP FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ 4 v Hk) as X.
  unfold estart in X. cbn [a_base a_off edenot] in X. rewrite clx_u64_lit in X by lia. rewrite !Z.add_0_l in X.
  split; [split; [repeat split|]| exact (proj1 (seg_rw_ok_sound asegs _ _ Hs m))].
  rewrite Z_to_bv_bv_unsigned. change (cells_bytes [C4 (edenot E v)]) with (le4 (edenot E v) ++ []). rewrite app_nil_r.
  exact (X ltac:(lia)).
Qed.

Theorem hi_xenv : hs_xenv_ok ch = true -> XENVA false m.
Proof.
  intros H. unfold hs_xenv_ok in H.
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
  apply andb_prop in H as [H H5i].   (* [comment removed for export] *)
  apply andb_prop in H as [H H5].
  apply andb_prop in H as [H H4].
  rename H into H1.
  unfold XENVA.
  split; [exact (hi_tid H1)|].
  split; [exists (Z_to_bv 8 0), (hs_blob ch 0xbc3f41 3), (hs_blob ch 0xbc3f4c 4); exact (conj (RWC _ _ H4) (RWC _ _ H5))|].
  split; [exact (RWC _ _ H5i)|].
  split; [exact (RWC _ _ H6)|].
  split; [exists (hs_byte ch 0xbc4180), (hs_byte ch 0xbc4181), (hs_byte ch 0xbc4182), (hs_word ch 0xbc4184 4); exact (RWC _ _ H7)|].
  split; [exact (RWC _ _ H8)|]. split; [exact (RWC _ _ H9)|]. split; [exact (RWC _ _ H10)|].
  split; [unfold stdin_file; exists (hs_blob ch 0x5aa858 8), (hs_blob ch 0x5aa870 16), (hs_blob ch 0x5aa888 8), (hs_blob ch 0x5aa898 76),
                             (hs_blob ch 0x5aa8e8 88); exact (RWC _ _ H11)|].
  split; [exact (RWC _ _ H12)|].
  split; [exact (hi_gtab H13)|].
  split; [exists (hs_word ch 0x669480 8); split; [apply negb_true_iff in H14; apply Z.eqb_neq in H14; exact H14| exact (RWC _ _ H15)]|].
  split; [exact (RWC _ _ H16)|].
  split; [|exact (RWC _ _ H18)].
  pose proof (proj2 (seg_rw_ok_sound asegs ODR_LO (ODR_HI - ODR_LO) H17 m)) as S. replace (ODR_LO + (ODR_HI - ODR_LO)) with ODR_HI in S by lia. exact S.
Qed.

End Xenv.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition hs_clx_ok (ch : acs) : bool := (hs_out_ok ch && hs_err_ok ch && hs_xenv_ok ch)%bool.

Section Clx.
Variables (A : atable) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (ISP : Z) (FS0 : Fs.Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok asegs A LIMIT SINV argH ISP FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.
Hypothesis Hsegtop : img_hi A = SEGTOP_A.
Hypothesis Hseglo : img_lo A = 0x10000.

#[local] Notation m := (mH FULL model A').

(* [comment removed for export] *)
Theorem hi_clx : forall LIB : mem -> Prop, LIB m -> hs_clx_ok ch = true ->
  CLX OUT_repA ERR_repA (XENVA false) LIB stdout_init m.
Proof.
  intros LIB HL H. unfold hs_clx_ok in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  destruct (hi_clx_statics m) as (G & Er & Ss & Tr).
  unfold CLX.
  split; [exact (hi_out A LIMIT SINV argH ISP FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' H1)|].
  split; [exact (hi_err A LIMIT SINV argH ISP FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' H2)|].
  split; [exact (hi_xenv A LIMIT SINV argH ISP FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' Hsegtop Hseglo H3)|].
  split; [exact HL|]. exact (conj G (conj Er (conj Ss Tr))).
Qed.

End Clx.
