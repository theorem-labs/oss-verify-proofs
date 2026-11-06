(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpRepA AWKit AWAuto AWAuto2 FakeKit HObjK HObjF H_scanner_get_token H_vfm_A.
Import ListNotations.
Open Scope Z_scope.

Section G.
Context {HC : HasCeiling}.
Hypothesis IC : icpt_contracts.
Variable FI : fs_if.
Hypothesis STACK_MALLOC_1 : stack_malloc_stmt FI 1.

#[using="Type"] Lemma vinv_fmt_acc : forall q lo S MB A len cap cur0 bs st Wx FMT flen ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 q' cur G cs m a,
  vinv FI q lo S MB A len cap cur0 bs st Wx FMT flen ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 q' cur G cs m ->
  FMT <= a < FMT + flen -> acc m a.
Proof.
  intros until a. intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SHFMT & _) Ha. exact (proj1 SHFMT a Ha).
Qed.
#[using="Type"] Lemma vinv_mi : forall q lo S MB A len cap cur0 bs st Wx FMT flen ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 q' cur G cs m,
  vinv FI q lo S MB A len cap cur0 bs st Wx FMT flen ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 q' cur G cs m -> mem_inv asegs m.
Proof. intros until m. intros (_ & _ & _ & _ & _ & _ & MI & _). exact MI. Qed.
#[using="Type"] Lemma fmt_rdA : forall m a fb (i : nat) c, bytes_at asegs m a fb -> nth_error fb i = Some (Z_to_bv 8 c) ->
  ov_read_bytes asegs m (wa (a + Z.of_nat i)) 1 = Some [Z_to_bv 8 c].
Proof.
  intros m a fb i c B N. pose proof (bytes_at_bound _ _ _ _ B) as BB.
  assert (Hi : (i < length fb)%nat) by (apply nth_error_Some; rewrite N; discriminate).
  rewrite (bytes_at_read asegs m a fb (Z.of_nat i) 1 B) by lia.
  f_equal. rewrite Nat2Z.id. change (Z.to_nat 1) with 1%nat.
  rewrite (firstn_skipn_nth _ _ _ _ N) || (clear - N Hi; revert fb N Hi; induction i; intros [|x fb] N Hi; cbn in *; try lia; [inversion N; reflexivity| apply IHi; [exact N| lia]]).
Qed.

#[using="Type"] Lemma vpostA_mono : forall q lo S MB A len cap cur0 bs st Wx ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 (X1 X2 : mem -> Z -> Z -> Prop) ms,
  vpostA FI q lo S MB A len cap cur0 bs st Wx ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 X1 ms ->
  (forall m r c, X1 m r c -> X2 m r c) ->
  vpostA FI q lo S MB A len cap cur0 bs st Wx ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 X2 ms.
Proof.
  intros until ms. intros (r & c & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & st' & E & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & HX) IMP.
  exists r, c, t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', st'. repeat (split; [assumption|]). apply IMP. exact HX.
Qed.

#[using="Type"] Lemma out_rframe_c : forall q lo S MB A len cap cur0 bs st Wx m0 P (pa pb : word),
  vf_okA FI q lo S MB A len cap cur0 bs st Wx -> RFAKE FI st m0 -> In (P, P + 16) Wx ->
  rframeA FI q lo S st (fun mm => rw_cells asegs mm P [C8 pa; C8 pb]).
Proof.
  intros q lo S MB A len cap cur0 bs st Wx m0 P pa pb VOK RF0 PIN m m' H MU WM.
  eapply rw_cells_transport; [exact H| exact MU| exact WM|].
  pose proof VOK as VOK'. destruct VOK' as (CLO & LO & _ & QHI & MBLO & MBS & SHI & _ & _ & PLB & _ & _ & _ & _ & _ & _ & _ & _ & _ & WXL & _ & WXP).
  rewrite Forall_forall in WXL. destruct (WXL _ PIN) as [LE [LB|ER]]; cbn [fst snd] in *; [| exfalso; clear - ER; lia]. replace (P + 16 - P) with 16 in LB by lia.
  destruct (new_frame_facts FI st 1 m0 (vF FI st) (vSF FI st) (vFL FI st) RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & FLO & FHI & FAL & FLLO & FLHI & APART).
  cbn [FB_of SB_of] in FHI, APART.
  pose proof (fsb_ok FI) as (FSB1 & FSB2 & _ & FSB4 & _).
  assert (SHF1 : sh (FSB FI) <= vSF FI st /\ vSF FI st + 16 <= sh (FSB FI) + A0_FS_SHSIZE).
  { unfold vSF, sh, SHADOW_OFF. clear - FLO FHI FSB4. Z.div_mod_to_equations. lia. }
  pose proof (lb_apart_frame _ _ _ (vF FI st) 128 _ _ LB APART) as P1.
  pose proof (lb_apart_shadow FI st m0 _ _ (vSF FI st) 16 RF0 LB ltac:(lia) ltac:(lia)) as P2.
  pose proof (lb_apart_flag FI st m0 _ _ (vFL FI st) RF0 LB FLLO FLHI) as P3.
  pose proof (In_disjoint Wx P (P + 16) _ _ PIN WXP) as P4.
  destruct (lb_in_fs FI st m0 RF0 _ _ LB) as [Q1 Q2].
  unfold vWE. cbn [disjoint_from]. simpl_sizes. repeat split; lia.
Qed.
#[using="Type"] Lemma out_rframe : forall q lo S MB A len cap cur0 bs st Wx m0 P,
  vf_okA FI q lo S MB A len cap cur0 bs st Wx -> RFAKE FI st m0 -> In (P, P + 16) Wx ->
  rframeA FI q lo S st (fun mm => exists pa pb, rw_cells asegs mm P [C8 pa; C8 pb]).
Proof.
  intros q lo S MB A len cap cur0 bs st Wx m0 P VOK RF0 PIN m m' (pa & pb & H) MU WM.
  exists pa, pb. exact (out_rframe_c q lo S MB A len cap cur0 bs st Wx m0 P pa pb VOK RF0 PIN m m' H MU WM).
Qed.
#[using="Type"] Lemma rframeA_and : forall q lo S st (R1 R2 : mem -> Prop), rframeA FI q lo S st R1 -> rframeA FI q lo S st R2 -> rframeA FI q lo S st (fun mm => R1 mm /\ R2 mm).
Proof. intros q lo S st R1 R2 H1 H2 m m' [A1 A2] MU WM. split; [eapply H1| eapply H2]; eassumption. Qed.
#[using="Type"] Lemma rframeA_True : forall q lo S st, rframeA FI q lo S st (fun _ => True).
Proof. intros q lo S st m m' _ _ _. exact I. Qed.

#[using="Type"] Lemma vinv_qb : forall q lo S MB A len cap cur0 bs st Wx FMT flen ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 q' cur G cs m,
  vinv FI q lo S MB A len cap cur0 bs st Wx FMT flen ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 q' cur G cs m -> q + -304 <= q' <= q + -288.
Proof. intros until m. intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (QB & _) & _). exact QB. Qed.

#[using="Type"] Lemma WP_app : forall q lo S MB A len cap cur0 bs st Wx m0 q' WD,
  vf_okA FI q lo S MB A len cap cur0 bs st Wx -> RFAKE FI st m0 -> (forall iv, In iv WD -> In iv Wx) -> app_ivs (vWP lo S q' WD).
Proof.
  intros q lo S MB A len cap cur0 bs st Wx m0 q' WD VOK RF0 SUB.
  pose proof VOK as VOK'. destruct VOK' as (CLO & LO & _ & QHI & MBLO & MBS & SHI & _ & _ & PLB & _ & _ & _ & _ & _ & _ & _ & _ & _ & WXL & _ & _).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  destruct (lb_in_fs FI st m0 RF0 _ _ PLB) as [H1 H2].
  unfold vWP, app_ivs. constructor; [apply app_iv_stack; lia|]. constructor; [apply (sub_app_iv_fs FI); lia|].
  apply Forall_forall. intros [a b] HI. rewrite Forall_forall in WXL. destruct (WXL _ (SUB _ HI)) as [LE [LB|ER]]; cbn [fst snd] in *.
  - destruct (lb_in_fs FI st m0 RF0 _ _ LB) as [H3 H4]. apply (sub_app_iv_fs FI); lia.
  - unfold app_iv. cbn [fst snd]. left. lia.
Qed.

#[using="Type"] Lemma cell_step : forall lo S q' WD m m' X cs,
  rw_cells asegs m X cs -> munch (vWP lo S q' WD) m m' -> wmono asegs m m' -> disjoint_from (vWP lo S q' WD) X (Z.of_nat (cells_size cs)) ->
  rw_cells asegs m' X cs.
Proof. intros lo S q' WD m m' X cs H MU WM D. eapply rw_cells_transport; eassumption. Qed.

#[using="Type"] Lemma vinv_cur : forall q lo S MB A len cap cur0 bs st Wx FMT flen ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 q' cur G cs m,
  vinv FI q lo S MB A len cap cur0 bs st Wx FMT flen ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 q' cur G cs m -> cur0 <= cur <= len.
Proof. intros until m. intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CR & _). exact CR. Qed.

Definition vaP (G P : Z) (m : mem) : Prop := rw_cells asegs m G [C8 (wz P)] /\ shw m G 8 /\ shw m P 16.

#[using="Type"] Lemma vaP_step : forall q lo S MB A len cap cur0 bs st Wx m0 q' WD G P m m',
  vf_okA FI q lo S MB A len cap cur0 bs st Wx -> RFAKE FI st m0 -> (forall iv, In iv WD -> In iv Wx) ->
  q + -304 <= q' <= q + -288 -> q <= G ->
  vaP G P m -> munch (vWP lo S q' WD) m m' -> wmono asegs m m' -> vaP G P m'.
Proof.
  intros q lo S MB A len cap cur0 bs st Wx m0 q' WD G P m m' VOK RF0 SUB QB GLO (GC & SHG & SHP) MU WM.
  pose proof (WP_app q lo S MB A len cap cur0 bs st Wx m0 q' WD VOK RF0 SUB) as WA.
  split; [| split; [exact (shw_frame _ _ _ _ _ SHG MU WA)| exact (shw_frame _ _ _ _ _ SHP MU WA)]].
  eapply rw_cells_transport; [exact GC| exact MU| exact WM|].
  pose proof VOK as VOK'. destruct VOK' as (CLO & LO & _ & QHI & MBLO & MBS & SHI & _ & _ & PLB & _ & _ & _ & _ & _ & _ & _ & _ & _ & WXL & _ & _).
  unfold vWP. cbn [disjoint_from]. simpl_sizes. split; [right; lia|]. split; [right; lia|].
  clear - SUB WXL RF0 CLO LO GLO. induction WD as [|[a b] WD IH]; cbn [disjoint_from]; [exact I|].
  split; [| apply IH; intros iv HI; apply SUB; right; exact HI].
  rewrite Forall_forall in WXL. destruct (WXL (a, b) (SUB _ (or_introl eq_refl))) as [LE [LB|ER]]; cbn [fst snd] in *.
  - destruct (lb_in_fs FI st m0 RF0 _ _ LB) as [H3 H4]. pose proof (fsb_ok FI) as (B1 & B2 & _). right. lia.
  - pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR. right. lia.
Qed.

#[using="Type"] Lemma out_step0 : forall q lo S MB A len cap cur0 bs st Wx m0 q' P (pa pb : word) m m',
  vf_okA FI q lo S MB A len cap cur0 bs st Wx -> RFAKE FI st m0 -> In (P, P + 16) Wx ->
  rw_cells asegs m P [C8 pa; C8 pb] -> munch (vWP lo S q' []) m m' -> wmono asegs m m' -> rw_cells asegs m' P [C8 pa; C8 pb].
Proof.
  intros q lo S MB A len cap cur0 bs st Wx m0 q' P pa pb m m' VOK RF0 PIN PC MU WM.
  destruct (out_facts FI q lo S MB A len cap cur0 bs st Wx m0 VOK RF0 P 16 PIN ltac:(lia) ltac:(left; lia)) as (PLO & PHI & PPAR & PTXT).
  pose proof VOK as VOK'. destruct VOK' as (CLO & LO & _ & QHI & MBLO & MBS & _).
  eapply rw_cells_transport; [exact PC| exact MU| exact WM|]. unfold vWP. cbn [disjoint_from]. simpl_sizes. split; [left; lia|]. split; [lia| exact I].
Qed.

#[using="Type"] Lemma vaP_pro : forall q lo S MB A len cap cur0 bs st Wx m0 G P m,
  vf_okA FI q lo S MB A len cap cur0 bs st Wx -> RFAKE FI st m0 -> In (P, P + 16) Wx -> q <= G -> G + 8 <= 2^47 ->
  vaP G P m0 -> munch ((lo, q) :: (FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: []) m0 m -> wmono asegs m0 m ->
  fkeep FI [] st m0 m -> vaP G P m.
Proof.
  intros q lo S MB A len cap cur0 bs st Wx m0 G P m VOK RF0 PIN GLO GHI (GC & SHG & SHP) MU WM FK.
  pose proof VOK as VOK'. destruct VOK' as (CLO & LO & _ & QHI & MBLO & MBS & SHI & _ & _ & PLB & _ & _ & _ & _ & _ & _ & _ & _ & _ & WXL & _ & _).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (fsb_ok FI) as (B1 & B2 & _ & B4 & _).
  rewrite Forall_forall in WXL. destruct (WXL _ PIN) as [LE [LB|ER]]; cbn [fst snd] in *; [| exfalso; clear - ER; lia]. replace (P + 16 - P) with 16 in LB by lia.
  assert (FW : Forall (fsw_iv FI) ((lo, q) :: (FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: [])).
  { apply fsw_cons_app; [apply app_iv_stack; lia|]. apply (fsw_FSIV FI []). constructor. }
  split; [| split].
  - eapply rw_cells_transport; [exact GC| exact MU| exact WM|]. cbn [disjoint_from]. simpl_sizes.
    split; [right; lia|]. split; [right; lia|]. split; [right; unfold sh, SHADOW_OFF; clear - B2 ACR CLO LO GLO; Z.div_mod_to_equations; lia| exact I].
  - exact (shw_frame_fs FI _ m0 m G 8 SHG MU FW ltac:(right; lia)).
  - exact (shw_fkeep0 FI st m0 m P 16 SHP FK RF0 LB).
Qed.
#[using="Type"] Lemma out_pro : forall q lo S MB A len cap cur0 bs st Wx m0 P (pa pb : word) m,
  vf_okA FI q lo S MB A len cap cur0 bs st Wx -> In (P, P + 16) Wx ->
  rw_cells asegs m0 P [C8 pa; C8 pb] -> wmono asegs m0 m -> fkeep FI [] st m0 m -> rw_cells asegs m P [C8 pa; C8 pb].
Proof.
  intros q lo S MB A len cap cur0 bs st Wx m0 P pa pb m VOK PIN PC WM FK.
  pose proof VOK as VOK'. destruct VOK' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WXL & _ & _).
  rewrite Forall_forall in WXL. destruct (WXL _ PIN) as [LE [LB|ER]]; cbn [fst snd] in *; [| exfalso; clear - ER; lia]. replace (P + 16 - P) with 16 in LB by lia.
  eapply (rw_cells_fkeep FI [] st m0 m P _ PC FK WM); [left; exact LB| exact I].
Qed.

Section FMTK.
  Variables (q lo S MB A len cap cur0 : Z) (bs : list byte) (st : fsstate FI) (Wx : list ivl) (FMT flen : Z) (fb : list byte).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (m0 : mem).
  Variables (X : mem -> Z -> Z -> Prop) (R : mem -> Prop) (q' : Z).
  Hypothesis VOK : vf_okA FI q lo S MB A len cap cur0 bs st Wx.
  Hypothesis RF0 : RFAKE FI st m0.
  Hypothesis FBAT : forall m, mem_inv asegs m -> bytes_at asegs m FMT fb.
  Hypothesis FLEN : Z.of_nat (length fb) = flen.
  Hypothesis RFR : rframeA FI q lo S st R.
  Hypothesis XERR : forall mm rr cc, R mm -> rr <> 4 -> X mm rr cc.
  Notation POST := (vpostA FI q lo S MB A len cap cur0 bs st Wx ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 X).
  Notation VINV cur G cs mm := (vinv FI q lo S MB A len cap cur0 bs st Wx FMT flen ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 q' cur G cs mm).

  Definition carried (C : mem -> Prop) : Prop :=
    (forall mm, C mm -> R mm) /\ (forall mm mm', C mm -> munch (vWP lo S q' []) mm mm' -> wmono asegs mm mm' -> C mm').

  #[using="VOK RF0 RFR XERR"] Lemma ERRk : forall r cur' G' cs y1 y5 y6 y7 y10 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y24 y25 y26 y28 y29 y30 y31 mm,
    VINV cur' G' cs mm -> 0 <= r <= 5 -> r <> 4 -> R mm ->
    evt asegs POST (errstA FI q S st gp tp F_ fc q' r y1 y5 y6 y7 y10 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y24 y25 y26 y28 y29 y30 y31 mm).
  Proof.
    intros until mm. intros INVe RRe RNe HRe.
    eapply evt_mono.
    - eapply (errV FI) with (R := R) (XP := fun r c => r <> 4); [exact VOK| exact RF0| exact INVe| exact RRe| exact RNe| exact HRe| exact RFR| exact RNe].
    - intros ms V. eapply vpostA_mono; [exact V|]. cbn beta. intros mm' rr cc [HRm HXP]. exact (XERR mm' rr cc HRm HXP).
  Qed.

  #[using="FLEN"] Lemma nth_lt : forall (i : nat) c, nth_error fb i = Some c -> Z.of_nat i < flen.
  Proof. intros i c H. rewrite <- FLEN. apply Nat2Z.inj_lt. apply nth_error_Some. rewrite H. discriminate. Qed.

  #[using="VOK RF0 FBAT FLEN RFR XERR"] Lemma CONTk : forall (i : nat) (c : Z) r cur' G' cs y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y28 y29 y30 y31 mm,
    VINV cur' G' cs mm -> nth_error fb i = Some (Z_to_bv 8 c) -> 0 < c < 256 -> 0 <= FMT -> FMT + flen < 2^62 -> 0 <= r <= 5 -> R mm ->
    (r = 4 -> forall z1 z5 z6 z7 z10 z11 z13 z14 z15 z16 z17 z25 z26 z28 z29 z30 z31,
       evt asegs POST (headstA FI q S st gp tp F_ fc q' (FMT + Z.of_nat i) c z1 z5 z6 z7 z10 z11 z13 z14 z15 z16 z17 z25 z26 z28 z29 z30 z31 mm)) ->
    evt asegs POST (contstA FI q S st gp tp F_ fc q' r (FMT + Z.of_nat i) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y28 y29 y30 y31 mm).
  Proof.
    intros until mm. intros INVc NTH CRc F0 FH RRc HRc KH. pose proof (nth_lt i _ NTH) as IL.
    eapply (contV FI) with (c := c) (b := Z_to_bv 8 c).
    - eapply vinv_fmt_acc; [exact INVc| lia].
    - exact (fmt_rdA mm FMT fb i c (FBAT mm (vinv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INVc)) NTH).
    - rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn. rewrite Z.mod_small by lia. reflexivity.
    - lia.
    - exact RRc.
    - intros E _. exact (KH E).
    - intros _ C0. exfalso. lia.
    - intros RN. intros. eapply ERRk; [exact INVc| exact RRc| exact RN| exact HRc].
  Qed.

  Hypothesis F0 : 0 <= FMT.
  Hypothesis FH : FMT + flen < 2^62.

  #[using="IC VOK RF0 FBAT FLEN RFR XERR F0 FH"] Lemma LITk : forall (C : mem -> Prop) (i : nat) (c c' : Z) cur G' cs y1 y5 y6 y7 y10 y11 y13 y14 y15 y16 y17 y25 y26 y28 y29 y30 y31 mm,
    carried C -> VINV cur G' cs mm -> C mm ->
    nth_error fb (Datatypes.S i) = Some (Z_to_bv 8 c') -> 0 < c' < 256 -> 0 <= cs <= 1 ->
    0 < c < 256 -> c <> 9 -> c <> 32 -> c <> 37 ->
    (forall mm2 z1 z5 z6 z7 z10 z11 z13 z14 z15 z16 z17 z25 z26 z28 z29 z30 z31,
       VINV (cur + 1) G' cs mm2 -> C mm2 ->
       evt asegs POST (headstA FI q S st gp tp F_ fc q' (FMT + Z.of_nat (Datatypes.S i)) c' z1 z5 z6 z7 z10 z11 z13 z14 z15 z16 z17 z25 z26 z28 z29 z30 z31 mm2)) ->
    evt asegs POST (headstA FI q S st gp tp F_ fc q' (FMT + Z.of_nat i) c y1 y5 y6 y7 y10 y11 y13 y14 y15 y16 y17 y25 y26 y28 y29 y30 y31 mm).
  Proof.
    intros until mm. intros [CR CS] INVl HCm NTH CR' CSl CRc N9 N32 N37 KN. pose proof (nth_lt _ _ NTH) as IL.
    eapply (dir_litV IC FI) with (c := c).
    3: exact INVl. 1: exact VOK. 1: exact RF0.
    1: lia. 1: exact CSl. 1: exact CRc. 1: exact N9. 1: exact N32. 1: exact N37.
    - intros r z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z18 z25 z26 z28 z29 z30 z31 m' INV' MU' WM' RR'.
      pose proof (CS mm m' HCm MU' WM') as HCm'.
      replace (FMT + Z.of_nat i + 1) with (FMT + Z.of_nat (Datatypes.S i)) by lia.
      eapply (CONTk (Datatypes.S i) c'); [exact INV'| exact NTH| exact CR'| exact F0| exact FH| exact RR'| exact (CR _ HCm')|].
      intros _. intros. eapply KN; [exact INV'| exact HCm'].
    - intros. eapply ERRk; [exact INVl| lia| lia| exact (CR _ HCm)].
  Qed.

  #[using="IC VOK RF0 FBAT FLEN RFR XERR F0 FH"] Lemma WKk : forall (C : mem -> Prop) (i : nat) (c' : Z) cur G' cs y1 y5 y6 y7 y10 y11 y13 y14 y15 y16 y17 y25 y26 y28 y29 y30 y31 mm,
    carried C -> VINV cur G' cs mm -> C mm ->
    nth_error fb (Datatypes.S i) = Some (Z_to_bv 8 119) ->
    nth_error fb (Datatypes.S (Datatypes.S i)) = Some (Z_to_bv 8 c') -> 0 < c' < 256 ->
    (forall cur2 mm2 z1 z5 z6 z7 z10 z11 z13 z14 z15 z16 z17 z25 z26 z28 z29 z30 z31,
       VINV cur2 G' cs mm2 -> C mm2 -> cur <= cur2 ->
       evt asegs POST (headstA FI q S st gp tp F_ fc q' (FMT + Z.of_nat (Datatypes.S (Datatypes.S i))) c' z1 z5 z6 z7 z10 z11 z13 z14 z15 z16 z17 z25 z26 z28 z29 z30 z31 mm2)) ->
    evt asegs POST (headstA FI q S st gp tp F_ fc q' (FMT + Z.of_nat i) 37 y1 y5 y6 y7 y10 y11 y13 y14 y15 y16 y17 y25 y26 y28 y29 y30 y31 mm).
  Proof.
    intros until mm. intros [CR CS] INVl HCm NTH1 NTH CR' KN. pose proof (nth_lt _ _ NTH) as IL.
    eapply (dir_wV IC FI) with (b2 := Z_to_bv 8 119).
    3: exact INVl. 1: exact VOK. 1: exact RF0.
    1: { eapply vinv_fmt_acc; [exact INVl| lia]. }
    1: { replace (FMT + Z.of_nat i + 1) with (FMT + Z.of_nat (Datatypes.S i)) by lia.
         exact (fmt_rdA mm FMT fb (Datatypes.S i) 119 (FBAT mm (vinv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INVl)) NTH1). }
    1: reflexivity. 1: lia.
    - intros r cur2 z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z18 z25 z26 z28 z29 z30 z31 m' INV' MU' WM' RR' X'.
      pose proof (CS mm m' HCm MU' WM') as HCm'.
      replace (FMT + Z.of_nat i + 2) with (FMT + Z.of_nat (Datatypes.S (Datatypes.S i))) by lia.
      eapply (CONTk (Datatypes.S (Datatypes.S i)) c'); [exact INV'| exact NTH| exact CR'| exact F0| exact FH| exact RR'| exact (CR _ HCm')|].
      intros E. intros. eapply KN; [exact INV'| exact HCm'| exact (X' E)].
    - intros r cur2 z1 z5 z6 z7 z10 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z24 z25 z26 z28 z29 z30 z31 m' INV' MU' WM' RR' RN'.
      eapply ERRk; [exact INV'| exact RR'| exact RN'| exact (CR _ (CS mm m' HCm MU' WM'))].
  Qed.

  #[using="IC VOK RF0 FBAT FLEN RFR XERR F0 FH"] Lemma SPk : forall (C : mem -> Prop) (i : nat) (c' : Z) cur G' cs y1 y5 y6 y7 y10 y11 y13 y14 y15 y16 y17 y25 y26 y28 y29 y30 y31 mm,
    carried C -> VINV cur G' cs mm -> C mm ->
    nth_error fb (Datatypes.S i) = Some (Z_to_bv 8 c') -> 0 < c' < 256 ->
    (forall cur2 mm2 z1 z5 z6 z7 z10 z11 z13 z14 z15 z16 z17 z25 z26 z28 z29 z30 z31,
       VINV cur2 G' cs mm2 -> C mm2 -> cur <= cur2 ->
       evt asegs POST (headstA FI q S st gp tp F_ fc q' (FMT + Z.of_nat (Datatypes.S i)) c' z1 z5 z6 z7 z10 z11 z13 z14 z15 z16 z17 z25 z26 z28 z29 z30 z31 mm2)) ->
    evt asegs POST (headstA FI q S st gp tp F_ fc q' (FMT + Z.of_nat i) 32 y1 y5 y6 y7 y10 y11 y13 y14 y15 y16 y17 y25 y26 y28 y29 y30 y31 mm).
  Proof.
    intros until mm. intros [CR CS] INVl HCm NTH CR' KN. pose proof (nth_lt _ _ NTH) as IL.
    eapply (dir_spV IC FI).
    3: exact INVl. 1: exact VOK. 1: exact RF0. 1: lia.
    intros r cur2 z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z18 z25 z26 z28 z29 z30 z31 m' INV' MU' WM' RR' X'.
    pose proof (CS mm m' HCm MU' WM') as HCm'.
    replace (FMT + Z.of_nat i + 1) with (FMT + Z.of_nat (Datatypes.S i)) by lia.
    eapply (CONTk (Datatypes.S i) c'); [exact INV'| exact NTH| exact CR'| exact F0| exact FH| exact RR'| exact (CR _ HCm')|].
    intros E. intros. eapply KN; [exact INV'| exact HCm'| exact (X' E)].
  Qed.

  #[using="IC VOK RF0 FBAT FLEN RFR XERR F0 FH"] Lemma TABk : forall (C : mem -> Prop) (i : nat) (c' : Z) cur G' cs y1 y5 y6 y7 y10 y11 y13 y14 y15 y16 y17 y25 y26 y28 y29 y30 y31 mm,
    carried C -> VINV cur G' cs mm -> C mm ->
    nth_error fb (Datatypes.S i) = Some (Z_to_bv 8 c') -> 0 < c' < 256 ->
    (forall cur2 mm2 z1 z5 z6 z7 z10 z11 z13 z14 z15 z16 z17 z25 z26 z28 z29 z30 z31,
       VINV cur2 G' cs mm2 -> C mm2 -> cur + 1 <= cur2 ->
       evt asegs POST (headstA FI q S st gp tp F_ fc q' (FMT + Z.of_nat (Datatypes.S i)) c' z1 z5 z6 z7 z10 z11 z13 z14 z15 z16 z17 z25 z26 z28 z29 z30 z31 mm2)) ->
    evt asegs POST (headstA FI q S st gp tp F_ fc q' (FMT + Z.of_nat i) 9 y1 y5 y6 y7 y10 y11 y13 y14 y15 y16 y17 y25 y26 y28 y29 y30 y31 mm).
  Proof.
    intros until mm. intros [CR CS] INVl HCm NTH CR' KN. pose proof (nth_lt _ _ NTH) as IL.
    eapply (dir_tabV IC FI).
    3: exact INVl. 1: exact VOK. 1: exact RF0. 1: lia.
    - intros r cur2 z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z18 z25 z26 z28 z29 z30 z31 m' INV' MU' WM' RR' X'.
      pose proof (CS mm m' HCm MU' WM') as HCm'.
      replace (FMT + Z.of_nat i + 1) with (FMT + Z.of_nat (Datatypes.S i)) by lia.
      eapply (CONTk (Datatypes.S i) c'); [exact INV'| exact NTH| exact CR'| exact F0| exact FH| exact RR'| exact (CR _ HCm')|].
      intros E. intros. eapply KN; [exact INV'| exact HCm'| exact (X' E)].
    - intros r cur2 z1 z5 z6 z7 z10 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z24 z25 z26 z28 z29 z30 z31 m' INV' MU' WM' RR' RN'.
      eapply ERRk; [exact INV'| exact RR'| exact RN'| exact (CR _ (CS mm m' HCm MU' WM'))].
  Qed.

  #[using="VOK RF0 FBAT FLEN RFR XERR F0 FH"] Lemma IKk : forall (C : mem -> Prop) (i : nat) (c' : Z) cur G' cs y1 y5 y6 y7 y10 y11 y13 y14 y15 y16 y17 y25 y26 y28 y29 y30 y31 mm,
    carried C -> VINV cur G' cs mm -> C mm ->
    nth_error fb (Datatypes.S i) = Some (Z_to_bv 8 105) ->
    nth_error fb (Datatypes.S (Datatypes.S i)) = Some (Z_to_bv 8 c') -> 0 < c' < 256 ->
    (forall mm2 z1 z5 z6 z7 z10 z11 z13 z14 z15 z16 z17 z25 z26 z28 z29 z30 z31,
       VINV cur G' 0 mm2 -> C mm2 ->
       evt asegs POST (headstA FI q S st gp tp F_ fc q' (FMT + Z.of_nat (Datatypes.S (Datatypes.S i))) c' z1 z5 z6 z7 z10 z11 z13 z14 z15 z16 z17 z25 z26 z28 z29 z30 z31 mm2)) ->
    evt asegs POST (headstA FI q S st gp tp F_ fc q' (FMT + Z.of_nat i) 37 y1 y5 y6 y7 y10 y11 y13 y14 y15 y16 y17 y25 y26 y28 y29 y30 y31 mm).
  Proof.
    intros until mm. intros [CR CS] INVl HCm NTH1 NTH CR' KN. pose proof (nth_lt _ _ NTH) as IL.
    eapply (dir_iV FI) with (b2 := Z_to_bv 8 105).
    3: exact INVl. 1: exact VOK. 1: exact RF0.
    1: { eapply vinv_fmt_acc; [exact INVl| lia]. }
    1: { replace (FMT + Z.of_nat i + 1) with (FMT + Z.of_nat (Datatypes.S i)) by lia.
         exact (fmt_rdA mm FMT fb (Datatypes.S i) 105 (FBAT mm (vinv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INVl)) NTH1). }
    1: reflexivity. 1: lia.
    intros z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z18 z25 z26 z28 z29 z30 z31 m' INV' MU' WM'.
    pose proof (CS mm m' HCm MU' WM') as HCm'.
    replace (FMT + Z.of_nat i + 2) with (FMT + Z.of_nat (Datatypes.S (Datatypes.S i))) by lia.
    eapply (CONTk (Datatypes.S (Datatypes.S i)) c'); [exact INV'| exact NTH| exact CR'| exact F0| exact FH| lia| exact (CR _ HCm')|].
    intros _. intros. eapply KN; [exact INV'| exact HCm'].
  Qed.
End FMTK.

Notation FMT_CRLF_A := 0x21a60%Z.
Definition fb_crlf : list byte := map (Z_to_bv 8) [37; 99; 0].
#[using="Type"] Lemma fb_crlf_at : forall m, mem_inv asegs m -> bytes_at asegs m FMT_CRLF_A fb_crlf.
Proof.
  intros m MI. pose proof (ro_cells_image asegs m FMT_CRLF_A fb_crlf MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO.
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

#[using="IC STACK_MALLOC_1"] Theorem vf_crlfA : forall (q lo S MB A len cap cur0 : Z) (bs : list byte) (st : fsstate FI) (G : Z)
    ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F_ : bvmap 5 word) fc m0,
  vf_okA FI q lo S MB A len cap cur0 bs st [] -> RFAKE FI st m0 -> fs_call_ok FI st tp 1 -> FSENV FI m0 ->
  stk asegs m0 lo q ->
  rw_cells asegs m0 S [C8 (wz MB); C8 (wz cur0); C4 (wz 0)] -> rw_cells asegs m0 MB (mbuf_cells A len cap) -> bytes_at asegs m0 A bs ->
  mem_inv asegs m0 -> asan_env asegs m0 ->
  shw m0 S 24 -> shw m0 MB 32 -> (0 < len -> shw m0 A len) -> shw m0 SEPTAB_A 20 -> shw m0 FMT_CRLF_A 3 ->
  shz m0 (sh lo) (sh q) ->
  evt asegs (vpostA FI q lo S MB A len cap cur0 bs st [] ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0
               (fun m' r cur' => True /\ (r = 4 -> cur0 + 1 <= cur')))
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz S) (wz FMT_CRLF_A) (wz G) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz vfmatch_entryA) fc None m0 (seg_rom asegs)).
Proof.
  intros until m0. intros VOK RF0 FCO FE0 ST SC MBC BUF MI AE SHS SHMB SHA SHSEP SHFMT SHZ.
  eapply (prologueV FI STACK_MALLOC_1) with (FMT := FMT_CRLF_A) (flen := 3) (c0 := 37) (b0 := Z_to_bv 8 37); try eassumption; try reflexivity; try lia.
  { intros m MIm. exact (fmt_rdA m FMT_CRLF_A fb_crlf 0 37 (fb_crlf_at m MIm) eq_refl). }
  intros q' m x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x25 x26 x28 x29 x30 x31 INV MUF WMF FKF.
  eapply (dir_cV IC FI) with (b2 := Z_to_bv 8 99).
  3: exact INV. 1: exact VOK. 1: exact RF0.
  1: { eapply vinv_fmt_acc; [exact INV| lia]. }
  1: { exact (fmt_rdA m FMT_CRLF_A fb_crlf 1 99 (fb_crlf_at m (vinv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV)) eq_refl). }
  1: reflexivity. 1: lia.
  - intros r cur' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y28 y29 y30 y31 m' INV' MU' WM' RR X1.
    eapply (contV FI) with (c := 0) (b := Z_to_bv 8 0).
    + eapply vinv_fmt_acc; [exact INV'| lia].
    + exact (fmt_rdA m' FMT_CRLF_A fb_crlf 2 0 (fb_crlf_at m' (vinv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV')) eq_refl).
    + reflexivity.
    + lia.
    + exact RR.
    + intros _ C. exfalso. apply C. reflexivity.
    + intros -> _. intros.
      eapply (epiV FI) with (R := fun _ => True) (XP := fun r c => r = 4 -> cur0 + 1 <= c).
      * exact VOK.
      * exact RF0.
      * exact INV'.
      * lia.
      * intros _. specialize (X1 eq_refl). lia.
      * intros C; exfalso; apply C; reflexivity.
      * exact I.
      * intros ? ? ? ? ?; exact I.
      * exact X1.
    + intros RN. intros.
      eapply (errV FI) with (R := fun _ => True) (XP := fun r c => r = 4 -> cur0 + 1 <= c); [exact VOK| exact RF0| exact INV'| exact RR| exact RN| exact I| intros ? ? ? ? ?; exact I| intros E; exfalso; exact (RN E)].
  - intros r cur' y1 y5 y6 y7 y10 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y24 y25 y26 y28 y29 y30 y31 m' INV' MU' WM' RR RN.
    eapply (errV FI) with (R := fun _ => True) (XP := fun r c => r = 4 -> cur0 + 1 <= c); [exact VOK| exact RF0| exact INV'| exact RR| exact RN| exact I| intros ? ? ? ? ?; exact I| intros E; exfalso; exact (RN E)].
Qed.

Notation FMT_RESP_A := 0x21880%Z.
Definition fb_resp : list byte := map (Z_to_bv 8) [37; 105; 104; 116; 116; 112; 37; 119; 47; 37; 119; 37; 76; 37; 99; 0].
#[using="Type"] Lemma fb_resp_at : forall m, mem_inv asegs m -> bytes_at asegs m FMT_RESP_A fb_resp.
Proof.
  intros m MI. pose proof (ro_cells_image asegs m FMT_RESP_A fb_resp MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO.
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Definition X_respA (A len cur0 : Z) (bs : list byte) (P1 : Z) : mem -> Z -> Z -> Prop := fun m' r cur' =>
  exists pa pb, rw_cells asegs m' P1 [C8 pa; C8 pb]
    /\ (r = 4 -> exists o l, pa = wz (A + o) /\ pb = wz l /\ cur0 <= o /\ 0 <= l /\ o + l < cur' /\ cur' <= len
          /\ exists b, nth_error bs (Z.to_nat (o + l)) = Some b /\ (bv_unsigned b = 13 \/ bv_unsigned b = 10)).

#[using="IC STACK_MALLOC_1"] Theorem vf_respA : forall (q lo S MB A len cap cur0 : Z) (bs : list byte) (st : fsstate FI) (G P1 : Z) (pw1 pw2 : word)
    ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F_ : bvmap 5 word) fc m0,
  vf_okA FI q lo S MB A len cap cur0 bs st [(P1, P1 + 16)] -> RFAKE FI st m0 -> fs_call_ok FI st tp 1 -> FSENV FI m0 ->
  stk asegs m0 lo q ->
  rw_cells asegs m0 S [C8 (wz MB); C8 (wz cur0); C4 (wz 0)] -> rw_cells asegs m0 MB (mbuf_cells A len cap) -> bytes_at asegs m0 A bs ->
  mem_inv asegs m0 -> asan_env asegs m0 ->
  shw m0 S 24 -> shw m0 MB 32 -> (0 < len -> shw m0 A len) -> shw m0 SEPTAB_A 20 -> shw m0 FMT_RESP_A 16 ->
  shz m0 (sh lo) (sh q) ->
  rw_cells asegs m0 G [C8 (wz P1)] -> shw m0 G 8 -> q <= G -> G + 8 <= 2^47 -> G mod 8 = 0 ->
  rw_cells asegs m0 P1 [C8 pw1; C8 pw2] -> shw m0 P1 16 -> P1 mod 8 = 0 ->
  evt asegs (vpostA FI q lo S MB A len cap cur0 bs st [(P1, P1 + 16)] ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 (X_respA A len cur0 bs P1))
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz S) (wz FMT_RESP_A) (wz G) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz vfmatch_entryA) fc None m0 (seg_rom asegs)).
Proof.
  intros until m0. intros VOK RF0 FCO FE0 ST SC MBC BUF MI AE SHS SHMB SHA SHSEP SHFMT SHZ GC SHG GLO GHI GAL PC1 SHP PAL.
  assert (PIN : In (P1, P1 + 16) [(P1, P1 + 16)]) by (left; reflexivity).
  assert (SUB0 : forall iv : ivl, In iv [] -> In iv [(P1, P1 + 16)]) by (intros iv []).
  assert (SUB1 : forall iv : ivl, In iv [(P1, P1 + 16)] -> In iv [(P1, P1 + 16)]) by (intros iv H; exact H).

  assert (ERR : forall q' r cur' G' cs (pa pb : word) y1 y5 y6 y7 y10 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y24 y25 y26 y28 y29 y30 y31 m,
    vinv FI q lo S MB A len cap cur0 bs st [(P1, P1 + 16)] FMT_RESP_A 16 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 q' cur' G' cs m ->
    0 <= r <= 5 -> r <> 4 -> rw_cells asegs m P1 [C8 pa; C8 pb] ->
    evt asegs (vpostA FI q lo S MB A len cap cur0 bs st [(P1, P1 + 16)] ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 (X_respA A len cur0 bs P1))
      (errstA FI q S st gp tp F_ fc q' r y1 y5 y6 y7 y10 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y24 y25 y26 y28 y29 y30 y31 m)).
  { intros until m. intros INVe RRe RNe PCe.
    eapply evt_mono.
    - eapply (errV FI) with (R := fun mm => exists pa pb, rw_cells asegs mm P1 [C8 pa; C8 pb]) (XP := fun r c => r <> 4);
        [exact VOK| exact RF0| exact INVe| exact RRe| exact RNe| exists pa, pb; exact PCe| eapply out_rframe; [exact VOK| exact RF0| exact PIN]| exact RNe].
    - intros ms V. eapply vpostA_mono; [exact V|]. cbn beta. intros mm rr cc [(pa' & pb' & HRm) HXP]. exists pa', pb'. split; [exact HRm| intros E; exfalso; exact (HXP E)]. }
  eapply (prologueV FI STACK_MALLOC_1) with (FMT := FMT_RESP_A) (flen := 16) (c0 := 37) (b0 := Z_to_bv 8 37); try eassumption; try reflexivity; try lia.
  { intros m MIm. exact (fmt_rdA m FMT_RESP_A fb_resp 0 37 (fb_resp_at m MIm) eq_refl). }
  intros q' m x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x25 x26 x28 x29 x30 x31 INV MUF WMF FKF.
  pose proof (vinv_qb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as QB.
  pose proof (vaP_pro q lo S MB A len cap cur0 bs st _ m0 G P1 m VOK RF0 PIN GLO GHI (conj GC (conj SHG SHP)) MUF WMF FKF) as VA.
  pose proof (out_pro q lo S MB A len cap cur0 bs st _ m0 P1 _ _ m VOK PIN PC1 WMF FKF) as PC.
  clear GC SHG SHP PC1 MUF WMF FKF.

  assert (CONTK : forall (i : nat) (c : Z) r cur' G' cs (pa pb : word) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y28 y29 y30 y31 mm,
    vinv FI q lo S MB A len cap cur0 bs st [(P1, P1 + 16)] FMT_RESP_A 16 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 q' cur' G' cs mm ->
    nth_error fb_resp i = Some (Z_to_bv 8 c) -> 0 < c < 256 -> (i < 16)%nat -> 0 <= r <= 5 -> rw_cells asegs mm P1 [C8 pa; C8 pb] ->
    (r = 4 -> forall z1 z5 z6 z7 z10 z11 z13 z14 z15 z16 z17 z25 z26 z28 z29 z30 z31,
       evt asegs (vpostA FI q lo S MB A len cap cur0 bs st [(P1, P1 + 16)] ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 (X_respA A len cur0 bs P1))
         (headstA FI q S st gp tp F_ fc q' (FMT_RESP_A + Z.of_nat i) c z1 z5 z6 z7 z10 z11 z13 z14 z15 z16 z17 z25 z26 z28 z29 z30 z31 mm)) ->
    evt asegs (vpostA FI q lo S MB A len cap cur0 bs st [(P1, P1 + 16)] ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 (X_respA A len cur0 bs P1))
      (contstA FI q S st gp tp F_ fc q' r (FMT_RESP_A + Z.of_nat i) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y28 y29 y30 y31 mm)).
  { intros until mm. intros INVc NTH CR IR RRc PCc KH.
    eapply (contV FI) with (c := c) (b := Z_to_bv 8 c).
    - eapply vinv_fmt_acc; [exact INVc| lia].
    - exact (fmt_rdA mm FMT_RESP_A fb_resp i c (fb_resp_at mm (vinv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INVc)) NTH).
    - rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn. rewrite Z.mod_small by lia. reflexivity.
    - lia.
    - exact RRc.
    - intros E _. exact (KH E).
    - intros _ C0. exfalso. lia.
    - intros RN. intros. eapply ERR; [exact INVc| exact RRc| exact RN| exact PCc]. }

  assert (LITK : forall (i : nat) (c c' : Z) cur G' cs (pa pb : word) y1 y5 y6 y7 y10 y11 y13 y14 y15 y16 y17 y25 y26 y28 y29 y30 y31 mm,
    vinv FI q lo S MB A len cap cur0 bs st [(P1, P1 + 16)] FMT_RESP_A 16 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 q' cur G' cs mm ->
    vaP G P1 mm -> rw_cells asegs mm P1 [C8 pa; C8 pb] ->
    nth_error fb_resp (Datatypes.S i) = Some (Z_to_bv 8 c') -> 0 < c' < 256 -> (i < 15)%nat -> 0 <= cs <= 1 ->
    0 < c < 256 -> c <> 9 -> c <> 32 -> c <> 37 ->
    (forall mm2 z1 z5 z6 z7 z10 z11 z13 z14 z15 z16 z17 z25 z26 z28 z29 z30 z31,
       vinv FI q lo S MB A len cap cur0 bs st [(P1, P1 + 16)] FMT_RESP_A 16 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 q' (cur + 1) G' cs mm2 ->
       vaP G P1 mm2 -> rw_cells asegs mm2 P1 [C8 pa; C8 pb] ->
       evt asegs (vpostA FI q lo S MB A len cap cur0 bs st [(P1, P1 + 16)] ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 (X_respA A len cur0 bs P1))
         (headstA FI q S st gp tp F_ fc q' (FMT_RESP_A + Z.of_nat (Datatypes.S i)) c' z1 z5 z6 z7 z10 z11 z13 z14 z15 z16 z17 z25 z26 z28 z29 z30 z31 mm2)) ->
    evt asegs (vpostA FI q lo S MB A len cap cur0 bs st [(P1, P1 + 16)] ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 (X_respA A len cur0 bs P1))
      (headstA FI q S st gp tp F_ fc q' (FMT_RESP_A + Z.of_nat i) c y1 y5 y6 y7 y10 y11 y13 y14 y15 y16 y17 y25 y26 y28 y29 y30 y31 mm)).
  { intros until mm. intros INVl VAl PCl NTH CR' IR CSl CRc N9 N32 N37 KN.
    eapply (dir_litV IC FI) with (c := c).
    3: exact INVl. 1: exact VOK. 1: exact RF0.
    1: lia. 1: exact CSl. 1: exact CRc. 1: exact N9. 1: exact N32. 1: exact N37.
    - intros r z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z18 z25 z26 z28 z29 z30 z31 m' INV' MU' WM' RR'.
      pose proof (vaP_step q lo S MB A len cap cur0 bs st _ m0 q' [] G P1 mm m' VOK RF0 SUB0 QB GLO VAl MU' WM') as VA'.
      pose proof (out_step0 q lo S MB A len cap cur0 bs st _ m0 q' P1 pa pb mm m' VOK RF0 PIN PCl MU' WM') as PC'.
      replace (FMT_RESP_A + Z.of_nat i + 1) with (FMT_RESP_A + Z.of_nat (Datatypes.S i)) by lia.
      eapply (CONTK (Datatypes.S i) c'); [exact INV'| exact NTH| exact CR'| lia| exact RR'| exact PC'|].
      intros _. intros. eapply KN; [exact INV'| exact VA'| exact PC'].
    - intros. eapply ERR; [exact INVl| lia| lia| exact PCl]. }

  assert (WK : forall (i : nat) (c' : Z) cur G' cs (pa pb : word) y1 y5 y6 y7 y10 y11 y13 y14 y15 y16 y17 y25 y26 y28 y29 y30 y31 mm,
    vinv FI q lo S MB A len cap cur0 bs st [(P1, P1 + 16)] FMT_RESP_A 16 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 q' cur G' cs mm ->
    vaP G P1 mm -> rw_cells asegs mm P1 [C8 pa; C8 pb] ->
    nth_error fb_resp (Datatypes.S i) = Some (Z_to_bv 8 119) ->
    nth_error fb_resp (Datatypes.S (Datatypes.S i)) = Some (Z_to_bv 8 c') -> 0 < c' < 256 -> (i < 14)%nat ->
    (forall cur2 mm2 z1 z5 z6 z7 z10 z11 z13 z14 z15 z16 z17 z25 z26 z28 z29 z30 z31,
       vinv FI q lo S MB A len cap cur0 bs st [(P1, P1 + 16)] FMT_RESP_A 16 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 q' cur2 G' cs mm2 ->
       vaP G P1 mm2 -> rw_cells asegs mm2 P1 [C8 pa; C8 pb] -> cur <= cur2 ->
       evt asegs (vpostA FI q lo S MB A len cap cur0 bs st [(P1, P1 + 16)] ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 (X_respA A len cur0 bs P1))
         (headstA FI q S st gp tp F_ fc q' (FMT_RESP_A + Z.of_nat (Datatypes.S (Datatypes.S i))) c' z1 z5 z6 z7 z10 z11 z13 z14 z15 z16 z17 z25 z26 z28 z29 z30 z31 mm2)) ->
    evt asegs (vpostA FI q lo S MB A len cap cur0 bs st [(P1, P1 + 16)] ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 (X_respA A len cur0 bs P1))
      (headstA FI q S st gp tp F_ fc q' (FMT_RESP_A + Z.of_nat i) 37 y1 y5 y6 y7 y10 y11 y13 y14 y15 y16 y17 y25 y26 y28 y29 y30 y31 mm)).
  { intros until mm. intros INVl VAl PCl NTH1 NTH CR' IR KN.
    eapply (dir_wV IC FI) with (b2 := Z_to_bv 8 119).
    3: exact INVl. 1: exact VOK. 1: exact RF0.
    1: { eapply vinv_fmt_acc; [exact INVl| lia]. }
    1: { replace (FMT_RESP_A + Z.of_nat i + 1) with (FMT_RESP_A + Z.of_nat (Datatypes.S i)) by lia.
         exact (fmt_rdA mm FMT_RESP_A fb_resp (Datatypes.S i) 119 (fb_resp_at mm (vinv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INVl)) NTH1). }
    1: reflexivity. 1: lia.
    - intros r cur2 z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z18 z25 z26 z28 z29 z30 z31 m' INV' MU' WM' RR' X'.
      pose proof (vaP_step q lo S MB A len cap cur0 bs st _ m0 q' [] G P1 mm m' VOK RF0 SUB0 QB GLO VAl MU' WM') as VA'.
      pose proof (out_step0 q lo S MB A len cap cur0 bs st _ m0 q' P1 pa pb mm m' VOK RF0 PIN PCl MU' WM') as PC'.
      replace (FMT_RESP_A + Z.of_nat i + 2) with (FMT_RESP_A + Z.of_nat (Datatypes.S (Datatypes.S i))) by lia.
      eapply (CONTK (Datatypes.S (Datatypes.S i)) c'); [exact INV'| exact NTH| exact CR'| lia| exact RR'| exact PC'|].
      intros E. intros. eapply KN; [exact INV'| exact VA'| exact PC'| exact (X' E)].
    - intros r cur2 z1 z5 z6 z7 z10 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z24 z25 z26 z28 z29 z30 z31 m' INV' MU' WM' RR' RN'.
      pose proof (out_step0 q lo S MB A len cap cur0 bs st _ m0 q' P1 pa pb mm m' VOK RF0 PIN PCl MU' WM') as PC'.
      eapply ERR; [exact INV'| exact RR'| exact RN'| exact PC']. }

  eapply (dir_iV FI) with (b2 := Z_to_bv 8 105).
  3: exact INV. 1: exact VOK. 1: exact RF0.
  1: { eapply vinv_fmt_acc; [exact INV| lia]. }
  1: { exact (fmt_rdA m FMT_RESP_A fb_resp 1 105 (fb_resp_at m (vinv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV)) eq_refl). }
  1: reflexivity. 1: lia.
  intros z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z18 z25 z26 z28 z29 z30 z31 m1 INV1 MU1 WM1.
  pose proof (vaP_step q lo S MB A len cap cur0 bs st _ m0 q' [] G P1 m m1 VOK RF0 SUB0 QB GLO VA MU1 WM1) as VA1.
  pose proof (out_step0 q lo S MB A len cap cur0 bs st _ m0 q' P1 _ _ m m1 VOK RF0 PIN PC MU1 WM1) as PC_1.
  eapply (CONTK 2%nat 104); [exact INV1| reflexivity| lia| lia| lia| exact PC_1|]. intros _. intros.
  eapply (LITK 2%nat 104 116); [exact INV1| exact VA1| exact PC_1| reflexivity| lia| lia| lia| lia| lia| lia| lia|]. intros m2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV2 VA2 PC_2.
  eapply (LITK 3%nat 116 116); [exact INV2| exact VA2| exact PC_2| reflexivity| lia| lia| lia| lia| lia| lia| lia|]. intros m3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV3 VA3 PC_3.
  eapply (LITK 4%nat 116 112); [exact INV3| exact VA3| exact PC_3| reflexivity| lia| lia| lia| lia| lia| lia| lia|]. intros m4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV4 VA4 PC_4.
  eapply (LITK 5%nat 112 37); [exact INV4| exact VA4| exact PC_4| reflexivity| lia| lia| lia| lia| lia| lia| lia|]. intros m5 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV5 VA5 PC_5.
  eapply (WK 6%nat 47); [exact INV5| exact VA5| exact PC_5| reflexivity| reflexivity| lia| lia|]. intros cur6 m6 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV6 VA6 PC_6 CU6.
  eapply (LITK 8%nat 47 37); [exact INV6| exact VA6| exact PC_6| reflexivity| lia| lia| lia| lia| lia| lia| lia|]. intros m7 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV7 VA7 PC_7.
  eapply (WK 9%nat 37); [exact INV7| exact VA7| exact PC_7| reflexivity| reflexivity| lia| lia|]. intros cur8 m8 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV8 VA8 PC_8 CU8.

  destruct VA8 as (GC8 & SHG8 & SHP8).
  eapply (dir_LV IC FI) with (b2 := Z_to_bv 8 76) (P := P1).
  3: exact INV8. 1: exact VOK. 1: exact RF0.
  1: { eapply vinv_fmt_acc; [exact INV8| lia]. }
  1: { exact (fmt_rdA m8 FMT_RESP_A fb_resp 12 76 (fb_resp_at m8 (vinv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV8)) eq_refl). }
  1: reflexivity. 1: lia. 1: exact GC8. 1: exact SHG8. 1: exact GLO. 1: exact GHI. 1: exact GAL. 1: exact PC_8. 1: exact SHP8. 1: exact PIN. 1: exact PAL.
  intros r9 cur9 pb9 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m9 INV9 MU9 WM9 RR9 PC_9 X9.
  eapply (CONTK 13%nat 37); [exact INV9| reflexivity| lia| lia| exact RR9| exact PC_9|]. intros E9. intros. specialize (X9 E9). destruct X9 as (l9 & -> & L0 & -> & CL9 & BY9).

  eapply (dir_cV IC FI) with (b2 := Z_to_bv 8 99).
  3: exact INV9. 1: exact VOK. 1: exact RF0.
  1: { eapply vinv_fmt_acc; [exact INV9| lia]. }
  1: { exact (fmt_rdA m9 FMT_RESP_A fb_resp 14 99 (fb_resp_at m9 (vinv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV9)) eq_refl). }
  1: reflexivity. 1: lia.
  - intros r10 cur10 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m10 INV10 MU10 WM10 RR10 X10.
    pose proof (out_step0 q lo S MB A len cap cur0 bs st _ m0 q' P1 _ _ m9 m10 VOK RF0 PIN PC_9 MU10 WM10) as PC_10.
    pose proof (vinv_cur _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV10) as CR10.
    pose proof (vinv_cur _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV8) as CR8.
    eapply (contV FI) with (c := 0) (b := Z_to_bv 8 0).
    + eapply vinv_fmt_acc; [exact INV10| lia].
    + exact (fmt_rdA m10 FMT_RESP_A fb_resp 15 0 (fb_resp_at m10 (vinv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV10)) eq_refl).
    + reflexivity.
    + lia.
    + exact RR10.
    + intros _ C. exfalso. apply C. reflexivity.
    + intros -> _. intros. specialize (X10 eq_refl).
      eapply evt_mono.
      * eapply (epiV FI) with (R := fun mm => rw_cells asegs mm P1 [C8 (wz (A + cur8)); C8 (wz l9)])
                             (XP := fun r c => r = 4 -> cur8 + l9 < c /\ c <= len);
          [exact VOK| exact RF0| exact INV10| lia| intros _; lia| intros C; exfalso; apply C; reflexivity| exact PC_10
          | eapply out_rframe_c; [exact VOK| exact RF0| exact PIN]| intros _; lia].
      * intros ms V. eapply vpostA_mono; [exact V|]. cbn beta. intros mm rr cc [HRm HXP].
        exists (wz (A + cur8)), (wz l9). split; [exact HRm|]. intros E. destruct (HXP E) as [H1 H2].
        exists cur8, l9. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia| exact BY9].
    + intros RN. intros. eapply ERR; [exact INV10| exact RR10| exact RN| exact PC_10].
  - intros r10 cur10 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m10 INV10 MU10 WM10 RR10 RN10.
    pose proof (out_step0 q lo S MB A len cap cur0 bs st _ m0 q' P1 _ _ m9 m10 VOK RF0 PIN PC_9 MU10 WM10) as PC_10.
    eapply ERR; [exact INV10| exact RR10| exact RN10| exact PC_10].
Qed.

Notation FMT_HDR_A := 0x218c0%Z.
Definition fb_hdr : list byte := map (Z_to_bv 8) [32; 58; 32; 37; 82; 37; 99; 0].
#[using="Type"] Lemma fb_hdr_at : forall m, mem_inv asegs m -> bytes_at asegs m FMT_HDR_A fb_hdr.
Proof.
  intros m MI. pose proof (ro_cells_image asegs m FMT_HDR_A fb_hdr MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO.
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Definition X_hdrA (A len cur0 : Z) (P1 : Z) : mem -> Z -> Z -> Prop := fun m' r cur' =>
  exists pa pb, rw_cells asegs m' P1 [C8 pa; C8 pb]
    /\ (r = 4 -> exists o l, pa = wz (A + o) /\ pb = wz l /\ cur0 + 1 <= o /\ 0 <= l /\ o + l <= len /\ cur0 + 1 <= cur' /\ o + l + 1 <= cur').

#[using="Type"] Lemma carried_vaP1 : forall q lo S MB A len cap cur0 bs st m0 q' G P1 (pw1 pw2 : word),
  vf_okA FI q lo S MB A len cap cur0 bs st [(P1, P1 + 16)] -> RFAKE FI st m0 -> q + -304 <= q' <= q + -288 -> q <= G ->
  carried lo S (fun mm => exists pa pb, rw_cells asegs mm P1 [C8 pa; C8 pb]) q'
          (fun mm => vaP G P1 mm /\ rw_cells asegs mm P1 [C8 pw1; C8 pw2]).
Proof.
  intros q lo S MB A len cap cur0 bs st m0 q' G P1 pw1 pw2 VOK RF0 QB GLO. split.
  - intros mm [_ PC]. exists pw1, pw2. exact PC.
  - intros mm mm' [VA PC] MU WM. split.
    + eapply (vaP_step q lo S MB A len cap cur0 bs st _ m0 q' [] G P1 mm mm' VOK RF0); [intros iv []| exact QB| exact GLO| exact VA| exact MU| exact WM].
    + eapply (out_step0 q lo S MB A len cap cur0 bs st _ m0 q' P1 pw1 pw2 mm mm' VOK RF0); [left; reflexivity| exact PC| exact MU| exact WM].
Qed.

#[using="IC STACK_MALLOC_1"] Theorem vf_hdrA : forall (q lo S MB A len cap cur0 : Z) (bs : list byte) (st : fsstate FI) (G P1 : Z) (pw1 pw2 : word)
    ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F_ : bvmap 5 word) fc m0,
  vf_okA FI q lo S MB A len cap cur0 bs st [(P1, P1 + 16)] -> RFAKE FI st m0 -> fs_call_ok FI st tp 1 -> FSENV FI m0 ->
  stk asegs m0 lo q ->
  rw_cells asegs m0 S [C8 (wz MB); C8 (wz cur0); C4 (wz 0)] -> rw_cells asegs m0 MB (mbuf_cells A len cap) -> bytes_at asegs m0 A bs ->
  mem_inv asegs m0 -> asan_env asegs m0 ->
  shw m0 S 24 -> shw m0 MB 32 -> (0 < len -> shw m0 A len) -> shw m0 SEPTAB_A 20 -> shw m0 FMT_HDR_A 8 ->
  shz m0 (sh lo) (sh q) ->
  rw_cells asegs m0 G [C8 (wz P1)] -> shw m0 G 8 -> q <= G -> G + 8 <= 2^47 -> G mod 8 = 0 ->
  rw_cells asegs m0 P1 [C8 pw1; C8 pw2] -> shw m0 P1 16 -> P1 mod 8 = 0 ->
  evt asegs (vpostA FI q lo S MB A len cap cur0 bs st [(P1, P1 + 16)] ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 (X_hdrA A len cur0 P1))
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz S) (wz FMT_HDR_A) (wz G) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz vfmatch_entryA) fc None m0 (seg_rom asegs)).
Proof.
  intros until m0. intros VOK RF0 FCO FE0 ST SC MBC BUF MI AE SHS SHMB SHA SHSEP SHFMT SHZ GC SHG GLO GHI GAL PC1 SHP PAL.
  assert (PIN : In (P1, P1 + 16) [(P1, P1 + 16)]) by (left; reflexivity).
  assert (SUB1 : forall iv : ivl, In iv [(P1, P1 + 16)] -> In iv [(P1, P1 + 16)]) by (intros iv H; exact H).
  pose (R := fun mm : mem => exists pa pb, rw_cells asegs mm P1 [C8 pa; C8 pb]).
  assert (RFR : rframeA FI q lo S st R) by (eapply out_rframe; [exact VOK| exact RF0| exact PIN]).
  assert (XERR : forall mm rr cc, R mm -> rr <> 4 -> X_hdrA A len cur0 P1 mm rr cc).
  { intros mm rr cc (pa & pb & H) RN. exists pa, pb. split; [exact H| intros E; exfalso; exact (RN E)]. }
  eapply (prologueV FI STACK_MALLOC_1) with (FMT := FMT_HDR_A) (flen := 8) (c0 := 32) (b0 := Z_to_bv 8 32); try eassumption; try reflexivity; try lia.
  { intros m MIm. exact (fmt_rdA m FMT_HDR_A fb_hdr 0 32 (fb_hdr_at m MIm) eq_refl). }
  intros q' m x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x25 x26 x28 x29 x30 x31 INV MUF WMF FKF.
  pose proof (vinv_qb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as QB.
  pose proof (vaP_pro q lo S MB A len cap cur0 bs st _ m0 G P1 m VOK RF0 PIN GLO GHI (conj GC (conj SHG SHP)) MUF WMF FKF) as VA.
  pose proof (out_pro q lo S MB A len cap cur0 bs st _ m0 P1 _ _ m VOK PIN PC1 WMF FKF) as PC.
  clear GC SHG SHP PC1 MUF WMF FKF.
  pose proof (carried_vaP1 q lo S MB A len cap cur0 bs st m0 q' G P1 pw1 pw2 VOK RF0 QB GLO) as CAR. fold R in CAR.
  assert (F0' : 0 <= FMT_HDR_A) by lia. assert (FH' : FMT_HDR_A + 8 < 2^62) by lia.
  pose proof (SPk q lo S MB A len cap cur0 bs st _ FMT_HDR_A 8 fb_hdr ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 _ R q' VOK RF0 fb_hdr_at eq_refl RFR XERR F0' FH') as SPK.
  pose proof (LITk q lo S MB A len cap cur0 bs st _ FMT_HDR_A 8 fb_hdr ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 _ R q' VOK RF0 fb_hdr_at eq_refl RFR XERR F0' FH') as LITK.
  pose proof (CONTk q lo S MB A len cap cur0 bs st _ FMT_HDR_A 8 fb_hdr ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 _ R q' VOK RF0 fb_hdr_at eq_refl RFR XERR) as CONTK.
  pose proof (ERRk q lo S MB A len cap cur0 bs st _ FMT_HDR_A 8 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 _ R q' VOK RF0 RFR XERR) as ERRK.

  change FMT_HDR_A with (FMT_HDR_A + Z.of_nat 0) at 1.
  eapply (SPK _ 0%nat 58); [exact CAR| exact INV| exact (conj VA PC)| reflexivity| lia|].
  intros cur2 m2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV2 [VA2 PC2] CU2.
  eapply (LITK _ 1%nat 58 32); [exact CAR| exact INV2| exact (conj VA2 PC2)| reflexivity| lia| lia| lia| lia| lia| lia|].
  intros m3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV3 [VA3 PC3].
  eapply (SPK _ 2%nat 37); [exact CAR| exact INV3| exact (conj VA3 PC3)| reflexivity| lia|].
  intros cur4 m4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV4 [VA4 PC4] CU4.

  destruct VA4 as (GC4 & SHG4 & SHP4).
  eapply (dir_RV IC FI) with (b2 := Z_to_bv 8 82) (P := P1).
  3: exact INV4. 1: exact VOK. 1: exact RF0.
  1: { eapply vinv_fmt_acc; [exact INV4| lia]. }
  1: { exact (fmt_rdA m4 FMT_HDR_A fb_hdr 4 82 (fb_hdr_at m4 (vinv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV4)) eq_refl). }
  1: reflexivity. 1: lia. 1: exact GC4. 1: exact SHG4. 1: exact GLO. 1: exact GHI. 1: exact GAL. 1: exact PC4. 1: exact SHP4. 1: exact PIN. 1: exact PAL.
  unfold KRt. intros r5 cur5 pa5 pb5 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m5 INV5 MU5 WM5 RR5 PC5 X5.
  eapply (CONTK 5%nat 37); [exact INV5| reflexivity| lia| lia| lia| exact RR5| exists pa5, pb5; exact PC5|].
  intros E5. intros. destruct (X5 E5) as (l5 & -> & -> & L0 & L1 & L2 & L3).

  eapply (dir_cV IC FI) with (b2 := Z_to_bv 8 99).
  3: exact INV5. 1: exact VOK. 1: exact RF0.
  1: { eapply vinv_fmt_acc; [exact INV5| lia]. }
  1: { exact (fmt_rdA m5 FMT_HDR_A fb_hdr 6 99 (fb_hdr_at m5 (vinv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV5)) eq_refl). }
  1: reflexivity. 1: lia.
  - intros r6 cur6 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m6 INV6 MU6 WM6 RR6 X6.
    pose proof (out_step0 q lo S MB A len cap cur0 bs st _ m0 q' P1 _ _ m5 m6 VOK RF0 PIN PC5 MU6 WM6) as PC6.
    eapply (contV FI) with (c := 0) (b := Z_to_bv 8 0).
    + eapply vinv_fmt_acc; [exact INV6| lia].
    + exact (fmt_rdA m6 FMT_HDR_A fb_hdr 7 0 (fb_hdr_at m6 (vinv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV6)) eq_refl).
    + reflexivity.
    + lia.
    + exact RR6.
    + intros _ C. exfalso. apply C. reflexivity.
    + intros -> _. intros. specialize (X6 eq_refl).
      pose proof (vinv_cur _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV6) as CR6.
      eapply evt_mono.
      * eapply (epiV FI) with (R := fun mm => rw_cells asegs mm P1 [C8 (wz (A + cur4)); C8 (wz l5)])
                             (XP := fun r c => r = 4 -> cur0 + 1 <= c /\ cur4 + l5 + 1 <= c);
          [exact VOK| exact RF0| exact INV6| lia| intros _; lia| intros C; exfalso; apply C; reflexivity| exact PC6
          | eapply out_rframe_c; [exact VOK| exact RF0| exact PIN]| intros _; lia].
      * intros ms V. eapply vpostA_mono; [exact V|]. cbn beta. intros mm rr cc [HRm HXP].
        exists (wz (A + cur4)), (wz l5). split; [exact HRm|]. intros E. destruct (HXP E) as [H1 H2].
        exists cur4, l5. repeat split; try reflexivity; lia.
    + intros RN. intros. eapply ERRK; [exact INV6| exact RR6| exact RN| eexists; eexists; exact PC6].
  - intros r6 cur6 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m6 INV6 MU6 WM6 RR6 RN6.
    pose proof (out_step0 q lo S MB A len cap cur0 bs st _ m0 q' P1 _ _ m5 m6 VOK RF0 PIN PC5 MU6 WM6) as PC6.
    eapply ERRK; [exact INV6| exact RR6| exact RN6| eexists; eexists; exact PC6].
Qed.

#[using="Type"] Lemma out_stepP : forall q lo S MB A len cap cur0 bs st Wx m0 q' P P' (pa pb : word) m m',
  vf_okA FI q lo S MB A len cap cur0 bs st Wx -> RFAKE FI st m0 -> In (P', P' + 16) Wx ->
  (P + 16 <= P' \/ P' + 16 <= P) ->
  rw_cells asegs m P' [C8 pa; C8 pb] -> munch (vWP lo S q' [(P, P + 16)]) m m' -> wmono asegs m m' -> rw_cells asegs m' P' [C8 pa; C8 pb].
Proof.
  intros q lo S MB A len cap cur0 bs st Wx m0 q' P P' pa pb m m' VOK RF0 PIN AP PC MU WM.
  destruct (out_facts FI q lo S MB A len cap cur0 bs st Wx m0 VOK RF0 P' 16 PIN ltac:(lia) ltac:(left; lia)) as (PLO & PHI & PPAR & PTXT).
  pose proof VOK as VOK'. destruct VOK' as (CLO & LO & _ & QHI & MBLO & MBS & _).
  eapply rw_cells_transport; [exact PC| exact MU| exact WM|]. unfold vWP. cbn [disjoint_from]. simpl_sizes. split; [left; lia|]. split; [lia|]. split; [lia| exact I].
Qed.

Notation FMT_REQ09_A := 0x21a80%Z.
Definition fb_req09 : list byte := map (Z_to_bv 8) [37; 115; 9; 37; 83; 37; 119; 37; 99; 0].
#[using="Type"] Lemma fb_req09_at : forall m, mem_inv asegs m -> bytes_at asegs m FMT_REQ09_A fb_req09.
Proof.
  intros m MI. pose proof (ro_cells_image asegs m FMT_REQ09_A fb_req09 MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO.
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Definition X_req09A (A len cur0 : Z) (P1 P2 : Z) : mem -> Z -> Z -> Prop := fun m' r cur' =>
  exists pa pb pc pd, rw_cells asegs m' P1 [C8 pa; C8 pb] /\ rw_cells asegs m' P2 [C8 pc; C8 pd]
    /\ (r = 4 -> exists o1 l1 o2 l2, pa = wz (A + o1) /\ pb = wz l1 /\ pc = wz (A + o2) /\ pd = wz l2
          /\ cur0 <= o1 /\ 1 <= l1 /\ o1 + l1 < o2 /\ 1 <= l2 /\ o2 + l2 < len /\ o2 + l2 < cur' /\ cur' <= len).

#[using="IC STACK_MALLOC_1"] Theorem vf_req09A : forall (q lo S MB A len cap cur0 : Z) (bs : list byte) (st : fsstate FI) (G P1 P2 : Z) (pw1 pw2 pw3 pw4 : word)
    ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F_ : bvmap 5 word) fc m0,
  vf_okA FI q lo S MB A len cap cur0 bs st [(P1, P1 + 16); (P2, P2 + 16)] -> RFAKE FI st m0 -> fs_call_ok FI st tp 1 -> FSENV FI m0 ->
  stk asegs m0 lo q ->
  rw_cells asegs m0 S [C8 (wz MB); C8 (wz cur0); C4 (wz 0)] -> rw_cells asegs m0 MB (mbuf_cells A len cap) -> bytes_at asegs m0 A bs ->
  mem_inv asegs m0 -> asan_env asegs m0 ->
  shw m0 S 24 -> shw m0 MB 32 -> (0 < len -> shw m0 A len) -> shw m0 SEPTAB_A 20 -> shw m0 FMT_REQ09_A 10 ->
  shz m0 (sh lo) (sh q) ->
  rw_cells asegs m0 G [C8 (wz P1)] -> shw m0 G 8 -> rw_cells asegs m0 (G + 8) [C8 (wz P2)] -> shw m0 (G + 8) 8 ->
  q <= G -> G + 16 <= 2^47 -> G mod 8 = 0 ->
  rw_cells asegs m0 P1 [C8 pw1; C8 pw2] -> shw m0 P1 16 -> P1 mod 8 = 0 ->
  rw_cells asegs m0 P2 [C8 pw3; C8 pw4] -> shw m0 P2 16 -> P2 mod 8 = 0 ->
  (P1 + 16 <= P2 \/ P2 + 16 <= P1) ->
  evt asegs (vpostA FI q lo S MB A len cap cur0 bs st [(P1, P1 + 16); (P2, P2 + 16)] ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 (X_req09A A len cur0 P1 P2))
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz S) (wz FMT_REQ09_A) (wz G) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz vfmatch_entryA) fc None m0 (seg_rom asegs)).
Proof.
  intros until m0. intros VOK RF0 FCO FE0 ST SC MBC BUF MI AE SHS SHMB SHA SHSEP SHFMT SHZ GC1 SHG1 GC2 SHG2 GLO GHI GAL PC1 SHP1 PAL1 PC2 SHP2 PAL2 AP12.
  assert (PIN1 : In (P1, P1 + 16) [(P1, P1 + 16); (P2, P2 + 16)]) by (left; reflexivity).
  assert (PIN2 : In (P2, P2 + 16) [(P1, P1 + 16); (P2, P2 + 16)]) by (right; left; reflexivity).
  assert (SUBP1 : forall iv : ivl, In iv [(P1, P1 + 16)] -> In iv [(P1, P1 + 16); (P2, P2 + 16)]) by (intros iv [<-|[]]; exact PIN1).
  assert (SUBP2 : forall iv : ivl, In iv [(P2, P2 + 16)] -> In iv [(P1, P1 + 16); (P2, P2 + 16)]) by (intros iv [<-|[]]; exact PIN2).
  assert (SUB0 : forall iv : ivl, In iv [] -> In iv [(P1, P1 + 16); (P2, P2 + 16)]) by (intros iv []).
  pose (R := fun mm : mem => (exists pa pb, rw_cells asegs mm P1 [C8 pa; C8 pb]) /\ (exists pc pd, rw_cells asegs mm P2 [C8 pc; C8 pd])).
  assert (RFR : rframeA FI q lo S st R).
  { apply rframeA_and; eapply out_rframe; [exact VOK| exact RF0| exact PIN1| exact VOK| exact RF0| exact PIN2]. }
  assert (XERR : forall mm rr cc, R mm -> rr <> 4 -> X_req09A A len cur0 P1 P2 mm rr cc).
  { intros mm rr cc [(pa & pb & H1) (pc & pd & H2)] RN. exists pa, pb, pc, pd. split; [exact H1|]. split; [exact H2| intros E; exfalso; exact (RN E)]. }
  eapply (prologueV FI STACK_MALLOC_1) with (FMT := FMT_REQ09_A) (flen := 10) (c0 := 37) (b0 := Z_to_bv 8 37); try eassumption; try reflexivity; try lia.
  { intros m MIm. exact (fmt_rdA m FMT_REQ09_A fb_req09 0 37 (fb_req09_at m MIm) eq_refl). }
  intros q' m x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x25 x26 x28 x29 x30 x31 INV MUF WMF FKF.
  pose proof (vinv_qb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as QB.
  pose proof (vaP_pro q lo S MB A len cap cur0 bs st _ m0 G P1 m VOK RF0 PIN1 GLO ltac:(lia) (conj GC1 (conj SHG1 SHP1)) MUF WMF FKF) as VA1.
  pose proof (vaP_pro q lo S MB A len cap cur0 bs st _ m0 (G + 8) P2 m VOK RF0 PIN2 ltac:(lia) ltac:(lia) (conj GC2 (conj SHG2 SHP2)) MUF WMF FKF) as VA2.
  pose proof (out_pro q lo S MB A len cap cur0 bs st _ m0 P1 _ _ m VOK PIN1 PC1 WMF FKF) as PCa.
  pose proof (out_pro q lo S MB A len cap cur0 bs st _ m0 P2 _ _ m VOK PIN2 PC2 WMF FKF) as PCb.
  clear GC1 SHG1 SHP1 PC1 GC2 SHG2 SHP2 PC2 MUF WMF FKF.
  assert (F0' : 0 <= FMT_REQ09_A) by lia. assert (FH' : FMT_REQ09_A + 10 < 2^62) by lia.
  pose proof (TABk q lo S MB A len cap cur0 bs st _ FMT_REQ09_A 10 fb_req09 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 _ R q' VOK RF0 fb_req09_at eq_refl RFR XERR F0' FH') as TABK.
  pose proof (WKk q lo S MB A len cap cur0 bs st _ FMT_REQ09_A 10 fb_req09 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 _ R q' VOK RF0 fb_req09_at eq_refl RFR XERR F0' FH') as WKK.
  pose proof (CONTk q lo S MB A len cap cur0 bs st _ FMT_REQ09_A 10 fb_req09 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 _ R q' VOK RF0 fb_req09_at eq_refl RFR XERR) as CONTK.
  pose proof (ERRk q lo S MB A len cap cur0 bs st _ FMT_REQ09_A 10 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 _ R q' VOK RF0 RFR XERR) as ERRK.

  destruct VA1 as (GCa & SHGa & SHPa).
  eapply (dir_sV IC FI) with (b2 := Z_to_bv 8 115) (P := P1).
  3: exact INV. 1: exact VOK. 1: exact RF0.
  1: { eapply vinv_fmt_acc; [exact INV| lia]. }
  1: { exact (fmt_rdA m FMT_REQ09_A fb_req09 1 115 (fb_req09_at m (vinv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV)) eq_refl). }
  1: reflexivity. 1: lia. 1: exact GCa. 1: exact SHGa. 1: exact GLO. 1: lia. 1: exact GAL. 1: exact PCa. 1: exact SHPa. 1: exact PIN1. 1: exact PAL1.

  2: {
    intros r1 cur1 pa1 pb1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m1 INV1 MU1 WM1 RR1 RN1 PC1.
    pose proof (out_stepP q lo S MB A len cap cur0 bs st _ m0 q' P1 P2 _ _ m m1 VOK RF0 PIN2 AP12 PCb MU1 WM1) as PCb1.
    eapply ERRK; [exact INV1| exact RR1| exact RN1| split; [exists pa1, pb1; exact PC1| eexists; eexists; exact PCb1]]. }
  intros r1 cur1 pa1 pb1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m1 INV1 MU1 WM1 RR1 PC1 X1.
  pose proof (out_stepP q lo S MB A len cap cur0 bs st _ m0 q' P1 P2 _ _ m m1 VOK RF0 PIN2 AP12 PCb MU1 WM1) as PCb1.
  pose proof (vaP_step q lo S MB A len cap cur0 bs st _ m0 q' [(P1, P1 + 16)] (G + 8) P2 m m1 VOK RF0 SUBP1 QB ltac:(lia) VA2 MU1 WM1) as VA2'.
  eapply (CONTK 2%nat 9); [exact INV1| reflexivity| lia| lia| lia| exact RR1| split; [exists pa1, pb1; exact PC1| eexists; eexists; exact PCb1]|].
  intros E1. intros. destruct (X1 E1) as (l1 & -> & -> & L1 & -> & CL1).

  pose (C1 := fun mm : mem => vaP (G + 8) P2 mm /\ rw_cells asegs mm P1 [C8 (wz (A + cur0)); C8 (wz l1)] /\ rw_cells asegs mm P2 [C8 pw3; C8 pw4]).
  assert (CAR1 : carried lo S R q' C1).
  { split.
    - intros mm (_ & H1 & H2). split; [eexists; eexists; exact H1| eexists; eexists; exact H2].
    - intros mm mm' (V & H1 & H2) MU WM. split; [| split].
      + exact (vaP_step q lo S MB A len cap cur0 bs st _ m0 q' [] (G + 8) P2 mm mm' VOK RF0 SUB0 QB ltac:(lia) V MU WM).
      + exact (out_step0 q lo S MB A len cap cur0 bs st _ m0 q' P1 _ _ mm mm' VOK RF0 PIN1 H1 MU WM).
      + exact (out_step0 q lo S MB A len cap cur0 bs st _ m0 q' P2 _ _ mm mm' VOK RF0 PIN2 H2 MU WM). }
  eapply (TABK C1 2%nat 37); [exact CAR1| exact INV1| exact (conj VA2' (conj PC1 PCb1))| reflexivity| lia|].
  intros cur2 m2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV2 (VA2'' & PC1_2 & PC2_2) CU2.

  destruct VA2'' as (GCb & SHGb & SHPb).
  eapply (dir_SV IC FI) with (b2 := Z_to_bv 8 83) (P := P2).
  3: exact INV2. 1: exact VOK. 1: exact RF0.
  1: { eapply vinv_fmt_acc; [exact INV2| lia]. }
  1: { exact (fmt_rdA m2 FMT_REQ09_A fb_req09 4 83 (fb_req09_at m2 (vinv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV2)) eq_refl). }
  1: reflexivity. 1: lia. 1: exact GCb. 1: exact SHGb. 1: lia. 1: lia. 1: { clear - GAL. Z.div_mod_to_equations. lia. } 1: exact PC2_2. 1: exact SHPb. 1: exact PIN2. 1: exact PAL2.
  intros r3 cur3 pc3 pd3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m3 INV3 MU3 WM3 RR3 PC2_3 X3.
  assert (AP21 : P2 + 16 <= P1 \/ P1 + 16 <= P2) by (clear - AP12; lia).
  pose proof (out_stepP q lo S MB A len cap cur0 bs st _ m0 q' P2 P1 _ _ m2 m3 VOK RF0 PIN1 AP21 PC1_2 MU3 WM3) as PC1_3.
  eapply (CONTK 5%nat 37); [exact INV3| reflexivity| lia| lia| lia| exact RR3| split; [eexists; eexists; exact PC1_3| exists pc3, pd3; exact PC2_3]|].
  intros E3. intros. destruct (X3 E3) as (l3 & -> & -> & L3 & -> & CL3).

  pose (C2 := fun mm : mem => rw_cells asegs mm P1 [C8 (wz (A + cur0)); C8 (wz l1)] /\ rw_cells asegs mm P2 [C8 (wz (A + cur2)); C8 (wz l3)]).
  assert (CAR2 : carried lo S R q' C2).
  { split.
    - intros mm (H1 & H2). split; [eexists; eexists; exact H1| eexists; eexists; exact H2].
    - intros mm mm' (H1 & H2) MU WM. split.
      + exact (out_step0 q lo S MB A len cap cur0 bs st _ m0 q' P1 _ _ mm mm' VOK RF0 PIN1 H1 MU WM).
      + exact (out_step0 q lo S MB A len cap cur0 bs st _ m0 q' P2 _ _ mm mm' VOK RF0 PIN2 H2 MU WM). }
  eapply (WKK C2 5%nat 37); [exact CAR2| exact INV3| exact (conj PC1_3 PC2_3)| reflexivity| reflexivity| lia|].
  intros cur4 m4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV4 (PC1_4 & PC2_4) CU4.

  eapply (dir_cV IC FI) with (b2 := Z_to_bv 8 99).
  3: exact INV4. 1: exact VOK. 1: exact RF0.
  1: { eapply vinv_fmt_acc; [exact INV4| lia]. }
  1: { exact (fmt_rdA m4 FMT_REQ09_A fb_req09 8 99 (fb_req09_at m4 (vinv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV4)) eq_refl). }
  1: reflexivity. 1: lia.
  - intros r5 cur5 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m5 INV5 MU5 WM5 RR5 X5.
    destruct CAR2 as [CR2 CS2]. destruct (CS2 m4 m5 (conj PC1_4 PC2_4) MU5 WM5) as (PC1_5 & PC2_5).
    eapply (contV FI) with (c := 0) (b := Z_to_bv 8 0).
    + eapply vinv_fmt_acc; [exact INV5| lia].
    + exact (fmt_rdA m5 FMT_REQ09_A fb_req09 9 0 (fb_req09_at m5 (vinv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV5)) eq_refl).
    + reflexivity.
    + lia.
    + exact RR5.
    + intros _ C. exfalso. apply C. reflexivity.
    + intros -> _. intros. specialize (X5 eq_refl).
      pose proof (vinv_cur _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV5) as CR5.
      eapply evt_mono.
      * eapply (epiV FI) with (R := fun mm => rw_cells asegs mm P1 [C8 (wz (A + cur0)); C8 (wz l1)] /\ rw_cells asegs mm P2 [C8 (wz (A + cur2)); C8 (wz l3)])
                             (XP := fun r c => r = 4 -> cur2 + l3 < c /\ c <= len);
          [exact VOK| exact RF0| exact INV5| lia| intros _; lia| intros C; exfalso; apply C; reflexivity| exact (conj PC1_5 PC2_5)
          | apply rframeA_and; eapply out_rframe_c; [exact VOK| exact RF0| exact PIN1| exact VOK| exact RF0| exact PIN2]| intros _; lia].
      * intros ms V. eapply vpostA_mono; [exact V|]. cbn beta. intros mm rr cc [[HR1 HR2] HXP].
        exists (wz (A + cur0)), (wz l1), (wz (A + cur2)), (wz l3). split; [exact HR1|]. split; [exact HR2|]. intros E. destruct (HXP E) as [H1 H2].
        exists cur0, l1, cur2, l3. repeat split; try reflexivity; lia.
    + intros RN. intros. eapply ERRK; [exact INV5| exact RR5| exact RN| exact (CR2 _ (conj PC1_5 PC2_5))].
  - intros r5 cur5 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m5 INV5 MU5 WM5 RR5 RN5.
    destruct CAR2 as [CR2 CS2].
    eapply ERRK; [exact INV5| exact RR5| exact RN5| exact (CR2 _ (CS2 m4 m5 (conj PC1_4 PC2_4) MU5 WM5))].
Qed.

Notation FMT_REQ_A := 0x21aa0%Z.
Definition fb_req : list byte := map (Z_to_bv 8) [37; 115; 9; 37; 83; 9; 37; 105; 104; 116; 116; 112; 37; 119; 47; 37; 119; 37; 76; 37; 99; 0].
#[using="Type"] Lemma fb_req_at : forall m, mem_inv asegs m -> bytes_at asegs m FMT_REQ_A fb_req.
Proof.
  intros m MI. pose proof (ro_cells_image asegs m FMT_REQ_A fb_req MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO.
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Definition X_reqA (A len cur0 : Z) (bs : list byte) (P1 P2 P3 : Z) : mem -> Z -> Z -> Prop := fun m' r cur' =>
  exists pa pb pc pd pe pf, rw_cells asegs m' P1 [C8 pa; C8 pb] /\ rw_cells asegs m' P2 [C8 pc; C8 pd] /\ rw_cells asegs m' P3 [C8 pe; C8 pf]
    /\ (r = 4 -> exists o1 l1 o2 l2 o3 l3, pa = wz (A + o1) /\ pb = wz l1 /\ pc = wz (A + o2) /\ pd = wz l2 /\ pe = wz (A + o3) /\ pf = wz l3
          /\ cur0 <= o1 /\ 1 <= l1 /\ o1 + l1 < o2 /\ 1 <= l2 /\ o2 + l2 < o3 /\ 0 <= l3 /\ o3 + l3 < cur' /\ cur' <= len
          /\ exists b, nth_error bs (Z.to_nat (o3 + l3)) = Some b /\ (bv_unsigned b = 13 \/ bv_unsigned b = 10)).

#[using="IC STACK_MALLOC_1"] Theorem vf_reqA : forall (q lo S MB A len cap cur0 : Z) (bs : list byte) (st : fsstate FI) (G P1 P2 P3 : Z) (pw1 pw2 pw3 pw4 pw5 pw6 : word)
    ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F_ : bvmap 5 word) fc m0,
  vf_okA FI q lo S MB A len cap cur0 bs st [(P1, P1 + 16); (P2, P2 + 16); (P3, P3 + 16)] -> RFAKE FI st m0 -> fs_call_ok FI st tp 1 -> FSENV FI m0 ->
  stk asegs m0 lo q ->
  rw_cells asegs m0 S [C8 (wz MB); C8 (wz cur0); C4 (wz 0)] -> rw_cells asegs m0 MB (mbuf_cells A len cap) -> bytes_at asegs m0 A bs ->
  mem_inv asegs m0 -> asan_env asegs m0 ->
  shw m0 S 24 -> shw m0 MB 32 -> (0 < len -> shw m0 A len) -> shw m0 SEPTAB_A 20 -> shw m0 FMT_REQ_A 22 ->
  shz m0 (sh lo) (sh q) ->
  rw_cells asegs m0 G [C8 (wz P1)] -> shw m0 G 8 -> rw_cells asegs m0 (G + 8) [C8 (wz P2)] -> shw m0 (G + 8) 8 ->
  rw_cells asegs m0 (G + 16) [C8 (wz P3)] -> shw m0 (G + 16) 8 ->
  q <= G -> G + 24 <= 2^47 -> G mod 8 = 0 ->
  rw_cells asegs m0 P1 [C8 pw1; C8 pw2] -> shw m0 P1 16 -> P1 mod 8 = 0 ->
  rw_cells asegs m0 P2 [C8 pw3; C8 pw4] -> shw m0 P2 16 -> P2 mod 8 = 0 ->
  rw_cells asegs m0 P3 [C8 pw5; C8 pw6] -> shw m0 P3 16 -> P3 mod 8 = 0 ->
  (P1 + 16 <= P2 \/ P2 + 16 <= P1) -> (P1 + 16 <= P3 \/ P3 + 16 <= P1) -> (P2 + 16 <= P3 \/ P3 + 16 <= P2) ->
  evt asegs (vpostA FI q lo S MB A len cap cur0 bs st [(P1, P1 + 16); (P2, P2 + 16); (P3, P3 + 16)] ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 (X_reqA A len cur0 bs P1 P2 P3))
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz S) (wz FMT_REQ_A) (wz G) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz vfmatch_entryA) fc None m0 (seg_rom asegs)).
Proof.
  intros until m0. intros VOK RF0 FCO FE0 ST SC MBC BUF MI AE SHS SHMB SHA SHSEP SHFMT SHZ GC1 SHG1 GC2 SHG2 GC3 SHG3 GLO GHI GAL PC1 SHP1 PAL1 PC2 SHP2 PAL2 PC3 SHP3 PAL3 AP12 AP13 AP23.
  set (WX := [(P1, P1 + 16); (P2, P2 + 16); (P3, P3 + 16)]) in *.
  assert (PIN1 : In (P1, P1 + 16) WX) by (left; reflexivity).
  assert (PIN2 : In (P2, P2 + 16) WX) by (right; left; reflexivity).
  assert (PIN3 : In (P3, P3 + 16) WX) by (right; right; left; reflexivity).
  assert (SUBP1 : forall iv : ivl, In iv [(P1, P1 + 16)] -> In iv WX) by (intros iv [<-|[]]; exact PIN1).
  assert (SUBP2 : forall iv : ivl, In iv [(P2, P2 + 16)] -> In iv WX) by (intros iv [<-|[]]; exact PIN2).
  assert (SUB0 : forall iv : ivl, In iv [] -> In iv WX) by (intros iv []).
  pose (R := fun mm : mem => (exists pa pb, rw_cells asegs mm P1 [C8 pa; C8 pb]) /\ (exists pc pd, rw_cells asegs mm P2 [C8 pc; C8 pd]) /\ (exists pe pf, rw_cells asegs mm P3 [C8 pe; C8 pf])).
  assert (RFR : rframeA FI q lo S st R).
  { apply rframeA_and; [eapply out_rframe; [exact VOK| exact RF0| exact PIN1]|]. apply rframeA_and; eapply out_rframe; [exact VOK| exact RF0| exact PIN2| exact VOK| exact RF0| exact PIN3]. }
  assert (XERR : forall mm rr cc, R mm -> rr <> 4 -> X_reqA A len cur0 bs P1 P2 P3 mm rr cc).
  { intros mm rr cc [(pa & pb & H1) [(pc & pd & H2) (pe & pf & H3)]] RN. exists pa, pb, pc, pd, pe, pf. split; [exact H1|]. split; [exact H2|]. split; [exact H3| intros E; exfalso; exact (RN E)]. }
  eapply (prologueV FI STACK_MALLOC_1) with (FMT := FMT_REQ_A) (flen := 22) (c0 := 37) (b0 := Z_to_bv 8 37); try eassumption; try reflexivity; try lia.
  { intros m MIm. exact (fmt_rdA m FMT_REQ_A fb_req 0 37 (fb_req_at m MIm) eq_refl). }
  intros q' m x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x25 x26 x28 x29 x30 x31 INV MUF WMF FKF.
  pose proof (vinv_qb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as QB.
  pose proof (vaP_pro q lo S MB A len cap cur0 bs st _ m0 G P1 m VOK RF0 PIN1 GLO ltac:(lia) (conj GC1 (conj SHG1 SHP1)) MUF WMF FKF) as VA1.
  pose proof (vaP_pro q lo S MB A len cap cur0 bs st _ m0 (G + 8) P2 m VOK RF0 PIN2 ltac:(lia) ltac:(lia) (conj GC2 (conj SHG2 SHP2)) MUF WMF FKF) as VA2.
  pose proof (vaP_pro q lo S MB A len cap cur0 bs st _ m0 (G + 16) P3 m VOK RF0 PIN3 ltac:(lia) ltac:(lia) (conj GC3 (conj SHG3 SHP3)) MUF WMF FKF) as VA3.
  pose proof (out_pro q lo S MB A len cap cur0 bs st _ m0 P1 _ _ m VOK PIN1 PC1 WMF FKF) as PCa.
  pose proof (out_pro q lo S MB A len cap cur0 bs st _ m0 P2 _ _ m VOK PIN2 PC2 WMF FKF) as PCb.
  pose proof (out_pro q lo S MB A len cap cur0 bs st _ m0 P3 _ _ m VOK PIN3 PC3 WMF FKF) as PCc.
  clear GC1 SHG1 SHP1 PC1 GC2 SHG2 SHP2 PC2 GC3 SHG3 SHP3 PC3 MUF WMF FKF.
  assert (F0' : 0 <= FMT_REQ_A) by lia. assert (FH' : FMT_REQ_A + 22 < 2^62) by lia.
  pose proof (TABk q lo S MB A len cap cur0 bs st _ FMT_REQ_A 22 fb_req ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 _ R q' VOK RF0 fb_req_at eq_refl RFR XERR F0' FH') as TABK.
  pose proof (WKk q lo S MB A len cap cur0 bs st _ FMT_REQ_A 22 fb_req ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 _ R q' VOK RF0 fb_req_at eq_refl RFR XERR F0' FH') as WKK.
  pose proof (LITk q lo S MB A len cap cur0 bs st _ FMT_REQ_A 22 fb_req ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 _ R q' VOK RF0 fb_req_at eq_refl RFR XERR F0' FH') as LITK.
  pose proof (IKk q lo S MB A len cap cur0 bs st _ FMT_REQ_A 22 fb_req ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 _ R q' VOK RF0 fb_req_at eq_refl RFR XERR F0' FH') as IKK.
  pose proof (CONTk q lo S MB A len cap cur0 bs st _ FMT_REQ_A 22 fb_req ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 _ R q' VOK RF0 fb_req_at eq_refl RFR XERR) as CONTK.
  pose proof (ERRk q lo S MB A len cap cur0 bs st _ FMT_REQ_A 22 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 _ R q' VOK RF0 RFR XERR) as ERRK.

  destruct VA1 as (GCa & SHGa & SHPa).
  eapply (dir_sV IC FI) with (b2 := Z_to_bv 8 115) (P := P1).
  3: exact INV. 1: exact VOK. 1: exact RF0.
  1: { eapply vinv_fmt_acc; [exact INV| lia]. }
  1: { exact (fmt_rdA m FMT_REQ_A fb_req 1 115 (fb_req_at m (vinv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV)) eq_refl). }
  1: reflexivity. 1: lia. 1: exact GCa. 1: exact SHGa. 1: exact GLO. 1: lia. 1: exact GAL. 1: exact PCa. 1: exact SHPa. 1: exact PIN1. 1: exact PAL1.
  2: { intros r1 cur1 pa1 pb1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m1 INV1 MU1 WM1 RR1 RN1 PC1.
    pose proof (out_stepP q lo S MB A len cap cur0 bs st _ m0 q' P1 P2 _ _ m m1 VOK RF0 PIN2 AP12 PCb MU1 WM1) as PCb1.
    pose proof (out_stepP q lo S MB A len cap cur0 bs st _ m0 q' P1 P3 _ _ m m1 VOK RF0 PIN3 AP13 PCc MU1 WM1) as PCc1.
    eapply ERRK; [exact INV1| exact RR1| exact RN1| split; [exists pa1, pb1; exact PC1| split; [eexists; eexists; exact PCb1| eexists; eexists; exact PCc1]]]. }
  intros r1 cur1 pa1 pb1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m1 INV1 MU1 WM1 RR1 PC1 X1.
  pose proof (out_stepP q lo S MB A len cap cur0 bs st _ m0 q' P1 P2 _ _ m m1 VOK RF0 PIN2 AP12 PCb MU1 WM1) as PCb1.
  pose proof (out_stepP q lo S MB A len cap cur0 bs st _ m0 q' P1 P3 _ _ m m1 VOK RF0 PIN3 AP13 PCc MU1 WM1) as PCc1.
  pose proof (vaP_step q lo S MB A len cap cur0 bs st _ m0 q' [(P1, P1 + 16)] (G + 8) P2 m m1 VOK RF0 SUBP1 QB ltac:(lia) VA2 MU1 WM1) as VA2'.
  pose proof (vaP_step q lo S MB A len cap cur0 bs st _ m0 q' [(P1, P1 + 16)] (G + 16) P3 m m1 VOK RF0 SUBP1 QB ltac:(lia) VA3 MU1 WM1) as VA3'.
  eapply (CONTK 2%nat 9); [exact INV1| reflexivity| lia| lia| lia| exact RR1| split; [exists pa1, pb1; exact PC1| split; [eexists; eexists; exact PCb1| eexists; eexists; exact PCc1]]|].
  intros E1. intros. destruct (X1 E1) as (l1 & -> & -> & L1 & -> & CL1).

  pose (C1 := fun mm : mem => vaP (G + 8) P2 mm /\ vaP (G + 16) P3 mm /\ rw_cells asegs mm P1 [C8 (wz (A + cur0)); C8 (wz l1)]
                               /\ rw_cells asegs mm P2 [C8 pw3; C8 pw4] /\ rw_cells asegs mm P3 [C8 pw5; C8 pw6]).
  assert (CAR1 : carried lo S R q' C1).
  { split.
    - intros mm (_ & _ & H1 & H2 & H3). split; [eexists; eexists; exact H1| split; [eexists; eexists; exact H2| eexists; eexists; exact H3]].
    - intros mm mm' (V2 & V3 & H1 & H2 & H3) MU WM. split; [| split; [| split; [| split]]].
      + exact (vaP_step q lo S MB A len cap cur0 bs st _ m0 q' [] (G + 8) P2 mm mm' VOK RF0 SUB0 QB ltac:(lia) V2 MU WM).
      + exact (vaP_step q lo S MB A len cap cur0 bs st _ m0 q' [] (G + 16) P3 mm mm' VOK RF0 SUB0 QB ltac:(lia) V3 MU WM).
      + exact (out_step0 q lo S MB A len cap cur0 bs st _ m0 q' P1 _ _ mm mm' VOK RF0 PIN1 H1 MU WM).
      + exact (out_step0 q lo S MB A len cap cur0 bs st _ m0 q' P2 _ _ mm mm' VOK RF0 PIN2 H2 MU WM).
      + exact (out_step0 q lo S MB A len cap cur0 bs st _ m0 q' P3 _ _ mm mm' VOK RF0 PIN3 H3 MU WM). }
  eapply (TABK C1 2%nat 37); [exact CAR1| exact INV1| exact (conj VA2' (conj VA3' (conj PC1 (conj PCb1 PCc1))))| reflexivity| lia|].
  intros cur2 m2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV2 (VA2'' & VA3'' & PC1_2 & PC2_2 & PC3_2) CU2.

  destruct VA2'' as (GCb & SHGb & SHPb).
  eapply (dir_SV IC FI) with (b2 := Z_to_bv 8 83) (P := P2).
  3: exact INV2. 1: exact VOK. 1: exact RF0.
  1: { eapply vinv_fmt_acc; [exact INV2| lia]. }
  1: { exact (fmt_rdA m2 FMT_REQ_A fb_req 4 83 (fb_req_at m2 (vinv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV2)) eq_refl). }
  1: reflexivity. 1: lia. 1: exact GCb. 1: exact SHGb. 1: lia. 1: lia. 1: { clear - GAL. Z.div_mod_to_equations. lia. } 1: exact PC2_2. 1: exact SHPb. 1: exact PIN2. 1: exact PAL2.
  intros r3 cur3 pc3 pd3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m3 INV3 MU3 WM3 RR3 PC2_3 X3.
  assert (AP21 : P2 + 16 <= P1 \/ P1 + 16 <= P2) by (clear - AP12; lia).
  pose proof (out_stepP q lo S MB A len cap cur0 bs st _ m0 q' P2 P1 _ _ m2 m3 VOK RF0 PIN1 AP21 PC1_2 MU3 WM3) as PC1_3.
  pose proof (out_stepP q lo S MB A len cap cur0 bs st _ m0 q' P2 P3 _ _ m2 m3 VOK RF0 PIN3 AP23 PC3_2 MU3 WM3) as PC3_3.
  pose proof (vaP_step q lo S MB A len cap cur0 bs st _ m0 q' [(P2, P2 + 16)] (G + 16) P3 m2 m3 VOK RF0 SUBP2 QB ltac:(lia) VA3'' MU3 WM3) as VA3_3.
  eapply (CONTK 5%nat 9); [exact INV3| reflexivity| lia| lia| lia| exact RR3| split; [eexists; eexists; exact PC1_3| split; [exists pc3, pd3; exact PC2_3| eexists; eexists; exact PC3_3]]|].
  intros E3. intros. destruct (X3 E3) as (l3 & -> & -> & L3 & -> & CL3).

  pose (C2 := fun mm : mem => vaP (G + 16) P3 mm /\ rw_cells asegs mm P1 [C8 (wz (A + cur0)); C8 (wz l1)]
                               /\ rw_cells asegs mm P2 [C8 (wz (A + cur2)); C8 (wz l3)] /\ rw_cells asegs mm P3 [C8 pw5; C8 pw6]).
  assert (CAR2 : carried lo S R q' C2).
  { split.
    - intros mm (_ & H1 & H2 & H3). split; [eexists; eexists; exact H1| split; [eexists; eexists; exact H2| eexists; eexists; exact H3]].
    - intros mm mm' (V3 & H1 & H2 & H3) MU WM. split; [| split; [| split]].
      + exact (vaP_step q lo S MB A len cap cur0 bs st _ m0 q' [] (G + 16) P3 mm mm' VOK RF0 SUB0 QB ltac:(lia) V3 MU WM).
      + exact (out_step0 q lo S MB A len cap cur0 bs st _ m0 q' P1 _ _ mm mm' VOK RF0 PIN1 H1 MU WM).
      + exact (out_step0 q lo S MB A len cap cur0 bs st _ m0 q' P2 _ _ mm mm' VOK RF0 PIN2 H2 MU WM).
      + exact (out_step0 q lo S MB A len cap cur0 bs st _ m0 q' P3 _ _ mm mm' VOK RF0 PIN3 H3 MU WM). }
  eapply (TABK C2 5%nat 37); [exact CAR2| exact INV3| exact (conj VA3_3 (conj PC1_3 (conj PC2_3 PC3_3)))| reflexivity| lia|].
  intros cur4 m4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV4 HC4 CU4.
  eapply (IKK C2 6%nat 104); [exact CAR2| exact INV4| exact HC4| reflexivity| reflexivity| lia|].
  intros m5 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV5 HC5.
  eapply (LITK C2 8%nat 104 116); [exact CAR2| exact INV5| exact HC5| reflexivity| lia| lia| lia| lia| lia| lia|]. intros m6 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV6 HC6.
  eapply (LITK C2 9%nat 116 116); [exact CAR2| exact INV6| exact HC6| reflexivity| lia| lia| lia| lia| lia| lia|]. intros m7 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV7 HC7.
  eapply (LITK C2 10%nat 116 112); [exact CAR2| exact INV7| exact HC7| reflexivity| lia| lia| lia| lia| lia| lia|]. intros m8 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV8 HC8.
  eapply (LITK C2 11%nat 112 37); [exact CAR2| exact INV8| exact HC8| reflexivity| lia| lia| lia| lia| lia| lia|]. intros m9 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV9 HC9.
  eapply (WKK C2 12%nat 47); [exact CAR2| exact INV9| exact HC9| reflexivity| reflexivity| lia|]. intros cur10 m10 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV10 HC10 CU10.
  eapply (LITK C2 14%nat 47 37); [exact CAR2| exact INV10| exact HC10| reflexivity| lia| lia| lia| lia| lia| lia|]. intros m11 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV11 HC11.
  eapply (WKK C2 15%nat 37); [exact CAR2| exact INV11| exact HC11| reflexivity| reflexivity| lia|]. intros cur12 m12 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV12 (VA3_12 & PC1_12 & PC2_12 & PC3_12) CU12.

  destruct VA3_12 as (GCc & SHGc & SHPc).
  replace (G + 8 + 8) with (G + 16) in INV12 by lia.
  eapply (dir_LV IC FI) with (b2 := Z_to_bv 8 76) (P := P3).
  3: exact INV12. 1: exact VOK. 1: exact RF0.
  1: { eapply vinv_fmt_acc; [exact INV12| lia]. }
  1: { exact (fmt_rdA m12 FMT_REQ_A fb_req 18 76 (fb_req_at m12 (vinv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV12)) eq_refl). }
  1: reflexivity. 1: lia. 1: exact GCc. 1: exact SHGc. 1: lia. 1: lia. 1: { clear - GAL. Z.div_mod_to_equations. lia. } 1: exact PC3_12. 1: exact SHPc. 1: exact PIN3. 1: exact PAL3.
  intros r13 cur13 pb13 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m13 INV13 MU13 WM13 RR13 PC3_13 X13.
  assert (AP31 : P3 + 16 <= P1 \/ P1 + 16 <= P3) by (clear - AP13; lia).
  assert (AP32 : P3 + 16 <= P2 \/ P2 + 16 <= P3) by (clear - AP23; lia).
  pose proof (out_stepP q lo S MB A len cap cur0 bs st _ m0 q' P3 P1 _ _ m12 m13 VOK RF0 PIN1 AP31 PC1_12 MU13 WM13) as PC1_13.
  pose proof (out_stepP q lo S MB A len cap cur0 bs st _ m0 q' P3 P2 _ _ m12 m13 VOK RF0 PIN2 AP32 PC2_12 MU13 WM13) as PC2_13.
  eapply (CONTK 19%nat 37); [exact INV13| reflexivity| lia| lia| lia| exact RR13| split; [eexists; eexists; exact PC1_13| split; [eexists; eexists; exact PC2_13| eexists; eexists; exact PC3_13]]|].
  intros E13. intros. destruct (X13 E13) as (l13 & -> & L13 & -> & CL13 & BY13).

  pose (C3 := fun mm : mem => rw_cells asegs mm P1 [C8 (wz (A + cur0)); C8 (wz l1)] /\ rw_cells asegs mm P2 [C8 (wz (A + cur2)); C8 (wz l3)]
                               /\ rw_cells asegs mm P3 [C8 (wz (A + cur12)); C8 (wz l13)]).
  assert (CS3 : forall mm mm', C3 mm -> munch (vWP lo S q' []) mm mm' -> wmono asegs mm mm' -> C3 mm').
  { intros mm mm' (H1 & H2 & H3) MU WM. split; [| split].
    - exact (out_step0 q lo S MB A len cap cur0 bs st _ m0 q' P1 _ _ mm mm' VOK RF0 PIN1 H1 MU WM).
    - exact (out_step0 q lo S MB A len cap cur0 bs st _ m0 q' P2 _ _ mm mm' VOK RF0 PIN2 H2 MU WM).
    - exact (out_step0 q lo S MB A len cap cur0 bs st _ m0 q' P3 _ _ mm mm' VOK RF0 PIN3 H3 MU WM). }
  assert (CR3 : forall mm, C3 mm -> R mm).
  { intros mm (H1 & H2 & H3). split; [eexists; eexists; exact H1| split; [eexists; eexists; exact H2| eexists; eexists; exact H3]]. }
  eapply (dir_cV IC FI) with (b2 := Z_to_bv 8 99).
  3: exact INV13. 1: exact VOK. 1: exact RF0.
  1: { eapply vinv_fmt_acc; [exact INV13| lia]. }
  1: { exact (fmt_rdA m13 FMT_REQ_A fb_req 20 99 (fb_req_at m13 (vinv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV13)) eq_refl). }
  1: reflexivity. 1: lia.
  - intros r14 cur14 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m14 INV14 MU14 WM14 RR14 X14.
    pose proof (CS3 m13 m14 (conj PC1_13 (conj PC2_13 PC3_13)) MU14 WM14) as HC14.
    eapply (contV FI) with (c := 0) (b := Z_to_bv 8 0).
    + eapply vinv_fmt_acc; [exact INV14| lia].
    + exact (fmt_rdA m14 FMT_REQ_A fb_req 21 0 (fb_req_at m14 (vinv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV14)) eq_refl).
    + reflexivity.
    + lia.
    + exact RR14.
    + intros _ C. exfalso. apply C. reflexivity.
    + intros -> _. intros. specialize (X14 eq_refl).
      pose proof (vinv_cur _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV14) as CR14.
      eapply evt_mono.
      * eapply (epiV FI) with (R := C3) (XP := fun r c => r = 4 -> cur12 + l13 < c /\ c <= len);
          [exact VOK| exact RF0| exact INV14| lia| intros _; lia| intros C; exfalso; apply C; reflexivity| exact HC14
          | unfold C3; apply rframeA_and; [eapply out_rframe_c; [exact VOK| exact RF0| exact PIN1]|]; apply rframeA_and; eapply out_rframe_c; [exact VOK| exact RF0| exact PIN2| exact VOK| exact RF0| exact PIN3]
          | intros _; lia].
      * intros ms V. eapply vpostA_mono; [exact V|]. cbn beta. intros mm rr cc [(HR1 & HR2 & HR3) HXP].
        exists (wz (A + cur0)), (wz l1), (wz (A + cur2)), (wz l3), (wz (A + cur12)), (wz l13). split; [exact HR1|]. split; [exact HR2|]. split; [exact HR3|].
        intros E. destruct (HXP E) as [H1 H2].
        exists cur0, l1, cur2, l3, cur12, l13. repeat split; try reflexivity; try lia. exact BY13.
    + intros RN. intros. eapply ERRK; [exact INV14| exact RR14| exact RN| exact (CR3 _ HC14)].
  - intros r14 cur14 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m14 INV14 MU14 WM14 RR14 RN14.
    eapply ERRK; [exact INV14| exact RR14| exact RN14| exact (CR3 _ (CS3 m13 m14 (conj PC1_13 (conj PC2_13 PC3_13)) MU14 WM14))].
Qed.

End G.
