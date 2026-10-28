(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim Canon Stdio.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_iface D_defs D_kit X_aexdefs D_aex D_libiface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma outside_of_not_in_ranges' : forall W x, ~ in_ranges W x -> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x H; [exact I|]. cbn [outside]. split.
  - intros Hx. apply H. exists lo, hi. split; [left; reflexivity| exact Hx].
  - apply IH. intros (l & h & Hin & Hx). apply H. exists l, h. split; [right; exact Hin| exact Hx].
Qed.

Lemma not_in_ranges_of_outside : forall W x, outside W x -> ~ in_ranges W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x H (l & h & Hin & Hx); [destruct Hin|].
  cbn [outside] in H. destruct H as [H1 H2]. destruct Hin as [E|Hin]; [injection E as <- <-; exact (H1 Hx)|].
  exact (IH x H2 (ex_intro _ l (ex_intro _ h (conj Hin Hx)))).
Qed.

Lemma client_static_range : forall x, client_static x -> 0x10000 <= x < SEGTOP_A.
Proof.
  intros x ((lo & hi & Hin & Hx) & _). unfold CLIENT_STATIC in Hin. unfold SEGTOP_A.
  destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
Qed.

Lemma client_static_intro : forall x,
  (0x172c90 <= x < 0x1731c0)
  \/ (0x173280 <= x < 0x174558)
  \/ (0x69a210 <= x < 0x6aa210)
  \/ (0x6aa210 <= x < 0x6aa270)
  \/ (0x6aa2a0 <= x < 0x6aa2a8)
  \/ (0x6aa2c0 <= x < 0x6aa2c8)
  \/ (0x6aa2e0 <= x < 0x6aa2e8)
  \/ (0x6aa300 <= x < 0x6aa310)
  \/ (0x6aa320 <= x < 0x6aa328)
  \/ (0x6aa340 <= x < 0x6aa348)
  \/ (0x6aa360 <= x < 0x6aa390)
  \/ (0x6aa3c0 <= x < 0x6aa3c8)
  \/ (0x6aa3e0 <= x < 0x6abd90)
  \/ (0x6abd98 <= x < 0x6abde0)
  \/ (0x6abe00 <= x < 0x6abe08)
  \/ (0x6abe18 <= x < 0x6cc0a8)
  \/ (0x6cc0b0 <= x < 0x6cd2a0)
  \/ (0x6cd2a8 <= x < 0x6cd7d8) -> client_static x.
Proof.
  intros x Hx. split.
  - destruct (Z.ltb_spec0 x 0x174558); [exists 0x172c90, 0x174558; split; [left; reflexivity| lia]|]. destruct (Z.ltb_spec0 x 0x6aa210); [exists 0x69a210, 0x6aa210; split; [right; left; reflexivity| lia]|]. exists 0x6aa210, 0x6cd7d8; split; [right; right; left; reflexivity| lia].
  - intros (lo & hi & Hin & Hlh). unfold RT_STATIC in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
Qed.

Lemma drv_cell_static : forall x, drv_cell x -> client_static x.
Proof.
  intros x Hx. apply client_static_intro. unfold drv_cell, ERRNO_A, TP_A, SSP_GUARD, g_read_stage, TR_INIT in Hx. lia.
Qed.

Lemma LIB_img : forall x, in_ranges LIB_FP x -> client_static x /\ ~ drv_cell x.
Proof.
  intros x (lo & hi & Hin & Hx). unfold LIB_FP in Hin.
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (split; [apply client_static_intro; lia|]);
    unfold drv_cell, ERRNO_A, TP_A, SSP_GUARD, g_read_stage, TR_INIT; lia|]). destruct Hin.
Qed.

Lemma drv_cell_not_lib : forall x, drv_cell x -> outside LIB_FP x.
Proof.
  intros x Hx. apply outside_of_not_in_ranges'. intros Hin. exact (proj2 (LIB_img x Hin) Hx).
Qed.

Lemma stage_static' : forall x, g_read_stage <= x < g_read_stage + 65536 -> client_static x.
Proof. intros x Hx. apply client_static_intro. unfold g_read_stage in *. lia. Qed.

Section CLXT.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable XENV : mem -> Prop.
Variable XENV_FP : list (Z * Z).
Variable LIB : mem -> Prop.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : xenv_laws XENV XENV_FP.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.

Notation CLX := (CLX OUT_rep ERR_rep XENV LIB).

Definition CLX_FP (x : Z) : Prop := in_ranges IO_FP x \/ in_ranges XENV_FP x \/ in_ranges LIB_FP x \/ drv_cell x.

Lemma CLX_FP_static : forall x, CLX_FP x -> client_static x.
Proof using IO_img XENV_img.
  intros x [H|[H|[H|H]]]; [exact (proj1 (IO_img x H))| exact (proj1 (XENV_img x H))| exact (proj1 (LIB_img x H))| exact (drv_cell_static x H)].
Qed.

Lemma CLX_FP_range : forall x, CLX_FP x -> 0x10000 <= x < SEGTOP_A.
Proof using IO_img XENV_img. intros x H. exact (client_static_range x (CLX_FP_static x H)). Qed.

Lemma agree_ranges_sub : forall (P : Z -> Prop) W m m', agree_on P m m' -> (forall x, in_ranges W x -> P x) ->
  forall a : word, in_ranges W (bv_unsigned a) -> m' a = m a.
Proof. intros P W m m' H HW a Ha. exact (H a (HW _ Ha)). Qed.

Lemma CLX_agree : forall so m m', CLX so m -> agree_on CLX_FP m m' -> wmono bsegs m m' -> CLX so m'.
Proof using OUT_loc ERR_loc XENV_loc LIB_loc.
  intros so m m' (H1 & H2 & H3 & H4 & (g & SG) & (v & ER) & RS) AG WM.
  split; [apply (OUT_loc so m m' H1); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; left; exact Hx]|].
  split; [apply (ERR_loc m m' H2); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; left; exact Hx]|].
  split; [apply (xl_loc XENV_loc m m' H3); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; right; left; exact Hx]|].
  split; [apply (LIB_loc m m' H4); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; right; right; left; exact Hx]|].
  assert (AGD : forall lo n, (forall x, lo <= x < lo + n -> drv_cell x) -> agree_on (fun x => lo <= x < lo + n) m m').
  { intros lo n Hd. eapply agree_sub; [exact AG|]. intros x Hx. right; right; right. exact (Hd x Hx). }
  unfold drv_cell in AGD.
  split; [exists g; apply (ro_cells_agree bsegs m m' _ _ SG); apply AGD; cbn; lia|].
  split; [exists v; apply (rw_cells_agree bsegs m m' _ _ ER); [apply AGD; cbn; lia| exact WM]|].
  apply (stk_agree bsegs m m' _ _ RS); [eapply agree_sub; [apply (AGD g_read_stage 65536); lia| cbv beta; lia]| exact WM].
Qed.

Lemma CLX_agree_nw : forall so m m', CLX so m -> agree_on CLX_FP m m' -> CLX so m'.
Proof using OUT_loc ERR_loc XENV_loc LIB_loc.
  intros so m m' (H1 & H2 & H3 & H4 & (g & SG) & (v & ER) & RS) AG.
  split; [apply (OUT_loc so m m' H1); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; left; exact Hx]|].
  split; [apply (ERR_loc m m' H2); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; left; exact Hx]|].
  split; [apply (xl_loc XENV_loc m m' H3); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; right; left; exact Hx]|].
  split; [apply (LIB_loc m m' H4); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; right; right; left; exact Hx]|].
  assert (AGD : forall lo n, (forall x, lo <= x < lo + n -> drv_cell x) -> agree_on (fun x => lo <= x < lo + n) m m').
  { intros lo n Hd. eapply agree_sub; [exact AG|]. intros x Hx. right; right; right. exact (Hd x Hx). }
  unfold drv_cell in AGD.
  split; [exists g; apply (ro_cells_agree bsegs m m' _ _ SG); apply AGD; cbn; lia|].
  split; [exists v; apply (rw_cells_agree_nw bsegs m m' _ _ ER); apply AGD; cbn; lia|].
  apply (stk_agree_nw bsegs m m' _ _ RS); eapply agree_sub; [apply (AGD g_read_stage 65536); lia| cbv beta; lia].
Qed.

Lemma CLX_pres_nw : forall so m m' live frames sp, CLX so m -> rt_pres live frames sp m m' -> CLX so m'.
Proof using OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
  intros so m m' live frames sp H PR. apply (CLX_agree_nw so m m' H).
  apply (agree_of_pres _ _ _ _ _ _ PR). intros x Hx. right; left. exact (CLX_FP_static x Hx).
Qed.

Lemma CLX_munch : forall so m m' W, CLX so m -> munch W m m' -> wmono bsegs m m' ->
  (forall x, 0x10000 <= x < SEGTOP_A -> outside W x) -> CLX so m'.
Proof using OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
  intros so m m' W H MU WM HW. apply (CLX_agree so m m' H); [| exact WM].
  apply (agree_of_munch _ _ _ _ MU). intros x Hx. apply HW, CLX_FP_range, Hx.
Qed.

Lemma CLX_munch_errno : forall so m m' W, CLX so m -> munch W m m' -> wmono bsegs m m' ->
  (forall x, 0x10000 <= x < SEGTOP_A -> ~ (ERRNO_A <= x < ERRNO_A + 4) -> outside W x) ->
  (exists v, rw_cells bsegs m' ERRNO_A [C4 v]) -> CLX so m'.
Proof using OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
  intros so m m' W H MU WM HW ER.
  set (FP' := fun x => CLX_FP x /\ ~ (ERRNO_A <= x < ERRNO_A + 4)).
  assert (AG : agree_on FP' m m').
  { apply (agree_of_munch _ _ _ _ MU). intros x (Hx & He). apply HW; [apply CLX_FP_range, Hx| exact He]. }
  destruct H as (H1 & H2 & H3 & H4 & (g & SG) & _ & RS).
  assert (NE : forall x, in_ranges IO_FP x \/ in_ranges XENV_FP x \/ in_ranges LIB_FP x -> ~ (ERRNO_A <= x < ERRNO_A + 4)).
  { intros x [Hx|[Hx|Hx]] Hn; [apply (proj1 (proj2 (IO_img x Hx)))| apply (proj1 (proj2 (XENV_img x Hx)))|
                                apply (proj2 (LIB_img x Hx))]; left; exact Hn. }
  split; [apply (OUT_loc so m m' H1); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; split; [left; exact Hx| apply NE; left; exact Hx]]|].
  split; [apply (ERR_loc m m' H2); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; split; [left; exact Hx| apply NE; left; exact Hx]]|].
  split; [apply (xl_loc XENV_loc m m' H3); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; split; [right; left; exact Hx| apply NE; right; left; exact Hx]]|].
  split; [apply (LIB_loc m m' H4); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; split; [right; right; left; exact Hx| apply NE; right; right; exact Hx]]|].
  assert (AGD : forall lo n, (forall x, lo <= x < lo + n -> drv_cell x /\ ~ (ERRNO_A <= x < ERRNO_A + 4)) ->
                  agree_on (fun x => lo <= x < lo + n) m m').
  { intros lo n Hd. eapply agree_sub; [exact AG|]. intros x Hx. destruct (Hd x Hx) as [D1 D2]. split; [right; right; right; exact D1| exact D2]. }
  unfold drv_cell in AGD. unfold ERRNO_A, TP_A, SSP_GUARD, g_read_stage, TR_INIT in AGD.
  split; [exists g; apply (ro_cells_agree bsegs m m' _ _ SG); apply AGD; cbn; unfold SSP_GUARD; lia|].
  split; [exact ER|].
  apply (stk_agree bsegs m m' _ _ RS); [eapply agree_sub; [apply (AGD g_read_stage 65536); unfold g_read_stage; lia| cbv beta; lia]| exact WM].
Qed.

Lemma CLX_pres : forall so m m' live frames sp, CLX so m -> rt_pres live frames sp m m' -> wmono bsegs m m' -> CLX so m'.
Proof using OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
  intros so m m' live frames sp H PR WM. apply (CLX_agree so m m' H); [| exact WM].
  apply (agree_of_pres _ _ _ _ _ _ PR). intros x Hx. right; left. exact (CLX_FP_static x Hx).
Qed.

Lemma CLX_pres_ex : forall so m m' live frames sp d n, CLX so m -> rt_pres_ex live frames sp d n m m' -> wmono bsegs m m' ->
  (forall x, 0x10000 <= x < SEGTOP_A -> ~ (d <= x < d + n)) -> CLX so m'.
Proof using OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
  intros so m m' live frames sp d n H PR WM HD. apply (CLX_agree so m m' H); [| exact WM].
  apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PR). intros x Hx. split; [right; left; exact (CLX_FP_static x Hx)|].
  apply HD, CLX_FP_range, Hx.
Qed.

Lemma CLX_io : forall so so' m m' live frames sp, CLX so m -> rt_pres_fp live frames sp IO_FP m m' -> wmono bsegs m m' ->
  OUT_rep so' m' -> ERR_rep m' -> CLX so' m'.
Proof using OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
  intros so so' m m' live frames sp (H1 & H2 & H3 & H4 & (g & SG) & (v & ER) & RS) PR WM O' E'.
  assert (AG : agree_on (fun x => in_ranges XENV_FP x \/ in_ranges LIB_FP x \/ drv_cell x) m m').
  { apply (agree_of_pres_fp _ _ _ _ _ _ _ PR). intros x [Hx|[Hx|Hx]].
    - split; [right; left; exact (proj1 (XENV_img x Hx))| exact (proj1 (proj2 (proj2 (XENV_img x Hx))))].
    - split; [right; left; exact (proj1 (LIB_img x Hx))|]. apply outside_of_not_in_ranges'. intros Hin.
      apply (not_in_ranges_of_outside _ _ (proj2 (proj2 (IO_img x Hin))) Hx).
    - split; [right; left; exact (drv_cell_static x Hx)|]. apply outside_of_not_in_ranges'. intros Hin.
      exact (proj1 (proj2 (IO_img x Hin)) Hx). }
  split; [exact O'|]. split; [exact E'|].
  split; [apply (xl_loc XENV_loc m m' H3); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; left; exact Hx]|].
  split; [apply (LIB_loc m m' H4); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; right; left; exact Hx]|].
  assert (AGD : forall lo n, (forall x, lo <= x < lo + n -> drv_cell x) -> agree_on (fun x => lo <= x < lo + n) m m').
  { intros lo n Hd. eapply agree_sub; [exact AG|]. intros x Hx. right; right. exact (Hd x Hx). }
  unfold drv_cell in AGD.
  split; [exists g; apply (ro_cells_agree bsegs m m' _ _ SG); apply AGD; cbn; lia|].
  split; [exists v; apply (rw_cells_agree bsegs m m' _ _ ER); [apply AGD; cbn; lia| exact WM]|].
  apply (stk_agree bsegs m m' _ _ RS); [eapply agree_sub; [apply (AGD g_read_stage 65536); lia| cbv beta; lia]| exact WM].
Qed.

Lemma CLX_lib : forall so m m' live frames sp, CLX so m -> rt_pres_fp live frames sp LIB_FP m m' -> wmono bsegs m m' ->
  LIB m' -> CLX so m'.
Proof using OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
  intros so m m' live frames sp (H1 & H2 & H3 & H4 & (g & SG) & (v & ER) & RS) PR WM L'.
  assert (AG : agree_on (fun x => in_ranges IO_FP x \/ in_ranges XENV_FP x \/ drv_cell x) m m').
  { apply (agree_of_pres_fp _ _ _ _ _ _ _ PR). intros x [Hx|[Hx|Hx]].
    - split; [right; left; exact (proj1 (IO_img x Hx))| exact (proj2 (proj2 (IO_img x Hx)))].
    - split; [right; left; exact (proj1 (XENV_img x Hx))| exact (proj2 (proj2 (proj2 (XENV_img x Hx))))].
    - split; [right; left; exact (drv_cell_static x Hx)| exact (drv_cell_not_lib x Hx)]. }
  split; [apply (OUT_loc so m m' H1); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; left; exact Hx]|].
  split; [apply (ERR_loc m m' H2); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; left; exact Hx]|].
  split; [apply (xl_loc XENV_loc m m' H3); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; right; left; exact Hx]|].
  split; [exact L'|].
  assert (AGD : forall lo n, (forall x, lo <= x < lo + n -> drv_cell x) -> agree_on (fun x => lo <= x < lo + n) m m').
  { intros lo n Hd. eapply agree_sub; [exact AG|]. intros x Hx. right; right. exact (Hd x Hx). }
  unfold drv_cell in AGD.
  split; [exists g; apply (ro_cells_agree bsegs m m' _ _ SG); apply AGD; cbn; lia|].
  split; [exists v; apply (rw_cells_agree bsegs m m' _ _ ER); [apply AGD; cbn; lia| exact WM]|].
  apply (stk_agree bsegs m m' _ _ RS); [eapply agree_sub; [apply (AGD g_read_stage 65536); lia| cbv beta; lia]| exact WM].
Qed.

Lemma CLX_lib_nw : forall so m m' live frames sp, CLX so m -> rt_pres_fp live frames sp LIB_FP m m' ->
  LIB m' -> CLX so m'.
Proof using OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
  intros so m m' live frames sp (H1 & H2 & H3 & H4 & (g & SG) & (v & ER) & RS) PR L'.
  assert (AG : agree_on (fun x => in_ranges IO_FP x \/ in_ranges XENV_FP x \/ drv_cell x) m m').
  { apply (agree_of_pres_fp _ _ _ _ _ _ _ PR). intros x [Hx|[Hx|Hx]].
    - split; [right; left; exact (proj1 (IO_img x Hx))| exact (proj2 (proj2 (IO_img x Hx)))].
    - split; [right; left; exact (proj1 (XENV_img x Hx))| exact (proj2 (proj2 (proj2 (XENV_img x Hx))))].
    - split; [right; left; exact (drv_cell_static x Hx)| exact (drv_cell_not_lib x Hx)]. }
  split; [apply (OUT_loc so m m' H1); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; left; exact Hx]|].
  split; [apply (ERR_loc m m' H2); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; left; exact Hx]|].
  split; [apply (xl_loc XENV_loc m m' H3); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; right; left; exact Hx]|].
  split; [exact L'|].
  assert (AGD : forall lo n, (forall x, lo <= x < lo + n -> drv_cell x) -> agree_on (fun x => lo <= x < lo + n) m m').
  { intros lo n Hd. eapply agree_sub; [exact AG|]. intros x Hx. right; right. exact (Hd x Hx). }
  unfold drv_cell in AGD.
  split; [exists g; apply (ro_cells_agree bsegs m m' _ _ SG); apply AGD; cbn; lia|].
  split; [exists v; apply (rw_cells_agree_nw bsegs m m' _ _ ER); apply AGD; cbn; lia|].
  apply (stk_agree_nw bsegs m m' _ _ RS); eapply agree_sub; [apply (AGD g_read_stage 65536); lia| cbv beta; lia].
Qed.

Lemma CLX_errno_pres : forall so m m' live frames sp, CLX so m ->
  rt_pres_fp live frames sp [(ERRNO_A, ERRNO_A + 4)] m m' -> wmono bsegs m m' ->
  OUT_rep so m' /\ ERR_rep m' /\ XENV m' /\ LIB m'.
Proof using OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
  intros so m m' live frames sp (H1 & H2 & H3 & H4 & _) PR WM.
  assert (NE : forall x, in_ranges IO_FP x \/ in_ranges XENV_FP x \/ in_ranges LIB_FP x ->
                 m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)).
  { intros x Hx. assert (CS : client_static x) by (destruct Hx as [Hx|[Hx|Hx]]; [exact (proj1 (IO_img x Hx))| exact (proj1 (XENV_img x Hx))| exact (proj1 (LIB_img x Hx))]).
    assert (ND : ~ drv_cell x) by (destruct Hx as [Hx|[Hx|Hx]]; [exact (proj1 (proj2 (IO_img x Hx)))| exact (proj1 (proj2 (XENV_img x Hx)))| exact (proj2 (LIB_img x Hx))]).
    pose proof (client_static_range x CS) as R.
    apply PR; rewrite unsigned_lit by (unfold SEGTOP_A in R; lia); [right; left; exact CS|].
    cbn. split; [| exact I]. intros Hn. apply ND. left. exact Hn. }
  assert (AG : forall (W : list (Z * Z)), (forall x, in_ranges W x -> in_ranges IO_FP x \/ in_ranges XENV_FP x \/ in_ranges LIB_FP x) ->
                 forall a : word, in_ranges W (bv_unsigned a) -> m' a = m a).
  { intros W HW a Ha. rewrite <- (Z_to_bv_bv_unsigned a). apply NE, HW, Ha. }
  split; [apply (OUT_loc so m m' H1); [apply AG; intros x Hx; left; exact Hx]|].
  split; [apply (ERR_loc m m' H2); [apply AG; intros x Hx; left; exact Hx]|].
  split; [apply (xl_loc XENV_loc m m' H3); [apply AG; intros x Hx; right; left; exact Hx]|].
  apply (LIB_loc m m' H4); [apply AG; intros x Hx; right; right; exact Hx].
Qed.

Lemma CLX_read : forall so m m' live frames sp bs, CLX so m ->
  rt_pres_fp live frames sp [(g_read_stage, g_read_stage + Z.of_nat (length bs))] m m' -> wmono bsegs m m' ->
  bytes_at bsegs m' g_read_stage bs -> Z.of_nat (length bs) <= 65536 -> CLX so m'.
Proof using OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
  intros so m m' live frames sp bs (H1 & H2 & H3 & H4 & (g & SG) & (v & ER) & RS) PR WM BS LB.
  set (k := Z.of_nat (length bs)) in *.
  assert (NS : forall x, CLX_FP x -> ~ (g_read_stage <= x < g_read_stage + 65536) -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)).
  { intros x Hx Hn. pose proof (CLX_FP_static x Hx) as CS. pose proof (client_static_range x CS) as R.
    apply PR; rewrite unsigned_lit by (unfold SEGTOP_A in R; lia); [right; left; exact CS|].
    cbn. split; [| exact I]. intros Hk. apply Hn. lia. }
  assert (AGW : forall (P : Z -> Prop), (forall x, P x -> CLX_FP x /\ ~ (g_read_stage <= x < g_read_stage + 65536)) -> agree_on P m m').
  { intros P HP a Ha. rewrite <- (Z_to_bv_bv_unsigned a). destruct (HP _ Ha) as [HP1 HP2]. exact (NS _ HP1 HP2). }
  assert (NRS : forall x, in_ranges IO_FP x \/ in_ranges XENV_FP x \/ in_ranges LIB_FP x -> ~ (g_read_stage <= x < g_read_stage + 65536)).
  { intros x [Hx|[Hx|Hx]] Hn; [apply (proj1 (proj2 (IO_img x Hx)))| apply (proj1 (proj2 (XENV_img x Hx)))|
                                apply (proj2 (LIB_img x Hx))]; right; right; left; exact Hn. }
  split; [apply (OUT_loc so m m' H1); [apply (agree_ranges_sub _ _ _ _ (AGW (fun x => in_ranges IO_FP x) ltac:(intros x Hx; split; [left; exact Hx| apply NRS; left; exact Hx]))); intros x Hx; exact Hx]|].
  split; [apply (ERR_loc m m' H2); [apply (agree_ranges_sub _ _ _ _ (AGW (fun x => in_ranges IO_FP x) ltac:(intros x Hx; split; [left; exact Hx| apply NRS; left; exact Hx]))); intros x Hx; exact Hx]|].
  split; [apply (xl_loc XENV_loc m m' H3); [apply (agree_ranges_sub _ _ _ _ (AGW (fun x => in_ranges XENV_FP x) ltac:(intros x Hx; split; [right; left; exact Hx| apply NRS; right; left; exact Hx]))); intros x Hx; exact Hx]|].
  split; [apply (LIB_loc m m' H4); [apply (agree_ranges_sub _ _ _ _ (AGW (fun x => in_ranges LIB_FP x) ltac:(intros x Hx; split; [right; right; left; exact Hx| apply NRS; right; right; exact Hx]))); intros x Hx; exact Hx]|].
  assert (AGD : forall lo n, (forall x, lo <= x < lo + n -> drv_cell x /\ ~ (g_read_stage <= x < g_read_stage + 65536)) ->
                  agree_on (fun x => lo <= x < lo + n) m m').
  { intros lo n Hd. apply AGW. intros x Hx. destruct (Hd x Hx) as [D1 D2]. split; [right; right; right; exact D1| exact D2]. }
  unfold drv_cell in AGD. unfold ERRNO_A, TP_A, SSP_GUARD, g_read_stage, TR_INIT in AGD.
  split; [exists g; apply (ro_cells_agree bsegs m m' _ _ SG); apply AGD; cbn; unfold SSP_GUARD; lia|].
  split; [exists v; apply (rw_cells_agree bsegs m m' _ _ ER); [apply AGD; cbn; unfold ERRNO_A, TP_A; lia| exact WM]|].
  pose proof RS as (RS1 & RS2 & RSH). split; [exact RS1|]. split; [exact RS2|].
  intros a Ha. destruct (RSH a Ha) as [Hw (b & Hb)]. split; [exact (WM _ Hw)|].
  destruct (Z.ltb_spec0 a (g_read_stage + k)) as [Hlt|Hge].
  + pose proof BS as (_ & _ & HBS). destruct (nth_error bs (Z.to_nat (a - g_read_stage))) as [b'|] eqn:E.
    * exists b'. rewrite <- E. rewrite <- HBS by lia. f_equal. unfold wa. f_equal. lia.
    * apply nth_error_None in E. lia.
  + exists b. unfold mrd in *. rewrite (PR (wa a)); [exact Hb| |].
    * rewrite wa_unsigned by lia. right; left. apply stage_static'. lia.
    * rewrite wa_unsigned by lia. cbn. split; [lia| exact I].
Qed.

Lemma CLX_aexw : forall so m m' W, CLX so m -> munch W m m' -> wmono bsegs m m' ->
  (forall x, 0x10000 <= x < SEGTOP_A -> ~ in_ranges AEX_FPA x -> outside W x) -> aexA m' -> CLX so m'.
Proof using OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
  intros so m m' W (H1 & H2 & H3 & H4 & (g & SG) & (v & ER) & RS) MU WM HW AEX'.
  destruct (xenv_open XENV XENV_FP XENV_loc m H3) as [CORE _].
  assert (NA : forall x, in_ranges IO_FP x \/ in_ranges (xl_core_fp XENV_loc) x \/ in_ranges LIB_FP x \/ drv_cell x -> ~ in_ranges AEX_FPA x).
  { intros x Hx Ha. pose proof (XENV_img x (xl_aex_in XENV_loc x Ha)) as (_ & ND & NIO & NLIB).
    destruct Hx as [Hx|[Hx|[Hx|Hx]]].
    - exact (not_in_ranges_of_outside _ _ NIO Hx).
    - exact (xl_core_sep XENV_loc x Ha Hx).
    - exact (not_in_ranges_of_outside _ _ NLIB Hx).
    - exact (ND Hx). }
  assert (AG : agree_on (fun x => in_ranges IO_FP x \/ in_ranges (xl_core_fp XENV_loc) x \/ in_ranges LIB_FP x \/ drv_cell x) m m').
  { apply (agree_of_munch _ _ _ _ MU). intros x Hx. apply HW; [| exact (NA x Hx)].
    destruct Hx as [Hx|[Hx|[Hx|Hx]]].
    - exact (client_static_range x (proj1 (IO_img x Hx))).
    - exact (client_static_range x (proj1 (XENV_img x (xl_core_in XENV_loc x Hx)))).
    - exact (client_static_range x (proj1 (LIB_img x Hx))).
    - exact (client_static_range x (drv_cell_static x Hx)). }
  split; [apply (OUT_loc so m m' H1); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; left; exact Hx]|].
  split; [apply (ERR_loc m m' H2); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; left; exact Hx]|].
  split; [apply (xenv_close XENV XENV_FP XENV_loc m'); [| exact AEX'];
          apply (core_keep XENV XENV_FP XENV_loc m m' CORE); apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; right; left; exact Hx|].
  split; [apply (LIB_loc m m' H4); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; right; right; left; exact Hx]|].
  assert (AGD : forall lo n, (forall x, lo <= x < lo + n -> drv_cell x) -> agree_on (fun x => lo <= x < lo + n) m m').
  { intros lo n Hd. eapply agree_sub; [exact AG|]. intros x Hx. right; right; right. exact (Hd x Hx). }
  unfold drv_cell in AGD.
  split; [exists g; apply (ro_cells_agree bsegs m m' _ _ SG); apply AGD; cbn; lia|].
  split; [exists v; apply (rw_cells_agree bsegs m m' _ _ ER); [apply AGD; cbn; lia| exact WM]|].
  apply (stk_agree bsegs m m' _ _ RS); [eapply agree_sub; [apply (AGD g_read_stage 65536); lia| cbv beta; lia]| exact WM].
Qed.

Lemma CLX_lib_flag : forall so m m', CLX so m ->
  agree_on (fun x => (in_ranges IO_FP x \/ in_ranges XENV_FP x \/ drv_cell x) /\ x <> AEF_INCB) m m' ->
  LIB m' -> rw_cells bsegs m' AEF_INCB [C1 (Z_to_bv 8 0)] -> CLX so m'.
Proof using OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
  intros so m m' (H1 & H2 & H3 & H4 & (g & SG) & (v & ER) & RS) AG L' F'.
  assert (NI : forall x, in_ranges IO_FP x \/ in_ranges (xl_core_fp XENV_loc) x \/ drv_cell x -> x <> AEF_INCB).
  { intros x Hx E. subst x.
    assert (HA : in_ranges AEX_FPA AEF_INCB) by (rewrite in_AEX_FPA_iff; right; right; right; reflexivity).
    pose proof (XENV_img _ (xl_aex_in XENV_loc _ HA)) as (_ & ND & NIO & _).
    destruct Hx as [Hx|[Hx|Hx]]; [exact (not_in_ranges_of_outside _ _ NIO Hx)| exact (xl_core_sep XENV_loc _ HA Hx)| exact (ND Hx)]. }
  split; [apply (OUT_loc so m m' H1); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; split; [left; exact Hx| apply NI; left; exact Hx]]|].
  split; [apply (ERR_loc m m' H2); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; split; [left; exact Hx| apply NI; left; exact Hx]]|].
  split.
  { destruct (xenv_open XENV XENV_FP XENV_loc m H3) as [CORE AEX]. apply (xenv_close XENV XENV_FP XENV_loc m').
    - apply (core_keep XENV XENV_FP XENV_loc m m' CORE). apply (agree_ranges_sub _ _ _ _ AG). intros x Hx.
      split; [right; left; exact (xl_core_in XENV_loc x Hx)| apply NI; right; left; exact Hx].
    - apply (aexA_reflag m m' AEX); [| exact F']. apply (agree_ranges_sub _ _ _ _ AG). intros x Hx.
      destruct (in_AEX_FP3 x Hx) as [HxA NE]. split; [right; left; exact (xl_aex_in XENV_loc x HxA)| exact NE]. }
  split; [exact L'|].
  assert (AGD : forall lo n, (forall x, lo <= x < lo + n -> drv_cell x) -> agree_on (fun x => lo <= x < lo + n) m m').
  { intros lo n Hd. eapply agree_sub; [exact AG|]. intros x Hx. split; [right; right; exact (Hd x Hx)| apply NI; right; right; exact (Hd x Hx)]. }
  unfold drv_cell in AGD.
  split; [exists g; apply (ro_cells_agree bsegs m m' _ _ SG); apply AGD; cbn; lia|].
  split; [exists v; apply (rw_cells_agree_nw bsegs m m' _ _ ER); apply AGD; cbn; lia|].
  apply (stk_agree_nw bsegs m m' _ _ RS); eapply agree_sub; [apply (AGD g_read_stage 65536); lia| cbv beta; lia].
Qed.

End CLXT.

Lemma CLX_io_ssp : forall (OUT_rep : stdout_st -> mem -> Prop) (ERR_rep XENV LIB : mem -> Prop) so m,
  CLX OUT_rep ERR_rep XENV LIB so m -> drv_consts m -> io_ssp m.
Proof. intros OUT_rep ERR_rep XENV LIB so m (_ & _ & _ & _ & (g & G) & _) DC. exact (drv_ssp m g DC G). Qed.

Ltac io_ssp_tac AFD :=
  lazymatch goal with
  | |- io_ssp ?mm =>
      first [ assumption
            | match goal with H : ssp_cells mm |- _ => exact H end
            | match goal with H : CLX _ _ _ _ _ mm |- _ =>
                match goal with HA : ART _ _ mm |- _ => exact (CLX_io_ssp _ _ _ _ _ mm H (AFD _ mm HA)) end end
            | match goal with G : ro_cells bsegs mm SSP_GUARD [C8 ?g] |- _ =>
                match goal with HA : ART _ _ mm |- _ => exact (drv_ssp mm g (AFD _ mm HA) G) end end ]
  end.

Lemma io_ssp_pres_fp : forall (W : list (Z * Z)) live frames sp m m',
  (forall x, SSP_GUARD <= x < SSP_GUARD + 8 -> outside W x) ->
  io_ssp m -> drv_consts m' -> rt_pres_fp live frames sp W m m' -> io_ssp m'.
Proof.
  intros W live frames sp m m' HW (g & _ & G) DC P. exists g. split; [exact (proj1 (proj2 DC))|].
  apply (ro_cells_agree bsegs m m' _ _ G). apply (agree_of_pres_fp _ _ _ _ _ _ _ P). intros x Hx. cbn in Hx.
  split.
  - right; left. apply client_static_intro. lia.
  - apply HW. unfold SSP_GUARD. lia.
Qed.
