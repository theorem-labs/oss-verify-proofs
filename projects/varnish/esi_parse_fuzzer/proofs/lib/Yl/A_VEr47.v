(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Po6qc A_Potrl A_Vsb A_World A_Img A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vez59.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_ImgAny.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vei6d A_vez59.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Potrl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59.A_Leaf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_ImgAny OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App.A_Fpx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vei6d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac icall_consts_in H ::= unfold leaf_post, vsb_leaf_post, vep_default_cb_post, VSB_finish_post, CB_STACK, FINISH_STACK, LEN_STACK, ASSERT_STACK, ERRNOA in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= hot_kdrop; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].

(* [comment removed for export] *)
Lemma rw_cells_split3 : forall segs m A cs k c,
  rw_cells segs m A cs -> nth_error cs k = Some c ->
  rw_cells segs m A (firstn k cs) /\
  rw_cells segs m (A + Z.of_nat (cells_size (firstn k cs))) [c] /\
  rw_cells segs m (A + Z.of_nat (cells_size (firstn k cs)) + Z.of_nat (csize c)) (skipn (S k) cs).
Proof.
  intros segs m A cs k c RC Hk.
  assert (E : cs = firstn k cs ++ [c] ++ skipn (S k) cs).
  { rewrite <- (firstn_skipn k cs) at 1. f_equal.
    revert Hk. clear. revert cs. induction k as [|k IH]; intros [|x cs] Hk; cbn in *; try discriminate.
    - inversion Hk. reflexivity.
    - apply IH. exact Hk. }
  rewrite E in RC. apply rw_cells_app in RC. destruct RC as [R1 R23]. apply rw_cells_app in R23. destruct R23 as [R2 R3].
  split; [exact R1|]. split; [exact R2|]. cbn [cells_size Nat.add] in R3. rewrite Nat.add_0_r in R3.
  eapply rwc_eq; [exact R3| lia].
Qed.

Lemma rw_cells_join3 : forall segs m A pre c post,
  rw_cells segs m A pre ->
  rw_cells segs m (A + Z.of_nat (cells_size pre)) [c] ->
  rw_cells segs m (A + Z.of_nat (cells_size pre) + Z.of_nat (csize c)) post ->
  rw_cells segs m A (pre ++ [c] ++ post).
Proof.
  intros segs m A pre c post R1 R2 R3. apply rw_cells_app. split; [exact R1|]. apply rw_cells_app. split; [exact R2|].
  cbn [cells_size Nat.add]. rewrite Nat.add_0_r. eapply rwc_eq; [exact R3| lia].
Qed.

Lemma vep_cells_vsb : forall v tag q,
  firstn 2 (vep_cells v tag q) ++ [C8 (Z_to_bv 64 0)] ++ skipn 3 (vep_cells v tag q) = vep_cells (fupd v Fvsb 0) tag q.
Proof. intros. reflexivity. Qed.
Lemma vep_cells_attr_vsb : forall v tag q,
  firstn 36 (vep_cells v tag q) ++ [C8 (Z_to_bv 64 0)] ++ skipn 37 (vep_cells v tag q) = vep_cells (fupd v Fattr_vsb 0) tag q.
Proof. intros. reflexivity. Qed.
Lemma vep_cells_include_src : forall v tag q,
  firstn 45 (vep_cells v tag q) ++ [C8 (Z_to_bv 64 0)] ++ skipn 46 (vep_cells v tag q) = vep_cells (fupd v Finclude_src 0) tag q.
Proof. intros. reflexivity. Qed.
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma vep_cells_ext : forall v v' tag q, (forall f, v' f = v f) -> vep_cells v' tag q = vep_cells v tag q.
Proof. intros v v' tag q E. unfold vep_cells. rewrite !E. reflexivity. Qed.
Lemma fupd_cbx0 : forall v f, fupd v Fcb_x (v Fcb_x + 0) f = v f.
Proof. intros v f. unfold fupd. destruct (vf_beq f Fcb_x) eqn:E; [|reflexivity]. apply vf_beq_eq in E. subst f. lia. Qed.

(* [comment removed for export] *)
Lemma frames_young_le {AI : AsanAlloc LPA} : forall A n0 n1 m0 m1,
  frames_young A n0 n1 -> (m0 <= n0)%nat -> (m1 <= n1)%nat -> frames_young A m0 m1.
Proof.
  intros A n0 n1 m0 m1 FY H0 H1 ff k age HF K. pose proof (FY ff k age HF K) as Y.
  unfold fbound in *. destruct (Z.eqb k 0); [lia|]. destruct (Z.eqb k 1); lia.
Qed.
Lemma frames_aged_back {AI : AsanAlloc LPA} : forall A A' a0 a1,
  frames_aged A A' a0 a1 ->
  forall ff k age, a_frame A' ff = Some (k, age) -> (k = 0 \/ k = 1) -> exists age0, a_frame A ff = Some (k, age0).
Proof.
  intros A A' a0 a1 [AG NN] ff k age HF _.
  destruct (a_frame A ff) as [[k0 age0]|] eqn:E.
  - (first [ pose proof ((AG _ _ _ E)) as dR_1; dex1 dR_1 as d; destruct dR_1 as [E' _] | pose proof ((AG _ _ _ E)) as dR_1; dand3 dR_1 as d E' _ | destruct (AG _ _ _ E) as (d & E' & _) ]). rewrite HF in E'. injection E' as <- _. exists age0. reflexivity.
  - rewrite (NN _ E) in HF. discriminate.
Qed.

End CEIL.

Section CF.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma cframe_after : forall o o' spx WIN (V N : Z -> Prop) ma mb mc W,
    cframe LPA o o' spx WIN V N ma mb -> munch W mb mc ->
    (forall a, 0 <= a < 2^64 -> ~ outside W a ->
               (spx - WIN <= a < spx) \/ V a \/ N a \/ (cl_errno LPA <= a < cl_errno LPA + 4)) ->
    mapped mc (spx - WIN) WIN ->
    cframe LPA o o' spx WIN V N ma mc.
  Proof.
    (intros o o' spx WIN V N ma mb mc W; (first [ intro dR_30; dand3 dR_30 as C1 C2 C3 | intros (C1 & C2 & C3) ]); intros MU IN MAP). split; [|split; [exact MAP| exact C3]].
    intros a Ha NO VIS NW NE NV.
    destruct (C1 a Ha NO VIS NW NE NV) as [E NO'].
    assert (NN : ~ N a).
    { intros X. destruct (C3 a Ha NW NE X) as [Y|[Y|[Y Z0]]]; [exact (NO Y)| exact (NV Y)|].
      destruct VIS as [U|U]; [exact (U Y)| exact (Z0 U)]. }
    assert (OW : outside W a).
    { destruct (Classical_Prop.classic (outside W a)) as [X|X]; [exact X|]. exfalso.
      destruct (IN a Ha X) as [Y|[Y|[Y|Y]]]; [exact (NW Y)| exact (NV Y)| exact (NN Y)| exact (NE Y)]. }
    split; [|exact NO']. rewrite <- E. apply (MU (Z_to_bv 64 a)). rewrite unsigned_lit by lia. exact OW.
  Qed.

  (* [comment removed for export] *)
  Lemma cframe_newV : forall o o' spx WIN (V N N' : Z -> Prop) ma mb,
    cframe LPA o o' spx WIN V N ma mb -> (forall a, N' a -> N a \/ V a) -> cframe LPA o o' spx WIN V N' ma mb.
  Proof.
    (intros o o' spx WIN V N N' ma mb; (first [ intro dR_31; dand3 dR_31 as C1 C2 C3 | intros (C1 & C2 & C3) ]); intros HN). split; [exact C1|]. split; [exact C2|].
    intros a Ha NW NE X. destruct (HN a X) as [Y|Y]; [exact (C3 a Ha NW NE Y)| right; left; exact Y].
  Qed.

  (* [comment removed for export] *)
  Definition vsb_len_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (r lo : Z) (v : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 v',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None v' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] v v' /\ wmono rsegs v v' /\ mem_inv rsegs v'
      /\ stk rsegs v' lo (bv_unsigned sp).
  Lemma VSB_len_w : VSB_len_stmt ->
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (v : mem) (S : Z) (vr : vsb_rec) (fin : bool) (lo : Z),
      a0 = Z_to_bv 64 S ->
      rw_cells rsegs v S (vsb_cells vr) -> vsb_inv vr fin ->
      shadowed LPA v S 40 -> cenv v ->
      S mod 8 = 0 -> kHighMemBeg <= S -> S + 40 <= alloc_ceiling ->
      stk rsegs v lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> alloc_ceiling <= lo ->
      mem_inv rsegs v ->
      evt rsegs (vsb_len_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (vsb_result (vb_error vr) (vb_len vr)) lo v)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 VSB_len_entry) fc None v (seg_rom rsegs)).
  Proof.
    intros HLN. intros until lo. intros EA VC VI SH CE S8 SLO SHI ST W CEIL MI.
    eapply evt_mono.
    { eapply (HLN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc v S vr fin lo);
        [exact EA| exact VC| exact VI| exact SH| exact CE| exact S8| exact SLO| exact SHI| exact ST| unfold LEN_STACK, ASSERT_STACK; lia| exact CEIL| exact MI]. }
    intros ms' PO. unfold vsb_leaf_post, leaf_post, LEN_STACK, ASSERT_STACK in PO. unfold vsb_len_post.
    (first [ dex16 PO as y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 v'; dand5 PO as E MU WM MI' ST' | dand21 PO as y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 v' E MU WM MI' ST' | destruct PO as (y0 & y1 & y2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & v' & E & MU & WM & MI' & ST') ]).
    do 15 eexists. split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'| exact ST'].
  Qed.
End CF.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HMC : vep_mark_common_stmt.
  Hypothesis HEC : vep_emit_common_stmt.
  Hypothesis HCB : vep_default_cb_stmt.
  Hypothesis HDS : VSB_destroy_stmt.
  Hypothesis HFI : VSB_finish_stmt.
  Hypothesis HLN : VSB_len_stmt.

  (* [comment removed for export] *)
  Variables (H : henv) (VEP wa n N DATA : Z) (v0 : vep) (tag : list byte) (q : vep_pads) (vv0 : vsb_rec)
            (va : option vsb_rec) (vi : option (vsb_rec * bool)) (lo : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (T : TSet).
  Let S := v0 Fvsb.
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis PW : parsed_world H A0 (aview A0 m0) VEP v0 tag q vv0 va vi wa n N.
  Hypothesis HENV0 : henv_ok LPA VIA H A0 (aview A0 m0).
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + VEPFIN_STACK <= bv_unsigned sp.
  Hypothesis LD0 : a_live A0 DATA = Some N.
  Hypothesis N0 : 0 < N.
  Hypothesis DRANGE : DATA <= v0 Fver_p <= DATA + N.
  Hypothesis NEDV : DATA <> VEP.
  Hypothesis NEDS : DATA <> v0 Fvsb.
  Hypothesis NPB : ~ parse_blocks v0 vv0 va vi DATA.
  Hypothesis LBM0 : a_livebytes A0 + FIN_LIVE N <= LIVE_MAX.
  Hypothesis NLV0 : a_nlive A0 + 1 <= NLIVE_MAX.
  Hypothesis SCC0 : FIN_CRED N <= a_seccred A0.
  Hypothesis PCC0 : PRIM_ROOM + (PPOT_CAP - vsb_ppot vv0) <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis FY0 : frames_young A0 4 0.
  Hypothesis K :
    forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model)
           (v' : vep) (vr : vsb_rec),
      let w' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs w' -> amd_frame md0 md' ->
      stk rsegs w' lo (bv_unsigned sp) -> henv_ok LPA VIA H A' w' ->
      vep_obj LPA A' w' VEP v' tag q -> ws1_obj LPA H A' w' wa VEP ->
      (r = 0 \/ (r <> 0 /\ r = v0 Fvsb /\ vsb_obj LPA A' w' r vr true /\ vsb_apart r vr [VEP; wa] /\
                 (parse_blocks v0 vv0 va vi (vb_buf vr) \/ a_live A0 (vb_buf vr) = None))) ->
      (forall p k, a_live A0 p = Some k -> p <> v0 Fvsb -> ~ parse_blocks v0 vv0 va vi p -> a_live A' p = Some k) ->
      frames_aged A0 A' 4 0 ->
      a_livebytes A' = a_livebytes A0 - world_bytes vv0 va vi + (if Z.eqb r 0 then 0 else 40 + vb_size vr) ->
      a_tinycred A' = a_tinycred A0 -> a_nlive A' = a_nlive A0 - world_nlive va vi - (if Z.eqb r 0 then 2 else 0) ->
      a_seccred A0 - FIN_CRED N <= a_seccred A' <= a_seccred A0 ->
      a_primcred A0 - (PPOT_CAP - vsb_ppot vv0) <= a_primcred A' <= a_primcred A0 ->   (* [comment removed for export] *)
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) VEPFIN_STACK (finish_changed H VEP v0 vv0 va vi)
             (fun a => r <> 0 /\ vsb_blocks r vr a) (aview A0 m0) w' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.

  (* [comment removed for export] *)
  Definition jst (A : AS) (m : mem) (md : Model) (v : vep) (vv : vsb_rec) (fin : bool) (lenb : Z) (fa : nat) (cr : Z) : Prop :=
       ainv A m md /\ mem_inv rsegs (aview A m) /\ amd_frame md0 md
    /\ stk rsegs (aview A m) lo (bv_unsigned sp - 64)
    /\ rw_cells rsegs (aview A m) (bv_unsigned sp - 64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ henv_ok LPA VIA H A (aview A m)
    /\ vep_obj LPA A (aview A m) VEP v tag q /\ vep_base H VEP v
    /\ v Fvsb = S /\ v Finclude_src = 0 /\ v Fattr_vsb = 0
    /\ v Fstate = v0 Fstate /\ v Fesi_found = v0 Fesi_found /\ bool01 (v Flast_mark) /\ v Fver_p = v0 Fver_p
    /\ 0 <= v Fcb_x < NMAX
    /\ vsb_obj LPA A (aview A m) S vv fin /\ vb_size vv <= vb_len vv + 4096 /\ 0 <= vb_len vv <= lenb
    /\ vb_buf vv <> VEP /\ vb_buf vv <> wa
    /\ ws1_obj LPA H A (aview A m) wa VEP
    /\ a_live A DATA = Some N
    /\ (forall p k, a_live A0 p = Some k -> p <> S -> ~ parse_blocks v0 vv0 va vi p -> a_live A p = Some k)
    /\ (parse_blocks v0 vv0 va vi (vb_buf vv) \/ a_live A0 (vb_buf vv) = None)
    /\ frames_aged A0 A fa 0
    /\ a_livebytes A = a_livebytes A0 - world_bytes vv0 va vi + 40 + vb_size vv
    /\ (a_tinycred A = a_tinycred A0 /\ a_nlive A + world_nlive va vi = a_nlive A0 /\ a_seccred A0 - cr <= a_seccred A <= a_seccred A0
        /\ a_primcred A0 - (vsb_ppot vv - vsb_ppot vv0) <= a_primcred A <= a_primcred A0)   (* [comment removed for export] *)
    /\ cframe LPA (owned A0) (owned A) (bv_unsigned sp) VEPFIN_STACK (finish_changed H VEP v0 vv0 va vi)
              (vsb_blocks S vv) (aview A0 m0) (aview A m).

  (* [comment removed for export] *)
  Local Ltac touch_all :=
    pose proof (conj HMC (conj HEC (conj HCB (conj HDS (conj HFI (conj HLN (conj AINV00 (conj PW (conj HENV0 (conj TP (conj SP16
      (conj CEIL (conj LO (conj LD0 (conj N0 (conj DRANGE (conj NEDV (conj NEDS (conj NPB (conj LBM0 (conj NLV0 (conj SCC0 (conj PCC0 (conj FY0 K)))))))))))))))))))))))
     ) as ALL_HYPS; clear ALL_HYPS.

  (* [comment removed for export] *)
  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (henv_geom_of_frame LPA A0 m0 md0 H AINV00 (proj1 HENV0)) as HG;
    pose proof HG as (G16 & GCE & GHI); unfold HFSIZE in GHI;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    assert (ES : S = v0 Fvsb) by reflexivity;
    pose proof (world_nlive_nonneg va vi) as WNL;
    unfold_stacks; unfold NMAX, kHighMemBeg in *; all_app_facts.

  (* [comment removed for export] *)
  Local Ltac ufs := unfold_stacks.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="K FY0 SCC0 PCC0 NLV0 LBM0 NPB NEDS NEDV DRANGE N0 LD0 LO CEIL SP16 TP HENV0 PW AINV00 n HLN HFI HDS HCB HEC HMC"] Lemma T6 : forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 xs2 xs3 xs4 xs5 : word) A m md v vr lenb cr,
    jst A m md v vr true lenb 4%nat cr -> cr <= FIN_CRED N ->
    srealizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 VEP) (Z_to_bv 64 (VEP + 8))
                                    a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5
                                    (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 0x909f8) fc None m (seg_rom rsegs)) md) T.
  Proof.
    touch_all. intros until cr. intros J CR. prelims.
    (first [ dand29 J as AINV MI MDF ST FR HENV VEPO VB EVSB EIS EAV EST EEF BLM EVP CBX VOBJ _ _ NEbV NEbw WS1 LD LIVE0 BUF0 FA LB BC CF | destruct J as (AINV & MI & MDF & ST & FR & HENV & VEPO & VB & EVSB & EIS & EAV & EST & EEF & BLM & EVP & CBX
                   & VOBJ & _ & _ & NEbV & NEbw & WS1 & LD & LIVE0 & BUF0 & FA & LB & BC & CF) ]).
    pose proof (as_minv LPA A _ _ AINV) as [_ MH].
    pose proof PW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & APART0 & _).
    destruct (APART0 VEP ltac:(left; reflexivity)) as [NESV _]. destruct (APART0 wa ltac:(right; left; reflexivity)) as [NESw _].
    (* [comment removed for export] *)
    (first [ pose proof (VEPO) as dR_4; dand4 dR_4 as VLV VEPC TAG8 PADS | pose proof VEPO as (VLV & VEPC & TAG8 & PADS) ]). fold_cl_segs.
    (first [ pose proof (PADS) as dR_5; dand7 dR_5 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]).
    unfold vep_cells in VEPC. rewrite EVSB in VEPC.
    (first [ pose proof ((rw_cells_split3 rsegs _ VEP _ 2 (C8 (Z_to_bv 64 S)) VEPC eq_refl)) as dR_6; dand3 dR_6 as VA VM VBk | pose proof (rw_cells_split3 rsegs _ VEP _ 2 (C8 (Z_to_bv 64 S)) VEPC eq_refl) as (VA & VM & VBk) ]). clear VEPC.
    cbn [firstn skipn cells_size csize Nat.add length] in VA, VM, VBk.
    change (Z.of_nat 8) with 8 in VM. change (Z.of_nat 8) with 8 in VBk. replace (VEP + 8 + 8) with (VEP + 16) in VBk by lia.
    (first [ pose proof ((live_geomP LPA A m md VEP _ AINV VLV)) as dR_7; dand7 dR_7 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A m md VEP _ AINV VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    (first [ pose proof ((vsb_obj_geom LPA A m md S vr true AINV VOBJ)) as dR_8; dand11 dR_8 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LPA A m md S vr true AINV VOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    (first [ pose proof (VOBJ) as dR_9; dand6 dR_9 as _ _ LS LBK NESb _ | pose proof VOBJ as (_ & _ & LS & LBK & NESb & _) ]). pose proof (proj1 (proj2 VOBJ)) as VINV. (first [ pose proof (VINV) as dR_10; dand3 dR_10 as Vsz Vlen _ | pose proof VINV as (Vsz & Vlen & _) ]).
    pose proof (as_live_disjoint LPA A m md S 40 VEP 312 AINV LS VLV NESV) as DJS.
    pose proof (as_live_disjoint LPA A m md (vb_buf vr) (vb_size vr) VEP 312 AINV LBK VLV NEbV) as DJB.
    pose proof WS1 as WS1x. (first [ dex2 WS1x as id pad; dand7 WS1x as IDOK PADL _ _ LWA _ _ | dand9 WS1x as id pad IDOK PADL _ _ LWA _ _ | destruct WS1x as (id & pad & IDOK & PADL & _ & _ & LWA & _ & _) ]).
    assert (NEwS : wa <> S) by (intros X; apply NESw; symmetry; exact X).
    assert (NEwB : wa <> vb_buf vr) by (intros X; apply NEbw; symmetry; exact X).
    unfold kHighMemBeg in *. all_app_facts.
    hide DSB. hide DJS. hide DJB. hide BUF0.
    pose proof (munch_refl [(bv_unsigned sp - 8864, bv_unsigned sp); (VEP, VEP + 312)] (aview A m)) as MU.
    pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (WMAPx : mapped (aview A m) (bv_unsigned sp - 8864) 8864).
    { eapply (window_mapped LPA _ lo); [exact ST | exact FR | cbn; lia | exact CEIL | lia | lia]. }
    assert (CFP : client_fp LPA A (aview A m) [(bv_unsigned sp - 8864, bv_unsigned sp); (VEP, VEP + 312)]).
    { cbn. split; [left; split; [lia|]; split; [lia|]; replace (bv_unsigned sp - (bv_unsigned sp - 8864)) with 8864 by lia; exact WMAPx |].
      split; [right; left; exists VEP, 312; split; [exact VLV|lia]| exact I]. }
    hide_neqs.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    zstep. zstep.
    astop AINV MU WM CFP.
    unhide NESV. unhide NEbV. unhide NEwS. unhide NEwB. unhide NESb.
    eapply (HDS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ _ A (VEP + 8) S vr true lo);
      [ exact AINV0 | assumption | reflexivity | exact VM
      | eapply cobj_block; [exact VLV| cbn; intros [X|[X|X]]; [exact (NESV X)| exact (NEbV X)| exact X] | lia | lia]
      | rewrite Z.add_mod, (mod8_of_mod16 VEP VEP16) by lia; reflexivity
      | lia
      | exact VOBJ | exact TP
      | rewrite unsigned_lit by lia; replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) by lia; apply align16_add; [exact SP16|reflexivity]
      | rewrite unsigned_lit by lia; exact ST | exact CEIL
      | rewrite unsigned_lit by lia; ufs; lia | ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 mc mdc. cbv zeta.
    intros AINV1 MI1 MDF1 FRS1 LB1 TC1 NL1 SC1 PC1 ST1 PSC DEADS DEADB LIVEq CF1.   (* [comment removed for export] *)
    rewrite unsigned_lit in ST1, CF1 by lia. ufs.
    (* [comment removed for export] *)
    assert (LVEP1 : a_live A1 VEP = Some 312) by (rewrite (LIVEq VEP (not_eq_sym NESV) (not_eq_sym NEbV)); exact VLV).
    assert (LWA1 : a_live A1 wa = Some 40) by (rewrite (LIVEq wa NEwS NEwB); exact LWA).
    assert (HENV1 : henv_ok LPA VIA H A1 (aview A1 mc)).
    { eapply (henv_ok_acall_gen H A A1); [exact AINV0| exact CF1| exact HENV| keeplia CEIL LO| intros ff k age HF; exists age; rewrite (FRS1 ff); exact HF|].
      intros a [X|[X|X]].
      - exists S, 40. split; [exact LS|]. unfold newblk, blk in X. keeplia X.
      - exists (vb_buf vr), (vb_size vr). split; [exact LBK|]. unfold newblk, blk in X. keeplia X.
      - exists VEP, 312. split; [exact VLV|]. left. keeplia X. }
    pose proof (proj1 HENV) as [ageh HFRh].
    assert (WS1_1 : ws1_obj LPA H A1 (aview A1 mc) wa VEP).
    { pose proof (as_live_disjoint LPA A m md S 40 wa 40 AINV LS LWA (not_eq_sym NEwS)) as DJ1.
      pose proof (as_live_disjoint LPA A m md (vb_buf vr) (vb_size vr) wa 40 AINV LBK LWA (not_eq_sym NEwB)) as DJ2.
      pose proof (as_live_disjoint (Clg:=Clg) LPA A m md wa 40 VEP 312 AINV LWA VLV ltac:(intros X; rewrite X in LWA; rewrite VLV in LWA; discriminate LWA)) as DJ3.
      pose proof (as_frame_blk_disjoint LPA A m md (h_ff H) HCLASS ageh S 40 AINV HFRh LS) as DJfS.
      pose proof (as_frame_blk_disjoint LPA A m md (h_ff H) HCLASS ageh _ _ AINV HFRh LBK) as DJfB.
      pose proof (as_frame_blk_disjoint LPA A m md (h_ff H) HCLASS ageh VEP 312 AINV HFRh VLV) as DJfV.
      change (fsize HCLASS) with 8192 in DJfS, DJfB, DJfV.
      (first [ pose proof ((live_geomP LPA A m md wa _ AINV LWA)) as dR_12; dand5 dR_12 as _ _ WAlo WAhi _ | pose proof (live_geomP LPA A m md wa _ AINV LWA) as (_ & _ & WAlo & WAhi & _) ]). unfold kHighMemBeg in WAlo. all_app_facts.
      pose proof (sh_boundL (Clg:=Clg) S 40 ltac:(keeplia Slo) ltac:(keeplia Slo) ltac:(keeplia Shi)) as SHS. rewrite SHMAX_val in SHS.
      pose proof (sh_boundL (Clg:=Clg) (vb_buf vr) (vb_size vr) ltac:(keeplia Blo) ltac:(keeplia Vsz) ltac:(keeplia Bhi)) as SHB. rewrite SHMAX_val in SHB.
      eapply ws1_obj_ccall; [exact AINV0| exact (proj1 HENV)| exact CF1| exact WS1| keeplia CEIL LO| exact LWA1| exact LVEP1|].
      intros a Ha [X|[X|X]]; unfold h_ws, h_wsbuf, newblk, blk in *;
        [ keeplia Ha X DJ1 DJfS SHS WAlo GCE | keeplia Ha X DJ2 DJfB SHB WAlo GCE | keeplia Ha X DJ3 DJfV ]. }
    hide_neqs.
    (* [comment removed for export] *)
    pose proof (crange_block (Clg:=Clg) (L:=LPA) A _ _ VEP 312 VEP 8 AINV0 VLV ltac:(keeplia VEPlo) ltac:(keeplia VEPlo) ltac:(keeplia VEPlo)) as CRA.
    pose proof (crange_block (Clg:=Clg) (L:=LPA) A _ _ VEP 312 (VEP + 16) 296 AINV0 VLV ltac:(keeplia VEPlo) ltac:(keeplia VEPlo) ltac:(keeplia VEPlo)) as CRB.
    pose proof (crange_stack (Clg:=Clg) (L:=LPA) A _ _ _ (bv_unsigned sp - 64) 64 AINV0 ltac:(keeplia ACV CEIL LO) ltac:(keeplia SPR)
                  (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FR ltac:(off_image_solve LPA))) as CRF.
    pose proof (sh_boundL (Clg:=Clg) S 40 ltac:(keeplia Slo) ltac:(keeplia Slo) ltac:(keeplia Shi)) as SHS. rewrite SHMAX_val in SHS.
    pose proof (sh_boundL (Clg:=Clg) (vb_buf vr) (vb_size vr) ltac:(keeplia Blo) ltac:(keeplia Vsz) ltac:(keeplia Bhi)) as SHB. rewrite SHMAX_val in SHB.
    clear VM WS1 ST. unhide DJS. unhide DJB. acall_xfer CF1. hide DJS. hide DJB. clear CRA CRB CRF.
    (* [comment removed for export] *)
    assert (VEPC1 : rw_cells rsegs (aview A1 mc) VEP (vep_cells (fupd v Fvsb 0) tag q)).
    { rewrite <- vep_cells_vsb. unfold vep_cells. rewrite ?EVSB. cbn [firstn skipn].
      lazymatch type of VA with rw_cells _ _ _ ?pre => apply (rw_cells_join3 rsegs (aview A1 mc) VEP pre); [exact VA| exact PSC|] end.
      eapply rwc_eq; [exact VBk| cbn [cells_size csize Nat.add length]; change (Z.of_nat 8) with 8; lia]. }
    clear VA VBk PSC.
    pose proof (munch_refl [(bv_unsigned sp - 8864, bv_unsigned sp); (VEP, VEP + 312)] (aview A1 mc)) as MU1.
    pose proof (wmono_refl rsegs (aview A1 mc)) as WM1.
    assert (WMAP1 : mapped (aview A1 mc) (bv_unsigned sp - 8864) 8864).
    { eapply (window_mapped LPA _ lo); [exact ST1 | exact FR | cbn; lia | exact CEIL | lia | lia]. }
    assert (CFP1 : client_fp LPA A1 (aview A1 mc) [(bv_unsigned sp - 8864, bv_unsigned sp); (VEP, VEP + 312)]).
    { cbn. split; [left; split; [lia|]; split; [lia|]; replace (bv_unsigned sp - (bv_unsigned sp - 8864)) with 8864 by lia; exact WMAP1 |].
      split; [right; left; exists VEP, 312; split; [exact LVEP1|lia]| exact I]. }
    pose proof (as_minv LPA A1 _ _ AINV1) as [_ MH1].
    ago AINV1. fold_cl_segs. fix_ret_pc.
    (* [comment removed for export] *)
    zstep. do 9 zstep.
    try replace (bv_unsigned sp - 64 + 64) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    release_frame FR ST1 (bv_unsigned sp).
    zstep.
    astop AINV1 MU1 WM1 CFP1.
    unhide BUF0.
    lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mf _) ?mdf) _ =>
      assert (MP : mapped (aview A1 mf) (bv_unsigned sp - 8864) 8864) by (eapply (stk_mapped (L:=LPA)); [exact ST1 | exact CEIL | lia | lia]);
      eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 A1 mf mdf (fupd v Fvsb 0) vr);
      [ assumption | assumption
      | eapply amd_frame_trans; [exact MDF|]; eapply amd_frame_sbm_l; [exact SBM | exact MH |]; eapply amd_frame_sbm_r; [exact MDF1 | exact SBM0]
      | exact ST1
      | exact HENV1
      | split; [exact LVEP1|]; split; [exact VEPC1 |split; [exact TAG8| exact PADS]]
      | exact WS1_1
      | left; reflexivity
      | intros p k L0 NS NP; rewrite (LIVEq p NS); [apply (LIVE0 p k L0 NS NP)|];
        intros ->; destruct BUF0 as [E|E]; [exact (NP E)| rewrite E in L0; discriminate L0]
      | eapply (frames_aged_trans A0 A A1 4%nat 0%nat 0%nat 0%nat); [exact FA| apply frames_same_aged; exact FRS1]
      | cbn [Z.eqb]; keeplia LB1 LB
      | rewrite TC1; exact (proj1 BC)
      | cbn [Z.eqb]; pose proof (proj1 (proj2 BC)) as BCn; keeplia NL1 BCn
      | rewrite SC1; pose proof (proj2 (proj2 BC)) as BCs; keeplia BCs CR
      | rewrite PC1; pose proof (proj2 (proj2 (proj2 BC))) as BCp; match type of BCp with _ - (vsb_ppot ?x - _) <= _ <= _ => pose proof (vsb_ppot_range x) as PPR end; unfold PPOT_CAP in *; keeplia BCp PPR (* [comment removed for export] *)
      | ] end.
    (* [comment removed for export] *)
    lazymatch goal with |- cframe _ _ _ _ _ _ _ _ (aview ?Ay ?mf) =>
      lazymatch type of CF1 with cframe _ _ _ _ _ _ _ ?vpre _ =>
      assert (CF2 : cframe LPA (owned A) (owned A1) (bv_unsigned sp) 8864
                      (fun a => newblk S 40 a \/ newblk (vb_buf vr) (vb_size vr) a \/ VEP + 8 <= a < VEP + 8 + 8) nowhere vpre (aview A1 mf))
        by (eapply (cframe_extend LPA _ _ _ _ _ _ _ _ _ _ vpre vpre (aview A1 mf) (aview A1 mf) [] []);
            [ apply munch_refl | intros a _ X; exfalso; apply X; exact I | exact CF1 | lia | lia
            | intros a X; exact X | intros a X; destruct X | apply munch_refl | intros a _ X; exfalso; apply X; exact I
            | eapply (stk_mapped (L:=LPA)); [exact ST1 | exact CEIL | lia | lia] ]);
      eapply (cframe_seq LPA _ _ _ _ _ _ _ _ _ _ _ _ _ (aview A0 m0) vpre (aview A1 mf) CF CF2);
        [ lia | lia | eapply (stk_mapped (L:=LPA)); [exact ST1 | exact CEIL | lia | lia]
        | intros a X; exact X
        | intros a [X|[X|X]]; [left; left; exact X| left; right; exact X| right; left; unfold blk; lia]
        | intros a [X _]; exfalso; apply X; reflexivity ]
      end end.
  Qed.
  (* [comment removed for export] *)
  Local Ltac OWN a Ha NO :=
    cbn [outside] in NO; rewrite ERRNOA_eq; unfold vsb_blocks; cbn [vb_buf vb_size vsb_set_flags];
    lazymatch goal with |- _ \/ finish_changed _ ?VEPx _ _ _ _ a \/ (newblk ?Sx 40 a \/ newblk ?bx ?szx a) \/ _ =>
      let C := fresh "CASES" in
      assert (C : (bv_unsigned sp - 8864 <= a < bv_unsigned sp) \/ (VEPx <= a < VEPx + 312) \/ (Sx <= a < Sx + 40) \/
                  (bx <= a < bx + szx) \/ (ERRNOA <= a < ERRNOA + 4) \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
        by (try (generalize alloc_ceiling_val); clear - Ha NO; try pose proof alloc_ceiling_val as ACV__; unfold ERRNOA in *; lia);
      clear NO;
      destruct C as [X|[X|[X|[X|[X|X]]]]];
      [ left; exact X
      | right; left; unfold finish_changed; left; unfold blk; split; [| exact X];
        match goal with L : 17594333495296 <= VEPx |- _ => try (generalize alloc_ceiling_val); clear - L; try pose proof alloc_ceiling_val as ACV__; lia end
      | right; left; unfold finish_changed; right; left; unfold vsb_blocks; left; unfold newblk, blk; left;
        try match goal with E : Sx = _ |- _ => rewrite <- E end; split; [| exact X];
        match goal with L : 17594333495296 <= Sx |- _ => try (generalize alloc_ceiling_val); clear - L; try pose proof alloc_ceiling_val as ACV__; lia end
      | right; right; left; right; unfold newblk, blk; left; split; [| exact X];
        first [ match goal with L : 17594333495296 <= bx |- _ => clear - L; lia end | match goal with L : context [ (4096 <= bx)%Z ] |- _ => clear - L; lia end ]   (* [comment removed for export] *)
      | right; right; right; exact X
      | right; left; unfold finish_changed; right; right; right; right; exact X ]
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="K FY0 SCC0 PCC0 NLV0 LBM0 NPB NEDS NEDV DRANGE N0 LD0 LO CEIL SP16 TP HENV0 PW AINV00 n HLN HFI HDS HCB HEC HMC"] Lemma T5 : forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) A m md v vv lenb cr,
    jst A m md v vv false lenb 4%nat cr -> cr <= FIN_CRED N ->
    srealizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 VEP) (Z_to_bv 64 (VEP + 24))
                                    a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (VEP + 144)) (Z_to_bv 64 (VEP + 304)) (Z_to_bv 64 (VEP + 48))
                                    (Z_to_bv 64 (VEP + 40)) (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 0x90950) fc None m (seg_rom rsegs)) md) T.
  Proof.
    touch_all. intros until cr. intros J CR. prelims.
    (first [ dand29 J as AINV MI MDF ST FR HENV VEPO VB EVSB EIS EAV EST EEF BLM EVP CBX VOBJ SZB LENB NEbV NEbw WS1 LD LIVE0 BUF0 FA LB BC CF | destruct J as (AINV & MI & MDF & ST & FR & HENV & VEPO & VB & EVSB & EIS & EAV & EST & EEF & BLM & EVP & CBX
                   & VOBJ & SZB & LENB & NEbV & NEbw & WS1 & LD & LIVE0 & BUF0 & FA & LB & BC & CF) ]).
    unfold NMAX in CBX.
    pose proof (as_minv LPA A _ _ AINV) as [_ MH].
    pose proof PW as (_ & _ & _ & _ & BEF0 & _ & _ & _ & _ & _ & _ & APART0 & _).
    destruct (APART0 VEP ltac:(left; reflexivity)) as [NESV _]. destruct (APART0 wa ltac:(right; left; reflexivity)) as [NESw _].
    (* [comment removed for export] *)
    (first [ pose proof (VEPO) as dR_14; dand4 dR_14 as VLV VEPC TAG8 PADS | pose proof VEPO as (VLV & VEPC & TAG8 & PADS) ]). fold_cl_segs.
    (first [ pose proof (PADS) as dR_15; dand7 dR_15 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]).
    (first [ pose proof ((live_geomP LPA A m md VEP _ AINV VLV)) as dR_16; dand7 dR_16 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A m md VEP _ AINV VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    pose proof (mod8_of_mod16 VEP VEP16) as V8.
    (first [ pose proof ((vsb_obj_geom LPA A m md S vv false AINV VOBJ)) as dR_17; dand11 dR_17 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LPA A m md S vv false AINV VOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    pose proof (mod8_of_mod16 S S16) as S8. pose proof (mod8_of_mod16 (vb_buf vv) B16) as B8.
    pose proof VOBJ as VOBJx. vsb_open VOBJx. (first [ dex1 VBUF as bs; dand3 VBUF as U8 LBS _ | dand4 VBUF as bs U8 LBS _ | destruct VBUF as (bs & U8 & LBS & _) ]). fold_cl_segs.
    pose proof VINV as VINVx. (first [ dand9 VINVx as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm Vsm | destruct VINVx as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm & Vsm) ]).
    pose proof (as_live_disjoint LPA A m md S 40 VEP 312 AINV VLS VLV NESV) as DJS.
    pose proof (as_live_disjoint LPA A m md (vb_buf vv) (vb_size vv) VEP 312 AINV VLB VLV NEbV) as DJB.
    pose proof WS1 as WS1x. (first [ dex2 WS1x as id pad; dand7 WS1x as IDOK PADL _ _ LWA _ _ | dand9 WS1x as id pad IDOK PADL _ _ LWA _ _ | destruct WS1x as (id & pad & IDOK & PADL & _ & _ & LWA & _ & _) ]).
    assert (NEwS : wa <> S) by (intros X; apply NESw; symmetry; exact X).
    assert (NEwB : wa <> vb_buf vv) by (intros X; apply NEbw; symmetry; exact X).
    (first [ pose proof ((live_geomP LPA A m md wa _ AINV LWA)) as dR_21; dand7 dR_21 as _ _ WAlo WAhi _ _ _ | pose proof (live_geomP LPA A m md wa _ AINV LWA) as (_ & _ & WAlo & WAhi & _ & _ & _) ]).
    pose proof (as_live_disjoint LPA A m md S 40 wa 40 AINV VLS LWA (not_eq_sym NEwS)) as DJ1.
    pose proof (as_live_disjoint LPA A m md (vb_buf vv) (vb_size vv) wa 40 AINV VLB LWA (not_eq_sym NEwB)) as DJ2.
    pose proof (as_live_disjoint (Clg:=Clg) LPA A m md wa 40 VEP 312 AINV LWA VLV ltac:(intros X; rewrite X in LWA; rewrite VLV in LWA; discriminate LWA)) as DJ3.
    pose proof (proj1 HENV) as [ageh HFRh].
    pose proof (as_frame_blk_disjoint LPA A m md (h_ff H) HCLASS ageh S 40 AINV HFRh VLS) as DJfS.
    pose proof (as_frame_blk_disjoint LPA A m md (h_ff H) HCLASS ageh _ _ AINV HFRh VLB) as DJfB.
    pose proof (as_frame_blk_disjoint LPA A m md (h_ff H) HCLASS ageh VEP 312 AINV HFRh VLV) as DJfV.
    pose proof (as_frame_blk_disjoint LPA A m md (h_ff H) HCLASS ageh wa 40 AINV HFRh LWA) as DJfW.
    change (fsize HCLASS) with 8192 in DJfS, DJfB, DJfV, DJfW.
    unfold kHighMemBeg in *. all_app_facts.
    pose proof (sh_boundL (Clg:=Clg) S 40 ltac:(lia) ltac:(lia) ltac:(lia)) as SHS. rewrite SHMAX_val in SHS.
    pose proof (sh_boundL (Clg:=Clg) (vb_buf vv) (vb_size vv) ltac:(lia) ltac:(lia) ltac:(lia)) as SHB. rewrite SHMAX_val in SHB.
    pose proof (sh_boundL (Clg:=Clg) VEP 312 ltac:(lia) ltac:(lia) ltac:(exact VEPhi)) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    pose proof (sh_boundL (Clg:=Clg) (h_ff H) 8192 ltac:(lia) ltac:(lia) ltac:(unfold HFSIZE in GHI; lia)) as SHF.
    rewrite SHMAX_val in SHF. change ((8192 + 7) / 8) with 1024 in SHF.
    pose proof (sh_mono 17594333495296 S ltac:(lia)) as SHSlo. change (sh 17594333495296) with 2201439137792 in SHSlo.
    pose proof (sh_mono 17594333495296 VEP ltac:(lia)) as SHVlo. change (sh 17594333495296) with 2201439137792 in SHVlo.
    unhide_app_of (vb_buf vv).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINV VLV) as SHV0. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV0.
    remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV0.
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity).
    pose proof (as_live_shadow LPA _ _ _ S 40 AINV VLS) as SHSr. pose proof (as_live_shadow LPA _ _ _ _ _ AINV VLB) as SHBu. fold_cl_segs. fold_aview.
    pose proof (shpat_length 40 ltac:(lia)) as LSH40. pose proof (shpat_length (vb_size vv) ltac:(lia)) as LSHB.
    pose proof (cenv_intro A m md AINV) as CEx.
    pose proof (map_cells_of_consts _ (proj1 CEx)) as MC. fold_aview.
    (* [comment removed for export] *)
    (first [ pose proof (VB) as dR_22; dand5 dR_22 as EVC EVCB EVCBP EVDZ EVURL | pose proof VB as (EVC & EVCB & EVCBP & EVDZ & EVURL) ]). cbn [vi_cb vi_url VIA] in EVCB, EVURL.
    pose proof VEPC as VEPCF. hide VEPCF.
    unfold vep_cells in VEPC. rewrite EVSB, EVC, EVCB, EVCBP in VEPC.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 8864, bv_unsigned sp); (VEP, VEP + 312); (S, S + 40); (vb_buf vv, vb_buf vv + vb_size vv); (ERRNOA, ERRNOA + 4); (h_vsc H + 1304, h_vsc H + 1320)] (aview A m)) as MU.
    pose proof (munch_refl [(bv_unsigned sp - 8864, bv_unsigned sp); (VEP, VEP + 312); (S, S + 40); (vb_buf vv, vb_buf vv + vb_size vv); (ERRNOA, ERRNOA + 4)] (aview A m)) as MUh.
    pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (WMAPx : mapped (aview A m) (bv_unsigned sp - 8864) 8864).
    { eapply (window_mapped LPA _ lo); [exact ST | exact FR | cbn; lia | exact CEIL | lia | lia]. }
    assert (CFP : client_fpx A (aview A m) [(bv_unsigned sp - 8864, bv_unsigned sp); (VEP, VEP + 312); (S, S + 40); (vb_buf vv, vb_buf vv + vb_size vv); (ERRNOA, ERRNOA + 4); (h_vsc H + 1304, h_vsc H + 1320)]).
    { cbn. split; [left; split; [lia|]; split; [lia|]; replace (bv_unsigned sp - (bv_unsigned sp - 8864)) with 8864 by lia; exact WMAPx |].
      split; [right; left; exists VEP, 312; split; [exact VLV|lia]|].
      split; [right; left; exists S, 40; split; [exact VLS|lia]|].
      split; [right; left; exists (vb_buf vv), (vb_size vv); split; [exact VLB|lia]|].
      split; [right; right; right; right; rewrite <- ERRNOA_eq; exact (img_ivl_errno (L:=LPA))|].
      split; [| exact I]. right; right; left. exists (h_ff H), HCLASS, ageh. split; [exact HFRh|]. unfold h_vsc. change (fsize HCLASS) with 8192. lia. }
    pose proof (got_vsc_cell (aview A m) (proj1 CEx)) as GOTV. unfold GOTA_vsc in GOTV. cbn [vi_bss_vsc VIA] in GOTV. fold_cl_segs.
    unfold ERRNOA in MU, MUh.
    (* [comment removed for export] *)
    hide DSB. hide DJ1. hide DJ2. hide DJ3. hide DJS. hide DJB. hide DJfS. hide DJfB. hide DJfV. hide DJfW. hide BUF0. hide Verr. hide BEF0.
    hide SHSr. hide SHBu. hide_neqs.
    (* [comment removed for export] *)
    assert (VINV' : vsb_inv (vsb_set_flags vv VSB_FLAGS_FIN) true).
    { try (generalize alloc_ceiling_val); clear - VINV; try pose proof alloc_ceiling_val as ACV__. unfold vsb_inv in *. cbn [vb_size vb_len vb_error vb_indent vb_flags vb_buf vsb_set_flags] in *.
      unfold VSB_FLAGS_FIN, VSB_FLAGS_LIVE in *. lia. }
    assert (VOBJT : forall mx, rw_cells rsegs mx S (vsb_cells (vsb_set_flags vv VSB_FLAGS_FIN)) ->
                    u8arr rsegs mx (vb_buf vv) (upd bs (Z.to_nat (vb_len vv)) (Z_to_bv 8 0)) ->
                    vsb_obj LPA A mx S (vsb_set_flags vv VSB_FLAGS_FIN) true).
    { intros mx C U. split; [exact C|]. split; [exact VINV'|]. split; [exact VLS|]. split; [exact VLB|]. split; [unhide VNE; exact VNE|].
      exists (upd bs (Z.to_nat (vb_len vv)) (Z_to_bv 8 0)). split; [exact U|]. split; [rewrite upd_length; exact LBS|].
      intros _. cbn [vb_len vsb_set_flags]. apply nth_error_upd_same. lia. }
    assert (JT : forall m1 md1, ainv A m1 md1 -> amd_frame md0 md1 -> mem_inv rsegs (aview A m1) ->
              munch [(bv_unsigned sp - 8864, bv_unsigned sp); (VEP, VEP + 312); (S, S + 40); (vb_buf vv, vb_buf vv + vb_size vv); (6193972, 6193972 + 4); (h_vsc H + 1304, h_vsc H + 1320)] (aview A m) (aview A m1) ->
              wmono rsegs (aview A m) (aview A m1) ->
              stk rsegs (aview A m1) lo (bv_unsigned sp - 64) ->
              rw_cells rsegs (aview A m1) (bv_unsigned sp - 64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
              rw_cells rsegs (aview A m1) VEP (vep_cells v tag q) ->
              rw_cells rsegs (aview A m1) S (vsb_cells (vsb_set_flags vv VSB_FLAGS_FIN)) ->
              u8arr rsegs (aview A m1) (vb_buf vv) (upd bs (Z.to_nat (vb_len vv)) (Z_to_bv 8 0)) ->
              glob_ok LPA VIA H (aview A m1) ->
              jst A m1 md1 v (vsb_set_flags vv VSB_FLAGS_FIN) true lenb 4%nat cr).
    { intros m1 md1 AIx MDx MIx MUx WMx STx FRx VEPCx Cx Ux GLx.
      split; [exact AIx|]. split; [exact MIx|]. split; [exact MDx|]. split; [exact STx|]. split; [exact FRx|].
      split. { split; [exact (proj1 HENV)|]. split; [exact GLx|]. split.
               - eapply (hobj_ok_munch LPA); [exact (proj1 (proj2 (proj2 HENV)))| exact MUx| exact WMx|].
                 intros a Ha. unfold h_vc, h_wrk, h_req, h_resp, h_hd, h_vsc in *. cbn [outside]. keeplia Ha DJfS DJfB DJfV GHI GCE ACV CEIL LO.
               - eapply (hshadow_munch LPA); [exact (proj2 (proj2 (proj2 HENV)))| exact MUx| exact HG|].
                 intros x Hx. change (HFSIZE / 8) with 1024 in Hx. unfold h_vsc. cbn [outside]. keeplia Hx SHF GCE VEPlo Slo Blo ACV CEIL LO. }
      split. { split; [exact VLV|]. split; [exact VEPCx|]. split; [exact TAG8| exact PADS]. }
      split; [exact VB|]. split; [exact EVSB|]. split; [exact EIS|]. split; [exact EAV|]. split; [exact EST|]. split; [exact EEF|].
      split; [exact BLM|]. split; [exact EVP|]. split; [exact CBX|].
      split; [exact (VOBJT _ Cx Ux)|]. split; [exact SZB|]. split; [exact LENB|]. split; [unhide NEbV; exact NEbV|]. split; [unhide NEbw; exact NEbw|].
      split. { eapply ws1_obj_munch; [exact WS1| exact MUx| exact WMx|]. intros a [Ha|[Ha|Ha]]; unfold h_ws, h_wsbuf, h_vsc in *; cbn [outside];
               [ keeplia Ha DJfS DJfB DJfV GHI GCE ACV CEIL LO | keeplia Ha DJfS DJfB DJfV GHI GCE ACV CEIL LO
               | keeplia Ha DJ1 DJ2 DJ3 DJfW WAlo WAhi GCE ACV CEIL LO ]. }
      split; [exact LD|]. split; [exact LIVE0|]. split; [unhide BUF0; exact BUF0|]. split; [exact FA|]. split; [exact LB|]. split; [exact BC|].
      ufs.
      eapply (cframe_after _ _ _ _ _ _ (aview A0 m0) (aview A m) (aview A m1)); [exact CF| exact MUx| intros a Ha NO; OWN a Ha NO |].
      eapply (window_mapped LPA _ lo); [exact STx | exact FRx | cbn; lia | exact CEIL | lia | lia]. }
    pose proof MI as MIw. pose proof ST as STw. clear ST.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    vchk SHV0 EzsV 8 0. vchk SHV0 EzsV 8 0. vchk SHV0 EzsV 8 0.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    unhide VEPCF. unhide DJS. unhide DJB. (first [ pose proof (HENV) as dR_23; dand4 dR_23 as _ GLOB HOBJ HSH | pose proof HENV as (_ & GLOB & HOBJ & HSH) ]). pose proof (vsb_cells_size vv) as VSZ.
    try clear VEPC. try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_VEPCF); icall (HCB VEP v tag q H 0 lo) by
      (rewrite ?unsigned_lit by lia;
       lazymatch goal with
       | |- @eq (bv _) _ _ => reflexivity
       | |- rw_cells _ _ _ _ => exact VEPCF
       | |- length _ = _ => exact TAG8
       | |- vep_pads_wf _ => exact PADS
       | |- hobj_ok _ _ _ _ => exact HOBJ
       | |- hshadow _ _ _ => exact HSH
       | |- henv_geom LPA _ => exact HG
       | |- cenv _ => exact CEx
       | |- shadowed _ _ _ _ => exists VEP, 312; split; [pose proof SHV0 as T__; rewrite EzsV in T__; exact T__|]; lia
       | |- stk _ _ _ _ => exact STw
       | |- mem_inv _ _ => assumption
       | |- _ => try unhide DJfV; unfold kHighMemBeg, HFSIZE, CB_STACK; lia
       end).
    clear GLOB HOBJ HSH. try clear STw. try clear VEPCF. try clear VEPC. hide DJS. hide DJB.
    lazymatch goal with X : stk _ ?mq _ _ |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename X into STq end.
    lazymatch goal with X : rw_cells _ ?mq VEP (vep_cells _ tag q) |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename X into VEPC1 end.
    rewrite (vep_cells_ext v (fupd v Fcb_x (v Fcb_x + 0)) tag q (fupd_cbx0 v)) in VEPC1.
    pose proof VEPC1 as VEPC. pose proof VEPC1 as VEPCF. clear VEPC1. hide VEPCF.
    unfold vep_cells in VEPC. rewrite EVSB, EVC, EVCB, EVCBP in VEPC.
    (* [comment removed for export] *)
    zstep. vchk SHV0 EzsV 8 0. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => destruct (rw_errno_any mx) as [e0 ERR] end.
    unhide DSB. unhide DJS. unhide DJB. unhide DJfS. unhide DJfB.
    (* [comment removed for export] *)
    unhide SHSr. unhide SHBu.
    eapply (bytes_at_munch LPA) in SHSr; [| exact MUh | rewrite LSH40; intros a__ Ha__; cbn; lia].
    eapply (bytes_at_munch LPA) in SHBu; [| exact MUh | rewrite LSHB; intros a__ Ha__; cbn; lia].
    fold_cl_segs.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_ERR); icall (HFI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ S vv bs e0 lo) by
      (rewrite ?unsigned_lit by lia;
       lazymatch goal with
       | |- @eq (bv _) _ _ => first [reflexivity | exact TP]
       | |- rw_cells _ _ _ (vsb_cells _) => exact VSBC
       | |- rw_cells _ _ _ [C4 _] => exact ERR
       | |- u8arr _ _ _ _ => exact U8
       | |- vsb_inv _ _ => exact VINV
       | |- Z.of_nat _ = _ => exact LBS
       | |- shadowed _ _ _ 40 => exists S, 40; split; [exact SHSr|]; split; [exact S8| lia]
       | |- shadowed _ _ _ (vb_size _) => exists (vb_buf vv), (vb_size vv); split; [exact SHBu|]; split; [exact B8| lia]
       | |- shadowed _ _ _ 4 => apply errno_shadowed; refine (proj1 (cenv_munch _ _ _ CEx MUh _));
                                     repeat (apply Forall_cons; [unfold const_free_ivl, CONSTS_TOP; cbn; lia|]); apply Forall_nil
       | |- cenv _ => eapply cenv_munch; [exact CEx| exact MUh| repeat (apply Forall_cons; [unfold const_free_ivl, CONSTS_TOP; cbn; lia|]); apply Forall_nil]
       | |- _ \/ _ => exact DSB
       | |- stk _ _ _ _ => exact STq
       | |- mem_inv _ _ => assumption
       | |- _ => first [assumption | unfold kHighMemBeg, FINISH_STACK, ASSERT_STACK; lia]
       end).
    hide DSB. hide DJS. hide DJB. hide DJfS. hide DJfB.
    try clear VSBC. try clear U8. try clear ERR. try clear STq.
    lazymatch goal with X : rw_cells _ ?mq S (vsb_cells _) |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename X into VSBC end.
    lazymatch goal with X : u8arr _ ?mq (vb_buf _) _ |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename X into U8 end.
    try match goal with X : rw_cells _ _ 6193972 _ |- _ => clear X end.
    pose proof (vsb_cells_size (vsb_set_flags vv VSB_FLAGS_FIN)) as VSZ'.
    lazymatch goal with X : stk _ ?mq _ _ |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename X into STq end.
    (* [comment removed for export] *)
    unhide Verr. pose proof Verr as E0.
    - (* [comment removed for export] *)
      rewrite E0. change (vsb_result 0 0) with 0.
      zstep. kdead.
      (* [comment removed for export] *)
      vrechk SHV0 EzsV (VEP + 8) 8 0. zstep. zstep.
      icall (VSB_len_w HLN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ S (vsb_set_flags vv VSB_FLAGS_FIN) true lo) by
        (rewrite ?unsigned_lit by lia;
         lazymatch goal with
         | |- @eq (bv _) _ _ => reflexivity
         | |- rw_cells _ _ _ (vsb_cells _) => exact VSBC
         | |- vsb_inv _ _ => exact VINV'
         | |- shadowed _ _ _ _ => exists S, 40; split; [exact SHSr|]; split; [exact S8| lia]
         | |- cenv _ => eapply cenv_munch; [exact CEx| exact MUh| repeat (apply Forall_cons; [unfold const_free_ivl, CONSTS_TOP; cbn; lia|]); apply Forall_nil]
         | |- stk _ _ _ _ => exact STq
         | |- mem_inv _ _ => assumption
         | |- _ => first [assumption | unfold OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9.inmem_range, kHighMemBeg; lia]
         end).
      try clear STq.
      lazymatch goal with X : stk _ ?mq _ _ |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename X into STq end.
      replace (vsb_result (vb_error (vsb_set_flags vv VSB_FLAGS_FIN)) (vb_len (vsb_set_flags vv VSB_FLAGS_FIN))) with (vb_len vv)
        by (cbn [vb_error vb_len vsb_set_flags]; rewrite E0; reflexivity).
      (* [comment removed for export] *)
      rewrite EEF in VEPC. unhide BEF0. destruct BEF0 as [EF | EF]; rewrite EF in VEPC.
      + (* [comment removed for export] *)
        zstep. vchk SHV0 EzsV 4 0. zstep. zstep. kdead2.
        astopx AINV MU WM CFP.
        lazymatch goal with VEPCx : rw_cells _ (aview ?Ax ?m1) VEP _ |- srealizes _ (mkCfg (MS _ _ _ _ _ ?m1 _) ?md1) _ =>
          eapply (T6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A m1 md1 v (vsb_set_flags vv VSB_FLAGS_FIN) lenb cr); [| exact CR];
          eapply JT; [ exact AINV0 | eapply amd_frame_trans; [exact MDF| apply amd_frame_sbm; [exact SBM| exact MH]] | assumption
                     | exact MU | exact WM | exact STq | exact FR
                     | unfold vep_cells; rewrite EVSB, EVC, EVCB, EVCBP, EEF, EF; exact VEPCx
                     | exact VSBC | exact U8 | ] end.
        eapply glob_ok_munch; [exact (proj1 (proj2 HENV))| exact MUh| exact WM|].
        intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_cp, h_vsc in Ha__; cbn; keeplia Ha__ DJfV DJfS DJfB GHI GCE VEPlo Slo Blo ACV CEIL LO.
      + zstep. vchk SHV0 EzsV 4 0. zstep. zstep. kdead.
        (* [comment removed for export] *)
        zstep. if_cases KL; zify_cond KL.
        * (* [comment removed for export] *)
          astopx AINV MU WM CFP.
          lazymatch goal with VEPCx : rw_cells _ (aview ?Ax ?m1) VEP _ |- srealizes _ (mkCfg (MS _ _ _ _ _ ?m1 _) ?md1) _ =>
            eapply (T6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A m1 md1 v (vsb_set_flags vv VSB_FLAGS_FIN) lenb cr); [| exact CR];
            eapply JT; [ exact AINV0 | eapply amd_frame_trans; [exact MDF| apply amd_frame_sbm; [exact SBM| exact MH]] | assumption
                       | exact MU | exact WM | exact STq | exact FR
                       | unfold vep_cells; rewrite EVSB, EVC, EVCB, EVCBP, EEF, EF; exact VEPCx
                       | exact VSBC | exact U8 | ] end.
          eapply glob_ok_munch; [exact (proj1 (proj2 HENV))| exact MUh| exact WM|].
          intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_cp, h_vsc in Ha__; cbn; keeplia Ha__ DJfV DJfS DJfB GHI GCE VEPlo Slo Blo ACV CEIL LO.
        * (* [comment removed for export] *)
          vrechk SHV0 EzsV (VEP + 8) 8 0. zstep. zstep. do 9 zstep.
          try replace (bv_unsigned sp - 64 + 64) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
          release_frame FR STq (bv_unsigned sp).
          zstep.
          astopx AINV MU WM CFP.
          lazymatch goal with VEPCx : rw_cells _ (aview ?Ax ?m1) VEP _ |- srealizes _ (mkCfg (MS _ _ _ _ _ ?m1 _) ?md1) _ =>
            assert (MP : mapped (aview A m1) (bv_unsigned sp - 8864) 8864) by (eapply (stk_mapped (L:=LPA)); [exact STq | exact CEIL | keeplia LO | keeplia LO SPR]);
            eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ S A m1 md1 v (vsb_set_flags vv VSB_FLAGS_FIN));
            [ exact AINV0 | assumption | eapply amd_frame_trans; [exact MDF| apply amd_frame_sbm; [exact SBM| exact MH]] | exact STq
            | split; [exact (proj1 HENV)|]; split; [| split];
              [ eapply glob_ok_munch; [exact (proj1 (proj2 HENV))| exact MUh| exact WM|];
                intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_cp, h_vsc in Ha__; cbn; keeplia Ha__ DJfV DJfS DJfB GHI GCE VEPlo Slo Blo ACV CEIL LO
              | eapply (hobj_ok_munch LPA); [exact (proj1 (proj2 (proj2 HENV)))| exact MU| exact WM|];
                intros a__ Ha__; unfold h_vc, h_wrk, h_req, h_resp, h_hd, h_vsc in *; cbn [outside]; keeplia Ha__ DJfV DJfS DJfB GHI GCE ACV CEIL LO
              | eapply (hshadow_munch LPA); [exact (proj2 (proj2 (proj2 HENV)))| exact MU| exact HG|];
                intros x__ Hx__; change (HFSIZE / 8) with 1024 in Hx__; unfold h_vsc; cbn [outside]; keeplia Hx__ SHF GCE VEPlo Slo Blo ACV CEIL LO ]
            | split; [exact VLV|]; split; [unfold vep_cells; rewrite EVSB, EVC, EVCB, EVCBP, EEF, EF; exact VEPCx| split; [exact TAG8| exact PADS]]
            | eapply ws1_obj_munch; [exact WS1| exact MU| exact WM|]; intros a__ [Ha__|[Ha__|Ha__]]; unfold h_ws, h_wsbuf, h_vsc in *; cbn [outside];
              [ keeplia Ha__ DJfS DJfB DJfV GHI GCE ACV CEIL LO | keeplia Ha__ DJfS DJfB DJfV GHI GCE ACV CEIL LO
              | keeplia Ha__ DJ1 DJ2 DJ3 DJfW WAlo WAhi GCE ACV CEIL LO ]
            | | | exact FA | cbn [vb_size vsb_set_flags]; destruct (Z.eqb_spec S 0) as [ES0|NS0]; [keeplia ES0 Slo| keeplia LB]
            | exact (proj1 BC)
            | pose proof (proj1 (proj2 BC)) as BCn; destruct (Z.eqb_spec S 0) as [ES0|NS0]; [keeplia ES0 Slo| keeplia BCn]
            | pose proof (proj2 (proj2 BC)) as BCs; keeplia BCs CR
            | pose proof (proj2 (proj2 (proj2 BC))) as BCp; match type of BCp with _ - (vsb_ppot ?x - _) <= _ <= _ => pose proof (vsb_ppot_range x) as PPR end; unfold PPOT_CAP in *; keeplia BCp PPR (* [comment removed for export] *) | ] end.
          -- right. split; [keeplia Slo|]. split; [reflexivity|]. split; [apply VOBJT; [exact VSBC| exact U8]|].
             split; [| unhide BUF0; exact BUF0].
             unhide_neqs. intros y [<-|[<-|[]]]; cbn [vb_buf vsb_set_flags]; [split; [exact NESV| exact NEbV] | split; [exact NESw| exact NEbw]].
          -- exact LIVE0.
          -- ufs. eapply (cframe_newV _ _ _ _ _ (vsb_blocks S vv));
               [ eapply (cframe_after _ _ _ _ _ _ (aview A0 m0) (aview A m)); [exact CF| exact MU| intros a Ha NO; OWN a Ha NO |]
               | intros a [_ X]; left; exact X ].
             exact MP.
  Qed.
End S.
