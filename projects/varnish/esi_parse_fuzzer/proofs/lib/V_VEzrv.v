(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Img0 Img0 V_Co10c V_Leaves.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_WSwg5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSle5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSle5 V_ve9hz.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_WSwg5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSle5.V_VS8yn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSle5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_ve9hz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac call_consts_in H ::= unfold CB_FRAME in H.
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
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac mem_side := cbn; first [ (let E := fresh "E" in intros E; discriminate E) | solve [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [ exact I | reflexivity ] ] | solve [ repeat first [ left; reflexivity | right ] ] | tauto ].
Local Ltac mem_hyp Hr := cbn in Hr; first [ solve [ repeat (destruct Hr as [Hr|Hr]; [discriminate Hr|]); first [ discriminate Hr | destruct Hr ] ] | intuition discriminate ].
(* [comment removed for export] *)

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

(* [comment removed for export] *)
Lemma vep_cells_vsb : forall v tag q,
  firstn 2 (vep_cells v tag q) ++ [C8 (Z_to_bv 64 0)] ++ skipn 3 (vep_cells v tag q) = vep_cells (fupd v Fvsb 0) tag q.
Proof. intros. reflexivity. Qed.
Lemma vep_cells_attr_vsb : forall v tag q,
  firstn 36 (vep_cells v tag q) ++ [C8 (Z_to_bv 64 0)] ++ skipn 37 (vep_cells v tag q) = vep_cells (fupd v Fattr_vsb 0) tag q.
Proof. intros. reflexivity. Qed.
Lemma vep_cells_include_src : forall v tag q,
  firstn 45 (vep_cells v tag q) ++ [C8 (Z_to_bv 64 0)] ++ skipn 46 (vep_cells v tag q) = vep_cells (fupd v Finclude_src 0) tag q.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma vep_cells_ext : forall v v' tag q, (forall f, v' f = v f) -> vep_cells v' tag q = vep_cells v tag q.
Proof. intros v v' tag q E. unfold vep_cells. rewrite !E. reflexivity. Qed.

(* [comment removed for export] *)
Ltac unhide_all := repeat match goal with H : kept _ |- _ => unhide H end.
Tactic Notation "keeplia" ne_hyp_list(hs) := clear - hs; unhide_all; lia.

Lemma fupd_cbx0 : forall v f, fupd v Fcb_x (v Fcb_x + 0) f = v f.
Proof. intros v f. unfold fupd. destruct (vf_beq f Fcb_x) eqn:E; [apply vf_beq_eq in E; subst; lia| reflexivity]. Qed.

Lemma sx32_small : forall z, (0 <= z < 2^31)%Z -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. rewrite bv_swrap_small; [reflexivity|].
  unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 `div` 2)%Z with 2147483648%Z. lia.
Qed.

(* [comment removed for export] *)
Local Ltac chunks_hide_except FRAME :=
  lazymatch goal with |- context [MS _ _ _ _ _ ?m _] =>
    lazymatch type of FRAME with rw_cells ?segs _ _ _ =>
      repeat match goal with
      | H : rw_cells segs m _ _ |- _ => first [ constr_eq H FRAME; fail 1 | hide H ]
      | H : ro_cells segs m _ _ |- _ => hide H
      | H : u8arr segs m _ _ |- _ => hide H
      end
    end
  end.
Local Ltac chunks_unhide :=
  lazymatch goal with |- context [MS _ _ _ _ _ ?m _] =>
    repeat match goal with
    | H : kept (rw_cells _ m _ _) |- _ => unhide H
    | H : kept (ro_cells _ m _ _) |- _ => unhide H
    | H : kept (u8arr _ m _ _) |- _ => unhide H
    end
  end.
Local Ltac stub_begin FRAME lo hi :=
  lazymatch goal with |- context [MS _ _ _ _ _ ?m _] =>
    lazymatch type of FRAME with rw_cells ?segs _ _ _ =>
      pose proof (munch_refl [(lo, hi)]%Z m) as MUstub; pose proof (wmono_refl segs m) as WMstub
    end
  end; chunks_hide_except FRAME.
Local Ltac stub_end MUstub WMstub :=
  lazymatch type of MUstub with munch ?W ?ma ?mb =>
    lazymatch type of WMstub with wmono ?segs _ _ =>
      repeat match goal with
      | H : kept (rw_cells segs ma ?B ?cs) |- _ =>
          unhide H; apply (rw_cells_transport segs W ma mb B cs) in H; [| exact MUstub| exact WMstub| cbn [disjoint_from]; simpl_sizes; slia]
      | H : kept (ro_cells segs ma ?B ?cs) |- _ =>
          unhide H; apply (ro_cells_transport segs W ma mb B cs) in H; [| exact MUstub| cbn [disjoint_from]; simpl_sizes; slia]
      | H : kept (u8arr segs ma ?B ?xs) |- _ =>
          unhide H; apply (u8arr_transport segs W ma mb B xs) in H; [| exact MUstub| exact WMstub| cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia]
      end
    end
  end; clear MUstub WMstub.

(* [comment removed for export] *)
Local Ltac plia := zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker.
Local Ltac avoids_false X :=
  lazymatch type of X with
  | _ \/ _ => destruct X as [X|X]; avoids_false X
  | False => destruct X
  | _ => try (lazymatch type of X with (_ <> _) /\ _ => destruct X as [_ X] end);
         first [ match goal with D : _ \/ _ |- _ => solve [ destruct D; plia ] end | plia ]
  end.
(* [comment removed for export] *)
Local Ltac plia2 := first [ plia | zify_prune; Zify.zify; xlia zchecker ].
Local Ltac avoids_solve ::=
  cbn [Cells.cells_size Cells.csize Nat.add length app];
  split; [ lia | intros ? ? X; unfold blk, nowhere in X; cbn beta in X; first [ avoids_false X | plia2 ] ].

Section CF.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.
  (* [comment removed for export] *)
  Lemma cframe_after : forall o o' spx WIN (V N : Z -> Prop) ma mb mc W,
    cframe LayoutP0 o o' spx WIN V N ma mb -> munch W mb mc ->
    (forall a, 0 <= a < 2^64 -> ~ outside W a ->
               (spx - WIN <= a < spx) \/ V a \/ N a \/ (al_errno LayoutP0 <= a < al_errno LayoutP0 + 4)) ->
    mapped mc (spx - WIN) WIN ->
    cframe LayoutP0 o o' spx WIN V N ma mc.
  Proof.
    (intros o o' spx WIN V N ma mb mc W; (first [ intro dR_99; dand3 dR_99 as C1 C2 C3 | intros (C1 & C2 & C3) ]); intros MU IN MAP). split; [|split; [exact MAP| exact C3]].
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
    cframe LayoutP0 o o' spx WIN V N ma mb -> (forall a, N' a -> N a \/ V a) -> cframe LayoutP0 o o' spx WIN V N' ma mb.
  Proof.
    (intros o o' spx WIN V N N' ma mb; (first [ intro dR_100; dand3 dR_100 as C1 C2 C3 | intros (C1 & C2 & C3) ]); intros HN). split; [exact C1|]. split; [exact C2|].
    intros a Ha NW NE X. destruct (HN a X) as [Y|Y]; [exact (C3 a Ha NW NE Y)| right; left; exact Y].
  Qed.
End CF.

Section WB.
Context {Clg : Ceiling}.
  Context {AI : AllocSpec LayoutP0}.
  (* [comment removed for export] *)
  Lemma world_bytes_ge56 : forall H A m VEP v tag q vv va vi wa n N,
    parsed_world H A m VEP v tag q vv va vi wa n N -> 56 <= world_bytes vv va vi.
  Proof.
    intros H A m VEP v tag q vv va vi wa n N PW.
    pose proof PW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VO & _ & _ & VA & VI).
    pose proof (proj1 (proj1 (proj2 VO))) as IV. unfold world_bytes.
    destruct va as [x|]; [destruct VA as (VOa & _); pose proof (proj1 (proj1 (proj2 VOa))) as IVa|];
    (destruct vi as [[y fi]|]; [destruct VI as (VOi & _); pose proof (proj1 (proj1 (proj2 VOi))) as IVi|]); lia.
  Qed.
End WB.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.
  Hypothesis HMC : vep_mark_common_stmt.
  Hypothesis HEC : vep_emit_common_stmt.

  (* [comment removed for export] *)
  Variables (H : henv) (VEP wa n N DATA : Z) (v0 : vep) (tag : list byte) (q : vep_pads) (vv0 : vsb_rec)
            (va : option vsb_rec) (vi : option (vsb_rec * bool)) (lo : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m0 : mem) (md0 : Model) (A0 : AS) (T : TSet).
  Let S := v0 Fvsb.
  Hypothesis PW : parsed_world H A0 m0 VEP v0 tag q vv0 va vi wa n N.
  Hypothesis HG : henv_geom H.
  Hypothesis TP : tp = al_tp LayoutP0.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + VEPFIN_STACK <= bv_unsigned sp.
  Hypothesis SPH : bv_unsigned sp = h_sp H.
  Hypothesis LD0 : a_live A0 DATA = Some N.
  Hypothesis N0 : 0 < N.
  Hypothesis DRANGE : DATA <= v0 Fver_p <= DATA + N.
  Hypothesis NEDV : DATA <> VEP.
  Hypothesis NEDS : DATA <> v0 Fvsb.
  Hypothesis NPB : ~ parse_blocks v0 vv0 va vi DATA.
  (* [comment removed for export] *)
  Hypothesis LBUD : a_livebytes A0 + FIN_LIVE N <= LIVE_MAX.
  Hypothesis NBUD : a_nlive A0 + 1 <= NLIVE_MAX.
  Hypothesis K :
    forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model)
           (v' : vep) (vr : vsb_rec),
      ainv A' m' md' -> mem_inv rsegs m' -> md_frame md0 md' ->
      stk rsegs m' lo (bv_unsigned sp) -> henv_ok LayoutP0 VI0 H m' -> img_ok0 m' ->
      vep_obj LayoutP0 A' m' VEP v' tag q -> ws1_obj LayoutP0 H A' m' wa VEP ->
      (r = 0 \/ (r <> 0 /\ r = v0 Fvsb /\ vsb_obj LayoutP0 A' m' r vr true /\ vsb_apart r vr [VEP; wa] /\
                 (parse_blocks v0 vv0 va vi (vb_buf vr) \/ a_live A0 (vb_buf vr) = None))) ->
      (forall p k, a_live A0 p = Some k -> p <> v0 Fvsb -> ~ parse_blocks v0 vv0 va vi p -> a_live A' p = Some k) ->
      a_livebytes A' = a_livebytes A0 - world_bytes vv0 va vi + (if Z.eqb r 0 then 0 else 40 + vb_size vr) ->
      a_nlive A' = a_nlive A0 - world_nlive va vi - (if Z.eqb r 0 then 2 else 0) ->
      cframe LayoutP0 (owned A0) (owned A') (bv_unsigned sp) VEPFIN_STACK (finish_changed H VEP v0 vv0 va vi)
             (fun a => r <> 0 /\ vsb_blocks r vr a) m0 m' ->
      realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T.

  (* [comment removed for export] *)
  Definition jst (A : AS) (m : mem) (md : Model) (v : vep) (vv : vsb_rec) (fin : bool) (lenb : Z) : Prop :=
       ainv A m md /\ mem_inv rsegs m /\ md_frame md0 md
    /\ stk rsegs m lo (bv_unsigned sp - 32)
    /\ (exists junk, rw_cells rsegs m (bv_unsigned sp - 32) [CB 8 junk; C8 s1; C8 s0; C8 ra])
    /\ henv_ok LayoutP0 VI0 H m /\ img_ok0 m
    /\ vep_obj LayoutP0 A m VEP v tag q /\ vep_base H VEP v
    /\ v Fvsb = S /\ v Finclude_src = 0 /\ v Fattr_vsb = 0
    /\ v Fstate = v0 Fstate /\ v Fesi_found = v0 Fesi_found /\ bool01 (v Flast_mark) /\ v Fver_p = v0 Fver_p
    /\ 0 <= v Fcb_x < NMAX
    /\ vsb_obj LayoutP0 A m S vv fin /\ vb_size vv <= vb_len vv + 4096 /\ 0 <= vb_len vv <= lenb
    /\ vb_buf vv <> VEP /\ vb_buf vv <> wa
    /\ ws1_obj LayoutP0 H A m wa VEP
    /\ a_live A DATA = Some N
    /\ (forall p k, a_live A0 p = Some k -> p <> S -> ~ parse_blocks v0 vv0 va vi p -> a_live A p = Some k)
    /\ (parse_blocks v0 vv0 va vi (vb_buf vv) \/ a_live A0 (vb_buf vv) = None)
    (* [comment removed for export] *)
    /\ (a_livebytes A = a_livebytes A0 - world_bytes vv0 va vi + 40 + vb_size vv /\ a_nlive A + world_nlive va vi = a_nlive A0)
    /\ cframe LayoutP0 (owned A0) (owned A) (bv_unsigned sp) VEPFIN_STACK (finish_changed H VEP v0 vv0 va vi)
              (vsb_blocks S vv) m0 m.

  (* [comment removed for export] *)
  Local Definition WBGE : 56 <= world_bytes vv0 va vi := world_bytes_ge56 _ _ _ _ _ _ _ _ _ _ _ _ _ PW.

  (* [comment removed for export] *)
  Local Ltac prelims :=
    pose proof (as_layout_order (L:=LayoutP0)) as LAY; cbn [al_image_lo al_rw_lo al_image_hi LayoutP0] in LAY;
    pose proof alloc_ceiling_val as ACV;
    pose proof HG as (G16 & GCE & GHI); unfold HFRAME in GHI;
    assert (ES : S = v0 Fvsb) by reflexivity; assert (E30 : ERRNO0 = 0x420b4) by reflexivity.
  (* [comment removed for export] *)
  Local Ltac OWN a Ha NO :=
    cbn [outside] in NO; change (al_errno LayoutP0) with 0x420b4; unfold vsb_blocks; cbn [vb_buf vb_size vsb_set_flags];
    lazymatch goal with |- _ \/ finish_changed _ ?VEPx _ _ _ _ a \/ (blk ?Sx 40 a \/ blk ?bx ?szx a) \/ _ =>
      let C := fresh "CASES" in
      assert (C : (bv_unsigned sp - 8512 <= a < bv_unsigned sp) \/ (VEPx <= a < VEPx + 312) \/ (Sx <= a < Sx + 40) \/
                  (bx <= a < bx + szx) \/ (0x420b4 <= a < 0x420b4 + 4) \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
        by (clear - Ha NO; unfold ERRNO0 in *; lia);
      clear NO;
      destruct C as [X|[X|[X|[X|[X|X]]]]];
      [ left; exact X
      | right; left; unfold finish_changed; left; unfold blk; split; [| exact X];
        match goal with L : 4096 <= VEPx |- _ => clear - L; lia end
      | right; left; unfold finish_changed; right; left; unfold vsb_blocks; left; unfold blk;
        match goal with E : Sx = _ |- _ => rewrite <- E end; split; [| exact X];
        match goal with L : 4096 <= Sx |- _ => clear - L; lia end
      | right; right; left; right; unfold blk; split; [| exact X];
        match goal with L : 0 < bx |- _ => clear - L; lia end
      | right; right; right; exact X
      | right; left; unfold finish_changed; right; right; right; right; exact X ]
    end.
  Local Ltac ufs := unfold VEPFIN_STACK, MARK_STACK, EMITC_STACK, EMITLEN_STACK, REALLOC_STACK, DESTROY_STACK, FREE_STACK, CB_FRAME in *.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="K NBUD LBUD NEDS NEDV SPH LO CEIL SP16 TP HG PW n"] Lemma T6 : forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) A m md v vr lenb,
    jst A m md v vr true lenb ->
    realizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 (Z_to_bv 64 VEP) (Z_to_bv 64 (VEP + 8))
                                    a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               bvmap_empty (Z_to_bv 64 0x1bf3c) (Z_to_bv 32 0) None m (seg_rom rsegs)) md) T.
  Proof.
    intros until lenb. intros J. prelims.
    (first [ dand28 J as AINV MI MDF ST [junk FR] HENV IMG VEPO VB EVSB EIS EAV EST EEF BLM EVP CBX VOBJ _ _ NEbV NEbw WS1 LD LIVE0 BUF0 BUDJ CF | destruct J as (AINV & MI & MDF & ST & [junk FR] & HENV & IMG & VEPO & VB & EVSB & EIS & EAV & EST & EEF & BLM & EVP & CBX
                   & VOBJ & _ & _ & NEbV & NEbw & WS1 & LD & LIVE0 & BUF0 & BUDJ & CF) ]).
    ufs.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH].
    destruct HENV as [GLOB HOBJ].
    assert (Ebss : h_bss H = 0x41830) by (destruct GLOB as [E _]; rewrite E; reflexivity).
    pose proof PW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & APART0 & _).
    destruct (APART0 VEP ltac:(left; reflexivity)) as [NESV _]. destruct (APART0 wa ltac:(right; left; reflexivity)) as [NESw _].
    (* [comment removed for export] *)
    (first [ pose proof (VEPO) as dR_2; dand4 dR_2 as VLV VEPC TAG8 PADS | pose proof VEPO as (VLV & VEPC & TAG8 & PADS) ]). cbn [al_segs LayoutP0] in VEPC.
    (first [ pose proof (PADS) as dR_3; dand7 dR_3 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]).
    unfold vep_cells in VEPC. rewrite EVSB in VEPC.
    (first [ pose proof ((rw_cells_split3 rsegs m VEP _ 2 (C8 (Z_to_bv 64 S)) VEPC eq_refl)) as dR_4; dand3 dR_4 as VA VM VBk | pose proof (rw_cells_split3 rsegs m VEP _ 2 (C8 (Z_to_bv 64 S)) VEPC eq_refl) as (VA & VM & VBk) ]). clear VEPC.
    cbn [firstn skipn cells_size csize Nat.add length] in VA, VM, VBk.
    change (Z.of_nat 8) with 8 in VM. change (Z.of_nat 8) with 8 in VBk. replace (VEP + 8 + 8) with (VEP + 16) in VBk by lia.
    (first [ pose proof ((as_live_ok A m md VEP _ AINV VLV)) as dR_5; dand7 dR_5 as _ VEP16 VEPlo VEPhi VEPimg VEPmap VEPown | pose proof (as_live_ok A m md VEP _ AINV VLV) as (_ & VEP16 & VEPlo & VEPhi & VEPimg & VEPmap & VEPown) ]).
    assert (VEPbss : VEP + 312 <= 0x10000 \/ 0x63000 <= VEP) by (unfold in_image in VEPimg; cbn [al_image_lo al_image_hi LayoutP0] in VEPimg; keeplia VEPimg).
    clear VEPimg VEPown.
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md S vr true AINV VOBJ)) as dR_6; dand11 dR_6 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LayoutP0 A m md S vr true AINV VOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    unfold off_image in Simg, Bimg. cbn [al_image_lo al_image_hi LayoutP0] in Simg, Bimg.
    (first [ pose proof (VOBJ) as dR_7; dand6 dR_7 as _ _ LS LB NESb _ | pose proof VOBJ as (_ & _ & LS & LB & NESb & _) ]).
    pose proof (as_live_disjoint A m md S 40 VEP 312 AINV LS VLV NESV) as DJS.
    pose proof (as_live_disjoint A m md (vb_buf vr) (vb_size vr) VEP 312 AINV LB VLV NEbV) as DJB.
    pose proof WS1 as WS1x. (first [ dex2 WS1x as id pad; dand7 WS1x as IDOK PADL _ _ LWA _ _ | dand9 WS1x as id pad IDOK PADL _ _ LWA _ _ | destruct WS1x as (id & pad & IDOK & PADL & _ & _ & LWA & _ & _) ]).
    assert (NEwS : wa <> S) by (intros X; apply NESw; symmetry; exact X).
    assert (NEwB : wa <> vb_buf vr) by (intros X; apply NEbw; symmetry; exact X).
    (first [ pose proof ((as_live_ok A m md wa _ AINV LWA)) as dR_9; dand7 dR_9 as _ _ WAlo WAhi _ _ _ | pose proof (as_live_ok A m md wa _ AINV LWA) as (_ & _ & WAlo & WAhi & _ & _ & _) ]).
    pose proof (as_live_disjoint A m md S 40 wa 40 AINV LS LWA (not_eq_sym NEwS)) as DJ1.
    pose proof (as_live_disjoint A m md (vb_buf vr) (vb_size vr) wa 40 AINV LB LWA (not_eq_sym NEwB)) as DJ2.
    pose proof (as_live_disjoint A m md wa 40 VEP 312 AINV LWA VLV ltac:(intros X; rewrite X in LWA; rewrite VLV in LWA; discriminate LWA)) as DJ3.
    (* [comment removed for export] *)
    hide DSB. hide Simg. hide Bimg. hide VEPbss. hide DJ1. hide DJ2. hide DJ3. hide DJS. hide DJB. hide BUF0. hide LAY.
    hide_neqs.
    apply rz_go; [exact MDH | exact MDL |].
    (* [comment removed for export] *)
    zstep. zstep.
    apply rz_stop.
    pose proof (crange_block (L:=LayoutP0) A m md VEP 312 VEP 8 AINV VLV ltac:(lia) ltac:(lia) ltac:(lia)) as CRA.
    pose proof (crange_block (L:=LayoutP0) A m md VEP 312 (VEP + 16) 296 AINV VLV ltac:(lia) ltac:(lia) ltac:(lia)) as CRB.
    pose_cranges LayoutP0 A m AINV.
    unhide NESV. unhide NEbV. unhide NEwS. unhide NEwB.
    eapply (VSB_destroy_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m md A (VEP + 8) S vr true lo);
      [ exact AINV | exact MI | reflexivity | exact VM
      | right; exists VEP, 312; split; [exact VLV|]; split; [cbn; intros [X|[X|X]]; [exact (NESV X)| exact (NEbV X)| exact X] | lia]
      | exact VOBJ | exact TP
      | rewrite unsigned_lit by lia; replace (bv_unsigned sp - 32) with (bv_unsigned sp + -32) by lia; apply align16_add; [exact SP16|reflexivity]
      | rewrite unsigned_lit by lia; reflexivity
      | rewrite unsigned_lit by lia; exact ST | exact CEIL
      | rewrite unsigned_lit by lia; ufs; keeplia LO
      | rewrite unsigned_lit by lia; keeplia GHI SPH | ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 m1 md1 AINV1 MI1 MDF1 ST1 PSC DEADS DEADB LIVEq LBd NLd FRK.
    pose proof (as_lazy_nil A1 m1 md1 AINV1) as [MDL1 MDH1].
    rewrite unsigned_lit in ST1, FRK by lia. ufs.
    (* [comment removed for export] *)
    assert (LVEP1 : a_live A1 VEP = Some 312) by (rewrite (LIVEq VEP (not_eq_sym NESV) (not_eq_sym NEbV)); exact VLV).
    assert (LWA1 : a_live A1 wa = Some 40) by (rewrite (LIVEq wa NEwS NEwB); exact LWA).
    assert (HOBJ1 : hobj_ok LayoutP0 VI0 H m1).
    { eapply (hobj_ok_ccall LayoutP0 VI0 H A A1 m md m1); [exact AINV| exact FRK| exact HG| exact HOBJ| lia|].
      intros a Ha X. unfold h_vc, h_wrk, h_req, h_resp, h_hd, blk in *. keeplia Ha X Shi Bhi VEPhi GCE SPH ACV. }
    assert (GLOB1 : glob_ok LayoutP0 VI0 H m1).
    { eapply (glob_ok_ccall LayoutP0 VI0 H A A1 m md m1); [exact AINV| exact FRK| exact HG| exact GLOB| keeplia SPH| keeplia SPH GCE ACV
        | rewrite Ebss; cbn; keeplia ACV| rewrite Ebss; cbn; keeplia ACV
        | intros i Hi; rewrite Ebss; cbn; unfold p0_static; keeplia Hi
        | rewrite Ebss; cbn; change (al_errno LayoutP0) with 0x420b4; keeplia ACV
        | intros a Ha X; rewrite Ebss in Ha; unfold h_cp, h_vsc, blk in *; keeplia Ha X Shi Bhi VEPhi GCE SPH ACV Simg Bimg VEPbss]. }
    assert (IMG1 : img_ok0 m1).
    { eapply (img_ok0_ccall A A1 m md m1); [exact AINV| exact FRK| unfold IMG0_HI; keeplia GCE SPH ACV| | exact IMG].
      intros a Ha X. unfold IMG0_LO, IMG0_HI, blk in *. keeplia Ha X Simg Bimg VEPbss. }
    assert (WS1_1 : ws1_obj LayoutP0 H A1 m1 wa VEP).
    { eapply (ws1_obj_ccall LayoutP0 H A A1 m md m1); [exact AINV| exact FRK| exact HG| exact WS1| keeplia SPH| keeplia SPH GCE ACV| exact LWA1| exact LVEP1|].
      intros a Ha X. unfold h_ws, h_wsbuf, blk in *. keeplia Ha X Shi Bhi VEPhi GCE SPH ACV DJ1 DJ2 DJ3. }
    clear HOBJ GLOB IMG WS1 ST.
    hide_neqs. unhide DJS. unhide DJB. try clear VM. acall_xfer FRK. hide DJS. hide DJB. unhide_neqs. clear CRA CRB.
    (* [comment removed for export] *)
    assert (VEPC1 : rw_cells rsegs m1 VEP (vep_cells (fupd v Fvsb 0) tag q)).
    { rewrite <- vep_cells_vsb. unfold vep_cells. rewrite ?EVSB. cbn [firstn skipn].
      lazymatch type of VA with rw_cells _ _ _ ?pre => apply (rw_cells_join3 rsegs m1 VEP pre); [exact VA| exact PSC|] end.
      eapply rwc_eq; [exact VBk| cbn [cells_size csize Nat.add length]; change (Z.of_nat 8) with 8; lia]. }
    clear VA VBk PSC.
    rz_resume MDH1 MDL1.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    try replace (bv_unsigned sp - 32 + 32) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    release_frame FR ST1 (bv_unsigned sp).
    zstep. cps_done.
    eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 A1 m1 md1 (fupd v Fvsb 0) vr);
      [ exact AINV1 | exact MI1 | eapply md_frame_trans; [exact MDF| exact MDF1] | exact ST1
      | split; [exact GLOB1| exact HOBJ1] | exact IMG1
      | split; [exact LVEP1|]; split; [cbn [al_segs LayoutP0]; exact VEPC1| split; [exact TAG8| exact PADS]]
      | exact WS1_1 | left; reflexivity |
      | rewrite LBd; change (0 =? 0) with true; cbv iota; keeplia BUDJ
      | rewrite NLd; change (0 =? 0) with true; cbv iota; keeplia BUDJ
      | ].
    - unhide BUF0. intros p k L0 NS NP. rewrite (LIVEq p NS).
      + apply (LIVE0 p k L0 NS NP).
      + intros ->. destruct BUF0 as [E|E]; [exact (NP E)| rewrite E in L0; discriminate L0].
    - assert (CF2 : cframe LayoutP0 (owned A) (owned A1) (bv_unsigned sp) 8512
                      (fun a => blk S 40 a \/ blk (vb_buf vr) (vb_size vr) a \/ VEP + 8 <= a < VEP + 8 + 8) nowhere m m1).
      { eapply (cframe_extend LayoutP0 _ _ _ _ _ _ _ _ _ _ m m m1 m1 [] []);
          [ apply munch_refl | intros a _ X; exfalso; apply X; exact I | exact FRK
          | keeplia ACV | keeplia ACV
          | intros a X; exact X | intros a X; destruct X | apply munch_refl | intros a _ X; exfalso; apply X; exact I
          | eapply (stk_mapped (L:=LayoutP0)); [exact ST1 | exact CEIL | keeplia LO | keeplia LO] ]. }
      eapply (cframe_seq LayoutP0 _ _ _ _ _ _ _ _ _ _ _ _ _ m0 m m1 CF CF2); [keeplia ACV | keeplia ACV
        | eapply (stk_mapped (L:=LayoutP0)); [exact ST1 | exact CEIL | keeplia LO | keeplia LO]
        | intros a X; exact X
        | intros a [X|[X|X]]; [left; left; exact X| left; right; exact X| right; left; unfold blk; keeplia X VEPlo]
        | intros a [X _]; exfalso; apply X; reflexivity ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="K NBUD LBUD NEDS NEDV SPH LO CEIL SP16 TP HG PW n"] Lemma T5 : forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) A m md v vv lenb,
    jst A m md v vv false lenb ->
    realizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 (Z_to_bv 64 VEP) s1
                                    a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               bvmap_empty (Z_to_bv 64 0x1bef8) (Z_to_bv 32 0) None m (seg_rom rsegs)) md) T.
  Proof.
    intros until lenb. intros J. prelims.
    (first [ dand28 J as AINV MI MDF ST [junk FR] HENV IMG VEPO VB EVSB EIS EAV EST EEF BLM EVP CBX VOBJ SZB LENB NEbV NEbw WS1 LD LIVE0 BUF0 BUDJ CF | destruct J as (AINV & MI & MDF & ST & [junk FR] & HENV & IMG & VEPO & VB & EVSB & EIS & EAV & EST & EEF & BLM & EVP & CBX
                   & VOBJ & SZB & LENB & NEbV & NEbw & WS1 & LD & LIVE0 & BUF0 & BUDJ & CF) ]).
    ufs. unfold NMAX in CBX.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH].
    destruct HENV as [GLOB HOBJ].
    assert (Ebss : h_bss H = 0x41830) by (destruct GLOB as [E _]; rewrite E; reflexivity).
    assert (Evc : h_vc H = h_sp H + 1304) by reflexivity.
    assert (Ewrk : h_wrk H = h_sp H + 1120) by reflexivity.
    assert (Evsc : h_vsc H = h_sp H + 2240) by reflexivity.
    assert (Ecp : h_cp H = h_sp H + 1488) by reflexivity.
    assert (Ews : h_ws H = h_sp H + 1080) by reflexivity.
    assert (Ewb : h_wsbuf H = h_sp H + 16) by reflexivity.
    assert (Ehd : h_hd H = h_sp H + 1040) by reflexivity.
    assert (Ereq : h_req H = h_sp H + 1432) by reflexivity.
    assert (Eresp : h_resp H = h_sp H + 1376) by reflexivity.
    pose proof PW as (_ & _ & _ & _ & BEF0 & _ & _ & _ & _ & _ & _ & APART0 & _).
    destruct (APART0 VEP ltac:(left; reflexivity)) as [NESV _]. destruct (APART0 wa ltac:(right; left; reflexivity)) as [NESw _].
    (* [comment removed for export] *)
    (first [ pose proof (VEPO) as dR_11; dand4 dR_11 as VLV VEPC TAG8 PADS | pose proof VEPO as (VLV & VEPC & TAG8 & PADS) ]). cbn [al_segs LayoutP0] in VEPC.
    (first [ pose proof ((as_live_ok A m md VEP _ AINV VLV)) as dR_12; dand7 dR_12 as _ VEP16 VEPlo VEPhi VEPimg VEPmap VEPown | pose proof (as_live_ok A m md VEP _ AINV VLV) as (_ & VEP16 & VEPlo & VEPhi & VEPimg & VEPmap & VEPown) ]).
    assert (VEPbss : VEP + 312 <= 0x10000 \/ 0x63000 <= VEP) by (unfold in_image in VEPimg; cbn [al_image_lo al_image_hi LayoutP0] in VEPimg; keeplia VEPimg).
    clear VEPimg VEPown.
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md S vv false AINV VOBJ)) as dR_13; dand11 dR_13 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LayoutP0 A m md S vv false AINV VOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    pose proof Simg as Simg'. pose proof Bimg as Bimg'. unfold off_image in Simg', Bimg'. cbn [al_image_lo al_image_hi LayoutP0] in Simg', Bimg'.
    pose proof VOBJ as VOBJx. vsb_open VOBJx. (first [ dex1 VBUF as bs; dand3 VBUF as U8 LBS _ | dand4 VBUF as bs U8 LBS _ | destruct VBUF as (bs & U8 & LBS & _) ]). cbn [al_segs LayoutP0] in U8.
    pose proof VINV as VINVx. (first [ dand9 VINVx as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm Vsm | destruct VINVx as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm & Vsm) ]).
    pose proof (as_live_disjoint A m md S 40 VEP 312 AINV VLS VLV NESV) as DJS.
    pose proof (as_live_disjoint A m md (vb_buf vv) (vb_size vv) VEP 312 AINV VLB VLV NEbV) as DJB.
    pose proof WS1 as WS1x. (first [ dex2 WS1x as id pad; dand7 WS1x as IDOK PADL _ _ LWA _ _ | dand9 WS1x as id pad IDOK PADL _ _ LWA _ _ | destruct WS1x as (id & pad & IDOK & PADL & _ & _ & LWA & _ & _) ]).
    assert (NEwS : wa <> S) by (intros X; apply NESw; symmetry; exact X).
    assert (NEwB : wa <> vb_buf vv) by (intros X; apply NEbw; symmetry; exact X).
    (first [ pose proof ((as_live_ok A m md wa _ AINV LWA)) as dR_17; dand7 dR_17 as _ _ WAlo WAhi WAimg _ _ | pose proof (as_live_ok A m md wa _ AINV LWA) as (_ & _ & WAlo & WAhi & WAimg & _ & _) ]).
    assert (WAbss : wa + 40 <= 0x10000 \/ 0x63000 <= wa) by (unfold in_image in WAimg; cbn [al_image_lo al_image_hi LayoutP0] in WAimg; keeplia WAimg).
    clear WAimg.
    pose proof (as_live_disjoint A m md S 40 wa 40 AINV VLS LWA (not_eq_sym NEwS)) as DJ1.
    pose proof (as_live_disjoint A m md (vb_buf vv) (vb_size vv) wa 40 AINV VLB LWA (not_eq_sym NEwB)) as DJ2.
    pose proof (as_live_disjoint A m md wa 40 VEP 312 AINV LWA VLV ltac:(intros X; rewrite X in LWA; rewrite VLV in LWA; discriminate LWA)) as DJ3.
    (* [comment removed for export] *)
    (first [ pose proof (HOBJ) as dR_18; dand3 dR_18 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]). (first [ dex2 VC as vcpad vcrest; dand3 VC as LVP LVR VC | dand5 VC as vcpad vcrest LVP LVR VC | destruct VC as (vcpad & vcrest & LVP & LVR & VC) ]). (first [ dex2 WK as wkpad wkrest; dand3 WK as LWP LWR WK | dand5 WK as wkpad wkrest LWP LWR WK | destruct WK as (wkpad & wkrest & LWP & LWR & WK) ]).
    cbn [al_segs LayoutP0] in VC, WK. unfold vc_cells in VC. unfold wrk_cells in WK.
    (first [ pose proof (GLOB) as dR_21; dand4 dR_21 as _ BSS CP [cnt CNT] | pose proof GLOB as (_ & BSS & CP & [cnt CNT]) ]). rewrite Ebss in BSS. cbn [al_segs LayoutP0] in BSS, CP, CNT.
    pose proof IMG as IMGx. (first [ dand4 IMGx as _ _ GVSC _ | destruct IMGx as (_ & _ & GVSC & _) ]). unfold GOT_vsc in GVSC.
    (* [comment removed for export] *)
    (first [ pose proof (VB) as dR_23; dand5 dR_23 as EVC EVCB EVCBP EVDZ EVURL | pose proof VB as (EVC & EVCB & EVCBP & EVDZ & EVURL) ]).
    unfold vep_cells in VEPC. rewrite EVSB, EVC, EVCB, EVCBP in VEPC. cbn [vi_cb VI0] in VEPC.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 8512, bv_unsigned sp); (VEP, VEP + 312); (S, S + 40); (vb_buf vv, vb_buf vv + vb_size vv); (ERRNO0, ERRNO0 + 4); (h_vsc H + 1304, h_vsc H + 1320)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (CFP : client_fp LayoutP0 A [(bv_unsigned sp - 8512, bv_unsigned sp); (VEP, VEP + 312); (S, S + 40); (vb_buf vv, vb_buf vv + vb_size vv); (ERRNO0, ERRNO0 + 4); (h_vsc H + 1304, h_vsc H + 1320)]).
    { cbn. split; [left; keeplia GCE SPH ACV LO GHI|]. split; [right; left; exists VEP, 312; split; [exact VLV|lia]|].
      split; [right; left; exists S, 40; split; [exact VLS|lia]|].
      split; [right; left; exists (vb_buf vv), (vb_size vv); split; [exact VLB|lia]|].
      split; [right; right; left; rewrite ERRNO0_eq; split; reflexivity|].
      split; [left; keeplia GCE SPH ACV Evsc GHI| exact I]. }
    (* [comment removed for export] *)
    hide DSB. hide Simg. hide Bimg. hide Simg'. hide Bimg'. hide VEPbss. hide DJ1. hide DJ2. hide DJ3. hide DJS. hide DJB.
    hide BUF0. hide LAY. hide WAbss. hide Verr. hide_neqs.
    (* [comment removed for export] *)
    assert (VINV' : vsb_inv (vsb_set_flags vv VSB_FLAGS_FIN) true).
    { clear - VINV. unfold vsb_inv in *. cbn [vb_size vb_len vb_error vb_indent vb_flags vb_buf vsb_set_flags] in *.
      unfold VSB_FLAGS_FIN, VSB_FLAGS_LIVE in *. lia. }
    assert (VOBJT : forall mx, rw_cells rsegs mx S (vsb_cells (vsb_set_flags vv VSB_FLAGS_FIN)) ->
                    u8arr rsegs mx (vb_buf vv) (upd bs (Z.to_nat (vb_len vv)) (Z_to_bv 8 0)) ->
                    vsb_obj LayoutP0 A mx S (vsb_set_flags vv VSB_FLAGS_FIN) true).
    { intros mx C U. split; [exact C|]. split; [exact VINV'|]. split; [exact VLS|]. split; [exact VLB|]. split; [unhide VNE; exact VNE|].
      exists (upd bs (Z.to_nat (vb_len vv)) (Z_to_bv 8 0)). split; [exact U|]. split; [rewrite upd_length; exact LBS|].
      intros _. cbn [vb_len vsb_set_flags]. apply nth_error_upd_same. keeplia LBS Vlen. }
    assert (JT : forall mx, mem_inv rsegs mx -> munch [(bv_unsigned sp - 8512, bv_unsigned sp); (VEP, VEP + 312); (S, S + 40); (vb_buf vv, vb_buf vv + vb_size vv); (ERRNO0, ERRNO0 + 4); (h_vsc H + 1304, h_vsc H + 1320)] m mx -> wmono rsegs m mx ->
              stk rsegs mx lo (bv_unsigned sp - 32) ->
              rw_cells rsegs mx (bv_unsigned sp - 32) [CB 8 junk; C8 s1; C8 s0; C8 ra] ->
              rw_cells rsegs mx VEP (vep_cells v tag q) ->
              rw_cells rsegs mx S (vsb_cells (vsb_set_flags vv VSB_FLAGS_FIN)) ->
              u8arr rsegs mx (vb_buf vv) (upd bs (Z.to_nat (vb_len vv)) (Z_to_bv 8 0)) ->
              glob_ok LayoutP0 VI0 H mx ->
              jst A mx md v (vsb_set_flags vv VSB_FLAGS_FIN) true lenb).
    { intros mx MIx MUx WMx STx FRx VEPCx Cx Ux GLx.
      assert (AINVx : ainv A mx md) by (eapply (ainv_munch LayoutP0 A m mx md); [exact AINV| exact MUx| exact WMx| exact CFP]).
      split; [exact AINVx|]. split; [exact MIx|]. split; [exact MDF|]. split; [exact STx|]. split; [exists junk; exact FRx|].
      split. { split; [exact GLx|]. eapply (hobj_ok_munch LayoutP0); [exact HOBJ| exact MUx| exact WMx|].
               intros a Ha. unfold h_vc, h_wrk, h_req, h_resp, h_hd in Ha. cbn [outside]. keeplia Ha VEPhi Shi Bhi GCE SPH ACV E30 Evsc. }
      split. { eapply (img_ok0_munch _ m); [exact MUx| | exact IMG]. intros a Ha. unfold IMG0_LO, IMG0_HI in Ha. cbn [outside].
               keeplia Ha VEPbss Simg' Bimg' GCE SPH ACV E30 Evsc. }
      split. { split; [exact VLV|]. split; [cbn [al_segs LayoutP0]; exact VEPCx|]. split; [exact TAG8| exact PADS]. }
      split; [exact VB|]. split; [exact EVSB|]. split; [exact EIS|]. split; [exact EAV|]. split; [exact EST|]. split; [exact EEF|].
      split; [exact BLM|]. split; [exact EVP|]. split; [unfold NMAX; exact CBX|].
      split; [exact (VOBJT mx Cx Ux)|]. split; [exact SZB|]. split; [exact LENB|]. split; [unhide NEbV; exact NEbV|]. split; [unhide NEbw; exact NEbw|].
      split. { eapply (ws1_obj_munch LayoutP0); [exact WS1| exact MUx| exact WMx|]. intros a Ha. unfold h_ws, h_wsbuf in Ha. cbn [outside].
               keeplia Ha VEPhi Shi Bhi GCE SPH ACV E30 Evsc DJ1 DJ2 DJ3 WAbss WAhi. }
      split; [exact LD|]. split; [exact LIVE0|]. split; [unhide BUF0; exact BUF0|].
      split; [cbn [vb_size vsb_set_flags]; exact BUDJ|].
      unfold VEPFIN_STACK, MARK_STACK, EMITC_STACK, EMITLEN_STACK, REALLOC_STACK.
      eapply (cframe_after _ _ _ _ _ _ m0 m mx); [exact CF| exact MUx| intros a Ha NO; OWN a Ha NO |].
      eapply (window_mapped LayoutP0 _ lo); [exact STx | exact FRx | cbn; lia | exact CEIL | keeplia LO | keeplia LO]. }
    apply rz_go; [exact MDH | exact MDL |].
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    assert (VEPCc : rw_cells rsegs m VEP (vep_cells v tag q)) by ((first [ pose proof (VEPO) as dR_24; dand3 dR_24 as _ X _ | pose proof VEPO as (_ & X & _) ]); cbn [al_segs LayoutP0] in X; exact X).
    clear VEPC.
    unhide VEPbss. unhide DJS. unhide DJB.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_VEPCc); call_fr (vep_default_cb_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                bvmap_empty (Z_to_bv 32 0) m (h_vc H) VEP v tag q 0 vcpad (h_resp H) (h_wrk H) vcrest lo) by (idtac;
      lazymatch goal with
      | |- mem_inv _ _ => assumption
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
      | |- rw_cells _ _ _ (vc_cells _ _ _ _) => unfold vc_cells; exact VC
      | |- rw_cells _ _ _ (vep_cells _ _ _) => exact VEPCc
      | |- @eq word _ _ => first [reflexivity | rewrite EVC; reflexivity | rewrite EVCBP; reflexivity]
      | |- @eq nat _ _ => assumption
      | |- vep_pads_wf _ => assumption
      | |- _ => rewrite ?unsigned_lit by lia; unfold CB_FRAME; keeplia CBX VEPhi GCE SPH ACV LO Evc CEIL
      end).
    hide VEPbss. hide DJS. hide DJB.
    match goal with X : rw_cells rsegs _ VEP (vep_cells _ _ _) |- _ => rename X into VEPC1 end.
    try clear ST. match goal with X : stk rsegs _ lo _ |- _ => rename X into ST end.
    rewrite (vep_cells_ext v (fupd v Fcb_x (v Fcb_x + 0)) tag q (fupd_cbx0 v)) in VEPC1.
    pose proof VEPC1 as VEPC. clear VEPC1. unfold vep_cells in VEPC. rewrite EVSB, EVC, EVCB, EVCBP in VEPC. cbn [vi_cb VI0] in VEPC.
    (* [comment removed for export] *)
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => destruct (rw_errno_any mx) as [e0 ERR];
      (* [comment removed for export] *)
      pose proof (munch_refl [(bv_unsigned sp - 32 - 48, bv_unsigned sp - 32); (S, S + 40); (vb_buf vv, vb_buf vv + vb_size vv); (ERRNO0, ERRNO0 + 4)]%Z mx) as MUf;
      pose proof (wmono_refl rsegs mx) as WMf end.
    hide FR. hide VC. hide WK. hide CP. hide CNT. hide BSS. hide GVSC. hide VEPC.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_ERR); call_lit (VSB_finish_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                bvmap_empty (Z_to_bv 32 0) _ S vv bs e0 lo) by (idtac;
      lazymatch goal with
      | |- mem_inv _ _ => assumption
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
      | |- rw_cells _ _ _ (vsb_cells _) => exact VSBC
      | |- rw_cells _ _ _ [C4 _] => exact ERR
      | |- u8arr _ _ _ _ => exact U8
      | |- vsb_inv _ _ => exact VINV
      | |- off_image _ _ _ => assumption
      | |- @eq word _ _ => first [reflexivity | exact TP]
      | |- _ \/ _ => unhide DSB; exact DSB
      | |- Z.of_nat _ = _ => exact LBS
      | |- _ => rewrite ?unsigned_lit by lia; keeplia Slo Shi Bhi GCE SPH ACV LO GHI CEIL
      end).
    unhide FR. unhide VC. unhide WK. unhide CP. unhide CNT. unhide BSS. unhide GVSC. unhide VEPC. unfold ERRNO0 in MUf.
    eapply rw_cells_transport in BSS; [| exact MUf| exact WMf| cbn [disjoint_from cells_size csize Nat.add length]; keeplia Slo Shi Bhi GCE SPH ACV LO GHI CEIL Simg' Bimg'].
    eapply ro_cells_transport in GVSC; [| exact MUf| cbn [disjoint_from cells_size csize Nat.add length]; keeplia Slo Shi Bhi GCE SPH ACV LO GHI CEIL Simg' Bimg'].
    eapply rw_cells_transport in VEPC; [| exact MUf| exact WMf| cbn [disjoint_from cells_size csize Nat.add length]; keeplia Slo Shi Bhi GCE SPH ACV LO GHI CEIL VEPhi DJS DJB VEPbss].
    eapply rw_cells_transport in FR; [| exact MUf| exact WMf| cbn [disjoint_from cells_size csize Nat.add length]; keeplia Slo Shi Bhi GCE SPH ACV LO GHI CEIL].
    eapply rw_cells_transport in VC; [| exact MUf| exact WMf| cbn [disjoint_from cells_size csize Nat.add length]; keeplia Slo Shi Bhi GCE SPH ACV LO GHI CEIL Evc].
    eapply rw_cells_transport in WK; [| exact MUf| exact WMf| cbn [disjoint_from cells_size csize Nat.add length]; keeplia Slo Shi Bhi GCE SPH ACV LO GHI CEIL Ewrk].
    eapply rw_cells_transport in CP; [| exact MUf| exact WMf| cbn [disjoint_from cells_size csize Nat.add length]; keeplia Slo Shi Bhi GCE SPH ACV LO GHI CEIL Ecp].
    eapply rw_cells_transport in CNT; [| exact MUf| exact WMf| cbn [disjoint_from cells_size csize Nat.add length]; keeplia Slo Shi Bhi GCE SPH ACV LO GHI CEIL Evsc].
    clear MUf WMf.
    try clear VSBC. try clear U8. try clear ERR.
    match goal with X : rw_cells rsegs _ S (vsb_cells _) |- _ => rename X into VSBC end.
    match goal with X : u8arr rsegs _ (vb_buf vv) _ |- _ => rename X into U8 end.
    match goal with X : rw_cells rsegs _ ERRNO0 _ |- _ => rename X into ERR end.
    try clear ST. match goal with X : stk rsegs _ lo _ |- _ => rename X into ST end.
    unfold vsb_cells in VSBC. cbn [vb_error vb_buf vb_size vb_len vb_flags vb_indent vsb_set_flags] in VSBC.
    (* [comment removed for export] *)
    cbn [vb_error vb_len vb_buf vb_size vsb_set_flags].
    unhide Verr. pose proof Verr as E0.
    - (* [comment removed for export] *)
      rewrite E0. change (vsb_result 0 0) with 0.
      zstep. if_cases KZ; zify_cond KZ. { kill KZ. } clear KZ.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      call_lit (VSB_len_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  bvmap_empty (Z_to_bv 32 0) _ S (vsb_set_flags vv VSB_FLAGS_FIN) true lo) by (idtac;
        lazymatch goal with
        | |- mem_inv _ _ => assumption
        | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
        | |- rw_cells _ _ _ (vsb_cells _) => exact VSBC
        | |- vsb_inv _ _ => exact VINV'
        | |- @eq word _ _ => reflexivity
        | |- _ => rewrite ?unsigned_lit by lia; keeplia Slo Shi GCE SPH ACV LO GHI CEIL
        end).
      try clear ST. match goal with X : stk rsegs _ lo _ |- _ => rename X into ST end.
      replace (vsb_result (vb_error (vsb_set_flags vv VSB_FLAGS_FIN)) (vb_len (vsb_set_flags vv VSB_FLAGS_FIN))) with (vb_len vv)
        by (cbn [vb_error vb_len vsb_set_flags]; rewrite E0; reflexivity).
      (* [comment removed for export] *)
      rewrite EEF in VEPC. destruct BEF0 as [EF | EF]; rewrite EF in VEPC.
      + (* [comment removed for export] *)
        zstep. zstep. if_cases KZ; zify_cond KZ. 2:{ kill KZ. } clear KZ.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          assert (VEPCf : rw_cells rsegs mx VEP (vep_cells v tag q)) by (unfold vep_cells; rewrite EVSB, EVC, EVCB, EVCBP, EEF, EF; cbn [vi_cb VI0]; exact VEPC);
          assert (VSBCg : rw_cells rsegs mx S (vsb_cells (vsb_set_flags vv VSB_FLAGS_FIN))) by exact VSBC end.
        apply rz_stop. eapply T6. eapply JT; [assumption | exact MU | exact WM | exact ST | exact FR | exact VEPCf | exact VSBCg | exact U8 |].
        eapply (glob_ok_intro LayoutP0); [exact Ebss| rewrite Ebss; cbn [al_segs LayoutP0]; exact BSS | exact CP | exact CNT].
      + zstep. zstep. if_cases KZ; zify_cond KZ. { kill KZ. } clear KZ.
        (* [comment removed for export] *)
        zstep. if_cases KL; zify_cond KL.
        * (* [comment removed for export] *)
          try clear KL.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
            assert (VEPCf : rw_cells rsegs mx VEP (vep_cells v tag q)) by (unfold vep_cells; rewrite EVSB, EVC, EVCB, EVCBP, EEF, EF; cbn [vi_cb VI0]; exact VEPC);
            assert (VSBCg : rw_cells rsegs mx S (vsb_cells (vsb_set_flags vv VSB_FLAGS_FIN))) by exact VSBC end.
          apply rz_stop. eapply T6. eapply JT; [assumption | exact MU | exact WM | exact ST | exact FR | exact VEPCf | exact VSBCg | exact U8 |].
          eapply (glob_ok_intro LayoutP0); [exact Ebss| rewrite Ebss; cbn [al_segs LayoutP0]; exact BSS | exact CP | exact CNT].
        * (* [comment removed for export] *)
          try clear KL.
          (* [comment removed for export] *)
          zstep. zstep. zstep. zstep. zstep. zstep.
          try replace (bv_unsigned sp - 32 + 32) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
          release_frame FR ST (bv_unsigned sp).
          zstep. cps_done.
          lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
            pose proof (ainv_munch LayoutP0 A m mx md _ AINV MU WM CFP) as AINV9;
            assert (VEPCf : rw_cells rsegs mx VEP (vep_cells v tag q)) by (unfold vep_cells; rewrite EVSB, EVC, EVCB, EVCBP, EEF, EF; cbn [vi_cb VI0]; exact VEPC);
            assert (VSBCg : rw_cells rsegs mx S (vsb_cells (vsb_set_flags vv VSB_FLAGS_FIN))) by exact VSBC end.
          eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ S A _ md v (vsb_set_flags vv VSB_FLAGS_FIN));
            [ exact AINV9 | assumption | exact MDF | exact ST
            | split; [ eapply (glob_ok_intro LayoutP0); [exact Ebss| rewrite Ebss; cbn [al_segs LayoutP0]; exact BSS | exact CP | exact CNT]
                     | eapply (hobj_ok_munch LayoutP0); [exact HOBJ| exact MU| exact WM|];
                       intros a Ha; unfold h_vc, h_wrk, h_req, h_resp, h_hd in Ha; cbn [outside]; keeplia Ha VEPhi Shi Bhi GCE SPH ACV E30 Evsc ]
            | eapply (img_ok0_munch _ m); [exact MU| | exact IMG];
              intros a Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; keeplia Ha VEPbss Simg' Bimg' GCE SPH ACV E30 Evsc
            | split; [exact VLV|]; split; [cbn [al_segs LayoutP0]; exact VEPCf| split; [exact TAG8| exact PADS]]
            | eapply (ws1_obj_munch LayoutP0); [exact WS1| exact MU| exact WM|];
              intros a Ha; unfold h_ws, h_wsbuf in Ha; cbn [outside]; keeplia Ha VEPhi Shi Bhi GCE SPH ACV E30 Evsc DJ1 DJ2 DJ3 WAbss WAhi
            | |
            | replace (S =? 0) with false by (symmetry; apply Z.eqb_neq; keeplia Slo); cbn [vb_size vsb_set_flags]; keeplia BUDJ
            | replace (S =? 0) with false by (symmetry; apply Z.eqb_neq; keeplia Slo); keeplia BUDJ
            | ].
          -- right. split; [keeplia Slo|]. split; [reflexivity|]. split; [apply VOBJT; [exact VSBCg| exact U8]|].
             split; [| unhide BUF0; exact BUF0].
             unhide_neqs. intros y [<-|[<-|[]]]; cbn [vb_buf vsb_set_flags]; [split; [exact NESV| exact NEbV] | split; [exact NESw| exact NEbw]].
          -- exact LIVE0.
          -- unfold VEPFIN_STACK, MARK_STACK, EMITC_STACK, EMITLEN_STACK, REALLOC_STACK.
             eapply (cframe_weaken LayoutP0); [ eapply (cframe_after _ _ _ _ _ _ m0 m); [exact CF| exact MU| intros a Ha NO; OWN a Ha NO |] | lia | | intros a X; exact X | intros a [_ X]; exact X ].
             ++ eapply (stk_mapped (L:=LayoutP0)); [exact ST | exact CEIL | keeplia LO | keeplia LO].
             ++ eapply (stk_mapped (L:=LayoutP0)); [exact ST | exact CEIL | keeplia LO | keeplia LO].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="K NBUD LBUD NPB NEDS NEDV LD0 SPH LO CEIL SP16 TP HG PW HEC"] Lemma T4 : forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) A m md v vv lenb,
    jst A m md v vv false lenb -> lenb <= 10 * N -> vep_cnt v n ->
    realizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 (Z_to_bv 64 VEP) s1
                                    a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               bvmap_empty (Z_to_bv 64 0x1bec4) (Z_to_bv 32 0) None m (seg_rom rsegs)) md) T.
  Proof.
    intros until lenb. intros J LB10 CNT0. prelims.
    pose proof J as J0.
    (first [ dand28 J as AINV MI MDF ST [junk FR] HENV IMG VEPO VB EVSB EIS EAV EST EEF BLM EVP CBX VOBJ SZB LENB NEbV NEbw WS1 LD LIVE0 BUF0 BUDJ CF | destruct J as (AINV & MI & MDF & ST & [junk FR] & HENV & IMG & VEPO & VB & EVSB & EIS & EAV & EST & EEF & BLM & EVP & CBX
                   & VOBJ & SZB & LENB & NEbV & NEbw & WS1 & LD & LIVE0 & BUF0 & BUDJ & CF) ]).
    ufs. unfold NMAX in CBX.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH].
    destruct HENV as [GLOB HOBJ].
    assert (Ebss : h_bss H = 0x41830) by (destruct GLOB as [E _]; rewrite E; reflexivity).
    assert (Evc : h_vc H = h_sp H + 1304) by reflexivity.
    assert (Ewrk : h_wrk H = h_sp H + 1120) by reflexivity.
    assert (Evsc : h_vsc H = h_sp H + 2240) by reflexivity.
    assert (Ecp : h_cp H = h_sp H + 1488) by reflexivity.
    assert (Ews : h_ws H = h_sp H + 1080) by reflexivity.
    assert (Ewb : h_wsbuf H = h_sp H + 16) by reflexivity.
    pose proof PW as (_ & _ & _ & _ & BEF0 & _ & _ & NNM & _ & _ & _ & APART0 & _). unfold NMAX in NNM.
    destruct (APART0 VEP ltac:(left; reflexivity)) as [NESV _]. destruct (APART0 wa ltac:(right; left; reflexivity)) as [NESw _].
    (first [ pose proof (CNT0) as dR_26; dand7 dR_26 as C1 C2 C3 C4 C5 C6 C7 | pose proof CNT0 as (C1 & C2 & C3 & C4 & C5 & C6 & C7) ]).
    (* [comment removed for export] *)
    (first [ pose proof (VEPO) as dR_27; dand4 dR_27 as VLV VEPC TAG8 PADS | pose proof VEPO as (VLV & VEPC & TAG8 & PADS) ]). cbn [al_segs LayoutP0] in VEPC.
    (first [ pose proof ((as_live_ok A m md VEP _ AINV VLV)) as dR_28; dand7 dR_28 as _ VEP16 VEPlo VEPhi VEPimg VEPmap VEPown | pose proof (as_live_ok A m md VEP _ AINV VLV) as (_ & VEP16 & VEPlo & VEPhi & VEPimg & VEPmap & VEPown) ]).
    assert (VEPbss : VEP + 312 <= 0x10000 \/ 0x63000 <= VEP) by (unfold in_image in VEPimg; cbn [al_image_lo al_image_hi LayoutP0] in VEPimg; keeplia VEPimg).
    clear VEPimg VEPown.
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md S vv false AINV VOBJ)) as dR_29; dand11 dR_29 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LayoutP0 A m md S vv false AINV VOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    pose proof Simg as Simg'. pose proof Bimg as Bimg'. unfold off_image in Simg', Bimg'. cbn [al_image_lo al_image_hi LayoutP0] in Simg', Bimg'.
    (first [ pose proof (VOBJ) as dR_30; dand6 dR_30 as _ VINV VLS VLB VNE _ | pose proof VOBJ as (_ & VINV & VLS & VLB & VNE & _) ]).
    pose proof VINV as VINVx. (first [ dand9 VINVx as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm Vsm | destruct VINVx as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm & Vsm) ]).
    pose proof (as_live_disjoint A m md S 40 VEP 312 AINV VLS VLV NESV) as DJS.
    pose proof (as_live_disjoint A m md (vb_buf vv) (vb_size vv) VEP 312 AINV VLB VLV NEbV) as DJB.
    pose proof WS1 as WS1x. (first [ dex2 WS1x as id pad; dand7 WS1x as IDOK PADL _ _ LWA _ _ | dand9 WS1x as id pad IDOK PADL _ _ LWA _ _ | destruct WS1x as (id & pad & IDOK & PADL & _ & _ & LWA & _ & _) ]).
    assert (NEwS : wa <> S) by (intros X; apply NESw; symmetry; exact X).
    assert (NEwB : wa <> vb_buf vv) by (intros X; apply NEbw; symmetry; exact X).
    (first [ pose proof ((as_live_ok A m md wa _ AINV LWA)) as dR_33; dand7 dR_33 as _ _ WAlo WAhi WAimg _ _ | pose proof (as_live_ok A m md wa _ AINV LWA) as (_ & _ & WAlo & WAhi & WAimg & _ & _) ]).
    assert (WAbss : wa + 40 <= 0x10000 \/ 0x63000 <= wa) by (unfold in_image in WAimg; cbn [al_image_lo al_image_hi LayoutP0] in WAimg; keeplia WAimg).
    clear WAimg.
    pose proof (as_live_disjoint A m md S 40 wa 40 AINV VLS LWA (not_eq_sym NEwS)) as DJ1.
    pose proof (as_live_disjoint A m md (vb_buf vv) (vb_size vv) wa 40 AINV VLB LWA (not_eq_sym NEwB)) as DJ2.
    pose proof (as_live_disjoint A m md wa 40 VEP 312 AINV LWA VLV ltac:(intros X; rewrite X in LWA; rewrite VLV in LWA; discriminate LWA)) as DJ3.
    (first [ pose proof ((as_live_ok A m md DATA _ AINV LD)) as dR_34; dand7 dR_34 as _ _ Dlo Dhi _ _ _ | pose proof (as_live_ok A m md DATA _ AINV LD) as (_ & _ & Dlo & Dhi & _ & _ & _) ]).
    (* [comment removed for export] *)
    (first [ pose proof (HOBJ) as dR_35; dand3 dR_35 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]). (first [ dex2 VC as vcpad vcrest; dand3 VC as LVP LVR VC | dand5 VC as vcpad vcrest LVP LVR VC | destruct VC as (vcpad & vcrest & LVP & LVR & VC) ]). (first [ dex2 WK as wkpad wkrest; dand3 WK as LWP LWR WK | dand5 WK as wkpad wkrest LWP LWR WK | destruct WK as (wkpad & wkrest & LWP & LWR & WK) ]).
    cbn [al_segs LayoutP0] in VC, WK. unfold vc_cells in VC. unfold wrk_cells in WK.
    (first [ pose proof (VB) as dR_38; dand5 dR_38 as EVC EVCB EVCBP EVDZ EVURL | pose proof VB as (EVC & EVCB & EVCBP & EVDZ & EVURL) ]).
    unfold vep_cells in VEPC. rewrite EVSB, EVC, EVCB, EVCBP in VEPC. cbn [vi_cb VI0] in VEPC.
    hide DSB. hide Simg. hide Bimg. hide Simg'. hide Bimg'. hide VEPbss. hide DJ1. hide DJ2. hide DJ3. hide DJS. hide DJB.
    hide BUF0. hide LAY. hide WAbss. hide Verr. hide_neqs.
    apply rz_go; [exact MDH | exact MDL |].
    (* [comment removed for export] *)
    zstep. zstep. if_cases KW; zify_cond KW.
    { (* [comment removed for export] *)
      apply rz_stop. eapply T5. exact J0. }
    (* [comment removed for export] *)
    match goal with X : 0 < v Fo_wait |- _ => rename X into OW end.
    pose proof (munch_refl [(bv_unsigned sp - 8512, bv_unsigned sp); (VEP, VEP + 312)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    assert (CFP : client_fp LayoutP0 A [(bv_unsigned sp - 8512, bv_unsigned sp); (VEP, VEP + 312)]).
    { cbn. split; [left; keeplia GCE SPH ACV LO GHI|]. split; [right; left; exists VEP, 312; split; [exact VLV|lia]| exact I]. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    assert (VEPCc : rw_cells rsegs m VEP (vep_cells v tag q)) by ((first [ pose proof (VEPO) as dR_39; dand3 dR_39 as _ X _ | pose proof VEPO as (_ & X & _) ]); cbn [al_segs LayoutP0] in X; exact X).
    clear VEPC.
    unhide VEPbss. unhide DJS. unhide DJB.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_VEPCc); call_fr (vep_default_cb_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                bvmap_empty (Z_to_bv 32 0) m (h_vc H) VEP v tag q 0 vcpad (h_resp H) (h_wrk H) vcrest lo) by (idtac;
      lazymatch goal with
      | |- mem_inv _ _ => assumption
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
      | |- rw_cells _ _ _ (vc_cells _ _ _ _) => unfold vc_cells; exact VC
      | |- rw_cells _ _ _ (vep_cells _ _ _) => exact VEPCc
      | |- @eq word _ _ => first [reflexivity | rewrite EVC; reflexivity | rewrite EVCBP; reflexivity]
      | |- @eq nat _ _ => assumption
      | |- vep_pads_wf _ => assumption
      | |- _ => rewrite ?unsigned_lit by lia; unfold CB_FRAME; keeplia CBX VEPhi GCE SPH ACV LO Evc CEIL
      end).
    hide VEPbss. hide DJS. hide DJB.
    match goal with X : rw_cells rsegs _ VEP (vep_cells _ _ _) |- _ => rename X into VEPC1 end.
    try clear ST. match goal with X : stk rsegs _ lo _ |- _ => rename X into ST end.
    rewrite (vep_cells_ext v (fupd v Fcb_x (v Fcb_x + 0)) tag q (fupd_cbx0 v)) in VEPC1.
    pose proof VEPC1 as VEPC. clear VEPC1. unfold vep_cells in VEPC. rewrite EVSB, EVC, EVCB, EVCBP in VEPC. cbn [vi_cb VI0] in VEPC.
    (* [comment removed for export] *)
    zstep. zstep. rewrite (sx32_small (v Flast_mark)) by (destruct BLM as [E|E]; rewrite E; lia).
    zstep. zstep. zstep.
    apply rz_stop.
    lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
      pose proof (ainv_munch LayoutP0 A m mx md _ AINV MU WM CFP) as AINV2;
      assert (VEPO2 : vep_obj LayoutP0 A mx VEP v tag q)
        by (split; [exact VLV|]; split; [cbn [al_segs LayoutP0]; unfold vep_cells; rewrite EVSB, EVC, EVCB, EVCBP; cbn [vi_cb VI0]; exact VEPC|]; split; [exact TAG8| exact PADS]);
      assert (VOBJ2 : vsb_obj LayoutP0 A mx (v Fvsb) vv false)
        by (rewrite EVSB; eapply (vsb_obj_munch LayoutP0); [exact VOBJ| exact MU| exact WM
            | cbn [disjoint_from]; unhide DJS; refine (conj _ (conj _ I)); keeplia Shi GCE SPH ACV DJS
            | cbn [disjoint_from]; unhide DJB; refine (conj _ (conj _ I)); keeplia Bhi GCE SPH ACV DJB])
    end.
    unhide NESV. unhide NEbV.
    eapply (HEC VEP v tag q vv _ (v Flast_mark) lo);
      [ exact AINV2 | assumption | reflexivity | reflexivity | reflexivity
      | keeplia C1 C2 C3 C4 C5 C6 C7 OW | keeplia C1 C2 C3 C4 C5 C6 C7 CBX | keeplia C4 | exact BLM
      | exact VEPO2 | exact EVDZ | exact VOBJ2 | rewrite EVSB; exact (not_eq_sym NESV) | exact (not_eq_sym NEbV)
      | unfold EXT_MAX; keeplia SZB LENB NNM LB10
      | pose proof (vsb_extendsize_tight (vb_size vv + 9)) as EXTV; pose proof WBGE as WB56; unfold FIN_LIVE in LBUD; keeplia BUDJ LBUD WB56 SZB LENB EXTV LB10
      | pose proof (world_nlive_nonneg va vi) as WNL; keeplia BUDJ NBUD WNL
      | exact TP
      | rewrite unsigned_lit by lia; replace (bv_unsigned sp - 32) with (bv_unsigned sp + -32) by lia; apply align16_add; [exact SP16|reflexivity]
      | rewrite unsigned_lit by lia; reflexivity
      | rewrite unsigned_lit by lia; exact ST | exact CEIL
      | rewrite unsigned_lit by lia; ufs; keeplia LO
      | rewrite unsigned_lit by lia; keeplia GHI SPH | ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 m1 md1 v1 vv1 AINV1 MI1 MDF1 ST1 VEPO1 CASES VOBJ1 LEN1 SZ1 REL1 LIVEq LBe NLe FRK.
    pose proof (as_lazy_nil A1 m1 md1 AINV1) as [MDL1 MDH1].
    rewrite unsigned_lit in ST1, FRK by lia. ufs.
    rewrite EVSB in VOBJ1, FRK.
    replace (ret_pc (Z_to_bv 64 0x1bef8)) with (Z_to_bv 64 0x1bef8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    assert (VK : forall f, f <> Fcrc -> f <> Fo_crc -> f <> Fo_total -> v1 f = v f).
    { destruct CASES as [(_ & -> & _) | (_ & c & ->)]; intros f F1 F2 F3; [reflexivity|]. rewrite !fupd_other by assumption. reflexivity. }
    (* [comment removed for export] *)
    assert (NEbV1 : vb_buf vv1 <> VEP).
    { destruct REL1 as [E|[E _]]; [rewrite E; exact NEbV|]. intros X. rewrite X, VLV in E. discriminate E. }
    assert (NEbw1 : vb_buf vv1 <> wa).
    { destruct REL1 as [E|[E _]]; [rewrite E; unhide NEbw; exact NEbw|]. intros X. rewrite X, LWA in E. discriminate E. }
    assert (LVEP1 : a_live A1 VEP = Some 312) by (rewrite (LIVEq VEP (not_eq_sym NEbV) (not_eq_sym NEbV1)); exact VLV).
    unhide NEwB.
    assert (LWA1 : a_live A1 wa = Some 40) by (rewrite (LIVEq wa NEwB (not_eq_sym NEbw1)); exact LWA).
    assert (NEbD : vb_buf vv <> DATA).
    { unhide BUF0. destruct BUF0 as [E|E]; intros X; rewrite X in E; [exact (NPB E)| rewrite LD0 in E; discriminate E]. }
    assert (NEbD1 : vb_buf vv1 <> DATA).
    { destruct REL1 as [E|[E _]]; [rewrite E; exact NEbD|]. intros X. rewrite X, LD in E. discriminate E. }
    assert (LD1 : a_live A1 DATA = Some N) by (rewrite (LIVEq DATA (not_eq_sym NEbD) (not_eq_sym NEbD1)); exact LD).
    (* [comment removed for export] *)
    assert (HOBJ1 : hobj_ok LayoutP0 VI0 H m1).
    { eapply (hobj_ok_ccall LayoutP0 VI0 H A A1 _ md m1); [exact AINV2| exact FRK| exact HG
        | eapply (hobj_ok_munch LayoutP0); [exact HOBJ| exact MU| exact WM| intros a Ha; unfold h_vc, h_wrk, h_req, h_resp, h_hd in Ha; cbn [outside]; keeplia Ha VEPhi GCE SPH ACV]
        | keeplia SPH |].
      intros a Ha X. unfold h_vc, h_wrk, h_req, h_resp, h_hd, blk in *. keeplia Ha X Shi Bhi VEPhi GCE SPH ACV. }
    assert (GLOB1 : glob_ok LayoutP0 VI0 H m1).
    { eapply (glob_ok_ccall LayoutP0 VI0 H A A1 _ md m1); [exact AINV2| exact FRK| exact HG
        | eapply (glob_ok_munch LayoutP0); [exact GLOB| exact MU| exact WM| intros a Ha; rewrite Ebss in Ha; unfold h_cp, h_vsc in Ha; cbn [outside]; keeplia Ha VEPhi VEPbss GCE SPH ACV]
        | keeplia SPH| keeplia SPH GCE ACV
        | rewrite Ebss; cbn; keeplia ACV| rewrite Ebss; cbn; keeplia ACV
        | intros i Hi; rewrite Ebss; cbn; unfold p0_static; keeplia Hi
        | rewrite Ebss; cbn; change (al_errno LayoutP0) with 0x420b4; keeplia ACV
        | intros a Ha X; rewrite Ebss in Ha; unfold h_cp, h_vsc, blk in *; keeplia Ha X Shi Bhi VEPhi GCE SPH ACV Simg' Bimg' VEPbss]. }
    assert (IMG1 : img_ok0 m1).
    { eapply (img_ok0_ccall A A1 _ md m1); [exact AINV2| exact FRK| unfold IMG0_HI; keeplia GCE SPH ACV| |
        eapply (img_ok0_munch _ m); [exact MU| intros a Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; keeplia Ha VEPbss GCE SPH ACV| exact IMG]].
      intros a Ha X. unfold IMG0_LO, IMG0_HI, blk in *. keeplia Ha X Simg' Bimg' VEPbss. }
    assert (WS1_1 : ws1_obj LayoutP0 H A1 m1 wa VEP).
    { eapply (ws1_obj_ccall LayoutP0 H A A1 _ md m1); [exact AINV2| exact FRK| exact HG
        | eapply (ws1_obj_munch LayoutP0); [exact WS1| exact MU| exact WM| intros a Ha; unfold h_ws, h_wsbuf in Ha; cbn [outside]; keeplia Ha VEPhi GCE SPH ACV DJ3 WAhi]
        | keeplia SPH| keeplia SPH GCE ACV| exact LWA1| exact LVEP1|].
      intros a Ha X. unfold h_ws, h_wsbuf, blk in *. keeplia Ha X Shi Bhi VEPhi GCE SPH ACV DJ1 DJ2 DJ3. }
    (* [comment removed for export] *)
    lazymatch type of MU with munch _ _ ?mx =>
      pose proof (crange_stack (L:=LayoutP0) A mx md (bv_unsigned sp - 32) 32 AINV2 ltac:(keeplia GCE SPH ACV) ltac:(keeplia GHI SPH)
                    (rw_cells_mapped LayoutP0 mx _ _ FR ltac:(off_image_solve LayoutP0))) as CRF end.
    try clear VC. try clear WK. try clear VEPCc. clear VEPC ST. hide_neqs. acall_xfer FRK. unhide_neqs.
    (* [comment removed for export] *)
    eapply T5 with (lenb := 10 * N + 9).
    split; [exact AINV1|]. split; [exact MI1|]. split; [eapply md_frame_trans; [exact MDF| exact MDF1]|]. split; [exact ST1|].
    split; [exists junk; exact FR|].
    split; [split; [exact GLOB1| exact HOBJ1]|]. split; [exact IMG1|].
    split; [exact VEPO1|].
    split. { unfold vep_base. rewrite !VK by discriminate. exact VB. }
    split; [rewrite VK by discriminate; exact EVSB|]. split; [rewrite VK by discriminate; exact EIS|]. split; [rewrite VK by discriminate; exact EAV|].
    split; [rewrite VK by discriminate; exact EST|]. split; [rewrite VK by discriminate; exact EEF|].
    split; [rewrite VK by discriminate; exact BLM|]. split; [rewrite VK by discriminate; exact EVP|].
    split; [rewrite VK by discriminate; unfold NMAX; exact CBX|].
    split; [exact VOBJ1|]. split; [keeplia SZ1 SZB LEN1|]. split; [keeplia LEN1 LENB LB10|].
    split; [exact NEbV1|]. split; [exact NEbw1|]. split; [exact WS1_1|]. split; [exact LD1|].
    split. { intros p k L0 NS NP. rewrite (LIVEq p).
             - exact (LIVE0 p k L0 NS NP).
             - intros ->. unhide BUF0. destruct BUF0 as [E|E]; [exact (NP E)| rewrite E in L0; discriminate L0].
             - intros ->. destruct REL1 as [E|[E _]].
               + rewrite E in *. unhide BUF0. destruct BUF0 as [E2|E2]; [exact (NP E2)| rewrite E2 in L0; discriminate L0].
               + rewrite (LIVE0 _ _ L0 NS NP) in E. discriminate E. }
    split. { destruct REL1 as [E|[E _]]; [rewrite E; unhide BUF0; exact BUF0|].
             destruct (a_live A0 (vb_buf vv1)) as [k|] eqn:L0; [|right; reflexivity]. left.
             destruct (Classical_Prop.classic (parse_blocks v0 vv0 va vi (vb_buf vv1))) as [Y|NP]; [exact Y|]. exfalso.
             assert (NS1 : vb_buf vv1 <> S) by (intros X; rewrite X, VLS in E; discriminate E).
             rewrite (LIVE0 _ k L0 NS1 NP) in E. discriminate E. }
    split; [keeplia BUDJ LBe NLe|].
    (* [comment removed for export] *)
    unfold VEPFIN_STACK, MARK_STACK, EMITC_STACK, EMITLEN_STACK, REALLOC_STACK.
    assert (CF2 : cframe LayoutP0 (owned A) (owned A1) (bv_unsigned sp) 8512
                    (fun a => blk VEP 312 a \/ blk (vb_buf vv) (vb_size vv) a \/ S <= a < S + 40) (blk (vb_buf vv1) (vb_size vv1)) m m1).
    { eapply (cframe_extend LayoutP0 _ _ _ _ _ _ _ _ _ _ m _ m1 m1 _ []);
        [ exact MU | | exact FRK | keeplia ACV | keeplia ACV
        | intros a X; exact X | intros a X; left; exact X | apply munch_refl | intros a _ X; exfalso; apply X; exact I
        | eapply (window_mapped LayoutP0 _ lo); [exact ST1 | exact FR | cbn; lia | exact CEIL | keeplia LO | keeplia LO] ].
      intros a Ha NO. cbn [outside] in NO.
      assert (CS : bv_unsigned sp - 8512 <= a < bv_unsigned sp \/ VEP <= a < VEP + 312) by keeplia Ha NO. clear NO.
      destruct CS as [X|X]; [left; exact X| right; left; unfold blk; split; [keeplia VEPlo| exact X]]. }
    eapply (cframe_seq LayoutP0 _ _ _ _ _ _ _ _ _ _ _ _ _ m0 m m1 CF CF2);
      [ keeplia ACV | keeplia ACV
      | eapply (window_mapped LayoutP0 _ lo); [exact ST1 | exact FR | cbn; lia | exact CEIL | keeplia LO | keeplia LO]
      | intros a X; exact X | | ].
    - (* [comment removed for export] *)
      intros a [X|[X|X]].
      + right. left. exact X.
      + left. right. exact X.
      + right. right. left. left. unfold blk. split; [keeplia Slo ES| rewrite <- ES; exact X].
    - (* [comment removed for export] *)
      intros a [X|X].
      + left. left. exact X.
      + right. left. exact X.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="K NBUD LBUD NPB NEDS NEDV DRANGE N0 LD0 SPH LO CEIL SP16 TP HG PW HEC HMC"] Lemma T3 : forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) A m md v vv,
    jst A m md v vv false (7 * N) -> vep_cnt v n ->
    realizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 (Z_to_bv 64 VEP) s1
                                    a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               bvmap_empty (Z_to_bv 64 0x1beac) (Z_to_bv 32 0) None m (seg_rom rsegs)) md) T.
  Proof.
    intros until vv. intros J CNT0. prelims.
    pose proof J as J0.
    (first [ dand28 J as AINV MI MDF ST [junk FR] HENV IMG VEPO VB EVSB EIS EAV EST EEF BLM EVP CBX VOBJ SZB LENB NEbV NEbw WS1 LD LIVE0 BUF0 BUDJ CF | destruct J as (AINV & MI & MDF & ST & [junk FR] & HENV & IMG & VEPO & VB & EVSB & EIS & EAV & EST & EEF & BLM & EVP & CBX
                   & VOBJ & SZB & LENB & NEbV & NEbw & WS1 & LD & LIVE0 & BUF0 & BUDJ & CF) ]).
    ufs. unfold NMAX in CBX.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH].
    pose proof HENV as [GLOB HOBJ].
    assert (Ebss : h_bss H = 0x41830) by (destruct GLOB as [E _]; rewrite E; reflexivity).
    assert (Evc : h_vc H = h_sp H + 1304) by reflexivity.
    assert (Ewrk : h_wrk H = h_sp H + 1120) by reflexivity.
    assert (Evsc : h_vsc H = h_sp H + 2240) by reflexivity.
    assert (Ecp : h_cp H = h_sp H + 1488) by reflexivity.
    assert (Ews : h_ws H = h_sp H + 1080) by reflexivity.
    assert (Ewb : h_wsbuf H = h_sp H + 16) by reflexivity.
    pose proof PW as (_ & _ & _ & _ & BEF0 & _ & NN0 & NNM & VP0 & _ & _ & APART0 & _). unfold NMAX in NNM.
    destruct (APART0 VEP ltac:(left; reflexivity)) as [NESV _]. destruct (APART0 wa ltac:(right; left; reflexivity)) as [NESw _].
    (first [ pose proof (CNT0) as dR_41; dand7 dR_41 as C1 C2 C3 C4 C5 C6 C7 | pose proof CNT0 as (C1 & C2 & C3 & C4 & C5 & C6 & C7) ]).
    (* [comment removed for export] *)
    (first [ pose proof (VEPO) as dR_42; dand4 dR_42 as VLV VEPC TAG8 PADS | pose proof VEPO as (VLV & VEPC & TAG8 & PADS) ]). cbn [al_segs LayoutP0] in VEPC.
    (first [ pose proof ((as_live_ok A m md VEP _ AINV VLV)) as dR_43; dand7 dR_43 as _ VEP16 VEPlo VEPhi VEPimg VEPmap VEPown | pose proof (as_live_ok A m md VEP _ AINV VLV) as (_ & VEP16 & VEPlo & VEPhi & VEPimg & VEPmap & VEPown) ]).
    assert (VEPbss : VEP + 312 <= 0x10000 \/ 0x63000 <= VEP) by (unfold in_image in VEPimg; cbn [al_image_lo al_image_hi LayoutP0] in VEPimg; keeplia VEPimg).
    clear VEPimg VEPown.
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md S vv false AINV VOBJ)) as dR_44; dand11 dR_44 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LayoutP0 A m md S vv false AINV VOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    pose proof Simg as Simg'. pose proof Bimg as Bimg'. unfold off_image in Simg', Bimg'. cbn [al_image_lo al_image_hi LayoutP0] in Simg', Bimg'.
    (first [ pose proof (VOBJ) as dR_45; dand6 dR_45 as _ VINV VLS VLB VNE _ | pose proof VOBJ as (_ & VINV & VLS & VLB & VNE & _) ]).
    pose proof VINV as VINVx. (first [ dand9 VINVx as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm Vsm | destruct VINVx as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm & Vsm) ]).
    pose proof (as_live_disjoint A m md S 40 VEP 312 AINV VLS VLV NESV) as DJS.
    pose proof (as_live_disjoint A m md (vb_buf vv) (vb_size vv) VEP 312 AINV VLB VLV NEbV) as DJB.
    pose proof WS1 as WS1x. (first [ dex2 WS1x as id pad; dand7 WS1x as IDOK PADL _ _ LWA _ _ | dand9 WS1x as id pad IDOK PADL _ _ LWA _ _ | destruct WS1x as (id & pad & IDOK & PADL & _ & _ & LWA & _ & _) ]).
    assert (NEwS : wa <> S) by (intros X; apply NESw; symmetry; exact X).
    assert (NEwB : wa <> vb_buf vv) by (intros X; apply NEbw; symmetry; exact X).
    (first [ pose proof ((as_live_ok A m md wa _ AINV LWA)) as dR_48; dand7 dR_48 as _ _ WAlo WAhi WAimg _ _ | pose proof (as_live_ok A m md wa _ AINV LWA) as (_ & _ & WAlo & WAhi & WAimg & _ & _) ]).
    assert (WAbss : wa + 40 <= 0x10000 \/ 0x63000 <= wa) by (unfold in_image in WAimg; cbn [al_image_lo al_image_hi LayoutP0] in WAimg; keeplia WAimg).
    clear WAimg.
    pose proof (as_live_disjoint A m md S 40 wa 40 AINV VLS LWA (not_eq_sym NEwS)) as DJ1.
    pose proof (as_live_disjoint A m md (vb_buf vv) (vb_size vv) wa 40 AINV VLB LWA (not_eq_sym NEwB)) as DJ2.
    pose proof (as_live_disjoint A m md wa 40 VEP 312 AINV LWA VLV ltac:(intros X; rewrite X in LWA; rewrite VLV in LWA; discriminate LWA)) as DJ3.
    (first [ pose proof ((as_live_ok A m md DATA _ AINV LD)) as dR_49; dand7 dR_49 as _ _ Dlo Dhi _ _ _ | pose proof (as_live_ok A m md DATA _ AINV LD) as (_ & _ & Dlo & Dhi & _ & _ & _) ]).
    assert (NEbD : vb_buf vv <> DATA).
    { destruct BUF0 as [E|E]; intros X; rewrite X in E; [exact (NPB E)| rewrite LD0 in E; discriminate E]. }
    (* [comment removed for export] *)
    (first [ pose proof (VB) as dR_50; dand5 dR_50 as EVC EVCB EVCBP EVDZ EVURL | pose proof VB as (EVC & EVCB & EVCBP & EVDZ & EVURL) ]).
    unfold vep_cells in VEPC. rewrite EVSB, EVC, EVCB, EVCBP in VEPC. cbn [vi_cb VI0] in VEPC.
    hide DSB. hide Simg. hide Bimg. hide Simg'. hide Bimg'. hide VEPbss. hide DJ1. hide DJ2. hide DJ3. hide DJS. hide DJB.
    hide BUF0. hide LAY. hide WAbss. hide Verr. hide_neqs.
    apply rz_go; [exact MDH | exact MDL |].
    (* [comment removed for export] *)
    zstep. zstep. if_cases KP; zify_cond KP.
    { (* [comment removed for export] *)
      apply rz_stop. eapply T4; [exact J0 | keeplia NN0 | exact CNT0]. }
    (* [comment removed for export] *)
    zstep. zstep. rewrite (sx32_small (v Flast_mark)) by (destruct BLM as [E|E]; rewrite E; lia).
    zstep. zstep.
    apply rz_stop.
    unhide NESV. unhide NEbV.
    eapply (HMC VEP v tag q vv H (v Fver_p) (v Flast_mark) n [] lo);
      [ exact AINV | exact MI | reflexivity | reflexivity | reflexivity | exact BLM
      | exact VEPO | exact VB | exact HENV | exact HG | exact IMG | exact BLM | exact CNT0 | keeplia NN0 | unfold NMAX; keeplia NN0 NNM
      | rewrite EVSB; exact VOBJ | rewrite EVSB; exact (not_eq_sym NESV) | exact (not_eq_sym NEbV)
      | unfold EXT_MAX; keeplia SZB LENB NNM NN0
      | pose proof (vsb_extendsize_tight (vb_size vv + 9)) as EXTV; pose proof WBGE as WB56; unfold FIN_LIVE in LBUD; keeplia BUDJ LBUD WB56 SZB LENB EXTV NN0
      | pose proof (world_nlive_nonneg va vi) as WNL; keeplia BUDJ NBUD WNL
      | split; [keeplia VP0 EVP| split; [cbn [length]; change (Z.of_nat 0) with 0; keeplia VP0 EVP ACV| intros i Hi; exfalso; cbn in Hi; keeplia Hi]]
      | cbn [length]; change (Z.of_nat 0) with 0; keeplia VP0
      | keeplia VP0 EVP | keeplia VP0 EVP ACV
      | right; exists DATA, N; split; [exact LD|]; split; [exact N0|]; split; [keeplia DRANGE EVP|]; split; [keeplia DRANGE EVP|];
        split; [exact NEDV|]; split; [rewrite EVSB; exact NEDS| exact (not_eq_sym NEbD)]
      | exact TP
      | rewrite unsigned_lit by lia; replace (bv_unsigned sp - 32) with (bv_unsigned sp + -32) by lia; apply align16_add; [exact SP16|reflexivity]
      | rewrite unsigned_lit by lia; reflexivity
      | rewrite unsigned_lit by lia; exact ST | exact CEIL
      | rewrite unsigned_lit by lia; ufs; keeplia LO
      | rewrite unsigned_lit by lia; keeplia SPH | ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 m1 md1 v1 vv1 AINV1 MI1 MDF1 ST1 VEPO1 VK EVP1 ELM1 EPD1 CNT1 CRC1 CRCP1 VOBJ1 LEN1 SZ1 REL1 LIVEq LBe NLe HENV1 BS1 FRK.
    pose proof (as_lazy_nil A1 m1 md1 AINV1) as [MDL1 MDH1].
    rewrite unsigned_lit in ST1, FRK by lia. ufs.
    rewrite EVSB in VOBJ1, FRK.
    replace (n + (v Fver_p - v Fver_p)) with n in CNT1 by lia.
    replace (ret_pc (Z_to_bv 64 0x1bec4)) with (Z_to_bv 64 0x1bec4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (first [ pose proof (CNT1) as dR_51; dand7 dR_51 as D1 D2 D3 D4 D5 D6 D7 | pose proof CNT1 as (D1 & D2 & D3 & D4 & D5 & D6 & D7) ]).
    (* [comment removed for export] *)
    assert (NEbV1 : vb_buf vv1 <> VEP).
    { destruct REL1 as [E|[E _]]; [rewrite E; exact NEbV|]. intros X. rewrite X, VLV in E. discriminate E. }
    unhide NEbw.
    assert (NEbw1 : vb_buf vv1 <> wa).
    { destruct REL1 as [E|[E _]]; [rewrite E; exact NEbw|]. intros X. rewrite X, LWA in E. discriminate E. }
    assert (LVEP1 : a_live A1 VEP = Some 312) by (rewrite (LIVEq VEP (not_eq_sym NEbV) (not_eq_sym NEbV1)); exact VLV).
    unhide NEwB.
    assert (LWA1 : a_live A1 wa = Some 40) by (rewrite (LIVEq wa NEwB (not_eq_sym NEbw1)); exact LWA).
    assert (NEbD1 : vb_buf vv1 <> DATA).
    { destruct REL1 as [E|[E _]]; [rewrite E; exact NEbD|]. intros X. rewrite X, LD in E. discriminate E. }
    assert (LD1 : a_live A1 DATA = Some N) by (rewrite (LIVEq DATA (not_eq_sym NEbD) (not_eq_sym NEbD1)); exact LD).
    assert (IMG1 : img_ok0 m1).
    { eapply (img_ok0_ccall A A1 m md m1); [exact AINV| exact FRK| unfold IMG0_HI; keeplia GCE SPH ACV| | exact IMG].
      intros a Ha X. unfold IMG0_LO, IMG0_HI, blk in *. keeplia Ha X Simg' Bimg' VEPbss. }
    assert (WS1_1 : ws1_obj LayoutP0 H A1 m1 wa VEP).
    { eapply (ws1_obj_ccall LayoutP0 H A A1 m md m1); [exact AINV| exact FRK| exact HG| exact WS1| keeplia SPH| keeplia SPH GCE ACV| exact LWA1| exact LVEP1|].
      intros a Ha X. unfold h_ws, h_wsbuf, blk in *. keeplia Ha X Shi Bhi VEPhi GCE SPH ACV DJ1 DJ2 DJ3. }
    pose proof (crange_stack (L:=LayoutP0) A m md (bv_unsigned sp - 32) 32 AINV ltac:(keeplia GCE SPH ACV) ltac:(keeplia GHI SPH)
                  (rw_cells_mapped LayoutP0 m _ _ FR ltac:(off_image_solve LayoutP0))) as CRF.
    clear VEPC ST. hide_neqs. acall_xfer FRK. unhide_neqs.
    (* [comment removed for export] *)
    eapply T4 with (lenb := 10 * N); [| keeplia NN0 | exact CNT1].
    split; [exact AINV1|]. split; [exact MI1|]. split; [eapply md_frame_trans; [exact MDF| exact MDF1]|]. split; [exact ST1|].
    split; [exists junk; exact FR|].
    split; [exact HENV1|]. split; [exact IMG1|].
    split; [exact VEPO1|].
    split. { unfold vep_base. rewrite !VK by (cbn; (let X := fresh "X" in intros X; mem_hyp X)). exact VB. }
    split; [rewrite VK by (cbn; (let X := fresh "X" in intros X; mem_hyp X)); exact EVSB|].
    split; [rewrite VK by (cbn; (let X := fresh "X" in intros X; mem_hyp X)); exact EIS|].
    split; [rewrite VK by (cbn; (let X := fresh "X" in intros X; mem_hyp X)); exact EAV|].
    split; [rewrite VK by (cbn; (let X := fresh "X" in intros X; mem_hyp X)); exact EST|].
    split; [rewrite VK by (cbn; (let X := fresh "X" in intros X; mem_hyp X)); exact EEF|].
    split; [rewrite ELM1; exact BLM|]. split; [rewrite EVP1; exact EVP|].
    split; [unfold NMAX; keeplia D1 D2 D3 NN0 NNM|].
    split; [exact VOBJ1|]. split; [keeplia SZ1 SZB LEN1|]. split; [keeplia LEN1 LENB D1 D2 D3 D5 C4 NN0|].
    split; [exact NEbV1|]. split; [exact NEbw1|]. split; [exact WS1_1|]. split; [exact LD1|].
    split. { intros p k L0 NS NP. rewrite (LIVEq p).
             - exact (LIVE0 p k L0 NS NP).
             - intros ->. unhide BUF0. destruct BUF0 as [E|E]; [exact (NP E)| rewrite E in L0; discriminate L0].
             - intros ->. destruct REL1 as [E|[E _]].
               + rewrite E in *. unhide BUF0. destruct BUF0 as [E2|E2]; [exact (NP E2)| rewrite E2 in L0; discriminate L0].
               + rewrite (LIVE0 _ _ L0 NS NP) in E. discriminate E. }
    split. { destruct REL1 as [E|[E _]]; [rewrite E; unhide BUF0; exact BUF0|].
             destruct (a_live A0 (vb_buf vv1)) as [k|] eqn:L0; [|right; reflexivity]. left.
             destruct (Classical_Prop.classic (parse_blocks v0 vv0 va vi (vb_buf vv1))) as [Y|NP]; [exact Y|]. exfalso.
             assert (NS1 : vb_buf vv1 <> S) by (intros X; rewrite X, VLS in E; discriminate E).
             rewrite (LIVE0 _ k L0 NS1 NP) in E. discriminate E. }
    split; [keeplia BUDJ LBe NLe|].
    (* [comment removed for export] *)
    unfold VEPFIN_STACK, MARK_STACK, EMITC_STACK, EMITLEN_STACK, REALLOC_STACK.
    assert (CF2 : cframe LayoutP0 (owned A) (owned A1) (bv_unsigned sp) 8512
                    (fun a => blk VEP 312 a \/ blk (vb_buf vv) (vb_size vv) a \/ S <= a < S + 40) (blk (vb_buf vv1) (vb_size vv1)) m m1).
    { eapply (cframe_extend LayoutP0 _ _ _ _ _ _ _ _ _ _ m m m1 m1 [] []);
        [ apply munch_refl | intros a _ X; exfalso; apply X; exact I | exact FRK | keeplia ACV | keeplia ACV
        | intros a X; exact X | intros a X; left; exact X | apply munch_refl | intros a _ X; exfalso; apply X; exact I
        | eapply (window_mapped LayoutP0 _ lo); [exact ST1 | exact FR | cbn; lia | exact CEIL | keeplia LO | keeplia LO] ]. }
    eapply (cframe_seq LayoutP0 _ _ _ _ _ _ _ _ _ _ _ _ _ m0 m m1 CF CF2);
      [ keeplia ACV | keeplia ACV
      | eapply (window_mapped LayoutP0 _ lo); [exact ST1 | exact FR | cbn; lia | exact CEIL | keeplia LO | keeplia LO]
      | intros a X; exact X | | ].
    - intros a [X|[X|X]].
      + right. left. exact X.
      + left. right. exact X.
      + right. right. left. left. unfold blk. split; [keeplia Slo ES| rewrite <- ES; exact X].
    - intros a [X|X].
      + left. left. exact X.
      + right. left. exact X.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="K NBUD LBUD NPB NEDS NEDV DRANGE N0 LD0 SPH LO CEIL SP16 TP HG PW HEC HMC"] Lemma T2 : forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) A m md v vv,
    jst A m md v vv false (7 * N) -> vep_cnt v n ->
    realizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 (Z_to_bv 64 VEP) s1
                                    a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               bvmap_empty (Z_to_bv 64 0x1be2c) (Z_to_bv 32 0) None m (seg_rom rsegs)) md) T.
  Proof.
    intros until vv. intros J CNT0. prelims.
    pose proof J as J0.
    (first [ dand28 J as AINV MI MDF ST [junk FR] HENV IMG VEPO VB EVSB EIS EAV EST EEF BLM EVP CBX VOBJ SZB LENB NEbV NEbw WS1 LD LIVE0 BUF0 BUDJ CF | destruct J as (AINV & MI & MDF & ST & [junk FR] & HENV & IMG & VEPO & VB & EVSB & EIS & EAV & EST & EEF & BLM & EVP & CBX
                   & VOBJ & SZB & LENB & NEbV & NEbw & WS1 & LD & LIVE0 & BUF0 & BUDJ & CF) ]).
    ufs.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH].
    pose proof HENV as [GLOB HOBJ].
    assert (Ebss : h_bss H = 0x41830) by (destruct GLOB as [E _]; rewrite E; reflexivity).
    assert (Evc : h_vc H = h_sp H + 1304) by reflexivity.
    assert (Ewrk : h_wrk H = h_sp H + 1120) by reflexivity.
    assert (Evsc : h_vsc H = h_sp H + 2240) by reflexivity.
    assert (Ecp : h_cp H = h_sp H + 1488) by reflexivity.
    assert (Ews : h_ws H = h_sp H + 1080) by reflexivity.
    assert (Ewb : h_wsbuf H = h_sp H + 16) by reflexivity.
    pose proof PW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & APART0 & _).
    destruct (APART0 VEP ltac:(left; reflexivity)) as [NESV _]. destruct (APART0 wa ltac:(right; left; reflexivity)) as [NESw _].
    (* [comment removed for export] *)
    (first [ pose proof (VEPO) as dR_53; dand4 dR_53 as VLV VEPC TAG8 PADS | pose proof VEPO as (VLV & VEPC & TAG8 & PADS) ]). cbn [al_segs LayoutP0] in VEPC.
    (first [ pose proof ((as_live_ok A m md VEP _ AINV VLV)) as dR_54; dand7 dR_54 as _ VEP16 VEPlo VEPhi VEPimg VEPmap VEPown | pose proof (as_live_ok A m md VEP _ AINV VLV) as (_ & VEP16 & VEPlo & VEPhi & VEPimg & VEPmap & VEPown) ]).
    assert (VEPbss : VEP + 312 <= 0x10000 \/ 0x63000 <= VEP) by (unfold in_image in VEPimg; cbn [al_image_lo al_image_hi LayoutP0] in VEPimg; keeplia VEPimg).
    clear VEPimg VEPown.
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md S vv false AINV VOBJ)) as dR_55; dand11 dR_55 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LayoutP0 A m md S vv false AINV VOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    pose proof Simg as Simg'. pose proof Bimg as Bimg'. unfold off_image in Simg', Bimg'. cbn [al_image_lo al_image_hi LayoutP0] in Simg', Bimg'.
    (first [ pose proof (VOBJ) as dR_56; dand6 dR_56 as _ VINV VLS VLB VNE _ | pose proof VOBJ as (_ & VINV & VLS & VLB & VNE & _) ]).
    pose proof VINV as VINVx. (first [ dand9 VINVx as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm Vsm | destruct VINVx as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm & Vsm) ]).
    pose proof (as_live_disjoint A m md S 40 VEP 312 AINV VLS VLV NESV) as DJS.
    pose proof (as_live_disjoint A m md (vb_buf vv) (vb_size vv) VEP 312 AINV VLB VLV NEbV) as DJB.
    pose proof WS1 as WS1x. (first [ dex2 WS1x as id pad; dand7 WS1x as IDOK PADL _ _ LWA _ _ | dand9 WS1x as id pad IDOK PADL _ _ LWA _ _ | destruct WS1x as (id & pad & IDOK & PADL & _ & _ & LWA & _ & _) ]).
    assert (NEwS : wa <> S) by (intros X; apply NESw; symmetry; exact X).
    assert (NEwB : wa <> vb_buf vv) by (intros X; apply NEbw; symmetry; exact X).
    (first [ pose proof ((as_live_ok A m md wa _ AINV LWA)) as dR_59; dand7 dR_59 as _ _ WAlo WAhi WAimg _ _ | pose proof (as_live_ok A m md wa _ AINV LWA) as (_ & _ & WAlo & WAhi & WAimg & _ & _) ]).
    assert (WAbss : wa + 40 <= 0x10000 \/ 0x63000 <= wa) by (unfold in_image in WAimg; cbn [al_image_lo al_image_hi LayoutP0] in WAimg; keeplia WAimg).
    clear WAimg.
    pose proof (as_live_disjoint A m md S 40 wa 40 AINV VLS LWA (not_eq_sym NEwS)) as DJ1.
    pose proof (as_live_disjoint A m md (vb_buf vv) (vb_size vv) wa 40 AINV VLB LWA (not_eq_sym NEwB)) as DJ2.
    pose proof (as_live_disjoint A m md wa 40 VEP 312 AINV LWA VLV ltac:(intros X; rewrite X in LWA; rewrite VLV in LWA; discriminate LWA)) as DJ3.
    (* [comment removed for export] *)
    (first [ pose proof (HOBJ) as dR_60; dand3 dR_60 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]). (first [ dex2 VC as vcpad vcrest; dand3 VC as LVP LVR VC | dand5 VC as vcpad vcrest LVP LVR VC | destruct VC as (vcpad & vcrest & LVP & LVR & VC) ]). (first [ dex2 WK as wkpad wkrest; dand3 WK as LWP LWR WK | dand5 WK as wkpad wkrest LWP LWR WK | destruct WK as (wkpad & wkrest & LWP & LWR & WK) ]).
    cbn [al_segs LayoutP0] in VC, WK. unfold vc_cells in VC. unfold wrk_cells in WK.
    (first [ pose proof (GLOB) as dR_63; dand4 dR_63 as _ BSS CP [cnt CNT] | pose proof GLOB as (_ & BSS & CP & [cnt CNT]) ]). rewrite Ebss in BSS. cbn [al_segs LayoutP0] in BSS, CP, CNT.
    pose proof IMG as IMGx. (first [ dand4 IMGx as _ _ GVSC _ | destruct IMGx as (_ & _ & GVSC & _) ]). unfold GOT_vsc in GVSC.
    (first [ pose proof (VB) as dR_65; dand5 dR_65 as EVC EVCB EVCBP EVDZ EVURL | pose proof VB as (EVC & EVCB & EVCBP & EVDZ & EVURL) ]).
    unfold vep_cells in VEPC. rewrite EVSB, EVC, EVCB, EVCBP in VEPC. cbn [vi_cb VI0] in VEPC.
    pose proof (munch_refl [(bv_unsigned sp - 8512, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (CFP : client_fp LayoutP0 A [(bv_unsigned sp - 8512, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320)]).
    { cbn. split; [left; keeplia GCE SPH ACV LO GHI|]. split; [left; keeplia GCE SPH ACV Evsc GHI| exact I]. }
    hide DSB. hide Simg. hide Bimg. hide Simg'. hide Bimg'. hide VEPbss. hide DJ1. hide DJ2. hide DJ3. hide DJS. hide DJB.
    hide BUF0. hide LAY. hide WAbss. hide Verr. hide_neqs.
    apply rz_go; [exact MDH | exact MDL |].
    (* [comment removed for export] *)
    zstep.
    zstep. zstep. zstep. if_cases K1; [apply rz_stop; eapply T3; [exact J0 | exact CNT0] |]. clear K1.
    zstep. zstep. zstep. if_cases K1; [apply rz_stop; eapply T3; [exact J0 | exact CNT0] |]. clear K1.
    zstep. zstep. zstep. if_cases K1; [apply rz_stop; eapply T3; [exact J0 | exact CNT0] |]. clear K1.
    zstep. zstep. zstep. if_cases K1; [apply rz_stop; eapply T3; [exact J0 | exact CNT0] |]. clear K1.
    zstep. zstep. zstep. if_cases K1; [apply rz_stop; eapply T3; [exact J0 | exact CNT0] |]. clear K1.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    carve_frame 48%nat ST. try replace (bv_unsigned sp + -32 + -48) with (bv_unsigned sp + -80) in * by lia.
    try replace (bv_unsigned sp - 32 - 48) with (bv_unsigned sp + -80) in * by lia.
    zstep. stub_begin FR0 (bv_unsigned sp + -80) (bv_unsigned sp + -32).
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. stub_end MUstub WMstub.
    try replace (bv_unsigned sp + -80 + 48) with (bv_unsigned sp + -32) by lia.
    release_frame FR0 ST (bv_unsigned sp + -32).
    destruct (rw_cells_forget _ _ _ _ CNT) as [cnt' CNT']. cbn [cells_size csize Nat.add] in CNT'. clear CNT.
    (* [comment removed for export] *)
    apply rz_stop.
    lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
      assert (VEPCf : rw_cells rsegs mx VEP (vep_cells v tag q)) by (unfold vep_cells; rewrite EVSB, EVC, EVCB, EVCBP; cbn [vi_cb VI0]; exact VEPC);
      pose proof (ainv_munch LayoutP0 A m mx md _ AINV MU WM CFP) as AINV9 end.
    eapply T3; [| exact CNT0].
    split; [exact AINV9|]. split; [assumption|]. split; [exact MDF|]. split; [exact ST|]. split; [exists junk; exact FR|].
    split. { split. { eapply (glob_ok_intro LayoutP0); [exact Ebss| rewrite Ebss; cbn [al_segs LayoutP0]; exact BSS | exact CP | exact CNT']. }
             eapply (hobj_ok_munch LayoutP0); [exact HOBJ| exact MU| exact WM|].
             intros a Ha. unfold h_vc, h_wrk, h_req, h_resp, h_hd in Ha. cbn [outside]. keeplia Ha GCE SPH ACV Evsc. }
    split. { eapply (img_ok0_munch _ m); [exact MU| | exact IMG]. intros a Ha. unfold IMG0_LO, IMG0_HI in Ha. cbn [outside]. keeplia Ha GCE SPH ACV Evsc. }
    split. { split; [exact VLV|]. split; [cbn [al_segs LayoutP0]; exact VEPCf|]. split; [exact TAG8| exact PADS]. }
    split; [exact VB|]. split; [exact EVSB|]. split; [exact EIS|]. split; [exact EAV|]. split; [exact EST|]. split; [exact EEF|].
    split; [exact BLM|]. split; [exact EVP|]. split; [exact CBX|].
    split. { eapply (vsb_obj_munch LayoutP0); [exact VOBJ| exact MU| exact WM
               | cbn [disjoint_from]; refine (conj _ (conj _ I)); keeplia Shi GCE SPH ACV Evsc
               | cbn [disjoint_from]; refine (conj _ (conj _ I)); keeplia Bhi GCE SPH ACV Evsc]. }
    split; [exact SZB|]. split; [exact LENB|]. split; [unhide NEbV; exact NEbV|]. split; [unhide NEbw; exact NEbw|].
    split. { eapply (ws1_obj_munch LayoutP0); [exact WS1| exact MU| exact WM|]. intros a Ha. unfold h_ws, h_wsbuf in Ha. cbn [outside].
             keeplia Ha WAhi GCE SPH ACV Evsc. }
    split; [exact LD|]. split; [exact LIVE0|]. split; [unhide BUF0; exact BUF0|].
    split; [exact BUDJ|].
    unfold VEPFIN_STACK, MARK_STACK, EMITC_STACK, EMITLEN_STACK, REALLOC_STACK.
    eapply (cframe_after _ _ _ _ _ _ m0 m); [exact CF| exact MU| intros a Ha NO; OWN a Ha NO |].
    eapply (window_mapped LayoutP0 _ lo); [exact ST | exact FR | cbn; lia | exact CEIL | keeplia LO | keeplia LO].
  Qed.

  (* [comment removed for export] *)
  Definition jst1 (A : AS) (m : mem) (md : Model) (v : vep) : Prop :=
       ainv A m md /\ mem_inv rsegs m /\ md_frame md0 md
    /\ stk rsegs m lo (bv_unsigned sp - 32)
    /\ (exists junk, rw_cells rsegs m (bv_unsigned sp - 32) [CB 8 junk; C8 s1; C8 s0; C8 ra])
    /\ henv_ok LayoutP0 VI0 H m /\ img_ok0 m
    /\ vep_obj LayoutP0 A m VEP v tag q /\ vep_base H VEP v
    /\ v Fvsb = S /\ v Finclude_src = 0 /\ v Fattr_vsb = v0 Fattr_vsb
    /\ v Fstate = v0 Fstate /\ v Fesi_found = v0 Fesi_found /\ bool01 (v Flast_mark) /\ v Fver_p = v0 Fver_p
    /\ 0 <= v Fcb_x < NMAX
    /\ vsb_obj LayoutP0 A m S vv0 false
    /\ match va with
       | None => v0 Fattr_vsb = 0
       | Some x => vsb_obj LayoutP0 A m (v0 Fattr_vsb) x false /\ vsb_apart (v0 Fattr_vsb) x [VEP; wa; S; vb_buf vv0]
       end
    /\ ws1_obj LayoutP0 H A m wa VEP
    /\ a_live A DATA = Some N
    /\ (forall p k, a_live A0 p = Some k -> p <> S -> ~ parse_blocks v0 vv0 va vi p -> a_live A p = Some k)
    (* [comment removed for export] *)
    /\ (a_livebytes A = a_livebytes A0 - match vi with None => 0 | Some (x, _) => 40 + vb_size x end /\
        a_nlive A = a_nlive A0 - match vi with None => 0 | Some _ => 2 end)
    /\ cframe LayoutP0 (owned A0) (owned A) (bv_unsigned sp) VEPFIN_STACK (finish_changed H VEP v0 vv0 va vi)
              (vsb_blocks S vv0) m0 m.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="K NBUD LBUD NPB NEDS NEDV DRANGE N0 LD0 SPH LO CEIL SP16 TP HG PW HEC HMC"] Lemma T1 : forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) A m md v,
    jst1 A m md v -> vep_cnt v n ->
    realizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 (Z_to_bv 64 VEP) s1
                                    a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               bvmap_empty (Z_to_bv 64 0x1be1c) (Z_to_bv 32 0) None m (seg_rom rsegs)) md) T.
  Proof.
    intros until v. intros J CNT0. prelims.
    (first [ dand24 J as AINV MI MDF ST [junk FR] HENV IMG VEPO VB EVSB EIS EAV EST EEF BLM EVP CBX VOBJ VAM WS1 LD LIVE0 BUD1 CF | destruct J as (AINV & MI & MDF & ST & [junk FR] & HENV & IMG & VEPO & VB & EVSB & EIS & EAV & EST & EEF & BLM & EVP & CBX
                   & VOBJ & VAM & WS1 & LD & LIVE0 & BUD1 & CF) ]).
    ufs.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH].
    pose proof HENV as [GLOB HOBJ].
    assert (Ebss : h_bss H = 0x41830) by (destruct GLOB as [E _]; rewrite E; reflexivity).
    assert (Evsc : h_vsc H = h_sp H + 2240) by reflexivity.
    pose proof PW as (_ & _ & _ & _ & _ & _ & NN0 & NNM & _ & _ & ROOM0 & APART0 & _). unfold NMAX in NNM. clear ROOM0. pose proof (proj1 (parsed_world_room _ _ _ _ _ _ _ _ _ _ _ _ _ PW)) as [RM1 RM2].
    destruct (APART0 VEP ltac:(left; reflexivity)) as [NESV NEbV]. destruct (APART0 wa ltac:(right; left; reflexivity)) as [NESw NEbw].
    (* [comment removed for export] *)
    (first [ pose proof (VEPO) as dR_67; dand4 dR_67 as VLV VEPC TAG8 PADS | pose proof VEPO as (VLV & VEPC & TAG8 & PADS) ]). cbn [al_segs LayoutP0] in VEPC.
    (first [ pose proof ((as_live_ok A m md VEP _ AINV VLV)) as dR_68; dand7 dR_68 as _ VEP16 VEPlo VEPhi VEPimg VEPmap VEPown | pose proof (as_live_ok A m md VEP _ AINV VLV) as (_ & VEP16 & VEPlo & VEPhi & VEPimg & VEPmap & VEPown) ]).
    assert (VEPbss : VEP + 312 <= 0x10000 \/ 0x63000 <= VEP) by (unfold in_image in VEPimg; cbn [al_image_lo al_image_hi LayoutP0] in VEPimg; keeplia VEPimg).
    clear VEPimg VEPown.
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md S vv0 false AINV VOBJ)) as dR_69; dand11 dR_69 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LayoutP0 A m md S vv0 false AINV VOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    unfold off_image in Simg, Bimg. cbn [al_image_lo al_image_hi LayoutP0] in Simg, Bimg.
    (first [ pose proof (VOBJ) as dR_70; dand6 dR_70 as _ VINV VLS VLB VNE _ | pose proof VOBJ as (_ & VINV & VLS & VLB & VNE & _) ]).
    pose proof VINV as VINVx. (first [ dand9 VINVx as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm Vsm | destruct VINVx as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm & Vsm) ]).
    pose proof (as_live_disjoint A m md S 40 VEP 312 AINV VLS VLV NESV) as DJS.
    pose proof (as_live_disjoint A m md (vb_buf vv0) (vb_size vv0) VEP 312 AINV VLB VLV NEbV) as DJB.
    pose proof WS1 as WS1x. (first [ dex2 WS1x as id pad; dand7 WS1x as IDOK PADL _ _ LWA _ _ | dand9 WS1x as id pad IDOK PADL _ _ LWA _ _ | destruct WS1x as (id & pad & IDOK & PADL & _ & _ & LWA & _ & _) ]).
    assert (NEwS : wa <> S) by (intros X; apply NESw; symmetry; exact X).
    assert (NEwB : wa <> vb_buf vv0) by (intros X; apply NEbw; symmetry; exact X).
    (* [comment removed for export] *)
    assert (JST : forall A' m' md' v' junk', ainv A' m' md' -> mem_inv rsegs m' -> md_frame md0 md' ->
              stk rsegs m' lo (bv_unsigned sp - 32) -> rw_cells rsegs m' (bv_unsigned sp - 32) [CB 8 junk'; C8 s1; C8 s0; C8 ra] ->
              henv_ok LayoutP0 VI0 H m' -> img_ok0 m' -> vep_obj LayoutP0 A' m' VEP v' tag q ->
              (forall f, f <> Fattr_vsb -> v' f = v f) -> v' Fattr_vsb = 0 ->
              vsb_obj LayoutP0 A' m' S vv0 false -> ws1_obj LayoutP0 H A' m' wa VEP -> a_live A' DATA = Some N ->
              (a_livebytes A' = a_livebytes A0 - world_bytes vv0 va vi + 40 + vb_size vv0 /\ a_nlive A' + world_nlive va vi = a_nlive A0) ->
              (forall p k, a_live A0 p = Some k -> p <> S -> ~ parse_blocks v0 vv0 va vi p -> a_live A' p = Some k) ->
              cframe LayoutP0 (owned A0) (owned A') (bv_unsigned sp) 8512 (finish_changed H VEP v0 vv0 va vi) (vsb_blocks S vv0) m0 m' ->
              jst A' m' md' v' vv0 false (7 * N)).
    { intros A' m' md' v' junk' X1 X2 X3 X4 X5 X6 X7 X8 VK X10 X11 X12 X13 XB X14 X15.
      split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exists junk'; exact X5|].
      split; [exact X6|]. split; [exact X7|]. split; [exact X8|].
      split; [unfold vep_base; rewrite !VK by discriminate; exact VB|].
      split; [rewrite VK by discriminate; exact EVSB|]. split; [rewrite VK by discriminate; exact EIS|]. split; [exact X10|].
      split; [rewrite VK by discriminate; exact EST|]. split; [rewrite VK by discriminate; exact EEF|].
      split; [rewrite VK by discriminate; exact BLM|]. split; [rewrite VK by discriminate; exact EVP|].
      split; [rewrite VK by discriminate; exact CBX|].
      split; [exact X11|]. split; [exact RM1|]. split; [keeplia RM2 Vlen|]. split; [exact NEbV|]. split; [exact NEbw|].
      split; [exact X12|]. split; [exact X13|]. split; [exact X14|]. split; [left; left; reflexivity|]. split; [exact XB|]. exact X15. }
    (* [comment removed for export] *)
    (first [ pose proof (VB) as dR_73; dand5 dR_73 as EVC EVCB EVCBP EVDZ EVURL | pose proof VB as (EVC & EVCB & EVCBP & EVDZ & EVURL) ]).
    unfold vep_cells in VEPC. rewrite EVSB, EAV in VEPC.
    pose proof VOBJ as VOBJx. vsb_open VOBJx. (first [ dex1 VBUF as bs; dand3 VBUF as U8 LBS _ | dand4 VBUF as bs U8 LBS _ | destruct VBUF as (bs & U8 & LBS & _) ]). cbn [al_segs LayoutP0] in U8.
    hide DSB. hide Simg. hide Bimg. hide VEPbss. hide LAY. hide Verr. hide DJS. hide DJB. hide_neqs.
    apply rz_go; [exact MDH | exact MDL |].
    remember va as vax eqn:EVA in VAM. destruct vax as [x|].
    2:{ (* [comment removed for export] *)
        rewrite VAM in VEPC.
        zstep. zstep. if_cases KZ; zify_cond KZ. 2:{ kill KZ. } clear KZ.
        apply rz_stop.
        lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
          assert (VEPCf : rw_cells rsegs mx VEP (vep_cells v tag q)) by (unfold vep_cells; rewrite EVSB, EAV, VAM; exact VEPC) end.
        eapply T2; [| exact CNT0].
        eapply (JST A m md v junk); [exact AINV| exact MI| exact MDF| exact ST| exact FR| exact HENV| exact IMG
          | split; [exact VLV|]; split; [cbn [al_segs LayoutP0]; exact VEPCf|]; split; [exact TAG8| exact PADS]
          | intros f _; reflexivity | rewrite EAV; exact VAM | exact VOBJ| exact WS1| exact LD
          | rewrite <- EVA; unfold world_bytes, world_nlive; revert BUD1; clear; destruct vi as [[xi fi]|]; intros; lia
          | exact LIVE0| exact CF]. }
    (* [comment removed for export] *)
    destruct VAM as [XOBJ XAP].
    destruct (XAP VEP ltac:(left; reflexivity)) as [NXV NXbV]. destruct (XAP wa ltac:(right; left; reflexivity)) as [NXw NXbw].
    destruct (XAP S ltac:(right; right; left; reflexivity)) as [NXS NXbS]. destruct (XAP (vb_buf vv0) ltac:(right; right; right; left; reflexivity)) as [NXB NXbB].
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md (v0 Fattr_vsb) x false AINV XOBJ)) as dR_75; dand11 dR_75 as X16 Xlo Xhi Ximg XB16 XBlo XBhi XBimg XDSB Xmap XBmap | pose proof (vsb_obj_geom LayoutP0 A m md (v0 Fattr_vsb) x false AINV XOBJ) as (X16 & Xlo & Xhi & Ximg & XB16 & XBlo & XBhi & XBimg & XDSB & Xmap & XBmap) ]).
    unfold off_image in Ximg, XBimg. cbn [al_image_lo al_image_hi LayoutP0] in Ximg, XBimg.
    (first [ pose proof (XOBJ) as dR_76; dand6 dR_76 as _ _ XLS XLB XNE _ | pose proof XOBJ as (_ & _ & XLS & XLB & XNE & _) ]).
    pose proof (as_live_disjoint A m md (v0 Fattr_vsb) 40 VEP 312 AINV XLS VLV NXV) as DX1.
    pose proof (as_live_disjoint A m md (vb_buf x) (vb_size x) VEP 312 AINV XLB VLV NXbV) as DX2.
    pose proof (as_live_disjoint A m md (v0 Fattr_vsb) 40 S 40 AINV XLS VLS NXS) as DX3.
    pose proof (as_live_disjoint A m md (vb_buf x) (vb_size x) S 40 AINV XLB VLS NXbS) as DX4.
    pose proof (as_live_disjoint A m md (v0 Fattr_vsb) 40 (vb_buf vv0) (vb_size vv0) AINV XLS VLB NXB) as DX5.
    pose proof (as_live_disjoint A m md (vb_buf x) (vb_size x) (vb_buf vv0) (vb_size vv0) AINV XLB VLB NXbB) as DX6.
    pose proof (as_live_disjoint A m md (v0 Fattr_vsb) 40 wa 40 AINV XLS LWA NXw) as DX7.
    pose proof (as_live_disjoint A m md (vb_buf x) (vb_size x) wa 40 AINV XLB LWA NXbw) as DX8.
    (first [ pose proof ((as_live_ok A m md wa _ AINV LWA)) as dR_77; dand7 dR_77 as _ _ WAlo WAhi _ _ _ | pose proof (as_live_ok A m md wa _ AINV LWA) as (_ & _ & WAlo & WAhi & _ & _ & _) ]).
    pose proof (as_live_disjoint A m md wa 40 VEP 312 AINV LWA VLV ltac:(intros X; rewrite X in LWA; rewrite VLV in LWA; discriminate LWA)) as DX9.
    hide DX1. hide DX2. hide DX3. hide DX4. hide DX5. hide DX6. hide DX7. hide DX8. hide DX9. hide XDSB. hide Ximg. hide XBimg. hide_neqs.
    (* [comment removed for export] *)
    (first [ pose proof ((rw_cells_split3 rsegs m VEP _ 36 (C8 (Z_to_bv 64 (v0 Fattr_vsb))) VEPC eq_refl)) as dR_78; dand3 dR_78 as VA VM VBk | pose proof (rw_cells_split3 rsegs m VEP _ 36 (C8 (Z_to_bv 64 (v0 Fattr_vsb))) VEPC eq_refl) as (VA & VM & VBk) ]). clear VEPC.
    cbn [firstn skipn cells_size csize Nat.add length] in VA, VM, VBk.
    change (Z.of_nat 224) with 224 in VM. change (Z.of_nat 224) with 224 in VBk. change (Z.of_nat 8) with 8 in VBk.
    replace (VEP + 224 + 8) with (VEP + 232) in VBk by lia.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KZ; zify_cond KZ. { unhide_neqs. kill KZ. } clear KZ.
    zstep. zstep.
    apply rz_stop.
    pose proof (crange_block (L:=LayoutP0) A m md VEP 312 VEP 224 AINV VLV ltac:(lia) ltac:(lia) ltac:(lia)) as CRA.
    pose proof (crange_block (L:=LayoutP0) A m md VEP 312 (VEP + 232) 80 AINV VLV ltac:(lia) ltac:(lia) ltac:(lia)) as CRB.
    pose_cranges LayoutP0 A m AINV.
    unhide NXV. unhide NXbV.
    eapply (VSB_destroy_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m md A (VEP + 224) (v0 Fattr_vsb) x false lo);
      [ exact AINV | exact MI | reflexivity | exact VM
      | right; exists VEP, 312; split; [exact VLV|]; split; [cbn; intros [X|[X|X]]; [exact (NXV X)| exact (NXbV X)| exact X] | lia]
      | exact XOBJ | exact TP
      | rewrite unsigned_lit by lia; replace (bv_unsigned sp - 32) with (bv_unsigned sp + -32) by lia; apply align16_add; [exact SP16|reflexivity]
      | rewrite unsigned_lit by lia; reflexivity
      | rewrite unsigned_lit by lia; exact ST | exact CEIL
      | rewrite unsigned_lit by lia; ufs; keeplia LO
      | rewrite unsigned_lit by lia; keeplia GHI SPH | ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 m1 md1 AINV1 MI1 MDF1 ST1 PSC DEADS DEADB LIVEq LBd NLd FRK.
    pose proof (as_lazy_nil A1 m1 md1 AINV1) as [MDL1 MDH1].
    rewrite unsigned_lit in ST1, FRK by lia. ufs.
    replace (ret_pc (Z_to_bv 64 0x1be2c)) with (Z_to_bv 64 0x1be2c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unhide_neqs.
    assert (LVEP1 : a_live A1 VEP = Some 312) by (rewrite (LIVEq VEP (not_eq_sym NXV) (not_eq_sym NXbV)); exact VLV).
    assert (LWA1 : a_live A1 wa = Some 40) by (rewrite (LIVEq wa (not_eq_sym NXw) (not_eq_sym NXbw)); exact LWA).
    assert (LS1 : a_live A1 S = Some 40) by (rewrite (LIVEq S (not_eq_sym NXS) (not_eq_sym NXbS)); exact VLS).
    assert (LB1 : a_live A1 (vb_buf vv0) = Some (vb_size vv0)) by (rewrite (LIVEq (vb_buf vv0) (not_eq_sym NXB) (not_eq_sym NXbB)); exact VLB).
    assert (NXD : v0 Fattr_vsb <> DATA) by (intros X; apply NPB; rewrite <- EVA; right; left; left; symmetry; exact X).
    assert (NXbD : vb_buf x <> DATA) by (intros X; apply NPB; rewrite <- EVA; right; left; right; symmetry; exact X).
    assert (LD1 : a_live A1 DATA = Some N) by (rewrite (LIVEq DATA (not_eq_sym NXD) (not_eq_sym NXbD)); exact LD).
    (* [comment removed for export] *)
    assert (HOBJ1 : hobj_ok LayoutP0 VI0 H m1).
    { eapply (hobj_ok_ccall LayoutP0 VI0 H A A1 m md m1); [exact AINV| exact FRK| exact HG| exact HOBJ| keeplia SPH|].
      intros a Ha X. unfold h_vc, h_wrk, h_req, h_resp, h_hd, blk in *. keeplia Ha X Xhi XBhi VEPhi GCE SPH ACV. }
    assert (GLOB1 : glob_ok LayoutP0 VI0 H m1).
    { eapply (glob_ok_ccall LayoutP0 VI0 H A A1 m md m1); [exact AINV| exact FRK| exact HG| exact GLOB| keeplia SPH| keeplia SPH GCE ACV
        | rewrite Ebss; cbn; keeplia ACV| rewrite Ebss; cbn; keeplia ACV
        | intros i Hi; rewrite Ebss; cbn; unfold p0_static; keeplia Hi
        | rewrite Ebss; cbn; change (al_errno LayoutP0) with 0x420b4; keeplia ACV
        | intros a Ha X; rewrite Ebss in Ha; unfold h_cp, h_vsc, blk in *; keeplia Ha X Xhi XBhi VEPhi GCE SPH ACV Ximg XBimg VEPbss]. }
    assert (IMG1 : img_ok0 m1).
    { eapply (img_ok0_ccall A A1 m md m1); [exact AINV| exact FRK| unfold IMG0_HI; keeplia GCE SPH ACV| | exact IMG].
      intros a Ha X. unfold IMG0_LO, IMG0_HI, blk in *. keeplia Ha X Ximg XBimg VEPbss. }
    assert (WS1_1 : ws1_obj LayoutP0 H A1 m1 wa VEP).
    { eapply (ws1_obj_ccall LayoutP0 H A A1 m md m1); [exact AINV| exact FRK| exact HG| exact WS1| keeplia SPH| keeplia SPH GCE ACV| exact LWA1| exact LVEP1|].
      intros a Ha X. unfold h_ws, h_wsbuf, blk in *. keeplia Ha X Xhi XBhi VEPhi GCE SPH ACV DX7 DX8 DX9 WAhi. }
    (* [comment removed for export] *)
    clear HOBJ GLOB IMG WS1 ST XOBJ.
    apply (rw_cells_ccall LayoutP0 A A1 _ _ _ _ m m1 FRK S) in VSBC;
      [| exact (crange_block (L:=LayoutP0) A m md S 40 S 40 AINV VLS ltac:(lia) ltac:(lia) ltac:(lia))
       | cbn [cells_size csize Nat.add length]; split; [keeplia Shi GCE SPH ACV| intros i Hi X; unfold blk in X; keeplia Hi X DX3 DX4 DJS] ].
    apply (u8arr_ccall LayoutP0 A A1 _ _ _ _ m m1 FRK (vb_buf vv0) bs) in U8;
      [| exact (crange_block (L:=LayoutP0) A m md (vb_buf vv0) (vb_size vv0) (vb_buf vv0) (Z.of_nat (length bs)) AINV VLB ltac:(lia) ltac:(keeplia LBS) ltac:(lia))
       | split; [keeplia Bhi GCE SPH ACV LBS| intros i Hi X; unfold blk in X; keeplia Hi X DX5 DX6 DJB LBS] ].
    hide VSBC. hide U8.
    hide_neqs. unhide DX1. unhide DX2.
    try clear VM. acall_xfer FRK.
    hide DX1. hide DX2. unhide_neqs. unhide VSBC. unhide U8. clear CRA CRB.
    assert (VOBJ1 : vsb_obj LayoutP0 A1 m1 S vv0 false).
    { split; [exact VSBC|]. split; [exact VINV|]. split; [exact LS1|]. split; [exact LB1|]. split; [exact VNE0|].
      exists bs. split; [exact U8|]. split; [exact LBS| intros X; discriminate X]. }
    (* [comment removed for export] *)
    assert (VEPC1 : rw_cells rsegs m1 VEP (vep_cells (fupd v Fattr_vsb 0) tag q)).
    { rewrite <- vep_cells_attr_vsb. unfold vep_cells. rewrite ?EVSB, ?EAV. cbn [firstn skipn].
      lazymatch type of VA with rw_cells _ _ _ ?pre => apply (rw_cells_join3 rsegs m1 VEP pre); [exact VA| exact PSC|] end.
      eapply rwc_eq; [exact VBk| cbn [cells_size csize Nat.add length]; change (Z.of_nat 224) with 224; change (Z.of_nat 8) with 8; lia]. }
    clear VA VBk PSC.
    eapply (T2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A1 m1 md1 (fupd v Fattr_vsb 0) vv0);
      [| unfold vep_cnt; rewrite !fupd_other by discriminate; exact CNT0].
    eapply (JST A1 m1 md1 (fupd v Fattr_vsb 0) junk); [exact AINV1| exact MI1| eapply md_frame_trans; [exact MDF| exact MDF1]| exact ST1| exact FR
      | split; [exact GLOB1| exact HOBJ1]| exact IMG1
      | split; [exact LVEP1|]; split; [cbn [al_segs LayoutP0]; exact VEPC1|]; split; [exact TAG8| exact PADS]
      | intros f Hf; apply fupd_other; exact Hf | apply fupd_same | exact VOBJ1| exact WS1_1| exact LD1
      | rewrite <- EVA; unfold world_bytes, world_nlive; revert BUD1 LBd NLd; clear; destruct vi as [[xi fi]|]; intros; lia
      | | ].
    - intros p k L0 NS NP. rewrite (LIVEq p); [exact (LIVE0 p k L0 NS NP)| |];
        intros ->; apply NP; rewrite <- EVA; right; left; [left|right]; reflexivity.
    - assert (CF2 : cframe LayoutP0 (owned A) (owned A1) (bv_unsigned sp) 8512
                      (fun a => blk (v0 Fattr_vsb) 40 a \/ blk (vb_buf x) (vb_size x) a \/ VEP + 224 <= a < VEP + 224 + 8) nowhere m m1).
      { eapply (cframe_extend LayoutP0 _ _ _ _ _ _ _ _ _ _ m m m1 m1 [] []);
          [ apply munch_refl | intros a _ X; exfalso; apply X; exact I | exact FRK | keeplia ACV | keeplia ACV
          | intros a X; exact X | intros a X; destruct X | apply munch_refl | intros a _ X; exfalso; apply X; exact I
          | eapply (window_mapped LayoutP0 _ lo); [exact ST1 | exact FR | cbn; lia | exact CEIL | keeplia LO | keeplia LO] ]. }
      eapply (cframe_seq LayoutP0 _ _ _ _ _ _ _ _ _ _ _ _ _ m0 m m1 CF CF2);
        [ keeplia ACV | keeplia ACV
        | eapply (window_mapped LayoutP0 _ lo); [exact ST1 | exact FR | cbn; lia | exact CEIL | keeplia LO | keeplia LO]
        | intros a X; exact X | | intros a X; left; exact X ].
      (* [comment removed for export] *)
      intros a [X|[X|X]].
      + right. right. right. left. rewrite <- EVA. left. exact X.
      + right. right. right. left. rewrite <- EVA. right. exact X.
      + right. left. unfold blk. split; [keeplia VEPlo| keeplia X].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="K NBUD LBUD NPB NEDS NEDV DRANGE N0 LD0 SPH LO CEIL SP16 TP HG PW S vi va vv0 q tag v0 DATA N n HEC HMC"] Lemma T0 : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ainv A0 m0 md0 -> mem_inv rsegs m0 -> a0 = Z_to_bv 64 VEP ->
    ws1_obj LayoutP0 H A0 m0 wa VEP -> henv_ok LayoutP0 VI0 H m0 -> img_ok0 m0 -> stk rsegs m0 lo (bv_unsigned sp) ->
    realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               bvmap_empty (Z_to_bv 64 VEP_Finish_entry) (Z_to_bv 32 0) None m0 (seg_rom rsegs)) md0) T.
  Proof.
    intros until t6. intros AINV MI Ha0 WS1 HENV IMG ST. prelims. rewrite Ha0. unfold VEP_Finish_entry. ufs.
    pose proof (as_lazy_nil A0 m0 md0 AINV) as [MDL MDH].
    pose proof HENV as [GLOB HOBJ].
    assert (Ebss : h_bss H = 0x41830) by (destruct GLOB as [E _]; rewrite E; reflexivity).
    assert (Evsc : h_vsc H = h_sp H + 2240) by reflexivity.
    pose proof PW as (VEPO & VB & _ & BLM & _ & CNT0 & NN0 & NNM & VP0 & VOBJ & ROOM0 & APART0 & VAM & VIM). unfold NMAX in NNM.
    (first [ pose proof (CNT0) as dR_79; dand7 dR_79 as C1 C2 C3 C4 C5 C6 C7 | pose proof CNT0 as (C1 & C2 & C3 & C4 & C5 & C6 & C7) ]).
    destruct (APART0 VEP ltac:(left; reflexivity)) as [NESV NEbV]. destruct (APART0 wa ltac:(right; left; reflexivity)) as [NESw NEbw].
    (* [comment removed for export] *)
    (first [ pose proof (VEPO) as dR_80; dand4 dR_80 as VLV VEPC TAG8 PADS | pose proof VEPO as (VLV & VEPC & TAG8 & PADS) ]). cbn [al_segs LayoutP0] in VEPC.
    (first [ pose proof ((as_live_ok A0 m0 md0 VEP _ AINV VLV)) as dR_81; dand7 dR_81 as _ VEP16 VEPlo VEPhi VEPimg VEPmap VEPown | pose proof (as_live_ok A0 m0 md0 VEP _ AINV VLV) as (_ & VEP16 & VEPlo & VEPhi & VEPimg & VEPmap & VEPown) ]).
    assert (VEPbss : VEP + 312 <= 0x10000 \/ 0x63000 <= VEP) by (unfold in_image in VEPimg; cbn [al_image_lo al_image_hi LayoutP0] in VEPimg; keeplia VEPimg).
    clear VEPimg VEPown.
    (first [ pose proof ((vsb_obj_geom LayoutP0 A0 m0 md0 S vv0 false AINV VOBJ)) as dR_82; dand11 dR_82 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LayoutP0 A0 m0 md0 S vv0 false AINV VOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    unfold off_image in Simg, Bimg. cbn [al_image_lo al_image_hi LayoutP0] in Simg, Bimg.
    (first [ pose proof (VOBJ) as dR_83; dand6 dR_83 as _ VINV VLS VLB VNE _ | pose proof VOBJ as (_ & VINV & VLS & VLB & VNE & _) ]).
    pose proof VINV as VINVx. (first [ dand9 VINVx as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm Vsm | destruct VINVx as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm & Vsm) ]).
    pose proof (as_live_disjoint A0 m0 md0 S 40 VEP 312 AINV VLS VLV NESV) as DJS.
    pose proof (as_live_disjoint A0 m0 md0 (vb_buf vv0) (vb_size vv0) VEP 312 AINV VLB VLV NEbV) as DJB.
    pose proof WS1 as WS1x. (first [ dex2 WS1x as id pad; dand7 WS1x as IDOK PADL _ _ LWA _ _ | dand9 WS1x as id pad IDOK PADL _ _ LWA _ _ | destruct WS1x as (id & pad & IDOK & PADL & _ & _ & LWA & _ & _) ]).
    assert (NEwS : wa <> S) by (intros X; apply NESw; symmetry; exact X).
    assert (NEwB : wa <> vb_buf vv0) by (intros X; apply NEbw; symmetry; exact X).
    (first [ pose proof ((as_live_ok A0 m0 md0 wa _ AINV LWA)) as dR_86; dand7 dR_86 as _ _ WAlo WAhi _ _ _ | pose proof (as_live_ok A0 m0 md0 wa _ AINV LWA) as (_ & _ & WAlo & WAhi & _ & _ & _) ]).
    pose proof (as_live_disjoint A0 m0 md0 wa 40 VEP 312 AINV LWA VLV ltac:(intros X; rewrite X in LWA; rewrite VLV in LWA; discriminate LWA)) as DX9.
    (* [comment removed for export] *)
    assert (JST : forall A' m' md' v' junk', ainv A' m' md' -> mem_inv rsegs m' -> md_frame md0 md' ->
              stk rsegs m' lo (bv_unsigned sp - 32) -> rw_cells rsegs m' (bv_unsigned sp - 32) [CB 8 junk'; C8 s1; C8 s0; C8 ra] ->
              henv_ok LayoutP0 VI0 H m' -> img_ok0 m' -> vep_obj LayoutP0 A' m' VEP v' tag q ->
              (forall f, f <> Finclude_src -> v' f = v0 f) -> v' Finclude_src = 0 ->
              vsb_obj LayoutP0 A' m' S vv0 false ->
              match va with None => v0 Fattr_vsb = 0
                          | Some x => vsb_obj LayoutP0 A' m' (v0 Fattr_vsb) x false /\ vsb_apart (v0 Fattr_vsb) x [VEP; wa; S; vb_buf vv0] end ->
              ws1_obj LayoutP0 H A' m' wa VEP -> a_live A' DATA = Some N ->
              (a_livebytes A' = a_livebytes A0 - match vi with None => 0 | Some (x, _) => 40 + vb_size x end /\
               a_nlive A' = a_nlive A0 - match vi with None => 0 | Some _ => 2 end) ->
              (forall p k, a_live A0 p = Some k -> p <> S -> ~ parse_blocks v0 vv0 va vi p -> a_live A' p = Some k) ->
              cframe LayoutP0 (owned A0) (owned A') (bv_unsigned sp) 8512 (finish_changed H VEP v0 vv0 va vi) (vsb_blocks S vv0) m0 m' ->
              jst1 A' m' md' v').
    { intros A' m' md' v' junk' X1 X2 X3 X4 X5 X6 X7 X8 VK X10 X11 X12 X13 X14 XB X15 X16.
      split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exists junk'; exact X5|].
      split; [exact X6|]. split; [exact X7|]. split; [exact X8|].
      split; [unfold vep_base; rewrite !VK by discriminate; exact VB|].
      split; [rewrite VK by discriminate; reflexivity|]. split; [exact X10|]. split; [rewrite VK by discriminate; reflexivity|].
      split; [rewrite VK by discriminate; reflexivity|]. split; [rewrite VK by discriminate; reflexivity|].
      split; [rewrite VK by discriminate; exact BLM|]. split; [rewrite VK by discriminate; reflexivity|].
      split; [rewrite VK by discriminate; unfold NMAX; keeplia C1 C2 C3 NN0 NNM|].
      split; [exact X11|]. split; [exact X12|]. split; [exact X13|]. split; [exact X14|]. split; [exact X15|]. split; [exact XB|]. exact X16. }
    (* [comment removed for export] *)
    unfold vep_cells in VEPC.
    pose proof VOBJ as VOBJx. vsb_open VOBJx. (first [ dex1 VBUF as bs; dand3 VBUF as U8 LBS _ | dand4 VBUF as bs U8 LBS _ | destruct VBUF as (bs & U8 & LBS & _) ]). cbn [al_segs LayoutP0] in U8.
    pose proof (munch_refl [(bv_unsigned sp - 8512, bv_unsigned sp)] m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
    assert (CFP : client_fp LayoutP0 A0 [(bv_unsigned sp - 8512, bv_unsigned sp)]).
    { cbn. split; [left; keeplia GCE SPH ACV LO GHI| exact I]. }
    hide DSB. hide Simg. hide Bimg. hide VEPbss. hide LAY. hide Verr. hide DJS. hide DJB. hide DX9. hide_neqs.
    apply rz_go; [exact MDH | exact MDL |].
    (* [comment removed for export] *)
    carve_frame 32%nat ST.
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0. { kill K0. } clear K0.
    zstep. zstep. zstep. zstep. zstep. if_cases K0; zify_cond K0. { kill K0. } clear K0.
    (* [comment removed for export] *)
    assert (NOCALL : forall mx junk', mem_inv rsegs mx -> munch [(bv_unsigned sp - 8512, bv_unsigned sp)] m0 mx -> wmono rsegs m0 mx ->
              stk rsegs mx lo (bv_unsigned sp + -32) -> rw_cells rsegs mx (bv_unsigned sp + -32) [CB 8 junk'; C8 s1; C8 s0; C8 ra] ->
              rw_cells rsegs mx VEP (vep_cells v0 tag q) -> v0 Finclude_src = 0 -> vi = None ->
              jst1 A0 mx md0 v0).
    { intros mx junk' MIx MUx WMx STx FRx VEPCx EIS0 EVIN.
      assert (AINVx : ainv A0 mx md0) by (eapply (ainv_munch LayoutP0 A0 m0 mx md0); [exact AINV| exact MUx| exact WMx| exact CFP]).
      eapply (JST A0 mx md0 v0 junk'); [exact AINVx| exact MIx| apply md_frame_refl; [exact MDL| exact MDH]| exact STx| exact FRx
        | eapply (henv_ok_munch LayoutP0); [exact HENV| exact MUx| exact WMx| intros a Ha; rewrite Ebss in Ha; unfold h_hd, h_wrk, h_req, h_vsc in Ha; cbn [outside]; keeplia Ha GCE SPH ACV]
        | eapply (img_ok0_munch _ m0); [exact MUx| intros a Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; keeplia Ha GCE SPH ACV| exact IMG]
        | split; [exact VLV|]; split; [cbn [al_segs LayoutP0]; exact VEPCx|]; split; [exact TAG8| exact PADS]
        | intros f _; reflexivity | exact EIS0
        | eapply (vsb_obj_munch LayoutP0); [exact VOBJ| exact MUx| exact WMx| cbn [disjoint_from]; split; [keeplia Shi GCE SPH ACV| exact I]| cbn [disjoint_from]; split; [keeplia Bhi GCE SPH ACV| exact I]]
        | | eapply (ws1_obj_munch LayoutP0); [exact WS1| exact MUx| exact WMx| intros a Ha; unfold h_ws, h_wsbuf in Ha; cbn [outside]; keeplia Ha WAhi GCE SPH ACV]
        | exact LD0 | rewrite EVIN; split; lia | intros p k L0 _ _; exact L0 | ].
      - destruct va as [x|]; [|exact VAM]. (first [ dand4 VAM as XO _ _ XA | destruct VAM as (XO & _ & _ & XA) ]). split; [|exact XA].
        (first [ pose proof ((vsb_obj_geom LayoutP0 A0 m0 md0 (v0 Fattr_vsb) x false AINV XO)) as dR_89; dand8 dR_89 as _ _ Xhi _ _ _ XBhi _ | pose proof (vsb_obj_geom LayoutP0 A0 m0 md0 (v0 Fattr_vsb) x false AINV XO) as (_ & _ & Xhi & _ & _ & _ & XBhi & _) ]).
        eapply (vsb_obj_munch LayoutP0); [exact XO| exact MUx| exact WMx| cbn [disjoint_from]; split; [keeplia Xhi GCE SPH ACV| exact I]| cbn [disjoint_from]; split; [keeplia XBhi GCE SPH ACV| exact I]].
      - eapply cframe_newV; [eapply (cframe_stores LayoutP0 _ _ _ _ m0 mx); [exact MUx| intros a Ha NO; cbn [outside] in NO; left; keeplia Ha NO|]|].
        + eapply (window_mapped LayoutP0 _ lo); [exact STx | exact FRx | cbn; lia | exact CEIL | keeplia LO | keeplia LO].
        + intros a [X|X]; right; right; left; [left; exact X| right; exact X]. }
    remember vi as vix eqn:EVI in VIM. destruct vix as [[x fi]|].
    2:{ (* [comment removed for export] *)
        rewrite VIM in VEPC.
        zstep. zstep. if_cases KZ; zify_cond KZ. 2:{ kill KZ. } clear KZ.
        apply rz_stop.
        lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
          assert (VEPCf : rw_cells rsegs mx VEP (vep_cells v0 tag q)) by (unfold vep_cells; rewrite VIM; exact VEPC) end.
        eapply T1; [| exact CNT0].
        eapply NOCALL; [assumption| exact MU| exact WM| exact ST| exact FR| exact VEPCf| exact VIM| symmetry; exact EVI]. }
    (* [comment removed for export] *)
    (first [ dand4 VIM as XOBJ _ XAP XVA | destruct VIM as (XOBJ & _ & XAP & XVA) ]).
    destruct (XAP VEP ltac:(left; reflexivity)) as [NXV NXbV]. destruct (XAP wa ltac:(right; left; reflexivity)) as [NXw NXbw].
    destruct (XAP S ltac:(right; right; left; reflexivity)) as [NXS NXbS]. destruct (XAP (vb_buf vv0) ltac:(right; right; right; left; reflexivity)) as [NXB NXbB].
    (first [ pose proof ((vsb_obj_geom LayoutP0 A0 m0 md0 (v0 Finclude_src) x fi AINV XOBJ)) as dR_91; dand11 dR_91 as X16 Xlo Xhi Ximg XB16 XBlo XBhi XBimg XDSB Xmap XBmap | pose proof (vsb_obj_geom LayoutP0 A0 m0 md0 (v0 Finclude_src) x fi AINV XOBJ) as (X16 & Xlo & Xhi & Ximg & XB16 & XBlo & XBhi & XBimg & XDSB & Xmap & XBmap) ]).
    unfold off_image in Ximg, XBimg. cbn [al_image_lo al_image_hi LayoutP0] in Ximg, XBimg.
    (first [ pose proof (XOBJ) as dR_92; dand6 dR_92 as _ _ XLS XLB XNE _ | pose proof XOBJ as (_ & _ & XLS & XLB & XNE & _) ]).
    pose proof (as_live_disjoint A0 m0 md0 (v0 Finclude_src) 40 VEP 312 AINV XLS VLV NXV) as DX1.
    pose proof (as_live_disjoint A0 m0 md0 (vb_buf x) (vb_size x) VEP 312 AINV XLB VLV NXbV) as DX2.
    pose proof (as_live_disjoint A0 m0 md0 (v0 Finclude_src) 40 S 40 AINV XLS VLS NXS) as DX3.
    pose proof (as_live_disjoint A0 m0 md0 (vb_buf x) (vb_size x) S 40 AINV XLB VLS NXbS) as DX4.
    pose proof (as_live_disjoint A0 m0 md0 (v0 Finclude_src) 40 (vb_buf vv0) (vb_size vv0) AINV XLS VLB NXB) as DX5.
    pose proof (as_live_disjoint A0 m0 md0 (vb_buf x) (vb_size x) (vb_buf vv0) (vb_size vv0) AINV XLB VLB NXbB) as DX6.
    pose proof (as_live_disjoint A0 m0 md0 (v0 Finclude_src) 40 wa 40 AINV XLS LWA NXw) as DX7.
    pose proof (as_live_disjoint A0 m0 md0 (vb_buf x) (vb_size x) wa 40 AINV XLB LWA NXbw) as DX8.
    hide DX1. hide DX2. hide DX3. hide DX4. hide DX5. hide DX6. hide DX7. hide DX8. hide XDSB. hide Ximg. hide XBimg. hide_neqs.
    (* [comment removed for export] *)
    assert (VAX : match va with None => True | Some y => vsb_apart (v0 Finclude_src) x [v0 Fattr_vsb; vb_buf y] /\
              exists bsy, rw_cells rsegs m0 (v0 Fattr_vsb) (vsb_cells y) /\ u8arr rsegs m0 (vb_buf y) bsy /\ Z.of_nat (length bsy) = vb_size y /\
                          a_live A0 (v0 Fattr_vsb) = Some 40 /\ a_live A0 (vb_buf y) = Some (vb_size y) end).
    { destruct va as [y|]; [|exact I]. split; [exact XVA|]. (first [ dand4 VAM as (YC & _ & YLS & YLB & _ & (bsy & YU & YL & _)) _ _ _ | destruct VAM as ((YC & _ & YLS & YLB & _ & (bsy & YU & YL & _)) & _ & _ & _) ]).
      exists bsy. cbn [al_segs LayoutP0] in YC, YU. split; [exact YC|]. split; [exact YU|]. split; [exact YL|]. split; [exact YLS| exact YLB]. }
    (* [comment removed for export] *)
    (first [ pose proof ((rw_cells_split3 rsegs _ VEP _ 45 (C8 (Z_to_bv 64 (v0 Finclude_src))) VEPC eq_refl)) as dR_94; dand3 dR_94 as VA VM VBk | pose proof (rw_cells_split3 rsegs _ VEP _ 45 (C8 (Z_to_bv 64 (v0 Finclude_src))) VEPC eq_refl) as (VA & VM & VBk) ]). clear VEPC.
    cbn [firstn skipn cells_size csize Nat.add length] in VA, VM, VBk.
    change (Z.of_nat 280) with 280 in VM. change (Z.of_nat 280) with 280 in VBk. change (Z.of_nat 8) with 8 in VBk.
    replace (VEP + 280 + 8) with (VEP + 288) in VBk by lia.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KZ; zify_cond KZ. { unhide_neqs. kill KZ. } clear KZ.
    zstep. zstep.
    apply rz_stop.
    lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into mA end.
    pose proof (ainv_munch LayoutP0 A0 m0 mA md0 _ AINV MU WM CFP) as AINV2.
    pose proof (crange_block (L:=LayoutP0) A0 mA md0 VEP 312 VEP 280 AINV2 VLV ltac:(lia) ltac:(lia) ltac:(lia)) as CRA.
    pose proof (crange_block (L:=LayoutP0) A0 mA md0 VEP 312 (VEP + 288) 24 AINV2 VLV ltac:(lia) ltac:(lia) ltac:(lia)) as CRB.
    pose proof (crange_stack (L:=LayoutP0) A0 mA md0 (bv_unsigned sp + -32) 32 AINV2 ltac:(keeplia GCE SPH ACV) ltac:(keeplia GHI SPH)
                  (rw_cells_mapped LayoutP0 mA _ _ FR ltac:(off_image_solve LayoutP0))) as CRF.
    assert (XOBJ2 : vsb_obj LayoutP0 A0 mA (v0 Finclude_src) x fi).
    { eapply (vsb_obj_munch LayoutP0); [exact XOBJ| exact MU| exact WM
        | cbn [disjoint_from]; split; [keeplia Xhi GCE SPH ACV| exact I]| cbn [disjoint_from]; split; [keeplia XBhi GCE SPH ACV| exact I]]. }
    assert (CFa : cframe LayoutP0 (owned A0) (owned A0) (bv_unsigned sp) 8512 (finish_changed H VEP v0 vv0 va vi) (vsb_blocks S vv0) m0 mA).
    { eapply cframe_newV; [eapply (cframe_stores LayoutP0 _ _ _ _ m0 mA); [exact MU| intros a Ha NO; cbn [outside] in NO; left; keeplia Ha NO|]|];
        [ eapply (window_mapped LayoutP0 _ lo); [exact ST | exact FR | cbn; lia | exact CEIL | keeplia LO | keeplia LO]
        | intros a [X|X]; right; right; left; [left; exact X| right; exact X] ]. }
    unhide NXV. unhide NXbV.
    eapply (VSB_destroy_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mA md0 A0 (VEP + 280) (v0 Finclude_src) x fi lo);
      [ exact AINV2 | assumption | reflexivity | exact VM
      | right; exists VEP, 312; split; [exact VLV|]; split; [cbn; intros [X|[X|X]]; [exact (NXV X)| exact (NXbV X)| exact X] | lia]
      | exact XOBJ2 | exact TP
      | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
      | rewrite unsigned_lit by lia; reflexivity
      | rewrite unsigned_lit by lia; exact ST | exact CEIL
      | rewrite unsigned_lit by lia; ufs; keeplia LO
      | rewrite unsigned_lit by lia; keeplia GHI SPH | ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 m1 md1 AINV1 MI1 MDF1 ST1 PSC DEADS DEADB LIVEq LBd NLd FRK.
    pose proof (as_lazy_nil A1 m1 md1 AINV1) as [MDL1 MDH1].
    rewrite unsigned_lit in ST1, FRK by lia. ufs.
    replace (ret_pc (Z_to_bv 64 0x1be1c)) with (Z_to_bv 64 0x1be1c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unhide_neqs.
    assert (LVEP1 : a_live A1 VEP = Some 312) by (rewrite (LIVEq VEP (not_eq_sym NXV) (not_eq_sym NXbV)); exact VLV).
    assert (LWA1 : a_live A1 wa = Some 40) by (rewrite (LIVEq wa (not_eq_sym NXw) (not_eq_sym NXbw)); exact LWA).
    assert (LS1 : a_live A1 S = Some 40) by (rewrite (LIVEq S (not_eq_sym NXS) (not_eq_sym NXbS)); exact VLS).
    assert (LB1 : a_live A1 (vb_buf vv0) = Some (vb_size vv0)) by (rewrite (LIVEq (vb_buf vv0) (not_eq_sym NXB) (not_eq_sym NXbB)); exact VLB).
    assert (NXD : v0 Finclude_src <> DATA) by (intros X; apply NPB; rewrite <- EVI; right; right; left; symmetry; exact X).
    assert (NXbD : vb_buf x <> DATA) by (intros X; apply NPB; rewrite <- EVI; right; right; right; symmetry; exact X).
    assert (LD1 : a_live A1 DATA = Some N) by (rewrite (LIVEq DATA (not_eq_sym NXD) (not_eq_sym NXbD)); exact LD0).
    (* [comment removed for export] *)
    assert (HOBJ1 : hobj_ok LayoutP0 VI0 H m1).
    { eapply (hobj_ok_ccall LayoutP0 VI0 H A0 A1 mA md0 m1); [exact AINV2| exact FRK| exact HG
        | eapply (hobj_ok_munch LayoutP0); [exact HOBJ| exact MU| exact WM| intros a Ha; unfold h_vc, h_wrk, h_req, h_resp, h_hd in Ha; cbn [outside]; keeplia Ha GCE SPH ACV]
        | keeplia SPH|].
      intros a Ha X. unfold h_vc, h_wrk, h_req, h_resp, h_hd, blk in *. keeplia Ha X Xhi XBhi VEPhi GCE SPH ACV. }
    assert (GLOB1 : glob_ok LayoutP0 VI0 H m1).
    { eapply (glob_ok_ccall LayoutP0 VI0 H A0 A1 mA md0 m1); [exact AINV2| exact FRK| exact HG
        | eapply (glob_ok_munch LayoutP0); [exact GLOB| exact MU| exact WM| intros a Ha; rewrite Ebss in Ha; unfold h_cp, h_vsc in Ha; cbn [outside]; keeplia Ha GCE SPH ACV]
        | keeplia SPH| keeplia SPH GCE ACV
        | rewrite Ebss; cbn; keeplia ACV| rewrite Ebss; cbn; keeplia ACV
        | intros i Hi; rewrite Ebss; cbn; unfold p0_static; keeplia Hi
        | rewrite Ebss; cbn; change (al_errno LayoutP0) with 0x420b4; keeplia ACV
        | intros a Ha X; rewrite Ebss in Ha; unfold h_cp, h_vsc, blk in *; keeplia Ha X Xhi XBhi VEPhi GCE SPH ACV Ximg XBimg VEPbss]. }
    assert (IMG1 : img_ok0 m1).
    { eapply (img_ok0_ccall A0 A1 mA md0 m1); [exact AINV2| exact FRK| unfold IMG0_HI; keeplia GCE SPH ACV| |
        eapply (img_ok0_munch _ m0); [exact MU| intros a Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; keeplia Ha GCE SPH ACV| exact IMG]].
      intros a Ha X. unfold IMG0_LO, IMG0_HI, blk in *. keeplia Ha X Ximg XBimg VEPbss. }
    assert (WS1_1 : ws1_obj LayoutP0 H A1 m1 wa VEP).
    { eapply (ws1_obj_ccall LayoutP0 H A0 A1 mA md0 m1); [exact AINV2| exact FRK| exact HG
        | eapply (ws1_obj_munch LayoutP0); [exact WS1| exact MU| exact WM| intros a Ha; unfold h_ws, h_wsbuf in Ha; cbn [outside]; keeplia Ha WAhi GCE SPH ACV]
        | keeplia SPH| keeplia SPH GCE ACV| exact LWA1| exact LVEP1|].
      intros a Ha X. unfold h_ws, h_wsbuf, blk in *. keeplia Ha X Xhi XBhi VEPhi GCE SPH ACV DX7 DX8 DX9 WAhi. }
    (* [comment removed for export] *)
    apply (rw_cells_ccall LayoutP0 A0 A1 _ _ _ _ mA m1 FRK S) in VSBC;
      [| exact (crange_block (L:=LayoutP0) A0 mA md0 S 40 S 40 AINV2 VLS ltac:(lia) ltac:(lia) ltac:(lia))
       | cbn [cells_size csize Nat.add length]; split; [keeplia Shi GCE SPH ACV| intros i Hi X; unfold blk in X; keeplia Hi X DX3 DX4 DJS] ].
    apply (u8arr_ccall LayoutP0 A0 A1 _ _ _ _ mA m1 FRK (vb_buf vv0) bs) in U8;
      [| exact (crange_block (L:=LayoutP0) A0 mA md0 (vb_buf vv0) (vb_size vv0) (vb_buf vv0) (Z.of_nat (length bs)) AINV2 VLB ltac:(lia) ltac:(keeplia LBS) ltac:(lia))
       | split; [keeplia Bhi GCE SPH ACV LBS| intros i Hi X; unfold blk in X; keeplia Hi X DX5 DX6 DJB LBS] ].
    (* [comment removed for export] *)
    assert (VAM1 : match va with None => v0 Fattr_vsb = 0
            | Some y => vsb_obj LayoutP0 A1 m1 (v0 Fattr_vsb) y false /\ vsb_apart (v0 Fattr_vsb) y [VEP; wa; S; vb_buf vv0] end).
    { destruct va as [y|]; [|exact VAM].
      (first [ dand7 VAX as YAP bsy YC YU YL YLS YLB | destruct VAX as (YAP & bsy & YC & YU & YL & YLS & YLB) ]). (first [ dand4 VAM as YO _ _ YA | destruct VAM as (YO & _ & _ & YA) ]). split; [|exact YA].
      destruct (YAP (v0 Fattr_vsb) ltac:(left; reflexivity)) as [NY1 NY2].
      destruct (YAP (vb_buf y) ltac:(right; left; reflexivity)) as [NY3 NY4].
      destruct (YA VEP ltac:(left; reflexivity)) as [NY5 NY6].
      (first [ pose proof ((vsb_obj_geom LayoutP0 A0 m0 md0 (v0 Fattr_vsb) y false AINV YO)) as dR_97; dand9 dR_97 as _ _ Yhi _ _ _ YBhi _ _ | pose proof (vsb_obj_geom LayoutP0 A0 m0 md0 (v0 Fattr_vsb) y false AINV YO) as (_ & _ & Yhi & _ & _ & _ & YBhi & _ & _) ]).
      (first [ pose proof (YO) as dR_98; dand6 dR_98 as _ YINV _ _ YNE _ | pose proof YO as (_ & YINV & _ & _ & YNE & _) ]).
      pose proof (as_live_disjoint A0 m0 md0 (v0 Finclude_src) 40 (v0 Fattr_vsb) 40 AINV XLS YLS NY1) as DY1.
      pose proof (as_live_disjoint A0 m0 md0 (vb_buf x) (vb_size x) (v0 Fattr_vsb) 40 AINV XLB YLS NY2) as DY2.
      pose proof (as_live_disjoint A0 m0 md0 (v0 Finclude_src) 40 (vb_buf y) (vb_size y) AINV XLS YLB NY3) as DY3.
      pose proof (as_live_disjoint A0 m0 md0 (vb_buf x) (vb_size x) (vb_buf y) (vb_size y) AINV XLB YLB NY4) as DY4.
      pose proof (as_live_disjoint A0 m0 md0 (v0 Fattr_vsb) 40 VEP 312 AINV YLS VLV NY5) as DY5.
      pose proof (as_live_disjoint A0 m0 md0 (vb_buf y) (vb_size y) VEP 312 AINV YLB VLV NY6) as DY6.
      eapply (rw_cells_transport rsegs _ m0 mA) in YC; [| exact MU| exact WM| cbn [disjoint_from]; rewrite vsb_cells_size; change (Z.of_nat 40) with 40; split; [keeplia Yhi GCE SPH ACV| exact I]].
      eapply (u8arr_transport rsegs _ m0 mA) in YU; [| exact MU| exact WM| cbn [disjoint_from]; split; [keeplia YBhi GCE SPH ACV YL| exact I]].
      apply (rw_cells_ccall LayoutP0 A0 A1 _ _ _ _ mA m1 FRK (v0 Fattr_vsb)) in YC;
        [| rewrite vsb_cells_size; exact (crange_block (L:=LayoutP0) A0 mA md0 (v0 Fattr_vsb) 40 (v0 Fattr_vsb) 40 AINV2 YLS ltac:(lia) ltac:(lia) ltac:(lia))
         | rewrite vsb_cells_size; change (Z.of_nat 40) with 40; split; [keeplia Yhi GCE SPH ACV| intros i Hi X; unfold blk in X; keeplia Hi X DY1 DY2 DY5] ].
      apply (u8arr_ccall LayoutP0 A0 A1 _ _ _ _ mA m1 FRK (vb_buf y) bsy) in YU;
        [| exact (crange_block (L:=LayoutP0) A0 mA md0 (vb_buf y) (vb_size y) (vb_buf y) (Z.of_nat (length bsy)) AINV2 YLB ltac:(lia) ltac:(keeplia YL) ltac:(lia))
         | split; [keeplia YBhi GCE SPH ACV YL| intros i Hi X; unfold blk in X; keeplia Hi X DY3 DY4 DY6 YL] ].
      split; [exact YC|]. split; [exact YINV|].
      split; [rewrite (LIVEq _ (not_eq_sym NY1) (not_eq_sym NY2)); exact YLS|].
      split; [rewrite (LIVEq _ (not_eq_sym NY3) (not_eq_sym NY4)); exact YLB|].
      split; [exact YNE|]. exists bsy. split; [exact YU|]. split; [exact YL| intros X; discriminate X]. }
    hide VSBC. hide U8. clear HOBJ GLOB IMG WS1 ST XOBJ XOBJ2 VAX.
    hide_neqs. unhide DX1. unhide DX2.
    try clear VM. acall_xfer FRK.
    hide DX1. hide DX2. unhide_neqs. unhide VSBC. unhide U8. clear CRA CRB CRF.
    assert (VOBJ1 : vsb_obj LayoutP0 A1 m1 S vv0 false).
    { split; [exact VSBC|]. split; [exact VINV|]. split; [exact LS1|]. split; [exact LB1|]. split; [exact VNE0|].
      exists bs. split; [exact U8|]. split; [exact LBS| intros X; discriminate X]. }
    (* [comment removed for export] *)
    assert (VEPC1 : rw_cells rsegs m1 VEP (vep_cells (fupd v0 Finclude_src 0) tag q)).
    { rewrite <- vep_cells_include_src. unfold vep_cells. cbn [firstn skipn].
      lazymatch type of VA with rw_cells _ _ _ ?pre => apply (rw_cells_join3 rsegs m1 VEP pre); [exact VA| exact PSC|] end.
      eapply rwc_eq; [exact VBk| cbn [cells_size csize Nat.add length]; change (Z.of_nat 280) with 280; change (Z.of_nat 8) with 8; lia]. }
    clear VA VBk PSC.
    eapply (T1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A1 m1 md1 (fupd v0 Finclude_src 0));
      [| unfold vep_cnt; rewrite !fupd_other by discriminate; exact CNT0].
    eapply (JST A1 m1 md1 (fupd v0 Finclude_src 0) _); [exact AINV1| exact MI1| exact MDF1| exact ST1| exact FR
      | split; [exact GLOB1| exact HOBJ1]| exact IMG1
      | split; [exact LVEP1|]; split; [cbn [al_segs LayoutP0]; exact VEPC1|]; split; [exact TAG8| exact PADS]
      | intros f Hf; apply fupd_other; exact Hf | apply fupd_same | exact VOBJ1| exact VAM1| exact WS1_1| exact LD1
      | rewrite <- EVI; revert LBd NLd; clear; intros; lia
      | | ].
    - intros p k L0 NS NP. rewrite (LIVEq p); [exact L0| |];
        intros ->; apply NP; rewrite <- EVI; right; right; [left|right]; reflexivity.
    - assert (CF2 : cframe LayoutP0 (owned A0) (owned A1) (bv_unsigned sp) 8512
                      (fun a => blk (v0 Finclude_src) 40 a \/ blk (vb_buf x) (vb_size x) a \/ VEP + 280 <= a < VEP + 280 + 8) nowhere mA m1).
      { eapply (cframe_extend LayoutP0 _ _ _ _ _ _ _ _ _ _ mA mA m1 m1 [] []);
            [ apply munch_refl | intros a _ X; exfalso; apply X; exact I | exact FRK | keeplia ACV | keeplia ACV
            | intros a X; exact X | intros a X; destruct X | apply munch_refl | intros a _ X; exfalso; apply X; exact I
            | eapply (window_mapped LayoutP0 _ lo); [exact ST1 | exact FR | cbn; lia | exact CEIL | keeplia LO | keeplia LO] ]. }
      eapply (cframe_seq LayoutP0 _ _ _ _ _ _ _ _ _ _ _ _ _ m0 mA m1 CFa CF2);
        [ keeplia ACV | keeplia ACV
        | eapply (window_mapped LayoutP0 _ lo); [exact ST1 | exact FR | cbn; lia | exact CEIL | keeplia LO | keeplia LO]
        | intros a X; exact X | | intros a X; left; exact X ].
      intros a [X|[X|X]].
      + right. right. right. right. left. rewrite <- EVI. left. exact X.
      + right. right. right. right. left. rewrite <- EVI. right. exact X.
      + right. left. unfold blk. split; [keeplia VEPlo| keeplia X].
  Qed.
End S.

Section Main.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.
  Hypothesis HMC : vep_mark_common_stmt.
  Hypothesis HEC : vep_emit_common_stmt.

  #[using="HEC HMC"] Lemma VEP_Finish_ok : VEP_Finish_stmt.
  Proof.
    unfold VEP_Finish_stmt. intros H VEP wa n N DATA v tag q vv va vi lo. intros until T.
    intros AINV MI Ha0 PW WS1 HENV HG IMG LD N0 DR NEDV NEDS NPB LBUD NBUD TP SP16 RA2 ST CEIL LO SPH K.
    eapply (T0 HMC HEC H VEP wa n N DATA v tag q vv va vi lo); eassumption.
  Qed.
End Main.
