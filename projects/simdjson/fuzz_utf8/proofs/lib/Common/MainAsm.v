(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import FPSteps. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import ShapeAlg SpinAlg AgentLib. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import Spec. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanInit AsanNodesIface AsanNodesMmA AsanNodesMmB. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AsanNodesArg AsanNodesIO AsanIOSpec AsanNodesIOSound AsanNodesIOInit AsanMainLib AsanShape ImgParams MainDefs MainTree MallocSpec MallocNodes MallocNodesSound ExecNodes ExecNodesSound ExecNodesWSound. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AsanPlanSoundSums. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import MallocNodes2 SlotProp MallocNodes2Sound AsanNodesRP LinkNodes LinkNodesSound SmearNode SmearNodeSound FactGcNode FactGcNodeSound MoveNodes MoveNodesSound MinifyGhost ParserGhost. (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Certs.
  Variable ip : imgparams.

  Record certs : Type := CERTS {
    c_IT0 : itab;                                 (* [comment removed for export] *)
    c_IT0_ok : itab_sound (ip_segs ip) c_IT0;     (* [comment removed for export] *)
    c_fuel0 : nat;                                (* [comment removed for export] *)
    c_HS0 : nat -> option acs;                    (* [comment removed for export] *)
    c_plan0 : plan;
    c_shape0 : shape;
    c_cert0 : startup_check ip c_IT0 c_fuel0 c_HS0 c_plan0 = COk c_shape0;
    c_holes0 : all_holes c_shape0 = true;         (* [comment removed for export] *)
    c_noblob : forall h ch, c_HS0 h = Some ch -> acs_noblob ch = true;   (* [comment removed for export] *)
    c_noprops : forall h ch, c_HS0 h = Some ch -> a_props ch = [];        (* [comment removed for export] *)
    c_ITm : itab;                                 (* [comment removed for export] *)
    c_ITm_ok : itab_sound (ip_segs ip) c_ITm;
    c_tree : nat -> nat -> mtree;                 (* [comment removed for export] *)
    c_SG : nat -> option segdef;                  (* [comment removed for export] *)
    c_SG_ok : segs_ok ip c_ITm c_SG;               (* [comment removed for export] *)
    c_trees : forall h ch i, c_HS0 h = Some ch -> (i < 6)%nat -> mtree_ok ip c_ITm c_SG None ch (root_class i) (c_tree h i) = true
  }.
  (* [comment removed for export] *)
  Record certsV : Type := CERTSV {
    v_IT0 : itab;
    v_IT0_ok : itab_sound (ip_segs ip) v_IT0;
    v_fuel0 : nat;
    v_HS0 : nat -> option acs;
    v_plan0 : plan;
    v_shape0 : shape;
    v_cert0 : startup_check ip v_IT0 v_fuel0 v_HS0 v_plan0 = COk v_shape0;
    v_holes0 : all_holes v_shape0 = true;
    v_noblob : forall h ch, v_HS0 h = Some ch -> acs_noblob ch = true;
    v_noprops : forall h ch, v_HS0 h = Some ch -> a_props ch = [];
    v_ITm : itab;
    v_ITm_ok : itab_sound (ip_segs ip) v_ITm;
    v_tree : nat -> nat -> mtree;
    v_ST : segtab;                                 (* [comment removed for export] *)
    v_ST_ok : segs_okV ip v_ITm v_ST;
    v_GV_ok : gv_ok ip v_ST;                       (* [comment removed for export] *)
    v_trees : forall h ch i, v_HS0 h = Some ch -> (i < 6)%nat -> mtree_okV ip v_ITm v_ST None ch (root_class i) (v_tree h i) = true
  }.
  Definition certs_V (C : certs) : certsV :=
    CERTSV (c_IT0 C) (c_IT0_ok C) (c_fuel0 C) (c_HS0 C) (c_plan0 C) (c_shape0 C) (c_cert0 C) (c_holes0 C) (c_noblob C) (c_noprops C)
           (c_ITm C) (c_ITm_ok C) (c_tree C) (ST (c_SG C) []) (c_SG_ok C) (gv_ok_nil ip (c_SG C)) (c_trees C).
End Certs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition arg_hooks_ok (ip : imgparams) (ph : PhdrInfo) : Prop :=
  forall (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (fs : Fs.Fs) (uid hw : word),   (* [comment removed for export] *)
    valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
    (forall (fy : FPState) id args, (id < 10)%nat ->
       node1_stmt (fx:=fy) (ip_segs ip) (ip_A ip) NX0 (ip_limit ip) (SINVm ph sp rdraw brk0 argv envp uid hw (content_of argv fs))
                  (argH0 ph sp rdraw argv envp uid hw) fs always
                  (fun cs => if ((id =? 0)%nat && (AN.g_istrlen (ip_G ip) =? 0))%bool then None
                             else AN.xn (ip_segs ip) (ip_A ip) NX0 (ip_G ip) id args cs))
    /\ forall (fy : FPState) id args cs ws, AN.xe_ws id args cs = Some ws ->    (* [comment removed for export] *)
       emit_stmtW_at (fx:=fy) (ip_segs ip) (ip_A ip) NX0 (ip_limit ip) (XEp ip) (SINVm ph sp rdraw brk0 argv envp uid hw (content_of argv fs))
                 (argH0 ph sp rdraw argv envp uid hw) fs id args cs ws.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Asm.
  (* [comment removed for export] *)
  Variable ip : imgparams.
  Variable ph : PhdrInfo.
  #[local] Notation SEGS := (ip_segs ip).
  #[local] Notation A := (ip_A ip).
  #[local] Notation G := (ip_G ip).
  #[local] Notation LIM := (ip_limit ip).
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
  Hypothesis RES_len : res_len_ok SEGS A.
  Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
                               (segments_reserved SEGS).
  Hypothesis HULL_ok : hull_ok A.
  Hypothesis SHADOW_ok : shadow_ok A.
  Hypothesis IMG : img_facts SEGS A ph.
  Hypothesis LIM_ok : LIMIT_MIN <= LIM.

  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid : word.
  Variable hw : word.   (* [comment removed for export] *)
  Variable groups : list word.
  Variable net : NetQueue.
  Variable nofile sigmask : word.   (* [comment removed for export] *)
  Variable abt : bool.   (* [comment removed for export] *)
  Variable urnd : InputStream.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk SEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis HULL_tight : AsanNodesMmLib.hull_tight_b (segments_reserved SEGS) (img_lo A) (img_hi A) = true /\ img_lo A < img_hi A.
  (* [comment removed for export] *)
  Hypothesis SEGS_wr : AsanPlanSoundSums.APSX.segs_wr_ok SEGS.

  #[local] Notation c := (content_of argv fs).
  #[local] Notation SINV0' := (SINV0 ph sp rdraw brk0 argv envp uid hw).
  #[local] Notation SINVM := (SINVm ph sp rdraw brk0 argv envp uid hw (content_of argv fs)).
  #[local] Notation argH := (argH0 ph sp rdraw argv envp uid hw).
  #[local] Notation E0a := (E0 ph sp rdraw brk0 argv envp uid hw).

  (* [comment removed for export] *)
  Let AH := argH0_high ph sp rdraw argv envp uid hw Hsp Hva.
  Let AA := argH0_agree ph sp rdraw argv envp uid hw.
  (* [comment removed for export] *)
  Let ASP0 := argH0_sp ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit.
  Let SSP0 := SINV0_sp ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit.
  Let SF0 := SINV0_frame ph sp rdraw brk0 argv envp uid hw.
  Let SA0 := SINV0_agree ph sp rdraw brk0 argv envp uid hw.
  Lemma SFm : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINVM E M -> SINVM E M'.
  Proof. intros. eapply SINVm_frame; eassumption. Qed.
  Lemma SAm : forall E E' M, env_agree NX0 E E' -> SINVM E M -> SINVM E' M.
  Proof. intros. eapply SINVm_agree; eassumption. Qed.
  Lemma SM0 : forall E M, SINVM E M -> SINV0' E M.
  Proof. intros E M H. eapply SINVm_SINV0. exact H. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis MX : forall SINV : env -> (word -> option byte) -> Prop,
    (forall E M, SINV E M -> SINV0' E M) ->
    (forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M') ->
    (forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M) ->
    forall (fy : FPState) x, x_stmt (fx:=fy) SEGS A NX0 LIM SINV argH fs x.
  (* [comment removed for export] *)
  Hypothesis MAN : forall (fy : FPState) id args, (id < 10)%nat ->
    node1_stmt (fx:=fy) SEGS A NX0 LIM SINVM argH fs always
      (fun cs => if ((id =? 0)%nat && (AN.g_istrlen G =? 0))%bool then None else AN.xn SEGS A NX0 G id args cs).
  (* [comment removed for export] *)
  Hypothesis MXE : forall (fy : FPState) id args cs ws, AN.xe_ws id args cs = Some ws ->
    emit_stmtW_at (fx:=fy) SEGS A NX0 LIM (XEp ip) SINVM argH fs id args cs ws.
  (* [comment removed for export] *)
  Hypothesis MENF : forall (fy : FPState), ENFRAME_STMT (fx:=fy) ip.
  Hypothesis MFRP : forall (fy : FPState), FREEPRO_STMT (fx:=fy) ip.
  (* [comment removed for export] *)
  Hypothesis MRP : RPN.rp_entry (ip_RP ip) <> 0 ->
    forall SINV : env -> (word -> option byte) -> Prop,
    (forall E M, SINV E M -> SINV0' E M) ->
    (forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M') ->
    (forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M) ->
    forall (fy : FPState), ext_stmt (fx:=fy) SEGS A NX0 LIM (RPN.xn SEGS NX0 (ip_RP ip)) SINV argH fs.
  (* [comment removed for export] *)
  Hypothesis MXW : forall SINV : env -> (word -> option byte) -> Prop,
    (forall E M, SINV E M -> SINV0' E M) ->
    (forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M') ->
    (forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M) ->
    forall (fy : FPState) x args cs ws, AP.x_ws_std x args cs = Some ws ->
      node1_stmtW_at (fx:=fy) SEGS A NX0 LIM SINV argH fs always (node_x SEGS A NX0 x args) cs ws.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section NodesAt.
    Variable SINV : env -> (word -> option byte) -> Prop.
    Hypothesis S0 : forall E M, SINV E M -> SINV0' E M.
    Hypothesis SF : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
    Hypothesis SA : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.
    (* [comment removed for export] *)
    Let ASP : forall E M (a : word), SINV E M -> argH E a = true -> APS.uE E e_sp0 <= bv_unsigned a
      := fun E M a HS Ha => ASP0 E M a (S0 E M HS) Ha.
    Let SSP : forall E M, SINV E M -> sp_window_lo <= APS.uE E e_sp0 <= sp_window_hi
      := fun E M HS => SSP0 E M (S0 E M HS).
    Lemma n_sys : forall (fy : FPState) y, sys_stmt (fx:=fy) SEGS A NX0 LIM SINV argH fs y.
    Proof. intros fy. exact (AsanNodesMmB.node_sys_sound SEGS A NX0 APC_NX0_min LIM SINV argH fs RES_len HULL_ok SHADOW_ok AA SF SA ASP SSP HULL_tight). Qed.
    (* [comment removed for export] *)
    Lemma n_brk2 : forall (fy : FPState), brk2d_stmt (fx:=fy) SEGS A NX0 LIM SINV argH fs (node_brk2 A LIM).
    Proof. intros fy. exact (AsanNodesMmB.node_brk2_sound SEGS A NX0 LIM SINV argH fs SEGS_in_hull RES_hull HULL_ok SHADOW_ok AH SF ASP). Qed.   (* [comment removed for export] *)
    Lemma n_mmap : forall (fy : FPState), mmap_stmtW (fx:=fy) SEGS A NX0 LIM SINV argH fs.   (* [comment removed for export] *)
    Proof. intros fy. exact (node_mmap_sound_OBL SEGS A NX0 LIM SINV argH fs SEGS_in_hull RES_len RES_hull HULL_ok SHADOW_ok APC_NX0_min AH AA SF SA ASP SSP HULL_tight). Qed.
    Lemma n_mmapin : forall (fy : FPState), node1_stmt (fx:=fy) SEGS A NX0 LIM SINV argH fs (is_ecall_at SEGS) (node_mmapin A LIM).
    Proof. intros fy. exact (node_mmapin_sound_OBL SEGS A NX0 LIM SINV argH fs SEGS_in_hull RES_len RES_hull HULL_ok SHADOW_ok APC_NX0_min AH AA SF SA ASP SSP HULL_tight). Qed.
    Lemma n_mprotect : forall (fy : FPState), node1_stmt (fx:=fy) SEGS A NX0 LIM SINV argH fs (is_ecall_at SEGS) (node_mprotect A LIM).
    Proof. intros fy. exact (node_mprotect_sound_OBL SEGS A NX0 LIM SINV argH fs SEGS_in_hull RES_len RES_hull HULL_ok SHADOW_ok APC_NX0_min AH AA SF SA ASP SSP HULL_tight). Qed.
    Lemma n_exit : forall (fy : FPState), exit_stmt (fx:=fy) SEGS A LIM SINV argH fs.
    Proof. intros fy. exact (AsanNodesMmB.node_exit_sound SEGS A LIM SINV argH fs). Qed.
    Lemma n_join : forall (fy : FPState), join_stmt (fx:=fy) SEGS A NX0 LIM SINV argH fs.
    Proof. intros fy. exact (node_join_sound SEGS A NX0 LIM SINV argH fs). Qed.
    Lemma n_x : forall (fy : FPState) x, x_stmt (fx:=fy) SEGS A NX0 LIM SINV argH fs x.
    Proof. exact (MX SINV S0 SF SA). Qed.
    (* [comment removed for export] *)
    Lemma n_sysW : forall (fy : FPState) y cs ws, AP.sys_ws_std y cs = Some ws ->
      node1_stmtW_at (fx:=fy) SEGS A NX0 LIM SINV argH fs (is_ecall_at SEGS) (node_sys A NX0 y) cs ws.
    Proof. intros fy. exact (AsanNodesMmB.node_sysW_sound SEGS A NX0 APC_NX0_min LIM SINV argH fs AA SA). Qed.
  End NodesAt.

  (* [comment removed for export] *)
  Lemma m_xn : forall IT, itab_sound SEGS IT -> forall T, H_class_prop T argv fs SINVM ->
    forall (fy : FPState), ext_stmt (fx:=fy) SEGS A NX0 LIM (XNp ip IT T) SINVM argH fs.
  Proof.
    intros IT IT_ok T HT fy id args. unfold XNp.
    destruct (Nat.ltb_spec id 10) as [Hid|Hid]; [exact (MAN fy id args Hid)|].
    destruct ((id =? 20)%nat || (id =? 21)%nat)%bool eqn:Hmn.
    { (* [comment removed for export] *)
      intros cs cs' E R FULL model TT HC Hpre Hn Hk. discriminate Hn. }
    destruct ((40 <=? id)%nat && (id <? 50)%nat)%bool eqn:Hex.
    { exact (EXWS.xn_sound SEGS IT IT_ok A NX0 APC_NX0_min LIM SINVM argH fs SEGS_wx SEGS_in_hull HULL_ok AH AA SFm SAm SEGS_wr id args). }
    destruct (Nat.ltb_spec id 90) as [Hid'|Hid'].
    - exact (io_ext_stmt_init SEGS A ph SEGS_in_hull HULL_ok sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit LIM
               SINVM SM0 SFm SAm T HT id args).
    - destruct ((((id =? 100)%nat || (id =? 101)%nat) && negb (RPN.rp_entry (ip_RP ip) =? 0))%bool) eqn:Hrp.
      2:{ destruct (id =? 110)%nat; [exact (LNKS.xn_sound SEGS A NX0 LIM SINVM argH fs args)|].
          destruct (id =? 111)%nat; [exact (MVNS.xn_sound SEGS IT IT_ok A NX0 LIM SINVM argH fs SEGS_wx SEGS_in_hull HULL_ok AH SFm args)|].
          destruct (id =? 113)%nat; [exact (SMRS.xn_sound SEGS A NX0 LIM SINVM argH fs args)|].   (* [comment removed for export] *)
          destruct (id =? 115)%nat; [exact (xn_visfoot_sound_OBL SEGS A NX0 LIM SINVM argH fs SEGS_in_hull RES_len RES_hull HULL_ok SHADOW_ok APC_NX0_min AH AA SFm SAm (fun E M a HS Ha => ASP0 E M a (SM0 E M HS) Ha) (fun E M HS => SSP0 E M (SM0 E M HS)) HULL_tight args)|].   (* [comment removed for export] *)
          destruct (id =? 117)%nat; [exact (FGCS.xn_sound SEGS A NX0 LIM SINVM argH fs args)|].   (* [comment removed for export] *)
          intros cs cs' E R FULL model TT _ _ H; discriminate H. }
      apply andb_prop in Hrp as [_ Hnz]. apply Bool.negb_true_iff in Hnz. apply Z.eqb_neq in Hnz.
      exact (MRP Hnz SINVM SM0 SFm SAm fy id args).
  Qed.
  (* [comment removed for export] *)
  Lemma m_xnm : forall IT, itab_sound SEGS IT -> forall GV T, H_class_prop T argv fs SINVM ->
    forall (fy : FPState) id, MN2.extG_m id = false -> ext_stmt_at (fx:=fy) SEGS A NX0 LIM (XNmV ip IT GV T) SINVM argH fs id.
  Proof.
    intros IT IT_ok GV T HT fy id Hg args. unfold XNmV. unfold MN2.extG_m in Hg. rewrite Hg.
    destruct (Nat.ltb_spec id 10) as [Hid|Hid]; [exact (MAN fy id args Hid)|].
    destruct ((40 <=? id)%nat && (id <? 50)%nat)%bool eqn:Hex.
    { exact (EXWS.xn_sound SEGS IT IT_ok A NX0 APC_NX0_min LIM SINVM argH fs SEGS_wx SEGS_in_hull HULL_ok AH AA SFm SAm SEGS_wr id args). }
    destruct (Nat.ltb_spec id 90) as [Hid'|Hid'].
    - exact (io_ext_stmt_init SEGS A ph SEGS_in_hull HULL_ok sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit LIM
               SINVM SM0 SFm SAm T HT id args).
    - destruct ((((id =? 100)%nat || (id =? 101)%nat) && negb (RPN.rp_entry (ip_RP ip) =? 0))%bool) eqn:Hrp.
      2:{ destruct (id =? 110)%nat; [exact (LNKS.xn_sound SEGS A NX0 LIM SINVM argH fs args)|].
          destruct (id =? 111)%nat; [exact (MVNS.xn_sound SEGS IT IT_ok A NX0 LIM SINVM argH fs SEGS_wx SEGS_in_hull HULL_ok AH SFm args)|].
          destruct (id =? 113)%nat; [exact (SMRS.xn_sound SEGS A NX0 LIM SINVM argH fs args)|].   (* [comment removed for export] *)
          destruct (id =? 115)%nat; [exact (xn_visfoot_sound_OBL SEGS A NX0 LIM SINVM argH fs SEGS_in_hull RES_len RES_hull HULL_ok SHADOW_ok APC_NX0_min AH AA SFm SAm (fun E M a HS Ha => ASP0 E M a (SM0 E M HS) Ha) (fun E M HS => SSP0 E M (SM0 E M HS)) HULL_tight args)|].   (* [comment removed for export] *)
          destruct (id =? 117)%nat; [exact (FGCS.xn_sound SEGS A NX0 LIM SINVM argH fs args)|].   (* [comment removed for export] *)
          intros cs cs' E R FULL model TT _ _ H; discriminate H. }
      apply andb_prop in Hrp as [_ Hnz]. apply Bool.negb_true_iff in Hnz. apply Z.eqb_neq in Hnz.
      exact (MRP Hnz SINVM SM0 SFm SAm fy id args).
  Qed.
  Lemma m_xnmG : forall GV (GP : nat -> list Z -> (word -> option byte) -> Prop),
    (forall vs M, GP MN2.SLOT_ID vs M <-> slot_sem SEGS vs M) ->
    (forall id args E M M', (forall a, in_fp E (g_fp (PGA.Gparse GV) id args) a = true -> M' a = M a) ->
                            GP id (map (uE E) args) M -> GP id (map (uE E) args) M') ->
    forall IT T (fy : FPState) id, MN2.extG_m id = true -> ext_stmtG (fy:=fy) SEGS A NX0 LIM (XNmV ip IT GV T) SINVM argH fs GP id.
  Proof.
    intros GV GP GP50 GPfr IT T fy id Hg args cs cs' E R FULL model TT HC HP Hn Hk. unfold XNmV in Hn. unfold MN2.extG_m in Hg.
    rewrite Hg in Hn.
    destruct (Nat.ltb_spec id 10) as [Hid|Hid].
    { exfalso. apply orb_prop in Hg as [X|X]; apply Nat.eqb_eq in X; lia. }
    exact (xn2_soundG ip NX0 APC_NX0_min LIM SEGS_wx SEGS_in_hull HULL_ok SINVM argH AH AA SFm SAm fs GP GP50 (PGA.Gparse GV) GPfr (MENF fy) (MFRP fy)
             id args cs cs' E R FULL model TT HC HP Hn Hk).
  Qed.
  Lemma m_xb : forall T, H_class_prop T argv fs SINVM -> forall (fy : FPState), ext2_stmt (fx:=fy) SEGS A NX0 LIM (XBp ip T) SINVM argH fs.
  Proof.
    intros T HT fy. unfold XBp.
    exact (io_ext2_stmt_init SEGS A ph sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit LIM SINVM SM0 SFm SAm T HT).
  Qed.

  (* [comment removed for export] *)
  Lemma m_xe : forall (fy : FPState), emit_stmt (fx:=fy) SEGS A NX0 LIM (XEp ip) SINVM argH fs.
  Proof.
    intros fy. apply (emitW_stmt SEGS A NX0 LIM (XEp ip) SINVM argH fs AN.xe_ws); [|exact (MXE fy)].
    intros id args cs r Hn. unfold XEp in Hn. exact (AN.xe_ws_total _ _ _ _ id args cs r Hn).
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma m_xnF : forall IT, itab_sound SEGS IT -> forall T, H_class_prop T argv fs SINVM ->
    forall (fy : FPState) id, xnp_extF id = true -> ext_stmtF (fx:=fy) SEGS A NX0 LIM (XNp ip IT T) SINVM argH fs id.
  Proof.
    intros IT IT_ok T HT fy id Hid args cs cs' E R FULL model TT HC Hpre. unfold XNp. unfold xnp_extF in Hid.
    destruct (Nat.eqb_spec id 111) as [E111|N111].
    { rewrite E111. cbn [Nat.ltb Nat.leb Nat.eqb orb andb].
      exact (MVNS.xn_soundF SEGS IT IT_ok A NX0 LIM SINVM argH fs SEGS_wx SEGS_in_hull HULL_ok AH SFm args cs cs' E R FULL model TT HC Hpre). }
    rewrite orb_false_r in Hid.
    destruct ((40 <=? id)%nat && (id <? 50)%nat)%bool eqn:Hex.
    { apply andb_prop in Hex as [H40 H50]. apply Nat.leb_le in H40. apply Nat.ltb_lt in H50.
      destruct (Nat.ltb_spec id 10); [lia|].
      destruct ((id =? 20)%nat || (id =? 21)%nat)%bool eqn:Hmn.
      { exfalso. apply orb_prop in Hmn as [Hm|Hm]; apply Nat.eqb_eq in Hm; lia. }
      exact (EXWS.xn_soundF SEGS IT IT_ok A NX0 APC_NX0_min LIM SINVM argH fs SEGS_wx SEGS_in_hull HULL_ok AH AA SFm SAm SEGS_wr id args cs cs' E R FULL model TT HC Hpre). }
    rewrite orb_false_r in Hid.
    assert (CASES : (id = 16 \/ id = 18 \/ id = 19 \/ id = 22 \/ id = 23 \/ id = 24)%nat).
    { repeat (apply orb_prop in Hid as [Hid|Hid]); apply Nat.eqb_eq in Hid; lia. }
    assert (HidF : AsanNodesIOSound.io_extF id = true).
    { unfold AsanNodesIOSound.io_extF. destruct CASES as [-> | [-> | [-> | [-> | [-> | ->]]]]]; reflexivity. }
    pose proof (io_xn_soundF_init SEGS A ph sp rdraw argv envp fs uid hw LIM SINVM SFm SAm T HT id HidF args cs cs' E R FULL model TT HC Hpre) as HF.
    destruct CASES as [-> | [-> | [-> | [-> | [-> | ->]]]]]; cbn [Nat.ltb Nat.leb Nat.eqb orb andb]; exact HF.
  Qed.
  Lemma m_xnmF : forall IT, itab_sound SEGS IT -> forall GV T, H_class_prop T argv fs SINVM ->
    forall (fy : FPState) id, xnp_extF id = true -> ext_stmtF (fx:=fy) SEGS A NX0 LIM (XNmV ip IT GV T) SINVM argH fs id.
  Proof.
    intros IT IT_ok GV T HT fy id Hid args cs cs' E R FULL model TT HC Hpre. unfold XNmV. unfold xnp_extF in Hid.
    destruct (Nat.eqb_spec id 111) as [E111|N111].
    { rewrite E111. cbn [Nat.ltb Nat.leb Nat.eqb orb andb].
      exact (MVNS.xn_soundF SEGS IT IT_ok A NX0 LIM SINVM argH fs SEGS_wx SEGS_in_hull HULL_ok AH SFm args cs cs' E R FULL model TT HC Hpre). }
    rewrite orb_false_r in Hid.
    destruct ((40 <=? id)%nat && (id <? 50)%nat)%bool eqn:Hex.
    { apply andb_prop in Hex as [H40 H50]. apply Nat.leb_le in H40. apply Nat.ltb_lt in H50.
      destruct (Nat.ltb_spec id 10); [lia|].
      destruct ((id =? 20)%nat || (id =? 21)%nat)%bool eqn:Hmn.
      { exfalso. apply orb_prop in Hmn as [Hm|Hm]; apply Nat.eqb_eq in Hm; lia. }
      exact (EXWS.xn_soundF SEGS IT IT_ok A NX0 APC_NX0_min LIM SINVM argH fs SEGS_wx SEGS_in_hull HULL_ok AH AA SFm SAm SEGS_wr id args cs cs' E R FULL model TT HC Hpre). }
    rewrite orb_false_r in Hid.
    assert (CASES : (id = 16 \/ id = 18 \/ id = 19 \/ id = 22 \/ id = 23 \/ id = 24)%nat).
    { repeat (apply orb_prop in Hid as [Hid|Hid]); apply Nat.eqb_eq in Hid; lia. }
    assert (HidF : AsanNodesIOSound.io_extF id = true).
    { unfold AsanNodesIOSound.io_extF. destruct CASES as [-> | [-> | [-> | [-> | [-> | ->]]]]]; reflexivity. }
    pose proof (io_xn_soundF_init SEGS A ph sp rdraw argv envp fs uid hw LIM SINVM SFm SAm T HT id HidF args cs cs' E R FULL model TT HC Hpre) as HF.
    destruct CASES as [-> | [-> | [-> | [-> | [-> | ->]]]]]; cbn [Nat.ltb Nat.leb Nat.eqb orb andb]; exact HF.
  Qed.
  (* [comment removed for export] *)
  Lemma m_xnmW : forall IT, itab_sound SEGS IT -> forall GV T, H_class_prop T argv fs SINVM ->
    forall (fy : FPState) id args cs ws, xnp_ws id args cs = Some ws ->
    node1_stmtW_at (fx:=fy) SEGS A NX0 LIM SINVM argH fs always (XNmV ip IT GV T id args) cs ws.
  Proof.
    intros IT IT_ok GV T HT fy id args cs ws Hws. unfold xnp_ws in Hws.
    destruct ((10 <=? id)%nat && (id <? 20)%nat)%bool eqn:Hr; [|discriminate Hws].
    apply andb_prop in Hr as [H10 H20]. apply Nat.leb_le in H10. apply Nat.ltb_lt in H20.
    intros cs' E R FULL model TT HC Hpre Hn Hk. unfold XNmV in Hn.
    destruct (Nat.ltb_spec id 10); [lia|].
    destruct ((id =? 20)%nat || (id =? 21)%nat)%bool eqn:Hmn; [exfalso; apply orb_prop in Hmn as [Hm|Hm]; apply Nat.eqb_eq in Hm; lia|].
    destruct ((40 <=? id)%nat && (id <? 50)%nat)%bool eqn:Hex; [exfalso; apply andb_prop in Hex as [He _]; apply Nat.leb_le in He; lia|].
    destruct (Nat.ltb_spec id 90); [|lia].
    exact (io_xn_soundW_init SEGS A ph SEGS_in_hull HULL_ok sp rdraw argv envp fs Hsp Hva uid hw LIM SINVM SFm T id args cs ws Hws cs' E R FULL model TT HC Hpre Hn Hk).
  Qed.
  Lemma m_xnW : forall IT, itab_sound SEGS IT -> forall T, H_class_prop T argv fs SINVM ->
    forall (fy : FPState) id args cs ws, xnp_ws id args cs = Some ws ->
    node1_stmtW_at (fx:=fy) SEGS A NX0 LIM SINVM argH fs always (XNp ip IT T id args) cs ws.
  Proof.
    intros IT IT_ok T HT fy id args cs ws Hws. unfold xnp_ws in Hws.
    destruct ((10 <=? id)%nat && (id <? 20)%nat)%bool eqn:Hr; [|discriminate Hws].
    apply andb_prop in Hr as [H10 H20]. apply Nat.leb_le in H10. apply Nat.ltb_lt in H20.
    intros cs' E R FULL model TT HC Hpre Hn Hk. unfold XNp in Hn.
    destruct (Nat.ltb_spec id 10); [lia|].
    destruct ((id =? 20)%nat || (id =? 21)%nat)%bool eqn:Hmn; [exfalso; apply orb_prop in Hmn as [Hm|Hm]; apply Nat.eqb_eq in Hm; lia|].
    destruct ((40 <=? id)%nat && (id <? 50)%nat)%bool eqn:Hex; [exfalso; apply andb_prop in Hex as [He _]; apply Nat.leb_le in He; lia|].
    destruct (Nat.ltb_spec id 90); [|lia].
    exact (io_xn_soundW_init SEGS A ph SEGS_in_hull HULL_ok sp rdraw argv envp fs Hsp Hva uid hw LIM SINVM SFm T id args cs ws Hws cs' E R FULL model TT HC Hpre Hn Hk).
  Qed.
  (* [comment removed for export] *)
  Lemma m_VF : forall E M, SINVM E M -> know_ok SEGS E M (vfacts (variant_of c)).
  Proof.
    intros E M HS.
    pose proof HS as (_ & _ & _ & Hb). specialize (Hb 0%nat). cbn [Nat.add] in Hb.
    assert (HC : uE E AsanShape.CFGX = cfglen c).
    { unfold AsanShape.CFGX, JB. rewrite CFGX_denot, Hb, !hbyte_chunk0 by lia. reflexivity. }
    assert (HM : uE E AsanShape.XCM = bz 2 c mod 4).
    { unfold AsanShape.XCM, JB. rewrite XCM_denot, Hb, hbyte_chunk0 by lia. reflexivity. }
    assert (HN : uE E AsanShape.XB1S = bv_swrap 8 (bz 1 c) mod 2 ^ 64).
    { unfold AsanShape.XB1S, JB. rewrite XB1S_denot, Hb, hbyte_chunk0 by lia. reflexivity. }
    unfold uE in HC, HM, HN. pose proof (cfglen_range c) as CR. pose proof (bz_range 2 c) as BR. pose proof (bz_range 1 c) as BR1.
    assert (SW : bv_swrap 8 (bz 1 c) = (if bz 1 c <? 128 then bz 1 c else bz 1 c - 256)).
    { unfold bv_swrap, bv_wrap. change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
      destruct (Z.ltb_spec (bz 1 c) 128); [rewrite Z.mod_small by lia; lia|].
      replace (bz 1 c + 128) with ((bz 1 c + 128 - 256) + 1 * 256) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia. }
    unfold vfacts, variant_of, v_cfg0, v_cmod, v_cnt. cbn [fst snd].
    constructor; [|constructor; [|constructor; [|constructor]]].
    - destruct (Z.eqb_spec (cfglen c) 0) as [Hz|Hz]; cbn [kentry_ok]; rewrite HC; lia.
    - cbn [kentry_ok]. rewrite HM. lia.
    - destruct (Z.leb_spec 128 (bz 1 c)) as [Hc|Hc]; cbn [kentry_ok]; rewrite HN, SW.
      + destruct (Z.ltb_spec (bz 1 c) 128); [lia|].
        replace (bz 1 c - 256) with ((bz 1 c - 256 + 2 ^ 64) + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
      + destruct (Z.ltb_spec (bz 1 c) 128); [|lia]. rewrite Z.mod_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Startup.
    Variable IT0 : itab.
    Hypothesis IT0_ok : itab_sound SEGS IT0.
    Variable fuel0 : nat.
    Variable HS0 : nat -> option acs.
    Variable plan0 : plan.
    Variable shape0 : shape.
    Hypothesis cert0 : startup_check ip IT0 fuel0 HS0 plan0 = COk shape0.
    (* [comment removed for export] *)
    Variable HOLES : nat -> env -> Fs.Fs -> TSet.
    Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs'.
    Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
    (* [comment removed for export] *)
    Hypothesis HOLES_const : forall h1 h2, HOLES h1 = HOLES h2.
    (* [comment removed for export] *)
    Hypothesis HOLES_sound : forall (fy : FPState), frm_zero (@fp_csr fy) -> holes_stmt (fx:=fy) SEGS A LIM HS0 SINV0' argH HOLES fs APS.GP0.

    Lemma XN0_sound : forall (fy : FPState), ext_stmt (fx:=fy) SEGS A NX0 LIM XN0 SINV0' argH fs.
    Proof. intros fy id args cs cs' E R FULL model T _ _ H. discriminate H. Qed.
    (* [comment removed for export] *)
    Lemma XNs_sound : forall (fy : FPState), ext_stmt (fx:=fy) SEGS A NX0 LIM (XNs ip IT0) SINV0' argH fs.
    Proof.
      intros fy id args. unfold XNs. destruct (id =? 110)%nat; [exact (LNKS.xn_sound SEGS A NX0 LIM SINV0' argH fs args)|].
      destruct ((40 <=? id)%nat && (id <? 50)%nat)%bool.
      { exact (EXWS.xn_sound SEGS IT0 IT0_ok A NX0 APC_NX0_min LIM SINV0' argH fs SEGS_wx SEGS_in_hull HULL_ok AH AA SF0 SA0 SEGS_wr id args). }
      (* [comment removed for export] *)
      destruct ((((id =? 100)%nat || (id =? 101)%nat) && negb (RPN.rp_entry (ip_RP ip) =? 0))%bool) eqn:Hrp.
      { apply andb_prop in Hrp as [_ Hnz]. apply Bool.negb_true_iff in Hnz. apply Z.eqb_neq in Hnz.
        exact (MRP Hnz SINV0' (fun _ _ H => H) SF0 SA0 fy id args). }
      destruct (id =? 113)%nat; [exact (SMRS.xn_sound SEGS A NX0 LIM SINV0' argH fs args)|].   (* [comment removed for export] *)
      destruct (id =? 115)%nat; [exact (xn_visfoot_sound_OBL SEGS A NX0 LIM SINV0' argH fs SEGS_in_hull RES_len RES_hull HULL_ok SHADOW_ok APC_NX0_min AH AA SF0 SA0 ASP0 SSP0 HULL_tight args)|].   (* [comment removed for export] *)
      destruct (id =? 117)%nat; [exact (FGCS.xn_sound SEGS A NX0 LIM SINV0' argH fs args)|].   (* [comment removed for export] *)
      intros cs cs' E R FULL model T _ _ H. discriminate H.
    Qed.
    Lemma XE0_sound : forall (fy : FPState), emit_stmt (fx:=fy) SEGS A NX0 LIM XE0 SINV0' argH fs.
    Proof. intros fy id args cs fd ps cs' E R FULL model T _ H _. discriminate H. Qed.
    Lemma XB0_sound : forall (fy : FPState), ext2_stmt (fx:=fy) SEGS A NX0 LIM XB0 SINV0' argH fs.
    Proof. intros fy id args cs csa csb E R FULL model TA TB _ H. discriminate H. Qed.

    Theorem startup_realizes : forall apc : N, Z.of_N apc = a_entry A ->
      srealizes SEGS (init_config SEGS apc ph sp brk0 mbase rdraw LIM (AsanInit.inp argv envp fs stdin uid gid hw groups net nofile sigmask abt urnd))
                (sd HOLES t_nil E0a fs shape0).
    Proof.
      intros apc Hpc.
      rewrite (init_cfg_eq SEGS A ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abt urnd LIM apc Hpc).
      pose proof (init_cs_ok SEGS A ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abt urnd IMG Hsp Hbrk Hva Hve Hfit Huid Hhw LIM LIM_ok) as HC.   (* [comment removed for export] *)
      unfold startup_check in cert0.
      pose proof (check_sound_top SEGS IT0 IT0_ok A NX0 APC_NX0_min LIM HS0 (XNs ip IT0) XE0 XB0
               SEGS_wx SEGS_in_hull HULL_ok SHADOW_ok SINV0' argH AH AA SF0 SA0
               HOLES HOLES_agree HOLES_nil fs KCm XPS APS.GP0
               (fun _ : xp_hq XPS = true => HOLES_const)                                  (* [comment removed for export] *)
               (n_sys SINV0' (fun E M H => H) SF0 SA0) (n_brk2 SINV0' (fun E M H => H) SF0) (n_mmap SINV0' (fun E M H => H) SF0 SA0)
               (n_mmapin SINV0' (fun E M H => H) SF0 SA0) (n_mprotect SINV0' (fun E M H => H) SF0 SA0) (n_exit SINV0') (n_x SINV0' (fun E M H => H) SF0 SA0)
               (n_join SINV0')
               (fun fy id _ => XNs_sound fy id) XE0_sound XB0_sound
               HOLES_sound (extF_none_sound SEGS A NX0 LIM (XNs ip IT0) SINV0' argH fs)
               (sysW_none_sound SEGS A NX0 LIM SINV0' argH fs) (extW_none_sound SEGS A NX0 LIM (XNs ip IT0) SINV0' argH fs)
               (emitW_none_sound SEGS A NX0 LIM XE0 SINV0' argH fs) (xW_none_sound SEGS A NX0 LIM SINV0' argH fs)   (* [comment removed for export] *)
               (APS.GP0_frame G0) (APS.G0_ok _ _) (APS.extG_none_sound _ _ _ _ _ _ _ _ _)                          (* [comment removed for export] *)
               (segs_none_sound SEGS A NX0 LIM SINV0' argH fs)
               eq_refl fuel0 BFUELm plan0 (init_acs_of A) shape0 cert0
               fx0 _ _ _ _ t_nil fp_frm_zero_fx0 HC (APS.props_ok_GP0 _ _ _) eq_refl) as RR.   (* [comment removed for export] *)
      match type of RR with srealizes _ ?c1 ?T1 =>
        match goal with |- srealizes _ ?c2 ?T2 => change c2 with c1; change T2 with T1 end end.
      exact RR.
    Qed.
  End Startup.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition HOLESM (h : nat) (E : env) (fs' : Fs.Fs) : TSet := spec argv fs'.
  Lemma HOLESM_agree : forall h E E' fs', env_agree NX0 E E' -> HOLESM h E fs' = HOLESM h E' fs'.
  Proof. reflexivity. Qed.
  Lemma HOLESM_nil : forall h E fs', HOLESM h E fs' [].
  Proof. intros. apply spec_nil. Qed.

  Variable CC : certsV ip.   (* [comment removed for export] *)

  Theorem main_holes : forall (fy : FPState), frm_zero (@fp_csr fy) -> holes_stmt (fx:=fy) SEGS A LIM (v_HS0 ip CC) SINV0' argH HOLESM fs APS.GP0.
  Proof.
    intros fy Hz h ch Hh E R FULL model HC _.
    (* [comment removed for export] *)
    pose proof (cs_ok_reblob SEGS A ph sp rdraw brk0 argv envp uid hw c LIM fs E ch R FULL model (v_noblob ip CC h ch Hh) HC) as HC1.
    unfold HOLESM. rewrite (co_fs _ _ _ _ _ _ _ _ _ _ _ HC).
    destruct (root_cover argv fs Hva) as (i & Hi & HCi).
    (* [comment removed for export] *)
    pose proof (mtree_sound ip ph (v_ITm ip CC) (v_ITm_ok ip CC) (v_ST ip CC) (v_ST_ok ip CC) (v_GV_ok ip CC) SEGS_wx SEGS_in_hull HULL_ok SHADOW_ok sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit
                  (n_sys SINVM SM0 SFm SAm) (n_brk2 SINVM SM0 SFm) (n_mmap SINVM SM0 SFm SAm) (n_mmapin SINVM SM0 SFm SAm)
                  (n_mprotect SINVM SM0 SFm SAm) (n_exit SINVM) (n_x SINVM SM0 SFm SAm) (n_join SINVM)
                  (m_xnm (v_ITm ip CC) (v_ITm_ok ip CC) (st_vcs (v_ST ip CC))) (m_xnmF (v_ITm ip CC) (v_ITm_ok ip CC) (st_vcs (v_ST ip CC)))
                  (m_xnmG (st_vcs (v_ST ip CC)) (PGA.GPall SEGS) (PGA.GPall_slot SEGS) (PGA.GPall_frame SEGS (st_vcs (v_ST ip CC))) (v_ITm ip CC))
                  (m_xnmW (v_ITm ip CC) (v_ITm_ok ip CC) (st_vcs (v_ST ip CC))) (m_xnW (v_ITm ip CC) (v_ITm_ok ip CC))
                  m_xe MXE (n_sysW SINVM SAm) m_xb
                  (MXW SINVM SM0 SFm SAm) (m_xn (v_ITm ip CC) (v_ITm_ok ip CC)) (m_xnF (v_ITm ip CC) (v_ITm_ok ip CC)) m_VF
                  (v_tree ip CC h i) None ch (root_class i) (v_trees ip CC h ch i Hh Hi) HCi I
                  fy _ R FULL model Hz HC1 ltac:(rewrite (v_noprops ip CC h ch Hh); apply props_ok_nil)) as RZ.
    cbn [DEN] in RZ. exact RZ.
  Qed.

  (* [comment removed for export] *)
  Theorem realizes_specV : forall apc : N, Z.of_N apc = a_entry A ->
    srealizes SEGS (init_config SEGS apc ph sp brk0 mbase rdraw LIM (AsanInit.inp argv envp fs stdin uid gid hw groups net nofile sigmask abt urnd))
              (spec argv fs).
  Proof.
    intros apc Hpc.
    eapply srz_conseq.
    - exact (startup_realizes (v_IT0 ip CC) (v_IT0_ok ip CC) (v_fuel0 ip CC) (v_HS0 ip CC) (v_plan0 ip CC) (v_shape0 ip CC) (v_cert0 ip CC)
               HOLESM HOLESM_agree HOLESM_nil (fun _ _ => eq_refl) main_holes apc Hpc).
    - apply sd_all_holes; [exact (v_holes0 ip CC) | reflexivity].
  Qed.
End Asm.

(* [comment removed for export] *)
Definition realizes_spec ip ph SEGS_wx SEGS_in_hull RES_len RES_hull HULL_ok SHADOW_ok IMG LIM_ok
    sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abt urnd Hsp Hbrk Hva Hve Hfit Huid Hhw HULL_tight SEGS_wr
    MX MAN MXE MENF MFRP MRP MXW (CC : certs ip) :=
  realizes_specV ip ph SEGS_wx SEGS_in_hull RES_len RES_hull HULL_ok SHADOW_ok IMG LIM_ok
    sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abt urnd Hsp Hbrk Hva Hve Hfit Huid Hhw HULL_tight SEGS_wr
    MX MAN MXE MENF MFRP MRP MXW (certs_V ip CC).
