(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.H Require GcFlushY01.  (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Import AsanUbsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs LibFrame LibWP2Spec LibWP2Lib.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs BoBase AsRtSpec AsLibFrame AsLibEnv AsLibTagsLib AsLibFPSpec AsLibWP2Spec AsLibCurveSpec AsLibBswap BoLibReadA2Ba BoLibReadA2Bb BoLibSpec BoLibReadB2Aa BoLibReadB2Ab BoLibReadB2Ac BoLibReadB2As AsLibPlace.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymDriveLZ.
Import ListNotations.
Open Scope bv_scope.
Import ASX. Import ASXS.
(* [comment removed for export] *)
Local Ltac ev_simpl E ::=
  lazymatch goal with |- ?G =>
    let G1 := match tt with | _ => eval unfold E in G | _ => G end in
    let G2 := eval lazy [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals] in G1 in
    change G2
  end.
Local Ltac ev_simpl_in E H ::= try unfold E in H; lazy [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals] in H.
(* [comment removed for export] *)
#[local] Ltac AsSymDrive.run_fp_with_h HR HF HK fuel stops scr chints keep extra ::= run_fp_with_h_lz HR HF HK fuel stops scr chints keep extra.
#[local] Ltac AsSymDrive.branch_case_with HR HF HK Hc ::= branch_case_with_lz HR HF HK Hc.
#[local] Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.   (* [comment removed for export] *)
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac el_t1 := (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker.
(* [comment removed for export] *)
Local Ltac el_dm_pose x k := let v := eval vm_compute in k in lazymatch v with Zpos _ =>   (* [comment removed for export] *)
  lazymatch goal with _ : (x = k * (x / k) + x mod k)%Z |- _ => fail | _ =>
    pose proof (Z.div_mod x k ltac:(vm_compute; discriminate)); pose proof (Z.mod_pos_bound x k ltac:(vm_compute; reflexivity)) end end.
Local Ltac el_dm := repeat match goal with
  | |- context [ (?x / ?k)%Z ] => el_dm_pose x k
  | |- context [ (?x mod ?k)%Z ] => el_dm_pose x k
  | H : ?T |- _ => lazymatch T with (_ <= _)%Z => idtac | (_ < _)%Z => idtac | @eq Z _ _ => idtac | _ /\ _ => idtac | _ \/ _ => idtac end;
      match T with context [ (?x / ?k)%Z ] => el_dm_pose x k | context [ (?x mod ?k)%Z ] => el_dm_pose x k end
  end.
Local Ltac el_lia_core3 := first [ el_t1 | Zify.zify; xlia zchecker ].   (* [comment removed for export] *)
Local Ltac el_lia_core := first [ el_t1 | ((progress el_dm); el_t1) ].
Local Ltac el_goal_has_var := match goal with |- ?G => match G with context [?x] => is_var x end end.
Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].

Section REB.
  Variable ceil : Z.
  Variables (FPI0 : FPState) (regs0 : bvmap 5 word) (mem0 rom : word -> option byte) (ret : word).
  Variables (data : word) (len : Z) (bs : list byte) (sp T B : word) (pcs : Z) (fs : Z) (ch : chain).
  Hypothesis Hra : getr regs0 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis HPRE : b2a_pre_bo SEGS as_both ceil data len bs sp T B pcs fs ch FPI0 regs0 mem0.
  Hypothesis Hcanon : canonicalize_contract_as SEGS as_both ceil.
  Hypothesis Hrc : read_curves_contract_bo SEGS as_both ceil.

  #[local] Abbreviation a := (bv_unsigned B).
  #[local] Abbreviation spv := (bv_unsigned sp).
  #[local] Abbreviation t := (bv_unsigned T).
  #[local] Abbreviation eobw := (Z_to_bv 64 (bv_unsigned data + len)).
  #[local] Abbreviation ADM := (adm ceil FPI0 regs0 mem0 ret data len bs sp T B fs ch).
  #[local] Abbreviation QP := (Qpost FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch).
  #[local] Abbreviation TAGC := (tagc data len T).
  #[local] Abbreviation curves0I := (curves0 data len B).
  #[local] Abbreviation stkI := (stk data len bs sp T B).
  #[local] Abbreviation WI := (W data bs).
  #[local] Abbreviation bbI := (bb data bs).
  #[local] Abbreviation pre_factsI := (pre_facts ceil FPI0 regs0 mem0 data len bs sp T B pcs fs ch HPRE).
  #[local] Abbreviation pre_tagI := (pre_tag ceil FPI0 regs0 mem0 data len bs sp T B pcs fs ch HPRE).
  #[local] Abbreviation kn_adm_okI := (kn_adm_ok ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch HPRE).
  #[local] Abbreviation kn_end_okI := (kn_end_ok ceil FPI0 regs0 mem0 ret data len bs sp T B pcs fs ch HPRE).
  #[local] Abbreviation kn_tag_okI := (kn_tag_ok ceil FPI0 regs0 mem0 ret data len bs sp T B pcs fs ch HPRE).
  #[local] Abbreviation kn_m_okI := (kn_m_ok ceil FPI0 regs0 mem0 ret data len bs sp T B pcs fs ch HPRE).
  #[local] Abbreviation adm_frame0I := (adm_frame0 ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch HPRE).
  #[local] Abbreviation failkI := (failk ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch Hret HPRE).
  #[local] Abbreviation failk'I := (failk' ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch Hret HPRE).
  #[local] Abbreviation tagc_frameI := (tagc_frame ceil FPI0 regs0 mem0 data len bs sp T B pcs fs ch HPRE).
  #[local] Abbreviation curves0_frameI := (curves0_frame ceil FPI0 regs0 mem0 data len bs sp T B pcs fs ch HPRE).
  #[local] Abbreviation rc_pre_atI := (rc_pre_at ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch HPRE).
  #[local] Abbreviation adm_rcI := (adm_rc ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch HPRE).
  #[local] Abbreviation curves0_rcI := (curves0_rc ceil FPI0 regs0 mem0 data len bs sp T B pcs fs ch HPRE).

  #[local] Abbreviation mab_cellsI := (mab_cells B).
  #[local] Abbreviation le4wI := (le4w data bs).
  #[local] Abbreviation be4I := (be4 data bs).
  #[local] Abbreviation kn_ms_okI := (kn_ms_ok ceil FPI0 regs0 mem0 ret data len bs sp T B pcs fs ch HPRE).
  #[local] Abbreviation stk_frameI := (stk_frame ceil FPI0 regs0 mem0 data len bs sp T B pcs fs ch HPRE).
  #[local] Abbreviation mab_cells_frameI := (mab_cells_frame ceil FPI0 regs0 mem0 data len bs sp T B pcs fs ch HPRE).
  #[local] Abbreviation m1_stmtI := (m1_stmt ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch).

  #[local] Abbreviation jseg_stmtI := (jseg_stmt ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch).
  #[local] Abbreviation curves10I := (curves10 data len B).
  #[local] Abbreviation in0I := (in0 ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch Hret HPRE Hcanon).
  #[local] Abbreviation curves10_rcI := (curves10_rc ceil FPI0 regs0 mem0 data len bs sp T B pcs fs ch HPRE).

  #[local] Abbreviation m3a_stmtI := (m3a_stmt ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch).
  Hypothesis M3A : m3a_stmtI.

  (* [comment removed for export] *)
  Ltac adm_facts HADM :=
    pose proof HADM as (A2 & A3 & A4 & A8 & AF & AS & AFR & AD & AWA & AWS & AASF & AH & AFL);
    pose proof pre_factsI as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & _);
    assert (U2 : bv_unsigned (getr _ 2) = (spv - 240)%Z) by (rewrite A2, u_small by lia; lia).

  Ltac pkg HADM extra kx ktac :=
    lazymatch goal with
    | |- runs_to _ (@mkst ?FPI ?R _ ?M _) _ =>
      set (E := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++
         [ret; getr regs0 8; getr regs0 9; getr regs0 18; getr regs0 19; getr regs0 20; getr regs0 21;
          getr regs0 22; getr regs0 23; getr regs0 24; getr regs0 25; getr regs0 26; getr regs0 27;
          data; Z_to_bv 64 len] ++ extra)) (blobs_ev [bs]));
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs]));
      assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs]));
      pose proof (HR : id _) as HR0; pose proof (HF : id _) as HF0;
      let HK1 := fresh "HK1" in let HK2 := fresh "HK2" in let HK3 := fresh "HK3" in
      pose proof (kn_adm_okI FPI R M extra HADM) as HK1; change (know_ok SEGS E M kn_adm) in HK1;
      assert (HK2 : know_ok SEGS E M kx); [ktac|];
      pose proof (kn_end_okI FPI R M extra HADM) as HK3; change (know_ok SEGS E M kn_end) in HK3;
      pose proof (know_ok_app SEGS E M kn_adm (kx ++ kn_end) HK1 (know_ok_app SEGS E M kx kn_end HK2 HK3)) as HK;
      clear HK1 HK2 HK3;
      cbv beta delta [kn_adm kn_end] in HK; cbn [app] in HK
    end.

  Ltac pkg_tag HADM HTAG H18 rest kx ktac :=
    lazymatch type of HTAG with tagc _ _ _ ?ty ?sz ?buf _ =>
      pkg HADM ([Z_to_bv 64 sz; buf] ++ rest) (kn_tag (ELit ty) ++ kx)
        ltac:(apply know_ok_app; [exact (kn_tag_okI _ _ _ ty sz buf rest (ELit ty) HADM HTAG H18 eq_refl) | ktac])
    end.

  (* [comment removed for export] *)
  Ltac pkg_m HADM HTAG Hsz rest kx ktac :=
    lazymatch type of HTAG with tagc _ _ _ _ ?sz ?buf _ =>
      pkg HADM (mvals data len bs T sz buf ++ rest) ((kn_tagv ++ kn_bytes) ++ kx)
        ltac:(match goal with Ed := Env _ _ |- _ => cbv beta delta [mvals mbytes] in Ed; cbn [app] in Ed end; apply know_ok_app; [exact (kn_m_okI _ _ _ sz buf rest HADM HTAG Hsz) | ktac]);
      lazymatch goal with HK : know_ok _ _ _ ?kn |- _ =>
        let kn' := eval vm_compute in kn in change kn with kn' in HK end;
      match goal with Edef := Env _ _ |- _ => cbv beta delta [mvals mbytes app] in Edef end
    end.

  Ltac pkg_ms HADM HTAG Hsz HSTK rest kx ktac :=
    lazymatch type of HTAG with tagc _ _ _ _ ?sz ?buf _ =>
      pkg HADM (mvals data len bs T sz buf ++ rest) ((kn_tagv ++ kn_bytes ++ kn_stk) ++ kx)
        ltac:(match goal with Ed := Env _ _ |- _ => cbv beta delta [mvals mbytes] in Ed; cbn [app] in Ed end; apply know_ok_app; [exact (kn_ms_okI _ _ _ sz buf rest HADM HTAG Hsz HSTK) | ktac]);
      lazymatch goal with HK : know_ok _ _ _ ?kn |- _ =>
        let kn' := eval vm_compute in kn in change kn with kn' in HK end;
      match goal with Edef := Env _ _ |- _ => cbv beta delta [mvals mbytes app] in Edef end
    end.

  Ltac rewrite_getr_in H :=
    repeat match goal with G : getr ?R ?r = _ |- _ => rewrite G in H end.
  Ltac subst_mems :=
    repeat match goal with H : @eq (word -> option byte) ?x _ |- _ => is_var x; subst x end.

  Ltac adm_now HADM HADM1 :=
    subst_mems;
    lazymatch goal with
    | HR : regs_ok ?E ?sr ?R1, HF : fregs_ok _ ?sfr (@fp_regs ?I1), HF0 : id (fregs_ok _ ?sfr0 (@fp_regs ?I0))
      |- runs_to _ (@mkst _ _ _ ?M1 _) _ =>
      lazymatch type of HADM with adm _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?R ?M0 =>
        assert (HADM1 : ADM I1 R1 M1);
        [ apply (adm_frame0I I0 I1 R R1 M0 M1 [] HADM);
          [ apply frame_mod_refl
          | apply Forall_nil
          | apply Forall_nil
          | regv HR (2%bv:reg); reflexivity
          | regv HR (3%bv:reg); reflexivity
          | regv HR (4%bv:reg); reflexivity
          | regv HR (8%bv:reg); reflexivity
          | exact (fregs_same_on E sfr0 sfr _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity)) ]
        | ]
      end
    end.

  Ltac pin_lit HR r H := lazymatch type of H with getr _ _ = Z_to_bv 64 ?v => pin_reg HR r (ELit v) by (cbn [edenot]; exact H) end.
  Ltac pin_add HR r Hr b Hb k :=
    lazymatch type of HR with regs_ok ?E _ _ =>
      pin_reg HR r (EAlu ALU_ADD (EVar b) (ELit k))
        by (cbn [edenot]; ev_simpl E; rewrite ?Hb, Hr; apply add_lit_word; lia)
    end.
  Ltac pin_sh HR r Hr b Hb P k c :=
    lazymatch type of HR with regs_ok ?E _ _ =>
      pin_reg HR r (EAlu ALU_ADD (EAlu ALU_SRL (EVar b) (ELit 3)) (ELit (SB + c)))
        by (cbn [edenot]; ev_simpl E; rewrite ?Hb, Hr; symmetry;
            apply (sh_addr_word P k); first [assumption | reflexivity | lia])
    end.
  Ltac pin_var HR r Hr v :=
    lazymatch type of HR with regs_ok ?E _ _ =>
      pin_reg HR r (EVar v) by (cbn [edenot]; ev_simpl E; exact Hr)
    end.
  Ltac kreg Hkeep r :=
    lazymatch goal with HR : regs_ok _ _ _ |- _ =>
      rewrite (Hkeep r ltac:(first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)])); regv HR r; rewrite_getr;
      first [ reflexivity | assumption
            | symmetry; apply add_lit_word; lia
            | apply sh_addr_word; first [assumption | reflexivity | lia] ]
    end.
  Ltac creg r :=
    lazymatch goal with HR : regs_ok _ _ _ |- _ =>
      regv HR r; rewrite_getr;
      first [ reflexivity | assumption
            | symmetry; apply add_lit_word; lia
            | apply sh_addr_word; first [assumption | reflexivity | lia] ]
    end.

  Ltac mods_in H :=
    repeat match type of H with context [ (?x mod ?m)%Z ] =>
      lazymatch x with context [ (_ mod _)%Z ] => fail | _ => rewrite (Z.mod_small x m) in H by lia end end.
  Ltac zbool H :=
    first [ apply Z.ltb_lt in H | apply Z.ltb_ge in H | apply Z.eqb_eq in H | apply Z.eqb_neq in H ].
  Ltac hc_lin Hc :=
    revert Hc; rewrite ?branch_taken_Z; cbv beta iota; linearize;
    cbn [edenot fop1_denot fop2_denot fop3_denot];
    lazymatch goal with HK : know_ok _ ?E _ _ |- _ => ev_simpl E end;
    rewrite ?uW, ?Z_to_bv_unsigned, ?bv_wrap64_mod; intros Hc;
    try (apply (f_equal negb) in Hc; rewrite negb_involutive in Hc; cbn [negb] in Hc);
    mods_in Hc; zbool Hc.

  Ltac regions_eq :=
    cbn [regions_denot map fst snd]; unfold adenot, v_addi; cbn [a_base a_off edenot];
    lazymatch goal with HK : know_ok _ ?E _ _ |- _ => ev_simpl E end; rewrite_getr; rewrite ?u_small_frame by lia;
    repeat (apply f_equal2; [apply f_equal2; [apply f_equal; lia | lia] | ]); reflexivity.

  Ltac frame_logs RS :=
    lazymatch goal with
    | |- frame_mod ?m0 ?m0 _ => apply frame_mod_refl
    | HK : know_ok _ ?E _ _ |- frame_mod ?m0 (mem_denot _ ?m1 ?log) _ =>
        apply (frame_mod_trans_same m0 m1);
        [ frame_logs RS
        | apply (frame_mod_mem_denot E m1 log RS);
          [ lazymatch goal with H : log_flat _ log |- _ => exact H end
          | repeat (apply Forall_cons); [..|apply Forall_nil]; cbn [fst snd]; unfold flat, estart;
            cbn [a_base a_off edenot]; ev_simpl E; rewrite_getr; rewrite ?u_small_frame by lia; lia
          | vm_compute; reflexivity ] ]
    end.

  (* [comment removed for export] *)
  Ltac frame_now HADM RS rsZ Hfr :=
    subst_mems;
    lazymatch type of HADM with adm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?M0 =>
    lazymatch goal with HK : know_ok _ ?E ?M1 _ |- _ =>
      assert (Hfr : frame_mod M0 M1 rsZ);
      [ replace rsZ with (regions_denot E RS) by regions_eq; frame_logs RS | ]
    end end.

  (* [comment removed for export] *)
  Ltac adm_fr HADM Hfr HADM1 :=
    lazymatch goal with
    | HR : regs_ok ?E ?sr ?R1, HF : fregs_ok _ ?sfr (@fp_regs ?I1), HF0 : id (fregs_ok _ ?sfr0 (@fp_regs ?I0))
      |- runs_to _ (@mkst _ _ _ ?M1 _) _ =>
      lazymatch type of HADM with adm _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?R ?M0 =>
        assert (HADM1 : ADM I1 R1 M1);
        [ apply (adm_frame0I I0 I1 R R1 M0 M1 _ HADM Hfr);
          [ solve [unfold BIG0; solve_within]
          | solve [solve_apart]
          | regv HR (2%bv:reg); reflexivity
          | regv HR (3%bv:reg); reflexivity
          | regv HR (4%bv:reg); reflexivity
          | regv HR (8%bv:reg); reflexivity
          | exact (fregs_same_on E sfr0 sfr _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity)) ]
        | ]
      end
    end.

  Ltac w_lt :=
    rewrite ?uW;
    lazymatch goal with
    | |- (bb _ _ ?b ?i < _)%Z => pose proof (bb_range data bs b i); lia
    | |- _ => rewrite ?u_small by lia; lia
    end.
  Ltac flat_tac := unfold flat, estart; cbn [a_base a_off edenot];
    lazymatch goal with HK : know_ok _ ?E _ _ |- _ => ev_simpl E end; rewrite_getr; rewrite ?u_small_frame by lia; lia.
  Ltac kcellv b k n H :=
    lazymatch goal with HK : know_ok _ ?E ?M ?kn |- _ =>
      let r := eval vm_compute in (kread SEGS kn b k n) in
      lazymatch r with
      | Some ?v =>
        let KR := fresh "KR" in let Hfl := fresh "Hfl" in
        assert (KR : kread SEGS kn b k n = Some v) by (vm_compute; reflexivity);
        pose proof (kread_rdn SEGS E M kn b k n v HK KR ltac:(lia) ltac:(lia)) as H; clear KR;
        lazymatch type of H with ?FL -> _ => assert (Hfl : FL) by flat_tac; specialize (H Hfl); clear Hfl end;
        unfold adenot, v_addi in H; cbn [a_base a_off edenot] in H; ev_simpl_in E H; rewrite_getr_in H;
        rewrite ?u_small_frame in H by lia;
        rewrite ?ext_val_zx_id4 in H by w_lt;
        rewrite ?ext_val_zx_id1 in H by w_lt
      | _ => fail "kcellv: no knowledge at" b k n
      end
    end.

  (* [comment removed for export] *)
  Ltac fail_st HADM RS rsZ :=
    let Hfr := fresh "Hfr" in let HADM1 := fresh "HADMf" in
    frame_now HADM RS rsZ Hfr; adm_fr HADM Hfr HADM1;
    match goal with H : adm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => apply (failkI _ _ _ H) end.
  Ltac fail_st' HADM RS rsZ :=
    let Hfr := fresh "Hfr" in let HADM1 := fresh "HADMf" in
    frame_now HADM RS rsZ Hfr; adm_fr HADM Hfr HADM1;
    match goal with H : adm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      apply (failk'I _ _ _ H); lazymatch goal with HR : regs_ok _ _ _ |- _ => regv HR (23%bv:reg); reflexivity end end.
  Ltac fail0 HADM :=
    let HADM1 := fresh "HADMf" in adm_now HADM HADM1;
    match goal with H : adm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => apply (failkI _ _ _ H) end.
  Ltac in_kept := cbn; repeat (first [ left; reflexivity | right ]).
  Ltac offsets_cases Hin :=
    cbn [b2a_curve_offsets In] in Hin;
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]].
  (* [comment removed for export] *)



  (* [comment removed for export] *)
  Ltac kcells_tac C1 C2 C3 :=
    repeat apply Forall_cons; try apply Forall_nil;
    lazymatch goal with
    | |- kentry_ok _ ?E _ (KWord (SA (EVar 8%nat) 96%Z) 4%nat (ELit 3%Z)) =>
        eapply (kword_intro SEGS E _ (EVar 8) B 96 4 (ELit 3%Z) (Z_to_bv 64 3)); [cbn [edenot]; ev_simpl E; assumption | reflexivity | lia | lia | lia | lia | exact (proj2 C1)]
    | |- kentry_ok _ ?E _ (KWord (SA (EVar 8%nat) 396%Z) 4%nat (EVar ?v)) =>
        eapply (kword_intro SEGS E _ (EVar 8) B 396 4 (EVar v)); [cbn [edenot]; ev_simpl E; assumption | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | exact (proj2 C2)]
    | |- kentry_ok _ ?E _ (KWord (SA (EVar 8%nat) 100%Z) 4%nat (EVar ?v)) =>
        eapply (kword_intro SEGS E _ (EVar 8) B 100 4 (EVar v)); [cbn [edenot]; ev_simpl E; assumption | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | exact (proj2 C3)]
    | |- kentry_ok _ ?E _ (KRange _ _ _) => apply krange_intro; cbn [edenot]; ev_simpl E; rewrite ?uW; first [lia | rewrite u_small by lia; lia]
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma jseg : jseg_stmtI.
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch Hret HPRE Hcanon Hrc M3A.
    unfold jseg_stmt.
    intros FPI R M sz buf oc mc HADM HTAG Hsz HMC HC0 HSTK H16 H15 H18 H21 H22 H20 H25 H28 H29 H30 H31 H19 H24.
    adm_facts HADM. pose proof HMC as (C1 & C2 & C3 & Hoc & Hmc).
    pose proof pre_tagI as (Q1 & Q2 & Q3 & Q4). pose proof (u64_range T).
    pose proof HTAG as (T1 & T2 & T3 & T4 & T5a & T5b & T5c). pose proof (u64_range buf).
    pkg_ms HADM HTAG Hsz HSTK [Z_to_bv 64 oc; Z_to_bv 64 mc]
      [KWord (SA (EVar 8) 96) 4 (ELit 3); KWord (SA (EVar 8) 396) 4 (EVar 105); KRange (EVar 105) 3 4;
       KWord (SA (EVar 8) 100) 4 (EVar 106)]
      ltac:(kcells_tac C1 C2 C3).
    pin_var HR (16%bv:reg) H16 103%nat. pin_var HR (15%bv:reg) H15 100%nat. pin_var HR (18%bv:reg) H18 99%nat.
    pin_var HR (21%bv:reg) H21 98%nat. pin_var HR (22%bv:reg) H22 102%nat. pin_var HR (20%bv:reg) H20 104%nat.
    pin_sh HR (25%bv:reg) H25 8%nat A8 B 396%Z 49%Z.
    pin_add HR (28%bv:reg) H28 81%nat A8 16%Z. pin_sh HR (29%bv:reg) H29 81%nat A8 T 16%Z 2%Z.
    pin_sh HR (30%bv:reg) H30 81%nat A8 T 8%Z 1%Z. pin_add HR (31%bv:reg) H31 8%nat A8 96%Z.
    pin_add HR (19%bv:reg) H19 81%nat A8 8%Z. pin_lit HR (24%bv:reg) H24.
    run_fp 60%nat [0x85fec%Z; 0x8822c%Z; 0x85e60%Z] noscr true.
    branch_case as Ha0.
    - (* [comment removed for export] *)
      run_fp 10%nat [0x85fec%Z; 0x8822c%Z; 0x85e60%Z] noscr true.
      branch_case as Hcl; [fail0 HADM|].
      run_fp 30%nat [0x85fec%Z; 0x8822c%Z; 0x85e60%Z] noscr true.
      branch_case as Hio; [fail0 HADM|].
      hc_lin Hio.
      run_fp 20%nat [0x85fec%Z; 0x8822c%Z; 0x85e60%Z] noscr true.
      (* [comment removed for export] *)
      frame_now HADM [(SA (EVar 8) 396, 4%Z)] [(Z_to_bv 64 (a + 396), 4%Z)] Hfr.
      adm_fr HADM Hfr HADM1.
      lazymatch goal with |- runs_to _ (@mkst _ _ _ ?M1 _) _ => remember M1 as Mz eqn:HMz; clear HMz end.
      pose proof pre_factsI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10 & P11 & P12 & _). app_facts.
      assert (HC0' : curves0I Mz).
      { eapply curves0_frameI; [exact HC0 | exact Hfr |].
        unfold b2a_curve_offsets. repeat (apply Forall_cons; [solve_apart|]). apply Forall_nil. }
      apply (in0I _ _ _ 3%Z mc 0%Z HADM1); [| creg (24%bv:reg)].
      kcellv (EVar 8) 96%Z 4%nat C96. kcellv (EVar 8) 100%Z 4%nat C100. kcellv (EVar 8) 396%Z 4%nat C396.
      split; [split; [lia | exact C96]|].
      split; [split; [lia | exact C100]|].
      split; [split; [lia | exact C396]|].
      split; [lia|]. split; [exact Hmc|]. split; [lia|].
      exact HC0'.
    - (* [comment removed for export] *)
      run_fp 10%nat [0x85fec%Z; 0x8822c%Z; 0x85e60%Z] noscr true.
      branch_case as Hcl; [fail0 HADM|].
      run_fp 60%nat [0x85fec%Z; 0x8822c%Z; 0x85e60%Z] noscr true.
      adm_now HADM HADM1.
      eapply rt_call.
      { eapply (Hrc data len bs (Z_to_bv 64 (spv - 240)) buf (Z_to_bv 64 (a + 248)) sz _ oc _ _ _ rom (Z_to_bv 64 0x867dc)).
        - regv HR (1%bv:reg). reflexivity.
        - apply ret_ok_even. rewrite u_small by lia. reflexivity.
        - eapply (rc_pre_atI _ _ _ 0x6d424120%Z sz buf (a + 248)%Z oc);
            [ exact HADM1 | exact HTAG | lia | lia | lia | apply mod8_add; [exact P2 | reflexivity]
            | intros _; exists 248%Z; split; [reflexivity | right; right; reflexivity]
            | regv HR (10%bv:reg); reflexivity
            | regv HR (11%bv:reg); reflexivity
            | reflexivity
            | regv HR (13%bv:reg); reflexivity
            | regv_lin HR (14%bv:reg); rewrite A8; f_equal; lia ].
      }
      cbv beta. intros FPI' R' M' (Hkeep & Hfkeep & Hpost).
      unfold rcurves_post_bo in Hpost. cbv zeta in Hpost. change RCURVES_DB with 2304%Z in Hpost.
      rewrite (u_small (spv - 240)), (u_small (a + 248)) in Hpost by lia.
      destruct Hpost as (Hfr & r & H10' & Hr01 & Hcv).
      destruct (adm_rcI _ FPI' _ R' _ M' (a + 248)%Z oc HADM1 ltac:(lia) ltac:(lia) ltac:(lia) Hfr Hkeep Hfkeep) as (HADM' & HT' & HS').
      pose proof pre_factsI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10 & P11 & P12 & _). app_facts.
      apply (M3A FPI' R' M' sz buf oc mc r HADM' (HT' _ _ _ HTAG) Hsz).
      + eapply mab_cells_frameI; [exact HMC | exact Hfr | solve_apart | solve_apart].
      + apply HS'. exact HSTK.
      + exact H10'.
      + destruct Hr01 as [-> | ->]; [left; reflexivity | right; split; [reflexivity|]].
        eapply (curves10_rcI M M' 248%Z oc HC0); [ exact Hfr | lia | lia | lia | | ].
        * intros i Hi. apply Hcv; [reflexivity | exact Hi].
        * intros o Hin. offsets_cases Hin;
            first [ left; lia
                  | right; exists 0%Z; lia
                  | right; exists 1%Z; lia
                  | right; exists 2%Z; lia
                  | destruct (Z_lt_le_dec 3 oc); [right; exists 3%Z; lia | left; lia] ].
      + kreg Hkeep (9%bv:reg).
      + kreg Hkeep (18%bv:reg).
      + kreg Hkeep (21%bv:reg).
      + kreg Hkeep (20%bv:reg).
      + kreg Hkeep (25%bv:reg).
      + kreg Hkeep (19%bv:reg).
      + kreg Hkeep (24%bv:reg).
  Qed.
End REB.
