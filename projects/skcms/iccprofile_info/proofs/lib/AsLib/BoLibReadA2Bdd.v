(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.H Require GcFlushY04.  (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Import AsanUbsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs LibFrame LibWP2Spec LibWP2Lib.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs BoBase AsRtSpec AsLibFrame AsLibEnv AsLibTagsLib AsLibFPSpec AsLibWP2Spec AsLibCurveSpec AsLibBswap BoLibSpec BoLibReadA2Ba BoLibReadA2Bb BoLibReadA2Bc BoLibReadA2Bs BoLibReadA2Bd BoLibReadA2Bd1 BoLibReadA2Bd2 BoLibReadA2Bd3 AsLibPlace.
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


Section RD2.
  Variable ceil : Z.
  Variables (FPI0 : FPState) (regs0 : bvmap 5 word) (mem0 rom : word -> option byte) (ret : word).
  Variables (data : word) (len : Z) (bs : list byte) (sp T A : word) (pcs : Z) (fs : Z) (ch : chain).
  Hypothesis Hra : getr regs0 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis HPRE : a2b_pre_bo SEGS as_both ceil data len bs sp T A pcs fs ch FPI0 regs0 mem0.
  Hypothesis Hcanon : canonicalize_contract_as SEGS as_both ceil.
  Hypothesis Hrc : read_curves_contract_bo SEGS as_both ceil.

  #[local] Abbreviation a := (bv_unsigned A).
  #[local] Abbreviation spv := (bv_unsigned sp).
  #[local] Abbreviation t := (bv_unsigned T).
  #[local] Abbreviation eobw := (Z_to_bv 64 (bv_unsigned data + len)).
  #[local] Abbreviation ADM := (adm ceil FPI0 regs0 mem0 ret data len bs sp T A fs ch).
  #[local] Abbreviation QP := (Qpost FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch).
  #[local] Abbreviation TAGC := (tagc data len T).
  #[local] Abbreviation curves0I := (curves0 data len A).
  #[local] Abbreviation stkI := (stk data len bs sp T A).
  #[local] Abbreviation WI := (W data bs).
  #[local] Abbreviation bbI := (bb data bs).
  #[local] Abbreviation pre_factsI := (pre_facts ceil FPI0 regs0 mem0 data len bs sp T A pcs fs ch HPRE).
  #[local] Abbreviation pre_tagI := (pre_tag ceil FPI0 regs0 mem0 data len bs sp T A pcs fs ch HPRE).
  #[local] Abbreviation kn_adm_okI := (kn_adm_ok ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch HPRE).
  #[local] Abbreviation kn_end_okI := (kn_end_ok ceil FPI0 regs0 mem0 ret data len bs sp T A pcs fs ch HPRE).
  #[local] Abbreviation kn_tag_okI := (kn_tag_ok ceil FPI0 regs0 mem0 ret data len bs sp T A pcs fs ch HPRE).
  #[local] Abbreviation kn_m_okI := (kn_m_ok ceil FPI0 regs0 mem0 ret data len bs sp T A pcs fs ch HPRE).
  #[local] Abbreviation adm_frame0I := (adm_frame0 ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch HPRE).
  #[local] Abbreviation failkI := (failk ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch Hret HPRE).
  #[local] Abbreviation failk'I := (failk' ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch Hret HPRE).
  #[local] Abbreviation tagc_frameI := (tagc_frame ceil FPI0 regs0 mem0 data len bs sp T A pcs fs ch HPRE).
  #[local] Abbreviation curves0_frameI := (curves0_frame ceil FPI0 regs0 mem0 data len bs sp T A pcs fs ch HPRE).
  #[local] Abbreviation rc_pre_atI := (rc_pre_at ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch HPRE).
  #[local] Abbreviation adm_rcI := (adm_rc ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch HPRE).
  #[local] Abbreviation curves0_rcI := (curves0_rc ceil FPI0 regs0 mem0 data len bs sp T A pcs fs ch HPRE).

  #[local] Abbreviation mab_cellsI := (mab_cells A).
  #[local] Abbreviation le4wI := (le4w data bs).
  #[local] Abbreviation be4I := (be4 data bs).
  #[local] Abbreviation kn_ms_okI := (kn_ms_ok ceil FPI0 regs0 mem0 ret data len bs sp T A pcs fs ch HPRE).
  #[local] Abbreviation stk_frameI := (stk_frame ceil FPI0 regs0 mem0 data len bs sp T A pcs fs ch HPRE).
  #[local] Abbreviation mab_cells_frameI := (mab_cells_frame ceil FPI0 regs0 mem0 data len bs sp T A pcs fs ch HPRE).
  #[local] Abbreviation m1_stmtI := (m1_stmt ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch).

  #[local] Abbreviation jseg_stmtI := (jseg_stmt ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch).
  #[local] Abbreviation curves10I := (curves10 data len A).
  #[local] Abbreviation in0I := (in0 ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch Hret HPRE Hcanon).
  #[local] Abbreviation curves10_rcI := (curves10_rc ceil FPI0 regs0 mem0 data len bs sp T A pcs fs ch HPRE).

  #[local] Abbreviation base_valsI := (base_vals regs0 ret data len).
  #[local] Abbreviation m3a_stmtI := (m3a_stmt ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch).

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
    cbn [a2b_curve_offsets In] in Hin;
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]].
  (* [comment removed for export] *)




  #[local] Abbreviation curves10_frameI := (curves0_frame ceil FPI0 regs0 mem0 data len bs sp T A pcs fs ch HPRE).

  #[local] Abbreviation gsl := (BoLibReadA2Bd.gsl data bs).
  #[local] Abbreviation Pval := (BoLibReadA2Bd.Pval data bs).
  #[local] Abbreviation gsl_bnd := (BoLibReadA2Bd.gsl_bnd data bs).
  #[local] Abbreviation Pval_bnd := (BoLibReadA2Bd.Pval_bnd data bs).
  #[local] Abbreviation curves10_frame1 := (BoLibReadA2Bd.curves10_frame1 ceil FPI0 regs0 mem0 data len bs sp T A pcs fs ch HPRE).
  #[local] Abbreviation vals_m3 := (BoLibReadA2Bd.vals_m3 data bs).
  #[local] Abbreviation kn_m3_ok := (BoLibReadA2Bd.kn_m3_ok ceil FPI0 regs0 mem0 ret data len bs sp T A pcs fs ch HPRE).
  #[local] Abbreviation m3b_stmtI := (m3b_stmt ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch).

  (* [comment removed for export] *)
  Ltac pkg_m3 HADM HTAG Hsz HSTK HMC Hco Hco20 Hn n :=
    lazymatch type of HTAG with tagc _ _ _ _ ?sz ?buf _ =>
    lazymatch type of HMC with mab_cells _ ?ic ?mc _ =>
    lazymatch type of Hco with (0 <= ?co < _)%Z =>
      pkg_ms HADM HTAG Hsz HSTK (vals_m3 buf co mc n) (kn_m3 (Z.of_nat n))
        ltac:(exact (kn_m3_ok _ _ _ sz buf ic mc co n HADM HTAG HMC Hco Hco20 Hn));
      match goal with Edef := Env _ _ |- _ => cbv beta delta [vals_m3 app] in Edef end
    end end end.

  Ltac m3b_intro :=
    intros FPI R M sz buf ic mc co HADM HTAG Hsz HMC HC10 HSTK Hco Hco20 Hn H14 H12 H10 H18 H19 H20 H21 H22 H23 H25 H24;
    adm_facts HADM; pose proof HMC as (C1 & C2 & C3 & Hic & Hmc);
    pose proof pre_tagI as (Q1 & Q2 & Q3 & Q4); pose proof (u64_range T);
    pose proof HTAG as (T1 & T2 & T3 & T4 & T5a & T5b & T5c); pose proof (u64_range buf);
    pose proof (bb_range data bs buf (co+16)) as R16.

  Ltac m3b_pins H14 H12 H10 H18 H19 H20 H21 H22 H23 H25 H24 :=
    lazymatch goal with HR : regs_ok ?E _ _, A8 : getr _ 8 = A |- _ =>
      pin_var HR (14%bv:reg) H14 105%nat;
      pin_reg HR (12%bv:reg) (EAlu ALU_ADD (EVar 111) (ELit 20)) by (cbn [edenot]; ev_simpl E; rewrite H12; apply bv_eq; rewrite u_add64, !u_small by lia; rewrite Z.mod_small by lia; reflexivity);
      pin_var HR (10%bv:reg) H10 80%nat; pin_var HR (18%bv:reg) H18 104%nat;
      pin_add HR (19%bv:reg) H19 81%nat A8 8%Z; pin_add HR (20%bv:reg) H20 81%nat A8 16%Z;
      pin_sh HR (21%bv:reg) H21 81%nat A8 T 16%Z 2%Z; pin_sh HR (22%bv:reg) H22 81%nat A8 T 8%Z 1%Z;
      pin_add HR (23%bv:reg) H23 8%nat A8 300%Z; pin_sh HR (25%bv:reg) H25 8%nat A8 A 300%Z 37%Z;
      pin_lit HR (24%bv:reg) H24
    end.

  Ltac mods_goal :=
    repeat match goal with |- context [ (?x mod ?m)%Z ] =>
      lazymatch x with context [ (_ mod _)%Z ] => fail | _ => rewrite (Z.mod_small x m) by lia end end.

  (* [comment removed for export] *)
  Ltac wle := lazymatch goal with |- (bv_unsigned (W _ _ ?b ?i) <= _)%Z => pose proof (bb_range data bs b i); rewrite uW; lia end.

  (* [comment removed for export] *)
  Ltac pin_P n :=
    lazymatch goal with HR : regs_ok ?E _ _ |- _ =>
      pin_reg HR (15%bv:reg) (EVar 113) by
        (regv HR (15%bv:reg); cbn [edenot]; ev_simpl E; apply bv_eq;
         lazymatch goal with
         | |- bv_unsigned (mul_div M_MUL (Z_to_bv 64 3) ?bw) = _ =>
             rewrite (proj1 (uP0 bw ltac:(wle)))
         | |- bv_unsigned (mul_div M_MUL (mul_div M_MUL (Z_to_bv 64 3) ?bw) ?g0) = _ =>
             rewrite (proj1 (uP1 bw g0 ltac:(wle) ltac:(wle)))
         | |- bv_unsigned (mul_div M_MUL (mul_div M_MUL (mul_div M_MUL (Z_to_bv 64 3) ?bw) ?g0) ?g1) = _ =>
             rewrite (proj1 (uP2 bw g0 g1 ltac:(wle) ltac:(wle) ltac:(wle)))
         | |- bv_unsigned (mul_div M_MUL (mul_div M_MUL (mul_div M_MUL (mul_div M_MUL (Z_to_bv 64 3) ?bw) ?g0) ?g1) ?g2) = _ =>
             rewrite (proj1 (uP3 bw g0 g1 g2 ltac:(wle) ltac:(wle) ltac:(wle) ltac:(wle)))
         | |- bv_unsigned (mul_div M_MUL (mul_div M_MUL (mul_div M_MUL (mul_div M_MUL (mul_div M_MUL (Z_to_bv 64 3) ?bw) ?g0) ?g1) ?g2) ?g3) = _ =>
             rewrite (proj1 (uP4 bw g0 g1 g2 g3 ltac:(wle) ltac:(wle) ltac:(wle) ltac:(wle) ltac:(wle)))
         | |- ?G => idtac "pin_P: unexpected" G; fail
         end;
         rewrite !uW;
         lazymatch goal with |- _ = bv_unsigned (Z_to_bv 64 (Pval ?b ?c ?k)) =>
           rewrite (u_small (Pval b c k)) by (pose proof (Pval_bnd b c k ltac:(cbn; lia)); lia) end;
         unfold Pval, gsl; cbn [firstn zprod]; lia)
    end.

  (* [comment removed for export] *)
  Ltac pin_slack :=
    lazymatch goal with HR : regs_ok ?E _ _ |- _ =>
      pin_reg HR (10%bv:reg) (EVar 110) by
        (regv HR (10%bv:reg); cbn [edenot]; ev_simpl E; first [apply slack_val; rewrite uW; lia | match goal with |- ?G => idtac "pin_slack: unexpected" G; fail end])
    end.

  (* [comment removed for export] *)
  Ltac frame_g HADM Hfr := frame_now HADM [(SA (EVar 8) 128, 24%Z)] [(Z_to_bv 64 (a + 128), 24%Z)] Hfr.
  Ltac fail_g HADM :=
    let Hfr := fresh "Hfr" in let HADM1 := fresh "HADMf" in
    frame_g HADM Hfr; adm_fr HADM Hfr HADM1;
    match goal with H : adm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => apply (failkI _ _ _ H) end.

  (* [comment removed for export] *)
  Ltac m3_loop k HADM :=
    lazymatch k with
    | O => idtac
    | S ?k' =>
        run_fp 80%nat [0x84598%Z; 0x84f98%Z] noscr true;
        let H := fresh "Hg" in
        branch_case as H; [ fail_g HADM | hc_lin H; m3_loop k' HADM ]
    end.

  (* [comment removed for export] *)
  Ltac m3_success n HADM HTAG HMC HC10 Hco Hn :=
    lazymatch goal with Heob : branch_taken _ _ _ = true |- _ =>
    lazymatch type of HTAG with tagc _ _ _ _ ?sz ?buf _ =>
    lazymatch type of Hco with (0 <= ?co < _)%Z =>
    lazymatch type of HMC with mab_cells _ ?ic ?mc _ =>
      pose proof (zprod_bnd _ (gsl_bnd buf co n)) as HZb;
      hc_lin Heob;
      let Hfr := fresh "Hfr" in let HADMs := fresh "HADMs" in
      frame_g HADM Hfr; adm_fr HADM Hfr HADMs;
      lazymatch goal with |- runs_to _ (@mkst _ _ _ ?M1 _) _ => remember M1 as Mz eqn:HMz; clear HMz end;
      eapply (in0I _ _ _ ic mc);
        [exact HADMs | | lazymatch goal with HR : regs_ok _ _ _ |- _ => regv HR (24%bv:reg); reflexivity end];
      let C144 := fresh "C144" in let C300 := fresh "C300" in let C296 := fresh "C296" in
      let C128 := fresh "C128" in let C136 := fresh "C136" in
      kcellv (EVar 8) 144%Z 4%nat C144; kcellv (EVar 8) 300%Z 4%nat C300; kcellv (EVar 8) 296%Z 4%nat C296;
      kcellv (EVar 8) 128%Z 8%nat C128; kcellv (EVar 8) 136%Z 8%nat C136;
      split; [split; [lia | rewrite Hn; exact C144]|];
      split; [split; [lia | exact C296]|];
      split; [split; [lia | exact C300]|];
      split; [lia|]; split; [assumption|];
      split; [eapply curves10_frame1; [exact HC10 | exact Hfr | intros o Ho; pose proof (offsets_bound o Ho);
              rewrite u_small_frame by lia; lia]|];
      lazymatch type of C128 with _ = Some (word_to_le_bytes 8 ?g8) =>
      lazymatch type of C136 with _ = Some (word_to_le_bytes 8 ?g16) =>
        exists ic, 3%Z, (gsl buf co n), g8, g16 end end;
      split; [split; [lia | rewrite Hn; exact C144]|];
      split; [split; [lia | exact C300]|];
      split; [lia|];
      split; [rewrite Hn; unfold gsl; rewrite length_firstn; cbn; lia|];
      split; [unfold gsl; cbn [firstn]; repeat apply Forall_cons; try apply Forall_nil;
              match goal with |- (2 <= bb _ _ ?b ?i <= 255)%Z => pose proof (bb_range data bs b i); lia end|];
      split; [intros i Hi; rewrite Hn in Hi; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hi;
              first [ exfalso; lia
                    | let Hi' := fresh in
                      assert (Hi' : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3)%Z) by lia;
                      let G := fresh "G" in
                      destruct Hi' as [-> |[-> |[-> | ->]]];
                      [ kcellv (EVar 8) 148%Z 1%nat G; replace (a + 148 + 0)%Z with (a + 148)%Z by lia
                      | first [ exfalso; lia | kcellv (EVar 8) 149%Z 1%nat G; replace (a + 148 + 1)%Z with (a + 149)%Z by lia ]
                      | first [ exfalso; lia | kcellv (EVar 8) 150%Z 1%nat G; replace (a + 148 + 2)%Z with (a + 150)%Z by lia ]
                      | first [ exfalso; lia | kcellv (EVar 8) 151%Z 1%nat G; replace (a + 148 + 3)%Z with (a + 151)%Z by lia ] ];
                      unfold gsl; cbn [firstn]; unfold Z.to_nat, Pos.to_nat; cbn [Pos.iter_op Nat.add nth];
                      (split; [ match goal with |- (0 <= bb _ _ ?b ?i' < 256)%Z => apply bb_range end
                              | unfold W in G; exact G ]) ]|];
      split; [exact C128|]; split; [exact C136|]; split; [reflexivity|];
      intros _; unfold inDATA; unfold Pval in Heob;
      split; intros Hnz;
        first [ exfalso; apply Hnz; rewrite u_lit64a; reflexivity
              | rewrite ?u_add64, ?u_lit64a; mods_goal; lia ]
    end end end end.

  (* [comment removed for export] *)
  Ltac m3_rest n HADM HTAG HMC HC10 Hco Hn :=
    lazymatch type of HTAG with tagc _ _ _ _ ?sz ?buf _ =>
    lazymatch type of Hco with (0 <= ?co < _)%Z =>
    pose proof (Pval_bnd buf co n ltac:(cbn; lia)) as HPb;
    m3_loop n HADM;
    run_fp 80%nat [0x84598%Z; 0x84f98%Z] noscr true;
    (* [comment removed for export] *)
    lazymatch n with
    | 4%nat => let H := fresh "Hmx" in branch_case as H; [ fail_g HADM | ]  (* [comment removed for export] *)
    | _ => idtac
    end;
    pin_P n;
    run_fp 80%nat [0x84598%Z; 0x84fe0%Z] noscr true;
    let Hs := fresh "Hszc" in
    branch_case as Hs; [ fail_g HADM |];
    run_fp 80%nat [0x84598%Z; 0x84fe0%Z] noscr true;
    pin_slack;
    (* [comment removed for export] *)
    run_fp 10%nat [0x84ff0%Z] noscr true;
    lazymatch goal with HR : regs_ok ?E _ _ |- _ =>
      pin_reg HR (12%bv:reg) (EVar 114) by (regv_lin HR (12%bv:reg); cbn [edenot]; ev_simpl E; rewrite !u_small by lia; f_equal; lia) end;
    run_fp 5%nat [0x84ff8%Z] (dirs [false]) true;
    lazymatch goal with HR : regs_ok ?E _ _ |- _ =>
      pin_reg HR (11%bv:reg) (ELit 1%Z) by (regv HR (11%bv:reg); cbn [edenot]; ev_simpl E; apply sltu_0_pos; lia) end;
    run_fp 3%nat [0x84ffc%Z] noscr true;
    lazymatch goal with HR : regs_ok ?E _ _ |- _ =>
      pin_reg HR (13%bv:reg) (ELit 0%Z) by (regv HR (13%bv:reg); cbn [edenot]; ev_simpl E; apply sltiu_ge1; rewrite u_small by lia; lia) end;
    run_fp 5%nat [0x85008%Z] noscr true;
    run_fp 3%nat [0x85010%Z] (dirs [false]) true;
    lazymatch goal with HR : regs_ok ?E _ _ |- _ =>
      pin_reg HR (12%bv:reg) (ELit 0%Z) by (regv HR (12%bv:reg); cbn [edenot]; ev_simpl E; apply sltiu_ge1;
        rewrite u_add64, uW, u_small by lia; pose proof (bb_range data bs buf (co + 16)); rewrite Z.mod_small by lia; lia) end;
    run_fp 10%nat [0x84598%Z; 0x84408%Z] noscr true;
    let Heob := fresh "Heob" in
    branch_case as Heob; [ m3_success n HADM HTAG HMC HC10 Hco Hn | run_fp 10%nat [0x84598%Z] noscr true; fail_g HADM ]
    end end.

  (* [comment removed for export] *)
  Ltac m3_open n HADM HTAG Hsz HSTK HMC Hco Hco20 Hn H14 H12 H10 H18 H19 H20 H21 H22 H23 H25 H24 :=
    pkg_m3 HADM HTAG Hsz HSTK HMC Hco Hco20 Hn n;
    m3b_pins H14 H12 H10 H18 H19 H20 H21 H22 H23 H25 H24;
    run_fp 100%nat [0x84598%Z; 0x84f1c%Z; 0x84f98%Z] (dirs [false]) true.

  Lemma m3b4 : m3b_stmtI 4.
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch Hret HPRE Hcanon.
    unfold m3b_stmt. m3b_intro. m3_open 4%nat HADM HTAG Hsz HSTK HMC Hco Hco20 Hn H14 H12 H10 H18 H19 H20 H21 H22 H23 H25 H24.
    branch_case as Hbw2.
    - hc_lin Hbw2. m3_rest 4%nat HADM HTAG HMC HC10 Hco Hn.
    - hc_lin Hbw2. run_fp 30%nat [0x84598%Z; 0x84f1c%Z; 0x84f98%Z] noscr true.
      branch_case as Hbw1; [ fail0 HADM |]. hc_lin Hbw1. m3_rest 4%nat HADM HTAG HMC HC10 Hco Hn.
  Qed.


  #[local] Abbreviation m3b0I := (m3b0 ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch Hret HPRE Hcanon).
  #[local] Abbreviation m3b1I := (m3b1 ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch Hret HPRE Hcanon).
  #[local] Abbreviation m3b2I := (m3b2 ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch Hret HPRE Hcanon).
  #[local] Abbreviation m3b3I := (m3b3 ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch Hret HPRE Hcanon).

  Lemma m3b : forall (FPI : FPState) R M sz buf ic mc co,
    ADM FPI R M -> TAGC 0x6d414220 sz buf M -> (32 <= sz)%Z -> mab_cellsI ic mc M -> curves10I M -> stkI buf M ->
    (0 <= co < 4294967296)%Z -> (co + 20 <= sz)%Z ->
    getr R 14 = Z_to_bv 64 (bv_unsigned buf + co) -> getr R 12 = Z_to_bv 64 (co + 20) -> getr R 10 = buf ->
    getr R 18 = eobw -> getr R 19 = Z_to_bv 64 (t + 8) -> getr R 20 = Z_to_bv 64 (t + 16) ->
    getr R 21 = Z_to_bv 64 (SB + (t + 16) / 8) -> getr R 22 = Z_to_bv 64 (SB + (t + 8) / 8) ->
    getr R 23 = Z_to_bv 64 (a + 300) -> getr R 25 = Z_to_bv 64 (SB + (a + 300) / 8) -> getr R 24 = Z_to_bv 64 SB ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x84df0) M rom) QP.
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch Hret HPRE Hcanon.
    intros FPI R M sz buf ic mc co HADM HTAG Hsz HMC HC10 HSTK Hco Hco20 H14 H12 H10 H18 H19 H20 H21 H22 H23 H25 H24.
    pose proof HMC as (_ & _ & _ & Hic & _).
    assert (H5 : ic = Z.of_nat 0 \/ ic = Z.of_nat 1 \/ ic = Z.of_nat 2 \/ ic = Z.of_nat 3 \/ ic = Z.of_nat 4) by (cbn; lia).
    destruct H5 as [Hn|[Hn|[Hn|[Hn|Hn]]]];
      [ eapply m3b0I | eapply m3b1I | eapply m3b2I | eapply m3b3I | eapply m3b4 ]; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma m3a : m3a_stmtI.
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch Hret HPRE Hcanon.
    unfold m3a_stmt.
    intros FPI R M sz buf ic mc r HADM HTAG Hsz HMC HSTK H10 Hr H9 H18 H21 H25 H26 H19 H24.
    adm_facts HADM. pose proof HMC as (C1 & C2 & C3 & Hic & Hmc).
    pose proof pre_tagI as (Q1 & Q2 & Q3 & Q4). pose proof (u64_range T).
    pose proof HTAG as (T1 & T2 & T3 & T4 & T5a & T5b & T5c). pose proof (u64_range buf).
    pose proof (bb_range data bs buf 24) as R24. pose proof (bb_range data bs buf 25) as R25.
    pose proof (bb_range data bs buf 26) as R26. pose proof (bb_range data bs buf 27) as R27.
    destruct Hr as [-> | [-> HC10]].
    - pkg_m HADM HTAG Hsz (@nil word) (@nil kentry) ltac:(constructor).
      pin_lit HR (10%bv:reg) H10.
      run_fp 10%nat [0x84598%Z] noscr true. fail0 HADM.
    - pose proof (be4_range data bs buf 24) as Hco.
      pkg_ms HADM HTAG Hsz HSTK [Z_to_bv 64 (be4I buf 24)] [KRange (EVar 105) 0 4294967295]
        ltac:(constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia | constructor]).
      pin_lit HR (10%bv:reg) H10.
      pin_reg HR (9%bv:reg) (LE4 96) by (cbn [edenot]; ev_simpl E; rewrite H9; reflexivity).
      pin_var HR (18%bv:reg) H18 104%nat. pin_var HR (21%bv:reg) H21 96%nat. pin_var HR (25%bv:reg) H25 99%nat.
      pin_var HR (26%bv:reg) H26 98%nat. pin_add HR (19%bv:reg) H19 81%nat A8 8%Z.
      pin_lit HR (24%bv:reg) H24.
      run_fp 40%nat [0x84598%Z; 0x84dc0%Z] noscr true.
      (* [comment removed for export] *)
      assert (Hbe : be4I buf 24 = (bbI buf 27 + 256 * bbI buf 26 + 65536 * bbI buf 25 + 16777216 * bbI buf 24)%Z) by reflexivity.
      set (nu := fun k : nat => nth k [bbI buf 24; bbI buf 25; bbI buf 26; bbI buf 27] 0%Z).
      assert (nu_range : forall k, (0 <= nu k < 256)%Z).
      { intros k. unfold nu. destruct k as [|[|[|[|k]]]]; cbn [nth]; try lia. destruct k; cbn; lia. }
      set (atoms := [(EVar 96, (false, 0%nat)); (EVar 97, (false, 1%nat)); (EVar 98, (false, 2%nat)); (EVar 99, (false, 3%nat))]).
      assert (Hat : atoms_ok E nu atoms).
      { unfold atoms, atoms_ok. repeat apply Forall_cons; try apply Forall_nil;
          unfold atom_ok; cbn [edenot]; ev_simpl E; rewrite uW; reflexivity. }
      pin_reg HR (10%bv:reg) (EVar 105) by
        (rewrite (HR (10%bv:reg));
         lazymatch goal with |- edenot _ ?e = _ =>
           apply bv_eq; rewrite (beval_bytes E nu nu_range atoms e [3; 2; 1; 0]%nat Hat ltac:(cbn; lia) ltac:(vm_compute; reflexivity))
         end;
         cbn [edenot]; ev_simpl E; rewrite u_small by lia; rewrite Hbe; unfold nu; cbn [bytes_val nth]; lia).
      run_fp 30%nat [0x84598%Z; 0x84df0%Z] noscr true.
      branch_case as Hco20b.
      { adm_now HADM HADM1. apply (failkI _ _ _ HADM1). }
      hc_lin Hco20b.
      run_fp 30%nat [0x84598%Z; 0x84df0%Z] noscr true.
      adm_now HADM HADM1.
      apply (m3b _ _ _ sz buf ic mc (be4I buf 24) HADM1 HTAG Hsz HMC HC10 HSTK Hco ltac:(lia)).
      + regv_lin HR (14%bv:reg). rewrite u_small by lia. f_equal. lia.
      + regv_lin HR (12%bv:reg). rewrite u_small by lia. f_equal. lia.
      + creg (10%bv:reg).
      + creg (18%bv:reg).
      + creg (19%bv:reg).
      + creg (20%bv:reg).
      + creg (21%bv:reg).
      + creg (22%bv:reg).
      + creg (23%bv:reg).
      + creg (25%bv:reg).
      + creg (24%bv:reg).
  Qed.
End RD2.
