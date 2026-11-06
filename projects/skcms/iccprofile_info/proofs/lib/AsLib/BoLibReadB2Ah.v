(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Import AsanUbsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs LibFrame LibWP2Spec LibWP2Lib.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs BoBase BoLibDefs AsRtSpec AsLibFrame AsLibEnv AsLibTagsLib AsLibFPSpec AsLibWP2Spec AsLibCurveSpec BoLibReadA2Ba BoLibReadA2Bb BoLibReadA2Bh BoLibSpec BoLibReadB2Aa BoLibReadB2Ab BoLibReadB2Ac BoLibReadB2As BoLibReadB2Ag BoLibReadB2Af BoLibReadB2Ae BoLibReadB2Ad BoLibReadB2Add AsLibPlace.
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

Section RHB.
  Variable ceil : Z.
  Variables (FPI0 : FPState) (regs0 : bvmap 5 word) (mem0 rom : word -> option byte) (ret : word).
  Variables (data : word) (len : Z) (bs : list byte) (sp T B : word) (pcs : Z) (fs : Z) (ch : chain).
  Hypothesis Hra : getr regs0 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis HPRE : b2a_pre_bo SEGS as_both ceil data len bs sp T B pcs fs ch FPI0 regs0 mem0.
  Hypothesis Hcanon : canonicalize_contract_as SEGS as_both ceil.
  Hypothesis Hmftc : read_mft_common_b2a_contract_as SEGS as_both ceil.
  Hypothesis Hitab : init_tables_b2a_contract_as SEGS as_both ceil.
  Hypothesis Hrc : read_curves_contract_bo SEGS as_both ceil.

  #[local] Abbreviation a := (bv_unsigned B).
  #[local] Abbreviation spv := (bv_unsigned sp).
  #[local] Abbreviation t := (bv_unsigned T).
  #[local] Abbreviation eobw := (Z_to_bv 64 (bv_unsigned data + len)).
  #[local] Abbreviation ADM := (adm ceil FPI0 regs0 mem0 ret data len bs sp T B fs ch).
  #[local] Abbreviation QP := (Qpost FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch).
  #[local] Abbreviation CI := (chain_inv data len B).
  #[local] Abbreviation TAGC := (tagc data len T).
  #[local] Abbreviation curves0I := (curves0 data len B).
  #[local] Abbreviation pre_factsI := (pre_facts ceil FPI0 regs0 mem0 data len bs sp T B pcs fs ch HPRE).
  #[local] Abbreviation pre_tagI := (pre_tag ceil FPI0 regs0 mem0 data len bs sp T B pcs fs ch HPRE).
  #[local] Abbreviation pre_spI := (pre_sp ceil FPI0 regs0 mem0 data len bs sp T B pcs fs ch HPRE).
  #[local] Abbreviation kn_adm_okI := (kn_adm_ok ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch HPRE).
  #[local] Abbreviation kn_end_okI := (kn_end_ok ceil FPI0 regs0 mem0 ret data len bs sp T B pcs fs ch HPRE).
  #[local] Abbreviation kn_tag_okI := (kn_tag_ok ceil FPI0 regs0 mem0 ret data len bs sp T B pcs fs ch HPRE).
  #[local] Abbreviation adm_frame0I := (adm_frame0 ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch HPRE).
  #[local] Abbreviation failkI := (failk ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch Hret HPRE).
  #[local] Abbreviation okkI := (okk ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch Hret HPRE Hcanon).
  #[local] Abbreviation f1I := (f1 ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch Hret HPRE Hcanon Hitab).
  #[local] Abbreviation f2I := (f2 ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch Hret HPRE Hcanon Hitab).
  #[local] Abbreviation f1bI := (f1b ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch Hret HPRE Hcanon).
  #[local] Abbreviation f2bI := (f2b ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch Hret HPRE Hcanon).
  #[local] Abbreviation mftc_pre_atI := (mftc_pre_at ceil FPI0 regs0 mem0 ret data len bs sp T B pcs fs ch HPRE).
  #[local] Abbreviation adm_mftcI := (adm_mftc ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch HPRE).
  #[local] Abbreviation curves0_frameI := (curves0_frame ceil FPI0 regs0 mem0 data len bs sp T B pcs fs ch HPRE).
  #[local] Abbreviation tagc_frameI := (tagc_frame ceil FPI0 regs0 mem0 data len bs sp T B pcs fs ch HPRE).

  (* [comment removed for export] *)
  #[local] Abbreviation m3aI := (m3a ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch Hret HPRE Hcanon).
  #[local] Abbreviation jsegI := (jseg ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch Hret HPRE Hcanon Hrc m3aI).
  #[local] Abbreviation m1I := (m1 ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch Hret HPRE Hrc jsegI).
  #[local] Abbreviation m0aI := (m0a ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch Hret HPRE Hrc m1I).

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
  Ltac pkg_tag_e HADM HTAG H18 rest tye kx ktac :=
    lazymatch type of HTAG with tagc _ _ _ ?ty ?sz ?buf _ =>
      pkg HADM ([Z_to_bv 64 sz; buf] ++ rest) (kn_tag tye ++ kx)
        ltac:(apply know_ok_app; [exact (kn_tag_okI _ _ _ ty sz buf rest tye HADM HTAG H18 ltac:(cbn [edenot]; reflexivity)) | ktac])
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
        by (cbn [edenot]; ev_simpl E; rewrite Hb, Hr; apply add_lit_word; lia)
    end.
  Ltac pin_sh HR r Hr b Hb P k c :=
    lazymatch type of HR with regs_ok ?E _ _ =>
      pin_reg HR r (EAlu ALU_ADD (EAlu ALU_SRL (EVar b) (ELit 3)) (ELit (SB + c)))
        by (cbn [edenot]; ev_simpl E; rewrite Hb, Hr; symmetry;
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
  (* [comment removed for export] *)
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
    rewrite ?Z_to_bv_unsigned, ?bv_wrap64_mod; intros Hc;
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
        rewrite ?u_small_frame in H by lia
      | _ => fail "kcellv: no knowledge at" b k n
      end
    end.
  Ltac in_kept := cbn; repeat (first [ left; reflexivity | right ]).
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac call_mftc HADM1 HTAG HC0 Hsz retpc fk :=
    lazymatch goal with
    | HR : regs_ok ?E ?sr ?R1 |- runs_to _ (@mkst ?I1 _ _ ?M1 _) _ =>
      lazymatch type of HTAG with tagc _ _ _ ?ty ?sz ?buf _ =>
      eapply rt_call;
      [ eapply (Hmftc data len bs buf B I1 R1 M1 rom (Z_to_bv 64 retpc));
        [ regv HR (1%bv:reg); reflexivity
        | apply ret_ok_even; rewrite u_small by lia; reflexivity
        | eapply (mftc_pre_atI I1 R1 M1 ty sz buf HADM1 HTAG Hsz); [regv HR (10%bv:reg); reflexivity | regv HR (11%bv:reg); assumption] ]
      | cbv beta;
        let I' := fresh "FPI" in let R' := fresh "R" in let M' := fresh "M" in
        let Hkeep := fresh "Hkeep" in let Hfkeep := fresh "Hfkeep" in let Hfr := fresh "Hfr" in
        let r := fresh "r" in let H10 := fresh "H10'" in let Hr01 := fresh "Hr01" in let Hcells := fresh "Hcells" in
        intros I' R' M' (Hkeep & Hfkeep & Hfr & r & H10 & Hr01 & Hcells);
        cbv zeta in Hfr;
        let HADM' := fresh "HADM'" in let HT' := fresh "HT'" in let HC' := fresh "HC'" in
        destruct (adm_mftcI I1 I' R1 R' M1 M' HADM1 Hfr Hkeep Hfkeep) as (HADM' & HT' & HC');
        fk I' R' M' r HADM' HT' HC' Hkeep H10 Hr01 Hcells
      ]
      end
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma dseg : forall (FPI : FPState) R M ty sz buf,
    ADM FPI R M -> TAGC ty sz buf M -> curves0I M ->
    getr R 18 = T -> getr R 19 = Z_to_bv 64 (t + 4) -> getr R 23 = Z_to_bv 64 (SB + (t + 4) / 8) ->
    getr R 24 = Z_to_bv 64 SB -> getr R 22 = Z_to_bv 64 pcs -> getr R 26 = eobw ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x85844) M rom) QP.
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch Hret HPRE Hcanon Hmftc Hitab Hrc.
    intros FPI R M ty sz buf HADM HTAG HC0 H18 H19 H23 H24 H22 H26. adm_facts HADM.
    pose proof pre_tagI as (Q1 & Q2 & Q3 & Q4).
    pose proof HTAG as (T1 & T2 & T3 & T4 & T5a & T5b & T5c). pose proof (u64_range buf).
    destruct (Z.eq_dec ty 0x6d667431) as [Ety1|Nty1];
      [| destruct (Z.eq_dec ty 0x6d667432) as [Ety2|Nty2];
         [| destruct (Z.eq_dec ty 0x6d424120) as [Ety3|Nty3] ]].
    - (* [comment removed for export] *)
      subst ty.
      pkg_tag HADM HTAG H18 (@nil word) (@nil kentry) ltac:(constructor).
      pin_add HR (19%bv:reg) H19 18%nat H18 4%Z. pin_sh HR (23%bv:reg) H23 18%nat H18 T 4%Z 0%Z. pin_lit HR (24%bv:reg) H24.
      run_fp 30%nat [0x8834c%Z; 0x858e8%Z] noscr true.
      branch_case as Hs48.
      + (* [comment removed for export] *)
        hc_lin Hs48. assert (Hsz : (48 <= sz)%Z) by lia.
        run_fp 30%nat [0x8834c%Z; 0x858e8%Z] noscr true.
        adm_now HADM HADM1.
        call_mftc HADM1 HTAG HC0 Hsz 0x858b8%Z
          ltac:(fun I' R' M' r HADM' HT' HC' Hkeep H10 Hr01 Hcells =>
            apply (f1I I' R' M' sz buf r HADM' (HT' _ _ _ HTAG) ltac:(lia));
            [ kreg Hkeep (18%bv:reg) | kreg Hkeep (19%bv:reg) | kreg Hkeep (23%bv:reg) | kreg Hkeep (24%bv:reg) | kreg Hkeep (9%bv:reg)
            | kreg Hkeep (20%bv:reg) | kreg Hkeep (25%bv:reg) | kreg Hkeep (21%bv:reg)
            | exact H10
            | destruct Hr01 as [-> | ->]; [left; reflexivity | right; split; [reflexivity|]];
              destruct (Hcells eq_refl) as (oc & g & Hoc & Hg & D1 & D2 & D3 & D4);
              exists oc, g; split; [exact Hoc|]; split; [exact Hg|]; split; [exact D1|]; split; [exact D2|]; split; [exact D3|]; exact D4
            | apply HC'; exact HC0 ]).
      + (* [comment removed for export] *)
        run_fp 20%nat [0x8834c%Z; 0x858e8%Z] noscr true.
        adm_now HADM HADM1.
        apply (f1bI _ _ _ sz buf 0%Z 0%Z HADM1 HTAG); [creg (18%bv:reg) | creg (19%bv:reg) | creg (23%bv:reg) | creg (24%bv:reg) | creg (9%bv:reg)
          | creg (10%bv:reg) | left; reflexivity].
    - (* [comment removed for export] *)
      subst ty.
      pkg_tag HADM HTAG H18 (@nil word) (@nil kentry) ltac:(constructor).
      pin_add HR (19%bv:reg) H19 18%nat H18 4%Z. pin_sh HR (23%bv:reg) H23 18%nat H18 T 4%Z 0%Z. pin_lit HR (24%bv:reg) H24.
      run_fp 40%nat [0x8834c%Z; 0x85a58%Z] noscr true.
      branch_case as Hs52.
      + hc_lin Hs52. assert (Hsz : (48 <= sz)%Z) by lia.
        run_fp 30%nat [0x8834c%Z; 0x85a58%Z] noscr true.
        adm_now HADM HADM1.
        call_mftc HADM1 HTAG HC0 Hsz 0x8595c%Z
          ltac:(fun I' R' M' r HADM' HT' HC' Hkeep H10 Hr01 Hcells =>
            apply (f2I I' R' M' sz buf r HADM' (HT' _ _ _ HTAG) ltac:(lia));
            [ kreg Hkeep (18%bv:reg) | kreg Hkeep (19%bv:reg) | kreg Hkeep (23%bv:reg) | kreg Hkeep (24%bv:reg)
            | kreg Hkeep (20%bv:reg) | kreg Hkeep (9%bv:reg) | kreg Hkeep (21%bv:reg)
            | exact H10
            | destruct Hr01 as [-> | ->]; [left; reflexivity | right; split; [reflexivity|]];
              destruct (Hcells eq_refl) as (oc & g & Hoc & Hg & D1 & D2 & D3 & D4);
              exists oc, g; split; [exact Hoc|]; split; [exact Hg|]; split; [exact D1|]; split; [exact D2|]; split; [exact D3|]; exact D4
            | apply HC'; exact HC0 ]).
      + run_fp 20%nat [0x8834c%Z; 0x85a58%Z] noscr true.
        adm_now HADM HADM1.
        apply (f2bI _ _ _ 0x6d667432%Z sz buf 0%Z 0%Z HADM1 HTAG); [right; reflexivity | creg (18%bv:reg) | creg (19%bv:reg) | creg (23%bv:reg) | creg (24%bv:reg)
          | creg (10%bv:reg) | left; reflexivity].
    - (* [comment removed for export] *)
      subst ty.
      pkg_tag HADM HTAG H18 (@nil word) (@nil kentry) ltac:(constructor).
      pin_add HR (19%bv:reg) H19 18%nat H18 4%Z. pin_sh HR (23%bv:reg) H23 18%nat H18 T 4%Z 0%Z. pin_lit HR (24%bv:reg) H24.
      run_fp 50%nat [0x8834c%Z; 0x85a74%Z] noscr true.
      adm_now HADM HADM1.
      apply (m0aI _ _ _ sz buf HADM1 HTAG HC0); [creg (18%bv:reg) | creg (24%bv:reg) | creg (22%bv:reg) | creg (26%bv:reg)].
    - (* [comment removed for export] *)
      destruct T1 as [Hty _].
      destruct (Z_lt_le_dec ty 2147483648) as [Hlo|Hhi].
      + pkg_tag_e HADM HTAG H18 [Z_to_bv 64 ty] (EVar 81) [KRange (EVar 81) 0 2147483647]
          ltac:(constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia | constructor]).
        pin_add HR (19%bv:reg) H19 18%nat H18 4%Z. pin_sh HR (23%bv:reg) H23 18%nat H18 T 4%Z 0%Z. pin_lit HR (24%bv:reg) H24.
        run_fp 30%nat [0x8834c%Z; 0x85e54%Z] noscr true.
        branch_case as Hc1; [| hc_lin Hc1; exfalso; lia].
        run_fp 30%nat [0x8834c%Z; 0x85e54%Z] noscr true.
        branch_case as Hc2; [| hc_lin Hc2; exfalso; lia].
        run_fp 30%nat [0x8834c%Z; 0x85e54%Z] noscr true.
        branch_case as Hc3; [| hc_lin Hc3; exfalso; lia].
        adm_now HADM HADM1. apply (okkI _ _ _ 0%Z 0%Z 0%Z 0%Z HADM1); [creg (24%bv:reg) | creg (10%bv:reg) | left; reflexivity].
      + pkg_tag_e HADM HTAG H18 [Z_to_bv 64 ty] (EVar 81) [KRange (EVar 81) 2147483648 4294967295]
          ltac:(constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia | constructor]).
        pin_add HR (19%bv:reg) H19 18%nat H18 4%Z. pin_sh HR (23%bv:reg) H23 18%nat H18 T 4%Z 0%Z. pin_lit HR (24%bv:reg) H24.
        run_fp 30%nat [0x8834c%Z; 0x85e54%Z] noscr true.
        branch_case as Hc1; [| hc_lin Hc1; rewrite sx4_hi in Hc1 by lia; exfalso; lia].
        run_fp 30%nat [0x8834c%Z; 0x85e54%Z] noscr true.
        branch_case as Hc2; [| hc_lin Hc2; rewrite sx4_hi in Hc2 by lia; exfalso; lia].
        run_fp 30%nat [0x8834c%Z; 0x85e54%Z] noscr true.
        branch_case as Hc3; [| hc_lin Hc3; rewrite sx4_hi in Hc3 by lia; exfalso; lia].
        adm_now HADM HADM1. apply (okkI _ _ _ 0%Z 0%Z 0%Z 0%Z HADM1); [creg (24%bv:reg) | creg (10%bv:reg) | left; reflexivity].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma entry : runs_to SEGS (mkst (FP:=FPI0) regs0 (Z_to_bv 64 0x857cc) mem0 rom) QP.
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch Hra Hret HPRE Hcanon Hmftc Hitab Hrc.
    pose proof HPRE as (Hsp & HT & HA & Hpcs & Heob & Htp & Hpcs01 & Hdok & (ty & Hty) & (sz & buf & Hsz & Hbuf & H4 & Hin) & HTal & HTst & HshT & HsT &
                      WA & HAal & HAhp & HshA & Hshw & Hfs5 & HfsA & Hcurves & Hfr & Hshs &
                      Henv & Hhdr & Hfsw & Hhint & Hfl & Dfs & DA).
    pose proof pre_factsI as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & _). app_facts.
    pose proof (u64_range T) as RT. pose proof Hfr as (_ & _ & WS). change A2B_DB with 2544%Z in WS.
    pose proof Henv as (Hcells & _). pose proof (both_cells64 SEGS mem0 Hcells) as (G1 & G2 & _).
    set (E := Env (vals_ev (junk_vals regs0 ++ fjunk_vals (fp_regs (FPState:=FPI0)) ++ [data; Z_to_bv 64 len])) (blobs_ev [bs])).
    assert (HR : regs_ok E (sr_vars 0) regs0) by exact (regs_ok_vars [] regs0 _ (blobs_ev [bs])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs0) fp_regs _ (blobs_ev [bs])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    assert (HK : know_ok SEGS E mem0
      [KRange (EVar 2) (AS_STKLO + 2544) (2 ^ 47); KWr (SA (EVar 2) (-2544)) 2544;
       KWord (SA (ELit 0) 0x9f920) 8 (ELit 0xa79b8); KWord (SA (ELit 0) 0xa79b8) 8 (ELit SB);
       KRange (EVar 10) AS_STKLO (2 ^ 47 - 24); KAlign (EVar 10) 8; KZero (SA (EAlu ALU_SRL (EVar 10) (ELit 3)) SB) (ELit 3)]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - apply krange_intro; cbn [edenot]; ev_simpl E. rewrite Hsp. lia.
      - apply (kwr_intro SEGS E mem0 (EVar 2) sp (-2544) 2544); [cbn [edenot]; ev_simpl E; exact Hsp | lia | lia | lia |].
        replace (spv + -2544)%Z with (spv - 2544)%Z by lia. exact (proj2 (proj2 (proj2 WS))).
      - eapply (kword_intro SEGS E mem0 (ELit 0) (Z_to_bv 64 0) 0x9f920 8 (ELit 0xa79b8));
          [reflexivity | reflexivity | lia | lia | rewrite u_small by lia; lia | rewrite u_small by lia; lia | rewrite u_small by lia; exact G1].
      - eapply (kword_intro SEGS E mem0 (ELit 0) (Z_to_bv 64 0) 0xa79b8 8 (ELit SB));
          [reflexivity | reflexivity | lia | lia | rewrite u_small by lia; lia | rewrite u_small by lia; lia | rewrite u_small by lia; exact G2].
      - apply krange_intro; cbn [edenot]; ev_simpl E. rewrite HT. lia.
      - apply kalign_intro; [lia|]. cbn [edenot]; ev_simpl E. rewrite HT. exact HTal.
      - apply (kzero_shz_intro SEGS E mem0 (EVar 10) T 3); [cbn [edenot]; ev_simpl E; exact HT | exact HshT | lia | lia]. }
    run_fp 40%nat [0x85844%Z] noscr true.
    (* [comment removed for export] *)
    subst_mems.
    lazymatch goal with |- runs_to _ (@mkst ?I1 ?R1 _ ?M1 _) _ =>
      assert (Hfr1 : frame_mod mem0 M1 [(Z_to_bv 64 (spv - 240), 240%Z)]);
      [ replace [(Z_to_bv 64 (spv - 240), 240%Z)] with (regions_denot E [(SA (EVar 2) (-240), 240%Z)]) by regions_eq;
        frame_logs [(SA (EVar 2) (-240), 240%Z)] | ]
    end.
    lazymatch goal with |- runs_to _ (@mkst ?I1 ?R1 _ ?M1 _) _ => remember M1 as Mz eqn:HMz in *; clear HMz end.
    kcellv (EVar 2) (-8)%Z 8%nat S1. kcellv (EVar 2) (-16)%Z 8%nat S2. kcellv (EVar 2) (-24)%Z 8%nat S3.
    kcellv (EVar 2) (-32)%Z 8%nat S4. kcellv (EVar 2) (-40)%Z 8%nat S5. kcellv (EVar 2) (-48)%Z 8%nat S6.
    kcellv (EVar 2) (-56)%Z 8%nat S7. kcellv (EVar 2) (-64)%Z 8%nat S8. kcellv (EVar 2) (-72)%Z 8%nat S9.
    kcellv (EVar 2) (-80)%Z 8%nat S10. kcellv (EVar 2) (-88)%Z 8%nat S11. kcellv (EVar 2) (-96)%Z 8%nat S12.
    kcellv (EVar 2) (-104)%Z 8%nat S13.
    assert (Hw1 : rs_within [(Z_to_bv 64 (spv - 240), 240%Z)] (BIG0 sp B)) by (unfold BIG0; solve_within).
    assert (HASF0 : ASF ceil sp T B fs ch mem0).
    { split; [exact HshT|]. split; [exact HshA|]. split; [exact Hshw|]. split; [change A2B_DB with 2544%Z in Hshs; exact Hshs|].
      split; [exact Henv|]. split; [exact Hhdr|]. exact Hfsw. }
    lazymatch goal with |- runs_to _ (@mkst ?I1 ?R1 _ ?M1 _) _ =>
      assert (HADM : ADM I1 R1 M1) end.
    { unfold adm.
      split; [regv_lin HR (2%bv:reg); rewrite Hsp; f_equal; lia|].
      split; [regv HR (3%bv:reg); reflexivity|]. split; [regv HR (4%bv:reg); reflexivity|].
      split; [regv HR (8%bv:reg); exact HA|].
      split; [intros r Hr; exact (fregs_same_on E _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity) r Hr)|].
      split.
      { unfold saved, cell64, cell.
        repeat match goal with |- _ /\ _ => split end;
        match goal with |- rdn _ _ (Z_to_bv 64 ?x) _ = _ =>
          first [ replace x with (spv + -8)%Z by ring; exact S1 | replace x with (spv + -16)%Z by ring; exact S2
                | replace x with (spv + -24)%Z by ring; exact S3 | replace x with (spv + -32)%Z by ring; exact S4
                | replace x with (spv + -40)%Z by ring; exact S5 | replace x with (spv + -48)%Z by ring; exact S6
                | replace x with (spv + -56)%Z by ring; exact S7 | replace x with (spv + -64)%Z by ring; exact S8
                | replace x with (spv + -72)%Z by ring; exact S9 | replace x with (spv + -80)%Z by ring; exact S10
                | replace x with (spv + -88)%Z by ring; exact S11 | replace x with (spv + -96)%Z by ring; exact S12
                | replace x with (spv + -104)%Z by ring; exact S13 ] end. }
      split; [eapply frame_mod_within; [| exact Hfr1]; apply within_BIG0; exact Hw1|].
      split.
      { destruct Hdok as (D1 & D2 & D3 & D4). split; [|split; [exact D2|split; [exact D3|]]].
        - eapply data_ok_frame; [exact Hfr1 | exact D1 | solve_apart].
        - eapply shdata_frame; [exact Hfr1 | exact D4 | lia | lia | lia | unfold SB; solve_apart]. }
      split; [eapply writable_frame; [exact Hfr1 | exact WA]|].
      split; [eapply writable_frame; [exact Hfr1 | exact WS]|].
      split; [apply (ASF_frame ceil FPI0 regs0 mem0 rom data len bs sp T B pcs fs ch HPRE _ _ _ HASF0 Hfr1); apply within_BIG0; exact Hw1|].
      exact (hint_flags_frame0 ceil FPI0 regs0 mem0 rom data len bs sp T B pcs fs ch HPRE _ _ _ Hhint Hfl Hfr1 Hw1). }
    apply (dseg _ _ _ ty sz buf HADM).
    - split; [eapply cell32_frame; [exact Hfr1 | exact Hty | lia | lia | solve_apart]|].
      split; [eapply cell32_frame; [exact Hfr1 | exact Hsz | lia | lia | solve_apart]|].
      split; [eapply cell64_frame; [exact Hfr1 | exact Hbuf | lia | lia | solve_apart]|].
      split; [exact H4 | exact Hin].
    - eapply curves0_frameI; [exact Hcurves | exact Hfr1 |].
      unfold b2a_curve_offsets; repeat (apply Forall_cons; [solve_apart|]); apply Forall_nil.
    - creg (18%bv:reg).
    - creg (19%bv:reg).
    - creg (23%bv:reg).
    - creg (24%bv:reg).
    - creg (22%bv:reg).
    - creg (26%bv:reg).
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
End RHB.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem read_b2a_bo_ok : forall ceil,
  read_mft_common_b2a_contract_as SEGS as_both ceil ->
  init_tables_b2a_contract_as SEGS as_both ceil ->
  read_curves_contract_bo SEGS as_both ceil ->
  canonicalize_contract_as SEGS as_both ceil ->
  read_b2a_contract_bo SEGS as_both ceil.
Proof.
  intros ceil Hmftc Hitab Hrc Hcanon. unfold read_b2a_contract_bo. intros data len bs sp T B pcs fs ch.
  unfold fn_contract. intros FPI regs mem rom ret Hra Hret HPRE.
  destruct (runs_to_contract SEGS _ ret rom _ (entry ceil FPI regs mem rom ret data len bs sp T B pcs fs ch Hra Hret HPRE Hcanon Hmftc Hitab Hrc))
    as (FPI' & regs' & mem' & Hms & Hk & Hfk & Hpost).
  exists FPI', regs', mem'. split; [exact Hms|]. split; [exact Hk|]. split; [exact Hfk|]. exact Hpost.
Qed.
