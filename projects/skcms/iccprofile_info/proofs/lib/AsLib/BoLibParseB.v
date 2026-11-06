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
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs LibFrame LibTagsSpec LibWP2Spec.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs BoBase AsRtSpec AsLibTagsSpec AsLibWP2Spec AsLibTagsLib AsLibTagsCall AsLibFPLib AsLibParseLib AsLibFrame AsLibEnv AsLibParseSpec BoLibParseDefs AsLibKit BoLibParseF BoLibParseE BoLibParseD BoLibParseC3 BoLibParseC2 BoLibParseC1 AsLibCurveSpec AsLibBswap AsLibBswapSx BoLibSpec AsLibPlace.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymDriveLZ.
Import ListNotations.
Open Scope bv_scope.
Import ASX. Import ASXS.
Ltac Zify.zify_post_hook ::= idtac.
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
(* [comment removed for export] *)
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

Section B.
  Variable ceil : Z.
  Variables (FP0 : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp data prio P : word) (len fs : Z) (bs : list byte) (ch : chain).
  Hypothesis HE : PENV ceil regs mem ret sp data prio P len fs bs ch.
  Hypothesis Hgettag : gettag_contract_as SEGS as_both ceil.
  Hypothesis Hrc : read_curve_contract_as SEGS as_both ceil.
  Hypothesis Hmc : imemcpy32_contract SEGS as_both ceil.
  Hypothesis Hxyz : xyzd50_contract_bo SEGS as_both ceil.
  Hypothesis Ha2b : read_a2b_contract_bo SEGS as_both ceil.
  Hypothesis Hb2a : read_b2a_contract_bo SEGS as_both ceil.
  Hypothesis Hcicp : cicp_contract_bo SEGS as_both ceil.
  Hypothesis Husable : usable_contract_bo SEGS as_both ceil.

  #[local] Notation Q := (Q FP0 regs mem rom ret sp data P len fs bs).
  #[local] Notation BIG := (BIG sp P fs).
  #[local] Notation COMMON := (COMMON FP0 regs sp P).
  #[local] Notation SAVED := (SAVED FP0 regs sp).
  #[local] Notation FSOK := (FSOK fs).

  Ltac common HR HF H2 H3 H4 H21 H22 HFK :=
    split; [regv HR (2%bv:reg); first [exact H2 | cbn [edenot]; ev_simpl_goal; exact H2 | rewrite ?H2; try reflexivity; lia]|];
    split; [regv HR (3%bv:reg); exact H3|];
    split; [regv HR (4%bv:reg); exact H4|];
    split; [regv HR (21%bv:reg); first [exact H21 | reflexivity]|];
    split; [regv HR (22%bv:reg); first [exact H22 | reflexivity]|];
    frk HF HFK.

  (* [comment removed for export] *)
  Variables (psz tc : Z) (raw wpcs wdcs : word).
  Hypothesis Htc : (0 <= tc)%Z.
  Hypothesis Hpsz : (132 + 12 * tc <= psz <= len)%Z.

  #[local] Notation ZFACTS := (ZFACTS sp data prio P psz tc raw).

  Variable M : word -> option byte.
  Hypothesis HS : SAVED M.
  Hypothesis Hf : frame_mod mem M BIG.
  Hypothesis HFS : FSOK M.
  Hypothesis HF : ZFACTS M.
  Hypothesis HXp : cell64 SEGS M (bv_unsigned sp - 352) wpcs.
  Hypothesis HXd : cell64 SEGS M (bv_unsigned sp - 360) wdcs.

  (* [comment removed for export] *)
  Ltac exit0_here HR HFr HC :=
    let HC' := fresh "HCx" in
    pose proof HC as HC'; destruct HC' as (?H2 & ?H3 & ?H4 & ?H21 & ?H22 & ?HFK);
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      apply (exit_ok ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE I R' M' 0);
      [ common HR HFr H2 H3 H4 H21 H22 HFK | regv HR (11%bv:reg); reflexivity | left; reflexivity
      | exact HS | exact Hf | exact HFS | intros; exfalso; lia ]
    end.

  (* [comment removed for export] *)
  Definition INV (i : Z) (FPc : FPState) (Rc : bvmap 5 word) : Prop :=
    (0 <= i < tc)%Z /\
    (bv_unsigned (getr Rc 17) = bv_unsigned data + 140 + 12 * i)%Z /\
    (bv_unsigned (getr Rc 10) = bv_unsigned data + 143 + 12 * i)%Z /\
    (bv_unsigned (getr Rc 6) = tc - i)%Z /\
    (bv_unsigned (getr Rc 15) = psz)%Z /\
    getr Rc 7 = Z_to_bv 64 4 /\ (bv_unsigned (getr Rc 16) = 12 * i)%Z /\
    (bv_unsigned (getr Rc 5) = 2 ^ 64 - 133 - bv_unsigned data)%Z /\
    getr Rc 19 = data /\ getr Rc 20 = Z_to_bv 64 len /\
    COMMON FPc Rc /\
    (forall j, (0 <= j < i)%Z -> (4 <= be32 bs (132 + 12 * j + 8))%Z /\
                                (be32 bs (132 + 12 * j + 4) + be32 bs (132 + 12 * j + 8) <= psz)%Z).

  Section Body.
    Variables (i : Z) (FPc : FPState) (Rc : bvmap 5 word).
    Hypothesis HI : INV i FPc Rc.
    Hypothesis IH : forall (FPc' : FPState) (R' : bvmap 5 word),
        INV (i + 1) FPc' R' -> runs_to SEGS (mkst (FP:=FPc') R' (Z_to_bv 64 0x82214) M rom) Q.

    #[local] Abbreviation off_i := (be32 bs (132 + 12 * i + 4)).
    #[local] Abbreviation s_i := (be32 bs (132 + 12 * i + 8)).
    #[local] Abbreviation b0 := (bs_byte bs (132 + 12 * i + 8)).

    Let E : env := Env (vals_ev (junk_vals Rc ++ fjunk_vals (fp_regs (FPState:=FPc))
                                  ++ [Z_to_bv 64 len; Z_to_bv 64 off_i; Z_to_bv 64 s_i; Z_to_bv 64 psz])) (blobs_ev [bs]).

    (* [comment removed for export] *)
    Definition kn_b (slo shi : Z) : list kentry :=
      [KRange (EVar 19) 1 (2 ^ 47 - 16);
       KRange (EVar 17) 140 (2 ^ 47 - 16);
       KRange (EVar 6) 1 (2^32);
       KRange (EVar 16) 0 (2^26);
       KRange (EVar 5) (2^63) (2^64 - 1);
       KRange (EVar 64) 0 (2^26);
       KRange (EVar 65) 0 (2^32 - 1);
       KRange (EVar 66) slo shi;
       KRange (EVar 67) 0 (2^26);
       KShad (EVar 19) (EVar 64) SB;
       KBlobD (SA (EVar 19) 0) (EVar 64) 0].

    Lemma kn_b_ok : forall slo shi, (slo <= s_i <= shi)%Z -> know_ok SEGS E M (kn_b slo shi).
    Proof.
      intros slo shi Hs.
      destruct HI as (Hi & H17 & H10 & H6 & H15 & H7 & H16 & H5 & H19 & _).
      pose proof (u64_range data).
      pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
      pose proof (be32_range bs (132 + 12 * i + 4)) as Ro. pose proof (be32_range bs (132 + 12 * i + 8)) as Rs.
      destruct (penv_at ceil regs mem rom ret sp data prio P len fs bs ch HE M Hf) as (((D1 & D2 & D3 & D4 & D5) & _ & _ & Hshd) & _).
      unfold kn_b, know_ok.
      repeat (apply Forall_cons); [..|apply Forall_nil].
      - apply krange_intro; cbn. rewrite H19. lia.
      - apply krange_intro; cbn. rewrite H17. lia.
      - apply krange_intro; cbn. rewrite H6. lia.
      - apply krange_intro; cbn. rewrite H16. lia.
      - apply krange_intro; cbn. rewrite H5. lia.
      - apply krange_intro; cbn. rewrite u_small by lia. lia.
      - apply krange_intro; cbn. rewrite u_small by lia. lia.
      - apply krange_intro; cbn. rewrite u_small by lia. lia.
      - apply krange_intro; cbn. rewrite u_small by lia. lia.
      - eapply (kshad_intro SEGS E M (EVar 19) (EVar 64) data len); [cbn; exact H19 | cbn; rewrite u_small by lia; reflexivity | lia | lia | exact Hshd].
      - cbn [kentry_ok]. unfold flat, estart, elenZ. cbn. rewrite H19, u_small by lia.
        split; [lia|]. split; [exact D2|]. intros k Hk. rewrite Z.add_0_r. apply D5. exact Hk.
    Qed.

    (* [comment removed for export] *)
    Definition nu (j : nat) : Z :=
      nth j [bs_byte bs (132 + 12 * i); bs_byte bs (132 + 12 * i + 1); bs_byte bs (132 + 12 * i + 2); bs_byte bs (132 + 12 * i + 3);
             bs_byte bs (132 + 12 * i + 4); bs_byte bs (132 + 12 * i + 4 + 1); bs_byte bs (132 + 12 * i + 4 + 2); bs_byte bs (132 + 12 * i + 4 + 3);
             bs_byte bs (132 + 12 * i + 8); bs_byte bs (132 + 12 * i + 8 + 1); bs_byte bs (132 + 12 * i + 8 + 2); bs_byte bs (132 + 12 * i + 8 + 3)]%Z 0%Z.
    Definition atom (sx : bool) (d : Z) : expr * (bool * nat) :=
      (EBlobX sx 0 (EVar 17) d (EVar 19) 1, (sx, Z.to_nat (d + 8))).
    Definition atoms : list (expr * (bool * nat)) :=
      [atom true 3; atom false 0; atom false 1; atom false 2;
       atom false (-3); atom false (-2); atom false (-4); atom true (-1)].

    Lemma nu_range : forall k, (0 <= nu k < 256)%Z.
    Proof. intros k. unfold nu. do 12 (destruct k as [|k]; [cbn [nth]; apply bs_byte_range|]). destruct k; cbn; lia. Qed.

    Lemma atoms_ok_i : atoms_ok E nu atoms.
    Proof.
      destruct HI as (Hi & H17 & H10 & H6 & H15 & H7 & H16 & H5 & H19 & _).
      destruct (penv_at ceil regs mem rom ret sp data prio P len fs bs ch HE M Hf) as (((D1 & D2 & D3 & D4 & D5) & _) & _).
      unfold atoms, atoms_ok. pose proof (u64_range data).
      repeat (apply Forall_cons); [..|apply Forall_nil];
        unfold atom, atom_ok; cbn [edenot eb ev E blobs_ev nth]; ev_simpl E; rewrite H17, H19;
        first [rewrite blob_val_u8 by lia | rewrite blob_val_s8 by lia]; unfold nu; cbn [nth Z.to_nat Z.add Pos.to_nat Pos.iter_op Nat.add]; unfold bs_byte;
        (repeat f_equal); lia.
    Qed.

    (* [comment removed for export] *)
    Lemma tail_ok : forall (FPt : FPState) (Rt : bvmap 5 word),
      (4 <= s_i)%Z ->
      getr Rt 13 = Z_to_bv 64 off_i -> getr Rt 12 = Z_to_bv 64 s_i -> getr Rt 11 = Z_to_bv 64 0 ->
      (bv_unsigned (getr Rt 17) = bv_unsigned data + 140 + 12 * i)%Z ->
      (bv_unsigned (getr Rt 10) = bv_unsigned data + 143 + 12 * i)%Z ->
      (bv_unsigned (getr Rt 6) = tc - i)%Z ->
      (bv_unsigned (getr Rt 15) = psz)%Z ->
      getr Rt 7 = Z_to_bv 64 4 -> (bv_unsigned (getr Rt 16) = 12 * i)%Z ->
      (bv_unsigned (getr Rt 5) = 2 ^ 64 - 133 - bv_unsigned data)%Z ->
      getr Rt 19 = data -> getr Rt 20 = Z_to_bv 64 len ->
      COMMON FPt Rt ->
      runs_to SEGS (mkst (FP:=FPt) Rt (Z_to_bv 64 0x822d4) M rom) Q.
    Proof.
      intros FPt Rt Hs4 T13 T12 T11 T17 T10 T6 T15 T7 T16 T5 T19 T20 HCt.
      pose proof HI as HI'. destruct HI' as (Hi & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsofar).
      pose proof HCt as HC'. destruct HC' as (H2 & H3 & H4 & H21 & H22 & HFK).
      pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
      pose proof (u64_range data) as Rd.
      pose proof (be32_range bs (132 + 12 * i + 4)) as Ro. pose proof (be32_range bs (132 + 12 * i + 8)) as Rs.
      set (Et := Env (vals_ev (junk_vals Rt ++ fjunk_vals (fp_regs (FPState:=FPt))
                               ++ [Z_to_bv 64 len; Z_to_bv 64 off_i; Z_to_bv 64 s_i; Z_to_bv 64 psz])) (blobs_ev [bs])).
      assert (HR : regs_ok Et (sr_vars 0) Rt) by exact (regs_ok_vars [] Rt _ (blobs_ev [bs])).
      assert (HFr : fregs_ok Et (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals Rt) fp_regs _ (blobs_ev [bs])).
      assert (HK : know_ok SEGS Et M
        [KRange (EVar 17) 140 (2 ^ 47 - 16); KRange (EVar 10) 143 (2 ^ 47 - 16); KRange (EVar 6) 1 (2^32);
         KRange (EVar 16) 0 (2^26); KRange (EVar 5) (2^63) (2^64 - 1);
         KRange (EVar 65) 0 (2^32 - 1); KRange (EVar 66) 4 (2^32 - 1); KRange (EVar 67) 0 (2^26)]).
      { unfold know_ok. repeat (apply Forall_cons); [..|apply Forall_nil];
          apply krange_intro; cbn; rewrite ?T17, ?T10, ?T6, ?T16, ?T5, ?u_small by lia; lia. }
      pin_reg HR (13%bv:reg) (EVar 65) by (rewrite (HR (13%bv:reg)); cbn [edenot sr_get sr_vars nth map seq Nat.add]; ev_simpl Et; exact T13).
      pin_reg HR (12%bv:reg) (EVar 66) by (rewrite (HR (12%bv:reg)); cbn [edenot sr_get sr_vars nth map seq Nat.add]; ev_simpl Et; exact T12).
      pin_reg HR (11%bv:reg) (ELit 0) by (rewrite (HR (11%bv:reg)); cbn [edenot sr_get sr_vars nth map seq Nat.add]; ev_simpl Et; exact T11).
      pin_reg HR (15%bv:reg) (EVar 67) by (rewrite (HR (15%bv:reg)); cbn [edenot sr_get sr_vars nth map seq Nat.add]; ev_simpl Et;
         rewrite <- (Z_to_bv_bv_unsigned 64 (getr Rt 15)), T15; reflexivity).
      run_fp 10%nat (@nil Z) noscr false.
      (* [comment removed for export] *)
      branch_case as Hend.
      { exit0_here HR HFr HCt. }
      br_simpl_in Et Hend.
      rewrite ?alu_add in Hend. unfold v_add in Hend. rewrite ?Z_to_bv_unsigned, ?bv_wrap64_mod in Hend.
      apply Z.ltb_ge in Hend. rewrite (Z.mod_small psz), (Z.mod_small off_i), (Z.mod_small s_i) in Hend by lia. rewrite Z.mod_small in Hend by lia.
      run_fp 10%nat [0x82214%Z; 0x82328%Z] noscr false.
      (* [comment removed for export] *)
      branch_case as Hmore.
      - (* [comment removed for export] *)
        br_simpl_in Et Hmore.
        assert (Hlast : (i = tc - 1)%Z).
        { rewrite alu_add in Hmore. unfold v_add in Hmore. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod in Hmore.
          apply Z.eqb_eq in Hmore. rewrite T6 in Hmore.
          Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
          lia.
          Ltac Zify.zify_post_hook ::= idtac. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
        assert (Htags : tags_ok len bs tc psz).
        { apply tags_ok_intro; [lia | lia | lia |].
          intros j Hj. destruct (Z.eq_dec j i) as [->|Hne]; [| apply Hsofar; lia]. split; [exact Hs4 | lia]. }
        lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ _ _) _ =>
          apply (blockC1_run ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE Hgettag Hrc Hmc Hxyz Ha2b Hb2a Hcicp Husable psz tc raw Htags I R2 M wpcs wdcs)
        end;
        [ common HR HFr H2 H3 H4 H21 H22 HFK | exact HS | exact Hf | exact HFS
        | regv HR (19%bv:reg); exact T19
        | regv HR (20%bv:reg); exact T20
        | exact HF | exact HXp | exact HXd ].
      - (* [comment removed for export] *)
        br_simpl_in Et Hmore.
        run_fp 3%nat [0x82214%Z] noscr false.
        apply IH. unfold INV.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]]].
        + rewrite alu_add in Hmore. unfold v_add in Hmore. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod in Hmore.
          apply Z.eqb_neq in Hmore. rewrite T6 in Hmore.
          Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
          lia.
          Ltac Zify.zify_post_hook ::= idtac. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        + regv_lin HR (17%bv:reg). rewrite u_small by lia. lia.
        + regv_lin HR (10%bv:reg). rewrite u_small by lia. lia.
        + regv_lin HR (6%bv:reg). rewrite u_small by lia. lia.
        + regv HR (15%bv:reg). rewrite u_small by lia. lia.
        + regv HR (7%bv:reg). exact T7.
        + regv_lin HR (16%bv:reg). rewrite u_small by lia. lia.
        + regv HR (5%bv:reg). exact T5.
        + regv HR (19%bv:reg). exact T19.
        + regv HR (20%bv:reg). exact T20.
        + common HR HFr H2 H3 H4 H21 H22 HFK.
        + intros j Hj. destruct (Z.eq_dec j i) as [->|Hne]; [| apply Hsofar; lia].
          split; [exact Hs4 | lia].
    Qed.

    Ltac pin_bytes HR r v ids :=
      pin_reg HR r v by
        (rewrite (HR r);
         lazymatch goal with |- edenot ?E0 ?e = _ =>
           apply bv_eq; rewrite (beval_bytes E0 nu nu_range atoms e ids atoms_ok_i ltac:(cbn; lia) ltac:(vm_compute; reflexivity));
           cbn [edenot ev vals_ev]; ev_simpl E0; rewrite u_small by lia; unfold nu, be32; cbn [bytes_val nth]; lia
         end).

    Ltac to_tail HR HFr HC :=
      let HC' := fresh "HCx" in
      pose proof HC as HC'; destruct HC' as (?H2 & ?H3 & ?H4 & ?H21 & ?H22 & ?HFK);
      lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ _ _) _ => apply (tail_ok I R2) end;
      [ lia
      | regv HR (13%bv:reg); reflexivity
      | regv HR (12%bv:reg); reflexivity
      | regv HR (11%bv:reg); reflexivity
      | regv HR (17%bv:reg); assumption
      | regv_lin HR (10%bv:reg); rewrite ?u_small by lia; lia
      | regv HR (6%bv:reg); assumption
      | regv HR (15%bv:reg); rewrite u_small by lia; reflexivity
      | regv HR (7%bv:reg); reflexivity
      | regv HR (16%bv:reg); assumption
      | regv HR (5%bv:reg); assumption
      | regv HR (19%bv:reg); assumption
      | regv HR (20%bv:reg); assumption
      | common HR HFr H2 H3 H4 H21 H22 HFK ].

    Lemma body_ok : runs_to SEGS (mkst (FP:=FPc) Rc (Z_to_bv 64 0x82214) M rom) Q.
    Proof.
      pose proof HI as HI'. destruct HI' as (Hi & H17 & H10 & H6 & H15 & H7 & H16 & H5 & H19 & H20 & HC & Hsofar).
      pose proof HC as HC'. destruct HC' as (_ & _ & _ & _ & H22 & _).
      pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
      destruct (penv_at ceil regs mem rom ret sp data prio P len fs bs ch HE M Hf) as (((D1 & D2 & D3 & D4 & D5) & _) & _).
      pose proof (u64_range data) as Rd.
      pose proof (be32_range bs (132 + 12 * i + 4)) as Ro. pose proof (be32_range bs (132 + 12 * i + 8)) as Rs.
      pose proof (bs_byte_range bs (132 + 12 * i + 8)) as Rb0.
      pose proof (bs_byte_range bs (132 + 12 * i + 8 + 1)) as Rb1. pose proof (bs_byte_range bs (132 + 12 * i + 8 + 2)) as Rb2.
      pose proof (bs_byte_range bs (132 + 12 * i + 8 + 3)) as Rb3.
      assert (HR : regs_ok E (sr_vars 0) Rc) by exact (regs_ok_vars [] Rc _ (blobs_ev [bs])).
      assert (HFr : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals Rc) fp_regs _ (blobs_ev [bs])).
      pin_reg HR (7%bv:reg) (ELit 4) by (rewrite (HR (7%bv:reg)); cbn [edenot sr_get sr_vars nth map seq Nat.add]; ev_simpl E; exact H7).
      pin_reg HR (22%bv:reg) (ELit SB) by (rewrite (HR (22%bv:reg)); cbn [edenot sr_get sr_vars nth map seq Nat.add]; ev_simpl E; exact H22).
      pin_reg HR (15%bv:reg) (EVar 67) by (rewrite (HR (15%bv:reg)); cbn [edenot sr_get sr_vars nth map seq Nat.add]; ev_simpl E;
         rewrite <- (Z_to_bv_bv_unsigned 64 (getr Rc 15)), H15; reflexivity).
      pin_reg HR (10%bv:reg) (EAlu ALU_ADD (EVar 17) (ELit 3)) by (rewrite (HR (10%bv:reg)); cbn [edenot sr_get sr_vars nth map seq Nat.add]; ev_simpl E;
         rewrite alu_add_lit, <- (Z_to_bv_bv_unsigned 64 (getr Rc 10)), H10, H17; apply (f_equal (Z_to_bv 64)); lia).
      destruct (Z_lt_le_dec b0 128) as [Hb0|Hb0].
      - (* [comment removed for export] *)
        assert (Hb7 : Z.testbit (nu 8%nat) 7 = false).
        { unfold nu. cbn [nth]. apply tb_small_high. cbn [Z.pow Z.pow_pos Pos.iter Z.mul]. lia. }
        assert (Hs31 : (s_i < 2 ^ 31)%Z) by (unfold be32 in *; lia).
        destruct (Z_lt_le_dec s_i 4) as [Hs4|Hs4].
        + (* [comment removed for export] *)
          pose proof (kn_b_ok 0 3 ltac:(lia)) as HK.
          run_fp 90%nat [0x822a4%Z] noscr false.
          pin_reg HR (12%bv:reg) (EVar 66) by
            (rewrite (HR (12%bv:reg));
             lazymatch goal with |- edenot _ ?e = _ =>
               apply bv_eq; rewrite (beval_bytes_sx E nu nu_range atoms e [11;10;9;8]%nat 8%nat atoms_ok_i ltac:(cbn; lia) Hb7 ltac:(vm_compute; reflexivity))
             end;
             cbn [edenot ev E vals_ev]; ev_simpl E; rewrite u_small by lia; unfold nu, be32; cbn [bytes_val nth]; lia).
          run_fp 10%nat [0x82194%Z] noscr false.
          exit0_here HR HFr HC.
        + (* [comment removed for export] *)
          pose proof (kn_b_ok 4 (2^31 - 1) ltac:(lia)) as HK.
          run_fp 90%nat [0x822a4%Z] noscr false.
          pin_reg HR (12%bv:reg) (EVar 66) by
            (rewrite (HR (12%bv:reg));
             lazymatch goal with |- edenot _ ?e = _ =>
               apply bv_eq; rewrite (beval_bytes_sx E nu nu_range atoms e [11;10;9;8]%nat 8%nat atoms_ok_i ltac:(cbn; lia) Hb7 ltac:(vm_compute; reflexivity))
             end;
             cbn [edenot ev E vals_ev]; ev_simpl E; rewrite u_small by lia; unfold nu, be32; cbn [bytes_val nth]; lia).
          run_fp 40%nat [0x822d4%Z] noscr false.
          pin_bytes HR (13%bv:reg) (EVar 65) [7; 6; 5; 4]%nat.
          to_tail HR HFr HC.
      - (* [comment removed for export] *)
        assert (Hs31 : (2 ^ 31 <= s_i)%Z) by (unfold be32 in *; lia).
        pose proof (kn_b_ok (2^31) (2^32 - 1) ltac:(lia)) as HK.
        run_fp 90%nat [0x822a4%Z] noscr false.
        branch_case as Hsz.
        { (* [comment removed for export] *) exit0_here HR HFr HC. }
        run_fp 40%nat [0x822d4%Z] noscr false.
        pin_bytes HR (12%bv:reg) (EVar 66) [11; 10; 9; 8]%nat.
        pin_bytes HR (13%bv:reg) (EVar 65) [7; 6; 5; 4]%nat.
        to_tail HR HFr HC.
    Qed.
  End Body.

  (* [comment removed for export] *)
  Lemma loopB_run : forall (n : nat) (i : Z) (FPc : FPState) (Rc : bvmap 5 word),
      (tc - i <= Z.of_nat n)%Z -> INV i FPc Rc ->
      runs_to SEGS (mkst (FP:=FPc) Rc (Z_to_bv 64 0x82214) M rom) Q.
  Proof.
    induction n as [|n IHn]; intros i FPc Rc Hn HI.
    - destruct HI as (Hi & _). exfalso. lia.
    - apply (body_ok i FPc Rc HI). intros FPc' R' HI'. apply (IHn (i + 1)%Z FPc' R'); [| exact HI'].
      lia.
  Qed.

  Lemma blockB_run : forall (FPc : FPState) (Rc : bvmap 5 word),
      INV 0 FPc Rc -> runs_to SEGS (mkst (FP:=FPc) Rc (Z_to_bv 64 0x82214) M rom) Q.
  Proof. intros FPc Rc HI. apply (loopB_run (Z.to_nat tc) 0 FPc Rc); [lia | exact HI]. Qed.
End B.
