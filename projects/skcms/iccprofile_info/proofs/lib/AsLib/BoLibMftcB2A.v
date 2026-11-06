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
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs LibWP2Lib.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs BoBase AsLibWP2Spec AsLibPlace.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymDriveLZ.
Import ListNotations.
Open Scope bv_scope.
Import ASX. Import ASXS.
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

Section P.
  Variable ceil : Z.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte) (ret sp : word).
  Variables (data : word) (len : Z) (bs : list byte) (mft B : word).
  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis HPRE : mftc_b2a_pre_as SEGS as_both ceil data len bs mft B FPI regs mem.

  #[local] Abbreviation ic := (bs_byte bs (bv_unsigned mft + 8 - bv_unsigned data)).
  #[local] Abbreviation oc := (bs_byte bs (bv_unsigned mft + 9 - bv_unsigned data)).
  #[local] Abbreviation g := (bs_byte bs (bv_unsigned mft + 10 - bv_unsigned data)).

  Let E : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI))
                                ++ [Z_to_bv 64 ic; Z_to_bv 64 oc; Z_to_bv 64 g; data; Z_to_bv 64 len])) (blobs_ev [bs]).

  (* [comment removed for export] *)
  Definition kn_base (eic eoc : expr) (glo ghi : Z) : list kentry :=
    [KWord (SA (ELit 0) 0x9f920) 8 (ELit 0xa79b8); KWord (SA (ELit 0) 0xa79b8) 8 (ELit SB);
     KWord (SA (EVar 10) 8) 1 eic; KWord (SA (EVar 10) 9) 1 eoc; KWord (SA (EVar 10) 10) 1 (EVar 66);
     KRange (EVar 66) glo ghi; KAlign (EVar 11) 8; KRange (EVar 11) 1 (2 ^ 47 - 400);
     KWr (SA (EVar 11) 0) 400; KDisj (SA (EVar 11) 0) 400 (SA (EVar 10) 0) 48;
     KZero (SA (EAlu ALU_SRL (EVar 11) (ELit 3)) SB) (ELit 50);
     KRange (EVar 10) 1 (2 ^ 47 - 48);
     KRange (EVar 2) (AS_STKLO + 16) (2^47); KWr (SA (EVar 2) (-16)) 16;
     KRange (EVar 67) 1 (2 ^ 47 - 16); KRange (EVar 68) 0 (2^26); KShad (EVar 67) (EVar 68) SB;
     KRange (EAlu ALU_ADD (EVar 67) (EVar 68)) 0 (2 ^ 47 - 16);
     KDisj (SA (EVar 11) 0) 400 ZSH ZSHL; KDisj (SA (EVar 11) 0) 400 ZIMG ZIMGL; KDisj (SA (EVar 11) 0) 400 (SA (EVar 2) (-16)) 16;
     KDisj (SA (EVar 10) 0) 48 ZSH ZSHL; KDisj (SA (EVar 10) 0) 48 ZIMG ZIMGL; KDisj (SA (EVar 10) 0) 48 (SA (EVar 2) (-16)) 16].

  Lemma kn_base_ok : forall eic eoc glo ghi,
    edenot E eic = Z_to_bv 64 ic -> edenot E eoc = Z_to_bv 64 oc -> (glo <= g <= ghi)%Z ->
    know_ok SEGS E mem (kn_base eic eoc glo ghi).
  Proof using ceil FPI regs mem sp data len bs mft B Hsp HPRE.
    intros eic eoc glo ghi Heic Heoc Hg.
    destruct HPRE as (Hmft & HB & (Hdok & Hdheap & Hdal & Hshd) & Hin & Hwr & Hal & HBheap & HshB & Hdisj & Hsb & (sp' & Hsp' & Hfr)).
    rewrite Hsp in Hsp'. subst sp'. destruct Hfr as (Hstk & Hspal & (_ & _ & _ & Hswr)). apply (as_sb_both SEGS mem) in Hsb. destruct Hsb as [Hg1 Hg2]. unfold cell64, cell in Hg1, Hg2.
    unfold heapish, stackish in Hdheap, HBheap, Hstk. app_facts.
    pose proof Hdok as (Hlen & Hbs & Hdnz & Hdhi & Hblob). destruct Hin as (Hin1 & _ & Hin2). destruct Hwr as (W1 & W2 & W3 & W4).
    pose proof (u64_range mft). pose proof (u64_range B). pose proof (u64_range data). pose proof (u64_range sp).
    pose proof (bs_byte_range bs (bv_unsigned mft + 8 - bv_unsigned data)) as R1.
    pose proof (bs_byte_range bs (bv_unsigned mft + 9 - bv_unsigned data)) as R2.
    pose proof (bs_byte_range bs (bv_unsigned mft + 10 - bv_unsigned data)) as R3.
    unfold kn_base.
    repeat apply Forall_cons; try apply Forall_nil.
    - eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0x9f920 8 (ELit 0xa79b8) (Z_to_bv 64 0xa79b8)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0xa79b8 8 (ELit SB) (Z_to_bv 64 SB)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (EVar 10) mft 8 1 eic (Z_to_bv 64 ic));
        [cbn [edenot]; ev_simpl E; exact Hmft | exact Heic | lia | lia | lia | lia
        | apply (data_byte_cell SEGS mem data len bs); [exact Hdok | lia | lia]].
    - eapply (kword_intro SEGS E mem (EVar 10) mft 9 1 eoc (Z_to_bv 64 oc));
        [cbn [edenot]; ev_simpl E; exact Hmft | exact Heoc | lia | lia | lia | lia
        | apply (data_byte_cell SEGS mem data len bs); [exact Hdok | lia | lia]].
    - eapply (kword_intro SEGS E mem (EVar 10) mft 10 1 (EVar 66) (Z_to_bv 64 g));
        [cbn [edenot]; ev_simpl E; exact Hmft | reflexivity | lia | lia | lia | lia
        | apply (data_byte_cell SEGS mem data len bs); [exact Hdok | lia | lia]].
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia.
    - apply kalign_intro; [lia|]. cbn [edenot]; ev_simpl E. rewrite HB. exact Hal.
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite HB; lia.
    - apply (kwr_intro SEGS E mem (EVar 11) B 0 400); [cbn [edenot]; ev_simpl E; exact HB | lia | lia | lia |].
      rewrite Z.add_0_r. exact W4.
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite Hmft, HB. lia.
    - eapply (kzero_shz_intro SEGS E mem (EVar 11) B 50); [cbn [edenot]; ev_simpl E; exact HB | exact HshB | lia | lia].
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite Hmft; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite Hsp; lia.
    - apply (kwr_intro SEGS E mem (EVar 2) sp (-16) 16); [cbn [edenot]; ev_simpl E; exact Hsp | lia | lia | lia | exact Hswr].
    - apply krange_intro; cbn [edenot]; ev_simpl E; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia.
    - eapply (kshad_intro SEGS E mem (EVar 67) (EVar 68) data len); [reflexivity | cbn; rewrite u_small by lia; reflexivity | lia | lia | exact Hshd].
    - eapply krange_add_intro; [place_den | place_den | rewrite ?u_small by lia; lia | lia].
    - kdisj_place.
    - kdisj_place.
    - kdisj_place.
    - kdisj_place.
    - kdisj_place.
    - kdisj_place.
  Qed.

  (* [comment removed for export] *)
  Definition Qpost : machine_state -> Prop := fun st' : machine_state =>
    exists (FPI' : FPState) regs' mem',
      st' = mkst (FP:=FPI') regs' ret mem' rom /\
      (regs_kept abi_kept regs regs' /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI')) /\
       mftc_b2a_post_as SEGS data len bs mft B regs mem FPI' regs' mem').

  Ltac kept_tac :=
    lazymatch goal with
    | HR : regs_ok ?E _ ?R, HF : fregs_ok _ _ (@fp_regs ?I), HR0 : id (regs_ok _ ?sr0 ?regs), HF0 : id (fregs_ok _ ?sfr0 ?fr) |- _ =>
      split; [exact (regs_same_on E sr0 _ regs R abi_kept HR0 HR ltac:(vm_compute; reflexivity))|];
      split; [exact (fregs_same_on E sfr0 _ fr _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity))|]
    end.

  (* [comment removed for export] *)
  Ltac frame_of_log E RS fixup :=
    lazymatch goal with
    | |- frame_mod ?M (mem_denot _ ?M ?log) ?regions =>
        replace regions with (regions_denot E RS)
          by (cbn [regions_denot map fst snd]; unfold adenot; cbn [a_base a_off edenot]; ev_simpl E; fixup; reflexivity);
        apply (frame_mod_mem_denot E M log RS);
          [ lazymatch goal with H : log_flat _ log |- _ => exact H end
          | repeat (apply Forall_cons); [..|apply Forall_nil]; cbn [fst snd]; unfold flat, estart; cbn [a_base a_off edenot]; ev_simpl E; fixup; lia
          | vm_compute; reflexivity ]
    end.

  (* [comment removed for export] *)
  Ltac finish_common :=
    fin_ret;
    lazymatch goal with |- Qpost (@mkst ?I ?R' _ ?M' _) =>
      exists I, R', M';
      split; [ lazymatch goal with HR : regs_ok _ _ R' |- _ => regv HR (1%bv:reg) end; rewrite_getr; reflexivity |];
      kept_tac;
      unfold mftc_b2a_post_as; cbv zeta; split;
      [ lazymatch goal with EQM : M' = _ |- _ => rewrite EQM end;
        frame_of_log E [(SA (EVar 2) (-16), 16%Z); (SA (EVar 11) 96, 8%Z); (SA (EVar 11) 392, 8%Z)] ltac:(rewrite_getr; rewrite ?Hsp; unfold v_addi)
      | exists (bv_unsigned (getr R' 10)); split; [symmetry; apply Z_to_bv_bv_unsigned|] ]
    end.

  Ltac rewrite_getr_in H :=
    repeat match goal with G : getr ?R ?r = _ |- _ => rewrite G in H end.

  Ltac flat_tac := unfold flat, estart; cbn [a_base a_off edenot]; ev_simpl E; rewrite_getr; lia.

  (* [comment removed for export] *)
  Ltac kcell b k n v H :=
    lazymatch goal with HK : know_ok _ ?E ?M ?kn |- _ =>
      let KR := fresh "KR" in let Hfl := fresh "Hfl" in
      assert (KR : kread SEGS kn b k n = Some v) by (vm_compute; reflexivity);
      pose proof (kread_rdn SEGS E M kn b k n v HK KR ltac:(lia) ltac:(lia)) as H; clear KR;
      lazymatch type of H with ?FL -> _ => assert (Hfl : FL) by flat_tac; specialize (H Hfl); clear Hfl end;
      unfold adenot, v_addi in H; cbn [a_base a_off edenot] in H; ev_simpl_in E H; rewrite_getr_in H
    end.

  Ltac prelim :=
    pose proof HPRE as (Hmft & HB & (Hdok & Hdheap & Hdal & Hshd) & Hin & Hwr & Hal & HBheap & HshB & Hdisj & Hsb & (sp' & Hsp' & Hfr));
    rewrite Hsp in Hsp'; subst sp'; destruct Hfr as (Hstk & Hspal & Hswin);
    unfold heapish, stackish in Hdheap, HBheap, Hstk; app_facts;
    pose proof Hdok as (Hlen & Hbs & Hdnz & Hdhi & Hblob); destruct Hin as (Hin1 & _ & Hin2);
    destruct Hwr as (W1 & W2 & W3 & W4);
    pose proof (u64_range mft); pose proof (u64_range B); pose proof (u64_range data); pose proof (u64_range sp);
    pose proof (bs_byte_range bs (bv_unsigned mft + 8 - bv_unsigned data)) as R1;
    pose proof (bs_byte_range bs (bv_unsigned mft + 9 - bv_unsigned data)) as R2;
    pose proof (bs_byte_range bs (bv_unsigned mft + 10 - bv_unsigned data)) as R3;
    assert (HR : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [bs]));
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [bs]));
    pose proof (HR : id _) as HR0; pose proof (HF : id _) as HF0.

  (* [comment removed for export] *)
  Ltac fin0 :=
    finish_common;
    lazymatch goal with HR : regs_ok _ _ ?R' |- _ => regv HR (10%bv:reg) end;
    rewrite ?mftc_ret_word; rewrite ?(u_small g), ?u_small by lia;
    try (replace (g <? 2)%Z with true by (symmetry; apply Z.ltb_lt; lia));
    split; [lia | intros; exfalso; lia].

  Ltac cell8_at j :=
    first [ exfalso; lia
          | let C := fresh "C" in
            let k := eval vm_compute in (392 + j)%Z in
            kcell (EVar 11) k 1%nat (EExt false 0 1 (EVar 66)) C;
            rewrite (ext_val_zx_id 1 (Z_to_bv 64 g)) in C by (rewrite u_small by lia; cbn; lia);
            replace (bv_unsigned B + 392 + j)%Z with (bv_unsigned B + k)%Z by lia; exact C ].
  Ltac cells8 :=
    intros i Hi; split; [lia|];
    let Hi4 := fresh "Hi4" in
    assert (Hi4 : (i = 0 \/ i = 1 \/ i = 2)%Z) by lia;
    destruct Hi4 as [->|[->| ->]]; [cell8_at 0%Z | cell8_at 1%Z | cell8_at 2%Z].

  (* [comment removed for export] *)
  Ltac case_ok :=
    lazymatch goal with Hl3 : edenot E (ELit 3) = Z_to_bv 64 ic, Hv65 : edenot E (EVar 65) = Z_to_bv 64 oc |- _ =>
      assert (HK : know_ok SEGS E mem (KRange (EVar 65) 3 4 :: kn_base (ELit 3) (EVar 65) 2 255))
        by (constructor; [apply krange_intro; rewrite Hv65; rewrite u_small by lia; lia | apply kn_base_ok; [exact Hl3 | exact Hv65 | lia]]);
      unfold kn_base in HK;
      run_fp 250%nat (@nil Z) noscr true;
      finish_common;
      lazymatch goal with HR : regs_ok _ _ ?R' |- _ => regv HR (10%bv:reg) end;
      rewrite mftc_ret_word; rewrite (u_small g) by lia;
      replace (g <? 2)%Z with false by (symmetry; apply Z.ltb_ge; lia);
      lazymatch goal with |- context [if ?b then 1%Z else 0%Z] => destruct b end;
      [ split; [lia|]; intros _;
        exists oc, g; split; [lia|]; split; [lia|];
        let C1 := fresh "C1" in let C2 := fresh "C2" in let C3 := fresh "C3" in
        kcell (EVar 11) 96%Z 4%nat (ELit 3) C1;
        kcell (EVar 11) 100%Z 4%nat (ELit 0) C2;
        kcell (EVar 11) 396%Z 4%nat (EExt false 0 4 (EVar 65)) C3;
        rewrite (ext_val_zx_id 4 (Z_to_bv 64 oc)) in C3 by (rewrite u_small by lia; cbn; lia);
        split; [split; [lia | exact C1]|];
        split; [split; [lia | exact C2]|];
        split; [split; [lia | exact C3]|];
        cells8
      | split; [lia | intros; exfalso; lia] ]
    end.

  Theorem body : runs_to SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x8834c) mem rom) Qpost.
  Proof using ceil FPI regs mem rom ret sp data len bs mft B Hra Hret Hsp HPRE.
    prelim.
    assert (Hv64 : edenot E (EVar 64) = Z_to_bv 64 ic) by (cbn [edenot]; ev_simpl E; reflexivity).
    assert (Hv65 : edenot E (EVar 65) = Z_to_bv 64 oc) by (cbn [edenot]; ev_simpl E; reflexivity).
    destruct (Z.eq_dec ic 3) as [Hic3|Hicne].
    - (* [comment removed for export] *)
      assert (Hl3 : edenot E (ELit 3) = Z_to_bv 64 ic) by (rewrite Hic3; reflexivity).
      destruct (Z_lt_le_dec oc 3) as [Hoc3|Hoc3]; [|destruct (Z_lt_le_dec oc 5) as [Hoc5|Hoc5]].
      + (* [comment removed for export] *)
        assert (HK : know_ok SEGS E mem (KRange (EVar 65) 0 2 :: kn_base (ELit 3) (EVar 65) 0 255)).
        { constructor; [apply krange_intro; rewrite Hv65; rewrite u_small by lia; lia | apply kn_base_ok; [exact Hl3 | exact Hv65 | lia]]. }
        unfold kn_base in HK. run_fp 150%nat (@nil Z) noscr true. fin0.
      + (* [comment removed for export] *)
        destruct (Z_lt_le_dec g 2) as [Hglt|Hgge].
        * assert (HK : know_ok SEGS E mem (KRange (EVar 65) 3 4 :: kn_base (ELit 3) (EVar 65) 0 1)).
          { constructor; [apply krange_intro; rewrite Hv65; rewrite u_small by lia; lia | apply kn_base_ok; [exact Hl3 | exact Hv65 | lia]]. }
          unfold kn_base in HK. run_fp 250%nat (@nil Z) noscr true. fin0.
        * case_ok.
      + (* [comment removed for export] *)
        assert (HK : know_ok SEGS E mem (KRange (EVar 65) 5 255 :: kn_base (ELit 3) (EVar 65) 0 255)).
        { constructor; [apply krange_intro; rewrite Hv65; rewrite u_small by lia; lia | apply kn_base_ok; [exact Hl3 | exact Hv65 | lia]]. }
        unfold kn_base in HK. run_fp 150%nat (@nil Z) noscr true. fin0.
    - (* [comment removed for export] *)
      destruct (Z_lt_le_dec ic 3) as [Hlt|Hge].
      + assert (HK : know_ok SEGS E mem (KRange (EVar 64) 0 2 :: kn_base (EVar 64) (EVar 65) 0 255)).
        { constructor; [apply krange_intro; rewrite Hv64; rewrite u_small by lia; lia | apply kn_base_ok; [exact Hv64 | exact Hv65 | lia]]. }
        unfold kn_base in HK. run_fp 150%nat (@nil Z) noscr true. fin0.
      + assert (HK : know_ok SEGS E mem (KRange (EVar 64) 4 255 :: kn_base (EVar 64) (EVar 65) 0 255)).
        { constructor; [apply krange_intro; rewrite Hv64; rewrite u_small by lia; lia | apply kn_base_ok; [exact Hv64 | exact Hv65 | lia]]. }
        unfold kn_base in HK. run_fp 150%nat (@nil Z) noscr true. fin0.
  Qed.
End P.

Theorem read_mft_common_b2a_bo_ok : forall ceil, read_mft_common_b2a_contract_as SEGS as_both ceil.
Proof.
  intros ceil data len bs mft B FPI regs mem rom ret Hra Hret HPRE.
  exact (runs_to_contract SEGS _ ret rom _ (body ceil FPI regs mem rom ret (getr regs 2) data len bs mft B Hra Hret eq_refl HPRE)).
Qed.
