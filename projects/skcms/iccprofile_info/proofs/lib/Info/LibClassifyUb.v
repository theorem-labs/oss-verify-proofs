(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Import Ubsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import SymExecFP SymExecFPSound SymRunFP SymDriveFP SymCallFP LibDefs LibWP1Spec LibCurveSpec LibRodata FpuFacts FpuGlue.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf Require Import SymDriveLB.
From Stdlib Require Import Zify.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import SymDriveLZ.
Unset Nia Cache.  (* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.ev_simpl E ::= ev_simpl_lz E.
#[local] Ltac SymDriveFP.ev_simpl_in E H ::= ev_simpl_in_lz E H.
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.run_fp_with_h HR HF HK fuel stops scr chints keep extra ::= run_fp_with_h_lz HR HF HK fuel stops scr chints keep extra.
#[local] Ltac SymDriveFP.branch_case_with HR HF HK Hc ::= branch_case_with_lz HR HF HK Hc.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SXF. Import SXFS.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Lemma mulm1_lit : forall v, mul_div M_MUL (Z_to_bv 64 (-1)) (Z_to_bv 64 v) = Z_to_bv 64 (- v).
Proof.
  intros v. apply bv_eq. rewrite u_mul64, !Z_to_bv_unsigned, !bv_wrap64_mod.
  change ((-1) mod 2 ^ 64)%Z with (2^64 - 1)%Z. nia.
Qed.

Lemma negw_lit : forall v, (-2^31 < v < 2^31)%Z ->
  sext 64 (alu32 ALU_SUB (low32 (Z_to_bv 64 0)) (low32 (Z_to_bv 64 v))) = Z_to_bv 64 (- v).
Proof.
  intros v Hv. rewrite w_subw. unfold v_subw. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2^31)%Z. change (bv_modulus 32) with (2^32)%Z. lia.
Qed.

Lemma addw0_lit : forall v, (-2^31 <= v < 2^31)%Z ->
  sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 v)) (low32 (Z_to_bv 64 0))) = Z_to_bv 64 v.
Proof.
  intros v Hv. rewrite w_addw. unfold v_addw. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2^31)%Z. change (bv_modulus 32) with (2^32)%Z. lia.
Qed.

#[local] Abbreviation SEGS := Ubsan.M.loaded_segments.

Section Proof.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp tf g a b c d e f : word).

  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis Htf : getr regs 10 = tf.
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 0.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 0.
  Hypothesis Hg : rdn SEGS mem (Z_to_bv 64 (bv_unsigned tf + 0)) 4 = Some (word_to_le_bytes 4 g).
  Hypothesis Ha : rdn SEGS mem (Z_to_bv 64 (bv_unsigned tf + 4)) 4 = Some (word_to_le_bytes 4 a).
  Hypothesis Hb : rdn SEGS mem (Z_to_bv 64 (bv_unsigned tf + 8)) 4 = Some (word_to_le_bytes 4 b).
  Hypothesis Hc : rdn SEGS mem (Z_to_bv 64 (bv_unsigned tf + 12)) 4 = Some (word_to_le_bytes 4 c).
  Hypothesis Hd : rdn SEGS mem (Z_to_bv 64 (bv_unsigned tf + 16)) 4 = Some (word_to_le_bytes 4 d).
  Hypothesis He : rdn SEGS mem (Z_to_bv 64 (bv_unsigned tf + 20)) 4 = Some (word_to_le_bytes 4 e).
  Hypothesis Hf : rdn SEGS mem (Z_to_bv 64 (bv_unsigned tf + 24)) 4 = Some (word_to_le_bytes 4 f).
  Hypothesis Htf28 : (bv_unsigned tf + 28 <= 2 ^ 64)%Z.
  Hypothesis Hsp16 : (0 <= bv_unsigned sp - 16)%Z.
  Hypothesis Hwr : store_ok SEGS mem (Z_to_bv 64 (bv_unsigned sp - 16)) (Z.to_nat 16) = true.
  Hypothesis Hro : forall i, (0x103ec <= i < 0x10490)%Z -> mem (Z_to_bv 64 i) = None.
  Hypothesis Hdisj : (bv_unsigned sp <= bv_unsigned tf \/ bv_unsigned tf + 28 <= bv_unsigned sp - 16)%Z.
  Hypothesis Hsro : (bv_unsigned sp - 16 + 16 <= 0x103ec \/ 0x10490 <= bv_unsigned sp - 16)%Z.

  Let E : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI))
                                ++ [g; a; b; c; d; e; f])) (blobs_ev []).

  Definition kn0 : list kentry :=
    [KImg 0x103ec 0x10490;
     KWord (SA (EVar 10) 0) 4 (EVar 64); KWord (SA (EVar 10) 4) 4 (EVar 65);
     KWord (SA (EVar 10) 8) 4 (EVar 66); KWord (SA (EVar 10) 12) 4 (EVar 67);
     KWord (SA (EVar 10) 16) 4 (EVar 68); KWord (SA (EVar 10) 20) 4 (EVar 69);
     KWord (SA (EVar 10) 24) 4 (EVar 70);
     KWr (SA (EVar 2) (-16)) 16;
     KDisj (SA (EVar 2) (-16)) 16 (SA (EVar 10) 0) 28;
     KDisj (SA (EVar 2) (-16)) 16 (SA (ELit 0) 0x103ec) 164].

  Lemma kn0_ok : know_ok SEGS E mem kn0.
  Proof.
    unfold kn0. pose proof (u64_range tf). pose proof (u64_range sp).
    constructor; [apply kimg_intro; [lia|lia|exact Hro]|].
    constructor; [eapply (kword_intro SEGS E mem (EVar 10) tf 0 4 (EVar 64) g); cbn; try lia; auto|].
    constructor; [eapply (kword_intro SEGS E mem (EVar 10) tf 4 4 (EVar 65) a); cbn; try lia; auto|].
    constructor; [eapply (kword_intro SEGS E mem (EVar 10) tf 8 4 (EVar 66) b); cbn; try lia; auto|].
    constructor; [eapply (kword_intro SEGS E mem (EVar 10) tf 12 4 (EVar 67) c); cbn; try lia; auto|].
    constructor; [eapply (kword_intro SEGS E mem (EVar 10) tf 16 4 (EVar 68) d); cbn; try lia; auto|].
    constructor; [eapply (kword_intro SEGS E mem (EVar 10) tf 20 4 (EVar 69) e); cbn; try lia; auto|].
    constructor; [eapply (kword_intro SEGS E mem (EVar 10) tf 24 4 (EVar 70) f); cbn; try lia; auto|].
    constructor; [apply (kwr_intro SEGS E mem (EVar 2) sp (-16) 16); cbn; try lia; auto|].
    constructor; [cbn [kentry_ok]; unfold estart; cbn; rewrite Hsp, Htf; lia|].
    constructor; [|constructor].
    cbn [kentry_ok]. unfold estart. cbn. rewrite Hsp. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia.
  Qed.


  (* [comment removed for export] *)
  Lemma idx_cases : forall u, (0 <= u < 2 ^ 64)%Z ->
    u = (2^64 - 6)%Z \/ u = (2^64 - 5)%Z \/ u = (2^64 - 4)%Z \/ u = (2^64 - 3)%Z \/ u = (2^64 - 2)%Z
    \/ (4 < (6 + u) mod 2 ^ 64)%Z.
  Proof.
    intros u Hu.
    destruct (Z_lt_dec u (2^64 - 6)) as [Hl|Hl].
    - do 5 right. rewrite Z.mod_small by lia. lia.
    - destruct (Z.eq_dec u (2^64 - 1)) as [->|Hne]; [|lia].
      do 5 right. change ((6 + (2 ^ 64 - 1)) mod 2 ^ 64)%Z with 5%Z. lia.
  Qed.

  Ltac post :=
    lazymatch goal with
    | |- exists FPI' regs' mem', @mkst ?FPI ?R _ ?M _ = _ /\ _ =>
      lazymatch goal with
      | HR : regs_ok ?E _ R, HF : fregs_ok _ _ (@fp_regs FPI), HR0 : id (regs_ok _ ?sr0 ?regs),
        HF0 : id (fregs_ok _ ?sfr0 ?fr), HFR : frame_mod _ M _ |- _ =>
        exists FPI, R, M; split; [| split; [|split]]; unfold regs_kept, fregs_kept;
        [ regv HR (1%bv:reg); rewrite_getr; reflexivity
        | eapply (regs_same_on E sr0 _ regs R abi_kept); [ exact HR0 | exact HR | vm_compute; reflexivity ]
        | eapply (fregs_same_on E sfr0 _ fr _ abi_fkept); [ exact HF0 | exact HF | vm_compute; reflexivity ]
        | exact HFR ]
      end
    end.

  Ltac crawl n :=
    lazymatch n with
    | O => idtac "crawl: out of depth"
    | S ?m =>
        run_fp 200%nat (@nil Z) noscr false;
        first
          [ fin_ret; post
          | let Hc := fresh "Hc" in branch_case as Hc; [crawl m | crawl m] ]
    end.

  Theorem classify_ok :
    exists (FPI' : FPState) regs' mem',
      msteps SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x133b8) mem rom)
                  (mkst (FP:=FPI') regs' ret mem' rom)
      /\ regs_kept abi_kept regs regs'
      /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI'))
      /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 16), 16%Z)].
  Proof.
    apply runs_to_contract with
      (P := fun FPI' regs' mem' => regs_kept abi_kept regs regs'
              /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI')) /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 16), 16%Z)]).
    assert (HR0 : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [])).
    assert (HR : regs_ok E (sr_upd (sr_upd (sr_vars 0) 11 (ELit 0)) 12 (ELit 0)) regs).
    { apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [exact HR0|]|]; cbn [edenot]; [exact H11 | exact H12]. }
    pose proof (HR0 : id _) as HRid. clear HR0. pose proof (HF : id _) as HFid.
    pose proof kn0_ok as HK.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range tf) as Htfr.
    (* [comment removed for export] *)
    run_fp 200%nat (@nil Z) noscr true.
    assert (HFR : frame_mod mem M [(Z_to_bv 64 (bv_unsigned sp - 16), 16%Z)]).
    { rewrite EQM.
      replace [(Z_to_bv 64 (bv_unsigned sp - 16), 16%Z)] with (regions_denot E [(SA (EVar 2) (-16), 16%Z)]).
      2:{ cbn [regions_denot map fst snd]. unfold adenot. cbn [a_base a_off edenot]. ev_simpl E. rewrite Hsp.
          unfold v_addi. f_equal. }
      apply (frame_mod_mem_denot E mem _ [(SA (EVar 2) (-16), 16%Z)]); [exact HLF | | reflexivity].
      constructor; [|constructor]. cbn [fst snd]. unfold flat, estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite Hsp. lia. }
    clear EQM HLF.
    branch_case as Hc1.
    { (* [comment removed for export] *)
      crawl 10%nat. }
    (* [comment removed for export] *)
    run_fp 200%nat (@nil Z) noscr false.
    branch_case as Hc2.
    { (* [comment removed for export] *) crawl 3%nat. }
    br_simpl_in E Hc1. br_simpl_in E Hc2.
    lazymatch type of Hc2 with fcmp_bool F_LT FMT_S ?g' ?wm = false =>
      destruct (classify_words g' (fmv_fx_res FMT_S (Z_to_bv 64 0)) wm
                  (fmv_fx_res FMT_S (Z_to_bv 64 3472883713)) (fmv_fx_res FMT_S (Z_to_bv 64 1325400064))
                  ltac:(rewrite fval_fmv_fx_S; reflexivity) ltac:(rewrite fval_fmv_fx_S; reflexivity)
                  ltac:(rewrite fval_fmv_fx_S; reflexivity) ltac:(rewrite fval_fmv_fx_S; reflexivity) Hc1 Hc2)
        as (TA & TB & v & Hv & Hcvt)
    end.
    (* [comment removed for export] *)
    run_fp 200%nat [0x1340c%Z] (dirs [false;false]) false by (rewrite ?TA, ?TB; reflexivity).
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok _ ?sr ?R =>
      let e := eval vm_compute in (sr_get sr 14) in
      pose proof (reg_val E sr R 14 HR) as HX; change (sr_get sr 14) with e in HX;
      cbn [edenot fop1_denot fop2_denot fop3_denot] in HX; ev_simpl_in E HX; rewrite Hcvt in HX
    end.
    assert (Hcases : v = (-6)%Z \/ v = (-5)%Z \/ v = (-4)%Z \/ v = (-3)%Z \/ v = (-2)%Z
                     \/ ((v < -6)%Z \/ (-2 < v)%Z)) by lia.
    destruct Hcases as [Hv6|[Hv5|[Hv4|[Hv3|[Hv2|Hgen]]]]].
    1-5: subst v;
         lazymatch goal with HR : regs_ok _ ?sr ?R |- _ =>
           lazymatch type of HX with getr _ 14 = Z_to_bv 64 ?v =>
             pose proof (regs_ok_pin E sr R 14 (ELit v) HR ltac:(cbn [edenot]; exact HX)) as HR';
             clear HR HX; rename HR' into HR
           end end.
    1-5: crawl 6%nat.
    (* [comment removed for export] *)
    clear HX.
    run_fp 200%nat (@nil Z) (dirs [false;false]) false
      by (rewrite ?Hcvt; rewrite ?mulm1_lit; rewrite ?negw_lit, ?Z.opp_involutive by lia; rewrite ?addw0_lit by lia;
          rewrite ?negw_lit by lia; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod;
          apply Bool.negb_false_iff; apply Z.eqb_eq; lia).
    branch_case as Hc3; [crawl 3%nat|].
    run_fp 200%nat (@nil Z) (dirs [true]) false
      by (rewrite ?Hcvt; rewrite ?mulm1_lit; rewrite ?addw0_lit by lia;
          rewrite !Z_to_bv_unsigned, !bv_wrap64_mod; apply Z.ltb_lt; lia).
    fin_ret. post.
  Qed.
End Proof.

Theorem classify_Ub_ok : classify_contract SEGS wp1_infoub.
Proof.
  intros sp tf FPI regs mem rom ret Hra Hret PRE.
  destruct PRE as (Hsp & Htf & H11 & H12 & (g & a & b & c & d & e & f & Hg & Ha & Hb & Hc & Hd & He & Hf)
                   & Htf28 & Hwr & Hro & Hdisj).
  pose proof (writable_rodata_apart_Ub mem _ _ 0x103ec 0x10490 ltac:(lia) ltac:(lia) ltac:(lia) Hwr Hro) as Hsro.
  destruct Hwr as (Hw0 & _ & _ & Hst).
  unfold cell in *.
  destruct (classify_ok FPI regs mem rom ret sp tf g a b c d e f Hra Hret Hsp Htf H11 H12
              ltac:(rewrite Z.add_0_r; exact Hg) Ha Hb Hc Hd He Hf Htf28 Hw0 Hst Hro Hdisj Hsro)
    as (FPI' & regs' & mem' & Hms & Hk1 & Hk2 & Hfr).
  exists FPI', regs', mem'. unfold classify_post. cbn [w1_ro_lo w1_ro_hi wp1_infoub] in *. auto.
Qed.
