(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Import Asan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs LibFPLib.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs AsRtSpec AsLibCurveSpec AsLibPlace.
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

#[local] Abbreviation SEGS := Asan.M.loaded_segments.

Section Proof.
  Variable ceil : Z.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp C g a b c d e f : word).

  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis Htf : getr regs 10 = Z_to_bv 64 (bv_unsigned C + 4).
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 0.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 0.
  Hypothesis Hg : rdn SEGS mem (Z_to_bv 64 (bv_unsigned C + 4)) 4 = Some (word_to_le_bytes 4 g).
  Hypothesis Ha : rdn SEGS mem (Z_to_bv 64 (bv_unsigned C + 8)) 4 = Some (word_to_le_bytes 4 a).
  Hypothesis Hb : rdn SEGS mem (Z_to_bv 64 (bv_unsigned C + 12)) 4 = Some (word_to_le_bytes 4 b).
  Hypothesis Hc : rdn SEGS mem (Z_to_bv 64 (bv_unsigned C + 16)) 4 = Some (word_to_le_bytes 4 c).
  Hypothesis Hd : rdn SEGS mem (Z_to_bv 64 (bv_unsigned C + 20)) 4 = Some (word_to_le_bytes 4 d).
  Hypothesis He : rdn SEGS mem (Z_to_bv 64 (bv_unsigned C + 24)) 4 = Some (word_to_le_bytes 4 e).
  Hypothesis Hf : rdn SEGS mem (Z_to_bv 64 (bv_unsigned C + 28)) 4 = Some (word_to_le_bytes 4 f).
  Hypothesis HCal : (bv_unsigned C mod 8 = 0)%Z.
  Hypothesis HCrange : (appm (bv_unsigned C) 32 /\ (0 < bv_unsigned C)%Z) /\ (bv_unsigned C + 32 <= ceil)%Z.
  Hypothesis HshC : shz mem (bv_unsigned C) 4.
  Hypothesis Hsprange : ((AS_STKLO <= ceil)%Z /\ (ceil + 16 <= bv_unsigned sp)%Z) /\ (bv_unsigned sp <= 2 ^ 47)%Z.
  Hypothesis Hwr : store_ok SEGS mem (Z_to_bv 64 (bv_unsigned sp - 16)) (Z.to_nat 16) = true.
  Hypothesis Hro : forall i, (0x20d00 <= i < 0x20f20)%Z -> mem (Z_to_bv 64 i) = None.
  Hypothesis Hsb : sbcell SEGS 0x9eaf0 0xa6bb8 mem.

  Let E : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI))
                                ++ [g; a; b; c; d; e; f; C])) (blobs_ev []).
  (* [comment removed for export] *)

  Definition kn0v1 : list kentry :=
    [KImg 0x20d00 0x20f20;
     KWord (SA (ELit 0) 0x9eaf0) 8 (ELit 0xa6bb8); KWord (SA (ELit 0) 0xa6bb8) 8 (ELit SB);
     KWord (SA (EVar 71) 4) 4 (EVar 64); KWord (SA (EVar 71) 8) 4 (EVar 65);
     KWord (SA (EVar 71) 12) 4 (EVar 66); KWord (SA (EVar 71) 16) 4 (EVar 67);
     KWord (SA (EVar 71) 20) 4 (EVar 68); KWord (SA (EVar 71) 24) 4 (EVar 69);
     KWord (SA (EVar 71) 28) 4 (EVar 70);
     KAlign (EVar 71) 8; KRange (EVar 71) 1 (2 ^ 47 - 32);
     KZero (SA (EAlu ALU_SRL (EVar 71) (ELit 3)) SB) (ELit 4);
     KRange (EVar 2) (AS_STKLO + 16) (2^47);
     KWr (SA (EVar 2) (-16)) 16].

  Lemma kn0v1_ok : know_ok SEGS E mem kn0v1.
  Proof using ceil FPI regs mem sp C g a b c d e f Hsp Hg Ha Hb Hc Hd He Hf HCal HCrange HshC Hsprange Hwr Hro Hsb.
    unfold kn0v1. pose proof (u64_range C). pose proof (u64_range sp).
    destruct Hsb as [Hg1 Hg2]. unfold cell64, cell in Hg1, Hg2.
    assert (V71 : edenot E (EVar 71) = C) by (cbn; reflexivity).
    unfold know_ok. repeat (apply Forall_cons); [..|apply Forall_nil].
    - apply kimg_intro; [lia|lia|exact Hro].
    - eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0x9eaf0 8 (ELit 0xa6bb8) (Z_to_bv 64 0xa6bb8)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0xa6bb8 8 (ELit SB) (Z_to_bv 64 SB)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (EVar 71) C 4 4 (EVar 64) g); cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (EVar 71) C 8 4 (EVar 65) a); cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (EVar 71) C 12 4 (EVar 66) b); cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (EVar 71) C 16 4 (EVar 67) c); cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (EVar 71) C 20 4 (EVar 68) d); cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (EVar 71) C 24 4 (EVar 69) e); cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (EVar 71) C 28 4 (EVar 70) f); cbn; try lia; auto.
    - apply kalign_intro; [lia|]. rewrite V71. exact HCal.
    - apply krange_intro. rewrite V71. lia.
    - eapply (kzero_shz_intro SEGS E mem (EVar 71) C 4); [exact V71 | exact HshC | lia | lia].
    - apply krange_intro. cbn. rewrite Hsp. lia.
    - apply (kwr_intro SEGS E mem (EVar 2) sp (-16) 16); cbn; try lia; auto.
  Qed.

  Definition kn0 : list kentry := kn0v1 ++
    [KDisj (SA (EVar 71) 0) 32 ZSH ZSHL; KDisj (SA (EVar 71) 0) 32 ZIMG ZIMGL;
     KDisj (SA (EVar 71) 0) 32 (SA (EVar 2) (-16)) 16].
  Lemma kn0_ok : know_ok SEGS E mem kn0.
  Proof using ceil FPI regs mem sp C g a b c d e f Hsp Hg Ha Hb Hc Hd He Hf HCal HCrange HshC Hsprange Hwr Hro Hsb. apply know_ok_app; [exact kn0v1_ok | kn_place]. Qed.

  (* [comment removed for export] *)
  Lemma idx_cases : forall u, (0 <= u < 2 ^ 64)%Z ->
    u = (2^64 - 6)%Z \/ u = (2^64 - 5)%Z \/ u = (2^64 - 4)%Z \/ u = (2^64 - 3)%Z \/ u = (2^64 - 2)%Z
    \/ (4 < (6 + u) mod 2 ^ 64)%Z.
  Proof using C.
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
      msteps SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x80624) mem rom)
                  (mkst (FP:=FPI') regs' ret mem' rom)
      /\ regs_kept abi_kept regs regs'
      /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI'))
      /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 16), 16%Z)].
  Proof using ceil FPI regs mem rom ret sp C g a b c d e f Hra Hret Hsp Htf H11 H12 Hg Ha Hb Hc Hd He Hf HCal HCrange HshC Hsprange Hwr Hro Hsb.
    apply runs_to_contract with
      (P := fun FPI' regs' mem' => regs_kept abi_kept regs regs'
              /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI')) /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 16), 16%Z)]).
    assert (HR0 : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [])).
    assert (HR : regs_ok E (sr_upd (sr_upd (sr_upd (sr_vars 0) 11 (ELit 0)) 12 (ELit 0)) 10 (EAlu ALU_ADD (EVar 71) (ELit 4))) regs).
    { apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [exact HR0|]|]|]; cbn [edenot];
        [exact H11 | exact H12 | ev_simpl E; rewrite Htf, alu_add_lit; reflexivity]. }
    pose proof (HR0 : id _) as HRid. clear HR0. pose proof (HF : id _) as HFid.
    pose proof kn0_ok as HK.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range C) as Htfr.
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
    run_fp 200%nat [0x80778%Z] noscr false.
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok _ ?sr ?R =>
      let e := eval vm_compute in (sr_get sr 14) in
      pose proof (reg_val E sr R 14 HR) as HX; change (sr_get sr 14) with e in HX;
      cbn [edenot fop1_denot fop2_denot fop3_denot] in HX; ev_simpl_in E HX
    end.
    lazymatch type of HX with getr ?R 14 = ?X =>
      destruct (idx_cases (bv_unsigned X) (u64_range X)) as [Hv|[Hv|[Hv|[Hv|[Hv|Hgen]]]]];
      [ .. | clear HX ]
    end.
    1-5: lazymatch goal with HR : regs_ok _ ?sr ?R |- _ =>
           lazymatch type of Hv with bv_unsigned ?X = ?v =>
             pose proof (regs_ok_pin E sr R 14 (ELit v) HR
                           ltac:(cbn [edenot]; rewrite HX, <- Hv, Z_to_bv_bv_unsigned; reflexivity)) as HR';
             clear HR HX; rename HR' into HR
           end end.
    1-5: crawl 10%nat.
    (* [comment removed for export] *)
    run_fp 200%nat (@nil Z) noscr false.
    branch_case as Hc3; [|crawl 3%nat].
    run_fp 200%nat (@nil Z) (dirs [true]) false
      by (apply Z.ltb_lt; eapply Z.lt_le_trans; [exact Hgen|]; apply Z.eq_le_incl; f_equal; lia).
    fin_ret. post.
  Qed.
End Proof.

Theorem classify_as_ok : forall ceil, classify_contract_as SEGS as_asan ceil.
Proof.
  intros ceil sp C FPI regs mem rom ret Hra Hret PRE.
  destruct PRE as (Hsp & Htf & H11 & H12 & (g & a & b & c & d & e & f & Hg & Ha & Hb & Hc & Hd & He & Hf)
                   & HCal & HCheap & HshC & Hro & Hsb & Hfr).
  destruct Hfr as (Hstk & Hspal & (Hw0 & _ & _ & Hst)). unfold CLASSIFY_D, heapish, stackish in *. app_facts.
  apply (as_sb_asan SEGS mem) in Hsb.
  unfold cell in *.
  destruct (classify_ok ceil FPI regs mem rom ret sp C g a b c d e f Hra Hret Hsp Htf H11 H12
              Hg Ha Hb Hc Hd He Hf HCal ltac:(plc) HshC ltac:(plc) Hst
              ltac:(intros i Hi; apply (Hro 0x20d00%Z 0x20f20%Z i); [first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)] | exact Hi]) Hsb)
    as (FPI' & regs' & mem' & Hms & Hk1 & Hk2 & Hfr).
  exists FPI', regs', mem'. unfold classify_post_as, CLASSIFY_D. auto.
Qed.
