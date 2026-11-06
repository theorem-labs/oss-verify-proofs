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
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs LibTagsSpec.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs BoBase AsLibTagsLib BoLibSpec AsLibPlace.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymDriveLZ.
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
Import ListNotations.
Open Scope bv_scope.
Import ASX. Import ASXS.
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

Section USABLE.
  Variable ceil : Z.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp P : word) (h4 h5 h6 : Z).

  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis HP : getr regs 10 = P.
  Hypothesis Hpal : (bv_unsigned P mod 8 = 0)%Z.
  Hypothesis HPrange : (appm (bv_unsigned P) 976 /\ (0 < bv_unsigned P)%Z) /\ (bv_unsigned P + 976 <= ceil)%Z.
  Hypothesis HshP : shz mem (bv_unsigned P) 122.
  Hypothesis H4 : cell SEGS mem (bv_unsigned P + 964) 1 (Z_to_bv 64 h4).
  Hypothesis H5 : cell SEGS mem (bv_unsigned P + 965) 1 (Z_to_bv 64 h5).
  Hypothesis H6 : cell SEGS mem (bv_unsigned P + 966) 1 (Z_to_bv 64 h6).
  Hypothesis Hh4 : (h4 = 0 \/ h4 = 1)%Z.
  Hypothesis Hh5 : (h5 = 0 \/ h5 = 1)%Z.
  Hypothesis Hh6 : (h6 = 0 \/ h6 = 1)%Z.
  Hypothesis Hsprange : ((AS_STKLO <= ceil)%Z /\ (ceil + 16 <= bv_unsigned sp)%Z) /\ (bv_unsigned sp <= 2 ^ 47)%Z.
  Hypothesis Hstk : RiscvSemantics.store_ok SEGS mem (Z_to_bv 64 (bv_unsigned sp - 16)) 16 = true.
  Hypothesis Hsb : sbcell SEGS 0x9f920 0xa79b8 mem.

  Let E : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ [])) (blobs_ev []).

  Definition kn0 (v4 v5 v6 : Z) : list kentry :=
    [KWord (SA (ELit 0) 0x9f920) 8 (ELit 0xa79b8); KWord (SA (ELit 0) 0xa79b8) 8 (ELit SB);
     KAlign (EVar 10) 8; KRange (EVar 10) 1 (2 ^ 47 - 976);
     KRange (EVar 2) (AS_STKLO + 16) (2 ^ 47); KWr (SA (EVar 2) (-16)) 16;
     KZero (SA (EAlu ALU_SRL (EVar 10) (ELit 3)) (SB + 120)) (ELit 1);
     KWord (SA (EVar 10) 964) 1 (ELit v4); KWord (SA (EVar 10) 965) 1 (ELit v5); KWord (SA (EVar 10) 966) 1 (ELit v6)].

  Lemma kn0_ok : know_ok SEGS E mem (kn0 h4 h5 h6).
  Proof using ceil FPI regs mem rom sp P h4 h5 h6 Hsp HP Hpal HPrange HshP H4 H5 H6 Hsprange Hstk Hsb.
    unfold kn0. pose proof (u64_range P). pose proof (u64_range sp).
    destruct Hsb as [Hg Hs]. unfold cell64, cell in Hg, Hs. unfold cell in H4, H5, H6.
    unfold know_ok. repeat lazymatch goal with |- Forall _ (_ :: _) => constructor | |- Forall _ [] => constructor end.
    all: lazymatch goal with |- Forall _ _ => fail | _ => idtac end.
    - eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0x9f920 8 (ELit 0xa79b8) (Z_to_bv 64 0xa79b8)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0xa79b8 8 (ELit SB) (Z_to_bv 64 SB)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
    - apply kalign_intro; [lia|]. cbn. rewrite HP. exact Hpal.
    - apply krange_intro. cbn. rewrite HP. lia.
    - apply krange_intro. cbn. rewrite Hsp. lia.
    - apply (kwr_intro SEGS E mem (EVar 2) sp (-16) 16); cbn; try lia; auto.
    - eapply (kzero_shadow_intro SEGS E mem (EVar 10) P 120 1); [cbn; exact HP | lia | lia | unfold SB; lia |].
      intros j Hj. destruct HshP as [_ Hz]. apply Hz. lia.
    - eapply (kword_intro SEGS E mem (EVar 10) P 964 1 (ELit h4) (Z_to_bv 64 h4)); cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (EVar 10) P 965 1 (ELit h5) (Z_to_bv 64 h5)); cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (EVar 10) P 966 1 (ELit h6) (Z_to_bv 64 h6)); cbn; try lia; auto.
  Qed.

  Definition RS : list (saddr * Z) := [(SA (EVar 2) (-16), 16%Z)].
  Lemma RS_denot : regions_denot E RS = [(Z_to_bv 64 (bv_unsigned sp - 16), 16%Z)].
  Proof using FPI regs sp Hsp.
    unfold regions_denot, RS. cbn [map fst snd]. unfold adenot. cbn [a_base a_off edenot]. ev_simpl E.
    rewrite Hsp. unfold v_addi. reflexivity.
  Qed.

  Ltac post :=
    lazymatch goal with
    | |- exists FPI' regs' mem', @mkst ?FPI ?R _ ?M _ = _ /\ _ =>
      lazymatch goal with
      | HR : regs_ok ?E _ R, HF : fregs_ok _ _ (@fp_regs FPI), HR0 : id (regs_ok _ ?sr0 ?regs), HF0 : id (fregs_ok _ ?sfr0 ?fr),
        EQM : M = mem_denot _ ?M0 ?log |- _ =>
        exists FPI, R, M; split; [| split; [|split; [|split]]]; unfold regs_kept, fregs_kept;
        [ regv HR (1%bv:reg); rewrite_getr; reflexivity
        | eapply (regs_same_on E sr0 _ regs R abi_kept); [ exact HR0 | exact HR | vm_compute; reflexivity ]
        | eapply (fregs_same_on E sfr0 _ fr _ abi_fkept); [ exact HF0 | exact HF | vm_compute; reflexivity ]
        | rewrite EQM, <- RS_denot; apply (frame_mod_mem_denot E M0 log RS);
          [ assumption | flats_auto | vm_compute; reflexivity ]
        | eexists; split; [regv HR (10%bv:reg); reflexivity | lia] ]
      end
    end.

  Theorem usable_run_ok :
    exists (FPI' : FPState) regs' mem',
      msteps SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x87418) mem rom)
                  (mkst (FP:=FPI') regs' ret mem' rom)
      /\ regs_kept abi_kept regs regs'
      /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI'))
      /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 16), 16%Z)]
      /\ exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1)%Z.
  Proof using ceil FPI regs mem rom ret sp P h4 h5 h6 Hra Hret Hsp HP Hpal HPrange HshP H4 H5 H6 Hh4 Hh5 Hh6 Hsprange Hstk Hsb.
    apply runs_to_contract with
      (P := fun FPI' regs' mem' => regs_kept abi_kept regs regs'
              /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI')) /\
              frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 16), 16%Z)] /\
              exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1)%Z).
    assert (HR : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof (u64_range P). pose proof (u64_range sp).
    pose proof kn0_ok as HK.
    destruct Hh6 as [E6 | E6]; rewrite E6 in HK;
      destruct Hh4 as [E4 | E4]; rewrite E4 in HK;
        destruct Hh5 as [E5 | E5]; rewrite E5 in HK; unfold kn0 in HK;
          run_fp 120%nat (@nil Z) noscr true; fin_ret; post.
  Qed.
End USABLE.

Theorem usable_bo_ok : forall ceil, usable_contract_bo SEGS as_both ceil.
Proof.
  intros ceil P sp FPI regs mem rom ret Hra Hret PRE.
  destruct PRE as (Hsp & HP & Hpal & Hheap & HshP & (h4 & [R4 H4] & Hh4) & (h5 & [R5 H5] & Hh5) & (h6 & [R6 H6] & Hh6) & Hsb & Hfr).
  apply (as_sb_both SEGS mem) in Hsb.
  destruct Hfr as ([Hst1 Hst2] & Hsal & (_ & _ & _ & Hwr)).
  unfold heapish, stackish in *. app_facts.
  destruct (usable_run_ok ceil FPI regs mem rom ret sp P h4 h5 h6 Hra Hret Hsp HP Hpal ltac:(plc) HshP H4 H5 H6 Hh4 Hh5 Hh6
              ltac:(plc) Hwr Hsb)
    as (FPI' & regs' & mem' & Hms & Hk1 & Hk2 & Hmem & Hr).
  exists FPI', regs', mem'. split; [exact Hms|]. split; [exact Hk1|]. split; [exact Hk2|]. split; [exact Hmem | exact Hr].
Qed.
