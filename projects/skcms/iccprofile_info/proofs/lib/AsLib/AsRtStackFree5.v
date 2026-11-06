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
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs AsRtSpec AsLibPlace.
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

(* [comment removed for export] *)
Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

#[local] Abbreviation SEGS := Asan.M.loaded_segments.

Section Free5.
  Variable ceil : Z.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp F flagp mid : word).

  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis Ha0 : getr regs 10 = F.
  Hypothesis HFal : (bv_unsigned F mod 2048 = 0)%Z.
  Hypothesis HFrange : (appm (bv_unsigned F) 2048 /\ (0 < bv_unsigned F)%Z) /\ (bv_unsigned F + 2048 <= ceil)%Z.
  Hypothesis Hflagp : rdn SEGS mem (Z_to_bv 64 (bv_unsigned F + 2040)) 8 = Some (word_to_le_bytes 8 flagp).
  Hypothesis Hfprange : (appm (bv_unsigned flagp) 1 /\ (0 < bv_unsigned flagp)%Z) /\ (bv_unsigned flagp + 1 <= ceil)%Z.
  Hypothesis Hfpw : RiscvSemantics.store_ok SEGS mem (Z_to_bv 64 (bv_unsigned flagp)) 1 = true.
  Hypothesis Hshw : RiscvSemantics.store_ok SEGS mem (Z_to_bv 64 (SB + bv_unsigned F / 8)) 256 = true.
  Hypothesis Hg308 : rdn SEGS mem (Z_to_bv 64 0x9eaf0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xa6bb8)).
  Hypothesis Hsb   : rdn SEGS mem (Z_to_bv 64 0xa6bb8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 SB)).
  Hypothesis Hg310 : rdn SEGS mem (Z_to_bv 64 0x9eaf8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xa78a8)).
  Hypothesis Hmidb : rdn SEGS mem (Z_to_bv 64 0xa78a8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Hypothesis Hg318 : rdn SEGS mem (Z_to_bv 64 0x9eb00) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xa78b0)).
  Hypothesis Hmide : rdn SEGS mem (Z_to_bv 64 0xa78b0) 8 = Some (word_to_le_bytes 8 mid).
  Hypothesis Hg320 : rdn SEGS mem (Z_to_bv 64 0x9eb08) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xa78a0)).
  Hypothesis Hhigh : rdn SEGS mem (Z_to_bv 64 0xa78a0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff)).
  Hypothesis Hro : forall i, (0x10338 <= i < 0x10340)%Z -> mem (Z_to_bv 64 i) = None.
  Hypothesis Hsprange : ((AS_STKLO <= ceil)%Z /\ (ceil + 16 <= bv_unsigned sp)%Z) /\ (bv_unsigned sp <= 2 ^ 47)%Z.
  Hypothesis Hstk : RiscvSemantics.store_ok SEGS mem (Z_to_bv 64 (bv_unsigned sp - 16)) 16 = true.

  Let E : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ [F; flagp; mid])) (blobs_ev []).

  Definition kn0v1 : list kentry :=
    [KWord (SA (ELit 0) 0x9eaf0) 8 (ELit 0xa6bb8); KWord (SA (ELit 0) 0xa6bb8) 8 (ELit SB);
     KWord (SA (ELit 0) 0x9eaf8) 8 (ELit 0xa78a8); KWord (SA (ELit 0) 0xa78a8) 8 (ELit 0);
     KWord (SA (ELit 0) 0x9eb00) 8 (ELit 0xa78b0); KWord (SA (ELit 0) 0xa78b0) 8 (EVar 66);
     KWord (SA (ELit 0) 0x9eb08) 8 (ELit 0xa78a0); KWord (SA (ELit 0) 0xa78a0) 8 (ELit 0x7fffffffffff);
     KImg 0x10338 0x10340;
     KWord (SA (EVar 10) 2040) 8 (EVar 65); KAlign (EVar 10) 2048; KRange (EVar 10) 1 (2 ^ 47 - 2048);
     KRange (EVar 65) 1 (2 ^ 47 - 1); KWr (SA (EVar 65) 0) 1;
     KWr (SA (EAlu ALU_SRL (EVar 10) (ELit 3)) SB) 256;
     KRange (EVar 2) (AS_STKLO + 16) (2 ^ 47); KWr (SA (EVar 2) (-16)) 16].

  Lemma kn0v1_ok : know_ok SEGS E mem kn0v1.
  Proof using ceil FPI regs mem rom sp F flagp mid Hsp Ha0 HFal HFrange Hflagp Hfprange Hfpw Hshw Hg308 Hsb Hg310 Hmidb Hg318 Hmide Hg320 Hhigh Hro Hsprange Hstk.
    unfold kn0v1, know_ok. pose proof (u64_range F). pose proof (u64_range flagp). pose proof (u64_range sp).
    repeat lazymatch goal with |- Forall _ (_ :: _) => constructor | |- Forall _ [] => constructor end.
    all: lazymatch goal with |- Forall _ _ => fail | _ => idtac end.
    - eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0x9eaf0 8 _ (Z_to_bv 64 0xa6bb8)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0xa6bb8 8 _ (Z_to_bv 64 SB)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0x9eaf8 8 _ (Z_to_bv 64 0xa78a8)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0xa78a8 8 _ (Z_to_bv 64 0)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0x9eb00 8 _ (Z_to_bv 64 0xa78b0)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0xa78b0 8 _ mid); cbn; rewrite ?u_lit0; cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0x9eb08 8 _ (Z_to_bv 64 0xa78a0)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0xa78a0 8 _ (Z_to_bv 64 0x7fffffffffff)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
    - apply kimg_intro; [lia|lia|exact Hro].
    - eapply (kword_intro SEGS E mem (EVar 10) F 2040 8 (EVar 65) flagp); cbn; try lia; auto.
    - apply kalign_intro; [lia|]. cbn. rewrite Ha0. exact HFal.
    - apply krange_intro. cbn. rewrite Ha0. lia.
    - apply krange_intro. cbn. lia.
    - apply (kwr_intro SEGS E mem (EVar 65) flagp 0 1); cbn; try lia; auto. rewrite ?Z.add_0_r. exact Hfpw.
    - replace SB with (SB + 0)%Z by lia. eapply (kwr_shadow_intro SEGS E mem (EVar 10) F 0 256); [cbn; exact Ha0 | lia | lia | | rewrite ?Z.add_0_r; exact Hshw].
      assert (bv_unsigned F / 8 < 2 ^ 44)%Z by (apply Z.div_lt_upper_bound; lia). lia.
    - apply krange_intro. cbn. rewrite Hsp. lia.
    - apply (kwr_intro SEGS E mem (EVar 2) sp (-16) 16); cbn; try lia; auto.
  Qed.

  Definition kn0 : list kentry := kn0v1 ++
    [KDisj (SA (EVar 10) 0) 2048 ZSH ZSHL; KDisj (SA (EVar 10) 0) 2048 ZIMG ZIMGL;
     KDisj (SA (EVar 10) 0) 2048 (SA (EVar 2) (-16)) 16;
     KDisj (SA (EVar 65) 0) 1 ZSH ZSHL; KDisj (SA (EVar 65) 0) 1 ZIMG ZIMGL;
     KDisj (SA (EVar 65) 0) 1 (SA (EVar 2) (-16)) 16].
  Lemma kn0_ok : know_ok SEGS E mem kn0.
  Proof using ceil FPI regs mem rom sp F flagp mid Hsp Ha0 HFal HFrange Hflagp Hfprange Hfpw Hshw Hg308 Hsb Hg310 Hmidb Hg318 Hmide Hg320 Hhigh Hro Hsprange Hstk. apply know_ok_app; [exact kn0v1_ok | kn_place]. Qed.

  Definition RS : list (saddr * Z) := [(SA (EVar 2) (-16), 16%Z); (SA (EVar 65) 0, 1%Z); (SA (EAlu ALU_SRL (EVar 10) (ELit 3)) SB, 256%Z)].
  Lemma RS_denot : regions_denot E RS =
     [(Z_to_bv 64 (bv_unsigned sp - 16), 16%Z); (flagp, 1%Z); (Z_to_bv 64 (AS_SB + bv_unsigned F / 8), 256%Z)].
  Proof using FPI regs sp F flagp mid Hsp Ha0.
    unfold regions_denot, RS. cbn [map fst snd]. unfold adenot. cbn [a_base a_off edenot]. ev_simpl E.
    rewrite Hsp, Ha0. unfold v_addi. rewrite u_srl3. unfold AS_SB, SB. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite (Z.add_comm 2147450880 (bv_unsigned F / 8)). reflexivity.
  Qed.

  Theorem free5_run_ok :
    exists (FPI' : FPState) regs' mem',
      msteps SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x3cc54) mem rom)
                  (mkst (FP:=FPI') regs' ret mem' rom)
      /\ regs_kept abi_kept regs regs'
      /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI'))
      /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 16), 16%Z); (flagp, 1%Z); (Z_to_bv 64 (AS_SB + bv_unsigned F / 8), 256%Z)]
      /\ mem' flagp = Some (Z_to_bv 8 0).
  Proof using ceil FPI regs mem rom ret sp F flagp mid Hra Hret Hsp Ha0 HFal HFrange Hflagp Hfprange Hfpw Hshw Hg308 Hsb Hg310 Hmidb Hg318 Hmide Hg320 Hhigh Hro Hsprange Hstk.
    apply runs_to_contract with
      (P := fun FPI' regs' mem' => regs_kept abi_kept regs regs'
              /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI'))
              /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 16), 16%Z); (flagp, 1%Z); (Z_to_bv 64 (AS_SB + bv_unsigned F / 8), 256%Z)]
              /\ mem' flagp = Some (Z_to_bv 8 0)).
    assert (HR : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof (u64_range F). pose proof (u64_range flagp). pose proof (u64_range sp).
    pose proof kn0_ok as HK0.
    (* [comment removed for export] *)
    destruct (app_sh_lit _ _ (proj1 (proj1 HFrange))) as [HZ|HZ];
      [ assert (HK : know_ok SEGS E mem (KRange (EVar 10) 1 (0x7fff7000 - 2048) :: kn0))
          by (constructor; [apply krange_intro; cbn; rewrite Ha0; lia | exact HK0])
      | assert (HK : know_ok SEGS E mem (KRange (EVar 10) 0x10007fff8000 (2 ^ 47 - 2048) :: kn0))
          by (constructor; [apply krange_intro; cbn; rewrite Ha0; lia | exact HK0]) ]; clear HK0.
    all: run_fp 200%nat (@nil Z) noscr true.
    all: fin_ret.
    all: exists FPI0, R, M; split; [| split; [|split; [|split]]]; unfold regs_kept, fregs_kept;
      [ regv HR (1%bv:reg); rewrite_getr; reflexivity
      | eapply (regs_same_on E _ _ regs R abi_kept); [ exact HR0 | exact HR | vm_compute; reflexivity ]
      | eapply (fregs_same_on E _ _ _ _ abi_fkept); [ exact HF0 | exact HF | vm_compute; reflexivity ]
      | rewrite EQM, <- RS_denot; apply (frame_mod_mem_denot E _ _ RS); [ exact HLF | flats_auto; rewrite ?u_srl3; unfold SB; lia | vm_compute; reflexivity ]
      | rewrite EQM, <- (Z_to_bv_bv_unsigned 64 flagp); rewrite <- (Z.add_0_r (bv_unsigned flagp));
        change (bv_unsigned flagp) with (bv_unsigned (edenot E (EVar 65)));
        eapply (mem_denot_lzK_cover SEGS E _ _ _ _ (EVar 65) 0 1%nat HK HLF); [vm_compute; reflexivity | cbn; lia | cbn; lia | lia] ].
  Qed.
End Free5.

Lemma areadable8_word : forall segs mem a,
  areadable segs mem a 8 -> exists w : word, rdn segs mem (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 w).
Proof.
  intros segs mem a [bs Hbs]. exists (Z_to_bv 64 (bytes_le_to_Z bs)).
  rewrite word_to_le_bytes_of_lez; [exact Hbs | exact (rdn_length _ _ _ _ _ Hbs) | lia].
Qed.

Theorem stkfree5_asan : forall ceil, stkfree5_contract SEGS as_asan ceil.
Proof.
  intros ceil F flagp FPI regs mem rom ret Hra Hret PRE.
  destruct PRE as (Ha0 & HFal & HFr & Hfp & Hfpr & Hfpw & Hshw & Henv & Hro & (sp & Hsp & Hfr)).
  destruct Henv as (C64 & C32 & C8 & R64).
  destruct Hfr as ([Hst1 Hst2] & Hsal & (_ & _ & _ & Hwr)).
  destruct Hfpw as (_ & _ & _ & Hfpw). destruct Hshw as (_ & _ & _ & Hshw).
  destruct (areadable8_word SEGS mem 0xa78b0 (R64 _ ltac:(first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)]))) as [mid Hmid].
  pose proof (C64 0x9eaf0%Z 0xa6bb8%Z ltac:(first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)])) as E1.
  pose proof (C64 0xa6bb8%Z AS_SB ltac:(first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)])) as E2.
  pose proof (C64 0x9eaf8%Z 0xa78a8%Z ltac:(first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)])) as E3.
  pose proof (C64 0xa78a8%Z 0%Z ltac:(first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)])) as E4.
  pose proof (C64 0x9eb00%Z 0xa78b0%Z ltac:(first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)])) as E5.
  pose proof (C64 0x9eb08%Z 0xa78a0%Z ltac:(first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)])) as E6.
  pose proof (C64 0xa78a0%Z 0x7fffffffffff%Z ltac:(first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)])) as E7.
  unfold acell in E1, E2, E3, E4, E5, E6, E7. unfold acellw in Hfp.
  unfold heapish, AS_SB, SB in *. app_facts.
  destruct (free5_run_ok ceil FPI regs mem rom ret sp F flagp mid Hra Hret Hsp Ha0 HFal ltac:(plc) Hfp ltac:(plc) Hfpw Hshw
             E1 E2 E3 E4 E5 Hmid E6 E7
             ltac:(intros i Hi; apply (Hro 0x10338%Z 0x10340%Z i); [first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)] | exact Hi]) ltac:(plc) Hwr)
    as (FPI' & regs' & mem' & Hms & Hk1 & Hk2 & Hfm & Hz).
  exists FPI', regs', mem'. split; [exact Hms|]. split; [exact Hk1|]. split; [exact Hk2|].
  unfold stkfree5_post. rewrite Hsp. split; [exact Hfm | exact Hz].
Qed.
