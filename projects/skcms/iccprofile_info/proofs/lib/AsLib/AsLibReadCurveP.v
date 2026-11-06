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
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs LibFrame.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs AsRtSpec AsLibFrame AsLibEnv AsLibFPLib AsLibTagsLib AsLibTagsCall AsLibReadCurveLib AsLibCurveSpec AsLibReadCurveK AsLibPlace.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymDriveLZ.
Import ListNotations.
Open Scope bv_scope.
Import ASX. Import ASXS.
(* [comment removed for export] *)
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

(* [comment removed for export] *)
Ltac kread_fact HK b k n H :=
  lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
    let r := eval vm_compute in (kread segs kn b k n) in
    lazymatch r with
    | Some ?v =>
        let Hfl := fresh "Hfl" in
        assert (Hfl : flat E (SA b k) (Z.of_nat n));
        [ unfold flat, estart, elenZ; cbn [a_base a_off edenot Z.of_nat Pos.of_succ_nat Pos.succ]; ev_simpl E;
          rewrite_getr; try lia
        | pose proof (kread_rdn segs E M kn b k n v HK
                        ltac:(vm_cast_no_check (@eq_refl (option expr) (Some v)))
                        ltac:(repeat constructor) ltac:(repeat constructor) Hfl) as H;
          clear Hfl; unfold adenot in H; cbn [a_base a_off edenot] in H; ev_simpl_in E H ]
    | None => fail "kread: no knowledge entry covers this range"
    end
  end.

#[local] Abbreviation SEGS := Asan.M.loaded_segments.
#[local] Abbreviation IMEMSET := 0x514d0%Z.
#[local] Abbreviation TAILK := 0x833a4%Z.
#[local] Abbreviation EXIT0 := 0x82c84%Z.

Section TailP.
  Variable ceil : Z.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret data : word) (len : Z) (bs : list byte) (sp buf C cs : word) (size : Z).
  (* [comment removed for export] *)
  Hypothesis Hmemset : imemset20_contract SEGS as_asan ceil.
  Hypothesis Hclassify : classify_contract_as SEGS as_asan ceil.
  (* [comment removed for export] *)
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis Hdok : data_ok mem data len bs.
  Hypothesis Hdheap : (appm (bv_unsigned data) len /\ (0 < bv_unsigned data)%Z) /\ (bv_unsigned data + len <= ceil)%Z.
  Hypothesis Hshd : shdata mem (bv_unsigned data) len.
  Hypothesis Hsize : (0 <= size < 2 ^ 32)%Z.
  Hypothesis Hin : inDATA data len (bv_unsigned buf) size.
  Hypothesis HWC : writable SEGS mem (bv_unsigned C) 32.
  Hypothesis HCal : (bv_unsigned C mod 8 = 0)%Z.
  Hypothesis HCheap : (appm (bv_unsigned C) 32 /\ (0 < bv_unsigned C)%Z) /\ (bv_unsigned C + 32 <= ceil)%Z.
  Hypothesis HshC : shz mem (bv_unsigned C) 4.
  Hypothesis HshwC : shwz mem (bv_unsigned C + 12) 20.
  Hypothesis Henv : env_cells SEGS asan_abi mem.
  Hypothesis Hro : env_ro asan_abi mem.
  Hypothesis Hsb : sbcell SEGS 0x9eaf0 0xa6bb8 mem.
  Hypothesis Hstk : ((AS_STKLO <= ceil)%Z /\ (ceil + 2208 <= bv_unsigned sp)%Z) /\ (bv_unsigned sp <= 2 ^ 47)%Z.
  Hypothesis Hspal : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis HWS : writable SEGS mem (bv_unsigned sp - 2208) 2208.
  Hypothesis HDC : (bv_unsigned data + len <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned data)%Z.
  Hypothesis Hcs : (bv_unsigned cs = 0)%Z \/
   (writable SEGS mem (bv_unsigned cs) 4 /\ (bv_unsigned cs mod 4 = 0)%Z /\
    (AS_STKLO <= ceil <= bv_unsigned cs /\ bv_unsigned cs + 4 <= 2 ^ 47)%Z /\
    shbyte mem (bv_unsigned cs) 0 /\ (bv_unsigned sp <= bv_unsigned cs)%Z).
  (* [comment removed for export] *)
  Variables (FPc : FPState) (R : bvmap 5 word) (M : word -> option byte).
  Variables (sp1 : word) (k : Z).
  Hypothesis Hsp1 : bv_unsigned sp1 = (bv_unsigned sp - 80)%Z.
  Hypothesis TR2 : getr R 2 = sp1.
  Hypothesis TR8 : getr R 8 = buf.
  Hypothesis TR18 : getr R 18 = C.
  Hypothesis TR21 : getr R 21 = Z_to_bv 64 SB.
  Hypothesis TR23 : getr R 23 = Z_to_bv 64 k.
  Hypothesis Hk : (0 <= k <= 4)%Z.
  Hypothesis Hszk : (12 + cb k <= size)%Z.
  Hypothesis TRK : forall r, In r rc_untouched -> getr R r = getr regs r.
  Hypothesis HFK : fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPc)).
  Hypothesis HM : frame_mod mem M ((Z_to_bv 64 (bv_unsigned sp - 2208), 2208%Z)
                                    :: (if Z.eq_dec (bv_unsigned cs) 0 then [] else [(cs, 4%Z)])).
  Hypothesis S72 : cell64 SEGS M (bv_unsigned sp - 8) ret.
  Hypothesis S64 : cell64 SEGS M (bv_unsigned sp - 16) (getr regs 8).
  Hypothesis S56 : cell64 SEGS M (bv_unsigned sp - 24) (getr regs 9).
  Hypothesis S48 : cell64 SEGS M (bv_unsigned sp - 32) (getr regs 18).
  Hypothesis S40 : cell64 SEGS M (bv_unsigned sp - 40) (getr regs 19).
  Hypothesis S32 : cell64 SEGS M (bv_unsigned sp - 48) (getr regs 20).
  Hypothesis S24 : cell64 SEGS M (bv_unsigned sp - 56) (getr regs 21).
  Hypothesis S16 : cell64 SEGS M (bv_unsigned sp - 64) (getr regs 22).
  Hypothesis S8 : cell64 SEGS M (bv_unsigned sp - 72) (getr regs 23).
  Hypothesis Hcsv : bv_unsigned cs <> 0%Z -> exists v, cell32 SEGS M (bv_unsigned cs) v.

  #[local] Abbreviation off := (bv_unsigned buf - bv_unsigned data)%Z.
  #[local] Abbreviation Lk := (12 + cb k)%Z.

  Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPc))
                                ++ [ret; getr regs 8; getr regs 9; getr regs 18; getr regs 19;
                                    getr regs 20; getr regs 21; getr regs 22; getr regs 23; data; Z_to_bv 64 len]))
                     (blobs_ev [sub bs off 16; sub bs off Lk]).
  (* [comment removed for export] *)

  Definition knP : list kentry :=
    [KRange (EVar 2) (AS_STKLO + 2128) (2^47 - 80);
     KRange (EVar 18) 1 (2 ^ 47 - 32); KAlign (EVar 18) 8;
     KRange (EVar 8) 1 (2 ^ 47 - 2048);
     KWord (SA (EVar 2) 72) 8 (EVar 64);
     KWord (SA (EVar 2) 64) 8 (EVar 65);
     KWord (SA (EVar 2) 56) 8 (EVar 66);
     KWord (SA (EVar 2) 48) 8 (EVar 67);
     KWord (SA (EVar 2) 40) 8 (EVar 68);
     KWord (SA (EVar 2) 32) 8 (EVar 69);
     KWord (SA (EVar 2) 24) 8 (EVar 70);
     KWord (SA (EVar 2) 16) 8 (EVar 71);
     KWord (SA (EVar 2) 8) 8 (EVar 72);
     KWr (SA (EVar 2) (-2128)) 2208;
     KWr (SA (EVar 18) 0) 32;
     KZero (SA (EAlu ALU_SRL (EVar 18) (ELit 3)) SB) (ELit 4);
     KDisj (SA (EVar 18) 0) 32 (SA (EVar 8) 0) 16;
     KImg 0x20d00 0x20f20;
     KRange (EVar 73) 1 (2 ^ 47 - 2048); KRange (EVar 74) 0 (2^26); KShad (EVar 73) (EVar 74) SB;
     KBlob (SA (EVar 8) 0) (ELit 16) 0;
     KRange (EAlu ALU_ADD (EVar 73) (EVar 74)) 0 (2 ^ 47 - 2048);
     KDisj (SA (EVar 18) 0) 32 ZSH ZSHL; KDisj (SA (EVar 18) 0) 32 ZIMG ZIMGL; KDisj (SA (EVar 18) 0) 32 (SA (EVar 2) (-2128)) 2208;
     KDisj (SA (EVar 8) 0) 16 ZSH ZSHL; KDisj (SA (EVar 8) 0) 16 ZIMG ZIMGL; KDisj (SA (EVar 8) 0) 16 (SA (EVar 2) (-2128)) 2208].

  (* [comment removed for export] *)
  Definition RSP : list (word * Z) := [(Z_to_bv 64 (bv_unsigned sp - 2208), 2128%Z); (C, 32%Z)].
  Definition RSPs : list (saddr * Z) := [(SA (EVar 2) (-2128), 2128%Z); (SA (EVar 18) 0, 32%Z)].
  Lemma RSPs_denot : regions_denot E RSPs = RSP.
  Proof using ceil regs mem ret data len bs sp buf C cs HCheap Hstk Hcs FPc R sp1 k Hsp1 TR2 TR18.
    pose proof (u64_range sp).
    cbn [regions_denot map fst snd RSPs]. unfold adenot, RSP. cbn [a_base a_off edenot]. ev_simpl E.
    rewrite TR2, TR18. unfold v_addi. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. repeat f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma HM_heaphigh : high_regions
                         ((Z_to_bv 64 (bv_unsigned sp - 2208), 2208%Z) :: (if Z.eq_dec (bv_unsigned cs) 0 then [] else [(cs, 4%Z)])).
  Proof using ceil mem sp C cs HCheap Hstk Hcs M HM.
    pose proof (u64_range sp). pose proof (u64_range cs).
    destruct (Z.eq_dec (bv_unsigned cs) 0).
    - repeat (apply Forall_cons); [..|apply Forall_nil]; zfree_tac.
    - destruct Hcs as [?|(_ & _ & Hcsr & _)]; [lia|].
      repeat (apply Forall_cons); [..|apply Forall_nil]; zfree_tac.
  Qed.
  Lemma HM_high : high_regions ((Z_to_bv 64 (bv_unsigned sp - 2208), 2208%Z) :: (if Z.eq_dec (bv_unsigned cs) 0 then [] else [(cs, 4%Z)])).
  Proof using ceil mem sp C cs HCheap Hstk Hcs M HM. exact HM_heaphigh. Qed.
  Lemma RSP_heaphigh : high_regions RSP.
  Proof using ceil data len sp C cs Hdheap HCheap Hstk. pose proof (u64_range sp). unfold RSP. repeat (apply Forall_cons); [..|apply Forall_nil]; zfree_tac. Qed.
  Lemma RSP_high : high_regions RSP.
  Proof using ceil data len sp C cs Hdheap HCheap Hstk. exact RSP_heaphigh. Qed.

  Lemma knP_ok : know_ok SEGS E M knP.
  Proof using ceil regs mem rom ret data len bs sp buf C cs size Hdok Hdheap Hshd Hsize Hin HWC HCal HCheap HshC Hro Hstk HWS HDC Hcs FPc R M sp1 k Hsp1 TR2 TR8 TR18 Hk Hszk HM S72 S64 S56 S48 S40 S32 S24 S16 S8.
    clear Hcsv HFK TRK.
    unfold knP. pose proof (u64_range sp). pose proof (u64_range C). pose proof (u64_range buf). pose proof (u64_range data).
    pose proof HWS as (W1 & W2 & W3 & W4). pose proof HWC as (V1 & V2 & V3 & V4).
    pose proof Hdok as (D1 & D2 & D3 & D4 & D5). pose proof Hin as (I1 & I2 & I3). pose proof (cb_range k).
    unfold cell64, cell in S72, S64, S56, S48, S40, S32, S24, S16, S8.
    unfold know_ok.
    repeat (apply Forall_cons); [..|apply Forall_nil].
    - apply krange_intro; cbn. rewrite TR2. lia.
    - apply krange_intro; cbn. rewrite TR18. lia.
    - apply kalign_intro; [lia|]. cbn. rewrite TR18. exact HCal.
    - apply krange_intro; cbn. rewrite TR8. lia.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 72 8 (EVar 64) ret);
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 72)%Z with (bv_unsigned sp - 8)%Z by lia. exact S72.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 64 8 (EVar 65) (getr regs 8));
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 64)%Z with (bv_unsigned sp - 16)%Z by lia. exact S64.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 56 8 (EVar 66) (getr regs 9));
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 56)%Z with (bv_unsigned sp - 24)%Z by lia. exact S56.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 48 8 (EVar 67) (getr regs 18));
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 48)%Z with (bv_unsigned sp - 32)%Z by lia. exact S48.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 40 8 (EVar 68) (getr regs 19));
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 40)%Z with (bv_unsigned sp - 40)%Z by lia. exact S40.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 32 8 (EVar 69) (getr regs 20));
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 32)%Z with (bv_unsigned sp - 48)%Z by lia. exact S32.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 24 8 (EVar 70) (getr regs 21));
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 24)%Z with (bv_unsigned sp - 56)%Z by lia. exact S24.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 16 8 (EVar 71) (getr regs 22));
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 16)%Z with (bv_unsigned sp - 64)%Z by lia. exact S16.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 8 8 (EVar 72) (getr regs 23));
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 8)%Z with (bv_unsigned sp - 72)%Z by lia. exact S8.
    - apply (kwr_intro SEGS E M (EVar 2) sp1 (-2128) 2208); [cbn; exact TR2 | lia | lia | lia |].
      replace (bv_unsigned sp1 + -2128)%Z with (bv_unsigned sp - 2208)%Z by lia.
      eapply frame_mod_store_ok; [exact HM | exact W4].
    - apply (kwr_intro SEGS E M (EVar 18) C 0 32); [cbn; exact TR18 | lia | lia | lia |].
      rewrite Z.add_0_r. eapply frame_mod_store_ok; [exact HM | exact V4].
    - eapply (kzero_shz_intro SEGS E M (EVar 18) C 4); [cbn; exact TR18 | | lia | lia].
      eapply shz_frame_high; [exact HM | apply HM_heaphigh | exact HshC | lia | lia | lia].
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite TR18, TR8. lia.
    - apply kimg_intro; [lia|lia|]. intros i Hi. apply (env_ro_frame_high mem M _ HM HM_high Hro 0x20d00%Z 0x20f20%Z i); [first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)] | exact Hi].
    - apply krange_intro; cbn. lia.
    - apply krange_intro; cbn. rewrite u_small by lia. lia.
    - eapply (kshad_intro SEGS E M (EVar 73) (EVar 74) data len); [reflexivity | cbn; rewrite u_small by lia; reflexivity | lia | lia |].
      eapply shdata_frame_high; [exact HM | apply HM_heaphigh | exact Hshd | lia | lia | lia].
    - eapply (kblob_sub SEGS E M (EVar 8) buf data len bs off 16 0);
        [cbn; exact TR8 | reflexivity | | reflexivity | lia | lia | lia].
      eapply data_ok_frame; [exact HM | exact Hdok |].
      destruct (Z.eq_dec (bv_unsigned cs) 0); [solve_apart|].
      destruct Hcs as [?|(X & _ & ? & _)]; [lia|]. destruct X as (X1 & X2 & X3 & X4). solve_apart.
    - eapply krange_add_intro; [place_den | place_den | rewrite ?u_small by lia; lia | lia].
    - kdisj_place.
    - kdisj_place.
    - kdisj_place.
    - kdisj_place.
    - kdisj_place.
    - kdisj_place.
  Qed.

  (* [comment removed for export] *)
  Lemma fixed_cells : forall M', frame_mod M M' RSP ->
    cell64 SEGS M' (bv_unsigned sp - 8) ret /\
    cell64 SEGS M' (bv_unsigned sp - 16) (getr regs 8) /\
    cell64 SEGS M' (bv_unsigned sp - 24) (getr regs 9) /\
    cell64 SEGS M' (bv_unsigned sp - 32) (getr regs 18) /\
    cell64 SEGS M' (bv_unsigned sp - 40) (getr regs 19) /\
    cell64 SEGS M' (bv_unsigned sp - 48) (getr regs 20) /\
    cell64 SEGS M' (bv_unsigned sp - 56) (getr regs 21) /\
    cell64 SEGS M' (bv_unsigned sp - 64) (getr regs 22) /\
    cell64 SEGS M' (bv_unsigned sp - 72) (getr regs 23) /\
    (bv_unsigned cs <> 0%Z -> exists v, cell32 SEGS M' (bv_unsigned cs) v).
  Proof using ceil regs mem ret sp C cs HCheap Hstk HWS Hcs M S72 S64 S56 S48 S40 S32 S24 S16 S8 Hcsv.
    intros M' Hf. clear HFK TRK HDC Hro Hszk Hk. unfold RSP in Hf.
    pose proof (u64_range sp). pose proof (u64_range C). pose proof (u64_range cs).
    pose proof HWS as (W1 & W2 & W3 & W4).
    repeat match goal with |- _ /\ _ => split end;
      try (eapply cell64_frame; [exact Hf | eassumption | lia | lia | solve_apart]).
    intros Hnz. destruct (Hcsv Hnz) as [v Hv]. exists v.
    destruct Hcs as [Hc0 | (HWcs & _ & Hcsr & _ & _)]; [lia|]. destruct HWcs as (X1 & X2 & X3 & X4).
    eapply cell32_frame; [exact Hf | exact Hv | lia | lia | solve_apart].
  Qed.

  Lemma frame_total : forall M', frame_mod M M' RSP -> frame_mod mem M' (RSF sp C cs).
  Proof using ceil mem sp C cs Hstk HWS M HM.
    intros M' Hf. clear Hcsv HFK TRK HDC Hro Hszk Hk. unfold RSP in Hf.
    pose proof (u64_range sp). pose proof (u64_range C). pose proof (u64_range cs).
    pose proof HWS as (W1 & W2 & W3 & W4).
    eapply frame_mod_trans_same.
    - eapply frame_mod_of_covered; [| exact HM]. unfold RSF.
      destruct (Z.eq_dec (bv_unsigned cs) 0); solve_covered.
    - eapply frame_mod_of_covered; [| exact Hf]. unfold RSF. solve_covered.
  Qed.

  Lemma RSF_heaphigh : high_regions (RSF sp C cs).
  Proof using ceil mem data len sp C cs Hdheap HCheap Hstk Hcs M HM.
    pose proof (u64_range sp). pose proof (u64_range C). pose proof (u64_range cs).
    unfold RSF. destruct (Z.eq_dec (bv_unsigned cs) 0).
    - repeat (apply Forall_cons); [..|apply Forall_nil]; zfree_tac.
    - destruct Hcs as [?|(_ & _ & Hcsr & _)]; [lia|].
      repeat (apply Forall_cons); [..|apply Forall_nil]; zfree_tac.
  Qed.
  Lemma RSF_high : high_regions (RSF sp C cs).
  Proof using ceil mem data len sp C cs Hdheap HCheap Hstk Hcs M HM. exact RSF_heaphigh. Qed.

  Lemma dok_at : forall M', frame_mod M M' RSP -> data_ok M' data len bs.
  Proof using ceil mem data len bs sp buf C cs size Hdok Hdheap Hin HCheap Hstk HWS HDC Hcs M HM.
    intros M' Hf. clear Hcsv HFK TRK Hro Hszk Hk.
    pose proof (u64_range sp). pose proof (u64_range C). pose proof (u64_range cs).
    pose proof HWS as (W1 & W2 & W3 & W4). pose proof Hin as (I1 & I2 & I3).
    eapply data_ok_frame; [exact (frame_total M' Hf) | exact Hdok |].
    unfold RSF. destruct (Z.eq_dec (bv_unsigned cs) 0); [solve_apart|].
    destruct Hcs as [?|(X & _ & ? & _)]; [lia|]. destruct X as (? & ? & ? & ?). solve_apart.
  Qed.

  (* [comment removed for export] *)
  Lemma env_at : forall M', frame_mod M M' RSP ->
    env_cells SEGS asan_abi M' /\ shwz M' (bv_unsigned C + 12) 20.
  Proof using ceil mem data len sp C cs Hdheap HCheap HshwC Henv Hstk HWS Hcs M HM.
    intros M' Hf. pose proof (u64_range C). split.
    - eapply env_cells_frame_high; [exact (frame_total M' Hf) | apply RSF_high | exact Henv].
    - eapply shwz_frame_high; [exact (frame_total M' Hf) | apply RSF_heaphigh | exact HshwC | lia | lia | lia].
  Qed.

  Lemma disj_stack_buf : forall L, (0 <= L)%Z -> (bv_unsigned buf + L <= bv_unsigned data + len)%Z ->
    (bv_unsigned sp1 + -2128 + 2208 <= bv_unsigned buf + 0 \/ bv_unsigned buf + 0 + L <= bv_unsigned sp1 + -2128)%Z.
  Proof using ceil data len sp buf C size Hdheap Hin HCheap Hstk sp1 Hsp1. intros L HL H. clear Hcs HDC. pose proof Hin as (I1 & I2 & I3). lia. Qed.

  Lemma disj_C_buf : forall L, (0 <= L)%Z -> (bv_unsigned buf + L <= bv_unsigned data + len)%Z ->
    (bv_unsigned C + 0 + 32 <= bv_unsigned buf + 0 \/ bv_unsigned buf + 0 + L <= bv_unsigned C + 0)%Z.
  Proof using ceil data len sp buf C size Hin HCheap Hstk HDC. intros L HL H. clear Hcs. pose proof Hin as (I1 & I2 & I3). lia. Qed.

  (* [comment removed for export] *)
  Ltac fold_frame :=
    lazymatch goal with
    | EQM : ?M1 = mem_denot ?Ex ?M0 ?log, HLF : log_flat _ _, HMt : frame_mod M ?M0' RSP |- _ =>
        let Hf := fresh "Hf" in
        assert (Hf : frame_mod M0 M1 RSP);
        [ rewrite EQM, <- RSPs_denot;
          apply (frame_mod_mem_denot Ex M0 log RSPs HLF); [unfold RSPs; flats_auto | vm_compute; reflexivity]
        | let H2 := fresh "HMt" in
          pose proof (frame_mod_trans_same _ _ _ _ HMt Hf) as H2; clear HMt Hf EQM HLF; rename H2 into HMt ]
    | EQM : ?M1 = ?M0, HLF : log_flat _ _ |- _ =>
        (* [comment removed for export] *)
        subst M1; clear HLF
    end.

  (* [comment removed for export] *)
  Ltac call_memset RET :=
    lazymatch goal with
    | HR : regs_ok _ _ ?Rx, HMt : frame_mod M ?Mx RSP |- runs_to _ (@mkst ?I ?Rx _ ?Mx ?ro) _ =>
        eapply rt_call;
        [ eapply (Hmemset (Z_to_bv 64 (bv_unsigned C + 12)) I Rx Mx ro (Z_to_bv 64 RET));
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by lia; reflexivity
          | unfold imemset_pre; rewrite !u_small by lia;
            split; [regv_lin HR (10%bv:reg); rewrite TR18; f_equal; lia|];
            split; [regv HR (11%bv:reg); reflexivity|];
            split; [regv HR (12%bv:reg); reflexivity|];
            split; [apply mod8_mod4_12; exact HCal|];
            split; [unfold heapish; plc|];
            split; [eapply writable_sub; [eapply writable_frame; [exact HMt | eapply writable_frame; [exact HM | exact HWC]] | lia | lia | lia] |];
            split; [cbn [Z.leb]; exact (proj2 (env_at Mx HMt))|];
            split; [exact (proj1 (env_at Mx HMt))|];
            exists sp1; split; [regv HR (2%bv:reg); exact TR2|];
            unfold as_frame, stackish; split; [lia|]; split;
            [ rewrite Hsp1; apply (mod_sub_multiple (bv_unsigned sp) 80 16); [lia | exact Hspal | reflexivity]
            | eapply writable_sub; [eapply writable_frame; [exact HMt | eapply writable_frame; [exact HM | exact HWS]] | lia | lia | lia] ] ]
        | cbv beta ]
    end.

  Ltac post_memset :=
    let FQ := fresh "FQ" in let rq := fresh "rq" in let mq := fresh "mq" in
    let Hkeep := fresh "Hkeep" in let Hfkeep := fresh "Hfkeep" in let Hfr := fresh "Hfr" in
    let Hz := fresh "Hz" in let Ha0 := fresh "Ha0" in
    intros FQ rq mq (Hkeep & Hfkeep & Hfr & Hz & Ha0);
    unfold regs_kept in Hkeep; unfold fregs_kept in Hfkeep; unfold imemset_post in Hfr;
    lazymatch goal with HRx : regs_ok _ _ ?Rx |- _ =>
      let HR2 := fresh "HR2" in
      assert (HR2 : getr Rx 2 = sp1) by (regv HRx (2%bv:reg); exact TR2); rewrite HR2 in Hfr; clear HR2 end;
    after_call Hkeep Hfkeep FQ; clear Hkeep Hfkeep;
    lazymatch goal with
    | HK : know_ok _ ?Ex ?Mx _, HMt : frame_mod M ?Mx' RSP |- _ =>
        know_frame HK Hfr [(SA (EVar 2) (-2128), 2128%Z); (SA (EVar 18) 12, 20%Z)];
          [rewrite TR2, TR18; unfold v_addi; rewrite ?u_small by lia; repeat f_equal; lia|];
        (* [comment removed for export] *)
        let H2 := fresh "HMt" in let Hfr2 := fresh "Hfr2" in
        lazymatch type of Hfr with frame_mod ?Ma ?Mb _ =>
          assert (Hfr2 : frame_mod Ma Mb RSP)
            by (eapply frame_mod_of_covered; [|exact Hfr]; unfold RSP; solve_covered)
        end;
        pose proof (frame_mod_trans_same _ _ _ _ HMt Hfr2) as H2;
        clear HMt Hfr Hfr2; rename H2 into HMt;
        (* [comment removed for export] *)
        lazymatch goal with
        | HK : know_ok _ _ mq ?kn |- _ =>
          let HKz := fresh "HKz" in
          assert (HKz : know_ok SEGS Ex mq (KZero (SA (EVar 18) 12) (ELit 20) :: kn));
          [ apply know_ok_cons; [| exact HK];
            eapply (kzero_intro SEGS Ex mq (EVar 18) C 12 (ELit 20) 20);
            [ cbn; exact TR18 | reflexivity | lia | lia | lia
            | intros i Hi; rewrite <- (Hz i Hi); f_equal; f_equal; rewrite u_small by lia; lia ]
          | clear HK; rename HKz into HK ]
        end
    end.

  (* [comment removed for export] *)
  Ltac ccell HK off H :=
    kread_fact HK (EVar 18) off 4%nat H;
    rewrite TR18 in H; unfold v_addi in H; try rewrite Z.add_0_r in H.

  (* [comment removed for export] *)
  Ltac to_tailK :=
    lazymatch goal with
    | HK : know_ok _ ?Ex ?Mx _, HR : regs_ok _ _ ?Rx, HF : fregs_ok _ _ _, HMt : frame_mod M ?Mx' RSP,
      HR0 : id _, HF0 : id _ |- runs_to _ (@mkst _ ?Rx _ ?Mx _) _ =>
        let C0 := fresh "C0" in let C4 := fresh "C4" in let C8 := fresh "C8" in let C12 := fresh "C12" in
        let C16 := fresh "C16" in let C20 := fresh "C20" in let C24 := fresh "C24" in let C28 := fresh "C28" in
        ccell HK 0%Z C0; ccell HK 4%Z C4; ccell HK 8%Z C8; ccell HK 12%Z C12;
        ccell HK 16%Z C16; ccell HK 20%Z C20; ccell HK 24%Z C24; ccell HK 28%Z C28;
        let T := fresh "T" in
        pose proof (fixed_cells Mx HMt) as T;
        let T72 := fresh "T72" in let T64 := fresh "T64" in let T56 := fresh "T56" in let T48 := fresh "T48" in
        let T40 := fresh "T40" in let T32 := fresh "T32" in let T24 := fresh "T24" in
        let T16 := fresh "T16" in let T8 := fresh "T8" in let Tcs := fresh "Tcs" in
        destruct T as (T72 & T64 & T56 & T48 & T40 & T32 & T24 & T16 & T8 & Tcs);
        lift_hyp HR0; lift_hyp HF0;
        eapply (tailK_ok ceil FPI regs mem rom ret data len bs sp buf C cs size Hclassify Hret Hsp HWC HCal HCheap HshC Hro Hsb Hstk Hspal HWS Hcs
                  _ Rx Mx sp1 _ _ _ _ _ _ _ Hsp1);
        [ regv HR (2%bv:reg); exact TR2
        | regv_lin HR (10%bv:reg); rewrite TR18; f_equal; lia
        | intros r Hr; rewrite <- (TRK r Hr); revert r Hr;
          eapply (regs_same_on _ _ _ R Rx rc_untouched); [exact HR0 | exact HR | vm_compute; reflexivity]
        | eapply fregs_kept_trans; [exact HFK|]; unfold fregs_kept;
          eapply (fregs_same_on _ _ _ _ _ abi_fkept); [exact HF0 | exact HF | vm_compute; reflexivity]
        | apply frame_total; exact HMt
        | exact T72 | exact T64 | exact T56 | exact T48 | exact T40 | exact T32 | exact T24 | exact T16 | exact T8
        | exact C0 | exact C4 | exact C8 | exact C12 | exact C16 | exact C20 | exact C24 | exact C28
        | exact Tcs ]
    end.

  (* [comment removed for export] *)
  Ltac post_exit0 :=
    fin_ret;
    lazymatch goal with
    | HR : regs_ok _ ?sr ?R2, HF : fregs_ok _ ?sfr (@fp_regs ?FP2), HK : know_ok _ _ ?M2 _,
      HMt : frame_mod M ?Mx' RSP, HR0 : id _, HF0 : id _ |- _ =>
      let C0 := fresh "C0" in let C8 := fresh "C8" in let C12 := fresh "C12" in
      let C16 := fresh "C16" in let C20 := fresh "C20" in
      ccell HK 0%Z C0; ccell HK 8%Z C8; ccell HK 12%Z C12; ccell HK 16%Z C16; ccell HK 20%Z C20;
      exists FP2, R2, M2;
      split; [regv HR (1%bv:reg); reflexivity|];
      lift_hyp HR0; lift_hyp HF0;
      split; [ apply abi_kept_split;
               [ regv_lin HR (2%bv:reg); rewrite TR2, Hsp; apply bv_eq; rewrite u_small by lia; lia
               | regv HR (8%bv:reg); reflexivity
               | regv HR (9%bv:reg); reflexivity
               | regv HR (18%bv:reg); reflexivity
               | regv HR (19%bv:reg); reflexivity
               | regv HR (20%bv:reg); reflexivity
               | regv HR (21%bv:reg); reflexivity
               | regv HR (22%bv:reg); reflexivity
               | regv HR (23%bv:reg); reflexivity
               | intros r Hr; rewrite <- (TRK r Hr); revert r Hr;
                 eapply (regs_same_on _ _ _ R R2 rc_untouched); [exact HR0 | exact HR | vm_compute; reflexivity] ] |];
      split; [ eapply fregs_kept_trans; [exact HFK|]; unfold fregs_kept;
               eapply (fregs_same_on _ _ _ _ _ abi_fkept); [exact HF0 | exact HF | vm_compute; reflexivity] |];
      unfold rcurve_post_as, RCURVE_D; cbv zeta;
      split; [apply frame_total; exact HMt|];
      exists 0%Z; split; [regv HR (10%bv:reg); reflexivity|];
      split; [left; reflexivity|];
      split; [intros; lia|];
      split; [intros _; apply (curve_ok_zero4 SEGS M2 data len (bv_unsigned C) _ _ _ _ ltac:(lia) ltac:(lia) C0 C8 C12 C16 C20)|];
      intros; lia
    end.

  Ltac crawl n :=
    lazymatch n with
    | O => fail "crawl: out of depth"
    | S ?m =>
        run_fp 400%nat [TAILK; EXIT0] noscr true; fold_frame;
        lazymatch goal with
        | |- runs_to _ (@mkst _ _ (Z_to_bv 64 TAILK) _ _) _ => to_tailK
        | _ => first [ post_exit0
                     | let Hc := fresh "Hc" in branch_case as Hc; [clear Hc; crawl m | clear Hc; crawl m] ]
        end
    end.

  (* [comment removed for export] *)
  Ltac k_case kv :=
    let L := eval vm_compute in (12 + cb kv)%Z in
    lazymatch goal with
    | Hkv : k = kv, HR : regs_ok ?Ex ?sr ?Rx, HK : know_ok _ _ ?Mx ?kn, HMt : frame_mod M ?Mx' RSP |- _ =>
        let Hsz := fresh "Hsz" in
        pose proof Hszk as Hsz; rewrite Hkv in Hsz; cbn [cb] in Hsz;
        pin_reg HR (23%bv:reg) (ELit kv) by (regv HR (23%bv:reg); rewrite TR23, Hkv; reflexivity);
        let HK2 := fresh "HK" in
        assert (HK2 : know_ok SEGS Ex Mx
                  (KBlob (SA (EVar 8) 0) (ELit L) 1
                   :: KDisj (SA (EVar 2) (-2128)) 2208 (SA (EVar 8) 0) L
                   :: KDisj (SA (EVar 18) 0) 32 (SA (EVar 8) 0) L :: kn));
        [ apply know_ok_cons;
          [ eapply (kblob_sub SEGS Ex Mx (EVar 8) buf data len bs off L 1);
            [ cbn; exact TR8 | cbn; rewrite Hkv; reflexivity
            | exact (dok_at Mx HMt)
            | reflexivity | lia | lia | lia ]
          | apply know_ok_cons;
            [ cbn [kentry_ok]; unfold estart; cbn [a_base a_off edenot]; ev_simpl Ex; rewrite TR2, TR8; apply disj_stack_buf; lia
            | apply know_ok_cons;
              [ cbn [kentry_ok]; unfold estart; cbn [a_base a_off edenot]; ev_simpl Ex; rewrite TR18, TR8; apply disj_C_buf; lia
              | exact HK ] ] ]
        | clear HK; rename HK2 into HK ];
        crawl 3%nat
    end.

  Lemma tailP_ok :
    runs_to SEGS (mkst (FP:=FPc) R (Z_to_bv 64 0x8296c) M rom)
            (RCQ regs mem rom ret FPI data len bs sp buf C cs size).
  Proof using ceil FPI regs mem rom ret data len bs sp buf C cs size Hmemset Hclassify Hret Hsp Hdok Hdheap Hshd Hsize Hin HWC HCal HCheap HshC HshwC Henv Hro Hsb Hstk Hspal HWS HDC Hcs FPc R M sp1 k Hsp1 TR2 TR8 TR18 TR21 TR23 Hk Hszk TRK HFK HM S72 S64 S56 S48 S40 S32 S24 S16 S8 Hcsv.
    (* [comment removed for export] *)
    pose proof (Hmemset, Hclassify, Hret, Hsp, Hdok, Hdheap, Hshd, Hsize, Hin, HWC, HCal, HCheap, HshC, HshwC, Henv, Hro, Hsb,
                Hstk, Hspal, HWS, HDC, Hcs,
                Hsp1, TR2, TR8, TR18, TR21, TR23, Hk, Hszk, TRK, HFK, HM, S72, S64, S56, S48, S40, S32, S24, S16, S8, Hcsv) as HUSE; clear HUSE.
    pose proof (u64_range sp) as Rsp. pose proof (u64_range C) as RC. pose proof (u64_range cs) as Rcs.
    pose proof (u64_range buf) as Rbuf. pose proof (u64_range data) as Rdata.
    pose proof HWS as (W1 & W2 & W3 & W4). pose proof HWC as (V1 & V2 & V3 & V4).
    pose proof Hdok as (D1 & D2 & D3 & D4 & D5). pose proof Hin as (I1 & I2 & I3). pose proof (cb_range k) as Rcb.
    assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [sub bs off 16; sub bs off Lk])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [sub bs off 16; sub bs off Lk])).
    (* [comment removed for export] *)
    pin_reg HR (21%bv:reg) (ELit SB) by (rewrite TR21; reflexivity).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof knP_ok as HK.
    pose proof (frame_mod_refl M RSP) as HMt.
    run_fp 60%nat [IMEMSET] noscr true.
    fold_frame.
    call_memset 0x829b4%Z.
    post_memset.
    run_fp 80%nat [0x82a3c%Z] noscr true.
    fold_frame.
    assert (Hk5 : (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4)%Z) by lia.
    destruct Hk5 as [Hkv | [Hkv | [Hkv | [Hkv | Hkv]]]].
    - k_case 0%Z.
    - k_case 1%Z.
    - k_case 2%Z.
    - k_case 3%Z.
    - k_case 4%Z.
  Qed.
End TailP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section EntryP.
  Variable ceil : Z.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret data : word) (len : Z) (bs : list byte) (sp buf C cs : word) (size : Z).
  Hypothesis Hmemset : imemset20_contract SEGS as_asan ceil.
  Hypothesis Hclassify : classify_contract_as SEGS as_asan ceil.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis Hdok : data_ok mem data len bs.
  Hypothesis Hdheap : (appm (bv_unsigned data) len /\ (0 < bv_unsigned data)%Z) /\ (bv_unsigned data + len <= ceil)%Z.
  Hypothesis Hshd : shdata mem (bv_unsigned data) len.
  Hypothesis Hsize : (0 <= size < 2 ^ 32)%Z.
  Hypothesis Hin : inDATA data len (bv_unsigned buf) size.
  Hypothesis HWC : writable SEGS mem (bv_unsigned C) 32.
  Hypothesis HCal : (bv_unsigned C mod 8 = 0)%Z.
  Hypothesis HCheap : (appm (bv_unsigned C) 32 /\ (0 < bv_unsigned C)%Z) /\ (bv_unsigned C + 32 <= ceil)%Z.
  Hypothesis HshC : shz mem (bv_unsigned C) 4.
  Hypothesis HshwC : shwz mem (bv_unsigned C + 12) 20.
  Hypothesis Henv : env_cells SEGS asan_abi mem.
  Hypothesis Hro : env_ro asan_abi mem.
  Hypothesis Hsb : sbcell SEGS 0x9eaf0 0xa6bb8 mem.
  Hypothesis Hstk : ((AS_STKLO <= ceil)%Z /\ (ceil + 2208 <= bv_unsigned sp)%Z) /\ (bv_unsigned sp <= 2 ^ 47)%Z.
  Hypothesis Hspal : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis HWS : writable SEGS mem (bv_unsigned sp - 2208) 2208.
  Hypothesis HDC : (bv_unsigned data + len <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned data)%Z.
  Hypothesis Hcs : (bv_unsigned cs = 0)%Z \/
   (writable SEGS mem (bv_unsigned cs) 4 /\ (bv_unsigned cs mod 4 = 0)%Z /\
    (AS_STKLO <= ceil <= bv_unsigned cs /\ bv_unsigned cs + 4 <= 2 ^ 47)%Z /\
    shbyte mem (bv_unsigned cs) 0 /\ (bv_unsigned sp <= bv_unsigned cs)%Z).
  (* [comment removed for export] *)
  Variables (FPc : FPState) (R : bvmap 5 word) (M : word -> option byte).
  Variables (sp1 : word) (k : Z).
  Hypothesis Hsp1 : bv_unsigned sp1 = (bv_unsigned sp - 80)%Z.
  Hypothesis TR2 : getr R 2 = sp1.
  Hypothesis TR8 : getr R 8 = buf.
  Hypothesis TR13 : getr R 13 = cs.
  Hypothesis TR18 : getr R 18 = C.
  Hypothesis TR21 : getr R 21 = Z_to_bv 64 SB.
  Hypothesis TR23 : getr R 23 = Z_to_bv 64 k.
  Hypothesis Hk : (0 <= k <= 4)%Z.
  Hypothesis Hszk : (12 + cb k <= size)%Z.
  Hypothesis TRK : forall r, In r rc_untouched -> getr R r = getr regs r.
  Hypothesis HFK : fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPc)).
  Hypothesis HM : frame_mod mem M [(Z_to_bv 64 (bv_unsigned sp - 2208), 2208%Z)].
  Hypothesis S72 : cell64 SEGS M (bv_unsigned sp - 8) ret.
  Hypothesis S64 : cell64 SEGS M (bv_unsigned sp - 16) (getr regs 8).
  Hypothesis S56 : cell64 SEGS M (bv_unsigned sp - 24) (getr regs 9).
  Hypothesis S48 : cell64 SEGS M (bv_unsigned sp - 32) (getr regs 18).
  Hypothesis S40 : cell64 SEGS M (bv_unsigned sp - 40) (getr regs 19).
  Hypothesis S32 : cell64 SEGS M (bv_unsigned sp - 48) (getr regs 20).
  Hypothesis S24 : cell64 SEGS M (bv_unsigned sp - 56) (getr regs 21).
  Hypothesis S16 : cell64 SEGS M (bv_unsigned sp - 64) (getr regs 22).
  Hypothesis S8 : cell64 SEGS M (bv_unsigned sp - 72) (getr regs 23).

  Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPc))
                                ++ [ret; getr regs 8; getr regs 9; getr regs 18; getr regs 19;
                                    getr regs 20; getr regs 21; getr regs 22; getr regs 23]))
                     (blobs_ev []).

  Definition knE : list kentry :=
    [KRange (EVar 2) (AS_STKLO + 2128) (2^47 - 80);
     KWord (SA (EVar 2) 72) 8 (EVar 64);
     KWord (SA (EVar 2) 64) 8 (EVar 65);
     KWord (SA (EVar 2) 56) 8 (EVar 66);
     KWord (SA (EVar 2) 48) 8 (EVar 67);
     KWord (SA (EVar 2) 40) 8 (EVar 68);
     KWord (SA (EVar 2) 32) 8 (EVar 69);
     KWord (SA (EVar 2) 24) 8 (EVar 70);
     KWord (SA (EVar 2) 16) 8 (EVar 71);
     KWord (SA (EVar 2) 8) 8 (EVar 72)].

  Lemma knE_ok : know_ok SEGS E M knE.
  Proof using ceil regs ret sp C HCheap Hstk FPc R M sp1 Hsp1 TR2 S72 S64 S56 S48 S40 S32 S24 S16 S8.
    clear HFK TRK Hro HDC Hcs Hszk Hk.
    unfold knE. pose proof (u64_range sp).
    unfold cell64, cell in S72, S64, S56, S48, S40, S32, S24, S16, S8.
    unfold know_ok.
    repeat (apply Forall_cons); [..|apply Forall_nil].
    - apply krange_intro; cbn. rewrite TR2. lia.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 72 8 (EVar 64) ret);
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 72)%Z with (bv_unsigned sp - 8)%Z by lia. exact S72.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 64 8 (EVar 65) (getr regs 8));
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 64)%Z with (bv_unsigned sp - 16)%Z by lia. exact S64.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 56 8 (EVar 66) (getr regs 9));
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 56)%Z with (bv_unsigned sp - 24)%Z by lia. exact S56.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 48 8 (EVar 67) (getr regs 18));
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 48)%Z with (bv_unsigned sp - 32)%Z by lia. exact S48.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 40 8 (EVar 68) (getr regs 19));
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 40)%Z with (bv_unsigned sp - 40)%Z by lia. exact S40.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 32 8 (EVar 69) (getr regs 20));
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 32)%Z with (bv_unsigned sp - 48)%Z by lia. exact S32.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 24 8 (EVar 70) (getr regs 21));
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 24)%Z with (bv_unsigned sp - 56)%Z by lia. exact S24.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 16 8 (EVar 71) (getr regs 22));
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 16)%Z with (bv_unsigned sp - 64)%Z by lia. exact S16.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 8 8 (EVar 72) (getr regs 23));
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 8)%Z with (bv_unsigned sp - 72)%Z by lia. exact S8.
  Qed.

  (* [comment removed for export] *)
  Ltac to_tailP HMf Tcs :=
    lazymatch goal with
    | HR : regs_ok _ ?sr ?Rx, HF : fregs_ok _ _ _, HK : know_ok _ _ ?Mx _, HR0 : id _, HF0 : id _
      |- runs_to _ (@mkst ?I ?Rx _ ?Mx _) _ =>
      let T72 := fresh "T72" in let T64 := fresh "T64" in let T56 := fresh "T56" in let T48 := fresh "T48" in
      let T40 := fresh "T40" in let T32 := fresh "T32" in let T24 := fresh "T24" in
      let T16 := fresh "T16" in let T8 := fresh "T8" in
      kread_fact HK (EVar 2) 72%Z 8%nat T72; kread_fact HK (EVar 2) 64%Z 8%nat T64;
      kread_fact HK (EVar 2) 56%Z 8%nat T56; kread_fact HK (EVar 2) 48%Z 8%nat T48;
      kread_fact HK (EVar 2) 40%Z 8%nat T40; kread_fact HK (EVar 2) 32%Z 8%nat T32;
      kread_fact HK (EVar 2) 24%Z 8%nat T24; kread_fact HK (EVar 2) 16%Z 8%nat T16;
      kread_fact HK (EVar 2) 8%Z 8%nat T8;
      rewrite TR2 in T72, T64, T56, T48, T40, T32, T24, T16, T8; unfold v_addi in T72, T64, T56, T48, T40, T32, T24, T16, T8;
      unfold id in HR0, HF0;
      eapply (tailP_ok ceil FPI regs mem rom ret data len bs sp buf C cs size Hmemset Hclassify Hret Hsp Hdok Hdheap Hshd Hsize Hin HWC HCal HCheap
                HshC HshwC Henv Hro Hsb Hstk Hspal HWS HDC Hcs I Rx Mx sp1 k Hsp1);
      [ regv HR (2%bv:reg); exact TR2
      | regv HR (8%bv:reg); exact TR8
      | regv HR (18%bv:reg); exact TR18
      | regv HR (21%bv:reg); reflexivity
      | regv HR (23%bv:reg); exact TR23
      | exact Hk | exact Hszk
      | intros r Hr; rewrite <- (TRK r Hr); exact (regs_same_on _ _ _ R Rx rc_untouched HR0 HR ltac:(vm_compute; reflexivity) r Hr)
      | eapply fregs_kept_trans; [exact HFK|]; unfold fregs_kept; intros r Hr;
        exact (fregs_same_on _ _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity) r Hr)
      | exact HMf
      | unfold cell64, cell; replace (bv_unsigned sp - 8)%Z with (bv_unsigned sp1 + 72)%Z by lia; exact T72
      | unfold cell64, cell; replace (bv_unsigned sp - 16)%Z with (bv_unsigned sp1 + 64)%Z by lia; exact T64
      | unfold cell64, cell; replace (bv_unsigned sp - 24)%Z with (bv_unsigned sp1 + 56)%Z by lia; exact T56
      | unfold cell64, cell; replace (bv_unsigned sp - 32)%Z with (bv_unsigned sp1 + 48)%Z by lia; exact T48
      | unfold cell64, cell; replace (bv_unsigned sp - 40)%Z with (bv_unsigned sp1 + 40)%Z by lia; exact T40
      | unfold cell64, cell; replace (bv_unsigned sp - 48)%Z with (bv_unsigned sp1 + 32)%Z by lia; exact T32
      | unfold cell64, cell; replace (bv_unsigned sp - 56)%Z with (bv_unsigned sp1 + 24)%Z by lia; exact T24
      | unfold cell64, cell; replace (bv_unsigned sp - 64)%Z with (bv_unsigned sp1 + 16)%Z by lia; exact T16
      | unfold cell64, cell; replace (bv_unsigned sp - 72)%Z with (bv_unsigned sp1 + 8)%Z by lia; exact T8
      | exact Tcs ]
    end.

  Lemma tailP_entry :
    runs_to SEGS (mkst (FP:=FPc) R (Z_to_bv 64 0x82954) M rom)
            (RCQ regs mem rom ret FPI data len bs sp buf C cs size).
  Proof using ceil FPI regs mem rom ret data len bs sp buf C cs size Hmemset Hclassify Hret Hsp Hdok Hdheap Hshd Hsize Hin HWC HCal HCheap HshC HshwC Henv Hro Hsb Hstk Hspal HWS HDC Hcs FPc R M sp1 k Hsp1 TR2 TR8 TR13 TR18 TR21 TR23 Hk Hszk TRK HFK HM S72 S64 S56 S48 S40 S32 S24 S16 S8.
    pose proof (Hmemset, Hclassify, Hret, Hsp, Hdok, Hdheap, Hshd, Hsize, Hin, HWC, HCal, HCheap, HshC, HshwC, Henv, Hro, Hsb,
                Hstk, Hspal, HWS, HDC, Hcs,
                Hsp1, TR2, TR8, TR13, TR18, TR21, TR23, Hk, Hszk, TRK, HFK, HM, S72, S64, S56, S48, S40, S32, S24, S16, S8) as HUSE; clear HUSE.
    pose proof (u64_range sp) as Rsp. pose proof (u64_range cs) as Rcs.
    pose proof HWS as (W1 & W2 & W3 & W4).
    assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [])).
    pin_reg HR (21%bv:reg) (ELit SB) by (rewrite TR21; reflexivity).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof knE_ok as HK.
    destruct (Z.eq_dec (bv_unsigned cs) 0) as [Hcs0 | Hnz].
    - (* [comment removed for export] *)
      add_krange (EVar 13) 0%Z 0%Z by (rewrite TR13; lia).
      run_fp 3%nat [0x8296c%Z] noscr false.
      assert (HMf : frame_mod mem M ((Z_to_bv 64 (bv_unsigned sp - 2208), 2208%Z)
                                     :: (if Z.eq_dec (bv_unsigned cs) 0 then [] else [(cs, 4%Z)])))
        by (rewrite Hcs0; exact HM).
      assert (Tcs : bv_unsigned cs <> 0%Z -> exists v, cell32 SEGS M (bv_unsigned cs) v) by (intros; lia).
      to_tailP HMf Tcs.
    - (* [comment removed for export] *)
      destruct Hcs as [? | (HWcs & Hcsal & Hcsr & Hcssh & Hcs3)]; [lia|].
      pose proof HWcs as (X1 & X2 & X3 & X4).
      lazymatch goal with
      | HK : know_ok _ _ _ ?kn |- _ =>
        let HK2 := fresh "HK" in
        assert (HK2 : know_ok SEGS E M (KRange (EVar 13) AS_STKLO (2^47 - 4) :: KAlign (EVar 13) 4
                                       :: KDisj (SA (EVar 2) 8) 72 (SA (EVar 13) 0) 4 :: KWr (SA (EVar 13) 0) 4
                                       :: KZero (SA (EAlu ALU_SRL (EVar 13) (ELit 3)) SB) (ELit 1) :: kn));
        [ apply know_ok_cons; [apply krange_intro; cbn; rewrite TR13; lia|];
          apply know_ok_cons; [apply kalign_intro; [lia|]; cbn; rewrite TR13; exact Hcsal|];
          apply know_ok_cons; [cbn [kentry_ok]; unfold estart; cbn [a_base a_off edenot]; ev_simpl E; rewrite TR2, TR13; lia|];
          apply know_ok_cons;
          [ apply (kwr_intro SEGS E M (EVar 13) cs 0 4); [cbn; exact TR13 | lia | lia | lia |];
            rewrite Z.add_0_r; eapply frame_mod_store_ok; [exact HM | exact X4]
          | apply know_ok_cons; [| exact HK];
            replace SB with (SB + 0)%Z by lia;
            eapply (kzero_shadow_intro SEGS E M (EVar 13) cs 0 1); [cbn; exact TR13 | lia | lia | |];
            [ assert (bv_unsigned cs / 8 < 2 ^ 44)%Z by (apply Z.div_lt_upper_bound; lia);
              pose proof (Z.div_pos (bv_unsigned cs) 8 ltac:(lia) ltac:(lia)); lia
            | intros j Hj; replace j with 0%Z by lia; rewrite Z.add_0_r;
              eapply shbyte_frame_high; [exact HM | | exact Hcssh | lia | lia];
              repeat (apply Forall_cons); [..|apply Forall_nil]; zfree_tac ] ]
        | clear HK; rename HK2 into HK ]
      end.
      run_fp 12%nat [0x8296c%Z] noscr true.
      assert (Hf : frame_mod M M0 [(cs, 4%Z)]).
      { rewrite EQM.
        replace [(cs, 4%Z)] with (regions_denot E [(SA (EVar 13) 0, 4%Z)])
          by (cbn [regions_denot map fst snd]; unfold adenot; cbn [a_base a_off edenot]; ev_simpl E;
              rewrite TR13; unfold v_addi; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
        apply (frame_mod_mem_denot E M _ [(SA (EVar 13) 0, 4%Z)] HLF); [flats_auto | vm_compute; reflexivity]. }
      clear EQM HLF.
      assert (HMf : frame_mod mem M0 ((Z_to_bv 64 (bv_unsigned sp - 2208), 2208%Z)
                                      :: (if Z.eq_dec (bv_unsigned cs) 0 then [] else [(cs, 4%Z)]))).
      { destruct (Z.eq_dec (bv_unsigned cs) 0) as [|_]; [lia|].
        eapply frame_mod_trans_same.
        - eapply frame_mod_of_covered; [|exact HM]. solve_covered.
        - eapply frame_mod_of_covered; [|exact Hf]. solve_covered. }
      kread_fact HK (EVar 13) 0%Z 4%nat Tc. rewrite TR13 in Tc. unfold v_addi in Tc. rewrite ?Z.add_0_r in Tc.
      assert (Tcs : bv_unsigned cs <> 0%Z -> exists v, cell32 SEGS M0 (bv_unsigned cs) v)
        by (intros _; eexists; apply cell32_of_word; exact Tc).
      clear Tc Hf.
      to_tailP HMf Tcs.
  Qed.
End EntryP.
