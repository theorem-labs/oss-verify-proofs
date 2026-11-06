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
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs AsRtSpec AsLibFrame AsLibEnv AsLibFPLib AsLibBswap AsLibTagsLib AsLibTagsCall AsLibReadCurveLib AsLibCurveSpec AsLibReadCurveK AsLibReadCurveP AsLibReadCurveC AsLibPlace.
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

#[local] Abbreviation SEGS := Asan.M.loaded_segments.

Section Main.
  Variable ceil : Z.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret data : word) (len : Z) (bs : list byte) (sp buf C cs : word) (size : Z).
  Hypothesis Hmemset : imemset20_contract SEGS as_asan ceil.
  Hypothesis Hclassify : classify_contract_as SEGS as_asan ceil.
  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis Hbuf : getr regs 10 = buf.
  Hypothesis Hsz : getr regs 11 = Z_to_bv 64 size.
  Hypothesis HC : getr regs 12 = C.
  Hypothesis Hcs13 : getr regs 13 = cs.
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
  Hypothesis Hshb : env_shb asan_abi mem.
  Hypothesis Hsb : sbcell SEGS 0x9eaf0 0xa6bb8 mem.
  Hypothesis Hstk : ((AS_STKLO <= ceil)%Z /\ (ceil + 2208 <= bv_unsigned sp)%Z) /\ (bv_unsigned sp <= 2 ^ 47)%Z.
  Hypothesis Hspal : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis HWS : writable SEGS mem (bv_unsigned sp - 2208) 2208.
  Hypothesis HDC : (bv_unsigned data + len <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned data)%Z.
  Hypothesis Hcs : (bv_unsigned cs = 0)%Z \/
   (writable SEGS mem (bv_unsigned cs) 4 /\ (bv_unsigned cs mod 4 = 0)%Z /\
    (AS_STKLO <= ceil <= bv_unsigned cs /\ bv_unsigned cs + 4 <= 2 ^ 47)%Z /\
    shbyte mem (bv_unsigned cs) 0 /\ (bv_unsigned sp <= bv_unsigned cs)%Z).

  #[local] Abbreviation off := (bv_unsigned buf - bv_unsigned data)%Z.

  Let E : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ [data; Z_to_bv 64 len]))
                     (blobs_ev [sub bs off 4; sub bs off 12]).
  (* [comment removed for export] *)

  Definition kn0v1 : list kentry :=
    [KImg 0x20d00 0x20f20;
     KWord (SA (ELit 0) 0x9eaf0) 8 (ELit 0xa6bb8); KWord (SA (ELit 0) 0xa6bb8) 8 (ELit SB);
     KWord (SA (ELit 0) 0x7fffc1d4) 1 (ELit 0); KWord (SA (ELit 0) 0x7fffc1d5) 1 (ELit 0); KWord (SA (ELit 0) 0x7fffc1d6) 1 (ELit 4);
     KRange (EVar 2) (AS_STKLO + 2208) (2^47);
     KRange (EVar 10) 1 (2 ^ 47 - 2048);
     KRange (EVar 11) 0 (2^32 - 1);
     KRange (EVar 12) 1 (2 ^ 47 - 32);
     KWr (SA (EVar 2) (-2208)) 2208;
     KRange (EVar 64) 1 (2 ^ 47 - 2048); KRange (EVar 65) 0 (2^26); KShad (EVar 64) (EVar 65) SB].

  Lemma kn0v1_ok : know_ok SEGS E mem kn0v1.
  Proof using ceil FPI regs mem rom ret data len bs sp buf C size Hsp Hbuf Hsz HC Hdok Hdheap Hshd Hsize Hin HCheap Hro Hshb Hsb Hstk HWS.
    unfold kn0v1. pose proof (u64_range sp). pose proof (u64_range C). pose proof (u64_range buf). pose proof (u64_range data).
    pose proof HWS as (W1 & W2 & W3 & W4). pose proof Hdok as (D1 & D2 & D3 & D4 & D5).
    destruct Hsb as [Hg1 Hg2]. unfold cell64, cell in Hg1, Hg2.
    clear HDC Hcs.
    unfold know_ok.
    repeat (apply Forall_cons); [..|apply Forall_nil].
    - apply kimg_intro; [lia|lia|]. intros i Hi. apply (Hro 0x20d00%Z 0x20f20%Z i); [first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)] | exact Hi].
    - eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0x9eaf0 8 (ELit 0xa6bb8) (Z_to_bv 64 0xa6bb8)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0xa6bb8 8 (ELit SB) (Z_to_bv 64 SB)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0x7fffc1d4 1 (ELit 0) (Z_to_bv 64 0)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
      rewrite Z.add_0_l, (Hshb 0x7fffc1d4%Z 0%Z) by (first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)]). reflexivity.
    - eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0x7fffc1d5 1 (ELit 0) (Z_to_bv 64 0)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
      rewrite Z.add_0_l, (Hshb 0x7fffc1d5%Z 0%Z) by (first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)]). reflexivity.
    - eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0x7fffc1d6 1 (ELit 4) (Z_to_bv 64 4)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
      rewrite Z.add_0_l, (Hshb 0x7fffc1d6%Z 4%Z) by (first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)]). reflexivity.
    - apply krange_intro; cbn. rewrite Hsp. lia.
    - apply krange_intro; cbn. rewrite Hbuf. pose proof Hin as (I1 & I2 & I3). lia.
    - apply krange_intro; cbn. rewrite Hsz, u_small by lia. lia.
    - apply krange_intro; cbn. rewrite HC. lia.
    - apply (kwr_intro SEGS E mem (EVar 2) sp (-2208) 2208); [cbn; exact Hsp | lia | lia | lia |].
      replace (bv_unsigned sp + -2208)%Z with (bv_unsigned sp - 2208)%Z by lia. exact W4.
    - apply krange_intro; cbn. lia.
    - apply krange_intro; cbn. rewrite u_small by lia. lia.
    - eapply (kshad_intro SEGS E mem (EVar 64) (EVar 65) data len); [reflexivity | cbn; rewrite u_small by lia; reflexivity | lia | lia | exact Hshd].
  Qed.

  Definition kn0 : list kentry := kn0v1 ++
    [KRange (EAlu ALU_ADD (EVar 64) (EVar 65)) 0 (2 ^ 47 - 2048);
     KDisj (SA (EVar 12) 0) 32 ZSH ZSHL; KDisj (SA (EVar 12) 0) 32 ZIMG ZIMGL;
     KDisj (SA (EVar 12) 0) 32 (SA (EVar 2) (-2208)) 2208].
  Lemma kn0_ok : know_ok SEGS E mem kn0.
  Proof using ceil FPI regs mem rom ret data len bs sp buf C cs size Hsp Hbuf Hsz HC Hdok Hdheap Hshd Hsize Hin HCheap Hro Hshb Hsb Hstk HWS Hcs. apply know_ok_app; [exact kn0v1_ok | kn_place]. Qed.

  (* [comment removed for export] *)
  Lemma exit_facts : forall M', frame_mod mem M' [(Z_to_bv 64 (bv_unsigned sp - 2208), 2208%Z)] ->
    frame_mod mem M' (RSF sp C cs) /\
    (curve_ok SEGS mem data len (bv_unsigned C) -> curve_ok SEGS M' data len (bv_unsigned C)).
  Proof using ceil mem data len sp C cs HWC HCheap Hstk HWS Hcs.
    intros M' HMs. clear Hro HDC.
    pose proof (u64_range sp). pose proof (u64_range C). pose proof (u64_range cs).
    pose proof HWS as (W1 & W2 & W3 & W4). pose proof HWC as (V1 & V2 & V3 & V4).
    split.
    - eapply frame_mod_of_covered; [| exact HMs]. unfold RSF.
      destruct (Z.eq_dec (bv_unsigned cs) 0);
        [ solve_covered | destruct Hcs as [?|(X & ?)]; [lia|]; destruct X as (?&?&?&?); solve_covered ].
    - intros Hc. eapply curve_ok_frame; [exact HMs | exact Hc | lia | lia | solve_apart].
  Qed.

  (* [comment removed for export] *)
  Ltac post_exit HMs :=
    fin_ret;
    let XF1 := fresh "XF1" in let XF2 := fresh "XF2" in
    lazymatch type of HMs with frame_mod mem ?M1 _ => destruct (exit_facts M1 HMs) as [XF1 XF2] end;
    lazymatch goal with
    | HR : regs_ok _ ?sr ?R2, HF : fregs_ok _ ?sfr (@fp_regs ?FP2), HK : know_ok _ _ ?M2 _, HR0 : id _, HF0 : id _ |- _ =>
      exists FP2, R2, M2;
      split; [regv HR (1%bv:reg); rewrite Hra; reflexivity|];
      unfold id in HR0, HF0;
      split; [ unfold regs_kept; eapply (regs_same_on _ _ _ regs R2 abi_kept); [exact HR0 | exact HR | vm_compute; reflexivity] |];
      split; [ unfold fregs_kept; eapply (fregs_same_on _ _ _ _ _ abi_fkept); [exact HF0 | exact HF | vm_compute; reflexivity] |];
      unfold rcurve_post_as, RCURVE_D; cbv zeta; unfold RSF in XF1;
      split; [ exact XF1 |];
      exists 0%Z; split; [regv HR (10%bv:reg); reflexivity|];
      split; [left; reflexivity|];
      split; [intros; lia|];
      split; [ exact XF2 |];
      intros; lia
    end.

  (* [comment removed for export] *)
  Ltac fold_stack HMs :=
    lazymatch goal with
    | EQM : ?M1 = mem_denot ?Ex ?M0 ?log, HLF : log_flat _ _ |- _ =>
        let Hf := fresh "Hf" in
        assert (Hf : frame_mod M0 M1 [(Z_to_bv 64 (bv_unsigned sp - 2208), 2208%Z)]);
        [ rewrite EQM;
          replace [(Z_to_bv 64 (bv_unsigned sp - 2208), 2208%Z)] with (regions_denot Ex [(SA (EVar 2) (-2208), 2208%Z)])
            by (cbn [regions_denot map fst snd]; unfold adenot; cbn [a_base a_off edenot]; ev_simpl Ex;
                rewrite Hsp; unfold v_addi; repeat f_equal; lia);
          apply (frame_mod_mem_denot Ex M0 log [(SA (EVar 2) (-2208), 2208%Z)] HLF); [flats_auto | vm_compute; reflexivity]
        | let H2 := fresh "HMs" in
          pose proof (frame_mod_trans_same _ _ _ _ HMs Hf) as H2; clear HMs Hf EQM HLF; rename H2 into HMs ]
    | EQM : ?M1 = ?M0, HLF : log_flat _ _ |- _ => subst M1; clear HLF
    end.

  (* [comment removed for export] *)
  Ltac add_blob L idx Hsz :=
    lazymatch goal with
    | HK : know_ok _ ?Ex ?Mx ?kn, HMs : frame_mod mem ?Mx _ |- _ =>
      let HK2 := fresh "HK" in
      assert (HK2 : know_ok SEGS Ex Mx (KBlob (SA (EVar 10) 0) (ELit L) idx :: kn));
      [ apply know_ok_cons; [| exact HK];
        eapply (kblob_sub SEGS Ex Mx (EVar 10) buf data len bs off L idx);
        [ cbn; exact Hbuf | reflexivity
        | eapply data_ok_frame; [exact HMs | exact Hdok | solve_apart]
        | reflexivity | lia | lia | lia ]
      | clear HK; rename HK2 into HK ]
    end.

  (* [comment removed for export] *)
  Ltac stack_cells T72 T64 T56 T48 T40 T32 T24 T16 T8 :=
    lazymatch goal with
    | HK : know_ok _ _ ?Mx _ |- _ =>
      kread_fact HK (EVar 2) (-8)%Z 8%nat T72; kread_fact HK (EVar 2) (-16)%Z 8%nat T64;
      kread_fact HK (EVar 2) (-24)%Z 8%nat T56; kread_fact HK (EVar 2) (-32)%Z 8%nat T48;
      kread_fact HK (EVar 2) (-40)%Z 8%nat T40; kread_fact HK (EVar 2) (-48)%Z 8%nat T32;
      kread_fact HK (EVar 2) (-56)%Z 8%nat T24; kread_fact HK (EVar 2) (-64)%Z 8%nat T16;
      kread_fact HK (EVar 2) (-72)%Z 8%nat T8;
      rewrite Hsp in T72, T64, T56, T48, T40, T32, T24, T16, T8;
      unfold v_addi in T72, T64, T56, T48, T40, T32, T24, T16, T8;
      rewrite Hra in T72
    end.

  (* [comment removed for export] *)
  Definition nuoff (j : nat) : Z := match j with 8%nat => 8 | 9%nat => 9 | 10%nat => 10 | _ => 11 end.
  Definition nu (j : nat) : Z := bs_byte bs (off + nuoff j).
  Definition atoms : list (expr * (bool * nat)) :=
    [(EBlob false 1 8 1, (false, 8%nat)); (EBlob false 1 9 1, (false, 9%nat));
     (EBlob false 1 10 1, (false, 10%nat)); (EBlob false 1 11 1, (false, 11%nat))].
  Lemma nu_range : forall j, (0 <= nu j < 256)%Z.
  Proof using data bs buf. intros j. unfold nu. apply bs_byte_range. Qed.
  Lemma atoms_ok12 : (12 <= size)%Z -> atoms_ok E nu atoms.
  Proof using ceil FPI regs mem data len bs sp buf C cs size Hdok Hin HCheap Hstk Hcs.
    intros H12. pose proof Hdok as (D1 & D2 & D3 & D4 & D5). pose proof Hin as (I1 & I2 & I3).
    unfold atoms, atoms_ok. repeat (apply Forall_cons); [..|apply Forall_nil];
      unfold atom_ok; cbn [edenot eb E blobs_ev nth]; unfold nu; cbn [nuoff];
      (rewrite blob_val_sub_u8; [reflexivity | lia | lia | lia]).
  Qed.
  #[local] Abbreviation vc := (be32 bs (off + 8)).

  (* [comment removed for export] *)
  Definition RAWe : expr :=
    EAlu ALU_ADD (EBlob false 1 8 1)
      (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EBlob false 1 9 1))
         (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EBlob false 1 10 1))
            (EMd M_MUL (ELit 16777216) (EBlob false 1 11 1)))).
  Definition Xe : expr :=
    EAlu ALU_OR
      (EAlu ALU_OR (EAluw ALU_SLL (EBlob false 1 8 1) (ELit 24))
         (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EBlob false 1 10 1)) (EBlob false 1 11 1)))
      (EMd M_MUL (ELit 256) (EAlu ALU_AND RAWe (ELit 65280))).
  Definition X11e : expr :=
    EAlu ALU_ADD (EAlu ALU_SRL (EMd M_MUL (ELit 4294967296) Xe) (ELit 31)) (ELit 12).

  Lemma be32_nu : vc = (nu 11 + 256 * (nu 10 + 256 * (nu 9 + 256 * nu 8)))%Z.
  Proof using data bs sp buf C cs.
    unfold be32, nu. cbn [nuoff].
    replace (off + 8 + 1)%Z with (off + 9)%Z by lia.
    replace (off + 8 + 2)%Z with (off + 10)%Z by lia.
    replace (off + 8 + 3)%Z with (off + 11)%Z by lia. lia.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma Xe_low32 : (12 <= size)%Z -> (bv_unsigned (edenot E Xe) mod 2 ^ 32 = vc)%Z.
  Proof using ceil FPI regs mem rom data len bs sp buf C cs size Hdok Hsize Hin HCheap Hstk Hspal Hcs.
    intros H12.
    pose proof (beval_bytes E nu nu_range atoms (EExt false 0 4 Xe) [11; 10; 9; 8]%nat (atoms_ok12 H12)
                  ltac:(cbn; lia) ltac:(vm_compute; reflexivity)) as B.
    cbn [edenot bytes_val] in B. fold (edenot E Xe) in B.
    rewrite ext_val_4_word in B. pose proof (u64_range (edenot E Xe)).
    rewrite u_small in B by lia. rewrite be32_nu. lia.
  Qed.

  Lemma RAWe_val : (12 <= size)%Z ->
    bv_unsigned (edenot E RAWe) = (nu 8 + 256 * (nu 9 + 256 * (nu 10 + 256 * nu 11)))%Z.
  Proof using ceil FPI regs mem rom data len bs sp buf C cs size Hdok Hsize Hin HCheap Hstk Hspal Hcs.
    intros H12.
    pose proof (beval_bytes E nu nu_range atoms RAWe [8; 9; 10; 11]%nat (atoms_ok12 H12)
                  ltac:(cbn; lia) ltac:(vm_compute; reflexivity)) as B.
    cbn [bytes_val] in B. lia.
  Qed.

  Lemma RAW_zero : (12 <= size)%Z -> (bv_unsigned (edenot E RAWe) = 0 <-> vc = 0)%Z.
  Proof using ceil FPI regs mem rom data len bs sp buf C cs size Hdok Hsize Hin HCheap Hstk Hspal Hcs.
    intros H12. rewrite RAWe_val by exact H12. rewrite be32_nu.
    pose proof (nu_range 8). pose proof (nu_range 9). pose proof (nu_range 10). pose proof (nu_range 11). lia.
  Qed.

  Lemma X11e_val : (12 <= size)%Z -> bv_unsigned (edenot E X11e) = (2 * vc + 12)%Z.
  Proof using ceil FPI regs mem rom data len bs sp buf C cs size Hdok Hsize Hin HCheap Hstk Hspal Hcs.
    intros H12. rewrite <- (Xe_low32 H12).
    change (edenot E X11e) with
      (alu64 ALU_ADD (alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 4294967296) (edenot E Xe)) (Z_to_bv 64 31)) (Z_to_bv 64 12)).
    pose proof (u_mul32_srl31 (edenot E Xe)) as U.
    pose proof (Z.mod_pos_bound (bv_unsigned (edenot E Xe)) (2 ^ 32) ltac:(lia)).
    rewrite alu_add_lit, u_small by lia. lia.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


  (* [comment removed for export] *)
  Ltac hand_C Hc3 Hc4 :=
    lazymatch goal with
    | HR : regs_ok _ ?sr ?Rx, HF : fregs_ok _ _ _, HMs : frame_mod mem ?Mx [_], HR0 : id _, HF0 : id _,
      T72 : rdn _ ?Mx (Z_to_bv 64 (bv_unsigned sp + -8)) 8 = _,
      T64 : rdn _ ?Mx (Z_to_bv 64 (bv_unsigned sp + -16)) 8 = _,
      T56 : rdn _ ?Mx (Z_to_bv 64 (bv_unsigned sp + -24)) 8 = _,
      T48 : rdn _ ?Mx (Z_to_bv 64 (bv_unsigned sp + -32)) 8 = _,
      T40 : rdn _ ?Mx (Z_to_bv 64 (bv_unsigned sp + -40)) 8 = _,
      T32 : rdn _ ?Mx (Z_to_bv 64 (bv_unsigned sp + -48)) 8 = _,
      T24 : rdn _ ?Mx (Z_to_bv 64 (bv_unsigned sp + -56)) 8 = _,
      T16 : rdn _ ?Mx (Z_to_bv 64 (bv_unsigned sp + -64)) 8 = _,
      T8 : rdn _ ?Mx (Z_to_bv 64 (bv_unsigned sp + -72)) 8 = _
      |- runs_to _ (@mkst ?I ?Rx _ ?Mx _) _ =>
      unfold id in HR0, HF0; unhide HDC; unhide Hcs;
      eapply (tailC_entry ceil FPI regs mem rom ret data len bs sp buf C cs size Hmemset Hret Hsp Hdok Hdheap Hshd Hsize Hin HWC HCal HCheap
                HshC HshwC Henv Hro Hsb Hstk Hspal HWS HDC Hcs I Rx Mx (Z_to_bv 64 (bv_unsigned sp - 80)) (edenot E Xe) (edenot E RAWe) vc);
      [ rewrite u_small by lia; reflexivity
      | regv_lin HR (2%bv:reg); rewrite Hsp; f_equal; lia
      | regv HR (8%bv:reg); exact Hbuf
      | regv HR (13%bv:reg); exact Hcs13
      | regv HR (18%bv:reg); exact HC
      | regv HR (21%bv:reg); reflexivity
      | rewrite (reg_val _ _ _ (9%bv:reg) HR); reflexivity
      | rewrite (reg_val _ _ _ (11%bv:reg) HR); reflexivity
      | apply Xe_low32; exact Hc3
      | apply RAW_zero; exact Hc3
      | let HX11 := fresh "HX11" in
        pose proof (X11e_val Hc3) as HX11; unfold X11e, Xe, RAWe in HX11;
        rewrite branch_taken_Z in Hc4; cbv beta iota in Hc4; rewrite HX11 in Hc4;
        cbn [edenot] in Hc4; ev_simpl_in E Hc4; rewrite Hsz, u_small in Hc4 by lia;
        apply Bool.negb_true_iff in Hc4; apply Z.ltb_ge in Hc4; clear -Hc4; lia
      | intros r Hr; exact (regs_same_on _ _ _ regs Rx rc_untouched HR0 HR ltac:(vm_compute; reflexivity) r Hr)
      | unfold fregs_kept; intros r Hr; exact (fregs_same_on _ _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity) r Hr)
      | exact HMs
      | unfold cell64, cell; replace (bv_unsigned sp - 8)%Z with (bv_unsigned sp + -8)%Z by lia; exact T72
      | unfold cell64, cell; replace (bv_unsigned sp - 16)%Z with (bv_unsigned sp + -16)%Z by lia; exact T64
      | unfold cell64, cell; replace (bv_unsigned sp - 24)%Z with (bv_unsigned sp + -24)%Z by lia; exact T56
      | unfold cell64, cell; replace (bv_unsigned sp - 32)%Z with (bv_unsigned sp + -32)%Z by lia; exact T48
      | unfold cell64, cell; replace (bv_unsigned sp - 40)%Z with (bv_unsigned sp + -40)%Z by lia; exact T40
      | unfold cell64, cell; replace (bv_unsigned sp - 48)%Z with (bv_unsigned sp + -48)%Z by lia; exact T32
      | unfold cell64, cell; replace (bv_unsigned sp - 56)%Z with (bv_unsigned sp + -56)%Z by lia; exact T24
      | unfold cell64, cell; replace (bv_unsigned sp - 64)%Z with (bv_unsigned sp + -64)%Z by lia; exact T16
      | unfold cell64, cell; replace (bv_unsigned sp - 72)%Z with (bv_unsigned sp + -72)%Z by lia; exact T8 ]
    end.

  (* [comment removed for export] *)
  Ltac hand_P Hb9 Hc4 :=
    lazymatch type of Hb9 with _ = ?kv =>
      lazymatch goal with
      | HR : regs_ok _ _ _ |- _ =>
        pin_reg HR (10%bv:reg) (ELit kv) by (regv HR (10%bv:reg); rewrite blob_val_sub_u8w by lia; rewrite Hb9; reflexivity)
      end;
      run_fp 40%nat [0x82954%Z] noscr false;
      (* [comment removed for export] *)
      let Hc5 := fresh "Hc5" in
      branch_case as Hc5;
      [ lazymatch goal with HMs : frame_mod mem _ [_] |- _ => run_fp 30%nat (@nil Z) noscr false; post_exit HMs end
      | br_simpl_in E Hc5; rewrite Hsz, u_small in Hc5 by lia; rewrite ?Z.mod_small in Hc5 by lia; apply Z.ltb_ge in Hc5;
        lazymatch goal with
        | HR : regs_ok _ ?sr ?Rx, HF : fregs_ok _ _ _, HMs : frame_mod mem ?Mx [_], HR0 : id _, HF0 : id _,
          T72 : rdn _ ?Mx (Z_to_bv 64 (bv_unsigned sp + -8)) 8 = _,
          T64 : rdn _ ?Mx (Z_to_bv 64 (bv_unsigned sp + -16)) 8 = _,
          T56 : rdn _ ?Mx (Z_to_bv 64 (bv_unsigned sp + -24)) 8 = _,
          T48 : rdn _ ?Mx (Z_to_bv 64 (bv_unsigned sp + -32)) 8 = _,
          T40 : rdn _ ?Mx (Z_to_bv 64 (bv_unsigned sp + -40)) 8 = _,
          T32 : rdn _ ?Mx (Z_to_bv 64 (bv_unsigned sp + -48)) 8 = _,
          T24 : rdn _ ?Mx (Z_to_bv 64 (bv_unsigned sp + -56)) 8 = _,
          T16 : rdn _ ?Mx (Z_to_bv 64 (bv_unsigned sp + -64)) 8 = _,
          T8 : rdn _ ?Mx (Z_to_bv 64 (bv_unsigned sp + -72)) 8 = _
          |- runs_to _ (@mkst ?I ?Rx _ ?Mx _) _ =>
          unfold id in HR0, HF0; unhide HDC; unhide Hcs;
          eapply (tailP_entry ceil FPI regs mem rom ret data len bs sp buf C cs size Hmemset Hclassify Hret Hsp Hdok Hdheap Hshd Hsize Hin
                    HWC HCal HCheap HshC HshwC Henv Hro Hsb Hstk Hspal HWS HDC Hcs I Rx Mx (Z_to_bv 64 (bv_unsigned sp - 80)) kv);
          [ rewrite u_small by lia; reflexivity
          | regv_lin HR (2%bv:reg); rewrite Hsp; f_equal; lia
          | regv HR (8%bv:reg); exact Hbuf
          | regv HR (13%bv:reg); exact Hcs13
          | regv HR (18%bv:reg); exact HC
          | regv HR (21%bv:reg); reflexivity
          | regv HR (23%bv:reg); reflexivity
          | lia
          | cbn [cb]; exact Hc5
          | intros r Hr; exact (regs_same_on _ _ _ regs Rx rc_untouched HR0 HR ltac:(vm_compute; reflexivity) r Hr)
          | unfold fregs_kept; intros r Hr; exact (fregs_same_on _ _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity) r Hr)
          | exact HMs
          | unfold cell64, cell; replace (bv_unsigned sp - 8)%Z with (bv_unsigned sp + -8)%Z by lia; exact T72
          | unfold cell64, cell; replace (bv_unsigned sp - 16)%Z with (bv_unsigned sp + -16)%Z by lia; exact T64
          | unfold cell64, cell; replace (bv_unsigned sp - 24)%Z with (bv_unsigned sp + -24)%Z by lia; exact T56
          | unfold cell64, cell; replace (bv_unsigned sp - 32)%Z with (bv_unsigned sp + -32)%Z by lia; exact T48
          | unfold cell64, cell; replace (bv_unsigned sp - 40)%Z with (bv_unsigned sp + -40)%Z by lia; exact T40
          | unfold cell64, cell; replace (bv_unsigned sp - 48)%Z with (bv_unsigned sp + -48)%Z by lia; exact T32
          | unfold cell64, cell; replace (bv_unsigned sp - 56)%Z with (bv_unsigned sp + -56)%Z by lia; exact T24
          | unfold cell64, cell; replace (bv_unsigned sp - 64)%Z with (bv_unsigned sp + -64)%Z by lia; exact T16
          | unfold cell64, cell; replace (bv_unsigned sp - 72)%Z with (bv_unsigned sp + -72)%Z by lia; exact T8 ]
        end ]
    end.

  Lemma main_ok :
    runs_to SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x82814) mem rom)
            (RCQ regs mem rom ret FPI data len bs sp buf C cs size).
  Proof using ceil FPI regs mem rom ret data len bs sp buf C cs size Hmemset Hclassify Hra Hret Hsp Hbuf Hsz HC Hcs13 Hdok Hdheap Hshd Hsize Hin HWC HCal HCheap HshC HshwC Henv Hro Hshb Hsb Hstk Hspal HWS HDC Hcs.
    (* [comment removed for export] *)
    pose proof (Hmemset, Hclassify, Hra, Hret, Hsp, Hbuf, Hsz, HC, Hcs13, Hdok, Hdheap, Hshd, Hsize, Hin, HWC, HCal, HCheap,
                HshC, HshwC, Henv, Hro, Hshb, Hsb, Hstk, Hspal, HWS, HDC, Hcs) as HUSE; clear HUSE.
    pose proof (u64_range sp) as Rsp. pose proof (u64_range C) as RC. pose proof (u64_range cs) as Rcs.
    pose proof (u64_range buf) as Rbuf. pose proof (u64_range data) as Rdata.
    pose proof HWS as (W1 & W2 & W3 & W4). pose proof HWC as (V1 & V2 & V3 & V4).
    pose proof Hdok as (D1 & D2 & D3 & D4 & D5). pose proof Hin as (I1 & I2 & I3).
    hide HDC. hide Hcs.
    assert (HR : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [sub bs off 4; sub bs off 12])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [sub bs off 4; sub bs off 12])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof kn0_ok as HK.
    pose proof (frame_mod_refl mem [(Z_to_bv 64 (bv_unsigned sp - 2208), 2208%Z)]) as HMs.
    (* [comment removed for export] *)
    run_fp 40%nat (@nil Z) noscr true. fold_stack HMs.
    stack_cells T72 T64 T56 T48 T40 T32 T24 T16 T8.
    branch_case as Hc1.
    { run_fp 20%nat (@nil Z) noscr false. post_exit HMs. }
    br_simpl_in E Hc1. rewrite Hsz, u_small in Hc1 by lia. rewrite ?Z.mod_small in Hc1 by lia. apply Z.ltb_ge in Hc1.
    add_blob 4%Z 0%nat Hc1.
    (* [comment removed for export] *)
    run_fp 60%nat (@nil Z) noscr false.
    branch_case as Hc2.
    { (* [comment removed for export] *)
      clear Hc2.
      run_fp 10%nat (@nil Z) noscr false.
      branch_case as Hc3.
      { run_fp 30%nat (@nil Z) noscr false. post_exit HMs. }
      br_simpl_in E Hc3. rewrite Hsz, u_small in Hc3 by lia. rewrite ?Z.mod_small in Hc3 by lia. apply Z.ltb_ge in Hc3.
      add_blob 12%Z 1%nat Hc3.
      run_fp 80%nat (@nil Z) noscr false.
      (* [comment removed for export] *)
      branch_case as Hc4.
      2:{ run_fp 30%nat (@nil Z) noscr false. post_exit HMs. }
      hand_C Hc3 Hc4. }
    run_fp 10%nat (@nil Z) noscr false.
    branch_case as Hc3.
    { run_fp 30%nat (@nil Z) noscr false. post_exit HMs. }
    clear Hc2 Hc3.
    (* [comment removed for export] *)
    run_fp 10%nat (@nil Z) noscr false.
    branch_case as Hc4.
    { run_fp 30%nat (@nil Z) noscr false. post_exit HMs. }
    br_simpl_in E Hc4. rewrite Hsz, u_small in Hc4 by lia. rewrite ?Z.mod_small in Hc4 by lia. apply Z.ltb_ge in Hc4.
    add_blob 12%Z 1%nat Hc4.
    (* [comment removed for export] *)
    run_fp 40%nat [0x82900%Z] noscr false.
    pose proof (bs_byte_range bs (off + 8)) as Rb8. pose proof (bs_byte_range bs (off + 9)) as Rb9.
    assert (Hft : ((bs_byte bs (off + 8) = 0 /\ (bs_byte bs (off + 9) = 0 \/ bs_byte bs (off + 9) = 1 \/ bs_byte bs (off + 9) = 2
                                             \/ bs_byte bs (off + 9) = 3 \/ bs_byte bs (off + 9) = 4))
                   \/ 4 < 256 * bs_byte bs (off + 8) + bs_byte bs (off + 9))%Z) by lia.
    destruct Hft as [[Hb8 Hb9] | Hbig].
    2:{ (* [comment removed for export] *)
        run_fp 60%nat (@nil Z) (dirs [true]) false by (rewrite ?blob_val_sub_u8 by lia; lia).
        post_exit HMs. }
    pin_reg HR (12%bv:reg) (ELit 0) by (regv HR (12%bv:reg); rewrite blob_val_sub_u8w by lia; rewrite Hb8; reflexivity).
    destruct Hb9 as [Hb9 | [Hb9 | [Hb9 | [Hb9 | Hb9]]]].
    all: hand_P Hb9 Hc4.
  Qed.
End Main.

Theorem read_curve_as_ok : forall ceil,
  imemset20_contract SEGS as_asan ceil -> classify_contract_as SEGS as_asan ceil -> read_curve_contract_as SEGS as_asan ceil.
Proof.
  intros ceil Hm Hcl data len bs sp buf C cs size FPI regs mem rom ret Hra Hret PRE.
  unfold rcurve_pre_as in PRE. cbv zeta in PRE. cbn [al_abi as_asan] in PRE.
  destruct PRE as (Hsp & Hbuf & Hsz & HC & Hcs13 & (Hdok & Hdheap & Hdal & Hshd) & Hsize & Hin & HWC & HCal & HCheap & HshC & HshwC
                   & HDC & Hro & Hshb & Henv & Hfr & Hcs).
  destruct Hfr as (Hstk & Hspal & HWS). unfold RCURVE_D, heapish, stackish in *. app_facts.
  assert (Hsb : sbcell SEGS 0x9eaf0 0xa6bb8 mem).
  { destruct (asan_cells64 SEGS mem Henv) as (G1 & G2 & _). split; [exact G1 | exact G2]. }
  apply runs_to_contract with
    (P := fun FPI' regs' mem' => regs_kept abi_kept regs regs'
            /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI'))
            /\ rcurve_post_as SEGS data len bs sp buf C cs size regs mem FPI' regs' mem').
  exact (main_ok ceil FPI regs mem rom ret data len bs sp buf C cs size Hm Hcl Hra Hret Hsp Hbuf Hsz HC Hcs13
           Hdok ltac:(plc) Hshd Hsize Hin HWC HCal ltac:(plc) HshC HshwC Henv Hro Hshb Hsb ltac:(plc) Hspal HWS HDC Hcs).
Qed.
