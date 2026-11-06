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
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs LibFrame LibTagsSpec LibWP2Spec.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs AsRtSpec AsLibTagsSpec AsLibWP2Spec AsLibTagsLib AsLibTagsCall AsLibFPLib AsLibParseLib AsLibFrame AsLibEnv AsLibParseSpec AsLibParseDefs AsLibKit AsLibParseF AsLibParseE AsLibParseD AsLibParseC3 AsLibParseC2 AsLibParseC1 AsLibParseB AsLibParseA2 AsLibCurveSpec AsLibBswap AsLibBswapSx AsLibPlace.
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

#[local] Abbreviation SEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Section TabArith.
Local Open Scope Z_scope.
Lemma a1_u_zbv : forall z, bv_unsigned (Z_to_bv 64 z) = z mod 2 ^ 64.
Proof. intros. rewrite Z_to_bv_unsigned. apply bv_wrap64_mod. Qed.

Lemma mul32_mod0 : forall v : word, bv_unsigned (mul_div M_MUL (Z_to_bv 64 4294967296) v) mod 4294967296 = 0.
Proof.
  intros v. rewrite m_mul. unfold v_mul. rewrite a1_u_zbv. rewrite (a1_u_zbv 4294967296).
  change (4294967296 mod 2 ^ 64) with 4294967296. change (2 ^ 64) with (4294967296 * 4294967296).
  rewrite (Z.mul_comm 4294967296 (bv_unsigned v)). rewrite Z.mul_mod_distr_r by lia. apply Z_mod_mult.
Qed.

Lemma tab_arith : forall (X : word) (t : Z),
  bv_unsigned (alu64 ALU_SRL X (Z_to_bv 64 32)) = t ->
  bv_unsigned X mod 4294967296 = 0 ->
  bv_unsigned (alu64 ALU_ADD (alu64 ALU_ADD (alu64 ALU_SRL X (Z_to_bv 64 28))
                                  (mul_div M_MUL (Z_to_bv 64 (-1)) (alu64 ALU_SRL X (Z_to_bv 64 30))))
                         (Z_to_bv 64 132)) = 12 * t + 132.
Proof.
  intros X t HT HM.
  pose proof (u64_range X) as RX.
  rewrite alu_srl in HT. unfold v_srl in HT. rewrite a1_u_zbv, (a1_u_zbv 32) in HT.
  change (32 mod 2 ^ 64) with 32 in HT. change (32 mod 64) with 32 in HT.
  rewrite Z.shiftr_div_pow2 in HT by lia.
  assert (Ht : 0 <= t < 4294967296).
  { rewrite <- HT. split; [apply Z.mod_pos_bound; lia|].
    rewrite Z.mod_small; [apply Z.div_lt_upper_bound; [lia|]; change (2^32 * 4294967296) with (2^64); lia|].
    split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 64) with (2^32 * 2^32) at 1. nia. }
  assert (HX : bv_unsigned X = 4294967296 * t).
  { rewrite Z.mod_small in HT.
    - pose proof (Z.div_mod (bv_unsigned X) 4294967296 ltac:(lia)) as E. change (2 ^ 32) with 4294967296 in HT. lia.
    - split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 64) with (2^32 * 2^32) at 1. nia. }
  rewrite !alu_add, !alu_srl, m_mul. unfold v_add, v_srl, v_mul.
  rewrite !a1_u_zbv. change (28 mod 2 ^ 64) with 28. change (28 mod 64) with 28. change (30 mod 2 ^ 64) with 30. change (30 mod 64) with 30.
  rewrite !Z.shiftr_div_pow2 by lia. rewrite HX.
  replace (4294967296 * t / 2 ^ 28) with (16 * t) by (replace (4294967296 * t) with (16 * t * 2 ^ 28) by lia; rewrite Z_div_mult by lia; reflexivity).
  replace (4294967296 * t / 2 ^ 30) with (4 * t) by (replace (4294967296 * t) with (4 * t * 2 ^ 30) by lia; rewrite Z_div_mult by lia; reflexivity).
  rewrite alu_add. unfold v_add. rewrite !a1_u_zbv.
  rewrite (Z.mod_small (16 * t)) by lia. rewrite (Z.mod_small (4 * t)) by lia.
  change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1). change (132 mod 2 ^ 64) with 132.
  replace (((2 ^ 64 - 1) * (4 * t)) mod 2 ^ 64) with ((- (4 * t)) mod 2 ^ 64).
  2:{ replace ((2 ^ 64 - 1) * (4 * t)) with (- (4 * t) + (4 * t) * 2 ^ 64) by lia. rewrite Z_mod_plus_full. reflexivity. }
  rewrite Zplus_mod_idemp_r. replace (16 * t + - (4 * t)) with (12 * t) by lia.
  rewrite (Z.mod_small (12 * t)) by lia. apply Z.mod_small. lia.
Qed.


(* [comment removed for export] *)
Lemma zext32_val : forall (v : word),
  bv_unsigned (alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 4294967296) v) (Z_to_bv 64 32)) = bv_unsigned v mod 4294967296.
Proof.
  intros v. pose proof (u64_range v).
  rewrite alu_srl, m_mul. unfold v_srl, v_mul. rewrite !a1_u_zbv. change (32 mod 2 ^ 64) with 32. change (32 mod 64) with 32.
  change (4294967296 mod 2 ^ 64) with 4294967296.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 64) with (4294967296 * 4294967296) at 1.
  rewrite (Z.mul_comm 4294967296 (bv_unsigned v)). rewrite Z.mul_mod_distr_r by lia. change (2^32) with 4294967296. rewrite Z_div_mult by lia.
  apply Z.mod_small. pose proof (Z.mod_pos_bound (bv_unsigned v) 4294967296 ltac:(lia)). change (2^64) with (4294967296 * 4294967296). lia.
Qed.

End TabArith.

Section A1.
  Variable ceil : Z.
  Variables (FP0 : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp data prio P : word) (len fs : Z) (bs : list byte) (ch : chain).
  Hypothesis HE : PENV ceil regs mem ret sp data prio P len fs bs ch.
  Hypothesis Hgettag : gettag_contract_as SEGS as_asan ceil.
  Hypothesis Hrc : read_curve_contract_as SEGS as_asan ceil.
  Hypothesis Hmc : imemcpy32_contract SEGS as_asan ceil.
  Hypothesis Hxyz : xyzd50_contract_as SEGS as_asan ceil.
  Hypothesis Ha2b : read_a2b_contract_as SEGS as_asan ceil.
  Hypothesis Hb2a : read_b2a_contract_as SEGS as_asan ceil.

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

  #[local] Abbreviation psz := (be32 bs 0).
  #[local] Abbreviation tc := (be32 bs 128).
  (* [comment removed for export] *)
  #[local] Abbreviation lepcs := (bs_byte bs 20 + bs_byte bs 21 * 256 + bs_byte bs 22 * 65536 + bs_byte bs 23 * 16777216)%Z.
  #[local] Abbreviation letc := (bs_byte bs 128 + bs_byte bs 129 * 256 + bs_byte bs 130 * 65536 + bs_byte bs 131 * 16777216)%Z.

  (* [comment removed for export] *)
  Definition nu (k : nat) : Z := bs_byte bs (Z.of_nat k).
  Definition atomu (d : nat) : expr * (bool * nat) := (EBlob false 0 (Z.of_nat d) 1, (false, d)).
  Definition atoms_s (d : nat) : expr * (bool * nat) := (EBlob true 0 (Z.of_nat d) 1, (true, d)).
  Definition atoms : list (expr * (bool * nat)) :=
    map atomu [0; 1; 2; 8; 9; 10; 11; 16; 17; 18; 19; 20; 21; 22; 23; 36; 37; 38; 39; 68; 69; 70; 72; 73; 74; 76; 77; 78; 128; 129; 130; 131]%nat
    ++ map atoms_s [3; 71; 75; 79]%nat.

  Lemma nu_range : forall k, (0 <= nu k < 256)%Z.
  Proof. intros k. unfold nu. apply bs_byte_range. Qed.

  Lemma atoms_ok_at : forall (FPc : FPState) (Rc : bvmap 5 word) (ws : list word),
    (132 <= len)%Z ->
    atoms_ok (Env (vals_ev (junk_vals Rc ++ fjunk_vals (fp_regs (FPState:=FPc)) ++ ws)) (blobs_ev [bs])) nu atoms.
  Proof.
    intros FPc Rc ws Hlen.
    destruct HE as (_ & _ & _ & _ & ((D1 & D2 & _) & _) & _).
    unfold atoms, atoms_ok. cbn [map app].
    repeat (apply Forall_cons); [..|apply Forall_nil];
      unfold atomu, atoms_s, atom_ok; cbn [edenot eb blobs_ev nth Z.of_nat Pos.of_succ_nat Pos.succ];
      first [rewrite blob_val_u8 by lia | rewrite blob_val_s8 by lia]; unfold nu, bs_byte; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.to_nat Pos.to_nat Pos.iter_op Nat.add]; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Ltac pin_bytes HR r v ids Hat Epsz Etc :=
    pin_reg HR r v by
      (rewrite (HR r);
       lazymatch goal with |- edenot ?E1 ?e = _ =>
         apply bv_eq; rewrite (beval_bytes E1 nu nu_range atoms e ids Hat ltac:(cbn; lia) ltac:(vm_compute; reflexivity));
         cbn [edenot ev vals_ev]; ev_simpl E1; rewrite u_small by lia; cbv [bytes_val nu Z.of_nat Pos.of_succ_nat Pos.succ];
         rewrite ?Epsz, ?Etc; lia
       end).

  (* [comment removed for export] *)
  Ltac log_frame RS Hfr HR2z H21 :=
    lazymatch goal with
    | EQM : ?M2 = mem_denot ?E2 ?M1 ?log, HLF : log_flat _ _ |- _ =>
      assert (Hfr : frame_mod M1 M2 (regions_denot E2 RS))
        by (rewrite EQM; apply (frame_mod_mem_denot E2 M1 log RS); [exact HLF | flats E2 | vm_compute; reflexivity]);
      unfold regions_denot in Hfr; cbn [map fst snd] in Hfr; unfold adenot in Hfr; cbn [a_base a_off edenot] in Hfr;
      ev_simpl_in E2 Hfr; rewrite ?H21 in Hfr; unfold v_addi in Hfr; clear EQM HLF
    end.

  (* [comment removed for export] *)
  Ltac advance RS HSo Hfo HFSo HSn Hfn HFSn HR2z H21 :=
    let Hfr := fresh "Hfr" in
    log_frame RS Hfr HR2z H21;
    assert (HSn : SAVED _) by (eapply (SAVED_frame FP0 regs sp); [exact HSo | exact Hfr | solve_apart | lia]);
    assert (Hfn : frame_mod mem _ BIG)
      by (eapply frame_BIG_app; [exact Hfo | exact Hfr |]; apply bincl_of; repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
          first [ apply (in_big_stack ceil regs mem rom ret sp data prio P len fs bs ch HE); lia
                | apply (in_big_P ceil regs mem rom ret sp data prio P len fs bs ch HE); lia ]);
    assert (HFSn : FSOK _)
      by (let HFa := fresh "HFa" in let hh := fresh "hh" in let HFb := fresh "HFb" in
          destruct HFSo as [HFa [hh HFb]]; split;
          [ eapply (fs_flags0_but_frame fs [] []); [exact Hfr | exact HFa | lia | unfold FS_SIZE; lia |];
            intros i Hi Hni; split; [exact Hni|]; unfold FS_FLAGS0_LEN in Hi; unfold FS_FLAGS0; solve_apart
          | exists hh; unfold FS_HINT0; eapply acellw_frame; [exact Hfr | exact HFb | lia | lia | solve_apart] ]);
    clear Hfr HSo Hfo HFSo.

  Section Hdr.
    Variables (FPI : FPState) (R : bvmap 5 word) (M : word -> option byte).
    Hypothesis HC : COMMON FPI R.
    Hypothesis HS : SAVED M.
    Hypothesis Hf : frame_mod mem M BIG.
    Hypothesis HFS : FSOK M.
    Hypothesis Hz : zero M (bv_unsigned P) 976.
    Hypothesis H8 : getr R 8 = prio.
    Hypothesis H9 : getr R 9 = Z_to_bv 64 2.
    Hypothesis H18 : getr R 18 = Z_to_bv 64 len.
    Hypothesis H19 : getr R 19 = data.
    Hypothesis Hlen : (132 <= len)%Z.

    Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI))
                        ++ [Z_to_bv 64 psz; Z_to_bv 64 tc; Z_to_bv 64 lepcs; Z_to_bv 64 letc; Z_to_bv 64 len; prio])) (blobs_ev [bs]).

    Definition kn_h : list kentry :=
      [KImg 0x20d00 0x20f20;
       KAlign (EVar 2) 16; KRange (EVar 2) (AS_STKLO + 2528) (2 ^ 47 - 368); KWr (SA (EVar 2) (-2528)) 2896;
       KAlign (EVar 21) 64; KRange (EVar 21) 1 (2 ^ 47 - 976); KWr (SA (EVar 21) 0) 976;
       KZero (SA (EAlu ALU_SRL (EVar 21) (ELit 3)) SB) (ELit 122);
       KZero (SA (EVar 21) 0) (ELit 976);
       KAlign (EVar 19) 16; KRange (EVar 19) 1 (2 ^ 47 - 132);
       KRange (EVar 64) 0 (2^32 - 1); KRange (EVar 67) 0 (2^32 - 1); KRange (EVar 68) 132 (2^26); KRange (EVar 69) 1 (2 ^ 47 - 8);
       KShad (EVar 19) (EVar 68) SB;
       KBlobD (SA (EVar 19) 0) (EVar 68) 0;
       KRange (EAlu ALU_ADD (EVar 19) (EVar 68)) 0 (2 ^ 47 - 16);
       KDisj (SA (EVar 21) 0) 976 ZSH ZSHL; KDisj (SA (EVar 21) 0) 976 ZIMG ZIMGL; KDisj (SA (EVar 21) 0) 976 (SA (EVar 2) (-2528)) 2896;
       KDisj (SA (EVar 69) 0) 8 ZSH ZSHL; KDisj (SA (EVar 69) 0) 8 ZIMG ZIMGL; KDisj (SA (EVar 69) 0) 8 (SA (EVar 2) (-2528)) 2896].

    Lemma kn_h_ok : know_ok SEGS E M kn_h.
    Proof.
      destruct HC as (H2 & H3 & H4 & H21 & H22 & HFK).
      pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
      destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13).
      destruct (penv_at ceil regs mem rom ret sp data prio P len fs bs ch HE M Hf) as (((D1 & D2 & D3 & D4 & D5) & _ & Hdal & Hshd) & _ & _ & _ & _ & _ & _ & WP & HshP & WS & _ & _ & Hro).
      pose proof HE as HE'. destruct HE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpal & _).
      pose proof (u64_range sp). pose proof (u64_range P). pose proof (u64_range data). pose proof (u64_range prio). unfold FS_SIZE in *.
      pose proof (be32_range bs 0). pose proof (bs_byte_range bs 128). pose proof (bs_byte_range bs 129). pose proof (bs_byte_range bs 130). pose proof (bs_byte_range bs 131).
      destruct WS as (_ & _ & _ & S4). destruct WP as (_ & _ & _ & W4).
      unfold kn_h, know_ok.
      repeat (apply Forall_cons); [..|apply Forall_nil].
      - apply kimg_intro; [lia | lia |]. intros i Hi. apply (Hro 0x20d00%Z 0x20f20%Z i); [cbn; tauto | exact Hi].
      - apply kalign_intro; [lia|]. cbn. apply (mod_down _ 16 1); [lia|lia|]. change (16*1)%Z with 16%Z.
        rewrite <- (Z_to_bv_bv_unsigned 64 (getr R 2)), H2, u_small by lia. apply mod_sub_multiple; [lia | exact N6 | reflexivity].
      - apply krange_intro; cbn. rewrite H2. lia.
      - apply (kwr_intro SEGS E M (EVar 2) (getr R 2) (-2528) 2896); cbn; try lia; try reflexivity.
        replace (bv_unsigned (getr R 2) + -2528)%Z with (bv_unsigned sp - 2896)%Z by lia. exact S4.
      - apply kalign_intro; [lia|]. cbn; rewrite H21. exact Hpal.
      - apply krange_intro; cbn. rewrite H21. lia.
      - apply (kwr_intro SEGS E M (EVar 21) P 0 976); cbn; rewrite ?H21; try lia; try reflexivity. rewrite Z.add_0_r. exact W4.
      - eapply (kzero_shz_intro SEGS E M (EVar 21) P 122); [cbn; exact H21 | exact HshP | lia | lia].
      - apply (kzero_intro SEGS E M (EVar 21) P 0 (ELit 976) 976);
          [ cbn; exact H21 | reflexivity | lia | lia | lia | intros i Hi; rewrite Z.add_0_r; apply Hz; exact Hi ].
      - apply kalign_intro; [lia|]. cbn; rewrite H19. exact Hdal.
      - apply krange_intro; cbn. rewrite H19. lia.
      - apply krange_intro; cbn. rewrite u_small by lia. lia.
      - apply krange_intro; cbn. rewrite u_small by lia. lia.
      - apply krange_intro; cbn. rewrite u_small by lia. lia.
      - apply krange_intro; cbn. lia.
      - eapply (kshad_intro SEGS E M (EVar 19) (EVar 68) data len); [cbn; exact H19 | cbn; rewrite u_small by lia; reflexivity | lia | lia | exact Hshd].
      - cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off edenot]. ev_simpl E.
        rewrite H19, u_small by lia. split; [lia|]. split; [exact D2|]. intros i Hi. rewrite Z.add_0_r. apply D5. exact Hi.
      - eapply krange_add_intro; [place_den | place_den | rewrite ?u_small by lia; lia | lia].
      - kdisj_place.
      - kdisj_place.
      - kdisj_place.
      - kdisj_place.
      - kdisj_place.
      - kdisj_place.
    Qed.

    Lemma hdr_run : runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x819d0) M rom) Q.
    Proof.
      pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H21 & H22 & HFK).
      pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
      destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13). unfold FS_SIZE in N2.
      pose proof HE as HE'. destruct HE' as (Hra & Hret & Hsp & _ & _ & Hdar & _ & _ & _ & _ & _ & _ & _ & Hqp & _ & Hpal & _ & _ & Hp1 & Hp2 & _).
      unfold FS_FRAMES5, FS_SIZE in Hp1, Hp2, Hdar.
      pose proof (u64_range sp) as Rsp. pose proof (u64_range P) as RP. pose proof (u64_range data) as Rd. pose proof (u64_range prio) as Rq.
      pose proof (be32_range bs 0) as Rpsz. pose proof (be32_range bs 128) as Rtc.
      assert (Epsz : be32 bs 0 = (bs_byte bs 0 * 16777216 + bs_byte bs 1 * 65536 + bs_byte bs 2 * 256 + bs_byte bs 3)%Z) by reflexivity.
      assert (Etc : be32 bs 128 = (bs_byte bs 128 * 16777216 + bs_byte bs 129 * 65536 + bs_byte bs 130 * 256 + bs_byte bs 131)%Z) by reflexivity.
      pose proof (bs_byte_range bs 0) as B0. pose proof (bs_byte_range bs 1) as B1. pose proof (bs_byte_range bs 2) as B2. pose proof (bs_byte_range bs 3) as B3.
      pose proof (bs_byte_range bs 20) as B20. pose proof (bs_byte_range bs 21) as B21. pose proof (bs_byte_range bs 22) as B22. pose proof (bs_byte_range bs 23) as B23.
      pose proof (bs_byte_range bs 128) as B128. pose proof (bs_byte_range bs 129) as B129. pose proof (bs_byte_range bs 130) as B130. pose proof (bs_byte_range bs 131) as B131.
      assert (HR2z : getr R 2 = Z_to_bv 64 (bv_unsigned sp - 368)) by (rewrite <- (Z_to_bv_bv_unsigned 64 (getr R 2)), H2; reflexivity).
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs])).
      assert (HFr : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs])).
      pose proof kn_h_ok as HK. unfold kn_h in HK.
      pose proof (atoms_ok_at FPI R [Z_to_bv 64 psz; Z_to_bv 64 tc; Z_to_bv 64 lepcs; Z_to_bv 64 letc; Z_to_bv 64 len; prio] Hlen) as Hat.
      change (atoms_ok E nu atoms) in Hat.
      pin_reg HR (22%bv:reg) (ELit SB) by (regv HR (22%bv:reg); exact H22).
      pin_reg HR (18%bv:reg) (EVar 68) by (regv HR (18%bv:reg); exact H18).
      pin_reg HR (8%bv:reg) (EVar 69) by (regv HR (8%bv:reg); exact H8).
      pin_reg HR (9%bv:reg) (ELit 2) by (regv HR (9%bv:reg); exact H9).
      clear Hz HR2z.
      (* [comment removed for export] *)
      run_fp 40%nat [0x81a50%Z] noscr true hints keep_all.
      advance [(SA (EVar 21) 0, 8%Z)] HS Hf HFS HS1 Hf1 HFS1 H2 H21.
      pin_bytes HR (15%bv:reg) (EVar 64) [3; 2; 1; 0]%nat Hat Epsz Etc.
      (* [comment removed for export] *)
      run_fp 80%nat [0x81b98%Z] noscr true hints keep_all.
      advance [(SA (EVar 21) 8, 4%Z); (SA (EVar 2) 64, 8%Z); (SA (EVar 21) 12, 4%Z)] HS1 Hf1 HFS1 HS2 Hf2 HFS2 H2 H21.
      pin_bytes HR (16%bv:reg) (EVar 66) [20; 21; 22; 23]%nat Hat Epsz Etc.
      (* [comment removed for export] *)
      run_fp 120%nat [0x81d44%Z] noscr true hints keep_all.
      advance [(SA (EVar 2) 0, 8%Z); (SA (EVar 21) 16, 4%Z); (SA (EVar 2) 16, 8%Z); (SA (EVar 2) 8, 8%Z); (SA (EVar 2) 56, 8%Z);
               (SA (EVar 2) 48, 8%Z); (SA (EVar 2) 40, 8%Z); (SA (EVar 2) 32, 8%Z); (SA (EVar 2) 24, 8%Z)] HS2 Hf2 HFS2 HS3 Hf3 HFS3 H2 H21.
      pin_bytes HR (18%bv:reg) (EVar 67) [128; 129; 130; 131]%nat Hat Epsz Etc.
      (* [comment removed for export] *)
      run_fp 20%nat [0x81e98%Z] noscr true hints keep_all.
      advance [(SA (EVar 21) 20, 4%Z)] HS3 Hf3 HFS3 HS4 Hf4 HFS4 H2 H21.
      Ltac exit0_now HR HF H2 H3 H4 H21 H22 HFK HSx Hfx HFSx :=
        lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
          apply (exit_ok ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE I R' M' 0);
          [ common HR HF H2 H3 H4 H21 H22 HFK | regv HR (10%bv:reg); reflexivity | lia | exact HSx | exact Hfx | exact HFSx | intros; exfalso; lia ]
        end.
      branch_case as Hsig.
      { lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
          apply (fail_ok ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE I R' M');
          [ common HR HFr H2 H3 H4 H21 H22 HFK | exact HS4 | exact Hf4 | exact HFS4 ] end. }
      run_fp 20%nat [0x81e9c%Z] noscr false.
      (* [comment removed for export] *)
      branch_case as Hver.
      { exit0_now HR HFr H2 H3 H4 H21 H22 HFK HS4 Hf4 HFS4. }
      run_fp 10%nat [0x81e9c%Z] noscr false.
      (* [comment removed for export] *)
      branch_case as Hlp.
      { exit0_now HR HFr H2 H3 H4 H21 H22 HFK HS4 Hf4 HFS4. }
      rewrite branch_taken_Z in Hlp. cbv beta iota in Hlp. cbn [edenot] in Hlp. ev_simpl_in E Hlp. rewrite !u_small in Hlp by lia. apply Z.ltb_ge in Hlp.
      run_fp 10%nat [0x81e9c%Z] noscr false.
      (* [comment removed for export] *)
      branch_case as Htab.
      { exit0_now HR HFr H2 H3 H4 H21 H22 HFK HS4 Hf4 HFS4. }
      lazymatch type of HR with regs_ok _ ?sr _ =>
        let e12 := eval vm_compute in (sr_get sr (12%bv:reg)) in
        assert (HT : bv_unsigned (edenot E (EAlu ALU_SRL (EMd M_MUL (ELit 4294967296) e12) (ELit 32))) = tc)
          by (rewrite (beval_bytes E nu nu_range atoms (EAlu ALU_SRL (EMd M_MUL (ELit 4294967296) e12) (ELit 32)) [131;130;129;128]%nat Hat ltac:(cbn; lia) ltac:(vm_compute; reflexivity));
              cbv [bytes_val nu Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite Etc; lia);
        pose proof (mul32_mod0 (edenot E e12)) as HM0;
        pose proof (tab_arith (edenot E (EMd M_MUL (ELit 4294967296) e12)) tc HT HM0) as HV;
        rewrite branch_taken_Z in Htab; cbv beta iota in Htab;
        lazymatch type of Htab with (Z.ltb _ (bv_unsigned (edenot _ ?b))) = false =>
          let HV' := fresh "HV'" in
          assert (HV' : bv_unsigned (edenot E b) = (12 * tc + 132)%Z) by exact HV;
          rewrite HV' in Htab; clear HV' end;
        cbn [edenot] in Htab; ev_simpl_in E Htab; rewrite u_small in Htab by lia; apply Z.ltb_ge in Htab;
        (* [comment removed for export] *)
        assert (Hb7 : Z.testbit (nu 128%nat) 7 = false)
          by (cbv [nu Z.of_nat Pos.of_succ_nat Pos.succ]; apply tb_small_high; cbn [Z.pow Z.pow_pos Pos.iter Z.mul]; lia);
        assert (E12 : edenot E e12 = Z_to_bv 64 tc)
          by (apply bv_eq; rewrite (beval_bytes_sx E nu nu_range atoms e12 [131; 130; 129; 128]%nat 128%nat Hat ltac:(cbn; lia) Hb7 ltac:(vm_compute; reflexivity));
              rewrite u_small by lia; cbv [bytes_val nu Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite Etc; lia);
        clear HT HM0 HV
      end.
      (* [comment removed for export] *)
      assert (HR2z : getr R 2 = Z_to_bv 64 (bv_unsigned sp - 368)) by (rewrite <- (Z_to_bv_bv_unsigned 64 (getr R 2)), H2; reflexivity).
      kcell HK (EVar 2) 16%Z 8%nat (ELit 2) K16. kcell HK (EVar 2) 0%Z 8%nat (EVar 66) K0.
      kcell HK (EVar 2) 64%Z 8%nat (EVar 68) K64. kcell HK (EVar 2) 56%Z 8%nat (EVar 69) K56.
      kcell HK (EVar 21) 0%Z 8%nat (EVar 19) KP0. kcell HK (EVar 21) 8%Z 4%nat (EExt false 0 4 (EVar 64)) KP8.
      cbn [edenot] in KP8. ev_simpl_in E KP8. rewrite ext_val_4_small in KP8 by lia.
      lazymatch type of E12 with edenot _ ?e12 = _ =>
        kcell HK (EVar 21) 20%Z 4%nat (EExt false 0 4 e12) KP20;
        let E12' := fresh "E12'" in pose proof E12 as E12'; cbn [edenot] in E12'; ev_simpl_in E E12';
        rewrite E12' in KP20; clear E12'; rewrite ext_val_4_small in KP20 by lia end.
      kcell_auto HK (EVar 2) 24%Z 8%nat K24. kcell_auto HK (EVar 2) 8%Z 8%nat K8.
      kcell_auto HK (EVar 2) 32%Z 8%nat K32. kcell_auto HK (EVar 2) 40%Z 8%nat K40. kcell_auto HK (EVar 2) 48%Z 8%nat K48.
      lazymatch type of HK with know_ok _ ?E1 ?Mx ?kn =>
        pose proof (kzero_lookup_sound SEGS E1 Mx kn (EVar 21) 24 952 HK ltac:(vm_compute; reflexivity) ltac:(lia)) as Kz;
        cbn [edenot] in Kz; ev_simpl_in E1 Kz; rewrite H21 in Kz
      end.
      lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ ?M2 _) _ =>
        lazymatch type of K24 with _ = Some (word_to_le_bytes 8 ?v24) =>
        lazymatch type of K8 with _ = Some (word_to_le_bytes 8 ?v8) =>
        lazymatch type of K32 with _ = Some (word_to_le_bytes 8 ?v32) =>
        lazymatch type of K40 with _ = Some (word_to_le_bytes 8 ?v40) =>
        lazymatch type of K48 with _ = Some (word_to_le_bytes 8 ?v48) =>
        assert (HF4 : ZFACTS sp data prio P len psz tc (Z_to_bv 64 lepcs) M2);
        [ split; [| exact Kz]; unfold ZH; cbv zeta;
          split; [replace (bv_unsigned sp - 352)%Z with (bv_unsigned sp - 368 + 16)%Z by lia; exact K16|];
          split; [replace (bv_unsigned sp - 368)%Z with (bv_unsigned sp - 368 + 0)%Z at 1 by lia; exact K0|];
          split; [replace (bv_unsigned sp - 304)%Z with (bv_unsigned sp - 368 + 64)%Z by lia; exact K64|];
          split; [replace (bv_unsigned sp - 312)%Z with (bv_unsigned sp - 368 + 56)%Z by lia; exact K56|];
          split; [unfold cell64, LibDefs.cell; rewrite <- (Z.add_0_r (bv_unsigned P)); exact KP0|];
          split; [split; [lia | exact KP8]|];
          split; [lia | exact KP20]
        | apply (stageX_run ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE Hgettag Hrc Hmc Hxyz Ha2b Hb2a psz tc (Z_to_bv 64 lepcs)
                   v24 v8 v32 v40 v48 ltac:(lia) ltac:(lia) M2 HS4 Hf4 HFS4 HF4
                   ltac:(unfold cell64, LibDefs.cell; replace (bv_unsigned sp - 344)%Z with (bv_unsigned sp - 368 + 24)%Z by lia; exact K24)
                   ltac:(unfold cell64, LibDefs.cell; replace (bv_unsigned sp - 360)%Z with (bv_unsigned sp - 368 + 8)%Z by lia; exact K8)
                   ltac:(unfold cell64, LibDefs.cell; replace (bv_unsigned sp - 336)%Z with (bv_unsigned sp - 368 + 32)%Z by lia; exact K32)
                   ltac:(unfold cell64, LibDefs.cell; replace (bv_unsigned sp - 328)%Z with (bv_unsigned sp - 368 + 40)%Z by lia; exact K40)
                   ltac:(unfold cell64, LibDefs.cell; replace (bv_unsigned sp - 320)%Z with (bv_unsigned sp - 368 + 48)%Z by lia; exact K48)
                   I R2);
          [ common HR HFr H2 H3 H4 H21 H22 HFK
          | unfold AREGS;
            split; [regv HR (11%bv:reg); apply u_small; lia|];
            split; [regv HR (12%bv:reg); first [rewrite E12 | pose proof E12 as E12'; cbn [edenot] in E12'; ev_simpl_in E E12'; rewrite E12']; apply u_small; lia|];
            split; [regv HR (18%bv:reg); rewrite u_small by lia; rewrite Etc; lia|];
            regv HR (19%bv:reg); exact H19 ] ]
        end end end end end end.
    Qed.
  End Hdr.
End A1.
