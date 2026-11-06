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
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs AsRtSpec AsLibTagsLib AsLibPlace.
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_wrap_of_swrap : forall n z, bv_wrap n (bv_swrap n z) = bv_wrap n z.
Proof.
  intros n z. unfold bv_swrap, bv_wrap.
  rewrite Zdiv.Zminus_mod_idemp_l. f_equal. lia.
Qed.

Lemma wtlb4_lo : forall w : word, word_to_le_bytes 4 (ext_val true 0 4 w) = Z_to_le_bytes 4 (bv_unsigned w).
Proof.
  intros w. unfold word_to_le_bytes, ext_val, ext_Z. rewrite Z_to_bv_unsigned.
  rewrite <- (Z_to_le_bytes_wrap 4 32 (bv_wrap 64 _)) by (cbn; lia).
  rewrite bv_wrap_bv_wrap by (cbn; lia).
  change (8 * N.of_nat 4)%N with 32%N. rewrite bv_wrap_of_swrap.
  change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.div_1_r.
  change (2 ^ (8 * Z.of_nat 4))%Z with (bv_modulus 32). fold (bv_wrap 32 (bv_unsigned w)).
  rewrite bv_wrap_idemp. apply Z_to_le_bytes_wrap. cbn; lia.
Qed.

Lemma wtlb4_hi : forall w : word, word_to_le_bytes 4 (ext_val true 4 4 w) = Z_to_le_bytes 4 (bv_unsigned w / 2 ^ 32).
Proof.
  intros w. unfold word_to_le_bytes, ext_val, ext_Z. rewrite Z_to_bv_unsigned.
  rewrite <- (Z_to_le_bytes_wrap 4 32 (bv_wrap 64 _)) by (cbn; lia).
  rewrite bv_wrap_bv_wrap by (cbn; lia).
  change (8 * N.of_nat 4)%N with 32%N. rewrite bv_wrap_of_swrap.
  change (2 ^ (8 * Z.of_nat 4))%Z with (bv_modulus 32). fold (bv_wrap 32 (bv_unsigned w / bv_modulus 32)).
  rewrite bv_wrap_idemp. apply Z_to_le_bytes_wrap. cbn; lia.
Qed.

Lemma wtlb4_ext0 : forall x : word, word_to_le_bytes 4 (ext_val false 0 4 x) = word_to_le_bytes 4 x.
Proof.
  intros x. unfold word_to_le_bytes, ext_val, ext_Z. rewrite Z_to_bv_unsigned.
  rewrite <- (Z_to_le_bytes_wrap 4 32 (bv_wrap 64 _)) by (cbn; lia).
  rewrite bv_wrap_bv_wrap by (cbn; lia).
  change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.div_1_r.
  change (2 ^ (8 * Z.of_nat 4))%Z with (bv_modulus 32). fold (bv_wrap 32 (bv_unsigned x)).
  rewrite bv_wrap_idemp. apply Z_to_le_bytes_wrap. cbn; lia.
Qed.

Lemma cell64_halves : forall M (a : Z) (w : word),
  (0 <= a)%Z -> (a + 8 <= 2 ^ 64)%Z ->
  rdn SEGS M (Z_to_bv 64 a) 4 = Some (word_to_le_bytes 4 (ext_val true 0 4 w)) ->
  rdn SEGS M (Z_to_bv 64 (a + 4)) 4 = Some (word_to_le_bytes 4 (ext_val true 4 4 w)) ->
  rdn SEGS M (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 w).
Proof.
  intros M a w Ha0 Ha8 Hlo Hhi.
  change 8%nat with (4 + 4)%nat.
  replace (word_to_le_bytes (4 + 4) w) with (word_to_le_bytes 4 (ext_val true 0 4 w) ++ word_to_le_bytes 4 (ext_val true 4 4 w)).
  - apply SeqExec.rdn_app; [exact Hlo|]. rewrite w_add_nat, u_small by lia. exact Hhi.
  - rewrite wtlb4_lo, wtlb4_hi. unfold word_to_le_bytes.
    rewrite <- (firstn_skipn 4 (Z_to_le_bytes (4 + 4) (bv_unsigned w))).
    rewrite firstn_Z_to_le_bytes by lia. rewrite skipn_Z_to_le_bytes by lia. reflexivity.
Qed.

Lemma add_lit_word : forall (P : word) (o : Z), (0 <= o < 2 ^ 64)%Z ->
  alu64 ALU_ADD P (Z_to_bv 64 o) = Z_to_bv 64 (bv_unsigned P + o).
Proof.
  intros P o Ho. apply bv_eq. rewrite u_add64, !u_lit64. unfold two64.
  rewrite (Z.mod_small o) by lia. reflexivity.
Qed.

Section Memcpy.
  Variable ceil : Z.
  Variable o : Z.
  Hypothesis Ho : o = 56%Z \/ o = 88%Z.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp P w0 w1 w2 w3 : word).
  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 (bv_unsigned P + o).
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 (bv_unsigned P + 24).
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 32.
  Hypothesis Hal : (bv_unsigned P mod 64 = 0)%Z.
  Hypothesis HPr : (appm (bv_unsigned P) 976 /\ (0 < bv_unsigned P)%Z) /\ (bv_unsigned P + 976 <= ceil)%Z.
  Hypothesis Hdw : RiscvSemantics.store_ok SEGS mem (Z_to_bv 64 (bv_unsigned P + o)) 32 = true.
  Hypothesis Hshz : shz mem (bv_unsigned P) 122.
  Hypothesis C0 : rdn SEGS mem (Z_to_bv 64 (bv_unsigned P + 24)) 8 = Some (word_to_le_bytes 8 w0).
  Hypothesis C1 : rdn SEGS mem (Z_to_bv 64 (bv_unsigned P + 32)) 8 = Some (word_to_le_bytes 8 w1).
  Hypothesis C2 : rdn SEGS mem (Z_to_bv 64 (bv_unsigned P + 40)) 8 = Some (word_to_le_bytes 8 w2).
  Hypothesis C3 : rdn SEGS mem (Z_to_bv 64 (bv_unsigned P + 48)) 8 = Some (word_to_le_bytes 8 w3).
  Hypothesis C_14c010 : rdn SEGS mem (Z_to_bv 64 0x9f658) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xa7899)).
  Hypothesis C_154d21 : rdn SEGS mem (Z_to_bv 64 0xa7899) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 1)).
  Hypothesis C_14b308 : rdn SEGS mem (Z_to_bv 64 0x9eaf0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xa6bb8)).
  Hypothesis C_154040 : rdn SEGS mem (Z_to_bv 64 0xa6bb8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 SB)).
  Hypothesis C_14dd28 : rdn SEGS mem (Z_to_bv 64 0xa0948) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x97e1c)).
  Hypothesis R_sp : ((AS_STKLO <= ceil)%Z /\ (ceil + 2144 <= bv_unsigned sp)%Z) /\ (bv_unsigned sp <= 2 ^ 47)%Z.
  Hypothesis W_sp : RiscvSemantics.store_ok SEGS mem (Z_to_bv 64 (bv_unsigned sp - 2144)) 2144 = true.

  Let E : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ [P; w0; w1; w2; w3])) (blobs_ev []).
  Definition lit8 (a v : Z) : kentry := KWord (SA (ELit 0) a) 8 (ELit v).
  Definition kn0v1 : list kentry :=
    [lit8 0x9f658 0xa7899; KWord (SA (ELit 0) 0xa7899) 1 (ELit 1);
     lit8 0x9eaf0 0xa6bb8; lit8 0xa6bb8 SB; lit8 0xa0948 0x97e1c;
     KAlign (EVar 64) 64; KRange (EVar 64) 1 (2 ^ 47 - 976); KWr (SA (EVar 64) o) 32;
     KZero (SA (EAlu ALU_SRL (EVar 64) (ELit 3)) SB) (ELit 122);
     KWord (SA (EVar 64) 24) 8 (EVar 65); KWord (SA (EVar 64) 32) 8 (EVar 66);
     KWord (SA (EVar 64) 40) 8 (EVar 67); KWord (SA (EVar 64) 48) 8 (EVar 68);
     KRange (EVar 2) (AS_STKLO + 2144) (2 ^ 47); KWr (SA (EVar 2) (-2144)) 2144].

  Ltac klit := eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0));
      [ reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia
      | rewrite u_lit0; lia | rewrite u_lit0; lia | rewrite u_lit0, Z.add_0_l; eassumption ].
  Ltac kP := eapply (kword_intro SEGS E mem (EVar 64) P);
      [ cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | eassumption ].

  Lemma kn0v1_ok : know_ok SEGS E mem kn0v1.
  Proof using ceil o Ho FPI regs mem rom sp P w0 w1 w2 w3 Hsp Hal HPr Hdw Hshz C0 C1 C2 C3 C_14c010 C_154d21 C_14b308 C_154040 C_14dd28 R_sp W_sp.
    unfold kn0v1, lit8. pose proof (u64_range P). pose proof (u64_range sp).
    unfold know_ok.
    repeat lazymatch goal with |- Forall _ (_ :: _) => constructor | |- Forall _ [] => constructor end.
    all: lazymatch goal with |- Forall _ _ => fail | _ => idtac end.
    all: try klit.
    all: try kP.
    - apply kalign_intro; [lia|]. cbn [edenot]; ev_simpl E. exact Hal.
    - apply krange_intro. cbn [edenot]; ev_simpl E. lia.
    - apply (kwr_intro SEGS E mem (EVar 64) P o 32); [cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | exact Hdw].
    - eapply (kzero_shz_intro SEGS E mem (EVar 64) P 122); [cbn [edenot]; ev_simpl E; reflexivity | exact Hshz | lia | lia].
    - apply krange_intro. cbn [edenot]; ev_simpl E. rewrite Hsp. lia.
    - apply (kwr_intro SEGS E mem (EVar 2) sp (-2144) 2144); [cbn [edenot]; ev_simpl E; exact Hsp | lia | lia | lia | ].
      replace (bv_unsigned sp + -2144)%Z with (bv_unsigned sp - 2144)%Z by lia. exact W_sp.
  Qed.

  Definition kn0 : list kentry := kn0v1 ++
    [KDisj (SA (EVar 64) 0) 976 ZSH ZSHL; KDisj (SA (EVar 64) 0) 976 ZIMG ZIMGL;
     KDisj (SA (EVar 64) 0) 976 (SA (EVar 2) (-2144)) 2144].
  Lemma kn0_ok : know_ok SEGS E mem kn0.
  Proof using ceil o Ho FPI regs mem rom sp P w0 w1 w2 w3 Hsp Hal HPr Hdw Hshz C0 C1 C2 C3 C_14c010 C_154d21 C_14b308 C_154040 C_14dd28 R_sp W_sp. apply know_ok_app; [exact kn0v1_ok | kn_place]. Qed.

  Definition RS : list (saddr * Z) := [(SA (EVar 2) (-2144), 2144%Z); (SA (EVar 64) o, 32%Z)].
  Lemma RS_denot : regions_denot E RS = [(Z_to_bv 64 (bv_unsigned sp - 2144), 2144%Z); (Z_to_bv 64 (bv_unsigned P + o), 32%Z)].
  Proof using o FPI regs rom sp P w0 w1 w2 w3 Hsp.
    unfold regions_denot, RS. cbn [map fst snd]. unfold adenot. cbn [a_base a_off edenot]. ev_simpl E.
    rewrite Hsp. unfold v_addi.
    replace (bv_unsigned sp + -2144)%Z with (bv_unsigned sp - 2144)%Z by lia. reflexivity.
  Qed.

  Ltac useRD RD K :=
    let X := fresh "X" in
    pose proof (RD _ _ K ltac:(lia) ltac:(lia)) as X; cbn [edenot] in X; ev_simpl_in E X; rewrite wtlb4_ext0 in X;
    lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) 4 = _ =>
      lazymatch type of X with rdn _ _ (Z_to_bv 64 ?b) 4 = _ => replace a with b by lia; exact X end end.

  Theorem imemcpy_run_ok :
    exists (FPI' : FPState) regs' mem',
      msteps SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x51034) mem rom)
                  (mkst (FP:=FPI') regs' ret mem' rom)
      /\ regs_kept abi_kept regs regs'
      /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI'))
      /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 2144), 2144%Z); (Z_to_bv 64 (bv_unsigned P + o), 32%Z)]
      /\ rdn SEGS mem' (Z_to_bv 64 (bv_unsigned P + o)) 8 = Some (word_to_le_bytes 8 w0)
      /\ rdn SEGS mem' (Z_to_bv 64 (bv_unsigned P + o + 8)) 8 = Some (word_to_le_bytes 8 w1)
      /\ rdn SEGS mem' (Z_to_bv 64 (bv_unsigned P + o + 16)) 8 = Some (word_to_le_bytes 8 w2)
      /\ rdn SEGS mem' (Z_to_bv 64 (bv_unsigned P + o + 24)) 8 = Some (word_to_le_bytes 8 w3)
      /\ getr regs' 10 = Z_to_bv 64 (bv_unsigned P + o).
  Proof using ceil o Ho FPI regs mem rom ret sp P w0 w1 w2 w3 Hra Hret Hsp H10 H11 H12 Hal HPr Hdw Hshz C0 C1 C2 C3 C_14c010 C_154d21 C_14b308 C_154040 C_14dd28 R_sp W_sp.
    apply runs_to_contract with
      (P := fun FPI' regs' mem' => regs_kept abi_kept regs regs'
              /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI'))
              /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 2144), 2144%Z); (Z_to_bv 64 (bv_unsigned P + o), 32%Z)]
              /\ rdn SEGS mem' (Z_to_bv 64 (bv_unsigned P + o)) 8 = Some (word_to_le_bytes 8 w0)
              /\ rdn SEGS mem' (Z_to_bv 64 (bv_unsigned P + o + 8)) 8 = Some (word_to_le_bytes 8 w1)
              /\ rdn SEGS mem' (Z_to_bv 64 (bv_unsigned P + o + 16)) 8 = Some (word_to_le_bytes 8 w2)
              /\ rdn SEGS mem' (Z_to_bv 64 (bv_unsigned P + o + 24)) 8 = Some (word_to_le_bytes 8 w3)
              /\ getr regs' 10 = Z_to_bv 64 (bv_unsigned P + o)).
    assert (HR : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof (u64_range P). pose proof (u64_range sp).
    pin_reg HR (10%bv:reg) (EAlu ALU_ADD (EVar 64) (ELit o)) by (regv HR (10%bv:reg); cbn [edenot]; ev_simpl E; rewrite add_lit_word by lia; exact H10).
    pin_reg HR (11%bv:reg) (EAlu ALU_ADD (EVar 64) (ELit 24)) by (regv HR (11%bv:reg); cbn [edenot]; ev_simpl E; rewrite add_lit_word by lia; exact H11).
    pin_reg HR (12%bv:reg) (ELit 32) by (regv HR (12%bv:reg); exact H12).
    pose proof kn0_ok as HK. unfold kn0, kn0v1, lit8 in HK.
    assert (FIN : forall (oo : Z) (FPI' : FPState) (R : bvmap 5 word) (M : word -> option byte) sr' sfr' kn' (log : list sentry),
      oo = o ->
      regs_ok E sr' R -> fregs_ok E sfr' (fp_regs (FPState:=FPI')) -> know_ok SEGS E M kn' ->
      M = mem_denot E mem log -> log_flat E log ->
      forallb (fun r => expr_eqb (sr_get sr' r) (sr_get (sr_vars 0) r)) abi_kept = true ->
      forallb (fun r => expr_eqb (sfr_get sfr' r) (sfr_get (sfr_vars 32) r)) abi_fkept = true ->
      sr_get sr' 10 = EAlu ALU_ADD (EVar 64) (ELit oo) -> sr_get sr' 1 = EVar 1 ->
      log_in_regions log [(SA (EVar 2) (-2144), 2144%Z); (SA (EVar 64) oo, 32%Z)] = true ->
      kread SEGS kn' (EVar 64) oo 4 = Some (EExt false 0 4 (EExt true 0 4 (EVar 65))) -> kread SEGS kn' (EVar 64) (oo + 4) 4 = Some (EExt false 0 4 (EExt true 4 4 (EVar 65))) ->
      kread SEGS kn' (EVar 64) (oo + 8) 4 = Some (EExt false 0 4 (EExt true 0 4 (EVar 66))) -> kread SEGS kn' (EVar 64) (oo + 12) 4 = Some (EExt false 0 4 (EExt true 4 4 (EVar 66))) ->
      kread SEGS kn' (EVar 64) (oo + 16) 4 = Some (EExt false 0 4 (EExt true 0 4 (EVar 67))) -> kread SEGS kn' (EVar 64) (oo + 20) 4 = Some (EExt false 0 4 (EExt true 4 4 (EVar 67))) ->
      kread SEGS kn' (EVar 64) (oo + 24) 4 = Some (EExt false 0 4 (EExt true 0 4 (EVar 68))) -> kread SEGS kn' (EVar 64) (oo + 28) 4 = Some (EExt false 0 4 (EExt true 4 4 (EVar 68))) ->
      runs_to SEGS (mkst (FP:=FPI') R (Z_to_bv 64 0x5115c) M rom)
        (fun st' => exists (FPI'0 : FPState) regs' mem',
           st' = mkst (FP:=FPI'0) regs' ret mem' rom /\
           (regs_kept abi_kept regs regs' /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI'0))
            /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 2144), 2144%Z); (Z_to_bv 64 (bv_unsigned P + o), 32%Z)]
            /\ rdn SEGS mem' (Z_to_bv 64 (bv_unsigned P + o)) 8 = Some (word_to_le_bytes 8 w0)
            /\ rdn SEGS mem' (Z_to_bv 64 (bv_unsigned P + o + 8)) 8 = Some (word_to_le_bytes 8 w1)
            /\ rdn SEGS mem' (Z_to_bv 64 (bv_unsigned P + o + 16)) 8 = Some (word_to_le_bytes 8 w2)
            /\ rdn SEGS mem' (Z_to_bv 64 (bv_unsigned P + o + 24)) 8 = Some (word_to_le_bytes 8 w3)
            /\ getr regs' 10 = Z_to_bv 64 (bv_unsigned P + o)))).
    { intros oo FPI' R M sr' sfr' kn' log Eoo HR' HF' HK' EQM HLF Hk Hfk Hs10 Hs1 Hreg K0 K1 K2 K3 K4 K5 K6 K7. subst oo.
      assert (RD : forall k v, kread SEGS kn' (EVar 64) k 4 = Some v -> (0 <= k)%Z -> (k + 4 <= 976)%Z ->
                 rdn SEGS M (Z_to_bv 64 (bv_unsigned P + k)) 4 = Some (word_to_le_bytes 4 (edenot E v))).
      { intros k v Kk Kk0 Kk1.
        pose proof (kread_rdn SEGS E M kn' (EVar 64) k 4 v HK' Kk ltac:(lia) ltac:(lia)) as X.
        unfold adenot in X. cbn [a_base a_off edenot] in X. ev_simpl_in E X. unfold v_addi in X. apply X.
        unfold flat, estart, elenZ. cbn [a_base a_off edenot Z.of_nat]. ev_simpl E. lia. }
      fin_ret_with HR'.
      { rewrite (HR' 1%bv), Hs1. cbn [edenot]. ev_simpl E. rewrite Hra. exact Hret. }
      exists FPI', R, M. split.
      + rewrite (HR' 1%bv), Hs1. cbn [edenot]. ev_simpl E. rewrite Hra. reflexivity.
      + split; [exact (regs_same_on E _ _ regs R abi_kept HR0 HR' Hk)|].
        split; [exact (fregs_same_on E _ _ _ _ abi_fkept HF0 HF' Hfk)|].
        split; [|split; [|split; [|split; [|split]]]].
        * rewrite EQM, <- RS_denot. apply (frame_mod_mem_denot E _ _ RS); [exact HLF | | exact Hreg].
          unfold RS. constructor; [|constructor; [|constructor]]; cbn [fst snd]; unfold flat, estart; cbn [a_base a_off edenot]; ev_simpl E;
            rewrite ?Hsp; lia.
        * apply (cell64_halves M _ w0); [lia | lia | useRD RD K0 | useRD RD K1].
        * apply (cell64_halves M _ w1); [lia | lia | useRD RD K2 | useRD RD K3].
        * apply (cell64_halves M _ w2); [lia | lia | useRD RD K4 | useRD RD K5].
        * apply (cell64_halves M _ w3); [lia | lia | useRD RD K6 | useRD RD K7].
        * rewrite (HR' 10%bv), Hs10. cbn [edenot]. ev_simpl E. apply add_lit_word. lia. }
    destruct Ho as [Eo|Eo]; rewrite Eo in HR, HK; cbn [Z.add] in HK.
    - run_fp 400%nat [0x5115c%Z] noscr true.
      eapply (FIN 56%Z); [exact (eq_sym Eo) | exact HR | exact HF | exact HK | exact EQM | exact HLF | vm_compute; reflexivity | vm_compute; reflexivity
                          | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity .. ].
    - run_fp 400%nat [0x5115c%Z] noscr true.
      eapply (FIN 88%Z); [exact (eq_sym Eo) | exact HR | exact HF | exact HK | exact EQM | exact HLF | vm_compute; reflexivity | vm_compute; reflexivity
                          | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity .. ].
  Qed.
End Memcpy.

Theorem imemcpy32_asan : forall ceil, imemcpy32_contract SEGS as_asan ceil.
Proof.
  intros ceil o P w0 w1 w2 w3 Ho FPI regs mem rom ret Hra Hret PRE.
  destruct PRE as (H10 & H11 & H12 & Hal & Hheap & Hwr & Hshz & C0 & C1 & C2 & C3 & Henv & (sp & Hsp & Hfr)).
  destruct Henv as (C64 & C32 & C8 & R64).
  destruct Hfr as ([Hst1 Hst2] & Hsal & (_ & _ & _ & Hwsp)).
  destruct Hwr as (_ & _ & _ & Hdw).
  pose proof (C64 0x9f658%Z 0xa7899%Z ltac:(first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)])) as E0.
  pose proof (C8 0xa7899%Z 1%Z ltac:(first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)])) as E0b.
  pose proof (C64 0x9eaf0%Z 0xa6bb8%Z ltac:(first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)])) as E1.
  pose proof (C64 0xa6bb8%Z AS_SB ltac:(first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)])) as E2.
  pose proof (C64 0xa0948%Z 0x97e1c%Z ltac:(first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)])) as E8.
  unfold acell in E0, E0b, E1, E2, E8. unfold cell64, cell in C0, C1, C2, C3.
  unfold heapish, stackish, AS_SB, SB in *. app_facts.
  destruct (imemcpy_run_ok ceil o Ho FPI regs mem rom ret sp P w0 w1 w2 w3 Hra Hret Hsp H10 H11 H12 Hal ltac:(plc) Hdw Hshz C0 C1 C2 C3
             E0 E0b E1 E2 E8 ltac:(plc) Hwsp)
    as (FPI' & regs' & mem' & Hms & Hk1 & Hk2 & Hfm & G0 & G1 & G2 & G3 & Ha0).
  exists FPI', regs', mem'. split; [exact Hms|]. split; [exact Hk1|]. split; [exact Hk2|].
  unfold imemcpy32_post, cell64, cell. rewrite Hsp.
  split; [exact Hfm|]. split; [exact G0|]. split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. exact Ha0.
Qed.
