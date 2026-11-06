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
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs BoBase AsRtSpec AsLibTagsLib AsLibPlace.
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

#[local] Abbreviation SEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Lemma rdn_zero8 : forall mem (a : word),
  (bv_unsigned a + 8 <= 2 ^ 64)%Z ->
  (forall i, (0 <= i < 8)%Z -> mem (Z_to_bv 64 (bv_unsigned a + i)) = Some (Z_to_bv 8 0)) ->
  exists bs, rdn SEGS mem a 8 = Some bs /\ Z_to_bv 64 (extz false 8 (bytes_le_to_Z bs)) = Z_to_bv 64 0.
Proof.
  intros mem a Hnw Hz. exists (repeat (Z_to_bv 8 0) 8). split; [|reflexivity].
  apply rdn_pointwise; [reflexivity | cbn [Z.of_nat]; lia |].
  intros j Hj. rewrite Hz by lia.
  destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; try reflexivity. lia.
Qed.

(* [comment removed for export] *)
Lemma u_quick_addr : forall (d : word) (k : Z),
  (0 <= k)%Z -> (bv_unsigned d + k < 2 ^ 47)%Z ->
  bv_unsigned (alu64 ALU_AND (alu64 ALU_ADD (alu64 ALU_SRL (alu64 ALU_ADD d (Z_to_bv 64 k)) (Z_to_bv 64 3)) (Z_to_bv 64 SB)) (Z_to_bv 64 (-8)))
  = (8 * ((SB + (bv_unsigned d + k) / 8) / 8))%Z.
Proof.
  intros d k Hk Hb. pose proof (u64_range d).
  rewrite u_and64, u_add64, u_srl3, u_add64, !u_lit64. unfold two64, SB.
  rewrite (Z.mod_small k) by lia. rewrite (Z.mod_small (bv_unsigned d + k)) by lia.
  rewrite (Z.mod_small 2147450880) by lia.
  rewrite (Z.mod_small ((bv_unsigned d + k) / 8 + 2147450880)) by lia.
  change ((-8) mod 2 ^ 64)%Z with (2 ^ 64 - 2 ^ 3)%Z.
  rewrite land_highmask by lia. lia.
Qed.

Lemma u_quick_addr0 : forall (d : word),
  (bv_unsigned d < 2 ^ 47)%Z ->
  bv_unsigned (alu64 ALU_AND (alu64 ALU_ADD (alu64 ALU_SRL d (Z_to_bv 64 3)) (Z_to_bv 64 SB)) (Z_to_bv 64 (-8)))
  = (8 * ((SB + bv_unsigned d / 8) / 8))%Z.
Proof.
  intros d Hb. pose proof (u64_range d).
  rewrite u_and64, u_add64, u_srl3, !u_lit64. unfold two64, SB.
  rewrite (Z.mod_small 2147450880) by lia.
  rewrite (Z.mod_small (bv_unsigned d / 8 + 2147450880)) by lia.
  change ((-8) mod 2 ^ 64)%Z with (2 ^ 64 - 2 ^ 3)%Z.
  rewrite land_highmask by lia. lia.
Qed.

Section Memset.
  Variable ceil : Z.
  Variables (n al fd : Z).
  Hypothesis Hn : n = 976%Z /\ al = 64%Z /\ fd = 2208%Z \/ n = 20%Z /\ al = 4%Z /\ fd = 2128%Z.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp d mid : word).
  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis Hd : getr regs 10 = d.
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 0.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 n.
  Hypothesis Hal : (bv_unsigned d mod al = 0)%Z.
  Hypothesis Hdr : (appm (bv_unsigned d) n /\ (0 < bv_unsigned d)%Z) /\ (bv_unsigned d + n <= ceil)%Z.
  Hypothesis Hdw : RiscvSemantics.store_ok SEGS mem (Z_to_bv 64 (bv_unsigned d)) (Z.to_nat n) = true.
  Hypothesis Hshz : n = 976%Z -> shz mem (bv_unsigned d) 122.
  Hypothesis Hshw : n = 20%Z -> shwz mem (bv_unsigned d) 20.
  Hypothesis C_14c010 : rdn SEGS mem (Z_to_bv 64 0xa0488) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xa8699)).
  Hypothesis C_154d21 : rdn SEGS mem (Z_to_bv 64 0xa8699) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 1)).
  Hypothesis C_14b308 : rdn SEGS mem (Z_to_bv 64 0x9f920) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xa79b8)).
  Hypothesis C_154040 : rdn SEGS mem (Z_to_bv 64 0xa79b8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 SB)).
  Hypothesis C_14b310 : rdn SEGS mem (Z_to_bv 64 0x9f928) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xa86a8)).
  Hypothesis C_154d30 : rdn SEGS mem (Z_to_bv 64 0xa86a8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Hypothesis C_14b318 : rdn SEGS mem (Z_to_bv 64 0x9f930) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xa86b0)).
  Hypothesis C_154d38 : rdn SEGS mem (Z_to_bv 64 0xa86b0) 8 = Some (word_to_le_bytes 8 mid).
  Hypothesis C_14b320 : rdn SEGS mem (Z_to_bv 64 0x9f938) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xa86a0)).
  Hypothesis C_154d28 : rdn SEGS mem (Z_to_bv 64 0xa86a0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff)).
  Hypothesis C_14dd30 : rdn SEGS mem (Z_to_bv 64 0xa1780) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x99050)).
  Hypothesis R_sp : ((AS_STKLO <= ceil)%Z /\ (ceil + fd <= bv_unsigned sp)%Z) /\ (bv_unsigned sp <= 2 ^ 47)%Z.
  Hypothesis W_sp : RiscvSemantics.store_ok SEGS mem (Z_to_bv 64 (bv_unsigned sp - fd)) (Z.to_nat fd) = true.

  Let E : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ [mid])) (blobs_ev []).
  Definition lit8 (a v : Z) : kentry := KWord (SA (ELit 0) a) 8 (ELit v).
  Definition kn0v1 : list kentry :=
    [lit8 0xa0488 0xa8699; KWord (SA (ELit 0) 0xa8699) 1 (ELit 1);
     lit8 0x9f920 0xa79b8; lit8 0xa79b8 SB; lit8 0x9f928 0xa86a8; lit8 0xa86a8 0; lit8 0x9f930 0xa86b0;
     KWord (SA (ELit 0) 0xa86b0) 8 (EVar 64); lit8 0x9f938 0xa86a0; lit8 0xa86a0 0x7fffffffffff; lit8 0xa1780 0x99050;
     KAlign (EVar 10) al; KRange (EVar 10) 1 (2 ^ 47 - n); KWr (SA (EVar 10) 0) n;
     KRange (EVar 2) (AS_STKLO + fd) (2 ^ 47); KWr (SA (EVar 2) (- fd)) fd]
    ++ (if Z.eqb n 976 then [KZero (SA (EAlu ALU_SRL (EVar 10) (ELit 3)) SB) (ELit 122)] else []).

  Ltac klit := eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0));
      [ reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia
      | rewrite u_lit0; lia | rewrite u_lit0; lia | rewrite u_lit0, Z.add_0_l; eassumption ].

  Lemma kn0v1_ok : know_ok SEGS E mem kn0v1.
  Proof using ceil n al fd Hn FPI regs mem rom sp d mid Hsp Hd Hal Hdr Hdw Hshz C_14c010 C_154d21 C_14b308 C_154040 C_14b310 C_154d30 C_14b318 C_154d38 C_14b320 C_154d28 C_14dd30 R_sp W_sp.
    unfold kn0v1, lit8. pose proof (u64_range d). pose proof (u64_range sp).
    apply know_ok_app.
    - unfold know_ok.
      repeat lazymatch goal with |- Forall _ (_ :: _) => constructor | |- Forall _ [] => constructor end.
      all: lazymatch goal with |- Forall _ _ => fail | _ => idtac end.
      all: try klit.
      + apply kalign_intro; [lia|]. cbn [edenot]; ev_simpl E. rewrite Hd. exact Hal.
      + apply krange_intro. cbn [edenot]; ev_simpl E. rewrite Hd. lia.
      + apply (kwr_intro SEGS E mem (EVar 10) d 0 n); [cbn [edenot]; ev_simpl E; exact Hd | lia | lia | lia | rewrite Z.add_0_r; exact Hdw].
      + apply krange_intro. cbn [edenot]; ev_simpl E. rewrite Hsp. lia.
      + apply (kwr_intro SEGS E mem (EVar 2) sp (- fd) fd); [cbn [edenot]; ev_simpl E; exact Hsp | lia | lia | lia | ].
        replace (bv_unsigned sp + - fd)%Z with (bv_unsigned sp - fd)%Z by lia. exact W_sp.
    - destruct (Z.eqb_spec n 976) as [En|En]; [|constructor].
      constructor; [|constructor].
      eapply (kzero_shz_intro SEGS E mem (EVar 10) d 122); [cbn [edenot]; ev_simpl E; exact Hd | exact (Hshz En) | lia | lia].
  Qed.

  Definition kn0 : list kentry := kn0v1 ++
    [KDisj (SA (EVar 10) 0) n ZSH ZSHL; KDisj (SA (EVar 10) 0) n ZIMG ZIMGL; KDisj (SA (EVar 10) 0) n (SA (EVar 2) (- fd)) fd].
  Lemma kn0_ok : know_ok SEGS E mem kn0.
  Proof using ceil n al fd Hn FPI regs mem rom sp d mid Hsp Hd Hal Hdr Hdw Hshz C_14c010 C_154d21 C_14b308 C_154040 C_14b310 C_154d30 C_14b318 C_154d38 C_14b320 C_154d28 C_14dd30 R_sp W_sp. apply know_ok_app; [exact kn0v1_ok | kn_place]. Qed.

  Definition RS : list (saddr * Z) := [(SA (EVar 2) (- fd), fd); (SA (EVar 10) 0, n)].
  Lemma RS_denot : regions_denot E RS = [(Z_to_bv 64 (bv_unsigned sp - fd), fd); (d, n)].
  Proof using n al fd FPI regs rom sp d mid Hsp Hd.
    unfold regions_denot, RS. cbn [map fst snd]. unfold adenot. cbn [a_base a_off edenot]. ev_simpl E.
    rewrite Hsp, Hd, v_addi_0. unfold v_addi.
    replace (bv_unsigned sp + - fd)%Z with (bv_unsigned sp - fd)%Z by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma FIN : forall (nn : nat) (FPI' : FPState) (R : bvmap 5 word) (log : list sentry) sr' sfr' kn',
      Z.of_nat nn = n ->
      regs_ok E sr' R -> fregs_ok E sfr' (fp_regs (FPState:=FPI')) ->
      know_ok SEGS E (mem_denot E mem log) kn' ->
      log_flat E log ->
      forallb (fun r => expr_eqb (sr_get sr' r) (sr_get (sr_vars 0) r)) abi_kept = true ->
      forallb (fun r => expr_eqb (sfr_get sfr' r) (sfr_get (sfr_vars 32) r)) abi_fkept = true ->
      sr_get sr' 10 = EVar 10 -> sr_get sr' 1 = EVar 1 ->
      log_in_regions log RS = true ->
      lz_cover log (EVar 10) 0 nn = true ->
      runs_to SEGS (mkst (FP:=FPI') R (Z_to_bv 64 0x515bc) (mem_denot E mem log) rom)
        (fun st' => exists (FPI'0 : FPState) regs' mem',
           st' = mkst (FP:=FPI'0) regs' ret mem' rom /\
           (regs_kept abi_kept regs regs' /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI'0)) /\
            frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - fd), fd); (d, n)] /\
            (forall i, (0 <= i < n)%Z -> mem' (Z_to_bv 64 (bv_unsigned d + i)) = Some (Z_to_bv 8 0)) /\
            getr regs' 10 = d)).
  Proof using ceil n al fd Hn FPI regs mem rom ret sp d mid Hra Hret Hsp Hd Hal Hdr R_sp.
    intros nn FPI' R log sr' sfr' kn' Hnn HR HF HK HLF Hk Hfk H10 H1 Hreg Hcov.
    assert (HR0 : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [])).
    assert (HF0 : fregs_ok E (sfr_vars 32) (fp_regs (FPState:=FPI))) by exact (fregs_ok_vars (junk_vals regs) (fp_regs (FPState:=FPI)) _ (blobs_ev [])).
    pose proof (u64_range d). pose proof (u64_range sp).
    fin_ret_with HR.
    { rewrite (HR 1%bv), H1. cbn [edenot]. ev_simpl E. rewrite Hra. exact Hret. }
    exists FPI', R, (mem_denot E mem log). split.
    + rewrite (HR 1%bv), H1. cbn [edenot]. ev_simpl E. rewrite Hra. reflexivity.
    + split; [exact (regs_same_on E _ _ regs R abi_kept HR0 HR Hk)|].
      split; [exact (fregs_same_on E _ _ _ _ abi_fkept HF0 HF Hfk)|].
      split; [|split].
      * rewrite <- RS_denot. apply (frame_mod_mem_denot E _ _ RS); [exact HLF | | exact Hreg].
        unfold RS. constructor; [|constructor; [|constructor]]; cbn [fst snd]; unfold flat, estart; cbn [a_base a_off edenot]; ev_simpl E;
          rewrite ?Hsp, ?Hd; lia.
      * intros i Hi. rewrite <- Hd.
        change (getr regs 10) with (edenot E (EVar 10)).
        apply (mem_denot_lz_cover E mem log (EVar 10) 0 nn HLF Hcov); cbn [edenot]; ev_simpl E; rewrite ?Hd; lia.
      * rewrite (HR 10%bv), H10. cbn [edenot]. ev_simpl E. exact Hd.
  Qed.

  Theorem imemset_run_ok :
    exists (FPI' : FPState) regs' mem',
      msteps SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x514fc) mem rom)
                  (mkst (FP:=FPI') regs' ret mem' rom)
      /\ regs_kept abi_kept regs regs'
      /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI'))
      /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - fd), fd); (d, n)]
      /\ (forall i, (0 <= i < n)%Z -> mem' (Z_to_bv 64 (bv_unsigned d + i)) = Some (Z_to_bv 8 0))
      /\ getr regs' 10 = d.
  Proof using ceil n al fd Hn FPI regs mem rom ret sp d mid Hra Hret Hsp Hd H11 H12 Hal Hdr Hdw Hshz Hshw C_14c010 C_154d21 C_14b308 C_154040 C_14b310 C_154d30 C_14b318 C_154d38 C_14b320 C_154d28 C_14dd30 R_sp W_sp.
    apply runs_to_contract with
      (P := fun FPI' regs' mem' => regs_kept abi_kept regs regs'
              /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI'))
              /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - fd), fd); (d, n)]
              /\ (forall i, (0 <= i < n)%Z -> mem' (Z_to_bv 64 (bv_unsigned d + i)) = Some (Z_to_bv 8 0))
              /\ getr regs' 10 = d).
    assert (HR : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [])).
    pin_reg HR (11%bv:reg) (ELit 0) by (regv HR (11%bv:reg); exact H11).
    pin_reg HR (12%bv:reg) (ELit n) by (regv HR (12%bv:reg); exact H12).
    pose proof kn0_ok as HK. unfold kn0, kn0v1, lit8 in HK. pose proof (u64_range d). pose proof (u64_range sp).
    destruct Hn as [(En & Eal & Efd) | (En & Eal & Efd)]; rewrite En in HR; rewrite En, Eal, Efd in HK; cbn [Z.eqb Pos.eqb app Z.opp Z.sub Z.add] in HK.
    - (* [comment removed for export] *)
      destruct (app_sh_lit _ _ (proj1 (proj1 Hdr))) as [HZ|HZ];
        [ eassert (HK' : know_ok SEGS E _ (KRange (EVar 10) 1 (0x7fff7000 - 976) :: _))
            by (constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite Hd; lia | exact HK])
        | eassert (HK' : know_ok SEGS E _ (KRange (EVar 10) 0x10007fff8000 (2 ^ 47 - 2208 - 976) :: _))
            by (constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite Hd; lia | exact HK]) ];
        clear HK; rename HK' into HK;
      run_fp 1200%nat [0x515bc%Z] noscr true; subst M;
      (eapply (FIN 976%nat); [rewrite En; reflexivity | exact HR | exact HF | exact HK | exact HLF | vm_compute; reflexivity | vm_compute; reflexivity
                            | reflexivity | reflexivity | unfold RS; rewrite En, Efd; vm_compute; reflexivity | vm_compute; reflexivity ]).
    - (* [comment removed for export] *)
      pose proof (Hshw En) as SW. unfold shwz, AS_SB in SW. pose proof Hdr as Hdr20. rewrite En in Hdr20.
      run_fp 400%nat [0x515bc%Z] (SCR [] [ELit 0; ELit 0] []) true.
      all: try subst M.
      + rewrite v_addi_0.
        match goal with |- exists bs, rdn _ _ ?a 8 = Some bs /\ _ => rewrite <- (Z_to_bv_bv_unsigned 64 a) end.
        rewrite u_quick_addr by lia. unfold SB.
        apply rdn_zero8; rewrite u_small by lia; [lia|]. intros i Hi. apply SW. lia.
      + rewrite v_addi_0.
        match goal with |- exists bs, rdn _ _ ?a 8 = Some bs /\ _ => rewrite <- (Z_to_bv_bv_unsigned 64 a) end.
        rewrite u_quick_addr0 by lia. unfold SB.
        apply rdn_zero8; rewrite u_small by lia; [lia|]. intros i Hi. apply SW. lia.
      + eapply (FIN 20%nat); [rewrite En; reflexivity | exact HR | exact HF | exact HK | exact HLF | vm_compute; reflexivity | vm_compute; reflexivity
                            | reflexivity | reflexivity | unfold RS; rewrite En, Efd; vm_compute; reflexivity | vm_compute; reflexivity ].
  Qed.
End Memset.

Lemma areadable8_word' : forall segs mem a,
  areadable segs mem a 8 -> exists w : word, rdn segs mem (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 w).
Proof.
  intros segs mem a [bs Hbs]. exists (Z_to_bv 64 (bytes_le_to_Z bs)).
  rewrite word_to_le_bytes_of_lez; [exact Hbs | exact (rdn_length _ _ _ _ _ Hbs) | lia].
Qed.

Section Pack.
  Variable ceil : Z.
  Variables (n al fd : Z).
  Hypothesis Hn : n = 976%Z /\ al = 64%Z /\ fd = 2208%Z \/ n = 20%Z /\ al = 4%Z /\ fd = 2128%Z.

  Lemma imemset_both : forall d, fn_contract SEGS (al_imemset as_both) (imemset_pre SEGS as_both ceil n al fd d) (imemset_post n fd d).
  Proof using ceil n al fd Hn.
    intros d FPI regs mem rom ret Hra Hret PRE.
    destruct PRE as (Hd & H11 & H12 & Hal & Hheap & Hwr & Hsh & Henv & (sp & Hsp & Hfr)).
    destruct Henv as (C64 & C32 & C8 & R64).
    destruct Hfr as ([Hst1 Hst2] & Hsal & (_ & _ & _ & Hwsp)).
    destruct Hwr as (_ & _ & _ & Hdw).
    destruct (areadable8_word' SEGS mem 0xa86b0 (R64 _ ltac:(first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)]))) as [mid Hmid].
    pose proof (C64 0xa0488%Z 0xa8699%Z ltac:(first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)])) as E0.
    pose proof (C8 0xa8699%Z 1%Z ltac:(first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)])) as E0b.
    pose proof (C64 0x9f920%Z 0xa79b8%Z ltac:(first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)])) as E1.
    pose proof (C64 0xa79b8%Z AS_SB ltac:(first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)])) as E2.
    pose proof (C64 0x9f928%Z 0xa86a8%Z ltac:(first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)])) as E3.
    pose proof (C64 0xa86a8%Z 0%Z ltac:(first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)])) as E4.
    pose proof (C64 0x9f930%Z 0xa86b0%Z ltac:(first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)])) as E5.
    pose proof (C64 0x9f938%Z 0xa86a0%Z ltac:(first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)])) as E6.
    pose proof (C64 0xa86a0%Z 0x7fffffffffff%Z ltac:(first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)])) as E7.
    pose proof (C64 0xa1780%Z 0x99050%Z ltac:(first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)])) as E8.
    unfold acell in E0, E0b, E1, E2, E3, E4, E5, E6, E7, E8.
    unfold heapish, stackish, AS_SB, SB in *. app_facts.
    assert (Hshz : n = 976%Z -> shz mem (bv_unsigned d) 122) by (intros En; rewrite En in Hsh; exact Hsh).
    assert (Hshw : n = 20%Z -> shwz mem (bv_unsigned d) 20) by (intros En; rewrite En in Hsh; exact Hsh).
    destruct (imemset_run_ok ceil n al fd Hn FPI regs mem rom ret sp d mid Hra Hret Hsp Hd H11 H12 Hal ltac:(plc) Hdw Hshz Hshw
               E0 E0b E1 E2 E3 E4 E5 Hmid E6 E7 E8 ltac:(plc) Hwsp)
      as (FPI' & regs' & mem' & Hms & Hk1 & Hk2 & Hfm & Hz & Ha0).
    exists FPI', regs', mem'. split; [exact Hms|]. split; [exact Hk1|]. split; [exact Hk2|].
    unfold imemset_post. rewrite Hsp. split; [exact Hfm | split; [exact Hz | exact Ha0]].
  Qed.
End Pack.

Theorem imemset976_both : forall ceil, imemset976_contract SEGS as_both ceil.
Proof. intros ceil. exact (imemset_both ceil 976 64 2208 (or_introl (conj eq_refl (conj eq_refl eq_refl)))). Qed.

Theorem imemset20_both : forall ceil, imemset20_contract SEGS as_both ceil.
Proof. intros ceil. exact (imemset_both ceil 20 4 2128 (or_intror (conj eq_refl (conj eq_refl eq_refl)))). Qed.
