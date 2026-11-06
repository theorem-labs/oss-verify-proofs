(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_beast.http_request.images Require Import Ubsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare Frame AgentLib SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 Spec LibTail RefMemcpyLib.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import RefExitBase LibDiagKn RefPrintfBufBase RefMemcpyBase RefMemcpy RefOpenFailCS_defs RefOpenFailCS_tail.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import RefUsageCS_defs RefUsageCS_tail.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section UsageCS.
  Variable sp0 : word.                 (* [comment removed for export] *)
  Variable model : Model.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  (* [comment removed for export] *)
  Lemma umemcpy1_denot : forall vals M, vals_ev vals 0 = sp0 ->
    mem_denot (ENV vals) M u_logM1 = wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 560)) PRE7.
  Proof.
    intros vals M P0. pose proof SPlo. pose proof SPhi.
    rewrite <- PRE7_word. cbn [mem_denot u_logM1].
    unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0.
    f_equal; f_equal; lia.
  Qed.

  (* [comment removed for export] *)
  Theorem us_tail_cs : forall (a0s : list byte) (pp : word) (t8 : list byte) vals R M,
    ~ In (Z_to_bv 8 0) a0s -> (Z.of_nat (length a0s) <= 131071)%Z ->
    length vals = 38%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 1 = pp ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z ->
    (bv_unsigned pp + Z.of_nat (length a0s) + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    (bv_unsigned pp + Z.of_nat (length a0s) + 8 <= 0x800000000000)%Z ->
    regs_ok (ENV vals) srUS0 R -> know_ok RSEGS (ENV vals) M knUS0 ->
    rdn RSEGS M pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + Z.of_nat (length a0s))) 8 = Some t8 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2bc84) M (seg_rom RSEGS)) model)
               (t_die (msg_usage a0s) (m_fs model)).
  Proof.
    intros a0s pp t8 vals R M Hnonul HL0 HL P0 P1 Hpp1 Hpp2 Hpp3 HR HK Sr Ht8.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
    (* [comment removed for export] *)
    run_blk_keep u_scrA 38%nat.
    assert (Habove : forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M0 x = M x).
    { intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) M _ 0%nat 0xb8000);
        [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia]. }
    clear EQM. rename M0 into M1. rename M into M0. rename M1 into M.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
    assert (Hsrc : rdn RSEGS M (Z_to_bv 64 0x11914) 7 = Some PRE7).
    { rewrite (kimg_rdn RSEGS (ENV vals) _ u_knA ltac:(let i := kidx u_knA (is_kimg_cov 0x11914 7) in exact i)
                 _ _ 0x11914 7 HK eq_refl) by (cbn; lia). apply pre7_img. }
    assert (Hdst : store_ok RSEGS M dst 7 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ u_knA ltac:(let i := kidx u_knA (is_kwr_cov (EVar 0) (-560) 7) in exact i)
                    _ _ _ (-560) 7 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
    assert (MC : mcH M dst (Z_to_bv 64 0x11914) 7 PRE7).
    { constructor; subst dst; rewrite ?u_small by lia; rewrite ?PRE7_len; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x6f13c : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x11914) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 7) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M dst (Z_to_bv 64 0x11914) 7 _ (seg_rom RSEGS) MC Rc (0x6f13c : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 496976) with (0x79550 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x6f13c : word) with (Z_to_bv 64 0x6f13c) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev []) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    assert (HK2 : know_ok RSEGS (ENV vals) (wbytes M dst PRE7) u_knB0).
    { subst dst. rewrite <- (umemcpy1_denot vals M P0).
      eapply (carry_after RSEGS (ENV vals) M u_logM1 u_knA [] u_knB0 [] []);
        [vm_compute; reflexivity | | exact HK | constructor].
      cbn [log_flat u_logM1]. split; [lia|]. split; [|exact I].
      apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev []) (wbytes M dst PRE7) u_knB0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 70%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q1 : vals_ev vals1 1 = pp) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev [])) with (ENV vals1) in HR, HK.
    eapply (us_tail sp0 model Hvsp Hh Hlazy Hfd2 a0s pp t8 vals1); try eassumption.
    - rewrite rdn_wbytes_out; [ | | |]; subst dst; rewrite ?PRE7_len; unorm; try lia.
      rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - rewrite rdn_wbytes_out; [ | | |]; subst dst; rewrite ?PRE7_len; unorm; try lia.
      rewrite <- Ht8. apply rdn_agree. intros j Hj. apply Habove. unorm. lia.
  
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Variables (pp : word) (tid can : Z) (s0v : word) (R : bvmap 5 word) (M : word -> option byte).
  (* [comment removed for export] *)
  Hypothesis Rsp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128).
  Hypothesis Rtp : getr R 4 = Z_to_bv 64 0x96970.
  Hypothesis Rs0 : getr R 8 = Z_to_bv 64 2.
  Hypothesis Ra1 : getr R 11 = Z_to_bv 64 (bv_unsigned sp0 + 8).
  (* [comment removed for export] *)
  Hypothesis Mstack : stk_ok RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 48)) US_STK.
  (* [comment removed for export] *)
  Hypothesis Mro : forall i, (0x10000 <= i < 0x7e000)%Z -> M (Z_to_bv 64 i) = None.
  (* [comment removed for export] *)
  Hypothesis Mcells : cells_ok M diag_cells.
  (* [comment removed for export] *)
  Hypothesis Mtid : rdn RSEGS M (Z_to_bv 64 0x968c8) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)).
  Hypothesis Htid : (0 < tid < 2 ^ 22)%Z.
  (* [comment removed for export] *)
  Hypothesis Mcan : canary_ok M can.
  (* [comment removed for export] *)
  Hypothesis Margv : rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 + 8)) 8 = Some (word_to_le_bytes 8 pp).
  Hypothesis Hpp1 : (bv_unsigned sp0 <= bv_unsigned pp)%Z.
  (* [comment removed for export] *)
  Hypothesis Mra : rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6b4a4)).
  Hypothesis Ms0 : rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 64)) 8 = Some (word_to_le_bytes 8 s0v).
  Hypothesis Ms1 : rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 72)) 8 = Some (word_to_le_bytes 8 (getr R 9)).
  Hypothesis Ms2 : rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 80)) 8 = Some (word_to_le_bytes 8 (getr R 18)).
  Hypothesis Ms3 : rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 88)) 8 = Some (word_to_le_bytes 8 (getr R 19)).
  Hypothesis Ms4 : rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 96)) 8 = Some (word_to_le_bytes 8 (getr R 20)).
  Hypothesis Ms5 : rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 104)) 8 = Some (word_to_le_bytes 8 (getr R 21)).
  Hypothesis Ms6 : rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 112)) 8 = Some (word_to_le_bytes 8 (getr R 22)).
  Hypothesis Ms7 : rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 120)) 8 = Some (word_to_le_bytes 8 (getr R 23)).

  Definition valsUS : list word :=
    [sp0; pp; Z_to_bv 64 can; s0v; Z_to_bv 64 0; Z_to_bv 64 tid] ++ junk_vals R.
  Let E : env := ENV valsUS.

  Lemma valsUS_len : length valsUS = 38%nat.
  Proof. unfold valsUS. rewrite !length_app, junk_vals_length. reflexivity. Qed.

  Lemma evUS_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold E, ENV. cbn [ev]. unfold valsUS.
    change (6 + i)%nat with (length [sp0; pp; Z_to_bv 64 can; s0v; Z_to_bv 64 0; Z_to_bv 64 tid] + i)%nat.
    unfold vals_ev. rewrite app_nth2_plus.
    unfold junk_vals. rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.

  Lemma spxUS_val : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
  Proof. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev E 0) with sp0.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

  Ltac reg_caseUS :=
    cbn [nth srUS0 allregs32];
    first [ rewrite spxUS_val
          | lazymatch goal with |- _ = edenot _ (EVar ?n) =>
              change (edenot E (EVar n)) with (ev E n);
              first [ rewrite (evUS_junk (n - 6)) by lia; reflexivity | idtac ]
            | |- _ => cbn [edenot] end ];
    first [ reflexivity
          | exact Rtp | exact Rs0 | exact Ra1
          | rewrite Rsp; f_equal; lia
          | idtac ].

  Lemma regs_okUS : regs_ok E srUS0 R.
  Proof.
    pose proof SPlo. pose proof SPhi.
    apply regs_ok_by_idx.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_caseUS.
  
  Qed.

  (* [comment removed for export] *)
  Ltac kslot HYP :=
    eapply (kword_intro RSEGS E M (EVar 0) sp0);
      [ reflexivity | | lia | lia | lia | lia | exact HYP ].

  Lemma know_okUS : (bv_unsigned pp + 8 <= bv_unsigned sp0 + 4194304)%Z -> know_ok RSEGS E M knUS0.
  Proof.
    intros Hpp2. pose proof SPlo. pose proof SPhi. pose proof SPal. pose proof (u64_range pp).
    unfold knUS0. apply know_ok_app; [|apply know_ok_app; [apply diag_cells_know; exact Mcells|]].
    - repeat (apply Forall_cons); [ .. | apply Forall_nil ].
      + apply kalign_intro; [lia|]. change (edenot E (EVar 0)) with sp0. exact SPal.
      + apply krange_intro. change (edenot E (EVar 0)) with sp0. lia.
      + (* [comment removed for export] *) cbn [kentry_ok]. split; [apply flat_intro; cbn; unfold US_STK; lia|].
        intros d m Hd Hm. unfold estart. cbn [a_base a_off]. change (edenot E (EVar 0)) with sp0.
        pose proof (Mstack (Z_to_bv 64 (bv_unsigned sp0 + (-48 - US_STK) + d)) m) as Hs.
        rewrite !u_small in Hs by (unfold US_STK in *; lia). apply Hs; unfold US_STK in *; lia.
      + (* [comment removed for export] *) kslot Margv. cbn [edenot]. reflexivity.
      + apply krange_intro. change (edenot E (EVar 1)) with pp. lia.
      + kslot Mra. cbn [edenot]. reflexivity.
      + kslot Ms0. cbn [edenot]. reflexivity.
      + kslot Ms1. change (edenot E (EVar 15)) with (ev E (6 + 9)). rewrite evUS_junk by lia. reflexivity.
      + kslot Ms2. change (edenot E (EVar 24)) with (ev E (6 + 18)). rewrite evUS_junk by lia. reflexivity.
      + kslot Ms3. change (edenot E (EVar 25)) with (ev E (6 + 19)). rewrite evUS_junk by lia. reflexivity.
      + kslot Ms4. change (edenot E (EVar 26)) with (ev E (6 + 20)). rewrite evUS_junk by lia. reflexivity.
      + kslot Ms5. change (edenot E (EVar 27)) with (ev E (6 + 21)). rewrite evUS_junk by lia. reflexivity.
      + kslot Ms6. change (edenot E (EVar 28)) with (ev E (6 + 22)). rewrite evUS_junk by lia. reflexivity.
      + kslot Ms7. change (edenot E (EVar 29)) with (ev E (6 + 23)). rewrite evUS_junk by lia. reflexivity.
      + (* [comment removed for export] *) cbn [kentry_ok]. split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|].
        intros d m Hd Hm. unfold estart. cbn [a_base a_off edenot]. rewrite (u_small 0) by lia.
        apply store_ok_data; rewrite u_small by lia; lia.
      + apply kimg_intro; [lia|lia|exact Mro].
      + eapply (kword_intro RSEGS E M (ELit 0) (Z_to_bv 64 0) 0x968c8 4 (EVar 5) (Z_to_bv 64 tid));
          [reflexivity | reflexivity | lia | lia | rewrite (u_small 0) by lia; lia | rewrite (u_small 0) by lia; lia |].
        rewrite (u_small 0) by lia. exact Mtid.
      + apply (canary_know E M 2 can); [reflexivity | exact Mcan].
    - apply Forall_cons; [|apply Forall_nil].
      apply krange_intro. change (edenot E (EVar 5)) with (Z_to_bv 64 tid : word). rewrite u_small by lia. lia.
  
  Qed.

  (* [comment removed for export] *)
  Theorem ref_usage_cs : forall (a0s : list byte) (t8 : list byte),
    ~ In (Z_to_bv 8 0) a0s -> (Z.of_nat (length a0s) <= 131071)%Z ->
    (bv_unsigned pp + Z.of_nat (length a0s) + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    (bv_unsigned pp + Z.of_nat (length a0s) + 8 <= 0x800000000000)%Z ->
    rdn RSEGS M pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + Z.of_nat (length a0s))) 8 = Some t8 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2bc84) M (seg_rom RSEGS)) model)
               (t_die (msg_usage a0s) (m_fs model)).
  Proof.
    intros a0s t8 Hnonul HPl Hpp2 Hpp3 Hstr Ht8.
    eapply (us_tail_cs a0s pp t8 valsUS R M); try eassumption.
    - apply valsUS_len.
    - reflexivity.
    - reflexivity.
    - apply regs_okUS.
    - apply know_okUS. lia.
  Qed.
End UsageCS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
