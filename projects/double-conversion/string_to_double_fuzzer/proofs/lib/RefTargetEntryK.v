(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec CatExec SeqExec StoreOk ShapeAlg Spec MallocDefs RefEnframeBase RefWorld RefTargetPre
  RefExitBase RefWorldK RefTargetPreK
  RefWorldK.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import SymExec3 SymExec3Sound SymRun3 SymDrive3 SymPlan SymSlots SymPlanSoundA RefTargetEntry RefTargetEntryK_defs.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast LiaTier.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast2.
Import ListNotations.
Import SX2. Import SX2S. Import SP. Import SSL. Import SPSA.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := ImgP.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPW_1. Context {fx : PropExec.FPState}.


Section EntryK.
  Variables (k sp0 gm area brkv mas tid sec : Z) (content : list byte) (R : bvmap 5 word) (M : word -> option byte).
  Variables (VM : VmMaps) (model : Model) (nlo nhi : Z).
  Hypothesis TP : target_pre_k k sp0 gm area brkv mas tid sec content R M.
  Hypothesis TV : target_vm_k k sp0 gm area VM.
  Hypothesis Mfds : m_fds model = fds_std.
  Hypothesis Mvm : m_vmmaps model = VM.
  Hypothesis Mhalt : m_halted model = None.
  Hypothesis Mlazy : m_vm_lazy model = [].
  Hypothesis Mmat : m_vm_materialized model = [].
  Hypothesis Hn : nlo <= hdr_paylen content <= nhi.
  Variable e : Z.
  Hypothesis He : 0 <= e < 2 ^ 32.
  Hypothesis Ce : cell M 0xc4874 4 e.
  Variable can : Z.                                   (* [comment removed for export] *)
  Hypothesis Hcan : 0 <= can < 2 ^ 64.
  Hypothesis Ccan : cell M 0xe4b88 8 can.

  Let E : env := E_T sp0 gm area tid content brkv mas e can sec R.
  Let L : Z := Z.of_nat (length content).

  (* [comment removed for export] *)
  #[using="Type"] Lemma EV0 : ev E 0 = Z_to_bv 64 sp0. Proof. reflexivity. Qed.
  #[using="Type"] Lemma EV1 : ev E 1 = Z_to_bv 64 gm. Proof. reflexivity. Qed.
  #[using="Type"] Lemma EV2 : ev E 2 = Z_to_bv 64 area. Proof. reflexivity. Qed.
  #[using="Type"] Lemma EV3 : ev E 3 = Z_to_bv 64 tid. Proof. reflexivity. Qed.
  #[using="Type"] Lemma EV4 : ev E 4 = Z_to_bv 64 (hdr_paylen content). Proof. reflexivity. Qed.
  #[using="Type"] Lemma EV5 : ev E 5 = Z_to_bv 64 (hdr_cfglen content). Proof. reflexivity. Qed.
  #[using="Type"] Lemma EV6 : ev E 6 = Z_to_bv 64 (hdr_b0 content). Proof. reflexivity. Qed.
  #[using="Type"] Lemma EV7 : ev E 7 = Z_to_bv 64 (hdr_b1 content). Proof. reflexivity. Qed.
  #[using="Type"] Lemma EV8 : ev E 8 = Z_to_bv 64 (bv_unsigned (nth 2 content (Z_to_bv 8 0))). Proof. reflexivity. Qed.
  #[using="Type"] Lemma EV9 : ev E 9 = Z_to_bv 64 brkv. Proof. reflexivity. Qed.
  #[using="Type"] Lemma EV10 : ev E 10 = Z_to_bv 64 mas. Proof. reflexivity. Qed.
  #[using="Type"] Lemma EV11 : ev E 11 = Z_to_bv 64 e. Proof. reflexivity. Qed.
  #[using="Type"] Lemma EV12 : ev E 12 = Z_to_bv 64 can. Proof. reflexivity. Qed.
  #[using="Type"] Lemma EV13 : ev E 13 = Z_to_bv 64 sec. Proof. reflexivity. Qed.
  #[using="L"] Lemma EVJ : forall i, (2 <= i < 32)%nat -> ev E (12 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold E, E_T. cbn [ev]. unfold vals_T. destruct i as [|[|i']]; [lia|lia|].
    change (12 + S (S i'))%nat with (length [Z_to_bv 64 sp0; Z_to_bv 64 gm; Z_to_bv 64 area; Z_to_bv 64 tid;
       Z_to_bv 64 (hdr_paylen content); Z_to_bv 64 (hdr_cfglen content); Z_to_bv 64 (hdr_b0 content);
       Z_to_bv 64 (hdr_b1 content); Z_to_bv 64 (bv_unsigned (nth 2 content (Z_to_bv 8 0)));
       Z_to_bv 64 brkv; Z_to_bv 64 mas; Z_to_bv 64 e; Z_to_bv 64 can; Z_to_bv 64 sec : word] + i')%nat.
    unfold vals_ev. rewrite app_nth2_plus.
    unfold junk_vals. change (seq 0 32) with (0%nat :: 1%nat :: seq 2 30). cbn [map skipn].
    rewrite (nth_map_seq_gen (fun i => getr R (Z_to_bv 5 (Z.of_nat i))) 30 2 i') by lia. reflexivity.
  Qed.
  #[using="Type"] Lemma EB0 : eb E 0 = content. Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="L"] Lemma b0_rng : 0 <= hdr_b0 content < 256. Proof. unfold hdr_b0. pose proof (bv_unsigned_in_range _ (nth 0 content (Z_to_bv 8 0))) as Hr. change (bv_modulus 8) with 256%Z in Hr. lia. Qed.
  #[using="L"] Lemma b1_rng : 0 <= hdr_b1 content < 256. Proof. unfold hdr_b1. pose proof (bv_unsigned_in_range _ (nth 1 content (Z_to_bv 8 0))) as Hr. change (bv_modulus 8) with 256%Z in Hr. lia. Qed.
  #[using="L"] Lemma b2_rng : 0 <= bv_unsigned (nth 2 content (Z_to_bv 8 0)) < 256. Proof. pose proof (bv_unsigned_in_range _ (nth 2 content (Z_to_bv 8 0))) as Hr. change (bv_modulus 8) with 256%Z in Hr. lia. Qed.
  #[using="L"] Lemma cfglen_rng : 0 <= hdr_cfglen content < 32768.
  Proof. unfold hdr_cfglen. apply Z.mod_pos_bound. lia. Qed.

  (* [comment removed for export] *)
  Ltac enorm :=
    cbn [edenot a_base a_off];
    rewrite ?alu_add, ?alu_sub, ?EV0, ?EV1, ?EV2, ?EV3, ?EV4, ?EV5, ?EV6, ?EV7, ?EV8, ?EV9, ?EV10, ?EV11, ?EV12, ?EV13;
    rewrite ?vadd_ZZ', ?vsub_ZZ'.
  Ltac anorm := unfold adenot, estart, elenZ; enorm; unfold slotC, slotF, offk, nbk, resk, Wk in *; rewrite ?v_addi_Z by lia; rewrite ?u_small by lia.

  Ltac klia := unfold slotC, slotF, offk, nbk, resk, Wk in *; lia.
  Ltac kimg Wimg := split; [lia|]; split; [lia|]; apply (img_clear_cover _ _ _ Wimg); vm_compute; reflexivity.
  Ltac karith := anorm; klia.
  Ltac kflat := apply flat_intro; unfold elenZ; enorm; rewrite ?u_small by klia; klia.
  Ltac kwr_stack Hst := split; [kflat|]; intros d m Hd Hm; unfold elenZ in Hm; cbn [edenot] in Hm; rewrite ?u_small in Hm by klia; anorm;
                    replace (sp0 + -8388608 + d) with (sp0 - 8388608 + d) by lia; apply Hst; lia.
  Ltac kwr_def Hdef := split; [kflat|]; intros d m Hd Hm; unfold elenZ in Hm; cbn [edenot] in Hm; rewrite ?u_small in Hm by klia; anorm; rewrite ?Z.add_0_r;
                    lazymatch goal with |- store_ok _ _ (Z_to_bv 64 ?a) _ = true =>
                      lazymatch type of Hdef with (forall i, _ -> ?MM (Z_to_bv 64 (?base + i)) <> None) =>
                        replace a with (base + (a - base)) by klia end end;
                    apply (store_ok_of_defined _ _ _ Hdef); klia.
  Ltac kwr_data := split; [kflat|]; intros d m Hd Hm; unfold elenZ in Hm; cbn [edenot] in Hm; rewrite ?u_small in Hm by klia; anorm; apply store_ok_data; rewrite u_small by lia; lia.
  (* [comment removed for export] *)
  Ltac kwordC C := split; [cbn; lia|]; split; [kflat|]; anorm; unfold cell in C;
                    lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
                      lazymatch type of C with rdn _ _ (Z_to_bv 64 ?a') _ = _ => replace a' with a in C by klia end end;
                    first [ exact C | rewrite C; apply f_equal; apply f_equal; apply f_equal; klia ].
  Ltac kword_abs aexp C := split; [cbn; lia|]; split; [kflat|]; anorm;
                    lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => change (Z_to_bv 64 a) with (Z_to_bv 64 aexp : word) end;
                    first [ exact C | unfold cell in C; rewrite C; first [ reflexivity | apply f_equal; apply f_equal; apply f_equal; klia ] ].
  Ltac kword_rel aexp C := kwordC C.
  Ltac kbyte_rel aexp C := split; [cbn; lia|]; split; [kflat|]; anorm;
                    lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
                      lazymatch type of C with _ (Z_to_bv 64 ?a') = Some _ => replace a' with a in C by klia end end;
                    rewrite (rdn1_of_mem _ _ _ C); rewrite w2b1 by lia; reflexivity.
  Ltac kzero aexp C := split; [kflat|]; intros i Hi; revert i Hi; anorm; intros i Hi; unfold zero_bytes in C;
                    lazymatch goal with |- _ (Z_to_bv 64 ?a) = _ =>
                      lazymatch type of C with (forall j, _ -> _ (Z_to_bv 64 (?base + j)) = _) =>
                        replace a with (base + (a - base)) by klia end end;
                    apply C; klia.
  Ltac kblob HTC Hdef := split; [kflat|]; split; [rewrite EB0; anorm; klia|];
                intros i Hi; revert i Hi; anorm; rewrite EB0; intros i Hi;
                lazymatch type of HTC with rdn _ _ (Z_to_bv 64 ?buf) _ = _ =>
                  lazymatch goal with |- _ (Z_to_bv 64 ?a) = _ => replace a with (buf + i) by klia end;
                  apply (rdn_defined_nth _ buf (length content) content HTC); try klia;
                  intros j Hj;
                  lazymatch type of Hdef with (forall i, _ -> ?MM (Z_to_bv 64 (?base + i)) <> None) =>
                    replace (buf + j) with (base + (buf + j - base)) by klia end;
                  apply Hdef; klia end.

  #[using="VM TP TV Mfds Mvm Mhalt Mlazy Mmat Hn He Ce Hcan Ccan L"] Theorem target_entry_k_ok_e :
    cs_ok E (cs_Tk k nlo nhi) R M model.
  Proof.
    pose proof TP as TP'.
    destruct TP' as [tp_ra tp_sp tp_gp tp_tp tp_a0 tp_a1 tp_a2 tp_a3 tp_s0 tp_s1 tp_s2 tp_s3 tp_s4 tp_s5 tp_s6 tp_s7
                     tp_sp0 tp_len tk_L tk_stack TF TW tk_content].
    pose proof TW as TW'. destruct TW'.
    lazymatch goal with H : enframe_post _ _ _ _ _ _ |- _ => pose proof H as EP0; destruct H end.
    lazymatch goal with x := gm + 16 + 16 * (k + 1) |- _ => subst x end.
    lazymatch goal with x := gm + 16 + (nbk k - 16) - 4 |- _ => subst x end.
    lazymatch goal with x := nbk k - 16 - 4 - capk k - 16 * (k + 1) |- _ => subst x end.
    lazymatch goal with x := (nbk k - 16) * 0 / 16 + (k + 1) |- _ => subst x end.
    destruct TF as [mf_ra mf_s0 mf_s1 mf_s2 mf_s3 mf_s4 mf_s5 mf_s6 mf_s7].
    pose proof b0_rng as Hb0. pose proof b1_rng as Hb1. pose proof b2_rng as Hb2. pose proof cfglen_rng as Hcl.
    assert (HL : hdr_paylen content + hdr_cfglen content + 6 = L) by (unfold hdr_paylen; subst L; lia).
    pose proof (capk_pos k ltac:(lia)) as Hck. pose proof (capk_le k ltac:(lia)) as Hck2.
    pose proof (capk_pos (k - 1) ltac:(lia)) as Hck1.
    assert (Hm2 : 0 <= k mod 2 <= 1) by (pose proof (Z.mod_pos_bound k 2 ltac:(lia)); lia).
    (* [comment removed for export] *)
    replace (gm + 16 + 16 * (k + 1) - 4) with (gm + (offk k - 4)) in Pm4 by (unfold offk; lia).
    replace (gm + 16 + 16 * (k + 1) - 3) with (gm + (offk k - 3)) in Pm3 by (unfold offk; lia).
    replace (gm + 16 + 16 * (k + 1) - 2) with (gm + (offk k - 2)) in Pm2 by (unfold offk; lia).
    replace (gm + 16 + 16 * (k + 1) + capk k) with (gm + (offk k + capk k)) in Pzr by (unfold offk; lia).
    replace (gm + 16 + (nbk k - 16) - 4 - 5) with (gm + (nbk k - 9)) in Pe5 by lia.
    replace (gm + 16 + (nbk k - 16) - 4 - 4) with (gm + (nbk k - 8)) in Pe4 by lia.
    replace (gm + 16 - 3) with (gm + 13) in Ps3 by lia.
    replace (gm + 16 - 2) with (gm + 14) in Ps2 by lia.
    replace (nbk k - 16 - 4 - capk k - 16 * (k + 1)) with (resk k) in Pm3, Pzr, Pe5, Pe4, Pr by (unfold resk, nbk; lia).
    replace ((nbk k - 16) * 0 / 16 + (k + 1)) with (k + 1) in Pm2, Pr by (rewrite Z.mul_0_r; reflexivity).
    assert (Hres : 5 <= resk k) by (unfold resk; lia).
    replace (0 + 32 * res_code (resk k)) with 160 in Pm3
      by (unfold res_code; destruct (Z.ltb_spec0 (resk k) 5); lia).
    specialize (Pzr ltac:(lia)). specialize (Pe5 ltac:(lia)). specialize (Pe4 ltac:(lia)).
    specialize (Ps3 ltac:(lia)). specialize (Ps2 ltac:(lia)).
    unfold slotC, slotF, offk, nbk, resk, Wk in *.
    constructor.
    - (* [comment removed for export] *)
      intros r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
      { assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. reflexivity. }
      pose proof (ridx_range r) as Hri. rewrite <- (ridx_roundtrip r) at 1.
      cbn [c_ss cs_Tk s_regs].
      generalize (ridx r) Hri. clear r Hr0 Hri. intros i Hi.
      destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
        [ .. | lia]; rewrite <- nth_all_regs by lia; cbn [nth sr_Tk all_regs];
        lazymatch goal with |- _ = edenot _ (EVar ?n) =>
                  change (edenot E (EVar n)) with (ev E n);
                  first [ rewrite (EVJ (n - 12)) by lia; reflexivity
                        | rewrite ?EV4, ?EV5; first [exact tp_a1 | exact tp_a3 | exact tp_s2 | exact tp_s4 | idtac] ]
              | |- _ => idtac end;
        try (enorm; first [ reflexivity | exact tp_ra | exact tp_gp | exact tp_tp | exact tp_s6 | exact tp_s7
                          | rewrite tp_sp; f_equal; klia
                          | rewrite tp_a0; f_equal; klia | rewrite tp_s1; f_equal; klia
                          | rewrite tp_s0; f_equal; klia | rewrite tp_s3; f_equal; klia
                          | rewrite tp_s6; f_equal; klia
                          | rewrite tp_a2; f_equal; klia ]).
      (* [comment removed for export] *)
      rewrite tp_s5. cbn [edenot]. rewrite EV7. unfold ext_val, ext_Z. rewrite u_small by lia.
      change (2 ^ (8 * Z.of_nat 0)) with 1. change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite Z.div_1_r, (Z.mod_small _ 256) by lia.
      apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold bv_swrap, bv_wrap.
      change (bv_half_modulus (8 * N.of_nat 1)) with 128. change (bv_modulus (8 * N.of_nat 1)) with 256.
      destruct (Z.ltb_spec0 (hdr_b1 content) 128).
      + rewrite (Z.mod_small (_ + 128) 256) by lia. f_equal. lia.
      + replace ((hdr_b1 content + 128) mod 256) with (hdr_b1 content + 128 - 256) by
          (apply Z.mod_unique with (q := 1); lia).
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        apply Z.mod_unique with (q := -1); [lia|]. rewrite Z.mod_small by lia. lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    - (* [comment removed for export] *)
      cbn [c_ss cs_Tk s_know]. unfold kn_Tk, kn_Tk0, know_ok.
      repeat (apply Forall_cons; [|try apply Forall_nil]).
      all: cbn [kentry_ok].
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *)
        anorm. pose proof (Z.le_min_l 32767 (capk k - 7 - nlo)). pose proof (Z.le_min_r 32767 (capk k - 7 - nlo)).
        pose proof (Z.min_spec 32767 (capk k - 7 - nlo)). lia.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) kwr_stack tk_stack.
      + (* [comment removed for export] *) kword_rel (sp0 - 56) mf_ra.
      + (* [comment removed for export] *) kword_rel (sp0 - 64) mf_s0.
      + (* [comment removed for export] *) kword_rel (sp0 - 72) mf_s1.
      + (* [comment removed for export] *) kword_rel (sp0 - 80) mf_s2.
      + (* [comment removed for export] *) kword_rel (sp0 - 88) mf_s3.
      + (* [comment removed for export] *) kword_rel (sp0 - 96) mf_s4.
      + (* [comment removed for export] *) kword_rel (sp0 - 104) mf_s5.
      + (* [comment removed for export] *) kword_rel (sp0 - 112) mf_s6.
      + (* [comment removed for export] *) kword_rel (sp0 - 120) mf_s7.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) kwr_def wk_grp_def.
      + (* [comment removed for export] *) kwr_def wk_area_def.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) kword_rel area wk_area_chk.
      + (* [comment removed for export] *) kword_rel (area + 8) wk_area_next.
      + (* [comment removed for export] *) kword_rel (area + 16) wk_area_ns.
      + (* [comment removed for export] *) kword_rel (slotC k area) wk_cur_prev.
      + (* [comment removed for export] *) kword_rel (slotC k area + 8) wk_cur_next.
      + (* [comment removed for export] *) kword_rel (slotC k area + 16) wk_cur_mem.
      + (* [comment removed for export] *) kword_rel (slotC k area + 24) wk_cur_avail.
      + (* [comment removed for export] *) kword_rel (slotC k area + 28) wk_cur_freed.
      + (* [comment removed for export] *) kword_rel (slotC k area + 32) wk_cur_W.
      + (* [comment removed for export] *) kword_rel (slotF k area) wk_free_prev.
      + (* [comment removed for export] *) kword_rel (slotF k area + 8) wk_free_next.
      + (* [comment removed for export] *) kword_rel (slotF k area + 16) wk_free_mem.
      + (* [comment removed for export] *) kword_rel (slotF k area + 24) wk_free_msk.
      + (* [comment removed for export] *) kword_rel (slotF k area + 32) wk_free_W.
      + (* [comment removed for export] *) kzero (area + 104) wk_area_rest.
      + (* [comment removed for export] *) kword_rel gm wk_grp_meta.
      + (* [comment removed for export] *) kword_rel (gm + 8) wk_grp_aidx.
      + (* [comment removed for export] *) kzero (gm + 9) wk_grp_pad.
      + (* [comment removed for export] *) kbyte_rel (gm + 13) Ps3.
      + (* [comment removed for export] *) kword_rel (gm + 14) Ps2.
      + (* [comment removed for export] *) kbyte_rel (gm + (offk k - 4)) Pm4.
      + (* [comment removed for export] *) kbyte_rel (gm + (offk k - 3)) Pm3.
      + (* [comment removed for export] *) kword_rel (gm + (offk k - 2)) Pm2.
      + (* [comment removed for export] *) kbyte_rel (gm + (offk k + capk k)) Pzr.
      + (* [comment removed for export] *) kbyte_rel (gm + (nbk k - 9)) Pe5.
      + (* [comment removed for export] *) kword_rel (gm + (nbk k - 8)) Pe4.
      + (* [comment removed for export] *) kzero (gm + nbk k - 4) wk_grp_tail.
      + (* [comment removed for export] *) kblob tk_content wk_grp_def.
      + (* [comment removed for export] *) kwr_data.
      + (* [comment removed for export] *) kwr_data.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kword_abs (804944) wk_self.
      + (* [comment removed for export] *) kword_abs (804976) wk_tid.
      + (* [comment removed for export] *) kword_abs (804980) Ce.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kword_abs (936840) Ccan.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kword_abs (936920) wk_pagesz.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kword_abs (ctx_secret) wk_secret.
      + (* [comment removed for export] *) kword_abs (ctx_init_done) wk_init.
      + (* [comment removed for export] *) kword_abs (ctx_mmap_counter) wk_ctr.
      + (* [comment removed for export] *) kword_abs (ctx_free_meta_head) wk_fmh.
      + (* [comment removed for export] *) kword_abs (ctx_avail_meta) wk_am.
      + (* [comment removed for export] *) kword_abs (ctx_avail_meta_count) wk_amc.
      + (* [comment removed for export] *) kword_abs (ctx_avail_meta_area_count) wk_amac.
      + (* [comment removed for export] *) kword_abs (ctx_meta_alloc_shift) wk_mas.
      + (* [comment removed for export] *) kword_abs (ctx_meta_area_head) wk_mah.
      + (* [comment removed for export] *) kword_abs (ctx_meta_area_tail) wk_mat.
      + (* [comment removed for export] *) kword_abs (ctx_avail_meta_areas) wk_amas.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kword_abs (ctx_active 44) wk_active44.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kword_abs (ctx_usage 44) wk_usage44.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kword_abs (ctx_seq) wk_seq.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kword_abs (ctx_brk) wk_brk.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
    - (* [comment removed for export] *) reflexivity.
    - (* [comment removed for export] *) exact Mhalt.
    - (* [comment removed for export] *) exact Mlazy.
    - (* [comment removed for export] *) exact Mmat.
    - (* [comment removed for export] *) exact Mfds.
    - (* [comment removed for export] *)
      rewrite Mvm.
      destruct TV as [Vres Visp Vtop Vlim Vhas Varea Vlen Vsmall Vseps Vlive].
      pose proof (capk_pos k ltac:(lia)) as Hck'. pose proof (capk_le k ltac:(lia)) as Hck2'.
      constructor; cbn [c_maps c_nmaps c_live cs_Tk].
      + exact Vres.
      + unfold maps_Tk. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold smap_ok; cbn [sm_base sm_len sm_exact edenot];
          rewrite ?EV1, ?EV2; rewrite ?u_small by klia.
        * split; [unfold nbk; lia|]. split; [unfold nbk in *; lia|]. exact Vhas.
        * split; [lia|]. split; [lia|]. exact Varea.
      + lia.
      + unfold vm_live_bytes. pose proof Vlive. lia.
      + eapply Forall_impl; [|exact Vsmall]. intros p [H1 H2]. lia.
      + eapply Forall_impl; [|exact Vsmall]. intros p [H1 H2]. lia.
      + apply seps_conv. exact Vseps.
      + exact Vlim.
      + (* [comment removed for export] *) rewrite Visp. symmetry. exact EV0.
      + (* [comment removed for export] *) rewrite Visp, u_small by lia. unfold sp_window_lo, sp_window_hi. lia.
      + (* [comment removed for export] *) rewrite Visp, u_small by lia. change SP.STKWIN with 8388608. exact Vtop.
    - (* [comment removed for export] *)
      cbn [c_slots cs_Tk]. unfold slots_Tk, slots_ok. apply Forall_cons; [|apply Forall_nil].
      unfold slot_ok. cbn [sl_start sl_stride sl_n sl_off sl_W sl_idx sl_p split_lit is_lit]. unfold uE. enorm.
      unfold Wk, offk in *. unfold nbk in *. unfold capk in *.
      rewrite !u_small by lia.
      split; [exact EP0 | ].
      assert (HWf : w_maplen (65536 * 2 ^ k + 4096 + 4064) = 16 * 2 ^ k + 1 /\ w_lastidx (65536 * 2 ^ k + 4096 + 4064) = 0
                    /\ w_sizeclass (65536 * 2 ^ k + 4096 + 4064) = 63).
      { unfold w_maplen, w_lastidx, w_sizeclass.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        (* [comment removed for export] *)
        repeat split; (clear - Hck Hck2 wk_k; first [lia | nia]).
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
      destruct HWf as (Hml & Hli & Hscl).
      rewrite Hml, Hli, Hscl. unfold slot_stride. cbn [negb Z.eqb andb].
      replace (16 * 2 ^ k + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb andb]. unfold UNIT.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      repeat split; (clear - Hck Hck2 wk_B_al wk_B_rng wk_sp0 wk_k; first [lia | nia]).   (* [comment removed for export] *)
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    - 
      assert (Hc : img_clear M 0xc2ee9 0xc4848).
      { pose proof wk_img as Hi. unfold img_clear_ivs in Hi.
        repeat (apply Forall_cons_iff in Hi as [?Hx Hi]); cbn [fst snd] in *; assumption. }
      unfold lib_ok, LibIface.lib_statics. split.
      + left. intros a Hin. pose proof (LIBR_in_hull a Hin) as Hh.
        change HULL_LO with 0xc2f20 in Hh. change HULL_HI with 0xc4008 in Hh. apply Hc. lia.
      + intros a Ha _. cbn [fst snd LibIface.LIBR_HULL_P] in Ha. apply Hc. lia.
  Qed.
End EntryK.

#[using="Type"] Theorem target_entry_k_ok :
  forall (k sp0 B area brkv mas tid sec : Z) (content : list byte) (R : bvmap 5 word) (M : word -> option byte)
         (VM : VmMaps) (model : Model) (nlo nhi : Z),
    target_pre_k k sp0 B area brkv mas tid sec content R M ->
    target_vm_k k sp0 B area VM ->
    m_fds model = fds_std -> m_vmmaps model = VM -> m_halted model = None ->
    m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    nlo <= hdr_paylen content <= nhi ->
    exists e can, 0 <= e < 2 ^ 32 /\ 0 <= can < 2 ^ 64 /\
      cs_ok (E_T sp0 B area tid content brkv mas e can sec R) (cs_Tk k nlo nhi) R M model.
Proof.
  intros k sp0 B area brkv mas tid sec content R M VM model nlo nhi TP TV Mf Mv Mh Ml Mm Hn.
  destruct (wk_errno _ _ _ _ _ _ _ _ _ (tk_world _ _ _ _ _ _ _ _ _ _ _ TP)) as (e & He & Ce).
  destruct (wk_canary _ _ _ _ _ _ _ _ _ (tk_world _ _ _ _ _ _ _ _ _ _ _ TP)) as (can & Hcan & Ccan).
  exists e, can. split; [exact He|]. split; [exact Hcan|].
  apply (target_entry_k_ok_e k sp0 B area brkv mas tid sec content R M VM model nlo nhi TP TV Mf Mv Mh Ml Mm Hn e He Ce can Hcan Ccan).
Qed.
End FPW_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
