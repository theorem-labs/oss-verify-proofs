(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Import Ubsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import SymExecFP SymExecFPSound SymRunFP SymDriveFP SymCallFP LibDefs LibTagsSpec LibBswap LibTagsLib.
Unset Nia Cache.  (* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SXF. Import SXFS.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].

#[local] Abbreviation SEGS := Ubsan.M.loaded_segments.

Lemma regs_kept_trans_u : forall l r1 r2 r3, regs_kept l r1 r2 -> regs_kept l r2 r3 -> regs_kept l r1 r3.
Proof. intros l r1 r2 r3 A B r Hr. rewrite (B r Hr). apply A. exact Hr. Qed.
Lemma fregs_kept_trans_u : forall l r1 r2 r3, fregs_kept l r1 r2 -> fregs_kept l r2 r3 -> fregs_kept l r1 r3.
Proof. intros l r1 r2 r3 A B r Hr. rewrite (B r Hr). apply A. exact Hr. Qed.

Section GT.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret P T data : word) (tc psz sig len : Z) (bs : list byte).

  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis HP : getr regs 10 = P.
  Hypothesis Hsg : getr regs 11 = Z_to_bv 64 sig.
  Hypothesis HT12 : getr regs 12 = T.
  Hypothesis Hsig : (0 <= sig < 2 ^ 32)%Z.
  (* [comment removed for export] *)
  Hypothesis Hlen : (0 <= len < 2 ^ 26)%Z.
  Hypothesis Hbs : Z.of_nat (length bs) = len.
  Hypothesis Hdnz : (0 < bv_unsigned data)%Z.
  Hypothesis Hdata : (bv_unsigned data + len < 2 ^ 47)%Z.
  Hypothesis Hblob : forall k, (0 <= k < len)%Z ->
      mem (Z_to_bv 64 (bv_unsigned data + k)) = Some (nth (Z.to_nat k) bs (Z_to_bv 8 0)).
  (* [comment removed for export] *)
  Hypothesis HPd : rdn SEGS mem (Z_to_bv 64 (bv_unsigned P + 0)) 8 = Some (word_to_le_bytes 8 data).
  Hypothesis HPtc : rdn SEGS mem (Z_to_bv 64 (bv_unsigned P + 20)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tc)).
  Hypothesis Htc : (0 <= tc < 2 ^ 32)%Z.
  Hypothesis Htags : (0 <= tc)%Z /\ (132 + 12 * tc <= psz <= len)%Z /\
     forall j, (0 <= j < tc)%Z ->
       let off := be32 bs (132 + 12 * j + 4) in let s := be32 bs (132 + 12 * j + 8) in
       (4 <= s)%Z /\ (off + s <= psz)%Z.
  Hypothesis Hp0 : (0 < bv_unsigned P)%Z.
  Hypothesis Hp24 : (bv_unsigned P + 24 <= 2 ^ 64)%Z.
  Hypothesis Hpal : (bv_unsigned P mod 8 = 0)%Z.
  Hypothesis Ht0 : (0 < bv_unsigned T)%Z.
  Hypothesis Htal : (bv_unsigned T mod 8 = 0)%Z.
  Hypothesis HTst : store_ok SEGS mem (Z_to_bv 64 (bv_unsigned T)) (Z.to_nat 24) = true.
  Hypothesis HT24 : (bv_unsigned T + 24 <= 2 ^ 64)%Z.
  Hypothesis HTD : (bv_unsigned data + len <= bv_unsigned T \/ bv_unsigned T + 24 <= bv_unsigned data)%Z.
  Hypothesis HPT : (bv_unsigned P + 24 <= bv_unsigned T \/ bv_unsigned T + 24 <= bv_unsigned P)%Z.

  Definition POST (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
    frame_mod mem mem' [(T, 24%Z)] /\
    exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1)%Z /\
      (r = 1%Z ->
         tag_ok SEGS mem' data len (bv_unsigned T) /\ cell32 SEGS mem' (bv_unsigned T) sig /\
         (exists ty, cell32 SEGS mem' (bv_unsigned T + 4) ty)).

  Definition Q (st' : machine_state) : Prop :=
    exists (FPI' : FPState) regs' mem',
      st' = mkst (FP:=FPI') regs' ret mem' rom /\
      regs_kept abi_kept regs regs' /\
      fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI')) /\
      POST regs' mem'.

  Definition INV (i : Z) (FPc : FPState) (R : bvmap 5 word) : Prop :=
    (0 <= i < tc)%Z /\
    (bv_unsigned (getr R 10) = 12 * i)%Z /\
    (bv_unsigned (getr R 15) = 12 * tc)%Z /\
    (bv_unsigned (getr R 13) = bv_unsigned data + 132)%Z /\
    (bv_unsigned (getr R 16) = 2 ^ 64 - 133 - bv_unsigned data)%Z /\
    getr R 11 = Z_to_bv 64 sig /\ getr R 12 = T /\ getr R 14 = data /\ getr R 1 = ret /\
    regs_kept abi_kept regs R /\
    fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPc)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Body.
    Variables (i : Z) (FPc : FPState) (R : bvmap 5 word).
    Hypothesis Hi : (0 <= i < tc)%Z.
    Hypothesis H10 : (bv_unsigned (getr R 10) = 12 * i)%Z.
    Hypothesis H15 : (bv_unsigned (getr R 15) = 12 * tc)%Z.
    Hypothesis H13 : (bv_unsigned (getr R 13) = bv_unsigned data + 132)%Z.
    Hypothesis H16 : (bv_unsigned (getr R 16) = 2 ^ 64 - 133 - bv_unsigned data)%Z.
    Hypothesis H11 : getr R 11 = Z_to_bv 64 sig.
    Hypothesis H12 : getr R 12 = T.
    Hypothesis H14 : getr R 14 = data.
    Hypothesis H1 : getr R 1 = ret.
    Hypothesis HRK : regs_kept abi_kept regs R.
    Hypothesis HFK : fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPc)).
    Hypothesis IH : forall (FPc' : FPState) (R' : bvmap 5 word),
        INV (i + 1) FPc' R' -> runs_to SEGS (mkst (FP:=FPc') R' (Z_to_bv 64 0x13aa8) mem rom) Q.

    #[local] Abbreviation off_i := (be32 bs (132 + 12 * i + 4)).
    #[local] Abbreviation s_i := (be32 bs (132 + 12 * i + 8)).

    Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPc))
                                  ++ [Z_to_bv 64 len; Z_to_bv 64 off_i; Z_to_bv 64 s_i])) (blobs_ev [bs]).

    Definition kn1 : list kentry :=
      [KRange (EVar 14) 1 (2^47);
       KRange (EVar 10) 0 (2^26);
       KRange (EVar 15) 0 (2^30);
       KRange (EVar 13) 133 (2^47 + 132);
       KRange (EVar 16) (2^63) (2^64 - 1);
       KRange (EVar 11) 0 (2^32 - 1);
       KRange (EVar 65) 0 (2^32 - 1);
       KRange (EVar 66) 0 (2^32 - 1);
       KAlign (EVar 12) 8;
       KWr (SA (EVar 12) 0) 24;
       KDisj (SA (EVar 12) 0) 24 (SA (EAlu ALU_ADD (EVar 10) (EVar 13)) 0) 12;
       KDisj (SA (EVar 12) 0) 24 (SA (EAlu ALU_ADD (EVar 10) (EVar 14)) 132) 12;
       KDisj (SA (EVar 12) 0) 24 (SA (EAlu ALU_ADD (EVar 14) (EVar 65)) 0) 4;
       KBlobD (SA (EVar 14) 0) (EVar 64) 0].

    Lemma kblob_ok : kentry_ok SEGS E mem (KBlobD (SA (EVar 14) 0) (EVar 64) 0).
    Proof using FPc H14 Hblob Hbs Hdata Hdnz Hi Hlen Hp0 Hsig Ht0 Htc.
      pose proof (u64_range data).
      cbn [kentry_ok]. unfold flat, estart, elenZ. cbn. rewrite H14, u_small by lia.
      split; [lia|]. split; [exact Hbs|]. intros k Hk. rewrite Z.add_0_r. apply Hblob. exact Hk.
    Qed.

    Lemma kn1_ok : know_ok SEGS E mem kn1.
    Proof using FPc H10 H11 H12 H13 H14 H15 H16 HT24 HTD HTst Hblob Hbs Hdata Hdnz Hi Hlen Hp0 Hsig Ht0 Htags Htal Htc.
      unfold kn1. pose proof (u64_range data). pose proof (u64_range T).
      destruct Htags as (Htc0 & Hpsz & Hall). destruct (Hall i Hi) as [Hs4 Hend].
      pose proof (be32_range bs (132 + 12 * i + 4)) as Ro. pose proof (be32_range bs (132 + 12 * i + 8)) as Rs.
      unfold know_ok.
      repeat (apply Forall_cons); [..|apply Forall_nil].
      - apply krange_intro; cbn. rewrite H14. lia.
      - apply krange_intro; cbn. rewrite H10. lia.
      - apply krange_intro; cbn. rewrite H15. lia.
      - apply krange_intro; cbn. rewrite H13. lia.
      - apply krange_intro; cbn. rewrite H16. lia.
      - apply krange_intro; cbn. rewrite H11, u_small by lia. lia.
      - apply krange_intro; cbn. rewrite u_small by lia. lia.
      - apply krange_intro; cbn. rewrite u_small by lia. lia.
      - apply kalign_intro; [lia|]. cbn. rewrite H12. exact Htal.
      - apply (kwr_intro SEGS E mem (EVar 12) T 0 24); cbn; try lia. exact H12. rewrite Z.add_0_r. exact HTst.
      - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite H12, alu_add. unfold v_add. rewrite u_small by lia. lia.
      - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite H12, H14, alu_add. unfold v_add. rewrite u_small by lia. lia.
      - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite H12, H14, alu_add. unfold v_add.
        rewrite (u_small off_i) by lia. rewrite u_small by lia. lia.
      - apply kblob_ok.
    Qed.

    (* [comment removed for export] *)
    Definition nu (j : nat) : Z :=
      nth j [bs_byte bs (132 + 12 * i); bs_byte bs (132 + 12 * i + 1); bs_byte bs (132 + 12 * i + 2); bs_byte bs (132 + 12 * i + 3);
             bs_byte bs (132 + 12 * i + 4); bs_byte bs (132 + 12 * i + 4 + 1); bs_byte bs (132 + 12 * i + 4 + 2); bs_byte bs (132 + 12 * i + 4 + 3);
             bs_byte bs (132 + 12 * i + 8); bs_byte bs (132 + 12 * i + 8 + 1); bs_byte bs (132 + 12 * i + 8 + 2); bs_byte bs (132 + 12 * i + 8 + 3)]%Z 0%Z.
    Definition atom (sx : bool) (d : Z) : expr * (bool * nat) :=
      (EBlobX sx 0 (EAlu ALU_ADD (EVar 10) (EVar 14)) d (EVar 14) 1, (sx, Z.to_nat (d - 132))).
    Definition atoms : list (expr * (bool * nat)) :=
      [atom true 143; atom false 140; atom false 141; atom false 142;
       atom false 137; atom false 138; atom false 136; atom true 139].

    Lemma nu_range : forall k, (0 <= nu k < 256)%Z.
    Proof using . intros k. unfold nu. do 12 (destruct k as [|k]; [cbn [nth]; apply bs_byte_range|]). destruct k; cbn; lia. Qed.

    Lemma atoms_ok_i : atoms_ok E nu atoms.
    Proof using FPc H10 H14 H16 Hbs Hdata Hdnz Hi Hlen Hp0 Hpal Hsig Ht0 Htags Htal Htc.
      destruct Htags as (Htc0 & Hpsz & Hall).
      unfold atoms, atoms_ok. pose proof (u64_range data).
      repeat (apply Forall_cons); [..|apply Forall_nil];
        unfold atom, atom_ok; cbn [edenot eb ev E blobs_ev nth]; ev_simpl E; rewrite H14, alu_add; unfold v_add; rewrite u_small by lia; rewrite H10;
        first [rewrite blob_val_u8 by lia | rewrite blob_val_s8 by lia]; unfold nu; cbn [nth Z.to_nat Z.add Pos.to_nat Pos.iter_op Nat.add]; unfold bs_byte;
        (repeat f_equal); lia.
    Qed.

    (* [comment removed for export] *)
    Ltac reblob RS :=
      lazymatch goal with
      | EQM : ?M1 = mem_denot _ ?M0 ?log, HLF : log_flat _ _ |- _ =>
        lazymatch goal with
        | HKb : kentry_ok _ _ M0 (KBlobD (SA ?b ?k) ?l ?bk), HK : know_ok _ _ M1 ?kn |- _ =>
          let Hfr := fresh "Hfr" in
          assert (Hfr : frame_mod M0 M1 (regions_denot E RS))
            by (rewrite EQM; apply (frame_mod_mem_denot E M0 log RS HLF); [flats_auto | vm_compute; reflexivity]);
          let H := fresh "HKb" in
          assert (H : kentry_ok SEGS E M1 (KBlobD (SA b k) l bk));
          [ apply (kblobd_frame SEGS E M0 M1 b k l bk _ HKb Hfr);
            unfold regions_denot; cbn [map fst snd]; 
            repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; unfold estart, adenot; cbn [a_base a_off edenot]; ev_simpl E;
            rewrite_getr; unfold v_addi; rewrite ?u_small by lia; first [lia | match goal with |- ?g => idtac "APART" g end]
          | let HK' := fresh "HK" in
            pose proof (know_ok_snoc SEGS E M1 _ _ HK H) as HK'; clear HK; clear HKb; clear EQM; clear HLF;
            rename HK' into HK; rename H into HKb; cbn [app] in HK ]
        end
      end.

    Ltac pin_be32 HR r v ids :=
      pin_reg HR r v by
        (rewrite (HR r);
         lazymatch goal with |- edenot _ ?e = _ =>
           apply bv_eq; rewrite (beval_bytes E nu nu_range atoms e ids atoms_ok_i ltac:(cbn; lia) ltac:(vm_compute; reflexivity))
         end;
         cbn [edenot ev E vals_ev]; ev_simpl E; rewrite u_small by lia; unfold nu, be32; cbn [bytes_val nth]; lia).

    Lemma body_ok : runs_to SEGS (mkst (FP:=FPc) R (Z_to_bv 64 0x13aa8) mem rom) Q.
    Proof using E H1 H10 H11 H12 H13 H14 H15 H16 HFK HRK HT24 HTD HTst Hblob Hbs Hdata Hdnz Hi Hlen Hp0 Hpal Hret Hsig Ht0 Htags Htal Htc IH.
      destruct Htags as (Htc0 & Hpsz & Hall). destruct (Hall i Hi) as [Hs4 Hend].
      pose proof (be32_range bs (132 + 12 * i + 4)) as Ro. pose proof (be32_range bs (132 + 12 * i + 8)) as Rs.
      pose proof (u64_range data) as Rd. pose proof (u64_range T) as RT.
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs])).
      assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs])).
      pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
      pose proof kn1_ok as HK. pose proof kblob_ok as HKb.
      (* [comment removed for export] *)
      run_fp 100%nat (@nil Z) noscr false.
      branch_case as Hc.
      - (* [comment removed for export] *)
        run_fp 100%nat [0x13b30%Z] noscr true.
        reblob [(SA (EVar 12) 0, 24%Z)].
        pin_be32 HR (11%bv:reg) (EVar 66) [11; 10; 9; 8]%nat.
        run_fp 100%nat [0x13b8c%Z] noscr true.
        reblob [(SA (EVar 12) 0, 24%Z)].
        pin_be32 HR (10%bv:reg) (EVar 65) [7; 6; 5; 4]%nat.
        (* [comment removed for export] *)
        run_fp 100%nat (@nil Z) (dirs [false]) true.
        lazymatch goal with
        | EQM : ?M1 = mem_denot _ ?M0 ?log, HLF : log_flat _ _ |- _ =>
          assert (Hfr3 : frame_mod M0 M1 (regions_denot E [(SA (EVar 12) 0, 24%Z)]))
            by (rewrite EQM; apply (frame_mod_mem_denot E M0 log _ HLF); [flats_auto | vm_compute; reflexivity]);
          clear EQM HLF
        end.
        fin_ret.
        lazymatch goal with
        | HR : regs_ok _ ?sr ?R2, HF : fregs_ok _ ?sfr (@fp_regs ?FP2), HK : know_ok _ _ ?M2 ?kn |- _ =>
          exists FP2, R2, M2 end.
        split; [regv HR (1%bv:reg); rewrite H1; reflexivity|].
        split; [eapply regs_kept_trans_u; [exact HRK | exact (regs_same_on E _ _ R _ abi_kept HR0 HR ltac:(vm_compute; reflexivity))]|].
        split; [eapply fregs_kept_trans_u; [exact HFK | exact (fregs_same_on E _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity))]|].
        assert (Hrs : regions_denot E [(SA (EVar 12) 0, 24%Z)] = [(T, 24%Z)]).
        { unfold regions_denot. cbn [map fst snd]. unfold adenot. cbn [a_base a_off edenot]. ev_simpl E.
          rewrite H12. unfold v_addi. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
        rewrite Hrs in Hfr, Hfr0, Hfr3.
        split.
        { eapply frame_mod_trans_same; [exact Hfr|]. eapply frame_mod_trans_same; [exact Hfr0|]. exact Hfr3. }
        exists 1%Z. split; [regv HR (10%bv:reg); reflexivity|]. split; [right; reflexivity|]. intros _.
        kread_fact HK (EVar 12) 0%Z 4%nat C0. kread_fact HK (EVar 12) 4%Z 4%nat C4.
        kread_fact HK (EVar 12) 8%Z 4%nat C8. kread_fact HK (EVar 12) 16%Z 8%nat C16.
        rewrite H12 in C0, C4, C8, C16. unfold v_addi in C0, C4, C8, C16.
        rewrite H11, ext_val_4_small in C0 by lia.
        rewrite ext_val_4_small in C8 by lia.
        rewrite H14 in C16.
        split; [| split].
        + exists s_i, (alu64 ALU_ADD data (Z_to_bv 64 off_i)).
          split; [split; [lia | exact C8]|]. split; [exact C16|]. split; [lia|].
          unfold inDATA. rewrite alu_add. unfold v_add. rewrite (u_small off_i), u_small by lia. lia.
        + split; [lia|]. rewrite Z.add_0_r in C0. exact C0.
        + eexists. apply cell32_of_word. exact C4.
      - (* [comment removed for export] *)
        run_fp 100%nat (@nil Z) noscr false.
        branch_case as Hc2.
        + (* [comment removed for export] *)
          apply IH. unfold INV.
          split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]].
          * br_simpl_in E Hc2. rewrite alu_add in Hc2. unfold v_add in Hc2.
            rewrite !Z_to_bv_unsigned, !bv_wrap64_mod in Hc2.
            apply Bool.negb_true_iff in Hc2 || idtac. 
            first [apply Z.eqb_neq in Hc2 | apply Bool.negb_false_iff in Hc2; apply Z.eqb_neq in Hc2 | idtac]. lia.
          * regv_lin HR (10%bv:reg). rewrite u_small by lia. lia.
          * regv HR (15%bv:reg). exact H15.
          * regv HR (13%bv:reg). exact H13.
          * regv HR (16%bv:reg). exact H16.
          * regv HR (11%bv:reg). exact H11.
          * regv HR (12%bv:reg). exact H12.
          * regv HR (14%bv:reg). exact H14.
          * regv HR (1%bv:reg). exact H1.
          * eapply regs_kept_trans_u; [exact HRK | exact (regs_same_on E _ _ R _ abi_kept HR0 HR ltac:(vm_compute; reflexivity))].
          * eapply fregs_kept_trans_u; [exact HFK | exact (fregs_same_on E _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity))].
        + (* [comment removed for export] *)
          run_fp 100%nat (@nil Z) noscr false.
          fin_ret.
          lazymatch goal with
          | HR : regs_ok _ ?sr ?R2, HF : fregs_ok _ ?sfr (@fp_regs ?FP2) |- _ => exists FP2, R2, mem end.
          split; [regv HR (1%bv:reg); rewrite H1; reflexivity|].
          split; [eapply regs_kept_trans_u; [exact HRK | exact (regs_same_on E _ _ R _ abi_kept HR0 HR ltac:(vm_compute; reflexivity))]|].
          split; [eapply fregs_kept_trans_u; [exact HFK | exact (fregs_same_on E _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity))]|].
          split; [apply frame_mod_refl|].
          exists 0%Z. split; [regv HR (10%bv:reg); reflexivity|]. split; [left; reflexivity|]. intros; lia.
    Qed.
  End Body.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma loop_ok : forall (n : nat) (i : Z) (FPc : FPState) (R : bvmap 5 word),
      (tc - i <= Z.of_nat n)%Z -> INV i FPc R ->
      runs_to SEGS (mkst (FP:=FPc) R (Z_to_bv 64 0x13aa8) mem rom) Q.
  Proof using HT24 HTD HTst Hblob Hbs Hdata Hdnz Hlen Hp0 Hpal Hret Hsig Ht0 Htags Htal Htc.
    induction n as [|n IHn]; intros i FPc R Hn HI.
    - destruct HI as (Hi & _). exfalso. lia.
    - destruct HI as (Hi & H10 & H15 & H13 & H16 & H11 & H12 & H14 & H1 & HRK & HFK).
      apply (body_ok i FPc R Hi H10 H15 H13 H16 H11 H12 H14 H1 HRK HFK).
      intros FPc' R' HI'. apply (IHn (i + 1)%Z FPc' R'); [| exact HI'].
      lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Let E0 : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI))
                                 ++ [data; Z_to_bv 64 tc])) (blobs_ev [bs]).

  Definition kn0 : list kentry :=
    [KRange (EVar 10) 1 (2^64 - 24);
     KRange (EVar 12) 1 (2^64 - 24);
     KRange (EVar 64) 1 (2^47);
     KRange (EVar 65) 0 (2^32 - 1);
     KAlign (EVar 10) 8;
     KWord (SA (EVar 10) 0) 8 (EVar 64);
     KWord (SA (EVar 10) 20) 4 (EVar 65)].

  Lemma kn0_ok : know_ok SEGS E0 mem kn0.
  Proof using FPI HP HPd HPtc HT12 HT24 Hdata Hdnz Hlen Hp0 Hp24 Hpal Hsig Ht0 Htags Htc rom.
    unfold kn0. pose proof (u64_range data). pose proof (u64_range T). pose proof (u64_range P).
    unfold know_ok.
    repeat (apply Forall_cons); [..|apply Forall_nil].
    - apply krange_intro; cbn. rewrite HP. lia.
    - apply krange_intro; cbn. rewrite HT12. lia.
    - apply krange_intro; cbn. lia.
    - apply krange_intro; cbn. rewrite u_small by lia. lia.
    - apply kalign_intro; [lia|]. cbn. rewrite HP. exact Hpal.
    - eapply (kword_intro SEGS E0 mem (EVar 10) P 0 8 (EVar 64) data); cbn; try lia; auto.
    - eapply (kword_intro SEGS E0 mem (EVar 10) P 20 4 (EVar 65) (Z_to_bv 64 tc)); cbn; try lia; auto.
  Qed.

  Lemma entry_ok : runs_to SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x13a68) mem rom) Q.
  Proof using E0 HP HPd HPtc HT12 HT24 HTD HTst Hblob Hbs Hdata Hdnz Hlen Hp0 Hp24 Hpal Hra Hret Hsg Hsig Ht0 Htags Htal Htc.
    destruct Htags as (Htc0 & Hpsz & Hall).
    pose proof (u64_range data) as Rd. pose proof (u64_range T) as RT. pose proof (u64_range P) as RP.
    assert (HR : regs_ok E0 (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [bs])).
    assert (HF : fregs_ok E0 (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [bs])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof kn0_ok as HK.
    run_fp 100%nat [0x13aa8%Z] noscr false.
    (* [comment removed for export] *)
    branch_case as Hc.
    - (* [comment removed for export] *)
      run_fp 100%nat (@nil Z) noscr false.
      fin_ret.
      lazymatch goal with
      | HR : regs_ok _ ?sr ?R2, HF : fregs_ok _ ?sfr (@fp_regs ?FP2) |- _ => exists FP2, R2, mem end.
      split; [regv HR (1%bv:reg); rewrite Hra; reflexivity|].
      split; [exact (regs_same_on E0 _ _ regs _ abi_kept HR0 HR ltac:(vm_compute; reflexivity))|].
      split; [exact (fregs_same_on E0 _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity))|].
      split; [apply frame_mod_refl|].
      exists 0%Z. split; [regv HR (10%bv:reg); reflexivity|]. split; [left; reflexivity|]. intros; lia.
    - (* [comment removed for export] *)
      run_fp 100%nat [0x13aa8%Z] noscr false.
      br_simpl_in E0 Hc.
      lazymatch goal with |- runs_to _ (@mkst ?FPx ?Rx _ _ _) _ => apply (loop_ok (Z.to_nat tc) 0%Z FPx Rx); [lia|] end.
      unfold INV.
      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]].
      + rewrite !Z.mod_small in Hc by lia. apply Z.eqb_neq in Hc. lia.
      + regv HR (10%bv:reg). rewrite u_small by lia. lia.
      + regv_lin HR (15%bv:reg). rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. lia.
      + regv_lin HR (13%bv:reg). rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. lia.
      + regv_lin HR (16%bv:reg). rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. lia.
      + regv HR (11%bv:reg). exact Hsg.
      + regv HR (12%bv:reg). exact HT12.
      + regv HR (14%bv:reg). reflexivity.
      + regv HR (1%bv:reg). exact Hra.
      + exact (regs_same_on E0 _ _ regs _ abi_kept HR0 HR ltac:(vm_compute; reflexivity)).
      + exact (fregs_same_on E0 _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity)).
  Qed.
End GT.

Theorem gettag_Ub_ok : gettag_contract SEGS tags_infoub.
Proof.
  intros data len bs P tc psz sig T FPI regs mem rom ret Hra Hret PRE.
  destruct PRE as (HP & Hsg & HT12 & Hsig & (Hlen & Hbs & Hdnz & Hdata & Hblob) & HPd & [Htc HPtc] & Htags &
                   Hp0 & Hp24 & Hpal & Ht0 & Htal & (HTw0 & _ & HTw24 & HTst) & HTD & HPT).
  unfold cell64, cell in HPd. unfold cell in HPtc.
  destruct (entry_ok FPI regs mem rom ret P T data tc psz sig len bs Hra Hret HP Hsg HT12 Hsig Hlen Hbs Hdnz Hdata Hblob
              ltac:(rewrite Z.add_0_r; exact HPd) HPtc Htc Htags Hp0 Hp24 Hpal Ht0 Htal HTst ltac:(lia) HTD)
    as (st' & Hms & (FPI' & regs' & mem' & -> & Hk1 & Hk2 & Hpost)).
  exists FPI', regs', mem'. split; [exact Hms|]. split; [exact Hk1|]. split; [exact Hk2|]. exact Hpost.
Qed.
