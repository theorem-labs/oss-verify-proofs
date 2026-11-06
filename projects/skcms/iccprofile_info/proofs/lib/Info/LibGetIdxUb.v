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
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import SymDriveLZ.
Unset Nia Cache.  (* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.ev_simpl E ::= ev_simpl_lz E.
#[local] Ltac SymDriveFP.ev_simpl_in E H ::= ev_simpl_in_lz E H.
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.run_fp_with_h HR HF HK fuel stops scr chints keep extra ::= run_fp_with_h_lz HR HF HK fuel stops scr chints keep extra.
#[local] Ltac SymDriveFP.branch_case_with HR HF HK Hc ::= branch_case_with_lz HR HF HK Hc.
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

Section GI.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret P T data : word) (tc psz idx len : Z) (bs : list byte).

  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis HP : getr regs 10 = P.
  Hypothesis Hidx : bv_unsigned (getr regs 11) = idx.
  Hypothesis HT12 : getr regs 12 = T.
  Hypothesis Hi : (0 <= idx < tc)%Z.
  Hypothesis Hlen : (0 <= len < 2 ^ 26)%Z.
  Hypothesis Hbs : Z.of_nat (length bs) = len.
  Hypothesis Hdnz : (0 < bv_unsigned data)%Z.
  Hypothesis Hdata : (bv_unsigned data + len < 2 ^ 47)%Z.
  Hypothesis Hblob : forall k, (0 <= k < len)%Z ->
      mem (Z_to_bv 64 (bv_unsigned data + k)) = Some (nth (Z.to_nat k) bs (Z_to_bv 8 0)).
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

  #[local] Abbreviation off_i := (be32 bs (132 + 12 * idx + 4)).
  #[local] Abbreviation s_i := (be32 bs (132 + 12 * idx + 8)).

  Let E : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI))
                                ++ [data; Z_to_bv 64 tc; Z_to_bv 64 len; Z_to_bv 64 off_i; Z_to_bv 64 s_i;
                                    Z_to_bv 64 (bv_unsigned data + 132 + 12 * idx)])) (blobs_ev [bs]).
  (* [comment removed for export] *)

  Definition kn0 : list kentry :=
    [KRange (EVar 10) 1 (2^64 - 24);
     KRange (EVar 12) 1 (2^64 - 24);
     KRange (EVar 64) 1 (2^47);
     KRange (EVar 65) 0 (2^23);
     KRange (EVar 11) 0 (2^23);
     KRange (EVar 67) 0 (2^32 - 1);
     KRange (EVar 68) 0 (2^32 - 1);
     KRange (EVar 69) 1 (2^47 + 132);
     KAlign (EVar 10) 8;
     KAlign (EVar 12) 8;
     KWord (SA (EVar 10) 0) 8 (EVar 64);
     KWord (SA (EVar 10) 20) 4 (EVar 65);
     KWr (SA (EVar 12) 0) 24;
     KDisj (SA (EVar 12) 0) 24 (SA (EVar 69) 0) 12;
     KDisj (SA (EVar 12) 0) 24 (SA (EAlu ALU_ADD (EVar 64) (EVar 67)) 0) 4;
     KBlobD (SA (EVar 64) 0) (EVar 66) 0].

  Lemma kblob_ok : kentry_ok SEGS E mem (KBlobD (SA (EVar 64) 0) (EVar 66) 0).
  Proof using FPI Hblob Hbs Hdata Hdnz Hi Hlen Hp0 Ht0 Htc regs rom.
    pose proof (u64_range data).
    cbn [kentry_ok]. unfold flat, estart, elenZ. cbn. rewrite u_small by lia.
    split; [lia|]. split; [exact Hbs|]. intros k Hk. rewrite Z.add_0_r. apply Hblob. exact Hk.
  Qed.

  Lemma kn0_ok : know_ok SEGS E mem kn0.
  Proof using FPI HP HPd HPtc HT12 HT24 HTD HTst Hblob Hbs Hdata Hdnz Hi Hidx Hlen Hp0 Hp24 Hpal Ht0 Htags Htal Htc rom.
    unfold kn0. pose proof (u64_range data). pose proof (u64_range T). pose proof (u64_range P).
    destruct Htags as (Htc0 & Hpsz & Hall). destruct (Hall idx Hi) as [Hs4 Hend].
    pose proof (be32_range bs (132 + 12 * idx + 4)) as Ro. pose proof (be32_range bs (132 + 12 * idx + 8)) as Rs.
    unfold know_ok.
    repeat (apply Forall_cons); [..|apply Forall_nil].
    - apply krange_intro; cbn. rewrite HP. lia.
    - apply krange_intro; cbn. rewrite HT12. lia.
    - apply krange_intro; cbn. lia.
    - apply krange_intro; cbn. rewrite u_small by lia. lia.
    - apply krange_intro; cbn. rewrite Hidx. lia.
    - apply krange_intro; cbn. rewrite u_small by lia. lia.
    - apply krange_intro; cbn. rewrite u_small by lia. lia.
    - apply krange_intro; cbn. rewrite u_small by lia. lia.
    - apply kalign_intro; [lia|]. cbn. rewrite HP. exact Hpal.
    - apply kalign_intro; [lia|]. cbn. rewrite HT12. exact Htal.
    - eapply (kword_intro SEGS E mem (EVar 10) P 0 8 (EVar 64) data); cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (EVar 10) P 20 4 (EVar 65) (Z_to_bv 64 tc)); cbn; try lia; auto.
    - apply (kwr_intro SEGS E mem (EVar 12) T 0 24); cbn; try lia. exact HT12. rewrite Z.add_0_r. exact HTst.
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite HT12, u_small by lia. lia.
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite HT12, alu_add. unfold v_add.
      rewrite (u_small off_i) by lia. rewrite u_small by lia. lia.
    - apply kblob_ok.
  Qed.

  (* [comment removed for export] *)
  Definition nu (j : nat) : Z :=
    nth j [bs_byte bs (132 + 12 * idx); bs_byte bs (132 + 12 * idx + 1); bs_byte bs (132 + 12 * idx + 2); bs_byte bs (132 + 12 * idx + 3);
           bs_byte bs (132 + 12 * idx + 4); bs_byte bs (132 + 12 * idx + 4 + 1); bs_byte bs (132 + 12 * idx + 4 + 2); bs_byte bs (132 + 12 * idx + 4 + 3);
           bs_byte bs (132 + 12 * idx + 8); bs_byte bs (132 + 12 * idx + 8 + 1); bs_byte bs (132 + 12 * idx + 8 + 2); bs_byte bs (132 + 12 * idx + 8 + 3)]%Z 0%Z.
  Definition atom (sx : bool) (d : Z) : expr * (bool * nat) :=
    (EBlobX sx 0 (EVar 69) d (EVar 64) 1, (sx, Z.to_nat d)).
  Definition atoms : list (expr * (bool * nat)) :=
    [atom true 11; atom false 8; atom false 9; atom false 10;
     atom false 5; atom false 6; atom false 4; atom true 7].

  Lemma nu_range : forall k, (0 <= nu k < 256)%Z.
  Proof using . intros k. unfold nu. do 12 (destruct k as [|k]; [cbn [nth]; apply bs_byte_range|]). destruct k; cbn; lia. Qed.

  Lemma atoms_ok_i : atoms_ok E nu atoms.
  Proof using FPI Hbs Hdata Hdnz Hi Hlen Hp0 Ht0 Htags Htc regs rom.
    destruct Htags as (Htc0 & Hpsz & Hall).
    unfold atoms, atoms_ok. pose proof (u64_range data).
    repeat (apply Forall_cons); [..|apply Forall_nil];
      unfold atom, atom_ok; cbn [edenot eb ev E blobs_ev nth]; ev_simpl E; rewrite u_small by lia;
      first [rewrite blob_val_u8 by lia | rewrite blob_val_s8 by lia]; unfold nu; cbn [nth Z.to_nat Z.add Pos.to_nat Pos.iter_op Nat.add]; unfold bs_byte;
      (repeat f_equal); lia.
  Qed.

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

  Definition POST (mem' : word -> option byte) : Prop :=
    frame_mod mem mem' [(T, 24%Z)] /\
    tag_ok SEGS mem' data len (bv_unsigned T) /\
    (exists s, cell32 SEGS mem' (bv_unsigned T) s) /\
    (exists ty, cell32 SEGS mem' (bv_unsigned T + 4) ty).

  Lemma getidx_run :
    runs_to SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x13cfc) mem rom)
      (fun st' => exists (FPI' : FPState) regs' mem',
          st' = mkst (FP:=FPI') regs' ret mem' rom /\
          regs_kept abi_kept regs regs' /\
          fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI')) /\
          POST mem').
  Proof using E HP HPd HPtc HT12 HT24 HTD HTst Hblob Hbs Hdata Hdnz Hi Hidx Hlen Hp0 Hp24 Hpal Hra Hret Ht0 Htags Htal Htc.
    destruct Htags as (Htc0 & Hpsz & Hall). destruct (Hall idx Hi) as [Hs4 Hend].
    pose proof (be32_range bs (132 + 12 * idx + 4)) as Ro. pose proof (be32_range bs (132 + 12 * idx + 8)) as Rs.
    pose proof (u64_range data) as Rd. pose proof (u64_range T) as RT. pose proof (u64_range P) as RP.
    assert (HR : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [bs])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [bs])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof kn0_ok as HK. pose proof kblob_ok as HKb.
    (* [comment removed for export] *)
    run_fp 100%nat [0x13d4c%Z] (dirs [false; false]) false.
    pin_reg HR (10%bv:reg) (EVar 69) by
      (rewrite (HR 10%bv); lazymatch goal with |- edenot _ ?e = _ =>
         let l := eval vm_compute in (lin_of e) in
         rewrite (edenot_lin E e); change (lin_of e) with l; cbn [fst snd tden]; unfold uE end;
       cbn [edenot ev E vals_ev]; ev_simpl E; rewrite Hidx; f_equal; lia).
    (* [comment removed for export] *)
    run_fp 100%nat [0x13da8%Z] noscr true.
    reblob [(SA (EVar 12) 0, 24%Z)].
    pin_be32 HR (11%bv:reg) (EVar 68) [11; 10; 9; 8]%nat.
    (* [comment removed for export] *)
    run_fp 100%nat [0x13e04%Z] noscr true.
    reblob [(SA (EVar 12) 0, 24%Z)].
    pin_be32 HR (10%bv:reg) (EVar 67) [7; 6; 5; 4]%nat.
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
    split; [regv HR (1%bv:reg); rewrite Hra; reflexivity|].
    split; [exact (regs_same_on E _ _ regs _ abi_kept HR0 HR ltac:(vm_compute; reflexivity))|].
    split; [exact (fregs_same_on E _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity))|].
    assert (Hrs : regions_denot E [(SA (EVar 12) 0, 24%Z)] = [(T, 24%Z)]).
    { unfold regions_denot. cbn [map fst snd]. unfold adenot. cbn [a_base a_off edenot]. ev_simpl E.
      rewrite HT12. unfold v_addi. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
    rewrite Hrs in Hfr, Hfr0, Hfr3.
    split.
    { eapply frame_mod_trans_same; [exact Hfr|]. eapply frame_mod_trans_same; [exact Hfr0|]. exact Hfr3. }
    kread_fact HK (EVar 12) 0%Z 4%nat C0. kread_fact HK (EVar 12) 4%Z 4%nat C4.
    kread_fact HK (EVar 12) 8%Z 4%nat C8. kread_fact HK (EVar 12) 16%Z 8%nat C16.
    rewrite HT12 in C0, C4, C8, C16. unfold v_addi in C0, C4, C8, C16.
    rewrite ext_val_4_small in C8 by lia.
    split; [| split].
    - exists s_i, (alu64 ALU_ADD data (Z_to_bv 64 off_i)).
      split; [split; [lia | exact C8]|]. split; [exact C16|]. split; [lia|].
      unfold inDATA. rewrite alu_add. unfold v_add. rewrite (u_small off_i), u_small by lia. lia.
    - eexists. apply cell32_of_word. rewrite Z.add_0_r in C0. exact C0.
    - eexists. apply cell32_of_word. exact C4.
  Qed.
End GI.

Theorem getidx_Ub_ok : getidx_contract SEGS tags_infoub.
Proof.
  intros data len bs P tc psz idx T FPI regs mem rom ret Hra Hret PRE.
  destruct PRE as (HP & Hidx & HT12 & Hi & (Hlen & Hbs & Hdnz & Hdata & Hblob) & HPd & [Htc HPtc] & Htags &
                   Hp0 & Hp24 & Hpal & Ht0 & Htal & (HTw0 & _ & HTw24 & HTst) & HTD & HPT).
  unfold cell64, cell in HPd. unfold cell in HPtc.
  pose proof (u64_range T).
  destruct (getidx_run FPI regs mem rom ret P T data tc psz idx len bs Hra Hret HP
              ltac:(rewrite Hidx; apply u_small; lia) HT12 Hi Hlen Hbs Hdnz Hdata Hblob
              ltac:(rewrite Z.add_0_r; exact HPd) HPtc Htc Htags Hp0 Hp24 Hpal Ht0 Htal HTst ltac:(lia) HTD)
    as (st' & Hms & (FPI' & regs' & mem' & -> & Hk1 & Hk2 & Hpost)).
  exists FPI', regs', mem'. split; [exact Hms|]. split; [exact Hk1|]. split; [exact Hk2|]. exact Hpost.
Qed.
