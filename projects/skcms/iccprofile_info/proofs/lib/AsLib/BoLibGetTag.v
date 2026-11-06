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
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs LibFrame.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsLibPlace.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymDriveLZ.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsFuzzContract AsLibShadow AsLibFPLib AsLibDefs BoBase AsLibFrame AsLibTagsSpec AsLibTagsLib AsLibBswap.
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

#[local] Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Lemma regs_kept_trans : forall l r1 r2 r3, regs_kept l r1 r2 -> regs_kept l r2 r3 -> regs_kept l r1 r3.
Proof. intros l r1 r2 r3 A B r Hr. rewrite (B r Hr). apply A. exact Hr. Qed.
(* [comment removed for export] *)
Definition loop_kept : list reg := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma regs_kept_sp : forall r1 r2, regs_kept loop_kept r1 r2 -> getr r2 2 = getr r1 2 -> regs_kept abi_kept r1 r2.
Proof.
  intros r1 r2 K H2 r Hr. unfold abi_kept in Hr. cbn [In] in Hr.
  destruct Hr as [<- | Hr]; [exact H2|]. apply K. unfold loop_kept. cbn [In]. exact Hr.
Qed.
Lemma fregs_kept_trans : forall l r1 r2 r3, fregs_kept l r1 r2 -> fregs_kept l r2 r3 -> fregs_kept l r1 r3.
Proof. intros l r1 r2 r3 A B r Hr. rewrite (B r Hr). apply A. exact Hr. Qed.

Section GT.
  Variable ceil : Z.
  (* [comment removed for export] *)
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem0 mem rom : word -> option byte).
  Variables (ret sp P T data : word) (tc psz sig len : Z) (bs : list byte).

  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis HP : getr regs 10 = P.
  Hypothesis Hsg : getr regs 11 = Z_to_bv 64 sig.
  Hypothesis HT12 : getr regs 12 = T.
  Hypothesis Hsig : (0 <= sig < 2 ^ 32)%Z.
  (* [comment removed for export] *)
  Hypothesis Hlen : (0 <= len < 2 ^ 26)%Z.
  Hypothesis Hbs : Z.of_nat (length bs) = len.
  Hypothesis Hdrange : (appm (bv_unsigned data) len /\ (0 < bv_unsigned data)%Z) /\ (bv_unsigned data + len <= ceil)%Z.
  Hypothesis Hblob : forall k, (0 <= k < len)%Z ->
      mem (Z_to_bv 64 (bv_unsigned data + k)) = Some (nth (Z.to_nat k) bs (Z_to_bv 8 0)).
  Hypothesis Hshd : shdata mem (bv_unsigned data) len.
  (* [comment removed for export] *)
  Hypothesis HPd : rdn SEGS mem0 (Z_to_bv 64 (bv_unsigned P + 0)) 8 = Some (word_to_le_bytes 8 data).
  Hypothesis HPtc : rdn SEGS mem0 (Z_to_bv 64 (bv_unsigned P + 20)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tc)).
  Hypothesis Htc : (0 <= tc < 2 ^ 32)%Z.
  Hypothesis Htags : (0 <= tc)%Z /\ (132 + 12 * tc <= psz <= len)%Z /\
     forall j, (0 <= j < tc)%Z ->
       let off := be32 bs (132 + 12 * j + 4) in let s := be32 bs (132 + 12 * j + 8) in
       (4 <= s)%Z /\ (off + s <= psz)%Z.
  Hypothesis Hpal : (bv_unsigned P mod 8 = 0)%Z.
  Hypothesis HPrange : (appm (bv_unsigned P) 24 /\ (0 < bv_unsigned P)%Z) /\ (bv_unsigned P + 24 <= ceil)%Z.
  Hypothesis HshP : shz mem0 (bv_unsigned P) 3.
  Hypothesis Hsb : sbcell SEGS 0x9f920 0xa79b8 mem0.
  (* [comment removed for export] *)
  Hypothesis Htal : (bv_unsigned T mod 8 = 0)%Z.
  Hypothesis HTrange : (ceil <= bv_unsigned T)%Z /\ (bv_unsigned T + 24 <= 2 ^ 47)%Z.
  Hypothesis HTst : store_ok SEGS mem (Z_to_bv 64 (bv_unsigned T)) (Z.to_nat 24) = true.
  Hypothesis HshT : shz mem (bv_unsigned T) 3.
  Hypothesis HTsp : (bv_unsigned T + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned T)%Z.
  (* [comment removed for export] *)
  Hypothesis Hsprange : ((AS_STKLO <= ceil)%Z /\ (ceil + 16 <= bv_unsigned sp)%Z) /\ (bv_unsigned sp <= 2 ^ 47)%Z.
  Hypothesis Hstk : store_ok SEGS mem0 (Z_to_bv 64 (bv_unsigned sp - 16)) 16 = true.
  Hypothesis Hfr0 : frame_mod mem0 mem [(Z_to_bv 64 (bv_unsigned sp - 16), 16%Z)].
  Hypothesis Hrsp : rdn SEGS mem (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = Some (word_to_le_bytes 8 ret).

  Definition RSall : list (word * Z) := [(Z_to_bv 64 (bv_unsigned sp - 16), 16%Z); (T, 24%Z)].

  Definition POST (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
    frame_mod mem0 mem' RSall /\
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

  Lemma post_frame_T : forall mem', frame_mod mem mem' [(T, 24%Z)] -> frame_mod mem0 mem' RSall.
  Proof using mem0 mem sp T Hfr0. intros mem' H. exact (frame_mod_trans _ _ _ _ _ Hfr0 H). Qed.
  Lemma post_frame_none : frame_mod mem0 mem RSall.
  Proof using mem0 mem sp T Hfr0. apply post_frame_T. apply frame_mod_refl. Qed.

  Definition INV (i : Z) (FPc : FPState) (R : bvmap 5 word) : Prop :=
    (0 <= i < tc)%Z /\
    (bv_unsigned (getr R 13) = 12 * i)%Z /\
    (bv_unsigned (getr R 5) = 12 * tc)%Z /\
    getr R 15 = data /\
    (bv_unsigned (getr R 6) = bv_unsigned data + 140)%Z /\
    (bv_unsigned (getr R 17) = 2 ^ 64 - 133 - bv_unsigned data)%Z /\
    getr R 11 = Z_to_bv 64 sig /\ getr R 12 = T /\ getr R 14 = Z_to_bv 64 SB /\
    getr R 1 = ret /\ getr R 2 = Z_to_bv 64 (bv_unsigned sp - 16) /\
    regs_kept loop_kept regs R /\
    fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPc)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Body.
    Variables (i : Z) (FPc : FPState) (R : bvmap 5 word).
    Hypothesis Hi : (0 <= i < tc)%Z.
    Hypothesis H13 : (bv_unsigned (getr R 13) = 12 * i)%Z.
    Hypothesis H5 : (bv_unsigned (getr R 5) = 12 * tc)%Z.
    Hypothesis H15 : getr R 15 = data.
    Hypothesis H6 : (bv_unsigned (getr R 6) = bv_unsigned data + 140)%Z.
    Hypothesis H17 : (bv_unsigned (getr R 17) = 2 ^ 64 - 133 - bv_unsigned data)%Z.   (* [comment removed for export] *)
    Hypothesis H11 : getr R 11 = Z_to_bv 64 sig.
    Hypothesis H12 : getr R 12 = T.
    Hypothesis H14 : getr R 14 = Z_to_bv 64 SB.
    Hypothesis H1 : getr R 1 = ret.
    Hypothesis H2 : getr R 2 = Z_to_bv 64 (bv_unsigned sp - 16).   (* [comment removed for export] *)
    Hypothesis HRK : regs_kept loop_kept regs R.
    Hypothesis HFK : fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPc)).
    Hypothesis IH : forall (FPc' : FPState) (R' : bvmap 5 word),
        INV (i + 1) FPc' R' -> runs_to SEGS (mkst (FP:=FPc') R' (Z_to_bv 64 0x812d8) mem rom) Q.

    #[local] Abbreviation off_i := (be32 bs (132 + 12 * i + 4)).
    #[local] Abbreviation s_i := (be32 bs (132 + 12 * i + 8)).

    (* [comment removed for export] *)
    Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPc))
                                  ++ [Z_to_bv 64 len; Z_to_bv 64 off_i; Z_to_bv 64 s_i;
                                      Z_to_bv 64 (bv_unsigned data + 132 + 12 * i)])) (blobs_ev [bs]).

    Definition kn1 : list kentry :=
      [KWord (SA (EVar 2) 8) 8 (EVar 1);
       KRange (EVar 2) AS_STKLO (2^47 - 16);
       KRange (EVar 15) 1 (2 ^ 47 - 16);
       KRange (EVar 6) 140 (2 ^ 47 - 16 + 140);
       KRange (EVar 17) (2 ^ 64 - 133 - 2 ^ 47) (2 ^ 64 - 133 - 1);
       KRange (EVar 13) 0 (2^36);
       KRange (EVar 5) 0 (2^36);
       KRange (EVar 11) 0 (2^32 - 1);
       KRange (EVar 67) 132 (2 ^ 47 - 16);
       KRange (EVar 64) 0 (2^26);
       KRange (EVar 65) 0 (2^32 - 1);
       KRange (EVar 66) 0 (2^32 - 1);
       KRange (EVar 12) AS_STKLO (2^47 - 24);
       KAlign (EVar 12) 8;
       KWr (SA (EVar 12) 0) 24;
       KDisj (SA (EVar 12) 0) 24 (SA (EVar 2) 0) 16;
       KZero (SA (EAlu ALU_SRL (EVar 12) (ELit 3)) SB) (ELit 3);
       KShad (EVar 15) (EVar 64) SB;
       KBlobD (SA (EVar 15) 0) (EVar 64) 0].

    Lemma kn1_ok : know_ok SEGS E mem kn1.
    Proof using ceil mem ret sp P T data tc psz sig len bs Hsig Hlen Hbs Hdrange Hblob Hshd Htags HPrange Htal HTrange HTst HshT HTsp Hsprange Hrsp i FPc R Hi H13 H5 H15 H6 H17 H11 H12 H1 H2.
      unfold kn1. pose proof (u64_range data). pose proof (u64_range T). pose proof (u64_range sp).
      destruct Htags as (Htc0 & Hpsz & Hall). destruct (Hall i Hi) as [Hs4 Hend].
      pose proof (be32_range bs (132 + 12 * i + 4)) as Ro. pose proof (be32_range bs (132 + 12 * i + 8)) as Rs.
      unfold know_ok.
      repeat (apply Forall_cons); [..|apply Forall_nil].
      - eapply (kword_intro SEGS E mem (EVar 2) (Z_to_bv 64 (bv_unsigned sp - 16)) 8 8 (EVar 1) ret); cbn; rewrite ?u_small by lia; try lia; auto.
        replace (bv_unsigned sp - 16 + 8)%Z with (bv_unsigned sp - 8)%Z by lia. exact Hrsp.
      - apply krange_intro; cbn. rewrite H2, u_small by lia. lia.
      - apply krange_intro; cbn. rewrite H15. lia.
      - apply krange_intro; cbn. rewrite H6. lia.
      - apply krange_intro; cbn. rewrite H17. lia.
      - apply krange_intro; cbn. rewrite H13. lia.
      - apply krange_intro; cbn. rewrite H5. lia.
      - apply krange_intro; cbn. rewrite H11, u_small by lia. lia.
      - apply krange_intro; cbn. rewrite u_small by lia. lia.
      - apply krange_intro; cbn. rewrite u_small by lia. lia.
      - apply krange_intro; cbn. rewrite u_small by lia. lia.
      - apply krange_intro; cbn. rewrite u_small by lia. lia.
      - apply krange_intro; cbn. rewrite H12. lia.
      - apply kalign_intro; [lia|]. cbn. rewrite H12. exact Htal.
      - apply (kwr_intro SEGS E mem (EVar 12) T 0 24); cbn; try lia. exact H12. rewrite Z.add_0_r. exact HTst.
      - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite H12, H2, u_small by lia. lia.
      - eapply (kzero_shz_intro SEGS E mem (EVar 12) T 3); [cbn; exact H12 | exact HshT | lia | lia].
      - eapply (kshad_intro SEGS E mem (EVar 15) (EVar 64) data len); [cbn; exact H15 | cbn; rewrite u_small by lia; reflexivity | lia | lia | exact Hshd].
      - cbn [kentry_ok]. unfold flat, estart, elenZ. cbn. rewrite H15, u_small by lia.
        split; [lia|]. split; [exact Hbs|]. intros k Hk. rewrite Z.add_0_r. apply Hblob. exact Hk.
    Qed.

    (* [comment removed for export] *)
    Definition nu (j : nat) : Z :=
      nth j [bs_byte bs (132 + 12 * i); bs_byte bs (132 + 12 * i + 1); bs_byte bs (132 + 12 * i + 2); bs_byte bs (132 + 12 * i + 3);
             bs_byte bs (132 + 12 * i + 4); bs_byte bs (132 + 12 * i + 4 + 1); bs_byte bs (132 + 12 * i + 4 + 2); bs_byte bs (132 + 12 * i + 4 + 3);
             bs_byte bs (132 + 12 * i + 8); bs_byte bs (132 + 12 * i + 8 + 1); bs_byte bs (132 + 12 * i + 8 + 2); bs_byte bs (132 + 12 * i + 8 + 3)]%Z 0%Z.
    Definition atom (sx : bool) (d : Z) : expr * (bool * nat) :=
      (EBlobX sx 0 (EVar 67) d (EVar 15) 1, (sx, Z.to_nat d)).
    Definition atoms : list (expr * (bool * nat)) :=
      [atom true 3; atom false 0; atom false 1; atom false 2;
       atom false 8; atom false 9; atom false 10; atom true 11;
       atom false 5; atom false 6; atom false 4; atom true 7].

    Lemma nu_range : forall k, (0 <= nu k < 256)%Z.
    Proof using bs i. intros k. unfold nu. do 12 (destruct k as [|k]; [cbn [nth]; apply bs_byte_range|]). destruct k; cbn; lia. Qed.

    Lemma atoms_ok_i : atoms_ok E nu atoms.
    Proof using ceil sp P T data tc psz len bs Hbs Hdrange Htags HPrange HTrange Hsprange i FPc R Hi H15.
      destruct Htags as (Htc0 & Hpsz & Hall).
      unfold atoms, atoms_ok. pose proof (u64_range data).
      repeat (apply Forall_cons); [..|apply Forall_nil];
        unfold atom, atom_ok; cbn [edenot eb ev E blobs_ev nth]; ev_simpl E; rewrite H15; rewrite (u_small (bv_unsigned data + 132 + 12 * i)) by lia;
        first [rewrite blob_val_u8 by lia | rewrite blob_val_s8 by lia]; unfold nu; cbn [nth Z.to_nat Z.add Pos.to_nat Pos.iter_op Nat.add]; unfold bs_byte;
        (repeat f_equal); lia.
    Qed.

    (* [comment removed for export] *)
    Ltac frame_here :=
      lazymatch goal with
      | EQM : ?M1 = mem_denot _ ?M0 ?log, HLF : log_flat _ _ |- _ =>
        let Hfr := fresh "Hfr" in
        assert (Hfr : frame_mod M0 M1 (regions_denot E [(SA (EVar 12) 0, 24%Z)]))
          by (rewrite EQM; apply (frame_mod_mem_denot E M0 log _ HLF); [flats_auto | vm_compute; reflexivity]);
        clear EQM HLF
      end.

    Ltac pin_be32 HR r v ids :=
      pin_reg HR r v by
        (rewrite (HR r);
         lazymatch goal with |- edenot _ ?e = _ =>
           apply bv_eq; rewrite (beval_bytes E nu nu_range atoms e ids atoms_ok_i ltac:(cbn; lia) ltac:(vm_compute; reflexivity))
         end;
         cbn [edenot ev E vals_ev]; ev_simpl E; rewrite u_small by lia; unfold nu, be32; cbn [bytes_val nth]; lia).

    (* [comment removed for export] *)
    Ltac kept_exit HR0 HR HF0 HF :=
      split; [apply regs_kept_sp;
              [ eapply regs_kept_trans; [exact HRK | exact (regs_same_on E _ _ R _ loop_kept HR0 HR ltac:(vm_compute; reflexivity))]
              | regv_lin HR (2%bv:reg); rewrite H2, Hsp; apply bv_eq;
                rewrite (u_small (bv_unsigned sp - 16)) by lia; rewrite u_small by lia; lia ]|];
      split; [eapply fregs_kept_trans; [exact HFK | exact (fregs_same_on E _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity))]|].
    Ltac kept_loop HR0 HR HF0 HF :=
      split; [eapply regs_kept_trans; [exact HRK | exact (regs_same_on E _ _ R _ loop_kept HR0 HR ltac:(vm_compute; reflexivity))]|];
      exact (fregs_kept_trans _ _ _ _ HFK (fregs_same_on E _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity))).

    Lemma body_ok : runs_to SEGS (mkst (FP:=FPc) R (Z_to_bv 64 0x812d8) mem rom) Q.
    Proof using ceil FPI regs mem0 mem rom ret sp P T data tc psz sig len bs Hret Hsp Hsig Hlen Hbs Hdrange Hblob Hshd Htc Htags HPrange Htal HTrange HTst HshT HTsp Hsprange Hfr0 Hrsp i FPc R Hi H13 H5 H15 H6 H17 H11 H12 H14 H1 H2 HRK HFK IH.
      destruct Htags as (Htc0 & Hpsz & Hall). destruct (Hall i Hi) as [Hs4 Hend].
      pose proof (be32_range bs (132 + 12 * i + 4)) as Ro. pose proof (be32_range bs (132 + 12 * i + 8)) as Rs.
      pose proof (u64_range data) as Rd. pose proof (u64_range T) as RT. pose proof (u64_range sp) as Rsp.
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs])).
      assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs])).
      pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
      pose proof kn1_ok as HK.
      (* [comment removed for export] *)
      pin_reg HR (14%bv:reg) (ELit SB) by (rewrite H14; reflexivity).
      (* [comment removed for export] *)
      run_fp 100%nat [0x8130c%Z] noscr false.
      (* [comment removed for export] *)
      pin_reg HR (10%bv:reg) (EAlu ALU_ADD (EVar 67) (ELit 8)) by
        (rewrite (HR 10%bv); lazymatch goal with |- edenot _ ?e = _ =>
           let l := eval vm_compute in (lin_of e) in
           rewrite (edenot_lin E e); change (lin_of e) with l; cbn [fst snd tden]; unfold uE end;
         cbn [edenot ev E vals_ev]; ev_simpl E; rewrite H6, H13; rewrite alu_add_lit, (u_small (bv_unsigned data + 132 + 12 * i)) by lia; apply bv_eq; rewrite !u_small by lia; lia).
      pin_reg HR (16%bv:reg) (EAlu ALU_ADD (EVar 67) (ELit (-132))) by
        (rewrite (HR 16%bv); lazymatch goal with |- edenot _ ?e = _ =>
           let l := eval vm_compute in (lin_of e) in
           rewrite (edenot_lin E e); change (lin_of e) with l; cbn [fst snd tden]; unfold uE end;
         cbn [edenot ev E vals_ev]; ev_simpl E; rewrite H15, H13; rewrite alu_add_lit, (u_small (bv_unsigned data + 132 + 12 * i)) by lia; apply bv_eq; rewrite !u_small by lia; lia).
      (* [comment removed for export] *)
      run_fp 100%nat (@nil Z) noscr false.
      branch_case as Hc.
      - (* [comment removed for export] *)
        run_fp 150%nat [0x81404%Z] noscr true hints keep_all.
        frame_here.
        pin_be32 HR (17%bv:reg) (EVar 66) [11; 10; 9; 8]%nat.
        run_fp 150%nat [0x81480%Z] noscr true hints keep_all.
        frame_here.
        pin_be32 HR (11%bv:reg) (EVar 65) [7; 6; 5; 4]%nat.
        run_fp 150%nat (@nil Z) noscr true hints keep_all.
        frame_here.
        fin_ret.
        lazymatch goal with
        | HR : regs_ok _ ?sr ?R2, HF : fregs_ok _ ?sfr (@fp_regs ?FP2), HK : know_ok _ _ ?M2 ?kn |- _ =>
          exists FP2, R2, M2 end.
        split; [regv HR (1%bv:reg); rewrite H1; reflexivity|].
        kept_exit HR0 HR HF0 HF.
        assert (Hrs : regions_denot E [(SA (EVar 12) 0, 24%Z)] = [(T, 24%Z)]).
        { unfold regions_denot. cbn [map fst snd]. unfold adenot. cbn [a_base a_off edenot]. ev_simpl E.
          rewrite H12. unfold v_addi. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
        rewrite Hrs in Hfr, Hfr1, Hfr2.
        split.
        { apply post_frame_T. eapply frame_mod_trans_same; [exact Hfr|]. eapply frame_mod_trans_same; [exact Hfr1|]. exact Hfr2. }
        exists 1%Z. split; [regv HR (10%bv:reg); reflexivity|]. split; [right; reflexivity|]. intros _.
        (* [comment removed for export] *)
        kread_fact HK (EVar 12) 0%Z 4%nat C0. kread_fact HK (EVar 12) 4%Z 4%nat C4.
        kread_fact HK (EVar 12) 8%Z 4%nat C8. kread_fact HK (EVar 12) 16%Z 8%nat C16.
        rewrite H12 in C0, C4, C8, C16. unfold v_addi in C0, C4, C8, C16.
        rewrite H11, ext_val_4_small in C0 by lia.
        rewrite ext_val_4_small in C8 by lia.
        rewrite H15 in C16.
        split; [| split].
        + (* [comment removed for export] *)
          exists s_i, (alu64 ALU_ADD data (Z_to_bv 64 off_i)).
          split; [split; [lia | exact C8]|]. split; [exact C16|]. split; [lia|].
          unfold inDATA. rewrite alu_add. unfold v_add. rewrite (u_small off_i), u_small by lia. lia.
        + split; [lia|]. rewrite Z.add_0_r in C0. exact C0.
        + eexists. apply cell32_of_word. exact C4.
      - (* [comment removed for export] *)
        run_fp 100%nat (@nil Z) noscr false.
        branch_case as Hc2.
        + (* [comment removed for export] *)
          run_fp 100%nat (@nil Z) noscr false.
          fin_ret.
          lazymatch goal with
          | HR : regs_ok _ ?sr ?R2, HF : fregs_ok _ ?sfr (@fp_regs ?FP2) |- _ => exists FP2, R2, mem end.
          split; [regv HR (1%bv:reg); rewrite H1; reflexivity|].
          kept_exit HR0 HR HF0 HF.
          split; [apply post_frame_none|].
          exists 0%Z. split; [regv HR (10%bv:reg); reflexivity|]. split; [left; reflexivity|]. intros; lia.
        + (* [comment removed for export] *)
          run_fp 100%nat [0x812d8%Z] noscr false.
          apply IH. unfold INV.
          split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [|split; [|split]]]]]]]]]].
          * Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
            br_simpl_in E Hc2. rewrite alu_add in Hc2. unfold v_add in Hc2.
            rewrite !Z_to_bv_unsigned, !bv_wrap64_mod in Hc2.
            apply Z.eqb_neq in Hc2. rewrite H5, H13 in Hc2. rewrite !Z.mod_small in Hc2 by lia. lia.
            Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
          * regv_lin HR (13%bv:reg). rewrite u_small by lia. lia.
          * regv HR (5%bv:reg). exact H5.
          * regv HR (15%bv:reg). exact H15.
          * regv HR (6%bv:reg). exact H6.
          * regv HR (17%bv:reg). exact H17.
          * regv HR (11%bv:reg). exact H11.
          * regv HR (12%bv:reg). exact H12.
          * regv HR (14%bv:reg). reflexivity.
          * regv HR (1%bv:reg). exact H1.
          * regv HR (2%bv:reg). exact H2.
          * kept_loop HR0 HR HF0 HF.
    Qed.
  End Body.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma loop_ok : forall (n : nat) (i : Z) (FPc : FPState) (R : bvmap 5 word),
      (tc - i <= Z.of_nat n)%Z -> INV i FPc R ->
      runs_to SEGS (mkst (FP:=FPc) R (Z_to_bv 64 0x812d8) mem rom) Q.
  Proof using ceil FPI regs mem0 mem rom ret sp P T data tc psz sig len bs Hret Hsp Hsig Hlen Hbs Hdrange Hblob Hshd Htc Htags HPrange Htal HTrange HTst HshT HTsp Hsprange Hfr0 Hrsp.
    induction n as [|n IHn]; intros i FPc R Hn HI.
    - destruct HI as (Hi & _). exfalso. lia.
    - destruct HI as (Hi & H13 & H5 & H15 & H6 & H17 & H11 & H12 & H14 & H1 & H2 & HRK & HFK).
      apply (body_ok i FPc R Hi H13 H5 H15 H6 H17 H11 H12 H14 H1 H2 HRK HFK).
      intros FPc' R' HI'. apply (IHn (i + 1)%Z FPc' R'); [| exact HI'].
      lia.
  Qed.
End GT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Entry.
  Variable ceil : Z.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp P T data : word) (tc psz sig len : Z) (bs : list byte).

  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis HP : getr regs 10 = P.
  Hypothesis Hsg : getr regs 11 = Z_to_bv 64 sig.
  Hypothesis HT12 : getr regs 12 = T.
  Hypothesis Hsig : (0 <= sig < 2 ^ 32)%Z.
  Hypothesis Hlen : (0 <= len < 2 ^ 26)%Z.
  Hypothesis Hbs : Z.of_nat (length bs) = len.
  Hypothesis Hdrange : (appm (bv_unsigned data) len /\ (0 < bv_unsigned data)%Z) /\ (bv_unsigned data + len <= ceil)%Z.
  Hypothesis Hblob : forall k, (0 <= k < len)%Z ->
      mem (Z_to_bv 64 (bv_unsigned data + k)) = Some (nth (Z.to_nat k) bs (Z_to_bv 8 0)).
  Hypothesis Hshd : shdata mem (bv_unsigned data) len.
  Hypothesis HPd : rdn SEGS mem (Z_to_bv 64 (bv_unsigned P + 0)) 8 = Some (word_to_le_bytes 8 data).
  Hypothesis HPtc : rdn SEGS mem (Z_to_bv 64 (bv_unsigned P + 20)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tc)).
  Hypothesis Htc : (0 <= tc < 2 ^ 32)%Z.
  Hypothesis Htags : (0 <= tc)%Z /\ (132 + 12 * tc <= psz <= len)%Z /\
     forall j, (0 <= j < tc)%Z ->
       let off := be32 bs (132 + 12 * j + 4) in let s := be32 bs (132 + 12 * j + 8) in
       (4 <= s)%Z /\ (off + s <= psz)%Z.
  Hypothesis Hpal : (bv_unsigned P mod 8 = 0)%Z.
  Hypothesis HPrange : (appm (bv_unsigned P) 24 /\ (0 < bv_unsigned P)%Z) /\ (bv_unsigned P + 24 <= ceil)%Z.
  Hypothesis HshP : shz mem (bv_unsigned P) 3.
  Hypothesis Hsb : sbcell SEGS 0x9f920 0xa79b8 mem.
  Hypothesis Htal : (bv_unsigned T mod 8 = 0)%Z.
  Hypothesis HTrange : (ceil <= bv_unsigned T)%Z /\ (bv_unsigned T + 24 <= 2 ^ 47)%Z.
  Hypothesis HTst : store_ok SEGS mem (Z_to_bv 64 (bv_unsigned T)) (Z.to_nat 24) = true.
  Hypothesis HshT : shz mem (bv_unsigned T) 3.
  Hypothesis HTsp : (bv_unsigned T + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned T)%Z.
  Hypothesis Hsprange : ((AS_STKLO <= ceil)%Z /\ (ceil + 16 <= bv_unsigned sp)%Z) /\ (bv_unsigned sp <= 2 ^ 47)%Z.
  Hypothesis Hstk : store_ok SEGS mem (Z_to_bv 64 (bv_unsigned sp - 16)) 16 = true.

  Let E0 : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI))
                                 ++ [data; Z_to_bv 64 tc])) (blobs_ev [bs]).

  Definition kn0v1 : list kentry :=
    [KWord (SA (ELit 0) 0x9f920) 8 (ELit 0xa79b8); KWord (SA (ELit 0) 0xa79b8) 8 (ELit SB);
     KRange (EVar 10) 1 (2 ^ 47 - 24); KAlign (EVar 10) 8;
     KRange (EVar 12) AS_STKLO (2^47 - 24);
     KRange (EVar 2) (AS_STKLO + 16) (2^47); KWr (SA (EVar 2) (-16)) 16;
     KDisj (SA (EVar 12) 0) 24 (SA (EVar 2) (-16)) 16;
     KZero (SA (EAlu ALU_SRL (EVar 10) (ELit 3)) SB) (ELit 3);
     KRange (EVar 64) 1 (2 ^ 47 - 16);
     KRange (EVar 65) 0 (2^32 - 1);
     KWord (SA (EVar 10) 0) 8 (EVar 64);
     KWord (SA (EVar 10) 20) 4 (EVar 65)].

  Lemma kn0v1_ok : know_ok SEGS E0 mem kn0v1.
  Proof using ceil FPI regs mem sp P T data tc len bs Hsp HP HT12 Hbs Hdrange HPd HPtc Htc Hpal HPrange HshP Hsb HTrange HTsp Hsprange Hstk.
    unfold kn0v1. pose proof (u64_range data). pose proof (u64_range T). pose proof (u64_range P). pose proof (u64_range sp).
    destruct Hsb as [Hg Hs]. unfold cell64, cell in Hg, Hs.
    unfold know_ok.
    repeat (apply Forall_cons); [..|apply Forall_nil].
    - eapply (kword_intro SEGS E0 mem (ELit 0) (Z_to_bv 64 0) 0x9f920 8 (ELit 0xa79b8) (Z_to_bv 64 0xa79b8)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
    - eapply (kword_intro SEGS E0 mem (ELit 0) (Z_to_bv 64 0) 0xa79b8 8 (ELit SB) (Z_to_bv 64 SB)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
    - apply krange_intro; cbn. rewrite HP. lia.
    - apply kalign_intro; [lia|]. cbn. rewrite HP. exact Hpal.
    - apply krange_intro; cbn. rewrite HT12. lia.
    - apply krange_intro; cbn. rewrite Hsp. lia.
    - apply (kwr_intro SEGS E0 mem (EVar 2) sp (-16) 16); cbn; try lia; auto.
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E0. rewrite HT12, Hsp. lia.
    - eapply (kzero_shz_intro SEGS E0 mem (EVar 10) P 3); [cbn; exact HP | exact HshP | lia | lia].
    - apply krange_intro; cbn. lia.
    - apply krange_intro; cbn. rewrite u_small by lia. lia.
    - eapply (kword_intro SEGS E0 mem (EVar 10) P 0 8 (EVar 64) data); cbn; try lia; auto.
    - eapply (kword_intro SEGS E0 mem (EVar 10) P 20 4 (EVar 65) (Z_to_bv 64 tc)); cbn; try lia; auto.
  Qed.

  Definition kn0 : list kentry := kn0v1 ++
    [KDisj (SA (EVar 10) 0) 24 (SA (EVar 12) 0) 24;
     KDisj (SA (EVar 10) 0) 24 ZSH ZSHL; KDisj (SA (EVar 10) 0) 24 ZIMG ZIMGL;
     KDisj (SA (EVar 10) 0) 24 (SA (EVar 2) (-16)) 16].
  Lemma kn0_ok : know_ok SEGS E0 mem kn0.
  Proof using ceil FPI regs mem sp P T data tc len bs Hsp HP HT12 Hbs Hdrange HPd HPtc Htc Hpal HPrange HshP Hsb HTrange HTsp Hsprange Hstk. apply know_ok_app; [exact kn0v1_ok | kn_place]. Qed.

  #[local] Abbreviation Q0 := (Q FPI regs mem rom ret sp T data sig len).

  Lemma entry_ok : runs_to SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x8125c) mem rom) Q0.
  Proof using ceil FPI regs mem rom ret sp P T data tc psz sig len bs Hra Hret Hsp HP Hsg HT12 Hsig Hlen Hbs Hdrange Hblob Hshd HPd HPtc Htc Htags Hpal HPrange HshP Hsb Htal HTrange HTst HshT HTsp Hsprange Hstk.
    destruct Htags as (Htc0 & Hpsz & Hall).
    pose proof (u64_range data) as Rd. pose proof (u64_range T) as RT. pose proof (u64_range P) as RP. pose proof (u64_range sp) as Rsp.
    assert (HR : regs_ok E0 (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [bs])).
    assert (HF : fregs_ok E0 (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [bs])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof kn0_ok as HK.
    (* [comment removed for export] *)
    run_fp 100%nat [0x812b8%Z] noscr true.
    (* [comment removed for export] *)
    lazymatch goal with
    | EQM : ?M1 = mem_denot _ ?M0 ?log, HLF : log_flat _ _ |- _ =>
      assert (Hfr0 : frame_mod M0 M1 [(Z_to_bv 64 (bv_unsigned sp - 16), 16%Z)])
        by (rewrite EQM; replace [(Z_to_bv 64 (bv_unsigned sp - 16), 16%Z)] with (regions_denot E0 [(SA (EVar 2) (-16), 16%Z)])
              by (unfold regions_denot; cbn [map fst snd]; unfold adenot; cbn [a_base a_off edenot]; ev_simpl E0; rewrite Hsp; reflexivity);
            apply (frame_mod_mem_denot E0 M0 log _ HLF); [flats_auto | vm_compute; reflexivity]);
      clear EQM HLF
    end.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    lazymatch goal with |- runs_to _ (@mkst _ _ _ ?M1 _) _ =>
      assert (ApD : apart (bv_unsigned data) len [(Z_to_bv 64 (bv_unsigned sp - 16), 16%Z)]) by (solve_apart);
      assert (ApS : apart (SB + bv_unsigned data / 8) (len / 8 + 1) [(Z_to_bv 64 (bv_unsigned sp - 16), 16%Z)])
        by (unfold SB; assert (bv_unsigned data / 8 < 2 ^ 44)%Z by (apply Z.div_lt_upper_bound; lia); solve_apart);
      assert (ApT : apart (SB + bv_unsigned T / 8) 3 [(Z_to_bv 64 (bv_unsigned sp - 16), 16%Z)])
        by (unfold SB; assert (bv_unsigned T / 8 < 2 ^ 44)%Z by (apply Z.div_lt_upper_bound; lia); solve_apart);
      pose proof (bytes_frame mem M1 _ data len bs Hfr0 ltac:(lia) ApD Hblob) as Hblob1;
      pose proof (shdata_frame mem M1 _ (bv_unsigned data) len Hfr0 Hshd ltac:(lia) ltac:(lia) ltac:(lia) ApS) as Hshd1;
      pose proof (shz_frame mem M1 _ (bv_unsigned T) 3 Hfr0 HshT ltac:(lia) ltac:(lia) ApT) as HshT1;
      pose proof (store_ok_frame SEGS mem M1 _ _ _ Hfr0 HTst) as HTst1
    end.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    kread_fact HK (EVar 2) (-8)%Z 8%nat Hrsp. rewrite Hsp, Hra in Hrsp. unfold v_addi in Hrsp.
    replace (bv_unsigned sp + -8)%Z with (bv_unsigned sp - 8)%Z in Hrsp by lia.
    (* [comment removed for export] *)
    branch_case as Hc.
    - (* [comment removed for export] *)
      run_fp 100%nat (@nil Z) noscr false.
      fin_ret.
      lazymatch goal with
      | HR : regs_ok _ ?sr ?R2, HF : fregs_ok _ ?sfr (@fp_regs ?FP2), HK : know_ok _ _ ?M1 _ |- _ => exists FP2, R2, M1 end.
      split; [regv HR (1%bv:reg); rewrite Hra; reflexivity|].
      split; [apply regs_kept_sp; [exact (regs_same_on E0 _ _ regs _ loop_kept HR0 HR ltac:(vm_compute; reflexivity))
                                 | regv_lin HR (2%bv:reg); rewrite Hsp; apply bv_eq; rewrite u_small by lia; lia ]|].
      split; [exact (fregs_same_on E0 _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity))|].
      split; [eapply post_frame_none; exact Hfr0|].
      exists 0%Z. split; [regv HR (10%bv:reg); reflexivity|]. split; [left; reflexivity|]. intros; lia.
    - (* [comment removed for export] *)
      run_fp 100%nat [0x812d8%Z] noscr false.
      br_simpl_in E0 Hc.
      lazymatch goal with |- runs_to _ (@mkst ?FPx ?Rx _ ?M1 _) _ =>
        apply (loop_ok ceil FPI regs mem M1 rom ret sp P T data tc psz sig len bs Hret Hsp Hsig Hlen Hbs Hdrange Hblob1 Hshd1 Htc
                 (conj Htc0 (conj Hpsz Hall)) HPrange Htal HTrange HTst1 HshT1 HTsp Hsprange Hfr0 Hrsp (Z.to_nat tc) 0%Z FPx Rx); [lia|] end.
      unfold INV.
      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [|split; [|split]]]]]]]]]].
      + rewrite ?Z.mod_small in Hc by lia. apply Z.eqb_neq in Hc. lia.
      + regv HR (13%bv:reg). reflexivity.
      + regv_lin HR (5%bv:reg). rewrite (u_small tc) by lia. rewrite u_small by lia. lia.
      + regv HR (15%bv:reg). reflexivity.
      + regv_lin HR (6%bv:reg). rewrite u_small by lia. lia.
      + regv_lin HR (17%bv:reg). rewrite Z_to_bv_unsigned, bv_wrap64_mod.
        match goal with |- (?x mod _ = _)%Z => replace x with ((2 ^ 64 - 133 - bv_unsigned data) + (-1) * 2 ^ 64)%Z by lia end.
        rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity.
      + regv HR (11%bv:reg). exact Hsg.
      + regv HR (12%bv:reg). exact HT12.
      + regv HR (14%bv:reg). reflexivity.
      + regv HR (1%bv:reg). exact Hra.
      + regv_lin HR (2%bv:reg). rewrite Hsp. f_equal. lia.
      + split; [exact (regs_same_on E0 _ _ regs _ loop_kept HR0 HR ltac:(vm_compute; reflexivity))|].
        exact (fregs_same_on E0 _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity)).
  Qed.
End Entry.

Theorem gettag_bo_ok : forall ceil, gettag_contract_as SEGS as_both ceil.
Proof.
  intros ceil data len bs P tc psz sig T FPI regs mem rom ret Hra Hret PRE.
  destruct PRE as (HP & Hsg & HT12 & Hsig & ((Hlen & Hbs & Hdnz & Hdata & Hblob) & Hdheap & Hdal & Hshd) & HPd & [Htc HPtc] & Htags &
                   Hpal & HPheap & HshP & Htal & HTstk & (HTw0 & _ & HTw24 & HTst) & HshT & Hsb & (sp & Hsp & Hfr & HTsp)).
  unfold cell64, cell in HPd. unfold cell in HPtc.
  apply (as_sb_both SEGS mem) in Hsb.
  destruct Hfr as ([Hst1 Hst2] & Hsal & (_ & _ & _ & Hwr)).
  unfold heapish, stackish in *. app_facts.
  destruct (entry_ok ceil FPI regs mem rom ret sp P T data tc psz sig len bs Hra Hret Hsp HP Hsg HT12 Hsig Hlen Hbs ltac:(plc) Hblob Hshd
              ltac:(rewrite Z.add_0_r; exact HPd) HPtc Htc Htags Hpal ltac:(plc) HshP Hsb Htal ltac:(plc) HTst HshT HTsp ltac:(plc) Hwr)
    as (st' & Hms & (FPI' & regs' & mem' & -> & Hk1 & Hk2 & Hpost)).
  exists FPI', regs', mem'. split; [exact Hms|]. split; [exact Hk1|]. split; [exact Hk2|].
  unfold gettag_post_as. rewrite Hsp. exact Hpost.
Qed.
