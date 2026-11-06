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

Section GI.
  Variable ceil : Z.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp P T data : word) (tc psz idx len : Z) (bs : list byte).

  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis HP : getr regs 10 = P.
  Hypothesis Hidx : bv_unsigned (getr regs 11) = idx.
  Hypothesis HT12 : getr regs 12 = T.
  Hypothesis Hi : (0 <= idx < tc)%Z.
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
  Hypothesis HTrange : (appm (bv_unsigned T) 24 /\ (0 < bv_unsigned T)%Z) /\ (bv_unsigned T + 24 <= ceil)%Z.
  Hypothesis HTst : store_ok SEGS mem (Z_to_bv 64 (bv_unsigned T)) (Z.to_nat 24) = true.
  Hypothesis HshT : shz mem (bv_unsigned T) 3.
  Hypothesis HTD : (bv_unsigned data + len <= bv_unsigned T \/ bv_unsigned T + 24 <= bv_unsigned data)%Z.
  Hypothesis HPT : (bv_unsigned P + 24 <= bv_unsigned T \/ bv_unsigned T + 24 <= bv_unsigned P)%Z.
  Hypothesis Hsprange : ((AS_STKLO <= ceil)%Z /\ (ceil + 16 <= bv_unsigned sp)%Z) /\ (bv_unsigned sp <= 2 ^ 47)%Z.
  Hypothesis Hstk : store_ok SEGS mem (Z_to_bv 64 (bv_unsigned sp - 16)) 16 = true.

  #[local] Abbreviation off_i := (be32 bs (132 + 12 * idx + 4)).
  #[local] Abbreviation s_i := (be32 bs (132 + 12 * idx + 8)).

  Let E : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI))
                                ++ [data; Z_to_bv 64 tc; Z_to_bv 64 len; Z_to_bv 64 off_i; Z_to_bv 64 s_i;
                                    Z_to_bv 64 (bv_unsigned data + 12 * idx)])) (blobs_ev [bs]).
  (* [comment removed for export] *)

  Definition kn0v1 : list kentry :=
    [KWord (SA (ELit 0) 0x9f920) 8 (ELit 0xa79b8); KWord (SA (ELit 0) 0xa79b8) 8 (ELit SB);
     KRange (EVar 10) 1 (2 ^ 47 - 24); KAlign (EVar 10) 8;
     KZero (SA (EAlu ALU_SRL (EVar 10) (ELit 3)) SB) (ELit 3);
     KRange (EVar 12) 1 (2 ^ 47 - 24); KAlign (EVar 12) 8;
     KZero (SA (EAlu ALU_SRL (EVar 12) (ELit 3)) SB) (ELit 3);
     KWr (SA (EVar 12) 0) 24;
     KRange (EVar 2) (AS_STKLO + 16) (2^47); KWr (SA (EVar 2) (-16)) 16;
     KRange (EVar 64) 1 (2 ^ 47 - 16);
     KRange (EVar 65) 0 (2^23);
     KRange (EVar 11) 0 (2^23);
     KRange (EVar 66) 0 (2^26);
     KRange (EVar 67) 0 (2^26);     (* [comment removed for export] *)
     KRange (EVar 68) 0 (2^26);
     KRange (EVar 69) 1 (2 ^ 47 - 16);
     KWord (SA (EVar 10) 0) 8 (EVar 64);
     KWord (SA (EVar 10) 20) 4 (EVar 65);
     KDisj (SA (EVar 12) 0) 24 (SA (EVar 69) 132) 12;
     KDisj (SA (EVar 12) 0) 24 (SA (EAlu ALU_ADD (EVar 64) (EVar 67)) 0) 4;
     KShad (EVar 64) (EVar 66) SB;
     KBlobD (SA (EVar 64) 0) (EVar 66) 0].

  Lemma kn0v1_ok : know_ok SEGS E mem kn0v1.
  Proof using ceil FPI regs mem sp P T data tc psz idx len bs Hsp HP Hidx HT12 Hi Hlen Hbs Hdrange Hblob Hshd HPd HPtc Htc Htags Hpal HPrange HshP Hsb Htal HTrange HTst HshT HTD Hsprange Hstk.
    unfold kn0v1. pose proof (u64_range data). pose proof (u64_range T). pose proof (u64_range P). pose proof (u64_range sp).
    destruct Htags as (Htc0 & Hpsz & Hall). destruct (Hall idx Hi) as [Hs4 Hend].
    pose proof (be32_range bs (132 + 12 * idx + 4)) as Ro. pose proof (be32_range bs (132 + 12 * idx + 8)) as Rs.
    destruct Hsb as [Hg Hs]. unfold cell64, cell in Hg, Hs.
    unfold know_ok.
    repeat (apply Forall_cons); [..|apply Forall_nil].
    - eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0x9f920 8 (ELit 0xa79b8) (Z_to_bv 64 0xa79b8)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0xa79b8 8 (ELit SB) (Z_to_bv 64 SB)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
    - apply krange_intro; cbn. rewrite HP. lia.
    - apply kalign_intro; [lia|]. cbn. rewrite HP. exact Hpal.
    - eapply (kzero_shz_intro SEGS E mem (EVar 10) P 3); [cbn; exact HP | exact HshP | lia | lia].
    - apply krange_intro; cbn. rewrite HT12. lia.
    - apply kalign_intro; [lia|]. cbn. rewrite HT12. exact Htal.
    - eapply (kzero_shz_intro SEGS E mem (EVar 12) T 3); [cbn; exact HT12 | exact HshT | lia | lia].
    - apply (kwr_intro SEGS E mem (EVar 12) T 0 24); cbn; try lia. exact HT12. rewrite Z.add_0_r. exact HTst.
    - apply krange_intro; cbn. rewrite Hsp. lia.
    - apply (kwr_intro SEGS E mem (EVar 2) sp (-16) 16); cbn; try lia; auto.
    - apply krange_intro; cbn. lia.
    - apply krange_intro; cbn. rewrite u_small by lia. lia.
    - apply krange_intro; cbn. rewrite Hidx. lia.
    - apply krange_intro; cbn. rewrite u_small by lia. lia.
    - apply krange_intro; cbn. rewrite u_small by lia. lia.
    - apply krange_intro; cbn. rewrite u_small by lia. lia.
    - apply krange_intro; cbn. rewrite u_small by lia. lia.
    - eapply (kword_intro SEGS E mem (EVar 10) P 0 8 (EVar 64) data); cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (EVar 10) P 20 4 (EVar 65) (Z_to_bv 64 tc)); cbn; try lia; auto.
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite HT12, u_small by lia. lia.
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite HT12, alu_add. unfold v_add.
      rewrite (u_small off_i) by lia. rewrite u_small by lia. lia.
    - eapply (kshad_intro SEGS E mem (EVar 64) (EVar 66) data len); [reflexivity | cbn; rewrite u_small by lia; reflexivity | lia | lia | exact Hshd].
    - cbn [kentry_ok]. unfold flat, estart, elenZ. cbn. rewrite u_small by lia.
      split; [lia|]. split; [exact Hbs|]. intros k Hk. rewrite Z.add_0_r. apply Hblob. exact Hk.
  Qed.

  Definition kn0 : list kentry := kn0v1 ++
    [KRange (EAlu ALU_ADD (EVar 64) (EVar 66)) 0 (2 ^ 47 - 16);
     KDisj (SA (EVar 10) 0) 24 ZSH ZSHL; KDisj (SA (EVar 10) 0) 24 ZIMG ZIMGL;
     KDisj (SA (EVar 10) 0) 24 (SA (EVar 2) (-16)) 16;
     KDisj (SA (EVar 12) 0) 24 ZSH ZSHL; KDisj (SA (EVar 12) 0) 24 ZIMG ZIMGL;
     KDisj (SA (EVar 12) 0) 24 (SA (EVar 2) (-16)) 16].
  Lemma kn0_ok : know_ok SEGS E mem kn0.
  Proof using ceil FPI regs mem sp P T data tc psz idx len bs Hsp HP Hidx HT12 Hi Hlen Hbs Hdrange Hblob Hshd HPd HPtc Htc Htags Hpal HPrange HshP Hsb Htal HTrange HTst HshT HTD HPT Hsprange Hstk. apply know_ok_app; [exact kn0v1_ok | kn_place]. Qed.

  (* [comment removed for export] *)
  Definition nu (j : nat) : Z :=
    nth j [bs_byte bs (132 + 12 * idx); bs_byte bs (132 + 12 * idx + 1); bs_byte bs (132 + 12 * idx + 2); bs_byte bs (132 + 12 * idx + 3);
           bs_byte bs (132 + 12 * idx + 4); bs_byte bs (132 + 12 * idx + 4 + 1); bs_byte bs (132 + 12 * idx + 4 + 2); bs_byte bs (132 + 12 * idx + 4 + 3);
           bs_byte bs (132 + 12 * idx + 8); bs_byte bs (132 + 12 * idx + 8 + 1); bs_byte bs (132 + 12 * idx + 8 + 2); bs_byte bs (132 + 12 * idx + 8 + 3)]%Z 0%Z.
  Definition atom (sx : bool) (d : Z) : expr * (bool * nat) :=
    (EBlobX sx 0 (EVar 69) d (EVar 64) 1, (sx, Z.to_nat (d - 132))).
  Definition atoms : list (expr * (bool * nat)) :=
    [atom true 143; atom false 140; atom false 141; atom false 142;
     atom false 137; atom false 138; atom false 136; atom true 139].

  Lemma nu_range : forall k, (0 <= nu k < 256)%Z.
  Proof using idx bs. intros k. unfold nu. do 12 (destruct k as [|k]; [cbn [nth]; apply bs_byte_range|]). destruct k; cbn; lia. Qed.

  Lemma atoms_ok_i : atoms_ok E nu atoms.
  Proof using ceil FPI regs sp P T data tc psz idx len bs Hi Hbs Hdrange Htags HPrange HTrange Hsprange.
    destruct Htags as (Htc0 & Hpsz & Hall).
    unfold atoms, atoms_ok. pose proof (u64_range data).
    repeat (apply Forall_cons); [..|apply Forall_nil];
      unfold atom, atom_ok; cbn [edenot eb ev E blobs_ev nth]; ev_simpl E; rewrite u_small by lia;
      first [rewrite blob_val_u8 by lia | rewrite blob_val_s8 by lia]; unfold nu; cbn [nth Z.to_nat Z.add Pos.to_nat Pos.iter_op Nat.add]; unfold bs_byte;
      (repeat f_equal); lia.
  Qed.

  Ltac frame_here RS :=
    lazymatch goal with
    | EQM : ?M1 = mem_denot _ ?M0 ?log, HLF : log_flat _ _ |- _ =>
      let Hfr := fresh "Hfr" in
      assert (Hfr : frame_mod M0 M1 (regions_denot E RS))
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

  Definition POST (mem' : word -> option byte) : Prop :=
    frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 16), 16%Z); (T, 24%Z)] /\
    tag_ok SEGS mem' data len (bv_unsigned T) /\
    (exists s, cell32 SEGS mem' (bv_unsigned T) s) /\
    (exists ty, cell32 SEGS mem' (bv_unsigned T + 4) ty).

  Lemma getidx_run :
    runs_to SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x818d8) mem rom)
      (fun st' => exists (FPI' : FPState) regs' mem',
          st' = mkst (FP:=FPI') regs' ret mem' rom /\
          regs_kept abi_kept regs regs' /\
          fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI')) /\
          POST mem').
  Proof using ceil FPI regs mem rom ret sp P T data tc psz idx len bs Hra Hret Hsp HP Hidx HT12 Hi Hlen Hbs Hdrange Hblob Hshd HPd HPtc Htc Htags Hpal HPrange HshP Hsb Htal HTrange HTst HshT HTD HPT Hsprange Hstk.
    destruct Htags as (Htc0 & Hpsz & Hall). destruct (Hall idx Hi) as [Hs4 Hend].
    pose proof (be32_range bs (132 + 12 * idx + 4)) as Ro. pose proof (be32_range bs (132 + 12 * idx + 8)) as Rs.
    pose proof (u64_range data) as Rd. pose proof (u64_range T) as RT. pose proof (u64_range P) as RP. pose proof (u64_range sp) as Rsp.
    assert (HR : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [bs])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [bs])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof kn0_ok as HK.
    (* [comment removed for export] *)
    run_fp 100%nat [0x81960%Z] (dirs [false]) true hints keep_all.
    frame_here [(SA (EVar 2) (-16), 16%Z)].
    (* [comment removed for export] *)
    pin_reg HR (10%bv:reg) (EAlu ALU_ADD (EVar 69) (ELit 132)) by
      (rewrite (HR 10%bv); lazymatch goal with |- edenot _ ?e = _ =>
         let l := eval vm_compute in (lin_of e) in
         rewrite (edenot_lin E e); change (lin_of e) with l; cbn [fst snd tden]; unfold uE end;
       cbn [edenot ev E vals_ev]; ev_simpl E; rewrite Hidx; rewrite alu_add_lit, (u_small (bv_unsigned data + 12 * idx)) by lia; f_equal; lia).
    (* [comment removed for export] *)
    run_fp 150%nat [0x81a34%Z] noscr true hints keep_all.
    frame_here [(SA (EVar 12) 0, 24%Z)].
    pin_be32 HR (14%bv:reg) (EVar 68) [11; 10; 9; 8]%nat.
    (* [comment removed for export] *)
    run_fp 150%nat [0x81ab0%Z] noscr true hints keep_all.
    frame_here [(SA (EVar 12) 0, 24%Z)].
    pin_be32 HR (11%bv:reg) (EVar 67) [7; 6; 5; 4]%nat.
    (* [comment removed for export] *)
    run_fp 150%nat (@nil Z) noscr true hints keep_all.
    frame_here [(SA (EVar 12) 0, 24%Z)].
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
    assert (Hrs1 : regions_denot E [(SA (EVar 2) (-16), 16%Z)] = [(Z_to_bv 64 (bv_unsigned sp - 16), 16%Z)]).
    { unfold regions_denot. cbn [map fst snd]. unfold adenot. cbn [a_base a_off edenot]. ev_simpl E.
      rewrite Hsp. unfold v_addi. reflexivity. }
    rewrite Hrs1 in Hfr. rewrite Hrs in Hfr0, Hfr1, Hfr2.
    split.
    { apply (frame_mod_trans _ _ _ [(Z_to_bv 64 (bv_unsigned sp - 16), 16%Z)] [(T, 24%Z)] Hfr).
      eapply frame_mod_trans_same; [exact Hfr0|]. eapply frame_mod_trans_same; [exact Hfr1|]. exact Hfr2. }
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

Theorem getidx_bo_ok : forall ceil, getidx_contract_as SEGS as_both ceil.
Proof.
  intros ceil data len bs P tc psz idx T FPI regs mem rom ret Hra Hret PRE.
  destruct PRE as (HP & Hidx & HT12 & Hi & ((Hlen & Hbs & Hdnz & Hdata & Hblob) & Hdheap & Hdal & Hshd) & HPd & [Htc HPtc] & Htags &
                   Hpal & HPheap & HshP & Htal & HTheap & (HTw0 & _ & HTw24 & HTst) & HshT & HTD & HPT & Hsb & (sp & Hsp & Hfr)).
  unfold cell64, cell in HPd. unfold cell in HPtc.
  apply (as_sb_both SEGS mem) in Hsb.
  destruct Hfr as ([Hst1 Hst2] & Hsal & (_ & _ & _ & Hwr)).
  unfold heapish, stackish in *. app_facts.
  pose proof (u64_range T).
  destruct (getidx_run ceil FPI regs mem rom ret sp P T data tc psz idx len bs Hra Hret Hsp HP
              ltac:(rewrite Hidx; apply u_small; lia) HT12 Hi Hlen Hbs ltac:(plc) Hblob Hshd
              ltac:(rewrite Z.add_0_r; exact HPd) HPtc Htc Htags Hpal ltac:(plc) HshP Hsb Htal ltac:(plc) HTst HshT HTD HPT ltac:(plc) Hwr)
    as (st' & Hms & (FPI' & regs' & mem' & -> & Hk1 & Hk2 & Hpost)).
  exists FPI', regs', mem'. split; [exact Hms|]. split; [exact Hk1|]. split; [exact Hk2|].
  unfold getidx_post_as. rewrite Hsp. exact Hpost.
Qed.
