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
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs LibTagsSpec.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs BoBase AsLibTagsLib AsLibKit BoLibSpec AsLibPlace.
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

#[local] Abbreviation SEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation CICP := 0x63696370%Z.

(* [comment removed for export] *)
Lemma sx4_small : forall z, (0 <= z < 2 ^ 31)%Z -> bv_unsigned (ext_val true 0 4 (Z_to_bv 64 z)) = z.
Proof.
  intros z Hz. unfold ext_val, ext_Z. rewrite !Z_to_bv_unsigned. unfold bv_swrap, bv_wrap.
  change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z.
  change (bv_half_modulus (8 * N.of_nat 4)) with (2 ^ 31)%Z. change (bv_modulus (8 * N.of_nat 4)) with (2 ^ 32)%Z.
  change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite Z.div_1_r. rewrite (Z.mod_small z (2 ^ 64)) by lia. rewrite (Z.mod_small z (2 ^ 32)) by lia.
  rewrite (Z.mod_small (z + 2 ^ 31) (2 ^ 32)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma sx4_big : forall z, (2 ^ 31 <= z < 2 ^ 32)%Z -> bv_unsigned (ext_val true 0 4 (Z_to_bv 64 z)) = (z - 2 ^ 32 + 2 ^ 64)%Z.
Proof.
  intros z Hz. unfold ext_val, ext_Z. rewrite !Z_to_bv_unsigned. unfold bv_swrap, bv_wrap.
  change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z.
  change (bv_half_modulus (8 * N.of_nat 4)) with (2 ^ 31)%Z. change (bv_modulus (8 * N.of_nat 4)) with (2 ^ 32)%Z.
  change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite Z.div_1_r. rewrite (Z.mod_small z (2 ^ 64)) by lia. rewrite (Z.mod_small z (2 ^ 32)) by lia.
  replace (z + 2 ^ 31)%Z with ((z - 2 ^ 31) + 1 * 2 ^ 32)%Z by lia. rewrite Z_mod_plus_full.
  rewrite (Z.mod_small (z - 2 ^ 31) (2 ^ 32)) by lia.
  replace (z - 2 ^ 31 - 2 ^ 31)%Z with ((z - 2 ^ 32 + 2 ^ 64) + (-1) * 2 ^ 64)%Z by lia. rewrite Z_mod_plus_full.
  apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma ext_Z_sx4_small : forall z, (0 <= z < 2 ^ 31)%Z -> ext_Z true 0 4 z = z.
Proof.
  intros z Hz. unfold ext_Z. unfold bv_swrap, bv_wrap.
  change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z.
  change (bv_half_modulus (8 * N.of_nat 4)) with (2 ^ 31)%Z. change (bv_modulus (8 * N.of_nat 4)) with (2 ^ 32)%Z.
  rewrite Z.div_1_r. rewrite (Z.mod_small z (2 ^ 32)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma ext_Z_sx4_big : forall z, (2 ^ 31 <= z < 2 ^ 32)%Z -> ext_Z true 0 4 z = (z - 2 ^ 32)%Z.
Proof.
  intros z Hz. unfold ext_Z. unfold bv_swrap, bv_wrap.
  change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z.
  change (bv_half_modulus (8 * N.of_nat 4)) with (2 ^ 31)%Z. change (bv_modulus (8 * N.of_nat 4)) with (2 ^ 32)%Z.
  rewrite Z.div_1_r. rewrite (Z.mod_small z (2 ^ 32)) by lia.
  replace (z + 2 ^ 31)%Z with ((z - 2 ^ 31) + 1 * 2 ^ 32)%Z by lia. rewrite Z_mod_plus_full.
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma mod_neg64 : forall x, (- 2 ^ 64 <= x < 0)%Z -> (x mod 2 ^ 64 = x + 2 ^ 64)%Z.
Proof. intros x Hx. replace x with ((x + 2 ^ 64) + (-1) * 2 ^ 64)%Z at 1 by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
Ltac bool_lia :=
  repeat match goal with
         | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
         | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
         | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b)
         end; cbn [negb]; first [reflexivity | lia | congruence].
Ltac sx4_tac :=
  rewrite ?u_small by lia;
  first [ rewrite !ext_Z_sx4_small by lia | rewrite !ext_Z_sx4_big by lia | rewrite !sx4_small by lia | rewrite !sx4_big by lia | idtac ];
  rewrite ?mod_neg64 by lia; rewrite ?Z.mod_small by lia; bool_lia.

Section CI.
  Variable ceil : Z.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp T C data buf : word) (ty sz len : Z) (bs : list byte).

  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis HT : getr regs 10 = T.
  Hypothesis HC : getr regs 11 = C.
  Hypothesis Hlen : (0 <= len < 2 ^ 26)%Z.
  Hypothesis Hbs : Z.of_nat (length bs) = len.
  Hypothesis Hdrange : (appm (bv_unsigned data) len /\ (0 < bv_unsigned data)%Z) /\ (bv_unsigned data + len <= ceil)%Z.
  Hypothesis Hblob : forall k, (0 <= k < len)%Z ->
      mem (Z_to_bv 64 (bv_unsigned data + k)) = Some (nth (Z.to_nat k) bs (Z_to_bv 8 0)).
  Hypothesis Hshd : shdata mem (bv_unsigned data) len.
  Hypothesis Hty : rdn SEGS mem (Z_to_bv 64 (bv_unsigned T + 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 ty)).
  Hypothesis Htyr : (0 <= ty < 2 ^ 32)%Z.
  Hypothesis Hsz : rdn SEGS mem (Z_to_bv 64 (bv_unsigned T + 8)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 sz)).
  Hypothesis Hszr : (0 <= sz < 2 ^ 32)%Z.
  Hypothesis Hbuf : rdn SEGS mem (Z_to_bv 64 (bv_unsigned T + 16)) 8 = Some (word_to_le_bytes 8 buf).
  Hypothesis Hin1 : (bv_unsigned data <= bv_unsigned buf)%Z.
  Hypothesis Hin2 : (bv_unsigned buf + sz <= bv_unsigned data + len)%Z.
  Hypothesis Htal : (bv_unsigned T mod 8 = 0)%Z.
  Hypothesis HTrange : (ceil <= bv_unsigned T)%Z /\ (bv_unsigned T + 24 <= 2 ^ 47)%Z.
  Hypothesis HshT : shz mem (bv_unsigned T) 3.
  Hypothesis HTsp : (bv_unsigned sp <= bv_unsigned T)%Z.
  Hypothesis HCst : store_ok SEGS mem (Z_to_bv 64 (bv_unsigned C)) (Z.to_nat 4) = true.
  Hypothesis HCal : (bv_unsigned C mod 8 = 0)%Z.
  Hypothesis HCrange : (appm (bv_unsigned C) 8 /\ (0 < bv_unsigned C)%Z) /\ (bv_unsigned C + 8 <= ceil)%Z.
  Hypothesis HshC : shz mem (bv_unsigned C) 1.
  Hypothesis HCD : (bv_unsigned data + len <= bv_unsigned C \/ bv_unsigned C + 4 <= bv_unsigned data)%Z.
  Hypothesis Hsprange : ((AS_STKLO <= ceil)%Z /\ (ceil + 16 <= bv_unsigned sp)%Z) /\ (bv_unsigned sp <= 2 ^ 47)%Z.
  Hypothesis Hstk : store_ok SEGS mem (Z_to_bv 64 (bv_unsigned sp - 16)) 16 = true.
  Hypothesis Hsb : sbcell SEGS 0x9f920 0xa79b8 mem.

  Let E : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI))
                                ++ [buf; Z_to_bv 64 ty; Z_to_bv 64 sz; Z_to_bv 64 len; data])) (blobs_ev [bs]).
  (* [comment removed for export] *)

  Definition kn0 (te : expr) : list kentry :=
    [KWord (SA (ELit 0) 0x9f920) 8 (ELit 0xa79b8); KWord (SA (ELit 0) 0xa79b8) 8 (ELit SB);
     KAlign (EVar 10) 8; KRange (EVar 10) AS_STKLO (2 ^ 47 - 24);
     KWord (SA (EVar 10) 4) 4 te; KWord (SA (EVar 10) 8) 4 (EVar 66); KWord (SA (EVar 10) 16) 8 (EVar 64);
     KZero (SA (EAlu ALU_SRL (EVar 10) (ELit 3)) SB) (ELit 3);
     KRange (EVar 2) (AS_STKLO + 16) (2 ^ 47); KWr (SA (EVar 2) (-16)) 16;
     KDisj (SA (EVar 10) 0) 24 (SA (EVar 2) (-16)) 16;
     KAlign (EVar 11) 8; KRange (EVar 11) 1 (2 ^ 47 - 8); KWr (SA (EVar 11) 0) 4;
     KZero (SA (EAlu ALU_SRL (EVar 11) (ELit 3)) SB) (ELit 1);
     KRange (EVar 64) 1 (2 ^ 47 - 16); KRange (EVar 68) 1 (2 ^ 47 - 16); KRange (EVar 67) 0 (2 ^ 26);
     KShad (EVar 68) (EVar 67) SB;
     KBlobD (SA (EVar 68) 0) (EVar 67) 0].

  Lemma kn0_ok : forall te, edenot E te = Z_to_bv 64 ty -> know_ok SEGS E mem (kn0 te).
  Proof using ceil FPI regs mem rom sp T C data buf ty sz len bs Hsp HT HC Hlen Hbs Hdrange Hblob Hshd Hty Htyr Hsz Hszr Hbuf Hin1 Hin2 Htal HTrange HshT HTsp HCst HCal HCrange HshC HCD Hsprange Hstk Hsb.
    intros te Hte. unfold kn0. pose proof (u64_range data). pose proof (u64_range T). pose proof (u64_range buf). pose proof (u64_range C). pose proof (u64_range sp).
    destruct Hsb as [Hg Hs]. unfold cell64, cell in Hg, Hs.
    unfold know_ok. repeat lazymatch goal with |- Forall _ (_ :: _) => constructor | |- Forall _ [] => constructor end.
    all: lazymatch goal with |- Forall _ _ => fail | _ => idtac end.
    - eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0x9f920 8 (ELit 0xa79b8) (Z_to_bv 64 0xa79b8)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0xa79b8 8 (ELit SB) (Z_to_bv 64 SB)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
    - apply kalign_intro; [lia|]. cbn. rewrite HT. exact Htal.
    - apply krange_intro. cbn. rewrite HT. lia.
    - eapply (kword_intro SEGS E mem (EVar 10) T 4 4 te (Z_to_bv 64 ty)); [cbn; exact HT | exact Hte | lia | lia | lia | cbn; lia | exact Hty].
    - eapply (kword_intro SEGS E mem (EVar 10) T 8 4 (EVar 66) (Z_to_bv 64 sz)); cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (EVar 10) T 16 8 (EVar 64) buf); cbn; try lia; auto.
    - eapply (kzero_shz_intro SEGS E mem (EVar 10) T 3); [cbn; exact HT | exact HshT | lia | lia].
    - apply krange_intro. cbn. rewrite Hsp. lia.
    - apply (kwr_intro SEGS E mem (EVar 2) sp (-16) 16); cbn; try lia; auto.
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite HT, Hsp. lia.
    - apply kalign_intro; [lia|]. cbn. rewrite HC. exact HCal.
    - apply krange_intro. cbn. rewrite HC. lia.
    - apply (kwr_intro SEGS E mem (EVar 11) C 0 4); cbn; try lia. exact HC. rewrite Z.add_0_r. exact HCst.
    - eapply (kzero_shz_intro SEGS E mem (EVar 11) C 1); [cbn; exact HC | exact HshC | lia | lia].
    - apply krange_intro. cbn. lia.
    - apply krange_intro. cbn. lia.
    - apply krange_intro. cbn. rewrite u_small by lia. lia.
    - eapply (kshad_intro SEGS E mem (EVar 68) (EVar 67) data len); [reflexivity | cbn; rewrite u_small by lia; reflexivity | lia | lia | exact Hshd].
    - cbn [kentry_ok]. unfold flat, estart, elenZ. cbn. rewrite u_small by lia.
      split; [lia|]. split; [exact Hbs|]. intros k Hk. rewrite Z.add_0_r. apply Hblob. exact Hk.
  Qed.

  (* [comment removed for export] *)
  Definition knA (te : expr) : list kentry := KRange (EVar 66) 12 (2 ^ 32 - 1) :: KDisj (SA (EVar 11) 0) 4 (SA (EVar 64) 8) 4 :: kn0 te.
  Definition knB (te : expr) : list kentry := KRange (EVar 66) 0 11 :: kn0 te.
  Lemma knA_ok : forall te, edenot E te = Z_to_bv 64 ty -> (12 <= sz)%Z -> know_ok SEGS E mem (knA te).
  Proof using ceil FPI regs mem rom sp T C data buf ty sz len bs Hsp HT HC Hlen Hbs Hdrange Hblob Hshd Hty Htyr Hsz Hszr Hbuf Hin1 Hin2 Htal HTrange HshT HTsp HCst HCal HCrange HshC HCD Hsprange Hstk Hsb. intros te Hte Hc. pose proof (u64_range buf). apply know_ok_cons; [| apply know_ok_cons; [| apply (kn0_ok te Hte)]].
    - apply krange_intro; cbn. rewrite u_small by lia. lia.
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite HC. lia.
  Qed.
  Lemma knB_ok : forall te, edenot E te = Z_to_bv 64 ty -> (sz < 12)%Z -> know_ok SEGS E mem (knB te).
  Proof using ceil FPI regs mem rom sp T C data buf ty sz len bs Hsp HT HC Hlen Hbs Hdrange Hblob Hshd Hty Htyr Hsz Hszr Hbuf Hin1 Hin2 Htal HTrange HshT HTsp HCst HCal HCrange HshC HCD Hsprange Hstk Hsb. intros te Hte Hc. apply know_ok_cons; [| apply (kn0_ok te Hte)]. apply krange_intro; cbn. rewrite u_small by lia. lia. Qed.

  Definition POST (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
    frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 16), 16%Z); (C, 4%Z)] /\
    exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1)%Z.

  Definition RS : list (saddr * Z) := [(SA (EVar 2) (-16), 16%Z); (SA (EVar 11) 0, 4%Z)].
  Lemma RS_denot : regions_denot E RS = [(Z_to_bv 64 (bv_unsigned sp - 16), 16%Z); (C, 4%Z)].
  Proof using FPI regs sp C data buf ty sz len bs Hsp HC.
    unfold regions_denot, RS. cbn [map fst snd]. unfold adenot. cbn [a_base a_off edenot]. ev_simpl E.
    rewrite HC, Hsp. unfold v_addi. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity.
  Qed.

  Ltac subst_triv := repeat match goal with H : ?a = ?b |- _ => is_var a; is_var b; subst a end.
  Ltac finish HR0 HF0 :=
    fin_ret;
    lazymatch goal with
    | HR : regs_ok _ ?sr ?R2, HF : fregs_ok _ ?sfr (@fp_regs ?FP2), HK : know_ok _ _ ?M2 _, EQM : ?M2 = mem_denot _ ?M0 ?log |- _ =>
      exists FP2, R2, M2;
      split; [regv HR (1%bv:reg); rewrite Hra; reflexivity|];
      split; [exact (regs_same_on E _ _ regs _ abi_kept HR0 HR ltac:(vm_compute; reflexivity))|];
      split; [exact (fregs_same_on E _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity))|];
      unfold POST; split;
      [ rewrite EQM, <- RS_denot; apply (frame_mod_mem_denot E M0 log RS); [assumption | flats_auto | vm_compute; reflexivity]
      | eexists; split; [regv HR (10%bv:reg); reflexivity | lia]]
    end.

  (* [comment removed for export] *)
  Ltac sig_case :=
    let Hbr := fresh "Hbr" in
    branch_case as Hbr;
    [ (* [comment removed for export] *)
      idtac | idtac ].

  Lemma cicp_run :
    runs_to SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x87228) mem rom)
      (fun st' => exists (FPI' : FPState) regs' mem',
          st' = mkst (FP:=FPI') regs' ret mem' rom /\
          regs_kept abi_kept regs regs' /\
          fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI')) /\
          POST regs' mem').
  Proof using ceil FPI regs mem rom ret sp T C data buf ty sz len bs Hra Hret Hsp HT HC Hlen Hbs Hdrange Hblob Hshd Hty Htyr Hsz Hszr Hbuf Hin1 Hin2 Htal HTrange HshT HTsp HCst HCal HCrange HshC HCD Hsprange Hstk Hsb.
    pose proof (u64_range data) as Rd. pose proof (u64_range T) as RT. pose proof (u64_range buf) as Rb.
    pose proof (u64_range C) as RC. pose proof (u64_range sp) as Rsp.
    assert (HR : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [bs])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [bs])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    assert (Hte : edenot E (EVar 65) = Z_to_bv 64 ty) by (cbn; reflexivity).
    destruct (Z.eq_dec ty CICP) as [Hsig | Hsig].
    - (* [comment removed for export] *)
      assert (Htl : edenot E (ELit CICP) = Z_to_bv 64 ty) by (cbn; rewrite Hsig; reflexivity).
      destruct (Z_lt_le_dec sz 12) as [Hc|Hc].
      + pose proof (knB_ok (ELit CICP) Htl Hc) as HK. unfold knB, kn0 in HK.
        run_fp 80%nat (@nil Z) (dirs [false]) true by sx4_tac.
        finish HR0 HF0.
      + pose proof (knA_ok (ELit CICP) Htl Hc) as HK. unfold knA, kn0 in HK.
        destruct (Z_lt_le_dec sz (2 ^ 31)) as [Hs|Hs];
          run_fp 150%nat (@nil Z) (dirs [true]) true by sx4_tac; finish HR0 HF0.
    - (* [comment removed for export] *)
      pose proof (kn0_ok (EVar 65) Hte) as HK. unfold kn0 in HK.
      destruct (Z_lt_le_dec ty (2 ^ 31)) as [Hs|Hs];
        run_fp 80%nat (@nil Z) (dirs [true]) true by sx4_tac; finish HR0 HF0.
  Qed.
End CI.

Theorem cicp_bo_ok : forall ceil, cicp_contract_bo SEGS as_both ceil.
Proof.
  intros ceil data len bs sp T C FPI regs mem rom ret Hra Hret PRE.
  destruct PRE as (Hsp & HT & HC & ((Hlen & Hbs & Hdnz & Hdata & Hblob) & Hdheap & Hdal & Hshd) & [ty [Htyr Hty]] &
                   (sz & buf & [Hszr Hsz] & Hbuf & Hsz4 & (Hin1 & _ & Hin2)) & Htal & HTstk & HshT & HTsp &
                   (_ & _ & _ & HCst) & HCal & HCheap & HshC & HCD & Hsb & Hfr).
  apply (as_sb_both SEGS mem) in Hsb.
  destruct Hfr as ([Hst1 Hst2] & Hsal & (_ & _ & _ & Hwr)).
  unfold cell64, cell in Hbuf. unfold cell in Hty, Hsz.
  unfold heapish, stackish in *. app_facts.
  destruct (cicp_run ceil FPI regs mem rom ret sp T C data buf ty sz len bs Hra Hret Hsp HT HC
              Hlen Hbs ltac:(plc) Hblob Hshd Hty Htyr Hsz Hszr Hbuf Hin1 Hin2 Htal ltac:(plc) HshT HTsp
              HCst HCal ltac:(plc) HshC HCD ltac:(plc) Hwr Hsb)
    as (st' & Hms & (FPI' & regs' & mem' & -> & Hk1 & Hk2 & Hpost)).
  exists FPI', regs', mem'. split; [exact Hms|]. split; [exact Hk1|]. split; [exact Hk2|]. exact Hpost.
Qed.
