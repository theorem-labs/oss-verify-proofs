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
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsFuzzContract AsLibShadow AsLibDefs BoBase AsLibFrame AsLibTagsSpec AsLibTagsLib.
Import ListNotations.
Open Scope bv_scope.
Import ASX. Import ASXS.
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

Section TX.
  Variable ceil : Z.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp T X Y Zc data buf : word) (ty sz len : Z) (bs : list byte).

  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis HT : getr regs 10 = T.
  Hypothesis HX : getr regs 11 = X.
  Hypothesis HY : getr regs 12 = Y.
  Hypothesis HZ : getr regs 13 = Zc.
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
  Hypothesis HTsp : (bv_unsigned T + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned T)%Z.
  Hypothesis HXst : store_ok SEGS mem (Z_to_bv 64 (bv_unsigned X)) (Z.to_nat 4) = true.
  Hypothesis HXal : (bv_unsigned X mod 4 = 0)%Z.
  Hypothesis HXrange : (appm (bv_unsigned X) 4 /\ (0 < bv_unsigned X)%Z) /\ (bv_unsigned X + 4 <= ceil)%Z.
  Hypothesis HXsh : shbyte mem (bv_unsigned X) 0.
  Hypothesis HXD : (bv_unsigned data + len <= bv_unsigned X \/ bv_unsigned X + 4 <= bv_unsigned data)%Z.
  Hypothesis HYst : store_ok SEGS mem (Z_to_bv 64 (bv_unsigned Y)) (Z.to_nat 4) = true.
  Hypothesis HYal : (bv_unsigned Y mod 4 = 0)%Z.
  Hypothesis HYrange : (appm (bv_unsigned Y) 4 /\ (0 < bv_unsigned Y)%Z) /\ (bv_unsigned Y + 4 <= ceil)%Z.
  Hypothesis HYsh : shbyte mem (bv_unsigned Y) 0.
  Hypothesis HYD : (bv_unsigned data + len <= bv_unsigned Y \/ bv_unsigned Y + 4 <= bv_unsigned data)%Z.
  Hypothesis HZst : store_ok SEGS mem (Z_to_bv 64 (bv_unsigned Zc)) (Z.to_nat 4) = true.
  Hypothesis HZal : (bv_unsigned Zc mod 4 = 0)%Z.
  Hypothesis HZrange : (appm (bv_unsigned Zc) 4 /\ (0 < bv_unsigned Zc)%Z) /\ (bv_unsigned Zc + 4 <= ceil)%Z.
  Hypothesis HZsh : shbyte mem (bv_unsigned Zc) 0.
  (* [comment removed for export] *)
  Hypothesis Hsprange : ((AS_STKLO <= ceil)%Z /\ (ceil + 16 <= bv_unsigned sp)%Z) /\ (bv_unsigned sp <= 2 ^ 47)%Z.
  Hypothesis Hstk : store_ok SEGS mem (Z_to_bv 64 (bv_unsigned sp - 16)) 16 = true.
  Hypothesis Hsb : sbcell SEGS 0x9f920 0xa79b8 mem.

  Let E : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI))
                                ++ [buf; Z_to_bv 64 ty; Z_to_bv 64 sz; Z_to_bv 64 len; data])) (blobs_ev [bs]).
  (* [comment removed for export] *)

  Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core3 else first [ solve [clear; el_lia_core3] | el_lia_core3 ].   (* [comment removed for export] *)
  Lemma kzero_shbyte_intro : forall (e : expr) (p : word),
    edenot E e = p -> shbyte mem (bv_unsigned p) 0 -> (bv_unsigned p < 2 ^ 47)%Z ->
    kentry_ok SEGS E mem (KZero (SA (EAlu ALU_SRL e (ELit 3)) SB) (ELit 1)).
  Proof using FPI regs mem T X Y Zc data buf ty sz len bs.
    intros e p He Hb Hp. replace SB with (SB + 0)%Z by lia.
    eapply (kzero_shadow_intro SEGS E mem e p 0 1 He); try lia.
    - assert (bv_unsigned p / 8 < 2 ^ 44)%Z by (apply Z.div_lt_upper_bound; lia).
      pose proof (Z.div_pos (bv_unsigned p) 8 ltac:(pose proof (u64_range p); lia) ltac:(lia)). lia.
    - intros j Hj. replace j with 0%Z by lia. rewrite Z.add_0_r. exact Hb.
  Qed.
  Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].

  (* [comment removed for export] *)
  Definition kn0v1 : list kentry :=
    [KWord (SA (ELit 0) 0x9f920) 8 (ELit 0xa79b8); KWord (SA (ELit 0) 0xa79b8) 8 (ELit SB);
     KRange (EVar 10) AS_STKLO (2^47 - 24); KAlign (EVar 10) 8;
     KZero (SA (EAlu ALU_SRL (EVar 10) (ELit 3)) SB) (ELit 3);
     KRange (EVar 11) 1 (2 ^ 47 - 4); KAlign (EVar 11) 4; KZero (SA (EAlu ALU_SRL (EVar 11) (ELit 3)) SB) (ELit 1);
     KRange (EVar 12) 1 (2 ^ 47 - 4); KAlign (EVar 12) 4; KZero (SA (EAlu ALU_SRL (EVar 12) (ELit 3)) SB) (ELit 1);
     KRange (EVar 13) 1 (2 ^ 47 - 4); KAlign (EVar 13) 4; KZero (SA (EAlu ALU_SRL (EVar 13) (ELit 3)) SB) (ELit 1);
     KRange (EVar 2) (AS_STKLO + 16) (2^47); KWr (SA (EVar 2) (-16)) 16;
     KDisj (SA (EVar 10) 0) 24 (SA (EVar 2) (-16)) 16;
     KRange (EVar 64) 1 (2 ^ 47 - 16);
     KRange (EVar 68) 1 (2 ^ 47 - 16);
     KRange (EVar 67) 0 (2^26);
     KRange (EVar 65) 0 (2^32 - 1);
     KWord (SA (EVar 10) 4) 4 (EVar 65);
     KWord (SA (EVar 10) 8) 4 (EVar 66);
     KWord (SA (EVar 10) 16) 8 (EVar 64);
     KWr (SA (EVar 11) 0) 4;
     KWr (SA (EVar 12) 0) 4;
     KWr (SA (EVar 13) 0) 4;
     KShad (EVar 68) (EVar 67) SB;
     KBlobD (SA (EVar 68) 0) (EVar 67) 0].

  Lemma kn0v1_ok : know_ok SEGS E mem kn0v1.
  Proof using ceil FPI regs mem sp T X Y Zc data buf ty sz len bs Hsp HT HX HY HZ Hlen Hbs Hdrange Hblob Hshd Hty Htyr Hsz Hszr Hbuf Hin1 Hin2 Htal HTrange HshT HTsp HXst HXal HXrange HXsh HXD HYst HYal HYrange HYsh HYD HZst HZal HZrange HZsh Hsprange Hstk Hsb.
    unfold kn0v1. pose proof (u64_range data). pose proof (u64_range T). pose proof (u64_range buf).
    pose proof (u64_range X). pose proof (u64_range Y). pose proof (u64_range Zc). pose proof (u64_range sp).
    destruct Hsb as [Hg Hs]. unfold cell64, cell in Hg, Hs.
    unfold know_ok.
    repeat (apply Forall_cons); [..|apply Forall_nil].
    - eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0x9f920 8 (ELit 0xa79b8) (Z_to_bv 64 0xa79b8)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0xa79b8 8 (ELit SB) (Z_to_bv 64 SB)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
    - apply krange_intro; cbn. rewrite HT. lia.
    - apply kalign_intro; [lia|]. cbn. rewrite HT. exact Htal.
    - eapply (kzero_shz_intro SEGS E mem (EVar 10) T 3); [cbn; exact HT | exact HshT | lia | lia].
    - apply krange_intro; cbn. rewrite HX. lia.
    - apply kalign_intro; [lia|]. cbn. rewrite HX. exact HXal.
    - apply (kzero_shbyte_intro (EVar 11) X); [cbn; exact HX | exact HXsh | lia].
    - apply krange_intro; cbn. rewrite HY. lia.
    - apply kalign_intro; [lia|]. cbn. rewrite HY. exact HYal.
    - apply (kzero_shbyte_intro (EVar 12) Y); [cbn; exact HY | exact HYsh | lia].
    - apply krange_intro; cbn. rewrite HZ. lia.
    - apply kalign_intro; [lia|]. cbn. rewrite HZ. exact HZal.
    - apply (kzero_shbyte_intro (EVar 13) Zc); [cbn; exact HZ | exact HZsh | lia].
    - apply krange_intro; cbn. rewrite Hsp. lia.
    - apply (kwr_intro SEGS E mem (EVar 2) sp (-16) 16); cbn; try lia; auto.
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite HT, Hsp. lia.
    - apply krange_intro; cbn. lia.
    - apply krange_intro; cbn. lia.
    - apply krange_intro; cbn. rewrite u_small by lia. lia.
    - apply krange_intro; cbn. rewrite u_small by lia. lia.
    - eapply (kword_intro SEGS E mem (EVar 10) T 4 4 (EVar 65) (Z_to_bv 64 ty)); cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (EVar 10) T 8 4 (EVar 66) (Z_to_bv 64 sz)); cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (EVar 10) T 16 8 (EVar 64) buf); cbn; try lia; auto.
    - apply (kwr_intro SEGS E mem (EVar 11) X 0 4); cbn; try lia. exact HX. rewrite Z.add_0_r. exact HXst.
    - apply (kwr_intro SEGS E mem (EVar 12) Y 0 4); cbn; try lia. exact HY. rewrite Z.add_0_r. exact HYst.
    - apply (kwr_intro SEGS E mem (EVar 13) Zc 0 4); cbn; try lia. exact HZ. rewrite Z.add_0_r. exact HZst.
    - eapply (kshad_intro SEGS E mem (EVar 68) (EVar 67) data len); [reflexivity | cbn; rewrite u_small by lia; reflexivity | lia | lia | exact Hshd].
    - cbn [kentry_ok]. unfold flat, estart, elenZ. cbn. rewrite u_small by lia.
      split; [lia|]. split; [exact Hbs|]. intros k Hk. rewrite Z.add_0_r. apply Hblob. exact Hk.
  Qed.

  Definition kn0 : list kentry := kn0v1 ++
    [KDisj (SA (EVar 11) 0) 4 (SA (EVar 10) 0) 24;
     KDisj (SA (EVar 12) 0) 4 (SA (EVar 10) 0) 24;
     KDisj (SA (EVar 13) 0) 4 (SA (EVar 10) 0) 24;
     KRange (EAlu ALU_ADD (EVar 68) (EVar 67)) 0 (2 ^ 47 - 16);
     KDisj (SA (EVar 11) 0) 4 ZSH ZSHL; KDisj (SA (EVar 11) 0) 4 ZIMG ZIMGL;
     KDisj (SA (EVar 11) 0) 4 (SA (EVar 2) (-16)) 16;
     KDisj (SA (EVar 12) 0) 4 ZSH ZSHL; KDisj (SA (EVar 12) 0) 4 ZIMG ZIMGL;
     KDisj (SA (EVar 12) 0) 4 (SA (EVar 2) (-16)) 16;
     KDisj (SA (EVar 13) 0) 4 ZSH ZSHL; KDisj (SA (EVar 13) 0) 4 ZIMG ZIMGL;
     KDisj (SA (EVar 13) 0) 4 (SA (EVar 2) (-16)) 16].
  Lemma kn0_ok : know_ok SEGS E mem kn0.
  Proof using ceil FPI regs mem sp T X Y Zc data buf ty sz len bs Hsp HT HX HY HZ Hlen Hbs Hdrange Hblob Hshd Hty Htyr Hsz Hszr Hbuf Hin1 Hin2 Htal HTrange HshT HTsp HXst HXal HXrange HXsh HXD HYst HYal HYrange HYsh HYD HZst HZal HZrange HZsh Hsprange Hstk Hsb. apply know_ok_app; [exact kn0v1_ok | kn_place]. Qed.

  (* [comment removed for export] *)
  Definition knA : list kentry :=
    KRange (EVar 66) 20 (2^26) ::
    KDisj (SA (EVar 11) 0) 4 (SA (EVar 64) 8) 12 ::
    KDisj (SA (EVar 12) 0) 4 (SA (EVar 64) 8) 12 :: kn0.
  Definition knB : list kentry := KRange (EVar 66) 0 19 :: kn0.

  Lemma knA_ok : (20 <= sz)%Z -> know_ok SEGS E mem knA.
  Proof using ceil FPI regs mem sp T X Y Zc data buf ty sz len bs Hsp HT HX HY HZ Hlen Hbs Hdrange Hblob Hshd Hty Htyr Hsz Hszr Hbuf Hin1 Hin2 Htal HTrange HshT HTsp HXst HXal HXrange HXsh HXD HYst HYal HYrange HYsh HYD HZst HZal HZrange HZsh Hsprange Hstk Hsb.
    intros Hc. pose proof (u64_range buf).
    apply know_ok_cons; [| apply know_ok_cons; [| apply know_ok_cons; [| apply kn0_ok]]].
    - apply krange_intro; cbn. rewrite u_small by lia. lia.
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite HX. lia.
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite HY. lia.
  Qed.

  Lemma knB_ok : (sz < 20)%Z -> know_ok SEGS E mem knB.
  Proof using ceil FPI regs mem sp T X Y Zc data buf ty sz len bs Hsp HT HX HY HZ Hlen Hbs Hdrange Hblob Hshd Hty Htyr Hsz Hszr Hbuf Hin1 Hin2 Htal HTrange HshT HTsp HXst HXal HXrange HXsh HXD HYst HYal HYrange HYsh HYD HZst HZal HZrange HZsh Hsprange Hstk Hsb.
    intros Hc. apply know_ok_cons; [| apply kn0_ok].
    apply krange_intro; cbn. rewrite u_small by lia. lia.
  Qed.

  Definition RSall : list (word * Z) := [(Z_to_bv 64 (bv_unsigned sp - 16), 16%Z); (X, 4%Z); (Y, 4%Z); (Zc, 4%Z)].

  Definition POST (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
    frame_mod mem mem' RSall /\
    exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1)%Z.

  Definition RS1 : list (saddr * Z) := [(SA (EVar 2) (-16), 16%Z)].
  Definition RS : list (saddr * Z) := [(SA (EVar 2) (-16), 16%Z); (SA (EVar 11) 0, 4%Z); (SA (EVar 12) 0, 4%Z); (SA (EVar 13) 0, 4%Z)].

  Lemma RS1_denot : regions_denot E RS1 = [(Z_to_bv 64 (bv_unsigned sp - 16), 16%Z)].
  Proof using FPI regs sp data buf ty sz len bs Hsp.
    unfold regions_denot, RS1. cbn [map fst snd]. unfold adenot. cbn [a_base a_off edenot]. ev_simpl E.
    rewrite Hsp. unfold v_addi. reflexivity.
  Qed.
  Lemma RS_denot : regions_denot E RS = RSall.
  Proof using FPI regs sp X Y Zc data buf ty sz len bs Hsp HX HY HZ.
    unfold regions_denot, RS, RSall. cbn [map fst snd]. unfold adenot. cbn [a_base a_off edenot]. ev_simpl E.
    rewrite Hsp, HX, HY, HZ. unfold v_addi. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity.
  Qed.

  Lemma frame_RS1_all : forall m1 m2, frame_mod m1 m2 [(Z_to_bv 64 (bv_unsigned sp - 16), 16%Z)] -> frame_mod m1 m2 RSall.
  Proof using ceil rom ret sp T X Y Zc data ty sz len Hlen Hdrange Htyr Hszr HTrange HTsp HXrange HXD HYrange HYD HZrange Hsprange.
    intros m1 m2 H. eapply frame_mod_weaken; [|exact H]. intros a Ha. cbn [outside RSall] in Ha |- *. tauto.
  Qed.

  (* [comment removed for export] *)
  Ltac frame1 :=
    lazymatch goal with
    | EQM : ?M1 = mem_denot _ ?M0 ?log, HLF : log_flat _ _ |- _ =>
      let Hfr := fresh "Hfr" in
      assert (Hfr : frame_mod M0 M1 [(Z_to_bv 64 (bv_unsigned sp - 16), 16%Z)])
        by (rewrite EQM, <- RS1_denot; apply (frame_mod_mem_denot E M0 log RS1 HLF); [flats_auto | vm_compute; reflexivity]);
      clear EQM HLF
    end.

  (* [comment removed for export] *)
  Ltac finish HR0 HF0 :=
    fin_ret;
    lazymatch goal with
    | HR : regs_ok _ ?sr ?R2, HF : fregs_ok _ ?sfr (@fp_regs ?FP2), HK : know_ok _ _ ?M2 _ |- _ =>
      exists FP2, R2, M2;
      split; [regv HR (1%bv:reg); rewrite Hra; reflexivity|];
      split; [exact (regs_same_on E _ _ regs _ abi_kept HR0 HR ltac:(vm_compute; reflexivity))|];
      split; [exact (fregs_same_on E _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity))|];
      unfold POST; split; [| eexists; split; [regv HR (10%bv:reg); reflexivity | lia]]
    end.

  Lemma tagxyz_run :
    runs_to SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x815e0) mem rom)
      (fun st' => exists (FPI' : FPState) regs' mem',
          st' = mkst (FP:=FPI') regs' ret mem' rom /\
          regs_kept abi_kept regs regs' /\
          fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI')) /\
          POST regs' mem').
  Proof using ceil FPI regs mem rom ret sp T X Y Zc data buf ty sz len bs Hra Hret Hsp HT HX HY HZ Hlen Hbs Hdrange Hblob Hshd Hty Htyr Hsz Hszr Hbuf Hin1 Hin2 Htal HTrange HshT HTsp HXst HXal HXrange HXsh HXD HYst HYal HYrange HYsh HYD HZst HZal HZrange HZsh Hsprange Hstk Hsb.
    pose proof (u64_range data) as Rd. pose proof (u64_range T) as RT. pose proof (u64_range buf) as Rb.
    pose proof (u64_range X) as RX. pose proof (u64_range Y) as RY. pose proof (u64_range Zc) as RZ. pose proof (u64_range sp) as Rsp.
    assert (HR : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [bs])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [bs])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    destruct (Z_lt_le_dec sz 20) as [Hc|Hc].
    - (* [comment removed for export] *)
      pose proof (knB_ok Hc) as HK.
      run_fp 40%nat (@nil Z) noscr true hints keep_all. frame1.
      branch_case as Hbr.
      + run_fp 40%nat (@nil Z) noscr false. finish HR0 HF0. apply frame_RS1_all. exact Hfr.
      + run_fp 40%nat (@nil Z) noscr false. finish HR0 HF0. apply frame_RS1_all. exact Hfr.
    - pose proof (knA_ok Hc) as HK.
      run_fp 40%nat (@nil Z) noscr true hints keep_all. frame1.
      branch_case as Hbr.
      + run_fp 40%nat (@nil Z) noscr false. finish HR0 HF0. apply frame_RS1_all. exact Hfr.
      + run_fp 250%nat (@nil Z) noscr true.
        finish HR0 HF0.
        apply (frame_mod_trans_same _ _ _ _ (frame_RS1_all _ _ Hfr)).
        rewrite EQM, <- RS_denot. apply (frame_mod_mem_denot E _ _ RS HLF); [flats_auto | vm_compute; reflexivity].
  Qed.
End TX.

Theorem tagxyz_bo_ok : forall ceil, tagxyz_contract_as SEGS as_both ceil.
Proof.
  intros ceil data len bs T X Y Zc FPI regs mem rom ret Hra Hret PRE.
  destruct PRE as (HT & HX & HY & HZ & ((Hlen & Hbs & Hdnz & Hdata & Hblob) & Hdheap & Hdal & Hshd) & [ty [Htyr Hty]] &
                   (sz & buf & [Hszr Hsz] & Hbuf & Hsz4 & (Hin1 & _ & Hin2)) & Htal & HTstk & HshT &
                   ((_ & _ & HX4 & HXst) & HXal & HXheap & HXsh & HXD) &
                   ((_ & _ & HY4 & HYst) & HYal & HYheap & HYsh & HYD) &
                   ((_ & _ & HZ4 & HZst) & HZal & HZheap & HZsh & HZD) & Hsb & (sp & Hsp & Hfr & HTsp)).
  unfold cell64, cell in Hbuf. unfold cell in Hty, Hsz.
  apply (as_sb_both SEGS mem) in Hsb.
  destruct Hfr as ([Hst1 Hst2] & Hsal & (_ & _ & _ & Hwr)).
  unfold heapish, stackish in *. app_facts.
  destruct (tagxyz_run ceil FPI regs mem rom ret sp T X Y Zc data buf ty sz len bs Hra Hret Hsp HT HX HY HZ
              Hlen Hbs ltac:(plc) Hblob Hshd Hty Htyr Hsz Hszr Hbuf Hin1 Hin2 Htal ltac:(plc) HshT HTsp
              HXst HXal ltac:(plc) HXsh HXD HYst HYal ltac:(plc) HYsh HYD HZst HZal ltac:(plc) HZsh ltac:(plc) Hwr Hsb)
    as (st' & Hms & (FPI' & regs' & mem' & -> & Hk1 & Hk2 & Hpost)).
  exists FPI', regs', mem'. split; [exact Hms|]. split; [exact Hk1|]. split; [exact Hk2|].
  unfold tagxyz_post_as. rewrite Hsp. exact Hpost.
Qed.
