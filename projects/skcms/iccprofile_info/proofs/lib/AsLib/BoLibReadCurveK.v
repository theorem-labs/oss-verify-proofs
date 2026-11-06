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
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs BoBase AsRtSpec AsLibFrame AsLibEnv AsLibFPLib AsLibTagsLib AsLibTagsCall AsLibReadCurveLib AsLibCurveSpec AsLibPlace.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymDriveLZ.
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
#[local] Abbreviation CLASSIFY := 0x80714%Z.

(* [comment removed for export] *)
Definition rc_untouched : list reg := [3; 4; 24; 25; 26; 27]%bv.

Lemma abi_kept_split : forall (regs regs' : bvmap 5 word),
  getr regs' 2 = getr regs 2 -> getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
  getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
  (forall r, In r rc_untouched -> getr regs' r = getr regs r) ->
  regs_kept abi_kept regs regs'.
Proof.
  intros regs regs' H2 H8 H9 H18 H19 H20 H21 H22 H23 HU r Hr. unfold abi_kept in Hr.
  cbn [In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [first [assumption | apply HU; first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)]]|]).
  destruct Hr.
Qed.

(* [comment removed for export] *)
Definition RCQ (regs : bvmap 5 word) (mem rom : word -> option byte) (ret : word) (FPI : FPState)
    (data : word) (len : Z) (bs : list byte) (sp buf C cs : word) (size : Z)
    (st' : machine_state) : Prop :=
  exists (FPI' : FPState) regs' mem',
    st' = mkst (FP:=FPI') regs' ret mem' rom /\
    regs_kept abi_kept regs regs' /\
    fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI')) /\
    rcurve_post_as SEGS data len bs sp buf C cs size regs mem FPI' regs' mem'.

(* [comment removed for export] *)
Definition RSF (sp C cs : word) : list (word * Z) :=
  (Z_to_bv 64 (bv_unsigned sp - 2208), 2208%Z) :: (C, 32%Z)
    :: (if Z.eq_dec (bv_unsigned cs) 0 then [] else [(cs, 4%Z)]).

(* [comment removed for export] *)
Definition zfree (r : word * Z) : Prop :=
  (0 <= snd r)%Z /\ ((bv_unsigned (fst r) + snd r <= 0x10000 \/ 0x5fc000 <= bv_unsigned (fst r))
                     /\ (bv_unsigned (fst r) + snd r <= 0x7fff7000 \/ 0x10007fff8000 <= bv_unsigned (fst r)))%Z.
Definition high_regions (rs : list (word * Z)) : Prop := Forall zfree rs.
Ltac zfree_tac := unfold zfree; cbn [fst snd]; rewrite ?u_small_frame by lia; rewrite ?u_small by lia;
  first [lia | (app_sh; app_img; lia)].

Lemma env_ro_frame_high : forall mem (M : word -> option byte) rs,
  frame_mod mem M rs -> high_regions rs -> env_ro both_abi mem -> env_ro both_abi M.
Proof.
  intros mem M rs Hf Hh Hro lo hi i Hin Hi. cbn in Hin.
  assert (Hhi : (0x10000 <= lo /\ hi <= 0x5fc000)%Z) by (destruct Hin as [E1|[E1|[]]]; injection E1; intros; subst; lia).
  rewrite (byte_frame mem M rs i Hf ltac:(lia)).
  - apply (Hro lo hi i Hin Hi).
  - unfold apart. eapply Forall_impl; [|exact Hh]. intros [b m] [Hm [Hb1 Hb2]]. cbn [fst snd] in *. lia.
Qed.

Lemma sbcell_frame_high : forall mem (M : word -> option byte) rs,
  frame_mod mem M rs -> high_regions rs -> sbcell SEGS 0x9f920 0xa79b8 mem -> sbcell SEGS 0x9f920 0xa79b8 M.
Proof.
  intros mem M rs Hf Hh Hsb. eapply sbcell_frame; [exact Hf | exact Hsb | lia | lia | lia | lia | |];
    unfold apart; (eapply Forall_impl; [|exact Hh]); intros [b m] [Hm [Hb1 Hb2]]; cbn [fst snd] in *; lia.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma shz_frame_high : forall mem (M : word -> option byte) rs a m,
  frame_mod mem M rs -> high_regions rs ->
  shz mem a m -> (0 <= a < 2 ^ 47)%Z -> (0 <= m)%Z -> (a + 8 * m <= 2 ^ 47)%Z -> shz M a m.
Proof.
  intros mem M rs a m Hf Hh Hz Ha Hm Ham. eapply shz_frame; [exact Hf | exact Hz | lia | lia |].
  unfold apart, SB. eapply Forall_impl; [|exact Hh]. intros [b n] [Hn [Hb1 Hb2]]. cbn [fst snd] in *. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma env_cells_frame_high : forall mem (M : word -> option byte) rs,
  frame_mod mem M rs -> high_regions rs -> env_cells SEGS both_abi mem -> env_cells SEGS both_abi M.
Proof.
  intros mem M rs Hf Hh (C64 & C32 & C8 & R64).
  pose proof both_abi_low as (L64 & L32 & L8 & LR & _).
  assert (AP : forall a n, in_env_zone a n -> (0 <= n)%Z -> apart a n rs).
  { intros a n Hz Hn. unfold apart. eapply Forall_impl; [|exact Hh]. intros [b m] [Hm [Hb1 Hb2]]. cbn [fst snd] in *.
    unfold in_env_zone, AS_IMGLO, AS_IMGHI, AS_SIMGLO, AS_SIMGHI in Hz. lia. }
  assert (ZB : forall a n, in_env_zone a n -> (0 <= a)%Z /\ (a + n <= 2 ^ 64)%Z).
  { intros a n Hz. unfold in_env_zone, AS_IMGLO, AS_IMGHI, AS_SIMGLO, AS_SIMGHI in Hz. lia. }
  split; [|split; [|split]].
  - intros a v Hin. pose proof (L64 a v Hin) as Z1. pose proof (ZB _ _ Z1).
    eapply acell_frame; [exact Hf | apply C64; exact Hin | lia | cbn; lia | apply AP; [exact Z1 | lia]].
  - intros a v Hin. pose proof (L32 a v Hin) as Z1. pose proof (ZB _ _ Z1).
    eapply acell_frame; [exact Hf | apply C32; exact Hin | lia | cbn; lia | apply AP; [exact Z1 | lia]].
  - intros a v Hin. pose proof (L8 a v Hin) as Z1. pose proof (ZB _ _ Z1).
    eapply acell_frame; [exact Hf | apply C8; exact Hin | lia | cbn; lia | apply AP; [exact Z1 | lia]].
  - intros a Hin. pose proof (LR a Hin) as Z1. pose proof (ZB _ _ Z1).
    eapply areadable_frame; [exact Hf | apply R64; exact Hin | lia | cbn; lia | apply AP; [exact Z1 | lia]].
Qed.

Lemma env_shb_frame_high : forall mem (M : word -> option byte) rs,
  frame_mod mem M rs -> high_regions rs -> env_shb both_abi mem -> env_shb both_abi M.
Proof.
  intros mem M rs Hf Hh H a v Hin. pose proof both_abi_low as (_ & _ & _ & _ & LS & _). pose proof (LS a v Hin) as Z1.
  unfold in_env_zone, AS_IMGLO, AS_IMGHI, AS_SIMGLO, AS_SIMGHI in Z1.
  rewrite (byte_frame mem M rs a Hf ltac:(lia)); [apply H; exact Hin|].
  unfold apart. eapply Forall_impl; [|exact Hh]. intros [b m] [Hm [Hb1 Hb2]]. cbn [fst snd] in *. lia.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma shdata_frame_high : forall mem (M : word -> option byte) rs d n,
  frame_mod mem M rs -> high_regions rs ->
  shdata mem d n -> (0 <= d)%Z -> (0 <= n)%Z -> (d + n <= 2 ^ 47 - 16)%Z -> shdata M d n.
Proof.
  intros mem M rs d n Hf Hh Hs Hd Hn Hdn. eapply shdata_frame; [exact Hf | exact Hs | lia | lia | lia |].
  unfold apart, SB. eapply Forall_impl; [|exact Hh]. intros [b m] [Hm [Hb1 Hb2]]. cbn [fst snd] in *. lia.
Qed.

Lemma shwz_frame_high : forall mem (M : word -> option byte) rs a n,
  frame_mod mem M rs -> high_regions rs ->
  shwz mem a n -> (0 <= a)%Z -> (0 < n)%Z -> (a + n <= 2 ^ 47 - 64)%Z -> shwz M a n.
Proof.
  intros mem M rs a n Hf Hh Hs Ha Hn Han. eapply shwz_frame; [exact Hf | exact Hs | lia | lia |].
  unfold apart, AS_SB. eapply Forall_impl; [|exact Hh]. intros [b m] [Hm [Hb1 Hb2]]. cbn [fst snd] in *. lia.
Qed.

Lemma shbyte_frame_high : forall mem (M : word -> option byte) rs a v,
  frame_mod mem M rs -> high_regions rs ->
  shbyte mem a v -> (0 <= a)%Z -> (a < 2 ^ 47)%Z -> shbyte M a v.
Proof.
  intros mem M rs a v Hf Hh Hs Ha Ha2. eapply shbyte_frame; [exact Hf | exact Hs | lia |].
  unfold apart, SB. eapply Forall_impl; [|exact Hh]. intros [b m] [Hm [Hb1 Hb2]]. cbn [fst snd] in *. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section TailK.
  Variable ceil : Z.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret data : word) (len : Z) (bs : list byte) (sp buf C cs : word) (size : Z).
  (* [comment removed for export] *)
  Hypothesis Hclassify : classify_contract_as SEGS as_both ceil.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis HWC : writable SEGS mem (bv_unsigned C) 32.
  Hypothesis HCal : (bv_unsigned C mod 8 = 0)%Z.
  Hypothesis HCheap : (appm (bv_unsigned C) 32 /\ (0 < bv_unsigned C)%Z) /\ (bv_unsigned C + 32 <= ceil)%Z.
  Hypothesis HshC : shz mem (bv_unsigned C) 4.
  Hypothesis Hro : env_ro both_abi mem.
  Hypothesis Hsb : sbcell SEGS 0x9f920 0xa79b8 mem.
  Hypothesis Hstk : ((AS_STKLO <= ceil)%Z /\ (ceil + 2208 <= bv_unsigned sp)%Z) /\ (bv_unsigned sp <= 2 ^ 47)%Z.
  Hypothesis Hspal : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis HWS : writable SEGS mem (bv_unsigned sp - 2208) 2208.
  Hypothesis Hcs : (bv_unsigned cs = 0)%Z \/
   (writable SEGS mem (bv_unsigned cs) 4 /\ (bv_unsigned cs mod 4 = 0)%Z /\
    (AS_STKLO <= ceil <= bv_unsigned cs /\ bv_unsigned cs + 4 <= 2 ^ 47)%Z /\
    shbyte mem (bv_unsigned cs) 0 /\ (bv_unsigned sp <= bv_unsigned cs)%Z).
  (* [comment removed for export] *)
  Variables (FPc : FPState) (R : bvmap 5 word) (M : word -> option byte).
  Variables (sp1 g a b cc d e f : word).
  Hypothesis Hsp1 : bv_unsigned sp1 = (bv_unsigned sp - 80)%Z.
  Hypothesis TR2 : getr R 2 = sp1.
  Hypothesis TR10 : getr R 10 = Z_to_bv 64 (bv_unsigned C + 4).
  Hypothesis TRK : forall r, In r rc_untouched -> getr R r = getr regs r.
  Hypothesis HFK : fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPc)).
  Hypothesis HM : frame_mod mem M (RSF sp C cs).
  Hypothesis S72 : cell64 SEGS M (bv_unsigned sp - 8) ret.
  Hypothesis S64 : cell64 SEGS M (bv_unsigned sp - 16) (getr regs 8).
  Hypothesis S56 : cell64 SEGS M (bv_unsigned sp - 24) (getr regs 9).
  Hypothesis S48 : cell64 SEGS M (bv_unsigned sp - 32) (getr regs 18).
  Hypothesis S40 : cell64 SEGS M (bv_unsigned sp - 40) (getr regs 19).
  Hypothesis S32 : cell64 SEGS M (bv_unsigned sp - 48) (getr regs 20).
  Hypothesis S24 : cell64 SEGS M (bv_unsigned sp - 56) (getr regs 21).
  Hypothesis S16 : cell64 SEGS M (bv_unsigned sp - 64) (getr regs 22).
  Hypothesis S8 : cell64 SEGS M (bv_unsigned sp - 72) (getr regs 23).
  Hypothesis C0 : cell SEGS M (bv_unsigned C) 4 (Z_to_bv 64 0).
  Hypothesis C4 : cell SEGS M (bv_unsigned C + 4) 4 g.
  Hypothesis C8 : cell SEGS M (bv_unsigned C + 8) 4 a.
  Hypothesis C12 : cell SEGS M (bv_unsigned C + 12) 4 b.
  Hypothesis C16 : cell SEGS M (bv_unsigned C + 16) 4 cc.
  Hypothesis C20 : cell SEGS M (bv_unsigned C + 20) 4 d.
  Hypothesis C24 : cell SEGS M (bv_unsigned C + 24) 4 e.
  Hypothesis C28 : cell SEGS M (bv_unsigned C + 28) 4 f.
  Hypothesis Hcsv : bv_unsigned cs <> 0%Z -> exists v, cell32 SEGS M (bv_unsigned cs) v.

  Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPc))
                                ++ [ret; getr regs 8; getr regs 9; getr regs 18; getr regs 19;
                                    getr regs 20; getr regs 21; getr regs 22; getr regs 23]))
                     (blobs_ev []).

  Definition knK : list kentry :=
    [KRange (EVar 2) (AS_STKLO + 2128) (2^47 - 80);
     KWord (SA (EVar 2) 72) 8 (EVar 64);
     KWord (SA (EVar 2) 64) 8 (EVar 65);
     KWord (SA (EVar 2) 56) 8 (EVar 66);
     KWord (SA (EVar 2) 48) 8 (EVar 67);
     KWord (SA (EVar 2) 40) 8 (EVar 68);
     KWord (SA (EVar 2) 32) 8 (EVar 69);
     KWord (SA (EVar 2) 24) 8 (EVar 70);
     KWord (SA (EVar 2) 16) 8 (EVar 71);
     KWord (SA (EVar 2) 8) 8 (EVar 72)].

  Lemma knK_ok : know_ok SEGS E M knK.
  Proof using ceil regs mem ret sp C cs HCheap Hstk Hcs FPc R M sp1 Hsp1 TR2 S72 S64 S56 S48 S40 S32 S24 S16 S8.
    unfold knK. pose proof (u64_range sp). pose proof (u64_range C).
    unfold cell64, cell in S72, S64, S56, S48, S40, S32, S24, S16, S8.
    unfold know_ok.
    repeat (apply Forall_cons); [..|apply Forall_nil].
    - apply krange_intro; cbn. rewrite TR2. lia.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 72 8 (EVar 64) ret); cbn; try lia; auto.
      replace (bv_unsigned sp1 + 72)%Z with (bv_unsigned sp - 8)%Z by lia. exact S72.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 64 8 (EVar 65) (getr regs 8)); cbn; try lia; auto.
      replace (bv_unsigned sp1 + 64)%Z with (bv_unsigned sp - 16)%Z by lia. exact S64.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 56 8 (EVar 66) (getr regs 9)); cbn; try lia; auto.
      replace (bv_unsigned sp1 + 56)%Z with (bv_unsigned sp - 24)%Z by lia. exact S56.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 48 8 (EVar 67) (getr regs 18)); cbn; try lia; auto.
      replace (bv_unsigned sp1 + 48)%Z with (bv_unsigned sp - 32)%Z by lia. exact S48.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 40 8 (EVar 68) (getr regs 19)); cbn; try lia; auto.
      replace (bv_unsigned sp1 + 40)%Z with (bv_unsigned sp - 40)%Z by lia. exact S40.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 32 8 (EVar 69) (getr regs 20)); cbn; try lia; auto.
      replace (bv_unsigned sp1 + 32)%Z with (bv_unsigned sp - 48)%Z by lia. exact S32.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 24 8 (EVar 70) (getr regs 21)); cbn; try lia; auto.
      replace (bv_unsigned sp1 + 24)%Z with (bv_unsigned sp - 56)%Z by lia. exact S24.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 16 8 (EVar 71) (getr regs 22)); cbn; try lia; auto.
      replace (bv_unsigned sp1 + 16)%Z with (bv_unsigned sp - 64)%Z by lia. exact S16.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 8 8 (EVar 72) (getr regs 23)); cbn; try lia; auto.
      replace (bv_unsigned sp1 + 8)%Z with (bv_unsigned sp - 72)%Z by lia. exact S8.
  Qed.

  Lemma RSF_high : high_regions (RSF sp C cs).
  Proof using ceil mem sp C cs HCheap Hstk Hcs.
    pose proof (u64_range sp). pose proof (u64_range C). pose proof (u64_range cs).
    unfold high_regions, RSF. destruct (Z.eq_dec (bv_unsigned cs) 0).
    - repeat (apply Forall_cons); [..|apply Forall_nil]; zfree_tac.
    - destruct Hcs as [?|(_ & _ & Hcsr & _)]; [lia|].
      repeat (apply Forall_cons); [..|apply Forall_nil]; zfree_tac.
  Qed.

  Lemma RSF_heaphigh : high_regions (RSF sp C cs).
  Proof using ceil mem sp C cs HCheap Hstk Hcs.
    pose proof (u64_range sp). pose proof (u64_range C). pose proof (u64_range cs).
    unfold RSF. destruct (Z.eq_dec (bv_unsigned cs) 0).
    - repeat (apply Forall_cons); [..|apply Forall_nil]; zfree_tac.
    - destruct Hcs as [?|(_ & _ & Hcsr & _)]; [lia|].
      repeat (apply Forall_cons); [..|apply Forall_nil]; zfree_tac.
  Qed.

  Lemma M_rodata : env_ro both_abi M.
  Proof using ceil mem sp C cs HCheap Hro Hstk Hcs M HM. eapply env_ro_frame_high; [exact HM | apply RSF_high | exact Hro]. Qed.

  Lemma M_sb : sbcell SEGS 0x9f920 0xa79b8 M.
  Proof using ceil mem sp C cs HCheap Hsb Hstk Hcs M HM. eapply sbcell_frame_high; [exact HM | apply RSF_high | exact Hsb]. Qed.

  Lemma M_shC : shz M (bv_unsigned C) 4.
  Proof using ceil mem sp C cs HCheap HshC Hstk Hcs M HM. pose proof (u64_range C). eapply shz_frame_high; [exact HM | apply RSF_heaphigh | exact HshC | lia | lia | lia]. Qed.

  Lemma M_writable_stk : writable SEGS M (bv_unsigned sp1 - 16) 16.
  Proof using ceil mem sp C cs HCheap Hstk HWS M sp1 Hsp1 HM.
    pose proof (u64_range sp).
    eapply writable_sub; [eapply writable_frame; [exact HM | exact HWS] | lia | lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma after_classify : forall M', frame_mod M M' [(Z_to_bv 64 (bv_unsigned sp1 - 16), 16%Z)] ->
    frame_mod mem M' (RSF sp C cs) /\
    curve_ok SEGS M' data len (bv_unsigned C) /\
    (bv_unsigned cs <> 0%Z -> exists v, cell32 SEGS M' (bv_unsigned cs) v).
  Proof using ceil mem data len sp C cs HWC HCheap Hstk HWS Hcs M sp1 a b cc d Hsp1 HM C0 C8 C12 C16 C20 Hcsv.
    intros M' Hf. pose proof (u64_range sp). pose proof (u64_range C). pose proof (u64_range cs).
    destruct HWS as (W1 & W2 & W3 & W4). destruct HWC as (V1 & V2 & V3 & V4).
    split; [|split].
    - eapply frame_mod_trans_same; [exact HM|]. eapply frame_mod_of_covered; [|exact Hf].
      unfold RSF. solve_covered.
    - apply (curve_ok_zero4 SEGS M' data len (bv_unsigned C) a b cc d); try lia;
        (eapply cell_frame; [exact Hf | eassumption | lia | cbn; lia | cbn; solve_apart]).
    - intros Hnz. destruct (Hcsv Hnz) as [v Hv]. exists v.
      destruct Hcs as [Hc0 | (HWcs & _ & Hcsr & _ & Hcs3)]; [lia|]. destruct HWcs as (X1 & X2 & X3 & X4).
      eapply cell32_frame; [exact Hf | exact Hv | lia | lia | solve_apart].
  Qed.

  Lemma tailK_ok :
    runs_to SEGS (mkst (FP:=FPc) R (Z_to_bv 64 0x8365c) M rom)
            (RCQ regs mem rom ret FPI data len bs sp buf C cs size).
  Proof using ceil FPI regs mem rom ret data len bs sp buf C cs size Hclassify Hret Hsp HWC HCal HCheap HshC Hro Hsb Hstk Hspal HWS Hcs FPc R M sp1 g a b cc d e f Hsp1 TR2 TR10 TRK HFK HM S72 S64 S56 S48 S40 S32 S24 S16 S8 C0 C4 C8 C12 C16 C20 C24 C28 Hcsv.
    pose proof (u64_range sp) as Rsp. pose proof (u64_range C) as RC. pose proof (u64_range cs) as Rcs.
    pose proof HWS as (W1 & W2 & W3 & W4). pose proof HWC as (V1 & V2 & V3 & V4).
    assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof knK_ok as HK.
    run_fp 20%nat [CLASSIFY] noscr false.
    (* [comment removed for export] *)
    lazymatch goal with
    | HR : regs_ok _ _ ?Rx |- runs_to _ (@mkst ?I ?Rx _ ?Mx ?ro) _ =>
        eapply rt_call;
        [ eapply (Hclassify sp1 C I Rx Mx ro (Z_to_bv 64 0x83668));
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by lia; reflexivity
          | ]
        | ]
    end.
    { unfold classify_pre_as, CLASSIFY_D. cbv zeta.
      split; [regv HR (2%bv:reg); exact TR2|].
      split; [regv HR (10%bv:reg); exact TR10|].
      split; [regv HR (11%bv:reg); reflexivity|].
      split; [regv HR (12%bv:reg); reflexivity|].
      split.
      { exists g, a, b, cc, d, e, f. repeat split; assumption. }
      split; [exact HCal|].
      split; [unfold heapish; plc|].
      split; [apply M_shC|].
      split; [apply M_rodata|].
      split; [apply (as_sb_both SEGS M); apply M_sb|].
      unfold as_frame, stackish. split; [lia|]. split; [|apply M_writable_stk].
      rewrite Hsp1. apply (mod_sub_multiple (bv_unsigned sp) 80 16); [lia | exact Hspal | reflexivity]. }
    cbv beta. intros FQ rq mq (Hkeep & Hfkeep & Hfr). unfold classify_post_as, CLASSIFY_D in Hfr.
    unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
    after_call Hkeep Hfkeep FQ. clear Hkeep Hfkeep.
    know_frame HK Hfr [(SA (EVar 2) (-16), 16%Z)];
      [rewrite TR2; unfold v_addi; repeat f_equal; lia|].
    destruct (after_classify mq Hfr) as (Hfr' & Hcurve & Hcsv'). clear Hfr.
    (* [comment removed for export] *)
    run_fp 40%nat (@nil Z) noscr false.
    fin_ret.
    lazymatch goal with
    | HR : regs_ok _ ?sr ?R2, HF : fregs_ok _ ?sfr (@fp_regs ?FP2) |- _ =>
      exists FP2, R2, mq;
      split; [regv HR (1%bv:reg); reflexivity|];
      lift_hyp HR0; lift_hyp HF0;
      split; [ apply abi_kept_split;
               [ regv_lin HR (2%bv:reg); rewrite TR2, Hsp; apply bv_eq; rewrite u_small by lia; lia
               | regv HR (8%bv:reg); reflexivity
               | regv HR (9%bv:reg); reflexivity
               | regv HR (18%bv:reg); reflexivity
               | regv HR (19%bv:reg); reflexivity
               | regv HR (20%bv:reg); reflexivity
               | regv HR (21%bv:reg); reflexivity
               | regv HR (22%bv:reg); reflexivity
               | regv HR (23%bv:reg); reflexivity
               | intros r Hr; rewrite <- (TRK r Hr); revert r Hr;
                 eapply (regs_same_on _ _ _ R R2 rc_untouched); [exact HR0 | exact HR | vm_compute; reflexivity] ] |];
      split; [ eapply fregs_kept_trans; [exact HFK|]; unfold fregs_kept;
               eapply (fregs_same_on _ _ _ _ _ abi_fkept); [exact HF0 | exact HF | vm_compute; reflexivity] |]
    end.
    unfold rcurve_post_as, RCURVE_D. cbv zeta.
    split; [exact Hfr'|].
    regv HR (10%bv:reg).
    rewrite alu_sltu. unfold v_sltu.
    match goal with |- exists r, (if ?cnd then _ else _) = _ /\ _ => destruct cnd end.
    - exists 1%Z. split; [reflexivity|]. split; [right; reflexivity|].
      split; [intros _; exact Hcurve|]. split; [intros _; exact Hcurve|]. intros Hnz _. exact (Hcsv' Hnz).
    - exists 0%Z. split; [reflexivity|]. split; [left; reflexivity|].
      split; [intros; lia|]. split; [intros _; exact Hcurve|]. intros Hnz Habs. lia.
  Qed.
End TailK.
