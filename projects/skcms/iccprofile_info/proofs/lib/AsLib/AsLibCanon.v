(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Import Asan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs LibFPSpec LibFrame.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs AsRtSpec AsLibFPSpec AsLibTagsLib AsLibFPLib AsLibFrame AsLibEnv AsLibPlace.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymDriveLZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import ASX. Import ASXS.
(* [comment removed for export] *)
Ltac disj_rel H := match type of H with context [?v] => is_var v; match goal with |- context [v] => idtac end end.
Ltac rlia := first [ (repeat match goal with H : _ \/ _ |- _ => tryif disj_rel H then fail else clear H end); dlia | dlia ].


#[local] Abbreviation SEGS := Asan.M.loaded_segments.
#[local] Abbreviation TP := 0x5d9b70%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma mod32_16 : forall u k, (u mod 32 = 0)%Z -> (k mod 16 = 0)%Z -> ((u + k) mod 16 = 0)%Z.
Proof. intros u k Hu Hk. rlia. Qed.

(* [comment removed for export] *)
Lemma realign_facts : forall sp : word, (bv_unsigned sp mod 16 = 0)%Z -> (144 <= bv_unsigned sp)%Z ->
  let s1 := bv_unsigned (alu64 ALU_AND (alu64 ALU_ADD sp (Z_to_bv 64 (-128))) (Z_to_bv 64 (-32))) in
  (s1 mod 32 = 0)%Z /\ (bv_unsigned sp - 144 <= s1 <= bv_unsigned sp - 128)%Z.
Proof.
  intros sp Hal Hge. cbv zeta. pose proof (u64_range sp).
  rewrite u_and64, u_add64, !u_lit64. unfold two64.
  change ((-32) mod 2 ^ 64)%Z with (2 ^ 64 - 2 ^ 5)%Z.
  rewrite land_highmask by rlia. rlia.
Qed.

Ltac Zify.zify_post_hook ::= idtac.
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

Section Proof.
  Variable ceil : Z.
  Hypothesis Hfit : fit_linear_contract_as SEGS as_asan ceil.
  Hypothesis Hsm : stkmalloc0_contract SEGS as_asan ceil.
  Hypothesis Hmemset : imemset20_contract SEGS as_asan ceil.

  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp C data t8 t16 h : word) (n len fs : Z) (bs : list byte) (ch : chain).

  Let S1w : word := alu64 ALU_AND (alu64 ALU_ADD sp (Z_to_bv 64 (-128))) (Z_to_bv 64 (-32)).
  Let S1 : Z := bv_unsigned S1w.
  Let F : Z := frame0 fs (pos0 h).                      (* [comment removed for export] *)
  Let fa : Z := (fs + FS_FLAGS0 + pos0 h)%Z.             (* [comment removed for export] *)
  Let h1 : word := Z_to_bv 64 (bv_unsigned h + 1).
  Let Ff : Z := frame0 fs (pos0 h1).                    (* [comment removed for export] *)
  Let faf : Z := (fs + FS_FLAGS0 + pos0 h1)%Z.

  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis Htp : getr regs 4 = Z_to_bv 64 TP.
  Hypothesis Hc : getr regs 10 = C.
  Hypothesis Hal16 : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis Hstk : stackish ceil (bv_unsigned sp - CANON_D) CANON_D.
  Hypothesis Hwst : writable SEGS mem (bv_unsigned sp - CANON_D) CANON_D.
  Hypothesis Hshs : shz mem (bv_unsigned sp - CANON_D) (CANON_D / 8).
  Hypothesis Hcal : (bv_unsigned C mod 8 = 0)%Z.
  Hypothesis Hch : heapish ceil (bv_unsigned C) 32.
  Hypothesis Hwc : writable SEGS mem (bv_unsigned C) 32.
  Hypothesis Hshc : shz mem (bv_unsigned C) 4.
  Hypothesis Hshw : shwz mem (bv_unsigned C + 12) 20.
  Hypothesis Hcar : (fs + FS_FRAMES5 <= bv_unsigned C)%Z /\ (bv_unsigned C + 32 <= fs + FS_SIZE)%Z.
  Hypothesis Hn32 : (0 <= n < 2 ^ 32)%Z.
  Hypothesis Hn   : rdn SEGS mem (Z_to_bv 64 (bv_unsigned C + 0)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 n)).
  Hypothesis Ht8  : rdn SEGS mem (Z_to_bv 64 (bv_unsigned C + 8)) 8 = Some (word_to_le_bytes 8 t8).
  Hypothesis Ht16 : rdn SEGS mem (Z_to_bv 64 (bv_unsigned C + 16)) 8 = Some (word_to_le_bytes 8 t16).
  Hypothesis Hcurve : n = 0%Z \/
     ((2 <= n <= 2 ^ 24)%Z
      /\ (bv_unsigned t8 <> 0%Z \/ bv_unsigned t16 <> 0%Z)
      /\ (bv_unsigned t8 <> 0%Z -> inDATA data len (bv_unsigned t8) n)
      /\ (bv_unsigned t16 <> 0%Z -> inDATA data len (bv_unsigned t16) (2 * n))).
  Hypothesis Hdok : as_data_ok ceil mem data len bs.
  Hypothesis Hdar : (bv_unsigned data + len <= fs \/ fs + FS_SIZE <= bv_unsigned data)%Z.
  Hypothesis Hdc : (bv_unsigned data + len <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned data)%Z.
  Hypothesis Henv : as_env SEGS ceil asan_abi fs ch mem.
  Hypothesis Hhdr : fs_hdr SEGS ceil asan_abi fs mem.
  Hypothesis Hfsw : fs_writable SEGS fs mem.
  Hypothesis Hhint : acellw SEGS mem (fs + FS_HINT0) h.
  Hypothesis Hflags : fs_flags0_but fs [] mem.

  Let E : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI))
                                ++ [S1w; Z_to_bv 64 n; t8; t16; Z_to_bv 64 fs; h; Z_to_bv 64 F; Z_to_bv 64 fa;
                                    Z_to_bv 64 Ff; Z_to_bv 64 faf])) (blobs_ev [bs]).
  (* [comment removed for export] *)

  Definition lit8 (a v : Z) : kentry := KWord (SA (ELit 0) a) 8 (ELit v).
  Definition kn0v1 : list kentry :=
    [lit8 0x9eaf0 0xa6bb8; lit8 0xa6bb8 SB; lit8 0x9eb48 0xa6bc0; KWord (SA (ELit 0) 0xa6bc0) 4 (ELit 1);
     (* [comment removed for export] *)
     KAlign (EVar 2) 16; KRange (EVar 2) (AS_STKLO + 2272) (2 ^ 47); KWr (SA (EVar 2) (-2272)) 2272;
     KAlign (EVar 64) 32; KRange (EVar 64) (AS_STKLO + 2128) (2 ^ 47 - 128); KWr (SA (EVar 64) (-2128)) 2160;
     KDisj (SA (EVar 64) (-2128)) 2160 (SA (EVar 2) (-96)) 96;
     (* [comment removed for export] *)
     KAlign (EVar 10) 8; KRange (EVar 10) 1 (2 ^ 47 - 32); KWr (SA (EVar 10) 0) 32;
     KZero (SA (EAlu ALU_SRL (EVar 10) (ELit 3)) SB) (ELit 4);
     KWord (SA (EVar 10) 0) 4 (EVar 65); KWord (SA (EVar 10) 8) 8 (EVar 66); KWord (SA (EVar 10) 16) 8 (EVar 67);
     (* [comment removed for export] *)
     KAlign (EVar 70) 64; KRange (EVar 70) 1 (2 ^ 47 - 64);
     KRange (EVar 71) 1 (2 ^ 47 - 1);
     KRange (EVar 68) 1 (2 ^ 47 - 8);
     KAlign (EVar 72) 64; KRange (EVar 72) 1 (2 ^ 47 - 64);
     KRange (EVar 73) 1 (2 ^ 47 - 1);
     KDisj (SA (EVar 70) 0) 64 (SA (EVar 10) 0) 32; KDisj (SA (EVar 71) 0) 1 (SA (EVar 10) 0) 32;
     KDisj (SA (EVar 68) 0) 8 (SA (EVar 10) 0) 32;
     KDisj (SA (EAlu ALU_SRL (EVar 70) (ELit 3)) SB) 8 (SA (EAlu ALU_SRL (EVar 10) (ELit 3)) SB) 4;
     KDisj (SA (EVar 70) 0) 64 (SA (EVar 68) 0) 8; KDisj (SA (EVar 71) 0) 1 (SA (EVar 68) 0) 8;
     KDisj (SA (EVar 70) 0) 64 (SA (EVar 71) 0) 1;
     KDisj (SA (EVar 72) 0) 64 (SA (EVar 10) 0) 32; KDisj (SA (EVar 73) 0) 1 (SA (EVar 10) 0) 32;
     KDisj (SA (EAlu ALU_SRL (EVar 72) (ELit 3)) SB) 8 (SA (EAlu ALU_SRL (EVar 10) (ELit 3)) SB) 4;
     KDisj (SA (EVar 72) 0) 64 (SA (EVar 70) 0) 64; KDisj (SA (EVar 72) 0) 64 (SA (EVar 71) 0) 1;
     KDisj (SA (EVar 72) 0) 64 (SA (EVar 68) 0) 8;
     KDisj (SA (EVar 73) 0) 1 (SA (EVar 70) 0) 64; KDisj (SA (EVar 73) 0) 1 (SA (EVar 71) 0) 1;
     KDisj (SA (EVar 73) 0) 1 (SA (EVar 68) 0) 8;
     KDisj (SA (EAlu ALU_SRL (EVar 72) (ELit 3)) SB) 8 (SA (EAlu ALU_SRL (EVar 70) (ELit 3)) SB) 8].

  (* [comment removed for export] *)
  Lemma placement :
    (fs + FS_FRAMES0 <= F)%Z /\ (F + 64 <= fs + FS_FRAMES0 + FS_FRAMES_LEN)%Z /\ (F mod 64 = 0)%Z /\
    (fs + FS_FLAGS0 <= fa)%Z /\ (fa < fs + FS_FLAGS0 + FS_FLAGS0_LEN)%Z /\
    (fs + FS_FRAMES0 <= Ff)%Z /\ (Ff + 64 <= fs + FS_FRAMES0 + FS_FRAMES_LEN)%Z /\ (Ff mod 64 = 0)%Z /\
    (fs + FS_FLAGS0 <= faf)%Z /\ (faf < fs + FS_FLAGS0 + FS_FLAGS0_LEN)%Z /\
    (F + 64 <= Ff \/ Ff + 64 <= F)%Z /\ (fa <> faf) /\
    (S1 mod 32 = 0)%Z /\ (bv_unsigned sp - 144 <= S1 <= bv_unsigned sp - 128)%Z.
  Proof using ceil mem sp C h fs Hal16 Hstk Hhdr.
    destruct Hhdr as (_ & _ & _ & Hlo & Hhi & Hal). pose proof (u64_range h). pose proof (u64_range h1). app_facts.
    pose proof (pos_succ_ne h) as Hne. fold h1 in Hne.
    destruct Hstk as [St1 St2]. unfold CANON_D in St1, St2.
    pose proof (realign_facts sp Hal16 ltac:(rlia)) as [RF1 RF2]. fold S1w in RF1, RF2. fold S1 in RF1, RF2.
    pose proof (frame0_al64 fs (pos0 h) Hal) as A1. pose proof (frame0_al64 fs (pos0 h1) Hal) as A2.
    unfold F, fa, Ff, faf, frame0, FS_FRAMES0, FS_FRAMES_LEN, FS_FLAGS0, FS_FLAGS0_LEN.
    assert (B1 : (0 <= pos0 h < 16384)%Z) by (unfold pos0; apply Z.mod_pos_bound; rlia).
    assert (B2 : (0 <= pos0 h1 < 16384)%Z) by (unfold pos0; apply Z.mod_pos_bound; rlia).
    revert Hne B1 B2 A1 A2. generalize (pos0 h) (pos0 h1). intros p q Hne B1 B2 A1 A2.
    repeat split; first [assumption | rlia].
  Qed.

  (* [comment removed for export] *)
  Lemma quotients :
    F = (8 * (F / 8))%Z /\ Ff = (8 * (Ff / 8))%Z /\ bv_unsigned C = (8 * (bv_unsigned C / 8))%Z /\
    (fs + FS_FRAMES0 = 8 * ((fs + FS_FRAMES0) / 8))%Z /\ S1 = (8 * (S1 / 8))%Z /\
    bv_unsigned data = (8 * (bv_unsigned data / 8))%Z /\ (8 * (len / 8) <= len < 8 * (len / 8) + 8)%Z /\
    bv_unsigned sp = (8 * (bv_unsigned sp / 8))%Z.
  Proof using ceil mem sp C data h len fs bs Hal16 Hstk Hcal Hdok Hhdr.
    pose proof placement as (_ & _ & F3 & _ & _ & _ & _ & G3 & _ & _ & _ & _ & SM & _).
    destruct Hhdr as (_ & _ & _ & _ & _ & Hal). destruct Hdok as (_ & _ & Hdal & _). unfold FS_FRAMES0. app_facts.
    split; [apply mod_exact; [rlia|]; apply (mod_down F 8 8); [rlia|rlia|exact F3]|].
    split; [apply mod_exact; [rlia|]; apply (mod_down Ff 8 8); [rlia|rlia|exact G3]|].
    split; [apply mod_exact; [rlia|exact Hcal]|].
    split. { apply mod_exact; [rlia|]. apply (mod_down _ 8 512); [rlia|rlia|]. change (8*512)%Z with 4096%Z.
             rewrite <- Zplus_mod_idemp_l, Hal. reflexivity. }
    split; [apply mod_exact; [rlia|]; apply (mod_down S1 8 4); [rlia|rlia|exact SM]|].
    split; [apply mod_exact; [rlia|]; apply (mod_down _ 8 2); [rlia|rlia|exact Hdal]|].
    split; [apply div8_bounds|].
    apply mod_exact; [rlia|]; apply (mod_down _ 8 2); [rlia|rlia|exact Hal16].
  Qed.

  Ltac qlia := lazymatch goal with HQ : hidden (_ = _ /\ _) |- _ =>
    let Q1 := fresh "Q" in let Q2 := fresh "Q" in let Q3 := fresh "Q" in let Q4 := fresh "Q" in
    let Q5 := fresh "Q" in let Q6 := fresh "Q" in let Q7 := fresh "Q" in let Q8 := fresh "Q" in
    pose proof (unhide HQ) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8);
    first [ clear Q2 Q4 Q5 Q6 Q7 Q8; rlia            (* [comment removed for export] *)
          | clear Q1 Q3 Q4 Q5 Q6 Q7 Q8; rlia         (* [comment removed for export] *)
          | clear Q3 Q4 Q5 Q6 Q7 Q8; rlia            (* [comment removed for export] *)
          | clear Q2 Q3 Q5 Q6 Q7 Q8; rlia            (* [comment removed for export] *)
          | clear Q2 Q3 Q4 Q6 Q7 Q8; rlia            (* [comment removed for export] *)
          | rlia ] end.
  (* [comment removed for export] *)
  Ltac opaque_lets := clearbody F fa Ff faf.

  Ltac klit H := eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0));
    [reflexivity | cbn [edenot]; ev_simpl E; reflexivity | rlia | rlia | rewrite u_lit0; rlia | rewrite u_lit0; rlia | rewrite u_lit0, Z.add_0_l; exact H].
  Ltac kdisj := cbn [kentry_ok]; unfold estart; cbn [a_base a_off]; rewrite ?edenot_srl3; cbn [edenot]; ev_simpl E;
                rewrite ?Hc, ?Hsp, ?u_small by clia; unfold SB; first [(div8_facts; rlia) | qlia].

  Lemma kn0v1_ok : know_ok SEGS E mem kn0v1.
  Proof using ceil FPI regs mem sp C data t8 t16 h n len fs bs ch Hsp Hc Hal16 Hstk Hwst Hcal Hch Hwc Hshc Hcar Hn Ht8 Ht16 Hdok Henv Hhdr.
    clear Hcurve Hdar Hdc Hshw Hflags Hfit Hsm Hmemset.
    unfold kn0v1, lit8. pose proof (u64_range C). pose proof (u64_range sp).
    pose proof placement as (F1 & F2 & F3 & F4 & F5 & G1 & G2 & G3 & G4 & G5 & FF & AA & SM & SR). pose proof quotients as HQ. hide HQ.
    destruct Hhdr as (_ & _ & _ & Hlo & Hhi & Hal). destruct Hstk as [St1 St2]. destruct Hch as [C1 C2]. app_facts.
    unfold CANON_D, FS_SIZE, FS_FRAMES0, FS_FRAMES_LEN, FS_FLAGS0, FS_FLAGS0_LEN, FS_FRAMES5 in *.
    destruct Hwst as (_ & _ & _ & W4). destruct Hwc as (_ & _ & _ & V4).
    destruct Henv as (Hcells & _ & _ & _). pose proof (asan_cells64 SEGS mem Hcells) as CC.
    destruct CC as (E1 & E2 & E3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E22 & _).
    unfold acell in E1, E2, E3, E22. opaque_lets.
    unfold know_ok.
    repeat lazymatch goal with |- Forall _ (_ :: _) => constructor | |- Forall _ [] => constructor end.
    all: lazymatch goal with |- Forall _ _ => fail | _ => idtac end.
    - klit E1. - klit E2. - klit E3. - klit E22.
    - apply kalign_intro; [rlia|]. cbn [edenot]; ev_simpl E. rewrite Hsp. exact Hal16.
    - apply krange_intro. cbn [edenot]; ev_simpl E. rewrite Hsp. rlia.
    - apply (kwr_intro SEGS E mem (EVar 2) sp (-2272) 2272); [cbn [edenot]; ev_simpl E; exact Hsp | rlia | rlia | rlia |].
      replace (bv_unsigned sp + -2272)%Z with (bv_unsigned sp - 2272)%Z by rlia. exact W4.
    - apply kalign_intro; [rlia|]. cbn [edenot]; ev_simpl E. exact SM.
    - apply krange_intro. cbn [edenot]; ev_simpl E. fold S1. rlia.
    - apply (kwr_intro SEGS E mem (EVar 64) S1w (-2128) 2160); [cbn [edenot]; ev_simpl E; reflexivity | fold S1; rlia | rlia | fold S1; rlia |].
      fold S1. eapply (proj2 (proj2 (proj2 (writable_sub SEGS mem _ _ (S1 + -2128) 2160 Hwst ltac:(rlia) ltac:(rlia) ltac:(rlia))))).
    - kdisj.
    - apply kalign_intro; [rlia|]. cbn [edenot]; ev_simpl E. rewrite Hc. exact Hcal.
    - apply krange_intro. cbn [edenot]; ev_simpl E. rewrite Hc. rlia.
    - apply (kwr_intro SEGS E mem (EVar 10) C 0 32); [cbn [edenot]; ev_simpl E; exact Hc | rlia | rlia | rlia | rewrite Z.add_0_r; exact V4].
    - eapply (kzero_shz_intro SEGS E mem (EVar 10) C 4); [cbn [edenot]; ev_simpl E; exact Hc | exact Hshc | rlia | rlia].
    - eapply (kword_intro SEGS E mem (EVar 10) C 0 4 (EVar 65) (Z_to_bv 64 n)); cbn; try rlia; auto.
    - eapply (kword_intro SEGS E mem (EVar 10) C 8 8 (EVar 66) t8); cbn; try rlia; auto.
    - eapply (kword_intro SEGS E mem (EVar 10) C 16 8 (EVar 67) t16); cbn; try rlia; auto.
    - apply kalign_intro; [rlia|]. cbn [edenot]; ev_simpl E. rewrite u_small by clia. exact F3.
    - apply krange_intro. cbn [edenot]; ev_simpl E. rewrite u_small by clia. rlia.
    - apply krange_intro. cbn [edenot]; ev_simpl E. rewrite u_small by clia. rlia.
    - apply krange_intro. cbn [edenot]; ev_simpl E. rewrite u_small by clia. rlia.
    - apply kalign_intro; [rlia|]. cbn [edenot]; ev_simpl E. rewrite u_small by clia. exact G3.
    - apply krange_intro. cbn [edenot]; ev_simpl E. rewrite u_small by clia. rlia.
    - apply krange_intro. cbn [edenot]; ev_simpl E. rewrite u_small by clia. rlia.
    - kdisj. - kdisj. - kdisj. - kdisj. - kdisj. - kdisj. - kdisj. - kdisj. - kdisj. - kdisj. - kdisj. - kdisj. - kdisj. - kdisj.
    - kdisj. - kdisj. - kdisj.
  Qed.

  Definition kn0 : list kentry := kn0v1 ++
    [KDisj (SA (EVar 10) 0) 32 ZSH ZSHL; KDisj (SA (EVar 10) 0) 32 ZIMG ZIMGL;
     KDisj (SA (EVar 10) 0) 32 (SA (EVar 2) (-2272)) 2272;
     KDisj (SA (EVar 10) 0) 32 (SA (EVar 64) (-2128)) 2160;
     KDisj (SA (EVar 70) 0) 64 ZSH ZSHL; KDisj (SA (EVar 70) 0) 64 ZIMG ZIMGL;
     KDisj (SA (EVar 70) 0) 64 (SA (EVar 2) (-2272)) 2272;
     KDisj (SA (EVar 70) 0) 64 (SA (EVar 64) (-2128)) 2160;
     KDisj (SA (EVar 71) 0) 1 ZSH ZSHL; KDisj (SA (EVar 71) 0) 1 ZIMG ZIMGL;
     KDisj (SA (EVar 71) 0) 1 (SA (EVar 2) (-2272)) 2272;
     KDisj (SA (EVar 71) 0) 1 (SA (EVar 64) (-2128)) 2160;
     KDisj (SA (EVar 68) 0) 8 ZSH ZSHL; KDisj (SA (EVar 68) 0) 8 ZIMG ZIMGL;
     KDisj (SA (EVar 68) 0) 8 (SA (EVar 2) (-2272)) 2272;
     KDisj (SA (EVar 68) 0) 8 (SA (EVar 64) (-2128)) 2160;
     KDisj (SA (EVar 72) 0) 64 ZSH ZSHL; KDisj (SA (EVar 72) 0) 64 ZIMG ZIMGL;
     KDisj (SA (EVar 72) 0) 64 (SA (EVar 2) (-2272)) 2272;
     KDisj (SA (EVar 72) 0) 64 (SA (EVar 64) (-2128)) 2160;
     KDisj (SA (EVar 73) 0) 1 ZSH ZSHL; KDisj (SA (EVar 73) 0) 1 ZIMG ZIMGL;
     KDisj (SA (EVar 73) 0) 1 (SA (EVar 2) (-2272)) 2272;
     KDisj (SA (EVar 73) 0) 1 (SA (EVar 64) (-2128)) 2160].
  Lemma kn0_ok : know_ok SEGS E mem kn0.
  Proof using ceil FPI regs mem sp C data t8 t16 h n len fs bs ch Hsp Hc Hal16 Hstk Hwst Hcal Hch Hwc Hshc Hcar Hn Ht8 Ht16 Hdok Henv Hhdr.
    apply know_ok_app; [exact kn0v1_ok|].
    pose proof placement as (F1 & F2 & F3 & F4 & F5 & G1 & G2 & G3 & G4 & G5 & FF & AA & SM & SR).
    destruct Hhdr as (_ & _ & _ & Hlo & Hhi & Hal). app_facts.
    unfold CANON_D, FS_SIZE, FS_FRAMES0, FS_FRAMES_LEN, FS_FLAGS0, FS_FLAGS0_LEN in *.
    (* [comment removed for export] *)
    repeat match goal with H : _ \/ _ |- _ => clear H end.
    kn_place.
  Qed.

  (* [comment removed for export] *)
  Lemma EF : (fs + 36864 + 0 * 2 ^ 20 + 64 * (bv_unsigned h mod 16384))%Z = F.
  Proof using sp C h fs. unfold F, frame0, pos0, FS_FRAMES0. rlia. Qed.
  Lemma Efa : (fs + 4096 + 0 + bv_unsigned h mod 16384)%Z = fa.
  Proof using sp C h fs. unfold fa, pos0, FS_FLAGS0. rlia. Qed.
  Lemma Efa' : (fs + FS_FLAGS0 + pos0 h)%Z = fa.
  Proof using h fs. reflexivity. Qed.
  Lemma WF : writable SEGS mem F 64.
  Proof using ceil mem sp C h fs Hal16 Hstk Hhdr Hfsw.
    pose proof placement as (F1 & F2 & _). destruct Hhdr as (_ & _ & _ & Hlo & Hhi & _). destruct Hfsw as (_ & _ & _ & _ & Wfr0 & _). app_facts.
    unfold FS_FRAMES0, FS_FRAMES_LEN, FS_SIZE in *.
    eapply (writable_sub SEGS mem (fs + 36864) 1048576); [split; [rlia|split; [rlia|split; [rlia|exact Wfr0]]]|rlia|rlia|rlia].
  Qed.
  Lemma WSF : writable SEGS mem (2147450880 + F / 8) 8.
  Proof using ceil mem sp C data h len fs bs Hal16 Hstk Hcal Hdok Hhdr Hfsw.
    pose proof placement as (F1 & F2 & _). pose proof quotients as (Q1 & _ & _ & Q4 & _).
    destruct Hhdr as (_ & _ & _ & Hlo & Hhi & _). destruct Hfsw as (_ & _ & _ & _ & _ & _ & Wsh0 & _). app_facts.
    unfold FS_FRAMES0, FS_FRAMES_LEN, FS_SIZE, AS_SB, FS_SHFRAMES_LEN in *.
    eapply (writable_sub SEGS mem (2147450880 + (fs + 36864) / 8) 131072); [split; [rlia|split; [rlia|split; [rlia|exact Wsh0]]]|rlia|rlia|rlia].
  Qed.
  Lemma Wfa : writable SEGS mem fa 1.
  Proof using ceil mem sp C h fs Hal16 Hstk Hhdr Hfsw.
    pose proof placement as (_ & _ & _ & F4 & F5 & _). destruct Hhdr as (_ & _ & _ & Hlo & Hhi & _). destruct Hfsw as (_ & _ & Wfl0 & _). app_facts.
    unfold FS_FLAGS0, FS_FLAGS0_LEN, FS_SIZE in *.
    eapply (writable_sub SEGS mem (fs + 4096) 16384); [split; [rlia|split; [rlia|split; [rlia|exact Wfl0]]]|rlia|rlia|rlia].
  Qed.
  Lemma shz_sub : forall M a m a' m', shz M a m -> (a' mod 8 = 0)%Z -> (a <= a')%Z -> (0 <= m')%Z -> (a' + 8 * m' <= a + 8 * m)%Z -> shz M a' m'.
  Proof using rom sp C h n fs Hn32.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    intros M a m a' m' [Hal Hz] Hal' Hle Hm' Hhi. split; [exact Hal'|]. intros j Hj.
    replace (SB + a' / 8 + j)%Z with (SB + a / 8 + (a' / 8 - a / 8 + j))%Z by rlia. apply Hz. rlia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.
  Lemma EF0 : frame0 fs (pos0 h) = F. Proof using h fs. reflexivity. Qed.
  Lemma EFf : frame0 fs (pos0 h1) = Ff. Proof using h fs. reflexivity. Qed.
  Lemma Efaf : (fs + FS_FLAGS0 + pos0 h1)%Z = faf. Proof using h fs. reflexivity. Qed.
  Lemma div8_F32 : ((F + 32) / 8 = F / 8 + 4)%Z.
  Proof using sp C h fs. replace (F + 32)%Z with (F + 8 * 4)%Z by rlia. apply div8_addk. Qed.
  Lemma SM32 : (S1 mod 32 = 0)%Z.
  Proof using ceil mem sp C h fs Hal16 Hstk Hhdr. pose proof placement as P. do 12 (apply proj2 in P). exact (proj1 P). Qed.
  (* [comment removed for export] *)
  Lemma canon_shwz : forall M rs,
    frame_mod mem M rs ->
    Forall (fun r => (bv_unsigned (fst r) + snd r <= 0x7fff7000 \/ 0x10007fff8000 <= bv_unsigned (fst r)) \/
                     (bv_unsigned (fst r) = 2147450880 + F / 8 /\ snd r = 8) \/
                     (bv_unsigned (fst r) = 2147450880 + Ff / 8 /\ snd r = 8) \/
                     (bv_unsigned (fst r) = 2147450880 + (fs + 36864) / 8 /\ snd r = 131072))%Z rs ->
    shwz M (bv_unsigned C + 12) 20.
  Proof using ceil mem rom sp C h n fs Hal16 Hstk Hcal Hch Hshw Hcar Hn32 Hhdr.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    intros M rs Hf Hrs. pose proof placement as (F1 & F2 & _ & _ & _ & G1 & G2 & _). destruct Hch as [C1 C2]. destruct Hcar as [A1 A2]. app_facts.
    destruct Hhdr as (_ & _ & _ & Hlo & Hhi & _). pose proof (u64_range C). app_facts.
    clear Hcurve Hdar Hdc Hflags Hfit Hsm Hmemset.
    unfold CANON_D, FS_FRAMES0, FS_FRAMES_LEN, FS_FRAMES5, FS_SIZE in *. opaque_lets.
    eapply shwz_frame; [exact Hf | exact Hshw | rlia | rlia |].
    unfold apart, AS_SB. eapply Forall_impl; [|exact Hrs]. cbv beta. intros [b m] Hb. cbn [fst snd] in *.
    destruct Hb as [Hb | [[Hb Hm] | [[Hb Hm] | [Hb Hm]]]]; rewrite ?Hb, ?Hm; dlia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  Lemma Whint : writable SEGS mem (fs + 0) 8.
  Proof using ceil mem sp C h fs Hstk Hhdr Hfsw.
    destruct Hhdr as (_ & _ & _ & Hlo & Hhi & _). destruct Hfsw as (Wh0 & _). unfold FS_SIZE, FS_HINT0 in *. app_facts.
    split; [rlia|split; [rlia|split; [rlia|exact Wh0]]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac rewrite_getr_in H :=
    repeat match goal with G : getr ?R ?r = _ |- _ => rewrite G in H end.
  Ltac ev_simpl_goal := match goal with HK : know_ok _ ?E0 _ _ |- _ => ev_simpl E0 end.

  (* [comment removed for export] *)
  Ltac regions_eq :=
    repeat (lazymatch goal with
            | |- (_ :: _) = (_ :: _) => apply f_equal2; [apply f_equal2; [apply (f_equal (Z_to_bv 64)); unfold SB; qlia | reflexivity] |]
            | |- [] = [] => reflexivity end).
  Ltac norm_denots E0 := cbn [regions_denot map fst snd]; unfold adenot; cbn [a_base a_off edenot]; ev_simpl E0;
                         unfold v_addi; rewrite ?u_srl3; rewrite_getr; fold S1; rewrite ?u_small by clia.
  Ltac flats E0 := repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; unfold flat, estart, elenZ; cbn [a_base a_off];
                   rewrite ?edenot_srl3; cbn [edenot]; ev_simpl E0; rewrite_getr; fold S1; rewrite ?u_small by clia; unfold SB; qlia.

  (* [comment removed for export] *)
  Ltac frame_of_log RS :=
    lazymatch goal with
    | |- frame_mod ?M0 (mem_denot ?E0 ?M0 ?log) ?regions =>
        replace regions with (regions_denot E0 RS) by (norm_denots E0; regions_eq);
        apply (frame_mod_mem_denot E0 M0 log RS);
          [ lazymatch goal with H : log_flat _ log |- _ => exact H end
          | flats E0
          | vm_compute; reflexivity ]
    end.

  (* [comment removed for export] *)
  Ltac kframe HK Hfr RS :=
    lazymatch type of HK with know_ok _ ?E1 ?M0 ?kn =>
    lazymatch type of Hfr with frame_mod _ ?M' ?rs =>
      let Hrd := fresh "Hrd" in let Hrs := fresh "Hrs" in let Hfl := fresh "Hfl" in let H := fresh "HK" in
      assert (Hrd : regions_denot E1 RS = rs) by (norm_denots E1; regions_eq);
      assert (Hrs : frame_mod M0 M' (regions_denot E1 RS)) by (rewrite Hrd; exact Hfr);
      assert (Hfl : Forall (fun r => flat E1 (fst r) (snd r)) RS) by (flats E1);
      pose proof (know_ok_frame_mod SEGS E1 RS M0 M' kn HK Hfl Hrs) as H;
      let kn' := eval vm_compute in (kn_frames kn RS) in
      change (kn_frames kn RS) with kn' in H;
      clear Hrd Hrs Hfl HK; rename H into HK
    end end.

  (* [comment removed for export] *)
  Ltac kcell HK b k n v H :=
    lazymatch type of HK with know_ok _ ?E0 ?M0 ?kn =>
      let KR := fresh "KR" in let Hfl := fresh "Hfl" in
      assert (KR : kread SEGS kn b k n = Some v) by (vm_compute; reflexivity);
      pose proof (kread_rdn SEGS E0 M0 kn b k n v HK KR ltac:(rlia) ltac:(rlia)) as H; clear KR;
      lazymatch type of H with ?FL -> _ =>
        assert (Hfl : FL) by (unfold flat, estart; cbn [a_base a_off]; rewrite ?edenot_srl3; cbn [edenot]; ev_simpl E0; rewrite_getr;
                              fold S1; rewrite ?u_small by clia; unfold SB; qlia);
        specialize (H Hfl); clear Hfl end;
      unfold adenot, v_addi in H; cbn [a_base a_off] in H; cbn [edenot] in H; ev_simpl_in E0 H; rewrite ?u_srl3 in H; rewrite_getr_in H;
      fold S1 in H; rewrite ?u_small in H by clia
    end.

  (* [comment removed for export] *)
  Ltac kn_prefix HK entries :=
    lazymatch type of HK with know_ok _ ?E1 ?M1 ?kn1 =>
      let HK' := fresh "HK" in
      assert (HK' : know_ok SEGS E1 M1 (entries ++ kn1));
      [ apply know_ok_app; [| exact HK]; unfold know_ok; repeat (apply Forall_cons); try apply Forall_nil
      | clear HK; rename HK' into HK; cbn [app] in HK ]
    end.

  (* [comment removed for export] *)
  Ltac post_regs :=
    lazymatch goal with
    | |- exists FPI' regs' mem', @mkst ?I ?R' _ ?M' _ = _ /\ _ =>
      lazymatch goal with
      | HR : regs_ok ?E1 ?sr R', HF : fregs_ok _ ?sfr (@fp_regs I), HR0 : id (regs_ok _ ?sr0 ?regs0), HF0 : id (fregs_ok _ ?sfr0 ?fr0) |- _ =>
        lift_id HR0 HR; lift_id HF0 HF;
        exists I, R', M'; split; [regv HR (1%bv:reg); rewrite_getr; reflexivity|];
        split; [ let Hso := fresh "Hso" in
                 pose proof (regs_same_on E1 sr0 sr regs0 R' [2;3;8;9;18;19;20;21;22;23;24;25;26;27]%bv HR0 HR ltac:(vm_compute; reflexivity)) as Hso;
                 intros r Hr; cbn [In abi_kept] in Hr;
                 destruct Hr as [<-|[<-|[<-|Hr]]]; [apply Hso; first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)] | apply Hso; first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)] | regv HR (4%bv:reg); rewrite Htp; reflexivity |];
                 apply Hso; cbn; cbn in Hr; tauto
               |];
        split; [exact (fregs_same_on E1 sfr0 sfr fr0 _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity))|]
      end
    end.

  (* [comment removed for export] *)
  Definition QP (FPI' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
    regs_kept abi_kept regs regs' /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI')) /\
    (frame_mod mem mem' ([(Z_to_bv 64 (bv_unsigned sp - CANON_D), CANON_D); (C, 32%Z)] ++ fs_mod0 fs) /\
     curve_ok SEGS mem' data len (bv_unsigned C) /\
     fs_flags0_but fs [] mem' /\ (exists h', acellw SEGS mem' (fs + FS_HINT0) h')).
  Definition Q (st' : machine_state) : Prop :=
    exists (FPI' : FPState) regs' mem', st' = mkst (FP:=FPI') regs' ret mem' rom /\ QP FPI' regs' mem'.

  (* [comment removed for export] *)
  Definition TGT : list (word * Z) :=
    [(Z_to_bv 64 (bv_unsigned sp - 2272), 2272%Z); (C, 32%Z); (Z_to_bv 64 (fs + 0), 8%Z); (Z_to_bv 64 (fs + 4096), 16384%Z);
     (Z_to_bv 64 (fs + 36864), 1048576%Z); (Z_to_bv 64 (2147450880 + (fs + 36864) / 8), 131072%Z)].

  Lemma TGT_eq : ([(Z_to_bv 64 (bv_unsigned sp - CANON_D), CANON_D); (C, 32%Z)] ++ fs_mod0 fs) = TGT.
  Proof using sp C fs. reflexivity. Qed.

  Definition in_tgt (b : word) (m : Z) : Prop :=
    exists b' n', In (b', n') TGT /\ (bv_unsigned b' <= bv_unsigned b)%Z /\ (bv_unsigned b + m <= bv_unsigned b' + n')%Z.

  Lemma incl_of_in_tgt : forall rs, Forall (fun r => in_tgt (fst r) (snd r)) rs -> regions_incl rs TGT.
  Proof using sp C fs.
    intros rs H b m Hin. rewrite Forall_forall in H. exact (H (b, m) Hin).
  Qed.

  Lemma frame_TGT_app : forall M1 M2 l,
    frame_mod mem M1 TGT -> frame_mod M1 M2 l -> regions_incl l TGT -> frame_mod mem M2 TGT.
  Proof using mem sp C h fs.
    intros M1 M2 l H1 H2 Hl. eapply frame_mod_incl; [| exact (frame_mod_trans _ _ _ _ _ H1 H2)].
    intros b m Hin. apply in_app_or in Hin as [Hin|Hin].
    - exists b, m. split; [exact Hin| rlia].
    - exact (Hl b m Hin).
  Qed.

  Lemma tgt_facts :
    in_tgt (Z_to_bv 64 (bv_unsigned sp - 128)) 128 /\ in_tgt (Z_to_bv 64 (S1 - 208)) 208 /\ in_tgt (Z_to_bv 64 (S1 - 432)) 464 /\
    in_tgt (Z_to_bv 64 (S1 - 2128)) 2128 /\ in_tgt (Z_to_bv 64 (S1 + 16)) 8 /\ in_tgt (Z_to_bv 64 (S1 + 28)) 4 /\
    in_tgt (Z_to_bv 64 (fs + 0)) 8 /\ in_tgt (Z_to_bv 64 fa) 1 /\ in_tgt (Z_to_bv 64 faf) 1 /\
    in_tgt (Z_to_bv 64 F) 24 /\ in_tgt (Z_to_bv 64 F) 64 /\ in_tgt (Z_to_bv 64 F) 8 /\ in_tgt (Z_to_bv 64 (F + 24)) 8 /\ in_tgt (Z_to_bv 64 (F + 32)) 4 /\
    in_tgt (Z_to_bv 64 (F + 56)) 8 /\ in_tgt (Z_to_bv 64 Ff) 64 /\
    in_tgt (Z_to_bv 64 (2147450880 + F / 8)) 8 /\ in_tgt (Z_to_bv 64 (2147450880 + Ff / 8)) 8 /\
    in_tgt C 32 /\ in_tgt (Z_to_bv 64 (bv_unsigned C + 12)) 20 /\ in_tgt (Z_to_bv 64 (bv_unsigned C + 0)) 12.
  Proof using ceil mem rom ret sp C data h n len fs bs Hal16 Hstk Hcal Hch Hcar Hn32 Hdok Hhdr.
    pose proof (u64_range C). pose proof (u64_range sp).
    pose proof placement as (F1 & F2 & F3 & F4 & F5 & G1 & G2 & G3 & G4 & G5 & FF & AA & SM & SR). pose proof quotients as HQ. hide HQ.
    destruct Hhdr as (_ & _ & _ & Hlo & Hhi & Hal). destruct Hstk as [St1 St2]. destruct Hch as [C1 C2]. app_facts.
    unfold CANON_D, FS_SIZE, FS_FRAMES0, FS_FRAMES_LEN, FS_FLAGS0, FS_FLAGS0_LEN, FS_FRAMES5 in *.
    clear Hcurve Hdar Hdc Hshw Hflags Hfit Hsm Hmemset FF AA. opaque_lets.
    unfold in_tgt, TGT.
    Ltac fin := split; [first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)] | rewrite ?u_small by first [(div8_facts; rlia) | qlia]; first [(div8_facts; rlia) | qlia]].
    Ltac p1 := exists (Z_to_bv 64 (bv_unsigned sp - 2272)), 2272%Z; fin.
    Ltac p2 := exists C, 32%Z; fin.
    Ltac p3 := exists (Z_to_bv 64 (fs + 0)), 8%Z; fin.
    Ltac p4 := exists (Z_to_bv 64 (fs + 4096)), 16384%Z; fin.
    Ltac p5 := exists (Z_to_bv 64 (fs + 36864)), 1048576%Z; fin.
    Ltac p6 := exists (Z_to_bv 64 (2147450880 + (fs + 36864) / 8)), 131072%Z; fin.
    split; [p1|]. split; [p1|]. split; [p1|]. split; [p1|]. split; [p1|]. split; [p1|].
    split; [p3|]. split; [p4|]. split; [p4|].
    split; [p5|]. split; [p5|]. split; [p5|]. split; [p5|]. split; [p5|]. split; [p5|]. split; [p5|].
    split; [p6|]. split; [p6|].
    split; [p2|]. split; [p2|]. p2.
  Qed.

  (* [comment removed for export] *)
  Ltac zone_split x :=
    let h := fresh "Fz" in
    first [ match goal with H : appm x ?n |- _ => pose proof (app_sh_lit x n H) as h end
          | match goal with H : appm x ?n /\ _ |- _ => pose proof (app_sh_lit x n (proj1 H)) as h end
          | match goal with H : (appm x ?n /\ _) /\ _ |- _ => pose proof (app_sh_lit x n (proj1 (proj1 H))) as h end
          | match goal with H : fs_hdr _ _ _ x _ |- _ => pose proof (app_sh_lit x _ (proj1 (proj2 (proj2 (proj2 H))))) as h end ];
    destruct h as [h|h].
  Ltac solve_apart_q :=
    unfold apart, SB; repeat (apply Forall_cons; [cbn [fst snd]; div8_facts; rewrite ?u_small_frame by first [clia | qlia];
       lazymatch goal with
       | |- context [ (2147450880 + _)%Z ] => first [(zone_split fs; clia) | (zone_split (bv_unsigned data); clia) | clia | dlia | qlia]
       | _ => first [clia | dlia | qlia] end |]);
    apply Forall_nil.

  Ltac solve_incl :=
    lazymatch goal with |- regions_incl ?rs _ => change (regions_incl rs TGT) end; apply incl_of_in_tgt;
    pose proof tgt_facts as (?T1 & ?T2 & ?T3 & ?T4 & ?T5 & ?T6 & ?T7 & ?T8 & ?T9 & ?T10 & ?T11 & ?T12 & ?T13 & ?T14 & ?T15 & ?T16 & ?T17 & ?T18 & ?T19 & ?T20 & ?T21);
    repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; first [assumption | match goal with |- ?g => idtac "INCL-MISS" g end].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Abbreviation fp0 := (fp_regs (FPState:=FPI)).

  Definition SAVED (M : word -> option byte) : Prop :=
    cell64 SEGS M (bv_unsigned sp - 8) ret /\ cell64 SEGS M (bv_unsigned sp - 16) (getr regs 8) /\
    cell64 SEGS M (bv_unsigned sp - 24) (getr regs 9) /\ cell64 SEGS M (bv_unsigned sp - 32) (getr regs 18) /\
    cell64 SEGS M (bv_unsigned sp - 40) (getr regs 19) /\ cell64 SEGS M (bv_unsigned sp - 48) (getr regs 20) /\
    cell64 SEGS M (bv_unsigned sp - 56) (getr regs 21) /\ cell64 SEGS M (bv_unsigned sp - 64) (getr regs 22) /\
    cell64 SEGS M (bv_unsigned sp - 72) (getr regs 23) /\ cell64 SEGS M (bv_unsigned sp - 80) (getr regs 24) /\
    cell64 SEGS M (bv_unsigned sp - 88) (getr regs 25) /\ cell64 SEGS M (bv_unsigned sp - 96) (reg_get fp0 8).

  Definition TINV (FPI' : FPState) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
    getr R 8 = sp /\ getr R 4 = Z_to_bv 64 TP /\ getr R 3 = getr regs 3 /\ getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27 /\
    getr R 18 = Z_to_bv 64 F /\ getr R 22 = Z_to_bv 64 F /\
    getr R 23 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 F) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
    (forall r, In r [9;18;19;20;21;22;23;24;25;26;27]%bv -> reg_get (fp_regs (FPState:=FPI')) r = reg_get fp0 r) /\
    SAVED M /\ frame_mod mem M TGT /\ curve_ok SEGS M data len (bv_unsigned C) /\
    fs_flags0_but fs [pos0 h] M /\ (exists h', acellw SEGS M (fs + 0) h') /\ acell SEGS M (F + 56) 8 fa.

  (* [comment removed for export] *)
  Definition SRT : list expr :=
    [ELit 0; EVar 1; EVar 2; EVar 67; ELit TP; EVar 5; EVar 6; EVar 7;
     EVar 66; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17;
     EVar 128; EVar 19; EVar 20; EVar 21; EVar 128; EAlu ALU_ADD (EAlu ALU_SRL (EVar 128) (ELit 3)) (ELit SB);
     EVar 24; EVar 25; EVar 90; EVar 91; EVar 28; EVar 29; EVar 30; EVar 31].
  Definition SFT : list expr :=
    [EVar 32; EVar 33; EVar 34; EVar 35; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 105;
     EVar 42; EVar 43; EVar 44; EVar 45; EVar 46; EVar 47; EVar 48; EVar 49;
     EVar 114; EVar 115; EVar 116; EVar 117; EVar 118; EVar 119; EVar 120; EVar 121; EVar 122; EVar 123;
     EVar 60; EVar 61; EVar 62; EVar 63].
  Definition KNT : list kentry :=
    [KAlign (EVar 66) 16; KRange (EVar 66) (AS_STKLO + 2272) (2 ^ 47); KWr (SA (EVar 66) (-2272)) 2272;
     KWord (SA (EVar 66) (-8)) 8 (EVar 65); KWord (SA (EVar 66) (-16)) 8 (EVar 72); KWord (SA (EVar 66) (-24)) 8 (EVar 73);
     KWord (SA (EVar 66) (-32)) 8 (EVar 82); KWord (SA (EVar 66) (-40)) 8 (EVar 83); KWord (SA (EVar 66) (-48)) 8 (EVar 84);
     KWord (SA (EVar 66) (-56)) 8 (EVar 85); KWord (SA (EVar 66) (-64)) 8 (EVar 86); KWord (SA (EVar 66) (-72)) 8 (EVar 87);
     KWord (SA (EVar 66) (-80)) 8 (EVar 88); KWord (SA (EVar 66) (-88)) 8 (EVar 89); KWord (SA (EVar 66) (-96)) 8 (EVar 104);
     KAlign (EVar 128) 64; KRange (EVar 128) 1 (2 ^ 47 - 64); KWr (SA (EVar 128) 0) 64;
     KWr (SA (EAlu ALU_SRL (EVar 128) (ELit 3)) SB) 8; KWord (SA (EVar 128) 56) 8 (EVar 129);
     KRange (EVar 129) 1 (2 ^ 47 - 1); KWr (SA (EVar 129) 0) 1; KDisj (SA (EVar 128) 0) 64 (SA (EVar 129) 0) 1;
     KDisj (SA (EVar 128) 0) 64 ZSH ZSHL; KDisj (SA (EVar 128) 0) 64 ZIMG ZIMGL; KDisj (SA (EVar 128) 0) 64 (SA (EVar 66) (-2272)) 2272;
     KDisj (SA (EVar 129) 0) 1 ZSH ZSHL; KDisj (SA (EVar 129) 0) 1 ZIMG ZIMGL; KDisj (SA (EVar 129) 0) 1 (SA (EVar 66) (-2272)) 2272].

  Lemma tailQ : forall (FPI' : FPState) R M, TINV FPI' R M ->
    runs_to SEGS (mkst (FP:=FPI') R (Z_to_bv 64 0x86f5c) M rom) Q.
  Proof using ceil FPI regs mem rom ret sp C data h n len fs bs Hra Hret Hsp Htp Hal16 Hstk Hwst Hcal Hch Hcar Hn32 Hdok Hhdr Hfsw.
    intros FPI' R M (R8 & R4 & R3 & R26 & R27 & R18 & R22 & R23 & FK & SV & HFM & Hcok & Hfl & Hhi & Hfp).
    clear Hcurve Hdar Hdc Hshw.
    pose proof (u64_range C) as HCr. pose proof (u64_range sp) as Hspr.
    pose proof placement as (F1 & F2 & F3 & F4 & F5 & G1 & G2 & G3 & G4 & G5 & FF & AA & SM & SR). pose proof quotients as HQ. hide HQ.
    clear FF AA G1 G2 G3 G4 G5.
    pose proof Hhdr as (_ & _ & _ & Hfslo & Hfshi & Hfsal). pose proof Hstk as [St1 St2]. pose proof Hch as [C1 C2]. app_facts.
    unfold CANON_D, AS_SB, FS_SIZE, FS_FRAMES0, FS_FRAMES_LEN, FS_FLAGS0, FS_FLAGS0_LEN, FS_FRAMES5, FS_HINT0,
           FS_SHFRAMES_LEN in *.
    pose proof (writable_frame SEGS mem M _ _ _ HFM WF) as WF'. pose proof (writable_frame SEGS mem M _ _ _ HFM WSF) as WSF'.
    pose proof (writable_frame SEGS mem M _ _ _ HFM Wfa) as Wfa'. pose proof (writable_frame SEGS mem M _ _ _ HFM Hwst) as Wst'.
    opaque_lets.
    set (E1 := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI')) ++ junk_vals regs ++ fjunk_vals fp0 ++ [Z_to_bv 64 F; Z_to_bv 64 fa]))
                   (blobs_ev [bs])).
    assert (HR : regs_ok E1 SRT R).
    { replace SRT with (sr_upds (sr_vars 0)
        [(3, EVar 67); (4, ELit TP); (8, EVar 66); (18, EVar 128); (22, EVar 128);
         (23, EAlu ALU_ADD (EAlu ALU_SRL (EVar 128) (ELit 3)) (ELit SB)); (26, EVar 90); (27, EVar 91)]%bv) by (vm_compute; reflexivity).
      apply regs_ok_pins; [exact (regs_ok_vars [] R _ (blobs_ev [bs]))|].
      repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd edenot]; ev_simpl E1; rewrite_getr; rewrite ?Hsp; reflexivity. }
    assert (HF : fregs_ok E1 SFT (fp_regs (FPState:=FPI'))).
    { replace SFT with (sr_upds (sfr_vars 32)
        [(9, EVar 105); (18, EVar 114); (19, EVar 115); (20, EVar 116); (21, EVar 117); (22, EVar 118); (23, EVar 119);
         (24, EVar 120); (25, EVar 121); (26, EVar 122); (27, EVar 123)]%bv) by (vm_compute; reflexivity).
      apply fregs_ok_pins; [exact (fregs_ok_vars (junk_vals R) (fp_regs (FPState:=FPI')) _ (blobs_ev [bs]))|].
      repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd edenot]; ev_simpl E1; apply FK; first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)]. }
    assert (HR0 : id (regs_ok E1 (sr_vars 64) regs))
      by exact (regs_ok_vars (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI'))) regs _ (blobs_ev [bs])).
    assert (HF0 : id (fregs_ok E1 (sfr_vars 96) fp0))
      by exact (fregs_ok_vars (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI')) ++ junk_vals regs) fp0 _ (blobs_ev [bs])).
    destruct SV as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12). unfold cell64, LibDefs.cell in *.
    destruct Wst' as (_ & _ & _ & Wst4). destruct WF' as (_ & _ & _ & WF4). destruct WSF' as (_ & _ & _ & WSF4). destruct Wfa' as (_ & _ & _ & Wfa4).
    assert (HK : know_ok SEGS E1 M KNT).
    { unfold KNT, know_ok.
      repeat lazymatch goal with |- Forall _ (_ :: _) => constructor | |- Forall _ [] => constructor end.
      all: lazymatch goal with |- Forall _ _ => fail | _ => idtac end.
      Ltac kw H := lazymatch goal with |- kentry_ok _ ?E0 _ _ =>
                   eapply (kword_intro SEGS _ _ (EVar 66) sp);
                   [cbn [edenot]; ev_simpl E0; exact Hsp | cbn [edenot]; ev_simpl E0; reflexivity | rlia | rlia | rlia | rlia |
                    lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
                      lazymatch type of H with rdn _ _ (Z_to_bv 64 ?b) _ = _ => replace a with b by rlia; rewrite_getr; exact H end end] end.
      - apply kalign_intro; [rlia|]. cbn [edenot]; ev_simpl E1. rewrite Hsp. exact Hal16.
      - apply krange_intro. cbn [edenot]; ev_simpl E1. rewrite Hsp. rlia.
      - apply (kwr_intro SEGS E1 M (EVar 66) sp (-2272) 2272); [cbn [edenot]; ev_simpl E1; exact Hsp | rlia | rlia | rlia |].
        replace (bv_unsigned sp + -2272)%Z with (bv_unsigned sp - 2272)%Z by rlia. exact Wst4.
      - kw V1. - kw V2. - kw V3. - kw V4. - kw V5. - kw V6. - kw V7. - kw V8. - kw V9. - kw V10. - kw V11. - kw V12.
      - apply kalign_intro; [rlia|]. cbn [edenot]; ev_simpl E1. rewrite u_small by clia. exact F3.
      - apply krange_intro. cbn [edenot]; ev_simpl E1. rewrite u_small by clia. rlia.
      - apply (kwr_intro SEGS E1 M (EVar 128) (Z_to_bv 64 F) 0 64); [cbn [edenot]; ev_simpl E1; reflexivity | rewrite u_small by clia; rlia | rlia | rewrite u_small by clia; rlia |].
        rewrite u_small, Z.add_0_r by rlia. exact WF4.
      - replace SB with (SB + 0)%Z by rlia. eapply (kwr_shadow_intro SEGS E1 M (EVar 128) (Z_to_bv 64 F) 0 8);
          [cbn [edenot]; ev_simpl E1; reflexivity | rlia | rlia | rewrite u_small by clia; qlia | rewrite u_small, Z.add_0_r by rlia; unfold SB; exact WSF4].
      - eapply (kword_intro SEGS E1 M (EVar 128) (Z_to_bv 64 F) 56 8 (EVar 129) (Z_to_bv 64 fa));
          [cbn [edenot]; ev_simpl E1; reflexivity | cbn [edenot]; ev_simpl E1; reflexivity | rlia | rlia
          | rewrite u_small by clia; rlia | rewrite u_small by clia; rlia | rewrite u_small by clia; unfold acell in Hfp; exact Hfp].
      - apply krange_intro. cbn [edenot]; ev_simpl E1. rewrite u_small by clia. rlia.
      - apply (kwr_intro SEGS E1 M (EVar 129) (Z_to_bv 64 fa) 0 1); [cbn [edenot]; ev_simpl E1; reflexivity | rewrite u_small by clia; rlia | rlia | rewrite u_small by clia; rlia |].
        rewrite u_small, Z.add_0_r by rlia. exact Wfa4.
      - cbn [kentry_ok]; unfold estart; cbn [a_base a_off edenot]; ev_simpl E1. rewrite !u_small by clia. rlia.
      - kdisj_place. - kdisj_place. - kdisj_place. - kdisj_place. - kdisj_place. - kdisj_place. }
    run_fp 100%nat (@nil Z) noscr true.
    assert (HFR3 : frame_mod M M0 [(Z_to_bv 64 (2147450880 + F / 8), 8%Z); (Z_to_bv 64 F, 8%Z); (Z_to_bv 64 fa, 1%Z)]).
    { rewrite EQM. frame_of_log [(SA (EAlu ALU_SRL (EVar 128) (ELit 3)) SB, 8%Z); (SA (EVar 128) 0, 8%Z); (SA (EVar 129) 0, 1%Z)]. }
    fin_ret. unfold Q, QP. post_regs.
    split; [|split; [|split]].
    - eapply frame_TGT_app; [exact HFM | exact HFR3 | solve_incl].
    - eapply curve_ok_frame; [exact HFR3 | exact Hcok | rlia | rlia | solve_apart_q].
    - apply (fs_flags0_but_clear fs [] M0 (pos0 h)).
      + eapply (fs_flags0_but_frame fs [pos0 h] [pos0 h] M M0); [exact HFR3 | exact Hfl | rlia | unfold FS_SIZE; rlia |].
        intros i Hi Hni. split; [exact Hni|]. unfold FS_FLAGS0_LEN in Hi. unfold FS_FLAGS0.
        assert (i <> pos0 h) by (intros ->; apply Hni; left; reflexivity).
        pose proof (eq_sym Efa') as Efa2. unfold FS_FLAGS0 in Efa2. solve_apart_q.
      + rewrite EQM.
        lazymatch type of HK with know_ok _ ?E2 _ _ =>
          replace (fs + FS_FLAGS0 + pos0 h)%Z with (bv_unsigned (edenot E2 (EVar 129)) + 0)%Z
            by (cbn [edenot]; ev_simpl E2; rewrite u_small by clia; rewrite <- Efa'; rlia);
          eapply (mem_denot_lzK_cover SEGS E2 _ _ _ _ (EVar 129) 0 1%nat HK HLF); [vm_compute; reflexivity | | | rlia];
          cbn [edenot]; ev_simpl E2; rewrite u_small by clia; rlia end.
    - destruct Hhi as [h' Hh']. exists h'. unfold FS_HINT0. eapply acellw_frame; [exact HFR3 | exact Hh' | rlia | rlia | solve_apart_q].
  Qed.

  Theorem canon_run : runs_to SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x86d9c) mem rom) Q.
  Proof using ceil Hfit Hsm Hmemset FPI regs mem rom ret sp C data t8 t16 h n len fs bs ch Hra Hret Hsp Htp Hc Hal16 Hstk Hwst Hshs Hcal Hch Hwc Hshc Hshw Hcar Hn32 Hn Ht8 Ht16 Hcurve Hdok Hdar Hdc Henv Hhdr Hfsw Hhint Hflags.
    assert (HR : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [bs])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [bs])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof (u64_range C) as HCr. pose proof (u64_range sp) as Hspr. pose proof (u64_range data) as Hdr. pose proof (u64_range h) as Hhr.
    pose proof placement as (F1 & F2 & F3 & F4 & F5 & G1 & G2 & G3 & G4 & G5 & FF & AA & SM & SR). pose proof quotients as HQ. hide HQ.
    hide FF. hide AA.
    pose proof Hhdr as (_ & _ & _ & Hfslo & Hfshi & Hfsal). pose proof Hstk as [St1 St2]. pose proof Hch as [C1 C2]. app_facts.
    pose proof Hfsw as (Wh0 & _ & Wfl0 & _ & Wfr0 & _ & Wsh0 & _).
    pose proof Hdok as (Hdok0 & Hdh & Hdal & Hshd). pose proof Hdok0 as (Hlen & Hbs & Hdnz & Hdhi & Hblob).
    unfold CANON_D, AS_SB, FS_SIZE, FS_FRAMES0, FS_FRAMES_LEN, FS_FLAGS0, FS_FLAGS0_LEN, FS_FRAMES5, FS_HINT0,
           FS_SHFRAMES_LEN in *.
    assert (Hpos : (0 <= pos0 h < 16384)%Z) by (unfold pos0; apply Z.mod_pos_bound; rlia).
    assert (Hshs' : shz mem (bv_unsigned sp - 2272) 284) by exact Hshs.
    pose proof Hdh as [D1 D2]. 
    hide Hdar. hide Hdc.
    opaque_lets.
    pin_reg HR (4%bv:reg) (ELit TP) by (regv HR (4%bv:reg); exact Htp).
    (* [comment removed for export] *)
    assert (Hcok : curve_ok SEGS mem data len (bv_unsigned C)).
    { exists n, t8, t16. split; [split; [exact Hn32| unfold LibDefs.cell; rewrite <- (Z.add_0_r (bv_unsigned C)); exact Hn]|].
      split; [exact Ht8|]. split; [exact Ht16|]. exact Hcurve. }
    hide Hcurve.
    pose proof kn0_ok as HK. unfold kn0, kn0v1, lit8 in HK.
    (* [comment removed for export] *)
    run_fp 40%nat [0x86de0%Z] noscr true.
    pin_reg HR (2%bv:reg) (EVar 64) by (regv HR (2%bv:reg); cbn [edenot]; ev_simpl E; rewrite Hsp; reflexivity).
    pin_reg HR (9%bv:reg) (EVar 64) by (regv HR (9%bv:reg); cbn [edenot]; ev_simpl E; rewrite Hsp; reflexivity).
    assert (HFR1 : frame_mod mem M [(Z_to_bv 64 (bv_unsigned sp - 128), 128%Z)]) by (rewrite EQM; frame_of_log [(SA (EVar 2) (-128), 128%Z)]).
    clear EQM HLF.
    (* [comment removed for export] *)
    run_fp 30%nat [0x3c8d4%Z] noscr false.
    eapply rt_call.
    { eapply (Hsm fs h ch FPI0 R M rom (Z_to_bv 64 0x86e08)).
      - regv HR (1%bv:reg); reflexivity.
      - apply ret_ok_even; rewrite u_small by clia; reflexivity.
      - unfold stkmalloc_pre; cbv zeta; cbn [al_abi as_asan aa_tp asan_abi];
        unfold sm_frame, sm_flag, sm_pos, FS_FRAMES0, FS_FLAGS0, AS_SB;
        rewrite EF, Efa; replace (fs + 8 * 0)%Z with (fs + 0)%Z by rlia; change (64 / 8)%Z with 8%Z.
        split; [regv HR (4%bv:reg); reflexivity|].
        split; [eapply (as_env_frame SEGS ceil asan_abi fs ch mem M); [exact asan_abi_low | ceil_lo | fs_app | exact HFR1 | | exact Henv];
                constructor; [|constructor]; unfold env_safe; cbn [fst snd]; rewrite u_small by clia; rlia|].
        split; [eapply (fs_hdr_frame SEGS ceil asan_abi fs mem M); [exact asan_abi_low | ceil_lo | exact HFR1 | | | exact Hhdr];
                [constructor; [|constructor]; unfold env_safe; cbn [fst snd]; rewrite u_small by clia; rlia
                | unfold FS_SSL; solve_apart]|].
        split; [eapply acellw_frame; [exact HFR1 | exact Hhint | rlia | rlia | solve_apart]|].
        split; [rewrite (byte_frame mem M _ _ HFR1) by (first [rlia | solve_apart]); rewrite <- Efa'; unfold FS_FLAGS0;
                apply (Hflags (pos0 h)); [unfold FS_FLAGS0_LEN; rlia | intros []]|].
        split; [eapply writable_frame; [exact HFR1|exact Whint]|].
        split; [eapply writable_frame; [exact HFR1|exact Wfa]|].
        split; [eapply writable_frame; [exact HFR1|exact WF]|].
        split; [eapply writable_frame; [exact HFR1|exact WSF]|].
        exists S1w; split; [regv HR (2%bv:reg); reflexivity|].
        unfold as_frame, stackish; fold S1.
        split; [rlia|]. split; [apply (mod_down S1 16 2); [rlia|rlia|exact SM32]|].
        eapply writable_frame; [exact HFR1|]. eapply writable_sub; [exact Hwst|rlia|rlia|rlia]. }
    cbv beta. intros FPI1 regs1 mem1 (Hkeep & Hfkeep & Hpost).
    unfold stkmalloc_post in Hpost; cbv zeta in Hpost; unfold sm_frame, sm_flag, sm_pos, FS_FRAMES0, FS_FLAGS0, AS_SB in Hpost.
    rewrite EF, Efa in Hpost.
    replace (fs + 8 * 0)%Z with (fs + 0)%Z in Hpost by rlia. change (64 / 8)%Z with 8%Z in Hpost.
    replace (F + 64 - 8)%Z with (F + 56)%Z in Hpost by rlia.
    destruct Hpost as (Ha0 & Hfr & Hh1 & Hfp).
    assert (HR2 : getr R 2 = S1w) by (regv HR (2%bv:reg); cbn [edenot]; ev_simpl E; reflexivity).
    rewrite HR2 in Hfr. fold S1 in Hfr. clear HR2.
    unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep. after_call Hkeep Hfkeep FPI1. clear Hkeep Hfkeep.
    kframe HK Hfr [(SA (EVar 64) (-208), 208%Z); (SA (EVar 68) 0, 8%Z); (SA (EVar 71) 0, 1%Z); (SA (EVar 70) 24, 8%Z);
                   (SA (EVar 70) 56, 8%Z); (SA (EAlu ALU_SRL (EVar 70) (ELit 3)) SB, 8%Z)].
    (* [comment removed for export] *)
    pin_reg HR (10%bv:reg) (EVar 70) by (regv HR (10%bv:reg); cbn [edenot]; ev_simpl_goal; exact Ha0).
    kn_prefix HK [KWr (SA (EVar 70) 0) 64; KWr (SA (EAlu ALU_SRL (EVar 70) (ELit 3)) SB) 8; KWord (SA (EVar 70) 56) 8 (EVar 71); KWr (SA (EVar 71) 0) 1].
    { apply (kwr_intro SEGS _ mem1 (EVar 70) (Z_to_bv 64 F) 0 64);
        [cbn [edenot]; ev_simpl_goal; reflexivity | rewrite u_small by clia; rlia | rlia | rewrite u_small by clia; rlia
        | rewrite u_small, Z.add_0_r by rlia; eapply writable_frame; [exact Hfr |]; eapply writable_frame; [exact HFR1 | exact WF]]. }
    { replace SB with (SB + 0)%Z by rlia; eapply (kwr_shadow_intro SEGS _ mem1 (EVar 70) (Z_to_bv 64 F) 0 8);
        [cbn [edenot]; ev_simpl_goal; reflexivity | rlia | rlia | rewrite u_small by clia; qlia
        | rewrite u_small, Z.add_0_r by rlia; unfold SB; eapply writable_frame; [exact Hfr |]; eapply writable_frame; [exact HFR1 | exact WSF]]. }
    { eapply (kword_intro SEGS _ mem1 (EVar 70) (Z_to_bv 64 F) 56 8 (EVar 71) (Z_to_bv 64 fa));
        [cbn [edenot]; ev_simpl_goal; reflexivity | cbn [edenot]; ev_simpl_goal; reflexivity | rlia | rlia
        | rewrite u_small by clia; rlia | rewrite u_small by clia; rlia | rewrite u_small by clia; unfold acell in Hfp; exact Hfp]. }
    { apply (kwr_intro SEGS _ mem1 (EVar 71) (Z_to_bv 64 fa) 0 1);
        [cbn [edenot]; ev_simpl_goal; reflexivity | rewrite u_small by clia; rlia | rlia | rewrite u_small by clia; rlia
        | rewrite u_small, Z.add_0_r by rlia; eapply writable_frame; [exact Hfr |]; eapply writable_frame; [exact HFR1 | exact Wfa]]. }
    (* [comment removed for export] *)
    pose proof (frame_mod_trans _ _ _ _ _ HFR1 Hfr) as HFR2. cbn [app] in HFR2.
    destruct (unhide Hcurve) as [Hn0 | (Hnr & Hsome & H8 & H16)]; clear Hcurve.
    - (* [comment removed for export] *)
      kn_prefix HK [KRange (EVar 65) 0 0]. { apply krange_intro; cbn [edenot]; ev_simpl_goal; rewrite u_small by clia; rlia. }
      run_fp 250%nat (@nil Z) noscr true.
      assert (HFR3 : frame_mod mem1 M0 [(Z_to_bv 64 F, 24%Z); (Z_to_bv 64 (2147450880 + F / 8), 8%Z); (Z_to_bv 64 (S1 + 16), 8%Z); (Z_to_bv 64 fa, 1%Z)]).
      { rewrite EQM. frame_of_log [(SA (EVar 70) 0, 24%Z); (SA (EAlu ALU_SRL (EVar 70) (ELit 3)) SB, 8%Z); (SA (EVar 64) 16, 8%Z); (SA (EVar 71) 0, 1%Z)]. }
      fin_ret. unfold Q, QP. post_regs.
      split; [|split; [|split]].
      * (* [comment removed for export] *)
        eapply frame_mod_incl; [| exact (frame_mod_trans _ _ _ _ _ HFR2 HFR3)]. cbn [app]. solve_incl.
      * (* [comment removed for export] *)
        kcell HK (EVar 10) 0%Z 4%nat (EExt false 0 4 (EVar 65)) HC0. rewrite ext_val_zx4_lit in HC0 by rlia.
        kcell HK (EVar 10) 8%Z 8%nat (EVar 66) HC8. kcell HK (EVar 10) 16%Z 8%nat (EVar 67) HC16.
        exists n, t8, t16. split; [split; [exact Hn32| unfold LibDefs.cell; rewrite <- (Z.add_0_r (bv_unsigned C)); exact HC0]|].
        split; [exact HC8|]. split; [exact HC16|]. left; exact Hn0.
      * (* [comment removed for export] *)
        apply (fs_flags0_but_clear fs [] M0 (pos0 h)).
        -- eapply (fs_flags0_but_frame fs [] [pos0 h] mem M0);
             [exact (frame_mod_trans _ _ _ _ _ HFR2 HFR3) | exact Hflags | rlia | unfold FS_SIZE; rlia |].
           intros i Hi Hni. split; [intros []|]. unfold FS_FLAGS0_LEN in Hi. unfold FS_FLAGS0.
           assert (i <> pos0 h) by (intros ->; apply Hni; left; reflexivity).
           cbn [app]. pose proof (eq_sym Efa') as Efa2. unfold FS_FLAGS0 in Efa2. solve_apart_q.
        -- rewrite EQM.
           lazymatch type of HK with know_ok _ ?E1 _ _ =>
             replace (fs + FS_FLAGS0 + pos0 h)%Z with (bv_unsigned (edenot E1 (EVar 71)) + 0)%Z
               by (cbn [edenot]; ev_simpl E1; rewrite u_small by clia; rewrite <- Efa'; rlia);
             eapply (mem_denot_lzK_cover SEGS E1 _ _ _ _ (EVar 71) 0 1%nat HK HLF); [vm_compute; reflexivity | | | rlia];
             cbn [edenot]; ev_simpl E1; rewrite u_small by clia; rlia end.
      * (* [comment removed for export] *)
        exists (Z_to_bv 64 (bv_unsigned h + 1)). unfold FS_HINT0. eapply acellw_frame; [exact HFR3 | exact Hh1 | rlia | rlia | solve_apart_q].
    - (* [comment removed for export] *)
      hide Hsome. hide H8. hide H16.
      kn_prefix HK [KRange (EVar 65) 2 (2 ^ 24)]. { apply krange_intro; cbn [edenot]; ev_simpl_goal; rewrite u_small by clia; rlia. }
      run_fp 120%nat [0x869e8%Z] noscr true.
      assert (HFR3 : frame_mod mem1 M0 [(Z_to_bv 64 F, 24%Z); (Z_to_bv 64 (2147450880 + F / 8), 8%Z); (Z_to_bv 64 (S1 + 16), 8%Z);
                                     (Z_to_bv 64 (S1 + 28), 4%Z); (Z_to_bv 64 (F + 32), 4%Z)]).
      { rewrite EQM. frame_of_log [(SA (EVar 70) 0, 24%Z); (SA (EAlu ALU_SRL (EVar 70) (ELit 3)) SB, 8%Z); (SA (EVar 64) 16, 8%Z);
                                   (SA (EVar 64) 28, 4%Z); (SA (EVar 70) 32, 4%Z)]. }
      clear EQM HLF.
      pose proof (frame_mod_trans _ _ _ _ _ HFR2 HFR3) as HFR4. cbn [app] in HFR4.
      assert (HFT4 : frame_mod mem M0 TGT) by (eapply frame_mod_incl; [|exact HFR4]; solve_incl).
      (* [comment removed for export] *)
      assert (ENVS4 : Forall (env_safe ceil fs) [(Z_to_bv 64 (bv_unsigned sp - 128), 128%Z); (Z_to_bv 64 (S1 - 208), 208%Z); (Z_to_bv 64 (fs + 0), 8%Z);
        (Z_to_bv 64 fa, 1%Z); (Z_to_bv 64 (F + 24), 8%Z); (Z_to_bv 64 (F + 56), 8%Z); (Z_to_bv 64 (2147450880 + F / 8), 8%Z);
        (Z_to_bv 64 F, 24%Z); (Z_to_bv 64 (2147450880 + F / 8), 8%Z); (Z_to_bv 64 (S1 + 16), 8%Z); (Z_to_bv 64 (S1 + 28), 4%Z); (Z_to_bv 64 (F + 32), 4%Z)]).
      { unfold env_safe, FS_SIZE. repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
          unfold AS_SB; rewrite ?u_small by first [clia | qlia]; div8_facts; first [clia | qlia | dlia]. }
      kcell HK (EVar 64) 28%Z 4%nat (ELit 0) HCc.
      kcell HK (EAlu ALU_SRL (EVar 70) (ELit 3)) (SB + 4)%Z 1%nat (ELit 4) HCf.
      kcell HK (EVar 10) 0%Z 4%nat (EExt false 0 4 (EVar 65)) HCn. rewrite ext_val_zx4_lit in HCn by rlia.
      kcell HK (EVar 10) 8%Z 8%nat (EVar 66) HC8. kcell HK (EVar 10) 16%Z 8%nat (EVar 67) HC16.
      eapply rt_call.
      { eapply (Hfit data len bs S1w C n t8 t16 fs h ch FPI2 R0 M0 rom (Z_to_bv 64 0x86eec)).
        - regv HR (1%bv:reg). reflexivity.
        - apply ret_ok_even. rewrite u_small by clia. reflexivity.
        - unfold fitlin_pre_as. cbv zeta. cbn [al_abi as_asan aa_tp asan_abi]. rewrite EF0. fold h1. fold S1.
          unfold FITLIN_D, FS_HINT0, FS_FRAMES5, FS_SIZE, AS_SB.
          split; [regv HR (2%bv:reg); reflexivity|].
          split; [regv HR (10%bv:reg); rewrite_getr; reflexivity|].
          split; [regv HR (11%bv:reg); reflexivity|].
          split; [regv_lin HR (12%bv:reg); fold S1; apply (f_equal (Z_to_bv 64)); rlia|].
          split; [regv_lin HR (13%bv:reg); fold S1; apply (f_equal (Z_to_bv 64)); rlia|].
          split; [regv_lin HR (14%bv:reg); rewrite u_small by clia; apply (f_equal (Z_to_bv 64)); rlia|].
          split; [regv HR (4%bv:reg); reflexivity|].
          split; [exact SM32|].
          split; [unfold stackish; rlia|].
          split; [eapply writable_frame; [exact HFR4|]; eapply writable_sub; [exact Hwst|rlia|rlia|rlia]|].
          split. { eapply shz_frame; [exact HFR4 | eapply (shz_sub _ _ _ _ _ Hshs'); [| rlia | rlia | rlia] | rlia | rlia |].
                   - apply mod_add_multiple; [rlia | apply (mod_down S1 8 4); [rlia|rlia|exact SM32] | reflexivity].
                   - replace (S1 + 24)%Z with (S1 + 8 * 3)%Z by rlia. rewrite div8_addk. solve_apart_q. }
          split; [exists (Z_to_bv 64 0); unfold LibDefs.cell; exact HCc|].
          split; [eapply writable_frame; [exact HFR4|]; eapply writable_sub; [exact WF|rlia|rlia|rlia]|].
          split; [unfold acell; rewrite div8_F32; replace (2147450880 + (F / 8 + 4))%Z with (F / 8 + (SB + 4))%Z by (unfold SB; rlia); exact HCf|].
          split; [exact Hcal|]. split; [exact Hch|].
          split. { eapply shz_frame; [exact HFR4 | eapply (shz_sub _ _ _ _ _ Hshc); [exact Hcal|rlia|rlia|rlia] | rlia | rlia | solve_apart_q]. }
          split; [rlia|]. split; [rlia|].
          split. { unfold table_curve. split; [split; [exact Hn32 | unfold LibDefs.cell; rewrite <- (Z.add_0_r (bv_unsigned C)); exact HCn]|].
                   split; [exact HC8|]. split; [exact HC16|]. split; [exact Hnr|]. split; [exact (unhide H8)|]. split; [exact (unhide H16)|]. exact (unhide Hsome). }
          split. { pose proof (unhide Hdar) as Hdar1.
                   split; [eapply data_ok_frame; [exact HFR4 | exact Hdok0 | solve_apart_q]|]. split; [exact Hdh|]. split; [exact Hdal|].
                   eapply shdata_frame; [exact HFR4 | exact Hshd | rlia | rlia | rlia | unfold SB; solve_apart_q]. }
          split; [exact (unhide Hdar)|].
          split; [eapply (as_env_frame SEGS ceil asan_abi fs ch mem M0); [exact asan_abi_low | ceil_lo | fs_app | exact HFR4 | exact ENVS4 | exact Henv]|].
          split; [eapply (fs_hdr_frame SEGS ceil asan_abi fs mem M0); [exact asan_abi_low | ceil_lo | exact HFR4 | exact ENVS4 | unfold FS_SSL; solve_apart_q | exact Hhdr]|].
          split; [eapply fs_writable_frame; [exact HFR4 | exact Hfsw]|].
          split; [eapply acellw_frame; [exact HFR3 | exact Hh1 | rlia | rlia | solve_apart_q]|].
          eapply (fs_flags0_but_frame fs [] [pos0 h] mem M0); [exact HFR4 | exact Hflags | rlia | unfold FS_SIZE; rlia |].
          intros i Hi Hni. split; [intros []|]. unfold FS_FLAGS0_LEN in Hi. unfold FS_FLAGS0.
          assert (i <> pos0 h) by (intros ->; apply Hni; left; reflexivity).
          pose proof (eq_sym Efa') as Efa2. unfold FS_FLAGS0 in Efa2. solve_apart_q. }
      cbv beta. intros FPI3 regs3 mem3 (Hkeep & Hfkeep & Hpost).
      unfold fitlin_post_as in Hpost. cbv zeta in Hpost. rewrite EF0 in Hpost. fold h1 in Hpost. rewrite EFf, Efaf in Hpost. fold S1 in Hpost.
      unfold FITLIN_D, FS_HINT0, AS_SB in Hpost. change (432 + 32)%Z with 464%Z in Hpost.
      destruct Hpost as (Hfr5 & (wc & HWc) & (wf & HWf) & Hh2 & Hfaf & (r & Hr10 & Hrr)).
      clear HCc HCf HCn HC8 HC16 ENVS4.
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep. after_call Hkeep Hfkeep FPI3. clear Hkeep Hfkeep.
      kframe HK Hfr5 [(SA (EVar 64) (-432), 464%Z); (SA (EVar 70) 32, 4%Z); (SA (EVar 68) 0, 8%Z); (SA (EVar 73) 0, 1%Z);
                      (SA (EVar 72) 0, 64%Z); (SA (EAlu ALU_SRL (EVar 72) (ELit 3)) SB, 8%Z)].
      assert (HFT5 : frame_mod mem mem3 TGT) by (eapply frame_TGT_app; [exact HFT4 | exact Hfr5 | solve_incl]).
      env_extend [wc; wf].
      unfold LibDefs.cell in HWc, HWf.
      kn_prefix HK [KWord (SA (EVar 64) 28) 4 (EVar 202); KWord (SA (EVar 70) 32) 4 (EVar 203)].
      { eapply (kword_intro SEGS _ mem3 (EVar 64) S1w 28 4 (EVar 202) wc); [cbn [edenot]; ev_simpl_goal; reflexivity | cbn [edenot]; ev_simpl_goal; reflexivity
          | rlia | rlia | fold S1; rlia | fold S1; rlia | fold S1; exact HWc]. }
      { eapply (kword_intro SEGS _ mem3 (EVar 70) (Z_to_bv 64 F) 32 4 (EVar 203) wf); [cbn [edenot]; ev_simpl_goal; reflexivity | cbn [edenot]; ev_simpl_goal; reflexivity
          | rlia | rlia | rewrite u_small by clia; rlia | rewrite u_small by clia; rlia | rewrite u_small by clia; exact HWf]. }
      (* [comment removed for export] *)
      assert (Hfl5 : fs_flags0_but fs [pos0 h] mem3).
      { apply (fs_flags0_but_clear fs [pos0 h] mem3 (pos0 h1)); [| rewrite Efaf; exact Hfaf].
        eapply (fs_flags0_but_frame fs [] [pos0 h1; pos0 h] mem mem3);
          [exact (frame_mod_trans _ _ _ _ _ HFR4 Hfr5) | exact Hflags | rlia | unfold FS_SIZE; rlia |].
        intros i Hi Hni. split; [intros []|]. unfold FS_FLAGS0_LEN in Hi. unfold FS_FLAGS0.
        assert (i <> pos0 h) by (intros ->; apply Hni; right; left; reflexivity).
        assert (i <> pos0 h1) by (intros ->; apply Hni; left; reflexivity).
        pose proof (eq_sym Efa') as Efa2. pose proof (eq_sym Efaf) as Efaf2. unfold FS_FLAGS0 in Efa2, Efaf2. cbn [app]. solve_apart_q. }
      assert (Hcok5 : curve_ok SEGS mem3 data len (bv_unsigned C)).
      { pose proof (unhide Hdc) as Hdc1. eapply curve_ok_frame; [exact (frame_mod_trans _ _ _ _ _ HFR4 Hfr5) | exact Hcok | rlia | rlia | cbn [app]; solve_apart_q]. }
      clear HWc HWf Hfaf.
      (* [comment removed for export] *)
      Ltac saved1 HK := lazymatch goal with |- rdn _ _ (Z_to_bv 64 (bv_unsigned sp - ?k)) 8 = _ =>
        lazymatch type of HK with know_ok _ _ _ ?kn =>
          let r := eval vm_compute in (kread SEGS kn (EVar 2) (- k)%Z 8%nat) in
          lazymatch r with Some ?v => let H := fresh "HS" in kcell HK (EVar 2) (-k)%Z 8%nat v H; rewrite ?Hra in H; exact H end end end.
      Ltac exit5 :=
        lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
        lazymatch goal with HR : regs_ok ?E1 ?sr R', HF : fregs_ok _ ?sfr (@fp_regs I), HK : know_ok _ _ M' _, HF0 : id (fregs_ok _ ?sfr0 ?fr0) |- _ =>
          apply tailQ; unfold TINV, SAVED;
          lift_id HF0 HF;
          repeat lazymatch goal with
          | |- getr R' _ = _ /\ _ => split; [regv HR ltac:(lazymatch goal with |- getr _ ?r = _ => r end); rewrite_getr; rewrite ?u_small by clia;
                                              first [reflexivity | apply (f_equal (Z_to_bv 64)); rlia] |]
          | |- (forall r, In r _ -> reg_get _ r = reg_get _ r) /\ _ =>
              split; [exact (fregs_same_on E1 sfr0 sfr fr0 _ [9;18;19;20;21;22;23;24;25;26;27]%bv HF0 HF ltac:(vm_compute; reflexivity))|]
          | |- (cell64 _ _ _ _ /\ _) /\ _ => split; [unfold cell64, LibDefs.cell; repeat split; saved1 HK |]
          | |- frame_mod mem M' TGT /\ _ => split; [assumption|]
          | |- curve_ok _ M' _ _ _ /\ _ => split; [assumption|]
          | |- fs_flags0_but _ _ M' /\ _ => split; [assumption|]
          | |- (exists h', acellw _ M' _ h') /\ _ => split; [eexists; eassumption|]
          | |- acell _ M' (F + 56) 8 fa => let H := fresh "HP" in kcell HK (EVar 70) 56%Z 8%nat (EVar 71) H; unfold acell; exact H
          end
        end end.
      run_fp 10%nat (@nil Z) noscr false.
      branch_case as Hb1. { exit5. }
      run_fp 10%nat (@nil Z) noscr false.
      branch_case as Hb2. { exit5. }
      run_fp 10%nat (@nil Z) noscr false.
      branch_case as Hb3. { exit5. }
      (* [comment removed for export] *)
      run_fp 40%nat [0x514d0%Z] noscr true.
      assert (HFR6 : frame_mod mem3 M1 [(Z_to_bv 64 (bv_unsigned C + 0), 12%Z)]) by (rewrite EQM; frame_of_log [(SA (EVar 10) 0, 12%Z)]).
      assert (HFT6 : frame_mod mem M1 TGT) by (eapply frame_TGT_app; [exact HFT5 | exact HFR6 | solve_incl]).
      clear EQM HLF.
      lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ => rename I into FPI8; rename R' into R8 end.
      eapply rt_call.
      { eapply (Hmemset (Z_to_bv 64 (bv_unsigned C + 12)) FPI8 R8 M1 rom (Z_to_bv 64 0x86f5c)).
        - regv HR (1%bv:reg). reflexivity.
        - apply ret_ok_even. rewrite u_small by clia. reflexivity.
        - unfold imemset_pre. cbn [Z.leb al_abi as_asan]. rewrite !(u_small (bv_unsigned C + 12)) by clia.
          split; [regv_lin HR (10%bv:reg); rewrite Hc; apply (f_equal (Z_to_bv 64)); rlia|].
          split; [regv HR (11%bv:reg); reflexivity|].
          split; [regv HR (12%bv:reg); reflexivity|].
          split; [apply mod8_mod4_12; exact Hcal|].
          split; [unfold heapish; plc|].
          split; [eapply writable_frame; [exact HFT6|]; eapply writable_sub; [exact Hwc|rlia|rlia|rlia]|].
          split. { eapply canon_shwz; [exact HFT6|].
                   pose proof (app_sh_lit _ _ (proj1 (proj2 (proj2 (proj2 Hhdr))))) as Fsh. unfold FS_SIZE, FS_FRAMES5 in *.
                   unfold TGT. repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
                   rewrite ?u_small by first [clia | qlia]; first [left; dlia | left; qlia | right; right; right; split; reflexivity]. }
          split. { eapply (env_cells_frame SEGS ceil asan_abi fs mem M1); [exact asan_abi_low | ceil_lo | fs_app | exact HFT6 | | exact (proj1 Henv)].
                   unfold TGT, env_safe, FS_SIZE, AS_SB. repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
                   rewrite ?u_small by first [clia | qlia]; div8_facts; first [clia | qlia | dlia]. }
          exists S1w. split; [regv HR (2%bv:reg); reflexivity|].
          unfold as_frame, stackish; fold S1.
          split; [rlia|]. split; [apply (mod_down S1 16 2); [rlia|rlia|exact SM32]|].
          eapply writable_frame; [exact HFT6|]. eapply writable_sub; [exact Hwst|rlia|rlia|rlia]. }
      cbv beta. intros FPI9 regs9 mem9 (Hkeep9 & Hfkeep9 & Hfr9 & Hz9 & _).
      rewrite !(u_small (bv_unsigned C + 12)) in Hz9 by clia.
      assert (HR2' : getr R8 2 = S1w) by (regv HR (2%bv:reg); cbn [edenot]; ev_simpl_goal; reflexivity).
      rewrite HR2' in Hfr9. fold S1 in Hfr9. clear HR2'.
      unfold regs_kept in Hkeep9. unfold fregs_kept in Hfkeep9. after_call Hkeep9 Hfkeep9 FPI9. clear Hkeep9 Hfkeep9.
      kframe HK Hfr9 [(SA (EVar 64) (-2128), 2128%Z); (SA (EVar 10) 12, 20%Z)].
      assert (HFT9 : frame_mod mem mem9 TGT) by (eapply frame_TGT_app; [exact HFT6 | exact Hfr9 | solve_incl]).
      (* [comment removed for export] *)
      kcell HK (EVar 10) 0%Z 4%nat (ELit 0) HC0. kcell HK (EVar 10) 8%Z 4%nat (ELit 1065353216) HC8.
      assert (HT8 : exists t8', LibDefs.cell SEGS mem9 (bv_unsigned C + 8) 8 t8').
      { eapply cell_of_rdn; [|rlia]. change 8%nat with (4 + 4)%nat. eapply rdn_app; [exact HC8|].
        rewrite u_small by clia. change (Z.of_nat 4) with 4%Z.
        replace (bv_unsigned C + 8 + 4)%Z with (bv_unsigned C + 12)%Z by rlia.
        apply rdn_zeros; [rlia|rlia|rlia|]. change (Z.of_nat 4) with 4%Z. intros i Hi. apply Hz9. rlia. }
      destruct HT8 as (t8' & HT8).
      assert (Hcok9 : curve_ok SEGS mem9 data len (bv_unsigned C)).
      { exists 0%Z, t8', (Z_to_bv 64 0). split; [|split; [exact HT8|split; [|left; reflexivity]]].
        * split; [rlia|]. unfold LibDefs.cell. rewrite Z.add_0_r in HC0. exact HC0.
        * unfold cell64. apply cell_zeros; [rlia|rlia|rlia|]. change (Z.of_nat 8) with 8%Z.
          intros i Hi. replace (bv_unsigned C + 16 + i)%Z with (bv_unsigned C + 12 + (i + 4))%Z by rlia. apply Hz9. rlia. }
      assert (Hfl9 : fs_flags0_but fs [pos0 h] mem9).
      { eapply (fs_flags0_but_frame fs [pos0 h] [pos0 h] M1 mem9); [exact Hfr9 | | rlia | unfold FS_SIZE; rlia |].
        - eapply (fs_flags0_but_frame fs [pos0 h] [pos0 h] mem3 M1); [exact HFR6 | exact Hfl5 | rlia | unfold FS_SIZE; rlia |].
          intros i Hi Hni. split; [exact Hni|]. unfold FS_FLAGS0_LEN in Hi. unfold FS_FLAGS0. solve_apart_q.
        - intros i Hi Hni. split; [exact Hni|]. unfold FS_FLAGS0_LEN in Hi. unfold FS_FLAGS0. solve_apart_q. }
      assert (Hh9 : acellw SEGS mem9 (fs + 0) (Z_to_bv 64 (bv_unsigned h + 2))).
      { eapply acellw_frame; [exact Hfr9 | | rlia | rlia | solve_apart_q]. eapply acellw_frame; [exact HFR6 | exact Hh2 | rlia | rlia | solve_apart_q]. }
      clear Hcok5 Hfl5 Hh2.
      exit5.
  Qed.
End Proof.

Theorem canonicalize_asan : forall ceil,
  fit_linear_contract_as SEGS as_asan ceil -> stkmalloc0_contract SEGS as_asan ceil -> imemset20_contract SEGS as_asan ceil ->
  canonicalize_contract_as SEGS as_asan ceil.
Proof.
  intros ceil Hfit Hsm Hmemset data len bs sp C fs h ch FPI regs mem rom ret Hra Hret PRE.
  destruct PRE as (Hsp & Hc & Htp & Hfr & Hshs & Hcal & Hch & Hwc & Hshc & Hshw & Har1 & Har2 & Hcurve & Hdok & Hdar & Hdc &
                   Henv & Hhdr & Hfsw & Hhint & Hflags).
  cbn [al_abi as_asan aa_tp asan_abi] in Htp.
  destruct Hfr as (Hstk & Hal16 & Hwst).
  destruct Hcurve as (n & t8 & t16 & [Hn32 Hn] & H8c & H16c & Hcase).
  unfold cell64, LibDefs.cell in H8c, H16c. unfold LibDefs.cell in Hn.
  pose proof (canon_run ceil Hfit Hsm Hmemset FPI regs mem rom ret sp C data t8 t16 h n len fs bs ch
                Hra Hret Hsp Htp Hc Hal16 Hstk Hwst Hshs Hcal Hch Hwc Hshc Hshw (conj Har1 Har2) Hn32
                ltac:(rewrite Z.add_0_r; exact Hn) H8c H16c Hcase Hdok Hdar Hdc Henv Hhdr Hfsw Hhint Hflags) as HRUN.
  destruct (runs_to_contract SEGS _ ret rom _ HRUN) as (FPI' & regs' & mem' & Hms & Hk1 & Hk2 & Hpost).
  exists FPI', regs', mem'. split; [exact Hms|]. split; [exact Hk1|]. split; [exact Hk2|]. exact Hpost.
Qed.
