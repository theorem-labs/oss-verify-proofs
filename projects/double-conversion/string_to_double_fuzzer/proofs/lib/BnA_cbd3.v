(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare BnModel BnMath BnMem BnDefs LibIface BnCbdLib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA AsRtLib AsZX AsZXTac AsZXDefs BnA_lib BnA_frame BnA_ads1 BnA_ads6 BnA_cbd1 BnA_cbd1b BnA_cbd2 BnA_ads7.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Ltac flia0 := first [ lia | match goal with H : hide _ |- _ => unfold hide in H; lia end | (unfold hide in *; lia) ].
#[local] Ltac BnA_ads1.flia ::= lf_once flia0.
Ltac inr0 H tac := cbn [In] in H; repeat (destruct H as [<-|H]; [tac|]); destruct H.
#[local] Ltac BnA_ads1.inr H tac ::= lf_once ltac:(inr0 H tac).
Import ListNotations. Import ZXA BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac inr H tac := cbn [In] in H; repeat (destruct H as [<-|H]; [tac|]); destruct H.
#[local] Ltac inr H tac ::= lf_once ltac:(inr0 H tac).
Ltac uw1 :=
  first [ lazymatch goal with |- exists r', _ /\ fst r' <= ?a /\ ?b <= snd r' => exists (a, b); split; [solve [in_list] | cbn [fst snd]; lia] end
        | eexists; split; [left; reflexivity | cbn [fst snd]; lia]
        | eexists; split; [right; left; reflexivity | cbn [fst snd]; lia]
        | eexists; split; [do 2 right; left; reflexivity | cbn [fst snd]; lia]
        | eexists; split; [do 3 right; left; reflexivity | cbn [fst snd]; lia]
        | eexists; split; [do 4 right; left; reflexivity | cbn [fst snd]; lia]
        | eexists; split; [do 5 right; left; reflexivity | cbn [fst snd]; lia]
        | eexists; split; [do 6 right; left; reflexivity | cbn [fst snd]; lia] ].
Ltac uwiden U := eapply unch_widen; [exact U|]; let rg := fresh "rg" in let H := fresh "Hrg" in intros rg H; cbn [fst snd]; inr H ltac:(uw1).

(* [comment removed for export] *)
Lemma swrap32_facts : forall a4 e, a4 mod 2 ^ 32 = e mod 2 ^ 32 -> -2047 <= e <= 2047 ->
  bv_swrap 32 (a4 mod M64) = e /\ bv_swrap 32 (0 - a4 mod M64) = - e.
Proof.
  intros a4 e H He. unfold bv_swrap, bv_wrap.
  change (bv_modulus 32) with 4294967296 in *. change (bv_half_modulus 32) with 2147483648 in *.
  change (2 ^ 32) with 4294967296 in *. change M64 with (4294967296 * 4294967296) in *.
  rewrite Z.rem_mul_r in * by lia. split; lia.
Qed.

(* [comment removed for export] *)
Ltac krest Y := refine (eq_trans Y _); rewrite Z_to_bv_bv_unsigned; reflexivity.

Theorem cbd_A : cbd_stmt_A.
Proof.
  unfold cbd_stmt_A.
  intros fx regs mem rom sp buf len expo e a4 FS ret f R1 Hra R2 Hsp16 Hfr Hsp2 R4 R10 Hb1 Hbapp Hb2 R11 R12 R13 R14 He4 Hlen Hle He Hdig Hdsh
    Dsp Dbsp RO RT GSH MCX TLS Hfs4096 Efs1 Efsapp Efs2 DspFS Hbw Hbws DFS DSHD L88 B96 FL0 STSH.
  clear Hbws STSH.
  unfold CBD_FR_A, CBD_ENTRY_A, app_mem, KHI_A, HIEND_A, IMGHI_A, LOSH_A in *.   (* [comment removed for export] *)
  pose proof (dsof_spec SEGS_A mem buf len ltac:(lia) Hdig) as DS. cbn zeta in DS. destruct DS as (Dlen & Dok & Dcells).
  set (ds := dsof SEGS_A mem buf (Z.to_nat len)) in *.
  assert (Hds : length ds = Z.to_nat len) by (unfold zlen in Dlen; lia).
  (* [comment removed for export] *)
  pose proof (Hbw (fs_hint FS 5, fs_hint FS 5 + 8) ltac:(right; left; reflexivity)) as Wh. rewrite fs_hint5 in Wh. cbn [fst snd] in Wh.
  pose proof (Hbw (FS5_FLAGS FS) ltac:(do 2 right; left; reflexivity)) as Wfl. unfold FS5_FLAGS in Wfl. rewrite fs_flag5 in Wfl. cbn [fst snd] in Wfl.
  pose proof (Hbw (FS5_FRAMES FS) ltac:(do 3 right; left; reflexivity)) as Wfr. unfold FS5_FRAMES in Wfr. rewrite fs_frame5 in Wfr. cbn [fst snd] in Wfr.
  change (2 ^ 20) with 1048576 in Wfr.
  clear Hbw.
  hide Wh; hide Wfl; hide Wfr; hide Dbsp; hide DspFS.
  assert (CE : cbdE buf len sp FS (buf / 8) ((buf + len - 1) / 8)).
  { constructor; unfold FS_LEN in *; try lia; first [exists (sp / 16); lia | exists (FS / 4096); lia | unfold hide in *; lia]. }
  clear Wh Wfl Wfr Dbsp DspFS.
  assert (DSH : dsh (buf / 8) ((buf + len - 1) / 8) mem).
  { intros q Hq. destruct (Z.le_gt_cases (8 * q) buf) as [Hle'|Hgt].
    - pose proof (Hdsh 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. unfold sh, SH_A in X.
      replace q with (buf / 8) by lia. eapply cellN_byte; [exact X | lia | lia | lia].
    - pose proof (Hdsh (8 * q - buf) ltac:(lia)) as X. unfold sh, SH_A in X.
      replace (2147450880 + (buf + (8 * q - buf)) / 8) with (2147450880 + q) in X by lia.
      eapply cellN_byte; [exact X | lia | lia | lia]. }
  clear Hdsh Hdig.
  pose proof (ret_ok_of_mod4 ret Hra) as Hret.
  rewrite <- (Z2bv_mod expo) in R12. rewrite <- (Z2bv_mod a4) in R14.
  pose proof (swrap32_facts a4 e He4 He) as [Hw4e Hw4n].
  assert (Hexr : 0 <= expo mod M64 < 2 ^ 64) by lia.
  assert (Hw4r : 0 <= a4 mod M64 < 2 ^ 64) by lia.
  (* [comment removed for export] *)
  destruct (cbd_pro_A rom buf len sp FS _ _ ds CE Hds regs mem ret f (expo mod M64) (a4 mod M64) R10 R11 R12 R13 R14 Hexr Hw4r R2 R1 R4
              RT RO GSH Dcells DSH Dsp MCX TLS DFS DSHD L88 B96 FL0)
    as (regsP & mP & p & F & g & MP & Hp & HF & HgF & P1 & P10 & P11 & P12 & P2 & P4 & P9 & P8 & P18 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27
        & KP & SL8 & S16 & S24 & SV & OBA & OBB & RTP & ROP & GSHP & DGP & DSHP & MCXP & TLSP & L88P & B96P & FL0P & FL1P & Q2040 & U0P & G0P).
  rewrite (Z2bv_mod expo) in P20.
  (* [comment removed for export] *)
  set (g0 := SHA + (FS + 5279744) / 8).
  assert (Hg0 : FS + 5279744 = 8 * (g0 - SHA)) by (subst g0; lia).
  (* [comment removed for export] *)
  destruct (cbd_core_A rom buf len sp FS _ _ ds p F g g0 expo e (a4 mod M64) f ret CE Hds Dok Hp HF HgF Hg0 Hle He Hw4r Hw4e Hw4n Hret (ads_A rom)
              regs regsP mP P1 P10 P11 P12 P2 P4 P9 P8 P18 P20 P21 P22 P23 P24 P25 P26 P27 S16 S24 SV OBA OBB RTP ROP GSHP DGP DSHP MCXP TLSP)
    as (regs' & m' & M' & X2 & X13 & K34 & X10 & FL' & U' & G').
  { eapply mem_def_grows; [exact G0P | exact Dsp]. }
  { eapply mem_def_grows; [exact G0P | exact DFS]. }
  { eapply mem_def_grows; [exact G0P | exact DSHD]. }
  { exact L88P. } { exact B96P. } { exact FL0P. } { exact FL1P. } { exact Q2040. } { exact R1. }
  exists regs', m'. split; [eapply msteps_trans; [exact MP | exact M']|].
  split.
  { (* [comment removed for export] *)
    destruct X13 as (Y1 & Y8 & Y9 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27). unfold savs in *. cbn [nth] in *.
    intros r Hr. unfold cs_regs in Hr. cbn [In] in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]].
    - refine (eq_trans X2 _). symmetry. exact R2.
    - refine (eq_trans (K34 3 ltac:(in_list)) _). exact (KP 3 ltac:(in_list)).
    - refine (eq_trans (K34 4 ltac:(in_list)) _). exact (KP 4 ltac:(in_list)).
    - krest Y8. - krest Y9. - krest Y18. - krest Y19. - krest Y20. - krest Y21. - krest Y22.
    - krest Y23. - krest Y24. - krest Y25. - krest Y26. - krest Y27. }
  split; [eexists; split; [exact X10 | unfold cbd; cbn zeta; apply compare_range]|].
  split; [exact FL'|].
  (* [comment removed for export] *)
  pose proof (csp1_facts buf len sp FS _ _ CE) as (Hs1 & _).
  apply mem_frame_of_unch; [| eapply mem_grows_trans; [exact G0P | exact G']].
  unfold cbd_writes, FS5_FLAGS, FS5_FRAMES, FS5_SHADOW, CBD_FR_A. rewrite fs_hint5, fs_flag5, fs_frame5. unfold sh, SH_A.
  change (2 ^ 20) with 1048576. change (2 ^ 17) with 131072.
  unfold CW in U'. unfold FS_LEN in *.
  eapply unch_trans; [uwiden U0P | uwiden U'].
Qed.
