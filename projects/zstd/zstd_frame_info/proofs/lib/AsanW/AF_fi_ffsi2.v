(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem Mem Frame.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import DrvAgree StrFun Stdio_pure.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg ABase RtCells AProto AMalloc_iface AHarness_iface AH_fi_iface AF_fi_kit AF_fi_chk AF_fi_chk3 AF_fi_cbs AF_fi_ffsi.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
#[using="Type"] Lemma zlen_skipnA : forall (bl : list Z) k, 0 <= k <= zlen bl -> zlen (skipn (Z.to_nat k) bl) = zlen bl - k.
Proof. intros bl k Hk. rewrite length_skipn. Local Ltac2 Set LiaHints.tbl := fun () => "0010=68659354476.4000004S2Hk".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma buf_atA_skipn : forall m S bl k, buf_atA m S bl -> 0 <= k <= zlen bl -> buf_atA m (S + k) (skipn (Z.to_nat k) bl).
Proof.
  intros m S bl k [B F] Hk. split.
  - rewrite <- (firstn_skipn (Z.to_nat k) bl) in B. rewrite map_app in B.
    apply (proj1 (bytes_at_app _ _ _ _ _)) in B. destruct B as [_ B].
    rewrite length_map, length_firstn in B. Local Ltac2 Set LiaHints.tbl := fun () => "0010=18147260095.8000004S2Hk".
replace (Z.of_nat (Nat.min (Z.to_nat k) (length bl))) with k in B by lia. exact B.
  - apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) F x). revert Hx. generalize (Z.to_nat k). clear.
    induction bl as [|y bl IH]; intros [|n] H; cbn in H; try exact H; [right; exact (IH n H)].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
(* [comment removed for export] *)
#[using="Type"] Lemma zx32_smallA : forall h, 0 <= h < 2^32 -> zx32 (Z_to_bv 64 h) = Z_to_bv 64 h.
Proof. intros h Hh. unfold zx32. Local Ltac2 Set LiaHints.tbl := fun () => "0020=50584898410.357703944554.3000004008S2HhS2Hh".
rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Notation f1c := (C1 (Z_to_bv 8 18446744073709551601)).
Notation f2c := (C1 (Z_to_bv 8 18446744073709551602)).
Notation f3c := (C1 (Z_to_bv 8 18446744073709551603)).
Notation f5c := (C1 (Z_to_bv 8 18446744073709551605)).
Notation f8c := (C1 (Z_to_bv 8 18446744073709551608)).
Notation z1c := (C1 (Z_to_bv 8 0)).
Notation c04 := (C1 (Z_to_bv 8 4)).
(* [comment removed for export] *)
Definition FSH3 : list cell := [f1c; f1c; f1c; f1c; z1c; z1c; z1c; z1c; z1c; z1c; f2c; f2c; f2c; f2c; z1c; c04; f3c; f3c; f3c; f3c] ++ FSHZ.
(* [comment removed for export] *)
#[using="Type"] Lemma fsh3_bp : forall m FF, rw_cells asegs m (Z.shiftr FF 3 + 2147450880) FSH3 -> FF mod 8 = 0 -> 0 <= FF ->
  rw_cells asegs m (shad (FF + 112)) [z1c; c04].
Proof.
  intros m FF SH F8 F0. unfold FSH3, FSHZ in SH.
  lazymatch type of SH with rw_cells _ _ _ ([?a; ?b; ?c; ?d; ?e; ?f; ?g; ?h; ?i; ?j; ?k; ?l; ?mm; ?nn; z1c; c04; ?o; ?p; ?q; ?r] ++ ?z) =>
    change ([a; b; c; d; e; f; g; h; i; j; k; l; mm; nn; z1c; c04; o; p; q; r] ++ z)
      with ([a; b; c; d; e; f; g; h; i; j; k; l; mm; nn] ++ [z1c; c04] ++ ([o; p; q; r] ++ z)) in SH end.
  apply (proj1 (rw_cells_appA _ _ _ _ _)) in SH. destruct SH as [_ SH]. apply (proj1 (rw_cells_appA _ _ _ _ _)) in SH. destruct SH as [SH _].
  cbn [cells_size csize Nat.add] in SH.
  replace (shad (FF + 112)) with (Z.shiftr FF 3 + 2147450880 + Z.of_nat 14); [exact SH|].
  unfold shad, ASHOFF. Local Ltac2 Set LiaHints.tbl := fun () => "0020=29784367838.654220130749.6000001005SS2F8".
rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Section S.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (SP lo : Z).
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SPT : SP + 16 < KEND.
  Hypothesis LOS : lo <= SP - 192 - AFI_STACK.
  Hypothesis LOC : ATOP <= lo.
  Variable RNG : footprint.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RI : rng_aimg RNG.
  Notation SPAz := (AF_fi_ffsi.SPAz SP).
  Notation FFRB := (AF_fi_ffsi.FFRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

  (* [comment removed for export] *)
  Variables (e7 e8 : word) (m : amem) (FF FLG S : Z) (bl : list Z) (D N R : Z).
  (* [comment removed for export] *)
  Definition W5 : list (Z * Z) :=
    [(SPAz - 16, SPAz); (SPAz + 16, SPAz + 32); (FF + 112, FF + 124);
     (Z.shiftr FF 3 + 2147450880 + 4, Z.shiftr FF 3 + 2147450880 + 10); (Z.shiftr FF 3 + 2147450880 + 14, Z.shiftr FF 3 + 2147450880 + 16);
     (R, R + 24); (FF, FF + 8)].
  Hypotheses (PLR : Forall (fun c => 0 <= c < 256) bl) (NB : zlen bl < 2^62).
  (* [comment removed for export] *)
  Hypothesis PAY : 0 < zlen bl -> D <= S /\ S + zlen bl <= D + N /\ N <= 2^40 /\ ablk D (D + N) /\ D mod 16 = 0 /\ rng RNG D N /\ rng RNG (shad D) (shlen (N + 7))
                   /\ (D + N <= FF \/ FF + 256 <= D).
  Hypotheses (R8 : R mod 8 = 0) (RLO : SP <= R) (RHI : R + 24 <= KEND) (RGR : rng RNG R 24) (RGRS : rng RNG (shad R) 3).
  Hypotheses (FH : ablk FF (FF + 256)) (FC : FF + 256 <= ATOP) (F256 : FF mod 256 = 0).
  Hypotheses (RF : rng RNG FF 256) (RSF : rng RNG (shad FF) 32).
  Hypotheses (GH : ablk FLG (FLG + 1)) (GC : FLG + 1 <= ATOP) (GF : FLG + 1 <= FF \/ FF + 256 <= FLG) (RG : rng RNG FLG 1).
  (* [comment removed for export] *)
  Hypotheses (PL0 : bytes_at asegs m S (map (Z_to_bv 8) bl)) (UNP0 : unpoisoned m S (S + zlen bl)) (RU0 : unpoisoned m R (R + 24)).

  (* [comment removed for export] *)
  Definition core (mx : amem) : Prop :=
    rw_cells asegs mx (SP + -104) FFRB /\ rw_cells asegs mx (FF + 248) [C8 (Z_to_bv 64 FLG)] /\
    rt_got mx /\ rt_shbase mx /\
    stk asegs mx (SPAz + 56) (SP + -104) /\ munch W5 m mx /\ wmono asegs m mx /\ mem_inv asegs mx.

  (* [comment removed for export] *)
  Definition POST_J : machine_state -> Prop :=
    fun ms' => exists (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31 : word)
                      (cl : list cell) (nb : list byte) (cs db : word) (m' : amem),
      ms' = MS (mkR y1 (Z_to_bv 64 SPAz) gp tp y5 y6 y7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) y10 y11 y12 y13 y14 y15 y16 y17
                   (Z_to_bv 64 FF) y19 y20 y21 y22 y23 y24 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) (Z_to_bv 64 2147450880)
                   y28 y29 y30 y31)
               FR (Z_to_bv 64 0x8182c) fc None m' (seg_rom asegs)
      /\ core m' /\ stk asegs m' lo SPAz
      /\ rw_cells asegs m' SPAz cl /\ cells_size cl = 56%nat
      /\ rw_cells asegs m' (Z.shiftr FF 3 + 2147450880) FSH1
      /\ rw_cells asegs m' FF [C8 (Z_to_bv 64 0x45e0360e); C8 (Z_to_bv 64 0x1a436); C8 (Z_to_bv 64 0x814a0)]
      /\ rw_cells asegs m' R [CB 8 nb; C8 cs; C8 db]
      /\ (bv_unsigned cs < 2^64 - 119 -> 1 <= bv_unsigned cs <= zlen bl).

  (* [comment removed for export] *)
  #[using="rc FH"] Lemma f2_bsf : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 32 <= 17594333495296.
  Proof.
    pose proof atop_range as ATR. pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). clear - ATR FHb FHc FHd.
    Local Ltac2 Set LiaHints.tbl := fun () => "0020=26987940019.629786463882.600000=00>S3ATR3FHb3FHcS".
rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
  #[using="rc lo SP16 LOS LOC RLO RHI FH"] Lemma f2_djr : disjoint_from W5 (shad R) (shad (R + 24 - 1) + 1 - shad R).
  Proof.
    pose proof atop_range as ATR. pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
    pose proof f2_bsf as BSF. pose proof (proj1 (spa160_propsA SP SP16)) as SPAB. unfold AFI_STACK in LOS. unfold KEND in RHI.
    unfold W5. clear - ATR FHb FHc FHu BSF LOC LOS RLO RHI SPAB.
    Local Ltac2 Set LiaHints.tbl := fun () => "0080>17792358713.1519287691209.1528062205174.1529788740460.1542847215913.155017153385.15 57359381492.1565933537932.1500000I00_01501601K01`02902JS3LOS3LOC3RLO3RHI3ATR3FHuS3LOS3LOC3RHI3ATR4SPABS3LOS3LOC3RHI3ATR4SPABSS3LOS3LOC3RLO3ATR3FHuS3LOS3LOC3RLO3ATR3FHuS3LOS3LOC3RLO3RHI3ATR3FHuS3LOS3LOC3RLO3ATR".
rewrite !shad_div, ?Z.shiftr_div_pow2 by lia. unfold ASHOFF. change (2^3) with 8. cbn [disjoint_from].
    repeat split; try exact I; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
  Ltac rsh8 k H :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with MUx : munch _ m mx |- _ =>
        let U := fresh "RU" in
        assert (U : unpoisoned mx R (R + 24)) by (eapply unpoisoned_munch; [exact RU0| exact MUx| exact f2_djr]);
        pose proof (chk8_zero mx R (R + 24) (R + k) U ltac:(lia) ltac:(lia) ltac:(clear - R8; unfold bx in R8; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia)) as H;
        let A := fresh "RA" in
        pose proof (shaccR RNG R k RGRS ltac:(lia) ltac:(lia) ltac:(lia)) as A;
        try replace (R + 0) with R in H, A by lia; clear U end end.

  Ltac prep2 :=
    pose proof atop_range as ATR; unfold KEND in SPT, RHI; unfold AFI_STACK in LOS;
    pose proof (proj1 (spa160_propsA SP SP16)) as SPAB;
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd); unfold AIMG_HI in FHa; pose proof FH as FHu; unfold ablk, AIMG_HI, KLS in FHu;
    pose proof (ablk_lin _ _ GH) as (GHa & GHb & GHc & GHd); unfold AIMG_HI in GHa; pose proof GH as GHu; unfold ablk, AIMG_HI, KLS in GHu;
    pose proof RSF as RSF'; replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in RSF' by (unfold shad, ASHOFF; lia);
    pose proof f2_bsf as BSF;
    assert (RSA : rng RNG SPAz 56) by (eapply rng_sub'; [exact RSTK| lia]);
    pose proof (bytes_at_bound _ _ _ _ PL0) as BB; rewrite length_map in BB;
    boxH SP16; boxH F256; boxH R8; boxH PL0;   (* [comment removed for export] *)
    (* [comment removed for export] *)
    unfold AF_fi_ffsi.FFRB, FFHDR, FSH1, FSH2, FSH3, FSHZ in *; cbn [app] in *.
  (* [comment removed for export] *)
  Ltac openc C := destruct C as (FRB & FF248 & GOT & SHB & STG & MU & WM & MI); unfold W5 in MU.
  Ltac closec := unfold core, W5; repeat match goal with |- _ /\ _ => split end; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast.
  Ltac after_apply := try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try closec; try reflexivity; try (unfold FSH3, FSH1, FSHZ; cbn [app]; assumption).
  (* [comment removed for export] *)
  Tactic Notation "zfin" ne_hyp_list(hs) :=
    change 18446744073709551615 with (2^64 - 1); rewrite ?zb_land_mask by lia; rewrite ?Z.mod_small by (clear - hs; lia); clear - hs; lia.

  (* [comment removed for export] *)
  #[using="rc SP16 LOS LOC RSTK S D RLO FH RF RSF GH GF PL0"] Lemma ffsi_scope : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 y19 y20 y21 y22 y23 y24 x28 x29 x30 x31 : word) mx
      (cl : list cell) (nb : list byte) (cs db : word),
    core mx -> stk asegs mx lo SPAz -> rw_cells asegs mx SPAz cl -> cells_size cl = 56%nat ->
    rw_cells asegs mx (Z.shiftr FF 3 + 2147450880) ([f1c; f1c; f1c; f1c; z1c; z1c; z1c; z1c; z1c; z1c; f2c; f2c; f2c; f2c; f8c; f8c; f3c; f3c; f3c; f3c] ++ FSHZ) ->
    rw_cells asegs mx FF FFHDR ->
    rw_cells asegs mx R [CB 8 nb; C8 cs; C8 db] -> (bv_unsigned cs < 2^64 - 119 -> 1 <= bv_unsigned cs <= zlen bl) ->
    evtF asegs RNG POST_J
      (MS (mkR x1 (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) y19 y20 y21 y22 y23 y24 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) (Z_to_bv 64 2147450880) x28 x29 x30 x31)
            FR (Z_to_bv 64 0x81800) fc None mx (seg_rom asegs)).
  Proof.
    intros until db. intros C STL FRA CL SHF FF0 RR CS. openc C. Local Ltac2 Set LiaHints.tbl := fun () => "01J0?12066655206.12612342077012.12612911143428.12612984826510.12613067081226.12615010729543.12515160347210.12615497861449.12615719060185.12616036404119.12516279979987.12216753464773.12216867429482.12617941155254.12218909631322.12619039061412.12219272833703.12519970786093.11320139715884.1262027029998.126 21470349994.12623584418860.12623687287154.12623823397578.12624521592556.12624686014778.126256274160.122  2673550442.126 26774769626.12627320971313.1212818573085.122 28322672359.12528516984212.12628897571974.12628987856538.12630734467726.12631439680862.12631693696482.12631930091218.12632365281766.12632377744366.12634098841190.126341926775.125  353645442.126  36685953222.12637242358366.12637349358057.12637545354041.12638389508810.12638709023052.12638889460260.12639340006770.12240324494905.12641156628862.12642452747910.12642583353243.12242643832943.12243349595838.126449256530.116  45221239098.12645342999668.12645740938393.12645958212890.1264605189994.126 46553288074.12646901542423.12247747998098.1264861306889.126 52567164907.12252567164907.12653638430191.11254769888194.12656017336446.1265634116633.126 56830590924.12657533215052.12659308628179.11661315274736.12263392461657.12663653409214.12664026414714.12664696793412.12665299792814.12666948228265.12667114676681.12668066155898.1266924395529.126 7303350522.126 8929938862.126 9417716919.125 00000800Y01:01F01R01Z01f02B02^02f02n03U03a03m04I04i05105R05Z05f06206:06a07=07E07Q07]07i08508=08E08M08n09609B09N09Z0:A0:h0;00;<0;D0;L0<30<;0<G0<n0=J0=V0=^0>?0>d0?K0?W0?_0@?0@K0@W0@g0A30AT0B00BL0Bh0CD0CL0D30DO0DW0D_0Dg0EN0EZ0FA0FI0FQ0F`0Fl0GS0G_0Gk0HL0HX0I40I[0Ig0JN0Jj0K60K>S2CL3FHbS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHb3BSFS2CL3FHb3BSFS2CL3FHbS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS2CL3FHbS3LOS3LOC3RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS2CL3FHb3FHdS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3FHc3GHcS2CL3FHbS3LOS3LOC3RLO2CL3ATR4SPAB3FHa3FHbS2CL3FHbS2CL3FHb3BSFS2CL3FHb3BSFS2CL3FHbS3LOS3LOC3RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS2CL3FHb3BSFS2CL3FHa3FHbS2CL3FHb3BSFS2CL3FHb3BSFS2CL3FHbS2CL3FHbS2CL3FHbS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHbS2CL3FHb3BSFS2CL3FHb3BSFS2CL3FHb3BSFS3LOS3LOC3RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS2CL3FHb3BSFS2CL3FHbS2CL3FHbS3LOS3LOC3RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS2CL3FHb3BSFS3LOS3LOC3RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHb3BSFS2CL3FHbS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3FHc3GHcS3LOS3LOC3RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS2CL3FHbS3LOS3LOC3RLO2CL3ATR3FHb3FHc3GHcS2CL3FHa3FHbS2CL3FHb3BSFS2CL3FHa3FHb3FHdS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS3LOS3LOC3RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS2CL3FHbS2CL3FHbS3LOS3LOC3RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS3LOS3LOC3RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS2CL3FHbS2CL3FHa3FHb2K0S2CL3FHa3FHbS3LOS3LOC3RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC3RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS3LOS3LOC3RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHb3BSFS2CL3FHb".
prep2. unfold FSHZ in SHF. cbn [app] in SHF. unfold FFHDR in FF0.
    zstep. neglit (-8).                           (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.     (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].   (* [comment removed for export] *)
    apply evtF_done. unfold POST_J. do 22 eexists. exists cl, nb, cs, db. eexists.
    split; [reflexivity|]. split; [closec|]. unfold FSH1, FSHZ. cbn [app].
    repeat match goal with |- _ /\ _ => split end; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; exact CS.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="rc SP16 LOS LOC RSTK S D RLO RHI RGR FH RF RSF GH GF PL0"] Lemma ffsi_db : forall (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 y19 y20 y21 y22 y23 y24 x28 x29 x30 x31 : word) mx
      (cl : list cell) (nb r2 : list byte) (cs db : word),
    core mx -> stk asegs mx lo SPAz -> rw_cells asegs mx SPAz cl -> cells_size cl = 56%nat ->
    rw_cells asegs mx (Z.shiftr FF 3 + 2147450880) ([f1c; f1c; f1c; f1c; z1c; z1c; z1c; z1c; z1c; z1c; f2c; f2c; f2c; f2c; f8c; f8c; f3c; f3c; f3c; f3c] ++ FSHZ) ->
    rw_cells asegs mx FF FFHDR ->
    rw_cells asegs mx R [CB 8 nb; C8 cs; CB 8 r2] -> (bv_unsigned cs < 2^64 - 119 -> 1 <= bv_unsigned cs <= zlen bl) ->
    evtF asegs RNG POST_J
      (MS (mkR x1 (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) (Z_to_bv 64 (R + 16)) db x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) y19 y20 y21 y22 y23 y24 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) (Z_to_bv 64 2147450880) x28 x29 x30 x31)
            FR (Z_to_bv 64 0x817fc) fc None mx (seg_rom asegs)).
  Proof.
    intros until db. intros C STL FRA CL SHF FF0 RR CS. pose proof C as C'. openc C. Local Ltac2 Set LiaHints.tbl := fun () => "00=0?13001224923.12314294568344.12316439798173.12319970786093.11324004349677.12237038741246.12337371137959.12344793722668.12352567164907.12353638430191.11260952295576.12363216898067.1237505495178.123 00000S00k01J01k02302?02J02m03503=03U03a04ES3LOS3LOC3RLO2CL3ATR3FHb3FHc3GHc2HBS3LOS3LOC3RLO2CL3ATR3FHbS3LOS3LOC3RLO2CL3ATR3FHb3BSF2HBS3LOS3LOC3RLO2CL3ATR4SPAB3FHa3FHbS2CL3FHbS3RHI2CL3FHbS2CL3FHb2HBS3LOS3LOC3RLO2CL3ATR3FHb3FHc3GHc2HBS2CL3FHbS2CL3FHbS3LOS3LOC3RLO2CL3ATR3FHbS3RLO2CL3FHbS3LOS3LOC3RLO2CL3ATR4SPAB3FHa3FHb2HB".
prep2.
    zstep.                                        (* [comment removed for export] *)
    eapply ffsi_scope. all: after_apply.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
  (* [comment removed for export] *)
  #[using="rc SP16 LOS LOC RSTK S D RLO RHI RGR FH RF RSF GH GF PL0"] Lemma ffsi_dbe : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 y19 y20 y21 y22 y23 y24 x28 x29 x30 x31 : word) mx
      (cl : list cell) (nb r2 : list byte) (cs : word),
    core mx -> stk asegs mx lo SPAz -> rw_cells asegs mx SPAz cl -> cells_size cl = 56%nat ->
    rw_cells asegs mx (Z.shiftr FF 3 + 2147450880) ([f1c; f1c; f1c; f1c; z1c; z1c; z1c; z1c; z1c; z1c; f2c; f2c; f2c; f2c; f8c; f8c; f3c; f3c; f3c; f3c] ++ FSHZ) ->
    rw_cells asegs mx FF FFHDR ->
    rw_cells asegs mx R [CB 8 nb; C8 cs; CB 8 r2] -> (bv_unsigned cs < 2^64 - 119 -> 1 <= bv_unsigned cs <= zlen bl) ->
    evtF asegs RNG POST_J
      (MS (mkR x1 (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) (Z_to_bv 64 (R + 16)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) y19 y20 y21 y22 y23 y24 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) (Z_to_bv 64 2147450880) x28 x29 x30 x31)
            FR (Z_to_bv 64 0x817f8) fc None mx (seg_rom asegs)).
  Proof.
    intros until cs. intros C STL FRA CL SHF FF0 RR CS. pose proof C as C'. openc C. Local Ltac2 Set LiaHints.tbl := fun () => "0020?19970786093.11353638430191.11200000Q00YS3LOS3LOC3RLO2CL3ATR4SPAB3FHa3FHbS2CL3FHb".
prep2.
    zstep.                                        (* [comment removed for export] *)
    eapply ffsi_db. all: after_apply.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="rc SP16 LOS LOC RSTK D R8 RLO RHI RGR RGRS FH RF RSF GH GF PL0 RU0"] Lemma ffsi_exitE : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 y18 y19 y21 y23 x28 x29 x30 x31 : word) mx
      (ja jb r0 r1 r2 : list byte) (cs : word),
    core mx -> stk asegs mx lo SPAz -> rw_cells asegs mx SPAz [CB 16 ja; C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 R); CB 16 jb; C8 (Z_to_bv 64 FF)] ->
    rw_cells asegs mx (Z.shiftr FF 3 + 2147450880) FSH3 -> rw_cells asegs mx FF FFHDR ->
    rw_cells asegs mx R [CB 8 r0; CB 8 r1; CB 8 r2] -> 2^64 - 119 <= bv_unsigned cs ->
    evtF asegs RNG POST_J
      (MS (mkR x1 (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) cs x11 x12 x13 x14 x15 x16 x17 y18 y19 (Z_to_bv 64 S) y21 (Z_to_bv 64 (FF + 32)) y23 (Z_to_bv 64 (FF + 112)) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) (Z_to_bv 64 2147450880) x28 x29 x30 x31)
            FR (Z_to_bv 64 0x819bc) fc None mx (seg_rom asegs)).
  Proof.
    intros until cs. intros C STL FRA SHF FF0 RR CSE. openc C. Local Ltac2 Set LiaHints.tbl := fun () => "0180?10841825258.13410990985245.12711383349470.13413001224923.13114294568344.13114453460750.1341532592226.126 15334474334.12716439798173.13117315598367.13318091811352.12718437397164.12719302942247.12719970786093.11120749162842.13421426538131.1272179254107.127 22200344330.12722718764814.13424004349666.1302601737496.127 27736797930.13429018245758.1273188101182.119 3188101183.115 33897463481.13435670257402.11436742878330.13437038741246.13137371137959.13138450959742.11839178121190.13442782745529.13442968992041.13443754901852.11544793722668.13145982589382.13447085352612.13447946365538.13448688364751.13349943447116.1345089449082.118 52567164907.12752567164907.13152567164907.13453557778676.13453638430191.11054302169230.2  56500923902.11456644364524.13457018326411.11957020423608.11559308628304.1  59308628433.1  59308768411.3  598848478.134  59991009118.12360952295576.1316192067805.119 61934652264.12162098338330.13463216898067.13163370524077.1156386823154.134 65071494699.12065073591832.11665499904044.11968516218382.2  6900360422.129 7139856330.134 7505495178.131 8374517865.134 00000900U00^01>01S01\01a02:02V02[03003P03X04:04C04L04l05Q05Z05_06406M06V06k07@07d07i08B08K08S08X08]09609O09T0:40:90:W0;;0;@0;E0;J0;O0;T0;Y0<70<<0<@0<E0<J0<O0<T0<X0<\0<d0<m0=F0=[0=`0=e0=n0>70><0>`0>e0>j0>o0?30?80?A0?f0@JS3FHb3BSFS3LOS3LOC3RLO3ATR3FHb3BSF2HBS3FHb3BSFS3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3LOS3LOC3RLO3ATR3FHbS3FHb3BSFS3FHbS3LOS3LOC3RLO3RHI3ATR3FHbS3LOS3LOC3RLO3ATR3FHb3BSF2HBS3FHbS3LOS3LOC3RLO3ATR3FHbS3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3FHb2HBS3LOS3LOC3RLO3ATR4SPAB3FHa3FHb3GHaS3FHb3BSFS3RLO3FHbS3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3LOS3LOC3RLO3ATR4SPAB3FHa3FHb3GHa2HBS3FHb3BSFS3FHbS3LOS3LOC3RLO3ATR3FHbS3LOS3LOC3RLO3ATR3FHb3BSFS3RHI3FHbS3LOS3LOC3RLO3ATR3FHbS3LOS3LOC3RLO3ATR3FHbS3LOS3LOC3RLO2GF3ATR3FHb3FHu3GHu3BSFS3FHbS3LOS3LOC3RLO3ATR3FHb3BSFS3RHI3FHbS3FHb2HBS3FHbS3FHbS3LOS3LOC3RLO3ATR3FHb3BSFS3LOS3LOC3RLO3ATR3FHb3BSFS3FHbS3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3FHbS3LOS3LOC3RLO3ATR4SPAB3FHb3BSFS3LOS3LOC3RLO2GF3ATR3FHb3FHu3GHu3BSFS3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS3LOS3LOC3RLO3ATR4SPAB3FHb3BSFS3FHbS2R8S3FHbS3FHbS3FHbS3FHbS2K1S2K2S3CSE2CxS3FHb3BSFS3LOS3LOC3RLO3RHI3ATR3FHbS3LOS3LOC3RLO3ATR3FHbS3FHbS3FHbS3FHb3BSFS3RLO3FHbS3FHbS3LOS3LOC3RLO2GF3ATR3FHb3FHu3GHu3BSFS3FHbS3FHbS3FHbS2R8S3FHbS3FHb3BSFS3LOS3LOC3RLO3ATR4SPAB3FHa3FHb3GHa2HBS3LOS3LOC3RLO2GF3ATR3FHb3FHu3GHu3BSF".
prep2. unfold FSH3, FSHZ in SHF. cbn [app] in SHF.
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    rsh8 8 RS1.
    zstep. cbv beta. rewrite (byte_litA 0) by lia. (* [comment removed for export] *)
    zstep. bcase K1; [exfalso; clear - K1; lia|]. (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    rsh8 16 RS2.
    zstep. cbv beta. rewrite (byte_litA 0) by lia. (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. bcase K2; [exfalso; clear - K2; lia|]. (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. neglit (-8).                           (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    eapply ffsi_scope. all: after_apply.
    all: intros Cx; exfalso; clear - Cx CSE; lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  Section Frame.
    Variables (j1 j2 : list byte) (h : Z) (r0 r1 r2 : list byte).
    Hypotheses (H6 : 6 <= h <= zlen bl) (H18 : h <= 18).
    Notation ZFHC := ([CB 24 j1; C4 (Z_to_bv 64 h); CB 20 j2]).

    (* [comment removed for export] *)
    #[using="SP R PAY h H6"] Lemma fr_pay : D <= S /\ S + zlen bl <= D + N /\ N <= 2^40 /\ ablk D (D + N) /\ D mod 16 = 0 /\ rng RNG D N /\ rng RNG (shad D) (shlen (N + 7))
                   /\ (D + N <= FF \/ FF + 256 <= D).
    Proof. apply PAY. Local Ltac2 Set LiaHints.tbl := fun () => "0010>32241140627.66000004S2H6".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
    #[using="rc lo SP16 LOS LOC RNG D N PAY RLO FH h H6"] Lemma f2_djp : disjoint_from W5 (shad S) (shad (S + zlen bl - 1) + 1 - shad S).
    Proof.
      pose proof atop_range as ATR. pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
      destruct fr_pay as (DS & SN & NN & DH & D16 & RGA & RGS & SEPF).
      pose proof (ablk_lin _ _ DH) as (DHa & DHb & DHc & DHd). pose proof DH as DHu. unfold ablk, AIMG_HI, KLS in DHu.
      pose proof f2_bsf as BSF. pose proof (proj1 (spa160_propsA SP SP16)) as SPAB. unfold AFI_STACK in LOS. unfold KEND in RHI.
      unfold W5. clear - ATR FHb FHc FHu DHb DHc DHu DS SN SEPF BSF LOC LOS RLO RHI SPAB H6.
      Local Ltac2 Set LiaHints.tbl := fun () => "0080>17792358713.2719287691209.2728062205174.2729788740460.2742847215913.275017153385.27 57359381492.2765933537932.2700000H00e01B01C01W01k02C02_S3ATR3FHu2DS2SN4SEPF3DHuS3LOS3LOC3ATR3FHu2SN3DHu4SPABS3LOS3LOC3ATR3FHu2SN3DHu4SPABSS3FHu2DS2SN4SEPF3DHuS3FHu2DS2SN4SEPF3DHuS3ATR3FHu2DS2SN4SEPF3DHuS3LOS3LOC3RLO3ATR3FHu2SN3DHu".
rewrite !shad_div, ?Z.shiftr_div_pow2 by lia. unfold ASHOFF. change (2^3) with 8. cbn [disjoint_from].
      repeat split; try exact I; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
    #[using="rc lo SP16 LOS LOC RNG D N PAY RLO FH h H6"] Lemma f2_djpl : disjoint_from W5 S (Z.of_nat (length (map (Z_to_bv 8) bl))).
    Proof.
      rewrite length_map.
      pose proof atop_range as ATR. pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
      destruct fr_pay as (DS & SN & NN & DH & D16 & RGA & RGS & SEPF).
      pose proof (ablk_lin _ _ DH) as (DHa & DHb & DHc & DHd). pose proof DH as DHu. unfold ablk, AIMG_HI, KLS in DHu.
      pose proof f2_bsf as BSF. pose proof (proj1 (spa160_propsA SP SP16)) as SPAB. unfold AFI_STACK in LOS. unfold KEND in RHI.
      unfold W5. clear - ATR FHb FHc FHu DHb DHc DHu DS SN SEPF BSF LOC LOS RLO RHI SPAB H6.
      Local Ltac2 Set LiaHints.tbl := fun () => "0080>16782228291.2721168659884.2724512028099.2729788740460.272980491436.27 40203774988.2740364307376.2750629948473.2700000D00_01601701R01g02>02SS3LOS3LOC3RLO2SN3DHcS2H63ATR3FHu2DS2SN4SEPF3DHuS2H63FHu2DS2SN4SEPF3DHuSS2H63ATR3FHu2DS2SN4SEPF3DHuS3LOS3LOC2SN3DHc4SPABS2H63FHu2DS2SN4SEPF3DHuS3LOS3LOC2SN3DHc4SPAB".
rewrite ?Z.shiftr_div_pow2 by lia. change (2^3) with 8. cbn [disjoint_from].
      repeat split; try exact I; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
    Ltac prepF :=
      prep2;
      destruct fr_pay as (DS & SN & NN & DH & D16 & RGA & RGS & SEPF);
      pose proof (ablk_lin _ _ DH) as (DHa & DHb & DHc & DHd); unfold AIMG_HI in DHa; pose proof DH as DHu; unfold ablk, AIMG_HI, KLS in DHu;
      boxH D16.

    (* [comment removed for export] *)
    #[using="rc SP16 LOS LOC RSTK D N NB PAY R8 RLO RHI RGR RGRS FH RF RSF GH GF PL0 RU0 H6"] Lemma ffsi_fin2 : forall (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 y23 x28 x29 x30 x31 : word) mx
        (ja jb : list byte) (db : word) (k nb ipz : Z),
      core mx -> stk asegs mx lo SPAz -> rw_cells asegs mx SPAz [CB 16 ja; C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 R); CB 16 jb; C8 (Z_to_bv 64 FF)] ->
      rw_cells asegs mx (Z.shiftr FF 3 + 2147450880) ([f1c; f1c; f1c; f1c; z1c; z1c; z1c; z1c; z1c; z1c; f2c; f2c; f2c; f2c; f8c; f8c; f3c; f3c; f3c; f3c] ++ FSHZ) -> rw_cells asegs mx FF FFHDR ->
      rw_cells asegs mx R [CB 8 r0; CB 8 r1; CB 8 r2] -> h <= k <= zlen bl -> 0 <= nb <= k -> ipz = S + k ->
      evtF asegs RNG POST_J
        (MS (mkR x1 (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) x10 db x12 (Z_to_bv 64 R) x14 x15 x16 x17 (Z_to_bv 64 nb) (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 S) (Z_to_bv 64 ipz) (Z_to_bv 64 (FF + 32)) y23 (Z_to_bv 64 (FF + 112)) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) (Z_to_bv 64 2147450880) x28 x29 x30 x31)
            FR (Z_to_bv 64 0x81a74) fc None mx (seg_rom asegs)).
    Proof.
      intros until ipz. intros C STL FRA SHF FF0 RR HK HNB ->. openc C. Local Ltac2 Set LiaHints.tbl := fun () => "00m0?10990985245.13615047390338.1201532592226.135 15334474333.13718091811352.13618437397164.13619302942247.13619970786093.11621426538131.1362179254107.136 22200344330.13622527583800.13222954551237.1322601737496.136 2603756902.132 26182954604.13226631416763.8  26824457171.13429018245758.13629791052619.1323188101180.120 3188101182.128 3188101183.124 33503717167.13235497761944.13035670257402.12335892103014.11935970547509.13137254250633.13238450959742.12743754901852.12445049100339.12046134221986.2  5089449082.127 51621919586.11952567164907.13252567164907.13653638430191.11554302169230.2  55318772066.13056500923902.12357018326408.12857018326411.12457020423608.12059245416335.13259308628179.1  59308628304.1  59308628433.1  59991009117.1336192067805.128 63318740076.13263370524077.12464295209551.13464373332722.13265071494696.12965071494699.12565073591832.12165093347183.13265499904044.12868516218382.2  6900360422.138 00000L00Q00V00o01D01d01l02J02S03303T04404904N04o05D05Q05R05[05c06806M06b06k07307807=07B07^07c07h07m08108608;08@08E08J08N08g08l09109609;09[09_09c09g0:@0:E0:Z0:_0;I0;R0;W0;\0;a0;f0;k0;o0<4S3LOS3LOC3RLO3ATR3FHb3BSF2HBS3FHbS3FHbS3LOS3LOC3RLO3RHI3ATR3FHbS3LOS3LOC3RLO3ATR3FHbS3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3FHb2HBS3LOS3LOC3RLO3ATR4SPAB3FHa3FHbS3RLO3FHbS3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3LOS3LOC3RLO3ATR4SPAB3FHa3FHb2HBS3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3FHbS3LOS3LOC3RLO3ATR3FHbS3LOS3LOC3RLO3ATR4SPAB3FHa3FHb2HBS3LOS3LOC3RLO3ATR3FHbS2NB2H62HK2BBFS3RHI3FHbS3FHb2HBS3LOS3LOC3RLO3ATR3FHbS3LOS3LOC3RLO3ATR3FHbS3LOS3LOC3RLO3ATR3FHbS3RLO3FHbS3FHb2WFS3FHbS3FHbS3FHbS3LOS3LOC3RLO3ATR3FHb3BSF2HBS3FHbS3FHbS3FHbS2R8S3FHbS3FHbS3FHbS3FHbS3FHbS2R8S3LOS3LOC3RLO3RHI3ATR3FHbS3FHbS3FHbS3FHbS3FHbS3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS2K0S2K1S2K2S3LOS3LOC3RLO3RHI3ATR3FHbS3FHbS3LOS3LOC3RLO3ATR3FHbS3FHbS3LOS3LOC3PAY3RLO2H62HK3ATR3FHb3FHc3GHc2BBS3RHI3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS2R8S3FHb".
prep2. unfold FSHZ in SHF. cbn [app] in SHF.
      zstep. zstep.                               (* [comment removed for export] *)
      rsh8 0 RS0.
      zstep. cbv beta. rewrite (byte_litA 0) by lia. (* [comment removed for export] *)
      zstep. bcase K0; [exfalso; clear - K0; lia|]. (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      zstep. zstep. zstep.                        (* [comment removed for export] *)
      rsh8 8 RS1.
      zstep. cbv beta. rewrite (byte_litA 0) by lia.
      zstep. bcase K1; [exfalso; clear - K1; lia|].
      zstep.                                      (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      zstep. zstep.                               (* [comment removed for export] *)
      rsh8 16 RS2.
      zstep. cbv beta. rewrite (byte_litA 0) by lia.
      zstep.                                      (* [comment removed for export] *)
      zstep. bcase K2; [| exfalso; clear - K2; lia]. (* [comment removed for export] *)
      (* [comment removed for export] *)
      lazymatch goal with H : rw_cells _ ?m1 R [C8 ?a; C8 ?b; CB 8 r2] |- _ =>
        pose proof (proj1 (proj1 H)) as WF; cbn [cells_wf cell_wf] in WF;
        apply (rw_cells_recast asegs m1 R _ [CB 8 (le8 a); C8 b; CB 8 r2]) in H;
          [| cbn [cells_wf cell_wf]; rewrite ?length_le8; tauto | reflexivity | reflexivity] end.
      eapply ffsi_db. all: after_apply.
      all: intros _; rewrite unsigned_lit_wrap; change 18446744073709551615 with (2^64 - 1); rewrite ?zb_land_mask by lia;
           clear - HK H6 NB BB; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

    (* [comment removed for export] *)
    #[using="rc SP16 LOS LOC RSTK D N NB PAY R8 RLO RHI RGR RGRS FH RF RSF GH GF PL0 RU0 H6"] Lemma ffsi_fin1 : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 y23 x28 x29 x30 x31 : word) mx
        (ja jb : list byte) (k nb ipz : Z),
      core mx -> stk asegs mx lo SPAz -> rw_cells asegs mx SPAz [CB 16 ja; C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 R); CB 16 jb; C8 (Z_to_bv 64 FF)] ->
      rw_cells asegs mx (Z.shiftr FF 3 + 2147450880) ([f1c; f1c; f1c; f1c; z1c; z1c; z1c; z1c; z1c; z1c; f2c; f2c; f2c; f2c; f8c; f8c; f3c; f3c; f3c; f3c] ++ FSHZ) -> rw_cells asegs mx FF FFHDR ->
      rw_cells asegs mx (FF + 32) ZFHC ->
      rw_cells asegs mx R [CB 8 r0; CB 8 r1; CB 8 r2] -> h <= k <= zlen bl -> 0 <= nb <= k -> ipz = S + k ->
      evtF asegs RNG POST_J
        (MS (mkR x1 (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) x10 x11 x12 (Z_to_bv 64 R) x14 x15 x16 x17 (Z_to_bv 64 nb) (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 S) (Z_to_bv 64 ipz) (Z_to_bv 64 (FF + 32)) y23 (Z_to_bv 64 (FF + 112)) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) (Z_to_bv 64 2147450880) x28 x29 x30 x31)
            FR (Z_to_bv 64 0x81a60) fc None mx (seg_rom asegs)).
    Proof.
      intros until ipz. intros C STL FRA SHF FF0 ZFH RR HK HNB HIP. pose proof C as C'. openc C. Local Ltac2 Set LiaHints.tbl := fun () => "0070?15574696078.13419970786093.12038883115334.13243203500333.13353638430191.11958812639243.13167190198865.13500000500S00X00]00b01I01NS3FHbS3LOS3LOC3RLO3ATR4SPAB3FHa3FHbS3FHbS3FHbS3FHbS3LOS3LOC3PAY3RLO2HK3HNB3FHb3FHc3GHc2BBS3FHb".
prep2.
      zstep.                                      (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      zstep. if_cases KF; clear KF.               (* [comment removed for export] *)
      - eapply ffsi_fin2. all: after_apply.
      - zstep. zstep.                             (* [comment removed for export] *)
        eapply ffsi_fin2. all: after_apply.
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

    (* [comment removed for export] *)
    #[using="rc SP16 LOS LOC RSTK D N NB PAY R8 RLO RHI RGR RGRS FH RF RSF GH GF PL0 RU0 H6"] Lemma ffsi_finish : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) mx
        (ja jb : list byte) (k nb ipz rmz : Z),
      core mx -> stk asegs mx lo SPAz -> rw_cells asegs mx SPAz [CB 16 ja; C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 R); CB 16 jb; C8 (Z_to_bv 64 FF)] ->
      rw_cells asegs mx (Z.shiftr FF 3 + 2147450880) ([f1c; f1c; f1c; f1c; z1c; z1c; z1c; z1c; z1c; z1c; f2c; f2c; f2c; f2c; f8c; f8c; f3c; f3c; f3c; f3c] ++ FSHZ) -> rw_cells asegs mx FF FFHDR ->
      rw_cells asegs mx (FF + 32) ZFHC ->
      rw_cells asegs mx R [CB 8 r0; CB 8 r1; CB 8 r2] -> h <= k <= zlen bl -> 0 <= nb <= k -> ipz = S + k -> rmz = zlen bl - k ->
      evtF asegs RNG POST_J
        (MS (mkR x1 (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 nb) (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 S) (Z_to_bv 64 ipz) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 rmz) (Z_to_bv 64 (FF + 112)) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) (Z_to_bv 64 2147450880) x28 x29 x30 x31)
            FR (Z_to_bv 64 0x81a08) fc None mx (seg_rom asegs)).
    Proof.
      intros until rmz. intros C STL FRA SHF FF0 ZFH RR HK HNB -> ->. pose proof C as C'. openc C. Local Ltac2 Set LiaHints.tbl := fun () => "00]0?10990985245.1341532592226.133 15334474334.13418091811352.13418437397164.13419302942247.13419970786093.11721426538131.1342179254107.134 22200344330.1342601737496.134 29018245758.1343188101182.126 3188101183.122 3479438036.120 35670257402.12136350570402.7  38450959742.12543754901852.1225089449082.125 52567164907.13453031384365.13253638430191.11654302169230.2  5537889499.134 56500923902.12156683856941.7  57018326411.12657020423608.12257571462470.8  59308628304.1  59308628433.1  59991009118.1306192067805.126 61934652261.13061934652265.12662843472462.13163370524077.1226386879048.7   65071494699.12765073591832.12365499904044.12668516218382.2  6900360422.136 9186259352.7   00000L00Q00j01?01_01g02E02N02n03O03d03m04B04W05A05F05K05P05U05Z05_05d05i05m06M06R06V06[06`06a06e06i07B07G07L07Q07V07[07`07e07j07o08308808<S3LOS3LOC3RLO3ATR3FHb3BSF2HBS3FHbS3LOS3LOC3RLO3RHI3ATR3FHbS3LOS3LOC3RLO3ATR3FHbS3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3FHb2HBS3LOS3LOC3RLO3ATR4SPAB3FHa3FHbS3RLO3FHbS3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3LOS3LOC3RLO3ATR4SPAB3FHa3FHb2HBS3LOS3LOC3RLO3ATR3FHbS3RHI3FHbS3LOS3LOC3RLO3ATR3FHbS3LOS3LOC3RLO3ATR3FHbS3LOS3LOC3PAY3RLO2H62HK3HNB3FHb3FHc3GHc2BBS3FHbS3HNBS3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS2R8S3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3FHbS2K4S3FHbS3FHbSS2K1S2K2S3LOS3LOC3RLO3RHI3ATR3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS3HNBS3FHbS3FHbS3FHbS2R8S3FHbS2HK".
prep2.
      zstep.                                      (* [comment removed for export] *)
      zstep. if_cases KC; clear KC.               (* [comment removed for export] *)
      - zstep. zstep.                             (* [comment removed for export] *)
        eapply ffsi_fin1. all: after_apply.
      - zstep. zstep.                             (* [comment removed for export] *)
        zstep. bcase K4.                          (* [comment removed for export] *)
        + zstep.                                  (* [comment removed for export] *)
          eapply ffsi_fin1 with (k := k + 4). all: after_apply. all: clear - HK K4 HNB; lia.
        + (* [comment removed for export] *)
          unfold FSHZ in SHF. cbn [app] in SHF.
          zstep. zstep. zstep.                    (* [comment removed for export] *)
          rsh8 8 RS1.
          zstep. cbv beta. rewrite (byte_litA 0) by lia.
          zstep. bcase K1; [exfalso; clear - K1; lia|].
          zstep. zstep.                           (* [comment removed for export] *)
          zstep. zstep. zstep.                    (* [comment removed for export] *)
          rsh8 16 RS2.
          zstep. cbv beta. rewrite (byte_litA 0) by lia.
          zstep.                                  (* [comment removed for export] *)
          zstep. bcase K2; [| exfalso; clear - K2; lia]. (* [comment removed for export] *)
          eapply ffsi_dbe. all: after_apply.
          all: intros C; exfalso; rewrite unsigned_lit_wrap in C; revert C; vm_compute; discriminate.
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

    (* [comment removed for export] *)
    Definition hinv (mx : amem) (k : Z) (rw : word) (nb ipz rmz : Z) (ja jb w0 w1 w2 : list byte) : Prop :=
      core mx /\ stk asegs mx lo SPAz /\ rw_cells asegs mx SPAz [CB 16 ja; C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 R); CB 16 jb; C8 (Z_to_bv 64 FF)] /\
      rw_cells asegs mx (Z.shiftr FF 3 + 2147450880) FSH3 /\ rw_cells asegs mx FF FFHDR /\
      rw_cells asegs mx (FF + 32) ZFHC /\ rw_cells asegs mx (FF + 112) [CB 4 w0; CB 4 w1; CB 4 w2] /\
      rw_cells asegs mx R [CB 8 r0; CB 8 r1; CB 8 r2] /\
      h <= k <= zlen bl /\ 0 <= nb <= k /\ bv_unsigned rw <= 2^64 - 120 /\ ipz = S + k /\ rmz = zlen bl - k.
    Definition head_st (mx : amem) (k : Z) (rw : word) (nb ipz rmz : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) : machine_state :=
      (MS (mkR x1 (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) rw x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 nb) (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 S) (Z_to_bv 64 ipz) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 rmz) (Z_to_bv 64 (FF + 112)) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) (Z_to_bv 64 2147450880) x28 x29 x30 x31)
            FR (Z_to_bv 64 0x8193c) fc None mx (seg_rom asegs)).

    (* [comment removed for export] *)
    #[using="rc SP16 LOS LOC RSTK RI D N PLR NB PAY R8 RLO RHI RGR RGRS FH F256 RF RSF GH GF PL0 UNP0 RU0 H6"] Lemma ffsi_step : forall mx k rw nb ipz rmz ja jb w0 w1 w2 (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      hinv mx k rw nb ipz rmz ja jb w0 w1 w2 ->
      (forall mx2 k2 rw2 nb2 ipz2 rmz2 jb2 v0 v1 v2 (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
         hinv mx2 k2 rw2 nb2 ipz2 rmz2 ja jb2 v0 v1 v2 -> k + 3 <= k2 ->
         evtF asegs RNG POST_J
           (MS (mkR (Z_to_bv 64 0x81978) (Z_to_bv 64 SPAz) gp tp y5 y6 y7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) rw2 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 nb2) (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 S) (Z_to_bv 64 ipz2) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 rmz2) (Z_to_bv 64 (FF + 112)) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) (Z_to_bv 64 2147450880) y28 y29 y30 y31)
            FR (Z_to_bv 64 0x8193c) fc None mx2 (seg_rom asegs))) ->
      evtF asegs RNG POST_J (head_st mx k rw nb ipz rmz x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
    Proof.
      intros until x31. intros HI CONT. unfold head_st.
      destruct HI as (C & STL & FRA & SHF & FF0 & ZFH & BP & RR & HK & HNB & RWB & -> & ->). pose proof C as C'. openc C. Local Ltac2 Set LiaHints.tbl := fun () => "01a0?10841825258.15010841825258.15211383349470.15011383349470.15211750063593.15011750063593.15212357356857.14812357356857.14912428150072.15713210268013.15814038803757.11 14038805170.13 14113831303.10 14453460750.14814453460750.14917317695511.15117317695513.14919970786093.12320133607273.2  20749162842.14820749162842.14922718764814.14822718764814.14925076071819.15625076071819.15725076071819.15825236826157.15125261068994.10 25261071709.12 27478534713.15727736797930.14827736797930.14928040491972.15929696349971.8  30665193763.15732716563636.17 33897463481.14833897463481.1493479450872.140 3488604889.149 35693770006.15336393902218.14036401657515.14936742878330.15036742878330.15237871915530.11 39178121190.14839178121190.14939819800638.14341805334855.15742086935187.11 42609501300.2  42782745529.15042782745529.15242968992041.14842968992041.1494466284721.143 45982589382.15045982589382.15246160081097.10 46160081097.11 46160084822.12 47085352612.15047085352612.15247436455302.15047946365538.15047946365538.15248690461897.14848690461899.14748947615290.12 49441733640.12 49943447116.15049943447116.15250629934895.15950802402711.14 51627303145.15051627303145.15252567164907.14852567164907.14952567164907.15052567164907.15253557778676.14853557778676.14953638430191.12254902296849.10 54902300302.12 56170384339.14356644364524.14856644364524.14957622410744.15858477402019.157598848478.150  598848478.152  61149760928.14362098338330.14862098338330.14962824932752.14363403938114.1586386823154.148 6386823154.149 6386891876.10  64180194694.14367334405174.13 67336552099.11 6801153045.143 7139856330.150 7139856330.152 8086067755.12  8374517865.150 8374517865.152 8803078713.148 8803078713.149 8984541093.2   00000A00R00c01402803<04@05D05E05o06406906B06S06d07107>07\07b08308D08U08f09P0::0;C0;P0;X0;`0<J0<k0=L0=M0=R0>80>N0?R0@V0AJ0B>0BK0B\0Bm0CN0Co0D40DA0DN0E00E10E?0EE0Ef0FG0Fh0GI0GV0Gc0H00H50H:0H?0He0IK0IX0J\0K`0Km0L:0L>0LG0LT0La0Lb0Lj0Mn0O20O?0OL0OY0Of0PL0Q20Q70Q?0QG0QY0Qf0R30RB0Rh0S90SJ0S[0Sl0T=0TW0UA0VE0WI0WR0W_0Wm0X80XE0XV0Xg0Y00Z40[80\<0]@0]AS3FHb3BSF3DHb3RW0S3FHb3BSF3DHb3RW0S3FHb3BSF3DHb3RW0S3FHb3BSF3DHb3RW0S3LOS3LOC3RLO2GF2H62HK3ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHu3RW02KXS3LOS3LOC3RLO2GF2H62HK3ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHu3RW02KXS3LOS3LOC3RLO2GF2H62HK3ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHu3RW02KXS3LOS3LOC3RLO2GF2H62HK3ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHu3RW02KXFS3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHb3RW0S3RW0S3RW0S3HNB3RW0S3FHb3BSF3DHb3RW0S3FHb3BSF3DHb3RW0S3FHb3DHb3RW0S3FHb3DHb3RW0S3LOS3LOC3RLO3ATR4SPAB3FHa3FHbS4F256S3FHb3BSF3DHb3RW0S3FHb3BSF3DHb3RW0S3FHb3BSF3DHb3RW0S3FHb3BSF3DHb3RW0S3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHb3RW0S3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHb3RW0S3LOS3LOC3RLO2GF2H62HK3ATR4SPAB3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHu3RW02KXS3FHb3DHb3RW0S3RW02KXS3RW02KXS3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHb3RW0S3LOS3LOC3RLO3ATR3FHb3BSF3DHb3RW0S3LOS3LOC3RLO3ATR3FHb3BSF3DHb3RW0FS3RW0S3LOS3LOC3RLO3ATR4SPAB3FHa3FHb3DHb3RW0S2H62HK2DS2SN4SEPF3RW0S3LOS3LOC3RLO2GF2H62HK3ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHu3RW02KXS3LOS3LOC3RLO2GF2H62HK3ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHu3RW02KXS3LOS3LOC3RLO2H62HK3HNB3FHb2DS2SN2NN3DHa3DHb3DHc3RW0S3LOS3LOC3RLO2H62HK3HNB3FHb2DS2SN2NN3DHa3DHb3DHc3RW0S3FHb3DHb3RW0S3RWB3FHb3DHb3RW0S3RWB3FHb3DHb3RW0S3LOS3LOC3RLO3ATR3FHb3BSF3DHb3RW0S3LOS3LOC3RLO3ATR3FHb3BSF3DHb3RW0S3RW0S3FHb3DHb3RW0S3FHb3DHb3RW0S3LOS3LOC3RLO3ATR4SPAB3FHb3DHb3RW0FS2H62HK3RW02KXS4F256S3LOS3LOC3RLO3ATR3FHb3BSF3DHb3RW0S3LOS3LOC3RLO3ATR3FHb3BSF3DHb3RW0S3LOS3LOC3RLO3ATR3FHb3BSF3DHb3RW0S3LOS3LOC3RLO3ATR3FHb3BSF3DHb3RW0S3FHb3DHb3RW0S3FHb3DHb3RW0S3FHb3DHb3RW0S3RW0S3RW0S3RW0S3LOS3LOC3RLO3ATR4SPAB3FHb3BSF3DHb3RW0S3LOS3LOC3RLO3ATR4SPAB3FHb3BSF3DHb3RW0S3FHb3DHb3RW0S3LOS3LOC3RLO2GF2H62HK3ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHu3RW02KXS3LOS3LOC3RLO2GF2H62HK3ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHu3RW02KXS3FHb3DHb3RW0S3FHb3DHb3RW0S2KES3HNB3RW0S3FHb3DHb3RW0S3FHb3DHb3RW0FS2SN3RW0S3LOS3LOC3RLO2GF2H62HK3ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHu3RW02KXS3LOS3LOC3RLO2GF2H62HK3ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHu3RW02KXS3FHb3DHb3RW0S3FHb3DHb3RW0S3FHb3DHb3RW0S3FHb3DHb3RW0S3LOS3LOC3RLO3ATR4SPAB3FHb3BSF3DHb3RW0S3LOS3LOC3RLO3ATR4SPAB3FHb3BSF3DHb3RW0S3FHbS2HK3RW0S2HK3RW0S4SPAB3FHb3DHb3RW0S3FHb3DHb3RW0S3FHb3DHb3RW0S3FHb3DHb3RW01HS3LOS3LOC3RLO3ATR4SPAB3FHa3FHb3DHb3RW0S3FHb3BSF3DHb3RW0S3FHb3BSF3DHb3RW0S3FHa3FHb3DHb3RW0S3FHb3BSF3DHb3RW0S3FHb3BSF3DHb3RW0S3RLO3RHI4SPAB3FHb3DHb3RW0S3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHb3RW0S3LOS3LOC3RLO2GF2H62HK3ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHu3RW02KXS3LOS3LOC3RLO2GF2H62HK3ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHu3RW02KXS3HNB3RW0S3FHb3DHb3RW0S2H62HK2DS3RW0S2H62HK3RW0S3FHb3DHb3RW0S3FHb3BSF3DHb3RW0S3FHb3BSF3DHb3RW0S3HNB3RW0S3LOS3LOC3RLO2GF2H62HK3ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHu3RW02KXS3LOS3LOC3RLO2GF2H62HK3ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHu3RW02KXS3LOS3LOC3RLO2GF2H62HK3ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHu3RW02KXS3LOS3LOC3RLO2GF2H62HK3ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHu3RW02KXS".
prepF.
      pose proof (bv_unsigned_in_range 64 rw) as RW0. unfold bv_modulus in RW0.
      unfold FSH3, FSHZ in SHF. cbn [app] in SHF.
      zstep.                                      (* [comment removed for export] *)
      zstep. bcase KX.                            (* [comment removed for export] *)
      { zstep.                                    (* [comment removed for export] *)
        eapply ffsi_exitE. all: after_apply.
        all: rewrite ?unsigned_lit_wrap; first [vm_compute; discriminate | clear - HK; lia]. }
      zstep.                                      (* [comment removed for export] *)
      zstep. zstep.                               (* [comment removed for export] *)
      zstep. zstep.                               (* [comment removed for export] *)
      zstep. if_cases KL; clear KL.               (* [comment removed for export] *)
      { eapply ffsi_finish with (k := k + (bv_unsigned rw + 3)). all: after_apply.
        all: zfin HK KX RWB HNB RW0. }
      zstep. zstep. zstep.                        (* [comment removed for export] *)
      zstep. zstep. zstep.                        (* [comment removed for export] *)
      (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      pose proof cbsA as CB. unfold cbsA_stmt in CB.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
        lazymatch goal with SHx : rw_cells asegs mc (Z.shiftr FF 3 + 2147450880) _, MUx : munch _ m mc, BPx : rw_cells asegs mc (FF + 112) _ |- _ =>
        pose proof (bytes_at_transport asegs _ m mc _ _ PL0 MUx f2_djpl) as PLx;
        eapply evtF_cut;
        [ eapply (CB RNG _ SPAz gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR fc mc (S + (k + (bv_unsigned rw + 3))) (skipn (Z.to_nat ((k + (bv_unsigned rw + 3)))) bl) D N (FF + 112) lo);
          [ apply (buf_atA_skipn mc S bl); [split; [exact PLx| exact PLR]| clear - HK KX RWB H6 RW0 BB; lia]
          | eapply unpoisoned_sub; [eapply unpoisoned_munch; [exact UNP0| exact MUx| exact f2_djp]| clear - HK KX RWB H6 RW0 BB; lia| rewrite zlen_skipnA by (clear - HK KX RWB H6 RW0 BB; lia); clear - HK KX RWB H6 RW0 BB; lia]
          | clear - HK KX RWB H6 RW0 BB DS; lia
          | rewrite zlen_skipnA by (clear - HK KX RWB H6 RW0 BB; lia); clear - SN HK KX RWB H6 RW0 BB; lia
          | exact NN | exact DH | exact D16 | exact RGA | exact RGS
          | exact BPx
          | clear - F256; unfold bx in F256; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia
          | eapply ablk_sub; [exact FH| lia| lia]
          | rewrite zlen_skipnA by (clear - HK KX RWB H6 RW0 BB; lia); clear - SEPF DS SN HK KX RWB H6 RW0 BB; lia
          | apply (fsh3_bp mc FF); [unfold FSH3, FSHZ; cbn [app]; exact SHx| clear - F256; unfold bx in F256; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia| lia]
          | eapply rng_sub'; [exact RF| lia]
          | eapply rng_sub'; [exact RSF|]; rewrite !shad_div; clear - FHb; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia
          | assumption | assumption
          | assumption | exact LOC | lia | unfold KEND; lia
          | assumption
          | eapply rng_sub'; [exact RSTK| lia] | exact RI
          | f_equal; clear - HK KX RWB H6 RW0 BB; lia
          | rewrite zlen_skipnA by (clear - HK KX RWB H6 RW0 BB; lia); f_equal; change 18446744073709551615 with (2^64 - 1); rewrite ?zb_land_mask by lia;
            rewrite ?Z.mod_small by (clear - HK KX RWB H6 RW0 BB; lia); clear - HK KX RWB H6 RW0 BB; lia
          | reflexivity ]
        | post_call asegs mc ] end end.
      clear CB.

      zstep.                                      (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      zstep. bcase KE.                            (* [comment removed for export] *)
      - eapply (CONT _ (k + (bv_unsigned rw + 3))); [| clear - HK KX RWB RW0; lia].
        unfold hinv. repeat match goal with |- _ /\ _ => split end. all: after_apply.
        all: zfin HK KX RWB HNB KE RW0.
      - zstep.                                    (* [comment removed for export] *)
        eapply ffsi_exitE. all: after_apply.
        all: zfin KE RW0.
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

    (* [comment removed for export] *)
    #[using="rc SP16 LOS LOC RSTK RI D N PLR NB PAY R8 RLO RHI RGR RGRS FH F256 RF RSF GH GF PL0 UNP0 RU0 H6"] Lemma ffsi_loop : forall (f : nat) mx k rw nb ipz rmz ja jb w0 w1 w2 (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      zlen bl - k <= Z.of_nat f ->
      hinv mx k rw nb ipz rmz ja jb w0 w1 w2 ->
      evtF asegs RNG POST_J (head_st mx k rw nb ipz rmz x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
    Proof.
      induction f as [|f IH]; intros until x31; intros FUEL HI.
      - eapply ffsi_step; [exact HI|]. intros until y31. intros HI2 HK2. exfalso.
        destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & HK & _). destruct HI2 as (_ & _ & _ & _ & _ & _ & _ & _ & HK' & _). cbn in FUEL. Local Ltac2 Set LiaHints.tbl := fun () => "0020?48306565083.12259314873579.12000000A00RS2H64FUEL3HK'3HK2S2H64FUEL3HK'3HK2".
lia.
      - eapply ffsi_step; [exact HI|]. intros until y31. intros HI2 HK2. unfold head_st in IH. eapply IH; [| exact HI2].
        destruct HI2 as (_ & _ & _ & _ & _ & _ & _ & _ & HK' & _). lia.
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

    (* [comment removed for export] *)
    #[using="rc SP16 LOS LOC RSTK RI D N PLR NB PAY R8 RLO RHI RGR RGRS FH F256 RF RSF GH GF PL0 UNP0 RU0 H6 H18"] Lemma ffsi_okpath : forall (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) mx (j48 : list byte) (w0 w1 w2 : list byte),
      core mx -> stk asegs mx lo SPAz -> rw_cells asegs mx SPAz [CB 48 j48; C8 (Z_to_bv 64 FF)] ->
      rw_cells asegs mx (Z.shiftr FF 3 + 2147450880) ([f1c; f1c; f1c; f1c; z1c; z1c; z1c; z1c; z1c; z1c; f2c; f2c; f2c; f2c; f8c; f8c; f3c; f3c; f3c; f3c] ++ FSHZ) -> rw_cells asegs mx FF FFHDR ->
      rw_cells asegs mx (FF + 32) ZFHC -> rw_cells asegs mx (FF + 112) [CB 4 w0; CB 4 w1; CB 4 w2] ->
      rw_cells asegs mx R [CB 8 r0; CB 8 r1; CB 8 r2] ->
      evtF asegs RNG POST_J
        (MS (mkR (Z_to_bv 64 0x8178c) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) (Z_to_bv 64 R) (Z_to_bv 64 S) (Z_to_bv 64 (zlen bl)) (Z_to_bv 64 (FF + 32)) e7 e8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) (Z_to_bv 64 2147450880) x28 x29 x30 x31)
            FR (Z_to_bv 64 0x818f8) fc None mx (seg_rom asegs)).
    Proof.
      intros until w2. intros C STL FRA SHF FF0 ZFH BP RR. pose proof C as C'. openc C. Local Ltac2 Set LiaHints.tbl := fun () => "01Q0?10375833354.14210751062487.3  10841825258.14111383349470.14111750063593.14112311023065.14112357356857.13912428150072.14713210268013.14814453460750.13915867410649.14115981451125.8  16083456449.14216598268889.14217317695510.14019970786093.11520003768591.6  20133607273.2  20749162842.13921529912041.6  22718764814.13925076071819.14625076071819.14725076071819.1482595860444.2   26128783840.6  27434788809.13827478534713.14727736797930.13928040491972.14928244409929.14129514832494.14230665193763.14730886936982.14332284519535.14133680001082.14133897463481.13936742878330.14137326182295.14137341542897.9  37388626009.14138119484249.14238297424623.14239178121190.13939819800638.13341805334855.14742609501300.2  42760314647.14242782745529.14142968992041.13943293708626.1424359095406.142 4466284721.133 45982589382.14146187586605.13946356275438.14147085352612.14147219577582.14147946365538.14148690461896.13849943447116.14150592957753.14250629934895.14951627303145.14152567164907.13952567164907.14152567164907.14253557778676.13953582707338.14153638430191.1145595802578.12  56078305746.14156170384339.133563227834.142  56644364524.13957000377357.8  57622410744.14857701858490.4  58477402019.147598848478.141  61149760928.13361934652262.14062098338330.13962824932752.13363403938114.1486386823154.139 64180194694.1336548478672.8   6755966729.8   67710724553.1426801153045.133 6900360422.141 7139856330.141 8374517865.141 8803078713.139 8984541093.2   9294175833.142 00000N00R00_00l01f02L03F03G03m04:04`04g05305Y05b06@06D06J06W06[06h07N08409;09?09@09I09o0:L0:M0:[0;90;[0;d0<00<<0=60=S0>50>90>_0?E0?Q0?Z0@80@90@?0@a0A>0A[0BA0B_0Bh0C10C:0CX0D:0DX0ER0E[0Ed0F40F50Fo0G80GA0GJ0Gl0HJ0HO0H^0ID0IR0I^0Ig0Ik0J60J>0J`0Jm0K:0KC0KP0Kf0LL0MF0MO0MS0MT0Mb0Mk0N40NA0O;0P50P60P\S3LOS3LOC3RLO3ATR4SPAB3FHb3DHbS2H6S3FHb3BSF3DHbS3FHb3BSF3DHbS3LOS3LOC3RLO2GF2H63ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHuS3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHbS3LOS3LOC3RLO2GF2H63ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHuFS3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHbS3FHb3BSF3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHbS2H62DSS2NB3FHb3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHbS3FHb3DHbS3LOS3LOC3RLO3ATR4SPAB3FHa3FHbS2H6S4F256S3FHb3BSF3DHbS2H6S3FHb3BSF3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHbS3LOS3LOC3RLO2GF2H63ATR4SPAB3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHu3FHc3GHcS2KESS3FHb3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHbS3LOS3LOC3RLO3ATR3FHb3BSF3DHbFS4SPAB3FHb3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3DHbS3LOS3LOC3RLO3ATR4SPAB3FHa3FHb3DHbS3FHb3DHbS3FHb3DHb2HBS3FHb3DHb2HBS3LOS3LOC3RLO2GF2H63ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHuS3LOS3LOC3RLO3ATR3FHb3BSF3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3BSF3DHbS2SNS3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHbS3FHb3DHb2HBS3FHb3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3DHbFS4F256S3LOS3LOC3RLO3ATR4SPAB3FHb3BSF3DHbS3LOS3LOC3RLO3ATR3FHb3BSF3DHbS3LOS3LOC3RLO3ATR3FHb3BSF3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3DHbS3FHb3DHbS3FHb3DHbS3FHb3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3BSF3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3DHbS3LOS3LOC3RLO2GF2H63ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHuS3FHb3DHbS3FHb3DHbS2H63H183FHb3DHbFS3LOS3LOC3RLO2GF2H63ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHuS3FHb3DHbS3FHb3DHbS3FHb3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3BSF3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3DHbS3FHbS2H62DS2SN4SEPFS3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHbS4SPAB3FHb3DHbS3FHb3DHb2HBS3FHb3DHbS2H6S3FHb3DHb1HS2H63H18S3LOS3LOC3RLO3ATR4SPAB3FHa3FHb3DHbS3FHb3BSF3DHbS3FHa3FHb3DHbS3FHb3DHbS3FHb3BSF3DHbS3RLO3RHI4SPAB3FHb3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHbS3LOS3LOC3RLO2GF2H63ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHuS3FHb3DHbS2H6SS4SPAB3FHb3DHbS3FHb3DHbS3FHb3DHbS3FHb3BSF3DHbS3LOS3LOC3RLO2GF2H63ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHuS3LOS3LOC3RLO2GF2H63ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHuSS3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHb".
prepF. unfold FSHZ in SHF. cbn [app] in SHF.
      zstep. zstep.                               (* [comment removed for export] *)
      zstep. rewrite (zx32_smallA h) by (clear - H6 H18; lia).   (* [comment removed for export] *)
      zstep. zstep.                               (* [comment removed for export] *)
      zstep. zstep.                               (* [comment removed for export] *)
      zstep. zstep.                               (* [comment removed for export] *)
      zstep. zstep. zstep.                        (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      pose proof cbsA as CB. unfold cbsA_stmt in CB.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
        lazymatch goal with SHx : rw_cells asegs mc (Z.shiftr FF 3 + 2147450880) _, MUx : munch _ m mc, BPx : rw_cells asegs mc (FF + 112) _ |- _ =>
        pose proof (bytes_at_transport asegs _ m mc _ _ PL0 MUx f2_djpl) as PLx;
        eapply evtF_cut;
        [ eapply (CB RNG _ SPAz gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR fc mc (S + h) (skipn (Z.to_nat (h)) bl) D N (FF + 112) lo);
          [ apply (buf_atA_skipn mc S bl); [split; [exact PLx| exact PLR]| clear - H6 H18 BB; lia]
          | eapply unpoisoned_sub; [eapply unpoisoned_munch; [exact UNP0| exact MUx| exact f2_djp]| clear - H6 H18 BB; lia| rewrite zlen_skipnA by (clear - H6 H18 BB; lia); clear - H6 H18 BB; lia]
          | clear - H6 H18 BB DS; lia
          | rewrite zlen_skipnA by (clear - H6 H18 BB; lia); clear - SN H6 H18 BB; lia
          | exact NN | exact DH | exact D16 | exact RGA | exact RGS
          | exact BPx
          | clear - F256; unfold bx in F256; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia
          | eapply ablk_sub; [exact FH| lia| lia]
          | rewrite zlen_skipnA by (clear - H6 H18 BB; lia); clear - SEPF DS SN H6 H18 BB; lia
          | apply (fsh3_bp mc FF); [unfold FSH3, FSHZ; cbn [app]; exact SHx| clear - F256; unfold bx in F256; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia| lia]
          | eapply rng_sub'; [exact RF| lia]
          | eapply rng_sub'; [exact RSF|]; rewrite !shad_div; clear - FHb; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia
          | assumption | assumption
          | assumption | exact LOC | lia | unfold KEND; lia
          | assumption
          | eapply rng_sub'; [exact RSTK| lia] | exact RI
          | f_equal; clear - H6 H18 BB; lia
          | rewrite zlen_skipnA by (clear - H6 H18 BB; lia); f_equal; change 18446744073709551615 with (2^64 - 1); rewrite ?zb_land_mask by lia;
            rewrite ?Z.mod_small by (clear - H6 H18 BB; lia); clear - H6 H18 BB; lia
          | reflexivity ]
        | post_call asegs mc ] end end.
      clear CB.

      zstep.                                      (* [comment removed for export] *)
      zstep. bcase KE.                            (* [comment removed for export] *)
      { eapply ffsi_exitE. all: after_apply.
        all: zfin KE. }
      zstep. zstep. neglit (-8).                  (* [comment removed for export] *)
      eapply (ffsi_loop (Z.to_nat (zlen bl)) _ h); [clear - H6; lia|].
      unfold hinv. repeat match goal with |- _ /\ _ => split end. all: after_apply.
      all: zfin H6 H18 KE BB.
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  End Frame.

  (* [comment removed for export] *)
  #[using="rc SP16 LOS LOC RSTK RI D N PLR NB PAY R8 RLO RHI RGR RGRS FH F256 RF RSF GH GF PL0 UNP0 RU0"] Lemma ffsi_gret : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (r : Z) (j48 j1 hb j2 r0 r1 r2 w0 w1 w2 : list byte),
    core m -> stk asegs m lo SPAz -> rw_cells asegs m SPAz [CB 48 j48; C8 (Z_to_bv 64 FF)] ->
    rw_cells asegs m (Z.shiftr FF 3 + 2147450880) ([f1c; f1c; f1c; f1c; z1c; z1c; z1c; z1c; z1c; z1c; f2c; f2c; f2c; f2c; f8c; f8c; f3c; f3c; f3c; f3c] ++ FSHZ) -> rw_cells asegs m FF FFHDR ->
    rw_cells asegs m (FF + 32) [CB 24 j1; CB 4 hb; CB 20 j2] ->
    (r mod 2^64 = 0 -> exists h, hb = le4 (Z_to_bv 64 h) /\ 6 <= h <= zlen bl /\ h <= 18) ->
    rw_cells asegs m (FF + 112) [CB 4 w0; CB 4 w1; CB 4 w2] ->
    rw_cells asegs m R [CB 8 r0; CB 8 r1; CB 8 r2] ->
    evtF asegs RNG POST_J
      (MS (mkR (Z_to_bv 64 0x8178c) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) (Z_to_bv 64 R) (Z_to_bv 64 S) (Z_to_bv 64 (zlen bl)) (Z_to_bv 64 (FF + 32)) e7 e8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) (Z_to_bv 64 2147450880) x28 x29 x30 x31)
            FR (ret_pc (Z_to_bv 64 0x8178c)) fc None m (seg_rom asegs)).
  Proof.
    intros until w2. intros C STL FRA SHF FF0 ZFH RF0 BP RR. pose proof C as C'. openc C. Local Ltac2 Set LiaHints.tbl := fun () => "0160?10990985245.13110990985245.1321532592225.130 1532592225.131 15334474333.13115334474333.13218091811352.13118091811352.13218437397164.13118437397164.13219302942247.13119302942247.13219970786093.11321426538131.13121426538131.1322179254107.131 2179254107.132 22000554496.11522200344330.13122200344330.1322601737496.131 2601737496.132 29010567573.11629010571016.11729018245758.13129018245758.1323188101182.122 3188101182.123 3188101183.118 3188101183.119 35497693828.11735497696281.11635670257402.11735670257402.11838450959742.12138450959742.12243754901852.11843754901852.11945432039387.13145432039387.1325089449082.121 5089449082.122 52567164907.13152567164907.13253638430191.11254302169230.2  5537889499.131 5537889499.132 56500923902.11756500923902.11857018326411.12257018326411.12357020423608.11857020423608.11959308628304.1  59308628433.1  59315053158.3  59991009117.12759991009117.1286192067805.122 6192067805.123 63370524077.11863370524077.11965071494699.12365071494699.12465073591832.11965073591832.12065499904044.12265499904044.12368516218382.2  00000L00h00m01201K01d02902N02n03N03V03^04<04E04N04n05N05S06806Y06n07C07D07E07N07W07l08A08V08k09009509:09?09D09I09N09S0:30:S0:X0:]0:b0:g0:l0;00;P0<00<50<:0<?0<D0<I0<N0<R0<V0<\0=50=N0=S0=X0=]0=b0=g0=l0>10>60>;0>@0>DS3LOS3LOC3RLO3ATR3FHb3BSF2HBS3LOS3LOC3RLO3ATR3FHb3BSF2HBS3FHbS3FHbS3LOS3LOC3RLO3RHI3ATR3FHbS3LOS3LOC3RLO3RHI3ATR3FHbS3LOS3LOC3RLO3ATR3FHbS3LOS3LOC3RLO3ATR3FHbS3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3FHb2HBS3FHb2HBS3LOS3LOC3RLO3ATR4SPAB3FHa3FHbS3RLO3FHbS3RLO3FHbS3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3FHbS3LOS3LOC3RLO3ATR4SPAB3FHa3FHb3GHa2HBS3LOS3LOC3RLO3ATR4SPAB3FHa3FHb2HBS3LOS3LOC3RLO3ATR3FHbS3LOS3LOC3RLO3ATR3FHbFFS3RHI3FHbS3RHI3FHbS3LOS3LOC3RLO3ATR3FHbS3LOS3LOC3RLO3ATR3FHbS3LOS3LOC3RLO3ATR3FHbS3LOS3LOC3RLO3ATR3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3FHbS3FHbS3FHbS3FHbS3FHbS2R8S3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS2K1S2K2S2KE1CS3LOS3LOC3RLO3RHI3ATR3FHbS3LOS3LOC3RLO3RHI3ATR3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS2R8".
prep2. retlitA.
    unfold FSHZ in SHF. cbn [app] in SHF.
    zstep.                                        (* [comment removed for export] *)
    zstep. bcase KE.                              (* [comment removed for export] *)
    { (* [comment removed for export] *)
      zstep. zstep. zstep.                        (* [comment removed for export] *)
      rsh8 8 RS1.
      zstep. cbv beta. rewrite (byte_litA 0) by lia.
      zstep. bcase K1; [exfalso; clear - K1; lia|].
      zstep.                                      (* [comment removed for export] *)
      zstep. zstep. zstep.                        (* [comment removed for export] *)
      rsh8 16 RS2.
      zstep. cbv beta. rewrite (byte_litA 0) by lia.
      zstep. bcase K2; [exfalso; clear - K2; lia|]. (* [comment removed for export] *)
      eapply ffsi_dbe. all: after_apply.
      all: intros C; exfalso; clear - C KE; rewrite ?unsigned_lit_wrap in *; lia. }
    zstep. bcase KZ.                              (* [comment removed for export] *)
    { destruct (RF0 ltac:(clear - KZ; rewrite ?unsigned_lit_wrap in KZ; first [exact KZ | lia])) as (h & -> & H6 & H18).
      lazymatch goal with H : rw_cells _ ?m1 (FF + 32) [CB 24 j1; CB 4 (le4 ?w); CB 20 j2] |- _ =>
        pose proof (proj1 (proj1 H)) as WF; cbn [cells_wf cell_wf] in WF;
        apply (rw_cells_recast asegs m1 (FF + 32) _ [CB 24 j1; C4 w; CB 20 j2]) in H;
          [| cbn [cells_wf cell_wf]; tauto | reflexivity | reflexivity] end.
      eapply ffsi_okpath. all: after_apply. }
    (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    rsh8 8 RS1.
    zstep. cbv beta. rewrite (byte_litA 0) by lia.
    zstep. bcase K1; [exfalso; clear - K1; lia|].
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    rsh8 16 RS2.
    zstep. cbv beta. rewrite (byte_litA 0) by lia.
    zstep. bcase K2; [| exfalso; clear - K2; lia]. (* [comment removed for export] *)
    eapply ffsi_dbe. all: after_apply.
    all: intros C; exfalso; rewrite unsigned_lit_wrap in C; revert C; vm_compute; discriminate.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="rc SP16 LOS LOC RSTK bl D R R8 RLO FH RF RSF GH GF RG"] Lemma ffsi_release : forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31 : word) mx (cl : list cell),
    rw_cells asegs mx (SP + -104) FFRB -> rw_cells asegs mx (FF + 248) [C8 (Z_to_bv 64 FLG)] -> rw_cells asegs mx FLG [C1 (Z_to_bv 8 1)] ->
    stk asegs mx (SPAz + 56) (SP + -104) -> stk asegs mx lo SPAz -> rw_cells asegs mx SPAz cl -> cells_size cl = 56%nat ->
    rw_cells asegs mx (Z.shiftr FF 3 + 2147450880) FSH1 -> mem_inv asegs mx ->
    evtF asegs RNG (fun ms' => exists mp m',
        ms' = MS (mkR ra (Z_to_bv 64 SP) gp tp y5 y6 y7 s0 s1 (Z_to_bv 64 FLG) y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                 FR (ret_pc ra) fc None m' (seg_rom asegs)
        /\ munch [(Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 32)] mx mp /\ wmono asegs mx mp /\ mem_inv asegs mp
        /\ munch [(FLG, FLG + 1)] mp m' /\ wmono asegs mp m' /\ mem_inv asegs m'
        /\ stk asegs m' lo SP /\ rw_cells asegs m' FLG [C1 (Z_to_bv 8 0)])
      (MS (mkR y1 (Z_to_bv 64 SPAz) gp tp y5 y6 y7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 FF) y19 y20 y21 y22 y23 y24 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) (Z_to_bv 64 2147450880) y28 y29 y30 y31)
            FR (Z_to_bv 64 0x8182c) fc None mx (seg_rom asegs)).
  Proof.
    intros until cl. intros FRB FF248 FLC STG STL FRA CL SHF MI.
    pose proof atop_range as ATR. unfold KEND in SPT. unfold AFI_STACK in LOS.
    pose proof (proj1 (spa160_propsA SP SP16)) as SPAB.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa. pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
    pose proof (ablk_lin _ _ GH) as (GHa & GHb & GHc & GHd). unfold AIMG_HI in GHa. pose proof GH as GHu. unfold ablk, AIMG_HI, KLS in GHu.
    pose proof RSF as RSF'. Local Ltac2 Set LiaHints.tbl := fun () => "05?0?1018082058.120 10299541350.12010757196425.12010841825258.12011350655860.12011603250610.12011776021145.12011805467289.11811805467289.11911805467289.12012066655206.11912342077012.12012649602618.12012911143428.12013067081226.11913325022025.12013547350398.12013641502813.118136972401.119  13701124551.11913890391188.12013912086366.12014033283697.12014738355418.12014793220770.12014866570234.12014981645286.12015010729543.11815059373769.12015160347210.11915188853002.11815309128057.12015341314694.12015440269036.12015497861449.12015719060185.12016036404119.11816141167028.12016598268889.12016867429482.11917162010020.12017264948956.11917317695511.11917404902110.12017444521370.12017635619076.12018138708044.12018368439854.12018660396218.12018759279913.12019272833703.11719570126950.12020139715884.12020563474841.12020563939225.12020749162842.12020810893807.1132089572985.120 21139636686.1202139396638.120 21470349994.11921610876870.12021917429068.12022087971884.12022298171673.12022416474134.11422544861286.12022700267513.11522775997703.11922843528825.12022895698612.12023098415148.12023223569694.12023404677272.1202342125148.119 23499613609.12023584418860.11823637580569.12023716884570.1202408208167.119 24085599111.11924516908640.12024521592556.11924686014778.12024801268105.12025082048471.1192509489337.120 25117449465.1202521080681.120 25653217698.12025862343643.12026048924876.12026348902346.12026416457748.12026669182065.12026671158508.1202673550442.120 26739224554.12026774769626.11927045444308.12027058951505.11927334627497.12027622887044.12028244409929.12028322672359.11928339690855.11928490377204.12028516984212.11828897571974.11928987856538.11929139002340.12029181457478.12029192875980.12029789957596.11930013766257.12030032268340.12030151347498.12030185424027.12030561560391.11930906104780.1203145208153.120 31518365030.1203199430677.120 32087020145.12132130763846.12032365281766.11832376603722.12032966260985.1203323235066.120 33680001082.12033864347846.12033897463481.12033965537418.12033969101564.12034067874935.11934098841190.120341926775.118  34490278001.11934782976605.11835235452859.12035301401292.12035381703415.11935894910345.12036172772266.1203619125578.120 36473820158.12036550167516.11936685953222.11937066468830.12037349358057.11937388626009.12037545354041.11937566535918.12037813484969.12037906871084.12038350898988.12038389508810.12038709023052.11938889460260.11938932229498.1203913742100.120 39178121190.12039419589006.12039640754311.11940058685594.12040093537476.12040324494905.11940401672937.12040456106473.12040811138462.12041044649514.12041055142510.12041091132398.12041377675910.12041615107788.12041947725143.11942200342570.12042452747910.12042782745529.12042831019478.12042919482676.12042968992041.12043054286892.12043146938807.11943641966310.11943833837156.12043872227804.11944229320300.12044417097546.12044456543799.11945003960668.11945221239098.12045342999668.1194537091657.120 45508725130.12045585588076.120456469350.120  45740938393.11945881473900.12045982589382.1204606400646.120 46080113946.1204641771485.118 46525677412.12046787521756.11946924073390.12046949129329.12047085352612.12047646465612.12047784655834.12048046123689.12048211285674.1204831013226.120 4861306889.118 48650452329.12048690461895.11949164012678.12049656697097.12049763279678.12049943447116.12050018932218.12050070184004.12050524051526.12051046823191.11951766063161.12051781592412.11951816630506.12052048616164.12052107682714.12052196777463.11952366239022.1205253856742.120 52631624166.12052973911975.11953018266553.12053036558889.12053472464966.12053541803018.12053557778676.12053638430191.10353706860006.12054068232029.11854077074143.12054226150513.12054256297073.11954279058471.11954374972478.12055142594814.11355190259372.11355846471854.12056027773562.120563227834.120  5634116633.118 56376734585.12056482153492.1205649771342.120 56644364524.12056804907040.12056830590924.12057089830186.12057466002425.12057496662641.12057533215052.11957871968190.12057919919806.12058116526106.12058143722584.12058226117964.12059118738686.1205927369223.119 59338331354.12059444586470.12059705885297.11959849706346.12059982339895.11960135071334.12060211452398.12060321776441.12061081885454.12061849248249.12061986099753.12062052811751.11962055344378.12062098338330.12062154059789.12062596255172.12062598956670.11962619446612.12062632894729.12062719221382.12063362316391.11963392461657.12063700058990.11963726620298.12063958622316.12064026414714.11864322305738.12064562105998.12064696793412.11964993435597.12065110321578.12065312824268.12065678933017.12065707003017.12066111488204.12066183421017.12066948228265.11967114676681.11967358824282.12067382833310.12067520808170.12067709824076.12067710724553.12067810302577.12067912497303.11968066155898.1186924395529.120 6961534551.119 6968827998.119 7039361418.120 7139856330.120 7309853801.120 7342793742.118 7555993734.120 763619204.120  8267992279.119 8374517865.120 8710768218.120 8747329497.120 8905668329.120 8955631908.120 9130008270.120 9415653658.120 9417716919.119 9899865354.120 00000<00D00n01:01[01c02M02U02]02e02m03N03Z04;04G05105[05g05o06706X07B07J07V08@08L08T08\09F09R09Z0:D0:L0:T0;00;L0;T0<50<_0<k0=L0=X0=`0>J0>V0?70??0?i0@50@_0@g0@o0A70AS0B=0BI0BQ0Bm0CW0DA0DM0DU0D]0De0EO0E[0Ec0Em0F50F_0G@0GH0H20H>0HJ0I40I<0IX0Id0Il0J40JU0J]0Ji0KE0KM0Ki0LS0Lo0M70M?0MG0MS0N40N<0ND0NP0N\0Nh0OI0OQ0P;0P\0Q80Q@0QH0Qi0RJ0RR0R^0S?0SG0SO0S[0Sc0TD0TP0U90UA0UI0Ue0Um0VI0VQ0VY0Va0Vm0WI0WU0Wa0Wi0XS0X_0YI0YQ0YY0Ya0Yi0Z50ZA0ZI0ZQ0[;0[G0[S0\=0\I0\Q0];0]e0^O0^k0_U0`10`90`A0`M0`U0a60aB0ac0ak0bU0b]0bi0cJ0d40dP0dl0eV0eb0fL0fX0f`0fh0g00g<0gD0g`0gl0hM0hi0i10i90iA0ib0in0j60jB0jJ0jV0jb0kC0km0l90lA0lI0le0lm0m50m=0mI0mU0n60nB0nl0o40oU0o]0oi10110=10I10e11O11W11_12I13313;13G13h14014814T14`14l15M15Y15a16K16S16[16c17M18718?18K18l19419<19H19T19\19d19l1:V1;;1;`1<J1<V1<b1=L1=h1>L1?61?>1?F1?N1?Z1@61@>1@F1A01AZ1Af1B11B91Bc1Bk1C71C?1CG1CS1C[1Cc1DM1E71Ea1FK1Fg1Fo1G;1GG1H11HR1I<1I]1J91JA1JI1K31K]1Ki1L11L=1LI1M31MT1M\1Mh1N01NL1Nh1O01OL1Oh1PR1P^1QH1QT1Q\1R81R@1RH1RT1S>1SF1T01T<1TH1Td1UN1UV1V71V?1Vi1W51WQ1X;1X\1YF1YR1YZ1YfS2CL3FHb3BSFS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS2CL3FHbS2CL3FHbS2CL3FHbS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS2CL3FHbS2CL3FHbS2CL3FHbS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS2CL3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS2CL3FHbS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS2CL3FHbS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS2CL3FHbS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS2CL3FHbS2CL3FHbS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS2CL3FHbS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS2CL3FHbS2CL3FHbS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS2CL3FHbS2CL3FHbS2CL3FHb1HS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3GHaS3LOS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHb3BSFS2CL3FHbS2CL3FHbS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHbS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS2CL3FHbS2CL3FHbS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHbS2CL3FHbS2CL3FHb3BSFS2CL3FHb3BSFS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS2CL3FHbS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHbS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHbS2CL3FHbS3LOS2CL3FHbS2CL3FHbS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHa3FHb3FHc3GHcS2CL3FHbS2CL3FHbS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS2CL3FHbS2CL3FHbS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHb3BSFS2CL3FHb3BSFS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS2CL3FHbS2CL3FHbS2CL3FHbS3LOS2CL3FHbS2CL3FHb3GHdS2CL3FHbS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS2CL3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS2CL3FHbS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS2CL3FHbS2CL3FHb3BSFS2CL3FHbS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS2CL3FHbS2CL3FHbS2CL3FHbS2CL3FHb3BSFS2CL3FHbS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS2CL3FHbS2CL3FHbS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS2CL3FHbS2CL3FHbS2CL3FHb3BSFS2CL3FHbS3LOS2CL3FHbS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS2CL3FHbS2CL3FHbS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS2CL3FHbS2CL3FHbS2CL3FHb3BSFS3LOS2CL3FHbS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHbS2CL3FHb3BSFS2CL3FHbS2CL3FHb3BSFS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHbS2CL3FHbS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS2CL3FHbS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHb3BSFS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS2CL3FHbS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHbS2CL3FHbS3LOS2CL3FHbS3LOS2CL3FHbS2CL3FHbS2CL3FHbS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHa3FHb3GHaS3LOS3LOC3RLO2CL3ATR4SPAB3FHa3FHb3GHaS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS2CL3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHa3FHb3FHc3GHcS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS2CL3FHbS2CL3FHbS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS2GF2CL3FHbS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS2CL3FHb3BSFS2CL3FHbS2CL3FHbS2CL3FHb3BSFS2CL3FHbS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS2CL3FHb3BSFS2CL3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS2CL3FHbS2CL3FHb3BSFS2CL3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHbS2CL3FHb3BSFS2CL3FHbS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS2CL3FHbS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS2CL3FHbS2CL3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS2CL3FHbS2CL3FHb3BSF".
replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in RSF' by (unfold shad, ASHOFF; lia).
    pose proof f2_bsf as BSF. boxH SP16. boxH F256.
    assert (LO0 : 0 <= lo) by (destruct STL as [? _]; assumption).
    unfold FSH1, FSHZ in SHF. cbn [app] in SHF. unfold AF_fi_ffsi.FFRB in FRB.
    pose proof (munch_refl [(Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 32)] mx) as MU1. pose proof (wmono_refl asegs mx) as WM1.
    zstep. neglit (-11).                          (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    sok0 (Z.shiftr FF 3 + 2147450880).
    zstep. clear SOK. zstep. zstep. zstep.        (* [comment removed for export] *)
    do 4 zstep.                                   (* [comment removed for export] *)
    do 4 zstep.                                   (* [comment removed for export] *)
    do 4 zstep.                                   (* [comment removed for export] *)
    do 4 zstep.                                   (* [comment removed for export] *)
    do 4 zstep.                                   (* [comment removed for export] *)
    do 4 zstep.                                   (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mp _) =>
      lazymatch goal with MIx : mem_inv asegs mp |- _ => pose proof MIx as MIp; boxH MIp end;
      pose proof (munch_refl [(FLG, FLG + 1)] mp) as MU2; pose proof (wmono_refl asegs mp) as WM2 end.
    boxH MU1. boxH WM1.
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    do 13 zstep.                                  (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    (* [comment removed for export] *)
    eapply stk_release in FRA; [| exact STL| lia]. rewrite CL in FRA. change (Z.of_nat 56) with 56 in FRA.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mf _) =>
      pose proof (stk_merge asegs mf lo (SPAz + 56) (SP + -104) FRA STG ltac:(lia)) as ST2 end.
    release_frame FRB ST2 SP.
    apply evtF_done. unfold bx in MU1, WM1, MIp.
    eexists _, _. split; [reflexivity|].
    split; [first [exact MU1| eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside]; intros; lia]|]. split; [exact WM1|]. split; [exact MIp|].
    split; [eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside]; intros; lia|]. split; [exact WM2|]. split; [eassumption|].
    split; [exact ST2| assumption].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End S.
End CANSEC1.
