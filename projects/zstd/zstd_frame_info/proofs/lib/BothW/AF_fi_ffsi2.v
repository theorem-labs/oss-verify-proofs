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
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg ABase RtCells AProto AMalloc_iface AHarness_iface AH_fi_iface AF_fi_kit AF_fi_chk AF_fi_chk3 AF_fi_cbs AF_fi_ffsi.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.
Ltac brr := first [if_true | if_false].
(* [comment removed for export] *)
Ltac guard_false :=
  first [ brr
        | let G := fresh "G" in if_cases G; zify_cond G;
          [ exfalso; first [ lia | rewrite ?unsigned_lit in G by lia; lia | rewrite ?unsigned_lit_wrap in G; rewrite ?Z.mod_small in G by lia; lia ]
          | clear G ] ].
Tactic Notation "guard_falseH" ne_hyp_list(hs) :=
  first [ brr
        | let G := fresh "G" in if_cases G; zify_cond G;
          [ exfalso; clear - G hs; change 18446744073709551615 with (2^64 - 1) in *; rewrite ?zb_land_mask in G by lia;
            first [ lia | rewrite ?unsigned_lit in G by lia; lia | rewrite ?unsigned_lit_wrap in G; rewrite ?Z.mod_small in G by lia; lia ]
          | clear G ] ].

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
#[using="Type"] Lemma fsh3_bp : forall m FF, rw_cells bsegs m (Z.shiftr FF 3 + 2147450880) FSH3 -> FF mod 8 = 0 -> 0 <= FF ->
  rw_cells bsegs m (shad (FF + 112)) [z1c; c04].
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
  Variables (e8 e9 : word) (m : amem) (FF FLG S : Z) (bl : list Z) (D N R : Z).
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
  Hypotheses (PL0 : bytes_at bsegs m S (map (Z_to_bv 8) bl)) (UNP0 : unpoisoned m S (S + zlen bl)) (RU0 : unpoisoned m R (R + 24)).

  (* [comment removed for export] *)
  Definition core (mx : amem) : Prop :=
    rw_cells bsegs mx (SP + -104) FFRB /\ rw_cells bsegs mx (FF + 248) [C8 (Z_to_bv 64 FLG)] /\
    rt_got mx /\ rt_shbase mx /\
    stk bsegs mx (SPAz + 56) (SP + -104) /\ munch W5 m mx /\ wmono bsegs m mx /\ mem_inv bsegs mx.

  (* [comment removed for export] *)
  Definition POST_J : machine_state -> Prop :=
    fun ms' => exists (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y23 y24 y25 y28 y29 y30 y31 : word)
                      (cl : list cell) (nb : list byte) (cs db : word) (m' : amem),
      ms' = MS (mkR y1 (Z_to_bv 64 SPAz) gp tp y5 y6 y7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) y10 y11 y12 y13 y14 y15 y16 y17
                   (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) y20 y21 y22 y23 y24 y25 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF)
                   y28 y29 y30 y31)
               FR (Z_to_bv 64 0x819c0) fc None m' (seg_rom bsegs)
      /\ core m' /\ stk bsegs m' lo SPAz
      /\ rw_cells bsegs m' SPAz cl /\ cells_size cl = 56%nat
      /\ rw_cells bsegs m' (Z.shiftr FF 3 + 2147450880) FSH1
      /\ rw_cells bsegs m' FF [C8 (Z_to_bv 64 0x45e0360e); C8 (Z_to_bv 64 0x1a436); C8 (Z_to_bv 64 0x81628)]
      /\ rw_cells bsegs m' R [CB 8 nb; C8 cs; C8 db]
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
  #[using="rc SP16 LOS LOC RSTK S D RLO FH RF RSF GH GF PL0"] Lemma ffsi_scope : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 y20 y21 y22 y23 y24 y25 x28 x29 x30 x31 : word) mx
      (cl : list cell) (nb : list byte) (cs db : word),
    core mx -> stk bsegs mx lo SPAz -> rw_cells bsegs mx SPAz cl -> cells_size cl = 56%nat ->
    rw_cells bsegs mx (Z.shiftr FF 3 + 2147450880) ([f1c; f1c; f1c; f1c; z1c; z1c; z1c; z1c; z1c; z1c; f2c; f2c; f2c; f2c; f8c; f8c; f3c; f3c; f3c; f3c] ++ FSHZ) ->
    rw_cells bsegs mx FF FFHDR ->
    rw_cells bsegs mx R [CB 8 nb; C8 cs; C8 db] -> (bv_unsigned cs < 2^64 - 119 -> 1 <= bv_unsigned cs <= zlen bl) ->
    evtF bsegs RNG POST_J
      (MS (mkR x1 (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) y20 y21 y22 y23 y24 y25 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) x28 x29 x30 x31)
            FR (Z_to_bv 64 0x81994) fc None mx (seg_rom bsegs)).
  Proof.
    intros until db. intros C STL FRA CL SHF FF0 RR CS. openc C. Local Ltac2 Set LiaHints.tbl := fun () => "01J0?11925506990.12212066655206.12212342077012.12212911143428.12213067081226.12213781830238.12214159447534.12215010729547.12115160347210.12215497861449.12215719060185.12216036404123.12116279979987.12516753464773.12516867429482.12217941155254.12518909631322.12219039061412.12519272833707.12119970786093.11320139715884.12221062356398.12221470349994.12223584418860.12223687287154.12223823397578.12224521592556.12224686014778.12225108855438.1222673550442.122 26774769626.12227320971324.1242818573085.125 28322672363.12128516984212.12228897571974.12228987856538.12231693696482.12231930091218.12232365281766.12234098841190.122341926779.121  353645442.122  36685953222.12237349358057.12237545354041.12238389508810.12238709023052.12238889460260.12239340006770.12540324494905.12242452747910.12242583353243.12542643832943.125449256530.116  45221239098.12245342999668.12245740938393.12245958212890.1224605189994.122 4634497118.122 46553288074.12246901542423.12547284459504.12547747998098.1224861306889.122 5012112366.122 52107771838.12252567164907.12252567164907.12553638430191.11254769888194.1225634116633.122 56830590924.12257533215052.12258325306352.12559308628179.11660610120334.12261238456766.12262037933182.12263392461657.12264026414714.12264696793412.12266948228265.12267114676681.12268066155898.12268141365374.1226924395529.122 7303350522.122 9417716923.121 00000<00D00e01F01R01^01j02202>02Z03603>03F03m04904E04a05A05I05j06206>06J06R07907U07]07i08508A08M08U08]08e09F09N09Z0:A0:h0;00;80;@0;g0;o0<V0=20=>0=F0=g0>L0?30?;0?[0?g0@70@C0@d0A@0A\0B80BD0B`0Bh0C40C[0D70DC0DO0DW0D_0Dg0EN0F50F=0FE0FQ0F`0Fl0G80GD0Gk0H70HX0I40I[0Ig0J30JZ0K60K>S2CL3FHb3BSFS2CL3FHbS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHb3BSFS2CL3FHb3BSFS2CL3FHb3BSFS2CL3FHbS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS2CL3FHbS3LOS3LOC3RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS2CL3FHb3FHdS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3FHc3GHcS2CL3FHbS3LOS3LOC3RLO2CL3ATR4SPAB3FHa3FHbS2CL3FHbS2CL3FHb3BSFS2CL3FHb3BSFS2CL3FHbS3LOS3LOC3RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS2CL3FHb3BSFS2CL3FHb3BSFS2CL3FHb3BSFS2CL3FHb3BSFS2CL3FHbS2CL3FHbS2CL3FHbS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHbS2CL3FHb3BSFS3LOS3LOC3RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS2CL3FHbS2CL3FHbS3LOS3LOC3RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS3LOS3LOC3RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHb3BSFS2CL3FHbS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3FHc3GHcS3LOS3LOC3RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS3LOS3LOC3RLO2CL3ATR3FHb3FHc3GHcS2CL3FHa3FHbS2CL3FHa3FHb3FHdS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS2CL3FHa3FHbS3LOS3LOC3RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHb3BSFS2CL3FHb3BSFS2CL3FHbS2CL3FHbS2CL3FHbS3LOS3LOC3RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS2CL3FHbS2CL3FHa3FHbS2CL3FHa3FHb2K0S2CL3FHb3BSFS2CL3FHb3BSFS2CL3FHb3BSFS3LOS3LOC3RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC3RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS2CL3FHb3BSFS3LOS3LOC3RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHb".
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
  #[using="rc SP16 LOS LOC RSTK S D RLO RHI RGR FH RF RSF GH GF PL0"] Lemma ffsi_db : forall (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 y20 y21 y22 y23 y24 y25 x28 x29 x30 x31 : word) mx
      (cl : list cell) (nb r2 : list byte) (cs db : word),
    core mx -> stk bsegs mx lo SPAz -> rw_cells bsegs mx SPAz cl -> cells_size cl = 56%nat ->
    rw_cells bsegs mx (Z.shiftr FF 3 + 2147450880) ([f1c; f1c; f1c; f1c; z1c; z1c; z1c; z1c; z1c; z1c; f2c; f2c; f2c; f2c; f8c; f8c; f3c; f3c; f3c; f3c] ++ FSHZ) ->
    rw_cells bsegs mx FF FFHDR ->
    rw_cells bsegs mx R [CB 8 nb; C8 cs; CB 8 r2] -> (bv_unsigned cs < 2^64 - 119 -> 1 <= bv_unsigned cs <= zlen bl) ->
    evtF bsegs RNG POST_J
      (MS (mkR x1 (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) (Z_to_bv 64 (R + 16)) db x12 x13 x14 x15 x16 x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) y20 y21 y22 y23 y24 y25 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) x28 x29 x30 x31)
            FR (Z_to_bv 64 0x81990) fc None mx (seg_rom bsegs)).
  Proof.
    intros until db. intros C STL FRA CL SHF FF0 RR CS. pose proof C as C'. openc C. Local Ltac2 Set LiaHints.tbl := fun () => "00=0?13001224923.12316439798173.12319970786093.11324004349677.12237038741246.12337371137959.12340351813784.12344793722668.12352567164907.12353638430191.11256892209304.12363216898067.1237505495178.123 00000S01201S01[01g02202J02m03503=03U03a04ES3LOS3LOC3RLO2CL3ATR3FHb3FHc3GHc2HBS3LOS3LOC3RLO2CL3ATR3FHb3BSF2HBS3LOS3LOC3RLO2CL3ATR4SPAB3FHa3FHbS2CL3FHbS3RHI2CL3FHbS2CL3FHb2HBS3LOS3LOC3RLO2CL3ATR3FHbS3LOS3LOC3RLO2CL3ATR3FHb3FHc3GHc2HBS2CL3FHbS2CL3FHbS3LOS3LOC3RLO2CL3ATR3FHbS3RLO2CL3FHbS3LOS3LOC3RLO2CL3ATR4SPAB3FHa3FHb2HB".
prep2.
    zstep.                                        (* [comment removed for export] *)
    eapply ffsi_scope. all: after_apply.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
  (* [comment removed for export] *)
  #[using="rc SP16 LOS LOC RSTK S D RLO RHI RGR FH RF RSF GH GF PL0"] Lemma ffsi_dbe : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 y20 y21 y22 y23 y24 y25 x28 x29 x30 x31 : word) mx
      (cl : list cell) (nb r2 : list byte) (cs : word),
    core mx -> stk bsegs mx lo SPAz -> rw_cells bsegs mx SPAz cl -> cells_size cl = 56%nat ->
    rw_cells bsegs mx (Z.shiftr FF 3 + 2147450880) ([f1c; f1c; f1c; f1c; z1c; z1c; z1c; z1c; z1c; z1c; f2c; f2c; f2c; f2c; f8c; f8c; f3c; f3c; f3c; f3c] ++ FSHZ) ->
    rw_cells bsegs mx FF FFHDR ->
    rw_cells bsegs mx R [CB 8 nb; C8 cs; CB 8 r2] -> (bv_unsigned cs < 2^64 - 119 -> 1 <= bv_unsigned cs <= zlen bl) ->
    evtF bsegs RNG POST_J
      (MS (mkR x1 (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) (Z_to_bv 64 (R + 16)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) y20 y21 y22 y23 y24 y25 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) x28 x29 x30 x31)
            FR (Z_to_bv 64 0x8198c) fc None mx (seg_rom bsegs)).
  Proof.
    intros until cs. intros C STL FRA CL SHF FF0 RR CS. pose proof C as C'. openc C. Local Ltac2 Set LiaHints.tbl := fun () => "0020?19970786093.11353638430191.11200000Q00YS3LOS3LOC3RLO2CL3ATR4SPAB3FHa3FHbS2CL3FHb".
prep2.
    zstep.                                        (* [comment removed for export] *)
    eapply ffsi_db. all: after_apply.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="rc SP16 LOS LOC RSTK D R8 RLO RHI RGR RGRS FH RF RSF GH GF PL0 RU0"] Lemma ffsi_exitE : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 y19 y21 y23 y25 x28 x29 x30 x31 : word) mx
      (ja jb r0 r1 r2 : list byte) (cs : word),
    core mx -> stk bsegs mx lo SPAz -> rw_cells bsegs mx SPAz [CB 16 ja; C8 (Z_to_bv 64 R); C8 (Z_to_bv 64 FF); CB 16 jb; C8 (Z_to_bv 64 FF)] ->
    rw_cells bsegs mx (Z.shiftr FF 3 + 2147450880) FSH3 -> rw_cells bsegs mx FF FFHDR ->
    rw_cells bsegs mx R [CB 8 r0; CB 8 r1; CB 8 r2] -> 2^64 - 119 <= bv_unsigned cs ->
    evtF bsegs RNG POST_J
      (MS (mkR x1 (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) cs x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 2147450880) y19 (Z_to_bv 64 S) y21 (Z_to_bv 64 (FF + 32)) y23 (Z_to_bv 64 (FF + 112)) y25 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) x28 x29 x30 x31)
            FR (Z_to_bv 64 0x81b74) fc None mx (seg_rom bsegs)).
  Proof.
    intros until cs. intros C STL FRA SHF FF0 RR CSE. openc C. Local Ltac2 Set LiaHints.tbl := fun () => "0170?10841825258.13110990985245.12713001224923.13114031725080.1271532592226.126 15334474334.12716439798173.13117317695510.13018437397164.12719302942247.12719970786093.11120303812366.13120749162842.13121426538131.1272179254107.127 22200344330.12724004349666.13027736797930.13128500580888.12729018245758.1273188101182.119 3188101183.115 33897463481.13134763826958.13135670257402.11436742878330.13137038741246.13137371137959.13138450959742.11839178121190.13140351813784.13142782745529.13142968992041.13143754901852.11544471906526.13144793722668.13145982589382.13147085352612.13147946365538.13148690461894.13049943447116.1315089449082.118 52567164907.12752567164907.13153557778676.13153638430191.11054302169230.2  56500923902.11456644364524.13156892209304.13157018326411.11957020423608.11559308628304.1  59308628433.1  59308768411.3  59991009118.1236192067805.119 61934652264.12762098338330.13163216898067.13163370524077.1156386823154.131 65071494699.12065073591832.11665499904044.11968516218382.2  6900360424.121 7139856330.131 7505495178.131 8374517865.131 8968528094.131 00000900U01501J01O01h02D02I02i03103S03\03e03n04N05305805Q05f05o06D06Y07=07F07K07d07m08508:08?08T08m09F09K09T0:40:90:W0;;0;@0;E0;J0;O0;T0<20<70<;0<@0<E0<Z0<_0<d0<h0<l0=40=M0=R0=W0=`0=i0=n0>R0>W0>\0>a0>e0>j0?30?X0@<0@ES3FHb3BSFS3LOS3LOC3RLO3ATR3FHb3BSF2HBS3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3LOS3LOC3RLO3ATR3FHbS3FHbS3LOS3LOC3RLO3RHI3ATR3FHbS3LOS3LOC3RLO3ATR3FHb3BSF2HBS3FHbS3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3FHb2HBS3LOS3LOC3RLO3ATR4SPAB3FHa3FHb3GHaS3FHb3BSFS3FHb3BSFS3RLO3FHbS3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3LOS3LOC3RLO3ATR4SPAB3FHa3FHb3GHa2HBS3FHbS3LOS3LOC3RLO3ATR3FHb3BSFS3LOS3LOC3RLO3ATR3FHbS3RHI3FHbS3LOS3LOC3RLO3ATR3FHbS3LOS3LOC3RLO3ATR3FHbS3LOS3LOC3RLO2GF3ATR3FHb3FHu3GHu3BSFS3FHb3BSFS3FHbS3LOS3LOC3RLO3ATR3FHb3BSFS3RHI3FHbS3FHb2HBS3FHbS3FHbS3LOS3LOC3RLO3ATR3FHbS3LOS3LOC3RLO3ATR3FHb3BSFS3LOS3LOC3RLO3ATR3FHb3BSFS3FHbS3FHb3BSFS3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3FHbS3LOS3LOC3RLO3ATR4SPAB3FHb3BSFS3LOS3LOC3RLO2GF3ATR3FHb3FHu3GHu3BSFS3FHbS3FHbS3FHbS3FHbS3FHbS3LOS3LOC3RLO3ATR4SPAB3FHb3BSFS3FHbS2R8S3FHbS3FHbS3LOS3LOC3RLO3ATR3FHbS3FHbS3FHbS2K1S2K2S3CSE2CxS3LOS3LOC3RLO3RHI3ATR3FHbS3FHbS3FHbS3FHb3BSFS3RLO3FHbS3FHbS3LOS3LOC3RLO2GF3ATR3FHb3FHu3GHu3BSFS3FHbS3FHbS3FHbS2R8S3FHbS3FHb3BSFS3LOS3LOC3RLO3ATR4SPAB3FHa3FHb3GHa2HBS3LOS3LOC3RLO2GF3ATR3FHb3FHu3GHu3BSFS3FHb3BSF".
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
    #[using="rc SP16 LOS LOC RSTK D N NB PAY R8 RLO RHI RGR RGRS FH RF RSF GH GF PL0 RU0 H6"] Lemma ffsi_fin2 : forall (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 y21 y25 x28 x29 x30 x31 : word) mx
        (ja jb : list byte) (db : word) (k nb ipz : Z),
      core mx -> stk bsegs mx lo SPAz -> rw_cells bsegs mx SPAz [CB 16 ja; C8 (Z_to_bv 64 R); C8 (Z_to_bv 64 FF); CB 16 jb; C8 (Z_to_bv 64 FF)] ->
      rw_cells bsegs mx (Z.shiftr FF 3 + 2147450880) ([f1c; f1c; f1c; f1c; z1c; z1c; z1c; z1c; z1c; z1c; f2c; f2c; f2c; f2c; f8c; f8c; f3c; f3c; f3c; f3c] ++ FSHZ) -> rw_cells bsegs mx FF FFHDR ->
      rw_cells bsegs mx R [CB 8 r0; CB 8 r1; CB 8 r2] -> h <= k <= zlen bl -> 0 <= nb <= k -> ipz = S + k ->
      evtF bsegs RNG POST_J
        (MS (mkR x1 (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) x10 db x12 (Z_to_bv 64 R) x14 x15 x16 x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 nb) (Z_to_bv 64 S) y21 (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 ipz) (Z_to_bv 64 (FF + 112)) y25 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) x28 x29 x30 x31)
            FR (Z_to_bv 64 0x81c30) fc None mx (seg_rom bsegs)).
    Proof.
      intros until ipz. intros C STL FRA SHF FF0 RR HK HNB ->. openc C. Local Ltac2 Set LiaHints.tbl := fun () => "00m0?10990985245.13714031725080.13715047390338.1211532592226.136 15334474333.13818437397164.13719302942247.13719970786093.11721426538131.1372179254107.137 22122868332.13022200344330.13722527583800.13022954551237.1302603756902.130 26631416763.8  26824457180.13428500580888.13729018245758.13729791052619.1303188101180.121 3188101182.129 3188101183.125 33503717167.13035497761944.13135670257402.12435892103014.12035970547514.12937254250633.13038450959742.12840107376748.13043754901852.12545049100339.12146134221986.2  5089449082.128 51621919586.12052567164907.13052567164907.13753638430191.11654302169230.2  55320869225.13056500923902.12457018326408.12957018326411.12557020423608.12159245416335.13059308628179.1  59308628304.1  59308628433.1  59991009117.1346192067805.129 61934652265.13663370524077.12564295209536.13464373332722.13065071494696.13065071494699.12665073591832.12265093347183.13065499904044.12968516218382.2  00000L00a00f00k01D01d01l02J02S03303H03i04I04N04o05<05=05R05[05c06806M06b06k07307807=07B07^07c08808=08B08F08K08P08U08Z08_08c09<09A09F09K09P0:00:40:80:<0:U0:Z0:_0:d0;N0;W0;\0;a0;f0;k0<00<4S3LOS3LOC3RLO3ATR3FHb3BSF2HBS3LOS3LOC3RLO3ATR3FHbS3FHbS3FHbS3LOS3LOC3RLO3RHI3ATR3FHbS3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3FHb2HBS3LOS3LOC3RLO3ATR4SPAB3FHa3FHbS3RLO3FHbS3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3LOS3LOC3RLO3ATR3FHbS3LOS3LOC3RLO3ATR4SPAB3FHa3FHb2HBS3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3FHbS3LOS3LOC3RLO3ATR4SPAB3FHa3FHb2HBS2NB2H62HK2BBFS3LOS3LOC3RLO3ATR3FHbS3RHI3FHbS3FHb2HBS3LOS3LOC3RLO3ATR3FHbS3LOS3LOC3RLO3ATR3FHbS3LOS3LOC3RLO3ATR3FHbS3RLO3FHbS3FHb2WFS3FHbS3FHbS3FHbS3LOS3LOC3RLO3ATR3FHb3BSF2HBS3FHbS3LOS3LOC3RLO3ATR3FHbS3FHbS3FHbS2R8S3FHbS3FHbS3FHbS3FHbS3FHbS2R8S3LOS3LOC3RLO3RHI3ATR3FHbS3FHbS3FHbS3FHbS3FHbS3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS2K0S2K1S2K2S3LOS3LOC3RLO3RHI3ATR3FHbS3FHbS3FHbS3FHbS3LOS3LOC3PAY3RLO2H62HK3ATR3FHb3FHc3GHc2BBS3RHI3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS2R8".
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
        apply (rw_cells_recast bsegs m1 R _ [CB 8 (le8 a); C8 b; CB 8 r2]) in H;
          [| cbn [cells_wf cell_wf]; rewrite ?length_le8; tauto | reflexivity | reflexivity] end.
      eapply ffsi_db. all: after_apply.
      all: intros _; rewrite unsigned_lit_wrap; change 18446744073709551615 with (2^64 - 1); rewrite ?zb_land_mask by lia;
           clear - HK H6 NB BB; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

    (* [comment removed for export] *)
    #[using="rc SP16 LOS LOC RSTK D N NB PAY R8 RLO RHI RGR RGRS FH RF RSF GH GF PL0 RU0 H6"] Lemma ffsi_fin1 : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 y21 y25 x28 x29 x30 x31 : word) mx
        (ja jb : list byte) (k nb ipz : Z),
      core mx -> stk bsegs mx lo SPAz -> rw_cells bsegs mx SPAz [CB 16 ja; C8 (Z_to_bv 64 R); C8 (Z_to_bv 64 FF); CB 16 jb; C8 (Z_to_bv 64 FF)] ->
      rw_cells bsegs mx (Z.shiftr FF 3 + 2147450880) ([f1c; f1c; f1c; f1c; z1c; z1c; z1c; z1c; z1c; z1c; f2c; f2c; f2c; f2c; f8c; f8c; f3c; f3c; f3c; f3c] ++ FSHZ) -> rw_cells bsegs mx FF FFHDR ->
      rw_cells bsegs mx (FF + 32) ZFHC ->
      rw_cells bsegs mx R [CB 8 r0; CB 8 r1; CB 8 r2] -> h <= k <= zlen bl -> 0 <= nb <= k -> ipz = S + k ->
      evtF bsegs RNG POST_J
        (MS (mkR x1 (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 nb) (Z_to_bv 64 S) y21 (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 ipz) (Z_to_bv 64 (FF + 112)) y25 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) x28 x29 x30 x31)
            FR (Z_to_bv 64 0x81c18) fc None mx (seg_rom bsegs)).
    Proof.
      intros until ipz. intros C STL FRA SHF FF0 ZFH RR HK HNB HIP. pose proof C as C'. openc C. Local Ltac2 Set LiaHints.tbl := fun () => "0080?15576793222.13319970786093.12138883115334.13343203500333.13453638430191.12058812639243.13267190198865.1346902457581.136 00000500S00X00]00b01I01N01SS3FHbS3LOS3LOC3RLO3ATR4SPAB3FHa3FHbS3FHbS3FHbS3FHbS3LOS3LOC3PAY3RLO2HK3HNB3FHb3FHc3GHc2BBS3FHbS3FHb".
prep2.
      zstep.                                      (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      zstep. if_cases KF; clear KF.               (* [comment removed for export] *)
      - eapply ffsi_fin2. all: after_apply.
      - zstep. zstep.                             (* [comment removed for export] *)
        eapply ffsi_fin2. all: after_apply.
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

    (* [comment removed for export] *)
    #[using="rc SP16 LOS LOC RSTK D N NB PAY R8 RLO RHI RGR RGRS FH RF RSF GH GF PL0 RU0 H6"] Lemma ffsi_finish : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 y25 x28 x29 x30 x31 : word) mx
        (ja jb : list byte) (k nb ipz rmz : Z),
      core mx -> stk bsegs mx lo SPAz -> rw_cells bsegs mx SPAz [CB 16 ja; C8 (Z_to_bv 64 R); C8 (Z_to_bv 64 FF); CB 16 jb; C8 (Z_to_bv 64 FF)] ->
      rw_cells bsegs mx (Z.shiftr FF 3 + 2147450880) ([f1c; f1c; f1c; f1c; z1c; z1c; z1c; z1c; z1c; z1c; f2c; f2c; f2c; f2c; f8c; f8c; f3c; f3c; f3c; f3c] ++ FSHZ) -> rw_cells bsegs mx FF FFHDR ->
      rw_cells bsegs mx (FF + 32) ZFHC ->
      rw_cells bsegs mx R [CB 8 r0; CB 8 r1; CB 8 r2] -> h <= k <= zlen bl -> 0 <= nb <= k -> ipz = S + k -> rmz = zlen bl - k ->
      evtF bsegs RNG POST_J
        (MS (mkR x1 (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 nb) (Z_to_bv 64 S) (Z_to_bv 64 rmz) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 ipz) (Z_to_bv 64 (FF + 112)) y25 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) x28 x29 x30 x31)
            FR (Z_to_bv 64 0x81bc0) fc None mx (seg_rom bsegs)).
    Proof.
      intros until rmz. intros C STL FRA SHF FF0 ZFH RR HK HNB -> ->. pose proof C as C'. openc C. Local Ltac2 Set LiaHints.tbl := fun () => "00`0?10990985245.14713156038281.13414031725080.1471532592227.146 15334474334.14818437397164.14719302942247.14719970786093.11821426538131.1472179254107.147 2211494699.134 22200344330.14728500580888.14729018245758.1473188101182.140 3188101183.136 3479438036.134 35670257402.13535905400123.13536350570402.7  38450959742.13943754901852.1365089449082.139 52567164907.14753031384365.14553638430191.11754302169230.2  5537889499.147 56500923902.13556683856941.7  57018326411.14057020423608.13657571462470.8  59308628304.1  59308628433.1  59314988138.14 59991009118.1446192067805.140 61934652264.14862845569605.14463370524077.1366386879048.7   65071494699.14165073591832.13765499904044.14068516218382.2  6900360422.144 9186259352.7   00000P00Q00j01301P02402@02^02k03O03P04104J04W05005I06906B07207707@07I07R07[07d07i07m08Q08Z08^08g09009109509909I09f09o0:80:A0:J0:O0:X0:a0:j0:n0;70;;S3LOS3LOC3RLO3ATR3FHb3BSF3DHb2HBFS3LOS3LOC3RLO3ATR3FHb3DHbS3FHb3DHbS3LOS3LOC3RLO3RHI3ATR3FHb3DHbS3LOS3LOC3RLO3ATR3FHb3FHc3GHc3DHb2HBS3FHb3DHb2HBS3LOS3LOC3RLO3ATR4SPAB3FHa3FHbS3RLO3FHb3DHbS3LOS3LOC3RLO3ATR3FHb3FHc3GHc3DHb2HBFS3LOS3LOC3RLO3ATR4SPAB3FHb3DHb2HBS3LOS3LOC3RLO3ATR3FHb3DHbS3RHI3FHb3DHbS3LOS3LOC3RLO3ATR3FHb3DHbS3LOS3LOC3RLO3ATR3FHb3DHbS3LOS3LOC3RLO2H62HK3HNB3FHb2DS2SN2NN3DHa3DHb3DHcS3FHb3DHbS3LOS3LOC3RLO2H62HK3ATR3FHb2DS2SN3DHa3DHb3DHc2K4S3HNBS3FHb3DHbS3FHb3DHbS3FHb3DHbS3FHb3DHbS3FHb3DHbS3FHbS2R8S3LOS3LOC3RLO3ATR3FHb3FHc3GHc3DHb2HBS3FHb3DHbS2K4S3FHb3DHbS3FHb3DHbSS2K1S2K2S2H62HK2DS3DHa1GS3LOS3LOC3RLO3RHI3ATR3FHb3DHbS3FHb3DHbS3FHb3DHbS3FHb3DHbS3FHb3DHbS3HNBS3FHb3DHbS3FHb3DHbS3FHb3DHbS2R8S3FHb3DHbS2HK".
prepF.
      zstep.                                      (* [comment removed for export] *)
      zstep. if_cases KC; clear KC.               (* [comment removed for export] *)
      - eapply ffsi_fin1. all: after_apply.
      - zstep.                                    (* [comment removed for export] *)
        zstep. bcase K4.                          (* [comment removed for export] *)
        + zstep.                                  (* [comment removed for export] *)
          zstep. zstep. guard_falseH HK K4 HNB BB H6 DS DHa.   (* [comment removed for export] *)
          eapply ffsi_fin1 with (k := k + 4). all: after_apply. all: clear - HK K4 HNB; lia.
        + (* [comment removed for export] *)
          unfold FSHZ in SHF. cbn [app] in SHF.
          zstep.                                  (* [comment removed for export] *)
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
      core mx /\ stk bsegs mx lo SPAz /\ rw_cells bsegs mx SPAz [CB 16 ja; C8 (Z_to_bv 64 R); C8 (Z_to_bv 64 FF); CB 16 jb; C8 (Z_to_bv 64 FF)] /\
      rw_cells bsegs mx (Z.shiftr FF 3 + 2147450880) FSH3 /\ rw_cells bsegs mx FF FFHDR /\
      rw_cells bsegs mx (FF + 32) ZFHC /\ rw_cells bsegs mx (FF + 112) [CB 4 w0; CB 4 w1; CB 4 w2] /\
      rw_cells bsegs mx R [CB 8 r0; CB 8 r1; CB 8 r2] /\
      h <= k <= zlen bl /\ 0 <= nb <= k /\ bv_unsigned rw <= 2^64 - 120 /\ ipz = S + k /\ rmz = zlen bl - k.
    Definition head_st (mx : amem) (k : Z) (rw : word) (nb ipz rmz : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 : word) : machine_state :=
      (MS (mkR x1 (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) rw x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 nb) (Z_to_bv 64 S) (Z_to_bv 64 rmz) (Z_to_bv 64 (FF + 32)) x23 (Z_to_bv 64 (FF + 112)) (Z_to_bv 64 ipz) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) x28 x29 x30 x31)
            FR (Z_to_bv 64 0x81ae0) fc None mx (seg_rom bsegs)).

    (* [comment removed for export] *)
    #[using="rc SP16 LOS LOC RSTK RI D N PLR NB PAY R8 RLO RHI RGR RGRS FH F256 RF RSF GH GF PL0 UNP0 RU0 H6"] Lemma ffsi_step : forall mx k rw nb ipz rmz ja jb w0 w1 w2 (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 : word),
      hinv mx k rw nb ipz rmz ja jb w0 w1 w2 ->
      (forall mx2 k2 rw2 nb2 ipz2 rmz2 jb2 v0 v1 v2 (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
         hinv mx2 k2 rw2 nb2 ipz2 rmz2 ja jb2 v0 v1 v2 -> k + 3 <= k2 ->
         evtF bsegs RNG POST_J
           (MS (mkR (Z_to_bv 64 0x81b2c) (Z_to_bv 64 SPAz) gp tp y5 y6 y7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) rw2 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 2147450880) (Z_to_bv 64 nb2) (Z_to_bv 64 S) (Z_to_bv 64 rmz2) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 ipz2) (Z_to_bv 64 (FF + 112)) (Z_to_bv 64 ipz2) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) y28 y29 y30 y31)
            FR (Z_to_bv 64 0x81ae0) fc None mx2 (seg_rom bsegs))) ->
      evtF bsegs RNG POST_J (head_st mx k rw nb ipz rmz x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31).
    Proof.
      intros until x31. intros HI CONT. unfold head_st.
      destruct HI as (C & STL & FRA & SHF & FF0 & ZFH & BP & RR & HK & HNB & RWB & -> & ->). pose proof C as C'. openc C. Local Ltac2 Set LiaHints.tbl := fun () => "01Y0?10841825258.14911750063593.14912357356857.14812357356857.15012428150072.15813210268013.15914038803757.11 14038805170.13 14113831303.10 15256690168.14117317695515.14819970786093.12420133607273.2  20303812366.14820303812366.15020749162842.14820749162842.15021209971458.14123891548451.15825076071819.15725076071819.15825076071819.15925236826157.15225261068994.10 25261071709.12 26813424995.14227478534713.15827736797930.14827736797930.15028040491972.16029696349971.8  32716563636.17 33897463481.14833897463481.15034763826958.14834763826958.1503479450872.141 3488604889.150 36393902218.14136401657515.15036742878330.14937871915530.11 39178121190.14839178121190.15039819800638.14441805334855.15842086935187.11 42609501300.2  42782745529.14942968992041.14842968992041.15044471906526.1494466284721.144 45982589382.14946160081097.10 46160081097.11 46160084822.12 47085352612.14947436455302.15147946365538.14948690461896.14948690461899.14748795416982.15448947615290.12 49441733640.12 49943447116.14950629934895.16050802402711.14 51627303145.14952567164907.14852567164907.14952567164907.15053322291235.15853557778676.14853557778676.15053638430191.12354902296849.10 54902300302.12 56170384339.14456644364524.14856644364524.15057622410744.15959314988138.11 59314988138.17 61149760928.14461598307493.14162098338330.14862098338330.15062824932752.14463403938114.1596386823154.148 6386823154.150 6386891876.10  64180194694.14467334405174.13 67336552099.11 6801153045.144 7139856330.149 8086067755.12  8374517865.149 8803078713.148 8803078713.150 8931455131.142 8968528094.149 8984541093.2   00000A01E02I03M03N04804=04B04K04L04Y05705=05N05_06006A06B06h07R08<09E09R09Z09b0:V0;@0;a0<B0<C0<H0<^0=b0>f0?70?H0@<0A00AA0AR0B30B80BE0BR0C40C50CC0CI0Cj0DK0Dl0E=0EJ0EW0E\0Ea0Ef0FL0FY0G]0Gj0H70HD0HH0HQ0H^0H_0Hg0Ik0J80JE0JR0K80K^0LD0LI0LQ0LY0Lk0M80ME0MT0Md0N80NI0NJ0N[0Nl0OF0P00Q40R80RA0RN0R\0Rg0S40SE0SN0TR0UV0VZ0WR0Wc0WdS3FHb3BSF3DHb3RW0S3LOS3LOC3RLO2GF2H62HK3ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHu3RW02KXS3LOS3LOC3RLO2GF2H62HK3ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHu3RW02KXS3LOS3LOC3RLO2GF2H62HK3ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHu3RW02KXFS3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHb3RW0S3RW0S3RW0S3HNB3RW0FS3FHb3DHb3RW0S3LOS3LOC3RLO3ATR4SPAB3FHa3FHbS4F256S3FHb3BSF3DHb3RW0S3FHb3BSF3DHb3RW0S3FHb3BSF3DHb3RW0S3FHb3BSF3DHb3RW0FS3LOS3LOC3RLO3ATR4SPAB3FHa3FHb3DHb3RW0S3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHb3RW0S3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHb3RW0S3LOS3LOC3RLO2GF2H62HK3ATR4SPAB3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHu3RW02KXS3FHb3DHb3RW0S3RW02KXS3RW02KXS3LOS3LOC3RLO2H62HK3ATR3FHb2DS2SN3DHa3DHb3DHc3RW02KXS3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHb3RW0S3LOS3LOC3RLO3ATR3FHb3BSF3DHb3RW0S3LOS3LOC3RLO3ATR3FHb3BSF3DHb3RW0FS3RW0S2H62HK2DS2SN4SEPF3RW0S3LOS3LOC3RLO2GF2H62HK3ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHu3RW02KXS3LOS3LOC3RLO2GF2H62HK3ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHu3RW02KXS3FHb3BSF3DHb3RW0S3FHb3BSF3DHb3RW0S3LOS3LOC3RLO2H62HK3HNB3FHb2DS2SN2NN3DHa3DHb3DHc3RW0S3LOS3LOC3RLO2H62HK3HNB3FHb2DS2SN2NN3DHa3DHb3DHc3RW0S3RWB3FHb3DHb3RW0S3RWB3FHb3DHb3RW0S3LOS3LOC3RLO3ATR3FHb3BSF3DHb3RW0S3RW0S3FHb3DHb3RW0S3FHb3DHb3RW0S3LOS3LOC3RLO3ATR4SPAB3FHb3DHb3RW0FS2H62HK3RW02KXS4F256S3LOS3LOC3RLO3ATR3FHb3BSF3DHb3RW0S3LOS3LOC3RLO3ATR3FHb3BSF3DHb3RW0S3LOS3LOC3RLO3ATR3FHb3BSF3DHb3RW0S3FHb3BSF3DHb3RW0S3FHb3DHb3RW0S3FHb3DHb3RW0S3RW0S3RW0S3RW0S3LOS3LOC3RLO3ATR4SPAB3FHb3BSF3DHb3RW0S3FHb3DHb3RW0S3LOS3LOC3RLO2GF2H62HK3ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHu3RW02KXS3FHb3DHb3RW0S3FHb3DHb3RW0S3FHb3DHb3RW0S2KES3HNB3RW0S3FHb3DHb3RW0FS2SN3RW0S3LOS3LOC3RLO2GF2H62HK3ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHu3RW02KXS3FHb3DHb3RW0S3FHb3DHb3RW0S3FHb3DHb3RW0S3LOS3LOC3RLO3ATR4SPAB3FHa3FHb3DHb3RW0S3LOS3LOC3RLO3ATR4SPAB3FHb3BSF3DHb3RW0S3LOS3LOC3RLO3ATR4SPAB3FHb3BSF3DHb3RW0S3FHbS2HK3RW0S2HK3RW0S4SPAB3FHb3DHb3RW0S3FHb3DHb3RW0S3FHb3DHb3RW0S3FHb3DHb3RW01HS2H62HK2DS3DHa1GS3RW01G2H62HK2DS3DHaS3FHa3FHb3DHb3RW0FS3FHb3BSF3DHb3RW0S3FHb3BSF3DHb3RW0S3RLO3RHI4SPAB3FHb3DHb3RW0S3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHb3RW0S3LOS3LOC3RLO2GF2H62HK3ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHu3RW02KXS3LOS3LOC3RLO2GF2H62HK3ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHu3RW02KXS3HNB3RW0S3FHb3DHb3RW0S2H62HK2DS3RW0S2H62HK3RW0S3FHb3DHb3RW0S3FHb3BSF3DHb3RW0S3HNB3RW0S3LOS3LOC3RLO2GF2H62HK3ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHu3RW02KXS3LOS3LOC3RLO2GF2H62HK3ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHu3RW02KXS3LOS3LOC3RLO2GF2H62HK3ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHu3RW02KXS3LOS3LOC3RLO2H62HK3HNB3ATR3FHb2DS2SN3DHa3DHb3DHc3RW02KXS3FHb3BSF3DHb3RW0S".
prepF.
      pose proof (bv_unsigned_in_range 64 rw) as RW0. unfold bv_modulus in RW0.
      unfold FSH3, FSHZ in SHF. cbn [app] in SHF.
      zstep.                                      (* [comment removed for export] *)
      zstep. bcase KX.                            (* [comment removed for export] *)
      { zstep.                                    (* [comment removed for export] *)
        eapply ffsi_exitE. all: after_apply.
        all: rewrite ?unsigned_lit_wrap; first [vm_compute; discriminate | clear - HK; lia]. }
      zstep.                                      (* [comment removed for export] *)
      zstep. guard_falseH HK KX RWB HNB RW0 BB H6 DS DHa.   (* [comment removed for export] *)
      zstep. guard_falseH HK H6 DS DHa BB.        (* [comment removed for export] *)
      zstep. guard_falseH HK KX RWB HNB RW0 BB H6 DS DHa.   (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      zstep. neglit (-8).                         (* [comment removed for export] *)
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
        lazymatch goal with SHx : rw_cells bsegs mc (Z.shiftr FF 3 + 2147450880) _, MUx : munch _ m mc, BPx : rw_cells bsegs mc (FF + 112) _ |- _ =>
        pose proof (bytes_at_transport bsegs _ m mc _ _ PL0 MUx f2_djpl) as PLx;
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
        | post_call bsegs mc ] end end.
      clear CB.

      zstep.                                      (* [comment removed for export] *)
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
    #[using="rc SP16 LOS LOC RSTK RI D N PLR NB PAY R8 RLO RHI RGR RGRS FH F256 RF RSF GH GF PL0 UNP0 RU0 H6"] Lemma ffsi_loop : forall (f : nat) mx k rw nb ipz rmz ja jb w0 w1 w2 (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 : word),
      zlen bl - k <= Z.of_nat f ->
      hinv mx k rw nb ipz rmz ja jb w0 w1 w2 ->
      evtF bsegs RNG POST_J (head_st mx k rw nb ipz rmz x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31).
    Proof.
      induction f as [|f IH]; intros until x31; intros FUEL HI.
      - eapply ffsi_step; [exact HI|]. intros until y31. intros HI2 HK2. exfalso.
        destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & HK & _). destruct HI2 as (_ & _ & _ & _ & _ & _ & _ & _ & HK' & _). cbn in FUEL. Local Ltac2 Set LiaHints.tbl := fun () => "0020?48306565083.12359314873579.12100000A00RS2H64FUEL3HK'3HK2S2H64FUEL3HK'3HK2".
lia.
      - eapply ffsi_step; [exact HI|]. intros until y31. intros HI2 HK2. unfold head_st in IH. eapply IH; [| exact HI2].
        destruct HI2 as (_ & _ & _ & _ & _ & _ & _ & _ & HK' & _). lia.
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

    (* [comment removed for export] *)
    #[using="rc SP16 LOS LOC RSTK RI D N PLR NB PAY R8 RLO RHI RGR RGRS FH F256 RF RSF GH GF PL0 UNP0 RU0 H6 H18"] Lemma ffsi_okpath : forall (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) mx (j48 : list byte) (w0 w1 w2 : list byte),
      core mx -> stk bsegs mx lo SPAz -> rw_cells bsegs mx SPAz [CB 48 j48; C8 (Z_to_bv 64 FF)] ->
      rw_cells bsegs mx (Z.shiftr FF 3 + 2147450880) ([f1c; f1c; f1c; f1c; z1c; z1c; z1c; z1c; z1c; z1c; f2c; f2c; f2c; f2c; f8c; f8c; f3c; f3c; f3c; f3c] ++ FSHZ) -> rw_cells bsegs mx FF FFHDR ->
      rw_cells bsegs mx (FF + 32) ZFHC -> rw_cells bsegs mx (FF + 112) [CB 4 w0; CB 4 w1; CB 4 w2] ->
      rw_cells bsegs mx R [CB 8 r0; CB 8 r1; CB 8 r2] ->
      evtF bsegs RNG POST_J
        (MS (mkR (Z_to_bv 64 0x81920) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 S) (Z_to_bv 64 (zlen bl)) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 R) e8 e9 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) x28 x29 x30 x31)
            FR (Z_to_bv 64 0x81a8c) fc None mx (seg_rom bsegs)).
    Proof.
      intros until w2. intros C STL FRA SHF FF0 ZFH BP RR. pose proof C as C'. openc C. Local Ltac2 Set LiaHints.tbl := fun () => "01b0?10375833354.14110751062487.3  10841825258.13811750063593.13812311023065.14012357356857.13912428150072.14713210268013.14815867410649.14015981451125.8  16083456450.14116598268889.14116670090264.8  17317695515.13719007305966.1401931560046.141 19970786093.11520003768591.6  20133607273.2  20303812366.13920749162842.13921529912041.6  23814431342.14123891548451.14725076071819.14625076071819.14725076071819.14825314235672.13125890530323.13225901595297.1422595860444.2   26128783840.6  27434788809.13827478534713.14727612731733.8  27736797930.13928040491972.14928244409929.14031407316583.8  32284519535.14032480504884.6  32480652977.8  33680001082.14033897463481.13934763826958.13936742878330.13837326182295.14037341542897.9  37388626009.14038119484249.14138297424623.14139178121190.13939418096022.14339819800638.13341805334855.14742609501300.2  42760314647.14142782745529.13842968992041.13943293708626.14144471906526.1384466284721.133 44804625134.14045982589382.13846187586605.13947085352612.13847946365538.13848690461896.13849795985777.8  49943447116.13850592957754.14150629934895.14951627303145.13852567164907.13852567164907.13952567164907.14052567164907.14153322291235.14753510313882.14153557778676.13953582707338.14053638430191.1145595802578.12  56078305746.14056170384339.133563227834.141  56644364524.13957000377357.8  57622410744.14857701858490.4  58395571798.13159314988138.10 61149760928.13361262187731.13161934652264.13962098338330.13962824932752.13363403938114.1486386823154.139 64180194694.13364295209550.14164301028607.1326548478672.8   6755966729.8   67710724553.1416801153045.133 6900360422.140 7139856330.138 8374517865.138 8803078713.139 8968528094.138 8984541093.2   9294175833.141 9692294724.8   00000N00R00_01Y02?03903:03`04F04M04Y05?05G05P05n06L06j06n07407A07N07R08008R09809^0:e0:f0;P0<:0<>0<?0<H0<n0=90=V0=W0=e0>00><0>=0>>0>J0?D0?Q0?n0@P0@T0A:0A`0Al0B50B>0B\0B]0Bc0CE0Cb0D?0De0E20E;0EY0Eb0Ek0FM0GG0GP0G[0Gd0H40H50Ho0I80IA0IJ0IS0J50J>0J`0K>0KC0KR0L80LF0LR0L[0L_0Lj0M20M30M90MF0MG0MP0M]0N30NY0OS0O\0PB0Ph0Pl0Pm0Q;0QD0QM0QZ0RT0SN0S[0S\0TB0TJS3LOS3LOC3RLO3ATR4SPAB3FHb3DHbS2H6S3FHb3BSF3DHbS3LOS3LOC3RLO2GF2H63ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHuS3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHbS3LOS3LOC3RLO2GF2H63ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHuFS3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHbS2H62DSS2NB3FHb3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHbS2DS3DHaS3FHb3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3DHbS3LOS3LOC3RLO3ATR4SPAB3FHa3FHbS2H6S4F256S3FHb3BSF3DHbS3FHb3BSF3DHbS2H6S3LOS3LOC3RLO3ATR4SPAB3FHb3DHbS3LOS3LOC3RLO3ATR4SPAB3FHa3FHb3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHbS3LOS3LOC3RLO2GF2H63ATR4SPAB3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHu3FHc3GHcFS3LOS3LOC3RLO2H63ATR3FHb2DS2SN3DHa3DHb3DHcS3LOS3LOC3RLO2H63ATR3FHb2DS2SN3DHa3DHb3DHcS2KESS3FHb3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHbS2H62DS3DHaS3LOS3LOC3RLO3ATR3FHb3BSF3DHbFS4SPAB3FHb3DHbS2H62DS3DHaS3FHb3DHb2HBSSS3FHb3DHb2HBS3LOS3LOC3RLO2GF2H63ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHuS3FHb3BSF3DHbS3LOS3LOC3RLO3ATR3FHb3BSF3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3BSF3DHbS2SNS3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHbS3FHb3DHb2HBS3FHb3DHbS3FHb3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3DHbFS4F256S3LOS3LOC3RLO3ATR4SPAB3FHb3BSF3DHbS3LOS3LOC3RLO3ATR3FHb3BSF3DHbS3LOS3LOC3RLO3ATR3FHb3BSF3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHbS3FHb3BSF3DHbS3FHb3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3DHbS3FHb3DHbS3FHb3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3BSF3DHbS3LOS3LOC3RLO2GF2H63ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHuS3FHb3DHbS2H62DS3DHaS3FHb3DHbS2H63H183FHb3DHbFS3LOS3LOC3RLO2GF2H63ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHuS3FHb3DHbS3FHb3DHbS3FHb3DHbS3FHb3DHbS3LOS3LOC3RLO3ATR4SPAB3FHa3FHb3DHbS3FHb3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3BSF3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3DHbS3FHbS2H62DS2SN4SEPFS3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHbS4SPAB3FHb3DHbS3FHb3DHb2HBS3FHb3DHbS2H6S3FHb3DHb1HS2H63H18FS2H61GS3FHa3FHb3DHbFS3FHb3DHbS3FHb3BSF3DHbS3RLO3RHI4SPAB3FHb3DHbS3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHbS3LOS3LOC3RLO2GF2H63ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHuS3FHb3DHbS3LOS3LOC3RLO2H63ATR3FHb2BB2SN3DHb3DHcS3LOS3LOC3RLO2H63ATR3FHb2BB2SN3DHb3DHcS2H6SS4SPAB3FHb3DHbS3FHb3DHbS3FHb3DHbS3FHb3BSF3DHbS3LOS3LOC3RLO2GF2H63ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHuS3LOS3LOC3RLO2GF2H63ATR3FHb3FHu3GHu3BSF2DS2SN4SEPF3DHb3DHuS3FHb3BSF3DHbSS3LOS3LOC3RLO3ATR4SPAB3FHb3FHc3GHc3DHbS2DS3DHa".
prepF. unfold FSHZ in SHF. cbn [app] in SHF.
      zstep. zstep.                               (* [comment removed for export] *)
      zstep. rewrite (zx32_smallA h) by (clear - H6 H18; lia).   (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      zstep. guard_falseH H6 H18 BB DS DHa.       (* [comment removed for export] *)
      zstep. zstep. zstep.                        (* [comment removed for export] *)
      (* [comment removed for export] *)
      try (replace (h + S <? 1) with false by (symmetry; apply Z.ltb_ge; clear - H6 BB DS DHa; lia));
      try (replace (S + h <? 1) with false by (symmetry; apply Z.ltb_ge; clear - H6 BB DS DHa; lia));
      try (replace (S <? 1) with false by (symmetry; apply Z.ltb_ge; clear - H6 BB DS DHa; lia));
      try (replace (0 <? S) with true by (symmetry; apply Z.ltb_lt; clear - H6 BB DS DHa; lia));
      try (replace (0 <? h + S) with true by (symmetry; apply Z.ltb_lt; clear - H6 BB DS DHa; lia));
      cbn [Z.b2z negb xorb]. try change (Z.lxor 1 0) with 1. try change (Z.lxor 0 1) with 1.
      zstep. guard_falseH H6 H18 BB DS DHa.       (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      zstep. zstep.                               (* [comment removed for export] *)
      zstep. zstep. zstep.                        (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      pose proof cbsA as CB. unfold cbsA_stmt in CB.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
        lazymatch goal with SHx : rw_cells bsegs mc (Z.shiftr FF 3 + 2147450880) _, MUx : munch _ m mc, BPx : rw_cells bsegs mc (FF + 112) _ |- _ =>
        pose proof (bytes_at_transport bsegs _ m mc _ _ PL0 MUx f2_djpl) as PLx;
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
        | post_call bsegs mc ] end end.
      clear CB.

      zstep.                                      (* [comment removed for export] *)
      zstep. bcase KE.                            (* [comment removed for export] *)
      { eapply ffsi_exitE. all: after_apply.
        all: zfin KE. }
      zstep.                                      (* [comment removed for export] *)
      eapply (ffsi_loop (Z.to_nat (zlen bl)) _ h); [clear - H6; lia|].
      unfold hinv. repeat match goal with |- _ /\ _ => split end. all: after_apply.
      all: zfin H6 H18 KE BB.
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  End Frame.

  (* [comment removed for export] *)
  #[using="rc SP16 LOS LOC RSTK RI D N PLR NB PAY R8 RLO RHI RGR RGRS FH F256 RF RSF GH GF PL0 UNP0 RU0"] Lemma ffsi_gret : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (r : Z) (j48 j1 hb j2 r0 r1 r2 w0 w1 w2 : list byte),
    core m -> stk bsegs m lo SPAz -> rw_cells bsegs m SPAz [CB 48 j48; C8 (Z_to_bv 64 FF)] ->
    rw_cells bsegs m (Z.shiftr FF 3 + 2147450880) ([f1c; f1c; f1c; f1c; z1c; z1c; z1c; z1c; z1c; z1c; f2c; f2c; f2c; f2c; f8c; f8c; f3c; f3c; f3c; f3c] ++ FSHZ) -> rw_cells bsegs m FF FFHDR ->
    rw_cells bsegs m (FF + 32) [CB 24 j1; CB 4 hb; CB 20 j2] ->
    (r mod 2^64 = 0 -> exists h, hb = le4 (Z_to_bv 64 h) /\ 6 <= h <= zlen bl /\ h <= 18) ->
    rw_cells bsegs m (FF + 112) [CB 4 w0; CB 4 w1; CB 4 w2] ->
    rw_cells bsegs m R [CB 8 r0; CB 8 r1; CB 8 r2] ->
    evtF bsegs RNG POST_J
      (MS (mkR (Z_to_bv 64 0x81920) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 S) (Z_to_bv 64 (zlen bl)) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 R) e8 e9 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) x28 x29 x30 x31)
            FR (ret_pc (Z_to_bv 64 0x81920)) fc None m (seg_rom bsegs)).
  Proof.
    intros until w2. intros C STL FRA SHF FF0 ZFH RF0 BP RR. pose proof C as C'. openc C. Local Ltac2 Set LiaHints.tbl := fun () => "0160?10990985245.13010990985245.13114031725080.13014031725080.1311532592226.129 1532592226.130 15334474333.13115334474333.13218437397164.13018437397164.13119302942247.13019302942247.13119970786093.11321426538131.13021426538131.1312179254107.130 2179254107.131 22200344330.13022200344330.13122407118464.11528500580888.13028500580888.13129010567573.11629010571016.11729018245758.13029018245758.1313188101182.122 3188101182.123 3188101183.118 3188101183.119 35497693828.11735497696281.11635670257402.11735670257402.11838450959742.12138450959742.12243754901852.11843754901852.11945432039387.13045432039387.1315089449082.121 5089449082.122 52567164907.13052567164907.13153638430191.11254302169230.2  5537889499.130 5537889499.131 56500923902.11756500923902.11857018326411.12257018326411.12357020423608.11857020423608.11959308628304.1  59308628433.1  59315053158.3  59991009117.12759991009117.1286192067805.122 6192067805.123 63370524077.11863370524077.11965071494699.12365071494699.12465073591832.11965073591832.12065499904044.12265499904044.12368516218382.2  00000L00h01=01R01W01\02502N02n03N03V03^04<04E04N04n05N06306T06Y06n07C07D07E07N07W07l08A08V08k09009509:09?09D09I09N09S0:30:S0:X0:]0:b0:g0:l0;00;P0<00<50<:0<?0<D0<I0<N0<R0<V0<\0=50=N0=S0=X0=]0=b0=g0=l0>10>60>;0>@0>DS3LOS3LOC3RLO3ATR3FHb3BSF2HBS3LOS3LOC3RLO3ATR3FHb3BSF2HBS3LOS3LOC3RLO3ATR3FHbS3LOS3LOC3RLO3ATR3FHbS3FHbS3FHbS3LOS3LOC3RLO3RHI3ATR3FHbS3LOS3LOC3RLO3RHI3ATR3FHbS3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3FHb2HBS3FHb2HBS3LOS3LOC3RLO3ATR4SPAB3FHa3FHbS3RLO3FHbS3RLO3FHbS3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3LOS3LOC3RLO3ATR4SPAB3FHa3FHb3GHa2HBS3LOS3LOC3RLO3ATR4SPAB3FHa3FHb2HBS3FHbS3LOS3LOC3RLO3ATR3FHbS3LOS3LOC3RLO3ATR3FHbFFS3RHI3FHbS3RHI3FHbS3LOS3LOC3RLO3ATR3FHbS3LOS3LOC3RLO3ATR3FHbS3LOS3LOC3RLO3ATR3FHbS3LOS3LOC3RLO3ATR3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3FHbS3FHbS3FHbS3FHbS3FHbS2R8S3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3LOS3LOC3RLO3ATR3FHb3FHc3GHc2HBS3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS2K1S2K2S2KE1CS3LOS3LOC3RLO3RHI3ATR3FHbS3LOS3LOC3RLO3RHI3ATR3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS2R8".
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
        apply (rw_cells_recast bsegs m1 (FF + 32) _ [CB 24 j1; C4 w; CB 20 j2]) in H;
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
  #[using="rc SP16 LOS LOC RSTK bl D R R8 RLO FH RF RSF GH GF RG"] Lemma ffsi_release : forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y23 y24 y25 y28 y29 y30 y31 : word) mx (cl : list cell),
    rw_cells bsegs mx (SP + -104) FFRB -> rw_cells bsegs mx (FF + 248) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs mx FLG [C1 (Z_to_bv 8 1)] ->
    stk bsegs mx (SPAz + 56) (SP + -104) -> stk bsegs mx lo SPAz -> rw_cells bsegs mx SPAz cl -> cells_size cl = 56%nat ->
    rw_cells bsegs mx (Z.shiftr FF 3 + 2147450880) FSH1 -> mem_inv bsegs mx ->
    evtF bsegs RNG (fun ms' => exists mp m',
        ms' = MS (mkR ra (Z_to_bv 64 SP) gp tp y5 y6 y7 s0 s1 (Z_to_bv 64 FLG) y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                 FR (ret_pc ra) fc None m' (seg_rom bsegs)
        /\ munch [(Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 32)] mx mp /\ wmono bsegs mx mp /\ mem_inv bsegs mp
        /\ munch [(FLG, FLG + 1)] mp m' /\ wmono bsegs mp m' /\ mem_inv bsegs m'
        /\ stk bsegs m' lo SP /\ rw_cells bsegs m' FLG [C1 (Z_to_bv 8 0)])
      (MS (mkR y1 (Z_to_bv 64 SPAz) gp tp y5 y6 y7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) y20 y21 y22 y23 y24 y25 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) y28 y29 y30 y31)
            FR (Z_to_bv 64 0x819c0) fc None mx (seg_rom bsegs)).
  Proof.
    intros until cl. intros FRB FF248 FLC STG STL FRA CL SHF MI.
    pose proof atop_range as ATR. unfold KEND in SPT. unfold AFI_STACK in LOS.
    pose proof (proj1 (spa160_propsA SP SP16)) as SPAB.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa. pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
    pose proof (ablk_lin _ _ GH) as (GHa & GHb & GHc & GHd). unfold AIMG_HI in GHa. pose proof GH as GHu. unfold ablk, AIMG_HI, KLS in GHu.
    pose proof RSF as RSF'. Local Ltac2 Set LiaHints.tbl := fun () => "05?0?1018082058.116 10299541350.11610757196425.11610841825258.11611350655860.11611603250610.11611776021145.11611805467289.11411805467289.11511805467289.11612066655206.11512342077012.11612649602618.11612911143428.11613067081226.11513325022025.11613547350398.11613641502813.118136972401.119  13701124555.11513890391188.11613912086366.11614033283697.12014738355418.11614793220770.11614866570234.11614981645286.11615010729547.11415059373769.11615160347210.11515188852999.12115309128057.11615341314694.11615440269036.11615497861449.11615719060185.11616036404123.11416141167028.11616598268889.11616867429482.11517162010020.11617264948956.11917317695515.11517404902110.11617444521370.11617635619076.11618138708044.11618368439854.11618660396218.11618759279913.11619272833707.11319570126950.11620139715884.11620563474841.11620563939225.11620749162842.11620810893807.1132089572985.116 21139636686.1162139396638.116 21470349994.11521610876870.11621917429068.11622087971884.11622298171673.11622416474134.11422544861286.11622700267513.11522775997707.11522843528825.11622895698612.11623098415148.11623223569694.11623404677272.1202342125148.119 23499613609.11623584418860.11423637580569.11623716884570.1162408208171.115 24085599115.11524516908640.11624521592556.11524686014778.11624801268105.11625082048475.1152509489337.116 25117449465.1162521080681.116 25653217698.12025862343643.12026048924876.11626348902346.11626416457748.11626669182065.12026671158508.1162673550442.116 26739224554.11626774769626.11527045444308.11627058951505.12227334627497.11627622887044.11628244409929.11628322672363.11528339690859.11528490377204.11628516984212.11428897571974.11528987856538.11529139002340.11629181457478.11629192875980.11629789957596.11930013766257.12030032268340.11630151347498.11630185424027.12030561560395.11530906104780.1163145208153.116 31518365030.1163199430677.116 32087020145.12132130763846.11632365281766.11432376603722.11632966260985.1163323235066.116 33680001082.11633864347846.11633897463481.11633965537418.11633969101564.12034067874939.11534098841190.116341926779.114  34490278001.11934782976605.11835235452859.12035301401292.11635381703419.11535894910345.11636172772266.1163619125578.116 36473820158.11636550167516.11936685953222.11537066468830.11637349358057.11537388626009.11637545354041.11537566535918.11637813484969.11637906871084.11638350898988.11638389508810.11638709023052.11538889460260.11538932229498.1163913742100.116 39178121190.11639419589006.11639640754315.11540058685594.11640093537476.11640324494905.11540401672937.11640456106473.11640811138462.11641044649514.11641055142510.11641091132398.11641377675910.11641615107788.11641947725147.11542200342570.11642452747910.11642782745529.11642831019478.11642919482676.11642968992041.11643054286892.11643146938811.11543641966310.11943833837156.11643872227804.11944229320300.11644417097546.11644456543803.11545003960668.11945221239098.11645342999668.1154537091657.116 45508725130.11645585588076.116456469350.116  45740938393.11545881473900.11645982589382.1164606400646.116 46080113946.1164641771485.118 46525677412.11646787521756.11946924073390.11646949129329.12047085352612.11647646465612.11647784655834.11648046123689.12048211285674.1164831013226.116 4861306889.114 48650452329.11648690461899.11549164012678.11649656697097.11649763279678.11649943447116.11650018932218.11650070184004.11650524051526.11651046823195.11551766063161.11651781592412.11951816630506.11652048616164.11652107682714.11652196777467.11552366239022.1165253856742.116 52631624166.11652973911979.11553018266553.11653036558889.11653472464966.11653541803018.11653557778676.11653638430191.10353706860006.11654068232029.11854077074143.12054226150513.12054256297073.11954279058475.11554374972478.11655142594814.11355190259372.11355846471854.11656027773562.116563227834.116  5634116633.114 56376734585.11656482153492.1205649771342.116 56644364524.11656804907040.11656830590924.11657089830186.11657466002425.11657496662641.12057533215052.11557871968190.11657919919806.11658116526106.11658143722584.12058226117964.11659118738686.1165927369227.115 59338331354.11659444586470.11659705885297.11959849706346.11659982339899.11560135071334.11660211452398.11660321776441.11661081885454.11661849248249.11661986099753.11662052811755.11562055344378.11662098338330.11662154059789.11662596255172.11662598956670.11562619446612.11662632894729.11662719221382.11663362316395.11563392461657.11663700058990.11563726620298.11663958622316.11664026414714.11464322305738.11664562105998.11664696793412.11564993435597.12065110321578.11665312824268.11665678933017.11665707003017.11666111488204.11666183421017.11666948228265.11567114676681.11567358824282.11667382833310.11667520808170.11667709824076.11667710724553.11667810302577.12067912497307.11568066155898.1146924395529.116 6961534555.115 6968827998.115 7039361418.116 7139856330.116 7309853801.116 7342793742.114 7555993734.116 763619204.116  8267992283.115 8374517865.116 8710768218.116 8747329497.116 8905668329.116 8955631908.116 9130008270.116 9415653658.116 9417716923.115 9899865354.116 00000<00D00n01:01[01c02M02U02]02e02m03N03Z04;04G05105[05g05o06706X07B07J07V08@08L08T08\09F09R09Z0:D0:L0:T0;00;L0;T0<50<_0<k0=L0=X0=`0>J0>V0?70??0?i0@50@_0@g0@o0A70AS0B=0BI0BQ0Bm0CW0DA0DM0DU0D]0De0EO0E[0Ec0Em0F50F_0G@0GH0H20H>0HJ0I40I<0IX0Id0Il0J40JU0J]0Ji0KE0KM0Ki0LS0Lo0M70M?0MG0MS0N40N<0ND0NP0N\0Nh0OI0OQ0P;0P\0Q80Q@0QH0Qi0RJ0RR0R^0S?0SG0SO0S[0Sc0TD0TP0U90UA0UI0Ue0Um0VI0VQ0VY0Va0Vm0WI0WU0Wa0Wi0XS0X_0YI0YQ0YY0Ya0Yi0Z50ZA0ZI0ZQ0[;0[G0[S0\=0\I0\Q0];0]e0^O0^k0_U0`10`90`A0`M0`U0a60aB0ac0ak0bU0b]0bi0cJ0d40dP0dl0eV0eb0fL0fX0f`0fh0g00g<0gD0g`0gl0hM0hi0i10i90iA0ib0in0j60jB0jJ0jV0jb0kC0km0l90lA0lI0le0lm0m50m=0mI0mU0n60nB0nl0o40oU0o]0oi10110=10I10e11O11W11_12I13313;13G13h14014814T14`14l15M15Y15a16K16S16[16c17M18718?18K18l19419<19H19T19\19d19l1:V1;;1;`1<J1<V1<b1=L1=h1>L1?61?>1?F1?N1?Z1@61@>1@F1A01AZ1Af1B11B91Bc1Bk1C71C?1CG1CS1C[1Cc1DM1E71Ea1FK1Fg1Fo1G;1GG1H11HR1I<1I]1J91JA1JI1K31K]1Ki1L11L=1LI1M31MT1M\1Mh1N01NL1Nh1O01OL1Oh1PR1P^1QH1QT1Q\1R81R@1RH1RT1S>1SF1T01T<1TH1Td1UN1UV1V71V?1Vi1W51WQ1X;1X\1YF1YR1YZ1YfS2CL3FHb3BSFS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS2CL3FHbS2CL3FHbS2CL3FHbS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS2CL3FHbS2CL3FHbS2CL3FHbS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS2CL3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS2CL3FHbS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS2CL3FHbS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS2CL3FHbS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS2CL3FHbS2CL3FHbS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS2CL3FHbS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS2CL3FHbS2CL3FHbS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS2CL3FHbS2CL3FHbS2CL3FHb1HS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3GHaS3LOS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHb3BSFS2CL3FHbS2CL3FHbS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHbS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS2CL3FHbS2CL3FHbS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHbS2CL3FHbS2CL3FHb3BSFS2CL3FHb3BSFS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS2CL3FHbS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHbS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHbS2CL3FHbS3LOS2CL3FHbS2CL3FHbS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHa3FHb3FHc3GHcS2CL3FHbS2CL3FHbS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS2CL3FHbS2CL3FHbS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHb3BSFS2CL3FHb3BSFS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS2CL3FHbS2CL3FHbS2CL3FHbS3LOS2CL3FHbS2CL3FHb3GHdS2CL3FHbS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS2CL3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS2CL3FHbS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS2CL3FHbS2CL3FHb3BSFS2CL3FHbS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS2CL3FHbS2CL3FHbS2CL3FHbS2CL3FHb3BSFS2CL3FHbS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS2CL3FHbS2CL3FHbS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS2CL3FHbS2CL3FHbS2CL3FHb3BSFS2CL3FHbS3LOS2CL3FHbS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS2CL3FHbS2CL3FHbS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS2CL3FHbS2CL3FHbS2CL3FHb3BSFS3LOS2CL3FHbS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHbS2CL3FHb3BSFS2CL3FHbS2CL3FHb3BSFS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHbS2CL3FHbS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS2CL3FHbS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHb3BSFS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS2CL3FHbS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHbS2CL3FHbS3LOS2CL3FHbS3LOS2CL3FHbS2CL3FHbS2CL3FHbS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHa3FHb3GHaS3LOS3LOC3RLO2CL3ATR4SPAB3FHa3FHb3GHaS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS2CL3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHa3FHb3FHc3GHcS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS2CL3FHbS2CL3FHbS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS2GF2CL3FHbS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS2CL3FHb3BSFS2CL3FHbS2CL3FHbS2CL3FHb3BSFS2CL3FHbS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS2CL3FHb3BSFS2CL3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS2CL3FHbS2CL3FHb3BSFS2CL3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHbS2CL3FHb3BSFS2CL3FHbS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS2CL3FHbS3LOS3LOC3RLO2CL3ATR3FHb3BSFS2CL3FHbS2CL3FHbS2CL3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHbS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS2CL3FHbS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS3LOS3LOC3RLO2CL3ATR3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS3LOS3LOC3RLO2CL3ATR4SPAB3FHb3BSFS3LOS3LOC2R83RLO2GF2CL3ATR3FHb3FHu3GHu3BSFS2CL3FHb3BSFS2CL3FHbS2CL3FHb3BSF".
replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in RSF' by (unfold shad, ASHOFF; lia).
    pose proof f2_bsf as BSF. boxH SP16. boxH F256.
    assert (LO0 : 0 <= lo) by (destruct STL as [? _]; assumption).
    unfold FSH1, FSHZ in SHF. cbn [app] in SHF. unfold AF_fi_ffsi.FFRB in FRB.
    pose proof (munch_refl [(Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 32)] mx) as MU1. pose proof (wmono_refl bsegs mx) as WM1.
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
      lazymatch goal with MIx : mem_inv bsegs mp |- _ => pose proof MIx as MIp; boxH MIp end;
      pose proof (munch_refl [(FLG, FLG + 1)] mp) as MU2; pose proof (wmono_refl bsegs mp) as WM2 end.
    boxH MU1. boxH WM1.
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    do 13 zstep.                                  (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    (* [comment removed for export] *)
    eapply stk_release in FRA; [| exact STL| lia]. rewrite CL in FRA. change (Z.of_nat 56) with 56 in FRA.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mf _) =>
      pose proof (stk_merge bsegs mf lo (SPAz + 56) (SP + -104) FRA STG ltac:(lia)) as ST2 end.
    release_frame FRB ST2 SP.
    apply evtF_done. unfold bx in MU1, WM1, MIp.
    eexists _, _. split; [reflexivity|].
    split; [first [exact MU1| eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside]; intros; lia]|]. split; [exact WM1|]. split; [exact MIp|].
    split; [eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside]; intros; lia|]. split; [exact WM2|]. split; [eassumption|].
    split; [exact ST2| assumption].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End S.
End CANSEC1.
