(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import DrvAgree StrFun Stdio_pure.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg ABase RtCells AProto AMalloc_iface AHarness_iface AH_fi_iface AF_fi_kit AF_fi_chk AF_fi_shacc AF_fi_gfhaM.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.
Local Ltac acc_hint ::= shacc.      (* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variables (gp tp s11 : word) (F : bvmap 5 word) (fc : bv 32) (SP FF ZF S : Z) (bl : list Z) (mM : amem) (RNG : footprint).
  Notation n := (zlen bl).
  Notation shF := (Z.shiftr FF 3 + 2147450880).
  Notation SPA := ((SP - 128) - (SP - 128) mod 32).
  Notation W := [(ZF, ZF + 48)].
  Hypothesis PLR : Forall (fun c => 0 <= c < 256) bl.
  Hypothesis NB : n < 2^62.
  Hypothesis SB : 0 < S /\ S + n <= ATOP.
  Hypothesis ZA : ZF mod 8 = 0.
  Hypothesis ZB : AIMG_HI <= ZF /\ ZF + 48 <= ATOP /\ (ZF + 48 <= KLS \/ KHIGH <= ZF).
  Hypothesis SEPZ : S + n <= ZF \/ ZF + 48 <= S.
  Hypothesis USRC : unpoisoned mM S (S + n).
  Hypothesis UZF : unpoisoned mM ZF (ZF + 48).
  Hypothesis RS : rng RNG S n.
  Hypothesis RSS : rng RNG (Z.shiftr S 3 + 2147450880) (Z.shiftr (S + n - 1) 3 - Z.shiftr S 3 + 1).
  Hypothesis RZ : rng RNG ZF 48.
  Hypothesis RSZ : rng RNG (Z.shiftr ZF 3 + 2147450880) 6.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RIS : rng RNG 0x7fffa000 0xbcc00.

  (* [comment removed for export] *)
  #[using="rc bl ZA ZB UZF"] Lemma zsh0 : forall m1 a, munch W mM m1 -> ZF <= a < ZF + 48 ->
    ov_read_bytes asegs m1 (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) 1 = Some [Z_to_bv 8 0].
  Proof. intros m1 a MU Ha. eapply zfh_sh_zero; eassumption. Qed.
  #[using="rc SB ZB SEPZ USRC"] Lemma schk : forall m1 a, munch W mM m1 -> S <= a < S + n ->
    exists b, ov_read_bytes asegs m1 (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) 1 = Some [b]
              /\ (sval b = 0 \/ (0 < sval b <= 7 /\ a mod 8 < sval b)) /\ -128 <= sval b <= 127.
  Proof. intros m1 a MU Ha. eapply src_chk; eassumption. Qed.
  (* [comment removed for export] *)
  Ltac brr := first [if_true | if_false].
  (* [comment removed for export] *)
  Ltac zf_genericA :=
    lazymatch goal with
    | CZ : rw_cells _ ?m1 ZF ?cs |- _ =>
        let j := fresh "zj" in let C := fresh "CZ" in
        destruct (rw_cells_forget asegs m1 ZF cs CZ) as [j C]; clear CZ; cbn [cells_size csize Nat.add] in C;
        apply (rw_cells_split_CB asegs _ _ [] 48 j [] [24; 4; 20]%nat) in C; [| reflexivity]; cbn [app mk_CB_cells] in C
    end.
  Ltac exit_tailA :=
    zf_genericA; eapply xdone; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast;
    (let HR := fresh in intros HR; exfalso; first [vm_compute in HR; lia | rewrite Z.mod_small in HR by lia; lia]).
  (* [comment removed for export] *)
  Ltac zf_successA :=
    lazymatch goal with
    | CZ : rw_cells _ ?m1 ZF [?c0; ?c1; ?c2; ?c3; C4 ?h; ?c5; ?c6; ?c7; ?c8] |- _ =>
        eapply rw_cells_recast with (cs' := [CB 24 (cbytes c0 ++ cbytes c1 ++ cbytes c2 ++ cbytes c3); CB 4 (le4 h);
                                              CB 20 (cbytes c5 ++ cbytes c6 ++ cbytes c7 ++ cbytes c8)]) in CZ;
        [| cbn [cells_wf cell_wf cbytes]; rewrite ?length_app, ?length_le8, ?length_le4; repeat split; reflexivity
         | cbn [cells_bytes cbytes]; rewrite ?app_nil_r, <- ?app_assoc; reflexivity
         | reflexivity ]
    end;
    eapply xdone; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; intros _; eexists; split; [reflexivity| lia].
  (* [comment removed for export] *)
  Ltac pose_rdA k :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      lazymatch goal with
      | PL : bytes_at asegs m1 S (map (Z_to_bv 8) bl) |- _ =>
          let H := fresh "RD" in let R := fresh "RB" in
          pose proof (buf_readA m1 S bl k (conj PL PLR) ltac:(lia)) as H;
          pose proof (proj2 (buf_nthA m1 S bl k (conj PL PLR) ltac:(lia))) as R;
          try (replace (wa (S + 0)) with (wa S) in H by (unfold wa; f_equal; lia))
      end
    end.
  Ltac clear_rdA :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      repeat match goal with
             | H : ov_read_bytes _ ?m0 _ _ = Some _ |- _ => lazymatch m0 with m1 => fail | _ => clear H end
             | H : 0 <= Znth _ bl < 256 |- _ => clear H
             end
    end.
  Ltac pose_rdsA a b :=
    let t := eval vm_compute in (Z.ltb a b) in
    lazymatch t with
    | true => pose_rdA a; let a' := eval vm_compute in (a + 1) in pose_rdsA a' b
    | false => idtac
    end.
  (* [comment removed for export] *)
  Ltac pose_tabA k :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      lazymatch goal with MIx : mem_inv asegs m1 |- _ =>
        let A := eval vm_compute in (AFI_DIDTAB + 8 * k) in
        let H := fresh "TAB" in
        pose proof (fhtab_read_at m1 k A MIx ltac:(lia) ltac:(reflexivity)) as H;
        lazymatch type of H with _ = Some ?r => let r' := eval vm_compute in r in change r with r' in H end
      end
    end.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac clear_rds := repeat match goal with H : ov_read_bytes _ _ _ _ = Some _ |- _ => clear H end.
  Ltac clear_cks := repeat match goal with H : sval _ = 0 \/ _ |- _ => clear H | H : -128 <= sval _ <= 127 |- _ => clear H end.
  Ltac shload r :=
    clear_rds; clear_cks;
    let w := getreg r in
    lazymatch w with
    | Z_to_bv 64 (Z.shiftr ?a 3 + 2147450880) =>
        lazymatch goal with
        | |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
          lazymatch goal with
          | MU : munch _ mM m1 |- _ =>
              first [ let H := fresh "ZSH" in pose proof (zsh0 m1 a MU ltac:(lia)) as H
                    | let sb := fresh "sb" in let RD := fresh "RD" in let CK := fresh "CK" in let SR := fresh "SR" in
                      destruct (schk m1 a MU ltac:(lia)) as (sb & RD & CK & SR)
                    | fail 1 "shload: no shadow fact for" a ]
          end
        end
    | _ => fail "shload: register" r "holds" w
    end.
  (* [comment removed for export] *)
  Ltac zload := zstep; clear_rds; try rewrite sxb_sval; try change (sval (Z_to_bv 8 0)) with 0.
  (* [comment removed for export] *)
  Ltac pload r off :=
    clear_rds;
    let w := getreg r in
    lazymatch w with
    | Z_to_bv 64 ?a =>
        let i := lazymatch a with
                 | S => constr:(off%Z)
                 | S + ?p => let v := eval vm_compute in (p + off)%Z in v
                 | _ => fail "pload: register does not hold S + pos:" a
                 end in
        lazymatch goal with
        | |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
          lazymatch goal with
          | PL : bytes_at asegs m1 S (map (Z_to_bv 8) bl) |- _ =>
              let R := fresh "RB" in let H := fresh "RD" in
              pose proof (buf_readA m1 S bl i (conj PL PLR) ltac:(lia)) as H;
              pose proof (proj2 (buf_nthA m1 S bl i (conj PL PLR) ltac:(lia))) as R;
              try (replace (wa (S + 0)) with (wa S) in H by (unfold wa; f_equal; lia))
          end
        end
    end.
  Ltac pstep := zstep; clear_rds.
  (* [comment removed for export] *)
  Ltac gfact CK := let C := fresh in destruct CK as [C|C]; [left; exact C| right; lia].
  Ltac chk_branch lem :=
    eapply lem;
    [ match goal with CK : sval ?x = 0 \/ _ |- sval ?x = 0 \/ _ => gfact CK end
    | match goal with SR : -128 <= sval ?x <= 127 |- -128 <= sval ?x <= 127 => exact SR end
    | lia
    | assumption
    | intros ?; clear_cks ].
  (* [comment removed for export] *)
  Ltac gstepA Hd Hs Hf E64 :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch pc with
      | 524764 => first [ zf_successA | exit_tailA ]                                 (* [comment removed for export] *)
      | 525096 => shload 11; zload            (* [comment removed for export] *)
      | 525100 => chk_branch chkA_802dc          (* [comment removed for export] *)
      | 525116 => shload 13; zload            (* [comment removed for export] *)
      | 525120 => chk_branch chkA_802f0          (* [comment removed for export] *)
      | 525196 => shload 11; zload            (* [comment removed for export] *)
      | 525200 => chk_branch chkA_80340          (* [comment removed for export] *)
      | 525212 => zstep; rewrite Hd          (* [comment removed for export] *)
      | 525244 => zstep; rewrite Hf          (* [comment removed for export] *)
      | 525280 => zstep; rewrite Hs          (* [comment removed for export] *)
      | 525292 => clear_rds; zstep; rewrite E64; try change (Z.b2z true) with 1; try change (Z.b2z false) with 0   (* [comment removed for export] *)
      | 525300 => zstep; try change (Z.b2z (0 <? 32)) with 1; try change (Z.b2z (0 <? 0)) with 0        (* [comment removed for export] *)
      | 525328 => zstep; let K := fresh "KL" in if_cases K; zify_cond K                                 (* [comment removed for export] *)
      | 525352 => shload 12; zload            (* [comment removed for export] *)
      | 525364 => clear_rdA; zstep              (* [comment removed for export] *)
      | 525380 => shload 12; zload            (* [comment removed for export] *)
      | 525384 => chk_branch chkA_803f8          (* [comment removed for export] *)
      | 525388 => pload 11 0; pstep; cbv beta; lazymatch goal with RB : 0 <= Znth 4 bl < 256 |- _ => rewrite (byte_litA _ RB) end   (* [comment removed for export] *)
      | 525396 => zstep; let K := fresh "KR" in if_cases K; zify_cond K                                 (* [comment removed for export] *)
      | 525400 => zstep; rewrite Hs          (* [comment removed for export] *)
      | 525416 => shload 11; zload            (* [comment removed for export] *)
      | 525420 => chk_branch chkA_8041c          (* [comment removed for export] *)
      | 525424 => pload 10 0; pstep; cbv beta; lazymatch goal with RB : 0 <= Znth 5 bl < 256 |- _ => rewrite (byte_litA _ RB) end   (* [comment removed for export] *)
      | 525432 => zstep; let K := fresh "KW" in if_cases K; zify_cond K                                 (* [comment removed for export] *)
      | 525512 => shload 14; zload            (* [comment removed for export] *)
      | 525528 => shload 11; zload            (* [comment removed for export] *)
      | 525532 => chk_branch chkA_8048c          (* [comment removed for export] *)
      | 525536 => shload 13; zload            (* [comment removed for export] *)
      | 525540 => chk_branch chkA_80494          (* [comment removed for export] *)
      | 525556 => shload 11; zload            (* [comment removed for export] *)
      | 525632 => shload 12; zload            (* [comment removed for export] *)
      | 525660 => shload 10; zload            (* [comment removed for export] *)
      | 525664 => chk_branch chkA_80510          (* [comment removed for export] *)
      | 525680 => shload 11; zload            (* [comment removed for export] *)
      | 525684 => chk_branch chkA_80524          (* [comment removed for export] *)
      | 525696 => shload 10; zload            (* [comment removed for export] *)
      | 525788 => zstep; rewrite Hd          (* [comment removed for export] *)
      | 525816 => shload 12; zload            (* [comment removed for export] *)
      | 525820 => chk_branch chkA_805ac          (* [comment removed for export] *)
      | 525824 => pload 10 0; pstep            (* [comment removed for export] *)
      | 525856 => shload 12; zload            (* [comment removed for export] *)
      | 525860 => chk_branch chkA_805d4          (* [comment removed for export] *)
      | 525876 => shload 16; zload            (* [comment removed for export] *)
      | 525880 => chk_branch chkA_805e8          (* [comment removed for export] *)
      | 525884 => pload 10 1; pstep            (* [comment removed for export] *)
      | 525888 => pload 10 0; pstep            (* [comment removed for export] *)
      | 525928 => shload 12; zload            (* [comment removed for export] *)
      | 525932 => chk_branch chkA_8061c          (* [comment removed for export] *)
      | 525948 => shload 16; zload            (* [comment removed for export] *)
      | 525952 => chk_branch chkA_80630          (* [comment removed for export] *)
      | 525956 => pload 10 1; pstep            (* [comment removed for export] *)
      | 525960 => pload 10 0; pstep            (* [comment removed for export] *)
      | 525964 => pload 10 2; pstep            (* [comment removed for export] *)
      | 525968 => pload 10 3; pstep            (* [comment removed for export] *)
      | 526000 => zstep; rewrite Hf          (* [comment removed for export] *)
      | 526052 => shload 12; zload            (* [comment removed for export] *)
      | 526056 => chk_branch chkA_80698          (* [comment removed for export] *)
      | 526072 => shload 15; zload            (* [comment removed for export] *)
      | 526076 => chk_branch chkA_806ac          (* [comment removed for export] *)
      | 526080 => pload 10 1; pstep            (* [comment removed for export] *)
      | 526084 => pload 10 0; pstep            (* [comment removed for export] *)
      | 526088 => pload 10 2; pstep            (* [comment removed for export] *)
      | 526092 => pload 10 3; pstep            (* [comment removed for export] *)
      | 526140 => shload 12; zload            (* [comment removed for export] *)
      | 526144 => chk_branch chkA_806f0          (* [comment removed for export] *)
      | 526160 => shload 15; zload            (* [comment removed for export] *)
      | 526164 => chk_branch chkA_80704          (* [comment removed for export] *)
      | 526168 => pload 10 1; pstep            (* [comment removed for export] *)
      | 526172 => pload 10 0; pstep            (* [comment removed for export] *)
      | 526208 => shload 12; zload            (* [comment removed for export] *)
      | 526212 => chk_branch chkA_80734          (* [comment removed for export] *)
      | 526228 => shload 15; zload            (* [comment removed for export] *)
      | 526232 => chk_branch chkA_80748          (* [comment removed for export] *)
      | 526236 => pload 10 1; pstep            (* [comment removed for export] *)
      | 526240 => pload 10 2; pstep            (* [comment removed for export] *)
      | 526244 => pload 10 3; pstep            (* [comment removed for export] *)
      | 526248 => pload 10 0; pstep            (* [comment removed for export] *)
      | 526268 => pload 10 4; pstep            (* [comment removed for export] *)
      | 526272 => pload 10 5; pstep            (* [comment removed for export] *)
      | 526280 => pload 10 6; pstep            (* [comment removed for export] *)
      | 526284 => pload 10 7; pstep            (* [comment removed for export] *)
      | 526344 => shload 14; zload            (* [comment removed for export] *)
      | 526364 => shload 10; zload            (* [comment removed for export] *)
      | 526388 => shload 12; zload            (* [comment removed for export] *)
      | 526404 => zstep; let K := fresh "KB" in if_cases K; clear K                                      (* [comment removed for export] *)
      | 526424 => shload 12; zload            (* [comment removed for export] *)
      | 526448 => shload 11; zload            (* [comment removed for export] *)
      | 526472 => shload 10; zload            (* [comment removed for export] *)
      | 526512 => shload 12; zload            (* [comment removed for export] *)
      | 526516 => chk_branch chkA_80864          (* [comment removed for export] *)
      | 526520 => pload 10 0; pstep            (* [comment removed for export] *)
      | _ => zstep; try brr
      end
    | |- evtF _ _ _ (MS _ _ ?pc _ _ _ _) => fail 1 "gstepA: undecided branch at" pc
    end.

  (* [comment removed for export] *)
  #[using="rc PLR NB SB ZA ZB SEPZ USRC UZF RS RSS RZ RSZ RI RIS"] Lemma decB3b : dec_okB gp tp s11 F fc SP FF ZF S bl mM RNG 3 32.
  Proof.
    unfold dec_okB, decA_at. intros until x31. intros N5 Hd Hs CZ PL GS MU WM MI.
    pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
    assert (LENB : Z.of_nat (length (map (Z_to_bv 8) bl)) = n) by (rewrite length_map; reflexivity).
    pose proof atop_range as ATR. pose proof ZB as ZBu. unfold AIMG_HI, KLS, KHIGH in ZBu.
    pose proof (rw_cells_bound _ _ _ _ CZ) as ZFB. cbn [cells_size csize Nat.add] in ZFB.
    unfold GSC, GSHC in GS.
    unfold ZCELLS, zcellA in CZ.
    Local Ltac2 Set LiaHints.tbl := fun () => "06]0?10512988003.10010512988003.89 10512988003.91 10512988003.95 1077445090.95  1077445090.99  1077445091.89  1077445093.90  10796611846.87 10798709004.97 10798709005.92 10798709006.86 11820491458.90 12100317789.86 12270618323.92 12270618325.91 12270618326.10112270618326.97 12331426017.10012331426017.96 12331426018.90 12331426020.91 12712716313.60 13140303554.88 13140303554.89 13140303554.94 13140303554.99 13666555668.72 13704059072.73 13847912576.87 13854552992.76 14165005376.73 14763973915.95 14763973915.96 15041153337.76 15041153339.78 15043250697.74 15043250697.77 15043250697.79 15043866943.73 15534906496.85 15534906502.95 15534906502.99 15534906503.96 15640285071.66 15658255133.88 15658255133.89 15658255133.94 15658255133.99 15876876809.68 15877476798.67 16075574774.60 16800856201.70 16809028512.62 1703303920.87  1705401081.87  1705401081.90  1705401083.89  1705401083.94  1705401084.95  1705401084.99  1705401085.100 17077626520.73 17539694136.75 17540089481.76 18086011986.92 18086011988.91 18086011991.10118086011991.97 18511472777.10018511472777.72 18511472777.87 18511472777.88 18511472777.89 18511472777.91 18511472777.93 18511472777.94 18511472777.95 18511472777.98 18511472777.99 18591908039.77 18681669866.60 19010590676.88 19010590676.89 19010590676.94 19010590676.99 19302163537.77 19302163538.74 19302163551.79 19304258773.83 19589975962.87 19589975962.88 19589975962.93 19589975962.98 20700320864.63 222951252.88   222951252.89   222951252.94   222951252.99   22390832721.90 22390832726.95 22390832726.99 22390832727.89 22495938365.71 23214346995.71 23594159549.68 23596256905.69 24063222530.87 24063222530.88 24063222530.93 24063222530.98 24348577460.67 25870727770.88 25870727770.89 25870727770.94 25870727770.99 26437422590.88 26437422590.89 26437422590.94 26437422590.99 26911179444.79 26913276297.80 27041498810.88 27041498811.94 27041498812.99 27043595954.89 27544385342.88 27546482480.98 27546482486.87 27546482487.93 27792411280.68 28018326431.71 28176076480.87 28181601760.76 28458877677.83 28458877678.84 28463086175.63 28465183332.80 28465183333.81 28465183334.82 28465183336.72 28465183337.75 28465183337.77 28465183338.78 28465183339.79 28465183341.69 28465183342.70 28465183343.71 28913119920.85 28913119926.95 28913119926.99 31143794842.72 3132576384.85  3132576390.95  3132576390.99  3132576391.96  32285357718.69 32417836825.87 32419933968.87 32419933968.90 32419933970.89 32419933970.94 32419933972.10032419933973.95 32419933973.99 3272297910.88  3272297910.89  3272297910.94  3272297910.99  33034670907.92 33034670909.91 33034670910.10133034670910.97 33903789786.88 33903789786.89 33903789786.94 33903789786.99 34296952314.88 34296952316.95 34296952316.99 34299049457.88 3462647984.59  34805410892.97 34805410893.92 34805410894.86 34807508038.87 35212070534.99 355734914.87   355734914.88   355734914.93   355734914.98   35852192547.88 35852192547.89 35852192547.94 35852192547.99 36509665588.63 36509797692.79 36944756847.88 36944756847.89 36944756847.94 36944756847.99 37245531378.74 37245531378.77 37245531378.79 37245531378.83 37245665252.60 37247908049.79 37247908060.74 37247908061.71 37247908063.77 37258295512.61 37258379355.83 37582835292.77 37582965332.63 38190204218.77 38190204219.78 38192301577.78 38192301577.79 3891787750.60  40190644683.97 41565867381.72 41565867381.74 41565867381.85 41565867382.87 41565867383.70 41565867383.71 41565867385.66 41567964539.86 41567964540.97 41567964541.92 41567964542.73 41624359654.72 41863133603.88 41863133603.89 41863133603.94 41863133603.99 42153485026.95 42153485026.99 42153485027.89 42153485029.90 42321050728.59 43158952066.10043158952066.89 43158952066.91 43158952066.95 43313548721.62 43544371931.10043610559407.71 43927186569.88 43929283712.85 43929283712.93 43929283718.95 43929283718.99 44327231968.10144327231968.97 44327231969.91 44327231971.92 44350553920.74 44355972199.86 4502176483.72  45064778230.61 45069446927.54 45071674889.62 45452174880.97 45452174881.87 45452174881.90 45452174881.92 45957560832.73 46343394424.94 46725515913.71 46727612863.70 49604477442.72 49652760249.87 50048828989.82 50050174752.68 50058288137.76 50061426057.83 50400893764.81 50581696400.90 50581696402.89 50581696404.10050581696405.95 50693103920.74 50693103920.77 50693103920.79 50693103920.83 51362258227.83 52377759097.90 52377759099.89 52377759100.95 52377759101.10052396529346.76 52447354635.98 52447354636.93 52447354637.87 52449451781.88 5265225235.88  5265225237.95  5265225237.99  5267322392.88  52825090735.59 5293472389.88  5295569547.98  5295569548.93  5295569549.87  53097216523.91 53097216523.96 53097216525.92 53099313668.89 53510313876.67 5363304391.75  53966538437.71 54242975897.81 54376156028.74 54376156028.77 54376156028.79 54376156028.83 54490019650.88 54490019650.89 54490019650.94 54490019650.99 54569436681.77 54569436681.78 54571533625.76 54571533626.77 54849128929.10054849128929.96 54849128930.90 54849128930.95 54849128930.99 54849128931.89 54849128932.91 54849128933.90 55975063515.89 55977160658.94 55977160659.88 55977160661.99 56213944123.98 56266717506.90 56735579373.85 57117873148.74 57117873148.77 57117873148.79 57117873148.83 58620089984.92 58620089989.10158620089989.97 58620089990.91 58821900441.60 5885610055.71  59088058364.74 59088058364.77 59088058364.79 59088058364.83 59180274506.99 59180274507.94 59180274508.88 59180274509.90 59314873579.62 60166627872.76 60173070592.87 61172658147.87 61172658147.88 61172658147.93 61172658147.98 61276787904.66 61283780578.75 61372096020.87 61372096020.88 61372096020.93 61372096020.98 61401417922.65 6165107444.63  6165239548.83  6177293594.65  62026611512.63 62395333547.95 62395333549.92 62766606145.87 63108286910.69 63110384265.70 63230379004.74 63230379004.77 63230379004.79 63230379004.83 63295845739.99 64092089369.60 64243778586.87 64243778586.88 64243778586.93 64243778586.98 64395266175.69 64816762434.90 66191829400.73 66232013900.74 66232143940.63 66353942983.71 66439544201.82 66441641654.81 67193953379.87 67193953379.88 67193953379.93 67193953379.98 68304808833.74 7065539866.100 7065539866.89  7065539866.91  7065539866.95  7442789529.60  8144176112.88  8144176112.89  8144176112.94  8144176112.99  8147615255.88  8147615255.89  8147615255.94  8147615255.99  8298977940.100 8298977940.89  8298977940.91  8298977940.95  8589140504.73  8605669008.63  8861642132.87  8861642132.88  8861642132.93  8861642132.98  8984330549.80  8986427913.81  00000500:00?00D00V00h01:01L01M01N01O01P01T01X01Y01Z01[01\01n02@02R02d02e03403C03R03a03f03g04604E04F04J04N04R04V04Z04^04b04f04g04h04i04j04m04n04o05005105505905@05O05^05_05`05a05b05c05d05e05f05j05n06206306406506606706806906:06;06<06=06>06?06@06A06E06F06K06P06U06Z06[06\06]06^06b06f06j06n06o07407907>07C07U07g08908K08L08M08Q08U08d09309B09Q09R09V09Z09^09b0:10:@0:O0:^0:b0:f0:g0:h0:i0:j0:k0:l0:m0:n0;10;50;D0;S0;T0;U0;V0;W0;X0;Y0;Z0;[0;\0;]0;^0;_0;`0;a0;b0;c0;d0;h0;i0;j0;k0;l0;m0;n0;o0<00<10<20<30<40<50<90<=0<A0<E0<F0<G0<H0<I0<M0<Q0<U0<Y0<Z0<[0<\0<]0<a0<b0<c0<d0<e0<f0=50=D0=S0=b0=g0=l0>10>60>:0>>0>C0>H0>M0>R0>S0>T0>U0>V0>W0>X0>Y0>Z0>[0>\0>]0>a0>e0>i0>m0?10?50?60?:0?>0?F0?N0?V0?Z0?b0?f0?n0@60@>0@B0@T0@Y0@^0@c0@h0A:0AL0A^0B00B10B@0BO0B^0Bm0C00C40C50C60C70C80C90C:0CL0C^0D00DB0DQ0D`0De0Di0Dm0E10E20E30E40E50E60E:0E>0EB0EQ0EU0EY0Eh0F70F;0F?0F@0FA0FB0FC0FD0FE0FF0FG0FH0FI0FJ0FK0FL0FO0FP0FQ0FR0FS0FT0FU0FV0FW0FX0FY0FZ0F[0F\0F`0Fd0Fh0Fl0Fm0G10G20G60G70G80G90G:0GI0GX0Gg0H60H:0H>0HB0HF0HX0Hj0I<0IN0I`0J20JD0JV0JW0JX0JY0JZ0J^0Jb0Jf0Jg0Jh0Ji0Jj0Jk0Jl0Jm0Jn0Jo0K30K40K50K60K70K80K90K:0K;0K>0KM0K\0Ka0Kf0Kk0L00L?0LN0LS0LX0L]0Lb0Lc0Lg0Lk0Lo0M30M70M;0M?0MC0MG0MH0MI0MJ0MK0MO0MP0MT0MX0M\0M`0Ma0Me0Mi0Mm0N10N20N60N:0N?0ND0NI0NN0NQ0NU0NY0N]0Na0Nb0Ng0Nl0O10O60O70O80O90O:0O?0OD0OI0ON0OR0OS0OX0O]0Ob0Og0Ok0OoS3ZFBS3ZFBS3ZFBS3ZFBS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLSSSSS2KLS2KLSSSSS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLSS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS3ZBuFS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLFS2KLS2KLS2KLS2KLS2KLS2KLS2KLS2KLFFFFS1HSSSSS2KLS2KLS2NB2N5S2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLSSSSSSSSS2KLS2KLS2KLSSSSSSSSSSSSSSSS2KLSS3ZBuS3ZBuS3ZBuS3ZBuSSSSS2HBS2HBS2HBS2HBFS3ZBuS3ZBuS3ZBuS3ZBuS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLFFS2KLS2KLS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBSS2HBS2HBS2HBS2HBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS2KLS2KLSSSSSSSSS1HS2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLSSSSSSSSSSSSSSSSSS2HBFFFFSSSSSSSSSS2HBS2HBS2HBS2HBSSSSS2HBS2HBS2HBS2HBSSSSS2N5SSSSFS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS3ZFBS3ZFBS3ZFBS3ZFBS2KLS2KLS3ZFBS3ZFBS3ZFBS3ZFBFFFFFFFFFFFS2KLS2KLS2KLS2KLS2KLS2KLFS2KLS2RBS3E642RBS3E642RBS3E642RBS2RBS3E642RBS2RBS3E642RBS3E642RBS3E642RBS2RBS2SB2ZB3ATR3ZFB2KLS3ZFBS3ZFBS3ZFBS3ZFBS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLFS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS1HS2KLFFFFFFS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS3ZFBS2N5S2N5S2N5FFFFFS2KLS2KLS2KLS4SEPZ4LENB3ZFBS2KLS2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2KLS2KLSSSSSSSSFSSSSS1HSSSSSSSSSSSSSS2KLS2KLS2KLS2KLSS2KLSS2N5SSSSS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS2KLS2KLS2KLS2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLSSSSS2KLS2KLS2KLSSSSSSSSSS2N5SSSSSSSSS1HS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS3ZFBS3ZFBS3ZFBS3ZFBS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS3ZBuS3ZBuS3ZBuS3ZBuFS2KLS2KLS2KLS2KLS2KLS2KLS2KLS2KLS2KLSSSSS2KLSS2HBS2HBS2HBS2HBSS2KLS2KLS2KLS2KLFS2KLS2KLS3ZFBS3ZFBS3ZFBS3ZFBS1HS2HBS2HBS2HBS2HBSS3ZBuS3ZBuS3ZBuS3ZBuSSSSS3ZBuS3ZBuS3ZBuS3ZBuS2KLSS3ZBuS3ZBuS3ZBuS3ZBuS2KLS2KL".
pose proof (proj2 (buf_nthA m1 S bl 4 (conj PL PLR) ltac:(lia))) as RB.
    pose proof (fhd_decompA _ RB) as DEC.
    destruct DEC as (_ & Hf & _ & Hr & E24 & E64).
    destruct Hf as [Hf|[Hf|[Hf|Hf]]]; (rewrite Hf in E24, E64; cbn in E64).
    all: pose_tabA 3.
    all: lazymatch type of Hf with _ = ?f => let k := eval vm_compute in (8 + f) in pose_tabA k end.
    all: repeat (gstepA Hd Hs Hf E64).
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End S.
End CANSEC1.
