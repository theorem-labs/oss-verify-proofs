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
  #[using="rc PLR NB SB ZA ZB SEPZ USRC UZF RS RSS RZ RSZ RI RIS"] Lemma decB1a : dec_okB gp tp s11 F fc SP FF ZF S bl mM RNG 1 0.
  Proof.
    unfold dec_okB, decA_at. intros until x31. intros N5 Hd Hs CZ PL GS MU WM MI.
    pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
    assert (LENB : Z.of_nat (length (map (Z_to_bv 8) bl)) = n) by (rewrite length_map; reflexivity).
    pose proof atop_range as ATR. pose proof ZB as ZBu. unfold AIMG_HI, KLS, KHIGH in ZBu.
    pose proof (rw_cells_bound _ _ _ _ CZ) as ZFB. cbn [cells_size csize Nat.add] in ZFB.
    unfold GSC, GSHC in GS.
    unfold ZCELLS, zcellA in CZ.
    Local Ltac2 Set LiaHints.tbl := fun () => "06\0?10348052249.70 10512988003.84 10512988003.90 10512988003.94 10512988003.99 1077445090.94  1077445090.98  1077445093.83  1077445093.89  10796611846.80 10796611846.86 10798709004.96 10798709005.91 12100317787.92 12270618323.85 12270618323.91 12270618326.10012270618326.96 12331426017.95 12331426017.99 12331426020.84 12331426020.90 12712716313.60 13049834364.76 13049965311.67 13049966452.63 13090646977.80 13101873376.70 13140303554.82 13140303554.88 13140303554.93 13140303554.98 13666555668.72 14763973912.98 15041153336.76 15041153343.75 15043250697.76 15043250697.77 15534906501.95 15534906501.99 15534906502.96 15640285071.66 15658255133.82 15658255133.88 15658255133.93 15658255133.98 15876876809.70 15877476798.69 16075574774.60 16800856201.70 16809028512.62 1703303920.80  1703303920.86  1705401081.83  1705401081.89  1705401083.93  1705401084.94  1705401084.98  1705401085.99  17077626520.72 17537992120.76 17537992121.77 17540089481.77 17540089481.78 17797826708.63 17797827871.67 17797958812.70 18086011986.85 18086011986.91 18086011991.10018086011991.96 18466260673.88 18511472777.72 18511472777.81 18511472777.82 18511472777.84 18511472777.87 18511472777.88 18511472777.90 18511472777.92 18511472777.93 18511472777.94 18511472777.97 18511472777.98 18511472777.99 18589810881.88 18681669866.60 19010590676.82 19010590676.88 19010590676.93 19010590676.98 19302163537.78 19302163539.76 19302163541.70 19302163549.82 19589975962.81 19589975962.87 19589975962.92 19589975962.97 19898057824.84 19908892480.73 20700320864.63 222951252.82   222951252.88   222951252.93   222951252.98   22390832721.83 22390832721.89 22390832726.94 22390832726.98 22495938363.70 23214346997.70 23596256905.66 23596676285.65 24063222530.81 24063222530.87 24063222530.92 24063222530.97 24991237562.77 25870727770.82 25870727770.88 25870727770.93 25870727770.98 26437422590.82 26437422590.88 26437422590.93 26437422590.98 26911179444.80 26913276297.81 27041498811.93 27041498812.98 27043595954.82 27043595954.88 27544385342.81 27544385342.87 27546482480.97 27546482487.92 27792411280.70 28176076481.85 28181601760.75 28463086175.63 28465183332.81 28465183333.82 28465183334.83 28465183336.77 28465183337.78 28465183338.79 28465183339.80 28465183341.67 28465183342.71 28465183343.76 28913119925.95 28913119925.99 28915217082.77 29792256214.77 30801439541.78 31143794842.72 31150540312.72 3132576389.95  3132576389.99  3132576390.96  32285357718.69 32417836825.80 32417836825.86 32419933968.83 32419933968.89 32419933970.93 32419933972.99 32419933973.94 32419933973.98 32573021867.67 3272297910.82  3272297910.88  3272297910.93  3272297910.98  33034670907.85 33034670907.91 33034670910.10033034670910.96 33903789786.82 33903789786.88 33903789786.93 33903789786.98 34296952316.94 34296952316.98 34299049457.81 34299049457.87 3462647984.59  34805410892.96 34805410893.91 34807508038.80 34807508038.86 35212070533.99 35499667119.59 355734914.81   355734914.87   355734914.92   355734914.97   35852192547.82 35852192547.88 35852192547.93 35852192547.98 36944756847.82 36944756847.88 36944756847.93 36944756847.98 37245531378.70 37245531378.76 37245531378.78 37245531378.82 37245661434.63 37245665252.60 37247908051.82 37247908059.70 37247908061.76 37247908063.78 37258295512.61 37582835292.78 37582965332.63 37582966751.67 38190204219.79 38192301577.80 3891787750.60  39971308225.85 39977226720.75 40190644680.99 41565867381.72 41565867381.74 41565867382.80 41565867382.86 41565867383.70 41565867383.71 41565867385.66 41567964538.83 41567964539.85 41567964540.96 41567964541.91 41567964542.73 41624359654.72 41863133603.82 41863133603.88 41863133603.93 41863133603.98 42153485026.94 42153485026.98 42153485029.83 42153485029.89 42321050728.59 42707542977.86 43158952066.84 43158952066.90 43158952066.94 43158952066.99 43313548721.62 43608317443.67 43610559401.70 43929283712.90 43929283717.95 43929283717.99 43929283719.93 44327231968.10044327231968.96 44327231971.85 44327231971.91 4502176483.72  45064778230.61 45069446927.54 45071674889.62 45452174880.96 45452174881.83 45452174881.89 45452174881.91 45689441237.78 45689441238.77 45697359223.67 45957560832.72 46343394424.95 46343394424.96 46724821560.74 46725515913.75 49404231370.82 49604477442.72 49652760248.88 50050174752.75 50056190977.85 50398796617.85 50581696400.83 50581696400.89 50581696404.99 50581696405.94 50693103920.70 50693103920.76 50693103920.78 50693103920.82 52377759097.83 52377759097.89 52377759100.94 52377759101.99 52396529346.75 52447354635.97 52447354636.92 52449451781.81 52449451781.87 5265225237.94  5265225237.98  5267322392.81  5267322392.87  5293472389.81  5293472389.87  5295569547.97  5295569548.92  53097216520.95 53097216522.92 53510313876.67 5363304390.74  53966538437.71 54242975897.81 54376156028.70 54376156028.76 54376156028.78 54376156028.82 54490019650.82 54490019650.88 54490019650.93 54490019650.98 54569436681.79 54571533626.78 54849128929.95 54849128929.99 54849128930.94 54849128930.98 54849128932.84 54849128932.90 54849128933.83 54849128933.89 55975063515.82 55975063515.88 55977160658.93 55977160661.98 56213944120.10056735579368.96 56735579370.92 56735579373.91 57117873148.70 57117873148.76 57117873148.78 57117873148.82 58620089984.85 58620089984.91 58620089989.10058620089989.96 58649831881.78 58821900441.60 5885610055.71  59088058364.70 59088058364.76 59088058364.78 59088058364.82 59180274506.98 59180274507.93 59180274509.83 59180274509.89 59314873579.62 61172658147.81 61172658147.87 61172658147.92 61172658147.97 61264202057.67 61276787904.66 61285877737.74 61372096020.81 61372096020.87 61372096020.92 61372096020.97 61401418176.72 6177293336.72  62009686963.67 62026611512.63 62395333544.97 63108286905.77 63108286911.75 63110384265.76 63110384265.78 63230379004.70 63230379004.76 63230379004.78 63230379004.82 64092089369.60 64243778586.81 64243778586.87 64243778586.92 64243778586.97 64324655132.82 64324786591.67 64324787220.63 64395266175.69 64816762433.88 64978467201.70 67193953379.81 67193953379.87 67193953379.92 67193953379.97 68304808833.73 7065539866.84  7065539866.90  7065539866.94  7065539866.99  7093271040.72  7442789529.60  8144176112.82  8144176112.88  8144176112.93  8144176112.98  8147615255.82  8147615255.88  8147615255.93  8147615255.98  8298977940.84  8298977940.90  8298977940.94  8298977940.99  8605669008.63  8861642132.81  8861642132.87  8861642132.92  8861642132.97  8984330549.81  8986427913.82  00000400900>00C00H00Z00l01>01P01Q01R01S01T01X01Y01Z01[01\01n02@02R02d02e02i02m03103@03O03^03m04<04K04P04T04X04\04`04d04e04f04g04j04k04l04m04n05205605=05L05[05\05]05^05_05`05a05b05c05g05k05o06306706;06?06C06D06E06F06G06K06L06M06N06O06P06Q06R06S06T06U06V06W06X06\06]06b06g06l07107207307407507907=07A07E07T07c07d07i07n08308808J08\08n09@09A09B09F09J09Y09h0:70:F0:G0:K0:O0:S0:W0:f0;50;D0;S0;W0;[0;\0;]0;^0;_0;`0;a0;b0;c0;f0<50<D0<E0<F0<G0<H0<I0<J0<K0<L0<M0<N0<O0<P0<Q0<R0<S0<T0<X0<\0<]0<^0<_0<`0<a0<b0<c0<d0<e0<f0<g0<h0<i0<m0=10=50=90=:0=;0=<0==0=A0=E0=I0=M0=N0=O0=P0=Q0=U0=V0=W0=X0=Y0=Z0=[0=j0>90>H0>W0>\0>a0>f0>k0?00?50?:0??0?@0?A0?B0?C0?D0?E0?F0?G0?H0?I0?J0?N0?R0?V0?Z0?^0?_0?n0@=0@A0@E0@M0@U0@]0@a0@i0@m0A50A=0AE0AM0AQ0Ac0Ah0Am0B20B70BI0B[0Bm0C?0C@0CD0CS0Cb0D10D@0DC0DD0DE0DF0DG0DH0DI0D[0Dm0E?0EQ0EV0EZ0E^0Eb0Ec0Ed0Ee0Ef0Ek0F00F50F60F:0F>0FB0FF0FJ0FY0F]0Fl0G;0G?0G@0GA0GB0GC0GD0GE0GF0GG0GH0GI0GJ0GK0GN0GO0GP0GQ0GR0GS0GT0GU0GV0GW0GX0GY0GZ0G^0Gb0Gc0Gg0Gh0Gl0Gm0Gn0Go0H00H?0HN0H]0Hl0I00I40IF0IX0Ij0J<0JN0J`0K20KD0KE0KF0KG0KH0KL0KP0KT0KX0KY0KZ0K[0K\0K]0K^0K_0K`0Ka0Kb0Kf0Kg0Kh0Ki0Kj0Kk0Kl0Km0Kn0L10L60L;0L@0LE0LF0LU0Ld0Li0Ln0M30M80M90M=0MA0ME0MI0MM0MQ0MU0MY0MZ0M[0M\0M]0M^0Mb0Mf0Mj0Mn0N20N60N:0N;0N?0N@0NE0NJ0NO0NT0NW0N[0N_0Nc0Ng0Nh0Ni0Nn0O30O80O=0O>0O?0O@0OA0OF0OK0OP0OU0OV0O[0O`0Oe0Oj0On0P2S2KLS3ZFBS3ZFBS3ZFBS3ZFBS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLSSSSS2KLSSSSS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLSS2KLS2KLS2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS3ZBuS2KLS2KLS2KLS2KLS2KLFFFS1HSSSSS2KLS2KLS2NB2N5S2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLSSSSSSSSS2KLS2KLS2KLS2KLS2KLS2KLS2KLS2KLSSSSS2KLSSSSSSSSSSSSSS2KLSS3ZBuS3ZBuS3ZBuS3ZBuSSSSS2HBS2HBS2HBS2HBS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLFS3ZBuS3ZBuS3ZBuS3ZBuS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLFFS2KLS2KLS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBSS2HBS2HBS2HBS2HBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS2KLS2KLSSSSSSSSS1HS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLSSSSSSSSSSSSSSSFS2HBS2KLFFFSSSSSSSSSFS2HBS2HBS2HBS2HBSSSSS2HBS2HBS2HBS2HBSSSSS2N5SSSSFSS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS3ZFBS3ZFBS3ZFBS3ZFBS3ZFBS3ZFBS3ZFBS3ZFBFFFFFFFFFFFS2KLS2KLS2KLS2KLS2KLFS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2KLS2RBS3E642RBS3E642RBS3E642RBS2RBS3E642RBS2RBS3E642RBS3E642RBS3E642RBS3E642RBS2RBS2SB2ZB3ATR3ZFB2KLS3ZFBS3ZFBS3ZFBS3ZFBS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLFS2KLS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS1HFFFFFFS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS3ZFBS2N5S2N5S2N5FFFFS3RB0S3RB0S3RB0FS2KLS2KLS2KLS2KLS2KLS4SEPZ4LENB3ZFBS2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2KLSSSSSSSSSSSSS1HSSSSSSSSSSSSS2KLS2KLSS2KLSS2N5SSSSS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS2KLS2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLSSSSS2KLS2KLS2KLS2KLSSSSSSSSFSS2N5SSSSSSSSS1HS3ZFBS3ZFBS3ZFBS3ZFBFS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS3ZBuS3ZBuS3ZBuS3ZBuFS2KLS2KLS2KLS2KLS2KLS2KLS2KLS2KLSSSSSS2HBS2HBS2HBS2HBS2KLS2KLS2KLSS2KLFS3ZFBS3ZFBS3ZFBS3ZFBS1HS2HBS2HBS2HBS2HBFSS3ZBuS3ZBuS3ZBuS3ZBuSSSSS3ZBuS3ZBuS3ZBuS3ZBuSS3ZBuS3ZBuS3ZBuS3ZBuS2KLS2KL".
pose proof (proj2 (buf_nthA m1 S bl 4 (conj PL PLR) ltac:(lia))) as RB.
    pose proof (fhd_decompA _ RB) as DEC.
    destruct DEC as (_ & Hf & _ & Hr & E24 & E64).
    destruct Hf as [Hf|[Hf|[Hf|Hf]]]; (rewrite Hf in E24, E64; cbn in E64).
    all: pose_tabA 1.
    all: lazymatch type of Hf with _ = ?f => let k := eval vm_compute in (8 + f) in pose_tabA k end.
    all: repeat (gstepA Hd Hs Hf E64).
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End S.
End CANSEC1.
