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
  #[using="rc PLR NB SB ZA ZB SEPZ USRC UZF RS RSS RZ RSZ RI RIS"] Lemma decB0a : dec_okB gp tp s11 F fc SP FF ZF S bl mM RNG 0 0.
  Proof.
    unfold dec_okB, decA_at. intros until x31. intros N5 Hd Hs CZ PL GS MU WM MI.
    pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
    assert (LENB : Z.of_nat (length (map (Z_to_bv 8) bl)) = n) by (rewrite length_map; reflexivity).
    pose proof atop_range as ATR. pose proof ZB as ZBu. unfold AIMG_HI, KLS, KHIGH in ZBu.
    pose proof (rw_cells_bound _ _ _ _ CZ) as ZFB. cbn [cells_size csize Nat.add] in ZFB.
    unfold GSC, GSHC in GS.
    unfold ZCELLS, zcellA in CZ.
    Local Ltac2 Set LiaHints.tbl := fun () => "06S0>10349463449.6910512988003.7710512988003.8310512988003.8710512988003.941075347949.78 1075347949.84 1077445092.89 1077445092.93 10796611847.8410796611850.7310796611850.7910798709006.9112100317787.9112100317789.8812270618322.8112270618322.8712270618325.9212270618325.9612331426018.9112331426018.9512331426021.8012331426021.8612712716313.6013090646977.8013101873376.7013140303554.7813140303554.8413140303554.8913140303554.9413666555668.7214763973915.9515041153336.7415041153343.7315043250697.7415043250697.7515534906502.9115534906502.9515534906503.9215640285071.6615658255133.7815658255133.8415658255133.8915658255133.9415876876809.7315876876809.7515878973752.7415878973758.7216075574774.6016800856201.7016809028512.621703303922.79 1703303922.85 1703303935.76 1703303935.82 1705401082.89 1705401083.90 1705401083.94 1705401084.95 17537992121.7517540089481.7618086011987.8118086011987.8718086011988.9218086011988.9618511472777.7218511472777.7418511472777.7718511472777.7818511472777.7918511472777.8018511472777.8318511472777.8418511472777.8518511472777.8718511472777.8918511472777.9018511472777.9218511472777.9418511472777.9518681669866.6019010590676.7819010590676.8419010590676.8919010590676.9419299691007.6719302163538.7519302163540.7319302163550.7919589975962.7419589975962.8019589975962.8519589975962.9219898057826.8119908892480.7220700320864.63222951252.79  222951252.85  222951252.90  222951252.95  22390832722.7922390832722.8522390832727.9022390832727.9422497888913.6723211843423.6723596256905.6623596676285.6523871407047.8124063222530.7424063222530.8024063222530.8524063222530.9224991237562.7725320119744.7225327275746.8125870727770.7825870727770.8425870727770.8925870727770.9426437422590.7826437422590.8426437422590.8926437422590.9426911179444.7826913276297.7927041498810.9327043595953.8627043595966.7527043595966.8127544385341.7727544385341.8327546482486.8827546482487.9327792411280.7028021048089.6928463086175.6328465183332.7928465183333.8028465183336.7528465183337.7628465183338.7728465183339.7828465183341.6728465183342.7328465183343.7428913119924.9728913119926.9128913119926.9528915217082.7729792256214.7730801439541.7831143794842.723132576390.91 3132576390.95 3132576391.92 31502733196.6731502863236.6331502863887.6732285357718.6932417836822.7632417836822.8232417836827.7932417836827.8532419933970.9032419933970.9432419933971.8932419933973.9532573021867.673272297910.78 3272297910.84 3272297910.89 3272297910.94 33034670906.8133034670906.8733034670909.9233034670909.9633197395535.5933903789786.7933903789786.8533903789786.9033903789786.9534296952314.8934296952314.9334299049471.7634299049471.823462647984.59 34805410894.9134807508039.8434807508042.7334807508042.7935212070534.95355734914.74  355734914.80  355734914.85  355734914.92  35852192547.7835852192547.8435852192547.8935852192547.9436255715521.6936944756847.7836944756847.8436944756847.8936944756847.9437245531378.6737245531378.7337245531378.7537245531378.7937245661434.6337245662577.6737245665252.6037247908048.7937247908058.7337247908060.7537258295512.6138190204219.7738192301577.783891787750.60 40190644683.9641565867381.7241565867381.7441565867383.7041565867383.7141565867383.8441565867385.6641565867386.7341565867386.7941567964538.8341567964539.8241567964542.7341567964542.9141624359654.7241863133603.7941863133603.8541863133603.9041863133603.9542153485028.8942153485028.9342155582189.7842155582189.8442321050728.5942709640135.8143158952066.7743158952066.8343158952066.8743158952066.9443313548721.6243608317443.6743929283712.8943929283713.8643929283718.9143929283718.9544327231969.9244327231969.9644327231972.8144327231972.8744350553920.7244355972194.814502176483.72 45064778230.6145069446927.5445071674889.6245450077739.7645450077739.8245450077739.8445452174882.9145689441237.7845689441238.7745697359223.6746343394427.9346725515913.7346725515913.7446727612862.7246727612863.7349404231370.8249604477442.7249652760251.9249652760252.8749652760253.8850398796617.8550579599259.7950579599259.8550581696402.9050581696405.9550693103920.6750693103920.7350693103920.7550693103920.7952375661938.7952375661938.8552377759099.9052377759100.9552447354635.9452447354636.8952449451781.7852449451781.845265225235.89 5265225235.93 5267322390.76 5267322390.82 5293472390.77 5293472390.83 5295569548.93 5295569549.88 53097216523.9153097216523.9253510313876.675363304390.74 53966538437.7154242975897.8154376156028.6754376156028.7354376156028.7554376156028.7954490019650.7954490019650.8554490019650.9054490019650.9554569436681.7754571533626.7654849128930.9154849128930.9554849128931.9054849128931.9454849128933.8054849128933.8654849128934.7954849128934.8555975063511.7555975063511.8155975063512.8655977160659.9356735579368.9057117873148.6757117873148.7357117873148.7557117873148.7958620089985.8158620089985.8758620089990.9258620089990.9658649831881.7858821900441.605885610055.71 59088058364.6759088058364.7359088058364.7559088058364.7959178177349.8659178177351.7659178177351.8259180274508.9359314873579.6261172658147.7461172658147.8061172658147.8561172658147.9261276787904.6661285877737.7461372096020.7461372096020.8061372096020.8561372096020.9262009686963.6762026611512.6362395333547.9462764508999.8163110050239.7163110384265.7263230379004.6763230379004.7363230379004.7563230379004.7964092089369.6064243778586.7464243778586.8064243778586.8564243778586.9264395266175.6964402063724.7364402194671.6764402195812.6364431430668.7964431560708.6364431562127.6764981188865.6966232013900.7566232143940.6366232145359.6766356652353.6967193953379.7467193953379.8067193953379.8567193953379.9267255412633.6968304808833.727065539866.77 7065539866.83 7065539866.87 7065539866.94 7442789529.60 8144176112.78 8144176112.84 8144176112.89 8144176112.94 8147615255.78 8147615255.84 8147615255.89 8147615255.94 8298977940.77 8298977940.83 8298977940.87 8298977940.94 8605669008.63 8861642132.74 8861642132.80 8861642132.85 8861642132.92 00000400900>00C00H00Z00l01>01P01Q01R01S01T01X01\01]01^01_01`02202D02V02h02i03803G03V03e04404C04H04L04P04T04X04\04]04^04_04b04c04d04e04f04j04n05205605=05L05[05\05]05^05_05`05a05b05c05g05k05l05m05n05o06006106206306406506606706806906:06;06<06=06>06?06D06I06N06S06T06U06V06W06[06_06c06g07607E07F07K07P07U07Z07l08>08P08b08c08d08h08l09009?09N09]09l09m0:<0:K0:O0:S0:W0:[0:j0;90;H0;W0;[0;_0;`0;a0;b0;c0;d0;e0;f0;g0;j0;n0;o0<00<10<20<30<40<50<60<70<80<90<:0<;0<<0<=0<>0<B0<C0<D0<E0<I0<M0<Q0<R0<S0<T0<U0<V0<W0<X0<Y0<Z0<[0<_0<c0<g0<k0<l0<m0<n0<o0=00=40=80=<0=@0=A0=B0=C0=D0=H0=I0=J0=K0=L0=M0=\0=k0>:0>I0>N0>S0>X0>]0>^0>c0>h0>m0?20?30?40?50?60?70?80?90?:0?;0?<0?=0?A0?E0?F0?J0?N0?V0?Z0?b0?j0?n0@60@>0@F0@N0@R0@Z0@l0A10A60A;0A@0AR0Ad0B60BH0BI0BM0B\0Bk0C:0CI0CL0CM0CN0CO0CP0CQ0Cc0D50DG0DY0Dh0E70E<0E@0ED0EH0EI0EJ0EK0EL0EQ0EV0E[0E_0Ec0Eg0Ek0Eo0F30FB0FF0FJ0FN0FR0FS0FT0FU0FV0FW0FX0FY0FZ0F[0F\0F]0F^0F_0F`0Fa0Fb0Fc0Fd0Fe0Ff0Fg0Fh0Fi0Fj0Fn0G20G30G70G80G<0G=0G>0G?0G@0GO0G^0Gm0H<0H@0HD0HV0Hh0I:0IL0I^0J00JB0JT0JU0JV0JW0JX0J\0J]0J^0J_0J`0Ja0Jb0Jc0Jd0Je0Jf0Jj0Jk0Jl0Jm0Jn0Jo0K00K10K20K50K:0K?0KD0KI0KX0Kg0Kl0L10L60L;0L?0LC0LG0LK0LO0LS0LT0LU0LV0LW0LX0L\0L`0Ld0Lh0Li0Lm0M10M50M90M=0MA0MB0MF0MJ0MN0MO0MT0MY0M^0Mc0Mg0Mj0Mn0N20N60N:0N;0N@0NE0NJ0NO0NP0NQ0NR0NS0NX0N]0Nb0Ng0Nh0Nm0O20O70O<S2KLS3ZFBS3ZFBS3ZFBS3ZFBS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLSSSSS2KLS2KLSSSSS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLSS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS3ZBuS2KLS2KLS2KLS2KLS2KLFFFS1HSSSSS2KLS2KLS2KLS2KLS2NB2N5S2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLSSSSSSSSS2KLS2KLSSSSSSSSSSSSSSSSSSSSS3ZBuS3ZBuS3ZBuS3ZBuSSSSS2HBS2HBS2HBS2HBS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLFS3ZBuS3ZBuS3ZBuS3ZBuS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLFFS2KLS2KLS2KLS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBSS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2HBS2HBS2HBS2HBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS2KLS2KLSSSSSSSSS1HS2KLSSSSSSSSSSSSSSSFS2HBFFFS2KLS2KLS2KLSSSSSSSSSFS2HBS2HBS2HBS2HBSSSSSS2HBS2HBS2HBS2HBSSSSS2N5SSSSFS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS3ZFBS3ZFBS3ZFBS3ZFBFS3ZFBS3ZFBS3ZFBS3ZFBFFFFFFFFFFFS2KLS2KLFS2KLS2RBS3E642RBS2RBS3E642RBS3E642RBS2RBS3E642RBS3E642RBS3E642RBS3E642RBS2RBS3E642RBS2SB2ZB3ATR3ZFB2KLS3ZFBS3ZFBS3ZFBS3ZFBS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLFS2KLS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS1HFFFFFS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS3ZFBS2N5S2N5S2N5FFFFS3RB0S3RB0S3RB0S2KLS2KLS2KLS2KLS2KLS2KLS4SEPZ4LENB3ZFBS2KLS2KLS2KLS2KLSSSSSSSSSSSSSSSSSSSSSSSSS2KLS2KLSS2KLSS2N5SSSSS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS2KLS2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLSSSSS2KLSSSSSSSSFSS2N5SSSSSSSSS1HS3ZFBS3ZFBS3ZFBS3ZFBS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS3ZBuS3ZBuS3ZBuS3ZBuS2KLS2KLS2KLS2KLS2KLS2KLSSSSSS2HBS2HBS2HBS2HBSS2KLS2KLS2KLS2KLS2KLS2KLFS2KLS2KLS2KLFS3ZFBS3ZFBS3ZFBS3ZFBS2KLS1HS2HBS2HBS2HBS2HBSS3ZBuS3ZBuS3ZBuS3ZBuSSSSS3ZBuS3ZBuS3ZBuS3ZBuSS3ZBuS3ZBuS3ZBuS3ZBu".
pose proof (proj2 (buf_nthA m1 S bl 4 (conj PL PLR) ltac:(lia))) as RB.
    pose proof (fhd_decompA _ RB) as DEC.
    destruct DEC as (_ & Hf & _ & Hr & E24 & E64).
    destruct Hf as [Hf|[Hf|[Hf|Hf]]]; (rewrite Hf in E24, E64; cbn in E64).
    all: pose_tabA 0.
    all: lazymatch type of Hf with _ = ?f => let k := eval vm_compute in (8 + f) in pose_tabA k end.
    all: repeat (gstepA Hd Hs Hf E64).
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End S.
End CANSEC1.
