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
  #[using="rc PLR NB SB ZA ZB SEPZ USRC UZF RS RSS RZ RSZ RI RIS"] Lemma decB1b : dec_okB gp tp s11 F fc SP FF ZF S bl mM RNG 1 32.
  Proof.
    unfold dec_okB, decA_at. intros until x31. intros N5 Hd Hs CZ PL GS MU WM MI.
    pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
    assert (LENB : Z.of_nat (length (map (Z_to_bv 8) bl)) = n) by (rewrite length_map; reflexivity).
    pose proof atop_range as ATR. pose proof ZB as ZBu. unfold AIMG_HI, KLS, KHIGH in ZBu.
    pose proof (rw_cells_bound _ _ _ _ CZ) as ZFB. cbn [cells_size csize Nat.add] in ZFB.
    unfold GSC, GSHC in GS.
    unfold ZCELLS, zcellA in CZ.
    Local Ltac2 Set LiaHints.tbl := fun () => "06J0>10349463449.6810512988003.8310512988003.8610512988003.9010512988003.951077445090.90 1077445090.94 1077445093.82 1077445093.85 10796611846.7910796611846.8210798709004.9210798709005.8712100317787.9012100317789.8712270618323.8412270618323.8712270618326.9212270618326.9612331426017.9112331426017.9512331426020.8312331426020.8612712716313.6013090646977.7913101873376.6913140303554.8113140303554.8413140303554.8913140303554.9413666555668.7214763973915.9415041153336.7315041153343.7215043250697.7315043250697.7415534906502.9015534906502.9415534906503.9115640285071.6615658255133.8115658255133.8415658255133.8915658255133.9415876876809.6915876876809.7215876876809.7415877476798.6815878973752.7315878973758.7116075574774.6016800856201.7016809028512.621703303920.79 1703303920.82 1705401081.82 1705401081.85 1705401083.89 1705401084.90 1705401084.94 1705401085.95 17537992121.7417540089481.7517797826708.6317797958812.6918086011986.8418086011986.8718086011991.9218086011991.9618511472777.7218511472777.8018511472777.8118511472777.8318511472777.8418511472777.8618511472777.8818511472777.8918511472777.9018511472777.9318511472777.9418511472777.9518681669866.6019010590676.8119010590676.8419010590676.8919010590676.9419302163538.7419302163540.7219302163541.6919302163550.7819589975962.8019589975962.8319589975962.8819589975962.9319898057826.8019908892480.7120700320864.63222951252.81  222951252.84  222951252.89  222951252.94  22390832721.8222390832721.8522390832726.9022390832726.9422495938360.6623214346998.6623596256905.6623596676285.6523871407050.8324063222530.8024063222530.8324063222530.8824063222530.9324348577460.6725320119744.7125327275746.8025870727770.8125870727770.8425870727770.8925870727770.9426437422590.8126437422590.8426437422590.8926437422590.9426911179444.7726913276297.7827041498811.8927041498812.9427043595954.8127043595954.8427544385342.8027544385342.8327546482480.9327546482487.8827792411280.6928021048089.6828463086175.6328465183332.7828465183333.7928465183336.7428465183337.7528465183338.7628465183339.7728465183341.6728465183342.7028465183342.7228465183343.7328913119926.9028913119926.9431143794842.723132576390.90 3132576390.94 3132576391.91 32285357718.6932417836825.7932417836825.8232419933968.8232419933968.8532419933970.8932419933972.9532419933973.9032419933973.9432575492866.663272297910.81 3272297910.84 3272297910.89 3272297910.94 33034670907.8433034670907.8733034670910.9233034670910.9633903789786.8133903789786.8433903789786.8933903789786.9434296952316.9034296952316.9434299049457.8034299049457.833462647984.59 34805410892.9234805410893.8734807508038.7934807508038.8235212070534.9435499667119.59355734914.80  355734914.83  355734914.88  355734914.93  35852192547.8135852192547.8435852192547.8935852192547.9436255715521.6836944756847.8136944756847.8436944756847.8936944756847.9437245531378.6937245531378.7237245531378.7437245531378.7837245665252.6037247908048.7837247908056.6637247908058.7237247908059.6937247908060.7437258295512.6138190204219.7638192301577.773891787750.60 40190644683.9541565867381.7241565867381.7441565867382.7941565867382.8241565867383.7041565867383.7141565867385.6641567964540.9241567964541.7941567964541.8741567964542.7341624359654.7241863133603.8141863133603.8441863133603.8941863133603.9442153485026.9042153485026.9442153485029.8242153485029.8542321050728.5942709640138.8343158952066.8343158952066.8643158952066.9043158952066.9543313548721.6243608316808.6343610559402.6643927186569.8343929283712.8843929283718.9043929283718.9444327231968.9244327231968.9644327231971.8444327231971.8744350553920.7144355972194.804502176483.72 45064778230.6145069446927.5445071674889.6245452174880.9245452174881.8545452174881.8745452174882.8146343394427.9246725515913.7246725515913.7346727612862.7146727612863.7249404231368.7949604477442.7249652760251.8649652760251.9149652760253.8749654857396.8450398796617.8550581696400.8250581696400.8550581696404.9550581696405.9050693103920.6950693103920.7250693103920.7450693103920.7851364357560.7852377759097.8252377759097.8552377759100.9052377759101.9552447354635.9352447354636.8852449451781.8052449451781.835265225237.90 5265225237.94 5267322392.80 5267322392.83 5293472389.80 5293472389.83 5295569547.93 5295569548.88 53097216523.9053097216523.9153510313876.675363304391.75 53966538437.7154242975897.8154376156028.6954376156028.7254376156028.7454376156028.7854490019650.8154490019650.8454490019650.8954490019650.9454569436681.7654571533626.7554849128929.9154849128929.9554849128930.9054849128930.9454849128932.8354849128932.8654849128933.8254849128933.8555975063515.8155975063515.8455977160658.8955977160661.9456735579368.8957117873148.6957117873148.7257117873148.7457117873148.7858620089984.8458620089984.8758620089989.9258620089989.9658821900441.605885610055.71 59088058364.6959088058364.7259088058364.7459088058364.7859180274506.9459180274507.8959180274509.8259180274509.8559314873579.6261172658147.8061172658147.8361172658147.8861172658147.9361264202946.6361276787904.6661283780578.7561372096020.8061372096020.8361372096020.8861372096020.9362012192282.6662026611512.6362395333547.9362764509002.8363110050239.7063110384265.7163230379004.6963230379004.7263230379004.7463230379004.7864092089369.6064243778586.8064243778586.8364243778586.8864243778586.9364395266175.6964402063724.7264402195812.6364431430668.7864431560708.6364981188865.6866232013900.7466232143940.6366356652353.6867193953379.8067193953379.8367193953379.8867193953379.9367255412633.6868304808833.717065539866.83 7065539866.86 7065539866.90 7065539866.95 7442789529.60 8144176112.81 8144176112.84 8144176112.89 8144176112.94 8147615255.81 8147615255.84 8147615255.89 8147615255.94 8298977940.83 8298977940.86 8298977940.90 8298977940.95 8605669008.63 8861642132.80 8861642132.83 8861642132.88 8861642132.93 00000400900>00C00H00Z00l01>01P01Q01R01S01T01X01\01]01^01_01`02202D02V02h02i03803G03V03e04404C04H04L04P04T04X04\04]04^04_04b04c04d04e04f04j04n05205605:05>05E05T05c05d05e05f05g05h05i05j05k05o06306706;06<06=06>06?06@06A06B06C06D06E06F06G06H06I06J06K06L06Q06V06[06`06a06b06c06d06h06l07007407C07R07S07X07]07b07g08908K08]08o09009109509909=09L09[09j0:90::0:I0:X0:\0:`0:d0:h0;70;F0;U0;d0;h0;l0;m0;n0;o0<00<10<20<30<40<70<;0<<0<=0<>0<?0<@0<A0<B0<C0<D0<E0<F0<G0<H0<L0<M0<N0<O0<P0<Q0<R0<S0<T0<U0<V0<W0<X0<Y0<]0<a0<e0<i0<j0<k0<l0<m0=10=50=90==0=>0=?0=@0=A0=E0=F0=G0=H0=I0=J0=K0=Z0=i0>80>G0>L0>Q0>V0>[0>\0>a0>f0>k0?00?10?20?30?40?50?60?70?80?90?:0?;0??0?C0?D0?H0?L0?T0?\0?d0?h0@00@40@<0@D0@L0@P0@b0@g0@l0A10A60AH0AZ0Al0B>0B?0BC0BR0Ba0C00C?0CB0CC0CD0CE0CF0CG0CH0CZ0Cl0D>0DP0D_0Dn0E30E70E;0E?0E@0EA0EB0EC0EG0EK0EO0ES0EW0E[0Ej0En0F20F60F:0F>0F?0F@0FA0FB0FC0FD0FE0FF0FG0FH0FI0FJ0FK0FL0FM0FN0FO0FP0FQ0FR0FS0FT0FU0FV0FW0F[0F_0F`0Fd0Fe0Fi0Fj0Fk0Fl0Fm0G<0GK0GZ0Gi0Gm0H10HC0HU0Hg0I90IK0I]0Io0JA0JB0JC0JD0JE0JI0JJ0JK0JL0JM0JN0JO0JP0JQ0JR0JV0JW0JX0JY0JZ0J[0J\0J]0J^0Ja0Jf0Jk0K00K50K60KE0KT0KY0K^0Kc0Kh0Kl0L00L40L80L<0L@0LA0LB0LC0LD0LE0LI0LM0LQ0LU0LV0LZ0L^0Lb0Lf0Lg0Lk0Lo0M00M50M:0M?0MD0MH0MK0MO0MS0MW0M[0M\0Ma0Mf0Mk0N00N10N20N30N40N90N>0NC0NH0NI0NN0NS0NX0N]S2KLS3ZFBS3ZFBS3ZFBS3ZFBS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLSSSSS2KLS2KLSSSSS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLSS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS3ZBuS2KLS2KLS2KLS2KLS2KLFFFS1HSSSSS2KLS2KLS2KLS2KLS2KLS2KLS2NB2N5S2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLSSSSSSSSS2KLS2KLS2KLS2KLSSSSSSSSSSSSSSSSSS3ZBuS3ZBuS3ZBuS3ZBuSSSSS2HBS2HBS2HBS2HBS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLFS3ZBuS3ZBuS3ZBuS3ZBuS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLFFS2KLS2KLS2KLS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBSS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2HBS2HBS2HBS2HBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS2KLS2KLSSSSSSSSS1HS2KLSSSSSSSSSSSSSS2HBFFFSSSSSSSSSFS2HBS2HBS2HBS2HBSSSSS2HBS2HBS2HBS2HBSSSSS2N5SSSSFSS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS3ZFBS3ZFBS3ZFBS3ZFBFS3ZFBS3ZFBS3ZFBS3ZFBFFFFFFFFFFFS2KLS2KLFS2KLS2RBS3E642RBS3E642RBS3E642RBS2RBS3E642RBS2RBS3E642RBS3E642RBS3E642RBS2RBS2SB2ZB3ATR3ZFB2KLS3ZFBS3ZFBS3ZFBS3ZFBS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLFS2KLS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS1HFFFFFFS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS3ZFBS2N5S2N5S2N5FFFFS2KLS2KLS2KLS2KLS2KLS2KLS4SEPZ4LENB3ZFBS2KLS2KLS2KLS2KLS2KLSSSSSSSSFSSSSSSSSSSSSSSSSS2KLS2KLSS2KLSS2N5SSSSS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS2KLS2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLSSSSS2KLSSSSSSSSSS2N5SSSSSSSSS1HS3ZFBS3ZFBS3ZFBS3ZFBFS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS3ZBuS3ZBuS3ZBuS3ZBuS2KLS2KLS2KLS2KLS2KLS2KLSSSSSS2HBS2HBS2HBS2HBSS2KLS2KLS2KLS2KLFS2KLS2KLFS3ZFBS3ZFBS3ZFBS3ZFBS2KLS1HS2HBS2HBS2HBS2HBSS3ZBuS3ZBuS3ZBuS3ZBuSSSSS3ZBuS3ZBuS3ZBuS3ZBuSS3ZBuS3ZBuS3ZBuS3ZBu".
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
