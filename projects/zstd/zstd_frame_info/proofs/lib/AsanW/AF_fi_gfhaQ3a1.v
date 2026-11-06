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
  #[using="rc PLR NB SB ZA ZB SEPZ USRC UZF RS RSS RZ RSZ RI RIS"] Lemma decC3a1 : forall m1 x1 x5 x6 x7 x11 x14 x16 x17 x28 x29 x30 x31,
    5 <= n -> Z.land (Znth 4 bl) 3 = 3 -> Z.land (Znth 4 bl) 32 = 0 -> Z.shiftr (Znth 4 bl) 6 = 1 ->
    rw_cells asegs m1 ZF ZCELLS -> bytes_at asegs m1 S (map (Z_to_bv 8) bl) -> GSC m1 ->
    munch W mM m1 -> wmono asegs mM m1 -> mem_inv asegs m1 ->
    evtF asegs RNG (QX gp tp s11 F fc SP FF ZF bl mM) (decA_at gp tp s11 F fc SP FF ZF S bl m1 x1 x5 x6 x7 x11 x14 x16 x17 x28 x29 x30 x31).
  Proof.
    unfold decA_at. intros until x31. intros N5 Hd Hs Hf CZ PL GS MU WM MI.
    pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
    assert (LENB : Z.of_nat (length (map (Z_to_bv 8) bl)) = n) by (rewrite length_map; reflexivity).
    pose proof atop_range as ATR. pose proof ZB as ZBu. unfold AIMG_HI, KLS, KHIGH in ZBu.
    pose proof (rw_cells_bound _ _ _ _ CZ) as ZFB. cbn [cells_size csize Nat.add] in ZFB.
    unfold GSC, GSHC in GS.
    unfold ZCELLS, zcellA in CZ.
    Local Ltac2 Set LiaHints.tbl := fun () => "02d0>10512988003.951077445093.94 10796611846.9112100317787.9112270618323.9612331426020.9513090646977.8013101873376.7013140303554.9313666555668.7215041153336.7415043250697.7515534906502.9115640285071.6615658255133.9315876876809.7315878973758.7216075574774.6016800856201.7016809028512.621703303920.91 1705401081.94 17075871390.7517537992122.8017540089481.8118086011986.9618511472777.7218511472777.9218511472777.9318511472777.9518681669866.6019010590676.9319302163536.8119589975962.9220330914311.7720700320864.63222951252.93  22390832721.9423596256905.6623596676285.6524063222530.9224991237562.7725827528879.6725827530020.6325827660076.8125870727770.9326437422590.9327043595954.9327544385342.9227792411280.7028021048089.6928176076486.9128181601760.7828463086175.6328465183336.7528465183337.7628465183338.8128465183339.8228465183341.6728465183342.7328465183343.7428913119926.9128915217082.7729792256214.7730801439541.7831143794842.723132576390.91 32285357718.6932417836825.9132419933968.9432573021867.673272297910.93 33034670907.9633903789786.9334299049457.923462647984.59 34807508038.91355734914.92  35852192547.9336944756847.9337245531378.8137245661434.6337245665252.6037247908062.8137258295512.613891787750.60 41565867381.7241565867381.7441565867382.9141565867383.7041565867383.7141565867385.6641567964537.9241567964538.8341567964542.7341624359654.7241863133603.9342153485029.9442321050728.5942829974483.8043158952066.9543313548721.6243610559406.7543929283712.9543929283718.9144327231971.9644350553920.7244355972194.814502176483.72 45064778230.6145069446927.5545071674889.6245452174881.9445689441237.7845689441238.7745697359223.6745959234054.7546343394429.9646725515913.7446727612863.7347887142943.7749404231370.8249604477442.7249652760253.8849815480807.9249821399744.8050398796617.8550581696400.9450693103920.8152377759097.9452396529346.7852449451781.925267322392.92 52825090735.595293472389.92 53097216523.9253510313876.675363304390.74 53966538437.7154242975897.8154376156028.8154490019650.9354569436681.8054569827897.7954849128932.9554849128933.9455975063515.9356735579368.9057117873148.8157256654659.9558620089984.9658649831881.785885610055.71 59088058364.8159180274509.9459314873579.6261172658147.9261276787904.6661285877737.7461372096020.9262009686963.6762026611512.6362395333547.9762764509002.8463110050239.7163110384265.7263230379004.8164092089369.6064243778586.9264395266175.6964816762435.9366356652353.6967193953379.9268304808833.727065539866.95 8144176112.93 8147615255.93 8298977940.95 8605669008.63 8861642132.92 00000500G00H00L00M00_00n01=01L01Q01U01Y01Z01]01^01b01f01m02<02K02L02M02Q02U02Y02Z02[02\02]02^02_02d02e02i02j02k03003B03F03J03Y03Z03^03b03f03j04904:04;04>04B04Q04`04a04b04c04d04e04f04g04h04i04j04k04l05005105205305405505905:05>05?05C05D05S05X05]05^05_05`05a05b05c05g05o06706;06C06G06O06W06[06m07207D07E07H07W07Z07[07\07]07o08>08M08R08V08Z08^08_08d08i08n08o09309709;09?09C09R09V09e0:40:80:90::0:;0:>0:?0:@0:A0:B0:F0:G0:K0:L0:P0:Q0:`0:d0:h0;:0;L0;M0;Q0;R0;V0;W0;X0;\0;]0;^0;a0;f0<50<D0<I0<M0<Q0<U0<Y0<]0<a0<b0<c0<g0<h0<l0<m0=20=50=90=>0=?0=D0=E0=JS3ZFBS2SB2ZB3ATR3ZFB2KLSS2KLSS2SB2ZB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS4SEPZ4LENB3ZFBS3ZBuS2KLS2KLFS1HSS2KLS2KLS2NB2N5S2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLSSS2KLS2KLS2KLSSSSSSS3ZBuSS2HBFFS3ZBuS2SB2ZB3ATR3ZFB2KLS2KLS2KLS4SEPZ4LENB3ZFBSS2KLS2KLS2KLS2HBS4SEPZ4LENB3ZFBSSS1HS2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLSSSSSSSSSSSFS2HBFSSSFS2HBSS2HBSS2N5SS4SEPZ4LENB3ZFBS3ZFBS3ZFBFFFFFFS2RBS3E642RBS3E642RBS2RBS3E642RBS2RBS3E642RBS3E642RBS2RBS2SB2ZB3ATR3ZFB2KLS3ZFBS2SB2ZB3ATR3ZFB2KLFS1HS4SEPZ4LENB3ZFBS1HFFFS2SB2ZB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS3ZFBS2N5S2N5S2N5FS3RB0S3RB0S3RB0FS2KLS2KLS2KLS2KLS2KLS4SEPZ4LENB3ZFBS2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2KLSSSS1HSSSSS2KLSS2KLSS2N5SS4SEPZ4LENB3ZFBS2KLS2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLSS2KLSS2KLSFS2N5SSS1HS3ZFBS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS3ZBuS2KLS2KLS2KLS2KLS2KLS2KLSSS2HBSS2KLFS3ZFBS1HS2HBS3ZBuSS3ZBuSS3ZBu".
pose proof (proj2 (buf_nthA m1 S bl 4 (conj PL PLR) ltac:(lia))) as RB.
    pose proof (fhd_decompA _ RB) as DEC.
    destruct DEC as (_ & _ & _ & Hr & E24 & E64).
    rewrite Hf in E24, E64; cbn in E64.
    pose_tabA 3.
    lazymatch type of Hf with _ = ?f => let k := eval vm_compute in (8 + f) in pose_tabA k end.
    repeat (gstepA Hd Hs Hf E64).
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End S.
End CANSEC1.
