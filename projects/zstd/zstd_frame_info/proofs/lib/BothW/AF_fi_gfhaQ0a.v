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
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg ABase RtCells AProto AMalloc_iface AHarness_iface AH_fi_iface AF_fi_kit AF_fi_chk AF_fi_shacc AF_fi_gfhaM.
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
    ov_read_bytes bsegs m1 (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) 1 = Some [Z_to_bv 8 0].
  Proof. intros m1 a MU Ha. eapply zfh_sh_zero; eassumption. Qed.
  #[using="rc SB ZB SEPZ USRC"] Lemma schk : forall m1 a, munch W mM m1 -> S <= a < S + n ->
    exists b, ov_read_bytes bsegs m1 (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) 1 = Some [b]
              /\ (sval b = 0 \/ (0 < sval b <= 7 /\ a mod 8 < sval b)) /\ -128 <= sval b <= 127.
  Proof. intros m1 a MU Ha. eapply src_chk; eassumption. Qed.
  (* [comment removed for export] *)
  Ltac brr := first [if_true | if_false].
  (* [comment removed for export] *)
  #[using="rc ZF bl"] Lemma lxor_m1 : forall x, Z.lxor x (-1) = - x - 1.
  Proof.
    intros x. Local Ltac2 Set LiaHints.tbl := fun () => "0020>10357883337.3157579677303.29000004005S2HiS".
replace (- x - 1) with (Z.lnot x) by (unfold Z.lnot; lia).
    apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.lnot_spec, Z.bits_m1 by lia. reflexivity.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
  Ltac lnot_src := try rewrite (zb_lxor_ones S) by lia; try rewrite (lxor_m1 S).
  (* [comment removed for export] *)
  #[using="rc bl ZA"] Lemma ZA7s : Z.land ZF 7 = 0.
  Proof. change 7 with (2^3 - 1). Local Ltac2 Set LiaHints.tbl := fun () => "0010>29782367974.28000001S".
rewrite zb_land_mask by lia. change (2^3) with 8. exact ZA. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
  (* [comment removed for export] *)
  Ltac guard_false :=
    first [ brr
          | let G := fresh "G" in if_cases G; zify_cond G;
            [ exfalso; rewrite ?zb_lxor_ones in G by lia; rewrite ?lxor_m1 in G; rewrite ?ZA7s in G;
              first [ lia | rewrite ?unsigned_lit in G by lia; lia | rewrite ?unsigned_lit_wrap in G; rewrite ?Z.mod_small in G by lia; lia ]
            | clear G ] ].
  (* [comment removed for export] *)
  Ltac zf_genericA :=
    lazymatch goal with
    | CZ : rw_cells _ ?m1 ZF ?cs |- _ =>
        let j := fresh "zj" in let C := fresh "CZ" in
        destruct (rw_cells_forget bsegs m1 ZF cs CZ) as [j C]; clear CZ; cbn [cells_size csize Nat.add] in C;
        apply (rw_cells_split_CB bsegs _ _ [] 48 j [] [24; 4; 20]%nat) in C; [| reflexivity]; cbn [app mk_CB_cells] in C
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
      | PL : bytes_at bsegs m1 S (map (Z_to_bv 8) bl) |- _ =>
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
      lazymatch goal with MIx : mem_inv bsegs m1 |- _ =>
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
          | PL : bytes_at bsegs m1 S (map (Z_to_bv 8) bl) |- _ =>
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
      | 524804 => first [ zf_successA | exit_tailA ]                                 (* [comment removed for export] *)
      | 525120 => zstep; guard_false              (* [comment removed for export] *)
      | 525164 => zstep; lnot_src           (* [comment removed for export] *)
      | 525168 => zstep; guard_false              (* [comment removed for export] *)
      | 525188 => zstep; lnot_src           (* [comment removed for export] *)
      | 525192 => zstep; guard_false              (* [comment removed for export] *)
      | 525216 => zstep; guard_false              (* [comment removed for export] *)
      | 525228 => shload 11; zload            (* [comment removed for export] *)
      | 525236 => chk_branch chkA_8036c          (* [comment removed for export] *)
      | 525252 => shload 13; zload            (* [comment removed for export] *)
      | 525256 => chk_branch chkA_80380          (* [comment removed for export] *)
      | 525316 => zstep; lnot_src           (* [comment removed for export] *)
      | 525320 => zstep; guard_false              (* [comment removed for export] *)
      | 525336 => shload 11; zload            (* [comment removed for export] *)
      | 525340 => chk_branch chkA_803d4          (* [comment removed for export] *)
      | 525356 => zstep; rewrite Hd          (* [comment removed for export] *)
      | 525364 => zstep; lnot_src           (* [comment removed for export] *)
      | 525368 => zstep; guard_false              (* [comment removed for export] *)
      | 525372 => zstep; rewrite Hf          (* [comment removed for export] *)
      | 525388 => zstep; lnot_src           (* [comment removed for export] *)
      | 525392 => zstep; guard_false              (* [comment removed for export] *)
      | 525396 => zstep; rewrite Hs          (* [comment removed for export] *)
      | 525484 => clear_rds; zstep; try change (Z.b2z (0 <? 32)) with 1; try change (Z.b2z (0 <? 0)) with 0        (* [comment removed for export] *)
      | 525488 => zstep; rewrite E64; try change (Z.b2z true) with 1; try change (Z.b2z false) with 0   (* [comment removed for export] *)
      | 525508 => zstep; let K := fresh "KL" in if_cases K; zify_cond K                                 (* [comment removed for export] *)
      | 525520 => zstep; rewrite ZA7s        (* [comment removed for export] *)
      | 525524 => zstep; guard_false              (* [comment removed for export] *)
      | 525540 => shload 10; zload            (* [comment removed for export] *)
      | 525556 => replace (Z_to_bv 64 (4 + S)) with (Z_to_bv 64 (S + 4)) by (f_equal; lia); zstep   (* [comment removed for export] *)
      | 525560 => zstep; guard_false              (* [comment removed for export] *)
      | 525564 => zstep; guard_false              (* [comment removed for export] *)
      | 525576 => shload 11; zload            (* [comment removed for export] *)
      | 525580 => chk_branch chkA_804c4          (* [comment removed for export] *)
      | 525584 => pload 10 0; pstep; cbv beta; lazymatch goal with RB : 0 <= Znth 4 bl < 256 |- _ => rewrite (byte_litA _ RB) end   (* [comment removed for export] *)
      | 525592 => zstep; let K := fresh "KR" in if_cases K; zify_cond K                                 (* [comment removed for export] *)
      | 525596 => zstep; rewrite Hs          (* [comment removed for export] *)
      | 525604 => zstep; lnot_src           (* [comment removed for export] *)
      | 525608 => zstep; guard_false              (* [comment removed for export] *)
      | 525624 => shload 11; zload            (* [comment removed for export] *)
      | 525628 => chk_branch chkA_804f4          (* [comment removed for export] *)
      | 525632 => pload 10 0; pstep; cbv beta; lazymatch goal with RB : 0 <= Znth 5 bl < 256 |- _ => rewrite (byte_litA _ RB) end   (* [comment removed for export] *)
      | 525640 => zstep; let K := fresh "KW" in if_cases K; zify_cond K                                 (* [comment removed for export] *)
      | 525708 => zstep; rewrite ZA7s        (* [comment removed for export] *)
      | 525712 => zstep; guard_false              (* [comment removed for export] *)
      | 525728 => shload 14; zload            (* [comment removed for export] *)
      | 525748 => chk_branch chkA_8056c          (* [comment removed for export] *)
      | 525756 => chk_branch chkA_80574          (* [comment removed for export] *)
      | 525772 => shload 11; zload            (* [comment removed for export] *)
      | 525848 => shload 12; zload            (* [comment removed for export] *)
      | 525872 => zstep; guard_false              (* [comment removed for export] *)
      | 525884 => shload 10; zload            (* [comment removed for export] *)
      | 525888 => chk_branch chkA_805f8          (* [comment removed for export] *)
      | 525904 => shload 11; zload            (* [comment removed for export] *)
      | 525908 => chk_branch chkA_8060c          (* [comment removed for export] *)
      | 525920 => shload 10; zload            (* [comment removed for export] *)
      | 526004 => zstep; rewrite Hd          (* [comment removed for export] *)
      | 526020 => zstep; lnot_src           (* [comment removed for export] *)
      | 526024 => zstep; guard_false              (* [comment removed for export] *)
      | 526040 => shload 12; zload            (* [comment removed for export] *)
      | 526044 => chk_branch chkA_80694          (* [comment removed for export] *)
      | 526048 => pload 10 0; pstep            (* [comment removed for export] *)
      | 526068 => zstep; lnot_src           (* [comment removed for export] *)
      | 526072 => zstep; guard_false              (* [comment removed for export] *)
      | 526088 => shload 12; zload            (* [comment removed for export] *)
      | 526092 => chk_branch chkA_806c4          (* [comment removed for export] *)
      | 526108 => shload 16; zload            (* [comment removed for export] *)
      | 526112 => chk_branch chkA_806d8          (* [comment removed for export] *)
      | 526116 => pload 10 1; pstep            (* [comment removed for export] *)
      | 526120 => pload 10 0; pstep            (* [comment removed for export] *)
      | 526148 => zstep; lnot_src           (* [comment removed for export] *)
      | 526152 => zstep; guard_false              (* [comment removed for export] *)
      | 526168 => shload 12; zload            (* [comment removed for export] *)
      | 526172 => chk_branch chkA_80714          (* [comment removed for export] *)
      | 526188 => shload 16; zload            (* [comment removed for export] *)
      | 526192 => chk_branch chkA_80728          (* [comment removed for export] *)
      | 526196 => pload 10 1; pstep            (* [comment removed for export] *)
      | 526200 => pload 10 0; pstep            (* [comment removed for export] *)
      | 526204 => pload 10 2; pstep            (* [comment removed for export] *)
      | 526208 => pload 10 3; pstep            (* [comment removed for export] *)
      | 526240 => zstep; rewrite Hf          (* [comment removed for export] *)
      | 526280 => zstep; lnot_src           (* [comment removed for export] *)
      | 526284 => zstep; guard_false              (* [comment removed for export] *)
      | 526300 => shload 12; zload            (* [comment removed for export] *)
      | 526304 => chk_branch chkA_80798          (* [comment removed for export] *)
      | 526320 => shload 14; zload            (* [comment removed for export] *)
      | 526324 => chk_branch chkA_807ac          (* [comment removed for export] *)
      | 526328 => pload 10 1; pstep            (* [comment removed for export] *)
      | 526332 => pload 10 0; pstep            (* [comment removed for export] *)
      | 526336 => pload 10 2; pstep            (* [comment removed for export] *)
      | 526340 => pload 10 3; pstep            (* [comment removed for export] *)
      | 526376 => zstep; lnot_src           (* [comment removed for export] *)
      | 526380 => zstep; guard_false              (* [comment removed for export] *)
      | 526396 => shload 12; zload            (* [comment removed for export] *)
      | 526400 => chk_branch chkA_807f8          (* [comment removed for export] *)
      | 526416 => shload 14; zload            (* [comment removed for export] *)
      | 526420 => chk_branch chkA_8080c          (* [comment removed for export] *)
      | 526424 => pload 10 1; pstep            (* [comment removed for export] *)
      | 526428 => pload 10 0; pstep            (* [comment removed for export] *)
      | 526464 => shload 14; zload            (* [comment removed for export] *)
      | 526484 => shload 10; zload            (* [comment removed for export] *)
      | 526508 => shload 12; zload            (* [comment removed for export] *)
      | 526528 => zstep; let K := fresh "KB" in if_cases K; clear K                                      (* [comment removed for export] *)
      | 526544 => shload 12; zload            (* [comment removed for export] *)
      | 526568 => shload 11; zload            (* [comment removed for export] *)
      | 526592 => shload 10; zload            (* [comment removed for export] *)
      | 526620 => zstep; lnot_src           (* [comment removed for export] *)
      | 526624 => zstep; guard_false              (* [comment removed for export] *)
      | 526640 => shload 12; zload            (* [comment removed for export] *)
      | 526644 => chk_branch chkA_808ec          (* [comment removed for export] *)
      | 526660 => shload 14; zload            (* [comment removed for export] *)
      | 526664 => chk_branch chkA_80900          (* [comment removed for export] *)
      | 526668 => pload 10 1; pstep            (* [comment removed for export] *)
      | 526672 => pload 10 2; pstep            (* [comment removed for export] *)
      | 526676 => pload 10 3; pstep            (* [comment removed for export] *)
      | 526680 => pload 10 0; pstep            (* [comment removed for export] *)
      | 526700 => pload 10 4; pstep            (* [comment removed for export] *)
      | 526704 => pload 10 5; pstep            (* [comment removed for export] *)
      | 526712 => pload 10 6; pstep            (* [comment removed for export] *)
      | 526716 => pload 10 7; pstep            (* [comment removed for export] *)
      | 526764 => zstep; lnot_src           (* [comment removed for export] *)
      | 526768 => zstep; guard_false              (* [comment removed for export] *)
      | 526784 => shload 12; zload            (* [comment removed for export] *)
      | 526788 => chk_branch chkA_8097c          (* [comment removed for export] *)
      | 526792 => pload 10 0; pstep            (* [comment removed for export] *)
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
    Local Ltac2 Set LiaHints.tbl := fun () => "06m0>10349463449.7110512988003.7910512988003.8510512988003.8810512988003.951075347949.80 1075347949.86 1077445093.90 1077445093.94 10796611845.9210796611848.8510796611850.7510796611850.8112100317787.9312100317789.9012270618322.8312270618322.8912270618324.9312270618324.9712331426019.9212331426019.9612331426021.8212331426021.8812712716313.6113090646977.8213101873376.7213140303554.8013140303554.8613140303554.9013140303554.9513156025775.6513283783202.6113666555668.7314274662228.6914763973915.9714854219923.6614854219923.7015041153336.7515041153337.7615043250697.7615043250697.7715534906502.9315534906502.9715534906503.9415640285071.6815658255133.8015658255133.8615658255133.9015658255133.9515876876809.7515876876809.7715878973753.7615878973759.7416075574774.6116800856201.7216802407995.6216809028512.641703303922.81 1703303922.87 1703303922.89 1703303935.78 1703303935.84 1705401081.94 1705401082.91 1705401083.96 17537992122.7717540089481.7818086011987.8318086011987.8918086011989.9318086011989.9718511472777.7318511472777.7618511472777.7918511472777.8018511472777.8118511472777.8218511472777.8518511472777.8618511472777.8718511472777.8818511472777.9018511472777.9118511472777.9318511472777.9518511472777.9618681669866.6119010590676.8019010590676.8619010590676.9019010590676.9519299691007.6919302163537.7719302163539.7519302163549.8119589975962.7619589975962.8219589975962.8619589975962.9319898057825.8419908892480.7420700320864.6521209840128.612211481613.65 222951252.81  222951252.87  222951252.91  222951252.96  22390832720.9122390832720.9522390832722.8122390832722.8722392929881.7222497888913.6923211843423.6923596256905.6823596676285.6723871407050.8624063222530.7624063222530.8224063222530.8624063222530.9324991237562.7925316413697.6125320119744.7425327275745.8425870727770.8025870727770.8625870727770.9025870727770.9526437422590.8026437422590.8626437422590.9026437422590.9526911179445.8026913276297.8127041498809.9427043595952.8727043595966.7727043595966.8327544385341.7927544385341.8527546482485.8927546482486.9427792411280.7228021048089.7128465183332.8028465183333.8128465183334.8228465183336.7628465183337.7728465183338.7828465183339.7928465183341.6528465183342.6928465183343.7528913119924.9928913119926.9328913119926.9728915217082.7929792256214.7930801439541.8031143794842.733132576390.93 3132576390.97 3132576391.94 31502733196.6931502863236.6531502863887.6932285357718.7032417836822.7832417836822.8432417836827.8132417836827.8732417836827.8932419933968.9432419933970.9632419933971.9132573021867.693272297910.80 3272297910.86 3272297910.90 3272297910.95 33034670906.8333034670906.8933034670908.9333034670908.9733197395535.6033903789786.8133903789786.8733903789786.9133903789786.9634299049458.8934299049458.9334299049471.7834299049471.843462647984.61 34807508037.9234807508040.8534807508042.7534807508042.8135212070534.97355734914.76  355734914.82  355734914.86  355734914.93  35852192547.8035852192547.8635852192547.9035852192547.953601076474.62 36255715521.7136861627478.6936944756847.8036944756847.8636944756847.9036944756847.9537245531378.6937245531378.7537245531378.7737245531378.8137245661434.6537245662577.6937245665252.6137247908051.8137247908061.7537247908063.7737258295512.6238190204212.7938192301577.803891787750.61 40190644683.9841565867381.7341565867381.7541565867382.7241565867382.9141565867383.7441565867384.6841565867385.8441565867386.7541565867386.8141567964538.8541567964539.8441567964542.7441626456813.7241863133603.8141863133603.8741863133603.9141863133603.9642153485029.9042153485029.9442155582189.8042155582189.8642321050728.6142709640138.8643158952066.7943158952066.8543158952066.8843158952066.9543313548721.6443608317443.6943929283713.8843929283718.9343929283718.9743929283719.9244327231970.9344327231970.9744327231972.8344327231972.8944350553920.7444355972193.844502176483.73 45064778230.6345069446927.5545071674889.6445450077738.8745450077739.7845450077739.8445452174881.9445689441237.8045689441238.7945697359223.6946343394427.9546725515913.7546725515913.7646727612856.7546727612863.7449404231370.8449604477442.7349652760251.9449652760252.8949652760253.9050398796617.8750579599259.8150579599259.8750581696402.9650581696403.9150693103920.6950693103920.7550693103920.7750693103920.8150818615802.6252375661938.8152375661938.8752377759098.9152377759099.9652447354636.9552447354637.9052449451781.8052449451781.865267322390.78 5267322390.84 5267322395.89 5267322395.93 5293472390.79 5293472390.85 5295569549.94 5295569550.89 53097216523.9353097216523.9453510313877.675363304390.76 53966538437.7254242975896.8254376156028.6954376156028.7554376156028.7754376156028.8154490019650.8154490019650.8754490019650.9154490019650.9654569436681.7954571533627.7854849128931.9254849128931.9654849128932.9154849128932.9554849128933.8254849128933.8854849128934.8154849128934.8755975063511.7755975063511.8355975063513.8755977160656.9456735579368.9257018870422.6257117873148.6957117873148.7557117873148.7757117873148.815734777466.62 58393424463.6158620089985.8358620089985.8958620089991.9358620089991.9758649831881.8058821900441.615885610054.72 59088058364.6959088058364.7559088058364.7759088058364.8159178177350.8759178177351.7859178177351.8459180274509.9459314873579.6359314988138.6259314988138.6659314988138.7061172658147.7661172658147.8261172658147.8661172658147.9361276787904.6861285877737.7661372096020.7661372096020.8261372096020.8661372096020.9361598176679.6162009686963.6962026611512.6562395333547.9662764509002.8663110050239.7363110384265.7463230379004.6963230379004.7563230379004.7763230379004.8164022589078.6264092089369.6164243778586.7664243778586.8264243778586.8664243778586.9364295209551.7464297306693.8264301028607.6264302930276.6564302931183.6964395266175.7064402063724.7564402194671.6964402195812.6564431430668.8164431560708.6564431562127.6964981188865.7166232013900.7766232143940.6566232145359.6966356652353.7167193953379.7667193953379.8267193953379.8667193953379.9367255412633.7168304808833.747065539866.79 7065539866.85 7065539866.88 7065539866.95 7442789529.61 8144176112.80 8144176112.86 8144176112.90 8144176112.95 8147615255.80 8147615255.86 8147615255.90 8147615255.95 8298977940.79 8298977940.85 8298977940.88 8298977940.95 8605669008.65 8861642132.76 8861642132.82 8861642132.86 8861642132.93 00000400900>00C00H00Z00l01>01P01Q01R01S01T01X01\01]01^01_01`02202D02V02h02i03803G03V03e04404C04D04E04J04K04O04^04m05105505905=05>05?05@05C05D05E05F05G05K05O05S05W05^05m06<06K06L06M06N06O06P06Q06R06S06W06[06\06]06^06_06`06a06b06c06d06e06f06g06h06i06j06k06l06m06n06o07407907>07C07D07E07F07G07K07O07S07W07f08508608708808=08B08G08L08^09009B09T09f09g09h09l0:00:40:C0:R0:a0;00;10;20;A0;P0;T0;X0;\0;`0;o0<>0<M0<\0<`0<d0<e0<f0<g0<h0<i0<j0<k0<l0<o0=30=40=50=60=70=80=90=:0=;0=<0==0=>0=?0=@0=A0=B0=C0=G0=H0=I0=J0=N0=R0=V0=W0=X0=Y0=Z0=[0=\0=]0=^0=_0=`0=d0=h0=l0>00>10>20>30>40>50>90>=0>A0>E0>F0>G0>H0>I0>M0>N0>O0>P0>Q0>R0>a0?00??0?N0?S0?X0?]0?b0?c0?d0?e0?j0?o0@40@90@:0@;0@<0@=0@>0@?0@@0@A0@B0@C0@D0@H0@L0@M0@Q0@U0@Y0@]0@a0@e0@i0@m0A10A50A90A=0AA0AS0AX0A]0Ab0Ag0B90BK0B]0Bo0C00C40CC0CR0Ca0D00D30D40D50D60D70D80DJ0D\0Dn0E@0EO0E^0Ec0Eg0Ek0Eo0F00F10F20F30F80F=0FB0FF0FJ0FN0FR0FV0FZ0Fi0Fm0G10G50G90G:0G;0G<0G=0G>0G?0G@0GA0GB0GC0GD0GE0GF0GG0GH0GI0GJ0GK0GL0GM0GN0GO0GP0GQ0GR0GV0GZ0G[0G_0G`0Gd0Ge0Gf0Gg0Gh0H70HF0HU0Hd0Hh0Hl0I>0IP0Ib0J40JF0JX0Jj0K<0K=0K>0K?0K@0KD0KE0KF0KG0KH0KI0KJ0KK0KL0KM0KN0KO0KP0KQ0KU0KV0KW0KX0KY0KZ0K[0K\0K]0K`0Kf0L70LH0LM0LR0LW0L\0Lk0M:0M?0MD0MI0MN0MO0MS0MW0M[0M_0Mc0Mg0Mh0Mi0Mj0Mk0Ml0Mm0N10N50N90N=0NL0N[0Nm0O<0OK0OL0OP0OT0OX0O\0O`0Od0Oe0Oi0Om0P10P20P70P<0PA0PF0PJ0PM0PQ0PU0PY0P]0P^0Pc0Ph0Pm0Q20Q30Q40Q50Q60Q;0Q@0QE0QJ0QK0QP0QU0QZ0Q_S2KLS3ZFBS3ZFBS3ZFBS3ZFBS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLSSSSS2KLS2KLSSSSS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLSS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBFSS3ZBuFS2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2KLS2KLS2KLS2KLFFFS1HSSSSS2KLS2KLS2KLS2KLS2NB2N5S2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLSSSSSSSSS2KLS2KLSSSSSSSSSSSSSSSSSSSSS3ZBuS3ZBuS3ZBuS3ZBuSSSSS2HBS2HBS2HBS2HBS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLFFFS3ZBuS3ZBuS3ZBuS3ZBuS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLFFS2KLS2KLS2KLS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBSFS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2HBS2HBS2HBS2HBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS2KLS2KLSSSSSSSSS1HS2KLSSSSSSSSSSSSSSSFS2HBFFFS2KLS2KLS2KLSSSSSSSSSFS2HBS2HBS2HBS2HBSSSSSS2HBS2HBS2HBS2HBSSSSS2N5SSSSFS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS3ZFBS3ZFBS3ZFBS3ZFBFFFS3ZFBS3ZFBS3ZFBS3ZFBFFFFFFFFFFFS2KLS2KLFS2KLS2RBS2RBS2RBS2RBS2RBS2RBS2RBS2RBS2RBS2RBS2RBS2RBS2SB2ZB3ATR3ZFB2KLS3ZFBS3ZFBS3ZFBS3ZFBS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLFS2KLS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS1HFFFFFS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS3ZFBS2N5S2N5S2N5FFFFS3RB1S3RB1S3RB1S2KLS2KLS2KLS2KLS2KLS2KLS4SEPZ4LENB3ZFBS2KLS2KLS2KLS2KLSSSSSSSSFSSSSSSSSSSSSSSSSS2KLS2KLSS2KLSS2N5SSSSS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS2KLS2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLSSSSS2KLFSSSSFFSSSSFSS2N5SSSSSSSSS1HS2SB1GS2SB3ATR3ZFB2KL1GS2SB3ATR3ZFB2KL1GS3ZFBS3ZFBS3ZFBS3ZFBS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS3ZBuS3ZBuS3ZBuS3ZBuFS2KLS2KLS2KLS2KLS2KLS2KLSSSSFSS2HBS2HBS2HBS2HBS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLSS2KLS2KLS2KLS2KLS2KLS2KLFS2KLS2KLS2KLFS3ZFBS3ZFBS3ZFBS3ZFBS2KLS1HS2HBS2HBS2HBS2HBSS3ZBuS3ZBuS3ZBuS3ZBuSSSSS3ZBuS3ZBuS3ZBuS3ZBuSS3ZBuS3ZBuS3ZBuS3ZBu".
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
