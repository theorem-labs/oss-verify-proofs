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
  #[using="rc PLR NB SB ZA ZB SEPZ USRC UZF RS RSS RZ RSZ RI RIS"] Lemma decB1a : dec_okB gp tp s11 F fc SP FF ZF S bl mM RNG 1 0.
  Proof.
    unfold dec_okB, decA_at. intros until x31. intros N5 Hd Hs CZ PL GS MU WM MI.
    pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
    assert (LENB : Z.of_nat (length (map (Z_to_bv 8) bl)) = n) by (rewrite length_map; reflexivity).
    pose proof atop_range as ATR. pose proof ZB as ZBu. unfold AIMG_HI, KLS, KHIGH in ZBu.
    pose proof (rw_cells_bound _ _ _ _ CZ) as ZFB. cbn [cells_size csize Nat.add] in ZFB.
    unfold GSC, GSHC in GS.
    unfold ZCELLS, zcellA in CZ.
    Local Ltac2 Set LiaHints.tbl := fun () => "07<0?10348052248.72 10512988003.10010512988003.86 10512988003.92 10512988003.95 1077445091.95  1077445091.99  1077445093.85  1077445093.91  10796611846.82 10796611846.88 10798709005.97 10798709006.92 12100317787.94 12270618323.87 12270618323.93 12270618325.10112270618325.97 12331426018.10012331426018.96 12331426020.86 12331426020.92 12712716313.61 13049834364.78 13049965311.69 13049966452.65 13090646977.82 13101873376.72 13140303554.84 13140303554.90 13140303554.94 13140303554.99 13156025775.65 13283783202.61 13666555668.73 14274662228.69 14763973912.10014854219923.66 14854219923.70 14854219923.73 15041153336.77 15041153337.78 15043250697.78 15043250697.79 15534906501.10115534906501.97 15534906502.98 15640285071.68 15658255133.84 15658255133.90 15658255133.94 15658255133.99 15876876809.72 15877476798.71 15986727343.72 16075574774.61 16800856201.72 16802407995.62 16809028512.64 1703303920.82  1703303920.88  1705401081.85  1705401081.91  1705401081.93  1705401082.98  1705401083.95  1705401084.100 17077626520.74 17537992121.78 17537992122.79 17540089481.79 17540089481.80 17797826708.65 17797827871.69 17797958812.72 18086011986.87 18086011986.93 18086011988.10118086011988.97 18466260674.91 18511472777.10018511472777.73 18511472777.83 18511472777.84 18511472777.86 18511472777.89 18511472777.90 18511472777.92 18511472777.93 18511472777.94 18511472777.95 18511472777.98 18511472777.99 18589810882.91 18681669866.61 19010590676.84 19010590676.90 19010590676.94 19010590676.99 19302163536.80 19302163538.78 19302163540.72 19304258774.84 19589975962.83 19589975962.89 19589975962.93 19589975962.98 19898057824.86 19908892480.75 20700320864.65 21209840128.61 2211481613.65  222951252.84   222951252.90   222951252.94   222951252.99   22390832721.85 22390832721.91 22390832727.95 22390832727.99 22392929881.72 22495938362.72 23214346996.72 23596256905.68 23596676285.67 24063222530.83 24063222530.89 24063222530.93 24063222530.98 24991237562.79 25231539789.72 25316413697.61 25870727770.84 25870727770.90 25870727770.94 25870727770.99 26437422590.84 26437422590.90 26437422590.94 26437422590.99 26911179445.82 26913276297.83 27041498810.94 27041498811.99 27043595954.84 27043595954.90 27544385342.83 27544385342.89 27546482486.93 27546482487.98 27792411280.72 28176076480.88 28181601760.77 28458877677.85 28465183332.82 28465183333.83 28465183334.84 28465183336.78 28465183337.79 28465183338.80 28465183339.81 28465183341.65 28465183342.69 28465183343.73 28913119925.10128913119925.97 28915217082.79 29792256214.79 30801439541.80 31143794842.73 31150540312.74 3132576389.101 3132576389.97  3132576390.98  32285357718.70 32417836825.82 32417836825.88 32419933968.85 32419933968.91 32419933968.93 32419933970.95 32419933971.98 32419933973.10032573021867.69 3272297910.84  3272297910.90  3272297910.94  3272297910.99  33034670907.87 33034670907.93 33034670909.10133034670909.97 33903789786.84 33903789786.90 33903789786.94 33903789786.99 34296952314.94 34296952314.98 34299049457.83 34299049457.89 3462647984.61  34805410893.97 34805410894.92 34807508038.82 34807508038.88 35212070533.10135499667119.60 355734914.83   355734914.89   355734914.93   355734914.98   35852192547.84 35852192547.90 35852192547.94 35852192547.99 3601076474.62  36861627478.69 36944756847.84 36944756847.90 36944756847.94 36944756847.99 37245531378.72 37245531378.78 37245531378.80 37245531378.84 37245661434.65 37245665252.61 37247908058.72 37247908060.78 37247908062.80 37258295512.62 37258379352.84 37582835292.80 37582965332.65 37582966751.69 38190204212.81 38192301577.82 3891787750.61  39971308224.88 39977226720.77 40190644680.10141565867381.73 41565867381.75 41565867381.91 41565867382.72 41565867382.82 41565867382.88 41565867383.74 41565867384.68 41567964538.85 41567964539.87 41567964542.74 41567964542.96 41626456813.72 41863133603.84 41863133603.90 41863133603.94 41863133603.99 42153485027.95 42153485027.99 42153485029.85 42153485029.91 42321050728.61 42707542977.88 43158952066.10043158952066.86 43158952066.92 43158952066.95 43313548721.64 43608317443.69 43610559400.72 43929283712.92 43929283717.10143929283717.97 43929283718.96 44327231969.10144327231969.97 44327231971.87 44327231971.93 4502176483.73  45064778230.63 45069446927.55 45071674889.64 45452174880.94 45452174881.85 45452174881.91 45452174887.99 45689441237.80 45689441238.79 45697359223.69 45957560832.74 46343394424.97 46343394424.98 46724821560.76 46725515913.77 49404231370.84 49604477442.73 49652760248.90 50050174752.77 50056190976.88 50398796617.87 50581696400.85 50581696400.91 50581696402.95 50581696405.10050693103920.72 50693103920.78 50693103920.80 50693103920.84 50818615802.62 52377759097.85 52377759097.91 52377759099.95 52377759100.10052396529346.77 52447354636.98 52447354637.93 52449451781.83 52449451781.89 5265225235.94  5265225235.98  5267322392.83  5267322392.89  5293472389.83  5293472389.89  5295569548.98  5295569549.93  53097216520.97 53097216522.94 53510313877.67 5363304390.76  53966538437.72 54242975896.82 54376156028.72 54376156028.78 54376156028.80 54376156028.84 54490019650.84 54490019650.90 54490019650.94 54490019650.99 54569436681.81 54571533627.80 54849128930.10054849128930.96 54849128931.95 54849128931.99 54849128932.86 54849128932.92 54849128933.85 54849128933.91 55975063515.84 55975063515.90 55977160658.99 55977160659.94 56213944120.10256735579368.98 56735579370.94 56735579373.93 57117873148.72 57117873148.78 57117873148.80 57117873148.84 5734777466.62  58393424463.61 58620089984.87 58620089984.93 58620089990.10158620089990.97 58649831881.80 58821900441.61 5885610054.72  59088058364.72 59088058364.78 59088058364.80 59088058364.84 59180274507.99 59180274508.94 59180274509.85 59180274509.91 59314873579.63 59314988138.62 59314988138.66 59314988138.70 59314988138.73 61172658147.83 61172658147.89 61172658147.93 61172658147.98 61264202057.69 61276787904.68 61285877737.76 61372096020.83 61372096020.89 61372096020.93 61372096020.98 61401418176.74 61598176679.61 6177293336.74  62009686963.69 62026611512.65 62395333544.99 63108286904.77 63108286906.79 63110384265.78 63110384265.80 63230379004.72 63230379004.78 63230379004.80 63230379004.84 64022589078.62 64092089369.61 64243778586.83 64243778586.89 64243778586.93 64243778586.98 64295209551.74 64297306692.86 64297306694.81 64301028607.62 64302930276.65 64302931183.69 64305402180.72 64324655132.84 64324786591.69 64324787220.65 64395266175.70 64816762434.91 64978467200.72 65280396538.62 67193953379.83 67193953379.89 67193953379.93 67193953379.98 68304808833.75 7065539866.100 7065539866.86  7065539866.92  7065539866.95  7093271040.74  7442789529.61  8144176112.84  8144176112.90  8144176112.94  8144176112.99  8147615255.84  8147615255.90  8147615255.94  8147615255.99  8298977940.100 8298977940.86  8298977940.92  8298977940.95  8605669008.65  8861642132.83  8861642132.89  8861642132.93  8861642132.98  8984330550.83  8986427913.84  00000400900>00C00H00Z00l01>01P01Q01R01S01T01X01Y01Z01[01\01n02@02R02d02e02i02m03103@03O03^03m04<04K04L04M04R04S04W04f05505D05H05L05P05T05U05V05W05Z05[05\05]05^05b05f05g05n06=06L06[06\06]06^06_06`06a06b06c06g06k06o07307707;07?07C07D07E07F07G07K07L07M07N07O07P07Q07R07S07T07U07V07W07X07\07]07b07g07l08108208308408508908=08A08E08T08c08d08e08f08k09009509:09L09^0:00:B0:T0:U0:V0:Z0:^0:m0;<0;K0;Z0;[0;\0;]0;a0;e0;i0;m0<<0<K0<Z0<i0<m0=10=20=30=40=50=60=70=80=90=<0=K0=Z0=[0=\0=]0=^0=_0=`0=a0=b0=c0=d0=e0=f0=g0=h0=i0=j0=n0>20>30>40>50>60>70>80>90>:0>;0><0>=0>>0>?0>C0>G0>K0>O0>P0>Q0>R0>S0>W0>[0>_0>c0>d0>e0>f0>g0>k0>l0>m0>n0>o0?00?10?@0?O0?^0?m0@20@70@<0@A0@B0@C0@H0@M0@R0@W0@X0@Y0@Z0@[0@\0@]0@^0@_0@`0@a0@b0@f0@j0@n0A20A60A70AF0AU0AY0A]0Aa0Ae0Ai0Am0B10B50B90B=0BA0BE0BI0B[0B`0Be0Bj0Bo0CA0CS0Ce0D70D80D<0DK0DZ0Di0E80E;0E<0E=0E>0E?0E@0EA0ES0Ee0F70FI0FN0FR0FV0FZ0F[0F\0F]0F^0Fc0Fh0Fm0Fn0G20G60G:0G>0GB0GQ0GU0Gd0H30H70H80H90H:0H;0H<0H=0H>0H?0H@0HA0HB0HC0HD0HG0HH0HI0HJ0HK0HL0HM0HN0HO0HP0HQ0HR0HS0HW0H[0H\0H`0Ha0He0Hf0Hg0Hh0Hi0I80IG0IV0Ie0Ii0Im0J?0JQ0Jc0K50KG0KY0Kk0L=0L>0L?0L@0LA0LE0LI0LM0LQ0LR0LS0LT0LU0LV0LW0LX0LY0LZ0L[0L\0L]0La0Lb0Lc0Ld0Le0Lf0Lg0Lh0Li0Ll0M20MC0MT0Me0Mj0Mo0N40N90N:0NI0NX0N]0Nb0Ng0Nl0Nm0Nn0O20O60O:0O>0OB0OF0OJ0ON0OO0OP0OQ0OR0OS0OT0OX0O\0O`0Od0P30PB0PQ0Pc0Q20QA0QP0QT0QX0Q\0Q]0Qa0Qb0Qc0Qh0Qm0R20R70R:0R>0RB0RF0RJ0RK0RL0RQ0RV0R[0R`0Ra0Rb0Rc0Rd0Ri0Rn0S30S80S90S>0SC0SH0SM0SQ0SUS2KLS3ZFBS3ZFBS3ZFBS3ZFBS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLSSSSS2KLSSSSS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLSS2KLS2KLS2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBFSS3ZBuFS2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2KLS2KLS2KLS2KLFFFS1HSSSSS2KLS2KLFS2NB2N5S2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLSSSSSSSSS2KLS2KLS2KLS2KLS2KLS2KLS2KLS2KLSSSSS2KLSSSSSSSSSSSSSS2KLSS3ZBuS3ZBuS3ZBuS3ZBuSSSSS2HBS2HBS2HBS2HBS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLFFFS3ZBuS3ZBuS3ZBuS3ZBuS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLFFS2KLS2KLS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBSFFS2HBS2HBS2HBS2HBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS2KLS2KLSSSSSSSSS1HS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLSSSSSSSSSSSSSSSFS2HBS2KLFFFSSSSSSSSSFS2HBS2HBS2HBS2HBSSSSS2HBS2HBS2HBS2HBSSSSS2N5SSSSFSS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS3ZFBS3ZFBS3ZFBS3ZFBFFS3ZFBS3ZFBS3ZFBS3ZFBFFFFFFFFFFFS2KLS2KLS2KLS2KLS2KLFS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2KLS2RBS2RBS2RBS2RBS2RBS2RBS2RBS2RBS2RBS2RBS2RBS2RBS2SB2ZB3ATR3ZFB2KLS3ZFBS3ZFBS3ZFBS3ZFBS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLFS2KLS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS1HFFFFFFS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS3ZFBS2N5S2N5S2N5FFFFS3RB1S3RB1S3RB1FS2KLS2KLS2KLS2KLS2KLS4SEPZ4LENB3ZFBS2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2KLSSSSSSSSFSSSSS1HSSSSSSSSSSSSS2KLS2KLSS2KLSS2N5SSSSS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS2KLS2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLSSSSS2KLS2KLS2KLS2KLSSSSFFSSSSFSS2N5SSSSSSSSS1HS2SB1GS2SB3ATR3ZFB2KL1GS2SB3ATR3ZFB2KL1GS2SB3ATR3ZFB2KL1GS3ZFBS3ZFBS3ZFBS3ZFBFS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS3ZBuS3ZBuS3ZBuS3ZBuFFS2KLS2KLS2KLS2KLS2KLS2KLS2KLS2KLSSSSFSS2HBS2HBS2HBS2HBS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2KLS2KLS2KLSS2KLFFS3ZFBS3ZFBS3ZFBS3ZFBS1HS2HBS2HBS2HBS2HBFSS3ZBuS3ZBuS3ZBuS3ZBuSSSSS3ZBuS3ZBuS3ZBuS3ZBuSS3ZBuS3ZBuS3ZBuS3ZBuS2KLS2KL".
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
