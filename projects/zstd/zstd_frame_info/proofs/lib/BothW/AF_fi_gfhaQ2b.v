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
  #[using="rc PLR NB SB ZA ZB SEPZ USRC UZF RS RSS RZ RSZ RI RIS"] Lemma decB2b : dec_okB gp tp s11 F fc SP FF ZF S bl mM RNG 2 32.
  Proof.
    unfold dec_okB, decA_at. intros until x31. intros N5 Hd Hs CZ PL GS MU WM MI.
    pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
    assert (LENB : Z.of_nat (length (map (Z_to_bv 8) bl)) = n) by (rewrite length_map; reflexivity).
    pose proof atop_range as ATR. pose proof ZB as ZBu. unfold AIMG_HI, KLS, KHIGH in ZBu.
    pose proof (rw_cells_bound _ _ _ _ CZ) as ZFB. cbn [cells_size csize Nat.add] in ZFB.
    unfold GSC, GSHC in GS.
    unfold ZCELLS, zcellA in CZ.
    Local Ltac2 Set LiaHints.tbl := fun () => "0700?10348052248.71 10512988003.88 10512988003.91 10512988003.94 10512988003.99 1077445091.94  1077445091.98  1077445093.87  1077445093.90  10796611846.84 10796611846.87 10798709005.96 10798709006.91 12100317784.94 12270618323.89 12270618323.92 12270618325.10012270618325.96 12331426018.95 12331426018.99 12331426020.88 12331426020.91 12712716313.61 13049834364.77 13049966452.65 13092744137.78 13101873376.70 13140303554.86 13140303554.89 13140303554.93 13140303554.98 13156025775.65 13283783202.61 13666555668.73 14763973914.97 14854219923.66 14854219923.72 15041153336.76 15041153337.77 15043250697.77 15043250697.78 15534906496.95 15534906503.94 15534906503.98 15640285071.68 15658255133.86 15658255133.89 15658255133.93 15658255133.98 15876876809.70 15877476798.69 15986727343.71 16075574774.61 16800856201.72 16802407995.62 16809028512.64 1703303920.84  1703303920.87  1705401081.87  1705401081.90  1705401081.92  1705401082.97  1705401083.94  1705401084.99  17077626520.73 17537992121.77 17537992122.78 17540089481.78 17540089481.79 18086011986.89 18086011986.92 18086011988.10018086011988.96 18464163529.87 18511472777.73 18511472777.85 18511472777.86 18511472777.88 18511472777.89 18511472777.91 18511472777.92 18511472777.93 18511472777.94 18511472777.97 18511472777.98 18511472777.99 18591908041.87 18681669866.61 19010590676.86 19010590676.89 19010590676.93 19010590676.98 19302163536.79 19302163538.77 19302163539.74 19304258774.83 19589975962.85 19589975962.88 19589975962.92 19589975962.97 19898057825.84 19908892480.74 20700320864.65 21209840128.61 2211481613.65  222951252.86   222951252.89   222951252.93   222951252.98   22390832721.87 22390832721.90 22390832727.94 22390832727.98 22392929881.72 22495938362.71 22497890074.65 23214346996.71 23594159550.70 23596256905.71 24063222530.85 24063222530.88 24063222530.92 24063222530.97 24348577461.67 25231539789.71 25316413697.61 25838294319.60 25870727770.86 25870727770.89 25870727770.93 25870727770.98 26437422590.86 26437422590.89 26437422590.93 26437422590.98 26911179445.81 26913276297.82 27041498810.93 27041498811.98 27043595954.86 27043595954.89 27544385342.85 27544385342.88 27546482486.92 27546482487.97 27792411280.70 28176076481.86 28181601760.76 28458877677.84 28465183332.81 28465183333.82 28465183334.83 28465183336.75 28465183336.77 28465183337.78 28465183338.79 28465183339.80 28465183341.65 28465183342.71 28465183343.72 28913119927.94 28913119927.98 31143794842.73 31150540312.73 3132576384.95  3132576391.94  3132576391.98  32285357718.70 32417836825.84 32417836825.87 32419933968.87 32419933968.90 32419933968.92 32419933970.94 32419933971.97 32419933973.99 32573778434.67 3272297910.86  3272297910.89  3272297910.93  3272297910.98  33034670907.89 33034670907.92 33034670909.10033034670909.96 33903789786.86 33903789786.89 33903789786.93 33903789786.98 34296952314.93 34296952314.97 34299049457.85 34299049457.88 3462647984.61  34805410893.96 34805410894.91 34807508038.84 34807508038.87 35212070535.98 355734914.85   355734914.88   355734914.92   355734914.97   35852192547.86 35852192547.89 35852192547.93 35852192547.98 3601076474.62  36944756847.86 36944756847.89 36944756847.93 36944756847.98 37245531378.74 37245531378.77 37245531378.79 37245531378.83 37245665252.61 37247908058.71 37247908060.77 37247908061.74 37247908062.79 37258295512.62 37258379352.83 37582835292.79 37582965332.65 38190204212.80 38192301577.81 3891787750.61  39971308225.86 39977226720.76 40190644682.98 41565867381.73 41565867381.75 41565867381.76 41565867381.90 41565867382.72 41565867382.84 41565867382.87 41565867383.74 41565867384.68 41567964540.85 41567964542.74 41567964542.95 41626456813.72 41863133603.86 41863133603.89 41863133603.93 41863133603.98 42153485027.94 42153485027.98 42153485029.87 42153485029.90 42321050728.61 42709640136.84 43158952066.88 43158952066.91 43158952066.94 43158952066.99 43313548721.64 43610559400.71 43927186569.82 43927186569.88 43929283712.93 43929283719.94 43929283719.98 44327231969.10044327231969.96 44327231971.89 44327231971.92 4502176483.73  45064778230.63 45069446927.55 45071674889.64 45452174880.93 45452174881.87 45452174881.90 45452174887.98 45957560832.73 46343394426.94 46343394426.95 46724821560.75 46725515913.76 49404231367.79 49604477442.73 49652760249.89 50050174752.76 50056190977.86 50400893767.82 50581696400.87 50581696400.90 50581696402.94 50581696405.99 50693103920.74 50693103920.77 50693103920.79 50693103920.83 50818615802.62 51362258224.83 51364357556.77 52377759097.87 52377759097.90 52377759099.94 52377759100.99 52396529346.76 52447354636.97 52447354637.92 52449451781.85 52449451781.88 5265225235.93  5265225235.97  5267322392.85  5267322392.88  5293472389.85  5293472389.88  5295569548.97  5295569549.92  53097216522.94 53097216527.90 53510313877.67 5363304391.77  53966538437.72 54242975896.82 54376156028.74 54376156028.77 54376156028.79 54376156028.83 54490019650.86 54490019650.89 54490019650.93 54490019650.98 54569436681.80 54571533627.79 54849128930.95 54849128930.99 54849128931.94 54849128931.98 54849128932.88 54849128932.91 54849128933.87 54849128933.90 55975063515.86 55975063515.89 55977160658.98 55977160659.93 56213944122.99 56733482212.89 56735579370.95 56735579371.91 56735579375.90 57117873148.74 57117873148.77 57117873148.79 57117873148.83 5734777466.62  58393424463.61 58620089984.89 58620089984.92 58620089990.10058620089990.96 58821900441.61 5885610054.72  59088058364.74 59088058364.77 59088058364.79 59088058364.83 59180274507.98 59180274508.93 59180274509.87 59180274509.90 59314873579.63 59314988138.62 59314988138.66 59314988138.72 61172658147.85 61172658147.88 61172658147.92 61172658147.97 61276787904.68 61283780578.77 61372096020.85 61372096020.88 61372096020.92 61372096020.97 61401418176.73 61598176679.61 6177293336.73  62010429210.67 62026611512.65 62395333546.96 63108286904.76 63108286906.78 63110050239.73 63110384265.74 63110384265.77 63110384265.79 63230379004.74 63230379004.77 63230379004.79 63230379004.83 64022589078.62 64092089369.61 64243778586.85 64243778586.88 64243778586.92 64243778586.97 64295209549.82 64295209551.74 64301028607.62 64302930276.65 64305402180.71 64324655132.83 64324787220.65 64395266175.70 64402063724.74 64402195812.65 64814665289.87 64978467200.71 67193953379.85 67193953379.88 67193953379.92 67193953379.97 67415031418.62 68304808833.74 7065539866.88  7065539866.91  7065539866.94  7065539866.99  7093271040.73  7442789529.61  8144176112.86  8144176112.89  8144176112.93  8144176112.98  8147615255.86  8147615255.89  8147615255.93  8147615255.98  8298977940.88  8298977940.91  8298977940.94  8298977940.99  8605669008.65  8861642132.85  8861642132.88  8861642132.92  8861642132.97  8984330550.82  8986427913.83  00000400900>00C00H00Z00l01>01P01Q01R01S01T01X01Y01Z01[01\01n02@02R02d02e02i02m03<03K03Z03i04804G04H04I04N04R04a05005405805<05@05A05B05C05F05G05H05I05J05N05R05S05Z05i06806G06H06I06J06K06L06M06N06O06S06W06[06_06c06d06e06f06g06k06l06m06n06o07007107207307407507607707;07<07A07F07K07P07Q07R07S07T07X07\07`07d08308B08C08D08E08J08O08T08Y08k09=09O09a0:30:40:50:60::0:>0:M0:\0:k0;:0;;0;<0;=0;>0;B0;F0;J0;N0;]0;l0<;0<J0<N0<R0<S0<T0<U0<V0<W0<X0<Y0<Z0<]0<l0=;0=<0==0=>0=?0=@0=A0=B0=C0=D0=E0=F0=G0=H0=I0=M0=Q0=R0=S0=T0=U0=V0=W0=X0=Y0=Z0=[0=\0=]0=^0=b0=f0=j0=n0=o0>00>10>20>60>:0>>0>B0>C0>D0>E0>F0>J0>K0>L0>M0>N0>O0>^0>m0?<0?K0?P0?U0?Z0?_0?`0?e0?j0?o0@40@50@60@70@80@90@:0@;0@<0@=0@>0@?0@C0@G0@K0@O0@P0@_0@n0A20A60A:0A>0AB0AF0AJ0AN0AR0AV0AZ0A^0Ab0B40B90B>0BC0BH0BZ0Bl0C>0CP0CQ0CU0Cd0D30DB0DQ0DT0DU0DV0DW0DX0DY0DZ0Dl0E>0EP0Eb0Eg0Ek0Eo0F30F40F50F60F70F80F<0F@0FD0FH0FL0F[0F_0Fn0G=0GA0GB0GC0GD0GE0GF0GG0GH0GI0GJ0GK0GL0GM0GN0GO0GP0GS0GT0GU0GV0GW0GX0GY0GZ0G[0G\0G]0G^0G_0Gc0Gg0Gh0Gl0Gm0H10H20H30H40H50HD0HS0Hb0I10I50I90IK0I]0Io0JA0JS0Je0K70KI0KJ0KK0KL0KM0KQ0KU0KY0K]0Ka0Kb0Kc0Kd0Ke0Kf0Kg0Kh0Ki0Kj0Kk0Kl0L00L10L20L30L40L50L60L70L80L;0LA0LR0Lc0Lh0Lm0M20M70MF0MU0MZ0M_0Md0Mi0Mj0Mk0Mo0N30N70N;0N?0NC0NG0NK0NO0NS0NT0NU0NV0NW0NX0NY0N]0Na0Ne0Ni0O80OG0OY0Oh0P70P;0P?0P@0PD0PH0PL0PM0PR0PW0P\0Pa0Pb0Pe0Pi0Pm0Q10Q50Q60Q70Q<0QA0QF0QK0QL0QM0QN0QO0QT0QY0Q^0Qc0Qd0Qi0Qn0R30R80R<0R@S2KLS3ZFBS3ZFBS3ZFBS3ZFBS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLSSSSS2KLSSSSS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLSS2KLS2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBFSS3ZBuS2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2KLS2KLS2KLS2KLFFFS1HSSSSS2KLS2KLFS2NB2N5S2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLSSSSSSSSS2KLS2KLS2KLS2KLS2KLSSSSS2KLSSSSSSSSSSSSS2KLSS3ZBuS3ZBuS3ZBuS3ZBuSSSSS2HBS2HBS2HBS2HBS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLFFFS3ZBuS3ZBuS3ZBuS3ZBuS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLFFFS2KLS2KLS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBSFFSS2HBS2HBS2HBS2HBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS2KLS2KLSSSSSSSSS1HS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLSSSSSSSSSSSSSSS2HBS2KLFFFSSSSSSSSSFS2HBS2HBS2HBS2HBSSSSS2HBS2HBS2HBS2HBSSSSS2N5SSSSFS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS3ZFBS3ZFBS3ZFBS3ZFBFS3ZFBS3ZFBS3ZFBS3ZFBFFFFFFFFFFFS2KLS2KLS2KLS2KLFS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2KLS2RBS2RBS2RBS2RBS2RBS2RBS2RBS2RBS2RBS2RBS2RBS2RBS2SB2ZB3ATR3ZFB2KLS3ZFBS3ZFBS3ZFBS3ZFBS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLFS2KLS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS1HFFFFFFS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS3ZFBS2N5S2N5S2N5FFFFFS2KLS2KLS2KLS2KLS2KLS4SEPZ4LENB3ZFBS2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2KLSSSSSSSSFFFSSSSS1HSSSSSSSSSSSSS2KLS2KLSS2KLSS2N5SSSSS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS4SEPZ4LENB3ZFBS2KLS2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLSSSSS2KLS2KLS2KLS2KLS2KLSSSSFFSSSSSS2N5SSSSSSSSS1HS2SB1GS2SB3ATR3ZFB2KL1GS2SB3ATR3ZFB2KL1GS3ZFBS3ZFBS3ZFBS3ZFBS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS3ZBuS3ZBuS3ZBuS3ZBuFFS2KLS2KLS2KLS2KLS2KLS2KLS2KLS2KLS2KLS2KLSSSSFSS2HBS2HBS2HBS2HBS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2KLS2KLSS2KLS2KLS2KLFS3ZFBS3ZFBS3ZFBS3ZFBFS1HS2HBS2HBS2HBS2HBFSS3ZBuS3ZBuS3ZBuS3ZBuSSSSS3ZBuS3ZBuS3ZBuS3ZBuSS3ZBuS3ZBuS3ZBuS3ZBuS2KLS2KL".
pose proof (proj2 (buf_nthA m1 S bl 4 (conj PL PLR) ltac:(lia))) as RB.
    pose proof (fhd_decompA _ RB) as DEC.
    destruct DEC as (_ & Hf & _ & Hr & E24 & E64).
    destruct Hf as [Hf|[Hf|[Hf|Hf]]]; (rewrite Hf in E24, E64; cbn in E64).
    all: pose_tabA 2.
    all: lazymatch type of Hf with _ = ?f => let k := eval vm_compute in (8 + f) in pose_tabA k end.
    all: repeat (gstepA Hd Hs Hf E64).
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End S.
End CANSEC1.
