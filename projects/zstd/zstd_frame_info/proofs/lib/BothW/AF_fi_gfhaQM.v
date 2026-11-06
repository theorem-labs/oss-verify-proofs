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
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg ABase RtCells AProto AMalloc_iface AHarness_iface AH_fi_iface AF_fi_kit AF_fi_chk AF_fi_shacc AF_fi_gfhaM AF_fi_gfhaQ0a AF_fi_gfhaQ0b AF_fi_gfhaQ1a AF_fi_gfhaQ1b AF_fi_gfhaQ2a AF_fi_gfhaQ2b AF_fi_gfhaQ3a AF_fi_gfhaQ3b.
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
  #[using="rc PLR NB SB ZA ZB SEPZ USRC UZF RS RSS RZ RSZ RI RIS"] Lemma gfha_mainA : main_okA gp tp s11 F fc SP FF ZF S bl mM RNG.
  Proof.
    unfold main_okA, mainA_at. intros until x31. intros N5 CZ PL GS MU WM MI.
    pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
    assert (LENB : Z.of_nat (length (map (Z_to_bv 8) bl)) = n) by (rewrite length_map; reflexivity).
    pose proof atop_range as ATR. pose proof ZB as ZBu. unfold AIMG_HI, KLS, KHIGH in ZBu.
    pose proof (rw_cells_bound _ _ _ _ CZ) as ZFB. cbn [cells_size csize Nat.add] in ZFB.
    unfold GSC, GSHC in GS.
    apply zcells_of_memset in CZ. unfold ZCELLS, zcellA in CZ.
    zstep. zstep. brr.                            (* [comment removed for export] *)
    zstep. Local Ltac2 Set LiaHints.tbl := fun () => "02Z0>10349462687.7410642097183.6810642750511.6010642751273.6110642751273.6910997198272.6010997198272.6911003117282.6912268521178.8813089779083.7713089779085.8513140303554.7913666555668.8713719612789.7213721985373.6314202097545.6214202097545.7114204193977.7014204193981.6114854219923.6415534906502.8815534906502.9615534906503.7815640285071.6015658255133.9615876876809.7915878973749.781590854844.55 1593100964.64 16075585474.6416081359311.7916798759040.7716798759040.8616802407995.7316809028512.6616809028512.7518086011987.7818511472777.7918511472777.8718511472777.9618681537532.7219010590676.7919299686750.6419898057824.8819908892480.7721207594008.5521209959202.6421920002360.6921921679421.5921922099721.6021922099721.70222951252.87  22390832720.7822390832726.9223596256905.7723596676793.7625826198440.7525826198443.8225870727770.7926437422590.9627041498809.8127546482480.9527792411280.6627792411280.6728458877677.8128463086175.6128465183332.7828465183333.7928465183334.8028465183336.6728465183336.7028465183337.7128465183338.7228465183339.7328465183341.6228465183342.6328465183343.6428913119921.7628913119926.8828913119926.9631143794842.873132576390.88 3132576390.96 3132576391.78 32287454868.893272297910.96 33034670906.7833903789786.8734529317445.8634531414602.723460799640.63 3462647984.72 35852192547.7936944756847.9637245531378.7237245650384.6437246403548.7637247908062.7237331021098.8837331021099.8040185173249.6640187277641.5740488766476.5541624359649.8941863133603.8742153485028.8242321050728.7242322866240.6342591939097.6642594029137.5742707542978.9142829974483.7743313548721.5843929283712.8643929283713.7643929283718.9644327231972.784502176483.87 45069577524.7745071062462.6545071674889.6645071674889.7849599660294.7049601757455.8249604477442.8749652760251.9650183204860.8550183204861.7750398796621.9250692740638.7652396529346.7552447354636.865295569548.78 53964441292.8654242975896.8454242975899.9554376857428.6854490019650.8755157148948.5555158833932.6455977160656.8156735579371.9758622187145.885885610058.87 5887707201.79 59314873579.6559314873579.6659314988138.5659314988138.6459314988138.7361448220169.6361448220169.7261450317114.7161450317118.6261941764855.7261943586527.6363108286902.7963110384265.8064295209550.6564297306693.7664301028607.5664303323492.5864303323492.6764305402180.6364397363325.8964402063724.8064981189127.7468304808833.698144176112.96 8147615255.96 00000800@00H00P00X00g01601E01J01R01Z01l02502602702?02G02O02W02f02g02h02i03003503=03E03M03U03`03a04004?04N04]04l05105605;05@05E05N05S05b06106206306;06C06K06S06\06a06f06n07607>07F07N07`07e07j08108808=08B08G08L08Q08V08[08`08e08j08o09409909>09C09H09P09Q09R09S09X09`09e09m0:50:=0:E0:M0:U0:]0:^0:_0:`0:a0:i0;10;20;30;40;90;A0;F0;G0;H0;P0;X0;`0;g0;n0;o0<00<10<60<>0<F0<N0<V0<^0<f0<n0=@0=H0=P0=X0=`0=e0=l0>10>60>;0>C0>K0>P0>b0>c0>d0>i0?10?60?>0?F0?M0?T0?^0?o0@90@A0@I0@Q0@Y0@Z0@[0@c0@k0A:0AI0AX0Ag0B60BE0BJ0BR0BS0BZ0Bc0BhS3ZFB2K8S2N53ZFBS2N53ZFBS2N53ZFBS2N53ZFBS2SB2N53ATR3ZFBS2SB3ATR3ZFB2K8S2SB2N53ATR3ZFBS3ZFBS2N53ZFBS2N53ZFBS4SEPZ4LENB3ZFB2HBS3ZBu3ZFBFFS2N53ZFBS2N53ZFBS2N53ZFBS2N53ZFBS2SB2N53ATR3ZFBFFFS3ZFB1HS3ZFBS3ZFB2K8S3ZFB2K8S2N53ZFBS2N53ZFBS2NB2N53ZFBFS2SB2N53ATR3ZFBS2SB3ATR3ZFB2K8S2SB3ATR3ZFB2K8S2SB2N53ATR3ZFBS2SB3ATR3ZFB2K8S3ZFBS3ZFBS3ZFBS3ZFBS3ZFBS3ZBu3ZFBS3ZFBS2SB3ATR3ZFB2K8S2SB3ATR3ZFB2K8FFS2N53ZFBS2N53ZFBS2N53ZFBS2N53ZFBS3ZBu3ZFBS3ZFBS3ZFBS3ZFB2K8S3ZFB2K8S2N53ZFBS2N53ZFBS3ZFB2HBS4SEPZ4LENB3ZFB2HBS3ZFBS3ZFBS3ZFB1HS3ZFB1HS3ZFBS3ZFBS3ZFBS3ZFBS3ZFBS3ZFBS3ZFBS3ZFBS3ZFBS3ZFBS3ZFBS3ZFBS3ZFBS3ZFBS3ZFBS3ZFBS3ZFB2HBFFFS3ZFBS3ZFB2HBS3ZFBS3ZFB2HBS2N53ZFBS2N53ZFBS2N53ZFBS2N53ZFBS3ZFB2HBS3ZFB2HBFFFFS2N53ZFBS2N53ZFBFFFS3ZFBS3ZFB2HBS3ZFBFFS2N53ZFBS2N53ZFBS3ZFB2K8S3ZFB1HS3ZFB1HFFFS3ZFBS3ZFB2HBS2N53ZFBS2N53ZFBS2N53ZFBS2N53ZFBS2N53ZFBS2N53ZFBS4SEPZ4LENB3ZFB2HBS3ZFB2K8S2N53ZFBS2N53ZFBS3ZFB2K8S3ZFBS3ZFB1HS3ZFBS3ZFBS3ZFBS2N53ZFBS2N53ZFBS3ZFBS4SEPZ4LENB3ZFB2HBFFS3ZFBS3ZFB2K8S3ZFBS2N53ZFBS2N53ZFBS3ZFB1HS3ZFB1HS2SB3ZFB1GS2SB2N53ATR3ZFB1GS2SB3ZFB1GS2N53ZFBS2N53ZFBS2N53ZFBS2N53ZFBFFS3ZFB2K8S3ZFB2K8S2SB2N53ATR3ZFBS2SB2N53ATR3ZFBS2SB2N53ATR3ZFBS2SB2N53ATR3ZFBS2SB3ATR3ZFB2K8S2SB2N53ATR3ZFBS3ZFBS3ZFB2K8FS3ZFB1HS3ZBu3ZFBS3ZFB".
guard_false.                           (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    shload 11. zload.                             (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    chk_branch chkA_8036c.                        (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    shload 13. zload.                             (* [comment removed for export] *)
    chk_branch chkA_80380.
    pload 20 1. pstep. pload 20 0. pstep. pload 20 2. pstep. pload 20 3. pstep.   (* [comment removed for export] *)
    do 8 zstep.                                   (* [comment removed for export] *)
    zstep. if_cases KM; clear KM.                 (* [comment removed for export] *)
    - (* [comment removed for export] *)
      zstep. zstep. zstep.                        (* [comment removed for export] *)
      zstep. if_cases KSK; clear KSK.             (* [comment removed for export] *)
      + zstep. zstep. exit_tailA.                 (* [comment removed for export] *)
      + zstep. zstep. if_cases K8; zify_cond K8.  (* [comment removed for export] *)
        * exit_tailA.                             (* [comment removed for export] *)
        * (* [comment removed for export] *)
          zstep. rewrite ZA7s. zstep. guard_false.    (* [comment removed for export] *)
          zstep. zstep. zstep.                    (* [comment removed for export] *)
          shload 14. zload. zstep. brr.           (* [comment removed for export] *)
          zstep. zstep.                           (* [comment removed for export] *)
          shload 11. zload. chk_branch chkA_8056c.   (* [comment removed for export] *)
          shload 13. zload. chk_branch chkA_80574.   (* [comment removed for export] *)
          zstep. zstep. zstep.                    (* [comment removed for export] *)
          shload 11. zload.                       (* [comment removed for export] *)
          pload 20 0. pstep. pload 20 1. pstep. pload 20 2. pstep. pload 20 3. pstep.   (* [comment removed for export] *)
          zstep. brr.                             (* [comment removed for export] *)
          do 9 zstep.                             (* [comment removed for export] *)
          zstep. zstep.                           (* [comment removed for export] *)
          zstep.                                  (* [comment removed for export] *)
          zstep.                                  (* [comment removed for export] *)
          shload 12. zload. zstep. brr.           (* [comment removed for export] *)
          zstep. zstep. zstep.                    (* [comment removed for export] *)
          zstep.                                  (* [comment removed for export] *)
          zstep. guard_false.                     (* [comment removed for export] *)
          zstep. zstep.                           (* [comment removed for export] *)
          shload 10. zload. chk_branch chkA_805f8.   (* [comment removed for export] *)
          zstep. zstep. zstep.                    (* [comment removed for export] *)
          shload 11. zload. chk_branch chkA_8060c.   (* [comment removed for export] *)
          zstep. zstep.                           (* [comment removed for export] *)
          shload 10. zload. zstep. brr.           (* [comment removed for export] *)
          pload 12 1. pstep. pload 12 0. pstep. pload 12 2. pstep. pload 12 3. pstep.   (* [comment removed for export] *)
          do 6 zstep.                             (* [comment removed for export] *)
          zstep.                                  (* [comment removed for export] *)
          zstep.                                  (* [comment removed for export] *)
          zf_successA.
    - (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      zstep. lnot_src.                            (* [comment removed for export] *)
      zstep. guard_false.                         (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      zstep. zstep.                               (* [comment removed for export] *)
      shload 11. zload. chk_branch chkA_803d4.   (* [comment removed for export] *)
      pload 10 0. pstep. cbv beta.                (* [comment removed for export] *)
      lazymatch goal with RB : 0 <= Znth 4 bl < 256 |- _ => rewrite (byte_litA _ RB); pose proof (fhd_decompA _ RB) as DEC end.
      destruct DEC as (Hd & _ & Hs & _).
      destruct Hd as [Hd|[Hd|[Hd|Hd]]]; destruct Hs as [Hs|Hs];
        [ eapply decB0a | eapply decB0b | eapply decB1a | eapply decB1b | eapply decB2a | eapply decB2b | eapply decB3a | eapply decB3b ]; eassumption.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End S.
End CANSEC1.
