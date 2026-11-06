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
  #[using="rc PLR NB SB ZA ZB SEPZ USRC UZF RS RSS RZ RSZ RI RIS"] Lemma decC2a1 : forall m1 x1 x5 x6 x7 x11 x13 x15 x16 x17 x28 x29 x30 x31,
    5 <= n -> Z.land (Znth 4 bl) 3 = 2 -> Z.land (Znth 4 bl) 32 = 0 -> Z.shiftr (Znth 4 bl) 6 = 1 ->
    rw_cells bsegs m1 ZF ZCELLS -> bytes_at bsegs m1 S (map (Z_to_bv 8) bl) -> GSC m1 ->
    munch W mM m1 -> wmono bsegs mM m1 -> mem_inv bsegs m1 ->
    evtF bsegs RNG (QX gp tp s11 F fc SP FF ZF bl mM) (decA_at gp tp s11 F fc SP FF ZF S bl m1 x1 x5 x6 x7 x11 x13 x15 x16 x17 x28 x29 x30 x31).
  Proof.
    unfold decA_at. intros until x31. intros N5 Hd Hs Hf CZ PL GS MU WM MI.
    pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
    assert (LENB : Z.of_nat (length (map (Z_to_bv 8) bl)) = n) by (rewrite length_map; reflexivity).
    pose proof atop_range as ATR. pose proof ZB as ZBu. unfold AIMG_HI, KLS, KHIGH in ZBu.
    pose proof (rw_cells_bound _ _ _ _ CZ) as ZFB. cbn [cells_size csize Nat.add] in ZFB.
    unfold GSC, GSHC in GS.
    unfold ZCELLS, zcellA in CZ.
    Local Ltac2 Set LiaHints.tbl := fun () => "0370>10349463449.7110512988003.951077445093.94 10796611846.9112100317789.9612270618323.9612331426020.9513090646977.8213101873376.7213140303554.9313156025775.6513283783202.6113666555668.7314274662228.6914854219923.6614854219923.7014854219923.7615043250697.8015043867193.7915640285071.6815658255133.9315876876809.7515878973759.7416075574774.6116800856201.7216802407995.6216809028512.641703303920.91 1705401081.94 18086011986.9618511472777.7318511472777.9218511472777.9318511472777.9518589810881.9118681669866.6119010590676.9319302163537.8119589975962.9219898057826.8319908892480.7420700320864.6521209840128.612211481613.65 222951252.93  22390832721.9422392929881.7222497888913.6923596256905.6823596676285.6724063222530.9224991237562.7925316413697.6125838294319.6025870727770.9326437422590.9327043595954.9327544385342.9227792411280.7228021047327.7728465183336.7628465183337.8128465183338.8228465183341.6528465183342.6928465183343.7528915217082.7929792256214.7930801439541.8031143794842.7332285357718.7032417836825.9132419933968.9432573021867.693272297910.93 33034670907.9633903789786.9334299049457.923462647984.61 34807508038.91355734914.92  35852192547.933601076474.62 36861627478.6936944756847.9337245531378.8137245661434.6537245665252.6137247908063.8137258295512.623891787750.61 41565867381.7341565867381.7541565867382.7241565867382.9141565867383.7441565867384.6841567964538.8541567964538.9141567964542.7441626456813.7241863133603.9342088995992.7542153485029.9442321050728.6142709640138.8642829974483.8043158952066.9543313548721.6443610559407.7543929283712.8943929283712.9544327231971.9644350553920.8044355972192.914502176483.73 45064778230.6345069446927.5645071674889.6445452174881.9445689441237.8045689441238.7945697359223.6946725515913.8146727612857.8049404231370.8449604477442.7349652760252.8950050174752.7850056190976.8950398796617.8750581696400.9450693103920.8152377759097.9452396529346.7852449451781.925267322392.92 5293472389.92 53097216523.9753510313877.675363304390.76 53966538437.7254242975896.8254376156028.8154490019650.9354849128932.9554849128933.9455975063515.9356735579368.9257117873148.8158393424463.6158620089984.9658649831881.805885610054.72 59088058364.8159180274509.9459314873579.6359314988138.6259314988138.6659314988138.7059314988138.7659879751450.7561172658147.9261276787904.6861285877737.7661372096020.9261402886599.7561598176679.616175652895.75 62009686963.6962026611512.6562766606146.9463110050239.7363110384265.7463230379004.8164092089369.6164243778586.9264295209551.7464297306692.8964297306694.8164301028607.6264302930276.6564302931183.6964305402179.7564395266175.7064981188865.7166232013900.8166232143940.6566232145359.6966356652615.7767193953379.9267415031418.6268304808833.747065539866.95 8144176112.93 8147615255.93 8298977940.95 8605669008.65 8861642132.92 00000400900K00L00P00Q00c01201A01P01Q01R01W01X01g02602E02I02M02P02Q02U02Y02`02o03>03M03N03O03P03Q03R03S03T03X03Y03^03_03c04204A04B04C04D04I04[04m04n05205605E05F05G05H05L05[05\05]05`05d05e05f05g05h05i05j05k05l05m06106206306406506906:06>06?06C06D06S06X06Y06Z06_06`06a06b06c06d06e06i06m07107507907=07A07E07I07[07`07a08308408808;08J08M08N08O08P08b09109@09E09I09M09Q09R09W09\09a09e09i09m0:<0:@0:O0:^0:b0:c0:d0:e0:h0:i0:j0:k0:o0;00;40;50;90;:0;I0;[0;m0;n0<20<30<40<50<60<:0<;0<<0<?0<E0<V0<g0=80=90=>0=M0=\0=a0=b0=c0=g0=k0=o0>30>70>;0><0>=0>A0>P0>_0>n0?@0?O0?^0?m0?n0?o0@30@70@;0@<0@A0@B0@E0@I0@N0@O0@T0@U0@ZS2KLS3ZFBS2SB2ZB3ATR3ZFB2KLSS2KLSS2SB2ZB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS4SEPZ4LENB3ZFBFSS3ZBuFS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2KLS2KLS1HSS2KLS2KLS2NB2N5S2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLSSSSSSSS2KLSS3ZBuSS2HBS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLFFFS3ZBuS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLFS2KLS2KLS4SEPZ4LENB3ZFBSFSS2HBS4SEPZ4LENB3ZFBSSS1HS2KLSSSSSSSSFS2HBSSSFS2HBSS2HBSS2N5SS4SEPZ4LENB3ZFBS3ZFBFFS3ZFBFFFFFFS2RBS2RBS2RBS2RBS2RBS2RBS2RBS2RBS2RBS2SB2ZB3ATR3ZFB2KLS3ZFBFS2SB2ZB3ATR3ZFB2KLFS2KLS1HS4SEPZ4LENB3ZFBS1HFFFS2SB2ZB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS3ZFBS2N5S2N5S2N5FS3RB1S3RB1S3RB1S2KLS2KLS2KLS4SEPZ4LENB3ZFBS2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2KLSSSS1HSSSS2KLSS2KLSS2N5SS4SEPZ4LENB3ZFBS2SB2ZB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLSS2KLSFSFS2N5SSS1HS2SB1GS2SB3ATR3ZFB2KL1GS2SB3ATR3ZFB2KL1GS2SB3ATR3ZFB2KL1GFS3ZFBS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS3ZBuFFS2KLS2KLS2KLS2KLS2KLS2KLSSS2HBS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2SB2ZB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLS2SB3ATR3ZFB2KLSFS2KLS2KLS2KLFS3ZFBFS1HS2HBS3ZBuSS3ZBuSS3ZBu".
pose proof (proj2 (buf_nthA m1 S bl 4 (conj PL PLR) ltac:(lia))) as RB.
    pose proof (fhd_decompA _ RB) as DEC.
    destruct DEC as (_ & _ & _ & Hr & E24 & E64).
    rewrite Hf in E24, E64; cbn in E64.
    pose_tabA 2.
    lazymatch type of Hf with _ = ?f => let k := eval vm_compute in (8 + f) in pose_tabA k end.
    repeat (gstepA Hd Hs Hf E64).
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End S.
End CANSEC1.
