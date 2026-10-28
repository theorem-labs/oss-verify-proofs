(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk PropExec MState Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem MemRange ZdWalkKit ZdCellKit SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_hft_iface AZ_kx AZ_hft_initds AZ_hft_dsym AZ_hft_fdec_defs.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.

Section CANSEC2. Context {rc : runConstT}.
(* [comment removed for export] *)
Local Ltac kxa_unpZ ::=
  lazymatch goal with
  | |- unpZ ?mm ?lo1 ?hi1 =>
      first [ kxa_hyp
            | match goal with
              | U : unpoisoned mm ?X ?hi0 |- _ =>
                  lazymatch lo1 with context [X] => apply (unpoisoned_unpZ mm X hi0 lo1 hi1 U); solve [unfold KXKEND; kx_lia] end
              end
            | match goal with
              | U : unpoisoned mm ?lo0 ?hi0 |- _ => apply (unpoisoned_unpZ mm lo0 hi0 lo1 hi1 U); solve [unfold KXKEND; kx_lia]
              end
            | kxa_unp_hook ]
  end.
Local Ltac kxa_rng0 ::=
  kxa_norm;
  lazymatch goal with
  | |- rng ?RG (KXSHLO + ?A / 8) (shspanZ ?A ?n) =>
      first [ match goal with
              | H : rng RG (shad ?X) ?N0 |- _ =>
                  lazymatch A with context [X] =>
                    apply (shad_shspan_rng RG A n (shad X) N0 H);
                    [ rewrite !shad_div; unfold ASHOFF; kx_lia | unfold shspanZ; rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia | kx_lia ]
                  end
              end
            | match goal with
              | H : rng RG (shad ?A0) ?N0 |- _ =>
                  apply (shad_shspan_rng RG A n (shad A0) N0 H);
                  [ rewrite !shad_div; unfold ASHOFF; kx_lia | unfold shspanZ; rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia | kx_lia ]
              | H : rng RG ?A0 ?N0 |- _ =>
                  apply (shad_shspan_rng RG A n A0 N0 H);
                  [ rewrite shad_div; unfold ASHOFF; kx_lia | unfold shspanZ; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia | kx_lia ]
              end
            | lazymatch RG with
              | (fun _ _ => True) => split; [unfold KXSHLO; kx_lia | split; [unfold KXSHLO, shspanZ; Z.div_mod_to_equations; lia | intros; exact I]]
              end
            | kxa_rng_hook ]
  end.

Section FD.
  Variables (RNG : footprint) (mA : amem) (SPV SPB lo DST cap SRC n WK wksz DT hs tl fast FF : Z) (tb : list Z) (src : list byte).
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Hypothesis HY : fdA_hyps RNG SPV SPB lo DST cap SRC n WK wksz DT hs tl FF.
  Hypothesis AN : fdA_an RNG mA SPV SPB lo DST cap SRC n WK wksz DT hs tl fast FF tb src.
  Hypothesis FAST1 : fast = 1.
  Variable Q : machine_state -> Prop.
  Hypothesis QX : fd_exitK Q gp tp F fc mA SPV SPB lo DST cap FF.
  Hypothesis QXC : fd_exitKc Q gp tp F fc mA SPV SPB lo DST cap FF.
  (* [comment removed for export] *)
  Hypothesis INITDS : fse_initds_stmtA.

  (* [comment removed for export] *)
  Notation F0ST pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 0x22700) (Z_to_bv 64 DT) (Z_to_bv 64 n) (Z_to_bv 64 SRC)
             (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 (DST + cap - 3)) (Z_to_bv 64 DST) (Z_to_bv 64 0x7fff8000) x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Ltac ids_call HY AN MU WM STC BDC FB STL MI :=
    eapply evtF_cut;
    [ eapply (INITDS RNG) with (lo := lo) (n := n - hs) (src := skipn (Z.to_nat hs) src) (tl := tl);
      lazymatch goal with
      | |- mem_inv _ _ => exact MI
      | |- stk bsegs _ lo _ => exact STL
      | |- rw_cells bsegs _ _ [CB 16 _] => exact STC
      | |- rw_cells bsegs _ _ (bitd_cells _ _ _ _ _) => exact BDC
      | |- rw_cells bsegs ?m DT _ => match goal with H : rw_cells bsegs m DT [C2 _; C2 _] |- _ => exact H end
      | |- fbit_ok _ _ _ _ => exact FB
      | |- bytes_at _ _ _ _ => exact (proj1 (fd_src0M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU))
      | |- zlen _ = _ => exact (proj2 (fd_src0M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU))
      | |- art ?m => match goal with H : art m |- _ => exact H end
      | |- astk _ _ _ => match goal with H : astk _ _ _ |- _ => exact H end
      | |- aro_client _ ?m => match goal with H : aro_client _ m |- _ => exact H end
      | |- aro _ _ DT 4 => exact (fd_aro_dtM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU)
      | |- 0 < _ -> aro _ _ _ _ => intros _; exact (fd_aro_srcM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU)
      | |- aro _ _ _ _ => eapply (fd_aro_frameM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ _ _ MU WM); clear; lia
      | |- app_blk _ _ => eapply (fd_app_frameM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ _ _ MU WM); clear; lia
      | |- _ => idtac
      end
    | ].

  (* [comment removed for export] *)
  Lemma fi_ini : (forall mm st1 st2 (cont : word) bc ptr pad (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
        FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> fbit_ok (SRC + hs) (n - hs) bc ptr ->
        evtF bsegs RNG Q (F0ST 0xac560 mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31)) ->
    forall mm x1 bc ptr (cont x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) pad j1 j2,
    rw_cells bsegs mm (SPB + 48) [CB 16 j2] -> rw_cells bsegs mm (SPB + 64) [CB 16 j1] ->
    rw_cells bsegs mm (SPB + 80) (bitd_cells cont (Z_to_bv 64 bc) pad ptr (SRC + hs)) ->
    stk bsegs mm DST (DST + cap) -> stk bsegs mm lo SPB -> mem_inv bsegs mm -> munch (FD_WB DST cap SPB) mA mm -> wmono bsegs mA mm ->
    fbit_ok (SRC + hs) (n - hs) bc ptr -> bc <= 64 ->
    evtF bsegs RNG Q (F0ST 0xac540 mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
  Proof.
    intros KI. intros until j2. intros F2 F1 BDC STD STL MI MU WM FOK BC64. unfold bitd_cells in BDC.
    pose proof HY as HY'. open_hy HY'. fd_atP HY AN. destruct FOK as [BCR BOK].
    clear DSTWK DSTSRC WKSRC FFDST FFWK FFSRC RDST RSDST ABD F64 FFH FFT RFF RSFF. unfold KHIGH in *.
    (* [comment removed for export] *)
    do 4 zstep.
    fd_atM HY AN MU WM.
    ids_call HY AN MU WM F1 BDC (conj BCR BOK) STL MI.
    all: match goal with |- forall ms', _ => idtac | _ => clear - LO0 LOS SPB0 SPB1 SPBA BCR BC64 TLR WKA DTE WKL WKH ROOM P2 SRCL SRCH HS1 HSN SP_BS SP_BT N0 SPR OFFSRC OFFWK; first [lia | Z.div_mod_to_equations; lia] end.
    intros ms' PO. unfold fse_initds_postA in PO.
    destruct PO as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m1 & st1 & cont1 & bc1 & ptr1 & -> & MU1 & WM1 & MI1 & STL1 & S1 & ST1 & BDC1 & FOK1 & BCB1 & DTH1).
    lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?nn)] => replace (ret_pc (Z_to_bv 64 nn)) with (Z_to_bv 64 nn) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end.
    assert (MU01 : munch (FD_WB DST cap SPB) mA m1).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU1]. intros x Hx. cbn [outside app] in *. clear - Hx. lia. }
    assert (WM01 : wmono bsegs mA m1) by (eapply wmono_trans; [exact WM| exact WM1]).
    assert (F2' : rw_cells bsegs m1 (SPB + 48) [CB 16 j2]) by (eapply rw_cells_transport; [exact F2 | exact MU1 | exact WM1 | cbn; clear; lia]).
    assert (STD1 : stk bsegs m1 DST (DST + cap)) by (eapply stk_transport_disjoint; [exact STD | exact MU1 | exact WM1 | cbn; clear - OFFDST LOS SPB0 SPB1 CAP0; lia]).
    clear MU WM MU1 WM1 STL F2 STD MI. fd_clearM DST SRC WK DT SPB. unfold bitd_cells in BDC1.
    (* [comment removed for export] *)
    do 4 zstep.
    destruct FOK1 as [BCR1 BOK1].
    fd_atM HY AN MU01 WM01.
    ids_call HY AN MU01 WM01 F2' BDC1 (conj BCR1 BOK1) STL1 MI1.
    all: match goal with |- forall ms', _ => idtac | _ => clear - LO0 LOS SPB0 SPB1 SPBA BCR1 BCB1 BC64 TLR WKA DTE WKL WKH ROOM P2 SRCL SRCH HS1 HSN SP_BS SP_BT N0 SPR OFFSRC OFFWK; first [lia | Z.div_mod_to_equations; lia] end.
    intros ms' PO. unfold fse_initds_postA in PO.
    destruct PO as (z5 & z6 & z7 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m2 & st2 & cont2 & bc2 & ptr2 & -> & MU2 & WM2 & MI2 & STL2 & S2 & ST2 & BDC2 & FOK2 & BCB2 & DTH2).
    lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?nn)] => replace (ret_pc (Z_to_bv 64 nn)) with (Z_to_bv 64 nn) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end.
    assert (MU02 : munch (FD_WB DST cap SPB) mA m2).
    { eapply munch_trans; [exact MU01|]. eapply munch_weaken; [| exact MU2]. intros x Hx. cbn [outside app] in *. clear - Hx. lia. }
    assert (WM02 : wmono bsegs mA m2) by (eapply wmono_trans; [exact WM01| exact WM2]).
    assert (S1' : rw_cells bsegs m2 (SPB + 64) [C8 (Z_to_bv 64 st1); C8 (Z_to_bv 64 (DT + 4))]) by (eapply rw_cells_transport; [exact S1 | exact MU2 | exact WM2 | cbn; clear; lia]).
    assert (STD2 : stk bsegs m2 DST (DST + cap)) by (eapply stk_transport_disjoint; [exact STD1 | exact MU2 | exact WM2 | cbn; clear - OFFDST LOS SPB0 SPB1 CAP0; lia]).
    eapply KI; [close_fdm | exact ST1 | exact ST2 | exact FOK2].
  Qed.
  Ltac fi_walk C2 C1 CB0 CA S N KR VM FUEL :=
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    let ks := eval cbv beta iota delta [app] in
      ([KR; KZRange S 4097 (2^47 - 16); KZRange (S + N) 4096 (2^47);
        KZWr (SPB + 48) 16; KZWr (SPB + 64) 16; KZWr (SPB + 80) 40; KZDisj (SPB + 48) 72 S N;
        KZImg 0x22620 0x22638] ++ kzb) in
    let ch := constr:((C2, C1, CB0, CA)) in
    kx_autoFLA_core VM constr:([0xac540; 0xac208; 0xac20c] : list Z) FUEL true ch
      constr:([KAUnp S N] : list kza) ks constr:([(S, N)] : list (Z * Z)) constr:([(S, N); (SPB, 120)] : list (Z * Z)).
  Ltac fi_enum :=
    let BCE := fresh "BCE" in
    match goal with
    | BDC : rw_cells _ ?m (SPB + 80) _ |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      lazymatch type of BDC with
      | context [C4 (Z_to_bv 64 (-1 * Z.lxor (bv_unsigned (edenot ?E ?e)) 31 + ?c))] =>
          kx_read_ranges;
          lazymatch e with context [EVar ?j] =>
            kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (-1 * Z.lxor v 31 + c) mod 2^64) && ((-1 * Z.lxor v 31 + c) mod 2^64 <=? 64))%bool end
      | context [C4 (Z_to_bv 64 (bv_unsigned (edenot ?E ?e) + ?c))] =>
          kx_read_ranges;
          lazymatch e with context [EVar ?j] =>
            kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (v + c) mod 2^64) && ((v + c) mod 2^64 <=? 64))%bool end
      | context [C4 (Z_to_bv 64 (bv_unsigned (edenot ?E ?e)))] =>
          kx_read_ranges;
          lazymatch e with context [EVar ?j] =>
            kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v mod 2^64) && (v mod 2^64 <=? 64))%bool end
      | context [C4 (edenot ?E ?e)] =>
          kx_read_ranges;
          lazymatch e with context [EVar ?j] =>
            kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v mod 2^64) && (v mod 2^64 <=? 64))%bool end
      end;
      cbv beta in BCE; apply andb_prop in BCE; destruct BCE as [BCE1 BCE2]; apply Z.leb_le in BCE1, BCE2
    end.
  Ltac fi_exb :=
    unfold EXB; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
    lazymatch goal with |- exists cs, rw_cells bsegs ?m _ _ /\ _ =>
      match goal with
      | A2 : rw_cells bsegs m (SPB + 48) ?c2, A1 : rw_cells bsegs m (SPB + 64) ?c1, A0 : rw_cells bsegs m (SPB + 80) ?c0 |- _ =>
        exists (c2 ++ (c1 ++ c0)); split;
        [ apply (proj2 (rw_cells_app bsegs m (SPB + 48) _ _)); split; [exact A2|];
          apply (proj2 (rw_cells_app bsegs m _ _ _)); split;
          [ replace (SPB + 48 + Z.of_nat (cells_size c2)) with (SPB + 64) by (cbn; clear; lia); exact A1
          | replace (SPB + 48 + Z.of_nat (cells_size c2) + Z.of_nat (cells_size c1)) with (SPB + 80) by (cbn; clear; lia); exact A0 ]
        | rewrite !cells_size_app; cbn; reflexivity ]
      end
    end.
  Ltac fi_ok KI :=
    match goal with BDC : rw_cells bsegs ?m (SPB + 80) ?cs |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      let v := lazymatch cs with
               | context [C4 (Z_to_bv 64 ?v)] => constr:(v mod 2^64)
               | context [C4 (edenot ?E ?e)] => constr:(bv_unsigned (edenot E e) mod 2^64)
               end in
      lazymatch cs with [C8 ?c; C4 _; CB _ ?pd; C8 ?pw; _; _] =>
      let p := lazymatch pw with Z_to_bv 64 ?p => p | _ => constr:(bv_unsigned pw) end in
      eapply (fi_ini KI) with (bc := v) (cont := c) (pad := pd) (ptr := p);
      lazymatch goal with
      | |- rw_cells _ _ (SPB + 80) _ => unfold bitd_cells; rewrite ?KXS.Z_to_bv64_mod, ?Z_to_bv_bv_unsigned; exact BDC
      | |- fbit_ok _ _ _ _ => unfold fbit_ok; split; [first [match goal with B1 : 1 <= ?x, B2 : ?x <= 64 |- _ => clear - B1 B2; lia end | lia] | intros; first [left; reflexivity | right; lia | left; lia | rewrite ?Z.mod_small by lia; first [left; lia | right; lia]]]
      | |- _ <= 64 => first [match goal with B1 : 1 <= ?x, B2 : ?x <= 64 |- _ => clear - B1 B2; lia end | lia]
      | |- _ => eassumption
      end end
    end.

  (* [comment removed for export] *)
  Lemma fi_bi : (forall mm st1 st2 (cont : word) bc ptr pad (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
        FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> fbit_ok (SRC + hs) (n - hs) bc ptr ->
        evtF bsegs RNG Q (F0ST 0xac560 mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31)) ->
    fd_entK RNG Q gp tp F fc mA SPV SPB lo DST cap SRC n hs WK wksz DT FF 0xac0c4.
  Proof.
    intros KI. unfold fd_entK, fd_entst. intros until jb. intros F2 F1 FB0 STD STL MI MU WM.
    pose proof HY as HY'. open_hy HY'. fd_atP HY AN.
    clear DSTWK DSTSRC WKSRC FFDST FFWK FFSRC RDST RSDST ABD F64 FFH FFT RFF RSFF. unfold KHIGH in *.
    (* [comment removed for export] *)
    fd_atM HY AN MU WM.
    pose proof (fd_aro_srcM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU) as AROS.
    assert (SSH : SRC + n <= 2^47 - 16) by (pose proof (ablk_lin _ _ ABS) as (_ & _ & SA & _); pose proof ATOP_range as ATR; unfold ATOP_MIN, ATOP_MAX in ATR; clear - SA ATR; lia).
    assert (NC : n - hs = 0 \/ n - hs = 1 \/ 2 <= n - hs <= 7 \/ 8 <= n - hs) by (clear - HSN; lia).
    clear - HY AN FAST1 QX QXC INITDS KI F2 F1 FB0 FA TB SRCB STD STL MI MU WM US RSRC RSSRC RWK RSWK RSTK RSFR RI SSH TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN ART AZ AC ASTK LO0 OFFSRC OFFWK OFFDST B_SRC WKA NC AROS.
    remember (SRC + hs) as SS eqn:ESS. remember (n - hs) as NN eqn:ENN. try rewrite <- ESS in AROS. try rewrite <- ENN in AROS. try rewrite <- ENN in NC.
    destruct AROS as (USS & RSS & RSSS).
    destruct NC as [NC | [NC | [NC | NC]]];
      [ fi_walk F2 F1 FB0 FA SS NN (KZRange NN 0 0) constr:(0%Z) 60%nat
      | rewrite ENN in KI; rewrite NC in *; fi_walk F2 F1 FB0 FA SS 1 (KZRange SS 4097 (2^47 - 16)) constr:(8%Z) 260%nat
      | fi_walk F2 F1 FB0 FA SS NN (KZRange NN 2 7) constr:(8%Z) 260%nat
      | fi_walk F2 F1 FB0 FA SS NN (KZRange NN 8 (2^32)) constr:(0%Z) 160%nat ].
    all: try (lazymatch goal with |- accP _ _ (?a, _) => lazymatch a with context [ALU_SRL] => first [kx_sh_acc RSSS | kx_sh_acc RSSRC] | context [EVar _] => first [kx_acc RSS | kx_acc RSRC] | _ => kx_acc RI end end).
    all: try (lazymatch goal with |- sc_resid _ _ _ (SCReadBase ?a _ _ _) => lazymatch a with context [ALU_SRL] => kx_sh_rd USS | _ => kx_rd SRCB end end).
    all: try (lazymatch goal with |- _ <= _ <= _ => clear - SSH SRCL HS1 HSN ESS ENN; lia end).
    all: try (kx_side_pre; solve [kx_lia | clear - LO0 LOS SPB0 SPB1 SPBA TLR WKA DTE WKL WKH ROOM P2 SRCL SRCH HS1 HSN SP_BS SP_BT N0 NH SPR OFFSRC OFFWK NC ESS ENN; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => lazymatch pc with 0xac540 => fail | 0xac208 => fail | 0xac20c => fail | _ => first [kx_sh_dead0_any | kx_sh_dead_any 1 | kx_sh_dead_any 8] end end).
    (* [comment removed for export] *)
    all: kx_mem.
    all: try fi_enum.
    all: kx_abs.
    all: subst SS NN.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xac208) _ _ _ _) =>
             (* [comment removed for export] *)
             apply evtF_done; eapply QX; [fi_exb | clear; lia | left; reflexivity]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xac20c) _ _ _ _) => apply evtF_done; eapply QXC; [fi_exb | clear; lia | left; reflexivity]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xac540) _ _ _ _) =>
             (* [comment removed for export] *)
             fi_ok KI
         end.
  Qed.
End FD.
End CANSEC2.
