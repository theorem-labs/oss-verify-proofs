(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.World Require Import Src_zlib_example_flush_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Frame Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead STower.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate
     InflateInv InflateInvKit InflateInvRun InflateInvApi InflateInvLoop InflateInvCall InflateRc InflateCall HarnessKit HarnessFacts.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.FMQ6 Require Import CallocLib6 CallocTail6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6 Callee6 CalleeKits6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6 Callee6i Itab6 UpdWin6
     Infl6 Infl6B Infl6C IfSpec6 IfFast6 InffastOk IRep6 IInit6 ITok6 ICall6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import ZlibStmtBase ExSmallIface FlLibStmt FlLibIface.
Import InflLv Infl6A.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Abbreviation RSX := Src_zlib_example_flush_fuzzer_repro.M.loaded_segments.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Lemma zb_store : forall (R : bvmap 5 word) (M : word -> option byte) (S w : Z),
  getr R 10 = zw w -> getr R 19 = zw S -> 0 < w < 2 ^ 63 -> 0 < S -> S + 7176 < 2 ^ 63 -> mapped M S 7176 ->
  exists R',
    msteps s6_segs (mkst R (Z_to_bv 64 pc6_zb) M s6_rom)
           (mkst R' (Z_to_bv 64 pc6_uwj) (wbytes M (zw (S + 88)) (Z_to_le_bytes 8 w)) s6_rom)
    /\ (forall rg, getr R' rg = getr R rg).
Proof.
  intros R M S w G10 G19 Hw HS0 HS1 MS. unfold mapped in *.
  symex s6_segs (CFG [] [] [] [pc6_uwj] []) 4%nat [false]
    NoReads [(10, EVar 32%nat); (19, EVar 33%nat)] [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63)]
    NoRegions [w; S] NoVals F0 F0'
    (mkst R (Z_to_bv 64 pc6_zb) M s6_rom) R' HR' Hfr Hms.
  exists R'. split; [by_run Hms|]. intros rg; apply Hfr; reflexivity.
Qed.

End FXG.
Ltac inl := cbn [In]; repeat (first [ left; reflexivity | right ]).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Section INB.
  Variables (R0 RW regs : bvmap 5 word) (mem : word -> option byte) (q : iptrs) (s : inflate_state) (zc : ZCall) (f : Z).
  Variables (sp ra inp outp zcl fa ff w : Z) (b : blk).
  Local Abbreviation p := (ip_p q). Local Abbreviation strm := (ip_strm q).
  Local Abbreviation input := (zc_input zc). Local Abbreviation n := (zlength (zc_input zc)). Local Abbreviation NO := (zc_avail_out zc).
  Local Abbreviation ans := (Some (b, fun _ : Z => 0)).

  Hypothesis HT : TWF R0 RW q inp outp s zc f mem.
  Hypothesis RK : rkeep RW regs FL_KEEP.
  Hypothesis G2 : getr R0 2 = zw sp.
  Hypothesis G1 : getr R0 1 = zw ra.
  Hypothesis G11 : getr R0 11 = zw f.
  Hypothesis P10 : getr regs 10 = zw w.
  Hypothesis P2 : getr regs 2 = zw (sp - FL_ZWD).
  Hypothesis HZC : zcl + FL_FRA <= sp.
  Hypothesis SP47 : sp <= 2 ^ 47.
  Hypothesis IC : img_clear mem.
  Hypothesis FA : fa = FL_ZCALLOC.
  Hypothesis FF : ff = FL_ZCFREE.
  Hypothesis BW : blk_okz RSX mem FL_IMG_TOP zcl w FL_WIN_N.
  Hypothesis ZW : zeros_at RSX mem w FL_WIN_N.
  Hypothesis AP : all_apart ((w, FL_WIN_N) :: (sp - FL_FRA, FL_FRA) :: (strm, 112) :: (outp, NO) :: (inp, n) :: iblocks q).
  Hypothesis HA : snd (inflate_p ivar_ref ans s zc f) = Some FL_WIN_N.

  Definition cvB : icv := cvW R0 sp q inp outp zc f w 32768.

  Theorem inflate_fl_inb :
    exists (regs' : bvmap 5 word) (mem' : word -> option byte) (nout : Z),
      let s' := fst (fst (inflate_p ivar_ref ans s zc f)) in let r := snd (fst (inflate_p ivar_ref ans s zc f)) in
      msteps RSX (mkst regs (Z_to_bv 64 FL_A_ZB) mem (seg_rom RSX)) (mkst regs' (Z_to_bv 64 ra) mem' (seg_rom RSX))
      /\ 0 <= nout <= NO
      /\ frame_mod mem mem' ((Z_to_bv 64 (sp - FL_IFR), FL_IFR) :: (Z_to_bv 64 strm, 112) :: (Z_to_bv 64 outp, nout) :: wz (iblocks (IP strm p w)))
      /\ getr regs' 10 = Z_to_bv 64 (zr_rc r) /\ getr regs' 2 = Z_to_bv 64 sp /\ rkeep R0 regs' FL_KEEP
      /\ (~ RR (zr_rc r) ->
          nout = zlength (zr_output r) /\ 0 <= zr_consumed r <= n
          /\ FL_IREP mem' (IP strm p w) s'
          /\ izs_cells FL_MSGA mem' strm (inp + zr_consumed r) (n - zr_consumed r) (outp + nout) (NO - nout) (zr_strm r) p fa ff
          /\ holds RSX mem' outp (zr_output r)).
  Proof.
    pose proof ICall6.consts as (KA & KF & KFRA & KTOP & KRO & KIS & KWN & KIFR & KZWD).
    destruct HT as (sp0 & sx & cx & rx & T). cbv zeta in T.
    destruct T as (Gsp & Hchk & EQL & LN & EWB & HX & SR & RIv & CIv & Hws0 & U & ZC & HXS & MSG & HW0 & Hblk & Hwl & C & RG & WR & W3 & W4 & HMC & HUW & Mf & Mz & Ms & Mp).
    pose proof (ic_sp _ C) as Csp. pose proof (ic_S _ C) as CS. pose proof (ic_ZP _ C) as CZP. pose proof (ic_I0 _ C) as CI0. pose proof (ic_P0 _ C) as CP0.
    cbn [cvW cv_sp cv_R0 cv_ZP cv_S cv_I0 cv_P0 cv_WB cv_NI cv_NO cv_WN cv_flush cv_TOT0 cv_fa cv_ff cv_opq] in Csp, CS, CZP, CI0, CP0.
    unfold IMG6_TOP, INF_FRAME, INF_SCRATCH in Csp.
    pose proof BW as BW'. unfold blk_okz, FL_WIN_N, FL_IMG_TOP in BW'. destruct BW' as (W16 & W1 & WZ & WIM & SOW).
    rewrite KFRA in HZC.
    assert (Esp : sp0 = sp).
    { pose proof (f_equal bv_unsigned (eq_trans (eq_sym Gsp) G2)) as E. rewrite !u_zw_small in E by (clear - Csp HZC SP47 W1 WZ; lia). exact E. }
    subst sp0.
    pose proof AP as A. unfold iblocks, FL_FRA, FL_ISTATE_N, FL_WIN_N in A. rewrite HW0 in A. cbn [Z.eqb app all_apart apart_from_all] in A.
    destruct A as ((AWF & AWZ & AWO & AWI & AWP & _) & _). unfold ExSmallIface.apart in AWF, AWZ, AWO, AWI, AWP.
    pose proof (mapped_of_store_ok6 mem w 32768 ltac:(clear - W1; lia) ltac:(clear; lia) ltac:(clear - WZ HZC SP47; lia) WIM SOW) as MWB0.
    change (forall x : word, w <= bv_unsigned x < w + 32768 -> mem x <> None) with (mapped mem w 32768) in MWB0.
    assert (Hrod : rod6_clear mem).
    { intros x Hx. unfold ROD6_LO, ROD6_HI in Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply IC. unfold FL_RO_LO, FL_RO_HI. exact Hx. }
    pose proof (cells_zero_of_zblock mem w 32768 w 1 1 32768 (fun _ => 0)
                  (zblock_of_zeros_at mem w 32768 ltac:(clear - W1; lia) ltac:(clear; lia) ltac:(clear - WZ HZC SP47; lia) MWB0 ZW)
                  (fun _ => eq_refl) ltac:(clear; cbn; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - W1; lia) ltac:(clear - WZ HZC SP47; lia) ltac:(clear; lia)) as ZWC.
    assert (C' : ictx cvB).
    { destruct C. cbn [cvW cv_sp cv_R0 cv_ZP cv_S cv_I0 cv_P0 cv_WB cv_NI cv_NO cv_WN cv_flush cv_TOT0 cv_fa cv_ff cv_opq] in *.
      constructor; cbn [cvB cvW cv_sp cv_R0 cv_ZP cv_S cv_I0 cv_P0 cv_WB cv_NI cv_NO cv_WN cv_flush cv_TOT0 cv_fa cv_ff cv_opq]; try assumption.
      all: unfold offimg, sep, IMG6_TOP, INF_FRAME, INF_SCRATCH; try exact WIM.
      all: try (clear - W1 WZ HZC SP47 W16; lia).
      all: try (clear - AWF; lia). all: try (clear - AWZ; lia). all: try (clear - AWP; lia).
      all: try (intros _; clear - AWI; lia). all: try (intros _; clear - AWO; lia).
      all: match goal with |- ?G => idtac "ICTXB-LEFT" G end. }
    (* 1.4 WSTR order: x21 = NI, x25 = out, x20 = out - left after updatewindow's own x8 / x9 / x18 / x19 *)
    destruct WR as (Q13 & Q10 & Q11 & Q12 & Q2 & Q8 & Q9 & Q18 & Q19 & Q21 & Q25 & Q20).
    cbn [cvW cv_sp cv_R0 cv_ZP cv_S cv_I0 cv_P0 cv_WB cv_NI cv_NO cv_WN cv_flush cv_TOT0 cv_fa cv_ff cv_opq] in Q13, Q10, Q11, Q12, Q2, Q8, Q9, Q18, Q19, Q21, Q25, Q20.
    unfold INF_FRAME in Q2.
    assert (EQW : forall r : reg, In r FL_KEEP -> getr regs r = getr RW r) by (intros r Hr; exact (RK r Hr)).
    pose proof RIv as RIx. unfold RINV in RIx. destruct RIx as (Rnx & Rhv0 & Rnh & Rpt0 & Rlf0 & Rpl & Rin & Rout & Routp & Rbits & Rhold).
    pose proof HX as HXx. unfold LX in HXx. cbn [w_s w_c w_r cvW cv_NI] in HXx. destruct HXx as (Xwrap & Xwbits & Xlive & Xflags & Xin & Xret & Xmsg & Xhd).
    pose proof (srng_win sx SR) as (Wsz2 & Wwh & Wwn & Wle & Weq).
    destruct (zb_store regs mem p w P10 ltac:(rewrite (EQW 19%bv ltac:(inl)); exact Q19) ltac:(clear - W1 WZ HZC SP47; lia) ltac:(clear - CS; lia) ltac:(clear - CS; lia) Ms)
      as (R1 & Hms0 & Hfr0).
    (* 1.4: state->window at p + 88 (zb_store) *)
    set (M1 := wbytes mem (zw (p + 88)) (Z_to_le_bytes 8 w)) in *.
    assert (EQ1 : forall x : word, ~ (p + 88 <= bv_unsigned x < p + 96) -> M1 x = mem x).
    { intros x Hx. subst M1. apply wbytes_inside; [clear - CS; lia | cbn; clear - CS; lia | cbn; clear - Hx; lia]. }
    set (sF := uw_fresh (sL (sR sx rx) (cR cx rx) rx) b (fun _ : Z => 0)).
    pose proof (uw_fresh_fields (sL (sR sx rx) (cR cx rx) rx) b (fun _ : Z => 0)) as F. cbv zeta in F. fold sF in F.
    destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19 & F20).
    pose proof (sL_fields (sR sx rx) (cR cx rx) rx) as (Gb & Gl & Gm & Gw & Gwb & Gf & Ghd & Gwin & Gblk & Gws).
    pose proof (sR_fields sx rx) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15).
    pose proof (cR_fields cx rx) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11).
    pose proof (cL_fields cvB (sR sx rx) (cR cx rx) rx) as (J1 & J2 & J3 & J4 & J5 & J6 & J7).
    assert (Hwb15 : is_wbits (sL (sR sx rx) (cR cx rx) rx) = 15) by (rewrite Gwb, Y6; exact Xwbits).
    unfold LMEMC in HMC. cbn [cvW cv_sp cv_R0 cv_ZP cv_S cv_I0 cv_P0 cv_WB cv_NI cv_NO cv_WN cv_flush cv_TOT0 cv_fa cv_ff cv_opq w_s w_c w_r] in HMC.
    destruct HMC as (Lsc & Llens & Lwork & Lcodes & _ & Lin & Lout & Lzs & Lfr & Loutc). unfold INF_FRAME in Lfr, Loutc.
    unfold INF_FRAME, INF_SCRATCH in Mf.
    assert (HM1 : LMEM cvB (mkW sF (cL cvB (sR sx rx) (cR cx rx) rx) rx) M1).
    { apply LMEM_ofC; cbn [cvB cvW cv_sp cv_R0 cv_ZP cv_S cv_I0 cv_P0 cv_WB cv_NI cv_NO cv_WN cv_flush cv_TOT0 cv_fa cv_ff cv_opq].
      - unfold LMEMC. cbn [cvB cvW cv_sp cv_R0 cv_ZP cv_S cv_I0 cv_P0 cv_WB cv_NI cv_NO cv_WN cv_flush cv_TOT0 cv_fa cv_ff cv_opq w_s w_c w_r].
        split.
        { subst sF. unfold is6_scalars. rewrite is6_vals_uw_fresh. subst M1.
          exact (is6_upd_window mem p (ISP strm 0) _ w Lsc ltac:(clear - CS; lia) ltac:(unfold is6_SIZE; clear - CS; lia)). }
        split; [rewrite F14; subst M1; apply (cells_write_other _ _ _ _ _ _ _ _ _ Llens); cbn; clear - CS; lia|].
        split; [rewrite F15; subst M1; apply (cells_write_other _ _ _ _ _ _ _ _ _ Lwork); cbn; clear - CS; lia|].
        split; [rewrite F16; subst M1; apply (cells_write_other _ _ _ _ _ _ _ _ _ Lcodes); cbn; clear - CS; lia|].
        split.
        { intros _ i Hi. rewrite F17, Hwb15. change (shl32 1 15) with 32768. rewrite arr_get_fresh0. subst M1.
          apply (cells_write_other _ _ _ _ _ _ _ _ _ ZWC); [cbn; clear; lia | clear - W1 WZ HZC SP47; lia | clear - W1 WZ HZC SP47; lia | clear - CS; lia | cbn; clear - CS; lia | | exact Hi].
          cbn. clear - AWP. lia. }
        split.
        { subst M1. pose proof (ic_d_SI _ C) as D. cbn [cvW cv_S cv_I0 cv_NI] in D. unfold sep in D.
          destruct (Z.eq_dec n 0) as [En|En]; [rewrite En; intros i Hi; exfalso; clear - Hi; lia|].
          apply (cells_write_other _ _ _ _ _ _ _ _ _ Lin); cbn; clear - CS CI0 D En; lia. }
        split.
        { subst M1. destruct (Z.eq_dec (ir_put rx) 0) as [E0|E0]; [rewrite E0; intros i Hi; exfalso; clear - Hi; lia|].
          apply (cells_write_other _ _ _ _ _ _ _ _ _ Lout); cbn; pose proof (ic_d_SP _ C) as D; cbn [cvW cv_S cv_P0 cv_NO] in D; unfold sep in D; clear - CS CP0 D Rpt0 Rpl Rlf0 E0; lia. }
        split; [subst M1; pose proof (ic_d_ZS _ C) as D; cbn [cvW cv_ZP cv_S] in D; unfold sep in D;
                apply (izs6_other _ C' mem _ (p + 88) (Z_to_le_bytes 8 w)); [exact Lzs | clear - CS; lia | cbn; clear - CS; lia | cbn; clear - D; lia]|].
        split.
        { apply (iframe6_local _ mem M1); cbn [cvB cvW cv_sp cv_R0]; [exact Lfr | clear - Csp; lia | clear - Csp; lia |].
          intros z Hz. apply EQ1. change (Z_to_bv 64 z) with (zw z). rewrite u_zw_small by (clear - Hz Csp; lia).
          pose proof (ic_d_fS _ C) as D. cbn [cvW cv_sp cv_S] in D. unfold sep, INF_FRAME, INF_SCRATCH in D. clear - Hz D. lia. }
        subst M1. unfold INF_FRAME. pose proof (ic_d_fS _ C) as D. cbn [cvW cv_sp cv_S] in D. unfold sep, INF_FRAME, INF_SCRATCH in D.
        apply cell_write_other; [exact Loutc | clear - Csp; lia | cbn; clear - Csp; lia | clear - CS; lia | cbn; clear - CS; lia | cbn; clear - D; lia].
      - subst M1. pose proof (ic_o_S _ C) as D. cbn [cvW cv_S] in D. unfold offimg, IMG6_TOP in D.
        apply rod6_store; [exact Hrod | clear - CS; lia | cbn; clear - CS; lia | cbn; unfold ROD6_LO, ROD6_HI; clear - D; lia].
      - unfold INF_FRAME, INF_SCRATCH. intros x Hx. subst M1. apply wbytes_grows. exact (Mf x Hx).
      - intros x Hx. subst M1. apply wbytes_grows. exact (Mz x Hx).
      - intros x Hx. subst M1. apply wbytes_grows. exact (Ms x Hx).
      - intros x Hx. subst M1. apply wbytes_grows. exact (Mp x Hx).
      - intros _ x Hx. subst M1. apply wbytes_grows. exact (MWB0 x Hx). }
    assert (HF1 : UWF cvB M1 (cv_S cvB) (ir_ret rx mod 2 ^ 64) (ir_have rx) (ir_left rx) (ir_out rx - ir_left rx)).
    { unfold UWF. cbn [cvB cvW cv_sp]. unfold UWC, INF_FRAME in HUW. unfold INF_FRAME. destruct HUW as (U1 & U2 & U3 & U4 & U5 & U6).
      pose proof (ic_d_fS _ C) as D. cbn [cvW cv_sp cv_S] in D. unfold sep, INF_FRAME, INF_SCRATCH in D.
      subst M1. repeat match goal with |- _ /\ _ => split end;
        (apply cell_write_other; [eassumption | clear - Csp; lia | cbn; clear - Csp; lia | clear - CS; lia | cbn; clear - CS; lia | cbn; clear - D; lia]). }
    assert (Hfl : is_flags sx = 0 \/ ir_out rx = ir_left rx) by (destruct Xflags as [X0 | (X1 & _ & XO)]; [left; exact X0 | right; exact XO]).
    pose proof (inflate_p_granted cvB s zc sx cx rx b (fun _ : Z => 0) Hchk EQL LN EWB Xwrap Xwbits Hws0
                  ltac:(clear - Wwn; lia) ltac:(clear - Wwh; lia) Hfl Xin ltac:(cbn [cvB cvW cv_NI]; clear - Rhv0 Rnh Rnx CI0; lia)
                  ltac:(clear - Rout Routp Rpt0 Rpl Rlf0 CP0; lia)) as [EQP ASK].
    fold sF in EQP. cbn [cvB cvW cv_flush] in EQP, ASK.
    destruct (inflate_resume6 cvB C' memcpy_run6_ok
                sx cx rx sF R1 M1 (outp + ir_put rx) (ir_out rx - ir_left rx)
                eq_refl SR RIv CIv HX Hws0
                ltac:(intros fd Hfd; cbn [In] in Hfd;
                      destruct Hfd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]; assumption)
                ltac:(rewrite F17, Hwb15; apply arr_len_fresh) HM1 eq_refl eq_refl
                ltac:(split; [| split; [cbn [cvB cvW cv_WB]; rewrite (Hfr0 10%bv); exact P10 | exact HF1]];
                      unfold uw_regs; cbn [cvB cvW cv_S cv_sp cv_P0]; unfold INF_FRAME; rewrite !Hfr0;
                      split; [rewrite (EQW 8%bv ltac:(inl)); exact Q8|]; split; [rewrite (EQW 9%bv ltac:(inl)); exact Q9|];
                      split; [rewrite (EQW 19%bv ltac:(inl)); exact Q19 | rewrite P2, KZWD; apply f_equal; clear; lia])
                ltac:(rewrite (Hfr0 21%bv), (EQW 21%bv ltac:(inl)); exact Q21)
                ltac:(rewrite (Hfr0 25%bv), (EQW 25%bv ltac:(inl)); exact Q25)
                ltac:(rewrite (Hfr0 3%bv), (EQW 3%bv ltac:(inl)); cbn [cvB cvW cv_R0]; exact W3)
                ltac:(rewrite (Hfr0 4%bv), (EQW 4%bv ltac:(inl)); cbn [cvB cvW cv_R0]; exact W4))
      as (R5 & M5 & Hms5 & A10 & A2 & Asv & A3 & A4 & Hg5 & HE5 & CM5 & HXS5 & Hmsg5 & Hno5 & HCC5).
    cbv zeta in CM5, HXS5. cbn [cvB cvW cv_sp cv_R0 cv_ZP cv_S cv_I0 cv_P0 cv_WB cv_NI cv_NO cv_WN cv_flush cv_TOT0 cv_fa cv_ff cv_opq] in Hms5, A10, A2, Asv, A3, A4, HE5, Hno5, Hmsg5.
    rewrite G1 in Hms5.
    set (cf := cL cvB (sR sx rx) (cR cx rx) rx) in *.
    set (s5 := uwc sF (ic_outbuf cx) (ir_put rx) (ir_out rx - ir_left rx)) in *.
    cbv zeta. destruct (inflate_p ivar_ref ans s zc f) as [[s' r'] asked] eqn:EP. cbn [fst snd] in EQP, HA |- *.
    pose proof (inflate_p_post ivar_ref ans s zc f U ZC) as PP. rewrite EP in PP. cbn [fst snd] in PP. destruct PP as [U' _].
    injection EQP as Es' Er'. subst s' r'. fold cf.
    assert (Hput : 0 <= ir_put rx <= NO) by (clear - Rpt0 Rlf0 Rpl; lia).
    exists R5, M5, (ir_put rx).
    split; [eapply msteps_trans; [exact Hms0 | exact Hms5]|].
    split; [exact Hput|].
    split.
    {
      split.
      - intros a Hout. pose proof (u64_range a) as Ha.
        unfold iblocks, FL_IFR, FL_ISTATE_N, FL_WIN_N in Hout. cbn [ip_p ip_w ip_strm] in Hout.
        replace (w =? 0) with false in Hout by (symmetry; apply Z.eqb_neq; clear - W1; lia).
        cbn [outside wz map fst snd app] in Hout. unfold in_rng in Hout. change (Z_to_bv 64) with zw in Hout.
        destruct Hout as (H1 & H2 & H3 & H4 & H5 & _).
        rewrite u_zw_small in H1 by (clear - Csp; lia). rewrite u_zw_small in H4 by (clear - CS; lia). rewrite u_zw_small in H5 by (clear - W1 WZ HZC SP47; lia).
        rewrite (HE5 a); [| unfold INF_FRAME, INF_SCRATCH; clear - H1; lia | clear - H4; lia | clear - H5; lia].
        apply EQ1. clear - H4. lia.
      - intros x Hx. apply Hg5. subst M1. apply wbytes_grows. exact Hx. }
    cbn [zret_of_icall zr_rc zr_consumed zr_output zr_strm].
    split; [exact A10|]. split; [exact A2|].
    split.
    { intros rg Hrg. unfold FL_KEEP in Hrg. cbn [In] in Hrg.
      destruct Hrg as [<-|[<-|Hrg]]; [exact A3 | exact A4 |]. apply Asv. cbn [In]. clear - Hrg. tauto. }
    intros NRR.
    unfold CCUR in HCC5. cbn [cvB cvW cv_NI cv_NO] in HCC5. destruct HCC5 as (V1 & V2 & V3 & V4 & V5 & V6 & V7).
    rewrite Hno5.
    split; [rewrite arr_slice_length; clear - Hput; lia|].
    split; [rewrite <- Hno5 in *; clear - V1 V2 V3; lia|].
    pose proof (uwc_fields sF (ic_outbuf cx) (ir_put rx) (ir_out rx - ir_left rx)) as UF. cbv zeta in UF. fold s5 in UF.
    destruct UF as (_ & _ & _ & _ & _ & U6 & _ & _ & _ & _ & U11).
    assert (Hblk5 : is_window_blk s5 = Some b) by (rewrite U11; exact F18).
    assert (Hwl5 : arr_len (is_window s5) = 32768).
    { destruct U' as ((SR' & _ & WS') & _). rewrite Hblk5 in WS'. destruct WS' as [L' _]. destruct HXS5 as (_ & Hwb5 & _). rewrite L', Hwb5. reflexivity. }
    destruct CM5 as [Rod5 Sc5 Lens5 Work5 Codes5 Win5 In5 Out5 Zs5 _ _ _ _ _].
    cbn [cvB cvW cv_sp cv_R0 cv_ZP cv_S cv_I0 cv_P0 cv_WB cv_NI cv_NO cv_WN cv_flush cv_TOT0 cv_fa cv_ff cv_opq] in *.
    split.
    {
      unfold FL_IREP, ISREP6, IRANGES. cbn [ip_p ip_strm ip_w]. unfold FL_ISTATE_N, FL_WIN_N.
      split; [| split].
      - split; [exact Sc5|]. split; [exact Lens5|]. split; [exact Work5|]. split; [exact Codes5|].
        split; [intros _; rewrite Hwl5; apply Win5; clear; lia|].
        split; [rewrite Hblk5; split; [intros E; exfalso; clear - E W1; lia | intros E; discriminate E]|].
        intros _; exact Hwl5.
      - destruct U' as ((SR' & _) & _). destruct SR' as (Smode' & _). exact Smode'.
      - unfold IRANGES, FL_ISTATE_N, FL_WIN_N in RG. clear - RG W1 WZ HZC SP47. lia. }
    split.
    {
      unfold izs6 in Zs5. cbn [cvB cvW cv_ZP cv_S cv_I0 cv_P0 cv_fa cv_ff cv_opq] in Zs5.
      destruct Zs5 as (Z0 & Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z96).
      unfold izs_cells, cell8, cell4, FL_MSGA. cbn [zstrm_of_icall zs_total_in zs_total_out zs_adler zs_msg]. unfold cell in *.
      rewrite Z.add_0_r in Z0. rewrite Hno5 in Z24. rewrite FA, FF.
      replace (n - ic_next_in cf) with (ic_avail_in cf) by (clear - V3; lia).
      replace (NO - ir_put rx) with (ic_avail_out cf) by (rewrite <- Hno5; clear - V6; lia).
      repeat match goal with |- _ /\ _ => split end; assumption. }
    pose proof (arr_slice_length (ic_outbuf cf) 0 (ir_put rx)) as Hl.
    apply cells_holds; [clear - CP0; lia | rewrite Hl; clear - CP0 Hput; lia |].
    rewrite Hl. replace (Z.max 0 (ir_put rx)) with (ir_put rx) by (clear - Hput; lia).
    rewrite <- Hno5. eapply cells_extf; [exact Out5|]. intros i Hi. cbn beta. symmetry. apply nth_arr_slice0. exact Hi.
  Qed.
End INB.
End FXG.
