(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells AProto AMalloc_iface AFake0k_iface AProg_kit
     AFake_arep FsKit AF_fse_rd_iface AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_fse_rd_asm AH_huf_kit AH_huf_iface
     AH_huf_rdt2 AF_huf_dec_iface AF_huf_x1t_top AF_huf_x1t_bseg AF_huf_x1t_bdefs AF_huf_x1t_bpure.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import ZdHufStats ZdHufX1.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AF_huf_x1t_brs.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require SysStep.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXCell.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation zlen l := (Z.of_nat (length l)).
Notation isbyte := (fun v : Z => 0 <= v < 256).
Local Notation unpz := unpoisoned (only parsing).
Local Notation unpz_munch := unpoisoned_munch (only parsing).

Lemma x1s_shd_ap4 : forall E X B O k,
  bv_unsigned (edenot E X) < 2^47 -> 0 <= O -> O + 2^44 <= 2^64 ->
  0 <= bv_unsigned (edenot E B) + k -> bv_unsigned (edenot E B) + k + 4 <= 2^64 ->
  bv_unsigned (edenot E B) + k + 4 <= O \/ O + 2^44 <= bv_unsigned (edenot E B) + k ->
  flat E (SA (EAlu ALU_SRL X (ELit 3)) O) (elenZ E (ELit 1)) /\ flat E (SA B k) (elenZ E (ELit 4)) /\
  (estart E (SA (EAlu ALU_SRL X (ELit 3)) O) + elenZ E (ELit 1) <= estart E (SA B k) \/
   estart E (SA B k) + elenZ E (ELit 4) <= estart E (SA (EAlu ALU_SRL X (ELit 3)) O)).
Proof.
  intros E X B O k HX HO1 HO2 HB1 HB2 HAP.
  pose proof (bv_unsigned_in_range _ (edenot E X)) as [RX0 _].
  unfold flat, estart, elenZ. cbn [a_base a_off edenot].
  rewrite u_srl64.
  change (bv_unsigned (Z_to_bv 64 3)) with 3. change (bv_unsigned (Z_to_bv 64 1)) with 1.
  change (bv_unsigned (Z_to_bv 64 4)) with 4. change (2 ^ (3 mod 64)) with 8.
  assert (HD : bv_unsigned (edenot E X) / 8 < 2^44)
    by (apply Z.div_lt_upper_bound; [lia | change (8 * 2^44) with (2^47); lia]).
  assert (HD0 : 0 <= bv_unsigned (edenot E X) / 8) by (apply Z.div_pos; lia).
  repeat split; lia.
Qed.
Lemma x1s_lts : forall x y : word, bv_unsigned x < 2^63 -> bv_unsigned y < 2^63 -> bv_lts x y = bv_ltu x y.
Proof. intros x y Hx Hy. exact (PropExec.c_lts_small x y Hx Hy). Qed.

Section CANSEC1. Context {rc : runConstT}.
Section X1B.
  Variables (RNG : footprint) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m5 : amem) (SPV SPA lo DT DTB WK wksz FF r : Z).
  Hypothesis HY : x1A_hyps RNG SPV SPA lo DT DTB WK wksz FF.
  Hypothesis UDT : unpoisoned m5 DT (DT + DTB).
  Hypothesis UW : unpoisoned m5 WK (WK + wksz).
  Hypothesis ART0 : artcells m5.
  Hypothesis Hr : 0 <= r < 2^32.
  Variable POST : machine_state -> Prop.
  Notation ST pc mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 0x7fff8000) xs4
             xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Variables (n0 SRC : Z) (flags : word).
  Notation XBm := (XB m5 SPV SPA lo DT DTB WK wksz FF r).
  Local Ltac setreg_m r z' :=
    let v := StepF.reg_val r in
    lazymatch v with
    | Z_to_bv 64 z' => idtac
    | Z_to_bv 64 ?z => replace (Z_to_bv 64 z) with (Z_to_bv 64 z') by (first [ f_equal; lia | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia ])
    end.
  Local Ltac x1ez :=
    repeat lazymatch goal with
    | |- context [edenot ?E _] =>
        let b := eval unfold E in E in
        lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
          rewrite ?(ez_ok zv E (kE_atoms zv xs));
          let na := eval vm_compute in (length zv) in
          cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]
        end
    end.
  Local Ltac x1br :=
    lazymatch goal with
    | |- branch_taken _ _ _ = _ =>
        x1ez; unfold branch_taken; rewrite ?bv_ltu_Z, ?bv_eqb_Z, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
        rewrite ?Z.mod_small by lia;
        first [ apply Bool.negb_true_iff, Z.ltb_ge; lia | apply Z.ltb_lt; lia
              | apply Bool.negb_false_iff, Z.ltb_lt; lia | apply Z.ltb_ge; lia
              | apply Z.eqb_neq; lia | apply Z.eqb_eq; lia
              | apply Bool.negb_false_iff, Z.eqb_eq; lia | apply Bool.negb_true_iff, Z.eqb_neq; lia ]
    end.
  Local Ltac x1es := unfold estart; cbn [a_base a_off]; x1ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
    rewrite ?Z.mod_small by lia.
  Local Ltac x1zs :=
    repeat match goal with
    | |- context [zsa ?a] => let s := eval vm_compute in (zsa a) in change (zsa a) with s
    | |- context [zle ?a] => let s := eval vm_compute in (zle a) in change (zle a) with s
    end.
  Section SRT.
  Variables (hw rank : list Z) (nbs tl dtd : Z).
  Hypothesis STATS : huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl.
  Hypothesis TLR : 1 <= tl <= 12.
  Hypothesis NBSR : 2 <= nbs <= 256.
  Hypothesis LHW : zlen hw = 256.
  Hypothesis BHW : Forall isbyte hw.
  Hypothesis LRK : zlen rank = 13.
  Notation ws := (firstn (Z.to_nat nbs) hw).
  Definition SINV (i : Z) (rst : list Z) : Prop := forall v, 0 <= v <= tl -> Znth v rst = xsym rank v + hcount (firstn (Z.to_nat i) ws) v.
  Lemma ws_len : FseNCount.Zlength ws = nbs.
  Proof. unfold FseNCount.Zlength. rewrite length_firstn. lia. Qed.
  Lemma ws_nth : forall i, 0 <= i < nbs -> Znth i ws = Znth i hw.
  Proof.
    intros i Hi. unfold Znth. rewrite <- (firstn_skipn (Z.to_nat nbs) hw) at 2.
    rewrite app_nth1 by (rewrite length_firstn; lia). reflexivity.
  Qed.
  Lemma sinv0 : forall rst, (forall v, 0 <= v <= tl -> Znth v rst = xsym rank v) -> SINV 0 rst.
  Proof. intros rst H v Hv. rewrite (H v Hv). change (Z.to_nat 0) with 0%nat. rewrite firstn_O. unfold hcount. cbn. lia. Qed.
  Lemma sinv_end : forall i rst, nbs <= i -> SINV i rst -> SINV nbs rst.
  Proof. intros i rst Hi H v Hv. rewrite (H v Hv). rewrite !firstn_firstn. do 2 f_equal. f_equal. lia. Qed.
  Lemma sort_unit : forall j rst, 0 <= j < nbs -> SINV j rst -> zlen rst = 13 ->
    0 <= Znth j hw <= tl /\ 0 <= Znth (Znth j hw) rst < nbs /\ SINV (j + 1) (Zupd (Znth j hw) (Znth (Znth j hw) rst + 1) rst).
  Proof.
    intros j rst Hj SI RL. pose proof ws_len as WL.
    destruct (sort_slot ws rank tl STATS j (Znth j hw) ltac:(rewrite WL; lia) (ws_nth j Hj)) as [WR SL].
    rewrite <- (SI (Znth j hw) WR) in SL. rewrite WL in SL.
    split; [exact WR|]. split; [exact SL|].
    intros v Hv. unfold SINV in SI.
    rewrite (sort_step ws rank tl STATS j (Znth j hw) rst ltac:(rewrite WL; lia) (ws_nth j Hj) ltac:(unfold FseNCount.Zlength; lia) SI v Hv). reflexivity.
  Qed.
  Notation NHW := (18446744073709551615 - (WK + 1236)) (only parsing).
  Notation NRS := (18446744073709551615 - (WK + 52)) (only parsing).
  Notation NSY := (18446744073709551615 - (WK + 980)) (only parsing).
  Notation STQ pc mm x5 x6 x7 xa0 xa2 xa3 xa4 xa5 x28 x29 x30 x31 :=
    (ST pc mm (Z_to_bv 64 0x80454) x5 x6 x7 xa0 (Z_to_bv 64 (WK + 52)) xa2 xa3 xa4 xa5 (Z_to_bv 64 nbs) (Z_to_bv 64 (WK / 8))
        (Z_to_bv 64 FF) (Z_to_bv 64 r) (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 18446744073709551572) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 n0) (Z_to_bv 64 SRC) flags (Z_to_bv 64 (FF + 48))
        x28 x29 x30 x31).
  Notation STS mm xa0 xa2 xa3 xa4 xa5 x6 x7 x28 x29 :=
    (ST 0x80c20 mm (Z_to_bv 64 0x80454) (Z_to_bv 64 (nbs - 4)) x6 x7 xa0 (Z_to_bv 64 (WK + 52)) xa2 xa3 xa4 xa5 (Z_to_bv 64 nbs) (Z_to_bv 64 (WK / 8))
        (Z_to_bv 64 FF) (Z_to_bv 64 r) (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 18446744073709551572) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 n0) (Z_to_bv 64 SRC) flags (Z_to_bv 64 (FF + 48))
        x28 x29 (Z_to_bv 64 dtd) (Z_to_bv 64 WK)).
  Notation STU pc mm n xa2 xa5 x29 x30 x31 :=
    (STQ pc mm (Z_to_bv 64 (nbs - 4)) (Z_to_bv 64 13) (Z_to_bv 64 255) (Z_to_bv 64 NSY) xa2 (Z_to_bv 64 NRS) (Z_to_bv 64 NHW) xa5 (Z_to_bv 64 n) x29 x30 x31).
  Notation STT mm n x5 x6 xa2 x28 x30 x31 :=
    (STQ 0x80ef4 mm x5 x6 (Z_to_bv 64 (WK + 980)) (Z_to_bv 64 NSY) xa2 (Z_to_bv 64 NRS) (Z_to_bv 64 13) (Z_to_bv 64 255) x28 (Z_to_bv 64 n) x30 x31).
  Notation STF mm x5 x6 xa0 xa2 xa4 xa5 x28 x29 x30 x31 :=
    (ST 0x80fa8 mm (Z_to_bv 64 0x80454) x5 x6 (Z_to_bv 64 (WK + 980)) xa0 (Z_to_bv 64 (WK + 52)) xa2 (Z_to_bv 64 NRS) xa4 xa5 (Z_to_bv 64 nbs) (Z_to_bv 64 (WK / 8))
        (Z_to_bv 64 FF) (Z_to_bv 64 r) (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 18446744073709551572) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 n0) (Z_to_bv 64 SRC) flags (Z_to_bv 64 (FF + 48))
        x28 x29 x30 x31).
  Notation XS jA jA2 jC jD jB jE := (XBm hw rank tl (Z_to_bv 64 (WK + 980)) jA jA2 jC jD jB jE).
  Definition x1_sortA_stmt : Prop := forall m1 (dt rst : list Z) (syb jA jA2 jC jD jB jE : list byte) (k176 : word) xa0 xa2 xa3 xa4 xa5 x6 x7 x28 x29,
    XBm hw rank tl k176 jA jA2 jC jD jB jE dt rst syb m1 -> (forall v, 0 <= v <= tl -> Znth v rst = xsym rank v) ->
    (forall m2 (rst' : list Z) (syb' : list byte) (y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31 : word),
       XBm hw rank tl (Z_to_bv 64 (WK + 980)) jA jA2 jC jD jB jE dt rst' syb' m2 ->
       evtF bsegs RNG POST (STF m2 y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (STS m1 xa0 xa2 xa3 xa4 xa5 x6 x7 x28 x29).
  Local Ltac x1s_open I :=
    destruct I as (DTC & DTLEN & DTBY & HWC & RK & RST & RSTLEN & RSTNN & STW & SYC & SYLEN & WKR & STL & MI & MU & WM & FR);
    let HYc := fresh "HYc" in pose proof HY as HYc; unfold x1A_hyps in HYc; unfold KHIGH in HYc;
    destruct HYc as (D1 & D2 & D3 & W1 & W2 & W3 & W4 & L1 & L2 & L3 & S1 & S2 & S3 & S4 & DLO & WLO & DW & F1 & F2 & F3 & FB & DF & WF
                     & DB & RD & RDS & WB & RW & RWS & RF & RLO & RAI);
    pose proof atop_range as ATR;
    assert (RSTA : rng RNG SPA 216) by (eapply rng_sub'; [exact RLO| lia]);
    assert (RWK : rng RNG WK 1492) by (eapply rng_sub'; [exact RW| lia]);
    assert (SCL : WK + wksz <= ASHOFF \/ ASHOFF + 2^44 <= WK) by (clear - WB; unfold ablk, KLS, ASHOFF in *; lia);
    unfold ASHOFF in SCL;
    lazymatch type of MU with munch _ _ ?mm =>
      assert (UWm : unpz mm WK (WK + wksz)) by (eapply x1_unp_wkM; eassumption);
      pose proof (AF_huf_x1t_brs.unp_kshz mm WK (WK + wksz) WK 1484 UWm ltac:(lia) ltac:(lia) ltac:(lia)) as SZ
    end;
    assert (SR : rng RNG (ASHOFF + Z.shiftr WK 3) (Z.shiftr (1484 + WK mod 8 + 7) 3))
      by (rewrite !Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; rewrite <- shad_div;
          apply (rng_sub' _ _ _ _ _ RWS); unfold shspan; clear - W4 W1; Z.div_mod_to_equations; lia);
    unfold shspan in RWS;
    assert (AP1 : KXGoM.apart DT DTB SPA 216) by (clear - DLO L3 S3; unfold KXGoM.apart; lia);
    assert (AP2 : KXGoM.apart WK wksz SPA 216) by (clear - WLO L3 S3; unfold KXGoM.apart; lia);
    assert (AP3 : KXGoM.apart DT DTB WK wksz) by (exact DW);
    assert (AP4 : KXGoM.apart WK wksz FF 64) by (exact WF);
    assert (AP5 : KXGoM.apart DT DTB FF 64) by (exact DF);
    assert (AP6 : KXGoM.apart SPA 216 FF 64) by (clear - F3 L2 L3 S3 ATR; unfold KXGoM.apart; lia);
    clear DLO WLO DW WF DF;
    assert (HW256 : zlen (map (Z_to_bv 8) hw) = 256) by (rewrite length_map; exact LHW);
    assert (RKL : Z.of_nat (length (u32b rank)) = 52) by (rewrite u32b_length2, LRK; reflexivity);
    assert (RK52 : Z.of_nat (length (map (Z_to_bv 8) (u32b rank))) = 52) by (rewrite length_map; exact RKL);
    lazymatch type of RST with u8arr _ _ _ (map _ (u32b ?l)) =>
      assert (RSL : Z.of_nat (length (u32b l)) = 52) by (rewrite u32b_length2, RSTLEN; reflexivity);
      assert (RS52 : Z.of_nat (length (map (Z_to_bv 8) (u32b l))) = 52) by (rewrite length_map; exact RSL) end;
    unfold X1FRB in FR.
  Local Ltac x1kw1 i :=
    lazymatch goal with
    | |- kentry_ok _ _ _ (zk_ent (ZKWord _ 1 _)) =>
        cbn [kentry_ok zk_ent]; x1zs; split; [lia|]; split; [unfold flat; x1es; lia|];
        rewrite adenot_wa; x1es; rewrite ?Z.add_0_r;
        lazymatch goal with |- PropExec.rdn _ ?mm (wa ?a) _ = Some (word_to_le_bytes _ (Z_to_bv 64 ?v)) =>
          replace a with (WK + 1236 + i) by lia; replace v with (Znth i hw) by (first [assumption | symmetry; assumption]);
          lazymatch goal with HWC : u8arr _ mm (WK + 1236) _ |- _ =>
            apply (rdn_u8Z bsegs mm (WK + 1236) hw i HWC); [lia | apply (Forall_Znth _ hw i BHW); lia] end
        end
    end.
  Local Ltac x1kw4s w :=
    lazymatch goal with
    | |- kentry_ok _ _ _ (zk_ent (ZKWord _ 4 _)) =>
        cbn [kentry_ok zk_ent]; x1zs; split; [lia|]; split; [unfold flat; x1es; lia|];
        rewrite adenot_wa; x1es; rewrite ?Z.add_0_r;
        lazymatch goal with |- PropExec.rdn _ ?mm (wa ?a) _ = Some (word_to_le_bytes _ (Z_to_bv 64 ?v)) =>
          replace a with (WK + 52 + 4 * w) by lia;
          lazymatch goal with RST : u8arr _ mm (WK + 52) (map _ (u32b ?rst)) |- _ =>
            replace v with (Znth w rst) by (first [assumption | symmetry; assumption]);
            apply (rdn_u32b bsegs mm (WK + 52) rst w RST); lia end
        end
    end.
  Local Ltac x1s_mem_go E mm lg a4 v4 a1 w rs :=
    lazymatch goal with
    | RST : u8arr _ mm (WK + 52) (map _ (u32b ?rst)), DTC : u8arr _ mm DT ?bdt, HWC : u8arr _ mm (WK + 1236) ?bhw,
      RK : u8arr _ mm WK ?brk, SYC : u8arr _ mm (WK + 980) ?bsy, STW : stk _ mm (WK + 104) _, WKR : stk _ mm (WK + 1492) _,
      STL : stk _ mm lo SPA, WM : wmono _ m5 mm, FR : rw_cells _ mm SPA _, MU : munch _ m5 mm, MI : mem_inv _ mm,
      SYLEN : zlen ?bsy = 256, RSTLEN : zlen ?rst = 13, KXLF : log_flat E lg |- _ =>
        assert (EAR : estart E a4 = WK + 52 + 4 * w) by (x1es; lia);
        assert (EAS : estart E a1 = WK + 980 + rs) by (x1es; lia);
        assert (EVR : edenot E v4 = Z_to_bv 64 (rs + 1)) by (x1ez; first [reflexivity | f_equal; lia]);
        assert (LA : forall A n, (A + n <= WK + 52 + 4 * w \/ WK + 52 + 4 * w + 4 <= A) ->
                                 (A + n <= WK + 980 + rs \/ WK + 980 + rs + 1 <= A) -> log_apart E lg A n)
          by (intros A0 q0 H0 H1; cbn [log_apart]; rewrite EAR, EAS; cbn [Z.of_nat Pos.of_succ_nat]; repeat split; lia);
        pose proof (kx_u8arr_replay bsegs E mm lg (WK + 52) _ RST KXLF) as RSTm;
        cbn [replay] in RSTm; rewrite EAR, EVR, EAS in RSTm;
        try rewrite (replay1_apart _ (WK + 52) (map (Z_to_bv 8) (u32b rst)) (WK + 980 + rs)) in RSTm
          by (right; rewrite length_map, u32b_length2; lia);
        rewrite (AF_huf_x1t_brs.x1r_replay_u32b _ w (rs + 1) (WK + 52) (WK + 52 + 4 * w)) in RSTm by lia;
        try rewrite (replay1_apart _ (WK + 52) _ (WK + 980 + rs)) in RSTm
          by (right; rewrite length_map, u32b_length2, Zupd_length2; lia);
        pose proof (kx_u8arr_replay bsegs E mm lg (WK + 980) _ SYC KXLF) as SYm;
        assert (SYLENm : zlen (replay E lg (WK + 980) bsy) = 256) by (rewrite replay_length; exact SYLEN);
        assert (DTm : u8arr bsegs (mem_denot E mm lg) DT bdt)
          by (split; [apply (kx_bytes_at_log bsegs E mm lg DT _ (proj1 DTC) KXLF); apply LA; rewrite length_map; unfold KXGoM.apart in *; lia
                     | exact (kx_wr_at_log bsegs E mm lg DT _ (proj2 DTC))]);
        assert (HWm : u8arr bsegs (mem_denot E mm lg) (WK + 1236) bhw)
          by (split; [apply (kx_bytes_at_log bsegs E mm lg _ _ (proj1 HWC) KXLF); apply LA; rewrite length_map; lia
                     | exact (kx_wr_at_log bsegs E mm lg _ _ (proj2 HWC))]);
        assert (RKm : u8arr bsegs (mem_denot E mm lg) WK brk)
          by (split; [apply (kx_bytes_at_log bsegs E mm lg _ _ (proj1 RK) KXLF); apply LA; rewrite length_map; lia
                     | exact (kx_wr_at_log bsegs E mm lg _ _ (proj2 RK))]);
        pose proof (kx_stk_log bsegs E mm lg _ _ STW) as STWm;
        pose proof (kx_stk_log bsegs E mm lg _ _ WKR) as WKRm;
        pose proof (kx_stk_log bsegs E mm lg _ _ STL) as STLm;
        pose proof (kx_wmono_log bsegs E m5 mm lg WM) as WMm;
        pose proof (kx_rw_cells_log bsegs E mm lg _ _ FR KXLF
          ltac:(apply LA; unfold KXGoM.apart in *; cbn [cells_size csize Nat.add length]; lia)) as FRm;
        pose proof (kx_munch_log E _ m5 mm lg MU KXLF
          ltac:(cbn [log_inside]; rewrite EAR, EAS; repeat split; cbn; lia)) as MUm;
        let WV := fresh "WV" in let WV2 := fresh "WV2" in
        destruct (proj2 RST) as (_ & _ & WV); destruct (proj2 SYC) as (_ & _ & WV2);
        pose proof (kx_mem_inv_log bsegs E mm lg MI KXLF
          ltac:(cbn [log_wr]; rewrite EAR, EAS; repeat split; intros j Hj; cbn [Z.of_nat Pos.of_succ_nat] in Hj;
                first [ replace (WK + 52 + 4 * w + j) with (WK + 52 + (4 * w + j)) by lia; apply WV; rewrite length_map; lia
                      | replace (WK + 980 + rs + j) with (WK + 980 + (rs + j)) by lia; apply WV2; lia ])) as MIm;
        clear WV WV2
    end.
  Local Ltac x1s_mem w rs :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E ?mm ?lg) _) =>
      lazymatch lg with
      | [SE ?a4 4 ?v4; SE ?a1 1 _] => x1s_mem_go E mm lg a4 v4 a1 w rs
      | [SE ?a1 1 _; SE ?a4 4 ?v4] => x1s_mem_go E mm lg a4 v4 a1 w rs
      end
    end.
  Local Ltac x1s_close :=
    unfold XB; do 6 (split; [eassumption|]); split; [rewrite Zupd_length2; eassumption|];
    split; [apply Forall_Zupd; [eassumption | lia]|]; do 8 (split; [eassumption|]); unfold X1FRB; eassumption.
  Local Ltac x1sxb :=
    x1ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia; lia.
  Local Ltac x1shd :=
    lazymatch goal with
    | |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) (elenZ ?E (ELit 1)) /\ flat ?E (SA ?B ?k) (elenZ ?E (ELit 4)) /\ _ =>
        apply (x1s_shd_ap4 E X B O k); [x1sxb | lia | lia | x1sxb | x1sxb | x1sxb]
    end.
  Local Ltac x1brs :=
    lazymatch goal with
    | |- branch_taken _ _ _ = _ =>
        x1ez; unfold branch_taken;
        rewrite ?bv_lts_zero_r;
        rewrite ?x1s_lts by (rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia; lia);
        rewrite ?bv_ltu_Z, ?bv_eqb_Z, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
        rewrite ?Z.mod_small by lia;
        first [ apply Bool.negb_true_iff, Z.ltb_ge; lia | apply Z.ltb_lt; lia
              | apply Bool.negb_false_iff, Z.ltb_lt; lia | apply Z.ltb_ge; lia
              | apply Z.eqb_neq; lia | apply Z.eqb_eq; lia
              | apply Bool.negb_false_iff, Z.eqb_eq; lia | apply Bool.negb_true_iff, Z.eqb_neq; lia
              | apply Z.leb_le; Z.div_mod_to_equations; lia | apply Z.leb_gt; Z.div_mod_to_equations; lia ]
    end.
  Local Ltac x1sa_mem :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E ?mm ?lg) _) =>
    lazymatch lg with [SE ?a 8 ?v] =>
    lazymatch goal with
    | RST : u8arr _ mm (WK + 52) ?brs, DTC : u8arr _ mm DT ?bdt, HWC : u8arr _ mm (WK + 1236) ?bhw, RK : u8arr _ mm WK ?brk,
      SYC : u8arr _ mm (WK + 980) ?bsy, STW : stk _ mm (WK + 104) _, WKR : stk _ mm (WK + 1492) _, STL : stk _ mm lo SPA,
      WM : wmono _ m5 mm, FR : rw_cells _ mm SPA _, MU : munch _ m5 mm, MI : mem_inv _ mm, KXLF : log_flat E lg |- _ =>
        assert (EA : estart E a = SPA + 176) by (x1es; lia);
        assert (EV : edenot E v = Z_to_bv 64 (WK + 980)) by (x1ez; first [reflexivity | f_equal; lia]);
        assert (LA : forall A n, A + n <= SPA + 176 \/ SPA + 184 <= A -> log_apart E lg A n)
          by (intros A0 q0 H0; cbn [log_apart]; rewrite EA; cbn [Z.of_nat Pos.of_succ_nat]; split; [lia | exact I]);
        repeat match goal with H : KXGoM.apart _ _ _ _ |- _ => unfold KXGoM.apart in H end;
        assert (DTm : u8arr bsegs (mem_denot E mm lg) DT bdt)
          by (split; [apply (kx_bytes_at_log bsegs E mm lg DT _ (proj1 DTC) KXLF); apply LA; rewrite length_map; lia
                     | exact (kx_wr_at_log bsegs E mm lg DT _ (proj2 DTC))]);
        assert (HWm : u8arr bsegs (mem_denot E mm lg) (WK + 1236) bhw)
          by (split; [apply (kx_bytes_at_log bsegs E mm lg _ _ (proj1 HWC) KXLF); apply LA; rewrite length_map; lia
                     | exact (kx_wr_at_log bsegs E mm lg _ _ (proj2 HWC))]);
        assert (RKm : u8arr bsegs (mem_denot E mm lg) WK brk)
          by (split; [apply (kx_bytes_at_log bsegs E mm lg _ _ (proj1 RK) KXLF); apply LA; rewrite length_map; lia
                     | exact (kx_wr_at_log bsegs E mm lg _ _ (proj2 RK))]);
        assert (RSTm : u8arr bsegs (mem_denot E mm lg) (WK + 52) brs)
          by (split; [apply (kx_bytes_at_log bsegs E mm lg _ _ (proj1 RST) KXLF); apply LA; rewrite length_map; lia
                     | exact (kx_wr_at_log bsegs E mm lg _ _ (proj2 RST))]);
        assert (SYm : u8arr bsegs (mem_denot E mm lg) (WK + 980) bsy)
          by (split; [apply (kx_bytes_at_log bsegs E mm lg _ _ (proj1 SYC) KXLF); apply LA; lia
                     | exact (kx_wr_at_log bsegs E mm lg _ _ (proj2 SYC))]);
        pose proof (kx_stk_log bsegs E mm lg _ _ STW) as STWm;
        pose proof (kx_stk_log bsegs E mm lg _ _ WKR) as WKRm;
        pose proof (kx_stk_log bsegs E mm lg _ _ STL) as STLm;
        pose proof (kx_wmono_log bsegs E m5 mm lg WM) as WMm;
        pose proof (kx_munch_log E _ m5 mm lg MU KXLF ltac:(cbn [log_inside]; rewrite EA; split; [cbn; lia | exact I])) as MUm;
        pose proof (SysStep.rw_cells_wr_at bsegs mm SPA _ 216 FR ltac:(cbn; lia)) as WRF;
        pose proof (kx_mem_inv_log bsegs E mm lg MI KXLF
          ltac:(cbn [log_wr]; rewrite EA; split;
                [exact (wr_at_covers bsegs mm SPA 216 (SPA + 176) 8 WRF ltac:(lia) ltac:(cbn; lia)) | exact I])) as MIm;
        kx_cells_split FR;
        lazymatch goal with H : rw_cells _ mm (SPA + 176) [C8 _] |- _ =>
          pose proof (kx_cell_store8 bsegs E mm [] a v [] (SPA + 176) _ KXLF H EA I) as HS; rewrite EV in HS; clear H end;
        repeat match goal with H : rw_cells _ mm ?A [?c] |- _ =>
          apply (kx_rw_cells_log bsegs E mm lg A [c]) in H; [ | exact KXLF | apply LA; cbn [cells_size csize]; lia ] end
    end end end.
  Local Ltac x1sa_close :=
    unfold XB; do 16 (split; [eassumption|]); unfold X1FRB; kx_cells_merge.
  Lemma x1_su0A : forall m1 (dt rst : list Z) (syb jA jA2 jC jD jB jE : list byte) (n : Z) xa2 xa5 x29 x30 x31,
    XS jA jA2 jC jD jB jE dt rst syb m1 -> 0 <= n -> n + 3 < nbs -> SINV (n + 0) rst ->
    (forall m2 (rst' : list Z) (syb' : list byte) (ya2 ya5 y30 : word),
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV (n + 0 + 1) rst' ->
       evtF bsegs RNG POST (STU 0x80cbc m2 n ya2 ya5 (Z_to_bv 64 (WK + n)) y30 x31)) ->
    evtF bsegs RNG POST (STU 0x80c48 m1 n xa2 xa5 x29 x30 x31).
  Proof.
    intros until x31; intros I HN HN3 SI K.
    x1s_open I.
    destruct (sort_unit (n + 0) rst ltac:(lia) SI RSTLEN) as (HWR & HSL & SI').
    pose proof (Forall_Znth _ hw (n + 0) BHW ltac:(lia)) as WBY; cbv beta in WBY.
    set (w := Znth (n + 0) hw) in *. set (rs := Znth w rst) in *.
    assert (Ew : w = Znth (n + 0) hw) by reflexivity. assert (Ers : rs = Znth w rst) by reflexivity. clearbody rs. clearbody w.
    kx_runFm [0x80cbc; 0x819cc] 60%nat
      [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZRange n 0 252; KZRange w 0 12; KZRange rs 0 255;
       KZWord (WK + 1236 + (n + 0)) 1%nat w; KZWord (WK + 52 + 4 * w) 4%nat rs; KZWr (WK + 52) 52; KZWr (WK + 980) 256;
       KZWord (SPA + 96) 8 WK; KZWord (SPA + 176) 8 (WK + 980);
       KZRange (WK / 8) 0 (2^44 - 187); KZShZ ASHOFF WK 1484]
      [(WK + 1236, 256); (WK + 52, 52)] [(WK + 52, 52); (WK + 980, 256); (WK + 1236, 256); (SPA, 216)]
      [(WK + 1236 + (n + 0), 1)].
    all: try x1brs.
    all: try x1kw1 (n + 0).
    all: try x1kw4s w.
    all: try x1shd.
    kx_post_regs.
    x1s_mem w rs.
    try replace (nbs + -4) with (nbs - 4) by lia; try setreg_m 10 constr:(NSY); try setreg_m 13 constr:(NRS); try setreg_m 14 constr:(NHW); try (let v := eval vm_compute in (2 ^ 64 - 44) in replace (Z_to_bv 64 (-44)) with (Z_to_bv 64 v) by (apply Z_to_bv_eqm; vm_compute; reflexivity)); setreg_m 29 (WK + n); eapply K; [x1s_close | exact SI'].
  Qed.

  Lemma x1_su1A : forall m1 (dt rst : list Z) (syb jA jA2 jC jD jB jE : list byte) (n : Z) xa2 xa5 x30 x31,
    XS jA jA2 jC jD jB jE dt rst syb m1 -> 0 <= n -> n + 3 < nbs -> SINV (n + 1) rst ->
    (forall m2 (rst' : list Z) (syb' : list byte) (ya2 ya5 : word),
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV (n + 1 + 1) rst' ->
       evtF bsegs RNG POST (STU 0x80d30 m2 n ya2 ya5 (Z_to_bv 64 (WK + n)) (Z_to_bv 64 (n + 2)) x31)) ->
    evtF bsegs RNG POST (STU 0x80cbc m1 n xa2 xa5 (Z_to_bv 64 (WK + n)) x30 x31).
  Proof.
    intros until x31; intros I HN HN3 SI K.
    x1s_open I.
    destruct (sort_unit (n + 1) rst ltac:(lia) SI RSTLEN) as (HWR & HSL & SI').
    pose proof (Forall_Znth _ hw (n + 1) BHW ltac:(lia)) as WBY; cbv beta in WBY.
    set (w := Znth (n + 1) hw) in *. set (rs := Znth w rst) in *.
    assert (Ew : w = Znth (n + 1) hw) by reflexivity. assert (Ers : rs = Znth w rst) by reflexivity. clearbody rs. clearbody w.
    kx_runFm [0x80d30; 0x819cc] 60%nat
      [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZRange n 0 252; KZRange w 0 12; KZRange rs 0 255;
       KZWord (WK + 1236 + (n + 1)) 1%nat w; KZWord (WK + 52 + 4 * w) 4%nat rs; KZWr (WK + 52) 52; KZWr (WK + 980) 256;
       KZWord (SPA + 96) 8 WK; KZWord (SPA + 176) 8 (WK + 980);
       KZRange (WK / 8) 0 (2^44 - 187); KZShZ ASHOFF WK 1484]
      [(WK + 1236, 256); (WK + 52, 52)] [(WK + 52, 52); (WK + 980, 256); (WK + 1236, 256); (SPA, 216)]
      [(WK + 1236 + (n + 1), 1)].
    all: try x1brs.
    all: try x1kw1 (n + 1).
    all: try x1kw4s w.
    all: try x1shd.
    kx_post_regs.
    x1s_mem w rs.
    try replace (nbs + -4) with (nbs - 4) by lia; try setreg_m 10 constr:(NSY); try setreg_m 13 constr:(NRS); try setreg_m 14 constr:(NHW); try (let v := eval vm_compute in (2 ^ 64 - 44) in replace (Z_to_bv 64 (-44)) with (Z_to_bv 64 v) by (apply Z_to_bv_eqm; vm_compute; reflexivity)); setreg_m 29 (WK + n); setreg_m 30 (n + 2); eapply K; [x1s_close | exact SI'].
  Qed.

  Lemma x1_su2A : forall m1 (dt rst : list Z) (syb jA jA2 jC jD jB jE : list byte) (n : Z) xa2 xa5 x31,
    XS jA jA2 jC jD jB jE dt rst syb m1 -> 0 <= n -> n + 3 < nbs -> SINV (n + 2) rst ->
    (forall m2 (rst' : list Z) (syb' : list byte) (ya2 y30 y31 : word),
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV (n + 2 + 1) rst' ->
       evtF bsegs RNG POST (STU 0x80da0 m2 n ya2 (Z_to_bv 64 (n + 3)) (Z_to_bv 64 (WK + n)) y30 y31)) ->
    evtF bsegs RNG POST (STU 0x80d30 m1 n xa2 xa5 (Z_to_bv 64 (WK + n)) (Z_to_bv 64 (n + 2)) x31).
  Proof.
    intros until x31; intros I HN HN3 SI K.
    x1s_open I.
    destruct (sort_unit (n + 2) rst ltac:(lia) SI RSTLEN) as (HWR & HSL & SI').
    pose proof (Forall_Znth _ hw (n + 2) BHW ltac:(lia)) as WBY; cbv beta in WBY.
    set (w := Znth (n + 2) hw) in *. set (rs := Znth w rst) in *.
    assert (Ew : w = Znth (n + 2) hw) by reflexivity. assert (Ers : rs = Znth w rst) by reflexivity. clearbody rs. clearbody w.
    kx_runFm [0x80da0; 0x819cc] 60%nat
      [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZRange n 0 252; KZRange w 0 12; KZRange rs 0 255;
       KZWord (WK + 1236 + (n + 2)) 1%nat w; KZWord (WK + 52 + 4 * w) 4%nat rs; KZWr (WK + 52) 52; KZWr (WK + 980) 256;
       KZWord (SPA + 96) 8 WK; KZWord (SPA + 176) 8 (WK + 980);
       KZRange (WK / 8) 0 (2^44 - 187); KZShZ ASHOFF WK 1484]
      [(WK + 1236, 256); (WK + 52, 52)] [(WK + 52, 52); (WK + 980, 256); (WK + 1236, 256); (SPA, 216)]
      [(WK + 1236 + (n + 2), 1)].
    all: try x1brs.
    all: try x1kw1 (n + 2).
    all: try x1kw4s w.
    all: try x1shd.
    kx_post_regs.
    x1s_mem w rs.
    try replace (nbs + -4) with (nbs - 4) by lia; try setreg_m 10 constr:(NSY); try setreg_m 13 constr:(NRS); try setreg_m 14 constr:(NHW); try (let v := eval vm_compute in (2 ^ 64 - 44) in replace (Z_to_bv 64 (-44)) with (Z_to_bv 64 v) by (apply Z_to_bv_eqm; vm_compute; reflexivity)); setreg_m 29 (WK + n); setreg_m 15 (n + 3); eapply K; [x1s_close | exact SI'].
  Qed.

  Lemma x1_su3A_1 : forall m1 (dt rst : list Z) (syb jA jA2 jC jD jB jE : list byte) (n : Z) xa2 x30 x31,
    n + 4 <= nbs - 4 ->
    XS jA jA2 jC jD jB jE dt rst syb m1 -> 0 <= n -> n + 3 < nbs -> SINV (n + 3) rst ->
    (forall m2 (rst' : list Z) (syb' : list byte) (ya2 ya5 y29 y30 y31 : word), n + 4 <= nbs - 4 ->
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV (n + 4) rst' ->
       evtF bsegs RNG POST (STU 0x80c48 m2 (n + 4) ya2 ya5 y29 y30 y31)) ->
    (forall m2 (rst' : list Z) (syb' : list byte) (y5 y6 ya2 y28 y30 y31 : word), nbs - 4 < n + 4 -> n + 4 < nbs ->
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV (n + 4) rst' ->
       evtF bsegs RNG POST (STT m2 (n + 4) y5 y6 ya2 y28 y30 y31)) ->
    (forall m2 (rst' : list Z) (syb' : list byte) (y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31 : word), nbs <= n + 4 ->
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV (n + 4) rst' ->
       evtF bsegs RNG POST (STF m2 y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (STU 0x80da0 m1 n xa2 (Z_to_bv 64 (n + 3)) (Z_to_bv 64 (WK + n)) x30 x31).
  Proof.
    intros until x31; intros C1 I HN HN3 SI KH KT KE.
    x1s_open I.
    destruct (sort_unit (n + 3) rst ltac:(lia) SI RSTLEN) as (HWR & HSL & SI').
    pose proof (Forall_Znth _ hw (n + 3) BHW ltac:(lia)) as WBY; cbv beta in WBY.
    set (w := Znth (n + 3) hw) in *. set (rs := Znth w rst) in *.
    assert (Ew : w = Znth (n + 3) hw) by reflexivity. assert (Ers : rs = Znth w rst) by reflexivity. clearbody rs. clearbody w.
    kx_runFmd [0x80c48; 0x80ef4; 0x80fa8; 0x819cc] 60%nat [true]
      [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZRange n 0 252; KZRange w 0 12; KZRange rs 0 255;
       KZWord (WK + 1236 + (n + 3)) 1%nat w; KZWord (WK + 52 + 4 * w) 4%nat rs; KZWr (WK + 52) 52; KZWr (WK + 980) 256;
       KZWord (SPA + 96) 8 WK; KZWord (SPA + 176) 8 (WK + 980);
       KZRange (WK / 8) 0 (2^44 - 187); KZShZ ASHOFF WK 1484]
      [(WK + 1236, 256); (WK + 52, 52)] [(WK + 52, 52); (WK + 980, 256); (WK + 1236, 256); (SPA, 216)]
      [(WK + 1236 + (n + 3), 1)].
    all: try x1brs.
    all: try x1kw1 (n + 3).
    all: try x1kw4s w.
    all: try x1shd.
    kx_post_regs.
    x1s_mem w rs.
    try replace (nbs + -4) with (nbs - 4) by lia; try setreg_m 10 constr:(NSY); try setreg_m 13 constr:(NRS); try setreg_m 14 constr:(NHW); try (let v := eval vm_compute in (2 ^ 64 - 44) in replace (Z_to_bv 64 (-44)) with (Z_to_bv 64 v) by (apply Z_to_bv_eqm; vm_compute; reflexivity)); replace (n + 3 + 1) with (n + 4) in SI' by lia; setreg_m 28 (n + 4); eapply KH; [lia | x1s_close | exact SI'].
  Qed.

  Lemma x1_su3A_2 : forall m1 (dt rst : list Z) (syb jA jA2 jC jD jB jE : list byte) (n : Z) xa2 x30 x31,
    nbs - 4 < n + 4 -> n + 4 < nbs ->
    XS jA jA2 jC jD jB jE dt rst syb m1 -> 0 <= n -> n + 3 < nbs -> SINV (n + 3) rst ->
    (forall m2 (rst' : list Z) (syb' : list byte) (ya2 ya5 y29 y30 y31 : word), n + 4 <= nbs - 4 ->
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV (n + 4) rst' ->
       evtF bsegs RNG POST (STU 0x80c48 m2 (n + 4) ya2 ya5 y29 y30 y31)) ->
    (forall m2 (rst' : list Z) (syb' : list byte) (y5 y6 ya2 y28 y30 y31 : word), nbs - 4 < n + 4 -> n + 4 < nbs ->
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV (n + 4) rst' ->
       evtF bsegs RNG POST (STT m2 (n + 4) y5 y6 ya2 y28 y30 y31)) ->
    (forall m2 (rst' : list Z) (syb' : list byte) (y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31 : word), nbs <= n + 4 ->
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV (n + 4) rst' ->
       evtF bsegs RNG POST (STF m2 y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (STU 0x80da0 m1 n xa2 (Z_to_bv 64 (n + 3)) (Z_to_bv 64 (WK + n)) x30 x31).
  Proof.
    intros until x31; intros C1 C2 I HN HN3 SI KH KT KE.
    x1s_open I.
    destruct (sort_unit (n + 3) rst ltac:(lia) SI RSTLEN) as (HWR & HSL & SI').
    pose proof (Forall_Znth _ hw (n + 3) BHW ltac:(lia)) as WBY; cbv beta in WBY.
    set (w := Znth (n + 3) hw) in *. set (rs := Znth w rst) in *.
    assert (Ew : w = Znth (n + 3) hw) by reflexivity. assert (Ers : rs = Znth w rst) by reflexivity. clearbody rs. clearbody w.
    kx_runFmd [0x80c48; 0x80ef4; 0x80fa8; 0x819cc] 60%nat [false; true]
      [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZRange n 0 252; KZRange w 0 12; KZRange rs 0 255;
       KZWord (WK + 1236 + (n + 3)) 1%nat w; KZWord (WK + 52 + 4 * w) 4%nat rs; KZWr (WK + 52) 52; KZWr (WK + 980) 256;
       KZWord (SPA + 96) 8 WK; KZWord (SPA + 176) 8 (WK + 980);
       KZRange (WK / 8) 0 (2^44 - 187); KZShZ ASHOFF WK 1484]
      [(WK + 1236, 256); (WK + 52, 52)] [(WK + 52, 52); (WK + 980, 256); (WK + 1236, 256); (SPA, 216)]
      [(WK + 1236 + (n + 3), 1)].
    all: try x1brs.
    all: try x1kw1 (n + 3).
    all: try x1kw4s w.
    all: try x1shd.
    kx_post_regs.
    x1s_mem w rs.
    try replace (nbs + -4) with (nbs - 4) by lia; try setreg_m 10 constr:(NSY); try setreg_m 13 constr:(NRS); try setreg_m 14 constr:(NHW); try (let v := eval vm_compute in (2 ^ 64 - 44) in replace (Z_to_bv 64 (-44)) with (Z_to_bv 64 v) by (apply Z_to_bv_eqm; vm_compute; reflexivity)); replace (n + 3 + 1) with (n + 4) in SI' by lia; setreg_m 29 (n + 4); eapply KT; [lia | lia | x1s_close | exact SI'].
  Qed.

  Lemma x1_su3A_3 : forall m1 (dt rst : list Z) (syb jA jA2 jC jD jB jE : list byte) (n : Z) xa2 x30 x31,
    nbs - 4 < n + 4 -> nbs <= n + 4 ->
    XS jA jA2 jC jD jB jE dt rst syb m1 -> 0 <= n -> n + 3 < nbs -> SINV (n + 3) rst ->
    (forall m2 (rst' : list Z) (syb' : list byte) (ya2 ya5 y29 y30 y31 : word), n + 4 <= nbs - 4 ->
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV (n + 4) rst' ->
       evtF bsegs RNG POST (STU 0x80c48 m2 (n + 4) ya2 ya5 y29 y30 y31)) ->
    (forall m2 (rst' : list Z) (syb' : list byte) (y5 y6 ya2 y28 y30 y31 : word), nbs - 4 < n + 4 -> n + 4 < nbs ->
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV (n + 4) rst' ->
       evtF bsegs RNG POST (STT m2 (n + 4) y5 y6 ya2 y28 y30 y31)) ->
    (forall m2 (rst' : list Z) (syb' : list byte) (y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31 : word), nbs <= n + 4 ->
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV (n + 4) rst' ->
       evtF bsegs RNG POST (STF m2 y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (STU 0x80da0 m1 n xa2 (Z_to_bv 64 (n + 3)) (Z_to_bv 64 (WK + n)) x30 x31).
  Proof.
    intros until x31; intros C1 C2 I HN HN3 SI KH KT KE.
    x1s_open I.
    destruct (sort_unit (n + 3) rst ltac:(lia) SI RSTLEN) as (HWR & HSL & SI').
    pose proof (Forall_Znth _ hw (n + 3) BHW ltac:(lia)) as WBY; cbv beta in WBY.
    set (w := Znth (n + 3) hw) in *. set (rs := Znth w rst) in *.
    assert (Ew : w = Znth (n + 3) hw) by reflexivity. assert (Ers : rs = Znth w rst) by reflexivity. clearbody rs. clearbody w.
    kx_runFmd [0x80c48; 0x80ef4; 0x80fa8; 0x819cc] 60%nat [false; false]
      [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZRange n 0 252; KZRange w 0 12; KZRange rs 0 255;
       KZWord (WK + 1236 + (n + 3)) 1%nat w; KZWord (WK + 52 + 4 * w) 4%nat rs; KZWr (WK + 52) 52; KZWr (WK + 980) 256;
       KZWord (SPA + 96) 8 WK; KZWord (SPA + 176) 8 (WK + 980);
       KZRange (WK / 8) 0 (2^44 - 187); KZShZ ASHOFF WK 1484]
      [(WK + 1236, 256); (WK + 52, 52)] [(WK + 52, 52); (WK + 980, 256); (WK + 1236, 256); (SPA, 216)]
      [(WK + 1236 + (n + 3), 1)].
    all: try x1brs.
    all: try x1kw1 (n + 3).
    all: try x1kw4s w.
    all: try x1shd.
    kx_post_regs.
    x1s_mem w rs.
    try replace (nbs + -4) with (nbs - 4) by lia; try setreg_m 10 constr:(NSY); try setreg_m 13 constr:(NRS); try setreg_m 14 constr:(NHW); try (let v := eval vm_compute in (2 ^ 64 - 44) in replace (Z_to_bv 64 (-44)) with (Z_to_bv 64 v) by (apply Z_to_bv_eqm; vm_compute; reflexivity)); replace (n + 3 + 1) with (n + 4) in SI' by lia; eapply KE; [lia | x1s_close | exact SI'].
  Qed.

  Lemma x1_su3A : forall m1 (dt rst : list Z) (syb jA jA2 jC jD jB jE : list byte) (n : Z) xa2 x30 x31,
    XS jA jA2 jC jD jB jE dt rst syb m1 -> 0 <= n -> n + 3 < nbs -> SINV (n + 3) rst ->
    (forall m2 (rst' : list Z) (syb' : list byte) (ya2 ya5 y29 y30 y31 : word), n + 4 <= nbs - 4 ->
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV (n + 4) rst' ->
       evtF bsegs RNG POST (STU 0x80c48 m2 (n + 4) ya2 ya5 y29 y30 y31)) ->
    (forall m2 (rst' : list Z) (syb' : list byte) (y5 y6 ya2 y28 y30 y31 : word), nbs - 4 < n + 4 -> n + 4 < nbs ->
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV (n + 4) rst' ->
       evtF bsegs RNG POST (STT m2 (n + 4) y5 y6 ya2 y28 y30 y31)) ->
    (forall m2 (rst' : list Z) (syb' : list byte) (y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31 : word), nbs <= n + 4 ->
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV (n + 4) rst' ->
       evtF bsegs RNG POST (STF m2 y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (STU 0x80da0 m1 n xa2 (Z_to_bv 64 (n + 3)) (Z_to_bv 64 (WK + n)) x30 x31).
  Proof.
    intros until x31; intros I HN HN3 SI KH KT KE.
    destruct (Z_le_gt_dec (n + 4) (nbs - 4)) as [C1|C1]; [| destruct (Z_lt_ge_dec (n + 4) nbs) as [C2|C2]].
    - apply (x1_su3A_1 m1 dt rst syb jA jA2 jC jD jB jE n xa2 x30 x31); first [eassumption | lia].
    - apply (x1_su3A_2 m1 dt rst syb jA jA2 jC jD jB jE n xa2 x30 x31); first [eassumption | lia].
    - apply (x1_su3A_3 m1 dt rst syb jA jA2 jC jD jB jE n xa2 x30 x31); first [eassumption | lia].
  Qed.
  Lemma x1_su_iterA : forall m1 (dt rst : list Z) (syb jA jA2 jC jD jB jE : list byte) (n : Z) xa2 xa5 x29 x30 x31,
    XS jA jA2 jC jD jB jE dt rst syb m1 -> 0 <= n -> n + 3 < nbs -> SINV n rst ->
    (forall m2 (rst' : list Z) (syb' : list byte) (ya2 ya5 y29 y30 y31 : word), n + 4 <= nbs - 4 ->
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV (n + 4) rst' ->
       evtF bsegs RNG POST (STU 0x80c48 m2 (n + 4) ya2 ya5 y29 y30 y31)) ->
    (forall m2 (rst' : list Z) (syb' : list byte) (y5 y6 ya2 y28 y30 y31 : word), nbs - 4 < n + 4 -> n + 4 < nbs ->
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV (n + 4) rst' ->
       evtF bsegs RNG POST (STT m2 (n + 4) y5 y6 ya2 y28 y30 y31)) ->
    (forall m2 (rst' : list Z) (syb' : list byte) (y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31 : word), nbs <= n + 4 ->
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV (n + 4) rst' ->
       evtF bsegs RNG POST (STF m2 y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (STU 0x80c48 m1 n xa2 xa5 x29 x30 x31).
  Proof.
    intros until x31; intros I HN HN3 SI KH KT KE.
    eapply x1_su0A; [exact I| exact HN| exact HN3| replace (n + 0) with n by lia; exact SI|]. intros m2 r2 b2 ya2 ya5 y30 I2 S2.
    eapply x1_su1A; [exact I2| exact HN| exact HN3| replace (n + 1) with (n + 0 + 1) by lia; exact S2|]. intros m3 r3 b3 za2 za5 I3 S3.
    eapply x1_su2A; [exact I3| exact HN| exact HN3| replace (n + 2) with (n + 1 + 1) by lia; exact S3|]. intros m4 r4 b4 wa2 w30 w31 I4 S4.
    eapply x1_su3A; [exact I4| exact HN| exact HN3| replace (n + 3) with (n + 2 + 1) by lia; exact S4| exact KH| exact KT| exact KE].
  Qed.

  Lemma x1_st_bodyA : forall m1 (dt rst : list Z) (syb jA jA2 jC jD jB jE : list byte) (n : Z) x5 x6 xa2 x28 x30 x31,
    XS jA jA2 jC jD jB jE dt rst syb m1 -> 0 <= n < nbs -> SINV n rst ->
    (forall m2 (rst' : list Z) (syb' : list byte) (y5 y6 ya2 y28 y30 y31 : word), n + 1 < nbs ->
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV (n + 1) rst' ->
       evtF bsegs RNG POST (STT m2 (n + 1) y5 y6 ya2 y28 y30 y31)) ->
    (forall m2 (rst' : list Z) (syb' : list byte) (y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31 : word), n + 1 = nbs ->
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV (n + 1) rst' ->
       evtF bsegs RNG POST (STF m2 y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (STT m1 n x5 x6 xa2 x28 x30 x31).
  Proof.
    intros until x31; intros I HN SI KH KE.
    x1s_open I.
    destruct (sort_unit (n) rst ltac:(lia) SI RSTLEN) as (HWR & HSL & SI').
    pose proof (Forall_Znth _ hw (n) BHW ltac:(lia)) as WBY; cbv beta in WBY.
    set (w := Znth (n) hw) in *. set (rs := Znth w rst) in *.
    assert (Ew : w = Znth (n) hw) by reflexivity. assert (Ers : rs = Znth w rst) by reflexivity. clearbody rs. clearbody w.
    destruct (Z.eq_dec (n + 1) nbs) as [CE|CE].
    - kx_runFmd [0x80ef4; 0x80fa8; 0x819cc] 60%nat [false]
      [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZRange n 0 255; KZRange w 0 12; KZRange rs 0 255;
       KZWord (WK + 1236 + (n)) 1%nat w; KZWord (WK + 52 + 4 * w) 4%nat rs; KZWr (WK + 52) 52; KZWr (WK + 980) 256;
       KZWord (SPA + 96) 8 WK; KZWord (SPA + 176) 8 (WK + 980);
       KZRange (WK / 8) 0 (2^44 - 187); KZShZ ASHOFF WK 1484]
      [(WK + 1236, 256); (WK + 52, 52)] [(WK + 52, 52); (WK + 980, 256); (WK + 1236, 256); (SPA, 216)]
      [(WK + 1236 + (n), 1)].
      all: try x1brs.
      all: try x1kw1 (n).
      all: try x1kw4s w.
      all: try x1shd.
      kx_post_regs.
      x1s_mem w rs.
      try replace (nbs + -4) with (nbs - 4) by lia; try setreg_m 10 constr:(NSY); try setreg_m 13 constr:(NRS); try setreg_m 14 constr:(NHW); try (let v := eval vm_compute in (2 ^ 64 - 44) in replace (Z_to_bv 64 (-44)) with (Z_to_bv 64 v) by (apply Z_to_bv_eqm; vm_compute; reflexivity)); eapply KE; [lia | x1s_close | exact SI'].
    - kx_runFmd [0x80ef4; 0x80fa8; 0x819cc] 60%nat [true]
      [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZRange n 0 255; KZRange w 0 12; KZRange rs 0 255;
       KZWord (WK + 1236 + (n)) 1%nat w; KZWord (WK + 52 + 4 * w) 4%nat rs; KZWr (WK + 52) 52; KZWr (WK + 980) 256;
       KZWord (SPA + 96) 8 WK; KZWord (SPA + 176) 8 (WK + 980);
       KZRange (WK / 8) 0 (2^44 - 187); KZShZ ASHOFF WK 1484]
      [(WK + 1236, 256); (WK + 52, 52)] [(WK + 52, 52); (WK + 980, 256); (WK + 1236, 256); (SPA, 216)]
      [(WK + 1236 + (n), 1)].
      all: try x1brs.
      all: try x1kw1 (n).
      all: try x1kw4s w.
      all: try x1shd.
      kx_post_regs.
      x1s_mem w rs.
      try replace (nbs + -4) with (nbs - 4) by lia; try setreg_m 10 constr:(NSY); try setreg_m 13 constr:(NRS); try setreg_m 14 constr:(NHW); try (let v := eval vm_compute in (2 ^ 64 - 44) in replace (Z_to_bv 64 (-44)) with (Z_to_bv 64 v) by (apply Z_to_bv_eqm; vm_compute; reflexivity)); setreg_m 29 (n + 1); eapply KH; [lia | x1s_close | exact SI'].
  Qed.

  Lemma x1_st_loopA : forall (f : nat) m1 (dt rst : list Z) (syb jA jA2 jC jD jB jE : list byte) (n : Z) x5 x6 xa2 x28 x30 x31,
    XS jA jA2 jC jD jB jE dt rst syb m1 -> 0 <= n -> n + Z.of_nat (S f) = nbs -> SINV n rst ->
    (forall m2 (rst' : list Z) (syb' : list byte) (y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31 : word),
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV nbs rst' ->
       evtF bsegs RNG POST (STF m2 y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (STT m1 n x5 x6 xa2 x28 x30 x31).
  Proof.
    induction f as [|f IH]; intros until x31; intros I HN HF SI KE.
    - eapply (x1_st_bodyA m1 dt rst syb jA jA2 jC jD jB jE n); [exact I| lia| exact SI| intros; exfalso; lia|].
      intros m2 rst' syb' y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31 Hn I2 S2. eapply KE; [exact I2| eapply sinv_end; [| exact S2]; lia].
    - eapply (x1_st_bodyA m1 dt rst syb jA jA2 jC jD jB jE n); [exact I| lia| exact SI| | intros; exfalso; lia].
      intros m2 rst' syb' y5 y6 ya2 y28 y30 y31 Hn I2 S2.
      eapply (IH m2 dt rst' syb' jA jA2 jC jD jB jE (n + 1)); [exact I2| lia| lia| exact S2| exact KE].
  Qed.

  Lemma x1_su_loopA : forall (f : nat) m1 (dt rst : list Z) (syb jA jA2 jC jD jB jE : list byte) (n : Z) xa2 xa5 x29 x30 x31,
    XS jA jA2 jC jD jB jE dt rst syb m1 -> 0 <= n -> n + 3 < nbs -> nbs - n <= 4 * Z.of_nat f -> SINV n rst ->
    (forall m2 (rst' : list Z) (syb' : list byte) (y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31 : word),
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV nbs rst' ->
       evtF bsegs RNG POST (STF m2 y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (STU 0x80c48 m1 n xa2 xa5 x29 x30 x31).
  Proof.
    induction f as [|f IH]; intros until x31; intros I HN HN3 HF SI KE; [exfalso; lia|].
    eapply x1_su_iterA; [exact I| exact HN| exact HN3| exact SI| | |].
    - intros m2 rst' syb' ya2 ya5 y29 y30 y31 Hn I2 S2.
      eapply (IH m2 dt rst' syb' jA jA2 jC jD jB jE (n + 4)); [exact I2| lia| lia| lia| exact S2| exact KE].
    - intros m2 rst' syb' y5 y6 ya2 y28 y30 y31 Hn1 Hn2 I2 S2.
      eapply (x1_st_loopA (Z.to_nat (nbs - (n + 4) - 1)) m2 dt rst' syb' jA jA2 jC jD jB jE (n + 4)); [exact I2| lia| lia| exact S2|].
      intros m3 rst3 syb3 z5 z6 za0 za2 za4 za5 z28 z29 z30 z31 I3 S3. eapply KE; [exact I3| exact S3].
    - intros m2 rst' syb' y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31 Hn I2 S2. eapply KE; [exact I2| eapply sinv_end; [exact Hn| exact S2]].
  Qed.

  Lemma x1_sortA : x1_sortA_stmt.
  Proof.
    unfold x1_sortA_stmt. intros until x29; intros I RS0 KE. pose proof (sinv0 rst RS0) as SI.
    x1s_open I.
    destruct (Z_lt_ge_dec nbs 4) as [CN|CN].
    - kx_runFmd [0x80c48; 0x80ef4; 0x80fa8; 0x819cc] 30%nat [true]
      [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZWr (SPA + 176) 8; KZWord (SPA + 96) 8 WK; KZRange (WK / 8) 0 (2^44 - 187)]
      (@nil (Z * Z)) [(SPA, 216)] (@nil (Z * Z)).
      all: try x1brs.
      kx_post_regs.
      x1sa_mem.
      try replace (nbs + -4) with (nbs - 4) by lia; try setreg_m 10 constr:(NSY); try setreg_m 13 constr:(NRS); try setreg_m 14 constr:(NHW); try (let v := eval vm_compute in (2 ^ 64 - 44) in replace (Z_to_bv 64 (-44)) with (Z_to_bv 64 v) by (apply Z_to_bv_eqm; vm_compute; reflexivity)); eapply (x1_st_loopA (Z.to_nat (nbs - 1)) _ dt rst syb jA jA2 jC jD jB jE 0); [x1sa_close | lia | lia | exact SI |]; intros; eapply KE; eassumption.
    - kx_runFmd [0x80c48; 0x80ef4; 0x80fa8; 0x819cc] 30%nat [false]
      [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZWr (SPA + 176) 8; KZWord (SPA + 96) 8 WK; KZRange (WK / 8) 0 (2^44 - 187)]
      (@nil (Z * Z)) [(SPA, 216)] (@nil (Z * Z)).
      all: try x1brs.
      kx_post_regs.
      x1sa_mem.
      try replace (nbs + -4) with (nbs - 4) by lia; try setreg_m 10 constr:(NSY); try setreg_m 13 constr:(NRS); try setreg_m 14 constr:(NHW); try (let v := eval vm_compute in (2 ^ 64 - 44) in replace (Z_to_bv 64 (-44)) with (Z_to_bv 64 v) by (apply Z_to_bv_eqm; vm_compute; reflexivity)); eapply (x1_su_loopA (Z.to_nat nbs) _ dt rst syb jA jA2 jC jD jB jE 0); [x1sa_close | lia | lia | lia | exact SI |]; intros; eapply KE; eassumption.
  Qed.

  End SRT.
End X1B.
End CANSEC1.
