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
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation zlen l := (Z.of_nat (length l)).
Notation isbyte := (fun v : Z => 0 <= v < 256).
Local Notation unpz := unpoisoned (only parsing).
Local Notation unpz_munch := unpoisoned_munch (only parsing).

Lemma u32b_upd4' : forall ws i x a b c d, 0 <= i < Z.of_nat (length ws) -> a = 4 * i -> b = 4 * i + 1 -> c = 4 * i + 2 -> d = 4 * i + 3 ->
  Zupd d ((x / 16777216) mod 256) (Zupd c ((x / 65536) mod 256) (Zupd b ((x / 256) mod 256) (Zupd a (x mod 256) (u32b ws))))
  = u32b (Zupd i x ws).
Proof. intros ws i x a b c d Hi -> -> -> ->. apply u32b_upd4. exact Hi. Qed.

Lemma rsinv_step : forall (rank r : list Z) k x, 0 <= k -> k + 1 < zlen r -> x = xsym rank (k + 1) ->
  (forall v, 0 <= v <= k -> Znth v r = xsym rank v) -> forall v, 0 <= v <= k + 1 -> Znth v (Zupd (k + 1) x r) = xsym rank v.
Proof.
  intros rank r k x Hk HL -> H v Hv. destruct (Z.eq_dec v (k + 1)) as [->|NE].
  - rewrite Znth_Zupd_same by (unfold FseNCount.Zlength; lia). reflexivity.
  - rewrite Znth_Zupd_other by lia. apply H. lia.
Qed.
Lemma rsinv_0 : forall (rank r : list Z), 0 < zlen r -> forall v, 0 <= v <= 0 -> Znth v (Zupd 0 0 r) = xsym rank v.
Proof. intros rank r HL v Hv. replace v with 0 by lia. rewrite Znth_Zupd_same by (unfold FseNCount.Zlength; lia). reflexivity. Qed.
Lemma rsinv_up : forall (rank rs : list Z) k x, 0 <= k < zlen rs -> x = xsym rank k ->
  (forall v, 0 <= v <= k - 1 -> Znth v rs = xsym rank v) -> forall v, 0 <= v <= k -> Znth v (Zupd k x rs) = xsym rank v.
Proof.
  intros rank rs k x HK -> H v Hv. destruct (Z.eq_dec v k) as [->|NE].
  - rewrite Znth_Zupd_same by (unfold FseNCount.Zlength; lia). reflexivity.
  - rewrite Znth_Zupd_other by lia. apply H. lia.
Qed.
Lemma unp_kshz : forall m L H A N, unpz m L H -> L <= A -> 0 <= N -> A + N + 8 <= H -> kshz_fact m ASHOFF A N.
Proof.
  intros m L H A N (HL & HH & HG) HA HN HAN x Hx.
  assert (G1 : 8 * (x / 8) <= x < 8 * (x / 8) + 8) by (Z.div_mod_to_equations; lia).
  destruct (HG (x / 8) ltac:(lia) ltac:(lia) ltac:(lia)) as (b & Hb & Hok).
  rewrite Z.min_l in Hok by lia. replace (8 * (x / 8) + 8 - 8 * (x / 8)) with 8 in Hok by lia.
  apply gran_ok_full in Hok; [| lia]. subst b.
  rewrite Z.shiftr_div_pow2 by lia. exact Hb.
Qed.
Lemma x1r_upd1 : forall (l : list Z) n v, (n < length l)%nat ->
  upd_bytes (map (Z_to_bv 8) l) n [Z_to_bv 8 v] = map (Z_to_bv 8) (FseNCount.upd_nat n v l).
Proof.
  induction l as [|h t IH]; intros n v Hn; [cbn in Hn; lia|].
  destruct n as [|n]; [reflexivity|].
  specialize (IH n v ltac:(cbn in Hn; lia)). unfold upd_bytes in IH |- *.
  cbn [map firstn skipn app FseNCount.upd_nat length Nat.add] in IH |- *. rewrite IH. reflexivity.
Qed.
Lemma x1r_rp1 : forall (l : list Z) A a v ws, A <= a < A + zlen l ->
  replay1 A (map (Z_to_bv 8) l) a (Z_to_bv 8 v :: ws) = replay1 A (map (Z_to_bv 8) (Zupd (a - A) v l)) (a + 1) ws.
Proof.
  intros l A a v ws Ha. cbn [replay1]. rewrite length_map.
  replace ((A <=? a) && (a <? A + zlen l))%bool with true
    by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  rewrite x1r_upd1 by lia. reflexivity.
Qed.
Lemma x1r_w4 : forall x, 0 <= x < 2^64 ->
  word_to_le_bytes 4 (Z_to_bv 64 x) = map (Z_to_bv 8) [x mod 256; (x / 256) mod 256; (x / 65536) mod 256; (x / 16777216) mod 256].
Proof.
  intros x Hx.
  assert (B8 : forall a b, a mod 256 = b mod 256 -> Z_to_bv 8 a = Z_to_bv 8 b).
  { intros a b Hab. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. exact Hab. }
  unfold word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_small by lia.
  cbn [Z_to_le_bytes map]. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  do 4 (apply (f_equal2 cons); [apply B8; Z.div_mod_to_equations; lia|]). reflexivity.
Qed.
Lemma x1r_replay_u32b : forall ws i x A a, a = A + 4 * i -> 0 <= i < zlen ws -> 0 <= x < 2^32 ->
  replay1 A (map (Z_to_bv 8) (u32b ws)) a (word_to_le_bytes 4 (Z_to_bv 64 x)) = map (Z_to_bv 8) (u32b (Zupd i x ws)).
Proof.
  intros ws i x A a -> Hi Hx.
  pose proof (u32b_length2 ws) as L.
  rewrite x1r_w4 by lia. cbn [map].
  rewrite x1r_rp1 by lia.
  rewrite x1r_rp1 by (rewrite Zupd_length2; lia).
  rewrite x1r_rp1 by (rewrite !Zupd_length2; lia).
  rewrite x1r_rp1 by (rewrite !Zupd_length2; lia).
  cbn [replay1].
  replace (A + 4 * i - A) with (4 * i) by lia. replace (A + 4 * i + 1 - A) with (4 * i + 1) by lia.
  replace (A + 4 * i + 1 + 1 - A) with (4 * i + 2) by lia. replace (A + 4 * i + 1 + 1 + 1 - A) with (4 * i + 3) by lia.
  rewrite u32b_upd4 by lia. reflexivity.
Qed.

Section CANSEC1. Context {rc : runConstT}.
Section X1B.
  Variables (RNG : footprint) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m5 : amem) (SPV SPA lo DT DTB WK wksz FF r : Z).
  Hypothesis HY : x1A_hyps RNG SPV SPA lo DT DTB WK wksz FF.
  Hypothesis UDT : unpoisoned m5 DT (DT + DTB).
  Hypothesis UW : unpoisoned m5 WK (WK + wksz).
  Hypothesis ART0 : artcells m5.
  Hypothesis Hr : 0 <= r < 2^32.
  Variable POST : machine_state -> Prop.
  Notation KZB := [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16);
     KZRange DT 0x629000 (2^47); KZRange WK 0x629000 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47);
     KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz] (only parsing).
  Notation ST pc mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 0x7fff8000) xs4
             xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Variables (n SRC : Z) (flags : word).
  Notation XBm := (XB m5 SPV SPA lo DT DTB WK wksz FF r).
  Local Ltac setreg_m r z' :=
    let v := StepF.reg_val r in
    lazymatch v with
    | Z_to_bv 64 z' => idtac
    | Z_to_bv 64 ?z => replace (Z_to_bv 64 z) with (Z_to_bv 64 z') by (first [ f_equal; lia | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia ])
    end.
  Section TL.
  Variables (hw rank : list Z) (nbs tl dtd : Z).
  Hypothesis STATS : huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl.
  Hypothesis TLR : 1 <= tl <= 12.
  Hypothesis NBSR : 2 <= nbs <= 256.
  Hypothesis LHW : zlen hw = 256.
  Hypothesis LRK : zlen rank = 13.
  Lemma rank_small : forall v, 0 <= v <= 12 -> 0 <= Znth v rank <= 256.
  Proof.
    intros v Hv. destruct STATS as (_ & (_ & LENW) & _ & _ & CNT & _). rewrite (CNT v Hv). unfold hcount.
    pose proof (count_occ_bound Z.eq_dec v (firstn (Z.to_nat nbs) hw)) as CB. unfold FseNCount.Zlength in LENW. lia.
  Qed.
  Lemma x1r_xsym_S : forall k, 0 <= k -> xsym rank (k + 1) = xsym rank k + Znth k rank.
  Proof. intros k Hk. unfold xsym. replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia. cbn [psum]. rewrite Z2Nat.id by lia. reflexivity. Qed.
  Lemma x1r_xsym_b : forall k, 0 <= k <= 13 -> 0 <= xsym rank k <= 256 * k.
  Proof.
    intros k Hk. unfold xsym.
    assert (P : forall q, (q <= 13)%nat -> 0 <= psum q (fun v => Znth v rank) <= 256 * Z.of_nat q).
    { intros q. induction q as [|q IH]; intros Hq; cbn [psum]; [lia|].
      pose proof (rank_small (Z.of_nat q) ltac:(lia)) as R. specialize (IH ltac:(lia)). lia. }
    pose proof (P (Z.to_nat k) ltac:(lia)) as Pk. rewrite Z2Nat.id in Pk by lia. exact Pk.
  Qed.
  Notation KZB2 := (KZB ++ [KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256]) (only parsing).
  Notation ST4 mm xa0 xa1 xa2 xa4 xa5 x6 x7 x28 x29 :=
    (ST 0x80718 mm (Z_to_bv 64 0x80454) (Z_to_bv 64 (nbs - 4)) x6 x7 xa0 xa1 xa2 (Z_to_bv 64 (0x7fff8000 + DT / 8)) xa4 xa5 (Z_to_bv 64 nbs) (Z_to_bv 64 tl)
        (Z_to_bv 64 FF) (Z_to_bv 64 r) (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 18446744073709551572) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 n) (Z_to_bv 64 SRC) flags (Z_to_bv 64 (FF + 48))
        x28 x29 (Z_to_bv 64 dtd) (Z_to_bv 64 WK)).
  Notation STS mm xa0 xa2 xa3 xa4 xa5 x6 x7 x28 x29 :=
    (ST 0x80c20 mm (Z_to_bv 64 0x80454) (Z_to_bv 64 (nbs - 4)) x6 x7 xa0 (Z_to_bv 64 (WK + 52)) xa2 xa3 xa4 xa5 (Z_to_bv 64 nbs) (Z_to_bv 64 (WK / 8))
        (Z_to_bv 64 FF) (Z_to_bv 64 r) (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 18446744073709551572) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 n) (Z_to_bv 64 SRC) flags (Z_to_bv 64 (FF + 48))
        x28 x29 (Z_to_bv 64 dtd) (Z_to_bv 64 WK)).
  Notation STK pc mm xa0 xa2 xa3 xa4 xa5 x6 x7 x28 x29 :=
    (ST pc mm (Z_to_bv 64 0x80454) (Z_to_bv 64 (nbs - 4)) x6 x7 xa0 (Z_to_bv 64 (WK + 52)) xa2 xa3 xa4 xa5 (Z_to_bv 64 nbs) (Z_to_bv 64 (WK / 8))
        (Z_to_bv 64 FF) (Z_to_bv 64 r) (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 18446744073709551572) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 n) (Z_to_bv 64 SRC) flags (Z_to_bv 64 (FF + 48))
        x28 x29 (Z_to_bv 64 dtd) (Z_to_bv 64 WK)).
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
  Local Ltac x1kw4 :=
    lazymatch goal with
    | |- kentry_ok _ _ _ (zk_ent (ZKWord _ 4 _)) =>
        cbn [kentry_ok zk_ent]; x1zs; split; [lia|]; split; [unfold flat; x1es; lia|];
        rewrite adenot_wa; x1es; rewrite ?Z.add_0_r
    end.
  Local Ltac x1rs_mem k x :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E ?mm ?lg) _) =>
    lazymatch lg with [SE ?a1 ?w1 ?v1] =>
    lazymatch goal with
    | RST : u8arr _ mm (WK + 52) _, DTC : u8arr _ mm DT ?bdt, HWC : u8arr _ mm (WK + 1236) ?bhw, RK : u8arr _ mm WK ?brk,
      SYC : u8arr _ mm (WK + 980) ?bsy, STW : stk _ mm (WK + 104) _, WKR : stk _ mm (WK + 1492) _, STL : stk _ mm lo SPA,
      WM : wmono _ m5 mm, FR : rw_cells _ mm SPA _, FFC : rw_cells _ mm FF _, MU : munch _ m5 mm, MI : mem_inv _ mm,
      KXLF : log_flat E lg |- _ =>
        assert (EA1 : estart E a1 = WK + 52 + 4 * k) by (x1es; lia);
        assert (EV1 : edenot E v1 = Z_to_bv 64 x) by (x1ez; first [reflexivity | f_equal; lia]);
        assert (LA : forall A n, A + n <= WK + 52 + 4 * k \/ WK + 52 + 4 * k + 4 <= A -> log_apart E lg A n)
          by (intros A0 n0 H0; cbn [log_apart]; rewrite EA1; cbn [Z.of_nat Pos.of_succ_nat]; split; [lia| exact I]);
        pose proof (kx_u8arr_replay bsegs E mm lg (WK + 52) _ RST KXLF) as RSTm;
        cbn [replay] in RSTm; rewrite EA1, EV1 in RSTm;
        rewrite (x1r_replay_u32b _ k x (WK + 52) (WK + 52 + 4 * k)) in RSTm by lia;
        assert (DTm : u8arr bsegs (mem_denot E mm lg) DT bdt)
          by (split; [apply (kx_bytes_at_log bsegs E mm lg DT _ (proj1 DTC) KXLF); apply LA; rewrite length_map; unfold KXGoM.apart in *; lia
                     | exact (kx_wr_at_log bsegs E mm lg DT _ (proj2 DTC))]);
        assert (HWm : u8arr bsegs (mem_denot E mm lg) (WK + 1236) bhw)
          by (split; [apply (kx_bytes_at_log bsegs E mm lg _ _ (proj1 HWC) KXLF); apply LA; rewrite length_map; lia
                     | exact (kx_wr_at_log bsegs E mm lg _ _ (proj2 HWC))]);
        assert (RKm : u8arr bsegs (mem_denot E mm lg) WK brk)
          by (split; [apply (kx_bytes_at_log bsegs E mm lg _ _ (proj1 RK) KXLF); apply LA; rewrite length_map; lia
                     | exact (kx_wr_at_log bsegs E mm lg _ _ (proj2 RK))]);
        assert (SYm : u8arr bsegs (mem_denot E mm lg) (WK + 980) bsy)
          by (split; [apply (kx_bytes_at_log bsegs E mm lg _ _ (proj1 SYC) KXLF); apply LA; lia
                     | exact (kx_wr_at_log bsegs E mm lg _ _ (proj2 SYC))]);
        pose proof (kx_stk_log bsegs E mm lg _ _ STW) as STWm;
        pose proof (kx_stk_log bsegs E mm lg _ _ WKR) as WKRm;
        pose proof (kx_stk_log bsegs E mm lg _ _ STL) as STLm;
        pose proof (kx_wmono_log bsegs E m5 mm lg WM) as WMm;
        pose proof (kx_rw_cells_log bsegs E mm lg _ _ FR KXLF
          ltac:(apply LA; unfold KXGoM.apart in *; cbn [cells_size csize Nat.add length]; lia)) as FRm;
        pose proof (kx_rw_cells_log bsegs E mm lg _ _ FFC KXLF
          ltac:(apply LA; unfold KXGoM.apart in *; cbn [cells_size csize Nat.add length]; lia)) as FFCm;
        pose proof (kx_munch_log E _ m5 mm lg MU KXLF ltac:(cbn [log_inside]; rewrite EA1; split; [cbn; lia| exact I])) as MUm;
        let WV := fresh "WV" in destruct (proj2 RST) as (_ & _ & WV);
        pose proof (kx_mem_inv_log bsegs E mm lg MI KXLF
          ltac:(cbn [log_wr]; rewrite EA1; split; [intros j Hj; cbn [Z.of_nat Pos.of_succ_nat] in Hj;
                replace (WK + 52 + 4 * k + j) with (WK + 52 + (4 * k + j)) by lia; apply WV; rewrite length_map; lia| exact I])) as MIm;
        clear WV
    end end end.
  Local Ltac x1rs_open I FFC :=
    destruct I as (DTC & DTLEN & DTBY & HWC & RK & RST & RSTLEN & RSTNN & STW & SYC & SYLEN & WKR & STL & MI & MU & WM & FR);
    let HYc := fresh "HYc" in pose proof HY as HYc; unfold x1A_hyps in HYc; unfold KHIGH in HYc;
    destruct HYc as (D1 & D2 & D3 & W1 & W2 & W3 & W4 & L1 & L2 & L3 & S1 & S2 & S3 & S4 & DLO & WLO & DW & F1 & F2 & F3 & FB & DF & WF
                     & DB & RD & RDS & WB & RW & RWS & RF & RLO & RAI);
    pose proof atop_range as ATR;
    assert (RSTA : rng RNG SPA 216) by (eapply rng_sub'; [exact RLO| lia]);
    assert (RWK : rng RNG WK 104) by (eapply rng_sub'; [exact RW| lia]);
    lazymatch type of MU with munch _ _ ?mm =>
      let UW1 := fresh "UW1" in
      assert (UW1 : unpz mm WK (WK + wksz)) by (eapply x1_unp_wkM; eassumption);
      pose proof (unp_kshz mm WK (WK + wksz) WK 104 UW1 ltac:(lia) ltac:(lia) ltac:(lia)) as SZ; clear UW1
    end;
    assert (SR : rng RNG (ASHOFF + Z.shiftr WK 3) (Z.shiftr (104 + WK mod 8 + 7) 3))
      by (rewrite !Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; rewrite <- shad_div;
          apply (rng_sub' _ _ _ _ _ RWS); unfold shspan; clear - W4 W1; Z.div_mod_to_equations; lia);
    assert (AP1 : KXGoM.apart DT DTB SPA 216) by (clear - DLO L3 S3; unfold KXGoM.apart; lia);
    assert (AP2 : KXGoM.apart WK wksz SPA 216) by (clear - WLO L3 S3; unfold KXGoM.apart; lia);
    assert (AP3 : KXGoM.apart DT DTB WK wksz) by (exact DW);
    assert (AP4 : KXGoM.apart WK wksz FF 64) by (exact WF);
    assert (AP5 : KXGoM.apart DT DTB FF 64) by (exact DF);
    assert (AP6 : KXGoM.apart SPA 216 FF 64) by (clear - F3 L2 L3 S3 ATR; unfold KXGoM.apart; lia);
    clear DLO WLO DW WF DF;
    pose proof (rank_small 0 ltac:(lia)) as R0; pose proof (rank_small 1 ltac:(lia)) as R1; pose proof (rank_small 2 ltac:(lia)) as R2;
    pose proof (rank_small 3 ltac:(lia)) as R3; pose proof (rank_small 4 ltac:(lia)) as R4; pose proof (rank_small 5 ltac:(lia)) as R5;
    pose proof (rank_small 6 ltac:(lia)) as R6; pose proof (rank_small 7 ltac:(lia)) as R7; pose proof (rank_small 8 ltac:(lia)) as R8;
    pose proof (rank_small 9 ltac:(lia)) as R9; pose proof (rank_small 10 ltac:(lia)) as R10; pose proof (rank_small 11 ltac:(lia)) as R11;
    pose proof (rank_small 12 ltac:(lia)) as R12;
    assert (RKL : Z.of_nat (length (u32b rank)) = 52) by (rewrite u32b_length2, LRK; reflexivity);
    assert (RK52 : Z.of_nat (length (map (Z_to_bv 8) (u32b rank))) = 52) by (rewrite length_map; exact RKL);
    lazymatch type of RST with u8arr _ _ _ (map _ (u32b ?l)) =>
      assert (RSL : Z.of_nat (length (u32b l)) = 52) by (rewrite u32b_length2, RSTLEN; reflexivity);
      assert (RS52 : Z.of_nat (length (map (Z_to_bv 8) (u32b l))) = 52) by (rewrite length_map; exact RSL) end;
    unfold X1FFHDR in FFC; unfold X1FRB in FR.
  Local Ltac x1rs_fix :=
    try replace (nbs + -4) with (nbs - 4) by lia;
    try replace (Z_to_bv 64 (WK mod 2 ^ 64 / 2 ^ (3 mod 64))) with (Z_to_bv 64 (WK / 8)) by (f_equal; rewrite Z.mod_small by lia; reflexivity);
    try (let v := eval vm_compute in (2 ^ 64 - 44) in replace (Z_to_bv 64 (-44)) with (Z_to_bv 64 v) by (apply Z_to_bv_eqm; vm_compute; reflexivity)).
  Local Ltac x1kwr :=
    x1kw4;
    lazymatch goal with |- PropExec.rdn _ ?mm (wa (WK + ?o)) _ = Some (word_to_le_bytes _ (Z_to_bv 64 (Znth ?i rank))) =>
      replace (WK + o) with (WK + 4 * i) by lia;
      lazymatch goal with RK : u8arr _ mm WK _ |- _ => apply (rdn_u32b bsegs mm WK rank i RK); lia end
    end.
  Local Ltac x1beq TLE :=
    lazymatch goal with |- branch_taken _ _ _ = _ => x1ez; rewrite ?TLE; vm_compute; reflexivity end.
  Local Ltac x1rs_close :=
    unfold XB; do 6 (split; [eassumption|]); split; [rewrite Zupd_length2; eassumption|];
    split; [apply Forall_Zupd; [eassumption | lia]|]; do 8 (split; [eassumption|]); unfold X1FRB; eassumption.
  Lemma x1_rs0A : forall m1 (dt rst : list Z) (syb jA jA2 jC jD jB jE j3 j5 j6 : list byte) (fl : Z) (k176 : word) xa0 xa1 xa2 xa4 xa5 x6 x7 x28 x29,
    XBm hw rank tl k176 jA jA2 jC jD jB jE dt rst syb m1 ->
    rw_cells bsegs m1 FF (X1FFHDR fl j3 j5 j6 (Z_to_bv 64 tl) (Z_to_bv 64 nbs)) ->
    (forall m2 (rs : list Z) (y6 : word),
       XBm hw rank tl k176 jA jA2 jC jD jB jE dt rs syb m2 -> (forall v, 0 <= v <= 0 -> Znth v rs = xsym rank v) ->
       rw_cells bsegs m2 FF (X1FFHDR fl j3 j5 j6 (Z_to_bv 64 tl) (Z_to_bv 64 nbs)) ->
       evtF bsegs RNG POST (STK 0x80768 m2 (Z_to_bv 64 (Znth 0 rank)) (Z_to_bv 64 1) (Z_to_bv 64 (tl + 1)) xa4 xa5 y6 x7 x28 x29)) ->
    evtF bsegs RNG POST (ST4 m1 xa0 xa1 xa2 xa4 xa5 x6 x7 x28 x29).
  Proof.
    intros until x29; intros I FFC K.
    destruct I as (DTC & DTLEN & DTBY & HWC & RK & RST & RSTLEN & RSTNN & STW & SYC & SYLEN & WKR & STL & MI & MU & WM & FR).
    pose proof HY as HYc; unfold x1A_hyps in HYc; unfold KHIGH in HYc.
    destruct HYc as (D1 & D2 & D3 & W1 & W2 & W3 & W4 & L1 & L2 & L3 & S1 & S2 & S3 & S4 & DLO & WLO & DW & F1 & F2 & F3 & FB & DF & WF & DB & RD & RDS & WB & RW & RWS & RF & RLO & RAI).
    pose proof atop_range as ATR.
    assert (RSTA : rng RNG SPA 216) by (eapply rng_sub'; [exact RLO| lia]).
    assert (RWK : rng RNG WK 104) by (eapply rng_sub'; [exact RW| lia]).
    assert (UW1 : unpz m1 WK (WK + wksz)) by (eapply x1_unp_wkM; eassumption).
    pose proof (unp_kshz m1 WK (WK + wksz) WK 104 UW1 ltac:(lia) ltac:(lia) ltac:(lia)) as SZ.
    assert (SR : rng RNG (ASHOFF + Z.shiftr WK 3) (Z.shiftr (104 + WK mod 8 + 7) 3)).
    { rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite <- shad_div.
      apply (rng_sub' _ _ _ _ _ RWS). unfold shspan. clear - W4 W1. Z.div_mod_to_equations. lia. }
    clear UW1.
    assert (AP1 : KXGoM.apart DT DTB SPA 216) by (clear - DLO L3 S3; unfold KXGoM.apart; lia).
    assert (AP2 : KXGoM.apart WK wksz SPA 216) by (clear - WLO L3 S3; unfold KXGoM.apart; lia).
    assert (AP3 : KXGoM.apart DT DTB WK wksz) by (exact DW).
    assert (AP4 : KXGoM.apart WK wksz FF 64) by (exact WF).
    assert (AP5 : KXGoM.apart DT DTB FF 64) by (exact DF).
    assert (AP6 : KXGoM.apart SPA 216 FF 64) by (clear - F3 L2 L3 S3 ATR; unfold KXGoM.apart; lia).
    clear DLO WLO DW WF DF.
    pose proof (rank_small 0 ltac:(lia)) as R0.
    assert (RK52 : zlen (map (Z_to_bv 8) (u32b rank)) = 52) by (rewrite length_map, u32b_length2, LRK; reflexivity).
    assert (RS52 : zlen (map (Z_to_bv 8) (u32b rst)) = 52) by (rewrite length_map, u32b_length2, RSTLEN; reflexivity).
    unfold X1FFHDR in FFC.
    unfold X1FRB in FR.
    assert (RKL : Z.of_nat (length (u32b rank)) = 52) by (rewrite u32b_length2, LRK; reflexivity).
    assert (RSL : Z.of_nat (length (u32b rst)) = 52) by (rewrite u32b_length2, RSTLEN; reflexivity).
    kx_runFm [0x80768; 0x80c20; 0x819cc] 60%nat
      [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZRange (tl + 1) 2 13; KZWr (WK + 52) 52; KZRange (WK / 8) 0 (2^44 - 187); KZWord (SPA + 72) 8 (tl + 1); KZWord (SPA + 96) 8 WK; KZWord (WK + 4 * 0) 4%nat (Znth 0 rank); KZRange (Znth 0 rank) 0 256; KZShZ ASHOFF WK 104]
      [(WK, 52)] [(WK, 52); (WK + 52, 52); (SPA, 216)] (@nil (Z * Z)).
    all: try x1br.
    all: try (x1kw4; replace WK with (WK + 4 * 0) at 1 by lia; apply (rdn_u32b bsegs m1 WK rank 0 RK); lia).
    kx_post_regs. x1rs_mem 0 0.
    replace (nbs + -4) with (nbs - 4) by lia.
    replace (Z_to_bv 64 (WK mod 2 ^ 64 / 2 ^ (3 mod 64))) with (Z_to_bv 64 (WK / 8)) by (f_equal; rewrite Z.mod_small by lia; reflexivity).
    let v := eval vm_compute in (2 ^ 64 - 44) in replace (Z_to_bv 64 (-44)) with (Z_to_bv 64 v) by (apply Z_to_bv_eqm; vm_compute; reflexivity).
    apply (K _ (Zupd 0 0 rst) x6); [| apply rsinv_0; lia | unfold X1FFHDR; exact FFCm].
    unfold XB. refine (conj DTm (conj DTLEN (conj DTBY (conj HWm (conj RKm (conj RSTm (conj _ (conj _
      (conj STWm (conj SYm (conj SYLEN (conj WKRm (conj STLm (conj MIm (conj MUm (conj WMm _)))))))))))))))).
    - rewrite Zupd_length2. exact RSTLEN.
    - apply Forall_Zupd; [exact RSTNN | lia].
    - unfold X1FRB. exact FRm.
  Qed.
  Section RSB.
  Variables (dt : list Z) (syb jA jA2 jC jD jB jE j3 j5 j6 : list byte) (fl : Z) (k176 x7 : word).
  Notation XBk m rs := (XBm hw rank tl k176 jA jA2 jC jD jB jE dt rs syb m).
  Notation FFk m := (rw_cells bsegs m FF (X1FFHDR fl j3 j5 j6 (Z_to_bv 64 tl) (Z_to_bv 64 nbs))).
  Hypothesis KF : forall m2 (rs : list Z) (ya0 ya2 ya3 ya4 ya5 y6 y28 y29 : word),
    XBk m2 rs -> (forall v, 0 <= v <= tl -> Znth v rs = xsym rank v) -> FFk m2 ->
    evtF bsegs RNG POST (STS m2 ya0 ya2 ya3 ya4 ya5 y6 x7 y28 y29).
  Lemma x1_rsb12 : forall m (rs : list Z) (c v : Z) (ya2 ya3 ya4 y6 x28 x29 : word),
    XBk m rs -> (forall u, 0 <= u <= 11 -> Znth u rs = xsym rank u) -> 12 <= tl -> c = xsym rank 11 -> v = Znth 11 rank -> FFk m ->
    evtF bsegs RNG POST (STK 0x80be0 m (Z_to_bv 64 c) ya2 ya3 ya4 (Z_to_bv 64 v) y6 x7 x28 x29).
  Proof.
    intros until x29; intros I RSI TLK HC HV FFC.
    x1rs_open I FFC.
    assert (CB : 0 <= c <= 2816) by (rewrite HC; apply x1r_xsym_b; lia).
    assert (VB : 0 <= v <= 256) by (rewrite HV; apply rank_small; lia).
    assert (XV : c + v = xsym rank 12) by (rewrite HC, HV; replace 12 with (11 + 1) by lia; rewrite x1r_xsym_S by lia; reflexivity).
    clear HC HV.
    assert (TLE : tl = 12) by lia.
    kx_runFm [0x80c20; 0x819cc] 60%nat
        [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZRange (tl + 1) 13 13; KZWr (WK + 52) 52; KZRange (WK / 8) 0 (2^44 - 187); KZWord (SPA + 72) 8 (tl + 1); KZWord (SPA + 96) 8 WK; KZRange c 0 2816; KZRange v 0 256; KZShZ ASHOFF WK 104]
        [(WK, 52)] [(WK, 52); (WK + 52, 52); (SPA, 216)] (@nil (Z * Z)).
    all: try x1br.
    all: try x1kwr.
    all: try x1beq TLE.
    kx_post_regs. x1rs_mem 12 (c + v). x1rs_fix.
    apply (KF _ (Zupd 12 (c + v) rs)); [x1rs_close | | unfold X1FFHDR; exact FFCm].
    intros u Hu. apply (rsinv_up rank rs 12 (c + v)); [lia | lia | exact RSI | lia].
  Qed.
  Lemma x1_rsb11 : forall m (rs : list Z) (c v : Z) (ya2 ya3 ya5 y6 x28 x29 : word),
    XBk m rs -> (forall u, 0 <= u <= 10 -> Znth u rs = xsym rank u) -> 11 <= tl -> c = xsym rank 10 -> v = Znth 10 rank -> FFk m ->
    evtF bsegs RNG POST (STK 0x80b7c m (Z_to_bv 64 c) ya2 ya3 (Z_to_bv 64 v) ya5 y6 x7 x28 x29).
  Proof.
    intros until x29; intros I RSI TLK HC HV FFC.
    x1rs_open I FFC.
    assert (CB : 0 <= c <= 2560) by (rewrite HC; apply x1r_xsym_b; lia).
    assert (VB : 0 <= v <= 256) by (rewrite HV; apply rank_small; lia).
    assert (XV : c + v = xsym rank 11) by (rewrite HC, HV; replace 11 with (10 + 1) by lia; rewrite x1r_xsym_S by lia; reflexivity).
    clear HC HV.
    destruct (Z.eq_dec tl 11) as [TLE|TLN].
    - kx_runFmd [0x80be0; 0x80c20; 0x819cc] 60%nat [true]
        [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZRange (tl + 1) 12 12; KZWr (WK + 52) 52; KZRange (WK / 8) 0 (2^44 - 187); KZWord (SPA + 72) 8 (tl + 1); KZWord (SPA + 96) 8 WK; KZWord (WK + 4 * 11) 4%nat (Znth 11 rank); KZRange (Znth 11 rank) 0 256; KZRange c 0 2560; KZRange v 0 256; KZShZ ASHOFF WK 104]
        [(WK, 52)] [(WK, 52); (WK + 52, 52); (SPA, 216)] (@nil (Z * Z)).
      all: try x1br.
      all: try x1kwr.
      all: try x1beq TLE.
      kx_post_regs. x1rs_mem 11 (c + v). x1rs_fix.
      apply (KF _ (Zupd 11 (c + v) rs)); [x1rs_close | | unfold X1FFHDR; exact FFCm].
      intros u Hu. apply (rsinv_up rank rs 11 (c + v)); [lia | lia | exact RSI | lia].
    - kx_runFm [0x80be0; 0x80c20; 0x819cc] 60%nat
        [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZRange (tl + 1) 13 13; KZWr (WK + 52) 52; KZRange (WK / 8) 0 (2^44 - 187); KZWord (SPA + 72) 8 (tl + 1); KZWord (SPA + 96) 8 WK; KZWord (WK + 4 * 11) 4%nat (Znth 11 rank); KZRange (Znth 11 rank) 0 256; KZRange c 0 2560; KZRange v 0 256; KZShZ ASHOFF WK 104]
        [(WK, 52)] [(WK, 52); (WK + 52, 52); (SPA, 216)] (@nil (Z * Z)).
      all: try x1br.
      all: try x1kwr.
      kx_post_regs. x1rs_mem 11 (c + v). x1rs_fix.
      eapply (x1_rsb12 _ (Zupd 11 (c + v) rs)); [x1rs_close | apply (rsinv_up rank rs 11 (c + v)); [lia | lia | exact RSI] | lia | lia | lia | unfold X1FFHDR; exact FFCm].
  Qed.
  Lemma x1_rsb10 : forall m (rs : list Z) (c v : Z) (ya2 ya3 ya4 y6 x28 x29 : word),
    XBk m rs -> (forall u, 0 <= u <= 9 -> Znth u rs = xsym rank u) -> 10 <= tl -> c = xsym rank 9 -> v = Znth 9 rank -> FFk m ->
    evtF bsegs RNG POST (STK 0x80b18 m (Z_to_bv 64 v) ya2 ya3 ya4 (Z_to_bv 64 c) y6 x7 x28 x29).
  Proof.
    intros until x29; intros I RSI TLK HC HV FFC.
    x1rs_open I FFC.
    assert (CB : 0 <= c <= 2304) by (rewrite HC; apply x1r_xsym_b; lia).
    assert (VB : 0 <= v <= 256) by (rewrite HV; apply rank_small; lia).
    assert (XV : c + v = xsym rank 10) by (rewrite HC, HV; replace 10 with (9 + 1) by lia; rewrite x1r_xsym_S by lia; reflexivity).
    clear HC HV.
    destruct (Z.eq_dec tl 10) as [TLE|TLN].
    - kx_runFmd [0x80b7c; 0x80c20; 0x819cc] 60%nat [true]
        [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZRange (tl + 1) 11 11; KZWr (WK + 52) 52; KZRange (WK / 8) 0 (2^44 - 187); KZWord (SPA + 72) 8 (tl + 1); KZWord (SPA + 96) 8 WK; KZWord (WK + 4 * 10) 4%nat (Znth 10 rank); KZRange (Znth 10 rank) 0 256; KZRange c 0 2304; KZRange v 0 256; KZShZ ASHOFF WK 104]
        [(WK, 52)] [(WK, 52); (WK + 52, 52); (SPA, 216)] (@nil (Z * Z)).
      all: try x1br.
      all: try x1kwr.
      all: try x1beq TLE.
      kx_post_regs. x1rs_mem 10 (c + v). x1rs_fix.
      apply (KF _ (Zupd 10 (c + v) rs)); [x1rs_close | | unfold X1FFHDR; exact FFCm].
      intros u Hu. apply (rsinv_up rank rs 10 (c + v)); [lia | lia | exact RSI | lia].
    - kx_runFm [0x80b7c; 0x80c20; 0x819cc] 60%nat
        [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZRange (tl + 1) 12 13; KZWr (WK + 52) 52; KZRange (WK / 8) 0 (2^44 - 187); KZWord (SPA + 72) 8 (tl + 1); KZWord (SPA + 96) 8 WK; KZWord (WK + 4 * 10) 4%nat (Znth 10 rank); KZRange (Znth 10 rank) 0 256; KZRange c 0 2304; KZRange v 0 256; KZShZ ASHOFF WK 104]
        [(WK, 52)] [(WK, 52); (WK + 52, 52); (SPA, 216)] (@nil (Z * Z)).
      all: try x1br.
      all: try x1kwr.
      kx_post_regs. x1rs_mem 10 (c + v). x1rs_fix.
      eapply (x1_rsb11 _ (Zupd 10 (c + v) rs)); [x1rs_close | apply (rsinv_up rank rs 10 (c + v)); [lia | lia | exact RSI] | lia | lia | lia | unfold X1FFHDR; exact FFCm].
  Qed.
  Lemma x1_rsb9 : forall m (rs : list Z) (c v : Z) (ya0 ya2 ya3 y6 x28 x29 : word),
    XBk m rs -> (forall u, 0 <= u <= 8 -> Znth u rs = xsym rank u) -> 9 <= tl -> c = xsym rank 8 -> v = Znth 8 rank -> FFk m ->
    evtF bsegs RNG POST (STK 0x80ab4 m ya0 ya2 ya3 (Z_to_bv 64 v) (Z_to_bv 64 c) y6 x7 x28 x29).
  Proof.
    intros until x29; intros I RSI TLK HC HV FFC.
    x1rs_open I FFC.
    assert (CB : 0 <= c <= 2048) by (rewrite HC; apply x1r_xsym_b; lia).
    assert (VB : 0 <= v <= 256) by (rewrite HV; apply rank_small; lia).
    assert (XV : c + v = xsym rank 9) by (rewrite HC, HV; replace 9 with (8 + 1) by lia; rewrite x1r_xsym_S by lia; reflexivity).
    clear HC HV.
    destruct (Z.eq_dec tl 9) as [TLE|TLN].
    - kx_runFmd [0x80b18; 0x80c20; 0x819cc] 60%nat [true]
        [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZRange (tl + 1) 10 10; KZWr (WK + 52) 52; KZRange (WK / 8) 0 (2^44 - 187); KZWord (SPA + 72) 8 (tl + 1); KZWord (SPA + 96) 8 WK; KZWord (WK + 4 * 9) 4%nat (Znth 9 rank); KZRange (Znth 9 rank) 0 256; KZRange c 0 2048; KZRange v 0 256; KZShZ ASHOFF WK 104]
        [(WK, 52)] [(WK, 52); (WK + 52, 52); (SPA, 216)] (@nil (Z * Z)).
      all: try x1br.
      all: try x1kwr.
      all: try x1beq TLE.
      kx_post_regs. x1rs_mem 9 (c + v). x1rs_fix.
      apply (KF _ (Zupd 9 (c + v) rs)); [x1rs_close | | unfold X1FFHDR; exact FFCm].
      intros u Hu. apply (rsinv_up rank rs 9 (c + v)); [lia | lia | exact RSI | lia].
    - kx_runFm [0x80b18; 0x80c20; 0x819cc] 60%nat
        [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZRange (tl + 1) 11 13; KZWr (WK + 52) 52; KZRange (WK / 8) 0 (2^44 - 187); KZWord (SPA + 72) 8 (tl + 1); KZWord (SPA + 96) 8 WK; KZWord (WK + 4 * 9) 4%nat (Znth 9 rank); KZRange (Znth 9 rank) 0 256; KZRange c 0 2048; KZRange v 0 256; KZShZ ASHOFF WK 104]
        [(WK, 52)] [(WK, 52); (WK + 52, 52); (SPA, 216)] (@nil (Z * Z)).
      all: try x1br.
      all: try x1kwr.
      kx_post_regs. x1rs_mem 9 (c + v). x1rs_fix.
      eapply (x1_rsb10 _ (Zupd 9 (c + v) rs)); [x1rs_close | apply (rsinv_up rank rs 9 (c + v)); [lia | lia | exact RSI] | lia | lia | lia | unfold X1FFHDR; exact FFCm].
  Qed.
  Lemma x1_rsb8 : forall m (rs : list Z) (c v : Z) (ya2 ya3 ya4 y6 x28 x29 : word),
    XBk m rs -> (forall u, 0 <= u <= 7 -> Znth u rs = xsym rank u) -> 8 <= tl -> c = xsym rank 7 -> v = Znth 7 rank -> FFk m ->
    evtF bsegs RNG POST (STK 0x80a50 m (Z_to_bv 64 v) ya2 ya3 ya4 (Z_to_bv 64 c) y6 x7 x28 x29).
  Proof.
    intros until x29; intros I RSI TLK HC HV FFC.
    x1rs_open I FFC.
    assert (CB : 0 <= c <= 1792) by (rewrite HC; apply x1r_xsym_b; lia).
    assert (VB : 0 <= v <= 256) by (rewrite HV; apply rank_small; lia).
    assert (XV : c + v = xsym rank 8) by (rewrite HC, HV; replace 8 with (7 + 1) by lia; rewrite x1r_xsym_S by lia; reflexivity).
    clear HC HV.
    destruct (Z.eq_dec tl 8) as [TLE|TLN].
    - kx_runFmd [0x80ab4; 0x80c20; 0x819cc] 60%nat [true]
        [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZRange (tl + 1) 9 9; KZWr (WK + 52) 52; KZRange (WK / 8) 0 (2^44 - 187); KZWord (SPA + 72) 8 (tl + 1); KZWord (SPA + 96) 8 WK; KZWord (WK + 4 * 8) 4%nat (Znth 8 rank); KZRange (Znth 8 rank) 0 256; KZRange c 0 1792; KZRange v 0 256; KZShZ ASHOFF WK 104]
        [(WK, 52)] [(WK, 52); (WK + 52, 52); (SPA, 216)] (@nil (Z * Z)).
      all: try x1br.
      all: try x1kwr.
      all: try x1beq TLE.
      kx_post_regs. x1rs_mem 8 (c + v). x1rs_fix.
      apply (KF _ (Zupd 8 (c + v) rs)); [x1rs_close | | unfold X1FFHDR; exact FFCm].
      intros u Hu. apply (rsinv_up rank rs 8 (c + v)); [lia | lia | exact RSI | lia].
    - kx_runFm [0x80ab4; 0x80c20; 0x819cc] 60%nat
        [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZRange (tl + 1) 10 13; KZWr (WK + 52) 52; KZRange (WK / 8) 0 (2^44 - 187); KZWord (SPA + 72) 8 (tl + 1); KZWord (SPA + 96) 8 WK; KZWord (WK + 4 * 8) 4%nat (Znth 8 rank); KZRange (Znth 8 rank) 0 256; KZRange c 0 1792; KZRange v 0 256; KZShZ ASHOFF WK 104]
        [(WK, 52)] [(WK, 52); (WK + 52, 52); (SPA, 216)] (@nil (Z * Z)).
      all: try x1br.
      all: try x1kwr.
      kx_post_regs. x1rs_mem 8 (c + v). x1rs_fix.
      eapply (x1_rsb9 _ (Zupd 8 (c + v) rs)); [x1rs_close | apply (rsinv_up rank rs 8 (c + v)); [lia | lia | exact RSI] | lia | lia | lia | unfold X1FFHDR; exact FFCm].
  Qed.
  Lemma x1_rsb7 : forall m (rs : list Z) (c v : Z) (ya0 ya2 ya3 y6 x28 x29 : word),
    XBk m rs -> (forall u, 0 <= u <= 6 -> Znth u rs = xsym rank u) -> 7 <= tl -> c = xsym rank 6 -> v = Znth 6 rank -> FFk m ->
    evtF bsegs RNG POST (STK 0x809ec m ya0 ya2 ya3 (Z_to_bv 64 v) (Z_to_bv 64 c) y6 x7 x28 x29).
  Proof.
    intros until x29; intros I RSI TLK HC HV FFC.
    x1rs_open I FFC.
    assert (CB : 0 <= c <= 1536) by (rewrite HC; apply x1r_xsym_b; lia).
    assert (VB : 0 <= v <= 256) by (rewrite HV; apply rank_small; lia).
    assert (XV : c + v = xsym rank 7) by (rewrite HC, HV; replace 7 with (6 + 1) by lia; rewrite x1r_xsym_S by lia; reflexivity).
    clear HC HV.
    destruct (Z.eq_dec tl 7) as [TLE|TLN].
    - kx_runFmd [0x80a50; 0x80c20; 0x819cc] 60%nat [true]
        [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZRange (tl + 1) 8 8; KZWr (WK + 52) 52; KZRange (WK / 8) 0 (2^44 - 187); KZWord (SPA + 72) 8 (tl + 1); KZWord (SPA + 96) 8 WK; KZWord (WK + 4 * 7) 4%nat (Znth 7 rank); KZRange (Znth 7 rank) 0 256; KZRange c 0 1536; KZRange v 0 256; KZShZ ASHOFF WK 104]
        [(WK, 52)] [(WK, 52); (WK + 52, 52); (SPA, 216)] (@nil (Z * Z)).
      all: try x1br.
      all: try x1kwr.
      all: try x1beq TLE.
      kx_post_regs. x1rs_mem 7 (c + v). x1rs_fix.
      apply (KF _ (Zupd 7 (c + v) rs)); [x1rs_close | | unfold X1FFHDR; exact FFCm].
      intros u Hu. apply (rsinv_up rank rs 7 (c + v)); [lia | lia | exact RSI | lia].
    - kx_runFm [0x80a50; 0x80c20; 0x819cc] 60%nat
        [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZRange (tl + 1) 9 13; KZWr (WK + 52) 52; KZRange (WK / 8) 0 (2^44 - 187); KZWord (SPA + 72) 8 (tl + 1); KZWord (SPA + 96) 8 WK; KZWord (WK + 4 * 7) 4%nat (Znth 7 rank); KZRange (Znth 7 rank) 0 256; KZRange c 0 1536; KZRange v 0 256; KZShZ ASHOFF WK 104]
        [(WK, 52)] [(WK, 52); (WK + 52, 52); (SPA, 216)] (@nil (Z * Z)).
      all: try x1br.
      all: try x1kwr.
      kx_post_regs. x1rs_mem 7 (c + v). x1rs_fix.
      eapply (x1_rsb8 _ (Zupd 7 (c + v) rs)); [x1rs_close | apply (rsinv_up rank rs 7 (c + v)); [lia | lia | exact RSI] | lia | lia | lia | unfold X1FFHDR; exact FFCm].
  Qed.
  Lemma x1_rsb6 : forall m (rs : list Z) (c v : Z) (ya2 ya3 ya4 y6 x28 x29 : word),
    XBk m rs -> (forall u, 0 <= u <= 5 -> Znth u rs = xsym rank u) -> 6 <= tl -> c = xsym rank 5 -> v = Znth 5 rank -> FFk m ->
    evtF bsegs RNG POST (STK 0x80980 m (Z_to_bv 64 v) ya2 ya3 ya4 (Z_to_bv 64 c) y6 x7 x28 x29).
  Proof.
    intros until x29; intros I RSI TLK HC HV FFC.
    x1rs_open I FFC.
    assert (CB : 0 <= c <= 1280) by (rewrite HC; apply x1r_xsym_b; lia).
    assert (VB : 0 <= v <= 256) by (rewrite HV; apply rank_small; lia).
    assert (XV : c + v = xsym rank 6) by (rewrite HC, HV; replace 6 with (5 + 1) by lia; rewrite x1r_xsym_S by lia; reflexivity).
    clear HC HV.
    destruct (Z.eq_dec tl 6) as [TLE|TLN].
    - kx_runFmd [0x809ec; 0x80c20; 0x819cc] 60%nat [true]
        [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZRange (tl + 1) 7 7; KZWr (WK + 52) 52; KZRange (WK / 8) 0 (2^44 - 187); KZWord (SPA + 72) 8 (tl + 1); KZWord (SPA + 96) 8 WK; KZWord (WK + 4 * 6) 4%nat (Znth 6 rank); KZRange (Znth 6 rank) 0 256; KZRange c 0 1280; KZRange v 0 256; KZShZ ASHOFF WK 104]
        [(WK, 52)] [(WK, 52); (WK + 52, 52); (SPA, 216)] (@nil (Z * Z)).
      all: try x1br.
      all: try x1kwr.
      all: try x1beq TLE.
      kx_post_regs. x1rs_mem 6 (c + v). x1rs_fix.
      apply (KF _ (Zupd 6 (c + v) rs)); [x1rs_close | | unfold X1FFHDR; exact FFCm].
      intros u Hu. apply (rsinv_up rank rs 6 (c + v)); [lia | lia | exact RSI | lia].
    - kx_runFm [0x809ec; 0x80c20; 0x819cc] 60%nat
        [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZRange (tl + 1) 8 13; KZWr (WK + 52) 52; KZRange (WK / 8) 0 (2^44 - 187); KZWord (SPA + 72) 8 (tl + 1); KZWord (SPA + 96) 8 WK; KZWord (WK + 4 * 6) 4%nat (Znth 6 rank); KZRange (Znth 6 rank) 0 256; KZRange c 0 1280; KZRange v 0 256; KZShZ ASHOFF WK 104]
        [(WK, 52)] [(WK, 52); (WK + 52, 52); (SPA, 216)] (@nil (Z * Z)).
      all: try x1br.
      all: try x1kwr.
      kx_post_regs. x1rs_mem 6 (c + v). x1rs_fix.
      eapply (x1_rsb7 _ (Zupd 6 (c + v) rs)); [x1rs_close | apply (rsinv_up rank rs 6 (c + v)); [lia | lia | exact RSI] | lia | lia | lia | unfold X1FFHDR; exact FFCm].
  Qed.
  Lemma x1_rsb5 : forall m (rs : list Z) (c v : Z) (ya0 ya2 ya3 y6 x28 x29 : word),
    XBk m rs -> (forall u, 0 <= u <= 4 -> Znth u rs = xsym rank u) -> 5 <= tl -> c = xsym rank 4 -> v = Znth 4 rank -> FFk m ->
    evtF bsegs RNG POST (STK 0x80914 m ya0 ya2 ya3 (Z_to_bv 64 v) (Z_to_bv 64 c) y6 x7 x28 x29).
  Proof.
    intros until x29; intros I RSI TLK HC HV FFC.
    x1rs_open I FFC.
    assert (CB : 0 <= c <= 1024) by (rewrite HC; apply x1r_xsym_b; lia).
    assert (VB : 0 <= v <= 256) by (rewrite HV; apply rank_small; lia).
    assert (XV : c + v = xsym rank 5) by (rewrite HC, HV; replace 5 with (4 + 1) by lia; rewrite x1r_xsym_S by lia; reflexivity).
    clear HC HV.
    destruct (Z.eq_dec tl 5) as [TLE|TLN].
    - kx_runFmd [0x80980; 0x80c20; 0x819cc] 60%nat [true]
        [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZRange (tl + 1) 6 6; KZWr (WK + 52) 52; KZRange (WK / 8) 0 (2^44 - 187); KZWord (SPA + 72) 8 (tl + 1); KZWord (SPA + 96) 8 WK; KZWord (WK + 4 * 5) 4%nat (Znth 5 rank); KZRange (Znth 5 rank) 0 256; KZRange c 0 1024; KZRange v 0 256; KZShZ ASHOFF WK 104]
        [(WK, 52)] [(WK, 52); (WK + 52, 52); (SPA, 216)] (@nil (Z * Z)).
      all: try x1br.
      all: try x1kwr.
      all: try x1beq TLE.
      kx_post_regs. x1rs_mem 5 (c + v). x1rs_fix.
      apply (KF _ (Zupd 5 (c + v) rs)); [x1rs_close | | unfold X1FFHDR; exact FFCm].
      intros u Hu. apply (rsinv_up rank rs 5 (c + v)); [lia | lia | exact RSI | lia].
    - kx_runFm [0x80980; 0x80c20; 0x819cc] 60%nat
        [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZRange (tl + 1) 7 13; KZWr (WK + 52) 52; KZRange (WK / 8) 0 (2^44 - 187); KZWord (SPA + 72) 8 (tl + 1); KZWord (SPA + 96) 8 WK; KZWord (WK + 4 * 5) 4%nat (Znth 5 rank); KZRange (Znth 5 rank) 0 256; KZRange c 0 1024; KZRange v 0 256; KZShZ ASHOFF WK 104]
        [(WK, 52)] [(WK, 52); (WK + 52, 52); (SPA, 216)] (@nil (Z * Z)).
      all: try x1br.
      all: try x1kwr.
      kx_post_regs. x1rs_mem 5 (c + v). x1rs_fix.
      eapply (x1_rsb6 _ (Zupd 5 (c + v) rs)); [x1rs_close | apply (rsinv_up rank rs 5 (c + v)); [lia | lia | exact RSI] | lia | lia | lia | unfold X1FFHDR; exact FFCm].
  Qed.
  Lemma x1_rsb4 : forall m (rs : list Z) (c v : Z) (ya2 ya3 ya4 y6 x28 x29 : word),
    XBk m rs -> (forall u, 0 <= u <= 3 -> Znth u rs = xsym rank u) -> 4 <= tl -> c = xsym rank 3 -> v = Znth 3 rank -> FFk m ->
    evtF bsegs RNG POST (STK 0x808a8 m (Z_to_bv 64 v) ya2 ya3 ya4 (Z_to_bv 64 c) y6 x7 x28 x29).
  Proof.
    intros until x29; intros I RSI TLK HC HV FFC.
    x1rs_open I FFC.
    assert (CB : 0 <= c <= 768) by (rewrite HC; apply x1r_xsym_b; lia).
    assert (VB : 0 <= v <= 256) by (rewrite HV; apply rank_small; lia).
    assert (XV : c + v = xsym rank 4) by (rewrite HC, HV; replace 4 with (3 + 1) by lia; rewrite x1r_xsym_S by lia; reflexivity).
    clear HC HV.
    destruct (Z.eq_dec tl 4) as [TLE|TLN].
    - kx_runFmd [0x80914; 0x80c20; 0x819cc] 60%nat [true]
        [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZRange (tl + 1) 5 5; KZWr (WK + 52) 52; KZRange (WK / 8) 0 (2^44 - 187); KZWord (SPA + 72) 8 (tl + 1); KZWord (SPA + 96) 8 WK; KZWord (WK + 4 * 4) 4%nat (Znth 4 rank); KZRange (Znth 4 rank) 0 256; KZRange c 0 768; KZRange v 0 256; KZShZ ASHOFF WK 104]
        [(WK, 52)] [(WK, 52); (WK + 52, 52); (SPA, 216)] (@nil (Z * Z)).
      all: try x1br.
      all: try x1kwr.
      all: try x1beq TLE.
      kx_post_regs. x1rs_mem 4 (c + v). x1rs_fix.
      apply (KF _ (Zupd 4 (c + v) rs)); [x1rs_close | | unfold X1FFHDR; exact FFCm].
      intros u Hu. apply (rsinv_up rank rs 4 (c + v)); [lia | lia | exact RSI | lia].
    - kx_runFm [0x80914; 0x80c20; 0x819cc] 60%nat
        [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZRange (tl + 1) 6 13; KZWr (WK + 52) 52; KZRange (WK / 8) 0 (2^44 - 187); KZWord (SPA + 72) 8 (tl + 1); KZWord (SPA + 96) 8 WK; KZWord (WK + 4 * 4) 4%nat (Znth 4 rank); KZRange (Znth 4 rank) 0 256; KZRange c 0 768; KZRange v 0 256; KZShZ ASHOFF WK 104]
        [(WK, 52)] [(WK, 52); (WK + 52, 52); (SPA, 216)] (@nil (Z * Z)).
      all: try x1br.
      all: try x1kwr.
      kx_post_regs. x1rs_mem 4 (c + v). x1rs_fix.
      eapply (x1_rsb5 _ (Zupd 4 (c + v) rs)); [x1rs_close | apply (rsinv_up rank rs 4 (c + v)); [lia | lia | exact RSI] | lia | lia | lia | unfold X1FFHDR; exact FFCm].
  Qed.
  Lemma x1_rsb3 : forall m (rs : list Z) (c v : Z) (ya0 ya2 ya3 y6 x28 x29 : word),
    XBk m rs -> (forall u, 0 <= u <= 2 -> Znth u rs = xsym rank u) -> 3 <= tl -> c = xsym rank 2 -> v = Znth 2 rank -> FFk m ->
    evtF bsegs RNG POST (STK 0x8083c m ya0 ya2 ya3 (Z_to_bv 64 v) (Z_to_bv 64 c) y6 x7 x28 x29).
  Proof.
    intros until x29; intros I RSI TLK HC HV FFC.
    x1rs_open I FFC.
    assert (CB : 0 <= c <= 512) by (rewrite HC; apply x1r_xsym_b; lia).
    assert (VB : 0 <= v <= 256) by (rewrite HV; apply rank_small; lia).
    assert (XV : c + v = xsym rank 3) by (rewrite HC, HV; replace 3 with (2 + 1) by lia; rewrite x1r_xsym_S by lia; reflexivity).
    clear HC HV.
    destruct (Z.eq_dec tl 3) as [TLE|TLN].
    - kx_runFmd [0x808a8; 0x80c20; 0x819cc] 60%nat [true]
        [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZRange (tl + 1) 4 4; KZWr (WK + 52) 52; KZRange (WK / 8) 0 (2^44 - 187); KZWord (SPA + 72) 8 (tl + 1); KZWord (SPA + 96) 8 WK; KZWord (WK + 4 * 3) 4%nat (Znth 3 rank); KZRange (Znth 3 rank) 0 256; KZRange c 0 512; KZRange v 0 256; KZShZ ASHOFF WK 104]
        [(WK, 52)] [(WK, 52); (WK + 52, 52); (SPA, 216)] (@nil (Z * Z)).
      all: try x1br.
      all: try x1kwr.
      all: try x1beq TLE.
      kx_post_regs. x1rs_mem 3 (c + v). x1rs_fix.
      apply (KF _ (Zupd 3 (c + v) rs)); [x1rs_close | | unfold X1FFHDR; exact FFCm].
      intros u Hu. apply (rsinv_up rank rs 3 (c + v)); [lia | lia | exact RSI | lia].
    - kx_runFm [0x808a8; 0x80c20; 0x819cc] 60%nat
        [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZRange (tl + 1) 5 13; KZWr (WK + 52) 52; KZRange (WK / 8) 0 (2^44 - 187); KZWord (SPA + 72) 8 (tl + 1); KZWord (SPA + 96) 8 WK; KZWord (WK + 4 * 3) 4%nat (Znth 3 rank); KZRange (Znth 3 rank) 0 256; KZRange c 0 512; KZRange v 0 256; KZShZ ASHOFF WK 104]
        [(WK, 52)] [(WK, 52); (WK + 52, 52); (SPA, 216)] (@nil (Z * Z)).
      all: try x1br.
      all: try x1kwr.
      kx_post_regs. x1rs_mem 3 (c + v). x1rs_fix.
      eapply (x1_rsb4 _ (Zupd 3 (c + v) rs)); [x1rs_close | apply (rsinv_up rank rs 3 (c + v)); [lia | lia | exact RSI] | lia | lia | lia | unfold X1FFHDR; exact FFCm].
  Qed.
  Lemma x1_rsb2 : forall m (rs : list Z) (c v : Z) (ya2 ya3 ya4 y6 x28 x29 : word),
    XBk m rs -> (forall u, 0 <= u <= 1 -> Znth u rs = xsym rank u) -> 2 <= tl -> c = xsym rank 1 -> v = Znth 1 rank -> FFk m ->
    evtF bsegs RNG POST (STK 0x807d0 m (Z_to_bv 64 c) ya2 ya3 ya4 (Z_to_bv 64 v) y6 x7 x28 x29).
  Proof.
    intros until x29; intros I RSI TLK HC HV FFC.
    x1rs_open I FFC.
    assert (CB : 0 <= c <= 256) by (rewrite HC; apply x1r_xsym_b; lia).
    assert (VB : 0 <= v <= 256) by (rewrite HV; apply rank_small; lia).
    assert (XV : c + v = xsym rank 2) by (rewrite HC, HV; replace 2 with (1 + 1) by lia; rewrite x1r_xsym_S by lia; reflexivity).
    clear HC HV.
    destruct (Z.eq_dec tl 2) as [TLE|TLN].
    - kx_runFmd [0x8083c; 0x80c20; 0x819cc] 60%nat [true]
        [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZRange (tl + 1) 3 3; KZWr (WK + 52) 52; KZRange (WK / 8) 0 (2^44 - 187); KZWord (SPA + 72) 8 (tl + 1); KZWord (SPA + 96) 8 WK; KZWord (WK + 4 * 2) 4%nat (Znth 2 rank); KZRange (Znth 2 rank) 0 256; KZRange c 0 256; KZRange v 0 256; KZShZ ASHOFF WK 104]
        [(WK, 52)] [(WK, 52); (WK + 52, 52); (SPA, 216)] (@nil (Z * Z)).
      all: try x1br.
      all: try x1kwr.
      all: try x1beq TLE.
      kx_post_regs. x1rs_mem 2 (c + v). x1rs_fix.
      apply (KF _ (Zupd 2 (c + v) rs)); [x1rs_close | | unfold X1FFHDR; exact FFCm].
      intros u Hu. apply (rsinv_up rank rs 2 (c + v)); [lia | lia | exact RSI | lia].
    - kx_runFm [0x8083c; 0x80c20; 0x819cc] 60%nat
        [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZRange (tl + 1) 4 13; KZWr (WK + 52) 52; KZRange (WK / 8) 0 (2^44 - 187); KZWord (SPA + 72) 8 (tl + 1); KZWord (SPA + 96) 8 WK; KZWord (WK + 4 * 2) 4%nat (Znth 2 rank); KZRange (Znth 2 rank) 0 256; KZRange c 0 256; KZRange v 0 256; KZShZ ASHOFF WK 104]
        [(WK, 52)] [(WK, 52); (WK + 52, 52); (SPA, 216)] (@nil (Z * Z)).
      all: try x1br.
      all: try x1kwr.
      kx_post_regs. x1rs_mem 2 (c + v). x1rs_fix.
      eapply (x1_rsb3 _ (Zupd 2 (c + v) rs)); [x1rs_close | apply (rsinv_up rank rs 2 (c + v)); [lia | lia | exact RSI] | lia | lia | lia | unfold X1FFHDR; exact FFCm].
  Qed.
  Lemma x1_rsb1 : forall m (rs : list Z) (c : Z) (ya2 ya3 ya4 ya5 y6 x28 x29 : word),
    XBk m rs -> (forall u, 0 <= u <= 0 -> Znth u rs = xsym rank u) -> 1 <= tl -> c = xsym rank 1 -> FFk m ->
    evtF bsegs RNG POST (STK 0x80768 m (Z_to_bv 64 c) ya2 ya3 ya4 ya5 y6 x7 x28 x29).
  Proof.
    intros until x29; intros I RSI TLK HC FFC.
    x1rs_open I FFC.
    assert (CB : 0 <= c <= 256) by (rewrite HC; apply x1r_xsym_b; lia).
    rename HC into XV.
    destruct (Z.eq_dec tl 1) as [TLE|TLN].
    - kx_runFmd [0x807d0; 0x80c20; 0x819cc] 60%nat [true]
        [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZRange (tl + 1) 2 2; KZWr (WK + 52) 52; KZRange (WK / 8) 0 (2^44 - 187); KZWord (SPA + 72) 8 (tl + 1); KZWord (SPA + 96) 8 WK; KZWord (WK + 4 * 1) 4%nat (Znth 1 rank); KZRange (Znth 1 rank) 0 256; KZRange c 0 256; KZShZ ASHOFF WK 104]
        [(WK, 52)] [(WK, 52); (WK + 52, 52); (SPA, 216)] (@nil (Z * Z)).
      all: try x1br.
      all: try x1kwr.
      all: try x1beq TLE.
      kx_post_regs. x1rs_mem 1 c. x1rs_fix.
      apply (KF _ (Zupd 1 c rs)); [x1rs_close | | unfold X1FFHDR; exact FFCm].
      intros u Hu. apply (rsinv_up rank rs 1 c); [lia | lia | exact RSI | lia].
    - kx_runFm [0x807d0; 0x80c20; 0x819cc] 60%nat
        [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47); KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT DTB SPA 216; KZDisj WK wksz SPA 216; KZDisj DT DTB WK wksz; KZDisj WK wksz FF 64; KZDisj DT DTB FF 64; KZDisj SPA 216 FF 64; KZRange tl 1 12; KZRange nbs 2 256; KZRange (tl + 1) 3 13; KZWr (WK + 52) 52; KZRange (WK / 8) 0 (2^44 - 187); KZWord (SPA + 72) 8 (tl + 1); KZWord (SPA + 96) 8 WK; KZWord (WK + 4 * 1) 4%nat (Znth 1 rank); KZRange (Znth 1 rank) 0 256; KZRange c 0 256; KZShZ ASHOFF WK 104]
        [(WK, 52)] [(WK, 52); (WK + 52, 52); (SPA, 216)] (@nil (Z * Z)).
      all: try x1br.
      all: try x1kwr.
      kx_post_regs. x1rs_mem 1 c. x1rs_fix.
      eapply (x1_rsb2 _ (Zupd 1 c rs)); [x1rs_close | apply (rsinv_up rank rs 1 c); [lia | lia | exact RSI] | lia | lia | lia | unfold X1FFHDR; exact FFCm].
  Qed.
  End RSB.
  Definition x1_rsA_stmt : Prop := forall m1 (dt rst : list Z) (syb jA jA2 jC jD jB jE j3 j5 j6 : list byte) (fl : Z) (k176 : word) xa4 xa5 x6 x7 x28 x29,
    XBm hw rank tl k176 jA jA2 jC jD jB jE dt rst syb m1 -> (forall v, 0 <= v <= 0 -> Znth v rst = xsym rank v) ->
    rw_cells bsegs m1 FF (X1FFHDR fl j3 j5 j6 (Z_to_bv 64 tl) (Z_to_bv 64 nbs)) ->
    (forall m2 (rst' : list Z) (ya0 ya2 ya3 ya4 ya5 y6 y28 y29 : word),
       XBm hw rank tl k176 jA jA2 jC jD jB jE dt rst' syb m2 -> (forall v, 0 <= v <= tl -> Znth v rst' = xsym rank v) ->
       rw_cells bsegs m2 FF (X1FFHDR fl j3 j5 j6 (Z_to_bv 64 tl) (Z_to_bv 64 nbs)) ->
       evtF bsegs RNG POST (STS m2 ya0 ya2 ya3 ya4 ya5 y6 x7 y28 y29)) ->
    evtF bsegs RNG POST (STK 0x80768 m1 (Z_to_bv 64 (Znth 0 rank)) (Z_to_bv 64 1) (Z_to_bv 64 (tl + 1)) xa4 xa5 x6 x7 x28 x29).
  Lemma x1_rsA : x1_rsA_stmt.
  Proof.
    unfold x1_rsA_stmt. intros until x29; intros I RSI FFC K.
    eapply (x1_rsb1 dt syb jA jA2 jC jD jB jE j3 j5 j6 fl k176 x7 K); [exact I | exact RSI | lia | | exact FFC].
    replace (xsym rank 1) with (xsym rank (0 + 1)) by reflexivity. rewrite x1r_xsym_S by lia.
    replace (xsym rank 0) with 0 by reflexivity. lia.
  Qed.
  End TL.
End X1B.
End CANSEC1.
