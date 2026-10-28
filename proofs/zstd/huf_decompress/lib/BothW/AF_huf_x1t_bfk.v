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
     AH_huf_rdt2 AF_huf_dec_iface AF_huf_x1t_top AF_huf_x1t_bseg AF_huf_x1t_bdefs.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import ZdHufStats ZdHufX1.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_x1t_bpure ADepotKit.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition d4k (sv nb : Z) : Z := 281479271743489 * nb + 72058693566333184 * sv.
Lemma d4k_bytes : forall sv nb, 0 <= sv < 256 -> 0 <= nb < 256 ->
  d4k sv nb mod 2 ^ 64 = d4k sv nb /\
  d4k sv nb mod 256 = nb /\ (d4k sv nb / 256) mod 256 = sv /\ (d4k sv nb / 65536) mod 256 = nb /\ (d4k sv nb / 16777216) mod 256 = sv /\
  (d4k sv nb / 4294967296) mod 256 = nb /\ (d4k sv nb / 1099511627776) mod 256 = sv /\ (d4k sv nb / 281474976710656) mod 256 = nb /\
  (d4k sv nb / 72057594037927936) mod 256 = sv.
Proof.
  set (chk := fun sv nb => let D := d4k sv nb in
     (D mod 2 ^ 64 =? D) && (D mod 256 =? nb) && ((D / 256) mod 256 =? sv) && ((D / 65536) mod 256 =? nb) && ((D / 16777216) mod 256 =? sv)
     && ((D / 4294967296) mod 256 =? nb) && ((D / 1099511627776) mod 256 =? sv) && ((D / 281474976710656) mod 256 =? nb) && ((D / 72057594037927936) mod 256 =? sv)).
  assert (IN : forall v, 0 <= v < 256 -> In v (map Z.of_nat (seq 0 256)))
    by (intros v Hv; apply in_map_iff; exists (Z.to_nat v); split; [lia| apply in_seq; lia]).
  assert (B : forallb (fun sv => forallb (fun nb => chk sv nb) (map Z.of_nat (seq 0 256))) (map Z.of_nat (seq 0 256)) = true)
    by (vm_compute; reflexivity).
  intros sv nb Hs Hn. rewrite forallb_forall in B. specialize (B sv (IN sv Hs)).
  rewrite forallb_forall in B. specialize (B nb (IN nb Hn)). unfold chk in B. cbv zeta in B.
  repeat (apply andb_prop in B; destruct B as [B ?]).
  repeat match goal with H : (_ =? _) = true |- _ => apply Z.eqb_eq in H end.
  repeat split; assumption.
Qed.

Section CANSEC3. Context {rc : runConstT}.
Definition XC (m5 : amem) (SPV SPA lo DT DTB WK wksz FF r : Z) (hw rank : list Z) (tl : Z) (j0 j192 : list byte) (dt rst : list Z)
    (syb : list byte) (w cur sym cnt : Z) (k112 k120 k128 k136 k144 : word) (m1 : amem) : Prop :=
  4 + 2 * 2 ^ tl <= DTB
  /\ u8arr bsegs m1 DT (map (Z_to_bv 8) dt) /\ zlen dt = DTB /\ Forall isbyte dt
  /\ u8arr bsegs m1 (WK + 1236) (map (Z_to_bv 8) hw) /\ u8arr bsegs m1 WK (map (Z_to_bv 8) (u32b rank))
  /\ u8arr bsegs m1 (WK + 52) (map (Z_to_bv 8) (u32b rst)) /\ zlen rst = 13
  /\ stk bsegs m1 (WK + 104) (WK + 980) /\ u8arr bsegs m1 (WK + 980) syb /\ zlen syb = 256 /\ stk bsegs m1 (WK + 1492) (WK + wksz)
  /\ stk bsegs m1 lo SPA /\ mem_inv bsegs m1
  /\ munch [(DT, DT + DTB); (WK, WK + wksz); (SPV - 5440, SPA + 216); (FF + 32, FF + 36)] m5 m1 /\ wmono bsegs m5 m1
  /\ rw_cells bsegs m1 SPA (X1FR1 DT WK FF r tl j0)
  /\ rw_cells bsegs m1 (SPA + 80) [C8 (Z_to_bv 64 cur); C8 (Z_to_bv 64 sym); C8 (Z_to_bv 64 WK); C8 (Z_to_bv 64 w);
                                    C8 k112; C8 k120; C8 k128; C8 k136; C8 k144; C8 (Z_to_bv 64 cnt)]
  /\ rw_cells bsegs m1 (SPA + 160) (X1FR4 DT WK FF j192).
End CANSEC3.

Ltac open_xf I :=
  destruct I as (DTF & DTC & DTLEN & DTBY & HWC & RK & RST & RSTLEN & STS & SYC & SYLEN & WKR & STK & MI & MU & WM & FR1 & F2 & FR4);
  destruct F2 as (k104 & k112 & k120 & k128 & k136 & k144 & k152 & FR2); unfold X1FR1 in FR1; unfold X1FR4 in FR4.
Ltac close_xf :=
  unfold XF, X1FR1, X1FR4, XFR2;
  repeat (split; [first [eassumption | do 7 eexists; eassumption]|]); first [eassumption | do 7 eexists; eassumption].
Ltac open_xc I :=
  destruct I as (DTF & DTC & DTLEN & DTBY & HWC & RK & RST & RSTLEN & STS & SYC & SYLEN & WKR & STK & MI & MU & WM & FR1 & FR2 & FR4);
  unfold X1FR1 in FR1; unfold X1FR4 in FR4.
Ltac close_xc := unfold XC, X1FR1, X1FR4; repeat (split; [eassumption|]); eassumption.

Lemma x1f_lxor_ones : forall x, 0 <= x < 2^64 -> Z.lxor x (Z.ones 64) = Z.ones 64 - x.
Proof.
  intros x Hx.
  assert (L : Z.land x (Z.lxor x (Z.ones 64)) = 0).
  { apply Z.bits_inj_0. intros n. rewrite Z.land_spec, Z.lxor_spec.
    destruct (Z.testbit x n) eqn:E; [|reflexivity]. cbn.
    destruct (Z.lt_ge_cases n 0) as [Hn0|Hn0]; [rewrite Z.testbit_neg_r in E by lia; discriminate|].
    destruct (Z.lt_ge_cases n 64) as [Hn|Hn].
    - rewrite Z.ones_spec_low by lia. reflexivity.
    - exfalso. rewrite <- (Z.mod_small x (2^64)) in E by lia. rewrite Z.mod_pow2_bits_high in E by lia. discriminate. }
  pose proof (Z.add_nocarry_lxor _ _ L) as A.
  rewrite <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l in A. lia.
Qed.

Section CANSEC4. Context {rc : runConstT}.
Lemma x1f_u32q_c4 : forall m A x, u8arr bsegs m A (map (Z_to_bv 8) (u32q x)) -> 0 <= x < 2^32 ->
  rw_cells bsegs m A [C4 (Z_to_bv 64 x)].
Proof.
  intros m A x H R. apply rw_cells_of_u8arr in H.
  eapply rw_cells_recast; [exact H| cbn; tauto| | reflexivity].
  unfold u32q. cbn [cells_bytes cbytes map app]. unfold le4. rewrite ?app_nil_r.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite (Z.mod_small x) by lia.
  cbn [Z_to_le_bytes]. rewrite ?app_nil_r. rewrite !Z.shiftr_div_pow2 by lia. rewrite ?Z.div_div by lia.
  repeat (apply f_equal2; [apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
                           Z.div_mod_to_equations; lia|]).
  reflexivity.
Qed.

Lemma x1f_u32b_at : forall (rk : list Z) m A i, u8arr bsegs m A (map (Z_to_bv 8) (u32b rk)) -> 0 <= i < zlen rk ->
  0 <= Znth i rk < 2^32 -> rw_cells bsegs m (A + 4 * i) [C4 (Z_to_bv 64 (Znth i rk))].
Proof.
  induction rk as [|x t IH]; intros m A i H Hi R; [cbn in Hi; lia|].
  cbn [u32b] in H. rewrite map_app in H. apply (proj1 (u8arr_app bsegs _ _ _ _)) in H. destruct H as [H0 H1].
  destruct (Z.eq_dec i 0) as [->|Hi0].
  - change (Znth 0 (x :: t)) with x in *. rewrite Z.mul_0_r, Z.add_0_r. exact (x1f_u32q_c4 m A x H0 R).
  - assert (EZ : Znth i (x :: t) = Znth (i - 1) t).
    { unfold Znth. replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia. reflexivity. }
    rewrite EZ in *.
    replace (A + 4 * i) with (A + zlen (map (Z_to_bv 8) (u32q x)) + 4 * (i - 1)) by (rewrite length_map; cbn; lia).
    apply IH; [exact H1| cbn [length] in Hi; lia| exact R].
Qed.

Lemma x1f_cb8_c8 : forall m A pre j post, rw_cells bsegs m A (pre ++ CB 8 j :: post) ->
  exists w, rw_cells bsegs m A (pre ++ C8 w :: post).
Proof.
  intros m A pre j post H.
  assert (L : length j = 8%nat).
  { destruct H as ((WF & _) & _). apply cells_wf_app in WF. destruct WF as [_ [WJ _]]. exact WJ. }
  exists (le_bytes_to_word j).
  apply (rw_cells_recell_mid bsegs m A pre [CB 8 j] post [C8 (le_bytes_to_word j)]) in H; [exact H| cbn; tauto|].
  cbn [cells_bytes cbytes app]. rewrite !app_nil_r, le8_of_bytes by exact L. reflexivity.
Qed.
End CANSEC4.

Ltac x1f_wordify8_go H m A pre rest :=
  lazymatch rest with
  | CB 8 ?j :: ?post =>
      let w := fresh "k" in let H' := fresh "WH" in
      destruct (x1f_cb8_c8 m A pre j post H) as [w H']; clear H; rename H' into H;
      let pre' := eval cbn [app] in (pre ++ [C8 w]) in x1f_wordify8_go H m A pre' post
  | ?c :: ?post => let pre' := eval cbn [app] in (pre ++ [c]) in x1f_wordify8_go H m A pre' post
  | nil => cbn [app] in H
  end.
Ltac x1f_wordify8 H := lazymatch type of H with rw_cells _ ?m ?A ?cs => x1f_wordify8_go H m A (@nil cell) cs end.

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
  Section FK.
  Variables (hw rank : list Z) (nbs tl mtl : Z).
  Hypothesis STATS : huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl.
  Hypothesis TLR : 1 <= tl <= 12.
  Hypothesis NBSR : 2 <= nbs <= 256.
  Hypothesis LHW : zlen hw = 256.
  Hypothesis BHW : Forall isbyte hw.
  Hypothesis LRK : zlen rank = 13.
  Notation XBm := (XB m5 SPV SPA lo DT DTB WK wksz FF r hw rank tl).
  Notation XFm := (XF m5 SPV SPA lo DT DTB WK wksz FF r hw rank tl).
  Local Ltac setreg_m r z' :=
    let v := StepF.reg_val r in
    lazymatch v with
    | Z_to_bv 64 z' => idtac
    | Z_to_bv 64 ?z => replace (Z_to_bv 64 z) with (Z_to_bv 64 z') by (first [ f_equal; lia | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia ])
    end.
  Notation SF pc mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 0x7fff8000) xs4 xs5
             (Z_to_bv 64 18446744073709551607) (Z_to_bv 64 18446744073709551599) (Z_to_bv 64 18446744073709551591) xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation STW mm w xra x5 x6 x7 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (SF 0x81030 mm xra x5 x6 x7 xa0 (Z_to_bv 64 w) xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs9 xs10 xs11 x28 x29 x30 x31).
  Notation XCm := (XC m5 SPV SPA lo DT DTB WK wksz FF r hw rank tl).
  Notation NRS := (18446744073709551615 - (WK + 52)) (only parsing).
  Notation STF mm x5 x6 xa0 xa2 xa4 xa5 x28 x29 x30 x31 :=
    (ST 0x80fa8 mm (Z_to_bv 64 0x80454) x5 x6 (Z_to_bv 64 (WK + 980)) xa0 (Z_to_bv 64 (WK + 52)) xa2 (Z_to_bv 64 NRS) xa4 xa5 (Z_to_bv 64 nbs) (Z_to_bv 64 (WK / 8))
        (Z_to_bv 64 FF) (Z_to_bv 64 r) (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 18446744073709551572) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 n0) (Z_to_bv 64 SRC) flags (Z_to_bv 64 (FF + 48))
        x28 x29 x30 x31).
  Hypothesis DTBT : 4 + 2 * 2 ^ tl <= DTB.

  Hypothesis KEND : forall m2 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (rsacc sym : Z)
      (xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs5 xs9 xs10 xs11 x28 x29 x30 x31 : word),
    XFm j0 j192 dt rst syb rsacc sym m2 -> x1pref mtl tl (2^tl) dt ->
    evtF bsegs RNG POST (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 FF) (Z_to_bv 64 0x7fff8000)
                                  xs4 xs5 (Z_to_bv 64 r) (Z_to_bv 64 18446744073709551599) (Z_to_bv 64 18446744073709551591) xs9 xs10 xs11 x28 x29 x30 x31)
                           F (Z_to_bv 64 0x80618) fc None m2 (seg_rom bsegs)).
  Lemma x1_fdoneA : forall m1 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (rsacc sym : Z)
      xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs9 xs10 xs11 x28 x29 x30 x31,
    XFm j0 j192 dt rst syb rsacc sym m1 -> x1pref mtl tl (2^tl) dt ->
    evtF bsegs RNG POST (SF 0x80fb4 m1 xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs9 xs10 xs11 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I PF. pose proof I as I0. open_xf I.
    pose proof HY as H0. unfold x1A_hyps in H0. destruct H0 as (_ & _ & _ & _ & _ & _ & _ & _ & ALO & LOS & SPH & SP16 & SPAR & SPA32 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RLO & RAI).
    assert (RSTA : rng RNG SPA 216)
      by (apply (rng_sub' _ _ _ _ _ RLO); lia).
    clear - FR1 RSTA RAI ALO LOS SPH SP16 SPAR SPA32 Hr KEND I0 PF.
    zstep.
    zstep.
    zstep.
    zstep.
    eapply KEND; [exact I0| exact PF].
  Qed.


  Lemma x1f_sw : forall z, 0 <= z < 2^31 -> bv_swrap 32 z = z.
  Proof.
    intros z Hz. assert (HM : bv_half_modulus 32 = 2^31) by reflexivity. assert (MM : bv_modulus 32 = 2^32) by reflexivity.
    unfold bv_swrap, bv_wrap. rewrite HM, MM. rewrite Z.mod_small by lia. lia.
  Qed.

  Local Ltac x1f_zz :=
    unfold sx32, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *; rewrite ?Z_to_bv_unsigned in *;
    unfold bv_wrap, bv_modulus in *; cbn [Z.of_N] in *; Z.div_mod_to_equations; lia.
  Local Ltac x1f_land :=
    repeat match goal with
    | |- context [Z.land ?x ?m] =>
        let ok1 := eval vm_compute in (m =? -1) in
        lazymatch ok1 with
        | true => replace (Z.land x m) with x by (symmetry; apply Z.land_m1_r)
        | false =>
            let k := eval vm_compute in (Z.log2 (m + 1)) in
            let ok := eval vm_compute in (m =? Z.ones k) in
            lazymatch ok with true =>
              replace (Z.land x m) with (x mod 2 ^ k) by (change m with (Z.ones k); symmetry; apply Z.land_ones; lia) end
        end
    end.
  Local Ltac x1f_lxor :=
    lazymatch goal with |- context [Z.lxor ?x ?a] =>
      let ok1 := eval vm_compute in (a =? -1) in
      lazymatch ok1 with
      | true => rewrite (Z.lxor_m1_r x); unfold Z.lnot; Z.div_mod_to_equations; lia
      | false =>
          let ok2 := eval vm_compute in (a =? Z.ones 64) in
          lazymatch ok2 with true =>
            change a with (Z.ones 64); rewrite (x1f_lxor_ones x) by lia; rewrite Z.ones_equiv; Z.div_mod_to_equations; lia end
      end
    end.
  Local Ltac x1f_brw K W P H :=
    first [ bcase K; try (exfalso; clear - K W P H TLR; first [lia | rewrite ?signed_lit_small64 in K by lia; lia | x1f_zz])
          | idtac ].

  Lemma x1f_rank_small : forall v, 0 <= v <= 12 -> 0 <= Znth v rank <= 256.
  Proof.
    intros v Hv. destruct STATS as (_ & (_ & LENW) & _ & _ & CNT & _). rewrite (CNT v Hv). unfold hcount.
    pose proof (count_occ_bound Z.eq_dec v (firstn (Z.to_nat nbs) hw)) as CB. unfold FseNCount.Zlength in LENW. lia.
  Qed.

  Lemma x1_fsetA : forall m1 (dt rst : list Z) (syb jA jA2 jC jD jB jE : list byte) x5 x6 xa0 xa2 xa4 xa5 x28 x29 x30 x31,
    XBm (Z_to_bv 64 (WK + 980)) jA jA2 jC jD jB jE dt rst syb m1 ->
    (forall m2 (j0 j192 : list byte) (y5 ya0 ya2 ya3 ya7 : word),
       XFm j0 j192 dt rst syb 0 (Znth 0 rank) m2 ->
       evtF bsegs RNG POST (STW m2 1 (Z_to_bv 64 0x80454) y5 x6 (Z_to_bv 64 (WK + 980)) ya0 ya2 ya3 xa4 xa5 (Z_to_bv 64 nbs) ya7
                              (Z_to_bv 64 FF) (Z_to_bv 64 r) (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 SRC) flags (Z_to_bv 64 (FF + 48)) x28 x29 x30 x31)) ->
    evtF bsegs RNG POST (STF m1 x5 x6 xa0 xa2 xa4 xa5 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I K.
    destruct I as (DTC & DTLEN & DTBY & HWC & RK & RST & RSTLEN & RSTP & STS & SYC & SYLEN & WKR & STK & MI & MU & WM & FRB).
    unfold X1FRB in FRB.
    pose proof HY as H0. unfold x1A_hyps in H0.
    destruct H0 as (D1 & D2 & D3 & W1h & W2h & W3h & WKS & KHL & ALO & LOS & SPH & SP16 & SPAR & SPA32 & DSP & WSP & DWK & F64 & F4K & FAT
                    & FBL & DFF & WFF & DBL & RDT & RSD & WBL & RWK & RSW & RFF & RLO & RAI).
    assert (RSTA : rng RNG SPA 216) by (apply (rng_sub' _ _ _ _ _ RLO); lia).
    assert (SDSA : DT + DTB <= SPA \/ SPA + 216 <= DT) by (clear - DSP LOS SPAR; lia).
    assert (SWSA : WK + wksz <= SPA \/ SPA + 216 <= WK) by (clear - WSP LOS SPAR; lia).
    assert (SFF : FF + 64 <= SPA) by (clear - FAT ALO LOS SPAR; lia).
    assert (UW1 : unpoisoned m1 WK (WK + wksz)) by (eapply x1_unp_wkM; eassumption).
    pose proof (x1f_rank_small 0 ltac:(lia)) as R0.
    pose proof (x1f_u32b_at rank m1 WK 0 RK ltac:(lia) ltac:(lia)) as RK0. replace (WK + 4 * 0) with WK in RK0 by lia.
    assert (SH0 : ov_read_bytes bsegs m1 (wa (ASHOFF + WK / 8)) 1 = Some [Z_to_bv 8 0]).
    { eapply unpoisoned_full_rd; [exact UW1| rewrite shad_div; lia| clear - WKS W1h W2h; Z.div_mod_to_equations; lia]. }
    assert (RSH : rng RNG (ASHOFF + WK / 8) 1).
    { rewrite <- shad_div. apply (rng_sub' _ _ _ _ _ RSW); unfold shspan; clear - WKS W1h; Z.div_mod_to_equations; lia. }
    unfold ASHOFF in SH0, RSH.
    clear DSP WSP DWK DFF WFF UW1.
    assert (LRKb : zlen (map (Z_to_bv 8) (u32b rank)) = 52) by (rewrite length_map, u32b_length; lia).
    assert (LRSb : zlen (map (Z_to_bv 8) (u32b rst)) = 52) by (rewrite length_map, u32b_length; lia).
    assert (LHWb : zlen (map (Z_to_bv 8) hw) = 256) by (rewrite length_map; lia).
    assert (LDTb : zlen (map (Z_to_bv 8) dt) = DTB) by (rewrite length_map; lia).
    zstep.
    zstep.
    zstep.
    bcase K0; [| exfalso; clear - K0 TLR; first [lia | x1f_zz]
      ].
    zstep.
    zstep.
    clear SH0 RSH.
    zstep.
    bcase K1; [exfalso; apply K1; vm_compute; reflexivity
      |].
    zstep.
    zstep.
    zstep.
    zstep.
    zstep.
    zstep.
    zstep.
    zstep.
    zstep.
    zstep.
    rewrite (FseRdKit2.sx32_small (Znth 0 rank)) by lia.
    zstep.
    zstep.
    zstep.
    zstep.
    zstep.
    zstep.
    zstep.
    zstep.
    zstep.
    zstep.
    zstep.
    zstep.
    zstep.
    zstep.
    zstep.
    zstep.
    let v := eval vm_compute in (2^64 - 9) in replace (Z_to_bv 64 (-9)) with (Z_to_bv 64 v) by (apply Z_to_bv_eqm; vm_compute; reflexivity).
    let v := eval vm_compute in (2^64 - 17) in replace (Z_to_bv 64 (-17)) with (Z_to_bv 64 v) by (apply Z_to_bv_eqm; vm_compute; reflexivity).
    let v := eval vm_compute in (2^64 - 25) in replace (Z_to_bv 64 (-25)) with (Z_to_bv 64 v) by (apply Z_to_bv_eqm; vm_compute; reflexivity).
    lazymatch goal with H : rw_cells _ _ SPA _ |- _ => rename H into FRA end.
    assert (TL1 : (tl + 1 <? 1) = false) by (apply Z.ltb_ge; lia).
    rewrite TL1 in FRA. cbn [Z.b2z] in FRA. rewrite Z.add_0_r in FRA. clear TL1.
    lazymatch type of FRA with context [Z.land (Z.land (tl + 1) ?a) ?b] =>
      replace (Z.land (Z.land (tl + 1) a) b) with (tl + 1) in FRA by (clear - TLR; x1f_land; Z.div_mod_to_equations; lia) end.
    lazymatch eval cbv [X1FR1] in (X1FR1 0 WK 0 0 0 []) with [_; _; _; _; _; _; C8 (Z_to_bv 64 (?D - WK)); _; _; _] =>
      lazymatch type of FRA with context [Z.lxor WK ?a] =>
        replace (Z_to_bv 64 (Z.lxor WK a)) with (Z_to_bv 64 (D - WK)) in FRA by (apply Z_to_bv_eqm; clear - W1h W2h WKS; x1f_lxor) end end.
    lazymatch eval cbv [X1FR4] in (X1FR4 0 WK 0 []) with [C8 (Z_to_bv 64 ?d4); C8 (Z_to_bv 64 (?D - (WK + 980))); _; _; _; _] =>
      lazymatch type of FRA with context [Z.lxor (WK + 980) ?a] =>
        replace (Z_to_bv 64 (Z.lxor (WK + 980) a)) with (Z_to_bv 64 (D - (WK + 980))) in FRA by (apply Z_to_bv_eqm; clear - W1h W2h WKS; x1f_lxor) end;
      lazymatch type of FRA with rw_cells _ _ _ [_; _; C8 (Z_to_bv 64 ?km); _; _; _; _; _; _; _; _; _; _; _; C8 (Z_to_bv 64 ?c4); _; _; _; _; _] =>
        replace (Z_to_bv 64 km) with (Z_to_bv 64 X1_KM32) in FRA by (apply Z_to_bv_eqm; unfold X1_KM32; vm_compute; reflexivity);
        replace (Z_to_bv 64 c4) with (Z_to_bv 64 d4) in FRA by (apply Z_to_bv_eqm; vm_compute; reflexivity) end end.
    lazymatch type of FRA with rw_cells _ ?mm _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; ?c11; ?c12; CB 56 ?j; ?c14; ?c15; ?c16; ?c17; ?c18; ?c19] =>
      apply (rw_cells_split_CB bsegs _ _ [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12] 56 j [c14; c15; c16; c17; c18; c19] [8; 8; 8; 8; 8; 8; 8]%nat) in FRA; [| reflexivity];
      cbn [mk_CB_cells app] in FRA end.
    lazymatch type of FRA with rw_cells _ ?mm _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?rest) =>
      pose proof (proj1 (rw_cells_app bsegs mm SPA [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9] rest) FRA) as [FR1 FRX]; clear FRA;
      cbn [cells_size csize Nat.add] in FRX end.
    lazymatch type of FRX with rw_cells _ ?mm ?A (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?rest) =>
      pose proof (proj1 (rw_cells_app bsegs mm A [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9] rest) FRX) as [FR2 FR4]; clear FRX;
      cbn [cells_size csize Nat.add] in FR4 end.
    x1f_wordify8 FR2.
    replace (SPA + Z.of_nat 80 + Z.of_nat 80) with (SPA + 160) in FR4 by (clear; lia).
    replace (SPA + Z.of_nat 80) with (SPA + 80) in FR2 by (clear; lia).
    eapply K. unfold XF, X1FR1, X1FR4; repeat (split; [eassumption|]).
    split; [unfold XFR2; do 7 eexists; exact FR2| exact FR4].
  Qed.

  Notation STC pc mm nb len xra x5 x6 x7 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31 :=
    (SF pc mm xra x5 x6 x7 xa0 (Z_to_bv 64 nb) xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 (Z_to_bv 64 len) xs10 xs11 x28 x29 x30 x31).
  Lemma x1_wheadA : forall m1 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (w cur sym : Z)
      xra x5 x6 x7 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs9 xs10 xs11 x28 x29 x30 x31,
    XFm j0 j192 dt rst syb cur sym m1 -> 1 <= w <= tl -> cur = xcur rank w -> sym = xsym rank w ->
    (forall m2 k112 k120 k128 k136 k144 (y5 y6 y7 ya0 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 : word), w = 1 -> XCm j0 j192 dt rst syb w cur sym (Znth w rank) k112 k120 k128 k136 k144 m2 ->
       evtF bsegs RNG POST (STC 0x816e0 m2 (tl + 1 - w) 1 xra y5 y6 y7 ya0 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs4 xs5 xs10 xs11 y28 y29 y30 y31)) ->
    (forall m2 k112 k120 k128 k136 k144 (y5 y6 y7 ya0 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 : word), w = 2 -> XCm j0 j192 dt rst syb w cur sym (Znth w rank) k112 k120 k128 k136 k144 m2 ->
       evtF bsegs RNG POST (STC 0x81098 m2 (tl + 1 - w) 2 xra y5 y6 y7 ya0 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs4 xs5 xs10 xs11 y28 y29 y30 y31)) ->
    (forall m2 k112 k120 k128 k136 k144 (y5 y6 y7 ya0 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 : word), w = 3 -> XCm j0 j192 dt rst syb w cur sym (Znth w rank) k112 k120 k128 k136 k144 m2 ->
       evtF bsegs RNG POST (STC 0x8180c m2 (tl + 1 - w) 4 xra y5 y6 y7 ya0 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs4 xs5 xs10 xs11 y28 y29 y30 y31)) ->
    (forall m2 k112 k120 k128 k136 k144 (y5 y6 y7 ya0 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 : word), w = 4 -> XCm j0 j192 dt rst syb w cur sym (Znth w rank) k112 k120 k128 k136 k144 m2 ->
       evtF bsegs RNG POST (STC 0x81248 m2 (tl + 1 - w) 8 xra y5 y6 y7 ya0 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs4 xs5 xs10 xs11 y28 y29 y30 y31)) ->
    (forall m2 k112 k120 k128 k136 k144 (y5 y6 y7 ya0 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 : word) (len : Z), 5 <= w -> len = 2^(w - 1) ->
       XCm j0 j192 dt rst syb w cur sym (Znth w rank) k112 k120 k128 k136 k144 m2 ->
       evtF bsegs RNG POST (STC 0x813f8 m2 (tl + 1 - w) len xra y5 y6 y7 ya0 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs4 xs5 xs10 xs11 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (STW m1 w xra x5 x6 x7 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs9 xs10 xs11 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I HW12 HC HS K1 K2 K4 K8 KD. open_xf I.
    pose proof HY as H0. unfold x1A_hyps in H0.
    destruct H0 as (D1 & D2 & D3 & W1h & W2h & W3h & WKS & KHL & ALO & LOS & SPH & SP16 & SPAR & SPA32 & DSP & WSP & DWK & F64 & F4K & FAT
                    & FBL & DFF & WFF & DBL & RDT & RSD & WBL & RWK & RSW & RFF & RLO & RAI).
    assert (RSTA : rng RNG SPA 216) by (apply (rng_sub' _ _ _ _ _ RLO); lia).
    assert (SDSA : DT + DTB <= SPA \/ SPA + 216 <= DT) by (clear - DSP LOS SPAR; lia).
    assert (SWSA : WK + wksz <= SPA \/ SPA + 216 <= WK) by (clear - WSP LOS SPAR; lia).
    assert (SFF : FF + 64 <= SPA) by (clear - FAT ALO LOS SPAR; lia).
    pose proof (x1f_rank_small w ltac:(lia)) as CNTR.
    pose proof (x1f_u32b_at rank m1 WK w RK ltac:(lia) ltac:(lia)) as RKw.
    assert (RSH : rng RNG (ASHOFF + (WK + 4 * w) / 8) 1).
    { rewrite <- shad_div. apply (rng_sub' _ _ _ _ _ RSW); rewrite ?shad_div; unfold shspan;
        clear - WKS W1h HW12 TLR; Z.div_mod_to_equations; lia. }
    unfold ASHOFF in RSH.
    clear DSP WSP DWK DFF WFF.
    assert (LRKb : zlen (map (Z_to_bv 8) (u32b rank)) = 52) by (rewrite length_map, u32b_length; lia).
    assert (LRSb : zlen (map (Z_to_bv 8) (u32b rst)) = 52) by (rewrite length_map, u32b_length; lia).
    assert (LHWb : zlen (map (Z_to_bv 8) hw) = 256) by (rewrite length_map; lia).
    assert (LDTb : zlen (map (Z_to_bv 8) dt) = DTB) by (rewrite length_map; lia).
    zstep.
    zstep.
    zstep.
    bcase KC1; [exfalso; clear - KC1 HW12 TLR; first [lia | x1f_zz]
      |].
    zstep.
    zstep.
    lazymatch goal with |- context [Z.shiftl w 2] =>
      replace (Z.shiftl w 2) with (4 * w) by (rewrite Z.shiftl_mul_pow2 by lia; lia) end.
    zstep.
    zstep.
    bcase KC2; [exfalso; clear - KC2 HW12 TLR W1h W2h WKS; first [lia | x1f_zz]
      |].
    zstep.
    zstep.
    zstep.
    try lazymatch goal with |- context [Z.land (WK + 4 * w) ?m] =>
      replace (Z.land (WK + 4 * w) m) with (WK + 4 * w) by (clear - W1h W2h WKS HW12 TLR; x1f_land; Z.div_mod_to_equations; lia) end.
    try replace (Z.shiftr (WK + 4 * w) 3) with ((WK + 4 * w) / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (UW1 : unpoisoned mm WK (WK + wksz)) by (eapply x1_unp_wkM; eassumption);
      assert (SH0 : ov_read_bytes bsegs mm (wa (ASHOFF + (WK + 4 * w) / 8)) 1 = Some [Z_to_bv 8 0])
        by (eapply unpoisoned_full_rd; [exact UW1| rewrite shad_div; clear - W1h HW12; Z.div_mod_to_equations; lia
                                       | clear - WKS W1h W2h HW12 TLR; Z.div_mod_to_equations; lia]) end.
    unfold ASHOFF in SH0. clear UW1.
    zstep.
    clear SH0 RSH.
    zstep.
    bcase KC3; [exfalso; apply KC3; vm_compute; reflexivity
      |].
    assert (RAW : rng RNG (WK + 4 * w) 4) by (apply (rng_sub' _ _ _ _ _ RWK); clear - WKS HW12 TLR; lia).
    remember (WK + 4 * w) as AW eqn:EAW.
    zstep.
    subst AW. clear RAW.
    rewrite (FseRdKit2.sx32_small (Znth w rank)) by lia.
    zstep.
    zstep.
    zstep.
    zstep.
    zstep.
    zstep.
    zstep.
    zstep.
    rewrite (x1f_sw (tl + 1 - w)) by lia.
    let v := StepF.reg_val 25 in
    lazymatch v with Z_to_bv 64 ?e =>
      replace e with (2 ^ (w - 1)) by (clear - HW12 TLR;
        assert (w = 1 \/ w = 2 \/ w = 3 \/ w = 4 \/ w = 5 \/ w = 6 \/ w = 7 \/ w = 8 \/ w = 9 \/ w = 10 \/ w = 11 \/ w = 12)
          as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]] by lia; vm_compute; reflexivity) end.
    assert (WCASE : (w = 1 /\ 2 ^ (w - 1) = 1) \/ (w = 2 /\ 2 ^ (w - 1) = 2) \/ (w = 3 /\ 2 ^ (w - 1) = 4)
                    \/ (w = 4 /\ 2 ^ (w - 1) = 8) \/ (5 <= w /\ 16 <= 2 ^ (w - 1) <= 2048)).
    { clear - HW12 TLR.
      assert (w = 1 \/ w = 2 \/ w = 3 \/ w = 4 \/ w = 5 \/ w = 6 \/ w = 7 \/ w = 8 \/ w = 9 \/ w = 10 \/ w = 11 \/ w = 12)
        as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]] by lia; cbn; lia. }
    destruct WCASE as [[Wc Pc]|[[Wc Pc]|[[Wc Pc]|[[Wc Pc]|[Wc Pc]]]]].
    - rewrite Pc.
      zstep. x1f_brw KD1 Wc Pc HW12.
      zstep. x1f_brw KD2 Wc Pc HW12.
      eapply K1; [exact Wc | close_xc].
    - rewrite Pc.
      zstep. x1f_brw KD1 Wc Pc HW12.
      zstep. x1f_brw KD2 Wc Pc HW12.
      zstep.
      zstep. x1f_brw KD3 Wc Pc HW12.
      eapply K2; [exact Wc | close_xc].
    - rewrite Pc.
      zstep. x1f_brw KD1 Wc Pc HW12.
      zstep.
      zstep. x1f_brw KD2 Wc Pc HW12.
      eapply K4; [exact Wc | close_xc].
    - rewrite Pc.
      zstep. x1f_brw KD1 Wc Pc HW12.
      zstep.
      zstep. x1f_brw KD2 Wc Pc HW12.
      zstep.
      zstep. x1f_brw KD3 Wc Pc HW12.
      eapply K8; [exact Wc | close_xc].
    - zstep. x1f_brw KD1 Wc Pc HW12.
      zstep.
      zstep. x1f_brw KD2 Wc Pc HW12.
      zstep.
      zstep. x1f_brw KD3 Wc Pc HW12.
      eapply KD; [exact Wc | reflexivity | close_xc].
  Qed.
  Notation STL mm len xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31 :=
    (SF 0x81964 mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 (Z_to_bv 64 len) xs10 xs11 x28 x29 x30 x31).
  Lemma x1_latchA : forall m1 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (w cur sym cnt len : Z) (k112 k120 k128 k136 k144 : word)
      xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31,
    XCm j0 j192 dt rst syb w cur sym cnt k112 k120 k128 k136 k144 m1 -> 1 <= w <= tl -> 0 <= cnt <= 256 -> 0 <= sym -> sym + cnt <= 256 ->
    0 <= cur -> 1 <= len <= 2048 -> 0 <= cnt * len -> cur + cnt * len <= 2 ^ tl ->
    (forall m2 (y5 y6 y7 ya0 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 : word), w + 1 <= tl -> XFm j0 j192 dt rst syb (cur + cnt * len) (sym + cnt) m2 ->
       evtF bsegs RNG POST (STW m2 (w + 1) xra y5 y6 y7 ya0 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs4 xs5 (Z_to_bv 64 len) xs10 xs11 y28 y29 y30 y31)) ->
    (forall m2 (y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 : word), w = tl -> XFm j0 j192 dt rst syb (cur + cnt * len) (sym + cnt) m2 ->
       evtF bsegs RNG POST (SF 0x80fb4 m2 xra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs4 xs5 (Z_to_bv 64 len) xs10 xs11 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (STL m1 len xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I HW HCNT HS0 HS1 HC0 HLEN HP0 HP1 KH KE. open_xc I.
    pose proof HY as H0. unfold x1A_hyps in H0.
    destruct H0 as (D1 & D2 & D3 & W1h & W2h & W3h & WKS & KHL & ALO & LOS & SPH & SP16 & SPAR & SPA32 & DSP & WSP & DWK & F64 & F4K & FAT
                    & FBL & DFF & WFF & DBL & RDT & RSD & WBL & RWK & RSW & RFF & RLO & RAI).
    assert (RSTA : rng RNG SPA 216) by (apply (rng_sub' _ _ _ _ _ RLO); lia).
    assert (SDSA : DT + DTB <= SPA \/ SPA + 216 <= DT) by (clear - DSP LOS SPAR; lia).
    assert (SWSA : WK + wksz <= SPA \/ SPA + 216 <= WK) by (clear - WSP LOS SPAR; lia).
    assert (SFF : FF + 64 <= SPA) by (clear - FAT ALO LOS SPAR; lia).
    clear DSP WSP DWK DFF WFF.
    assert (LT : 2 ^ tl <= 4096) by (change 4096 with (2 ^ 12); apply Z.pow_le_mono_r; lia).
    assert (SB : 0 <= sym < 2^32) by (clear - HS0 HS1 HCNT; lia).
    assert (CB : 0 <= cur < 2^32) by (clear - HC0 HP0 HP1 LT; lia).
    assert (LRKb : zlen (map (Z_to_bv 8) (u32b rank)) = 52) by (rewrite length_map, u32b_length; lia).
    assert (LRSb : zlen (map (Z_to_bv 8) (u32b rst)) = 52) by (rewrite length_map, u32b_length; lia).
    assert (LHWb : zlen (map (Z_to_bv 8) hw) = 256) by (rewrite length_map; lia).
    assert (LDTb : zlen (map (Z_to_bv 8) dt) = DTB) by (rewrite length_map; lia).
    pose proof (rw_cells_C8_C4C4 bsegs m1 (SPA + 80) [C8 (Z_to_bv 64 cur)] [C8 (Z_to_bv 64 WK); C8 (Z_to_bv 64 w); C8 k112; C8 k120; C8 k128; C8 k136; C8 k144; C8 (Z_to_bv 64 cnt)] sym FR2 SB) as FR2s. cbn [app] in FR2s. clear FR2.
    zstep.
    pose proof (rw_cells_C4C4_C8 bsegs m1 (SPA + 80) [C8 (Z_to_bv 64 cur)] [C8 (Z_to_bv 64 WK); C8 (Z_to_bv 64 w); C8 k112; C8 k120; C8 k128; C8 k136; C8 k144; C8 (Z_to_bv 64 cnt)] sym FR2s SB) as FR2. cbn [app] in FR2. clear FR2s.
    zstep.
    zstep.
    zstep.
    zstep.
    zstep.
    bcase K1; [exfalso; clear - K1 HS0 HS1 HCNT HC0 HP0 HP1 HLEN LT; x1f_zz
      |].
    zstep.
    zstep.
    zstep.
    zstep.
    bcase K2; [exfalso; clear - K2 HS0 HS1 HCNT HC0 HP0 HP1 HLEN LT; x1f_zz
      |].
    zstep.
    lazymatch goal with H : rw_cells bsegs ?mm (SPA + 80) (C8 (Z_to_bv 64 cur) :: ?rest) |- _ =>
      pose proof (rw_cells_C8_C4C4 bsegs mm (SPA + 80) [] rest cur H CB) as FRc; cbn [app] in FRc; clear H end.
    zstep.
    lazymatch goal with H : rw_cells bsegs ?mm (SPA + 80) (C4 (Z_to_bv 64 cur) :: C4 (Z_to_bv 64 0) :: ?rest) |- _ =>
      pose proof (rw_cells_C4C4_C8 bsegs mm (SPA + 80) [] rest cur H CB) as FR2; cbn [app] in FR2; clear H end.
    zstep.
    zstep.
    zstep.
    zstep.
    bcase K3; [exfalso; clear - K3 HS0 HS1 HCNT HC0 HP0 HP1 HLEN LT; x1f_zz
      |].
    zstep.
    zstep.
    zstep.
    zstep.
    bcase KL.
    - assert (W1 : w + 1 <= tl) by (clear - KL HW; lia).
      lazymatch goal with H : rw_cells bsegs ?mm (SPA + 80) (C8 (Z_to_bv 64 ?a) :: C8 (Z_to_bv 64 ?b) :: _) |- _ =>
        replace a with (cur + cnt * len) in H by (clear - HS0 HS1 HCNT HC0 HP0 HP1 HLEN LT; x1f_zz);
        replace b with (sym + cnt) in H by (clear - HS0 HS1 HCNT HC0 HP0 HP1 HLEN LT; x1f_zz) end.
      try setreg_m 11 (w + 1).
      eapply KH; [exact W1 | close_xf
      ].
    - assert (W2 : w = tl) by (clear - KL HW; lia).
      zstep.
      lazymatch goal with H : rw_cells bsegs ?mm (SPA + 80) (C8 (Z_to_bv 64 ?a) :: C8 (Z_to_bv 64 ?b) :: _) |- _ =>
        replace a with (cur + cnt * len) in H by (clear - HS0 HS1 HCNT HC0 HP0 HP1 HLEN LT; x1f_zz);
        replace b with (sym + cnt) in H by (clear - HS0 HS1 HCNT HC0 HP0 HP1 HLEN LT; x1f_zz) end.
      eapply KE; [exact W2 | close_xf
      ].
  Qed.
  End FK.
End X1B.
End CANSEC1.
