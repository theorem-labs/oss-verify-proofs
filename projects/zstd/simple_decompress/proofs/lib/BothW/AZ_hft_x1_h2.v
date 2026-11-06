(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufWM ZdHufWX SepHide.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AProg_kit AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_kx AZ_hft_x1_seg AZ_hft_x1_defs.
From OSSVerify.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RZ_hft_x1_kit.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

Notation zlen l := (Z.of_nat (length l)).
Notation isbyte := (fun v : Z => 0 <= v < 256).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma u32b_firstn : forall k l, firstn (4 * k) (u32b l) = u32b (firstn k l).
Proof.
  induction k as [|k IH]; intros [|x l]; try reflexivity.
  replace (4 * S k)%nat with (S (S (S (S (4 * k)))))%nat by lia. cbn [firstn u32b u32q app]. rewrite IH. reflexivity.
Qed.
Lemma u32b_skipn : forall k l, skipn (4 * k) (u32b l) = u32b (skipn k l).
Proof.
  induction k as [|k IH]; intros [|x l]; try reflexivity.
  replace (4 * S k)%nat with (S (S (S (S (4 * k)))))%nat by lia. cbn [skipn u32b u32q app]. rewrite IH. reflexivity.
Qed.
Lemma u32b_repeat0 : forall k, u32b (repeat 0 k) = repeat 0 (4 * k).
Proof.
  induction k as [|k IH]; [reflexivity|].
  replace (4 * S k)%nat with (S (S (S (S (4 * k)))))%nat by lia. cbn [repeat u32b u32q app]. rewrite IH. reflexivity.
Qed.
Lemma map_repeat' : forall {A B} (f : A -> B) (a : A) k, map f (repeat a k) = repeat (f a) k.
Proof. intros A B f a k. induction k as [|k IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

(* [comment removed for export] *)
Lemma land_m1_l : forall s, 0 <= s < 18446744073709551616 -> Z.land 18446744073709551615 s = s.
Proof. intros s Hs. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
Lemma u32b_resc_split : forall (rk0 : list Z) (sc0 : Z), Z.of_nat (length rk0) = 13 -> 0 <= sc0 <= 12 ->
  map (Z_to_bv 8) (u32b ([Znth 0 rk0] ++ repeat 0 (Z.to_nat sc0) ++ skipn (Z.to_nat (sc0 + 1)) rk0))
  = firstn 4 (map (Z_to_bv 8) (u32b rk0)) ++ (repeat (Z_to_bv 8 0) (Z.to_nat (4 * sc0)) ++ skipn (Z.to_nat (4 * sc0)) (skipn 4 (map (Z_to_bv 8) (u32b rk0)))).
Proof.
  intros rk0 sc0 L Hs. rewrite !u32b_app, !map_app. destruct rk0 as [|x t]; [cbn in L; lia|].
  assert (E1 : map (Z_to_bv 8) (u32b [Znth 0 (x :: t)]) = firstn 4 (map (Z_to_bv 8) (u32b (x :: t)))).
  { rewrite firstn_map. change 4%nat with (4 * 1)%nat. rewrite u32b_firstn. reflexivity. }
  assert (E2 : map (Z_to_bv 8) (u32b (repeat 0 (Z.to_nat sc0))) = repeat (Z_to_bv 8 0) (Z.to_nat (4 * sc0))).
  { rewrite u32b_repeat0, map_repeat'. f_equal. lia. }
  assert (E3 : map (Z_to_bv 8) (u32b (skipn (Z.to_nat (sc0 + 1)) (x :: t))) = skipn (Z.to_nat (4 * sc0)) (skipn 4 (map (Z_to_bv 8) (u32b (x :: t))))).
  { rewrite skipn_skipn, !skipn_map. replace (Z.to_nat (4 * sc0) + 4)%nat with (4 * Z.to_nat (sc0 + 1))%nat by lia. rewrite u32b_skipn. reflexivity. }
  rewrite E1, E2, E3. reflexivity.
Qed.

(* [comment removed for export] *)
Definition zeroed (k sc : Z) (cur0 cur : list Z) : Prop :=
  zlen cur = 13 /\ forall v, 0 <= v <= 12 -> Znth v cur = if (k <? v) && (v <=? sc) then 0 else Znth v cur0.
Lemma zeroed_init : forall sc cur0, zlen cur0 = 13 -> zeroed sc sc cur0 cur0.
Proof. intros sc cur0 L. split; [exact L|]. intros v Hv. destruct (Z.ltb_spec sc v), (Z.leb_spec v sc); cbn [andb]; try reflexivity; lia. Qed.
Lemma zeroed_step : forall k sc cur0 cur, zeroed k sc cur0 cur -> 1 <= k <= sc -> sc <= 12 -> zeroed (k - 1) sc cur0 (Zupd k 0 cur).
Proof.
  intros k sc cur0 cur (L & H) Hk Hs. split; [rewrite Zupd_length; exact L|].
  intros v Hv. destruct (Z.eq_dec v k) as [->|NE].
  - rewrite Znth_Zupd_same by (unfold FseNCount.Zlength; lia). destruct (Z.ltb_spec (k - 1) k), (Z.leb_spec k sc); cbn [andb]; first [reflexivity | lia].
  - rewrite Znth_Zupd_other by lia. rewrite H by lia.
    destruct (Z.ltb_spec k v), (Z.ltb_spec (k - 1) v), (Z.leb_spec v sc); cbn [andb]; try reflexivity; lia.
Qed.
Lemma zeroed_resc : forall sc rank cur0 cur tl, shifted sc sc rank cur0 -> zeroed 0 sc cur0 cur -> 0 < sc -> tl + sc = 11 -> 1 <= tl ->
  (forall v, tl < v <= 12 -> Znth v rank = 0) -> rank_resc sc rank cur.
Proof.
  intros sc rank cur0 cur tl (L0 & H0) (L & H) Hsc HT TL HI. split; [unfold FseNCount.Zlength; exact L|].
  intros v Hv. rewrite H by lia.
  destruct (Z.eqb_spec v 0) as [->|NZ].
  - destruct (Z.ltb_spec 0 0); [lia|]. cbn [andb]. rewrite H0 by lia. destruct (Z.ltb_spec sc 0); [lia | reflexivity].
  - destruct (Z.leb_spec v sc).
    + destruct (Z.ltb_spec 0 v); [|lia]. cbn [andb]. destruct (Z.leb_spec v sc); [reflexivity | lia].
    + destruct (Z.ltb_spec 0 v); cbn [andb]; [| lia]. destruct (Z.leb_spec v sc); [lia|]. rewrite H0 by lia.
      destruct (Z.ltb_spec sc v), (Z.leb_spec v 11); cbn [andb]; try reflexivity; try lia.
      assert (v = 12) by lia. subst v. rewrite (HI 12) by lia. rewrite (HI (12 - sc)) by lia. reflexivity.
Qed.

Section CANSEC1. Context {rc : runConstT}.
Section X1B.
  Variables (RNG : footprint) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m5 : amem) (SPV SPA lo DT WK wksz FF r : Z).
  Hypothesis HY : x1A_hyps RNG SPV SPA lo DT WK wksz FF.
  Hypothesis UDT : unpoisoned m5 DT (DT + 16388).
  Hypothesis UW : unpoisoned m5 WK (WK + wksz).
  Hypothesis ART0 : art m5.
  Hypothesis Hr : 0 <= r < 2^32.
  Variable POST : machine_state -> Prop.
  (* [comment removed for export] *)
  Local Ltac kx_lia_bf :=
    lazymatch goal with
    | |- context [_ + _ <= _ \/ _] => first [ kx_sep_unhide5 DT WK SPA lo FF; lia | lia | kx_bv_ranges; lia ]
    | |- _ => first [ lia | kx_bv_ranges; lia ]
    end.
  Local Ltac kx_lia ::= kx_lia_bf.
  Local Ltac kxl_lia ::= kx_lia_bf.
  Local Ltac kxa_unpZ ::=
    lazymatch goal with
    | |- unpZ ?mm ?lo1 ?hi1 =>
        first [ kxa_hyp
              | let X := kxk_sbase5 DT WK SPA lo FF lo1 in
                lazymatch goal with
                | U : unpoisoned mm X ?hi0 |- _ => apply (unpoisoned_unpZ mm X hi0 lo1 hi1 U); solve [unfold KXKEND; kx_lia]
                end
              | match goal with
                | U : unpoisoned mm ?lo0 ?hi0 |- _ => apply (unpoisoned_unpZ mm lo0 hi0 lo1 hi1 U); solve [unfold KXKEND; kx_lia]
                end
              | kxa_unp_hook ]
    end.
  Local Ltac kxl_rng ::=
    first [ kxl_hyp
          | lazymatch goal with
            | |- rng ?RG ?A ?N =>
                let X := kxk_sbase5 DT WK SPA lo FF A in
                lazymatch goal with H : rng RG X ?N0 |- _ => apply (rng_sub' RG X N0 A N H); solve [kx_lia] end
            end
          | lazymatch goal with
            | |- rng ?RG ?A ?N => match goal with H : rng RG ?A0 ?N0 |- _ => apply (rng_sub' RG A0 N0 A N H); solve [kxl_lia_small] end
            end
          | kx_rng ].
  Local Ltac kxa_rng0 ::=
    kxa_norm;
    lazymatch goal with
    | |- rng ?RG (KXSHLO + ?A / 8) (shspanZ ?A ?n) =>
        first [ let X := kxk_sbase5 DT WK SPA lo FF A in
                lazymatch goal with
                | H : rng RG (shad X) ?N0 |- _ =>
                    apply (shad_shspan_rng RG A n (shad X) N0 H);
                    [ rewrite !shad_div; unfold ASHOFF; kx_lia | unfold shspanZ; rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia | kx_lia ]
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
  (* [comment removed for export] *)
  Local Ltac x1_reunp :=
    repeat match goal with H : unpoisoned ?mx _ _ |- _ => lazymatch mx with m5 => fail | _ => clear H end end;
    try match goal with H : art ?mx |- _ => lazymatch mx with m5 => fail | _ => clear H end end;
    lazymatch goal with
    | MU : munch _ m5 ?m2 |- _ =>
        pose proof (x1_unp_dtM _ _ _ _ _ _ _ _ _ HY UDT m2 MU) as UDT1;
        pose proof (x1_unp_wkM _ _ _ _ _ _ _ _ _ HY UW m2 MU) as UW1;
        try lazymatch goal with WM : wmono _ m5 m2 |- _ => pose proof (x1_artM _ _ _ _ _ _ _ _ _ HY ART0 m2 MU WM) as ART1 end
    | |- _ => idtac
    end.
  Local Ltac x1_open :=
    open_hx HY; unfold KHIGH in *;
    pose proof (x1_bands _ _ _ _ _ _ _ _ HY) as (BDT & BWK & BSP & BSP2 & B5 & B6 & B7 & BFF);
    assert (RSTA : rng RNG SPA 216) by (lazymatch goal with H : rng RNG lo (SPV - lo) |- _ => eapply rng_sub'; [exact H| lia] end);
    lazymatch goal with H1 : DT + 16388 <= lo \/ SPV <= DT, H2 : WK + wksz <= lo \/ SPV <= WK, H3 : lo <= SPV - 5936, H4 : SPV - 336 <= SPA <= SPV - 320 |- _ =>
      assert (SDSA : DT + 16388 <= SPA \/ SPA + 216 <= DT) by (clear - H1 H3 H4; lia);
      assert (SWSA : WK + wksz <= SPA \/ SPA + 216 <= WK) by (clear - H2 H3 H4; lia) end;
    hide_all_disj; x1_reunp.
  (* [comment removed for export] *)
  Notation KZB := [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16);
     KZRange DT 0x629000 (2^47 - 16388); KZRange WK 0x629000 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47);
     KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT 16388 SPA 216; KZDisj WK wksz SPA 216; KZDisj DT 16388 WK wksz] (only parsing).
  Notation ST pc mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 0x7fff8000) xs4
             xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Variables (n SRC : Z) (flags : word).
  Notation FRA0 jA jC jD jB jE := ([CB 24 jA; C8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)); C8 (Z_to_bv 64 FF); CB 16 jC; C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DT); CB 24 jD;
                                    C8 (Z_to_bv 64 WK); CB 80 jB; C8 (Z_to_bv 64 (DT + 4)); CB 16 jE; C8 (Z_to_bv 64 FF)]).
  (* [comment removed for export] *)
  Notation STR pc mm dtd nbs x5 x6 x7 xa1 xa2 xa7 x28 x29 :=
    (ST pc mm (Z_to_bv 64 0x97960) x5 x6 x7 (Z_to_bv 64 DT) xa1 xa2 (Z_to_bv 64 (0x7fff8000 + DT / 8)) (Z_to_bv 64 13) (Z_to_bv 64 11) (Z_to_bv 64 nbs) xa7
        (Z_to_bv 64 FF) (Z_to_bv 64 r) (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 18446744073709551572) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 n) (Z_to_bv 64 SRC) flags (Z_to_bv 64 (FF + 48))
        x28 x29 (Z_to_bv 64 dtd) (Z_to_bv 64 WK)).

  (* [comment removed for export] *)
  Local Ltac setreg_m r z' :=
    let v := StepF.reg_val r in
    lazymatch v with
    | Z_to_bv 64 z' => idtac
    | Z_to_bv 64 ?z => replace (Z_to_bv 64 z) with (Z_to_bv 64 z') by (first [ f_equal; lia | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia ])
    end.

  Section RESC.
  Variables (hw rank dt : list Z) (nbs tl dtd sc fl : Z) (jA jC jD jB jE j3 j5 j6 : list byte).
  Hypothesis STATS : huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl.
  Hypothesis TLR : 1 <= tl <= 10.
  Hypothesis NBSR : 2 <= nbs <= 256.
  Hypothesis LHW : zlen hw = 256.
  Hypothesis BHW : Forall isbyte hw.
  Hypothesis LRK : zlen rank = 13.
  Hypothesis SCE : sc = 11 - tl.
  Hypothesis DTLEN : zlen dt = 16388.
  (* [comment removed for export] *)
  Notation hwk k := (map (resc sc) (firstn (Z.to_nat k) hw) ++ skipn (Z.to_nat k) hw).
  (* [comment removed for export] *)
  Definition XH (hwc rk : list Z) (m1 : amem) : Prop :=
    u8arr bsegs m1 DT (map (Z_to_bv 8) dt)
    /\ u8arr bsegs m1 (WK + 1236) (map (Z_to_bv 8) hwc)
    /\ u8arr bsegs m1 WK (map (Z_to_bv 8) (u32b rk))
    /\ stk bsegs m1 (WK + 52) (WK + 1236) /\ stk bsegs m1 (WK + 1492) (WK + wksz) /\ stk bsegs m1 lo SPA
    /\ mem_inv bsegs m1 /\ munch [(DT, DT + 16388); (WK, WK + wksz); (SPV - 5440, SPA + 216); (FF + 32, FF + 36)] m5 m1 /\ wmono bsegs m5 m1
    /\ rw_cells bsegs m1 SPA (FRA0 jA jC jD jB jE)
    /\ rw_cells bsegs m1 FF (X1FFHDR fl j3 j5 j6 (Z_to_bv 64 tl) (Z_to_bv 64 nbs)).
  Local Ltac open_xh I := destruct I as (DTC & HWC & RK & WS1 & WKR & STK & MI & MU & WM & FR & FFC); unfold X1FFHDR in FFC.
  Local Ltac close_xh := unfold XH, X1FFHDR; repeat (split; [eassumption|]); eassumption.

  Lemma hw_small : forall i, 0 <= i < nbs -> 0 <= Znth i hw <= tl.
  Proof.
    intros i Hi. destruct STATS as (_ & _ & FA' & _).
    assert (WSI : Znth i (firstn (Z.to_nat nbs) hw) = Znth i hw).
    { unfold Znth. rewrite <- (firstn_skipn (Z.to_nat nbs) hw) at 2. rewrite app_nth1 by (rewrite length_firstn; lia). reflexivity. }
    rewrite <- WSI. apply (Forall_Znth _ _ i FA'). rewrite length_firstn. lia.
  Qed.
  Lemma rank_small : forall v, 0 <= v <= 12 -> 0 <= Znth v rank <= 256.
  Proof.
    intros v Hv. destruct STATS as (_ & (_ & LENW) & _ & _ & CNT & _). rewrite (CNT v Hv). unfold hcount.
    pose proof (count_occ_bound Z.eq_dec v (firstn (Z.to_nat nbs) hw)) as CB. unfold FseNCount.Zlength in LENW. lia.
  Qed.
  Lemma hwk_len : forall k, zlen (hwk k) = 256.
  Proof. intros k. rewrite resc_len_nat. exact LHW. Qed.
  Lemma hwk_bytes : forall k, 0 <= k <= nbs -> Forall isbyte (hwk k).
  Proof.
    intros k Hk. destruct STATS as (_ & _ & FA' & _). apply Forall_app. split.
    - replace (firstn (Z.to_nat k) hw) with (firstn (Z.to_nat k) (firstn (Z.to_nat nbs) hw)) by (rewrite firstn_firstn; f_equal; lia).
      apply Forall_map.
      eapply Forall_impl. 2: apply AProg_kit.Forall_firstnA; exact FA'. cbv beta. intros w Hw. unfold resc. destruct (Z.eqb_spec w 0); lia.
    - apply AProg_kit.Forall_skipnA. exact BHW.
  Qed.
  Lemma hwk_step : forall k, 0 <= k < 256 -> Zupd k (resc sc (Znth k hw)) (hwk k) = hwk (k + 1).
  Proof. intros k Hk. unfold Zupd, Znth. replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia. apply resc_step_nat. lia. Qed.

  (* [comment removed for export] *)
  Notation KZB2 := (KZB ++ [KZDisj WK wksz FF 64; KZDisj DT 16388 FF 64; KZRange tl 1 10; KZRange sc 1 10; KZRange nbs 2 256]) (only parsing).
  Notation NHW := (18446744073709551615 - (WK + 1236)) (only parsing).
  Notation NW := (18446744073709551615 - WK) (only parsing).

  (* [comment removed for export] *)
  Lemma x1_w_bodyA : forall m1 (rk : list Z) (k : Z) xa1 x28 x29,
    XH (hwk k) rk m1 -> zlen rk = 13 -> 0 <= k < nbs ->
    (forall m2 (ya1 y28 y29 : word), k + 1 < nbs -> XH (hwk (k + 1)) rk m2 ->
       evtF bsegs RNG POST (STR 0x979d8 m2 dtd nbs (Z_to_bv 64 sc) (Z_to_bv 64 (k + 1)) (Z_to_bv 64 NHW) ya1 (Z_to_bv 64 nbs) (Z_to_bv 64 tl) y28 y29)) ->
    (forall m2 (ya1 y28 y29 : word), k + 1 = nbs -> XH (hwk nbs) rk m2 ->
       evtF bsegs RNG POST (STR 0x97a3c m2 dtd nbs (Z_to_bv 64 sc) (Z_to_bv 64 NW) (Z_to_bv 64 11) ya1 (Z_to_bv 64 nbs) (Z_to_bv 64 tl) y28 y29)) ->
    evtF bsegs RNG POST (STR 0x979d8 m1 dtd nbs (Z_to_bv 64 sc) (Z_to_bv 64 k) (Z_to_bv 64 NHW) xa1 (Z_to_bv 64 nbs) (Z_to_bv 64 tl) x28 x29).
  Proof.
    intros until x29; intros I LRK2 HK KH KE. open_xh I. x1_open.
    remember (Znth k hw) as w eqn:EW.
    assert (NTHK : Znth k (hwk k) = w) by (rewrite EW; unfold Znth; apply resc_nth_nat).
    pose proof (hw_small k ltac:(lia)) as WB. rewrite <- EW in WB.
    assert (LHK : zlen (map (Z_to_bv 8) (hwk k)) = 256) by (rewrite length_map; apply hwk_len).
    assert (LRKB : zlen (map (Z_to_bv 8) (u32b rk)) = 52) by (rewrite length_map, u32b_length2, LRK2; reflexivity).
    assert (LDT : zlen (map (Z_to_bv 8) dt) = 16388) by (rewrite length_map; exact DTLEN).
    (* [comment removed for export] *)
    destruct (Z.eq_dec w 0) as [W0|WNZ].
    - subst w.
      kx_autoFLAc tt [KAUnp WK 1492; KAApp WK 1492] [0x979d8; 0x97a3c; 0x97b24; 0x98ed8] 60%nat
        (KZB2 ++ [KZRange k 0 255; KZWord (WK + 1236 + k) 1%nat 0; KZWr (WK + 1236) 256])
        [(SPA, 216)] [(WK, 1492); (SPA, 216)].
      1: split; [lia| split; [lia| split; [lia| replace (Z_to_bv 64 0) with (Z_to_bv 64 (Znth k (hwk k))) by (rewrite NTHK, W0; reflexivity);
                                                apply (rdn_u8Z bsegs m1 (WK + 1236) (hwk k) k HWC); [pose proof (hwk_len k); lia| rewrite NTHK, W0; lia]]]].
      all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x98ed8) _ _ _ _) => kx_trap_fast | _ => idtac end.
      all: kxk_keepg HWC. all: kx_mem. all: kx_tidy_run.
      all: repeat match goal with E : hidden (?v = _) |- _ => unfold hidden in E; subst v end.
      all: clear KXUL; match type of HWC with context [Zupd ?i _ _] => replace i with k in HWC by lia end; change (0 mod 256) with 0 in HWC.
      all: replace (Zupd k 0 (hwk k)) with (hwk (k + 1)) in HWC by (rewrite <- hwk_step, W0 by lia; reflexivity).
      all: lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x979d8) _ _ _ _) => eapply KH; [clear - KXBR HK; lia| close_xh]
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x97a3c) _ _ _ _) => setreg_m 6 (18446744073709551615 - WK);
               assert (EK : k + 1 = nbs) by (clear - KXBR HK; lia); rewrite EK in HWC; eapply KE; [exact EK| close_xh]
           end.
    - kx_autoFLAc tt [KAUnp WK 1492; KAApp WK 1492] [0x979d8; 0x97a3c; 0x97b24; 0x98ed8] 60%nat
        (KZB2 ++ [KZRange k 0 255; KZRange w 1 10; KZWord (WK + 1236 + k) 1%nat w; KZWr (WK + 1236) 256])
        [(SPA, 216)] [(WK, 1492); (SPA, 216)].
      1: split; [lia| split; [lia| split; [lia| rewrite <- NTHK; apply (rdn_u8Z bsegs m1 (WK + 1236) (hwk k) k HWC); [pose proof (hwk_len k); lia| rewrite NTHK; lia]]]].
      all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x98ed8) _ _ _ _) => kx_trap_fast | _ => idtac end.
      all: kxk_keepg HWC. all: kx_mem. all: kx_tidy_run.
      all: repeat match goal with E : hidden (?v = _) |- _ => unfold hidden in E; subst v end.
      all: clear KXUL; match type of HWC with context [Zupd ?i _ _] => replace i with k in HWC by lia end.
      all: match type of HWC with context [Zupd ?kk ?v (hwk ?kk2)] => replace (Zupd kk v (hwk kk2)) with (hwk (k + 1)) in HWC
        by (rewrite <- hwk_step, <- EW by lia; unfold resc; destruct (Z.eqb_spec w 0); [lia|]; rewrite ?Z.mod_small by lia; f_equal; rewrite ?land_m1_l by lia; lia) end.
      all: lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x979d8) _ _ _ _) => eapply KH; [clear - KXBR HK; lia| close_xh]
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x97a3c) _ _ _ _) => setreg_m 6 (18446744073709551615 - WK);
               assert (EK : k + 1 = nbs) by (clear - KXBR HK; lia); rewrite EK in HWC; eapply KE; [exact EK| close_xh]
           end.
  Qed.

  (* [comment removed for export] *)
  Lemma x1_w_loopA : forall (f : nat) m1 (rk : list Z) (k : Z) xa1 x28 x29,
    XH (hwk k) rk m1 -> zlen rk = 13 -> 0 <= k -> k + 1 + Z.of_nat f = nbs ->
    (forall m2 (ya1 y28 y29 : word), XH (hwk nbs) rk m2 ->
       evtF bsegs RNG POST (STR 0x97a3c m2 dtd nbs (Z_to_bv 64 sc) (Z_to_bv 64 NW) (Z_to_bv 64 11) ya1 (Z_to_bv 64 nbs) (Z_to_bv 64 tl) y28 y29)) ->
    evtF bsegs RNG POST (STR 0x979d8 m1 dtd nbs (Z_to_bv 64 sc) (Z_to_bv 64 k) (Z_to_bv 64 NHW) xa1 (Z_to_bv 64 nbs) (Z_to_bv 64 tl) x28 x29).
  Proof.
    induction f as [|f IH]; intros until x29; intros I LRK2 HK HF KE.
    - eapply (x1_w_bodyA m1 rk k); [exact I| exact LRK2| lia| intros; exfalso; lia|].
      intros m2 ya1 y28 y29 _ I2. eapply KE; exact I2.
    - eapply (x1_w_bodyA m1 rk k); [exact I| exact LRK2| lia| | intros; exfalso; lia].
      intros m2 ya1 y28 y29 Hk I2.
      eapply (IH m2 rk (k + 1)); [exact I2| exact LRK2| lia| lia| exact KE].
  Qed.

  (* [comment removed for export] *)
  Lemma x1_s_bodyA : forall m1 (rk : list Z) (q t2v a7v : Z) xa1 xa2 x28 x29,
    XH (hwk nbs) rk m1 -> shifted (q + sc) sc rank rk -> 1 <= q <= 11 - sc -> t2v = q + sc -> a7v = q ->
    (forall m2 (rk' : list Z) (t2v' a7v' : Z) (ya1 ya2 y28 y29 : word), 1 < q ->
       XH (hwk nbs) rk' m2 -> shifted (q - 1 + sc) sc rank rk' -> t2v' = q - 1 + sc -> a7v' = q - 1 ->
       evtF bsegs RNG POST (STR 0x97a3c m2 dtd nbs (Z_to_bv 64 sc) (Z_to_bv 64 NW) (Z_to_bv 64 t2v') ya1 ya2 (Z_to_bv 64 a7v') y28 y29)) ->
    (forall m2 (rk' : list Z) (y7 ya1 ya2 ya7 y28 y29 : word), q = 1 ->
       XH (hwk nbs) rk' m2 -> shifted sc sc rank rk' ->
       evtF bsegs RNG POST (STR 0x97ae0 m2 dtd nbs (Z_to_bv 64 sc) (Z_to_bv 64 NW) y7 ya1 ya2 ya7 y28 y29)) ->
    evtF bsegs RNG POST (STR 0x97a3c m1 dtd nbs (Z_to_bv 64 sc) (Z_to_bv 64 NW) (Z_to_bv 64 t2v) xa1 xa2 (Z_to_bv 64 a7v) x28 x29).
  Proof.
    intros until x29; intros I SH HQ E2 E7 KH KE. subst t2v a7v. open_xh I. x1_open.
    pose proof SH as (LRK2 & _). unfold FseNCount.Zlength in LRK2.
    destruct (shifted_step (q + sc) sc rank rk SH ltac:(lia) ltac:(lia)) as [ERD SH'].
    replace (q + sc - sc) with q in ERD, SH' by lia.
    remember (Znth q rank) as v eqn:EV.
    pose proof (rank_small q ltac:(lia)) as VB. rewrite <- EV in VB.
    assert (LHK : zlen (map (Z_to_bv 8) (hwk nbs)) = 256) by (rewrite length_map; apply hwk_len).
    assert (LRKB : zlen (map (Z_to_bv 8) (u32b rk)) = 52) by (rewrite length_map, u32b_length2, LRK2; reflexivity).
    assert (LDT : zlen (map (Z_to_bv 8) dt) = 16388) by (rewrite length_map; exact DTLEN).
    kx_autoFLAc tt [KAUnp WK 1492; KAApp WK 1492] [0x97a3c; 0x97ae0; 0x97b24; 0x98ed8] 60%nat
      (KZB2 ++ [KZRange q 1 10; KZRange (q + sc) 2 11; KZRange v 0 256; KZWord (WK + 4 * q) 4%nat v; KZWr WK 52])
      [(SPA, 216)] [(WK, 1492); (SPA, 216)].
    1: split; [lia| split; [lia| split; [lia| rewrite <- ERD; apply (rdn_u32b bsegs m1 WK rk q RK); [lia| rewrite ERD; lia]]]].
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x98ed8) _ _ _ _) => kx_trap_fast | _ => idtac end.
    all: kxk_keepg RK. all: kx_mem. all: kx_tidy_run.
    all: repeat match goal with E : hidden (?v = _) |- _ => unfold hidden in E; subst v end.
    all: clear KXUL.
    all: match type of RK with context [Zupd ?i3 _ (Zupd ?i2 _ (Zupd ?i1 _ (Zupd ?i0 _ _)))] =>
           replace i3 with (4 * (q + sc) + 3) in RK by lia; replace i2 with (4 * (q + sc) + 2) in RK by lia;
           replace i1 with (4 * (q + sc) + 1) in RK by lia; replace i0 with (4 * (q + sc)) in RK by lia end.
    all: rewrite (u32b_upd4 rk (q + sc) v) in RK by lia.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x97a3c) _ _ _ _) =>
             replace (q + sc - 1) with (q - 1 + sc) in SH' by lia; eapply KH; [clear - KXBR HQ; lia| close_xh| exact SH'| clear - HQ; lia| clear - HQ; lia]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x97ae0) _ _ _ _) =>
             assert (EQ1 : q = 1) by (clear - KXBR HQ; lia); subst q; replace (1 + sc - 1) with sc in SH' by lia; eapply KE; [reflexivity| close_xh| exact SH']
         end.
  Qed.
  (* [comment removed for export] *)
  Lemma x1_s_loopA : forall (f : nat) m1 (rk : list Z) (q t2v a7v : Z) xa1 xa2 x28 x29,
    XH (hwk nbs) rk m1 -> shifted (q + sc) sc rank rk -> 1 <= q <= 11 - sc -> q = 1 + Z.of_nat f -> t2v = q + sc -> a7v = q ->
    (forall m2 (rk' : list Z) (y7 ya1 ya2 ya7 y28 y29 : word),
       XH (hwk nbs) rk' m2 -> shifted sc sc rank rk' ->
       evtF bsegs RNG POST (STR 0x97ae0 m2 dtd nbs (Z_to_bv 64 sc) (Z_to_bv 64 NW) y7 ya1 ya2 ya7 y28 y29)) ->
    evtF bsegs RNG POST (STR 0x97a3c m1 dtd nbs (Z_to_bv 64 sc) (Z_to_bv 64 NW) (Z_to_bv 64 t2v) xa1 xa2 (Z_to_bv 64 a7v) x28 x29).
  Proof.
    induction f as [|f IH]; intros until x29; intros I SH HQ HF E2 E7 KE.
    - eapply (x1_s_bodyA m1 rk q); [exact I| exact SH| exact HQ| exact E2| exact E7| intros; exfalso; lia|].
      intros m2 rk' y7 ya1 ya2 ya7 y28 y29 _ I2 SH2. eapply KE; [exact I2| exact SH2].
    - eapply (x1_s_bodyA m1 rk q); [exact I| exact SH| exact HQ| exact E2| exact E7| | intros; exfalso; lia].
      intros m2 rk' t2v' a7v' ya1 ya2 y28 y29 Hq I2 SH2 E2' E7'.
      eapply (IH m2 rk' (q - 1)); [exact I2| exact SH2| lia| lia| exact E2'| exact E7'| exact KE].
  Qed.

  (* [comment removed for export] *)
  Lemma x1_z_bodyA : forall m1 (rk0 rk : list Z) (z : Z) x7 xa1 xa2 xa7 x28 x29,
    XH (hwk nbs) rk m1 -> zeroed z sc rk0 rk -> 1 <= z <= sc ->
    (forall m2 (rk' : list Z) (ya1 ya2 ya7 y28 y29 : word), 1 <= z - 1 ->
       XH (hwk nbs) rk' m2 -> zeroed (z - 1) sc rk0 rk' ->
       evtF bsegs RNG POST (STR 0x97ae0 m2 dtd nbs (Z_to_bv 64 (z - 1)) (Z_to_bv 64 NW) x7 ya1 ya2 ya7 y28 y29)) ->
    (forall m2 (rk' : list Z) (ya1 ya2 y28 y29 : word), z - 1 = 0 ->
       XH (hwk nbs) rk' m2 -> zeroed 0 sc rk0 rk' ->
       evtF bsegs RNG POST (STR 0x97b1c m2 dtd nbs (Z_to_bv 64 0) (Z_to_bv 64 NW) x7 ya1 ya2 (Z_to_bv 64 11) y28 y29)) ->
    evtF bsegs RNG POST (STR 0x97ae0 m1 dtd nbs (Z_to_bv 64 z) (Z_to_bv 64 NW) x7 xa1 xa2 xa7 x28 x29).
  Proof.
    intros until x29; intros I ZE HZ KH KE. open_xh I. x1_open.
    pose proof ZE as (LRK2 & _).
    assert (LHK : zlen (map (Z_to_bv 8) (hwk nbs)) = 256) by (rewrite length_map; apply hwk_len).
    assert (LRKB : zlen (map (Z_to_bv 8) (u32b rk)) = 52) by (rewrite length_map, u32b_length2, LRK2; reflexivity).
    assert (LDT : zlen (map (Z_to_bv 8) dt) = 16388) by (rewrite length_map; exact DTLEN).
    kx_autoFLAc tt [KAUnp WK 1492; KAApp WK 1492] [0x97ae0; 0x97b1c; 0x97b24; 0x98ed8] 60%nat
      (KZB2 ++ [KZRange z 1 10; KZWr WK 52])
      [(SPA, 216)] [(WK, 1492); (SPA, 216)].
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x98ed8) _ _ _ _) => kx_trap_fast | _ => idtac end.
    all: kxk_keepg RK. all: kx_mem. all: kx_tidy_run.
    all: repeat match goal with E : hidden (?v = _) |- _ => unfold hidden in E; subst v end.
    all: clear KXUL.
    all: match type of RK with context [Zupd ?i3 _ (Zupd ?i2 _ (Zupd ?i1 _ (Zupd ?i0 _ _)))] =>
           replace i3 with (4 * z + 3) in RK by lia; replace i2 with (4 * z + 2) in RK by lia; replace i1 with (4 * z + 1) in RK by lia; replace i0 with (4 * z) in RK by lia end.
    all: match type of RK with context [Zupd _ ?v3 (Zupd _ ?v2 (Zupd _ ?v1 (Zupd _ ?v0 _)))] =>
           change v3 with ((0 / 16777216) mod 256) in RK; change v2 with ((0 / 65536) mod 256) in RK; change v1 with ((0 / 256) mod 256) in RK; change v0 with (0 mod 256) in RK end.
    all: rewrite (u32b_upd4 rk z 0) in RK by lia.
    all: pose proof (zeroed_step z sc rk0 rk ZE ltac:(lia) ltac:(lia)) as ZE'.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x97ae0) _ _ _ _) => setreg_m 5 (z - 1); eapply KH; [clear - KXBR HZ; lia| close_xh| exact ZE']
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x97b1c) _ _ _ _) =>
             assert (EZ : z - 1 = 0) by (clear - KXBR HZ; lia); rewrite EZ in ZE'; setreg_m 5 0; eapply KE; [exact EZ| close_xh| exact ZE']
         end.
  Qed.
  (* [comment removed for export] *)
  Lemma x1_z_loopA : forall (f : nat) m1 (rk0 rk : list Z) (z : Z) x7 xa1 xa2 xa7 x28 x29,
    XH (hwk nbs) rk m1 -> zeroed z sc rk0 rk -> 1 <= z <= sc -> z = 1 + Z.of_nat f ->
    (forall m2 (rk' : list Z) (ya1 ya2 y28 y29 : word),
       XH (hwk nbs) rk' m2 -> zeroed 0 sc rk0 rk' ->
       evtF bsegs RNG POST (STR 0x97b1c m2 dtd nbs (Z_to_bv 64 0) (Z_to_bv 64 NW) x7 ya1 ya2 (Z_to_bv 64 11) y28 y29)) ->
    evtF bsegs RNG POST (STR 0x97ae0 m1 dtd nbs (Z_to_bv 64 z) (Z_to_bv 64 NW) x7 xa1 xa2 xa7 x28 x29).
  Proof.
    induction f as [|f IH]; intros until x29; intros I ZE HZ HF KE.
    - eapply (x1_z_bodyA m1 rk0 rk z); [exact I| exact ZE| exact HZ| intros; exfalso; lia|].
      intros m2 rk' ya1 ya2 y28 y29 _ I2 ZE2. eapply KE; [exact I2| exact ZE2].
    - eapply (x1_z_bodyA m1 rk0 rk z); [exact I| exact ZE| exact HZ| | intros; exfalso; lia].
      intros m2 rk' ya1 ya2 ya7 y28 y29 Hz I2 ZE2.
      eapply (IH m2 rk0 rk' (z - 1)); [exact I2| exact ZE2| lia| lia| exact KE].
  Qed.
  End RESC.

  (* [comment removed for export] *)
  Lemma x1_h2A : forall m1 (hw rank dt : list Z) (nbs tl : Z) (fl : Z) (jA jC jD jB jE j3 j5 j6 : list byte)
      (x5 x6 x7 x28 x29 : word) (dtd : Z),
    huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl -> 1 <= tl <= 10 -> 2 <= nbs <= 256 -> zlen hw = 256 -> Forall isbyte hw -> zlen rank = 13 ->
    mem_inv bsegs m1 -> munch [(DT, DT + 16388); (WK, WK + wksz); (SPV - 5440, SPA + 216); (FF + 32, FF + 36)] m5 m1 -> wmono bsegs m5 m1 -> stk bsegs m1 lo SPA ->
    rw_cells bsegs m1 SPA (FRA0 jA jC jD jB jE) -> rw_cells bsegs m1 FF (X1FFHDR fl j3 j5 j6 (Z_to_bv 64 tl) (Z_to_bv 64 nbs)) ->
    u8arr bsegs m1 DT (map (Z_to_bv 8) dt) -> zlen dt = 16388 ->
    u8arr bsegs m1 (WK + 1236) (map (Z_to_bv 8) hw) -> u8arr bsegs m1 WK (map (Z_to_bv 8) (u32b rank)) ->
    stk bsegs m1 (WK + 52) (WK + 1236) -> stk bsegs m1 (WK + 1492) (WK + wksz) ->
    (forall m2 (hw' rank' : list Z) (y5 y6 y7 ya1 ya2 y28 y29 : word),
       huf_stats_ok (firstn (Z.to_nat nbs) hw') rank' 11 -> zlen hw' = 256 -> Forall isbyte hw' -> zlen rank' = 13 ->
       mem_inv bsegs m2 -> munch [(DT, DT + 16388); (WK, WK + wksz); (SPV - 5440, SPA + 216); (FF + 32, FF + 36)] m5 m2 -> wmono bsegs m5 m2 -> stk bsegs m2 lo SPA ->
       rw_cells bsegs m2 SPA (FRA0 jA jC jD jB jE) -> rw_cells bsegs m2 FF (X1FFHDR fl j3 j5 j6 (Z_to_bv 64 tl) (Z_to_bv 64 nbs)) ->
       u8arr bsegs m2 DT (map (Z_to_bv 8) dt) ->
       u8arr bsegs m2 (WK + 1236) (map (Z_to_bv 8) hw') -> u8arr bsegs m2 WK (map (Z_to_bv 8) (u32b rank')) ->
       stk bsegs m2 (WK + 52) (WK + 1236) -> stk bsegs m2 (WK + 1492) (WK + wksz) ->
       evtF bsegs RNG POST (STR 0x97b1c m2 dtd nbs y5 y6 y7 ya1 ya2 (Z_to_bv 64 11) y28 y29)) ->
    evtF bsegs RNG POST (STR 0x979c8 m1 dtd nbs x5 x6 x7 (Z_to_bv 64 12) (Z_to_bv 64 nbs) (Z_to_bv 64 tl) x28 x29).
  Proof.
    intros until dtd; intros STATS TLR NBSR LHW BHW LRK MI MU WM STK FR FFC DTC DTLEN HWC RK WS1 WKR KK.
    x1_open.
    (* [comment removed for export] *)
    zstep. rewrite (swrap32_small (11 - tl)) by lia.
    assert (LHK : zlen (map (Z_to_bv 8) hw) = 256) by (rewrite length_map; exact LHW).
    assert (LRKB : zlen (map (Z_to_bv 8) (u32b rank)) = 52) by (rewrite length_map, u32b_length2, LRK; reflexivity).
    assert (LDT : zlen (map (Z_to_bv 8) dt) = 16388) by (rewrite length_map; exact DTLEN).
    (* [comment removed for export] *)
    unfold X1FFHDR in FFC.
    kx_autoFLAc tt [KAUnp WK 1492; KAApp WK 1492] [0x979d8; 0x97a30; 0x97b24; 0x98ed8] 40%nat
      (KZB ++ [KZRange tl 1 10; KZRange nbs 2 256]) [(SPA, 216)] [(WK, 1492); (SPA, 216)].
    all: kx_tidy_run.
    clear KXMI.
    setreg_m 7 (18446744073709551615 - (WK + 1236)).
    eapply (x1_w_loopA hw rank dt nbs tl dtd (11 - tl) fl jA jC jD jB jE j3 j5 j6 STATS TLR NBSR LHW eq_refl DTLEN (Z.to_nat (nbs - 1)) m1 rank 0);
      [ unfold XH, X1FFHDR; cbn [Z.to_nat firstn skipn map app]; repeat (split; [eassumption|]); eassumption
      | exact LRK| clear; lia| clear - NBSR; lia|].
    intros m2 ya1 y28 y29 I2.
    pose proof STATS as (_ & _ & _ & RKL0 & _).
    eapply (x1_s_loopA hw rank dt nbs tl dtd (11 - tl) fl jA jC jD jB jE j3 j5 j6 STATS TLR NBSR LHW eq_refl DTLEN (Z.to_nat (tl - 1)) m2 rank tl 11 tl);
      [ exact I2| replace (tl + (11 - tl)) with 11 by lia; apply shifted_init; exact RKL0| clear - TLR; lia| clear - TLR; lia| clear - TLR; lia| reflexivity|].
    intros m3 rk' z7 za1 za2 za7 z28 z29 I3 SH3.
    assert (CL3 : zlen rk' = 13) by (destruct SH3 as (L & _); exact L).
    eapply (x1_z_loopA hw rank dt nbs tl dtd (11 - tl) fl jA jC jD jB jE j3 j5 j6 TLR NBSR LHW eq_refl DTLEN (Z.to_nat (11 - tl - 1)) m3 rk' rk' (11 - tl));
      [ exact I3| apply zeroed_init; exact CL3| clear - TLR; lia| clear - TLR; lia|].
    intros m4 rk'' wa1 wa2 w28 w29 I4 ZE4.
    destruct I4 as (DTC4 & HWC4 & RK4 & WS14 & WKR4 & STK4 & MI4 & MU4 & WM4 & FR4 & FFC4).
    pose proof STATS as (T1 & T2 & T3 & T4 & T5 & T6).
    assert (HI : forall v, tl < v <= 12 -> Znth v rank = 0).
    { intros v Hv. rewrite (T5 v) by lia. unfold hcount. rewrite (proj1 (count_occ_not_In Z.eq_dec (firstn (Z.to_nat nbs) hw) v)); [reflexivity|].
      intros IN. pose proof (proj1 (Forall_forall _ _) T3 v IN) as HX. cbv beta in HX. lia. }
    pose proof (zeroed_resc (11 - tl) rank rk' rk'' tl SH3 ZE4 ltac:(clear - TLR; lia) ltac:(clear; lia) ltac:(clear - TLR; lia) HI) as RR4.
    assert (EFH : firstn (Z.to_nat nbs) (map (resc (11 - tl)) (firstn (Z.to_nat nbs) hw) ++ skipn (Z.to_nat nbs) hw) = map (resc (11 - tl)) (firstn (Z.to_nat nbs) hw)).
    { assert (LL : length (map (resc (11 - tl)) (firstn (Z.to_nat nbs) hw)) = Z.to_nat nbs) by (rewrite length_map, length_firstn; lia).
      rewrite firstn_app, LL, Nat.sub_diag, firstn_O, app_nil_r. rewrite <- LL at 1. apply firstn_all. }
    eapply KK; [| | | | exact MI4| exact MU4| exact WM4| exact STK4| exact FR4| exact FFC4| exact DTC4| exact HWC4| exact RK4| exact WS14| exact WKR4].
    - rewrite EFH. replace 11 with (tl + (11 - tl)) at 2 by lia. apply (huf_stats_rescale _ rank rk'' tl (11 - tl) STATS ltac:(lia) ltac:(lia) RR4).
    - apply (hwk_len hw (11 - tl) LHW).
    - apply (hwk_bytes hw rank dt nbs tl (11 - tl) STATS TLR NBSR BHW eq_refl nbs); lia.
    - destruct RR4 as [RL _]. exact RL.
  Qed.
End X1B.
End CANSEC1.
