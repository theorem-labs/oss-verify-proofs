(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit Gm_ropkit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation ROP_W datad ld := [(datad, datad + 4 * ld)]%Z (only parsing).

(* [comment removed for export] *)
Definition rop_words_exit (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a7 s2 s3 s4 s5 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (datad datas ld ls nfw : Z) (wsd wss : list word) : machine_state -> Prop :=
  fun ms' => exists (a0' s6' s7' s8' : word) (m' : mem) (wsd' : list word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (Z_to_bv 64 (4 * nfw)) a2 a3 a4 (Z_to_bv 64 SHB) (Z_to_bv 64 0) a7
                  s2 s3 s4 s5 s6' s7' s8' s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xa27c8) fc None m' (seg_rom asegs)
    /\ munch (ROP_W datad ld) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' datad wsd' /\ Z.of_nat (length wsd') = ld /\ u32arr asegs m' datas wss
    /\ acc asegs m' datad (4 * ld) /\ acc asegs m' datas (4 * ls).

Lemma rop_words : forall (k : nat) (j : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a7 s2 s3 s6 s7 s8 s9 s10 s11 t3 t6 : word) F fc (m : mem)
    (datad datas ld ls rbd rbs nfw : Z) (wsd wss : list word),
  Z.of_nat k = nfw - j -> 0 <= j -> (1 <= k)%nat -> nfw <= 2^20 ->
  0 <= rbd -> rbd + nfw <= ld -> 0 <= rbs -> rbs + nfw <= ls -> ld <= 2^24 -> ls <= 2^24 ->
  0 < datad -> datad mod 8 = 0 -> datad + 4 * ld <= 2^47 -> (datad + 4 * ld <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
  (datad + 4 * ld <= 0x10000 \/ SEGTOP_A <= datad) ->
  0 < datas -> datas mod 8 = 0 -> datas + 4 * ls <= 2^47 -> (datas + 4 * ls <= 0x7fff7000 \/ 0x10007fff8000 <= datas) ->
  (datad + 4 * ld <= datas \/ datas + 4 * ls <= datad) ->
  u32arr asegs m datad wsd -> Z.of_nat (length wsd) = ld -> u32arr asegs m datas wss -> Z.of_nat (length wss) = ls ->
  acc asegs m datad (4 * ld) -> acc asegs m datas (4 * ls) -> mem_inv asegs m ->
  evt asegs (rop_words_exit ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a7 s2 s3 (Z_to_bv 64 (datas + 4 * rbs)) (Z_to_bv 64 (datad + 4 * rbd))
                            s9 s10 s11 t3 (Z_to_bv 64 (datas + 4 * rbs)) (Z_to_bv 64 (datad + 4 * rbd)) t6 F fc m datad datas ld ls nfw wsd wss)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (4 * j)) a2 a3 a4 (Z_to_bv 64 SHB) (Z_to_bv 64 (j - nfw)) a7
             s2 s3 (Z_to_bv 64 (datas + 4 * rbs)) (Z_to_bv 64 (datad + 4 * rbd)) s6 s7 s8 s9 s10 s11 t3
             (Z_to_bv 64 (datas + 4 * rbs)) (Z_to_bv 64 (datad + 4 * rbd)) t6)
        F (Z_to_bv 64 0xa2760) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a7 s2 s3 s6 s7 s8 s9 s10 s11 t3 t6 F fc m
    datad datas ld ls rbd rbs nfw wsd wss HK HJ HK1 NFW RBD RBDN RBS RBSN LD LS D0 D8 DHI DSH DSEG S0 S8 SHI SSH DSAP UAD UADL UAS UASL ACCD ACCS MI.
  { lia. }
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (ROP_W datad ld) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lwalk [0xa2788].
  destruct (u32arr_nth wss (rbs + j) ltac:(lia)) as (wv & NTH).
  pose proof (u32arr_read asegs m datas wss (rbs + j) wv (wa (datas + 4 * rbs + 4 * j)) UAS NTH ltac:(lia) ltac:(f_equal; lia)) as R.
  lstep. clear R NTH.
  lwalk [0xa2798].
  rewrite (swrap32_modadd (j - nfw) 1) by lia.
  arr_sw datad (rbd + j) (datad + 4 * rbd + 4 * j).
  lwalk [0xa2760; 0xa27c8].
  destruct k as [|k].
  - replace (j - nfw + 1) with 0 by lia. brF. lwalk [0xa27c8].
    apply evt_done. unfold rop_words_exit. do 4 eexists. exists m0, aws. split; [replace (4 * nfw) with (4 * j + 4) by lia; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact UAD|]. split; [exact UADL|]. split; [exact UAS|]. split; assumption.
  - brT.
    replace (4 * j + 4) with (4 * (j + 1)) by lia. replace (j - nfw + 1) with (j + 1 - nfw) by lia.
    eapply evt_cut.
    + eapply (IH (j + 1)) with (wsd := aws) (wss := wss) (rbd := rbd) (rbs := rbs) (ld := ld) (ls := ls); try eassumption; try lia.
    + intros ms' PO. apply evt_done. unfold rop_words_exit in PO |- *.
      destruct PO as (a0' & s6' & s7' & s8' & m' & wsd' & E & MU' & WM' & R).
      exists a0', s6', s7', s8', m', wsd'.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact R].
Qed.

(* [comment removed for export] *)
Definition rop_exit (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (datad datas ld : Z) (wss : list word)
    : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' : word)
                    (m' : mem) (wsd' : list word),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
             F (Z_to_bv 64 0xa4c70) fc None m' (seg_rom asegs)
    /\ munch (ROP_W datad ld) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' datad wsd' /\ Z.of_nat (length wsd') = ld /\ u32arr asegs m' datas wss.

Lemma rop_rows : forall (k : nat) (i : Z)
    (sp gp tp a0 a1 a6 s6 s7 s8 s9 s10 s11 u nu : word) F fc (m : mem)
    (datad datas ld ls dwpl swpl doff soff dh dwb nfw lw : Z) (wsd wss : list word),
  Z.of_nat k = dh - i -> 0 <= i -> (1 <= k)%nat -> 0 < dh <= 20000 ->
  0 < dwb <= 2^25 -> nfw = dwb / 32 -> lw = dwb mod 32 -> 0 < dwpl <= 5001 -> 0 < swpl <= 5001 ->
  0 <= doff -> (lw = 0 -> doff + (dh - 1) * dwpl + nfw <= ld) -> (lw <> 0 -> doff + (dh - 1) * dwpl + nfw + 1 <= ld) ->
  0 <= soff -> (lw = 0 -> soff + (dh - 1) * swpl + nfw <= ls) -> (lw <> 0 -> soff + (dh - 1) * swpl + nfw + 1 <= ls) ->
  ld <= 2^24 -> ls <= 2^24 ->
  0 < datad -> datad mod 8 = 0 -> datad + 4 * ld <= 2^47 -> (datad + 4 * ld <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
  (datad + 4 * ld <= 0x10000 \/ SEGTOP_A <= datad) ->
  0 < datas -> datas mod 8 = 0 -> datas + 4 * ls <= 2^47 -> (datas + 4 * ls <= 0x7fff7000 \/ 0x10007fff8000 <= datas) ->
  (datad + 4 * ld <= datas \/ datas + 4 * ls <= datad) ->
  u32arr asegs m datad wsd -> Z.of_nat (length wsd) = ld -> u32arr asegs m datas wss -> Z.of_nat (length wss) = ls ->
  acc asegs m datad (4 * ld) -> acc asegs m datas (4 * ls) -> mem_inv asegs m ->
  evt asegs (rop_exit sp gp tp F fc m datad datas ld wss)
    (MS (mkR (Z_to_bv 64 dh) sp gp tp (Z_to_bv 64 lw) (Z_to_bv 64 (datad + 4 * doff)) u (Z_to_bv 64 (0 - nfw)) (Z_to_bv 64 (dwpl * 4))
             a0 a1 (Z_to_bv 64 (datas + 4 * soff)) (Z_to_bv 64 i) (Z_to_bv 64 dwpl) (Z_to_bv 64 SHB) a6 (Z_to_bv 64 swpl)
             (Z_to_bv 64 (swpl * 4)) (Z_to_bv 64 32) (Z_to_bv 64 (datas + 4 * (soff + i * swpl))) (Z_to_bv 64 (datad + 4 * (doff + i * dwpl)))
             s6 s7 s8 s9 s10 s11 (Z_to_bv 64 dwb) (Z_to_bv 64 (datas + 4 * (soff + i * swpl))) (Z_to_bv 64 (datad + 4 * (doff + i * dwpl))) nu)
        F (Z_to_bv 64 0xa2734) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i sp gp tp a0 a1 a6 s6 s7 s8 s9 s10 s11 u nu F fc m
    datad datas ld ls dwpl swpl doff soff dh dwb nfw lw wsd wss
    HK HI HK1 DH DWB NFW LW DWPL SWPL DOFF DB0 DB1 SOFF SB0 SB1 LD LS D0 D8 DHI DSH DSEG S0 S8 SHI SSH DSAP UAD UADL UAS UASL ACCD ACCS MI.
  { lia. }
  assert (NFWR : 0 <= nfw < 2^26) by (subst nfw; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (LWR : 0 <= lw < 32) by (subst lw; apply Z.mod_pos_bound; lia).
  assert (PD : 0 <= i * dwpl /\ i * dwpl <= (dh - 1) * dwpl) by (clear - HK HI DWPL; nia).
  assert (PS : 0 <= i * swpl /\ i * swpl <= (dh - 1) * swpl) by (clear - HK HI SWPL; nia).
  assert (PD1 : (dh - 1) * dwpl <= 100020000) by (clear - DH DWPL; nia).
  assert (PS1 : (dh - 1) * swpl <= 100020000) by (clear - DH SWPL; nia).
  unfold SEGTOP_A, SHB in *.
  (* [comment removed for export] *)
  assert (ROWEND : forall (a0' a1' a6' s6' s7' s8' : word) (m1 : mem) (wsd1 : list word),
    munch (ROP_W datad ld) m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
    u32arr asegs m1 datad wsd1 -> Z.of_nat (length wsd1) = ld -> u32arr asegs m1 datas wss ->
    acc asegs m1 datad (4 * ld) -> acc asegs m1 datas (4 * ls) ->
    evt asegs (rop_exit sp gp tp F fc m datad datas ld wss)
      (MS (mkR (Z_to_bv 64 dh) sp gp tp (Z_to_bv 64 lw) (Z_to_bv 64 (datad + 4 * doff)) u (Z_to_bv 64 (0 - nfw)) (Z_to_bv 64 (dwpl * 4))
               a0' a1' (Z_to_bv 64 (datas + 4 * soff)) (Z_to_bv 64 i) (Z_to_bv 64 dwpl) (Z_to_bv 64 2147450880) a6' (Z_to_bv 64 swpl)
               (Z_to_bv 64 (swpl * 4)) (Z_to_bv 64 32) (Z_to_bv 64 (datas + 4 * (soff + i * swpl))) (Z_to_bv 64 (datad + 4 * (doff + i * dwpl)))
               s6' s7' s8' s9 s10 s11 (Z_to_bv 64 dwb) (Z_to_bv 64 (datas + 4 * (soff + i * swpl))) (Z_to_bv 64 (datad + 4 * (doff + i * dwpl))) nu)
          F (Z_to_bv 64 0xa2718) fc None m1 (seg_rom asegs))).
  { intros a0' a1' a6' s6' s7' s8' m1 wsd1 MU1 WM1 MI1 UAD1 UADL1 UAS1 ACCD1 ACCS1.
    lwalk [0xa2734; 0xa4c70].

    replace (datad + 4 * (doff + i * dwpl) + dwpl * 4) with (datad + 4 * (doff + (i + 1) * dwpl)) by lia.
    replace (datas + 4 * (soff + i * swpl) + swpl * 4) with (datas + 4 * (soff + (i + 1) * swpl)) by lia.
    destruct k as [|k].
    - assert (EI : i + 1 = dh) by lia. rewrite EI in *.
      brF. lwalk [0xa4c70].
      apply evt_done. unfold rop_exit. do 28 eexists. exists m1, wsd1. split; [reflexivity|].
      split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact UAD1|]. split; [exact UADL1| exact UAS1].
    - brT.
      eapply evt_cut.
      + eapply (IH (i + 1)) with (wsd := wsd1) (ld := ld) (ls := ls) (doff := doff) (soff := soff) (nfw := nfw) (lw := lw) (dwb := dwb);
          try eassumption; try lia.
      + intros ms' PO. apply evt_done. unfold rop_exit in PO |- *.
        destruct PO as (ra' & t0' & t1' & t2' & s0' & s1' & a0'' & a1'' & a2' & a3' & a4' & a5' & a6'' & a7' & s2' & s3' & s4' & s5' & s6'' & s7'' & s8''
                        & s9' & s10' & s11' & t3' & t4' & t5' & t6' & m' & wsd' & E & MU' & WM' & R).
        exists ra', t0', t1', t2', s0', s1', a0'', a1'', a2', a3', a4', a5', a6'', a7', s2', s3', s4', s5', s6'', s7'', s8'', s9', s10', s11', t3', t4', t5', t6', m', wsd'.
        split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU1 MU')|]. split; [exact (wmono_trans asegs _ _ _ WM1 WM')| exact R]. }

  (* [comment removed for export] *)
  assert (PARTIAL : forall (a6' s6' s7' s8' : word) (m1 : mem) (wsd1 : list word),
    lw <> 0 ->
    munch (ROP_W datad ld) m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
    u32arr asegs m1 datad wsd1 -> Z.of_nat (length wsd1) = ld -> u32arr asegs m1 datas wss ->
    acc asegs m1 datad (4 * ld) -> acc asegs m1 datas (4 * ls) ->
    evt asegs (rop_exit sp gp tp F fc m datad datas ld wss)
      (MS (mkR (Z_to_bv 64 dh) sp gp tp (Z_to_bv 64 lw) (Z_to_bv 64 (datad + 4 * doff)) u (Z_to_bv 64 (0 - nfw)) (Z_to_bv 64 (dwpl * 4))
               (Z_to_bv 64 (datad + 4 * (doff + i * dwpl + nfw))) (Z_to_bv 64 (datas + 4 * (soff + i * swpl + nfw)))
               (Z_to_bv 64 (datas + 4 * soff)) (Z_to_bv 64 i) (Z_to_bv 64 dwpl) (Z_to_bv 64 2147450880) a6' (Z_to_bv 64 swpl)
               (Z_to_bv 64 (swpl * 4)) (Z_to_bv 64 32) (Z_to_bv 64 (datas + 4 * (soff + i * swpl))) (Z_to_bv 64 (datad + 4 * (doff + i * dwpl)))
               s6' s7' s8' s9 s10 s11 (Z_to_bv 64 dwb) (Z_to_bv 64 (datas + 4 * (soff + i * swpl))) (Z_to_bv 64 (datad + 4 * (doff + i * dwpl))) nu)
          F (Z_to_bv 64 0xa27d4) fc None m1 (seg_rom asegs))).
  { intros a6' s6' s7' s8' m1 wsd1 LWN MU1 WM1 MI1 UAD1 UADL1 UAS1 ACCD1 ACCS1.
    specialize (DB1 LWN). specialize (SB1 LWN).
    lwalk [0xa27f0].

    destruct (u32arr_nth wsd1 (doff + i * dwpl + nfw) ltac:(lia)) as (wd & NTHD).
    pose proof (u32arr_read asegs m1 datad wsd1 (doff + i * dwpl + nfw) wd _ UAD1 NTHD ltac:(lia) eq_refl) as RD.
    lstep. clear RD NTHD.
    lwalk [0xa2704].

    destruct (u32arr_nth wss (soff + i * swpl + nfw) ltac:(lia)) as (wv & NTHS).
    pose proof (u32arr_read asegs m1 datas wss (soff + i * swpl + nfw) wv _ UAS1 NTHS ltac:(lia) eq_refl) as RS.
    lstep. clear RS NTHS.
    lwalk [0xa2714].
    arr_sw datad (doff + i * dwpl + nfw) (datad + 4 * (doff + i * dwpl + nfw)).
    lwalk [0xa2718].
    eapply ROWEND; try eassumption. }

  pose proof (munch_refl (ROP_W datad ld) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lstep.
  destruct (Z.ltb_spec dwb 32) as [WLT|WGE].
  - (* [comment removed for export] *)
    brF.
    assert (NF0 : nfw = 0) by (subst nfw; apply Z.div_small; lia).
    assert (LWN : lw <> 0) by (subst lw; rewrite Z.mod_small by lia; lia).
    lwalk [0xa2750].

    lstep. brT.
    replace (datad + 4 * doff + i * dwpl * 4) with (datad + 4 * (doff + i * dwpl + nfw)) by lia.
    replace (datas + 4 * soff + i * swpl * 4) with (datas + 4 * (soff + i * swpl + nfw)) by lia.
    eapply PARTIAL; try eassumption.
  - (* [comment removed for export] *)
    brT. lwalk [0xa2760].

    assert (NF1 : 1 <= nfw) by (subst nfw; apply Z.div_le_lower_bound; lia).
    change z64 with (Z_to_bv 64 (4 * 0)) at 1.
    eapply evt_cut.
    + eapply (rop_words (Z.to_nat nfw) 0) with (wsd := wsd) (wss := wss) (rbd := doff + i * dwpl) (rbs := soff + i * swpl) (ld := ld) (ls := ls);
        try eassumption; try lia.
    + intros ms' PO. unfold rop_words_exit in PO.
      destruct PO as (a0' & s6' & s7' & s8' & m' & wsd' & -> & MU' & WM' & MI' & UAD' & UADL' & UAS' & ACCD' & ACCS').
      lwalk [0xa27d0].

      lstep.
      destruct (Z.eq_dec lw 0) as [LW0|LWN].
      * rewrite LW0 in *. brT. eapply ROWEND; eassumption.
      * brF.
        replace (datad + 4 * (doff + i * dwpl) + 4 * nfw) with (datad + 4 * (doff + i * dwpl + nfw)) by lia.
        replace (datas + 4 * (soff + i * swpl) + 4 * nfw) with (datas + 4 * (soff + i * swpl + nfw)) by lia.
        eapply PARTIAL; eassumption.
Qed.

(* [comment removed for export] *)
Lemma rop_rows0 : forall (sp gp tp a0 a1 a3 a6 s6 s7 s8 s9 s10 s11 u nu : word) F fc (m : mem)
    (datad datas ld ls dwpl swpl doff soff dh dwb nfw lw T1 A2 S4 S5 T4 T5 : Z) (wsd wss : list word),
  T1 = datad + 4 * doff -> A2 = datas + 4 * soff -> S4 = A2 -> T4 = A2 -> S5 = T1 -> T5 = T1 -> a3 = Z_to_bv 64 0 ->
  0 < dh <= 20000 ->
  0 < dwb <= 2^25 -> nfw = dwb / 32 -> lw = dwb mod 32 -> 0 < dwpl <= 5001 -> 0 < swpl <= 5001 ->
  0 <= doff -> (lw = 0 -> doff + (dh - 1) * dwpl + nfw <= ld) -> (lw <> 0 -> doff + (dh - 1) * dwpl + nfw + 1 <= ld) ->
  0 <= soff -> (lw = 0 -> soff + (dh - 1) * swpl + nfw <= ls) -> (lw <> 0 -> soff + (dh - 1) * swpl + nfw + 1 <= ls) ->
  ld <= 2^24 -> ls <= 2^24 ->
  0 < datad -> datad mod 8 = 0 -> datad + 4 * ld <= 2^47 -> (datad + 4 * ld <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
  (datad + 4 * ld <= 0x10000 \/ SEGTOP_A <= datad) ->
  0 < datas -> datas mod 8 = 0 -> datas + 4 * ls <= 2^47 -> (datas + 4 * ls <= 0x7fff7000 \/ 0x10007fff8000 <= datas) ->
  (datad + 4 * ld <= datas \/ datas + 4 * ls <= datad) ->
  u32arr asegs m datad wsd -> Z.of_nat (length wsd) = ld -> u32arr asegs m datas wss -> Z.of_nat (length wss) = ls ->
  acc asegs m datad (4 * ld) -> acc asegs m datas (4 * ls) -> mem_inv asegs m ->
  evt asegs (rop_exit sp gp tp F fc m datad datas ld wss)
    (MS (mkR (Z_to_bv 64 dh) sp gp tp (Z_to_bv 64 lw) (Z_to_bv 64 T1) u (Z_to_bv 64 (0 - nfw)) (Z_to_bv 64 (dwpl * 4))
             a0 a1 (Z_to_bv 64 A2) a3 (Z_to_bv 64 dwpl) (Z_to_bv 64 SHB) a6 (Z_to_bv 64 swpl)
             (Z_to_bv 64 (swpl * 4)) (Z_to_bv 64 32) (Z_to_bv 64 S4) (Z_to_bv 64 S5)
             s6 s7 s8 s9 s10 s11 (Z_to_bv 64 dwb) (Z_to_bv 64 T4) (Z_to_bv 64 T5) nu)
        F (Z_to_bv 64 0xa2734) fc None m (seg_rom asegs)).
Proof.
  intros sp gp tp a0 a1 a3 a6 s6 s7 s8 s9 s10 s11 u nu F fc m datad datas ld ls dwpl swpl doff soff dh dwb nfw lw T1 A2 S4 S5 T4 T5 wsd wss
    -> -> -> -> -> -> -> DH. intros.
  replace (datad + 4 * doff) with (datad + 4 * (doff + 0 * dwpl)) at 2 3 by lia.
  replace (datas + 4 * soff) with (datas + 4 * (soff + 0 * swpl)) at 2 3 by lia.
  eapply (rop_rows (Z.to_nat dh) 0); try eassumption; lia.
Qed.
