(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import ImageA.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import Layout.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit Gm_ropkit LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation UNI_W datad ld := [(datad, datad + 4 * ld)]%Z (only parsing).

(* [comment removed for export] *)
Definition usw_exit (ra sp gp tp t0 t2 s1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (datad ld rb nfw : Z) : machine_state -> Prop :=
  fun ms' => exists (a1' s3' s4' s5' s6' : word) (m' : mem) (ws' : list word),
    ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 SHB) t2 (Z_to_bv 64 5) s1 (Z_to_bv 64 (datad + 4 * (rb + nfw))) a1' a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 (-1)) s3' s4' s5' s6' s7 s8 s9 s10 s11 t3 t4 (Z_to_bv 64 0) t6)
             F (Z_to_bv 64 0xa2ed0) fc None m' (seg_rom asegs)
    /\ munch (UNI_W datad ld) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' datad ws' /\ Z.of_nat (length ws') = ld /\ acc asegs m' datad (4 * ld).

Lemma usw_words : forall (k : nat) (j : Z)
    (ra sp gp tp t0 t2 s1 a0 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t6 : word) F fc (m : mem)
    (datad ld rb nfw p p2 c : Z) (ws : list word),
  p = datad + 4 * (rb + j) -> p2 = datad + 4 * (rb + j) -> c = nfw - j ->
  Z.of_nat k = nfw - j -> 0 <= j -> (1 <= k)%nat -> nfw <= 2^20 -> 0 <= rb -> rb + nfw <= ld -> ld <= 2^24 ->
  0 < datad -> datad mod 8 = 0 -> datad + 4 * ld <= 2^47 -> (datad + 4 * ld <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
  (datad + 4 * ld <= 0x10000 \/ SEGTOP_A <= datad) ->
  u32arr asegs m datad ws -> Z.of_nat (length ws) = ld -> acc asegs m datad (4 * ld) -> mem_inv asegs m ->
  evt asegs (usw_exit ra sp gp tp t0 t2 s1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t6 F fc m datad ld rb nfw)
    (MS (mkR ra sp gp tp t0 (Z_to_bv 64 SHB) t2 (Z_to_bv 64 5) s1 a0 (Z_to_bv 64 p2) a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (-1)) (Z_to_bv 64 p) (Z_to_bv 64 c) s5 s6 s7 s8 s9 s10 s11 t3 t4 (Z_to_bv 64 0) t6)
        F (Z_to_bv 64 0xa2f0c) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j ra sp gp tp t0 t2 s1 a0 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t6 F fc m
    datad ld rb nfw p p2 c ws -> -> -> HK HJ HK1 NFW RB RBN LD D0 D8 DHI DSH DSEG UAD UADL ACCD MI.
  { lia. }
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (UNI_W datad ld) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lwalk [0xa2f34].
  arr_sw datad (rb + j) (datad + 4 * (rb + j)).
  lwalk [0xa2f40].
  rewrite ?(swrap32_modadd (nfw - j) (-1)) by lia.
  rewrite ?(bv_swrap_small 32 (nfw - j + -1)) by (change (bv_half_modulus 32) with (2^31); lia).
  lstep.
  destruct k as [|k].
  - replace (nfw - j + -1) with 0 by lia. brF. lwalk [0xa2ed0].
    apply evt_done. unfold usw_exit. do 5 eexists. exists m0, aws. split; [replace (datad + 4 * (rb + nfw)) with (datad + 4 * (rb + j) + 4) by lia; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact UAD|]. split; [exact UADL| exact ACCD].
  - brT.
    eapply evt_cut.
    + eapply (IH (j + 1)) with (ws := aws) (rb := rb) (ld := ld) (nfw := nfw) (p := datad + 4 * (rb + j) + 4) (p2 := datad + 4 * (rb + j) + 4) (c := nfw - j + -1);
        try eassumption; try lia.
    + intros ms' PO. apply evt_done. unfold usw_exit in PO |- *.
      destruct PO as (x1 & x2 & x3 & x4 & x5 & m' & ws' & E & MU' & WM' & R).
      do 5 eexists. do 2 eexists.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact R].
Qed.

(* [comment removed for export] *)
Definition usr_exit (sp gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (datad ld : Z) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' : word)
                    (m' : mem) (ws' : list word),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0xa2e30) fc None m' (seg_rom asegs)
    /\ munch (UNI_W datad ld) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' datad ws' /\ Z.of_nat (length ws') = ld.

Lemma usr_rows : forall (k : nat) (i : Z)
    (ra sp gp tp a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 u : word) F fc (m : mem)
    (datad ld wpl doff dh dwb nfw lw pb pb2 : Z) (ws : list word),
  pb = datad + 4 * doff -> pb2 = datad + 4 * doff ->
  Z.of_nat k = dh - i -> 0 <= i -> (1 <= k)%nat -> 0 < dh <= 20000 ->
  0 < dwb <= 2^25 -> nfw = dwb / 32 -> lw = dwb mod 32 -> 0 < wpl <= 5001 ->
  0 <= doff -> (lw = 0 -> doff + (dh - 1) * wpl + nfw <= ld) -> (lw <> 0 -> doff + (dh - 1) * wpl + nfw + 1 <= ld) -> ld <= 2^24 ->
  0 < datad -> datad mod 8 = 0 -> datad + 4 * ld <= 2^47 -> (datad + 4 * ld <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
  (datad + 4 * ld <= 0x10000 \/ SEGTOP_A <= datad) ->
  u32arr asegs m datad ws -> Z.of_nat (length ws) = ld -> acc asegs m datad (4 * ld) -> mem_inv asegs m ->
  evt asegs (usr_exit sp gp tp s7 s8 s9 s10 s11 F fc m datad ld)
    (MS (mkR ra sp gp tp (Z_to_bv 64 lw) (Z_to_bv 64 SHB) u (Z_to_bv 64 5) (Z_to_bv 64 pb) a0 a1 (Z_to_bv 64 1) (Z_to_bv 64 dh) (Z_to_bv 64 wpl)
             (Z_to_bv 64 dwb) (Z_to_bv 64 pb2) (Z_to_bv 64 nfw)
             (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (i * wpl)) (Z_to_bv 64 i) (Z_to_bv 64 0) (Z_to_bv 64 32))
        F (Z_to_bv 64 0xa2e94) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i ra sp gp tp a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 u F fc m
    datad ld wpl doff dh dwb nfw lw pb pb2 ws -> -> HK HI HK1 DH DWB NFW LW WPLB DOFF DB0 DB1 LD D0 D8 DHI DSH DSEG UAD UADL ACCD MI.
  { lia. }
  assert (NFWR : 0 <= nfw < 2^26) by (subst nfw; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (LWR : 0 <= lw < 32) by (subst lw; apply Z.mod_pos_bound; lia).
  assert (PD : 0 <= i * wpl /\ i * wpl <= (dh - 1) * wpl) by (clear - HK HI WPLB; nia).
  assert (PD1 : (dh - 1) * wpl <= 100020000) by (clear - DH WPLB; nia).
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (UNI_W datad ld) m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  assert (ROWEND : forall (a0' a1' s3' s4' s5' s6' : word) (m1 : mem) (ws1 : list word),
    munch (UNI_W datad ld) m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
    u32arr asegs m1 datad ws1 -> Z.of_nat (length ws1) = ld -> acc asegs m1 datad (4 * ld) ->
    evt asegs (usr_exit sp gp tp s7 s8 s9 s10 s11 F fc m datad ld)
      (MS (mkR ra sp gp tp (Z_to_bv 64 lw) (Z_to_bv 64 2147450880) u (Z_to_bv 64 5) (Z_to_bv 64 (datad + 4 * doff)) a0' a1' (Z_to_bv 64 1) (Z_to_bv 64 dh) (Z_to_bv 64 wpl)
               (Z_to_bv 64 dwb) (Z_to_bv 64 (datad + 4 * doff)) (Z_to_bv 64 nfw)
               (Z_to_bv 64 (-1)) s3' s4' s5' s6' s7 s8 s9 s10 s11 (Z_to_bv 64 (i * wpl)) (Z_to_bv 64 i) (Z_to_bv 64 0) (Z_to_bv 64 32))
          F (Z_to_bv 64 0xa2e88) fc None m1 (seg_rom asegs))).
  { intros a0' a1' s3' s4' s5' s6' m1 ws1 MU1 WM1 MI1 UAD1 UADL1 ACCD1.
    lwalk [0xa2e90].
    rewrite ?(bv_swrap_small 32 (i + 1)), ?(bv_swrap_small 32 (i * wpl + wpl)) by (change (bv_half_modulus 32) with (2^31); lia).
    replace (i * wpl + wpl) with ((i + 1) * wpl) by lia.
    lstep.
    destruct k as [|k].
    - assert (EI : i + 1 = dh) by lia. rewrite EI in *.
      brT.
      apply evt_done. unfold usr_exit. do 23 eexists. exists m1, ws1. split; [reflexivity|].
      split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact UAD1| exact UADL1].
    - brF.
      eapply evt_cut.
      + eapply (IH (i + 1)) with (ws := ws1) (ld := ld) (doff := doff) (nfw := nfw) (lw := lw) (dwb := dwb) (pb := datad + 4 * doff) (pb2 := datad + 4 * doff);
          try eassumption; try lia.
      + intros ms' PO. apply evt_done. unfold usr_exit in PO |- *.
        destruct PO as (ra' & t0' & t1' & t2' & s0' & s1' & a0'' & a1'' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3'' & s4'' & s5'' & s6''
                        & t3' & t4' & t5' & t6' & m' & ws' & E & MU' & WM' & R).
        do 25 eexists.
        split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU1 MU')|]. split; [exact (wmono_trans asegs _ _ _ WM1 WM')| exact R]. }
  (* [comment removed for export] *)
  assert (PARTIAL : forall (a1' s3' s4' s5' s6' : word) (m1 : mem) (ws1 : list word),
    munch (UNI_W datad ld) m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
    u32arr asegs m1 datad ws1 -> Z.of_nat (length ws1) = ld -> acc asegs m1 datad (4 * ld) ->
    evt asegs (usr_exit sp gp tp s7 s8 s9 s10 s11 F fc m datad ld)
      (MS (mkR ra sp gp tp (Z_to_bv 64 lw) (Z_to_bv 64 2147450880) u (Z_to_bv 64 5) (Z_to_bv 64 (datad + 4 * doff))
               (Z_to_bv 64 (datad + 4 * (doff + i * wpl + nfw))) a1' (Z_to_bv 64 1) (Z_to_bv 64 dh) (Z_to_bv 64 wpl)
               (Z_to_bv 64 dwb) (Z_to_bv 64 (datad + 4 * doff)) (Z_to_bv 64 nfw)
               (Z_to_bv 64 (-1)) s3' s4' s5' s6' s7 s8 s9 s10 s11 (Z_to_bv 64 (i * wpl)) (Z_to_bv 64 i) (Z_to_bv 64 0) (Z_to_bv 64 32))
          F (Z_to_bv 64 0xa2ed0) fc None m1 (seg_rom asegs))).
  { intros a1' s3' s4' s5' s6' m1 ws1 MU1 WM1 MI1 UAD1 UADL1 ACCD1.
    lstep.
    destruct (Z.eq_dec lw 0) as [LW0|LWN].
    - rewrite LW0 in *. brT. eapply ROWEND; eassumption.
    - brF. specialize (DB1 LWN).
      lwalk [0xa2e7c].
      destruct (u32arr_nth ws1 (doff + i * wpl + nfw) ltac:(lia)) as (wd & NTHD).
      pose proof (u32arr_read asegs m1 datad ws1 (doff + i * wpl + nfw) wd _ UAD1 NTHD ltac:(lia) eq_refl) as RD.
      lstep. clear RD NTHD.
      lwalk [0xa2e84].
      arr_sw datad (doff + i * wpl + nfw) (datad + 4 * (doff + i * wpl + nfw)).
      eapply ROWEND; try eassumption. }
  lwalk [0xa2ec8].
  rewrite ?Z.add_0_r. rewrite ?(Z.mod_small (i * wpl)) by lia.
  lstep.
  destruct (Z.ltb_spec dwb 32) as [WLT|WGE].
  - (* [comment removed for export] *)
    brF.
    assert (NF0 : nfw = 0) by (subst nfw; apply Z.div_small; lia).
    lwalk [0xa2ed0].
    replace (i * wpl * 4 + (datad + 4 * doff)) with (datad + 4 * (doff + i * wpl + nfw)) by lia.
    eapply PARTIAL; try eassumption.
  - (* [comment removed for export] *)
    brT. lwalk [0xa2f0c].
    assert (NF1 : 1 <= nfw) by (subst nfw; apply Z.div_le_lower_bound; lia).
    eapply evt_cut.
    + eapply (usw_words (Z.to_nat nfw) 0) with (ws := ws) (rb := doff + i * wpl) (ld := ld) (nfw := nfw) (c := nfw); try eassumption; try lia.
    + intros ms' PO. unfold usw_exit in PO.
      destruct PO as (x1 & x2 & x3 & x4 & x5 & m' & ws' & -> & MU' & WM' & MI' & UAD' & UADL' & ACCD').
      unfold SHB in *.
      replace (datad + 4 * (doff + i * wpl + nfw)) with (datad + 4 * (doff + i * wpl + nfw)) by lia.
      eapply PARTIAL; eassumption.
Qed.

(* [comment removed for export] *)
Definition ucw_exit (ra sp gp tp t0 t2 s0 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (datad ld rb nfw : Z) : machine_state -> Prop :=
  fun ms' => exists (a1' s2' s3' s4' s5' : word) (m' : mem) (ws' : list word),
    ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 SHB) t2 s0 (Z_to_bv 64 5) (Z_to_bv 64 (datad + 4 * (rb + nfw))) a1' a2 a3 a4 a5 a6 a7
                  s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 (Z_to_bv 64 0) t6)
             F (Z_to_bv 64 0xa2fd4) fc None m' (seg_rom asegs)
    /\ munch (UNI_W datad ld) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' datad ws' /\ Z.of_nat (length ws') = ld /\ acc asegs m' datad (4 * ld).

Lemma ucw_words : forall (k : nat) (j : Z)
    (ra sp gp tp t0 t2 s0 a0 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t6 : word) F fc (m : mem)
    (datad ld rb nfw p p2 c : Z) (ws : list word),
  p = datad + 4 * (rb + j) -> p2 = datad + 4 * (rb + j) -> c = nfw - j ->
  Z.of_nat k = nfw - j -> 0 <= j -> (1 <= k)%nat -> nfw <= 2^20 -> 0 <= rb -> rb + nfw <= ld -> ld <= 2^24 ->
  0 < datad -> datad mod 8 = 0 -> datad + 4 * ld <= 2^47 -> (datad + 4 * ld <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
  (datad + 4 * ld <= 0x10000 \/ SEGTOP_A <= datad) ->
  u32arr asegs m datad ws -> Z.of_nat (length ws) = ld -> acc asegs m datad (4 * ld) -> mem_inv asegs m ->
  evt asegs (ucw_exit ra sp gp tp t0 t2 s0 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t6 F fc m datad ld rb nfw)
    (MS (mkR ra sp gp tp t0 (Z_to_bv 64 SHB) t2 s0 (Z_to_bv 64 5) a0 (Z_to_bv 64 p2) a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) (Z_to_bv 64 c) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 (Z_to_bv 64 0) t6)
        F (Z_to_bv 64 0xa3010) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j ra sp gp tp t0 t2 s0 a0 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t6 F fc m
    datad ld rb nfw p p2 c ws -> -> -> HK HJ HK1 NFW RB RBN LD D0 D8 DHI DSH DSEG UAD UADL ACCD MI.
  { lia. }
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (UNI_W datad ld) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lwalk [0xa3038].
  arr_sw datad (rb + j) (datad + 4 * (rb + j)).
  lwalk [0xa3044].
  rewrite ?(swrap32_modadd (nfw - j) (-1)) by lia.
  rewrite ?(bv_swrap_small 32 (nfw - j + -1)) by (change (bv_half_modulus 32) with (2^31); lia).
  lstep.
  destruct k as [|k].
  - replace (nfw - j + -1) with 0 by lia. brF. lwalk [0xa2fd4].
    apply evt_done. unfold ucw_exit. do 5 eexists. exists m0, aws. split; [replace (datad + 4 * (rb + nfw)) with (datad + 4 * (rb + j) + 4) by lia; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact UAD|]. split; [exact UADL| exact ACCD].
  - brT.
    eapply evt_cut.
    + eapply (IH (j + 1)) with (ws := aws) (rb := rb) (ld := ld) (nfw := nfw) (p := datad + 4 * (rb + j) + 4) (p2 := datad + 4 * (rb + j) + 4) (c := nfw - j + -1);
        try eassumption; try lia.
    + intros ms' PO. apply evt_done. unfold ucw_exit in PO |- *.
      destruct PO as (x1 & x2 & x3 & x4 & x5 & m' & ws' & E & MU' & WM' & R).
      do 5 eexists. do 2 eexists.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact R].
Qed.

(* [comment removed for export] *)
Definition ucr_exit (sp gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (datad ld : Z) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' : word)
                    (m' : mem) (ws' : list word),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0xa2e30) fc None m' (seg_rom asegs)
    /\ munch (UNI_W datad ld) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' datad ws' /\ Z.of_nat (length ws') = ld.

Lemma ucr_rows : forall (k : nat) (i : Z)
    (ra sp gp tp a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u : word) F fc (m : mem)
    (datad ld wpl doff dh dwb nfw lw pb pb2 : Z) (ws : list word),
  pb = datad + 4 * doff -> pb2 = datad + 4 * doff ->
  Z.of_nat k = dh - i -> 0 <= i -> (1 <= k)%nat -> 0 < dh <= 20000 ->
  0 < dwb <= 2^25 -> nfw = dwb / 32 -> lw = dwb mod 32 -> 0 < wpl <= 5001 ->
  0 <= doff -> (lw = 0 -> doff + (dh - 1) * wpl + nfw <= ld) -> (lw <> 0 -> doff + (dh - 1) * wpl + nfw + 1 <= ld) -> ld <= 2^24 ->
  0 < datad -> datad mod 8 = 0 -> datad + 4 * ld <= 2^47 -> (datad + 4 * ld <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
  (datad + 4 * ld <= 0x10000 \/ SEGTOP_A <= datad) ->
  u32arr asegs m datad ws -> Z.of_nat (length ws) = ld -> acc asegs m datad (4 * ld) -> mem_inv asegs m ->
  evt asegs (ucr_exit sp gp tp s7 s8 s9 s10 s11 F fc m datad ld)
    (MS (mkR ra sp gp tp (Z_to_bv 64 lw) (Z_to_bv 64 SHB) u (Z_to_bv 64 pb) (Z_to_bv 64 5) a0 a1 (Z_to_bv 64 1) (Z_to_bv 64 dh) (Z_to_bv 64 wpl)
             (Z_to_bv 64 dwb) (Z_to_bv 64 pb2) (Z_to_bv 64 nfw)
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (i * wpl)) (Z_to_bv 64 i) (Z_to_bv 64 0) (Z_to_bv 64 32))
        F (Z_to_bv 64 0xa2f98) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i ra sp gp tp a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u F fc m
    datad ld wpl doff dh dwb nfw lw pb pb2 ws -> -> HK HI HK1 DH DWB NFW LW WPLB DOFF DB0 DB1 LD D0 D8 DHI DSH DSEG UAD UADL ACCD MI.
  { lia. }
  assert (NFWR : 0 <= nfw < 2^26) by (subst nfw; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (LWR : 0 <= lw < 32) by (subst lw; apply Z.mod_pos_bound; lia).
  assert (PD : 0 <= i * wpl /\ i * wpl <= (dh - 1) * wpl) by (clear - HK HI WPLB; nia).
  assert (PD1 : (dh - 1) * wpl <= 100020000) by (clear - DH WPLB; nia).
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (UNI_W datad ld) m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  assert (ROWEND : forall (a0' a1' s2' s3' s4' s5' : word) (m1 : mem) (ws1 : list word),
    munch (UNI_W datad ld) m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
    u32arr asegs m1 datad ws1 -> Z.of_nat (length ws1) = ld -> acc asegs m1 datad (4 * ld) ->
    evt asegs (ucr_exit sp gp tp s7 s8 s9 s10 s11 F fc m datad ld)
      (MS (mkR ra sp gp tp (Z_to_bv 64 lw) (Z_to_bv 64 2147450880) u (Z_to_bv 64 (datad + 4 * doff)) (Z_to_bv 64 5) a0' a1' (Z_to_bv 64 1) (Z_to_bv 64 dh) (Z_to_bv 64 wpl)
               (Z_to_bv 64 dwb) (Z_to_bv 64 (datad + 4 * doff)) (Z_to_bv 64 nfw)
               s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (i * wpl)) (Z_to_bv 64 i) (Z_to_bv 64 0) (Z_to_bv 64 32))
          F (Z_to_bv 64 0xa2f8c) fc None m1 (seg_rom asegs))).
  { intros a0' a1' s2' s3' s4' s5' m1 ws1 MU1 WM1 MI1 UAD1 UADL1 ACCD1.
    lwalk [0xa2f94].
    rewrite ?(bv_swrap_small 32 (i + 1)), ?(bv_swrap_small 32 (i * wpl + wpl)) by (change (bv_half_modulus 32) with (2^31); lia).
    replace (i * wpl + wpl) with ((i + 1) * wpl) by lia.
    lstep.
    destruct k as [|k].
    - assert (EI : i + 1 = dh) by lia. rewrite EI in *.
      brT.
      apply evt_done. unfold ucr_exit. do 23 eexists. exists m1, ws1. split; [reflexivity|].
      split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact UAD1| exact UADL1].
    - brF.
      eapply evt_cut.
      + eapply (IH (i + 1)) with (ws := ws1) (ld := ld) (doff := doff) (nfw := nfw) (lw := lw) (dwb := dwb) (pb := datad + 4 * doff) (pb2 := datad + 4 * doff);
          try eassumption; try lia.
      + intros ms' PO. apply evt_done. unfold ucr_exit in PO |- *.
        destruct PO as (ra' & t0' & t1' & t2' & s0' & s1' & a0'' & a1'' & a2' & a3' & a4' & a5' & a6' & a7' & s2'' & s3'' & s4'' & s5'' & s6''
                        & t3' & t4' & t5' & t6' & m' & ws' & E & MU' & WM' & R).
        do 25 eexists.
        split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU1 MU')|]. split; [exact (wmono_trans asegs _ _ _ WM1 WM')| exact R]. }
  (* [comment removed for export] *)
  assert (PARTIAL : forall (a1' s2' s3' s4' s5' : word) (m1 : mem) (ws1 : list word),
    munch (UNI_W datad ld) m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
    u32arr asegs m1 datad ws1 -> Z.of_nat (length ws1) = ld -> acc asegs m1 datad (4 * ld) ->
    evt asegs (ucr_exit sp gp tp s7 s8 s9 s10 s11 F fc m datad ld)
      (MS (mkR ra sp gp tp (Z_to_bv 64 lw) (Z_to_bv 64 2147450880) u (Z_to_bv 64 (datad + 4 * doff)) (Z_to_bv 64 5)
               (Z_to_bv 64 (datad + 4 * (doff + i * wpl + nfw))) a1' (Z_to_bv 64 1) (Z_to_bv 64 dh) (Z_to_bv 64 wpl)
               (Z_to_bv 64 dwb) (Z_to_bv 64 (datad + 4 * doff)) (Z_to_bv 64 nfw)
               s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (i * wpl)) (Z_to_bv 64 i) (Z_to_bv 64 0) (Z_to_bv 64 32))
          F (Z_to_bv 64 0xa2fd4) fc None m1 (seg_rom asegs))).
  { intros a1' s2' s3' s4' s5' m1 ws1 MU1 WM1 MI1 UAD1 UADL1 ACCD1.
    lstep.
    destruct (Z.eq_dec lw 0) as [LW0|LWN].
    - rewrite LW0 in *. brT. eapply ROWEND; eassumption.
    - brF. specialize (DB1 LWN).
      lwalk [0xa2f80].
      destruct (u32arr_nth ws1 (doff + i * wpl + nfw) ltac:(lia)) as (wd & NTHD).
      pose proof (u32arr_read asegs m1 datad ws1 (doff + i * wpl + nfw) wd _ UAD1 NTHD ltac:(lia) eq_refl) as RD.
      lstep. clear RD NTHD.
      lwalk [0xa2f88].
      arr_sw datad (doff + i * wpl + nfw) (datad + 4 * (doff + i * wpl + nfw)).
      eapply ROWEND; try eassumption. }
  lwalk [0xa2fcc].
  rewrite ?Z.add_0_r. rewrite ?(Z.mod_small (i * wpl)) by lia.
  lstep.
  destruct (Z.ltb_spec dwb 32) as [WLT|WGE].
  - (* [comment removed for export] *)
    brF.
    assert (NF0 : nfw = 0) by (subst nfw; apply Z.div_small; lia).
    lwalk [0xa2fd4].
    replace (i * wpl * 4 + (datad + 4 * doff)) with (datad + 4 * (doff + i * wpl + nfw)) by lia.
    eapply PARTIAL; try eassumption.
  - (* [comment removed for export] *)
    brT. lwalk [0xa3010].
    assert (NF1 : 1 <= nfw) by (subst nfw; apply Z.div_le_lower_bound; lia).
    eapply evt_cut.
    + eapply (ucw_words (Z.to_nat nfw) 0) with (ws := ws) (rb := doff + i * wpl) (ld := ld) (nfw := nfw) (c := nfw); try eassumption; try lia.
    + intros ms' PO. unfold ucw_exit in PO.
      destruct PO as (x1 & x2 & x3 & x4 & x5 & m' & ws' & -> & MU' & WM' & MI' & UAD' & UADL' & ACCD').
      unfold SHB in *.
      replace (datad + 4 * (doff + i * wpl + nfw)) with (datad + 4 * (doff + i * wpl + nfw)) by lia.
      eapply PARTIAL; eassumption.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ug1s_exit (ra sp gp tp t0 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (datad ld : Z) : machine_state -> Prop :=
  fun ms' => exists (s0' s1' a0' t3' t6' : word) (m' : mem) (ws' : list word),
    ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 SHB) t2 s0' s1' a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6')
             F (Z_to_bv 64 0xa2c6c) fc None m' (seg_rom asegs)
    /\ munch (UNI_W datad ld) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' datad ws' /\ Z.of_nat (length ws') = ld /\ acc asegs m' datad (4 * ld).

Lemma ug1s_rows : forall (k : nat) (q : Z)
    (ra sp gp tp t0 t2 s0 s1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 : word) F fc (m : mem)
    (datad ld wpl p p2 c : Z) (ws : list word),
  p = datad + 4 * q -> p2 = datad + 4 * q -> c = Z.of_nat k ->
  (1 <= k)%nat -> Z.of_nat k <= 20000 -> 0 < wpl <= 5001 -> 0 <= q -> q + (Z.of_nat k - 1) * wpl < ld -> ld <= 2^24 ->
  0 < datad -> datad mod 8 = 0 -> datad + 4 * ld <= 2^47 -> (datad + 4 * ld <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
  (datad + 4 * ld <= 0x10000 \/ SEGTOP_A <= datad) ->
  u32arr asegs m datad ws -> Z.of_nat (length ws) = ld -> acc asegs m datad (4 * ld) -> mem_inv asegs m ->
  evt asegs (ug1s_exit ra sp gp tp t0 t2 (Z_to_bv 64 (wpl * 4)) a2 a3 (Z_to_bv 64 0) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 F fc m datad ld)
    (MS (mkR ra sp gp tp t0 (Z_to_bv 64 SHB) t2 s0 s1 (Z_to_bv 64 p2) (Z_to_bv 64 (wpl * 4)) a2 a3 (Z_to_bv 64 0) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) t4 t5 (Z_to_bv 64 c))
        F (Z_to_bv 64 0xa2a50) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros q ra sp gp tp t0 t2 s0 s1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 F fc m
    datad ld wpl p p2 c ws -> -> -> HK1 KB WPLB Q0 QB LD D0 D8 DHI DSH DSEG UAD UADL ACCD MI.
  { lia. }
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (UNI_W datad ld) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (PQ : 0 <= Z.of_nat k * wpl) by (apply Z.mul_nonneg_nonneg; lia).
  lwalk [0xa2a64].
  destruct (u32arr_nth ws q ltac:(lia)) as (wv & NTH).
  pose proof (u32arr_read asegs m datad ws q wv (wa (datad + 4 * q)) UAD NTH ltac:(lia) ltac:(f_equal; lia)) as R.
  lstep. clear R NTH.
  lwalk [0xa2a70].
  arr_sw datad q (datad + 4 * q).
  lwalk [0xa2a94].
  rewrite ?(swrap32_modadd (Z.of_nat (S k)) (-1)) by lia.
  rewrite ?(bv_swrap_small 32 (Z.of_nat (S k) + -1)) by (change (bv_half_modulus 32) with (2^31); lia).
  replace (Z.of_nat (S k) + -1) with (Z.of_nat k) by lia.
  lstep.
  destruct k as [|k].
  - brF. lwalk [0xa2c6c].
    apply evt_done. unfold ug1s_exit. do 5 eexists. exists m0, aws. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact UAD|]. split; [exact UADL| exact ACCD].
  - brT.
    eapply evt_cut.
    + eapply (IH (q + wpl)) with (ws := aws) (ld := ld) (wpl := wpl); try eassumption; try lia.
    + intros ms' PO. apply evt_done. unfold ug1s_exit in PO |- *.
      destruct PO as (x1 & x2 & x3 & x4 & x5 & m' & ws' & E & MU' & WM' & R).
      do 7 eexists.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact R].
Qed.

(* [comment removed for export] *)
Definition ug1c_exit (ra sp gp tp t0 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (datad ld : Z) : machine_state -> Prop :=
  fun ms' => exists (s0' s1' a0' t3' t6' : word) (m' : mem) (ws' : list word),
    ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 SHB) t2 s0' s1' a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6')
             F (Z_to_bv 64 0xa2d84) fc None m' (seg_rom asegs)
    /\ munch (UNI_W datad ld) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' datad ws' /\ Z.of_nat (length ws') = ld /\ acc asegs m' datad (4 * ld).

Lemma ug1c_rows : forall (k : nat) (q : Z)
    (ra sp gp tp t0 t2 s0 s1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 : word) F fc (m : mem)
    (datad ld wpl p p2 c : Z) (ws : list word),
  p = datad + 4 * q -> p2 = datad + 4 * q -> c = Z.of_nat k ->
  (1 <= k)%nat -> Z.of_nat k <= 20000 -> 0 < wpl <= 5001 -> 0 <= q -> q + (Z.of_nat k - 1) * wpl < ld -> ld <= 2^24 ->
  0 < datad -> datad mod 8 = 0 -> datad + 4 * ld <= 2^47 -> (datad + 4 * ld <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
  (datad + 4 * ld <= 0x10000 \/ SEGTOP_A <= datad) ->
  u32arr asegs m datad ws -> Z.of_nat (length ws) = ld -> acc asegs m datad (4 * ld) -> mem_inv asegs m ->
  evt asegs (ug1c_exit ra sp gp tp t0 t2 (Z_to_bv 64 (wpl * 4)) a2 a3 (Z_to_bv 64 0) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 F fc m datad ld)
    (MS (mkR ra sp gp tp t0 (Z_to_bv 64 SHB) t2 s0 s1 (Z_to_bv 64 p2) (Z_to_bv 64 (wpl * 4)) a2 a3 (Z_to_bv 64 0) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) t4 t5 (Z_to_bv 64 c))
        F (Z_to_bv 64 0xa2988) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros q ra sp gp tp t0 t2 s0 s1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 F fc m
    datad ld wpl p p2 c ws -> -> -> HK1 KB WPLB Q0 QB LD D0 D8 DHI DSH DSEG UAD UADL ACCD MI.
  { lia. }
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (UNI_W datad ld) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (PQ : 0 <= Z.of_nat k * wpl) by (apply Z.mul_nonneg_nonneg; lia).
  lwalk [0xa299c].
  destruct (u32arr_nth ws q ltac:(lia)) as (wv & NTH).
  pose proof (u32arr_read asegs m datad ws q wv (wa (datad + 4 * q)) UAD NTH ltac:(lia) ltac:(f_equal; lia)) as R.
  lstep. clear R NTH.
  lwalk [0xa29a8].
  arr_sw datad q (datad + 4 * q).
  lwalk [0xa29cc].
  rewrite ?(swrap32_modadd (Z.of_nat (S k)) (-1)) by lia.
  rewrite ?(bv_swrap_small 32 (Z.of_nat (S k) + -1)) by (change (bv_half_modulus 32) with (2^31); lia).
  replace (Z.of_nat (S k) + -1) with (Z.of_nat k) by lia.
  lstep.
  destruct k as [|k].
  - brF. lwalk [0xa2d84].
    apply evt_done. unfold ug1c_exit. do 5 eexists. exists m0, aws. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact UAD|]. split; [exact UADL| exact ACCD].
  - brT.
    eapply evt_cut.
    + eapply (IH (q + wpl)) with (ws := aws) (ld := ld) (wpl := wpl); try eassumption; try lia.
    + intros ms' PO. apply evt_done. unfold ug1c_exit in PO |- *.
      destruct PO as (x1 & x2 & x3 & x4 & x5 & m' & ws' & E & MU' & WM' & R).
      do 7 eexists.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact R].
Qed.

(* [comment removed for export] *)
Definition ug3s_exit (ra sp gp tp t0 s0 s1 a1 a4 a5 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (datad ld : Z) : machine_state -> Prop :=
  fun ms' => exists (t2' a0' a2' a3' a6' : word) (m' : mem) (ws' : list word),
    ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 SHB) t2' s0 s1 a0' a1 a2' a3' a4 a5 a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xa2e30) fc None m' (seg_rom asegs)
    /\ munch (UNI_W datad ld) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' datad ws' /\ Z.of_nat (length ws') = ld /\ acc asegs m' datad (4 * ld).

Lemma ug3s_rows : forall (k : nat) (q : Z)
    (ra sp gp tp t0 s0 s1 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (datad ld wpl p p2 c : Z) (ws : list word),
  p = datad + 4 * q -> p2 = datad + 4 * q -> c = Z.of_nat k ->
  (1 <= k)%nat -> Z.of_nat k <= 20000 -> 0 < wpl <= 5001 -> 0 <= q -> q + (Z.of_nat k - 1) * wpl < ld -> ld <= 2^24 ->
  0 < datad -> datad mod 8 = 0 -> datad + 4 * ld <= 2^47 -> (datad + 4 * ld <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
  (datad + 4 * ld <= 0x10000 \/ SEGTOP_A <= datad) ->
  u32arr asegs m datad ws -> Z.of_nat (length ws) = ld -> acc asegs m datad (4 * ld) -> mem_inv asegs m ->
  evt asegs (ug3s_exit ra sp gp tp t0 s0 s1 (Z_to_bv 64 (wpl * 4)) (Z_to_bv 64 0) a5 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m datad ld)
    (MS (mkR ra sp gp tp t0 (Z_to_bv 64 SHB) (Z_to_bv 64 c) s0 s1 (Z_to_bv 64 p2) (Z_to_bv 64 (wpl * 4)) (Z_to_bv 64 p) a3 (Z_to_bv 64 0) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xa2d28) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros q ra sp gp tp t0 s0 s1 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    datad ld wpl p p2 c ws -> -> -> HK1 KB WPLB Q0 QB LD D0 D8 DHI DSH DSEG UAD UADL ACCD MI.
  { lia. }
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (UNI_W datad ld) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (PQ : 0 <= Z.of_nat k * wpl) by (apply Z.mul_nonneg_nonneg; lia).
  lwalk [0xa2d3c].
  destruct (u32arr_nth ws q ltac:(lia)) as (wv & NTH).
  pose proof (u32arr_read asegs m datad ws q wv (wa (datad + 4 * q)) UAD NTH ltac:(lia) ltac:(f_equal; lia)) as R.
  lstep. clear R NTH.
  lwalk [0xa2d48].
  arr_sw datad q (datad + 4 * q).
  lwalk [0xa2d6c].
  rewrite ?(swrap32_modadd (Z.of_nat (S k)) (-1)) by lia.
  rewrite ?(bv_swrap_small 32 (Z.of_nat (S k) + -1)) by (change (bv_half_modulus 32) with (2^31); lia).
  replace (Z.of_nat (S k) + -1) with (Z.of_nat k) by lia.
  lstep.
  destruct k as [|k].
  - brF. lwalk [0xa2e30].
    apply evt_done. unfold ug3s_exit. do 5 eexists. exists m0, aws. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact UAD|]. split; [exact UADL| exact ACCD].
  - brT.
    eapply evt_cut.
    + eapply (IH (q + wpl)) with (ws := aws) (ld := ld) (wpl := wpl); try eassumption; try lia.
    + intros ms' PO. apply evt_done. unfold ug3s_exit in PO |- *.
      destruct PO as (x1 & x2 & x3 & x4 & x5 & m' & ws' & E & MU' & WM' & R).
      do 7 eexists.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact R].
Qed.

(* [comment removed for export] *)
Definition ug3c_exit (ra sp gp tp t0 s0 s1 a1 a3 a4 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (datad ld : Z) : machine_state -> Prop :=
  fun ms' => exists (t2' a0' a2' a5' a6' : word) (m' : mem) (ws' : list word),
    ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 SHB) t2' s0 s1 a0' a1 a2' a3 a4 a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xa2e30) fc None m' (seg_rom asegs)
    /\ munch (UNI_W datad ld) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' datad ws' /\ Z.of_nat (length ws') = ld /\ acc asegs m' datad (4 * ld).

Lemma ug3c_rows : forall (k : nat) (q : Z)
    (ra sp gp tp t0 s0 s1 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (datad ld wpl p p2 c : Z) (ws : list word),
  p = datad + 4 * q -> p2 = datad + 4 * q -> c = Z.of_nat k ->
  (1 <= k)%nat -> Z.of_nat k <= 20000 -> 0 < wpl <= 5001 -> 0 <= q -> q + (Z.of_nat k - 1) * wpl < ld -> ld <= 2^24 ->
  0 < datad -> datad mod 8 = 0 -> datad + 4 * ld <= 2^47 -> (datad + 4 * ld <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
  (datad + 4 * ld <= 0x10000 \/ SEGTOP_A <= datad) ->
  u32arr asegs m datad ws -> Z.of_nat (length ws) = ld -> acc asegs m datad (4 * ld) -> mem_inv asegs m ->
  evt asegs (ug3c_exit ra sp gp tp t0 s0 s1 (Z_to_bv 64 (wpl * 4)) a3 (Z_to_bv 64 0) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m datad ld)
    (MS (mkR ra sp gp tp t0 (Z_to_bv 64 SHB) (Z_to_bv 64 c) s0 s1 (Z_to_bv 64 p2) (Z_to_bv 64 (wpl * 4)) (Z_to_bv 64 p) a3 (Z_to_bv 64 0) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xa3070) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros q ra sp gp tp t0 s0 s1 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    datad ld wpl p p2 c ws -> -> -> HK1 KB WPLB Q0 QB LD D0 D8 DHI DSH DSEG UAD UADL ACCD MI.
  { lia. }
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (UNI_W datad ld) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (PQ : 0 <= Z.of_nat k * wpl) by (apply Z.mul_nonneg_nonneg; lia).
  lwalk [0xa3084].
  destruct (u32arr_nth ws q ltac:(lia)) as (wv & NTH).
  pose proof (u32arr_read asegs m datad ws q wv (wa (datad + 4 * q)) UAD NTH ltac:(lia) ltac:(f_equal; lia)) as R.
  lstep. clear R NTH.
  lwalk [0xa3090].
  arr_sw datad q (datad + 4 * q).
  lwalk [0xa30b4].
  rewrite ?(swrap32_modadd (Z.of_nat (S k)) (-1)) by lia.
  rewrite ?(bv_swrap_small 32 (Z.of_nat (S k) + -1)) by (change (bv_half_modulus 32) with (2^31); lia).
  replace (Z.of_nat (S k) + -1) with (Z.of_nat k) by lia.
  lstep.
  destruct k as [|k].
  - brF. lwalk [0xa2e30].
    apply evt_done. unfold ug3c_exit. do 5 eexists. exists m0, aws. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact UAD|]. split; [exact UADL| exact ACCD].
  - brT.
    eapply evt_cut.
    + eapply (IH (q + wpl)) with (ws := aws) (ld := ld) (wpl := wpl); try eassumption; try lia.
    + intros ms' PO. apply evt_done. unfold ug3c_exit in PO |- *.
      destruct PO as (x1 & x2 & x3 & x4 & x5 & m' & ws' & E & MU' & WM' & R).
      do 7 eexists.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact R].
Qed.

(* [comment removed for export] *)
Definition ug2s_wexit (ra sp gp tp t0 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (datad ld : Z) : machine_state -> Prop :=
  fun ms' => exists (a0' s2' s3' s4' s5' : word) (m' : mem) (ws' : list word),
    ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 SHB) t2 (Z_to_bv 64 1) (Z_to_bv 64 1) a0' a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xa2ce8) fc None m' (seg_rom asegs)
    /\ munch (UNI_W datad ld) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' datad ws' /\ Z.of_nat (length ws') = ld /\ acc asegs m' datad (4 * ld).

Lemma ug2s_words : forall (k : nat) (j : Z)
    (ra sp gp tp t0 t2 a1 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (datad ld rb n p p2 pr c : Z) (ws : list word),
  p = datad + 4 * (rb + j) -> p2 = datad + 4 * (rb + j) -> pr = datad + 4 * rb -> c = n - j ->
  Z.of_nat k = n - j -> 0 <= j -> (1 <= k)%nat -> n <= 2^20 -> 0 <= rb -> rb + n <= ld -> ld <= 2^24 ->
  0 < datad -> datad mod 8 = 0 -> datad + 4 * ld <= 2^47 -> (datad + 4 * ld <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
  (datad + 4 * ld <= 0x10000 \/ SEGTOP_A <= datad) ->
  u32arr asegs m datad ws -> Z.of_nat (length ws) = ld -> acc asegs m datad (4 * ld) -> mem_inv asegs m ->
  evt asegs (ug2s_wexit ra sp gp tp t0 t2 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 pr) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m datad ld)
    (MS (mkR ra sp gp tp t0 (Z_to_bv 64 SHB) t2 (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 p2) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 pr) (Z_to_bv 64 p) (Z_to_bv 64 c) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xa2c9c) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j ra sp gp tp t0 t2 a1 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    datad ld rb n p p2 pr c ws -> -> -> -> HK HJ HK1 NB RB RBN LD D0 D8 DHI DSH DSEG UAD UADL ACCD MI.
  { lia. }
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (UNI_W datad ld) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lwalk [0xa2cc0].
  arr_sw datad (rb + j) (datad + 4 * (rb + j)).
  lwalk [0xa2cd0].
  lstep.
  destruct k as [|k].
  - replace (n - j + -1) with 0 by lia. brF. lwalk [0xa2ce8].
    apply evt_done. unfold ug2s_wexit. do 5 eexists. exists m0, aws. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact UAD|]. split; [exact UADL| exact ACCD].
  - brT.
    eapply evt_cut.
    + eapply (IH (j + 1)) with (ws := aws) (rb := rb) (ld := ld) (n := n); try eassumption; try lia.
    + intros ms' PO. apply evt_done. unfold ug2s_wexit in PO |- *.
      destruct PO as (x1 & x2 & x3 & x4 & x5 & m' & ws' & E & MU' & WM' & R).
      do 7 eexists.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact R].
Qed.

(* [comment removed for export] *)
Definition ug2c_wexit (ra sp gp tp t0 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (datad ld : Z) : machine_state -> Prop :=
  fun ms' => exists (a0' s1' s2' s3' s4' : word) (m' : mem) (ws' : list word),
    ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 SHB) t2 (Z_to_bv 64 1) s1' a0' a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 (Z_to_bv 64 1))
             F (Z_to_bv 64 0xa2dfc) fc None m' (seg_rom asegs)
    /\ munch (UNI_W datad ld) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' datad ws' /\ Z.of_nat (length ws') = ld /\ acc asegs m' datad (4 * ld).

Lemma ug2c_words : forall (k : nat) (j : Z)
    (ra sp gp tp t0 t2 a1 a2 a3 a4 a5 a6 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 : word) F fc (m : mem)
    (datad ld rb n p p2 pr c : Z) (ws : list word),
  p = datad + 4 * (rb + j) -> p2 = datad + 4 * (rb + j) -> pr = datad + 4 * rb -> c = n - j ->
  Z.of_nat k = n - j -> 0 <= j -> (1 <= k)%nat -> n <= 2^20 -> 0 <= rb -> rb + n <= ld -> ld <= 2^24 ->
  0 < datad -> datad mod 8 = 0 -> datad + 4 * ld <= 2^47 -> (datad + 4 * ld <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
  (datad + 4 * ld <= 0x10000 \/ SEGTOP_A <= datad) ->
  u32arr asegs m datad ws -> Z.of_nat (length ws) = ld -> acc asegs m datad (4 * ld) -> mem_inv asegs m ->
  evt asegs (ug2c_wexit ra sp gp tp t0 t2 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 pr) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 F fc m datad ld)
    (MS (mkR ra sp gp tp t0 (Z_to_bv 64 SHB) t2 (Z_to_bv 64 1) (Z_to_bv 64 p) (Z_to_bv 64 p2) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 pr) (Z_to_bv 64 c) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 (Z_to_bv 64 1))
        F (Z_to_bv 64 0xa2db0) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j ra sp gp tp t0 t2 a1 a2 a3 a4 a5 a6 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 F fc m
    datad ld rb n p p2 pr c ws -> -> -> -> HK HJ HK1 NB RB RBN LD D0 D8 DHI DSH DSEG UAD UADL ACCD MI.
  { lia. }
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (UNI_W datad ld) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lwalk [0xa2dd4].
  arr_sw datad (rb + j) (datad + 4 * (rb + j)).
  lwalk [0xa2de4].
  lstep.
  destruct k as [|k].
  - replace (n - j + -1) with 0 by lia. brF. lwalk [0xa2dfc].
    apply evt_done. unfold ug2c_wexit. do 5 eexists. exists m0, aws. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact UAD|]. split; [exact UADL| exact ACCD].
  - brT.
    eapply evt_cut.
    + eapply (IH (j + 1)) with (ws := aws) (rb := rb) (ld := ld) (n := n); try eassumption; try lia.
    + intros ms' PO. apply evt_done. unfold ug2c_wexit in PO |- *.
      destruct PO as (x1 & x2 & x3 & x4 & x5 & m' & ws' & E & MU' & WM' & R).
      do 7 eexists.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact R].
Qed.

(* [comment removed for export] *)
Definition ug2s_exit (ra sp gp tp t0 t2 a1 a2 a3 a4 a5 a6 s6 s7 s8 s9 s10 s11 t4 t5 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (datad ld : Z) : machine_state -> Prop :=
  fun ms' => exists (s0' s1' a0' a7' s2' s3' s4' s5' t3' t6' : word) (m' : mem) (ws' : list word),
    ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 SHB) t2 s0' s1' a0' a1 a2 a3 a4 a5 a6 a7' s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3' t4 t5 t6')
             F (Z_to_bv 64 0xa2d18) fc None m' (seg_rom asegs)
    /\ munch (UNI_W datad ld) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' datad ws' /\ Z.of_nat (length ws') = ld /\ acc asegs m' datad (4 * ld).

Lemma ug2s_rows : forall (k : nat) (q : Z)
    (ra sp gp tp t0 t2 s0 s1 a0 a2 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) F fc (m : mem)
    (datad ld wpl n dh p p2 i : Z) (ws : list word),
  p = datad + 4 * q -> p2 = datad + 4 * q -> i = dh - Z.of_nat k ->
  (1 <= k)%nat -> Z.of_nat k <= dh -> dh <= 20000 -> 0 < wpl <= 5001 -> 1 <= n <= 5000 -> 0 <= q -> q + (Z.of_nat k - 1) * wpl + n <= ld -> ld <= 2^24 ->
  0 < datad -> datad mod 8 = 0 -> datad + 4 * ld <= 2^47 -> (datad + 4 * ld <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
  (datad + 4 * ld <= 0x10000 \/ SEGTOP_A <= datad) ->
  u32arr asegs m datad ws -> Z.of_nat (length ws) = ld -> acc asegs m datad (4 * ld) -> mem_inv asegs m ->
  evt asegs (ug2s_exit ra sp gp tp t0 t2 (Z_to_bv 64 (wpl * 4)) a2 (Z_to_bv 64 dh) (Z_to_bv 64 0) a5 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) (Z_to_bv 64 (-1)) F fc m datad ld)
    (MS (mkR ra sp gp tp t0 (Z_to_bv 64 SHB) t2 s0 s1 a0 (Z_to_bv 64 (wpl * 4)) a2 (Z_to_bv 64 dh) (Z_to_bv 64 0) a5 (Z_to_bv 64 n) (Z_to_bv 64 p) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 i) (Z_to_bv 64 1) (Z_to_bv 64 (-1)) (Z_to_bv 64 p2))
        F (Z_to_bv 64 0xa2c84) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros q ra sp gp tp t0 t2 s0 s1 a0 a2 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m
    datad ld wpl n dh p p2 i ws -> -> -> HK1 KB DHB WPLB NR Q0 QB LD D0 D8 DHI DSH DSEG UAD UADL ACCD MI.
  { lia. }
  unfold SEGTOP_A, SHB in *.
  assert (PQ : 0 <= Z.of_nat k * wpl) by (apply Z.mul_nonneg_nonneg; lia).
  lwalk [0xa2c9c].
  repeat match goal with |- context [Z.b2z (0 <? ?e)] => replace (Z.b2z (0 <? e)) with 1 by (symmetry; destruct (Z.ltb_spec 0 e); [reflexivity| lia]) end.
  change (Z.land 1 1) with 1.
  eapply evt_cut.
  { eapply (ug2s_words (Z.to_nat n) 0) with (ws := ws) (rb := q) (ld := ld) (n := n); try eassumption; try lia. }
  intros ms' PO. unfold ug2s_wexit in PO.
  destruct PO as (x1 & x2 & x3 & x4 & x5 & m' & ws' & -> & MU' & WM' & MI' & UAD' & UADL' & ACCD').
  unfold SHB in *.
  lwalk [0xa2d14].
  rewrite ?(bv_swrap_small 32 (dh - Z.of_nat (S k) + 1)) by (change (bv_half_modulus 32) with (2^31); lia).
  lstep.
  destruct k as [|k].
  - replace (dh - Z.of_nat 1 + 1) with dh by lia. brF. lwalk [0xa2d18].
    apply evt_done. unfold ug2s_exit. do 10 eexists. exists m', ws'. split; [reflexivity|].
    split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact UAD'|]. split; [exact UADL'| exact ACCD'].
  - brT.
    eapply evt_cut.
    + eapply (IH (q + wpl)) with (ws := ws') (ld := ld) (wpl := wpl) (n := n) (dh := dh); try eassumption; try lia.
    + intros ms' PO. apply evt_done. unfold ug2s_exit in PO |- *.
      destruct PO as (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & m'' & ws'' & E & MU'' & WM'' & R).
      do 12 eexists.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU' MU'')|]. split; [exact (wmono_trans asegs _ _ _ WM' WM'')| exact R].
Qed.

(* [comment removed for export] *)
Definition ug2c_exit (ra sp gp tp t0 t2 a1 a2 a3 a4 a5 a6 s5 s6 s7 s8 s9 s10 s11 t4 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (datad ld : Z) : machine_state -> Prop :=
  fun ms' => exists (s0' s1' a0' a7' s2' s3' s4' t3' t5' t6' : word) (m' : mem) (ws' : list word),
    ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 SHB) t2 s0' s1' a0' a1 a2 a3 a4 a5 a6 a7' s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 t3' t4 t5' t6')
             F (Z_to_bv 64 0xa2e2c) fc None m' (seg_rom asegs)
    /\ munch (UNI_W datad ld) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' datad ws' /\ Z.of_nat (length ws') = ld /\ acc asegs m' datad (4 * ld).

Lemma ug2c_rows : forall (k : nat) (q : Z)
    (ra sp gp tp t0 t2 s0 s1 a0 a2 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) F fc (m : mem)
    (datad ld wpl n dh p p2 i : Z) (ws : list word),
  p = datad + 4 * q -> p2 = datad + 4 * q -> i = dh - Z.of_nat k ->
  (1 <= k)%nat -> Z.of_nat k <= dh -> dh <= 20000 -> 0 < wpl <= 5001 -> 1 <= n <= 5000 -> 0 <= q -> q + (Z.of_nat k - 1) * wpl + n <= ld -> ld <= 2^24 ->
  0 < datad -> datad mod 8 = 0 -> datad + 4 * ld <= 2^47 -> (datad + 4 * ld <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
  (datad + 4 * ld <= 0x10000 \/ SEGTOP_A <= datad) ->
  u32arr asegs m datad ws -> Z.of_nat (length ws) = ld -> acc asegs m datad (4 * ld) -> mem_inv asegs m ->
  evt asegs (ug2c_exit ra sp gp tp t0 t2 (Z_to_bv 64 (wpl * 4)) a2 (Z_to_bv 64 dh) (Z_to_bv 64 0) a5 (Z_to_bv 64 n) s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) F fc m datad ld)
    (MS (mkR ra sp gp tp t0 (Z_to_bv 64 SHB) t2 s0 s1 a0 (Z_to_bv 64 (wpl * 4)) a2 (Z_to_bv 64 dh) (Z_to_bv 64 0) a5 (Z_to_bv 64 n) (Z_to_bv 64 p) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 i) (Z_to_bv 64 1) (Z_to_bv 64 p2) t6)
        F (Z_to_bv 64 0xa2d98) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros q ra sp gp tp t0 t2 s0 s1 a0 a2 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 F fc m
    datad ld wpl n dh p p2 i ws -> -> -> HK1 KB DHB WPLB NR Q0 QB LD D0 D8 DHI DSH DSEG UAD UADL ACCD MI.
  { lia. }
  unfold SEGTOP_A, SHB in *.
  assert (PQ : 0 <= Z.of_nat k * wpl) by (apply Z.mul_nonneg_nonneg; lia).
  lwalk [0xa2db0].
  repeat match goal with |- context [Z.b2z (0 <? ?e)] => replace (Z.b2z (0 <? e)) with 1 by (symmetry; destruct (Z.ltb_spec 0 e); [reflexivity| lia]) end.
  change (Z.land 1 1) with 1.
  eapply evt_cut.
  { eapply (ug2c_words (Z.to_nat n) 0) with (ws := ws) (rb := q) (ld := ld) (n := n); try eassumption; try lia. }
  intros ms' PO. unfold ug2c_wexit in PO.
  destruct PO as (x1 & x2 & x3 & x4 & x5 & m' & ws' & -> & MU' & WM' & MI' & UAD' & UADL' & ACCD').
  unfold SHB in *.
  lwalk [0xa2e28].
  rewrite ?(bv_swrap_small 32 (dh - Z.of_nat (S k) + 1)) by (change (bv_half_modulus 32) with (2^31); lia).
  lstep.
  destruct k as [|k].
  - replace (dh - Z.of_nat 1 + 1) with dh by lia. brF. lwalk [0xa2e2c].
    apply evt_done. unfold ug2c_exit. do 10 eexists. exists m', ws'. split; [reflexivity|].
    split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact UAD'|]. split; [exact UADL'| exact ACCD'].
  - brT.
    eapply evt_cut.
    + eapply (IH (q + wpl)) with (ws := ws') (ld := ld) (wpl := wpl) (n := n) (dh := dh); try eassumption; try lia.
    + intros ms' PO. apply evt_done. unfold ug2c_exit in PO |- *.
      destruct PO as (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & m'' & ws'' & E & MU'' & WM'' & R).
      do 12 eexists.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU' MU'')|]. split; [exact (wmono_trans asegs _ _ _ WM' WM'')| exact R].
Qed.
