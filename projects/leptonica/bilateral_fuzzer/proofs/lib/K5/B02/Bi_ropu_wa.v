(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (recorded (KReplay) proofs re-proved by tactics). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit Lept_chain Lept_leaf Lept_objkit Lept_deserkit Pm_gaps_iface Pm_iface Pm_iface2 Pm_iface4 Pm_ckit Pm_okit Cf_iface Cf_kit Km_setelem Km_iface Km_kit RT_fk RT_fk_iface Bi_iface Bi_fktw Bi_fkkit Bi_ropkit Bi_ropu_iface LeptB_guard LeptB_guard2 LeptB_guard3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* The last-word masks: the bytes of lmask32 (0x28da0), read from the image. *)
Local Lemma ropu_lmask_bytes : forall m : mem, mem_inv asegs m ->
  exists bs, bytes_at asegs m 0x28da0 bs /\ Z.of_nat (length bs) = 132.
Proof.
  intros m MI. destruct (image_bytes asegs 0x28da0 132) as [bs|] eqn:IB; [| vm_compute in IB; discriminate IB].
  assert (OK : ro_bytes_b asegs 0x28da0 bs = true) by (vm_compute in IB; injection IB as <-; vm_compute; reflexivity).
  pose proof (image_bytes_length asegs _ _ _ IB) as LB.
  exists bs. split; [apply ro_bytes_at; [exact MI| lia| rewrite LB; lia| apply ro_bytes_b_sound; exact OK]| rewrite LB; reflexivity].
Qed.
Local Lemma ropu_ztobv_modM : forall e, Z_to_bv 64 (e mod 18446744073709551616) = Z_to_bv 64 e.
Proof. intros e. exact (ZBridge.Z_to_bv_mod64 e). Qed.
Local Lemma ropu_srliw5_small : forall j, 0 <= j < 2^31 -> bv_swrap 32 (bv_wrap 32 j / 32) = j / 32.
Proof.
  intros j Hj. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small j) by lia.
  apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). split; [apply Z.le_trans with 0; [lia| apply Z.div_pos; lia]| apply Z.div_lt_upper_bound; lia].
Qed.

(* The walk's normalisation between steps (B: the hidden bounds of the walk). *)
Local Ltac ropu_cnb B :=
  rewrite ?Z.add_0_r;
  repeat match goal with |- context [bv_swrap 32 (bv_wrap 32 ?j / ?d) mod 18446744073709551616] =>
    rewrite (srliw_idx j d) by (clear - B; unfold hid in *; lia) end;
  repeat match goal with |- context [bv_swrap 32 ?z] =>
    rewrite (bv_swrap_small 32 z) by (change (bv_half_modulus 32) with (2^31); clear - B; unfold hid in *; lia) end;
  repeat match goal with |- context [?E mod 18446744073709551616] =>
    rewrite (Z.mod_small E 18446744073709551616) by (clear - B; unfold hid in *; lia) end;
  rewrite ?ropu_ztobv_modM.
Local Ltac ropu_bwalk stops B := repeat (tryif at_stop stops then fail else (ropu_cnb B; awalk1)).
Local Ltac ropu_dedup_ro := repeat match goal with H1 : ro_cells asegs ?m ?a ?c, H2 : ro_cells asegs ?m ?a ?c |- _ => clear H2 end.
Local Ltac ropu_drop_acc a := repeat match goal with H : acc asegs _ a _ |- _ => clear H end.
(* The same normalisation inside the row loops, where the bounds are plain hypotheses. *)
Local Ltac ropu_nrm :=
  rewrite ?Z.add_0_r;
  repeat match goal with |- context [bv_swrap 32 ?z] =>
    rewrite (bv_swrap_small 32 z) by (change (bv_half_modulus 32) with (2^31); lia) end;
  repeat match goal with |- context [?E mod 18446744073709551616] =>
    rewrite (Z.mod_small E 18446744073709551616) by lia end;
  rewrite ?Z.add_0_r.
(* Give register r the value T (equal to its own by lia), the form a loop lemma states. *)
Local Ltac ropu_regfix r T := reg_val r ltac:(fun v => lazymatch v with Z_to_bv 64 ?X =>
  first [ constr_eq X T | replace (Z_to_bv 64 X) with (Z_to_bv 64 T) by (f_equal; lia) ] end).

(* [comment removed for export] *)
Definition uw_words_exit (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (D n : Z) : machine_state -> Prop :=
  fun ms' => exists (s3' s4' s5' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (D + 4 * n)) (Z_to_bv 64 (D + 4 * n)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (D + 4 * n)) s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xb4460) fc None m' (seg_rom asegs)
    /\ munch [(D, D + 4 * n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'.

(* [comment removed for export] *)
Lemma uw_words_loop : forall (k : nat) (j : Z)
    (ra sp gp tp t0 t2 s0 a0 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t6 : word) F fc (m : mem) (DA n : Z),
  Z.of_nat k = n - j -> 0 <= j -> (1 <= k)%nat -> n < 2^26 ->
  0 < DA -> DA mod 4 = 0 -> DA + 4 * n <= 2^47 ->
  (DA + 4 * n <= 0x7fff7000 \/ 0x10007fff8000 <= DA) ->
  wr_at asegs m DA (4 * n) -> acc asegs m DA (4 * n) -> mem_inv asegs m ->
  evt asegs (uw_words_exit ra sp gp tp t0 (Z_to_bv 64 2147450880) t2 s0 (Z_to_bv 64 5) a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 (Z_to_bv 64 0) t6 F fc m DA n)
    (MS (mkR ra sp gp tp t0 (Z_to_bv 64 2147450880) t2 s0 (Z_to_bv 64 5) a0 (Z_to_bv 64 (DA + 4 * j)) a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (DA + 4 * j)) (Z_to_bv 64 (n - j)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 (Z_to_bv 64 0) t6)
        F (Z_to_bv 64 0xb449c) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j ra sp gp tp t0 t2 s0 a0 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t6 F fc m DA n
    HK HJ HK1 HN D0 D4 DHI DSH WRD ACD MI.
  { lia. }
  pose proof (munch_refl [(DA, DA + 4 * n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  gwalk [0xb44c4].
  hstore4 WRD (DA + 4 * j).
  gwalk [0xb44d0].
  ropu_nrm.
  lstep.
  destruct k as [|k].
  { ropu_regfix (Z_to_bv 5 19) 0; brF.
    gwalk [0xb4460].
    ropu_regfix (Z_to_bv 5 10) (DA + 4 * n); ropu_regfix (Z_to_bv 5 11) (DA + 4 * n); ropu_regfix (Z_to_bv 5 18) (DA + 4 * n).
    apply evt_done; unfold uw_words_exit; do 3 eexists; eexists; split; [reflexivity|];
      split; [exact MU|]; split; [exact WM| exact MI]. }
  brT.
  ropu_regfix (Z_to_bv 5 11) (DA + 4 * (j + 1)); ropu_regfix (Z_to_bv 5 18) (DA + 4 * (j + 1)); ropu_regfix (Z_to_bv 5 19) (n - (j + 1)).
  eapply evt_mono.
  { eapply (IH (j + 1)) with (DA := DA) (n := n); first [ eassumption | lia ]. }
  intros ms' PO. unfold uw_words_exit in PO |- *.
  destruct PO as (x1 & x2 & x3 & m' & E & MU' & WM' & MI').
  do 3 eexists; eexists; split; [exact E|]; split; [exact (munch_trans _ _ _ _ MU MU')|]; split; [exact (wmono_trans asegs _ _ _ WM WM')| exact MI'].
Qed.

(* [comment removed for export] *)
Definition uw_part_exit (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (DW : Z) : machine_state -> Prop :=
  fun ms' => exists (a1' s2' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2 a3 a4 a5 a6 a7 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xb4418) fc None m' (seg_rom asegs)
    /\ munch [(DW, DW + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'.

Lemma uw_part : forall (ra sp gp tp t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lwb DW : Z),
  0 < lwb < 32 -> 0 < DW -> DW mod 4 = 0 -> DW + 4 <= 2^47 ->
  (DW + 4 <= 0x7fff7000 \/ 0x10007fff8000 <= DW) ->
  wr_at asegs m DW 4 -> acc asegs m DW 4 -> mem_inv asegs m ->
  evt asegs (uw_part_exit ra sp gp tp (Z_to_bv 64 lwb) (Z_to_bv 64 2147450880) t2 s0 s1 (Z_to_bv 64 DW) a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m DW)
    (MS (mkR ra sp gp tp (Z_to_bv 64 lwb) (Z_to_bv 64 2147450880) t2 s0 s1 (Z_to_bv 64 DW) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5
             s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb4460) fc None m (seg_rom asegs)).
Proof.
  intros ra sp gp tp t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lwb DW LWB D0 D4 DHI DSH WRD ACD MI.
  pose proof (munch_refl [(DW, DW + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  gwalk [0xb440c].
  hload4 WRD DW.
  gwalk [0xb4414].
  hstore4 WRD DW.
  apply evt_done; unfold uw_part_exit; do 2 eexists; eexists; split; [reflexivity|]; split; [exact MU|]; split; [exact WM| exact MI].
Qed.

(* [comment removed for export] *)
Definition uw_rows_exit (sp gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (DR dn : Z) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0xb42bc) fc None m' (seg_rom asegs)
    /\ munch [(DR, DR + dn)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'.

(* [comment removed for export] *)
Lemma uw_rows : forall (k : nat) (i : Z)
    (ra sp gp tp t2 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) F fc (m : mem) (dh dwb nfw lwb dwpl PF DR dn : Z),
  Z.of_nat k = dh - i -> 0 <= i -> (1 <= k)%nat -> dh <= 20000 ->
  dwb = 32 * nfw + lwb -> 0 <= nfw -> 0 <= lwb < 32 -> 0 < dwb -> dwb <= 8 * 20000 ->
  0 < dwpl <= 2^24 -> dwpl * dh <= 2^24 ->
  0 < DR -> DR mod 4 = 0 -> DR + dn <= 2^47 -> PF mod 4 = 0 ->
  (DR + dn <= 0x7fff7000 \/ 0x10007fff8000 <= DR) ->
  (forall i', 0 <= i' < dh -> DR <= PF + 4 * (dwpl * i') /\ PF + 4 * (dwpl * i') + 4 * (nfw + 1) <= DR + dn + 4 * (if lwb =? 0 then 1 else 0)) ->
  wr_at asegs m DR dn -> acc asegs m DR dn -> mem_inv asegs m ->
  evt asegs (uw_rows_exit sp gp tp s7 s8 s9 s10 s11 F fc m DR dn)
    (MS (mkR ra sp gp tp (Z_to_bv 64 lwb) (Z_to_bv 64 2147450880) t2 (Z_to_bv 64 PF) (Z_to_bv 64 5) a0 a1 (Z_to_bv 64 1) (Z_to_bv 64 dh)
             (Z_to_bv 64 dwpl) (Z_to_bv 64 dwb) (Z_to_bv 64 PF) (Z_to_bv 64 nfw) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             (Z_to_bv 64 (dwpl * i)) (Z_to_bv 64 i) (Z_to_bv 64 0) (Z_to_bv 64 32))
        F (Z_to_bv 64 0xb4424) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i ra sp gp tp t2 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m dh dwb nfw lwb dwpl PF DR dn
    HK HI HK1 HDH EDW NF0 LWB DW0 DWHI DWPL DDH D0 D4 DHI PF4 DSH RD WRD ACD MI.
  { lia. }
  pose proof (munch_refl [(DR, DR + dn)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  destruct (RD i ltac:(lia)) as (RD1 & RD2).
  assert (DI0 : 0 <= dwpl * i) by (apply Z.mul_nonneg_nonneg; lia).
  assert (DI1 : dwpl * i + dwpl <= 2^24).
  { assert (dwpl * (i + 1) <= dwpl * dh) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
  assert (LB : 0 <= (if lwb =? 0 then 1 else 0) <= 1) by (destruct (lwb =? 0); lia).
  assert (RD3 : PF + 4 * (dwpl * i) + 4 * nfw <= DR + dn) by lia.
  assert (PFP : DR <= PF).
  { destruct (RD 0 ltac:(lia)) as (R0 & _). rewrite Z.mul_0_r in R0. lia. }
  (* The end of a row from 0xb4418: the next row, or the exit after the last one. *)
  assert (TAIL : forall (a0' a1' s2' s3' s4' s5' : word) (mT : mem),
    munch [(DR, DR + dn)] m mT -> wmono asegs m mT -> mem_inv asegs mT -> wr_at asegs mT DR dn -> acc asegs mT DR dn ->
    evt asegs (uw_rows_exit sp gp tp s7 s8 s9 s10 s11 F fc m DR dn)
      (MS (mkR ra sp gp tp (Z_to_bv 64 lwb) (Z_to_bv 64 2147450880) t2 (Z_to_bv 64 PF) (Z_to_bv 64 5) a0' a1' (Z_to_bv 64 1) (Z_to_bv 64 dh)
               (Z_to_bv 64 dwpl) (Z_to_bv 64 dwb) (Z_to_bv 64 PF) (Z_to_bv 64 nfw) s2' s3' s4' s5' s6 s7 s8 s9 s10 s11
               (Z_to_bv 64 (dwpl * i)) (Z_to_bv 64 i) (Z_to_bv 64 0) (Z_to_bv 64 32))
          F (Z_to_bv 64 0xb4418) fc None mT (seg_rom asegs))).
  { intros a0' a1' s2' s3' s4' s5' mT MUT WMT MIT WRDT ACDT.
    gwalk [0xb4420].
    ropu_nrm.
    lstep.
    destruct k as [|k].
    { assert (EI : i + 1 = dh) by lia.
      brT.
      apply evt_done; unfold uw_rows_exit; do 23 eexists; exists mT; split; [reflexivity|]; split; [exact MUT|]; split; [exact WMT| exact MIT]. }
    brF.
    ropu_regfix (Z_to_bv 5 28) (dwpl * (i + 1)); ropu_regfix (Z_to_bv 5 29) (i + 1).
    eapply evt_mono.
    { eapply (IH (i + 1)) with (DR := DR) (dn := dn) (PF := PF) (nfw := nfw) (lwb := lwb) (dwb := dwb) (dh := dh) (dwpl := dwpl);
        first [ eassumption | lia ]. }
    intros ms' PO. unfold uw_rows_exit in PO |- *.
    destruct PO as (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y20 & y21 & y22 & y23 & m' & E & MU' & WM' & MI').
    do 23 eexists; exists m'; split; [exact E|]; split; [exact (munch_trans _ _ _ _ MUT MU')|]; split; [exact (wmono_trans asegs _ _ _ WMT WM')| exact MI']. }
  destruct (Z_le_gt_dec 32 dwb) as [BIG|SMALL].
  { (* The full words of the row, then its last word when lwb <> 0. *)
    assert (NF1 : 1 <= nfw) by lia.
    gwalk [0xb449c].
    ropu_nrm.
    ropu_regfix (Z_to_bv 5 11) (PF + 4 * (dwpl * i) + 4 * 0); ropu_regfix (Z_to_bv 5 18) (PF + 4 * (dwpl * i) + 4 * 0); ropu_regfix (Z_to_bv 5 19) (nfw - 0).
    assert (WRD' : wr_at asegs m (PF + 4 * (dwpl * i)) (4 * nfw)) by (apply (wr_at_sub m DR dn); [exact WRD| lia| lia| lia]).
    assert (ACD' : acc asegs m (PF + 4 * (dwpl * i)) (4 * nfw)) by (apply (acc_sub asegs m DR dn); [exact ACD| lia| lia]).
    eapply evt_cut.
    { eapply (uw_words_loop (Z.to_nat nfw) 0) with (DA := PF + 4 * (dwpl * i)) (n := nfw);
        first [ exact WRD' | exact ACD' | exact MI | lia | clear - PF4; Z.div_mod_to_equations; lia ]. }
    intros ms' PO. unfold uw_words_exit in PO.
    destruct PO as (w3 & w4 & w5 & m1 & -> & MU1 & WM1 & MI1).
    replace (Z_to_bv 64 (nfw - 0)) with (Z_to_bv 64 nfw) by (f_equal; lia).
    assert (OUT1 : PF + 4 * (dwpl * i) + 4 * nfw <= 0x7fff8000 \/ 0x10007fff8000 <= PF + 4 * (dwpl * i)) by lia.
    pose proof (wr_at_transport asegs _ _ DR dn WRD WM1) as WRD1.
    pose proof (Bi_ropkit.acc_munch_out _ _ _ _ DR dn MU1 OUT1 ltac:(lia) ltac:(lia) ACD) as ACD1.
    assert (MUW1 : munch [(DR, DR + dn)] m m1).
    { apply (munch_weaken [(PF + 4 * (dwpl * i), PF + 4 * (dwpl * i) + 4 * nfw)] [(DR, DR + dn)]); [| exact MU1].
      intros x [Hx _]. cbn [outside]. split; [lia | exact I]. }
    destruct (Z.eq_dec lwb 0) as [LZ|LNZ].
    { lstep.
      brT.
      eapply TAIL; [exact MUW1| exact WM1| exact MI1| exact WRD1| exact ACD1]. }
    assert (LB0 : (lwb =? 0) = false) by (apply Z.eqb_neq; exact LNZ).
    rewrite LB0 in RD2. cbv iota in RD2.
    assert (WRD2 : wr_at asegs m1 (PF + 4 * (dwpl * i) + 4 * nfw) 4) by (apply (wr_at_sub m1 DR dn); [exact WRD1| lia| lia| lia]).
    assert (ACD2 : acc asegs m1 (PF + 4 * (dwpl * i) + 4 * nfw) 4) by (apply (acc_sub asegs m1 DR dn); [exact ACD1| lia| lia]).
    eapply evt_cut.
    { eapply uw_part with (DW := PF + 4 * (dwpl * i) + 4 * nfw) (lwb := lwb);
        first [ exact WRD2 | exact ACD2 | exact MI1 | lia | clear - PF4; Z.div_mod_to_equations; lia ]. }
    intros ms2 PO2. unfold uw_part_exit in PO2.
    destruct PO2 as (p1 & p2 & m2 & -> & MU2 & WM2 & MI2).
    assert (OUT2 : PF + 4 * (dwpl * i) + 4 * nfw + 4 <= 0x7fff8000 \/ 0x10007fff8000 <= PF + 4 * (dwpl * i) + 4 * nfw) by lia.
    pose proof (wr_at_transport asegs _ _ DR dn WRD1 WM2) as WRD3.
    pose proof (Bi_ropkit.acc_munch_out _ _ _ _ DR dn MU2 OUT2 ltac:(lia) ltac:(lia) ACD1) as ACD3.
    assert (MUW2 : munch [(DR, DR + dn)] m1 m2).
    { apply (munch_weaken [(PF + 4 * (dwpl * i) + 4 * nfw, PF + 4 * (dwpl * i) + 4 * nfw + 4)] [(DR, DR + dn)]); [| exact MU2].
      intros x [Hx _]. cbn [outside]. split; [lia | exact I]. }
    eapply TAIL; [exact (munch_trans _ _ _ _ MUW1 MUW2)| exact (wmono_trans asegs _ _ _ WM1 WM2)| exact MI2| exact WRD3| exact ACD3].
  }
  (* Fewer than 32 bits: the last word is the only word of the row. *)
  assert (NFZ : nfw = 0) by lia.
  subst nfw.
  assert (LNZ : lwb <> 0) by lia.
  assert (LB0 : (lwb =? 0) = false) by (apply Z.eqb_neq; exact LNZ).
  rewrite LB0 in RD2. cbv iota in RD2.
  gwalk [0xb4460].
  ropu_nrm.
  ropu_regfix (Z_to_bv 5 10) (PF + 4 * (dwpl * i)).
  assert (WRD2 : wr_at asegs m (PF + 4 * (dwpl * i)) 4) by (apply (wr_at_sub m DR dn); [exact WRD| lia| lia| lia]).
  assert (ACD2 : acc asegs m (PF + 4 * (dwpl * i)) 4) by (apply (acc_sub asegs m DR dn); [exact ACD| lia| lia]).
  eapply evt_cut.
  { eapply uw_part with (DW := PF + 4 * (dwpl * i)) (lwb := lwb);
      first [ exact WRD2 | exact ACD2 | exact MI | lia | clear - PF4; Z.div_mod_to_equations; lia ]. }
  intros ms2 PO2. unfold uw_part_exit in PO2.
  destruct PO2 as (p1 & p2 & m2 & -> & MU2 & WM2 & MI2).
  assert (OUT2 : PF + 4 * (dwpl * i) + 4 <= 0x7fff8000 \/ 0x10007fff8000 <= PF + 4 * (dwpl * i)) by lia.
  pose proof (wr_at_transport asegs _ _ DR dn WRD WM2) as WRD3.
  pose proof (Bi_ropkit.acc_munch_out _ _ _ _ DR dn MU2 OUT2 ltac:(lia) ltac:(lia) ACD) as ACD3.
  assert (MUW2 : munch [(DR, DR + dn)] m m2).
  { apply (munch_weaken [(PF + 4 * (dwpl * i), PF + 4 * (dwpl * i) + 4)] [(DR, DR + dn)]); [| exact MU2].
    intros x [Hx _]. cbn [outside]. split; [lia | exact I]. }
  eapply TAIL; [exact MUW2| exact WM2| exact MI2| exact WRD3| exact ACD3].
Qed.

(* [comment removed for export] *)
Lemma uw_rows0 : forall (k : nat)
    (ra sp gp tp t2 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) F fc (m : mem) (dh dwb nfw lwb dwpl PF DR dn : Z),
  Z.of_nat k = dh -> (1 <= k)%nat -> dh <= 20000 ->
  dwb = 32 * nfw + lwb -> 0 <= nfw -> 0 <= lwb < 32 -> 0 < dwb -> dwb <= 8 * 20000 ->
  0 < dwpl <= 2^24 -> dwpl * dh <= 2^24 ->
  0 < DR -> DR mod 4 = 0 -> DR + dn <= 2^47 -> PF mod 4 = 0 ->
  (DR + dn <= 0x7fff7000 \/ 0x10007fff8000 <= DR) ->
  (forall i', 0 <= i' < dh -> DR <= PF + 4 * (dwpl * i') /\ PF + 4 * (dwpl * i') + 4 * (nfw + 1) <= DR + dn + 4 * (if lwb =? 0 then 1 else 0)) ->
  wr_at asegs m DR dn -> acc asegs m DR dn -> mem_inv asegs m ->
  evt asegs (uw_rows_exit sp gp tp s7 s8 s9 s10 s11 F fc m DR dn)
    (MS (mkR ra sp gp tp (Z_to_bv 64 lwb) (Z_to_bv 64 2147450880) t2 (Z_to_bv 64 PF) (Z_to_bv 64 5) a0 a1 (Z_to_bv 64 1) (Z_to_bv 64 dh)
             (Z_to_bv 64 dwpl) (Z_to_bv 64 dwb) (Z_to_bv 64 PF) (Z_to_bv 64 nfw) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 32))
        F (Z_to_bv 64 0xb4424) fc None m (seg_rom asegs)).
Proof.
  intros k ra sp gp tp t2 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m dh dwb nfw lwb dwpl PF DR dn
    HK HK1 HDH EDW NF0 LWB DW0 DWHI DWPL DDH D0 D4 DHI PF4 DSH RD WRD ACD MI.
  pose proof (uw_rows k 0 ra sp gp tp t2 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m dh dwb nfw lwb dwpl PF DR dn
                ltac:(lia) ltac:(lia) HK1 HDH EDW NF0 LWB DW0 DWHI DWPL DDH D0 D4 DHI PF4 DSH RD WRD ACD MI) as H.
  rewrite Z.mul_0_r in H.
  exact H.
Qed.

Section ROPUWA.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis TABR : In (167136, 132) ACC_LITS.
Hypothesis TABL : In (167328, 132) ACC_LITS.

Lemma ropu_clr_wa : rasteropUniLow_clr_case RT 0.
Proof using AF GP FKC TABR TABL.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    datad dpixw dpixh dwpl dx dy dw dh FDO MST -> -> -> -> -> -> -> -> ARGS DX0 DY0 DW0 DH0 DXW DYH DPW DPH
    DWPL DWC DNHI CH ENV RES DXMOD.
  unfold lpost, lenv, keeps, keepsL, chunk, PIX_CLR in *.
  destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct CH as (DIN & D0 & D16 & DSZ).
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_rasteropUniLow, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(datad, datad + 4 * (dwpl * dpixh))] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  pose proof ST as (STa & STb & _).
  chunk_facts RT AF GP datad (4 * (dwpl * dpixh)).
  pose proof (proj1 (Forall_forall _ _) (af_acc_lits RT AF Σ m ART0) _ TABL) as ACCL. cbn [fst snd] in ACCL.
  pose proof (proj1 (Forall_forall _ _) (af_acc_lits RT AF Σ m ART0) _ TABR) as ACCR. cbn [fst snd] in ACCR.
  refresh RT AF; unfold shad, SHB in *; park_disj.
  assert (BD : 0 <= dx /\ 0 <= dy /\ 0 < dw /\ 0 < dh /\ dx + dw <= dpixw /\ dy + dh <= dpixh /\ dpixw <= 20000 /\ dpixh <= 20000) by lia.
  hide BD.
  ropu_dedup_ro. ropu_drop_acc datad.
  unfold hid in BD.
  walk_to AF MST [(usp - 64, usp); (datad, datad + 4 * (dwpl * dpixh))] [0xb3b1c].
  rewrite ?Z.add_0_r.
  lstep;
    change 31 with (Z.ones 5); rewrite (Z.land_ones (dx * 8) 5) by lia; change (2^5) with 32.
  set (xb := (dx * 8) mod 32) in *.
  assert (XBR : 0 <= xb < 32) by (unfold xb; apply Z.mod_pos_bound; lia).
  assert (XBV : xb = 0) by (unfold xb; change 32 with (4 * 8); rewrite Z.mul_mod_distr_r by lia; rewrite DXMOD; reflexivity).
  lstep.
  brfork XB0.
  2: { exfalso. clear - XB0 XBV. lia. }
  (* The destination starts on a word boundary: the full words of each row, then its last word. *)
  lstep;
    change 31 with (Z.ones 5); rewrite (Z.land_ones (dw * 8) 5) by lia; change (2^5) with 32.
  set (lw := (dw * 8) mod 32) in *.
  assert (LWR : 0 <= lw < 32) by (unfold lw; apply Z.mod_pos_bound; lia).
  lstep.
  merge3 0xb3c50 (Z_to_bv 5 7) (Z_to_bv 5 12) (Z_to_bv 5 29).
  { brfork LW0.
    { merge_done. }
    awalk [0xb3c2c].
    lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS ?R _ _ _ _ ?mm _) =>
      destruct (ropu_lmask_bytes mm MIx) as (rbs & RB & RBL);
      destruct (bytes_at_read4w mm 0x28da0 rbs (lw * 4) RB ltac:(clear - LWR; lia) ltac:(rewrite RBL; clear - LWR; lia)) as (wm & RM) end;
      lstep; clear RM RB.
    awalk [0xb3c50]; merge_done. }
  assert (WPLB : 0 < dwpl <= 16777216).
  { assert (dwpl * 1 <= dwpl * dpixh) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
  assert (BD2 : 0 <= dy * dwpl /\ dy * dwpl + dh * dwpl <= dwpl * dpixh /\ dwpl * dpixh <= 16777216).
  { clear - BD WPLB DNHI.
    pose proof (Z.mul_nonneg_nonneg dy dwpl ltac:(lia) ltac:(lia)) as N1.
    pose proof (Z.mul_le_mono_nonneg_r (dy + dh) dpixh dwpl ltac:(lia) ltac:(lia)) as N3.
    rewrite Z.mul_add_distr_r in N3. rewrite (Z.mul_comm dpixh dwpl) in N3. lia. }
  assert (FWD : 0 <= dx * 8 / 32 <= 5000 /\ 0 <= dw * 8 / 32 <= 5000) by (clear - BD; split; split; try (apply Z.div_pos; lia); apply Z.div_le_upper_bound; lia).
  assert (DHI : datad + 4 * (dwpl * dpixh) <= 140737488355328) by lia.
  assert (NB : (0 <= dx /\ 0 <= dy /\ 0 < dw /\ 0 < dh /\ dx + dw <= dpixw /\ dy + dh <= dpixh /\ dpixw <= 20000 /\ dpixh <= 20000)
            /\ (0 <= dy * dwpl /\ dy * dwpl + dh * dwpl <= dwpl * dpixh /\ dwpl * dpixh <= 16777216) /\ 0 < dwpl <= 16777216
            /\ (0 <= dx * 8 / 32 <= 5000 /\ 0 <= dw * 8 / 32 <= 5000) /\ 0 < datad /\ datad + 4 * (dwpl * dpixh) <= 140737488355328).
  { repeat split; try (clear - BD; lia); try (clear - BD2; lia); try (clear - WPLB; lia); try (clear - FWD; lia); try assumption; lia. }
  hide NB.
  ropu_bwalk [0xb3ca8] NB.
  ropu_bwalk [0xb4424] NB.
  ropu_cnb NB.
  rewrite !(ropu_srliw5_small (dw * 8)) by (clear - NB; unfold hid in *; lia).
  set (nfw := dw * 8 / 32) in *.
  replace (Z.land datad 3) with 0
    by (symmetry; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; clear - D16; Z.div_mod_to_equations; lia).
  lazymatch goal with MUx : munch ?W ?m0 ?mm, WMx : wmono asegs ?m0 ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (ARTn : ART RT Σ mm)
      by (apply (art_client_writes RT AF Σ m0 mm lo W ART0 MUx WMx); [unfold STACK_WIN; lia|
          cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (dwpl * dpixh)); split; [exact DIN| lia]| exact I]]]);
    pose proof (af_acc_live RT AF Σ mm datad (4 * (dwpl * dpixh)) ARTn DIN) as (WRD & ACCD) end.
  assert (D4 : datad mod 4 = 0) by (clear - D16; Z.div_mod_to_equations; lia).
  assert (HD0 : lw = 0 -> dx * 8 / 32 + dw * 8 / 32 <= dwpl) by (clear - BD DWC XB0; unfold lw, xb in *; intros; Z.div_mod_to_equations; lia).
  assert (HD1 : lw <> 0 -> dx * 8 / 32 + dw * 8 / 32 + 1 <= dwpl) by (clear - BD DWC XB0; unfold lw, xb in *; intros; Z.div_mod_to_equations; lia).
  ropu_regfix (Z_to_bv 5 8) (datad + 4 * (dwpl * dy) + 4 * (dx * 8 / 32)); ropu_regfix (Z_to_bv 5 16) (datad + 4 * (dwpl * dy) + 4 * (dx * 8 / 32)).
  eapply evt_cut.
  { eapply (uw_rows0 (Z.to_nat dh)) with (DR := datad) (dn := 4 * (dwpl * dpixh)) (dwpl := dwpl) (dh := dh) (dwb := dw * 8) (nfw := nfw) (lwb := lw)
        (PF := datad + 4 * (dwpl * dy) + 4 * (dx * 8 / 32));
      first [ exact WRD | exact ACCD | assumption
            | lia
            | exact CKH
            | unfold nfw, lw; apply Z.div_mod; lia
            | unfold nfw in *; clear - D16 FWD WPLB BD2 DY0 DWPL; Z.div_mod_to_equations; lia
            | intros i' Hi';
              assert (M : dwpl * (dy + i' + 1) <= dwpl * dpixh) by (apply Z.mul_le_mono_nonneg_l; lia);
              assert (N : 0 <= dwpl * (dy + i')) by (apply Z.mul_nonneg_nonneg; lia);
              destruct (Z.eqb_spec lw 0) as [LZ|LNZ]; [pose proof (HD0 LZ) as HD| pose proof (HD1 LNZ) as HD];
              cbv iota; unfold nfw in *; split; lia ]. }
  intros ms' PO. unfold uw_rows_exit in PO.
  destruct PO as (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y20 & y21 & y22 & y23 & mE & -> & MUE & WME & MIE).
  clear ARTn ACCD.
  (* The epilogue from 0xb42bc: the frame reloads, the return, and the post-condition. *)
  loop_art RT AF Σ mE lo MUE
    ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (dwpl * dpixh)); split; [solve [in_live_tac]| lia]| exact I]]).
  lazymatch type of MUE with munch _ ?mm ?me =>
    loop_transport mm me MUE ltac:(fun Hx => clear - Hx CKR CKS CKH LOW LOR SPT SPB STa USP SP0R SP0W; unfold parked in *; lia) end.
  clear MUE WME.
  cwalk (@nil Z); cps_stop.
  agf_munch AGF MU ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; destruct Hx as [_ HxO]; cbn [outside] in HxO;
                                   clear - P HxO LOR; split; [lia| split; [tauto| exact I]]).
  apply cps_finish. intros c Hc. subst QF. cbv beta.
  eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-.
  do 2 eexists; split; [split; [unfold ret_st; do 16 eexists; reflexivity| apply fs_agree_refl]|].
  split; [split; [split; [exact ARTl| split; [exact MIE| split; [| assumption]]]| split; assumption]|];
    [ repeat match goal with H : wmono asegs _ _ |- _ => revert H end; clear; intros; eauto using wmono_trans
    | intros a Ha Ho; exact (AGF a (conj Ha Ho)) ].
Qed.
End ROPUWA.
