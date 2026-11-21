(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness ZInst ZTarget Target Driver Prog.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Startup_glue.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Layout Exit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_fprintf.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Printf_pieces F_fprintf Printf_stdio_iface Zlib_iface Driver_iface Drv_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Layout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Zh_kit Zh_stderr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Driver_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Layout OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Exit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_fprintf.F_vsnprintf OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Printf_pieces OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_fprintf OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Printf_stdio_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zlib_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Driver_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Layout.F_memcmp OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zh_stderr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Driver_iface.Zh_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.

Module Zh_deflate.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness ZInst ZTarget Target Driver Prog.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Startup_glue.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Layout Exit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Printf_stdio_iface Zlib_iface Driver_iface Drv_kit Zh_kit Zh_stderr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Driver_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Layout OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Exit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Printf_stdio_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zlib_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Driver_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zh_stderr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Driver_iface.Zh_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation usegs := Image.usegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac nm n t := first [t | fail 100 "premise" n].
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation za := the_zapi.

Section TD.
  Variable R : zreps.
  Hypothesis ZOK : zlib_ok R.
  Hypothesis CHK : @check_err_stmt PState.
  Hypothesis HFRAME : RHEAP_frame_stmt.
  Hypothesis HBR : RHEAP_block_range_stmt.

  Variables (ra sp gp tp : word) (S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Variables (LB : list block) (D C cl : Z) (d : list Z) (cp : bptr) (lo B : Z) (canary : word).
  Notation usp := (bv_unsigned sp).
  Notation SS := (usp + -152).
  Hypothesis INC : In (cp, C, cl) LB.
  Hypothesis DLEN : 1 <= zlength d <= ZH_MAX.
  Hypothesis DR : Forall (fun c => 0 <= c < 256) d.
  Hypothesis CL : cl = z_bound za (zlength d).
  Hypothesis SPB : usp <= B.
  Hypothesis B63 : B < 2^63.
  Hypothesis LOC : alloc_ceiling <= lo.
  Hypothesis LOG : GLOBALS_TOP <= lo.
  Hypothesis LOSP : lo <= usp - ZH_TEST_STACK.
  Hypothesis TP : tp = wz RATP.
  Hypothesis SP16 : usp mod 16 = 0.
  Hypothesis D0 : 0 < D.
  Hypothesis D63 : D + zlength d < 2^63.
  Hypothesis CR : rblock_range C cl.
  Hypothesis DHI : D + zlength d <= alloc_ceiling.
  Hypothesis DC : D + zlength d <= C \/ C + cl <= D.

  Lemma cl_facts : 0 < cl <= ZB_MAX.
  Proof. rewrite CL. apply (zo_bound za the_zapi_ok). exact DLEN. Qed.

  Definition FRLO (mm : mem) : Prop := exists j0 : list byte, rw_cells usegs mm (usp + -160) [CB 8 j0].
  Definition FRHI (mm : mem) : Prop := rw_cells usegs mm (usp + -40) [C8 S3; C8 S2; C8 S1; C8 S0; C8 ra].

  Section Loops.
    Variables (LBz : list block) (m0 : mem) (F : bvmap 5 word) (fc : bv 32).
    Hypothesis LBZR : forall b, In b LBz -> rblock_range (blk_addr b) (blk_size b).
    Hypothesis LBZC : forall b, In b LBz -> blk_addr b + blk_size b <= C \/ C + cl <= blk_addr b.
    Hypothesis LBZD : forall b, In b LBz -> blk_addr b + blk_size b <= D \/ D + zlength d <= blk_addr b.
    Definition W0 : list (Z * Z) :=
      [(lo, usp + -160); (SS, SS + ZS_SIZEOF); (C, C + cl)] ++ map (fun b => (blk_addr b, blk_addr b + blk_size b)) LBz.

    Definition DINV (m : mem) (ds : DS za) (ai ao : Z) (out : list Z) : Prop :=
      (exists p1 p2, rw_cells usegs m SS (zs_pub (D + d_total_in za ds) ai (d_total_in za ds) (C + d_total_out za ds) ao (d_total_out za ds) p1 p2))
      /\ zr_d R m SS LBz ds /\ u8arr usegs m C (to_bytes out) /\ zlength out = cl
      /\ bytes_at usegs m D (to_bytes d)
      /\ munch W0 m0 m /\ wmono usegs m0 m /\ mem_inv usegs m /\ stk usegs m lo (usp + -160)
      /\ 0 <= d_total_in za ds <= zlength d /\ 0 <= d_total_out za ds <= cl.
    Definition AIOK (ds : DS za) (ai : Z) : Prop := 0 <= ai <= 1 /\ d_total_in za ds + ai <= zlength d.

    Lemma outside_app : forall (W1 W2 : list (Z * Z)) x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
    Proof. induction W1 as [|[l h] W1 IH]; intros W2 x; cbn [app outside]; [tauto|]. rewrite IH. tauto. Qed.

    Lemma fp_sub : forall to n, 0 <= to -> 0 <= n -> to + n <= cl ->
      sub_fp ([(lo, usp + -160); (SS, SS + ZS_SIZEOF); (C + to, C + to + n)] ++ map (fun b => (blk_addr b, blk_addr b + blk_size b)) LBz) W0.
    Proof.
      intros to n H0 Hn H x Hx. unfold W0 in Hx. apply outside_app in Hx. destruct Hx as [Hx1 Hx2]. apply outside_app. split; [| exact Hx2].
      cbn [outside] in Hx1 |- *. lia.
    Qed.

    Lemma W0_image : forall a, 0x2b000 <= a < 0x5e000 -> outside W0 a.
    Proof.
      intros a Ha. unfold W0. apply outside_app. split.
      - cbn [outside]. unfold GLOBALS_TOP, ZH_TEST_STACK, LX_PRINTF_STACK, ZS_SIZEOF in *. destruct CR as (_ & _ & _ & _ & CI). lia.
      - clear LBZC LBZD. induction LBz as [|b L IH]; cbn [map outside]; [exact I|]. split.
        + destruct (LBZR b (or_introl eq_refl)) as (_ & _ & _ & _ & BI). lia.
        + apply IH. intros b' Hb'. apply LBZR. right. exact Hb'.
    Qed.

    Lemma fp_pub : sub_fp [(SS, SS + 48)] W0.
    Proof. intros x Hx. unfold W0 in Hx. cbn [app outside] in Hx |- *. unfold ZS_SIZEOF in Hx. split; [lia| exact I]. Qed.

    Local Definition zidle (P : Prop) : Prop := P.

    Notation TDST pc x1 s0v s1v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m :=
      (MS (mkR x1 (wz (usp + -160)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 (wz (zlength d)) (wz ZH_STATICS) S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
          F (wz pc) fc None m (seg_rom usegs)).

    Hypothesis ZLS0 : zl_statics m0.

    Lemma zls_of_inv : forall m, munch W0 m0 m -> wmono usegs m0 m -> zl_statics m.
    Proof.
      intros m MU WM. eapply zl_statics_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact ZLS0].
      intros a Ha. apply W0_image. unfold zls_addr, ZL_RELRO_LO, ZL_RELRO_HI, ZL_GOT_LO, ZL_GOT_HI, ZH_STATICS, ZL_MREPL in Ha. lia.
    Qed.

    Lemma zrd_pub : forall m m' ds, zr_d R m SS LBz ds -> munch [(SS, SS + 48)] m m' -> wmono usegs m m' -> zr_d R m' SS LBz ds.
    Proof.
      intros m m' ds ZR MU WM. eapply (zr_d_frame R); [exact ZR|]. intros a Ha Hin.
      apply (agree_on_of_munch _ _ _ MU WM a Ha). cbn [outside]. split; [| exact I].
      destruct Hin as [Hin|(b & Hb & Hr)]; [unfold ZS_PUB, ZS_SIZEOF in *; lia|].
      destruct (LBZR b Hb) as (_ & _ & _ & BC & _). unfold ZH_TEST_STACK, LX_PRINTF_STACK, ZS_PUB in *. lia.
    Qed.

    Lemma td_loop1 : forall (Q : machine_state -> Prop) (fuel : nat) (dsa : DSA za) (out : list Z) (dsa1 : DSA za) (out1 : list Z),
      dloop1 za fuel d cl dsa out = Some (dsa1, out1) ->
      (forall x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m ao, DINV m (fst dsa1) (snd dsa1) ao out1 -> AIOK (fst dsa1) (snd dsa1) ->
         evt usegs Q (TDST 0x16028 x1 (wz cl) (wz 1) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m)) ->
      forall x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m aic ao, DINV m (fst dsa) aic ao out ->
      ((aic = snd dsa /\ AIOK (fst dsa) (snd dsa)) \/ (d_total_in za (fst dsa) <> zlength d /\ d_total_out za (fst dsa) < cl)) ->
      evt usegs Q (TDST 0x15fdc x1 (wz cl) (wz 1) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m).
    Proof.
      destruct ZOK as (_ & _ & DEFL & _).
      intros Q. induction fuel as [|f IH]; intros dsa out dsa1 out1 EQ K; intros until ao; intros INV FIRST; [discriminate|].
      cbn [dloop1] in EQ. destruct dsa as [ds ai]. cbn [fst snd] in *.
      pose proof INV as ((p1 & p2 & PUB) & ZR & CARR & OLEN & DBY & MU & WM & MI & ST & TI0 & TO).
      pose proof cl_facts as CLF. unfold ZB_MAX, ZH_MAX in *.
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      pose proof CR as (C0 & _ & _ & CC & CI).
      unfold ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG.
      unfold zs_pub in PUB. cbv beta delta [MallocRep.wz] in PUB |- *.
      zstep. zstep. if_cases K1; zify_cond K1.
      {
        replace (d_total_in za ds =? zlength d) with true in EQ by (symmetry; apply Z.eqb_eq; lia). cbn [negb andb] in EQ.
        inversion EQ; subst dsa1 out1. destruct FIRST as [[-> AOK]|[NE _]]; [| exfalso; lia].
        apply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m ao); [exact INV| exact AOK]. }
      replace (d_total_in za ds =? zlength d) with false in EQ by (symmetry; apply Z.eqb_neq; lia). cbn [negb andb] in EQ.
      zstep. zstep. if_cases K2; zify_cond K2.
      { replace (d_total_out za ds <? cl) with false in EQ by (symmetry; apply Z.ltb_ge; lia).
        inversion EQ; subst dsa1 out1. destruct FIRST as [[-> AOK]|[_ LT]]; [| exfalso; lia].
        apply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m ao); [exact INV| exact AOK]. }
      replace (d_total_out za ds <? cl) with true in EQ by (symmetry; apply Z.ltb_lt; lia).
      unfold d_call in EQ. cbn [fst snd] in EQ. change (Z_NO_FLUSH =? Z_NO_FLUSH) with true in EQ. cbv iota in EQ.
      destruct (d_deflate za d ds 1 1 Z_NO_FLUSH) as [[[[ds' ai'] ao'] bs] rc] eqn:EDD.
      destruct (d_step_ok za d cl ds (ds', ai') bs) eqn:G; [|discriminate].
      destruct (rc =? Z_OK) eqn:RC; [|discriminate]. apply Z.eqb_eq in RC. subst rc.
      unfold d_step_ok in G. cbn [fst snd] in G. rewrite !andb_true_iff in G. destruct G as (((((G1 & G1') & G2) & G3) & G4) & G5).
      apply Z.leb_le in G1, G1', G2, G3, G5. apply Z.eqb_eq in G4.
      assert (BS0 : 0 <= zlength bs) by (unfold zlength; lia).
      assert (LD : Z.of_nat (length (to_bytes d)) = zlength d) by (rewrite to_bytes_len; reflexivity).
      assert (LO2 : Z.of_nat (length (to_bytes out)) = cl) by (rewrite to_bytes_len; exact OLEN).
      pose proof (munch_refl [(SS, SS + 48)] m) as MUz. pose proof (wmono_refl usegs m) as WMz.
      change (zidle (munch W0 m0 m)) in MU. change (zidle (wmono usegs m0 m)) in WM.
      zstep. zstep. zstep. zstep.
      unfold zidle in MU, WM.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m2 _) =>
        assert (ZR2 : zr_d R m2 SS LBz ds) by (eapply zrd_pub; [exact ZR| exact MUz| exact WMz]);
        assert (MU2 : munch W0 m0 m2) by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [exact fp_pub| exact MUz]);
        assert (WM2 : wmono usegs m0 m2) by (eapply wmono_trans; [exact WM| exact WMz]) end.
      clear MUz WMz MU WM.
      zstep.
      eapply evt_cut.
      { assert (SPM : (usp + -160) mod 16 = 0) by (clear - SP16; Z.div_mod_to_equations; lia).
        eapply DEFL with (S := SS) (D := D) (C := C) (cl := cl) (LBz := LBz) (d := d) (out := out) (ds := ds) (ai := 1) (ao := 1)
                         (flush := Z_NO_FLUSH) (p1 := p1) (p2 := p2) (lo := lo) (B := B);
          rewrite ?EDD; cbn [fst snd]; unfold strm_in_frame, Z_DEFLATE_STACK, ZS_SIZEOF; rewrite ?unsigned_lit by lia;
          [ nm 1 ltac:(unfold zs_pub; cbv beta delta [MallocRep.wz]; exact PUB)
          | nm 2 ltac:(exact ZR2) | nm 3 ltac:(exact DBY) | nm 4 ltac:(exact DR) | nm 5 ltac:(exact D0) | nm 6 ltac:(exact D63)
          | nm 7 ltac:(exact CARR) | nm 8 ltac:(exact OLEN) | nm 9 ltac:(lia) | nm 10 ltac:(lia) | nm 11 ltac:(lia) | nm 12 ltac:(lia) | nm 13 ltac:(lia)
          | nm 14 ltac:(left; reflexivity) | nm 141 ltac:(lia) | nm 142 ltac:(lia) | nm 1421 ltac:(exact CI) | nm 143 ltac:(exact LBZC) | nm 144 ltac:(exact LBZD) | nm 145 ltac:(exact DC)
          | nm 15 ltac:(lia)
          | nm 16 ltac:(eapply zls_of_inv; eassumption)
          | nm 17 ltac:(repeat split; try lia; clear - SP16; Z.div_mod_to_equations; lia)
          | nm 18 ltac:(exact ST) | nm 19 ltac:(exact LOC) | nm 20 ltac:(unfold GLOBALS_TOP; lia) | nm 21 ltac:(lia) | nm 22 ltac:(exact SPM)
          | nm 23 ltac:(lia) | nm 24 ltac:(exact B63) | nm 25 ltac:(exact MI)
          | nm 26 ltac:(reflexivity) | nm 27 ltac:(reflexivity) ]. }
      cbv beta. intros ms' PO. unfold deflate_post in PO. rewrite EDD in PO.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & p1' & p2' & -> & MU' & WM' & MI' & ST' & -> & PUB' & ZR' & CARR' & DBY').
      rewrite ?unsigned_lit in MU', ST' by lia.
      replace (ret_pc (Z_to_bv 64 0x16000)) with (Z_to_bv 64 0x16000) by (symmetry; rpc).
      change (wint Z_OK) with (Z_to_bv 64 0).
      zstep. if_true.
      eapply (IH (ds', ai') (zstore out (d_total_out za ds) bs) dsa1 out1 EQ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ai' ao'); cbn [fst snd].
      - unfold DINV. split; [exists p1', p2'; exact PUB'|]. split; [exact ZR'|]. split; [exact CARR'|].
        split; [rewrite zstore_length; exact OLEN|]. split; [exact DBY'|].
        split. { eapply munch_trans; [eassumption|]. eapply munch_weaken; [| exact MU']. apply fp_sub; lia. }
        split; [eapply wmono_trans; eassumption|]. split; [exact MI'|]. split; [exact ST'|]. lia.
      - left. split; [reflexivity|]. unfold AIOK. lia.
    Qed.

    Lemma td_loop2 : forall (Q : machine_state -> Prop) (fuel : nat) (dsa : DSA za) (out : list Z) (dsa2 : DSA za) (out2 : list Z),
      dloop2 za fuel d cl dsa out = Some (dsa2, out2) ->
      (forall x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m ao, DINV m (fst dsa2) (snd dsa2) ao out2 ->
         evt usegs Q (TDST 0x16048 x1 (wz 1) (wz 1) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m)) ->
      forall x1 s0v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m ao, DINV m (fst dsa) (snd dsa) ao out -> AIOK (fst dsa) (snd dsa) ->
      evt usegs Q (TDST 0x16028 x1 s0v (wz 1) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m).
    Proof.
      destruct ZOK as (_ & _ & DEFL & _).
      intros Q. induction fuel as [|f IH]; intros dsa out dsa2 out2 EQ K; intros until ao; intros INV AOK; [discriminate|].
      cbn [dloop2] in EQ. destruct dsa as [ds ai]. cbn [fst snd] in *.
      pose proof INV as ((p1 & p2 & PUB) & ZR & CARR & OLEN & DBY & MU & WM & MI & ST & TI0 & TO). destruct AOK as [AI0 TIA].
      pose proof cl_facts as CLF. unfold ZB_MAX, ZH_MAX in *.
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      pose proof CR as (C0 & _ & _ & CC & CI).
      unfold ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG.
      unfold zs_pub in PUB. cbv beta delta [MallocRep.wz] in PUB |- *.
      unfold d_call in EQ. cbn [fst snd] in EQ. change (Z_FINISH =? Z_NO_FLUSH) with false in EQ. cbv iota in EQ.
      destruct (d_deflate za d ds ai 1 Z_FINISH) as [[[[ds' ai'] ao'] bs] rc] eqn:EDD.
      destruct (d_step_ok za d cl ds (ds', ai') bs) eqn:G; [|discriminate].
      unfold d_step_ok in G. cbn [fst snd] in G. rewrite !andb_true_iff in G. destruct G as (((((G1 & G1') & G2) & G3) & G4) & G5).
      apply Z.leb_le in G1, G1', G2, G3, G5. apply Z.eqb_eq in G4.
      assert (BS0 : 0 <= zlength bs) by (unfold zlength; lia).
      assert (LD : Z.of_nat (length (to_bytes d)) = zlength d) by (rewrite to_bytes_len; reflexivity).
      assert (LO2 : Z.of_nat (length (to_bytes out)) = cl) by (rewrite to_bytes_len; exact OLEN).
      pose proof (munch_refl [(SS, SS + 48)] m) as MUz. pose proof (wmono_refl usegs m) as WMz.
      change (zidle (munch W0 m0 m)) in MU. change (zidle (wmono usegs m0 m)) in WM.
      zstep. zstep. zstep. zstep.
      unfold zidle in MU, WM.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m2 _) =>
        assert (ZR2 : zr_d R m2 SS LBz ds) by (eapply zrd_pub; [exact ZR| exact MUz| exact WMz]);
        assert (MU2 : munch W0 m0 m2) by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [exact fp_pub| exact MUz]);
        assert (WM2 : wmono usegs m0 m2) by (eapply wmono_trans; [exact WM| exact WMz]) end.
      clear MUz WMz MU WM.
      zstep.
      eapply evt_cut.
      { assert (SPM : (usp + -160) mod 16 = 0) by (clear - SP16; Z.div_mod_to_equations; lia).
        eapply DEFL with (S := SS) (D := D) (C := C) (cl := cl) (LBz := LBz) (d := d) (out := out) (ds := ds) (ai := ai) (ao := 1)
                         (flush := Z_FINISH) (p1 := p1) (p2 := p2) (lo := lo) (B := B);
          rewrite ?EDD; cbn [fst snd]; unfold strm_in_frame, Z_DEFLATE_STACK, ZS_SIZEOF; rewrite ?unsigned_lit by lia;
          [ nm 1 ltac:(unfold zs_pub; cbv beta delta [MallocRep.wz]; exact PUB)
          | nm 2 ltac:(exact ZR2) | nm 3 ltac:(exact DBY) | nm 4 ltac:(exact DR) | nm 5 ltac:(exact D0) | nm 6 ltac:(exact D63)
          | nm 7 ltac:(exact CARR) | nm 8 ltac:(exact OLEN) | nm 9 ltac:(lia) | nm 10 ltac:(lia) | nm 11 ltac:(lia) | nm 12 ltac:(lia) | nm 13 ltac:(lia)
          | nm 14 ltac:(right; reflexivity) | nm 141 ltac:(lia) | nm 142 ltac:(lia) | nm 1421 ltac:(exact CI) | nm 143 ltac:(exact LBZC) | nm 144 ltac:(exact LBZD) | nm 145 ltac:(exact DC)
          | nm 15 ltac:(lia)
          | nm 16 ltac:(eapply zls_of_inv; eassumption)
          | nm 17 ltac:(repeat split; try lia; clear - SP16; Z.div_mod_to_equations; lia)
          | nm 18 ltac:(exact ST) | nm 19 ltac:(exact LOC) | nm 20 ltac:(unfold GLOBALS_TOP; lia) | nm 21 ltac:(lia) | nm 22 ltac:(exact SPM)
          | nm 23 ltac:(lia) | nm 24 ltac:(exact B63) | nm 25 ltac:(exact MI)
          | nm 26 ltac:(reflexivity) | nm 27 ltac:(reflexivity) ]. }
      cbv beta. intros ms' PO. unfold deflate_post in PO. rewrite EDD in PO.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & p1' & p2' & -> & MU' & WM' & MI' & ST' & -> & PUB' & ZR' & CARR' & DBY').
      rewrite ?unsigned_lit in MU', ST' by lia.
      replace (ret_pc (Z_to_bv 64 0x1603c)) with (Z_to_bv 64 0x1603c) by (symmetry; rpc).
      assert (INV' : DINV m' ds' ai' ao' (zstore out (d_total_out za ds) bs)).
      { unfold DINV. split; [exists p1', p2'; exact PUB'|]. split; [exact ZR'|]. split; [exact CARR'|].
        split; [rewrite zstore_length; exact OLEN|]. split; [exact DBY'|].
        split. { eapply munch_trans; [eassumption|]. eapply munch_weaken; [| exact MU']. apply fp_sub; lia. }
        split; [eapply wmono_trans; eassumption|]. split; [exact MI'|]. split; [exact ST'|]. lia. }
      destruct (rc =? Z_STREAM_END) eqn:RC1.
      -
        apply Z.eqb_eq in RC1. subst rc. inversion EQ; subst dsa2 out2. change (wint Z_STREAM_END) with (Z_to_bv 64 1).
        zstep. if_false. zstep. zstep. if_false.
        apply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ao'). exact INV'.
      - destruct (rc =? Z_OK) eqn:RC; [|discriminate]. apply Z.eqb_eq in RC. subst rc. change (wint Z_OK) with (Z_to_bv 64 0).
        zstep. if_true.
        eapply (IH (ds', ai') (zstore out (d_total_out za ds) bs) dsa2 out2 EQ K); [exact INV'|]. unfold AIOK. cbn [fst snd]. lia.
    Qed.

    Lemma W0_high : forall a, B <= a -> outside W0 a.
    Proof.
      intros a Ha. unfold W0. apply outside_app. split.
      - cbn [outside]. unfold ZH_TEST_STACK, LX_PRINTF_STACK, ZS_SIZEOF in *. destruct CR as (_ & _ & _ & CC & _). lia.
      - clear LBZC LBZD. induction LBz as [|b L IH]; cbn [map outside]; [exact I|]. split.
        + destruct (LBZR b (or_introl eq_refl)) as (_ & _ & _ & BC & _). unfold ZH_TEST_STACK, LX_PRINTF_STACK in *. lia.
        + apply IH. intros b' Hb'. apply LBZR. right. exact Hb'.
    Qed.

    Lemma W0_stack : forall a, usp + -160 <= a -> ~ (SS <= a < SS + ZS_SIZEOF) -> outside W0 a.
    Proof.
      intros a Ha Hs. unfold W0. apply outside_app. split.
      - cbn [outside]. unfold ZH_TEST_STACK, LX_PRINTF_STACK in *. destruct CR as (_ & _ & _ & CC & _). lia.
      - clear LBZC LBZD. induction LBz as [|b L IH]; cbn [map outside]; [exact I|]. split.
        + destruct (LBZR b (or_introl eq_refl)) as (_ & _ & _ & BC & _). unfold ZH_TEST_STACK, LX_PRINTF_STACK in *. lia.
        + apply IH. intros b' Hb'. apply LBZR. right. exact Hb'.
    Qed.

    Lemma W0_heap : forall a, a < lo -> ~ (C <= a < C + cl) -> (forall b, In b LBz -> ~ (blk_addr b <= a < blk_addr b + blk_size b)) -> outside W0 a.
    Proof.
      intros a Ha Hc Hb. unfold W0. apply outside_app. split.
      - cbn [outside]. unfold ZH_TEST_STACK, LX_PRINTF_STACK, ZS_SIZEOF in *. lia.
      - clear LBZC LBZD LBZR. induction LBz as [|b L IH]; cbn [map outside]; [exact I|]. split.
        + apply Hb. left. reflexivity.
        + apply IH. intros b' Hb'. apply Hb. right. exact Hb'.
    Qed.
  End Loops.

  Hypothesis HND : RHEAP_blocks_nodup_stmt.
  Hypothesis HBD : RHEAP_blocks_disjoint_stmt.
  Hypothesis DBLK : exists bd, In bd LB /\ blk_addr bd <= D /\ D + zlength d <= blk_addr bd + blk_size bd.
  Hypothesis LBR : forall b, In b LB -> rblock_range (blk_addr b) (blk_size b).

  Notation POST s m0 := (rtest_deflate_post ra sp gp tp S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 s LB C cl lo B canary m0).

  Lemma fr_lx : forall m m' (A : Z) cs, lx_pres LB (usp + -160) [(SS, SS + ZS_SIZEOF)] m m' -> rw_cells usegs m A cs ->
    usp + -160 <= A -> (A + Z.of_nat (cells_size cs) <= SS \/ SS + ZS_SIZEOF <= A) -> rw_cells usegs m' A cs.
  Proof.
    intros m m' A cs LXP H HA HD. eapply rw_cells_agree; [exact (agree_of_lx_pres _ _ _ _ _ LXP)| exact H|].
    intros a Ha. apply stack_client; [lia|]. cbn [rin_ivs fst snd]. lia.
  Qed.

  Lemma client_inner : forall X a, lx_client LB usp X a -> lx_client LB (usp + -160) [(SS, SS + ZS_SIZEOF)] a.
  Proof.
    intros X a [_ Hc]. split.
    - cbn [rin_ivs fst snd]. intros [Hi|[]]. unfold ZS_SIZEOF in Hi. destruct Hc as [Hc|[(b & Hb & Hr)|[Hc _]]]; [lia| |].
      + destruct (LBR b Hb) as (_ & _ & _ & BC & _). unfold ZH_TEST_STACK, LX_PRINTF_STACK in *. lia.
      + unfold ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in *. lia.
    - destruct Hc as [Hc|[Hc|Hc]]; [left; lia| right; left; exact Hc| right; right; exact Hc].
  Qed.

  Lemma frame_split : forall m (j0 jp jm js jr : list byte),
    rw_cells usegs m (usp + -160) [CB 8 j0; CB 48 jp; CB 8 jm; CB 8 js; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 24 jr;
                                   C8 S3; C8 S2; C8 S1; C8 S0; C8 ra] ->
    FRLO m /\ FRHI m
    /\ exists ni ai ti no ao to p1 p2 (jmsg jstate : word),
         rw_cells usegs m SS (zs_pub ni ai ti no ao to p1 p2 ++ [C8 jmsg; C8 jstate; C8 (wz 0); C8 (wz 0); C8 (wz 0); CB 24 jr]).
  Proof.
    intros m j0 jp jm js jr FR.
    apply (proj1 (rw_cells_app usegs _ _ [_] _)) in FR. destruct FR as [FRL FR].
    apply (proj1 (rw_cells_app usegs _ _ [_;_;_;_;_;_;_] _)) in FR. destruct FR as [FRS FRH].
    cbn [cells_size csize Nat.add] in FRS, FRH.
    replace (usp + -160 + Z.of_nat 8) with SS in FRS, FRH by lia. replace (SS + Z.of_nat 112) with (usp + -40) in FRH by lia.
    split; [exists j0; exact FRL|]. split; [exact FRH|].
    pose proof FRS as [[WFS _] _]. cbn [cells_wf cell_wf] in WFS. destruct WFS as (L1 & L2 & L3 & _ & _ & _ & L4 & _).
    destruct (zs_pub_of_bytes _ L1) as (ni & ai & ti & no & ao & to & p1 & p2 & EB & WFP & _).
    destruct (le8_of_bytes _ L2) as (zmsg & _ & Emsg). destruct (le8_of_bytes _ L3) as (zst & _ & Est).
    exists ni, ai, ti, no, ao, to, p1, p2, (Z_to_bv 64 zmsg), (Z_to_bv 64 zst).
    eapply rw_cells_recast; [exact FRS| |].
    - apply cells_wf_app. split; [exact WFP|]. cbn [cells_wf cell_wf]. repeat split. exact L4.
    - rewrite cells_bytes_app, EB. cbn [cells_bytes cbytes]. rewrite Emsg, Est. reflexivity.
  Qed.

  Lemma wz_m1 : Z_to_bv 64 (-1) = wint (-1).
  Proof. unfold wint, wz. apply Z_to_bv_eqm. reflexivity. Qed.

  Lemma frame_join : forall m (j0 js : list byte), rw_cells usegs m (usp + -160) [CB 8 j0] -> rw_cells usegs m SS [CB 112 js] -> FRHI m ->
    rw_cells usegs m (usp + -160) [CB 8 j0; CB 112 js; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra].
  Proof.
    intros m j0 js FL FS FH. change [CB 8 j0; CB 112 js; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra] with ([CB 8 j0] ++ [CB 112 js] ++ [C8 S3; C8 S2; C8 S1; C8 S0; C8 ra]).
    apply (proj2 (rw_cells_app usegs _ _ _ _)). split; [exact FL|]. apply (proj2 (rw_cells_app usegs _ _ _ _)).
    cbn [cells_size csize Nat.add]. split; [eapply rw_cells_addr_eq; [exact FS| lia]| eapply rw_cells_addr_eq; [exact FH| lia]].
  Qed.

  Lemma pres_munch : forall W m m', munch W m m' -> wmono usegs m m' ->
    (forall a, usp <= a \/ (0x2b000 <= a < 0x5e000 /\ ~ stderr_addr a)
               \/ (a < lo /\ (a < 0x10000 \/ 0x5e000 <= a) /\ ~ (C <= a < C + cl) /\ exists b, In b LB /\ blk_addr b <= a < blk_addr b + blk_size b) -> outside W a) ->
    lx_pres LB usp [(C, C + cl); LXW_STDERR] m m'.
  Proof.
    intros W m m' MU WM HW. eapply lx_pres_of_munch; [exact MU| exact WM|]. intros a [HX [Ha|[(b & Hb & Hr)|[Ha _]]]]; apply HW.
    - left. exact Ha.
    - right; right. destruct (LBR b Hb) as (_ & _ & _ & BC & BI). split; [lia|]. split; [lia|]. split; [| exists b; auto].
      intros Hc. apply HX. cbn [rin_ivs fst snd]. left. exact Hc.
    - right; left. split; [exact Ha|]. intros Hs. apply HX. cbn [rin_ivs]. right; left. unfold LXW_STDERR, LX_STDERR_FILE, stderr_addr in *. cbn [fst snd]. lia.
  Qed.

  Theorem td_main : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) (s : PState) (errv : word),
    lx_env m0 s [] LB sp tp B lo errv canary -> zh_statics m0 D d -> bytes_at usegs m0 D (to_bytes d) ->
    u8arr usegs m0 C (to_bytes (zrepeat 0 cl)) -> frm0 fc ->
    implM usegs (test_deflate lops za d cl) s (POST s m0)
      (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 (wz C) (wz cl) a2 a3 a4 a5 a6 a7 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
          F (wz ZH_TEST_DEFLATE) fc None m0 (seg_rom usegs)).
  Proof.
    intros until errv. intros ENV0 ZST0 DBY0 CARR0 FRM.
    pose proof ENV0 as (HP0 & _ & _ & _ & _ & _ & _ & _ & ST0 & _ & _ & _ & _ & MI0).
    pose proof cl_facts as CLF. unfold ZB_MAX, ZH_MAX in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof CR as (C0 & C16 & _ & CC & CI).
    destruct DBLK as (bd & INBD & BD1 & BD2).
    unfold ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG.
    destruct ZOK as (_ & DINIT & _ & DEND & _).
    unfold test_deflate. cbn [bind ret lops Target.ops out_stderr unreachable].
    unfold ZH_TEST_DEFLATE. unfold zh_statics, ZH_STATICS in ZST0. cbv beta delta [MallocRep.wz] in ZST0 |- *.
    assert (LD : Z.of_nat (length (to_bytes d)) = zlength d) by (rewrite to_bytes_len; reflexivity).
    assert (LC0 : Z.of_nat (length (to_bytes (zrepeat 0 cl))) = cl) by (rewrite to_bytes_len; unfold zrepeat; rewrite repeat_length; lia).
    pose proof (munch_refl [(usp + -160, usp)] m0) as MU. pose proof (wmono_refl usegs m0) as WM.
    unfold implM. iprefix.
    zstep. carve_frame 160%nat ST0.
    apply (rw_cells_split_CB usegs _ _ [] 160 junk [] [8; 48; 8; 8; 8; 8; 8; 24; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 5 zstep. do 2 zstep. do 2 zstep. zstep. do 3 zs. do 5 zstep. zstep.
    rewrite wz_m1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    destruct (frame_split m1 _ _ _ _ _ FR) as (FRL1 & FRH1 & (ni & ai & ti & no & ao & to & p1 & p2 & jmsg & jstate & FRS1)). clear FR.
    destruct FRL1 as [j0 FRL1].
    assert (SPM : (usp + -160) mod 16 = 0) by (clear - SP16; Z.div_mod_to_equations; lia).
    assert (E160 : bv_unsigned (Z_to_bv 64 (usp + -160)) = usp + -160) by (apply unsigned_lit; lia).
    assert (ENV1 : lx_env m1 s [] LB (Z_to_bv 64 (usp + -160)) tp B lo errv canary).
    { eapply (lx_env_munch [(usp + -160, usp)] m0 m1); [exact HFRAME| exact ENV0| exact MU| exact WM| exact MI0| rewrite E160; exact ST0| rewrite E160; lia| |].
      - constructor; [left; cbn [fst]; lia| constructor].
      - intros a Ha. cbn [outside]. lia. }
    assert (PRES1 : lx_pres LB usp [(C, C + cl); LXW_STDERR] m0 m1).
    { eapply pres_munch; [exact MU| exact WM|]. intros a Ha. cbn [outside]. lia. }
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s (POST s m0) msx) end.
    eapply implM_bind.
    { eapply DINIT with (S := SS) (lo := lo) (B := B) (errv := errv) (canary := canary);
        [ exact ENV1 | exact FRS1
        | unfold strm_in_frame, ZS_SIZEOF; rewrite E160; repeat split; try lia; clear - SP16; Z.div_mod_to_equations; lia
        | rewrite E160; unfold Z_DEFLATEINIT_STACK, RMALLOC_STACK; lia | rewrite E160; exact SPM | exact FRM
        | f_equal; lia | reflexivity | reflexivity | reflexivity ]. }
    cbv beta. intros r s2 ms2 PO. unfold deflateInit_post in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & -> & PO).
    replace (ret_pc (Z_to_bv 64 0x15fc8)) with (Z_to_bv 64 0x15fc8) by (symmetry; rpc).
    destruct r as [blk|].
    2:{
      destruct PO as (((errv2 & ENV2) & FRM2 & LXP2 & ESO2 & EFA2) & -> & (js & STR2)).
      rewrite E160 in LXP2.
      pose proof ENV2 as (HP2 & (GS1 & GS2) & ZLS2 & SEW2 & SSP2 & AUX2 & _ & _ & ST2 & _ & _ & ERR2 & _ & MI2). rewrite E160 in ST2.
      pose proof (fr_lx _ _ _ _ LXP2 FRL1 ltac:(lia) ltac:(cbn; unfold ZS_SIZEOF; lia)) as FRL2.
      pose proof (fr_lx _ _ _ _ LXP2 FRH1 ltac:(lia) ltac:(cbn; unfold ZS_SIZEOF; lia)) as FRH2.
      assert (CARR2 : u8arr usegs m2 C (to_bytes (zrepeat 0 cl))).
      { eapply u8arr_agree; [exact (agree_of_lx_pres _ _ _ _ _ LXP2)| exact CARR0|]. intros a Ha.
        eapply block_client; [exact INC| cbn [blk_addr blk_size fst snd]; lia| cbn [rin_ivs fst snd]; unfold ZS_SIZEOF; lia]. }
      unfold LX_GOT_STDERR, LX_STDERR_PTR, LX_STDERR_FILE in GS1, GS2. cbv beta delta [MallocRep.wz] in GS1, GS2.
      unfold FRHI in FRH2. change (wint Z_MEM_ERROR) with (Z_to_bv 64 18446744073709551612).
      unfold implM. iprefix.
      zstep. if_true. do 10 zstep.
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s2 (POST s m0) msx) end.
      eapply implM_bind.
      { eapply (CHK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 m2 s2 lo canary 0x102bb N_deflateInit Z_MEM_ERROR);
          [ exact SEW2 | reflexivity | reflexivity | reflexivity
          | exists [105]; left; reflexivity
          | unfold Z_MEM_ERROR; lia | reflexivity
          | rewrite E160; exact ST2 | rewrite E160; unfold FPRINTF_DEPTH; lia | unfold GLOBALS_TOP; lia | rewrite E160; lia
          | exact SSP2 | exact MI2 | exact FRM2 ]. }
      cbv beta. intros [] s3 ms3 PO3.
      destruct PO3 as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & F3 & fc3 & m3 & -> & MU3 & WM3 & MI3 & FRM3 & FREG3 & ST3 & SEW3 & SSP3 & ->).
      rewrite E160 in MU3, ST3.
      replace (ret_pc (Z_to_bv 64 0x160bc)) with (Z_to_bv 64 0x160bc) by (symmetry; rpc).
      apply implM_ret.
      assert (LJS : Z.of_nat (length js) = 112) by (destruct STR2 as [[[LL _] _] _]; cbn in LL; lia).
      pose proof MU3 as MU3'. pose proof WM3 as WM3'.
      transport_after_call usegs m2 m3 MU3 WM3.
      do 7 zstep.
      pose proof (frame_join _ _ _ FRL2 STR2 FRH2) as FALL. release_frame FALL ST3 (bv_unsigned sp).
      zstep.
      apply evt_done. unfold rtest_deflate_post.
      do 15 eexists. exists F3, fc3, m3.
      split; [reflexivity|].
      split; [| split; [exact CARR2| apply zlength_zrepeat; lia]].
      unfold lx_post_env. split; [| split; [exact FRM3| split; [| split; [exact ESO2| exact EFA2]]]].
      - exists errv2. eapply (lx_env_munch_se _ m2 m3); [exact HFRAME| exact ENV2| exact MU3'| exact WM3'| exact MI3| exact ST3| exact SPB| | | exact SEW3].
        + constructor; [left; cbn [fst]; lia|]. constructor; [| constructor]. right; left. cbn [fst snd].
          unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia.
        + intros a Ha. cbn [outside]. unfold stderr_addr in Ha. lia.
      - eapply lx_pres_trans; [exact PRES1|]. eapply lx_pres_trans.
        + eapply lx_pres_sub; [exact LXP2| apply client_inner].
        + eapply pres_munch; [exact MU3'| exact WM3'|]. intros a Ha. cbn [outside]. unfold stderr_addr in Ha. lia. }
    destruct PO as (As & Aw & Ap & Ah & Ab & ((errv2 & ENV2) & FRM2 & LXP2 & ESO2 & EFA2) & -> & PUB2 & ZR2).
    rewrite E160 in LXP2.
    set (LBz := blk5_blocks blk As Aw Ap Ah Ab) in *.
    pose proof ENV2 as (HP2 & _ & ZLS2 & _ & _ & _ & _ & _ & ST2 & _ & _ & _ & _ & MI2). rewrite E160 in ST2.
    destruct (test_deflate_pure za d cl) as [comprc|] eqn:TDP; [| apply implM_unr].
    unfold test_deflate_pure in TDP.
    destruct (dloop1 za _ d cl (d_init za, 0) _) as [[dsa1 out1]|] eqn:E1; [|discriminate].
    destruct (dloop2 za _ d cl dsa1 out1) as [[dsa2 out2]|] eqn:E2; [|discriminate].
    destruct (d_end za (fst dsa2) =? Z_OK) eqn:EEND; [|discriminate]. apply Z.eqb_eq in EEND. inversion TDP; subst comprc. clear TDP.
    pose proof (fr_lx _ _ _ _ LXP2 FRL1 ltac:(lia) ltac:(cbn; unfold ZS_SIZEOF; lia)) as FRL2.
    pose proof (fr_lx _ _ _ _ LXP2 FRH1 ltac:(lia) ltac:(cbn; unfold ZS_SIZEOF; lia)) as FRH2.
    pose proof (agree_of_lx_pres _ _ _ _ _ LXP2) as AG2.
    assert (CARR2 : u8arr usegs m2 C (to_bytes (zrepeat 0 cl))).
    { eapply u8arr_agree; [exact AG2| exact CARR0|]. intros a Ha.
      eapply block_client; [exact INC| cbn [blk_addr blk_size fst snd]; lia| cbn [rin_ivs fst snd]; unfold ZS_SIZEOF; lia]. }
    assert (DBY2 : bytes_at usegs m2 D (to_bytes d)).
    { eapply bytes_at_agree; [exact AG2| exact DBY0|]. intros a Ha.
      eapply block_client; [exact INBD| lia| cbn [rin_ivs fst snd]; unfold ZS_SIZEOF; lia]. }
    assert (ZST2 : rw_cells usegs m2 250656 [C8 (Z_to_bv 64 (zlength d)); C8 (Z_to_bv 64 D)]).
    { eapply rw_cells_agree; [exact AG2| exact ZST0|]. intros a Ha. cbn in Ha. apply zls_addr_client.
      - unfold zls_addr, ZH_STATICS. lia.
      - cbn [rin_ivs fst snd]. unfold ZS_SIZEOF. lia. }
    assert (LBZR : forall b, In b LBz -> rblock_range (blk_addr b) (blk_size b)).
    { intros b Hb. apply (HBR _ _ _ _ HP2). apply in_or_app. left. exact Hb. }
    assert (LBZC : forall b, In b LBz -> blk_addr b + blk_size b <= C \/ C + cl <= blk_addr b).
    { intros b Hb. exact (heap_sep _ _ _ _ b (cp, C, cl) HND HBD HP2 Hb INC). }
    assert (LBZD : forall b, In b LBz -> blk_addr b + blk_size b <= D \/ D + zlength d <= blk_addr b).
    { intros b Hb. pose proof (heap_sep _ _ _ _ b bd HND HBD HP2 Hb INBD) as X. pose proof (LBZR b Hb) as (_ & _ & BS0 & _). lia. }
    unfold zs_pub in PUB2. cbv beta delta [MallocRep.wz] in PUB2. change (wint Z_OK) with (Z_to_bv 64 0).
    pose proof (munch_refl [(SS, SS + 48)] m2) as MUz. pose proof (wmono_refl usegs m2) as WMz.
    unfold implM. iprefix.
    zstep. if_false. zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (ZR3 : zr_d R m3 SS LBz (d_init za)) by (eapply (zrd_pub LBz LBZR); [exact ZR2| exact MUz| exact WMz]).
    assert (ZLS3 : zl_statics m3).
    { eapply zl_statics_agree; [exact (agree_on_of_munch _ _ _ MUz WMz)| | exact ZLS2]. intros a Ha. cbn [outside].
      unfold zls_addr, ZL_RELRO_LO, ZL_RELRO_HI, ZL_GOT_LO, ZL_GOT_HI, ZH_STATICS, ZL_MREPL in Ha. lia. }
    destruct (zo_dinit za the_zapi_ok) as [TI0 TO0].
    assert (INV3 : DINV LBz m3 m3 (d_init za) ai ao (zrepeat 0 cl)).
    { unfold DINV. rewrite TI0, TO0. split.
      { exists p1, p2. unfold zs_pub. cbv beta delta [MallocRep.wz]. replace (D + 0) with D by lia. replace (C + 0) with C by lia. exact PUB2. }
      split; [exact ZR3|]. split; [exact CARR2|]. split; [apply zlength_zrepeat; lia|]. split; [exact DBY2|].
      split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI2|]. split; [exact ST2|]. lia. }
    eapply td_loop1 with (LBz := LBz) (m0 := m3) (dsa := (d_init za, 0)) (aic := ai) (ao := ao);
      [exact LBZR| exact LBZC| exact LBZD| exact ZLS3| exact E1| | exact INV3| right; cbn [fst snd]; lia].
    intros x1 w0 w1 w2 e0 e1 e2 e3 e4 e5 e6 e7 w3 w4 w5 w6 m4 ao4 INV4 AOK4.
    eapply td_loop2 with (LBz := LBz) (m0 := m3) (dsa := dsa1) (ao := ao4);
      [exact LBZR| exact LBZC| exact LBZD| exact ZLS3| exact E2| | exact INV4| exact AOK4].
    clear x1 w0 w1 w2 e0 e1 e2 e3 e4 e5 e6 e7 w3 w4 w5 w6 INV4 AOK4 m4 ao4.
    intros x1 w0 w1 w2 e0 e1 e2 e3 e4 e5 e6 e7 w3 w4 w5 w6 m5 ao5 INV5.
    destruct INV5 as ((p1' & p2' & PUB5) & ZR5 & CARR5 & OLEN5 & DBY5 & MU5 & WM5 & MI5 & ST5 & _).
    assert (MU25 : munch (W0 LBz) m2 m5) by (eapply munch_trans; [eapply munch_weaken; [exact (fp_pub LBz)| exact MUz]| exact MU5]).
    assert (WM25 : wmono usegs m2 m5) by (eapply wmono_trans; eassumption).
    pose proof (agree_on_of_munch _ _ _ MU5 WM5) as AG35.
    assert (ENV5 : lx_env m5 s2 LBz LB (Z_to_bv 64 (usp + -160)) tp B lo errv2 canary).
    { eapply (lx_env_munch (W0 LBz) m2 m5); [exact HFRAME| exact ENV2| exact MU25| exact WM25| exact MI5| rewrite E160; exact ST5| rewrite E160; lia| |].
      - unfold W0. apply Forall_app. split; [| apply blocks_write_ok].
        constructor; [left; cbn [fst]; lia|]. constructor; [left; cbn [fst]; lia|]. constructor; [| constructor].
        right; right. exists (cp, C, cl). split; [apply in_or_app; right; exact INC| cbn [fst snd blk_addr blk_size]; lia].
      - intros a [Ha|Ha]; [apply (W0_high LBz m3 LBZR); exact Ha| apply (W0_image LBz m3 LBZR); exact Ha]. }
    assert (FRL5 : rw_cells usegs m5 (usp + -160) [CB 8 j0]).
    { eapply rw_cells_agree; [exact AG35| exact FRL2|]. intros a Ha. cbn in Ha. apply (W0_stack LBz m3 LBZR); unfold ZS_SIZEOF; lia. }
    assert (FRH5 : FRHI m5).
    { unfold FRHI. eapply rw_cells_agree; [exact AG35| exact FRH2|]. intros a Ha. cbn in Ha. apply (W0_stack LBz m3 LBZR); unfold ZS_SIZEOF; lia. }
    assert (PRES25 : lx_pres LB usp [(C, C + cl); LXW_STDERR] m2 m5).
    { eapply pres_munch; [exact MU25| exact WM25|]. intros a [Ha|[[Ha _]|(Ha & _ & Hc & (b & Hb & Hr))]].
      - apply (W0_stack LBz m3 LBZR); unfold ZS_SIZEOF; lia.
      - apply (W0_image LBz m3 LBZR). exact Ha.
      - apply (W0_heap LBz m3); [exact Ha| exact Hc|]. intros bz Hbz Hin.
        pose proof (heap_sep _ _ _ _ bz b HND HBD HP2 Hbz Hb). lia. }
    cbv beta delta [MallocRep.wz].
    zstep. zstep.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s2 (POST s m0) msx) end.
    eapply implM_bind.
    { eapply DEND with (S := SS) (ds := fst dsa2) (lo := lo) (B := B) (errv := errv2) (canary := canary);
        [ exact ENV5 | exact PUB5 | exact ZR5 | exact EEND
        | unfold strm_in_frame, ZS_SIZEOF; rewrite E160; repeat split; try lia; clear - SP16; Z.div_mod_to_equations; lia
        | rewrite E160; unfold Z_DEFLATEEND_STACK, RFREE_STACK; lia | rewrite E160; exact SPM | exact FRM2
        | f_equal; lia ]. }
    cbv beta. intros [] s6 ms6 PO6. unfold deflateEnd_post in PO6.
    destruct PO6 as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & F6 & fc6 & m6 & -> & ((errv6 & ENV6) & FRM6 & LXP6 & ESO6 & EFA6) & -> & (js & STR6)).
    rewrite E160 in LXP6.
    replace (ret_pc (Z_to_bv 64 0x16050)) with (Z_to_bv 64 0x16050) by (symmetry; rpc).
    pose proof ENV6 as (_ & _ & _ & _ & _ & _ & _ & _ & ST6 & _ & _ & _ & _ & MI6). rewrite E160 in ST6.
    pose proof (fr_lx _ _ _ _ LXP6 FRL5 ltac:(lia) ltac:(cbn; unfold ZS_SIZEOF; lia)) as FRL6.
    pose proof (fr_lx _ _ _ _ LXP6 FRH5 ltac:(lia) ltac:(cbn; unfold ZS_SIZEOF; lia)) as FRH6.
    assert (CARR6 : u8arr usegs m6 C (to_bytes out2)).
    { eapply u8arr_agree; [exact (agree_of_lx_pres _ _ _ _ _ LXP6)| exact CARR5|]. intros a Ha. rewrite to_bytes_len in Ha. pose proof OLEN5 as OL. unfold zlength in OL.
      eapply block_client; [exact INC| cbn [blk_addr blk_size fst snd]; lia| cbn [rin_ivs fst snd]; unfold ZS_SIZEOF; lia]. }
    apply implM_ret. change (wint Z_OK) with (Z_to_bv 64 0). unfold FRHI in FRH6.
    zstep. if_true. do 7 zstep.
    pose proof (frame_join _ _ _ FRL6 STR6 FRH6) as FALL. release_frame FALL ST6 (bv_unsigned sp).
    zstep.
    apply evt_done. unfold rtest_deflate_post.
    do 15 eexists. exists F6, fc6, m6.
    split; [reflexivity|].
    split; [| split; [exact CARR6| exact OLEN5]].
    unfold lx_post_env. split; [| split; [exact FRM6| split; [| split; [rewrite ESO6; exact ESO2| rewrite EFA6; exact EFA2]]]].
    - exists errv6. eapply lx_env_sp; [exact ENV6| exact ST6| exact SPB].
    - eapply lx_pres_trans; [exact PRES1|]. eapply lx_pres_trans; [eapply lx_pres_sub; [exact LXP2| apply client_inner]|].
      eapply lx_pres_trans; [exact PRES25|]. eapply lx_pres_sub; [exact LXP6| apply client_inner].
  Qed.
End TD.

Theorem rtest_deflate_proof : forall R : zreps, zlib_ok R -> @check_err_stmt PState ->
  RHEAP_frame_stmt -> RHEAP_block_range_stmt -> RHEAP_blocks_nodup_stmt -> RHEAP_blocks_disjoint_stmt ->
  rtest_deflate_stmt.
Proof.
  intros R ZOK CHK HFRAME HBR HND HBD. unfold rtest_deflate_stmt. intros until canary.
  intros ENV ZST POK DLEN INC CARR CL DC LOSP SP16 FRM -> ->.
  pose proof ENV as (HP & _ & _ & _ & _ & _ & SPB & B63 & _ & LOC & LOG & _ & TP & _). cbn [app] in HP.
  destruct POK as (DBY & DR & D0 & D63 & _ & PIN).
  destruct PIN as [EP|(bd & INBD & BD1 & BD2)]; [exfalso; rewrite EP in DLEN; unfold zlength in DLEN; cbn in DLEN; lia|].
  rewrite (norm8_id d DR).
  pose proof (HBR _ _ _ _ HP INC) as CR. cbn [blk_addr blk_size fst snd] in CR.
  pose proof (HBR _ _ _ _ HP INBD) as (_ & _ & _ & BDC & _).
  assert (DHI : D + zlength d <= alloc_ceiling) by lia.
  assert (DBLK : exists bd, In bd LB /\ blk_addr bd <= D /\ D + zlength d <= blk_addr bd + blk_size bd) by (exists bd; auto).
  assert (LBR : forall b, In b LB -> rblock_range (blk_addr b) (blk_size b)) by (intros b Hb; exact (HBR _ _ _ _ HP Hb)).
  eapply (td_main R) with (cp := cp) (errv := errv); eassumption.
Qed.
End WithCeiling0.
End Zh_deflate.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation usegs := Image.usegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac nm n t := first [t | fail 100 "premise" n].
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Lemma to_bytes_inj : forall a b : list Z, Forall (fun c => 0 <= c < 256) a -> Forall (fun c => 0 <= c < 256) b -> to_bytes a = to_bytes b -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] Ha Hb E; try reflexivity; try discriminate.
  inversion Ha; subst. inversion Hb; subst. unfold to_bytes in *. cbn [map] in E.
  pose proof (f_equal (fun l => hd (Z_to_bv 8 0) l) E) as E1. pose proof (f_equal (@tl _) E) as E2. cbn [hd tl] in E1, E2.
  f_equal; [| apply IH; assumption].
  apply (f_equal bv_unsigned) in E1. rewrite !Z_to_bv_unsigned in E1. unfold bv_wrap in E1. change (bv_modulus 8) with 256 in E1.
  rewrite !Z.mod_small in E1 by lia. exact E1.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation za := the_zapi.

Section TI.
  Variable R : zreps.
  Hypothesis ZOK : zlib_ok R.
  Hypothesis CHK : @check_err_stmt PState.
  Hypothesis FWR : @fwrite_diag_stmt PState.
  Hypothesis HFRAME : RHEAP_frame_stmt.
  Hypothesis HBR : RHEAP_block_range_stmt.
  Hypothesis HND : RHEAP_blocks_nodup_stmt.
  Hypothesis HBD : RHEAP_blocks_disjoint_stmt.

  Variables (ra sp gp tp : word) (S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Variables (LB : list block) (D C cl U size : Z) (d cc : list Z) (cp up : bptr) (lo B : Z) (canary : word).
  Notation usp := (bv_unsigned sp).
  Notation SS := (usp + -152).
  Hypothesis INC : In (cp, C, cl) LB.
  Hypothesis INU : In (up, U, size) LB.
  Hypothesis DLEN : 1 <= zlength d <= ZH_MAX.
  Hypothesis SIZE : size = zlength d.
  Hypothesis DR : Forall (fun c => 0 <= c < 256) d.
  Hypothesis CCR : Forall (fun c => 0 <= c < 256) cc.
  Hypothesis CCL : zlength cc = cl.
  Hypothesis CL : cl = z_bound za (zlength d).
  Hypothesis SPB : usp <= B.
  Hypothesis B63 : B < 2^63.
  Hypothesis LOC : alloc_ceiling <= lo.
  Hypothesis LOG : GLOBALS_TOP <= lo.
  Hypothesis LOSP : lo <= usp - ZH_TEST_STACK.
  Hypothesis TP : tp = wz RATP.
  Hypothesis SP16 : usp mod 16 = 0.
  Hypothesis D0 : 0 < D.
  Hypothesis D63 : D + zlength d < 2^63.
  Hypothesis CR : rblock_range C cl.
  Hypothesis UR : rblock_range U size.
  Hypothesis CU : U + size <= C \/ C + cl <= U.
  Hypothesis DU : D + zlength d <= U \/ U + size <= D.
  Hypothesis DBLK : exists bd, In bd LB /\ blk_addr bd <= D /\ D + zlength d <= blk_addr bd + blk_size bd.
  Hypothesis LBR : forall b, In b LB -> rblock_range (blk_addr b) (blk_size b).

  Lemma cl_facts : 0 < cl <= ZB_MAX.
  Proof. rewrite CL. apply (zo_bound za the_zapi_ok). exact DLEN. Qed.

  Notation XX := [(U, U + size); LXW_STDERR].

  Definition FRLO (mm : mem) : Prop := exists j0 : list byte, rw_cells usegs mm (usp + -160) [CB 8 j0].
  Definition FRHI (mm : mem) : Prop := rw_cells usegs mm (usp + -40) [C8 S3; C8 S2; C8 S1; C8 S0; C8 ra].

  Lemma client_inner : forall a u n, 0 <= u -> 0 <= n -> u + n <= size ->
    lx_client LB usp XX a -> lx_client LB (usp + -160) [(SS, SS + ZS_SIZEOF); (U + u, U + u + n)] a.
  Proof.
    intros a u n Hu Hn Hun [HX Hc]. split.
    - cbn [rin_ivs fst snd]. intros [Hi|[Hi|[]]].
      + unfold ZS_SIZEOF in Hi. destruct Hc as [Hc|[(b & Hb & Hr)|[Hc _]]]; [lia| |].
        * destruct (LBR b Hb) as (_ & _ & _ & BC & _). unfold ZH_TEST_STACK, LX_PRINTF_STACK in *. lia.
        * unfold ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in *. lia.
      + apply HX. cbn [rin_ivs fst snd]. left. lia.
    - destruct Hc as [Hc|[Hc|Hc]]; [left; lia| right; left; exact Hc| right; right; exact Hc].
  Qed.
  Lemma client_inner0 : forall a, lx_client LB usp XX a -> lx_client LB (usp + -160) [(SS, SS + ZS_SIZEOF)] a.
  Proof.
    intros a [HX Hc]. split.
    - cbn [rin_ivs fst snd]. intros [Hi|[]]. unfold ZS_SIZEOF in Hi. destruct Hc as [Hc|[(b & Hb & Hr)|[Hc _]]]; [lia| |].
      + destruct (LBR b Hb) as (_ & _ & _ & BC & _). unfold ZH_TEST_STACK, LX_PRINTF_STACK in *. lia.
      + unfold ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in *. lia.
    - destruct Hc as [Hc|[Hc|Hc]]; [left; lia| right; left; exact Hc| right; right; exact Hc].
  Qed.

  Lemma pres_munch : forall W m m', munch W m m' -> wmono usegs m m' ->
    (forall a, usp <= a \/ (0x2b000 <= a < 0x5e000 /\ ~ stderr_addr a)
               \/ (a < lo /\ (a < 0x10000 \/ 0x5e000 <= a) /\ ~ (U <= a < U + size)) -> outside W a) ->
    lx_pres LB usp XX m m'.
  Proof.
    intros W m m' MU WM HW. eapply lx_pres_of_munch; [exact MU| exact WM|]. intros a [HX [Ha|[(b & Hb & Hr)|[Ha _]]]]; apply HW.
    - left. exact Ha.
    - right; right. destruct (LBR b Hb) as (_ & _ & _ & BC & BI). split; [lia|]. split; [lia|].
      intros Hc. apply HX. cbn [rin_ivs fst snd]. left. exact Hc.
    - right; left. split; [exact Ha|]. intros Hs. apply HX. cbn [rin_ivs]. right; left. unfold LXW_STDERR, LX_STDERR_FILE, stderr_addr in *. cbn [fst snd]. lia.
  Qed.

  Section Inv.
    Variables (m0 : mem) (s0 : PState) (pst : bptr) (As : Z).

    Definition EINV (m : mem) (s : PState) (fc : bv 32) (OW : list block) : Prop :=
      (exists errv, lx_env m s OW LB (Z_to_bv 64 (usp + -160)) tp B lo errv canary)
      /\ FRLO m /\ FRHI m /\ zh_statics m D d /\ bytes_at usegs m D (to_bytes d) /\ u8arr usegs m C (to_bytes cc)
      /\ lx_pres LB usp XX m0 m /\ ps_so s = ps_so s0 /\ ps_fa s = ps_fa s0 /\ frm0 fc.

    Definition IINV (m : mem) (s : PState) (fc : bv 32) (is : IS za) (uc : list Z) (w : option bptr) (Aw : Z) : Prop :=
      EINV m s fc (iblocks w Aw pst As)
      /\ (exists p1 p2 ai ao, rw_cells usegs m SS (zs_pub (C + i_total_in za is) ai (i_total_in za is) (U + i_total_out za is) ao (i_total_out za is) p1 p2))
      /\ zr_i R m SS (iblocks w Aw pst As) is
      /\ u8arr usegs m U (to_bytes uc) /\ zlength uc = size.

    Definition IINVw (m : mem) (s : PState) (fc : bv 32) (is : IS za) (uc : list Z) (w : option bptr) (Aw : Z) : Prop :=
      EINV m s fc (iblocks w Aw pst As)
      /\ (exists ni p1 p2 ai ao, rw_cells usegs m SS (zs_pub ni ai (i_total_in za is) (U + i_total_out za is) ao (i_total_out za is) p1 p2))
      /\ zr_i R m SS (iblocks w Aw pst As) is
      /\ u8arr usegs m U (to_bytes uc) /\ zlength uc = size.
    Lemma IINV_w : forall m s fc is uc w Aw, IINV m s fc is uc w Aw -> IINVw m s fc is uc w Aw.
    Proof. intros m s fc is uc w Aw (EI & (p1 & p2 & ai & ao & PUB) & REST). split; [exact EI|]. split; [exists (C + i_total_in za is), p1, p2, ai, ao; exact PUB| exact REST]. Qed.

    Lemma wint_cases : forall rc, - 2^31 <= rc < 2^31 -> (0 <= rc /\ bv_unsigned (wint rc) = rc) \/ (rc < 0 /\ bv_unsigned (wint rc) = rc + 2^64).
    Proof.
      intros rc Hrc. unfold wint, wz. rewrite unsigned_lit by (apply Z.mod_pos_bound; lia).
      destruct (Z.lt_ge_cases rc 0) as [N|N]; [right| left]; (split; [lia|]).
      - symmetry. apply (Z.mod_unique_pos _ _ (-1)); lia.
      - apply Z.mod_small. lia.
    Qed.

    Lemma cells_lx : forall X m m' (A : Z) cs, lx_pres LB (usp + -160) X m m' -> rw_cells usegs m A cs ->
      (forall a, A <= a < A + Z.of_nat (cells_size cs) -> lx_client LB (usp + -160) X a) -> rw_cells usegs m' A cs.
    Proof. intros X m m' A cs LXP H HC. eapply rw_cells_agree; [exact (agree_of_lx_pres _ _ _ _ _ LXP)| exact H| exact HC]. Qed.

    Notation TIST pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m :=
      (MS (mkR x1 (wz (usp + -160)) gp tp t0 t1 t2 (wz U) (wz size) a0 a1 a2 a3 a4 a5 a6 a7 (wz cl) (wz 1) S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
          F (wz pc) fc None m (seg_rom usegs)).

    Ltac stackc := apply stack_client; [lia| cbn [rin_ivs fst snd]; unfold ZS_SIZEOF; lia].

    Lemma einv_step : forall m m' s s' fc fc' OW OW' u n,
      EINV m s fc OW -> 0 <= u -> 0 <= n -> u + n <= size ->
      lx_post_env m m' s s' OW' LB (Z_to_bv 64 (usp + -160)) tp B lo canary [(SS, SS + ZS_SIZEOF); (U + u, U + u + n)] fc' ->
      EINV m' s' fc' OW'.
    Proof.
      intros m m' s s' fc fc' OW OW' u n ((errv & ENV) & (j0 & FRL) & FRH & ZST & DBY & CARR & PRES & ESO & EFA & FRM) Hu Hn Hun (ENV' & FRM' & LXP & ESO' & EFA').
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      unfold ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG.
      rewrite unsigned_lit in LXP by lia.
      pose proof CR as (C0 & _ & _ & CC & CI). pose proof UR as (U0 & _ & _ & UC & UI). destruct DBLK as (bd & INBD & BD1 & BD2).
      pose proof (LBR bd INBD) as (_ & _ & _ & BDC & _).
      unfold EINV. split; [exact ENV'|].
      split. { exists j0. eapply cells_lx; [exact LXP| exact FRL|]. intros a Ha. cbn in Ha. stackc. }
      split. { unfold FRHI in *. eapply cells_lx; [exact LXP| exact FRH|]. intros a Ha. cbn in Ha. stackc. }
      split. { unfold zh_statics in *. eapply cells_lx; [exact LXP| exact ZST|]. intros a Ha. cbn in Ha. apply zls_addr_client.
               - unfold zls_addr, ZH_STATICS in *. lia.
               - cbn [rin_ivs fst snd]. unfold ZS_SIZEOF, ZH_STATICS in *. lia. }
      split. { eapply bytes_at_agree; [exact (agree_of_lx_pres _ _ _ _ _ LXP)| exact DBY|]. intros a Ha. rewrite to_bytes_len in Ha.
               eapply block_client; [exact INBD| unfold zlength in *; lia| cbn [rin_ivs fst snd]; unfold ZS_SIZEOF, zlength in *; lia]. }
      split. { eapply u8arr_agree; [exact (agree_of_lx_pres _ _ _ _ _ LXP)| exact CARR|]. intros a Ha. rewrite to_bytes_len in Ha.
               eapply block_client; [exact INC| cbn [blk_addr blk_size fst snd]; unfold zlength in *; lia| cbn [rin_ivs fst snd]; unfold ZS_SIZEOF, zlength in *; lia]. }
      split. { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_sub; [exact LXP|]. intros a Ha. apply client_inner; assumption. }
      split; [rewrite ESO'; exact ESO|]. split; [rewrite EFA'; exact EFA| exact FRM'].
    Qed.

    Lemma zri_pub : forall m m' LBz is, (forall b, In b LBz -> rblock_range (blk_addr b) (blk_size b)) ->
      zr_i R m SS LBz is -> munch [(SS, SS + 48)] m m' -> wmono usegs m m' -> zr_i R m' SS LBz is.
    Proof.
      intros m m' LBz is LBZR ZR MU WM. eapply (zr_i_frame R); [exact ZR|]. intros a Ha Hin.
      apply (agree_on_of_munch _ _ _ MU WM a Ha). cbn [outside]. split; [| exact I].
      destruct Hin as [Hin|(b & Hb & Hr)]; [unfold ZS_PUB, ZS_SIZEOF in *; lia|].
      destruct (LBZR b Hb) as (_ & _ & _ & BC & _). unfold ZH_TEST_STACK, LX_PRINTF_STACK, ZS_PUB in *. lia.
    Qed.

    Lemma ti_loop : forall (A : Type) (K : @iloop_res bptr za -> M PState A) (POSTQ : A -> PState -> machine_state -> Prop),
      (forall is uc w Aw s (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc m, IINVw m s fc is uc w Aw ->
         implM usegs (K (ILdone is uc w)) s POSTQ (TIST 0x16168 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m)) ->
      (forall rc is uc w Aw s (x1 t0 t1 t2 a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc m, IINVw m s fc is uc w Aw ->
         - 2^31 <= rc < 2^31 ->
         implM usegs (K (ILerr rc w)) s POSTQ (TIST 0x1621c x1 t0 t1 t2 (wz 1) a1 a2 (wint rc) a4 a5 a6 a7 t3 t4 t5 t6 F fc m)) ->
      forall (fuel : nat) is uc w Aw s (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc m,
      IINV m s fc is uc w Aw -> 0 <= i_total_in za is <= cl -> 0 <= i_total_out za is <= size ->
      implM usegs (mbind (iloop lops za fuel cc size cl is uc w) K) s POSTQ
            (TIST 0x16134 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m).
    Proof.
      destruct ZOK as (_ & _ & _ & _ & _ & INFL & _).
      intros A K POSTQ KDONE KERR. induction fuel as [|f IH]; intros until m; intros INV BI BO.
      { cbn [iloop unreachable lops Target.ops]. unfold implM. rewrite mbind_munr. apply impl_ret_unr. }
      cbn [iloop]. cbn [bind ret unreachable lib_malloc lops Target.ops].
      pose proof INV as (EI & (p1 & p2 & ai & ao & PUB) & ZR & UARR & ULEN).
      pose proof EI as ((errv & ENV) & (j0 & FRL) & FRH & ZST & DBY & CARR & PRES & ESO & EFA & FRM).
      pose proof ENV as (HP & _ & _ & _ & _ & _ & _ & _ & ST & _ & _ & _ & _ & MI).
      pose proof cl_facts as CLF. unfold ZB_MAX, ZH_MAX in *.
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      pose proof CR as (C0 & _ & _ & CC & CI). pose proof UR as (U0 & _ & _ & UC & UI).
      unfold ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG.
      assert (E160 : bv_unsigned (Z_to_bv 64 (usp + -160)) = usp + -160) by (apply unsigned_lit; lia). rewrite E160 in ST.
      unfold zs_pub in PUB. cbv beta delta [MallocRep.wz] in PUB |- *.
      destruct ((i_total_out za is <? size) && (i_total_in za is <? cl)) eqn:COND.
      2:{
        apply implM_ret_bind. apply andb_false_iff in COND.
        unfold implM. iprefix. zstep. zstep. if_cases K1; zify_cond K1.
        - apply evt_done. apply (KDONE is uc w Aw s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m). exact (IINV_w _ _ _ _ _ _ _ INV).
        - zstep. zstep. if_cases K2; zify_cond K2.
          + apply evt_done. apply (KDONE is uc w Aw s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m). exact (IINV_w _ _ _ _ _ _ _ INV).
          + exfalso. destruct COND as [X|X]; apply Z.ltb_ge in X; lia. }
      apply andb_true_iff in COND. destruct COND as [CO CI']. apply Z.ltb_lt in CO, CI'.
      assert (LCC : Z.of_nat (length (to_bytes cc)) = cl) by (rewrite to_bytes_len; exact CCL).
      assert (LUC : Z.of_nat (length (to_bytes uc)) = size) by (rewrite to_bytes_len; exact ULEN).
      assert (LD : Z.of_nat (length (to_bytes d)) = zlength d) by (rewrite to_bytes_len; reflexivity).
      destruct DBLK as (bd & INBD & BD1 & BD2). pose proof (LBR bd INBD) as (_ & _ & _ & BDC & _).
      pose proof (munch_refl [(SS, SS + 48)] m) as MUz. pose proof (wmono_refl usegs m) as WMz.
      unfold zh_statics, ZH_STATICS, FRHI in *. cbv beta delta [MallocRep.wz] in ZST.
      unfold implM. iprefix.
      zstep. zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
      zstep. zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
      zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
      assert (LBZR : forall b, In b (iblocks w Aw pst As) -> rblock_range (blk_addr b) (blk_size b)).
      { intros b Hb. apply (HBR _ _ _ _ HP). apply in_or_app. left. exact Hb. }
      assert (ZR2 : zr_i R m2 SS (iblocks w Aw pst As) is) by (eapply zri_pub; [exact LBZR| exact ZR| exact MUz| exact WMz]).
      assert (ENV2 : lx_env m2 s (iblocks w Aw pst As) LB (Z_to_bv 64 (usp + -160)) tp B lo errv canary).
      { eapply (lx_env_munch [(SS, SS + 48)] m m2); [exact HFRAME| exact ENV| exact MUz| exact WMz| exact MI| rewrite E160; exact ST| rewrite E160; lia| |].
        - constructor; [left; cbn [fst]; lia| constructor].
        - intros a Ha. cbn [outside]. lia. }
      assert (EI2 : EINV m2 s fc (iblocks w Aw pst As)).
      { unfold EINV, FRLO, FRHI, zh_statics, ZH_STATICS. cbv beta delta [MallocRep.wz].
        split; [exists errv; exact ENV2|]. split; [exists j0; exact FRL|]. split; [exact FRH|]. split; [exact ZST|]. split; [exact DBY|]. split; [exact CARR|].
        split. { eapply lx_pres_trans; [exact PRES|]. eapply pres_munch; [exact MUz| exact WMz|]. intros a Ha. cbn [outside]. lia. }
        split; [exact ESO|]. split; [exact EFA| exact FRM]. }
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s POSTQ msx) end.
      apply implM_bind_assoc. eapply implM_bind.
      { assert (SPM : (usp + -160) mod 16 = 0) by (clear - SP16; Z.div_mod_to_equations; lia).
        eapply INFL with (S := SS) (C := C) (U := U) (cl := cl) (size := size) (comprc := cc) (uc := uc) (is := is) (w := w) (Aw := Aw) (sp_ := pst) (As := As)
                         (p1 := p1) (p2 := p2) (lo := lo) (B := B) (errv := errv) (canary := canary);
          unfold strm_in_frame, Z_INFLATE_STACK, RMALLOC_STACK, ZS_SIZEOF; rewrite ?E160;
          [ nm 1 ltac:(exact ENV2)
          | nm 2 ltac:(unfold zs_pub; cbv beta delta [MallocRep.wz]; exact PUB)
          | nm 3 ltac:(exact ZR2)
          | nm 4 ltac:(exists (cp, C, cl); split; [exact INC| split; reflexivity])
          | nm 5 ltac:(exact CARR) | nm 6 ltac:(exact CCL) | nm 7 ltac:(exact CCR)
          | nm 8 ltac:(exists (up, U, size); split; [exact INU| split; reflexivity])
          | nm 9 ltac:(exact UARR) | nm 10 ltac:(exact ULEN) | nm 11 ltac:(lia) | nm 12 ltac:(lia) | nm 13 ltac:(exact CU)
          | nm 14 ltac:(repeat split; try lia; clear - SP16; Z.div_mod_to_equations; lia)
          | nm 15 ltac:(lia) | nm 16 ltac:(exact SPM) | nm 17 ltac:(exact FRM) | nm 18 ltac:(reflexivity) | nm 19 ltac:(reflexivity) ]. }
      cbv beta. intros r s' ms' PO. unfold inflate_post in PO.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F' & fc' & m' & p1' & p2' & Aw' & ni' & PO).
      unfold i_ok, i_window, i_wants in PO. unfold i_call.
      pose proof (zo_irc za the_zapi_ok cc is (if i_wants_window za cc is && match w with None => true | Some _ => false end
                                                then match r with Some _ => true | None => false end else true)) as RCR. unfold i_call in RCR.
      revert PO RCR.
      destruct (i_inflate za cc is 1 1 (if i_wants_window za cc is && match w with None => true | Some _ => false end
                                         then match r with Some _ => true | None => false end else true)) as [[[[is' ai'] ao'] bs] rc] eqn:EINF.
      cbn [snd]. intros (-> & LPE & AWE & -> & PUB' & NIE & ZR' & UARR') RCR.
      replace (ret_pc (Z_to_bv 64 0x16158)) with (Z_to_bv 64 0x16158) by (symmetry; rpc).
      set (w' := if i_wants_window za cc is && match w with None => true | Some _ => false end then r else w) in *.
      destruct (i_out_ok za size is bs) eqn:GO.
      2:{ unfold implM. rewrite mbind_munr. apply impl_ret_unr. }
      unfold i_out_ok in GO. apply Z.leb_le in GO. assert (BS0 : 0 <= zlength bs) by (unfold zlength; lia).
      pose proof (einv_step _ _ _ _ _ _ _ _ (i_total_out za is) (zlength bs) EI2 ltac:(lia) BS0 GO LPE) as EI'.
      assert (INV' : IINVw m' s' fc' is' (zstore uc (i_total_out za is) bs) w' Aw').
      { unfold IINVw. split; [exact EI'|]. split; [exists ni', p1', p2', ai', ao'; exact PUB'|]. split; [exact ZR'|]. split; [exact UARR'|].
        rewrite zstore_length. exact ULEN. }
      destruct (wint_cases rc RCR) as [[RC0 ERC]|[RC0 ERC]].
      - destruct (rc =? Z_STREAM_END) eqn:RC1.
        +
          apply Z.eqb_eq in RC1. apply implM_ret_bind.
          unfold implM. iprefix. cbv beta delta [MallocRep.wz].
          zstep. if_cases KB; zify_cond KB; [exfalso; unfold Z_STREAM_END in *; lia|].
          zstep. zstep. zstep. if_cases KC; zify_cond KC; [exfalso; unfold Z_STREAM_END in *; rewrite ?unsigned_lit in KC by lia; lia|].
          apply evt_done. apply (KDONE is' _ w' Aw' s' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' m'). exact INV'.
        + apply Z.eqb_neq in RC1. destruct (rc =? Z_OK) eqn:RC2.
          *
            apply Z.eqb_eq in RC2. destruct (i_next_ok za size cl is') eqn:GN.
            2:{ unfold implM. rewrite mbind_munr. apply impl_ret_unr. }
            unfold i_next_ok in GN. rewrite !andb_true_iff in GN. destruct GN as (((N1 & N2) & N3) & N4). apply Z.leb_le in N1, N2, N3, N4.
            unfold implM. iprefix. cbv beta delta [MallocRep.wz].
            zstep. if_cases KB; zify_cond KB; [| exfalso; unfold Z_OK in *; lia].
            assert (INVx : IINV m' s' fc' is' (zstore uc (i_total_out za is) bs) w' Aw').
            { unfold IINV. split; [exact EI'|]. split; [exists p1', p2', ai', ao'; rewrite <- (NIE RC2); exact PUB'|]. split; [exact ZR'|]. split; [exact UARR'|].
              rewrite zstore_length. exact ULEN. }
            apply evt_done. apply (IH is' _ w' Aw' s' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' m' INVx); lia.
          *
            apply Z.eqb_neq in RC2. apply implM_ret_bind.
            unfold implM. iprefix. cbv beta delta [MallocRep.wz].
            zstep. if_cases KB; zify_cond KB; [exfalso; unfold Z_OK in *; lia|].
            zstep. zstep. zstep. if_cases KC; zify_cond KC; [| exfalso; unfold Z_STREAM_END in *; rewrite ?unsigned_lit in KC by lia; lia].
            apply evt_done. apply (KERR rc is' _ w' Aw' s' _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' m' INV' RCR).
      -
        assert (RC1 : (rc =? Z_STREAM_END) = false) by (apply Z.eqb_neq; unfold Z_STREAM_END; lia).
        assert (RC2 : (rc =? Z_OK) = false) by (apply Z.eqb_neq; unfold Z_OK; lia).
        rewrite RC1, RC2. apply implM_ret_bind.
        unfold implM. iprefix. cbv beta delta [MallocRep.wz].
        zstep. if_cases KB; zify_cond KB; [exfalso; lia|].
        zstep. zstep. zstep. if_cases KC; zify_cond KC; [| exfalso; rewrite ?unsigned_lit in KC by lia; lia].
        apply evt_done. apply (KERR rc is' _ w' Aw' s' _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' m' INV' RCR).
    Qed.

    Lemma einv_print : forall m m' s fc fc' OW,
      EINV m s fc OW -> munch [(lo, usp + -160); (RSTDERR, RSTDERR + 232)] m m' -> wmono usegs m m' -> mem_inv usegs m' ->
      stk usegs m' lo (usp + -160) -> stderr_wfile0 m' -> frm0 fc' -> EINV m' s fc' OW.
    Proof.
      intros m m' s fc fc' OW ((errv & ENV) & (j0 & FRL) & FRH & ZST & DBY & CARR & PRES & ESO & EFA & FRM) MU WM MI' ST' SEW' FRM'.
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      unfold ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG.
      assert (E160 : bv_unsigned (Z_to_bv 64 (usp + -160)) = usp + -160) by (apply unsigned_lit; lia).
      pose proof CR as (C0 & _ & _ & CC & CI). destruct DBLK as (bd & INBD & BD1 & BD2).
      pose proof (LBR bd INBD) as (_ & _ & _ & BDC & BDI).
      pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
      unfold EINV. split.
      { exists errv. eapply (lx_env_munch_se _ m m'); [exact HFRAME| exact ENV| exact MU| exact WM| exact MI'| rewrite E160; exact ST'| rewrite E160; lia| | | exact SEW'].
        - constructor; [left; cbn [fst]; lia|]. constructor; [| constructor]. right; left. cbn [fst snd].
          unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia.
        - intros a Ha. cbn [outside]. unfold stderr_addr in Ha. lia. }
      split. { exists j0. eapply rw_cells_agree; [exact AG| exact FRL|]. intros a Ha. cbn in Ha. cbn [outside]. lia. }
      split. { unfold FRHI in *. eapply rw_cells_agree; [exact AG| exact FRH|]. intros a Ha. cbn in Ha. cbn [outside]. lia. }
      split. { unfold zh_statics, ZH_STATICS in *. eapply rw_cells_agree; [exact AG| exact ZST|]. intros a Ha. cbn in Ha. cbn [outside]. lia. }
      split. { eapply bytes_at_agree; [exact AG| exact DBY|]. intros a Ha. rewrite to_bytes_len in Ha. cbn [outside]. unfold zlength in *. lia. }
      split. { eapply u8arr_agree; [exact AG| exact CARR|]. intros a Ha. rewrite to_bytes_len in Ha. cbn [outside]. unfold zlength in *. lia. }
      split. { eapply lx_pres_trans; [exact PRES|]. eapply pres_munch; [exact MU| exact WM|]. intros a Ha. cbn [outside]. unfold stderr_addr in Ha. lia. }
      split; [exact ESO|]. split; [exact EFA| exact FRM'].
    Qed.

    Notation POST := (rtest_inflate_post ra sp gp tp S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 s0 LB U size lo B canary m0).

    Lemma ti_tail : forall s LK (x1 t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v t3 t4 t5 t6 : word) F fc m (scs : list cell),
      EINV m s fc LK -> rw_cells usegs m SS scs -> cells_size scs = 112%nat -> (length LK <= 2)%nat ->
      evt usegs (POST tt s)
        (MS (mkR x1 (wz (usp + -160)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
            F (wz 0x16190) fc None m (seg_rom usegs)).
    Proof.
      intros until scs. intros ((errv & ENV) & (j0 & FRL) & FRH & _ & _ & _ & PRES & ESO & EFA & FRM) STR SZ LKL.
      pose proof ENV as (_ & _ & _ & _ & _ & _ & _ & _ & ST & _ & _ & _ & _ & MI).
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      unfold ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG.
      assert (E160 : bv_unsigned (Z_to_bv 64 (usp + -160)) = usp + -160) by (apply unsigned_lit; lia). rewrite E160 in ST.
      unfold FRHI in FRH. cbv beta delta [MallocRep.wz].
      do 7 zstep.
      assert (FALL : rw_cells usegs m (usp + -160) ([CB 8 j0] ++ scs ++ [C8 S3; C8 S2; C8 S1; C8 S0; C8 ra])).
      { apply (proj2 (rw_cells_app usegs _ _ _ _)). split; [exact FRL|]. apply (proj2 (rw_cells_app usegs _ _ _ _)).
        cbn [cells_size csize Nat.add]. rewrite SZ. split; [eapply rw_cells_addr_eq; [exact STR| lia]| eapply rw_cells_addr_eq; [exact FRH| lia]]. }
      eapply stk_release in FALL; [| exact ST| lia]. rewrite !cells_size_app, SZ in FALL. cbn [cells_size csize Nat.add] in FALL.
      replace (usp + -160 + Z.of_nat (8 + (112 + 40))) with usp in FALL by lia.
      zstep.
      apply evt_done. unfold rtest_inflate_post.
      do 15 eexists. exists F, fc, m, LK. split; [reflexivity|]. split; [| exact LKL].
      unfold lx_post_env. split; [exists errv; eapply lx_env_sp; [exact ENV| exact FALL| exact SPB]|].
      split; [exact FRM|]. split; [exact PRES|]. split; [exact ESO| exact EFA].
    Qed.

    Lemma wint_mod32 : forall rc, - 2^31 <= rc < 2^31 -> bv_unsigned (wint rc) mod 2^32 = rc mod 2^32.
    Proof.
      intros rc Hrc. unfold wint, wz. rewrite unsigned_lit by (apply Z.mod_pos_bound; lia).
      change (2^64) with (2^32 * 2^32). rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia.
    Qed.

    Lemma stream_cells : forall m LBz is, zr_i R m SS LBz is ->
      (exists p1 p2 ni ai ti no ao to, rw_cells usegs m SS (zs_pub ni ai ti no ao to p1 p2)) ->
      exists scs, rw_cells usegs m SS scs /\ cells_size scs = 112%nat.
    Proof.
      intros m LBz is ZR (p1 & p2 & ni & ai & ti & no & ao & to & PUB). destruct (zr_i_stream R _ _ _ _ ZR) as [j PRIV].
      exists (zs_pub ni ai ti no ao to p1 p2 ++ [CB 64 j]). split; [| reflexivity].
      apply (proj2 (rw_cells_app usegs _ _ _ _)). split; [exact PUB|]. eapply rw_cells_addr_eq; [exact PRIV|]. unfold ZS_PUB. cbn. lia.
    Qed.

    Lemma ti_check : forall (An : Z) (name : list Z) (rc : Z) (pc : Z) s LK (x1 t0 t1 t2 s0v s1v a0 a1 a2 a4 a5 a6 a7 s2v s3v t3 t4 t5 t6 : word) F fc m (scs : list cell),
      harness_name An name -> - 2^31 <= rc < 2^31 ->
      EINV m s fc LK -> rw_cells usegs m SS scs -> cells_size scs = 112%nat -> (length LK <= 2)%nat ->
      (forall (Q : machine_state -> Prop) (mm : mem), lx_statics mm -> mem_inv usegs mm ->
         evt usegs Q (MS (mkR x1 (wz (usp + -160)) gp tp t0 t1 t2 s0v s1v (wz RSTDERR) (wz A_FMT_err) (wz An) (wint rc) a4 a5 a6 a7 s2v s3v S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
                         F (wz 0x16238) fc None mm (seg_rom usegs)) ->
         evt usegs Q (MS (mkR x1 (wz (usp + -160)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 (wint rc) a4 a5 a6 a7 s2v s3v S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
                         F (wz pc) fc None mm (seg_rom usegs))) ->
      implM usegs (stderr_fprintf [msg_err name rc]) s POST
        (MS (mkR x1 (wz (usp + -160)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 (wint rc) a4 a5 a6 a7 s2v s3v S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
            F (wz pc) fc None m (seg_rom usegs)).
    Proof.
      intros until scs. intros HN RCR EI STR SZ LKL LOAD.
      pose proof EI as ((errv & ENV) & _ & _ & _ & _ & _ & _ & _ & _ & FRM).
      pose proof ENV as (_ & LXS & _ & SEW & SSP & _ & _ & _ & ST & _ & _ & _ & _ & MI).
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      unfold ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG.
      assert (E160 : bv_unsigned (Z_to_bv 64 (usp + -160)) = usp + -160) by (apply unsigned_lit; lia).
      unfold implM. iprefix. eapply LOAD; [exact LXS| exact MI|]. cbv beta delta [MallocRep.wz].
      zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s POST msx) end.
      eapply (Printf_pieces.implM_post_evt usegs).
      { eapply (CHK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m s lo canary An name rc);
          [ exact SEW | reflexivity | reflexivity | reflexivity | exact HN | exact RCR | apply wint_mod32; exact RCR
          | exact ST | rewrite E160; unfold FPRINTF_DEPTH; lia | unfold GLOBALS_TOP; lia | rewrite E160; lia
          | exact SSP | exact MI | exact FRM ]. }
      cbv beta. intros [] s3 ms3 PO3.
      destruct PO3 as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & F3 & fc3 & m3 & -> & MU3 & WM3 & MI3 & FRM3 & FREG3 & ST3 & SEW3 & SSP3 & ->).
      rewrite E160 in MU3, ST3.
      replace (ret_pc (Z_to_bv 64 0x1623c)) with (Z_to_bv 64 0x1623c) by (symmetry; rpc).
      pose proof (einv_print _ _ _ _ fc3 _ EI MU3 WM3 MI3 ST3 SEW3 FRM3) as EI3.
      assert (STR3 : rw_cells usegs m3 SS scs).
      { eapply rw_cells_agree; [exact (agree_on_of_munch _ _ _ MU3 WM3)| exact STR|]. intros a Ha. rewrite SZ in Ha. cbn [outside]. lia. }
      zstep.
      eapply ti_tail; eassumption.
    Qed.

    Definition KONT (r : @iloop_res bptr za) : M PState unit :=
      match r with
      | ILerr rc w => stderr_fprintf [msg_err N_inflate rc]
      | ILdone is uc w =>
          if i_end za is =? Z_OK then
            mbind (Target.lib_free_opt raw_free w) (fun _ => mbind (Target.lib_free_opt raw_free (Some pst)) (fun _ =>
              if zlist_eqb (norm8 uc) d then mret tt else stderr_fwrite MSG_BAD_INFLATE))
          else munr
      end.

    Lemma iblocks_len : forall w Aw, (length (iblocks w Aw pst As) <= 2)%nat.
    Proof. intros [q|] Aw; cbn; lia. Qed.

    Lemma ti_err : forall rc is uc w Aw s (x1 t0 t1 t2 a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc m, IINVw m s fc is uc w Aw ->
      - 2^31 <= rc < 2^31 ->
      implM usegs (KONT (ILerr rc w)) s POST (TIST 0x1621c x1 t0 t1 t2 (wz 1) a1 a2 (wint rc) a4 a5 a6 a7 t3 t4 t5 t6 F fc m).
    Proof.
      intros until m. intros (EI & (ni & p1 & p2 & ai & ao & PUB) & ZR & _) RCR. cbn [KONT].
      destruct (stream_cells _ _ _ ZR ltac:(do 8 eexists; exact PUB)) as (scs & STR & SZ).
      eapply (ti_check 0x10561 N_inflate rc 0x1621c); try eassumption.
      - exists [105; 110; 118; 97; 108; 105; 100]. unfold harness_names. cbn [In]. do 5 right. left. reflexivity.
      - apply iblocks_len.
      - intros Q mm (GS1 & GS2) MIm KK. unfold LX_GOT_STDERR, LX_STDERR_PTR, LX_STDERR_FILE in GS1, GS2. cbv beta delta [MallocRep.wz] in GS1, GS2 |- *.
        do 7 zstep. exact KK.
    Qed.

    Definition A_BAD : Z := 0x10298.
    Lemma bad_bytes : ro_bytes_b usegs A_BAD (zb MSG_BAD_INFLATE) = true.
    Proof. vm_compute. reflexivity. Qed.

    Lemma ti_done : forall is uc w Aw s (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc m, IINVw m s fc is uc w Aw ->
      implM usegs (KONT (ILdone is uc w)) s POST (TIST 0x16168 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m).
    Proof.
      destruct ZOK as (_ & _ & _ & _ & _ & _ & IEND).
      intros until m. intros (EI & (ni & p1 & p2 & ai & ao & PUB) & ZR & UARR & ULEN). cbn [KONT].
      destruct (i_end za is =? Z_OK) eqn:EEND; [| apply implM_unr]. apply Z.eqb_eq in EEND.
      pose proof EI as ((errv & ENV) & _ & _ & _ & _ & _ & _ & _ & _ & FRM).
      pose proof ENV as (HP & _ & _ & _ & _ & _ & _ & _ & ST & _ & _ & _ & _ & MI).
      pose proof cl_facts as CLF. unfold ZB_MAX, ZH_MAX in *.
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      pose proof CR as (C0 & _ & _ & CC & CI). pose proof UR as (U0 & _ & _ & UC & UI).
      unfold ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG.
      assert (E160 : bv_unsigned (Z_to_bv 64 (usp + -160)) = usp + -160) by (apply unsigned_lit; lia).
      assert (SPM : (usp + -160) mod 16 = 0) by (clear - SP16; Z.div_mod_to_equations; lia).
      unfold implM. iprefix. cbv beta delta [MallocRep.wz].
      zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s POST msx) end.
      eapply implM_bind2.
      { eapply IEND with (S := SS) (is := is) (w := w) (Aw := Aw) (sp_ := pst) (As := As) (lo := lo) (B := B) (errv := errv) (canary := canary);
          unfold strm_in_frame, Z_INFLATEEND_STACK, RFREE_STACK, ZS_SIZEOF; rewrite ?E160;
          [ exact ENV | exact PUB | exact ZR | exact EEND
          | repeat split; try lia; clear - SP16; Z.div_mod_to_equations; lia
          | lia | exact SPM | exact FRM | reflexivity ]. }
      cbv beta. intros [] s6 ms6 PO6. unfold inflateEnd_post in PO6.
      destruct PO6 as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & F6 & fc6 & m6 & -> & ((errv6 & ENV6) & FRM6 & LXP6 & ESO6 & EFA6) & -> & (js & STR6)).
      replace (ret_pc (Z_to_bv 64 0x16170)) with (Z_to_bv 64 0x16170) by (symmetry; rpc).
      assert (LPE6 : lx_post_env m m6 s s6 [] LB (Z_to_bv 64 (usp + -160)) tp B lo canary [(SS, SS + ZS_SIZEOF); (U + 0, U + 0 + 0)] fc6).
      { split; [exists errv6; exact ENV6|]. split; [exact FRM6|]. split; [| split; [exact ESO6| exact EFA6]].
        eapply lx_pres_weaken; [exact LXP6| lia| auto|]. intros a Ha. cbn [rin_ivs] in *. tauto. }
      pose proof (einv_step _ _ _ _ _ _ _ _ 0 0 EI ltac:(lia) ltac:(lia) ltac:(lia) LPE6) as EI6.
      rewrite E160 in LXP6.
      assert (UARR6 : u8arr usegs m6 U (to_bytes uc)).
      { eapply u8arr_agree; [exact (agree_of_lx_pres _ _ _ _ _ LXP6)| exact UARR|]. intros a Ha. rewrite to_bytes_len in Ha. unfold zlength in ULEN.
        eapply block_client; [exact INU| cbn [blk_addr blk_size fst snd]; lia| cbn [rin_ivs fst snd]; unfold ZS_SIZEOF; lia]. }
      pose proof EI6 as ((errv7 & ENV7) & (j0 & FRL6) & FRH6 & ZST6 & DBY6 & CARR6 & _).
      pose proof ENV7 as (_ & (GS1 & GS2) & _ & SEW6 & SSP6 & _ & _ & _ & ST6 & _ & _ & _ & _ & MI6). rewrite E160 in ST6.
      unfold zh_statics, ZH_STATICS in ZST6. cbv beta delta [MallocRep.wz] in ZST6.
      change (wint Z_OK) with (Z_to_bv 64 0).
      assert (LJS : Z.of_nat (length js) = 112) by (destruct STR6 as [[[LL _] _] _]; cbn in LL; lia).
      assert (LUC : Z.of_nat (length (to_bytes uc)) = zlength d) by (rewrite to_bytes_len; unfold zlength in *; lia).
      assert (LD : Z.of_nat (length (to_bytes d)) = zlength d) by (rewrite to_bytes_len; reflexivity).
      unfold implM. iprefix.
      zstep. if_false. do 5 zstep. zstep.
      rewrite <- LUC.
      eapply evt_cut.
      { eapply (bcmp_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F6 fc6 m6 U D (to_bytes uc) (to_bytes d));
          [ destruct UARR6 as [X _]; exact X | exact DBY6 | rewrite !to_bytes_len; unfold zlength in *; lia
          | lia | rewrite LUC; lia | lia | rewrite LD; lia | exact MI6 ]. }
      cbv beta. intros ms7 (w0 & w1 & w2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & m7 & -> & MU7 & WM7 & MI7 & CMP).
      replace (ret_pc (Z_to_bv 64 0x1618c)) with (Z_to_bv 64 0x1618c) by (symmetry; rpc).
      assert (MU7' : munch [(lo, usp + -160); (RSTDERR, RSTDERR + 232)] m6 m7) by (eapply munch_weaken; [| exact MU7]; intros x _; exact I).
      pose proof (agree_on_of_munch _ _ _ MU7 WM7) as AG7.
      assert (ST7 : stk usegs m7 lo (usp + -160)) by (eapply stk_agree; [exact AG7| exact ST6| intros a Ha; exact I]).
      assert (SEW7 : stderr_wfile0 m7) by (eapply stderr_wfile0_agree; [exact AG7| intros a Ha; exact I| exact SEW6]).
      pose proof (einv_print _ _ _ _ fc6 _ EI6 MU7' WM7 MI7 ST7 SEW7 FRM6) as EI7.
      assert (STR7 : rw_cells usegs m7 SS [CB 112 js]) by (eapply rw_cells_agree; [exact AG7| exact STR6| intros a Ha; exact I]).
      assert (EQV : zlist_eqb (norm8 uc) d = true <-> to_bytes uc = to_bytes d).
      { rewrite zlist_eqb_eq. split; [intros <-; symmetry; apply to_bytes_norm8|].
        intros E. apply to_bytes_inj; [apply norm8_bytes| exact DR| rewrite to_bytes_norm8; exact E]. }
      destruct CMP as [[EQL ->]|[NEQ NZ]].
      -
        rewrite (proj2 EQV EQL). apply evt_done. apply implM_ret.
        zstep. if_false.
        eapply ti_tail; [exact EI7| exact STR7| reflexivity| cbn; lia].
      -
        replace (zlist_eqb (norm8 uc) d) with false by (symmetry; apply not_true_is_false; intros X; apply NEQ; apply (proj1 EQV X)).
        pose proof EI7 as ((errv8 & ENV8) & _). pose proof ENV8 as (_ & (GT1 & GT2) & _ & _ & SSP7 & _).
        unfold LX_GOT_STDERR, LX_STDERR_PTR, LX_STDERR_FILE in GT1, GT2. cbv beta delta [MallocRep.wz] in GT1, GT2.
        zstep. if_cases KB; zify_cond KB; [| exfalso; apply NZ; lia].
        do 7 zstep. zstep. apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s6 POST msx) end.
        eapply (Printf_pieces.implM_post_evt usegs).
        { eapply (FWR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F6 fc6 m7 s6 lo canary MSG_BAD_INFLATE);
            rewrite ?unsigned_lit by lia;
            [ exact SEW7
            | apply (fmt_bytes_at m7 A_BAD MSG_BAD_INFLATE MI7 bad_bytes); [unfold A_BAD; lia| vm_compute; discriminate]
            | apply forall_range_b; vm_compute; reflexivity | vm_compute; split; reflexivity
            | reflexivity | reflexivity | reflexivity
            | exact ST7 | unfold FWRITE_DEPTH; lia | unfold GLOBALS_TOP; lia
            | left; change (zlength MSG_BAD_INFLATE) with 12; lia | left; change (zlength MSG_BAD_INFLATE) with 12; lia
            | exact SSP7 | exact MI7 ]. }
        cbv beta. intros [] s8 ms8 PO8.
        destruct PO8 as (g0 & g1 & g2 & h0 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & g3 & g4 & g5 & g6 & m8 & -> & MU8 & WM8 & MI8 & ST8 & SEW8 & SSP8 & ->).
        rewrite ?unsigned_lit in MU8, ST8 by lia.
        replace (ret_pc (Z_to_bv 64 0x16218)) with (Z_to_bv 64 0x16218) by (symmetry; rpc).
        pose proof (einv_print _ _ _ _ fc6 _ EI7 MU8 WM8 MI8 ST8 SEW8 FRM6) as EI8.
        assert (STR8 : rw_cells usegs m8 SS [CB 112 js]).
        { eapply rw_cells_agree; [exact (agree_on_of_munch _ _ _ MU8 WM8)| exact STR7|]. intros a Ha. cbn in Ha. cbn [outside]. lia. }
        zstep.
        eapply ti_tail; [exact EI8| exact STR8| reflexivity| cbn; lia].
    Qed.
  End Inv.

  Lemma frame_split_i : forall m (j0 p1 jti jao p2 jto jm js jr : list byte),
    rw_cells usegs m (usp + -160) [CB 8 j0; C8 (Z_to_bv 64 C); C4 (Z_to_bv 64 0); CB 4 p1; CB 8 jti; C8 (Z_to_bv 64 U); CB 4 jao; CB 4 p2; CB 8 jto;
                                   CB 8 jm; CB 8 js; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 24 jr;
                                   C8 S3; C8 S2; C8 S1; C8 S0; C8 ra] ->
    FRLO m /\ FRHI m
    /\ exists ti ao to (jmsg jstate : word),
         rw_cells usegs m SS (zs_pub C 0 ti U ao to p1 p2 ++ [C8 jmsg; C8 jstate; C8 (wz 0); C8 (wz 0); C8 (wz 0); CB 24 jr]).
  Proof.
    intros m j0 p1 jti jao p2 jto jm js jr FR.
    apply (proj1 (rw_cells_app usegs _ _ [_] _)) in FR. destruct FR as [FRL FR].
    apply (proj1 (rw_cells_app usegs _ _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_] _)) in FR. destruct FR as [FRS FRH].
    cbn [cells_size csize Nat.add] in FRS, FRH.
    replace (usp + -160 + Z.of_nat 8) with SS in FRS, FRH by lia. replace (SS + Z.of_nat 112) with (usp + -40) in FRH by lia.
    split; [exists j0; exact FRL|]. split; [exact FRH|].
    pose proof FRS as [[WFS _] _]. cbn [cells_wf cell_wf] in WFS. destruct WFS as (_ & _ & L1 & L2 & _ & L3 & L4 & L5 & L6 & L7 & _ & _ & _ & L8 & _).
    destruct (le8_of_bytes _ L2) as (ti & _ & Eti). destruct (le4_of_bytes _ L3) as (ao & _ & Eao). destruct (le8_of_bytes _ L5) as (to & _ & Eto).
    destruct (le8_of_bytes _ L6) as (zmsg & _ & Emsg). destruct (le8_of_bytes _ L7) as (zst & _ & Est).
    exists ti, ao, to, (Z_to_bv 64 zmsg), (Z_to_bv 64 zst).
    eapply rw_cells_recast; [exact FRS| |].
    - unfold zs_pub. cbn [app cells_wf cell_wf]. repeat split; assumption.
    - unfold zs_pub, wz. cbn [app cells_bytes cbytes]. rewrite Eti, Eao, Eto, Emsg, Est. reflexivity.
  Qed.

  Theorem ti_main : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) (s : PState) (errv : word),
    lx_env m0 s [] LB sp tp B lo errv canary -> zh_statics m0 D d -> bytes_at usegs m0 D (to_bytes d) ->
    u8arr usegs m0 C (to_bytes cc) -> u8arr usegs m0 U (to_bytes (zrepeat 0 size)) -> frm0 fc ->
    implM usegs (mbind (raw_malloc (z_isize za)) (fun so => match so with
                   | None => stderr_fprintf [msg_err N_inflateInit Z_MEM_ERROR]
                   | Some pst => mbind (iloop lops za (ZI_FUEL size cl) cc size cl (i_init za) (zrepeat 0 size) None) (KONT pst)
                   end)) s
      (rtest_inflate_post ra sp gp tp S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 s LB U size lo B canary m0)
      (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 (wz C) (wz cl) (wz U) (wz size) a4 a5 a6 a7 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
          F (wz ZH_TEST_INFLATE) fc None m0 (seg_rom usegs)).
  Proof.
    intros until errv. intros ENV0 ZST0 DBY0 CARR0 UARR0 FRM.
    pose proof ENV0 as (HP0 & _ & _ & _ & _ & _ & _ & _ & ST0 & _ & _ & _ & _ & MI0).
    pose proof cl_facts as CLF. unfold ZB_MAX, ZH_MAX in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof CR as (C0 & _ & _ & CC & CI). pose proof UR as (U0 & _ & _ & UC & UI).
    destruct DBLK as (bd & INBD & BD1 & BD2). pose proof (LBR bd INBD) as (_ & _ & _ & BDC & _).
    unfold ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG.
    destruct ZOK as (_ & _ & _ & _ & IINIT & _).
    unfold ZH_TEST_INFLATE. pose proof ZST0 as ZST0'. unfold zh_statics, ZH_STATICS in ZST0. cbv beta delta [MallocRep.wz] in ZST0 |- *.
    assert (LD : Z.of_nat (length (to_bytes d)) = zlength d) by (rewrite to_bytes_len; reflexivity).
    assert (LCC : Z.of_nat (length (to_bytes cc)) = cl) by (rewrite to_bytes_len; exact CCL).
    assert (LU0 : Z.of_nat (length (to_bytes (zrepeat 0 size))) = size) by (rewrite to_bytes_len; unfold zrepeat; rewrite repeat_length; lia).
    pose proof (munch_refl [(usp + -160, usp)] m0) as MU. pose proof (wmono_refl usegs m0) as WM.
    unfold implM. iprefix.
    zstep. carve_frame 160%nat ST0.
    apply (rw_cells_split_CB usegs _ _ [] 160 junk [] [8; 8; 4; 4; 8; 8; 4; 4; 8; 8; 8; 8; 8; 8; 24; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 5 zstep. do 3 zstep. zs. zs. zs. zs. zs. zs. do 4 zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    destruct (frame_split_i m1 _ _ _ _ _ _ _ _ _ FR) as (FRL1 & FRH1 & (ti & ao & to & jmsg & jstate & FRS1)). clear FR.
    assert (SPM : (usp + -160) mod 16 = 0) by (clear - SP16; Z.div_mod_to_equations; lia).
    assert (E160 : bv_unsigned (Z_to_bv 64 (usp + -160)) = usp + -160) by (apply unsigned_lit; lia).
    assert (ENV1 : lx_env m1 s [] LB (Z_to_bv 64 (usp + -160)) tp B lo errv canary).
    { eapply (lx_env_munch [(usp + -160, usp)] m0 m1); [exact HFRAME| exact ENV0| exact MU| exact WM| exact MI0| rewrite E160; exact ST0| rewrite E160; lia| |].
      - constructor; [left; cbn [fst]; lia| constructor].
      - intros a Ha. cbn [outside]. lia. }
    assert (EI1 : EINV m0 s m1 s fc []).
    { unfold EINV, zh_statics, ZH_STATICS. cbv beta delta [MallocRep.wz].
      split; [exists errv; exact ENV1|]. split; [exact FRL1|]. split; [exact FRH1|]. split; [exact ZST0|]. split; [exact DBY0|]. split; [exact CARR0|].
      split. { eapply pres_munch; [exact MU| exact WM|]. intros a Ha. cbn [outside]. lia. }
      split; [reflexivity|]. split; [reflexivity| exact FRM]. }
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s (rtest_inflate_post ra sp gp tp S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 s LB U size lo B canary m0) msx) end.
    eapply implM_bind.
    { eapply IINIT with (S := SS) (lo := lo) (B := B) (errv := errv) (canary := canary);
        [ exact ENV1 | exact FRS1
        | unfold strm_in_frame, ZS_SIZEOF; rewrite E160; repeat split; try lia; clear - SP16; Z.div_mod_to_equations; lia
        | rewrite E160; unfold Z_INFLATEINIT_STACK, RMALLOC_STACK; lia | rewrite E160; exact SPM | exact FRM
        | f_equal; lia | reflexivity | reflexivity ]. }
    cbv beta. intros r s2 ms2 PO. unfold inflateInit_post in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & -> & PO).
    replace (ret_pc (Z_to_bv 64 0x1612c)) with (Z_to_bv 64 0x1612c) by (symmetry; rpc).
    destruct r as [pst|].
    2:{
      destruct PO as (((errv2 & ENV2) & FRM2 & LXP2 & ESO2 & EFA2) & -> & (js & STR2)).
      assert (LPE2 : lx_post_env m1 m2 s s2 [] LB (Z_to_bv 64 (usp + -160)) tp B lo canary [(SS, SS + ZS_SIZEOF); (U + 0, U + 0 + 0)] fc2).
      { split; [exists errv2; exact ENV2|]. split; [exact FRM2|]. split; [| split; [exact ESO2| exact EFA2]].
        eapply lx_pres_weaken; [exact LXP2| lia| auto|]. intros a Ha. cbn [rin_ivs] in *. tauto. }
      pose proof (einv_step _ _ _ _ _ _ _ _ _ _ 0 0 EI1 ltac:(lia) ltac:(lia) ltac:(lia) LPE2) as EI2.
      change (wint Z_MEM_ERROR) with (Z_to_bv 64 18446744073709551612).
      unfold implM. iprefix. zstep. if_true. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s2 (rtest_inflate_post ra sp gp tp S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 s LB U size lo B canary m0) msx) end.
      change (Z_to_bv 64 18446744073709551612) with (wint Z_MEM_ERROR).
      eapply (ti_check m0 s 0x102af N_inflateInit Z_MEM_ERROR 0x161b4 s2 []); try eassumption.
      - exists [100; 101; 102; 108; 97]. unfold harness_names. cbn [In]. do 4 right. left. reflexivity.
      - unfold Z_MEM_ERROR. lia.
      - reflexivity.
      - cbn. lia.
      - intros Q mm (GS1 & GS2) MIm KK. unfold LX_GOT_STDERR, LX_STDERR_PTR, LX_STDERR_FILE in GS1, GS2. cbv beta delta [MallocRep.wz] in GS1, GS2 |- *.
        do 8 zstep. exact KK. }
    destruct PO as (As & ((errv2 & ENV2) & FRM2 & LXP2 & ESO2 & EFA2) & -> & PUB2 & ZR2).
    assert (LPE2 : lx_post_env m1 m2 s s2 (iblocks None 0 pst As) LB (Z_to_bv 64 (usp + -160)) tp B lo canary [(SS, SS + ZS_SIZEOF); (U + 0, U + 0 + 0)] fc2).
    { split; [exists errv2; exact ENV2|]. split; [exact FRM2|]. split; [| split; [exact ESO2| exact EFA2]].
      eapply lx_pres_weaken; [exact LXP2| lia| auto|]. intros a Ha. cbn [rin_ivs] in *. tauto. }
    pose proof (einv_step _ _ _ _ _ _ _ _ _ _ 0 0 EI1 ltac:(lia) ltac:(lia) ltac:(lia) LPE2) as EI2.
    rewrite E160 in LXP2.
    assert (UARR2 : u8arr usegs m2 U (to_bytes (zrepeat 0 size))).
    { eapply u8arr_agree; [exact (agree_of_lx_pres _ _ _ _ _ LXP2)| exact UARR0|]. intros a Ha.
      eapply block_client; [exact INU| cbn [blk_addr blk_size fst snd]; lia| cbn [rin_ivs fst snd]; unfold ZS_SIZEOF; lia]. }
    destruct (zo_iinit za the_zapi_ok) as [TI0 TO0].
    assert (INV2 : IINV m0 s pst As m2 s2 fc2 (i_init za) (zrepeat 0 size) None 0).
    { unfold IINV. split; [exact EI2|]. split.
      { eexists. eexists. exists 0, ao. rewrite TI0, TO0. replace (C + 0) with C by lia. replace (U + 0) with U by lia. exact PUB2. }
      split; [exact ZR2|]. split; [exact UARR2| apply zlength_zrepeat; lia]. }
    change (wint Z_OK) with (Z_to_bv 64 0).
    unfold implM. iprefix. zstep. if_false. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s2 (rtest_inflate_post ra sp gp tp S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 s LB U size lo B canary m0) msx) end.
    eapply (ti_loop m0 s pst As unit (KONT pst) _ (ti_done m0 s pst As) (ti_err m0 s pst As)); [exact INV2| rewrite TI0; lia| rewrite TO0; lia].
  Qed.
End TI.

Theorem rtest_inflate_proof : forall R : zreps, zlib_ok R -> @check_err_stmt PState -> @fwrite_diag_stmt PState ->
  RHEAP_frame_stmt -> RHEAP_block_range_stmt -> RHEAP_blocks_nodup_stmt -> RHEAP_blocks_disjoint_stmt ->
  rtest_inflate_stmt.
Proof.
  intros R ZOK CHK FWR HFRAME HBR HND HBD. unfold rtest_inflate_stmt. intros until canary.
  intros ENV ZST POK DLEN SIZE INC CARR CCL CL INU UARR NE DU LOSP SP16 FRM -> -> -> ->.
  pose proof ENV as (HP & _ & _ & _ & _ & _ & SPB & B63 & _ & LOC & LOG & _ & TP & _). cbn [app] in HP.
  destruct POK as (DBY & DR & D0 & D63 & _ & PIN).
  destruct PIN as [EP|(bd & INBD & BD1 & BD2)]; [exfalso; rewrite EP in DLEN; unfold zlength in DLEN; cbn in DLEN; lia|].
  rewrite (norm8_id d DR).
  pose proof (HBR _ _ _ _ HP INC) as CR. cbn [blk_addr blk_size fst snd] in CR.
  pose proof (HBR _ _ _ _ HP INU) as UR. cbn [blk_addr blk_size fst snd] in UR.
  assert (CU : U + size <= C \/ C + cl <= U).
  { pose proof (HBD _ _ _ _ _ HP INC INU NE) as X. cbn [blk_addr blk_size fst snd] in X. lia. }
  assert (DBLK : exists bd, In bd LB /\ blk_addr bd <= D /\ D + zlength d <= blk_addr bd + blk_size bd) by (exists bd; auto).
  assert (LBR : forall b, In b LB -> rblock_range (blk_addr b) (blk_size b)) by (intros b Hb; exact (HBR _ _ _ _ HP Hb)).
  assert (CARR' : u8arr usegs m C (to_bytes (norm8 comprc))) by (rewrite to_bytes_norm8; exact CARR).
  assert (CCL' : zlength (norm8 comprc) = cl) by (rewrite norm8_length; exact CCL).
  pose proof (norm8_bytes comprc) as CCR.
  unfold test_inflate. cbn [bind ret lops Target.ops lib_malloc lib_free out_stderr out_stderr_fw unreachable].
  eapply (ti_main R) with (cp := cp) (up := up) (cc := norm8 comprc) (errv := errv); eassumption.
Qed.
End WithCeiling0.
