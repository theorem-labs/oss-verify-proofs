(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Agree Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import RunWord.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts Globals IcptA0 AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import InitStack EntrySecret.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Monad Stdio Driver Prog.
From OSSVerify.pupnp.FuzzHttp.images Require Import Asan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AsanAcct.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7 Require Import RealizeS SeamA0 A0Prog AssembleA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit GlobalsShadow Stdio_base Printf_lib F_printf_iface Stdio_iface F_printf_diag Exit RDriverA_kit RDriverA_ctx RDriverA_main RDriverA_exit RF_mainA_A.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import RDriverA_lib RF_mainA_B1.

Section B2.
  Context {HC : HasCeiling} {HG : HasGuard}.
  Variable FI : fs_if.
  Variable AI : am_if FI.
  Hypothesis AMS : forall lo hi, a0_static lo hi -> am_static FI AI lo hi.
  Variable PZ : mem -> Prop.
  Hypothesis PZ_agree : forall (P : Z -> Prop) m m', gagree_on P m m' -> (forall a, pz_band a -> P a) -> PZ m -> PZ m'.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (arg0 arg1 : list byte) (TID : Z)
            (MPAD : list byte) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : alloc_ceiling = LO sp0.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis ESF : entry_stack_fits sp0 argv envp.
  Hypothesis EARGV : argv = [arg0; arg1].
  Hypothesis HT : 0 < TID < 2^31.
  Hypothesis AC : am_contracts FI AI (JA FI AI).
  Hypothesis FPR : @fprintf_diag_stmt HC ASt.
  Hypothesis EXK : forall TID, 0 < TID < 2^31 -> exit_k_stmtA TID.
  Hypothesis FWR : @fwrite_diagA_stmt HC ASt.
  Hypothesis MCI : memcpy_i_stmt.
  Hypothesis RDF : read_front_stmt.
  Hypothesis RDB : read_back_stmt.

  Hypothesis BSR : forall s LB m b, RHEAP_A FI AI s LB m -> In b LB -> sh_readable m (blk_addr b) (blk_size b).

  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATPA).
  Notation IMGB := (build_stack_bytes rph sp0 argv envp uid hw rnd).
  Notation LO' := (LO sp0).
  Notation BASE' := (BASE_A PZ sp0 argv envp uid hw rnd TID stdout_init).
  Notation FRAME' mm := (MFRAME sp0 argv mm MPAD S7 S6 S5 S4).
  Notation RDINV' := (RDINV FI AI PZ sp0 argv envp uid hw rnd TID MPAD S4 S5 S6 S7 S8 S9 S10 S11).
  Notation RDBRK' := (RDBRK FI AI PZ sp0 argv envp uid hw rnd TID MPAD S4 S5 S6 S7 S8 S9 S10 S11).
  Notation POSTBODY' := (POSTBODY FI AI PZ sp0 argv envp uid hw rnd TID MPAD S4 S5 S6 S7 S8 S9 S10 S11).
  Local Notation K := (am_K FI AI).

  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  Notation RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 P1v len fd cap x23 t3 t4 t5 t6 F fc mm :=
    (GST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 len) (Z_to_bv 64 fd) (Z_to_bv 64 cap) (Z_to_bv 64 RSVA) (Z_to_bv 64 x23) t3 t4 t5 t6 F fc mm).

  #[using="Type"] Lemma read_clamp : forall (Q : machine_state -> Prop) x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 (len : Z) x20 (cap : Z) x22 x23 t3 t4 t5 t6
      (F : bvmap 5 word) (fc : bv 32) (mm : mem),
    0 <= len <= cap -> cap <= 2^40 ->
    evt asegs Q (GST 0x86150 x1 t0 t1 t2 x9 (Z_to_bv 64 0x10000) a1 (Z_to_bv 64 (Z.min (cap - len) 65536)) a3 a4 a5 a6 a7 x18 (Z_to_bv 64 len) x20 (Z_to_bv 64 cap) x22 x23 t3 t4 t5 t6 F fc mm) ->
    evt asegs Q (GST 0x86140 x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 len) x20 (Z_to_bv 64 cap) x22 x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until mm. intros HL HC0 H.
    zstep. zstep. zstep. if_cases K0; zify_cond K0.
    - replace (Z.min (cap - len) 65536) with (cap + - len) in H by (rewrite ?unsigned_lit in K0 by lia; lia). exact H.
    - zstep. replace (Z.min (cap - len) 65536) with 65536 in H by (rewrite ?unsigned_lit in K0 by lia; lia). exact H.
  Qed.

  #[using="Type"] Lemma len_test_step : forall (Q : machine_state -> Prop) x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 (len : Z) x20 (cap : Z) x22 x23 t3 t4 t5 t6
      (F : bvmap 5 word) (fc : bv 32) (mm : mem),
    0 <= len <= cap -> cap <= 2^40 ->
    evt asegs Q (GST (if len =? cap then 0x86108 else 0x86100) x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 len) x20 (Z_to_bv 64 cap) x22 x23 t3 t4 t5 t6 F fc mm) ->
    evt asegs Q (GST 0x860fc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 len) x20 (Z_to_bv 64 cap) x22 x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until mm. intros HL HC0 H.
    zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia;
      first [ replace (len =? cap) with true in H by (symmetry; apply Z.eqb_eq; lia); exact H
            | replace (len =? cap) with false in H by (symmetry; apply Z.eqb_neq; lia); exact H ].
  Qed.

  #[using="Type"] Lemma entry_test_step : forall (Q : machine_state -> Prop) x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 (cap : Z) x22 x23 t3 t4 t5 t6
      (F : bvmap 5 word) (fc : bv 32) (mm : mem),
    0 < cap <= 2^40 ->
    evt asegs Q (GST 0x86100 x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 (Z_to_bv 64 cap) x22 x23 t3 t4 t5 t6 F fc mm) ->
    evt asegs Q (GST 0x860dc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 (Z_to_bv 64 cap) x22 x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until mm. intros HC0 H.
    zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia; first [exact H | exfalso; lia].
  Qed.

  #[using="AMS PZ_agree arg0 VSP CEIL VARGV ESF EARGV HT FPR MCI RDF RDB BSR"] Lemma rd_read : forall (fd P1v : Z) (st1 : rd_st) (g : gst) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (x23 : Z) t3 t4 t5 t6
      (F : bvmap 5 word) (fc : bv 32) (mm : mem) (A : Z) (DATA junk : list byte) (errv : word) (kb : K),
    3 <= fd < 2^32 -> nth_error (argv_ptrs sp0 argv envp) 1 = Some (Z_to_bv 64 P1v) ->
    rd_content st1 = map bv_unsigned DATA -> BUF_A FI AI mm g kb A (rd_cap st1) DATA junk -> Z.of_nat (length DATA) < rd_cap st1 ->
    FRAME' mm -> BASE' mm -> CJ0 mm -> rw_cells asegs mm RERRNOA [C4 errv] -> frm0 fc ->
    implM asegs (rd_read_part fd (map bv_unsigned arg1) st1) stdout_init (fun r so ms => POSTBODY' fd P1v r so ms g)
      (RST 0x86140 x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 P1v (zlength (rd_content st1)) fd (rd_cap st1) x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until kb. intros FD HP1 HCT BU LT FR BA CJ ERR FRM.
    pose proof (sp_facts sp0 VSP CEIL) as SF. pose proof (IMGB_len47 sp0 argv envp uid hw rnd ESF) as IL47. pose proof alloc_ceiling_bounds as CB'. unfold LO in SF.
    assert (ERSV : RSVA = 0x5d5f50) by reflexivity.
    destruct BU as (HP0 & BLK & BSH & [CAPR CAPK] & LENR & BR1 & BR2 & BR3 & BR4).

    pose proof (BSH : boxed (rw_cells asegs mm (sh A) (shadow_cells (block_shadow (rd_cap st1))))) as BSHb. clear BSH.
    pose proof BA as (ST & MI & EX & MC & IMG & SE & SOF & RSS & SI & SZ & ENV & GSH & HPZ & CRT). unfold LO in ST.
    assert (LENZ : zlength (rd_content st1) = Z.of_nat (length DATA)) by (rewrite HCT; unfold zlength; rewrite length_map; reflexivity).
    rewrite LENZ.
    unfold rd_read_part. cbv beta zeta. rewrite LENZ. unfold READ_CHUNK.
    unfold MFRAME in FR. unfold RERRNOA in ERR.
    unfold implM. iprefix.
    eapply read_clamp; [lia| lia|].
    zstep. zstep. zstep.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM asegs tm stdout_init (fun r so ms => POSTBODY' fd P1v r so ms g) msx) end.
    set (LEN := Z.of_nat (length DATA)) in *. set (CNT := Z.min (rd_cap st1 - LEN) 65536) in *.
    assert (ELEN : LEN = Z.of_nat (length DATA)) by reflexivity. assert (ECNT : CNT = Z.min (rd_cap st1 - LEN) 65536) by reflexivity. clearbody LEN CNT. assert (LEN0 : 0 <= LEN) by lia.
    assert (CNTR : 0 < CNT <= rd_cap st1 - LEN /\ CNT <= 65536) by lia.

    destruct (stk_split asegs mm RSVA (RSVA + CNT) (RSVA + 65536) RSS ltac:(unfold RSVA; lia)) as [RSlo RShi].
    destruct (stk_carve asegs mm RSVA (RSVA + CNT) (Z.to_nat CNT) RSlo ltac:(lia)) as [_ [rsj RSC]].
    replace (RSVA + CNT - Z.of_nat (Z.to_nat CNT)) with RSVA in RSC by lia. clear RSlo.

    eapply implM_bind.
    { eapply (read_icpt RDF RDB) with (lo := usp0 - 8388608) (junk := rsj) (errv := errv); rewrite ?unsigned_lit by lia; try reflexivity;
        first [ exact ENV | exact ST | exact MI | exact ERR | unfold READI_DEPTH, A0_RT_STACK; lia | unfold RSVA in *; lia
              | replace (Z.to_nat CNT) with (Z.to_nat CNT) by reflexivity; exact RSC
              | apply (SHZ_cli sp0 argv envp uid hw rnd); [exact SZ | unfold RSVA; lia | unfold RSVA; lia | lia] ]. }
    cbv beta. intros rd s' ms' PO. unfold read_icpt_post in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MUc & WMc & MI2 & ST2 & ENV2 & RES & ->).
    transport_after_call asegs mm m2 MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x8615c)) with (Z_to_bv 64 0x8615c) by (symmetry; rpc).
    rename ST2 into ST2'.
    assert (BSH2 : boxed (rw_cells asegs m2 (sh A) (shadow_cells (block_shadow (rd_cap st1))))).
    { unfold boxed in *. eapply bshadow_transport; [lia| exact BSHb| exact MUc| exact WMc| cbn [disjoint_from]; unfold sh, SHADOW_OFF, RSVA; Z.div_mod_to_equations; lia]. }
    clear BSHb.
    assert (WOKW : Forall (WOKRA sp0) [(usp0 - 8388608, usp0 + -128); (RSVA, RSVA + Z.of_nat (Z.to_nat CNT)); (6187212, 6187212 + 4)]).
    { unfold WOKRA, WOKA, LO, RERRNOA, RSVA. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }

    assert (HP2 : HEAP FI AI m2 g [(kb, A, rd_cap st1)]).
    { destruct HP0 as (sA & stA & RH & RF & Eg). exists sA, stA. split; [| split; [| exact Eg]].
      - eapply (am_heap_frame FI AI); [exact RH| exact MUc| exact WMc|].
        repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
          first [ left; lia | right; left; exists 0x5d5f40, 0x5e5f80; split; [apply AMS; unfold a0_static; lia| unfold RSVA, a0_wsafe; lia]
                | right; left; exists 0x5e68c8, 0x5e68d0; split; [apply AMS; unfold a0_static; lia| unfold a0_wsafe; lia] ].
      - pose proof (fsb_ok FI) as FB. unfold app_mem in FB.
        eapply (rfake_frame FI); [exact RF| exact MUc| exact WMc|].
        repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; left; unfold RSVA, sh, SHADOW_OFF in *; Z.div_mod_to_equations; lia. }
    assert (CJ2 : CJ0 m2).
    { destruct CJ as [C1 C2]. split; (eapply rw_cells_transport; [eassumption| exact MUc| exact WMc| cbn [disjoint_from]; simpl_sizes; unfold RSVA; lia]). }
    destruct rd as [e|bs]; cbn [read_ret] in *.
    -
      destruct RES as (RSC2 & ERR2 & He).
      assert (RSS2 : stk asegs m2 RSVA (RSVA + 65536)).
      { eapply stk_rejoin; [exact RSC2| exact RShi| cbn [cells_size csize Nat.add]; lia| lia]. }
      assert (BA2 : BASE' m2) by (eapply (BASE_A_munchR PZ PZ_agree sp0 argv envp uid hw rnd TID VSP CEIL ESF HT stdout_init); [exact BA| exact WOKW| exact MUc| exact WMc| exact MI2| unfold LO; exact ST2'| exact RSS2| exact ENV2]).
      clear MUc WMc BA WOKW.
      pose proof BA2 as (ST3 & MI3 & EX3 & MC3 & IMG3 & SE3 & SOF3 & _). destruct MC3 as (G28 & GSE & SSP3).
      pose proof VARGV as (_ & _ & ARGLEN & NONUL & _).
      destruct (argv_cstring sp0 argv envp uid hw rnd m2 IMG3 1 arg1 ltac:(rewrite EARGV; reflexivity) ltac:(clear -SF; Z.div_mod_to_equations; lia))
        as (p1 & slack1 & HP1' & P1LO & P1HI & STR1 & SLK1). unfold str_base, struct_size, argc, envc in P1LO.
      rewrite HP1 in HP1'. assert (EP : Z_to_bv 64 P1v = Z_to_bv 64 p1) by congruence. rewrite EP. clear HP1' EP.
      assert (A1NN : ~ In (Z_to_bv 8 0) arg1) by (rewrite EARGV in NONUL; inversion NONUL as [|? ? ? X]; inversion X; assumption).
      assert (A1LEN : Z.of_nat (length arg1) <= 131071) by (rewrite EARGV in ARGLEN; inversion ARGLEN as [|? ? ? X]; inversion X; assumption).
      unfold implM. iprefix.
      replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
      zstep. if_cases K0; zify_cond K0; try (exfalso; revert K0; clear; intros K0; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM asegs tm stdout_init (fun r so ms => POSTBODY' fd P1v r so ms g) msx) end.
      cbn [io_diag ioA io_S].
      eapply (fprintf_exit PZ sp0 argv envp uid hw rnd TID S8 S9 S10 S11 VSP CEIL ESF FPR (PDReadError (map bv_unsigned arg1)));
        [| exact BA2| reflexivity| exact FRM| intros ms'' AE; apply implM_ret; apply evt_done; exact AE].
      cbn [diag_args pdiag_fmt]. split; [reflexivity|]. exists slack1. rewrite unsigned_lit by lia.
      unfold zb. rewrite zbytes_map_unsigned'. unfold zlength. rewrite !length_map.
      split; [exact STR1|]. split; [apply map_unsigned_pos; exact A1NN|]. split; [lia|].
      split; [lia|]. split; [right; lia|]. split; [unfold GLOBALS_TOP; lia|]. split; [lia|].
      destruct BA2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SZ2 & _).
      apply (SHZ_stack sp0 argv envp uid hw rnd); [exact SZ2 | lia | lia | lia | lia].
    - destruct RES as (RSC2 & ERR2 & Hbs).
      assert (RSS2 : stk asegs m2 RSVA (RSVA + 65536)).
      { eapply stk_rejoin; [exact RSC2| exact RShi| cbn [cells_size csize Nat.add]; lia| lia]. }
      assert (BA2 : BASE' m2) by (eapply (BASE_A_munchR PZ PZ_agree sp0 argv envp uid hw rnd TID VSP CEIL ESF HT stdout_init); [exact BA| exact WOKW| exact MUc| exact WMc| exact MI2| unfold LO; exact ST2'| exact RSS2| exact ENV2]).
      clear MUc WMc BA WOKW.
      pose proof BA2 as (ST3 & MI3 & EX3 & MC3 & IMG3 & SE3 & SOF3 & RSS3 & SI3 & SZ3 & ENV3 & GSH3 & HPZ3 & CRT3).
      unfold implM. iprefix.
      zstep. if_cases K0; zify_cond K0; try (exfalso; revert K0 Hbs CAPR LEN0 ECNT LENR CNTR; clear; intros; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
      zstep. zstep. if_cases K1; zify_cond K1.
      +
        assert (NPOS : length bs <> 0%nat) by (intros E; rewrite E in K1; apply K1; reflexivity).

        pose proof RSC2 as SRC. apply (proj1 (rw_cells_app _ _ _ [CB (length bs) bs] _)) in SRC. destruct SRC as [SRC _].
        pose proof (rw_cells_bytes_at _ _ _ _ SRC) as SRCB. cbn [cells_bytes cbytes app] in SRCB. rewrite app_nil_r in SRCB. clear SRC.
        pose proof BLK as BLK2. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in BLK2. destruct BLK2 as [BLK1 BLK2].
        cbn [cells_size csize Nat.add] in BLK2. replace (length DATA + 0)%nat with (length DATA) in BLK2 by lia.
        destruct (rw_cells_CB_split m2 (A + Z.of_nat (length DATA)) (Z.to_nat (rd_cap st1 - LEN)) (length bs) junk BLK2 ltac:(lia)) as [BLK2c BLK2r].
        zstep. zstep. zstep. zstep.

        destruct HP2 as (sA & stA & RH2 & RF2 & Eg2).
        eapply evt_cut.
        { eapply (memcpy_i_callq MCI (usp0 - 8388608)) with (src := bs) (junk := firstn (length bs) junk); rewrite ?unsigned_lit by lia;
            first [ exact SRCB | exact MI2 | exact ENV2 | exact ST3 | unfold RSVA in *; lia
                  | replace (A + LEN) with (A + Z.of_nat (length DATA)) by lia; replace (Z.to_nat (Z.of_nat (length bs))) with (length bs) by lia; exact BLK2c
                  | unfold A0_RT_STACK; lia | env_safe_tac | idtac ].
          -
            split; [| split; [| eapply win_ok_sub; [exact BR4| lia| lia| lia]]].
            + eapply (accessible_of_block_shadow m2 A (rd_cap st1)); [exact BSH2 | clear - BR3; Z.div_mod_to_equations; lia | lia | reflexivity | lia | lia].
            + eapply sh_readable_sub; [eapply (BSR sA _ m2 (kb, A, rd_cap st1)); [exact RH2| left; reflexivity] | cbn; lia | cbn; lia | lia].
          - apply (SHZ_cli sp0 argv envp uid hw rnd); [exact SZ3 | unfold RSVA; lia | unfold RSVA; lia | lia].
          - pose proof (@alloc_ceiling_bounds HC) as CBX; unfold icpt_rng, icpt_win, win_ok, RSVA in *; lia.
          - pose proof (@alloc_ceiling_bounds HC) as CBX; unfold icpt_rng, icpt_win, win_ok, RSVA in *; lia. }
        cbv beta. intros ms' PO.
        destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MUc & WMc & MI3' & POX).
        transport_after_call asegs m2 m3 MUc WMc.
        destruct POX as (ST4 & ENV4 & NB3 & _).
        replace (ret_pc (Z_to_bv 64 0x860f4)) with (Z_to_bv 64 0x860f4) by (symmetry; rpc).
        assert (WOKW : Forall (WOKA sp0) [(A + LEN, A + LEN + Z.of_nat (length bs)); (usp0 - 8388608, usp0 + -128)]).
        { unfold WOKA. constructor; [right; right; cbn [fst snd]; split; [lia| split; [lia| app_iv_tac]]|]. constructor; [left; cbn [fst snd]; unfold LO; lia| constructor]. }
        assert (HP3 : HEAP FI AI m3 g [(kb, A, rd_cap st1)]).
        { exists sA, stA. split; [| split; [| exact Eg2]].
          - eapply (am_heap_frame FI AI); [exact RH2| exact MUc| exact WMc|].
            apply Forall_cons; [| apply Forall_cons; [left; cbn; lia| apply Forall_nil]].
            right; right; left. exists (kb, A, rd_cap st1). split; [left; reflexivity|]. cbn. lia.
          - pose proof (fsb_ok FI) as FB. unfold app_mem in FB.
            pose proof (am_block_range FI AI _ _ _ (kb, A, rd_cap st1) RH2 ltac:(left; reflexivity)) as BRG. cbn in BRG.
            eapply (rfake_frame FI); [exact RF2| exact MUc| exact WMc|].
            repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; left; unfold sh, SHADOW_OFF in *; Z.div_mod_to_equations; lia. }
        assert (BA3 : BASE' m3) by (eapply (BASE_A_munch PZ PZ_agree sp0 argv envp uid hw rnd TID VSP CEIL ESF HT stdout_init); [exact BA2| exact WOKW| exact MUc| exact WMc| exact MI3'| unfold LO; exact ST4| exact ENV4]).
        assert (CJ3 : CJ0 m3).
        { destruct CJ2 as [C1 C2]. split; (eapply rw_cells_transport; [eassumption| exact MUc| exact WMc| cbn [disjoint_from]; simpl_sizes; lia]). }
        assert (BSH3 : rw_cells asegs m3 (sh A) (shadow_cells (block_shadow (rd_cap st1)))).
        { unfold boxed in BSH2. unfold win_ok in BR4. eapply bshadow_transport; [lia| exact BSH2| exact MUc| exact WMc| cbn [disjoint_from]; unfold sh, SHADOW_OFF in *; Z.div_mod_to_equations; lia]. }
        clear MUc WMc WOKW.

        zstep. zstep.
        assert (LEN' : zlength (rd_content st1 ++ u8s_of_bytes bs) = LEN + Z.of_nat (length bs)).
        { unfold zlength, u8s_of_bytes. rewrite length_app, length_map. unfold zlength in LENZ. lia. }
        replace (Z.of_nat (length bs) + LEN) with (LEN + Z.of_nat (length bs)) by lia.
        eapply len_test_step; [lia| lia|].
        apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM asegs tm stdout_init (fun r so ms => POSTBODY' fd P1v r so ms g) msx) end.
        replace (length bs =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; exact NPOS).
        apply implM_ret. apply evt_done. cbn [POSTBODY]. unfold RDINV, rd_pc. cbn [rd_content rd_cap rd_buf].
        rewrite LEN'.

        pose proof (rw_cells_CB_join _ _ _ _ _ _ BLK1 ltac:(replace (A + Z.of_nat (length DATA)) with (A + LEN) by lia; replace (length bs) with (Z.to_nat (Z.of_nat (length bs))) by lia; exact NB3)) as BLK1'.
        assert (BLK' : rw_cells asegs m3 A [CB (length (DATA ++ bs)) (DATA ++ bs); CB (Z.to_nat (rd_cap st1 - Z.of_nat (length (DATA ++ bs)))) (skipn (length bs) junk)]).
        { apply (proj2 (rw_cells_app _ _ _ [CB (length (DATA ++ bs)) (DATA ++ bs)] _)). rewrite length_app. split.
          - replace (length DATA + length bs)%nat with (length DATA + Z.to_nat (Z.of_nat (length bs)))%nat by lia. exact BLK1'.
          - cbn [cells_size csize Nat.add].
            replace (A + Z.of_nat (length DATA + length bs + 0)) with (A + Z.of_nat (length DATA) + Z.of_nat (length bs)) by lia.
            replace (Z.to_nat (rd_cap st1 - Z.of_nat (length DATA + length bs))) with (Z.to_nat (rd_cap st1 - LEN) - length bs)%nat by lia. exact BLK2r. }
        do 17 eexists. exists F, fc, m3, A, (DATA ++ bs), (skipn (length bs) junk), errv, kb.
        split; [reflexivity|].
        split; [rewrite HCT; unfold u8s_of_bytes; rewrite map_app; reflexivity|]. split; [reflexivity|].
        split; [| split; [exact FR| split; [exact BA3| split; [exact CJ3| split; [exact ERR2| exact FRM]]]]].
        split; [exact HP3|]. split; [exact BLK'|]. split; [exact BSH3|]. split; [split; [lia| exact CAPK]|]. split; [rewrite length_app; lia| split; [lia| split; [lia| split; [lia| exact BR4]]]].
      +
        assert (Ebs : bs = []) by (destruct bs; [reflexivity| cbn [length] in K1; exfalso; rewrite ?unsigned_lit in K1 by lia; lia]). subst bs.
        cbn [length Nat.eqb Z.of_nat]. apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM asegs tm stdout_init (fun r so ms => POSTBODY' fd P1v r so ms g) msx) end.
        apply implM_ret. apply evt_done.
        cbn [POSTBODY]. unfold RDBRK.
        do 16 eexists. exists F, fc, m2, A, (rd_cap st1), DATA, junk, errv, kb.
        split; [rewrite LENZ; reflexivity|].
        split; [exact HCT|]. split; [reflexivity|]. split; [| split; [exact FR| split; [exact BA2| split; [exact CJ2| split; [exact ERR2| exact FRM]]]]].
        split; [exact HP2|]. split; [rewrite ELEN in BLK; exact BLK|]. split; [exact BSH2|]. split; [split; [lia| exact CAPK]|]. split; [lia| split; [lia| split; [lia| split; [lia| exact BR4]]]].
  Qed.
End B2.
