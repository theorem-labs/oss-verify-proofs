(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Agree MonadX Ceiling.
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

From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import RDriverA_lib RDriverA_iface RF_mainA_B1 RF_mainA_B2.

Section B3.
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

  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  Local Notation K := (am_K FI AI).

  #[using="Type"] Lemma shiftr26_zero_iff : forall a, 0 <= a -> (Z.shiftr a 26 = 0 <-> a < 67108864).
  Proof.
    intros a Ha. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 26) with 67108864.
    split; intros H; [| apply Z.div_small; lia]. Z.div_mod_to_equations. lia.
  Qed.

  #[using="Type"] Lemma djM_mret_bind : forall {A B} (a : A) (f : A -> M ASt B) s Q msr g,
    djM (f a) s Q msr g -> djM (x <- mret a ;; f x) s Q msr g.
  Proof. intros. exact H. Qed.
  #[using="Type"] Lemma djM_mret_bind2 : forall {A B C} (a : A) (f : A -> M ASt B) (h : B -> M ASt C) s Q msr g,
    djM (y <- f a ;; h y) s Q msr g -> djM (y <- (x <- mret a ;; f x) ;; h y) s Q msr g.
  Proof. intros. exact H. Qed.

  #[using="sp0 argv envp arg0 arg1 VARGV ESF EARGV"] Lemma lb_remove_second : forall (k0 k : K) A0 n0 A n,
    NoDup (map blk_id [(k0, A0, n0); (k, A, n)]) -> lb_remove (am_K_eqb FI AI) k [(k0, A0, n0); (k, A, n)] = [(k0, A0, n0)].
  Proof.
    intros k0 k A0 n0 A n ND. unfold lb_remove. rewrite !filter_cons, filter_nil. cbn [blk_id fst] in *.
    inversion ND as [|x l NI ND']; subst.
    destruct (am_K_eqb FI AI k0 k) eqn:E0.
    - exfalso. apply (proj1 (am_K_eqb_eq FI AI _ _)) in E0. subst k0. apply NI. constructor.
    - replace (am_K_eqb FI AI k k) with true by (symmetry; apply (proj2 (am_K_eqb_eq FI AI k k)); reflexivity).
      cbn [negb]. destruct (decide (Is_true true)) as [Y|N]; [| exfalso; exact (N I)]. destruct (decide (Is_true false)) as [Y'|N']; [exfalso; exact Y'| reflexivity].
  Qed.

  #[using="AMS PZ_agree arg0 VSP CEIL VARGV ESF EARGV HT AC FPR MCI RDF RDB BSR"] Lemma rd_body : forall (fd P1v : Z) (st : rd_st) (so : ASt) msr g,
    3 <= fd < 2^32 -> nth_error (argv_ptrs sp0 argv envp) 1 = Some (Z_to_bv 64 P1v) ->
    RDINV' fd P1v st so msr g ->
    djM (read_loop_body ioA amalloc0 afree0 RSVA fd (map bv_unsigned arg1) st) so (POSTBODY' fd P1v) msr g.
  Proof.
    intros fd P1v st so msr g FD HP1 RI.
    destruct RI as (x1 & t0 & t1 & t2 & x9 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & mm & A & DATA & junk & errv & kb
                    & -> & HCT & -> & BU & FR & BA & CJ & ERR & FRM).
    pose proof (sp_facts sp0 VSP CEIL) as SF. pose proof (IMGB_len47 sp0 argv envp uid hw rnd ESF) as IL47. pose proof alloc_ceiling_bounds as CB'. unfold LO in SF.
    assert (LENZ : zlength (rd_content st) = Z.of_nat (length DATA)) by (rewrite HCT; unfold zlength; rewrite length_map; reflexivity).
    pose proof BU as (HP0 & BLK & BSH & [CAPR [k [K0' CAPK]]] & LENR & BR1 & BR2 & BR3 & BR4).
    unfold read_loop_body, rd_pc. cbn [ioA io_S]. rewrite LENZ.
    pose proof BA as (ST & MI & EX & MC & IMG & SE & SOF & RSS & SI & SZ & ENV & GSH & HPZ & CRT). unfold LO in ST. unfold RERRNOA in ERR. unfold MFRAME in FR.
    destruct MC as (G28 & GSE & SSP).
    destruct (Z.eqb_spec (Z.of_nat (length DATA)) (rd_cap st)) as [K00|K00].
    2:{
        eapply djM_evt; [| intros msr' H; exact H]. zstep. zstep. apply evt_done.
        apply djM_mret_bind. cbv iota beta.
        rewrite <- LENZ.
        eapply djM_mono; [eapply djM_of_implM; [| unfold rd_read_part; fdt] |].
        { eapply (rd_read FI AI AMS PZ PZ_agree sp0 argv envp uid hw rnd arg0 arg1 TID MPAD S4 S5 S6 S7 S8 S9 S10 S11);
            first [eassumption | exact HCT | exact BU | unfold MFRAME; exact FR | unfold RERRNOA; exact ERR | lia]. }
        cbv beta. intros r so' ms' g' [PO ->]. exact PO. }

    eapply djM_evt; [| intros msr' H; exact H].
    zstep. zstep. if_cases K0; zify_cond K0.
    {
      assert (GE : 67108864 <= rd_cap st).
      { destruct (Z.lt_ge_cases (rd_cap st) 67108864) as [L|G]; [| exact G]. exfalso. apply K0.
        apply (proj2 (shiftr26_zero_iff (Z.of_nat (length DATA)) ltac:(lia))). lia. }
      replace (MAX_INPUT <=? rd_cap st) with true by (symmetry; apply Z.leb_le; unfold MAX_INPUT; lia).
      zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
      eapply djM_mono; [eapply (djM_of_implM _ _ (fun r so ms => POSTBODY' fd P1v r so ms g)); [| fdt] |].
      { apply implM_bind_assoc. cbn [io_diag ioA io_S].
        eapply (fprintf_exit PZ sp0 argv envp uid hw rnd TID S8 S9 S10 S11 VSP CEIL ESF FPR PDTooBig);
          [| exact BA| reflexivity| exact FRM| intros ms'' AE; apply implM_mret_bind; cbv beta iota; apply implM_ret; apply evt_done; exact AE].
        cbn [diag_args pdiag_fmt]. split; [reflexivity|]. rewrite unsigned_lit by lia. reflexivity. }
      cbv beta. intros r so' ms' g' [PO ->]. exact PO. }

    assert (LTM : rd_cap st < 67108864).
    { rewrite <- K00. apply (proj1 (shiftr26_zero_iff (Z.of_nat (length DATA)) ltac:(lia))). exact K0. }
    replace (MAX_INPUT <=? rd_cap st) with false by (symmetry; apply Z.leb_gt; unfold MAX_INPUT; lia).
    assert (CAP2 : rd_cap st * 2 <= 67108864).
    { rewrite CAPK in LTM |- *. change 67108864 with (2 ^ 26) in LTM |- *. apply Z.pow_lt_mono_r_iff in LTM; [| lia| lia].
      replace (2 ^ k * 2) with (2 ^ (k + 1)) by (rewrite Z.pow_add_r by lia; lia). apply Z.pow_le_mono_r; lia. }
    zstep. zstep. zstep. apply evt_done.
    replace (Z.shiftl (Z.of_nat (length DATA)) 1) with (rd_cap st * 2) by (rewrite Z.shiftl_mul_pow2 by lia; lia).

    rewrite <- LENZ.
    lazymatch goal with |- djM _ ?s ?Q ?ms ?g0 =>
      change (djM (rd_read_part fd (map bv_unsigned arg1) (mkRd tt (rd_cap st * 2) (rd_content st))) s Q ms g0) end.
    rewrite LENZ.

    destruct HP0 as (sA & stA & RH & RF & Eg & FSL & NSI). subst g.
    unfold lb_bytes in NSI; cbn in NSI.
    pose proof (am_stack_ok FI AI) as SOK.
    eapply djM_seam.
    { eapply ((ac_malloc_any FI AI (JA FI AI) AC)) with (lo := usp0 - 8388608) (n := rd_cap st * 2);
        rewrite ?unsigned_lit by lia;
        first [ exact RH | exact ENV | exact RF | exact ST | exact MI | reflexivity | lia | unfold A0_RT_STACK; lia | unfold A0_MAXREQ; lia
              | cbn [fpchain]; unfold valid_frame; lia
              | cbn; tauto
              | (apply (am_budget_short FI AI); [lia| cbn [length]; lia| repeat constructor; cbn; lia| unfold lb_bytes; cbn; lia| unfold A0_NSEC_MAX; lia])
              | clear -SF; Z.div_mod_to_equations; lia ]. }
    cbv beta. intros msr1 g1 (s1 & LB1 & -> & PO).
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & k1 & A' & junk' & -> & AFR & -> & RH1 & NBLK & NBSH & WM1 & NS1).

    pose proof (am_block_range FI AI _ _ _ (k1, A', rd_cap st * 2) RH1 ltac:(left; reflexivity)) as NBR. cbn [blk_addr blk_size fst snd] in NBR.
    pose proof (am_blocks_nodup FI AI _ _ _ RH1) as ND.
    assert (NE : k1 <> kb).
    { intros E. pose proof ND as ND'. rewrite E in ND'. cbn [map blk_id fst] in ND'. inversion ND' as [|x l NI ND'']; subst. apply NI. constructor. }
    assert (DISJ : A' + rd_cap st * 2 <= A \/ A + rd_cap st <= A').
    { pose proof (am_blocks_disjoint FI AI _ _ _ (k1, A', rd_cap st * 2) (kb, A, rd_cap st) RH1 ltac:(left; reflexivity) ltac:(right; left; reflexivity)) as D.
      cbn [blk_addr blk_size fst snd] in D. apply D. intros E. apply NE. congruence. }

    assert (BA1 : BASE' m1) by (eapply (BASE_A_alloc FI AI AMS PZ PZ_agree sp0 argv envp uid hw rnd TID VSP CEIL ESF HT stdout_init); [exact BA| unfold LO; exact AFR]).
    destruct AFR as (MI1 & ST1 & ENV1 & RF1 & AP1).
    assert (FR1 : FRAME' m1) by (unfold MFRAME; eapply (apres_rw_cells FI AI); [exact AP1| exact FR| apply aclient_range_above; lia]).
    assert (CJ1 : CJ0 m1).
    { destruct CJ as [C1' C2']. split; (eapply (apres_rw_cells FI AI); [exact AP1| eassumption| eapply (aclient_range_static FI AI _ _ _ _ 0x5d5f40 0x5e5f80); [apply AMS; unfold a0_static; lia| cbn; lia| cbn; lia]]). }
    assert (ERR1 : rw_cells asegs m1 RERRNOA [C4 errv]).
    { unfold RERRNOA. eapply (apres_rw_cells FI AI); [exact AP1| exact ERR| eapply (aclient_range_static FI AI _ _ _ _ 0x5e68c8 0x5e68d0); [apply AMS; unfold a0_static; lia| cbn; lia| cbn; lia]]. }
    assert (BLK1 : rw_cells asegs m1 A [CB (length DATA) DATA; CB (Z.to_nat (rd_cap st - Z.of_nat (length DATA))) junk]).
    { eapply (apres_rw_cells FI AI); [exact AP1| exact BLK| eapply aclient_range_block; [left; reflexivity| cbn; lia| cbn -[Z.of_nat Z.add]; simpl_sizes; lia]]. }
    clear BA ST MI EX G28 GSE SSP IMG SE SOF RSS SI SZ ENV GSH HPZ CRT FR CJ ERR BLK BSH AP1 WM1.
    pose proof BA1 as (ST & MI & EX & MC & IMG & SE & SOF & RSS & SI & SZ & ENV & GSH & HPZ & CRT). unfold LO in ST. destruct MC as (G28 & GSE & SSP).
    replace (ret_pc (Z_to_bv 64 0x8611c)) with (Z_to_bv 64 0x8611c) by (symmetry; rpc).

    eapply djM_evt; [| intros msr' H; exact H].
    zstep. if_cases K1; zify_cond K1; try (exfalso; rewrite ?unsigned_lit in K1 by lia; lia). clear K1.
    zstep. zstep. if_cases K2; zify_cond K2; try (exfalso; rewrite ?unsigned_lit in K2 by lia; lia). clear K2.
    zstep. zstep. zstep. zstep.

    pose proof BLK1 as SRC. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in SRC. destruct SRC as [SRC _].
    pose proof (rw_cells_bytes_at _ _ _ _ SRC) as SRCB. cbn [cells_bytes cbytes app] in SRCB. rewrite app_nil_r in SRCB. clear SRC.
    destruct (rw_cells_CB_split m1 A' (Z.to_nat (rd_cap st * 2)) (length DATA) junk' NBLK ltac:(lia)) as [NB1 NB2].
    pose proof (am_block_shadow FI AI _ _ _ (kb, A, rd_cap st) RH1 ltac:(right; left; reflexivity)) as OBSH. cbn [blk_addr blk_size fst snd] in OBSH.
    eapply evt_cut.
    { eapply (memcpy_i_callq MCI (usp0 - 8388608)) with (src := DATA) (junk := firstn (length DATA) junk'); rewrite ?unsigned_lit by lia;
        first [ exact SRCB | exact MI1 | exact ENV1 | exact ST1 | lia
              | replace (Z.to_nat (Z.of_nat (length DATA))) with (length DATA) by lia; exact NB1
              | unfold A0_RT_STACK; lia | env_safe_tac | idtac ].
      -
        split; [| split; [| unfold win_ok in *; lia]].
        + eapply (accessible_of_block_shadow m1 A' (rd_cap st * 2)); [exact NBSH | clear -NBR; Z.div_mod_to_equations; lia | lia | reflexivity | lia | lia].
        + eapply sh_readable_sub; [eapply (BSR s1 _ m1 (k1, A', rd_cap st * 2)); [exact RH1| left; reflexivity] | cbn; lia | cbn; lia | lia].
      -
        split; [| split; [| unfold win_ok in *; lia]].
        + eapply (accessible_of_block_shadow m1 A (rd_cap st)); [exact OBSH | clear -BR3; Z.div_mod_to_equations; lia | lia | reflexivity | lia | lia].
        + eapply sh_readable_sub; [eapply (BSR s1 _ m1 (kb, A, rd_cap st)); [exact RH1| right; left; reflexivity] | cbn; lia | cbn; lia | lia].
      - pose proof (@alloc_ceiling_bounds HC) as CBX; unfold icpt_rng, icpt_win, win_ok, RSVA in *; lia.
      - pose proof (@alloc_ceiling_bounds HC) as CBX; unfold icpt_rng, icpt_win, win_ok, RSVA in *; lia. }
    cbv beta. intros ms' PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & -> & MUc & WMc & MI2 & ST2 & ENV2 & NB1' & _).
    rewrite ?unsigned_lit in MUc by lia. rewrite ?unsigned_lit in ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x86138)) with (Z_to_bv 64 0x86138) by (symmetry; rpc).

    assert (WOKW : Forall (WOKA sp0) [(A', A' + Z.of_nat (length DATA)); (usp0 - 8388608, usp0 + -128)]).
    { unfold WOKA. constructor; [right; right; cbn [fst snd]; split; [lia| split; [lia| app_iv_tac]]|]. constructor; [left; cbn [fst snd]; unfold LO; lia| constructor]. }
    assert (RH2 : RHEAP_A FI AI s1 [(k1, A', rd_cap st * 2); (kb, A, rd_cap st)] m2).
    { eapply (am_heap_frame FI AI); [exact RH1| exact MUc| exact WMc|].
      apply Forall_cons; [| apply Forall_cons; [left; cbn; lia| apply Forall_nil]].
      right; right; left. exists (k1, A', rd_cap st * 2). split; [left; reflexivity|]. cbn. lia. }
    assert (RF2 : RFAKE FI stA m2).
    { pose proof (fsb_ok FI) as FB. unfold app_mem in FB.
      eapply (rfake_frame FI); [exact RF1| exact MUc| exact WMc|].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; left; unfold sh, SHADOW_OFF in *; Z.div_mod_to_equations; lia. }
    assert (BA2 : BASE' m2) by (eapply (BASE_A_munch PZ PZ_agree sp0 argv envp uid hw rnd TID VSP CEIL ESF HT stdout_init); [exact BA1| exact WOKW| exact MUc| exact WMc| exact MI2| unfold LO; exact ST2| exact ENV2]).
    assert (CJ2 : CJ0 m2).
    { destruct CJ1 as [C1' C2']. split; (eapply rw_cells_transport; [eassumption| exact MUc| exact WMc| cbn [disjoint_from]; simpl_sizes; lia]). }
    assert (ERR2 : rw_cells asegs m2 RERRNOA [C4 errv]).
    { eapply rw_cells_transport; [exact ERR1| exact MUc| exact WMc| cbn [disjoint_from]; simpl_sizes; unfold RERRNOA; lia]. }
    assert (FR2 : FRAME' m2).
    { unfold MFRAME in *. eapply rw_cells_transport; [exact FR1| exact MUc| exact WMc| cbn [disjoint_from]; simpl_sizes; lia]. }
    assert (NB2' : rw_cells asegs m2 (A' + Z.of_nat (length DATA)) [CB (Z.to_nat (rd_cap st * 2) - length DATA) (skipn (length DATA) junk')]).
    { eapply rw_cells_transport; [exact NB2| exact MUc| exact WMc| cbn [disjoint_from]; simpl_sizes; lia]. }
    clear MUc WMc WOKW BA1 FR1 CJ1 ERR1 BLK1 NB1 NB2 NBLK NBSH OBSH SRCB ST MI EX G28 GSE SSP IMG SE SOF RSS SI SZ ENV GSH HPZ CRT MI1 ST1 ENV1 RF1 RH1.
    pose proof BA2 as (ST & MI & EX & MC & IMG & SE & SOF & RSS & SI & SZ & ENV & GSH & HPZ & CRT). unfold LO in ST. destruct MC as (G28 & GSE & SSP).

    zstep. zstep. apply evt_done.
    eapply djM_seam.
    { eapply ((ac_free_any FI AI (JA FI AI) AC)) with (lo := usp0 - 8388608) (k := kb) (A := A) (n := rd_cap st);
        rewrite ?unsigned_lit by lia;
        first [ exact RH2 | right; left; reflexivity | exact ENV2 | exact RF2 | exact ST2 | exact MI2 | reflexivity | lia | unfold A0_RT_STACK; lia | unfold A0_MAXREQ; lia
              | cbn [fpchain]; unfold valid_frame; lia
              | cbn; tauto
              | clear -SF; Z.div_mod_to_equations; lia ]. }
    cbv beta. intros msr3 g3 (s3 & LB3 & -> & PO).
    destruct PO as (w0 & w1 & w2 & ra0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & AFR3 & -> & RH3 & NS3).
    rewrite (lb_remove_second k1 kb A' (rd_cap st * 2) A (rd_cap st) ND) in AFR3, RH3.

    assert (BA3 : BASE' m3) by (eapply (BASE_A_alloc FI AI AMS PZ PZ_agree sp0 argv envp uid hw rnd TID VSP CEIL ESF HT stdout_init); [exact BA2| unfold LO; exact AFR3]).
    destruct AFR3 as (MI3 & ST3 & ENV3 & RF3 & AP3).
    assert (FR3 : FRAME' m3) by (unfold MFRAME in *; eapply (apres_rw_cells FI AI); [exact AP3| exact FR2| apply aclient_range_above; lia]).
    assert (CJ3 : CJ0 m3).
    { destruct CJ2 as [C1' C2']. split; (eapply (apres_rw_cells FI AI); [exact AP3| eassumption| eapply (aclient_range_static FI AI _ _ _ _ 0x5d5f40 0x5e5f80); [apply AMS; unfold a0_static; lia| cbn; lia| cbn; lia]]). }
    assert (ERR3 : rw_cells asegs m3 RERRNOA [C4 errv]).
    { unfold RERRNOA in *. eapply (apres_rw_cells FI AI); [exact AP3| exact ERR2| eapply (aclient_range_static FI AI _ _ _ _ 0x5e68c8 0x5e68d0); [apply AMS; unfold a0_static; lia| cbn; lia| cbn; lia]]. }
    assert (BLK3 : rw_cells asegs m3 A' [CB (length DATA) DATA; CB (Z.to_nat (rd_cap st * 2 - Z.of_nat (length DATA))) (skipn (length DATA) junk')]).
    { apply (proj2 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)). split.
      - eapply (apres_rw_cells FI AI); [exact AP3| replace (length DATA) with (Z.to_nat (Z.of_nat (length DATA))) at 1 by lia; exact NB1'
                                       | eapply aclient_range_block; [left; reflexivity| cbn; lia| cbn -[Z.of_nat Z.add Z.mul]; simpl_sizes; lia]].
      - cbn [cells_size csize Nat.add]. replace (Z.to_nat (rd_cap st * 2 - Z.of_nat (length DATA))) with (Z.to_nat (rd_cap st * 2) - length DATA)%nat by lia.
        replace (A' + Z.of_nat (length DATA + 0)) with (A' + Z.of_nat (length DATA)) by lia.
        eapply (apres_rw_cells FI AI); [exact AP3| exact NB2'| eapply aclient_range_block; [left; reflexivity| cbn; lia| cbn -[Z.of_nat Z.add Z.mul Z.sub]; simpl_sizes; lia]]. }
    pose proof (am_block_shadow FI AI _ _ _ (k1, A', rd_cap st * 2) RH3 ltac:(left; reflexivity)) as NBSH3. cbn [blk_addr blk_size fst snd] in NBSH3.
    clear AP3 NB1' NB2' BA2 FR2 CJ2 ERR2 RH2 RF2 ST MI ENV.
    replace (ret_pc (Z_to_bv 64 0x86140)) with (Z_to_bv 64 0x86140) by (symmetry; rpc).

    rewrite <- LENZ.
    eapply djM_mono; [eapply djM_of_implM; [| unfold rd_read_part; fdt] |].
    { epose proof (rd_read FI AI AMS PZ PZ_agree sp0 argv envp uid hw rnd arg0 arg1 TID MPAD S4 S5 S6 S7 S8 S9 S10 S11) as RR.
      specialize (RR VSP CEIL VARGV ESF EARGV HT FPR MCI RDF RDB BSR fd P1v (mkRd tt (rd_cap st * 2) (rd_content st)) (gh FI AI s3)).
      cbn [rd_buf rd_cap rd_content] in RR. eapply RR; clear RR.
      1: exact FD. 1: exact HP1. 1: exact HCT. 2: cbn [rd_buf rd_cap rd_content]; lia. 2: exact FR3. 2: exact BA3. 2: exact CJ3. 2: exact ERR3. 2: exact FRM.
      split; [exists s3, stA; split; [exact RH3| split; [exact RF3| split; [reflexivity| split; [exact FSL|]]]]|].
      {
        unfold lb_bytes; cbn. rewrite NS3, NS1. destruct (a0_cls (rd_cap st * 2) =? 0); lia. }
      split; [exact BLK3|]. split; [exact NBSH3|].
      split; [split; [lia| exists (k + 1); split; [lia| rewrite CAPK, Z.pow_add_r by lia; lia]]|].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. apply win_ok_of_range; lia. }
    cbv beta. intros r so' ms' g' [PO ->]. exact PO.
  Qed.

  Definition POSTLOOP (fd P1v : Z) (r : rd_result) (so : ASt) (ms : machine_state) (g : gst) : Prop :=
    match r with
    | RdExit => rat_exitA TID 2 so ms
    | RdDone b c => RDBRK' fd P1v b c so ms g
    end.

  #[using="Type"] Lemma djM_loop_S : forall {X R} fuel (body : X -> M ASt (X + R)) (x : X) s Q msr g,
    djM (r <- body x ;; match r with inl x' => mloop fuel body x' | inr v => mret v end) s Q msr g ->
    djM (mloop (S fuel) body x) s Q msr g.
  Proof. intros. exact H. Qed.

  #[using="AMS PZ_agree arg0 VSP CEIL VARGV ESF EARGV HT AC FPR MCI RDF RDB BSR"] Lemma rd_loop : forall (fuel : nat) (fd P1v : Z) (st : rd_st) (so : ASt) msr g,
    3 <= fd < 2^32 -> nth_error (argv_ptrs sp0 argv envp) 1 = Some (Z_to_bv 64 P1v) ->
    RDINV' fd P1v st so msr g ->
    djM (mloop fuel (read_loop_body ioA amalloc0 afree0 RSVA fd (map bv_unsigned arg1)) st) so (POSTLOOP fd P1v) msr g.
  Proof.
    induction fuel as [|fuel IH]; intros fd P1v st so msr g FD HP1 RI.
    - cbn [mloop]. apply djM_unr.
    - apply djM_loop_S. eapply djM_bind; [apply rd_body; [exact FD| exact HP1| exact RI]|].
      intros [st'|[|b c]] so' msr' g' PO; cbn [POSTBODY POSTLOOP] in PO |- *.
      + apply IH; [exact FD| exact HP1| exact PO].
      + apply djM_ret. exact PO.
      + apply djM_ret. exact PO.
  Qed.
End B3.
