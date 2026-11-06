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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import F_syscalls RDriverA_lib RDriverA_iface RF_mainA_B1 RF_mainA_B2 RF_mainA_B3.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Section B4.
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
  Notation POSTLOOP' := (POSTLOOP FI AI PZ sp0 argv envp uid hw rnd TID MPAD S4 S5 S6 S7 S8 S9 S10 S11).
  Local Notation K := (am_K FI AI).

  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  Notation RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 P1v len fd cap x23 t3 t4 t5 t6 F fc mm :=
    (GST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 len) (Z_to_bv 64 fd) (Z_to_bv 64 cap) (Z_to_bv 64 RSVA) (Z_to_bv 64 x23) t3 t4 t5 t6 F fc mm).

  Definition RDONE (b : unit) (content : list Z) (so : ASt) (ms : machine_state) (g : gst) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem)
           (A cap P1v fd : Z) (DATA junk : list byte) (errv : word) (kb : K),
      ms = RST 0x86170 x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 P1v (zlength content) fd cap 0 t3 t4 t5 t6 F fc mm
      /\ content = map bv_unsigned DATA /\ so = stdout_init
      /\ BUF_A FI AI mm g kb A cap DATA junk
      /\ FRAME' mm /\ BASE' mm /\ CJ0 mm /\ rw_cells asegs mm RERRNOA [C4 errv] /\ frm0 fc.

  Definition POSTB (r : rd_result) (so : ASt) (ms : machine_state) (g : gst) : Prop :=
    match r with
    | RdExit => rat_exitA TID 2 so ms
    | RdDone b c => RDONE b c so ms g
    end.

  #[using="AMS PZ_agree arg0 VSP CEIL VARGV ESF EARGV HT AC FPR MCI RDF RDB BSR"] Lemma main_read_all : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem) (g : gst) (e : word),
    FRAME' mm -> BASE' mm -> HEAP FI AI mm g [] -> CJ0 mm -> rw_cells asegs mm RERRNOA [C4 e] -> frm0 fc ->
    djM (read_all ioA amalloc0 afree0 RSVA (map bv_unsigned arg1)) stdout_init POSTB
      (MS (mkR (Z_to_bv 64 0x94384) (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2
               (Z_to_bv 64 2) (Z_to_bv 64 2) (Z_to_bv 64 2) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
               (Z_to_bv 64 0x86074) (Z_to_bv 64 (envp_addr sp0 argv)) S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x860a4) fc None mm (seg_rom asegs)) g.
  Proof.
    intros until e. intros FR BA HP0 CJ ERR FRM.
    pose proof (sp_facts sp0 VSP CEIL) as SF. pose proof (IMGB_len47 sp0 argv envp uid hw rnd ESF) as IL47. pose proof alloc_ceiling_bounds as CB'. unfold LO in SF.
    assert (ERSV : RSVA = 0x5d5f50) by reflexivity.
    pose proof BA as (ST & MI & EX & MC & IMG & SE & SOF & RSS & SI & SZ & ENV & GSH & HPZ & CRT). unfold LO in ST. unfold RERRNOA in ERR. unfold MFRAME in FR.
    destruct MC as (G28 & GSE & SSP).
    pose proof VARGV as (_ & _ & ARGLEN & NONUL & _).

    destruct (argv_cstring sp0 argv envp uid hw rnd mm IMG 1 arg1 ltac:(rewrite EARGV; reflexivity) ltac:(clear -SF; Z.div_mod_to_equations; lia))
      as (P1v & slack1 & HP1 & P1LO & P1HI & STR1 & SLK1). unfold str_base, struct_size, argc, envc in P1LO.
    pose proof (stack_argv2 sp0 argv envp uid hw rnd mm IMG ltac:(rewrite EARGV; cbn [length]; lia)) as ARGVP.
    assert (A1NN : ~ In (Z_to_bv 8 0) arg1) by (rewrite EARGV in NONUL; inversion NONUL as [|? ? ? X]; inversion X; assumption).
    assert (A1LEN : Z.of_nat (length arg1) <= 131071) by (rewrite EARGV in ARGLEN; inversion ARGLEN as [|? ? ? X]; inversion X; assumption).
    assert (A1NS : Namei.path_has_slash arg1 = false).
    { pose proof VARGV as (_ & _ & _ & _ & SL). rewrite EARGV in SL. cbn [tl] in SL. inversion SL as [|? ? [X _] _]. exact X. }
    assert (STR1' : bytes_at asegs mm P1v (arg1 ++ [Z_to_bv 8 0])).
    { change (arg1 ++ Z_to_bv 8 0 :: slack1) with (arg1 ++ ([Z_to_bv 8 0] ++ slack1)) in STR1. rewrite app_assoc in STR1. apply bytes_at_app in STR1. destruct STR1 as [S1 _]. exact S1. }
    destruct SSP as [G1 G2]. unfold got_ssp, ssp_guard in G1, G2.
    unfold read_all.
    pose proof (u64ro_read mm (usp0 + 8) (firstn 2 (argv_ptrs sp0 argv envp ++ [Z_to_bv 64 0])) 1 (Z_to_bv 64 P1v) (Z_to_bv 64 (usp0 + 16))
                  ARGVP ltac:(apply nth_error_firstn2; [cbn; lia|]; rewrite nth_error_app1 by (rewrite argv_ptrs_length, EARGV; cbn; lia); exact HP1) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    eapply djM_evt; [| intros msr' H; exact H].
    zstep. clear RD. zstep. zstep. zstep.
    remember READ_FUEL as rf eqn:Erf. clear Erf.
    apply evt_done.
    replace (map (Z_to_bv 8) (map bv_unsigned arg1)) with arg1 by (symmetry; apply zbytes_map_unsigned').

    eapply djM_bind.
    { eapply djM_of_implM; [| fdt].
      eapply implM_of_enode.
      eapply open_spec with (lo := usp0 - 8388608) (errv := e);
        [ rewrite (unsigned_lit (usp0 + -128)) by lia; exact ST
        | rewrite (unsigned_lit P1v) by lia; exact STR1'
        | unfold RATPA; rewrite (unsigned_lit 6187376) by lia; exact ERR
        | exact G1 | exact G2 | exact MI | reflexivity | exact A1NN | exact A1NS | ..].
      all: unfold RATPA, F_syscalls.got_ssp, F_syscalls.ssp_guard; rewrite ?(unsigned_lit 6187376) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia; rewrite ?(unsigned_lit P1v) by lia; lia. }
    cbv beta. intros r so1 msr1 g1 [[PO ->] ->].
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MUc & WMc & MI1 & ST1 & ERR1 & _ & _ & _ & FDR).
    unfold RATPA in MUc, ERR1. rewrite ?(unsigned_lit 6187376) in MUc by lia. rewrite ?(unsigned_lit (usp0 + -128)) in MUc by lia.
    rewrite ?(unsigned_lit (usp0 + -128)) in ST1 by lia. rewrite ?(unsigned_lit 6187376) in ERR1 by lia. change (6187376 + -164) with 6187212 in MUc, ERR1.
    transport_after_call asegs mm m1 MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x860b4)) with (Z_to_bv 64 0x860b4) by (symmetry; rpc).
    assert (WOKW : Forall (WOKA sp0) [(usp0 + -128 - 112, usp0 + -128); (6187212, 6187212 + 4)]).
    { unfold WOKA, LO, RERRNOA. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
    assert (HP1' : HEAP FI AI m1 g [])
      by (destruct HP0 as (sA & stA & RH & RF & Eg); exists sA, stA; split; [| split; [| exact Eg]];
          [ eapply (am_heap_frame FI AI); [exact RH| exact MUc| exact WMc|];
            repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
              first [ left; lia | right; left; exists 0x5e68c8, 0x5e68d0; split; [apply AMS; unfold a0_static; lia| unfold a0_wsafe; lia] ]
          | pose proof (fsb_ok FI) as FB; unfold app_mem in FB; eapply (rfake_frame FI); [exact RF| exact MUc| exact WMc|];
            repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; left; unfold sh, SHADOW_OFF in *; Z.div_mod_to_equations; lia ]).
    assert (ENV1 : asan_env asegs m1) by (eapply asan_env_frame; [exact ENV | exact MUc | exact WMc | env_safe_tac]).
    assert (BA1 : BASE' m1) by (eapply (BASE_A_munch PZ PZ_agree sp0 argv envp uid hw rnd TID VSP CEIL ESF HT stdout_init); [exact BA| exact WOKW| exact MUc| exact WMc| exact MI1| unfold LO; exact ST1| exact ENV1]).
    assert (CJ1 : CJ0 m1).
    { destruct CJ as [C1' C2']. split; (eapply rw_cells_transport; [eassumption| exact MUc| exact WMc| cbn [disjoint_from]; simpl_sizes; lia]). }
    pose proof FR as FR1.
    clear MUc WMc WOKW CJ HP0 G1 G2 FR BA. try clear ST; try clear MI; try clear EX; try clear G28; try clear GSE; try clear IMG; try clear SE; try clear SOF; try clear RSS; try clear SI; try clear SZ; try clear ENV; try clear GSH; try clear HPZ; try clear CRT.
    pose proof BA1 as (ST & MI & EX & MC & IMG & SE & SOF & RSS & SI & SZ & ENV & GSH & HPZ & CRT). unfold LO in ST. destruct MC as (G28 & GSE & SSP).
    destruct r as [err|fd]; cbn [open_ret open_errno] in *.
    -
      replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
      eapply djM_evt; [| intros msr' H; exact H].
      zstep. if_cases K0; zify_cond K0; try (exfalso; revert K0; clear; intros K0; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
      eapply djM_mono; [eapply (djM_of_implM _ _ (fun r so ms => POSTB r so ms g)); [| fdt] |].
      { cbn [io_diag ioA io_S].
        eapply (fprintf_exit PZ sp0 argv envp uid hw rnd TID S8 S9 S10 S11 VSP CEIL ESF FPR (PDCannotOpen (map bv_unsigned arg1)));
          [| exact BA1| reflexivity| exact FRM| intros ms'' AE; apply implM_ret; apply evt_done; exact AE].
        cbn [diag_args pdiag_fmt]. split; [reflexivity|]. exists slack1. rewrite unsigned_lit by lia.
        unfold zb. rewrite zbytes_map_unsigned'. unfold zlength. rewrite !length_map.
        split; [exact STR1|]. split; [apply map_unsigned_pos; exact A1NN|]. split; [lia|].
        split; [lia|]. split; [right; lia|]. split; [unfold GLOBALS_TOP; lia|]. split; [lia|].
        apply (SHZ_stack sp0 argv envp uid hw rnd); [exact SZ | lia | lia | lia | lia]. }
      cbv beta. intros r so' ms' g' [PO ->]. exact PO.
    -
      eapply djM_evt; [| intros msr' H; exact H].
      zstep. if_cases K0; zify_cond K0; try (exfalso; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
      zstep. zstep. zstep. zstep. apply evt_done.
      destruct HP1' as (sA & stA & RH & RF & Eg & FSL & NSI). subst g.
      unfold lb_bytes in NSI; cbn in NSI.
      pose proof (am_stack_ok FI AI) as SOK.
      eapply djM_seam.
      { eapply ((ac_malloc_any FI AI (JA FI AI) AC)) with (lo := usp0 - 8388608) (n := 65536);
          rewrite ?unsigned_lit by lia;
          first [ exact RH | exact ENV | exact RF | exact ST | exact MI | reflexivity | lia | unfold A0_RT_STACK; lia | unfold A0_MAXREQ; lia
                | cbn [fpchain]; unfold valid_frame; lia
                | cbn; tauto
                | (apply (am_budget_short FI AI); [lia| cbn [length]; lia| repeat constructor; cbn; lia| unfold lb_bytes; cbn; lia| unfold A0_NSEC_MAX; lia])
                | clear -SF; Z.div_mod_to_equations; lia ]. }
      cbv beta. intros msr2 g2 (s2 & LB2 & -> & PO).
      destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & kb & A & junk & -> & AFR & -> & RH2 & NBLK & NBSH & WM2 & NS2).
      pose proof (am_block_range FI AI _ _ _ (kb, A, 65536) RH2 ltac:(left; reflexivity)) as NBR. cbn [blk_addr blk_size fst snd] in NBR.
      assert (BA2 : BASE' m2) by (eapply (BASE_A_alloc FI AI AMS PZ PZ_agree sp0 argv envp uid hw rnd TID VSP CEIL ESF HT stdout_init); [exact BA1| unfold LO; exact AFR]).
      destruct AFR as (MI2 & ST2 & ENV2 & RF2 & AP2).
      assert (FR2 : FRAME' m2) by (unfold MFRAME in *; eapply (apres_rw_cells FI AI); [exact AP2| exact FR1| apply aclient_range_above; lia]).
      assert (CJ2 : CJ0 m2).
      { destruct CJ1 as [C1' C2']. split; (eapply (apres_rw_cells FI AI); [exact AP2| eassumption| eapply (aclient_range_static FI AI _ _ _ _ 0x5d5f40 0x5e5f80); [apply AMS; unfold a0_static; lia| cbn; lia| cbn; lia]]). }
      assert (ERR2 : rw_cells asegs m2 RERRNOA [C4 (open_errno (SVal fd) e)]).
      { unfold RERRNOA in *. eapply (apres_rw_cells FI AI); [exact AP2| exact ERR1| eapply (aclient_range_static FI AI _ _ _ _ 0x5e68c8 0x5e68d0); [apply AMS; unfold a0_static; lia| cbn; lia| cbn; lia]]. }
      clear AP2 WM2 BA1 FR1 CJ1 ERR1 ST MI EX G28 GSE SSP IMG SE SOF RSS SI SZ ENV GSH HPZ CRT.
      replace (ret_pc (Z_to_bv 64 0x860c8)) with (Z_to_bv 64 0x860c8) by (symmetry; rpc).

      eapply djM_evt; [| intros msr' H; exact H].
      zstep. if_cases K1; zify_cond K1; try (exfalso; rewrite ?unsigned_lit in K1 by lia; lia). clear K1.
      zstep. zstep. zstep. zstep.
      eapply entry_test_step; [lia|].
      apply evt_done.
      apply djM_mret_bind. cbv beta iota.
      eapply djM_bind.
      { eapply rd_loop; first [eassumption | lia | idtac].
        unfold RDINV, rd_pc. cbn [rd_content rd_cap rd_buf zlength length Z.of_nat Z.eqb].
        do 17 eexists. exists F, fc, m2, A, [], junk, (open_errno (SVal fd) e), kb.
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [| split; [exact FR2| split; [exact BA2| split; [exact CJ2| split; [exact ERR2| exact FRM]]]]].
        split; [exists s2, stA; split; [exact RH2| split; [exact RF2| split; [reflexivity| split; [exact FSL|]]]]|].
        {
          unfold lb_bytes; cbn. rewrite NS2. destruct (a0_cls 65536 =? 0); lia. }
        cbn [length Z.of_nat Z.sub].
        split; [replace (Z.to_nat (65536 - 0)) with (Z.to_nat 65536) by reflexivity; apply (proj2 (rw_cells_app _ _ _ [CB 0%nat []] _)); split; [apply rw_cells_CB0; lia| cbn [cells_size csize Nat.add]; rewrite Z.add_0_r; exact NBLK] |].
        split; [exact NBSH|]. split; [split; [lia| exists 16; split; [lia| reflexivity]]|].
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. apply win_ok_of_range; lia. }
      cbv beta. intros res so3 msr3 g3 PO.
      destruct res as [|b c]; cbn [POSTLOOP] in PO.
      { apply djM_ret. exact PO. }

      clear dependent m2.
      destruct PO as (x1 & w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & F3 & fc3 & m3 & A3 & cap3 & DATA3 & junk3 & errv3 & kb3
                      & -> & HC3 & -> & BU3 & FR3 & BA3 & CJ3 & ERR3 & FRM3).
      pose proof BA3 as (ST & MI & EX & MC & IMG & SE & SOF & RSS & SI & SZ & ENV & GSH & HPZ & CRT). unfold LO in ST. destruct MC as (G28 & GSE & SSP).
      unfold RERRNOA in ERR3. unfold MFRAME in FR3.
      pose proof BU3 as (HP3 & BLK3 & BSH3 & CAP3 & LEN3 & BQ1 & BQ2 & BQ3 & BQ4).
      eapply djM_evt; [| intros msr' H; exact H]. zstep. zstep. apply evt_done.
      eapply djM_mono; [eapply (djM_of_implM _ _ (fun r so ms => POSTB r so ms g3)); [| fdt] |].
      { eapply implM_bind.
        { eapply implM_of_enode.
          eapply close_spec with (lo := usp0 - 8388608) (errv := errv3); try reflexivity; unfold RATPA; rewrite ?(unsigned_lit 6187376) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia;
            first [ exact ST | exact ERR3 | exact MI | lia ]. }
        cbv beta. intros r3 so4 ms4 [PO ->].
        destruct PO as (y0 & y1 & y2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & m4 & -> & MUc & WMc & MI4 & ST4 & ERR4).
        unfold RATPA in MUc, ERR4. rewrite ?(unsigned_lit 6187376) in MUc by lia. rewrite ?(unsigned_lit (usp0 + -128)) in MUc by lia.
        rewrite ?(unsigned_lit (usp0 + -128)) in ST4 by lia. rewrite ?(unsigned_lit 6187376) in ERR4 by lia. change (6187376 + -164) with 6187212 in MUc, ERR4.
        pose proof (BSH3 : boxed (rw_cells asegs m3 (sh A3) (shadow_cells (block_shadow cap3)))) as BSHb. clear BSH3.
        transport_after_call asegs m3 m4 MUc WMc.
        replace (ret_pc (Z_to_bv 64 0x86170)) with (Z_to_bv 64 0x86170) by (symmetry; rpc).
        assert (WOKW : Forall (WOKA sp0) [(usp0 + -128 - 32, usp0 + -128); (6187212, 6187212 + 4)]).
        { unfold WOKA, LO, RERRNOA. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
        assert (HP4 : HEAP FI AI m4 g3 [(kb3, A3, cap3)])
          by (destruct HP3 as (sB & stB & RHb & RFb & Egb); exists sB, stB; split; [| split; [| exact Egb]];
              [ eapply (am_heap_frame FI AI); [exact RHb| exact MUc| exact WMc|];
                repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
                  first [ left; lia | right; left; exists 0x5e68c8, 0x5e68d0; split; [apply AMS; unfold a0_static; lia| unfold a0_wsafe; lia] ]
              | pose proof (fsb_ok FI) as FB; unfold app_mem in FB; eapply (rfake_frame FI); [exact RFb| exact MUc| exact WMc|];
                repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; left; unfold sh, SHADOW_OFF in *; Z.div_mod_to_equations; lia ]).
        assert (ENV4 : asan_env asegs m4) by (eapply asan_env_frame; [exact ENV | exact MUc | exact WMc | env_safe_tac]).
        assert (BA4 : BASE' m4) by (eapply (BASE_A_munch PZ PZ_agree sp0 argv envp uid hw rnd TID VSP CEIL ESF HT stdout_init); [exact BA3| exact WOKW| exact MUc| exact WMc| exact MI4| unfold LO; exact ST4| exact ENV4]).
        assert (CJ4 : CJ0 m4).
        { destruct CJ3 as [C1' C2']. split; (eapply rw_cells_transport; [eassumption| exact MUc| exact WMc| cbn [disjoint_from]; simpl_sizes; lia]). }
        assert (BSH4 : rw_cells asegs m4 (sh A3) (shadow_cells (block_shadow cap3))).
        { unfold boxed in BSHb. eapply bshadow_transport; [lia| exact BSHb| exact MUc| exact WMc| cbn [disjoint_from]; unfold sh, SHADOW_OFF in *; Z.div_mod_to_equations; lia]. }
        apply implM_ret. apply evt_done. cbn [POSTB]. unfold RDONE.
        do 16 eexists. exists F3, fc3, m4, A3, cap3, P1v, fd, DATA3. exists junk3, (close_errno r3 errv3), kb3.
        split; [reflexivity|]. split; [exact HC3|]. split; [reflexivity|]. split; [| split; [exact FR3| split; [exact BA4| split; [exact CJ4| split; [exact ERR4| exact FRM3]]]]].
        split; [exact HP4|]. split; [exact BLK3|]. split; [exact BSH4|]. split; [exact CAP3|]. split; [exact LEN3|]. split; [lia|]. split; [lia|]. split; [lia| exact BQ4]. }
      cbv beta. intros r so' ms' g' [PO ->]. exact PO.
  Qed.
End B4.
