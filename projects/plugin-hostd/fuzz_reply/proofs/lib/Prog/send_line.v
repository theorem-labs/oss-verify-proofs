From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import memcpy_c __errno_location_c send_line_c send_line_loop.
Import ListNotations.
Open Scope Z_scope.

Ltac sl_off Hoff :=
  unfold send_live; rewrite Hoff; cbn [negb andb orb];
  eapply evt_mono;
  [ eapply sl_epi;
    [ | match goal with H : stk _ _ _ _ |- _ => exact H end
      | match goal with H : rw_cells _ _ (bv_unsigned _ + -96) _ |- _ => exact H end ];
    lia
  | intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & STR);
    do 16 eexists;
    split; [reflexivity|];
    split; [eapply munch_weaken; [|eassumption]; unfold sub_fp; intros x Hx; cbn [outside app] in *; lia|];
    split; [eassumption|]; split; [exact STR|];
    split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
    split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
    intros D; discriminate ].

Theorem send_line_nogrow_holds : memcpy_contract -> __errno_location_contract -> send_line_nogrow_contract.
Proof.
  intros MC EL. unfold send_line_nogrow_contract. cbv zeta.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    B junk cl br dd ei mx nout cap out ev
    ST HLO HE1 HE2 MI HB HLB HLG HLE HLS Hcl Hbr Hdd Hei HCL HBR HDD HEI HOV HER HLIVE.
  unfold SEND_LINE, SEND_LINE_FRAME, G_CLIENT, G_RELAY_LO, G_BROKEN, G_DEAD, G_EINTR, G_OUTV, G_RELAY_HI,
    ERRNO_OFF, EINTR_V, EPIPE_V in *.
  pose proof (zr_word sp) as Rsp. pose proof (zr_word tp) as Rtp. pose proof (zr_word a0) as Ra0.
  pose proof (zr_word a1) as Ra1. pose proof (zr_word out) as Rout. pose proof (zr_word nout) as Rnout.
  pose proof (zr_word cap) as Rcap. unfold inr64 in *.
  pose proof (bytes_at_bound rsegs m _ _ HB) as BHB.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 96%nat ST.
  do 12 step.
  destruct (Z.eq_dec (bv_unsigned a1) 0) as [L0|L0].
  - step. if_true.
    assert (Hoff : send_off cl br (bv_unsigned a1) = true).
    { unfold send_off. rewrite (proj2 (Z.eqb_eq _ _) L0), Bool.orb_true_r. reflexivity. }
    sl_off Hoff.
  - step. if_false. step. step.
    destruct Hcl as [-> | ->].
    + step. if_false.
      step. step. step. step. step. step.
      destruct Hbr as [-> | ->].
      * if_false. step. step. step. step.
        replace (sx32 (Z_to_bv 64 3)) with (Z_to_bv 64 3) by (apply bv_eq; reflexivity).
        match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
        assert (Hlive : send_live 3 0 dd (bv_unsigned a1) = (dd =? 0)).
        { unfold send_live, send_off. rewrite (proj2 (Z.eqb_neq _ _) L0). reflexivity. }
        assert (Hoff : send_off 3 0 (bv_unsigned a1) = false).
        { unfold send_off. rewrite (proj2 (Z.eqb_neq _ _) L0). reflexivity. }
        rewrite Hlive in HLIVE |- *. rewrite Hoff. cbn [negb andb orb].
        assert (OUTC : dd = 0 ->
          rw_cells rsegs m1 (bv_unsigned out + bv_unsigned nout) [CB (Z.to_nat (bv_unsigned a1)) junk] /\
          bv_unsigned nout + bv_unsigned a1 <= bv_unsigned cap /\
          0x31018 <= bv_unsigned out + bv_unsigned nout /\
          (bv_unsigned out + bv_unsigned nout + bv_unsigned a1 <= bv_unsigned tp + -164 \/
           bv_unsigned tp + -164 + 4 <= bv_unsigned out + bv_unsigned nout) /\
          bv_unsigned out + bv_unsigned nout + bv_unsigned a1 <= lo /\
          (bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned out + bv_unsigned nout \/
           bv_unsigned out + bv_unsigned nout + bv_unsigned a1 <= bv_unsigned a0)).
        { intros D. rewrite D in HLIVE. destruct (HLIVE eq_refl) as (C & H1 & H2 & H3 & H4 & H5).
          split; [| exact (conj H1 (conj H2 (conj H3 (conj H4 H5))))].
          eapply rw_cells_transport; [exact C | exact MU | exact WM |].
          cbn [disjoint_from cells_size csize]. lia. }
        clear HLIVE.
        assert (INV : sl_inv tp a0 a1 mx cap out B dd ei 0 ev nout (bv_unsigned a1) junk m1).
        { unfold sl_inv.
          split; [lia|]. split; [exact Hdd|]. split; [exact Hei|]. split; [lia|].
          split; [intros D; destruct (OUTC D) as (_ & H1 & _); lia|].
          split; [lia|].
          split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
          split; [assumption|]. split; [assumption|]. split; [assumption|].
          intros D. destruct (OUTC D) as (C & H1 & H2 & H3 & H4 & H5).
          replace (bv_unsigned out + bv_unsigned nout - 0) with (bv_unsigned out + bv_unsigned nout) by lia.
          split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
          change [CB (Z.to_nat 0) (firstn (Z.to_nat 0) B); CB (Z.to_nat (bv_unsigned a1)) junk]
            with ([CB 0 []] ++ [CB (Z.to_nat (bv_unsigned a1)) junk]).
          apply sl_cells_app_r; [apply sl_cb_nil; lia|].
          change (Z.of_nat (cells_size [CB 0 []])) with 0. rewrite Z.add_0_r. exact C. }
        eapply evt_cut.
        { eapply (sl_loop sp gp tp s10 s11 a0 a1 mx cap out F fc B MC EL HLB HE1 HLG HLE
                   (S (Z.to_nat (2 * (bv_unsigned a1 - 0) + ei)))); [ | exact INV | ];
            [lia | intros D; destruct (OUTC D) as (_ & H1 & _); lia]. }
        intros ms' Hd. unfold sl_done in Hd.
        destruct Hd as (z1 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z18 & z19 & z20
                        & z21 & z22 & z23 & z24 & z25 & z28 & z29 & z30 & z31 & m2 & -> & MU2 & WM2 & MI2 & BL2
                        & C1 & C2 & C3 & C4 & C5 & C6).
        replace (bv_unsigned out + bv_unsigned nout - 0) with (bv_unsigned out + bv_unsigned nout) in MU2 by lia.
        replace (bv_unsigned out + bv_unsigned nout - 0) with (bv_unsigned out + bv_unsigned nout) in C6 by lia.
        replace (0 + bv_unsigned a1) with (bv_unsigned a1) in MU2 by lia.
        destruct Hdd as [-> | ->].
        -- destruct (OUTC eq_refl) as (C0 & N1 & N2 & N3 & N4 & N5). clear C0.
           unfold sl_wit in MU2. cbn [Z.eqb app] in MU2 |- *.
           eapply (rw_cells_transport rsegs _ m1 m2) in FR;
             [ | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize]; lia ].
           eapply (rw_cells_transport rsegs _ m1 m2) in HCL;
             [ | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize]; lia ].
           eapply (stk_transport_disjoint rsegs _ m1 m2) in ST; [ | exact MU2 | exact WM2 | cbn [disjoint_from]; lia ].
           eapply evt_mono;
             [eapply (sl_epi ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); [lia | exact ST | exact FR] |].
           intros ms'' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & STR).
           exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m2.
           split; [reflexivity|].
           split; [eapply munch_trans; [eapply munch_weaken; [|exact MU] | eapply munch_weaken; [|exact MU2]];
                   unfold sub_fp; intros x Hx; cbn [outside app] in *; lia|].
           split; [exact (wmono_trans rsegs _ _ _ WM WM2)|]. split; [exact STR|].
           split; [exact MI2|]. split; [exact BL2|].
           split; [exact HCL|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
           split; [replace (bv_unsigned a1 - 0) with (bv_unsigned a1) in C4 by lia; exact C4|].
           split; [exact C5|].
           intros _. destruct (C6 eq_refl) as (_ & j' & C7).
           apply (sl_cells_app_l rsegs m2 _ [_] [_]) in C7. destruct C7 as [C7 _].
           rewrite firstn_all2 in C7 by lia. exact C7.
        -- unfold sl_wit in MU2. cbn [Z.eqb app] in MU2 |- *.
           eapply (rw_cells_transport rsegs _ m1 m2) in FR;
             [ | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize]; lia ].
           eapply (rw_cells_transport rsegs _ m1 m2) in HCL;
             [ | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize]; lia ].
           eapply (stk_transport_disjoint rsegs _ m1 m2) in ST; [ | exact MU2 | exact WM2 | cbn [disjoint_from]; lia ].
           eapply evt_mono;
             [eapply (sl_epi ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); [lia | exact ST | exact FR] |].
           intros ms'' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & STR).
           exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m2.
           split; [reflexivity|].
           split; [eapply munch_trans; [eapply munch_weaken; [|exact MU] | eapply munch_weaken; [|exact MU2]];
                   unfold sub_fp; intros x Hx; cbn [outside app] in *; lia|].
           split; [exact (wmono_trans rsegs _ _ _ WM WM2)|]. split; [exact STR|].
           split; [exact MI2|]. split; [exact BL2|].
           split; [exact HCL|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
           split; [exact C4|].
           split; [exact C5|].
           intros D; discriminate.
      * if_true.
        assert (Hoff : send_off 3 1 (bv_unsigned a1) = true) by reflexivity.
        sl_off Hoff.
    + step. if_true.
      assert (Hoff : send_off (-1) br (bv_unsigned a1) = true) by reflexivity.
      sl_off Hoff.
Qed.
