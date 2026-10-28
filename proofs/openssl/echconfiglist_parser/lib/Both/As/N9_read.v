(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge TacX SFModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface N6_tac N6_mem_is_zero N6_rip N6_quick N6_strlen.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N8Store.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.   (* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition AREAD_STUB : Z := 0x1a8728.
Definition AREAD_ICPT : Z := 0x1ab658.
(* [comment removed for export] *)
Definition AREAD_ECALL : Z := 0x56aabc.      (* [comment removed for export] *)
Definition AREAD_STACK : Z := 4096.          (* [comment removed for export] *)

Lemma aconst_ok_errno : aconst_ok (12458988, 12458988 + 4).
Proof.
  apply aconst_ok_intro; unfold ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL,
    ACANPOISON_CELL, AF_DCO_CELL, AVERBOSITY_CELL, AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL, sh, AIMG_LO, AIMG_TOP in *; rewrite ?ASHADOW_BASE_val; try lia.
Qed.
End HCW.

Section READ.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (fd buf cnt lo : Z).
  Hypothesis CEIL : aceil <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - AREAD_STACK.
  Hypothesis FDR : 0 <= fd < 2^63.
  Hypothesis BUFR : 0 <= buf.
  Hypothesis CNTR : 0 <= cnt.
  Hypothesis BCR : buf + cnt <= AAPP_HI.

  Notation W := [(bv_unsigned sp - 4096, bv_unsigned sp)].
  Notation FRAME mm := (rw_cells asegs mm (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
Notation FRAMEM mm fj2 := (rw_cells asegs mm (bv_unsigned sp + -2144) [CB 8 fj2; C8 (Z_to_bv 64 0x1ab6a8)]).
  Notation RRD mm := (rw_cells asegs mm AREADP_CELL [C8 (Z_to_bv 64 AREAL_READ)]).

  (* [comment removed for export] *)
  Definition read_at (pc : Z) (x10 : word) (mm : word -> option byte) : machine_state :=
    MS (mkR (Z_to_bv 64 0x570d2c) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp (Z_to_bv 64 buf) x10
             (Z_to_bv 64 buf) (Z_to_bv 64 cnt) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 63)
             (Z_to_bv 64 cnt) (Z_to_bv 64 fd) (Z_to_bv 64 1) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 pc) fc None mm (seg_rom asegs).

  Definition aread_pre_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m' fj fj2,
      ms' = read_at AREAD_ECALL (Z_to_bv 64 fd) m'
      /\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp + -2144)
      /\ FRAME m' /\ rw_cells asegs m' (bv_unsigned sp + -2128) [CB 2080 fj] /\ FRAMEM m' fj2
      /\ ACONST m' /\ RRD m'.

  Ltac prep :=
    intros; acb; unfold AREAD_STACK, AREADP_CELL, AREAL_READ, AREAD_ECALL in *;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; change (2 ^ Z.of_N 64) with (2^64) in SPR.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma aread_pre : forall (a0 a1 a2 : word) (m : word -> option byte),
    a0 = Z_to_bv 64 fd -> a1 = Z_to_bv 64 buf -> a2 = Z_to_bv 64 cnt ->
    stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m -> ACONST m -> RRD m ->
    evt asegs (aread_pre_post m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AREAD_STUB) fc None m (seg_rom asegs)).
  Proof.
    intros a0 a1 a2 m -> -> -> ST0 MI AC RD. unfold AREAD_STUB. prep.
    destruct (ACONST_layout_flag m AC) as (G5 & C5). change (b8 1) with (Z_to_bv 8 1) in C5.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof ST0 as ST. carve_frame 48%nat ST. rename FR into FR1. carve_frame 2080%nat ST. rename FR into FR2.
    zstep. (* [comment removed for export] *)
    do 13 zstep.
    destruct (stk_split asegs _ _ (bv_unsigned sp + -2128 - 16) _ ST ltac:(lia)) as [STlo SThi].
    call2 tryinit_body; try eassumption; rewrite ?unsigned_lit by lia; [exact SThi | lia |].
    try rewrite unsigned_lit in * by lia.
    match goal with Hhi : stk asegs ?mx (bv_unsigned sp + -2128 - 16) (bv_unsigned sp + -2128),
                    Hlo : stk asegs ?mx lo (bv_unsigned sp + -2128 - 16) |- _ =>
      pose proof (stk_merge asegs _ _ _ _ Hlo Hhi ltac:(lia)) as ST; clear Hlo Hhi end.
    do 7 zstep.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    zstep. st1. do 7 zstep. zstep. (* [comment removed for export] *) zstep. (* [comment removed for export] *)
    do 7 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (AC' : ACONST mc)
        by (eapply ACONST_frame; [exact AC | exact MU | exact WM |];
            constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| constructor]) end.
    apply evt_done. unfold aread_pre_post, read_at. do 3 eexists.
    split; [reflexivity|]. repeat (split; [(first [exact MU | exact WM | exact MI0 | exact ST | exact FR1 | exact FR2 | exact FR | exact AC' | eassumption])|]). eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition aread_ret_post (x10 : word) (m2 : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m3,
      ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (ret_pc ra) fc None m3 (seg_rom asegs)
      /\ munch W m2 m3 /\ wmono asegs m2 m3 /\ mem_inv asegs m3
      /\ stk asegs m3 lo (bv_unsigned sp) /\ ACONST m3.

  (* [comment removed for export] *)
  Notation RST pc x1 x5 x10 x11 x12 x13 x14 x15 x16 x17 x18 x9 x20 mm :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 t1 t2 sp x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 fd) x20
             s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Section POST.
    Variables (m2 : word -> option byte) (fj : list byte) (r : Z).

    (* [comment removed for export] *)
    Section EPI.
      Variables (mm : word -> option byte).
      Hypothesis MIm : mem_inv asegs mm.
      Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2128).
      Hypothesis FRm : FRAME mm.
      Hypothesis FR2m : rw_cells asegs mm (bv_unsigned sp + -2128) [CB 2080 fj].
      Hypothesis MU : munch W m2 mm.
      Hypothesis WM : wmono asegs m2 mm.
      Hypothesis ACm : ACONST mm.
      (* [comment removed for export] *)
      Lemma ar_epi : forall (x1 x5 x10 x11 x12 x13 x14 x15 x16 x17 x18 x9 x20 : word),
        evt asegs (aread_ret_post x10 m2) (RST 0x1ab708 x1 x5 x10 x11 x12 x13 x14 x15 x16 x17 x18 x9 x20 mm).
      Proof.
        prep. do 8 zstep. zstep.
        pose proof STm as ST. release_frame FR2m ST (bv_unsigned sp + -48). release_frame FRm ST (bv_unsigned sp).
        unfold aread_ret_post. finish.
      Qed.
    End EPI.

    (* [comment removed for export] *)
    Section JR.
      Variables (mm : word -> option byte).
      Hypothesis MIm : mem_inv asegs mm.
      Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2128).
      Hypothesis FRm : FRAME mm.
      Hypothesis FR2m : rw_cells asegs mm (bv_unsigned sp + -2128) [CB 2080 fj].
      Hypothesis MU : munch W m2 mm.
      Hypothesis WM : wmono asegs m2 mm.
      Hypothesis ACm : ACONST mm.
      Hypothesis RP : 0 < r <= 2^40.
      Hypothesis RC : r <= cnt.
      Hypothesis ACC : accessible mm buf r.
      Hypothesis INM : in_app_mem buf (buf + r).
      Lemma ar_jr : forall (x1 x5 x11 x12 x13 x14 x15 x16 x17 x20 : word),
        evt asegs (aread_ret_post (Z_to_bv 64 r) m2) (RST 0x1ab7a4 x1 x5 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 cnt) (Z_to_bv 64 buf) x20 mm).
      Proof using HCEIL ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc fd buf cnt lo CEIL LO FDR BUFR BCR m2 fj r mm MIm STm FRm FR2m MU WM ACm RP RC ACC INM.
        prep. pose proof BCR as BCR'. unfold AAPP_HI in BCR'.
        pose proof INM as INM'. unfold in_app_mem, AHI_LO, AAPP_HI in INM'. rewrite ASHADOW_BASE_val in INM'.
        do 3 zstep.
        zstep. call2 rip_body_w; try eassumption; rewrite ?unsigned_lit by (first [clear - INM' RP SPR ACEILB LO CEIL; lia | lia]);
          [ exact ACC | lia | exact INM | exact STm | unfold RIP_STACK; lia | unfold AHI_LO; lia | ].
        try rewrite unsigned_lit in * by lia.
        do 2 zstep.
        zstep. if_cases K; zify_cond K; [| exfalso; (first [clear - FDR K; lia | lia])].
        eapply ar_epi; try eassumption.
      Qed.
    End JR.

    (* [comment removed for export] *)
    Section JQ.
      Variables (mm : word -> option byte).
      Hypothesis MIm : mem_inv asegs mm.
      Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2128).
      Hypothesis FRm : FRAME mm.
      Hypothesis FR2m : rw_cells asegs mm (bv_unsigned sp + -2128) [CB 2080 fj].
      Hypothesis MU : munch W m2 mm.
      Hypothesis WM : wmono asegs m2 mm.
      Hypothesis ACm : ACONST mm.
      Hypothesis RP : 0 < r <= 2^40.
      Hypothesis RC : r <= cnt.
      Hypothesis ACC : accessible mm buf r.
      Hypothesis INM : in_app_mem buf (buf + r).
      Hypothesis N64 : 1 <= r <= 64.
      Hypothesis SVm : stk asegs mm (sh (hull_lo buf)) (sh (hull_hi (buf + r))).

      Let LAY := ACONST_layout mm ACm.

      (* [comment removed for export] *)
      Lemma ar_j4c : forall (x1 x5 x11 x12 x13 x14 x15 x16 x17 x20 : word),
        evt asegs (aread_ret_post (Z_to_bv 64 r) m2) (RST 0x1ab87c x1 x5 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 cnt) (Z_to_bv 64 buf) x20 mm).
      Proof using HCEIL ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc fd buf cnt lo CEIL LO FDR BUFR BCR m2 fj r mm MIm STm FRm FR2m MU WM ACm RP RC ACC INM.
        intros. zstep. zstep. if_cases K.
        - eapply ar_epi; eassumption.
        - zstep. eapply ar_jr; eassumption.
      Qed.

      Section Loop.
        Variables (q1 : Z) (qj : list byte).
        Hypothesis QA : u8arr asegs mm (8 * q1) qj.
        Hypothesis QB : 8 * q1 <= sh buf /\ sh (buf + r - 1) < 8 * q1 + Z.of_nat (length qj).
        Hypothesis SR12 : 2147450880 <= sh buf /\ sh (buf + r - 1) < 17594333495296.
        Lemma ar_loop : forall (k : nat) (i : Z) (x1 x5 x13 x14 x15 x16 x17 x20 : word),
          Z.to_nat (sh (buf + r - 1) - (sh buf + i)) = k -> 0 <= i -> sh buf + i < sh (buf + r - 1) ->
          evt asegs (aread_ret_post (Z_to_bv 64 r) m2)
              (RST 0x1ab86c x1 x5 (Z_to_bv 64 r) (Z_to_bv 64 (sh buf + i)) (Z_to_bv 64 (sh (buf + r - 1))) x13 x14 x15 x16 x17 (Z_to_bv 64 cnt) (Z_to_bv 64 buf) x20 mm).
        Proof using HCEIL ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc fd buf cnt lo CEIL LO FDR BUFR BCR m2 fj r mm MIm STm FRm FR2m MU WM ACm RP RC ACC INM q1 qj QA QB SR12.
          induction k as [k IH] using lt_wf_ind; intros i x1 x5 x13 x14 x15 x16 x17 x20 Hk Hi Hlt.
          pose proof (q_read mm q1 qj QA (sh buf + i) ltac:(lia)) as RD.
          do 3 zstep.
          zstep. if_cases K; zify_cond K.
          - replace (sh buf + i + 1) with (sh buf + (i + 1)) by lia.
            eapply (IH (Z.to_nat (sh (buf + r - 1) - (sh buf + (i + 1))))); first [(first [clear - Hlt Hk ACm Hi K; lia | lia]) | exact (Z_to_bv 64 0)].
          - apply ar_j4c.
        Qed.
      End Loop.

      Lemma ar_jq : forall (x1 x5 x11 x12 x13 x14 x15 x16 x17 x20 : word),
        evt asegs (aread_ret_post (Z_to_bv 64 r) m2) (RST 0x1ab6cc x1 x5 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 cnt) (Z_to_bv 64 buf) x20 mm).
      Proof.
        prep. pose proof BCR as BCR'. unfold AAPP_HI in BCR'.
        pose proof INM as INM'. unfold in_app_mem, AHI_LO, AAPP_HI in INM'. rewrite ASHADOW_BASE_val in INM'.
        destruct LAY as (G1 & C1 & G2 & G3 & G4 & C4).
        destruct (hull_words buf r ltac:(lia) N64) as (HLO & HHI & HQ2 & HB1 & HB2 & HB3).
        pose proof (sh_range_app buf ltac:(unfold AAPP_HI; lia)) as SR1.
        pose proof (sh_range_app (buf + r - 1) ltac:(unfold AAPP_HI; lia)) as SR2.
        unfold AHI_LO in SR1, SR2. rewrite ASHADOW_BASE_val in SR1, SR2.
        destruct (hull_chunk mm buf r ltac:(lia) N64 ltac:(lia) SVm) as (qj & QW & QL & QL2).
        pose proof (u8arr_of_rw_cells asegs mm _ _ _ QW) as QA.
        set (q1 := sh buf / 8) in *. set (q2 := sh (buf + r - 1) / 8) in *.
        assert (QB : 8 * q1 <= sh buf /\ sh (buf + r - 1) < 8 * q1 + Z.of_nat (length qj)) by lia.
        assert (SR12 : 2147450880 <= sh buf /\ sh (buf + r - 1) < 17594333495296) by lia.
        do 9 zstep. try replace (buf + r + -1) with (buf + r - 1) by lia. rewrite !shr3_sh by lia.
        do 2 zstep. rewrite !land_m8 by lia. fold q1. fold q2.
        destruct QL2 as [[E L]|[E L]]; rewrite E in QL |- *; rewrite L in QW, QL.
        - do 3 zstep. zstep. if_cases K0.
          + pose proof (q_read mm q1 qj QA (sh (buf + r - 1)) ltac:(lia)) as RD.
            do 6 zstep.
            zstep. if_cases K1; zify_cond K1.
            * apply ar_j4c.
            * replace (Z_to_bv 64 (sh buf)) with (Z_to_bv 64 (sh buf + 0)) by (f_equal; lia).
              eapply (ar_loop q1 qj); first [eassumption | reflexivity | lia].
          + eapply ar_epi; [exact MIm | exact STm | exact FRm | exact FR2m | exact MU | exact WM | exact ACm].
        - replace (8 * (q1 + 1)) with (8 * q1 + 8) by lia.
          do 3 zstep. zstep. if_cases K0.
          + pose proof (q_read mm q1 qj QA (sh (buf + r - 1)) ltac:(lia)) as RD.
            do 6 zstep.
            zstep. if_cases K1; zify_cond K1.
            * apply ar_j4c.
            * replace (Z_to_bv 64 (sh buf)) with (Z_to_bv 64 (sh buf + 0)) by (f_equal; lia).
              eapply (ar_loop q1 qj); first [eassumption | reflexivity | lia].
          + eapply ar_epi; [exact MIm | exact STm | exact FRm | exact FR2m | exact MU | exact WM | exact ACm].
      Qed.
    End JQ.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Variables (fj2 : list byte).
    Hypothesis MI2 : mem_inv asegs m2.
    Hypothesis ST2 : stk asegs m2 lo (bv_unsigned sp + -2144).
    Hypothesis FR1 : FRAME m2.
    Hypothesis FR2 : rw_cells asegs m2 (bv_unsigned sp + -2128) [CB 2080 fj].
    Hypothesis FR3 : FRAMEM m2 fj2.
    Hypothesis AC2 : ACONST m2.

    (* [comment removed for export] *)
    Lemma aread_post_zero :
      evt asegs (aread_ret_post (Z_to_bv 64 0) m2) (read_at (AREAD_ECALL + 4) (Z_to_bv 64 0) m2).
    Proof.
      prep. unfold read_at. change (5679804 + 4) with 5679808.
      pose proof (munch_refl W m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      zstep. (* [comment removed for export] *) zstep. (* [comment removed for export] *) zstep. (* [comment removed for export] *)
      pose proof ST2 as ST. release_frame FR3 ST (bv_unsigned sp + -2128).
      zstep. (* [comment removed for export] *) do 2 zstep.
      zstep. if_cases K; zify_cond K; [| exfalso; revert K; rewrite ?unsigned_lit by lia; vm_compute; lia || lia].
      zstep. (* [comment removed for export] *)
      zstep. if_cases K1; [exfalso; revert K1; vm_compute; discriminate|].
      zstep. if_cases K2; zify_cond K2; [| exfalso; lia].
      eapply ar_epi; eassumption.
    Qed.

    (* [comment removed for export] *)
    Lemma aread_post_pos :
      0 < r <= cnt -> r <= 2^40 ->
      accessible m2 buf r -> shvis m2 buf (buf + r) -> in_app_mem buf (buf + r) ->
      evt asegs (aread_ret_post (Z_to_bv 64 r) m2) (read_at (AREAD_ECALL + 4) (Z_to_bv 64 r) m2).
    Proof.
      intros RP R40 ACC SV INM. prep. unfold read_at. change (5679804 + 4) with 5679808.
      pose proof BCR as BCR'. unfold AAPP_HI in BCR'.
      pose proof INM as INM'. unfold in_app_mem, AHI_LO, AAPP_HI in INM'. rewrite ASHADOW_BASE_val in INM'.
      pose proof (munch_refl W m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      zstep. (* [comment removed for export] *) zstep. (* [comment removed for export] *) zstep. (* [comment removed for export] *)
      pose proof ST2 as ST. release_frame FR3 ST (bv_unsigned sp + -2128).
      zstep. (* [comment removed for export] *) do 2 zstep.
      zstep. if_cases K; zify_cond K; [| exfalso; lia].
      zstep. (* [comment removed for export] *)
      zstep. if_cases K1; [exfalso; revert K1; vm_compute; discriminate|].
      zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
      zstep. zstep. zstep.
      zstep. if_cases K5; zify_cond K5; rewrite ?lxor_ones64 in K5 by lia; [exfalso; lia|].
      zstep. zstep.
      zstep. if_cases K6; zify_cond K6; rewrite ?land_ones64 in K6.
      - eapply ar_jr; try eassumption; lia.
      - eapply ar_jq; try eassumption; try (first [clear - FDR RP R40 ACEILB K3 K6; lia | lia]); try exact SV; Z.div_mod_to_equations; lia.
    Qed.
  End POST.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition aread_err_post (e : Z) (m2 : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m3,
      ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (ret_pc ra) fc None m3 (seg_rom asegs)
      /\ bv_unsigned x10 = 2^64 - 1
      /\ munch ((AERRNO, AERRNO + 4) :: W) m2 m3 /\ wmono asegs m2 m3 /\ mem_inv asegs m3
      /\ stk asegs m3 lo (bv_unsigned sp) /\ ACONST m3
      /\ rw_cells asegs m3 AERRNO [C4 (Z_to_bv 64 e)].

  Lemma aread_post_err : forall (m2 : word -> option byte) (fj fj2 : list byte) (e : Z) (errv : word),
    mem_inv asegs m2 -> stk asegs m2 lo (bv_unsigned sp + -2144) ->
    FRAME m2 -> rw_cells asegs m2 (bv_unsigned sp + -2128) [CB 2080 fj] -> FRAMEM m2 fj2 -> ACONST m2 ->
    tp = Z_to_bv 64 ATP -> rw_cells asegs m2 AERRNO [C4 errv] ->
    1 <= e <= 4095 ->
    evt asegs (aread_err_post e m2) (read_at (AREAD_ECALL + 4) (Z_to_bv 64 (2^64 - e)) m2).
  Proof.
    intros m2 fj fj2 e errv MI2 ST2 FR1 FR2 FR3 AC2 TP ERR HE. prep. unfold read_at. change (5679804 + 4) with 5679808.
    assert (ETP : bv_unsigned tp = 12459152) by (rewrite TP; apply unsigned_lit; lia).
    assert (ERR' : rw_cells asegs m2 (bv_unsigned tp + -164) [C4 errv]) by (rewrite ETP; exact ERR). clear ERR.
    unfold AERRNO, ATP. change (12459152 - 164) with 12458988.
    pose proof (munch_refl ((12458988, 12458988 + 4) :: W) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    zstep. (* [comment removed for export] *) zstep. (* [comment removed for export] *) zstep. (* [comment removed for export] *)
    pose proof ST2 as ST. release_frame FR3 ST (bv_unsigned sp + -2128).
    zstep. (* [comment removed for export] *) do 2 zstep.
    zstep. if_cases K; zify_cond K; [exfalso; lia|].
    zstep. carve_frame 16%nat ST. st1. st1.
    zstep. (* [comment removed for export] *)
    replace (Z_to_bv 64 (bv_swrap 32 (0 - (18446744073709551616 - e)))) with (Z_to_bv 64 e)
      by (f_equal; unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus; cbn -[Z.add Z.sub Z.mul Z.modulo Z.opp Z.pow]; Z.div_mod_to_equations; lia).
    zstep. (* [comment removed for export] *) zstep. zstep. zstep. (* [comment removed for export] *)
    st1. (* [comment removed for export] *)
    do 4 zstep. zstep. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp + -2128).
    zstep. if_cases K1; [exfalso; revert K1; vm_compute; discriminate|].
    zstep. if_cases K2; [ | exfalso; revert K2; vm_compute; discriminate ].
    (* [comment removed for export] *)
    do 8 zstep. zstep.
    release_frame FR2 ST (bv_unsigned sp + -48). release_frame FR1 ST (bv_unsigned sp).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (ACf : ACONST mc)
        by (eapply ACONST_frame; [exact AC2 | exact MU | exact WM |];
            constructor; [exact aconst_ok_errno|];
            constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| constructor]) end.
    apply evt_done. unfold aread_err_post. unfold AERRNO, ATP. change (12459152 - 164) with 12458988.
    do 16 eexists. split; [reflexivity|]. split; [vm_compute; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact ACf|].
    match goal with H : rw_cells asegs _ (bv_unsigned tp + -164) _ |- _ => rewrite ETP in H; change (12459152 + -164) with 12458988 in H; exact H end.
  Qed.
End READ.

