(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun Stdio_pure.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ShadowTac F_irt F_rip I_printf_lib.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

(* [comment removed for export] *)
Local Ltac mem_after_store ::= cbv beta; try rewrite le1_unsigned8; mem_after_store_fast.

Section CANSEC1. Context {rc : runConstT}.
Section PC.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (FMT : Z) (fstr : list byte).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2320)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis A1 : a1 = Z_to_bv 64 FMT.
  Hypothesis FB : bytes_at bsegs m FMT (fstr ++ [Z_to_bv 8 0]).
  Hypothesis NOZ : Forall (fun b : byte => bv_unsigned b <> 0%Z) fstr.
  Notation L := (Z.of_nat (length fstr)).
  Hypothesis FL : (1 <= L <= 62)%Z.
  Hypothesis FIMG : (0x10000 <= FMT /\ FMT + L + 1 <= 0x625000)%Z.
  Notation SLO := (shad (FMT - 64))%Z.
  Notation SHI := (shad (FMT + L + 64))%Z.
  Hypothesis FZ : shadow_bytes m SLO SHI (fun _ => 0%Z).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RSHF : rng RNG SLO (SHI - SLO).

  Notation W := [(bv_unsigned sp + -2320, bv_unsigned sp)]%Z.
  Notation SAVES := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation PAT := 12297829382473034410%Z.

  (* [comment removed for export] *)
  Definition INV (mc : word -> option byte) : Prop :=
    rw_cells bsegs mc (bv_unsigned sp + -104) SAVES
    /\ (exists j0, rw_cells bsegs mc (bv_unsigned sp + -2240) [CB 8 j0; C8 (Z_to_bv 64 (bv_unsigned sp + -120)); C8 a0])
    /\ stk bsegs mc (bv_unsigned sp + -2176) (bv_unsigned sp + -104)
    /\ stk bsegs mc lo (bv_unsigned sp + -2240)
    /\ munch W m mc /\ wmono bsegs m mc /\ mem_inv bsegs mc /\ rt_got mc /\ rt_shbase mc.

  Definition BL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2320 /\ 17594333495296 <= lo /\ bv_unsigned sp < 2^64
     /\ 65536 <= FMT /\ FMT + L + 1 <= 6443008 /\ 1 <= L <= 62
     /\ 8192 <= Z.shiftr FMT 3 /\ Z.shiftr FMT 3 <= Z.shiftr (FMT + L) 3 /\ Z.shiftr (FMT + L) 3 <= Z.shiftr FMT 3 + 8 /\ Z.shiftr (FMT + L) 3 <= 999999
     /\ shad (FMT - 64) = 2147450872 + Z.shiftr FMT 3 /\ shad (FMT + L + 64) = 2147450888 + Z.shiftr (FMT + L) 3)%Z.
  Lemma BL_ok : BL.
  Proof.
    unfold BL. pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R.
    destruct ST as (L0 & _). unfold KHIGH in KLO. rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac hide_sec :=
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in GOT;
    change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in FB;
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO.
  Ltac inv_open H := let j0 := fresh "j0" in destruct H as (FRT & (j0 & FRL) & STM & ST1 & MU1 & WM1 & MI1 & GOT1 & SHB1).
  Ltac prep IV :=
    inv_open IV;
    let B := fresh "B" in pose proof BL_ok as B; unfold BL in B;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2320) 2320) by (eapply rng_sub'; [exact RSTK| lia]);
    hide_sec.

  (* [comment removed for export] *)
  Lemma fmt_rd : forall mc (i : Z) b, mem_inv bsegs mc -> munch W m mc ->
    nth_error (fstr ++ [Z_to_bv 8 0]) (Z.to_nat i) = Some b -> (0 <= i)%Z ->
    ov_read_bytes bsegs mc (wa (FMT + i)) 1 = Some [b].
  Proof.
    intros mc i b MIc MUc Hn Hi. pose proof BL_ok as B; unfold BL in B.
    eapply u8ro_read; [| exact Hn | exact Hi | reflexivity].
    eapply bytes_at_transport; [exact FB | exact MUc |]. rewrite length_app; cbn [length disjoint_from]. lia.
  Qed.

  Ltac fmt_read i b Hn :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      lazymatch goal with MUc : munch _ m mc, MIc : mem_inv _ mc |- _ =>
        let H := fresh "RD" in
        pose proof (fmt_rd mc i b MIc MUc ltac:(rewrite nth_error_app1 by lia; exact Hn) ltac:(lia)) as H
    end end.

  (* [comment removed for export] *)
  Ltac prem :=
    lazymatch goal with
    | |- evtF _ _ _ _ => idtac
    | |- mem_inv _ _ => first [assumption | eassumption | idtac "prem: mem_inv"; fail]
    | |- context [bv_unsigned (Z_to_bv 64 _)] => rewrite !unsigned_lit by lia; prem
    | |- stk _ _ _ _ => first [assumption | eassumption | idtac "prem: stk"; fail]
    | |- find_byte _ _ = _ => first [eassumption | idtac "prem: find_byte"; fail]
    | |- rw_cells _ _ _ _ => first [eassumption | idtac "prem: rw_cells"; fail]
    | |- u8arr _ _ _ _ => first [eassumption | idtac "prem: u8arr"; fail]
    | |- bytes_at _ _ _ _ => first [eassumption | first [apply flags_bytes | apply jzt_bytes | apply ccss_bytes | apply aefg_bytes | apply dioux_bytes | apply cs_bytes | apply csb_bytes | apply ss_bytes | idtac "prem: bytes_at"; fail]; assumption]
    | |- Forall _ _ => first [exact flags_noz | exact jzt_noz | exact ccss_noz | exact aefg_noz | exact dioux_noz | exact cs_noz | exact csb_noz | exact ss_noz | assumption | idtac "prem: Forall"; fail]
    | |- _ = Z_to_bv 64 _ => first [reflexivity | idtac "prem: eq"; fail]
    | |- rng _ _ _ => first [ assumption | eapply rng_sub'; [exact RI | cbn; unfold sf_hide in *; lia] | eapply rng_sub'; [exact RSTK | unfold sf_hide in *; lia] | idtac "prem: rng"; fail ]
    | |- ?g => unfold sf_hide in *; first [lia | cbv; discriminate | cbn; lia | idtac "prem: other" g; fail]
    end.

  (* [comment removed for export] *)
  Ltac br CC := let K := fresh "K" in if_cases K; zify_cond K; try (exfalso; clear -K CC; lia); [clear K].

  Notation CONT Q x19v x21v mc dcs :=
    (forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp y9 y10 y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 10) x19v (Z_to_bv 64 0x15307) x21v y22 (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
                 (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31)
             F (Z_to_bv 64 0x46bd4) fc None mc (seg_rom bsegs))) (only parsing).

  (* [comment removed for export] *)
  Lemma L_entry : forall Q,
    (forall mc dj, INV mc -> rw_cells bsegs mc (bv_unsigned sp + -2216) [CB 40 dj] ->
       forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp y9 y10 y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 10) (Z_to_bv 64 FMT) (Z_to_bv 64 0x15307) a2 y22 (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
                 (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31)
             F (Z_to_bv 64 0x46bd4) fc None mc (seg_rom bsegs))) ->
    evtF bsegs RNG Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x46ac0) fc None m (seg_rom bsegs)).
  Proof.
    intros Q K.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
    pose proof BL_ok as B; unfold BL in B.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2320) 2320) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof MI as MIc. pose proof FB as FBc. pose proof GOT as GOTc. pose proof SHB as SHBc. pose proof ST as ST0.
    hide_sec.
    subst a1.
    carve_frame 104%nat ST0.
    destruct (stk_split _ _ lo (bv_unsigned sp + -2176) _ ST0 ltac:(lia)) as [ST1 STM]. clear ST0.
    carve_frame 40%nat ST1. carve_frame 24%nat ST1.
    do 16 zstep. do 6 zstep. zstep.
    call istrlen_spec; [ exact MIc | rewrite unsigned_lit by lia; exact FBc | exact NOZ | rewrite unsigned_lit by lia; eapply rng_sub'; [exact RI| lia] | ].
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m mc |- _ =>
      pose proof (shadow_bytes_munch _ m mc _ _ _ FZ MUc ltac:(cbn [disjoint_from]; lia)) as FZ1 end end.
    zstep. zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. clear - K1 B. lia. } clear K1.
    zstep. zstep. if_cases K2; zify_cond K2. { exfalso. clear - K2 B. lia. } clear K2.
    do 4 zstep. replace (L + FMT)%Z with (FMT + L)%Z by lia. do 6 zstep.
    change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (ov_read8_zero bsegs mc _ _ _ (2147450880 + Z.shiftr FMT 3 - (2147450880 + Z.shiftr FMT 3) mod 8)%Z FZ1
                    ltac:(clear -B; Z.div_mod_to_equations; lia) ltac:(clear -B; Z.div_mod_to_equations; lia) ltac:(intros; reflexivity)) as P1;
      pose proof (ov_read8_zero bsegs mc _ _ _ (2147450880 + Z.shiftr (FMT + L) 3 - (2147450880 + Z.shiftr (FMT + L) 3) mod 8)%Z FZ1
                    ltac:(clear -B; Z.div_mod_to_equations; lia) ltac:(clear -B; Z.div_mod_to_equations; lia) ltac:(intros; reflexivity)) as P2
    end.
    zs. zs. zs. fold_lits. zs. if_cases K3; zify_cond K3. { exfalso. clear - K3. lia. } clear K3 P1 P2.
    do 3 zs.
    (* [comment removed for export] *)
    destruct (nth_error fstr 0) as [c0|] eqn:E0. 2:{ exfalso. apply nth_error_None in E0. lia. }
    assert (NZ0 : bv_unsigned c0 <> 0%Z) by (eapply (proj1 (Forall_forall _ _) NOZ); eapply nth_error_In; exact E0).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m mc, MIc : mem_inv _ mc |- _ =>
      pose proof (fmt_rd mc 0 c0 MIc MUc ltac:(rewrite nth_error_app1 by lia; exact E0) ltac:(lia)) as RD0; rewrite Z.add_0_r in RD0 end end.
    zs. zs. if_cases K4; zify_cond K4. { exfalso. clear - K4 NZ0. pose proof (bv_unsigned_in_range 8 c0). cbn in *. lia. } clear K4 RD0.
    do 17 zs.
    eapply K. 2:{ exact FR0. }
    split; [exact FR|]. split; [eexists; exact FR1|]. unfold sf_hide in *. repeat (split; [assumption|]). assumption.
  Qed.


  Notation dcells1 :=
    ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 18446744073709551615); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3)]) (only parsing).

  (* [comment removed for export] *)
  Definition lregs (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 : word) (p aq : word) (y22 y28 y29 y30 y31 : word) :=
    mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp y9 y10 y11 y12 y13 y14 y15 y16 y17
        (Z_to_bv 64 10) p (Z_to_bv 64 0x15307) aq y22 (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
        (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31.

  (* [comment removed for export] *)
  Lemma L_head : forall Q mc dcs p aq,
    INV mc -> rw_cells bsegs mc (bv_unsigned sp + -2216) dcs -> cells_size dcs = 40%nat ->
    (forall mc', INV mc' -> rw_cells bsegs mc' (bv_unsigned sp + -2216) dcells1 ->
       forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evtF bsegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 p aq y22 y28 y29 y30 y31)
                           F (Z_to_bv 64 0x46c00) fc None mc' (seg_rom bsegs))) ->
    forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
    evtF bsegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 p aq y22 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x46bd4) fc None mc (seg_rom bsegs)).
  Proof.
    intros Q mc dcs p aq IV DIR SZ K. intros. unfold lregs. prep IV.
    destruct (rw_cells_forget _ _ _ _ DIR) as [dj DJ]. rewrite SZ in DJ. clear DIR.
    do 5 zs. do 5 zs.
    destruct (u8arr_of_chunk _ _ _ _ DJ) as (dj2 & DA & DL). cbn in DL. clear DJ.
    call imemset_specZ; [ exact MI1 | exact DA | rewrite DL; reflexivity | lia | lia | lia | cbv; discriminate | ].
    match goal with H : u8arr bsegs ?mc _ _ |- _ => rewrite ?unsigned_lit in H by lia;
      apply rw_cells_of_u8arr in H; recell H 0%nat 1%nat (zcells0 : list cell); rename H into DIR end.
    zs.
    eapply K. 2:{ exact DIR. }
    split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
  Qed.


  (* [comment removed for export] *)
  Lemma fmt_char : forall mc (i : Z), mem_inv bsegs mc -> munch W m mc -> (0 <= i < L)%Z ->
    exists b, nth_error fstr (Z.to_nat i) = Some b /\ bv_unsigned b <> 0%Z /\ (0 <= bv_unsigned b < 256)%Z /\
              ov_read_bytes bsegs mc (wa (FMT + i)) 1 = Some [b].
  Proof.
    intros mc i MIc MUc Hi.
    destruct (nth_error fstr (Z.to_nat i)) as [b|] eqn:E. 2:{ exfalso. apply nth_error_None in E. lia. }
    exists b. split; [reflexivity|]. split.
    { eapply (proj1 (Forall_forall _ _) NOZ). eapply nth_error_In; exact E. }
    split. { pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. }
    eapply fmt_rd; [exact MIc | exact MUc | rewrite nth_error_app1 by lia; exact E | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma L_skip : forall Q mc (k : nat) (i : Z) aq,
    mem_inv bsegs mc -> munch W m mc -> (0 <= i)%Z -> (i + Z.of_nat k <= L)%Z ->
    (forall j b, (Z.to_nat i <= j < Z.to_nat i + k)%nat -> nth_error fstr j = Some b -> bv_unsigned b <> 37%Z) ->
    (forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evtF bsegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + (i + Z.of_nat k))) aq y22 y28 y29 y30 y31)
                           F (Z_to_bv 64 0x46c00) fc None mc (seg_rom bsegs))) ->
    forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
    evtF bsegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i)) aq y22 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x46c00) fc None mc (seg_rom bsegs)).
  Proof.
    intros Q mc k. induction k as [|k IH]; intros i aq MIc MUc Hi Hk NP K; intros.
    - specialize (K y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31).
      rewrite Z.add_0_r in K. exact K.
    - pose proof BL_ok as B; unfold BL in B. unfold lregs.
      destruct (fmt_char mc i MIc MUc ltac:(lia)) as (b & Hn & NZ & RB & RD).
      assert (NP0 : bv_unsigned b <> 37%Z) by (eapply NP; [|exact Hn]; lia).
      zs. zs. if_cases K1; zify_cond K1. { exfalso. clear -K1 NP0 RB. lia. }
      zs. if_cases K2; zify_cond K2. { exfalso. clear -K2 NZ RB. lia. }
      zs. zs. zs.
      replace (FMT + i + 1)%Z with (FMT + (i + 1))%Z by lia.
      eapply (IH (i + 1)%Z); [exact MIc | exact MUc | lia | lia | | ].
      { intros j b' Hj Hb'. eapply NP; [|exact Hb']. lia. }
      intros. replace (i + 1 + Z.of_nat k)%Z with (i + Z.of_nat (S k))%Z by lia. apply K.
  Qed.


  (* [comment removed for export] *)
  Definition dirA_ok (c : Z) : Prop :=
    find_byte c B_FLAGS = None /\ find_byte c B_JZT = None /\ (58 <= c < 256)%Z /\ c <> 108%Z /\ c <> 104%Z.
  (* [comment removed for export] *)
  Definition intconv (c : Z) : Prop := c = 100%Z \/ c = 117%Z.
  Lemma cfacts : forall c, intconv c ->
    dirA_ok c /\ find_byte c B_CCSS = None /\ find_byte c B_AEFG = None
    /\ (exists ix, find_byte c B_DIOUX = Some ix) /\ (58 <= c < 256)%Z /\ c <> 109%Z /\ c <> 110%Z.
  Proof. intros c [-> | ->]; repeat split; try (cbv; reflexivity); try lia; eexists; cbv; reflexivity. Qed.
  (* [comment removed for export] *)
  Definition sconv (c : Z) : Prop := c = 115%Z.
  Lemma sfacts : forall c, sconv c ->
    dirA_ok c /\ (58 <= c < 256)%Z /\ c <> 109%Z /\ c <> 110%Z
    /\ find_byte c B_CCSS = Some 2%nat /\ find_byte c B_CS = None /\ find_byte c B_CSB = Some 1%nat /\ find_byte c B_SS = Some 0%nat.
  Proof. intros c ->; repeat split; try (cbv; reflexivity); lia. Qed.

  Lemma istrchr_res_none : forall A str c, find_byte c str = None -> istrchr_res A str c = 0%Z.
  Proof. intros A str c H. unfold istrchr_res. rewrite H. reflexivity. Qed.

  Notation dcellsA p bc :=
    ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 18446744073709551615); C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 (p + 2));
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 bc; CB 3 (repeat (Z_to_bv 8 0) 3)]) (only parsing).

  (* [comment removed for export] *)
  Lemma L_dirA : forall Q mc (i : Z) aq b37 bc,
    INV mc -> rw_cells bsegs mc (bv_unsigned sp + -2216) dcells1 ->
    (0 <= i)%Z -> (i + 2 <= L)%Z ->
    nth_error fstr (Z.to_nat i) = Some b37 -> bv_unsigned b37 = 37%Z ->
    nth_error fstr (Z.to_nat (i + 1)) = Some bc -> dirA_ok (bv_unsigned bc) ->
    (forall mc', INV mc' -> rw_cells bsegs mc' (bv_unsigned sp + -2216) (dcellsA (FMT + i) bc) ->
       forall y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp (Z_to_bv 64 (FMT + i)) (Z_to_bv 64 (bv_unsigned bc)) y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 10) (Z_to_bv 64 (FMT + i + 2)) (Z_to_bv 64 0x15307) aq (Z_to_bv 64 (FMT + i + 1)) (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
                 (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31)
                           F (Z_to_bv 64 0x46d7c) fc None mc' (seg_rom bsegs))) ->
    forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
    evtF bsegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i)) aq y22 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x46c00) fc None mc (seg_rom bsegs)).
  Proof.
    intros Q mc i aq b37 bc IV DIR Hi HiL H37 E37 Hc HC K. intros. unfold lregs. prep IV.
    destruct HC as (NF1 & NF2 & CR & N108 & N104).
    pose proof (conj CR (conj N108 N104)) as CC.
    fmt_read i b37 H37. zs. clear RD. cbv beta. rewrite E37. zs. br CC.
    (* [comment removed for export] *) zs. fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta.
    zs. br CC.
    (* [comment removed for export] *) zs. br CC.
    zs. zs. zs. br CC.
    (* [comment removed for export] *) zs. fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta. zs. zs. zs.
    call istrchr_spec; [ eassumption | apply flags_bytes; assumption | exact flags_noz | reflexivity | clear -CC; lia
                       | rewrite unsigned_lit by lia; eapply rng_sub'; [exact RI | cbn; lia] | ].
    rewrite (istrchr_res_none _ _ _ NF1).
    (* [comment removed for export] *) zs. zs. zs. br CC.
    replace (FMT + (i + 1) + 1 + -1)%Z with (FMT + (i + 1))%Z by lia.
    fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta. zs. zs. br CC.
    (* [comment removed for export] *) zs. replace (FMT + (i + 1) + 1 + -1)%Z with (FMT + (i + 1))%Z by lia.
    zs. fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta. zs. zs. br CC.
    (* [comment removed for export] *) zs. zs. br CC.
    (* [comment removed for export] *) zs. fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta. zs. zs. zs.
    call istrchr_spec; [ eassumption | apply jzt_bytes; assumption | exact jzt_noz | reflexivity | clear -CC; lia
                       | rewrite unsigned_lit by lia; eapply rng_sub'; [exact RI | cbn; lia] | ].
    rewrite (istrchr_res_none _ _ _ NF2).
    (* [comment removed for export] *) fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta. zs. br CC.
    (* [comment removed for export] *) zs. zs. br CC. zs. zs. br CC.
    (* [comment removed for export] *) fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta. zs. zs. zs.
    zs. br CC.
    replace (FMT + (i + 1) + 1)%Z with (FMT + i + 2)%Z by lia. replace (FMT + (i + 1))%Z with (FMT + i + 1)%Z by lia.
    eapply K. 2:{ match goal with H : rw_cells bsegs _ (bv_unsigned sp + -2216) _ |- _ => exact H end. }
    split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
  Qed.


  (* [comment removed for export] *)
  Lemma L_dirB : forall Q mc (i : Z) aq bc,
    INV mc -> rw_cells bsegs mc (bv_unsigned sp + -2216) (dcellsA (FMT + i) bc) ->
    (0 <= i)%Z -> (i + 2 <= L)%Z -> intconv (bv_unsigned bc) ->
    (forall mc' dcs', INV mc' -> rw_cells bsegs mc' (bv_unsigned sp + -2216) dcs' -> cells_size dcs' = 40%nat ->
       forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evtF bsegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i + 2)) (Z_to_bv 64 (bv_unsigned aq + 8)) y22 y28 y29 y30 y31)
                           F (Z_to_bv 64 0x46bcc) fc None mc' (seg_rom bsegs))) ->
    forall y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
    evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp (Z_to_bv 64 (FMT + i)) (Z_to_bv 64 (bv_unsigned bc)) y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 10) (Z_to_bv 64 (FMT + i + 2)) (Z_to_bv 64 0x15307) aq (Z_to_bv 64 (FMT + i + 1)) (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
                 (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31)
                       F (Z_to_bv 64 0x46d7c) fc None mc (seg_rom bsegs)).
  Proof.
    intros Q mc i aq bc IV DIR Hi HiL HC K. intros. prep IV.
    destruct (cfacts _ HC) as (_ & NF3 & NF4 & (ix & HF) & CR & N109 & N110).
    pose proof (conj CR (conj N109 N110)) as CC.
    recell DIR 2%nat 1%nat [C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 4294967295)].
    zs. change (sx32 (Z_to_bv 64 4294967295)) with (Z_to_bv 64 (-1)). zs. br CC.
    zs. change (sx32 (Z_to_bv 64 4294967295)) with (Z_to_bv 64 (-1)). zs. br CC.
    (* [comment removed for export] *) zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
    (* [comment removed for export] *) zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
    (* [comment removed for export] *) zs. cbv beta. zs. zs. br CC. zs. zs. zs.
    call istrchr_spec. all: prem.
    rewrite (istrchr_res_none _ _ _ NF3).
    (* [comment removed for export] *) zs. cbv beta. zs. br CC.
    (* [comment removed for export] *) zs. zs. zs. zs. zs.
    chunk_split DIR 8%nat DIR2. chunk_split DIR2 1%nat DIR3.
    call_sp fgvs_spec. all: prem.
    (* [comment removed for export] *) zs. zs. zs. br CC.
    (* [comment removed for export] *) zs. cbv beta. zs. zs. br CC.
    (* [comment removed for export] *) zs. zs. br CC. zs. br CC.
    (* [comment removed for export] *) zs. zs. zs.
    call istrchr_spec. all: prem.
    rewrite (istrchr_res_none _ _ _ NF4).
    zs. br CC.
    (* [comment removed for export] *) zs. zs. zs. br CC. zs. zs. br CC. zs. zs. br CC.
    (* [comment removed for export] *) zs.
    chunk_join DIR DIR2. chunk_join DIR DIR3.
    unfold lregs in K. eapply K. 2:{ exact DIR. } 2:{ reflexivity. }
    split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
  Qed.


  Ltac norm_stk H tgt :=
    lazymatch type of H with stk _ _ _ ?hi =>
      replace hi with tgt in H by (cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; lia) end.

  Notation POST := (printf_common_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).

  (* [comment removed for export] *)
  Lemma L_last : forall mc aq,
    INV mc -> rw_cells bsegs mc (bv_unsigned sp + -2216) dcells1 ->
    forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
    evtF bsegs RNG POST (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + L)) aq y22 y28 y29 y30 y31)
                          F (Z_to_bv 64 0x46c00) fc None mc (seg_rom bsegs)).
  Proof.
    intros mc aq IV DIR. intros. unfold lregs. prep IV.
    assert (HL : nth_error (fstr ++ [Z_to_bv 8 0]) (Z.to_nat L) = Some (Z_to_bv 8 0)) by (rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia; reflexivity).
    assert (CC : True) by exact I.
    pose proof (fmt_rd mc L (Z_to_bv 8 0) MI1 MU1 HL ltac:(lia)) as RD.
    zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC. zs. br CC.
    (* [comment removed for export] *) zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC. zs.
    (* [comment removed for export] *) zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
    (* [comment removed for export] *) clear RD. zs. do 13 zs. zs. zs.
    (* [comment removed for export] *)
    pose proof (stk_release _ _ _ _ _ ST1 FRL ltac:(lia)) as SK1. norm_stk SK1 (bv_unsigned sp + -2216)%Z.
    pose proof (stk_release _ _ _ _ _ SK1 DIR ltac:(lia)) as SK2. norm_stk SK2 (bv_unsigned sp + -2176)%Z.
    pose proof (stk_merge _ _ _ _ _ SK2 STM ltac:(lia)) as SK3.
    pose proof (stk_release _ _ _ _ _ SK3 FRT ltac:(lia)) as SK4. norm_stk SK4 (bv_unsigned sp).
    replace (bv_unsigned sp + -2320)%Z with (bv_unsigned sp - 2320)%Z in MU1 by lia.
    finish.
  Qed.


  (* [comment removed for export] *)
  Theorem printf_common_int1 : forall pre b37 bc post,
    fstr = pre ++ b37 :: bc :: post ->
    Forall (fun b : byte => bv_unsigned b <> 37%Z) pre -> Forall (fun b : byte => bv_unsigned b <> 37%Z) post ->
    bv_unsigned b37 = 37%Z -> intconv (bv_unsigned bc) -> post <> [] ->
    evtF bsegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x46ac0) fc None m (seg_rom bsegs)).
  Proof.
    intros pre b37 bc post EF NP1 NP2 E37 HC NE.
    assert (LEN : length fstr = (length pre + 2 + length post)%nat) by (rewrite EF, length_app; cbn; lia).
    assert (NE' : (1 <= length post)%nat) by (destruct post; [congruence | cbn; lia]).
    set (np := Z.of_nat (length pre)).
    eapply L_entry. intros mc dj IV DIR. intros.
    eapply (L_head _ mc [CB 40 dj]); [exact IV | exact DIR | reflexivity |]. clear mc dj IV DIR. intros mc IV DIR. intros.
    replace (Z_to_bv 64 FMT) with (Z_to_bv 64 (FMT + 0)) by (f_equal; lia).
    pose proof IV as IV'. destruct IV' as (_ & _ & _ & _ & MUc & _ & MIc & _).
    eapply (L_skip _ mc (length pre) 0); [exact MIc | exact MUc | lia | lia | |].
    { intros j b Hj Hb. eapply (proj1 (Forall_forall _ _) NP1). eapply nth_error_In. rewrite EF, nth_error_app1 in Hb by lia. exact Hb. }
    clear MUc MIc. intros. rewrite Z.add_0_l.
    eapply (L_dirA _ mc np _ b37 bc); [exact IV | exact DIR | lia | lia | | exact E37 | | exact (proj1 (cfacts _ HC)) |].
    { rewrite EF. replace (Z.to_nat np) with (length pre) by lia. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. }
    { rewrite EF. replace (Z.to_nat (np + 1)) with (length pre + 1)%nat by lia. rewrite nth_error_app2 by lia.
      replace (length pre + 1 - length pre)%nat with 1%nat by lia. reflexivity. }
    clear mc IV DIR. intros mc IV DIR. intros.
    eapply (L_dirB _ mc np); [exact IV | exact DIR | lia | lia | exact HC |].
    clear mc IV DIR. intros mc dcs IV DIR SZ. intros. unfold lregs.
    (* [comment removed for export] *)
    destruct (nth_error post 0) as [b2|] eqn:E2. 2:{ exfalso. apply nth_error_None in E2. lia. }
    assert (H2 : nth_error fstr (Z.to_nat (np + 2)) = Some b2).
    { rewrite EF. replace (Z.to_nat (np + 2)) with (length pre + 2)%nat by lia. rewrite nth_error_app2 by lia.
      replace (length pre + 2 - length pre)%nat with 2%nat by lia. exact E2. }
    pose proof IV as IV'. prep IV'.
    destruct (fmt_char mc (np + 2) MI1 MU1 ltac:(lia)) as (b2' & Hb2 & NZ2 & RB2 & RD2). rewrite H2 in Hb2. injection Hb2 as <-.
    replace (FMT + np + 2)%Z with (FMT + (np + 2))%Z by lia.
    zs. cbv beta. zs. assert (CC : True) by exact I. br NZ2.
    (* [comment removed for export] *)
    eapply (L_head _ mc dcs); [exact IV | exact DIR | exact SZ |].
    clear mc IV DIR SZ FRT FRL STM ST1 MU1 WM1 MI1 GOT1 SHB1 RD2. intros mc IV DIR. intros.
    pose proof IV as IV'. destruct IV' as (_ & _ & _ & _ & MUc & _ & MIc & _).
    eapply (L_skip _ mc (length post) (np + 2)); [exact MIc | exact MUc | lia | lia | |].
    { intros j b Hj Hb. eapply (proj1 (Forall_forall _ _) NP2). eapply nth_error_In with (n := (j - (length pre + 2))%nat).
      rewrite EF, nth_error_app2 in Hb by lia.
      replace (j - length pre)%nat with (S (S (j - (length pre + 2)))) in Hb by lia. exact Hb. }
    intros. replace (np + 2 + Z.of_nat (length post))%Z with L by lia.
    eapply L_last; [exact IV | exact DIR].
  Qed.



  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Variables (Sa : Z) (sstr : list byte) (RLO RHI : Z).
  Hypothesis LAY : rt_layout m.
  Hypothesis VAQ : rw_cells bsegs m (bv_unsigned a2) [C8 (Z_to_bv 64 Sa)].
  Hypothesis SEPV : (bv_unsigned sp <= bv_unsigned a2 /\ bv_unsigned a2 + 8 <= 2^64)%Z.
  Hypothesis SSTR : bytes_at bsegs m Sa (sstr ++ [Z_to_bv 8 0]).
  Hypothesis SNOZ : Forall (fun b : byte => bv_unsigned b <> 0%Z) sstr.
  Notation LS := (Z.of_nat (length sstr)).
  Notation NS := (Z.of_nat (length sstr) + 1)%Z.
  Hypothesis SEPS : (Sa + NS <= bv_unsigned sp - 2320 \/ bv_unsigned sp <= Sa)%Z.
  Hypothesis APPS : app_blk Sa (Sa + NS).
  Hypothesis SPOS : (0 < Sa)%Z.
  Hypothesis USTR : unpoisoned m Sa (Sa + NS).
  Hypothesis NSZ : (NS <= 2^40)%Z.
  Hypothesis R1 : (RLO <= Sa /\ Sa + NS <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z.
  Hypothesis WR1 : wr_at bsegs m (shad RLO) (shad RHI - shad RLO).
  Hypothesis RVA : rng RNG (bv_unsigned a2) 8.
  Hypothesis RS : rng RNG Sa NS.
  Hypothesis RSH1 : rng RNG (shad RLO) (shad RHI - shad RLO).


  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition INVS (mc : word -> option byte) : Prop :=
    INV mc /\ rt_layout mc /\ unpoisoned mc Sa (Sa + NS) /\ wr_at bsegs mc (shad RLO) (shad RHI - shad RLO)
    /\ bytes_at bsegs mc Sa (sstr ++ [Z_to_bv 8 0]) /\ rw_cells bsegs mc (bv_unsigned a2) [C8 (Z_to_bv 64 Sa)].

  Definition BND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2320 /\ KHIGH <= lo /\ 1 <= NS /\ NS <= 2^40
     /\ 0 < Sa /\ Sa + NS + 8 <= KEND
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad Sa /\ shad (Sa + NS - 1) + 1 <= shad RHI /\ shad RHI <= KHIGH
     /\ 0 <= Z.shiftr Sa 3 < 2^44 /\ 0 <= Z.shiftr (Sa + NS + -1) 3 < 2^44
     /\ shad RLO mod 8 = 0 /\ shad RHI mod 8 = 0
     /\ RLO <= Sa /\ Sa + NS <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0
     /\ bv_unsigned sp <= bv_unsigned a2 /\ bv_unsigned a2 + 8 <= 2^64)%Z.
  Lemma BND_ok : BND.
  Proof.
    unfold BND. destruct ST as (L0 & _). destruct APPS as [LES AS]. unfold KLOW, KHIGH, KEND in *.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF.
    Z.div_mod_to_equations. nia.
  Qed.
  Ltac acc_facts B ::= pose proof BND_ok as B; unfold BND, KHIGH, KEND in B.

  Definition BLS : Prop :=
    (1 <= NS /\ NS <= 2^40 /\ 0 < Sa /\ Sa + NS + 8 <= 2^47
     /\ 0 <= Z.shiftr Sa 3 < 2^44 /\ 0 <= Z.shiftr (Sa + NS + -1) 3 < 2^44
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad Sa /\ shad (Sa + NS - 1) + 1 <= shad RHI /\ shad RHI <= 17594333495296
     /\ bv_unsigned sp <= bv_unsigned a2 /\ bv_unsigned a2 + 8 <= 2^64)%Z.
  Lemma BLS_ok : BLS. Proof. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B. unfold BLS. lia. Qed.

  Lemma invs_of : forall mc, INV mc -> INVS mc.
  Proof.
    intros mc IV. pose proof IV as (FRT & (j0 & FRL) & STM & ST1 & MU1 & WM1 & MI1 & GOT1 & SHB1).
    pose proof BND_ok as B. unfold BND, KHIGH, KEND in B.
    split; [exact IV|].
    split. { eapply rw_cells_transport; [exact LAY | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    assert (SS : (shad (Sa + NS - 1) + 1 <= 17594333495296)%Z) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    split. { eapply unpoisoned_munch; [exact USTR | exact MU1 |]. cbn [disjoint_from]. lia. }
    split. { eapply wr_at_transport; eassumption. }
    split. { eapply bytes_at_transport; [exact SSTR | exact MU1 |]. rewrite length_app. cbn [length disjoint_from]. lia. }
    eapply rw_cells_transport; [exact VAQ | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia.
  Qed.

  Ltac preps IV :=
    let IVS := fresh "IVS" in pose proof (invs_of _ IV) as IVS;
    destruct IVS as (_ & LAY1 & US1 & WR11 & SSTR1 & VAQ1);
    prep IV;
    let B := fresh "BS" in pose proof BLS_ok as B; unfold BLS in B;
    change (?P) with (sf_hide P) in SEPS; change (?P) with (sf_hide P) in R1; change (?P) with (sf_hide P) in SEPV;
    change (?P) with (sf_hide P) in SSTR; change (?P) with (sf_hide P) in NSZ.

  Ltac unland K :=
    change 18446744073709551615%Z with (Z.ones 64) in K; rewrite ?Z.land_ones in K by lia;
    change (2 ^ 64)%Z with 18446744073709551616%Z in K.

  (* [comment removed for export] *)
  Definition KS (Q : machine_state -> Prop) (i : Z) : Prop :=
    forall mc' dcs', INV mc' -> rw_cells bsegs mc' (bv_unsigned sp + -2216) dcs' -> cells_size dcs' = 40%nat ->
       forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evtF bsegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i + 2)) (Z_to_bv 64 (bv_unsigned a2 + 8)) y22 y28 y29 y30 y31)
                           F (Z_to_bv 64 0x46bcc) fc None mc' (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition sregs (i : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31 : word) :=
    mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp x5 x6 x7 sp (Z_to_bv 64 (-1)) x10 x11 x12 x13 x14 x15 x16 x17
        (Z_to_bv 64 10) (Z_to_bv 64 (FMT + i + 2)) (Z_to_bv 64 0x15307) (Z_to_bv 64 (bv_unsigned a2 + 8)) x22 x23
        (Z_to_bv 64 (bv_unsigned sp + -2184)) (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) x28 x29 x30 x31.

  (* [comment removed for export] *)
  Lemma LS_X : forall Q i mc dcs, KS Q i -> INV mc -> rw_cells bsegs mc (bv_unsigned sp + -2216) dcs -> cells_size dcs = 40%nat ->
    forall x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31,
    evtF bsegs RNG Q (MS (sregs i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x46f4c) fc None mc (seg_rom bsegs)).
  Proof.
    intros Q i mc dcs K IV DIR SZ. intros. unfold sregs. prep IV.
    zs. zs. unfold KS, lregs in K. eapply K; [| exact DIR | exact SZ].
    split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma LS_L : forall Q i mc dcs (k : nat) (c : Z), KS Q i -> INV mc -> rw_cells bsegs mc (bv_unsigned sp + -2216) dcs -> cells_size dcs = 40%nat ->
    (NS <= 64)%Z -> Z.to_nat (shad (Sa + NS - 1) - c) = k -> (shad Sa <= c < shad (Sa + NS - 1))%Z ->
    forall x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    evtF bsegs RNG Q (MS (sregs i x1 x5 x6 x7 (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (Sa + NS + -1) 3)) (Z_to_bv 64 0) x13 x14 x15 x16 x17
                              (Z_to_bv 64 Sa) (Z_to_bv 64 NS) x28 x29 x30 x31)
                       F (Z_to_bv 64 0x4705c) fc None mc (seg_rom bsegs)).
  Proof.
    intros Q i mc dcs k c K IV DIR SZ N1 Hk Hc. intros. unfold sregs. pose proof IV as IV0. preps IV.
    revert c x13 Hk Hc. induction k as [|k IH]; intros c x13 Hk Hc; [exfalso; lia|].
    assert (SL : (shad (Sa + NS - 1) = 2147450880 + Z.shiftr (Sa + NS + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd bsegs mc Sa (Sa + NS) c US1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K1; zify_cond K1.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LS_X; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma LS_E : forall Q i mc dcs, KS Q i -> INV mc -> rw_cells bsegs mc (bv_unsigned sp + -2216) dcs -> cells_size dcs = 40%nat ->
    (NS <= 64)%Z ->
    forall x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    evtF bsegs RNG Q (MS (sregs i x1 x5 x6 x7 (Z_to_bv 64 (2147450880 + Z.shiftr Sa 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (Sa + NS + -1) 3))
                              (Z_to_bv 64 (Sa + NS + -1)) x13 x14 x15 x16 x17 (Z_to_bv 64 Sa) (Z_to_bv 64 NS) x28 x29 x30 x31)
                       F (Z_to_bv 64 0x47040) fc None mc (seg_rom bsegs)).
  Proof.
    intros Q i mc dcs K IV DIR SZ N1. intros. unfold sregs. pose proof IV as IV0. preps IV.
    destruct (unpoisoned_check_rd bsegs mc Sa (Sa + NS) (Sa + NS + -1) 1 US1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((Sa + NS + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LS_X; eassumption.
    - eapply (LS_L Q i mc dcs); [exact K | exact IV0 | exact DIR | exact SZ | exact N1 | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma LS_C : forall Q i mc dcs, KS Q i -> INV mc -> rw_cells bsegs mc (bv_unsigned sp + -2216) dcs -> cells_size dcs = 40%nat ->
    forall x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    evtF bsegs RNG Q (MS (sregs i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 Sa) (Z_to_bv 64 NS) x28 x29 x30 x31)
                       F (Z_to_bv 64 0x46ff0) fc None mc (seg_rom bsegs)).
  Proof.
    intros Q i mc dcs K IV DIR SZ. intros. unfold sregs. pose proof IV as IV0. preps IV.
    zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1 BS. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      assert (N1 : (64 < NS)%Z) by (unland K2; clear - K2 BS; Z.div_mod_to_equations; lia).
      zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3 BS. lia. }
      zstep. zstep. zstep.
      unfold sf_hide in LO.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1
        | zsimp; exact APPS | zsimp; exact US1
        | zsimp; pose proof BND_ok as B9; unfold BND in B9; lia
        | eapply rng_sub'; [exact RSTK | lia] | ].
      zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply LS_X; [exact K | | eassumption | exact SZ].
      split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
    - (* [comment removed for export] *)
      assert (N1 : (NS <= 64)%Z) by (unland K2; clear - K2 BS; Z.div_mod_to_equations; lia).
      do 11 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R1.
      destruct (shadow_probe8 bsegs mc RLO RHI Sa WR11 ltac:(apply no_image_asan; pose proof BND_ok as B9; unfold BND in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w1 P1].
      destruct (shadow_probe8 bsegs mc RLO RHI (Sa + NS + -1) WR11 ltac:(apply no_image_asan; pose proof BND_ok as B9; unfold BND in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. prr [10;11;12;13]%Z. if_cases K5; zify_cond K5.
      + eapply LS_X; eassumption.
      + eapply LS_E; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma L_dirS : forall Q mc (i : Z) bc,
    INV mc -> rw_cells bsegs mc (bv_unsigned sp + -2216) (dcellsA (FMT + i) bc) ->
    (0 <= i)%Z -> (i + 2 <= L)%Z -> sconv (bv_unsigned bc) -> KS Q i ->
    forall y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
    evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp (Z_to_bv 64 (FMT + i)) (Z_to_bv 64 (bv_unsigned bc)) y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 10) (Z_to_bv 64 (FMT + i + 2)) (Z_to_bv 64 0x15307) a2 (Z_to_bv 64 (FMT + i + 1)) (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
                 (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31)
                       F (Z_to_bv 64 0x46d7c) fc None mc (seg_rom bsegs)).
  Proof.
    intros Q mc i bc IV DIR Hi HiL HC K. intros. pose proof IV as IV0. preps IV.
    destruct (sfacts _ HC) as (_ & CR & N109 & N110 & F3 & F4 & F5 & F6).
    pose proof (conj CR (conj N109 N110)) as CC.
    recell DIR 2%nat 1%nat [C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 4294967295)].
    zs. change (sx32 (Z_to_bv 64 4294967295)) with (Z_to_bv 64 (-1)). zs. br CC.
    zs. change (sx32 (Z_to_bv 64 4294967295)) with (Z_to_bv 64 (-1)). zs. br CC.
    (* [comment removed for export] *) zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
    (* [comment removed for export] *) zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
    (* [comment removed for export] *) zs. cbv beta. zs. zs. br CC. zs. zs. zs.
    call istrchr_spec. all: prem. unfold istrchr_res. rewrite F3. rewrite unsigned_lit by (cbn; lia).
    (* [comment removed for export] *) zs. cbv beta. zs. br CC.
    (* [comment removed for export] *) zs. zs. zs. zs. call istrchr_spec. all: prem. rewrite (istrchr_res_none _ _ _ F4).
    (* [comment removed for export] *) zs. zs. zs. br CC.
    (* [comment removed for export] *) zs. zs. zs. zs. call istrchr_spec. all: prem. unfold istrchr_res. rewrite F5. rewrite unsigned_lit by (cbn; lia).
    (* [comment removed for export] *) zs. zs. br CC. zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
    (* [comment removed for export] *) zs. zs.
    (* [comment removed for export] *) zs. cbv beta. zs. zs. zs. call istrchr_spec. all: prem. unfold istrchr_res. rewrite F6. rewrite unsigned_lit by (cbn; lia).
    (* [comment removed for export] *) zs. br CC. zs.
    (* [comment removed for export] *) zs. cbv beta. zs. zs. br CC.
    (* [comment removed for export] *) zs. zs. br CC. zs. br CC.
    (* [comment removed for export] *) zs. zs. zs. br BS.
    (* [comment removed for export] *) zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
    zs. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0). zs. br CC.
    (* [comment removed for export] *) zs. zs.
    unfold sf_hide in SSTR1.
    call istrlen_spec. all: prem.
    zs.
    cbn [app] in DIR.
    eapply (LS_C Q i); [exact K | | exact DIR | reflexivity].
    split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
  Qed.

  (* [comment removed for export] *)
  Theorem printf_common_str1 : forall pre b37 bc post,
    fstr = pre ++ b37 :: bc :: post ->
    Forall (fun b : byte => bv_unsigned b <> 37%Z) pre -> Forall (fun b : byte => bv_unsigned b <> 37%Z) post ->
    bv_unsigned b37 = 37%Z -> sconv (bv_unsigned bc) -> post <> [] ->
    evtF bsegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x46ac0) fc None m (seg_rom bsegs)).
  Proof.
    intros pre b37 bc post EF NP1 NP2 E37 HC NE.
    assert (LEN : length fstr = (length pre + 2 + length post)%nat) by (rewrite EF, length_app; cbn; lia).
    assert (NE' : (1 <= length post)%nat) by (destruct post; [congruence | cbn; lia]).
    set (np := Z.of_nat (length pre)).
    eapply L_entry. intros mc dj IV DIR. intros.
    eapply (L_head _ mc [CB 40 dj]); [exact IV | exact DIR | reflexivity |]. clear mc dj IV DIR. intros mc IV DIR. intros.
    replace (Z_to_bv 64 FMT) with (Z_to_bv 64 (FMT + 0)) by (f_equal; lia).
    pose proof IV as IV'. destruct IV' as (_ & _ & _ & _ & MUc & _ & MIc & _).
    eapply (L_skip _ mc (length pre) 0); [exact MIc | exact MUc | lia | lia | |].
    { intros j b Hj Hb. eapply (proj1 (Forall_forall _ _) NP1). eapply nth_error_In. rewrite EF, nth_error_app1 in Hb by lia. exact Hb. }
    clear MUc MIc. intros. rewrite Z.add_0_l.
    eapply (L_dirA _ mc np _ b37 bc); [exact IV | exact DIR | lia | lia | | exact E37 | | exact (proj1 (sfacts _ HC)) |].
    { rewrite EF. replace (Z.to_nat np) with (length pre) by lia. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. }
    { rewrite EF. replace (Z.to_nat (np + 1)) with (length pre + 1)%nat by lia. rewrite nth_error_app2 by lia.
      replace (length pre + 1 - length pre)%nat with 1%nat by lia. reflexivity. }
    clear mc IV DIR. intros mc IV DIR. intros.
    eapply (L_dirS _ mc np); [exact IV | exact DIR | lia | lia | exact HC |].
    clear mc IV DIR. unfold KS. intros mc dcs IV DIR SZ. intros. unfold lregs.
    destruct (nth_error post 0) as [b2|] eqn:E2. 2:{ exfalso. apply nth_error_None in E2. lia. }
    assert (H2 : nth_error fstr (Z.to_nat (np + 2)) = Some b2).
    { rewrite EF. replace (Z.to_nat (np + 2)) with (length pre + 2)%nat by lia. rewrite nth_error_app2 by lia.
      replace (length pre + 2 - length pre)%nat with 2%nat by lia. exact E2. }
    pose proof IV as IV'. prep IV'.
    destruct (fmt_char mc (np + 2) MI1 MU1 ltac:(lia)) as (b2' & Hb2 & NZ2 & RB2 & RD2). rewrite H2 in Hb2. injection Hb2 as <-.
    replace (FMT + np + 2)%Z with (FMT + (np + 2))%Z by lia.
    zs. cbv beta. zs. assert (CC : True) by exact I. br NZ2.
    eapply (L_head _ mc dcs); [exact IV | exact DIR | exact SZ |].
    clear mc IV DIR SZ FRT FRL STM ST1 MU1 WM1 MI1 GOT1 SHB1 RD2. intros mc IV DIR. intros.
    pose proof IV as IV'. destruct IV' as (_ & _ & _ & _ & MUc & _ & MIc & _).
    eapply (L_skip _ mc (length post) (np + 2)); [exact MIc | exact MUc | lia | lia | |].
    { intros j b Hj Hb. eapply (proj1 (Forall_forall _ _) NP2). eapply nth_error_In with (n := (j - (length pre + 2))%nat).
      rewrite EF, nth_error_app2 in Hb by lia.
      replace (j - length pre)%nat with (S (S (j - (length pre + 2)))) in Hb by lia. exact Hb. }
    intros. replace (np + 2 + Z.of_nat (length post))%Z with L by lia.
    eapply L_last; [exact IV | exact DIR].
  Qed.

End PC.
End CANSEC1.
