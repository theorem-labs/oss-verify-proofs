(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import SFModel Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim Monad PrintfModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Printf_mlib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Fe_pop_arg Fe_printf_iface Fe_printf_snsink Fe_vfprintf Fe_vsnprintf.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import FX_lib F_memset F_memcpy F_fwritex.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Fe_icalls.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_m2s I_consts. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import F_achk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import PrintfModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Notation SNL_ENTRY := 0x142990%Z (only parsing).
Notation USELOC_ENTRY := 0x14d61c%Z (only parsing).
Notation LOC_CELL := 0x6a7e38%Z (only parsing).
Notation GLOC := 0x6c8130%Z (only parsing).
Notation SNL_FRAME := 80%Z (only parsing).
Notation SNL_DEPTH := 10448%Z (only parsing).

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).

Definition usel_new (old loc : Z) : Z := if loc =? 0 then old else if loc =? 2^64 - 1 then GLOC else loc.
Definition usel_ret (old : Z) : Z := if old =? GLOC then 2^64 - 1 else old.

Lemma lor_ones64 : forall x, 0 <= x < 2^64 -> Z.lor 18446744073709551615 x = 18446744073709551615.
Proof.
  intros x Hx. apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
  change 18446744073709551615 with (Z.ones 64).
  destruct (Z.lt_ge_cases i 64).
  - rewrite Z.ones_spec_low by lia. reflexivity.
  - rewrite Z.ones_spec_high by lia. cbn.
    destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia| lia].
Qed.
Lemma usel_ret_eq : forall old, 0 <= old < 2^64 ->
  Z.lor (Z.land (Z.b2z (0 <? Z.lxor old 7110960) + -1) 18446744073709551615) old = usel_ret old.
Proof.
  intros old Hold. unfold usel_ret.
  destruct (Z.eqb_spec old 7110960) as [->|NE].
  - rewrite Z.lxor_nilpotent. cbn. apply lor_ones64. lia.
  - assert (NZ : Z.lxor old 7110960 <> 0) by (intros E; apply Z.lxor_eq in E; lia).
    pose proof (Z.lxor_nonneg old 7110960) as NN.
    replace (0 <? Z.lxor old 7110960) with true by (symmetry; apply Z.ltb_lt; lia). cbn. reflexivity.
Qed.

Definition uselocale_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (old loc : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (usel_ret old)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(LOC_CELL, LOC_CELL + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' LOC_CELL [C8 (Z_to_bv 64 (usel_new old loc))].

Lemma uselocale_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (old loc : Z),
  tp = Z_to_bv 64 (LOC_CELL + 48) -> a0 = Z_to_bv 64 loc -> (0 <= loc < 2^64) -> (0 <= old < 2^64) ->
  rw_cells asegs m LOC_CELL [C8 (Z_to_bv 64 old)] -> mem_inv asegs m ->
  evt asegs (uselocale_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc old loc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 USELOC_ENTRY) fc None m (seg_rom asegs)).
Proof.
  intros until loc. intros -> -> Hloc Hold CELL MI.
  pose proof (munch_refl [(0x6a7e38, 0x6a7e38 + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  zs. zs. zs. zs.
  zs. if_cases K0; zify_cond K0.
  -
    zs. zs. zs. zs. zs. zs.
    rewrite (usel_ret_eq old Hold).
    apply evt_done. unfold uselocale_post, usel_new. try rewrite !unsigned_lit in K0 by lia.
    replace (loc =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. exact CELL.
  - try rewrite !unsigned_lit in K0 by lia.
    zs. zs. if_cases K1; zify_cond K1; try rewrite !unsigned_lit in K1 by lia.
    +
      zs.
      zs. zs. zs. zs. zs. zs.
      rewrite (usel_ret_eq old Hold).
      apply evt_done. unfold uselocale_post, usel_new.
      replace (loc =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (loc =? 2^64 - 1) with false by (symmetry; apply Z.eqb_neq; lia).
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      match goal with H : rw_cells _ _ 6979128 _ |- _ => exact H end.
    +
      zs. zs.
      zs. zs. zs. zs. zs. zs.
      rewrite (usel_ret_eq old Hold).
      apply evt_done. unfold uselocale_post, usel_new.
      replace (loc =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (loc =? 2^64 - 1) with true by (symmetry; apply Z.eqb_eq; lia).
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      match goal with H : rw_cells _ _ 6979128 _ |- _ => exact H end.
Qed.

Definition snl_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (D : Z) (dn : nat) (junkd : list byte) (r : Z) (o : list Z) (lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (ret_pc ra) fc' None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (D, D + Z.of_nat dn); (LOC_CELL, LOC_CELL + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ frm0 fc'
    /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ ssp_cells m' canary
    /\ rw_cells asegs m' D [CB dn (zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) junkd)]
    /\ rw_cells asegs m' LOC_CELL [C8 (Z_to_bv 64 GLOC)].

Section SNL.
Hypothesis RIP : rip_stmt.

Variable PCOK2 : list Z -> list parg -> list word -> Z -> Z -> Z -> mem -> Prop.
Hypothesis IVSN : ivsn_stmt PCOK2.

Definition snl_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (D n LOC A : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (args : list parg)
         (lo : Z) (canary : word) (r : Z) (o : list Z),
    let q := bv_unsigned sp in
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 LOC -> a3 = Z_to_bv 64 A -> tp = Z_to_bv 64 (LOC_CELL + 48) ->
    (0 < LOC < 2^64) ->
    rw_cells asegs m LOC_CELL [C8 (Z_to_bv 64 GLOC)] ->
    rw_cells asegs m D [CB dn junkd] ->
    bytes_at asegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
    (forall m', args_ok 0 0 0 m' lo (q - SNL_FRAME) 0 [a4; a5; a6; a7] args) ->
    printf_model OUT_sn OUTFP_sn fmt args [] = ITree.Ret (Ok (r, o)) ->
    fpcalls_sn_ok fmt args ->
    (length o < dn)%nat -> (zlength o <= n - 1) -> (1 <= n < 2^63) ->
    stk asegs m lo q -> (lo <= q - SNL_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
    ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
    (q <= A) -> (A + zlength fmt <= 2^62) -> (D + Z.of_nat dn <= A \/ A + zlength fmt <= D) ->
    (q <= D) -> (D + Z.of_nat dn <= 2^62) ->

    (q <= 2^47) -> (q mod 16 = 0) ->
    (kHighShadowEnd + 8 <= lo) -> ictx m -> (forall p n', lo <= p -> p + n' <= q -> chkr m p n') ->
    chkr m A (zlength fmt) -> rod_chk m -> chkr m D (zlength o + 1) -> (D + Z.of_nat dn <= SHADOW_LO \/ SHADOW_HI <= D) ->
    rod_chk_fp m -> ifx_real m ->
    (forall m', munch [(lo, q); (D, D + Z.of_nat dn); (LOC_CELL, LOC_CELL + 8)] m m' -> wmono asegs m m' -> PCOK2 fmt args [a4; a5; a6; a7] A (q - 32) lo m') ->
    evt asegs (snl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd r o lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SNL_ENTRY) fc None m (seg_rom asegs)).

Theorem snl_proof : snl_stmt.
Proof using RIP IVSN.
  unfold snl_stmt. intros until o. cbv zeta.
  intros -> -> -> -> Etp HLOC CELL DST BY HF P1 AOK MODEL FPF ROOM Hn Hn1 ST LO GLO QHI SSP MI FRM QA AHI DFMT QD DHI.
  intros HQ47 HQ16 HSH IC STKC FMTC ROD CHD DSH RODFP IFX PCO.
  unfold GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB. unfold zlength in *.
  destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  pose proof (munch_refl [(lo, bv_unsigned sp); (D, D + Z.of_nat dn); (LOC_CELL, LOC_CELL + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  subst tp.
  carve_frame 80%nat ST.

  do 13 zs. zs. zs. zs. zs.

  eapply evt_cut.
  { eapply (uselocale_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ GLOC LOC);
      [ reflexivity | reflexivity | lia | lia | exact CELL | assumption ]. }
  cbv beta. intros ms' P. unfold uselocale_post in P.
  destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m2 & -> & MUc & WMc & MI2 & CELL2).
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m2 MUc WMc; clear MUc WMc; try clear MI end.
  fix_ret.
  replace (usel_ret GLOC) with 18446744073709551615 by (unfold usel_ret; rewrite Z.eqb_refl; reflexivity).

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with FR : rw_cells _ mm (bv_unsigned sp + -80)%Z _ |- _ =>
      pose proof FR as FRc;
      apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_;_] _)) in FRc; destruct FRc as [_ VAA];
      cbn [cells_size csize Nat.add app] in VAA;
      pose proof (rw_cells_bytes_at' _ _ _ _ VAA) as VAB; cbn [cells_bytes cbytes app] in VAB; rewrite ?app_nil_r in VAB;
      replace (bv_unsigned sp + -80 + Z.of_nat 48)%Z with (bv_unsigned sp + -32)%Z in VAB by lia
    end end.

  zs. zs. zs. zs. zs. zs.
  pose proof IVSN as VS. unfold ivsn_stmt, e_vsnprintf_stub in VS.
  eapply evt_cut.
  { eapply VS with (D := D) (n := n) (A := A) (VA := (bv_unsigned sp + -32)%Z) (dn := dn) (junkd := junkd) (fmt := fmt) (slots := [a4; a5; a6; a7])
                   (args := args) (lo := lo) (canary := canary) (r := r) (o := o) (F0 := 0) (B0 := 0) (BS0 := 0) (ap0 := 0);
      clear VS; rewrite ?unsigned_lit by lia; unfold IVSN_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ].
    all: try reflexivity.
    all: try lia.

    all: try first [ exact DSH | exact I
               | (let m2 := fresh "mq" in let MU2 := fresh "MUq" in let WM2 := fresh "WMq" in
                  intros m2 MU2 WM2; apply PCO;
                  [ eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MU2]; unfold sub_fp, VSN_W; cbn [outside]; intros; lia]
                  | eapply wmono_trans; [exact WM | exact WM2] ])
               | (apply (ictx_munch _ m _ IC MU WM); intros ?x ?Hx; cbn [in_rl ICR outside] in *; unfold kHighShadowEnd in *; lia)
               | (intros p n' Hp1 Hp2; apply (chkr_munch _ m _ p n' (STKC p n' Hp1 ltac:(lia)) MU);
                  intros ?x ?Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI, kHighShadowEnd in *; lia)
               | (apply (chkr_munch _ m _ _ _ FMTC MU); intros ?x ?Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI, kHighShadowEnd in *; lia)
               | (destruct ROD as (R1 & R2 & R3); split; [| split];
                  [apply (chkr_munch _ m _ _ _ R1 MU) | apply (chkr_munch _ m _ _ _ R2 MU) | apply (chkr_munch _ m _ _ _ R3 MU)];
                  intros ?x ?Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI, kHighShadowEnd in *; lia)
               | (destruct RODFP as (R1 & R2 & R3 & R4 & R5 & R6); split; [|split; [|split; [|split; [|split]]]];
                  [apply (chkr_munch _ m _ _ _ R1 MU) | apply (chkr_munch _ m _ _ _ R2 MU) | apply (chkr_munch _ m _ _ _ R3 MU)
                  | apply (chkr_munch _ m _ _ _ R4 MU) | apply (chkr_munch _ m _ _ _ R5 MU) | apply (chkr_munch _ m _ _ _ R6 MU)];
                  intros ?x ?Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI, kHighShadowEnd in *; lia)
               | (unfold ifx_real in *; eapply ro_cells_transport; [exact IFX | exact MU |]; cbn [disjoint_from cells_size csize];
                  unfold kHighShadowEnd in *; lia)
               | (unfold zlength in CHD; apply (chkr_munch _ m _ _ _ CHD MU); intros ?x ?Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI, kHighShadowEnd in *; lia)
               | (unfold kHighShadowEnd in *; lia) ].
    - assumption.
    - exact BY.
    - exact HF.
    - exact P1.
    - unfold va_area. cbn [u64s app]. rewrite ?app_nil_r. exact VAB.
    - intros m' _. apply AOK.
    - exact MODEL.
    - exact FPF.
    - assumption.
    - split; assumption.
    - assumption.
    - exact FRM. }
  cbv beta. intros ms' P.
  unfold vsnprintf_post in P. rewrite !unsigned_lit in P by lia.
  destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SSP3 & DST3).
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m3 MUc WMc; clear MUc WMc; try clear MI2 end.
  fix_ret.
  clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.

  zs. zs. try (if_cases K2; zify_cond K2; try rewrite !unsigned_lit in K2 by lia; [ exfalso; lia | ]).
  zs. zs.
  eapply evt_cut.
  { eapply (uselocale_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fc' _ (usel_new GLOC LOC) (2^64 - 1));
      [ reflexivity | reflexivity | lia
      | unfold usel_new; destruct (LOC =? 0); [lia|]; destruct (LOC =? 2^64 - 1); lia
      | match goal with H : rw_cells _ _ 6979128 _ |- _ => exact H end
      | assumption ]. }
  cbv beta. intros ms' P. unfold uselocale_post in P.
  destruct P as (z5 & z6 & z7 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & z28 & z29 & z30 & z31 & m4 & -> & MUc & WMc & MI4 & CELL4).
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m4 MUc WMc; clear MUc WMc; try clear MI3 end.
  fix_ret.
  replace (usel_new (usel_new GLOC LOC) (2^64 - 1)) with GLOC in CELL4
    by (unfold usel_new; rewrite (proj2 (Z.eqb_neq (2^64 - 1) 0)) by lia; rewrite Z.eqb_refl; reflexivity).

  do 8 zs.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with FR : rw_cells _ mm (bv_unsigned sp + -80)%Z _ |- _ => release_frame FR ST3 (bv_unsigned sp) end end.
  apply evt_done. unfold snl_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI4|]. split; [exact FRM'|]. split; [exact FOK|].
  split; [exact ST3|].
  split; [split; [exact SSP1 | exact SSP2]|].
  split; [exact DST3|].
  exact CELL4.
Qed.
End SNL.
