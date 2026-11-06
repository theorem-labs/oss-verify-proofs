(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg RtCells AProto ABase ABytes AModelFacts F_memset F_apoison F_m2s.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AKit AKit2 FsKit.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::=
  first [ OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.LiaTuning.zify_prune_relevant; OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.LiaTuning.zify_noeuclid_nosat; Z.euclidean_division_equations_cleanup; xlia zchecker
        | Zify.zify; xlia zchecker ].
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.
Definition AANNOT : Z := 0x84930.
Definition ANNOT_STACK : Z := 2720.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition annot_cells (m : amem) : Prop :=
     rw_cells asegs m 0x16dc18 [C1 (Z_to_bv 8 1)]          (* [comment removed for export] *)
  /\ rw_cells asegs m 0x167068 [C8 (Z_to_bv 64 0x1ffe58)] (* [comment removed for export] *)
  /\ rw_cells asegs m 0x1ffe58 [C4 (Z_to_bv 64 0)].       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rdn8 (x : Z) : Z := x - x mod 8.
Definition rup8 (x : Z) : Z := rdn8 (x + 7).

(* [comment removed for export] *)
Definition end_byte_ok (cap : Z) (sb : byte) : Prop := sval sb <> 0 /\ sval sb <= cap mod 8.

(* [comment removed for export] *)
Lemma end_byte_read : forall m beg cap sb,
  beg mod 8 = 0 -> 0 < cap ->
  rw_cells asegs m (shad beg + cap / 8) [C1 sb] ->
  ov_read_bytes asegs m (wa (2147450880 + Z.shiftr (beg + cap) 3)) 1 = Some [sb].
Proof.
  intros m beg cap sb AL CAP SBC.
  replace (2147450880 + Z.shiftr (beg + cap) 3) with (shad beg + cap / 8 + Z.of_nat 0)
    by (unfold shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  exact (rw_cells_read asegs m _ _ 0%nat (C1 sb) SBC eq_refl).
Qed.

(* [comment removed for export] *)
Lemma shadow_join : forall m beg cap junk sb,
  0 < cap -> cap mod 8 <> 0 ->
  rw_cells asegs m (shad beg) [CB (Z.to_nat (cap / 8)) junk] ->
  rw_cells asegs m (shad beg + cap / 8) [C1 sb] ->
  rw_cells asegs m (shad beg) [CB (Z.to_nat (shlen (rup8 cap))) (junk ++ [sb])].
Proof.
  intros m beg cap junk sb CAP NE BODY SBC.
  assert (E : shlen (rup8 cap) = cap / 8 + 1).
  { unfold shlen, rup8, rdn8. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  rewrite E. pose proof BODY as B0. destruct B0 as [[[LJ _] _] _]. cbn in LJ.
  assert (H : rw_cells asegs m (shad beg) ([CB (Z.to_nat (cap / 8)) junk] ++ [CB 1 [sb]])).
  { apply rw_cells_app. split; [exact BODY|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia.
    eapply rw_cells_recast; [exact SBC| cbn; tauto| reflexivity| reflexivity]. }
  pose proof (rw_cells_merge asegs m (shad beg) [] ([CB (Z.to_nat (cap / 8)) junk] ++ [CB 1 [sb]]) [] ) as M.
  cbn [app] in M, H. specialize (M H). cbn [cells_size cells_bytes csize cbytes Nat.add app] in M.
  rewrite ?app_nil_r, ?Nat.add_0_r in M. replace (Z.to_nat (cap / 8) + 1)%nat with (Z.to_nat (cap / 8 + 1)) in M by lia. exact M.
Qed.
Lemma shadow_whole_aligned : forall m beg cap junk,
  0 < cap -> cap mod 8 = 0 ->
  rw_cells asegs m (shad beg) [CB (Z.to_nat (cap / 8)) junk] ->
  rw_cells asegs m (shad beg) [CB (Z.to_nat (shlen (rup8 cap))) junk].
Proof.
  intros m beg cap junk CAP AL BODY. replace (shlen (rup8 cap)) with (cap / 8); [exact BODY|].
  unfold shlen, rup8, rdn8. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
End CANSEC1.
Local Ltac shrink_detour Kal M8E M8 M7 CAP AL SBC RSH SHF SHL R8 beg cap sb :=
  zstep; rewrite land_align8, M8E by lia;     (* [comment removed for export] *)
  zstep; zstep;
  let Ki := fresh "Ki" in if_cases Ki; zify_cond Ki; [| exfalso; clear - Ki CAP; lia];   (* [comment removed for export] *)
  zstep; let Kj := fresh "Kj" in if_cases Kj; zify_cond Kj; [exfalso; clear - Kj Kal M8; lia|];        (* [comment removed for export] *)
  do 5 zstep;                                 (* [comment removed for export] *)
  let HR := fresh "HR" in let ACC := fresh "ACC" in let SBR := fresh "SBR" in let Kk := fresh "Kk" in
  let SB1 := fresh "SB1" in let SB2 := fresh "SB2" in
  lazymatch goal with |- evtF _ ?RNG _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (end_byte_read mm beg cap sb AL ltac:(lia) SBC) as HR;
    assert (ACC : rng RNG (2147450880 + Z.shiftr (beg + cap) 3) 1)
      by (eapply rng_sub'; [exact RSH|]; rewrite SHF, SHL, R8, Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - AL CAP M7 M8 Kal; Z.div_mod_to_equations; lia)
  end;
  zstep; clear HR ACC; rewrite sxb_sval;       (* [comment removed for export] *)
  pose proof (sval_range sb) as SBR;
  lazymatch goal with EOK : end_byte_ok cap sb |- _ => destruct EOK as [SB1 SB2] end;
  zstep; if_cases Kk; zify_cond Kk; [ exfalso; clear - Kk SB1 SBR; rewrite ?unsigned_sval in Kk; apply SB1; apply sval_zero_iff; lia |];
  zstep; unfold bv_lts; rewrite !signed_lit_small64 by lia;   (* [comment removed for export] *)
  replace (cap mod 8 <? sval sb) with false by (symmetry; apply Z.ltb_ge; lia); cbn [negb];
  clear Ki Kj Kk SB1 SB2 SBR.

Local Ltac shrink_tail :=
  zstep; zstep; zstep;                                  (* [comment removed for export] *)
  zstep;                                                (* [comment removed for export] *)
  match goal with |- context [Z_to_bv 64 (Z.land ?b 7)] =>
    replace (Z.land b 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; lia) end;
  zstep; if_lit;                                        (* [comment removed for export] *)
  zstep; zstep;                                         (* [comment removed for export] *)
  zstep; let K1 := fresh "Kt" in if_cases K1; zify_cond K1; [exfalso; lia|];   (* [comment removed for export] *)
  zstep; rewrite land_align8 by lia;                    (* [comment removed for export] *)
  match goal with |- context [Z_to_bv 64 (?b - ?b mod 8)] => replace (b - b mod 8) with b by lia end;
  zstep; let K2 := fresh "Kt" in if_cases K2; zify_cond K2; [exfalso; lia|];   (* [comment removed for export] *)
  zstep; rewrite land_align8 by lia;                    (* [comment removed for export] *)
  match goal with |- context [Z_to_bv 64 (?b - ?b mod 8)] => replace (b - b mod 8) with b by lia end;
  zstep; zstep; rewrite land_align8 by lia;             (* [comment removed for export] *)
  match goal with |- context [Z_to_bv 64 (?b + 7 - (?b + 7) mod 8)] => replace (b + 7 - (b + 7) mod 8) with b by (Z.div_mod_to_equations; lia) end;
  zstep; let K3 := fresh "Kt" in if_cases K3; zify_cond K3; [| exfalso; lia];   (* [comment removed for export] *)
  zstep; zstep; rewrite land_align8 by lia;             (* [comment removed for export] *)
  match goal with |- context [Z_to_bv 64 (?b + ?c + 7 - (?b + ?c + 7) mod 8)] =>
    replace (b + c + 7 - (b + c + 7) mod 8) with (b + rup8 c) by (unfold rup8, rdn8; Z.div_mod_to_equations; lia) end;
  zstep; let K4 := fresh "Kt" in if_cases K4; zify_cond K4; [exfalso; lia|];   (* [comment removed for export] *)
  zstep; zstep; zstep;                                  (* [comment removed for export] *)
  match goal with |- context [Z_to_bv 64 (?b + rup8 ?c - ?b)] => replace (b + rup8 c - b) with (rup8 c) by lia end;
  zstep.                                                (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Definition annot_shrink_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (beg cap lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - ANNOT_STACK, bv_unsigned sp); (shad beg, shad beg + shlen (rup8 cap))] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (shad beg) [CB (Z.to_nat (shlen (rup8 cap))) (repeat (Z_to_bv 8 252) (Z.to_nat (shlen (rup8 cap))))].

Lemma annot_shrink_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (beg cap lo : Z) (junk : list byte) (sb : byte),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - ANNOT_STACK ->
  poison_cells m -> annot_cells m ->
  a0 = Z_to_bv 64 beg -> a1 = Z_to_bv 64 (beg + cap) -> a2 = Z_to_bv 64 (beg + cap) -> a3 = Z_to_bv 64 beg ->
  beg mod 8 = 0 -> 0 < cap <= 2^40 -> ablk beg (beg + rup8 cap) -> beg + rup8 cap <= 2^47 ->     (* [comment removed for export] *)
  rw_cells asegs m (shad beg) [CB (Z.to_nat (cap / 8)) junk] ->
  (cap mod 8 <> 0 -> rw_cells asegs m (shad beg + cap / 8) [C1 sb] /\ end_byte_ok cap sb) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad beg) (shlen (rup8 cap)) ->
  evtF asegs RNG (annot_shrink_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc beg cap lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AANNOT) fc None m (seg_rom asegs)).
Proof.
  intros until sb. intros MI ST CEIL LO PC AC -> -> -> -> AL CAP KH HE BODY SB RIMG RSTK RSH.
  unfold ANNOT_STACK, AANNOT in *. pose proof KH as KH0. unfold ablk, AIMG_HI, KLS in KH. pose proof atop_range as ATR.   (* [comment removed for export] *)
  pose proof PC as PC'. destruct PC' as (GOT & GOTMS & REAL & SHB & LAY & CANP & THR). destruct AC as (DCO & GVB & VERB).
  pose proof (munch_refl [(bv_unsigned sp - 2720, bv_unsigned sp); (shad beg, shad beg + shlen (rup8 cap))] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (R8 : rup8 cap = cap + 7 - (cap + 7) mod 8 /\ 0 <= (cap + 7) mod 8 < 8 /\ 0 <= cap mod 8 < 8) by (unfold rup8, rdn8; repeat split; try lia; apply Z.mod_pos_bound; lia).
  destruct R8 as (R8 & M7 & M8).
  assert (SHF : shad beg = 2147450880 + beg / 8 /\ shlen (rup8 cap) = rup8 cap / 8 /\ 8 * (cap / 8) = cap - cap mod 8).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. repeat split; try reflexivity. clear - CAP. Z.div_mod_to_equations. lia. }
  destruct SHF as (SHF & SHL & DIV8).
  assert (M8E : (beg + cap) mod 8 = cap mod 8) by (clear - AL CAP; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 2720, bv_unsigned sp)]%Z m) as MUF.
  (* [comment removed for export] *)
  carve_frame 56%nat ST;
       (destruct (stk_split asegs _ lo (bv_unsigned sp + -2128) (bv_unsigned sp + -56) ST ltac:(lia)) as [ST' STP]; clear ST; rename ST' into ST).
  do 9 zstep.                 (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  zstep; zstep.               (* [comment removed for export] *)
  zstep; rewrite zxb_lit by lia.   (* [comment removed for export] *)
  zstep; let K := fresh "Ka" in if_cases K; zify_cond K; [exfalso; clear - K; lia|].   (* [comment removed for export] *)
  do 3 zstep.                 (* [comment removed for export] *)
  zstep; zstep; zstep; lits.  (* [comment removed for export] *)
  zstep; zstep; let K := fresh "Kb" in if_cases K; zify_cond K; [exfalso; clear - K; lia|].   (* [comment removed for export] *)
  zstep; let K := fresh "Kc" in if_cases K; zify_cond K; [| exfalso; clear - K CAP; lia].   (* [comment removed for export] *)
  zstep; let K := fresh "Kd" in if_cases K; zify_cond K; [exfalso; clear - K CAP; lia|].   (* [comment removed for export] *)
  zstep; let K := fresh "Ke" in if_cases K; zify_cond K; [exfalso; clear - K CAP; lia|].   (* [comment removed for export] *)
  zstep; let K := fresh "Kf" in if_cases K; zify_cond K; [exfalso; clear - K CAP; lia|].   (* [comment removed for export] *)
  do 4 zstep.                 (* [comment removed for export] *)
  zstep; let K := fresh "Kg" in if_cases K; zify_cond K; [exfalso; clear - K CAP; lia|].   (* [comment removed for export] *)
  zstep; let K := fresh "Kh" in if_cases K; zify_cond K; [exfalso; clear - K CAP; lia|].   (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  replace (Z.land (beg + cap) 7) with (cap mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; clear - AL CAP; Z.div_mod_to_equations; lia).
  zstep; if_cases Kal; zify_cond Kal.   (* [comment removed for export] *)
  all: swap 1 2.                       (* [comment removed for export] *)
  1: assert (ALI : cap mod 8 = 0) by (clear - Kal M8; lia).
  2: assert (NAL : cap mod 8 <> 0) by (clear - Kal M8; lia).
  2: destruct (SB NAL) as [SBC0 EOK];
     pose proof (rw_cells_transport asegs _ _ _ _ _ SBC0 MUF WM ltac:(cbn [disjoint_from cells_size csize]; lia)) as SBC; clear SBC0.
  all: clear SB MUF Kal.
  (* [comment removed for export] *)
  2: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => pose proof (shadow_join mm beg cap junk sb ltac:(lia) NAL BODY SBC) as SHJ end;
     shrink_detour NAL M8E M8 M7 CAP AL SBC RSH SHF SHL R8 beg cap sb; clear SBC BODY.
  1: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => pose proof (shadow_whole_aligned mm beg cap junk ltac:(lia) ALI BODY) as SHJ end; clear BODY.
  all: shrink_tail.
  all: call_sp (poison_shadow_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ beg (rup8 cap) 252);
       first [ exact CEIL | reflexivity | (rewrite Hsp; exact ST) | eassumption
             | (unfold poison_cells; repeat lazymatch goal with |- _ /\ _ => split end; assumption)
             | (unfold rup8, rdn8; clear - AL CAP M7 M8; Z.div_mod_to_equations; lia)
             | (intros X; exfalso; clear - X; lia)
             | lia | (rewrite Hsp; solve_rng) | solve_rng | idtac ].
  all: lazymatch goal with P : stk asegs ?mm ?a _, H : stk asegs ?mm _ ?a |- _ => rename H into ST9 end.   (* [comment removed for export] *)
  all: zstep; let K := fresh "Kt" in if_cases K; zify_cond K; [| exfalso; lia].   (* [comment removed for export] *)
  all: do 10 zstep.                                    (* [comment removed for export] *)
  all: (pose proof (stk_merge asegs _ _ _ _ ST9 STP ltac:(lia)) as ST9'; clear ST9 STP); release_frame FR ST9' (bv_unsigned sp).
  all: finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition annot_grow_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (beg cap lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - ANNOT_STACK, bv_unsigned sp); (shad beg, shad beg + shlen (rup8 cap))] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (shad beg) [CB (Z.to_nat (cap / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (cap / 8)))]
    /\ (cap mod 8 <> 0 -> rw_cells asegs m' (shad beg + cap / 8) [C1 (Z_to_bv 8 (cap mod 8))]).

(* [comment removed for export] *)
End CANSEC2.
Local Ltac grow_detour Kal M8E M8 M7 CAP AL SBC RSH SHF SHL R8 beg cap sb :=
  zstep; rewrite land_align8, M8E by lia;     (* [comment removed for export] *)
  zstep; zstep;
  let Ki := fresh "Ki" in if_cases Ki; zify_cond Ki; [exfalso; clear - Ki CAP; lia|];   (* [comment removed for export] *)
  zstep;                                                                                 (* [comment removed for export] *)
  zstep; let Kj := fresh "Kj" in if_cases Kj; zify_cond Kj; [exfalso; clear - Kj Kal M8; lia|];        (* [comment removed for export] *)
  do 5 zstep;                                 (* [comment removed for export] *)
  let HR := fresh "HR" in let ACC := fresh "ACC" in let SBR := fresh "SBR" in let Kk := fresh "Kk" in
  let SB1 := fresh "SB1" in let SB2 := fresh "SB2" in
  lazymatch goal with |- evtF _ ?RNG _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (end_byte_read mm beg cap sb AL ltac:(lia) SBC) as HR;
    assert (ACC : rng RNG (2147450880 + Z.shiftr (beg + cap) 3) 1)
      by (eapply rng_sub'; [exact RSH|]; rewrite SHF, SHL, R8, Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - AL CAP M7 M8 Kal; Z.div_mod_to_equations; lia)
  end;
  zstep; clear HR ACC; rewrite sxb_sval;       (* [comment removed for export] *)
  pose proof (sval_range sb) as SBR;
  lazymatch goal with EOK : end_byte_ok cap sb |- _ => destruct EOK as [SB1 SB2] end;
  zstep; if_cases Kk; zify_cond Kk; [ exfalso; clear - Kk SB1 SBR; rewrite ?unsigned_sval in Kk; apply SB1; apply sval_zero_iff; lia |];
  zstep; unfold bv_lts; rewrite !signed_lit_small64 by lia;   (* [comment removed for export] *)
  replace (cap mod 8 <? sval sb) with false by (symmetry; apply Z.ltb_ge; lia); cbn [negb];
  clear Ki Kj Kk SB1 SB2 SBR.

Section CANSEC3. Context {rc : runConstT}.
Lemma annot_grow_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (beg cap lo : Z) (junk : list byte) (sb : byte),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - ANNOT_STACK ->
  poison_cells m -> annot_cells m ->
  a0 = Z_to_bv 64 beg -> a1 = Z_to_bv 64 (beg + cap) -> a2 = Z_to_bv 64 beg -> a3 = Z_to_bv 64 (beg + cap) ->
  beg mod 8 = 0 -> 0 < cap <= 2^40 -> ablk beg (beg + rup8 cap) -> beg + rup8 cap <= 2^47 ->     (* [comment removed for export] *)
  cap / 8 < 65536 ->                                           (* [comment removed for export] *)
  rw_cells asegs m (shad beg) [CB (Z.to_nat (cap / 8)) junk] ->
  (cap mod 8 <> 0 -> rw_cells asegs m (shad beg + cap / 8) [C1 sb] /\ end_byte_ok cap sb) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad beg) (shlen (rup8 cap)) ->
  evtF asegs RNG (annot_grow_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc beg cap lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AANNOT) fc None m (seg_rom asegs)).
Proof.
  intros until sb. intros MI ST CEIL LO PC AC -> -> -> -> AL CAP KH HE SMALL BODY SB RIMG RSTK RSH.
  unfold ANNOT_STACK, AANNOT in *. pose proof KH as KH0. unfold ablk, AIMG_HI, KLS in KH. pose proof atop_range as ATR.   (* [comment removed for export] *)
  pose proof PC as PC'. destruct PC' as (GOT & GOTMS & REAL & SHB & LAY & CANP & THR). destruct AC as (DCO & GVB & VERB).
  pose proof (munch_refl [(bv_unsigned sp - 2720, bv_unsigned sp); (shad beg, shad beg + shlen (rup8 cap))] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (R8 : rup8 cap = cap + 7 - (cap + 7) mod 8 /\ 0 <= (cap + 7) mod 8 < 8 /\ 0 <= cap mod 8 < 8) by (unfold rup8, rdn8; repeat split; try lia; apply Z.mod_pos_bound; lia).
  destruct R8 as (R8 & M7 & M8).
  assert (SHF : shad beg = 2147450880 + beg / 8 /\ shlen (rup8 cap) = rup8 cap / 8 /\ 8 * (cap / 8) = cap - cap mod 8 /\ shlen (rdn8 cap) = cap / 8).
  { unfold shad, shlen, rdn8, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. repeat split; try reflexivity; clear - CAP; Z.div_mod_to_equations; lia. }
  destruct SHF as (SHF & SHL & DIV8 & SHL2).
  assert (M8E : (beg + cap) mod 8 = cap mod 8) by (clear - AL CAP; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 2720, bv_unsigned sp)]%Z m) as MUF.
  (* [comment removed for export] *)
  carve_frame 56%nat ST;
       (destruct (stk_split asegs _ lo (bv_unsigned sp + -2128) (bv_unsigned sp + -56) ST ltac:(lia)) as [ST' STP]; clear ST; rename ST' into ST).
  do 9 zstep.                 (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  zstep; zstep.               (* [comment removed for export] *)
  zstep; rewrite zxb_lit by lia.   (* [comment removed for export] *)
  zstep; let K := fresh "Ka" in if_cases K; zify_cond K; [exfalso; clear - K; lia|].   (* [comment removed for export] *)
  do 3 zstep.                 (* [comment removed for export] *)
  zstep; zstep; zstep; lits.  (* [comment removed for export] *)
  zstep; zstep; let K := fresh "Kb" in if_cases K; zify_cond K; [exfalso; clear - K; lia|].   (* [comment removed for export] *)
  zstep; let K := fresh "Kc" in if_cases K; zify_cond K; [| exfalso; clear - K CAP; lia].   (* [comment removed for export] *)
  zstep; let K := fresh "Kd" in if_cases K; zify_cond K; [exfalso; clear - K CAP; lia|].   (* [comment removed for export] *)
  zstep; let K := fresh "Ke" in if_cases K; zify_cond K; [exfalso; clear - K CAP; lia|].   (* [comment removed for export] *)
  zstep; let K := fresh "Kf" in if_cases K; zify_cond K; [exfalso; clear - K CAP; lia|].   (* [comment removed for export] *)
  do 4 zstep.                 (* [comment removed for export] *)
  zstep; let K := fresh "Kg" in if_cases K; zify_cond K; [exfalso; clear - K CAP; lia|].   (* [comment removed for export] *)
  zstep; let K := fresh "Kh" in if_cases K; zify_cond K; [exfalso; clear - K CAP; lia|].   (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  replace (Z.land (beg + cap) 7) with (cap mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; clear - AL CAP; Z.div_mod_to_equations; lia).
  zstep; if_cases Kal; zify_cond Kal.   (* [comment removed for export] *)
  all: swap 1 2.                       (* [comment removed for export] *)
  1: assert (ALI : cap mod 8 = 0) by (clear - Kal M8; lia).
  2: assert (NAL : cap mod 8 <> 0) by (clear - Kal M8; lia).
  2: destruct (SB NAL) as [SBC0 EOK];
     pose proof (rw_cells_transport asegs _ _ _ _ _ SBC0 MUF WM ltac:(cbn [disjoint_from cells_size csize]; lia)) as SBC; clear SBC0.
  all: clear SB MUF Kal.
  2: grow_detour NAL M8E M8 M7 CAP AL SBC RSH SHF SHL R8 beg cap sb.
  (* [comment removed for export] *)
  all: do 3 zstep.                 (* [comment removed for export] *)
  all: zstep.                      (* [comment removed for export] *)
  all: replace (Z.land beg 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; clear - AL; lia).
  all: zstep; if_lit.              (* [comment removed for export] *)
  all: zstep; zstep.               (* [comment removed for export] *)
  all: zstep; let K := fresh "Kt" in if_cases K; zify_cond K; [| exfalso; clear - K CAP; lia].   (* [comment removed for export] *)
  all: zstep; rewrite land_align8 by lia.     (* [comment removed for export] *)
  all: replace (beg - beg mod 8) with beg by (clear - AL; lia).
  all: zstep; let K := fresh "Kt" in if_cases K; zify_cond K; [exfalso; clear - K CAP; lia|].   (* [comment removed for export] *)
  all: zstep.                      (* [comment removed for export] *)
  all: zstep; rewrite land_align8, M8E by lia.        (* [comment removed for export] *)
  all: zstep; zstep; rewrite land_align8 by lia.      (* [comment removed for export] *)
  all: replace (beg + cap + 7 - (beg + cap + 7) mod 8) with (beg + rup8 cap) by (unfold rup8, rdn8; clear - AL CAP; Z.div_mod_to_equations; lia).
  all: zstep; let K := fresh "Kge" in if_cases K; zify_cond K; first [ exfalso; clear - K ALI CAP M8; Z.div_mod_to_equations; lia | idtac ].   (* [comment removed for export] *)
  (* [comment removed for export] *)
  3: zstep; zstep; rewrite land_align8 by lia;         (* [comment removed for export] *)
     replace (beg + cap + 7 - (beg + cap + 7) mod 8) with (beg + rup8 cap) by (unfold rup8, rdn8; clear - AL CAP; Z.div_mod_to_equations; lia);
     zstep; let K := fresh "Kt" in if_cases K; zify_cond K; [| exfalso; clear - K; lia].   (* [comment removed for export] *)
  1,2: zstep; zstep; zstep;                           (* [comment removed for export] *)
       replace (beg + cap - cap mod 8 - beg) with (rdn8 cap) by (unfold rdn8; lia);
       zstep;                                         (* [comment removed for export] *)
       call_sp (poison_shadow_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ beg (rdn8 cap) 0);
       first [ exact CEIL | reflexivity | (rewrite Hsp; exact ST) | (rewrite SHL2; exact BODY) | eassumption
             | (unfold poison_cells; repeat lazymatch goal with |- _ /\ _ => split end; assumption)
             | (unfold rdn8; clear - AL CAP M7 M8 Kge HE R8 KH ATR; Z.div_mod_to_equations; lia)
             | (eapply ablk_sub; [exact KH0 | clear; lia | unfold rup8, rdn8; clear - CAP M7 M8; Z.div_mod_to_equations; lia])
             | (intros _; rewrite SHL2; exact SMALL)
             | lia | (rewrite Hsp; solve_rng) | solve_rng | idtac ].
  (* [comment removed for export] *)
  all: zstep; let K := fresh "Keq" in if_cases K; zify_cond K;
       first [ exfalso; clear - K ALI R8 M7 M8 CAP; Z.div_mod_to_equations; lia
             | exfalso; clear - K NAL R8 M7 M8 CAP; Z.div_mod_to_equations; lia | clear K ].   (* [comment removed for export] *)
  2,3: zstep; replace (beg + rup8 cap - (beg + cap - cap mod 8)) with 8 by (clear - NAL R8 M7 M8 CAP; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  2,3: zstep; zstep; if_lit.                          (* [comment removed for export] *)
  2,3: zstep; replace (Z.land (beg + cap) 7) with (cap mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; clear - AL CAP; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  2,3: zstep; zstep.                                  (* [comment removed for export] *)
  2,3: call m2s_spec; first [ eassumption | (rewrite ?unsigned_lit by (clear - KH HE R8 M7 M8 CAP NAL ATR; Z.div_mod_to_equations; lia); unfold KLOW, KHIGH, KEND; clear - KH HE R8 M7 M8 CAP NAL ATR; Z.div_mod_to_equations; lia) | idtac ].
  2,3: rewrite ?unsigned_lit by (clear - KH HE R8 M7 M8 CAP NAL ATR; Z.div_mod_to_equations; lia).
  2,3: replace (shad (beg + cap - cap mod 8)) with (shad beg + cap / 8) by (unfold shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - AL CAP M8; Z.div_mod_to_equations; lia).
  2,3: set (SBA := shad beg + cap / 8) in *; zstep; rewrite le1_sym; mem_after_store; subst SBA.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: do 10 zstep.
  all: match goal with P : stk asegs ?mm ?a _, H : stk asegs ?mm _ ?a |- _ => (pose proof (stk_merge asegs _ _ _ _ H P ltac:(lia)) as ST9'; clear H P); release_frame FR ST9' (bv_unsigned sp) end.
  all: finish.
  (* [comment removed for export] *)
  all: try (intros NE; exfalso; apply NE; exact ALI).
  all: try (intros _; assumption).
  all: try (rewrite SHL2 in *; assumption).
  (* [comment removed for export] *)
  all: assert (Q0 : cap / 8 = 0) by (clear - CAP Kge M8; Z.div_mod_to_equations; lia);
       rewrite Q0 in BODY |- *; cbn [Z.to_nat repeat];
       pose proof BODY as B0; destruct B0 as [[[LJ _] _] _]; cbn in LJ;
       destruct junk; [exact BODY| cbn in LJ; lia].
Qed.
End CANSEC3.
