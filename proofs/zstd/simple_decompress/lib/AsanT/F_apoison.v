(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase F_memset.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition poison_cells (m : amem) : Prop :=
     rw_cells bsegs m 0xc72f8 [C8 (Z_to_bv 64 0x161828); C8 (Z_to_bv 64 0xcd4f8); C8 (Z_to_bv 64 0xcfcf8);
                               C8 (Z_to_bv 64 0xd09e8); C8 (Z_to_bv 64 0xd09f0); C8 (Z_to_bv 64 0xd09e0)]
  /\ rw_cells bsegs m 0xc7328 [C8 (Z_to_bv 64 0xc91b8)]
  /\ rw_cells bsegs m 0xc91b0 [C8 (Z_to_bv 64 0xc0638); C8 (Z_to_bv 64 0xc0a3c)]
  /\ rw_cells bsegs m 0xcfcf8 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ rw_cells bsegs m 0xd09e0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m 0xcf55c [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m 0x1618a0 [C8 (Z_to_bv 64 18446744073709551615)].   (* [comment removed for export] *)

Lemma poison_cells_frame : forall m m' W,
  poison_cells m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv) W -> poison_cells m'.
Proof.
  intros m m' W PC MU WM HW.
  assert (D : forall A n, A + n <= AIMG_HI -> disjoint_from W A n).
  { intros A n HA. clear MU. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| exact IH]. }
  unfold poison_cells, AIMG_HI in *.
  destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  repeat split; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply D; cbn; lia]).
Qed.

(* [comment removed for export] *)
Definition poison_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (addr size v lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (shad addr, shad addr + shlen size)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (shad addr) [CB (Z.to_nat (shlen size)) (repeat (Z_to_bv 8 v) (Z.to_nat (shlen size)))].

End CANSEC1.
Local Ltac poison_tail sp v MU WM DST RSH FR ST :=
  do 3 step; do 8 step; step;
  eapply evtF_mono;
  [ eapply memset_spec;
    [ rewrite !unsigned_lit by (unfold shlen in *; rewrite ?Z.shiftr_div_pow2 in * by lia; Z.div_mod_to_equations; lia); exact DST
    | assumption
    | rewrite !unsigned_lit by (unfold shlen in *; rewrite ?Z.shiftr_div_pow2 in * by lia; Z.div_mod_to_equations; lia); exact RSH ]
  | ];
  let ms' := fresh "ms'" in let PO := fresh "PO" in let MU2 := fresh "MU2" in let WM2 := fresh "WM2" in
  let MI2 := fresh "MI2" in let DST2 := fresh "DST2" in let FR' := fresh "FR'" in let ST' := fresh "ST'" in
  intros ms' PO; unfold memset_post in PO; unfold poison_post; destruct_exs PO;
  destruct PO as (-> & MU2 & WM2 & MI2 & DST2);
  rewrite !unsigned_lit in MU2, DST2 by (unfold shlen in *; rewrite ?Z.shiftr_div_pow2 in * by lia; Z.div_mod_to_equations; lia);
  rewrite ?unsigned_lit in DST2 by lia; rewrite ?(Z.mod_small v 256) in DST2 by lia; change (0 mod 256) with 0 in DST2;
  do 16 eexists; split; [reflexivity|];
  split; [eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MU2]; let xq := fresh in let Hxq := fresh in intros xq Hxq; cbn in Hxq |- *; tauto |];
  split; [eapply wmono_trans; [exact WM| exact WM2] |]; split; [exact MI2|];
  split; [| exact DST2];
  pose proof (rw_cells_transport bsegs _ _ _ _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize]; lia)) as FR';
  pose proof (stk_transport_disjoint bsegs _ _ _ _ _ ST MU2 WM2 ltac:(cbn [disjoint_from]; lia)) as ST';
  eapply stk_release in FR'; [| exact ST' | lia]; cbn [cells_size csize Nat.add] in FR';
  match type of FR' with stk _ _ _ ?hi => replace hi with (bv_unsigned sp) in FR' by lia end; exact FR'.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Lemma poison_core_any : forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m m1 : amem) (addr size v lo : Z) (junk fj : list byte),
  stk bsegs m1 lo (bv_unsigned sp + -64) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv bsegs m1 ->
  poison_cells m1 ->
  rw_cells bsegs m1 (bv_unsigned sp + -64) [CB 8 fj; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch [(bv_unsigned sp - 64, bv_unsigned sp); (shad addr, shad addr + shlen size)]%Z m m1 -> wmono bsegs m m1 ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> ablk addr (addr + size) -> addr + size <= 2^47 ->     (* [comment removed for export] *)
  0 <= v < 256 ->
  rw_cells bsegs m1 (shad addr) [CB (Z.to_nat (shlen size)) junk] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) (shlen size) ->
  evtF bsegs RNG (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size v lo m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 addr) (Z_to_bv 64 size) (Z_to_bv 64 v) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x55d9c) fc None m1 (seg_rom bsegs)).
Proof.
  intros until fj. intros ST CEIL LO MI PC FR MU WM AL SL SZ HI HE V DST RIMG RSTK RSH.
  atop_facts. destruct PC as (GOT & GOTMS & REAL & SHB & LAY & CANP & THR).
  unfold ablk, AIMG_HI, KLS in HI.                     (* [comment removed for export] *)
  assert (SHR : 0x800bca00 <= shad addr /\ shad addr + shlen size <= 0x10007fff8000 /\ 0 < shlen size).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  zstep. step. if_cases K1; zify_cond K1.               (* [comment removed for export] *)
  { exfalso. apply K1. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact AL. }
  do 3 step.                                           (* [comment removed for export] *)
  do 4 zstep.                                          (* [comment removed for export] *)
  match goal with |- context [Z.land ?x 2147450879] => let v := eval vm_compute in (Z.land x 2147450879) in change (Z.land x 2147450879) with v end.
  step. if_cases K2; zify_cond K2.                     (* [comment removed for export] *)
  2: do 6 step.                                        (* [comment removed for export] *)
  2: zstep; step; if_cases K3; zify_cond K3; [| exfalso; lia].   (* [comment removed for export] *)
  2: do 3 step; do 2 zstep.                            (* [comment removed for export] *)
  2: step; if_cases K4; zify_cond K4; [exfalso; lia|].           (* [comment removed for export] *)
  2: step; if_cases K5; zify_cond K5; [| exfalso; lia].          (* [comment removed for export] *)
  2: step; do 2 zstep.                                 (* [comment removed for export] *)
  2: step; if_cases K6; zify_cond K6; [exfalso; lia|].
  2: step; if_cases K7; zify_cond K7; [| exfalso; lia].          (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: zstep; step; if_cases K8; zify_cond K8;
       [ exfalso; apply K8; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; exact SL |].
  all: do 2 zstep.                                     (* [comment removed for export] *)
  all: step; if_cases K9; zify_cond K9.                (* [comment removed for export] *)
  all: try (exfalso; lia).
  (* [comment removed for export] *)
  2: do 6 step; zstep.                                 (* [comment removed for export] *)
  2: step; if_cases K10; zify_cond K10; [| exfalso; lia].
  2: do 3 step; do 2 zstep.                            (* [comment removed for export] *)
  2: step; if_cases K11; zify_cond K11; [exfalso; lia|].
  2: step; if_cases K12; zify_cond K12; [exfalso; lia|].
  (* [comment removed for export] *)
  all: do 3 step.                                      (* [comment removed for export] *)
  all: step; if_lit.                                   (* [comment removed for export] *)
  all: do 5 zstep.                                     (* [comment removed for export] *)
  all: replace ((Z.shiftr (addr + size + -8) 3 + 1) mod 18446744073709551616 - Z.shiftr addr 3) with (shlen size)
      by (unfold shlen; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  all: change (2147450880 + Z.shiftr addr 3) with (shad addr).
  (* [comment removed for export] *)
  all: step; if_cases KV; zify_cond KV;
      [| do 2 step; lstep; step; if_cases KT; zify_cond KT;
         [| exfalso; rewrite ?Z.mod_small in KT by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia); clear -KT SHR; lia]].
  (* [comment removed for export] *)
  all: poison_tail sp v MU WM DST RSH FR ST.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma poison_shadow_any : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size v lo : Z) (junk : list byte),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv bsegs m ->
  poison_cells m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 v ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> ablk addr (addr + size) -> addr + size <= 2^47 ->     (* [comment removed for export] *)
  0 <= v < 256 ->
  rw_cells bsegs m (shad addr) [CB (Z.to_nat (shlen size)) junk] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) (shlen size) ->
  evtF bsegs RNG (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size v lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x55d68) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros ST CEIL LO MI PC -> -> -> AL SL SZ HI HE V DST RIMG RSTK RSH.
  atop_facts. pose proof PC as PC'. destruct PC' as (GOT & GOTMS & REAL & SHB & LAY & CANP & THR).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (shad addr, shad addr + shlen size)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  pose proof HI as HI'. unfold ablk, AIMG_HI, KLS in HI'.
  assert (SHR : 0x800bca00 <= shad addr /\ shad addr + shlen size <= 0x10007fff8000 /\ 0 < shlen size).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  word_range sp SPR.
  carve_frame 64%nat ST.
  do 8 step.                                           (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. if_cases KV; zify_cond KV.
  2: step; lstep; step; step; if_lit.                  (* [comment removed for export] *)
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
         eapply (poison_core_any RNG ra sp gp tp t0 t1 t2 s0 s1 _ _ _ a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mm addr size v lo junk) end.
  all: try eassumption; try lia.
  all: eapply poison_cells_frame; [exact PC | exact MU | exact WM | ].
  all: apply Forall_cons; [cbn; unfold AIMG_HI; lia|]; apply Forall_cons; [cbn; unfold AIMG_HI; lia | apply Forall_nil].
Qed.

(* [comment removed for export] *)
Lemma poison_shadow_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size v lo : Z) (junk : list byte),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv bsegs m ->
  poison_cells m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 v ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> ablk addr (addr + size) -> addr + size <= 2^47 ->
  0 <= v < 256 -> (v = 0 -> shlen size < 0x10000) ->
  rw_cells bsegs m (shad addr) [CB (Z.to_nat (shlen size)) junk] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) (shlen size) ->
  evtF bsegs RNG (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size v lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x55d68) fc None m (seg_rom bsegs)).
Proof. intros until junk. intros ST CEIL LO MI PC E0 E1 E2 AL SL SZ HI HE V _ DST RIMG RSTK RSH. eapply poison_shadow_any; eassumption. Qed.
End CANSEC2.
