(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import
  PropExec CatSim CatExec SeqExec StoreOk ShapeAlg ShapeAlgCfg LibWritev LibWritevCfg.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc AsanWBase AsanWWritev.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition SW_WORDS : list (Z * Z) :=
  [(0x88, 0x00000073); (0x90, 0x09651863); (0xe4, 0x00800713); (0xe8, 0x000a0593); (0xec, 0x00e98733);
   (0xf0, 0x00073783); (0xf4, 0x40ab0b33); (0xf8, 0x0784a503); (0xfc, 0x40c9093b); (0x100, 0x40d787b3);
   (0x104, 0x00f73023); (0x108, 0x04200893); (0x10c, 0x00090613); (0x110, 0x00000073); (0x118, 0x000a0993);
   (0x11c, 0xf7650ce3); (0x120, 0x02054c63); (0x124, 0x0089b583); (0x128, 0x00a5b633); (0x12c, 0x00461a13);
   (0x130, 0x01498a33); (0x134, 0x000a3703); (0x138, 0x40c006b3); (0x13c, 0x00b6f6b3); (0x140, 0x40d506b3);
   (0x144, 0x00d70733); (0x148, 0x00ea3023); (0x14c, 0xf8a5fce3); (0x150, 0x01800713); (0x154, 0xf95ff06f)]%Z.

(* [comment removed for export] *)
Definition SR_WORDS : list (Z * Z) :=
  [(0x0, 0xfffff5b7); (0x4, 0x0015859b); (0x8, 0x02b56663); (0x34, 0x00008067)]%Z.

(* [comment removed for export] *)
Local Ltac dec := wdec.
Lemma D_88  : decode_any (Z_to_bv 32 0x00000073) = None \/ True. Proof. right; exact I. Qed.
Lemma E_88  : is_ecall (Z_to_bv 32 0x00000073) = true. Proof. dec. Qed.
Lemma D_90  : decode_any (Z_to_bv 32 0x09651863) = Some (Branch BC_NE 10 22 144, 4%Z). Proof. dec. Qed.
Lemma D_e4  : decode_any (Z_to_bv 32 0x00800713) = Some (OpImm ALU_ADD 14 0 8, 4%Z). Proof. dec. Qed.
Lemma D_e8  : decode_any (Z_to_bv 32 0x000a0593) = Some (OpImm ALU_ADD 11 20 0, 4%Z). Proof. dec. Qed.
Lemma D_ec  : decode_any (Z_to_bv 32 0x00e98733) = Some (Op ALU_ADD 14 19 14, 4%Z). Proof. dec. Qed.
Lemma D_f0  : decode_any (Z_to_bv 32 0x00073783) = Some (Load SZ8 true 15 14 0, 4%Z). Proof. dec. Qed.
Lemma D_f4  : decode_any (Z_to_bv 32 0x40ab0b33) = Some (Op ALU_SUB 22 22 10, 4%Z). Proof. dec. Qed.
Lemma D_f8  : decode_any (Z_to_bv 32 0x0784a503) = Some (Load SZ4 true 10 9 120, 4%Z). Proof. dec. Qed.
Lemma D_fc  : decode_any (Z_to_bv 32 0x40c9093b) = Some (Op32 ALU_SUB 18 18 12, 4%Z). Proof. dec. Qed.
Lemma D_100 : decode_any (Z_to_bv 32 0x40d787b3) = Some (Op ALU_SUB 15 15 13, 4%Z). Proof. dec. Qed.
Lemma D_104 : decode_any (Z_to_bv 32 0x00f73023) = Some (Store SZ8 14 15 0, 4%Z). Proof. dec. Qed.
Lemma D_108 : decode_any (Z_to_bv 32 0x04200893) = Some (OpImm ALU_ADD 17 0 66, 4%Z). Proof. dec. Qed.
Lemma D_10c : decode_any (Z_to_bv 32 0x00090613) = Some (OpImm ALU_ADD 12 18 0, 4%Z). Proof. dec. Qed.
Lemma D_118 : decode_any (Z_to_bv 32 0x000a0993) = Some (OpImm ALU_ADD 19 20 0, 4%Z). Proof. dec. Qed.
Lemma D_11c : decode_any (Z_to_bv 32 0xf7650ce3) = Some (Branch BC_EQ 10 22 8056, 4%Z). Proof. dec. Qed.
Lemma D_120 : decode_any (Z_to_bv 32 0x02054c63) = Some (Branch BC_LT 10 0 56, 4%Z). Proof. dec. Qed.
Lemma D_124 : decode_any (Z_to_bv 32 0x0089b583) = Some (Load SZ8 true 11 19 8, 4%Z). Proof. dec. Qed.
Lemma D_128 : decode_any (Z_to_bv 32 0x00a5b633) = Some (Op ALU_SLTU 12 11 10, 4%Z). Proof. dec. Qed.
Lemma D_12c : decode_any (Z_to_bv 32 0x00461a13) = Some (ShiftImm ALU_SLL 20 12 4, 4%Z). Proof. dec. Qed.
Lemma D_130 : decode_any (Z_to_bv 32 0x01498a33) = Some (Op ALU_ADD 20 19 20, 4%Z). Proof. dec. Qed.
Lemma D_134 : decode_any (Z_to_bv 32 0x000a3703) = Some (Load SZ8 true 14 20 0, 4%Z). Proof. dec. Qed.
Lemma D_138 : decode_any (Z_to_bv 32 0x40c006b3) = Some (Op ALU_SUB 13 0 12, 4%Z). Proof. dec. Qed.
Lemma D_13c : decode_any (Z_to_bv 32 0x00b6f6b3) = Some (Op ALU_AND 13 13 11, 4%Z). Proof. dec. Qed.
Lemma D_140 : decode_any (Z_to_bv 32 0x40d506b3) = Some (Op ALU_SUB 13 10 13, 4%Z). Proof. dec. Qed.
Lemma D_144 : decode_any (Z_to_bv 32 0x00d70733) = Some (Op ALU_ADD 14 14 13, 4%Z). Proof. dec. Qed.
Lemma D_148 : decode_any (Z_to_bv 32 0x00ea3023) = Some (Store SZ8 20 14 0, 4%Z). Proof. dec. Qed.
Lemma D_14c : decode_any (Z_to_bv 32 0xf8a5fce3) = Some (Branch BC_GEU 11 10 8088, 4%Z). Proof. dec. Qed.
Lemma D_150 : decode_any (Z_to_bv 32 0x01800713) = Some (OpImm ALU_ADD 14 0 24, 4%Z). Proof. dec. Qed.
Lemma D_154 : decode_any (Z_to_bv 32 0xf95ff06f) = Some (Jal 0 2097044, 4%Z). Proof. dec. Qed.
Lemma D_s0  : decode_any (Z_to_bv 32 0xfffff5b7) = Some (Lui 11 1048575, 4%Z). Proof. dec. Qed.
Lemma D_s4  : decode_any (Z_to_bv 32 0x0015859b) = Some (OpImm32 11 11 1, 4%Z). Proof. dec. Qed.
Lemma D_s8  : decode_any (Z_to_bv 32 0x02b56663) = Some (Branch BC_LTU 10 11 44, 4%Z). Proof. dec. Qed.
Lemma D_s34 : decode_any (Z_to_bv 32 0x00008067) = Some (Jalr 0 1 0, 4%Z). Proof. dec. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition CLOB : list reg := [1; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20; 22].

(* [comment removed for export] *)
Record SWF (ms0 ms : machine_state) (lo hi : Z) : Prop := {
  swf_svc : ms_svc_pending ms = None;
  swf_rom : ms_rom ms = ms_rom ms0;
  swf_fregs : ms_fregs ms = ms_fregs ms0;
  swf_fcsr : ms_fcsr ms = ms_fcsr ms0;
  swf_resv : ms_resv ms = ms_resv ms0 \/ ms_resv ms = None;
  swf_regs : forall r, ~ In r CLOB -> rg ms r = rg ms0 r;
  swf_mem : forall x : word, ~ (lo <= bv_unsigned x < hi)%Z -> ms_mem ms x = ms_mem ms0 x;
  swf_grows : mem_grows (ms_mem ms0) (ms_mem ms)
}.

Lemma SWF_setx : forall ms0 S lo hi rd v p r m,
  SWF ms0 S lo hi -> (rd = 0 \/ In rd CLOB) -> r = ms_resv S -> m = ms_mem S -> SWF ms0 (setx S rd v p r m) lo hi.
Proof.
  intros ms0 S lo hi rd v p r m [H1 H2 H3 H4 H5 H6 H7 H8] Hrd -> ->. constructor;
    [reflexivity | exact H2 | exact H3 | exact H4 | exact H5 | | exact H7 | exact H8].
  intros r Hr. rewrite <- (H6 r Hr).
  destruct Hrd as [->|Hin]; [apply rg_setx_x0|].
  apply rg_setx_other. intros ->. exact (Hr Hin).
Qed.

Lemma SWF_store : forall ms0 S lo hi p (a : word) (bs : list byte) r m,
  SWF ms0 S lo hi ->
  r = inval a (ms_resv S) -> m = write_to_mem (ms_mem S) a bs ->
  (lo <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat (length bs) <= hi)%Z -> (hi <= 2 ^ 64)%Z ->
  SWF ms0 (setx S 0 w0 p r m) lo hi.
Proof.
  intros ms0 S lo hi p a bs r m [H1 H2 H3 H4 H5 H6 H7 H8] -> -> Hlo Hhi H64.
  constructor; [reflexivity | exact H2 | exact H3 | exact H4 | | | | ].
  - rewrite resv_setx.
    destruct (inval_cases a (ms_resv S)) as [E|E]; rewrite E; [exact H5 | right; reflexivity].
  - intros r Hr. rewrite rg_setx_x0. exact (H6 r Hr).
  - intros x Hx. rewrite mem_setx, w2m_outside; [exact (H7 x Hx) | lia | lia].
  - intros x Hx. rewrite mem_setx. apply w2m_keeps_some. exact (H8 x Hx).
Qed.

Lemma adv_latch : forall S v,
  advance_past_svc (set_gpr0 (latch S) v) = setx S 10 v (ms_pc_val S + Z_to_bv 64 4) (ms_resv S) (ms_mem S).
Proof. reflexivity. Qed.

Lemma gpr_latch0 : forall S, ms_gpr (latch S) 0 = rg S 10. Proof. reflexivity. Qed.
Lemma gpr_latch1 : forall S, ms_gpr (latch S) 1 = rg S 11. Proof. reflexivity. Qed.
Lemma gpr_latch2 : forall S, ms_gpr (latch S) 2 = rg S 12. Proof. reflexivity. Qed.

Lemma FR_SWF : forall ms0 S S' lo hi rs,
  SWF ms0 S lo hi -> FR rs S S' -> (forall r, In r rs -> In r CLOB) -> SWF ms0 S' lo hi.
Proof.
  intros ms0 S S' lo hi rs [H1 H2 H3 H4 H5 H6 H7 H8] (F1 & F2 & F3 & F4 & F5 & F6 & F7) Hinc.
  constructor.
  - exact F1.
  - rewrite F2. exact H2.
  - rewrite F3. exact H3.
  - rewrite F4. exact H4.
  - rewrite F5. exact H5.
  - intros r Hr. rewrite F7; [exact (H6 r Hr)|]. intros Hin. exact (Hr (Hinc r Hin)).
  - intros x Hx. rewrite F6. exact (H7 x Hx).
  - rewrite F6. exact H8.
Qed.

Lemma SWF_refl : forall S lo hi, ms_svc_pending S = None -> SWF S S lo hi.
Proof.
  intros S lo hi H. constructor;
    [exact H | reflexivity | reflexivity | reflexivity | left; reflexivity | intros; reflexivity | intros; reflexivity
    | apply mem_grows_refl].
Qed.

Lemma SWF_trans : forall ms0 S S' lo hi lo' hi',
  SWF ms0 S lo hi -> SWF S S' lo' hi' -> (lo <= lo')%Z -> (hi' <= hi)%Z -> SWF ms0 S' lo hi.
Proof.
  intros ms0 S S' lo hi lo' hi' [H1 H2 H3 H4 H5 H6 H7 H8] [G1 G2 G3 G4 G5 G6 G7 G8] Hl Hh.
  constructor.
  - exact G1.
  - rewrite G2. exact H2.
  - rewrite G3. exact H3.
  - rewrite G4. exact H4.
  - destruct G5 as [E|E]; [rewrite E; exact H5 | right; exact E].
  - intros r Hr. rewrite (G6 r Hr). exact (H6 r Hr).
  - intros x Hx. rewrite (G7 x ltac:(lia)). exact (H7 x Hx).
  - intros x Hx. apply G8. apply H8. exact Hx.
Qed.

Ltac rwregs :=
  repeat match goal with H : rg ?S ?r = _ |- context [rg ?S ?r] => rewrite H end.

Ltac vnorm :=
  unfold w0; rewrite ?alu_add, ?alu_sub, ?zw_add, ?zw_sub, ?zw_add_sext; lits; rewrite ?Z.add_0_r, ?Z.sub_0_r.

Ltac w2m_out :=
  repeat (rewrite rdn_w2m_outZ;
          [ | lia | rewrite ?length_store8; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia
            | cbn [msz_n Z.of_nat Pos.of_succ_nat Pos.succ]; lia
            | rewrite ?length_store8; cbn [msz_n Z.of_nat Pos.of_succ_nat Pos.succ]; lia ]).

Ltac addr_fix R :=
  match type of R with rdn _ _ (Z_to_bv 64 ?e') _ = _ =>
    match goal with |- rdn _ _ (Z_to_bv 64 ?e) _ = _ => replace e with e' by lia end end.

Ltac side_ld R := rewrite ?mem_setx; rgn; rwregs; vnorm; w2m_out; addr_fix R; exact R.

(* [comment removed for export] *)
Ltac side_st SOK :=
  rewrite ?mem_setx; rgn; rwregs; vnorm; repeat apply store_ok_w2m;
  eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?bvu_z by lia; cbn [msz_n Z.of_nat Pos.of_succ_nat Pos.succ]; lia.

Ltac acc_side NL :=
  rgn; rwregs; vnorm; apply acc_ok_one; rewrite bvu_z by lia; cbn [msz_n Z.of_nat Pos.of_succ_nat Pos.succ];
  [ lia | eapply no_lazy_sub; [exact NL | lia | lia] ].

Ltac wld F D R NL :=
  eapply rzc_acc;
  [ assumption
  | reflexivity
  | eapply wacc_Load; [ fetch_tac F | reflexivity | exact D | side_ld R ]
  | acc_side NL
  | pcn ].

Ltac wsd F D SOK NL :=
  eapply rzc_acc;
  [ assumption
  | reflexivity
  | eapply wacc_Store; [ fetch_tac F | reflexivity | exact D | side_st SOK ]
  | acc_side NL
  | pcn ].

Ltac nst := rgn; rwregs; rewrite ?load8; vnorm.

Ltac inclob := first [ left; reflexivity | right; cbn [In CLOB]; repeat first [ left; reflexivity | right ] ].

Ltac swf_chain Hsvc :=
  repeat first
   [ (eapply SWF_store; [ | reflexivity | reflexivity | rewrite bvu_z by lia; lia
                        | rewrite bvu_z by lia; rewrite length_store8; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                        | lia ])
   | (eapply SWF_setx; [ | inclob | reflexivity | reflexivity ]) ];
  first [ apply SWF_refl; exact Hsvc | idtac ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record SWCode (segs : list Segment) (b sr wj1 wj2 : Z) (ij1 ij2 : bv 21) : Prop := {
  swc_W : words_ok segs b SW_WORDS = true;
  swc_R : words_ok segs sr SR_WORDS = true;
  swc_j1f : fetch_word segs (pcw b 0x8c) = Some (Z_to_bv 32 wj1);
  swc_j1e : is_ecall (Z_to_bv 32 wj1) = false;
  swc_j1d : decode_any (Z_to_bv 32 wj1) = Some (Jal 1 ij1, 4%Z);
  swc_j1t : (b + 0x8c + bv_signed ij1 = sr)%Z;
  swc_j2f : fetch_word segs (pcw b 0x114) = Some (Z_to_bv 32 wj2);
  swc_j2e : is_ecall (Z_to_bv 32 wj2) = false;
  swc_j2d : decode_any (Z_to_bv 32 wj2) = Some (Jal 1 ij2, 4%Z);
  swc_j2t : (b + 0x114 + bv_signed ij2 = sr)%Z;
  swc_bnd : (0 <= b /\ b + 0x200 <= 2 ^ 47 /\ 0 <= sr /\ sr + 0x40 <= 2 ^ 47 /\ b mod 4 = 0)%Z
}.

Section SW.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variables b sr : Z.
Variables (wj1 wj2 : Z) (ij1 ij2 : bv 21).


Hypothesis HC : SWCode segs b sr wj1 wj2 ij1 ij2.

Local Ltac inw := repeat (first [left; reflexivity | right]).
Local Ltac fw := apply (words_get segs b SW_WORDS); [exact (swc_W _ _ _ _ _ _ _ HC) | inw | lia].
Local Ltac fr := apply (words_get segs sr SR_WORDS); [exact (swc_R _ _ _ _ _ _ _ HC) | inw | lia].

Lemma F_88  : fetch_word segs (pcw b 0x88)  = Some (Z_to_bv 32 0x00000073). Proof. fw. Qed.
Lemma F_90  : fetch_word segs (pcw b 0x90)  = Some (Z_to_bv 32 0x09651863). Proof. fw. Qed.
Lemma F_e4  : fetch_word segs (pcw b 0xe4)  = Some (Z_to_bv 32 0x00800713). Proof. fw. Qed.
Lemma F_e8  : fetch_word segs (pcw b 0xe8)  = Some (Z_to_bv 32 0x000a0593). Proof. fw. Qed.
Lemma F_ec  : fetch_word segs (pcw b 0xec)  = Some (Z_to_bv 32 0x00e98733). Proof. fw. Qed.
Lemma F_f0  : fetch_word segs (pcw b 0xf0)  = Some (Z_to_bv 32 0x00073783). Proof. fw. Qed.
Lemma F_f4  : fetch_word segs (pcw b 0xf4)  = Some (Z_to_bv 32 0x40ab0b33). Proof. fw. Qed.
Lemma F_f8  : fetch_word segs (pcw b 0xf8)  = Some (Z_to_bv 32 0x0784a503). Proof. fw. Qed.
Lemma F_fc  : fetch_word segs (pcw b 0xfc)  = Some (Z_to_bv 32 0x40c9093b). Proof. fw. Qed.
Lemma F_100 : fetch_word segs (pcw b 0x100) = Some (Z_to_bv 32 0x40d787b3). Proof. fw. Qed.
Lemma F_104 : fetch_word segs (pcw b 0x104) = Some (Z_to_bv 32 0x00f73023). Proof. fw. Qed.
Lemma F_108 : fetch_word segs (pcw b 0x108) = Some (Z_to_bv 32 0x04200893). Proof. fw. Qed.
Lemma F_10c : fetch_word segs (pcw b 0x10c) = Some (Z_to_bv 32 0x00090613). Proof. fw. Qed.
Lemma F_110 : fetch_word segs (pcw b 0x110) = Some (Z_to_bv 32 0x00000073). Proof. fw. Qed.
Lemma F_118 : fetch_word segs (pcw b 0x118) = Some (Z_to_bv 32 0x000a0993). Proof. fw. Qed.
Lemma F_11c : fetch_word segs (pcw b 0x11c) = Some (Z_to_bv 32 0xf7650ce3). Proof. fw. Qed.
Lemma F_120 : fetch_word segs (pcw b 0x120) = Some (Z_to_bv 32 0x02054c63). Proof. fw. Qed.
Lemma F_124 : fetch_word segs (pcw b 0x124) = Some (Z_to_bv 32 0x0089b583). Proof. fw. Qed.
Lemma F_128 : fetch_word segs (pcw b 0x128) = Some (Z_to_bv 32 0x00a5b633). Proof. fw. Qed.
Lemma F_12c : fetch_word segs (pcw b 0x12c) = Some (Z_to_bv 32 0x00461a13). Proof. fw. Qed.
Lemma F_130 : fetch_word segs (pcw b 0x130) = Some (Z_to_bv 32 0x01498a33). Proof. fw. Qed.
Lemma F_134 : fetch_word segs (pcw b 0x134) = Some (Z_to_bv 32 0x000a3703). Proof. fw. Qed.
Lemma F_138 : fetch_word segs (pcw b 0x138) = Some (Z_to_bv 32 0x40c006b3). Proof. fw. Qed.
Lemma F_13c : fetch_word segs (pcw b 0x13c) = Some (Z_to_bv 32 0x00b6f6b3). Proof. fw. Qed.
Lemma F_140 : fetch_word segs (pcw b 0x140) = Some (Z_to_bv 32 0x40d506b3). Proof. fw. Qed.
Lemma F_144 : fetch_word segs (pcw b 0x144) = Some (Z_to_bv 32 0x00d70733). Proof. fw. Qed.
Lemma F_148 : fetch_word segs (pcw b 0x148) = Some (Z_to_bv 32 0x00ea3023). Proof. fw. Qed.
Lemma F_14c : fetch_word segs (pcw b 0x14c) = Some (Z_to_bv 32 0xf8a5fce3). Proof. fw. Qed.
Lemma F_150 : fetch_word segs (pcw b 0x150) = Some (Z_to_bv 32 0x01800713). Proof. fw. Qed.
Lemma F_154 : fetch_word segs (pcw b 0x154) = Some (Z_to_bv 32 0xf95ff06f). Proof. fw. Qed.
Lemma F_s0  : fetch_word segs (pcw sr 0x0)  = Some (Z_to_bv 32 0xfffff5b7). Proof. fr. Qed.
Lemma F_s4  : fetch_word segs (pcw sr 0x4)  = Some (Z_to_bv 32 0x0015859b). Proof. fr. Qed.
Lemma F_s8  : fetch_word segs (pcw sr 0x8)  = Some (Z_to_bv 32 0x02b56663). Proof. fr. Qed.
Lemma F_s34 : fetch_word segs (pcw sr 0x34) = Some (Z_to_bv 32 0x00008067). Proof. fr. Qed.

Lemma pcw_jal1 : pcw b 0x8c + sext 64 ij1 = pcw sr 0.
Proof. rewrite pcw_sext. unfold pcw. f_equal. pose proof (swc_j1t _ _ _ _ _ _ _ HC). lia. Qed.
Lemma pcw_jal2 : pcw b 0x114 + sext 64 ij2 = pcw sr 0.
Proof. rewrite pcw_sext. unfold pcw. f_equal. pose proof (swc_j2t _ _ _ _ _ _ _ HC). lia. Qed.
Lemma Hbnd : (0 <= b /\ b + 0x200 <= 2 ^ 47 /\ 0 <= sr /\ sr + 0x40 <= 2 ^ 47 /\ b mod 4 = 0)%Z.
Proof. exact (swc_bnd _ _ _ _ _ _ _ HC). Qed.

Section Walks.
Variable model : Model.
Hypothesis Hh : m_halted model = None.

(* [comment removed for export] *)
Lemma walk_sr : forall S T (o k : Z),
  ms_svc_pending S = None -> ms_pc_val S = pcw sr 0 -> rg S 1 = pcw b o ->
  (0 <= o <= 0x200)%Z -> (o mod 4 = 0)%Z ->
  rg S 10 = Z_to_bv 64 k -> (1 <= k <= 2 ^ 30)%Z ->
  (forall S', FR [11] S S' -> ms_pc_val S' = pcw b o -> realizes_cfg segs cfg (mkCfg S' model) T) ->
  realizes_cfg segs cfg (mkCfg S model) T.
Proof.
  intros S T o k Hsvc Hpc Hra Ho Hom Ha0 Hk HT.
  wst wacc_Lui F_s0 D_s0.
  wst wacc_OpImm32 F_s4 D_s4.
  wst wacc_Branch F_s8 D_s8.
  rgn. rewrite Ha0.
  match goal with |- context [branch_taken BC_LTU _ ?V] =>
    assert (HV : V = Z_to_bv 64 18446744073709547521) by (apply bv_eq; vm_compute; reflexivity); rewrite HV end.
  rewrite branch_ltu_z by lia. rewrite (proj2 (Z.ltb_lt k _)) by lia. pcn.
  wst wacc_Jalr F_s34 D_s34.
  rgn. pose proof Hbnd as HB. rewrite Hra, ret_pcw by lia.
  apply HT; [| reflexivity].
  repeat (apply FR_setx; [ | first [left; reflexivity | right; left; reflexivity] | reflexivity | reflexivity ]).
  apply FR_refl. exact Hsvc.
Qed.


End Walks.

End SW.
