(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac MemRange.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memmove RZ_seq_iface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma sc_signed : forall z, - 2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). change (2^64 / 2) with (2^63).
  rewrite Z.mod_small by lia. lia.
Qed.

Ltac dec_b H :=
  repeat (rewrite sc_signed in H by lia);
  repeat match type of H with
  | context [Z.ltb ?x ?y] => first [ rewrite (proj2 (Z.ltb_lt x y)) in H by lia | rewrite (proj2 (Z.ltb_ge x y)) in H by lia ]
  | context [Z.leb ?x ?y] => first [ rewrite (proj2 (Z.leb_le x y)) in H by lia | rewrite (proj2 (Z.leb_gt x y)) in H by lia ]
  | context [Z.eqb ?x ?y] => first [ rewrite (proj2 (Z.eqb_eq x y)) in H by lia | rewrite (proj2 (Z.eqb_neq x y)) in H by lia ]
  end;
  cbn [Z.b2z] in H;
  repeat match type of H with
  | context [Z.lxor ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v in H
  end.
Ltac br H := if_cases H; zify_cond H; dec_b H.
Ltac ub H := br H; [exfalso; lia|].

Ltac str REG A k :=
  lazymatch type of REG with stk ?segs ?m1 ?b0 ?b1 =>
    let a := cur_mem_addr in
    let SOK := fresh "SOK" in
    pose proof (stk_store_ok_at segs m1 b0 b1 A k a REG ltac:(lia) ltac:(lia) ltac:(addr_tac)) as SOK;
    zstep; store_done
  end.
Ltac ldRd RD A k :=
  lazymatch type of RD with rdbl ?segs ?m1 ?r0 ?r1 =>
    let a := cur_mem_addr in
    let bs := fresh "bs" in let RDb := fresh "RDb" in let L := fresh "L" bs in
    destruct (rdbl_read_at segs m1 r0 r1 A k a RD ltac:(lia) ltac:(lia) ltac:(addr_tac)) as [bs [L RDb]];
    zstep; try clear RDb
  end.

Definition sc_ovc (OV IP OP LEN B0 B1 R0 R1 : Z) : Prop :=
  (OV = 1 /\ R0 = B0 /\ R1 = B1 /\ IP <= OP)
  \/ (OV = 0 /\ IP + LEN + 32 <= R1 /\ (apart R0 (R1 - R0) B0 (B1 - B0) \/ (B0 <= R0 /\ R1 <= B1))).

Definition sc_inv (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 : word) (m : fmem) (SPV lo OP OENDW LEN B0 B1 : Z) (m1 : fmem) : Prop :=
  stk usegs m1 B0 B1 /\ stk usegs m1 lo (SPV + -80)
  /\ rw_cells usegs m1 (SPV + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
  /\ mem_inv usegs m1 /\ munch [(OP, Z.max (OP + LEN) (OENDW + 32)); (SPV - 80, SPV)] m m1 /\ wmono usegs m m1.
Ltac open_sci I := destruct I as (REG & STK & FR & MI & MU & WM).
Ltac close_sci := split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption.
Tactic Notation "use" uconstr(L) :=
  eapply L; first [ eassumption | close_sci | idtac ]; try (f_equal; lia); try lia.
Ltac mmv RD b0 b1 d sr :=
  lazymatch type of RD with rdbl ?segs ?m1 ?r0 ?r1 =>
    lazymatch goal with REG : stk segs m1 b0 b1 |- _ =>
      eapply evt_cut;
      [ eapply memmove_reg_spec with (D := d) (S := sr) (n := 16) (B0 := b0) (B1 := b1) (R0 := r0) (R1 := r1);
        [ exact REG | exact RD | lia | eassumption | try reflexivity; f_equal; lia | try reflexivity; f_equal; lia | reflexivity ]
      | post_call segs m1 ]
    end;
    lazymatch goal with H : stk segs ?m2 b0 b1, H2 : rdbl segs ?m2 r0 r1 |- _ => clear H2; rename H into REG end
  end.

Lemma sc_rd : forall (m m1 : fmem) (SPV lo OP OENDW LEN B0 B1 R0 R1 : Z),
  rdbl usegs m R0 R1 -> B0 <= OP -> OP + LEN <= B1 -> OENDW + 32 <= B1 -> lo <= SPV - 80 ->
  R0 + (R1 - R0) <= lo \/ SPV <= R0 ->
  munch [(OP, Z.max (OP + LEN) (OENDW + 32)); (SPV - 80, SPV)] m m1 -> stk usegs m1 B0 B1 -> rdbl usegs m1 R0 R1.
Proof.
  intros m m1 SPV lo OP OENDW LEN B0 B1 R0 R1 RDM OPB OPL OWH LOS OFFR MU ST.
  pose proof RDM as (H1 & H2 & H). pose proof ST as (_ & _ & S).
  split; [lia|]. split; [lia|]. intros a Ha.
  destruct (Z_lt_le_dec a B0) as [L|L]; [| destruct (Z_lt_le_dec a B1) as [L2|L2]].
  - destruct (H a Ha) as (b & Hb). exists b. unfold mrd in *. rewrite MU; [exact Hb|].
    rewrite wa_unsigned by lia. cbn [outside]. split; [lia| split; [lia| exact I]].
  - exact (proj2 (S a ltac:(lia))).
  - destruct (H a Ha) as (b & Hb). exists b. unfold mrd in *. rewrite MU; [exact Hb|].
    rewrite wa_unsigned by lia. cbn [outside]. split; [lia| split; [lia| exact I]].
Qed.

Section Base.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo OP OENDW IP LEN OV B0 B1 R0 R1 : Z).
  Hypothesis B0L : 4096 <= B0.
  Hypothesis B1H : B1 < 2^47.
  Hypothesis OPB : B0 <= OP.
  Hypothesis LEN0 : 0 <= LEN.
  Hypothesis OPL : OP + LEN <= B1.
  Hypothesis OW0 : 0 <= OENDW.
  Hypothesis OWH : OENDW + 32 <= B1.
  Hypothesis RDM : rdbl usegs m R0 R1.
  Hypothesis R0L : 4096 <= R0.
  Hypothesis R1H : R1 < 2^47.
  Hypothesis IPR : R0 <= IP.
  Hypothesis OVC : sc_ovc OV IP OP LEN B0 B1 R0 R1.
  Hypothesis LOS : lo <= SPV - 80.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis SPR : 0 <= SPV < 2^47.
  Hypothesis OFFB : B0 + (B1 - B0) <= lo \/ SPV <= B0.
  Hypothesis OFFR : R0 + (R1 - R0) <= lo \/ SPV <= R0.

  Notation POST := (zd_safecopy_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV OP LEN OENDW B0 B1 R0 R1 lo m).
  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -80)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation SCI m1 := (sc_inv ra s0 s1 s2 s3 s4 s5 s6 s7 s8 m SPV lo OP OENDW LEN B0 B1 m1).

  Lemma sc_ipl : IP + LEN <= R1.
  Proof. destruct OVC as [(_ & _ & E & H)|(_ & H & _)]; lia. Qed.

  Lemma sc_epi : forall m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31,
    SCI m1 -> evt usegs POST (ST 0x1e59c m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I. open_sci I.
    do 10 zstep. zstep.
    release_frame FR STK SPV.
    zstep. finish2.
    all: exact (sc_rd _ _ _ _ _ _ _ _ _ _ _ RDM OPB OPL OWH LOS OFFR MU REG).
  Qed.
End Base.
