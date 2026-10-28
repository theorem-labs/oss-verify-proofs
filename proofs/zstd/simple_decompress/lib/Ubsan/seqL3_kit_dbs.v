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

Definition PZD_SAFECOPY_DBS : Z := 0x1dd78.
Notation SAFECOPY_DBS_STACK := 80 (only parsing).

Definition zd_safecopy_dbs_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV OP LEN B0 B1 R0 R1 lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(OP, OP + LEN); (SPV - SAFECOPY_DBS_STACK, SPV)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV /\ stk usegs m' B0 B1 /\ rdbl usegs m' R0 R1.

Definition zd_safecopy_dbs_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV lo OP IP LEN B0 B1 R0 R1 : Z),
  stk usegs m B0 B1 -> 4096 <= B0 -> B1 < 2^47 -> B0 <= OP -> 0 <= LEN -> OP + LEN <= B1 ->
  rdbl usegs m R0 R1 -> 4096 <= R0 -> R1 < 2^47 -> R0 <= IP -> IP + LEN <= R1 ->
  stk usegs m lo SPV -> lo <= SPV - SAFECOPY_DBS_STACK -> 0 <= SPV < 2^47 ->
  off_stack lo SPV B0 (B1 - B0) -> off_stack lo SPV R0 (R1 - R0) ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 OP -> a1 = Z_to_bv 64 IP -> a2 = Z_to_bv 64 LEN ->
  evt usegs (zd_safecopy_dbs_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV OP LEN B0 B1 R0 R1 lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_SAFECOPY_DBS) fc None m (seg_rom usegs)).

Section Proofs.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo OP IP LEN B0 B1 R0 R1 : Z).
  Hypothesis B0L : 4096 <= B0.
  Hypothesis B1H : B1 < 2^47.
  Hypothesis OPB : B0 <= OP.
  Hypothesis LEN0 : 0 <= LEN.
  Hypothesis OPL : OP + LEN <= B1.
  Hypothesis RDM : rdbl usegs m R0 R1.
  Hypothesis R0L : 4096 <= R0.
  Hypothesis R1H : R1 < 2^47.
  Hypothesis IPR : R0 <= IP.
  Hypothesis IPL : IP + LEN <= R1.
  Hypothesis LOS : lo <= SPV - 80.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis SPR : 0 <= SPV < 2^47.
  Hypothesis OFFB : B0 + (B1 - B0) <= lo \/ SPV <= B0.
  Hypothesis OFFR : R0 + (R1 - R0) <= lo \/ SPV <= R0.

  Notation POST := (zd_safecopy_dbs_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV OP LEN B0 B1 R0 R1 lo m).
  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -80)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Definition dbs_inv (m1 : fmem) : Prop :=
    stk usegs m1 B0 B1 /\ stk usegs m1 lo (SPV + -80)
    /\ (exists j0, rw_cells usegs m1 (SPV + -80) [CB 8 j0; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ mem_inv usegs m1 /\ munch [(OP, OP + LEN); (SPV - 80, SPV)] m m1 /\ wmono usegs m m1.
  Ltac open_inv I := destruct I as (REG & STK & [j0 FR] & MI & MU & WM).
  Ltac close_inv := split; [eassumption|]; split; [eassumption|]; split; [eexists; eassumption|]; split; [eassumption|]; split; eassumption.
  Lemma dbs_signed : forall z, - 2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
  Proof.
    intros z Hz. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 64) with (2^64). change (2^64 / 2) with (2^63).
    rewrite Z.mod_small by lia. lia.
  Qed.
  Ltac dec_b H :=
    repeat (rewrite dbs_signed in H by lia);
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

  Lemma dbs_rd : forall m1, munch [(OP, OP + LEN); (SPV - 80, SPV)] m m1 -> stk usegs m1 B0 B1 -> rdbl usegs m1 R0 R1.
  Proof.
    intros m1 MU ST. pose proof RDM as (H1 & H2 & H). pose proof ST as (_ & _ & S).
    split; [lia|]. split; [lia|]. intros a Ha.
    destruct (Z_lt_le_dec a OP) as [L|L]; [| destruct (Z_lt_le_dec a (OP + LEN)) as [L2|L2]].
    - destruct (H a Ha) as (b & Hb). exists b. unfold mrd in *. rewrite MU; [exact Hb|].
      rewrite wa_unsigned by lia. cbn [outside]. split; [lia| split; [lia| exact I]].
    - exact (proj2 (S a ltac:(lia))).
    - destruct (H a Ha) as (b & Hb). exists b. unfold mrd in *. rewrite MU; [exact Hb|].
      rewrite wa_unsigned by lia. cbn [outside]. split; [lia| split; [lia| exact I]].
  Qed.

  Ltac ldR A k :=
    lazymatch goal with REG : stk usegs ?m1 B0 B1, MU : munch _ m ?m1 |- _ =>
      let a := cur_mem_addr in
      let bs := fresh "bs" in let RDb := fresh "RDb" in let L := fresh "L" bs in
      destruct (rdbl_read_at usegs m1 R0 R1 A k a (dbs_rd m1 MU REG) ltac:(lia) ltac:(lia) ltac:(addr_tac)) as [bs [L RDb]];
      zstep; try clear RDb
    end.
  Ltac str REG A k :=
    lazymatch type of REG with stk ?segs ?m1 ?b0 ?b1 =>
      let a := cur_mem_addr in
      let SOK := fresh "SOK" in
      pose proof (stk_store_ok_at segs m1 b0 b1 A k a REG ltac:(lia) ltac:(lia) ltac:(addr_tac)) as SOK;
      zstep; store_done
    end.
  Ltac mmv d sr :=
    lazymatch goal with REG : stk usegs ?m1 B0 B1, MU : munch _ m ?m1 |- _ =>
      eapply evt_cut;
      [ eapply memmove_reg_spec with (D := d) (S := sr) (n := 16) (B0 := B0) (B1 := B1) (R0 := R0) (R1 := R1);
        [ exact REG | exact (dbs_rd m1 MU REG) | lia | eassumption | try reflexivity; f_equal; lia | try reflexivity; f_equal; lia | reflexivity ]
      | post_call usegs m1 ]
    end;
    lazymatch goal with H : stk usegs ?m2 B0 B1, H2 : rdbl usegs ?m2 R0 R1 |- _ => clear H2; rename H into REG end.
  Tactic Notation "use" uconstr(L) :=
    eapply L; first [ eassumption | close_inv | idtac ]; try (f_equal; lia); try lia.

  Lemma dbs_epi : forall m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 x28 x29 x30 x31,
    dbs_inv m1 -> evt usegs POST (ST 122640 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I. open_inv I.
    do 9 zstep. zstep.
    release_frame FR STK SPV.
    zstep. finish2.
    all: exact (dbs_rd _ MU REG).
  Qed.

  Lemma dbs_lo_loop : forall (k : nat) m1 (op ip : Z) xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 x28 x29 x30 x31,
    dbs_inv m1 -> OP <= op -> ip - op = IP - OP -> op + Z.of_nat k + 1 = OP + LEN ->
    xs0 = Z_to_bv 64 ip -> xa0 = Z_to_bv 64 op -> xa1 = Z_to_bv 64 (Z.of_nat k + 1) -> xa2 = Z_to_bv 64 2 ->
    xa3 = Z_to_bv 64 op -> xa4 = Z_to_bv 64 ip ->
    evt usegs POST (ST 122596 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 x28 x29 x30 x31).
  Proof.
    induction k as [|k IH]; intros until x31; intros I HOP HIP HK -> -> -> -> -> ->; open_inv I.
    - zstep. zstep. ub K. zstep. zstep. ub K1. ldR ip 1%nat. zstep. zstep. zstep. str REG op 1%nat. zstep. zstep.
      br K2; [exfalso; lia|]. use dbs_epi.
    - zstep. zstep. ub K. zstep. zstep. ub K1. ldR ip 1%nat. zstep. zstep. zstep. str REG op 1%nat. zstep. zstep.
      br K2; [|exfalso; lia]. use (IH _ (op + 1) (ip + 1)).
  Qed.

  Lemma dbs_348 : forall m1 (op ip : Z) xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 x28 x29 x30 x31,
    dbs_inv m1 -> OP <= op < OP + LEN -> ip - op = IP - OP ->
    xa0 = Z_to_bv 64 op -> xs0 = Z_to_bv 64 ip -> xs4 = Z_to_bv 64 (OP + LEN) ->
    evt usegs POST (ST 122580 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I HOP HIP -> -> ->.
    zstep. zstep. zstep. zstep. use (dbs_lo_loop (Z.to_nat (OP + LEN - op - 1)) _ op ip).
  Qed.

  Lemma dbs_344 : forall m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 x28 x29 x30 x31,
    dbs_inv m1 -> 8 <= LEN ->
    xa0 = Z_to_bv 64 OP -> xa2 = Z_to_bv 64 LEN -> xs0 = Z_to_bv 64 IP -> xs4 = Z_to_bv 64 (OP + LEN) ->
    evt usegs POST (ST 122576 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I HL -> -> -> ->.
    zstep. br K; [exfalso; lia|]. use (dbs_348 _ OP IP).
  Qed.

  Lemma dbs_sh_loop : forall (k : nat) m1 (op ip : Z) xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 x28 x29 x30 x31,
    dbs_inv m1 -> OP <= op -> ip - op = IP - OP -> op + Z.of_nat k + 1 = OP + LEN ->
    xa0 = Z_to_bv 64 op -> xs0 = Z_to_bv 64 ip -> xa1 = Z_to_bv 64 2 -> xa2 = Z_to_bv 64 ip -> xa3 = Z_to_bv 64 op ->
    xs4 = Z_to_bv 64 (OP + LEN) ->
    evt usegs POST (ST 122532 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 x28 x29 x30 x31).
  Proof.
    induction k as [|k IH]; intros until x31; intros I HOP HIP HK -> -> -> -> -> ->; open_inv I.
    - zstep. zstep. ub K. zstep. zstep. ub K1. ldR ip 1%nat. zstep. zstep. str REG op 1%nat. zstep. zstep.
      br K2; [exfalso; lia|]. zstep. use dbs_epi.
    - zstep. zstep. ub K. zstep. zstep. ub K1. ldR ip 1%nat. zstep. zstep. str REG op 1%nat. zstep. zstep.
      br K2; [|exfalso; lia]. use (IH _ (op + 1) (ip + 1)).
  Qed.

  Lemma dbs_short : forall m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 x28 x29 x30 x31,
    dbs_inv m1 ->
    xa0 = Z_to_bv 64 OP -> xa2 = Z_to_bv 64 LEN -> xs0 = Z_to_bv 64 IP -> xs4 = Z_to_bv 64 (OP + LEN) ->
    evt usegs POST (ST 122516 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I -> -> -> ->.
    zstep. br K.
    - use dbs_epi.
    - zstep. zstep. zstep. use (dbs_sh_loop (Z.to_nat (LEN - 1)) _ OP IP).
  Qed.

  Lemma dbs_248 : forall m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 x28 x29 x30 x31,
    dbs_inv m1 -> 32 <= LEN ->
    xs0 = Z_to_bv 64 IP -> xs4 = Z_to_bv 64 (OP + LEN) -> xs5 = Z_to_bv 64 (OP + LEN - 32) -> xs6 = Z_to_bv 64 (LEN - 32) ->
    evt usegs POST (ST 122480 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I HL -> -> -> ->.
    zstep. zstep. zstep. zstep. ub K. zstep. ub K1. zstep. ub K2.
    zstep. zstep. zstep. use (dbs_348 _ (OP + LEN - 32) (IP + LEN - 32)).
  Qed.

  Lemma dbs_wl : forall (q : nat) m1 (d : Z) xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 x28 x29 x30 x31,
    dbs_inv m1 -> 32 <= LEN -> OP <= d -> d < OP + LEN - 32 -> OP + LEN - 32 - d <= 32 * (Z.of_nat q + 1) ->
    xs0 = Z_to_bv 64 IP -> xs1 = Z_to_bv 64 (d + (IP - OP) + 16) -> xs2 = Z_to_bv 64 d ->
    xs4 = Z_to_bv 64 (OP + LEN) -> xs5 = Z_to_bv 64 (OP + LEN - 32) -> xs6 = Z_to_bv 64 (LEN - 32) -> xs7 = Z_to_bv 64 (-17) ->
    evt usegs POST (ST 122412 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 x28 x29 x30 x31).
  Proof.
    induction q as [|q IH]; intros until x31; intros I HL HD HE HQ -> -> -> -> -> -> ->; open_inv I.
    - zstep. zstep. zstep. zstep. zstep. mmv d (d + (IP - OP)). zstep. ub K. zstep. ub K1.
      zstep. zstep. zstep. zstep. zstep. mmv (d + 16) (d + (IP - OP) + 16). zstep. ub K2. zstep. ub K3.
      zstep. zstep. zstep. br K4; [exfalso; lia|]. use dbs_248.
    - zstep. zstep. zstep. zstep. zstep. mmv d (d + (IP - OP)). zstep. ub K. zstep. ub K1.
      zstep. zstep. zstep. zstep. zstep. mmv (d + 16) (d + (IP - OP) + 16). zstep. ub K2. zstep. ub K3.
      zstep. zstep. zstep. br K4.
      + use (IH _ (d + 32)).
      + use dbs_248.
  Qed.

  Lemma dbs_main : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    stk usegs m B0 B1 -> stk usegs m lo SPV -> mem_inv usegs m ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OP) (Z_to_bv 64 IP) (Z_to_bv 64 LEN) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 122232) fc None m (seg_rom usegs)).
  Proof.
    intros until t6. intros REG STK MI.
    assert (MU : munch [(OP, OP + LEN); (SPV - 80, SPV)] m m) by apply munch_refl.
    assert (WM : wmono usegs m m) by apply wmono_refl.
    zstep. carve_frame 80%nat STK.
    do 9 zstep. zstep. zstep. ub K.
    zstep. zstep. zstep. zstep. zstep. ub K1.
    zstep. zstep. br K2; [use dbs_short|].
    zstep. zstep. zstep. br K3; [use dbs_short|].
    zstep. zstep. ub K4. zstep. zstep. zstep. zstep. ub K5.
    zstep. zstep. br K6; [use dbs_344|].
    zstep. br K7; [use dbs_344|].
    zstep. ub K8. zstep. zstep. zstep. zstep. zstep. mmv OP IP.
    zstep. zstep. br K9; [use dbs_248|].
    zstep. zstep. ub K10. zstep. ub K11. zstep. zstep. zstep.
    use (dbs_wl (Z.to_nat LEN) _ (OP + 16)).
  Qed.
End Proofs.

Theorem zd_safecopy_dbs_proof : zd_safecopy_dbs_stmt.
Proof.
  unfold zd_safecopy_dbs_stmt, PZD_SAFECOPY_DBS. intros until R1.
  intros REG B0L B1H OPB LEN0 OPL RDM R0L R1H IPR IPL STK LOS SPR OFFB OFFR MI -> -> ->.
  unfold off_stack in OFFB, OFFR. pose proof STK as (LO0 & _ & _).
  eapply dbs_main; eassumption.
Qed.
