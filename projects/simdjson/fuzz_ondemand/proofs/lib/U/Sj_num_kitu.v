(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjNumber SjNumU.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Definition NUMU_GTOP : Z := 0xb6000.

Definition bigu_post_g (STACK : Z) (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' ws' len',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(bv_unsigned sp - STACK, bv_unsigned sp); (X, X + 498)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ bigint_at segs m' X ws' len' /\ stk segs m' lo (bv_unsigned sp).

Definition LAFU_STACK : Z := 32.
Definition lafu_stmt_g (segs : list Segment) (entry : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (X Y ny st lo : Z) ws len (ybs : list byte),
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> (lo + LAFU_STACK <= bv_unsigned sp)%Z ->
  bigint_at segs m X ws len -> (X + 498 <= 2^64)%Z ->
  bytes_at segs m Y ybs -> Z.of_nat (length ybs) = (8 * ny)%Z -> (bv_unsigned sp <= Y)%Z -> (Y + 8 * ny <= X)%Z -> (0 < Y)%Z -> (Y mod 8 = 0)%Z ->
  (0 <= ny <= 62)%Z -> (0 <= st <= 62)%Z ->
  evt segs (bigu_post_g LAFU_STACK segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 ny) (Z_to_bv 64 st) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Definition LMU_STACK : Z := 1120 + LAFU_STACK.
Definition lmu_stmt_g (segs : list Segment) (entry : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (X Y ny lo : Z) ws len (ybs : list byte),
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> (lo + LMU_STACK <= bv_unsigned sp)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
  bigint_at segs m X ws len -> (bv_unsigned sp <= X)%Z -> (X + 498 <= 2^64)%Z ->
  bytes_at segs m Y ybs -> Z.of_nat (length ybs) = (8 * ny)%Z -> (Y + 8 * ny <= lo)%Z -> (0 < Y)%Z -> (Y mod 8 = 0)%Z -> (0 <= ny <= 62)%Z ->
  evt segs (bigu_post_g LMU_STACK segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 ny) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Definition P5U_STACK : Z := 48 + LMU_STACK.
Definition p5u_stmt_g (segs : list Segment) (entry gtop : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (X e lo : Z) ws len,
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> (lo + P5U_STACK <= bv_unsigned sp)%Z -> (gtop <= lo)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
  bigint_at segs m X ws len -> (bv_unsigned sp <= X)%Z -> (X + 498 <= 2^64)%Z ->
  (-2147483648 <= e < 2147483648)%Z ->
  evt segs (bigu_post_g P5U_STACK segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Definition SHLU_STACK : Z := 48.
Definition shlu_stmt_g (segs : list Segment) (entry : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (X lo : Z) ws len,
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> (lo + SHLU_STACK <= bv_unsigned sp)%Z ->
  bigint_at segs m X ws len -> (bv_unsigned sp <= X)%Z -> (X + 498 <= 2^64)%Z -> (0 < X)%Z ->
  evt segs (bigu_post_g SHLU_STACK segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Ltac nnorm_p :=
  cbv beta;
  repeat match goal with
  | |- context [Z.shiftl ?x 3] => rewrite (shl3 x)
  | |- context [Z.shiftl ?x 1] => rewrite (shl1 x)
  | |- context [Z.shiftl ?x 2] => rewrite (shl2 x)
  | |- context [Z.shiftl ?x 4] => rewrite (shl4 x)
  | |- context [bv_swrap 32 ?t] =>
      num_simple_expr t;
      let t' := num_strip_mods t in
      replace (bv_swrap 32 t) with t' by (rewrite bv_swrap32; unfold swrap32; Z.div_mod_to_equations; lia)
  | |- context [zx16 (Z_to_bv 64 ?x)] => rewrite (zx16_small x) by lia
  | |- context [sx16 (Z_to_bv 64 ?x)] => rewrite (sx16_small x) by lia
  | |- context [Z.modulo ?x 65536] => rewrite (Z.mod_small x 65536) by lia
  | |- context [Z.modulo ?x 18446744073709551616] => num_simple_expr x; rewrite (Z.mod_small x 18446744073709551616) by lia
  | |- context [Z_to_bv 64 ?t] =>
      lazymatch t with context [Z.modulo ?x 18446744073709551616] => num_simple_expr x end;
      let t' := num_strip_mods t in
      lazymatch t' with context [Z.modulo _ 18446744073709551616] => fail | _ => idtac end;
      replace (Z_to_bv 64 t) with (Z_to_bv 64 t') by (apply Z_to_bv_eqm; Z.div_mod_to_equations; lia)
  | |- context [Z.shiftr (Z.shiftl ?k 48 mod 18446744073709551616) 48] => rewrite (shl48_shr48 k) by lia
  | |- context [Z.shiftr (Z.shiftl ?k 48 mod 18446744073709551616) 45] => rewrite (shl48_shr45 k) by lia
  | |- context [Z.shiftr (Z.shiftl ?k 51 mod 18446744073709551616) 48] => rewrite (shl51_shr48 k) by lia
  end.

Ltac unorm :=
  repeat match goal with
  | |- context [Z.shiftr ?x 60] => rewrite (shr60_small x) by lia
  | |- context [Z.shiftr ?x 3] => rewrite (Z.shiftr_div_pow2 x 3) by lia; change (2 ^ 3)%Z with 8%Z
  | |- context [Z.shiftr ?x 6] => rewrite (Z.shiftr_div_pow2 x 6) by lia; change (2 ^ 6)%Z with 64%Z
  | |- context [Z.lxor ?x 18446744073709551615] => rewrite (lxor_ones64 x) by lia
  | |- context [Z.land ?y 7] =>
      rewrite (land_7 y);
      try match goal with H : (y mod 8 = 0)%Z |- _ => rewrite H end
  | |- context [Z.land ((0 - Z.b2z (?a <? ?k)) mod 18446744073709551616) ?t] =>
      first [ replace (a <? k)%Z with true by (symmetry; apply Z.ltb_lt; lia);
              change ((0 - Z.b2z true) mod 18446744073709551616)%Z with 18446744073709551615%Z;
              rewrite (land_ones64_l t) by first [apply Z.mod_pos_bound; lia | lia]
            | replace (a <? k)%Z with false by (symmetry; apply Z.ltb_ge; lia);
              change ((0 - Z.b2z false) mod 18446744073709551616)%Z with 0%Z; rewrite (Z.land_0_l t) ]
  | |- context [Z.land ((Z.b2z (?a <? ?k) + -1) mod 18446744073709551616) ?t] =>
      first [ replace (a <? k)%Z with false by (symmetry; apply Z.ltb_ge; lia);
              change ((Z.b2z false + -1) mod 18446744073709551616)%Z with 18446744073709551615%Z;
              rewrite (land_ones64_l t) by first [apply Z.mod_pos_bound; lia | lia]
            | replace (a <? k)%Z with true by (symmetry; apply Z.ltb_lt; lia);
              change ((Z.b2z true + -1) mod 18446744073709551616)%Z with 0%Z; rewrite (Z.land_0_l t) ]
  end.
Ltac nnorm_u := nnorm_p; unorm; nnorm_p.

Ltac u_trap pc := first [ exfalso; lia | fail 100 "TRAP reachable" pc ].

Ltac unorm_in H :=
  repeat match type of H with
  | context [Z.shiftl ?k 48 mod 18446744073709551616] => rewrite (shl48_small k) in H by lia
  | context [Z.land ?x 255] => rewrite (Z.land_ones x 8 ltac:(lia) : Z.land x 255 = x mod 2 ^ 8)%Z in H
  end.
Ltac uwalk_fuel n K :=
  lazymatch n with
  | O => lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail 100 "uwalk: out of fuel at" pc end
  | S ?n' =>
      lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => first [ K pc | (nstep; uwalk_fuel n' K) ]
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
          let H := fresh "KB" in
          if_cases H; zify_cond H; num_signed_lits_in H; unorm_in H;
          tryif num_is_data H then (clear H; uwalk_fuel n' K) else first [ solve [exfalso; lia] | uwalk_fuel n' K ]
      end
  end.
Ltac uwalk K := uwalk_fuel 400%nat K.

Ltac num_call_memcpy HC UA az bz SRCz srcb SB :=
  lazymatch type of UA with
  | u8arr ?segs ?m ?Ub ?bsb =>
      let b1 := fresh "b" in let mid := fresh "mid" in let b3 := fresh "b" in
      let L1 := fresh "L1" in let LM := fresh "LM" in let L3 := fresh "L3" in
      let U1 := fresh "U1" in let MID := fresh "MID" in let U3 := fresh "U3" in
      destruct (u8arr_range_split segs m Ub bsb (Z.to_nat az) (Z.to_nat bz) UA ltac:(lia) ltac:(lia))
        as (b1 & mid & b3 & L1 & LM & L3 & U1 & MID & U3);
      clear UA;
      replace (Ub + Z.of_nat (Z.to_nat az))%Z with (Ub + az)%Z in MID by lia;
      replace (Z.to_nat bz - Z.to_nat az)%nat with (Z.to_nat (bz - az)) in MID by lia;
      let HC' := fresh "HC" in pose proof HC as HC'; hnf in HC';
      eapply evt_cut;
      [ eapply evt_eq;
        [| eapply HC' with (Dst := (Ub + az)%Z) (Src := SRCz) (N := (bz - az)%Z) (src := srcb) (junk := mid);
           [ exact SB | first [lia | rewrite length_firstn; lia] | exact MID | lia | lia | lia | lia
           | lazymatch goal with MI : mem_inv segs m |- _ => exact MI end ] ];
        num_st_eq
      | cbv beta;
        let ms' := fresh "ms'" in let P := fresh "P" in
        intros ms' P; unfold memcpyZ_post_g in P;
        let m3 := fresh "m" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
        let DSTc := fresh "DSTc" in let SRCc := fresh "SRCc" in
        destruct P as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & -> & MUc & WMc & MIc & DSTc & SRCc);
        transport_after_call segs m m3 MUc WMc;
        clear MUc WMc HC' SRCc;
        repeat match goal with MI : mem_inv segs m |- _ => clear MI end;
        num_ret_pc;
        replace (Ub + az)%Z with (Ub + Z.of_nat (length b1))%Z in DSTc by lia;
        replace (Ub + Z.of_nat (Z.to_nat bz))%Z with (Ub + Z.of_nat (length b1) + Z.of_nat (Z.to_nat (bz - az)))%Z in U3 by lia;
        let bs' := fresh "bs" in let LJ := fresh "LJ" in let LB := fresh "LB" in
        destruct (u8arr_range_join segs m3 Ub b1 _ _ b3 U1 DSTc U3) as (bs' & LJ & UA);
        assert (LB : length bs' = length bsb) by lia;
        clear U1 U3 DSTc LJ ]
  end.

Definition NDCU_STACK : Z := 576 + P5U_STACK.
Definition PDCU_STACK : Z := 32 + P5U_STACK.
Definition PMU_STACK : Z := 128.
Definition SPATHU_STACK : Z := 704 + NDCU_STACK.
Definition FFU_STACK : Z := 112 + SPATHU_STACK.

Definition ffu_post_g (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom segs)
    /\ frm0 fc'
    /\ munch [(bv_unsigned sp - FFU_STACK, bv_unsigned sp)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ stk segs m' lo (bv_unsigned sp).
Definition ffu_stmt_g (segs : list Segment) (entry gtop : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (A FIRST LAST lo : Z) (txt : list byte),
  mem_inv segs m -> frm0 fc ->
  stk segs m lo (bv_unsigned sp) -> (lo + FFU_STACK <= bv_unsigned sp)%Z -> (gtop <= lo)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
  bytes_at segs m A txt -> (A + Z.of_nat (length txt) <= lo)%Z -> (Z.of_nat (length txt) < NUM_TXT_MAX)%Z -> (0 < A)%Z ->
  (A <= FIRST <= LAST)%Z -> (LAST <= A + Z.of_nat (length txt))%Z ->
  evt segs (ffu_post_g segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom segs)).
