(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast SFModel.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel Target Prog PjImpl.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjAlloc SjTape SjTapeList SjTapeTile SjPjSer SjPjDig SjPjItoa.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit F_memcpy F_memmove_t2.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Pj_defs Pj_kit Pj_grow Pj_ser_defs Pj_ser_kit Pj_ser_calls Pj_num_defs Pj_ser_ncalls.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_store ::= first [ pj_solve_store0 | pj_store_wr ].
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Section Arm.
  Variables (E : senv) (Q : @chst bptr -> PState -> machine_state -> Prop) (esc : word) (isobj : list byte)
            (F : bvmap 5 word) (fc : bv 32) (i dp A : Z) (xs8 : word)
            (buf size cap : Z) (blk : option bptr) (fuel : nat) (s : PState).
  Hypothesis OK : senv_ok E.
  Hypothesis FRM : frm0 fc.
  Hypothesis I1 : 1 <= i.
  Hypothesis I2 : i + 1 < e_n E.
  Hypothesis ACC : size <= A.
  Hypothesis BUD : A + 20 <= PJ_OUTMAX (e_len E).
  Hypothesis HK : av_K E Q esc isobj 0x3e5e0 (i + 1) dp (A + 20).
  Notation st0 := (mkSb buf size cap blk fuel).

  Lemma i64_after : forall (k sg : Z) (spill : word) (m : mem) (xs5 xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xt3 xt4 xt5 xt6 : word),
    SERM E esc spill isobj st0 s m -> 0 <= sg <= 1 -> 0 <= k -> k + 1 + sg <= 20 ->
    evt psegs (sgoal E Q (sb_ch st0) s)
        (LST E 0x3e56c (i + 1) dp xs5 xra xt0 xt1 xt2 xa0 (Z_to_bv 64 (e_q E + -105 - k)) xa2 xa3 xa4 xa5 xa6 xa7
             (Z_to_bv 64 (e_q E + -164 + sg)) xs4 xs8 xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK FRM I1 I2 ACC BUD HK.
    intros k sg spill m xs5 xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xt3 xt4 xt5 xt6 HSM HSG K0 HKS.
    ser_env OK.
    set (n := k + 1).
    set (tot := sg + n).

    assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (spill5 : word) (yra zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 : word),
      SERM E esc spill5 isobj st5 s5 m5 -> sb_size st5 = size -> size + tot <= sb_cap st5 ->
      evt psegs (sgoal E Q (sb_ch st5) s5)
          (LST E 0x3e5bc (i + 1) dp (Z_to_bv 64 (e_q E + -164 + tot)) yra zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 (Z_to_bv 64 tot) (Z_to_bv 64 (tot + size)) xs8 zt3 zt4 zt5 zt6 F fc m5)).
    { intros st5 s5 m5 spill5 yra zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 HSM5 ESZ ROOM.
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap] in ESZ, ROOM. subst size5.
      ser_open HSM5 OK.

      zstep. step.
      if_cases K; zify_cond K.
      { exfalso. rewrite ?unsigned_lit in K by (unfold tot, n; lia). unfold tot, n in K. lia. }

      step. step. zstep. zstep. step. step.
      ser_close HSM6 OK.
      eapply (ser_copy E Q esc spill5 isobj (mkSb buf5 size cap5 blk5 fuel5) s5) with (fpc := MEMMOVE_T2) (Src := e_q E + -164) (n := tot) (rpc := 0x3e5dc);
        [right; reflexivity | exact OK | exact HSM6 | | unfold tot, n; lia | cbn [sb_size sb_cap]; lia | lia | lia | cbn [sb_buf sb_size]; unfold tot, n; lia | lia | reflexivity | ].
      { eapply (frt_src E esc spill5 isobj _ s5 m5); [exact HSM6 | lia | unfold tot, n; lia | unfold tot, n; lia]. }
      intros m7 wt0 wt1 wt2 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6 HSM7.
      ser_open HSM7 OK.

      step.
      ser_close HSM8 OK.
      eapply (HK (mkSb buf5 (tot + size) cap5 blk5 fuel5)); [exact HSM8| exact FRM| cbn [sb_size]; unfold tot, n; lia| left; reflexivity]. }
    ser_open HSM OK.

    zstep.
    step. pj_store_done.

    zstep. zstep. step. step. step.
    ser_close HSM1 OK.
    eapply evt_eq; [| eapply (ser_frt_memcpy E Q esc spill isobj st0 s) with (Dst := e_q E + -164 + sg) (Src := e_q E + -105 - k) (n := n) (rpc := 0x3e588);
                      [exact OK | exact HSM1 | lia | unfold n; lia | lia | unfold n; lia | unfold n; lia | unfold n; lia | lia | reflexivity | ]].
    { unfold n. nst_eq. }
    intros m2 yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM2.
    ser_open HSM2 OK.

    step. step. zstep. zstep. zstep. zstep. step.
    if_cases K; zify_cond K.
    - rewrite ?unsigned_lit in K by (unfold tot, n; lia).
      ser_close HSM3 OK.
      eapply evt_eq; [| eapply (TAIL st0); [exact HSM3| reflexivity| cbn [sb_cap]; unfold tot, n; lia]].
      unfold tot, n. nst_eq.
    - rewrite ?unsigned_lit in K by (unfold tot, n; lia).

      zstep. pjnorm. step. step.
      assert (GROWN : forall (z : Z) (ya0 : word), z = Z.max (2 * cap) (tot + size) ->
        evt psegs (sgoal E Q (sb_ch st0) s)
          (LST E 0x3e5b4 (i + 1) dp (Z_to_bv 64 (e_q E + -164 + tot)) (Z_to_bv 64 0x3e588) yt0 yt1 yt2 ya0 (Z_to_bv 64 z) (Z_to_bv 64 (e_q E + -164)) ya3 ya4 ya5 ya6 ya7
               (Z_to_bv 64 tot) (Z_to_bv 64 (tot + size)) xs8 yt3 yt4 yt5 yt6 F fc m2)).
      { intros z ya0 EZ.

        step. step.
        ser_close HSM3 OK.
        eapply (ser_grow HM HF) with (z := z) (rpc := 0x3e5bc); [exact OK| exact HSM3| | lia| reflexivity|].
        { rewrite EZ. eapply (ser_req_ok E _ _ _ _ _ _ (tot + size) OK HSM3); cbn [sb_cap]; unfold tot, n; lia. }
        intros s' m' b NEW zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 HSM4.
        eapply TAIL; [exact HSM4| reflexivity|].
        unfold sb_grown. cbn [sb_cap]. rewrite EZ. lia. }
      if_cases K2; zify_cond K2.
      + pjnorm_in K2. eapply evt_eq; [| eapply (GROWN (tot + size)); unfold tot, n; lia]. unfold tot, n. nst_eq.
      + pjnorm_in K2.   step. eapply evt_eq; [| eapply (GROWN (2 * cap)); unfold tot, n in *; lia]. unfold tot, n. nst_eq.
  Qed.

  Lemma i64_loop : forall (f : nat) (k sg w : Z) (spill : word) (m : mem) (xs5 xra xt0 xt1 xt2 xa1 xa4 xa5 xs4 xt3 xt4 xt5 xt6 : word),
    SERM E esc spill isobj st0 s m -> 0 <= sg <= 1 -> 10 <= w < 10 ^ (20 - sg - k) -> w < 18446744073709551616 -> 0 <= k ->
    20 - sg - k <= Z.of_nat f ->
    evt psegs (sgoal E Q (sb_ch st0) s)
        (LST E 0x3e22c (i + 1) dp xs5 xra xt0 xt1 xt2 (Z_to_bv 64 PJ_DIV10_BASE) xa1 (Z_to_bv 64 w) (Z_to_bv 64 (e_q E + -105 - k)) xa4 xa5
             (Z_to_bv 64 10) (Z_to_bv 64 99) (Z_to_bv 64 (e_q E + -164 + sg)) xs4 xs8 xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK FRM I1 I2 ACC BUD HK.
    induction f as [|f IH]; intros k sg w spill m xs5 xra xt0 xt1 xt2 xa1 xa4 xa5 xs4 xt3 xt4 xt5 xt6 HSM HSG HW W64 K0 HFU.
    { exfalso. pose proof (pow10_ge2 w (20 - sg - k) HW). lia. }
    pose proof (pow10_ge2 w (20 - sg - k) HW) as J2.
    pose proof (pow10_step w (20 - sg - k) ltac:(lia) ltac:(lia)) as HQ.
    ser_env OK.
    ser_open HSM OK.

    unfold PJ_DIV10_BASE.
    step. step. zstep. zstep.
    rewrite SFModel.land_W64. change (2 ^ 64) with 18446744073709551616.
    change 14757395258967641293 with DIV10_MAGIC. rewrite (div10_machine w) by lia.

    zstep. zstep. zstep. zstep.
    step. pj_store_done.
    step. step.
    if_cases K; zify_cond K.
    -
      rewrite ?unsigned_lit in K by lia.
      ser_close HSM2 OK.
      eapply evt_eq; [| eapply (IH (k + 1) sg (w / 10)); [exact HSM2 | exact HSG | | | lia | lia]].
      + nst_eq.
      + replace (20 - sg - (k + 1)) with (20 - sg - k - 1) by lia. split; [apply (div10_ge10 w); lia | lia].
      + Z.div_mod_to_equations. lia.
    - rewrite ?unsigned_lit in K by lia.

      step.
      ser_close HSM2 OK.
      eapply evt_eq; [| eapply (i64_after (k + 1) sg); [exact HSM2 | exact HSG | lia | lia]].
      nst_eq.
  Qed.

  Lemma i64_mag : forall (sg w : Z) (spill : word) (m : mem) (xs5 xra xt0 xt1 xt2 xa1 xa3 xa4 xa5 xa6 xa7 xs4 xt3 xt4 xt5 xt6 : word),
    SERM E esc spill isobj st0 s m -> 0 <= sg <= 1 -> 0 <= w < 10 ^ (20 - sg) -> w < 18446744073709551616 ->
    evt psegs (sgoal E Q (sb_ch st0) s)
        (LST E 0x3e21c (i + 1) dp xs5 xra xt0 xt1 xt2 (Z_to_bv 64 PJ_DIV10_BASE) xa1 (Z_to_bv 64 w) xa3 xa4 xa5 xa6 xa7
             (Z_to_bv 64 (e_q E + -164 + sg)) xs4 xs8 xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK FRM I1 I2 ACC BUD HK.
    intros sg w spill m xs5 xra xt0 xt1 xt2 xa1 xa3 xa4 xa5 xa6 xa7 xs4 xt3 xt4 xt5 xt6 HSM HSG HW W64.
    ser_env OK.
    pose proof HSM as HSM0.
    ser_open HSM OK.

    step. step. step.
    if_cases K; zify_cond K.
    - rewrite ?unsigned_lit in K by lia.

      zstep.
      eapply evt_eq; [| eapply (i64_after 0 sg); [exact HSM0 | exact HSG | lia | lia]].
      nst_eq.
    - rewrite ?unsigned_lit in K by lia.

      zstep.
      eapply evt_eq; [| eapply (i64_loop (Z.to_nat (20 - sg)) 0 sg w); [exact HSM0 | exact HSG | | lia | lia | lia]].
      + nst_eq.
      + replace (20 - sg - 0) with (20 - sg) by lia. lia.
  Qed.

  Lemma i64_arm : forall (spill : word) (m : mem) (xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xt3 xt4 xt5 xt6 : word),
    SERM E esc spill isobj st0 s m ->
    evt psegs (sgoal E Q (sb_ch st0) s)
        (LST E 0x3e1f4 i dp (Z_to_bv 64 125) xra xt0 xt1 xt2 (Z_to_bv 64 PJ_DIV10_BASE) (Z_to_bv 64 (e_TAPE E)) xa2 xa3 xa4 xa5 xa6 xa7
             xs3 xs4 xs8 xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK FRM I1 I2 ACC BUD HK.
    intros spill m xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xt3 xt4 xt5 xt6 HSM.
    ser_env OK.
    pose proof (ser_ranges _ _ _ _ _ _ _ OK HSM) as (TP0 & TP1 & _ & _).
    pose proof HSM as HSM0.
    ser_open HSM OK.

    zstep. zstep. pjnorm. zstep.
    pose proof (tape_read_mu E _ _ _ _ (i + 1) OK HREF MU WM ltac:(lia)) as RD.
    step. clear RD.
    set (wd := Z_to_bv 64 (e_T E (i + 1))).
    pose proof (bv_unsigned_in_range 64 wd) as WR. unfold bv_modulus in WR. cbn in WR.
    rewrite <- (Z_to_bv_bv_unsigned wd). set (w := bv_unsigned wd) in *. clearbody w. clear wd.

    zstep. step.
    if_cases K; zify_cond K.
    -
      eapply evt_eq; [| eapply (i64_mag 0 w); [exact HSM0 | lia | | lia]].
      + nst_eq.
      + replace (20 - 0) with 20 by lia. apply u64_lt_pow10_20. lia.
    -

      step.
      step. pj_store_done.
      zstep. zstep.
      ser_close HSM2 OK.
      replace (Z_to_bv 64 (0 + - w)) with (Z_to_bv 64 (18446744073709551616 - w))
        by (apply Z_to_bv_eqm; change (2 ^ 64) with 18446744073709551616; Z.div_mod_to_equations; lia).
      eapply evt_eq; [| eapply (i64_mag 1 (18446744073709551616 - w)); [exact HSM2 | lia | | lia]].
      + nst_eq.
      + change (10 ^ (20 - 1)) with 10000000000000000000. lia.
  Qed.
  End Arm.

  Theorem i64_proof : i64_stmt.
  Proof.
    unfold i64_stmt.
    intros E Q esc spill isobj st s m F fc i dp A xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs8 xt3 xt4 xt5 xt6 OK HSM FRM I1 I2 ACC BUD HK.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in ACC.
    eapply i64_arm; eassumption.
  Qed.

End Proofs.
End WithCeiling0.
