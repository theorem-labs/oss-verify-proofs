(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Tac Arr SFModel.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit Str_cpy Fz_W4_defs Fz_W4_block.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation z64 := (Z_to_bv 64 0) (only parsing).

Definition dupdate_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (C B OL : Z) (N : nat) (inl num : Z) (ln : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (rv ret num' : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 (ed' bs' : list byte) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 128, bv_unsigned sp); (C, C + 84); (B, B + Z.of_nat N); (OL, OL + 4)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ (-1 <= rv <= 1 /\ 0 <= ret /\ 0 <= num' <= 64 /\ 4 * ret + 3 * num' <= 3 * (inl + num))
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' C (ectx_cells (Z_to_bv 64 num') ed' ln z64) /\ length ed' = 80%nat
    /\ rw_cells psegs m' B [CB N bs']
    /\ rw_cells psegs m' OL [C4 (Z_to_bv 64 ret)].

Section Proofs.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (C B OL : Z) (N : nat) (inl num : Z) (ln old : word) (lo : Z).
  Notation SP := (bv_unsigned sp).
  Notation W := [(bv_unsigned sp - 128, bv_unsigned sp); (C, C + 84); (B, B + Z.of_nat N); (OL, OL + 4)]%Z.
  Hypothesis AB : 0 <= num <= 64 /\ 0 <= inl <= Z.of_nat N /\ inl < 2 ^ 31 /\ 3 * (inl + num) <= 4 * Z.of_nat N
                  /\ 0 < C /\ C + 92 <= 2 ^ 64 /\ 0 < B /\ B + Z.of_nat N <= 2 ^ 64 /\ 0 < OL /\ OL + 4 <= 2 ^ 64
                  /\ 0 <= lo /\ lo <= SP - 128 /\ SP < 2 ^ 64.
  Hypothesis SEP_CB : C + 92 <= B \/ B + Z.of_nat N <= C.
  Hypothesis SEP_CO : C + 92 <= OL \/ OL + 4 <= C.
  Hypothesis SEP_BO : B + Z.of_nat N <= OL \/ OL + 4 <= B.
  Hypothesis SEP_CS : C + 92 <= lo \/ SP <= C.
  Hypothesis SEP_BS : B + Z.of_nat N <= lo \/ SP <= B.
  Hypothesis SEP_OS : OL + 4 <= lo \/ SP <= OL.

  Notation POST := (dupdate_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 F fc C B OL N inl num ln lo m).
  (* [comment removed for export] *)
  Notation ST pc mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -112)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition INV (slot : word) (mX : mem) : Prop :=
    exists (ed' bs : list byte),
      rw_cells psegs mX C [C4 (Z_to_bv 64 num)] /\ u8arr psegs mX (C + 4) ed' /\ length ed' = 80%nat
      /\ rw_cells psegs mX (C + 84) [C4 ln; C4 z64]
      /\ u8arr psegs mX B bs /\ length bs = N
      /\ rw_cells psegs mX OL [C4 old]
      /\ rw_cells psegs mX (SP + -112) [C8 slot; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ stk psegs mX lo (SP + -112)
      /\ mem_inv psegs mX /\ munch W m mX /\ wmono psegs m mX.

  Ltac open_inv I := destruct I as (ed' & bs & CN & ED & LED & CT & BLK & LBS & OLC & FR & ST & MI & MU & WM).
  Ltac close_inv := do 2 eexists; do 11 (split; [eassumption|]); eassumption.

  (* [comment removed for export] *)
  Lemma ectx_join : forall mX nw ed', length ed' = 80%nat ->
    rw_cells psegs mX C [C4 nw] -> u8arr psegs mX (C + 4) ed' -> rw_cells psegs mX (C + 84) [C4 ln; C4 z64] ->
    rw_cells psegs mX C (ectx_cells nw ed' ln z64).
  Proof.
    intros mX nw ed' L CN ED CT. apply rw_cells_of_u8arr in ED. rewrite L in ED. unfold ectx_cells.
    change [C4 nw; CB 80 ed'; C4 ln; C4 z64] with ([C4 nw] ++ [CB 80 ed'] ++ [C4 ln; C4 z64]).
    apply (proj2 (rw_cells_app psegs mX C _ _)). split; [exact CN|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app psegs mX (C + Z.of_nat 4) _ _)). split; [exact ED|]. cbn [cells_size csize Nat.add].
    replace (C + Z.of_nat 4 + Z.of_nat 80) with (C + 84) by lia. exact CT.
  Qed.

  (* [comment removed for export] *)
  Lemma U_end : forall slot mX rv ret n x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x19 x20 x21 x22 x23 x26 x27 x28 x29 x30,
    INV slot mX -> -1 <= rv <= 1 -> 0 <= ret -> 0 <= n <= 64 -> 4 * ret + 3 * n <= 3 * (inl + num) ->
    evt psegs POST (ST 0x1749fc mX x1 x5 x6 x7 (Z_to_bv 64 OL) x10 x11 x12 (Z_to_bv 64 n) x14 x15 x16 x17 (Z_to_bv 64 C) x19 x20 x21 x22 x23
                       (Z_to_bv 64 rv) (Z_to_bv 64 ret) x26 x27 x28 x29 x30).
  Proof.
    intros slot mX rv ret n x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x19 x20 x21 x22 x23 x26 x27 x28 x29 x30 I Hrv Hret Hn HI.
    open_inv I.
    do 3 ths.
    do 13 ths. do 2 ths.
    release_frame FR ST (bv_unsigned sp).
    pose proof (ectx_join _ _ _ LED CN ED CT) as CTX.
    apply rw_cells_of_u8arr in BLK. rewrite LBS in BLK.
    apply evt_done. exists rv, ret, n. do 13 eexists. exists ed', bs. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [lia|]. split; [exact ST|].
    split; [exact CTX|]. split; [exact LED|]. split; [exact BLK | exact OLC].
  Qed.
  Notation OLW := (Z_to_bv 64 OL).

  (* [comment removed for export] *)
  Lemma U_end_r : forall mX rv ret n x1 x5 x6 x7 x9 x10 x11 x12 x14 x15 x16 x17 x19 x20 x21 x22 x23 x26 x27 x28 x29 x30,
    INV OLW mX -> -1 <= rv <= 1 -> 0 <= ret -> 0 <= n <= 64 -> 4 * ret + 3 * n <= 3 * (inl + num) ->
    evt psegs POST (ST 0x1749f8 mX x1 x5 x6 x7 x9 x10 x11 x12 (Z_to_bv 64 n) x14 x15 x16 x17 (Z_to_bv 64 C) x19 x20 x21 x22 x23
                       (Z_to_bv 64 rv) (Z_to_bv 64 ret) x26 x27 x28 x29 x30).
  Proof.
    intros mX rv ret n x1 x5 x6 x7 x9 x10 x11 x12 x14 x15 x16 x17 x19 x20 x21 x22 x23 x26 x27 x28 x29 x30 I Hrv Hret Hn HI.
    pose proof I as I'. open_inv I'.
    ths.
    eapply (U_end OLW _ rv ret n); first [exact I | lia].
  Qed.

  Lemma U_end_r0 : forall mX rv ret x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x26 x27 x28 x29 x30,
    INV OLW mX -> -1 <= rv <= 1 -> 0 <= ret -> 4 * ret <= 3 * (inl + num) ->
    evt psegs POST (ST 0x1749f4 mX x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 C) x19 x20 x21 x22 x23
                       (Z_to_bv 64 rv) (Z_to_bv 64 ret) x26 x27 x28 x29 x30).
  Proof.
    intros mX rv ret x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x26 x27 x28 x29 x30 I Hrv Hret HI.
    zstep. eapply (U_end_r _ rv ret 0); first [exact I | lia].
  Qed.
  (* [comment removed for export] *)
  Lemma U_rv : forall mX ret n eof f10 x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x20 x21 x22 x23 x24 x27 x28 x29 x30,
    INV OLW mX -> 0 <= ret -> 0 <= n <= 64 -> 4 * ret + 3 * n <= 3 * (inl + num) -> 0 <= f10 <= 1 ->
    evt psegs POST (ST 0x1749b4 mX x1 x5 x6 x7 OLW x10 x11 x12 (Z_to_bv 64 n) x14 x15 x16 x17 (Z_to_bv 64 C) (Z_to_bv 64 eof) x20 x21 x22 x23
                       x24 (Z_to_bv 64 ret) (Z_to_bv 64 f10) x27 x28 x29 x30).
  Proof.
    intros mX ret n eof f10 x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x20 x21 x22 x23 x24 x27 x28 x29 x30 I Hret Hn HI Hf.
    do 5 zstep.
    eapply (U_end OLW mX _ ret n); [exact I | | lia | lia | lia].
    assert (Hf' : f10 = 0 \/ f10 = 1) by lia.
    destruct Hf' as [-> | ->]; destruct (Z.land eof 18446744073709551615 <? 1); destruct (0 <? n); split; apply Z.leb_le; reflexivity.
  Qed.
  (* [comment removed for export] *)
  Ltac call_dblock CN ED LED CT BLK LBS ret n eof :=
    let CTXR := fresh "CTXR" in
    pose proof (proj1 (ectx_join _ _ _ LED CN ED CT) : ro_cells psegs _ C (ectx_cells (Z_to_bv 64 num) _ ln z64)) as CTXR;
    let BA := fresh "BA" in let BB := fresh "BB" in
    apply rw_cells_of_u8arr in BLK; rewrite LBS in BLK;
    destruct (rw_cells_CB_split_at psegs _ B N _ (Z.to_nat ret) ltac:(lia) BLK) as [BA BB]; clear BLK;
    rewrite Z2Nat.id in BB by lia;
    tcall (dblock_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C (B + ret) (N - Z.to_nat ret)%nat n eof (Z_to_bv 64 num) ln _ _ lo);
    [ first [reflexivity | eassumption | lia] .. | ].

  (* [comment removed for export] *)
  Ltac rejoin_block BA POST ret :=
    replace (B + ret) with (B + Z.of_nat (Z.to_nat ret)) in POST by lia;
    let BLK' := fresh "BLK" in let LB' := fresh "LBS" in
    pose proof (rw_cells_CB_join psegs _ B _ _ _ _ BA POST) as BLK';
    replace (Z.to_nat ret + (N - Z.to_nat ret))%nat with N in BLK' by lia;
    pose proof (rw_cells_CB_length psegs _ _ _ _ BLK') as LB';
    apply u8arr_of_rw_cells in BLK'; clear BA POST.

  (* [comment removed for export] *)
  Lemma U_tail : forall mX ret n eof f10 x1 x5 x6 x7 x9 x10 x11 x12 x14 x15 x16 x17 x22 x23 x24 x27 x28 x29 x30,
    INV OLW mX -> 0 <= ret -> 0 <= n <= 64 -> 4 * ret + 3 * n <= 3 * (inl + num) -> 0 <= eof <= 2 -> 0 <= f10 <= 1 ->
    evt psegs POST (ST 0x174994 mX x1 x5 x6 x7 x9 x10 x11 x12 (Z_to_bv 64 n) x14 x15 x16 x17 (Z_to_bv 64 C) (Z_to_bv 64 eof) (Z_to_bv 64 (B + ret))
                       (Z_to_bv 64 (C + 4)) x22 x23 x24 (Z_to_bv 64 ret) (Z_to_bv 64 f10) x27 x28 x29 x30).
  Proof.
    intros mX ret n eof f10 x1 x5 x6 x7 x9 x10 x11 x12 x14 x15 x16 x17 x22 x23 x24 x27 x28 x29 x30 I Hret Hn HI He Hf.
    pose proof (Z.mul_div_le n 4 ltac:(lia)) as HD. pose proof (Z.div_pos n 4 ltac:(lia) ltac:(lia)) as HD0.
    zstep. if_cases K0; zify_cond K0; signed_lits_in K0.
    - (* [comment removed for export] *)
      pose proof I as I'. open_inv I'. ths.
      eapply (U_rv _ ret n eof f10); first [exact I | lia].
    - pose proof I as I'. open_inv I'.
      do 3 ths. if_cases K3; zify_cond K3.
      + (* [comment removed for export] *)
        do 5 ths.
        call_dblock CN ED LED CT BLK LBS ret n eof.
        rejoin_block BA POST ret. clear PC1.
        lazymatch goal with MIh : mem_inv psegs ?mm |- _ => assert (I2 : INV OLW mm) by close_inv end.
        clear CN ED CT OLC FR PC0 MI0 MU WM.
        cbv beta delta [mkR].
        destruct PC as [-> | PC].
        * do 2 zstep. th_if_lit. do 2 zstep.
          eapply (U_end OLW _ (-1) ret 0); first [exact I2 | lia].
        * do 2 zstep. if_cases KD; zify_cond KD; signed_lits_in KD. { exfalso. lia. }
          zstep. if_cases KE; zify_cond KE; signed_lits_in KE.
          -- do 3 zstep.
             eapply (U_rv _ (x + ret) 0 eof f10); first [exact I2 | lia].
          -- zstep. if_cases KZ; zify_cond KZ.
             ++ do 3 zstep.
                eapply (U_rv _ (x + ret) 0 eof f10); first [exact I2 | lia].
             ++ do 2 zstep.
                eapply (U_end OLW _ (-1) ret 0); first [exact I2 | lia].
      + (* [comment removed for export] *)
        zstep. if_cases KS; zify_cond KS.
        * eapply (U_rv _ ret n eof f10); first [exact I | lia].
        * do 2 zstep.
          eapply (U_end OLW _ (-1) ret n); first [exact I | lia].
  Qed.
  (* [comment removed for export] *)
  Definition HEADP (i n eof ret : Z) : Prop :=
    forall mX x1 x7 x10 x11 x12 x14 x24 x26 x28 x29 x30,
      INV OLW mX -> 0 <= i < inl -> 0 <= n <= 64 -> 0 <= eof <= 2 -> 0 <= ret -> 4 * ret + 3 * n <= 3 * (i + num) ->
      evt psegs POST (ST 0x1748d8 mX x1 (Z_to_bv 64 242) (Z_to_bv 64 64) x7 (Z_to_bv 64 224) x10 x11 x12 (Z_to_bv 64 n) x14
                         (Z_to_bv 64 255) (Z_to_bv 64 61) (Z_to_bv 64 2) (Z_to_bv 64 C) (Z_to_bv 64 eof) (Z_to_bv 64 (B + ret)) (Z_to_bv 64 (C + 4))
                         (Z_to_bv 64 (inl - i)) (Z_to_bv 64 (B + i)) x24 (Z_to_bv 64 ret) x26 (Z_to_bv 64 B64_TABLE) x28 x29 x30).

  Section Iter.
    Variable i : Z.
    Hypothesis Hi : 0 <= i < inl.
    Hypothesis NEXT : forall n eof ret, HEADP (i + 1) n eof ret.

    (* [comment removed for export] *)
    Lemma U_next : forall mX n eof ret f10 x1 x7 x10 x11 x12 x14 x24 x28 x29 x30,
      INV OLW mX -> 0 <= n <= 64 -> 0 <= eof <= 2 -> 0 <= ret -> 4 * ret + 3 * n <= 3 * (i + 1 + num) -> 0 <= f10 <= 1 ->
      evt psegs POST (ST 0x174978 mX x1 (Z_to_bv 64 242) (Z_to_bv 64 64) x7 (Z_to_bv 64 224) x10 x11 x12 (Z_to_bv 64 n) x14
                         (Z_to_bv 64 255) (Z_to_bv 64 61) (Z_to_bv 64 2) (Z_to_bv 64 C) (Z_to_bv 64 eof) (Z_to_bv 64 (B + ret)) (Z_to_bv 64 (C + 4))
                         (Z_to_bv 64 (inl - i)) (Z_to_bv 64 (B + i)) x24 (Z_to_bv 64 ret) (Z_to_bv 64 f10) (Z_to_bv 64 B64_TABLE) x28 x29 x30).
    Proof.
      intros mX n eof ret f10 x1 x7 x10 x11 x12 x14 x24 x28 x29 x30 I Hn He Hret HI Hf.
      do 2 zstep.
      assert (SW : bv_swrap 32 (inl - i + -1) = inl - (i + 1)).
      { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 / 2)%Z with (2^31)%Z.
        rewrite Z.mod_small by lia. lia. }
      rewrite SW. replace (B + i + 1) with (B + (i + 1)) by lia.
      zstep. if_cases KL; zify_cond KL.
      - eapply (NEXT n eof ret); first [exact I | lia].
      - zstep. eapply (U_tail _ ret n eof f10); first [exact I | lia].
    Qed.
    (* [comment removed for export] *)
    Lemma U_n : forall mX n eof ret f10 x1 x7 x10 x11 x12 x14 x28 x29 x30,
      INV OLW mX -> 0 <= n <= 64 -> 0 <= eof <= 2 -> 0 <= ret -> 4 * ret + 3 * n <= 3 * (i + 1 + num) -> 0 <= f10 <= 1 ->
      evt psegs POST (ST 0x174930 mX x1 (Z_to_bv 64 242) (Z_to_bv 64 64) x7 (Z_to_bv 64 224) x10 x11 x12 (Z_to_bv 64 n) x14
                         (Z_to_bv 64 255) (Z_to_bv 64 61) (Z_to_bv 64 2) (Z_to_bv 64 C) (Z_to_bv 64 eof) (Z_to_bv 64 (B + ret)) (Z_to_bv 64 (C + 4))
                         (Z_to_bv 64 (inl - i)) (Z_to_bv 64 (B + i)) (Z_to_bv 64 (-1)) (Z_to_bv 64 ret) (Z_to_bv 64 f10) (Z_to_bv 64 B64_TABLE) x28 x29 x30).
    Proof.
      intros mX n eof ret f10 x1 x7 x10 x11 x12 x14 x28 x29 x30 I Hn He Hret HI Hf.
      zstep. if_cases K64; zify_cond K64.
      - eapply (U_next _ n eof ret f10); first [exact I | lia].
      - pose proof I as I'. open_inv I'.
        do 6 ths.
        call_dblock CN ED LED CT BLK LBS ret 64 eof.
        rejoin_block BA POST ret. clear PC1.
        lazymatch goal with MIh : mem_inv psegs ?mm |- _ => assert (I2 : INV OLW mm) by close_inv end.
        clear CN ED CT OLC FR PC0 MI0 MU WM.
        cbv beta delta [mkR].
        destruct PC as [-> | PC].
        + zstep. th_if_lit.
          eapply (U_end_r0 _ (-1) ret); first [exact I2 | lia].
        + zstep. if_cases KD; zify_cond KD; signed_lits_in KD. { exfalso. lia. }
          do 5 zstep. if_cases KE; zify_cond KE; signed_lits_in KE.
          * do 4 zstep.
            replace (B + ret + x) with (B + (x + ret)) by lia.
            eapply (U_next _ 0 eof (x + ret) f10); first [exact I2 | lia].
          * zstep. if_cases KZ; zify_cond KZ.
            -- eapply (U_end_r0 _ (-1) ret); first [exact I2 | lia].
            -- do 4 zstep.
               replace (B + ret + x) with (B + (x + ret)) by lia.
               eapply (U_next _ 0 eof (x + ret) f10); first [exact I2 | lia].
    Qed.
    (* [comment removed for export] *)
    Lemma U_mid : forall mX n eof ret tz vz x1 x7 x14 x26 x28 x29 x30,
      INV OLW mX -> 0 <= n <= 64 -> 0 <= eof <= 2 -> 0 <= ret -> 4 * ret + 3 * n <= 3 * (i + num) -> 0 <= tz < 128 -> 0 <= vz <= 255 ->
      evt psegs POST (ST 0x17490c mX x1 (Z_to_bv 64 242) (Z_to_bv 64 64) x7 (Z_to_bv 64 224) (Z_to_bv 64 tz) (Z_to_bv 64 vz) (Z_to_bv 64 (Z.land vz 236))
                         (Z_to_bv 64 n) x14
                         (Z_to_bv 64 255) (Z_to_bv 64 61) (Z_to_bv 64 2) (Z_to_bv 64 C) (Z_to_bv 64 eof) (Z_to_bv 64 (B + ret)) (Z_to_bv 64 (C + 4))
                         (Z_to_bv 64 (inl - i)) (Z_to_bv 64 (B + i)) (Z_to_bv 64 (-1)) (Z_to_bv 64 ret) x26 (Z_to_bv 64 B64_TABLE) x28 x29 x30).
    Proof.
      intros mX n eof ret tz vz x1 x7 x14 x26 x28 x29 x30 I Hn He Hret HI Htz Hvz.
      do 3 zstep.
      assert (Hf : 0 <= Z.b2z (0 <? Z.land (vz + -242) 18446744073709551615) <= 1) by (destruct (0 <? Z.land (vz + -242) 18446744073709551615); cbn; lia).
      if_cases KEOF.
      - eapply (U_tail _ ret n eof _); first [exact I | lia].
      - zstep. if_cases KNB.
        + eapply (U_n _ n eof ret _); first [exact I | lia].
        + do 2 zstep. if_cases K63; zify_cond K63; signed_lits_in K63.
          * eapply (U_end_r _ (-1) ret n); first [exact I | lia].
          * pose proof I as I'. open_inv I'.
            do 2 zstep.
            pose proof (u8arr_store_ok_n psegs mX (C + 4) ed' n 1 (Z_to_bv 64 (C + 4 + n)) ED ltac:(lia) ltac:(rewrite LED; lia) eq_refl) as SOK.
            zstep. rewrite th_le1_mod.
            pose proof (u8arr_write_bytes psegs mX (C + 4) ed' n [Z_to_bv 8 (tz mod 256)] ED ltac:(lia) ltac:(cbn [length]; rewrite LED; lia)) as ED2.
            assert (LED2 : length (upd_bytes ed' (Z.to_nat n) [Z_to_bv 8 (tz mod 256)]) = 80%nat) by (rewrite upd_bytes_length; [exact LED | cbn [length]; rewrite LED; lia]).
            clear ED.
            store_done.
            assert (SW : bv_swrap 32 (n + 1) = n + 1).
            { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 / 2)%Z with (2^31)%Z.
              rewrite Z.mod_small by lia. lia. }
            rewrite SW.
            lazymatch goal with MIh : mem_inv psegs ?mm |- _ => assert (I2 : INV OLW mm) by close_inv end.
            eapply (U_n _ (n + 1) eof ret _); first [exact I2 | lia].
    Qed.
    (* [comment removed for export] *)
    Lemma U_head : forall n eof ret, HEADP i n eof ret.
    Proof.
      intros n eof ret mX x1 x7 x10 x11 x12 x14 x24 x26 x28 x29 x30 I _ Hn He Hret HI.
      pose proof I as I'. open_inv I'.
      destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:Hb; [|apply nth_error_None in Hb; lia].
      pose proof (u8arr_read psegs mX B bs i b (Z_to_bv 64 (B + i)) BLK Hb ltac:(lia) eq_refl) as RD.
      zstep. clear RD. do 2 zstep.
      destruct (sxb_cases b) as [[SB HB]|[SB [HB EQ]]]; rewrite SB; cbv iota.
      - eapply (U_end_r _ (-1) ret n); first [exact I | lia].
      - rewrite EQ. zstep.
        pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
        destruct (b64_table_nth (bv_unsigned b) ltac:(lia)) as [v Hv].
        pose proof (u8ro_read psegs _ B64_TABLE b64_table (bv_unsigned b) v (Z_to_bv 64 (B64_TABLE + bv_unsigned b))
                      (b64_table_at _ MI) Hv ltac:(lia) eq_refl) as RD2.
        zstep. clear RD2.
        pose proof (bv_unsigned_in_range 8 v) as Rv. unfold bv_modulus in Rv. change (2 ^ Z.of_N 8) with 256 in Rv.
        clear CN ED LED CT BLK LBS OLC FR ST MI MU WM.
        zstep. if_cases K255.
        + eapply (U_end_r _ (-1) ret n); first [exact I | lia].
        + do 2 zstep. if_cases K61.
          * (* [comment removed for export] *)
            zstep. if_cases KE0; zify_cond KE0; signed_lits_in KE0.
            -- do 2 zstep.
               eapply (U_mid _ n 0 ret (bv_unsigned b) (bv_unsigned v)); first [exact I | lia].
            -- zstep. if_cases KB.
               ++ eapply (U_end_r _ (-1) ret n); first [exact I | lia].
               ++ zstep. if_cases K2; zify_cond K2; signed_lits_in K2.
                  ** eapply (U_end_r _ (-1) ret n); first [exact I | lia].
                  ** eapply (U_mid _ n eof ret (bv_unsigned b) (bv_unsigned v)); first [exact I | lia].
          * (* [comment removed for export] *)
            do 2 zstep.
            assert (SW : bv_swrap 32 (eof + 1) = eof + 1).
            { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 / 2)%Z with (2^31)%Z.
              rewrite Z.mod_small by lia. lia. }
            rewrite SW.
            zstep. if_cases K2; zify_cond K2; signed_lits_in K2.
            -- eapply (U_end_r _ (-1) ret n); first [exact I | lia].
            -- eapply (U_mid _ n (eof + 1) ret (bv_unsigned b) (bv_unsigned v)); first [exact I | lia].
    Qed.
  End Iter.
  Lemma U_loop : forall (k : nat) i, Z.to_nat (inl - i) = k -> forall n eof ret, HEADP i n eof ret.
  Proof.
    induction k as [k IH] using lt_wf_ind; intros i HK n eof ret.
    intros mX x1 x7 x10 x11 x12 x14 x24 x26 x28 x29 x30 I Hi Hn He Hret HI.
    eapply (U_head i Hi); [| exact I | exact Hi | exact Hn | exact He | exact Hret | exact HI].
    intros n' eof' ret'. eapply (IH (Z.to_nat (inl - (i + 1)))); [lia | reflexivity].
  Qed.
  Lemma ectx_split : forall mX nw ed',
    rw_cells psegs mX C (ectx_cells nw ed' ln z64) ->
    rw_cells psegs mX C [C4 nw] /\ u8arr psegs mX (C + 4) ed' /\ rw_cells psegs mX (C + 84) [C4 ln; C4 z64].
  Proof.
    intros mX nw ed' H. unfold ectx_cells in H.
    change [C4 nw; CB 80 ed'; C4 ln; C4 z64] with ([C4 nw] ++ [CB 80 ed'] ++ [C4 ln; C4 z64]) in H.
    apply (proj1 (rw_cells_app psegs mX C _ _)) in H. destruct H as [CN H]. cbn [cells_size csize Nat.add] in H.
    apply (proj1 (rw_cells_app psegs mX (C + Z.of_nat 4) _ _)) in H. destruct H as [ED CT]. cbn [cells_size csize Nat.add] in CT.
    replace (C + Z.of_nat 4 + Z.of_nat 80) with (C + 84) in CT by lia.
    split; [exact CN|]. split; [|exact CT]. apply u8arr_of_rw_cells in ED. exact ED.
  Qed.

  (* [comment removed for export] *)
  Lemma U_flags : forall slot mX eof x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x24 x25 x26 x27 x28 x29 x30,
    INV slot mX -> 0 < inl -> 0 <= eof <= 2 ->
    evt psegs POST (ST 0x174880 mX x1 x5 x6 x7 OLW x10 x11 x12 (Z_to_bv 64 num) x14 x15 x16 x17 (Z_to_bv 64 C) (Z_to_bv 64 eof) (Z_to_bv 64 B)
                       (Z_to_bv 64 (C + 4)) (Z_to_bv 64 inl) (Z_to_bv 64 B) x24 x25 x26 x27 x28 x29 x30).
  Proof.
    intros slot mX eof x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x24 x25 x26 x27 x28 x29 x30 I Hinl He.
    open_inv I.
    apply (th_cells_congr psegs mX (C + 84) _ [C4 ln; C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) in CT;
      [| reflexivity | reflexivity | cbn; tauto].
    do 3 ths. th_if_lit.
    do 2 ths.
    ths.
    do 2 zstep. if_cases KI; zify_cond KI; signed_lits_in KI. { exfalso. lia. }
    do 6 zstep.
    apply (th_cells_congr psegs _ (C + 84) _ [C4 ln; C4 z64]) in CT; [| reflexivity | reflexivity | cbn; tauto].
    lazymatch goal with MIh : mem_inv psegs ?mm |- _ => assert (I2 : INV OLW mm) by close_inv end.
    replace (Z_to_bv 64 B) with (Z_to_bv 64 (B + 0)) by (f_equal; lia).
    replace (Z_to_bv 64 inl) with (Z_to_bv 64 (inl - 0)) by (f_equal; lia).
    eapply (U_loop (Z.to_nat (inl - 0)) 0 eq_refl num eof 0); first [exact I2 | lia].
  Qed.
  (* [comment removed for export] *)
  Lemma U_join : forall slot mX eof x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x24 x25 x26 x27 x28 x29 x30,
    INV slot mX -> 0 <= eof <= 2 ->
    evt psegs POST (ST 0x17487c mX x1 x5 x6 x7 OLW x10 x11 x12 (Z_to_bv 64 num) x14 x15 x16 x17 (Z_to_bv 64 C) (Z_to_bv 64 eof) (Z_to_bv 64 B)
                       (Z_to_bv 64 (C + 4)) (Z_to_bv 64 inl) (Z_to_bv 64 B) x24 x25 x26 x27 x28 x29 x30).
  Proof.
    intros slot mX eof x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x24 x25 x26 x27 x28 x29 x30 I He.
    zstep. if_cases KI; zify_cond KI.
    - do 3 zstep. eapply (U_end slot _ 0 0 num); first [exact I | lia].
    - eapply (U_flags slot _ eof); first [exact I | lia].
  Qed.

  Lemma U_eof0 : forall slot mX x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x19 x24 x25 x26 x27 x28 x29 x30,
    INV slot mX ->
    evt psegs POST (ST 0x174898 mX x1 x5 x6 x7 OLW x10 x11 x12 (Z_to_bv 64 num) x14 x15 x16 x17 (Z_to_bv 64 C) x19 (Z_to_bv 64 B)
                       (Z_to_bv 64 (C + 4)) (Z_to_bv 64 inl) (Z_to_bv 64 B) x24 x25 x26 x27 x28 x29 x30).
  Proof.
    intros slot mX x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x19 x24 x25 x26 x27 x28 x29 x30 I.
    do 2 zstep. if_cases KI; zify_cond KI.
    - eapply (U_flags slot _ 0); first [exact I | lia].
    - do 3 zstep. eapply (U_end slot _ 0 0 num); first [exact I | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma dupdate_body : forall ed bs t0 t1 t2 a5 a6 a7 t3 t4 t5,
    rw_cells psegs m C (ectx_cells (Z_to_bv 64 num) ed ln z64) -> length ed = 80%nat ->
    rw_cells psegs m B [CB N bs] -> rw_cells psegs m OL [C4 old] -> stk psegs m lo SP -> mem_inv psegs m ->
    evt psegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 C) (Z_to_bv 64 B) OLW (Z_to_bv 64 B) (Z_to_bv 64 inl) a5 a6 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1747f8) fc None m (seg_rom psegs)).
  Proof.
    intros ed bs t0 t1 t2 a5 a6 a7 t3 t4 t5 CTX LED BLK OLC ST MI.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl psegs m) as WM.
    destruct (ectx_split _ _ _ CTX) as (CN & ED & CT). clear CTX.
    pose proof (rw_cells_CB_length psegs _ _ _ _ BLK) as LBS. apply u8arr_of_rw_cells in BLK.
    th_frame 112%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
    do 15 ths. do 5 ths.
    ths. rewrite (t_sx32_small num) by lia.
    ths.
    (* [comment removed for export] *)
    assert (L8 : length (firstn 8 junk) = 8%nat) by (destruct FR as [[WF _] _]; cbn in WF; tauto).
    apply (th_cells_congr psegs _ (SP + -112) _
             [C8 (bv_extract 0 64 (le_bytes_to_word (firstn 8 junk))); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) in FR;
      [| cbn [cells_bytes cbytes]; rewrite (le8_ld _ L8); reflexivity | reflexivity | cbn; tauto].
    lazymatch goal with MIh : mem_inv psegs ?mm |- _ => assert (I : INV (bv_extract 0 64 (le_bytes_to_word (firstn 8 junk))) mm) by close_inv end.
    zstep. if_cases KN; zify_cond KN; signed_lits_in KN.
    - eapply (U_eof0 _ _); exact I.
    - destruct (nth_error ed (Z.to_nat (num - 1))) as [b1|] eqn:Hb1; [|apply nth_error_None in Hb1; lia].
      pose proof (u8arr_read psegs _ (C + 4) ed (num - 1) b1 (Z_to_bv 64 (C + 4 + num + -1)) ED Hb1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      do 2 zstep. clear RD.
      do 2 zstep. if_cases KP.
      + eapply (U_eof0 _ _); exact I.
      + do 2 zstep. if_cases K1; zify_cond K1.
        * eapply (U_join _ _ 1); first [exact I | lia].
        * destruct (nth_error ed (Z.to_nat (num - 2))) as [b2|] eqn:Hb2; [|apply nth_error_None in Hb2; lia].
          pose proof (u8arr_read psegs _ (C + 4) ed (num - 2) b2 (Z_to_bv 64 (C + 4 + num + -2)) ED Hb2 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
          zstep. clear RD.
          do 3 zstep.
          set (e := Z.b2z (Z.land (bv_unsigned b2 + -61) 18446744073709551615 <? 1) + 1).
          assert (He : 1 <= e <= 2) by (unfold e; destruct (Z.land (bv_unsigned b2 + -61) 18446744073709551615 <? 1); cbn [Z.b2z]; lia).
          assert (SW : bv_swrap 32 e = e).
          { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 / 2)%Z with (2^31)%Z.
            rewrite Z.mod_small by lia. lia. }
          rewrite SW. clearbody e.
          eapply (U_join _ _ e); first [exact I | lia].
  Qed.
End Proofs.

(* [comment removed for export] *)
Definition W4_decode_update_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (C B OL : Z) (N : nat) (inl num : Z) (ln old : word) (ed bs : list byte) (lo : Z),
    a0 = Z_to_bv 64 C -> a1 = Z_to_bv 64 B -> a2 = Z_to_bv 64 OL -> a3 = Z_to_bv 64 B -> a4 = Z_to_bv 64 inl ->
    0 < C -> C mod 4 = 0 -> 0 < B -> 0 < OL -> OL mod 4 = 0 ->
    rw_cells psegs m C (ectx_cells (Z_to_bv 64 num) ed ln z64) -> length ed = 80%nat -> 0 <= num <= 64 ->
    rw_cells psegs m B [CB N bs] -> 0 <= inl <= Z.of_nat N -> inl < 2 ^ 31 -> 3 * (inl + num) <= 4 * Z.of_nat N ->
    rw_cells psegs m OL [C4 old] ->
    stk psegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 128 ->
    (C + 92 <= B \/ B + Z.of_nat N <= C) -> (C + 92 <= OL \/ OL + 4 <= C) -> (B + Z.of_nat N <= OL \/ OL + 4 <= B) ->
    (C + 92 <= lo \/ bv_unsigned sp <= C) -> (B + Z.of_nat N <= lo \/ bv_unsigned sp <= B) -> (OL + 4 <= lo \/ bv_unsigned sp <= OL) ->
    mem_inv psegs m ->
    evt psegs (dupdate_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 F fc C B OL N inl num ln lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1747f8) fc None m (seg_rom psegs)).

Theorem W4_decode_update_proof : W4_decode_update_stmt.
Proof.
  unfold W4_decode_update_stmt. intros until lo.
  intros -> -> -> -> -> HC HCA HB HO HOA CTX LED HN BLK HI HI31 HROOM OLC ST LO0 LO S1 S2 S3 S4 S5 S6 MI.
  pose proof (rw_cells_bound _ _ _ _ CTX) as CB. unfold ectx_cells in CB. cbn [cells_size csize Nat.add] in CB.
  pose proof (rw_cells_bound _ _ _ _ BLK) as BB. cbn [cells_size csize Nat.add] in BB.
  pose proof (rw_cells_bound _ _ _ _ OLC) as OB. cbn [cells_size csize Nat.add] in OB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  eapply (dupdate_body ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 F fc m C B OL N inl num ln old lo); try eassumption; lia.
Qed.

