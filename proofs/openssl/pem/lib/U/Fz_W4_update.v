(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Ubs Arr SFModel.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_W4_defs Fz_W4_block.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation z64 := (Z_to_bv 64 0) (only parsing).

Definition dupdate_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (C B OL : Z) (N : nat) (inl num : Z) (ln : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (rv ret num' : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (ed' bs' : list byte) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (C, C + 84); (B, B + Z.of_nat N); (OL, OL + 4)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ (-1 <= rv <= 1 /\ 0 <= ret /\ 0 <= num' <= 64 /\ 4 * ret + 3 * num' <= 3 * (inl + num))
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' C (ectx_cells (Z_to_bv 64 num') ed' ln z64) /\ length ed' = 80%nat
    /\ rw_cells usegs m' B [CB N bs']
    /\ rw_cells usegs m' OL [C4 (Z_to_bv 64 ret)].

Section Proofs.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (C B OL : Z) (N : nat) (inl num : Z) (ln old : word) (lo : Z).
  Notation SP := (bv_unsigned sp).
  Notation W := [(bv_unsigned sp - 160, bv_unsigned sp); (C, C + 84); (B, B + Z.of_nat N); (OL, OL + 4)]%Z.
  Hypothesis AB : 0 <= num <= 64 /\ 0 <= inl <= Z.of_nat N /\ inl < 2 ^ 31 /\ 3 * (inl + num) <= 4 * Z.of_nat N
                  /\ 0 < C /\ C + 92 <= 2 ^ 64 /\ 0 < B /\ B + Z.of_nat N <= 2 ^ 64 /\ 0 < OL /\ OL + 4 <= 2 ^ 64
                  /\ 0 <= lo /\ lo <= SP - 160 /\ SP < 2 ^ 64.
  Hypothesis SEP_CB : C + 92 <= B \/ B + Z.of_nat N <= C.
  Hypothesis SEP_CO : C + 92 <= OL \/ OL + 4 <= C.
  Hypothesis SEP_BO : B + Z.of_nat N <= OL \/ OL + 4 <= B.
  Hypothesis SEP_CS : C + 92 <= lo \/ SP <= C.
  Hypothesis SEP_BS : B + Z.of_nat N <= lo \/ SP <= B.
  Hypothesis SEP_OS : OL + 4 <= lo \/ SP <= OL.
  Hypothesis CAL : C mod 4 = 0.
  Hypothesis OAL : OL mod 4 = 0.

  Notation POST := (dupdate_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc C B OL N inl num ln lo m).
  (* [comment removed for export] *)
  Notation ST pc mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -112)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition INV (slot : word) (mX : mem) : Prop :=
    exists (ed' bs : list byte),
      rw_cells usegs mX C [C4 (Z_to_bv 64 num)] /\ u8arr usegs mX (C + 4) ed' /\ length ed' = 80%nat
      /\ rw_cells usegs mX (C + 84) [C4 ln; C4 z64]
      /\ u8arr usegs mX B bs /\ length bs = N
      /\ rw_cells usegs mX OL [C4 old]
      /\ rw_cells usegs mX (SP + -112) [C8 slot; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ stk usegs mX lo (SP + -112)
      /\ mem_inv usegs mX /\ munch W m mX /\ wmono usegs m mX.

  Ltac open_inv I := destruct I as (ed' & bs & CN & ED & LED & CT & BLK & LBS & OLC & FR & ST & MI & MU & WM).
  Ltac close_inv := do 2 eexists; do 11 (split; [eassumption|]); eassumption.

  (* [comment removed for export] *)
  Lemma ectx_join : forall mX nw ed', length ed' = 80%nat ->
    rw_cells usegs mX C [C4 nw] -> u8arr usegs mX (C + 4) ed' -> rw_cells usegs mX (C + 84) [C4 ln; C4 z64] ->
    rw_cells usegs mX C (ectx_cells nw ed' ln z64).
  Proof.
    intros mX nw ed' L CN ED CT. apply rw_cells_of_u8arr in ED. rewrite L in ED. unfold ectx_cells.
    change [C4 nw; CB 80 ed'; C4 ln; C4 z64] with ([C4 nw] ++ [CB 80 ed'] ++ [C4 ln; C4 z64]).
    apply (proj2 (rw_cells_app usegs mX C _ _)). split; [exact CN|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app usegs mX (C + Z.of_nat 4) _ _)). split; [exact ED|]. cbn [cells_size csize Nat.add].
    replace (C + Z.of_nat 4 + Z.of_nat 80) with (C + 84) by lia. exact CT.
  Qed.

  (* [comment removed for export] *)
  Lemma U_end : forall slot mX rv ret n x1 x5 x7 x9 x10 x11 x14 x15 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x30 x31,
    INV slot mX -> -1 <= rv <= 1 -> 0 <= ret -> 0 <= n <= 64 -> 4 * ret + 3 * n <= 3 * (inl + num) ->
    evt usegs POST (ST 0x192074 mX x1 x5 (Z_to_bv 64 ret) x7 x9 x10 x11 (Z_to_bv 64 OL) (Z_to_bv 64 n) x14 x15 x16 (Z_to_bv 64 C) x18 x19 x20 x21 x22 x23
                       x24 x25 x26 x27 x28 (Z_to_bv 64 rv) x30 x31).
  Proof.
    intros slot mX rv ret n x1 x5 x7 x9 x10 x11 x14 x15 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x30 x31 I Hrv Hret Hn HI.
    open_inv I.
    do 3 ths.
    do 13 ths. do 2 ths.
    release_frame FR ST (bv_unsigned sp).
    pose proof (ectx_join _ _ _ LED CN ED CT) as CTX.
    apply rw_cells_of_u8arr in BLK. rewrite LBS in BLK.
    apply evt_done. exists rv, ret, n. do 14 eexists. exists ed', bs. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [lia|]. split; [exact ST|].
    split; [exact CTX|]. split; [exact LED|]. split; [exact BLK | exact OLC].
  Qed.
  Notation OLW := (Z_to_bv 64 OL).

  (* [comment removed for export] *)
  Lemma U_end_r : forall mX rv ret n x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x30 x31,
    INV OLW mX -> -1 <= rv <= 1 -> 0 <= ret -> 0 <= n <= 64 -> 4 * ret + 3 * n <= 3 * (inl + num) ->
    evt usegs POST (ST 0x192004 mX x1 x5 x6 x7 (Z_to_bv 64 C) x10 x11 x12 (Z_to_bv 64 n) x14 x15 x16 x17 (Z_to_bv 64 ret) x19 x20 x21 x22 x23
                       x24 x25 x26 x27 x28 (Z_to_bv 64 rv) x30 x31).
  Proof.
    intros mX rv ret n x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x30 x31 I Hrv Hret Hn HI.
    pose proof I as I'. open_inv I'.
    do 5 ths. ubs_if. do 2 ths. ubs_if.
    eapply (U_end OLW _ rv ret n); first [exact I | lia].
  Qed.

  Lemma U_end_r0 : forall mX rv ret x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x30 x31,
    INV OLW mX -> -1 <= rv <= 1 -> 0 <= ret -> 4 * ret <= 3 * (inl + num) ->
    evt usegs POST (ST 0x192000 mX x1 x5 x6 x7 (Z_to_bv 64 C) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ret) x19 x20 x21 x22 x23
                       x24 x25 x26 x27 x28 (Z_to_bv 64 rv) x30 x31).
  Proof.
    intros mX rv ret x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x30 x31 I Hrv Hret HI.
    zstep. eapply (U_end_r _ rv ret 0); first [exact I | lia].
  Qed.
  (* [comment removed for export] *)
  Lemma U_rv : forall mX ret n eof f10 x1 x5 x7 x9 x10 x11 x14 x15 x16 x18 x19 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31,
    INV OLW mX -> 0 <= ret -> 0 <= n <= 64 -> 4 * ret + 3 * n <= 3 * (inl + num) -> 0 <= f10 <= 1 ->
    evt usegs POST (ST 0x192058 mX x1 x5 (Z_to_bv 64 ret) x7 x9 x10 x11 OLW (Z_to_bv 64 n) x14 x15 x16 (Z_to_bv 64 C) x18 x19 (Z_to_bv 64 f10) x21 x22 x23
                       x24 x25 (Z_to_bv 64 eof) x27 x28 x29 x30 x31).
  Proof.
    intros mX ret n eof f10 x1 x5 x7 x9 x10 x11 x14 x15 x16 x18 x19 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 I Hret Hn HI Hf.
    do 5 zstep. ubs_if. do 2 zstep. ubs_if.
    eapply (U_end OLW mX _ ret n); [exact I | | lia | lia | lia].
    assert (Hf' : f10 = 0 \/ f10 = 1) by lia.
    destruct Hf' as [-> | ->]; destruct (Z.land eof 18446744073709551615 <? 1); destruct (0 <? n); split; apply Z.leb_le; reflexivity.
  Qed.
  (* [comment removed for export] *)
  Ltac call_dblock CN ED LED CT BLK LBS ret n eof :=
    let CTXR := fresh "CTXR" in
    pose proof (proj1 (ectx_join _ _ _ LED CN ED CT) : ro_cells usegs _ C (ectx_cells (Z_to_bv 64 num) _ ln z64)) as CTXR;
    let BA := fresh "BA" in let BB := fresh "BB" in
    apply rw_cells_of_u8arr in BLK; rewrite LBS in BLK;
    destruct (rw_cells_CB_split_at usegs _ B N _ (Z.to_nat ret) ltac:(lia) BLK) as [BA BB]; clear BLK;
    rewrite Z2Nat.id in BB by lia;
    tcall (dblock_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C (B + ret) (N - Z.to_nat ret)%nat n eof (Z_to_bv 64 num) ln _ _ lo);
    [ first [reflexivity | eassumption | lia] .. | ].

  (* [comment removed for export] *)
  Ltac rejoin_block BA POST ret :=
    replace (B + ret) with (B + Z.of_nat (Z.to_nat ret)) in POST by lia;
    let BLK' := fresh "BLK" in let LB' := fresh "LBS" in
    pose proof (rw_cells_CB_join usegs _ B _ _ _ _ BA POST) as BLK';
    replace (Z.to_nat ret + (N - Z.to_nat ret))%nat with N in BLK' by lia;
    pose proof (rw_cells_CB_length usegs _ _ _ _ BLK') as LB';
    apply u8arr_of_rw_cells in BLK'; clear BA POST.

  (* [comment removed for export] *)
  Lemma U_tail : forall mX ret n eof f10 x1 x5 x9 x10 x11 x14 x15 x16 x18 x19 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31,
    INV OLW mX -> 0 <= ret -> 0 <= n <= 64 -> 4 * ret + 3 * n <= 3 * (inl + num) -> 0 <= eof <= 2 -> 0 <= f10 <= 1 ->
    evt usegs POST (ST 0x191fa0 mX x1 x5 (Z_to_bv 64 ret) (Z_to_bv 64 (B + ret)) x9 x10 x11 (Z_to_bv 64 (C + 4)) (Z_to_bv 64 n) x14 x15 x16 (Z_to_bv 64 C) x18 x19 (Z_to_bv 64 f10)
                       x21 x22 x23 x24 x25 (Z_to_bv 64 eof) x27 x28 x29 x30 x31).
  Proof.
    intros mX ret n eof f10 x1 x5 x9 x10 x11 x14 x15 x16 x18 x19 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 I Hret Hn HI He Hf.
    pose proof (Z.mul_div_le n 4 ltac:(lia)) as HD. pose proof (Z.div_pos n 4 ltac:(lia) ltac:(lia)) as HD0.
    zstep. if_cases K0; zify_cond K0; signed_lits_in K0. all: cycle 1.
    - (* [comment removed for export] *)
      pose proof I as I'. open_inv I'. zstep. ths.
      eapply (U_rv _ ret n eof f10); first [exact I | lia].
    - pose proof I as I'. open_inv I'.
      do 2 ths. if_cases K3; zify_cond K3.
      + (* [comment removed for export] *)
        do 6 ths.
        call_dblock CN ED LED CT BLK LBS ret n eof.
        rejoin_block BA POST ret. clear PC1.
        lazymatch goal with MIh : mem_inv usegs ?mm |- _ => assert (I2 : INV OLW mm) by close_inv end.
        clear CN ED CT OLC PC0 MI0 MU WM.
        cbv beta delta [mkR].
        destruct PC as [-> | PC].
        * do 2 zstep. th_if_lit. zstep. ths. do 4 zstep. ubs_if. do 2 zstep. ubs_if.
          eapply (U_end OLW _ (-1) ret 0); first [exact I2 | lia].
        * assert (SW : forall z, - 2 ^ 31 <= z < 2 ^ 31 -> bv_swrap 32 z = z)
            by (intros z Hz; unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus; change (2 ^ Z.of_N 32)%Z with (2^32)%Z;
                change (2 ^ 32 `div` 2)%Z with (2^31)%Z; rewrite Z.mod_small by lia; lia).
          do 2 zstep. if_cases KD; zify_cond KD; signed_lits_in KD. { exfalso. lia. }
          do 2 zstep. if_cases KE; zify_cond KE; signed_lits_in KE.
          -- do 4 zstep. if_cases KC; zify_cond KC; signed_lits_in KC.
             { exfalso. apply KC. rewrite !(SW (ret + 0)) by lia. rewrite !land_W64. rewrite (Z.mod_small (ret + 0)) by lia.
               rewrite (SW (ret + 0 + x)) by lia. reflexivity. }
             do 2 zstep. ths.
             rewrite !(SW (ret + 0)) by lia. rewrite (land_W64 (ret + 0)), (Z.mod_small (ret + 0)) by lia.
             rewrite (SW (ret + 0 + x)) by lia. replace (ret + 0 + x) with (ret + x) by lia.
             eapply (U_rv _ (ret + x) 0 eof f10); first [exact I2 | lia].
          -- zstep. if_cases KZ; zify_cond KZ.
             ++ do 4 zstep. if_cases KC; zify_cond KC; signed_lits_in KC.
                { exfalso. apply KC. rewrite !(SW (ret + 0)) by lia. rewrite !land_W64. rewrite (Z.mod_small (ret + 0)) by lia.
                  rewrite (SW (ret + 0 + x)) by lia. reflexivity. }
                do 2 zstep. ths.
                rewrite !(SW (ret + 0)) by lia. rewrite (land_W64 (ret + 0)), (Z.mod_small (ret + 0)) by lia.
                rewrite (SW (ret + 0 + x)) by lia. replace (ret + 0 + x) with (ret + x) by lia.
                eapply (U_rv _ (ret + x) 0 eof f10); first [exact I2 | lia].
             ++ zstep. ths. do 3 zstep. ubs_if. do 2 zstep. ubs_if.
                eapply (U_end OLW _ (-1) ret 0); first [exact I2 | lia].
      + (* [comment removed for export] *)
        do 2 ths. if_cases KS; zify_cond KS.
        * do 3 zstep. ubs_if. do 2 zstep. ubs_if.
          eapply (U_end OLW _ (-1) ret n); first [exact I | lia].
        * zstep.
          eapply (U_rv _ ret n eof f10); first [exact I | lia].
  Qed.
  (* [comment removed for export] *)
  Definition HEADP (i n eof ret : Z) : Prop :=
    forall mX x1 x5 x10 x11 x14 x15 x20 x25 x28 x29,
      INV OLW mX -> 0 <= i < inl -> 0 <= n <= 64 -> 0 <= eof <= 2 -> 0 <= ret -> 4 * ret + 3 * n <= 3 * (i + num) ->
      evt usegs POST (ST 0x191e70 mX x1 x5 (Z_to_bv 64 ret) (Z_to_bv 64 (B + ret)) (Z_to_bv 64 (B + i)) x10 x11 (Z_to_bv 64 (C + 4)) (Z_to_bv 64 n) x14
                         x15 (Z_to_bv 64 B64_TABLE) (Z_to_bv 64 C) (Z_to_bv 64 61) (Z_to_bv 64 242) x20 (Z_to_bv 64 224)
                         (Z_to_bv 64 (inl - i)) (Z_to_bv 64 (B + i)) (Z_to_bv 64 64) x25 (Z_to_bv 64 eof) (Z_to_bv 64 (2 ^ 64 - 1 - B64_TABLE)) x28 x29 (Z_to_bv 64 2) (Z_to_bv 64 255)).

  Section Iter.
    Variable i : Z.
    Hypothesis Hi : 0 <= i < inl.
    Hypothesis NEXT : forall n eof ret, HEADP (i + 1) n eof ret.

    (* [comment removed for export] *)
    Lemma U_next : forall mX n eof ret f10 x1 x5 x10 x11 x14 x15 x25 x28 x29,
      INV OLW mX -> 0 <= n <= 64 -> 0 <= eof <= 2 -> 0 <= ret -> 4 * ret + 3 * n <= 3 * (i + 1 + num) -> 0 <= f10 <= 1 ->
      evt usegs POST (ST 0x191f94 mX x1 x5 (Z_to_bv 64 ret) (Z_to_bv 64 (B + ret)) (Z_to_bv 64 (B + i)) x10 x11 (Z_to_bv 64 (C + 4)) (Z_to_bv 64 n) x14
                         x15 (Z_to_bv 64 B64_TABLE) (Z_to_bv 64 C) (Z_to_bv 64 61) (Z_to_bv 64 242) (Z_to_bv 64 f10) (Z_to_bv 64 224)
                         (Z_to_bv 64 (inl - i)) (Z_to_bv 64 (B + i + 1)) (Z_to_bv 64 64) x25 (Z_to_bv 64 eof) (Z_to_bv 64 (2 ^ 64 - 1 - B64_TABLE)) x28 x29 (Z_to_bv 64 2) (Z_to_bv 64 255)).
    Proof.
      intros mX n eof ret f10 x1 x5 x10 x11 x14 x15 x25 x28 x29 I Hn He Hret HI Hf.
      do 2 zstep.
      assert (SW : bv_swrap 32 (inl - i + -1) = inl - (i + 1)).
      { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 / 2)%Z with (2^31)%Z.
        rewrite Z.mod_small by lia. lia. }
      rewrite SW. replace (B + i + 1) with (B + (i + 1)) by lia.
      zstep. if_cases KL; zify_cond KL.
      - eapply (NEXT n eof ret); first [exact I | lia].
      - eapply (U_tail _ ret n eof f10); first [exact I | lia].
    Qed.
    (* [comment removed for export] *)
    Lemma U_n : forall mX n eof ret f10 x1 x5 x10 x11 x14 x15 x25 x28 x29,
      INV OLW mX -> 0 <= n <= 64 -> 0 <= eof <= 2 -> 0 <= ret -> 4 * ret + 3 * n <= 3 * (i + 1 + num) -> 0 <= f10 <= 1 ->
      evt usegs POST (ST 0x191ef8 mX x1 x5 (Z_to_bv 64 ret) (Z_to_bv 64 (B + ret)) (Z_to_bv 64 (B + i)) x10 x11 (Z_to_bv 64 (C + 4)) (Z_to_bv 64 n) x14
                         x15 (Z_to_bv 64 B64_TABLE) (Z_to_bv 64 C) (Z_to_bv 64 61) (Z_to_bv 64 242) (Z_to_bv 64 f10) (Z_to_bv 64 224) (Z_to_bv 64 (inl - i))
                         (Z_to_bv 64 (B + i + 1)) (Z_to_bv 64 64) x25 (Z_to_bv 64 eof) (Z_to_bv 64 (2 ^ 64 - 1 - B64_TABLE)) x28 x29 (Z_to_bv 64 2) (Z_to_bv 64 255)).
    Proof.
      intros mX n eof ret f10 x1 x5 x10 x11 x14 x15 x25 x28 x29 I Hn He Hret HI Hf.
      zstep. if_cases K64; zify_cond K64.
      - eapply (U_next _ n eof ret f10); first [exact I | lia].
      - pose proof I as I'. open_inv I'.
        do 11 ths.
        call_dblock CN ED LED CT BLK LBS ret 64 eof.
        rejoin_block BA POST ret. clear PC1.
        lazymatch goal with MIh : mem_inv usegs ?mm |- _ => assert (I2 : INV OLW mm) by close_inv end.
        clear CN ED CT OLC FR PC0 MI0 MU WM.
        cbv beta delta [mkR].
        destruct PC as [-> | PC].
        + zstep. th_if_lit.
          pose proof I2 as I3. destruct I3 as (ed3 & bs3 & CN3 & ED3 & LED3 & CT3 & BLK3 & LBS3 & OLC3 & FR3 & ST3 & MI3 & MU3 & WM3).
          do 8 zstep. ubs_if. do 2 zstep. ubs_if.
          eapply (U_end OLW _ (-1) ret 0); first [exact I2 | lia].
        + assert (SW0 : forall z, 0 <= z < 2 ^ 31 -> bv_swrap 32 z = z).
          { intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 / 2)%Z with (2^31)%Z.
            rewrite Z.mod_small by lia. lia. }
          assert (BT : B + Z.of_nat N <= 2 ^ 47).
          { pose proof I2 as I3. destruct I3 as (ed3 & bs3 & CN3 & ED3 & LED3 & CT3 & BLK3 & LBS3 & OLC3 & FR3 & ST3 & MI3 & MU3 & WM3).
            pose proof (bytes_at_below _ _ _ _ MI3 (proj1 BLK3)) as BB. rewrite LBS3 in BB. unfold UTOP in BB. apply BB.
            intros E. rewrite E in LBS3. cbn in LBS3. lia. }
          zstep. if_cases KD; zify_cond KD; signed_lits_in KD. { exfalso. lia. }
          do 2 zstep. if_cases KE; zify_cond KE; signed_lits_in KE.
          * do 4 zstep.
            rewrite (SW0 (ret + 0)) by lia. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
            rewrite (Z.mod_small (ret + 0) (2 ^ 64)) by lia. rewrite (SW0 (ret + 0 + x)) by lia.
            if_cases KO; zify_cond KO; [exfalso; clear - KO; lia | clear KO].
            do 12 zstep. if_cases KP; zify_cond KP; [exfalso; rewrite ?unsigned_lit in KP by lia; lia | clear KP].
            do 4 zstep.
            replace (0 <? B + ret) with true by (symmetry; apply Z.ltb_lt; lia).
            replace (x + (B + ret) <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
            cbn [Z.b2z]. rewrite Z.lxor_0_r. ubs_if.
            do 3 zstep.
            replace (ret + 0 + x) with (x + ret) by lia. replace (B + ret + x) with (B + (x + ret)) by lia.
            eapply (U_next _ 0 eof (x + ret) f10); first [exact I2 | lia].
          * zstep. if_cases KZ; zify_cond KZ.
            -- pose proof I2 as I3. destruct I3 as (ed3 & bs3 & CN3 & ED3 & LED3 & CT3 & BLK3 & LBS3 & OLC3 & FR3 & ST3 & MI3 & MU3 & WM3).
               do 6 zstep. ubs_if. do 2 zstep. ubs_if.
               eapply (U_end OLW _ (-1) ret 0); first [exact I2 | lia].
            -- do 4 zstep.
               rewrite (SW0 (ret + 0)) by lia. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
               rewrite (Z.mod_small (ret + 0) (2 ^ 64)) by lia. rewrite (SW0 (ret + 0 + x)) by lia.
               if_cases KO; zify_cond KO; [exfalso; clear - KO; lia | clear KO].
               do 12 zstep. if_cases KP; zify_cond KP; [exfalso; rewrite ?unsigned_lit in KP by lia; lia | clear KP].
               do 4 zstep.
               replace (0 <? B + ret) with true by (symmetry; apply Z.ltb_lt; lia).
               replace (x + (B + ret) <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
               cbn [Z.b2z]. rewrite Z.lxor_0_r. ubs_if.
               do 3 zstep.
               replace (ret + 0 + x) with (x + ret) by lia. replace (B + ret + x) with (B + (x + ret)) by lia.
               eapply (U_next _ 0 eof (x + ret) f10); first [exact I2 | lia].
    Qed.
    (* [comment removed for export] *)
    Lemma U_mid : forall mX n eof ret tz vz x1 x14 x15 x20 x25 x28,
      INV OLW mX -> 0 <= n <= 64 -> 0 <= eof <= 2 -> 0 <= ret -> 4 * ret + 3 * n <= 3 * (i + num) -> 0 <= tz < 128 -> 0 <= vz <= 255 ->
      evt usegs POST (ST 0x191ebc mX x1 (Z_to_bv 64 (Z.land vz 236)) (Z_to_bv 64 ret) (Z_to_bv 64 (B + ret)) (Z_to_bv 64 (B + i)) (Z_to_bv 64 tz) (Z_to_bv 64 vz)
                         (Z_to_bv 64 (C + 4)) (Z_to_bv 64 n) x14
                         x15 (Z_to_bv 64 B64_TABLE) (Z_to_bv 64 C) (Z_to_bv 64 61) (Z_to_bv 64 242) x20 (Z_to_bv 64 224)
                         (Z_to_bv 64 (inl - i)) (Z_to_bv 64 (B + i + 1)) (Z_to_bv 64 64) x25 (Z_to_bv 64 eof) (Z_to_bv 64 (2 ^ 64 - 1 - B64_TABLE)) x28 (Z_to_bv 64 (-1)) (Z_to_bv 64 2) (Z_to_bv 64 255)).
    Proof.
      intros mX n eof ret tz vz x1 x14 x15 x20 x25 x28 I Hn He Hret HI Htz Hvz.
      do 3 zstep.
      assert (Hf : 0 <= Z.b2z (0 <? Z.land (vz + -242) 18446744073709551615) <= 1) by (destruct (0 <? Z.land (vz + -242) 18446744073709551615); cbn; lia).
      if_cases KEOF.
      - eapply (U_tail _ ret n eof _); first [exact I | lia].
      - zstep. if_cases KNB.
        + eapply (U_n _ n eof ret _); first [exact I | lia].
        + do 2 zstep. if_cases K63; zify_cond K63; signed_lits_in K63.
          * pose proof I as I'. open_inv I'.
            ths. do 2 ths. ubs_if. do 2 ths. ubs_if.
            eapply (U_end OLW _ (-1) ret n); first [exact I | lia].
          * pose proof I as I'. open_inv I'.
            do 2 zstep. ubs_if.
            do 5 zstep. if_cases KC; zify_cond KC; signed_lits_in KC.
            { exfalso. change 9223372036854775808 with (2 ^ 63) in KC. rewrite (zb_lxor_pow2_small n 63) in KC by lia.
              replace (n + (C + 4) <? C + 4) with false in KC by (symmetry; apply Z.ltb_ge; lia).
              replace (n + 2 ^ 63 <? 2 ^ 63) with false in KC by (symmetry; apply Z.ltb_ge; lia).
              vm_compute in KC. discriminate KC. }
            zstep.
            pose proof (u8arr_store_ok_n usegs mX (C + 4) ed' n 1 (Z_to_bv 64 (C + 4 + n)) ED ltac:(lia) ltac:(rewrite LED; lia) eq_refl) as SOK.
            zstep. rewrite th_le1_mod.
            pose proof (u8arr_write_bytes usegs mX (C + 4) ed' n [Z_to_bv 8 (tz mod 256)] ED ltac:(lia) ltac:(cbn [length]; rewrite LED; lia)) as ED2.
            assert (LED2 : length (upd_bytes ed' (Z.to_nat n) [Z_to_bv 8 (tz mod 256)]) = 80%nat) by (rewrite upd_bytes_length; [exact LED | cbn [length]; rewrite LED; lia]).
            clear ED.
            store_done.
            assert (SW : bv_swrap 32 (n + 1) = n + 1).
            { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 / 2)%Z with (2^31)%Z.
              rewrite Z.mod_small by lia. lia. }
            rewrite SW.
            lazymatch goal with MIh : mem_inv usegs ?mm |- _ => assert (I2 : INV OLW mm) by close_inv end.
            eapply (U_n _ (n + 1) eof ret _); first [exact I2 | lia].
    Qed.
    (* [comment removed for export] *)
    Lemma U_head : forall n eof ret, HEADP i n eof ret.
    Proof.
      intros n eof ret mX x1 x5 x10 x11 x14 x15 x20 x25 x28 x29 I _ Hn He Hret HI.
      pose proof I as I'. open_inv I'.
      assert (BB : B + Z.of_nat (length bs) <= UTOP) by (eapply bytes_at_below; [exact MI | exact (proj1 BLK) | intro E; rewrite E in LBS; cbn in LBS; lia]).
      unfold UTOP in BB.
      do 2 zstep. if_cases KC; zify_cond KC. { exfalso. rewrite ?land_W64 in KC. rewrite ?Z.mod_small in KC by lia. lia. }
      destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:Hb; [|apply nth_error_None in Hb; lia].
      pose proof (u8arr_read usegs mX B bs i b (Z_to_bv 64 (B + i)) BLK Hb ltac:(lia) eq_refl) as RD.
      do 3 zstep. clear RD.
      destruct (sxb_cases b) as [[SB HB]|[SB [HB EQ]]]; rewrite SB; cbv iota.
      - do 3 zstep. ubs_if. do 2 zstep. ubs_if. eapply (U_end OLW _ (-1) ret n); first [exact I | lia].
      - rewrite EQ.
        pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
        zstep. if_cases KT; zify_cond KT. { exfalso. lia. }
        zstep.
        destruct (b64_table_nth (bv_unsigned b) ltac:(lia)) as [v Hv].
        pose proof (u8ro_read usegs _ B64_TABLE b64_table (bv_unsigned b) v (Z_to_bv 64 (B64_TABLE + bv_unsigned b))
                      (b64_table_at _ MI) Hv ltac:(lia) eq_refl) as RD2.
        zstep. clear RD2.
        pose proof (bv_unsigned_in_range 8 v) as Rv. unfold bv_modulus in Rv. change (2 ^ Z.of_N 8) with 256 in Rv.
        zstep. if_cases K255.
        + do 3 zstep. ubs_if. do 2 zstep. ubs_if. eapply (U_end OLW _ (-1) ret n); first [exact I | lia].
        + do 2 zstep. if_cases K61.
          * (* [comment removed for export] *)
            zstep. if_cases KE0; zify_cond KE0; signed_lits_in KE0.
            -- zstep.
               eapply (U_mid _ n 0 ret (bv_unsigned b) (bv_unsigned v)); first [exact I | lia].
            -- zstep. if_cases KB.
               ++ do 3 zstep. ubs_if. do 2 zstep. ubs_if. eapply (U_end OLW _ (-1) ret n); first [exact I | lia].
               ++ zstep. eapply (U_mid _ n eof ret (bv_unsigned b) (bv_unsigned v)); first [exact I | lia].
          * (* [comment removed for export] *)
            do 2 zstep. if_cases K2; zify_cond K2; signed_lits_in K2.
            -- do 3 zstep. ubs_if. do 2 zstep. ubs_if. eapply (U_end OLW _ (-1) ret n); first [exact I | lia].
            -- do 2 zstep.
               assert (SW : bv_swrap 32 (eof + 1) = eof + 1).
               { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 / 2)%Z with (2^31)%Z.
                 rewrite Z.mod_small by lia. lia. }
               rewrite SW.
               eapply (U_mid _ n (eof + 1) ret (bv_unsigned b) (bv_unsigned v)); first [exact I | lia].
    Qed.
  End Iter.
  Lemma U_loop : forall (k : nat) i, Z.to_nat (inl - i) = k -> forall n eof ret, HEADP i n eof ret.
  Proof.
    induction k as [k IH] using lt_wf_ind; intros i HK n eof ret.
    intros mX x1 x5 x10 x11 x14 x15 x20 x25 x28 x29 I Hi Hn He Hret HI.
    eapply (U_head i Hi); [| exact I | exact Hi | exact Hn | exact He | exact Hret | exact HI].
    intros n' eof' ret'. eapply (IH (Z.to_nat (inl - (i + 1)))); [lia | reflexivity].
  Qed.
  Lemma ectx_split : forall mX nw ed',
    rw_cells usegs mX C (ectx_cells nw ed' ln z64) ->
    rw_cells usegs mX C [C4 nw] /\ u8arr usegs mX (C + 4) ed' /\ rw_cells usegs mX (C + 84) [C4 ln; C4 z64].
  Proof.
    intros mX nw ed' H. unfold ectx_cells in H.
    change [C4 nw; CB 80 ed'; C4 ln; C4 z64] with ([C4 nw] ++ [CB 80 ed'] ++ [C4 ln; C4 z64]) in H.
    apply (proj1 (rw_cells_app usegs mX C _ _)) in H. destruct H as [CN H]. cbn [cells_size csize Nat.add] in H.
    apply (proj1 (rw_cells_app usegs mX (C + Z.of_nat 4) _ _)) in H. destruct H as [ED CT]. cbn [cells_size csize Nat.add] in CT.
    replace (C + Z.of_nat 4 + Z.of_nat 80) with (C + 84) in CT by lia.
    split; [exact CN|]. split; [|exact CT]. apply u8arr_of_rw_cells in ED. exact ED.
  Qed.

  (* [comment removed for export] *)
  Lemma U_flags : forall mX eof x1 x5 x6 x10 x11 x14 x15 x16 x18 x19 x20 x21 x23 x24 x25 x27 x28 x29 x30 x31,
    INV OLW mX -> 0 < inl -> 0 <= eof <= 2 ->
    evt usegs POST (ST 0x191e10 mX x1 x5 x6 (Z_to_bv 64 B) (Z_to_bv 64 B) x10 x11 (Z_to_bv 64 (C + 4)) (Z_to_bv 64 num) x14 x15 x16 (Z_to_bv 64 C) x18 x19 x20
                       x21 (Z_to_bv 64 inl) x23 x24 x25 (Z_to_bv 64 eof) x27 x28 x29 x30 x31).
  Proof.
    intros mX eof x1 x5 x6 x10 x11 x14 x15 x16 x18 x19 x20 x21 x23 x24 x25 x27 x28 x29 x30 x31 I Hinl He.
    open_inv I.
    apply (th_cells_congr usegs mX (C + 84) _ [C4 ln; C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) in CT;
      [| reflexivity | reflexivity | cbn; tauto].
    do 3 ths. th_if_lit.
    do 3 ths.
    zstep. if_cases KI; zify_cond KI; signed_lits_in KI. { exfalso. lia. }
    do 8 zstep.
    apply (th_cells_congr usegs _ (C + 84) _ [C4 ln; C4 z64]) in CT; [| reflexivity | reflexivity | cbn; tauto].
    lazymatch goal with MIh : mem_inv usegs ?mm |- _ => assert (I2 : INV OLW mm) by close_inv end.
    replace (Z_to_bv 64 B) with (Z_to_bv 64 (B + 0)) by (f_equal; lia).
    replace (Z_to_bv 64 inl) with (Z_to_bv 64 (inl - 0)) by (f_equal; lia).
    eapply (U_loop (Z.to_nat (inl - 0)) 0 eq_refl num eof 0); first [exact I2 | lia].
  Qed.
  (* [comment removed for export] *)
  Lemma U_join : forall mX eof x1 x5 x6 x10 x11 x15 x16 x18 x19 x20 x21 x23 x24 x25 x27 x28 x29 x30 x31,
    INV OLW mX -> 0 <= eof <= 2 ->
    evt usegs POST (ST 0x191e0c mX x1 x5 x6 (Z_to_bv 64 B) (Z_to_bv 64 B) x10 x11 (Z_to_bv 64 (C + 4)) (Z_to_bv 64 num) (Z_to_bv 64 61) x15 x16 (Z_to_bv 64 C) x18 x19 x20
                       x21 (Z_to_bv 64 inl) x23 x24 x25 (Z_to_bv 64 eof) x27 x28 x29 x30 x31).
  Proof.
    intros mX eof x1 x5 x6 x10 x11 x15 x16 x18 x19 x20 x21 x23 x24 x25 x27 x28 x29 x30 x31 I He.
    zstep. if_cases KI; zify_cond KI.
    - pose proof I as I0. open_inv I0. do 5 zstep. ubs_if. do 2 zstep. ubs_if.
      eapply (U_end OLW _ 0 0 num); first [exact I | lia].
    - eapply (U_flags _ eof); first [exact I | lia].
  Qed.

  Lemma U_eof0 : forall mX x1 x5 x6 x10 x11 x14 x15 x16 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    INV OLW mX ->
    evt usegs POST (ST 0x191e28 mX x1 x5 x6 (Z_to_bv 64 B) (Z_to_bv 64 B) x10 x11 (Z_to_bv 64 (C + 4)) (Z_to_bv 64 num) x14 x15 x16 (Z_to_bv 64 C) x18 x19 x20
                       x21 (Z_to_bv 64 inl) x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros mX x1 x5 x6 x10 x11 x14 x15 x16 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 I.
    do 2 zstep. if_cases KI; zify_cond KI.
    - eapply (U_flags _ 0); first [exact I | lia].
    - pose proof I as I'. open_inv I'.
      do 5 ths. ubs_if. do 2 ths. ubs_if. eapply (U_end OLW _ 0 0 num); first [exact I | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma dupdate_body : forall ed bs t0 t1 t2 a5 a6 a7 t3 t4 t5 t6,
    rw_cells usegs m C (ectx_cells (Z_to_bv 64 num) ed ln z64) -> length ed = 80%nat ->
    rw_cells usegs m B [CB N bs] -> rw_cells usegs m OL [C4 old] -> stk usegs m lo SP -> mem_inv usegs m ->
    evt usegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 C) (Z_to_bv 64 B) OLW (Z_to_bv 64 B) (Z_to_bv 64 inl) a5 a6 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x191d64) fc None m (seg_rom usegs)).
  Proof.
    intros ed bs t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 CTX LED BLK OLC ST MI.
    assert (SW32 : forall z, - 2 ^ 31 <= z < 2 ^ 31 -> bv_swrap 32 z = z).
    { intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 / 2)%Z with (2^31)%Z.
      rewrite Z.mod_small by lia. lia. }
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl usegs m) as WM.
    destruct (ectx_split _ _ _ CTX) as (CN & ED & CT). clear CTX.
    pose proof (rw_cells_CB_length usegs _ _ _ _ BLK) as LBS. apply u8arr_of_rw_cells in BLK.
    th_frame 112%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
    do 16 ths. ubs_if. do 3 ths. ubs_if. do 6 ths.
    (* [comment removed for export] *)
    lazymatch goal with MIh : mem_inv usegs ?mm |- _ => assert (I : INV OLW mm) by close_inv end.
    zstep. rewrite (t_sx32_small num) by lia. if_cases KN; zify_cond KN; signed_lits_in KN.
    - eapply (U_eof0 _ _); exact I.
    - do 3 zstep. if_cases KU; zify_cond KU.
      { exfalso. rewrite ?zb_lxor_ones in KU by lia; rewrite ?SW32 in KU by lia; rewrite ?land_W64 in KU;
          rewrite ?Z.mod_small in KU by lia; rewrite ?unsigned_lit in KU by lia; lia. }
      rewrite (SW32 (num + -1)) by lia.
      destruct (nth_error ed (Z.to_nat (num - 1))) as [b1|] eqn:Hb1; [|apply nth_error_None in Hb1; lia].
      pose proof (u8arr_read usegs _ (C + 4) ed (num - 1) b1 (Z_to_bv 64 (C + 4 + (num + -1))) ED Hb1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      do 2 zstep. clear RD.
      do 2 zstep. if_cases KP.
      + eapply (U_eof0 _ _); exact I.
      + do 2 zstep. if_cases K1; zify_cond K1.
        * eapply (U_join _ 1); first [exact I | lia].
        * do 2 zstep. if_cases KU2; zify_cond KU2.
          { exfalso. rewrite ?zb_lxor_ones in KU2 by lia; rewrite ?SW32 in KU2 by lia; rewrite ?land_W64 in KU2;
              rewrite ?Z.mod_small in KU2 by lia; rewrite ?unsigned_lit in KU2 by lia; lia. }
          rewrite (SW32 (num + -2)) by lia.
          destruct (nth_error ed (Z.to_nat (num - 2))) as [b2|] eqn:Hb2; [|apply nth_error_None in Hb2; lia].
          pose proof (u8arr_read usegs _ (C + 4) ed (num - 2) b2 (Z_to_bv 64 (C + 4 + (num + -2))) ED Hb2 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
          do 2 zstep. clear RD.
          do 3 zstep.
          set (e := Z.b2z (Z.land (bv_unsigned b2 + -61) 18446744073709551615 <? 1) + 1).
          assert (He : 1 <= e <= 2) by (unfold e; destruct (Z.land (bv_unsigned b2 + -61) 18446744073709551615 <? 1); cbn [Z.b2z]; lia).
          rewrite (SW32 e) by lia. clearbody e.
          eapply (U_join _ e); first [exact I | lia].
  Qed.
End Proofs.

(* [comment removed for export] *)
Definition W4_decode_update_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (C B OL : Z) (N : nat) (inl num : Z) (ln old : word) (ed bs : list byte) (lo : Z),
    a0 = Z_to_bv 64 C -> a1 = Z_to_bv 64 B -> a2 = Z_to_bv 64 OL -> a3 = Z_to_bv 64 B -> a4 = Z_to_bv 64 inl ->
    0 < C -> C mod 4 = 0 -> 0 < B -> 0 < OL -> OL mod 4 = 0 ->
    rw_cells usegs m C (ectx_cells (Z_to_bv 64 num) ed ln z64) -> length ed = 80%nat -> 0 <= num <= 64 ->
    rw_cells usegs m B [CB N bs] -> 0 <= inl <= Z.of_nat N -> inl < 2 ^ 31 -> 3 * (inl + num) <= 4 * Z.of_nat N ->
    rw_cells usegs m OL [C4 old] ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 160 ->
    (C + 92 <= B \/ B + Z.of_nat N <= C) -> (C + 92 <= OL \/ OL + 4 <= C) -> (B + Z.of_nat N <= OL \/ OL + 4 <= B) ->
    (C + 92 <= lo \/ bv_unsigned sp <= C) -> (B + Z.of_nat N <= lo \/ bv_unsigned sp <= B) -> (OL + 4 <= lo \/ bv_unsigned sp <= OL) ->
    mem_inv usegs m ->
    evt usegs (dupdate_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc C B OL N inl num ln lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x191d64) fc None m (seg_rom usegs)).

Theorem W4_decode_update_proof : W4_decode_update_stmt.
Proof.
  unfold W4_decode_update_stmt. intros until lo.
  intros -> -> -> -> -> HC HCA HB HO HOA CTX LED HN BLK HI HI31 HROOM OLC ST LO0 LO S1 S2 S3 S4 S5 S6 MI.
  pose proof (rw_cells_bound _ _ _ _ CTX) as CB. unfold ectx_cells in CB. cbn [cells_size csize Nat.add] in CB.
  pose proof (rw_cells_bound _ _ _ _ BLK) as BB. cbn [cells_size csize Nat.add] in BB.
  pose proof (rw_cells_bound _ _ _ _ OLC) as OB. cbn [cells_size csize Nat.add] in OB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  eapply (dupdate_body ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m C B OL N inl num ln old lo); try eassumption; lia.
Qed.

