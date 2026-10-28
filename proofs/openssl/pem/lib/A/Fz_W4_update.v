(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac Arr SFModel.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit Str_cpy.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree R_cache_defs Fz_kit I_ut Fz_chk Fz_fkit Fz_W4_kit Fz_W4_defs Fz_ukit Fz_W4_block.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Notation z64 := (Z_to_bv 64 0) (only parsing).

Definition dupdate_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (C B OL : Z) (N : nat) (inl num : Z) (ln : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (rv ret num' : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (ed' bs' : list byte) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 192, bv_unsigned sp); (C, C + 84); (B, B + Z.of_nat N); (OL, OL + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ (-1 <= rv <= 1 /\ 0 <= ret /\ 0 <= num' <= 64 /\ 4 * ret + 3 * num' <= 3 * (inl + num))
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' C (ectx_cells (Z_to_bv 64 num') ed' ln z64) /\ length ed' = 80%nat
    /\ rw_cells asegs m' B [CB N bs']
    /\ rw_cells asegs m' OL [C4 (Z_to_bv 64 ret)].

Section Proofs.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (C B OL : Z) (N : nat) (inl num : Z) (ln old : word) (lo : Z).
  Notation SP := (bv_unsigned sp).
  Notation W := [(bv_unsigned sp - 192, bv_unsigned sp); (C, C + 84); (B, B + Z.of_nat N); (OL, OL + 4)]%Z.
  Hypothesis AB : 0 <= num <= 64 /\ 0 <= inl <= Z.of_nat N /\ inl < 2 ^ 31 /\ 3 * (inl + num) <= 4 * Z.of_nat N
                  /\ 0 < C /\ C + 92 <= lo /\ 0 < B /\ B + Z.of_nat N <= lo /\ 0 < OL /\ OL + 4 <= 2 ^ 47
                  /\ 0x10007fff8000 <= lo /\ lo <= SP - 192 /\ SP <= 2 ^ 47.
  Hypothesis OLO : OL + 4 <= lo \/ SP <= OL.
  Hypothesis SEP_CB : C + 92 <= B \/ B + Z.of_nat N <= C.
  Hypothesis SEP_CO : C + 92 <= OL \/ OL + 4 <= C.
  Hypothesis SEP_BO : B + Z.of_nat N <= OL \/ OL + 4 <= B.
  Hypothesis CAL : C mod 8 = 0.
  Hypothesis OAL : OL mod 4 = 0.
  Hypothesis TAL : 672160 mod 8 = 0.
  Hypothesis ACC_C : acc asegs m C 92.
  Hypothesis ACC_BUF : acc asegs m B (Z.of_nat N).
  Hypothesis ACC_O : acc asegs m OL 4.
  Hypothesis ACC_B : acc asegs m 672160 128.
  Hypothesis UT : img_untouched m.
  (* [comment removed for export] *)
  Hypothesis HWS : sh_fp W.
  Hypothesis HWU : ut_fp W.
  Hypothesis BIMr : forall r, 0 <= r <= Z.of_nat N -> B + r + Z.of_nat (N - Z.to_nat r) <= 0x10000 \/ 0xbc6000 <= B + r.
  Hypothesis BSHr : forall r, 0 <= r <= Z.of_nat N -> B + r + Z.of_nat (N - Z.to_nat r) <= 0x7fff8000 \/ 0x10007fff8000 <= B + r.
  Hypothesis SHCX : forall mX, munch W m mX -> ro_cells asegs mX 6736696 [C8 (Z_to_bv 64 2147450880)].

  Notation POST := (dupdate_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc C B OL N inl num ln lo m).
  (* [comment removed for export] *)
  Notation ST pc mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -128)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  Notation SHBv := (Z_to_bv 64 2147450880).
  Notation TBL := (Z_to_bv 64 672160).
  Notation CW := (Z_to_bv 64 C).
  Notation DW := (Z_to_bv 64 (C + 4)).
  Notation OLW := (Z_to_bv 64 OL).
  Notation SHW := (Z_to_bv 64 (C ≫ 3 + 2147450880)).

  (* [comment removed for export] *)
  Definition INV (w0 w1 w2 : word) (mX : mem) : Prop :=
    exists (ed' bs : list byte),
      rw_cells asegs mX C [C4 (Z_to_bv 64 num)] /\ u8arr asegs mX (C + 4) ed' /\ length ed' = 80%nat
      /\ rw_cells asegs mX (C + 84) [C4 ln; C4 z64]
      /\ u8arr asegs mX B bs /\ length bs = N
      /\ rw_cells asegs mX OL [C4 old]
      /\ rw_cells asegs mX (SP + -128) [C8 w0; C8 w1; C8 w2; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ stk asegs mX lo (SP + -128)
      /\ mem_inv asegs mX /\ munch W m mX /\ wmono asegs m mX.

  Ltac open_inv I := destruct I as (ed' & bs & CN & ED & LED & CT & BLK & LBS & OLC & FR & ST & MI & MU & WM).
  Ltac close_inv := do 2 eexists; do 11 (split; [eassumption|]); eassumption.
  (* [comment removed for export] *)
  Ltac prep I := let I' := fresh "Ic" in pose proof I as I'; open_inv I'.
  (* [comment removed for export] *)
  Lemma ectx_join : forall mX nw ed', length ed' = 80%nat ->
    rw_cells asegs mX C [C4 nw] -> u8arr asegs mX (C + 4) ed' -> rw_cells asegs mX (C + 84) [C4 ln; C4 z64] ->
    rw_cells asegs mX C (ectx_cells nw ed' ln z64).
  Proof.
    intros mX nw ed' L CN ED CT. apply rw_cells_of_u8arr in ED. rewrite L in ED. unfold ectx_cells.
    change [C4 nw; CB 80 ed'; C4 ln; C4 z64] with ([C4 nw] ++ [CB 80 ed'] ++ [C4 ln; C4 z64]).
    apply (proj2 (rw_cells_app mX C _ _)). split; [exact CN|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app mX (C + Z.of_nat 4) _ _)). split; [exact ED|]. cbn [cells_size csize Nat.add].
    replace (C + Z.of_nat 4 + Z.of_nat 80) with (C + 84) by lia. exact CT.
  Qed.
  Lemma ectx_split : forall mX nw ed',
    rw_cells asegs mX C (ectx_cells nw ed' ln z64) ->
    rw_cells asegs mX C [C4 nw] /\ u8arr asegs mX (C + 4) ed' /\ rw_cells asegs mX (C + 84) [C4 ln; C4 z64].
  Proof.
    intros mX nw ed' H. unfold ectx_cells in H.
    change [C4 nw; CB 80 ed'; C4 ln; C4 z64] with ([C4 nw] ++ [CB 80 ed'] ++ [C4 ln; C4 z64]) in H.
    apply (proj1 (rw_cells_app mX C _ _)) in H. destruct H as [CN H]. cbn [cells_size csize Nat.add] in H.
    apply (proj1 (rw_cells_app mX (C + Z.of_nat 4) _ _)) in H. destruct H as [ED CT]. cbn [cells_size csize Nat.add] in CT.
    replace (C + Z.of_nat 4 + Z.of_nat 80) with (C + 84) in CT by lia.
    split; [exact CN|]. split; [|exact CT]. apply u8arr_of_rw_cells in ED. exact ED.
  Qed.

  (* [comment removed for export] *)
  Lemma U_end : forall w0 w1 w2 mX rv ret n x1 x5 x6 x10 x11 x12 x14 x15 x16 x17 x18 x20 x22 x23 x24 x27 x28 x29 x30 x31,
    INV w0 w1 w2 mX -> -1 <= rv <= 1 -> 0 <= ret -> 0 <= n <= 64 -> 4 * ret + 3 * n <= 3 * (inl + num) ->
    evt asegs POST (ST 0x31f7cc mX x1 x5 x6 (Z_to_bv 64 rv) CW x10 x11 x12 (Z_to_bv 64 n) x14 x15 x16 x17 x18 SHW x20 (Z_to_bv 64 ret) x22 x23 x24
                       OLW SHBv x27 x28 x29 x30 x31).
  Proof.
    intros w0 w1 w2 mX rv ret n x1 x5 x6 x10 x11 x12 x14 x15 x16 x17 x18 x20 x22 x23 x24 x27 x28 x29 x30 x31 I Hrv Hret Hn HI.
    open_inv I.
    chk_pass ACC_O OL 4 0x31f7dc 10 11. zstep.
    zstep. zstep. th_if_lit. zstep.
    zstep.
    do 14 zstep.
    release_frame FR ST (bv_unsigned sp).
    pose proof (ectx_join _ _ _ LED CN ED CT) as CTX.
    apply rw_cells_of_u8arr in BLK. rewrite LBS in BLK.
    zstep. apply evt_done. exists rv, ret, n. do 14 eexists. exists ed', bs. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [lia|]. split; [exact ST|].
    split; [exact CTX|]. split; [exact LED|]. split; [exact BLK | exact OLC].
  Qed.

  (* [comment removed for export] *)
  Lemma U_984 : forall w0 w1 w2 mX ret x eof sf x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x27 x28 x29 x30 x31,
    INV w0 w1 w2 mX -> 0 <= ret -> 0 <= x -> 4 * (ret + x) <= 3 * (inl + num) -> 0 <= eof <= 2 -> 0 <= sf <= 1 ->
    evt asegs POST (ST 0x31f77c mX x1 x5 x6 x7 CW (Z_to_bv 64 x) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sf) SHW x20 (Z_to_bv 64 ret) x22 x23
                       (Z_to_bv 64 eof) OLW SHBv x27 x28 x29 x30 x31).
  Proof.
    intros w0 w1 w2 mX ret x eof sf x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x27 x28 x29 x30 x31 I Hret Hx HI He Hsf.
    zstep. zstep. if_cases KS; zify_cond KS.
    - do 3 zstep.
      match goal with |- context [Z.b2z ?bb] => destruct bb end; cbn [Z.b2z]; eapply (U_end _ _ _ _ _ (x + ret) 0); first [exact I | lia].
    - do 3 zstep. eapply (U_end _ _ _ _ 0 (x + ret) 0); first [exact I | lia].
  Qed.

  (* [comment removed for export] *)
  Ltac call_dblock CN ED LED CT BLK LBS MU STK ret n eof :=
    let RETN := fresh "RETN" in
    assert (RETN : 0 <= ret /\ ret + 3 * (n / 4) <= Z.of_nat N /\ 0 <= n / 4) by lia;
    let CTXR := fresh "CTXR" in
    pose proof (proj1 (ectx_join _ _ _ LED CN ED CT) : ro_cells asegs _ C (ectx_cells (Z_to_bv 64 num) _ ln z64)) as CTXR;
    let BA := fresh "BA" in let BB := fresh "BB" in
    apply rw_cells_of_u8arr in BLK; rewrite LBS in BLK;
    destruct (rw_cells_CB_split_at asegs _ B N _ (Z.to_nat ret) ltac:(lia) BLK) as [BA BB]; clear BLK;
    rewrite Z2Nat.id in BB by lia;
    tcall (dblock_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C (B + ret) (N - Z.to_nat ret)%nat n eof (Z_to_bv 64 num) ln _ _ lo);
    [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | exact CTXR | exact LED | lia | exact CAL | lia
    | exact (acc_munch_sh _ m _ _ _ ACC_C MU HWS ltac:(lia) ltac:(lia))
    | exact BB | clear - AB RETN; lia | clear - AB RETN; lia
    | eapply (acc_sub asegs _ B (Z.of_nat N)); [exact (acc_munch_sh _ m _ _ _ ACC_BUF MU HWS ltac:(lia) ltac:(lia)) | clear - RETN; lia | clear - RETN; lia]
    | apply BIMr; clear - AB RETN; lia | apply BSHr; clear - AB RETN; lia | clear - AB SEP_CB RETN; lia
    | lia | clear - RETN; lia | lia
    | exact (acc_munch_sh _ m _ _ _ ACC_B MU HWS ltac:(lia) ltac:(lia))
    | exact (ut_munch _ m _ UT MU HWU)
    | unfold g_shadow_memory_dynamic_address, SHB; exact (SHCX _ MU)
    | exact STK | lia | lia | lia | assumption | ]
    || fail "call_dblock"; clear RETN.

  (* [comment removed for export] *)
  Ltac rejoin_block BA POST ret :=
    replace (B + ret) with (B + Z.of_nat (Z.to_nat ret)) in POST by lia;
    let BLK' := fresh "BLK" in let LB' := fresh "LBS" in
    pose proof (rw_cells_CB_join asegs _ B _ _ _ _ BA POST) as BLK';
    replace (Z.to_nat ret + (N - Z.to_nat ret))%nat with N in BLK' by lia;
    pose proof (rw_cells_CB_length asegs _ _ _ _ BLK') as LB';
    apply u8arr_of_rw_cells in BLK'; clear BA POST.

  (* [comment removed for export] *)
  Lemma U_tail : forall w0 mX ret n eof z x1 x5 x6 x7 x10 x11 x12 x14 x15 x19 x20 x22 x23 x25 x27 x28 x29 x30 x31,
    INV w0 OLW SHW mX -> 0 <= ret -> 0 <= n <= 64 -> 4 * ret + 3 * n <= 3 * (inl + num) -> 0 <= eof <= 2 -> 0 <= z <= 255 ->
    evt asegs POST (ST 0x31f730 mX x1 x5 x6 x7 CW x10 x11 x12 (Z_to_bv 64 n) x14 x15 DW (Z_to_bv 64 (B + ret)) (Z_to_bv 64 z) x19 x20 (Z_to_bv 64 ret) x22 x23
                       (Z_to_bv 64 eof) x25 SHBv x27 x28 x29 x30 x31).
  Proof.
    intros w0 mX ret n eof z x1 x5 x6 x7 x10 x11 x12 x14 x15 x19 x20 x22 x23 x25 x27 x28 x29 x30 x31 I Hret Hn HI He Hz.
    pose proof (Z.mul_div_le n 4 ltac:(lia)) as HD. pose proof (Z.div_pos n 4 ltac:(lia) ltac:(lia)) as HD0.
    pose proof I as I'. open_inv I'. rename ST into ST0.
    zstep. if_cases K0; zify_cond K0; signed_lits_in K0.
    - (* [comment removed for export] *)
      do 3 zstep. zstep. if_cases KF; zify_cond KF.
      + zstep. if_cases KZ; zify_cond KZ.
        * do 3 zstep. match goal with |- context [Z.b2z ?bb] => destruct bb end; cbn [Z.b2z]; eapply (U_end _ _ _ _ _ ret 0); first [exact I | lia].
        * do 2 zstep. eapply (U_end _ _ _ _ 1 ret n); first [exact I | lia].
      + zstep. eapply (U_end _ _ _ _ 0 ret n); first [exact I | lia].
    - do 4 zstep.
      match goal with |- context [Z.b2z ?bb] => destruct bb eqn:SEOF end; cbn [Z.b2z].
      + (* [comment removed for export] *)
        zstep. zstep. if_cases K3; zify_cond K3.
        * (* [comment removed for export] *)
          do 5 zstep.
          call_dblock CN ED LED CT BLK LBS MU ST0 ret n eof.
          rejoin_block BA POST ret. clear PC1.
          lazymatch goal with MIh : mem_inv asegs ?mm |- _ => assert (I2 : INV w0 OLW SHW mm) by close_inv end.
          clear CN ED CT OLC FR PC0 MI0 MU WM.
          cbv beta delta [mkR].
          destruct PC as [-> | PC].
          -- zstep. zstep. th_if_lit. do 2 zstep.
             eapply (U_end _ _ _ _ (-1) ret 0); first [exact I2 | lia].
          -- zstep. zstep. if_cases KD; zify_cond KD; signed_lits_in KD. { exfalso. lia. }
             zstep. if_cases KE; zify_cond KE; signed_lits_in KE.
             ++ eapply (U_984 _ _ _ _ ret x eof 1); first [exact I2 | lia].
             ++ zstep. if_cases KZ; zify_cond KZ.
                ** do 2 zstep. eapply (U_end _ _ _ _ (-1) ret 0); first [exact I2 | lia].
                ** eapply (U_984 _ _ _ _ ret x eof 1); first [exact I2 | lia].
        * (* [comment removed for export] *)
          do 3 zstep.
          replace (Z_to_bv 64 18446744073709551615) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
          eapply (U_end _ _ _ _ (-1) ret n); first [exact I | lia].
      + (* [comment removed for export] *)
        zstep. zstep. if_cases K3; zify_cond K3.
        * do 5 zstep.
          call_dblock CN ED LED CT BLK LBS MU ST0 ret n eof.
          rejoin_block BA POST ret. clear PC1.
          lazymatch goal with MIh : mem_inv asegs ?mm |- _ => assert (I2 : INV w0 OLW SHW mm) by close_inv end.
          clear CN ED CT OLC FR PC0 MI0 MU WM.
          cbv beta delta [mkR].
          destruct PC as [-> | PC].
          -- zstep. zstep. th_if_lit. do 2 zstep.
             eapply (U_end _ _ _ _ (-1) ret 0); first [exact I2 | lia].
          -- zstep. zstep. if_cases KD; zify_cond KD; signed_lits_in KD. { exfalso. lia. }
             zstep. if_cases KE; zify_cond KE; signed_lits_in KE.
             ++ eapply (U_984 _ _ _ _ ret x eof 0); first [exact I2 | lia].
             ++ zstep. if_cases KZ; zify_cond KZ.
                ** do 2 zstep. eapply (U_end _ _ _ _ (-1) ret 0); first [exact I2 | lia].
                ** eapply (U_984 _ _ _ _ ret x eof 0); first [exact I2 | lia].
        * do 3 zstep. eapply (U_end _ _ _ _ 1 ret n); first [exact I | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma U_978 : forall w0 mX ret x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x23 x24 x25 x27 x28 x29 x30 x31,
    INV w0 OLW SHW mX -> 0 <= ret -> 4 * ret <= 3 * (inl + num) ->
    evt asegs POST (ST 0x31f790 mX x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 SHBv (Z_to_bv 64 ret) x22 x23 x24 x25 CW x27 x28 x29 x30 x31).
  Proof.
    intros w0 mX ret x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x23 x24 x25 x27 x28 x29 x30 x31 I Hret HI.
    pose proof I as I'. open_inv I'.
    do 7 zstep. eapply (U_end _ _ _ _ (-1) ret 0); first [exact I | lia].
  Qed.

  (* [comment removed for export] *)
  Definition HEADP (i n eof ret : Z) : Prop :=
    forall w0 mX x1 x5 x6 x7 x10 x11 x12 x14 x15 x18,
      INV w0 OLW SHW mX -> 0 <= i < inl -> 0 <= n <= 64 -> 0 <= eof <= 2 -> 0 <= ret -> 4 * ret + 3 * n <= 3 * (i + num) ->
      evt asegs POST (ST 0x31f5f4 mX x1 x5 x6 x7 CW x10 x11 x12 (Z_to_bv 64 n) x14 x15 DW (Z_to_bv 64 (B + ret)) x18 (Z_to_bv 64 224) (Z_to_bv 64 64)
                         (Z_to_bv 64 ret) (Z_to_bv 64 (inl - i)) (Z_to_bv 64 (B + i)) (Z_to_bv 64 eof) (Z_to_bv 64 (B + i)) SHBv TBL
                         (Z_to_bv 64 255) (Z_to_bv 64 61) (Z_to_bv 64 2) (Z_to_bv 64 242)).

  Section Iter.
    Variable i : Z.
    Hypothesis Hi : 0 <= i < inl.
    Hypothesis NEXT : forall n eof ret, HEADP (i + 1) n eof ret.

    (* [comment removed for export] *)
    Notation IT pc mX x1 x5 x6 x7 x10 x11 x12 x14 x15 x18 n eof ret :=
      (ST pc mX x1 x5 x6 x7 CW x10 x11 x12 (Z_to_bv 64 n) x14 x15 DW (Z_to_bv 64 (B + ret)) x18 (Z_to_bv 64 224) (Z_to_bv 64 64)
          (Z_to_bv 64 ret) (Z_to_bv 64 (inl - i)) (Z_to_bv 64 (B + i)) (Z_to_bv 64 eof) (Z_to_bv 64 (B + i)) SHBv TBL
          (Z_to_bv 64 255) (Z_to_bv 64 61) (Z_to_bv 64 2) (Z_to_bv 64 242)).

    (* [comment removed for export] *)
    Lemma U_next : forall w0 mX n eof ret z x1 x5 x6 x7 x10 x11 x12 x14 x15,
      INV w0 OLW SHW mX -> 0 <= n <= 64 -> 0 <= eof <= 2 -> 0 <= ret -> 4 * ret + 3 * n <= 3 * (i + 1 + num) -> 0 <= z <= 255 ->
      evt asegs POST (IT 0x31f6dc mX x1 x5 x6 x7 x10 x11 x12 x14 x15 (Z_to_bv 64 z) n eof ret).
    Proof.
      intros w0 mX n eof ret z x1 x5 x6 x7 x10 x11 x12 x14 x15 I Hn He Hret HI Hz.
      do 3 zstep.
      assert (SW : bv_swrap 32 (inl - i + -1) = inl - (i + 1)) by (rewrite ubs_sw32 by lia; lia).
      rewrite ?SW. try replace (inl - i + -1) with (inl - (i + 1)) by lia. replace (B + i + 1) with (B + (i + 1)) by lia.
      zstep. if_cases KL; zify_cond KL.
      - eapply (NEXT n eof ret); first [exact I | lia].
      - zstep. eapply (U_tail _ _ ret n eof z); first [exact I | lia].
    Qed.

    (* [comment removed for export] *)
    Lemma U_828 : forall w0 mX eof ret x z x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
      INV w0 OLW SHW mX -> 0 <= eof <= 2 -> 0 <= ret -> 0 <= x -> 4 * (ret + x) <= 3 * (i + 1 + num) -> 0 <= z <= 255 ->
      evt asegs POST (ST 0x31f6ac mX x1 x5 x6 x7 (Z_to_bv 64 (B + ret)) (Z_to_bv 64 x) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 z) DW SHBv (Z_to_bv 64 ret)
                         (Z_to_bv 64 (inl - i)) (Z_to_bv 64 (B + i)) (Z_to_bv 64 eof) (Z_to_bv 64 (B + i)) CW TBL x28 x29 x30 x31).
    Proof.
      intros w0 mX eof ret x z x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 I He Hret Hx HI Hz.
      do 12 zstep.
      try replace (x + (B + ret)) with (B + (ret + x)) by lia. try replace (B + ret + x) with (B + (ret + x)) by lia.
      try replace (x + ret) with (ret + x) by lia.
      eapply (U_next _ _ 0 eof (ret + x) z); first [exact I | lia].
    Qed.

    (* [comment removed for export] *)
    Lemma U_4d0 : forall w0 mX n eof ret z x1 x5 x6 x7 x10 x11 x12 x14 x15,
      INV w0 OLW SHW mX -> 0 <= n <= 64 -> 0 <= eof <= 2 -> 0 <= ret -> 4 * ret + 3 * n <= 3 * (i + 1 + num) -> 0 <= z <= 255 ->
      evt asegs POST (IT 0x31f674 mX x1 x5 x6 x7 x10 x11 x12 x14 x15 (Z_to_bv 64 z) n eof ret).
    Proof.
      intros w0 mX n eof ret z x1 x5 x6 x7 x10 x11 x12 x14 x15 I Hn He Hret HI Hz.
      zstep. if_cases K64; zify_cond K64.
      - eapply (U_next _ _ n eof ret z); first [exact I | lia].
      - pose proof I as I'. open_inv I'. rename ST into ST0.
        do 10 zstep.
        call_dblock CN ED LED CT BLK LBS MU ST0 ret 64 eof.
        rejoin_block BA POST ret. clear PC1.
        lazymatch goal with MIh : mem_inv asegs ?mm |- _ => assert (I2 : INV w0 OLW SHW mm) by close_inv end.
        clear CN ED CT OLC FR PC0 MI0 MU WM.
        cbv beta delta [mkR].
        destruct PC as [-> | PC].
        + zstep. th_if_lit.
          eapply (U_978 _ _ ret); first [exact I2 | lia].
        + zstep. if_cases KD; zify_cond KD; signed_lits_in KD. { exfalso. lia. }
          zstep. if_cases KE; zify_cond KE; signed_lits_in KE.
          * eapply (U_828 _ _ eof ret x z); first [exact I2 | lia].
          * zstep. if_cases KZ; zify_cond KZ.
            -- eapply (U_978 _ _ ret); first [exact I2 | lia].
            -- eapply (U_828 _ _ eof ret x z); first [exact I2 | lia].
    Qed.

    (* [comment removed for export] *)
    Lemma U_4a8 : forall w0 mX n eof ret t z x1 x5 x6 x12 x14 x15,
      INV w0 OLW SHW mX -> 0 <= n <= 64 -> 0 <= eof <= 2 -> 0 <= ret -> 4 * ret + 3 * n <= 3 * (i + num) -> 0 <= t < 128 -> 0 <= z <= 255 ->
      evt asegs POST (IT 0x31f64c mX x1 x5 x6 (Z_to_bv 64 (-1)) (Z_to_bv 64 (Z.land z 236)) (Z_to_bv 64 t) x12 x14 x15 (Z_to_bv 64 z) n eof ret).
    Proof.
      intros w0 mX n eof ret t z x1 x5 x6 x12 x14 x15 I Hn He Hret HI Ht Hz.
      zstep. if_cases KWS.
      - eapply (U_4d0 _ _ n eof ret z); first [exact I | lia].
      - do 2 zstep. if_cases K63; zify_cond K63; signed_lits_in K63.
        + prep I. do 3 zstep. eapply (U_end _ _ _ _ (-1) ret n); first [exact I | lia].
        + prep I.
          zstep.
          do 3 zstep. zstep. th_if_lit.
          zstep. rewrite ?(ubs_sw32 (n + 1)) by lia.
          pose proof (u8arr_store_ok_n asegs _ (C + 4) ed' n 1 (Z_to_bv 64 (n + (C + 4))) ED ltac:(lia) ltac:(rewrite LED; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
          zstep. rewrite th_le1_mod.
          pose proof (u8arr_write_bytes asegs _ (C + 4) ed' n [Z_to_bv 8 (t mod 256)] ED ltac:(lia) ltac:(cbn [length]; rewrite LED; lia)) as ED2.
          assert (LED2 : length (upd_bytes ed' (Z.to_nat n) [Z_to_bv 8 (t mod 256)]) = 80%nat) by (rewrite upd_bytes_length; [exact LED | cbn [length]; rewrite LED; lia]).
          replace (C + 4 + n) with (n + (C + 4)) in ED2 by lia.
          clear ED.
          store_done.
          lazymatch goal with MIh : mem_inv asegs ?mm |- _ => assert (I2 : INV w0 OLW SHW mm) by close_inv end.
          eapply (U_4d0 _ _ (n + 1) eof ret z); first [exact I2 | lia].
    Qed.

    (* [comment removed for export] *)
    Lemma U_780 : forall w0 mX n eof ret t z x1 x5 x6 x12 x14 x15,
      INV w0 OLW SHW mX -> 0 <= n <= 64 -> 0 <= eof <= 3 -> 0 <= ret -> 4 * ret + 3 * n <= 3 * (i + num) -> 0 <= t < 128 -> 0 <= z <= 255 ->
      evt asegs POST (IT 0x31f644 mX x1 x5 x6 (Z_to_bv 64 (-1)) (Z_to_bv 64 (Z.land z 236)) (Z_to_bv 64 t) x12 x14 x15 (Z_to_bv 64 z) n eof ret).
    Proof.
      intros w0 mX n eof ret t z x1 x5 x6 x12 x14 x15 I Hn He Hret HI Ht Hz.
      zstep. if_cases K2; zify_cond K2; signed_lits_in K2.
      - prep I. do 3 zstep. eapply (U_end _ _ _ _ (-1) ret n); first [exact I | lia].
      - zstep. if_cases KEOF.
        + eapply (U_tail _ _ ret n eof z); first [exact I | lia].
        + eapply (U_4a8 _ _ n eof ret t z); first [exact I | lia].
    Qed.

    (* [comment removed for export] *)
    Lemma U_794 : forall w0 mX n eof ret t z x1 x5 x6 x12 x14 x15,
      INV w0 OLW SHW mX -> 0 <= n <= 64 -> 0 <= eof <= 2 -> 0 <= ret -> 4 * ret + 3 * n <= 3 * (i + num) -> 0 <= t < 128 -> 0 <= z <= 255 ->
      evt asegs POST (IT 0x31f63c mX x1 x5 x6 (Z_to_bv 64 (-1)) (Z_to_bv 64 (Z.land z 236)) (Z_to_bv 64 t) x12 x14 x15 (Z_to_bv 64 z) n eof ret).
    Proof.
      intros w0 mX n eof ret t z x1 x5 x6 x12 x14 x15 I Hn He Hret HI Ht Hz.
      zstep. if_cases KE0; zify_cond KE0; signed_lits_in KE0.
      - zstep. zstep. if_cases KEOF.
        + eapply (U_tail _ _ ret n 0 z); first [exact I | lia].
        + zstep. eapply (U_4a8 _ _ n 0 ret t z); first [exact I | lia].
      - zstep. if_cases KNB.
        + prep I. do 3 zstep. eapply (U_end _ _ _ _ (-1) ret n); first [exact I | lia].
        + eapply (U_780 _ _ n eof ret t z); first [exact I | lia].
    Qed.

    (* [comment removed for export] *)
    Lemma U_head : forall n eof ret, HEADP i n eof ret.
    Proof.
      intros n eof ret w0 mX x1 x5 x6 x7 x10 x11 x12 x14 x15 x18 I _ Hn He Hret HI.
      prep I.
      chk_pass ACC_BUF (B + i) 1 0x31f604 10 11.
      destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:Hb; [|apply nth_error_None in Hb; lia].
      pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
      pose proof (u8arr_read asegs _ B bs i b (Z_to_bv 64 (B + i)) BLK Hb ltac:(lia) eq_refl) as RD.
      zstep. clear RD. do 2 zstep.
      destruct (sxb_cases b) as [[SB HB]|[SB [HB EQ]]]; rewrite SB; cbv iota.
      - do 3 zstep. eapply (U_end _ _ _ _ (-1) ret n); first [exact I | lia].
      - rewrite EQ. zstep.
        do 3 zstep. zstep. th_if_lit.
        destruct (b64A_table_nth (bv_unsigned b) ltac:(lia)) as [tv Hv].
        pose proof (u8ro_read asegs _ 672160 b64A_table (bv_unsigned b) tv (Z_to_bv 64 (672160 + bv_unsigned b)) (b64A_table_at _ MI) Hv ltac:(lia) eq_refl) as RD2.
        zstep. clear RD2.
        pose proof (bv_unsigned_in_range 8 tv) as Rv. unfold bv_modulus in Rv. change (2 ^ Z.of_N 8) with 256 in Rv.
        clear CN ED LED CT BLK LBS OLC ST MI MU WM.
        zstep. if_cases K255.
        + do 3 zstep. eapply (U_end _ _ _ _ (-1) ret n); first [exact I | lia].
        + do 2 zstep. if_cases K61.
          * eapply (U_794 _ _ n eof ret (bv_unsigned b) (bv_unsigned tv)); first [exact I | lia].
          * zstep. rewrite ?(ubs_sw32 (eof + 1)) by lia. zstep.
            eapply (U_780 _ _ n (eof + 1) ret (bv_unsigned b) (bv_unsigned tv)); first [exact I | lia].
    Qed.
  End Iter.

  Lemma U_loop : forall (k : nat) i, Z.to_nat (inl - i) = k -> forall n eof ret, HEADP i n eof ret.
  Proof.
    induction k as [k IH] using lt_wf_ind; intros i HK n eof ret.
    intros w0 mX x1 x5 x6 x7 x10 x11 x12 x14 x15 x18 I Hi Hn He Hret HI.
    eapply (U_head i Hi); [| exact I | exact Hi | exact Hn | exact He | exact Hret | exact HI].
    intros n' eof' ret'. eapply (IH (Z.to_nat (inl - (i + 1)))); [lia | reflexivity].
  Qed.

  Notation JW l := (bv_extract 0 64 (le_bytes_to_word l)).

  (* [comment removed for export] *)
  Lemma U_flags : forall w0 w1 w2 mX eof x1 x5 x6 x7 x10 x11 x12 x14 x15 x18 x20 x21 x27 x28 x29 x30 x31,
    INV w0 w1 w2 mX -> 0 < inl -> 0 <= eof <= 2 ->
    evt asegs POST (ST 0x31f564 mX x1 x5 x6 x7 CW x10 x11 x12 (Z_to_bv 64 num) x14 x15 DW (Z_to_bv 64 B) x18 SHW x20 x21 (Z_to_bv 64 inl) (Z_to_bv 64 B)
                       (Z_to_bv 64 eof) OLW SHBv x27 x28 x29 x30 x31).
  Proof.
    intros w0 w1 w2 mX eof x1 x5 x6 x7 x10 x11 x12 x14 x15 x18 x20 x21 x27 x28 x29 x30 x31 I Hinl He.
    open_inv I.
    apply (th_cells_congr asegs mX (C + 84) _ [C4 ln; C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) in CT;
      [| reflexivity | reflexivity | cbn; tauto].
    zstep. chk_pass ACC_C (C + 88) 4 0x31f578 11 12.
    ths.
    ths. zstep. zstep. th_if_lit.
    do 2 zstep.
    zstep. if_cases KI; zify_cond KI; signed_lits_in KI. { exfalso. lia. }
    ths.
    do 8 zstep.
    apply (th_cells_congr asegs _ (C + 84) _ [C4 ln; C4 z64]) in CT; [| reflexivity | reflexivity | cbn; tauto].
    lazymatch goal with MIh : mem_inv asegs ?mm |- _ => assert (I2 : INV w0 OLW SHW mm) by close_inv end.
    replace (Z_to_bv 64 B) with (Z_to_bv 64 (B + 0)) by (f_equal; lia).
    replace (Z_to_bv 64 inl) with (Z_to_bv 64 (inl - 0)) by (f_equal; lia).
    eapply (U_loop (Z.to_nat (inl - 0)) 0 eq_refl num eof 0); first [exact I2 | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma U_join : forall w0 w1 w2 mX eof x1 x5 x6 x7 x10 x11 x12 x14 x15 x18 x20 x21 x27 x28 x29 x30 x31,
    INV w0 w1 w2 mX -> 0 <= eof <= 2 ->
    evt asegs POST (ST 0x31f560 mX x1 x5 x6 x7 CW x10 x11 x12 (Z_to_bv 64 num) x14 x15 DW (Z_to_bv 64 B) x18 SHW x20 x21 (Z_to_bv 64 inl) (Z_to_bv 64 B)
                       (Z_to_bv 64 eof) OLW SHBv x27 x28 x29 x30 x31).
  Proof.
    intros w0 w1 w2 mX eof x1 x5 x6 x7 x10 x11 x12 x14 x15 x18 x20 x21 x27 x28 x29 x30 x31 I He.
    zstep. if_cases KI; zify_cond KI.
    - do 3 zstep. eapply (U_end _ _ _ _ 0 0 num); first [exact I | lia].
    - eapply (U_flags _ _ _ _ eof); first [exact I | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma U_eof0 : forall w0 w1 w2 mX x1 x5 x6 x7 x10 x11 x12 x14 x15 x18 x20 x21 x24 x27 x28 x29 x30 x31,
    INV w0 w1 w2 mX ->
    evt asegs POST (ST 0x31f5b0 mX x1 x5 x6 x7 CW x10 x11 x12 (Z_to_bv 64 num) x14 x15 DW (Z_to_bv 64 B) x18 SHW x20 x21 (Z_to_bv 64 inl) (Z_to_bv 64 B)
                       x24 OLW SHBv x27 x28 x29 x30 x31).
  Proof.
    intros w0 w1 w2 mX x1 x5 x6 x7 x10 x11 x12 x14 x15 x18 x20 x21 x24 x27 x28 x29 x30 x31 I.
    do 2 zstep. if_cases KI; zify_cond KI.
    - eapply (U_flags _ _ _ _ 0); first [exact I | lia].
    - do 3 zstep. eapply (U_end _ _ _ _ 0 0 num); first [exact I | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma dupdate_body : forall ed bs t0 t1 t2 a5 a6 a7 t3 t4 t5 t6,
    rw_cells asegs m C (ectx_cells (Z_to_bv 64 num) ed ln z64) -> length ed = 80%nat ->
    rw_cells asegs m B [CB N bs] -> rw_cells asegs m OL [C4 old] -> stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 CW (Z_to_bv 64 B) OLW (Z_to_bv 64 B) (Z_to_bv 64 inl) a5 a6 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x31f498) fc None m (seg_rom asegs)).
  Proof.
    intros ed bs t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 CTX LED BLK OLC ST MI.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    destruct (ectx_split _ _ _ CTX) as (CN & ED & CT). clear CTX.
    pose proof (rw_cells_CB_length asegs _ _ _ _ BLK) as LBS. apply u8arr_of_rw_cells in BLK.
    assert (CAL4 : C mod 4 = 0) by (clear - CAL; Z.div_mod_to_equations; lia).
    th_frame 128%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
    do 15 ths. pose proof (SHCX _ MU) as SHC0.
    (* [comment removed for export] *)
    assert (L0 : length (firstn 8 junk) = 8%nat /\ length (firstn 8 (skipn 8 junk)) = 8%nat /\ length (firstn 8 (skipn 8 (skipn 8 junk))) = 8%nat)
      by (destruct FR as [[WF _] _]; cbn in WF; tauto).
    destruct L0 as (L0 & L1 & L2).
    apply (th_cells_congr asegs _ (SP + -128) _
             [C8 (JW (firstn 8 junk)); C8 (JW (firstn 8 (skipn 8 junk))); C8 (JW (firstn 8 (skipn 8 (skipn 8 junk))));
              C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) in FR;
      [| cbn [cells_bytes cbytes]; rewrite (le8_ld _ L0), (le8_ld _ L1), (le8_ld _ L2); reflexivity | reflexivity | cbn; tauto].
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    do 3 zstep.
    zstep. zstep. zstep. zstep. zstep. zstep. th_if_lit.
    zstep. rewrite (t_sx32_small num) by lia.
    zstep.
    lazymatch goal with MIh : mem_inv asegs ?mm |- _ =>
      assert (I : INV (JW (firstn 8 junk)) (JW (firstn 8 (skipn 8 junk))) (JW (firstn 8 (skipn 8 (skipn 8 junk)))) mm) by close_inv end.
    zstep. if_cases KN; zify_cond KN; signed_lits_in KN.
    { eapply (U_eof0 _ _ _ _); exact I. }
    zstep. zstep.
    destruct (nth_error ed (Z.to_nat (num - 1))) as [b1|] eqn:Hb1; [|apply nth_error_None in Hb1; lia].
    do 3 zstep. zstep. th_if_lit.
    pose proof (u8arr_read asegs _ (C + 4) ed (num - 1) b1 (Z_to_bv 64 (num + (C + 4) + -1)) ED Hb1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD.
    zstep. zstep. if_cases KP.
    { eapply (U_eof0 _ _ _ _); exact I. }
    zstep. zstep. if_cases K1; zify_cond K1.
    { eapply (U_join _ _ _ _ 1); first [exact I | lia]. }
    zstep.
    destruct (nth_error ed (Z.to_nat (num - 2))) as [b2|] eqn:Hb2; [|apply nth_error_None in Hb2; lia].
    do 3 zstep. zstep. th_if_lit.
    pose proof (u8arr_read asegs _ (C + 4) ed (num - 2) b2 (Z_to_bv 64 (num + (C + 4) + -2)) ED Hb2 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD.
    do 3 zstep.
    set (e := Z.b2z (Z.land (bv_unsigned b2 + -61) 18446744073709551615 <? 1) + 1).
    assert (He : 1 <= e <= 2) by (unfold e; destruct (Z.land (bv_unsigned b2 + -61) 18446744073709551615 <? 1); cbn [Z.b2z]; lia).
    rewrite ?(ubs_sw32 e) by lia. clearbody e.
    eapply (U_join _ _ _ _ e); first [exact I | lia].
  Qed.
End Proofs.

(* [comment removed for export] *)
Definition W4_decode_update_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (C B OL : Z) (N : nat) (inl num : Z) (ln old : word) (ed bs : list byte) (lo : Z),
    a0 = Z_to_bv 64 C -> a1 = Z_to_bv 64 B -> a2 = Z_to_bv 64 OL -> a3 = Z_to_bv 64 B -> a4 = Z_to_bv 64 inl ->
    rw_cells asegs m C (ectx_cells (Z_to_bv 64 num) ed ln z64) -> length ed = 80%nat -> 0 <= num <= 64 ->
    0 < C -> C mod 8 = 0 -> C + 92 <= lo -> acc asegs m C 92 -> (C + 92 <= 0x10000 \/ 0xbc6000 <= C) -> (C + 92 <= 0x7fff8000 \/ 0x10007fff8000 <= C) ->
    rw_cells asegs m B [CB N bs] -> 0 <= inl <= Z.of_nat N -> inl < 2 ^ 31 -> 3 * (inl + num) <= 4 * Z.of_nat N ->
    0 < B -> B + Z.of_nat N <= lo -> acc asegs m B (Z.of_nat N) ->
    (B + Z.of_nat N <= 0x10000 \/ 0xbc6000 <= B) -> (B + Z.of_nat N <= 0x7fff8000 \/ 0x10007fff8000 <= B) ->
    rw_cells asegs m OL [C4 old] -> 0 < OL -> OL mod 4 = 0 -> acc asegs m OL 4 -> (OL + 4 <= lo \/ bv_unsigned sp <= OL) -> OL + 4 <= 2 ^ 47 ->
    (OL + 4 <= 0x10000 \/ 0xbc6000 <= OL) -> (OL + 4 <= 0x7fff8000 \/ 0x10007fff8000 <= OL) ->
    (C + 92 <= B \/ B + Z.of_nat N <= C) -> (C + 92 <= OL \/ OL + 4 <= C) -> (B + Z.of_nat N <= OL \/ OL + 4 <= B) ->
    acc asegs m 672160 128 ->
    img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
    stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 192 -> bv_unsigned sp <= 2 ^ 47 ->
    mem_inv asegs m ->
    evt asegs (dupdate_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc C B OL N inl num ln lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_EVP_DecodeUpdate) fc None m (seg_rom asegs)).

Theorem W4_decode_update_proof : W4_decode_update_stmt.
Proof.
  unfold W4_decode_update_stmt, g_shadow_memory_dynamic_address, SHB, e_EVP_DecodeUpdate. intros until lo.
  intros -> -> -> -> -> CTX LED HN HC CAL CLO ACC_C CIM CSH BLK HI HI31 HROOM HB BLO ACC_BUF BIM BSH OLC HO OAL ACC_O OLO OTOP OIM OSH S1 S2 S3 ACC_B UT SHC ST LO0 LO HTOP MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (rw_cells_bound _ _ _ _ BLK) as BB. cbn [cells_size csize Nat.add] in BB.
  Ltac dupd_side CSH BSH OSH OLO CLO BLO LO0 LO HTOP RSP CIM BIM OIM BB SHC :=
    first [ reflexivity
          | solve [clear - CSH BSH OSH OLO CLO BLO LO0 LO HTOP RSP; sh_fp_lia]
          | solve [clear - CIM BIM OIM OLO CLO BLO LO0 LO HTOP RSP; ut_fp_lia]
          | solve [clear - BIM BB; intros r Hr; lia]
          | solve [clear - BSH BB; intros r Hr; lia]
          | solve [clear - SHC CIM BIM OIM OLO CLO BLO LO0 LO HTOP RSP BB; intros mX MU; eapply ro_cells_transport; [exact SHC| exact MU|];
                   cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia] ].
  eapply (dupdate_body ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m C B OL N inl num ln old lo); try eassumption; try lia.
  all: dupd_side CSH BSH OSH OLO CLO BLO LO0 LO HTOP RSP CIM BIM OIM BB SHC.
  Unshelve.
  all: dupd_side CSH BSH OSH OLO CLO BLO LO0 LO HTOP RSP CIM BIM OIM BB SHC.
Qed.
