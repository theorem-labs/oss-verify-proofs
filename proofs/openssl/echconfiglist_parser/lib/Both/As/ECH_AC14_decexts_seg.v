(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C10 ECH_AKit ECH_AsKit ECH_AsKitK.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ADX_LOOP : Z := 0x554f54.   Definition ADX_R1 : Z := 0x555068.    Definition ADX_R2 : Z := 0x555088.    Definition ADX_MALLOC : Z := 0x5550a4.
Definition ADX_R3 : Z := 0x5550ac.     Definition ADX_R4 : Z := 0x555130.    Definition ADX_R5 : Z := 0x555148.    Definition ADX_R6 : Z := 0x55515c.
Definition ADX_R7 : Z := 0x555170.     Definition ADX_PUSH : Z := 0x555180.  Definition ADX_R8 : Z := 0x55518c.    Definition ADX_RET1 : Z := 0x5551f0.
Definition ADX_RAISE : Z := 0x55520c.  Definition ADX_RA1 : Z := 0x555214.   Definition ADX_RA2 : Z := 0x555230.   Definition ADX_RA3 : Z := 0x555244.
Definition ADX_CLEAN : Z := 0x555258.  Definition ADX_R9 : Z := 0x555278.    Definition ADX_R10 : Z := 0x555288.   Definition ADX_R11 : Z := 0x55529c.
Definition ADX_R12 : Z := 0x5552b4.    Definition ADX_EPI : Z := 0x5552b8.
(* [comment removed for export] *)
Definition ADX_FILE_PKT : Z := 0x400aa.   (* [comment removed for export] *)
Definition ADX_FILE_ECHS : Z := 0x11238e.  (* [comment removed for export] *)
Definition ADX_FUNC : Z := 0x1125c0.       (* [comment removed for export] *)
Definition ADX_THUNK_CMP : Z := 0x5553f8. Definition ADX_THUNK_COPY : Z := 0x555424. Definition ADX_THUNK_FREE : Z := 0x5544f4.
Definition ADX_R_INTERNAL : Z := 0xc0103. Definition ADX_REASON : Z := 425. Definition ADX_ERR_LIB_SSL : Z := 20.
Definition ASHB : Z := 0x7fff8000.          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition adx_frame (j0 : list byte) (pk ee : Z) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 (wz ADX_FILE_ECHS); C8 (wz ADX_FILE_PKT); C8 (wz (ee + 56)); C8 (wz 0); C8 (wz 0);
   C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac br := let K0 := fresh "K0" in if_cases K0; zify_cond K0; try kill K0; try clear K0.
  Local Ltac retpc := match goal with |- context [ret_pc (Z_to_bv 64 ?v)] => replace (ret_pc (Z_to_bv 64 v)) with (Z_to_bv 64 v) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
  (* [comment removed for export] *)
  Local Ltac reacc ACCP0 ACCB0 MU :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch type of ACCP0 with id (accessible _ ?pk ?n) =>
        let A := fresh "ACCP" in
        assert (A : accessible mx pk n) by (unfold id in ACCP0; eapply accessible_across; [exact ACCP0| exact MU|]; constructor; [cbn; lia| constructor]) end;
      lazymatch type of ACCB0 with id (accessible _ ?b ?n) =>
        let B := fresh "ACCB" in
        assert (B : accessible mx b n) by (unfold id in ACCB0; eapply accessible_across; [exact ACCB0| exact MU|]; constructor; [cbn; lia| constructor]) end
    end.


  (* [comment removed for export] *)
  Lemma adx_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo ee pk : Z),
      a0 = Z_to_bv 64 ee -> a1 = Z_to_bv 64 pk -> 0 <= pk -> pk + 24 <= AAPP_HI -> 0 <= ee -> ee + 104 <= AAPP_HI -> pk mod 8 = 0 -> ee mod 8 = 0 ->
      rw_cells asegs m AGOT_SHBASE [C8 (wz ASHBASE_CELL)] -> rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)] ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 144 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1 j0 (a1' a2' : word),
          ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 0) a1' a2' a3 a4 (Z_to_bv 64 (-2)) (Z_to_bv 64 1) (Z_to_bv 64 2)
                       (Z_to_bv 64 pk) (Z_to_bv 64 (pk + 16)) (Z_to_bv 64 (Z.shiftr pk 3 + ASHB)) (Z_to_bv 64 (Z.shiftr (pk + 16) 3 + ASHB)) s6 s7 s8 (Z_to_bv 64 ASHB) s10 (Z_to_bv 64 (ee + 56)) t3 t4 t5 t6)
                   F (Z_to_bv 64 ADX_LOOP) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -144, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp + -144)
          /\ rw_cells asegs m1 (bv_unsigned sp + -144) (adx_frame j0 pk ee s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_ech_decode_echconfig_exts) fc None m (seg_rom asegs)).
  Proof.
    intros until pk. intros A0 A1 PK0 PKH EE0 EEH PAL EAL GSB SHB0 ST CEIL LO MI. subst a0 a1.
    unfold P_ech_decode_echconfig_exts, ADX_LOOP, ADX_R_INTERNAL, ASHB, ADX_FILE_PKT.
    acb. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0. unfold AAPP_HI in *.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -144, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. carve_frame 144%nat ST.
    do 13 st1.
    do 27 (first [zstep; fix_lit_store; try nrm | st1]).
    ubal_by PAL. if_lit.
    rewrite (al8 pk PAL), (al8 ee EAL) in FR.
    apply evt_done. eexists. exists (@nil byte). do 2 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma apk_byte : forall m base bs cur i b,
    bytes_at asegs m base bs -> nth_error bs (Z.to_nat (cur - base + i)) = Some b -> base <= cur -> 0 <= i ->
    ov_read_bytes asegs m (wa (cur + i)) 1 = Some [b].
  Proof.
    intros m base bs cur i b BS NTH LE I0. eapply (u8ro_read asegs m base bs (cur - base + i) b); [exact BS| exact NTH| lia|]. f_equal. lia.
  Qed.



  (* [comment removed for export] *)
  Definition adxH_post (ra sp gp tp t0 t1 t2 s1 a1 a2 a4 s6 s7 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (pk ee cur base rem : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (a0' a1' a2' a3' a4' a5' s1' s7' s11' : word) m' cur' rem',
          munch [(pk, pk + 24)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
          /\ rw_cells asegs m' pk (pk_cells cur' base rem') /\ cur + rem = cur' + rem' /\ 0 <= rem' <= rem /\
         (  (rem = 0 /\ m' = m /\ rem' = rem /\
             ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 1) a1 a2 (Z_to_bv 64 rem) a4 (Z_to_bv 64 (-2)) (Z_to_bv 64 1) (Z_to_bv 64 2)
                          (Z_to_bv 64 pk) (Z_to_bv 64 (pk + 16)) (Z_to_bv 64 (Z.shiftr pk 3 + ASHB)) (Z_to_bv 64 (Z.shiftr (pk + 16) 3 + ASHB))
                          s6 s7 s8 (Z_to_bv 64 ASHB) s10 (Z_to_bv 64 (ee + 56)) t3 t4 t5 t6)
                      F (Z_to_bv 64 ADX_EPI) fc None m' (seg_rom asegs))
         \/ (exists line, (line = 206 \/ line = 210) /\ 1 <= rem /\
             ms' = MS (mkR (Z_to_bv 64 ADX_RA1) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp s1' a0' a1' a2' a3' a4' a5' (Z_to_bv 64 1) (Z_to_bv 64 2)
                          (Z_to_bv 64 pk) (Z_to_bv 64 (pk + 16)) (Z_to_bv 64 (Z.shiftr pk 3 + ASHB)) (Z_to_bv 64 (Z.shiftr (pk + 16) 3 + ASHB))
                          (Z_to_bv 64 line) s7' s8 (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr (ee + 56) 3)) s11' t3 t4 t5 t6)
                      F (Z_to_bv 64 P_ERR_new) fc None m' (seg_rom asegs))
         \/ (exists x0 x1 extlen, 0 <= extlen < 512 /\ cur' = cur + 4 + extlen /\ rem' = rem - 4 - extlen /\ 0 <= x0 < 256 /\ 0 <= x1 < 256 /\
             ms' = MS (mkR (Z_to_bv 64 ADX_R1) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp (Z_to_bv 64 x1) (Z_to_bv 64 0) (Z_to_bv 64 ADX_FILE_PKT) (Z_to_bv 64 518) a3' a4' a5'
                          (Z_to_bv 64 1) (Z_to_bv 64 2) (Z_to_bv 64 pk) (Z_to_bv 64 (pk + 16)) (Z_to_bv 64 (Z.shiftr pk 3 + ASHB)) (Z_to_bv 64 (Z.shiftr (pk + 16) 3 + ASHB))
                          (Z_to_bv 64 (cur + 4)) (Z_to_bv 64 extlen) s8 (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr (ee + 56) 3)) (Z_to_bv 64 x0) t3 t4 t5 t6)
                      F (Z_to_bv 64 P_CRYPTO_free) fc None m' (seg_rom asegs))).

  Local Ltac ckp := lazymatch goal with
    | A0 : id (accessible _ ?p 24), B0 : id (accessible _ ?b ?n), U : munch _ _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        let A := fresh "ACx" in
        assert (A : accessible mx p 24) by (unfold id in A0; eapply accessible_across; [exact A0| exact U|]; constructor; [cbn; lia| constructor]);
        first [ck8_check A p | ck8_check A (p + 16)]; clear A end.
  Local Ltac hclose mx c r := apply evt_done; unfold adxH_post; do 9 eexists; exists mx, c, r;
    repeat match goal with |- _ /\ _ => split end; try assumption; try lia.

  (* [comment removed for export] *)
  Lemma adx_segH :
    forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 s6 s7 s8 s10 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (pk ee cur base rem blen : Z) (bs : list byte)
           (j0 : list byte) (f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra : word),
      rw_cells asegs m pk (pk_cells cur base rem) -> bytes_at asegs m base bs -> pk_in base (zlength bs) cur rem ->
      0 <= pk -> pk + 24 <= AAPP_HI -> (pk + 24 <= base \/ base + blen <= pk) -> (pk + 24 <= ALOWSH_LO \/ AHI_LO <= pk) ->
      (pk + 24 <= bv_unsigned sp + -144 \/ bv_unsigned sp <= pk) ->
      accessible m pk 24 -> accessible m base blen -> zlength bs <= blen -> 0 <= ee -> ee + 104 <= AAPP_HI ->
      pk mod 8 = 0 -> ee mod 8 = 0 -> 0 < base ->
      rw_cells asegs m (bv_unsigned sp + -144) (adx_frame j0 pk ee f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra) -> 144 <= bv_unsigned sp ->
      mem_inv asegs m ->
      evt asegs (adxH_post ra sp gp tp t0 t1 t2 s1 a1 a2 a4 s6 s7 s8 s10 t3 t4 t5 t6 F fc pk ee cur base rem m)
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 (Z_to_bv 64 (-2)) (Z_to_bv 64 1) (Z_to_bv 64 2)
                 (Z_to_bv 64 pk) (Z_to_bv 64 (pk + 16)) (Z_to_bv 64 (Z.shiftr pk 3 + ASHB)) (Z_to_bv 64 (Z.shiftr (pk + 16) 3 + ASHB))
                 s6 s7 s8 (Z_to_bv 64 ASHB) s10 (Z_to_bv 64 (ee + 56)) t3 t4 t5 t6)
            F (Z_to_bv 64 ADX_LOOP) fc None m (seg_rom asegs)).
  Proof.
    intros until fra. intros PK BS PIN PK0 PKH PKA NSP OD ACCP ACCB BL EE0 EEH PAL EAL BP0 FR SPL MI.
    unfold ADX_LOOP, ADX_EPI, ADX_RA1, ADX_R1, ADX_REASON, ADX_FILE_PKT, ADX_FILE_ECHS, ASHB, P_ERR_new, P_CRYPTO_free in *.
    unfold adx_frame, ADX_FILE_PKT, ADX_FILE_ECHS, wz in FR. unfold pk_cells, wz in PK. acb. unfold AAPP_HI in *.
    pose proof (aword_range sp) as SPR. pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold pk_in, zlength in PIN. unfold zlength in BL.
    pose proof (munch_refl [(pk, pk + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof ACCP as ACCP0. change (accessible m pk 24) with (id (accessible m pk 24)) in ACCP0.
    pose proof ACCB as ACCB0. change (accessible m base blen) with (id (accessible m base blen)) in ACCB0.
    pose proof ACCB as (_ & BHI & _). unfold AAPP_HI in BHI.
    (* [comment removed for export] *)
    ck8_check ACCP (pk + 16). step. step. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      assert (R0 : rem = 0) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0. go_to ADX_EPI.
      hclose m cur rem.
      left. split; [exact R0|]. split; [reflexivity|]. split; [reflexivity|]. reflexivity. }
    assert (R1 : 1 <= rem) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
    step. step. step. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      go. step.
      hclose m cur rem.
      right; left. exists 206. split; [left; reflexivity|]. split; [exact R1|]. reflexivity. }
    assert (R2 : 2 <= rem) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
    (* [comment removed for export] *)
    ck8_check ACCP pk. step. step.
    (* [comment removed for export] *)
    ub_dead.
    go.
    (* [comment removed for export] *)
    destruct (nth_error bs (Z.to_nat (cur - base + 0))) as [c0|] eqn:N0; [| apply nth_error_None in N0; lia].
    destruct (nth_error bs (Z.to_nat (cur - base + 1))) as [c1|] eqn:N1; [| apply nth_error_None in N1; lia].
    pose proof (apk_byte _ _ _ _ _ _ BS N0 ltac:(lia) ltac:(lia)) as RD0. pose proof (apk_byte _ _ _ _ _ _ BS N1 ltac:(lia) ltac:(lia)) as RD1.
    pose proof (abyte_range c0) as C0R. pose proof (abyte_range c1) as C1R.
    (* [comment removed for export] *)
    ck1_load ACCB cur v1 Y1 Y2 Hk1.
    ck_K 12 0x554f98 K1.
    { intros tv1. red_tset. go.
      (* [comment removed for export] *)
      ck1_load ACCB (cur + 1) v2 V1 V2 Hk. step.
      (* [comment removed for export] *)
      ck_K 14 0x554fb0 K2.
      { intros tv2. red_tset. go.
        (* [comment removed for export] *)
        do 4 (try ckp; go). if_cases K0; zify_cond K0.
        { (* [comment removed for export] *)
          go. step.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => hclose mx (cur + 2) (rem + -2) end.
          right; left. exists 206. split; [left; reflexivity|]. split; [exact R1|]. reflexivity. }
        assert (R4 : 4 <= rem) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
        go.
        (* [comment removed for export] *)
        destruct (nth_error bs (Z.to_nat (cur - base + 2))) as [c2|] eqn:N2; [| apply nth_error_None in N2; lia].
        destruct (nth_error bs (Z.to_nat (cur - base + 3))) as [c3|] eqn:N3; [| apply nth_error_None in N3; lia].
        pose proof (abyte_range c2) as C2R. pose proof (abyte_range c3) as C3R.
        lazymatch goal with BSx : bytes_at asegs ?mx base bs |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          pose proof (apk_byte _ _ _ _ _ _ BSx N2 ltac:(lia) ltac:(lia)) as RD2; pose proof (apk_byte _ _ _ _ _ _ BSx N3 ltac:(lia) ltac:(lia)) as RD3 end.
        lazymatch goal with B0 : id (accessible _ ?b ?n), U : munch _ _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          assert (ACB : accessible mx b n) by (unfold id in B0; eapply accessible_across; [exact B0| exact U|]; constructor; [cbn; lia| constructor]) end.
        (* [comment removed for export] *)
        ck1_load ACB (cur + 2) v3 U1 U2 Hk3.
        ck_K 14 0x554fec K3.
        { intros tv3. red_tset. go.
          (* [comment removed for export] *)
          ck1_load ACB (cur + 3) v4 W1 W2 Hk4. step.
          ck_K 15 0x555010 K4.
          { intros tv4. red_tset. go.
            (* [comment removed for export] *)
            change (zxb c2) with (Z_to_bv 64 (bv_unsigned c2)). change (zxb c3) with (Z_to_bv 64 (bv_unsigned c3)).
            set (x2 := bv_unsigned c2) in *. set (x3 := bv_unsigned c3) in *.
            rewrite (unsigned_lit x2) by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (x2 * 2 ^ 8)) by lia. rewrite (unsigned_lit x3) by lia.
            replace (Z.lor (x2 * 2 ^ 8) x3) with (x3 + 256 * x2) by (rewrite Z.lor_comm; rewrite <- (lor_shiftl8_add x3 x2) by lia; rewrite Z.shiftl_mul_pow2 by lia; f_equal; lia).
            set (extlen := x3 + 256 * x2) in *. assert (XLR : 0 <= extlen < 2^16) by (subst extlen; lia).
            if_cases K0; zify_cond K0.
            { (* [comment removed for export] *)
              go. step.
              lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => hclose mx (cur + 2) (rem + -2) end.
              right; left. exists 206. split; [left; reflexivity|]. split; [exact R1|]. reflexivity. }
            assert (RX : 4 + extlen <= rem) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
            (* [comment removed for export] *)
            go. rewrite zb_lxor_ones by lia. ub_dead.
            do 6 (try ckp; go). if_cases K0; zify_cond K0.
            { (* [comment removed for export] *)
              do 4 (try ckp; go). step.
              lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => hclose mx (cur + 4 + extlen) (rem + -4 - extlen) end.
              right; left. exists 210. split; [right; reflexivity|]. split; [exact R1|]. reflexivity. }
            assert (X512 : extlen < 512) by (revert K0; rewrite ?unsigned_lit by lia; subst extlen; lia). clear K0.
            (* [comment removed for export] *)
            do 4 (try ckp; go). step.
            change (zxb c0) with (Z_to_bv 64 (bv_unsigned c0)). change (zxb c1) with (Z_to_bv 64 (bv_unsigned c1)).
            lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => hclose mx (cur + 4 + extlen) (rem + -4 - extlen) end.
            right; right. exists (bv_unsigned c0), (bv_unsigned c1), extlen. repeat match goal with |- _ /\ _ => split end; try lia. reflexivity. }
          (* [comment removed for export] *)
          ck1_branch_bge (cur + 3) v4 W1 W2 Hk4 K4. }
        ck1_branch_bge (cur + 2) v3 U1 U2 Hk3 K3. }
      ck1_branch_bge (cur + 1) v2 V1 V2 Hk K2. }
    (* [comment removed for export] *)
    ck1_branch_bge cur v1 Y1 Y2 Hk1 K1.
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma adx_seg2 :
    forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (extlen : Z)
           (j0 : list byte) (pk ee : Z) (f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra : word),
      0 <= extlen < 512 ->
      rw_cells asegs m (bv_unsigned sp + -144) (adx_frame j0 pk ee f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra) -> 144 <= bv_unsigned sp -> mem_inv asegs m ->
      evt asegs (fun ms' =>
         (extlen = 0 /\
          ms' = MS (mkR (Z_to_bv 64 ADX_R3) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 16) (Z_to_bv 64 ADX_FILE_ECHS) (Z_to_bv 64 217) a3 a4 a5 a6 a7
                        s2 s3 s4 s5 s6 (Z_to_bv 64 extlen) (Z_to_bv 64 0) s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_malloc) fc None m (seg_rom asegs))
      \/ (1 <= extlen /\
          ms' = MS (mkR (Z_to_bv 64 ADX_R2) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp s1 s6 (Z_to_bv 64 extlen) (Z_to_bv 64 ADX_FILE_PKT) (Z_to_bv 64 527) a4 a5 a6 a7
                        s2 s3 s4 s5 s6 (Z_to_bv 64 extlen) s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_memdup) fc None m (seg_rom asegs)))
        (MS (mkR (Z_to_bv 64 ADX_R1) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 extlen) s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADX_R1)) fc None m (seg_rom asegs)).
  Proof.
    intros until fra. intros XR FR SPL MI. unfold ADX_R1, ADX_R2, ADX_R3, P_CRYPTO_malloc, P_CRYPTO_memdup, ADX_FILE_PKT, ADX_FILE_ECHS in *.
    unfold adx_frame, ADX_FILE_PKT, ADX_FILE_ECHS, wz in FR. retpc.
    pose proof (aword_range sp) as SPR. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. if_cases K0; zify_cond K0.
    - assert (X0 : extlen = 0) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      go. step. apply evt_done. left. split; [exact X0| reflexivity].
    - assert (X1 : 1 <= extlen) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      go. step. apply evt_done. right. split; [exact X1| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma adx_seg3 :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (D : Z)
           (j0 : list byte) (pk ee : Z) (f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra : word),
      0 < D < 2^64 ->
      rw_cells asegs m (bv_unsigned sp + -144) (adx_frame j0 pk ee f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra) -> 144 <= bv_unsigned sp -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ADX_R3) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 16) (Z_to_bv 64 ADX_FILE_ECHS) (Z_to_bv 64 217) a3 a4 a5 a6 a7
                        s2 s3 s4 s5 s6 s7 (Z_to_bv 64 D) s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_malloc) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 ADX_R2) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADX_R2)) fc None m (seg_rom asegs)).
  Proof.
    intros until fra. intros DR FR SPL MI. unfold ADX_R2, ADX_R3, P_CRYPTO_malloc, ADX_FILE_ECHS in *.
    unfold adx_frame, ADX_FILE_PKT, ADX_FILE_ECHS, wz in FR. retpc.
    pose proof (aword_range sp) as SPR. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. step. try br. go. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma adx_seg4 :
    forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ee oe val x0 x1 extlen : Z) (E : entrep) pad1 pad2 pad3 pad4 junk
           (j0 : list byte) (pk : Z) (f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra : word),
      rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 <= ee -> ee + ENTRY_SIZE <= AAPP_HI -> 0 <= en_exts E < 2^64 ->
      rw_cells asegs m oe [CB 16 junk] -> 0 < oe -> (oe + 16 <= ee \/ ee + ENTRY_SIZE <= oe) -> oe + 16 <= bv_unsigned sp + -144 ->
      (oe + 16 <= ALOWSH_LO \/ AHI_LO <= oe) -> accessible m oe 16 -> accessible m (ee + 56) 8 ->
      0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= extlen < 512 -> 0 <= val < 2^64 -> oe mod 8 = 0 ->
      rw_cells asegs m (bv_unsigned sp + -144) (adx_frame j0 pk ee f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra) -> 144 <= bv_unsigned sp ->
      mem_inv asegs m ->
      evt asegs (fun ms' => exists m1 jk (a0' a1' : word),
          munch [(oe, oe + 16)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 oe [C2 (wz (256 * x0 + x1)); C2 (wz extlen); CB 4 jk; C8 (wz val)] /\
         (  (en_exts E = 0 /\
             ms' = MS (mkR (Z_to_bv 64 ADX_R4) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp (Z_to_bv 64 (Z.shiftr (ee + 56) 3 + ASHB)) a0' a1' a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 (Z_to_bv 64 oe) (Z_to_bv 64 extlen) (Z_to_bv 64 val) (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr (ee + 56) 3)) (Z_to_bv 64 (ee + 56)) t3 t4 t5 t6)
                      F (Z_to_bv 64 P_OPENSSL_sk_new_null) fc None m1 (seg_rom asegs))
         \/ (0 < en_exts E /\
             ms' = MS (mkR (Z_to_bv 64 ADX_R8) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp (Z_to_bv 64 (Z.shiftr (ee + 56) 3 + ASHB)) (Z_to_bv 64 (en_exts E)) (Z_to_bv 64 oe) a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 (Z_to_bv 64 oe) (Z_to_bv 64 extlen) (Z_to_bv 64 val) (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr (ee + 56) 3)) (Z_to_bv 64 (ee + 56)) t3 t4 t5 t6)
                      F (Z_to_bv 64 P_OPENSSL_sk_push) fc None m1 (seg_rom asegs))))
        (MS (mkR (Z_to_bv 64 ADX_R3) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp (Z_to_bv 64 x1) (Z_to_bv 64 oe) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 (Z_to_bv 64 extlen) (Z_to_bv 64 val) (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr (ee + 56) 3)) (Z_to_bv 64 x0) t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADX_R3)) fc None m (seg_rom asegs)).
  Proof.
    intros until fra. intros EC EE0 EEH XR OE OEP DJ OSP NSO ACCO ACCE X0R X1R XL VR OAL FR SPL MI.
    unfold ADX_R3, ADX_R4, ADX_R8, P_OPENSSL_sk_new_null, P_OPENSSL_sk_push, ASHB in *. unfold entry_cells in EC. unfold ENTRY_SIZE, AAPP_HI in *.
    unfold adx_frame, ADX_FILE_PKT, ADX_FILE_ECHS, ASHB, wz in FR. retpc.
    acb. pose proof (aword_range sp) as SPR.
    pose proof (munch_refl [(oe, oe + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof ACCO as ACCO0. change (accessible m oe 16) with (id (accessible m oe 16)) in ACCO0.
    pose proof ACCE as ACCE0. change (accessible m (ee + 56) 8) with (id (accessible m (ee + 56) 8)) in ACCE0.
    (* [comment removed for export] *)
    step. try br. step. step. step. ubal_by OAL; if_lit. zstep. zstep. ck8_check ACCO oe.
    (* [comment removed for export] *)
    step. step.
    rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit x0) by lia. rewrite (unsigned_lit (x0 * 2^8)) by lia. rewrite (unsigned_lit x1) by lia.
    replace (Z.lor (x0 * 2 ^ 8) x1) with (256 * x0 + x1) by (rewrite Z.lor_comm; replace (x0 * 2 ^ 8) with (Z.shiftl x0 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity); rewrite (lor_shiftl8_add x1 x0) by lia; lia).
    zstep. clear ACCO ACCE. st1. reacc ACCO0 ACCE0 MU.
    (* [comment removed for export] *)
    zstep. zstep. ck8_check ACCP (oe + 8). clear ACCP ACCB. st1. reacc ACCO0 ACCE0 MU.
    (* [comment removed for export] *)
    zstep. zstep. zstep. ck8_check ACCP (oe + 2). clear ACCP ACCB. st1. reacc ACCO0 ACCE0 MU.
    (* [comment removed for export] *)
    step. step. if_lit. zstep. ck8_check ACCB (ee + 56). step. step. unfold wz. step.
    if_cases K0; zify_cond K0.
    - assert (XP : 0 < en_exts E) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      step. step. step.
      apply evt_done. do 4 eexists. repeat match goal with |- _ /\ _ => split end; try eassumption.
      right. split; [exact XP| reflexivity].
    - assert (XZ : en_exts E = 0) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      step. step.
      apply evt_done. do 4 eexists. repeat match goal with |- _ /\ _ => split end; try eassumption.
      left. split; [exact XZ|]. reflexivity.
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma adx_seg5 :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (P : Z),
      mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ADX_R5) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 P) (Z_to_bv 64 ADX_THUNK_CMP) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 P) s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OPENSSL_sk_set_cmp_thunks) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 ADX_R4) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADX_R4)) fc None m (seg_rom asegs)).
  Proof.
    intros until P. intros MI. unfold ADX_R4, ADX_R5, P_OPENSSL_sk_set_cmp_thunks, ADX_THUNK_CMP. retpc.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    do 6 step. apply evt_done. reflexivity.
  Qed.
  Lemma adx_seg6 :
    forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (P : Z),
      mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ADX_R6) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 P) (Z_to_bv 64 ADX_THUNK_COPY) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 P) s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OPENSSL_sk_set_copy_thunks) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 ADX_R5) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 P) s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADX_R5)) fc None m (seg_rom asegs)).
  Proof.
    intros until P. intros MI. unfold ADX_R5, ADX_R6, P_OPENSSL_sk_set_copy_thunks, ADX_THUNK_COPY. retpc.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    do 5 step. apply evt_done. reflexivity.
  Qed.
  Lemma adx_seg7 :
    forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (P : Z),
      mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ADX_R7) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 P) (Z_to_bv 64 ADX_THUNK_FREE) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 P) s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OPENSSL_sk_set_thunks) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 ADX_R6) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 P) s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADX_R6)) fc None m (seg_rom asegs)).
  Proof.
    intros until P. intros MI. unfold ADX_R6, ADX_R7, P_OPENSSL_sk_set_thunks, ADX_THUNK_FREE. retpc.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    do 5 step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma adx_seg8 :
    forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ee P : Z) (E : entrep) pad1 pad2 pad3 pad4,
      rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 <= ee -> ee + ENTRY_SIZE <= AAPP_HI -> 0 < P < 2^64 ->
      accessible m (ee + 56) 8 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          munch [(ee, ee + ENTRY_SIZE)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 ee (entry_cells (mkENT (en_version E) (en_pname E) (en_pname_o E) (en_publen E) (en_pub E) (en_pub_o E) (en_nsuites E) (en_suites E) (en_suites_o E)
                      (en_maxname E) (en_cfgid E) P (en_exts_o E) (en_loadtime E) (en_forretry E) (en_enclen E) (en_encoded E) (en_encoded_o E) (en_id E)) pad1 pad2 pad3 pad4)
          /\ ms' = MS (mkR (Z_to_bv 64 ADX_R8) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp (Z_to_bv 64 (Z.shiftr (ee + 56) 3 + ASHB)) (Z_to_bv 64 P) s6 a2 a3 a4 a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 (ee + 56)) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OPENSSL_sk_push) fc None m1 (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 ADX_R7) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp (Z_to_bv 64 (Z.shiftr (ee + 56) 3 + ASHB)) (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 (ee + 56)) t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADX_R7)) fc None m (seg_rom asegs)).
  Proof.
    intros until pad4. intros EC EE0 EEH PR ACCE MI. unfold ADX_R7, ADX_R8, P_OPENSSL_sk_push, ASHB in *. unfold entry_cells in EC |- *.
    cbn [en_version en_pname en_publen en_pub en_nsuites en_suites en_maxname en_cfgid en_exts en_loadtime en_forretry en_enclen en_encoded].
    unfold ENTRY_SIZE, AAPP_HI in *. retpc. acb.
    pose proof (munch_refl [(ee, ee + 104)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    ck8_check ACCE (ee + 56). clear ACCE.
    st1. step. try br. step. step. step. apply evt_done. eexists. repeat match goal with |- _ /\ _ => split end; try eassumption; try reflexivity.
    all: unfold wz in *; exact EC.
  Qed.

  (* [comment removed for export] *)
  Lemma adx_seg9 :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (r : Z)
           (j0 : list byte) (pk ee : Z) (f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra : word),
      0 < r < 2^63 ->
      rw_cells asegs m (bv_unsigned sp + -144) (adx_frame j0 pk ee f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra) -> 144 <= bv_unsigned sp -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ADX_R8) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 0) a1 a2 a3 a4 (Z_to_bv 64 (-2)) (Z_to_bv 64 1) (Z_to_bv 64 2)
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 ADX_LOOP) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 ADX_R8) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADX_R8)) fc None m (seg_rom asegs)).
  Proof.
    intros until fra. intros RR FR SPL MI. unfold ADX_R8, ADX_LOOP, ASHB. unfold adx_frame, ADX_FILE_PKT, ADX_FILE_ECHS, ASHB, wz in FR. retpc.
    pose proof (aword_range sp) as SPR. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. step. step. step. try br. go. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma adx_glue1 : forall (line : Z) (sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m1 : mem), 0 <= line < 2^31 -> mem_inv asegs m1 ->
      evt asegs (fun ms' => exists v0 v1 v2 c3 c4 c5 c6 c7 v3 v4 v5 v6,
                   ms' = MS (mkR (Z_to_bv 64 ADX_RA2) sp gp tp v0 v1 v2 s0 s1 (Z_to_bv 64 ADX_FILE_ECHS) (Z_to_bv 64 line) (Z_to_bv 64 ADX_FUNC) c3 c4 c5 c6 c7
                                 s2 s3 s4 s5 (Z_to_bv 64 line) s7 s8 s9 s10 s11 v3 v4 v5 v6) F (Z_to_bv 64 P_ERR_set_debug) fc None m1 (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 ADX_RA1) sp gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 (Z_to_bv 64 line) s7 s8 s9 s10 s11 u3 u4 u5 u6)
            F (ret_pc (Z_to_bv 64 ADX_RA1)) fc None m1 (seg_rom asegs)).
  Proof.
    intros until m1. intros LR MI. unfold ADX_RA1, ADX_RA2, P_ERR_set_debug, ADX_FILE_ECHS, ADX_FUNC. retpc.
    do 7 step. finish.
  Qed.
  Lemma adx_glue2 : forall (reason : Z) (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m1 : mem), reason = ADX_REASON -> mem_inv asegs m1 ->
      evt asegs (fun ms' => exists v0 v1 v2 c3 c4 c5 c6 c7 v3 v4 v5 v6,
                   ms' = MS (mkR (Z_to_bv 64 ADX_RA3) sp gp tp v0 v1 v2 s0 s1 (Z_to_bv 64 ADX_ERR_LIB_SSL) (Z_to_bv 64 reason) (Z_to_bv 64 0) c3 c4 c5 c6 c7
                                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6) F (Z_to_bv 64 P_ERR_set_error) fc None m1 (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 ADX_RA2) sp gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
            F (ret_pc (Z_to_bv 64 ADX_RA2)) fc None m1 (seg_rom asegs)).
  Proof.
    intros until m1. intros RR MI. subst reason. unfold ADX_RA2, ADX_RA3, P_ERR_set_error, ADX_ERR_LIB_SSL, ADX_REASON. retpc.
    do 5 step. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma adx_segF2 :
    forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ee : Z) (E : entrep) pad1 pad2 pad3 pad4
           (j0 : list byte) (pk : Z) (f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra : word),
      rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 <= ee -> ee + ENTRY_SIZE <= AAPP_HI -> 0 <= en_exts E < 2^64 ->
      accessible m (ee + 56) 8 ->
      rw_cells asegs m (bv_unsigned sp + -144) (adx_frame j0 pk ee f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra) -> 144 <= bv_unsigned sp -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ADX_R9) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 (en_exts E)) (Z_to_bv 64 ADX_THUNK_FREE) a2 a3 a4 a5 a6 a7
                        s2 s3 s4 s5 (Z_to_bv 64 0) s7 (Z_to_bv 64 0) (Z_to_bv 64 (Z.shiftr (ee + 56) 3 + ASHB)) (Z_to_bv 64 (Z.shiftr (ee + 56) 3)) (Z_to_bv 64 (ee + 56)) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OPENSSL_sk_set_thunks) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 ADX_RA3) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr (ee + 56) 3)) s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADX_RA3)) fc None m (seg_rom asegs)).
  Proof.
    intros until fra. intros EC EE0 EEH XR ACCE FR SPL MI. unfold ADX_RA3, ADX_R9, P_OPENSSL_sk_set_thunks, ADX_THUNK_FREE, ASHB in *. unfold entry_cells in EC.
    unfold adx_frame, ADX_FILE_PKT, ADX_FILE_ECHS, ASHB, wz in FR.
    unfold ENTRY_SIZE, AAPP_HI in *. retpc. acb. pose proof (aword_range sp) as SPR.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. step. step. if_lit. step. step. step. ck8_check ACCE (ee + 56). unfold wz. step. do 4 step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma adx_segF3 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (P : Z),
      GOT_echfree m -> 0 <= P < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ADX_R10) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 P_ossl_echext_free) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OPENSSL_sk_pop_free) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 ADX_R9) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADX_R9)) fc None m (seg_rom asegs)).
  Proof.
    intros until P. intros GE PR MI. unfold ADX_R9, ADX_R10, P_OPENSSL_sk_pop_free, P_ossl_echext_free. unfold GOT_echfree, A_got_ossl_echext_free, P_ossl_echext_free, P_ossl_echstore_entry_free in GE. retpc.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. unfold wz. step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma adx_segF4 :
    forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ee oe : Z) (E : entrep) pad1 pad2 pad3 pad4,
      rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 <= ee -> ee + ENTRY_SIZE <= AAPP_HI -> 0 <= oe < 2^64 ->
      accessible m (ee + 56) 8 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          munch [(ee, ee + ENTRY_SIZE)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 ee (entry_cells (mkENT (en_version E) (en_pname E) (en_pname_o E) (en_publen E) (en_pub E) (en_pub_o E) (en_nsuites E) (en_suites E) (en_suites_o E)
                      (en_maxname E) (en_cfgid E) 0 (en_exts_o E) (en_loadtime E) (en_forretry E) (en_enclen E) (en_encoded E) (en_encoded_o E) (en_id E)) pad1 pad2 pad3 pad4)
          /\ ms' = MS (mkR (Z_to_bv 64 ADX_R11) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 oe) a1 a2 a3 a4 a5 a6 a7
                        s2 s3 s4 s5 (Z_to_bv 64 oe) s7 s8 (Z_to_bv 64 (Z.shiftr (ee + 56) 3 + ASHB)) s10 (Z_to_bv 64 (ee + 56)) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_ossl_echext_free) fc None m1 (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 ADX_R10) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 (Z_to_bv 64 oe) s7 s8 (Z_to_bv 64 (Z.shiftr (ee + 56) 3 + ASHB)) s10 (Z_to_bv 64 (ee + 56)) t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADX_R10)) fc None m (seg_rom asegs)).
  Proof.
    intros until pad4. intros EC EE0 EEH OR ACCE MI. unfold ADX_R10, ADX_R11, P_ossl_echext_free, ASHB in *. unfold entry_cells in EC |- *.
    cbn [en_version en_pname en_publen en_pub en_nsuites en_suites en_maxname en_cfgid en_exts en_loadtime en_forretry en_enclen en_encoded]. unfold ENTRY_SIZE, AAPP_HI in *. retpc. acb.
    pose proof (munch_refl [(ee, ee + 104)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    ck8_check ACCE (ee + 56). clear ACCE.
    st1. step. step. apply evt_done. eexists. repeat match goal with |- _ /\ _ => split end; try eassumption; try reflexivity.
    all: unfold wz in *; exact EC.
  Qed.

  (* [comment removed for export] *)
  Lemma adx_segF5 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (D : Z),
      mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ADX_R12) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 ADX_FILE_ECHS) (Z_to_bv 64 240) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 D) s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 ADX_R11) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 D) s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADX_R11)) fc None m (seg_rom asegs)).
  Proof.
    intros until D. intros MI. unfold ADX_R11, ADX_R12, P_CRYPTO_free, ADX_FILE_ECHS. retpc.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    do 6 step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma adx_segF6 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ADX_R12) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 ADX_EPI) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 ADX_R12) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADX_R12)) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros MI. unfold ADX_R12, ADX_EPI. retpc.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma adx_segE :
    forall (rax sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (j0 : list byte) (pk ee : Z) (x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 ra : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      rw_cells asegs m (bv_unsigned sp + -144) (adx_frame j0 pk ee x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 ra) ->
      stk asegs m lo (bv_unsigned sp + -144) -> aceil <= lo -> lo <= bv_unsigned sp - 144 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR ra sp gp tp t0 t1 t2 x0 x1 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m (seg_rom asegs)
          /\ stk asegs m lo (bv_unsigned sp))
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ADX_EPI) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros FR ST CEIL LO MI. unfold ADX_EPI. unfold adx_frame in FR. acb.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    do 13 st1. step. step.
    release_frame FR ST (bv_unsigned sp). apply evt_done. split; [reflexivity| exact ST].
  Qed.
End S.
