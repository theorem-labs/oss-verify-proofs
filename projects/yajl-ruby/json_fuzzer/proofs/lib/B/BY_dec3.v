(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep Arr Cells.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlParser YajlFactsBuf YajlDecode YajlFactsBits.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep RY_lib RY_decode1.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BY_ubkit B_iface BI_shadow BYajlRep BYajl_iface BY_hand BY_dec1 BY_dec2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition ADP_TAIL : Z := 0x8b9ac.   (* [comment removed for export] *)
Definition ADP_TAIL0 : Z := 0x8b9ac.  (* [comment removed for export] *)
Definition ADP_U : Z := 0x8b830.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition esc_lit (c : Z) : Z :=
  if c =? 114 then A_LIT_CR else if c =? 110 then A_LIT_LF else if c =? 92 then A_LIT_BSL else if c =? 47 then A_LIT_SL
  else if c =? 34 then A_LIT_QT else if c =? 102 then A_LIT_FF else if c =? 98 then A_LIT_BS else A_LIT_TAB.

End RC__1.
Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.

(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma seg_esc1 : forall (P : acc -> Prop) (rav sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word) (w0 w96 sur cp : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (SQ FF B S n e beg c2 OT OTn : Z) (shT : list byte),
  mem_inv bsegs m ->
  rw_cells bsegs m SQ (dspill w0 w96 FF sur cp) -> alloc_ceiling <= SQ -> SQ + 240 <= 2^47 ->
  ov_read_bytes bsegs m (Z_to_bv 64 (S + (e + 1))) 1 = Some [Z_to_bv 8 c2] -> In c2 [34; 47; 92; 98; 102; 110; 114; 116; 117] ->
  u8arr bsegs m (2147450880 + OT / 8) shT -> shT = blk_shadow OTn -> OT mod 8 = 0 -> 0 <= OT -> OT <= S + (e + 1) -> S + (e + 1) + 1 <= OT + OTn -> OT + OTn <= alloc_ceiling ->
  0 <= e -> e + 1 < n -> n < 2^26 -> 0 < S -> S + n < 2^47 ->
  pol P SQ (SQ + 120) -> pol P (2147450880 + OT / 8) (2147450880 + OT / 8 + (OTn + 7) / 8) -> pol P OT (OT + OTn) -> pol P 0x10000 0x603000 ->
  evtA bsegs P (fun ms' => exists (x0 x1 x2 : word),
       (c2 <> 117 /\ ms' = DST rav sp gp tp t0 t1 t2 SQ x0 x1 x2 a3 a4 a5 a6 a7 S B n (Z_to_bv 64 (esc_lit c2)) e FF (e + 1) t3 t4 t5 t6 F ADP_TAIL fc m)
    \/ (c2 = 117 /\ ms' = DST rav sp gp tp t0 t1 t2 SQ (Z_to_bv 64 117) (Z_to_bv 64 117) x2 a3 a4 a5 a6 a7 S B n s7 e FF (e + 1) t3 t4 t5 t6 F ADP_U fc m))
    (DST rav sp gp tp t0 t1 t2 SQ a0 a1 a2 a3 a4 a5 a6 a7 S B n s7 e FF beg t3 t4 t5 t6 F ADP_RET2 fc m).
Proof. aceil.
  intros until shT. intros MI FR SQL SQH HRD C2 TSH TSHeq OT8 OT0 OTe OTe1 OTce E0 EN N26 S0 SN PSTK PTS PT PIMG.
  unfold DST, pol, ADP_RET2, ADP_TAIL, ADP_U, dspill, esc_lit, A_LIT_CR, A_LIT_LF, A_LIT_BSL, A_LIT_SL, A_LIT_QT, A_LIT_FF, A_LIT_BS, A_LIT_TAB in *.
  assert (CR2 : 0 <= c2 < 256) by (cbn in C2; lia).
  assert (USQ : bv_unsigned (Z_to_bv 64 SQ) = SQ) by (apply unsigned_lit; lia).
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstepA.                                                 (* [comment removed for export] *)
  zstepA. zstepA. zext32 (e + 1).                         (* [comment removed for export] *)
  ugd.                                                    (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  eapply evtA_cut.
  { eapply (drdck_b8b7d4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (S + (e + 1)) 2147450880 OT OTn);
      [ exact TSH | exact TSHeq | exact OT8 | exact OT0 | exact OTe | exact OTe1 | lia | clear -CEILB OTce OT0; Z.div_mod_to_equations; lia | lia | exact PTS ]. }
  cbv beta. intros ms1 (x1 & x2 & ->).
  zstepA. rewrite ?zxb_small, ?(u8_lit c2) by lia.       (* [comment removed for export] *)
  Ltac fin := apply evtA_done; first [eexists _, _, _; left; split; [lia| reflexivity]
                                    | eexists (Z_to_bv 64 0), (Z_to_bv 64 0), _; right; split; [lia| reflexivity]].
  Ltac br c K := zstepA; if_cases K; zify_cond K; rewrite ?(u8_lit c), ?signed_lit_small in K by lia; try rewrite (u8_lit c) by lia.
  zstepA. br c2 K0.                                          (* [comment removed for export] *)
  - (* [comment removed for export] *)
    zstepA. br c2 K1.                                        (* [comment removed for export] *)
    + (* [comment removed for export] *)
      zstepA. br c2 K2.                                      (* [comment removed for export] *)
      * assert (Ec : c2 = 92) by lia. rewrite Ec. cbn [Z.eqb Pos.eqb]. zstepA. stepA. fin.   (* [comment removed for export] *)
      * zstepA. br c2 K3.                                    (* [comment removed for export] *)
        { exfalso. cbn in C2. lia. }
        assert (Ec : c2 = 98) by lia. rewrite Ec. cbn [Z.eqb Pos.eqb]. zstepA. stepA. fin.   (* [comment removed for export] *)
    + (* [comment removed for export] *)
      zstepA. br c2 K2.                                      (* [comment removed for export] *)
      * assert (Ec : c2 = 34) by lia. rewrite Ec. cbn [Z.eqb Pos.eqb]. zstepA. stepA. fin.   (* [comment removed for export] *)
      * zstepA. br c2 K3.                                    (* [comment removed for export] *)
        { exfalso. cbn in C2. lia. }
        assert (Ec : c2 = 47) by lia. rewrite Ec. cbn [Z.eqb Pos.eqb]. zstepA. stepA. fin.   (* [comment removed for export] *)
  - zstepA. br c2 K1.                                        (* [comment removed for export] *)
    + (* [comment removed for export] *)
      zstepA. br c2 K2.                                      (* [comment removed for export] *)
      * assert (Ec : c2 = 102) by lia. rewrite Ec. cbn [Z.eqb Pos.eqb]. zstepA. zstepA. stepA. fin.   (* [comment removed for export] *)
      * zstepA. br c2 K3.                                    (* [comment removed for export] *)
        { exfalso. cbn in C2. lia. }
        assert (Ec : c2 = 110) by lia. rewrite Ec. cbn [Z.eqb Pos.eqb]. zstepA. zstepA. stepA. fin.
    + zstepA. br c2 K2.                                      (* [comment removed for export] *)
      * assert (Ec : c2 = 114) by lia. rewrite Ec. cbn [Z.eqb Pos.eqb]. zstepA. stepA. fin.   (* [comment removed for export] *)
      * zstepA. br c2 K3.                                    (* [comment removed for export] *)
        -- assert (Ec : c2 = 116) by lia. rewrite Ec. cbn [Z.eqb Pos.eqb]. zstepA. zstepA. fin.     (* [comment removed for export] *)
        -- zstepA. br c2 K4.                                 (* [comment removed for export] *)
           { exfalso. cbn in C2. lia. }
           assert (Ec : c2 = 117) by lia. rewrite Ec. fin.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma abytes_at_sub : forall m A bs i k,
  bytes_at bsegs m A bs -> (i <= length bs)%nat -> bytes_at bsegs m (A + Z.of_nat i) (firstn k (skipn i bs)).
Proof. aceil.
  intros m A bs i k HB Hi.
  rewrite <- (firstn_skipn i bs) in HB. apply bytes_at_app in HB. destruct HB as [_ HB].
  rewrite length_firstn, Nat.min_l in HB by lia.
  rewrite <- (firstn_skipn k (skipn i bs)) in HB. apply bytes_at_app in HB. destruct HB as [HB _]. exact HB.
Qed.
Lemma abytes_at_zslice : forall m A str i k,
  bytes_at bsegs m A (zbytes str) -> 0 <= i <= zlength str -> bytes_at bsegs m (A + i) (zbytes (zslice str i k)).
Proof. aceil.
  intros m A str i k HB Hi. unfold zslice. rewrite RY_decode1.zbytes_firstn, RY_decode1.zbytes_skipn.
  replace i with (Z.of_nat (Z.to_nat i)) at 1 by lia. apply abytes_at_sub; [exact HB|]. rewrite zbytes_length. unfold zlength in Hi. lia.
Qed.
Lemma dznth_nth_error : forall l i, 0 <= i < zlength l -> nth_error l (Z.to_nat i) = Some (znth l i).
Proof. aceil.
  intros l i Hi. unfold znth. destruct (Z.ltb_spec0 i 0); [lia|].
  destruct (nth_error l (Z.to_nat i)) as [c|] eqn:E.
  - rewrite (nth_error_nth _ _ _ E). reflexivity.
  - apply nth_error_None in E. unfold zlength in Hi. lia.
Qed.
Lemma dstr_read : forall m S str i, bytes_at bsegs m S (zbytes str) -> 0 <= i < zlength str ->
  ov_read_bytes bsegs m (Z_to_bv 64 (S + i)) 1 = Some [Z_to_bv 8 (znth str i)].
Proof. aceil.
  intros m S str i TB Hi. eapply (u8ro_read bsegs m S (zbytes str) i); [exact TB| | lia| reflexivity].
  unfold zbytes. rewrite nth_error_map, (dznth_nth_error _ _ Hi). reflexivity.
Qed.
Lemma dstr_byte : forall str i, Forall (fun c => 0 <= c < 256) str -> 0 <= znth str i < 256.
Proof. aceil.
  intros txt i HF. unfold znth. destruct (Z.ltb_spec0 i 0); [lia|].
  destruct (Nat.lt_ge_cases (Z.to_nat i) (length txt)).
  - apply (proj1 (Forall_forall _ _) HF). apply nth_In. assumption.
  - rewrite nth_overflow by lia. lia.
Qed.
Lemma dForall_disjoint_from : forall W lo0 hi0 A n,
  Forall (fun iv : Z * Z => snd iv <= lo0 \/ hi0 <= fst iv) W -> lo0 <= A -> A + n <= hi0 -> disjoint_from W A n.
Proof. aceil.
  intros W lo0 hi0 A n FW H1 H2. induction W as [|[lo hi] W IH]; cbn; [exact I|].
  inversion FW as [|x l F1 F2]; subst. cbn in F1. split; [lia| apply IH; exact F2].
Qed.
Lemma ay_statics_munch : forall W m m',
  ay_statics m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv : Z * Z => snd iv <= 0xa5000 \/ 0xae838 <= fst iv) W -> ay_statics m'.
Proof. aceil.
  intros W m m' (G1 & G2 & G3 & G4) MU WM FW.
  pose proof (fun A n => dForall_disjoint_from W _ _ A n FW) as D.
  split; [|split; [|split]];
    (eapply rw_cells_transport; [eassumption| exact MU| exact WM| apply D;
       unfold AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR; cbn; lia]).
Qed.

Definition ADP_RETH1 : Z := 0x8b850.  (* [comment removed for export] *)
Definition ADP_SUR : Z := 0x8b868.    (* [comment removed for export] *)
Definition ADP_CP : Z := 0x8b9dc.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition dspill15 (w0 w96 : word) (FF : Z) (sur : word) : list cell :=
  [C8 w0; C8 (Z_to_bv 64 0xffc00); C8 (Z_to_bv 64 (FF + 32)); C8 (Z_to_bv 64 0xd800); C8 (Z_to_bv 64 0xfc00);
   C8 (Z_to_bv 64 A_LIT_BS); C8 (Z_to_bv 64 A_LIT_BSL); C8 (Z_to_bv 64 A_LIT_SL); C8 (Z_to_bv 64 A_LIT_QT); C8 (Z_to_bv 64 A_LIT_CR);
   C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 w96; C8 (Z_to_bv 64 FF); C4 sur].
Lemma dspill_split : forall m SQ w0 w96 FF sur cp,
  rw_cells bsegs m SQ (dspill w0 w96 FF sur cp) <-> rw_cells bsegs m SQ (dspill15 w0 w96 FF sur) /\ rw_cells bsegs m (SQ + 116) [C4 cp].
Proof. aceil.
  intros. unfold dspill.
  lazymatch goal with |- rw_cells _ _ _ ?cs <-> _ => rewrite <- (firstn_skipn 15 cs); rewrite (ycells_app bsegs m SQ (firstn 15 cs) (skipn 15 cs)) end.
  cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ app]. unfold dspill15. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma seg_u1 : forall (HEX : ayhexToDigit_stmt) (P : acc -> Prop) (rav sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word) (w0 w96 sur cp0 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (SQ FF B S n e lo cp OT OTn : Z) (str : list Z),
  mem_inv bsegs m -> ay_statics m ->
  rw_cells bsegs m SQ (dspill w0 w96 FF sur cp0) -> stk bsegs m lo SQ -> alloc_ceiling <= lo -> lo + 64 <= SQ -> SQ + 240 <= 2^47 -> SQ mod 32 = 0 ->
  bytes_at bsegs m (A_SB + SQ / 8 + 14) [Z_to_bv 8 0] ->
  bytes_at bsegs m S (zbytes str) -> Forall (fun c => 0 <= c < 256) str -> n = zlength str ->
  oshadow m OT OTn -> OT <= S -> S + n <= OT + OTn -> amem OT OTn -> OT + OTn <= alloc_ceiling ->
  0 <= e -> e + 5 < n -> n < 2^26 -> 0 < S -> S + n < 2^47 ->
  (forall k, 0 <= k < 4 -> is_vhc (znth str (e + 2 + k)) = true) -> yhexToDigit 0 str (e + 2) = Some cp -> 0 <= cp < 2^16 ->
  pol P lo (SQ + 120) -> pol P (A_SB + SQ / 8 + 14) (A_SB + SQ / 8 + 15) -> pol P (oshw_lo OT) (oshw_hi OT OTn) -> pol P OT (OT + OTn) -> pol P 0x10000 0x603000 ->
  evtA bsegs P (fun ms' => exists (rax x1 x2 x3 x4 x5 x6 x7 q0 q1 q2 q3 q4 q5 q6 : word) (m' : mem) (pc' : Z),
       ms' = MS (mkR rax (Z_to_bv 64 SQ) gp tp q0 q1 q2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 cp) x1 x2 x3 x4 x5 x6 x7
                      (Z_to_bv 64 (18446744073709551615 - S)) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 1) s7 (Z_to_bv 64 e) (Z_to_bv 64 (FF / 8 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (e + 5)) q3 q4 q5 q6)
                     F (Z_to_bv 64 pc') fc None m' (seg_rom bsegs)
       /\ ((Z.land cp 64512 <> 55296 /\ pc' = ADP_CP) \/ (Z.land cp 64512 = 55296 /\ pc' = ADP_SUR))
       /\ munch [(lo, SQ + 120)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo SQ /\ ay_statics m'
       /\ rw_cells bsegs m' SQ (dspill w0 w96 FF sur (Z_to_bv 64 cp)) /\ bytes_at bsegs m' (A_SB + SQ / 8 + 14) [Z_to_bv 8 0]
       /\ bytes_at bsegs m' S (zbytes str) /\ oshadow m' OT OTn)
    (DST rav sp gp tp t0 t1 t2 SQ a0 a1 a2 a3 a4 a5 a6 a7 S B n s7 e FF (e + 1) t3 t4 t5 t6 F ADP_U fc m).
Proof. aceil.
  intros until str. intros MI STA FR ST CEIL LOQ SQH SQ32 SSH TB SF NL OSH OTS OTE OTH OTC E0 E5 N26 S0 SN VHC HX CPR PSTK PSSH PTS PT PIMG.
  unfold DST, pol, ADP_U, ADP_CP, ADP_SUR in *. unfold dspill in FR.
  destruct OSH as (OT8 & OTn0 & TSH). remember (blk_shadow OTn) as shT eqn:TSHeq in TSH.
  pose proof (blk_shadow_length OTn ltac:(lia)) as SHL. rewrite <- TSHeq in SHL. unfold A_SB in TSH.
  assert (USQ : bv_unsigned (Z_to_bv 64 SQ) = SQ) by (apply unsigned_lit; lia).
  assert (OTLO : OT + OTn <= lo) by (clear -CEILB OTC CEIL; aceil; lia).
  pose proof OTH as OTH'. unfold oshw_hi, A_SB, amem in OTH'. unfold A_SB in SSH, PSSH.
  assert (SHB : 0 <= OT / 8 /\ 2147450880 + OT / 8 + (OTn + 7) / 8 <= 17594333495296) by (clear -CEILB OTH' OTC OTn0; aceil; Z.div_mod_to_equations; lia).
  pose proof (zlength_nonneg str) as NL0.
  pose proof (munch_refl [(lo, SQ + 120)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  (* [comment removed for export] *)
  pose proof (abytes_at_zslice m S str (e + 2) 4 TB ltac:(lia)) as HB4. rewrite RY_decode1.zslice4 in HB4 by lia.
  pose proof HX as HXL. unfold yhexToDigit in HXL. cbn [zbytes map] in HB4.
  replace (e + 2 + 1) with (e + 3) in * by lia. replace (e + 2 + 2) with (e + 4) in * by lia. replace (e + 2 + 3) with (e + 5) in * by lia.
  yhide TB.
  zstepA. zstepA. zstepA. zext32 (e + 2).                 (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  ugd.                                                    (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  stepA.                                                  (* [comment removed for export] *)
  lazymatch goal with FRx : rw_cells bsegs ?mx SQ _ |- _ => fold dspill in FRx; apply (proj1 (dspill_split _ _ _ _ _ _ _)) in FRx; destruct FRx as [FRa FRb] end.
  pose proof HEX as HEX'. unfold ayhexToDigit_stmt, ayhexToDigit_rpost, wz, AY_HEXTODIGIT, pol in HEX'.
  specialize (HEX' P (SQ + 116) (S + (e + 2)) 0 lo (znth str (e + 2)) (znth str (e + 3)) (znth str (e + 4)) (znth str (e + 5)) cp OT OTn (Z_to_bv 64 ADP_RETH1) (Z_to_bv 64 SQ)).
  rewrite !USQ in HEX'. unfold dspill15 in FRa. unfold ADP_RETH1 in HEX'.
  call_spA HEX'.
  - red. split; [clear -CEILB SQ32; Z.div_mod_to_equations; lia| lia].   (* [comment removed for export] *)
  - eapply ay_statics_munch; [exact STA| exact MU| exact WM| constructor; [cbn; lia| constructor]].
  - exact FRb.
  - lia.
  - exact HB4.
  - replace (e + 2) with (e + 2 + 0) by lia. apply VHC. lia.
  - replace (e + 3) with (e + 2 + 1) by lia. apply VHC. lia.
  - replace (e + 4) with (e + 2 + 2) by lia. apply VHC. lia.
  - replace (e + 5) with (e + 2 + 3) by lia. apply VHC. lia.
  - exact HXL.
  - split; [exact OT8| split; [exact OTn0|]]. unfold A_SB. subst shT. assumption.
  - lia. - lia. - exact OTH. - exact OTC.
  - assumption.
  - assumption.
  - exact CEIL. - lia. - lia. - lia. - lia.
  - replace (A_SB + (SQ + 116) / 8) with (2147450880 + SQ / 8 + 14) by (unfold A_SB; clear -CEILB SQ32; Z.div_mod_to_equations; lia). assumption.
  - reflexivity. - reflexivity.
  - intros a k Ha Hk; apply PSTK; lia.
  - intros a k Ha Hk; apply PIMG; unfold AY_IMG_LO, AY_IMG_HI in *; lia.
  - intros a k Ha Hk; apply PSTK; lia.
  - intros a k Ha Hk; apply PSSH; unfold A_SB in Ha, Hk; clear -CEILB Ha Hk SQ32; Z.div_mod_to_equations; lia.
  - intros a k Ha Hk; apply PT; lia.
  - exact PTS.
  - cbv beta.
    zstepA. rewrite (yzx32_small cp) by lia.              (* [comment removed for export] *)
    zstepA.                                               (* [comment removed for export] *)
    zstepA. rewrite ?(unsigned_lit cp) by lia.            (* [comment removed for export] *)
    zstepA.                                               (* [comment removed for export] *)
    zstepA.                                               (* [comment removed for export] *)
    pose proof (RY_decode1.land_lt16 cp ltac:(lia)) as LA.
    (* [comment removed for export] *)
    lazymatch goal with FA : rw_cells bsegs ?mx SQ _, FB : rw_cells bsegs ?mx (SQ + 116) _ |- _ =>
      assert (FRj : rw_cells bsegs mx SQ (dspill w0 w96 FF sur (Z_to_bv 64 cp)))
        by (apply (proj2 (dspill_split _ _ _ _ _ _ _)); split; [exact FA| exact FB]); clear FA FB end.
    lazymatch goal with X : stk bsegs ?mx lo _ |- _ => rename X into ST2 end.
    yshow TB. pose proof (bytes_at_transport bsegs _ m _ _ _ TB MU ltac:(cbv [disjoint_from fst snd]; rewrite zbytes_length; unfold zlength in NL; lia)) as TB2.
    Ltac fin1 MU WM FRj ST2 := apply evtA_done;
      lazymatch goal with |- exists rax x1 x2 x3 x4 x5 x6 x7 q0 q1 q2 q3 q4 q5 q6 m' pc', MS _ _ (Z_to_bv 64 ?p) _ _ ?mx _ = _ /\ _ =>
        eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, mx, p end;
      split; [reflexivity|]; split; [| split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact ST2|]; split; [assumption|]; split; [exact FRj|];
                                       split; [assumption|]; split; [assumption|] ].
    zstepA; if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia.   (* [comment removed for export] *)
    + fin1 MU WM FRj ST2. { left. split; [lia| reflexivity]. }
      split; [lia|]. split; [lia|]. unfold A_SB. subst shT. assumption.
    + fin1 MU WM FRj ST2. { right. split; [lia| reflexivity]. }
      split; [lia|]. split; [lia|]. unfold A_SB. subst shT. assumption.
Qed.

Definition dlook (str : list Z) (e n : Z) : bool := (e + 7 <? n) && (znth str (e + 6) =? 92) && (znth str (e + 7) =? 117).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ADP_U2 : Z := 0x8b8d4.     (* [comment removed for export] *)
Lemma seg_u2 : forall (P : acc -> Prop) (rav sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (SQ FF B S n e cp OT OTn : Z) (str : list Z),
  mem_inv bsegs m ->
  bytes_at bsegs m S (zbytes str) -> Forall (fun c => 0 <= c < 256) str -> n = zlength str ->
  oshadow m OT OTn -> OT <= S -> S + n <= OT + OTn -> amem OT OTn -> OT + OTn <= alloc_ceiling ->
  0 <= e -> e + 5 < n -> n < 2^26 -> 0 < S -> S + n < 2^47 -> 0 <= cp < 2^16 ->
  pol P (oshw_lo OT) (oshw_hi OT OTn) -> pol P OT (OT + OTn) -> pol P 0x10000 0x603000 ->
  evtA bsegs P (fun ms' => exists (x0 x1 x2 x3 : word),
         (dlook str e n = false
          /\ ms' = DST rav sp gp tp t0 t1 t2 SQ x0 x1 x2 x3 a4 a5 a6 a7 S B n (Z_to_bv 64 A_LIT_Q) e FF (e + 5) t3 t4 t5 t6 F ADP_TAIL0 fc m)
      \/ (dlook str e n = true
          /\ ms' = DST rav sp gp tp t0 t1 t2 SQ (Z_to_bv 64 (S + (e + 6))) (Z_to_bv 64 117) (Z_to_bv 64 117) x3 a4 a5 a6 a7 S B n (Z_to_bv 64 A_LIT_Q) e FF (e + 5) t3 t4 t5 t6 F ADP_U2 fc m))
    (DST rav sp gp tp t0 t1 t2 SQ (Z_to_bv 64 cp) a1 a2 a3 a4 a5 a6 a7 S B n s7 e FF (e + 5) t3 t4 t5 t6 F ADP_SUR fc m).
Proof. aceil.
  intros until str. intros MI TB SF NL OSH OTS OTE OTH OTC E0 E5 N26 S0 SN CPR PTS PT PIMG.
  unfold DST, pol, ADP_SUR, ADP_U2, ADP_TAIL0, A_LIT_Q, dlook in *.
  destruct OSH as (OT8 & OTn0 & TSH). remember (blk_shadow OTn) as shT eqn:TSHeq in TSH. unfold A_SB in TSH.
  pose proof OTH as OTH'. unfold oshw_hi, A_SB, amem in OTH'. unfold oshw_lo, oshw_hi, A_SB, amem in PTS.
  pose proof OTC as OTC'. aceil.
  pose proof (zlength_nonneg str) as NL0.
  Ltac finL := apply evtA_done; eexists _, _, _, _; left; split; [| reflexivity].
  zstepA. rewrite (yswrap32_small (e + 7)) by lia.      (* [comment removed for export] *)
  zstepA. zstepA.                                         (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0; rewrite ?unsigned_lit, ?land64_small in K0 by lia.   (* [comment removed for export] *)
  { finL. apply andb_false_intro1. apply andb_false_intro1. apply Z.ltb_ge. lia. }
  zstepA. zstepA. zstepA. zext32 (e + 6).                 (* [comment removed for export] *)
  ugd.                                                    (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  eapply evtA_cut.
  { eapply (drdck_b8b86c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (S + (e + 6)) 2147450880 OT OTn);
      [ exact TSH | exact TSHeq | exact OT8 | lia | lia | lia | lia | clear -CEILB OTC' OTH'; Z.div_mod_to_equations; lia | lia | exact PTS ]. }
  cbv beta. intros ms1 (x1 & x2 & ->).
  pose proof (dstr_read m S str (e + 6) TB ltac:(lia)) as RD. pose proof (dstr_byte str (e + 6) SF) as C6.
  zstepA. clear RD. rewrite ?zxb_small, ?(u8_lit (znth str (e + 6))) by lia.   (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1; rewrite ?(u8_lit (znth str (e + 6))), ?unsigned_lit in K1 by lia.   (* [comment removed for export] *)
  { finL. apply andb_false_intro1. apply andb_false_intro2. apply Z.eqb_neq. lia. }
  zstepA. zstepA. zext32 (e + 7).                         (* [comment removed for export] *)
  ugd.                                                    (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  eapply evtA_cut.
  { eapply (drdck_b8b898 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (S + (e + 7)) 2147450880 OT OTn);
      [ exact TSH | exact TSHeq | exact OT8 | lia | lia | lia | lia | clear -CEILB OTC' OTH'; Z.div_mod_to_equations; lia | lia | exact PTS ]. }
  cbv beta. intros ms2 (x3 & x4 & ->).
  pose proof (dstr_read m S str (e + 7) TB ltac:(lia)) as RD. pose proof (dstr_byte str (e + 7) SF) as C7.
  zstepA. clear RD. rewrite ?zxb_small, ?(u8_lit (znth str (e + 7))) by lia.   (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  zstepA. if_cases K2; zify_cond K2; rewrite ?(u8_lit (znth str (e + 7))), ?unsigned_lit in K2 by lia.   (* [comment removed for export] *)
  { finL. apply andb_false_intro2. apply Z.eqb_neq. lia. }
  apply evtA_done. eexists (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), _. right. split.
  - rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite (proj2 (Z.eqb_eq _ _)) by lia. rewrite (proj2 (Z.eqb_eq _ _)) by lia. reflexivity.
  - replace (znth str (e + 7)) with 117 by lia. reflexivity.
Qed.

Definition ADP_J4 : Z := 0x8baa8.      (* [comment removed for export] *)
Definition ADP_RETH2 : Z := 0x8b8ec.   (* [comment removed for export] *)
Definition dspill14 (w0 w96 : word) (FF : Z) : list cell :=
  [C8 w0; C8 (Z_to_bv 64 0xffc00); C8 (Z_to_bv 64 (FF + 32)); C8 (Z_to_bv 64 0xd800); C8 (Z_to_bv 64 0xfc00);
   C8 (Z_to_bv 64 A_LIT_BS); C8 (Z_to_bv 64 A_LIT_BSL); C8 (Z_to_bv 64 A_LIT_SL); C8 (Z_to_bv 64 A_LIT_QT); C8 (Z_to_bv 64 A_LIT_CR);
   C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 w96; C8 (Z_to_bv 64 FF)].
Lemma dspill_split3 : forall m SQ w0 w96 FF sur cp,
  rw_cells bsegs m SQ (dspill w0 w96 FF sur cp) <-> rw_cells bsegs m SQ (dspill14 w0 w96 FF) /\ rw_cells bsegs m (SQ + 112) [C4 sur] /\ rw_cells bsegs m (SQ + 116) [C4 cp].
Proof. aceil.
  intros. unfold dspill.
  lazymatch goal with |- rw_cells _ _ _ ?cs <-> _ => rewrite <- (firstn_skipn 14 cs); rewrite (ycells_app bsegs m SQ (firstn 14 cs) (skipn 14 cs)) end.
  cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ app].
  rewrite (ycells_app bsegs m (SQ + 112) [C4 sur] [C4 cp]). cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ app].
  replace (SQ + 112 + 4) with (SQ + 116) by lia. unfold dspill14. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma seg_u3 : forall (HEX : ayhexToDigit_stmt) (P : acc -> Prop) (rav sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (w0 w96 sur0 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (SQ FF B S n e lo cp sur OT OTn : Z) (str : list Z),
  mem_inv bsegs m -> ay_statics m ->
  rw_cells bsegs m SQ (dspill w0 w96 FF sur0 (Z_to_bv 64 cp)) -> stk bsegs m lo SQ -> alloc_ceiling <= lo -> lo + 64 <= SQ -> SQ + 240 <= 2^47 -> SQ mod 32 = 0 ->
  bytes_at bsegs m (A_SB + SQ / 8 + 14) [Z_to_bv 8 0] ->
  bytes_at bsegs m S (zbytes str) -> Forall (fun c => 0 <= c < 256) str -> n = zlength str ->
  oshadow m OT OTn -> OT <= S -> S + n <= OT + OTn -> amem OT OTn -> OT + OTn <= alloc_ceiling ->
  0 <= e -> e + 11 < n -> n < 2^26 -> 0 < S -> S + n < 2^47 -> 0 <= cp < 2^16 ->
  (forall k, 0 <= k < 4 -> is_vhc (znth str (e + 8 + k)) = true) -> yhexToDigit 0 str (e + 8) = Some sur -> 0 <= sur < 2^16 ->
  pol P lo (SQ + 120) -> pol P (A_SB + SQ / 8 + 14) (A_SB + SQ / 8 + 15) -> pol P (oshw_lo OT) (oshw_hi OT OTn) -> pol P OT (OT + OTn) -> pol P 0x10000 0x603000 ->
  evtA bsegs P (fun ms' => exists (rax x1 x2 x3 x4 x5 x6 x7 q0 q1 q2 q3 q4 q5 q6 : word) (m' : mem),
       ms' = MS (mkR rax (Z_to_bv 64 SQ) gp tp q0 q1 q2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 (combine_surrogate cp sur)) x1 x2 x3 x4 x5 x6 x7
                      (Z_to_bv 64 (18446744073709551615 - S)) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 1) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 e) (Z_to_bv 64 (FF / 8 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (e + 11)) q3 q4 q5 q6)
                     F (Z_to_bv 64 ADP_J4) fc None m' (seg_rom bsegs)
       /\ 65536 <= combine_surrogate cp sur < 2097152
       /\ munch [(lo, SQ + 120)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo SQ /\ ay_statics m'
       /\ rw_cells bsegs m' SQ (dspill w0 w96 FF (Z_to_bv 64 sur) (Z_to_bv 64 (combine_surrogate cp sur))) /\ bytes_at bsegs m' (A_SB + SQ / 8 + 14) [Z_to_bv 8 0]
       /\ bytes_at bsegs m' S (zbytes str) /\ oshadow m' OT OTn)
    (DST rav sp gp tp t0 t1 t2 SQ (Z_to_bv 64 (S + (e + 6))) (Z_to_bv 64 117) (Z_to_bv 64 117) a3 a4 a5 a6 a7 S B n (Z_to_bv 64 A_LIT_Q) e FF (e + 5) t3 t4 t5 t6 F ADP_U2 fc m).
Proof. aceil.
  intros until str. intros MI STA FR ST CEIL LOQ SQH SQ32 SSH TB SF NL OSH OTS OTE OTH OTC E0 E11 N26 S0 SN CPR VHC HX SUR PSTK PSSH PTS PT PIMG.
  unfold DST, pol, ADP_U2, ADP_J4 in *. unfold dspill in FR.
  destruct OSH as (OT8 & OTn0 & TSH). remember (blk_shadow OTn) as shT eqn:TSHeq in TSH.
  pose proof (blk_shadow_length OTn ltac:(lia)) as SHL. rewrite <- TSHeq in SHL. unfold A_SB in TSH.
  assert (USQ : bv_unsigned (Z_to_bv 64 SQ) = SQ) by (apply unsigned_lit; lia).
  assert (OTLO : OT + OTn <= lo) by (clear -CEILB OTC CEIL; aceil; lia).
  pose proof OTH as OTH'. unfold oshw_hi, A_SB, amem in OTH'. unfold A_SB in SSH, PSSH.
  assert (SHB : 0 <= OT / 8 /\ 2147450880 + OT / 8 + (OTn + 7) / 8 <= 17594333495296) by (clear -CEILB OTH' OTC OTn0; aceil; Z.div_mod_to_equations; lia).
  pose proof (zlength_nonneg str) as NL0.
  pose proof (munch_refl [(lo, SQ + 120)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  (* [comment removed for export] *)
  pose proof (abytes_at_zslice m S str (e + 8) 4 TB ltac:(lia)) as HB4. rewrite RY_decode1.zslice4 in HB4 by lia.
  pose proof HX as HXL. unfold yhexToDigit in HXL. cbn [zbytes map] in HB4.
  replace (e + 8 + 1) with (e + 9) in * by lia. replace (e + 8 + 2) with (e + 10) in * by lia. replace (e + 8 + 3) with (e + 11) in * by lia.
  yhide TB.
  zstepA.                                                 (* [comment removed for export] *)
  zstepA. ugd.                                            (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  replace (S + (e + 6) + 2) with (S + (e + 8)) by lia.
  zstepA.                                                 (* [comment removed for export] *)
  stepA.                                                  (* [comment removed for export] *)
  lazymatch goal with FRx : rw_cells bsegs ?mx SQ _ |- _ => fold dspill in FRx; apply (proj1 (dspill_split3 _ _ _ _ _ _ _)) in FRx; destruct FRx as (FRa & FRb & FRc) end.
  pose proof HEX as HEX'. unfold ayhexToDigit_stmt, ayhexToDigit_rpost, wz, AY_HEXTODIGIT, pol in HEX'.
  specialize (HEX' P (SQ + 112) (S + (e + 8)) 0 lo (znth str (e + 8)) (znth str (e + 9)) (znth str (e + 10)) (znth str (e + 11)) sur OT OTn (Z_to_bv 64 ADP_RETH2) (Z_to_bv 64 SQ)).
  rewrite !USQ in HEX'. unfold dspill14 in FRa. unfold ADP_RETH2 in HEX'.
  call_spA HEX'.
  - red. split; [clear -CEILB SQ32; Z.div_mod_to_equations; lia| lia].   (* [comment removed for export] *)
  - eapply ay_statics_munch; [exact STA| exact MU| exact WM| constructor; [cbn; lia| constructor]].
  - exact FRb.
  - lia.
  - exact HB4.
  - replace (e + 8) with (e + 8 + 0) by lia. apply VHC. lia.
  - replace (e + 9) with (e + 8 + 1) by lia. apply VHC. lia.
  - replace (e + 10) with (e + 8 + 2) by lia. apply VHC. lia.
  - replace (e + 11) with (e + 8 + 3) by lia. apply VHC. lia.
  - exact HXL.
  - split; [exact OT8| split; [exact OTn0|]]. unfold A_SB. subst shT. assumption.
  - lia. - lia. - exact OTH. - exact OTC.
  - assumption.
  - assumption.
  - exact CEIL. - lia. - lia. - lia. - lia.
  - replace (A_SB + (SQ + 112) / 8) with (2147450880 + SQ / 8 + 14) by (unfold A_SB; clear -CEILB SQ32; Z.div_mod_to_equations; lia). assumption.
  - reflexivity. - reflexivity.
  - intros a k Ha Hk; apply PSTK; lia.
  - intros a k Ha Hk; apply PIMG; unfold AY_IMG_LO, AY_IMG_HI in *; lia.
  - intros a k Ha Hk; apply PSTK; lia.
  - intros a k Ha Hk; apply PSSH; unfold A_SB in Ha, Hk; clear -CEILB Ha Hk SQ32; Z.div_mod_to_equations; lia.
  - intros a k Ha Hk; apply PT; lia.
  - exact PTS.
  - cbv beta.
    assert (SL : 0 <= cp ≪ 10 < 67108864) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    Ltac nrm cp sur := rewrite ?(unsigned_lit cp), ?(unsigned_lit sur) by lia; rewrite ?(land64_small (cp ≪ 10)) by lia.
    zstepA. rewrite (ysx32_small cp) by lia.              (* [comment removed for export] *)
    zstepA. rewrite (yzx32_small sur) by lia.             (* [comment removed for export] *)
    zstepA. nrm cp sur.                                   (* [comment removed for export] *)
    zstepA. nrm cp sur.                                   (* [comment removed for export] *)
    zstepA. nrm cp sur.                                   (* [comment removed for export] *)
    zstepA. nrm cp sur.                                   (* [comment removed for export] *)
    zstepA. nrm cp sur.                                   (* [comment removed for export] *)
    zstepA. zstepA. nrm cp sur.                           (* [comment removed for export] *)
    pose proof (RY_decode1.land_lt_pow2 (cp ≪ 10) 1047552 20 ltac:(lia) ltac:(lia) ltac:(lia)) as LB1.
    pose proof (RY_decode1.land_lt_pow2 sur 1023 10 ltac:(lia) ltac:(lia) ltac:(lia)) as LB2.
    rewrite ?(unsigned_lit cp), ?(unsigned_lit sur), ?(unsigned_lit 1047552) by lia.
    rewrite ?(unsigned_lit (cp ≪ 10)) by lia. rewrite ?(unsigned_lit (Z.land (cp ≪ 10) 1047552)) by lia. rewrite ?(unsigned_lit (Z.land sur 1023)) by lia.
    assert (CSR : 65536 <= combine_surrogate cp sur < 2097152).
    { pose proof (combine_surrogate_bound cp sur ltac:(lia) ltac:(lia)) as CB0.
      rewrite <- (combine_surrogate_machine cp sur) in CB0 by lia. rewrite <- (combine_surrogate_machine cp sur) by lia.
      pose proof (proj2 (Z.lor_nonneg (Z.land (Z.shiftl cp 10) 1047552) (Z.land sur 1023)) (conj (proj1 LB1) (proj1 LB2))). lia. }
    rewrite ?(unsigned_lit (Z.lor (Z.land (cp ≪ 10) 1047552) (Z.land sur 1023))) by lia.
    rewrite ?(combine_surrogate_machine cp sur) by lia.
    zstepA.                                               (* [comment removed for export] *)
    zstepA.                                               (* [comment removed for export] *)
    zstepA.                                               (* [comment removed for export] *)
    stepA.                                                (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with FA : rw_cells bsegs ?mx SQ _, FB : rw_cells bsegs ?mx (SQ + 112) _, FC : rw_cells bsegs ?mx (SQ + 116) _ |- _ =>
      assert (FRj : rw_cells bsegs mx SQ (dspill w0 w96 FF (Z_to_bv 64 sur) (Z_to_bv 64 (combine_surrogate cp sur))))
        by (apply (proj2 (dspill_split3 _ _ _ _ _ _ _)); split; [exact FA| split; [exact FB| exact FC]]); clear FA FB FC end.
    lazymatch goal with X : stk bsegs ?mx lo _ |- _ => rename X into ST2 end.
    yshow TB. pose proof (bytes_at_transport bsegs _ m _ _ _ TB MU ltac:(cbv [disjoint_from fst snd]; rewrite zbytes_length; unfold zlength in NL; lia)) as TB2.
    apply evtA_done.
    lazymatch goal with |- exists rax x1 x2 x3 x4 x5 x6 x7 q0 q1 q2 q3 q4 q5 q6 m', MS _ _ _ _ _ ?mx _ = _ /\ _ =>
        eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, mx end.
    split; [reflexivity|]. split; [exact CSR|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST2|].
    split; [eapply ay_statics_munch; [exact STA| exact MU| exact WM| constructor; [cbn; lia| constructor]]|]. split; [exact FRj|].
    split; [assumption|]. split; [assumption|]. split; [lia|]. split; [lia|]. unfold A_SB. subst shT. assumption.
Qed.
End RC__2.
