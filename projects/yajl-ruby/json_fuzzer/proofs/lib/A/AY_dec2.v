(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep Arr Cells.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlParser YajlFactsBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 AImages Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AI_shadow AYajlRep AYajl_iface AY_hand AY_dec1.
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
Definition ADP_RET2 : Z := 0x8ac80.   (* [comment removed for export] *)
Definition ADP_RET3 : Z := 0x8ae50.   (* [comment removed for export] *)
Definition ADP_RET4 : Z := 0x8af54.   (* [comment removed for export] *)
Definition ADP_RET5 : Z := 0x8afc8.   (* [comment removed for export] *)
Definition ADP_LATCH : Z := 0x8af58.

End RC__1.
Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.

(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma yzext32_idiom : forall x, 0 <= x < 2^32 ->
  (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) ≪ 32)) ≫ 32) = x.
Proof. aceil.
  intros x Hx. rewrite (unsigned_lit x) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite unsigned_lit by (change (2^64) with (2^32 * 2^32); nia).
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.
Lemma yzext32_idiom' : forall x, 0 <= x < 2^32 -> (bv_unsigned (Z_to_bv 64 (x ≪ 32)) ≫ 32) = x.
Proof. aceil.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite unsigned_lit by (change (2^64) with (2^32 * 2^32); nia).
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.
Lemma yswrap32_small : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
Proof. aceil. intros x Hx. rewrite ybv_swrap32_eq. rewrite Z.mod_small by lia. lia. Qed.
Lemma u8_lit : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. aceil. intros c Hc. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.
Lemma land64_small : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
Proof. aceil. intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

End RC__2.
Ltac zext32 e := replace (Z.land e 4294967295) with e by (change 4294967295 with (Z.ones 32); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).

(* [comment removed for export] *)
Ltac dslow :=
  zstepA; change 7 with (Z.ones 3); rewrite ?Z.land_ones by lia; change (2^3) with 8;
  zstepA; let Kc := fresh "Kc" in if_cases Kc; zify_cond Kc;
  first [ exfalso; revert Kc; rewrite ?sxb_small, ?zxb_small, ?signed_lit_small by lia; intro Kc; lia
        | clear Kc; stepA ].

Ltac drdck_tac SLOW :=
  intros;
  lazymatch goal with
  | BS : u8arr _ _ _ ?shb, E : ?shb = blk_shadow ?On, PL : pol _ _ _ |- evtA _ _ _ (MS _ _ _ _ _ ?m _) =>
      unfold pol in PL;
      let L := fresh "BSlen" in pose proof (blk_shadow_length On ltac:(lia)) as L; rewrite <- E in L;
      pose proof (munch_refl ([] : list (Z * Z)) m) as MU; pose proof (wmono_refl asegs m) as WM
  end.

(* [comment removed for export] *)
Section RC__3.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma drdck_111718 : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 a1v a2v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr asegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA asegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x' y' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 SB) s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8ac58) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 SB) s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8ac48) fc None m (seg_rom asegs)).
Proof. aceil.
  drdck_tac idtac.
  lazymatch goal with BS : u8arr _ _ _ _ |- _ => shadow_cases BS E 1 end;
    [ apply evtA_done; eexists _, _; reflexivity
    | dslow; apply evtA_done; eexists _, _; reflexivity ].
Qed.

(* [comment removed for export] *)
Lemma drdck_111760 : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 a1v a2v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr asegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA asegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x' y' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 SB) s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8aca0) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 SB) s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8ac90) fc None m (seg_rom asegs)).
Proof. aceil.
  drdck_tac idtac.
  lazymatch goal with BS : u8arr _ _ _ _ |- _ => shadow_cases BS E 1 end;
    [ apply evtA_done; eexists _, _; reflexivity
    | dslow; apply evtA_done; eexists _, _; reflexivity ].
Qed.

(* [comment removed for export] *)
Lemma drdck_1117f0 : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 a2v a3v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr asegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA asegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1 x' y' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 SB) s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8ad30) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1 a2v a3v a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 SB) s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8ad20) fc None m (seg_rom asegs)).
Proof. aceil.
  drdck_tac idtac.
  lazymatch goal with BS : u8arr _ _ _ _ |- _ => shadow_cases BS E 1 end;
    [ apply evtA_done; eexists _, _; reflexivity
    | dslow; apply evtA_done; eexists _, _; reflexivity ].
Qed.

(* [comment removed for export] *)
Lemma drdck_111814 : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 a2v a3v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr asegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA asegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 E) x' y' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 SB) s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8ad54) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 E) a2v a3v a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 SB) s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8ad44) fc None m (seg_rom asegs)).
Proof. aceil.
  drdck_tac idtac.
  lazymatch goal with BS : u8arr _ _ _ _ |- _ => shadow_cases BS E 1 end;
    [ apply evtA_done; eexists _, _; reflexivity
    | shadow_slow; apply evtA_done; eexists _, _; reflexivity ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fsh_out : list cell := [C1 F1b; C1 F1b; C1 F1b; C1 F1b; C1 F8b; C1 F3b; C1 F3b; C1 F3b].
Definition fsh_in : list cell := [C1 F1b; C1 F1b; C1 F1b; C1 F1b; C1 (Z_to_bv 8 5); C1 F3b; C1 F3b; C1 F3b].

Lemma seg_head : forall (P : acc -> Prop) (rav sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (SQ FF B S n e beg c OT OTn : Z) (shT : list byte),
  mem_inv asegs m ->
  ov_read_bytes asegs m (Z_to_bv 64 (S + e)) 1 = Some [Z_to_bv 8 c] -> 0 <= c < 256 ->
  u8arr asegs m (2147450880 + OT / 8) shT -> shT = blk_shadow OTn -> OT mod 8 = 0 -> 0 <= OT -> OT <= S + e -> S + e + 1 <= OT + OTn -> OT + OTn <= alloc_ceiling ->
  rw_cells asegs m (FF / 8 + 2147450880) fsh_out ->
  (6303744 <= FF /\ (FF + 64 <= 2147446784 \/ 17594333495296 <= FF)) -> FF + 64 <= alloc_ceiling -> FF mod 64 = 0 ->
  0 <= beg <= e -> e < n -> n < 2^26 -> 0 < S ->
  pol P (2147450880 + OT / 8) (2147450880 + OT / 8 + (OTn + 7) / 8) -> pol P OT (OT + OTn) -> pol P (FF / 8 + 2147450880) (FF / 8 + 2147450880 + 8) ->
  evtA asegs P (fun ms' => exists (x1 x2 : word) (m' : mem), mem_inv asegs m' /\
     (  (c <> 92 /\ e + 1 < n /\ m' = m
         /\ ms' = MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 c) x1 x2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 (e + 1)) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 92) s7 (Z_to_bv 64 2147450880) (Z_to_bv 64 (-8)) (Z_to_bv 64 (FF / 8 + 2147450880)) (Z_to_bv 64 beg) t3 t4 t5 t6)
                     F (Z_to_bv 64 ADP_HEAD) fc None m' (seg_rom asegs))
     \/ (c <> 92 /\ e + 1 = n /\ m' = m
         /\ ms' = MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 c) x1 x2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 (e + 1)) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 92) s7 (Z_to_bv 64 2147450880) (Z_to_bv 64 (-8)) (Z_to_bv 64 (FF / 8 + 2147450880)) (Z_to_bv 64 beg) t3 t4 t5 t6)
                     F (Z_to_bv 64 ADP_EXIT) fc None m' (seg_rom asegs))
     \/ (c = 92 /\ munch [(FF / 8 + 2147450880 + 4, FF / 8 + 2147450880 + 5)] m m' /\ wmono asegs m m' /\ rw_cells asegs m' (FF / 8 + 2147450880) fsh_in
         /\ ms' = MS (mkR (Z_to_bv 64 ADP_RET2) (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 B) (Z_to_bv 64 (S + beg)) (Z_to_bv 64 (e - beg)) a3 a4 a5 a6 a7
                      (Z_to_bv 64 e) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 92) s7 (Z_to_bv 64 2147450880) (Z_to_bv 64 (-8)) (Z_to_bv 64 (FF / 8 + 2147450880)) (Z_to_bv 64 beg) t3 t4 t5 t6)
                     F (Z_to_bv 64 AY_BUF_APPEND) fc None m' (seg_rom asegs))))
    (MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 e) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 92) s7 (Z_to_bv 64 2147450880) (Z_to_bv 64 (-8)) (Z_to_bv 64 (FF / 8 + 2147450880)) (Z_to_bv 64 beg) t3 t4 t5 t6)
        F (Z_to_bv 64 ADP_HEAD) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until shT. intros MI HRD CR TSH TSHeq OT8 OT0 OTe OTe1 OTce FSH FF1 FF2 FF3 BE EN N26 S0 PTS PT PFS.
  unfold pol, ADP_HEAD, ADP_EXIT, ADP_RET2, AY_BUF_APPEND, fsh_out, fsh_in, F1b, F3b, F8b in *.
  set (SHF := FF / 8 + 2147450880) in *.
  assert (SHFR : 2147450880 <= SHF /\ SHF + 8 <= 17594333495296) by (subst SHF; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(SHF + 4, SHF + 5)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstepA. zstepA.                                         (* [comment removed for export] *)
  zstepA. zext32 e.                                       (* [comment removed for export] *)
  eapply evtA_cut.
  { eapply (drdck_111718 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (S + e) 2147450880 OT OTn);
      [ exact TSH | exact TSHeq | exact OT8 | exact OT0 | exact OTe | exact OTe1 | lia | clear -CEILB OTce OT0; Z.div_mod_to_equations; lia | lia | exact PTS ]. }
  cbv beta. intros ms1 (x1 & x2 & ->).
  zstepA.                                                 (* [comment removed for export] *)
  rewrite ?zxb_small, ?(u8_lit c) by lia.
  zstepA. if_cases K0; zify_cond K0; rewrite (u8_lit c) in K0 by lia; try rewrite (u8_lit c) by lia.   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    zstepA. rewrite (yswrap32_small (e + 1)) by lia.      (* [comment removed for export] *)
    zstepA. if_cases K1; zify_cond K1; rewrite ?(yswrap32_small (e + 1)), ?land64_small in K1 by lia.   (* [comment removed for export] *)
    + apply evtA_done. eexists _, _, m. split; [exact MI|]. left. split; [lia|]. split; [lia|]. split; [reflexivity| reflexivity].
    + stepA. apply evtA_done. eexists _, _, m. split; [exact MI|]. right; left. split; [lia|]. split; [lia|]. split; [reflexivity| reflexivity].
  - (* [comment removed for export] *)
    zstepA.                                               (* [comment removed for export] *)
    zstepA.                                               (* [comment removed for export] *)
    zstepA. zstepA.                                       (* [comment removed for export] *)
    zstepA. zext32 beg.                                   (* [comment removed for export] *)
    zstepA. rewrite (yswrap32_small (e - beg)) by lia.   (* [comment removed for export] *)
    stepA. stepA.                                         (* [comment removed for export] *)
    apply evtA_done. lazymatch goal with |- exists _ _ m', _ /\ _ => lazymatch goal with H : rw_cells asegs ?mx SHF _ |- _ => eexists x1, x2, mx end end.
    split; [assumption|]. right; right. split; [lia|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma seg_latch : forall (P : acc -> Prop) (rav sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word) (shb4 : byte)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (SQ FF B S n e2 p : Z),
  mem_inv asegs m ->
  rw_cells asegs m (FF / 8 + 2147450880) [C1 F1b; C1 F1b; C1 F1b; C1 F1b; C1 shb4; C1 F3b; C1 F3b; C1 F3b] ->
  (6303744 <= FF /\ (FF + 64 <= 2147446784 \/ 17594333495296 <= FF)) -> FF + 64 <= alloc_ceiling -> FF mod 64 = 0 ->
  0 <= p -> p + 1 <= n -> n < 2^26 -> 0 <= e2 < 2^32 ->
  pol P (FF / 8 + 2147450880) (FF / 8 + 2147450880 + 8) ->
  evtA asegs P (fun ms' => exists (m' : mem), mem_inv asegs m'
     /\ munch [(FF / 8 + 2147450880 + 4, FF / 8 + 2147450880 + 5)] m m' /\ wmono asegs m m' /\ rw_cells asegs m' (FF / 8 + 2147450880) fsh_out
     /\ (  (p + 1 < n /\ ms' = MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 (p + 1)) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 92) s7 (Z_to_bv 64 2147450880) (Z_to_bv 64 (-8)) (Z_to_bv 64 (FF / 8 + 2147450880)) (Z_to_bv 64 (p + 1)) t3 t4 t5 t6)
                     F (Z_to_bv 64 ADP_HEAD) fc None m' (seg_rom asegs))
        \/ (p + 1 = n /\ ms' = MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 (p + 1)) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 92) s7 (Z_to_bv 64 2147450880) (Z_to_bv 64 (-8)) (Z_to_bv 64 (FF / 8 + 2147450880)) (Z_to_bv 64 (p + 1)) t3 t4 t5 t6)
                     F (Z_to_bv 64 ADP_EXIT) fc None m' (seg_rom asegs))))
    (MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 e2) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 92) s7 (Z_to_bv 64 2147450880) (Z_to_bv 64 (-8)) (Z_to_bv 64 (FF / 8 + 2147450880)) (Z_to_bv 64 p) t3 t4 t5 t6)
        F (Z_to_bv 64 ADP_RET4) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until p. intros MI FSH FF1 FF2 FF3 P0 PN N26 E2 PFS.
  unfold pol, ADP_HEAD, ADP_EXIT, ADP_RET4, fsh_out, F1b, F3b, F8b in *.
  set (SHF := FF / 8 + 2147450880) in *.
  assert (SHFR : 2147450880 <= SHF /\ SHF + 8 <= 17594333495296) by (subst SHF; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(SHF + 4, SHF + 5)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstepA. rewrite (yswrap32_small (p + 1)) by lia.        (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  stepA.                                                  (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1; rewrite ?land64_small in K1 by lia.   (* [comment removed for export] *)
  - apply evtA_done. lazymatch goal with H : rw_cells asegs ?mx SHF _ |- _ => exists mx end.
    split; [assumption|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. left. split; [lia| reflexivity].
  - stepA. apply evtA_done. lazymatch goal with H : rw_cells asegs ?mx SHF _ |- _ => exists mx end.
    split; [assumption|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. right. split; [lia| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma seg_latch0 : forall (P : acc -> Prop) (rav sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s9 s11 t3 t4 t5 t6 : word) (shb4 : byte)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (SQ FF B S n e : Z),
  mem_inv asegs m ->
  rw_cells asegs m (FF / 8 + 2147450880) [C1 F1b; C1 F1b; C1 F1b; C1 F1b; C1 shb4; C1 F3b; C1 F3b; C1 F3b] ->
  (6303744 <= FF /\ (FF + 64 <= 2147446784 \/ 17594333495296 <= FF)) -> FF + 64 <= alloc_ceiling -> FF mod 64 = 0 ->
  0 <= e -> e + 6 <= n -> n < 2^26 ->
  pol P (FF / 8 + 2147450880) (FF / 8 + 2147450880 + 8) ->
  evtA asegs P (fun ms' => exists (m' : mem), mem_inv asegs m'
     /\ munch [(FF / 8 + 2147450880 + 4, FF / 8 + 2147450880 + 5)] m m' /\ wmono asegs m m' /\ rw_cells asegs m' (FF / 8 + 2147450880) fsh_out
     /\ (  (e + 6 < n /\ ms' = MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 (e + 6)) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 92) s7 (Z_to_bv 64 2147450880) (Z_to_bv 64 (-8)) (Z_to_bv 64 (FF / 8 + 2147450880)) (Z_to_bv 64 (e + 6)) t3 t4 t5 t6)
                     F (Z_to_bv 64 ADP_HEAD) fc None m' (seg_rom asegs))
        \/ (e + 6 = n /\ ms' = MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 (e + 6)) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 92) s7 (Z_to_bv 64 2147450880) (Z_to_bv 64 (-8)) (Z_to_bv 64 (FF / 8 + 2147450880)) (Z_to_bv 64 (e + 6)) t3 t4 t5 t6)
                     F (Z_to_bv 64 ADP_EXIT) fc None m' (seg_rom asegs))))
    (MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 e) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 92) s7 (Z_to_bv 64 2147450880) s9 (Z_to_bv 64 (FF / 8 + 2147450880)) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ADP_RET3) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until e. intros MI FSH FF1 FF2 FF3 E0 EN N26 PFS.
  unfold pol, ADP_HEAD, ADP_EXIT, ADP_RET3, fsh_out, F1b, F3b, F8b in *.
  set (SHF := FF / 8 + 2147450880) in *.
  assert (SHFR : 2147450880 <= SHF /\ SHF + 8 <= 17594333495296) by (subst SHF; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(SHF + 4, SHF + 5)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstepA. rewrite (yswrap32_small (e + 6)) by lia.        (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  stepA.                                                  (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  stepA.                                                  (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1; rewrite ?land64_small in K1 by lia.   (* [comment removed for export] *)
  - apply evtA_done. lazymatch goal with H : rw_cells asegs ?mx SHF _ |- _ => exists mx end.
    split; [assumption|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. left. split; [lia| reflexivity].
  - stepA. apply evtA_done. lazymatch goal with H : rw_cells asegs ?mx SHF _ |- _ => exists mx end.
    split; [assumption|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. right. split; [lia| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma seg_exit : forall (P : acc -> Prop) (rav sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s9 s10 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (SQ B S n e beg : Z),
  mem_inv asegs m -> 0 <= beg <= e -> e <= n -> n < 2^26 -> 0 < S -> S + n < 2^47 ->
  evtA asegs P (fun ms' => ms' = MS (mkR (Z_to_bv 64 ADP_RET5) (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 B) (Z_to_bv 64 (S + beg)) (Z_to_bv 64 (e - beg)) a3 a4 a5 a6 a7
                      (Z_to_bv 64 e) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) s6 s7 (Z_to_bv 64 2147450880) s9 s10 (Z_to_bv 64 beg) t3 t4 t5 t6)
                     F (Z_to_bv 64 AY_BUF_APPEND) fc None m (seg_rom asegs))
    (MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 e) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) s6 s7 (Z_to_bv 64 2147450880) s9 s10 (Z_to_bv 64 beg) t3 t4 t5 t6)
        F (Z_to_bv 64 ADP_EXIT) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until beg. intros MI BE EN N26 S0 SN. unfold ADP_EXIT, ADP_RET5, AY_BUF_APPEND.
  zstepA. zstepA.                                         (* [comment removed for export] *)
  zstepA. zext32 beg.                                     (* [comment removed for export] *)
  zstepA. rewrite (yswrap32_small (e - beg)) by lia.      (* [comment removed for export] *)
  stepA. stepA.                                           (* [comment removed for export] *)
  apply evtA_done. reflexivity.
Qed.
End RC__3.
