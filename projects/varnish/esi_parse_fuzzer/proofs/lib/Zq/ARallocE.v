(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA RA_mqq1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AIcpm9j ARtStmts ARtSscs AMTac AMallocI.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_ids [@CGOT; @CRM]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= hot_kdrop; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaLt.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition memcpy_post_z (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D S n : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(D, D + n)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' D [CB (Z.to_nat n) src] /\ bytes_at rsegs m' S src.

Lemma memcpy_spec_z : forall ra sp gp tp t0 t1 t2 s0 s1 (D S n : Z) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
  bytes_at rsegs m S src -> length src = Z.to_nat n ->
  rw_cells rsegs m D [CB (Z.to_nat n) junk] ->
  (S + n <= D \/ D + n <= S) ->
  0 <= n -> 0 <= S -> S + n < 2^64 -> 0 <= D -> D + n < 2^64 ->
  mem_inv rsegs m ->
  evt rsegs (memcpy_post_z ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D S n src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xa1b8c) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros SRC LEN DST SEP N0 S0 SHI D0 DHI MI.
  assert (U0 : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (U1 : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (U2 : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { apply (memcpy_spec ra sp gp tp t0 t1 t2 s0 s1 _ _ _ a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m src junk);
      rewrite ?U0, ?U1, ?U2; [exact SRC | exact LEN | exact DST | exact SEP | exact MI]. }
  intros ms' PO. unfold memcpy_post in PO. unfold memcpy_post_z.
  (first [ dex15 PO as x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 m'; dand6 PO as E MU WM MI' RW BA | dand21 PO as x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 m' E MU WM MI' RW BA | destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & E & MU & WM & MI' & RW & BA) ]).
  rewrite ?U0, ?U1, ?U2 in *.
  exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, m'.
  split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact RW|]. exact BA.
Qed.

(* [comment removed for export] *)
Lemma used_size_words : forall n0, 0 <= n0 < 2^48 ->
  Z.lor (Z.shiftl (size_hi n0 mod 2^16) 32 mod 2^64) (n0 mod 2^32) = n0.
Proof.
  intros n0 H. pose proof (used_size_roundtrip n0 H) as R. unfold used_size_decode, size_lo in R.
  rewrite Z.mod_small; [exact R|].
  rewrite Z.shiftl_mul_pow2 by lia. pose proof (Z.mod_pos_bound (size_hi n0) (2^16)). lia.
Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac slia ::= first [ exact I | lazymatch goal with |- _ /\ _ => split; slia | |- _ => lia end ].
Ltac aobjL H := let A := fresh "A" H in pose proof (proj1 H) as A; aobj_lin1 A.

Notation wz z := (Z_to_bv 64 z) (only parsing).
Definition realloc_mid2_entry : Z := 0x37bfc.
Definition realloc_epi_entry : Z := 0x37c90.
Definition realloc_tail_entry : Z := 0x59038.

Section CEIL.
Context {Clg : Ceiling}.

(* [comment removed for export] *)
Definition realloc_mid2_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (fp lo p n n0 r b1 : Z) (src uj : list byte) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (fp - 2208) -> lo <= fp - 2208 -> alloc_ceiling <= lo -> fp <= 2^47 ->
    sp = wz (fp + -2208) -> a0 = wz r -> s0 = wz (fp + -2136) -> s1 = wz p -> s2 = wz 0xb1558 -> s3 = wz n ->
    0 < r -> r + n <= alloc_ceiling -> 16 <= p -> p + n0 <= alloc_ceiling -> 1 <= n -> 0 <= n0 < 2^48 -> 0 <= b1 < 256 ->
    (p + n0 <= r \/ r + n <= p + -16) ->                                                   (* [comment removed for export] *)
    ro_cells rsegs m (p + -16) [C1 (Z_to_bv 8 CHUNK_ALLOCATED); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n0)); C4 (wz n0)] ->  (* [comment removed for export] *)
    ro_cells rsegs m 0xa8b98 [C8 (wz 0xaaa10)] -> ro_cells rsegs m 0xaaa10 [C8 (wz 0xa1b8c)] ->   (* [comment removed for export] *)
    bytes_at rsegs m p src -> length src = Z.to_nat (Z.min n n0) ->                         (* [comment removed for export] *)
    rw_cells rsegs m r [CB (Z.to_nat (Z.min n n0)) uj] ->                                 (* [comment removed for export] *)
    (forall (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
        mem_inv rsegs m' -> munch [(r, r + Z.min n n0)] m m' -> wmono rsegs m m' ->
        rw_cells rsegs m' r [CB (Z.to_nat (Z.min n n0)) src] -> bytes_at rsegs m' p src ->
        stk rsegs m' lo (fp - 2208) ->
        evt rsegs Q (MS (mkR (wz 0x37c90) (wz (fp + -2208)) gp tp t0' t1' t2' (wz (fp + -2136)) (wz p)
                         (wz 0xb1558) (wz p) (wz 0) (wz 0) (wz (fp + -2136)) (wz 1) a6' a7'
                         (wz 0xb1558) (wz (Z.min n n0)) (wz r) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (wz dealloc_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz realloc_mid2_entry) fc None m (seg_rom rsegs)).

Theorem realloc_mid2_ok : realloc_mid2_stmt.
Proof.
  pose proof alloc_ceiling_val as CE0. unfold realloc_mid2_stmt. intros until Q.
  intros MI ST LOLE CEIL F1 SP A0 S0 S1 S2 S3 RR RHI P16 PHI N1 N0R B1R SEPC HDR CGOT CRM SRC LEN DST K.
  unfold realloc_mid2_entry, dealloc_entry in *. subst sp a0 s0 s1 s2 s3.
  pose proof (munch_refl [(r, r + Z.min n n0)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (MN : 1 <= Z.min n n0 <= n /\ Z.min n n0 <= n0 \/ Z.min n n0 = n0 /\ n0 <= n) by lia.
  unfold CHUNK_ALLOCATED in HDR.
  amz. (* [comment removed for export] *)
  amz. br_not_taken. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  amz. br_taken. (* [comment removed for export] *)
  amz. amz. amz. (* [comment removed for export] *)
  amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  assert (HR16 : 0 <= size_hi n0 < 2^16).
  { unfold size_hi. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  replace (bv_unsigned (zx16 (Z_to_bv 64 (size_hi n0)))) with (size_hi n0 mod 2^16)
    by (unfold zx16; rewrite !unsigned_lit; [reflexivity| lia | pose proof (Z.mod_pos_bound (size_hi n0) (2^16)); rewrite unsigned_lit by lia; lia]).
  replace (bv_unsigned (zx32 (Z_to_bv 64 n0))) with (n0 mod 2^32)
    by (unfold zx32; rewrite !unsigned_lit; [reflexivity| lia | pose proof (Z.mod_pos_bound n0 (2^32)); rewrite unsigned_lit by lia; lia]).
  change 18446744073709551616 with (2^64).
  rewrite (used_size_words n0) by lia.
  amz. if_cases Kmin; zify_cond Kmin.
  - (* [comment removed for export] *)
    replace (Z.min n n0) with n in * by lia.
    amz. amz. amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    callx (memcpy_spec_z _ _ _ _ _ _ _ _ _ r p n).
    match goal with H : stk _ _ _ _ |- _ => rename H into ST' end.
    do 7 amz. (* [comment removed for export] *)
    match goal with H : munch _ _ ?m1, W : wmono rsegs _ ?m1, M : mem_inv rsegs ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      rename H into MUf; rename W into WMf; rename M into MIf end.
    eapply K; try eassumption.
  - (* [comment removed for export] *)
    replace (Z.min n n0) with n0 in * by lia.
    amz. (* [comment removed for export] *)
    amz. amz. amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    callx (memcpy_spec_z _ _ _ _ _ _ _ _ _ r p n0).
    match goal with H : stk _ _ _ _ |- _ => rename H into ST' end.
    do 7 amz.
    match goal with H : munch _ _ ?m1, W : wmono rsegs _ ?m1, M : mem_inv rsegs ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      rename H into MUf; rename W into WMf; rename M into MIf end.
    eapply K; try eassumption.
Qed.

(* [comment removed for export] *)
Definition realloc_tail_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fp lo : Z)
         (w0 w8 w12 w2056 s6v s5v s4v s3v s2v s1v s0v ra0 : word) (cs16 : list cell) (j32 pad1 pad2 : list byte)
         (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (fp - 2144) -> lo <= fp - 2144 -> 0 <= fp - 2144 -> fp <= 2^47 ->
    sp = wz (fp + -2144) ->
    rw_cells rsegs m (fp + -2144) [CB 8 pad2] ->
    rw_cells rsegs m (fp + -2136) [C8 w0] -> rw_cells rsegs m (fp + -2128) [C4 w8] -> rw_cells rsegs m (fp + -2124) [C4 w12] ->
    rw_cells rsegs m (fp + -2120) cs16 -> cells_size cs16 = 16%nat -> rw_cells rsegs m (fp + -2104) [CB 2024 j32] ->
    rw_cells rsegs m (fp + -80) [C8 w2056] -> rw_cells rsegs m (fp + -72) [CB 8 pad1] ->
    rw_cells rsegs m (fp + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
    (stk rsegs m lo fp ->
        evt rsegs Q (MS (mkR ra0 (wz fp) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra0) fc None m (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz realloc_tail_entry) fc None m (seg_rom rsegs)).

Theorem realloc_tail_ok : realloc_tail_stmt.
Proof.
  unfold realloc_tail_stmt. intros until Q. intros MI ST LOLE F0 F1 SP P2 O0 O8 O12 O16 S16 O32 O2056 P1 SAV K.
  unfold realloc_tail_entry in *. subst sp.
  pose proof (munch_refl [(fp - 2144, fp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  replace (fp - 2144) with (fp + -2144) in ST by lia.
  do 11 amz. (* [comment removed for export] *)
  release_frame P2 ST (fp + -2136).
  release_frame O0 ST (fp + -2128).
  release_frame O8 ST (fp + -2124).
  release_frame O12 ST (fp + -2120).
  eapply stk_release in O16; [| exact ST| lia]. clear ST. rename O16 into ST. rewrite S16 in ST.
  lazymatch type of ST with stk _ _ _ ?h => replace h with (fp + -2104) in ST by (cbn; lia) end.
  release_frame O32 ST (fp + -80).
  release_frame O2056 ST (fp + -72).
  release_frame P1 ST (fp + -64).
  release_frame SAV ST fp.
  apply K. exact ST.
Qed.

(* [comment removed for export] *)
Definition realloc_epi_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fp lo r : Z)
         (w0 w8 w12 w2056 s6v s5v s4v s3v s2v s1v s0v ra0 c0 c8 c16 c24 c32 : word) (cs16 : list cell) (j32 pad1 pad2 js0 : list byte)
         (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (fp - 2208) -> lo <= fp - 2208 -> 0 <= fp - 2208 -> fp <= 2^47 ->
    sp = wz (fp + -2208) -> s4 = wz r -> 0 < r < 2^64 ->
    rw_cells rsegs m (fp + -2208) [C8 c0; C8 c8; C8 c16; C8 c24; C8 c32; C8 (wz 0x37b80)] ->   (* [comment removed for export] *)
    rw_cells rsegs m (fp + -2160) [CB 8 js0; C8 (wz 0x59038)] ->                            (* [comment removed for export] *)
    rw_cells rsegs m (fp + -2144) [CB 8 pad2] ->
    rw_cells rsegs m (fp + -2136) [C8 w0] -> rw_cells rsegs m (fp + -2128) [C4 w8] -> rw_cells rsegs m (fp + -2124) [C4 w12] ->
    rw_cells rsegs m (fp + -2120) cs16 -> cells_size cs16 = 16%nat -> rw_cells rsegs m (fp + -2104) [CB 2024 j32] ->
    rw_cells rsegs m (fp + -80) [C8 w2056] -> rw_cells rsegs m (fp + -72) [CB 8 pad1] ->
    rw_cells rsegs m (fp + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
    (stk rsegs m lo fp ->
        evt rsegs Q (MS (mkR ra0 (wz fp) gp tp t0 t1 t2 s0v s1v (wz r) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra0) fc None m (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz realloc_epi_entry) fc None m (seg_rom rsegs)).

Theorem realloc_epi_ok : realloc_epi_stmt.
Proof.
  unfold realloc_epi_stmt. intros until Q. intros MI ST LOLE F0 F1 SP S4 RR C48 C16 P2 O0 O8 O12 O16 S16 O32 O2056 P1 SAV K.
  unfold realloc_epi_entry in *. subst sp s4.
  pose proof (munch_refl [(fp - 2208, fp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  replace (fp - 2208) with (fp + -2208) in ST by lia.
  amz. (* [comment removed for export] *)
  do 7 amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. amz. (* [comment removed for export] *)
  release_frame C48 ST (fp + -2160).
  release_frame C16 ST (fp + -2144).
  eapply realloc_tail_ok; [ exact MI | exact ST | lia | lia | lia | reflexivity | try eassumption .. | ].
  all: first [ eassumption | intros ST'; eapply K; exact ST' ].
Qed.

(* [comment removed for export] *)
Definition realloc_epi0_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fp lo : Z)
         (w0 w8 w12 w2056 s6v s5v s4v s3v s2v s1v s0v ra0 c0 c8 c16 c24 c32 e0 : word) (cs16 : list cell) (j32 pad1 pad2 js0 : list byte)
         (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (fp - 2208) -> lo <= fp - 2208 -> alloc_ceiling <= lo -> fp <= 2^47 ->
    sp = wz (fp + -2208) -> a0 = wz 0 ->
    164 <= bv_unsigned tp -> bv_unsigned tp <= kHighMemBeg ->
    rw_cells rsegs m (bv_unsigned tp + -164) [C4 e0] ->
    rw_cells rsegs m (fp + -2208) [C8 c0; C8 c8; C8 c16; C8 c24; C8 c32; C8 (wz 0x37b80)] ->   (* [comment removed for export] *)
    rw_cells rsegs m (fp + -2160) [CB 8 js0; C8 (wz 0x59038)] ->                            (* [comment removed for export] *)
    rw_cells rsegs m (fp + -2144) [CB 8 pad2] ->
    rw_cells rsegs m (fp + -2136) [C8 w0] -> rw_cells rsegs m (fp + -2128) [C4 w8] -> rw_cells rsegs m (fp + -2124) [C4 w12] ->
    rw_cells rsegs m (fp + -2120) cs16 -> cells_size cs16 = 16%nat -> rw_cells rsegs m (fp + -2104) [CB 2024 j32] ->
    rw_cells rsegs m (fp + -80) [C8 w2056] -> rw_cells rsegs m (fp + -72) [CB 8 pad1] ->
    rw_cells rsegs m (fp + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
    (forall (t0' t1' t2' a1' : word) (m' : word -> option byte),
        stk rsegs m' lo fp -> mem_inv rsegs m' ->
        munch [(fp - 2176, fp - 2160); (bv_unsigned tp + -164, bv_unsigned tp + -160)] m m' -> wmono rsegs m m' ->
        rw_cells rsegs m' (bv_unsigned tp + -164) [C4 (wz 12)] ->
        evt rsegs Q (MS (mkR ra0 (wz fp) gp tp t0' t1' t2' s0v s1v (wz 0) a1' a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra0) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz realloc_mid2_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)

End CEIL.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
