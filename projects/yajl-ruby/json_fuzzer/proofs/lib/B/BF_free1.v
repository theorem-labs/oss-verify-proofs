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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_place BF_kit BF_kit2 BF_poison BF_free_kit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac post_call_rw segs m rw :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  rw MUc;
  (* [comment removed for export] *)
  try match goal with Hs : bv_unsigned ?sp1 = (bv_unsigned ?sp0 + ?k)%Z |- _ => rewrite ?Hs in MUc end;
  lazymatch type of MUc with
  | munch ?W m ?m' =>
      repeat match goal with
      | H : munch ?Wq ?mq m |- _ =>
          apply (munch_trans Wq mq m m') in H;
          [ | eapply (munch_weaken W Wq m m'); [ first [ sub_fp_fast | unfold sub_fp; cbn [outside]; intros; slia ] | exact MUc ] ]
      end;
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).
Local Tactic Notation "callA_rw" uconstr(SPEC) tactic3(rw) :=
  lazymatch goal with
  | |- evtA ?segs _ _ (MS _ _ _ _ _ ?m _) => eapply evtA_cut; [ eapply SPEC | post_call_rw segs m rw; ret_pc_lit ]
  end.
Local Tactic Notation "call_spA_rw" uconstr(SPEC) tactic3(rw) :=
  lazymatch goal with
  | |- evtA _ _ _ (MS (TNode _ None (TNode _ (Some (Z_to_bv 64 (bv_unsigned ?sp + ?k))) _)) _ _ _ _ _ _) =>
      name_sp sp k; callA_rw SPEC rw; unname_sp
  | |- evtA _ _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?sp + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      name_sp sp k; callA_rw SPEC rw; unname_sp
  | _ => callA_rw SPEC rw
  end.
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma land_mul256_small : forall k c, 0 <= k -> 0 <= c < 4 -> Z.land (256 * k) c = 0.
Proof. aceil.
  intros k c Hk Hc. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 2).
  - replace (256 * k) with (Z.shiftl (64 * k) 2) by (rewrite Z.shiftl_mul_pow2 by lia; lia). rewrite Z.shiftl_spec_low by lia. reflexivity.
  - rewrite (Z.bits_above_log2 c i); [apply andb_false_r| lia|].
    destruct (Z.eq_dec c 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; [lia|]. apply (Z.lt_le_trans _ (2^2)); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma hdr_cas_val : forall k, 0 <= k -> Z.lxor (256 * k + 2) (Z.land (Z.lxor (256 * k + 2) 3) 255) = 256 * k + 3.
Proof. aceil.
  intros k Hk.
  assert (E2 : 256 * k + 2 = Z.lxor (256 * k) 2) by (apply Z.add_nocarry_lxor; apply land_mul256_small; lia).
  assert (E3 : 256 * k + 3 = Z.lxor (256 * k) 3) by (apply Z.add_nocarry_lxor; apply land_mul256_small; lia).
  assert (E1 : 256 * k + 1 = Z.lxor (256 * k) 1) by (apply Z.add_nocarry_lxor; apply land_mul256_small; lia).
  replace (Z.lxor (256 * k + 2) 3) with (256 * k + 1) by (rewrite E2, Z.lxor_assoc; change (Z.lxor 2 3) with 1; exact E1).
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2^8) with 256.
  replace ((256 * k + 1) mod 256) with 1 by (rewrite Z.add_comm, Z.mul_comm, Z_mod_plus_full; reflexivity).
  rewrite E2, Z.lxor_assoc. change (Z.lxor 2 1) with 3. symmetry. exact E3.
Qed.

Section DEALLOC.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variable Q : machine_state -> Prop.
Variables (m : mem) (lo cb B : Z) (b1 nhi nlo frees freed : Z) (aidw uw : word) (TSD CTX T : Z).
Notation INST := 0xaaf58.
Definition hk : Z := b1 + 256 * nhi.          (* [comment removed for export] *)
Definition n : Z := nhi * 2^32 + nlo.          (* [comment removed for export] *)

Hypothesis SK : stk bsegs m lo (bv_unsigned sp).
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 96.
Hypothesis SPH : bv_unsigned sp <= 2^47.
Hypothesis MI : mem_inv bsegs m.
Hypothesis HCB : 0x603000 <= cb /\ cb + 24 <= alloc_ceiling /\ cb mod 16 = 0.
Hypothesis HB1 : 0 <= b1 < 256 /\ Z.land b1 3 = 1.          (* [comment removed for export] *)
Hypothesis HNHI : 0 <= nhi < 256.                           (* [comment removed for export] *)
Hypothesis HNLO : 0 <= nlo < 2^32.
Hypothesis HDR : rw_cells bsegs m cb [C4 (Z_to_bv 64 (2 + 256 * hk)); C4 (Z_to_bv 64 nlo); C8 aidw].   (* [comment removed for export] *)
Hypothesis UW : rw_cells bsegs m (cb + 16) [C8 uw].                                               (* [comment removed for export] *)
Hypothesis HK1 : rw_cells bsegs m 0x140088 [C8 (Z_to_bv 64 0)].                                 (* [comment removed for export] *)
Hypothesis TC : thread_cells m tp TSD CTX T.
Hypothesis HT1 : 0x5d0810 <= TSD. Hypothesis HT2 : TSD + 8 <= 0x603000.
Hypothesis HC : placed_s CTX 4096.        (* [comment removed for export] *)
Hypothesis HTp : placed_s T 4096.         (* [comment removed for export] *)
Hypothesis HTP : 0x5d0810 + 88 <= bv_unsigned tp < 0x603000.
Hypothesis STATS : rw_cells bsegs m (T + 2824) [C8 (Z_to_bv 64 frees); C8 (Z_to_bv 64 freed)].   (* [comment removed for export] *)
Hypothesis HCBT : cb + 24 <= T \/ T + 4096 <= cb.
Hypothesis HCBC : cb + 24 <= CTX \/ CTX + 4096 <= cb.
Hypothesis HTC : CTX + 160 <= T \/ T + 4096 <= CTX.
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k).
Hypothesis PDAT : forall a k, 0xa5000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PCTX : P (Z_to_bv 64 (CTX + 152), 8%nat).
Hypothesis PT : forall a k, T <= a -> a + Z.of_nat k <= T + 4096 -> P (Z_to_bv 64 a, k).
Hypothesis PCH : forall a k, cb <= a -> a + Z.of_nat k <= cb + 24 -> P (Z_to_bv 64 a, k).

(* [comment removed for export] *)
(* [comment removed for export] *)
End DEALLOC.

Section QCHUNK.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variable Q : machine_state -> Prop.
Variables (m : mem) (lo hi cb B A len : Z) (ws : list word) (b1 nhi nlo : Z) (aidw uw : word) (TSD CTX T : Z).
Variables (D : depot_ifc) (ds : DS D).
Notation INST := 0xaaf58.
Notation n := (nhi * 2^32 + nlo).
Definition key : list Z := map bv_unsigned (firstn (Z.to_nat len) ws).
Definition ds' := fst (dput D ds key).
Definition fid := snd (dput D ds key).

Hypothesis SK : stk bsegs m lo (bv_unsigned sp).
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 272.
Hypothesis SPH : bv_unsigned sp <= B.
Hypothesis HB : B + 16 = A /\ A + 240 <= hi.
Hypothesis HI : hi < 2^47.
Hypothesis MI : mem_inv bsegs m.
Hypothesis HCB : 0x603000 <= cb /\ cb + 24 <= alloc_ceiling /\ cb mod 16 = 0.
Hypothesis HNHI : 0 <= nhi < 256.
Hypothesis HNLO : 0 <= nlo < 2^32.
Hypothesis HDR : rw_cells bsegs m cb [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 nhi); C4 (Z_to_bv 64 nlo); C8 aidw].
Hypothesis UW : rw_cells bsegs m (cb + 16) [C8 uw].
Hypothesis TC : thread_cells m tp TSD CTX T.
Hypothesis TCTX : rw_cells bsegs m T [C8 (Z_to_bv 64 CTX)].                 (* [comment removed for export] *)
Hypothesis TID : rw_cells bsegs m (CTX + 8) [C4 (Z_to_bv 64 0)].            (* [comment removed for export] *)
Hypothesis HT1 : 0x5d0810 <= TSD. Hypothesis HT2 : TSD + 8 <= 0x603000.
Hypothesis HC : placed_s CTX 4096.        (* [comment removed for export] *)
Hypothesis HTp : placed_s T 4096.         (* [comment removed for export] *)
Hypothesis HTP : 0x5d0810 + 88 <= bv_unsigned tp < 0x603000.
Hypothesis HCBT : cb + 24 <= T \/ T + 4096 <= cb.
Hypothesis HCBC : cb + 24 <= CTX \/ CTX + 4096 <= cb.
Hypothesis HTC : CTX + 160 <= T \/ T + 4096 <= CTX.
(* [comment removed for export] *)
Hypothesis OBJ : rw_cells bsegs m B [C8 (Z_to_bv 64 A); C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 0)].
Hypothesis TR : u64arr bsegs m A ws.
Hypothesis LEN : 1 <= len <= Z.of_nat (length ws).
Hypothesis LWS : Z.of_nat (length ws) = 30.
(* [comment removed for export] *)
Hypothesis DEPOT : depot_put_spec D P.
Hypothesis DRm : DR D ds m.
Hypothesis DSstk : forall jv, down D ds jv -> iv_sep (lo, hi) jv.
Hypothesis DScb : forall jv, down D ds jv -> iv_sep (cb, cb + 24) jv.
Hypothesis DST : forall jv, down D ds jv -> iv_sep (T, T + 4096) jv.
Hypothesis DSctx : forall jv, down D ds jv -> iv_sep (CTX, CTX + 4096) jv.
Hypothesis DSimg : forall jv, down D ds jv -> iv_sep (0, 0x140810) jv.
Hypothesis DSmusl : forall jv, down D ds jv -> iv_sep (0x5d0810, 0x603000) jv.   (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= hi -> P (Z_to_bv 64 a, k).
Hypothesis PDAT : forall a k, 0xa5000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PRO : forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x31000 -> P (Z_to_bv 64 a, k).
Hypothesis PCTX : forall a k, CTX <= a -> a + Z.of_nat k <= CTX + 4096 -> P (Z_to_bv 64 a, k).
Hypothesis PT : forall a k, T <= a -> a + Z.of_nat k <= T + 4096 -> P (Z_to_bv 64 a, k).
Hypothesis PCH : forall a k, cb <= a -> a + Z.of_nat k <= cb + 24 -> P (Z_to_bv 64 a, k).
Hypothesis PDOWN : forall jv a k, down D ds jv -> fst jv <= a -> a + Z.of_nat k <= snd jv -> P (Z_to_bv 64 a, k).

(* [comment removed for export] *)
(* [comment removed for export] *)
End QCHUNK.

Section ENQ1.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variable Q : machine_state -> Prop.
Variables (m : mem) (lo T CA B cb n cnt first last bnext bsz bcnt qb : Z) (its : list word).

Hypothesis SK : stk bsegs m lo (bv_unsigned sp).
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 64.
Hypothesis SPH : bv_unsigned sp <= 2^47.
Hypothesis MI : mem_inv bsegs m.
Hypothesis HTp : placed_s T 4096.
Hypothesis QC : rw_cells bsegs m (T + 80) [C8 (Z_to_bv 64 cnt); C8 (Z_to_bv 64 first); C8 (Z_to_bv 64 last); C8 (Z_to_bv 64 qb)].
Hypothesis HCNT : 0 < cnt < 2^63.
Hypothesis HL : 0x603000 <= last /\ last + 8192 <= alloc_ceiling.
Hypothesis HLT : last + 8192 <= T \/ T + 4096 <= last.
Hypothesis LB : rw_cells bsegs m last [C8 (Z_to_bv 64 bnext); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 bcnt)].
Hypothesis ITS : u64arr bsegs m (last + 24) its.
Hypothesis LITS : Z.of_nat (length its) = 1021.
Hypothesis HBC : 0 <= bcnt < 1021.
Hypothesis HBSZ : 0 <= bsz /\ 0 <= n /\ bsz + n < 2^64.
Hypothesis HQB : 0 <= qb /\ qb + n < 2^64.
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k).
Hypothesis PT : forall a k, T <= a -> a + Z.of_nat k <= T + 4096 -> P (Z_to_bv 64 a, k).
Hypothesis PLB : forall a k, last <= a -> a + Z.of_nat k <= last + 8192 -> P (Z_to_bv 64 a, k).

(* [comment removed for export] *)
Lemma enqueue1_walk :
  (forall m' (a1' a2' a5' a6' a7' : word),
     mem_inv bsegs m' -> stk bsegs m' lo (bv_unsigned sp) -> wmono bsegs m m' ->
     munch [(bv_unsigned sp - 64, bv_unsigned sp); (last + 8, last + 24); (last + 24 + 8 * bcnt, last + 24 + 8 * bcnt + 8); (T + 104, T + 112)] m m' ->
     rw_cells bsegs m' (T + 80) [C8 (Z_to_bv 64 cnt); C8 (Z_to_bv 64 first); C8 (Z_to_bv 64 last); C8 (Z_to_bv 64 (qb + n))] ->
     rw_cells bsegs m' last [C8 (Z_to_bv 64 bnext); C8 (Z_to_bv 64 (bsz + n)); C8 (Z_to_bv 64 (bcnt + 1))] ->
     u64arr bsegs m' (last + 24) (upd its (Z.to_nat bcnt) (Z_to_bv 64 cb)) ->
     evtA bsegs P Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (T + 80)) a1' a2' (Z_to_bv 64 cb) (Z_to_bv 64 n) a5' a6' a7'
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  evtA bsegs P Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (T + 80)) (Z_to_bv 64 CA) (Z_to_bv 64 B) (Z_to_bv 64 cb) (Z_to_bv 64 n) a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x36ec8) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros CONT.
  pose proof HTp as HT. plopen HT. assert (HT : 0x1000 <= T /\ T + 4096 <= alloc_ceiling) by (split; assumption).
  pose proof LOC as LOC0. aceil.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (MU : munch [(bv_unsigned sp - 64, bv_unsigned sp); (last + 8, last + 24); (last + 24 + 8 * bcnt, last + 24 + 8 * bcnt + 8); (T + 104, T + 112)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  carve_frame 64%nat SK.
  frame_stores 8 FR. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1; [| exfalso; revert K1; rewrite ?unsigned_lit by lia; lia]. clear K1.
  zstepA. if_cases K2; zify_cond K2. { exfalso. revert K2. rewrite ?unsigned_lit by lia. lia. } clear K2.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *) rewrite (Z.shiftl_mul_pow2 bcnt 3) by lia. change (2^3) with 8.
  do 3 zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (u64arr_store_ok bsegs mx (last + 24) its bcnt (Z_to_bv 64 (last + 24 + 8 * bcnt)) ITS ltac:(lia) ltac:(reflexivity)) as SOK;
    pose proof (u64arr_write bsegs mx (last + 24) its bcnt (Z_to_bv 64 cb) ITS ltac:(lia)) as ITS' end.
  replace (last + bcnt * 8 + 24) with (last + 24 + 8 * bcnt) by lia.
  stepA. (* [comment removed for export] *)
  all: lazymatch goal with |- P _ => apply PLB; lia | _ => idtac end.
  clear ITS. store_done. rename ITS' into ITS.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  do 8 zstepA. (* [comment removed for export] *)
  release_frame FR SK (bv_unsigned sp).
  zstepA. (* [comment removed for export] *)
  eapply CONT; [exact MI| exact SK| exact WM| exact MU| exact QC| exact LB| exact ITS].
Qed.
End ENQ1.

Section PUT.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variable Q : machine_state -> Prop.
Variables (m : mem) (lo T B cb g : Z) (b1 nhi nlo n : Z) (aidw : word) (cnt first last bnext bsz bcnt qb : Z) (its : list word) (shj : list byte).
Notation INST := 0xaaf58.
Notation CA := (T + 208).
Hypothesis Hn : n = nhi * 2^32 + nlo.
Definition l8 : Z := (n + 7) / 8.                  (* [comment removed for export] *)
Notation L := (8 * l8).                            (* [comment removed for export] *)
Hypothesis Hg : 8 * g = cb + 16.                   (* [comment removed for export] *)
Notation SHa := (0x7fff8000 + g).

Hypothesis SK : stk bsegs m lo (bv_unsigned sp).
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 144.
Hypothesis SPH : bv_unsigned sp <= 2^47.
Hypothesis MI : mem_inv bsegs m.
Hypothesis HTp : placed_s T 4096.
Hypothesis HCB : 0x603000 <= cb /\ cb + 16 + L <= alloc_ceiling /\ cb mod 16 = 0.   (* [comment removed for export] *)
Hypothesis HCBP : cb + 16 + L <= 0x7fff7000 \/ kHighMemBeg <= cb.                (* [comment removed for export] *)
Hypothesis HNHI : 0 <= nhi < 256. Hypothesis HNLO : 0 <= nlo < 2^32.
Hypothesis HN : n <= 2^27.
Hypothesis QMAX : rw_cells bsegs m 0xab270 (* [comment removed for export] *) [C8 (Z_to_bv 64 0x10000000); C8 (Z_to_bv 64 kQuarantineMin); C8 (Z_to_bv 64 0x100000)].
Hypothesis GFL : rw_cells bsegs m 0xa5598 [C8 (Z_to_bv 64 0xabdb8)].        (* [comment removed for export] *)
Hypothesis FFS : rw_cells bsegs m 0xabde8 (* [comment removed for export] *) [C4 (Z_to_bv 64 0)].       (* [comment removed for export] *)
Hypothesis PG : poison_globals m.
Hypothesis HDR : rw_cells bsegs m cb [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 nhi); C4 (Z_to_bv 64 nlo); C8 aidw].
Hypothesis SH : rw_cells bsegs m SHa [CB (Z.to_nat l8) shj].
Hypothesis HCBT : cb + 16 + L <= T \/ T + 4096 <= cb.
(* [comment removed for export] *)
Hypothesis QC : rw_cells bsegs m (T + 80) [C8 (Z_to_bv 64 cnt); C8 (Z_to_bv 64 first); C8 (Z_to_bv 64 last); C8 (Z_to_bv 64 qb)].
Hypothesis HCNT : 0 < cnt < 2^63.
Hypothesis HL : kHighMemBeg <= last /\ last + 8192 <= alloc_ceiling.
Hypothesis HLT : last + 8192 <= T \/ T + 4096 <= last.
Hypothesis HLCB : last + 8192 <= cb \/ cb + 16 + L <= last.
Hypothesis LB : rw_cells bsegs m last [C8 (Z_to_bv 64 bnext); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 bcnt)].
Hypothesis ITS : u64arr bsegs m (last + 24) its.
Hypothesis LITS : Z.of_nat (length its) = 1021.
Hypothesis HBC : 0 <= bcnt < 1021.
Hypothesis HBSZ : 0 <= bsz /\ bsz + n < 2^64.
Hypothesis HQB : 0 <= qb /\ qb + n < 2^64.
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k).
Hypothesis PDAT : forall a k, 0xa5000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PT : forall a k, T <= a -> a + Z.of_nat k <= T + 4096 -> P (Z_to_bv 64 a, k).
Hypothesis PLB : forall a k, last <= a -> a + Z.of_nat k <= last + 8192 -> P (Z_to_bv 64 a, k).
Hypothesis PCH : forall a k, cb <= a -> a + Z.of_nat k <= cb + 16 -> P (Z_to_bv 64 a, k).
Hypothesis PSH : forall a k, SHa <= a -> a + Z.of_nat k <= SHa + l8 -> P (Z_to_bv 64 a, k).

Definition putW : list (Z * Z) :=
  [(bv_unsigned sp - 144, bv_unsigned sp); (SHa, SHa + l8); (last + 8, last + 24); (last + 24 + 8 * bcnt, last + 24 + 8 * bcnt + 8); (T + 104, T + 112)].

(* [comment removed for export] *)
(* [comment removed for export] *)
End PUT.
End RC__1.
