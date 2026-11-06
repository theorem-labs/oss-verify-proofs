(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v, with its module names changed; 486 of its 526 lines of code are new or changed and 1265 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the kit of kernel's raw path (the raw segment of kernel's walk, +0x1f30 -> +0x2100): the
   lane's own cuts and what its steps need beside kernel_defs.v, kernel_kit.v, kernel_msg0_kit.v and kernel_qmsg_kit.v.
   Listing (internal path) (internal record, sha256 7bc02d6772b3), +0x1f30 .. +0x2100.
   THE CUTS (kat of kernel_defs.v at a private pc; slots kslots_setup ++ [(KS_ROOM, 4097)]; s7 = x23 = ci from
   +0x1fe0 / +0x2000 on):
     kr_c1 +0x1f3c  meta_fill_00(shadow(w1)) returned: F's shadow kfsh 00 f8 f3
     kr_c2 +0x1f4c  checked_memset(w1, 0, 4112) returned: w1's fields n = f = 0
     kr_c3 +0x2074  the jal checked_memcpy(w1, p', t): a0 = w1, a1 = p' = wp + adv - t, a2 = s11 = t (1..4096); the
                    cursor already at adv (p' + t, the bytes left minus t)
     kr_c4 +0x2078  that copy returned
     kr_c5 +0x20b8  the jal checked_memcpy(g_nl + 4096 j, w1, t): s6 = g_nl, w1.n = t
     kr_c6 +0x20bc  that copy returned
     kr_c7 +0x20f8  the jal meta_fill_f8(shadow(w1), 0x202): j' <= ci + 1 chunks queued
     kr_c8 +0x20fc  it returned: kfsh f8 f8 f3
   THE LEMMAS: an input range at a cut (kr_inp: shadow facts moved from the call by LinkWalkShadow.v sbyte_transport,
   the bytes present, off kernel's window, off F), an input byte as a 1-byte value (kr_inbyte), the two calls into
   w1 (kr_call_ms: link_ajkit.v aj_gx_intrin_at OSet over AMEMSET; kr_call_icpy: OCpy over AMEMCPY, the source an
   input range), the cut after a run that wrote the cursor and w1.n (kr_land_cw), w1's fields kept (kr_kw_cur,
   kr_kw_cpy), the cursor restated (kr_kcursor_new), and the engine's chunk length d0 + (d1 & 15) * 256 + 1
   (kr_U_s11e).
   Section hypotheses: LAWS, LV, TB, KI, AMEMCPY, AMEMSET.
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkNlw LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkShadow LinkWalkCall.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c kernel_img.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro kernel_defs kernel_kit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_msg0_kit kernel_next kernel_qmsg_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* every lemma of the Section below takes all its hypotheses (one calling convention for the lane) *)
Set Default Proof Using "All".

(* F's shadow from shadow(F): w1's 0x202 bytes [4, 0x206) *)
Lemma kr_kfsh_w1z : forall s2v r i, 4 <= i < 0x206 -> nth (Z.to_nat i) (kfsh 0 s2v r) 0 = 0.
Proof.
  intros s2v r i Hi. rewrite kn_kfsh_nth.
  destruct (Nat.ltb_spec (Z.to_nat i) 4); [lia|]. destruct (Nat.ltb_spec (Z.to_nat i) 0x206); [reflexivity | lia].
Qed.

(* the engine's chunk length at +0x2008: d0 + ((d1 << 60) >> 52) + 1 = d0 + (d1 & 15) * 256 + 1 *)
Definition kr_s11e : sv :=
  SAlu ALU_ADD (SAlu ALU_ADD (SOff 34 0) (SAlu ALU_SRL (SAlu ALU_SLL (SOff 35 0) (SLit 60)) (SLit 52))) (SLit 1).

Lemma kr_shift_nib : forall d1, 0 <= d1 < 256 ->
  (d1 * 1152921504606846976) mod 18446744073709551616 / 4503599627370496 = (d1 mod 16) * 256.
Proof.
  intros d1 Hd.
  assert (H1 : (d1 * 1152921504606846976) mod 18446744073709551616 = (d1 mod 16) * 1152921504606846976).
  { rewrite (Z.div_mod d1 16) at 1 by lia.
    replace ((16 * (d1 / 16) + d1 mod 16) * 1152921504606846976)
      with ((d1 mod 16) * 1152921504606846976 + (d1 / 16) * 18446744073709551616) by ring.
    rewrite Z.mod_add by lia. apply Z.mod_small. pose proof (Z.mod_pos_bound d1 16 ltac:(lia)). lia. }
  rewrite H1. replace ((d1 mod 16) * 1152921504606846976) with ((d1 mod 16) * 256 * 4503599627370496) by ring.
  apply Z.div_mul. lia.
Qed.

Lemma kr_U_s11e : forall (E : env) d0 d1,
  ew E 34%nat = Z_to_bv 64 d0 -> ew E 35%nat = Z_to_bv 64 d1 -> 0 <= d0 < 256 -> 0 <= d1 < 256 ->
  U E kr_s11e = d0 + (d1 mod 16) * 256 + 1 /\ U E (SAlu ALU_ADD (SLit 0) kr_s11e) = d0 + (d1 mod 16) * 256 + 1.
Proof.
  intros E d0 d1 E34 E35 H0 H1.
  assert (HS : U E kr_s11e = d0 + (d1 mod 16) * 256 + 1).
  { unfold kr_s11e. rewrite !U_SAlu, (U_atom E 34 d0 E34 ltac:(lia)), (U_atom E 35 d1 E35 ltac:(lia)), !U_lit by lia.
    cbn [zalu_raw]. change (Z.land 60 63) with 60. change (Z.land 52 63) with 52.
    rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
    change (2 ^ 60) with 1152921504606846976. change (2 ^ 52) with 4503599627370496.
    unfold zcanon, M64. change (2 ^ 64) with 18446744073709551616.
    rewrite kr_shift_nib by exact H1. pose proof (Z.mod_pos_bound d1 16 ltac:(lia)).
    rewrite (Z.mod_small ((d1 mod 16) * 256)) by lia.
    rewrite (Z.mod_small (d0 + (d1 mod 16) * 256)) by lia.
    apply Z.mod_small. lia. }
  split; [exact HS|].
  rewrite U_SAlu, U_lit, HS by lia. cbn [zalu_raw]. unfold zcanon, M64. pose proof (Z.mod_pos_bound d1 16 ltac:(lia)).
  apply Z.mod_small. lia.
Qed.

(* a present byte as a 1-byte value *)
Lemma kr_inbyte : forall (segs : list Segment) (H : word -> bool) (m : word -> option byte) x v,
  aview segs H m x = Some v -> val_mem segs (mrestrict H m) x 1 v /\ 0 <= v < 256.
Proof.
  intros segs H m x v Hv. unfold aview in Hv.
  destruct (mbyte segs (mrestrict H m) x) as [b|] eqn:Eb; cbn in Hv; [|discriminate].
  injection Hv as <-. pose proof (bv_unsigned_in_range 8 b) as Hr.
  assert (Hr' : 0 <= bv_unsigned b < 256) by (change 256 with (2 ^ Z.of_N 8); exact Hr).
  split; [|exact Hr'].
  intros k Hk. assert (k = 0%nat) by lia. subst k. rewrite Z.add_0_r, Eb. f_equal.
  match goal with |- context [?f (bv_unsigned b) 1%nat 0%nat] =>
    change (f (bv_unsigned b) 1%nat 0%nat) with ((bv_unsigned b mod 256) mod 256) end.
  rewrite !Z.mod_small by lia.
  first [apply Z_to_bv_bv_unsigned | symmetry; apply Z_to_bv_bv_unsigned].
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis LV : LinkVals.
Hypothesis TB : AF0m.PcapSyms B.                                (* AF0m.v; discharged at the frame's B by AD2l.PcapB_syms *)
Hypothesis KI : KernImg pa_segs B.                              (* kernel_img_syms at the image *)
Hypothesis AMEMCPY : aintrin_realizes pa_segs B OCpy 0x52d78.   (* checked_memcpy: AE2q.v asan_memcpy_realizes *)
Hypothesis AMEMSET : aintrin_realizes pa_segs B OSet 0x53214.   (* checked_memset: AE2r.v asan_memset_realizes *)

(* ---- the lane's cuts ---- *)
Definition kr_sl (cx : kcx) (fpos c : Z) : list (Z * Z) := kslots_setup cx fpos c ++ [(KS_ROOM, 4097)].
Definition kr_rl0 (cx : kcx) (fpos : Z) : list (nat * Z) :=
  [(19%nat, ka0 cx + 8); (21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N)].

Definition kr_c1 (Rc : kcx -> Z -> Prop) :
  kcx -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
  fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j adv, Rc cx (c - ci) /\ 1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci /\
  kat B cx fpos 0x1f3c (kregs_chunk cx fpos ci) (kr_sl cx fpos c) (kfsh 0 0xf8 0xf3) true adv (Some j)
    k2 ly3 S3 W3 ms3 md3.
Definition kr_c2 (Rc : kcx -> Z -> Prop) :
  kcx -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
  fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j adv, Rc cx (c - ci) /\ 1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci /\
  kw_at W3 ms3 (kW1 cx fpos) 0 0 /\
  kat B cx fpos 0x1f4c (kregs_chunk cx fpos ci) (kr_sl cx fpos c) (kfsh 0 0xf8 0xf3) true adv (Some j)
    k2 ly3 S3 W3 ms3 md3.
Definition kr_rl3 (cx : kcx) (fpos ci t p : Z) : list (nat * Z) :=
  kregs_chunk cx fpos ci ++ [(23%nat, ci); (27%nat, t); (10%nat, kW1 cx fpos); (11%nat, p); (12%nat, t)].
Definition kr_c3 (Rc : kcx -> Z -> Prop) :
  kcx -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
  fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j adv t, Rc cx (c - ci) /\ 1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci /\ 1 <= t <= 4096 /\
  t <= adv /\ kw_at W3 ms3 (kW1 cx fpos) 0 0 /\
  kat B cx fpos 0x2074 (kr_rl3 cx fpos ci t (k_wp cx + adv - t)) (kr_sl cx fpos c) (kfsh 0 0xf8 0xf3) true adv
    (Some j) k2 ly3 S3 W3 ms3 md3.
Definition kr_rl4 (cx : kcx) (fpos ci t : Z) : list (nat * Z) :=
  kregs_chunk cx fpos ci ++ [(23%nat, ci); (27%nat, t)].
Definition kr_c4 (Rc : kcx -> Z -> Prop) :
  kcx -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
  fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j adv t, Rc cx (c - ci) /\ 1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci /\ 1 <= t <= 4096 /\
  kw_at W3 ms3 (kW1 cx fpos) 0 0 /\
  kat B cx fpos 0x2078 (kr_rl4 cx fpos ci t) (kr_sl cx fpos c) (kfsh 0 0xf8 0xf3) true adv (Some j)
    k2 ly3 S3 W3 ms3 md3.
Definition kr_rl5 (cx : kcx) (fpos ci t j : Z) : list (nat * Z) :=
  kr_rl0 cx fpos ++ [(22%nat, LA_G_NL); (23%nat, ci); (27%nat, t); (10%nat, LA_G_NL + 4096 * j);
                     (11%nat, kW1 cx fpos); (12%nat, t)].
Definition kr_c5 (Rc : kcx -> Z -> Prop) :
  kcx -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
  fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j adv t, Rc cx (c - ci) /\ 1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci /\ 1 <= t <= 4096 /\
  kat B cx fpos 0x20b8 (kr_rl5 cx fpos ci t j) (kr_sl cx fpos c) (kfsh 0 0xf8 0xf3) true adv (Some j)
    k2 ly3 S3 W3 ms3 md3.
Definition kr_rl6 (cx : kcx) (fpos ci t : Z) : list (nat * Z) :=
  kr_rl0 cx fpos ++ [(22%nat, LA_G_NL); (23%nat, ci); (27%nat, t)].
Definition kr_c6 (Rc : kcx -> Z -> Prop) :
  kcx -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
  fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j adv t, Rc cx (c - ci) /\ 1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci /\ 1 <= t <= 4096 /\
  kat B cx fpos 0x20bc (kr_rl6 cx fpos ci t) (kr_sl cx fpos c) (kfsh 0 0xf8 0xf3) true adv (Some j)
    k2 ly3 S3 W3 ms3 md3.
Definition kr_rl7 (cx : kcx) (fpos ci : Z) : list (nat * Z) :=
  kr_rl0 cx fpos ++ [(23%nat, ci); (10%nat, kFSH cx fpos + 4); (11%nat, 0x202)].
Definition kr_c7 (Rc : kcx -> Z -> Prop) :
  kcx -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
  fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j adv, Rc cx (c - ci) /\ 1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci + 1 /\
  kat B cx fpos 0x20f8 (kr_rl7 cx fpos ci) (kr_sl cx fpos c) (kfsh 0 0xf8 0xf3) true adv (Some j)
    k2 ly3 S3 W3 ms3 md3.
Definition kr_rl8 (cx : kcx) (fpos ci : Z) : list (nat * Z) := kr_rl0 cx fpos ++ [(23%nat, ci)].
Definition kr_c8 (Rc : kcx -> Z -> Prop) :
  kcx -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
  fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j adv, Rc cx (c - ci) /\ 1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci + 1 /\
  kat B cx fpos 0x20fc (kr_rl8 cx fpos ci) (kr_sl cx fpos c) (kfsh 0xf8 0xf8 0xf3) true adv (Some j)
    k2 ly3 S3 W3 ms3 md3.

Lemma kr_sl_ok : forall cx fpos c, kslots_okb (kr_sl cx fpos c) = true.
Proof using. intros cx fpos c. reflexivity. Qed.

(* ---- an input range at a cut ---- *)
Lemma kr_inp : forall cx fpos k2 ly3 S3 W3 ms3 md3 x n,
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kjbk B cx fpos k2 ly3 S3 md3 -> kkept B cx fpos W3 ms3 ->
  k_wp cx <= x -> x + n <= k_wp cx + k_wn cx -> 0 < n ->
  range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF x n /\
  shadow_hull_vis (aview SEGS (w_H W3) (ms_mem ms3)) x n /\
  (forall a, x <= a < x + n -> exists v, aview SEGS (w_H W3) (ms_mem ms3) a = Some v) /\
  amem_range x n /\
  (forall a, x <= a < x + n -> ~ (ksp cx - KERNEL_AK <= a < ksp cx)) /\
  (forall a, x <= a < x + n -> 4096 <= a < 2 ^ 47 /\ ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44) /\
     ~ (kF cx fpos <= a < kF cx fpos + fs_frame_bytes KN_CID)).
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 x n HB HJ HJB HKK Hx1 Hx2 Hn.
  pose proof (kn_apre SK B cx HB) as (_ & _ & _ & Hra & Hamr & Hap).
  pose proof HB as (HPRE & HRD & HKP & _ & _ & HWP & HWN & HWPr & HWNr & _).
  destruct HKP as (kbs & _ & _ & _ & _ & (wp & wn & Hwp & Hwn & Hwpr & Hwnr & Hd & _ & _ & Hhull & _) & _).
  assert (E1 : wp = k_wp cx).
  { pose proof (rdword_of_val_mem SEGS (w_H (k_W cx)) (k_memc cx) _ _ Hwp Hwpr) as R1.
    pose proof (rdword_of_val_mem SEGS (w_H (k_W cx)) (k_memc cx) _ _ HWP HWPr) as R2.
    unfold ka0 in *. rewrite R1 in R2. injection R2 as R2. exact R2. }
  assert (E2 : wn = k_wn cx).
  { pose proof (rdword_of_val_mem SEGS (w_H (k_W cx)) (k_memc cx) _ _ Hwn Hwnr) as R1.
    pose proof (rdword_of_val_mem SEGS (w_H (k_W cx)) (k_memc cx) _ _ HWN HWNr) as R2.
    unfold ka0 in *. rewrite R1 in R2. injection R2 as R2. exact R2. }
  subst wp wn.
  assert (HIN : forall a, x <= a < x + n -> kernel_ard SEGS (k_regs cx) (km0 cx) a)
    by (intros a Ha; apply (kn_ard_inp SK B cx a ltac:(lia) HB)).
  assert (HIA : forall a, x <= a < x + n ->
            saddr (aview SEGS (w_H W3) (ms_mem ms3)) a /\
            aview SEGS (w_H W3) (ms_mem ms3) a = aview SEGS (w_H (k_W cx)) (k_memc cx) a)
    by (intros a Ha; exact (kn_input_at SK B LAWS TB cx fpos k2 ly3 S3 W3 ms3 md3 a HB HJ HJB HKK ltac:(lia))).
  split; [apply ra_of_saddr; intros a Ha; exact (proj1 (HIA a Ha))|].
  split.
  { (* the hull: each byte's 8-byte group, moved from the call (LinkWalkShadow.v sbyte_transport) *)
    apply hull_of_gvis; [exact Hn|]. intros a Ha.
    pose proof HPRE as (HJ0 & _).
    pose proof HJ0 as (_ & _ & (memS0 & HJi0 & _) & _). pose proof HJi0 as (HAR0 & _).
    pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (HAR3 & _).
    destruct (aj_stk_row_eq SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as (R0lo & R0hi).
    destruct (aj_stk_row_eq SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (R3lo & R3hi).
    pose proof HJB as (_ & _ & Hperm & Hnin & (S1 & W1 & mem1 & md1 & HAR1 & HF1 & _) & _).
    assert (Hin1 : In (KN_CID, fpos) (frames S1)) by (rewrite HF1; left; reflexivity).
    pose proof HAR1 as (M1 & _).
    destruct (frame_facts B _ _ _ KN_CID fpos M1 Hin1) as (_ & Hpos & _).
    destruct HKK as (Hak & _).
    assert (Hwn0 : 0 < k_wn cx) by lia.
    refine (proj2 (sbyte_transport SEGS B LAWS TB pa_img_range (k_lyc cx) (k_Sc cx) (k_W cx) (k_memc cx) (k_mdc cx)
      ly3 S3 W3 (ms_mem ms3) md3 (ksp cx - KERNEL_AK) (ksp cx)
      (fun a => kE cx a \/ aside_rng (k_lyc cx) KN_CID fpos a) a HAR0 HAR3 _ _ _ Hak _ _ _ _)).
    - congruence.
    - congruence.
    - intros b m Hbm. apply (Permutation_in _ (Permutation_sym Hperm)). exact Hbm.
    - apply fmiss_or.
      + apply (fmiss_app SEGS B LAWS _ _ _ _ _ _ HAR0). intros q Hq.
        destruct (kn_ard_loc SK B LAWS cx fpos k2 ly3 S3 md3 q HB HJB (kn_kE_ard cx q Hq)) as (_ & Happ & _).
        exact Happ.
      + apply (fmiss_side SEGS B _ _ _ _ _ KN_CID fpos HAR0); [unfold KN_CID; lia | exact Hpos | exact Hnin].
    - exact (sclass_of_akb SEGS B _ _ _ _ a (HRD a (HIN a Ha))).
    - apply (saddr_of_ra _ (k_wp cx) (k_wn cx) a); [|lia]. rewrite <- ard_aview. exact Hra.
    - apply (gvis_of_hull _ (k_wp cx) (k_wn cx) a); [|lia]. rewrite <- ard_aview. exact (Hhull Hwn0). }
  split.
  { intros a Ha. destruct Hd as (d & Hab & Hdl). pose proof Hab as (_ & _ & Hb).
    rewrite (proj2 (HIA a Ha)). unfold km0 in Hb.
    specialize (Hb (Z.to_nat (a - k_wp cx)) ltac:(lia)). rewrite Z2Nat.id in Hb by lia.
    replace (k_wp cx + (a - k_wp cx)) with a in Hb by lia.
    unfold aview. rewrite Hb.
    destruct (nth_error d (Z.to_nat (a - k_wp cx))) as [b|] eqn:Eb; [eexists; reflexivity|].
    apply nth_error_None in Eb. lia. }
  split; [unfold amem_range in *; lia|].
  split.
  { intros a Ha. destruct Hap as (Hfr & _). unfold apart_frame in Hfr. unfold ksp. lia. }
  intros a Ha. pose proof (kn_rd_facts SK B LAWS cx fpos k2 ly3 S3 md3 a HB HJB (HIN a Ha)) as (R1 & R2 & R3).
  split; [exact R1|]. split; [exact R2|].
  exact (kn_ard_not_F SK B LAWS cx fpos k2 ly3 S3 md3 a HB HJB (HIN a Ha)).
Qed.

(* ---- w1's fields: kept when only the cursor changed; kept by a copy into [w1, w1 + t) ---- *)
Lemma kr_kw_cur : forall cx fpos k2 ly3 S3 md3 W3 ms3 ms' n f,
  kbase SK B cx -> kjbk B cx fpos k2 ly3 S3 md3 ->
  kw_at W3 ms3 (kW1 cx fpos) n f ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (ka0 cx <= a < ka0 cx + 16) ->
     aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem ms') a) ->
  kw_at W3 ms' (kW1 cx fpos) n f.
Proof.
  intros cx fpos k2 ly3 S3 md3 W3 ms3 ms' n f HB HJB HW UN HP.
  destruct (km_cur_loc SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (CU0 & CU16 & CL).
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & _).
  rewrite kn_fsb8 in F2.
  pose proof (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (HF4 & HFc & _).
  pose proof asan_consts as ((C1a & C1b) & _).
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & _).
  apply (kn_kw_keep W3 ms3 ms' _ n f HW); [|exact HP].
  intros i Hi. unfold kW1, KN_W1, NW_SIZE in *. apply UN; [lia|].
  intros Hx.
  assert (Hx' : kernel_ard SEGS (k_regs cx) (km0 cx) (kF cx fpos + 0x20 + i)) by (left; unfold ka0 in Hx; exact Hx).
  pose proof (kn_ard_not_F SK B LAWS cx fpos k2 ly3 S3 md3 _ HB HJB Hx') as HnF. rewrite kn_fsb8 in HnF. lia.
Qed.

Lemma kr_kw_cpy : forall W3 ms3 ms' w n f t,
  kw_at W3 ms3 w n f -> 0 <= t <= NW_N ->
  (forall i, 0 <= i < t -> aview SEGS (w_H W3) (ms_mem ms') (w + i) <> None) ->
  (forall i, t <= i < NW_SIZE ->
     aview SEGS (w_H W3) (ms_mem ms') (w + i) = aview SEGS (w_H W3) (ms_mem ms3) (w + i)) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem ms') a) ->
  kw_at W3 ms' w n f.
Proof.
  intros W3 ms3 ms' w n f t HW Ht Hv UN HP.
  destruct HW as (Hw0 & Hwl & Hpres & Hnv & Hfv & Hnr & Hfr).
  split; [exact Hw0|]. split; [exact Hwl|].
  split.
  { intros i Hi. destruct (Hpres i Hi) as ((b & Hb) & Hwr). split.
    - destruct (Z.lt_ge_cases i t) as [Hit | Hit].
      + specialize (Hv i ltac:(lia)). unfold aview in Hv.
        destruct (mbyte SEGS (mrestrict (w_H W3) (ms_mem ms')) (w + i)) as [b'|]; [exists b'; reflexivity|].
        exfalso. apply Hv. reflexivity.
      + rewrite (kn_mbyte_of_aview SEGS (w_H W3) (w_H W3) (ms_mem ms3) (ms_mem ms') _ _ (UN i ltac:(lia))).
        exists b. exact Hb.
    - apply (writable_kept (w_H W3) (ms_mem ms3) (ms_mem ms') (w + i) (HP _)). exact Hwr. }
  split.
  { apply (kn_val_mem_move W3 (ms_mem ms3) (ms_mem ms') _ 8 _ Hnv). intros i Hi.
    rewrite <- Z.add_assoc. apply UN. unfold NW_N, NW_SIZE in *. lia. }
  split; [|split; [exact Hnr | exact Hfr]].
  apply (kn_val_mem_move W3 (ms_mem ms3) (ms_mem ms') _ 4 _ Hfv). intros i Hi.
  rewrite <- Z.add_assoc. apply UN. unfold NW_FULL, NW_N, NW_SIZE in *. lia.
Qed.

(* ---- the cursor restated at adv' ---- *)
Lemma kr_kcursor_new : forall cx W3 ms3 ms' adv adv',
  kcursor cx W3 ms3 adv -> 0 <= adv' <= k_wn cx ->
  val_mem SEGS (rdW W3 (ms_mem ms')) (ka0 cx) 8 (k_wp cx + adv') ->
  val_mem SEGS (rdW W3 (ms_mem ms')) (ka0 cx + 8) 8 (k_wn cx - adv') ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem ms') a) ->
  kcursor cx W3 ms' adv'.
Proof.
  intros cx W3 ms3 ms' adv adv' (_ & _ & _ & HW) Hadv H0 H8 Hpr.
  split; [exact Hadv|]. split; [exact H0|]. split; [exact H8|].
  intros i Hi. apply (writable_kept (w_H W3) (ms_mem ms3) (ms_mem ms') (ka0 cx + i) (Hpr _)). exact (HW i Hi).
Qed.

(* ---- THE CUT AFTER A RUN that wrote the cursor and w1.n (X = the cursor's 16 bytes and w1.n's 8) ---- *)
Lemma kr_land_cw : forall cx fpos pc rl sl sh adv g k2 ly3 S3 W3 ms3 md3 ms' md' pc' rl' adv',
  kbase SK B cx ->
  kat B cx fpos pc rl sl sh true adv g k2 ly3 S3 W3 ms3 md3 ->
  (length sh <= 2048)%nat -> kslots_okb sl = true ->
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ ((ka0 cx <= a < ka0 cx + 16) \/ (kW1 cx fpos + NW_N <= a < kW1 cx fpos + NW_N + 8)) ->
     aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem ms') a) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  kms pc' ms' -> kregs0 cx ms' -> kregs_eq ms' rl' -> kcursor cx W3 ms' adv' ->
  kat B cx fpos pc' rl' sl sh true adv' g k2 ly3 S3 W3 ms' md'.
Proof.
  intros cx fpos pc rl sl sh adv g k2 ly3 S3 W3 ms3 md3 ms' md' pc' rl' adv'
    HB HK Hsh Hok UN HP Hfds Hfs Hkms Hr0 Hrl Hcur.
  pose proof HK as (_ & _ & _ & HSAV & HFR & HSH & HSL & HJB & HKEPT & _ & HGNL & HLA).
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & _ & S4 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK8 : KERNEL_AK = 4640) by reflexivity. rewrite HK8 in S1.
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & F3 & _ & F5 & _).
  rewrite kn_fsb8 in F2, F3, F5. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in F3.
  unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in F5.
  pose proof (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (HF4 & HFc & _).
  destruct (km_cur_loc SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (CU0 & CU16 & CL).
  pose proof (kn_apre SK B cx HB) as (AG & AL & _).
  unfold apart_gnl, apart in AG, AL.
  assert (UNX : forall a, 0 <= a < 2 ^ 64 ->
            ~ (fun a => (ka0 cx <= a < ka0 cx + 16) \/ (kW1 cx fpos + NW_N <= a < kW1 cx fpos + NW_N + 8)) a ->
            aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a) by exact UN.
  assert (CW : forall a, ka0 cx <= a < ka0 cx + 16 ->
            ~ (ksp cx - 4640 <= a < ksp cx) /\ (a < kLowMemEnd \/ kHighMemBeg <= a) /\
            ~ (kF cx fpos <= a < kF cx fpos + 16384)).
  { intros a Ha. destruct (CL a Ha) as (CL1 & CL2). rewrite HK8 in CL2.
    split; [exact CL2|]. split; [exact CL1|].
    assert (Hx : kernel_ard SEGS (k_regs cx) (km0 cx) a) by (left; unfold ka0 in Ha; exact Ha).
    pose proof (kn_ard_not_F SK B LAWS cx fpos k2 ly3 S3 md3 a HB HJB Hx) as HnF. rewrite kn_fsb8 in HnF. exact HnF. }
  assert (WN : forall a, kW1 cx fpos + NW_N <= a < kW1 cx fpos + NW_N + 8 ->
            kF cx fpos + 24 <= a < kF cx fpos + 16384 - 8) by (intros a Ha; unfold kW1, KN_W1, NW_N in Ha; lia).
  unfold kat.
  refine (conj Hkms (conj Hr0 (conj Hrl (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj Hcur
    (conj _ _))))))))))).
  - apply (ksaved_frame SK B _ cx W3 ms3 W3 ms' HB UNX); [|exact HSAV].
    intros a Ha [Hx | Hx]; [destruct (CW a Hx) as (CW1 & _); lia | pose proof (WN a Hx); lia].
  - apply (kframe_frame B LAWS _ cx fpos true k2 ly3 S3 md3 W3 ms3 W3 ms' HJB UNX HP); [| | exact HFR];
      rewrite ?kn_fsb8; intros a Ha [Hx | Hx];
      first [destruct (CW a Hx) as (_ & _ & CW3); lia | pose proof (WN a Hx); lia].
  - apply (kshadow_frame B LAWS _ cx fpos sh k2 ly3 S3 md3 W3 ms3 W3 ms' HJB UNX Hsh); [|exact HSH].
    intros a Ha [Hx | Hx].
    + destruct (CW a Hx) as (_ & CW2 & _). unfold kFSH, shadow_of_addr, kLowMemEnd, kHighMemBeg, SHADOW_OFF in *. lia.
    + pose proof (WN a Hx). unfold kFSH, shadow_of_addr, SHADOW_OFF in *. lia.
  - apply (kslots_frame SK B _ cx sl sl W3 ms3 W3 ms' HB UNX (incl_refl _)); [|exact HSL].
    intros ov Hov. pose proof (kslots_okb_spec sl Hok ov Hov) as (Ho1 & Ho2). split; [lia|].
    intros a Ha [Hx | Hx]; [destruct (CW a Hx) as (CW1 & _); lia | pose proof (WN a Hx); lia].
  - exact (kjbk_md B cx fpos k2 ly3 S3 md3 md' HJB Hfds Hfs).
  - apply (kkept_frame SK B LAWS _ cx fpos k2 ly3 S3 md3 W3 ms3 W3 ms' HB HJB UNX HP); [|exact HKEPT].
    intros a [Hx | Hx].
    + unfold kX_in. left. unfold kE, inFP. exists (aarg (k_regs cx) 0, aarg (k_regs cx) 0 + 16).
      split; [unfold kernel_awr; km_inl | cbn [fst snd]; unfold ka0 in Hx; exact Hx].
    + unfold kX_in. right. left. pose proof (WN a Hx). rewrite kn_fsb8. lia.
  - apply (kgnl_frame _ cx g W3 ms3 W3 ms' UNX HP); [|exact HGNL].
    intros a Ha [Hx | Hx]; [unfold LA_G_NL, NK_SIZE in *; lia | pose proof (WN a Hx); unfold LA_G_NL, NK_SIZE in *; lia].
  - apply (kla_frame _ W3 ms3 W3 ms' UNX HP); [|exact HLA].
    intros a Ha [Hx | Hx]; [unfold LA_LONG_ALIAS, LONG_ALIAS_SIZE in *; lia
                          | pose proof (WN a Hx); unfold LA_LONG_ALIAS, LONG_ALIAS_SIZE in *; lia].
Qed.

(* ---- THE TWO CALLS into w1 ---- *)

(* checked_memset(w1, 0, 4112) from s1 (link_ajkit.v aj_gx_intrin_at): w1 lies in F, its shadow is 0 (kfsh 0 ..) *)
Lemma kr_call_ms : forall cx fpos k2 ly3 S3 W3 ms3 md3 (rg : bvmap 5 word) raw s2v r
    (Q : world SEGS -> config -> Prop),
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kjbk B cx fpos k2 ly3 S3 md3 ->
  kshadow cx fpos W3 ms3 (kfsh 0 s2v r) ->
  getr rg 10 = w64 (kW1 cx fpos) -> getr rg 11 = w64 0 -> getr rg 12 = w64 NW_SIZE -> getr rg 2 = w64 (ksp1 cx) ->
  getr rg 3 = getr (k_regs cx) 3 -> getr rg 4 = getr (k_regs cx) 4 -> getr rg 1 = raw -> YK0s.ret_ok raw ->
  (forall regs2 mem2 md2,
     ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
       (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 mem2 md2 k2 ->
     aregs_preserved rg regs2 ->
     (forall i, 0 <= i < NW_SIZE -> aview SEGS (w_H W3) mem2 (kW1 cx fpos + i) = Some 0) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (kW1 cx fpos <= a < kW1 cx fpos + NW_SIZE) ->
        ~ (ksp1 cx - ESTACK <= a < ksp1 cx) -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
     (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) mem2 a) ->
     same_but_materialized md3 md2 ->
     SRr SEGS W3 (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W3 (mkCfg (mkst rg (Z_to_bv 64 0x53214) (ms_mem ms3) (seg_rom SEGS)) md3) Q.
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 rg raw s2v r Q HB HJ HJB HSH R10 R11 R12 R2 R3 R4 R1 Hraw CONT.
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & HGok & _ & _ & _ & Hgp & Htp & _).
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & S3' & S4 & S5 & S6 & S7 & S8 & S9 & _).
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & F3 & F4 & F5 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK8 : KERNEL_AK = 4640) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
  rewrite kn_fsb8 in F2, F3.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in F3.
  assert (Hsp : spZ rg = ksp1 cx) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
  assert (HF8 : (kF cx fpos) mod 8 = 0) by lia.
  (* the shadow byte of a byte of w1 *)
  assert (Hsh8 : forall x, kW1 cx fpos <= x < kW1 cx fpos + NW_SIZE ->
            shadow_of_addr SHADOW_OFF x = kFSH cx fpos + (4 + (x - kW1 cx fpos) / 8)).
  { intros x Hx. unfold kFSH, shadow_of_addr.
    replace x with (kF cx fpos + (0x20 + (x - kW1 cx fpos))) at 1 by (unfold kW1, KN_W1; lia).
    rewrite (km_div8 (kF cx fpos)) by exact HF8.
    replace (0x20 + (x - kW1 cx fpos)) with (4 * 8 + (x - kW1 cx fpos)) by lia.
    rewrite Z.div_add_l by lia. lia. }
  eapply SRr_bind.
  - eapply (aj_gx_intrin_at SK SEGS B LAWS pa_segs_low OSet 0x53214 AMEMSET (k_G cx) (k_XO cx) (k_OUT cx) W3 rg
      (ms_mem ms3) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx) (k_mem0 cx) (k_md0 cx) _ ly3 S3 md3 k2
      (kW1 cx fpos) 0 NW_SIZE raw HGok HJ R10 R11 R12);
    [ unfold NW_SIZE; lia | unfold kW1, KN_W1; lia | unfold kW1, KN_W1, NW_SIZE; lia
    | rewrite Hsp; lia | rewrite Hsp, HES; rewrite HK8 in S6; lia | rewrite Hsp; lia
    | rewrite R3; exact Hgp | rewrite R4; exact Htp | exact R1 | exact Hraw
    | | | | | exact I ].
    + intros a Ha. left. split; [|split].
      * right. right. right. exists KN_CID, fpos. split; [left; reflexivity|]. left.
        unfold in_zr. cbn [fst snd]. rewrite (km_fa SK B cx fpos k2 ly3 S3 W3 (ms_mem ms3) md3 HB HJ), kn_fsb8.
        fold (kF cx fpos). unfold kW1, KN_W1, NW_SIZE in Ha. lia.
      * unfold kW1, KN_W1, NW_SIZE in Ha. lia.
      * rewrite Hsp, HES. rewrite HK8 in S6. unfold kW1, KN_W1, NW_SIZE in Ha. lia.
    + unfold amem_range, kLowMemEnd, kHighMemEnd, kW1, KN_W1, NW_SIZE. unfold kHighMemBeg in *. lia.
    + intros x Hx. exists 0. split; [|left; reflexivity].
      rewrite (Hsh8 x Hx).
      assert (Hi : 4 <= 4 + (x - kW1 cx fpos) / 8 < 0x206).
      { unfold NW_SIZE in Hx. split; [pose proof (Z.div_pos (x - kW1 cx fpos) 8); lia|].
        assert ((x - kW1 cx fpos) / 8 < 514) by (apply Z.div_lt_upper_bound; lia). lia. }
      rewrite (km_sh_at cx fpos W3 ms3 _ _ HSH) by (rewrite kfsh_length; lia).
      rewrite kr_kfsh_w1z by exact Hi. reflexivity.
    + intros _ s Hs.
      assert (E1 : shadow_addr (kW1 cx fpos) = kFSH cx fpos + 4).
      { pose proof (Hsh8 (kW1 cx fpos) ltac:(unfold NW_SIZE; lia)) as Hq.
        unfold shadow_of_addr in Hq. unfold shadow_addr. rewrite Hq. rewrite Z.sub_diag. reflexivity. }
      assert (E2 : shadow_addr (kW1 cx fpos + NW_SIZE - 1) = kFSH cx fpos + 0x205).
      { pose proof (Hsh8 (kW1 cx fpos + NW_SIZE - 1) ltac:(unfold NW_SIZE; lia)) as Hq.
        unfold shadow_of_addr in Hq. unfold shadow_addr. rewrite Hq. f_equal.
        replace (kW1 cx fpos + NW_SIZE - 1 - kW1 cx fpos) with 4111 by (unfold NW_SIZE; lia). reflexivity. }
      rewrite E1, E2 in Hs.
      assert (HFS8 : kFSH cx fpos mod 8 = 0) by (unfold kFSH, shadow_of_addr, SHADOW_OFF; lia).
      assert (Hlo : kFSH cx fpos <= s < kFSH cx fpos + 0x208).
      { assert (D1 : (kFSH cx fpos + 4) / 8 * 8 = kFSH cx fpos) by lia.
        assert (D2 : (kFSH cx fpos + 0x205) / 8 * 8 = kFSH cx fpos + 0x200) by lia.
        lia. }
      replace s with (kFSH cx fpos + (s - kFSH cx fpos)) by lia.
      rewrite (km_sh_at cx fpos W3 ms3 _ _ HSH) by (rewrite kfsh_length; lia). discriminate.
  - cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Hset & Hfr & Hpres & Hsbm).
    apply (CONT regs2 mem2 md2 HJ2 HP2); [| | exact Hpres | exact Hsbm].
    + intros i Hi. rewrite (Hset i Hi). reflexivity.
    + intros a Ha Hd Hw. apply Hfr; [exact Ha | exact Hd | rewrite Hsp; exact Hw].
Qed.

(* checked_memcpy(w1, x, n) from s1 (link_ajkit.v aj_gx_intrin_at): the source an input range *)
Lemma kr_call_icpy : forall cx fpos pc rl sl sh adv g k2 ly3 S3 W3 ms3 md3 (rg : bvmap 5 word) raw x n
    (Q : world SEGS -> config -> Prop),
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kat B cx fpos pc rl sl sh true adv g k2 ly3 S3 W3 ms3 md3 ->
  kshadow cx fpos W3 ms3 (kfsh 0 0xf8 0xf3) ->
  1 <= n <= 4096 -> k_wp cx <= x -> x + n <= k_wp cx + k_wn cx ->
  getr rg 10 = w64 (kW1 cx fpos) -> getr rg 11 = w64 x -> getr rg 12 = w64 n -> getr rg 2 = w64 (ksp1 cx) ->
  getr rg 3 = getr (k_regs cx) 3 -> getr rg 4 = getr (k_regs cx) 4 -> getr rg 1 = raw -> YK0s.ret_ok raw ->
  (forall regs2 mem2 md2,
     ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
       (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 mem2 md2 k2 ->
     aregs_preserved rg regs2 ->
     (forall i, 0 <= i < n ->
        aview SEGS (w_H W3) mem2 (kW1 cx fpos + i) = aview SEGS (w_H W3) (ms_mem ms3) (x + i)) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (kW1 cx fpos <= a < kW1 cx fpos + n) ->
        ~ (ksp1 cx - ESTACK <= a < ksp1 cx) -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
     (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) mem2 a) ->
     same_but_materialized md3 md2 ->
     SRr SEGS W3 (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W3 (mkCfg (mkst rg (Z_to_bv 64 0x52d78) (ms_mem ms3) (seg_rom SEGS)) md3) Q.
Proof.
  intros cx fpos pc rl sl sh adv g k2 ly3 S3 W3 ms3 md3 rg raw x n Q HB HJ HK HSH Hn Hx1 Hx2
    R10 R11 R12 R2 R3 R4 R1 Hraw CONT.
  pose proof HK as (_ & _ & _ & _ & HFR & _ & _ & HJB & HKK & _).
  pose proof HB as (HPRE & _).
  pose proof HPRE as (_ & HGok & _ & _ & _ & Hgp & Htp & _).
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & S3' & S4 & S5 & S6 & S7 & S8 & S9 & _).
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & F3 & F4 & F5 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK8 : KERNEL_AK = 4640) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
  rewrite kn_fsb8 in F2, F3, F5.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in F3.
  assert (Hsp : spZ rg = ksp1 cx) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
  destruct (kr_inp cx fpos k2 ly3 S3 W3 ms3 md3 x n HB HJ HJB HKK Hx1 Hx2 ltac:(lia))
    as (IRA & IHU & IPR & IAM & IWN & ILO).
  assert (HW1 : range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF (kW1 cx fpos) n).
  { pose proof (kn_w1_ra B LAWS cx fpos k2 ly3 S3 md3 W3 ms3 0xf8 0xf3 HJB HSH) as Hw.
    intros y Hy. apply Hw. unfold NW_SIZE. lia. }
  eapply SRr_bind.
  - eapply (aj_gx_intrin_at SK SEGS B LAWS pa_segs_low OCpy 0x52d78 AMEMCPY (k_G cx) (k_XO cx) (k_OUT cx) W3 rg
      (ms_mem ms3) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx) (k_mem0 cx) (k_md0 cx) _ ly3 S3 md3 k2
      (kW1 cx fpos) x n raw HGok HJ R10 R11 R12);
    [ lia | unfold kW1, KN_W1; lia | unfold kW1, KN_W1; lia
    | rewrite Hsp; lia | rewrite Hsp, HES; rewrite HK8 in S6; lia | rewrite Hsp; lia
    | rewrite R3; exact Hgp | rewrite R4; exact Htp | exact R1 | exact Hraw
    | | | exact HW1 | | ].
    + intros a Ha. left. split; [|split].
      * right. right. right. exists KN_CID, fpos. split; [left; reflexivity|]. left.
        unfold in_zr. cbn [fst snd]. rewrite (km_fa SK B cx fpos k2 ly3 S3 W3 (ms_mem ms3) md3 HB HJ), kn_fsb8.
        fold (kF cx fpos). unfold kW1, KN_W1 in Ha. lia.
      * unfold kW1, KN_W1 in Ha. lia.
      * rewrite Hsp, HES. rewrite HK8 in S6. unfold kW1, KN_W1 in Ha. lia.
    + unfold amem_range, kLowMemEnd, kHighMemEnd, kW1, KN_W1. unfold kHighMemBeg in *. lia.
    + intros Hn0.
      pose proof (kq_fbuf_hull SK B LAWS TB KI AMEMCPY LV cx fpos k2 ly3 S3 md3 W3 ms3 KN_W1 n HJB HFR
                    ltac:(unfold KN_W1; lia) ltac:(unfold KN_W1, KN_FSZ; lia) Hn0) as HH.
      exact HH.
    + destruct (ILO x ltac:(lia)) as (IL1 & _ & _). split; [lia|].
      split; [pose proof IAM as IAM'; unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg in IAM'; lia|]. split.
      { intros a Ha. split.
        - destruct (IPR a Ha) as (v & Hv). rewrite Hv. discriminate.
        - rewrite Hsp, HES. pose proof (IWN a Ha) as Hw. rewrite HK8 in Hw. lia. }
      split.
      { destruct (ILO x ltac:(lia)) as (_ & _ & L3). destruct (ILO (x + n - 1) ltac:(lia)) as (_ & _ & L4).
        rewrite kn_fsb8 in L3, L4. unfold kW1, KN_W1.
        lia. }
      split; [exact IAM|]. split; [exact IRA|]. intros _. exact IHU.
  - cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Hset & Hfr & Hpres & Hsbm).
    apply (CONT regs2 mem2 md2 HJ2 HP2); [| | exact Hpres | exact Hsbm].
    + intros i Hi. exact (Hset i Hi).
    + intros a Ha Hd Hw. apply Hfr; [exact Ha | exact Hd | rewrite Hsp; exact Hw].
Qed.

End b.
End a.

(* membership in a cut's register list *)
Ltac kr_in := cbn [kr_rl3 kr_rl4 kr_rl5 kr_rl6 kr_rl7 kr_rl8 kr_rl0 kregs_chunk app In];
  repeat (first [left; reflexivity | left; apply bv_eq; reflexivity | right]).
