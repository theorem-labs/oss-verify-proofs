(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState Inftrees ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr U2AKit ItAKit ItAPure.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U3B Require Import ItB_base.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_base | solve_load_sh0 | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.

Definition lowS (z : Z) : Z := if z =? 4294967295 then -1 else z.
(* [U14B] A2 2026-11-12: zlib 1.4's CODES case stores null base / extra (0x9740c sd zero,48(s1); 0x97414 sd zero,16(s1);
   1.3.1 stored the work pointer, 0x96f1c / 0x96f20), and a new frame word, XFL, the UBSan "extra is not null" flag
   (slot 56: 0x97410 sd zero for CODES, 0x97400 / 0x97450 sd 1 for LENS / DISTS). CODES never reads base / extra
   (every code-length symbol is below match = 20; G's U1A cure C48). *)
Definition EXA (ty : codetype) (S : Z) : Z := match ty with CODES => 0 | LENS => 149312 | DISTS => 149504 end.
Definition BSA (ty : codetype) (S : Z) : Z := match ty with CODES => 0 | LENS => 149216 | DISTS => 149408 end.
Definition XFL (ty : codetype) : Z := match ty with CODES => 0 | _ => 1 end.
Definition NE (ty : codetype) : Z := match ty with CODES => 288 | LENS => 31 | DISTS => 32 end.
Definition isL (ty : codetype) : Z := match ty with LENS => 1 | _ => 0 end.
Definition isD (ty : codetype) : Z := match ty with DISTS => 1 | _ => 0 end.

Lemma NE_ext_len : forall ty, NE ty = it_ext_len ty 288.
Proof. destruct ty; reflexivity. Qed.
Lemma ty_cases : forall ty S,
  (ty = CODES /\ cty ty = 0 /\ it_match ty = 20 /\ EXA ty S = 0 /\ BSA ty S = 0 /\ NE ty = 288 /\ isL ty = 0 /\ isD ty = 0)
  \/ (ty = LENS /\ cty ty = 1 /\ it_match ty = 257 /\ EXA ty S = 149312 /\ BSA ty S = 149216 /\ NE ty = 31 /\ isL ty = 1 /\ isD ty = 0)
  \/ (ty = DISTS /\ cty ty = 2 /\ it_match ty = 0 /\ EXA ty S = 149504 /\ BSA ty S = 149408 /\ NE ty = 32 /\ isL ty = 0 /\ isD ty = 1).
Proof. intros ty S. destruct ty; [left | right; left | right; right]; repeat split; reflexivity. Qed.

Lemma pow2_le15 : forall k, 0 <= k <= 15 -> 1 <= 2 ^ k <= 32768.
Proof. intros k Hk. split; [apply (Z.pow_le_mono_r 2 0 k); lia | apply (Z.pow_le_mono_r 2 k 15); lia]. Qed.
Lemma ne_pow : forall ty k, 1 <= k <= 15 ->
  it_not_enough ty (itm_used k) = match ty with CODES => false | _ => negb (k <=? 9) end.
Proof.
  intros ty k Hk. rewrite itm_used_pow2 by lia. unfold it_not_enough, ENOUGH_LENS, ENOUGH_DISTS.
  destruct ty; [reflexivity| |].
  - destruct (Z.leb_spec k 9); cbn [negb].
    + apply Z.ltb_ge. assert (2 ^ k <= 2 ^ 9) by (apply Z.pow_le_mono_r; lia). change (2 ^ 9) with 512 in *. lia.
    + apply Z.ltb_lt. assert (2 ^ 10 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia). change (2 ^ 10) with 1024 in *. lia.
  - destruct (Z.leb_spec k 9); cbn [negb].
    + apply Z.ltb_ge. assert (2 ^ k <= 2 ^ 9) by (apply Z.pow_le_mono_r; lia). change (2 ^ 9) with 512 in *. lia.
    + apply Z.ltb_lt. assert (2 ^ 10 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia). change (2 ^ 10) with 1024 in *. lia.
Qed.

Lemma mxmn_facts_g : forall lf lo codes bits, 1 <= mxA lf lo codes ->
  1 <= mnA lf lo codes <= mxA lf lo codes /\ mxA lf lo codes <= 15 /\ 1 <= rootA lf lo codes bits <= 15 /\
  mnA lf lo codes <= rootA lf lo codes bits /\
  rootA lf lo codes bits = (let r := (if bits <? mxA lf lo codes then bits else mxA lf lo codes) in
                            if mnA lf lo codes <? r then r else mnA lf lo codes).
Proof.
  intros lf lo codes bits H1. pose proof (mx_range (cntA lf lo codes)) as MR.
  pose proof (mn_range (cntA lf lo codes) (mxA lf lo codes) ltac:(unfold mxA in *; lia)) as NR.
  unfold rootA, itm_root. unfold mnA in *. unfold mxA in *.
  set (mxv := itm_max (cntA lf lo codes)) in *. set (mnv := itm_min (cntA lf lo codes) mxv) in *.
  destruct (Z.ltb_spec mxv bits); destruct (Z.ltb_spec bits mxv); try lia;
    destruct (Z.ltb_spec mxv mnv); destruct (Z.ltb_spec bits mnv); destruct (Z.ltb_spec mnv mxv); destruct (Z.ltb_spec mnv bits); cbv zeta; lia.
Qed.
Lemma rt_facts : forall lf lo codes bits, 1 <= mxA lf lo codes ->
  1 <= rootA lf lo codes bits <= 15 /\ mnA lf lo codes <= rootA lf lo codes bits <= mxA lf lo codes /\ 1 <= mnA lf lo codes.
Proof.
  intros lf lo codes bits H. pose proof (mxmn_facts_g lf lo codes bits H) as (A & B & D & E & F). cbv zeta in F.
  destruct (Z.ltb_spec bits (mxA lf lo codes)); [destruct (Z.ltb_spec (mnA lf lo codes) bits) | destruct (Z.ltb_spec (mnA lf lo codes) (mxA lf lo codes))]; lia.
Qed.

Lemma sllw_1 : forall k, 0 <= k <= 15 -> bv_swrap 32 (Z.shiftl 1 (k mod 32)) = 2 ^ k.
Proof.
  intros k Hk. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l. pose proof (pow2_le15 k Hk). apply swrap32_small. lia.
Qed.
Lemma sllw_m1 : forall k, 0 <= k <= 15 -> bv_swrap 32 (Z.shiftl (-1) (k mod 32)) = - 2 ^ k.
Proof.
  intros k Hk. rewrite Z.mod_small by lia. rewrite Z.shiftl_mul_pow2 by lia. pose proof (pow2_le15 k Hk).
  rewrite swrap32_small by lia. lia.
Qed.
Lemma srlw_small : forall a b, 0 <= a < 2147483648 -> 0 <= b < 32 ->
  bv_swrap 32 (Z.shiftr (a mod 4294967296) (b mod 32)) = Z.shiftr a b.
Proof.
  intros a b Ha Hb. rewrite !Z.mod_small by lia.
  assert (0 <= Z.shiftr a b <= a).
  { rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 b ltac:(lia) ltac:(lia)).
    split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; [lia | nia]]. }
  apply swrap32_small. lia.
Qed.
Lemma wrap8_mod : forall z, wrap8 z = z mod 256.
Proof. intros z. unfold wrap8. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma lowS_small : forall z, 0 <= z < 4294967295 -> lowS z = z.
Proof. intros z Hz. unfold lowS. destruct (Z.eqb_spec z 4294967295); [lia | reflexivity]. Qed.
Lemma sextw_lowS : forall z, (z = 4294967295 \/ 0 <= z < 32768) ->
  Z_to_bv 64 (bv_swrap 32 (lowS z mod 18446744073709551616 + 0)) = Z_to_bv 64 (lowS z).
Proof.
  intros z [->|Hz]; [reflexivity|]. rewrite lowS_small by lia. rewrite Z.mod_small by lia. rewrite Z.add_0_r.
  rewrite swrap32_small by lia. reflexivity.
Qed.

Section CANSEC1. Context {rc : runConstT}.

Definition mst (SP SPA S F PB LP TY : Z) (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (rt mx : Z) (st : ItSt)
    (x5 x6 x7 x11 x16 x29 x30 x31 : word) (pc : Z) (m : amem) : machine_state :=
  (* [U14B] A2 2026-11-12: the 1.4 combined table loop keeps drop in t0 (1.3.1 a7: 0x974e0 li t0,0), len in t1 (1.3.1 s9:
     0x97518 mv t1,a2) and huff in t4 (1.3.1 t3: 0x974dc li t4,0); the 1.3.1 temporaries t0 / t1 / t2 / t4 / t5 / t6 are
     a7 / t2 / t3 / t5 / t6 / s9 at 1.4. The binders keep their 1.3.1 order and meaning (as G's U1A mst). *)
  bst SP SPA S F PB LP TY gp tp FR fc (Z_to_bv 64 (S + 1384 + 4 * t_next st)) (Z_to_bv 64 (t_drop st)) (Z_to_bv 64 (t_len st)) x6
      (Z_to_bv 64 (S + 808 + 2 * t_sym st)) x11
      (Z_to_bv 64 (t_len st - t_drop st)) (Z_to_bv 64 (Z.shiftr PB 3 + 2147450880))
      (Z_to_bv 64 rt) (Z_to_bv 64 mx) x16 x5 x31 x7 (Z_to_bv 64 (t_huff st)) x29 x30 pc m.

Definition minv (SPA S F PB : Z) (m1 m : amem) (ty : codetype) (rt nx bits : Z) (lf w1 : Z -> Z) (st : ItSt)
    (v0 v8 v16 v56 v128 v136 : word) (of : Z -> Z) : Prop :=
  (* [U14B] A2 2026-11-12: the 1.4 combined frame: extra in slot 16 (1.3.1 48), base in 48 (1.3.1 64), the flag XFL in 56,
     and the spill v56 of 1.3.1's slot 56 in 64 (0x97624 sd a2,64(s1)). The binder v16 stays (unused: slot 16 is extra). *)
  itb_inv SPA S F PB m1 m v0 v8 (Z_to_bv 64 (EXA ty S)) (Z_to_bv 64 (Z.shiftr (S + 160) 3 + 2147450880))
          (Z_to_bv 64 (2 ^ rt - 1)) (Z_to_bv 64 (t_used st)) (Z_to_bv 64 (BSA ty S)) (Z_to_bv 64 (XFL ty)) v56 (Z_to_bv 64 (it_match ty))
          (Z_to_bv 64 (Z.lxor (S + 808) 18446744073709551615)) (Z_to_bv 64 (lowS (t_low st))) (Z_to_bv 64 (t_curr st)) (Z_to_bv 64 (t_sym st))
          (Z_to_bv 64 (Z.lxor (F + 32) 18446744073709551615)) (Z_to_bv 64 (S + 160)) v128 v136 (Z_to_bv 64 F)
          (arr_get (t_count st)) of lf w1 (arr_get (t_tbl st))
          (Z_to_bv 64 (S + 1384 + 4 * nx)) (Z_to_bv 64 bits).

Definition ret_pre (SP SPA S F PB LP TY : Z) (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (m1 : amem)
    (r : Z) (lf wf' cf' : Z -> Z) (next' bits' : word) : machine_state -> Prop :=
  fun ms' => exists (m : amem) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 : word)
                    (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 : word) (cnt of : Z -> Z),
    ms' = bst SP SPA S F PB LP TY gp tp FR fc x1 x5 x6 x7 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 0x97a80 m
    /\ itb_inv SPA S F PB m1 m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 cnt of lf wf' cf' next' bits'.

End CANSEC1.

Definition spure (work1 : arr) (rt nx : Z) (st : ItSt) : Prop :=
  t_work st = work1 /\ BOX (t_low st = 4294967295 \/ 0 <= t_low st < 32768) /\ BOX (t_drop st = 0 \/ t_drop st = rt) /\
  0 <= t_next st /\ nx <= t_next st /\
  (forall j, 0 <= j < 16 -> 0 <= arr_get (t_count st) j < 65536) /\
  (forall j, 0 <= j < 1444 -> 0 <= arr_get (t_tbl st) j < 4294967296) /\
  arr_len (t_count st) = 16 /\ arr_len (t_tbl st) = 1444.
Ltac open_spure H :=
  let H' := fresh "SPc" in pose proof H as H';
  destruct H' as (WK & LOWR & DROPR & NX0 & NX1 & HCr & HTr & CL & TL).
