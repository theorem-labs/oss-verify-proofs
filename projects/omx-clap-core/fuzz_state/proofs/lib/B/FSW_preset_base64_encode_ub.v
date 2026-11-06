(* preset_base64_encode 0x84700 (preset_file.c:577-608), image B (fs.asan-ubsan): the UBSAN half of the walk, as plain
   arithmetic over Z. No engine, no image, no ASan kit (like lib/A/FSW_preset_base64_encode_blocks.v): every lemma is a
   fact about the numbers the walk's registers hold, so the walk lanes apply it at each decider.

   What this file proves. Image B carries UBSan checks image A does not. Each one is a branch to 0x84b58 `unimp`.
   The B listing (fs.asan-ubsan 5ac5ce0954f8, 0x84700 .. 0x84c48) has 24 such branches, all in the loop body
   0x84784 .. 0x84914 and the tail 0x849bc .. 0x84b24; none is in the entry, the malloc arm or the epilogue. For each
   one, enc_ub_<addr> states that the branch is NOT taken: the branch's boolean, over the unsigned values (bv_unsigned)
   the compared registers hold, is false (for `bgeu`, the `bltu` it negates is true). The premises are only
   encode_spec's bounds (lib/B/FSH_Fn_writer.v: 0 <= len <= 2^27, 4096 <= data, data + len <= alloc_ceiling), the malloc
   post's q + enc_size len <= alloc_ceiling (enc_size len = (len + 2) / 3 * 4 + 1, the same term by delta), and the
   loop's own index facts: the round r with 0 <= r, 3r + 3 <= len (the round step's premises), or the tail's R full
   rounds with 0 <= R, 3R < len. No decider needed any other fact.

   The register file the checks read (B listing; old B donor's BL at lib/B/Prog/preset_base64_encode_blocks.v:374-379):
     s0 = len, s1 = data, a4 = G_B64 = 0x21060 = 135264,
     a6 = not s1 = 2^64 - 1 - data, a7 = data + 1, t0 = snez s1, t1 = not a4 = 18446744073709416351, t2 = -1,
     loop round r: a5 = 3r + 2, a1 = t6 = q + 4r at the head 0x84784;
     tail after R rounds: a3 = 3R, a1 = q + 4R at 0x849bc (R = 0 on the len < 3 arm 0x849a0).
   The UBSan checks are of three kinds:
     (P) pointer overflow of `data + off` (C: in[i]): `bltu res, base`, the `(base != 0) == (res != 0)` test
         (snez / seqz / xor / beqz) and `bltu ~base, off` / `bgeu off - 1, ~base`;
     (N) null base: `beqz s1`;
     (T) the table pointer `g_b64 + idx`: `bltu ~G_B64, idx`, idx a 6-bit index;
     (O) the output pointer `p + 1` (C: *p++): `beq p, -1`.
   Deciders, kind, lemma:
     0x8478c P bltu a3,s1        a3 = data + 3r                  enc_ub_8478c
     0x84798 P beqz t4           t4 = snez data ^ seqz (data+3r) enc_ub_84798
     0x8479c N beqz s1                                           enc_ub_8479c
     0x847b8 P bltu a6,a3        a3 = 3r + 1                     enc_ub_847b8
     0x847bc P bltu a6,a5        a5 = 3r + 2                     enc_ub_847bc
     0x847f4 T bltu t1,a2        a2 = b0 / 4                     enc_ub_847f4
     0x847f8 O beq t3,t2         t3 = q + 4r                     enc_ub_847f8
     0x84840 T bltu t1,a3        a3 = (b0 mod 4) * 16 + b1 / 16  enc_ub_84840
     0x84848 O beq t6,t2         t6 = q + 4r + 1                 enc_ub_84848
     0x84888 T bltu t1,a3        a3 = (b1 mod 16) * 4 + b2 / 64  enc_ub_84888
     0x84890 O beq t6,t2         t6 = q + 4r + 2                 enc_ub_84890
     0x848c8 T bltu t1,a3        a3 = b2 mod 64                  enc_ub_848c8
     0x848d0 O beq t6,t2         t6 = q + 4r + 3                 enc_ub_848d0
     0x849c0 P bltu a2,s1        a2 = data + 3R                  enc_ub_849c0
     0x849d0 P beqz a5           a5 = snez data ^ seqz (data+3R) enc_ub_849d0
     0x849d4 N beqz s1                                           enc_ub_849d4
     0x849f8 P bgeu a3,a6        a3 = 3R                         enc_ub_849f8
     0x84a2c T bltu a7,a2        a2 = bA / 4                     enc_ub_84a2c
     0x84a34 O beq a1,t0         a1 = q + 4R                     enc_ub_84a34
     0x84a70 T bltu a7,a3        a3 = (bA mod 4) * 16 + bB / 16, or (bA mod 4) * 16 on one byte    enc_ub_84a70
     0x84a7c O beq a2,t0         a2 = q + 4R + 1                 enc_ub_84a7c
     0x84ab8 T bltu a7,a2        a2 = (bB mod 16) * 4            enc_ub_84ab8
     0x84ae4 O beq a3,a2         a3 = q + 4R + 2                 enc_ub_84ae4
     0x84b04 O beq a2,a5         a2 = q + 4R + 3                 enc_ub_84b04
   (in the tail a7 = not a4 is t1 again; a2 / t0 / a5 = -1 at the O checks.) The 6-bit indices are in the forms
   lib/A/FSW_preset_base64_encode_blocks.v's enc_ix0..enc_ix3 / enc_t0 / enc_t1_one / enc_t2 produce from the shift
   words. enc_ub_rng_loop / enc_ub_rng_tail give the walk the no-wrap bounds of every address the round and the
   tail form, so each register's unsigned value is the plain sum used above (YN3v U_off / U_add_off_atom), and
   enc_ub_not turns the engine's `xori _, -1` into 2^64 - 1 - x.

   rule 24: proves function preset_base64_encode (part ub; reuse search: proof-index preset_base64_encode,
   ported from a working branch 402eb5565fc + donor a working branch b96980d72d1)
   Port-from: A lib/A/FSW_preset_base64_encode_blocks.v:1-40 (402eb5565fc; form: model half, pure arithmetic) and
   lib/A/FSW_preset_base64_encode.v:1241-1244 encR_loop_regs, 1510-1513 encR_exit_regs, 1571-1572 encR_round_step's
   index premises (the quantities r, 3r + 2, q + 4r; R, 3R, q + 4R); image A has no UBSan check, so the checks
   themselves come from the old B donor a working branch 7676bbb0e23 lib/B/Prog/preset_base64_encode_blocks.v:
   328-344 (lnot64 -> enc_ub_not), 353 (HD0, here 4096 <= data), 374-379 (BL register file), 383-386 (brk: each
   unimp branch refuted by lia / a computed lxor), 401-459 (enc_B_r1 / r2: 0x8478c .. 0x847bc), 470-633
   (enc_B_o0 .. o3: 0x847f4 .. 0x848d0), 792-1051 (enc_tail_c0 .. enc_tail_e: 0x849c0 .. 0x84b04). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section UB. Context {rc : YM05.RunCeil}.

(* ---- shared arithmetic ---- *)

(* `not x` = `xori x, -1` on a 64-bit value (donor lnot64) *)
Lemma enc_ub_not : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
intros x Hx. change 18446744073709551615 with (Z.ones 64).
assert (HB : forall n, 64 <= n -> Z.testbit x n = false).
{ intros n Hn. destruct (Z.eq_dec x 0) as [->|Hx0]; [apply Z.testbit_0_l|].
  apply Z.bits_above_log2; [lia|]. pose proof (proj1 (Z.log2_lt_pow2 x 64 ltac:(lia)) ltac:(lia)). lia. }
assert (HD : Z.ldiff x (Z.ones 64) = 0).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.ldiff_spec, Z.bits_0.
  destruct (Z.lt_ge_cases n 64).
  + rewrite Z.ones_spec_low by lia. destruct (Z.testbit x n); reflexivity.
  + rewrite HB by lia. reflexivity. }
rewrite (Z.sub_nocarry_ldiff (Z.ones 64) x HD).
apply Z.bits_inj'. intros n Hn. rewrite Z.lxor_spec, Z.ldiff_spec.
destruct (Z.lt_ge_cases n 64).
+ rewrite Z.ones_spec_low by lia. destruct (Z.testbit x n); reflexivity.
+ rewrite Z.ones_spec_high by lia. rewrite HB by lia. reflexivity.
Qed.

(* the output block holds the four letters of every round started before len: enc_size len >= 4R + 5 *)
Lemma enc_ub_size_ge : forall len R, 0 <= R -> 3 * R < len -> 4 * R + 5 <= (len + 2) / 3 * 4 + 1.
Proof.
intros len R HR HL.
assert (R + 1 <= (len + 2) / 3) by (apply Z.div_le_lower_bound; lia).
lia.
Qed.

(* (T): t1 = not G_B64 = 2^64 - 1 - 0x21060 is above every 6-bit index *)
Lemma enc_ub_tbl : forall v, 0 <= v < 64 -> (18446744073709416351 <? v) = false.
Proof. intros v Hv. apply Z.ltb_ge. lia. Qed.

(* (O): no byte of the output block, nor the NUL slot after it, sits at 2^64 - 1 *)
Lemma enc_ub_out : forall len q R k, 0 <= R -> 3 * R < len -> 0 <= k <= 3 ->
  q + ((len + 2) / 3 * 4 + 1) <= alloc_ceiling -> (q + 4 * R + k =? 18446744073709551615) = false.
Proof.
intros len q R k HR HL Hk HQ.
pose proof (enc_ub_size_ge len R HR HL). pose proof alloc_ceiling_lt.
apply Z.eqb_neq. lia.
Qed.

(* (P), the `(base != 0) == (res != 0)` test: false once base and res are both nonzero *)
Lemma enc_ub_nz : forall base res, 0 < base -> 0 < res ->
  (Z.lxor (if 0 <? base then 1 else 0) (if res <? 1 then 1 else 0) =? 0) = false.
Proof.
intros base res Hb Hr.
replace (0 <? base) with true by (symmetry; apply Z.ltb_lt; lia).
replace (res <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
reflexivity.
Qed.

(* ---- no wrap: every address the round and the tail form is a plain sum below alloc_ceiling < 2^47 ---- *)

Lemma enc_ub_rng_loop : forall data len q r,
  data + len <= alloc_ceiling -> q + ((len + 2) / 3 * 4 + 1) <= alloc_ceiling ->
  0 <= r -> 3 * r + 3 <= len ->
  data + 3 * r + 3 <= alloc_ceiling /\ q + 4 * r + 4 < alloc_ceiling /\ alloc_ceiling < 2 ^ 47.
Proof.
intros data len q r HD HQ Hr Hr3.
pose proof (enc_ub_size_ge len r Hr ltac:(lia)). pose proof alloc_ceiling_lt.
lia.
Qed.

Lemma enc_ub_rng_tail : forall data len q R,
  data + len <= alloc_ceiling -> q + ((len + 2) / 3 * 4 + 1) <= alloc_ceiling ->
  0 <= R -> 3 * R < len ->
  data + 3 * R + 1 <= alloc_ceiling /\ q + 4 * R + 4 < alloc_ceiling /\ alloc_ceiling < 2 ^ 47.
Proof.
intros data len q R HD HQ HR HL.
pose proof (enc_ub_size_ge len R HR HL). pose proof alloc_ceiling_lt.
lia.
Qed.

(* ================= the loop body 0x84784 .. 0x84914, round r ================= *)

(* 0x84784..0x8478c  add a2,s1,a5; addi a3,a2,-2; bltu a3,s1: in[3r] does not wrap below data *)
Lemma enc_ub_8478c : forall data r, 0 <= r -> (data + 3 * r <? data) = false.
Proof. intros data r Hr. apply Z.ltb_ge. lia. Qed.

(* 0x84770 snez t0,s1; 0x84790..0x84798 seqz t4,a3; xor t4,t0,t4; beqz t4: data and data + 3r both nonzero *)
Lemma enc_ub_84798 : forall data r, 4096 <= data -> 0 <= r ->
  (Z.lxor (if 0 <? data then 1 else 0) (if data + 3 * r <? 1 then 1 else 0) =? 0) = false.
Proof. intros data r HD Hr. apply enc_ub_nz; lia. Qed.

(* 0x8479c  beqz s1: data is not null *)
Lemma enc_ub_8479c : forall data, 4096 <= data -> (data =? 0) = false.
Proof. intros data HD. apply Z.eqb_neq. lia. Qed.

(* 0x847b4..0x847b8  addi a3,a5,-1; bltu a6,a3 (a6 = not data): data + (3r + 1) does not wrap *)
Lemma enc_ub_847b8 : forall data len r, data + len <= alloc_ceiling -> 0 <= r -> 3 * r + 3 <= len ->
  (18446744073709551615 - data <? 3 * r + 1) = false.
Proof. intros data len r HD Hr Hr3. pose proof alloc_ceiling_lt. apply Z.ltb_ge. lia. Qed.

(* 0x847bc  bltu a6,a5: data + (3r + 2) does not wrap *)
Lemma enc_ub_847bc : forall data len r, data + len <= alloc_ceiling -> 0 <= r -> 3 * r + 3 <= len ->
  (18446744073709551615 - data <? 3 * r + 2) = false.
Proof. intros data len r HD Hr Hr3. pose proof alloc_ceiling_lt. apply Z.ltb_ge. lia. Qed.

(* 0x847f0..0x847f4  srli a2,t5,2; bltu t1,a2: g_b64 + b0 / 4 does not wrap *)
Lemma enc_ub_847f4 : forall b0, 0 <= b0 < 256 -> (18446744073709416351 <? b0 / 4) = false.
Proof. intros b0 H0. apply enc_ub_tbl. Z.div_mod_to_equations. lia. Qed.

(* 0x847f8  beq t3,t2: the round's first output byte q + 4r is not at 2^64 - 1 *)
Lemma enc_ub_847f8 : forall len q r, 0 <= r -> 3 * r + 3 <= len ->
  q + ((len + 2) / 3 * 4 + 1) <= alloc_ceiling -> (q + 4 * r =? 18446744073709551615) = false.
Proof.
intros len q r Hr Hr3 HQ. pose proof (enc_ub_out len q r 0 Hr ltac:(lia) ltac:(lia) HQ) as E.
rewrite Z.add_0_r in E. exact E.
Qed.

(* 0x84834..0x84840  slli a3,a3,0x2e; srli a3,a3,0x3a; bltu t1,a3: g_b64 + the second index does not wrap *)
Lemma enc_ub_84840 : forall b0 b1, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  (18446744073709416351 <? (b0 mod 4) * 16 + b1 / 16) = false.
Proof. intros b0 b1 H0 H1. apply enc_ub_tbl. Z.div_mod_to_equations. lia. Qed.

(* 0x84844..0x84848  addi t6,t3,1; beq t6,t2: q + 4r + 1 *)
Lemma enc_ub_84848 : forall len q r, 0 <= r -> 3 * r + 3 <= len ->
  q + ((len + 2) / 3 * 4 + 1) <= alloc_ceiling -> (q + 4 * r + 1 =? 18446744073709551615) = false.
Proof. intros len q r Hr Hr3 HQ. exact (enc_ub_out len q r 1 Hr ltac:(lia) ltac:(lia) HQ). Qed.

(* 0x8487c..0x84888  slli a3,a3,0x34; srli a3,a3,0x3a; bltu t1,a3: g_b64 + the third index does not wrap *)
Lemma enc_ub_84888 : forall b1 b2, 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  (18446744073709416351 <? (b1 mod 16) * 4 + b2 / 64) = false.
Proof. intros b1 b2 H1 H2. apply enc_ub_tbl. Z.div_mod_to_equations. lia. Qed.

(* 0x8488c..0x84890  addi t6,t6,1; beq t6,t2: q + 4r + 2 *)
Lemma enc_ub_84890 : forall len q r, 0 <= r -> 3 * r + 3 <= len ->
  q + ((len + 2) / 3 * 4 + 1) <= alloc_ceiling -> (q + 4 * r + 2 =? 18446744073709551615) = false.
Proof. intros len q r Hr Hr3 HQ. exact (enc_ub_out len q r 2 Hr ltac:(lia) ltac:(lia) HQ). Qed.

(* 0x848c0..0x848c8  andi a3,t4,63; bltu t1,a3: g_b64 + the fourth index does not wrap *)
Lemma enc_ub_848c8 : forall b2, 0 <= b2 < 256 -> (18446744073709416351 <? b2 mod 64) = false.
Proof. intros b2 H2. apply enc_ub_tbl. Z.div_mod_to_equations. lia. Qed.

(* 0x848cc..0x848d0  addi t6,t6,1; beq t6,t2: q + 4r + 3 *)
Lemma enc_ub_848d0 : forall len q r, 0 <= r -> 3 * r + 3 <= len ->
  q + ((len + 2) / 3 * 4 + 1) <= alloc_ceiling -> (q + 4 * r + 3 =? 18446744073709551615) = false.
Proof. intros len q r Hr Hr3 HQ. exact (enc_ub_out len q r 3 Hr ltac:(lia) ltac:(lia) HQ). Qed.

(* ================= the tail 0x849bc .. 0x84b24, after R full rounds (3R < len <= 3R + 2) ================= *)

(* 0x849bc..0x849c0  add a2,s1,a3; bltu a2,s1: in[3R] does not wrap below data *)
Lemma enc_ub_849c0 : forall data R, 0 <= R -> (data + 3 * R <? data) = false.
Proof. intros data R HR. apply Z.ltb_ge. lia. Qed.

(* 0x849c4..0x849d0  snez a5,s1; seqz a6,a2; xor a5,a5,a6; beqz a5: data and data + 3R both nonzero *)
Lemma enc_ub_849d0 : forall data R, 4096 <= data -> 0 <= R ->
  (Z.lxor (if 0 <? data then 1 else 0) (if data + 3 * R <? 1 then 1 else 0) =? 0) = false.
Proof. intros data R HD HR. apply enc_ub_nz; lia. Qed.

(* 0x849d4  beqz s1: data is not null *)
Lemma enc_ub_849d4 : forall data, 4096 <= data -> (data =? 0) = false.
Proof. intros data HD. apply Z.eqb_neq. lia. Qed.

(* 0x849f4..0x849f8  not a6,s1; bgeu a3,a6: data + (3R + 1) does not wrap. The branch is taken on
   negb (3R <? not data), so it is not taken when this `<?` is true. *)
Lemma enc_ub_849f8 : forall data len R, data + len <= alloc_ceiling -> 0 <= R -> 3 * R < len ->
  (3 * R <? 18446744073709551615 - data) = true.
Proof. intros data len R HD HR HL. pose proof alloc_ceiling_lt. apply Z.ltb_lt. lia. Qed.

(* 0x84a20..0x84a2c  slli a3,a2,0x10; srli a2,a3,0x12; not a7,a4; bltu a7,a2: g_b64 + bA / 4 does not wrap *)
Lemma enc_ub_84a2c : forall b0, 0 <= b0 < 256 -> (18446744073709416351 <? b0 / 4) = false.
Proof. intros b0 H0. apply enc_ub_tbl. Z.div_mod_to_equations. lia. Qed.

(* 0x84a30..0x84a34  li t0,-1; beq a1,t0: the tail's first output byte q + 4R *)
Lemma enc_ub_84a34 : forall len q R, 0 <= R -> 3 * R < len ->
  q + ((len + 2) / 3 * 4 + 1) <= alloc_ceiling -> (q + 4 * R =? 18446744073709551615) = false.
Proof.
intros len q R HR HL HQ. pose proof (enc_ub_out len q R 0 HR HL ltac:(lia) HQ) as E.
rewrite Z.add_0_r in E. exact E.
Qed.

(* 0x84a60..0x84a70  or a3,a6,a3; slli a3,a3,0x2e; srli a3,a3,0x3a; bltu a7,a3: g_b64 + the second index does
   not wrap, on the two-byte arm ((bA mod 4) * 16 + bB / 16) and on the one-byte arm (a6 = 0: (bA mod 4) * 16) *)
Lemma enc_ub_84a70 : forall b0 b1, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  (18446744073709416351 <? (b0 mod 4) * 16 + b1 / 16) = false /\
  (18446744073709416351 <? (b0 mod 4) * 16) = false.
Proof. intros b0 b1 H0 H1. split; apply enc_ub_tbl; Z.div_mod_to_equations; lia. Qed.

(* 0x84a74..0x84a7c  addi a2,a1,1; li t0,-1; beq a2,t0: q + 4R + 1 *)
Lemma enc_ub_84a7c : forall len q R, 0 <= R -> 3 * R < len ->
  q + ((len + 2) / 3 * 4 + 1) <= alloc_ceiling -> (q + 4 * R + 1 =? 18446744073709551615) = false.
Proof. intros len q R HR HL HQ. exact (enc_ub_out len q R 1 HR HL ltac:(lia) HQ). Qed.

(* 0x84ab0..0x84ab8  srli a2,a6,6; andi a2,a2,60; bltu a7,a2: g_b64 + (bB mod 16) * 4 does not wrap *)
Lemma enc_ub_84ab8 : forall b1, 0 <= b1 < 256 -> (18446744073709416351 <? (b1 mod 16) * 4) = false.
Proof. intros b1 H1. apply enc_ub_tbl. Z.div_mod_to_equations. lia. Qed.

(* 0x84adc..0x84ae4  addi a3,a1,2; li a2,-1; beq a3,a2: q + 4R + 2 *)
Lemma enc_ub_84ae4 : forall len q R, 0 <= R -> 3 * R < len ->
  q + ((len + 2) / 3 * 4 + 1) <= alloc_ceiling -> (q + 4 * R + 2 =? 18446744073709551615) = false.
Proof. intros len q R HR HL HQ. exact (enc_ub_out len q R 2 HR HL ltac:(lia) HQ). Qed.

(* 0x84af8..0x84b04  addi a2,a1,3; li a5,-1; beq a2,a5: q + 4R + 3 *)
Lemma enc_ub_84b04 : forall len q R, 0 <= R -> 3 * R < len ->
  q + ((len + 2) / 3 * 4 + 1) <= alloc_ceiling -> (q + 4 * R + 3 =? 18446744073709551615) = false.
Proof. intros len q R HR HL HQ. exact (enc_ub_out len q R 3 HR HL ltac:(lia) HQ). Qed.

End UB.
