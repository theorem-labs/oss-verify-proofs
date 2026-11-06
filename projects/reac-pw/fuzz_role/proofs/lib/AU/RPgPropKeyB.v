(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, as pa_i_region_nth over a restricted state and pa_i_field) and proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v at a0d3fb0309b (aj_intrin_at, as pa_i_memset_at: at OSet on rsegs, its post adds same_io from the contract's same_but_materialized); the rest of the file is new: the block lemma pa_int7 of LLVMFuzzerTestOneInput's shape-7 Int pod block and its helpers. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a6181 (the block lemma pa_int7 and its helpers) and the piece pa_piece_int7 of proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at the same commit, for reac-pw/fuzz_rate image A: rate's pcs (SEL7 0x80e6c, the memset call 0x80fec to 0x51cfc with return 0x80ff0, LATCH7 0x82530), registers (s6 / s7 / s2 for role's s4 / s5 / s7) and real-frame cells (i at R+0xf8, -0x3ffd at R+0x130, -0x4001 at R+0x118 and in s10); rate's block keeps what is left of the input (s8) in s10 across the pad and restores s8 and s10 at its end, so both join the clobbered set and the block's relation states their end values; the call is lib/A/RtPgSteps.v rts_intrin_at (in place of pa_i_memset_at), the region lemma its rts_region_nth (in place of pa_i_region_nth); the block post is RtPgSteps' rts_post; the cut lists of the piece are lib/A/RtPgSeg.v's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgPropIntB.v, with its module paths, module names, addresses and numbers changed; 497 of its 601 lines of code are new or changed and 486 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropKeyB.v at a529a88a6181 (the key block
   pa_key) and the key piece pa_piece_key of proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at the same commit, for
   reac-pw/fuzz_rate image A: rate's pcs, registers (s6 = shadow address of pp + 0x4000, s7 = pp + 0x4000, s2 = K,
   s10 = -0x4001, the capacity bound both tests compare with) and real-frame cells (0x10003 at R+0x68, 0x80001 at
   R+0x80, -0x3ffd at R+0x130, seen' to R+0xc8, first to R+0x110, at to R+0xe0); the block post is lib/A/RtPgSteps.v
   rts_post; the cut lists are lib/A/RtPgSeg.v's. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgPropKeyB.v at 533bf30ff015 for image B
   (fuzz_rate.asan-ubsan): image B's pcs (SELK 0x810a4, SELS 0x81210, SELI 0x82398); pp, &pp->len, the shadow address
   of &pp->len, ~pp, -0x4001 and -0x3ffd come from the real frame's cells (R+0x168, R+0x158, R+0x170, R+0x108, R+0xc0,
   R+0x120) and len from &pp->len, as atoms with closed-numeral bounds and alias facts, so that the engine decides the
   two capacity tests and the four UBSan trap tests; s4 = K; seen is in s6, seen' goes to a4 and first to R+0x160,
   at is not computed; the block post is lib/AU/RtPgStepsB.v rtsb_post, the cut lists are lib/AU/RtPgSegB.v's, the kit
   and the helpers lib/AU/RtPgPropBKit.v / RtPgPropBLib.v (pa_ becomes pab_). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgPropBKey.v at 6aea585e8b5b for
   reac-pw/fuzz_role image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role, the segments lib/AU/Img0.v
   rsegs; role B's pcs (SELK 0x8086c, SELS 0x809d4, SELI 0x81b98); &pp->len is the register s6 (the cut's
   pp + 0x4000), -0x3ffd and -0x4001 are loaded once into t0 / t2 from R+0xc0 / R+0xa8, the keys 0x80001 / 0x10003
   come from R+0xb0 / R+0x70, ~pp from R+0xf8, pp from R+0x140, the shadow address of &pp->len from R+0x148; s11 = K;
   seen is in s2, seen' goes to a4, first to R+0x138 and s8 := pp before the arm tests; the block post is
   lib/AU/RPgSteps.v rl_wpost, the cut lists lib/AU/RPgSeg.v's, the kit and the helpers lib/AU/RPgPropKit.v /
   RPgPropLib.v; pab_ becomes pa_ and ss_keyb ss_key. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address below is measured on its unstripped
   twin sha256 dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the key block
   SELK 0x8086c of the property loop of LLVMFuzzerTestOneInput, as a block lemma over lib/AU/RPgPropKit.v, and the
   piece rs_piece_W4_key_stmt (SELK -> SELS / SELI) of lib/AU/RPgSeg.v. Proves no function (kind: segment lemma).

   THE BLOCK 0x8086c -> 0x809d4 (params Struct) / 0x81b98 (Int 7), pod.h:177-180 twice (pod_put32) and 405-412:
     0x8086c andi a3,a1,3; a5 = R+0xb0 (0x80001), t0 = R+0xc0 (-0x3ffd), t2 = R+0xa8 (-0x4001); 0x8087c bnez a3,
     else 0x80880 a5 = R+0x70 (0x10003); 0x80884 the instrumented check of &pp->len through its shadow address in
     R+0x148 (error path 0x82814, never taken); len from s6 = &pp->len; 0x8089c the capacity test bltu len - 0x3ffd,
     t2 (not taken); the UBSan trap tests 0x808a8 bltu len, 0x4001 and 0x808b4 bgeu ~pp (R+0xf8), len (both to the
     non-trap side; the trap side is 0x808ac / 0x808b8 j 0x82604); a0 = pp (R+0x140) + len; the instrumented checks
     of a0 0x808cc and a0 + 3 0x808e4 (slow blocks 0x81dac / 0x81db8 of the `andi; bge error path; j back` form,
     never reached: the shadow bytes of pp's block are 0); the four byte stores of a5; the check of &pp->len 0x80908;
     len += 4; the second capacity test 0x80928 and the trap tests 0x8092c / 0x8093c; the checks of pp + len + 4
     0x80950 / 0x80968 (slow blocks 0x81e10 / 0x81e1c, never reached); four zero bytes; the check of &pp->len
     0x80984; len += 4; 0x809a0 a4 = s2, or 1 when a3 <> 0 (seen'); first := snez(a3) & seqz(s2) -> R+0x138;
     0x809bc s8 = pp (R+0x140); 0x809c0 bnez a3, else 0x809c4 j SELI; 0x809c8 andi a1,a1,16; 0x809cc beqz a1 -> SELS,
     else 0x809d0 j SELI.
   THE ROUTE. One straight run of the token engine per case of (sel mod 4 = 0, bit 4 of sel, seen): the entry facts
   carry the case as alias facts (sel & 3 -> 0 or the atom 36 = sel mod 4 in [1, 3]; sel & 0x10 -> 0 or 0x10) and
   seen as an exact atom fact, so every data branch and every value is decided. Every atom bound is a closed
   numeral: pp (atom 33), len (34), pp + len (35: the alias of pp + len and, at offset 4, of pp + (len + 4)),
   len - 0x3ffd and len + 4 - 0x3ffd (37, 38: the aliases of the two capacity sums) and ~pp (39: the cell R+0xf8),
   so the two capacity tests and the four trap tests are decided by the ranges. s11 holds K as SOff 32 0, s6 holds
   pp + 0x4000 as SOff 33 0x4000 and the cell R+0x148 the shadow address of pp + 0x4000 as the engine's shadow form,
   so the shadow entries of pp's block and of the 16 bytes from pp + len decide every instrumented check. The write
   rights: pp's block was made since the journal's start (RPgBase.rl_fresh_awr), the slot R+0x138 lies in the
   caller's stack window. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgImgA RPgSteps RPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgSeg RPgPropKit RPgPropLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Local Arguments x_STK {segs} _.
Local Arguments x_sp0 {segs} _.
Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _.
Local Arguments x_S {segs} _.
Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _.
Local Arguments x_md0 {segs} _.
Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _.
Local Arguments x_regs {segs} _.
Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _.
Local Arguments x_W {segs} _.
Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _.
Local Arguments x_RLO {segs} _.
Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _.
Local Arguments x_pos {segs} _.

(* ---- the entry state of 0x8086c ----
   env slots: 0 .. 31 the registers (9 R, 11 sel, 18 seen, 22 &pp->len), 32 the shadow offset K, 33 pp, 34 len,
   35 pp + len, 36 sel mod 4, 37 len - 0x3ffd, 38 len + 4 - 0x3ffd, 39 ~pp. *)
Definition pa_k_x (pp plen sel : Z) : list Z :=
[pp; plen; pp + plen; sel mod 4; plen - 16381; plen - 16377; Z.lnot pp].
(* the shadow entries: pp's whole block, and the 16 bytes from pp + len *)
Definition pa_k_SH : list shent := [mkSHE 33 0 19744; mkSHE 35 0 16].
(* every bound a closed numeral *)
Definition pa_k_atoms (s : Z) : list (nat * afact) :=
[ (9%nat, mkAF 70368744177664 140737488355328 4); (33%nat, mkAF 4096 140737479946976 4);
  (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (34%nat, mkAF 0 5424 0); (11%nat, mkAF 0 255 0); (18%nat, mkAF s s 0);
  (35%nat, mkAF 4096 140737479952400 0); (37%nat, mkAF 18446744073709535235 18446744073709540659 0);
  (38%nat, mkAF 18446744073709535239 18446744073709540663 0);
  (39%nat, mkAF 18446603336229604639 18446744073709547519 0) ].
(* the case: z3 = (sel mod 4 =? 0), b4 = bit 4 of sel *)
Definition pa_k_ex (z3 : bool) : list (nat * afact) := if z3 then [] else [(36%nat, mkAF 1 3 0)].
Definition pa_k_al (z3 b4 : bool) : list (sv * sv) :=
[ (SAlu ALU_AND (SOff 11 0) (SLit 3), if z3 then SLit 0 else SOff 36 0);
  (SAlu ALU_AND (SOff 11 0) (SLit 16), SLit (if b4 then 16 else 0)) ].
Definition pa_k_al0 : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 33 0) (SOff 34 0), SOff 35 0); (SAlu ALU_ADD (SOff 33 0) (SOff 34 4), SOff 35 4);
  (SOff 34 (-16381), SOff 37 0); (SOff 34 (-16377), SOff 38 0) ].
Definition pa_k_facts (z3 b4 : bool) (s : Z) : facts :=
mkFacts (pa_k_atoms s ++ pa_k_ex z3) [] (pa_k_al0 ++ pa_k_al z3 b4).
(* s11 = K, s6 = pp + 0x4000 *)
Definition pa_k_regs : list sv := sr_set (sr_set sr_atoms (27%bv : bv 5) (SOff 32 0)) (22%bv : bv 5) (SOff 33 16384).
(* the cells the block reads (R+0x148: the shadow address of pp + 0x4000), the slot it writes (R+0x138), &pp->len
   and the 8 bytes from pp + len *)
Definition pa_k_mem : smem :=
[ YP09.mkRegion (Some 9%nat) 0x70 0x78 0 0 [ YP09.mkChunk 0x70 (CVal 8 (SLit 0x10003)) ];
  YP09.mkRegion (Some 9%nat) 0xa8 0xb0 0 0 [ YP09.mkChunk 0xa8 (CVal 8 (SLit (-16385))) ];
  YP09.mkRegion (Some 9%nat) 0xb0 0xb8 0 0 [ YP09.mkChunk 0xb0 (CVal 8 (SLit 0x80001)) ];
  YP09.mkRegion (Some 9%nat) 0xc0 0xc8 0 0 [ YP09.mkChunk 0xc0 (CVal 8 (SLit (-16381))) ];
  YP09.mkRegion (Some 9%nat) 0xf8 0x100 0 0 [ YP09.mkChunk 0xf8 (CVal 8 (SOff 39 0)) ];
  YP09.mkRegion (Some 9%nat) 0x138 0x140 0x138 0x140 [];
  YP09.mkRegion (Some 9%nat) 0x140 0x148 0 0 [ YP09.mkChunk 0x140 (CVal 8 (SOff 33 0)) ];
  YP09.mkRegion (Some 9%nat) 0x148 0x150 0 0
    [ YP09.mkChunk 0x148 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 33 16384) (SLit 3)) (SOff 32 0))) ];
  YP09.mkRegion (Some 33%nat) 0x4000 0x4008 0x4000 0x4008 [ YP09.mkChunk 0x4000 (CVal 8 (SOff 34 0)) ];
  YP09.mkRegion (Some 35%nat) 0 8 0 8 [] ].
Definition ss_key (z3 b4 : bool) (s : Z) : sstate := mkSS PA_SELK pa_k_regs pa_k_mem None (pa_k_facts z3 b4 s).

(* ---- small arithmetic ---- *)
Lemma pa_k_land3 : forall a, Z.land a 3 = a mod 4.
Proof. intros a. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma pa_k_land16 : forall a, Z.land a 16 = if Z.testbit a 4 then 16 else 0.
Proof.
intros a. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
change 16 with (2 ^ 4). rewrite Z.pow2_bits_eqb by lia.
destruct (Z.testbit a 4) eqn:Hb.
- rewrite Z.pow2_bits_eqb by lia. destruct (Z.eqb_spec 4 i) as [<-|Hne]; [rewrite Hb; reflexivity | apply andb_false_r].
- rewrite Z.bits_0. destruct (Z.eqb_spec 4 i) as [<-|Hne]; [rewrite Hb; reflexivity | apply andb_false_r].
Qed.
Lemma pa_k_lnot : forall p, 0 <= p < 2 ^ 64 -> Z.lnot p mod 2 ^ 64 = 2 ^ 64 - 1 - p.
Proof. intros p Hp. rewrite Z.lnot_eq_pred_opp. symmetry. apply (Z.mod_unique _ (2 ^ 64) (-1)); lia. Qed.

Section h. Context {fx : YK11.FPState}.
Lemma pa_k_soff : forall E n c v, bv_unsigned (ew E n) = v -> sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros E n c v Hn. cbn [sv_denot]. rewrite Hn. reflexivity. Qed.
Lemma pa_k_and_lit : forall E n x k, bv_unsigned (ew E n) = x -> 0 <= x < 2 ^ 64 -> 0 <= k < 2 ^ 63 ->
sv_denot E (SAlu ALU_AND (SOff n 0) (SLit k)) = Z_to_bv 64 (Z.land x k).
Proof.
intros E n x k Hn Hx Hk. cbn [sv_denot]. rewrite Hn, Z.add_0_r, and_lit_Z. f_equal.
unfold YP0m.zsigned64, zcanon, M64. rewrite !Z.mod_small by lia.
destruct (Z.ltb_spec k (2 ^ 63)); [reflexivity | lia].
Qed.
(* the cell R+0x148: the engine's shadow form of the address of &pp->len *)
Lemma pa_k_shv : forall E pp, bv_unsigned (ew E 33) = pp -> bv_unsigned (ew E 32) = SHADOW_OFF ->
0 <= pp -> pp + 16384 < 2 ^ 47 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 33 16384) (SLit 3)) (SOff 32 0)) = Z_to_bv 64 (shadow_addr (pp + 0x4000)).
Proof.
intros E pp U33 U32 H0 H1. apply bv_eq.
change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 33 16384) (SLit 3)) (SOff 32 0))))
  with (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 33 16384) (SLit 3)) (SOff 32 0))).
rewrite U_SAlu, U_srl3. cbn [zalu_raw]. rewrite !U_SOff, U33, U32.
rewrite (zcanon_id (pp + 16384)) by (unfold M64; lia). rewrite (zcanon_id (SHADOW_OFF + 0)) by (unfold M64, SHADOW_OFF; lia).
assert (Hd : 0 <= (pp + 16384) / 8 <= pp + 16384) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
unfold shadow_addr. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
rewrite zcanon_id by (unfold M64, SHADOW_OFF; lia). lia.
Qed.
(* an override of a register by an expression of its value keeps regs_ok *)
Lemma pa_k_override : forall E sr regs (r : bv 5) e,
regs_ok E sr regs -> bv_eqb r 0 = false -> sv_denot E e = getr regs r -> regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e Hr Hr0 Hv rr. destruct (base.decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. symmetry. exact Hv.
- rewrite sr_get_set_other by exact Hne. apply Hr.
Qed.
(* every register outside clob still holds its entry value: its symbolic value is the entry state's *)
Lemma pa_k_regs_kept : forall E ss ms sr0 regs0 (H : word -> bool) (clob : list (bv 5)),
st_ok rsegs E ss (restrict H ms) -> regs_ok E sr0 regs0 ->
forallb (fun r : bv 5 => existsb (fun c => bv_eqb c r) clob || sv_eqb (sr_get (ss_regs ss) r) (sr_get sr0 r)) nz_regs = true ->
forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr (ms_regs ms) r = getr regs0 r.
Proof.
intros E ss ms sr0 regs0 H clob HS HR Hck r Hr0 Hn.
pose proof (proj1 (forallb_forall _ _) Hck r (in_nz_regs r Hr0)) as Hq. cbn beta in Hq.
apply orb_prop in Hq as [Hq|Hq].
- exfalso. apply existsb_exists in Hq as (c & Hc & Hb). apply bv_eqb_eq in Hb. subst c. exact (Hn Hc).
- apply sv_eqb_eq in Hq. rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hq. symmetry. apply HR.
Qed.
Lemma pa_k_atoms_app : forall E l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof. intros E l1 l2 H1 H2. induction l1 as [|[n f] l IH]; cbn in *; [exact H2 | tauto]. Qed.
Lemma pa_k_alias_app : forall E l1 l2, alias_ok E l1 -> alias_ok E l2 -> alias_ok E (l1 ++ l2).
Proof. intros E l1 l2 H1 H2. induction l1 as [|[a b] l IH]; cbn in *; [exact H2 | tauto]. Qed.

(* ---- reading the end state: an 8-byte chunk, and the byte chunks of a region ---- *)
Definition pa_k_find (n : nat) (rs : smem) (o : Z) : option sv :=
match List.find (fun r => match YP09.r_base r with Some m => Nat.eqb m n | None => false end &&
  existsb (fun c => (YP09.c_off c =? o) && match YP09.c_val c with CVal w _ => N.eqb w 8 | _ => false end) (YP09.r_chunks r)) rs with
| Some r =>
  match List.find (fun c => (YP09.c_off c =? o) && match YP09.c_val c with CVal w _ => N.eqb w 8 | _ => false end) (YP09.r_chunks r) with
  | Some c => match YP09.c_val c with CVal _ v => Some v | _ => None end
  | None => None
  end
| None => None
end.
Lemma pa_k_slot : forall E ss ms (H : word -> bool) n b o e v,
st_ok rsegs E ss (restrict H ms) -> pa_k_find n (ss_mem ss) o = Some e -> bv_unsigned (ew E n) = b ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> val_mem rsegs (mrestrict H (ms_mem ms)) (b + o) 8 v.
Proof.
intros E ss ms H n b o e v HS Hf Hn He Hv. unfold pa_k_find in Hf.
destruct (List.find _ (ss_mem ss)) as [r|] eqn:Hr; [|discriminate].
apply find_some in Hr as [Hr Hq]. apply andb_prop in Hq as [Hbase _].
destruct (YP09.r_base r) as [m|] eqn:Hrb; [|discriminate]. apply Nat.eqb_eq in Hbase. subst m.
destruct (List.find _ (YP09.r_chunks r)) as [c|] eqn:Hc; [|discriminate].
apply find_some in Hc as [Hc Hq]. apply andb_prop in Hq as [Ho Hw]. apply Z.eqb_eq in Ho.
destruct c as [co cv]. cbn [YP09.c_off YP09.c_val] in *. subst co.
destruct cv as [w e'| | | ]; try discriminate. apply N.eqb_eq in Hw. subst w. injection Hf as Hf. subst e'.
destruct (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & Hrs & _).
pose proof (proj1 (Forall_forall _ _) Hrs r Hr) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. rewrite Hrb in Hck. cbn [base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok rsegs E _ b o 8 e v Hck He ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
Definition pa_k_bytes_b (n : nat) (rs : smem) (l : list Z) : bool :=
forallb (fun j => (0 <=? nth j l 0) && (nth j l 0 <? 256) &&
  existsb (fun r => match YP09.r_base r with Some m => Nat.eqb m n | None => false end &&
    existsb (fun c => (YP09.c_off c =? Z.of_nat j) &&
      match YP09.c_val c with CVal w (SLit z) => N.eqb w 1 && (z mod 256 =? nth j l 0) | _ => false end)
    (YP09.r_chunks r)) rs) (seq 0 (length l)).
Lemma pa_k_bytes : forall E ss ms (H : word -> bool) n b l,
st_ok rsegs E ss (restrict H ms) -> pa_k_bytes_b n (ss_mem ss) l = true -> bv_unsigned (ew E n) = b ->
garr8 rsegs (mrestrict H (ms_mem ms)) b l.
Proof.
intros E ss ms H n b l HS Hb Hn j Hj.
assert (Hjs : In j (seq 0 (length l))) by (apply in_seq; lia).
pose proof (proj1 (forallb_forall _ _) Hb j Hjs) as Hq. cbn beta in Hq.
apply andb_prop in Hq as [Hq Hex]. apply andb_prop in Hq as [H0 H256]. apply Z.leb_le in H0. apply Z.ltb_lt in H256.
split; [|lia].
apply existsb_exists in Hex as (r & Hr & Hq). apply andb_prop in Hq as [Hbase Hc].
destruct (YP09.r_base r) as [m|] eqn:Hrb; [|discriminate]. apply Nat.eqb_eq in Hbase. subst m.
apply existsb_exists in Hc as (c & Hc & Hq). apply andb_prop in Hq as [Ho Hw].
apply Z.eqb_eq in Ho. destruct c as [co cv]. cbn [YP09.c_off YP09.c_val] in *. subst co.
destruct cv as [w [z| | | | | | | | | | ]| | | ]; try discriminate.
apply andb_prop in Hw as [Hw Hz]. apply N.eqb_eq in Hw. apply Z.eqb_eq in Hz. subst w.
destruct (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & Hrs & _).
pose proof (proj1 (Forall_forall _ _) Hrs r Hr) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. rewrite Hrb in Hck. cbn [base_val] in Hck. rewrite Hn in Hck.
destruct (Hck 0 ltac:(cbn; lia)) as (bt & Hcb & Hmb). cbn [cbyte YP09.c_val] in Hcb. injection Hcb as <-.
intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [YP09.c_off] in Hmb. change (Z.of_nat 0) with 0.
rewrite Z.add_0_r. rewrite Z.add_0_r in Hmb. change (ms_mem (restrict H ms)) with (mrestrict H (ms_mem ms)) in Hmb.
rewrite Hmb. f_equal.
rewrite rm_le_byte_1 by lia. apply bv_eq. unfold byte_of_word. cbn [sv_denot]. change (8 * 0) with 0.
rewrite Z.shiftr_0_r. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
change (bv_modulus 8) with 256. rewrite <- Hz. rewrite Z.mod_mod by lia.
rewrite (Z.div_mod z (2 ^ 64)) at 2 by lia. rewrite Z.add_comm.
replace (2 ^ 64 * (z / 2 ^ 64)) with ((2 ^ 56 * (z / 2 ^ 64)) * 256) by ring. rewrite Z.mod_add by lia. reflexivity.
Qed.
End h.

(* ---- the env's values ---- *)
Lemma pa_k_env : forall (regs : bvmap 5 word) R pp plen sel seen,
getr regs 9 = w64 R -> getr regs 11 = w64 sel -> getr regs 18 = w64 seen ->
0 <= R < 2 ^ 64 -> 0 <= pp -> pp + 19744 < 2 ^ 64 -> 0 <= plen <= 5424 -> 0 <= sel < 256 -> 0 <= seen <= 1 ->
let E := Ereg regs (pa_extra (pa_k_x pp plen sel)) in
bv_unsigned (ew E 9) = R /\ bv_unsigned (ew E 11) = sel /\ bv_unsigned (ew E 18) = seen /\
bv_unsigned (ew E 32) = SHADOW_OFF /\ bv_unsigned (ew E 33) = pp /\ bv_unsigned (ew E 34) = plen /\
bv_unsigned (ew E 35) = pp + plen /\ bv_unsigned (ew E 36) = sel mod 4 /\
bv_unsigned (ew E 37) = plen - 16381 + 2 ^ 64 /\ bv_unsigned (ew E 38) = plen - 16377 + 2 ^ 64 /\
bv_unsigned (ew E 39) = 2 ^ 64 - 1 - pp.
Proof.
intros regs R pp plen sel seen H9 H11 H18 HR Hpp0 Hpp1 Hp Hs Hn E.
assert (W : forall z, - 2 ^ 64 <= z < 0 -> bv_unsigned (Z_to_bv 64 z) = z + 2 ^ 64).
{ intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  symmetry. apply (Z.mod_unique z (2 ^ 64) (-1)); lia. }
subst E. repeat match goal with |- _ /\ _ => split end.
- rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9. unfold w64. apply unsigned_lit_small. lia.
- rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl), H11. unfold w64. apply unsigned_lit_small. lia.
- rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl), H18. unfold w64. apply unsigned_lit_small. lia.
- rewrite pa_extra_K. apply unsigned_lit_small. unfold SHADOW_OFF. lia.
- change (ew (Ereg regs (pa_extra (pa_k_x pp plen sel))) 33) with (Z_to_bv 64 pp). apply unsigned_lit_small. lia.
- change (ew (Ereg regs (pa_extra (pa_k_x pp plen sel))) 34) with (Z_to_bv 64 plen). apply unsigned_lit_small. lia.
- change (ew (Ereg regs (pa_extra (pa_k_x pp plen sel))) 35) with (Z_to_bv 64 (pp + plen)). apply unsigned_lit_small. lia.
- change (ew (Ereg regs (pa_extra (pa_k_x pp plen sel))) 36) with (Z_to_bv 64 (sel mod 4)).
  apply unsigned_lit_small. pose proof (Z.mod_pos_bound sel 4 ltac:(lia)). lia.
- change (ew (Ereg regs (pa_extra (pa_k_x pp plen sel))) 37) with (Z_to_bv 64 (plen - 16381)). rewrite W by lia. reflexivity.
- change (ew (Ereg regs (pa_extra (pa_k_x pp plen sel))) 38) with (Z_to_bv 64 (plen - 16377)). rewrite W by lia. reflexivity.
- change (ew (Ereg regs (pa_extra (pa_k_x pp plen sel))) 39) with (Z_to_bv 64 (Z.lnot pp)).
  rewrite Z.lnot_eq_pred_opp, W by lia. lia.
Qed.

(* ---- the walk's plumbing for this block ---- *)
(* the write right of a window: the slot R+0x138 lies in the caller's stack window; pp's block was made since the
   journal's start (lib/A/RPgBase.v rl_fresh_awr) *)
Ltac pa_k_awr_stk := idtac; let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; left; lia.
Ltac pa_k_awr_pp := idtac; let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
lazymatch goal with Hin : In (?p, Layout.PP_SIZE) _, Hout : ~ In (?p, Layout.PP_SIZE) _ |- _ =>
replace a with (p + (a - p)) by lia;
apply (rl_fresh_awr _ _ _ _ _ _ _ p Layout.PP_SIZE); [exact Hin | exact Hout | change (req_size Layout.PP_SIZE) with 19744; lia]
end.
Ltac pa_k_awr :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | eassumption | pa_k_awr_stk | ]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat); [reflexivity | eassumption | pa_k_awr_pp | ]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 35%nat); [reflexivity | eassumption | pa_k_awr_pp | ] ].
(* every write window lies in the block's write set *)
Ltac pa_k_kwr :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr];
  [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
   lazymatch goal with U9 : bv_unsigned (ew _ 9) = _, U33 : bv_unsigned (ew _ 33) = _, U35 : bv_unsigned (ew _ 35) = _ |- _ =>
   rewrite ?U9, ?U33, ?U35 in Hb end; lia | ]);
destruct Hr.
Ltac pa_k_run stop :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok pa_tbl_ok HS HJ SHOK PAspan stop; [pa_k_awr | ] end.
(* the leaf: the post's first eight clauses (lib/AU/RPgPropKit.v pa_leaf), with the registers kept against the
   entry state's registers (s11 holds K as the expression SOff 32 0, s6 holds pp + 0x4000 as SOff 33 0x4000) *)
Ltac pa_k_leaf :=
lazymatch goal with
| HS : st_ok _ ?E _ (restrict (w_H ?W) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyc ?Sc _ _ _ _,
  HRO : regs_ok ?E pa_k_regs ?regs, KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
apply SRr_ret;
red; exists lyc, Sc, (ms_regs ms), (ms_mem ms); eexists;
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|];
split; [exact HJ|];
split; [apply (pa_k_regs_kept _ _ ms pa_k_regs regs (w_H W) _ HS HRO); vm_compute; reflexivity|];
split; [reflexivity|];
split; [apply Permutation_refl|];
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|];
split; [apply mo_le_refl; assumption|];
split; [intros a Ha Hz; exact (KE a Ha Hz)|]
end.
(* the value of a register / an 8-byte cell / the bytes of a region at the end of the run *)
Ltac pa_k_val := first [ reflexivity | (try unfold w64; erewrite pa_k_soff by eassumption; f_equal; lia) ].
Ltac pa_k_slot_tac n b o Ub :=
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms) |- _ =>
let r := eval vm_compute in (pa_k_find n (ss_mem ss) o) in
lazymatch r with Some ?e =>
apply (pa_k_slot E ss ms H n b o e); [exact HS | vm_compute; reflexivity | exact Ub | pa_k_val | lia]
end end.
Ltac pa_k_bytes_tac n b Ub :=
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms) |- _ =>
apply (pa_k_bytes E ss ms H n b); [exact HS | vm_compute; reflexivity | exact Ub]
end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* the entry state holds at 0x8086c *)
Lemma pa_k_entry : forall (W : world rsegs) (regs : bvmap 5 word) memc R pp plen sel seen (z3 b4 : bool),
getr regs 9 = w64 R -> getr regs 27 = w64 SHADOW_OFF -> getr regs 11 = w64 sel -> getr regs 18 = w64 seen ->
getr regs 22 = w64 (pp + 0x4000) ->
70368744177664 <= R -> R + 0x150 <= 140737488355328 -> R mod 16 = 0 ->
pp mod 16 = 0 -> 4096 <= pp -> pp <= 140737479946976 -> pp + 19744 <= R ->
(forall o, 0x138 <= o < 0x140 -> apresent (w_H W) memc (R + o)) ->
(forall o, 0 <= o < 19744 -> apresent (w_H W) memc (pp + o)) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x70) 8 0x10003 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xa8) 8 (2 ^ 64 - 0x4001) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xb0) 8 0x80001 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xc0) 8 (2 ^ 64 - 0x3ffd) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf8) 8 (2 ^ 64 - 1 - pp) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x140) 8 pp ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x148) 8 (shadow_addr (pp + 0x4000)) ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 plen ->
0 <= plen <= 5424 -> 0 <= sel < 256 -> 0 <= seen <= 1 ->
(sel mod 4 =? 0) = z3 -> Z.testbit sel 4 = b4 ->
regs_ok (Ereg regs (pa_extra (pa_k_x pp plen sel))) pa_k_regs regs /\
st_ok rsegs (Ereg regs (pa_extra (pa_k_x pp plen sel))) (ss_key z3 b4 seen)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 PA_SELK) memc (seg_rom rsegs))).
Proof.
intros W regs memc R pp plen sel seen z3 b4 H9 H27 H11 H18 H22 HR0 HR1 HR16 Hpp16 Hpp0 Hpp1 HppR HpR Hppp
  V70 Va8 Vb0 Vc0 Vf8 V140 V148 Vlen Hp Hs Hn Hz3 Hb4.
destruct (pa_k_env regs R pp plen sel seen H9 H11 H18 ltac:(lia) ltac:(lia) ltac:(lia) Hp Hs Hn)
  as (U9 & U11 & U18 & U32 & U33 & U34 & U35 & U36 & U37 & U38 & U39).
set (E := Ereg regs (pa_extra (pa_k_x pp plen sel))) in *.
assert (Hsa : 0 <= shadow_addr (pp + 0x4000) < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF.
  assert (0 <= (pp + 0x4000) / 8 <= pp + 0x4000) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia). lia. }
assert (HRO : regs_ok E pa_k_regs regs).
{ unfold pa_k_regs. apply pa_k_override; [apply pa_k_override; [apply regs_ok_Ereg | reflexivity |] | reflexivity |].
  - rewrite H27, (pa_k_soff E 32 0 SHADOW_OFF U32), Z.add_0_r. reflexivity.
  - rewrite H22, (pa_k_soff E 33 16384 pp U33). reflexivity. }
split; [exact HRO|].
unfold ss_key. rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
- exact HRO.
- vm_compute. reflexivity.
- unfold pa_k_mem. repeat apply Forall_cons; try apply Forall_nil.
  + apply (rm_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
    apply Forall_cons; [|apply Forall_nil].
    eapply pa_chunk8; [reflexivity | lia | exact V70].
  + apply (rm_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
    apply Forall_cons; [|apply Forall_nil].
    eapply pa_chunk8; [ | | exact Va8]; [apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity | lia].
  + apply (rm_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
    apply Forall_cons; [|apply Forall_nil].
    eapply pa_chunk8; [reflexivity | lia | exact Vb0].
  + apply (rm_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
    apply Forall_cons; [|apply Forall_nil].
    eapply pa_chunk8; [ | | exact Vc0]; [apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity | lia].
  + apply (rm_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
    apply Forall_cons; [|apply Forall_nil].
    eapply pa_chunk8; [ | | exact Vf8]; [rewrite (pa_k_soff E 39 0 _ U39), Z.add_0_r; reflexivity | lia].
  + apply (rm_rw_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia | intros o Ho; apply HpR; lia | apply Forall_nil].
  + apply (rm_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
    apply Forall_cons; [|apply Forall_nil].
    eapply pa_chunk8; [ | | exact V140]; [rewrite (pa_k_soff E 33 0 pp U33), Z.add_0_r; reflexivity | lia].
  + apply (rm_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
    apply Forall_cons; [|apply Forall_nil].
    eapply pa_chunk8; [ | | exact V148]; [apply (pa_k_shv E pp U33 U32); lia | exact Hsa].
  + apply (rm_rw_region rsegs E (w_H W) memc 33 pp); [exact U33 | lia | lia | intros o Ho; apply Hppp; lia |].
    apply Forall_cons; [|apply Forall_nil].
    eapply pa_chunk8; [rewrite (pa_k_soff E 34 0 plen U34), Z.add_0_r; reflexivity | lia | exact Vlen].
  + apply (rm_rw_region rsegs E (w_H W) memc 35 (pp + plen)); [exact U35 | lia | lia | | apply Forall_nil].
    intros o Ho. replace (pp + plen + o) with (pp + (plen + o)) by lia. apply Hppp. lia.
- unfold pa_k_mem. change (Ereg regs (pa_extra (pa_k_x pp plen sel))) with E. clearbody E.
  cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, base_val. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite U9, U33, U35.
  repeat match goal with |- _ /\ _ => split | |- True => exact I end; lia.
- unfold pa_k_facts, facts_ok. change (Ereg regs (pa_extra (pa_k_x pp plen sel))) with E. clearbody E.
  cbn [f_atoms f_conds f_alias]. split; [|split; [exact I|]].
  + apply pa_k_atoms_app.
    * unfold pa_k_atoms. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U9, U33, U32, U34, U11, U18, U35, U37, U38, U39.
      repeat match goal with |- _ /\ _ => split | |- True => exact I end;
      first [ (change (2 ^ 0) with 1; apply Z.mod_1_r) | (change (2 ^ 4) with 16; lia) | (unfold SHADOW_OFF; lia) | lia ].
    * destruct z3; cbn [pa_k_ex atoms_ok]; [exact I|]. split; [|exact I].
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U36. apply Z.eqb_neq in Hz3.
      pose proof (Z.mod_pos_bound sel 4 ltac:(lia)).
      split; [lia|]. split; [change (2 ^ 0) with 1; apply Z.mod_1_r | lia].
  + apply pa_k_alias_app.
    * unfold pa_k_al0. cbn [alias_ok]. split; [|split; [|split; [|split; [|exact I]]]].
      -- apply bv_eq.
         change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff 33 0) (SOff 34 0)))) with (U E (SAlu ALU_ADD (SOff 33 0) (SOff 34 0))).
         rewrite U_add_off_atom by (rewrite ?U33, ?U34; unfold M64; lia). rewrite U33, U34.
         rewrite (pa_k_soff E 35 0 (pp + plen) U35). rewrite unsigned_lit_small by lia. lia.
      -- apply bv_eq.
         change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff 33 0) (SOff 34 4)))) with (U E (SAlu ALU_ADD (SOff 33 0) (SOff 34 4))).
         rewrite U_add_off_atom by (rewrite ?U33, ?U34; unfold M64; lia). rewrite U33, U34.
         rewrite (pa_k_soff E 35 4 (pp + plen) U35). rewrite unsigned_lit_small by lia. lia.
      -- rewrite (pa_k_soff E 34 (-16381) plen U34), (pa_k_soff E 37 0 _ U37). apply bv_eq. rewrite !Z_to_bv_unsigned.
         unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_0_r.
         replace (plen - 16381 + 2 ^ 64) with ((plen + -16381) + 1 * 2 ^ 64) by ring. rewrite Z.mod_add by lia. reflexivity.
      -- rewrite (pa_k_soff E 34 (-16377) plen U34), (pa_k_soff E 38 0 _ U38). apply bv_eq. rewrite !Z_to_bv_unsigned.
         unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_0_r.
         replace (plen - 16377 + 2 ^ 64) with ((plen + -16377) + 1 * 2 ^ 64) by ring. rewrite Z.mod_add by lia. reflexivity.
    * destruct z3, b4; cbn [pa_k_al alias_ok]; (split; [|split; [|exact I]]);
      (rewrite (pa_k_and_lit E 11 sel _ U11) by lia);
      first [ (rewrite pa_k_land16, Hb4; reflexivity)
            | (rewrite pa_k_land3; first [ (apply Z.eqb_eq in Hz3; rewrite Hz3; reflexivity)
                                         | (rewrite (pa_k_soff E 36 0 _ U36), Z.add_0_r; reflexivity) ]) ].
Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Local Abbreviation pa_post := (rl_wpost B MT).

(* the shadow entries: the bytes of pp's block and the 16 bytes from pp + len are addressable, outside the band *)
Lemma pa_k_shok : forall ly S W mem md E pp plen,
AR rsegs B ly S W mem md -> In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
bv_unsigned (ew E 32) = SHADOW_OFF -> bv_unsigned (ew E 33) = pp -> bv_unsigned (ew E 35) = pp + plen ->
0 <= plen -> plen + 16 <= 19744 -> 4096 <= pp -> pp + 19744 <= 140737479966720 -> in_app pp 19744 ->
sh_ok rsegs PABx pa_k_SH E (mrestrict (w_H W) mem).
Proof using LAWS.
intros ly S W mem md E pp plen HAR Hin U32 U33 U35 Hp0 Hp1 Hpp0 Hpp1 Happ.
assert (UB : U E PABx = SHADOW_OFF) by (unfold PABx; rewrite U_SOff, U32, Z.add_0_r; apply zcanon_id; unfold SHADOW_OFF, M64; lia).
assert (HAP : forall a, pp <= a < pp + 19744 -> ~ (U E PABx <= a < U E PABx + 17592186044416)).
{ intros a Ha. rewrite UB. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
assert (V33 : U E (SOff 33 0) = pp) by (rewrite U_SOff, U33, Z.add_0_r; apply zcanon_id; unfold M64; lia).
assert (V35 : U E (SOff 35 0) = pp + plen) by (rewrite U_SOff, U35, Z.add_0_r; apply zcanon_id; unfold M64; lia).
constructor; [|constructor; [|constructor]]; split; cbn [she_m she_lo she_hi].
- rewrite V33. eapply (obl_of_block rsegs B LAWS); [exact HAR | exact Hin | exact UB | lia | change (req_size Layout.PP_SIZE) with 19744; lia].
- unfold app_apart. cbn [she_m she_lo she_hi]. intros a Ha. rewrite V33 in Ha. apply HAP. lia.
- rewrite V35. eapply (obl_of_block rsegs B LAWS); [exact HAR | exact Hin | exact UB | lia | change (req_size Layout.PP_SIZE) with 19744; lia].
- unfold app_apart. cbn [she_m she_lo she_hi]. intros a Ha. rewrite V35 in Ha. apply HAP. lia.
Qed.

(* ---- the key block 0x8086c -> 0x809d4 (params Struct) / 0x81b98 (Int 7) ---- *)
Lemma pa_key : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (R pp plen sel seen : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> getr regs 27 = w64 SHADOW_OFF -> getr regs 11 = w64 sel -> getr regs 18 = w64 seen ->
getr regs 22 = w64 (pp + 0x4000) ->
sp0 - STK + T_SEG_STK <= R -> R + 0x200 <= sp0 -> R mod 16 = 0 ->
In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x70) 8 0x10003 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xa8) 8 (2 ^ 64 - 0x4001) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xb0) 8 0x80001 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xc0) 8 (2 ^ 64 - 0x3ffd) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf8) 8 (2 ^ 64 - 1 - pp) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x140) 8 pp ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x148) 8 (shadow_addr (pp + 0x4000)) ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 plen ->
0 <= plen -> plen + 16 <= 5440 -> 0 <= sel < 256 -> (seen = 0 \/ seen = 1) ->
SRr rsegs W (cfg_at rsegs PA_SELK regs memc mdc)
(pa_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc
 (if (sel mod 4 =? 0) || Z.testbit sel 4 then PA_SELI else PA_SELS)
 [5; 7; 10; 11; 12; 13; 14; 15; 16; 24]%bv
 (fun a => pp + plen <= a < pp + plen + 8 \/ pp + 0x4000 <= a < pp + 0x4008 \/ R + 0x138 <= a < R + 0x140)
 (fun W2 regs2 mem2 =>
   getr regs2 14 = w64 (if sel mod 4 =? 0 then seen else 1) /\
   getr regs2 24 = w64 pp /\ getr regs2 5 = w64 (-0x3ffd) /\ getr regs2 7 = w64 (-0x4001) /\
   garr8 rsegs (mrestrict (w_H W2) mem2) (pp + plen)
     (map (fun x : byte => bv_unsigned x) (Cursor.le32 (if sel mod 4 =? 0 then 0x10003 else 0x80001) ++ Cursor.le32 0)) /\
   val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 (plen + 8) /\
   val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x138) 8 (if (sel mod 4 =? 0) || (seen =? 1) then 0 else 1))).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp plen sel seen HJ H9 H27 H11 H18 H22
  HRlo HRhi HR16 Hin Hout V70 Va8 Vb0 Vc0 Vf8 V140 V148 Vlen Hp0 Hp16 Hsel Hseen.
pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (Hpp16 & Hpp4k & Hppc & Happ & Hppres & _).
change (req_size Layout.PP_SIZE) with 19744 in Hppc, Happ, Hppres.
unfold T_SEG_STK, ASTACK in HRlo.
assert (HpR : forall o, 0x138 <= o < 0x140 -> apresent (w_H W) memc (R + o)) by (intros o Ho; apply Hpres; lia).
assert (Hppp : forall o, 0 <= o < 19744 -> apresent (w_H W) memc (pp + o)) by (intros o Ho; apply (Hppres (pp + o)); lia).
assert (Hpp' : pp <= 140737479946976) by lia.
assert (Hppc' : pp + 19744 <= 140737479966720) by lia.
destruct (sel mod 4 =? 0) eqn:Hz3; destruct (Z.testbit sel 4) eqn:Hb4; destruct Hseen as [Hs | Hs]; subst seen;
cbv beta iota delta [orb Z.eqb Pos.eqb].
all: pose proof (pa_k_entry W regs memc R pp plen sel _ _ _ H9 H27 H11 H18 H22 ltac:(lia) ltac:(lia) HR16
  Hpp16 Hpp4k Hpp' ltac:(lia) HpR Hppp V70 Va8 Vb0 Vc0 Vf8 V140 V148 Vlen ltac:(lia) ltac:(lia) ltac:(lia)
  Hz3 Hb4) as [HRO HS].
all: destruct (pa_k_env regs R pp plen sel _ H9 H11 H18 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
  as (U9 & U11 & U18 & U32 & U33 & U34 & U35 & U36 & U37 & U38 & U39).
all: pose proof (pa_k_shok lyc Sc W memc mdc (Ereg regs (pa_extra (pa_k_x pp plen sel))) pp plen HAR Hin U32 U33 U35
  ltac:(lia) ltac:(lia) Hpp4k Hppc' Happ) as SHOK.
all: remember (Ereg regs (pa_extra (pa_k_x pp plen sel))) as E eqn:HE.
all: clear HE.
all: assert (KE : forall a, 0 <= a < 2 ^ 64 ->
  ~ (pp + plen <= a < pp + plen + 8 \/ pp + 0x4000 <= a < pp + 0x4008 \/ R + 0x138 <= a < R + 0x140) ->
  aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by (intros; reflexivity).
all: unfold cfg_at; change (w64 PA_SELK) with (Z_to_bv 64 PA_SELK).
all: lazymatch goal with |- context [rl_wpost _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?pc _ _ _] => pa_k_run pc end.
all: pa_keep pa_k_kwr.
all: pa_k_leaf.
all: cbv beta.
all: split; [pa_reg (14%bv : bv 5); pa_k_val|].
all: split; [pa_reg (24%bv : bv 5); pa_k_val|].
all: split; [pa_reg (5%bv : bv 5); pa_k_val|].
all: split; [pa_reg (7%bv : bv 5); pa_k_val|].
all: split; [pa_k_bytes_tac 35%nat (pp + plen) U35|].
all: split; [pa_k_slot_tac 33%nat pp 16384 U33|].
all: pa_k_slot_tac 9%nat R 312 U9.
Qed.
End d.
End b.

(* ================================ the key piece: SELK -> SELS / SELI ================================ *)
Section pk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Lemma pa_piece_key : rs_piece_W4_key_stmt rsegs B MT.
Proof using MTL LAWS.
unfold rs_piece_W4_key_stmt. intros cx POST rest i Hst HSS HSI.
destruct Hst as (Hpre & Hfsh0 & Hc1 & Hlen0 & Hin0).
pose proof (pa_R_bounds B cx Hpre) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & RB7).
pose proof (pa_blk_bounds B LAWS cx Hpre) as (PB1 & PB2 & FB1 & FB2 & FB3 & FB4).
pose proof (pa_pp_blocks B LAWS cx Hpre) as (Ppin & Ppout & PA).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold rs_from_SELK. intros ly2 S2 W2 regs2 mem2 md2 sh np sel ps r Hlen Hcut.
destruct Hcut as (Hb & Hat & Hpp & Hsh7 & Hsel & Hselr).
pose proof Hb as (Hcore & Hfsh & Hin & Hsuf & Hwf & Hqlen & Hpsl & Hsh & Hnp & Hlen1 & Hnp3).
pose proof Hcore as (HJ & _ & _ & HPerm & _).
assert (Ppin2 : In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Ppin]).
destruct (pa_img_bounds sh ps Hwf ltac:(lia)) as (IB1 & IB2 & IB3 & IB4).
assert (Hpp20 : e_pp (x_e cx) + 19744 <= 0x7fffff800000) by (unfold Layout.PP_SIZE in PB2; lia).
unfold rs_at_cx in Hat.
pa_take Hat (LReg 9) (e_R (x_e cx)) A9. pa_take Hat (LReg 27) SHADOW_OFF A27.
pa_take Hat (LReg 11) sel A11. pa_take Hat (LReg 18) (rs_seen ps) A18.
pa_take Hat (LReg 22) (e_pp (x_e cx) + 0x4000) A22.
pa_take Hat (LCell XR 0x70) 0x10003 A70. pa_take Hat (LCell XR 0xa8) (-0x4001) Aa8.
pa_take Hat (LCell XR 0xb0) 0x80001 Ab0. pa_take Hat (LCell XR 0xf8) (Z.lnot (e_pp (x_e cx))) Af8.
pa_take Hat (LCell XR 0xc0) (-0x3ffd) Ac0. pa_take Hat (LCell XR 0x140) (e_pp (x_e cx)) A140.
pa_take Hat (LCell XR 0x148) (shadow_addr (e_pp (x_e cx) + 0x4000)) A148.
assert (M2 : (-0x3ffd) mod 2 ^ 64 = 2 ^ 64 - 0x3ffd) by reflexivity.
assert (M3 : (-0x4001) mod 2 ^ 64 = 2 ^ 64 - 0x4001) by reflexivity.
rewrite M2 in Ac0. rewrite M3 in Aa8. rewrite Z.mod_small in A70, Ab0 by lia.
rewrite (pa_k_lnot (e_pp (x_e cx))) in Af8 by lia.
rewrite Z.mod_small in A140 by lia.
assert (Hsa : 0 <= shadow_addr (e_pp (x_e cx) + 0x4000) < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF.
  assert (0 <= (e_pp (x_e cx) + 0x4000) / 8 <= e_pp (x_e cx) + 0x4000)
    by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia). lia. }
rewrite Z.mod_small in A148 by exact Hsa.
assert (Hseen : rs_seen ps = 0 \/ rs_seen ps = 1) by (unfold rs_seen; destruct (existsb _ _); cbn; lia).
assert (Hplen : rs_plen sh ps = Z.of_nat (length (pc_buf (PbCut sh ps None)))) by reflexivity.
assert (Alen : val_mem rsegs (mrestrict (w_H W2) mem2) (e_pp (x_e cx) + 0x4000) 8 (rs_plen sh ps)).
{ rewrite Hplen. unfold rs_pp_at, pc_image in Hpp.
  assert (Hb16 : Z.of_nat (length (pc_buf (PbCut sh ps None))) <= Layout.POD_BUF_MAX) by (unfold Layout.POD_BUF_MAX; lia).
  exact (rm_pp_len rsegs _ _ _ _ _ _ Hb16 IB3 IB4 _ _ _ Hpp). }
eapply SRr_bind.
{ refine (pa_key B MT MTL LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (e_R (x_e cx)) (e_pp (x_e cx)) (rs_plen sh ps)
    sel (rs_seen ps) HJ A9 A27 A11 A18 A22 RB1 RB2 RB3 Ppin2 Ppout A70 Aa8 Ab0 Ac0 Af8 A140 A148 Alen _ _ Hsel Hseen);
  lia. }
intros W3 c3 Hle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkeep & Hfr & Hperm & Hio & Hmo & Hmem & HR).
destruct HR as (R14 & R24 & R5 & R7 & Rpp & Rlen & R138).
set (R := e_R (x_e cx)) in *. set (pp := e_pp (x_e cx)) in *. set (F := e_F (x_e cx)) in *.
set (plen := rs_plen sh ps) in *.
assert (Hcore3 : rs_core rsegs B MT cx (rs_E1 rsegs cx) ly3 S3 W3 regs3 mem3 md3).
{ refine (pa_core_step B MT MTL cx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore HJ3 _ Hfr Hperm Hio Hmo Hmem _).
  - pa_regs234 Hkeep.
  - intros a Ha. right. destruct Ha as [Ha|[Ha|Ha]];
    [apply pa_E1_pp | apply pa_E1_pp | apply pa_E1_R48]; fold pp R; unfold Layout.PP_SIZE; lia. }
assert (Hfsh3 : rs_fsh_at rsegs cx W3 mem3 rs_P0).
{ unfold rs_fsh_at in *. eapply rm_fsh_kept; [exact Hfsh|]. intros j Hj.
  replace (Z.of_nat (length rs_P0)) with 88 in Hj by reflexivity. fold F.
  assert (F8 : 0 <= F / 8 <= 0xfffffff0000) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in PA. unfold shadow_addr, SHADOW_OFF.
  apply Hmem; [lia|]. unfold Layout.PP_SIZE in *. lia. }
(* the cut's locations the block does not write keep their values *)
assert (Hat3 : rs_at rsegs (w_H W3) mem3 regs3 (x_e cx)
  (rs_Rc0 rsegs cx ++ [(LReg 6, Z.of_nat (length ps)); (LReg 26, -8); (LReg 22, e_pp (x_e cx) + 0x4000)] ++
   rs_Kc rsegs cx sh np ++ rs_cur2s rsegs cx rest r)).
{ assert (Hat' : rs_at rsegs (w_H W2) mem2 regs2 (x_e cx)
    (rs_Rc0 rsegs cx ++ [(LReg 6, Z.of_nat (length ps)); (LReg 26, -8); (LReg 22, e_pp (x_e cx) + 0x4000)] ++
     rs_Kc rsegs cx sh np ++ rs_cur2s rsegs cx rest r)) by (pa_list; pa_from Hat).
  eapply pa_at_move; [exact Hat'|].
  pa_kept Hkeep ltac:(fold R pp; apply Hmem; unfold T_SEG_STK, ASTACK, Layout.PP_SIZE in *; lia). }
assert (Hpp3 : forall kk, rm_bytes rsegs (w_H W3) mem3 (pp + plen) (le32 kk ++ le32 0) ->
  rs_pp_at rsegs cx W3 mem3 (rs_img_key sh ps kk)).
{ intros kk Nx. unfold rs_pp_at, rs_img_key. fold pp.
  unfold rs_pp_at, pc_image in Hpp. fold pp in Hpp.
  eapply (pa_pp_append (w_H W2) mem2 (w_H W3) mem3 pp); [| exact IB3 | exact IB4 | exact Hpp | | |].
  - rewrite length_app, !length_le32. rewrite Nat2Z.inj_add. unfold Layout.POD_BUF_MAX. lia.
  - exact Nx.
  - rewrite length_app, !length_le32, Nat2Z.inj_add. cbn [Z.of_nat Pos.of_succ_nat]. unfold Layout.OFF_LEN.
    rewrite <- Hplen. fold plen. replace (plen + Z.of_nat 8) with (plen + 8) by reflexivity. exact Rlen.
  - intros y Hy Hx Hl. rewrite length_app, !length_le32 in Hx. rewrite <- Hplen in Hx. fold plen in Hx.
    apply Hmem; [unfold Layout.PP_SIZE in *; lia|]. unfold T_SEG_STK, ASTACK, Layout.OFF_LEN, Layout.PP_SIZE in *.
    cbn [Nat.add Z.of_nat Pos.of_succ_nat] in Hx. lia. }
assert (Hseen01 : rs_first ps = 1 - rs_seen ps) by (unfold rs_first, rs_seen; destruct (existsb _ _); reflexivity).
assert (Hf138 : (if sel mod 4 =? 0 then 0 else rs_first ps) mod 2 ^ 64 =
  (if (sel mod 4 =? 0) || (rs_seen ps =? 1) then 0 else 1)).
{ rewrite Hseen01. destruct (sel mod 4 =? 0); destruct Hseen as [E1|E1]; rewrite E1; reflexivity. }
(* the locations of rs_L_KEY: the kept ones, seen' in a4, pp in s8 and first in R+0x138 *)
assert (HatK : rs_at rsegs (w_H W3) mem3 regs3 (x_e cx) (rs_L_KEY rsegs cx sh np sel ps rest r)).
{ pa_list; first [pa_from Hat3 | idtac].
  all: lazymatch goal with
       | |- rl_at _ _ _ _ _ (LReg 14) _ => cbn [rl_at]; exact R14
       | |- rl_at _ _ _ _ _ (LReg 24) _ => cbn [rl_at]; exact R24
       | |- rl_at _ _ _ _ _ (LCell XR 312) _ => cbn [rl_at rl_xv]; fold R; rewrite Hf138; exact R138
       end. }
destruct ((sel mod 4 =? 0) || Z.testbit sel 4) eqn:Ec.
- change (mkCfg (mkst regs3 (w64 PA_SELI) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs RS_SELI regs3 mem3 md3).
  apply (HSI ly3 S3 W3 regs3 mem3 md3 sh np sel ps r Hlen).
  split; [split; [exact Hcore3|]; split; [exact Hfsh3|]; repeat (split; [eassumption|]); repeat split; assumption|].
  split; [exact HatK|].
  split; [apply Hpp3; unfold rs_key_of; exact Rpp|].
  split; [exact Hsh7|]. split; [exact Hsel|]. split; [|exact Hselr].
  apply orb_true_iff in Ec as [E|E]; [left; apply Z.eqb_eq; exact E | right; exact E].
- change (mkCfg (mkst regs3 (w64 PA_SELS) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs RS_SELS regs3 mem3 md3).
  apply orb_false_iff in Ec as [E0 E4]. apply Z.eqb_neq in E0.
  apply (HSS ly3 S3 W3 regs3 mem3 md3 sh np sel ps r Hlen).
  split; [split; [exact Hcore3|]; split; [exact Hfsh3|]; repeat (split; [eassumption|]); repeat split; assumption|].
  split.
  + unfold rs_at_cx. apply (pa_at_app _ _ _ _ _ _ HatK).
    pa_list; first [pa_from Hat3 | idtac].
    all: lazymatch goal with
         | |- rl_at _ _ _ _ _ (LReg 5) _ => cbn [rl_at]; exact R5
         | |- rl_at _ _ _ _ _ (LReg 7) _ => cbn [rl_at]; exact R7
         end.
  + replace (sel mod 4 =? 0) with false in Rpp by (symmetry; apply Z.eqb_neq; exact E0).
    split; [apply Hpp3; exact Rpp|].
    split; [exact Hsh7|]. split; [exact Hsel|]. split; [exact E0|]. split; [exact E4 | exact Hselr].
Qed.
End pk.

Print Assumptions pa_piece_key.
