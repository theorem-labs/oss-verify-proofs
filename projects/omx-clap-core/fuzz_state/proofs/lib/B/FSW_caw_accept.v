(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACem.v, with its module paths and module names changed; 1540 of its 1601 lines of code are new or changed and 390 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_pj_string.v, with its module names changed; 1107 of its 1191 lines of code are new or changed and 1517 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_caw_emit.v, with its addresses and numbers changed; 788 of its 885 lines of code are new or changed and 1094 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/FSW_caw_accept.v (a working branch),
   the same names over B's own code (B listing: capstone over the unstripped twin of fs.asan-ubsan, sha256 b1566a1c...).
   rule 24: proves no function (kind: segment lemma; check_as_written, B 0x8164c, CONFIRM by a Theorem Labs lane). *)
(* The ACCEPT and the remaining REFUSAL arms of the tail of the inlined expected_body of check_as_written over
   fs.asan-ubsan (B A_check_as_written 0x8164c), machine code 0x81804 .. 0x818ac / 0x81a78, C source fuzz_state.c:91-93:

     r = m % 4;
     if ( *text || pad > 2 || r == 1 || (r == 2 && (six[m-1] & 15)) || (r == 3 && (six[m-1] & 3))) n = SIZE_MAX;

   B's code reaches 0x81804 only at the NUL (the refused-character exit of the scan goes straight to 0x81a78 with
   s5 = SIZE_MAX, FSW_caw_scan.v), so `*text` is not tested here.
   THE COMMON EXIT STATE at 0x81a78 (`jal __wrap_free` of six), caa_xss: the registers the free call and the back half
   read (a0 = six, s2 = want, s5 = the answer n through atom 49, s0 = l, s1 = body, sp and the shadow base s4), ra the
   atom 31, a3 = ~six (atom 30) and a4 = m (atom 38) kept, the frame region caw_stk, the kept atom facts; every other
   register (a1 a2 s3 s6 t0 t1 t2 a5 a6 a7 t3 t4 t5 t6) re-keyed to the fresh atoms 44 .. 61 with YL09.st_ok_reabs,
   so every exit of the scan, the tail, the empty-text arm and the emit loop hands over this one state.
   This file walks, from the tail state cawt_ss 0 3145728 at 0x81804 (FSW_caw_tail.v) with pad <= 2, in
   continuation-passing form:
   - caa_refuse_tail: WriterSpec.six_tail_ok sx = false, that is r = 1, or r = 2 with six[m-1] land 15 <> 0, or
     r = 3 with six[m-1] land 3 <> 0; the walk reaches 0x81a78 with s5 = SIZE_MAX.
   - caa_accept_m0: m = 0; the walk reaches 0x81a78 with s5 = 0.
   - caa_accept_emit: six_tail_ok sx = true and m > 0; the walk reaches the emit loop head 0x818ac in exactly the
     state FSW_caw_emit.v's caw_emit_loop asks for, at i = 0, n = 0, done = [].
   Together with FSW_caw_tail.v's pad refusal this is WriterSpec.b64_dec's `(pad <=? 2) && six_tail_ok six`.
   METHOD (measured with the engine over the pinned fs.asan-ubsan): the shadow `lb` of six[m-1] at 0x81850 / 0x8187c
   is a token atom, resolved by the engine's slow-block pattern and covered by the SH entry mkSHE 40 (-1) 0
   (six[m-1], based at the alias atom 40 = six + m), so no __asan_report_* call is reached; the UBSan trap of
   `bltu a3, m - 1` (0x81840 / 0x8186c) is decided by the engine once m >= 1 is an atom fact (caa_add_six); the
   branches the engine cannot decide (0x81828 `beq r, 1`, 0x81830 `beq r, 3`, 0x81838 `bne r, 2`, 0x81860 / 0x8188c
   on six[m-1] land 15 / land 3, 0x81894 `beqz m`) are conditions the arm's own hypothesis decides (YP06
   st_ok_add_cond); at 0x818ac the atoms are re-keyed with YL09.st_ok_reabs through FSW_caw_emit.v's cae_head_st
   (a5 = ~want, `not a5, s2` at 0x81898, onto the loop's atom 66). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP05 YL01 YL02 YL07 YL09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w FSH_Base FSH_Rt FSW_K
FSW_caw_defs FSW_caw_model FSW_caw_tail FSW_caw_emit.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Module WSA := WriterSpec.

(* ---- the common exit state at 0x81a78 (`jal __wrap_free` of six) ---- *)
Definition caa_P (n : nat) : bool := Nat.ltb n 44.
Definition caa_xregs : list sv :=
  [SLit 0; SOff 31 0; SOff 2 (-64); SOff 3 0; SOff 4 0;
   SOff 50 0; SOff 51 0; SOff 52 0;
   SOff 12 0; SOff 11 0;
   SOff 33 0; SOff 44 0; SOff 45 0; SOff 30 0; SOff 38 0;
   SOff 55 0; SOff 56 0; SOff 57 0;
   SOff 34 0; SOff 46 0; SOff 32 0;
   SOff 49 0; SOff 47 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
   SOff 58 0; SOff 59 0; SOff 60 0; SOff 61 0].
Definition caa_xatoms : list (nat * afact) :=
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4);
   (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (33%nat, mkAF 4096 CAW_CEIL 0);
   (34%nat, mkAF 4096 CAW_CEIL 0);
   (38%nat, mkAF 0 3145728 0)].
Definition caa_xss : sstate := mkSS 0x81a78 caa_xregs [caw_stk] None (mkFacts caa_xatoms [] []).

(* ---- the state at 0x81804 once this segment's atom fact is in: pad <= 2 ---- *)
Definition caa_facts0 : facts :=
  mkFacts ((39%nat, mkAF 0 2 0) :: f_atoms (cawt_facts 0 3145728))
          (f_conds (cawt_facts 0 3145728)) (f_alias (cawt_facts 0 3145728)).
Definition caa_ss0 : sstate := mkSS 0x81804 cawt_regs [caw_stk] None caa_facts0.
(* with m >= 1 and the one-byte region of six[m - 1] (every arm that reads it, and the arms that only pass it by) *)
Definition caa_facts6 : facts :=
  mkFacts ((38%nat, mkAF 1 3145728 0) :: f_atoms caa_facts0) (f_conds caa_facts0) (f_alias caa_facts0).
Definition caa_ss6 : sstate := mkSS 0x81804 cawt_regs [caw_stk; cawt_six] None caa_facts6.
Definition caa_SH6 : list shent := [mkSHE 40 (-1) 0].

(* ---- pure helpers ---- *)
Lemma caa_last_nth : forall (l : list Z) (d : Z), last l d = nth (Nat.pred (length l)) l d.
Proof.
induction l as [|a l IH]; intros d; [reflexivity|].
destruct l as [|b l']; [reflexivity|].
cbn [last length Nat.pred nth] in *. exact (IH d).
Qed.

Lemma caa_pred_len : forall (l : list Z) (m : Z),
  Z.of_nat (length l) = m -> 1 <= m -> Z.of_nat (Nat.pred (length l)) = m - 1.
Proof.
intros l m Hl Hm. destruct (length l) as [|k] eqn:HL; [cbn in Hl; lia|].
cbn [Nat.pred]. rewrite Nat2Z.inj_succ in Hl. lia.
Qed.

(* `not x, y` (xori x, y, -1) of a 64-bit value v is 2^64 - 1 - v *)
Lemma caa_lxor_ones : forall v, 0 <= v < 2 ^ 64 -> Z.lxor v (Z.ones 64) = Z.ones 64 - v.
Proof.
intros v Hv.
assert (HL : Z.land (Z.lxor v (Z.ones 64)) v = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.lxor_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 64) as [Hlt|Hge].
  - rewrite Z.ones_spec_low by lia. destruct (Z.testbit v i); reflexivity.
  - replace (Z.testbit v i) with false; [apply andb_false_r|].
    symmetry. apply Z.testbit_false; [lia|]. rewrite Z.div_small; [reflexivity|].
    split; [lia|]. apply (Z.lt_le_trans _ (2 ^ 64)); [lia | apply Z.pow_le_mono_r; lia]. }
assert (HX : Z.lxor (Z.lxor v (Z.ones 64)) v = Z.ones 64).
{ rewrite Z.lxor_comm, <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l. reflexivity. }
rewrite <- Z.add_nocarry_lxor in HX by exact HL. lia.
Qed.
Lemma caa_U_not : forall E (a : sv) v, U E a = v -> 0 <= v < 2 ^ 64 ->
  U E (SAlu ALU_XOR a (SLit (-1))) = 2 ^ 64 - 1 - v.
Proof.
intros E a v Ha Hv. rewrite U_SAlu, U_SLit, Ha. cbn [zalu_raw].
replace (zcanon (-1)) with (Z.ones 64) by reflexivity.
rewrite caa_lxor_ones by exact Hv. rewrite Z.ones_equiv.
apply zcanon_id. unfold M64. lia.
Qed.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable Q : world tfibsegs -> config -> Prop.

(* `andi x, n, 2 ^ k - 1` is v mod 2 ^ k *)
Lemma caa_and_ones : forall E n v k, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= k < 64 ->
  U E (SAlu ALU_AND (SOff n 0) (SLit (Z.ones k))) = v mod 2 ^ k.
Proof.
intros E n v k Hn Hv Hk.
assert (Ho : 0 <= Z.ones k < 2 ^ 64).
{ rewrite Z.ones_equiv. assert (2 ^ k <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia). lia. }
rewrite U_and_lit by lia. rewrite (U_atom E n v Hn Hv).
rewrite Z.land_ones by lia. reflexivity.
Qed.
(* restating one register by a value with the same denotation *)
Lemma caa_setreg : forall E ss ms (r : bv 5) v,
  st_ok tfibsegs E ss ms -> bv_eqb r 0 = false ->
  sv_denot E (sr_get (ss_regs ss) r) = sv_denot E v ->
  st_ok tfibsegs E
    (mkSST (ss_pc ss) (sr_set (ss_regs ss) r v) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r v (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) Hr0 Hden.
unfold st_ok. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
split; [exact H5|]. split; [exact H6|]. split; [|split; [exact H8 | exact H9]].
intros r'. destruct (decide (r' = r)) as [->|Hne].
- rewrite (sr_get_set_same (ss_regs ss) r v Hr0). rewrite (H7 r), Hden. reflexivity.
- rewrite (sr_get_set_other (ss_regs ss) r r' v Hne). exact (H7 r').
Qed.

(* the entry sp is where the atom fact of the state puts it *)
Lemma caa_sp_range : forall (W : world tfibsegs) E ms,
  st_ok tfibsegs E (cawt_ss 0 3145728) (restrict (w_H W) ms) ->
  2 ^ 46 <= bv_unsigned (ew E 2) <= 2 ^ 47.
Proof.
intros W E ms (_ & _ & _ & _ & _ & _ & _ & _ & (Hat & _)).
cbn [cawt_ss cawt_facts ss_facts f_atoms] in Hat.
destruct (atoms_ok_In E _ 2%nat (mkAF (2 ^ 46) (2 ^ 47) 4) Hat
            ltac:(cbn [In]; right; left; reflexivity)) as [X _].
exact X.
Qed.

(* the alias fact of the state: atom 40 is six + m *)
Lemma caa_atom40 : forall (W : world tfibsegs) E ms six m,
  st_ok tfibsegs E caa_ss0 (restrict (w_H W) ms) ->
  ew E 33 = Z_to_bv 64 six -> ew E 38 = Z_to_bv 64 m ->
  0 <= six -> 0 <= m -> six + m < 2 ^ 64 ->
  ew E 40 = Z_to_bv 64 (six + m).
Proof.
intros W E ms six m (_ & _ & _ & _ & _ & _ & _ & _ & (Hat & _ & Hal)) E33 E38 H6 Hm Hsum.
cbn [caa_ss0 caa_facts0 ss_facts f_alias f_atoms] in Hat, Hal.
pose proof (alias_ok_In E _ (SAlu ALU_ADD (SOff 33 0) (SOff 38 0)) (SOff 40 0) Hal
              ltac:(cbn [In]; left; reflexivity)) as Hd.
assert (HU : U E (SAlu ALU_ADD (SOff 33 0) (SOff 38 0)) = U E (SOff 40 0))
  by (unfold U; rewrite Hd; reflexivity).
rewrite U_SAlu in HU. cbn [zalu_raw] in HU.
rewrite (U_atom E 33 six E33 ltac:(lia)), (U_atom E 38 m E38 ltac:(lia)) in HU.
rewrite (zcanon_id (six + m)) in HU by (unfold M64; lia).
unfold U in HU. rewrite fsw_SOff0 in HU.
apply bv_eq. rewrite <- HU. rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* the state with m >= 1 and the one-byte region of six[m - 1] added (YP09.v mem_ok: regions_wf, Forall region_ok,
   pairwise disjoint) *)
Lemma caa_add_six : forall (W : world tfibsegs) E ms six m l sp0,
  st_ok tfibsegs E caa_ss0 (restrict (w_H W) ms) ->
  bv_unsigned (ew E 2) = sp0 -> ew E 33 = Z_to_bv 64 six ->
  ew E 38 = Z_to_bv 64 m -> ew E 43 = Z_to_bv 64 l -> 0 <= l < 64 ->
  1 <= m <= 3145728 -> 4096 <= six -> six + m <= CAW_CEIL ->
  six + m <= sp0 - 64 ->
  caw_at W (ms_mem ms) (six + m - 1) l ->
  st_ok tfibsegs E caa_ss6 (restrict (w_H W) ms).
Proof.
intros W E ms six m l sp0 HS Hsp E33 E38 E43 Hl Hm H6 H6hi Hdj1 HB.
assert (CC : 0 < CAW_CEIL < 2 ^ 64) by (unfold CAW_CEIL; lia).
pose proof (caa_atom40 W E ms six m HS E33 E38 ltac:(lia) ltac:(lia) ltac:(lia)) as E40.
pose proof HS as (H1 & H2 & H3 & H4 & H5 & H6r & H7 & H8 & H9).
cbn [caa_ss0 ss_mem] in H8.
destruct H8 as (Hwf & Hok & Hpd).
unfold st_ok. cbn [caa_ss6 ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
cbn [caa_ss0 ss_pc ss_regs ss_fregs ss_resv ss_facts] in H1, H2, H3, H4, H5, H6r, H7, H9.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
split; [exact H5|]. split; [exact H6r|]. split; [exact H7|]. split.
2:{ unfold caa_facts6. apply facts_ok_add_atom; [exact H9|].
    split; [rewrite E38; rewrite unsigned_lit_small by lia; cbn [af_lo af_hi]; lia|].
    split; [cbn [af_al2]; rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | cbn [af_al2]; lia]. }
assert (Hs : region_ok tfibsegs E (ms_mem (restrict (w_H W) ms)) cawt_six).
{ unfold cawt_six, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E40, (unsigned_lit_small (six + m)) by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val tfibsegs E _ (six + m) (-1) 1%N (SOff 43 0) l).
  - rewrite fsw_SOff0. exact E43.
  - cbn [Z.of_N Z.mul]. cbn. lia.
  - cbn. lia.
  - replace (six + m + -1) with (six + m - 1) by lia. exact HB. }
split; [vm_compute; reflexivity|]. split.
- apply Forall_cons; [exact (Forall_inv Hok)|].
  apply Forall_cons; [exact Hs | apply Forall_nil].
- cbn [pairwise_disjoint all_disjoint].
  unfold extent_disjoint, caw_stk, cawt_six.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E40, (unsigned_lit_small (six + m)) by lia. rewrite Hsp.
  split; [split; [right; lia | exact I] | split; exact I].
Qed.

(* the shadow entry of six[m - 1], from the block's range_addressable *)
Lemma caa_sh6 : forall (W : world tfibsegs) E ms six m Lsix,
  ew E 32 = Z_to_bv 64 SHADOW_OFF -> ew E 40 = Z_to_bv 64 (six + m) ->
  range_addressable (rd_of tfibsegs (mrestrict (w_H W) (ms_mem ms))) SHADOW_OFF six Lsix ->
  in_app six Lsix -> 1 <= m -> m <= Lsix -> 4096 <= six -> six + m <= CAW_CEIL ->
  sh_ok tfibsegs caw_Bx caa_SH6 E (mrestrict (w_H W) (ms_mem ms)).
Proof.
intros W E ms six m Lsix E32 E40 RA6 Happ6 Hm Hmle H6 H6hi.
unfold sh_ok, caa_SH6. apply Forall_cons; [|apply Forall_nil].
apply (cae_shent_of_ra E _ 40%nat (six + m) six Lsix).
- rewrite E32. apply unsigned_lit_small. unfold SHADOW_OFF. lia.
- rewrite E40. apply unsigned_lit_small. unfold CAW_CEIL in *. lia.
- exact RA6.
- exact Happ6.
- lia.
- lia.
- lia.
Qed.

Lemma caa_agree_pd : forall E1 E2, env_agree 44 E1 E2 -> env_agree_pd caa_P PT E1 E2.
Proof.
intros E1 E2 [H1 H2]. split.
- intros nn Hnn. unfold caa_P in Hnn. apply Nat.ltb_lt in Hnn. exact (H1 nn Hnn).
- intros d _. rewrite H2. reflexivity.
Qed.

(* the 0x8197c exit, re-keyed onto the canonical atoms *)
Lemma caa_exit_st : forall (W : world tfibsegs) (E1 E2 : env) (ms1 : machine_state) (ssf : sstate),
  st_ok tfibsegs E1 ssf (restrict (w_H W) ms1) ->
  ss_pc ssf = 0x81a78 ->
  nth_error (ss_mem ssf) 0 = Some caw_stk ->
  reabs_check caa_P ssf caa_xregs (mkFacts caa_xatoms [] []) = true ->
  env_agree 44 E1 E2 ->
  Forall (fun rj : bv 5 * nat => ew E2 (snd rj) = getr (ms_regs ms1) (fst rj)) (reabs_obl caa_P caa_xregs) ->
  st_ok tfibsegs E2 caa_xss (restrict (w_H W) ms1).
Proof.
intros W E1 E2 ms1 ssf HS Hpc Hm0 Hchk HAG HOB.
assert (HM1 : mem_ok tfibsegs E1 (ms_mem (restrict (w_H W) ms1)) [caw_stk]).
{ split; [vm_compute; reflexivity|]. split.
  - apply Forall_cons; [exact (fsw_region_nth E1 ssf _ 0%nat caw_stk HS Hm0) | apply Forall_nil].
  - cbn [pairwise_disjoint all_disjoint]. split; exact I. }
unfold caa_xss. rewrite <- Hpc.
apply (st_ok_reabs tfibsegs caa_P E1 E2 ssf (restrict (w_H W) ms1) caa_xregs [caw_stk]
        (mkFacts caa_xatoms [] []) HS (caa_agree_pd E1 E2 HAG) Hchk HOB).
- apply Forall_forall. intros nf Hin. vm_compute in Hin. destruct Hin.
- apply (mem_ok_agree tfibsegs 44 E1 E2); [exact HAG | vm_compute; reflexivity | exact HM1].
Qed.

(* FSW_caw_tail.v's exit, in the same state *)
Lemma caa_free_xst : forall (W : world tfibsegs) (E1 E2 : env) (ms1 : machine_state) plo phi,
  st_ok tfibsegs E1 (cawt_ss_free plo phi) (restrict (w_H W) ms1) ->
  env_agree 44 E1 E2 ->
  Forall (fun rj : bv 5 * nat => ew E2 (snd rj) = getr (ms_regs ms1) (fst rj)) (reabs_obl caa_P caa_xregs) ->
  st_ok tfibsegs E2 caa_xss (restrict (w_H W) ms1).
Proof.
intros W E1 E2 ms1 plo phi HS HAG HOB.
apply (caa_exit_st W E1 E2 ms1 (cawt_ss_free plo phi) HS);
  [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact HAG | exact HOB].
Qed.

(* the register obligations of the re-key: every atom from 44 up is set by the extension list *)
Ltac caa_lk EL LD :=
  lazymatch goal with
  | |- ew _ ?j = _ =>
      let jj := eval compute in (Nat.sub j 44) in
      change j with (44 + jj)%nat; rewrite (EL jj ltac:(lia)); unfold LD; cbn [nth]; reflexivity
  end.

(* the same, for the emit loop's base atom 47 *)
Ltac caa_lk47 EL LD :=
  lazymatch goal with
  | |- ew _ ?j = _ =>
      let jj := eval compute in (Nat.sub j 47) in
      change j with (47 + jj)%nat; rewrite (EL jj ltac:(lia)); unfold LD; cbn [nth]; reflexivity
  end.

(* the registers at 0x81a78, as every arm leaves them: a1, a2, a5 dead, s5 the answer *)
Definition caa_fregs (a1 a2 a5 : sv) (nv : Z) : list sv :=
  [SLit 0; SOff 31 0; SOff 2 (-64); SOff 3 0; SOff 4 0;
   SOff 50 0; SOff 51 0; SOff 52 0;
   SOff 12 0; SOff 11 0;
   SOff 33 0; a1; a2; SOff 30 0; SOff 38 0;
   a5; SOff 56 0; SOff 57 0;
   SOff 34 0; SOff 35 0; SOff 32 0;
   SLit nv; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
   SOff 39 0; SOff 58 0; SOff 59 0; SOff 60 0].

(* the whole hand-over at 0x81a78: the env the re-key needs, the state, and the answer in atom 49 *)
Lemma caa_mkexit : forall (W : world tfibsegs) (E E1 : env) (ms0 : machine_state) (ssf : sstate)
    (a1 a2 a5 : sv) (nv : Z),
  st_ok tfibsegs E1 ssf (restrict (w_H W) ms0) ->
  ss_pc ssf = 0x81a78 ->
  nth_error (ss_mem ssf) 0 = Some caw_stk ->
  reabs_check caa_P ssf caa_xregs (mkFacts caa_xatoms [] []) = true ->
  ss_regs ssf = caa_fregs a1 a2 a5 nv ->
  0 <= nv < 2 ^ 64 ->
  (forall nn, (nn < 44)%nat -> ew E1 nn = ew E nn) -> ed E1 = ed E ->
  exists E2, env_agree 44 E E2 /\ st_ok tfibsegs E2 caa_xss (restrict (w_H W) ms0)
             /\ ew E2 49 = Z_to_bv 64 nv.
Proof.
intros W E E1 ms0 ssf a1 a2 a5 nv HS Hpc Hm0 Hchk Hregs Hnv Hag Hed.
set (LD := [getr (ms_regs ms0) 11%bv; getr (ms_regs ms0) 12%bv; getr (ms_regs ms0) 19%bv;
            getr (ms_regs ms0) 22%bv; Z_to_bv 64 0; getr (ms_regs ms0) 21%bv;
            getr (ms_regs ms0) 5%bv; getr (ms_regs ms0) 6%bv; getr (ms_regs ms0) 7%bv;
            Z_to_bv 64 0; Z_to_bv 64 0;
            getr (ms_regs ms0) 15%bv; getr (ms_regs ms0) 16%bv; getr (ms_regs ms0) 17%bv;
            getr (ms_regs ms0) 28%bv; getr (ms_regs ms0) 29%bv; getr (ms_regs ms0) 30%bv;
            getr (ms_regs ms0) 31%bv]).
set (E2 := extK E1 44 LD).
assert (EL : forall j, (j < 18)%nat -> ew E2 (44 + j) = nth j LD (Z_to_bv 64 0))
  by (intros j Hj; unfold E2; apply cae_ext_lookup; unfold LD; cbn [length]; lia).
exists E2.
split.
{ split.
  - intros nn Hnn. unfold E2. rewrite (proj1 (env_agree_extK E1 44 LD) nn Hnn). exact (Hag nn Hnn).
  - unfold E2. rewrite (proj2 (env_agree_extK E1 44 LD)). exact Hed. }
split.
{ apply (caa_exit_st W E1 E2 ms0 ssf HS Hpc Hm0 Hchk ltac:(unfold E2; apply env_agree_extK)).
  apply Forall_forall. intros rj Hin. vm_compute in Hin.
  repeat (destruct Hin as [<-|Hin]); [..|destruct Hin]; cbn [fst snd]; caa_lk EL LD. }
change 49%nat with (44 + 5)%nat. rewrite (EL 5%nat ltac:(lia)). unfold LD. cbn [nth].
exact (fsw_reg_lit (w_H W) E1 ssf ms0 21%bv nv HS ltac:(rewrite Hregs; vm_compute; reflexivity) Hnv).
Qed.

(* the write window of every run of this segment is the frame of check_as_written *)
Ltac caa_awr Esp :=
  cbn [add_cond caa_ss6 caa_ss0 ss_mem];
  eapply awr_ok_cons_stack with (n := 2%nat);
  [ reflexivity | exact Esp | cbn; lia | cbn; lia
  | repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil ].
(* the frame clause of one run of this segment, from the run's frame_of: the only write window is the frame *)
Ltac caa_kf HF Esp :=
  let x := fresh "x" in let Hx := fresh "Hx" in
  let rr := fresh "rr" in let Hin := fresh "Hin" in let Hb := fresh "Hb" in
  intros x Hx; apply HF; intros (rr & Hin & Hb);
  cbn [add_cond caa_ss6 caa_ss0 ss_mem In] in Hin;
  repeat (destruct Hin as [<-|Hin]; [cbn [caw_stk cawt_six YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
    try rewrite Esp in Hb; apply Hx; lia|]); destruct Hin.

(* ---- the refusal arms: r = 1, or r = 2 with six[m-1] land 15 <> 0, or r = 3 with six[m-1] land 3 <> 0 ---- *)
Lemma caa_refuse_tail : forall (E : env) (ms : machine_state) (mdc : Model)
    (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world tfibsegs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
    (Up : list (Z * Z)) (W : world tfibsegs) (kj : Z) (sx : list Z)
    (six want Lsix Lwant m pad : Z),
  st_ok tfibsegs E (cawt_ss 0 3145728) (restrict (w_H W) ms) ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison Up (ms_mem ms)) mdc kj ->
  ARU tfibsegs B lyc Sc Up W (ms_mem ms) mdc ->
  bv_unsigned (ew E 2) = sp0 -> 64 <= STK ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF -> ew E 33 = Z_to_bv 64 six -> ew E 34 = Z_to_bv 64 want ->
  ew E 38 = Z_to_bv 64 m -> ew E 39 = Z_to_bv 64 pad ->
  ew E 43 = Z_to_bv 64 (last sx 0) ->
  0 <= pad <= 2 -> 1 <= m <= 3145728 ->
  Z.of_nat (length sx) = m -> Forall (fun v => 0 <= v < 64) sx ->
  caw_bytes W (ms_mem ms) six sx ->
  in_app six Lsix -> m <= Lsix -> in_app want Lwant ->
  range_addressable (rd_of tfibsegs (mrestrict (w_H W) (ms_mem ms))) SHADOW_OFF six Lsix ->
  range_addressable (rd_of tfibsegs (mrestrict (w_H W) (ms_mem ms))) SHADOW_OFF want Lwant ->
  six + m <= sp0 - 64 ->
  WSA.six_tail_ok sx = false ->
  (forall (E2 : env) (ms2 : machine_state) (mdc2 : Model),
     env_agree 44 E E2 ->
     st_ok tfibsegs E2 caa_xss (restrict (w_H W) ms2) ->
     ew E2 49 = Z_to_bv 64 SIZE_MAXZ ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison Up (ms_mem ms2)) mdc2 kj ->
     ARU tfibsegs B lyc Sc Up W (ms_mem ms2) mdc2 ->
     (forall x : word, ~ (sp0 - 64 <= bv_unsigned x < sp0) -> ms_mem ms2 x = ms_mem ms x) ->
     mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms2)) ->
     range_addressable (rd_of tfibsegs (mrestrict (w_H W) (ms_mem ms2))) SHADOW_OFF six Lsix ->
     range_addressable (rd_of tfibsegs (mrestrict (w_H W) (ms_mem ms2))) SHADOW_OFF want Lwant ->
     SRr tfibsegs W (mkCfg ms2 mdc2) Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros E ms mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc Up W kj sx six want Lsix Lwant m pad
  HS HJ HARU Esp HSTK E32 E33 E34 E38 E39 E43 Hpad Hm Hlen Hsx HB6
  Happ6 Hmle Happw RA6 RAW Hdj1 HTAIL HCONT.
pose proof ASAN_CEIL_range as [HC1 HC2].
assert (H6lo : 4096 <= six) by (destruct Happ6 as [X _]; exact X).
assert (H6hi : six + Lsix <= CAW_CEIL)
  by (destruct Happ6 as [_ [X|[_ X]]]; unfold kLowShadowBeg, CAW_CEIL in *; lia).
assert (Hwlo : 4096 <= want) by (destruct Happw as [X _]; exact X).
assert (Hwhi : want + Lwant <= CAW_CEIL)
  by (destruct Happw as [_ [X|[_ X]]]; unfold kLowShadowBeg, CAW_CEIL in *; lia).
pose proof (caa_sp_range W E ms HS) as Hspr. rewrite Esp in Hspr.
assert (HL1 : (0 < length sx)%nat) by (destruct (length sx) as [|k] eqn:HL; [cbn in Hlen; lia | lia]).
assert (Hlb : 0 <= last sx 0 < 64).
{ rewrite caa_last_nth. rewrite Forall_forall in Hsx. apply Hsx. apply nth_In. lia. }
assert (HBl : caw_at W (ms_mem ms) (six + m - 1) (last sx 0)).
{ rewrite caa_last_nth. pose proof (HB6 (Nat.pred (length sx)) ltac:(lia)) as Hx.
  rewrite (caa_pred_len sx m Hlen ltac:(lia)) in Hx.
  replace (six + (m - 1)) with (six + m - 1) in Hx by lia. exact Hx. }
pose proof (cawt_add_atom E _ _ 39%nat (mkAF 0 2 0) HS
  ltac:(split; [cbn [af_lo af_hi]; rewrite E39; rewrite unsigned_lit_small by lia; lia|];
        split; [cbn [af_al2]; rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | cbn [af_al2]; lia])) as HS2.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts cawt_ss] in HS2. clear HS.
assert (HS0 : st_ok tfibsegs E caa_ss0 (restrict (w_H W) ms)) by exact HS2. clear HS2.
pose proof (caa_atom40 W E ms six m HS0 E33 E38 ltac:(lia) ltac:(lia) ltac:(unfold CAW_CEIL in *; lia)) as E40.
pose proof (caa_add_six W E ms six m (last sx 0) sp0 HS0 Esp E33 E38 E43 Hlb ltac:(lia) ltac:(lia)
  ltac:(lia) Hdj1 HBl) as HS6. clear HS0.
pose proof (caa_sh6 W E ms six m Lsix E32 E40 RA6 Happ6 ltac:(lia) Hmle ltac:(lia) ltac:(lia)) as SHOK.
unfold WSA.six_tail_ok in HTAIL. cbv zeta in HTAIL. rewrite Hlen in HTAIL.
apply andb_false_iff in HTAIL as [HT|HT3]; [apply andb_false_iff in HT as [HT1|HT2]|].
- (* r = 1 *)
  apply negb_false_iff, Z.eqb_eq in HT1.
  pose proof (st_ok_add_cond tfibsegs E _ _ BC_EQ (SAlu ALU_AND (SOff 38 0) (SLit 3)) (SLit 1) HS6
    ltac:(rewrite branch_eq_U, (cawt_and3 E 38 m E38 ltac:(lia)), (U_lit E 1 ltac:(lia));
          apply Z.eqb_eq; exact HT1)) as HSc. clear HS6.
  fsw_aj_run_to_tokU caw_tbl_ok HSc HJ HARU SHOK caw_Bspan 0x81a78.
  { caa_awr Esp. }
  { lazymatch type of HSc with st_ok _ ?EE _ _ => set (E1 := EE) in * end.
    assert (EQ : forall nn, (nn < 62)%nat -> ew E1 nn = ew E nn)
      by (intros nn Hnn; unfold E1; repeat (rewrite ew_ewset_other by lia); reflexivity).
    assert (KF : forall x : word, ~ (sp0 - 64 <= bv_unsigned x < sp0) -> ms_mem ms0 x = ms_mem ms x)
      by caa_kf HF Esp.
    destruct (caa_mkexit W E E1 ms0 _ (SAlu ALU_AND (SOff 38 0) (SLit 3)) (SLit 1) (SOff 55 0) SIZE_MAXZ
                HSc ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(unfold SIZE_MAXZ; lia) ltac:(intros nn Hnn; apply EQ; lia)
                ltac:(unfold E1; reflexivity))
      as (E2 & HAG & HSX & H49).
    apply (HCONT E2 ms0 _); [exact HAG | exact HSX | exact H49 | exact HJ | exact HARU | exact KF | exact HG | |].
    - apply (cae_ra_keep W (ms_mem ms) (ms_mem ms0) six Lsix (sp0 - 64) sp0 RA6 KF);
        [lia | right; unfold kHighMemBeg in *; lia | lia | unfold CAW_CEIL in *; lia].
    - apply (cae_ra_keep W (ms_mem ms) (ms_mem ms0) want Lwant (sp0 - 64) sp0 RAW KF);
        [lia | right; unfold kHighMemBeg in *; lia | lia | unfold CAW_CEIL in *; lia]. }
- (* r = 2 and six[m-1] land 15 <> 0 *)
  apply orb_false_iff in HT2 as [HT2a HT2b].
  apply negb_false_iff, Z.eqb_eq in HT2a. apply Z.eqb_neq in HT2b.
  pose proof (st_ok_add_cond tfibsegs E _ _ BC_NE (SAlu ALU_AND (SOff 38 0) (SLit 3)) (SLit 1) HS6
    ltac:(rewrite branch_ne_U, (cawt_and3 E 38 m E38 ltac:(lia)), (U_lit E 1 ltac:(lia));
          apply negb_true_iff, Z.eqb_neq; lia)) as HSa. clear HS6.
  pose proof (st_ok_add_cond tfibsegs E _ _ BC_NE (SAlu ALU_AND (SOff 38 0) (SLit 3)) (SLit 3) HSa
    ltac:(rewrite branch_ne_U, (cawt_and3 E 38 m E38 ltac:(lia)), (U_lit E 3 ltac:(lia));
          apply negb_true_iff, Z.eqb_neq; lia)) as HSb. clear HSa.
  pose proof (st_ok_add_cond tfibsegs E _ _ BC_EQ (SAlu ALU_AND (SOff 38 0) (SLit 3)) (SLit 2) HSb
    ltac:(rewrite branch_eq_U, (cawt_and3 E 38 m E38 ltac:(lia)), (U_lit E 2 ltac:(lia));
          apply Z.eqb_eq; exact HT2a)) as HSd. clear HSb.
  pose proof (st_ok_add_cond tfibsegs E _ _ BC_NE (SAlu ALU_AND (SOff 43 0) (SLit 15)) (SLit 0) HSd
    ltac:(replace 15 with (Z.ones 4) by reflexivity;
          rewrite branch_ne_U, (caa_and_ones E 43 (last sx 0) 4 E43 ltac:(lia) ltac:(lia)),
                  (U_lit E 0 ltac:(lia));
          apply negb_true_iff, Z.eqb_neq; change (2 ^ 4) with 16; exact HT2b)) as HSc. clear HSd.
  fsw_aj_run_to_tokU caw_tbl_ok HSc HJ HARU SHOK caw_Bspan 0x81a78.
  { caa_awr Esp. }
  { lazymatch type of HSc with st_ok _ ?EE _ _ => set (E1 := EE) in * end.
    assert (EQ : forall nn, (nn < 62)%nat -> ew E1 nn = ew E nn)
      by (intros nn Hnn; unfold E1; repeat (rewrite ew_ewset_other by lia); reflexivity).
    assert (KF : forall x : word, ~ (sp0 - 64 <= bv_unsigned x < sp0) -> ms_mem ms0 x = ms_mem ms x)
      by caa_kf HF Esp.
    destruct (caa_mkexit W E E1 ms0 _ (SAlu ALU_AND (SOff 43 0) (SLit 15)) (SOff 62 0) (SOff 63 0) SIZE_MAXZ
                HSc ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(unfold SIZE_MAXZ; lia) ltac:(intros nn Hnn; apply EQ; lia)
                ltac:(unfold E1; reflexivity))
      as (E2 & HAG & HSX & H49).
    apply (HCONT E2 ms0 _); [exact HAG | exact HSX | exact H49 | exact HJ | exact HARU | exact KF | exact HG | |].
    - apply (cae_ra_keep W (ms_mem ms) (ms_mem ms0) six Lsix (sp0 - 64) sp0 RA6 KF);
        [lia | right; unfold kHighMemBeg in *; lia | lia | unfold CAW_CEIL in *; lia].
    - apply (cae_ra_keep W (ms_mem ms) (ms_mem ms0) want Lwant (sp0 - 64) sp0 RAW KF);
        [lia | right; unfold kHighMemBeg in *; lia | lia | unfold CAW_CEIL in *; lia]. }
- (* r = 3 and six[m-1] land 3 <> 0 *)
  apply orb_false_iff in HT3 as [HT3a HT3b].
  apply negb_false_iff, Z.eqb_eq in HT3a. apply Z.eqb_neq in HT3b.
  pose proof (st_ok_add_cond tfibsegs E _ _ BC_NE (SAlu ALU_AND (SOff 38 0) (SLit 3)) (SLit 1) HS6
    ltac:(rewrite branch_ne_U, (cawt_and3 E 38 m E38 ltac:(lia)), (U_lit E 1 ltac:(lia));
          apply negb_true_iff, Z.eqb_neq; lia)) as HSa. clear HS6.
  pose proof (st_ok_add_cond tfibsegs E _ _ BC_EQ (SAlu ALU_AND (SOff 38 0) (SLit 3)) (SLit 3) HSa
    ltac:(rewrite branch_eq_U, (cawt_and3 E 38 m E38 ltac:(lia)), (U_lit E 3 ltac:(lia));
          apply Z.eqb_eq; exact HT3a)) as HSb. clear HSa.
  pose proof (st_ok_add_cond tfibsegs E _ _ BC_NE (SAlu ALU_AND (SOff 43 0) (SLit 3)) (SLit 0) HSb
    ltac:(replace 3 with (Z.ones 2) by reflexivity;
          rewrite branch_ne_U, (caa_and_ones E 43 (last sx 0) 2 E43 ltac:(lia) ltac:(lia)),
                  (U_lit E 0 ltac:(lia));
          apply negb_true_iff, Z.eqb_neq; change (2 ^ 2) with 4; exact HT3b)) as HSc. clear HSb.
  fsw_aj_run_to_tokU caw_tbl_ok HSc HJ HARU SHOK caw_Bspan 0x81a78.
  { caa_awr Esp. }
  { lazymatch type of HSc with st_ok _ ?EE _ _ => set (E1 := EE) in * end.
    assert (EQ : forall nn, (nn < 62)%nat -> ew E1 nn = ew E nn)
      by (intros nn Hnn; unfold E1; repeat (rewrite ew_ewset_other by lia); reflexivity).
    assert (KF : forall x : word, ~ (sp0 - 64 <= bv_unsigned x < sp0) -> ms_mem ms0 x = ms_mem ms x)
      by caa_kf HF Esp.
    destruct (caa_mkexit W E E1 ms0 _ (SAlu ALU_AND (SOff 43 0) (SLit 3)) (SOff 62 0) (SOff 63 0) SIZE_MAXZ
                HSc ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(unfold SIZE_MAXZ; lia) ltac:(intros nn Hnn; apply EQ; lia)
                ltac:(unfold E1; reflexivity))
      as (E2 & HAG & HSX & H49).
    apply (HCONT E2 ms0 _); [exact HAG | exact HSX | exact H49 | exact HJ | exact HARU | exact KF | exact HG | |].
    - apply (cae_ra_keep W (ms_mem ms) (ms_mem ms0) six Lsix (sp0 - 64) sp0 RA6 KF);
        [lia | right; unfold kHighMemBeg in *; lia | lia | unfold CAW_CEIL in *; lia].
    - apply (cae_ra_keep W (ms_mem ms) (ms_mem ms0) want Lwant (sp0 - 64) sp0 RAW KF);
        [lia | right; unfold kHighMemBeg in *; lia | lia | unfold CAW_CEIL in *; lia]. }
Qed.

(* ---- the accept arm with m = 0: 0x81890 `mv s5, zero`, then `beqz a4` to 0x81a78 with n = 0 ---- *)
Lemma caa_accept_m0 : forall (E : env) (ms : machine_state) (mdc : Model)
    (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world tfibsegs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
    (Up : list (Z * Z)) (W : world tfibsegs) (kj : Z)
    (six want Lsix Lwant pad : Z),
  st_ok tfibsegs E (cawt_ss 0 3145728) (restrict (w_H W) ms) ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison Up (ms_mem ms)) mdc kj ->
  ARU tfibsegs B lyc Sc Up W (ms_mem ms) mdc ->
  bv_unsigned (ew E 2) = sp0 -> 64 <= STK ->
  ew E 33 = Z_to_bv 64 six -> ew E 34 = Z_to_bv 64 want ->
  ew E 38 = Z_to_bv 64 0 -> ew E 39 = Z_to_bv 64 pad ->
  0 <= pad <= 2 ->
  in_app six Lsix -> in_app want Lwant ->
  range_addressable (rd_of tfibsegs (mrestrict (w_H W) (ms_mem ms))) SHADOW_OFF six Lsix ->
  range_addressable (rd_of tfibsegs (mrestrict (w_H W) (ms_mem ms))) SHADOW_OFF want Lwant ->
  (forall (E2 : env) (ms2 : machine_state) (mdc2 : Model),
     env_agree 44 E E2 ->
     st_ok tfibsegs E2 caa_xss (restrict (w_H W) ms2) ->
     ew E2 49 = Z_to_bv 64 0 ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison Up (ms_mem ms2)) mdc2 kj ->
     ARU tfibsegs B lyc Sc Up W (ms_mem ms2) mdc2 ->
     (forall x : word, ~ (sp0 - 64 <= bv_unsigned x < sp0) -> ms_mem ms2 x = ms_mem ms x) ->
     mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms2)) ->
     range_addressable (rd_of tfibsegs (mrestrict (w_H W) (ms_mem ms2))) SHADOW_OFF six Lsix ->
     range_addressable (rd_of tfibsegs (mrestrict (w_H W) (ms_mem ms2))) SHADOW_OFF want Lwant ->
     SRr tfibsegs W (mkCfg ms2 mdc2) Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros E ms mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc Up W kj six want Lsix Lwant pad
  HS HJ HARU Esp HSTK E33 E34 E38 E39 Hpad Happ6 Happw RA6 RAW HCONT.
pose proof ASAN_CEIL_range as [HC1 HC2].
assert (H6lo : 4096 <= six) by (destruct Happ6 as [X _]; exact X).
assert (H6hi : six + Lsix <= CAW_CEIL)
  by (destruct Happ6 as [_ [X|[_ X]]]; unfold kLowShadowBeg, CAW_CEIL in *; lia).
assert (Hwlo : 4096 <= want) by (destruct Happw as [X _]; exact X).
assert (Hwhi : want + Lwant <= CAW_CEIL)
  by (destruct Happw as [_ [X|[_ X]]]; unfold kLowShadowBeg, CAW_CEIL in *; lia).
pose proof (caa_sp_range W E ms HS) as Hspr. rewrite Esp in Hspr.
pose proof (cawt_add_atom E _ _ 39%nat (mkAF 0 2 0) HS
  ltac:(split; [cbn [af_lo af_hi]; rewrite E39; rewrite unsigned_lit_small by lia; lia|];
        split; [cbn [af_al2]; rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | cbn [af_al2]; lia])) as HS2.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts cawt_ss] in HS2. clear HS.
assert (HS0 : st_ok tfibsegs E caa_ss0 (restrict (w_H W) ms)) by exact HS2. clear HS2.
pose proof (st_ok_add_cond tfibsegs E _ _ BC_NE (SAlu ALU_AND (SOff 38 0) (SLit 3)) (SLit 1) HS0
  ltac:(rewrite branch_ne_U, (cawt_and3 E 38 0 E38 ltac:(lia)), (U_lit E 1 ltac:(lia));
        apply negb_true_iff, Z.eqb_neq; lia)) as HSa. clear HS0.
pose proof (st_ok_add_cond tfibsegs E _ _ BC_NE (SAlu ALU_AND (SOff 38 0) (SLit 3)) (SLit 3) HSa
  ltac:(rewrite branch_ne_U, (cawt_and3 E 38 0 E38 ltac:(lia)), (U_lit E 3 ltac:(lia));
        apply negb_true_iff, Z.eqb_neq; lia)) as HSb. clear HSa.
pose proof (st_ok_add_cond tfibsegs E _ _ BC_NE (SAlu ALU_AND (SOff 38 0) (SLit 3)) (SLit 2) HSb
  ltac:(rewrite branch_ne_U, (cawt_and3 E 38 0 E38 ltac:(lia)), (U_lit E 2 ltac:(lia));
        apply negb_true_iff, Z.eqb_neq; lia)) as HSd. clear HSb.
pose proof (st_ok_add_cond tfibsegs E _ _ BC_EQ (SOff 38 0) (SLit 0) HSd
  ltac:(rewrite branch_eq_U, (U_atom E 38 0 E38 ltac:(lia)), (U_lit E 0 ltac:(lia));
        apply Z.eqb_eq; reflexivity)) as HSc. clear HSd.
assert (SHOK : sh_ok tfibsegs caw_Bx cawt_SH E (mrestrict (w_H W) (ms_mem ms))) by (unfold sh_ok, cawt_SH; constructor).
fsw_aj_run_to_tokU caw_tbl_ok HSc HJ HARU SHOK caw_Bspan 0x81a78.
{ caa_awr Esp. }
  { lazymatch type of HSc with st_ok _ ?EE _ _ => set (E1 := EE) in * end.
    assert (EQ : forall nn, (nn < 62)%nat -> ew E1 nn = ew E nn)
      by (intros nn Hnn; unfold E1; repeat (rewrite ew_ewset_other by lia); reflexivity).
    assert (KF : forall x : word, ~ (sp0 - 64 <= bv_unsigned x < sp0) -> ms_mem ms0 x = ms_mem ms x)
      by caa_kf HF Esp.
    destruct (caa_mkexit W E E1 ms0 _ (SAlu ALU_AND (SOff 38 0) (SLit 3)) (SLit 2) (SOff 55 0) 0
                HSc ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(lia) ltac:(intros nn Hnn; apply EQ; lia)
                ltac:(unfold E1; reflexivity))
      as (E2 & HAG & HSX & H49).
    apply (HCONT E2 ms0 _); [exact HAG | exact HSX | exact H49 | exact HJ | exact HARU | exact KF | exact HG | |].
    - apply (cae_ra_keep W (ms_mem ms) (ms_mem ms0) six Lsix (sp0 - 64) sp0 RA6 KF);
        [lia | right; unfold kHighMemBeg in *; lia | lia | unfold CAW_CEIL in *; lia].
    - apply (cae_ra_keep W (ms_mem ms) (ms_mem ms0) want Lwant (sp0 - 64) sp0 RAW KF);
        [lia | right; unfold kHighMemBeg in *; lia | lia | unfold CAW_CEIL in *; lia]. }
Qed.

(* ---- the hand-over at the emit loop head 0x818ac ----
   the registers the three accept arms leave there; only a2 (x12, dead) differs between them *)
Definition caa_hregs (a2 : sv) : list sv :=
  [SLit 0; SOff 31 0; SOff 2 (-64); SOff 3 0; SOff 4 0;
   SLit CAW_M1; SOff 51 0; SOff 52 0;
   SOff 12 0; SOff 11 0;
   SOff 33 0; SLit 4; a2; SOff 30 0; SOff 38 0;
   SAlu ALU_XOR (SOff 34 0) (SLit (-1)); SOff 33 1; SLit 4;
   SOff 34 0; SOff 35 0; SOff 32 0;
   SLit 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
   SOff 39 0; SOff 58 0; SOff 59 0; SOff 60 0].

Lemma caa_mkhead : forall (W : world tfibsegs) (E E1 : env) (ms0 : machine_state) (ssf : sstate) (a2 : sv)
    (sx : list Z) (six want Lsix Lwant m : Z),
  st_ok tfibsegs E1 ssf (restrict (w_H W) ms0) ->
  ss_pc ssf = 0x818ac ->
  ss_regs ssf = caa_hregs a2 ->
  ss_resv ssf = None ->
  facts_reabs_ok cae_P (ss_facts ssf) (mkFacts cae_atoms [] []) = true ->
  nth_error (ss_mem ssf) 0 = Some caw_stk ->
  (forall nn, (nn < 44)%nat -> ew E1 nn = ew E nn) -> ed E1 = ed E ->
  ew E 33 = Z_to_bv 64 six -> ew E 34 = Z_to_bv 64 want ->
  caw_bytes W (ms_mem ms0) six sx ->
  (forall a, want <= a < want + Lwant -> writable_at tfibsegs (mrestrict (w_H W) (ms_mem ms0)) a) ->
  Forall (fun v => 0 <= v < 64) sx -> Z.of_nat (length sx) = m -> 2 <= m <= 3145728 ->
  4096 <= six -> six + Lsix <= CAW_CEIL -> m <= Lsix -> 4096 <= want -> want + Lwant <= CAW_CEIL ->
  3 <= Lwant -> (six + Lsix <= want \/ want + Lwant <= six) ->
  exists E2, env_agree 44 E E2
    /\ st_ok tfibsegs E2 (cae_ss (cae_k sx) []) (restrict (w_H W) ms0)
    /\ ew E2 47 = Z_to_bv 64 (0 + 4) /\ ew E2 48 = Z_to_bv 64 (six + 0 + 4)
    /\ ew E2 49 = Z_to_bv 64 0 /\ ew E2 50 = Z_to_bv 64 (want + 0)
    /\ ew E2 51 = Z_to_bv 64 (six + 0 + 5)
    /\ (forall j, (j < cae_k sx)%nat -> ew E2 (52 + j) = Z_to_bv 64 (nth j sx 0))
    /\ ew E2 66 = Z_to_bv 64 (2 ^ 64 - 1 - want)
    /\ region_ok tfibsegs E2 (mrestrict (w_H W) (ms_mem ms0)) caw_stk.
Proof.
intros W E E1 ms0 ssf a2 sx six want Lsix Lwant m HS Hpc Hregs Hresv Hfacts Hm0 Hag Hed E33 E34 HB6 HWR
  Hsx Hlen Hm H6lo H6hi Hmle Hwlo Hwhi Hw3 Hdisj.
assert (Hk : (2 <= cae_k sx <= 4)%nat).
{ unfold cae_k. assert (2 <= length sx)%nat by lia. lia. }
set (LD2 := [getr (ms_regs ms0) 11%bv; Z_to_bv 64 (six + 4); getr (ms_regs ms0) 21%bv;
             Z_to_bv 64 want; Z_to_bv 64 (six + 5);
             Z_to_bv 64 (nth 0 sx 0); Z_to_bv 64 (nth 1 sx 0);
             Z_to_bv 64 (nth 2 sx 0); Z_to_bv 64 (nth 3 sx 0);
             getr (ms_regs ms0) 6%bv; getr (ms_regs ms0) 7%bv; getr (ms_regs ms0) 12%bv;
             getr (ms_regs ms0) 19%bv; getr (ms_regs ms0) 22%bv; getr (ms_regs ms0) 28%bv;
             getr (ms_regs ms0) 29%bv; getr (ms_regs ms0) 30%bv; getr (ms_regs ms0) 31%bv;
             Z_to_bv 64 0; getr (ms_regs ms0) 15%bv]).
set (E2 := extK E1 47 LD2).
assert (EL : forall j, (j < 20)%nat -> ew E2 (47 + j) = nth j LD2 (Z_to_bv 64 0))
  by (intros j Hj; unfold E2; apply cae_ext_lookup; unfold LD2; cbn [length]; lia).
assert (HAG47 : env_agree 47 E1 E2) by (unfold E2; apply env_agree_extK).
assert (R11 : getr (ms_regs ms0) 11%bv = Z_to_bv 64 4)
  by (apply (fsw_reg_lit (w_H W) E1 ssf ms0 11%bv 4 HS ltac:(rewrite Hregs; vm_compute; reflexivity)
               ltac:(lia))).
assert (R21 : getr (ms_regs ms0) 21%bv = Z_to_bv 64 0)
  by (apply (fsw_reg_lit (w_H W) E1 ssf ms0 21%bv 0 HS ltac:(rewrite Hregs; vm_compute; reflexivity)
               ltac:(lia))).
assert (E34' : ew E1 34 = Z_to_bv 64 want) by (rewrite (Hag 34%nat ltac:(lia)); exact E34).
assert (R15 : getr (ms_regs ms0) 15%bv = Z_to_bv 64 (2 ^ 64 - 1 - want)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E1 ssf ms0 15%bv HS).
  replace (sr_get (ss_regs ssf) 15%bv) with (SAlu ALU_XOR (SOff 34 0) (SLit (-1)))
    by (rewrite Hregs; vm_compute; reflexivity).
  apply bv_eq. change (U E1 (SAlu ALU_XOR (SOff 34 0) (SLit (-1))) = bv_unsigned (Z_to_bv 64 (2 ^ 64 - 1 - want))).
  rewrite (caa_U_not E1 (SOff 34 0) want (U_atom E1 34 want E34' ltac:(unfold CAW_CEIL in *; lia))
             ltac:(unfold CAW_CEIL in *; lia)).
  rewrite unsigned_lit_small by (unfold CAW_CEIL in *; lia). reflexivity. }
assert (A47 : ew E2 47 = Z_to_bv 64 (0 + 4)).
{ change 47%nat with (47 + 0)%nat. rewrite (EL 0%nat ltac:(lia)). unfold LD2. cbn [nth].
  rewrite R11. f_equal. }
assert (A48 : ew E2 48 = Z_to_bv 64 (six + 0 + 4)).
{ change 48%nat with (47 + 1)%nat. rewrite (EL 1%nat ltac:(lia)). unfold LD2. cbn [nth]. f_equal. try lia. }
assert (A49 : ew E2 49 = Z_to_bv 64 0).
{ change 49%nat with (47 + 2)%nat. rewrite (EL 2%nat ltac:(lia)). unfold LD2. cbn [nth]. exact R21. }
assert (A50 : ew E2 50 = Z_to_bv 64 (want + 0)).
{ change 50%nat with (47 + 3)%nat. rewrite (EL 3%nat ltac:(lia)). unfold LD2. cbn [nth]. f_equal. try lia. }
assert (A51 : ew E2 51 = Z_to_bv 64 (six + 0 + 5)).
{ change 51%nat with (47 + 4)%nat. rewrite (EL 4%nat ltac:(lia)). unfold LD2. cbn [nth]. f_equal. try lia. }
assert (A52 : ew E2 52 = Z_to_bv 64 (nth 0 sx 0))
  by (change 52%nat with (47 + 5)%nat; rewrite (EL 5%nat ltac:(lia)); unfold LD2; cbn [nth]; reflexivity).
assert (A53 : ew E2 53 = Z_to_bv 64 (nth 1 sx 0))
  by (change 53%nat with (47 + 6)%nat; rewrite (EL 6%nat ltac:(lia)); unfold LD2; cbn [nth]; reflexivity).
assert (A54 : ew E2 54 = Z_to_bv 64 (nth 2 sx 0))
  by (change 54%nat with (47 + 7)%nat; rewrite (EL 7%nat ltac:(lia)); unfold LD2; cbn [nth]; reflexivity).
assert (A55 : ew E2 55 = Z_to_bv 64 (nth 3 sx 0))
  by (change 55%nat with (47 + 8)%nat; rewrite (EL 8%nat ltac:(lia)); unfold LD2; cbn [nth]; reflexivity).
assert (A66 : ew E2 66 = Z_to_bv 64 (2 ^ 64 - 1 - want))
  by (change 66%nat with (47 + 19)%nat; rewrite (EL 19%nat ltac:(lia)); unfold LD2; cbn [nth]; exact R15).
assert (A33 : ew E2 33 = Z_to_bv 64 six)
  by (rewrite (proj1 HAG47 33%nat ltac:(lia)); rewrite (Hag 33%nat ltac:(lia)); exact E33).
assert (A34 : ew E2 34 = Z_to_bv 64 want)
  by (rewrite (proj1 HAG47 34%nat ltac:(lia)); rewrite (Hag 34%nat ltac:(lia)); exact E34).
assert (Asx : forall j, (j < cae_k sx)%nat -> ew E2 (52 + j) = Z_to_bv 64 (nth j sx 0)).
{ intros j Hj. destruct j as [|[|[|[|j]]]]; cbn [Nat.add];
    [exact A52 | exact A53 | exact A54 | exact A55 | exfalso; unfold cae_k in Hj; lia]. }
(* the frame region of check_as_written, read off the hand-over state and re-keyed: the emit loop's state
   (FSW_caw_emit.v cae_ss) drops caw_stk, and the back half's epilogue reloads ra and s0..s6 from it, so the
   walk carries it across the loop by hand (assembly) *)
assert (HRG : region_ok tfibsegs E2 (mrestrict (w_H W) (ms_mem ms0)) caw_stk).
{ assert (HM1 : mem_ok tfibsegs E1 (ms_mem (restrict (w_H W) ms0)) [caw_stk]).
  { split; [vm_compute; reflexivity|]. split.
    - apply Forall_cons; [exact (fsw_region_nth E1 ssf _ 0%nat caw_stk HS Hm0) | apply Forall_nil].
    - cbn [pairwise_disjoint all_disjoint]. split; exact I. }
  assert (HAT : mem_atoms_lt 47 [caw_stk] = true) by (vm_compute; reflexivity).
  destruct (mem_ok_agree tfibsegs 47 E1 E2 (ms_mem (restrict (w_H W) ms0)) [caw_stk] HAG47 HAT HM1)
    as (_ & HFr & _).
  cbn [ms_mem restrict] in HFr. exact (Forall_inv HFr). }
exists E2. split.
{ split.
  - intros nn Hnn. rewrite (proj1 HAG47 nn ltac:(lia)). exact (Hag nn Hnn).
  - rewrite (proj2 HAG47). exact Hed. }
split; [|split; [exact A47 | split; [exact A48 | split; [exact A49 | split; [exact A50 | split;
  [exact A51 | split; [exact Asx | split; [exact A66 | exact HRG]]]]]]]].
apply (cae_head_st W E1 E2 ms0 ssf (cae_k sx) sx six want 0 0 HS).
- exact Hpc.
- unfold reabs_check. rewrite Hregs, Hresv, Hfacts.
  vm_compute. reflexivity.
- exact HAG47.
- apply Forall_forall. intros rj Hin. vm_compute in Hin.
  repeat (destruct Hin as [<-|Hin]); [..|destruct Hin]; cbn [fst snd]; caa_lk47 EL LD2.
- exact A33.
- exact A34.
- exact A47.
- exact A48.
- exact A49.
- exact A50.
- exact A51.
- exact A52.
- exact A53.
- exact A54.
- exact A55.
- exact A66.
- exact Hsx.
- lia.
- lia.
- lia.
- lia.
- unfold CAW_CEIL in *. lia.
- lia.
- unfold CAW_CEIL in *. lia.
- cbn [ms_mem restrict].
  apply (cae_mem_ok (cae_k sx) E2 _ six want sx).
  + exact Hk.
  + unfold cae_k. lia.
  + rewrite A51. rewrite unsigned_lit_small by (unfold CAW_CEIL in *; lia). lia.
  + rewrite A50. rewrite unsigned_lit_small by (unfold CAW_CEIL in *; lia). lia.
  + intros j Hj. exact (Asx j Hj).
  + exact Hsx.
  + intros j Hj. apply HB6. unfold cae_k in Hj. lia.
  + intros o Ho. apply HWR. lia.
  + lia.
  + unfold CAW_CEIL in *. lia.
  + lia.
  + unfold CAW_CEIL in *. lia.
  + destruct Hdisj as [X|X]; [left; unfold cae_k; lia | right; lia].
Qed.

(* ---- the accept arms with m > 0 (r = 0, or r = 2 with six[m-1] land 15 = 0, or r = 3 with six[m-1] land 3 = 0):
   0x81890 `mv s5, zero; beqz a4` falls through, `not a5, s2; addi a6, a0, 1; addi a7, zero, 4; addi t0, zero, -1;
   addi a1, zero, 4`, and the walk is at the emit loop head 0x818ac in caw_emit_loop's state at i = 0, n = 0,
   done = [] ---- *)
Lemma caa_accept_emit : forall (E : env) (ms : machine_state) (mdc : Model)
    (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world tfibsegs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
    (Up : list (Z * Z)) (W : world tfibsegs) (kj : Z) (sx : list Z)
    (six want Lsix Lwant m pad : Z),
  st_ok tfibsegs E (cawt_ss 0 3145728) (restrict (w_H W) ms) ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison Up (ms_mem ms)) mdc kj ->
  ARU tfibsegs B lyc Sc Up W (ms_mem ms) mdc ->
  bv_unsigned (ew E 2) = sp0 -> 64 <= STK ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF -> ew E 33 = Z_to_bv 64 six -> ew E 34 = Z_to_bv 64 want ->
  ew E 38 = Z_to_bv 64 m -> ew E 39 = Z_to_bv 64 pad ->
  ew E 43 = Z_to_bv 64 (last sx 0) ->
  0 <= pad <= 2 -> 1 <= m <= 3145728 ->
  Z.of_nat (length sx) = m -> Forall (fun v => 0 <= v < 64) sx ->
  caw_bytes W (ms_mem ms) six sx ->
  in_app six Lsix -> m <= Lsix -> in_app want Lwant -> 3 * (m / 4) + 3 <= Lwant ->
  (six + Lsix <= want \/ want + Lwant <= six) ->
  range_addressable (rd_of tfibsegs (mrestrict (w_H W) (ms_mem ms))) SHADOW_OFF six Lsix ->
  range_addressable (rd_of tfibsegs (mrestrict (w_H W) (ms_mem ms))) SHADOW_OFF want Lwant ->
  (forall a, want <= a < want + Lwant -> writable_at tfibsegs (mrestrict (w_H W) (ms_mem ms)) a) ->
  six + m <= sp0 - 64 ->
  WSA.six_tail_ok sx = true ->
  (forall (E2 : env) (ms2 : machine_state) (mdc2 : Model),
     env_agree 44 E E2 ->
     st_ok tfibsegs E2 (cae_ss (cae_k sx) []) (restrict (w_H W) ms2) ->
     ew E2 47 = Z_to_bv 64 (0 + 4) -> ew E2 48 = Z_to_bv 64 (six + 0 + 4) ->
     ew E2 49 = Z_to_bv 64 0 -> ew E2 50 = Z_to_bv 64 (want + 0) ->
     ew E2 51 = Z_to_bv 64 (six + 0 + 5) ->
     (forall j, (j < cae_k sx)%nat -> ew E2 (52 + j) = Z_to_bv 64 (nth j sx 0)) ->
     ew E2 66 = Z_to_bv 64 (2 ^ 64 - 1 - want) ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison Up (ms_mem ms2)) mdc2 kj ->
     ARU tfibsegs B lyc Sc Up W (ms_mem ms2) mdc2 ->
     caw_bytes W (ms_mem ms2) (six + 0) sx ->
     (forall x : word, ~ (sp0 - 64 <= bv_unsigned x < sp0) -> ms_mem ms2 x = ms_mem ms x) ->
     mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms2)) ->
     range_addressable (rd_of tfibsegs (mrestrict (w_H W) (ms_mem ms2))) SHADOW_OFF six Lsix ->
     range_addressable (rd_of tfibsegs (mrestrict (w_H W) (ms_mem ms2))) SHADOW_OFF want Lwant ->
     (forall a, want <= a < want + Lwant -> writable_at tfibsegs (mrestrict (w_H W) (ms_mem ms2)) a) ->
     (* the frame region, which the emit loop's own state (cae_ss) does not carry: the back half reloads ra and
        s0..s6 from it after the loop (assembly) *)
     region_ok tfibsegs E2 (mrestrict (w_H W) (ms_mem ms2)) caw_stk ->
     SRr tfibsegs W (mkCfg ms2 mdc2) Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros E ms mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc Up W kj sx six want Lsix Lwant m pad
  HS HJ HARU Esp HSTK E32 E33 E34 E38 E39 E43 Hpad Hm Hlen Hsx HB6
  Happ6 Hmle Happw Hwfit Hdisj RA6 RAW HWR Hdj1 HTAIL HCONT.
pose proof ASAN_CEIL_range as [HC1 HC2].
assert (H6lo : 4096 <= six) by (destruct Happ6 as [X _]; exact X).
assert (H6hi : six + Lsix <= CAW_CEIL)
  by (destruct Happ6 as [_ [X|[_ X]]]; unfold kLowShadowBeg, CAW_CEIL in *; lia).
assert (Hwlo : 4096 <= want) by (destruct Happw as [X _]; exact X).
assert (Hwhi : want + Lwant <= CAW_CEIL)
  by (destruct Happw as [_ [X|[_ X]]]; unfold kLowShadowBeg, CAW_CEIL in *; lia).
assert (Hw3 : 3 <= Lwant) by (assert (0 <= m / 4) by (apply Z.div_pos; lia); lia).
pose proof (caa_sp_range W E ms HS) as Hspr. rewrite Esp in Hspr.
assert (HL1 : (0 < length sx)%nat) by (destruct (length sx) as [|k] eqn:HL; [cbn in Hlen; lia | lia]).
assert (Hlb : 0 <= last sx 0 < 64).
{ rewrite caa_last_nth. rewrite Forall_forall in Hsx. apply Hsx. apply nth_In. lia. }
assert (HBl : caw_at W (ms_mem ms) (six + m - 1) (last sx 0)).
{ rewrite caa_last_nth. pose proof (HB6 (Nat.pred (length sx)) ltac:(lia)) as Hx.
  rewrite (caa_pred_len sx m Hlen ltac:(lia)) in Hx.
  replace (six + (m - 1)) with (six + m - 1) in Hx by lia. exact Hx. }
pose proof (cawt_add_atom E _ _ 39%nat (mkAF 0 2 0) HS
  ltac:(split; [cbn [af_lo af_hi]; rewrite E39; rewrite unsigned_lit_small by lia; lia|];
        split; [cbn [af_al2]; rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | cbn [af_al2]; lia])) as HS2.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts cawt_ss] in HS2. clear HS.
assert (HS0 : st_ok tfibsegs E caa_ss0 (restrict (w_H W) ms)) by exact HS2. clear HS2.
pose proof (caa_atom40 W E ms six m HS0 E33 E38 ltac:(lia) ltac:(lia) ltac:(unfold CAW_CEIL in *; lia)) as E40.
pose proof (caa_add_six W E ms six m (last sx 0) sp0 HS0 Esp E33 E38 E43 Hlb ltac:(lia) ltac:(lia)
  ltac:(lia) Hdj1 HBl) as HS6. clear HS0.
pose proof (caa_sh6 W E ms six m Lsix E32 E40 RA6 Happ6 ltac:(lia) Hmle ltac:(lia) ltac:(lia)) as SHOK.
(* the condition m <> 0, common to the three arms *)
assert (Cm : branch_taken BC_NE (sv_denot E (SOff 38 0)) (sv_denot E (SLit 0)) = true).
{ rewrite branch_ne_U, (U_atom E 38 m E38 ltac:(lia)), (U_lit E 0 ltac:(lia)).
  apply negb_true_iff, Z.eqb_neq. lia. }
unfold WSA.six_tail_ok in HTAIL. cbv zeta in HTAIL. rewrite Hlen in HTAIL.
apply andb_true_iff in HTAIL as [HTa HT3]. apply andb_true_iff in HTa as [HT1 HT2].
apply negb_true_iff, Z.eqb_neq in HT1.
destruct (Z.eq_dec (m mod 4) 2) as [Hr2|Hr2].
- (* r = 2 and six[m-1] land 15 = 0 *)
  assert (Hl16 : last sx 0 mod 16 = 0).
  { apply orb_true_iff in HT2 as [X|X]; [rewrite Hr2 in X; cbn in X; discriminate | apply Z.eqb_eq; exact X]. }
  pose proof (st_ok_add_cond tfibsegs E _ _ BC_NE (SAlu ALU_AND (SOff 38 0) (SLit 3)) (SLit 1) HS6
    ltac:(rewrite branch_ne_U, (cawt_and3 E 38 m E38 ltac:(lia)), (U_lit E 1 ltac:(lia));
          apply negb_true_iff, Z.eqb_neq; lia)) as HSa. clear HS6.
  pose proof (st_ok_add_cond tfibsegs E _ _ BC_NE (SAlu ALU_AND (SOff 38 0) (SLit 3)) (SLit 3) HSa
    ltac:(rewrite branch_ne_U, (cawt_and3 E 38 m E38 ltac:(lia)), (U_lit E 3 ltac:(lia));
          apply negb_true_iff, Z.eqb_neq; lia)) as HSb. clear HSa.
  pose proof (st_ok_add_cond tfibsegs E _ _ BC_EQ (SAlu ALU_AND (SOff 38 0) (SLit 3)) (SLit 2) HSb
    ltac:(rewrite branch_eq_U, (cawt_and3 E 38 m E38 ltac:(lia)), (U_lit E 2 ltac:(lia));
          apply Z.eqb_eq; exact Hr2)) as HSd. clear HSb.
  pose proof (st_ok_add_cond tfibsegs E _ _ BC_EQ (SAlu ALU_AND (SOff 43 0) (SLit 15)) (SLit 0) HSd
    ltac:(replace 15 with (Z.ones 4) by reflexivity;
          rewrite branch_eq_U, (caa_and_ones E 43 (last sx 0) 4 E43 ltac:(lia) ltac:(lia)),
                  (U_lit E 0 ltac:(lia));
          apply Z.eqb_eq; change (2 ^ 4) with 16; exact Hl16)) as HSe. clear HSd.
  pose proof (st_ok_add_cond tfibsegs E _ _ BC_NE (SOff 38 0) (SLit 0) HSe Cm) as HSc. clear HSe.
  fsw_aj_run_to_tokU caw_tbl_ok HSc HJ HARU SHOK caw_Bspan 0x818ac.
  { caa_awr Esp. }
    { lazymatch type of HSc with st_ok _ ?EE _ _ => set (E1 := EE) in * end.
      assert (EQ : forall nn, (nn < 62)%nat -> ew E1 nn = ew E nn)
        by (intros nn Hnn; unfold E1; repeat (rewrite ew_ewset_other by lia); reflexivity).
      assert (KF : forall x : word, ~ (sp0 - 64 <= bv_unsigned x < sp0) -> ms_mem ms0 x = ms_mem ms x)
        by caa_kf HF Esp.
      assert (HB6' : caw_bytes W (ms_mem ms0) six sx)
        by (apply (cae_bytes_frame W (ms_mem ms) (ms_mem ms0) six (sp0 - 64) sp0 sx HB6 KF); lia).
      assert (HWR' : forall a, want <= a < want + Lwant ->
                       writable_at tfibsegs (mrestrict (w_H W) (ms_mem ms0)) a)
        by (intros a Ha; apply (wview_grows tfibsegs _ _ _ HG); apply HWR; exact Ha).
      destruct (caa_mkhead W E E1 ms0 _ (SOff 62 0) sx six want Lsix Lwant m HSc
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(intros nn Hnn; apply EQ; lia)
                  ltac:(unfold E1; reflexivity) E33 E34 HB6' HWR' Hsx Hlen ltac:(lia) H6lo H6hi Hmle Hwlo Hwhi
                  Hw3 Hdisj)
        as (E2 & HAG & HSN & A47 & A48 & A49 & A50 & A51 & Asx & A66 & HRG).
      apply (HCONT E2 ms0 _); [exact HAG | exact HSN | exact A47 | exact A48 | exact A49 | exact A50 | exact A51
        | exact Asx | exact A66 | exact HJ | exact HARU | | exact KF | exact HG | | | exact HWR' | exact HRG].
      - replace (six + 0) with six by lia. exact HB6'.
      - apply (cae_ra_keep W (ms_mem ms) (ms_mem ms0) six Lsix (sp0 - 64) sp0 RA6 KF);
          [lia | right; unfold kHighMemBeg in *; lia | lia | unfold CAW_CEIL in *; lia].
      - apply (cae_ra_keep W (ms_mem ms) (ms_mem ms0) want Lwant (sp0 - 64) sp0 RAW KF);
          [lia | right; unfold kHighMemBeg in *; lia | lia | unfold CAW_CEIL in *; lia]. }
- destruct (Z.eq_dec (m mod 4) 3) as [Hr3|Hr3].
  + (* r = 3 and six[m-1] land 3 = 0 *)
    assert (Hl4 : last sx 0 mod 4 = 0).
    { apply orb_true_iff in HT3 as [X|X]; [rewrite Hr3 in X; cbn in X; discriminate | apply Z.eqb_eq; exact X]. }
    pose proof (st_ok_add_cond tfibsegs E _ _ BC_NE (SAlu ALU_AND (SOff 38 0) (SLit 3)) (SLit 1) HS6
      ltac:(rewrite branch_ne_U, (cawt_and3 E 38 m E38 ltac:(lia)), (U_lit E 1 ltac:(lia));
            apply negb_true_iff, Z.eqb_neq; lia)) as HSa. clear HS6.
    pose proof (st_ok_add_cond tfibsegs E _ _ BC_EQ (SAlu ALU_AND (SOff 38 0) (SLit 3)) (SLit 3) HSa
      ltac:(rewrite branch_eq_U, (cawt_and3 E 38 m E38 ltac:(lia)), (U_lit E 3 ltac:(lia));
            apply Z.eqb_eq; exact Hr3)) as HSb. clear HSa.
    pose proof (st_ok_add_cond tfibsegs E _ _ BC_EQ (SAlu ALU_AND (SOff 43 0) (SLit 3)) (SLit 0) HSb
      ltac:(replace 3 with (Z.ones 2) by reflexivity;
            rewrite branch_eq_U, (caa_and_ones E 43 (last sx 0) 2 E43 ltac:(lia) ltac:(lia)),
                    (U_lit E 0 ltac:(lia));
            apply Z.eqb_eq; change (2 ^ 2) with 4; exact Hl4)) as HSe. clear HSb.
    pose proof (st_ok_add_cond tfibsegs E _ _ BC_NE (SOff 38 0) (SLit 0) HSe Cm) as HSc. clear HSe.
    fsw_aj_run_to_tokU caw_tbl_ok HSc HJ HARU SHOK caw_Bspan 0x818ac.
    { caa_awr Esp. }
    { lazymatch type of HSc with st_ok _ ?EE _ _ => set (E1 := EE) in * end.
      assert (EQ : forall nn, (nn < 62)%nat -> ew E1 nn = ew E nn)
        by (intros nn Hnn; unfold E1; repeat (rewrite ew_ewset_other by lia); reflexivity).
      assert (KF : forall x : word, ~ (sp0 - 64 <= bv_unsigned x < sp0) -> ms_mem ms0 x = ms_mem ms x)
        by caa_kf HF Esp.
      assert (HB6' : caw_bytes W (ms_mem ms0) six sx)
        by (apply (cae_bytes_frame W (ms_mem ms) (ms_mem ms0) six (sp0 - 64) sp0 sx HB6 KF); lia).
      assert (HWR' : forall a, want <= a < want + Lwant ->
                       writable_at tfibsegs (mrestrict (w_H W) (ms_mem ms0)) a)
        by (intros a Ha; apply (wview_grows tfibsegs _ _ _ HG); apply HWR; exact Ha).
      destruct (caa_mkhead W E E1 ms0 _ (SOff 62 0) sx six want Lsix Lwant m HSc
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(intros nn Hnn; apply EQ; lia)
                  ltac:(unfold E1; reflexivity) E33 E34 HB6' HWR' Hsx Hlen ltac:(lia) H6lo H6hi Hmle Hwlo Hwhi
                  Hw3 Hdisj)
        as (E2 & HAG & HSN & A47 & A48 & A49 & A50 & A51 & Asx & A66 & HRG).
      apply (HCONT E2 ms0 _); [exact HAG | exact HSN | exact A47 | exact A48 | exact A49 | exact A50 | exact A51
        | exact Asx | exact A66 | exact HJ | exact HARU | | exact KF | exact HG | | | exact HWR' | exact HRG].
      - replace (six + 0) with six by lia. exact HB6'.
      - apply (cae_ra_keep W (ms_mem ms) (ms_mem ms0) six Lsix (sp0 - 64) sp0 RA6 KF);
          [lia | right; unfold kHighMemBeg in *; lia | lia | unfold CAW_CEIL in *; lia].
      - apply (cae_ra_keep W (ms_mem ms) (ms_mem ms0) want Lwant (sp0 - 64) sp0 RAW KF);
          [lia | right; unfold kHighMemBeg in *; lia | lia | unfold CAW_CEIL in *; lia]. }
  + (* r = 0 *)
    assert (Hr0 : m mod 4 = 0) by (pose proof (Z.mod_pos_bound m 4 ltac:(lia)); lia).
    pose proof (st_ok_add_cond tfibsegs E _ _ BC_NE (SAlu ALU_AND (SOff 38 0) (SLit 3)) (SLit 1) HS6
      ltac:(rewrite branch_ne_U, (cawt_and3 E 38 m E38 ltac:(lia)), (U_lit E 1 ltac:(lia));
            apply negb_true_iff, Z.eqb_neq; lia)) as HSa. clear HS6.
    pose proof (st_ok_add_cond tfibsegs E _ _ BC_NE (SAlu ALU_AND (SOff 38 0) (SLit 3)) (SLit 3) HSa
      ltac:(rewrite branch_ne_U, (cawt_and3 E 38 m E38 ltac:(lia)), (U_lit E 3 ltac:(lia));
            apply negb_true_iff, Z.eqb_neq; lia)) as HSb. clear HSa.
    pose proof (st_ok_add_cond tfibsegs E _ _ BC_NE (SAlu ALU_AND (SOff 38 0) (SLit 3)) (SLit 2) HSb
      ltac:(rewrite branch_ne_U, (cawt_and3 E 38 m E38 ltac:(lia)), (U_lit E 2 ltac:(lia));
            apply negb_true_iff, Z.eqb_neq; lia)) as HSe. clear HSb.
    pose proof (st_ok_add_cond tfibsegs E _ _ BC_NE (SOff 38 0) (SLit 0) HSe Cm) as HSc. clear HSe.
    fsw_aj_run_to_tokU caw_tbl_ok HSc HJ HARU SHOK caw_Bspan 0x818ac.
    { caa_awr Esp. }
    { lazymatch type of HSc with st_ok _ ?EE _ _ => set (E1 := EE) in * end.
      assert (EQ : forall nn, (nn < 62)%nat -> ew E1 nn = ew E nn)
        by (intros nn Hnn; unfold E1; repeat (rewrite ew_ewset_other by lia); reflexivity).
      assert (KF : forall x : word, ~ (sp0 - 64 <= bv_unsigned x < sp0) -> ms_mem ms0 x = ms_mem ms x)
        by caa_kf HF Esp.
      assert (HB6' : caw_bytes W (ms_mem ms0) six sx)
        by (apply (cae_bytes_frame W (ms_mem ms) (ms_mem ms0) six (sp0 - 64) sp0 sx HB6 KF); lia).
      assert (HWR' : forall a, want <= a < want + Lwant ->
                       writable_at tfibsegs (mrestrict (w_H W) (ms_mem ms0)) a)
        by (intros a Ha; apply (wview_grows tfibsegs _ _ _ HG); apply HWR; exact Ha).
      destruct (caa_mkhead W E E1 ms0 _ (SLit 2) sx six want Lsix Lwant m HSc
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(intros nn Hnn; apply EQ; lia)
                  ltac:(unfold E1; reflexivity) E33 E34 HB6' HWR' Hsx Hlen ltac:(lia) H6lo H6hi Hmle Hwlo Hwhi
                  Hw3 Hdisj)
        as (E2 & HAG & HSN & A47 & A48 & A49 & A50 & A51 & Asx & A66 & HRG).
      apply (HCONT E2 ms0 _); [exact HAG | exact HSN | exact A47 | exact A48 | exact A49 | exact A50 | exact A51
        | exact Asx | exact A66 | exact HJ | exact HARU | | exact KF | exact HG | | | exact HWR' | exact HRG].
      - replace (six + 0) with six by lia. exact HB6'.
      - apply (cae_ra_keep W (ms_mem ms) (ms_mem ms0) six Lsix (sp0 - 64) sp0 RA6 KF);
          [lia | right; unfold kHighMemBeg in *; lia | lia | unfold CAW_CEIL in *; lia].
      - apply (cae_ra_keep W (ms_mem ms) (ms_mem ms0) want Lwant (sp0 - 64) sp0 RAW KF);
          [lia | right; unfold kHighMemBeg in *; lia | lia | unfold CAW_CEIL in *; lia]. }
Qed.

End W.
