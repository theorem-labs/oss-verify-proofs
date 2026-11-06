(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, as pa_i_region_nth over a restricted state and pa_i_field) and proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v at a0d3fb0309b (aj_intrin_at, as pa_i_memset_at: at OSet on rsegs, its post adds same_io from the contract's same_but_materialized); the rest of the file is new: the block lemma pa_int7 of LLVMFuzzerTestOneInput's shape-7 Int pod block and its helpers. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a618 for reac-pw/fuzz_headamp image A: every address relocated (role image A -> headamp image A); pp in its own env slot (atom 35, the value of the cell R+0xf0: s11 holds the input cursor here), so the entry and resume states, the shadow entry, the alias fact and the len region name atom 35 for role's 27; the cells move by the slot map (R+0xb8 -> R+0xd8, R+0xe0 -> R+0x100, R+0xe8 -> R+0x108) and the index register is a7 (role a6); pa_i_memset_at removed, the call is lib/A/HPgIntrin.v hd_memset_at; kept_run / same_io_wvb from lib/A/HPgPropKit.v / HPgSteps.v; module paths. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgPropIntB.v; 642 of its 696 lines of code are new or changed and 398 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgE01.v at a1f54c45fc22 (fuzz_role's
   image-A walk of the same prologue, unfinished there); its arithmetic and state-reading helpers are adapted
   to headamp's frame (0x1a0 -> 0x1e0, class 3 -> class 4, rh_ -> hq_, rl_ -> hd_) and renamed e01p_*; the
   three `fsd` steps, the frame call through lib/A/HPgCalls.v hc_frame_call and the walk itself are new. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address below is measured on the
   unstripped twin b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, whose loaded sections other than
   .note.gnu.build-id are byte-equal to the pin's): PART 1 of segment E01 of the walk of LLVMFuzzerTestOneInput, the prologue
   ENTRY 0x80bc0 -> 0x80c40 (the return of the class-4 frame call), lib/A/HPgE01D.v e01_pro_stmt.
   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk, part 1 of 4).

   THE CODE (capstone over the unstripped twin; lib/A/HPgE01D.v E01_TBL):
     0x80bc0 .. 0x80bf8  addi sp,sp,-0x1e0; sd zero,0(sp); the 13 saves ra, s0 .. s11 at S-8 .. S-0x68   (run P1a)
     0x80bfc .. 0x80c04  fsd fs0,0x170(sp); fsd fs1,0x168(sp); fsd fs2,0x160(sp), i.e. the three float saves at
                         S-0x70, S-0x78, S-0x80. The engine has no rule for an `fsd`: the three steps are taken
                         by lib/Reusable/YK0o.v fp_step_fsd (e01p_fsd), and the journal is carried over the
                         three writes by YCbq.ajournal_exec (their window [S-0x80, S-0x68) lies in the
                         harness's stack window).
     0x80c08 .. 0x80c3c  addi s0,sp,0x1e0 (s0 = S); andi sp,sp,-0x20 (sp = s1 = R = 32 * ((S - 0x1e0) / 32));
                         mv s2,a1 (n); the two .got words 0x9c3c8 -> 0xa4dc0 and 0x9c370 -> 0xa4db8;
                         lw a2 (the option byte, 1); ld s7 (K = SHADOW_OFF); mv s11,a0 (p);
                         `beqz a2` (not taken, the byte is 1); a0 = 0x280; jal __asan_stack_malloc_4 0x3ccac
                         with ra = 0x80c40                                                              (run P1b)
     the call itself: lib/A/HPgCalls.v hc_frame_call (YCbq aj_stack_malloc_at at class 4).
   The engine runs P1a over a single stack region [S-0x1e0, S) (so the window needs 0x1f0 + ASTACK <= LLVMF_STK)
   and P1b over four read-only regions (the two .got words and the two runtime cells they point to), so P1b
   writes no byte: the 13 saves, the three float saves and every other byte are kept across it, and the frame
   call keeps every byte at or above the allocator's ceiling outside the callee's stack (acall_kept).

   SECTION HYPOTHESES: HSTK, errno_low, ML, ASM4 (the class-4 law), HSM4, HGOT, HSC, HGU, HUC. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o YN2e YK0u.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgSegM HPgCalls HPgSteps HPgMem HPgE01D.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================== the two engine entry states ======================================== *)
(* P1a, from 0x80bc0: the stack window [S - 0x1e0, S) the prologue writes (the 13 saves and `sd zero,0(sp)`) *)
Definition e01p_p1a_rs : smem := [ YP09.mkRegion (Some 2%nat) (-0x1e0) 0 (-0x1e0) 0 [] ].
Definition e01p_p1a_facts : facts := mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) ] [] [].
Definition e01p_p1a_ss : sstate := mkSS E01_A sr_atoms e01p_p1a_rs None e01p_p1a_facts.
(* P1b, from 0x80c08: the two .got words and the two runtime cells they hold, all read-only *)
Definition e01p_p1b_rs : smem := [
  YP09.mkRegion None E01_GOT_UAR (E01_GOT_UAR + 8) 0 0 [YP09.mkChunk E01_GOT_UAR (CVal 8 (SLit E01_UAR))];
  YP09.mkRegion None E01_GOT_SH (E01_GOT_SH + 8) 0 0 [YP09.mkChunk E01_GOT_SH (CVal 8 (SLit E01_SHC))];
  YP09.mkRegion None E01_UAR (E01_UAR + 4) 0 0 [YP09.mkChunk E01_UAR (CVal 4 (SLit 1))];
  YP09.mkRegion None E01_SHC (E01_SHC + 8) 0 0 [YP09.mkChunk E01_SHC (CVal 8 (SLit SHADOW_OFF))] ].
Definition e01p_p1b_facts : facts := mkFacts [ (2%nat, mkAF (2 ^ 46 - 512) (2 ^ 47) 4) ] [] [].
Definition e01p_p1b_ss : sstate := mkSS E01_P1B sr_atoms e01p_p1b_rs None e01p_p1b_facts.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
Hypothesis HSTK : 0x1f0 + ASTACK <= LLVMF_STK.
Hypothesis errno_low : api_env rsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM4 : astack_malloc_realizes rsegs B 4.
Hypothesis HSM4 : pc_stack_malloc (as_code B) 4 = A_SM4.
Hypothesis HGOT : as_got_shadow B = E01_GOT_SH.
Hypothesis HSC : as_shadow_cell B = E01_SHC.
Hypothesis HGU : as_got_uar B = E01_GOT_UAR.
Hypothesis HUC : as_uar_cell B = E01_UAR.

(* ============================================ arithmetic ============================================ *)
Lemma e01p_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.
Lemma e01p_denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite e01p_land_m32 by lia. apply zcanon_id. unfold M64.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
Lemma e01p_denot_add0 : forall E (a : sv), sv_denot E (SAlu ALU_ADD a (SLit 0)) = sv_denot E a.
Proof.
intros E a. rewrite denot_lit_U, U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
change (zcanon 0) with 0. rewrite Z.add_0_r, Z_to_bv64_canon. unfold U. apply Z_to_bv_bv_unsigned.
Qed.
(* R = (S - 0x1e0) & -32 *)
Lemma e01p_R_range : forall Sp, Sp mod 16 = 0 -> 0x1e0 <= Sp ->
Sp - 0x1f0 <= 32 * ((Sp - 0x1e0) / 32) <= Sp - 0x1e0 /\ (32 * ((Sp - 0x1e0) / 32)) mod 32 = 0 /\
(32 * ((Sp - 0x1e0) / 32) - Sp) mod 16 = 0.
Proof.
intros Sp H16 HS. pose proof (Z.div_mod (Sp - 0x1e0) 32 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound (Sp - 0x1e0) 32 ltac:(lia)) as M.
pose proof (Z.div_mod Sp 16 ltac:(lia)) as D16.
assert (HM : (Sp - 0x1e0) mod 32 = 0 \/ (Sp - 0x1e0) mod 32 = 16).
{ pose proof (Z.div_mod (Sp - 0x1e0) 16 ltac:(lia)) as D2.
  assert (Hm16 : (Sp - 0x1e0) mod 16 = 0) by (rewrite Zminus_mod, H16; reflexivity).
  pose proof (Z.mod_pos_bound (Sp - 0x1e0) 16 ltac:(lia)).
  assert (Hq : (Sp - 0x1e0) mod 32 = (Sp - 0x1e0) mod 16 \/ (Sp - 0x1e0) mod 32 = (Sp - 0x1e0) mod 16 + 16).
  { pose proof (Z.div_mod ((Sp - 0x1e0) / 16) 2 ltac:(lia)). pose proof (Z.mod_pos_bound ((Sp - 0x1e0) / 16) 2 ltac:(lia)).
    rewrite Z.div_div in * by lia. lia. }
  lia. }
split; [lia|]. split; [rewrite Z.mul_comm, Z_mod_mult; reflexivity|].
replace (32 * ((Sp - 0x1e0) / 32) - Sp) with ((2 * ((Sp - 0x1e0) / 32) - Sp / 16) * 16) by lia.
apply Z_mod_mult.
Qed.
Lemma e01p_umod : forall (w : word), bv_unsigned w mod 2 ^ 64 = bv_unsigned w.
Proof.
intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ 64) in H.
apply Z.mod_small. exact H.
Qed.

(* ===================================== reading a run's last state ===================================== *)
Lemma e01p_reg_atom : forall H E ss ms regs0 extra (r : bv 5) n,
st_ok rsegs E ss (restrict H ms) -> E = Ereg regs0 extra -> sr_get (ss_regs ss) r = SOff n 0 -> (n < 32)%nat ->
getr (ms_regs ms) r = getr regs0 (Z_to_bv 5 (Z.of_nat n)).
Proof.
intros H E ss ms regs0 extra r n HS HE Hsr Hn.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hsr. apply bv_eq. rewrite denot_SOff, Z.add_0_r, HE.
rewrite (ew_Ereg_nat regs0 extra n (Z_to_bv 5 (Z.of_nat n))).
- apply zcanon_id. pose proof (bv_unsigned_in_range _ (getr regs0 (Z_to_bv 5 (Z.of_nat n)))) as Hb.
  change (bv_modulus 64) with (2 ^ 64) in Hb. unfold M64. lia.
- rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. change (bv_modulus 5) with 32. lia.
Qed.
Lemma e01p_reg_lit2 : forall H E ss ms (r : bv 5) z v,
st_ok rsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SLit z -> z = v -> getr (ms_regs ms) r = w64 v.
Proof.
intros H E ss ms r z v HS Hsr <-. rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hsr. reflexivity.
Qed.
Lemma e01p_reg_off : forall H E ss ms (r : bv 5) n c v,
st_ok rsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n c ->
bv_unsigned (ew E n) + c = v -> getr (ms_regs ms) r = w64 v.
Proof.
intros H E ss ms r n c v HS Hsr Hu.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hsr, denot_lit_U, U_SOff, Hu. unfold w64. apply Z_to_bv64_canon.
Qed.
Lemma e01p_reg_and : forall H E ss ms (r : bv 5) n c v,
st_ok rsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SAlu ALU_AND (SOff n c) (SLit (-32)) ->
ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
getr (ms_regs ms) r = w64 (32 * ((v + c) / 32)).
Proof.
intros H E ss ms r n c v HS Hsr Hew H1 H2 H3.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hsr.
exact (e01p_denot_and_m32 E n v c Hew H1 H2 H3).
Qed.
Lemma e01p_reg_and_add0 : forall H E ss ms (r : bv 5) n c v,
st_ok rsegs E ss (restrict H ms) ->
sr_get (ss_regs ss) r = SAlu ALU_ADD (SAlu ALU_AND (SOff n c) (SLit (-32))) (SLit 0) ->
ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
getr (ms_regs ms) r = w64 (32 * ((v + c) / 32)).
Proof.
intros H E ss ms r n c v HS Hsr Hew H1 H2 H3.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hsr, e01p_denot_add0.
exact (e01p_denot_and_m32 E n v c Hew H1 H2 H3).
Qed.
Lemma e01p_region_nth : forall (H : word -> bool) E ss ms i r,
st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
region_ok rsegs E (mrestrict H (ms_mem ms)) r.
Proof.
intros H E ss ms i r HS Hi. destruct (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma e01p_field_of_region : forall E m n b cs lo hi wlo whi od (w : N) e v,
region_ok rsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
val_mem rsegs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok rsegs E m b od w e v Hck He Hv Hw).
Qed.
(* the 13 saves, from the chunks of the stack region of P1a's last state *)
Definition e01p_cv8 (v : cval) : option nat :=
match v with
| CVal w (SOff i k) => if N.eqb w 8 && (k =? 0) then Some i else None
| _ => None
end.
Lemma e01p_cv8_ok : forall v i, e01p_cv8 v = Some i -> v = CVal 8 (SOff i 0).
Proof.
intros v i H. unfold e01p_cv8 in H.
destruct v as [w e | | |]; try discriminate. destruct e; try discriminate.
lazymatch type of H with (if N.eqb w 8 && (?k =? 0) then Some ?j else None) = Some i =>
  destruct (N.eqb_spec w 8); destruct (Z.eqb_spec k 0); cbn in H; try discriminate; injection H as <-; subst; reflexivity end.
Qed.
Definition e01p_save_ok (j : nat) (c : YP09.chunk) : bool :=
(YP09.c_off c =? -8 - 8 * Z.of_nat j) &&
match e01p_cv8 (YP09.c_val c) with
| Some i => Z.of_nat i =? bv_unsigned (nth j hq_saved_regs 0%bv)
| None => false
end.
Lemma e01p_saves_of_region : forall E (m : word -> option byte) regs0 lo hi wlo whi cs,
region_ok rsegs E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) -> E = Ereg regs0 [] ->
forallb (fun j => existsb (e01p_save_ok j) cs) (seq 0 13) = true ->
forall j, (j < 13)%nat ->
val_mem rsegs m (spZ regs0 + (-8 - 8 * Z.of_nat j)) 8 (bv_unsigned (getr regs0 (nth j hq_saved_regs 0%bv))).
Proof.
intros E m regs0 lo hi wlo whi cs Hreg HE Hck j Hj.
assert (Hin : In j (seq 0 13)) by (apply in_seq; lia).
pose proof (proj1 (forallb_forall _ _) Hck j Hin) as Hx. apply existsb_exists in Hx as ([off v] & Hc & Hok).
unfold e01p_save_ok in Hok. cbn [YP09.c_off YP09.c_val] in Hok.
apply andb_prop in Hok as [Hoff Hok]. apply Z.eqb_eq in Hoff. subst off.
destruct (e01p_cv8 v) as [i|] eqn:Ev; [|discriminate]. apply e01p_cv8_ok in Ev. subst v.
apply Z.eqb_eq in Hok. rename Hok into Hi.
assert (Hi5 : Z_to_bv 5 (Z.of_nat i) = nth j hq_saved_regs 0%bv).
{ apply bv_eq. rewrite Z_to_bv_unsigned, Hi. apply bv_wrap_small. apply bv_unsigned_in_range. }
pose proof (e01p_field_of_region E m 2 (spZ regs0) cs lo hi wlo whi (-8 - 8 * Z.of_nat j) 8 (SOff i 0)
  (bv_unsigned (getr regs0 (nth j hq_saved_regs 0%bv))) Hreg) as HF.
apply HF.
- rewrite HE, (ew_Ereg_nat regs0 [] 2 2%bv eq_refl). reflexivity.
- exact Hc.
- apply bv_eq. rewrite denot_SOff, Z.add_0_r, HE, Z_to_bv_bv_unsigned.
  assert (Hi32 : (i < 32)%nat).
  { pose proof (bv_unsigned_in_range _ (nth j hq_saved_regs 0%bv)) as Hb. change (bv_modulus 5) with 32 in Hb. lia. }
  rewrite (ew_Ereg_nat regs0 [] i (Z_to_bv 5 (Z.of_nat i))), Hi5.
  + apply zcanon_id. pose proof (bv_unsigned_in_range _ (getr regs0 (nth j hq_saved_regs 0%bv))) as Hb.
    change (bv_modulus 64) with (2 ^ 64) in Hb. unfold M64. lia.
  + rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. change (bv_modulus 5) with 32. lia.
- pose proof (bv_unsigned_in_range _ (getr regs0 (nth j hq_saved_regs 0%bv))) as Hb.
  change (bv_modulus 64) with (2 ^ 64) in Hb. exact Hb.
- cbn. lia.
Qed.
(* a byte view the engine's state gives, as a val_mem *)
Lemma e01p_vm_of_view : forall H mem a (n : nat) v,
(forall k, (k < n)%nat -> aview rsegs H mem (a + Z.of_nat k) = Some (le_byte v n k)) ->
val_mem rsegs (mrestrict H mem) a n v.
Proof.
intros H mem a n v HA k Hk. specialize (HA k Hk). unfold aview in HA.
destruct (mbyte rsegs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; [|discriminate].
cbn [option_map] in HA. injection HA as HA.
pose proof (bv_unsigned_in_range 8 b) as Rb. rewrite HA in Rb.
f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, HA. symmetry. apply bv_wrap_small. exact Rb.
Qed.
Lemma e01p_val_mem_of_rd32 : forall H mem a v,
rd32 (aview rsegs H mem) a v -> val_mem rsegs (mrestrict H mem) a 4 v.
Proof. intros H mem a v Hr. apply e01p_vm_of_view. exact Hr. Qed.
(* a run keeps every byte outside the write windows of its regions *)
Lemma e01p_keep_ro : forall E rs H (m m' : word -> option byte),
frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, ~ in_wrange E rs a) ->
forall a, aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E rs H m m' HF Hw a. unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a) (Hw _)). reflexivity.
Qed.

(* ======================================= the three float saves ======================================= *)
Definition e01p_wr (m : word -> option byte) (a : Z) (v : word) : word -> option byte :=
  wbytes m (Z_to_bv 64 a) (word_to_le_bytes 8 v).
Definition e01p_fr (r : bv 5) : word := Sem.reg_get (@fp_regs fx) r.
Definition e01p_m3 (m : word -> option byte) (Sp : Z) (f0 f1 f2 : word) : word -> option byte :=
  e01p_wr (e01p_wr (e01p_wr m (Sp - 0x70) f0) (Sp - 0x78) f1) (Sp - 0x80) f2.
Lemma e01p_getr_bv : forall (regs : bvmap 5 word) (r : bv 5) (z : Z),
  bv_unsigned r = z -> getr regs r = getr regs (Z_to_bv 5 z).
Proof. intros regs r z <-. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma e01p_cs : forall (r : bv 5) (z : Z), bv_unsigned r = z -> acallee_saved z -> acallee_saved (bv_unsigned r).
Proof. intros r z <- H. exact H. Qed.
Lemma e01p_spZ : forall (regs : bvmap 5 word) v, getr regs 2 = w64 v -> 0 <= v < 2 ^ 64 -> spZ regs = v.
Proof. intros regs v H Hv. unfold spZ. rewrite H. unfold w64. apply unsigned_lit_small. exact Hv. Qed.
Lemma e01p_vm_mod64 : forall m a v, val_mem rsegs m a 8 v -> val_mem rsegs m a 8 (v mod 2 ^ 64).
Proof.
intros m a v V k Hk. rewrite (V k Hk). do 2 f_equal.
unfold YO0f.le_byte. change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma e01p_wr_out_at : forall m a v b, 0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  (b < a \/ a + 8 <= b) -> e01p_wr m a v (Z_to_bv 64 b) = m (Z_to_bv 64 b).
Proof.
intros m a v b Ha0 Ha1 Hb Hd. unfold e01p_wr.
apply YK0u.wbytes_outside; rewrite length_N_to_le_bytes, ?unsigned_lit_small by lia; lia.
Qed.
Lemma e01p_wr_in : forall m a (v : word) k, 0 <= a -> a + 8 <= 2 ^ 64 -> (k < 8)%nat ->
  e01p_wr m a v (Z_to_bv 64 (a + Z.of_nat k)) = Some (Z_to_bv 8 (le_byte (bv_unsigned v) 8 k)).
Proof.
intros m a v k Ha0 Ha1 Hk.
assert (Hv : 0 <= bv_unsigned v < 2 ^ 64)
  by (pose proof (bv_unsigned_in_range 64 v) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr; lia).
unfold e01p_wr.
rewrite (YK0u.wbytes_inside (word_to_le_bytes 8 v) m (Z_to_bv 64 a) (Z_to_bv 64 (a + Z.of_nat k)));
  [ | rewrite length_N_to_le_bytes, unsigned_lit_small by lia; lia
  | rewrite length_N_to_le_bytes, !unsigned_lit_small by lia; lia ].
pose proof (YN2e.word_to_le_bytes_nth 8 (bv_unsigned v) k Hk Hv) as HN.
rewrite Z_to_bv_bv_unsigned in HN.
rewrite !unsigned_lit_small by lia.
replace (Z.to_nat (a + Z.of_nat k - a)) with k by lia.
f_equal. exact (nth_error_nth (word_to_le_bytes 8 v) k (Z_to_bv 8 0) HN).
Qed.
Lemma e01p_wr_grows : forall m a v, mem_grows m (e01p_wr m a v).
Proof. intros m a v. unfold e01p_wr. apply wbytes_grows. Qed.

Lemma e01p_fsd : forall (Q : world rsegs -> config -> Prop) (W : world rsegs) regs mem md
  STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc k Sp,
ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W mem md k ->
getr regs 2 = w64 (Sp - 0x1e0) ->
2 ^ 46 <= Sp <= 2 ^ 47 -> sp0 - STK <= Sp - 0x80 -> Sp <= sp0 ->
(forall a, Sp - 0x80 <= a < Sp - 0x68 -> apresent (w_H W) mem a) ->
(forall mem' md',
  ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W mem' md' k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (Sp - 0x80 <= a < Sp - 0x68) ->
     aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) ->
  (exists v0 v1 v2,
     val_mem rsegs (mrestrict (w_H W) mem') (Sp - 0x70) 8 v0 /\
     val_mem rsegs (mrestrict (w_H W) mem') (Sp - 0x78) 8 v1 /\
     val_mem rsegs (mrestrict (w_H W) mem') (Sp - 0x80) 8 v2) ->
  SRr rsegs W (cfg_at rsegs E01_P1B regs mem' md') Q) ->
SRr rsegs W (mkCfg (@mkst fx regs (Z_to_bv 64 E01_FSD) mem (seg_rom rsegs)) md) Q.
Proof.
intros Q W regs mem md STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc k Sp HJ Hsp HSp Hlo Hhi Hpres K.
assert (Hsp' : getr regs (Z_to_bv 5 2) = w64 (Sp - 0x1e0)) by exact Hsp.
(* the three stores are inside the harness's stack window, so every byte they touch is writable *)
assert (SOK : forall (mm : word -> option byte) a, mem_grows (mrestrict (w_H W) mem) mm ->
  Sp - 0x80 <= a -> a + 8 <= Sp - 0x68 -> store_ok rsegs mm (Z_to_bv 64 a) 8 = true).
{ intros mm a Hgr Ha0 Ha1. apply store_ok_of_all; [rewrite unsigned_lit_small by lia; lia|].
  intros x Hx. rewrite unsigned_lit_small in Hx by lia.
  destruct (Hpres (bv_unsigned x) ltac:(lia)) as [Hh [b Hb]].
  rewrite Z_to_bv_bv_unsigned in Hh, Hb.
  assert (Hm : mrestrict (w_H W) mem x = Some b) by (unfold mrestrict; rewrite Hh; exact Hb).
  specialize (Hgr x ltac:(rewrite Hm; discriminate)).
  unfold wview. destruct (mm x) eqn:Em; [discriminate | exfalso; exact (Hgr eq_refl)]. }
assert (GR1 : forall m a v, mem_grows m (e01p_wr m a v)) by (intros; apply e01p_wr_grows).
assert (D1 : exists w r1 r2 im, fetch_word rsegs (Z_to_bv 64 E01_FSD) = Some w /\ is_ecall w = false /\
  decode_any w = Some (FStore FMT_D r1 r2 im, 4) /\ bv_unsigned r1 = 2 /\ bv_signed im = 368).
{ do 4 eexists. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|]. split; vm_compute; reflexivity. }
destruct D1 as (w1 & a1 & b1 & i1 & F1 & E1 & Dc1 & Hu1 & Hs1).
assert (D2 : exists w r1 r2 im, fetch_word rsegs (Z_to_bv 64 0x80c00) = Some w /\ is_ecall w = false /\
  decode_any w = Some (FStore FMT_D r1 r2 im, 4) /\ bv_unsigned r1 = 2 /\ bv_signed im = 360).
{ do 4 eexists. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|]. split; vm_compute; reflexivity. }
destruct D2 as (w2 & a2 & b2 & i2 & F2 & E2 & Dc2 & Hu2 & Hs2).
assert (D3 : exists w r1 r2 im, fetch_word rsegs (Z_to_bv 64 0x80c04) = Some w /\ is_ecall w = false /\
  decode_any w = Some (FStore FMT_D r1 r2 im, 4) /\ bv_unsigned r1 = 2 /\ bv_signed im = 352).
{ do 4 eexists. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|]. split; vm_compute; reflexivity. }
destruct D3 as (w3 & a3 & b3 & i3 & F3 & E3 & Dc3 & Hu3 & Hs3).
assert (ST1 : RiscvSemantics.step rsegs (@mkst fx regs (Z_to_bv 64 E01_FSD) (mrestrict (w_H W) mem) (seg_rom rsegs))
  = MachineOk (@mkst fx regs (Z_to_bv 64 0x80c00)
      (e01p_wr (mrestrict (w_H W) mem) (Sp - 0x70) (e01p_fr b1)) (seg_rom rsegs))).
{ rewrite (YK0o.fp_step_fsd fx rsegs regs (Z_to_bv 64 E01_FSD) (mrestrict (w_H W) mem) (seg_rom rsegs)
    w1 a1 b1 i1 (Z_to_bv 64 (Sp - 0x70)) F1 E1 Dc1
    ltac:(rewrite (e01p_getr_bv regs a1 2 Hu1), Hsp', Hs1; unfold w64, v_addi;
          rewrite unsigned_lit_small by lia; f_equal; lia)
    ltac:(apply (SOK _ (Sp - 0x70) (mem_grows_refl _)); lia)).
  unfold e01p_wr, e01p_fr. reflexivity. }
assert (ST2 : RiscvSemantics.step rsegs (@mkst fx regs (Z_to_bv 64 0x80c00)
      (e01p_wr (mrestrict (w_H W) mem) (Sp - 0x70) (e01p_fr b1)) (seg_rom rsegs))
  = MachineOk (@mkst fx regs (Z_to_bv 64 0x80c04)
      (e01p_wr (e01p_wr (mrestrict (w_H W) mem) (Sp - 0x70) (e01p_fr b1)) (Sp - 0x78) (e01p_fr b2))
      (seg_rom rsegs))).
{ rewrite (YK0o.fp_step_fsd fx rsegs regs (Z_to_bv 64 0x80c00)
    (e01p_wr (mrestrict (w_H W) mem) (Sp - 0x70) (e01p_fr b1)) (seg_rom rsegs)
    w2 a2 b2 i2 (Z_to_bv 64 (Sp - 0x78)) F2 E2 Dc2
    ltac:(rewrite (e01p_getr_bv regs a2 2 Hu2), Hsp', Hs2; unfold w64, v_addi;
          rewrite unsigned_lit_small by lia; f_equal; lia)
    ltac:(apply (SOK _ (Sp - 0x78) (GR1 _ _ _)); lia)).
  unfold e01p_wr, e01p_fr. reflexivity. }
assert (ST3 : RiscvSemantics.step rsegs (@mkst fx regs (Z_to_bv 64 0x80c04)
      (e01p_wr (e01p_wr (mrestrict (w_H W) mem) (Sp - 0x70) (e01p_fr b1)) (Sp - 0x78) (e01p_fr b2))
      (seg_rom rsegs))
  = MachineOk (@mkst fx regs (Z_to_bv 64 E01_P1B)
      (e01p_m3 (mrestrict (w_H W) mem) Sp (e01p_fr b1) (e01p_fr b2) (e01p_fr b3)) (seg_rom rsegs))).
{ rewrite (YK0o.fp_step_fsd fx rsegs regs (Z_to_bv 64 0x80c04)
    (e01p_wr (e01p_wr (mrestrict (w_H W) mem) (Sp - 0x70) (e01p_fr b1)) (Sp - 0x78) (e01p_fr b2))
    (seg_rom rsegs)
    w3 a3 b3 i3 (Z_to_bv 64 (Sp - 0x80)) F3 E3 Dc3
    ltac:(rewrite (e01p_getr_bv regs a3 2 Hu3), Hsp', Hs3; unfold w64, v_addi;
          rewrite unsigned_lit_small by lia; f_equal; lia)
    ltac:(apply (SOK _ (Sp - 0x80) (mem_grows_trans _ _ _ (GR1 _ _ _) (GR1 _ _ _))); lia)).
  unfold e01p_m3, e01p_wr, e01p_fr. reflexivity. }
assert (MS : msteps rsegs (restrict (w_H W) (@mkst fx regs (Z_to_bv 64 E01_FSD) mem (seg_rom rsegs)))
  (@mkst fx regs (Z_to_bv 64 E01_P1B)
     (e01p_m3 (mrestrict (w_H W) mem) Sp (e01p_fr b1) (e01p_fr b2) (e01p_fr b3)) (seg_rom rsegs))).
{ rewrite restrict_mkst_fx.
  apply (msteps_trans rsegs _ (@mkst fx regs (Z_to_bv 64 0x80c00)
    (e01p_wr (mrestrict (w_H W) mem) (Sp - 0x70) (e01p_fr b1)) (seg_rom rsegs)) _);
  [apply msteps_one; [reflexivity | exact ST1]|].
  apply (msteps_trans rsegs _ (@mkst fx regs (Z_to_bv 64 0x80c04)
    (e01p_wr (e01p_wr (mrestrict (w_H W) mem) (Sp - 0x70) (e01p_fr b1)) (Sp - 0x78) (e01p_fr b2))
    (seg_rom rsegs)) _);
  [apply msteps_one; [reflexivity | exact ST2]|].
  apply msteps_one; [reflexivity | exact ST3]. }
assert (HSfin : st_ok rsegs (Ereg regs []) (mkSS E01_P1B sr_atoms [] None (mkFacts [] [] []))
  (@mkst fx regs (Z_to_bv 64 E01_P1B)
     (e01p_m3 (mrestrict (w_H W) mem) Sp (e01p_fr b1) (e01p_fr b2) (e01p_fr b3)) (seg_rom rsegs))).
{ apply (entry_st_ok_full rsegs); [apply regs_ok_Ereg | reflexivity | constructor | exact I | repeat split]. }
apply (SRr_msteps_st rsegs HPgSteps.img_wx W (Ereg regs []) _ _ _ md Q MS HSfin).
intros ms' mat' HS2 Hkl Hkh Hreg.
assert (HNW : forall x : word, w_H W x = true -> ~ (Sp - 0x80 <= bv_unsigned x < Sp - 0x68)).
{ intros x Hx Hr. destruct (Hpres (bv_unsigned x) Hr) as [Hh _]. rewrite Z_to_bv_bv_unsigned in Hh.
  rewrite Hh in Hx. discriminate. }
assert (OUT : forall (mm : word -> option byte) (x : word), ~ (Sp - 0x80 <= bv_unsigned x < Sp - 0x68) ->
  e01p_m3 mm Sp (e01p_fr b1) (e01p_fr b2) (e01p_fr b3) x = mm x).
{ intros mm x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). unfold e01p_m3.
  rewrite !e01p_wr_out_at by (pose proof (bv_unsigned_in_range 64 x) as Hr;
    change (bv_modulus 64) with (2 ^ 64) in Hr; rewrite ?Z_to_bv_bv_unsigned; lia).
  reflexivity. }
assert (EM : forall x : word, mrestrict (w_H W) (ms_mem ms') x
  = e01p_m3 (mrestrict (w_H W) mem) Sp (e01p_fr b1) (e01p_fr b2) (e01p_fr b3) x).
{ intros x. destruct (w_H W x) eqn:Hx.
  - unfold mrestrict at 1. rewrite Hx. symmetry. rewrite OUT by (apply HNW; exact Hx).
    unfold mrestrict. rewrite Hx. reflexivity.
  - unfold mrestrict at 1. rewrite Hx. rewrite (Hkl x Hx). cbn [ms_mem mkst]. reflexivity. }
assert (EMf : mrestrict (w_H W) (ms_mem ms')
  = e01p_m3 (mrestrict (w_H W) mem) Sp (e01p_fr b1) (e01p_fr b2) (e01p_fr b3))
  by (apply functional_extensionality; exact EM).
assert (GR : mem_grows (mrestrict (w_H W) mem)
  (e01p_m3 (mrestrict (w_H W) mem) Sp (e01p_fr b1) (e01p_fr b2) (e01p_fr b3))).
{ unfold e01p_m3. eapply mem_grows_trans; [|apply GR1]. eapply mem_grows_trans; [|apply GR1]. apply GR1. }
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (Sp - 0x80 <= a < Sp - 0x68) ->
  aview rsegs (w_H W) (ms_mem ms') a = aview rsegs (w_H W) mem a).
{ intros a Ha Hn. unfold aview, mbyte. rewrite EMf. unfold e01p_m3.
  rewrite !e01p_wr_out_at by lia. reflexivity. }
assert (HJ' : ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W (ms_mem ms')
  (with_vm_backing (m_vm_lazy md) mat' md) k).
{ apply (ajournal_exec rsegs B (AR_laws_ok rsegs B) HPgSteps.img_segs_low STK sp0 FP ly S0 W0 mem0 md0 own
    lyc Sc W mem md k (ms_mem ms') (with_vm_backing (m_vm_lazy md) mat' md)
    (fun a => Sp - 0x80 <= a < Sp - 0x68) HJ).
  - intros x Hw. rewrite EMf. apply OUT. exact Hw.
  - rewrite EMf. exact GR.
  - intros x Hx. rewrite (Hkh x Hx). reflexivity.
  - apply same_but_materialized_wvb_any.
  - intros a Ha. unfold awr_byte. left. lia. }
assert (V0 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms')) (Sp - 0x70) 8 (bv_unsigned (e01p_fr b1))).
{ intros kk Hk. unfold mbyte. rewrite EMf. unfold e01p_m3.
  rewrite (e01p_wr_out_at _ (Sp - 0x80) (e01p_fr b3) (Sp - 0x70 + Z.of_nat kk)) by lia.
  rewrite (e01p_wr_out_at _ (Sp - 0x78) (e01p_fr b2) (Sp - 0x70 + Z.of_nat kk)) by lia.
  rewrite (e01p_wr_in _ (Sp - 0x70) (e01p_fr b1) kk) by lia. reflexivity. }
assert (V1 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms')) (Sp - 0x78) 8 (bv_unsigned (e01p_fr b2))).
{ intros kk Hk. unfold mbyte. rewrite EMf. unfold e01p_m3.
  rewrite (e01p_wr_out_at _ (Sp - 0x80) (e01p_fr b3) (Sp - 0x78 + Z.of_nat kk)) by lia.
  rewrite (e01p_wr_in _ (Sp - 0x78) (e01p_fr b2) kk) by lia. reflexivity. }
assert (V2 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms')) (Sp - 0x80) 8 (bv_unsigned (e01p_fr b3))).
{ intros kk Hk. unfold mbyte. rewrite EMf. unfold e01p_m3.
  rewrite (e01p_wr_in _ (Sp - 0x80) (e01p_fr b3) kk) by lia. reflexivity. }
rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms' HS2 eq_refl). cbn [ss_pc]. rewrite Hreg. cbn [ms_regs mkst].
apply (K (ms_mem ms') (with_vm_backing (m_vm_lazy md) mat' md) HJ' KEEP).
exists (bv_unsigned (e01p_fr b1)), (bv_unsigned (e01p_fr b2)), (bv_unsigned (e01p_fr b3)).
split; [exact V0|]. split; [exact V1 | exact V2].
Qed.

(* ========================================= the two entry states ========================================= *)
Lemma e01p_p1a_entry : forall (W : world rsegs) regs mem,
(forall a, spZ regs - 0x1e0 <= a < spZ regs -> apresent (w_H W) mem a) ->
2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
st_ok rsegs (Ereg regs []) e01p_p1a_ss (restrict (w_H W) (@mkst fx regs (Z_to_bv 64 E01_A) mem (seg_rom rsegs))).
Proof.
intros W regs mem Hpres Hsp Hal.
rewrite restrict_mkst_fx.
set (E := Ereg regs []).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
unfold e01p_p1a_ss. apply (entry_st_ok_full rsegs); change (Ereg regs []) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold e01p_p1a_rs. apply Forall_cons; [|apply Forall_nil].
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable rsegs). apply Hpres. lia.
- apply pairwise_disjoint_of_extents. cbn. tauto.
- split; [|split; [exact I | exact I]]. cbn [e01p_p1a_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp. change (2 ^ 4) with 16. repeat split; lia.
Qed.
Lemma e01p_p1b_entry : forall (W : world rsegs) regs mem,
2 ^ 46 - 512 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
rdword (aview rsegs (w_H W) mem) E01_GOT_UAR = Some E01_UAR ->
rdword (aview rsegs (w_H W) mem) E01_GOT_SH = Some E01_SHC ->
rd32 (aview rsegs (w_H W) mem) E01_UAR 1 ->
rdword (aview rsegs (w_H W) mem) E01_SHC = Some SHADOW_OFF ->
st_ok rsegs (Ereg regs []) e01p_p1b_ss (restrict (w_H W) (@mkst fx regs (Z_to_bv 64 E01_P1B) mem (seg_rom rsegs))).
Proof.
intros W regs mem Hsp Hal K1 K2 K3 K4.
rewrite restrict_mkst_fx.
set (E := Ereg regs []).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
unfold e01p_p1b_ss. apply (entry_st_ok_full rsegs); change (Ereg regs []) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold e01p_p1b_rs. repeat apply Forall_cons; try apply Forall_nil;
  unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + split; [unfold E01_GOT_UAR; lia|]. split; [unfold E01_GOT_UAR; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. rewrite <- (Z.add_0_l E01_GOT_UAR) at 1.
    apply (chunk_ok_val rsegs E _ 0 E01_GOT_UAR 8 (SLit E01_UAR) E01_UAR); [reflexivity | unfold E01_UAR; zside | zside |].
    exact (val_mem_of_rdword rsegs (w_H W) mem _ _ K1).
  + split; [unfold E01_GOT_SH; lia|]. split; [unfold E01_GOT_SH; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. rewrite <- (Z.add_0_l E01_GOT_SH) at 1.
    apply (chunk_ok_val rsegs E _ 0 E01_GOT_SH 8 (SLit E01_SHC) E01_SHC); [reflexivity | unfold E01_SHC; zside | zside |].
    exact (val_mem_of_rdword rsegs (w_H W) mem _ _ K2).
  + split; [unfold E01_UAR; lia|]. split; [unfold E01_UAR; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. rewrite <- (Z.add_0_l E01_UAR) at 1.
    apply (chunk_ok_val rsegs E _ 0 E01_UAR 4 (SLit 1) 1); [reflexivity | zside | zside |].
    exact (e01p_val_mem_of_rd32 (w_H W) mem E01_UAR 1 K3).
  + split; [unfold E01_SHC; lia|]. split; [unfold E01_SHC; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. rewrite <- (Z.add_0_l E01_SHC) at 1.
    apply (chunk_ok_val rsegs E _ 0 E01_SHC 8 (SLit SHADOW_OFF) SHADOW_OFF); [reflexivity | unfold SHADOW_OFF; zside | zside |].
    exact (val_mem_of_rdword rsegs (w_H W) mem _ _ K4).
- apply pairwise_disjoint_of_extents.
  unfold e01p_p1b_rs, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  unfold E01_GOT_UAR, E01_GOT_SH, E01_UAR, E01_SHC.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]]. cbn [e01p_p1b_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp. change (2 ^ 4) with 16. repeat split; lia.
Qed.

(* ===================================== the class-4 frame call ===================================== *)
Lemma e01p_call : forall (hx : hq_hcx rsegs) (regsT : bvmap 5 word) (memT : word -> option byte) (mdT : Model) (R : Z),
@hq_base rc rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx ->
@hq_j rc SK rsegs B LLVMF_STK hx [] (h_ly rsegs hx) (h_S rsegs hx) (h_W rsegs hx) memT mdT 0 ->
R = 32 * ((spZ (h_regs rsegs hx) - 0x1e0) / 32) ->
getr regsT 1 = w64 RA_SM4 -> getr regsT 2 = w64 R ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 8 = w64 (spZ (h_regs rsegs hx)) -> getr regsT 9 = w64 R ->
getr regsT 18 = w64 (h_n rsegs hx) -> getr regsT 23 = w64 SHADOW_OFF ->
getr regsT 27 = w64 (h_p rsegs hx) ->
(forall j, (j < 13)%nat -> val_mem rsegs (mrestrict (w_H (h_W rsegs hx)) memT)
   (spZ (h_regs rsegs hx) + (-8 - 8 * Z.of_nat j)) 8
   (bv_unsigned (getr (h_regs rsegs hx) (nth j hq_saved_regs 0%bv)))) ->
(exists v0 v1 v2,
   val_mem rsegs (mrestrict (w_H (h_W rsegs hx)) memT) (spZ (h_regs rsegs hx) - 0x70) 8 v0 /\
   val_mem rsegs (mrestrict (w_H (h_W rsegs hx)) memT) (spZ (h_regs rsegs hx) - 0x78) 8 v1 /\
   val_mem rsegs (mrestrict (w_H (h_W rsegs hx)) memT) (spZ (h_regs rsegs hx) - 0x80) 8 v2) ->
SRr rsegs (h_W rsegs hx) (cfg_at rsegs A_SM4 regsT memT mdT) (@e01_at_fr fx rc SK B LLVMF_STK hx).
Proof.
intros hx regsT memT mdT R HB HJ HR Hr1 Hr2 Hr3 Hr4 Hr8 Hr9 Hr18 Hr23 Hr27 HSAV HFS.
pose proof HB as (HPRE & _ & _ & _ & _ & _ & _ & Hfr0 & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (YM05.alloc_ceiling_val) as Hceilv.
assert (HASTK : ASTACK = 16384) by reflexivity. rewrite HASTK in HSTK.
assert (Hsp46 : 2 ^ 46 <= spZ (h_regs rsegs hx) <= 2 ^ 47) by lia.
destruct (e01p_R_range (spZ (h_regs rsegs hx)) Hal16 ltac:(lia)) as (HRr & HR32 & HR16).
rewrite <- HR in HRr, HR32, HR16.
apply (hc_frame_call rsegs B HPgSteps.img_segs_low errno_low ML ASM4 HSM4
  (@e01_at_fr fx rc SK B LLVMF_STK hx) (h_W rsegs hx) regsT memT
  LLVMF_STK (spZ (h_regs rsegs hx)) [] (h_ly rsegs hx) (h_S rsegs hx) (h_W rsegs hx) (h_mem rsegs hx)
  (h_md rsegs hx) [] (h_ly rsegs hx) (h_S rsegs hx) mdT 0 (R - spZ (h_regs rsegs hx)) HJ).
- unfold spZ. rewrite Hr2. unfold w64. rewrite unsigned_lit_small by lia. lia.
- exact HR16.
- lia.
- unfold ESTACK. lia.
- exact Hr3.
- exact Hr4.
- exact Hr1.
- exact Hfr0.
- intros S2 regs2 mem2 md2 pos HJ2 Hpres2 H10 Hbl Hfr2 Hnev Hbb Hz Hflag Hkept.
  apply SRr_ret.
  exists pos,
    (HDEnv (spZ (h_regs rsegs hx)) R (frame_addr (h_ly rsegs hx) HQ_CID pos) 0 0 0 0 0 0 0 0 0 0),
    (h_ly rsegs hx), S2, regs2, mem2, md2.
  split; [reflexivity|].
  assert (CS : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr regsT r).
  { intros r Hr. pose proof (Hpres2 (bv_unsigned r) Hr) as X. rewrite Z_to_bv_bv_unsigned in X. exact X. }
  assert (FIN : In (HQ_CID, pos) (frames S2)) by (rewrite Hfr2; left; reflexivity).
  destruct (al_flag _ _ LAWS (h_ly rsegs hx) S2 (h_W rsegs hx) mem2 md2 HQ_CID pos (proj1 HJ2) FIN)
    as (_ & _ & Hfapp & Hflt).
  destruct Hfapp as (Hf0 & _).
  assert (FLG : val_mem rsegs (mrestrict (w_H (h_W rsegs hx)) mem2)
    (frame_addr (h_ly rsegs hx) HQ_CID pos + HC_FLAG) 8 (flag_addr (h_ly rsegs hx) HQ_CID pos))
    by exact (val_mem_of_rdword rsegs (w_H (h_W rsegs hx)) mem2 _ _ Hflag).
  (* what the call keeps: every byte at or above the ceiling outside [R - ESTACK, R) *)
  pose proof Hkept as (K1 & _).
  assert (KV : forall a (n : nat) v, alloc_ceiling <= a -> a + Z.of_nat n <= spZ (h_regs rsegs hx) ->
     R <= a \/ spZ (h_regs rsegs hx) - 0x80 <= a ->
     val_mem rsegs (mrestrict (w_H (h_W rsegs hx)) memT) a n v ->
     val_mem rsegs (mrestrict (w_H (h_W rsegs hx)) mem2) a n v).
  { intros a n v Ha0 Ha1 Ha2 HV.
    apply (val_mem_kept rsegs (w_H (h_W rsegs hx)) (w_H (h_W rsegs hx)) memT mem2 a n v); [|exact HV].
    intros kk Hkk. apply K1; unfold ESTACK in *; lia. }
  split; [exact HJ2|].
  split; [exact Hbl|].
  split; [unfold hq_geo; cbn [e_S e_R e_F]; split; [reflexivity|]; split; [exact HR | reflexivity]|].
  split; [cbn [e_R]; rewrite (CS 2%bv (e01p_cs 2%bv 2 ltac:(vm_compute; reflexivity)
    ltac:(unfold acallee_saved; lia))); exact Hr2|].
  split; [rewrite (CS 3%bv (e01p_cs 3%bv 3 ltac:(vm_compute; reflexivity)
    ltac:(unfold acallee_saved; lia))); exact Hr3|].
  split; [rewrite (CS 4%bv (e01p_cs 4%bv 4 ltac:(vm_compute; reflexivity)
    ltac:(unfold acallee_saved; lia))); exact Hr4|].
  split; [cbn [e_S]; rewrite (CS 8%bv (e01p_cs 8%bv 8 ltac:(vm_compute; reflexivity)
    ltac:(unfold acallee_saved; lia))); exact Hr8|].
  split; [cbn [e_R]; rewrite (CS 9%bv (e01p_cs 9%bv 9 ltac:(vm_compute; reflexivity)
    ltac:(unfold acallee_saved; lia))); exact Hr9|].
  split; [cbn [e_F]; exact H10|].
  split; [rewrite (CS 18%bv (e01p_cs 18%bv 18 ltac:(vm_compute; reflexivity)
    ltac:(unfold acallee_saved; lia))); exact Hr18|].
  split; [rewrite (CS 23%bv (e01p_cs 23%bv 23 ltac:(vm_compute; reflexivity)
    ltac:(unfold acallee_saved; lia))); exact Hr23|].
  split; [rewrite (CS 27%bv (e01p_cs 27%bv 27 ltac:(vm_compute; reflexivity)
    ltac:(unfold acallee_saved; lia))); exact Hr27|].
  split; [cbn [e_F]; exact (hm_fsh_zero rsegs (w_H (h_W rsegs hx)) mem2 _ Hz)|].
  unfold hq_kept, hq_cells, hq_saves_L, hq_fsaves. split.
  + apply Forall_app. split.
    * apply Forall_forall. intros f Hf. apply in_map_iff in Hf as (j & <- & Hj). apply in_seq in Hj.
      cbn [fst snd hd_at hd_xv e_S]. rewrite e01p_umod.
      apply KV; [lia | lia | right; lia |]. apply HSAV. lia.
    * constructor; [|constructor]. cbn [fst snd hd_at hd_xv e_F]. rewrite Z.add_0_r.
      rewrite (Z.mod_small (flag_addr (h_ly rsegs hx) HQ_CID pos) (2 ^ 64)) by lia.
      change HQ_FLAG with HC_FLAG. exact FLG.
  + destruct HFS as (v0 & v1 & v2 & HV0 & HV1 & HV2).
    exists v0, v1, v2. cbn [hd_at hd_xv e_S].
    replace (spZ (h_regs rsegs hx) + -0x70) with (spZ (h_regs rsegs hx) - 0x70) by lia.
    replace (spZ (h_regs rsegs hx) + -0x78) with (spZ (h_regs rsegs hx) - 0x78) by lia.
    replace (spZ (h_regs rsegs hx) + -0x80) with (spZ (h_regs rsegs hx) - 0x80) by lia.
    split; [apply e01p_vm_mod64; apply KV; [lia | lia | right; lia | exact HV0]|].
    split; [apply e01p_vm_mod64; apply KV; [lia | lia | right; lia | exact HV1]|].
    apply e01p_vm_mod64. apply KV; [lia | lia | right; lia | exact HV2].
Qed.

(* ========================================= the prologue ========================================= *)
Theorem e01_pro_ok : @e01_pro_stmt fx rc SK B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
unfold e01_pro_stmt. intros hx HB.
pose proof HB as (HPRE & Hra & Hp & Hn & Hpn & Hnl & Hpl & Hfr0 & Hev & Hlive & HROD).
clear Hpn Hnl Hpl Hev Hlive HROD Hra.
pose proof HPRE as (HAR & Hra1 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
clear HAR Hra1 Hra4 Hch HQT.
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
clear Hbot Htop Htop2.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof HPgSteps.img_wx as Hwx.
pose proof HPgSteps.img_segs_low as Hsegs.
assert (HASTK : ASTACK = 16384) by reflexivity. rewrite HASTK in HSTK.
assert (Hsp46 : 2 ^ 46 <= spZ (h_regs rsegs hx) <= 2 ^ 47) by lia.
pose proof (ajournal_init rsegs B LLVMF_STK [] (h_ly rsegs hx) (h_S rsegs hx) (h_W rsegs hx)
  (h_regs rsegs hx) (h_mem rsegs hx) (h_md rsegs hx) [] HPRE) as HJ.
assert (Hpres1 : forall a, spZ (h_regs rsegs hx) - 0x1e0 <= a < spZ (h_regs rsegs hx) ->
  apresent (w_H (h_W rsegs hx)) (h_mem rsegs hx) a) by (intros a Ha; apply Hpres; lia).
pose proof (e01p_p1a_entry (h_W rsegs hx) (h_regs rsegs hx) (h_mem rsegs hx) Hpres1 Hsp46 Hal16) as HS.
unfold cfg_at. change (w64 HQ_ENTRY) with (Z_to_bv 64 E01_A).
(* ---- P1a: 0x80bc0 .. 0x80bfc ---- *)
aj_run_to E01_TBL_ok HS HJ E01_FSD.
{ lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end.
  eapply awr_ok_cons_stack;
  [reflexivity | rewrite (ew_Ereg_nat (h_regs rsegs hx) _ 2 2%bv eq_refl); reflexivity
  | cbn; lia | cbn; lia | apply awr_ok_nil]. }
rename ms into ms1, HS into HS1, HJ into HJ1, HF into HF1, HFr into HFr1, HG into HG1.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres1 & _).
assert (R2 : getr (ms_regs ms1) 2 = w64 (spZ (h_regs rsegs hx) - 0x1e0)).
{ eapply (e01p_reg_off (w_H (h_W rsegs hx)) _ _ ms1 2%bv 2 (-0x1e0));
  [exact HS1 | vm_compute; reflexivity
  | rewrite (ew_Ereg_nat (h_regs rsegs hx) [] 2 2%bv eq_refl); unfold spZ; lia]. }
pose proof (HPgSteps.regs_kept_of_st_ok rsegs _ _ ms1 (h_regs rsegs hx) [] (w_H (h_W rsegs hx)) [2%bv]
  HS1 (env_agree_refl 32 _) ltac:(vm_compute; reflexivity)) as KR1.
assert (SAV1 : forall j, (j < 13)%nat -> val_mem rsegs (mrestrict (w_H (h_W rsegs hx)) (ms_mem ms1))
  (spZ (h_regs rsegs hx) + (-8 - 8 * Z.of_nat j)) 8
  (bv_unsigned (getr (h_regs rsegs hx) (nth j hq_saved_regs 0%bv)))).
{ lazymatch type of HS1 with st_ok _ _ ?ss _ =>
  let r := eval vm_compute in (nth_error (ss_mem ss) 0) in
  lazymatch r with Some ?rg =>
  apply (e01p_saves_of_region _ (mrestrict (w_H (h_W rsegs hx)) (ms_mem ms1)) (h_regs rsegs hx) _ _ _ _ _
    (e01p_region_nth (w_H (h_W rsegs hx)) _ _ ms1 0 rg HS1 ltac:(vm_compute; reflexivity)) eq_refl);
  vm_compute; reflexivity end end. }
rewrite (st_ok_restrict_mkst rsegs (w_H (h_W rsegs hx)) _ _ ms1 HS1 eq_refl). cbn [ss_pc].
(* ---- the three `fsd` ---- *)
apply (e01p_fsd _ (h_W rsegs hx) (ms_regs ms1) (ms_mem ms1) _
  LLVMF_STK (spZ (h_regs rsegs hx)) [] (h_ly rsegs hx) (h_S rsegs hx) (h_W rsegs hx) (h_mem rsegs hx)
  (h_md rsegs hx) [] (h_ly rsegs hx) (h_S rsegs hx) 0 (spZ (h_regs rsegs hx)) HJ1 R2 Hsp46
  ltac:(lia) ltac:(lia) ltac:(intros a Ha; apply HJpres1; lia)).
intros mem2 md2 HJ2 KEEP2 HFS2.
assert (SAV2 : forall j, (j < 13)%nat -> val_mem rsegs (mrestrict (w_H (h_W rsegs hx)) mem2)
  (spZ (h_regs rsegs hx) + (-8 - 8 * Z.of_nat j)) 8
  (bv_unsigned (getr (h_regs rsegs hx) (nth j hq_saved_regs 0%bv)))).
{ intros j Hj. apply (val_mem_kept rsegs (w_H (h_W rsegs hx)) (w_H (h_W rsegs hx)) (ms_mem ms1) mem2 _ 8 _);
  [intros kk Hkk; apply KEEP2; lia | exact (SAV1 j Hj)]. }
(* ---- P1b: 0x80c08 .. the `jal` 0x80c3c ---- *)
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ2)) as (Kc & Ku & Kg & Kgu).
rewrite HSC in Kc. rewrite HUC in Ku. rewrite HGOT, HSC in Kg. rewrite HGU, HUC in Kgu.
assert (Hsp2 : spZ (ms_regs ms1) = spZ (h_regs rsegs hx) - 0x1e0).
{ apply (e01p_spZ _ _ R2). lia. }
pose proof (e01p_p1b_entry (h_W rsegs hx) (ms_regs ms1) mem2
  ltac:(rewrite Hsp2; lia) ltac:(rewrite Hsp2; rewrite Zminus_mod, Hal16; reflexivity) Kgu Kg Ku Kc) as HS.
clear Kc Ku Kg Kgu.
unfold cfg_at.
aj_run_to E01_TBL_ok HS HJ2 A_SM4.
{ lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
rename ms into ms3, HS into HS3, HJ2 into HJ3, HF into HF3, HFr into HFr3, HG into HG3.
assert (NW : forall a, ~ in_wrange (Ereg (ms_regs ms1) []) e01p_p1b_rs a).
{ intros a (r & Hin & Ha). unfold e01p_p1b_rs in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|]). destruct Hin. }
assert (KEEP3 : forall a, aview rsegs (w_H (h_W rsegs hx)) (ms_mem ms3) a = aview rsegs (w_H (h_W rsegs hx)) mem2 a)
  by (intros a; exact (e01p_keep_ro _ _ _ _ _ HFr3 NW a)).
(* ---- the registers at the `jal` ---- *)
pose proof (HPgSteps.regs_kept_of_st_ok rsegs _ _ ms3 (ms_regs ms1) [] (w_H (h_W rsegs hx))
  [1%bv; 2%bv; 8%bv; 9%bv; 10%bv; 11%bv; 12%bv; 18%bv; 23%bv; 27%bv]
  HS3 (env_agree_refl 32 _) ltac:(vm_compute; reflexivity)) as KR3.
assert (U2 : ew (Ereg (ms_regs ms1) []) 2 = Z_to_bv 64 (spZ (h_regs rsegs hx) - 0x1e0)).
{ rewrite (ew_Ereg_nat (ms_regs ms1) [] 2 2%bv eq_refl), R2. reflexivity. }
assert (G1 : getr (ms_regs ms3) 1 = w64 RA_SM4).
{ exact (e01p_reg_lit2 _ _ _ ms3 1%bv _ RA_SM4 HS3 ltac:(vm_compute; reflexivity) eq_refl). }
assert (G2 : getr (ms_regs ms3) 2 = w64 (32 * ((spZ (h_regs rsegs hx) - 0x1e0 + 0) / 32))).
{ eapply (e01p_reg_and (w_H (h_W rsegs hx)) _ _ ms3 2%bv 2 0 (spZ (h_regs rsegs hx) - 0x1e0));
  [exact HS3 | vm_compute; reflexivity | exact U2 | lia | lia | lia]. }
rewrite Z.add_0_r in G2.
assert (G9 : getr (ms_regs ms3) 9 = w64 (32 * ((spZ (h_regs rsegs hx) - 0x1e0 + 0) / 32))).
{ eapply (e01p_reg_and_add0 (w_H (h_W rsegs hx)) _ _ ms3 9%bv 2 0 (spZ (h_regs rsegs hx) - 0x1e0));
  [exact HS3 | vm_compute; reflexivity | exact U2 | lia | lia | lia]. }
rewrite Z.add_0_r in G9.
assert (G8 : getr (ms_regs ms3) 8 = w64 (spZ (h_regs rsegs hx))).
{ eapply (e01p_reg_off (w_H (h_W rsegs hx)) _ _ ms3 8%bv 2 480);
  [exact HS3 | vm_compute; reflexivity | rewrite U2, unsigned_lit_small by lia; lia]. }
assert (G23 : getr (ms_regs ms3) 23 = w64 SHADOW_OFF).
{ exact (e01p_reg_lit2 _ _ _ ms3 23%bv _ SHADOW_OFF HS3 ltac:(vm_compute; reflexivity) eq_refl). }
assert (G3 : getr (ms_regs ms3) 3 = w64 (as_gp B)).
{ rewrite (e01p_reg_atom (w_H (h_W rsegs hx)) _ _ ms3 (ms_regs ms1) [] 3%bv 3 HS3 eq_refl
    ltac:(vm_compute; reflexivity) ltac:(lia)).
  rewrite KR1 by (vm_compute; first [discriminate | intros [Hq|[]]; discriminate Hq]). exact Hgp. }
assert (G4 : getr (ms_regs ms3) 4 = w64 (as_tp B)).
{ rewrite (e01p_reg_atom (w_H (h_W rsegs hx)) _ _ ms3 (ms_regs ms1) [] 4%bv 4 HS3 eq_refl
    ltac:(vm_compute; reflexivity) ltac:(lia)).
  rewrite KR1 by (vm_compute; first [discriminate | intros [Hq|[]]; discriminate Hq]). exact Htp. }
assert (G18 : getr (ms_regs ms3) 18 = w64 (h_n rsegs hx)).
{ rewrite (e01p_reg_atom (w_H (h_W rsegs hx)) _ _ ms3 (ms_regs ms1) [] 18%bv 11 HS3 eq_refl
    ltac:(vm_compute; reflexivity) ltac:(lia)).
  rewrite KR1 by (vm_compute; first [discriminate | intros [Hq|[]]; discriminate Hq]). exact Hn. }
assert (G27 : getr (ms_regs ms3) 27 = w64 (h_p rsegs hx)).
{ rewrite (e01p_reg_atom (w_H (h_W rsegs hx)) _ _ ms3 (ms_regs ms1) [] 27%bv 10 HS3 eq_refl
    ltac:(vm_compute; reflexivity) ltac:(lia)).
  rewrite KR1 by (vm_compute; first [discriminate | intros [Hq|[]]; discriminate Hq]). exact Hp. }
(* ---- the call ---- *)
rewrite (st_ok_restrict_mkst rsegs (w_H (h_W rsegs hx)) _ _ ms3 HS3 eq_refl). cbn [ss_pc].
apply (e01p_call hx (ms_regs ms3) (ms_mem ms3) _ (32 * ((spZ (h_regs rsegs hx) - 0x1e0) / 32))
  HB HJ3 eq_refl G1 G2 G3 G4 G8 G9 G18 G23 G27).
- intros j Hj. apply (val_mem_kept rsegs (w_H (h_W rsegs hx)) (w_H (h_W rsegs hx)) mem2 (ms_mem ms3) _ 8 _);
  [intros kk Hkk; apply KEEP3 | exact (SAV2 j Hj)].
- destruct HFS2 as (v0 & v1 & v2 & HV0 & HV1 & HV2). exists v0, v1, v2.
  split; [apply (val_mem_kept rsegs (w_H (h_W rsegs hx)) (w_H (h_W rsegs hx)) mem2 (ms_mem ms3) _ 8 _);
    [intros kk Hkk; apply KEEP3 | exact HV0]|].
  split; [apply (val_mem_kept rsegs (w_H (h_W rsegs hx)) (w_H (h_W rsegs hx)) mem2 (ms_mem ms3) _ 8 _);
    [intros kk Hkk; apply KEEP3 | exact HV1]|].
  apply (val_mem_kept rsegs (w_H (h_W rsegs hx)) (w_H (h_W rsegs hx)) mem2 (ms_mem ms3) _ 8 _);
    [intros kk Hkk; apply KEEP3 | exact HV2].
Qed.

End s.

Print Assumptions e01_pro_ok.
