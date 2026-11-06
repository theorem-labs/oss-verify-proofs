(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, as pa_i_region_nth over a restricted state and pa_i_field) and proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v at a0d3fb0309b (aj_intrin_at, as pa_i_memset_at: at OSet on rsegs, its post adds same_io from the contract's same_but_materialized); the rest of the file is new: the block lemma pa_int7 of LLVMFuzzerTestOneInput's shape-7 Int pod block and its helpers. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a618 for reac-pw/fuzz_headamp image A: every address relocated (role image A -> headamp image A); pp in its own env slot (atom 35, the value of the cell R+0xf0: s11 holds the input cursor here), so the entry and resume states, the shadow entry, the alias fact and the len region name atom 35 for role's 27; the cells move by the slot map (R+0xb8 -> R+0xd8, R+0xe0 -> R+0x100, R+0xe8 -> R+0x108) and the index register is a7 (role a6); pa_i_memset_at removed, the call is lib/A/HPgIntrin.v hd_memset_at; kept_run / same_io_wvb from lib/A/HPgPropKit.v / HPgSteps.v; module paths. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgPropIntB.v; 586 of its 649 lines of code are new or changed and 389 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgE01.v at 800a94bc01d1 (the arithmetic, register and save readers, the P1a / P1b entries), proofs/reac-pw/fuzz_role/lib/A/RPgCheckStr.v at 77f59d02b018 (field_of_region, st_ok_region_nth) and proofs/reac-pw/fuzz_headamp/lib/A/HPgCalls.v at 0b1fb19172b (hc_frame_call); restated at image B's pcs, frame size 0x220, cells and class-4 call, with the four float saves stepped by YK0o.fp_step_fsd. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address below is measured on the
   unstripped twin 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): part 1 of segment E01 of the walk of LLVMFuzzerTestOneInput (0x80c40), the prologue,
   ENTRY 0x80c40 -> 0x80cc4 (the return of the class-4 frame call): lib/AU/HPgE01D.v e01u_pro_stmt. Proves no
   function (kind: segment lemma of LLVMFuzzerTestOneInput's walk, segment E01 of image B, its part 1).

   THE CODE (capstone over the pinned file; lib/AU/HPgE01D.v E01U_TBL):
     0x80c40 .. 0x80c78  addi sp,sp,-0x220; sd zero,0(sp); the 13 saves ra, s0 .. s11 at S - 8 .. S - 0x68
                         (`sd ra,0x218(sp)` .. `sd s11,0x1b8(sp)`)                                   (run P1a)
     0x80c7c .. 0x80c88  fsd fs0,0x1b0(sp); fsd fs1,0x1a8(sp); fsd fs2,0x1a0(sp); fsd fs3,0x198(sp), i.e. the
                         four float saves at S - 0x70, S - 0x78, S - 0x80, S - 0x88: the engine has no rule for
                         `fsd`, so e1p_fsd4 steps the four by YK0o.fp_step_fsd and keeps the journal by
                         YCbq.ajournal_exec over the stack window [S - 0x88, S - 0x68)
     0x80c8c .. 0x80cc0  addi s0,sp,0x220; andi sp,sp,-32; mv s1,sp; mv s4,a1; the .got words 0x9c848 (the option
                         word's address 0xa5240) and 0x9c7f0 (the shadow offset's cell 0xa5238); lw a2 (the option
                         word, 1); ld s11 (K); mv s2,a0; beqz a2 (not taken); li a0,0x3a0; jal 0x3cd2c, ra = 0x80cc4
                         (run P1b: it writes no memory)
     0x3cd2c             the class-4 frame function: YCbq.aj_stack_malloc_at at cid 4 over the class-4 law ASM4
                         (e1p_frame_call, the image-B twin of image A's HPgCalls.hc_frame_call).
   At 0x80cc4: the journal from the entry with own = [(4, pos)] and no event, the entry's blocks, the geometry (S the
   entry sp, R = 32 * ((S - 0x220) / 32), F = frame_addr ly 4 pos), sp = s1 = R, gp, tp, s0 = S, a0 = F, s2 = p,
   s4 = n, s11 = K, the frame's 128 shadow bytes 0, and the carried cells (the 13 saves, the flag-pointer word
   F + 0x3f8, the four float saves): e01u_fr_facts.

   SECTION HYPOTHESES of e01u_pro_ok: HSTK (the harness's stack budget), errno_low (api_env), ML (model_laws),
   ASM4 (the class-4 law), HSM4 (the symbol record's class-4 entry 0x3cd2c), HGOT / HSC / HGU / HUC (the symbol
   record's .got words and runtime cells). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q YG05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o YN2e YK0u YK0e.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSegM HPgSteps HPgMem HPgE01D.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================== arithmetic ======================================== *)
Lemma e1p_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.
(* R = (S - 0x220) & -32 *)
Lemma e1p_denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite e1p_land_m32 by lia. apply zcanon_id. unfold M64.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
Lemma e1p_U_m32 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
YP0e.U E (SAlu ALU_AND (SOff n 0) (SLit (-32))) = 32 * (v / 32).
Proof.
intros E n v Hn Hv. unfold YP0e.U. rewrite (e1p_denot_and_m32 E n v 0 Hn) by lia. rewrite Z.add_0_r.
apply unsigned_lit_small. split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le v 32 ltac:(lia)). lia.
Qed.
Lemma e1p_U_add0 : forall E a, YP0e.U E (SAlu ALU_ADD a (SLit 0)) = YP0e.U E a.
Proof.
intros E a. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. change (zcanon 0) with 0. rewrite Z.add_0_r.
apply zcanon_id. apply U_range.
Qed.
Lemma e1p_R_range : forall S, S mod 16 = 0 -> 0x220 <= S ->
S - 0x230 <= 32 * ((S - 0x220) / 32) <= S - 0x220 /\ (32 * ((S - 0x220) / 32)) mod 32 = 0 /\
(32 * ((S - 0x220) / 32) - S) mod 16 = 0.
Proof.
intros S H16 HS. pose proof (Z.div_mod (S - 0x220) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (S - 0x220) 32 ltac:(lia)) as M.
pose proof (Z.div_mod S 16 ltac:(lia)) as D16.
assert (HM : (S - 0x220) mod 32 = 0 \/ (S - 0x220) mod 32 = 16).
{ pose proof (Z.div_mod (S - 0x220) 16 ltac:(lia)) as D2.
  assert (Hm16 : (S - 0x220) mod 16 = 0) by (rewrite Zminus_mod, H16; reflexivity).
  pose proof (Z.mod_pos_bound (S - 0x220) 16 ltac:(lia)).
  assert (Hq : (S - 0x220) mod 32 = (S - 0x220) mod 16 \/ (S - 0x220) mod 32 = (S - 0x220) mod 16 + 16).
  { pose proof (Z.div_mod ((S - 0x220) / 16) 2 ltac:(lia)). pose proof (Z.mod_pos_bound ((S - 0x220) / 16) 2 ltac:(lia)).
    rewrite Z.div_div in * by lia. lia. }
  lia. }
split; [lia|]. split; [rewrite Z.mul_comm, Z_mod_mult; reflexivity|].
replace (32 * ((S - 0x220) / 32) - S) with ((2 * ((S - 0x220) / 32) - S / 16) * 16) by lia.
apply Z_mod_mult.
Qed.
Lemma e1p_umod : forall w : word, bv_unsigned w mod 2 ^ 64 = bv_unsigned w.
Proof.
intros w. apply Z.mod_small. pose proof (bv_unsigned_in_range _ w) as Hb.
change (bv_modulus 64) with (2 ^ 64) in Hb. exact Hb.
Qed.
Lemma e1p_ret_ok : forall ret, 0 <= ret < 2 ^ 64 -> ret mod 2 = 0 -> YK0s.ret_ok (w64 ret).
Proof. intros ret Hr He. apply YK0s.ret_ok_even. unfold w64. rewrite unsigned_lit_small by exact Hr. exact He. Qed.
Lemma e1p_frames4 : 0 < fs_frames 4.
Proof. vm_compute. reflexivity. Qed.

(* ======================================== memory cells ======================================== *)
Section rd. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* a 4-byte cell read as rd32 *)
Lemma e1p_val_mem_of_rd32 : forall H mem a v, 0 <= v < 2 ^ 32 ->
rd32 (aview rsegs H mem) a v -> val_mem rsegs (mrestrict H mem) a 4 v.
Proof.
intros H mem a v Hv Hr k Hk. specialize (Hr k Hk).
unfold aview in Hr. destruct (mbyte rsegs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; [|discriminate].
cbn [option_map] in Hr. injection Hr as Hr. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
lazymatch goal with |- _ = bv_wrap _ ?x => change x with (YG0f.le_byte v 4 k) end. rewrite <- Hr.
symmetry. apply bv_wrap_small. pose proof (bv_unsigned_in_range 8 b) as R. exact R.
Qed.
Lemma e1p_val_mem_mod64 : forall m a v, val_mem rsegs m a 8 v -> val_mem rsegs m a 8 (v mod 2 ^ 64).
Proof.
intros m a v V k Hk. rewrite (V k Hk). unfold YO0f.le_byte. change (8 * Z.of_nat 8) with 64.
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma e1p_vm_at : forall m a b n v, a = b -> val_mem rsegs m a n v -> val_mem rsegs m b n v.
Proof. intros m a b n v -> V. exact V. Qed.
(* the four float stores: a byte outside a store is the memory's before it, a byte inside is the stored word's *)
Lemma e1p_wb_out : forall (m : word -> option byte) a (bs : list byte) (x : word),
length bs = 8%nat -> 0 <= a -> a + 8 <= 2 ^ 64 ->
bv_unsigned x < a \/ a + 8 <= bv_unsigned x ->
wbytes m (Z_to_bv 64 a) bs x = m x.
Proof.
intros m a bs x Hl H0 H1 Hx. apply YK0u.wbytes_outside; rewrite unsigned_lit_small by lia; rewrite Hl;
change (Z.of_nat 8) with 8; lia.
Qed.
Lemma e1p_wb_hit : forall (m : word -> option byte) a (w : word) (k : nat),
0 <= a -> a + 8 <= 2 ^ 64 -> (k < 8)%nat ->
wbytes m (Z_to_bv 64 a) (word_to_le_bytes 8 w) (Z_to_bv 64 (a + Z.of_nat k)) =
Some (Z_to_bv 8 (YO0f.le_byte (bv_unsigned w) 8 k)).
Proof.
intros m a w k H0 H1 Hk.
pose proof (YK0e.AX2S.wbytes_nth (word_to_le_bytes 8 w) m (Z_to_bv 64 a) k) as X.
rewrite length_N_to_le_bytes, unsigned_lit_small in X by lia.
change (Z.of_nat 8) with 8 in X.
rewrite X by lia. f_equal. apply nth_error_nth.
assert (Hw : 0 <= bv_unsigned w < 2 ^ 64).
{ pose proof (bv_unsigned_in_range _ w) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb. exact Hb. }
pose proof (YN2e.word_to_le_bytes_nth 8 (bv_unsigned w) k Hk Hw) as Y.
rewrite Z_to_bv_bv_unsigned in Y. exact Y.
Qed.
Lemma e1p_vm_hit : forall (mL : word -> option byte) (H : word -> bool) (mem' : word -> option byte) a (w : word),
0 <= a -> a + 8 <= 2 ^ 64 ->
(forall k, (k < 8)%nat -> H (Z_to_bv 64 (a + Z.of_nat k)) = false /\
  mem' (Z_to_bv 64 (a + Z.of_nat k)) = wbytes mL (Z_to_bv 64 a) (word_to_le_bytes 8 w) (Z_to_bv 64 (a + Z.of_nat k))) ->
val_mem rsegs (mrestrict H mem') a 8 (bv_unsigned w).
Proof.
intros mL H mem' a w H0 H1 Hb k Hk. destruct (Hb k Hk) as [Hh Hm].
unfold YP09.mbyte, mrestrict. rewrite Hh, Hm, e1p_wb_hit by lia. reflexivity.
Qed.
End rd.

(* ================================ reading a run's last state ================================ *)
Section rdst. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma e1p_reg_of : forall H E ss ms (r : bv 5) e v,
st_ok rsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = e -> YP0e.U E e = v -> getr (ms_regs ms) r = w64 v.
Proof. intros H E ss ms r e v HS He Hv. rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), He, denot_lit_U, Hv. reflexivity. Qed.
(* a register the state holds as an entry atom *)
Lemma e1p_reg_atom : forall H E ss ms regs0 extra (r : bv 5) n,
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
Lemma e1p_st_ok_region_nth : forall H E ss ms i r,
st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r -> region_ok rsegs E (mrestrict H (ms_mem ms)) r.
Proof.
intros H E ss ms i r HS Hi. destruct (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma e1p_field_of_region : forall E m n b cs lo hi wlo whi od (w : N) e v,
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
Definition e1p_cv8 (v : cval) : option nat :=
match v with
| CVal w (SOff i k) => if N.eqb w 8 && (k =? 0) then Some i else None
| _ => None
end.
Lemma e1p_cv8_ok : forall v i, e1p_cv8 v = Some i -> v = CVal 8 (SOff i 0).
Proof.
intros v i H. unfold e1p_cv8 in H.
destruct v as [w e | | |]; try discriminate. destruct e; try discriminate.
lazymatch type of H with (if N.eqb w 8 && (?k =? 0) then Some ?j else None) = Some i =>
  destruct (N.eqb_spec w 8); destruct (Z.eqb_spec k 0); cbn in H; try discriminate; injection H as <-; subst; reflexivity end.
Qed.
Definition e1p_save_ok (j : nat) (c : YP09.chunk) : bool :=
(YP09.c_off c =? -8 - 8 * Z.of_nat j) &&
match e1p_cv8 (YP09.c_val c) with
| Some i => Z.of_nat i =? bv_unsigned (nth j hqu_saved_regs 0%bv)
| None => false
end.
Lemma e1p_saves_of_region : forall E (m : word -> option byte) regs0 lo hi wlo whi cs,
region_ok rsegs E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) -> E = Ereg regs0 [] ->
forallb (fun j => existsb (e1p_save_ok j) cs) (seq 0 13) = true ->
forall j, (j < 13)%nat ->
val_mem rsegs m (spZ regs0 + (-8 - 8 * Z.of_nat j)) 8 (bv_unsigned (getr regs0 (nth j hqu_saved_regs 0%bv))).
Proof.
intros E m regs0 lo hi wlo whi cs Hreg HE Hck j Hj.
assert (Hin : In j (seq 0 13)) by (apply in_seq; lia).
pose proof (proj1 (forallb_forall _ _) Hck j Hin) as Hx. apply existsb_exists in Hx as ([off v] & Hc & Hok).
unfold e1p_save_ok in Hok. cbn [YP09.c_off YP09.c_val] in Hok.
apply andb_prop in Hok as [Hoff Hok]. apply Z.eqb_eq in Hoff. subst off.
destruct (e1p_cv8 v) as [i|] eqn:Ev; [|discriminate]. apply e1p_cv8_ok in Ev. subst v.
apply Z.eqb_eq in Hok. rename Hok into Hi.
assert (Hi5 : Z_to_bv 5 (Z.of_nat i) = nth j hqu_saved_regs 0%bv).
{ apply bv_eq. rewrite Z_to_bv_unsigned, Hi. apply bv_wrap_small. apply bv_unsigned_in_range. }
pose proof (e1p_field_of_region E m 2 (spZ regs0) cs lo hi wlo whi (-8 - 8 * Z.of_nat j) 8 (SOff i 0)
  (bv_unsigned (getr regs0 (nth j hqu_saved_regs 0%bv))) Hreg) as HF.
apply HF.
- rewrite HE, (ew_Ereg_nat regs0 [] 2 2%bv eq_refl). reflexivity.
- exact Hc.
- apply bv_eq. rewrite denot_SOff, Z.add_0_r, HE, Z_to_bv_bv_unsigned.
  assert (Hi32 : (i < 32)%nat).
  { pose proof (bv_unsigned_in_range _ (nth j hqu_saved_regs 0%bv)) as Hb. change (bv_modulus 5) with 32 in Hb. lia. }
  rewrite (ew_Ereg_nat regs0 [] i (Z_to_bv 5 (Z.of_nat i))), Hi5.
  + apply zcanon_id. pose proof (bv_unsigned_in_range _ (getr regs0 (nth j hqu_saved_regs 0%bv))) as Hb.
    change (bv_modulus 64) with (2 ^ 64) in Hb. unfold M64. lia.
  + rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. change (bv_modulus 5) with 32. lia.
- pose proof (bv_unsigned_in_range _ (getr regs0 (nth j hqu_saved_regs 0%bv))) as Hb.
  change (bv_modulus 64) with (2 ^ 64) in Hb. exact Hb.
- cbn. lia.
Qed.
End rdst.

(* the carried cells from the 13 saves, the flag-pointer word and the four float saves *)
Section kept. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma e1p_kept_of : forall (hx : hqu_hcx rsegs) pos e (W' : world rsegs) mem' regs' v0 v1 v2 v3,
(forall j, (j < 13)%nat -> val_mem rsegs (mrestrict (w_H W') mem') (e_S e + (-8 - 8 * Z.of_nat j)) 8
  (bv_unsigned (getr (hu_regs rsegs hx) (nth j hqu_saved_regs 0%bv)))) ->
val_mem rsegs (mrestrict (w_H W') mem') (e_F e + HQU_FLAG) 8 (flag_addr (hu_ly rsegs hx) HQU_CID pos) ->
val_mem rsegs (mrestrict (w_H W') mem') (e_S e - 0x70) 8 v0 ->
val_mem rsegs (mrestrict (w_H W') mem') (e_S e - 0x78) 8 v1 ->
val_mem rsegs (mrestrict (w_H W') mem') (e_S e - 0x80) 8 v2 ->
val_mem rsegs (mrestrict (w_H W') mem') (e_S e - 0x88) 8 v3 ->
hqu_kept rsegs hx pos e W' mem' regs'.
Proof.
intros hx pos e W' mem' regs' v0 v1 v2 v3 HS HFl F0 F1 F2 F3. unfold hqu_kept, hqu_cells, hqu_saves_L, hqu_fsaves.
split.
- apply Forall_app. split.
  + apply Forall_forall. intros f Hf. apply in_map_iff in Hf as (j & <- & Hj). apply in_seq in Hj.
    cbn [fst snd hd_at hd_xv]. rewrite e1p_umod. apply HS. lia.
  + constructor; [|constructor]. cbn [fst snd hd_at hd_xv]. rewrite Z.add_0_r. apply e1p_val_mem_mod64. exact HFl.
- exists v0, v1, v2, v3. cbn [hd_at hd_xv].
  split; [apply e1p_val_mem_mod64; apply (e1p_vm_at _ (e_S e - 0x70)); [lia | exact F0]|].
  split; [apply e1p_val_mem_mod64; apply (e1p_vm_at _ (e_S e - 0x78)); [lia | exact F1]|].
  split; [apply e1p_val_mem_mod64; apply (e1p_vm_at _ (e_S e - 0x80)); [lia | exact F2]|].
  apply e1p_val_mem_mod64; apply (e1p_vm_at _ (e_S e - 0x88)); [lia | exact F3].
Qed.
End kept.

(* ======================================== the run P1a ========================================
   The entry: the stack window [S - 0x220, S) the prologue writes (`sd zero,0(sp)` at S - 0x220, the 13 saves). *)
Definition e1p_p1a_rs : smem := [ YP09.mkRegion (Some 2%nat) (-0x220) 0 (-0x220) 0 [] ].
Definition e1p_p1a_facts : facts := mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) ] [] [].
Definition e1p_p1a_ss : sstate := mkSS E01U_A sr_atoms e1p_p1a_rs None e1p_p1a_facts.
(* ======================================== the run P1b ========================================
   From 0x80c8c with sp = S - 0x220 (atom 2): the two .got words and the two runtime cells they point to (AR's
   const law: the shadow offset's cell holds K, the option word's cell holds 1). P1b writes no memory. *)
Definition e1p_p1b_rs : smem := [
  YP09.mkRegion None E01U_GOT_UAR (E01U_GOT_UAR + 8) 0 0 [YP09.mkChunk E01U_GOT_UAR (CVal 8 (SLit E01U_UAR))];
  YP09.mkRegion None E01U_GOT_SH (E01U_GOT_SH + 8) 0 0 [YP09.mkChunk E01U_GOT_SH (CVal 8 (SLit E01U_SHC))];
  YP09.mkRegion None E01U_UAR (E01U_UAR + 4) 0 0 [YP09.mkChunk E01U_UAR (CVal 4 (SLit 1))];
  YP09.mkRegion None E01U_SHC (E01U_SHC + 8) 0 0 [YP09.mkChunk E01U_SHC (CVal 8 (SLit SHADOW_OFF))] ].
Definition e1p_p1b_facts : facts := mkFacts [ (2%nat, mkAF (2 ^ 46 - 0x220) (2 ^ 47) 4) ] [] [].
Definition e1p_p1b_ss : sstate := mkSS E01U_P1B sr_atoms e1p_p1b_rs None e1p_p1b_facts.
(* the state after the four float stores, before the entry state of P1b is built *)
Definition e1p_emp_ss : sstate := mkSS E01U_P1B sr_atoms [] None (mkFacts [] [] []).

Section en. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma e1p_p1a_entry : forall (W : world rsegs) regs mem,
(forall a, spZ regs - 0x220 <= a < spZ regs -> apresent (w_H W) mem a) ->
2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
st_ok rsegs (Ereg regs []) e1p_p1a_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 E01U_A) mem (seg_rom rsegs))).
Proof.
intros W regs mem Hpres Hsp Hal.
rewrite restrict_mkst_fx.
set (E := Ereg regs []).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
unfold e1p_p1a_ss. apply (entry_st_ok_full rsegs); change (Ereg regs []) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold e1p_p1a_rs. apply Forall_cons; [|apply Forall_nil].
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable rsegs). apply Hpres. lia.
- apply pairwise_disjoint_of_extents. cbn. tauto.
- split; [|split; [exact I | exact I]]. cbn [e1p_p1a_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp. change (2 ^ 4) with 16. repeat split; lia.
Qed.
Lemma e1p_p1b_entry : forall (W : world rsegs) regs mem,
2 ^ 46 - 0x220 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
rdword (aview rsegs (w_H W) mem) E01U_GOT_UAR = Some E01U_UAR ->
rdword (aview rsegs (w_H W) mem) E01U_GOT_SH = Some E01U_SHC ->
rd32 (aview rsegs (w_H W) mem) E01U_UAR 1 ->
rdword (aview rsegs (w_H W) mem) E01U_SHC = Some SHADOW_OFF ->
st_ok rsegs (Ereg regs []) e1p_p1b_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 E01U_P1B) mem (seg_rom rsegs))).
Proof.
intros W regs mem Hsp Hal K1 K2 K3 K4.
rewrite restrict_mkst_fx.
set (E := Ereg regs []).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
unfold e1p_p1b_ss. apply (entry_st_ok_full rsegs); change (Ereg regs []) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold e1p_p1b_rs. repeat apply Forall_cons; try apply Forall_nil;
  unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + split; [unfold E01U_GOT_UAR; lia|]. split; [unfold E01U_GOT_UAR; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. rewrite <- (Z.add_0_l E01U_GOT_UAR) at 1.
    apply (chunk_ok_val rsegs E _ 0 E01U_GOT_UAR 8 (SLit E01U_UAR) E01U_UAR); [reflexivity | unfold E01U_UAR; zside | zside |].
    exact (val_mem_of_rdword rsegs (w_H W) mem _ _ K1).
  + split; [unfold E01U_GOT_SH; lia|]. split; [unfold E01U_GOT_SH; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. rewrite <- (Z.add_0_l E01U_GOT_SH) at 1.
    apply (chunk_ok_val rsegs E _ 0 E01U_GOT_SH 8 (SLit E01U_SHC) E01U_SHC); [reflexivity | unfold E01U_SHC; zside | zside |].
    exact (val_mem_of_rdword rsegs (w_H W) mem _ _ K2).
  + split; [unfold E01U_UAR; lia|]. split; [unfold E01U_UAR; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. rewrite <- (Z.add_0_l E01U_UAR) at 1.
    apply (chunk_ok_val rsegs E _ 0 E01U_UAR 4 (SLit 1) 1); [reflexivity | zside | zside |].
    exact (e1p_val_mem_of_rd32 (w_H W) mem E01U_UAR 1 ltac:(lia) K3).
  + split; [unfold E01U_SHC; lia|]. split; [unfold E01U_SHC; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. rewrite <- (Z.add_0_l E01U_SHC) at 1.
    apply (chunk_ok_val rsegs E _ 0 E01U_SHC 8 (SLit SHADOW_OFF) SHADOW_OFF); [reflexivity | unfold SHADOW_OFF; zside | zside |].
    exact (val_mem_of_rdword rsegs (w_H W) mem _ _ K4).
- apply pairwise_disjoint_of_extents.
  unfold e1p_p1b_rs, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  unfold E01U_GOT_UAR, E01U_GOT_SH, E01U_UAR, E01U_SHC.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [|split; [exact I | exact I]]. cbn [e1p_p1b_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp. change (2 ^ 4) with 16. repeat split; lia.
Qed.
Lemma e1p_emp_st_ok : forall regs pcw m, pcw = Z_to_bv 64 E01U_P1B ->
st_ok rsegs (Ereg regs []) e1p_emp_ss (mkst regs pcw m (seg_rom rsegs)).
Proof.
intros regs pcw m ->. unfold e1p_emp_ss. apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- reflexivity.
- apply Forall_nil.
- exact I.
- split; [exact I | split; exact I].
Qed.
End en.

(* ======================================== the four float saves, 0x80c7c .. 0x80c88 ========================================
   `fsd fs0,0x1b0(sp)`, `fsd fs1,0x1a8(sp)`, `fsd fs2,0x1a0(sp)`, `fsd fs3,0x198(sp)` with sp = sp0 - 0x220: four
   steps of YK0o.fp_step_fsd (the engine has no rule for `fsd`). The journal is kept by ajournal_exec: the stores
   write only [sp0 - 0x88, sp0 - 0x68), inside the stack window. *)
Lemma e1p_getr_eq : forall (regs : bvmap 5 word) (r r' : bv 5), bv_unsigned r = bv_unsigned r' -> getr regs r = getr regs r'.
Proof. intros regs r r' H. assert (E : r = r') by (apply bv_eq; exact H). rewrite E. reflexivity. Qed.
(* the decoder's fields are taken as it returns them (their bit-vector proofs are its own) *)
Ltac e1p_dec := lazymatch goal with |- ?l = _ =>
  let v := eval vm_compute in l in transitivity v; [vm_compute; reflexivity | reflexivity] end.
(* the store's address: sp = sp0 - 0x220 plus the decoded offset *)
Ltac e1p_addr Hsp off := lazymatch goal with |- v_addi (getr ?rg ?r) (bv_signed ?i) = _ =>
  rewrite (e1p_getr_eq rg r (Z_to_bv 5 2) eq_refl), Hsp;
  replace (bv_signed i) with off by (vm_compute; reflexivity) end;
  unfold w64; rewrite YCbn.v_addi_lit; f_equal; lia.
Section fsd. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.

Lemma e1p_fsd4 : forall (W : world rsegs) regs mem md (Q : world rsegs -> config -> Prop)
STK sp0 FP ly S W0 mem0 md0 own lyc Sc k,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
getr regs (Z_to_bv 5 2) = w64 (sp0 - 0x220) -> 0x88 <= STK -> 0x220 <= sp0 -> sp0 <= 2 ^ 64 ->
(forall a, sp0 - 0x88 <= a < sp0 - 0x68 -> apresent (w_H W) mem a) ->
(forall mem' X,
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' (with_vm_backing (m_vm_lazy md) X md) k ->
 (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 0x88 <= a < sp0 - 0x68) ->
  aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) ->
 (exists v0 v1 v2 v3,
  val_mem rsegs (mrestrict (w_H W) mem') (sp0 - 0x70) 8 v0 /\
  val_mem rsegs (mrestrict (w_H W) mem') (sp0 - 0x78) 8 v1 /\
  val_mem rsegs (mrestrict (w_H W) mem') (sp0 - 0x80) 8 v2 /\
  val_mem rsegs (mrestrict (w_H W) mem') (sp0 - 0x88) 8 v3) ->
 SRr rsegs W (cfg_at rsegs E01U_P1B regs mem' (with_vm_backing (m_vm_lazy md) X md)) Q) ->
SRr rsegs W (cfg_at rsegs E01U_FSD regs mem md) Q.
Proof.
intros W regs mem md Q STK sp0 FP ly S W0 mem0 md0 own lyc Sc k HJ Hsp Hstk Hs0 Hs1 Hpres K.
assert (SO : forall a, sp0 - 0x88 <= a -> a + 8 <= sp0 - 0x68 ->
  store_ok rsegs (mrestrict (w_H W) mem) (Z_to_bv 64 a) 8 = true).
{ intros a Ha1 Ha2. apply store_ok_of_all; [rewrite unsigned_lit_small by lia; change (Z.of_nat 8) with 8; lia |].
  intros x Hx. rewrite unsigned_lit_small in Hx by lia. change (Z.of_nat 8) with 8 in Hx.
  pose proof (apresent_writable rsegs (w_H W) mem (bv_unsigned x) (Hpres (bv_unsigned x) ltac:(lia))) as Hw.
  unfold writable_at in Hw. rewrite Z_to_bv_bv_unsigned in Hw. exact Hw. }
unfold cfg_at at 1.
eapply (SRr_msteps_st rsegs img_wx W (Ereg regs []) e1p_emp_ss _ _ md Q).
- rewrite restrict_mkst_fx.
  eapply msteps_trans.
  { apply msteps_one; [reflexivity|].
    eapply (YK0o.fp_step_fsd fx rsegs regs _ _ _ (Z_to_bv 32 444676135) _ _ _ (Z_to_bv 64 (sp0 - 0x70)));
    [ vm_compute; reflexivity | vm_compute; reflexivity | e1p_dec | e1p_addr Hsp 432 | apply SO; lia ]. }
  eapply msteps_trans.
  { apply msteps_one; [reflexivity|].
    eapply (YK0o.fp_step_fsd fx rsegs regs _ _ _ (Z_to_bv 32 445723687) _ _ _ (Z_to_bv 64 (sp0 - 0x78)));
    [ vm_compute; reflexivity | vm_compute; reflexivity | e1p_dec | e1p_addr Hsp 424
    | apply (store_ok_mono rsegs 8 (mrestrict (w_H W) mem)); [apply wbytes_grows | apply SO; lia] ]. }
  eapply msteps_trans.
  { apply msteps_one; [reflexivity|].
    eapply (YK0o.fp_step_fsd fx rsegs regs _ _ _ (Z_to_bv 32 455159847) _ _ _ (Z_to_bv 64 (sp0 - 0x80)));
    [ vm_compute; reflexivity | vm_compute; reflexivity | e1p_dec | e1p_addr Hsp 416
    | apply (store_ok_mono rsegs 8 (mrestrict (w_H W) mem));
      [exact (mem_grows_trans _ _ _ (wbytes_grows _ _ _) (wbytes_grows _ _ _)) | apply SO; lia] ]. }
  apply msteps_one; [reflexivity|].
  eapply (YK0o.fp_step_fsd fx rsegs regs _ _ _ (Z_to_bv 32 422657063) _ _ _ (Z_to_bv 64 (sp0 - 0x88)));
  [ vm_compute; reflexivity | vm_compute; reflexivity | e1p_dec | e1p_addr Hsp 408
  | apply (store_ok_mono rsegs 8 (mrestrict (w_H W) mem));
    [exact (mem_grows_trans _ _ _ (mem_grows_trans _ _ _ (wbytes_grows _ _ _) (wbytes_grows _ _ _)) (wbytes_grows _ _ _))
    | apply SO; lia] ].
- apply e1p_emp_st_ok. vm_compute. reflexivity.
- intros ms' mat' HS2 Hlo Hhi Hreg.
  cbn [ms_mem ms_regs mkst] in Hlo, Hhi, Hreg.
  assert (KM : forall x : word, ~ (sp0 - 0x88 <= bv_unsigned x < sp0 - 0x68) ->
    mrestrict (w_H W) (ms_mem ms') x = mrestrict (w_H W) mem x).
  { intros x Hx. pose proof (bv_unsigned_in_range _ x) as Hxr. change (bv_modulus 64) with (2 ^ 64) in Hxr.
    unfold mrestrict. destruct (w_H W x) eqn:Hh; [reflexivity|]. rewrite (Hlo x Hh).
    rewrite !e1p_wb_out by (first [apply length_N_to_le_bytes | lia]).
    unfold mrestrict. rewrite Hh. reflexivity. }
  assert (HJ' : ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms')
    (with_vm_backing (m_vm_lazy md) mat' md) k).
  { apply (ajournal_exec rsegs B (AR_laws_ok rsegs B) img_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k
      (ms_mem ms') _ (fun a => sp0 - 0x88 <= a < sp0 - 0x68) HJ).
    - exact KM.
    - intros x. unfold mrestrict. destruct (w_H W x) eqn:Hh; intros Hx; [exact Hx|].
      rewrite (Hlo x Hh). cbv iota.
      refine (wbytes_grows _ _ _ x _). refine (wbytes_grows _ _ _ x _). refine (wbytes_grows _ _ _ x _).
      refine (wbytes_grows _ _ _ x _). unfold mrestrict. rewrite Hh. exact Hx.
    - intros x Hh. rewrite (Hhi x Hh). reflexivity.
    - apply same_but_materialized_wvb_any.
    - intros a Ha. left. lia. }
  assert (Hkeep : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 0x88 <= a < sp0 - 0x68) ->
    aview rsegs (w_H W) (ms_mem ms') a = aview rsegs (w_H W) mem a).
  { intros a Ha Hn. apply aview_eq_of. apply KM. rewrite unsigned_lit_small by exact Ha. exact Hn. }
  assert (Hv : exists v0 v1 v2 v3,
    val_mem rsegs (mrestrict (w_H W) (ms_mem ms')) (sp0 - 0x70) 8 v0 /\
    val_mem rsegs (mrestrict (w_H W) (ms_mem ms')) (sp0 - 0x78) 8 v1 /\
    val_mem rsegs (mrestrict (w_H W) (ms_mem ms')) (sp0 - 0x80) 8 v2 /\
    val_mem rsegs (mrestrict (w_H W) (ms_mem ms')) (sp0 - 0x88) 8 v3).
  { do 4 eexists. split; [|split; [|split]].
    - eapply e1p_vm_hit; [lia | lia |]. intros k' Hk'.
      destruct (Hpres (sp0 - 0x70 + Z.of_nat k') ltac:(lia)) as [Hh _]. split; [exact Hh|]. rewrite (Hlo _ Hh).
      rewrite !e1p_wb_out by (first [apply length_N_to_le_bytes | lia | (rewrite unsigned_lit_small by lia; lia)]).
      reflexivity.
    - eapply e1p_vm_hit; [lia | lia |]. intros k' Hk'.
      destruct (Hpres (sp0 - 0x78 + Z.of_nat k') ltac:(lia)) as [Hh _]. split; [exact Hh|]. rewrite (Hlo _ Hh).
      rewrite !e1p_wb_out by (first [apply length_N_to_le_bytes | lia | (rewrite unsigned_lit_small by lia; lia)]).
      reflexivity.
    - eapply e1p_vm_hit; [lia | lia |]. intros k' Hk'.
      destruct (Hpres (sp0 - 0x80 + Z.of_nat k') ltac:(lia)) as [Hh _]. split; [exact Hh|]. rewrite (Hlo _ Hh).
      rewrite !e1p_wb_out by (first [apply length_N_to_le_bytes | lia | (rewrite unsigned_lit_small by lia; lia)]).
      reflexivity.
    - eapply e1p_vm_hit; [lia | lia |]. intros k' Hk'.
      destruct (Hpres (sp0 - 0x88 + Z.of_nat k') ltac:(lia)) as [Hh _]. split; [exact Hh|]. rewrite (Hlo _ Hh).
      reflexivity. }
  rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms' HS2 eq_refl), Hreg.
  exact (K (ms_mem ms') mat' HJ' Hkeep Hv).
Qed.
End fsd.

(* ======================================== the class-4 frame request at 0x80cc0 ========================================
   From the `jal` 0x80cc0 (pc = 0x3cd2c, ra = 0x80cc4) with no frame held yet: the request returns at 0x80cc4 with
   a0 = F, the class-4 frame at some position pos, held by the harness's journal from here on; its 1024 bytes'
   shadow all 0; its last word, F + 0x3f8, holds the flag byte's address; the blocks, events and live bytes as
   before; every byte at or above the allocator's ceiling outside the request's stack as before (acall_kept).
   The image-B twin of image A's lib/A/HPgCalls.v hc_frame_call: lib/Reusable/YCbq.v's aj_stack_malloc_at at
   cid 4, with the segments' bound img_segs_low and the kernel's stack_malloc_progress (YG05). *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
Hypothesis HSTK : 0x230 + ASTACK <= LLVMF_STK.
Hypothesis errno_low : api_env rsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM4 : astack_malloc_realizes rsegs B 4.
Hypothesis HSM4 : pc_stack_malloc (as_code B) 4 = E01U_SM4.
(* the symbol record's cells and code entries *)
Hypothesis HGOT : as_got_shadow B = E01U_GOT_SH.
Hypothesis HSC : as_shadow_cell B = E01U_SHC.
Hypothesis HGU : as_got_uar B = E01U_GOT_UAR.
Hypothesis HUC : as_uar_cell B = E01U_UAR.

Lemma e1p_frame_call : forall (Q : world rsegs -> config -> Prop) W (regsT : bvmap 5 word) memT
STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = w64 E01U_SM4_RA ->
frames Sc = [] ->
(forall S2 (regs2 : bvmap 5 word) mem2 md2 pos,
 ajournal rsegs B STK sp0 FP ly S W0 mem md ((4, pos) :: own) lyc S2 W mem2 md2 k ->
 aregs_preserved regsT regs2 -> getr regs2 10 = w64 (frame_addr lyc 4 pos) ->
 ablocks B lyc S2 = ablocks B lyc Sc -> frames S2 = [(4, pos)] ->
 st_nev S2 = st_nev Sc -> blocks_bytes S2 = blocks_bytes Sc ->
 zero_shadow (aview rsegs (w_H W) mem2) SHADOW_OFF (frame_addr lyc 4 pos) E01U_FB ->
 rdword (aview rsegs (w_H W) mem2) (frame_addr lyc 4 pos + HQU_FLAG) = Some (flag_addr lyc 4 pos) ->
 acall_kept rsegs B lyc Sc W memT W mem2 (sp0 + o - ESTACK) (sp0 + o) (fun _ => False) ->
 SRr rsegs W (cfg_at rsegs E01U_SM4_RA regs2 mem2 md2) Q) ->
SRr rsegs W (cfg_at rsegs E01U_SM4 regsT memT mdc) Q.
Proof.
intros Q W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o HJ Hsp Hal Hneg Hbud Hgp Htp Hra Hfr0 K.
assert (Hcnt : count_cid 4 (frames Sc) < fs_frames 4) by (rewrite Hfr0; cbn [count_cid]; exact e1p_frames4).
unfold cfg_at at 1. rewrite <- HSM4.
eapply SRr_bind.
{ exact (aj_stack_malloc_at rsegs B (AR_laws_ok rsegs B) img_segs_low errno_low ML
    (stack_malloc_progress (as_universe B)) 4 ASM4 ltac:(lia) W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc
    k o (w64 E01U_SM4_RA) HJ Hsp Hal Hneg Hbud Hgp Htp Hra
    ltac:(apply e1p_ret_ok; [unfold E01U_SM4_RA; lia | reflexivity]) Hcnt). }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & Hpres & H10 & Hbl & Hfr2 & _ & Hnev & Hbb
  & Hz & Hflag & Hkept).
rewrite Hfr0 in Hfr2.
apply (K S2 regs2 mem2 md2 pos HJ2 Hpres H10 Hbl Hfr2 Hnev Hbb).
- change E01U_FB with (fs_frame_bytes 4). exact Hz.
- replace (frame_addr lyc 4 pos + HQU_FLAG) with (frame_addr lyc 4 pos + fs_frame_bytes 4 - 8)
    by (change (fs_frame_bytes 4) with 1024; unfold HQU_FLAG; lia). exact Hflag.
- exact Hkept.
Qed.

(* ======================================== the prologue: ENTRY -> 0x80cc4 ======================================== *)
Theorem e01u_pro_ok : e01u_pro_stmt B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
intros hx HB.
destruct hx as [ly S W regs mem md p n pl].
unfold hqu_base in HB. cbn [hu_ly hu_S hu_W hu_regs hu_mem hu_md hu_p hu_n hu_pl] in HB.
pose proof HB as (HPRE & Hra & Hp & Hn & Hpn & Hnl & Hpl & Hfr0 & Hev & Hlive & HROD).
cbn [hu_ly hu_S hu_W hu_regs hu_mem hu_md hu_p hu_n hu_pl].
pose proof HPRE as (HAR & Hra1 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (ajournal_init rsegs B LLVMF_STK [] ly S W regs mem md [] HPRE) as HJ.
assert (HSTK' : 0x230 + 16384 <= LLVMF_STK) by exact HSTK.
assert (HSb : alloc_ceiling + 0x230 + 16384 <= spZ regs <= 2 ^ 47).
{ revert Hceil Hslo Hshi H47 HSTK'. clear. intros. lia. }
assert (Hsp46 : 2 ^ 46 <= spZ regs <= 2 ^ 47) by (revert C1 HSb; clear; intros; lia).
assert (Hpres1 : forall a, spZ regs - 0x220 <= a < spZ regs -> apresent (w_H W) mem a).
{ intros a Ha. apply Hpres. revert Ha HSTK'. clear. intros. lia. }
pose proof (e1p_p1a_entry W regs mem Hpres1 Hsp46 Hal16) as HS.
unfold cfg_at. change (w64 HQU_ENTRY) with (Z_to_bv 64 E01U_A).
(* ---- P1a: 0x80c40 .. 0x80c78, to the first `fsd` 0x80c7c ---- *)
aj_run_to E01U_TBL_ok HS HJ E01U_FSD.
{ lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end.
  eapply awr_ok_cons_stack; [reflexivity | rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity
  | cbn; revert HSTK'; clear; intros; lia | cbn; lia | apply awr_ok_nil]. }
rename ms into ms1, HS into HS1, HJ into HJ1, HF into HF1, HFr into HFr1, HG into HG1.
repeat rewrite wvb_collapse in HJ1.
(* P1a's end: sp = S - 0x220, every other register as at the entry, the 13 saves *)
assert (R2a : getr (ms_regs ms1) 2 = w64 (spZ regs - 0x220)).
{ apply (e1p_reg_of _ _ _ _ 2%bv (SOff 2 (-544)) _ HS1); [vm_compute; reflexivity|].
  rewrite (U_atom_off _ 2 (spZ regs) (-544)); [revert Hsp46; clear; lia | | |].
  - rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl). unfold spZ. symmetry. apply Z_to_bv_bv_unsigned.
  - revert Hsp46; clear; lia.
  - revert Hsp46; clear; lia. }
assert (Hsp1 : spZ (ms_regs ms1) = spZ regs - 0x220).
{ unfold spZ at 1. rewrite R2a. unfold w64. apply unsigned_lit_small. revert Hsp46; clear; lia. }
assert (P3 : getr (ms_regs ms1) 3 = w64 (as_gp B)).
{ rewrite (e1p_reg_atom (w_H W) _ _ ms1 regs [] 3%bv 3 HS1 eq_refl ltac:(vm_compute; reflexivity) ltac:(lia)). exact Hgp. }
assert (P4 : getr (ms_regs ms1) 4 = w64 (as_tp B)).
{ rewrite (e1p_reg_atom (w_H W) _ _ ms1 regs [] 4%bv 4 HS1 eq_refl ltac:(vm_compute; reflexivity) ltac:(lia)). exact Htp. }
assert (P10 : getr (ms_regs ms1) 10 = w64 p).
{ rewrite (e1p_reg_atom (w_H W) _ _ ms1 regs [] 10%bv 10 HS1 eq_refl ltac:(vm_compute; reflexivity) ltac:(lia)). exact Hp. }
assert (P11 : getr (ms_regs ms1) 11 = w64 n).
{ rewrite (e1p_reg_atom (w_H W) _ _ ms1 regs [] 11%bv 11 HS1 eq_refl ltac:(vm_compute; reflexivity) ltac:(lia)). exact Hn. }
assert (SAV1 : forall j, (j < 13)%nat -> val_mem rsegs (mrestrict (w_H W) (ms_mem ms1))
  (spZ regs + (-8 - 8 * Z.of_nat j)) 8 (bv_unsigned (getr regs (nth j hqu_saved_regs 0%bv)))).
{ lazymatch type of HS1 with st_ok _ _ ?ss _ =>
  let r := eval vm_compute in (nth_error (ss_mem ss) 0) in
  lazymatch r with Some ?rg =>
  apply (e1p_saves_of_region _ (mrestrict (w_H W) (ms_mem ms1)) regs _ _ _ _ _
    (e1p_st_ok_region_nth (w_H W) _ _ ms1 0 rg HS1 ltac:(vm_compute; reflexivity)) eq_refl);
  vm_compute; reflexivity end end. }
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres1 & _).
rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms1 HS1 eq_refl). cbn [ss_pc].
change (Z_to_bv 64 527484) with (w64 E01U_FSD).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdl) ?QQ =>
  change (SRr rsegs W (cfg_at rsegs E01U_FSD rg mm mdl) QQ) end.
(* ---- the four float saves 0x80c7c .. 0x80c88 ---- *)
apply (e1p_fsd4 B W (ms_regs ms1) (ms_mem ms1) _ _ LLVMF_STK (spZ regs) [] ly S W mem md [] ly S 0 HJ1).
{ exact R2a. }
{ revert HSTK'; clear; intros; lia. }
{ revert Hsp46; clear; intros; lia. }
{ revert Hsp46; clear; intros; lia. }
{ intros a Ha. apply HJpres1. revert Ha HSTK'. clear. intros. lia. }
intros mem2 X2 HJ2 K2 (v0 & v1 & v2 & v3 & FV0 & FV1 & FV2 & FV3).
(* ---- P1b: 0x80c8c .. the `jal` 0x80cc0 to the class-4 frame function 0x3cd2c ---- *)
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ2)) as (Kc & Ku & Kg & Kgu).
rewrite HSC in Kc. rewrite HUC in Ku. rewrite HGOT, HSC in Kg. rewrite HGU, HUC in Kgu.
assert (Hal1 : spZ (ms_regs ms1) mod 16 = 0).
{ rewrite Hsp1. replace (spZ regs - 0x220) with (spZ regs + (-34) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16. }
pose proof (e1p_p1b_entry W (ms_regs ms1) mem2 ltac:(rewrite Hsp1; revert Hsp46; clear; lia) Hal1 Kgu Kg Ku Kc) as HS.
clear Kc Ku Kg Kgu.
unfold cfg_at. change (w64 E01U_P1B) with (Z_to_bv 64 E01U_P1B).
aj_run_to E01U_TBL_ok HS HJ2 E01U_SM4.
{ lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
rename ms into ms3, HS into HS3, HJ2 into HJ3, HF into HF3, HFr into HFr3, HG into HG3.
repeat rewrite wvb_collapse in HJ3.
(* P1b's end, pc 0x3cd2c: ra = 0x80cc4, sp = s1 = R, s0 = S, s2 = p, s4 = n, s11 = K; P1b writes no memory *)
set (R := 32 * ((spZ regs - 0x220) / 32)).
destruct (e1p_R_range (spZ regs) Hal16 ltac:(revert Hsp46; clear; lia)) as (HRr & HR32 & HR16).
fold R in HRr, HR32, HR16.
assert (Ew2 : ew (Ereg (ms_regs ms1) []) 2 = Z_to_bv 64 (spZ regs - 0x220))
  by (rewrite (ew_Ereg_nat (ms_regs ms1) [] 2 2%bv eq_refl); exact R2a).
assert (T1 : getr (ms_regs ms3) 1 = w64 E01U_SM4_RA).
{ apply (e1p_reg_of _ _ _ _ 1%bv (SLit 527556) _ HS3); [vm_compute; reflexivity|].
  rewrite U_SLit. reflexivity. }
assert (T2 : getr (ms_regs ms3) 2 = w64 R).
{ apply (e1p_reg_of _ _ _ _ 2%bv (SAlu ALU_AND (SOff 2 0) (SLit (-32))) _ HS3); [vm_compute; reflexivity|].
  rewrite (e1p_U_m32 _ 2 (spZ regs - 0x220) Ew2) by (revert Hsp46; clear; lia). reflexivity. }
assert (T9 : getr (ms_regs ms3) 9 = w64 R).
{ apply (e1p_reg_of _ _ _ _ 9%bv (SAlu ALU_ADD (SAlu ALU_AND (SOff 2 0) (SLit (-32))) (SLit 0)) _ HS3);
  [vm_compute; reflexivity|].
  rewrite e1p_U_add0, (e1p_U_m32 _ 2 (spZ regs - 0x220) Ew2) by (revert Hsp46; clear; lia). reflexivity. }
assert (T8 : getr (ms_regs ms3) 8 = w64 (spZ regs)).
{ apply (e1p_reg_of _ _ _ _ 8%bv (SOff 2 544) _ HS3); [vm_compute; reflexivity|].
  rewrite (U_atom_off _ 2 (spZ regs - 0x220) 544 Ew2) by (revert Hsp46; clear; lia). lia. }
assert (T3 : getr (ms_regs ms3) 3 = w64 (as_gp B)).
{ rewrite (e1p_reg_atom (w_H W) _ _ ms3 (ms_regs ms1) [] 3%bv 3 HS3 eq_refl ltac:(vm_compute; reflexivity) ltac:(lia)).
  exact P3. }
assert (T4 : getr (ms_regs ms3) 4 = w64 (as_tp B)).
{ rewrite (e1p_reg_atom (w_H W) _ _ ms3 (ms_regs ms1) [] 4%bv 4 HS3 eq_refl ltac:(vm_compute; reflexivity) ltac:(lia)).
  exact P4. }
assert (T18 : getr (ms_regs ms3) 18 = w64 p).
{ rewrite (e1p_reg_atom (w_H W) _ _ ms3 (ms_regs ms1) [] 18%bv 10 HS3 eq_refl ltac:(vm_compute; reflexivity) ltac:(lia)).
  exact P10. }
assert (T20 : getr (ms_regs ms3) 20 = w64 n).
{ rewrite (e1p_reg_atom (w_H W) _ _ ms3 (ms_regs ms1) [] 20%bv 11 HS3 eq_refl ltac:(vm_compute; reflexivity) ltac:(lia)).
  exact P11. }
assert (T27 : getr (ms_regs ms3) 27 = w64 SHADOW_OFF).
{ apply (e1p_reg_of _ _ _ _ 27%bv (SLit 2147450880) _ HS3); [vm_compute; reflexivity|].
  rewrite U_SLit. reflexivity. }
assert (K3 : forall a, aview rsegs (w_H W) (ms_mem ms3) a = aview rsegs (w_H W) mem2 a).
{ intros a. apply aview_eq_of. apply HFr3. intros (r & Hin & Ha).
  change (In r e1p_p1b_rs) in Hin. unfold e1p_p1b_rs in Hin.
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
  destruct Hin. }
(* ---- the class-4 frame call 0x3cd2c, back at 0x80cc4 ---- *)
rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms3 HS3 eq_refl). cbn [ss_pc].
change (Z_to_bv 64 249132) with (w64 E01U_SM4).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdl) ?QQ =>
  change (SRr rsegs W (cfg_at rsegs E01U_SM4 rg mm mdl) QQ) end.
apply (e1p_frame_call _ W (ms_regs ms3) (ms_mem ms3) LLVMF_STK (spZ regs) [] ly S W mem md [] ly S _ 0
  (R - spZ regs) HJ3).
{ unfold spZ at 1. rewrite T2. unfold w64. rewrite unsigned_lit_small by (revert HRr Hsp46; clear; lia). lia. }
{ exact HR16. }
{ revert HRr; clear; lia. }
{ unfold ESTACK. revert HRr HSTK'; clear; intros; lia. }
{ exact T3. }
{ exact T4. }
{ exact T1. }
{ exact Hfr0. }
intros S2 regs4 mem4 md4 pos HJ4 Hpres4 H10 Hbl Hfr2 Hnev Hbb Hz Hflag Hkept.
(* ---- the state at 0x80cc4: e01u_fr_facts ---- *)
set (F := frame_addr ly 4 pos) in *.
assert (CS : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs4 r = getr (ms_regs ms3) r).
{ intros r Hr. pose proof (Hpres4 (bv_unsigned r) Hr) as X. rewrite !Z_to_bv_bv_unsigned in X. exact X. }
assert (Hcs : forall z, z = 2 \/ z = 3 \/ z = 4 \/ z = 8 \/ z = 9 \/ z = 18 \/ z = 20 \/ z = 27 -> acallee_saved z)
  by (unfold acallee_saved; clear; intros; lia).
assert (KC : forall a, spZ regs - 0x88 <= a < spZ regs -> aview rsegs (w_H W) mem4 a = aview rsegs (w_H W) mem2 a).
{ intros a Ha. destruct Hkept as [Hk1 _]. rewrite (Hk1 a).
  - apply K3.
  - revert Ha HSb; clear; intros; lia.
  - unfold ESTACK. revert Ha HRr; clear; intros; lia. }
apply SRr_ret. unfold e01u_at_fr.
exists pos, (HDEnv (spZ regs) R F 0 0 0 0 0 0 0 0 0 0), ly, S2, regs4, mem4, md4.
split; [reflexivity|].
unfold e01u_fr_facts. cbn [hu_ly hu_S hu_W hu_regs hu_mem hu_md hu_p hu_n hu_pl e_S e_R e_F].
split; [exact HJ4|]. split; [exact Hbl|].
split; [split; [reflexivity | split; reflexivity]|].
split; [rewrite (CS 2%bv) by (apply Hcs; vm_compute; lia); exact T2|].
split; [rewrite (CS 3%bv) by (apply Hcs; vm_compute; lia); exact T3|].
split; [rewrite (CS 4%bv) by (apply Hcs; vm_compute; lia); exact T4|].
split; [rewrite (CS 8%bv) by (apply Hcs; vm_compute; lia); exact T8|].
split; [rewrite (CS 9%bv) by (apply Hcs; vm_compute; lia); exact T9|].
split; [exact H10|].
split; [rewrite (CS 18%bv) by (apply Hcs; vm_compute; lia); exact T18|].
split; [rewrite (CS 20%bv) by (apply Hcs; vm_compute; lia); exact T20|].
split; [rewrite (CS 27%bv) by (apply Hcs; vm_compute; lia); exact T27|].
split; [apply hm_fsh_zero; exact Hz|].
apply (e1p_kept_of _ pos _ W mem4 regs4 v0 v1 v2 v3); cbn [hu_regs hu_ly e_S e_F].
- intros j Hj. apply (val_mem_kept rsegs (w_H W) (w_H W) (ms_mem ms1) mem4); [|exact (SAV1 j Hj)].
  intros kk Hkk. cbn in Hkk. assert (Hjz : 0 <= Z.of_nat j <= 12) by lia.
  rewrite KC by (revert Hjz Hkk; clear; intros; lia).
  apply K2.
  + revert Hjz Hkk Hsp46; clear; intros; lia.
  + revert Hjz Hkk; clear; intros; lia.
- exact (val_mem_of_rdword rsegs (w_H W) mem4 _ _ Hflag).
- apply (val_mem_kept rsegs (w_H W) (w_H W) mem2 mem4); [|exact FV0].
  intros kk Hkk. cbn in Hkk. apply KC. revert Hkk; clear; intros; lia.
- apply (val_mem_kept rsegs (w_H W) (w_H W) mem2 mem4); [|exact FV1].
  intros kk Hkk. cbn in Hkk. apply KC. revert Hkk; clear; intros; lia.
- apply (val_mem_kept rsegs (w_H W) (w_H W) mem2 mem4); [|exact FV2].
  intros kk Hkk. cbn in Hkk. apply KC. revert Hkk; clear; intros; lia.
- apply (val_mem_kept rsegs (w_H W) (w_H W) mem2 mem4); [|exact FV3].
  intros kk Hkk. cbn in Hkk. apply KC. revert Hkk; clear; intros; lia.
Qed.
Print Assumptions e01u_pro_ok.
End b.

Print Assumptions e01u_pro_ok.
About e01u_pro_ok.
