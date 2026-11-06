(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_up.v, with its module paths and module names changed; 264 of its 309 lines of code are new or changed and 2644 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/fuzz_recv_cp.v, with its module names changed; 278 of its 327 lines of code are new or changed and 260 lines of the source are left out. *)
(* talk on image A: the steps the message piece (lib/A/Prog/talk_msg.v) and the attribute piece
   (lib/A/Prog/talk_attr.v) of its walk share:
   - tq_region, tq_den0, tq_den_U, tq_den_off, tq_Sg, tq_br_lt, tq_br_ge, tq_U_*: the values the runner forms from
     the bytes it loads (sums, the 16-bit joins of two bytes, the flags `seqz | seqz`, NL_ALIGN as `srliw / slli`
     and as `& 0x1fffc`, the 4-byte NLMSG_ERROR code with its sign-extended top byte) and the signed compares;
   - tq_val1, tq_spill_word, tq_keep_regs: a byte of a region, a word the code stored into the frame, the registers
     a run leaves as they were;
   - tq_ck, tq_byte, tq_gbyte, tq_ra: chunk c of g_nl (its length, its bytes in memory, the addressable range the
     instrumented checks of its loads test);
   - tq_out, tq_keep: the model block and the live buffers lie outside the frame, so a run that writes only the
     frame keeps them (amodel_at and tk_bufs).
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk talk_c talk_defs talk_kit talk_spec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---- the symbolic state ---------------------------------------------------------------------------------------- *)
(* a region of a symbolic state holds at the machine state *)
Lemma tq_region : forall E ss ms i r,
  st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok SEGS E (ms_mem ms) r.
Proof. intros E ss ms i r HS Hi. exact (st_ok_region_nth (segs := SEGS) E (abs_ss VAL ss) ms i r HS Hi). Qed.

Lemma tq_den0 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by exact Hv. rewrite Z.add_0_r. reflexivity. Qed.

Lemma tq_den_U : forall E v z, U E v = z mod 2 ^ 64 -> sv_denot E v = w64 z.
Proof.
  intros E v z H. rewrite denot_lit_U, H. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Zmod_mod.
Qed.

Lemma tq_den_off : forall E n v k, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n k) = w64 (v + k).
Proof.
  intros E n v k H Hv. apply tq_den_U. rewrite U_SOff, H, unsigned_lit_small by exact Hv. reflexivity.
Qed.

(* the signed value of a symbolic value whose unsigned value is z modulo 2^64 *)
Lemma tq_Sg : forall E v z, U E v = z mod 2 ^ 64 -> - 2 ^ 63 <= z < 2 ^ 63 -> Sg E v = z.
Proof.
  intros E v z H Hz. rewrite S_of_U, H. change (2 ^ 64) with M64. rewrite modM64_wrap, bv_swrap_wrap.
  apply swrap64_id. unfold half64. lia.
Qed.

Lemma tq_br_lt : forall E a b, branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (Sg E a <? Sg E b).
Proof. intros E a b. cbn [branch_taken]. rewrite bv_lts_signed. reflexivity. Qed.

Lemma tq_br_ge : forall E a b, branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (Sg E a <? Sg E b).
Proof. intros E a b. cbn [branch_taken]. rewrite bv_lts_signed. reflexivity. Qed.

(* ---- the values the runner forms --------------------------------------------------------------------------------- *)
Lemma tq_U_add : forall E a b x y, U E a = x -> U E b = y -> 0 <= x + y < 2 ^ 64 -> U E (SAlu ALU_ADD a b) = x + y.
Proof. intros E a b x y Hx Hy R. rewrite U_SAlu, Hx, Hy. cbn [zalu_raw]. apply zcanon_id. unfold M64. lia. Qed.

Lemma tq_U_addk : forall E a x k, U E a = x -> 0 <= x + k < 2 ^ 64 -> U E (SAlu ALU_ADD a (SLit k)) = x + k.
Proof.
  intros E a x k Hx R. rewrite U_SAlu, Hx, U_SLit. cbn [zalu_raw]. unfold zcanon, M64.
  rewrite Z.add_mod_idemp_r by lia. apply Z.mod_small. exact R.
Qed.

(* lbu hi, lbu lo, slli hi 8, or: the 16-bit little-endian value *)
Lemma tq_U_join2 : forall E hi lo x y, U E hi = x -> U E lo = y -> 0 <= x < 256 -> 0 <= y < 256 ->
  U E (SAlu ALU_OR (SAlu ALU_SLL hi (SLit 8)) lo) = y + 256 * x.
Proof.
  intros E hi lo x y Hx Hy Rx Ry. rewrite !U_SAlu, Hx, Hy, U_lit by lia. cbn [zalu_raw].
  change (Z.land 8 63) with 8.
  rewrite (zcanon_id (Z.shiftl x 8)) by (rewrite Z.shiftl_mul_pow2 by lia; unfold M64; lia).
  rewrite tw_join2 by lia. apply zcanon_id. unfold M64. lia.
Qed.

(* seqz *)
Lemma tq_U_sltu1 : forall E a x, U E a = x -> U E (SAlu ALU_SLTU a (SLit 1)) = if x =? 0 then 1 else 0.
Proof.
  intros E a x Hx. pose proof (U_range E a) as R. rewrite Hx in R. rewrite U_SAlu, Hx, U_lit by lia.
  cbn [zalu_raw]. destruct (Z.eqb_spec x 0) as [E0|E0]; destruct (Z.ltb_spec x 1); first [lia | reflexivity].
Qed.

(* the flag the RTM_NEWLINK arm spills: seqz p | seqz n *)
Lemma tq_U_flag : forall E p n P N, U E p = P -> U E n = N ->
  U E (SAlu ALU_OR (SAlu ALU_SLTU p (SLit 1)) (SAlu ALU_SLTU n (SLit 1))) = tk_flag P N.
Proof.
  intros E p n P N HP HN. rewrite U_SAlu, (tq_U_sltu1 E p P HP), (tq_U_sltu1 E n N HN). cbn [zalu_raw].
  unfold tk_flag. destruct (P =? 0), (N =? 0); reflexivity.
Qed.

(* +0x244..+0x24c: addi 3, srliw 2, slli 2 of ml (the atom n): NL_ALIGN(ml) *)
Lemma tq_U_align : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x <= 4096 ->
  U E (SAlu ALU_SLL (SAluw ALU_SRL (SOff n 3) (SLit 2)) (SLit 2)) = nl_align x.
Proof.
  intros E n x Hn Hx.
  assert (A : U E (SAluw ALU_SRL (SOff n 3) (SLit 2)) = (x + 3) / 4).
  { rewrite U_of_S, S_SAluw, (U_atom_off E n x 3 Hn) by lia. rewrite U_lit by lia. cbn [zalu_raw].
    change (Z.land (2 mod 2 ^ 32) 31) with 2. rewrite tw_srliw by lia.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small.
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  rewrite U_SAlu, A, U_lit by lia. cbn [zalu_raw]. change (Z.land 2 63) with 2. rewrite tw_align_eq.
  apply zcanon_id. pose proof (tw_align_range x ltac:(lia)) as R. unfold M64. lia.
Qed.

(* +0x250: left - NL_ALIGN(ml), signed *)
Lemma tq_S_sub_align : forall E n m x l, ew E n = Z_to_bv 64 x -> ew E m = Z_to_bv 64 l ->
  0 <= x <= 4096 -> 0 <= l <= 4096 ->
  Sg E (SAlu ALU_SUB (SOff m 0) (SAlu ALU_SLL (SAluw ALU_SRL (SOff n 3) (SLit 2)) (SLit 2))) = l - nl_align x.
Proof.
  intros E n m x l Hn Hm Hx Hl. pose proof (tw_align_range x ltac:(lia)) as R.
  apply tq_Sg; [|lia].
  rewrite U_SAlu, (tq_U_align E n x Hn Hx), (U_atom E m l Hm) by lia. cbn [zalu_raw]. reflexivity.
Qed.

Lemma tq_U_sub_align : forall E n m x l, ew E n = Z_to_bv 64 x -> ew E m = Z_to_bv 64 l ->
  0 <= x <= 4096 -> 0 <= l <= 4096 ->
  U E (SAlu ALU_SUB (SOff m 0) (SAlu ALU_SLL (SAluw ALU_SRL (SOff n 3) (SLit 2)) (SLit 2))) =
  (l - nl_align x) mod 2 ^ 64.
Proof.
  intros E n m x l Hn Hm Hx Hl.
  rewrite U_SAlu, (tq_U_align E n x Hn Hx), (U_atom E m l Hm) by lia. cbn [zalu_raw]. reflexivity.
Qed.

(* +0x598 / +0x504: (l + 3) & 0x1fffc, the attribute length l in the atom n plus 3 *)
Lemma tq_U_land : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 16 ->
  U E (SAlu ALU_AND (SOff n 3) (SLit 131068)) = nl_align x.
Proof.
  intros E n x Hn Hx. rewrite U_SAlu, (U_atom_off E n x 3 Hn), U_lit by lia. cbn [zalu_raw].
  rewrite tw_land_align by lia. apply zcanon_id. pose proof (tw_align_range x ltac:(lia)) as R. unfold M64. lia.
Qed.

(* +0x614..+0x638: the NLMSG_ERROR code from its four bytes (lbu, lbu, lbu, lb), sign-extended *)
Lemma tq_U_code : forall E (bt0 bt1 bt2 bt3 : byte),
  ew E 51 = Z_to_bv 64 (bz bt0) -> ew E 52 = Z_to_bv 64 (bz bt1) -> ew E 53 = Z_to_bv 64 (bz bt2) ->
  ew E 54 = Z_to_bv 64 (bz bt3) ->
  U E (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SExt true 8 (SOff 54 0)) (SLit 24)) (SAlu ALU_SLL (SOff 53 0) (SLit 16)))
                   (SAlu ALU_OR (SAlu ALU_SLL (SOff 52 0) (SLit 8)) (SOff 51 0)))
  = (bz bt0 + 256 * bz bt1 + 65536 * bz bt2 + 16777216 * sbz bt3) mod 2 ^ 64.
Proof.
  intros E bt0 bt1 bt2 bt3 H0 H1 H2 H3.
  pose proof (tw_byte_range bt0) as R0. pose proof (tw_byte_range bt1) as R1.
  pose proof (tw_byte_range bt2) as R2. pose proof (tw_byte_range bt3) as R3. pose proof (sbz_range bt3) as S3.
  assert (X3 : U E (SExt true 8 (SOff 54 0)) = sbz bt3 mod 2 ^ 64).
  { rewrite U_SExt, (U_atom E 54 (bz bt3) H3) by lia. cbv iota. change (2 ^ Z.of_N 8) with 256.
    rewrite (Z.mod_small (bz bt3) 256) by lia. rewrite <- sbz_signed. unfold zcanon, M64, bz. reflexivity. }
  assert (X4 : U E (SAlu ALU_SLL (SExt true 8 (SOff 54 0)) (SLit 24)) = (sbz bt3 mod 2 ^ 40) * 2 ^ 24).
  { rewrite U_SAlu, X3, U_lit by lia. cbn [zalu_raw]. change (Z.land 24 63) with 24.
    rewrite Z.shiftl_mul_pow2 by lia. unfold zcanon, M64. rewrite Z.mul_mod_idemp_l by lia.
    change (2 ^ 64) with (2 ^ 40 * 2 ^ 24). apply Z.mul_mod_distr_r; lia. }
  assert (X2 : U E (SAlu ALU_SLL (SOff 53 0) (SLit 16)) = bz bt2 * 2 ^ 16).
  { rewrite U_SAlu, (U_atom E 53 (bz bt2) H2), U_lit by lia. cbn [zalu_raw]. change (Z.land 16 63) with 16.
    rewrite Z.shiftl_mul_pow2 by lia. apply zcanon_id. unfold M64. lia. }
  assert (X1 : U E (SAlu ALU_OR (SAlu ALU_SLL (SOff 52 0) (SLit 8)) (SOff 51 0)) = bz bt0 + 256 * bz bt1).
  { apply (tq_U_join2 E _ _ (bz bt1) (bz bt0)); [apply (U_atom E 52 (bz bt1) H1); lia
      | apply (U_atom E 51 (bz bt0) H0); lia | lia | lia]. }
  pose proof (Z.mod_pos_bound (sbz bt3) (2 ^ 40) ltac:(lia)) as M.
  set (q := sbz bt3 mod 2 ^ 40) in *.
  assert (X5 : U E (SAlu ALU_OR (SAlu ALU_SLL (SExt true 8 (SOff 54 0)) (SLit 24)) (SAlu ALU_SLL (SOff 53 0) (SLit 16)))
              = q * 2 ^ 24 + bz bt2 * 2 ^ 16).
  { rewrite U_SAlu, X4, X2. cbn [zalu_raw].
    rewrite (tw_lor_add (q * 2 ^ 24) (bz bt2 * 2 ^ 16) 24) by (first [lia | apply Z.mod_mul; lia]).
    apply zcanon_id. unfold M64. lia. }
  rewrite U_SAlu, X5, X1. cbn [zalu_raw].
  rewrite (tw_lor_add (q * 2 ^ 24 + bz bt2 * 2 ^ 16) (bz bt0 + 256 * bz bt1) 16)
    by (first [lia | replace (q * 2 ^ 24 + bz bt2 * 2 ^ 16) with ((q * 2 ^ 8 + bz bt2) * 2 ^ 16) by lia;
                     apply Z.mod_mul; lia]).
  rewrite zcanon_id by (unfold M64; lia).
  subst q. destruct (Z_lt_le_dec (sbz bt3) 0) as [Hn|Hp].
  - rewrite <- (Z.mod_add (sbz bt3) 1 (2 ^ 40)) by lia. rewrite (Z.mod_small (sbz bt3 + 1 * 2 ^ 40)) by lia.
    rewrite <- (Z.mod_add (bz bt0 + 256 * bz bt1 + 65536 * bz bt2 + 16777216 * sbz bt3) 1 (2 ^ 64)) by lia.
    rewrite Z.mod_small by lia. lia.
  - rewrite (Z.mod_small (sbz bt3) (2 ^ 40)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* ---- bytes and words in regions ---------------------------------------------------------------------------------- *)
Lemma tq_val1 : forall m a bt, mbyte SEGS m a = Some bt -> val_mem SEGS m a 1 (bz bt).
Proof.
  intros m a bt H k Hk. assert (Hk0 : k = 0%nat) by lia. subst k.
  change (Z.of_nat 0) with 0. rewrite Z.add_0_r, H. f_equal.
  pose proof (tw_byte_range bt) as R.
  rewrite (YI04.le_byte_small (bz bt) 1 0) by (try change (2 ^ (8 * Z.of_nat 1)) with 256; lia).
  change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. unfold bz. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* a word the code stored into the frame region (base atom 2), read back as the val_mem of its value *)
Lemma tq_spill_word : forall E m cs lo hi wlo whi od e w b,
  region_ok SEGS E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) -> bv_unsigned (ew E 2) = b ->
  In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = w ->
  val_mem SEGS m (b + od) 8 (bv_unsigned w).
Proof.
  intros E m cs lo hi wlo whi od e w b HR Hb Hin He.
  pose proof (field_of_region_any (segs := SEGS) E m 2 b cs lo hi wlo whi od 8 e HR Hb Hin ltac:(lia)) as V.
  rewrite He in V. change (N.to_nat 8) with 8%nat in V.
  pose proof (bv_unsigned_in_range 64 w) as Rw. change (bv_modulus 64) with (2 ^ 64) in Rw.
  rewrite Z.mod_small in V by (change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia). exact V.
Qed.

(* the registers a run leaves as the fresh state had them (the pairs ov, checked by computation); E' is the
   environment after the run, which agrees with the fresh state's E below the runner's fresh atoms *)
Lemma tq_keep_regs : forall (H : word -> bool) E E' ss ms regs (ov : list (bv 5 * sv)),
  st_ok_pi SEGS VAL E' ss (restrict H ms) -> YP06.env_agree 512 E E' ->
  Forall (fun p => sv_denot E (snd p) = getr regs (fst p)) ov ->
  forallb (fun p => sv_eqb (sr_get (ss_regs ss) (fst p)) (snd p) && sv_atoms_lt 512 (snd p)) ov = true ->
  Forall (fun p => getr (ms_regs ms) (fst p) = getr regs (fst p)) ov.
Proof.
  intros H E E' ss ms regs ov HS HA HO HB. rewrite Forall_forall in HO |- *. intros [r v] Hin. cbn [fst snd].
  rewrite forallb_forall in HB. specialize (HB (r, v) Hin). cbn [fst snd] in HB.
  apply andb_true_iff in HB as [HB HL].
  rewrite (st_ok_pi_restrict_reg H E' ss ms r HS). apply sv_eqb_eq in HB. rewrite HB.
  rewrite (YP06.sv_denot_agree 512 E E' v HA HL). exact (HO (r, v) Hin).
Qed.

Variable B : asyms.
Hypothesis LV : LinkVals.
Variable c : tkc.
Hypothesis HC : tk_call SK B c.
#[local] Notation W := (tc_W c).
#[local] Notation memc := (tc_memc c).
#[local] Notation regs0 := (tc_regs0 c).
#[local] Notation kbs := (tc_kbs c).

(* a register of a fresh state is the atom of itself *)
Lemma tq_den_reg : forall regs xs n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  sv_denot (tk_E c regs xs) (SOff n 0) = getr regs r.
Proof.
  intros regs xs n r Hn Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply tk_E_reg; assumption.
Qed.

(* ---- chunk c of g_nl ------------------------------------------------------------------------------------------ *)
Lemma tq_ck : forall ci, 0 <= ci < tk_nch c ->
  Z.of_nat (length (tk_ck c ci)) = fld_u64 kbs (NK_CHUNK_LEN + 8 * ci) /\
  Z.of_nat (length (tk_ck c ci)) <= NL_CHUNK_MAX /\ tk_nch c <= NL_CHUNKS.
Proof.
  intros ci Hci. pose proof HC as (_ & _ & _ & (_ & HL) & HNW & _).
  destruct (nk_chunk_len kbs ci HNW HL Hci) as (A & B1 & C1). unfold tk_ck, tk_nch in *. lia.
Qed.

(* byte i of chunk c, in memory at b + i *)
Lemma tq_byte : forall regs mem md ci i, tk_inv SK B c regs mem md -> 0 <= ci < tk_nch c ->
  0 <= i < Z.of_nat (length (tk_ck c ci)) ->
  exists bt, nth_error (tk_ck c ci) (Z.to_nat i) = Some bt /\ mbyte SEGS (rdW W mem) (tk_b ci + i) = Some bt.
Proof.
  intros regs mem md ci i HI Hci Hi.
  pose proof HC as (_ & _ & _ & _ & HNW & _).
  destruct (tq_ck ci Hci) as (L1 & _ & _).
  pose proof (anlk_chunk_byte SEGS (rdW W mem) LA_G_NL kbs ci i (tk_nlk_kept SK B c HC regs mem md HI) HNW Hci
    ltac:(lia)) as E.
  destruct (nth_error (tk_ck c ci) (Z.to_nat i)) as [bt|] eqn:Eb; [|apply nth_error_None in Eb; lia].
  exists bt. split; [reflexivity|]. unfold tk_b, NL_CHUNK_MAX. rewrite E. exact Eb.
Qed.

(* byte x of g_nl *)
Lemma tq_gbyte : forall regs mem md x, tk_inv SK B c regs mem md -> 0 <= x < NK_SIZE ->
  exists bt, nth_error kbs (Z.to_nat x) = Some bt /\ mbyte SEGS (rdW W mem) (LA_G_NL + x) = Some bt.
Proof.
  intros regs mem md x HI Hx. destruct (tk_nlk_kept SK B c HC regs mem md HI) as ((Hab & _) & HL).
  destruct Hab as (_ & _ & Hb).
  destruct (nth_error kbs (Z.to_nat x)) as [bt|] eqn:Eb; [|apply nth_error_None in Eb; lia].
  exists bt. split; [reflexivity|]. rewrite <- Eb.
  replace (LA_G_NL + x) with (LA_G_NL + Z.of_nat (Z.to_nat x)) by lia. apply Hb.
  apply nth_error_Some. rewrite Eb. discriminate.
Qed.

(* a read of chunk c of length n at off *)
Lemma tq_val_ck : forall regs mem md ci off (n : nat), tk_inv SK B c regs mem md -> 0 <= ci < tk_nch c ->
  0 <= off -> off + Z.of_nat n <= Z.of_nat (length (tk_ck c ci)) ->
  val_mem SEGS (rdW W mem) (tk_b ci + off) n (rdn (tk_ck c ci) off (Z.of_nat n)).
Proof.
  intros regs mem md ci off n HI Hci Ho Hn.
  pose proof HC as (_ & _ & _ & _ & HNW & _).
  destruct (tq_ck ci Hci) as (L1 & _ & _).
  unfold tk_b, NL_CHUNK_MAX.
  exact (anlk_chunk_val SEGS (rdW W mem) LA_G_NL kbs ci off n (tk_nlk_kept SK B c HC regs mem md HI) HNW Hci Ho
    ltac:(lia)).
Qed.

(* the shadow of the chunk queue at the current memory: the addressable range the checks of a chunk's loads test *)
Lemma tq_ra : forall regs mem md x n, tk_inv SK B c regs mem md ->
  LA_G_NL <= x -> x + n <= LA_G_NL + NK_N_CHUNKS -> 0 <= n ->
  range_addressable (rd_of SEGS (rdW W mem)) SHADOW_OFF x n.
Proof.
  intros regs mem md x n HI Hx Hn Hn0.
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRAq & _).
  change (ard SEGS (rdW W memc)) with (aview SEGS (w_H W) memc) in HRAq.
  pose proof (tk_ra_kept SK B c HC regs mem md (LA_G_NL + NK_CHUNK) NK_N_CHUNKS HI
    ltac:(unfold LA_G_NL, NK_CHUNK; lia) ltac:(unfold LA_G_NL, NK_CHUNK, NK_N_CHUNKS, kHighMemEnd; lia) HRAq) as R.
  change (rd_of SEGS (rdW W mem)) with (aview SEGS (w_H W) mem).
  apply (range_addressable_sub _ _ (LA_G_NL + NK_CHUNK) NK_N_CHUNKS); [exact R | unfold NK_CHUNK; lia | unfold NK_CHUNK; lia].
Qed.

(* ---- the model block and the buffers outside the frame -------------------------------------------------------------- *)
Lemma tq_out : forall d n a, tk_dst c d n -> 0 <= n -> d <= a < d + n ->
  0 <= a < 2 ^ 64 /\ ~ (tk_sp c - TALK_AK <= a < tk_sp c).
Proof.
  intros d n a Hd Hn Ha. destruct (tk_dst_facts SK B c HC d n Hd Hn) as (_ & _ & _ & _ & _ & _ & Hw).
  destruct (Hw a Ha) as [HE _]. destruct (tk_ewr_facts SK B c HC a HE) as (Hf & _ & Hr).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  split; [destruct Hr as [Hr|Hr]; lia | exact Hf].
Qed.

(* a run that changes no byte outside the frame window [sp - K, sp) keeps the model block and the buffers *)
Lemma tq_keep : forall mem mem',
  (forall a, 0 <= a < 2 ^ 64 -> ~ (tk_sp c - TALK_AK <= a < tk_sp c) ->
     aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
  (forall mb, amodel_at SEGS (rdW W mem) (tk_m c) mb -> amodel_at SEGS (rdW W mem') (tk_m c) mb) /\
  (forall acc, tk_bufs c mem acc -> tk_bufs c mem' acc).
Proof.
  intros mem mem' UN PR.
  assert (K : forall d n a, tk_dst c d n -> 0 <= n -> d <= a < d + n ->
             aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a).
  { intros d n a Hd Hn Ha. destruct (tq_out d n a Hd Hn Ha) as (R & F). exact (UN a R F). }
  assert (KB : forall d n a, tk_dst c d n -> 0 <= n -> d <= a < d + n ->
             mbyte SEGS (rdW W mem') a = mbyte SEGS (rdW W mem) a).
  { intros d n a Hd Hn Ha. apply (mbyte_of_aview SEGS). exact (K d n a Hd Hn Ha). }
  assert (KW : forall a, writable_at SEGS (rdW W mem) a -> writable_at SEGS (rdW W mem') a).
  { intros a Hw. exact (writable_kept (segs := SEGS) (w_H W) mem mem' a (PR a) Hw). }
  split.
  { intros mb Hm. apply (amodel_kept SEGS (rdW W mem) (rdW W mem') (tk_m c) mb Hm).
    - intros i Hi. apply (KB (tk_m c) MD_SIZE); [unfold tk_dst; left; lia | unfold MD_SIZE; lia | lia].
    - intros i Hi. apply KW. destruct Hm as ((_ & Hwr) & HL). apply Hwr. lia. }
  intros acc (B1 & B2 & B3 & B4 & B5 & B6).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  - intros H0 H1. destruct (B1 H0 H1) as (junk & Hjl & (Hab & Hwr)). exists junk. split; [exact Hjl|]. split.
    + apply (abytes_kept SEGS (rdW W mem) (rdW W mem') (tk_kd c) junk Hab). intros i Hi.
      apply (KB (tk_kd c) (tk_kn c)); [unfold tk_dst; right; left; lia | lia | lia].
    + intros i Hi. apply KW. apply Hwr. exact Hi.
  - intros H0 H1. destruct (B2 H0 H1) as (junk & Hjl & (Hab & Hwr)). exists junk. split; [exact Hjl|]. split.
    + apply (abytes_kept SEGS (rdW W mem) (rdW W mem') (tk_ad c) junk Hab). intros i Hi.
      apply (KB (tk_ad c) (tk_an c)); [unfold tk_dst; right; right; lia | lia | lia].
    + intros i Hi. apply KW. apply Hwr. exact Hi.
  - intros pay Hk H0 H1. destruct (B3 pay Hk H0 H1) as (Hab & Hnn). split; [|exact Hnn].
    apply (abytes_kept SEGS (rdW W mem) (rdW W mem') (tk_kd c) _ Hab). intros i Hi.
    rewrite length_app in Hi. cbn [length] in Hi. pose proof (tt_cut_len pay (tk_kn c) H1) as Lc.
    apply (KB (tk_kd c) (tk_kn c)); [unfold tk_dst; right; left; lia | lia | lia].
  - intros pay Hk H0 H1. destruct (B4 pay Hk H0 H1) as (Hab & Hnn). split; [|exact Hnn].
    apply (abytes_kept SEGS (rdW W mem) (rdW W mem') (tk_ad c) _ Hab). intros i Hi.
    rewrite length_app in Hi. cbn [length] in Hi. pose proof (tt_cut_len pay (tk_an c) H1) as Lc.
    apply (KB (tk_ad c) (tk_an c)); [unfold tk_dst; right; right; lia | lia | lia].
  - intros Hn H0 H1 i Hi. rewrite (K (tk_kd c) (tk_kn c) (tk_kd c + i)); [exact (B5 Hn H0 H1 i Hi)
      | unfold tk_dst; right; left; lia | lia | lia].
  - intros Hn H0 H1 i Hi. rewrite (K (tk_ad c) (tk_an c) (tk_ad c + i)); [exact (B6 Hn H0 H1 i Hi)
      | unfold tk_dst; right; right; lia | lia | lia].
Qed.

Lemma tq_keep_cmem : forall mem mem' j,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (tk_sp c - TALK_AK <= a < tk_sp c) ->
     aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
  tk_cmem c mem j -> tk_cmem c mem' j.
Proof.
  intros mem mem' j UN PR (mb & Hm & Ho & Hn). exists mb. split; [|exact (conj Ho Hn)].
  exact (proj1 (tq_keep mem mem' UN PR) mb Hm).
Qed.
End w.

(* the environment after a run agrees with the fresh state's below the runner's fresh atoms (512 on) *)
Ltac tq_agree :=
  split; [ intros ?nn ?Hnn; cbn [ew ewset];
           repeat match goal with |- context [Nat.eqb ?x ?k] => rewrite (proj2 (Nat.eqb_neq x k)) by lia end;
           reflexivity
         | reflexivity ].

(* a register's symbolic value at a stop, unnormalised *)
Ltac tq_rreg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
  end.
