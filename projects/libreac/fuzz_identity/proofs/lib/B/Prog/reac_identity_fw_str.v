(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* reac_identity_fw_str (fuzz_identity.asan-ubsan 0x8406c, listing offset AF_reac_identity_fw_str = 0x38f8,
   141 slots up to 0x8429c): its ASan+UBSan-build contract treac_identity_fw_str_spec and the walk
   pb_reac_identity_fw_str. The statement is the ASan build's (lib/A/Prog/reac_identity_fw_str.v) over
   the B listing identb_listing and the B layer (IdentBPa, IdentBPaLib, IdentBCJ).

   The function takes a0 = v (a uint16_t, zero-extended), a1 = o (the buffer), a2 = c (its capacity).
   With o = 0 or c < 8 it writes nothing and returns -1. Otherwise it writes the plain model's FW v (the whole
   part of v / 1000, '.', three digits of v mod 1000; lib/Prog/reac_identity_fw_str_c.v) and a NUL
   at o, L v + 1 bytes (6 or 7), and returns L v. Each store is checked by the memory-checking
   runtime: the shadow byte of the address is loaded through the GOT slot A_OBJ 1 (0x9c690) and the
   shadow cell A_OBJ 31 (0xa52b8), and a nonzero shadow byte that does not allow the access leads to
   __asan_report_store1 (0x8423c .. 0x8429c). The walk never reaches that path: the premise
   range_addressable over [o, o + L v + 1) puts that range in the walk's shadow entries.
   Before the store to o + d + j (d = 1 if 10000 <= v else 0, j = 0 .. 5), the UBSan pointer-overflow
   check `bltu ~o, d + j` (0x840d0, 0x84120, 0x84144, 0x8418c, 0x841dc, 0x8420c) branches to the trap
   word 0x84238. It is not taken: the buffer lies in the caller's heap blocks or side-stack frames
   (IdentBCJ.tdst_ok), below the allocator's ceiling, so o + d + j does not wrap (fw_trap_ltu). The
   UBSan checks add no premise to the ASan build's statement.
   The frame is 16 bytes (0x8406c addi sp,sp,-16, 0x84230 addi sp,sp,16) and holds ra at sp-8; no
   call is reached.

   The form is cgif's caller-journal form (projects/cgif/cgif_file_fuzzer/proofs/lib/YC20.v:311-365), for the
   reason lib/A/Prog/reac_identity_fw_str.v gives: the caller, LLVMFuzzerTestOneInput (call slots
   0x80a6c, 0x8142c, 0x818b8, 0x818d4, 0x819dc of identb_listing), passes buffers in its own frame.
   The premise is the caller's journal; the right to write each byte of the buffer is the caller's
   (IdentBCJ.twr_ok); the post extends the same journal and says what the call kept
   (IdentBCJ.tcj_kept). The call makes no allocation and no event: its journal's event count is the
   caller's k. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBCJ.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_identity_fw_str_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* The bytes the call writes when it writes: FW v and the NUL, as byte values. *)
Definition fw_n (v : Z) : Z := reac_identity_fw_str_c.L v + 1.
Definition fw_bytes (v : Z) : list Z :=
  map (fun b : byte => bv_unsigned b) (reac_identity_fw_str_c.FW v ++ [Z_to_bv 8 0]).
(* The call writes the buffer exactly when o <> 0 and 8 <= c. *)
Definition fw_writes (o c : Z) : bool := negb (o =? 0) && (8 <=? c).
(* The function's own frame (0x8406c addi sp,sp,-16), and the stack the call needs: its frame and the
   runtime's ESTACK (CONVENTIONS.md section 3). *)
Definition FW_FRAME : Z := 16.
Definition REAC_IDENTITY_FW_STR_STK : Z := FW_FRAME + ESTACK.
Lemma fw_n_short : forall v, 0 <= v < 10000 -> fw_n v = 6.
Proof.
intros v Hv. unfold fw_n. rewrite (proj2 (reac_identity_fw_str_c.reac_identity_fw_str_c3_len v ltac:(lia))).
rewrite (proj2 (Z.ltb_lt v 10000)) by lia. reflexivity.
Qed.
Lemma fw_n_long : forall v, 10000 <= v < 65536 -> fw_n v = 7.
Proof.
intros v Hv. unfold fw_n. rewrite (proj2 (reac_identity_fw_str_c.reac_identity_fw_str_c3_len v ltac:(lia))).
rewrite (proj2 (Z.ltb_ge v 10000)) by lia. reflexivity.
Qed.
Lemma fw_bytes_len : forall v, length (fw_bytes v) = Z.to_nat (fw_n v).
Proof.
intros v. unfold fw_bytes, fw_n, reac_identity_fw_str_c.L. rewrite length_map, length_app. cbn [length]. lia.
Qed.
(* A check of f on [lo, lo + n), run by vm_compute. *)
Fixpoint fw_zall (f : Z -> bool) (n : nat) (lo : Z) : bool :=
  match n with O => true | S n' => if f lo then fw_zall f n' (lo + 1) else false end.
Lemma fw_zall_spec : forall f n lo, fw_zall f n lo = true -> forall x, lo <= x < lo + Z.of_nat n -> f x = true.
Proof.
intros f n; induction n as [|n IH]; intros lo H x Hx; cbn [fw_zall] in H; [lia|].
destruct (f lo) eqn:Hf; [|discriminate H].
destruct (Z.eq_dec x lo) as [->|Hne]; [exact Hf|]. apply (IH (lo + 1) H). lia.
Qed.
(* A byte range that meets no byte of [lo, hi) lies on one side of it. *)
Lemma fw_range_apart : forall o n lo hi, 0 < n -> lo < hi -> (forall a, o <= a < o + n -> ~ (lo <= a < hi)) ->
  o + n <= lo \/ hi <= o.
Proof.
intros o n lo hi Hn Hlh H. destruct (Z_le_gt_dec (o + n) lo) as [H1|H1]; [left; exact H1|].
destruct (Z_le_gt_dec hi o) as [H2|H2]; [right; exact H2|]. exfalso. apply (H (Z.max o lo)); lia.
Qed.
(* ~o as a 64-bit value (the UBSan checks compare it with the offset). *)
Lemma fw_lxor_ones : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
intros x Hx. change 18446744073709551615 with (Z.ones 64).
pose proof (Z.add_lnot_diag x).
assert (E : Z.lxor x (Z.ones 64) = (Z.lnot x) mod 2 ^ 64).
{ rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
  rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
  destruct (Z.lt_ge_cases i 64).
  - rewrite Z.ones_spec_low by lia. rewrite xorb_true_r, andb_true_r. reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite xorb_false_r, andb_false_r.
    destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia|lia]. }
rewrite E. unfold Z.ones. rewrite Z.shiftl_1_l. change (Z.pred (2 ^ 64)) with (2 ^ 64 - 1).
replace (Z.lnot x) with (- x - 1) by lia.
rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* A symbolic value that reads no atom but a0's (atom 10) has the same value in every valuation that
   agrees on atom 10; fw_E0 v is the one that gives every atom the value v. *)
Fixpoint uses10 (e : sv) : bool :=
  match e with
  | SLit _ => true
  | SOff n _ => Nat.eqb n 10
  | SAlu _ a b | SAluw _ a b | SMd _ a b | SMdw _ a b => uses10 a && uses10 b
  | SExt _ _ a => uses10 a
  | SData _ _ _ => false
  | SF1 _ a => uses10 a
  | SF2 _ a b => uses10 a && uses10 b
  | SF3 _ a b c => uses10 a && uses10 b && uses10 c
  end.
Lemma denot10 : forall E E' e, uses10 e = true -> ew E 10 = ew E' 10 -> sv_denot E e = sv_denot E' e.
Proof.
intros E E' e Hu HE. induction e; cbn [uses10] in Hu; cbn [sv_denot]; try discriminate;
try (apply andb_prop in Hu as [Ha Hb]; rewrite (IHe1 Ha), (IHe2 Hb); reflexivity).
- reflexivity.
- apply Nat.eqb_eq in Hu. subst n. rewrite HE. reflexivity.
- rewrite (IHe Hu). reflexivity.
- rewrite (IHe Hu). reflexivity.
- apply andb_prop in Hu as [Hab Hc]. apply andb_prop in Hab as [Ha Hb].
  rewrite (IHe1 Ha), (IHe2 Hb), (IHe3 Hc). reflexivity.
Qed.
Definition fw_E0 (v : Z) : env := mkEnv (fun _ => Z_to_bv 64 v) (fun _ => []).
(* The byte a store of e leaves, checked against byte j of fw_bytes v for every v of [lo, lo + n). *)
Definition fw_byte_ok (e : sv) (j : nat) (v : Z) : bool :=
  bv_unsigned (byte_of_word (sv_denot (fw_E0 v) e) 0) =? nth j (fw_bytes v) 0.
Lemma fw_byte_check : forall (e : sv) (j : nat) (lo n : Z),
  fw_zall (fw_byte_ok e j) (Z.to_nat n) lo = true -> uses10 e = true ->
  forall E v, ew E 10 = Z_to_bv 64 v -> lo <= v < lo + n -> 0 <= n ->
  bv_unsigned (byte_of_word (sv_denot E e) 0) = nth j (fw_bytes v) 0.
Proof.
intros e j lo n Hz Hu E v Hv Hr Hn.
rewrite (denot10 E (fw_E0 v) e Hu) by (rewrite Hv; reflexivity).
apply Z.eqb_eq. apply (fw_zall_spec (fw_byte_ok e j) (Z.to_nat n) lo Hz v). lia.
Qed.
(* The UBSan check `bltu ~o, k` is not taken when o + k does not wrap. *)
Lemma fw_trap_ltu : forall E o k m, ew E 11 = Z_to_bv 64 o -> 0 <= o -> 0 <= k -> o + k < 2 ^ 64 ->
  zcanon m = 2 ^ 64 - 1 ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_XOR (SOff 11 0) (SLit m))) (sv_denot E (SLit k)) = false.
Proof.
intros E o k m H11 Ho Hk Hok Hm. rewrite branch_ltu_U, U_SAlu, U_SLit, U_SLit.
rewrite (U_atom E 11 o H11) by lia.
rewrite Hm. cbn [zalu_raw]. change (2 ^ 64 - 1) with 18446744073709551615. rewrite fw_lxor_ones by lia.
unfold zcanon, M64. rewrite !Z.mod_small by lia. apply Z.ltb_ge. lia.
Qed.
Section f.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
(* ---- the walk's symbolic start states ---------------------------------------------------------
   Atoms 0..31 are the registers at entry (a0 = v is atom 10, a1 = o atom 11, a2 = c atom 12), atom
   32 is the shadow offset that the shadow cell holds. Regions: the 16-byte frame below sp, the GOT
   slot of the shadow cell (A_OBJ 1), the shadow cell (A_OBJ 31), and, when the call writes, the n
   bytes of the buffer at o; the shadow entry of the buffer is the premise range_addressable. *)
Definition SB_FW : Z := 0x7fff8000.
Definition Bx_FW : sv := SOff 32 0.
Definition Bspan_FW : Z * Z := (SB_FW, SB_FW + 2 ^ 44 - 1).
Definition fw_rs0 : YP09.smem := [stack_region FW_FRAME; got_regionP; bcell_regionP 32].
Definition fw_buf (n : Z) : YP09.region := YP09.mkRegion (Some 11%nat) 0 n 0 n [].
Definition fw_G (lo10 hi10 lo11 hi11 lo12 hi12 : Z) : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF lo10 hi10 0); (11%nat, mkAF lo11 hi11 0);
            (12%nat, mkAF lo12 hi12 0); (32%nat, mkAF SB_FW SB_FW 0) ] [] [].
Definition fw_ss (rs : YP09.smem) (G : facts) : sstate := mkSS AF_reac_identity_fw_str sr_atoms rs None G.
Definition fw_E (regs : bvmap 5 word) : env := Eimg (Ereg regs [Z_to_bv 64 SB_FW]).
(* The bytes a run may write: its frame and the buffer. *)
Definition fw_P (sp o n a : Z) : Prop := (sp - FW_FRAME <= a < sp) \/ (o <= a < o + n).
Lemma fw_le_byte1 : forall b : byte, Z_to_bv 8 (le_byte (bv_unsigned b) 1 0) = b.
Proof.
intros b. unfold le_byte. pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
replace (8 * Z.of_nat 1) with 8 by reflexivity. replace (8 * Z.of_nat 0) with 0 by reflexivity.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. apply Z_to_bv_bv_unsigned.
Qed.
(* The bytes a region's chunks say are at o, one CVal 1 chunk per byte. *)
Lemma fw_garr8 : forall E m (cs : list YP09.chunk) o (l : list Z),
  Forall (YP09.chunk_ok SEGS E m o) cs ->
  (forall j, (j < length l)%nat -> exists e, In (YP09.mkChunk (Z.of_nat j) (CVal 1 e)) cs /\
     bv_unsigned (byte_of_word (sv_denot E e) 0) = nth j l 0) ->
  garr8 SEGS m o l.
Proof.
intros E m cs o l Hcs Hl j Hj. destruct (Hl j Hj) as (e & Hin & He).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc.
destruct (Hc 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
cbn [YP09.c_off YP09.c_val cbyte] in Hb1, Hb2. injection Hb1 as Hb1. subst b.
pose proof (bv_unsigned_in_range 8 (byte_of_word (sv_denot E e) 0)) as Hr. change (bv_modulus 8) with 256 in Hr.
rewrite <- He. split; [|lia].
intros kk Hk. assert (kk = 0%nat) by lia. subst kk.
replace (o + Z.of_nat j + Z.of_nat 0) with (o + Z.of_nat j + 0) by lia. rewrite Hb2. f_equal.
symmetry. apply fw_le_byte1.
Qed.
(* A run writes only its regions' windows: the memory outside P stays as it was. *)
Lemma fw_keep_step : forall Ef rs (m0 m1 m2 : word -> option byte) (P : Z -> Prop),
  frame_of Ef rs m1 m2 -> (forall a, in_wrange Ef rs a -> P a) ->
  (forall x : word, ~ P (bv_unsigned x) -> m1 x = m0 x) -> forall x : word, ~ P (bv_unsigned x) -> m2 x = m0 x.
Proof. intros Ef rs m0 m1 m2 P HF Hw HM x Hx. rewrite (HF x); [exact (HM x Hx) | intros Hin; exact (Hx (Hw _ Hin))]. Qed.
Section h.
Variable B : asyms.
(* The caller's buffer [o, o + n): each byte in a heap block or a side-stack frame of the caller's
   state (IdentBCJ.tdst_ok), one the caller lets the call write (IdentBCJ.twr_ok), and its shadow allows
   each byte. *)
Definition fw_dest_ok (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (lyc : alayout) (Sc : astate) (own : list (Z * Z)) (W : world SEGS) (memc : word -> option byte)
  (sp o n : Z) : Prop :=
  tdst_ok B lyc Sc o n /\
  twr_ok B STK sp0 FP ly S lyc Sc own W memc sp o n /\
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF o n.
(* What the call leaves: the same journal, the callee-saved registers, and either the bytes and the
   length it wrote, or -1; IdentBCJ.tcj_kept says what it kept. *)
Definition treac_identity_fw_str_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (v o c : Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    (if fw_writes o c then
      getr regs2 10 = w64 (reac_identity_fw_str_c.L v) /\
      garr8 SEGS (mrestrict (w_H W2) mem2) o (fw_bytes v) /\
      tcj_kept B REAC_IDENTITY_FW_STR_STK lyc Sc W memc W2 mem2 (spZ regs) (fun a => o <= a < o + fw_n v)
    else
      getr regs2 10 = w64 (-1) /\
      tcj_kept B REAC_IDENTITY_FW_STR_STK lyc Sc W memc W2 mem2 (spZ regs) (fun _ => False)).
Definition treac_identity_fw_str_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (v o c : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) ->
  getr regs 10 = w64 v -> getr regs 11 = w64 o -> getr regs 12 = w64 c ->
  0 <= v < 65536 -> 0 <= o < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_IDENTITY_FW_STR_STK -> spZ regs <= sp0 ->
  (fw_writes o c = true -> fw_dest_ok STK sp0 FP ly S lyc Sc own W memc (spZ regs) o (fw_n v)) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_reac_identity_fw_str) regs memc mdc)
    (treac_identity_fw_str_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs v o c).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_identb) (PI := PI).
Lemma fw_E_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (fw_E regs) n = getr regs r.
Proof.
intros regs n r Hn. unfold fw_E. rewrite Eimg_low; [apply ew_Ereg_nat; exact Hn|].
pose proof (bv_unsigned_in_range 5 r) as Q. change (bv_modulus 5) with 32 in Q. unfold A_TEXT. lia.
Qed.
Lemma fw_E_32 : forall regs, ew (fw_E regs) 32 = Z_to_bv 64 SB_FW.
Proof. intros regs. unfold fw_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma fw_E_obj : forall regs i, (i < 32)%nat -> ew (fw_E regs) (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)).
Proof. intros regs i Hi. unfold fw_E. apply Eimg_img. unfold A_OBJ, A_TEXT, A_LIM. lia. Qed.
(* The facts of the start state that come from the caller's journal: the stack and the image's two
   cells of the memory-checking runtime. *)
Lemma fw_base_facts : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= spZ regs - REAC_IDENTITY_FW_STR_STK -> spZ regs <= sp0 ->
  alloc_ceiling <= spZ regs - REAC_IDENTITY_FW_STR_STK /\ 2 ^ 46 <= spZ regs - FW_FRAME /\ spZ regs <= 2 ^ 47 /\
  (forall a, spZ regs - REAC_IDENTITY_FW_STR_STK <= a < spZ regs -> apresent (w_H W) memc a) /\
  rdword (aview SEGS (w_H W) memc) (VAL (A_OBJ 31)) = Some SHADOW_OFF /\
  rdword (aview SEGS (w_H W) memc) (VAL (A_OBJ 1)) = Some (VAL (A_OBJ 31)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ Hsp1 Hsp2.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
unfold REAC_IDENTITY_FW_STR_STK, ESTACK, FW_FRAME in *. split; [lia|]. split; [lia|]. split; [lia|]. split; [intros a Ha; apply Hpres; lia|]. split; assumption.
Qed.
(* A byte of a buffer that lies in the caller's heap blocks or side-stack frames is app memory below
   the allocator's ceiling, off the shadow band, and off the image. *)
Lemma fw_dst_byte : forall lyc Sc W memc mdc o n a,
  AR SEGS B lyc Sc W memc mdc -> tdst_ok B lyc Sc o n -> o <= a < o + n ->
  4096 <= a < alloc_ceiling /\ (a < kLowShadowBeg \/ kHighMemBeg <= a) /\ (a < IMG_LO \/ IMG_TOP <= a).
Proof.
intros lyc Sc W memc mdc o n a HAR Hd Ha.
destruct (Hd a Ha) as [(b & m & Hin & Hb) | (cid & pos & Hin & Hr)].
- destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & H4096 & Hcl & Happ & _).
  pose proof (blk_off_imgP B lyc Sc W memc mdc b m HAR Hin) as Hoff.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. split; [lia|]. split; lia.
- unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hin) as (Hf1 & Hf2 & Happ).
  assert (Hcl : ~ in_zr a (ly_img lyc) /\ ~ in_img SEGS a)
    by (apply (al_client_img _ _ LAWS _ _ _ _ _ a HAR); right; left; exists cid, pos; split; [exact Hin | exact Hr]).
  destruct HAR as (_ & LG & _). pose proof (pa_img_cover lyc Sc mdc LG) as (Hc1 & Hc2).
  destruct Hcl as (Hni & _). unfold in_zr in Hni.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. split; [lia|]. split; lia.
Qed.
Lemma fw_entry_w : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) v o c n lo10 hi10,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 10 = w64 v -> getr regs 11 = w64 o -> getr regs 12 = w64 c ->
  lo10 <= v <= hi10 -> 0 <= v < 65536 -> 0 < o < 2 ^ 64 -> 8 <= c < 2 ^ 64 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_IDENTITY_FW_STR_STK -> spZ regs <= sp0 ->
  fw_dest_ok STK sp0 FP ly S lyc Sc own W memc (spZ regs) o n -> (n = 6 \/ n = 7) ->
  st_ok_pi SEGS VAL (fw_E regs) (fw_ss (fw_rs0 ++ [fw_buf n]) (fw_G lo10 hi10 1 (2 ^ 47 - 1 - n) 8 (2 ^ 64 - 1)))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_identity_fw_str)) memc (seg_rom SEGS))) /\
  sh_ok SEGS Bx_FW [mkSHE 11 0 n] (fw_E regs) (mrestrict (w_H W) memc).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs v o c n lo10 hi10
  HJ H10 H11 H12 Hv10 Hv Ho Hc Hal Hsp1 Hsp2 (Hdst & Hbytes & Hrange) Hn.
destruct (fw_base_facts STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ Hsp1 Hsp2)
  as (Hac & Hlo & Hhi & Hpres & Kcell & Kgot).
pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR. pose proof (pa_obj_img 31 ltac:(lia)) as HcellR.
pose proof (pa_val_range (A_OBJ 1)) as HV1. pose proof (pa_val_range (A_OBJ 31)) as HV31.
assert (Hn' : 6 <= n <= 7) by (destruct Hn; lia).
assert (Hsap : o + n <= spZ regs - FW_FRAME \/ spZ regs <= o)
  by (apply fw_range_apart; [lia | unfold FW_FRAME; lia | intros a Ha Hin; apply (proj2 (proj2 (proj2 (Hbytes a Ha)))); unfold ESTACK, FW_FRAME in *; lia]).
assert (Hdb : forall a, o <= a < o + n ->
  4096 <= a < alloc_ceiling /\ (a < kLowShadowBeg \/ kHighMemBeg <= a) /\ (a < IMG_LO \/ IMG_TOP <= a))
  by (intros a Ha; exact (fw_dst_byte lyc Sc W memc mdc o n a (proj1 HJ) Hdst Ha)).
assert (Hoff : o + n <= IMG_LO \/ IMG_TOP <= o)
  by (apply fw_range_apart; [lia | lia | intros a Ha Hin; destruct (Hdb a Ha) as (_ & _ & Hq); lia]).
assert (Hhm : o + n <= 2 ^ 47 - 1)
  by (destruct (Hdb (o + n - 1) ltac:(lia)) as (Hq & _); pose proof asan_consts as (C1 & _); lia).
pose proof (fw_E_reg regs 10 10%bv eq_refl) as E10. rewrite H10 in E10.
pose proof (fw_E_reg regs 11 11%bv eq_refl) as E11. rewrite H11 in E11.
pose proof (fw_E_reg regs 12 12%bv eq_refl) as E12. rewrite H12 in E12.
pose proof (fw_E_32 regs) as E32.
pose proof (fw_E_obj regs 1 ltac:(lia)) as EO1. pose proof (fw_E_obj regs 31 ltac:(lia)) as EO31.
assert (Usp : bv_unsigned (ew (fw_E regs) 2) = spZ regs) by (rewrite (fw_E_reg regs 2 2%bv eq_refl); reflexivity).
unfold w64 in E10, E11, E12.
assert (VB : forall kk vv, ew (fw_E regs) kk = Z_to_bv 64 vv -> 0 <= vv < 2 ^ 64 -> base_val (fw_E regs) (Some kk) = vv)
  by (intros kk vv Hk Hvv; cbn [base_val]; rewrite Hk; apply unsigned_lit_small; exact Hvv).
split.
- rewrite restrict_mkst_fx. unfold fw_ss. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + destruct Hn as [-> | ->]; vm_compute; reflexivity.
  + unfold fw_rs0, stack_region, got_regionP, bcell_regionP, fw_buf. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. unfold FW_FRAME in *. split; [lia|]. split; [lia|]. split; [|constructor].
      intros oo Hoo. apply (apresent_writable SEGS). apply Hpres. unfold REAC_IDENTITY_FW_STR_STK, ESTACK, FW_FRAME. lia.
    * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1) by lia. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS _ _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 31) 0) (VAL (A_OBJ 31)));
      [ cbn [sv_denot]; rewrite EO31, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
    * rewrite (VB (A_OBJ 31) (VAL (A_OBJ 31)) EO31) by lia. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS _ _ (VAL (A_OBJ 31)) 0 8 Bx_FW SB_FW);
      [ unfold Bx_FW; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB_FW; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
    * rewrite (VB 11%nat o E11) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
      intros oo Hoo. apply (apresent_writable SEGS). exact (proj1 (proj2 (Hbytes (o + oo) ltac:(lia)))).
  + apply pairwise_disjoint_of_extents.
    unfold fw_rs0, stack_region, got_regionP, bcell_regionP, fw_buf, extent_of_region.
    cbn [app map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 11%nat o E11) by lia. rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1) by lia.
    rewrite (VB (A_OBJ 31) (VAL (A_OBJ 31)) EO31) by lia.
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold FW_FRAME in *.
    repeat split; lia.
  + split; [|split; exact I]. cbn [f_atoms atoms_ok fw_G]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E11, E12, E32, !unsigned_lit_small by (unfold SB_FW; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold FW_FRAME in *.
    repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok. constructor; [|constructor]. unfold shent_ok, app_apart, Bx_FW. cbn [she_m she_lo she_hi].
  rewrite (U_atom _ 32 SB_FW E32) by (unfold SB_FW; lia). rewrite (U_atom _ 11 o E11) by lia. split.
  + rewrite Z.add_0_r, Z.sub_0_r. exact Hrange.
  + intros a Ha. destruct (Hdb a ltac:(lia)) as (_ & Hq & _). unfold kLowShadowBeg, kHighMemBeg, SB_FW in *. lia.
Qed.
Lemma fw_entry_r : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) v o c lo11 hi11 lo12 hi12,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 10 = w64 v -> getr regs 11 = w64 o -> getr regs 12 = w64 c ->
  0 <= v < 65536 -> 0 <= o < 2 ^ 64 -> 0 <= c < 2 ^ 64 -> lo11 <= o <= hi11 -> lo12 <= c <= hi12 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_IDENTITY_FW_STR_STK -> spZ regs <= sp0 ->
  st_ok_pi SEGS VAL (fw_E regs) (fw_ss fw_rs0 (fw_G 0 65535 lo11 hi11 lo12 hi12))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_identity_fw_str)) memc (seg_rom SEGS))) /\
  sh_ok SEGS Bx_FW [] (fw_E regs) (mrestrict (w_H W) memc).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs v o c lo11 hi11 lo12 hi12
  HJ H10 H11 H12 Hv Ho Hc Ho' Hc' Hal Hsp1 Hsp2.
destruct (fw_base_facts STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ Hsp1 Hsp2)
  as (Hac & Hlo & Hhi & Hpres & Kcell & Kgot).
pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR. pose proof (pa_obj_img 31 ltac:(lia)) as HcellR.
pose proof (pa_val_range (A_OBJ 1)) as HV1. pose proof (pa_val_range (A_OBJ 31)) as HV31.
pose proof (fw_E_reg regs 10 10%bv eq_refl) as E10. rewrite H10 in E10.
pose proof (fw_E_reg regs 11 11%bv eq_refl) as E11. rewrite H11 in E11.
pose proof (fw_E_reg regs 12 12%bv eq_refl) as E12. rewrite H12 in E12.
pose proof (fw_E_32 regs) as E32.
pose proof (fw_E_obj regs 1 ltac:(lia)) as EO1. pose proof (fw_E_obj regs 31 ltac:(lia)) as EO31.
assert (Usp : bv_unsigned (ew (fw_E regs) 2) = spZ regs) by (rewrite (fw_E_reg regs 2 2%bv eq_refl); reflexivity).
unfold w64 in E10, E11, E12.
assert (VB : forall kk vv, ew (fw_E regs) kk = Z_to_bv 64 vv -> 0 <= vv < 2 ^ 64 -> base_val (fw_E regs) (Some kk) = vv)
  by (intros kk vv Hk Hvv; cbn [base_val]; rewrite Hk; apply unsigned_lit_small; exact Hvv).
split; [|constructor].
rewrite restrict_mkst_fx. unfold fw_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold fw_rs0, stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. unfold FW_FRAME in *. split; [lia|]. split; [lia|]. split; [|constructor].
    intros oo Hoo. apply (apresent_writable SEGS). apply Hpres. unfold REAC_IDENTITY_FW_STR_STK, ESTACK, FW_FRAME. lia.
  + rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1) by lia. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS _ _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 31) 0) (VAL (A_OBJ 31)));
    [ cbn [sv_denot]; rewrite EO31, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + rewrite (VB (A_OBJ 31) (VAL (A_OBJ 31)) EO31) by lia. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS _ _ (VAL (A_OBJ 31)) 0 8 Bx_FW SB_FW);
    [ unfold Bx_FW; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB_FW; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
- apply pairwise_disjoint_of_extents.
  unfold fw_rs0, stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1) by lia. rewrite (VB (A_OBJ 31) (VAL (A_OBJ 31)) EO31) by lia.
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold FW_FRAME in *.
  repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok fw_G]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E10, E11, E12, E32, !unsigned_lit_small by (unfold SB_FW; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold FW_FRAME in *.
  repeat match goal with |- _ /\ _ => split end; lia.
Qed.
(* A walk that changed no byte outside its frame [sp - 16, sp) and the bytes E (none of them in the
   image), and lost no byte, kept what IdentBCJ.tcj_kept says for any window [sp - STKw, sp) that holds
   the frame and was present. *)
Lemma fw_tcj : forall STKw lyc Sc W memc mdc mem2 sp (E : Z -> Prop),
  AR SEGS B lyc Sc W memc mdc ->
  FW_FRAME <= STKw -> alloc_ceiling <= sp - STKw -> sp <= 2 ^ 47 ->
  (forall a, in_img SEGS a -> ~ E a) ->
  (forall x : word, ~ (sp - FW_FRAME <= bv_unsigned x < sp) -> ~ E (bv_unsigned x) ->
     mrestrict (w_H W) mem2 x = mrestrict (w_H W) memc x) ->
  mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) mem2) ->
  (forall a, sp - STKw <= a < sp -> apresent (w_H W) memc a) ->
  tcj_kept B STKw lyc Sc W memc W mem2 sp E.
Proof.
intros STKw lyc Sc W memc mdc mem2 sp E HAR Hw16 Hc H47 HimgE HK HG Hpw.
pose proof asan_consts as (C1 & _).
assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - FW_FRAME <= a < sp) -> ~ E a ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a).
{ intros a Ha Hw He. unfold aview, mbyte. rewrite HK; [reflexivity | |];
  rewrite unsigned_lit_small by lia; assumption. }
assert (KP : forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a).
{ intros a (Hh & b & Hb). split; [exact Hh|]. specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG.
  rewrite Hh, Hb in HG. destruct (mem2 (Z_to_bv 64 a)) as [b'|] eqn:Em; [exists b'; reflexivity|].
  exfalso. apply HG; [discriminate | reflexivity]. }
unfold FW_FRAME in *.
split; [intros a Ha Hw He; apply KV; [lia | lia | exact He]|].
split.
{ intros b m i Hin Hi He. destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & H4096 & Hcl & _).
  apply KV; [lia | lia | exact He]. }
split.
{ intros a Hi Hns Herr. pose proof (pa_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl.
  apply KV; [lia | lia | exact (HimgE a Hi)]. }
split.
{ intros cid pos a Hin Hr He. destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hin) as (Hf1 & Hf2 & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfb.
  apply KV; [| | exact He]; destruct Hr as [Hr|Hr]; unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Hr;
  cbn [fst snd] in Hr; lia. }
split; [intros a Ha Hw Hp; exact (KP a Hp)|].
intros a Ha. exact (KP a (Hpw a Ha)).
Qed.
(* ---- walk tactics ------------------------------------------------------------------------------ *)
Ltac fw_ewn := repeat rewrite ew_ewset_other by lia.
Ltac fw_ewn_in H := repeat rewrite ew_ewset_other in H by lia.
(* The run's write right: the frame is in the caller's window below sp, the image cells are not
   written, and the caller lets the call write the buffer. *)
Ltac fw_awr regs sp0 o Usp E11 Hsp1 Hsp2 Hbytes :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0' fp b0 bc ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia |]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
    [ reflexivity | fw_ewn; rewrite Usp; lia
    | cbn [YP09.r_wlo YP09.r_whi]; unfold REAC_IDENTITY_FW_STR_STK, ESTACK, FW_FRAME in *; lia
    | cbn [YP09.r_wlo YP09.r_whi]; lia | ]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 11%nat o);
    [ reflexivity | fw_ewn; rewrite E11; apply unsigned_lit_small; lia
    | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; exact (proj1 (Hbytes a ltac:(lia))) | ] ].
(* Where a run may write: in its frame or in the buffer. *)
Ltac fw_wrP Usp E11 :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros a (r & Hin & Ha); vm_compute in Hin;
  repeat destruct Hin as [<- | Hin]; try destruct Hin;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; fw_ewn_in Ha;
  try rewrite Usp in Ha; try (rewrite E11, unsigned_lit_small in Ha by lia);
  unfold fw_P, FW_FRAME in *; lia.
(* After a run: what it kept outside the frame and the buffer, and that it lost no byte. *)
Ltac fw_keep Usp E11 HKP HGP :=
  let HKP2 := fresh "HKP2" in
  lazymatch type of HKP with forall x : word, ~ ?P (bv_unsigned x) -> _ = mrestrict ?H ?m0 x =>
  lazymatch goal with HFr : frame_of ?Ef ?rs (mrestrict ?H1 ?mm1) ?m2, HG : mem_grows _ ?m2 |- _ =>
    pose proof (fw_keep_step Ef rs (mrestrict H m0) (mrestrict H1 mm1) m2 P HFr ltac:(fw_wrP Usp E11) HKP) as HKP2;
    clear HKP; rename HKP2 into HKP;
    let HGP2 := fresh "HGP2" in pose proof (mem_grows_trans _ _ _ HGP HG) as HGP2;
    clear HGP HG; rename HGP2 into HGP
  end end;
  repeat match goal with Hf : frame_of _ _ _ _ |- _ => clear Hf end.
(* The UBSan pointer-overflow branch to the trap word is not taken. *)
Ltac fw_trap E11 Hhm :=
  exfalso;
  lazymatch type of E11 with ew _ 11 = Z_to_bv 64 ?o =>
  lazymatch goal with Hc : branch_taken BC_LTU (sv_denot ?Ef (SAlu ALU_XOR (SOff 11 0) (SLit ?m))) (sv_denot ?Ef (SLit ?kk)) = true |- _ =>
    rewrite (fw_trap_ltu Ef o kk m) in Hc;
    [ discriminate Hc | fw_ewn; exact E11 | lia | lia | lia | vm_compute; reflexivity ]
  end end.
(* At the return: the machine is at the caller's return address with the run's journal and the
   callee-saved registers. *)
Ltac fw_ret W regs lyc Sc E1 Hra Hsegs HAE R10 R1 Ef msf :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ef0 ?ssf (restrict (w_H W) ?msf0) |- _ =>
  prreg HS (10%bv : bv 5) R10; prreg HS (1%bv : bv 5) R1;
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  let mat' := fresh "mat" in intros mat'; cbv beta;
  exists lyc, Sc, (ms_regs msf0), (ms_mem msf0); eexists;
  split; [rewrite R1; fw_ewn; rewrite ?E1; rewrite Hra; reflexivity|];
  split; [apply (ajournal_materialize SEGS B LAWS Hsegs); assumption|];
  split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [Z_to_bv 64 SB_FW] HS);
          [env_agree_chain HAE | vm_compute; reflexivity]|];
  split; [reflexivity|]; split; [apply Permutation_refl|];
  pose (Ef := Ef0); pose (msf := msf0)
  end.
(* The walk: run to the next stop; a UBSan branch to the trap word is not taken; the return ends it. *)
Ltac fw_go W regs lyc Sc sp0 o Usp E1 E11 Hsp1 Hsp2 Hbytes Hhm Hra Hsegs HAE HKP HGP R10 R1 Ef msf :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_tok RUN HS HJ SHOK Bspan_FW; [fw_awr regs sp0 o Usp E11 Hsp1 Hsp2 Hbytes |];
  fw_keep Usp E11 HKP HGP;
  lazymatch goal with
  | HS' : st_ok_pi _ _ _ ?ss _, SHOK' : sh_ok _ _ ?SH _ _ |- _ =>
    let K := eval vm_compute in (run_K A_LIM Bx_FW SH ss) in
    let why := lazymatch paj_tables RUN with (?tpi, ?tw) => psym_why_tok tpi tw K Bx_FW Bspan_FW SH (start K Bx_FW Bspan_FW SH ss) end in
    lazymatch why with
    | SR_jalr _ => fw_ret W regs lyc Sc E1 Hra Hsegs HAE R10 R1 Ef msf
    | SR_branch _ _ _ =>
        psrr_branch_tok RUN BR HS' SHOK' Bspan_FW;
        [ fw_trap E11 Hhm
        | fw_go W regs lyc Sc sp0 o Usp E1 E11 Hsp1 Hsp2 Hbytes Hhm Hra Hsegs HAE HKP HGP R10 R1 Ef msf ]
    | _ => let pc := eval vm_compute in (ss_pc ss) in idtac "STUCK" pc why; fail
    end
  end end.
(* The bytes the buffer holds at the return, from the final state's region of atom 11. *)
Ltac fw_find11 l :=
  lazymatch l with
  | (YP09.mkRegion (Some 11%nat) ?lo ?hi ?wlo ?whi ?cs) :: _ => constr:(YP09.mkRegion (Some 11%nat) lo hi wlo whi cs)
  | _ :: ?t => fw_find11 t
  end.
Ltac fw_bytes_at W v o lo len n E10 E11 Ef msf :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict (w_H W) _) |- _ =>
  let HRok := fresh "HRok" in let HR11 := fresh "HR11" in let HCH := fresh "HCH" in
  let B11 := fresh "B11" in let E10f := fresh "E10f" in
  pose proof (st_ok_mem_ok SEGS _ _ _ HS) as (_ & HRok & _);
  lazymatch type of HRok with Forall _ ?rs =>
    let rs' := eval vm_compute in rs in
    let r := fw_find11 rs' in
    assert (HR11 : YP09.region_ok SEGS Ef (ms_mem (restrict (w_H W) msf)) r)
      by (apply (proj1 (Forall_forall _ _) HRok); change rs with rs'; cbn [In];
          repeat (first [left; reflexivity | right]))
  end;
  destruct HR11 as (_ & _ & _ & HCH); cbn [YP09.r_chunks YP09.r_base base_val] in HCH;
  assert (B11 : bv_unsigned (ew Ef 11) = o)
    by (unfold Ef; fw_ewn; rewrite E11; apply unsigned_lit_small; lia);
  assert (E10f : ew Ef 10 = Z_to_bv 64 v) by (unfold Ef; fw_ewn; exact E10);
  rewrite B11 in HCH;
  apply (fw_garr8 _ _ _ _ _ HCH);
  let j := fresh "j" in let Hj := fresh "Hj" in
  intros j Hj; rewrite fw_bytes_len, n in Hj; cbn in Hj;
  do 8 (first
    [ solve [exfalso; lia]
    | destruct j as [|j];
      [ eexists; split;
        [ cbn [In]; repeat (first [left; reflexivity | right])
        | apply (fw_byte_check _ _ lo len);
          [ vm_compute; reflexivity | vm_compute; reflexivity | exact E10f | lia | lia ] ]
      | ] ])
  end.
Theorem pb_reac_identity_fw_str : treac_identity_fw_str_spec.
Proof.
unfold treac_identity_fw_str_spec.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs v o c HJ Hra H10 H11 H12 Hv Ho Hc Hal Hsp1 Hsp2 Hdest.
pose proof pa_segs_low as Hsegs.
destruct (fw_base_facts STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ Hsp1 Hsp2)
  as (Hac & Hlo & Hhi & Hpres & _ & _).
pose proof (proj1 HJ) as HAR0.
pose proof (fw_E_reg regs 1 1%bv eq_refl) as E1.
pose proof (fw_E_reg regs 10 10%bv eq_refl) as E10. rewrite H10 in E10. unfold w64 in E10.
pose proof (fw_E_reg regs 11 11%bv eq_refl) as E11. rewrite H11 in E11. unfold w64 in E11.
assert (Usp : bv_unsigned (ew (fw_E regs) 2) = spZ regs) by (rewrite (fw_E_reg regs 2 2%bv eq_refl); reflexivity).
assert (HEI : img_env VAL A_LIM (fw_E regs)) by apply Eimg_env.
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SB_FW]) (fw_E regs))
  by (split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
unfold cfg_at.
change (w64 (BASE + AF_reac_identity_fw_str)) with (Z_to_bv 64 (BASE + AF_reac_identity_fw_str)).
unfold treac_identity_fw_str_post.
destruct (fw_writes o c) eqn:Hw.
- specialize (Hdest eq_refl). pose proof Hw as Hw'. unfold fw_writes in Hw'.
  apply andb_prop in Hw' as [Ho0 Hc8]. apply negb_true_iff, Z.eqb_neq in Ho0. apply Z.leb_le in Hc8.
  destruct (Z.ltb_spec v 10000) as [Vs | Vl].
  + assert (Hn6 : fw_n v = 6) by (apply fw_n_short; lia).
    rewrite Hn6 in Hdest |- *. pose proof Hdest as (Hdst & Hbytes & _).
    assert (Hhm : o + 6 <= 2 ^ 47 - 1)
      by (destruct (fw_dst_byte lyc Sc W memc mdc o 6 (o + 6 - 1) HAR0 Hdst ltac:(lia)) as (Hq & _);
          pose proof asan_consts as (C1 & _); lia).
    destruct (fw_entry_w STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs v o c 6 0 9999
      HJ H10 H11 H12 ltac:(lia) Hv ltac:(lia) ltac:(lia) Hal Hsp1 Hsp2 Hdest ltac:(left; reflexivity)) as [HS SHOK].
    change memc with (ms_mem (mkst regs (Z_to_bv 64 (BASE + AF_reac_identity_fw_str)) memc (seg_rom SEGS))) in HJ.
    assert (HKP : forall x : word, ~ fw_P (spZ regs) o 6 (bv_unsigned x) -> mrestrict (w_H W) memc x = mrestrict (w_H W) memc x)
      by (intros; reflexivity).
    pose proof (mem_grows_refl (mrestrict (w_H W) memc)) as HGP.
    fw_go W regs lyc Sc sp0 o Usp E1 E11 Hsp1 Hsp2 Hbytes Hhm Hra Hsegs HAE HKP HGP R10 R1 Ef msf.
    split; [rewrite R10; unfold w64; f_equal; rewrite (proj2 (reac_identity_fw_str_c.reac_identity_fw_str_c3_len v Hv));
            destruct (Z.ltb_spec v 10000); [reflexivity | lia]|].
    split; [fw_bytes_at W v o 0 10000 Hn6 E10 E11 Ef msf|].
    apply (fw_tcj REAC_IDENTITY_FW_STR_STK lyc Sc W memc mdc _ (spZ regs) _ HAR0 ltac:(unfold REAC_IDENTITY_FW_STR_STK, ESTACK; lia) Hac Hhi);
    [ intros a Ha Hin; cbv beta in Hin; pose proof (pa_img_range a Ha); destruct (fw_dst_byte lyc Sc W memc mdc o _ a HAR0 Hdst Hin) as (_ & _ & Hq); lia
    | intros x Hx1 Hx2; apply HKP; cbv beta in Hx2; unfold fw_P; intros [Hq|Hq]; [exact (Hx1 Hq) | exact (Hx2 Hq)]
    | exact HGP | exact Hpres ].
  + assert (Hn7 : fw_n v = 7) by (apply fw_n_long; lia).
    rewrite Hn7 in Hdest |- *. pose proof Hdest as (Hdst & Hbytes & _).
    assert (Hhm : o + 7 <= 2 ^ 47 - 1)
      by (destruct (fw_dst_byte lyc Sc W memc mdc o 7 (o + 7 - 1) HAR0 Hdst ltac:(lia)) as (Hq & _);
          pose proof asan_consts as (C1 & _); lia).
    destruct (fw_entry_w STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs v o c 7 10000 65535
      HJ H10 H11 H12 ltac:(lia) Hv ltac:(lia) ltac:(lia) Hal Hsp1 Hsp2 Hdest ltac:(right; reflexivity)) as [HS SHOK].
    change memc with (ms_mem (mkst regs (Z_to_bv 64 (BASE + AF_reac_identity_fw_str)) memc (seg_rom SEGS))) in HJ.
    assert (HKP : forall x : word, ~ fw_P (spZ regs) o 7 (bv_unsigned x) -> mrestrict (w_H W) memc x = mrestrict (w_H W) memc x)
      by (intros; reflexivity).
    pose proof (mem_grows_refl (mrestrict (w_H W) memc)) as HGP.
    fw_go W regs lyc Sc sp0 o Usp E1 E11 Hsp1 Hsp2 Hbytes Hhm Hra Hsegs HAE HKP HGP R10 R1 Ef msf.
    split; [rewrite R10; unfold w64; f_equal; rewrite (proj2 (reac_identity_fw_str_c.reac_identity_fw_str_c3_len v Hv));
            destruct (Z.ltb_spec v 10000); [lia | reflexivity]|].
    split; [fw_bytes_at W v o 10000 55536 Hn7 E10 E11 Ef msf|].
    apply (fw_tcj REAC_IDENTITY_FW_STR_STK lyc Sc W memc mdc _ (spZ regs) _ HAR0 ltac:(unfold REAC_IDENTITY_FW_STR_STK, ESTACK; lia) Hac Hhi);
    [ intros a Ha Hin; cbv beta in Hin; pose proof (pa_img_range a Ha); destruct (fw_dst_byte lyc Sc W memc mdc o _ a HAR0 Hdst Hin) as (_ & _ & Hq); lia
    | intros x Hx1 Hx2; apply HKP; cbv beta in Hx2; unfold fw_P; intros [Hq|Hq]; [exact (Hx1 Hq) | exact (Hx2 Hq)]
    | exact HGP | exact Hpres ].
- pose proof Hw as Hw'. unfold fw_writes in Hw'. destruct (Z.eqb_spec o 0) as [O0 | O0].
  + destruct (fw_entry_r STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs v o c 0 0 0 (2 ^ 64 - 1)
      HJ H10 H11 H12 Hv Ho Hc ltac:(lia) ltac:(lia) Hal Hsp1 Hsp2) as [HS0 SHOK].
    (* a1 is 0: the walk knows it, so the test of a1 at 0x84078 is decided. *)
    pose proof (st_ok_pi_pin_reg' _ _ _ (11%bv : bv 5) 0 HS0
      ltac:(rewrite restrict_mkst_fx; cbn [ms_regs mkst]; rewrite H11, O0; reflexivity) ltac:(vm_compute; reflexivity)) as HS.
    clear HS0.
    change memc with (ms_mem (mkst regs (Z_to_bv 64 (BASE + AF_reac_identity_fw_str)) memc (seg_rom SEGS))) in HJ.
    assert (HKP : forall x : word, ~ fw_P (spZ regs) o 0 (bv_unsigned x) -> mrestrict (w_H W) memc x = mrestrict (w_H W) memc x)
      by (intros; reflexivity).
    pose proof (mem_grows_refl (mrestrict (w_H W) memc)) as HGP.
    assert (Hhm : o + 0 <= 2 ^ 47 - 1) by lia.
    fw_go W regs lyc Sc sp0 o Usp E1 E11 Hsp1 Hsp2 Usp Hhm Hra Hsegs HAE HKP HGP R10 R1 Ef msf.
    split; [rewrite R10; unfold w64; apply bv_eq; reflexivity|].
    apply (fw_tcj REAC_IDENTITY_FW_STR_STK lyc Sc W memc mdc _ (spZ regs) _ HAR0 ltac:(unfold REAC_IDENTITY_FW_STR_STK, ESTACK; lia) Hac Hhi);
    [ intros a Ha []
    | intros x Hx1 _; apply HKP; unfold fw_P; intros [Hq|Hq]; [exact (Hx1 Hq) | lia]
    | exact HGP | exact Hpres ].
  + cbn [negb andb] in Hw'. apply Z.leb_gt in Hw'.
    destruct (fw_entry_r STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs v o c 1 (2 ^ 64 - 1) 0 7
      HJ H10 H11 H12 Hv Ho Hc ltac:(lia) ltac:(lia) Hal Hsp1 Hsp2) as [HS SHOK].
    change memc with (ms_mem (mkst regs (Z_to_bv 64 (BASE + AF_reac_identity_fw_str)) memc (seg_rom SEGS))) in HJ.
    assert (HKP : forall x : word, ~ fw_P (spZ regs) o 0 (bv_unsigned x) -> mrestrict (w_H W) memc x = mrestrict (w_H W) memc x)
      by (intros; reflexivity).
    pose proof (mem_grows_refl (mrestrict (w_H W) memc)) as HGP.
    fw_go W regs lyc Sc sp0 o Usp E1 E11 Hsp1 Hsp2 Usp Ho Hra Hsegs HAE HKP HGP R10 R1 Ef msf.
    split; [rewrite R10; unfold w64; apply bv_eq; reflexivity|].
    apply (fw_tcj REAC_IDENTITY_FW_STR_STK lyc Sc W memc mdc _ (spZ regs) _ HAR0 ltac:(unfold REAC_IDENTITY_FW_STR_STK, ESTACK; lia) Hac Hhi);
    [ intros a Ha []
    | intros x Hx1 _; apply HKP; unfold fw_P; intros [Hq|Hq]; [exact (Hx1 Hq) | lia]
    | exact HGP | exact Hpres ].
Qed.
End h.
End f.
End d.
