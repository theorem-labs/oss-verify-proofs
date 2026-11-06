(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the walk of musl's __toread inside libreac/fuzz_pcap (libreac v1.9.0, ASan
   build), proving PFreadM.v's rtoread_contract (a working branch beb05bac2a3) in
   cgif_file_fuzzer's per-function form (the donor's walk / spec of lib/A/AE26.v + AE27.v: one SRr
   theorem over cfg_at, its post apost_base). Theorem: rtoread_contract_proof (any image holding
   the code). The image instances are in their own files: rtoread_contract_asan (PTOREAD) in
   lib/A/Stdio/PFtoreadMWA.v and rtoread_contract_asan_ubsan (PTOREAD_U) in lib/B/Stdio/PFtoreadMWB.v.

   IMAGE ROOT: the ORIGINAL v1.9.0 set -- the pinned fuzz_pcap images,
   unstripped twins (sha256 36da3052c383 asan, c969d83cdd59 asan-ubsan); listing
   fuzz_pcap.objdump.txt (sha256 bf9d80d6e30f; internal record) lines 98961-98998.

   IMAGE-GENERIC AND IMAGE-FREE. The walk is stated over any segment list `segs` whose 37 words at
   the entry `pc` are TOREAD_WORDS (the boolean check toread_code, discharged by computation for each
   image), so ONE proof serves both memory-checking images: asan __toread 0x8e638 (PTOREAD, instance
   in lib/A/Stdio/PFtoreadMWA.v) and asan-ubsan 0x8e504 (PTOREAD_U, instance in
   lib/B/Stdio/PFtoreadMWB.v). This file Requires no image and no image's pc file, so a closure that
   uses one instance does not reach the other image.
   The code is position-independent (pc-relative branches only, no auipc, no absolute
   address), and the two images hold the same 37 words: each instance file checks its image. The other
   hypotheses are the core's laws (AR_laws, the image below kLowMemEnd, wx_segs_nowrap) and the
   stream record's image law (PSourceMeta.v asource_img_laws, SK explicit), as the donor's walks take them; the
   two instances discharge all but asource_img_laws (AR_laws by YG0q.AR_laws_ok, as cgif
   A/ACed.v:73 does, the other two by computation; segs_low_of_b below is the image-free half).

   THE PATH WALKED (the pre fixes it): 29 of the 37 instructions.
     0x00-0x08  frame of 16: sp -= 16, sd ra 8(sp), sd s0 0(sp)          (stack window [sp-16, sp))
     0x0c-0x24  s0 = f; mode = lw +136; mode |= mode - 1; sw mode +136  -> +136 holds -1 (U32M1)
     0x28       beq wpos(+40) wbase(+56): TAKEN, both 0 (source_static), so f->write (0x8e674,
                `jalr a3`) is NOT reached
     0x40-0x50  a0 = lwu flags(+0); a1 = a0 & 4 (F_NORD) = 0 for flags 8 / 24; sd 0 at +32 +40 +56
     0x54       bnez a1: NOT taken, so the F_ERR arm 0x8e6b0-0x8e6b8 (`sw` at +0) is NOT reached
     0x58-0x70  rpos(+8) = rend(+16) = bufbase(+88) + bufsiz(+96) = f + 1304; a0 = (flags<<59)>>63
     0x74       j 0x84; 0x84-0x90 ld ra, ld s0, sp += 16, ret
   No call instruction is executed: no allocator call, no event, no callee contract.

   THE STORES, each placed by the pre: sp-16 .. sp (inside the RTOREAD_STK window, afn_pre) and
   f+8 .. f+24, f+32 .. f+48, f+56 .. f+64, f+136 .. f+140 (inside the FILE block, the pre's
   `In (f, SRC_FILE_BLOCK) (ablocks B ly S)`, and inside the footprint rtoread_fp f). The journal is
   ajournal_exec from ajournal_init over exactly these bytes, so it holds for the token-free
   footprint. The data buffer b is a live block (the pre's `In (b, |C|) (ablocks B ly S)`, added in
   9b4de8c19fc after this lane's gap report: without it b = sp-16 makes the post false), hence below
   alloc_ceiling and off the stack window.

   rule 24: __toread is the function this lane was assigned (a Theorem Labs lane). proof-index
   (built 2026-10-28T21:58:24Z) and git grep on main / ossv/recipes / ossv/candidates /
   release/pau-projects-recipes: no released cgif-form (lib/A, SRr / apost_base) proof of __toread;
   the hits are pcap's plain / ubsan lib/Prog walks (lib/Lib form) and mpv's own form. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK0s YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN01 YO0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YP09 YO0f.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI00 YI04 YI16.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YCbq YC20.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YG0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFreadM.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. The code: the 37 words of __toread, MEASURED in both images.         *)
(* ---------------------------------------------------------------------- *)
Definition TOREAD_WORDS : list Z := [
  0xff010113; 0x00113423; 0x00813023; 0x00050413; 0x08852503; 0x02843583; 0x03843603; 0xfff50693;
  0x00a6e533; 0x08a42423; 0x00c58c63; 0x04843683; 0x00040513; 0x00000593; 0x00000613; 0x000680e7;
  0x00046503; 0x00457593; 0x02043023; 0x02043423; 0x02043c23; 0x02059263; 0x05843583; 0x06043603;
  0x03b51513; 0x00c585b3; 0x00b43423; 0x00b43823; 0x43f55513; 0x0100006f; 0x02056513; 0x00a42023;
  0xfff00513; 0x00813083; 0x00013403; 0x01010113; 0x00008067].

Fixpoint code_from (segs : list Segment) (a : Z) (l : list Z) : bool :=
  match l with
  | [] => true
  | w :: l' =>
      match fetch_word segs (Z_to_bv 64 a) with Some x => Z.eqb (bv_unsigned x) w | None => false end
      && code_from segs (a + 4) l'
  end.
Definition toread_code (segs : list Segment) (pc : Z) : bool := code_from segs pc TOREAD_WORDS.

Lemma code_from_at : forall segs l a n w, code_from segs a l = true -> nth_error l n = Some w ->
  fetch_word segs (Z_to_bv 64 (a + 4 * Z.of_nat n)) = Some (Z_to_bv 32 w).
Proof.
  intros segs l. induction l as [|x l IH]; intros a n w Hc Hn; [destruct n; discriminate|].
  cbn [code_from] in Hc. apply andb_prop in Hc as [Hx Hl].
  destruct n as [|n]; cbn [nth_error] in Hn.
  - injection Hn as <-. replace (a + 4 * Z.of_nat 0) with a by lia.
    destruct (fetch_word segs (Z_to_bv 64 a)) as [y|]; [|discriminate].
    apply Z.eqb_eq in Hx. rewrite <- Hx, Z_to_bv_bv_unsigned. reflexivity.
  - replace (a + 4 * Z.of_nat (S n)) with (a + 4 + 4 * Z.of_nat n) by lia. exact (IH (a + 4) n w Hl Hn).
Qed.

(* The decoded instructions of the walked path (offset from the entry). *)
Lemma D00 : decode_any (Z_to_bv 32 0xff010113) = Some (OpImm ALU_ADD 2 2 4080, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D04 : decode_any (Z_to_bv 32 0x00113423) = Some (Store SZ8 2 1 8, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D08 : decode_any (Z_to_bv 32 0x00813023) = Some (Store SZ8 2 8 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D0c : decode_any (Z_to_bv 32 0x00050413) = Some (OpImm ALU_ADD 8 10 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D10 : decode_any (Z_to_bv 32 0x08852503) = Some (Load SZ4 true 10 10 136, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D14 : decode_any (Z_to_bv 32 0x02843583) = Some (Load SZ8 true 11 8 40, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D18 : decode_any (Z_to_bv 32 0x03843603) = Some (Load SZ8 true 12 8 56, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D1c : decode_any (Z_to_bv 32 0xfff50693) = Some (OpImm ALU_ADD 13 10 4095, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D20 : decode_any (Z_to_bv 32 0x00a6e533) = Some (Op ALU_OR 10 13 10, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D24 : decode_any (Z_to_bv 32 0x08a42423) = Some (Store SZ4 8 10 136, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D28 : decode_any (Z_to_bv 32 0x00c58c63) = Some (Branch BC_EQ 11 12 24, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D40 : decode_any (Z_to_bv 32 0x00046503) = Some (Load SZ4 false 10 8 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D44 : decode_any (Z_to_bv 32 0x00457593) = Some (OpImm ALU_AND 11 10 4, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D48 : decode_any (Z_to_bv 32 0x02043023) = Some (Store SZ8 8 0 32, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D4c : decode_any (Z_to_bv 32 0x02043423) = Some (Store SZ8 8 0 40, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D50 : decode_any (Z_to_bv 32 0x02043c23) = Some (Store SZ8 8 0 56, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D54 : decode_any (Z_to_bv 32 0x02059263) = Some (Branch BC_NE 11 0 36, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D58 : decode_any (Z_to_bv 32 0x05843583) = Some (Load SZ8 true 11 8 88, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D5c : decode_any (Z_to_bv 32 0x06043603) = Some (Load SZ8 true 12 8 96, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D60 : decode_any (Z_to_bv 32 0x03b51513) = Some (ShiftImm ALU_SLL 10 10 59, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D64 : decode_any (Z_to_bv 32 0x00c585b3) = Some (Op ALU_ADD 11 11 12, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D68 : decode_any (Z_to_bv 32 0x00b43423) = Some (Store SZ8 8 11 8, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D6c : decode_any (Z_to_bv 32 0x00b43823) = Some (Store SZ8 8 11 16, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D70 : decode_any (Z_to_bv 32 0x43f55513) = Some (ShiftImm ALU_SRA 10 10 63, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D74 : decode_any (Z_to_bv 32 0x0100006f) = Some (Jal 0 16, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D84 : decode_any (Z_to_bv 32 0x00813083) = Some (Load SZ8 true 1 2 8, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D88 : decode_any (Z_to_bv 32 0x00013403) = Some (Load SZ8 true 8 2 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D8c : decode_any (Z_to_bv 32 0x01010113) = Some (OpImm ALU_ADD 2 2 16, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D90 : decode_any (Z_to_bv 32 0x00008067) = Some (Jalr 0 1 0, 4%Z). Proof. vm_refl_bv. Qed.

(* A Prop wrapper that keeps a disjunction out of lia's case splits. *)
Definition HIDE (P : Prop) : Prop := P.

Ltac gr :=
  repeat first [ rewrite getr_same by reg_neq_tac | rewrite getr_other by reg_neq_tac ];
  rewrite ?getr_zero.

(* ---------------------------------------------------------------------- *)
(* 2. Memory: a store at a literal-offset address, and the bytes it keeps. *)
(* ---------------------------------------------------------------------- *)
Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.

Lemma vaddiZ : forall x i, v_addi (Z_to_bv 64 x) i = Z_to_bv 64 (x + i).
Proof.
  intros x i. unfold v_addi. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma vaddZ : forall x y, v_add (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof.
  intros x y. unfold v_add. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r. reflexivity.
Qed.

Lemma wb_out : forall (m : word -> option byte) a (n : nat) w x,
  0 <= a < 2 ^ 64 -> a + Z.of_nat n <= 2 ^ 64 -> 0 <= x < 2 ^ 64 -> (x < a \/ a + Z.of_nat n <= x) ->
  wbytes m (Z_to_bv 64 a) (word_to_le_bytes n w) (Z_to_bv 64 x) = m (Z_to_bv 64 x).
Proof.
  intros m a n w x Ha Han Hx Hd.
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply u_Z2bv; lia).
  assert (Ux : bv_unsigned (Z_to_bv 64 x) = x) by (apply u_Z2bv; lia).
  destruct Hd as [Hlt | Hge].
  - apply wbytes_below; rewrite ?length_N_to_le_bytes, ?Ua, ?Ux; lia.
  - apply wbytes_above. rewrite length_N_to_le_bytes, Ua, Ux. lia.
Qed.

(* copied from lib/Reusable/YN3h.v:257 wbytes_inside (released), default byte spelled out *)
Lemma wb_in : forall bs (m : word -> option byte) (a x : word),
  bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64 ->
  bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs) ->
  wbytes m a bs x = Some (nth (Z.to_nat (bv_unsigned x - bv_unsigned a)) bs (Z_to_bv 8 0)).
Proof.
  induction bs as [|b rest IH]; intros m a x Hnw Hx; cbn [length] in *; [lia|].
  cbn [wbytes].
  destruct rest as [|b' rest'].
  - cbn [wbytes length] in *.
    replace (bv_eqb x a) with true by (symmetry; unfold bv_eqb; apply Z.eqb_eq; lia).
    replace (Z.to_nat (bv_unsigned x - bv_unsigned a)) with 0%nat by lia. reflexivity.
  - cbn [length] in *.
    assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (apply u_add1; lia).
    destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
    + rewrite wbytes_below by (cbn [length]; rewrite ?Hu1; lia).
      replace (bv_eqb x a) with true by (symmetry; unfold bv_eqb; apply Z.eqb_eq; lia).
      rewrite Heq, Z.sub_diag. reflexivity.
    + rewrite IH by (cbn [length]; rewrite Hu1; lia).
      rewrite Hu1.
      replace (Z.to_nat (bv_unsigned x - bv_unsigned a)) with (S (Z.to_nat (bv_unsigned x - (bv_unsigned a + 1)))) by lia.
      reflexivity.
Qed.

Lemma wb_at : forall (m : word -> option byte) a (n : nat) w (k : nat),
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (k < n)%nat ->
  wbytes m (Z_to_bv 64 a) (word_to_le_bytes n w) (Z_to_bv 64 (a + Z.of_nat k)) =
  Some (Z_to_bv 8 (Z.shiftr (bv_unsigned w) (8 * Z.of_nat k))).
Proof.
  intros m a n w k Ha Han Hk.
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply u_Z2bv; lia).
  assert (Ux : bv_unsigned (Z_to_bv 64 (a + Z.of_nat k)) = a + Z.of_nat k) by (apply u_Z2bv; lia).
  rewrite wb_in by (rewrite length_N_to_le_bytes, ?Ua, ?Ux; lia).
  rewrite Ua, Ux. replace (Z.to_nat (a + Z.of_nat k - a)) with k by lia.
  f_equal. unfold word_to_le_bytes. apply nth_error_nth. apply nth_error_Z_to_le_bytes. exact Hk.
Qed.

Lemma vm_out : forall (m : word -> option byte) b (n' : nat) w a (n : nat) v,
  0 <= b < 2 ^ 64 -> b + Z.of_nat n' <= 2 ^ 64 -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (a + Z.of_nat n <= b \/ b + Z.of_nat n' <= a) ->
  val_mem segs m a n v -> val_mem segs (wbytes m (Z_to_bv 64 b) (word_to_le_bytes n' w)) a n v.
Proof.
  intros m b n' w a n v Hb Hbn Ha Han Hd Hv k Hk. unfold YP09.mbyte.
  rewrite wb_out by lia. exact (Hv k Hk).
Qed.

Lemma vm_hit8 : forall (m : word -> option byte) a w, 0 <= a -> a + 8 <= 2 ^ 64 ->
  val_mem segs (wbytes m (Z_to_bv 64 a) (word_to_le_bytes 8 w)) a 8 (bv_unsigned w).
Proof.
  intros m a w Ha Ha8 k Hk. unfold YP09.mbyte. rewrite wb_at by lia. f_equal.
  rewrite le_byte_bv by exact Hk. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64).
  rewrite Z.mod_small; [reflexivity | exact (u64_range w)].
Qed.

Lemma vm_hitZ8 : forall (m : word -> option byte) a v, 0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  val_mem segs (wbytes m (Z_to_bv 64 a) (word_to_le_bytes 8 (Z_to_bv 64 v))) a 8 v.
Proof.
  intros m a v Ha Ha8 Hv. pose proof (vm_hit8 m a (Z_to_bv 64 v) Ha Ha8) as H.
  rewrite u_Z2bv in H by lia. exact H.
Qed.

Lemma vm_hit4m1 : forall (m : word -> option byte) a, 0 <= a -> a + 4 <= 2 ^ 64 ->
  val_mem segs (wbytes m (Z_to_bv 64 a) (word_to_le_bytes 4 (Z_to_bv 64 (-1)))) a 4 U32M1.
Proof.
  intros m a Ha Ha4 k Hk. unfold YP09.mbyte. rewrite wb_at by lia. f_equal.
  destruct k as [|[|[|[|k]]]]; [bveq | bveq | bveq | bveq | lia].
Qed.

Lemma vm_kept : forall (m m' : word -> option byte) a n v,
  (forall k, (k < n)%nat -> m' (Z_to_bv 64 (a + Z.of_nat k)) = m (Z_to_bv 64 (a + Z.of_nat k))) ->
  val_mem segs m a n v -> val_mem segs m' a n v.
Proof. intros m m' a n v Hk Hv k Hlt. unfold YP09.mbyte. rewrite (Hk k Hlt). exact (Hv k Hlt). Qed.

Lemma grows_wb : forall (m m' : word -> option byte) a bs, mem_grows m m' -> mem_grows m (wbytes m' a bs).
Proof. intros m m' a bs Hg x Hx. apply (wbytes_grows bs m' a x). apply Hg. exact Hx. Qed.

Lemma vm8_inj : forall (m : word -> option byte) a v1 v2, 0 <= a -> a + 8 <= 2 ^ 64 ->
  val_mem segs m a 8 v1 -> val_mem segs m a 8 v2 -> v1 mod 2 ^ 64 = v2 mod 2 ^ 64.
Proof.
  intros m a v1 v2 Ha Ha8 H1 H2.
  pose proof (word_mem_rdn segs m a v1 (proj1 (val_mem_word_mem segs m a v1) H1) Ha Ha8) as R1.
  pose proof (word_mem_rdn segs m a v2 (proj1 (val_mem_word_mem segs m a v2) H2) Ha Ha8) as R2.
  rewrite R1 in R2.
  assert (E : word_to_le_bytes 8 (Z_to_bv 64 v1) = word_to_le_bytes 8 (Z_to_bv 64 v2)) by congruence.
  apply (f_equal bytes_le_to_Z) in E. rewrite <- !n_to_le_8_spec, !bytes_le_n_to_le_8 in E.
  rewrite !Z_to_bv_unsigned in E. exact E.
Qed.

Lemma so_pres : forall H (mem : word -> option byte) a (n : nat),
  0 <= a < 2 ^ 64 -> a + Z.of_nat n <= 2 ^ 64 -> (forall x, a <= x < a + Z.of_nat n -> apresent H mem x) ->
  store_ok segs (mrestrict H mem) (Z_to_bv 64 a) n = true.
Proof.
  intros H mem a n Ha Han Hp. apply writable_store_ok; [lia | lia |].
  intros x Hx. apply apresent_writable. exact (Hp x Hx).
Qed.

Lemma nrange : forall lo hi x, ~ (lo <= x < hi) -> x < lo \/ hi <= x.
Proof.
  intros lo hi x Hn. destruct (Z_lt_le_dec x lo) as [H|H]; [left; exact H|].
  destruct (Z_lt_le_dec x hi) as [H'|H']; [exfalso; apply Hn; split; assumption | right; exact H'].
Qed.

Lemma getr_upd_eq : forall (regs : bvmap 5 word) (r r' : bv 5) v, bv_unsigned r = bv_unsigned r' -> r <> 0%bv ->
  getr (regupd regs r v) r' = v.
Proof. intros regs r r' v E H0. replace r' with r by (apply bv_eq; exact E). apply getr_same. exact H0. Qed.
End m.

Ltac vpeel := repeat (apply vm_out; [lia | lia | lia | lia | lia | ]).
Ltac peel := repeat (rewrite wb_out; [ | lia | lia | lia | lia ]).

(* ---------------------------------------------------------------------- *)
(* 3. One step of the walk at offset k from the entry, per instruction kind. *)
(* ---------------------------------------------------------------------- *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable pc : Z.
#[local] Abbreviation ST regs k m := (mkst regs (Z_to_bv 64 (pc + k)) m (seg_rom segs)).

Lemma pcz : forall k k', k + 4 = k' -> v_addi (Z_to_bv 64 (pc + k)) 4 = Z_to_bv 64 (pc + k').
Proof. intros k k' E. rewrite vaddiZ. f_equal. lia. Qed.
Lemma pcj : forall k i k', k + i = k' -> btgt (Z_to_bv 64 (pc + k)) i = Z_to_bv 64 (pc + k').
Proof. intros k i k' E. unfold btgt. rewrite vaddiZ. f_equal. lia. Qed.

Lemma W_alu : forall regs k k' m rd vexp vv ms'',
  RiscvSemantics.step segs (ST regs k m) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd vexp) (v_addi (Z_to_bv 64 (pc + k)) 4) m (seg_rom segs)) ->
  bv_eqb rd 0 = false -> vexp = vv -> k + 4 = k' ->
  msteps segs (ST (regupd regs rd vv) k' m) ms'' -> msteps segs (ST regs k m) ms''.
Proof.
  intros regs k k' m rd vexp vv ms'' Hs Hrd Hv Hk Hn.
  eapply mst_step; [reflexivity | exact Hs |]. rewrite Hrd, Hv, (pcz k k' Hk). exact Hn.
Qed.

Lemma W_addi : forall regs k k' m w rd rs (imm : bv 12) i x y ms'',
  fetch_word segs (Z_to_bv 64 (pc + k)) = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_ADD rd rs imm, 4%Z) -> bv_eqb rd 0 = false ->
  bv_signed imm = i -> getr regs rs = Z_to_bv 64 x -> x + i = y -> k + 4 = k' ->
  msteps segs (ST (regupd regs rd (Z_to_bv 64 y)) k' m) ms'' -> msteps segs (ST regs k m) ms''.
Proof.
  intros regs k k' m w rd rs imm i x y ms'' Hf He Hd Hrd Hi Hx Hy Hk Hn.
  eapply mst_step; [reflexivity | exact (step_addi segs regs _ m _ w rd rs imm Hf He Hd) |].
  rewrite Hrd, Hx, Hi, (vaddiZ x i), Hy, (pcz k k' Hk). exact Hn.
Qed.

Lemma W_ld : forall regs k k' m w rd rs (imm : bv 12) i x a v ms'',
  fetch_word segs (Z_to_bv 64 (pc + k)) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ8 true rd rs imm, 4%Z) -> bv_eqb rd 0 = false ->
  bv_signed imm = i -> getr regs rs = Z_to_bv 64 x -> x + i = a -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  val_mem segs m a 8 v -> k + 4 = k' ->
  msteps segs (ST (regupd regs rd (Z_to_bv 64 v)) k' m) ms'' -> msteps segs (ST regs k m) ms''.
Proof.
  intros regs k k' m w rd rs imm i x a v ms'' Hf He Hd Hrd Hi Hx Ha Ha0 Ha8 Hv Hk Hn.
  destruct (word_mem_ld segs m a v (proj1 (val_mem_word_mem segs m a v) Hv) Ha0 Ha8) as (bs & Hbs & Hle).
  eapply mst_step; [reflexivity | eapply (step_ld segs regs _ m _ w rd rs imm bs (Z_to_bv 64 v) Hf He Hd); [| exact Hle] |].
  - rewrite Hx, Hi, (vaddiZ x i), Ha. exact Hbs.
  - rewrite Hrd, (pcz k k' Hk). exact Hn.
Qed.

Lemma W_lw : forall regs k k' m w rd rs (imm : bv 12) i x a v ms'',
  fetch_word segs (Z_to_bv 64 (pc + k)) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 true rd rs imm, 4%Z) -> bv_eqb rd 0 = false ->
  bv_signed imm = i -> getr regs rs = Z_to_bv 64 x -> x + i = a -> 0 <= a -> a + 4 <= 2 ^ 64 ->
  val_mem segs m a 4 v -> k + 4 = k' ->
  msteps segs (ST (regupd regs rd (Z_to_bv 64 (bv_swrap 32 (v mod 2 ^ 32)))) k' m) ms'' ->
  msteps segs (ST regs k m) ms''.
Proof.
  intros regs k k' m w rd rs imm i x a v ms'' Hf He Hd Hrd Hi Hx Ha Ha0 Ha4 Hv Hk Hn.
  destruct (bytes4_rdn segs m a v Ha0 Ha4 Hv) as [Hbs Hle].
  pose proof (Z.mod_pos_bound v (2 ^ 32) ltac:(lia)) as Hb.
  eapply mst_step; [reflexivity | eapply (step_lw segs regs _ m _ w rd rs imm _ (Z_to_bv 64 (v mod 2 ^ 32)) Hf He Hd) |].
  - rewrite Hx, Hi, (vaddiZ x i), Ha. exact Hbs.
  - rewrite Hle, u_Z2bv by lia. reflexivity.
  - rewrite Hrd, (pcz k k' Hk). unfold v_lw. rewrite u_Z2bv by lia. exact Hn.
Qed.

Lemma W_lwu : forall regs k k' m w rd rs (imm : bv 12) i x a v ms'',
  fetch_word segs (Z_to_bv 64 (pc + k)) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 false rd rs imm, 4%Z) -> bv_eqb rd 0 = false ->
  bv_signed imm = i -> getr regs rs = Z_to_bv 64 x -> x + i = a -> 0 <= a -> a + 4 <= 2 ^ 64 ->
  val_mem segs m a 4 v -> k + 4 = k' ->
  msteps segs (ST (regupd regs rd (Z_to_bv 64 (v mod 2 ^ 32))) k' m) ms'' ->
  msteps segs (ST regs k m) ms''.
Proof.
  intros regs k k' m w rd rs imm i x a v ms'' Hf He Hd Hrd Hi Hx Ha Ha0 Ha4 Hv Hk Hn.
  destruct (bytes4_rdn segs m a v Ha0 Ha4 Hv) as [Hbs Hle].
  pose proof (Z.mod_pos_bound v (2 ^ 32) ltac:(lia)) as Hb.
  eapply mst_step; [reflexivity | eapply (step_lwu segs regs _ m _ w rd rs imm _ (Z_to_bv 64 (v mod 2 ^ 32)) Hf He Hd) |].
  - rewrite Hx, Hi, (vaddiZ x i), Ha. exact Hbs.
  - rewrite Hle, u_Z2bv by lia. reflexivity.
  - rewrite Hrd, (pcz k k' Hk). exact Hn.
Qed.

Lemma W_sd : forall regs k k' m w rs1 rs2 (imm : bv 12) i x a vv ms'',
  fetch_word segs (Z_to_bv 64 (pc + k)) = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ8 rs1 rs2 imm, 4%Z) ->
  bv_signed imm = i -> getr regs rs1 = Z_to_bv 64 x -> x + i = a -> getr regs rs2 = vv ->
  store_ok segs m (Z_to_bv 64 a) 8 = true -> k + 4 = k' ->
  msteps segs (ST regs k' (wbytes m (Z_to_bv 64 a) (word_to_le_bytes 8 vv))) ms'' ->
  msteps segs (ST regs k m) ms''.
Proof.
  intros regs k k' m w rs1 rs2 imm i x a vv ms'' Hf He Hd Hi Hx Ha Hv Hok Hk Hn.
  eapply mst_step; [reflexivity | eapply (step_sd_at segs regs _ m _ w rs1 rs2 imm (Z_to_bv 64 a) vv Hf He Hd); [| exact Hv | exact Hok] |].
  - rewrite Hx, Hi, (vaddiZ x i), Ha. reflexivity.
  - rewrite (pcz k k' Hk). exact Hn.
Qed.

Lemma W_sw : forall regs k k' m w rs1 rs2 (imm : bv 12) i x a vv ms'',
  fetch_word segs (Z_to_bv 64 (pc + k)) = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ4 rs1 rs2 imm, 4%Z) ->
  bv_signed imm = i -> getr regs rs1 = Z_to_bv 64 x -> x + i = a -> getr regs rs2 = vv ->
  store_ok segs m (Z_to_bv 64 a) 4 = true -> k + 4 = k' ->
  msteps segs (ST regs k' (wbytes m (Z_to_bv 64 a) (word_to_le_bytes 4 vv))) ms'' ->
  msteps segs (ST regs k m) ms''.
Proof.
  intros regs k k' m w rs1 rs2 imm i x a vv ms'' Hf He Hd Hi Hx Ha Hv Hok Hk Hn.
  eapply mst_step; [reflexivity | eapply (step_sw_at segs regs _ m _ w rs1 rs2 imm (Z_to_bv 64 a) vv Hf He Hd); [| exact Hv | exact Hok] |].
  - rewrite Hx, Hi, (vaddiZ x i), Ha. reflexivity.
  - rewrite (pcz k k' Hk). exact Hn.
Qed.

Lemma W_beq : forall regs k k' m w rs1 rs2 (imm : bv 13) i ms'',
  fetch_word segs (Z_to_bv 64 (pc + k)) = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_EQ rs1 rs2 imm, 4%Z) ->
  c_eq (getr regs rs1) (getr regs rs2) = true -> bv_signed imm = i -> k + i = k' ->
  msteps segs (ST regs k' m) ms'' -> msteps segs (ST regs k m) ms''.
Proof.
  intros regs k k' m w rs1 rs2 imm i ms'' Hf He Hd Hc Hi Hk Hn.
  eapply mst_step; [reflexivity | exact (step_beq_tk segs regs _ m _ w rs1 rs2 imm Hf He Hd Hc) |].
  rewrite Hi, (pcj k i k' Hk). exact Hn.
Qed.

Lemma W_bne_ft : forall regs k k' m w rs1 rs2 (imm : bv 13) ms'',
  fetch_word segs (Z_to_bv 64 (pc + k)) = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_NE rs1 rs2 imm, 4%Z) ->
  c_eq (getr regs rs1) (getr regs rs2) = true -> k + 4 = k' ->
  msteps segs (ST regs k' m) ms'' -> msteps segs (ST regs k m) ms''.
Proof.
  intros regs k k' m w rs1 rs2 imm ms'' Hf He Hd Hc Hk Hn.
  eapply mst_step; [reflexivity | exact (step_bne_ft segs regs _ m _ w rs1 rs2 imm Hf He Hd Hc) |].
  rewrite (pcz k k' Hk). exact Hn.
Qed.

Lemma W_jal : forall regs k k' m w (imm : bv 21) i ms'',
  fetch_word segs (Z_to_bv 64 (pc + k)) = Some w -> is_ecall w = false ->
  decode_any w = Some (Jal 0 imm, 4%Z) -> bv_signed imm = i -> k + i = k' ->
  msteps segs (ST regs k' m) ms'' -> msteps segs (ST regs k m) ms''.
Proof.
  intros regs k k' m w imm i ms'' Hf He Hd Hi Hk Hn.
  eapply mst_step; [reflexivity | exact (step_jal_x0 segs regs _ m _ w imm Hf He Hd) |].
  rewrite Hi, (pcj k i k' Hk). exact Hn.
Qed.

Lemma W_ret : forall regs k m w rs1 (imm : bv 12) t ms'',
  fetch_word segs (Z_to_bv 64 (pc + k)) = Some w -> is_ecall w = false ->
  decode_any w = Some (Jalr 0 rs1 imm, 4%Z) -> getr regs rs1 = t -> bv_signed imm = 0 -> YK0s.ret_ok t ->
  msteps segs (mkst regs t m (seg_rom segs)) ms'' -> msteps segs (ST regs k m) ms''.
Proof.
  intros regs k m w rs1 imm t ms'' Hf He Hd Ht Hi Hr Hn.
  eapply mst_step; [reflexivity | exact (step_jalr_x0 segs regs _ m _ w rs1 imm t Hf He Hd Ht) |].
  rewrite Hi. unfold YK0s.ret_ok in Hr. rewrite Hr. exact Hn.
Qed.
End w.

(* ---------------------------------------------------------------------- *)
(* 4. The walk.                                                            *)
(* ---------------------------------------------------------------------- *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable K : asource_syms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, YG0d.in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis ASIL : asource_img_laws SK segs B K.
Variable pc : Z.
Hypothesis CODE : toread_code segs pc = true.

Lemma F00 : fetch_word segs (Z_to_bv 64 (pc + 0x00)) = Some (Z_to_bv 32 0xff010113). Proof. exact (code_from_at segs _ pc 0 _ CODE eq_refl). Qed.
Lemma F04 : fetch_word segs (Z_to_bv 64 (pc + 0x04)) = Some (Z_to_bv 32 0x00113423). Proof. exact (code_from_at segs _ pc 1 _ CODE eq_refl). Qed.
Lemma F08 : fetch_word segs (Z_to_bv 64 (pc + 0x08)) = Some (Z_to_bv 32 0x00813023). Proof. exact (code_from_at segs _ pc 2 _ CODE eq_refl). Qed.
Lemma F0c : fetch_word segs (Z_to_bv 64 (pc + 0x0c)) = Some (Z_to_bv 32 0x00050413). Proof. exact (code_from_at segs _ pc 3 _ CODE eq_refl). Qed.
Lemma F10 : fetch_word segs (Z_to_bv 64 (pc + 0x10)) = Some (Z_to_bv 32 0x08852503). Proof. exact (code_from_at segs _ pc 4 _ CODE eq_refl). Qed.
Lemma F14 : fetch_word segs (Z_to_bv 64 (pc + 0x14)) = Some (Z_to_bv 32 0x02843583). Proof. exact (code_from_at segs _ pc 5 _ CODE eq_refl). Qed.
Lemma F18 : fetch_word segs (Z_to_bv 64 (pc + 0x18)) = Some (Z_to_bv 32 0x03843603). Proof. exact (code_from_at segs _ pc 6 _ CODE eq_refl). Qed.
Lemma F1c : fetch_word segs (Z_to_bv 64 (pc + 0x1c)) = Some (Z_to_bv 32 0xfff50693). Proof. exact (code_from_at segs _ pc 7 _ CODE eq_refl). Qed.
Lemma F20 : fetch_word segs (Z_to_bv 64 (pc + 0x20)) = Some (Z_to_bv 32 0x00a6e533). Proof. exact (code_from_at segs _ pc 8 _ CODE eq_refl). Qed.
Lemma F24 : fetch_word segs (Z_to_bv 64 (pc + 0x24)) = Some (Z_to_bv 32 0x08a42423). Proof. exact (code_from_at segs _ pc 9 _ CODE eq_refl). Qed.
Lemma F28 : fetch_word segs (Z_to_bv 64 (pc + 0x28)) = Some (Z_to_bv 32 0x00c58c63). Proof. exact (code_from_at segs _ pc 10 _ CODE eq_refl). Qed.
Lemma F40 : fetch_word segs (Z_to_bv 64 (pc + 0x40)) = Some (Z_to_bv 32 0x00046503). Proof. exact (code_from_at segs _ pc 16 _ CODE eq_refl). Qed.
Lemma F44 : fetch_word segs (Z_to_bv 64 (pc + 0x44)) = Some (Z_to_bv 32 0x00457593). Proof. exact (code_from_at segs _ pc 17 _ CODE eq_refl). Qed.
Lemma F48 : fetch_word segs (Z_to_bv 64 (pc + 0x48)) = Some (Z_to_bv 32 0x02043023). Proof. exact (code_from_at segs _ pc 18 _ CODE eq_refl). Qed.
Lemma F4c : fetch_word segs (Z_to_bv 64 (pc + 0x4c)) = Some (Z_to_bv 32 0x02043423). Proof. exact (code_from_at segs _ pc 19 _ CODE eq_refl). Qed.
Lemma F50 : fetch_word segs (Z_to_bv 64 (pc + 0x50)) = Some (Z_to_bv 32 0x02043c23). Proof. exact (code_from_at segs _ pc 20 _ CODE eq_refl). Qed.
Lemma F54 : fetch_word segs (Z_to_bv 64 (pc + 0x54)) = Some (Z_to_bv 32 0x02059263). Proof. exact (code_from_at segs _ pc 21 _ CODE eq_refl). Qed.
Lemma F58 : fetch_word segs (Z_to_bv 64 (pc + 0x58)) = Some (Z_to_bv 32 0x05843583). Proof. exact (code_from_at segs _ pc 22 _ CODE eq_refl). Qed.
Lemma F5c : fetch_word segs (Z_to_bv 64 (pc + 0x5c)) = Some (Z_to_bv 32 0x06043603). Proof. exact (code_from_at segs _ pc 23 _ CODE eq_refl). Qed.
Lemma F60 : fetch_word segs (Z_to_bv 64 (pc + 0x60)) = Some (Z_to_bv 32 0x03b51513). Proof. exact (code_from_at segs _ pc 24 _ CODE eq_refl). Qed.
Lemma F64 : fetch_word segs (Z_to_bv 64 (pc + 0x64)) = Some (Z_to_bv 32 0x00c585b3). Proof. exact (code_from_at segs _ pc 25 _ CODE eq_refl). Qed.
Lemma F68 : fetch_word segs (Z_to_bv 64 (pc + 0x68)) = Some (Z_to_bv 32 0x00b43423). Proof. exact (code_from_at segs _ pc 26 _ CODE eq_refl). Qed.
Lemma F6c : fetch_word segs (Z_to_bv 64 (pc + 0x6c)) = Some (Z_to_bv 32 0x00b43823). Proof. exact (code_from_at segs _ pc 27 _ CODE eq_refl). Qed.
Lemma F70 : fetch_word segs (Z_to_bv 64 (pc + 0x70)) = Some (Z_to_bv 32 0x43f55513). Proof. exact (code_from_at segs _ pc 28 _ CODE eq_refl). Qed.
Lemma F74 : fetch_word segs (Z_to_bv 64 (pc + 0x74)) = Some (Z_to_bv 32 0x0100006f). Proof. exact (code_from_at segs _ pc 29 _ CODE eq_refl). Qed.
Lemma F84 : fetch_word segs (Z_to_bv 64 (pc + 0x84)) = Some (Z_to_bv 32 0x00813083). Proof. exact (code_from_at segs _ pc 33 _ CODE eq_refl). Qed.
Lemma F88 : fetch_word segs (Z_to_bv 64 (pc + 0x88)) = Some (Z_to_bv 32 0x00013403). Proof. exact (code_from_at segs _ pc 34 _ CODE eq_refl). Qed.
Lemma F8c : fetch_word segs (Z_to_bv 64 (pc + 0x8c)) = Some (Z_to_bv 32 0x01010113). Proof. exact (code_from_at segs _ pc 35 _ CODE eq_refl). Qed.
Lemma F90 : fetch_word segs (Z_to_bv 64 (pc + 0x90)) = Some (Z_to_bv 32 0x00008067). Proof. exact (code_from_at segs _ pc 36 _ CODE eq_refl). Qed.

Theorem rtoread_contract_proof : rtoread_contract segs B K pc.
Proof.
  intros W ly S regs mem md ch f b p fl C HPRE.
  destruct HPRE as (HFN & G10 & Hblk & HbB & Hbsp & HUB & HFL). clear Hbsp.
  pose proof HFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  assert (RS : RTOREAD_STK = 4160) by reflexivity.
  rewrite RS in Hslo, Hpres.
  pose proof asan_consts as (C1 & _ & _ & _ & C5).
  destruct HUB as [HAT HW0].
  destruct HAT as (Wn & cpos & fl0 & md0 & HAT). cbv zeta in HAT.
  destruct HAT as (Hp0 & Hpc & Hcn & Hn63 & Hbw & Hcpos & HWn & Hok & HC & HST & HWIN & HFL0 & HEOF & HMD & HCP & HENV & HHEAD & Hfnz). (* POS *)
  destruct HST as (Vclose & Vread & Vwrite & Vseek & V88 & V96 & Vl1 & Vl2 & Vcb & Vcm & Vck & V32 & V40 & V48 & V56
    & V104 & V112 & V168 & V120 & V140 & V144 & Hf0 & Hfm & Hb0 & Hfbd).
  destruct HMD as (V136 & Hmd). destruct HFL as (VFL & Hfl). destruct HFL0 as (VFL0 & Hfl0).
  unfold SRC_FILE_BLOCK, SRC_BUF_OFF, SRC_BUFSIZ, SRC_COOKIE_OFF, SRC_MODE_R, U32M1 in *.
  assert (RQ : req_size 1304 = 1304) by reflexivity.
  destruct (al_blocks _ _ LAWS ly S W mem md f 1304 HAR Hblk) as (Hf16 & Hf4 & Hfc & Hfapp & Hfb & _ & _).
  rewrite RQ in Hfc, Hfapp, Hfb.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp.
  (* the FILE block is application memory: below the low shadow or above the high one *)
  assert (Hfapp' : HIDE (f + 1304 <= 0x7fff7000 \/ 0x10007fff8000 <= f))
    by (unfold HIDE; destruct Hfapp as [_ [H | [H _]]]; [left | right]; lia).
  clear Hfapp.
  assert (Hfp : forall a, f <= a < f + 1304 -> apresent (w_H W) mem a) by (intros a Ha; exact (proj1 (Hfb a Ha))).
  clear Hfb.
  destruct (al_blocks _ _ LAWS ly S W mem md b _ HAR HbB) as (_ & Hb4 & Hbc & _ & _ & _ & _).
  assert (Hbn : b + Z.of_nat (length C) <= alloc_ceiling).
  { revert Hbc. unfold req_size. destruct (Z.of_nat (length C) =? 0) eqn:E; cbv iota; intros Hbc;
      [apply Z.eqb_eq in E|]; lia. }
  clear Hbc.
  (* the window is empty: rpos/rend pin |Wn| to 0 *)
  assert (HWe : Wn = []).
  { destruct HWIN as [(-> & _ & _) | (i & Hi0 & Hi1 & Vr & Ve & _)]; [reflexivity|].
    assert (Hl : Z.of_nat (length Wn) = 0).
    { destruct HW0 as [(_ & Vr0 & Ve0) | (j & Hj0 & Hj1 & Vr0 & Ve0 & _)]; unfold SRC_BUF_OFF, SRC_BUFSIZ in *.
      - pose proof (vm8_inj segs _ (f + 8) _ _ ltac:(lia) ltac:(lia) Vr Vr0) as E1.
        pose proof (vm8_inj segs _ (f + 16) _ _ ltac:(lia) ltac:(lia) Ve Ve0) as E2.
        rewrite !Z.mod_small in E1, E2 by lia. lia.
      - cbn [length Z.of_nat] in Ve0, Hj1.
        pose proof (vm8_inj segs _ (f + 8) _ _ ltac:(lia) ltac:(lia) Vr Vr0) as E1.
        pose proof (vm8_inj segs _ (f + 16) _ _ ltac:(lia) ltac:(lia) Ve Ve0) as E2.
        rewrite !Z.mod_small in E1, E2 by lia. lia. }
    destruct Wn as [|w0 Wn']; [reflexivity | cbn [length] in Hl; lia]. }
  clear HWIN HW0.
  rewrite HWe in Hcpos. cbn [length Z.of_nat] in Hcpos.
  assert (Gsp : getr regs 2 = Z_to_bv 64 (spZ regs)) by (unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
  unfold w64 in G10.
  assert (Hsm : bv_swrap 32 (md0 mod 2 ^ 32) = 0 \/ bv_swrap 32 (md0 mod 2 ^ 32) = -1)
    by (destruct Hmd as [-> | ->]; [left | right]; reflexivity).
  assert (Hsp1 : alloc_ceiling + 4160 <= spZ regs) by lia.
  assert (Hsp2 : spZ regs <= 2 ^ 47) by lia.
  assert (Hac : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000) by lia.
  clear Hceil Hslo Hshi H47 Hbot Htop2 Htop C1 Hstk0.
  (* hide the disjunctions lia does not need *)
  assert (Hmd' : HIDE (md0 = 0 \/ md0 = 4294967295)) by exact Hmd. clear Hmd.
  assert (Hsm' : HIDE (bv_swrap 32 (md0 mod 2 ^ 32) = 0 \/ bv_swrap 32 (md0 mod 2 ^ 32) = -1)) by exact Hsm. clear Hsm.
  assert (Hfl' : HIDE (fl = 8 \/ fl = 24)) by exact Hfl. clear Hfl.
  assert (Hfl0' : HIDE (fl0 = 8 \/ fl0 = 24)) by exact Hfl0. clear Hfl0.
  assert (HEOF' : HIDE (fl0 = 24 -> p = Z.of_nat (length C))) by exact HEOF. clear HEOF.
  unfold cfg_at.
  eapply (SRr_msteps segs Hwx W (mkst regs (w64 pc) mem (seg_rom segs)) _ md).
  { rewrite restrict_mkst_fx. replace (w64 pc) with (Z_to_bv 64 (pc + 0x00)) by (unfold w64; f_equal; lia).
    (* 0x00 addi sp,sp,-16 *)
    eapply (W_addi segs pc) with (k := 0x00) (k' := 0x04) (i := -16) (x := spZ regs) (y := spZ regs - 16);
      [exact F00 | reflexivity | exact D00 | reflexivity | reflexivity | exact Gsp | lia | reflexivity |].
    (* 0x04 sd ra,8(sp) *)
    eapply (W_sd segs pc) with (k := 0x04) (k' := 0x08) (i := 8) (x := spZ regs - 16) (a := spZ regs - 8) (vv := getr regs 1);
      [exact F04 | reflexivity | exact D04 | reflexivity | gr; reflexivity | lia | gr; reflexivity
      | apply so_pres; [lia | lia | intros a' Ha'; apply Hpres; lia] | reflexivity |].
    (* 0x08 sd s0,0(sp) *)
    eapply (W_sd segs pc) with (k := 0x08) (k' := 0x0c) (i := 0) (x := spZ regs - 16) (a := spZ regs - 16) (vv := getr regs 8);
      [exact F08 | reflexivity | exact D08 | reflexivity | gr; reflexivity | lia | gr; reflexivity
      | eapply store_ok_mono; [repeat apply grows_wb; apply mem_grows_refl | apply so_pres; [lia | lia | intros a' Ha'; apply Hpres; lia]]
      | reflexivity |].
    (* 0x0c mv s0,a0 *)
    eapply (W_addi segs pc) with (k := 0x0c) (k' := 0x10) (i := 0) (x := f) (y := f);
      [exact F0c | reflexivity | exact D0c | reflexivity | reflexivity | gr; exact G10 | lia | reflexivity |].
    (* 0x10 lw a0,136(a0): the orientation word *)
    eapply (W_lw segs pc) with (k := 0x10) (k' := 0x14) (i := 136) (x := f) (a := f + 136) (v := md0);
      [exact F10 | reflexivity | exact D10 | reflexivity | reflexivity | gr; exact G10 | lia | lia | lia
      | vpeel; exact V136 | reflexivity |].
    (* 0x14 ld a1,40(s0): wpos *)
    eapply (W_ld segs pc) with (k := 0x14) (k' := 0x18) (i := 40) (x := f) (a := f + 40) (v := 0);
      [exact F14 | reflexivity | exact D14 | reflexivity | reflexivity | gr; reflexivity | lia | lia | lia
      | vpeel; exact V40 | reflexivity |].
    (* 0x18 ld a2,56(s0): wbase *)
    eapply (W_ld segs pc) with (k := 0x18) (k' := 0x1c) (i := 56) (x := f) (a := f + 56) (v := 0);
      [exact F18 | reflexivity | exact D18 | reflexivity | reflexivity | gr; reflexivity | lia | lia | lia
      | vpeel; exact V56 | reflexivity |].
    (* 0x1c addi a3,a0,-1 *)
    eapply (W_addi segs pc) with (k := 0x1c) (k' := 0x20) (i := -1) (x := bv_swrap 32 (md0 mod 2 ^ 32))
      (y := bv_swrap 32 (md0 mod 2 ^ 32) - 1);
      [exact F1c | reflexivity | exact D1c | reflexivity | reflexivity | gr; reflexivity | lia | reflexivity |].
    (* 0x20 or a0,a3,a0: mode | (mode - 1) = -1 for mode 0 and -1 *)
    eapply (W_alu segs pc) with (k := 0x20) (k' := 0x24) (rd := 10%bv) (vv := Z_to_bv 64 (-1));
      [exact (step_or segs _ _ _ _ _ _ _ _ F20 eq_refl D20) | reflexivity
      | gr; unfold HIDE in Hsm'; destruct Hsm' as [Hs | Hs]; rewrite Hs; bveq | reflexivity |].
    (* 0x24 sw a0,136(s0) *)
    eapply (W_sw segs pc) with (k := 0x24) (k' := 0x28) (i := 136) (x := f) (a := f + 136) (vv := Z_to_bv 64 (-1));
      [exact F24 | reflexivity | exact D24 | reflexivity | gr; reflexivity | lia | gr; reflexivity
      | eapply store_ok_mono; [repeat apply grows_wb; apply mem_grows_refl | apply so_pres; [lia | lia | intros a' Ha'; apply Hfp; lia]]
      | reflexivity |].
    (* 0x28 beq a1,a2: taken, wpos = wbase = 0 *)
    eapply (W_beq segs pc) with (k := 0x28) (k' := 0x40) (i := 24);
      [exact F28 | reflexivity | exact D28 | gr; reflexivity | reflexivity | reflexivity |].
    (* 0x40 lwu a0,0(s0): flags *)
    eapply (W_lwu segs pc) with (k := 0x40) (k' := 0x44) (i := 0) (x := f) (a := f) (v := fl);
      [exact F40 | reflexivity | exact D40 | reflexivity | reflexivity | gr; reflexivity | lia | lia | lia
      | vpeel; exact VFL | reflexivity |].
    (* 0x44 andi a1,a0,4: F_NORD clear *)
    eapply (W_alu segs pc) with (k := 0x44) (k' := 0x48) (rd := 11%bv) (vv := Z_to_bv 64 0);
      [exact (step_andi segs _ _ _ _ _ _ _ _ F44 eq_refl D44) | reflexivity
      | gr; unfold HIDE in Hfl'; destruct Hfl' as [-> | ->]; bveq | reflexivity |].
    (* 0x48 0x4c 0x50 sd zero at +32 +40 +56 *)
    eapply (W_sd segs pc) with (k := 0x48) (k' := 0x4c) (i := 32) (x := f) (a := f + 32) (vv := Z_to_bv 64 0);
      [exact F48 | reflexivity | exact D48 | reflexivity | gr; reflexivity | lia | gr; reflexivity
      | eapply store_ok_mono; [repeat apply grows_wb; apply mem_grows_refl | apply so_pres; [lia | lia | intros a' Ha'; apply Hfp; lia]]
      | reflexivity |].
    eapply (W_sd segs pc) with (k := 0x4c) (k' := 0x50) (i := 40) (x := f) (a := f + 40) (vv := Z_to_bv 64 0);
      [exact F4c | reflexivity | exact D4c | reflexivity | gr; reflexivity | lia | gr; reflexivity
      | eapply store_ok_mono; [repeat apply grows_wb; apply mem_grows_refl | apply so_pres; [lia | lia | intros a' Ha'; apply Hfp; lia]]
      | reflexivity |].
    eapply (W_sd segs pc) with (k := 0x50) (k' := 0x54) (i := 56) (x := f) (a := f + 56) (vv := Z_to_bv 64 0);
      [exact F50 | reflexivity | exact D50 | reflexivity | gr; reflexivity | lia | gr; reflexivity
      | eapply store_ok_mono; [repeat apply grows_wb; apply mem_grows_refl | apply so_pres; [lia | lia | intros a' Ha'; apply Hfp; lia]]
      | reflexivity |].
    (* 0x54 bnez a1: not taken *)
    eapply (W_bne_ft segs pc) with (k := 0x54) (k' := 0x58);
      [exact F54 | reflexivity | exact D54 | gr; reflexivity | reflexivity |].
    (* 0x58 ld a1,88(s0); 0x5c ld a2,96(s0): the buffer base and size *)
    eapply (W_ld segs pc) with (k := 0x58) (k' := 0x5c) (i := 88) (x := f) (a := f + 88) (v := f + 280);
      [exact F58 | reflexivity | exact D58 | reflexivity | reflexivity | gr; reflexivity | lia | lia | lia
      | vpeel; exact V88 | reflexivity |].
    eapply (W_ld segs pc) with (k := 0x5c) (k' := 0x60) (i := 96) (x := f) (a := f + 96) (v := 1024);
      [exact F5c | reflexivity | exact D5c | reflexivity | reflexivity | gr; reflexivity | lia | lia | lia
      | vpeel; exact V96 | reflexivity |].
    (* 0x60 slli a0,a0,59 *)
    eapply (W_alu segs pc) with (k := 0x60) (k' := 0x64) (rd := 10%bv) (vv := v_slli (Z_to_bv 64 (fl mod 2 ^ 32)) 59);
      [exact (step_slli segs _ _ _ _ _ _ _ _ F60 eq_refl D60) | reflexivity | gr; reflexivity | reflexivity |].
    (* 0x64 add a1,a1,a2: f + 1304 *)
    eapply (W_alu segs pc) with (k := 0x64) (k' := 0x68) (rd := 11%bv) (vv := Z_to_bv 64 (f + 1304));
      [exact (step_add segs _ _ _ _ _ _ _ _ F64 eq_refl D64) | reflexivity
      | gr; rewrite vaddZ; f_equal; lia | reflexivity |].
    (* 0x68 sd a1,8(s0); 0x6c sd a1,16(s0): rpos = rend = f + 1304 *)
    eapply (W_sd segs pc) with (k := 0x68) (k' := 0x6c) (i := 8) (x := f) (a := f + 8) (vv := Z_to_bv 64 (f + 1304));
      [exact F68 | reflexivity | exact D68 | reflexivity | gr; reflexivity | lia | gr; reflexivity
      | eapply store_ok_mono; [repeat apply grows_wb; apply mem_grows_refl | apply so_pres; [lia | lia | intros a' Ha'; apply Hfp; lia]]
      | reflexivity |].
    eapply (W_sd segs pc) with (k := 0x6c) (k' := 0x70) (i := 16) (x := f) (a := f + 16) (vv := Z_to_bv 64 (f + 1304));
      [exact F6c | reflexivity | exact D6c | reflexivity | gr; reflexivity | lia | gr; reflexivity
      | eapply store_ok_mono; [repeat apply grows_wb; apply mem_grows_refl | apply so_pres; [lia | lia | intros a' Ha'; apply Hfp; lia]]
      | reflexivity |].
    (* 0x70 srai a0,a0,63: -1 exactly when F_EOF (16) is set *)
    eapply (W_alu segs pc) with (k := 0x70) (k' := 0x74) (rd := 10%bv) (vv := Z_to_bv 64 (if fl =? 24 then -1 else 0));
      [exact (step_srai segs _ _ _ _ _ _ _ _ F70 eq_refl D70) | reflexivity
      | gr; unfold HIDE in Hfl'; destruct Hfl' as [-> | ->]; bveq | reflexivity |].
    (* 0x74 j 0x84 *)
    eapply (W_jal segs pc) with (k := 0x74) (k' := 0x84) (i := 16);
      [exact F74 | reflexivity | exact D74 | reflexivity | reflexivity |].
    (* 0x84 ld ra,8(sp); 0x88 ld s0,0(sp) *)
    eapply (W_ld segs pc) with (k := 0x84) (k' := 0x88) (i := 8) (x := spZ regs - 16) (a := spZ regs - 8)
      (v := bv_unsigned (getr regs 1));
      [exact F84 | reflexivity | exact D84 | reflexivity | reflexivity | gr; reflexivity | lia | lia | lia
      | vpeel; apply vm_hit8; lia | reflexivity |].
    eapply (W_ld segs pc) with (k := 0x88) (k' := 0x8c) (i := 0) (x := spZ regs - 16) (a := spZ regs - 16)
      (v := bv_unsigned (getr regs 8));
      [exact F88 | reflexivity | exact D88 | reflexivity | reflexivity | gr; reflexivity | lia | lia | lia
      | vpeel; apply vm_hit8; lia | reflexivity |].
    (* 0x8c addi sp,sp,16 *)
    eapply (W_addi segs pc) with (k := 0x8c) (k' := 0x90) (i := 16) (x := spZ regs - 16) (y := spZ regs);
      [exact F8c | reflexivity | exact D8c | reflexivity | reflexivity | gr; reflexivity | lia | reflexivity |].
    (* 0x90 ret *)
    eapply (W_ret segs pc) with (k := 0x90) (t := getr regs 1);
      [exact F90 | reflexivity | exact D90 | gr; apply Z_to_bv_bv_unsigned | reflexivity | exact Hra |].
    apply mst_refl. }
  (* the state after `ret`: name its registers R and its (restricted) memory M *)
  intros md' Hsame Hcl.
  match goal with |- context [unrestrict _ _ (mkst ?RR _ ?MM _)] => set (R := RR) in *; set (M := MM) in * end.
  assert (EM : mrestrict (w_H W) (munrestrict (w_H W) mem M) = M)
    by exact (mrestrict_unrestrict_mem (w_H W) mem (mkst R (getr regs 1) M (seg_rom segs)) Hcl).
  (* every byte outside the eight stores is as it was *)
  assert (KEPT : forall x, 0 <= x < 2 ^ 64 -> (x < spZ regs - 16 \/ spZ regs <= x) ->
    (x < f + 8 \/ f + 24 <= x) -> (x < f + 32 \/ f + 48 <= x) -> (x < f + 56 \/ f + 64 <= x) ->
    (x < f + 136 \/ f + 140 <= x) -> M (Z_to_bv 64 x) = mrestrict (w_H W) mem (Z_to_bv 64 x)).
  { intros x Hx H1 H2 H3 H4 H5. unfold M. peel. reflexivity. }
  (* the stdio environment lies in the image, so off the FILE block and the stack *)
  assert (ENV : forall x, asrc_env_addr K x -> M (Z_to_bv 64 x) = mrestrict (w_H W) mem (Z_to_bv 64 x)).
  { intros x Hx. destruct (asil_env _ _ _ _ ASIL x Hx) as (Hi & _ & _).
    pose proof (segs_low x Hi) as Hlo. unfold kLowMemEnd in Hlo.
    assert (Hxf : x < f \/ f + 1304 <= x).
    { destruct (Z_lt_le_dec x f) as [H1|H1]; [left; exact H1|].
      destruct (Z_lt_le_dec x (f + 1304)) as [H2|H2]; [|right; exact H2].
      exfalso. apply (blk_img segs B LAWS ly S W mem md f 1304 x HAR Hblk); [rewrite RQ; lia | exact Hi]. }
    apply KEPT; lia. }
  assert (SW : source_window segs M f []).
  { unfold source_window. right. exists 1024. unfold SRC_BUFSIZ, SRC_BUF_OFF.
    split; [lia|]. split; [cbn [length]; lia|].
    split; [replace (f + 280 + 1024) with (f + 1304) by lia; unfold M; vpeel; apply vm_hitZ8; lia|].
    split; [replace (f + 280 + 1024 + Z.of_nat (length (@nil Z))) with (f + 1304) by (cbn [length]; lia);
            unfold M; vpeel; apply vm_hitZ8; lia|].
    apply garr8_nil. }
  assert (SM : source_mode segs M f 4294967295).
  { split; [unfold M; vpeel; apply vm_hit4m1; lia | right; reflexivity]. }
  assert (SRC : asource_at segs K M f b C p).
  { exists [], cpos, fl0, 4294967295. cbv zeta.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [cbn [length]; lia|]. (* POS *)
    split; [replace (cpos - p) with 0 by lia; reflexivity|].
    split; [exact Hok|].
    split.
    { intros j Hj. destruct (HC j Hj) as [Hv Hr]. split; [|exact Hr].
      eapply vm_kept; [|exact Hv]. intros k Hk. apply KEPT; lia. }
    split.
    { unfold source_static, SRC_COOKIE_OFF, SRC_BUF_OFF, SRC_BUFSIZ, SRC_FILE_BLOCK, SRC_MODE_R, U32M1.
      repeat split; try lia; try exact Hfbd;
        try (eapply vm_kept; [intros k Hk; apply KEPT; lia | eassumption]);
        unfold M; vpeel; apply vm_hitZ8; lia. }
    split; [exact SW|].
    split; [split; [eapply vm_kept; [intros k Hk; apply KEPT; lia | exact VFL0] | exact Hfl0'] |].
    split; [exact HEOF'|].
    split; [exact SM|].
    split; [unfold SRC_COOKIE_OFF; eapply vm_kept; [intros k Hk; apply KEPT; lia | exact HCP] |].
    split.
    { destruct HENV as (E1 & E2 & E3 & E4 & E5 & (cval & Hcv & E6)).
      split; [eapply vm_kept; [intros k Hk; apply ENV; unfold asrc_env_addr; left; lia | exact E1] |].
      split; [eapply vm_kept; [intros k Hk; apply ENV; unfold asrc_env_addr; right; left; lia | exact E2] |].
      split; [eapply vm_kept; [intros k Hk; apply ENV; unfold asrc_env_addr; right; right; left; lia | exact E3] |].
      split.
      { intros j Hj. destruct (E4 j Hj) as [Hv Hr]. split; [|exact Hr].
        unfold src_mode_Z in Hj; cbn [length app] in Hj.
        eapply vm_kept; [|exact Hv]. intros k Hk. apply ENV. unfold asrc_env_addr. right; right; right; left. lia. }
      split.
      { intros j Hj. destruct (E5 j Hj) as [Hv Hr]. split; [|exact Hr].
        unfold src_modeset_Z in Hj; cbn [length app] in Hj.
        eapply vm_kept; [|exact Hv]. intros k Hk. apply ENV. unfold asrc_env_addr. right; right; right; right; left. lia. }
      exists cval. split; [exact Hcv|].
      eapply vm_kept; [|exact E6]. intros k Hk. apply ENV. unfold asrc_env_addr. right; right; right; right; right. lia. }
    split; [|exact Hfnz].
    eapply vm_kept; [|exact HHEAD]. intros k Hk. apply ENV. unfold asrc_env_addr, as_ofl_head. right; right; left. lia. }
  apply SRr_ret.
  exists ly, S, R, (munrestrict (w_H W) mem M), md'.
  split; [reflexivity|].
  split.
  { (* the journal: the eight stores are in the stack window and the FILE block *)
    eapply (ajournal_exec segs B LAWS segs_low RTOREAD_STK (spZ regs) (rtoread_fp f) ly S W mem md [] ly S W mem md 0
      (munrestrict (w_H W) mem M) md' (fun a => spZ regs - 16 <= a < spZ regs \/ f <= a < f + 1304)
      (ajournal_init segs B RTOREAD_STK (rtoread_fp f) ly S W regs mem md ch HFN)).
    - intros x Hx. rewrite EM.
      assert (Hx1 : ~ (spZ regs - 16 <= bv_unsigned x < spZ regs)) by (intro H0; apply Hx; left; exact H0).
      assert (Hx2 : ~ (f <= bv_unsigned x < f + 1304)) by (intro H0; apply Hx; right; exact H0).
      apply nrange in Hx1, Hx2. pose proof (u64_range x) as Hxr.
      pose proof (KEPT (bv_unsigned x) Hxr ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as E.
      rewrite Z_to_bv_bv_unsigned in E. exact E.
    - rewrite EM. unfold M. repeat apply grows_wb. apply mem_grows_refl.
    - intros x Hx. unfold munrestrict. rewrite Hx. reflexivity.
    - exact Hsame.
    - intros a [Ha | Ha].
      + left. rewrite RS. lia.
      + right. left. split.
        * exists (f, f + 1304). split; [unfold rtoread_fp, SRC_FILE_BLOCK; left; reflexivity | cbn [fst snd]; lia].
        * exists f, 1304. split; [exact Hblk | rewrite RQ; lia]. }
  split.
  { (* callee-saved registers: sp and s0 restored, the rest untouched *)
    intros r Hr. unfold acallee_saved in Hr. unfold R.
    destruct Hr as [-> | [-> | [-> | [-> | [-> | [Hr1 Hr2]]]]]].
    - rewrite getr_upd_eq by (first [vm_compute; reflexivity | reg_neq_tac]).
      transitivity (getr regs 2); [exact (eq_sym Gsp) | f_equal; apply bv_eq; vm_compute; reflexivity].
    - gr. reflexivity.
    - gr. reflexivity.
    - rewrite getr_other by reg_neq_tac. rewrite getr_upd_eq by (first [vm_compute; reflexivity | reg_neq_tac]).
      transitivity (getr regs 8); [apply Z_to_bv_bv_unsigned | f_equal; apply bv_eq; vm_compute; reflexivity].
    - gr. reflexivity.
    - assert (Hc : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; gr; reflexivity. }
  unfold rtoread_post. rewrite !EM.
  split; [reflexivity|]. split; [reflexivity|].
  split; [unfold R; gr; reflexivity|].
  split; [split; [exact SRC | exact SW]|].
  split; [split; [eapply vm_kept; [intros k Hk; apply KEPT; lia | exact VFL] | exact Hfl']|].
  split; [exact SM|].
  split; [unfold SRC_FILE_BLOCK, M; vpeel; apply vm_hitZ8; lia|].
  split; [unfold SRC_FILE_BLOCK, M; vpeel; apply vm_hitZ8; lia|].
  (* the shadow band is outside both the stack window and the FILE block *)
  intros s Hs. unfold kLowMemEnd, kHighShadowEnd in Hs. unfold HIDE in Hfapp'.
  unfold aview. cbv beta. rewrite EM. unfold YP09.mbyte.
  rewrite KEPT; [reflexivity | lia | lia | lia | lia | lia | lia].
Qed.
End a.

(* ---------------------------------------------------------------------- *)
(* 5. The image-free half of the image facts: a segment list whose         *)
(*    segments all lie below kLowMemEnd (a boolean check, discharged by    *)
(*    computation in each instance file) satisfies segs_low.               *)
(* ---------------------------------------------------------------------- *)
Section i.

Lemma segs_low_of_b : forall segs,
  forallb (fun s => (0 <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? kLowMemEnd)) segs = true ->
  forall a, YG0d.in_img segs a -> 0 <= a < kLowMemEnd.
Proof.
  intros segs Hb a (sg & Hin & Hr). pose proof (proj1 (forallb_forall _ _) Hb sg Hin) as Hs.
  apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
End i.
