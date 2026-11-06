(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFfi.v, with its module paths changed and its addresses moved to libreac/fuzz_disco's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/AFfi.v, with its module paths and module names changed; 392 of its 466 lines of code are new or changed and 398 lines of the source are left out. *)
(* fuzz_state image A: the thin realloc segment S4 (the NULL-return arm) of a Theorem Labs lane's realloc composition, i.e.
   RGtop's [seg_nret] at fs's instance [FS_seg_nret] (lib/A/FSRealloc_inst.v), under fs's symbol fact [TfibSyms B]
   (the errno cell is tp - 0xa4, see below; owner ruling a Theorem Labs lane 2026-10-29: the composition supplies TfibSyms B).

   Rule 24 (released-proof lookup): a Theorem Labs lane (internal path; ossv proof
   index v5, ossv/recipes@566eb6ffa5df) answered CONFIRM: no released ASan-image proof of any fuzz_state function.
   Ported from the released donor walk of the same machine code, cgif_rgb_fuzzer's NULL-return arm
   proofs/cgif/cgif_rgb_fuzzer/lib/YF68.v:104 (c_null; composed at YF78.v:553), in the form a Theorem Labs lane's fuzz_reply port
   gives it on the cgif_file core that fuzz_state shares (worktree (internal path)): committed
   f26e0262fc2 proofs/plugin-hostd/fuzz_reply/lib/RT/RTm2.v:217 (m4) with RTm2.v:34-108 and :176-197 (frames,
   chunk8_atom / chunk8_lit / vm_vis, ret_post, ifr_chunks, MRerr, vis_keep) and RTm.v:37-55 (c8, val_mem_addr,
   apresent_wr, rw_wr); uncommitted RT/RTs.v:47-83 there (val_mem_xfer, apresent_vis, vis_apresent_hi, w64_unsigned,
   ap_get, ap_mk).  New here: the decode table, the start state at fs's frames, [cs15] (the callee-saved case split),
   [word_of_present] generalised from fs's A/AFfi.v:255, [errno_in_img] after fs's A/AD1y.v:65 and
   [errno_not_static] after A/AD1y.v:19, and the segment theorem.  Addresses moved to fuzz_state.asan (sha256
   64b53ff86172bb07...).  No file is copied; no generated-class file (AF0m's tables, AB01 / AB03 / AB05, AD2j, ACej)
   is relocated; the walk reads no .bss cell (it reads the stack frames and writes errno).

   THE RUN (capstone over the pinned A image, RV64, no compressed instructions; every literal below checked there):
     Reallocate   0x32994 00050a13 mv s4, a0            (a0 = 0: Allocate returned NULL)
                  0x32998 08050863 beqz a0, +0x90        -> 0x32a28 (taken)
                  0x32a28 000a0513 mv a0, s4
                  0x32a2c 02813083 ld ra, 0x28(sp)       (= 0x32918, FS_RA_REALLOCATE, fs_rframe)
                  0x32a30-0x32a40   ld s0..s4, 0x20..0(sp)
                  0x32a44 03010113 addi sp, sp, 0x30
                  0x32a48 00008067 ret
     asan_realloc 0x32918 fe0500e3 beqz a0, -0x20        -> 0x328f8 (taken)
                  0x328f8 3dc3a0ef jal 0x3a3dc           -> 0x6ccd4 (= 0x328f8 + 0x3a3dc), ra = 0x328fc
     0x6ccd4 (SetErrnoToENOMEM): ff010113 addi sp, sp, -0x10; 00113423 sd ra, 8(sp); 2691f0ef jal 0x1fa68 (-> 0x8c744);
                  00c00593 addi a1, zero, 0xc; 00b52023 sw a1, 0(a0); 00813083 ld ra, 8(sp); 01010113 addi sp, sp, 0x10;
                  00008067 ret
     0x8c744 (__errno_location): 00020513 mv a0, tp; f5c50513 addi a0, a0, -0xa4; 00008067 ret
                  so the store hits tp - 0xa4 = TFIB_TP - 0xa4 = 0x5dae8c = TFIB_ERRNO = as_errno B (TfibSyms ts_tp,
                  ts_errno), 4 bytes, and nothing else outside the stack.
     asan_realloc 0x328fc fc9ff06f j -0x38               -> 0x328c4
                  0x328c4 00000513 mv a0, zero; 0x328c8 00813083 ld ra, 8(sp) (= 0x53620); 0x328cc 01010113 addi sp,
                  sp, 0x10; 0x328d0 00008067 ret
     interceptor  0x53620 07010113 addi sp, sp, 0x70; 0x53624-0x53640 ld ra, s0..s6, 0x7e8..0x7b0(sp);
                  0x53644 7f010113 addi sp, sp, 0x7f0; 0x53648 00008067 ret   -> realloc's caller, a0 = 0.
   No branch to an ASan error report is on this path (the only branches, 0x32998 and 0x32918, are decided by a0 = 0).
   The decode table: asan_realloc 0x3287c (ff010113 addi sp, sp, -0x10) .. Reallocate's ret 0x32a48, 116 words;
   0x53620 .. 0x53648, 11 words; 0x6ccd4, 8 words; 0x8c744, 3 words.
   The frames, as offsets from Reallocate's sp (= realloc's entry sp - 0x8a0 = - 2208, FS_RFRAME): Reallocate's 48
   bytes (s4..s0 at 0..32, ra at 40), asan_realloc's 16 (ra at 56), the interceptor's top 64 bytes at 2144..2208 (s6..s0,
   ra; fs_rframe).  SetErrnoToENOMEM's frame is [32, 48), inside Reallocate's popped frame.

   No Axiom, no Admitted. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.omx_clap_core.fuzz_state.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import AllocG DeallocG ReallocG RGtop.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YO0f YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1h AF0x AF0m FSRealloc_inst.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.

Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The decode table of the run (addresses in the header).                                                          *)

Definition s4_tbl_build : ctable :=
build_table tfibsegs 0x3287c 116%nat (build_table tfibsegs 0x53620 11%nat
(build_table tfibsegs 0x6ccd4 8%nat (build_table tfibsegs 0x8c744 3%nat TEmpty))).
Definition s4_tbl : ctable := Eval vm_compute in s4_tbl_build.
Lemma s4_tbl_eq : s4_tbl = s4_tbl_build.
Proof. vm_cast_no_check (@eq_refl ctable s4_tbl). Qed.
Lemma s4_tbl_ok : table_ok tfibsegs s4_tbl.
Proof.
rewrite s4_tbl_eq. unfold s4_tbl_build.
do 3 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The symbolic start state at 0x32994: the frames based at atom 2 (Reallocate's sp), the errno cell at atom 4 (tp). *)

Definition c8 (o : Z) (e : sv) : YP09.chunk := YP09.mkChunk o (CVal 8 e).
(* Atoms 32..36: Reallocate's saved s4..s0; 37..44: the interceptor's saved ra, s0..s6. *)
Definition s4_RFR : YP09.region := YP09.mkRegion (Some 2%nat) 0 48 32 48
[c8 0 (SOff 32 0); c8 8 (SOff 33 0); c8 16 (SOff 34 0); c8 24 (SOff 35 0); c8 32 (SOff 36 0);
 c8 40 (SLit FS_RA_REALLOCATE)].
Definition s4_AFR : YP09.region := YP09.mkRegion (Some 2%nat) 48 64 0 0 [c8 56 (SLit FS_RA_ASAN_REALLOC)].
Definition s4_IFR : YP09.region := YP09.mkRegion (Some 2%nat) 2144 2208 0 0
[c8 2144 (SOff 44 0); c8 2152 (SOff 43 0); c8 2160 (SOff 42 0); c8 2168 (SOff 41 0); c8 2176 (SOff 40 0);
 c8 2184 (SOff 39 0); c8 2192 (SOff 38 0); c8 2200 (SOff 37 0)].
(* 0x8c744 `addi a0, a0, -0xa4` (f5c50513): errno = tp - 164. *)
Definition s4_ERR : YP09.region := YP09.mkRegion (Some 4%nat) (-164) (-160) (-164) (-160) [].
Definition s4_SS : sstate := mkSS FS_RA_ALLOC sr_atoms [s4_RFR; s4_AFR; s4_IFR; s4_ERR] None (mkFacts [] [] []).

Definition xvals (w0 w1 w2 w3 w4 vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 : Z) : list word :=
[w64 w0; w64 w1; w64 w2; w64 w3; w64 w4; w64 vra; w64 vs0; w64 vs1; w64 vs2; w64 vs3; w64 vs4; w64 vs5; w64 vs6].

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Memory and register lemmas (reply RTm.v / RTm2.v / RTs.v, see the header).                                      *)

Lemma val_mem_addr : forall m a a' (n : nat) v, val_mem tfibsegs m a n v -> a = a' -> val_mem tfibsegs m a' n v.
Proof. intros m a a' n v H <-. exact H. Qed.
Lemma apresent_wr : forall (H : word -> bool) (mem : word -> option byte) a,
apresent H mem a -> writable_at tfibsegs (mrestrict H mem) a.
Proof. intros H m a [Hh [b Hb]]. unfold writable_at, wview, mrestrict. rewrite Hh, Hb. discriminate. Qed.
Lemma rw_wr : forall (m : word -> option byte) a, 0x9f000 <= a < 0x5fd000 -> writable_at tfibsegs m a.
Proof.
intros m a Ha. unfold writable_at. rewrite <- tsegs_tfasegs. apply tfib_rw_window. rewrite unsigned_lit_small by lia. exact Ha.
Qed.
Lemma val_mem_xfer : forall (H H' : word -> bool) (m m' : word -> option byte) a (n : nat) v,
(forall k, (k < n)%nat -> aview tfibsegs H' m' (a + Z.of_nat k) = aview tfibsegs H m (a + Z.of_nat k)) ->
val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v E V k Hk. specialize (V k Hk). specialize (E k Hk). unfold aview in E. rewrite V in E. cbn in E.
destruct (mbyte tfibsegs (mrestrict H' m') (a + Z.of_nat k)) as [b|] eqn:Eb; [|discriminate]. cbn in E. injection E as E.
f_equal. apply bv_eq. exact E.
Qed.
Lemma apresent_vis : forall (H : word -> bool) (m : word -> option byte) a, apresent H m a -> aview tfibsegs H m a <> None.
Proof. intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.
Lemma vis_apresent_hi : forall (H : word -> bool) (m : word -> option byte) a, TFIB_IMG_END <= a < 2 ^ 64 ->
aview tfibsegs H m a <> None -> apresent H m a.
Proof.
intros H m a Ha Hv. unfold aview in Hv. destruct (mbyte tfibsegs (mrestrict H m) a) as [b|] eqn:E; [|exfalso; exact (Hv eq_refl)].
exact (mbyte_high_apresent H m a b Ha E).
Qed.
Lemma vm_vis : forall (H : word -> bool) mem a (w : nat) v i, val_mem tfibsegs (mrestrict H mem) a w v -> 0 <= i < Z.of_nat w ->
aview tfibsegs H mem (a + i) <> None.
Proof.
intros H mem a w v i Hv Hi. unfold aview. replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite (Hv (Z.to_nat i) ltac:(lia)). discriminate.
Qed.
Lemma w64_unsigned : forall w : word, w64 (bv_unsigned w) = w.
Proof. intros w. unfold w64. apply Z_to_bv_bv_unsigned. Qed.
Lemma ap_get : forall (regs regs' : bvmap 5 word) (k : Z) (r : bv 5),
aregs_preserved regs regs' -> acallee_saved k -> bv_unsigned r = k -> getr regs' r = getr regs r.
Proof.
intros regs regs' k r P Hk Hr. replace r with (Z_to_bv 5 k) by (subst k; apply Z_to_bv_bv_unsigned). apply P. exact Hk.
Qed.
Lemma ap_mk : forall (regs regs' : bvmap 5 word),
(forall k (r : bv 5), acallee_saved k -> bv_unsigned r = k -> getr regs' r = getr regs r) -> aregs_preserved regs regs'.
Proof.
intros regs regs' Hm k Hk. apply (Hm k); [exact Hk|]. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 5) with 32. apply Z.mod_small. unfold acallee_saved in Hk. lia.
Qed.
(* The callee-saved registers, one goal per register (2, 3, 4, 8, 9, 18..27), each at its literal. *)
Lemma cs15 : forall (P : bv 5 -> Prop),
P 2%bv -> P 3%bv -> P 4%bv -> P 8%bv -> P 9%bv -> P 18%bv -> P 19%bv -> P 20%bv -> P 21%bv -> P 22%bv ->
P 23%bv -> P 24%bv -> P 25%bv -> P 26%bv -> P 27%bv ->
forall k (r : bv 5), acallee_saved k -> bv_unsigned r = k -> P r.
Proof.
intros P H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 k r Hk Hr. unfold acallee_saved in Hk.
assert (Kc : k = 2 \/ k = 3 \/ k = 4 \/ k = 8 \/ k = 9 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/
  k = 24 \/ k = 25 \/ k = 26 \/ k = 27) by lia.
assert (E : forall (s : bv 5), bv_unsigned s = k -> r = s) by (intros s Hs; apply bv_eq; rewrite Hr, Hs; reflexivity).
destruct Kc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
first [ rewrite (E 2%bv eq_refl) | rewrite (E 3%bv eq_refl) | rewrite (E 4%bv eq_refl) | rewrite (E 8%bv eq_refl)
      | rewrite (E 9%bv eq_refl) | rewrite (E 18%bv eq_refl) | rewrite (E 19%bv eq_refl) | rewrite (E 20%bv eq_refl)
      | rewrite (E 21%bv eq_refl) | rewrite (E 22%bv eq_refl) | rewrite (E 23%bv eq_refl) | rewrite (E 24%bv eq_refl)
      | rewrite (E 25%bv eq_refl) | rewrite (E 26%bv eq_refl) | rewrite (E 27%bv eq_refl) ]; assumption.
Qed.
Ltac inlist := cbn [In]; repeat (first [left; reflexivity | right]).

(* An 8-byte word of present bytes has a value (AFfi.v:255 word_of_present, over any H / mem). *)
Lemma word_of_present : forall (H : word -> bool) (mem : word -> option byte) a,
(forall i, 0 <= i < 8 -> apresent H mem (a + i)) -> exists w, 0 <= w < 2 ^ 64 /\ val_mem tfibsegs (mrestrict H mem) a 8 w.
Proof.
intros H mem a PR.
assert (BY : forall k, (k < 8)%nat -> exists b, mbyte tfibsegs (mrestrict H mem) (a + Z.of_nat k) = Some b).
{ intros k Hk. apply apresent_mbyte. apply PR. lia. }
destruct (BY 0%nat ltac:(lia)) as [b0 B0]. destruct (BY 1%nat ltac:(lia)) as [b1 B1]. destruct (BY 2%nat ltac:(lia)) as [b2 B2]. destruct (BY 3%nat ltac:(lia)) as [b3 B3].
destruct (BY 4%nat ltac:(lia)) as [b4 B4]. destruct (BY 5%nat ltac:(lia)) as [b5 B5]. destruct (BY 6%nat ltac:(lia)) as [b6 B6]. destruct (BY 7%nat ltac:(lia)) as [b7 B7].
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1. pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
pose proof (bv_unsigned_in_range 8 b4) as R4. pose proof (bv_unsigned_in_range 8 b5) as R5. pose proof (bv_unsigned_in_range 8 b6) as R6. pose proof (bv_unsigned_in_range 8 b7) as R7.
change (bv_modulus 8) with 256 in R0, R1, R2, R3, R4, R5, R6, R7.
exists (bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))))).
split; [lia|].
assert (LB : forall (z q b : Z) (k : nat) r, (k < 8)%nat -> 0 <= b < 256 -> 0 <= q -> 0 <= r < 2 ^ (8 * Z.of_nat k) ->
z = 2 ^ (8 * Z.of_nat k) * (b + 256 * q) + r -> z < 2 ^ 64 -> YG0f.le_byte z 8 k = b).
{ clear. intros z q b k r Hk Hb Hq Hr Hz Hz64. unfold YG0f.le_byte. rewrite Z.shiftr_div_pow2 by lia.
rewrite (Z.mod_small z) by (change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); lia).
rewrite <- (Z.div_unique z (2 ^ (8 * Z.of_nat k)) (b + 256 * q) r ltac:(left; exact Hr) Hz).
symmetry. apply (Z.mod_unique _ 256 q b); lia. }
match goal with |- val_mem _ _ _ _ ?w => set (WW := w) end.
assert (GOAL : forall (bk : byte) kk, mbyte tfibsegs (mrestrict H mem) (a + Z.of_nat kk) = Some bk -> YG0f.le_byte WW 8 kk = bv_unsigned bk ->
mbyte tfibsegs (mrestrict H mem) (a + Z.of_nat kk) = Some (Z_to_bv 8 (YO0f.le_byte WW 8 kk))).
{ intros bk kk Hm Hl. rewrite Hm, <- le_byte_eq, Hl, Z_to_bv_bv_unsigned. reflexivity. }
intros k Hk.
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [..|lia];
[ apply (GOAL b0 0%nat B0) | apply (GOAL b1 1%nat B1) | apply (GOAL b2 2%nat B2) | apply (GOAL b3 3%nat B3)
| apply (GOAL b4 4%nat B4) | apply (GOAL b5 5%nat B5) | apply (GOAL b6 6%nat B6) | apply (GOAL b7 7%nat B7) ]; subst WW.
- apply (LB _ ((bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))))) _ 0%nat (0)); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 0)) with 1; lia | change (2 ^ (8 * Z.of_nat 0)) with 1; lia | lia].
- apply (LB _ ((bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7)))))) _ 1%nat (bv_unsigned b0)); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 1)) with 256; lia | change (2 ^ (8 * Z.of_nat 1)) with 256; lia | lia].
- apply (LB _ ((bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))) _ 2%nat ((bv_unsigned b0 + 256 * bv_unsigned b1))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 2)) with 65536; lia | change (2 ^ (8 * Z.of_nat 2)) with 65536; lia | lia].
- apply (LB _ ((bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7)))) _ 3%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * bv_unsigned b2)))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 3)) with 16777216; lia | change (2 ^ (8 * Z.of_nat 3)) with 16777216; lia | lia].
- apply (LB _ ((bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))) _ 4%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3))))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 4)) with 4294967296; lia | change (2 ^ (8 * Z.of_nat 4)) with 4294967296; lia | lia].
- apply (LB _ ((bv_unsigned b6 + 256 * bv_unsigned b7)) _ 5%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * bv_unsigned b4)))))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 5)) with 1099511627776; lia | change (2 ^ (8 * Z.of_nat 5)) with 1099511627776; lia | lia].
- apply (LB _ (bv_unsigned b7) _ 6%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * bv_unsigned b5))))))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 6)) with 281474976710656; lia | change (2 ^ (8 * Z.of_nat 6)) with 281474976710656; lia | lia].
- apply (LB _ (0) _ 7%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * bv_unsigned b6)))))))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 7)) with 72057594037927936; lia | change (2 ^ (8 * Z.of_nat 7)) with 72057594037927936; lia | lia].
Qed.

(* The errno cell is in the image's writable part, and no owned static range of fs meets it (Tfib_owned_static,
   AF0m.v:281; the same gap 0x5da590..0x5daed8 as AD1y.v:17 DRV_IVS). *)
Lemma errno_in_img : forall a, TFIB_ERRNO <= a < TFIB_ERRNO + 4 -> in_img tfibsegs a.
Proof.
intros a Ha. unfold TFIB_ERRNO in Ha. unfold in_img.
assert (E : tfibsegs = [Asan_segment_000; Asan_segment_001; Asan_segment_002; Asan_segment_003]) by reflexivity.
exists Asan_segment_003. split; [rewrite E; cbn; tauto | cbn; lia].
Qed.
Lemma errno_not_static : forall a, TFIB_ERRNO <= a < TFIB_ERRNO + 4 -> ~ Exists (in_zr a) Tfib_owned_static.
Proof.
intros a Ha X. unfold TFIB_ERRNO in Ha. unfold Tfib_owned_static in X.
repeat (apply Exists_cons in X; destruct X as [X|X]; [unfold in_zr in X; cbn [fst snd] in X; lia|]).
inversion X.
Qed.

Lemma wvb_parts : forall md mat,
m_vmmaps (with_vm_backing (m_vm_lazy md) mat md) = m_vmmaps md /\
m_vm_lazy (with_vm_backing (m_vm_lazy md) mat md) = m_vm_lazy md /\
eager_used (with_vm_backing (m_vm_lazy md) mat md) = eager_used md.
Proof. intros [fd [maps lazy mat0] io fs proc lim tm] mat. repeat split; reflexivity. Qed.
Lemma same_io_wvb : forall md mat, same_io md (with_vm_backing (m_vm_lazy md) mat md).
Proof. intros md mat. destruct md. repeat split; reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The machine run (reply RTm2.v:217 m4, at fs's addresses).                                                         *)

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma chunk8_atom : forall regs (extra : list word) m base off j v,
nth j extra (Z_to_bv 64 0) = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> val_mem tfibsegs m (base + off) 8 v ->
YP09.chunk_ok tfibsegs (Ereg regs extra) m base (c8 off (SOff (32 + j) 0)).
Proof.
intros regs extra m base off j v Hn Hv Hm. apply (chunk_ok_val tfibsegs _ m base off 8 (SOff (32 + j) 0) v); [|cbn; lia|cbn; lia|exact Hm].
cbn [sv_denot]. rewrite ew_Ereg_extra, Hn. rewrite unsigned_lit_small by lia. f_equal; lia.
Qed.
Lemma chunk8_lit : forall E m base off v, 0 <= v < 2 ^ 64 -> val_mem tfibsegs m (base + off) 8 v ->
YP09.chunk_ok tfibsegs E m base (c8 off (SLit v)).
Proof. intros E m base off v Hv Hm. apply (chunk_ok_val tfibsegs E m base off 8 (SLit v) v); [reflexivity|cbn; lia|cbn; lia|exact Hm]. Qed.

Section W.
Variable W : world tfibsegs.
Variable md : Model.
Local Abbreviation H := (w_H W).

Definition rfr_ok (m : word -> option byte) (a w0 w1 w2 w3 w4 : Z) : Prop :=
val_mem tfibsegs (mrestrict H m) a 8 w0 /\ val_mem tfibsegs (mrestrict H m) (a + 8) 8 w1 /\
val_mem tfibsegs (mrestrict H m) (a + 16) 8 w2 /\ val_mem tfibsegs (mrestrict H m) (a + 24) 8 w3 /\
val_mem tfibsegs (mrestrict H m) (a + 32) 8 w4 /\ val_mem tfibsegs (mrestrict H m) (a + 40) 8 FS_RA_REALLOCATE.
Definition afr_ok (m : word -> option byte) (a : Z) : Prop := val_mem tfibsegs (mrestrict H m) (a + 8) 8 FS_RA_ASAN_REALLOC.
Definition ifr_ok (m : word -> option byte) (a vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 : Z) : Prop :=
val_mem tfibsegs (mrestrict H m) (a + 56) 8 vra /\ val_mem tfibsegs (mrestrict H m) (a + 48) 8 vs0 /\
val_mem tfibsegs (mrestrict H m) (a + 40) 8 vs1 /\ val_mem tfibsegs (mrestrict H m) (a + 32) 8 vs2 /\
val_mem tfibsegs (mrestrict H m) (a + 24) 8 vs3 /\ val_mem tfibsegs (mrestrict H m) (a + 16) 8 vs4 /\
val_mem tfibsegs (mrestrict H m) (a + 8) 8 vs5 /\ val_mem tfibsegs (mrestrict H m) a 8 vs6.

(* realloc's return: the interceptor's callee-saved registers restored from its frame, a0 = [a0], memory [MR]. *)
Definition ret_post (regs : bvmap 5 word) (MR : (word -> option byte) -> Prop) (sp' a0 vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 : Z)
(W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 vra) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\ MR mem' /\
getr regs' 2 = w64 sp' /\ getr regs' 1 = w64 vra /\ getr regs' 8 = w64 vs0 /\ getr regs' 9 = w64 vs1 /\
getr regs' 18 = w64 vs2 /\ getr regs' 19 = w64 vs3 /\ getr regs' 20 = w64 vs4 /\ getr regs' 21 = w64 vs5 /\
getr regs' 22 = w64 vs6 /\ getr regs' 10 = w64 a0 /\
(forall r : bv 5, In r [3; 4; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).

(* The memory at realloc's return: changed only in the stack window [lo, hi) and errno; errno holds 12; the window
   stays present; every visible byte stays visible. *)
Definition MRerr (mem : word -> option byte) (lo hi : Z) (m' : word -> option byte) : Prop :=
(forall x : word, ~ (lo <= bv_unsigned x < hi) -> ~ (TFIB_ERRNO <= bv_unsigned x < TFIB_ERRNO + 4) -> m' x = mem x) /\
val_mem tfibsegs (mrestrict H m') TFIB_ERRNO 4 12 /\ (forall a, lo <= a < hi -> apresent H m' a) /\
(forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs H mem a <> None -> aview tfibsegs H m' a <> None).

Lemma vis_keep : forall (mem m' : word -> option byte) lo hi a, 0 <= a < 2 ^ 64 ->
(forall x : word, ~ (lo <= bv_unsigned x < hi) -> ~ (TFIB_ERRNO <= bv_unsigned x < TFIB_ERRNO + 4) -> m' x = mem x) ->
val_mem tfibsegs (mrestrict H m') TFIB_ERRNO 4 12 -> (forall a, lo <= a < hi -> apresent H m' a) ->
aview tfibsegs H mem a <> None -> aview tfibsegs H m' a <> None.
Proof.
intros mem m' lo hi a Ha MEQ V P Hv.
destruct (Z_lt_le_dec a lo) as [L1|L1]; [|destruct (Z_lt_le_dec a hi) as [L2|L2]].
3: destruct (Z_lt_le_dec a TFIB_ERRNO) as [L3|L3]; [|destruct (Z_lt_le_dec a (TFIB_ERRNO + 4)) as [L4|L4]].
- destruct (Z_lt_le_dec a TFIB_ERRNO) as [L3|L3]; [|destruct (Z_lt_le_dec a (TFIB_ERRNO + 4)) as [L4|L4]].
  + rewrite (aview_same H mem m' a). exact Hv. apply MEQ; rewrite unsigned_lit_small by lia; lia.
  + replace a with (TFIB_ERRNO + (a - TFIB_ERRNO)) by lia. apply (vm_vis H m' TFIB_ERRNO 4 12); [exact V | cbn; lia].
  + rewrite (aview_same H mem m' a). exact Hv. apply MEQ; rewrite unsigned_lit_small by lia; lia.
- destruct (P a ltac:(lia)) as [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
- rewrite (aview_same H mem m' a). exact Hv. apply MEQ; rewrite unsigned_lit_small by lia; lia.
- replace a with (TFIB_ERRNO + (a - TFIB_ERRNO)) by lia. apply (vm_vis H m' TFIB_ERRNO 4 12); [exact V | cbn; lia].
- rewrite (aview_same H mem m' a). exact Hv. apply MEQ; rewrite unsigned_lit_small by lia; lia.
Qed.

Ltac reg_ent HS r k :=
let R := fresh "R" in rreg HS r R; rewrite R; exact (ew_Ereg_nat _ _ k r eq_refl).
Ltac reg_x HS r j :=
let R := fresh "R" in rreg HS r R; rewrite R; exact (ew_Ereg_extra _ _ j).
Ltac range8 := match goal with RV : Forall _ _ |- _ =>
  repeat (apply Forall_cons_iff in RV as [? RV]) end.
Ltac ifr_chunks regs X m sp b vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 I0 I1 I2 I3 I4 I5 I6 I7 :=
  apply Forall_cons; [apply (chunk8_atom regs X m sp b 12 vs6); [reflexivity|lia|eapply val_mem_addr; [exact I7|lia]]|];
  apply Forall_cons; [apply (chunk8_atom regs X m sp (b + 8) 11 vs5); [reflexivity|lia|eapply val_mem_addr; [exact I6|lia]]|];
  apply Forall_cons; [apply (chunk8_atom regs X m sp (b + 16) 10 vs4); [reflexivity|lia|eapply val_mem_addr; [exact I5|lia]]|];
  apply Forall_cons; [apply (chunk8_atom regs X m sp (b + 24) 9 vs3); [reflexivity|lia|eapply val_mem_addr; [exact I4|lia]]|];
  apply Forall_cons; [apply (chunk8_atom regs X m sp (b + 32) 8 vs2); [reflexivity|lia|eapply val_mem_addr; [exact I3|lia]]|];
  apply Forall_cons; [apply (chunk8_atom regs X m sp (b + 40) 7 vs1); [reflexivity|lia|eapply val_mem_addr; [exact I2|lia]]|];
  apply Forall_cons; [apply (chunk8_atom regs X m sp (b + 48) 6 vs0); [reflexivity|lia|eapply val_mem_addr; [exact I1|lia]]|];
  apply Forall_cons; [apply (chunk8_atom regs X m sp (b + 56) 5 vra); [reflexivity|lia|eapply val_mem_addr; [exact I0|lia]]|];
  apply Forall_nil.

(* Allocate's NULL return into Reallocate (0x32994, sp = Reallocate's sp) -> realloc's return, a0 = 0, errno = 12. *)
Lemma s4_run : forall (regs : bvmap 5 word) (mem : word -> option byte) (sp w0 w1 w2 w3 w4 vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 : Z),
bv_unsigned (getr regs 2) = sp -> 0x5fd000 <= sp -> sp + 2208 <= 2 ^ 64 ->
getr regs 10 = w64 0 -> getr regs 4 = w64 TFIB_TP ->
Forall (fun v => 0 <= v < 2 ^ 64) [w0; w1; w2; w3; w4; vra; vs0; vs1; vs2; vs3; vs4; vs5; vs6] ->
rfr_ok mem sp w0 w1 w2 w3 w4 -> afr_ok mem (sp + 48) -> ifr_ok mem (sp + 2144) vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 ->
(forall a, sp + 32 <= a < sp + 48 -> apresent H mem a) -> YK0s.ret_ok (w64 vra) ->
SRr tfibsegs W (mkCfg (mkst regs (w64 FS_RA_ALLOC) mem (seg_rom tfibsegs)) md)
(ret_post regs (MRerr mem (sp + 32) (sp + 48)) (sp + 2208) 0 vra vs0 vs1 vs2 vs3 vs4 vs5 vs6).
Proof.
intros regs mem sp w0 w1 w2 w3 w4 vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 Hsp Hlo Hhi G10 G4 RV
(F0 & F1 & F2 & F3 & F4 & F5) A0 (I0 & I1 & I2 & I3 & I4 & I5 & I6 & I7) HP Hret.
pose proof Hwx_tfa as Hwx. range8.
set (X := xvals w0 w1 w2 w3 w4 vra vs0 vs1 vs2 vs3 vs4 vs5 vs6).
assert (E2 : bv_unsigned (ew (Ereg regs X) 2) = sp) by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact Hsp).
assert (E4 : bv_unsigned (ew (Ereg regs X) 4) = TFIB_TP).
{ rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl), G4. unfold w64, TFIB_TP. apply unsigned_lit_small. lia. }
assert (HS0 : st_ok tfibsegs (Ereg regs X) s4_SS (restrict (w_H W) (mkst regs (Z_to_bv 64 FS_RA_ALLOC) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold s4_SS. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    + unfold region_ok, s4_RFR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
      split; [lia|]. split; [lia|]. split; [intros o Ho; apply apresent_wr, HP; lia|].
      apply Forall_cons; [apply (chunk8_atom regs X _ sp 0 0 w0); [reflexivity|lia|eapply val_mem_addr; [exact F0|lia]]|].
      apply Forall_cons; [apply (chunk8_atom regs X _ sp 8 1 w1); [reflexivity|lia|eapply val_mem_addr; [exact F1|lia]]|].
      apply Forall_cons; [apply (chunk8_atom regs X _ sp 16 2 w2); [reflexivity|lia|eapply val_mem_addr; [exact F2|lia]]|].
      apply Forall_cons; [apply (chunk8_atom regs X _ sp 24 3 w3); [reflexivity|lia|eapply val_mem_addr; [exact F3|lia]]|].
      apply Forall_cons; [apply (chunk8_atom regs X _ sp 32 4 w4); [reflexivity|lia|eapply val_mem_addr; [exact F4|lia]]|].
      apply Forall_cons; [apply chunk8_lit; [unfold FS_RA_REALLOCATE; lia|eapply val_mem_addr; [exact F5|lia]]|]. apply Forall_nil.
    + unfold region_ok, s4_AFR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [apply chunk8_lit; [unfold FS_RA_ASAN_REALLOC; lia|eapply val_mem_addr; [exact A0|lia]]|]. apply Forall_nil.
    + unfold region_ok, s4_IFR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      ifr_chunks regs X (mrestrict (w_H W) mem) sp 2144 vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 I0 I1 I2 I3 I4 I5 I6 I7.
    + unfold region_ok, s4_ERR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E4.
      unfold TFIB_TP. split; [lia|]. split; [lia|]. split; [intros o Ho; apply rw_wr; lia|]. apply Forall_nil.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, s4_RFR, s4_AFR, s4_IFR, s4_ERR.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite !E2, !E4. unfold TFIB_TP. repeat split; lia.
  - split; [exact I | split; exact I]. }
pose proof (st_ok_pin_reg (Ereg regs X) s4_SS _ 10%bv (SLit 0) HS0 ltac:(intros XX; discriminate XX)
  ltac:(cbn [restrict ms_regs mkst]; rewrite G10; reflexivity)) as HS. clear HS0.
change (w64 FS_RA_ALLOC) with (Z_to_bv 64 FS_RA_ALLOC).
srr_run_sh s4_tbl_ok HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msA end.
assert (MEQ : forall x : word, ~ (sp + 32 <= bv_unsigned x < sp + 48) -> ~ (TFIB_ERRNO <= bv_unsigned x < TFIB_ERRNO + 4) -> ms_mem msA x = mem x).
{ intros x N1 N2. apply HF. intros Hw. destruct (in_wrange_windows _ _ _ Hw) as (b & lo & hi & Hin & Hrg). vm_compute in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hrg; rewrite ?E2, ?E4 in Hrg; unfold TFIB_ERRNO, TFIB_TP in *; lia|]).
  destruct Hin. }
clear HF HFr.
assert (V12 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msA)) TFIB_ERRNO 4 12).
{ pose proof (st_ok_chunk_val (w_H W) _ _ _ 3 _ 0 (-164) 4 (SLit 12) 12 HS eq_refl eq_refl eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  cbn [base_val YP09.r_base N.to_nat] in V. rewrite E4 in V. eapply val_mem_addr; [exact V | unfold TFIB_ERRNO, TFIB_TP; lia]. }
assert (PW : forall a, sp + 32 <= a < sp + 48 -> apresent (w_H W) (ms_mem msA) a).
{ intros a Ha. eapply (st_ok_window_apresent (w_H W) _ _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite E2; lia | unfold TFIB_IMG_END; lia]. }
eapply (SRr_ret_at tfibsegs s4_tbl s4_tbl_ok Hwx W _); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. split; [reflexivity|].
assert (R1 : getr (ms_regs msA) 1 = w64 vra) by reg_x HS (1%bv : bv 5) 5%nat.
exists (ms_regs msA), (ms_mem msA), mat'.
split; [rewrite R1; unfold YK0s.ret_ok in Hret; rewrite Hret; reflexivity|].
split. { split; [exact MEQ|]. split; [exact V12|]. split; [exact PW|]. intros a Ha Hv. exact (vis_keep mem (ms_mem msA) _ _ a Ha MEQ V12 PW Hv). }
split; [let R := fresh "R" in rreg HS (2%bv : bv 5) R; rewrite R, E2; reflexivity|].
split; [exact R1|].
split; [reg_x HS (8%bv : bv 5) 6%nat|]. split; [reg_x HS (9%bv : bv 5) 7%nat|]. split; [reg_x HS (18%bv : bv 5) 8%nat|].
split; [reg_x HS (19%bv : bv 5) 9%nat|]. split; [reg_x HS (20%bv : bv 5) 10%nat|]. split; [reg_x HS (21%bv : bv 5) 11%nat|].
split; [reg_x HS (22%bv : bv 5) 12%nat|].
split. { let R := fresh "R" in rreg HS (10%bv : bv 5) R; rewrite R; reflexivity. }
intros r Hr. cbn [In] in Hr.
repeat (destruct Hr as [<-|Hr]; [ lazymatch goal with |- getr _ ?rr = _ =>
  let k := eval vm_compute in (Z.to_nat (bv_unsigned rr)) in reg_ent HS rr k end |]).
destruct Hr.
Qed.
End W.
End c.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* S4 = FS_seg_nret.                                                                                                 *)

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable Up : list (Z * Z).
Hypothesis TB : TfibSyms B.
Let LAWS : AR_laws tfibsegs B := YG0q.AR_laws_ok tfibsegs B.

Theorem fs_seg_nret : FS_seg_nret B Up.
Proof.
unfold FS_seg_nret, seg_nret.
(* c5's errno premise (as_errno B = as_tp B - 0xa4) is not needed: TfibSyms gives both cells (ts_errno / ts_tp) *)
intros _ ly S W regs mem md p n_old n ch S1 W1 so bp regsA memA mdA ly2 S2 W2 regs2 mem2 md2 RE K1 APRE APOST G10 _ OOM.
intros.
pose proof (ts_tp B TB) as ETP. pose proof (ts_errno B TB) as EER.
(* realloc's entry *)
destruct RE as (RP & _).
destruct RP as ((_ & ARU0) & Hra & _ & Hlo & _ & Hhi & _ & Hgp & Htp & _).
unfold ASTACK in Hlo.
(* K1, by pattern *)
cbv beta delta [K1_fs] in K1.
repeat lazymatch type of K1 with _ /\ _ => let X := fresh "K" in destruct K1 as [X K1] end.
lazymatch goal with Hx : raZ regsA = _ |- _ => rename Hx into KRA end.
lazymatch goal with Hx : spZ regsA = _ |- _ => rename Hx into KSP end.
lazymatch goal with Hx : forall r : Z, 23 <= r <= 27 -> @?P r |- _ => rename Hx into K2327 end.
lazymatch goal with Hx : fs_rframe regs W1 memA |- _ => rename Hx into KFR end.
lazymatch goal with Hx : rwin tfibsegs regs W1 memA |- _ => rename Hx into KWIN end.
(* Allocate's pre and post *)
destruct APRE as ((_ & ARUA) & _ & _ & _ & _ & _ & _ & _ & _ & HgpA & HtpA & _).
destruct APOST as ((_ & ARU2) & LLE & _ & PRES & _ & FR & _ & PRS).
destruct LLE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & LSL & LSH & _).
(* the stack lies in high memory *)
assert (SK : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd)
  by (eapply FSP.stk_kHighMemBeg; eapply FSP.ARU_ARm; exact ARU0).
destruct SK as (SKL & SKH).
pose proof (u64_range (getr regs 2)) as Usp. fold (spZ regs) in Usp.
unfold FS_RFRAME in KSP.
assert (SPR : spZ regs - 2208 = spZ regsA) by lia.
assert (NOS1 : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ aowned B ly S1 a).
{ intros a Ha. eapply (FSP.ARU_stack _ _ LAWS); [exact ARUA | exact Ha]. }
assert (NOS2 : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ aowned B ly2 S2 a).
{ intros a Ha. eapply (FSP.ARU_stack _ _ LAWS); [exact ARU2 |]. rewrite LSL, LSH. exact Ha. }
assert (NOE2 : forall a, TFIB_ERRNO <= a < TFIB_ERRNO + 4 -> ~ aowned B ly2 S2 a).
{ intros a Ha Ho. apply (errno_not_static a Ha). rewrite <- (ts_owned B TB).
  assert (HAR : exists m, AR tfibsegs B ly2 S2 W2 m md2) by (eexists; eapply FSP.ARU_AR; exact ARU2).
  destruct HAR as (m & HAR).
  exact (proj1 (al_owned_image _ _ LAWS ly2 S2 W2 m md2 a HAR (errno_in_img a Ha)) Ho). }
(* Allocate's frame: realloc's window outside Allocate's 4096 bytes reads as at Allocate's entry *)
assert (FRW : forall a, spZ regs - ASTACK <= a < spZ regs -> ~ (spZ regsA - AFSTACK_G <= a < spZ regsA) ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W1) memA a).
{ intros a Ha Hn. unfold ASTACK in Ha. apply FR.
  - unfold kHighMemBeg, kHighMemEnd in *. lia.
  - apply NOS1. lia.
  - apply NOS2. lia.
  - unfold ascratch. intros [Xa|Xa]; [exact (Hn Xa)|]. rewrite EER in Xa. unfold TFIB_ERRNO, kHighMemBeg in *. lia.
  - intros (Xn & _). exact (Xn eq_refl). }
assert (RWIN2 : rwin tfibsegs regs W2 mem2).
{ intros a Ha. destruct (Z_lt_le_dec a (spZ regsA - AFSTACK_G)) as [L|L]; [|destruct (Z_lt_le_dec a (spZ regsA)) as [L2|L2]].
  - apply vis_apresent_hi; [unfold TFIB_IMG_END, ASTACK, kHighMemBeg, kHighMemEnd in *; lia|].
    rewrite (FRW a Ha ltac:(lia)). apply apresent_vis. exact (KWIN a Ha).
  - apply PRS. lia.
  - apply vis_apresent_hi; [unfold TFIB_IMG_END, ASTACK, kHighMemBeg, kHighMemEnd in *; lia|].
    rewrite (FRW a Ha ltac:(lia)). apply apresent_vis. exact (KWIN a Ha). }
assert (XF : forall a (k : nat) v, spZ regsA <= a -> a + Z.of_nat k <= spZ regs ->
  val_mem tfibsegs (mrestrict (w_H W1) memA) a k v -> val_mem tfibsegs (mrestrict (w_H W2) mem2) a k v).
{ intros a k v Ha Hk V. apply (val_mem_xfer (w_H W1) (w_H W2) memA mem2 a k v); [|exact V].
  intros j Hj. apply FRW; unfold ASTACK, AFSTACK_G in *; lia. }
destruct KFR as (F28 & F38 & F8 & F16 & F24 & F32 & F40 & F48 & F56 & F64).
unfold FS_RFRAME in F28, F38.
(* Reallocate's saved s0..s4: any present words *)
assert (PW8 : forall o, 0 <= o <= 32 -> forall i, 0 <= i < 8 -> apresent (w_H W2) mem2 (spZ regs - 2208 + o + i)).
{ intros o Ho i Hi. apply RWIN2. unfold ASTACK. lia. }
destruct (word_of_present _ _ _ (PW8 0 ltac:(lia))) as (w0 & Rw0 & V0).
destruct (word_of_present _ _ _ (PW8 8 ltac:(lia))) as (w1 & Rw1 & V1).
destruct (word_of_present _ _ _ (PW8 16 ltac:(lia))) as (w2 & Rw2 & V2).
destruct (word_of_present _ _ _ (PW8 24 ltac:(lia))) as (w3 & Rw3 & V3).
destruct (word_of_present _ _ _ (PW8 32 ltac:(lia))) as (w4 & Rw4 & V4).
(* the registers at Allocate's return *)
assert (P2 : getr regs2 2%bv = getr regsA 2%bv) by (apply (ap_get regsA regs2 2); [exact PRES | unfold acallee_saved; lia | reflexivity]).
assert (P4 : getr regs2 4%bv = getr regsA 4%bv) by (apply (ap_get regsA regs2 4); [exact PRES | unfold acallee_saved; lia | reflexivity]).
assert (G10' : getr regs2 10 = w64 0) by (rewrite G10; reflexivity).
assert (G4 : getr regs2 4 = w64 TFIB_TP) by (rewrite P4, HtpA, ETP; reflexivity).
assert (Hsp2 : bv_unsigned (getr regs2 2) = spZ regs - 2208) by (rewrite P2; fold (spZ regsA); lia).
rewrite KRA. unfold cfg_at.
eapply SRr_mono.
{ apply (s4_run W2 md2 regs2 mem2 (spZ regs - 2208) w0 w1 w2 w3 w4 (raZ regs)
    (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9)) (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19))
    (bv_unsigned (getr regs 20)) (bv_unsigned (getr regs 21)) (bv_unsigned (getr regs 22))).
  - exact Hsp2.
  - unfold ASTACK, kHighMemBeg in *. lia.
  - lia.
  - exact G10'.
  - exact G4.
  - unfold raZ. repeat apply Forall_cons; try apply Forall_nil; try lia; apply u64_range.
  - split; [eapply val_mem_addr; [exact V0 | lia]|]. split; [eapply val_mem_addr; [exact V1 | lia]|].
    split; [eapply val_mem_addr; [exact V2 | lia]|]. split; [eapply val_mem_addr; [exact V3 | lia]|].
    split; [eapply val_mem_addr; [exact V4 | lia]|].
    eapply val_mem_addr; [apply XF; [| |exact F28]; cbn [Z.of_nat]; lia | lia].
  - unfold afr_ok. eapply val_mem_addr; [apply XF; [| |exact F38]; cbn [Z.of_nat]; lia | lia].
  - split; [eapply val_mem_addr; [apply XF; [| |exact F8]; cbn [Z.of_nat]; lia | lia]|].
    split; [eapply val_mem_addr; [apply XF; [| |exact F16]; cbn [Z.of_nat]; lia | lia]|].
    split; [eapply val_mem_addr; [apply XF; [| |exact F24]; cbn [Z.of_nat]; lia | lia]|].
    split; [eapply val_mem_addr; [apply XF; [| |exact F32]; cbn [Z.of_nat]; lia | lia]|].
    split; [eapply val_mem_addr; [apply XF; [| |exact F40]; cbn [Z.of_nat]; lia | lia]|].
    split; [eapply val_mem_addr; [apply XF; [| |exact F48]; cbn [Z.of_nat]; lia | lia]|].
    split; [eapply val_mem_addr; [apply XF; [| |exact F56]; cbn [Z.of_nat]; lia | lia]|].
    eapply val_mem_addr; [apply XF; [| |exact F64]; cbn [Z.of_nat]; lia | lia].
  - intros a Ha. apply RWIN2. unfold ASTACK. lia.
  - unfold raZ. rewrite w64_unsigned. exact Hra. }
intros W' c' _ (-> & regs' & mem' & mat & -> & (MEQ & V12 & PW & VIS) & R2 & R1 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R10 & RK).
exists regs', mem', (with_vm_backing (m_vm_lazy md2) mat md2).
split; [reflexivity|].
split.
{ (* the callee-saved registers of realloc's entry *)
  apply ap_mk. apply (cs15 (fun r => getr regs' r = getr regs r)); cbv beta.
  - rewrite R2. replace (spZ regs - 2208 + 2208) with (bv_unsigned (getr regs 2%bv)) by (unfold spZ in *; lia). apply w64_unsigned.
  - rewrite (RK 3%bv ltac:(inlist)), (ap_get regsA regs2 3 3%bv PRES ltac:(unfold acallee_saved; lia) eq_refl), HgpA, Hgp; reflexivity.
  - rewrite (RK 4%bv ltac:(inlist)), P4, HtpA, Htp; reflexivity.
  - rewrite R8. apply w64_unsigned.
  - rewrite R9. apply w64_unsigned.
  - rewrite R18. apply w64_unsigned.
  - rewrite R19. apply w64_unsigned.
  - rewrite R20. apply w64_unsigned.
  - rewrite R21. apply w64_unsigned.
  - rewrite R22. apply w64_unsigned.
  - rewrite (RK 23%bv ltac:(inlist)), (ap_get regsA regs2 23 23%bv PRES ltac:(unfold acallee_saved; lia) eq_refl).
    replace (23%bv : bv 5) with (Z_to_bv 5 23) by (apply bv_eq; reflexivity). apply K2327. lia.
  - rewrite (RK 24%bv ltac:(inlist)), (ap_get regsA regs2 24 24%bv PRES ltac:(unfold acallee_saved; lia) eq_refl).
    replace (24%bv : bv 5) with (Z_to_bv 5 24) by (apply bv_eq; reflexivity). apply K2327. lia.
  - rewrite (RK 25%bv ltac:(inlist)), (ap_get regsA regs2 25 25%bv PRES ltac:(unfold acallee_saved; lia) eq_refl).
    replace (25%bv : bv 5) with (Z_to_bv 5 25) by (apply bv_eq; reflexivity). apply K2327. lia.
  - rewrite (RK 26%bv ltac:(inlist)), (ap_get regsA regs2 26 26%bv PRES ltac:(unfold acallee_saved; lia) eq_refl).
    replace (26%bv : bv 5) with (Z_to_bv 5 26) by (apply bv_eq; reflexivity). apply K2327. lia.
  - rewrite (RK 27%bv ltac:(inlist)), (ap_get regsA regs2 27 27%bv PRES ltac:(unfold acallee_saved; lia) eq_refl).
    replace (27%bv : bv 5) with (Z_to_bv 5 27) by (apply bv_eq; reflexivity). apply K2327. lia. }
split; [exact R10|].
(* the allocator relation: only realloc's window and errno changed, neither owned *)
assert (MEQZ : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2208 + 32 <= a < spZ regs - 2208 + 48) ->
  ~ (TFIB_ERRNO <= a < TFIB_ERRNO + 4) -> mem' (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a)).
{ intros a Ha N1 N2. apply MEQ; rewrite unsigned_lit_small by lia; assumption. }
split.
{ split; [reflexivity|].
  pose proof (wvb_parts md2 mat) as (E1 & E2 & E3).
  eapply (FSP.ARU_frame _ _ LAWS); [exact ARU2 | | | exact E1 | exact E2 | exact E3 |].
  - intros a Ha Ho. apply aview_same. apply MEQZ; [exact Ha | |].
    + intros Xa. apply (NOS2 a); [unfold ASTACK in *; lia | exact Ho].
    + intros Xa. exact (NOE2 a Xa Ho).
  - intros a Hv. rewrite (FSP.aview_mod tfibsegs (w_H W2) mem2 a) in Hv. rewrite (FSP.aview_mod tfibsegs (w_H W2) mem' a).
    apply VIS; [apply Z.mod_pos_bound; lia | exact Hv].
  - intros a Hb Hh. unfold w64. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hb.
    apply MEQZ; [lia | unfold kHighMemBeg in *; lia | unfold TFIB_ERRNO; lia]. }
split; [apply same_io_wvb|].
split.
{ (* rkeep, in the view and in the raw memory *)
  split.
  - intros a Ha Hn. apply aview_same. apply MEQZ; [exact Ha | |].
    + intros Xa. apply Hn. left. unfold ASTACK. lia.
    + intros Xa. apply Hn. right. rewrite EER. exact Xa.
  - intros x Hn. pose proof (u64_range x) as Ux. apply MEQ.
    + intros Xa. apply Hn. left. unfold ASTACK. lia.
    + intros Xa. apply Hn. right. rewrite EER. exact Xa. }
split.
{ (* rwin *)
  intros a Ha. destruct (Z_lt_le_dec a (spZ regs - 2208 + 32)) as [L|L]; [|destruct (Z_lt_le_dec a (spZ regs - 2208 + 48)) as [L2|L2]].
  - apply (apresent_same _ mem2 mem' a); [apply MEQZ; unfold ASTACK, TFIB_ERRNO, kHighMemBeg, kHighMemEnd in *; lia | exact (RWIN2 a Ha)].
  - apply PW. lia.
  - apply (apresent_same _ mem2 mem' a); [apply MEQZ; unfold ASTACK, TFIB_ERRNO, kHighMemBeg, kHighMemEnd in *; lia | exact (RWIN2 a Ha)]. }
split; [rewrite EER; exact V12|].
(* the out-of-memory byte *)
apply (val_mem_frame _ mem2 mem' TFIB_OOM 1%nat 1); [|exact OOM].
intros k Hk. apply MEQZ; unfold TFIB_OOM, TFIB_ERRNO, kHighMemBeg in *; lia.
Qed.
End s.
